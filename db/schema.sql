-- The seven tables the corpus shreds into.
--
-- Column order matches the order each .mli lists its accessors, and NOT NULL
-- appears exactly where the .mli does *not* say [option]. Both are deliberate:
-- the database is meant to be a faithful second copy of the same data, so that
-- a difference in answers between it and the JSON is a bug and not a sampling
-- artefact.
--
-- The foreign keys live in constraints.sql and are applied after the COPY.
-- Validating them per row while loading ten million rows would dominate the
-- load; applied afterwards they are checked once, in bulk, and the tables end
-- up in exactly the same state.

DROP TABLE IF EXISTS step, label, job, run, topic, repository, owner CASCADE;

-- repository.owner was a nested object, so it is a table and the parent holds
-- a key into it. One row per repository.
CREATE TABLE owner (
  id        integer PRIMARY KEY,
  login     text    NOT NULL,
  kind      text    NOT NULL,
  followers integer NOT NULL,
  email     text                 -- string option
);

CREATE TABLE repository (
  id             integer PRIMARY KEY,
  name           text    NOT NULL,
  org            text    NOT NULL,
  default_branch text    NOT NULL,
  is_private     boolean NOT NULL,
  stars          integer NOT NULL,
  created_at     integer NOT NULL,
  description    text,                -- string option
  owner_id       integer NOT NULL
);

-- repository.topics was an array of strings. A scalar array still becomes a
-- table: the element needs somewhere to live and its position has to survive.
CREATE TABLE topic (
  id            integer PRIMARY KEY,
  repository_id integer NOT NULL,
  idx           integer NOT NULL,
  value         text    NOT NULL
);

CREATE TABLE run (
  id            integer PRIMARY KEY,
  repository_id integer NOT NULL,
  idx           integer NOT NULL,
  number        integer NOT NULL,
  commit_sha    text    NOT NULL,
  branch        text    NOT NULL,
  status        text    NOT NULL,
  started_at    integer NOT NULL,
  duration_ms   integer NOT NULL,
  trigger       text                 -- string option
);

CREATE TABLE job (
  id          integer PRIMARY KEY,
  run_id      integer NOT NULL,
  idx         integer NOT NULL,
  name        text    NOT NULL,
  runner_os   text    NOT NULL,
  status      text    NOT NULL,
  duration_ms integer NOT NULL,
  queued_ms   integer NOT NULL,
  exit_code   integer              -- int option
);

CREATE TABLE label (
  id     integer PRIMARY KEY,
  job_id integer NOT NULL,
  idx    integer NOT NULL,
  value  text    NOT NULL
);

-- The largest table, three hops from the root. duration_ms and cost_per_ms are
-- both total, so their product needs no validity array -- which is the claim a
-- catalog cannot make, having no column there to describe.
CREATE TABLE step (
  id          integer PRIMARY KEY,
  job_id      integer NOT NULL,
  idx         integer NOT NULL,
  name        text    NOT NULL,
  status      text    NOT NULL,
  duration_ms integer NOT NULL,
  cost_per_ms double precision NOT NULL,
  log_bytes   integer NOT NULL,
  memory_mb   integer NOT NULL,
  error       text                 -- string option
);
