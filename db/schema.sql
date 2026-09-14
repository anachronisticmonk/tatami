-- The four tables the corpus shreds into.
--
-- Column order matches the order each .mli lists its accessors, and NOT NULL
-- appears exactly where the .mli does *not* say [option]. Both are deliberate:
-- the database is meant to be a faithful second copy of the same data, so that
-- a difference in answers between it and the JSON is a bug rather than a
-- sampling artefact.
--
-- The foreign keys live in constraints.sql and are applied after the COPY.
-- Validating them per row while loading millions of rows would dominate the
-- load; applied afterwards they are checked once, in bulk.

DROP TABLE IF EXISTS step, job, run, repo CASCADE;

CREATE TABLE repo (
  id         uuid    PRIMARY KEY,
  name       text    NOT NULL,
  org        text    NOT NULL,
  is_private boolean NOT NULL      -- JSON key "private", an OCaml keyword
);

-- repo.runs was an array, so it is a table whose elements point back. idx is
-- the position the element had in the array, kept because order is
-- information the array carried and a table would otherwise lose.
CREATE TABLE run (
  id      integer PRIMARY KEY,
  repo_id uuid    NOT NULL,
  idx     integer NOT NULL,
  branch  text    NOT NULL,
  status  text    NOT NULL,
  ms      integer NOT NULL,
  trigger text                      -- string option
);

CREATE TABLE job (
  id     integer PRIMARY KEY,
  run_id integer NOT NULL,
  idx    integer NOT NULL,
  os     text    NOT NULL,
  status text    NOT NULL,
  ms     integer NOT NULL,
  exit   integer                    -- int option
);

-- The largest table, three hops from the root. ms and rate are both total, so
-- ms * rate needs no validity array -- the claim a catalog cannot make, there
-- being no such column for it to describe.
CREATE TABLE step (
  id     integer PRIMARY KEY,
  job_id integer NOT NULL,
  idx    integer NOT NULL,
  name   text    NOT NULL,
  ms     integer NOT NULL,
  rate   double precision NOT NULL,
  error  text                       -- string option
);
