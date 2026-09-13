-- Applied after the COPY. The references are the same ones the .mli files
-- declare with their cross-module id types -- repository.owner_id is
-- Owner.id, step.job_id is Job.id -- so this file is that part of the schema
-- restated in the database's own vocabulary.

ALTER TABLE repository ADD CONSTRAINT repository_owner_fk
  FOREIGN KEY (owner_id) REFERENCES owner (id);
ALTER TABLE topic ADD CONSTRAINT topic_repository_fk
  FOREIGN KEY (repository_id) REFERENCES repository (id);
ALTER TABLE run ADD CONSTRAINT run_repository_fk
  FOREIGN KEY (repository_id) REFERENCES repository (id);
ALTER TABLE job ADD CONSTRAINT job_run_fk
  FOREIGN KEY (run_id) REFERENCES run (id);
ALTER TABLE label ADD CONSTRAINT label_job_fk
  FOREIGN KEY (job_id) REFERENCES job (id);
ALTER TABLE step ADD CONSTRAINT step_job_fk
  FOREIGN KEY (job_id) REFERENCES job (id);

-- A join across the nesting follows these, so they are indexed. Without them
-- a three-hop join is three sequential scans and the comparison would be
-- measuring the absence of an index rather than anything about layout.
CREATE INDEX topic_repository_idx ON topic (repository_id);
CREATE INDEX run_repository_idx   ON run (repository_id);
CREATE INDEX job_run_idx          ON job (run_id);
CREATE INDEX label_job_idx        ON label (job_id);
CREATE INDEX step_job_idx         ON step (job_id);

ANALYZE;
