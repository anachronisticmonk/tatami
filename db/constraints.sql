-- Applied after the COPY. These are the same references the .mli files declare
-- with their cross-module id types -- run.repo_id is Repo.id, step.job_id is
-- Job.id -- restated in the database's own vocabulary.

ALTER TABLE run  ADD CONSTRAINT run_repo_fk FOREIGN KEY (repo_id) REFERENCES repo (id);
ALTER TABLE job  ADD CONSTRAINT job_run_fk  FOREIGN KEY (run_id)  REFERENCES run (id);
ALTER TABLE step ADD CONSTRAINT step_job_fk FOREIGN KEY (job_id)  REFERENCES job (id);

-- A join across the nesting follows these, so they are indexed. Without them a
-- three-hop join is three sequential scans, and the comparison would be
-- measuring the absence of an index rather than anything about layout.
CREATE INDEX run_repo_idx ON run (repo_id);
CREATE INDEX job_run_idx  ON job (run_id);
CREATE INDEX step_job_idx ON step (job_id);

ANALYZE;
