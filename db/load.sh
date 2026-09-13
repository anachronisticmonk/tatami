#!/usr/bin/env bash
# Shred the corpus into Postgres.
#
#   ./db/up.sh                     container and nothing else
#   ./db/load.sh                   corpus/ci.json -> seven tables
#   ./db/load.sh /tmp/small.json   a smaller one
#
# Tables are created empty, filled by COPY in dependency order, and only then
# given their foreign keys and indexes. The result is the same as declaring the
# references up front; it just does not validate ten million rows one at a
# time on the way in.
set -euo pipefail

NAME=${TATAMI_PG_CONTAINER:-tatami-pg}
PGUSER=${TATAMI_PGUSER:-tatami}
DB=${TATAMI_PGDATABASE:-tatami}
CORPUS=${1:-corpus/ci.json}
TSV=${TATAMI_TSV:-corpus/pg}
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")

# TSV may be given absolutely; make it so either way before anything uses it.
case "$TSV" in /*) ;; *) TSV="$root/$TSV" ;; esac

psql() { docker exec -i "$NAME" psql -qXU "$PGUSER" -d "$DB" "$@"; }

echo "shredding $CORPUS"
(cd "$root" && dune exec bin/shred.exe -- --corpus "$CORPUS" --out "$TSV")

echo "creating tables"
psql < "$here/schema.sql"

for t in owner repository topic run job label step; do
  printf '  copy %-11s' "$t"
  psql -c "COPY $t FROM STDIN" < "$TSV/$t.tsv"
  printf '%9s rows\n' "$(psql -tAc "select count(*) from $t")"
done

echo "foreign keys and indexes"
psql < "$here/constraints.sql"
echo "done"
