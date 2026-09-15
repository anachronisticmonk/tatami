#!/usr/bin/env bash
# Load a corpus into Postgres.
#
#   ./db/up.sh                     the container and nothing else
#   ./db/load.sh                   corpus/ci.json -> the tables it implies
#   ./db/load.sh /tmp/small.json   a smaller one
#
# There is no schema file to apply first. The tables, their columns, their
# nullability and their foreign keys are all derived from the corpus by the
# generator, and `load.exe` issues them over the same connection it loads on --
# create, then load, then constrain, in one transaction.
#
# Regenerate the modules first if the corpus has changed shape:
#
#   lake build && ./.lake/build/bin/tatami CORPUS --config CONFIG -o schema
set -euo pipefail

CORPUS=${1:-corpus/ci.json}
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")

cd "$root"
dune build bin/load.exe
exec ./_build/default/bin/load.exe --corpus "$CORPUS"
