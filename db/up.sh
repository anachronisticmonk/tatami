#!/usr/bin/env bash
# Bring up the Postgres the kernels read, and make sure the tables exist.
# Safe to run repeatedly: it starts an existing container rather than
# replacing one, and the schema is CREATE TABLE IF NOT EXISTS.
set -euo pipefail

NAME=${TATAMI_PG_CONTAINER:-tatami-pg}
PORT=${TATAMI_PGPORT:-5432}
USER=${TATAMI_PGUSER:-tatami}
PASS=${TATAMI_PGPASSWORD:-tatami}
DB=${TATAMI_PGDATABASE:-tatami}
here=$(cd "$(dirname "$0")" && pwd)

if docker ps --format '{{.Names}}' | grep -qx "$NAME"; then
  echo "$NAME already running"
elif docker ps -a --format '{{.Names}}' | grep -qx "$NAME"; then
  echo "starting existing $NAME"
  docker start "$NAME" >/dev/null
else
  echo "creating $NAME"
  docker run -d --name "$NAME" \
    -e POSTGRES_USER="$USER" -e POSTGRES_PASSWORD="$PASS" \
    -e POSTGRES_DB="$DB" -p "$PORT":5432 postgres:16 >/dev/null
fi

printf 'waiting for postgres'
for _ in $(seq 1 60); do
  if docker exec "$NAME" pg_isready -U "$USER" -d "$DB" >/dev/null 2>&1; then
    echo " ready"
    docker exec -i "$NAME" psql -qU "$USER" -d "$DB" < "$here/schema.sql"
    docker exec "$NAME" psql -tAU "$USER" -d "$DB" \
      -c "select 'orders: ' || count(*) || ' rows' from orders"
    exit 0
  fi
  printf '.'; sleep 1
done
echo " timed out"; exit 1
