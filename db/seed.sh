#!/usr/bin/env bash
# Add benchmark rows. The signature's effect is invisible on a handful of
# rows -- it is a claim about what a large result set costs to materialise --
# so the perf page needs a table with enough in it to see.
#
#   ./db/seed.sh            200000 rows
#   ./db/seed.sh 1000000    a million
#   ./db/seed.sh --reset    remove only the rows this script added
#
# Seeded rows are marked by their sku prefix, so --reset cannot touch data
# that was already there.
set -euo pipefail

NAME=${TATAMI_PG_CONTAINER:-tatami-pg}
PGUSER=${TATAMI_PGUSER:-tatami}
DB=${TATAMI_PGDATABASE:-tatami}
run() { docker exec -i "$NAME" psql -qtAU "$PGUSER" -d "$DB" "$@"; }

if [ "${1:-}" = "--reset" ]; then
  run -c "DELETE FROM orders WHERE sku LIKE 'BENCH-%'"
  run -c "select 'orders: ' || count(*) || ' rows' from orders"
  exit 0
fi

ROWS=${1:-200000}

# The foreign key needs customers to exist. Whatever is already there is left
# alone -- only an empty table is filled, and with every NOT NULL column.
run -c "INSERT INTO customers (id, name, city, since)
        SELECT g, 'customer ' || g, 'city ' || g, 2020 + (g % 5)
        FROM generate_series(1, 5) g
        WHERE NOT EXISTS (SELECT 1 FROM customers)"

# Values are arithmetic rather than random so a re-seed is reproducible.
# customer_id is drawn from the ids that actually exist, gathered once into an
# array rather than looked up per row.
# note is NULL on one row in three: the mask has to have something to say.
run -c "INSERT INTO orders (id, customer_id, sku, qty, price, note)
        SELECT (SELECT coalesce(max(id), 0) FROM orders) + g,
               c.ids[1 + (g % array_length(c.ids, 1))],
               'BENCH-' || lpad(((g * 7919) % 100000)::text, 6, '0'),
               ((g::bigint * 2654435761) % 1000)::int,
               round((((g::bigint * 48271) % 100000) / 100.0)::numeric, 2),
               CASE WHEN g % 3 = 0 THEN NULL ELSE 'note for order ' || g END
        FROM generate_series(1, $ROWS) g,
             (SELECT array_agg(id ORDER BY id) AS ids FROM customers) c"

run -c "select 'orders: ' || count(*) || ' rows' from orders"
