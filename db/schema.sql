-- The tables schema/orders.mli describes. Column order in orders matches the
-- order the .mli lists, so `select *` and the expansion tuned emits agree.
CREATE TABLE IF NOT EXISTS customers (
  id    integer PRIMARY KEY,
  name  text    NOT NULL,
  city  text    NOT NULL,
  since integer NOT NULL
);

CREATE TABLE IF NOT EXISTS orders (
  id          integer PRIMARY KEY,
  customer_id integer NOT NULL REFERENCES customers (id),
  sku         text    NOT NULL,
  qty         integer NOT NULL,
  price       numeric(10, 2) NOT NULL,
  note        text            -- the one nullable column, and the only
);                            -- place `string option` comes from
