# The design note's worked example

Every file here is generated:

```sh
tatami -o . < input.json
```

`input.json` is §2.1 Step 1 of the design note. The six files are what Phase 1
emits for it: `ids`, plus an `.mli` and an `.ml` per table.

## Why there is nothing to run

`build.sh` typechecks the output and stops. It used to build and run a demo,
and cannot any more, which is the point rather than a regression.

Phase 1 describes the tables and never produces one. So every operation that
would *reach* a row is emitted as `failwith "...: no row source"` --- `get`,
and the `of_`*p* lookup a collection table carries. Everything that *reads* an
existing row is real: `let a r = r.a`, `let b r = B.get r.b`.

A key can therefore only come from a row, and a row only from one of the
holes. `ids.mli` declares the key types abstract and offers no way to make
one:

```ocaml
type b
type root
```

An earlier version exposed `val unsafe_b : int -> b` so that a demo could
fabricate rows. Nothing generated ever called it, and it let a consumer build
a foreign key naming a row that does not exist --- so it is gone, and with it
the demo. "No row source" now means there is no way in at all.

## What this does demonstrate

That the emitted code compiles, in the order it is emitted, with each module
in its own compilation unit and the foreign keys intact. That is the whole of
what Phase 1 claims.
