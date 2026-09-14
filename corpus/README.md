# small.json

A CI service's build history. 1,000 projects, 1.7 MB — a readable slice of the
same corpus `bin/gen_corpus.ml` produces at any size.

```
repo        a project someone is building
└── run     one build, triggered by a commit
    └── job one machine's share of that build
        └── step   one command inside that job: checkout, build, test, …
```

Each step records how long it ran (`ms`) and what a millisecond cost on that
runner (`rate`). Four levels, three hops, every level an array.

The full 1.5 GB version is not checked in — regenerate it, byte for byte:

```sh
dune exec bin/gen_corpus.exe -- --bytes 1.5G --seed 20260914 --out corpus/ci.json
```

See `CORPUS.md` at the repository root for the field list and the four tables
it shreds into.
