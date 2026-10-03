# Tatami explainer

A reader for the Lean half of Tatami: what the pipeline does, which part of it
each theorem covers, and the dependency tree under each guarantee.

```sh
npm install
npm run dev      # http://localhost:5173
npm run build    # static site in dist/
```

## Nothing here is transcribed

Both data files are generated from the repository, so the app cannot drift
from the sources it describes:

```sh
npm run extract
```

| file | from | by |
| --- | --- | --- |
| `src/data/graph.json` | `Proofs/*.lean` | `scripts/extract-graph.py` |
| `src/data/types.json` | `Tatami/*.lean`, `Main.lean` | `scripts/extract-types.py` |
| `src/data/stages.json` | the pipeline itself | `scripts/Stages.lean` |

`extract-graph.py` is a **text scraper** — it never invokes Lean. It reads each
theorem's statement, source and line, and records an edge wherever one proof
body names another theorem, with block comments, line comments and string
literals blanked first. So an edge means *this proof mentions that theorem*,
which is the argument structure, not a kernel dependency graph.

`extract-types.py` is a scraper too, and the same caveat applies: it records
every `structure`, `inductive` and `abbrev` with its docstring, its source and
its line, and an edge wherever one declaration's body *names* another. That is
what a reader following a type wants and not a resolved reference. It is what
puts a declaration behind every value in the worked example — the type a step
binds is clickable, and so is each declaration it is built out of, opening in
the same panel the Lean map uses for a theorem.

`Stages.lean` is the opposite: it runs the real `documents`,
`observeDocument`, `Tables.merge`, `inferFinish`, `toSchema` and `gen` on
`scripts/corpus.json` and prints every intermediate value. Change the corpus
and re-run `extract` to retell the worked example with different data.

Each value is printed **twice**, off the same value, so the two cannot
disagree: once structured, for the tables and panels the page draws, and once
as Lean source, so a reader can see the raw intermediate the call actually
returned. The Lean rendering lays itself out to about eighty columns — where a
term is broken across lines it is the same term with more whitespace, never a
shortened one. Two elisions are marked as such and nothing else is hidden: a
`.ml` body, which is an `Expr` rather than a declaration, is counted rather
than printed; and in the final record `ocaml` and `tables` are given by size,
being the values two other steps already show in full.

One thing in that file is transcribed rather than computed: the five field
names of the `Outcome` record, which is declared in `Main.lean`. A script
cannot import it, because `Main` already declares a `main`.

The corpus is chosen so that every step changes something — `meta` present in
one document and missing from the other, `runs` a lone object in one and an
array of objects in the other (so the singleton collapse fires), and `ms` an
integer in one place and a decimal in another.

Glosses — the one-line plain-English summary per theorem — are authored, in
`src/data/gloss.js`. Everything else on the page comes out of the repository.

## Theme

Dark by default, light on request, remembered — the same `tatami-theme` key
the playground and the backend use, so a reader who switched there arrives
here switched. The palette tokens are lifted verbatim from
`web/playground-react.html`: VS Code Dark+ for dark, saffron-on-cream for
light. The theme is stamped on `<html>` by a small script in `index.html`
before first paint, so the page never flashes the wrong one.

The graph is themed too: the proof files' categorical colours are CSS
variables with a per-theme set, and the SVG takes them through `style` rather
than presentation attributes, which do not accept `var()`.

## Sections

| | |
| --- | --- |
| **Overview** | the one theorem and its five parts |
| **The pipeline** | eight stages, with each guarantee drawn against the span it covers — and the two transitions nothing covers |
| **A worked example** | one corpus through every call, each value drawn and as raw Lean, with the declaration behind it one click away |
| **The guarantees** | each statement, and how it is proved, in plain words |
| **Lean map** | the dependency tree under each guarantee |
| **What is not proved** | the boundary, stated rather than implied |
