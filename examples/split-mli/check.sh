#!/bin/sh
# Compile every variant with ocamlc and report which structures OCaml accepts.
# eval $(opam env --switch=5.5.0) first if ocamlc is not on your PATH
cd "$(dirname "$0")"

try() {                       # try DIR "file1.mli file2.mli ..."
  dir=$1; shift
  ( cd "$dir" && rm -f *.cmi && ocamlc -c $* 2>&1 ) >/tmp/tatami-ocamlc.$$ 2>&1
  if [ $? -eq 0 ]; then printf '  OK    %-34s %s\n' "$dir" "$*"
  else printf '  FAIL  %-34s %s\n' "$dir" "$*"; sed 's/^/          /' /tmp/tatami-ocamlc.$$; fi
  rm -f /tmp/tatami-ocamlc.$$
}

echo "D1 -- the design note's document"
try d1-design-note/naive-split "b.mli root.mli"
try d1-design-note/option-a    "ids.mli b.mli root.mli"
try d1-design-note/option-b    "b.mli root.mli"

echo
echo "D2 -- the same document plus one repeated substructure"
echo "  the naive split, in both possible orders:"
try d2-with-collection/naive-split "b.mli xs.mli root.mli"
try d2-with-collection/naive-split "b.mli root.mli xs.mli"
echo "  the two proposals:"
try d2-with-collection/option-a "ids.mli xs.mli b.mli root.mli"
try d2-with-collection/option-b "b.mli root.mli xs.mli"

echo
echo "D2 -- the foreign key still means something"
expect_ok()   { ( cd "$1" && ocamlc -c "$2" >/dev/null 2>&1 ) && printf '  OK    %-22s %s type-checks\n' "$1" "$2" || printf '  FAIL  %-22s %s was rejected\n' "$1" "$2"; }
expect_fail() { ( cd "$1" && ocamlc -c "$2" >/dev/null 2>&1 ) && printf '  FAIL  %-22s %s compiled -- the key IS forgeable\n' "$1" "$2" || printf '  OK    %-22s %s rejected, as it must be\n' "$1" "$2"; }
expect_ok   d2-with-collection/option-a use.ml
expect_fail d2-with-collection/option-a forge.ml
expect_ok   d2-with-collection/option-b use.ml
expect_fail d2-with-collection/option-b forge.ml
