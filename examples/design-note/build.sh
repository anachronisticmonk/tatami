#!/bin/sh
# eval $(opam env --switch=5.5.0) first if ocamlc is not on your PATH
#
# A typecheck, not a demo. Nothing here can be run -- see README.md.
set -e
ocamlc -c ids.mli ids.ml b.mli b.ml root.mli root.ml
echo "ok: the generated signatures and implementations typecheck"
rm -f *.cmi *.cmo
