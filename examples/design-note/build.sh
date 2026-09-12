#!/bin/sh
# eval $(opam env --switch=5.5.0) first if ocamlc is not on your PATH
set -e
ocamlc generated.mli generated.ml demo.ml -o demo
./demo
