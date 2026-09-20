#!/usr/bin/env bash
# Why the keyword suffix is `_` and not `'`. A Q&A card, not the main demo.
set -uo pipefail
cd "$(dirname "$0")/.."
B=$'\e[1m'; D=$'\e[2m'; R=$'\e[31m'; G=$'\e[32m'; C=$'\e[36m'; N=$'\e[0m'
FILE=Tatami/Mangle.lean
GOOD="  if isKeyword p then p ++ ['_'] else p"
BAD="  if isKeyword p then p ++ ['\\''] else p"
PROBE=$(mktemp -t mangle_probe.XXXXXX.lean)
restore(){ git checkout -- "$FILE" 2>/dev/null; rm -f "$PROBE"; }
trap restore EXIT INT TERM
beat(){ if [ -n "${PACE:-}" ]; then sleep "$PACE"; else printf "${D}   ⏎${N}"; read -r _ </dev/tty; fi; }

git diff --quiet -- "$FILE" || { echo "${R}$FILE has uncommitted edits.${N}"; exit 1; }
printf "${D}building…${N}\r"; lake build >/dev/null 2>&1; printf "         \r"
cat > "$PROBE" <<'EOF'
import Tatami
open Tatami
#eval (mangle "type", mangle "type'")
#eval mangle "type" == mangle "type'"
EOF

printf "\n${B}Two members: ${C}type${N}${B} (an OCaml keyword) and ${C}type'${N}\n\n"
printf "   ${D}mangled:${N} "; lake env lean "$PROBE" | head -1
printf "   ${D}same?   ${N} ${G}"; lake env lean "$PROBE" | tail -1; printf "${N}"
beat

printf "\n${B}Now suffix keywords with ' instead of _${N} ${D}(Mangle.lean:73)${N}\n\n"
printf "   ${R}- %s${N}\n   ${G}+ %s${N}\n" "$GOOD" "$BAD"
# python, not perl: the replacement contains a backslash-quote, which perl
# reads as the postmatch variable and silently drops
GOOD="$GOOD" BAD="$BAD" FILE="$FILE" python3 -c 'import os
p=os.environ["FILE"]; s=open(p).read()
assert s.count(os.environ["GOOD"])==1
open(p,"w").write(s.replace(os.environ["GOOD"], os.environ["BAD"]))'
lake build Tatami >/dev/null 2>&1
printf "\n   ${D}mangled:${N} "; lake env lean "$PROBE" | head -1
printf "   ${D}same?   ${N} ${R}"; lake env lean "$PROBE" | tail -1; printf "${N}"
printf "\n   ${R}Two JSON members, one OCaml field.${N}\n"
beat

printf "\n${B}The proof${N}\n\n"
lake build Proofs 2>&1 | grep -E "^error: Proofs/Mangle" | head -3 | sed 's/^/   /'
printf "\n   ${C}keywordSuffixed_inj${N} ${D}fails, on the step ${N}${C}prefixedCore_ne_snoc${N}${D}:${N}\n\n"
sed -n '/^theorem prefixedCore_ne_snoc/,/:= by$/p' Proofs/Mangle.lean | sed "s/^/   ${C}/;s/\$/${N}/"
printf "\n   ${D}No mangled name is a keyword with the suffix stuck on the end.${N}\n"
printf "   ${D}That holds for ${N}_${D} because the mangler escapes it, so an encoding${N}\n"
printf "   ${D}never ends in one. It fails for ${N}'${D} because the mangler passes ${N}'${D}${N}\n"
printf "   ${D}through, so the member ${N}type'${D} encodes to exactly ${N}type'${D}.${N}\n"
beat
restore; printf "${D}restoring…${N}\r"; lake build >/dev/null 2>&1
printf "${G}restored, build green        ${N}\n"
