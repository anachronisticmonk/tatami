#!/usr/bin/env python3
"""Scrape Proofs/*.lean for theorems, their statements, sources and the
theorems each proof body names.

A text scraper: it never invokes Lean. An edge means "this identifier appears
in that proof body", with comments and string literals stripped first -- so it
is what the proof *mentions*, not a kernel dependency graph.
"""
import re, json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FILES = ["Sorted", "Order", "Spec", "Lattice", "Mangle", "Merge", "Walk",
         "Counts", "Wellformed", "Tree", "Inference", "Correctness"]
ID = r"[A-Za-z_][A-Za-z0-9_.'?!]*"
KINDS = r"(?:theorem|lemma)"

def strip(t):
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    t = re.sub(r"--[^\n]*", " ", t)
    return re.sub(r'"(?:[^"\\]|\\.)*"', ' "" ', t)

decls, order = {}, []
for area in FILES:
    rel = f"Proofs/{area}.lean"
    src = open(os.path.join(ROOT, rel), encoding="utf-8").read()
    # Blank block comments in place -- same length, newlines kept -- so that
    # prose like "A preservation\ntheorem would need ..." is not scanned as a
    # declaration while offsets and line numbers stay valid.
    scan = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), src, flags=re.S)
    for m in re.finditer(r"^(?:private\s+)?" + KINDS + r"\s+(" + ID + ")", scan, re.M):
        name, start = m.group(1), m.start()
        nxt = re.search(r"^(?:private\s+)?(?:theorem|lemma|def|structure|inductive|end|/-!|@\[)",
                        src[m.end():], re.M)
        end = m.end() + (nxt.start() if nxt else len(src) - m.end())
        body = src[start:end].rstrip()
        # where the statement stops and the proof starts. Equation-style
        # declarations (`| 0, _, h => h`) have no `:=` at all, so the first
        # bar at the start of a line counts too.
        cands = [body.find(":= by"), body.find(":=")]
        bar = re.search(r"^\s*\|", body, re.M)
        if bar:
            cands.append(bar.start())
        cands = [c for c in cands if c > 0]
        i = min(cands) if cands else -1
        decls[name] = dict(name=name, area=area, file=rel,
                           line=src[:start].count("\n") + 1,
                           stmt=(body[:i] if i > 0 else body).rstrip(),
                           full=body,
                           proof=strip(body[i:] if i >= 0 else ""))
        order.append(name)

names = set(decls)
edges = []
for n in order:
    p = decls[n]["proof"]
    for o in names:
        if o == n:
            continue
        if re.search(r"(?<![A-Za-z0-9_.'?!])" + re.escape(o) + r"(?![A-Za-z0-9_.'?!])", p):
            edges.append([n, o])

for d in decls.values():
    del d["proof"]

out = dict(decls=decls, edges=edges, order=order,
           areas=FILES, counts=dict(theorems=len(order), edges=len(edges)))
path = os.path.join(ROOT, "explainer/src/data/graph.json")
json.dump(out, open(path, "w"), indent=0)
print(f"{len(order)} theorems, {len(edges)} edges -> {path}")
