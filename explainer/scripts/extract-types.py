#!/usr/bin/env python3
"""Scrape the Lean sources for the types the pipeline passes between stages.

A text scraper, like `extract-graph.py`, and never invokes Lean. It records
each `structure`, `inductive` and `abbrev` with its docstring, its source, and
which other scraped types its body names -- so the worked example can show not
only the value a call returned but the declaration that value inhabits.

An edge means "this declaration mentions that name", which is what a reader
following a type wants, and not a resolved reference.
"""
import re, json, os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SOURCES = sorted(f"Tatami/{f}" for f in os.listdir(os.path.join(ROOT, "Tatami"))
                 if f.endswith(".lean")) + ["Main.lean"]

ID = r"[A-Za-z_][A-Za-z0-9_.']*"
KINDS = r"(?:structure|inductive|abbrev)"
# a declaration runs until the next one starts at the left margin
NEXT = (r"^(?:private\s+|protected\s+|noncomputable\s+)*"
        r"(?:structure|inductive|abbrev|def|theorem|lemma|instance|example|"
        r"namespace|end|mutual|open|import|@\[|/-!|/--)")


def doc_before(src, start):
    """The `/-- ... -/` block immediately above a declaration, if the only
    thing between them is whitespace or attribute lines."""
    end = src.rfind("-/", 0, start)
    if end < 0:
        return "", start
    between = src[end + 2:start]
    if between.strip() and not re.fullmatch(r"(?:\s|@\[[^\]]*\])*", between):
        return "", start
    open_at = src.rfind("/--", 0, end)
    if open_at < 0:
        return "", start
    body = src[open_at + 3:end]
    # the comment markers go; the indentation of the continuation lines does
    # too, so the panel is not showing a column of spaces
    lines = [ln.strip() for ln in body.strip().split("\n")]
    return "\n".join(lines), open_at


types, order = {}, []
for rel in SOURCES:
    path = os.path.join(ROOT, rel)
    src = open(path, encoding="utf-8").read()
    # Comment bodies blanked for *scanning* only, so prose naming a structure
    # is not read as one; offsets and line numbers stay valid. The opening
    # three characters survive, because a docstring at the left margin is
    # where the next declaration begins and the scan has to see it.
    def blank(m):
        t = m.group(0)
        return t[:3] + re.sub(r"[^\n]", " ", t[3:])
    scan = re.sub(r"/-.*?-/", blank, src, flags=re.S)

    for m in re.finditer(r"^(?:private\s+)?(" + KINDS + r")\s+(" + ID + ")", scan, re.M):
        kind, name, start = m.group(1), m.group(2), m.start()
        nxt = re.search(NEXT, scan[m.end():], re.M)
        end = m.end() + (nxt.start() if nxt else len(src) - m.end())
        body = src[start:end].rstrip()
        doc, _ = doc_before(src, start)
        # the namespace this sits in, read off the headers above it
        opened = re.findall(r"^namespace\s+(" + ID + ")", scan[:start], re.M)
        closed = len(re.findall(r"^end\s+" + ID, scan[:start], re.M))
        stack = [n for n in opened[closed:] if n != "Tatami"]
        qual = ".".join(stack + [name])
        types[qual] = dict(name=qual, kind=kind, file=rel,
                           line=src[:start].count("\n") + 1,
                           doc=doc, src=body)
        order.append(qual)

# which scraped types each declaration's body names
short = {}
for q in types:
    short.setdefault(q.split(".")[-1], q)
for q, d in types.items():
    body = re.sub(r"/-.*?-/", " ", d["src"], flags=re.S)
    body = re.sub(r"--[^\n]*", " ", body)
    seen = []
    for s, target in short.items():
        if target == q:
            continue
        if re.search(r"(?<![A-Za-z0-9_.'])" + re.escape(s) + r"(?![A-Za-z0-9_'])", body):
            seen.append(target)
    d["mentions"] = sorted(seen)

out = dict(types=types, order=order)
dest = os.path.join(ROOT, "explainer/src/data/types.json")
json.dump(out, open(dest, "w"), indent=0)
print(f"{len(order)} types -> {dest}")
