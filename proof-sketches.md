# How each guarantee is proved — in plain words

For Q&A. If a judge asks *"how did you actually prove that?"*, the answer is
the **In one sentence** line. Everything above it is there if they push.

No lemma names anywhere — deliberately. Naming the scaffolding answers a
question nobody asked.

---

## The move that does most of the work

Three of the five are proved the same way, and it is worth being able to
explain the trick once.

**The generator checks its own output before returning it.** It builds the
signature, then inspects what it built, and refuses to hand back anything that
repeats a name or describes a table nothing can reach.

So the proof of "what comes out is well formed" is one step: *it gave us a
file, therefore the check passed, therefore the property holds.* We never
trace names through the generator at all.

This is worth more than it sounds. Because the proof never reasons about
*where* the schema came from, the guarantee holds for **any** schema — not
only the ones our own inference produces. A schema handed to us by something
else, or by a future version of the inference, gets the same promise.

The obvious objection: *"so you've proved the checker agrees with itself?"*
No — the check is a program returning yes or no, and the theorem is a
statement about all files. The work is proving the first really implies the
second. And the checks are not what make the program usable: separately we
prove the name mangler never produces a collision, which is *why* the check
never fires on real input. The check is the seatbelt; the mangler proof is why
you don't crash.

---

## 1 · Well-formedness — *the names are legal, and no two collide*

**How.** Inversion on the generator's self-check, as above. It compares every
module name, every value name inside a module, and every record field name,
and refuses on a repeat.

Separately — and this is the part with real content — we prove that turning a
JSON key into an OCaml identifier never maps two different keys to the same
name. That is three layers, each shown not to lose information: escaping the
characters that are illegal, prefixing names that cannot start an identifier,
and suffixing names that collide with an OCaml keyword. The escape character
is chosen so that it can never appear by accident, which is what keeps the
three layers from interfering.

**In one sentence.** The generator refuses its own output if two names
collide, so anything it *does* return is clean — and separately we prove
distinct JSON keys never produce the same identifier, so it never has to.

---

## 2 · Canonicity — *order in, same answer out*

**How.** We did not prove the order does not matter. We removed the place
where order could enter.

Each document is read **from nothing** into its own small set of tables.
Those are then combined pairwise. The combining operation adds counts, unions
the sets of types seen, and ORs the flags — none of which can depend on which
side came first. And every list involved is kept **in sorted order**, so
combining in a different order gives an answer that is literally *equal*, not
merely equivalent.

Once the operation is order-blind in that strong sense, the rest is the
standard fact that folding a list with such an operation gives the same result
for any rearrangement of the list.

The deliberate design choice: each field remembers the **set of types seen
there**, not a running total. A set does not need a proof to be
order-independent.

**In one sentence.** Every document is read independently and the results are
merged with an operation that adds and unions — and since everything is kept
sorted, two orderings give the identical answer, not just equivalent ones.

---

## 3 · Structure preservation — *the nesting survives*

Six clauses. The first four are two directions of one correspondence.

**No edge lost.** Take any nesting in the data. We follow it to the module the
generator emitted for that table, and point at the specific declaration it
produced — the accessor that returns the parent's key, or the one that returns
a list of children.

**No edge invented.** The same reading, backwards: every such declaration in
the file traces back to a nesting that was really in the data.

**Distinct tables, distinct modules.** Without this, two tables could share a
module name and the file's graph would be a *collapsed* copy of the real one —
the same edges, fewer nodes. This comes from the generator's self-check again.

**Rooted.** Every table is reachable from the root by following nestings. This
is the one with teeth, and the reason is a silent failure: an unreachable
table would still get a `CREATE TABLE`, and would then never receive a single
row, because the loader finds children by walking down from the root. Nothing
would report an error. The generator computes reachability over the schema and
refuses if anything is stranded.

**In one sentence.** For every nesting in the data we point at the declaration
it produced and vice versa, and the generator refuses outright if two tables
would share a module name or if any table cannot be reached from the root.

---

## 4 · Principality — *the tightest type that still fits*

**How.** We never widen as we go. Each field remembers the set of types
actually observed there, and only at the very end do we take the least type
above all of them.

Then the two halves are exactly the two defining properties of a *least upper
bound*:

- **it fits the data** — the answer is above every type in the set;
- **it is not too loose** — the answer is below anything else that is also
  above them all.

The real work was proving our type order genuinely has least upper bounds:
that combining types is order-independent, repeat-insensitive, and always
lands on the smallest type above both.

Why the second half matters: "fits the data" alone is nearly free. A column of
integers is adequately described by `float`, or by `string`, or by
`int option`. It is minimality that rules those out, and the two together pin
the type from both sides.

**In one sentence.** We keep the set of types we actually saw and take their
least upper bound — which by definition is above all of them and below any
other type that is.

---

## 5 · Nullability — *`option` exactly where the data needs it*

**How.** Absence is not counted directly. It is computed by subtraction:
visits, minus values seen, minus explicit nulls. In Lean's naturals,
subtraction **truncates at zero** — so if the counts could ever exceed the
visits, a field that documents had omitted would report zero absences, come
out non-optional, and we would emit `string` where the data needs
`string option`. That compiles, and then fails on the first document missing
the field.

So everything rests on one invariant: *values plus nulls never exceed visits*.
Two facts keep it:

- the walk counts the visit **before** looking at any field, so there is
  always room for one more;
- a repeated key inside one object is rejected, so no field can be recorded
  twice in a single visit;
- and merging two runs adds both sides of the inequality, so it survives.

With that, the subtraction is exact rather than truncated, and the optional
flag follows by arithmetic: a field is optional precisely when it carried a
value in fewer than all of its table's visits.

**In one sentence.** We prove every visit is accounted for — value, explicit
null, or absent, and nothing else — which makes a truncating subtraction exact,
and then the `option` marking is just arithmetic on those counts.

---

## The whole

The top-level statement is the conjunction of the five, under two hypotheses:
that inference accepted the corpus, and that the generator accepted the
schema.

**In one sentence.** Each part is proved separately; the top theorem just
states them together so the guarantee can be read without opening nine files.

---

## If they ask what is *not* proved

Answer this one straight — it is the strongest thing you can say.

- **Nothing about data we refuse.** Every guarantee is conditional on both
  stages succeeding. We prove that what comes *out* is correct, not that
  everything sensible gets in. A companion theorem — *if inference accepts a
  corpus, the generator accepts the schema it built* — is stateable and is the
  obvious next one. It does not exist yet.
- **Nothing about rows.** We emit a *description* of tables. The loader that
  fills them is OCaml, outside what the proofs see.
- **Null-only columns.** A field that only ever held `null` has no type
  information to constrain, so the type guarantees hold of it vacuously.
