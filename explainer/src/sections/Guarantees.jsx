import React, { useState } from 'react'
import { ROOTS, DECLS, closure, uses } from '../data/graph.js'
import LeanCode from '../components/LeanCode.jsx'
import L from '../components/LeanRef.jsx'

/** How each one is proved, in plain words. No lemma names: naming the
    scaffolding answers a question nobody asked. */
const HOW = {
  signature_wellFormed: [
    'The generator inspects its own output before returning it, and refuses anything that repeats a module name, a value name inside a module, or a field inside a record. So the proof is one step: it gave us a file, therefore the check passed, therefore nothing repeats.',
    'Separately — and this is the part with real content — turning a JSON key into an OCaml identifier is shown never to map two different keys to the same name. That is why the check never has to fire on real input.',
  ],
  schema_canonical: [
    'We did not prove the order does not matter. We removed the place where order could enter.',
    'Each document is read from nothing into its own small set of tables. Those are combined with an operation that adds counts, unions the sets of types seen and ORs the flags — none of which can depend on which side came first. Every list is kept sorted, so combining in a different order gives an answer that is literally equal, not merely equivalent.',
    'After that it is the standard fact that folding with such an operation is unchanged by rearranging the list.',
  ],
  structure_preserved: [
    'Six clauses. No edge lost: take any nesting in the data, follow it to the module the generator emitted, and point at the declaration it produced. No edge invented: the same reading, backwards.',
    'Distinct tables get distinct modules — without it the file’s graph could be a collapsed copy of the real one, the same edges over fewer nodes.',
    'And rooted: every table is reachable from the root. That is the one with teeth, because the failure is silent — an unreachable table would still get a CREATE TABLE and then never receive a row.',
  ],
  types_principal: [
    'We never widen as we go. Each member remembers the set of types actually seen there, and only at the very end do we take the least type above all of them.',
    'The two halves are then the two defining properties of a least upper bound: it is above everything in the set, and below anything else that is also above them all. The work was proving our type order really has them.',
    'Adequacy alone is nearly free — a column of integers is adequately described by float, or string, or int option. Minimality is what rules those out.',
  ],
  nullability_sound: [
    'Absence is not counted directly. It is computed by subtraction — visits, minus values, minus explicit nulls — and in Lean’s naturals subtraction truncates at zero.',
    'So everything rests on one invariant: values plus nulls never exceeds visits. The walk counts the visit before looking at any field, a repeated key in one object is rejected, and merging two runs adds both sides — so it survives.',
    'With that the subtraction is exact rather than truncated, and the optional flag follows by arithmetic.',
  ],
}

export default function Guarantees() {
  const [open, setOpen] = useState('nullability_sound')
  return (
    <div>
      <div className="eyebrow">The guarantees</div>
      <h2 className="title">Five statements, and how each is proved</h2>
      <p className="lede">
        The statements are scraped from <code>Proofs/Correctness.lean</code>.
        The explanations are in plain words and name no helper lemmas — those
        are in the Lean map, for when someone wants them.
      </p>

      {ROOTS.map((r) => {
        const d = DECLS[r.id]
        const on = open === r.id
        return (
          <div className={`gcard${on ? ' on' : ''}`} key={r.id}>
            <button className="gcard-head" onClick={() => setOpen(on ? null : r.id)}>
              <span className="gcard-title">{r.label}</span>
              <span className="gcard-sub">{r.blurb}</span>
              <span className="gcard-count mono">{closure(r.id).size} theorems</span>
            </button>
            {on && (
              <div className="gcard-body">
                {d && <LeanCode src={d.stmt} />}
                <h3 style={{ fontSize: 16 }}>How it is proved</h3>
                {HOW[r.id].map((p, i) => <p key={i}>{p}</p>)}
                <p className="small">
                  Rests directly on{' '}
                  {uses(r.id).map((n, i) => (
                    <React.Fragment key={n}>{i ? ', ' : ''}<L n={n} /></React.Fragment>
                  ))}.
                </p>
              </div>
            )}
          </div>
        )
      })}

      <div className="note">
        <b>Three of the five share one trick.</b> The generator checks its own
        output and refuses anything malformed, so those proofs are an inversion:
        it returned a file, therefore the check passed. The objection writes
        itself — <em>so you proved the checker agrees with itself?</em> No: the
        check is a program returning yes or no, the theorem is a statement about
        all files, and the work is proving the first implies the second.
      </div>
    </div>
  )
}
