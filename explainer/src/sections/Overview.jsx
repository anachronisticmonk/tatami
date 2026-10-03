import React from 'react'
import { COUNTS, ROOTS } from '../data/graph.js'
import L from '../components/LeanRef.jsx'
import LeanCode from '../components/LeanCode.jsx'

export default function Overview({ go }) {
  return (
    <div>
      <div className="eyebrow">Tatami</div>
      <h2 className="title">Schemaless JSON in. Typed OCaml out. Proved in Lean 4.</h2>
      <p className="lede">
        Tatami reads a corpus of JSON that declares no schema, works out what
        schema the documents <em>have</em>, and emits an OCaml module per table.
        This is a reader for the Lean half: what the pipeline does, and exactly
        which part of it each theorem covers.
      </p>

      <div className="stats">
        <div><b>{COUNTS.theorems}</b><span>theorems and lemmas</span></div>
        <div><b>5</b><span>named guarantees</span></div>
        <div><b>0</b><span>uses of <code>sorry</code></span></div>
      </div>

      <h3>One theorem, in five parts</h3>
      <p>
        Everything rests on <L n="pipeline_correct" />. It says: for a corpus
        inference accepted and a schema the generator accepted, all five of
        these hold at once.
      </p>
      <ul>
        {ROOTS.map((r) => (
          <li key={r.id}><L n={r.id}>{r.label}</L> — {r.blurb}</li>
        ))}
      </ul>

      <h3>What is conditional about it</h3>
      <p>
        Both hypotheses matter and are worth saying out loud. Every guarantee
        assumes inference and generation each returned <code>ok</code>, and both
        refuse inputs — a member holding two types with no common type, a schema
        whose tree a signature cannot express. <b>The promise is about what is
        emitted, not about what is accepted.</b>
      </p>
      <LeanCode src={`theorem pipeline_correct (cfg : Config) (nm : Naming) (ds : List Doc)
    (ts : Tables) (f : File)
    (hinf : inferCorpus cfg ds = .ok ts)
    (hgen : gen nm (toSchema ts) = .ok f) :
    f.WellFormed ∧ … ∧ … ∧ … ∧ …`} />

      <h3>How to read this</h3>
      <p>
        <b>The pipeline</b> lays out the stages a corpus passes through and
        marks which transition each guarantee covers — including the two that
        nothing covers. <b>A worked example</b> runs one small corpus through
        every stage, printed straight from the real Lean functions.{' '}
        <b>The Lean map</b> is the dependency tree under each guarantee.
      </p>
      <p className="small">
        Nothing on these pages is transcribed by hand. Theorem statements and
        sources are scraped from <code>Proofs/*.lean</code>; the worked example
        is printed by running the pipeline itself.
      </p>
    </div>
  )
}
