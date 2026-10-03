import React from 'react'
import L from '../components/LeanRef.jsx'

export default function Scope() {
  return (
    <div>
      <div className="eyebrow">Scope</div>
      <h2 className="title">What is not proved</h2>
      <p className="lede">
        Worth reading before the guarantees, not after. Each of these is
        stateable; none of them is stated.
      </p>

      <h3>Nothing about a corpus the program refuses</h3>
      <p>
        Every guarantee is conditional on both stages returning <code>ok</code>.
        There is no theorem saying inference accepts everything reasonable, or
        that a schema inference produced is one the generator will accept. The
        companion result — <em>if inference accepts a corpus, generation accepts
        the schema it built</em> — is the obvious next one and does not exist.
      </p>

      <h3>Nothing about rows</h3>
      <p>
        Tatami emits a <em>description</em> of tables. The loader that fills
        them is OCaml, outside what the proofs see. A round-trip theorem would
        need the shredder verified first — and could only ever hold up to member
        order, explicit <code>null</code> versus an absent key, and the written
        form of a number, all three of which are discarded by design.
      </p>

      <h3>The signatures, not the implementations</h3>
      <p>
        Well-formedness is stated of the <code>.mli</code> declarations only.
        The <code>.ml</code> is checked against it by the OCaml compiler, so
        proving it again in Lean would duplicate <code>ocamlc</code>. The row
        modules and the loader are constrained only in that their module names
        are distinct — and that loaders declare nothing, which is load-bearing:
        without it a loader could fake a nesting edge and{' '}
        <L n="structure_preserved" /> would be false.
      </p>

      <h3>The DDL</h3>
      <p>
        <code>ddlOf</code>, <code>constraintsOf</code> and{' '}
        <code>storageTy</code> appear in the JSON report and no proof mentions
        them. The Postgres side rests on nothing.
      </p>

      <h3>Null-only columns</h3>
      <p>
        A member that only ever held <code>null</code> has an empty set of seen
        types, so both halves of <L n="types_principal" /> hold vacuously. There
        is no type information to constrain — but nothing constrains it either.
      </p>
    </div>
  )
}
