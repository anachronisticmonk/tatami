import React from 'react'
import Pipeline from '../components/Pipeline.jsx'
import { GAPS, CAVEATS, STAGES, BANDS } from '../data/pipeline.js'
import L from '../components/LeanRef.jsx'

const name = (id) => STAGES.find((s) => s.id === id)?.label
const KIND = {
  proved:   ['proved',   'A theorem covers this step.'],
  unstated: ['unstated', 'The facts are proved. Nobody assembled the statement.'],
  open:     ['open',     'Nobody knows. The statement is worth wanting.'],
  trusted:  ['trusted',  'Deliberately outside the development.'],
}

/** Every transition in order, proved or not, so the page cannot quietly omit
    one. Built from the two lists rather than typed out twice. */
function rows() {
  return STAGES.slice(1).map((s, i) => {
    const from = STAGES[i].id
    const gap = GAPS.find((g) => g.from === from && g.to === s.id)
    const covers = BANDS.filter((b) => {
      const a = STAGES.findIndex((x) => x.id === b.from)
      const z = STAGES.findIndex((x) => x.id === b.to)
      return i >= a && i + 1 <= z
    })
    return { from, to: s.id, by: s.by, gap, covers }
  })
}

export default function PipelineSection() {
  return (
    <div>
      <div className="eyebrow">The pipeline</div>
      <h2 className="title">What is proved, and what is not</h2>
      <p className="lede">
        Nine stages between the text on disk and the files that come out. Four
        of the eight steps have a theorem across them; four do not, and each of
        those four is a different kind of admission.
      </p>

      <Pipeline />

      <h3>Every step, in order</h3>
      <table className="t">
        <thead><tr>
          <th>step</th><th>by</th><th></th><th>what holds, or why nothing does</th>
        </tr></thead>
        <tbody>
          {rows().map((r) => {
            const kind = r.gap ? r.gap.kind : 'proved'
            return (
              <tr key={r.to}>
                <td className="mono" style={{ whiteSpace: 'nowrap' }}>
                  {name(r.from)} → {name(r.to)}
                </td>
                <td className="mono small">{r.by}</td>
                <td><span className={`pipe-gapmark ${kind}`}>{KIND[kind][0]}</span></td>
                <td>
                  {r.gap
                    ? r.gap.why
                    : r.covers.map((b, i) => (
                        <React.Fragment key={b.id}>
                          {i ? ', ' : ''}<L n={b.id}>{b.label}</L>
                        </React.Fragment>
                      ))}
                </td>
              </tr>
            )
          })}
        </tbody>
      </table>

      <h3>The four we do not prove, and whether we could</h3>
      <p>
        Stated plainly rather than implied. <b>Unstated</b>, <b>open</b> and{' '}
        <b>trusted</b> are three different things, and running them together
        would be the dishonest part.
      </p>
      {GAPS.map((g) => (
        <div className="card" key={g.to}>
          <div className="gap-head">
            <span className={`pipe-gapmark ${g.kind}`}>{KIND[g.kind][0]}</span>
            <code>{name(g.from)} → {name(g.to)}</code>
          </div>
          <p><b>{g.why}</b></p>
          <p className="small">{g.feasible}</p>
        </div>
      ))}

      <h3>And where a theorem does apply, what it still does not say</h3>
      <table className="t">
        <thead><tr><th>caveat</th><th></th></tr></thead>
        <tbody>
          {CAVEATS.map(([k, v]) => (
            <tr key={k}><td style={{ whiteSpace: 'nowrap' }}><b>{k}</b></td><td>{v}</td></tr>
          ))}
        </tbody>
      </table>

      <div className="note">
        <b>One correction worth making out loud.</b> The three inference
        guarantees begin at <em>parsed documents</em>, not at the JSON text —
        they quantify over a <code>List Doc</code>. Reading the file into that
        list is the trusted step, and it sits before every theorem in the
        development.
      </div>
    </div>
  )
}
