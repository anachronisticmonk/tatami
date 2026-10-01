import React, { useState, useRef, useLayoutEffect } from 'react'
import { STAGES, BANDS, GAPS } from '../data/pipeline.js'
import L from './LeanRef.jsx'

/* Guarantees that cover the same stretch are drawn as one bracket, so the
   spans stay legible where several overlap. */
const SPANS = Object.values(BANDS.reduce((acc, b) => {
  const key = `${b.from}>${b.to}`
  ;(acc[key] ||= { key, from: b.from, to: b.to, items: [] }).items.push(b)
  return acc
}, {}))

export default function Pipeline() {
  const [open, setOpen] = useState(null)
  const rail = useRef(null)
  const cells = useRef({})
  const [box, setBox] = useState({})

  /* Bands are drawn against the stages they cover, so the span is visible
     rather than described. Measured because the stages are variable height. */
  useLayoutEffect(() => {
    const measure = () => {
      if (!rail.current) return
      const base = rail.current.getBoundingClientRect().top
      const next = {}
      for (const [id, el] of Object.entries(cells.current)) {
        if (!el) continue
        const r = el.getBoundingClientRect()
        next[id] = { top: r.top - base, bottom: r.bottom - base }
      }
      setBox(next)
    }
    measure()
    const ro = new ResizeObserver(measure)
    if (rail.current) ro.observe(rail.current)
    window.addEventListener('resize', measure)
    return () => { ro.disconnect(); window.removeEventListener('resize', measure) }
  }, [open])

  return (
    <div className="pipe">
      <div className="pipe-rail" ref={rail}>
        {STAGES.map((s, i) => {
          const gap = GAPS.find((g) => g.to === s.id)
          return (
            <React.Fragment key={s.id}>
              {i > 0 && (
                <div className={`pipe-arrow${gap ? ' gap' : ''}`}>
                  <span className="pipe-by mono">{s.by}</span>
                  {gap && (
                    <span className={`pipe-gapmark ${gap.kind}`} title={gap.why}>
                      {gap.kind === 'open' ? 'not proved' : 'unstated'}
                    </span>
                  )}
                </div>
              )}
              <button ref={(el) => { cells.current[s.id] = el }}
                      className={`pipe-stage${open === s.id ? ' on' : ''}`}
                      onClick={() => setOpen(open === s.id ? null : s.id)}>
                <span className="pipe-label">{s.label}</span>
                <span className="pipe-type mono">{s.type}</span>
              </button>
              {open === s.id && <div className="pipe-note">{s.note}</div>}
            </React.Fragment>
          )
        })}
      </div>

      <div className="pipe-bands" style={{ height: box[STAGES.at(-1).id]?.bottom ?? 'auto' }}>
        {SPANS.map((sp) => {
          const a = box[sp.from], z = box[sp.to]
          return (
            <div key={sp.key} className="band"
                 style={a && z ? { top: a.top, height: z.bottom - a.top } : undefined}>
              <div className="band-bar" />
              <div className="band-text">
                <div className="band-span mono">
                  {STAGES.find((x) => x.id === sp.from).label} &rarr;{' '}
                  {STAGES.find((x) => x.id === sp.to).label}
                </div>
                {sp.items.map((b) => (
                  <div className="band-item" key={b.id}>
                    <L n={b.id}>{b.label}</L>
                    <p className="small">{b.line}</p>
                  </div>
                ))}
              </div>
            </div>
          )
        })}
      </div>
    </div>
  )
}
