import React, { useEffect } from 'react'
import { DECLS, uses, usedBy, AREAS } from '../data/graph.js'
import LeanCode from './LeanCode.jsx'
import { GLOSS } from '../data/gloss.js'

export default function DeclPanel({ name, onClose, onOpen }) {
  useEffect(() => {
    if (!name) return
    const onKey = (e) => { if (e.key === 'Escape') onClose() }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [name, onClose])

  if (!name) return null
  const d = DECLS[name]
  const area = AREAS[d?.area]

  return (
    <>
      <div className="panel-scrim" onClick={onClose} />
      <aside className="decl-panel" role="dialog" aria-label={`Theorem ${name}`}>
        <button className="decl-close" onClick={onClose} aria-label="Close">×</button>
        <div className="decl-head">
          {area && <span className="decl-area" style={{ background: area.color }}>{area.label}</span>}
          <h3 className="mono">{name}</h3>
          {d && <p className="small mono">{d.file}:{d.line}</p>}
        </div>

        {GLOSS[name] && <p className="decl-gloss">{GLOSS[name]}</p>}

        {d
          ? <LeanCode src={d.full} />
          : <p className="small">Not scraped — it is not a theorem in <code>Proofs/</code>.</p>}

        {[['Its proof names', uses(name)], ['Named by', usedBy(name)]].map(([label, list]) => (
          list.length > 0 && (
            <div className="decl-rel" key={label}>
              <div className="decl-rel-label">{label}</div>
              <div className="decl-chips">
                {list.map((o) => (
                  <button key={o} className="leanref" onClick={() => onOpen(o)}>{o}</button>
                ))}
              </div>
            </div>
          )
        ))}
      </aside>
    </>
  )
}
