import React, { useEffect } from 'react'
import { TYPES, mentionedBy, KIND_LABEL } from '../data/types.js'
import LeanCode from './LeanCode.jsx'

/** A Lean docstring, rendered. Paragraphs split on a blank line; `code` and
    *emphasis* are the only markup the sources use, so they are the only
    markup read. Everything else is text. */
function prose(doc) {
  return doc.split(/\n\s*\n/).map((para, i) => (
    <p key={i}>
      {para.split(/(`[^`]+`|\*\*[^*]+\*\*|\*[^*\n]+\*)/g).map((piece, j) => {
        if (/^`[^`]+`$/.test(piece)) return <code key={j}>{piece.slice(1, -1)}</code>
        if (/^\*\*[^*]+\*\*$/.test(piece)) return <strong key={j}>{piece.slice(2, -2)}</strong>
        if (/^\*[^*]+\*$/.test(piece)) return <em key={j}>{piece.slice(1, -1)}</em>
        return <span key={j}>{piece}</span>
      })}
    </p>
  ))
}

export default function TypePanel({ name, onClose, onOpen }) {
  useEffect(() => {
    if (!name) return
    const onKey = (e) => { if (e.key === 'Escape') onClose() }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [name, onClose])

  if (!name) return null
  const t = TYPES[name]
  if (!t) return null

  return (
    <>
      <div className="panel-scrim" onClick={onClose} />
      <aside className="decl-panel" role="dialog" aria-label={`Declaration ${name}`}>
        <button className="decl-close" onClick={onClose} aria-label="Close">×</button>
        <div className="decl-head">
          <span className="decl-area decl-kind">{KIND_LABEL[t.kind] ?? t.kind}</span>
          <h3 className="mono">{name}</h3>
          <p className="small mono">{t.file}:{t.line}</p>
        </div>

        {t.doc ? <div className="decl-gloss decl-doc">{prose(t.doc)}</div> : null}

        <LeanCode src={t.src} />

        {[['It names', t.mentions || []], ['Named by', mentionedBy(name)]].map(
          ([label, list]) =>
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
        )}
      </aside>
    </>
  )
}
