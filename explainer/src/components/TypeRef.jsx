import React, { createContext, useContext } from 'react'
import { TYPES, isType } from '../data/types.js'

export const TypeCtx = createContext(() => {})

/** A clickable type name. Opens the declaration panel. */
export function T({ n, children }) {
  const open = useContext(TypeCtx)
  if (!isType(n)) return <span className="mono">{children ?? n}</span>
  return (
    <button className="leanref" onClick={() => open(n)} title={`Show ${n}`}>
      {children ?? n}
    </button>
  )
}

/** A Lean type as written — `List (Path × TableObs)` — with every scraped
    name in it made clickable and everything else left as text. Splitting on
    identifiers rather than listing the links by hand means a type that gains
    a component gains a link with it. */
export function TypeExpr({ s }) {
  const parts = String(s).split(/([A-Za-z_][A-Za-z0-9_'.]*)/g)
  return (
    <>
      {parts.map((p, i) =>
        isType(p) ? <T key={i} n={p} /> : <span key={i}>{p}</span>
      )}
    </>
  )
}

/** The declaration itself, named and labelled with its kind — the thing the
    value on screen inhabits. */
export function TypeChip({ n }) {
  const open = useContext(TypeCtx)
  const t = TYPES[n]
  if (!t) return null
  return (
    <button className="typeref" onClick={() => open(n)} title={`${t.file}:${t.line}`}>
      <span className="tr-kind">{t.kind}</span>
      <span className="mono">{n}</span>
    </button>
  )
}
