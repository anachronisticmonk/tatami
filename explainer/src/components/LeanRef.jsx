import React, { createContext, useContext } from 'react'

export const DeclCtx = createContext(() => {})

/** A clickable theorem name. Opens the source panel. */
export default function L({ n, children }) {
  const open = useContext(DeclCtx)
  return (
    <button className="leanref" onClick={() => open(n)} title={`Show ${n}`}>
      {children ?? n}
    </button>
  )
}
