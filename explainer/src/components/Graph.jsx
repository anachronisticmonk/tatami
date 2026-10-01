import React, { useMemo, useState } from 'react'
import { DECLS, EDGES, AREAS, ROOTS, closure, layers, uses, usedBy } from '../data/graph.js'

const NW = 196, NH = 26, VGAP = 7, HGAP = 74, PAD = 18

/** Lay the reachable subgraph out in columns: the root on the left, and each
    theorem one column to the right of everything that uses it. */
function layout(root) {
  const inSub = closure(root)
  inSub.add(root)
  const depth = layers(root)
  const cols = []
  for (const n of inSub) {
    const d = depth.get(n) ?? 0
    ;(cols[d] ||= []).push(n)
  }
  cols.forEach((c) => c.sort((a, b) =>
    (DECLS[a]?.area ?? '').localeCompare(DECLS[b]?.area ?? '') || a.localeCompare(b)))

  const pos = new Map()
  const tallest = Math.max(...cols.map((c) => c.length), 1)
  cols.forEach((col, i) => {
    // centre short columns against the tallest one
    const off = ((tallest - col.length) * (NH + VGAP)) / 2
    col.forEach((n, j) => {
      pos.set(n, { x: PAD + i * (NW + HGAP), y: PAD + off + j * (NH + VGAP) })
    })
  })
  const edges = EDGES.filter(([a, b]) => inSub.has(a) && inSub.has(b) && pos.has(a) && pos.has(b))
  return {
    pos, edges, cols,
    w: PAD * 2 + cols.length * (NW + HGAP) - HGAP,
    h: PAD * 2 + tallest * (NH + VGAP) - VGAP,
  }
}

export default function Graph({ selected, onSelect }) {
  const [rootId, setRootId] = useState('nullability_sound')
  const [hover, setHover] = useState(null)
  const g = useMemo(() => layout(rootId), [rootId])
  const root = ROOTS.find((r) => r.id === rootId)

  const lit = hover ?? selected
  const near = useMemo(() => {
    if (!lit) return null
    return new Set([lit, ...uses(lit), ...usedBy(lit)])
  }, [lit])

  return (
    <div>
      <div className="eyebrow">Lean map</div>
      <h2 className="title">What each guarantee rests on</h2>
      <p className="lede">
        Every box is a real theorem in <code>Proofs/</code>. An arrow means the
        proof on the left <em>names</em> the theorem on the right — scraped from
        the proof bodies, with comments and strings stripped. It is what each
        proof mentions, not a kernel dependency graph.
      </p>

      <div className="rootbar">
        {ROOTS.map((r) => (
          <button key={r.id}
                  className={`rootbtn${r.id === rootId ? ' on' : ''}`}
                  onClick={() => setRootId(r.id)}>
            {r.label}
            <span className="rootcount">{closure(r.id).size}</span>
          </button>
        ))}
      </div>
      <p className="small" style={{ marginTop: 10 }}>{root?.blurb}</p>

      <div className="graphwrap">
        <svg width={g.w} height={g.h} role="img" aria-label={`Dependencies of ${rootId}`}>
          <defs>
            <marker id="ar" viewBox="0 0 8 8" refX="7" refY="4"
                    markerWidth="7" markerHeight="7" orient="auto">
              <path d="M0 0 L8 4 L0 8 z" style={{ fill: 'var(--faint)' }} />
            </marker>
          </defs>
          {g.edges.map(([a, b], i) => {
            const p = g.pos.get(a), q = g.pos.get(b)
            const x1 = p.x + NW, y1 = p.y + NH / 2
            const x2 = q.x, y2 = q.y + NH / 2
            const mx = (x1 + x2) / 2
            const on = near && (near.has(a) && near.has(b) && (a === lit || b === lit))
            return (
              <path key={i} d={`M${x1},${y1} C${mx},${y1} ${mx},${y2} ${x2},${y2}`}
                    style={{ fill: 'none', stroke: on ? 'var(--accent)' : 'var(--edge)' }}
                    strokeWidth={on ? 1.8 : 1}
                    opacity={near && !on ? 0.3 : 1}
                    markerEnd={on ? 'url(#ar)' : undefined} />
            )
          })}
          {[...g.pos.entries()].map(([n, p]) => {
            const d = DECLS[n]
            const colour = AREAS[d?.area]?.color ?? 'var(--faint)'
            const isRoot = n === rootId
            const dim = near && !near.has(n)
            return (
              <g key={n} transform={`translate(${p.x},${p.y})`}
                 opacity={dim ? 0.3 : 1}
                 onMouseEnter={() => setHover(n)} onMouseLeave={() => setHover(null)}
                 onClick={() => onSelect(n)} style={{ cursor: 'pointer' }}>
                <rect width={NW} height={NH}
                      style={{
                        fill: isRoot ? 'var(--accent-bg)'
                              : n === selected ? 'var(--sunk)' : 'var(--bg)',
                        stroke: isRoot ? 'var(--accent)' : colour,
                      }}
                      strokeWidth={isRoot || n === selected ? 2 : 1.2} />
                <rect width="4" height={NH} style={{ fill: colour }} />
                <text x="11" y={NH / 2 + 4} fontSize="11.5"
                      fontFamily="var(--mono)"
                      style={{ fill: isRoot ? 'var(--accent)' : 'var(--ink)' }}>
                  {n.length > 26 ? n.slice(0, 25) + '…' : n}
                </text>
              </g>
            )
          })}
        </svg>
      </div>

      <div className="legend">
        {Object.entries(AREAS).filter(([k]) =>
          [...closure(rootId), rootId].some((n) => DECLS[n]?.area === k)
        ).map(([k, v]) => (
          <span key={k}><i style={{ background: v.color }} />{v.label}</span>
        ))}
      </div>
      <p className="small" style={{ marginTop: 12 }}>
        Click a box for its Lean source. Hover to pick out its own edges.
      </p>
    </div>
  )
}
