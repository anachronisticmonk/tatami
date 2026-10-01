import raw from './graph.json'

export const DECLS = raw.decls
export const EDGES = raw.edges
export const ORDER = raw.order
export const COUNTS = raw.counts

/** Which proof file a theorem lives in, and how that file is grouped. */
export const AREAS = {
  Correctness: { label: 'The guarantee',   color: 'var(--a-correct)' },
  Tree:        { label: 'Structure',       color: 'var(--a-tree)' },
  Inference:   { label: 'Inference',       color: 'var(--a-infer)' },
  Counts:      { label: 'Counting',        color: 'var(--a-counts)' },
  Wellformed:  { label: 'Well-formedness', color: 'var(--a-wf)' },
  Mangle:      { label: 'Names',           color: 'var(--a-mangle)' },
  Lattice:     { label: 'Type order',      color: 'var(--a-lattice)' },
  Merge:       { label: 'Merging',         color: 'var(--a-merge)' },
  Walk:        { label: 'The walk',        color: 'var(--a-walk)' },
  Sorted:      { label: 'Sorted lists',    color: 'var(--a-sorted)' },
  Order:       { label: 'Key orders',      color: 'var(--a-order)' },
  Spec:        { label: 'Specification',   color: 'var(--a-spec)' },
}

const OUT = new Map()
for (const [a, b] of EDGES) {
  if (!OUT.has(a)) OUT.set(a, [])
  OUT.get(a).push(b)
}
export const uses = (n) => OUT.get(n) ?? []
export const usedBy = (n) => EDGES.filter(([, b]) => b === n).map(([a]) => a)

/** Everything a theorem's proof reaches, transitively. */
export function closure(root) {
  const seen = new Set(), stack = [root]
  while (stack.length) {
    for (const y of uses(stack.pop())) if (!seen.has(y)) { seen.add(y); stack.push(y) }
  }
  return seen
}

/** Longest distance from the root, so a theorem sits below everything that
    uses it. Cycles cannot occur — a Lean proof cannot use a later theorem. */
export function layers(root) {
  const depth = new Map([[root, 0]])
  let changed = true, guard = 0
  while (changed && guard++ < 200) {
    changed = false
    for (const [a, b] of EDGES) {
      if (!depth.has(a)) continue
      const d = depth.get(a) + 1
      if (!depth.has(b) || depth.get(b) < d) { depth.set(b, d); changed = true }
    }
  }
  return depth
}

export const ROOTS = [
  { id: 'signature_wellFormed', label: 'Well-formedness',
    blurb: 'The names it emits are legal, and no two collide.' },
  { id: 'schema_canonical', label: 'Canonicity',
    blurb: 'Shuffle the corpus and the answer is equal, not merely equivalent.' },
  { id: 'structure_preserved', label: 'Structure preservation',
    blurb: 'The nesting in the data is the graph in the signatures.' },
  { id: 'types_principal', label: 'Principality',
    blurb: 'Every type is the tightest one that still fits the data.' },
  { id: 'nullability_sound', label: 'Nullability',
    blurb: 'A field is optional exactly where some document lacked a value.' },
]
