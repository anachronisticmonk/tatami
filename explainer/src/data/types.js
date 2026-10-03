import raw from './types.json'

/** Every `structure`, `inductive` and `abbrev` the pipeline passes between
    stages, scraped from the Lean sources by `scripts/extract-types.py`. */
export const TYPES = raw.types
export const TYPE_ORDER = raw.order

export const isType = (n) => Object.prototype.hasOwnProperty.call(TYPES, n)

/** Declarations whose body names this one. The reverse of `mentions`, so a
    panel can be walked in both directions the way a theorem's can. */
export const mentionedBy = (n) =>
  TYPE_ORDER.filter((q) => (TYPES[q].mentions || []).indexOf(n) >= 0)

/** What a kind is called in the panel's badge. */
export const KIND_LABEL = {
  structure: 'structure',
  inductive: 'inductive',
  abbrev: 'abbreviation',
}
