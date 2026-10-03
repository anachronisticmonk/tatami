/** The stages a corpus passes through, and the Lean function that makes each.
    `type` is the Lean type of the value that comes out. */
export const STAGES = [
  { id: 'json',   label: 'JSON text',        type: 'String',
    by: 'the file, or stdin',
    note: 'Documents as written. One object, or an array of them.' },
  { id: 'doc',    label: 'Parsed documents', type: 'List Doc',
    by: 'Doc.parse, documents',
    note: 'A tree of objects, arrays, numbers, strings, booleans and nulls. Nothing is interpreted yet.' },
  { id: 'perdoc', label: 'One picture per document', type: 'Tables',
    by: 'observeDocument',
    note: 'Each document is walked on its own, from nothing. Every nesting it contains becomes a table; every member records the type it held and whether it was present, null or missing.' },
  { id: 'folded', label: 'One picture of all of them', type: 'Tables',
    by: 'Tables.merge (folded)',
    note: 'The per-document pictures are merged. Counts add, the sets of types seen union, flags disjoin — none of which can depend on which document came first.' },
  { id: 'finished', label: 'Settled', type: 'Tables',
    by: 'inferFinish',
    note: 'What only the whole corpus can settle: a lone object where another document had an array, a member whose types do not join, and the absence counts.' },
  { id: 'schema', label: 'Schema', type: 'Schema',
    by: 'toSchema',
    note: 'The same content as tables, keys and columns, ordered so a module always follows the modules it names. Each table’s parent and keyedness are read off its path.' },
  { id: 'file',   label: 'Signature', type: 'File',
    by: 'gen',
    note: 'Modules and declarations. `gen` checks the schema it was handed, lays out the modules, and then checks its own output before returning it.' },
  { id: 'named',  label: 'One file name per module', type: 'List (String × Module)',
    by: 'Module.fileName',
    note: 'Each module is handed the file it will live in: its own name with the first letter lowered. Module names are already proved distinct, and a module name is a mangled name with its first letter raised — so lowering it again recovers the mangled name exactly, and distinct modules land in distinct files.' },
  { id: 'units',  label: 'Files on disk', type: 'List (String × String)',
    by: 'Decl.print',
    note: 'Each declaration becomes a line of text. This is where a structured value — a type tree — turns into the characters a reader and the OCaml compiler see.' },
]

/** A guarantee covers a span of the pipeline: it is stated about the value
    at `to`, given that everything from `from` onwards succeeded. */
export const BANDS = [
  { id: 'schema_canonical', label: 'Canonicity', from: 'doc', to: 'finished',
    line: 'Shuffle the documents and this value is equal, not merely equivalent.' },
  { id: 'types_principal', label: 'Principality', from: 'doc', to: 'finished',
    line: 'Every member’s type is the least one admitting every value seen there.' },
  { id: 'nullability_sound', label: 'Nullability', from: 'doc', to: 'finished',
    line: 'values + nulls + absent = visits, so the optional marking is exact.' },
  { id: 'signature_wellFormed', label: 'Well-formedness', from: 'schema', to: 'file',
    line: 'No module name, value name or record field is repeated.' },
  { id: 'structure_preserved', label: 'Structure preservation', from: 'schema', to: 'file',
    line: 'The nesting in the data is the graph a reader finds in the signatures.' },
]

/** Transitions nothing is proved about. Stated here rather than left out. */
/** Every step with no theorem across it, and why.

    `kind` separates three very different admissions:
      unstated  the facts are proved; nobody assembled the statement
      open      nobody knows, and the statement is worth wanting
      trusted   deliberately outside the development, like any parser  */
export const GAPS = [
  { from: 'json', to: 'doc', kind: 'trusted',
    why: 'Reading the text. Our reader sits on Lean\u2019s JSON parser, and neither is verified.',
    feasible: 'Possible, and a project of its own: it means writing down what JSON text means \u2014 RFC 8259 \u2014 and proving the parser implements it. It is also the trust everyone extends to a parser; nothing downstream can check it.' },
  { from: 'finished', to: 'schema', kind: 'unstated',
    why: 'A rearrangement: the same content, ordered for emission, with each table\u2019s parent read off its path.',
    feasible: 'Easy, and worth little. The guarantees are stated on either side of it, so a statement across it would repeat them.' },
  { from: 'file', to: 'named', kind: 'unstated',
    why: 'Which file each module lands in.',
    feasible: 'Cheap. Module names are already proved distinct, and a module name is a mangled name with its first letter raised \u2014 lowering it again recovers the mangled name exactly. Both halves exist; the one-line statement about the file list does not.' },
  { from: 'named', to: 'units', kind: 'open',
    why: 'Turning a declaration into text. The theorems are about structured values; every reader, and the OCaml compiler, sees characters.',
    feasible: 'The obvious statement \u2014 distinct declarations print differently \u2014 is false as it stands: `int` and a type literally named `int` print the same. The statement worth wanting is a round trip, parse (print d) = d, which needs a parser in Lean and no OCaml semantics at all. Proving the text *means* what the tree means would need OCaml\u2019s grammar and type system formalised, which is years of work and not the right goal.' },
]

/** What the guarantees are silent about even where they do apply. */
export const CAVEATS = [
  ['Only what is emitted', 'Every guarantee assumes inference and generation each returned ok. Both refuse inputs. Nothing says a reasonable corpus is accepted \u2014 the companion statement, that generation accepts any schema inference built, does not exist.'],
  ['Only the signature', 'Well-formedness and structure preservation are stated of the .mli declarations. The .ml is checked against them by the OCaml compiler. The row modules and the loader are constrained only in that their names are distinct, and that loaders declare nothing.'],
  ['Not the DDL', 'ddlOf, constraintsOf and storageTy appear in the JSON report and no proof mentions them.'],
  ['Not the rows', 'Tatami emits a description of tables. The loader that fills them is OCaml, outside what the proofs see.'],
]
