import React, { useState } from 'react'
import stages from '../data/stages.json'
import corpus from '../data/corpus.json'
import { TablesView, SchemaView, FileView } from '../components/Stage.jsx'
import LeanCode from '../components/LeanCode.jsx'
import L from '../components/LeanRef.jsx'
import { TypeExpr, TypeChip } from '../components/TypeRef.jsx'

const CORPUS = JSON.stringify(corpus, null, 2)

/** One entry per call the pipeline makes, in source order. `call` is the line
    from `Main.lean` or `Tatami/Infer.lean` that produces the value, `type` is
    what that line binds, and `decls` are the Lean declarations the value is
    built out of -- the type itself first, then what it unfolds to. Every name
    in either is clickable: the declaration opens in a panel, the same way a
    theorem does on the Lean map. */
const STEPS = [
  { id: 'json', n: '1', label: 'The corpus',
    call: 'let input ← (← IO.getStdin).readToEnd', type: 'String', decls: [] },
  { id: 'docs', n: '2', label: 'Parsed',
    call: 'let docs ← documents j', type: 'List Doc', decls: ['Doc'] },
  { id: 'perdoc', n: '3', label: 'Each document alone',
    call: 'observeDocument cfg d', type: 'Tables',
    decls: ['Tables', 'Path', 'Seg', 'TableObs', 'Obs', 'Ty'] },
  { id: 'folded', n: '4', label: 'Merged',
    call: 'ts ← inferStep cfg ts d', type: 'Tables',
    decls: ['Tables', 'TableObs', 'Obs', 'Ty'] },
  { id: 'finished', n: '5', label: 'Settled',
    call: 'let tables ← inferFinish cfg tables', type: 'Tables',
    decls: ['Tables', 'TableObs', 'Obs', 'Ty'] },
  { id: 'naming', n: '6', label: 'Names',
    call: 'let nm : Naming := { root := rootModuleName cfg.root, tables := cfg.names }',
    type: 'Naming', decls: ['Naming', 'Config', 'Path'] },
  { id: 'schema', n: '7', label: 'The schema',
    call: 'let schema := toSchema tables', type: 'Schema',
    decls: ['Schema', 'Table', 'Column', 'Field', 'Ty'] },
  { id: 'file', n: '8', label: 'The signature',
    call: 'let file ← gen nm schema', type: 'File',
    decls: ['File', 'Module', 'Decl', 'TyExpr', 'RecField'] },
  { id: 'units', n: '9', label: 'The files',
    call: 'file.units', type: 'List (String × String)', decls: [] },
  { id: 'outcome', n: '10', label: 'What finish returns',
    call: 'return { naming := nm, units := file.units, ocaml := file.print, tables, documents }',
    type: 'Outcome', decls: ['Outcome', 'Naming', 'Tables'] },
]

/** Steps that have both a drawn view and a raw one. The rest have only the
    raw value, and the toggle is not offered. */
const BOTH = new Set(['perdoc', 'folded', 'finished', 'schema', 'file'])

function Views({ step, view, setView }) {
  if (!BOTH.has(step)) return null
  return (
    <div className="unitbar">
      {[['drawn', 'as a picture'], ['raw', 'as a Lean value']].map(([k, lbl]) => (
        <button key={k} className={`unitbtn${view === k ? ' on' : ''}`}
                onClick={() => setView(k)}>{lbl}</button>
      ))}
    </div>
  )
}

export default function Walkthrough() {
  const [step, setStep] = useState('json')
  const [view, setView] = useState('drawn')
  const [unit, setUnit] = useState(stages.units[0].name)
  const u = stages.units.find((x) => x.name === unit) ?? stages.units[0]
  const cur = STEPS.find((s) => s.id === step)
  const raw = view === 'raw'

  return (
    <div>
      <div className="eyebrow">A worked example</div>
      <h2 className="title">Two documents, all the way through</h2>
      <p className="lede">
        Every value below is printed by running the real pipeline on the corpus
        in step 1 — the same functions the theorems are about. Nothing is
        hand-written. Each step is one call, and shows the value that call
        returns: drawn as a picture, or written out as the Lean value itself.
        Under each call are the declarations that value inhabits — click one to
        read it where it is declared.
      </p>

      <div className="steps">
        {STEPS.map((s) => (
          <button key={s.id} className={`step${step === s.id ? ' on' : ''}`}
                  onClick={() => setStep(s.id)}>
            <span className="step-n mono">{s.n}</span>{s.label}
          </button>
        ))}
      </div>

      <div className="callline">
        <div className="callline-src">
          <code className="mono">{cur.call}</code>
          <span className="callty mono">: <TypeExpr s={cur.type} /></span>
        </div>
        {cur.decls.length > 0 && (
          <div className="callline-decls">
            <span className="cl-label">
              {cur.decls.length === 1 ? 'declared as' : 'built out of'}
            </span>
            {cur.decls.map((n) => <TypeChip key={n} n={n} />)}
          </div>
        )}
      </div>

      {step === 'json' && (
        <div>
          <h3>The corpus</h3>
          <p>
            Two documents, chosen so that something changes at every step
            below. <code>meta</code> is an object in the first and missing from
            the second. <code>runs</code> is a lone object in the first and an
            array of objects in the second — the shape that has to be
            collapsed. And <code>ms</code> is an integer in one place and a
            decimal in another.
          </p>
          <LeanCode src={CORPUS} />
        </div>
      )}

      {step === 'docs' && (
        <div>
          <h3>One level of array comes off</h3>
          <p>
            <code>Doc.parse</code> turns the text into a single{' '}
            <code>Doc</code>; <code>documents</code> then says what a corpus
            is — a lone object is a corpus of one, a top-level array is a
            corpus of its elements, each of which must be an object.
          </p>
          <p className="small">
            On the success path this is the identity on the element list: the
            outer <code>.arr</code> is gone and nothing inside an element has
            been touched. The <code>.arr</code> under <code>runs</code> in the
            second document is still there, and numbers are still their
            literals — <code>.num "8.5"</code>, not a parsed float. That text
            is what later decides <code>int</code> against <code>float</code>.
          </p>
          <LeanCode src={stages.docs} />
        </div>
      )}

      {step === 'perdoc' && (
        <div>
          <h3>Each document, walked from nothing</h3>
          <p>
            <code>observeDocument</code> runs on one document at a time, with no
            memory of any other. Every nesting becomes a table; every member
            records the set of types it held and whether it was present.
          </p>
          <p className="small">
            The first document builds a table at <code>.runs</code> — a lone
            object, so a <code>ref</code>. The second builds one at{' '}
            <code>.runs[]</code> — an array, so a <code>coll</code>. Neither
            knows about the other yet, and absences are not counted: at this
            point nothing knows what the rest of the corpus contains.
          </p>
          <Views step={step} view={view} setView={setView} />
          {stages.perDocument.map((t, i) => (
            <div key={i}>
              <h3 style={{ fontSize: 15 }}>Document {i + 1}</h3>
              {raw ? <LeanCode src={stages.perDocumentLean[i]} />
                   : <TablesView tables={t} />}
            </div>
          ))}
        </div>
      )}

      {step === 'folded' && (
        <div>
          <h3>Merged into one picture</h3>
          <p>
            Counts add, the sets of types seen union, flags disjoin. None of
            those can depend on which document came first — which is the whole
            of why <L n="schema_canonical">canonicity</L> holds, and why it
            gives an <em>equal</em> answer rather than an equivalent one.
          </p>
          <p className="small">
            Two things to read off the value. <code>ms</code> now holds both{' '}
            <code>int</code> and <code>float</code> in its seen set, with the
            join not yet taken — that happens once, at the end, so a conflict
            can name every type involved rather than the two that happened to
            meet first. And <code>runs</code> holds <b>two</b> types that do
            not join at all: the corpus would be refused if this value went
            straight to the type check.
          </p>
          <Views step={step} view={view} setView={setView} />
          {raw ? <LeanCode src={stages.foldedLean} />
               : <TablesView tables={stages.folded} />}
        </div>
      )}

      {step === 'finished' && (
        <div>
          <h3>What only the whole corpus can settle</h3>
          <p>
            <code>inferFinish</code> collapses a lone object where another
            document had an array, rejects a member whose types do not join, and
            fills in the absences — in that order, because the collapse is what
            removes the conflict the check would otherwise reject.
          </p>
          <p className="small">
            The table at <code>.runs</code> is <b>gone</b>: its rows moved into{' '}
            <code>.runs[]</code>, whose visits went 2 → 3, and the{' '}
            <code>ref</code> on the <code>runs</code> column was rewritten to
            the <code>coll</code> already beside it, so the two deduplicated to
            one type that joins. Meanwhile <code>meta</code> reads{' '}
            <b>absent 1</b> — the second document had no such key. That number
            is computed by subtraction against each table's own visit count,
            which is why <L n="nullability_sound">nullability</L> has to prove{' '}
            <code>values + nulls + absent = visits</code> before the{' '}
            <code>option</code> marking can be trusted.
          </p>
          <Views step={step} view={view} setView={setView} />
          {raw ? <LeanCode src={stages.finishedLean} />
               : <TablesView tables={stages.finished} />}
        </div>
      )}

      {step === 'naming' && (
        <div>
          <h3>What the tables will be called</h3>
          <p>
            The one step that reads no data. <code>Naming</code> is a
            projection of the configuration: the root's module name, already
            mangled and capitalised, and whatever names the user supplied for
            other tables, by the path of the table each one names.
          </p>
          <p className="small">
            This corpus is run with no configuration, so the root defaults to{' '}
            <code>Root</code> and nothing else is named — every other module
            name is derived from its table's path by{' '}
            <code>moduleName</code>, which is why <code>.runs[]</code> becomes{' '}
            <code>Runs</code>. The asymmetry is deliberate:{' '}
            <code>root</code> is normalised here, while <code>tables</code>{' '}
            holds the user's strings verbatim and is mangled at lookup.
          </p>
          <LeanCode src={stages.naming} />
        </div>
      )}

      {step === 'schema' && (
        <div>
          <h3>The same content, arranged for emission</h3>
          <p>
            <code>toSchema</code> orders the tables so a module always follows
            the modules it names, and reads each table's parent and keyedness
            off its path rather than recording them.
          </p>
          <p className="small">
            Three changes are visible in the raw value. The order is reversed —
            deepest first, so <code>.runs[]</code> now leads and the root comes
            last. Every <code>Obs</code> has become a <code>Field</code>: the
            counts are gone and <code>meta</code> is <b>nullable</b> for the
            first time. And <code>parent</code> appears — <code>some []</code>{' '}
            on <code>.runs[]</code>, because its path ends in an element
            marker, and <code>none</code> on <code>.meta</code>, which is
            pointed at rather than collected. Nothing is proved across this
            step; the guarantees are stated on either side of it.
          </p>
          <Views step={step} view={view} setView={setView} />
          {raw ? <LeanCode src={stages.schemaLean} />
               : <SchemaView schema={stages.schema} />}
        </div>
      )}

      {step === 'file' && (
        <div>
          <h3>Modules and declarations</h3>
          <p>
            <code>gen</code> checks the schema, lays out the modules, then
            checks its own output before returning it.{' '}
            <L n="signature_wellFormed">Well-formedness</L> and{' '}
            <L n="structure_preserved">structure preservation</L> are both
            proved by inverting those checks.
          </p>
          <p className="small">
            The nesting is visible in the declarations:{' '}
            <code>val meta : t -&gt; Meta.id option</code> is the reference edge,{' '}
            <code>val of_root : Root.id -&gt; t list</code> in{' '}
            <code>Runs</code> is the collection edge. Those two shapes are
            exactly what the structure theorem quantifies over. In the raw
            value they are still trees — <code>.option (.qualified "Meta" "id")</code>{' '}
            — which is the point of having a structured codomain at all:
            these are the things the theorems can be stated about. The{' '}
            <code>.ml</code> bodies are counted rather than printed, because
            well-formedness is stated of <code>decls</code> alone.
          </p>
          <Views step={step} view={view} setView={setView} />
          {raw ? <LeanCode src={stages.fileLean} />
               : <FileView modules={stages.file} />}
        </div>
      )}

      {step === 'units' && (
        <div>
          <h3>What lands on disk</h3>
          <p>
            One <code>.mli</code> and <code>.ml</code> per table, a row reader
            each, and a loader. Printing is the one step nothing is proved
            about — a tree becomes characters here, and no theorem crosses it.
          </p>
          <div className="unitbar">
            {stages.units.map((x) => (
              <button key={x.name} className={`unitbtn${x.name === unit ? ' on' : ''}`}
                      onClick={() => setUnit(x.name)}>{x.name}</button>
            ))}
          </div>
          <LeanCode src={u.text} />
        </div>
      )}

      {step === 'outcome' && (
        <div>
          <h3>The record that comes back</h3>
          <p>
            <code>finish</code> packs the five things anything downstream
            needs: the naming, the units as (file name, text), the same units
            in one text for a terminal, the settled tables, and how many
            documents were read. <code>--json</code> reads the whole record;
            plain output uses <code>ocaml</code> or writes <code>units</code>{' '}
            to a directory.
          </p>
          <p className="small">
            <code>tables</code> is the value of step 5 and <code>ocaml</code>{' '}
            the text of step 9, so both are given here by size rather than
            repeated. Note what is <em>not</em> in the record: the documents.
            The accumulator is bounded by the schema, not by the corpus, which
            is exactly what lets the streaming reader hand documents over one
            at a time and drop each one after.
          </p>
          <LeanCode src={stages.outcome} />
        </div>
      )}
    </div>
  )
}
