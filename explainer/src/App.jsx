import React, { useState, useCallback, useRef, useEffect } from 'react'
import { DeclCtx } from './components/LeanRef.jsx'
import { TypeCtx } from './components/TypeRef.jsx'
import DeclPanel from './components/DeclPanel.jsx'
import TypePanel from './components/TypePanel.jsx'
import Theme from './components/Theme.jsx'
import Overview from './sections/Overview.jsx'
import PipelineSection from './sections/PipelineSection.jsx'
import Walkthrough from './sections/Walkthrough.jsx'
import Guarantees from './sections/Guarantees.jsx'
import LeanMap from './sections/LeanMap.jsx'
import Scope from './sections/Scope.jsx'

const SECTIONS = [
  { id: 'overview',  num: '',  label: 'Overview',        group: 'Start',    Comp: Overview },
  { id: 'pipeline',  num: '1', label: 'The pipeline',    group: 'Follow',   Comp: PipelineSection },
  { id: 'example',   num: '2', label: 'A worked example',group: 'Follow',   Comp: Walkthrough },
  { id: 'guarantees',num: '3', label: 'The guarantees',  group: 'Prove',    Comp: Guarantees },
  { id: 'map',       num: '4', label: 'Lean map',        group: 'Prove',    Comp: LeanMap, wide: true },
  { id: 'scope',     num: '5', label: 'What is not proved', group: 'Prove', Comp: Scope },
]
const GROUPS = ['Start', 'Follow', 'Prove']

export default function App() {
  const [sectionId, setSectionId] = useState(() => {
    const h = window.location.hash.slice(1)
    return SECTIONS.some((s) => s.id === h) ? h : 'overview'
  })
  /* One panel slot, two kinds of thing in it: a theorem from `Proofs/`, or a
     declaration from the sources. Separate slots would let two panels sit on
     top of each other, and they are the same piece of screen. */
  const [panel, setPanel] = useState(null)
  const [graphSel, setGraphSel] = useState(null)
  const main = useRef(null)

  const go = useCallback((id) => {
    setSectionId(id)
    window.location.hash = id
    main.current?.scrollTo({ top: 0 })
  }, [])
  const openDecl = useCallback((n) => { setPanel({ kind: 'decl', name: n }); setGraphSel(n) }, [])
  const openType = useCallback((n) => setPanel({ kind: 'type', name: n }), [])
  const close = useCallback(() => setPanel(null), [])

  useEffect(() => {
    const onHash = () => {
      const h = window.location.hash.slice(1)
      if (SECTIONS.some((s) => s.id === h)) setSectionId(h)
    }
    window.addEventListener('hashchange', onHash)
    return () => window.removeEventListener('hashchange', onHash)
  }, [])

  const i = SECTIONS.findIndex((s) => s.id === sectionId)
  const section = SECTIONS[i]
  const { Comp } = section
  const prev = SECTIONS[i - 1], next = SECTIONS[i + 1]

  return (
    <DeclCtx.Provider value={openDecl}>
     <TypeCtx.Provider value={openType}>
      <div className="app">
        <nav className="sidebar">
          <div className="brand">
            <h1>tatami</h1>
            <p>the pipeline, and what the Lean proofs cover of it</p>
          </div>
          {GROUPS.map((g) => (
            <div className="nav-group" key={g}>
              <div className="nav-group-label">{g}</div>
              {SECTIONS.filter((s) => s.group === g).map((s) => (
                <button key={s.id}
                        className={`nav-item${s.id === sectionId ? ' active' : ''}`}
                        onClick={() => go(s.id)}>
                  <span className="nav-num">{s.num}</span><span>{s.label}</span>
                </button>
              ))}
            </div>
          ))}
        </nav>

        <main className="main" ref={main}>
          <Theme />
          <div className={`main-inner${section.wide ? ' wide' : ''}`}>
            {section.wide
              ? <Comp selected={graphSel} onSelect={openDecl} />
              : (
                <>
                  <Comp go={go} />
                  <div className="pagenav">
                    {prev ? <button onClick={() => go(prev.id)}>
                      <span className="pn-label">Previous</span>← {prev.label}</button> : <span />}
                    {next ? <button onClick={() => go(next.id)}>
                      <span className="pn-label">Next</span>{next.label} →</button> : <span />}
                  </div>
                </>
              )}
          </div>
        </main>
      </div>
      <DeclPanel name={panel?.kind === 'decl' ? panel.name : null}
                 onClose={close} onOpen={openDecl} />
      <TypePanel name={panel?.kind === 'type' ? panel.name : null}
                 onClose={close} onOpen={openType} />
     </TypeCtx.Provider>
    </DeclCtx.Provider>
  )
}
