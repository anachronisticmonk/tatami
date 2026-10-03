import React from 'react'

const KW = /\b(theorem|lemma|def|structure|inductive|instance|abbrev|match|with|fun|let|do|if|then|else|by|intro|exact|refine|simp|rw|unfold|cases|induction|obtain|have|show|return|where|deriving|namespace|end|open|import|private)\b/g
const TY = /\b(Nat|String|Bool|List|Option|Prop|Type|Except|Path|Ty|Tables|TableObs|Obs|Schema|Table|File|Module|Doc|Config|Naming|Field|Col|Seg)\b/g

/** Highlighting is cosmetic: a regex over the text, not a parse. */
function paint(src) {
  const out = []
  src.split('\n').forEach((line, i) => {
    const c = line.indexOf('--')
    const code = c >= 0 ? line.slice(0, c) : line
    const cm = c >= 0 ? line.slice(c) : ''
    const html = code
      .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
      .replace(KW, '<span class="kw">$1</span>')
      .replace(TY, '<span class="ty">$1</span>')
    out.push(
      <div key={i} dangerouslySetInnerHTML={{
        __html: html + (cm ? `<span class="cm">${cm.replace(/</g, '&lt;')}</span>` : '') || '&nbsp;',
      }} />
    )
  })
  return out
}

export default function LeanCode({ children, src }) {
  return <pre className="lean">{paint(src ?? String(children ?? ''))}</pre>
}
