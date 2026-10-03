import React from 'react'

export function TablesView({ tables, showSeen = true }) {
  if (!tables?.length) return <p className="small">no tables</p>
  return (
    <div className="tv">
      {tables.map((t) => (
        <div className="tv-tbl" key={t.path}>
          <div className="tv-head">
            <code>{t.path === '.' ? '.  (the document itself)' : t.path}</code>
            <span className="tv-visits mono">{t.visits} visit{t.visits === 1 ? '' : 's'}</span>
          </div>
          <table className="t tv-t">
            <thead><tr>
              <th>member</th>{showSeen && <th>types seen</th>}<th>joined</th>
              <th>values</th><th>nulls</th><th>absent</th>
            </tr></thead>
            <tbody>
              {t.members.map((m) => (
                <tr key={m.key}>
                  <td className="mono">{m.key}</td>
                  {showSeen && <td className="mono dim">{m.seen.join(', ') || '—'}</td>}
                  <td className="mono">{m.joined}</td>
                  <td className="num">{m.values}</td>
                  <td className="num">{m.nulls}</td>
                  <td className={'num' + (m.absent ? ' hot' : '')}>{m.absent}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      ))}
    </div>
  )
}

export function SchemaView({ schema }) {
  return (
    <div className="tv">
      {schema.map((t) => (
        <div className="tv-tbl" key={t.path}>
          <div className="tv-head">
            <code>{t.path === '.' ? '.' : t.path}</code>
            <span className="tv-visits mono">
              parent {t.parent ?? '—'}{t.keyed ? ' · keyed' : ''}
            </span>
          </div>
          <table className="t tv-t">
            <thead><tr><th>column</th><th>type</th><th>optional</th></tr></thead>
            <tbody>
              {t.columns.map((c) => (
                <tr key={c.name}>
                  <td className="mono">{c.name}</td>
                  <td className="mono">{c.ty}</td>
                  <td>{c.nullable ? <span className="hot">yes</span> : '—'}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      ))}
    </div>
  )
}

export function FileView({ modules }) {
  return (
    <div className="tv">
      {modules.filter((m) => !m.implOnly).map((m) => (
        <div className="tv-tbl" key={m.name}>
          <div className="tv-head"><code>module {m.name}</code></div>
          <pre className="lean tv-decls">{m.decls.join('\n')}</pre>
        </div>
      ))}
      <p className="small">
        Plus {modules.filter((m) => m.implOnly).length} modules that declare
        nothing — the row readers and the loader.
      </p>
    </div>
  )
}
