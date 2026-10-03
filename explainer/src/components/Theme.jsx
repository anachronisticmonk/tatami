import React, { useState, useEffect } from 'react'

const read = () => {
  try {
    const v = localStorage.getItem('tatami-theme')
    return v === 'light' || v === 'dark' ? v : 'dark'
  } catch { return 'dark' }
}

/** Dark unless the reader says otherwise, remembered, and shared with the
    playground and the backend — same key, same two values. */
export default function Theme() {
  const [t, setT] = useState(read)
  useEffect(() => {
    document.documentElement.setAttribute('data-theme', t)
    try { localStorage.setItem('tatami-theme', t) } catch {}
  }, [t])
  return (
    <button className="themebtn" title="switch between light and dark"
            onClick={() => setT(t === 'dark' ? 'light' : 'dark')}>{t}</button>
  )
}
