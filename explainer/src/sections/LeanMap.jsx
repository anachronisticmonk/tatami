import React from 'react'
import Graph from '../components/Graph.jsx'
export default function LeanMap({ selected, onSelect }) {
  return <Graph selected={selected} onSelect={onSelect} />
}
