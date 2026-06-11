/-
Figures/Rigidity/PebbleGame.lean — 2D rigidity analysis (Jacobs &
Hendrickson 1997).

Each vertex starts with k = 2 pebbles (DoF in 2D). For each candidate
edge, we try to free up enough pebbles on the endpoints (3 total) by
sliding pebbles along previously-added edges via DFS. If we succeed,
the edge is INDEPENDENT and joins the rigid skeleton; if not, the edge
is REDUNDANT (could be inconsistent).

After processing all edges:
- Rigid components are connected sub-graphs whose edges all became
  independent AND whose total pebbles (free + directed-edge-pebbles)
  equal 3 (locally Laman-tight).
- Free DoF joints are those connected to nothing rigid, OR with surplus
  pebbles after all edges processed.
- Redundant edges flag potential inconsistency.

MVP scope (v0): we implement the pebble-slide DFS faithfully, but the
rigid-component extraction uses a simplified "all-incident-via-
independent-edges" heuristic. The proper algorithm walks the directed
pebble graph; the v0 component extraction may merge two truly separate
rigid components into one. Refine when a real test case forces it.
-/

import Figures.Rigidity.Types

namespace Figures.Rigidity.PebbleGame

open Figures.Rigidity

/-- Internal mutable state during the pebble game. -/
private structure State where
  /-- Free pebbles at each vertex. Initialized to 2. -/
  pebbles : Array Nat
  /-- For each edge id, the "owner" vertex (whose pebble is consumed
  by this edge). `none` if the edge isn't yet added (or was redundant). -/
  owners  : Array (Option Nat)
  /-- For each vertex id, the list of edge ids it directs outward (i.e.
  edges that consumed THIS vertex's pebble). Mirror of `owners`. -/
  outEdges : Array (Array Nat)
  deriving Inhabited

private def State.init (numJoints numEdges : Nat) : State :=
  { pebbles  := Array.replicate numJoints 2
    owners   := Array.replicate numEdges none
    outEdges := Array.replicate numJoints #[] }

/-- DFS from `start` along directed edges, trying to find a vertex with
a free pebble. Returns the path of edge ids from start to that vertex,
or `none` if no path exists. Avoids `forbidden` (the other endpoint of
the current edge — pebbles on `forbidden` shouldn't be "stolen" since
they're needed for the edge being added). -/
private partial def findFreePebblePath
    (g : ConstraintGraph) (st : State) (start forbidden : Nat) :
    Option (Array Nat) := Id.run do
  let mut visited : Array Bool := Array.replicate g.joints.size false
  -- DFS stack of (vertex, path-to-vertex).
  let mut stack : Array (Nat × Array Nat) := #[(start, #[])]
  while !stack.isEmpty do
    let (v, path) := stack.back!
    stack := stack.pop
    if v != forbidden && st.pebbles[v]! > 0 then
      return some path
    if visited[v]! then continue
    visited := visited.set! v true
    -- Follow each outgoing directed edge.
    for eid in st.outEdges[v]! do
      let edge := g.edges[eid]!
      -- The "other end" of the directed edge: edge direction is from
      -- owner to the other endpoint. If v is the owner (which it is,
      -- since this edge is in v's outEdges), the other end is whichever
      -- of edge.a / edge.b isn't v.
      let other := if edge.a == v then edge.b else edge.a
      if !visited[other]! then
        stack := stack.push (other, path.push eid)
  return none

/-- Reverse a pebble-slide path: edges along the path get their owner
flipped. Effectively transfers one free pebble from the path's end
back to its start. -/
private def slideAlong (g : ConstraintGraph) (st : State) (start : Nat)
    (path : Array Nat) : State := Id.run do
  let mut st := st
  let mut current := start
  for eid in path do
    let edge := g.edges[eid]!
    let other := if edge.a == current then edge.b else edge.a
    -- Move this edge's ownership from `current` to `other`.
    st := { st with
      owners := st.owners.set! eid (some other)
      outEdges :=
        let oc := st.outEdges[current]!
        let oo := st.outEdges[other]!
        st.outEdges
          |>.set! current (oc.filter (· != eid))
          |>.set! other (oo.push eid) }
    current := other
  -- After sliding, `current` is the vertex with a free pebble to spare;
  -- `start` is the vertex that now has access to it. Transfer one
  -- pebble from current to start.
  st := { st with
    pebbles := st.pebbles
      |>.set! current (st.pebbles[current]! - 1)
      |>.set! start (st.pebbles[start]! + 1) }
  return st

/-- Try to ensure vertex `v` has at least 1 free pebble by sliding from
elsewhere. `forbidden` is the other endpoint of the current candidate
edge — its pebbles are off-limits. Returns the updated state, and
`true` iff a pebble was found (or already there). -/
private def gatherPebble (g : ConstraintGraph) (st : State) (v forbidden : Nat) :
    State × Bool :=
  if st.pebbles[v]! > 0 then (st, true)
  else
    match findFreePebblePath g st v forbidden with
    | some path => (slideAlong g st v path, true)
    | none      => (st, false)

/-- Try to add edge `eid` (joining `a` and `b`) to the rigid skeleton.
Returns the new state + whether the edge was independent. -/
private def tryAddEdge (g : ConstraintGraph) (st : State) (eid : Nat) :
    State × Bool := Id.run do
  let edge := g.edges[eid]!
  let a := edge.a
  let b := edge.b
  -- Gather pebbles on both endpoints, totaling at least 3 (one will be
  -- consumed by this edge; the other two ensure local rigidity).
  let (st, gotA) := gatherPebble g st a b
  if !gotA then return (st, false)
  let (st, gotB) := gatherPebble g st b a
  if !gotB then return (st, false)
  -- After gathering, both a and b have ≥ 1 free pebble. We need a total
  -- of ≥ 3 free in {a, b} to ensure this edge is independent. With both
  -- ≥ 1, we have at least 2; one more is needed.
  let totalFree := st.pebbles[a]! + st.pebbles[b]!
  if totalFree < 3 then
    -- Try to gather one more pebble onto either a or b.
    let (st', gotMore) := gatherPebble g st a b
    let gotEnough := gotMore && (st'.pebbles[a]! + st'.pebbles[b]! ≥ 3)
    if !gotEnough then
      let (st'', gotMore') := gatherPebble g st b a
      let gotEnough' := gotMore' && (st''.pebbles[a]! + st''.pebbles[b]! ≥ 3)
      if !gotEnough' then return (st'', false)
      else
        -- Consume one pebble from a as the edge's owner.
        let owner := if st''.pebbles[a]! > 0 then a else b
        let st''' :=
          { st'' with
            pebbles := st''.pebbles.set! owner (st''.pebbles[owner]! - 1)
            owners  := st''.owners.set! eid (some owner)
            outEdges := st''.outEdges.set! owner (st''.outEdges[owner]!.push eid) }
        return (st''', true)
    else
      let owner := if st'.pebbles[a]! > 0 then a else b
      let st'' :=
        { st' with
          pebbles := st'.pebbles.set! owner (st'.pebbles[owner]! - 1)
          owners  := st'.owners.set! eid (some owner)
          outEdges := st'.outEdges.set! owner (st'.outEdges[owner]!.push eid) }
      return (st'', true)
  else
    -- Already have ≥ 3 free in {a, b}; consume one as the edge's owner.
    let owner := if st.pebbles[a]! > 0 then a else b
    let st' :=
      { st with
        pebbles := st.pebbles.set! owner (st.pebbles[owner]! - 1)
        owners  := st.owners.set! eid (some owner)
        outEdges := st.outEdges.set! owner (st.outEdges[owner]!.push eid) }
    return (st', true)

/-- Union-find root lookup with fuel-bounded recursion (graphs we care
about are small enough that O(n) walks are fine). -/
private partial def ufFind (parent : Array Nat) (i : Nat) : Nat :=
  let p := parent[i]!
  if p == i then i else ufFind parent p

/-- Extract rigid components after all edges processed: union-find on
joints connected by independent edges. -/
private def extractComponents (g : ConstraintGraph) (st : State) :
    Array RigidComponent × Array Nat × Array Nat := Id.run do
  let n := g.joints.size
  let mut parent : Array Nat := Array.range n
  let mut redundant : Array Nat := #[]
  -- Process each edge. Edges with `owners[eid] = some _` are
  -- independent; with `none` are redundant.
  for eid in [0:g.edges.size] do
    match st.owners[eid]! with
    | some _ =>
      let edge := g.edges[eid]!
      let ra := ufFind parent edge.a
      let rb := ufFind parent edge.b
      if ra != rb then parent := parent.set! ra rb
    | none => redundant := redundant.push eid
  -- Group joints by root.
  let mut groups : Array (Array Nat) := Array.replicate n #[]
  for j in [0:n] do
    let r := ufFind parent j
    groups := groups.set! r ((groups[r]!).push j)
  -- Convert to RigidComponents (with ≥ 2 joints) and collect free DoF.
  let mut components : Array RigidComponent := #[]
  let mut freeDoF : Array Nat := #[]
  for grp in groups do
    if grp.size == 1 then
      freeDoF := freeDoF.push grp[0]!
    else if grp.size ≥ 2 then
      -- Collect edge ids that connect joints within this group.
      let groupSet := grp
      let mut compEdges : Array Nat := #[]
      for eid in [0:g.edges.size] do
        if st.owners[eid]!.isSome then
          let edge := g.edges[eid]!
          if groupSet.contains edge.a && groupSet.contains edge.b then
            compEdges := compEdges.push eid
      components := components.push { joints := grp, edges := compEdges }
  return (components, freeDoF, redundant)

/-- Run the pebble game on a constraint graph. -/
def analyze (g : ConstraintGraph) : RigidityDecomposition := Id.run do
  let mut st : State := State.init g.joints.size g.edges.size
  for eid in [0:g.edges.size] do
    let (st', _) := tryAddEdge g st eid
    st := st'
  let (components, freeDoF, redundant) := extractComponents g st
  return { components, freeDoF, redundant }

end Figures.Rigidity.PebbleGame
