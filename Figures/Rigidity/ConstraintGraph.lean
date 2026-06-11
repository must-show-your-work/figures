/-
Figures/Rigidity/ConstraintGraph.lean — DSL.Construction → ConstraintGraph.

Walks a `Figures.Construction.DSL.Construction` and produces the
bar-and-joint graph the pebble game will analyze. Rules:

- `exists … : Point` → one joint per name.
- `construct name := segment A B / ray A B / line_through A B` → a
  rigid edge between A and B. The DSL doesn't carry a rest length, so
  `rest := none` (synthesizer or registry picks).
- `assert incident P L` where `L` was constructed via `line_through B
  C` → P joins to the line's endpoints (2 edges: P-B, P-C). Approximate
  but adequate for v0 — a strict 1-DoF "slider" model would require an
  extended pebble game.
- `assert collinear A B C [D…]` → if 3+ joints, all pairs (A,B), (A,C),
  (B,C)… get edges treating collinearity as fully constraining for the
  layout (the pebble game will mark redundancies).
- `assert between A X B` → edges (A,X) and (X,B) so X is rigidly tied
  to the segment; the `between` annotation tells the synthesizer X is
  interior.
- `assert noncollinear`, `assert distinct`, `focus`, `hidden`,
  `assert on_ray / on_segment` → annotations. They don't add rigid
  edges; they feed the anti-regularity rules and the position
  synthesizer.
- Unknown asserts are ignored (graceful degradation).
-/

import Figures.Rigidity.Types
import Figures.Construction.DSL

namespace Figures.Rigidity.ConstraintGraph

open Figures Figures.Construction.DSL Figures.Rigidity

/-- Linear-lookup id for a joint name. -/
private def jointIdOf (joints : Array Joint) (name : String) : Option Nat :=
  joints.findIdx? (·.name == name)

/-- Insert a joint if absent; return its id. -/
private def ensureJoint (joints : Array Joint) (name : String)
    (synthetic : Bool := false) : Array Joint × Nat :=
  match jointIdOf joints name with
  | some id => (joints, id)
  | none =>
    let id := joints.size
    (joints.push { id, name, synthetic }, id)

/-- Stable synthetic name for a "line through B and C" anchor — same
convention as the proof-state matcher's `lineAnchor`. -/
private def lineAnchorName (b c : String) : String := s!"L_{b}_{c}"

/-- Push a `RigidEdge` if not already present (any direction). -/
private def addEdge (edges : Array RigidEdge) (a b : Nat) : Array RigidEdge :=
  let alreadyHas := edges.any fun e =>
    (e.a == a && e.b == b) || (e.a == b && e.b == a)
  if alreadyHas then edges else edges.push { a, b }

/-- Read the head and args of a `ConstraintExpr` if it's an `.app`. -/
private def asApp : ConstraintExpr → Option (String × List ConstraintExpr)
  | .app h xs => some (h, xs)
  | _ => none

/-- Read an arg as a name. -/
private def asName : ConstraintExpr → Option String
  | .name n => some n
  | _ => none

/-- Pull all name-typed args from a list, all-or-nothing. -/
private def allNames (xs : List ConstraintExpr) : Option (Array String) := Id.run do
  let mut out : Array String := #[]
  for x in xs do
    let some n := asName x | return none
    out := out.push n
  return some out

/-- Add an `on line through (b, c)` incidence: P-B and P-C edges. The
line's anchor joint may or may not exist as a named joint — if there
was a corresponding `construct L := line_through B C` earlier, we
already have edges (L-B) and (L-C). For incidence we connect P to the
line's endpoints directly. -/
private def addLineIncidence (g : ConstraintGraph) (p b c : String) :
    ConstraintGraph :=
  let (j0, pid) := ensureJoint g.joints p
  let (j1, bid) := ensureJoint j0 b
  let (j2, cid) := ensureJoint j1 c
  let edges := addEdge (addEdge g.edges pid bid) pid cid
  { g with joints := j2, edges }

/-- Translate a `.construct name := expr` stmt to a rigid edge (when
the expr names a known shape) plus, if not already present, the
endpoint joints. Unknown constructs are dropped. -/
private def applyConstruct (g : ConstraintGraph) (_name : String)
    (expr : ConstraintExpr) : ConstraintGraph :=
  match asApp expr with
  | some ("segment", [.name a, .name b])
  | some ("ray", [.name a, .name b])
  | some ("line_through", [.name a, .name b]) =>
    let (j0, aid) := ensureJoint g.joints a
    let (j1, bid) := ensureJoint j0 b
    { g with joints := j1, edges := addEdge g.edges aid bid }
  | _ => g

/-- Translate an `assert claim` stmt to either rigid edges,
annotations, or both. -/
private def applyAssert (g : ConstraintGraph) (claim : ConstraintExpr) :
    ConstraintGraph :=
  match asApp claim with
  | some ("between", [.name a, .name x, .name b]) =>
    let (j0, aid) := ensureJoint g.joints a
    let (j1, xid) := ensureJoint j0 x
    let (j2, bid) := ensureJoint j1 b
    let edges := addEdge (addEdge g.edges aid xid) xid bid
    { g with joints := j2, edges,
             annotations := g.annotations.push (.between aid xid bid) }
  | some ("collinear", args) =>
    match allNames args with
    | none => g
    | some names => Id.run do
      let mut joints := g.joints
      let mut ids : Array Nat := #[]
      for n in names do
        let (j', id) := ensureJoint joints n
        joints := j'
        ids := ids.push id
      let mut edges := g.edges
      for i in [0:ids.size] do
        for j in [i+1:ids.size] do
          edges := addEdge edges ids[i]! ids[j]!
      return { g with joints, edges }
  | some ("incident", [.name p, .name lineName]) =>
    -- The line name is either a "L_b_c" synthetic anchor (from
    -- proof-state matchers) or a user-supplied construct name. Strip
    -- the L_ prefix to recover endpoints; if not present, treat lineName
    -- as a joint to connect to.
    if lineName.startsWith "L_" then
      let rest : String := (lineName.drop 2).toString
      match rest.splitOn "_" with
      | [b, c] => addLineIncidence g p b c
      | _ => g
    else
      let (j0, pid) := ensureJoint g.joints p
      let (j1, lid) := ensureJoint j0 lineName
      { g with joints := j1, edges := addEdge g.edges pid lid }
  | some ("noncollinear", [.name a, .name b, .name c]) =>
    let (j0, aid) := ensureJoint g.joints a
    let (j1, bid) := ensureJoint j0 b
    let (j2, cid) := ensureJoint j1 c
    { g with joints := j2,
             annotations := g.annotations.push (.noncollinear aid bid cid) }
  | some ("¬", [.app "collinear" [.name a, .name b, .name c]]) =>
    let (j0, aid) := ensureJoint g.joints a
    let (j1, bid) := ensureJoint j0 b
    let (j2, cid) := ensureJoint j1 c
    { g with joints := j2,
             annotations := g.annotations.push (.noncollinear aid bid cid) }
  | some ("distinct", args) =>
    match allNames args with
    | none => g
    | some names => Id.run do
      let mut joints := g.joints
      let mut ids : Array Nat := #[]
      for n in names do
        let (j', id) := ensureJoint joints n
        joints := j'
        ids := ids.push id
      return { g with joints, annotations := g.annotations.push (.distinct ids) }
  | some ("on_ray", [.name p, .name a, .name b]) =>
    let (j0, pid) := ensureJoint g.joints p
    let (j1, aid) := ensureJoint j0 a
    let (j2, bid) := ensureJoint j1 b
    let edges := addEdge (addEdge g.edges pid aid) pid bid
    { g with joints := j2, edges,
             annotations := g.annotations.push (.onRay pid aid bid) }
  | some ("on_segment", [.name p, .name a, .name b]) =>
    let (j0, pid) := ensureJoint g.joints p
    let (j1, aid) := ensureJoint j0 a
    let (j2, bid) := ensureJoint j1 b
    let edges := addEdge (addEdge g.edges pid aid) pid bid
    { g with joints := j2, edges,
             annotations := g.annotations.push (.onSegment pid aid bid) }
  | some ("focus", [.name n]) =>
    let (j', id) := ensureJoint g.joints n
    { g with joints := j', annotations := g.annotations.push (.focus id) }
  | some ("hidden", args) =>
    match allNames args with
    | none => g
    | some names => Id.run do
      let mut joints := g.joints
      let mut ids : Array Nat := #[]
      for n in names do
        let (j', id) := ensureJoint joints n
        joints := j'
        ids := ids.push id
      return { g with joints, annotations := g.annotations.push (.hidden ids) }
  | _ => g

/-- Translate an `exists name+ : sort` stmt by adding a joint per name. -/
private def applyExists (g : ConstraintGraph) (names : Array Name) :
    ConstraintGraph :=
  names.foldl (init := g) fun g' n =>
    let (j', _) := ensureJoint g'.joints n
    { g' with joints := j' }

/-- Public entry: walk a Construction's stmts and produce the graph. -/
def build (c : Construction) : ConstraintGraph :=
  c.stmts.foldl (init := ({} : ConstraintGraph)) fun g s => match s with
    | .«exists» names _   => applyExists g names
    | .assert claim _     => applyAssert g claim
    | .construct name expr => applyConstruct g name expr

end Figures.Rigidity.ConstraintGraph
