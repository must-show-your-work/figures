/-
Figures/Rigidity/Types.lean — data types for the L_full geometric solver.

A `ConstraintGraph` is the input to the pebble-game rigidity analysis:
vertices (`Joint`s) are named particles, edges (`RigidEdge`s) are
fixed-distance constraints between pairs, and annotations carry the
non-edge information the rigidity analyzer ignores but the position
synthesizer (or the anti-regularities registry) consumes — betweenness,
focus hints, noncollinearity, etc.

A `RigidityDecomposition` is the pebble game's output: which joints
form rigid components, which joints are free DoF, which edges are
redundant (potentially inconsistent).

A `DoFContext` is what an anti-regularity rule sees when picking a
position for a free DoF — the graph, the placements so far, the joint
we're placing, an optional candidate position from algebra.

A `Chooser` is the registered function shape — `DoFContext → MetaM
(Option Pos2)`. Returning `none` means "this rule doesn't apply, try
the next one"; returning `some p` means "use this position".
-/

import Lean
import Figures.Vec2

namespace Figures.Rigidity

open Figures

/-- A vertex in the constraint graph. -/
structure Joint where
  id : Nat
  name : String
  synthetic : Bool := false
  deriving Repr, Inhabited

/-- A fixed-distance bar-and-joint edge. `rest` is the desired distance
in canvas units; if `none`, the synthesizer (or anti-regularity
chooser) picks one. -/
structure RigidEdge where
  a    : Nat
  b    : Nat
  rest : Option Float := none
  deriving Repr, Inhabited

/-- Non-edge information the rigidity analyzer ignores but the
position synthesizer and anti-regularity rules use. -/
inductive Annotation where
  | noncollinear  : Nat → Nat → Nat → Annotation
  | distinct      : Array Nat → Annotation
  | between       : Nat → Nat → Nat → Annotation
  | onLineThrough : Nat → Nat → Nat → Annotation
  | onRay         : Nat → Nat → Nat → Annotation
  | onSegment     : Nat → Nat → Nat → Annotation
  | focus         : Nat → Annotation
  | hidden        : Array Nat → Annotation
  deriving Repr, Inhabited

/-- Input to the pebble-game rigidity analysis. -/
structure ConstraintGraph where
  joints      : Array Joint        := #[]
  edges       : Array RigidEdge    := #[]
  annotations : Array Annotation   := #[]
  deriving Inhabited

/-- A rigid component: joints whose pairwise distances are all
constrained, so the whole component moves as a rigid body. -/
structure RigidComponent where
  joints : Array Nat
  edges  : Array Nat
  deriving Repr, Inhabited

/-- Output of the pebble-game pass. -/
structure RigidityDecomposition where
  components : Array RigidComponent  := #[]
  freeDoF    : Array Nat             := #[]
  redundant  : Array Nat             := #[]
  deriving Inhabited

/-- What an anti-regularity chooser sees when picking a free-DoF position. -/
structure DoFContext where
  graph     : ConstraintGraph
  placed    : Array (Nat × Pos2)    := #[]
  joint     : Nat
  candidate : Option Pos2           := none
  canvasW   : Float                 := 1280
  canvasH   : Float                 := 720
  deriving Inhabited

/-- Look up a placed joint's position. -/
def DoFContext.posOf (ctx : DoFContext) (id : Nat) : Option Pos2 :=
  ctx.placed.findSome? fun (i, p) => if i == id then some p else none

/-- A registered position-picker. `none` defers; `some p` claims. -/
abbrev Chooser := DoFContext → Lean.MetaM (Option Pos2)

end Figures.Rigidity
