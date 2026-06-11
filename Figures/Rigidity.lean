/-
Figures/Rigidity.lean — top-level entry for the L_full geometric solver.

`solve : DSL.Construction → Float → Float → MetaM (Array (Name × Pos2))`

Walks the Construction into a ConstraintGraph (extractor), runs the
pebble game for rigidity analysis (informational for now), then hands
each joint to the position synthesizer (which calls the anti-regularity
registry for free DoFs). Returns named positions for downstream
rendering.

Decoration (label placement, color, line weight) lives in a separate
pass — figures/Figures/Solver/LabelLayout.lean keeps working on top of
the output positions; it isn't touched by this module.
-/

import Lean
import Figures.Vec2
import Figures.Rigidity.Types
import Figures.Rigidity.AntiRegularity
import Figures.Rigidity.ConstraintGraph
import Figures.Rigidity.PebbleGame
import Figures.Rigidity.Synthesize
import Figures.Rigidity.Rules
import Figures.Construction.DSL

namespace Figures.Rigidity

open Figures Figures.Construction.DSL

/-- Solve positions for a Construction via the L_full pipeline. -/
def solvePositions (c : Construction)
    (canvasW : Float := 1280) (canvasH : Float := 720) :
    Lean.MetaM (Array (Figures.Name × Pos2)) := do
  let graph  := Figures.Rigidity.ConstraintGraph.build c
  let decomp := Figures.Rigidity.PebbleGame.analyze graph
  let placed ← Figures.Rigidity.Synthesize.run graph decomp canvasW canvasH
  -- Map joint ids back to user-visible names; drop synthetic helpers.
  return placed.filterMap fun (jid, p) =>
    let j := graph.joints[jid]!
    if j.synthetic then none else some (j.name, p)

end Figures.Rigidity
