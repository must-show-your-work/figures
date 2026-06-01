/-
Figures/Examples.lean — Self-contained demos. No atlas, no giyf, no
geometry. Used to iterate on the figures library in isolation: build,
`#eval` to dump SVG, open in a browser or pipe to a file.

Examples here are deliberately non-geometric (commutative squares,
flowcharts, …) — figures is a generic visualization library; the
geometry stuff lives in giyf.
-/

import Figures
import Figures.SVG

namespace Figures.Examples


/-! ## Commutative square -/

/-- A 2×2 commutative square. Four labeled corners, four sides as
segments. The diagonal segment is dashed to suggest the composed
morphism `g ∘ f = k ∘ h`. -/
def commutativeSquare : Scene Pos2 :=
  let topL : Pos2 := (120, 100)
  let topR : Pos2 := (360, 100)
  let botL : Pos2 := (120, 340)
  let botR : Pos2 := (360, 340)
  {
    shapes := #[
      .point   "tl" topL,
      .point   "tr" topR,
      .point   "bl" botL,
      .point   "br" botR,
      .segment "top"      topL topR,
      .segment "right"    topR botR,
      .segment "bottom"   botL botR,
      .segment "left"     topL botL,
      .segment "diagonal" topL botR .dashed
    ]
    annotations := #[
      .label "tl" "A",
      .label "tr" "B",
      .label "bl" "C",
      .label "br" "D",
      .label "top"      "f",
      .label "right"    "g",
      .label "bottom"   "h",
      .label "left"     "k",
      .label "diagonal" "g ∘ f = k ∘ h"
    ]
  }


/-! ## Number line -/

/-- A number line with marked integer ticks. Demonstrates `.line`
viewport extension and labeled points along it. -/
def numberLine : Scene Pos2 :=
  let y : Float := 240
  let tick (n : Nat) : Pos2 := (60 + 60 * n.toFloat, y)
  {
    shapes := #[
      .line "axis" (0, y) (480, y) .bold,
      .point "p0" (tick 0),
      .point "p1" (tick 1),
      .point "p2" (tick 2),
      .point "p3" (tick 3),
      .point "p4" (tick 4),
      .point "p5" (tick 5),
      .point "p6" (tick 6)
    ]
    annotations := #[
      .label "p0" "0",
      .label "p1" "1",
      .label "p2" "2",
      .label "p3" "3",
      .label "p4" "4",
      .label "p5" "5",
      .label "p6" "6"
    ]
  }


/-! ## Inspection helpers

Cursor on these to preview in InfoView, or `lake env lean --run` a
file that calls these and writes to disk to view in a browser. -/

#eval IO.println (Renderable.render (out := String) commutativeSquare)
#eval IO.println (Renderable.render (out := String) numberLine)

end Figures.Examples
