/-
Figures/Category/Examples.lean — hand-built diagrams that exercise
the IR → layout → lowering → SVG pipeline end-to-end.

These also serve as the first integration tests: every example
constructs a `Diagram`, lowers it to a `Scene Pos2`, runs the SVG
backend, and writes the result to disk under `figures/Examples/`.

Run with:
  lake env lean Figures/Category/Examples.lean
-/

import Figures
import Figures.Category
import Figures.Construction.DSL
import Figures.Construction.Syntax
import Figures.SVG

namespace Figures.Category.Examples

open Figures
open Figures.Category
open Figures.Construction.DSL

/-! ## Vakil 1.1.21 — Naturality square for α : F ⟹ G

A natural transformation α between functors F, G : 𝒜 → ℬ is the
data of a morphism α_A : F(A) → G(A) for each A ∈ 𝒜 such that for
each f : A ⟶ A' the following square commutes:

    F(A) ---- F(f) ----> F(A')
     |                    |
    α_A                  α_A'
     |                    |
     v                    v
    G(A) ---- G(f) ----> G(A')
-/

def naturalitySquare : Diagram := {
  nodes := #[
    { name := "FA",  label := .txt "F(A)"  },
    { name := "FA'", label := .txt "F(A')" },
    { name := "GA",  label := .txt "G(A)"  },
    { name := "GA'", label := .txt "G(A')" }
  ]
  edges := #[
    { source := "FA",  target := "FA'", label := .txt "F(f)" },
    { source := "GA",  target := "GA'", label := .txt "G(f)" },
    { source := "FA",  target := "GA",  label := .txt "α_A"  },
    { source := "FA'", target := "GA'", label := .txt "α_A'" }
  ]
  cells := #[
    { paths := #[#["FA", "FA'", "GA'"], #["FA", "GA", "GA'"]] }
  ]
  layout := some "square"
}

/-- Lower + render and return the SVG string for the naturality square. -/
def naturalitySquareSvg : Except String String := do
  let (scene, (w, h)) ← Lowering.lower naturalitySquare
  let canvas : SVG.Canvas := { width := w, height := h }
  return SVG.render scene canvas


/-! ## Same diagram via the DSL surface

Exercises the parser + Stmt → Diagram conversion + lowering + SVG.
Should produce the same SVG as `naturalitySquareSvg` above. -/

def naturalitySquareViaDsl : Construction := construction {
  commutative diagram
  as_layout square
  node FA "F(A)"
  node FA' "F(A')"
  node GA "G(A)"
  node GA' "G(A')"
  arrow FA → FA' "F(f)"
  arrow GA → GA' "G(f)"
  arrow FA → GA "α_A"
  arrow FA' → GA' "α_A'"
  commutes [FA, FA', GA'] [FA, GA, GA']
}

def naturalitySquareDslSvg : Except String String := do
  let some d := Diagram.fromConstruction naturalitySquareViaDsl
    | throw "construction has no `commutative diagram` mode marker"
  let (scene, (w, h)) ← Lowering.lower d
  let canvas : SVG.Canvas := { width := w, height := h }
  return SVG.render scene canvas

end Figures.Category.Examples
