/-
Figures/Category.lean — top-level entry point for category-theory
commutative-diagram support.

Importing `Figures.Category` brings in the IR, layout templates, and
the `Lowering.lower : Diagram → Except _ (Scene Pos2 × Pos2)` entry
point. The DSL surface (parser for `commutative diagram` mode inside
`construction { … }`) is in `Figures.Category.Syntax`.
-/

import Figures.Category.IR
import Figures.Category.Layout
import Figures.Category.Lowering
