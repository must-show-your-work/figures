/-
scripts/PreviewExamples.lean — Dump each example scene to
`/tmp/figures-<name>.svg` so you can `xdg-open` / preview in a
browser. Avoids needing atlas / lean.nvim to inspect output.

Run:
    lake exe preview-examples
-/

import Figures
import Figures.SVG
import Figures.Examples

open Figures Figures.Examples

def previewOne (name : String) (s : Scene Pos2) : IO Unit := do
  let path := s!"/tmp/figures-{name}.svg"
  let svg : String := Renderable.render s
  IO.FS.writeFile path svg
  IO.println s!"wrote {path} ({svg.length} bytes)"

def main : IO Unit := do
  previewOne "commutative-square" commutativeSquare
  previewOne "number-line" numberLine
  IO.println ""
  IO.println "Open with:  xdg-open /tmp/figures-commutative-square.svg"
  IO.println "or:         firefox /tmp/figures-commutative-square.svg"
