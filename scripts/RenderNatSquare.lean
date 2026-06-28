import Figures.Category.Examples

open Figures.Category.Examples

def main : IO Unit := do
  match naturalitySquareSvg with
  | .ok svg =>
    IO.FS.writeFile "natsquare.svg" svg
    IO.println "wrote natsquare.svg"
  | .error e =>
    IO.eprintln s!"render failed: {e}"
    IO.Process.exit 1
