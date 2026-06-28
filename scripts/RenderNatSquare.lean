import Figures.Category.Examples

open Figures.Category.Examples

def main : IO Unit := do
  match naturalitySquareSvg, naturalitySquareDslSvg with
  | .ok handBuilt, .ok viaDsl =>
    IO.FS.writeFile "natsquare-hand.svg" handBuilt
    IO.FS.writeFile "natsquare-dsl.svg"  viaDsl
    IO.println "wrote natsquare-hand.svg and natsquare-dsl.svg"
    if handBuilt == viaDsl then
      IO.println "round-trip OK: DSL produces identical SVG to hand-built IR"
    else
      IO.println "ROUND-TRIP MISMATCH — outputs differ"
  | _, _ =>
    IO.eprintln "render failed"
    IO.Process.exit 1
