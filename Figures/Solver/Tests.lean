/-
Figures/Solver/Tests.lean — pure unit tests for solver primitives.

These tests check each force / projection in isolation by constructing
a tiny `World` directly and asserting the expected post-`solve` state.
They don't go through the giyf DSL, so a regression that breaks one
of these primitives surfaces here before the higher-level stress
fixtures (which can mask a primitive bug behind other forces).

Run with: `lake env lean --run Figures/Solver/Tests.lean`
-/

import Figures
import Figures.Vec2
import Figures.Solver

open Figures Figures.Solver

namespace Figures.Solver.Tests

private def near (a b eps : Float) : Bool := (a - b).abs < eps

/-- Two particles + one spring converge to the spring's rest length. -/
def testSpringConvergence : IO Bool := do
  let world : World := {
    particles := #[
      { id := 0, name := "A", pos := (0, 0),  prev := (0, 0),  pinned := false },
      { id := 1, name := "B", pos := (50, 0), prev := (50, 0), pinned := false }
    ]
    springs := #[{ a := 0, b := 1, rest := 100, stiffness := 1.0 }]
  }
  let solved := Solver.solve { maxSteps := 200 } world
  let dx := solved.particles[1]!.pos.x - solved.particles[0]!.pos.x
  let dy := solved.particles[1]!.pos.y - solved.particles[0]!.pos.y
  let len := (dx * dx + dy * dy).sqrt
  return near len 100 1.0

/-- `Projections.between` clamps the middle particle onto the segment
interior. C starts above AB; after one solve step the projection
snaps it back onto the segment, regardless of springs. -/
def testBetweenProjection : IO Bool := do
  let world : World := {
    particles := #[
      { id := 0, name := "A", pos := (0, 0),   prev := (0, 0),   pinned := true },
      { id := 1, name := "B", pos := (100, 0), prev := (100, 0), pinned := true },
      { id := 2, name := "X", pos := (60, 30), prev := (60, 30), pinned := false }
    ]
    projections := #[Projections.between 0 2 1]
  }
  let solved := Solver.solve { maxSteps := 5 } world
  return near solved.particles[2]!.pos.y 0 0.5

/-- `Projections.intersect2` snaps a particle to the line-line
intersection of two segments. Lines AB (y=0) and CD (x=50, vertical)
intersect at (50, 0). -/
def testIntersect2Projection : IO Bool := do
  let world : World := {
    particles := #[
      { id := 0, name := "A", pos := (0,   0),  prev := (0,   0),  pinned := true },
      { id := 1, name := "B", pos := (100, 0),  prev := (100, 0),  pinned := true },
      { id := 2, name := "C", pos := (50,  -50), prev := (50,  -50), pinned := true },
      { id := 3, name := "D", pos := (50,  50),  prev := (50,  50),  pinned := true },
      { id := 4, name := "X", pos := (10,  10),  prev := (10,  10),  pinned := false }
    ]
    projections := #[Projections.intersect2 0 1 2 3 4]
  }
  let solved := Solver.solve { maxSteps := 3 } world
  let p := solved.particles[4]!.pos
  return near p.x 50 0.5 && near p.y 0 0.5

/-- `Forces.noncollinear` pushes a triangle off a degenerate
configuration. Springs are configured to want C exactly at the
midpoint of AB (rest = base/2 on both A-C and B-C). Without the
force, C settles on the line (y=0); with the force, C moves off. -/
def testNoncollinearForce : IO Bool := do
  let mkWorld (force? : Option Force) : World := {
    particles := #[
      { id := 0, name := "A", pos := (0,   0), prev := (0,   0), pinned := true },
      { id := 1, name := "B", pos := (100, 0), prev := (100, 0), pinned := true },
      { id := 2, name := "C", pos := (50,  0), prev := (50,  0), pinned := false }
    ]
    springs := #[
      { a := 1, b := 2, rest := 50, stiffness := 1.0 },
      { a := 0, b := 2, rest := 50, stiffness := 1.0 }
    ]
    forces := match force? with
      | some f => #[f]
      | none => #[]
  }
  let yWithout := (Solver.solve { maxSteps := 200 } (mkWorld none)).particles[2]!.pos.y.abs
  let yWith := (Solver.solve { maxSteps := 200 }
    (mkWorld (some (Forces.noncollinear 0 1 2 (strength := 2.0) (threshold := 1000))))).particles[2]!.pos.y.abs
  -- The force should produce a meaningful perpendicular displacement
  -- while springs alone leave C on the line.
  return near yWithout 0 0.1 && yWith > 1.0

def runAll : IO UInt32 := do
  let mut failures : Nat := 0
  let tests : List (String × IO Bool) := [
    ("spring-convergence",   testSpringConvergence),
    ("between-projection",   testBetweenProjection),
    ("intersect2-projection", testIntersect2Projection),
    ("noncollinear-force",   testNoncollinearForce)
  ]
  for (name, t) in tests do
    let ok ← t
    let tag := if ok then "PASS" else "FAIL"
    IO.println s!"{tag} {name}"
    if !ok then failures := failures + 1
  if failures == 0 then return 0 else return 1

end Figures.Solver.Tests

def main : IO UInt32 := Figures.Solver.Tests.runAll
