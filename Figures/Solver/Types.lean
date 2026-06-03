/-
Figures/Solver/Types.lean — data model for the force-directed solver.

The solver positions a set of named particles by integrating springs
and forces while satisfying hard-constraint projections. This file
defines the value types only; integration logic is in
`Figures/Solver/Integrator.lean`.

Verlet was chosen over explicit-velocity Euler so projections compose
cleanly with the integrator: after a projection mutates `pos`, the
implicit velocity `(pos - prev) / dt` automatically reflects the
correction with no separate velocity field to keep in sync.
-/

import Figures
import Figures.Vec2

namespace Figures.Solver

abbrev ParticleId := Nat

/-- A movable point. `prev` carries Verlet's implicit velocity:
the next step computes velocity as `(pos - prev) / dt`. -/
structure Particle where
  id     : ParticleId
  name   : Name
  pos    : Pos2
  prev   : Pos2
  pinned : Bool := false
deriving Inhabited

/-- A pairwise spring at rest length `rest` with stiffness `stiffness`.
Stiffness is jittered at world construction time (in [0.7, 1.3] ×
baseline) to break accidental symmetries like exact equilateral
triangles. -/
structure Spring where
  a         : ParticleId
  b         : ParticleId
  rest      : Float
  stiffness : Float
deriving Inhabited

/-- A hard constraint applied after each integration sub-step as a
position projection. Whole-array signature so a projection can read
other particles' state (e.g. project X onto segment AB requires
reading A and B). Order matters: projections are applied in
Gauss-Seidel order — each sees the post-previous-projection state. -/
abbrev Projection := Array Particle → Array Particle

/-- A soft constraint contributing a force vector per particle each
step. Forces accumulate (Jacobi-style): the integrator sums across
all forces, then advances positions in one Verlet step. -/
abbrev Force := Array Particle → Array Pos2

/-- The full solver state. -/
structure World where
  particles   : Array Particle
  springs     : Array Spring   := #[]
  projections : Array Projection := #[]
  forces      : Array Force      := #[]

/-- Solver knobs. Defaults tuned for typical 4-10-point figures from
a warm-start initial layout. -/
structure SolverConfig where
  /-- Integration timestep. -/
  dt        : Float := 0.5
  /-- Velocity damping per step (1 = none, 0 = critically damped). -/
  damping   : Float := 0.85
  /-- Hard cap on steps; abort even if not converged. -/
  maxSteps  : Nat   := 200
  /-- Convergence threshold on total kinetic energy. -/
  energyEps : Float := 1e-3
deriving Inhabited

end Figures.Solver
