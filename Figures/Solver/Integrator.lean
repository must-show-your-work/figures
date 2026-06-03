/-
Figures/Solver/Integrator.lean — Verlet step + solve loop.

Each step:
  1. accumulate forces (springs + registered Force fns)
  2. Verlet position update: new_pos = pos + damping·(pos - prev) + dt²·accel
  3. snap `prev ← pos`, `pos ← new_pos` (pinned particles untouched)
  4. apply projections in Gauss-Seidel order

Loop until total kinetic energy < `energyEps` or step count hits
`maxSteps`. KE is computed as the squared implicit-velocity norm
summed across non-pinned particles.
-/

import Figures.Vec2
import Figures.Solver.Types

namespace Figures.Solver

open Figures

/-- Spring force contribution for one Hooke spring (linear).
Returns the force vector applied to particle `a`; the equal-and-
opposite goes to `b`. -/
@[inline] private def springForce (parts : Array Particle) (s : Spring) : Pos2 :=
  let pa := parts[s.a]!.pos
  let pb := parts[s.b]!.pos
  let d := Pos2.sub pb pa
  let len := Pos2.norm d
  if len < 1e-9 then (0, 0)
  else
    let unit := Pos2.smul (1 / len) d
    Pos2.smul (s.stiffness * (len - s.rest)) unit

/-- Sum per-particle accelerations from all springs + force fns.
Spring contributions: each spring adds its force to both endpoints
(equal-and-opposite). All particles get the same unit mass; we treat
the spring/force outputs as accelerations directly. -/
private def accumulateAccel (w : World) : Array Pos2 := Id.run do
  let n := w.particles.size
  let mut accel : Array Pos2 := Array.replicate n (0, 0)
  for s in w.springs do
    let f := springForce w.particles s
    accel := accel.modify s.a (Pos2.add · f)
    accel := accel.modify s.b (Pos2.sub · f)
  for force in w.forces do
    let contrib := force w.particles
    for i in [0 : n] do
      accel := accel.modify i (Pos2.add · contrib[i]!)
  return accel

/-- One Verlet integration step. Computes acceleration, advances each
non-pinned particle, then runs projections in Gauss-Seidel order. -/
def step (cfg : SolverConfig) (w : World) : World :=
  let accel := accumulateAccel w
  let dt2 := cfg.dt * cfg.dt
  let advanced := w.particles.mapIdx fun i p =>
    if p.pinned then p
    else
      let drift := Pos2.smul cfg.damping (Pos2.sub p.pos p.prev)
      let kick  := Pos2.smul dt2 accel[i]!
      let newPos := Pos2.add (Pos2.add p.pos drift) kick
      { p with prev := p.pos, pos := newPos }
  let projected := w.projections.foldl (init := advanced) fun ps proj => proj ps
  { w with particles := projected }

/-- Total kinetic energy: Σ ‖pos - prev‖² across non-pinned particles. -/
def kineticEnergy (w : World) : Float :=
  w.particles.foldl (init := 0.0) fun acc p =>
    if p.pinned then acc
    else acc + Pos2.normSq (Pos2.sub p.pos p.prev)

/-- Loop `step` until KE drops below `cfg.energyEps` or step count
hits `cfg.maxSteps`. Returns the final world; caller reads positions
out of `world.particles`. -/
partial def solve (cfg : SolverConfig) (w₀ : World) : World :=
  let rec go (n : Nat) (w : World) : World :=
    if n ≥ cfg.maxSteps then w
    else
      let w' := step cfg w
      if kineticEnergy w' < cfg.energyEps then w'
      else go (n + 1) w'
  go 0 w₀

end Figures.Solver
