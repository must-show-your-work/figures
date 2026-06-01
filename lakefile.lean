import Lake
open Lake DSL

-- figures: a Lean 4 library for declarative figures (geometric and
-- otherwise), with an IR + multi-backend rendering pipeline. Extracted
-- from giyf/atlas so it can be consumed independently of the geometry
-- theorem-prover stack.
--
-- See `Figures.lean` for the entry point: IR (`Figures.Construction`)
-- + standard SVG backend. Pluggable backends via a typeclass (TBD).

package "figures" where
  version := v!"0.1.0"

-- Core library. No external Lean deps beyond Std (HashMap). Consumers
-- (atlas, giyf, etc.) `require figures` to get the IR + renderers.
@[default_target]
lean_lib «Figures» where
  srcDir := "."
  roots := #[`Figures]
