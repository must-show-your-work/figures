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

-- Preview tool: dump each `Figures.Examples` scene to /tmp/figures-*.svg
-- so the renderer's output can be inspected in a browser without
-- needing atlas / lean.nvim. Run with `lake exe preview-examples`.
lean_exe "preview-examples" where
  root := `scripts.PreviewExamples
