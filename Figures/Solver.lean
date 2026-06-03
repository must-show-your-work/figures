/-
Figures/Solver.lean — public entry point for the force-directed
layout solver. Re-exports the data types and the `solve` loop;
downstream callers should import this rather than the internal files.
-/

import Figures.Solver.Types
import Figures.Solver.Integrator
import Figures.Solver.Projections
import Figures.Solver.Forces
import Figures.Solver.LabelLayout
