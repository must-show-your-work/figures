/-
Figures/Construction/Matchers/Logical.lean — aggregator for the
logical-decomposition matchers shipped with figures.

Importing this brings the And / Iff / Not / Pi matchers into the env
at low priority (5), so they fire as structural fallbacks when no
higher-priority geometric matcher claims the type.
-/

import Figures.Construction.Matchers.Logical.And
import Figures.Construction.Matchers.Logical.Iff
import Figures.Construction.Matchers.Logical.Not
import Figures.Construction.Matchers.Logical.Pi
