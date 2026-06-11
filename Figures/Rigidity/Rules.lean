/-
Figures/Rigidity/Rules.lean — aggregator for built-in anti-regularity
rules.

Importing this brings every default rule into the env. Downstream
packages can register additional rules via the `@[anti_regularity N]`
attribute without modifying this file.
-/

import Figures.Rigidity.Rules.AvoidCollinear
import Figures.Rigidity.Rules.AvoidMidpoint
import Figures.Rigidity.Rules.AvoidEquilateral
import Figures.Rigidity.Rules.Between
import Figures.Rigidity.Rules.OnLine
import Figures.Rigidity.Rules.Equal
import Figures.Rigidity.Rules.AvoidIsoceles
