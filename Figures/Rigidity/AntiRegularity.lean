/-
Figures/Rigidity/AntiRegularity.lean — open registry of anti-regularity
rules.

A **rule** is a function `Chooser := DoFContext → MetaM (Option Pos2)`
that recognizes a particular *accidental regularity* (collinearity,
equilateral, midpoint, etc.) and returns a perturbed position that
breaks it. `none` defers to the next rule; `some p` claims the
position.

Consumers register rules with the `@[anti_regularity P]` attribute,
where P is an optional Nat priority (default 0). Higher priorities run
first; ties break by registration order. The `chooseFor` helper walks
registered rules in priority order and returns the first hit.

Same architectural shape as `Figures.Construction.ProofState` — the
proof-state matcher registry. New rules are added by writing a file in
`Figures/Rigidity/Rules/` (or any consumer module), tagging the def
with `@[anti_regularity N]`, and importing the file somewhere on the
elab path so its `initialize` block runs.
-/

import Lean
import Figures.Rigidity.Types

namespace Figures.Rigidity.AntiRegularity

open Lean Meta

/-- Registered rule entry. -/
structure RuleEntry where
  declName : Lean.Name
  priority : Nat
  deriving Inhabited, Repr

/-- Env-extension of registered rules. Aggregated across imported
modules — importing a rule-bearing module makes the rule visible. -/
initialize rulesExt :
    SimplePersistentEnvExtension RuleEntry (Array RuleEntry) ←
  registerSimplePersistentEnvExtension {
    name := `Figures.Rigidity.AntiRegularity.rulesExt
    addEntryFn    := Array.push
    addImportedFn := fun ass => ass.foldl Array.append #[]
  }

/-- Attribute syntax: `@[anti_regularity]` or `@[anti_regularity 100]`. -/
syntax (name := antiRegularity)
  "anti_regularity" (num)? : attr

initialize registerBuiltinAttribute {
  name  := `antiRegularity
  descr := "Registers a function (DoFContext → MetaM (Option Pos2)) as an anti-regularity rule for the L_full geometric solver. Optional Nat priority — higher beats lower; ties broken by registration order."
  add declName stx _kind := do
    let priority : Nat ← match stx with
      | `(attr| anti_regularity $n:num) => pure n.getNat
      | `(attr| anti_regularity)        => pure 0
      | _ => throwError "anti_regularity: malformed attribute syntax"
    modifyEnv (rulesExt.addEntry · ⟨declName, priority⟩)
}

/-- Walk registered rules in descending priority order; return the
first `some p` hit, or `none` if no rule applied. -/
def chooseFor (ctx : Figures.Rigidity.DoFContext) :
    MetaM (Option Figures.Pos2) := do
  let env ← getEnv
  let entries := (rulesExt.getState env).qsort (·.priority > ·.priority)
  for entry in entries do
    let fn ← unsafe evalConstCheck Figures.Rigidity.Chooser
      ``Figures.Rigidity.Chooser entry.declName
    if let some result ← fn ctx then return some result
  return none

end Figures.Rigidity.AntiRegularity
