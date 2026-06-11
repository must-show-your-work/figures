/-
Figures/Construction/ProofState.lean — open registry of proof-state →
DSL matchers.

A **matcher** is a function `Expr → MetaM (Option (Array Stmt))` that
recognizes a particular Prop shape (`Geometry.Theory.Angle`,
`Geometry.Theory.Between`, `Circle`, whatever) and emits the
corresponding DSL stmts — including any implied constructions (e.g.,
the two rays of an angle that aren't textually present in the type).

Consumers (giyf, EWM, future apps) register matchers with the
`@[proof_state_matcher P]` attribute, where `P` is an optional Nat
priority (default 0). Higher priorities run first. The convention
(rule of thumb):

  level 0    — leaf constraints (no implied constructions)
  level 100  — composite of leaves (Angle = two rays + noncollinear)
  level 200  — composite of composites (Triangle = three angle-pairs
                                        rendered as three segments)
  level 300+ — higher arrangements

A composite matcher's priority = S(max(priority of parts it would
otherwise decompose to)). This ensures the matcher that recognizes the
LARGEST gestalt fires first; constituent matchers never run for that
decl.

The `classify` helper tries registered matchers in priority order
(stable on ties: registration order wins) and returns the first hit's
stmts. Consumers fall back to a structural walker (And/Not/etc.) on
miss.
-/

import Lean
import Figures.Construction.DSL

namespace Figures.Construction.ProofState

open Lean Meta Elab

/-- A matcher: try to recognize an Expr as a known Prop shape and emit
the corresponding DSL stmts. `none` means "I don't handle this shape";
the registry tries the next matcher. -/
abbrev Matcher := Expr → MetaM (Option (Array Figures.Construction.DSL.Stmt))

/-- Registered matcher entry: the decl name (resolved at call time) +
its priority. -/
structure MatcherEntry where
  declName : Lean.Name
  priority : Nat
  deriving Inhabited, Repr

/-- Env-extension of registered matchers. Aggregated across imported
modules; entries persist in `.olean` so importing a matcher-bearing
module makes it visible to the classifier. -/
initialize matchersExt :
    SimplePersistentEnvExtension MatcherEntry (Array MatcherEntry) ←
  registerSimplePersistentEnvExtension {
    name := `Figures.Construction.ProofState.matchersExt
    addEntryFn    := Array.push
    addImportedFn := fun ass => ass.foldl Array.append #[]
  }

/-- Attribute syntax: `@[proof_state_matcher]` or
`@[proof_state_matcher 100]`. -/
syntax (name := proofStateMatcher)
  "proof_state_matcher" (num)? : attr

initialize registerBuiltinAttribute {
  name  := `proofStateMatcher
  descr := "Registers a function (Expr → MetaM (Option (Array Stmt))) as a proof-state classifier matcher. Optional Nat priority — higher beats lower; ties broken by registration order."
  add declName stx _kind := do
    let priority : Nat ← match stx with
      | `(attr| proof_state_matcher $n:num) => pure n.getNat
      | `(attr| proof_state_matcher)        => pure 0
      | _ => throwError "proof_state_matcher: malformed attribute syntax"
    modifyEnv (matchersExt.addEntry · ⟨declName, priority⟩)
}

/-- Try each registered matcher in descending priority order; return
the first `some` hit's stmts, or `none` if no matcher applied. -/
def classify (e : Expr) : MetaM (Option (Array Figures.Construction.DSL.Stmt)) := do
  let env ← getEnv
  let entries := (matchersExt.getState env).qsort (·.priority > ·.priority)
  for entry in entries do
    let fn ← unsafe evalConstCheck Matcher
      ``Figures.Construction.ProofState.Matcher entry.declName
    if let some result ← fn e then return some result
  return none

end Figures.Construction.ProofState
