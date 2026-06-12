/-
Figures/Construction/Matchers/Logical/Exists.lean — telescope ∃ and ∃!
binders, emit existential stmts for Point/Line binders, then classify
the body.

For a goal like `∃ X : Point, L intersects M at X`, the LCtx walk in
`extract` doesn't see `X` (it's bound inside the existential). This
matcher opens the lambda, looks at each binder's type, emits the
appropriate `exists` stmt for Point/Line binders, and recursively
classifies the now-open body — picking up `L intersects M at X` and
similar.

Same shape as `matchPi` for ∀, mutatis mutandis.
-/

import Figures.Construction.ProofState

namespace Figures.Construction.Matchers.Logical

open Lean Meta
open Figures.Construction.DSL Figures.Construction.ProofState

private def collectBinderStmts (binders : Array Expr) :
    MetaM (Array Stmt) := do
  let mut acc : Array Stmt := #[]
  for b in binders do
    let bTy ← instantiateMVars (← inferType b)
    -- String-match on the constant name — figures doesn't link giyf,
    -- so we can't reference `Geometry.Theory.Point` directly.
    if bTy.isConstOf `Geometry.Theory.Point then
      let decl ← b.fvarId!.getDecl
      acc := acc.push (.«exists» #[decl.userName.toString] "Point")
    else if bTy.isConstOf `Geometry.Theory.Line then
      let decl ← b.fvarId!.getDecl
      acc := acc.push (.«exists» #[decl.userName.toString] "Line")
    else
      acc := acc ++ (← classify bTy).getD #[]
  return acc

@[proof_state_matcher 5]
def matchExists : Matcher := fun e => do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``Exists, #[_, body]) =>
    lambdaTelescope body fun binders bodyOpen => do
      let bs ← collectBinderStmts binders
      let conclStmts := (← classify bodyOpen).getD #[]
      return some (bs ++ conclStmts)
  | _ => return none

-- `∃!` desugars to `ExistsUnique`. Use a string-literal Name (single
-- backtick) so figures doesn't need to import the declaring module.
@[proof_state_matcher 5]
def matchExistsUnique : Matcher := fun e => do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (`ExistsUnique, #[_, body]) =>
    lambdaTelescope body fun binders bodyOpen => do
      let bs ← collectBinderStmts binders
      let conclStmts := (← classify bodyOpen).getD #[]
      return some (bs ++ conclStmts)
  | _ => return none

end Figures.Construction.Matchers.Logical
