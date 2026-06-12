/-
Figures/Rigidity/Rules/CollinearOrder.lean — global placement for a
collinear group with chained betweenness.

When several `between` annotations share members of a single collinear
group (e.g. `between A B C` ∧ `between A C D` ∧ `between B C D` for
Prop 3.3.i), the per-triple Between rule (priority 150) places each
middle at 1/3 of its endpoints' positions. With chained betweens this
clusters joints near the canvas edge: B at 1/9 along AD, C at 1/3
along AD, D at the right edge — A, B, C collapse onto the left third.

This rule fires at priority 160 (above Between) when:
  - the candidate joint is in a `collinear` annotation of size ≥ 3
  - that group has at least one `between` annotation
  - a linear order on the group consistent with all betweens exists
  - the order's two endpoints are already placed

It places the candidate at index `i / (n-1)` along the line from
order[0] to order[n-1], so all middles spread evenly. For n=3 it
falls back to 1/3 (not midpoint — Joe's not-midpoint rule).
-/

import Figures.Rigidity.AntiRegularity
import Figures.Vec2

namespace Figures.Rigidity.Rules

open Figures Figures.Rigidity

/-- Permutations of an array (Heap-style recursion). Cheap for the
group sizes we care about (≤ 6). -/
private partial def permutations {α : Type} [Inhabited α] (a : Array α) : Array (Array α) := Id.run do
  if a.size ≤ 1 then return #[a]
  let mut result : Array (Array α) := #[]
  for i in [0:a.size] do
    let chosen := a[i]!
    let rest := (a.extract 0 i) ++ (a.extract (i+1) a.size)
    for p in permutations rest do
      result := result.push (#[chosen] ++ p)
  return result

/-- Check that a candidate linear order is consistent with every
`between a x b` triple: x's index must lie strictly between a's and
b's indices. -/
private def isConsistentOrder (order : Array Nat)
    (betweens : Array (Nat × Nat × Nat)) : Bool := Id.run do
  for (a, x, b) in betweens do
    let ia := order.findIdx? (· == a) |>.getD 0
    let ix := order.findIdx? (· == x) |>.getD 0
    let ib := order.findIdx? (· == b) |>.getD 0
    let ok := (ia < ix ∧ ix < ib) ∨ (ib < ix ∧ ix < ia)
    if !ok then return false
  return true

/-- Find a permutation of `group` consistent with all `betweens`. -/
private def linearOrder? (group : Array Nat)
    (betweens : Array (Nat × Nat × Nat)) : Option (Array Nat) := Id.run do
  for ord in permutations group do
    if isConsistentOrder ord betweens then return some ord
  none

/-- Fraction along the line for position index `i` in an `n`-point
order. For n=3 the lone middle goes at 1/3 (Joe's not-midpoint rule).
For n≥4 use even spacing i/(n-1). -/
private def fracAt (i n : Nat) : Float :=
  if n == 3 ∧ i == 1 then 1.0 / 3.0
  else i.toFloat / (n.toFloat - 1.0)

@[anti_regularity 160]
def collinearOrder : Chooser := fun ctx => do
  -- Smallest collinear group containing this joint.
  let groupOpt := ctx.graph.annotations.findSome? fun ann => match ann with
    | .collinear ids => if ids.contains ctx.joint then some ids else none
    | _ => none
  let some groupIds := groupOpt | return none
  if groupIds.size < 3 then return none
  let betweens : Array (Nat × Nat × Nat) :=
    ctx.graph.annotations.filterMap fun ann => match ann with
    | .between a x b =>
      if groupIds.contains a ∧ groupIds.contains x ∧ groupIds.contains b then
        some (a, x, b)
      else none
    | _ => none
  if betweens.isEmpty then return none
  let some order := linearOrder? groupIds betweens | return none
  let some myIdx := order.findIdx? (· == ctx.joint) | return none
  let endpoint0 := order[0]!
  let endpointN := order[order.size - 1]!
  -- Both endpoints must be placed for interpolation.
  match ctx.posOf endpoint0, ctx.posOf endpointN with
  | some p0, some pN =>
    let frac := fracAt myIdx order.size
    return some (p0.x + (pN.x - p0.x) * frac, p0.y + (pN.y - p0.y) * frac)
  | _, _ => return none

end Figures.Rigidity.Rules
