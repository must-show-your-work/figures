/-
Figures/Construction/DSL.lean — IR for the construction DSL.

A `Construction` is a flat sequence of `Stmt`s describing fresh
objects, asserted constraints, and constructed derived objects. The
type is **domain-agnostic** — figures owns the shape; consumers (giyf
for synthetic geometry, EWM, future animation/Manim-style frontends)
attach their own semantics by pattern-matching on `ConstraintExpr`
heads.

Lives in figures (not in a consumer) so the IR can be shared across
backends and the proof-state matcher registry (`ProofState.lean`) has
a target type that doesn't pull in any consumer-specific code.
-/

import Figures

namespace Figures.Construction.DSL

open Figures

inductive Stmt where
  | «exists»  (names : Array Name) (sort : Name) : Stmt
  | assert    (claim : ConstraintExpr) (description : String := "") : Stmt
  | construct (name : Name) (expr : ConstraintExpr) : Stmt
  /-- Mode marker: switches the construction's processing pipeline.
  Current modes: `"commutative diagram"` (handled by
  `Figures.Category.Lowering`). Geometry constructions have no mode
  marker; absence of any `mode` stmt = geometry mode. -/
  | mode      (name : String) : Stmt
  /-- Category-diagram statement: declare a node.
  `label` is a raw display source (LaTeX string in V1.5+, plain text
  for V1). Only meaningful in `commutative diagram` mode. -/
  | node      (name : Name) (label : String) : Stmt
  /-- Category-diagram statement: declare a directed edge.
  `head` is the arrowhead style (standard / hooked / double / iso /
  none). Only meaningful in `commutative diagram` mode. -/
  | edge      (source target : Name) (label : String)
              (head : Figures.ArrowHead := .standard) : Stmt
  /-- Category-diagram statement: assert that two or more paths
  through the diagram commute. Each path is a sequence of node names.
  Only meaningful in `commutative diagram` mode. -/
  | commutes  (paths : Array (Array Name)) : Stmt
  /-- Category-diagram statement: pin the diagram's layout to a
  named template (overrides the auto-classifier). Examples: `"square"`,
  `"triangle"`. Only meaningful in `commutative diagram` mode. -/
  | layoutHint (template : String) : Stmt
  deriving Repr, Inhabited

structure Construction where
  stmts : Array Stmt
  deriving Repr, Inhabited

private partial def exprToString : ConstraintExpr → String
  | .name n   => n
  | .num k    => toString k
  | .app f [] => f
  | .app f args =>
    let parts := args.map fun a => match a with
      | .app _ [] | .name _ | .num _ => exprToString a
      | _ => "(" ++ exprToString a ++ ")"
    f ++ " " ++ String.intercalate " " parts

private def arrowHeadString : Figures.ArrowHead → String
  | .standard => "→"
  | .hooked   => "↪"
  | .double   => "↠"
  | .iso      => "≃"
  | .none     => "→"

def printStmt : Stmt → String
  | .«exists» names sort =>
    "exists " ++ String.intercalate " " names.toList ++ " : " ++ sort
  | .assert claim "" =>
    "assert " ++ exprToString claim
  | .assert claim desc =>
    "assert " ++ exprToString claim ++ "    -- " ++ desc
  | .construct name expr =>
    "construct " ++ name ++ " := " ++ exprToString expr
  | .mode name =>
    name
  | .node name label =>
    s!"node {name} \"{label}\""
  | .edge source target label head =>
    s!"arrow {source} {arrowHeadString head} {target} \"{label}\""
  | .commutes paths =>
    let renderPath := fun (p : Array Name) =>
      "[" ++ String.intercalate ", " p.toList ++ "]"
    "commutes " ++ String.intercalate " " (paths.toList.map renderPath)
  | .layoutHint template =>
    s!"layout {template}"

def printConstruction (c : Construction) : String :=
  String.intercalate "\n" (c.stmts.toList.map printStmt)

/-- Sentinel stmt: signals "use proof-state inference for this figure."
A `construction { infer }` block lowers to a `Construction` containing
just this stmt. Downstream dispatchers detect it and route to the
proof-state path instead of rendering the DSL literally. -/
def inferMarker : Stmt :=
  .assert (.app "__infer__" []) "use proof-state inference"

/-- Does this construction opt into proof-state inference? -/
def Construction.isInfer (c : Construction) : Bool :=
  c.stmts.any fun s => match s with
    | .assert (.app "__infer__" _) _ => true
    | _ => false

end Figures.Construction.DSL
