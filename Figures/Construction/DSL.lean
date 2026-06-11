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

def printStmt : Stmt → String
  | .«exists» names sort =>
    "exists " ++ String.intercalate " " names.toList ++ " : " ++ sort
  | .assert claim "" =>
    "assert " ++ exprToString claim
  | .assert claim desc =>
    "assert " ++ exprToString claim ++ "    -- " ++ desc
  | .construct name expr =>
    "construct " ++ name ++ " := " ++ exprToString expr

def printConstruction (c : Construction) : String :=
  String.intercalate "\n" (c.stmts.toList.map printStmt)

end Figures.Construction.DSL
