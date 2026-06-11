/-
Figures/Construction/Syntax.lean — Surface syntax for the Construction DSL.

Provides a `construction { … }` term-level block whose body uses the
three-verb syntax:

  construction {
    exists P Q : Point
    assert distinct P Q
    construct lPQ := line_through P Q
  }

elaborates to a `Figures.Construction.DSL.Construction` value.

Lives in figures (not in a consumer) so the surface syntax stays
adjacent to the IR types it lowers to. Consumer namespaces (giyf's
`Geometry.*`) consume the DSL but don't extend it; new constraint heads
are just new strings on the `assert` / `construct` line.
-/

import Lean
import Figures.Construction.DSL

namespace Figures.Construction.DSL

open Lean

/-- Argument to a constraint head: just an identifier in V1. The
expression `head a b c` lowers to `.app "head" [.name "a", .name "b",
.name "c"]`. Numeric literals and nested expressions will land here
later when needed. -/
declare_syntax_cat constrArg
syntax ident : constrArg

declare_syntax_cat constructionStmt
-- `rawIdent` (not `ident`) for head positions so keywords reserved in
-- consumer namespaces (like giyf's `distinct` and `collinear`) still
-- parse as construction heads here.
syntax "exists " ident+ " : " ident                      : constructionStmt
syntax "assert " rawIdent constrArg*                     : constructionStmt
syntax "assert " "¬" rawIdent constrArg*                 : constructionStmt
syntax "construct " ident " := " rawIdent constrArg*     : constructionStmt
syntax "focus " ident                                    : constructionStmt
syntax "hidden " ident+                                  : constructionStmt

syntax (name := constructionBlock) "construction" "{" constructionStmt* "}" : term

private def argToExpr (s : TSyntax `constrArg) : MacroM (TSyntax `term) :=
  match s with
  | `(constrArg| $i:ident) =>
    let lit := Syntax.mkStrLit i.getId.toString
    `(Figures.ConstraintExpr.name $lit)
  | _ => Macro.throwUnsupported

private def argsListExpr (args : Array (TSyntax `constrArg)) : MacroM (TSyntax `term) := do
  let exprs ← args.mapM argToExpr
  `([$exprs,*])

private def stmtToTerm (s : TSyntax `constructionStmt) : MacroM (TSyntax `term) :=
  match s with
  | `(constructionStmt| exists $names:ident* : $sort:ident) => do
    let nameStrs := names.map (fun n => Syntax.mkStrLit n.getId.toString)
    let sortStr  := Syntax.mkStrLit sort.getId.toString
    `(Figures.Construction.DSL.Stmt.«exists» #[$nameStrs,*] $sortStr)
  | `(constructionStmt| assert $head:ident $args:constrArg*) => do
    let headStr := Syntax.mkStrLit head.getId.toString
    let argsList ← argsListExpr args
    `(Figures.Construction.DSL.Stmt.assert (Figures.ConstraintExpr.app $headStr $argsList))
  | `(constructionStmt| assert ¬ $head:ident $args:constrArg*) => do
    let headStr := Syntax.mkStrLit head.getId.toString
    let argsList ← argsListExpr args
    `(Figures.Construction.DSL.Stmt.assert
        (Figures.ConstraintExpr.app "¬" [Figures.ConstraintExpr.app $headStr $argsList]))
  | `(constructionStmt| construct $name:ident := $head:ident $args:constrArg*) => do
    let nameStr := Syntax.mkStrLit name.getId.toString
    let headStr := Syntax.mkStrLit head.getId.toString
    let argsList ← argsListExpr args
    `(Figures.Construction.DSL.Stmt.construct $nameStr (Figures.ConstraintExpr.app $headStr $argsList))
  | `(constructionStmt| focus $name:ident) => do
    let nameStr := Syntax.mkStrLit name.getId.toString
    `(Figures.Construction.DSL.Stmt.assert
        (Figures.ConstraintExpr.app "focus" [Figures.ConstraintExpr.name $nameStr]))
  | `(constructionStmt| hidden $names:ident*) => do
    let nameExprs ← names.mapM (fun n => do
      let lit := Syntax.mkStrLit n.getId.toString
      `(Figures.ConstraintExpr.name $lit))
    `(Figures.Construction.DSL.Stmt.assert
        (Figures.ConstraintExpr.app "hidden" [$nameExprs,*]))
  | _ => Macro.throwUnsupported

macro_rules
  | `(construction { $stmts:constructionStmt* }) => do
    let stmtTerms ← stmts.mapM stmtToTerm
    `({ stmts := #[$stmtTerms,*] : Figures.Construction.DSL.Construction })

end Figures.Construction.DSL
