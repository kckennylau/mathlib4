/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

/-! # Notation for Filter.Tendsto -/

namespace Filter

open Topology Lean Elab Term

declare_syntax_cat limit

syntax ppSpace "∞" : limit
syntax ppSpace "-∞" : limit
syntax ppSpace term : limit
syntax ("[≠] " <|> "[<] " <|> "[≤] " <|> "[>] " <|> "[≥] ") term : limit

scoped
syntax:49 term:max " ⟶[" Lean.Parser.Term.funBinder " →" limit "]" limit : term

def parseLimit {m : Type → Type} [Monad m] [MonadQuotation m] :
    TSyntax `limit → m Term
  | `(limit| $t:term) => `(nhds $t)
  | `(limit| ∞) => `(atTop)
  | `(limit| -∞) => `(atBot)
  | `(limit| [≠] $t:term) => `(𝓝[≠] $t)
  | `(limit| [<] $t:term) => `(𝓝[<] $t)
  | `(limit| [≤] $t:term) => `(𝓝[≤] $t)
  | `(limit| [>] $t:term) => `(𝓝[>] $t)
  | `(limit| [≥] $t:term) => `(𝓝[≥] $t)
  | _ => default

macro_rules
| `($fx ⟶[$x →$src]$tgt) => do
  let fn ← `(fun $x ↦ $fx)
  `(Tendsto $fn $(← parseLimit src) $(← parseLimit tgt))

open PrettyPrinter Delaborator

def limitDelab : DelabM (TSyntax `limit) := do
  match (← SubExpr.getExpr).getAppFnArgs with
  | (``nhds, _) =>
    let t ← SubExpr.withNaryArg 2 delab
    `(limit| $t:term)
  | (``nhdsWithin, #[_, _, _, s]) =>
    match s.getAppFnArgs with
    | (``Set.Ici, _) =>
      let t ← SubExpr.withNaryArg 3 <| SubExpr.withNaryArg 2 delab
      `(limit| [≥] $t)
    | (``Set.Iic, _) =>
      let t ← SubExpr.withNaryArg 3 <| SubExpr.withNaryArg 2 delab
      `(limit| [≤] $t)
    | (``Set.Ioi, _) =>
      let t ← SubExpr.withNaryArg 3 <| SubExpr.withNaryArg 2 delab
      `(limit| [>] $t)
    | (``Set.Iio, _) =>
      let t ← SubExpr.withNaryArg 3 <| SubExpr.withNaryArg 2 delab
      `(limit| [<] $t)
    | (``HasCompl.compl, #[_, _, s]) =>
      match s.getAppFnArgs with
      | (``Singleton.singleton, _) =>
        let t ← SubExpr.withNaryArg 3 <| SubExpr.withNaryArg 2 <| SubExpr.withNaryArg 3 delab
        `(limit| [≠] $t)
      | _ => failure
    | _ => failure
  | _ => failure

@[app_delab Tendsto] def tendstoDelab : Delab := whenPPOption Lean.getPPNotation do
  let fn ← SubExpr.withNaryArg 2 delab
  let src ← SubExpr.withNaryArg 3 limitDelab
  let tgt ← SubExpr.withNaryArg 4 limitDelab
  let `(fun $x ↦ $fx) := fn | failure
  `($fx ⟶[$x →$src] $tgt)

variable {α : Type*} [Pow α ℕ] [Preorder α] [TopologicalSpace α] (x : α)
#check (y ^ 2) ⟶[y →[<] x] x ^ 2
#check y ⟶[y →[≤] x] x
#check y ⟶[y →[>] x] x
#check y ⟶[y →[≥] x] x
#check y ⟶[y →[≠] x] x
#check y ⟶[y → x] x
#check y ⟶[y → x][≠] x
#check y ⟶[y → x][<] x
#check y ⟶[y → ∞][<] x
#check PrettyPrinter.Unexpander
#check iInf_delab
end Filter
