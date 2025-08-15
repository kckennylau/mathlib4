/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kenny Lau
-/

import Lean

-- import Mathlib.Algebra.MvPolynomial.Basic
-- import Mathlib.Algebra.Polynomial.Basic

/-!
The command `name_poly_vars` names variables in any combination of `Polynomial`, `MvPolynomial`,
`RatFunc`, `PowerSeries`, `MvPowerSeries`, and `LaurentSeries`, where the `Mv` is restricted to
`Fin n`.

The notation introduced by this command is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_poly_vars R[[X,Y]][t]⸨a⸩(u)

#check X -- X : R[[X,Y]][t]⸨a⸩(u)
#check t -- t : R[[X,Y]][t]⸨a⸩(u)
```

For the edge case of `MvPolynomial (Fin 1) R`, use the syntax `R[u,]` with a trailing comma.
-/

open Lean Elab Command

initialize registerTraceClass `name_poly_vars

namespace Mathlib.Tactic.NamePolyVars

section Syntax

/--
A variable that can be in the head position of a `name_poly_vars` command.
This is either an identifier or a term enclosed in parentheses.
-/
syntax polyesqueHead := ident <|> ("(" term ")")

-- syntax to allow specifying `MvPolynomial (Fin 1) R` with `R[t,]` and `Polynomial R` with `R[t]`
syntax polyesqueMv? := sepBy(ident,",",",",allowTrailingSep)

syntax polynomialMv? := "[" polyesqueMv? "]"
syntax powerSeriesMv? := "[[" polyesqueMv? "]]"
syntax ratFunc := "(" ident ")"
syntax laurentSeries := "⸨" ident "⸩"

syntax polyesqueBody := polynomialMv? <|> powerSeriesMv? <|> ratFunc <|> laurentSeries
syntax polyesque := polyesqueHead noWs polyesqueBody+

syntax (name := polyesque') polyesque : term

abbrev PolyesqueHead : Type := TSyntax ``polyesqueHead

abbrev Polyesque : Type := TSyntax ``polyesque

/-- Convert a `polyesqueHead` to a term. -/
def PolyesqueHead.term? : PolyesqueHead → Option Term
  | `(polyesqueHead| $k:ident) => some { raw := k.raw }
  | `(polyesqueHead| ($u:term)) => some u
  | _ => none

inductive PolyesqueType
  | polynomial | mvPolynomial | powerSeries | mvPowerSeries | ratFunc | laurentSeries
deriving DecidableEq, Repr

inductive Mv?
  | yes | no
deriving DecidableEq, Repr

def PolyesqueType.mv? : PolyesqueType → Mv?
  | .mvPolynomial => .yes
  | .mvPowerSeries => .yes
  | _ => .no

def Mv?.Vars : Mv? → Type
  | .yes => Array Name
  | .no => Name

def PolyesqueType.Vars (pt : PolyesqueType) : Type :=
  pt.mv?.Vars

def Mv?.Vars.raw : ∀ {b : Mv?} (_ : b.Vars), String
  | .yes, vars => .intercalate "," (vars.map toString).toList
  | .no, (var : Name) => s!"{var}"

def PolyesqueType.raw : ∀ (pt : PolyesqueType), (_ : pt.Vars) → String
  | .polynomial, var => s!"[{var.raw}]"
  | .mvPolynomial, vars => s!"[{vars.raw}]"
  | .powerSeries, var => s!"[[{var.raw}]]"
  | .mvPowerSeries, vars => s!"[[{vars.raw}]]"
  | .ratFunc, var => s!"({var.raw})"
  | .laurentSeries, var => s!"⸨{var.raw}⸩"

def PolyesqueType.mkC (t : Term) : PolyesqueType → CommandElabM Term
  | .polynomial => `(Polynomial.C $t)
  | .mvPolynomial => `(MvPolynomial.C $t)
  | .powerSeries => `(PowerSeries.C _ $t)
  | .mvPowerSeries => `(MvPowerSeries.C _ _ $t)
  | .ratFunc => `(RatFunc.C $t)
  | .laurentSeries => `(HahnSeries.C $t)

def PolyesqueType.mkX : ∀ (pt : PolyesqueType) (_ : pt.Vars), CommandElabM (Array (Name × Term))
  | .polynomial, var => return #[(var, ← `(Polynomial.X))]
  | .mvPolynomial, vars =>
    vars.zipIdx.mapM fun n ↦ do return (n.fst, ← `(MvPolynomial.X $(quote n.snd)))
  | .powerSeries, var => return #[(var, ← `(PowerSeries.X))]
  | .mvPowerSeries, vars =>
    vars.zipIdx.mapM fun n ↦ do return (n.fst, ← `(MvPowerSeries.X $(quote n.snd)))
  | .ratFunc, var => return #[(var, ← `(RatFunc.X))]
  | .laurentSeries, var => return #[(var, ← `(HahnSeries.single 1 1))]

def PolyesqueType.mkTerm : ∀ pt : PolyesqueType, pt.Vars → Term → CommandElabM Term
  | .polynomial, _, ih => `(Polynomial $ih)
  | .mvPolynomial, vars, ih => `(MvPolynomial (Fin $(quote vars.size)) $ih)
  | .powerSeries, _, ih => `(PowerSeries $ih)
  | .mvPowerSeries, vars, ih => `(MvPowerSeries (Fin $(quote vars.size)) $ih)
  | .ratFunc, _, ih => `(RatFunc $ih)
  | .laurentSeries, _, ih => `(LaurentSeries $ih)

abbrev Tree := PolyesqueHead × Array ((pt : PolyesqueType) × pt.Vars)

-- right = mv
def parseMv? : TSyntax ``polyesqueMv? → Option (Name ⊕ Array Name)
  | `(polyesqueMv?| $var,) => pure (Sum.inr #[var.getId])
  | `(polyesqueMv?| $var:ident) => pure (Sum.inl var.getId)
  | `(polyesqueMv?| $vars:ident,*) => pure (Sum.inr (vars.getElems.map TSyntax.getId))
  | _ => .none

def parseBody : TSyntax ``polyesqueBody → Option ((pt : PolyesqueType) × pt.Vars)
  | `(polyesqueBody| [$vars]) =>
    match parseMv? vars with
    | .some (Sum.inl var) => return ⟨.polynomial, var⟩
    | .some (Sum.inr vars) => return ⟨.mvPolynomial, vars⟩
    | .none => .none
  | `(polyesqueBody| [[$vars]]) =>
    match parseMv? vars with
    | .some (Sum.inl var) => return ⟨.powerSeries, var⟩
    | .some (Sum.inr vars) => return ⟨.mvPowerSeries, vars⟩
    | .none => .none
  | `(polyesqueBody| ($var)) => return ⟨.ratFunc, var.getId⟩
  | `(polyesqueBody| ⸨$var⸩) => return ⟨.laurentSeries, var.getId⟩
  | _ => .none

def tree? : Polyesque → Option Tree
  | `(polyesque| $head:polyesqueHead$body:polyesqueBody*) => do
    return (head, ← body.mapM parseBody)
  | _ => .none

def raw (t : Tree) : String :=
  t.1.raw.prettyPrint.pretty' ++ .join (t.2.map fun v ↦ v.1.raw v.2).toList

def type (t : Tree) : CommandElabM Term := do
  let .some head := t.fst.term?
    | throwError "Unrecognised head"
  t.snd.foldlM (fun t b ↦ b.1.mkTerm b.2 t) head

end Syntax

section Storage

/-# Storing declared polyesque syntaxes in the environment -/

abbrev Table :=
  Std.HashMap String Term

/-- An environmental extension to store declared polyesque syntaxes. -/
abbrev TableExt := SimpleScopedEnvExtension (String × Term) Table

initialize tableExt : TableExt ← registerSimpleScopedEnvExtension <|
  { addEntry old new := old.modify new.fst fun _ ↦ new.snd
    initial := {} }

def getTerm (stx : Polyesque) : CoreM Term := do
  let .some t := tree? stx
    | throwError m!"Unrecognised syntax: {stx}"
  let .some t := (tableExt.getState (← getEnv)).get? (raw t)
    | throwError m!"Polyesque syntax not declared: {stx}"
  return t

def setTerm (stx : Polyesque) : CoreM Unit := do
  let .some t := tree? stx
    | throwError m!"Unrecognised syntax: {stx}"
  let typ ← liftCommandElabM <| type t
  trace[name_poly_vars] m!"Setting {raw t} := {typ}"
  tableExt.add (raw t, typ) .local

@[term_elab polyesque']
def getTermElab : Term.TermElab := fun stx e ↦ do
  Term.elabTermEnsuringType (← getTerm ⟨stx⟩) e

end Storage

syntax (name := namePolyVars) "name_poly_vars " polyesque : command

-- syntax (name := nameMvPolyVars) "name_poly_vars " polyVarsHead "[" ident,+ "]" : command
-- | `(command|name_poly_vars $R:polyVarsHead [$vars:ident,*]) => do

@[command_elab namePolyVars]
def namePolyVarsElab : CommandElab := fun stx ↦ do
  let `(command|name_poly_vars $stx:polyesque) := stx
    | throwError "unrecognised syntax"
  let .some tree := tree? stx
    | throwError m!"Failed to parse syntax: {stx}"
  have str := raw tree
  let typ ← type tree
  tableExt.add (str, typ) .local
  let mut terms : Array (Name × Term) := #[]
  for ⟨pt, vars⟩ in tree.snd do
    terms := (← terms.mapM (fun nt ↦ do return (nt.fst, ← pt.mkC nt.snd))) ++ (← pt.mkX vars)
  unless (terms.map Prod.fst).toList.Nodup do
    throwError m!"Duplicate variable names found: {terms.map Prod.fst}"
  for (name, term) in terms do
    elabCommand <| ← `(command|local notation $(quote s!"{name}"):str => ($term : $typ))


-- /--
-- The command `name_poly_vars` names variables in
-- `MvPolynomial (Fin n) R` for the appropriate value of `n`.
-- The notation introduced by this command is local.

-- For `Polynomial (Polynomial (...))`, use the syntax `name_poly_vars R[X][Y][Z]`.

-- Usage:

-- ```lean
-- variable (R : Type) [CommRing R]

-- name_poly_vars R[X,Y,Z]

-- #check Y -- Y : MvPolynomial (Fin 3) R
-- ```
-- -/
-- syntax (name := nameMvPolyVars) "name_poly_vars " polyVarsHead "[" ident,+ "]" : command

-- /--
-- The command `name_poly_vars` names variables in `Polynomial (Polynomial (... R))` stacked
-- appropriately many times. The notation introduced by this command is local.

-- For `MvPolynomial (Fin n) R`, use the syntax `name_poly_vars R[X,Y,Z]`.

-- Usage:

-- ```lean
-- variable (R : Type) [CommRing R]

-- name_poly_vars R[X][Y][Z]

-- #check Y -- Y : Polynomial (Polynomial (Polynomial R))
-- ```
-- -/

-- @[command_elab nameMvPolyVars, inherit_doc namePolyVars]
-- def elabNameMvVariables : CommandElab
-- | `(command|name_poly_vars $R:polyVarsHead [$vars:ident,*]) => do
--   let some R := polyVarsHeadToTerm? R | throwUnsupportedSyntax
--   let mut RStr : String := R.raw.prettyPrint.pretty'
--   if R.raw.getId = .anonymous then
--     RStr := s!"({RStr})"
--   let vars : Array String := vars.getElems.map (toString ∘ Syntax.getId)
--   have varsStr : String := ",".intercalate vars.toList
--   have typeStr : String := s!"{RStr}[{varsStr}]"
--   let size : ℕ := vars.size
--   let sizeStx : Term := quote size
--   let type : Term ← `(MvPolynomial (Fin $sizeStx) $R)
--   trace[debug] m!"{typeStr}, {type}"
--   -- e.g. `local notation3 "R[X,Y,Z] => MvPolynomial (Fin 3) R`
--   elabCommand <| ← `(command|local notation3 $(quote typeStr):str => $type)
--   for h : idx in [:size] do
--     let var := vars[idx]
--     -- e.g. `local notation3 "Y" => (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)`
--     elabCommand <| ← `(command|local notation3 $(quote var):str =>
--       (MvPolynomial.X $(quote idx) : $type))
-- | _ => throwUnsupportedSyntax

-- @[command_elab namePolyVars, inherit_doc namePolyVars]
-- def elabNamePolyVariables : CommandElab
-- | `(command|name_poly_vars $R:polyVarsHead [$vars:ident][*]) => do
--   have typeStr : String := s!"{R}[" ++ "][".intercalate (vars.getElems.map toString).toList ++ "]"
--   let some R := polyVarsHeadToTerm? R | throwUnsupportedSyntax
--   have RStr : String := R.raw.prettyPrint.pretty'
--   let vars : Array String := vars.getElems.map (toString ∘ Syntax.getId)
--   have varsStr : String := "][".intercalate vars.toList
--   have typeStr : String := s!"{RStr}[{varsStr}]"
--   -- we reverse this because the last variable is `Polynomial.X`, the second-to-last variable is
--   -- `Polynomial.C Polynomial.X`, etc.
--   let vars := vars.reverse
--   let size := vars.size
--   -- build the term `Polynomial (Polynomial (... R))`.
--   let type : Term ← size.rec (return R) fun _ S ↦ do `(Polynomial $(← S))
--   -- e.g. `local notation3 "R[X][Y][Z]" => Polynomial (Polynomial (Polynomial R))`
--   elabCommand <| ← `(command|local notation3 $(quote typeStr):str => $type)
--   -- build the term `Polynomial.C (Polynomial.C (... Polynomial.X))`.
--   let mut term : Term ← `(Polynomial.X)
--   for h : idx in [:size] do
--     let var := vars[idx]
--     elabCommand <| ← `(command|local notation3 $(quote var):str => ($term : $type))
--     term ← `(Polynomial.C $term)
-- | _ => throwUnsupportedSyntax


-- local notation3 "(Fin 37)[d,e]" => Int

-- set_option trace.debug true
-- name_poly_vars (Fin 37)[d,e]
-- end Mathlib.Tactic
