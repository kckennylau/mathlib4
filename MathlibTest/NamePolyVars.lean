import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Ring.NamePolyVars

variable (R : Type) [CommRing R]

-- name_poly_vars R[X,Y,Z][t][[a,b,c]][[d]](u)⸨v⸩[p,][[q,]]
-- set_option quotPrecheck false
-- name_poly_vars R[x]
-- #check x

elab "asdf" : term => do
  have bar : Lean.Ident := Lean.mkIdent `foo
  Lean.Elab.Term.elabTermEnsuringType (← `($bar)) .none
axiom foo : Type
#check asdf
