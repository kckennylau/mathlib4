/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.OverClass
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Elliptic curves defined in terms of the Grassmannian

This file defines a "model" elliptic curve over a ring given an explicit Weierstrass cubic. Here
"model" means that an elliptic curve in general should be locally isomorphic to a model.

## Main definitions

-/

universe u v

variable (R : Type u) [CommRing R]

open Module TensorProduct CategoryTheory Limits

section WaitingPR

variable (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

-- PR #26060 https://github.com/leanprover-community/mathlib4/pull/26060
def Grassmannian : Type v :=
  { N : Submodule R M // Module.Finite R (M ⧸ N) ∧ Projective R (M ⧸ N) ∧
    ∀ p, rankAtStalk (R := R) (M ⧸ N) p = k }

namespace Grassmannian

scoped notation "G("k", "M"; "R")" => Grassmannian R M k

variable {R M k}

/-- The underlying submodule of an element of `G(M; R, k)`. This cannot be a coercion because `k`
cannot be inferred. -/
def val (N : G(k, M; R)) : Submodule R M :=
  Subtype.val N

end Grassmannian

abbrev ProjectiveSpace : Type v :=
  Grassmannian R M 1

end WaitingPR


namespace WeierstrassCurve

abbrev P2 : Type u :=
  Grassmannian R (Fin 3 → R) 1

namespace P2

variable {R}

def x {p : P2 R} : (Fin 3 → R) ⧸ p.val :=
  Submodule.Quotient.mk (Pi.single 0 1)

def y {p : P2 R} : (Fin 3 → R) ⧸ p.val :=
  Submodule.Quotient.mk (Pi.single 1 1)

def z {p : P2 R} : (Fin 3 → R) ⧸ p.val :=
  Submodule.Quotient.mk (Pi.single 2 1)

abbrev Target (p : P2 R) :=
  ((Fin 3 → R) ⧸ p.val) ⊗[R] ((Fin 3 → R) ⧸ p.val) ⊗[R] ((Fin 3 → R) ⧸ p.val)

noncomputable abbrev Target.mk {p : P2 R} (a b c : (Fin 3 → R) ⧸ p.val) : Target p :=
  a ⊗ₜ[R] b ⊗ₜ[R] c

end P2

/-- An abbreviation for a Weierstrass curve in the Grassmannian. -/
abbrev Grass : Type u :=
  WeierstrassCurve R

variable {R} in
/-- The conversion from a Weierstrass curve to Grassmannian. -/
def toGrass (W : WeierstrassCurve R) : Grass R := W

namespace Grass

open P2

variable {R} (W : Grass R)

/-- `y^2 + a₁xy + a₃y = x^3 + a₂x^2 + a₄x + a₆`, homogenised with `z`. -/
@[simp] def condition (p : P2 R) : Prop :=
  (.mk y y z + W.a₁ • .mk x y z + W.a₃ • .mk y z z : Target p) =
    (.mk x x x + W.a₂ • .mk x x z + W.a₄ • .mk x z z + W.a₆ • .mk z z z)

/-- `W` is smooth iff the discriminant is a unit. -/
def Smooth : Prop := IsUnit W.Δ

/-- The `R`-points on the elliptic curve defined by `W` are `p : P2 R` such that the homogeneous
cubic polynomial `W` evaluates to `0` at the point `p`. -/
abbrev Point : Type u :=
  { p : P2 R // W.condition p }

def zero : W.Point :=
  ⟨⟨LinearMap.ker (LinearMap.proj 1), sorry⟩, sorry⟩

instance : Zero W.Point := ⟨W.zero⟩

/-- A Weierstrass cubic produces a functor `R-Alg ⥤ Set` (to be elevated to `AddCommGrp`). -/
def functor {R : CommRingCat.{u}} (W : Grass R) (hW : W.Smooth) : Under R ⥤ Type u where
  obj A := (W.baseChange A.right).toGrass.Point
  map f p := ⟨sorry, sorry⟩

end Grass

end WeierstrassCurve

namespace AlgebraicGeometry

open WeierstrassCurve

/-- An elliptic curve over a scheme `S` is a map `f : E ⟶ S` with a section `e : S ⟶ E` such that
locally (over `S`), i.e. `S` is covered by (affine) opens `Uᵢ := Spec Aᵢ` such that, the map
`E_Uᵢ ⟶ Spec Aᵢ` (with the section) is ismorphic to the model of a smooth Weierstrass curve. -/
class IsEllipticCurve (S : Scheme.{u}) (E : Over S) (e : Over.mk (𝟙 S) ⟶ E) : Prop where
  (locally_elliptic : ∃ 𝒰 : S.AffineOpenCover, ∀ i : 𝒰.J, ∃ (W : Grass (𝒰.obj i))
    (hW : W.Smooth) (h : W.functor hW ≅ Under.post Scheme.Spec.rightOp ⋙
        (Under.opEquivOpOver _).functor ⋙ yoneda.obj ((Over.pullback (𝒰.map i)).obj E)),
      ∀ A : Under (𝒰.obj i), h.inv.app A (Over.homMk (pullback.lift ((Spec.map A.hom ≫ 𝒰.map i
        ≫ e.left)) (Spec.map A.hom) (by simp)) (by simp)) = (0 : Grass.Point _))

end AlgebraicGeometry
