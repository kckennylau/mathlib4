/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kenny Lau
-/

import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Formal Coproducts

In this file we construct the category of formal coproducts given a category.

## Main definitions

* `FormalCoproduct`: the category of formal coproducts, which are indexed sets of objects in a
  category. A morphism `∐ i : X.I, X.obj i ⟶ ∐ j : Y.I, Y.obj j` is given by a function
  `f : X.I → Y.I` and maps `X.obj i ⟶ Y.obj (f i)` for each `i : X.I`.
* `FormalCoproduct.eval : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct C)ᵒᵖ ⥤ A)`:
  the universal property that a presheaf on `C` where the target category has arbitrary coproducts,
  can be extended to a presheaf on `FormalCoproduct C`.

-/


universe w w₁ w₂ w₃ v v₁ v₂ v₃ u u₁ u₂ u₃

open Opposite

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] (A : Type u₁) [Category.{v₁} A]

variable (C) in
/-- A formal coproduct is an indexed set of objects. -/
structure FormalCoproduct where
  I : Type w
  obj (i : I) : C

namespace FormalCoproduct

structure Hom (X Y : FormalCoproduct.{w} C) where
  f : X.I → Y.I
  φ (i : X.I) : X.obj i ⟶ Y.obj (f i)

-- this category identifies to the fullsubcategory of the category of
-- presheaves of sets on `C` which are coproducts of representable presheaves
@[simps!] instance category : Category (FormalCoproduct.{w} C) where
  Hom := Hom
  id X := { f := id, φ := fun _ ↦ 𝟙 _ }
  comp α β := { f := β.f ∘ α.f, φ := fun _ ↦ α.φ _ ≫ β.φ _ }
#check category_id_φ  -- 𝟙 should be eqToHom -- that way lean doesnt check objects def eq
@[ext (iff := false)]
lemma hom_ext {X Y : FormalCoproduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f)
    (h₂ : ∀ (i : X.I), f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i) : f = g := by
  obtain ⟨f, F⟩ := f
  obtain ⟨g, G⟩ := g
  obtain rfl : f = g := h₁
  obtain rfl : F = G := by ext i; simpa using h₂ i
  rfl

lemma hom_ext_iff {X Y : FormalCoproduct.{w} C} (f g : X ⟶ Y) :
    f = g ↔ ∃ h₁ : f.f = g.f, ∀ (i : X.I), f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i :=
  ⟨(· ▸ by simp), fun ⟨h₁, h₂⟩ ↦ hom_ext h₁ h₂⟩

lemma hom_ext_iff' {X Y : FormalCoproduct.{w} C} (f g : X ⟶ Y) :
    f = g ↔ ∀ i : X.I, ∃ h₁ : f.f i = g.f i, f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i :=
  ⟨(· ▸ by simp), fun h ↦ hom_ext (funext fun i ↦ (h i).fst) fun i ↦ (h i).snd⟩

@[simps!] def isoOfComponents {X Y : FormalCoproduct.{w} C} (e : X.I ≃ Y.I)
    (h : ∀ i, X.obj i ≅ Y.obj (e i)) : X ≅ Y where
  hom := { f := e, φ := fun i ↦ (h i).hom }
  inv := { f := e.symm, φ := fun i ↦ eqToHom (by simp) ≫ (h (e.symm i)).inv }
  hom_inv_id := by ext <;> aesop
  inv_hom_id := by ext <;> aesop

variable (C) in
@[simps!] def of : C ⥤ FormalCoproduct.{w} C where
  obj X := ⟨PUnit, fun _ ↦ X⟩
  map f := ⟨fun _ ↦ PUnit.unit, fun _ ↦ f⟩

section ofHom

variable {X : C} {Y : FormalCoproduct.{w} C}

def ofHom.mk (i : Y.I) (f : X ⟶ Y.obj i) : (of C).obj X ⟶ Y :=
  ⟨fun _ ↦ i, fun _ ↦ f⟩

def ofHom.fst (f : (of C).obj X ⟶ Y) : Y.I :=
  f.f PUnit.unit

def ofHom.snd (f : (of C).obj X ⟶ Y) :
    X ⟶ Y.obj (ofHom.fst f) :=
  f.φ PUnit.unit

lemma ofHom.mk_fst_snd (f : (of C).obj X ⟶ Y) : ofHom.mk (ofHom.fst f) (ofHom.snd f) = f := by
  ext <;> aesop

end ofHom

-- This is probably some form of adjunction.
def ofHomEquiv (X : C) (Y : FormalCoproduct.{w} C) :
    ((of C).obj X ⟶ Y) ≃ (i : Y.I) × (X ⟶ Y.obj i) where
  toFun f := ⟨ofHom.fst f, ofHom.snd f⟩
  invFun f := ofHom.mk f.1 f.2
  left_inv f := ofHom.mk_fst_snd f
  right_inv _ := rfl

def fullyFaithfulOf : (of C).FullyFaithful where
  preimage f := f.φ PUnit.unit

instance : (of C).Full :=
  fullyFaithfulOf.full

instance : (of C).Faithful :=
  fullyFaithfulOf.faithful


section Coproduct

variable (𝒜 : Type w) (f : 𝒜 → FormalCoproduct.{w} C) (t X : FormalCoproduct.{w} C)

def cofan : Cofan f :=
  Cofan.mk ⟨(i : 𝒜) × (f i).I, fun p ↦ (f p.1).obj p.2⟩
    fun i ↦ ⟨fun x ↦ ⟨i, x⟩, fun x ↦ 𝟙 ((f i).obj x)⟩

section simp_lemmas

variable {𝒜 f}

theorem cofan_inj (i : 𝒜) : (cofan 𝒜 f).inj i = ⟨fun x ↦ ⟨i, x⟩, fun x ↦ 𝟙 ((f i).obj x)⟩ := rfl
-- JH: this is probably a bad theorem? At least not good for simp

@[simp] lemma cofan_inj_f_fst (i : 𝒜) (x) : (((cofan 𝒜 f).inj i).f x).1 = i := rfl

@[simp] lemma cofan_inj_f_snd (i : 𝒜) (x) : (((cofan 𝒜 f).inj i).f x).2 = x := rfl

@[simp] lemma cofan_inj_φ (i : 𝒜) (x) : ((cofan 𝒜 f).inj i).φ x = 𝟙 ((f i).obj x) := rfl

end simp_lemmas

@[simps!] def cofanHomEquiv :
    ((cofan 𝒜 f).pt ⟶ t) ≃ ((i : 𝒜) → (f i ⟶ t)) where
  toFun m i := (cofan 𝒜 f).inj i ≫ m
  invFun s := ⟨fun p ↦ (s p.1).f p.2, fun p ↦ (s p.1).φ p.2⟩
  left_inv m := hom_ext rfl (fun ⟨i, x⟩ ↦ by simp [cofan_inj])
  right_inv p := by ext <;> simp

@[simps!] def isColimitCofan : IsColimit (cofan 𝒜 f) :=
  mkCofanColimit (cofan 𝒜 f) (fun t ↦ (cofanHomEquiv _ _ _).symm t.inj)
    (fun t i ↦ congrFun ((cofanHomEquiv _ _ _).right_inv t.inj) i)
    (fun _ _ h ↦ (Equiv.eq_symm_apply _).2 (funext h))

instance : HasCoproducts.{w} (FormalCoproduct.{w} C) :=
  hasCoproducts_of_colimit_cofans _ (isColimitCofan _)

noncomputable def coproductIsoCofan : ∐ f ≅ (cofan 𝒜 f).pt :=
  colimit.isoColimitCocone ⟨_, isColimitCofan _ _⟩

variable {𝒜 f} in
@[reassoc (attr := simp)] lemma ι_comp_coproductIsoCofan (i) :
    Sigma.ι f i ≫ (coproductIsoCofan 𝒜 f).hom = (cofan 𝒜 f).inj i :=
  colimit.isoColimitCocone_ι_hom _ _

def toFun (X : FormalCoproduct.{w} C) : X.I → FormalCoproduct.{w} C :=
  (of C).obj ∘ X.obj

def coproductCoconeIsoSelf : (cofan X.I X.toFun).pt ≅ X :=
  isoOfComponents (Equiv.sigmaPUnit X.I) fun i ↦ Iso.refl (X.obj i.fst)

@[reassoc (attr := simp)]
lemma inj_comp_coproductCoconeIsoSelf (i : X.I) :
    (cofan X.I X.toFun).inj i ≫ (coproductCoconeIsoSelf X).hom = ofHom.mk i (𝟙 (X.obj i)) :=
  hom_ext rfl (fun i => by simp; rfl)

@[simps!] noncomputable def coproductIsoSelf :
    ∐ X.toFun ≅ X :=
  coproductIsoCofan _ _ ≪≫ coproductCoconeIsoSelf X

@[reassoc (attr := simp)] lemma ι_comp_coproductIsoSelf (i : X.I) :
    Sigma.ι _ i ≫ (coproductIsoSelf X).hom = ofHom.mk i (𝟙 (X.obj i)) := by
  simp [coproductIsoSelf]

end Coproduct


noncomputable
instance [HasTerminal C] (X : FormalCoproduct.{w} C) : Unique (X ⟶ (of C).obj (⊤_ C)) :=
  ⟨⟨⟨fun _ ↦ PUnit.unit, fun _ ↦ terminal.from _⟩⟩,
  fun j ↦ hom_ext (funext fun _ ↦ rfl) (by aesop)⟩

instance [HasTerminal C] : HasTerminal (FormalCoproduct.{w} C) :=
  (IsTerminal.ofUnique <| (of C).obj (⊤_ C)).hasTerminal


noncomputable section Pullback

variable [HasPullbacks C] (T : FormalCoproduct.{w} C)
  {X Y Z : FormalCoproduct.{w} C} (f : X ⟶ Z) (g : Y ⟶ Z)

def pullback: FormalCoproduct.{w} C :=
  ⟨Function.Pullback f.f g.f, fun xy ↦
    Limits.pullback (f.φ xy.1.1 ≫ eqToHom (by rw [xy.2])) (g.φ xy.1.2)⟩

def pullbackCone : PullbackCone f g :=
  .mk (W := pullback f g)
    ⟨fun i ↦ i.1.1, fun i ↦ pullback.fst _ _⟩
    ⟨fun i ↦ i.1.2, fun i ↦ pullback.snd _ _⟩
    (hom_ext (funext fun i ↦ i.2) (by simp [pullback.condition]))

section simp_lemmas

@[simp] lemma pullbackCone_fst_f (i) : (pullbackCone f g).fst.f i = i.1.1 := rfl

@[simp] lemma pullbackCone_fst_φ (i) : (pullbackCone f g).fst.φ i = pullback.fst _ _ := rfl

@[simp] lemma pullbackCone_snd_f (i) : (pullbackCone f g).snd.f i = i.1.2 := rfl

@[simp] lemma pullbackCone_snd_φ (i) : (pullbackCone f g).snd.φ i = pullback.snd _ _ := rfl

@[simp] lemma pullbackCone_condition : (pullbackCone f g).fst ≫ f = (pullbackCone f g).snd ≫ g :=
  (pullbackCone f g).condition

end simp_lemmas

@[simps!] def homPullbackEquiv : (T ⟶ pullback f g) ≃
    { p : (T ⟶ X) × (T ⟶ Y) // p.1 ≫ f = p.2 ≫ g } :=
  { toFun m := ⟨⟨m ≫ (pullbackCone f g).fst, m ≫ (pullbackCone f g).snd⟩, by simp⟩
    invFun s := ⟨fun i ↦ ⟨(s.1.1.f i, s.1.2.f i), congrFun (congrArg Hom.f s.2) i⟩,
      fun i ↦ pullback.lift (s.1.1.φ i) (s.1.2.φ i) (by simpa using ((hom_ext_iff _ _).1 s.2).2 i)⟩
    left_inv m := hom_ext rfl (fun i ↦ by
      simp only [category_comp_f, category_comp_φ, eqToHom_refl, Category.comp_id]
      exact pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))
    right_inv s := by ext <;> simp }

def isLimitPullback : IsLimit (pullbackCone f g) := by
  refine PullbackCone.IsLimit.mk (fst := (pullbackCone f g).fst) (snd := (pullbackCone f g).snd) _
    (fun s ↦ (homPullbackEquiv s.pt f g).2 ⟨⟨s.fst, s.snd⟩, s.condition⟩)
    (fun s ↦ by ext <;> simp) (fun s ↦ by ext <;> simp)
    (fun s m h₁ h₂ ↦ ?_)
  convert ((homPullbackEquiv s.pt f g).left_inv m).symm using 3
  rw [← h₁, ← h₂]; rfl

end Pullback


noncomputable section HasCoproducts

variable [HasCoproducts.{w} A]

variable (C) in
@[simps] def eval : (C ⥤ A) ⥤ (FormalCoproduct.{w} C ⥤ A) where
  obj F :=
    { obj X := ∐ fun (i : X.I) ↦ F.obj (X.obj i)
      map {X Y} f := Sigma.desc fun i ↦ F.map (f.φ i) ≫ Sigma.ι (F.obj ∘ Y.obj) (f.f i)
      map_comp _ _ := Sigma.hom_ext _ _ (fun _ ↦ by simp [Sigma.ι_desc]) }
  map α := { app f := Sigma.map fun i ↦ α.app (f.obj i) }

def evalOf : eval C A ⋙ (whiskeringLeft _ _ A).obj (of C) ≅ Functor.id (C ⥤ A) :=
  NatIso.ofComponents fun F ↦ NatIso.ofComponents
    (fun x ↦ ⟨Sigma.desc fun _ ↦ 𝟙 _, Sigma.ι (fun _ ↦ F.obj x) PUnit.unit, by aesop, by simp⟩)
    (fun f ↦ Sigma.hom_ext _ _ (by simp [Sigma.ι_desc]))

def isColimitEvalMapCocone (𝒜 : Type w) (f : 𝒜 → FormalCoproduct.{w} C) (F : C ⥤ A) :
    IsColimit (((eval.{w} C A).obj F).mapCocone (cofan.{w} 𝒜 f)) :=
  sorry

variable {A} in
@[simps!]
def evalCoproductIso (F : C ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    ((eval C A).obj F).obj (cofan J f).pt ≅ ∐ fun j ↦ ((eval C A).obj F).obj (f j) :=
  (sigmaSigmaIso (fun j ↦ (f j).I) (fun j x ↦ F.obj ((f j).obj x))).symm

lemma comp_evalCoproductIso (F : C ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C)
    (j : J) (x : (f j).I) :
    ((eval C A).obj F).map ((ofHomEquiv ((f j).obj x) _).2 ⟨Sigma.mk j x, 𝟙 _⟩) ≫
        (evalCoproductIso F f).hom =
      Sigma.desc fun _ ↦ Sigma.ι (fun i ↦ F.obj ((f j).obj i)) x ≫
        Sigma.ι (fun b ↦ ∐ fun i ↦ F.obj ((f b).obj i)) j :=
  Sigma.hom_ext _ _ fun _ ↦ by simp [ofHomEquiv, Sigma.ι_desc]

lemma sigmaComparison_eq (F : C ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    sigmaComparison ((eval C A).obj F) f =
      (evalCoproductIso F f).inv ≫ ((eval C A).obj F).map (coproductIsoCoproduct f).inv := by
  refine Sigma.hom_ext _ _ fun j ↦ Sigma.hom_ext _ _ fun x ↦ ?_
  rw [ι_comp_sigmaComparison, ← Functor.mapIso_inv, ← Category.assoc, ← Category.assoc,
    Iso.eq_comp_inv, evalCoproductIso, Iso.symm_inv, sigmaSigmaIso_hom, Category.assoc,
    Category.assoc, Sigma.ι_desc, Sigma.ι_desc, Functor.mapIso_hom, ← Functor.map_comp,
    coproductIsoCoproduct_hom, colimit.ι_desc]
  simp [coproduct]
  rfl

variable {A} in
theorem preservesCoproductEval (F : C ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    PreservesColimit (Discrete.functor f) ((eval.{w} C A).obj F) := by
  refine CategoryTheory.Limits.PreservesCoproduct.of_iso_comparison _ _ (i := ?_)
  rw [sigmaComparison_eq, ← Functor.mapIso_inv, ← Iso.trans_inv, ← Iso.symm_hom]
  infer_instance

end HasCoproducts


section HasProducts

variable [HasProducts.{w} A]

variable (C) in
@[simps] noncomputable
def evalOp : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct.{w} C)ᵒᵖ ⥤ A) where
  obj F :=
    { obj X := ∏ᶜ fun (i : X.unop.I) ↦ F.obj (op (X.unop.obj i))
      map f := Pi.lift fun i ↦ Pi.π _ (f.unop.f i) ≫ F.map (f.unop.φ i).op }
  map α := { app f := Pi.map fun i ↦ α.app (op (f.unop.obj i)) }

variable {A} in
noncomputable def evalOpOf :
    evalOp C A ⋙ (whiskeringLeft _ _ A).obj (of C).op ≅ Functor.id (Cᵒᵖ ⥤ A) :=
  NatIso.ofComponents fun F ↦ NatIso.ofComponents fun x ↦
    ⟨Pi.π _ PUnit.unit, Pi.lift fun _ ↦ 𝟙 _, by aesop, by simp⟩

variable {A} in
@[simps!] noncomputable
def evalOpCoproductIso (F : Cᵒᵖ ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    ((evalOp C A).obj F).obj (op (coproduct J f).cocone.pt) ≅
      ∏ᶜ fun j ↦ ((evalOp C A).obj F).obj (op (f j)) :=
  (piPiIso (fun j ↦ (f j).I) (fun j x ↦ F.obj (op ((f j).obj x)))).symm

lemma evalOpCoproductIso_comp (F : Cᵒᵖ ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) (j : J) :
    (evalOpCoproductIso F f).hom ≫ Pi.π _ j =
      ((evalOp C A).obj F).map (op ((coproduct J f).cocone.ι.app ⟨j⟩)) :=
  (Pi.lift_π _ _).trans (by simp [coproduct])

lemma π_eq {J : Type w} (f : J → FormalCoproduct.{w} C) (j : J) :
    Pi.π (op ∘ f) j = (opCoproductIsoProduct _).inv ≫ op (colimit.ι _ _) :=
  (opCoproductIsoProduct_inv_comp_ι _ _).symm

lemma piComparison_eq (F : Cᵒᵖ ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    piComparison ((evalOp C A).obj F) (op ∘ f) =
      ((evalOp C A).obj F).map ((opCoproductIsoProduct _).inv ≫ (coproductIsoCoproduct _).op.inv) ≫
        (evalOpCoproductIso F f).hom := by
  refine Pi.hom_ext _ _ fun j ↦ Pi.hom_ext _ _ fun x ↦ ?_
  rw [piComparison_comp_π, evalOp_obj_map, Pi.lift_π, evalOp_obj_map, evalOpCoproductIso_hom,
    Category.assoc, Category.assoc]
  conv => enter [2,2]; rw [← Category.assoc]; enter [1]; exact Pi.lift_π _ _
  conv => enter [2,2]; exact Pi.lift_π _ _
  refine Eq.symm ((Pi.lift_π _ _).trans ?_)
  congr 1
  · congr 3; simp [π_eq]
  · congr 1; simp [π_eq]
  · congr 1
    · rw [π_eq]; rfl
    · rw [π_eq]; rfl

variable {A} in
theorem preservesProductEvalOp (F : Cᵒᵖ ⥤ A) {J : Type w} (f : J → FormalCoproduct.{w} C) :
    PreservesLimit (Discrete.functor (op ∘ f)) ((evalOp.{w} C A).obj F) := by
  refine CategoryTheory.Limits.PreservesProduct.of_iso_comparison _ _ (i := ?_)
  rw [piComparison_eq, ← Iso.trans_inv, ← Functor.mapIso_inv, ← Iso.symm_hom]
  infer_instance

end HasProducts


def arrowOfMaps (X : C) {J : Type w} (f : (j : J) → C) (φ : (j : J) → f j ⟶ X) :
    FormalCoproduct.mk _ f ⟶ (of C).obj X :=
  ⟨fun _ ↦ PUnit.unit, φ⟩


end FormalCoproduct

end Limits

end CategoryTheory
