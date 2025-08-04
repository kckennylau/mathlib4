/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yury Kudryashov
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.NormedSpace.OperatorNorm.Completeness
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# Weak dual of normed space

Let `E` be a normed space over a field `𝕜`. This file is concerned with properties of the weak-*
topology on the dual of `E`. By the dual, we mean either of the type synonyms
`NormedSpace.Dual 𝕜 E` or `WeakDual 𝕜 E`, depending on whether it is viewed as equipped with its
usual operator norm topology or the weak-* topology.

It is shown that the canonical mapping `NormedSpace.Dual 𝕜 E → WeakDual 𝕜 E` is continuous, and
as a consequence the weak-* topology is coarser than the topology obtained from the operator norm
(dual norm).

In this file, we also establish the Banach-Alaoglu theorem about the compactness of closed balls
in the dual of `E` (as well as sets of somewhat more general form) with respect to the weak-*
topology.

## Main definitions

The main definitions concern the canonical mapping `Dual 𝕜 E → WeakDual 𝕜 E`.

* `NormedSpace.Dual.toWeakDual` and `WeakDual.toNormedDual`: Linear equivalences from
  `dual 𝕜 E` to `WeakDual 𝕜 E` and in the converse direction.
* `NormedSpace.Dual.continuousLinearMapToWeakDual`: A continuous linear mapping from
  `Dual 𝕜 E` to `WeakDual 𝕜 E` (same as `NormedSpace.Dual.toWeakDual` but different bundled
  data).

## Main results

The first main result concerns the comparison of the operator norm topology on `dual 𝕜 E` and the
weak-* topology on (its type synonym) `WeakDual 𝕜 E`:
* `dual_norm_topology_le_weak_dual_topology`: The weak-* topology on the dual of a normed space is
  coarser (not necessarily strictly) than the operator norm topology.
* `WeakDual.isCompact_polar` (a version of the Banach-Alaoglu theorem): The polar set of a
  neighborhood of the origin in a normed space `E` over `𝕜` is compact in `WeakDual _ E`, if the
  nontrivially normed field `𝕜` is proper as a topological space.
* `WeakDual.isCompact_closedBall` (the most common special case of the Banach-Alaoglu theorem):
  Closed balls in the dual of a normed space `E` over `ℝ` or `ℂ` are compact in the weak-star
  topology.

## TODO
* Add that in finite dimensions, the weak-* topology and the dual norm topology coincide.
* Add that in infinite dimensions, the weak-* topology is strictly coarser than the dual norm
  topology.
* Add metrizability of the dual unit ball (more generally weak-star compact subsets) of
  `WeakDual 𝕜 E` under the assumption of separability of `E`.
* Add the sequential Banach-Alaoglu theorem: the dual unit ball of a separable normed space `E`
  is sequentially compact in the weak-star topology. This would follow from the metrizability above.

## Notations

No new notation is introduced.

## Implementation notes

Weak-* topology is defined generally in the file `Mathlib/Topology/Algebra/Module/WeakDual.lean.

When `E` is a normed space, the duals `Dual 𝕜 E` and `WeakDual 𝕜 E` are type synonyms with
different topology instances.

For the proof of Banach-Alaoglu theorem, the weak dual of `E` is embedded in the space of
functions `E → 𝕜` with the topology of pointwise convergence.

The polar set `polar 𝕜 s` of a subset `s` of `E` is originally defined as a subset of the dual
`Dual 𝕜 E`. We care about properties of these w.r.t. weak-* topology, and for this purpose give
the definition `WeakDual.polar 𝕜 s` for the "same" subset viewed as a subset of `WeakDual 𝕜 E`
(a type synonym of the dual but with a different topology instance).

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology
* https://en.wikipedia.org/wiki/Banach%E2%80%93Alaoglu_theorem

## Tags

weak-star, weak dual

-/


noncomputable section

open Filter Function Bornology Metric Set

open Topology Filter

/-!
### Weak star topology on duals of normed spaces

In this section, we prove properties about the weak-* topology on duals of normed spaces.
We prove in particular that the canonical mapping `Dual 𝕜 E → WeakDual 𝕜 E` is continuous,
i.e., that the weak-* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace NormedSpace

namespace Dual

/-- For normed spaces `E`, there is a canonical map `Dual 𝕜 E → WeakDual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
def toWeakDual : Dual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E :=
  LinearEquiv.refl 𝕜 (E →L[𝕜] 𝕜)

@[simp]
theorem coe_toWeakDual (x' : Dual 𝕜 E) : toWeakDual x' = x' :=
  rfl

@[simp]
theorem toWeakDual_inj (x' y' : Dual 𝕜 E) : toWeakDual x' = toWeakDual y' ↔ x' = y' :=
  (LinearEquiv.injective toWeakDual).eq_iff

@[deprecated (since := "2024-12-29")] alias toWeakDual_eq_iff := toWeakDual_inj

theorem toWeakDual_continuous : Continuous fun x' : Dual 𝕜 E => toWeakDual x' :=
  WeakBilin.continuous_of_continuous_eval _ fun z => (inclusionInDoubleDual 𝕜 E z).continuous

/-- For a normed space `E`, according to `toWeakDual_continuous` the "identity mapping"
`Dual 𝕜 E → WeakDual 𝕜 E` is continuous. This definition implements it as a continuous linear
map. -/
def continuousLinearMapToWeakDual : Dual 𝕜 E →L[𝕜] WeakDual 𝕜 E :=
  { toWeakDual with cont := toWeakDual_continuous }

/-- The weak-star topology is coarser than the dual-norm topology. -/
theorem dual_norm_topology_le_weak_dual_topology :
    (UniformSpace.toTopologicalSpace : TopologicalSpace (Dual 𝕜 E)) ≤
      (WeakDual.instTopologicalSpace : TopologicalSpace (WeakDual 𝕜 E)) := by
  convert (@toWeakDual_continuous _ _ _ _ (by assumption)).le_induced
  exact induced_id.symm

end Dual

end NormedSpace

namespace WeakDual

open NormedSpace

/-- For normed spaces `E`, there is a canonical map `WeakDual 𝕜 E → Dual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. Here it is implemented as the inverse of the linear
equivalence `NormedSpace.Dual.toWeakDual` in the other direction. -/
def toNormedDual : WeakDual 𝕜 E ≃ₗ[𝕜] Dual 𝕜 E :=
  NormedSpace.Dual.toWeakDual.symm

theorem toNormedDual_apply (x : WeakDual 𝕜 E) (y : E) : (toNormedDual x) y = x y :=
  rfl

@[simp]
theorem coe_toNormedDual (x' : WeakDual 𝕜 E) : toNormedDual x' = x' :=
  rfl

@[simp]
theorem toNormedDual_inj (x' y' : WeakDual 𝕜 E) : toNormedDual x' = toNormedDual y' ↔ x' = y' :=
  (LinearEquiv.injective toNormedDual).eq_iff

@[deprecated (since := "2024-12-29")] alias toNormedDual_eq_iff := toNormedDual_inj

theorem isClosed_closedBall (x' : Dual 𝕜 E) (r : ℝ) : IsClosed (toNormedDual ⁻¹' closedBall x' r) :=
  isClosed_induced_iff'.2 (ContinuousLinearMap.is_weak_closed_closedBall x' r)

/-!
### Polar sets in the weak dual space
-/


variable (𝕜)

/-- The polar set `polar 𝕜 s` of `s : Set E` seen as a subset of the dual of `E` with the
weak-star topology is `WeakDual.polar 𝕜 s`. -/
def polar (s : Set E) : Set (WeakDual 𝕜 E) :=
  toNormedDual ⁻¹' (NormedSpace.polar 𝕜) s

theorem polar_def (s : Set E) : polar 𝕜 s = { f : WeakDual 𝕜 E | ∀ x ∈ s, ‖f x‖ ≤ 1 } :=
  rfl

/-- The polar `polar 𝕜 s` of a set `s : E` is a closed subset when the weak star topology
is used. -/
theorem isClosed_polar (s : Set E) : IsClosed (polar 𝕜 s) := by
  simp only [polar_def, setOf_forall]
  exact isClosed_biInter fun x hx => isClosed_Iic.preimage (WeakBilin.eval_continuous _ _).norm

variable {𝕜}

/-- While the coercion `↑ : WeakDual 𝕜 E → (E → 𝕜)` is not a closed map, it sends *bounded*
closed sets to closed sets. -/
theorem isClosed_image_coe_of_bounded_of_closed {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded (Dual.toWeakDual ⁻¹' s)) (hc : IsClosed s) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' s) :=
  ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed hb (isClosed_induced_iff'.1 hc)

theorem isCompact_of_bounded_of_closed [ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded (Dual.toWeakDual ⁻¹' s)) (hc : IsClosed s) : IsCompact s :=
  DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.mpr <|
    ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image hb <|
      isClosed_image_coe_of_bounded_of_closed hb hc

variable (𝕜)

/-- The image under `↑ : WeakDual 𝕜 E → (E → 𝕜)` of a polar `WeakDual.polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
theorem isClosed_image_polar_of_mem_nhds {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' polar 𝕜 s) :=
  isClosed_image_coe_of_bounded_of_closed (isBounded_polar_of_mem_nhds_zero 𝕜 s_nhds)
    (isClosed_polar _ _)

/-- The image under `↑ : NormedSpace.Dual 𝕜 E → (E → 𝕜)` of a polar `polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
theorem _root_.NormedSpace.Dual.isClosed_image_polar_of_mem_nhds {s : Set E}
    (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsClosed (((↑) : Dual 𝕜 E → E → 𝕜) '' NormedSpace.polar 𝕜 s) :=
  WeakDual.isClosed_image_polar_of_mem_nhds 𝕜 s_nhds

/-- The **Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in a
normed space `E` is a compact subset of `WeakDual 𝕜 E`. -/
theorem isCompact_polar [ProperSpace 𝕜] {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsCompact (polar 𝕜 s) :=
  isCompact_of_bounded_of_closed (isBounded_polar_of_mem_nhds_zero 𝕜 s_nhds) (isClosed_polar _ _)

/-- The **Banach-Alaoglu theorem**: closed balls of the dual of a normed space `E` are compact in
the weak-star topology. -/
theorem isCompact_closedBall [ProperSpace 𝕜] (x' : Dual 𝕜 E) (r : ℝ) :
    IsCompact (toNormedDual ⁻¹' closedBall x' r) :=
  isCompact_of_bounded_of_closed isBounded_closedBall (isClosed_closedBall x' r)

end WeakDual
