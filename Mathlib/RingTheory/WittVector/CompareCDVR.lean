/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Teichmuller
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-! # Witt vectors over residue field of complete discrete valuation ring

Let `R` be a complete discrete valuation ring with perfect residue field `k`. Then there is a
canonical map `W(k) →+* R`. We call this map `WittVector.compare`.
-/

open Ring Perfection

namespace WittVector

local notation:max "𝓂["R"]" => IsLocalRing.maximalIdeal R
local notation:max "𝓀["R"]" => IsLocalRing.ResidueField R

variable (R : Type*) (p : ℕ) [Fact p.Prime]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete 𝓂[R] R]
  [CharP 𝓀[R] p] --[PerfectRing 𝓀[R] p]

def compare' (ϖ : R) (hϖ : Irreducible ϖ) : WittVector p (Perfection 𝓀[R] p) →+* R where
  toFun x := _

end WittVector

#min_imports
