/-
normalize to `integer` or `valuationSubring`?
-/

import RamificationGroup.Valued.Hom.ValExtension
import RamificationGroup.Valuation.Discrete
import RamificationGroup.Compat.LocalClassFieldTheory.DiscreteValuationExtension


open Valuation Valued DiscreteValuation

section non_discrete

open Polynomial

namespace Valuation

theorem isEquiv_iff_integer {K : Type*} [DivisionRing K] {Γ₀ Γ'₀ : outParam Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
  v.IsEquiv v' ↔ v.integer = v'.integer := by
  rw [isEquiv_iff_val_le_one]
  constructor <;> intro h
  · ext x; rw [mem_integer_iff, mem_integer_iff]
    exact h
  · intro x
    rw [← mem_integer_iff, ← mem_integer_iff]
    simp only [h]

variable {K L : Type*} {ΓK ΓL: outParam Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
  [vK : Valued K ΓK] {v : Valuation L ΓL}
  [Algebra K L] [FiniteDimensional K L]
-- variable [HenselianLocalRing vK.valuationSubring]

theorem eval_lt_one_of_coeff_le_one_of_const_eq_zero_of_lt_one {f : L[X]}
    (hf : ∀n : ℕ, v (f.coeff n) ≤ 1) (h0 : f.coeff 0 = 0)
    {x : L} (hx : v x < 1) :
  v (f.eval x) < 1 := by
  rw [eval_eq_sum_range]
  apply map_sum_lt v (one_ne_zero' ΓL)
  intro n _
  by_cases hn : n = 0
  · rw [hn, h0]
    simp only [pow_zero, mul_one, _root_.map_zero, zero_lt_one]
  · rw [map_mul, map_pow, ← mul_one 1]
    simpa using mul_lt_one_of_nonneg_of_lt_one_right (hf n) zero_le' ((pow_lt_one_iff hn).mpr hx)

theorem aeval_valuationSubring_lt_one_of_lt_one
    (h : vK.v.IsEquiv <| v.comap (algebraMap K L))
    (f : 𝒪[K][X]) (h0 : f.coeff 0 = 0) {x : L} (hx : v x < 1) :
  v (aeval x f) < 1 := by
  rw [aeval_def, ← eval_map]
  apply eval_lt_one_of_coeff_le_one_of_const_eq_zero_of_lt_one _ _ hx
  · intro n
    rw [coeff_map, show (algebraMap 𝒪[K] L) (f.coeff n) = (algebraMap K L) (f.coeff n) by rfl, ← comap_apply]
    apply ((isEquiv_iff_val_le_one).mp h).mp (f.coeff n).2
  · simp only [coeff_map, h0, _root_.map_zero]

theorem aeval_valuationSubring_lt_one_of_lt_one_self
  (f : 𝒪[K][X]) (h0 : f.coeff 0 = 0) {x : K} (hx : vK.v x < 1) :
    vK.v (aeval x f) < 1 := by
  rw [aeval_def, ← eval_map]
  apply eval_lt_one_of_coeff_le_one_of_const_eq_zero_of_lt_one _ _ hx
  · intro n
    rw [coeff_map, show (algebraMap 𝒪[K] K) (f.coeff n) = (algebraMap K K) (f.coeff n) by rfl, ← comap_apply]
    apply (f.coeff n).2
  · simp only [coeff_map, h0, _root_.map_zero]

theorem mem_integer_of_mem_integral_closure (h : vK.v.IsEquiv <| v.comap (algebraMap K L))
    {x : L} (hx : x ∈ integralClosure 𝒪[K] L) :
  x ∈ v.integer := by
  rcases hx with ⟨p, hp⟩
  rw [mem_integer_iff]
  by_contra! vxgt1
  have xne0 : x ≠ 0 := (Valuation.ne_zero_iff v).mp <| ne_of_gt <| lt_trans (zero_lt_one' _) vxgt1
  letI : Invertible x := invertibleOfNonzero xne0
  have : v (aeval x⁻¹ (p.reverse - 1)) < 1 := by
    apply aeval_valuationSubring_lt_one_of_lt_one h
    · simp only [coeff_sub, coeff_zero_reverse, hp.1, Monic.leadingCoeff, coeff_one_zero, sub_self]
    · apply (one_lt_val_iff v xne0).mp vxgt1
  apply ne_of_lt this
  have hrev : eval₂ (algebraMap (↥𝒪[K]) L) x⁻¹ p.reverse = 0 := by
    have hrev' : eval₂ (algebraMap (↥𝒪[K]) L) (⅟x) p.reverse = 0 :=
      (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap (↥𝒪[K]) L) x p).2 hp.2
    simpa [invOf_eq_inv x] using hrev'
  have : aeval x⁻¹ (p.reverse - 1) = -1 := by
    rw [aeval_def, Polynomial.eval₂_sub, hrev, Polynomial.eval₂_one, zero_sub]
  rw [this, map_neg, map_one]

end Valuation

end non_discrete

variable {K : Type*} [Field K] [vK : Valued K ℤₘ₀]
variable {L : Type*} [Field L]

namespace DiscreteValuation

variable [Algebra K L] [FiniteDimensional K L]

section int_closure_discrete

variable [IsDiscrete vK.v] [CompleteSpace K]
variable {vL : Valuation L ℤₘ₀}

theorem nontrivial_of_valuation_extension (h : vK.v.IsEquiv <| vL.comap (algebraMap K L)) : vL.IsNontrivial := by
  rcases exists_isUniformizer_of_isDiscrete (v := vK.v) with ⟨π, hπ⟩
  refine ⟨(algebraMap K L) (π : K), ?_, ?_⟩
  · rw [← comap_apply]
    have hvk_ne0 : vK.v (π : K) ≠ 0 :=
      (Valuation.ne_zero_iff (v := vK.v)).2 (isUniformizer_ne_zero (v := vK.v) hπ)
    exact (Valuation.IsEquiv.eq_zero h).not.mp hvk_ne0
  · rw [← comap_apply]
    exact ne_of_lt <| ((Valuation.isEquiv_iff_val_lt_one).mp h).1
      (isUniformizer_val_lt_one (v := vK.v) hπ)


instance : IsIntegralClosure (↥vL.integer) (↥𝒪[K]) L := sorry


/-- If a valuation `v : L → ℤₘ₀` extends a discrete valuation on `K`, then `v` is equivalent to `extendedValuation K L`.-/

theorem extension_valuation_equiv_extendedValuation_of_discrete
  (h : vK.v.IsEquiv <| vL.comap (algebraMap K L)) :
    vL.IsEquiv (extendedValuation K L) := by
  letI : vL.IsNontrivial := nontrivial_of_valuation_extension h
  apply isEquiv_of_val_le_one
  intro x
  constructor
  · nth_rw 2 [← mem_valuationSubring_iff]
    rw [← ValuationSubring.mem_toSubring, ← Extension.integralClosure_eq_integer, Subalgebra.mem_toSubring]
    intro hx
    refine (mem_integralClosure_iff (↥v.valuationSubring) L).mpr ?_
    simp only [valuationSubring]
    have : IsIntegral vK.v.integer x := by
      rw [IsIntegralClosure.isIntegral_iff (A := vL.integer) (R := 𝒪[K]) (B := L)]
      use ⟨x, hx⟩
      rfl
    exact this
  · rw [← mem_valuationSubring_iff, ← ValuationSubring.mem_toSubring, ← Extension.integralClosure_eq_integer]
    apply mem_integer_of_mem_integral_closure h

theorem extension_integer_eq_extendedValuation_of_discrete (h : vK.v.IsEquiv <| vL.comap (algebraMap K L)) :
  vL.integer = (extendedValuation K L).integer := by
  rw [← isEquiv_iff_integer]
  exact extension_valuation_equiv_extendedValuation_of_discrete h

theorem integral_closure_eq_integer_of_complete_discrete
    (h : vK.v.IsEquiv <| vL.comap (algebraMap K L)) :
  (integralClosure 𝒪[K] L).toSubring = vL.integer := by
  have hint :
      (integralClosure vK.v.valuationSubring L).toSubring = (extendedValuation K L).integer := by
    ext x
    have hmem :=
      congrArg (fun S : Subring L => x ∈ S) (Extension.integralClosure_eq_integer (K := K) (L := L))
    simpa [ValuationSubring.mem_toSubring, mem_valuationSubring_iff, mem_integer_iff] using hmem
  calc
    (integralClosure 𝒪[K] L).toSubring = (integralClosure vK.v.valuationSubring L).toSubring := by
      rfl
    _ = (extendedValuation K L).integer := hint
    _ = vL.integer := (extension_integer_eq_extendedValuation_of_discrete h).symm

end int_closure_discrete

section value_ext

variable [CompleteSpace K] [IsDiscrete vK.v]
variable {v₁ v₂ : Valuation L ℤₘ₀}

theorem unique_valuationSubring_of_ext (h₁ : vK.v.IsEquiv <| v₁.comap (algebraMap K L))
  (h₂ : vK.v.IsEquiv <| v₂.comap (algebraMap K L)) :
    v₁.valuationSubring = v₂.valuationSubring := by
  ext
  rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    ← Valuation.mem_integer_iff, ← Valuation.mem_integer_iff,
    ← integral_closure_eq_integer_of_complete_discrete h₁, ← integral_closure_eq_integer_of_complete_discrete h₂]

theorem unique_val_of_ext
  (h₁ : vK.v.IsEquiv <| v₁.comap (algebraMap K L))
  (h₂ : vK.v.IsEquiv <| v₂.comap (algebraMap K L)) :
    v₁.IsEquiv v₂ :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr <| unique_valuationSubring_of_ext h₁ h₂

end value_ext

end DiscreteValuation

namespace DiscreteValuation

variable [CompleteSpace K] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀]
variable [Algebra K L] [IsValExtension vK.v vL.v] [FiniteDimensional K L]

theorem algHom_preserve_val_of_complete (f : L →ₐ[K] L) : vL.v.IsEquiv <| vL.v.comap f := by
  apply unique_val_of_ext (K := K)
  · apply IsValExtension.val_isEquiv_comap
  · rw [Valuation.isEquiv_iff_val_le_one]
    simp only [comap_apply, RingHom.coe_coe, AlgHom.commutes]
    intro x
    rw [← Valuation.comap_apply (algebraMap K L)]
    revert x
    rw [← Valuation.isEquiv_iff_val_le_one]
    apply IsValExtension.val_isEquiv_comap

theorem algEquiv_preserve_val_of_complete (f : L ≃ₐ[K] L) : vL.v.IsEquiv <| vL.v.comap f := algHom_preserve_val_of_complete f.toAlgHom


end DiscreteValuation
