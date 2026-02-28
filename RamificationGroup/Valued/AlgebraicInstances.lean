import RamificationGroup.Valued.Hom.ValExtension'
import RamificationGroup.Valuation.Extension
import RamificationGroup.Valued.Hom.Discrete
import RamificationGroup.ForMathlib.Algebra.Algebra.Basic


open DiscreteValuation Valuation Valued ExtDVR IsValExtension Polynomial

-- `IsDiscrete vK.v` may be weakened to `IsNontrivial vK.v`.
variable (K L : Type*) [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀]  [Algebra K L] [IsValExtension vK.v vL.v] [FiniteDimensional K L]

section algebra_instances

/-- 1. The conditions might be too strong.
2. The proof is almost the SAME with `Valuation.mem_integer_of_mem_integral_closure`. -/
instance : IsIntegrallyClosed 𝒪[K] := by
  rw [isIntegrallyClosed_iff K]
  intro x ⟨p, hp⟩
  by_cases xne0 : x = 0
  · subst xne0; use 0; simp only [_root_.map_zero]
  by_cases vxgt1 : v x ≤ 1
  · use ⟨x, vxgt1⟩; rfl
  · exfalso
    push_neg at vxgt1
    letI : Invertible x := invertibleOfNonzero xne0
    have : v (aeval x⁻¹ (p.reverse - 1)) < 1 := by
      apply aeval_valuationSubring_lt_one_of_lt_one_self
      · simp only [coeff_sub, coeff_zero_reverse, hp.1, Monic.leadingCoeff, coeff_one_zero, sub_self]
      · apply (one_lt_val_iff v xne0).mp vxgt1
    apply ne_of_lt this
    have : aeval x⁻¹ (p.reverse - 1) = -1 := by
      have hrev' : eval₂ (algebraMap (↥𝒪[K]) K) (⅟x) p.reverse = 0 := by
        rw [Polynomial.eval₂_reverse_eq_zero_iff]
        simpa [Polynomial.aeval_def] using hp.2
      have hrev : eval₂ (algebraMap (↥𝒪[K]) K) x⁻¹ p.reverse = 0 := by
        simpa [invOf_eq_inv x] using hrev'
      calc
        aeval x⁻¹ (p.reverse - 1)
            = eval₂ (algebraMap (↥𝒪[K]) K) x⁻¹ p.reverse - 1 := by
              simp [Polynomial.aeval_def]
        _ = -1 := by simp [hrev]
    rw [this, Valuation.map_neg, Valuation.map_one]

variable [IsDiscrete vK.v]
attribute [local instance 1001] Algebra.toSMul

instance : IsScalarTower 𝒪[K] 𝒪[L] L := inferInstanceAs (IsScalarTower vK.v.integer vL.v.integer L)


instance [CompleteSpace K] : Algebra.IsIntegral 𝒪[K] 𝒪[L] where
  isIntegral := by
    intro ⟨x, hx⟩
    rw [show x ∈ 𝒪[L] ↔ x ∈ vL.v.valuationSubring by rfl,
      (Valuation.isEquiv_iff_valuationSubring _ _).mp
        (extension_valuation_equiv_extendedValuation_of_discrete (IsValExtension.val_isEquiv_comap (R := K) (A := L))),
      ← ValuationSubring.mem_toSubring, ← Extension.integralClosure_eq_integer, Subalgebra.mem_toSubring] at hx
    rcases hx with ⟨p, hp⟩
    refine ⟨p, hp.1, ?_⟩
    ext
    rw [show (0 : 𝒪[L]).val = 0 by rfl, ← hp.2]
    calc
      _ = 𝒪[L].subtype (eval₂ (algebraMap 𝒪[K] 𝒪[L]) ⟨x, hx⟩ p) := rfl
      _ = _ := by
        rw [Polynomial.hom_eval₂]
        -- simp only [ValuationSubring.algebraMap_def]
        congr

set_option synthInstance.maxHeartbeats 0
instance [CompleteSpace K] : IsIntegralClosure 𝒪[L] 𝒪[K] L := IsIntegralClosure.of_isIntegrallyClosed 𝒪[L] 𝒪[K] L

instance : IsDiscreteValuationRing 𝒪[K] :=
  inferInstanceAs (IsDiscreteValuationRing vK.v.valuationSubring)

theorem aux6 [CompleteSpace K] : IsDiscreteValuationRing 𝒪[L] :=
  by
    letI : IsNontrivial vL.v := nontrivial_of_valExtension K L
    simpa using (inferInstance : IsDiscreteValuationRing vL.v.valuationSubring)

/-- Can't be inferred automatically. -/
instance [CompleteSpace K] [Algebra.IsSeparable K L] : IsNoetherian 𝒪[K] 𝒪[L] :=
  IsIntegralClosure.isNoetherian 𝒪[K] K L 𝒪[L]

-- Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])
-- Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])

set_option maxHeartbeats 0
noncomputable def PowerBasisValExtension [CompleteSpace K] [Algebra.IsSeparable K L] [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])] : PowerBasis 𝒪[K] 𝒪[L] :=
  letI : IsNontrivial vL.v := nontrivial_of_valExtension K L
  letI : IsDiscreteValuationRing 𝒪[L] := aux6 K L
  PowerBasisExtDVR (Valuation.HasExtension.algebraMap_injective (vK := vK.v) (vA := vL.v))

example [CompleteSpace K] [Algebra.IsSeparable K L] :
  Algebra.FiniteType 𝒪[K] 𝒪[L] := inferInstance

end algebra_instances

section ramification

section general

variable (K L : Type*) {ΓK ΓL : outParam Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    [Algebra K L] [vK : Valued K ΓK] [vL : Valued L ΓL] [IsValExtension vK.v vL.v]

/-- Should be renamed -/
noncomputable def LocalField.ramificationIdx : ℕ :=
  IsLocalRing.ramificationIdx 𝒪[K] 𝒪[L]

end general

section discrete

variable (K L : Type*) {ΓK ΓL : outParam Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    [vK : Valued K ℤₘ₀] [IsDiscrete vK.v]
    [vL : Valued L ℤₘ₀] [IsValExtension vK.v vL.v]

open LocalField ExtDVR

-- theorem integerAlgebra_integral_of_integral
variable [Algebra.IsSeparable K L]

instance [CompleteSpace K] : Module.Finite ↥𝒪[K] ↥𝒪[L] := IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]

#check exists_isUniformizer_of_isDiscrete
set_option synthInstance.maxHeartbeats 0
theorem ramificationIdx_ne_zero [CompleteSpace K] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])]: ramificationIdx K L ≠ 0 := by
  letI : IsDiscreteValuationRing 𝒪[L] := aux6 K L
  apply ramificationIdx_ne_zero_of_injective_of_integral
  exact Valuation.HasExtension.algebraMap_injective (vK := vK.v) (vA := vL.v)
  rw [← Algebra.isIntegral_iff_isIntegral]
  infer_instance

theorem aux0 [CompleteSpace K] [IsDiscrete vL.v] : vL.v = extendedValuation K L := by
  rw [← isEquiv_iff_eq]
  apply extension_valuation_equiv_extendedValuation_of_discrete val_isEquiv_comap


end discrete

#check Ideal.ramificationIdx

end ramification
