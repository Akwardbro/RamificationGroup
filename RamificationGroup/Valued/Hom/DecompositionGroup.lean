import RamificationGroup.Valued.Hom.Discrete

open DiscreteValuation Valuation Valued

section DecompositionGroup

variable (R S : Type*) {ΓS : outParam Type*} [CommRing R] [Ring S]
[LinearOrderedCommGroupWithZero ΓS] [vS : Valued S ΓS] [Algebra R S]

variable {S} in
theorem Valuation.IsEquiv_comap_symm {s : S ≃+* S} (h : vS.v.IsEquiv (vS.v.comap s)) : vS.v.IsEquiv (vS.v.comap s.symm) := by
  intro x y
  convert (h (s.symm x) (s.symm y)).symm using 2 <;>
  simp

namespace Valued

variable {s : S ≃ₐ[R] S}
#check vS.v.IsEquiv <| vS.v.comap s

def decompositionGroup : Subgroup (S ≃ₐ[R] S) where
  carrier := {s | vS.v.IsEquiv <| vS.v.comap s}
  mul_mem' {s} {s'} hs hs' x y := by
    calc
      _ ↔ (vS.v.comap s' x) ≤ (vS.v.comap s') y := hs' x y
      _ ↔ _ := hs _ _
  one_mem' := by
    apply Valuation.IsEquiv.refl
  inv_mem' {_} {h} := by
    apply Valuation.IsEquiv_comap_symm
    exact h

/-- This stupid theorem should be parametrized over `Subgroup (S ≃ₐ[R] S)`. -/
theorem decompositionGroup_one : (1 : decompositionGroup R S).1 = .refl := by
  simp only [OneMemClass.coe_one, AlgEquiv.aut_one]

/-- This stupid theorem should be parametrized over `Subgroup (S ≃ₐ[R] S)`. -/
theorem refl_mem_decompositionGroup : .refl ∈ decompositionGroup R S := by
  rw [← decompositionGroup_one R S]
  exact (1 : decompositionGroup R S).2

section eq_top

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Algebra K L] [FiniteDimensional K L]

@[simp]
theorem decompositionGroup_eq_top [IsValExtension vK.v vL.v] [CompleteSpace K] : decompositionGroup K L = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro f
  change vL.v.IsEquiv (vL.v.comap f)
  apply algEquiv_preserve_val_of_complete

end eq_top

end Valued

end DecompositionGroup
