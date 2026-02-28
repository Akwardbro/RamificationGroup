import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import RamificationGroup.ForMathlib.LocalRing.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import RamificationGroup.Valued.Hom.Discrete

namespace IsDiscreteValuationRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

section uniformiser

variable {ϖ x : A} (hϖ : Irreducible ϖ)
include hϖ
theorem unit_mul_irreducible_of_irreducible (hx : Irreducible x) : ∃u : A, IsUnit u ∧ x = u * ϖ := by
  obtain ⟨u, hu⟩ : ∃u : A, x = u * ϖ := by
    refine exists_eq_mul_left_of_dvd <| addVal_le_iff_dvd.mp <| le_of_eq ?_
    rw [addVal_uniformizer hx, addVal_uniformizer hϖ]
  have : IsUnit u := Or.resolve_right (Irreducible.isUnit_or_isUnit hx hu) hϖ.not_isUnit
  use u

theorem mul_irreducible_of_not_unit (h : ¬IsUnit x) : ∃y : A, x = y * ϖ := by
  obtain ⟨y, hy⟩ : ∃y : A, y * ϖ = x := by
    apply Ideal.mem_span_singleton'.mp
    rw [← (irreducible_iff_uniformizer _).mp hϖ, IsLocalRing.mem_maximalIdeal]
    assumption
  use y
  apply Eq.symm hy

theorem mul_irreducible_square_of_not_unit_of_not_irreducible (h1 : ¬Irreducible x) (h2 : ¬IsUnit x) : ∃y : A, x = y * ϖ ^ 2 := by
  obtain ⟨y, hy⟩ := mul_irreducible_of_not_unit hϖ h2
  have : ¬IsUnit y := fun h ↦
    h1 (Eq.mpr (id (congrArg (fun _a ↦ Irreducible _a) hy)) ((irreducible_isUnit_mul h).mpr hϖ))
  obtain ⟨z, hz⟩ := mul_irreducible_of_not_unit hϖ this
  use z
  rw [hy, hz]
  ring

theorem irreducible_of_irreducible_add_addVal_ge_two (hx : Irreducible x) {y : A} : Irreducible (x + y * ϖ ^ 2) := by
  rcases unit_mul_irreducible_of_irreducible hϖ hx with ⟨u, hu, hxu⟩
  rw [hxu, pow_two, ← mul_assoc, ← add_mul]
  apply (irreducible_isUnit_mul (IsLocalRing.is_unit_of_unit_add_nonunit hu _)).mpr hϖ
  simp only [mem_nonunits_iff, IsUnit.mul_iff, not_and]
  exact fun _ ↦ Irreducible.not_isUnit hϖ

theorem maximalIdeal_pow_eq_span_irreducible_pow (n : ℕ) : IsLocalRing.maximalIdeal A ^ n = Ideal.span {ϖ ^ n} := by
  rw [Irreducible.maximalIdeal_eq hϖ, Ideal.span_singleton_pow]

theorem ideal_le_iff {m n : ℕ} :
  Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ m} ↔ m ≤ n := by
  constructor
  · intro h
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton, pow_dvd_pow_iff (Irreducible.ne_zero hϖ) hϖ.not_isUnit] at h
    exact h
  · rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right

end uniformiser

end IsDiscreteValuationRing

section uniform_dvd

open DiscreteValuation Valued Valuation
variable {L : Type*} [Field L] [vL : Valued L ℤₘ₀] [DiscreteValuation.IsDiscrete vL.v]

theorem DiscreteValuationRing.uniformizer_dvd_iff_le {n1 n2 : ℕ} {π : vL.v.valuationSubring}
    (hpi : Valuation.IsUniformizer vL.v π) : π ^ n1 ∣ π ^ n2 ↔ n1 ≤ n2 := by
  constructor <;> intro h
  · have hnezero : π ≠ 0 := by
      exact_mod_cast (Valuation.IsUniformizer.ne_zero (v := vL.v) hpi)
    have hneunit : ¬ IsUnit π := by
      exact Valuation.IsUniformizer.not_isUnit (v := vL.v) hpi
    apply (pow_dvd_pow_iff hnezero hneunit).1
    obtain ⟨u1, hu1⟩ := h
    use u1
  · apply pow_dvd_pow
    exact h

theorem IsDiscreteValuationRing.irreducible_of_uniformizer' (π : vL.v.valuationSubring)
    (hpi : Valuation.IsUniformizer vL.v π) : Irreducible π := by
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 ?_
  exact Valuation.IsUniformizer.is_generator (v := vL.v) hpi

end uniform_dvd
