import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic
import RamificationGroup.ForMathlib.DiscreteValuationRing.Basic
import RamificationGroup.Valuation.SubAlgEquiv
import RamificationGroup.Valuation.PolyTaylor


open IsLocalRing Classical IntermediateField Polynomial Classical IsDiscreteValuationRing

namespace ExtDVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
variable [Module.Finite A B]


omit [Algebra.IsSeparable (ResidueField A) (ResidueField B)] in
instance : Module.Finite (ResidueField A) (ResidueField B) :=
  IsLocalRing.ResidueField.finite_of_module_finite (R := A) (S := B)

omit [Algebra.IsSeparable (ResidueField A) (ResidueField B)] in
instance : FiniteDimensional (ResidueField A) (ResidueField B) := by
  infer_instance



variable (A) (B) in
/-- There exists `x : B` generating `k_B` over `k_A` -/
theorem exists_lift_residue_primitive : ∃x : B, (ResidueField A)⟮residue B x⟯ = ⊤ := by
  sorry

variable (A) in
omit [Algebra.IsSeparable (ResidueField A) (ResidueField B)] [Module.Finite A B] in
/-- For any `x : k_B`, there eixsts `f : A[X]` that reduces to the minimal polynomial of `x` over `k_A` -/
theorem exists_lift_polynomial_of_residue (x : B) : ∃f : A[X], f.map (residue A) = minpoly (ResidueField A) (residue B x) := by
  let f0 := minpoly (ResidueField A) (residue B x)
  have : (Polynomial.map (residue A)).Surjective := map_surjective (residue A) Ideal.Quotient.mk_surjective
  use (this f0).choose
  rw [(this f0).choose_spec]

section x_and_f

open Subalgebra

-- `x` : a lift of a primitive element of `k_B/k_A`
variable {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
-- `f` : a polynomial with `A`-coeff that reduces to the minpoly of `x : k_B` over `k_A`
variable {f : A[X]} (h_red : f.map (residue A) = minpoly (ResidueField A) (residue B x))
-- `ϖ` : a uniformizer `ϖ` of `B`
variable {ϖ : B} (hϖ : Irreducible ϖ)

include hx hϖ h_red
omit [Algebra.IsSeparable (ResidueField A) (ResidueField B)] h_red hϖ in
/-- Auxiliary lemma: `A[x, ϖ] ⊔ m_B = ⊤`. Can be strenthened to `A[x] ⊔ m_B = B`-/
lemma adjoin_lift_residue_primitive_and_irreducible_sup_maximalIdeal_eq_top : toSubmodule (Algebra.adjoin A {x, ϖ}) ⊔ (IsLocalRing.maximalIdeal B).restrictScalars A = ⊤ := by
  sorry

omit [Algebra.IsSeparable (ResidueField A) (ResidueField B)] h_red in
/-- Auxiliary lemma: `A[x, ϖ] ⊔ m_B ^ i = ⊤` for any `i : ℕ`-/
lemma adjoin_lift_residue_primitive_and_irreducible_sup_maximalIdeal_pow_eq_top (i : ℕ) : toSubmodule (Algebra.adjoin A {x, ϖ}) ⊔ (IsLocalRing.maximalIdeal B ^ i).restrictScalars A = ⊤ := by
  induction' i with i hi
  · simp only [Nat.zero_eq, pow_zero, Ideal.one_eq_top, Submodule.restrictScalars_top, ge_iff_le,
    le_top, sup_of_le_right]
  · rw [eq_top_iff, ← hi]
    intro y hy
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, hc⟩ : ∃c : B, b = ϖ ^ i * c := by
      rw [maximalIdeal_pow_eq_span_irreducible_pow hϖ, Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hb
      rcases hb with ⟨c, hc⟩
      use c
      rw [← hc, mul_comm]
    have : c ∈ toSubmodule (Algebra.adjoin A {x, ϖ}) ⊔ (IsLocalRing.maximalIdeal B).restrictScalars A := by
      rw [adjoin_lift_residue_primitive_and_irreducible_sup_maximalIdeal_eq_top hx]
      apply Submodule.mem_top
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp this
    obtain ⟨w, hw⟩ : ∃w : B, v = ϖ * w := by
      rw [Irreducible.maximalIdeal_eq hϖ, Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hv
      rcases hv with ⟨c, hc⟩
      use c
      rw [← hc, mul_comm]
    rw [← hab, hc, ← huv, mul_add, ← add_assoc, hw, ← mul_assoc]
    apply Submodule.add_mem_sup
    · apply Submodule.add_mem
      · assumption
      · rw [Subalgebra.mem_toSubmodule]
        apply mul_mem
        · apply Algebra.adjoin_mono (show ({ϖ} : Set B) ⊆ {x, ϖ} by simp only [Set.subset_insert])
          apply Algebra.pow_mem_adjoin_singleton
        · assumption
    · rw [Submodule.restrictScalars_mem, maximalIdeal_pow_eq_span_irreducible_pow hϖ, Ideal.mem_span_singleton']
      use w
      rw [mul_comm, pow_succ]


omit [IsDomain B] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] [Module.Finite A B] hx h_red hϖ in
theorem maximalIdeal_map_ne_bot_of_injective (h_inj : Function.Injective (algebraMap A B)) : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
  intro h
  rw [Ideal.map_eq_bot_iff_of_injective h_inj] at h
  apply IsDiscreteValuationRing.not_a_field' (R := A) h

omit [Algebra.IsSeparable (ResidueField A) (ResidueField B)] h_red in
/--
lemma 3 states that `xⁱϖʲ`'s with finite many `i j`'s form a `A`-basis of `B`.
This is an alternative and weaker version of lemma 3,
stating that `A[x, ϖ] = B`.
-/
theorem adjoin_lift_residue_primitive_and_irreducible_eq_top (h_inj : Function.Injective (algebraMap A B)) : Algebra.adjoin A {x, ϖ} = ⊤ := by
  rw [← Algebra.toSubmodule_eq_top, eq_top_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot _ (le_of_eq (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) -- Nakayama's lemma
  · rw [Ideal.smul_top_eq_map]
    obtain ⟨n, hn⟩ : ∃n : ℕ, (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B ^ n := by
      rcases (TFAE B (not_isField B)).out 0 6 with ⟨h, _⟩
      apply h; assumption
      exact maximalIdeal_map_ne_bot_of_injective h_inj
    rw [hn, adjoin_lift_residue_primitive_and_irreducible_sup_maximalIdeal_pow_eq_top hx hϖ]
  · apply Module.finite_def.mp
    assumption

-- preparation for lemma 4
omit [Algebra.IsSeparable (ResidueField A) (ResidueField B)] [Module.Finite A B] hx h_red in
theorem residue_primitive_of_add_uniformizer (hx : (ResidueField A)⟮residue B x⟯ = ⊤) : (ResidueField A)⟮residue B (x + ϖ)⟯ = ⊤ := by
  rw [← residue_eq_add_irreducible hϖ]
  exact hx

omit [Algebra.IsSeparable (ResidueField A) (ResidueField B)] [Module.Finite A B] hx hϖ in
theorem not_unit_aeval_lift_residue_primitive : ¬IsUnit (f.eval₂ (algebraMap A B) x) := by
  rw [is_unit_iff_residue_ne_zero, ne_eq, not_not,
    hom_eval₂, algebraMap_residue_compat, ← eval₂_map,
    ← aeval_def, h_red, minpoly.aeval]

omit [Module.Finite A B] hx in
/--
This is the first part of lemma 4:
If `f x` has valuation ≥ 2, then `f (x + ϖ)` is a uniformizer.
-/
theorem irreducible_aeval_lift_redisue_primitive_add_irreducible_of_reducible_aeval_lift_residue_primitve (h_fx : ¬Irreducible (f.eval₂ (algebraMap A B) x)) : Irreducible (f.eval₂ (algebraMap A B) (x + ϖ)) := by
  obtain ⟨b, hb⟩ := taylor_order_one_apply₂ f (algebraMap A B) x ϖ
  obtain ⟨y, hy⟩ := mul_irreducible_square_of_not_unit_of_not_irreducible hϖ h_fx (not_unit_aeval_lift_residue_primitive h_red)
  rw [hb, hy, mul_comm ϖ, ← mul_comm b, add_comm, ← add_assoc, ← add_mul, add_comm]
  apply irreducible_of_irreducible_add_addVal_ge_two hϖ
  apply (irreducible_isUnit_mul _).mpr hϖ
  apply IsLocalRing.is_unit_iff_residue_ne_zero.mpr
  rw [hom_eval₂, algebraMap_residue_compat, ← eval₂_map, ← derivative_map]
  apply Separable.eval₂_derivative_ne_zero
  · rw [h_red]
    apply Algebra.IsSeparable.isSeparable
  · rw [← aeval_def, h_red, minpoly.aeval]

end x_and_f

omit [Algebra.IsSeparable (ResidueField A) (ResidueField B)] in
/--
This is the second part of lemma 4:
`B = A[x]` if `k_B = k_A[x]` and `f x` is a uniformizer.-/
theorem adjoin_lift_primitive_eq_top_of_irreducible_aeval_lift_residue_primitive (h_inj : Function.Injective (algebraMap A B)) {x : B} (hx : (ResidueField A)⟮residue B x⟯ = ⊤)
    {f : A[X]} (h_fx : Irreducible (f.eval₂ (algebraMap A B) x) )  :
    Algebra.adjoin A {x} = ⊤ := by
  apply Algebra.adjoin_eq_of_le
  · simp only [Algebra.coe_top, Set.subset_univ]
  let fx := f.eval₂ (algebraMap A B) x
  rw [← adjoin_lift_residue_primitive_and_irreducible_eq_top hx h_fx h_inj]
  rw [show ({x, fx} : Set B) = {x} ∪ {fx} by rfl, Algebra.adjoin_union]
  simp only [sup_le_iff, le_refl, true_and, ge_iff_le]
  rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  apply aeval_mem_adjoin_singleton

/-- For a finite extension of DVR `A ↪ B` with seperable residue field extension,
there exists `x : B` s.t. `B = A[x]`-/
theorem exists_primitive (h_inj : Function.Injective (algebraMap A B)) : ∃x : B, Algebra.adjoin A {x} = ⊤ := by
  rcases exists_lift_residue_primitive A B with ⟨x, hx⟩
  rcases exists_lift_polynomial_of_residue A x with ⟨f, h_red⟩
  exact if h : Irreducible (f.eval₂ (algebraMap A B) x)
    then ⟨x, (adjoin_lift_primitive_eq_top_of_irreducible_aeval_lift_residue_primitive h_inj hx h)⟩
    else ⟨x + (IsDiscreteValuationRing.exists_irreducible B).choose,
      (adjoin_lift_primitive_eq_top_of_irreducible_aeval_lift_residue_primitive h_inj (residue_primitive_of_add_uniformizer (IsDiscreteValuationRing.exists_irreducible B).choose_spec hx)
        (irreducible_aeval_lift_redisue_primitive_add_irreducible_of_reducible_aeval_lift_residue_primitve h_red (IsDiscreteValuationRing.exists_irreducible B).choose_spec h))⟩

/-- A power basis of finite extension of DVR `A ↪ B` with seperable residue field extension.-/
noncomputable def PowerBasisExtDVR (h : Function.Injective (algebraMap A B)) : PowerBasis A B :=
  by
    sorry

section ramiIdx

theorem maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx (h_inj : Function.Injective (algebraMap A B)) :
  (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B ^
    (Ideal.ramificationIdx (algebraMap A B)
      (maximalIdeal A) (maximalIdeal B)) := by
  rcases exists_lift_residue_primitive A B with ⟨x, hx⟩
  rcases exists_lift_polynomial_of_residue A x with ⟨f, h_red⟩
  rcases exists_irreducible B with ⟨πB, hπB⟩
  nth_rw 1 [Irreducible.maximalIdeal_eq hπB]
  rcases ideal_eq_span_pow_irreducible (maximalIdeal_map_ne_bot_of_injective h_inj) hπB with ⟨e, he⟩
  rw [Ideal.span_singleton_pow]
  convert he
  have : ∀k : ℕ,
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ IsLocalRing.maximalIdeal B ^ k
      → k ≤ e := by
    intro k
    rw [he, Irreducible.maximalIdeal_eq hπB, Ideal.span_singleton_pow]
    exact (ideal_le_iff hπB).mp
  rw [Ideal.ramificationIdx_eq_find ⟨e, this⟩, Nat.find_eq_iff]
  constructor
  · exact this
  · intro n hne h
    replace h := h e
    rw [he, Irreducible.maximalIdeal_eq hπB, Ideal.span_singleton_pow] at h
    simp only [le_refl, true_implies] at h
    omega


theorem ramificationIdx_ne_zero_of_injective_of_integral (h_inj : Function.Injective (algebraMap A B))
  (h_int : (algebraMap A B).IsIntegral) :
    Ideal.ramificationIdx (algebraMap A B)
      (maximalIdeal A) (maximalIdeal B) ≠ 0 := by
  intro h
  suffices (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≠ ⊤ by
    apply this
    simp only [maximalIdeal_map_eq_maximalIdeal_pow_ramificationIdx h_inj, h, pow_zero, Ideal.one_eq_top]
  intro h
  rw [Ideal.map_eq_top_iff _ h_inj h_int] at h
  apply IsLocalRing.maximalIdeal_ne_top A h

end ramiIdx

end ExtDVR
