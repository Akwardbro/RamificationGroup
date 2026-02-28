import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic

namespace IsLocalRing

variable (A B : Type*) [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [Algebra A B] [is_local : IsLocalHom (algebraMap A B)]

noncomputable def ramificationIdx : ℕ := Ideal.ramificationIdx (algebraMap A B) (maximalIdeal A) (maximalIdeal B)

noncomputable def inertiaDeg : ℕ := Ideal.inertiaDeg (maximalIdeal A) (maximalIdeal B)

-- instance : Algebra (ResidueField A) (ResidueField B) :=
--   Ideal.Quotient.algebraQuotientOfLEComap <| le_of_eq (((local_hom_TFAE <| algebraMap A B).out 0 4 rfl rfl).mp is_local).symm

variable {A B}

theorem algebraMap_residue_compat :
    (residue B).comp (algebraMap A B) =
      (algebraMap (ResidueField A) (ResidueField B)).comp (residue A) :=
  (IsLocalRing.ResidueField.map_comp_residue (algebraMap A B)).symm

theorem residue_irreducible_eq_zero {ϖ : A} (h : Irreducible ϖ) : residue A ϖ = 0 := by
  exact (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal _).2
    (mem_nonunits_iff.2 h.not_isUnit))

theorem is_unit_iff_residue_ne_zero {x : A} : IsUnit x ↔ residue A x ≠ 0 := by
  exact (IsLocalRing.residue_ne_zero_iff_isUnit x).symm

theorem residue_eq_add_irreducible {x ϖ : A} (h : Irreducible ϖ) : residue A x = residue A (x + ϖ) := by
  simpa [RingHom.map_add, residue_irreducible_eq_zero h]

theorem is_unit_of_unit_add_nonunit {x y : A} (hx : IsUnit x) (hy : y ∈ nonunits A) : IsUnit (x + y) := by
  rw [eq_add_neg_iff_add_eq.mpr (show x + y = x + y by rfl)] at hx
  exact (isUnit_or_isUnit_of_isUnit_add hx).resolve_right fun h ↦ hy ((IsUnit.neg_iff y).mp h)

theorem maximalIdeal_eq_jacobson_of_bot : maximalIdeal A ≤ Ideal.jacobson ⊥ := le_of_eq (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm

variable (A) in
theorem maximalIdeal_ne_top : maximalIdeal A ≠ ⊤ :=
  Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal A)
