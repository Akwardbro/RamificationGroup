import RamificationGroup.HerbrandFunction.Bijection

namespace HerbrandFunction
open Function DiscreteValuation Valuation Valued

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

noncomputable def psi : ℚ → ℚ :=
  invFun (phi R S)

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [vK : Valued K ℤₘ₀] [DiscreteValuation.IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [DiscreteValuation.IsDiscrete vL.v] [IsValExtension vK.v vL.v] [CompleteSpace K] [Algebra.IsSeparable K L]
[Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])]

theorem psi_bij : Function.Bijective (psi K L) := by
  constructor
  have hpsi: (invFun (phi K L)).Injective :=
    (rightInverse_invFun (phi_Bijective_aux K L).2).injective
  exact hpsi
  apply invFun_surjective
  apply (phi_Bijective_aux K L).1


noncomputable def psi' (v : ℚ): ℚ :=
  1 / (phiDeriv K L (psi K L v))

theorem psi_zero_eq_zero : psi K L 0 = 0 := by
  unfold psi
  nth_rw 1 [← phi_zero_eq_zero K L]
  have : id 0 = (0 : ℚ) := by rfl
  nth_rw 2 [← this]
  have Inj : (phi K L).Injective := by apply (phi_Bijective_aux K L).1
  rw [← invFun_comp Inj]
  simp

theorem leftInverse_phi_psi : Function.LeftInverse (phi K L) (psi K L)  := by
  rintro a
  apply invFun_eq
  apply (phi_Bijective_aux K L).surjective

@[simp]
theorem phi_psi_eq_self (u : ℚ) : (phi K L) ((psi K L) u) = u := leftInverse_phi_psi K L u


@[simp]
theorem psi_phi_eq_self (u : ℚ) : (psi K L) ((phi K L) u) = u := by
  rw [← Function.comp_apply (f := psi K L) (g := phi K L)]
  unfold psi
  rw [Function.invFun_comp (f := (phi K L))]
  rfl; apply (phi_Bijective_aux K L).injective


theorem psi_eq_self_of_le_neg_one {v : ℚ} (hv : v ≤ 0) : psi K L v = v := by
  have h1 : phi K L (psi K L v) = v := by apply phi_psi_eq_self K L _
  have h2 : phi K L v = v := by apply phi_eq_self_of_le_zero K L hv
  apply (phi_Bijective_aux K L).injective
  simp [h1, h2]


variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S]

variable (S' : Type*) [Ring S'] [vS' : Valued S' ℤₘ₀] [Algebra R S']

theorem phiDeriv_eq_ofEquiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℚ) : phiDeriv R S u = phiDeriv R S' u := by
  unfold phiDeriv
  congr 2
  repeat apply Nat.card_congr (lowerRamificationGroup_equiv_of_ring_equiv hf _).toEquiv

theorem phi_eq_ofEquiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℚ) : phi R S u = phi R S' u := by
  unfold phi
  congr 2
  rw [funext_iff]
  intro i
  repeat exact phiDeriv_eq_ofEquiv _ _ _ hf _


theorem psi_eq_ofEquiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℚ) : psi R S u = psi R S' u := by
  apply congrArg₂ invFun
  apply (funext_iff.mpr (phi_eq_ofEquiv _ _ _ hf))
  rfl

-- theorem psi_phi_eq_self (u : ℚ) : (psi R S) ((phi R S) u) = u := by
--   rw [← Function.comp_apply (f := psi R S) (g := phi R S)]
--   unfold psi
--   rw [Function.invFun_comp (f := (phi R S))]
--   rfl; apply (phi_Bijective R S).injective
