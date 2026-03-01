import RamificationGroup.UpperNumbering.phiReal
import RamificationGroup.ForMathlib.Analysis.Basic

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction
open MeasureTheory.MeasureSpace
open Pointwise
open AlgEquiv AlgHom
open ExtDVR
open Asymptotics Filter intervalIntegral MeasureTheory Function

variable (K K' L : Type*) {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK : Valued K ℤₘ₀] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension vK.v vK'.v] [IsValExtension vK'.v vL.v] [IsValExtension vK.v vL.v] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L] [CompleteSpace K] [CompleteSpace K'] [Algebra.IsSeparable K L
] [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])]

local notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup_aux K L v

theorem phiReal_comp_of_isValExtension_neg_aux [Normal K' L] {u : ℝ} (hu : u < 0) : ((phiReal K K') ∘ (phiReal K' L)) u = phiReal K L u := by
  rw [Function.comp_apply, phiReal_eq_self_of_le_zero K L (le_of_lt hu), phiReal_eq_self_of_le_zero K' L (le_of_lt hu), phiReal_eq_self_of_le_zero K K' (le_of_lt hu)]

noncomputable def phiDerivReal' (u : ℝ) : ℝ := (Nat.card G(L/K)_[(⌊u⌋ + 1)] : ℝ) / (Nat.card G(L/K)_[0])

theorem phiDerivReal'_antitone : Antitone (phiDerivReal' K L) := by
  intro x y hxy
  unfold phiDerivReal'
  have hcard : Nat.card G(L/K)_[(⌊y⌋ + 1)] ≤ Nat.card G(L/K)_[(⌊x⌋ + 1)] := by
    apply Nat.card_mono
    · exact Set.toFinite (G(L/K)_[(⌊x⌋ + 1)] : Set (L ≃ₐ[K] L))
    · apply lowerRamificationGroup.antitone
      linarith [Int.floor_le_floor hxy]
  have hcard' : (Nat.card G(L/K)_[(⌊y⌋ + 1)] : ℝ) ≤ (Nat.card G(L/K)_[(⌊x⌋ + 1)] : ℝ) := by
    exact Nat.cast_le.2 hcard
  simpa [div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right hcard' (show 0 ≤ ((Nat.card G(L/K)_[0] : ℝ)⁻¹) by positivity))


theorem phiDerivReal'_eq_phiDerivReal_mul_of {u : ℝ} (h : u = ⌈u⌉) (h' : 0 < u) : phiDerivReal' K L u = phiDerivReal K L u * ((Nat.card G(L/K)_[(⌈u⌉ + 1)] : ℝ) / (Nat.card G(L/K)_[⌈u⌉] : ℝ)) := by
  rw [phiDerivReal', phiDerivReal, max_eq_right, ← mul_div_mul_comm, mul_comm, mul_div_mul_comm, div_self, mul_one, h, Int.floor_intCast, Int.ceil_intCast]
  apply ne_of_gt
  simp only [Nat.cast_pos, Nat.card_pos]
  apply Int.ceil_nonneg (le_of_lt h')

theorem phiDerivReal'_eq_phiDerivReal_add_one_of {u : ℝ} (h : u = ⌈u⌉) (h' : 0 < u) : phiDerivReal' K L u = phiDerivReal K L (u + 1) := by
  rw [phiDerivReal', phiDerivReal, max_eq_right, h, Int.floor_intCast, Int.ceil_add_one, Int.ceil_intCast]
  apply Int.ceil_nonneg
  apply le_of_lt (lt_trans h' (by linarith))

theorem phiDerivReal'_eq_phiDerivReal_of {u : ℝ} (h : u ≠ ⌈u⌉) (h' : 0 < u) : phiDerivReal' K L u = phiDerivReal K L u := by
  unfold phiDerivReal' phiDerivReal
  rw [max_eq_right (le_of_lt (Int.ceil_pos.2 h'))]
  have h1 : ⌈u⌉ = ⌊u⌋ + 1 := by
    symm
    apply le_antisymm _ (Int.ceil_le_floor_add_one u)
    apply Int.add_one_le_of_lt
    apply lt_of_le_of_ne (Int.floor_le_ceil u)
    by_contra hc
    apply h
    apply le_antisymm
    exact Int.le_ceil u
    rw [← hc]
    exact Int.floor_le u
  rw [h1]


#check RamificationGroup_card_comp_aux
#check RamificationGroup_card_zero_comp_aux

variable [IsScalarTower 𝒪[K] 𝒪[K'] 𝒪[L]] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])] [Algebra.IsSeparable K K'] [Algebra.IsSeparable K L] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]]

theorem phiDerivReal'_comp_zero : (phiDerivReal' K' L 0) * (phiDerivReal' K K' (phiReal K' L 0)) = phiDerivReal' K L 0 := by
  unfold phiDerivReal'
  simp only [phiReal_zero_eq_zero, Int.floor_zero, zero_add, ← mul_div_mul_comm]
  congr
  rw [← (Int.ceil_one : (⌈(1 : ℝ)⌉ : ℤ) = 1), ← RamificationGroup_card_comp_aux K K' L (x := (1 : ℝ)) (by positivity), mul_comm, mul_eq_mul_right_iff]
  left
  have hp : ⌈phiReal K' L 1⌉ = 1 := by
    apply Int.ceil_eq_iff.2
    simp only [Int.cast_one, sub_self]
    constructor
    · rw [← phiReal_zero_eq_zero K' L]
      apply phiReal_StrictMono K' L (by linarith)
    · apply phiReal_one_le_one K' L
  rw [Nat.cast_inj, Nat.card_congr, herbrand_Real K K' L 1 (by linarith), hp]
  simp only [Int.ceil_one]
  exact Equiv.setCongr rfl
  rw [mul_comm, RamificationGroup_card_zero_comp_aux K K' L]

theorem phiDerivReal'_comp {u : ℝ} (h : 0 < u) : (phiDerivReal' K' L u) * phiDerivReal' K K' (phiReal K' L u) = phiDerivReal' K L u := by
  have h' : ∃ v : ℝ, ⌈v⌉ = ⌊u⌋ + 1 ∧ ⌈phiReal K' L v⌉ = ⌊phiReal K' L u⌋ + 1 := by
    have h'' : ∃ v : ℝ, v ∈ Set.Ioc u (⌊u⌋ + 1) ∧ v ∈ Set.Ioc u (u + ⌊phiReal K' L u⌋ + 1 - phiReal K' L u) := by
      simp only [← Set.mem_inter_iff, ← Set.nonempty_def, Set.Ioc_inter_Ioc, le_refl, sup_of_le_left, Set.nonempty_Ioc, lt_inf_iff, Int.lt_floor_add_one, true_and, add_assoc, add_sub_assoc, lt_add_iff_pos_right]
      rw [add_sub_assoc', sub_pos]
      exact Int.lt_floor_add_one (phiReal K' L u)
    obtain ⟨v, hv1, hv2⟩ := h''
    use v
    constructor
    · apply Int.ceil_eq_iff.2
      constructor
      · simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right]
        apply lt_of_le_of_lt (Int.floor_le u) (Set.mem_Ioc.1 hv1).1
      · apply_mod_cast (Set.mem_Ioc.1 hv1).2
    · apply Int.ceil_eq_iff.2
      constructor
      · simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right]
        apply lt_of_le_of_lt (Int.floor_le (phiReal K' L u))
        apply phiReal_StrictMono K' L (Set.mem_Ioc.1 hv1).1
      · rw [← add_le_add_iff_right (-phiReal K' L u), ← sub_eq_add_neg]
        calc
            _ ≤ (v - u) * phiDerivReal K' L u := by
              apply phiReal_sub_phiReal_le K' L (le_of_lt (Set.mem_Ioc.1 hv1).1) h
            _ ≤ v - u := by
              calc
                (v - u) * phiDerivReal K' L u ≤ (v - u) * 1 := by
                  apply mul_le_mul_of_nonneg_left (phiDerivReal_le_one K' L h)
                  linarith [le_of_lt (Set.mem_Ioc.1 hv1).1]
                _ = v - u := by ring
            _ ≤ _ := by
              rw [← sub_eq_add_neg, tsub_le_iff_left]
              convert (Set.mem_Ioc.1 hv2).2 using 1
              simp only [Int.cast_add, Int.cast_one, add_assoc, add_sub_assoc]
  obtain ⟨v, hv1, hv2⟩ := h'
  have hv : 0 ≤ v := by
    have hv_pos : 0 < v := by
      apply (Int.ceil_pos).1
      rw [hv1]
      have hu_floor : 0 ≤ ⌊u⌋ := Int.floor_nonneg.mpr (le_of_lt h)
      linarith
    exact le_of_lt hv_pos
  obtain hcm := phiDerivReal_comp K K' L hv
  unfold phiDerivReal at hcm
  rw [max_eq_right, max_eq_right] at hcm
  unfold phiDerivReal'
  rw [← hv1, ← hv2, hcm]
  · rw [hv2]
    have h' : 0 ≤ ⌊phiReal K' L u⌋ := by
      apply Int.floor_nonneg.2 (le_of_lt (phiReal_pos_of_pos K' L h))
    exact Int.le_add_one h'
  · rw [hv1]
    have h' : 0 ≤ ⌊u⌋ := Int.floor_nonneg.2 (le_of_lt h)
    exact Int.le_add_one h'

#check Int.ceil_eq_add_one_sub_fract
#check Int.fract
theorem phiReal_eq_sum_card' {u : ℝ} (hu : 0 < u) : phiReal K L u = (1 / Nat.card G(L/K)_[0]) * ((∑ x ∈ Finset.Icc 1 ⌊u⌋, Nat.card G(L/K)_[x]) + (u - (max 0 ⌊u⌋)) * (Nat.card G(L/K)_[(⌊u⌋ + 1)])) := by
  rw [phiReal_eq_sum_card K L (le_of_lt hu), mul_eq_mul_left_iff]
  left
  by_cases hc : ⌈u⌉ - 1 = ⌊u⌋
  · simp only [hc, Int.cast_max, Int.cast_zero, add_comm ⌊u⌋, ← (eq_add_of_sub_eq' hc)]
  · have h2 : ⌊u⌋ = u := by
      by_contra hcon
      apply hc
      rw [← Int.cast_inj (α := ℝ), Int.cast_sub, Int.ceil_eq_add_one_sub_fract, Int.fract]
      ring
      unfold Int.fract
      exact sub_ne_zero_of_ne fun a ↦ hcon (id (Eq.symm a))
    have h1 : ⌈u⌉ = u := by rw [← h2, Int.ceil_intCast]
    have h3 : ⌈u⌉ = ⌊u⌋ := by rw [← Int.cast_inj (α := ℝ), h1, h2]
    have h' : Finset.Icc 1 ⌊u⌋ = Finset.Icc 1 (⌊u⌋ - 1) ∪ {⌊u⌋} := by
      ext x
      constructor
      <;>intro hx
      · apply Finset.mem_union.2
        by_cases hx' : x ≤ ⌊u⌋ - 1
        · left
          apply Finset.mem_Icc.2
          refine ⟨(Finset.mem_Icc.1 hx).1, hx'⟩
        · right
          simp only [Finset.mem_singleton]
          apply eq_of_le_of_not_lt (Finset.mem_Icc.1 hx).2
          push_neg at *
          rw [← sub_add_cancel ⌊u⌋ 1]
          apply (Int.add_one_le_iff (a := ⌊u⌋ - 1) (b := x)).2 hx'
      · rw [Finset.mem_union] at hx
        match hx with
        | Or.inl hx =>
                      apply Finset.mem_Icc.2
                      refine ⟨(Finset.mem_Icc.1 hx).1, le_trans (Finset.mem_Icc.1 hx).2 (by linarith)⟩
        | Or.inr hx =>
                      rw [Finset.mem_singleton] at hx
                      rw [hx]
                      apply Finset.right_mem_Icc.2
                      rw [← h3]
                      apply (Int.add_one_le_iff (a := 0) (b := ⌈u⌉)).2 (Int.ceil_pos.2 hu)
    rw [h3, ← sub_eq_zero, ← sub_sub, add_sub_right_comm, max_eq_right, max_eq_right, add_sub_assoc, Int.cast_sub, h2, Nat.cast_sum, Int.cast_one, sub_sub_cancel, one_mul, sub_self, zero_mul, sub_zero, sub_add_comm, sub_add, sub_eq_zero, h', Finset.sum_union, Nat.cast_add, Nat.cast_sum, add_sub_cancel_left, Finset.sum_singleton]
    simp only [Finset.disjoint_singleton_right, Finset.mem_Icc, le_sub_self_iff, Int.reduceLE, and_false, not_false_eq_true]
    exact Int.floor_nonneg.2 (le_of_lt hu)
    rw [← h3]
    apply Int.le_sub_one_iff.2 (Int.ceil_pos.2 hu)

theorem phiReal_sub_phiReal_le' {u v : ℝ} (h : u ≤ v) (h': 0 < u) : phiReal K L v - phiReal K L u ≤ (v - u) * phiDerivReal' K L u := by
  by_cases hc : u ≠ ⌈u⌉
  · rw [phiDerivReal'_eq_phiDerivReal_of K L hc h']
    apply phiReal_sub_phiReal_le K L h h'
  · push_neg at hc
    have h1 : Finset.Icc 1 ⌊v⌋ = Finset.Icc 1 ⌊u⌋ ∪ Finset.Icc (⌊u⌋ + 1) ⌊v⌋ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      constructor
      <;> intro hx
      · by_cases hc' : x ≤ ⌊u⌋
        · left
          refine ⟨hx.1, hc'⟩
        · right
          constructor
          · push_neg at hc'
            apply Int.le_of_sub_one_lt
            rw [add_sub_cancel_right]
            exact hc'
          · exact hx.2
      · match hx with
        | Or.inl hx => refine ⟨hx.1, le_trans hx.2 (Int.floor_le_floor h)⟩
        | Or.inr hx =>
            refine ⟨le_trans ?_ hx.1, hx.2⟩
            simp only [le_add_iff_nonneg_left]
            apply Int.floor_nonneg.2 (le_of_lt h')
    rw [phiReal_eq_sum_card' K L h', phiReal_eq_sum_card', phiDerivReal', ← mul_sub, one_div, inv_mul_eq_div, ← mul_div_assoc, div_le_div_iff_of_pos_right, ← sub_sub, add_sub_right_comm, add_sub_assoc, h1, Finset.sum_union, Nat.cast_add, add_sub_cancel_left, max_eq_right, max_eq_right]
    calc
      _ ≤ ∑ x ∈ Finset.Icc (⌊u⌋ + 1) ⌊v⌋, Nat.card G(L/K)_[(⌊u⌋ + 1)] + ((v - ↑⌊v⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊v⌋ + 1)] ) - (u - ↑⌊u⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊u⌋ + 1)])) := by
        simp only [add_le_add_iff_right, Nat.cast_le]
        apply Finset.sum_le_sum
        intro i hi
        apply Nat.card_mono
        · exact Set.toFinite (G(L/K)_[(⌊u⌋ + 1)] : Set (L ≃ₐ[K] L))
        · apply lowerRamificationGroup.antitone K L (Finset.mem_Icc.1 hi).1
      _ ≤  ∑ x ∈ Finset.Icc (⌊u⌋ + 1) ⌊v⌋, Nat.card G(L/K)_[(⌊u⌋ + 1)] + ((v - ↑⌊v⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊u⌋ + 1)] ) - (u - ↑⌊u⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊u⌋ + 1)])) := by
        simp only [add_le_add_iff_left, sub_eq_add_neg (b := (u - ↑⌊u⌋) * ↑(Nat.card ↥ G(L/K)_[(⌊u⌋ + 1)])), add_le_add_iff_right]
        by_cases hfloorv : ⌊v⌋ = v
        · simp only [hfloorv, sub_self, zero_mul, le_rfl]
        · have hcard : (Nat.card G(L/K)_[(⌊v⌋ + 1)] : ℝ) ≤ (Nat.card G(L/K)_[(⌊u⌋ + 1)] : ℝ) := by
            exact Nat.cast_le.2 <| by
              apply Nat.card_mono
              · exact Set.toFinite (G(L/K)_[(⌊u⌋ + 1)] : Set (L ≃ₐ[K] L))
              · apply lowerRamificationGroup.antitone K L
                linarith [Int.floor_le_floor h]
          exact mul_le_mul_of_nonneg_left hcard (sub_nonneg.2 (Int.floor_le v))
      _ ≤ _ := by
        simp only [Finset.sum_const, Int.card_Icc, sub_add_cancel, smul_eq_mul, Nat.cast_mul]
        rw [← Int.cast_natCast, Int.toNat_of_nonneg, ← sub_mul, ← add_mul, Int.cast_sub]
        have haux : (↑(⌊v⌋ + 1) - ↑(⌊u⌋ + 1) + (v - ↑⌊v⌋ - (u - ↑⌊u⌋))) = v - u := by
          simp only [Int.cast_add, Int.cast_one]
          ring
        by_cases huv : u = v
        · simp only [huv, Int.cast_add, Int.cast_one, sub_self, Int.self_sub_floor, add_zero, zero_mul, le_rfl]
        · rw [haux]
        exact sub_nonneg.mpr (by linarith [Int.floor_le_floor h])
    exact Int.floor_nonneg.2 (le_of_lt h')
    exact Int.floor_nonneg.2 (le_of_lt (lt_of_lt_of_le h' h))
    have hIcc : Finset.Icc 1 ⌊u⌋ = Finset.Ico 1 (⌊u⌋ + 1) := rfl
    have hIcc' : Finset.Icc (⌊u⌋ + 1) ⌊v⌋ = Finset.Ico (⌊u⌋ + 1) (⌊v⌋ + 1) := rfl
    rw [hIcc, hIcc']
    apply Finset.Ico_disjoint_Ico_consecutive
    simp only [Nat.cast_pos, Nat.card_pos]
    apply lt_of_lt_of_le h' h


theorem le_phiReal_sub_phiReal' {u v : ℝ} (h : u ≤ v) (h' : 0 < u) : (v - u) * phiDerivReal' K L v ≤ phiReal K L v - phiReal K L u := by
  by_cases hc : v ≠ ⌈v⌉
  · rw [phiDerivReal'_eq_phiDerivReal_of K L hc]
    apply le_phiReal_sub_phiReal K L h h'
    apply lt_of_lt_of_le h' h
  · push_neg at hc
    rw [phiDerivReal'_eq_phiDerivReal_mul_of K L hc]
    calc
      _ ≤  (v - u) * (phiDerivReal K L v) := by
        by_cases huv : u < v
        · calc
            (v - u) * (phiDerivReal K L v * ((Nat.card G(L/K)_[(⌈v⌉ + 1)] : ℝ) / (Nat.card G(L/K)_[⌈v⌉] : ℝ)))
                ≤ (v - u) * (phiDerivReal K L v * 1) := by
                  apply mul_le_mul_of_nonneg_left
                  · apply mul_le_mul_of_nonneg_left
                    · exact (div_le_one (show 0 < (Nat.card G(L/K)_[⌈v⌉] : ℝ) by
                        simp only [Nat.cast_pos, Nat.card_pos])).2 <| by
                        exact Nat.cast_le.2 <| by
                          apply Nat.card_mono
                          · exact Set.toFinite (G(L/K)_[⌈v⌉] : Set (L ≃ₐ[K] L))
                          · apply lowerRamificationGroup.antitone
                            linarith
                    · exact le_of_lt (phiDerivReal_pos K L)
                  · linarith [le_of_lt huv]
            _ = (v - u) * phiDerivReal K L v := by ring
        · have heq : u = v := eq_of_le_of_not_lt h huv
          simp only [heq, sub_self, zero_mul, le_refl]
      _ ≤ _ := by
        apply le_phiReal_sub_phiReal K L h h'
    apply lt_of_lt_of_le h' h

variable {f g : Filter ℝ}

set_option maxHeartbeats 0

theorem phiReal_linear_section {n : ℕ} {x : ℝ} (h : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ)) : phiReal K L x = phiReal K L n + (1 / Nat.card G(L/K)_[0] : ℝ) * (Nat.card G(L/K)_[(n + 1)]) * (x - n) := by
  by_cases hc : x = n
  · simp only [hc, sub_self, one_div, mul_zero, add_zero]
  · have hc' : ⌈x⌉ = n + 1 := by
      apply Int.ceil_eq_iff.2
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_cancel_right]
      refine ⟨lt_of_le_of_ne (Set.mem_Icc.1 h).1 ?_, (Set.mem_Icc.1 h).2⟩
      exact fun a ↦ hc (id (Eq.symm a))
    have hx : 0 < x := by
      apply lt_of_le_of_lt (b := (n : ℝ))
      exact Nat.cast_nonneg' n
      apply lt_of_le_of_ne (Set.mem_Icc.1 h).1
      exact fun a ↦ hc (id (Eq.symm a))
    by_cases hc'' : n = 0
    · rw [phiReal_eq_sum_card K L (le_of_lt hx)]
      simp only [hc', hc'', one_div, CharP.cast_eq_zero, zero_add, sub_self, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, max_self, Int.cast_zero, sub_zero, phiReal_zero_eq_zero, zero_add]
      ring
    · rw [phiReal_eq_sum_card K L (le_of_lt hx), hc', phiReal_eq_sum_card', Int.floor_natCast]
      simp only [one_div, add_sub_cancel_right, Nat.cast_sum, Nat.cast_nonneg, max_eq_right, Int.cast_natCast, sub_self, zero_mul, add_zero, mul_add]
      congr 1
      ring
      apply lt_of_le_of_ne (Nat.cast_nonneg' n)
      symm
      simp only [ne_eq, Nat.cast_eq_zero, hc'', not_false_eq_true]

theorem phiReal_HasDerivWithinAt {u : ℝ} (h : 0 ≤ u) : HasDerivWithinAt (phiReal K L) (phiDerivReal' K L u) (Set.Ici u) u := by
  have hu : ⌊u⌋.toNat = ⌊u⌋ := by
    apply Int.toNat_of_nonneg
    apply Int.floor_nonneg.2 h
  apply hasDerivWithinAt_Ioi_iff_Ici.1
  apply (HasDerivWithinAt.Ioi_iff_Ioo (y := (⌊u⌋ : ℝ) + 1) _).1
  apply HasDerivWithinAt.congr (f := fun x => phiReal K L ⌊u⌋ + (1 / Nat.card G(L/K)_[0] : ℝ) * (Nat.card G(L/K)_[(⌊u⌋ + 1)]) * (x - ⌊u⌋))
  apply HasDerivWithinAt.congr_deriv (f' := 0 + (Nat.card G(L/K)_[(⌊u⌋ + 1)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ))
  apply HasDerivWithinAt.add
  apply hasDerivWithinAt_const
  apply HasDerivWithinAt.congr_deriv (f' := (1 / Nat.card G(L/K)_[0] : ℝ) * (Nat.card G(L/K)_[(⌊u⌋ + 1)]) * 1)
  apply HasDerivWithinAt.const_mul
  apply HasDerivWithinAt.sub_const
  apply hasDerivWithinAt_id
  simp only [one_div, mul_one, ← div_eq_inv_mul]
  unfold phiDerivReal'
  rw [zero_add]
  intro x hx
  rw [phiReal_linear_section K L (n := ⌊u⌋.toNat) (x := x), ← Int.cast_natCast, hu]
  rw [← Int.cast_natCast, hu, Set.mem_Icc]
  refine ⟨le_of_lt (lt_of_le_of_lt (Int.floor_le u) (Set.mem_Ioo.1 hx).1), le_of_lt (Set.mem_Ioo.1 hx).2⟩
  rw [phiReal_linear_section K L (n := ⌊u⌋.toNat) (x := u), ← Int.cast_natCast, hu]
  rw [← Int.cast_natCast, hu, Set.mem_Icc]
  refine ⟨Int.floor_le u, le_of_lt (Int.lt_floor_add_one u)⟩
  exact Int.lt_floor_add_one u


#check phiDerivReal'_comp
theorem phiReal_comp_HasDerivWithinAt {u : ℝ} (h : 0 ≤ u) : HasDerivWithinAt (phiReal K K' ∘ phiReal K' L) (phiDerivReal' K L u) (Set.Ici u) u := by
  apply HasDerivWithinAt.congr_deriv (f' := phiDerivReal' K' L u * phiDerivReal' K K' (phiReal K' L u))
  apply HasDerivWithinAt.scomp (t' := Set.Ici (phiReal K' L u))
  apply phiReal_HasDerivWithinAt
  rw [← phiReal_zero_eq_zero K' L]
  apply (phiReal_StrictMono K' L).monotone h
  apply phiReal_HasDerivWithinAt K' L h
  apply Monotone.mapsTo_Ici (phiReal_StrictMono K' L).monotone
  by_cases hu : 0 < u
  · rw [← phiDerivReal'_comp K K' L hu]
  · have hu' : u = 0 := Eq.symm (eq_of_le_of_not_lt h hu)
    rw [hu', phiDerivReal'_comp_zero K K' L]

theorem phiReal_continuousOn_section {n : ℕ} : ContinuousOn (phiReal K L) (Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
  let g : ℝ → ℝ := fun x => phiReal K L n + (1 / Nat.card G(L/K)_[0] : ℝ) * (Nat.card G(L/K)_[(n + 1)]) * (x - n)
  apply ContinuousOn.congr (f := g)
  apply ContinuousOn.add (continuousOn_const)
  apply ContinuousOn.mul (continuousOn_const)
  apply ContinuousOn.add (continuousOn_id' (Set.Icc (n : ℝ) (n + 1 : ℝ))) (continuousOn_const)
  intro x hx
  apply phiReal_linear_section K L hx

theorem phiReal_left_continuous {x : ℝ} : ContinuousWithinAt (phiReal K L) (Set.Iic x) x := by
  by_cases hc : x ≤ 0
  · apply ContinuousWithinAt.congr (f := fun t => t) (continuousWithinAt_id)
    intro y hy
    rw [phiReal_eq_self_of_le_zero]
    apply le_trans (Set.mem_Iic.1 hy) hc
    rw [phiReal_eq_self_of_le_zero K L hc]
  · push_neg at hc
    have hx : (⌈x⌉ - 1).toNat = ⌈x⌉ - 1 := by
      apply Int.toNat_of_nonneg
      apply Int.le_of_sub_one_lt
      simp only [zero_sub, Int.reduceNeg, neg_lt_sub_iff_lt_add, lt_add_iff_pos_right, Int.ceil_pos]
      exact hc
    apply (continuousWithinAt_Icc_iff_Iic (a := (⌈x⌉ - 1 : ℝ)) _).1
    apply ContinuousWithinAt.congr (f := fun t => (phiReal K L (⌈x⌉ - 1)) + ((1 / (Nat.card G(L/K)_[0] : ℝ)) * (Nat.card G(L/K)_[(⌈x⌉)] : ℝ)) * (t - (⌈x⌉ - 1)))
    apply ContinuousWithinAt.add (continuousWithinAt_const)
    apply ContinuousWithinAt.mul (continuousWithinAt_const)
    apply ContinuousWithinAt.sub (continuousWithinAt_id) (continuousWithinAt_const)
    intro y hy
    rw [phiReal_linear_section K L (n := (⌈x⌉ - 1).toNat) (x := y), ← Int.cast_natCast, hx, sub_add_cancel, Int.cast_sub, Int.cast_one]
    rw [← Int.cast_natCast, hx, Int.cast_sub, Int.cast_one, sub_add_cancel,  Set.mem_Icc]
    refine ⟨(Set.mem_Icc.1 hy).1, le_trans (Set.mem_Icc.1 hy).2 (Int.le_ceil x)⟩
    rw [phiReal_linear_section K L (n := (⌈x⌉ - 1).toNat), ← Int.cast_natCast, hx, Int.cast_sub, Int.cast_one, one_div, sub_add_cancel]
    rw [← Int.cast_natCast, hx, Int.cast_sub, Int.cast_one, sub_add_cancel, Set.mem_Icc]
    refine ⟨by linarith [Int.ceil_lt_add_one x], Int.le_ceil x⟩
    linarith [Int.ceil_lt_add_one x]

theorem phiReal_right_continuous {x : ℝ} : ContinuousWithinAt (phiReal K L) (Set.Ici x) x := by
  apply (continuousWithinAt_Icc_iff_Ici (b := (⌊x⌋ + 1 : ℝ)) _).1
  by_cases hc : x < 0
  ·
    apply ContinuousWithinAt.congr (f := fun t => t) (continuousWithinAt_id)
    intro y hy
    apply phiReal_eq_self_of_le_zero
    apply le_trans (Set.mem_Icc.1 hy).2
    rw [← Int.cast_one (R := ℝ), ← Int.cast_add, ← Int.cast_zero (R := ℝ), Int.cast_le]
    apply Int.le_of_sub_one_lt
    rw [add_sub_cancel_right]
    apply_mod_cast lt_of_le_of_lt (Int.floor_le x) hc
    apply phiReal_eq_self_of_le_zero K L (le_of_lt hc)
  · push_neg at hc
    have hx : ⌊x⌋.toNat = ⌊x⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.2 hc)
    apply ContinuousWithinAt.congr (f := fun t => (phiReal K L ⌊x⌋) + ((1 / (Nat.card G(L/K)_[0] : ℝ)) * (Nat.card G(L/K)_[(⌊x⌋ + 1)] : ℝ)) * (t - ⌊x⌋))
    apply ContinuousWithinAt.add (continuousWithinAt_const)
    apply ContinuousWithinAt.mul (continuousWithinAt_const)
    apply ContinuousWithinAt.sub (continuousWithinAt_id) (continuousWithinAt_const)
    intro y hy
    rw [phiReal_linear_section K L (n := ⌊x⌋.toNat), ← Int.cast_natCast, hx]
    rw [← Int.cast_natCast, hx, Set.mem_Icc]
    refine ⟨le_trans (Int.floor_le x) (Set.mem_Icc.1 hy).1, (Set.mem_Icc.1 hy).2⟩
    rw [phiReal_linear_section K L (n := ⌊x⌋.toNat), ← Int.cast_natCast, hx]
    rw [← Int.cast_natCast, hx, Set.mem_Icc]
    refine ⟨Int.floor_le x, le_of_lt (Int.lt_floor_add_one x)⟩
  exact Int.lt_floor_add_one x

theorem phiReal_Continuous : Continuous (phiReal K L) := by
  apply continuous_iff_continuousAt.2
  intro x
  apply continuousAt_iff_continuous_left_right.2
  constructor
  · exact phiReal_left_continuous K L
  · exact phiReal_right_continuous K L

theorem phiReal_comp_continuousOn_section {n : ℕ} : ContinuousOn (phiReal K K' ∘ phiReal K' L) (Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
  show ContinuousOn (fun x => phiReal K K' (phiReal K' L x)) (Set.Icc (n : ℝ) (n + 1 : ℝ))
  apply Continuous.comp_continuousOn'
  apply phiReal_Continuous
  apply phiReal_continuousOn_section


theorem phiReal_comp_of_isVal_Extension_pos_aux {n : ℕ} : ∀ u ∈ Set.Icc (n : ℝ) (n + 1 : ℝ), ((phiReal K K') ∘ (phiReal K' L)) u = phiReal K L u := by
  induction' n with n hn
  · intro u hu
    apply eq_of_has_deriv_right_eq (a := (0 : ℝ)) (b := (1 : ℝ)) (f' := phiDerivReal' K L)
    · intro x hx
      apply phiReal_comp_HasDerivWithinAt K K' L (Set.mem_Ico.1 hx).1
    · intro x hx
      apply phiReal_HasDerivWithinAt K L (Set.mem_Ico.1 hx).1
    · convert phiReal_comp_continuousOn_section K K' L (n := 0)
      simp only [CharP.cast_eq_zero]
      simp only [CharP.cast_eq_zero, zero_add]
    · convert phiReal_continuousOn_section K L (n := 0)
      simp only [CharP.cast_eq_zero]
      simp only [CharP.cast_eq_zero, zero_add]
    · rw [Function.comp_apply, phiReal_zero_eq_zero, phiReal_zero_eq_zero, phiReal_zero_eq_zero]
    · simp only [CharP.cast_eq_zero, zero_add] at hu
      exact hu
  · intro u hu
    apply eq_of_has_deriv_right_eq (a := (n + 1 : ℝ)) (b := (n + 2 : ℝ)) (f' := phiDerivReal' K L)
    · intro x hx
      apply phiReal_comp_HasDerivWithinAt K K' L (le_trans _ (Set.mem_Ico.1 hx).1)
      apply le_trans (Nat.cast_nonneg' n) (by linarith)
    · intro x hx
      apply phiReal_HasDerivWithinAt K L (le_trans _ (Set.mem_Ico.1 hx).1)
      apply le_trans (Nat.cast_nonneg' n) (by linarith)
    · convert phiReal_comp_continuousOn_section K K' L (n := n + 1) using 1
      simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
    · convert phiReal_continuousOn_section K L (n := n + 1) using 1
      simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
    · apply hn (n + 1 : ℝ)
      simp only [Set.mem_Icc, le_add_iff_nonneg_right, zero_le_one, le_refl, and_self]
    · simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] at hu
      exact hu

theorem phiReal_comp_of_isValExtension (u : ℝ) : (phiReal K K') ((phiReal K' L) u) = (phiReal K L) u := by
  by_cases hu : u ≤ 0
  · rw [phiReal_eq_self_of_le_zero K L hu, phiReal_eq_self_of_le_zero K' L hu, phiReal_eq_self_of_le_zero K K' hu]
  · rw [← Function.comp_apply (f := phiReal K K') (g := phiReal K' L), phiReal_comp_of_isVal_Extension_pos_aux K K' L u (n := ⌊u⌋.toNat)]
    apply Set.mem_Icc.2
    push_neg at hu
    constructor
    · rw [← Int.cast_natCast, Int.toNat_of_nonneg]
      exact Int.floor_le u
      apply Int.le_floor.mpr
      simp only [Int.cast_zero]
      exact le_of_lt hu
    · rw [← Int.cast_natCast, Int.toNat_of_nonneg]
      apply le_of_lt
      apply Int.lt_floor_add_one
      apply Int.le_floor.mpr
      simp only [Int.cast_zero]
      exact le_of_lt hu

@[simp]
theorem phi_comp_of_isValExtension' (u : ℚ) : (phi K K') ((phi K' L) u) = (phi K L) u := by
  by_cases hu : 0 ≤ u
  · simp only [← Rat.cast_inj (α := ℝ)]
    rw [← phiReal_eq_phi K L hu, ← phiReal_eq_phi K K', ← phiReal_eq_phi K' L hu]
    apply phiReal_comp_of_isVal_Extension_pos_aux K K' L (n := ⌊u⌋.toNat)
    simp only [Set.mem_Icc, Rat.natCast_le_cast]
    have hu':= Int.floor_nonneg.2 hu
    constructor <;> rw [← Int.cast_natCast, Int.toNat_of_nonneg hu']
    · exact Int.floor_le u
    · rw [← Rat.cast_one, ← Rat.cast_intCast, ← Rat.cast_add]
      apply Rat.cast_mono
      apply le_trans (Int.le_ceil u)
      rw [← Int.cast_one, ← Int.cast_add]
      apply Int.cast_mono
      apply Int.ceil_le_floor_add_one u
    apply phi_nonneg K' L hu
  · push_neg at hu
    let hu' := le_of_lt hu
    rw [phi_eq_self_of_le_zero K' L hu', phi_eq_self_of_le_zero K K' hu', phi_eq_self_of_le_zero K L hu']


@[simp]
theorem phi_comp_of_isValExtension : (phi K K') ∘ (phi K' L) = phi K L := by
  ext u
  apply phi_comp_of_isValExtension'

instance : Finite (L ≃ₐ[K'] L) := Finite.algEquiv

@[simp]
theorem psi_comp_of_isValExtension : (psi K' L) ∘ (psi K K') = psi K L := by
  ext v
  apply (phi_Bijective_aux K L).injective
  have hcomp := congrArg (fun f => f ((psi K' L) ((psi K K') v))) (phi_comp_of_isValExtension K K' L)
  simpa [Function.comp_apply] using hcomp.symm

@[simp]
theorem psi_comp_of_isValExtension' (v : ℚ) : (psi K' L) ((psi K K') v) = psi K L v := by
  rw [← psi_comp_of_isValExtension (K := K) (K' := K') (L := L)]
  simp


@[simp]
theorem herbrand' (v : ℚ) : G(L/K)^[v].map (AlgEquiv.restrictNormalHom K') = G(K'/K)^[v] := by
  calc
    _ = G(L/K)_[⌈psi K L v⌉].map (AlgEquiv.restrictNormalHom K') := rfl
    _ = G(K'/K)_[⌈phi K' L (psi K L v)⌉] := herbrand _
    _ = G(K'/K)^[v] := by
      rw [← psi_comp_of_isValExtension (K := K) (K' := K') (L := L)]
      simp only [Function.comp_apply, phi_psi_eq_self K' L (psi K K' v)]
      rfl

#check AlgEquiv
