import RamificationGroup.LowerNumbering.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.Cast.Basic
import RamificationGroup.ForMathlib.Unknow

open DiscreteValuation Subgroup Set Function Finset BigOperators Int Valued

namespace HerbrandFunction

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [Algebra R S] [Finite (S ≃ₐ[R] S)]

theorem Ramification_Group_card_pos {u : ℚ} : 0 < Nat.card G(S/R)_[⌈u⌉] := Nat.card_pos

-- by definition of relindex, it's always 1 when u < 0
noncomputable def phiDeriv (u : ℚ) : ℚ :=
  (Nat.card G(S/R)_[(max 0 ⌈u⌉)] : ℚ) / (Nat.card G(S/R)_[0] : ℚ)

noncomputable def phi (u : ℚ) : ℚ :=
  ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (phiDeriv R S x) + (u - (max 0 (⌈u⌉ - 1))) * (phiDeriv R S u)

omit [Finite (S ≃ₐ[R] S)] in
theorem phi_zero_eq_zero : phi R S 0 = 0 := by
  unfold phi
  simp

theorem phiDeriv_eq_one_of_le_zero {u : ℚ} (hu : u ≤ 0) : phiDeriv R S u = 1 := by
  unfold phiDeriv
  have hu' : ⌈u⌉ ≤ 0 := by exact ceil_nonpos hu
  simp only [hu', max_eq_left]
  apply div_self
  --card of ramigroup ne one
  apply ne_of_gt
  simp only [Nat.cast_pos]
  apply Ramification_Group_card_pos R S (u := 0)

theorem phi_eq_self_of_le_zero {u : ℚ} (hu : u ≤ 0) : phi R S u = u := by
  unfold phi
  simp [phiDeriv_eq_one_of_le_zero R S hu]
  have h : ⌈u⌉ - 1 ≤ 0 := by linarith [ceil_nonpos hu]
  have h' : ⌈u⌉ - 1 < 1 := by linarith [h]
  calc
    _ = (u - max 0 (⌈u⌉ - 1)) := by simp [h']
    _ = u := by simp [h]

theorem phiDeriv_pos (u : ℚ) : 0 < phiDeriv R S u := by
  unfold phiDeriv
  apply div_pos
  <;> simp only [Nat.cast_pos]
  have : max 0 ⌈u⌉ = ⌈max 0 (⌈u⌉ : ℚ)⌉ := by
    symm
    apply Int.ceil_eq_iff.2
    constructor
    · apply lt_of_lt_of_le (b := ↑(max 0 ⌈u⌉))
      linarith
      simp only [cast_max, cast_zero, le_refl]
    · simp only [cast_max, cast_zero, le_refl]
  rw [this]
  apply Ramification_Group_card_pos R S (u := max 0 ⌈u⌉)
  apply Ramification_Group_card_pos R S (u := 0)

omit [Finite (S ≃ₐ[R] S)] in
theorem phiDeriv_eq_ceil {u : ℚ} : phiDeriv R S u = phiDeriv R S ⌈u⌉ := by
  unfold phiDeriv
  simp

theorem phi_pos_of_pos {u : ℚ} (hu : 0 < u) : 0 < phi R S u := by
  unfold phi
  have h : 0 ≤ ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), phiDeriv R S x := by
    by_cases h : ⌈u⌉ - 1 = 0
    · simp [h]
    · apply le_of_lt
      apply sum_pos (s := Finset.Icc 1 (⌈u⌉ - 1))
      · intro i _
        apply phiDeriv_pos
      · simp
        apply Int.le_of_sub_one_lt
        simp [one_le_ceil_iff.2]
        apply lt_of_le_of_ne
        apply one_le_ceil_iff.2 hu
        omega
  have h' : 0 < (u - (max 0 (⌈u⌉ - 1))) * phiDeriv R S u := by
    apply mul_pos
    simp [hu]
    linarith [ceil_lt_add_one u]
    exact phiDeriv_pos R S u
  linarith [h, h']

theorem phi_nonneg {u : ℚ} (hu : 0 ≤ u) : 0 ≤ phi R S u := by
  by_cases hu' : u = 0
  · rw [hu', phi_zero_eq_zero]
  · apply le_of_lt (phi_pos_of_pos R S (lt_of_le_of_ne hu _))
    exact fun a ↦ hu' (id (Eq.symm a))

theorem phi_pos_gt_nonpos {a b : ℚ} (hu1 : a ≤ 0) (hu2 : 0 < b) : phi R S a < phi R S b := by
  apply lt_of_le_of_lt (b := 0)
  rw [phi_eq_self_of_le_zero]
  <;> exact hu1
  exact phi_pos_of_pos R S hu2

omit [Finite (S ≃ₐ[R] S)] in
theorem phi_of_pos_of_le_one {u : ℚ} (h1 : 0 < u) (h2 : u ≤ 1) : phi R S u = u * phiDeriv R S u := by
  unfold phi
  have huc : ⌈u⌉ = 1 := by
    apply ceil_eq_iff.2
    simp [h1, h2]
  have huf1 : ⌈u⌉ - 1 < 1 := by linarith [huc]
  have huf0 : ⌈u⌉ - 1 = 0 := by simp [huc]
  simp [huf1, huf0]

omit [Finite (S ≃ₐ[R] S)] in
theorem Finset.sum_Icc_sub_sum_Icc {n : ℤ} {m : ℤ} (hn : 1 ≤ n) (hnm : n ≤ m) : ∑ x ∈ Finset.Icc 1 m, phiDeriv R S x - ∑ x ∈ Finset.Icc 1 n, phiDeriv R S x = ∑ x ∈ Finset.Icc (n + 1) m, phiDeriv R S x := by
  have hd : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) m) := by
    refine Disjoint.symm ((fun {α} {s t} ↦ Finset.disjoint_left.mpr) ?_)
    intro a ha
    rw [Finset.mem_Icc] at *
    apply not_and_or.2
    right
    linarith [ha.1]
  have hu : Finset.Icc 1 m = Finset.Icc 1 n ∪ Finset.Icc (n + 1) m := by
    ext x
    rw [Finset.mem_union]
    repeat rw [Finset.mem_Icc]
    constructor <;> intro h
    · by_cases hc : x ≤ n
      · left
        exact ⟨h.1, hc⟩
      · right
        exact ⟨by linarith [hc], h.2⟩
    · constructor
      · match h with
        | Or.inl h => exact h.left
        | Or.inr h => linarith [hn, h.right]
      · match h with
        | Or.inl h => linarith [h.left]
        | Or.inr h => exact h.right
  rw [sub_eq_iff_eq_add', hu]
  apply Finset.sum_union hd

theorem phi_strictMono_of_gt_one {a b : ℚ} (ha : 0 < a) (hb : 1 < b) (hab : a < b) : phi R S a < phi R S b := by
  unfold phi
  by_cases hceil : ⌈a⌉ = ⌈b⌉
  · simp only [hceil, phiDeriv_eq_ceil, ceil_intCast, cast_max, cast_zero, cast_sub, cast_one,
    add_lt_add_iff_left]
    refine mul_lt_mul_of_pos_right ?_ (phiDeriv_pos R S _)
    simpa only [sub_lt_sub_iff_right] using hab
  · calc
      _ ≤ ∑ x ∈ Finset.Icc 1 ⌈a⌉, phiDeriv R S x := by
        apply le_trans (b := ∑ x ∈ Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S ↑x + 1 * phiDeriv R S ⌈a⌉)
        rw [phiDeriv_eq_ceil R S]
        have hmul : (a - ↑(max 0 (⌈a⌉ - 1))) * phiDeriv R S ↑⌈a⌉ ≤ 1 * phiDeriv R S ↑⌈a⌉ := by
          refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (phiDeriv_pos R S _))
          have : a - 1 ≤ (max 0 (⌈a⌉ - 1)) := by
            simp only [cast_max, cast_zero, cast_sub, cast_one, le_max_iff, tsub_le_iff_right,
              zero_add, sub_add_cancel]
            right; apply le_ceil
          linarith [this]
        have hsum := add_le_add_left hmul (∑ x ∈ Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S ↑x)
        simpa [add_comm, add_left_comm, add_assoc] using hsum
        have h : ∑ x ∈ Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S x + 1 * phiDeriv R S ⌈a⌉ = ∑ x ∈ Finset.Icc 1 ⌈a⌉, phiDeriv R S x := by
            have h' : ∑ x ∈ Finset.Icc 1 ⌈a⌉, phiDeriv R S x - 1 * phiDeriv R S ⌈a⌉ = ∑ x ∈ Finset.Icc 1 (⌈a⌉ - 1), phiDeriv R S x := by
              by_cases hc : 1 ≤ a
              · rw [one_mul]
                apply sum_insert_right_aux 1 ⌈a⌉ ?_ (phiDeriv R S); exact one_le_ceil_iff.mpr ha
              · have h : ⌈a⌉ = 1 := by
                  refine ceil_eq_on_Ioc 1 a ?_
                  simp only [cast_one, sub_self, Set.mem_Ioc, ha, true_and]
                  apply le_of_lt; push_neg at hc; exact hc
                rw [h]; simp only [Finset.Icc_self, sum_singleton, cast_one, one_mul, sub_self, zero_lt_one, Finset.Icc_eq_empty_of_lt, sum_empty]
            exact add_eq_of_eq_sub (id (Eq.symm h'))
        apply le_of_eq h
      _ ≤ ∑ x ∈ Finset.Icc 1 (⌈b⌉ - 1), phiDeriv R S x := by
        have h : ⌈a⌉ ≤ ⌈b⌉ - 1 := by
          have hc : ⌈a⌉ < ⌈b⌉ := by
            apply lt_of_le_of_ne
            apply ceil_le_ceil
            linarith [hab]
            push_neg at hceil
            exact hceil
          apply le_sub_one_of_lt hc
        have h' : Finset.Icc 1 (⌈a⌉) ⊆ Finset.Icc 1 (⌈b⌉ - 1) := by apply Finset.Icc_subset_Icc (by linarith) h
        apply  Finset.sum_le_sum_of_subset_of_nonneg h'
        intro i _ _
        apply le_of_lt
        apply phiDeriv_pos
      _ < phi R S b := by
        unfold phi
        simp only [cast_max, cast_zero, cast_sub, cast_one, lt_add_iff_pos_right]
        apply mul_pos
        simp only [sub_pos, max_lt_iff]
        constructor
        · linarith [hb]
        · linarith [ceil_lt_add_one b]
        apply phiDeriv_pos R S

theorem phi_strictMono : StrictMono (phi R S) := by
  rintro a b h
  by_cases ha0 : a ≤ 0
  · by_cases hb0 : b ≤ 0
    · rw [phi_eq_self_of_le_zero R S ha0, phi_eq_self_of_le_zero R S hb0]; assumption
    · by_cases hb1 : b ≤ 1
      · push_neg at *
        apply phi_pos_gt_nonpos R S ha0 hb0
      · push_neg at *
        apply phi_pos_gt_nonpos R S ha0 hb0
  · by_cases ha1 : a ≤ 1
    push_neg at *
    have hac : ⌈a⌉ = 1 := by
      apply ceil_eq_iff.2
      simp only [cast_one, sub_self, ha0, ha1, and_self]
    · by_cases hb1 : b ≤ 1
      · have hbc : ⌈b⌉ = 1 := by
          apply ceil_eq_iff.2
          simp only [cast_one, sub_self, lt_trans ha0 h, hb1, and_self]
        have hceil : ⌈a⌉ = ⌈b⌉ := by simp [hac, hbc]
        have hderiv : phiDeriv R S a = phiDeriv R S b := by
          unfold phiDeriv
          simp only [hceil]
        rw [phi_of_pos_of_le_one R S ha0 ha1, phi_of_pos_of_le_one R S (by linarith) hb1]
        simp only [hderiv, gt_iff_lt]
        exact mul_lt_mul_of_pos_right h (phiDeriv_pos R S _)
      · apply phi_strictMono_of_gt_one R S (by linarith) (by linarith) h
    apply phi_strictMono_of_gt_one R S (by linarith) (by linarith) h
