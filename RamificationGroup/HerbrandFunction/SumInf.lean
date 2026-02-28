import RamificationGroup.HerbrandFunction.Basic
import Mathlib.RingTheory.Valuation.Basic

open scoped Classical
open HerbrandFunction DiscreteValuation AlgEquiv Valued
open DiscreteValuation Subgroup Set Function Finset BigOperators Int Valued

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [vK : Valued K ℤₘ₀] [Valuation.IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Valuation.IsDiscrete vL.v] [Algebra K L] [IsValExtension vK.v vL.v] [FiniteDimensional K L] [CompleteSpace K] [Algebra.IsSeparable K L]
[Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])]

set_option maxHeartbeats 0

noncomputable def HerbrandFunction.Ramification_Group_diff (i : ℤ) : Finset (L ≃ₐ[K] L) := ((G(L/K)_[i] : Set (L ≃ₐ[K] L)) \ (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L))).toFinset

theorem Ramification_Group_Disjoint {i j : ℤ} {s : (L ≃ₐ[K] L)} (hi : s ∈ Ramification_Group_diff K L i) (hj : s ∈ Ramification_Group_diff K L j) (hij : i ≠ j) : s ∈ (⊥ : Finset (L ≃ₐ[K] L)) := by
  simp
  unfold Ramification_Group_diff at *
  simp at hi hj
  rcases hi with ⟨hi1, hi2⟩
  rcases hj with ⟨hj1, hj2⟩
  by_cases h : i < j
  · have hle : i + 1 ≤ j := by apply Int.le_of_sub_one_lt (by simp [h])
    have hle' : G(L/K)_[j] ≤ G(L/K)_[(i + 1)] := by apply lowerRamificationGroup.antitone K L hle
    apply hi2
    apply mem_of_subset_of_mem hle' hj1
  · have hle : j + 1 ≤ i := by
      apply Int.le_of_sub_one_lt
      apply lt_of_le_of_ne (by push_neg at h; linarith [h]) (by ring; apply hij.symm)
    have hle' : G(L/K)_[i] ≤ G(L/K)_[(j + 1)] := by apply lowerRamificationGroup.antitone K L hle
    apply hj2
    apply mem_of_subset_of_mem hle' hi1

theorem Ramification_Group_pairwiseDisjoint (n : ℤ) : (PairwiseDisjoint (↑(Finset.Icc (-1) (n - 1))) (Ramification_Group_diff K L)) := by
  rintro i _ j _ hij u hu1 hu2
  have hu : u ≤ (Ramification_Group_diff K L i) ∩ (Ramification_Group_diff K L j) := by
    rintro s hs
    simp only [Finset.mem_inter]
    constructor
    · apply mem_of_subset_of_mem hu1 hs
    · apply mem_of_subset_of_mem hu2 hs
  apply le_trans hu
  rintro s hs
  simp at hs
  apply Ramification_Group_Disjoint K L hs.1 hs.2 hij

set_option synthInstance.maxHeartbeats 0

variable [CompleteSpace K] [Algebra.IsSeparable K L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])]


theorem mem_all_lowerRamificationGroup_iff_refl {x : (L ≃ₐ[K] L)} : (∀ n : ℤ, x ∈ G(L/K)_[n]) ↔ x = .refl := by
  constructor <;> intro h
  · by_contra hc
    push_neg at hc
    have hx : x = AlgEquiv.refl := by
      obtain ⟨u, hu⟩ := exist_lowerRamificationGroup_eq_bot (K := K) (L := L)
      replace h : x ∈ G(L/K)_[u] := by apply h u
      rw [hu] at h
      apply Subgroup.mem_bot.1 h
    apply hc hx
  · intro n
    rw [h]
    apply Subgroup.one_mem

theorem m_lt_n_of_in_G_m_of_notin_G_n {x : (L ≃ₐ[K] L)} {m n : ℤ} (hm : x ∈ G(L/K)_[m]) (hn : x ∉ G(L/K)_[n]) : m ≤ n - 1 := by
  by_contra hc
  push_neg at *
  have h : G(L/K)_[m] ≤  G(L/K)_[n] := by
    convert lowerRamificationGroup.antitone K L hc
    simp only [sub_add_cancel]
  apply hn
  apply Set.mem_of_subset_of_mem h hm

theorem aux_0 {x : L ≃ₐ[K] L} (hx : x ≠ .refl) : ∃ n : ℤ , -1 ≤ n ∧ x ∈ G(L/K)_[n] ∧ x ∉ G(L/K)_[(n + 1)] := by
  by_contra hc; push_neg at hc
  apply hx
  apply (mem_all_lowerRamificationGroup_iff_refl K L).1
  intro n
  set t := n + 1; have : n = t - 1 := by ring
  rw [this]
  induction' t using Int.induction_on with m hm m _
  · simp only [zero_sub, reduceNeg]
    rw [lowerRamificationGroup_eq_decompositionGroup, decompositionGroup_eq_top]
    apply Subgroup.mem_top; rfl
  · have : ((m : ℤ) + 1 - 1) = ((m : ℤ) - 1 + 1) := by simp only [add_sub_cancel_right, sub_add_cancel]
    rw [this]
    apply hc (m - 1) (by linarith) hm
  · rw [lowerRamificationGroup_eq_decompositionGroup, decompositionGroup_eq_top]
    apply Subgroup.mem_top
    simp only [reduceNeg, tsub_le_iff_right, neg_add_cancel, zero_add]
    omega


theorem Raimification_Group_split (n : ℤ) : (⊤ : Finset (L ≃ₐ[K] L)) = (disjiUnion (Finset.Icc (-1) (n - 1)) (Ramification_Group_diff K L) (Ramification_Group_pairwiseDisjoint K L n)) ∪ (G(L/K)_[n] : Set (L ≃ₐ[K] L)).toFinset := by
  ext x
  constructor
  · simp
    by_cases hc : x ∉ G(L/K)_[n]
    · left
      unfold Ramification_Group_diff
      have h : x ≠ .refl := by
        by_contra hc1
        apply hc
        apply (mem_all_lowerRamificationGroup_iff_refl K L).2 hc1
      obtain ⟨t, ht1, ht2, ht3⟩ := aux_0 K L h
      use t
      constructor
      · constructor
        --the index is greater than -1
        · exact ht1
        · apply m_lt_n_of_in_G_m_of_notin_G_n K L ht2 hc
      · simp only [toFinset_diff, mem_sdiff, mem_toFinset, SetLike.mem_coe, ht2, ht3,
        not_false_eq_true, and_self]
    · push_neg at hc
      right; exact hc
  · intro h
    simp only [Finset.top_eq_univ, Finset.mem_univ]

theorem phi_eq_sum_card {u : ℚ} (hu : 0 < u): phi K L u = (1 / Nat.card G(L/K)_[0]) * ((∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
  unfold phi phiDeriv
  calc
    _ = ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card  G(L/K)_[⌈x⌉] : ℚ) / (Nat.card G(L/K)_[0] : ℚ) + (u - (max 0 (⌈u⌉ - 1))) * ((Nat.card G(L/K)_[⌈u⌉] ) / (Nat.card G(L/K)_[0] )) := by
      have h1 : ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card G(L/K)_[(max 0 ⌈(x : ℚ)⌉)] : ℚ) / (Nat.card G(L/K)_[0] : ℚ)  = ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card  G(L/K)_[⌈x⌉] : ℚ) / (Nat.card G(L/K)_[0] : ℚ) := by
        have h : ∀ i ∈ Finset.Icc 1 (⌈u⌉ - 1), max 0 ⌈(i : ℚ)⌉ = ⌈i⌉ := by
          intro i hi
          simp only [ceil_intCast, ceil_int, id_eq, max_eq_right_iff]
          rw [Finset.mem_Icc] at hi; linarith [hi.1]
        apply (Finset.sum_eq_sum_iff_of_le ?_).2
        · intro i hi
          rw [h i hi]
        · intro i hi
          rw [h i hi]
      have h2 :  (u - (max 0 (⌈u⌉ - 1))) * ((Nat.card G(L/K)_[(max 0 ⌈u⌉)] : ℚ) / (Nat.card G(L/K)_[0] : ℚ)) = (u - (max 0 (⌈u⌉ - 1))) * ((Nat.card G(L/K)_[⌈u⌉] : ℚ) / (Nat.card G(L/K)_[0] : ℚ)) := by
        have h : max 0 ⌈u⌉ = ⌈u⌉ := by
          apply max_eq_right
          apply le_of_lt; apply ceil_pos.2; exact hu
        rw [h]
      rw [h1, h2]
    _ = (1 / (Nat.card G(L/K)_[0] )) * ∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card G(L/K)_[⌈x⌉] ) + (u - (max 0 (⌈u⌉ - 1))) * ((Nat.card G(L/K)_[⌈u⌉] ) / (Nat.card G(L/K)_[0] )) := by
      congr
      convert (Finset.sum_div (Finset.Icc 1 (⌈u⌉ - 1)) (fun x => (Nat.card (lowerRamificationGroup K L ⌈x⌉) : ℚ)) (Nat.card ↥ G(L/K)_[0] : ℚ))
      · exact
        Eq.symm (sum_div (Finset.Icc 1 (⌈u⌉ - 1)) (fun i ↦ (Nat.card ↥ G(L/K)_[⌈i⌉] : ℚ)) (Nat.card ↥ G(L/K)_[0] : ℚ))
      · convert one_div_mul_eq_div (Nat.card G(L/K)_[0] : ℚ) ((∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card ↥ G(L/K)_[⌈x⌉]) : ℚ)
        · exact Nat.cast_sum (Finset.Icc 1 (⌈u⌉ - 1)) fun x ↦ Nat.card ↥ G(L/K)_[⌈x⌉]
        · exact
          Eq.symm (sum_div (Finset.Icc 1 (⌈u⌉ - 1)) (fun i ↦ (Nat.card ↥ G(L/K)_[⌈i⌉] : ℚ)) (Nat.card ↥ G(L/K)_[0] : ℚ))
    _ = (1 / Nat.card G(L/K)_[0]) * ((∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
      rw [mul_add]
      congr 1
      rw [← mul_assoc, mul_comm (1 / (Nat.card G(L/K)_[0] : ℚ)), mul_assoc, one_div_mul_eq_div]


theorem truncatedLowerindex_eq_if_aux {i : ℤ} {u : ℚ} {s : (L ≃ₐ[K] L)} (hgt : -1 < u) (hgt' : -1 ≤ i) (hu : i ≤ (⌈u⌉ - 1)) (hs : s ∈ HerbrandFunction.Ramification_Group_diff K L i) : i_[L/K]ₜ (u + 1) s = i + 1 := by
  obtain ⟨gen, hgen⟩ := AlgEquiv.Simple_Extension_of_CDVR (K := K) (L := L)
  unfold Ramification_Group_diff at hs
  simp only [Set.toFinset_diff, Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe] at hs
  rcases hs with ⟨hs1, hs2⟩
  have h1 : i + 1 ≤ i_[L/K]ₜ (u + 1) s := by
    have h1' : i ≤ i_[L/K]ₜ (u + 1) s - 1 := by
      apply (le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup s i (u + 1)  _ hgen).2
      · simp only [ceil_intCast, hs1]
      · simp only [add_le_add_iff_right]
        apply le_of_lt; apply Int.add_one_le_ceil_iff.1; linarith [hu]
    linarith [h1']
  have h2 : i_[L/K]ₜ (u + 1) s < i + 2 := by
    by_contra hc; push_neg at hc
    have h : s ∈ decompositionGroup K L := by exact mem_decompositionGroup s
    have hs2' : s ∈ G(L/K)_[⌈i + 1⌉] := by
      convert mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one h (u := ((i : ℤ) + 1)) hgen (by linarith [hc])
      simp only [ceil_add_one, ceil_int, id_eq, ceil_intCast]
    apply hs2
    simp only [ceil_add_one, ceil_int, id_eq] at hs2'; exact hs2'
  have h3 : i_[L/K] s ≠ ⊤ := by
    by_contra hc
    rw [lowerIndex_eq_top_iff_eq_refl (by apply mem_decompositionGroup)] at hc
    have hs2' : s ∈ G(L/K)_[(i + 1)] := by
      rw [hc]; apply Subgroup.one_mem
    apply hs2 hs2'
  have h4 : i_[L/K]ₜ (u + 1) s = ↑(WithTop.untop (i_[L/K] s) (of_eq_false (eq_false h3) : ¬ i_[L/K] s = ⊤)) := by
    unfold AlgEquiv.truncatedLowerIndex
    simp only [h3, ↓reduceDIte, min_eq_right_iff, ge_iff_le]
    apply le_of_lt
    have h : i_[L/K] s < (i + 1).toNat + 1 := by
      by_contra hc
      push_neg at hc
      have hi : 0 ≤ i + 1 := by linarith [hgt']
      have hs2' : s ∈ G(L/K)_[(i + 1).toNat] := by
        apply (mem_lowerRamificationGroup_iff_of_generator hgen ?_ (i + 1).toNat).2
        exact hc
        apply mem_decompositionGroup s
      rw [Int.toNat_of_nonneg hi] at hs2'
      apply hs2 hs2'
    have h' : (i + 1).toNat ≤ i_[L/K] s := by
      by_contra hc
      push_neg at hc
      have h1' : i_[L/K]ₜ (u + 1) s < i + 1 := by
        unfold AlgEquiv.truncatedLowerIndex
        simp only [h3, ↓reduceDIte, min_lt_iff, add_lt_add_iff_right]
        right
        rw [← Int.cast_one, ← cast_add, ← Int.cast_natCast, cast_lt, ← Int.toNat_of_nonneg (a := i + 1), Nat.cast_lt]
        apply (WithTop.untop_lt_iff _).2
        exact hc
        linarith [hgt']
      absurd h1
      push_neg
      exact h1'
    have hilk : i_[L/K] s = (i + 1).toNat := by
      by_cases hc : 1 ≤ i + 1
      · apply (ENat.toNat_eq_iff _).1
        apply Nat.eq_of_lt_succ_of_not_lt
        · rw [← Nat.cast_lt (α := ℕ∞), ENat.coe_toNat h3, Nat.cast_add, Nat.cast_one]
          exact h
        · push_neg
          rw [← Nat.cast_le (α := ℕ∞), ENat.coe_toNat h3]
          exact h'
        simp only [ne_eq, toNat_eq_zero, not_le]
        linarith [hc]
      · have hi : i = -1 := by
          symm; apply eq_iff_le_not_lt.2; constructor
          · exact hgt'
          · linarith [hc]
        simp only [hi, reduceNeg, neg_add_cancel, toNat_zero, CharP.cast_eq_zero]
        by_contra hcon
        have hilk : 1 ≤ i_[L/K] s := by
          apply ENat.one_le_iff_ne_zero.2 hcon
        simp only [hi, reduceNeg, neg_add_cancel, toNat_zero, CharP.cast_eq_zero, zero_add] at h
        absurd h; push_neg
        exact hilk
    apply lt_of_le_of_lt (b := (⌈u⌉.toNat : ℚ))
    · rw [Nat.cast_le]
      apply (WithTop.untop_le_iff h3).2
      rw [hilk, ENat.some_eq_coe, Nat.cast_le]
      apply toNat_le_toNat
      linarith [hu]
    · rw [← Int.cast_natCast, Int.toNat_of_nonneg]
      exact ceil_lt_add_one u
      apply le_ceil_iff.mpr ?_
      simp only [cast_zero, zero_sub]
      exact hgt
  rw [h4, ← cast_one, ← cast_add (m := i) (n := 1)]
  have : (2 : ℚ) = ((2 : ℤ) : ℚ) := by simp only [cast_ofNat]
  rw [h4] at h1 h2
  have h5 : (WithTop.untop (i_[L/K] s) (of_eq_false (eq_false h3) : ¬ i_[L/K] s = ⊤)) = i + 1 := by
    symm
    apply Int.aux
    · rw [← cast_one, ← cast_add (m := i) (n := 1), ← Int.cast_natCast, cast_le] at h1
      exact h1
    · have h : (2 : ℚ) = ((2 : ℤ) : ℚ) := by simp only [cast_ofNat]
      rw [h , ← cast_add (m := i) (n := 2), ← Int.cast_natCast, cast_lt] at h2
      rw [add_assoc, one_add_one_eq_two]; exact h2
  exact Rat.ext h5 rfl

theorem sum_of_diff_aux_aux {i : ℤ} {u : ℚ} (hu : 0 ≤ u) (h : i ∈ Finset.Icc (-1) (⌈u⌉ - 1)) : ∑ s ∈ Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) = (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)]) := by
  calc
     ∑ s ∈ Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) = ∑ s ∈ Ramification_Group_diff K L i, ((i : ℚ) + 1) := by
      apply sum_equiv (by rfl : (L ≃ₐ[K] L) ≃ (L ≃ₐ[K] L)) (by simp)
      intro s hs
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 h
      apply truncatedLowerindex_eq_if_aux K L (by linarith [hu]) h1 h2 hs
     _ = (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)]) := by
      simp only [sum_const, smul_add, nsmul_eq_mul, mul_comm, mul_one, Nat.card_eq_fintype_card,
        add_mul, one_mul]
      unfold Ramification_Group_diff
      have hsub : (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L)) ⊆ (G(L/K)_[i] : Set (L ≃ₐ[K] L)) := by
        apply lowerRamificationGroup.antitone
        linarith
      have h : (((G(L/K)_[i] : Set (L ≃ₐ[K] L)) \ (G(L/K)_[(i + 1)] : Set (L ≃ₐ[K] L))).toFinset).card = ((Fintype.card G(L/K)_[i] ) - (Fintype.card G(L/K)_[(i + 1)])) := by
        rw [toFinset_diff, card_sdiff (by apply Set.toFinset_mono hsub)]
        simp only [toFinset_card, SetLike.coe_sort_coe]
      rw [h, Nat.cast_sub]
      ring
      exact Set.card_le_card hsub

theorem truncatedLowerindex_eq_of_lt {s : (L ≃ₐ[K] L)} {u : ℚ} (h : s ∈ G(L/K)_[⌈u⌉]) (hu : 0 ≤ u) : i_[L/K]ₜ (u + 1) s = u + 1 := by
  obtain ⟨gen, hgen⟩ := AlgEquiv.Simple_Extension_of_CDVR (K := K) (L := L)
  unfold AlgEquiv.truncatedLowerIndex
  by_cases ht : i_[L/K] s = ⊤
  · simp only [ht, ↓reduceDIte]
  · simp only [ht, ↓reduceDIte, min_eq_left_iff]
    have h1 : ⌈u⌉.toNat + 1 ≤ i_[L/K] s := by
      apply (mem_lowerRamificationGroup_iff_of_generator hgen ?_ ⌈u⌉.toNat).1
      rw [Int.toNat_of_nonneg]; exact h; exact ceil_nonneg hu
      · apply mem_decompositionGroup
    have h2 : u + 1 ≤ ⌈u⌉.toNat + 1 := by
      apply (add_le_add_iff_right 1).2
      apply le_trans (b := (⌈u⌉ : ℚ))
      · exact le_ceil u
      · apply Int.cast_mono; apply self_le_toNat ⌈u⌉
    apply le_trans h2
    have h3 : ⌈u⌉.toNat + 1 ≤ WithTop.untop (i_[L/K] s) (of_eq_false (eq_false ht) : ¬ i_[L/K] s = ⊤) := by
      apply (WithTop.le_untop_iff ht).2
      simp only [WithTop.coe_add, ENat.some_eq_coe, WithTop.coe_one, h1]
    rw [← Mathlib.Tactic.Ring.inv_add (a₁ := ⌈u⌉.toNat) (a₂ := 1) rfl (by simp only [Nat.cast_one])]
    apply Nat.mono_cast h3

set_option synthInstance.maxHeartbeats 0

theorem sum_fiberwise_aux {u : ℚ} (hu : 0 ≤ u) : ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) = ∑ i ∈ Finset.Icc (-1) (⌈u⌉ - 1), ∑ s ∈ Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s) + (u + 1) * (Nat.card ↥ G(L/K)_[⌈u⌉]) := by
  rw [Raimification_Group_split K L ⌈u⌉, sum_union, sum_disjiUnion]
  congr 1
  calc
    _ =  ∑ x ∈ (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L)).toFinset , (u + 1) := by
      apply sum_equiv (by rfl : (L ≃ₐ[K] L) ≃ (L ≃ₐ[K] L)) (by simp)
      intro i hi
      apply truncatedLowerindex_eq_of_lt K L _ hu
      apply Set.mem_toFinset.1 hi
    _ = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) := by
      simp [← mul_sum (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L)).toFinset (fun _ => 1) (u + 1), add_mul, mul_comm]
      ring
  simp [Finset.disjoint_iff_ne]
  intro s n _ hn2 hs b hb
  unfold Ramification_Group_diff at *
  simp at hs
  rcases hs with ⟨_, hs2⟩
  by_contra h
  have h' : s ∈ G(L/K)_[⌈u⌉] := by
     rw [← h] at hb; exact hb
  have hs : s ∉ G(L/K)_[⌈u⌉] := by
    apply Set.not_mem_subset _ hs2
    apply lowerRamificationGroup.antitone
    linarith [hn2]
  apply hs h'

theorem sum_sub_aux {u : ℚ} (hu : 0 ≤ ⌈u⌉ - 1): (∑ i ∈ Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)])) = ∑ i ∈ Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[i] - ⌈u⌉ * (Nat.card G(L/K)_[⌈u⌉]) := by
  calc
    _ = ∑ i ∈ Finset.Icc (-1) (⌈u⌉ - 1), ((i + 1) * Nat.card G(L/K)_[i] - (i + 1) * Nat.card G(L/K)_[(i + 1)]) := by
      apply (Finset.sum_eq_sum_iff_of_le _).2
      · intro i _
        rw [mul_sub]
      · intro i _
        apply le_of_eq
        rw [mul_sub]
    _ = ∑ i ∈ Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * Nat.card G(L/K)_[i] - ∑ i ∈ Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * Nat.card G(L/K)_[(i + 1)] := by
      rw [sum_sub_distrib]
    _ = ∑ i ∈ Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * Nat.card G(L/K)_[i] - ∑ i ∈ Finset.Icc 0 ⌈u⌉, i * Nat.card G(L/K)_[i] := by
      congr 1
      let e : ℤ ≃ ℤ :=
      {
        toFun := fun x => x + 1
        invFun := fun x => x - 1
        left_inv := by
          rintro x
          simp only [add_sub_cancel_right]
        right_inv := by
          rintro x
          simp only [sub_add_cancel]
      }
      apply sum_equiv e
      rintro i
      constructor
      · simp only [reduceNeg, Finset.mem_Icc, and_imp]
        intro hi1 hi2
        simp only [Equiv.coe_fn_mk, add_one_le_ceil_iff, e]
        constructor
        · linarith [hi1]
        · apply add_one_le_ceil_iff.1 (by linarith [hi2])
      · simp only [Finset.mem_Icc, reduceNeg, and_imp]
        intro hi
        simp only [sub_nonneg, one_le_ceil_iff, Equiv.coe_fn_mk, add_one_le_ceil_iff, reduceNeg,
          e] at *
        intro hi'
        constructor
        · linarith [hi]
        · linarith [add_one_le_ceil_iff.2 hi']
      rintro i _
      simp only [Nat.card_eq_fintype_card, Equiv.coe_fn_mk, e]
    _ = ((-1) + 1) * Nat.card G(L/K)_[(-1)] + ∑ i ∈ Finset.Icc 0 (⌈u⌉ - 1), (i + 1) * Nat.card G(L/K)_[i] - ∑ i ∈ Finset.Icc 0 (⌈u⌉ - 1), i * Nat.card G(L/K)_[i] - ⌈u⌉ * Nat.card G(L/K)_[⌈u⌉] := by
      have h : (-1) ≤ ⌈u⌉ - 1 := by linarith [hu]
      erw [← sum_insert_left_aux' (-1) (⌈u⌉ - 1) h (fun i => (i + 1) * Nat.card (lowerRamificationGroup K L i)), sub_sub, ← sum_insert_right_aux' 0 ⌈u⌉ (by linarith [h]) (fun i => i * Nat.card (lowerRamificationGroup K L i))]
      simp
    _ = ∑ i ∈ Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[i] - ⌈u⌉ * (Nat.card G(L/K)_[⌈u⌉]) := by
      rw [neg_add_cancel, zero_mul, zero_add]
      congr
      rw [← sum_sub_distrib]
      ring_nf
      exact Eq.symm (Nat.cast_sum (Finset.Icc 0 (-1 + ⌈u⌉)) fun x ↦ Nat.card ↥ G(L/K)_[x])


theorem truncatedLowerIndex_aux {u : ℚ} (hu : -1 ≤ u) {x : L ≃ₐ[K] L} (hx : x ∈ G(L/K)_[⌈u⌉]) : i_[L/K]ₜ (u + 1) x = (u + 1) := by
  obtain ⟨gen, hgen⟩ := AlgEquiv.Simple_Extension_of_CDVR (K := K) (L := L)
  unfold AlgEquiv.truncatedLowerIndex
  by_cases hc : i_[L/K] x = ⊤
  · simp only [hc, ↓reduceDIte]
  · simp only [hc, ↓reduceDIte, min_eq_left_iff]
    by_cases hu' : u = -1
    · simp only [hu', neg_add_cancel, Nat.cast_nonneg]
    have h : ⌈u⌉.toNat + 1 ≤ WithTop.untop (i_[L/K] x) (of_eq_false (eq_false hc) : ¬ i_[L/K] x = ⊤) := by
      · apply (WithTop.le_untop_iff _).2
        apply (mem_lowerRamificationGroup_iff_of_generator hgen ?_ ⌈u⌉.toNat).1
        · rw [Int.toNat_of_nonneg]; exact hx;
          apply le_ceil_iff.mpr ?_
          simp only [cast_zero, zero_sub]
          apply lt_of_le_of_ne hu
          exact fun a ↦ hu' (id (Eq.symm a))
        · apply mem_decompositionGroup
    apply le_trans (b := (⌈u⌉.toNat + 1 : ℚ))
    · simp only [add_le_add_iff_right]
      apply le_trans
      apply Int.le_ceil
      rw [← Int.cast_natCast]
      simp only [ofNat_toNat, cast_max, cast_zero, le_sup_left]
    · simp only [← Nat.cast_one (R := ℚ), ← Nat.cast_add (m := ⌈u⌉.toNat) (n := 1), Nat.mono_cast h]

theorem phi_eq_sum_inf_aux {u : ℚ} (hu : -1 ≤ u) : (phi K L u) = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) - 1 := by
  by_cases hc : 0 < u
  · have hu' : 0 ≤ ⌈u⌉ - 1 := by
      simp only [sub_nonneg, one_le_ceil_iff]; exact hc
    calc
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[i]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
        apply phi_eq_sum_card K L hc
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i ∈ Finset.Icc 0 (⌈u⌉ - 1), Nat.card G(L/K)_[i]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) - (1 : ℕ) := by
        have h : 0 < Nat.card G(L/K)_[0] := by rw [← ceil_zero (α := ℤ)]; apply Ramification_Group_card_pos K L (u := 0)
        erw [← sum_insert_left_aux 0 (⌈u⌉ - 1) hu' (fun x => Nat.card (lowerRamificationGroup K L x)), ← (Nat.div_self h), Nat.cast_div (by simp) (by simp [h]), ← (mul_one_div ((Nat.card G(L/K)_[0]) : ℚ) ((Nat.card G(L/K)_[0]) : ℚ)), (mul_comm ((Nat.card ↥ G(L/K)_[0]) : ℚ) (1 / ↑(Nat.card ↥ G(L/K)_[0] ))), ← mul_sub, Nat.cast_sub]
        · ring
        · rw [insert_Icc_left 0 (⌈u⌉ - 1) hu', Finset.sum_insert (by simp)]
          simp only [Nat.card_eq_fintype_card, zero_add, le_add_iff_nonneg_right, zero_le]
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i ∈ Finset.Icc (-1) (⌈u⌉ - 1), (i + 1) * (Nat.card G(L/K)_[i] - Nat.card G(L/K)_[(i + 1)])) + (u + 1) * (Nat.card G(L/K)_[⌈u⌉])) - 1 := by
        rw [sum_sub_aux K L hu', cast_sub]
        congr 2
        have h : (u - max 0 (⌈u⌉ - 1)) * (Nat.card G(L/K)_[⌈u⌉]) = (u + 1) * (Nat.card G(L/K)_[⌈u⌉]) - ⌈u⌉ * (Nat.card G(L/K)_[⌈u⌉]) := by
          simp only [hu', max_eq_right, cast_sub, cast_one, ← sub_add, Nat.card_eq_fintype_card]
          ring
        rw [h, add_sub, cast_mul, cast_natCast, add_comm_sub, add_sub]
        congr
      _ = (1 / Nat.card G(L/K)_[0]) * ((∑ i ∈ Finset.Icc (-1) (⌈u⌉ - 1), ∑ s ∈ Ramification_Group_diff K L i, (AlgEquiv.truncatedLowerIndex K L (u + 1) s)) + (u + 1) * (Nat.card G(L/K)_[⌈u⌉])) - 1 := by
        congr 3
        have h : Finset.Icc (-1) (⌈u⌉ - 1) = Finset.Icc (-1) (⌈u⌉ - 1) := by rfl
        rw [Int.cast_sum]
        apply sum_congr h
        intro x hx
        simp only [Nat.card_eq_fintype_card, cast_mul, cast_add, cast_one, cast_sub,
          Int.cast_natCast, (sum_of_diff_aux_aux K L (by linarith) hx)]
      _ = (1 / Nat.card G(L/K)_[0]) * ((Finset.sum (⊤ : Finset (L ≃ₐ[K] L)) (AlgEquiv.truncatedLowerIndex K L (u + 1) ·))) - 1 := by
        congr 2
        apply (sum_fiberwise_aux K L (by linarith)).symm
  · push_neg at hc
    rw [phi_eq_self_of_le_zero _ _ hc]
    rw [Raimification_Group_split K L 0, sum_union]
    · simp only [one_div, reduceNeg, zero_sub, Finset.Icc_self, disjiUnion_eq_biUnion, singleton_biUnion, zero_add]
      symm
      calc
        _ = ((Nat.card ↥ G(L/K)_[0]) : ℚ)⁻¹ * (0 + ∑ x ∈ (G(L/K)_[0] : Set (L ≃ₐ[K] L)).toFinset, i_[L/K]ₜ (u + 1) x) - 1 := by
          congr
          apply Finset.sum_eq_zero
          intro x hx
          by_cases hu' : u = -1
          · simp only [hu', neg_add_cancel]
            unfold truncatedLowerIndex
            simp only [decompositionGroup_eq_top, mem_top, lowerIndex_eq_top_iff_eq_refl,Nat.cast_nonneg, inf_of_le_left, dite_eq_ite, ite_self]
          · rw [truncatedLowerindex_eq_if_aux K L _ (by linarith) _ hx]
            simp only [reduceNeg, cast_neg, cast_one, neg_add_cancel]
            apply lt_of_le_of_ne hu
            exact fun a ↦ hu' (id (Eq.symm a))
            simp only [reduceNeg, neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
            apply Int.le_ceil_iff.2
            simp only [cast_zero, zero_sub]
            apply lt_of_le_of_ne hu
            exact fun a ↦ hu' (id (Eq.symm a))
        _ = ((Nat.card ↥ G(L/K)_[0]) : ℚ)⁻¹ * (0 + Nat.card G(L/K)_[0] * (u + 1)) - 1 := by
          congr
          have h : Nat.card G(L/K)_[0] = Finset.card (G(L/K)_[0] : Set (L ≃ₐ[K] L)).toFinset := Nat.card_eq_card_toFinset  (G(L/K)_[0] : Set (L ≃ₐ[K] L))
          rw [h, Finset.cast_card, Finset.sum_mul, one_mul]
          apply Finset.sum_congr rfl
          intro x hx
          apply truncatedLowerIndex_aux K L hu _
          by_cases hu' : u = -1
          · rw [hu']
            apply mem_lowerRamificationGroup_of_le_neg_one
            exact mem_decompositionGroup x
            exact ceil_le.mpr rfl
          · have hceil : ⌈u⌉ = 0 := by
              apply ceil_eq_iff.mpr
              simp only [cast_zero, zero_sub]
              refine ⟨lt_of_le_of_ne hu ?_, hc⟩
              exact fun a ↦ hu' (id (Eq.symm a))
            rw [hceil]
            simp only [mem_toFinset, SetLike.mem_coe] at hx
            exact hx
        _ = _ := by simp only [Nat.card_eq_fintype_card, zero_add, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, inv_mul_cancel_left₀, add_sub_cancel_right]
    · unfold Ramification_Group_diff
      simp only [reduceNeg, zero_sub, Finset.Icc_self, toFinset_diff, disjiUnion_eq_biUnion, singleton_biUnion, neg_add_cancel]
      exact sdiff_disjoint
