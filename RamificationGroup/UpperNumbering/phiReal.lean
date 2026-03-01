import RamificationGroup.UpperNumbering.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import RamificationGroup.Valuation.Extension


open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction MeasureTheory.MeasureSpace intervalIntegral Pointwise AlgEquiv ExtDVR Asymptotics Filter intervalIntegral MeasureTheory

variable (K K' L : Type*) {ΓK : outParam Type*} [Field K] [Field K'] [Field L] [vK : Valued K ℤₘ₀] [vK' : Valued K' ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vK'.v] [IsDiscrete vL.v] [Algebra K L] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L] [IsValExtension vK.v vK'.v] [IsValExtension vK'.v vL.v] [IsValExtension vK.v vL.v] [Normal K K'] [Normal K L] [FiniteDimensional K L] [FiniteDimensional K K'] [FiniteDimensional K' L] [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])]

local notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup_aux K L v

noncomputable def μ : MeasureTheory.Measure ℝ := MeasureTheory.volume

noncomputable def phiDerivReal (u : ℝ) : ℝ :=
  (Nat.card G(L/K)_[(max 0 ⌈u⌉)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ)

noncomputable def phiReal (u : Real) : Real := ∫ x in (0 : ℝ)..u, phiDerivReal K L x ∂μ

#check Valuation.IsEquiv
theorem phiReal_zero_eq_zero : phiReal K L 0 = 0 := by
  unfold phiReal
  simp only [intervalIntegral.integral_same]


theorem phiReal_one_le_one : phiReal K L 1 ≤ 1 := by
  unfold phiReal
  rw [integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [MeasureTheory.setIntegral_congr_fun (g := fun _ => phiDerivReal K L 1) measurableSet_Ioc]
  · rw [MeasureTheory.setIntegral_const]
    simp [μ, MeasureTheory.Measure.real_def, Real.volume_Ioc]
    unfold phiDerivReal
    have hmax1 : max 0 ⌈(1 : ℝ)⌉ = (1 : ℤ) := by norm_num
    rw [hmax1]
    refine (div_le_one (show 0 < (Nat.card G(L/K)_[0] : ℝ) by exact Nat.cast_pos.2 Nat.card_pos)).2 ?_
    exact Nat.cast_le.2 <| by
      apply Nat.card_mono
      · exact Set.toFinite (G(L/K)_[0] : Set (L ≃ₐ[K] L))
      · exact lowerRamificationGroup.antitone K L (by linarith : (0 : ℤ) ≤ 1)
  · intro x hx
    have hx' : ⌈x⌉ = 1 := by
      apply Int.ceil_eq_iff.2
      simp only [Int.cast_one, sub_self]
      exact ⟨(Set.mem_Ioc.1 hx).1, (Set.mem_Ioc.1 hx).2⟩
    unfold phiDerivReal
    rw [hx']
    simp

theorem phiDerivReal_pos {x : ℝ} : 0 < phiDerivReal K L x := by
  unfold phiDerivReal
  apply div_pos
  · exact Nat.cast_pos.2 Nat.card_pos
  · exact Nat.cast_pos.2 Nat.card_pos

theorem phiDerivReal_le_one {u : ℝ} (h : 0 < u) : phiDerivReal K L u ≤ 1 := by
  have h' : 0 ≤ ⌈u⌉ := le_of_lt (Int.ceil_pos.2 h)
  rw [phiDerivReal, max_eq_right h']
  refine (div_le_one (show 0 < (Nat.card G(L/K)_[0] : ℝ) by exact Nat.cast_pos.2 Nat.card_pos)).2 ?_
  exact Nat.cast_le.2 <| by
    apply Nat.card_mono
    · exact Set.toFinite (G(L/K)_[0] : Set (L ≃ₐ[K] L))
    · exact lowerRamificationGroup.antitone K L h'

theorem phiReal_nonneg {u : ℝ} (h : 0 ≤ u) : 0 ≤ phiReal K L u := by
  simp only [phiReal, integral_of_le h]
  apply MeasureTheory.setIntegral_nonneg_ae measurableSet_Ioc
  unfold Filter.Eventually phiDerivReal
  apply MeasureTheory.ae_of_all
  intro a _
  apply div_nonneg
  apply Nat.cast_nonneg
  apply Nat.cast_nonneg

#check IsUltrametricDist
#check Valuation.prolongs_by_ramificationIndex
#check NormedAlgebra

-- instance Valuation.IsDiscrete_comap (g : L ≃ₐ[K] L) : (Valuation.comap (R := L) g v).IsDiscrete (A := L) where
--   one_mem_range := by
--     obtain ⟨x, hx⟩ := IsDiscrete.one_mem_range (v := vL.v)
--     simp only [Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, Set.mem_range, comap_apply, RingHom.coe_coe]
--     use g⁻¹ x
--     rw [show g (g⁻¹ x) = x from (eq_symm_apply g).mp rfl]
--     exact hx


-- open NormedField
-- variable [CompleteSpace K] in
-- theorem Val_AlgEquiv_eq (g : L ≃ₐ[K] L) {x : L} (hx : x ∈ vL.v.integer) : vL.v x = vL.v (g x) := by
--   have h := algHom_preserve_val_of_complete (K := K) (L := L) g
--   rw [show vL.v (g x) = (vL.v.comap g) x by rfl]
--   exact DFunLike.congr (isEquiv_iff_eq.mp h) rfl


#check mem_decompositionGroup
variable [CompleteSpace K]
instance {u : ℤ} : Subgroup.Normal (lowerRamificationGroup K L u) where
  conj_mem := by
    unfold lowerRamificationGroup
    simp only [ofAdd_sub, ofAdd_neg, Subtype.forall, Subgroup.mem_mk, Set.mem_setOf_eq, mul_apply]
    intro n hn g
    rcases hn with ⟨hd, hn⟩
    constructor
    · apply mem_decompositionGroup
    · intro a ha
      have hg : g⁻¹ a ∈ v.integer := by
        rw [mem_integer_iff, val_map_le_one_iff (mem_decompositionGroup g⁻¹)]
        exact ha
      let hn' := hn (g⁻¹ a) hg
      rw [Val_AlgEquiv_eq g, _root_.map_sub] at hn'
      · have hgg : g (g⁻¹ a) = a := by exact (eq_symm_apply g).mp rfl
        rw [hgg] at hn'
        exact hn'
      · refine Subring.sub_mem v.integer ?_ hg
        rw [mem_integer_iff, val_map_le_one_iff (mem_decompositionGroup n)]
        exact hg


------------------------------for lower
theorem lowerIndex_eq_of_subgroup_aux {t : L ≃ₐ[K] L} {k : L ≃ₐ[K'] L} (h : AlgEquiv.restrictScalarsHom K k = t) : i_[L/K] t = i_[L/K'] k := by
  unfold AlgEquiv.lowerIndex
  have h' : ∀ x : L, t x = k x := by
    intro x
    rw [← h]
    rfl
  have h'' : ⨆ x : vL.v.integer, vL.v (t x - x) = ⨆ x : vL.v.integer, vL.v (k x - x) := iSup_congr fun i ↦ congrArg (vL.v) (congrFun (congrArg HSub.hSub (h' ↑i)) (i : L))
  rw [h'']

variable [CompleteSpace K] [CompleteSpace K']
theorem RamificationGroup_of_Subgroup_aux {t : L ≃ₐ[K] L} {n : ℤ} (hn : 0 ≤ n) : t ∈ G(L/K')_[n].map (AlgEquiv.restrictScalarsHom K) → t ∈ G(L/K)_[n] := by
  obtain ⟨gen, hgen⟩ := AlgEquiv.Simple_Extension_of_CDVR (K := K) (L := L)
  obtain ⟨gen', hgen'⟩ := AlgEquiv.Simple_Extension_of_CDVR (K := K') (L := L)
  intro ht
  rw [← Int.toNat_of_nonneg (a := n)]
  apply (mem_lowerRamificationGroup_iff_of_generator (K := K) (L := L) hgen ?_ n.toNat).2
  obtain ⟨k, hk1, hk2⟩ := Subgroup.mem_map.1 ht
  rw [lowerIndex_eq_of_subgroup_aux K K' L hk2]
  apply (mem_lowerRamificationGroup_iff_of_generator (K := K') (L := L) hgen' ?_ n.toNat).1
  rw [Int.toNat_of_nonneg]
  exact hk1
  apply hn
  repeat
    {
      rw [decompositionGroup_eq_top]
      exact trivial
    }
  apply hn

theorem RamificationGroup_iff_Subgroup_aux {t : L ≃ₐ[K] L} {n : ℤ} (hn : 0 ≤ n) : t ∈ G(L/K')_[n].map (AlgEquiv.restrictScalarsHom K) ↔ t ∈ G(L/K)_[n] ⊓ (⊤ : Subgroup (L ≃ₐ[K'] L)).map (restrictScalarsHom K) := by
  obtain ⟨gen, hgen⟩ := AlgEquiv.Simple_Extension_of_CDVR (K := K) (L := L)
  obtain ⟨gen', hgen'⟩ := AlgEquiv.Simple_Extension_of_CDVR (K := K') (L := L)
  constructor
  <;> intro ht
  · rw [Subgroup.mem_inf]
    constructor
    · apply RamificationGroup_of_Subgroup_aux K K' L hn ht
    · obtain ⟨k, _, hk2⟩ := Subgroup.mem_map.1 ht
      apply Subgroup.mem_map.2
      use k
      constructor
      · apply Subgroup.mem_top
      · apply hk2
  · rw [Subgroup.mem_inf] at ht
    obtain ⟨k, _, hk2⟩ := Subgroup.mem_map.1 ht.2
    apply Subgroup.mem_map.2
    use k
    constructor
    · have h : k ∈ G(L/K')_[n.toNat] := by
        apply (mem_lowerRamificationGroup_iff_of_generator (K := K') (L := L) hgen' ?_ n.toNat).2
        rw [← lowerIndex_eq_of_subgroup_aux K K' L hk2]
        apply (mem_lowerRamificationGroup_iff_of_generator (K := K) (L := L) hgen ?_ n.toNat).1
        rw [Int.toNat_of_nonneg]
        exact ht.1
        apply hn
        repeat
          {
            rw [decompositionGroup_eq_top]
            exact trivial
          }
      rw [Int.toNat_of_nonneg] at h
      exact h
      apply hn
    · apply hk2

theorem RamificationGroup_card_comp_aux {x : ℝ} (hx : 0 ≤ x) : (Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom K') G(L/K)_[⌈x⌉]) : ℝ) * (Nat.card G(L/K')_[⌈x⌉] : ℝ) = (Nat.card G(L/K)_[⌈x⌉] : ℝ) := by
  norm_cast
  haveI h1 : G(L/K')_[⌈x⌉] ≃ (G(L/K')_[⌈x⌉].map (AlgEquiv.restrictScalarsHom K)) := by
    let f : G(L/K')_[⌈x⌉] → (G(L/K')_[⌈x⌉].map (AlgEquiv.restrictScalarsHom K)) := (fun t => ⟨ (AlgEquiv.restrictScalarsHom K) t.1,by exact Subgroup.apply_coe_mem_map (AlgEquiv.restrictScalarsHom K) G(L/K')_[⌈x⌉] t⟩)
    apply Equiv.ofBijective f
    constructor
    · intro x y
      dsimp [f]
      rw [Subtype.mk.injEq]
      intro hx
      apply_mod_cast AlgEquiv.restrictScalarsHom_injective K hx
    · intro t
      have ht : t.1 ∈ (Subgroup.map (AlgEquiv.restrictScalarsHom K) G(L/K')_[⌈x⌉] ) := by exact SetLike.coe_mem t
      obtain ⟨y, hy1, hy2⟩ := Subgroup.mem_map.1 ht
      dsimp [f]
      simp only [Subtype.exists]
      use y
      use hy1
      exact SetCoe.ext hy2
  haveI h2: (Subgroup.map (AlgEquiv.restrictNormalHom K') G(L/K)_[⌈x⌉]) ≃ (G(L/K)_[⌈x⌉] ⧸ (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉]) := by
    apply Subgroup_map
    -- exact AlgEquiv.restrictNormalHom_surjective L
  haveI h3 : (G(L/K')_[⌈x⌉].map (AlgEquiv.restrictScalarsHom K)) = (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker) := by
    ext t
    constructor
    <;> intro ht
    · apply Subgroup.mem_inf.2
      constructor
      · rw [(RamificationGroup_iff_Subgroup_aux K K' L ?_), Subgroup.mem_inf] at ht
        apply ht.1
        apply Int.ceil_nonneg hx
      · apply (MonoidHom.mem_ker (f := AlgEquiv.restrictNormalHom K')).2
        obtain ⟨y, _, hy2⟩ := Subgroup.mem_map.1 ht
        rw [← hy2]
        apply AlgEquiv.restrictNormalHom_restrictScalarsHom
    · rw [AlgEquiv.restrictNormal_ker_eq] at ht
      apply (RamificationGroup_iff_Subgroup_aux K K' L ?_).2 ht
      apply Int.ceil_nonneg hx
  rw [Nat.card_congr h1, Nat.card_congr h2, h3]
  have h4 : Nat.card (↥ G(L/K)_[⌈x⌉] ⧸ ( G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] ) * Nat.card ((G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉])= Nat.card (G(L/K)_[⌈x⌉]) := by
    symm
    apply Subgroup.card_eq_card_quotient_mul_card_subgroup
  rw [← h4]
  congr 1
  rw [Nat.card_congr]
  let f : (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] → (G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker : Subgroup (L ≃ₐ[K] L)) := fun x => ⟨x.1, by
    apply Subgroup.mem_subgroupOf.1
    exact SetLike.coe_mem x⟩
  haveI hf : Function.Bijective f := by
    constructor
    · intro x y
      dsimp [f]
      simp only [Subtype.mk.injEq, SetLike.coe_eq_coe, imp_self]
    · intro y
      dsimp [f]
      simp only [Subtype.exists]
      use y
      have hy1 : y.1 ∈ G(L/K)_[⌈x⌉] := by
        apply (Subgroup.mem_inf.1 (SetLike.coe_mem y)).1
      have hy2 : ⟨y.1, hy1⟩ ∈ ( G(L/K)_[⌈x⌉] ⊓ (AlgEquiv.restrictNormalHom K').ker).subgroupOf G(L/K)_[⌈x⌉] := by
        apply Subgroup.mem_subgroupOf.2
        simp only [SetLike.coe_mem]
      use hy1; use hy2
  symm
  apply Equiv.ofBijective f hf

#check IsDedekindDomain
#check Ideal.map_eq_bot_iff_of_injective
omit [Normal K L] in
theorem Ideal_map_ne_bot : Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) (IsLocalRing.maximalIdeal ↥𝒪[K]) ≠ ⊥ := fun hc ↦ IsDiscreteValuationRing.not_a_field (↥𝒪[K])
    ((Ideal.map_eq_bot_iff_of_injective (IsValExtension.integerAlgebra_injective K L)).mp hc)

#check Valuation.Integers.isUnit_iff_valuation_eq_one
omit [CompleteSpace K] in
theorem MaximalIdeal_iff_val_lt_one {x : 𝒪[K]} : x ∈ IsLocalRing.maximalIdeal 𝒪[K] ↔ vK.v x < 1 := by
  simpa using (Valuation.mem_maximalIdeal_iff K vK.v (a := x))

omit [Normal K L] in
theorem coe_algbraMap_eq_algebraMap_coe {x : 𝒪[K]} : ((algebraMap 𝒪[K] 𝒪[L]) x : L) = algebraMap K L (x : K) := by
  simpa using (IsValExtension.val_algebraMap (vK := vK.v) (vA := vL.v) x)

#check Ideal.map_le_iff_le_comap
theorem Ideal.map_maximalIdeal_le_maximalIdeal : Ideal.map (algebraMap ↥𝒪[K'] ↥𝒪[L]) (IsLocalRing.maximalIdeal ↥𝒪[K']) ≤ IsLocalRing.maximalIdeal ↥𝒪[L] := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  simp only [Ideal.mem_comap]
  rw [MaximalIdeal_iff_val_lt_one] at hx ⊢
  rw [coe_algbraMap_eq_algebraMap_coe]
  exact (IsValExtension.val_map_lt_one_iff (vR := vK'.v) (vA := vL.v) (x := (x : K'))).2 hx


variable [IsScalarTower 𝒪[K] 𝒪[K'] 𝒪[L]] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])] [CompleteSpace K'] in
theorem RamificationGroup_card_zero_comp_aux : (Nat.card G(K'/K)_[0] : ℝ) * (Nat.card G(L/K')_[0] : ℝ) = (Nat.card G(L/K)_[0] : ℝ) := by
  repeat rw [RamificationIdx_eq_card_of_inertia_group]
  norm_cast
  unfold LocalField.ramificationIdx IsLocalRing.ramificationIdx
  symm
  apply Ideal.ramificationIdx_algebra_tower (R := 𝒪[K]) (S := 𝒪[K']) (T := 𝒪[L]) (p := (IsLocalRing.maximalIdeal ↥𝒪[K])) (P := (IsLocalRing.maximalIdeal ↥𝒪[K'])) (Q := (IsLocalRing.maximalIdeal ↥𝒪[L]))
  exact Ideal_map_ne_bot K' L
  exact Ideal_map_ne_bot K L
  exact Ideal.map_maximalIdeal_le_maximalIdeal _ _

theorem phiDerivReal_integrableOn_section {k : ℤ} (hk : 0 ≤ k): IntegrableOn (phiDerivReal K L) (Set.Ioc (k : ℝ) (k + 1 : ℝ)) μ := by
  let c : ℝ := (Nat.card G(L/K)_[(k + 1)] : ℝ) / (Nat.card G(L/K)_[0] : ℝ)
  have hconst : IntegrableOn (fun _ : ℝ => c) (Set.Ioc (k : ℝ) (k + 1 : ℝ)) μ := by
    refine MeasureTheory.integrableOn_const (s := Set.Ioc (k : ℝ) (k + 1 : ℝ)) (μ := μ) (C := c) ?_
    dsimp [μ]
    exact measure_Ioc_lt_top.ne
  refine hconst.congr_fun ?_ measurableSet_Ioc
  intro a ha
  have ha' : ⌈a⌉ = k + 1 := by
    apply Int.ceil_eq_on_Ioc (k + 1) a ?_
    simpa [add_sub_cancel_right] using ha
  have hk1 : 0 ≤ k + 1 := by linarith
  unfold phiDerivReal c
  rw [ha', max_eq_right hk1]


theorem phiReal_eq_sum_card {u : ℝ} (hu : 0 ≤ u) : phiReal K L u = (1 / Nat.card G(L/K)_[0]) * ((∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), Nat.card G(L/K)_[x]) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(L/K)_[⌈u⌉])) := by
  sorry

theorem phiReal_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < phiReal K L x := by
  rw [phiReal_eq_sum_card K L (le_of_lt hx)]
  apply mul_pos
  · simp only [one_div, inv_pos, Nat.cast_pos, Nat.card_pos]
  · apply add_pos_of_nonneg_of_pos
    · apply Nat.cast_nonneg
    · apply mul_pos
      · rw [max_eq_right, Int.cast_sub, Int.cast_one, ← sub_add, sub_add_eq_add_sub]
        linarith [Int.ceil_lt_add_one x]
        apply Int.le_of_sub_one_lt
        simp only [zero_sub, Int.reduceNeg, neg_lt_sub_iff_lt_add, lt_add_iff_pos_right,
          Int.ceil_pos]
        exact hx
      · simp only [Nat.cast_pos, Nat.card_pos]

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] in
theorem phiReal_eq_phi {u : ℚ} (hu : 0 ≤ u) : phiReal K L u = phi K L u := by
  by_cases hu' : u = 0
  · simp only [hu', phi_zero_eq_zero, Rat.cast_zero, phiReal_zero_eq_zero]
  · rw [phiReal_eq_sum_card K L, phi_eq_sum_card]
    simp only [one_div, Rat.ceil_cast, Nat.cast_sum, Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_one, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_sum, Rat.cast_sub, Rat.cast_max, Rat.cast_zero, Rat.cast_intCast, Rat.cast_one]
    apply lt_of_le_of_ne hu
    exact fun a ↦ hu' (id (Eq.symm a))
    exact Rat.cast_nonneg.mpr hu

theorem phiReal_eq_self_of_le_zero {u : ℝ} (hu : u ≤ 0) : phiReal K L u = u := by
  unfold phiReal
  rw [integral_of_ge hu]
  rw [MeasureTheory.setIntegral_congr_fun (g := fun _ => (1 : ℝ)) measurableSet_Ioc]
  · rw [MeasureTheory.setIntegral_const]
    have hu' : 0 ≤ -u := by linarith
    simp [μ, MeasureTheory.Measure.real_def, Real.volume_Ioc, ENNReal.toReal_ofReal hu', hu]
  · intro x hx
    unfold phiDerivReal
    have hx0 : ⌈x⌉ ≤ 0 := by
      exact Int.ceil_le.2 (by simpa using (Set.mem_Ioc.1 hx).2)
    have hden : (Nat.card G(L/K)_[0] : ℝ) ≠ 0 := by
      exact ne_of_gt (Nat.cast_pos.2 Nat.card_pos)
    simp [max_eq_left hx0, hden]

set_option maxHeartbeats 0

theorem phiReal_sub_phiReal_le {u v : ℝ} (h : u ≤ v) (h' : 0 < u) : phiReal K L v - phiReal K L u ≤ (v - u) * phiDerivReal K L u := by
  by_cases hc : u = v
  · simp only [hc, sub_self, zero_mul]
    linarith
  · by_cases hceil : ⌈v⌉ = 1
    · have hceil' : ⌈u⌉ = 1 := by
        apply Int.ceil_eq_iff.mpr
        refine ⟨by simp only [Int.cast_one, sub_self, h'], le_trans h ?_⟩
        rw [← hceil]
        exact Int.le_ceil v
      rw [phiReal_eq_sum_card K L (le_of_lt h'), phiReal_eq_sum_card, phiDerivReal, ← mul_sub, one_div, inv_mul_eq_div, ← mul_div_assoc, div_le_div_iff_of_pos_right, ← sub_sub, add_sub_right_comm, add_sub_assoc, hceil, hceil', sub_self]
      simp only [sub_self, max_self, Int.cast_zero, sub_zero, zero_add, zero_le_one, max_eq_right, tsub_le_iff_right]
      ring_nf
      linarith
      simp only [Nat.cast_pos, Nat.card_pos]
      exact le_of_lt (lt_of_lt_of_le h' h)
    · by_cases hu : ⌈u⌉ = 1
      · rw [phiReal_eq_sum_card K L (le_of_lt h'), phiReal_eq_sum_card, phiDerivReal, ← mul_sub, one_div, inv_mul_eq_div, ← mul_div_assoc, div_le_div_iff_of_pos_right, ← sub_sub, add_sub_right_comm, add_sub_assoc, hu, sub_self]
        simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, max_self, Nat.cast_sum, CharP.cast_eq_zero, sub_zero, Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_one, zero_le_one, max_eq_right]
        rw [max_eq_right]
        calc
          _ ≤ ∑ x ∈ Finset.Icc 1 (⌈v⌉ - 1), (Nat.card ↥ G(L/K)_[1]) + ((v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]) - u * (Nat.card G(L/K)_[1])) := by
            simp only [add_le_add_iff_right, ← Nat.cast_sum, Nat.cast_le]
            apply Finset.sum_le_sum
            intro i hi
            apply Nat.card_mono
            exact Set.toFinite (G(L/K)_[1] : Set (L ≃ₐ[K] L))
            apply lowerRamificationGroup.antitone
            apply (Finset.mem_Icc.1 hi).1
          _ ≤ (⌈v⌉ - 1) * (Nat.card G(L/K)_[1]) + ((v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉]) - u * (Nat.card G(L/K)_[1])) := by
            simp only [Finset.sum_const, Int.card_Icc, sub_add_cancel, Int.pred_toNat, smul_eq_mul, Nat.cast_mul, add_le_add_iff_right, Nat.cast_pos, Nat.card_pos, mul_le_mul_right]
            have hvnonneg : 0 ≤ ⌈v⌉ := by
              apply Int.ceil_nonneg
              exact le_trans (le_of_lt h') h
            have hvpos : 0 < ⌈v⌉ := by
              have hvone : (1 : ℤ) ≤ ⌈v⌉ := Int.one_le_ceil_iff.mpr (lt_of_lt_of_le h' h)
              linarith
            rw [← Int.cast_natCast, Int.toNat_pred_coe_of_pos hvpos]
            simpa [Int.cast_sub]
          _ ≤ (⌈v⌉ - 1) * (Nat.card G(L/K)_[1]) + ((v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[1]) - u * (Nat.card G(L/K)_[1])) := by
            simp only [add_le_add_iff_left, tsub_le_iff_right, sub_add_cancel]
            have hcard : (Nat.card G(L/K)_[⌈v⌉] : ℝ) ≤ (Nat.card G(L/K)_[1] : ℝ) := by
              exact Nat.cast_le.2 <| by
                apply Nat.card_mono
                · exact Set.toFinite (G(L/K)_[1] : Set (L ≃ₐ[K] L))
                · apply lowerRamificationGroup.antitone
                  apply Int.one_le_ceil_iff.mpr
                  exact lt_of_lt_of_le h' h
            apply mul_le_mul_of_nonneg_left hcard
            linarith [Int.ceil_lt_add_one v]
          _ ≤ _ := by
            ring
            simp only [le_refl]
        rw [sub_nonneg, ← Int.cast_one, Int.cast_le]
        apply Int.one_le_ceil_iff.mpr
        apply lt_of_lt_of_le h' h
        rw [← Nat.cast_zero, Nat.cast_lt]
        apply Ramification_Group_card_pos K L (u := 0)
        apply le_of_lt (lt_of_lt_of_le h' h)
      · have h1 : Finset.Icc 1 (⌈v⌉ - 1) = Finset.Icc 1 (⌈u⌉ - 1) ∪ Finset.Icc ⌈u⌉ (⌈v⌉ - 1) := by
          nth_rw 2 [← sub_add_cancel ⌈u⌉ 1]
          rw [Finset.Icc_union_Icc_eq_Icc (a := 1) (b := (⌈u⌉ - 1)) (c := (⌈v⌉ - 1))]
          apply Int.le_of_sub_one_lt
          simp only [sub_self, sub_pos]
          apply lt_of_le_of_ne
          apply Int.one_le_ceil_iff.mpr h'
          exact fun a ↦ hu (id (Eq.symm a))
          simp only [tsub_le_iff_right, sub_add_cancel]
          exact Int.ceil_le_ceil h
        rw [phiReal_eq_sum_card K L (le_of_lt h'), phiReal_eq_sum_card, phiDerivReal, ← mul_sub, one_div, inv_mul_eq_div, ← mul_div_assoc, div_le_div_iff_of_pos_right, ← sub_sub, add_sub_right_comm, add_sub_assoc, h1, Finset.sum_union, Nat.cast_add, add_sub_cancel_left, max_eq_right, max_eq_right]
        calc
          _ ≤ ∑ x ∈ Finset.Icc ⌈u⌉ (⌈v⌉ - 1), Nat.card G(L/K)_[⌈u⌉] + ((v - (⌈v⌉ - 1)) * (Nat.card G(L/K)_[⌈v⌉] ) - (u - (⌈u⌉ - 1)) * (Nat.card G(L/K)_[⌈u⌉])) := by
            simp only [Int.cast_sub, Int.cast_one, add_le_add_iff_right, Nat.cast_le]
            apply Finset.sum_le_sum
            intro i hi
            apply Nat.card_mono
            exact Set.toFinite (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L))
            apply lowerRamificationGroup.antitone K L (Finset.mem_Icc.1 hi).1
          _ ≤ ∑ x ∈ Finset.Icc ⌈u⌉ (⌈v⌉ - 1), Nat.card G(L/K)_[⌈u⌉] + ((v - (⌈v⌉ - 1)) * (Nat.card ↥ G(L/K)_[⌈u⌉] ) - (u - (⌈u⌉ - 1)) * (Nat.card G(L/K)_[⌈u⌉])) := by
            simp only [add_le_add_iff_left, sub_eq_add_neg (b := (u - (↑⌈u⌉ - 1)) * ↑(Nat.card ↥ G(L/K)_[⌈u⌉] )), add_le_add_iff_right]
            have hcard : (Nat.card G(L/K)_[⌈v⌉] : ℝ) ≤ (Nat.card G(L/K)_[⌈u⌉] : ℝ) := by
              exact Nat.cast_le.2 <| by
                apply Nat.card_mono
                · exact Set.toFinite (G(L/K)_[⌈u⌉] : Set (L ≃ₐ[K] L))
                · apply lowerRamificationGroup.antitone K L
                  exact Int.ceil_le_ceil h
            have hfac : 0 ≤ v - (↑⌈v⌉ - 1) := by
              linarith [Int.ceil_lt_add_one v]
            exact mul_le_mul_of_nonneg_left hcard hfac
          _ ≤ _ := by
            simp only [Finset.sum_const, Int.card_Icc, sub_add_cancel, smul_eq_mul, Nat.cast_mul]
            rw [← Int.cast_natCast, Int.toNat_of_nonneg, ← sub_mul, ← add_mul, Int.cast_sub]
            have h1 : (↑⌈v⌉ - ↑⌈u⌉ + (v - (↑⌈v⌉ - 1) - (u - (↑⌈u⌉ - 1)))) = v - u := by ring
            rw [h1, max_eq_right]
            · exact_mod_cast (Int.ceil_nonneg (le_of_lt h'))
            · exact sub_nonneg.mpr (Int.ceil_le_ceil h)
        exact sub_nonneg.mpr (by exact_mod_cast (Int.one_le_ceil_iff.2 h'))
        exact sub_nonneg.mpr (by exact_mod_cast (Int.one_le_ceil_iff.2 (lt_of_lt_of_le h' h)))
        apply Disjoint.symm ((fun {α} {s t} ↦ Finset.disjoint_left.mpr) ?_)
        intro a ha
        simp only [Finset.mem_Icc] at *
        push_neg
        intro ha'
        apply lt_of_lt_of_le (by linarith) ha.1
        simp only [Nat.cast_pos, Nat.card_pos]
        exact le_of_lt (lt_of_lt_of_le h' h)

theorem le_phiReal_sub_phiReal {u v : ℝ} (h : u ≤ v) (hu : 0 < u) : (v - u) * phiDerivReal K L v ≤ phiReal K L v - phiReal K L u := by
  sorry

theorem phiReal_StrictMono : StrictMono (phiReal K L) := by
  intro a b hab
  by_cases hb : 0 < b
  · by_cases ha : 0 < a
    · apply lt_of_sub_pos
      apply lt_of_lt_of_le _ (le_phiReal_sub_phiReal K L (le_of_lt hab) ha)
      apply mul_pos (by linarith [hab]) (phiDerivReal_pos K L)
    · push_neg at ha
      rw [phiReal_eq_self_of_le_zero K L ha]
      apply lt_of_le_of_lt ha (phiReal_pos_of_pos K L hb)
  · push_neg at hb
    obtain ha' := lt_of_lt_of_le hab hb
    rw [phiReal_eq_self_of_le_zero K L (le_of_lt ha'), phiReal_eq_self_of_le_zero K L hb]
    exact hab

theorem phiReal_injective : Function.Injective (phiReal K L) := by
  intro a1 a2 h
  contrapose! h
  by_cases h1 : a1 > a2
  · apply ne_of_gt (phiReal_StrictMono K L h1)
  · push_neg at *
    apply ne_of_lt (phiReal_StrictMono K L (lt_of_le_of_ne h1 h))

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] in
theorem phiReal_phi_ceil_eq_aux {u : ℝ} (hu : 0 ≤ u) : ∃ u' : ℚ, ⌈u⌉ = ⌈u'⌉ ∧ ⌈phiReal K L u⌉ = ⌈phi K L u'⌉ := by
  sorry

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [CompleteSpace K'] [CompleteSpace K] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] in
theorem herbrand_Real (u : ℝ) (hu : 0 ≤ u)  : G(L/K)_[⌈u⌉].map (AlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phiReal K' L u⌉] := by
  obtain ⟨u', hu'1, hu'2⟩ := phiReal_phi_ceil_eq_aux K' L (u := u) hu
  rw [hu'1, hu'2]
  apply herbrand (K := K) (K' := K') (L := L) u'

variable [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] [Algebra.IsSeparable K' L] [CompleteSpace K'] [CompleteSpace K] [Normal K' L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] in
theorem phiDerivReal_comp {u : ℝ} (hu : 0 ≤ u) : (phiDerivReal K' L u) * phiDerivReal K K' (phiReal K' L u) = phiDerivReal K L u := by
  unfold phiDerivReal
  rw [← mul_div_mul_comm]
  congr
  · rw [← Int.ceil_intCast (R := ℝ) (z := (max 0 ⌈u⌉)), ← RamificationGroup_card_comp_aux K K' L ?_, mul_comm]
    congr 1
    rw [max_eq_right, ← herbrand_Real K K' L _ hu, max_eq_right]
    simp only [Subgroup.mem_map, Int.ceil_intCast]
    apply Int.ceil_nonneg hu
    apply Int.ceil_nonneg
    apply phiReal_nonneg K' L hu
    simp only [Int.cast_max, Int.cast_zero, le_max_iff, le_refl, Int.cast_nonneg, true_or]
  · rw [← Int.ceil_zero (R := ℝ), ← RamificationGroup_card_comp_aux K K' L (by linarith), mul_comm]
    congr 1
    rw [herbrand_Real K K' L _ (by linarith), phiReal_zero_eq_zero]
