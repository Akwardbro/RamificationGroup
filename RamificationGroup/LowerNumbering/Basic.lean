import RamificationGroup.Valued.Hom.Lift
import RamificationGroup.ForMathlib.Algebra.Algebra.Tower
import Mathlib.NumberTheory.LocalField.Basic
import RamificationGroup.ForMathlib.Algebra.Algebra.PowerBasis
import RamificationGroup.Valued.AlgebraicInstances
import RamificationGroup.Valuation.Extension
import RamificationGroup.Valued.Hom.ValExtension
import RamificationGroup.Valued.AlgebraicInstances

/-
# Lower Numbering Ramification Group

## Main Definitions

## Main Theorem

## TODO

prove theorems using Bichang's preparation in section SeparatedExhausive

rename theorems, many theorem should be named as LowerRamificationGroup.xxx, not lowerRamificationGroup_xxx

-/

open DiscreteValuation Valued Valuation

section def_lower_rami_grp

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [vS : Valued S ℤₘ₀] [Algebra R S]

def lowerRamificationGroup (u : ℤ) : Subgroup (S ≃ₐ[R] S) where
    carrier := {s | s ∈ decompositionGroup R S ∧ ∀ x : vS.v.integer, Valued.v (s x - x) ≤ .coe (.ofAdd (- u - 1))}
    mul_mem' {a} {b} ha hb := by
      constructor
      · exact mul_mem ha.1 hb.1
      · intro x
        calc
          _ = v (a (b x) - x) := rfl
          _ = v ((a (b x) - b x) + (b x - x)) := by congr; simp
          _ ≤ max (v (a (b x) - b x)) (v (b x - x)) := Valuation.map_add _ _ _
          _ ≤ max (.coe (.ofAdd (- u - 1))) (.coe (.ofAdd (- u - 1))) := by
            apply max_le_max
            · exact ha.2 ⟨b x, (val_map_le_one_iff hb.1 x).mpr x.2⟩
            · exact hb.2 x
          _ = _ := max_self _
    one_mem' := by
      constructor
      · exact one_mem _
      · simp only [AlgEquiv.one_apply, sub_self, _root_.map_zero, ofAdd_sub, ofAdd_neg, zero_le',
        Subtype.forall, implies_true, forall_const]
    inv_mem' {s} hs := by
      constructor
      · exact inv_mem hs.1
      intro a
      calc
      _ = v (s⁻¹ a - a) := rfl
      _ = v ( s⁻¹ a - s (s⁻¹ a) ) := by
        congr 1
        simp only [sub_right_inj]
        exact (EquivLike.apply_inv_apply s ↑a).symm
      _ = v ( s (s⁻¹ a) - s ⁻¹ a) := by
        rw [← Valuation.map_neg]
        congr
        simp only [neg_sub]
      _ ≤ _ := hs.2 ⟨s⁻¹ a, (val_map_le_one_iff (f := (s.symm : S →+* S))
        (Valuation.IsEquiv_comap_symm hs.1) a.1).mpr a.2⟩

scoped [Valued] notation:max " G(" S:max "/" R:max ")_[" u:max "] " => lowerRamificationGroup R S u

theorem lowerRamificationGroup.antitone : Antitone (lowerRamificationGroup R S) := by
  intro a b hab s hs
  constructor
  · exact hs.1
  · intro y
    apply le_trans (hs.2 y)
    simp only [ofAdd_sub, ofAdd_neg, WithZero.coe_le_coe, div_le_iff_le_mul, div_mul_cancel,
      inv_le_inv_iff, Multiplicative.ofAdd_le]
    exact hab

end def_lower_rami_grp

instance Valuation.instNonemptyToValuation {R Γ₀: Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀): Nonempty v.integer := Zero.instNonempty

section autCongr

/--
Shouldn't be here.-/
noncomputable def restrict_mulEquiv_to_subgroup {G : Type*} {G' : Type*} [Group G] [Group G'] (f : G ≃* G')
{H : Subgroup G} {H' : Subgroup G'}
(hf : ∀ x : G, x ∈ H ↔ f x ∈ H') :
H ≃* H' := by
  let f_H := Subgroup.equivMapOfInjective (G := G) (N := G') H f f.injective
  have : H' = Subgroup.map f H := by
    ext y
    rw [Subgroup.mem_map]
    let ⟨x, hx⟩ := f.surjective y
    rw [← hx, ← hf x]
    simp only [MonoidHom.coe_coe, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  rw [this]
  apply f_H

variable {R S S': Type*} {ΓR : outParam Type*} [CommRing R] [Ring S] [Ring S'] [vS : Valued S ℤₘ₀] [vS : Valued S' ℤₘ₀] [Algebra R S] [Algebra R S']


/-- if f is a R-algebra isom of S and S', f preserves the valuation, then s ∈ G(S/R)_[u] if and only if F s ∈ G(S'/R)_[u], where F : Gal(S/R) → Gal(S'/R), F(σ)(s') = σ(f⁻¹(s')). -/
theorem autCongr_mem_lowerRamificationGroup_iff {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (s : S ≃ₐ[R] S) (u : ℤ) : s ∈ G(S/R)_[u] ↔ (AlgEquiv.autCongr f s : S' ≃ₐ[R] S') ∈ G(S'/R)_[u] := by
  have hf' : ∀ a : S', v (f.symm a) = v a := by
    intro a
    rw [hf (f.symm a), AlgEquiv.apply_symm_apply]
  simp only [lowerRamificationGroup, ofAdd_sub, ofAdd_neg, Subtype.forall, Subgroup.mem_mk,
    Set.mem_setOf_eq, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
  constructor <;>
  intro h <;>
  constructor <;>
  intro a ha
  constructor <;> intro h'
  · simp only [comap_apply, RingHom.coe_coe, AlgEquiv.trans_apply]
    rw [← hf _, ← hf _]
    apply (h.1 (f.symm a) (f.symm ha)).1
    rw [hf' _, hf' _]
    exact h'
  · rw [← hf' _, ← hf' _]
    apply (h.1 (f.symm a) (f.symm ha)).2
    simp only [comap_apply, RingHom.coe_coe]
    rw [hf _, hf _]
    exact h'
   -- need theorem/def of lift of f to integer is isom
  · nth_rw 2 [← AlgEquiv.symm_apply_apply f.symm a]
    simp only [AlgEquiv.symm_symm]
    have hmem : f.symm a ∈ v.integer := by
      apply (mem_integer_iff _ _).2
      rw [hf' _]
      exact ha
    have hs' := h.2 (f.symm a) hmem
    calc
      v ((f.symm.trans (s.trans f)) a - f (f.symm a)) = v (f (s (f.symm a) - f.symm a)) := by
        simp only [AlgEquiv.trans_apply, _root_.map_sub]
      _ = v (s (f.symm a) - f.symm a) := by
        simpa using (hf (s (f.symm a) - f.symm a)).symm
      _ ≤ _ := by simpa using hs'
  · constructor <;> intro hs'
    · simp only [comap_apply, RingHom.coe_coe]
      rw [hf _, hf _, ← AlgEquiv.symm_apply_apply f a, ← AlgEquiv.symm_apply_apply f ha]
      apply (h.1 (f a) (f ha)).1
      rw [← hf _, ← hf _]
      exact hs'
    · simp only [comap_apply, RingHom.coe_coe, hf _, hf _] at hs'
      rw [← AlgEquiv.symm_apply_apply f a, ← AlgEquiv.symm_apply_apply f ha] at hs'
      rw [hf _, hf _]
      apply (h.1 (f a) (f ha)).2 hs'
  · rw [hf _, _root_.map_sub, ← AlgEquiv.symm_apply_apply f a]
    nth_rw 2 [AlgEquiv.symm_apply_apply]
    apply h.2
    apply (mem_integer_iff _ _).2
    rw [← hf _]
    exact ha

/-- the `u`-th lower ramification groups of two isomorphic ring extensions are isomorphic for all `u ∈ ℤ`. -/
noncomputable def lowerRamificationGroup_equiv_of_ring_equiv {f : S ≃ₐ[R] S'} (hf : ∀ a : S, v a = v (f a)) (u : ℤ) : G(S/R)_[u] ≃* G(S'/R)_[u] := by
  apply restrict_mulEquiv_to_subgroup f.autCongr
  apply fun s ↦ autCongr_mem_lowerRamificationGroup_iff hf s u

end autCongr

section WithBot
-- this should be put into a suitable place, Also add `WithOne`? `WithTop`, `WithBot`, `WithOne`, `Multiplicative`, `Additive`
open Classical
-- there is no `ConditionallyCompleteLinearOrderTop` in mathlib ...
-- # The definition of `WithTop.instInfSet` have to be changed （done in latest version）
noncomputable instance {α} [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot (WithBot α) where
  toConditionallyCompleteLinearOrder := {
    toConditionallyCompleteLattice := WithBot.conditionallyCompleteLattice
    le_total := WithBot.linearOrder.le_total
    toDecidableLE := inferInstance
    csSup_of_not_bddAbove := by
      intro s h
      rw [WithBot.sSup_empty]
      change (if s ⊆ ({⊥} : Set (WithBot α)) ∨ ¬BddAbove s then (⊥ : WithBot α)
        else ↑(sSup ((fun a : α ↦ (↑a : WithBot α)) ⁻¹' s))) = ⊥
      exact if_pos (Or.inr h)
    csInf_of_not_bddBelow := by
      intro s h
      exfalso
      exact h (OrderBot.bddBelow s) }
  toOrderBot := inferInstance
  csSup_empty := by
    simp only [WithBot.sSup_empty]

noncomputable instance {α} [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot (WithZero α) := inferInstanceAs (ConditionallyCompleteLinearOrderBot (WithBot α))

instance {α} [Add α] [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder (Multiplicative α) := inferInstanceAs (ConditionallyCompleteLinearOrder α)

-- noncomputable instance : ConditionallyCompleteLinearOrderBot ℤₘ₀ := inferInstanceAs (ConditionallyCompleteLinearOrderBot (WithZero ℤ))

end WithBot

section lowerIndex

variable (R S : Type*) [CommRing R] [Ring S] [vS : Valued S ℤₘ₀] [Algebra R S]


open Classical
-- 0 if lower than 0
-- we define the lower index of ramification groups of ring extension S/R i_[S/R] : Gal(S/R) → ℕ∞ (ℕ∞ is somehow conflict with ℤₘ₀, it causes some extra coercion), i_[S/R] s = sup_{x} v (s (x) - x)
noncomputable def AlgEquiv.lowerIndex (s : S ≃ₐ[R] S) : ℕ∞ :=
  if h : ⨆ x : vS.v.integer, vS.v (s x - x) = 0 then ⊤
  else (- Multiplicative.toAdd (WithZero.unzero h)).toNat

scoped [Valued] notation:max " i_[" S:max "/" R:max "]" => AlgEquiv.lowerIndex R S


-- translate the type of lowerIndex from ℕ∞ to ℚ
  noncomputable def AlgEquiv.truncatedLowerIndex (u : ℚ) (s : (S ≃ₐ[R] S)) : ℚ :=
    if h : i_[S/R] s = ⊤ then u
    else min u ((i_[S/R] s).untop h)

scoped [Valued] notation:max " i_[" L:max "/" K:max "]ₜ" => AlgEquiv.truncatedLowerIndex K L

section lowerIndex_inequality

variable {R S}

/-- One of `val_map_sub_le_one` and `sub_self_mem_integer` should be thrown away.-/


theorem sub_self_mem_integer {s : S ≃ₐ[R] S} (hs' : s ∈ decompositionGroup R S)
  (x : vS.v.integer) :
    s x - x ∈ vS.v.integer := by
  apply Subring.sub_mem
  ·
    rw [mem_integer_iff, val_map_le_one_iff hs']; exact x.2
  · exact x.2

/-- One of `val_map_sub_le_one` and `sub_self_mem_integer` should be thrown away.-/
theorem val_map_sub_le_one {s : S ≃ₐ[R] S} (hs' : s ∈ decompositionGroup R S)
  (x : vS.v.integer) :
    v (s x - x) ≤ 1 := sub_self_mem_integer hs' x

--if sup_{x ∈ S| v (x) ≤ 1} v (s (x) - x) ≠ ∞, sup_{x ∈ S| v (x) ≤ 1} v (s (x) - x) > 0
--is trivil in math, but is important in Lean and our project.
theorem toAdd_iSup_val_map_sub_le_zero_of_ne_zero {s : S ≃ₐ[R] S} (hs' : s ∈ decompositionGroup R S)
  (h : ⨆ x : vS.v.integer, vS.v (s x - x) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) ≤ 0 := by
  change (WithZero.unzero h) ≤ 1
  suffices ⨆ x : vS.v.integer, vS.v (s x - x) ≤ 1 from by
    rw [← WithZero.coe_le_coe, WithZero.coe_unzero h]
    exact this
  apply ciSup_le <| val_map_sub_le_one hs'

section adjoin_singleton

variable {K L : Type*} [Field K] [Field L]
[vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [Algebra K L] [IsValExtension vK.v vL.v]

/-- Should be strenthened to ` > 0`-/--??-/
--suppose the generator of 𝒪[L] as a 𝒪[K]-algebra exists.
theorem decomp_val_map_generator_sub_ne_zero {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤)
  {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) (hs : s ≠ .refl) :
    vL.v (s gen - gen) ≠ 0 := by
  by_contra h
  rw [zero_iff, sub_eq_zero] at h
  apply hs
  rw [elem_decompositionGroup_eq_iff_ValuationSubring' hs' (refl_mem_decompositionGroup K L)]
  apply Algebra.algHomClass_ext_generator hgen
  ext
  rw [DecompositionGroup.restrictValuationSubring_apply' hs',
    DecompositionGroup.restrictValuationSubring_apply' (refl_mem_decompositionGroup K L),
    h, AlgEquiv.coe_refl, id_eq]

open Polynomial in
theorem decomp_val_map_sub_le_generator {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) (x : 𝒪[L]) : v (s x - x) ≤ v (s gen - gen) := by
  by_cases hs : s = .refl
  · subst hs
    simp only [AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, le_refl]
  rcases Algebra.exists_eq_aeval_generator hgen x with ⟨f, hf⟩
  subst hf
  rcases taylor_order_zero_apply_aeval f gen ((DecompositionGroup.restrictValuationSubring' hs') gen - gen) with ⟨b, hb⟩
  rw [add_sub_cancel, add_comm, ← sub_eq_iff_eq_add, aeval_algHom_apply, Subtype.ext_iff] at hb
  simp only [AddSubgroupClass.coe_sub, DecompositionGroup.restrictValuationSubring_apply' hs', Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subring.coe_toSubsemiring] at hb
  rw [hb]
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub,DecompositionGroup.restrictValuationSubring_apply', _root_.map_mul]
  nth_rw 2 [← mul_one (v (s gen - gen))]
  exact mul_le_mul_of_nonneg_left b.2 (WithZero.zero_le (v (s ↑gen - ↑gen)))

--sup_{x ∈ S | v x ≤ 1} v (s (x) - x) = v (s gen - gen)
theorem decomp_iSup_val_map_sub_eq_generator {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) :
  ⨆ x : vL.v.integer, v (s x - x) = v (s gen - gen) := by
  apply le_antisymm
  · letI : Nonempty 𝒪[L] := inferInstanceAs (Nonempty vL.v.integer)
    apply ciSup_le <| decomp_val_map_sub_le_generator hgen hs'
  · apply le_ciSup (f := fun (x : 𝒪[L]) ↦ v (s x - x)) _ gen
    use v (s gen - gen)
    intro y hy
    simp only [Set.mem_range, Subtype.exists, exists_prop] at hy
    rcases hy with ⟨a, ha⟩
    rw [← ha.2, show s a - a = s (⟨a, ha.1⟩ : 𝒪[L]) - (⟨a, ha.1⟩ : 𝒪[L]) by rfl]
    apply decomp_val_map_sub_le_generator hgen hs'

end adjoin_singleton

end lowerIndex_inequality

end lowerIndex

section ScalarTower

variable {R : Type*} {R' S: Type*} {ΓR ΓS ΓA ΓB : outParam Type*} [CommRing R] [CommRing R'] [Ring S]
[vS : Valued S ℤₘ₀]
[Algebra R S] [Algebra R R'] [Algebra R' S] [IsScalarTower R R' S]

@[simp]
theorem lowerIndex_refl : (i_[S/R] .refl) = ⊤ := by
  simp only [AlgEquiv.lowerIndex, AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, ciSup_const,
    ↓reduceDIte]

@[simp]
theorem truncatedLowerIndex_refl (u : ℚ) : AlgEquiv.truncatedLowerIndex R S u .refl = u := by
  simp only [AlgEquiv.truncatedLowerIndex, lowerIndex_refl, ↓reduceDIte]

section lowerIndex_inequality

section K_not_field

variable {K K' L : Type*} {ΓK ΓK' : outParam Type*} [CommRing K] [Field K'] [Field L] [LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓK'] [vL : Valued L ℤₘ₀] [Algebra K L]
[Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]

/-- Another version where `𝒪[L] is finite over 𝒪[K]` -/
theorem lowerIndex_ne_one {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) (hs : s ≠ .refl) : i_[L/K] s ≠ ⊤ := by
  intro heq
  simp only [AlgEquiv.lowerIndex, AddSubgroupClass.coe_sub,
    dite_eq_left_iff, ENat.coe_ne_top, imp_false, not_not] at heq
  have hL : ∀ x : vL.v.integer, s x = x := by
    intro x
    have hxle : v (s x - x) ≤ 0 := by
      refine (ciSup_le_iff' ?_).mp (le_of_eq heq) x
      use 1
      intro a ha
      rcases ha with ⟨y, hy⟩
      rw [← hy]
      exact sub_self_mem_integer hs' _
    have hxeq : v (s x - x) = 0 := le_antisymm hxle (WithZero.zero_le _)
    exact sub_eq_zero.mp ((Valuation.zero_iff vL.v).1 hxeq)
  apply hs
  ext x
  rcases ValuationSubring.mem_or_inv_mem vL.v.valuationSubring x with h | h
  · exact hL ⟨x, h⟩
  · calc
    _ = (s x⁻¹)⁻¹ := by simp only [inv_inv, map_inv₀]
    _ = _ := by rw [hL ⟨x⁻¹, h⟩, inv_inv, AlgEquiv.coe_refl, id_eq]

@[simp]
theorem lowerIndex_eq_top_iff_eq_refl {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) : i_[L/K] s = ⊤ ↔ s = .refl := by
  constructor <;> intro h
  · contrapose! h
    apply lowerIndex_ne_one hs' h
  · simp only [h, lowerIndex_refl]

theorem iSup_val_map_sub_eq_zero_iff_eq_refl {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) :
  ⨆ x : vL.v.integer, vL.v (s x - x) = 0 ↔ s = .refl := by
  rw [← lowerIndex_eq_top_iff_eq_refl]
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AlgEquiv.lowerIndex, dite_eq_left_iff, ENat.coe_ne_top, imp_false, Decidable.not_not]
  exact hs'

end K_not_field

--K_is_Valued_field
section K_is_field

variable {K L : Type*} [Field K] [Field L]
[vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [Algebra K L] [IsValExtension vK.v vL.v]

omit [IsValExtension vK.v vL.v] vK in
theorem mem_lowerRamificationGroup_of_le_neg_one {s : L ≃ₐ[K] L} (hs : s ∈ decompositionGroup K L) {u : ℤ} (hu : u ≤ -1) : s ∈ G(L/K)_[u] := by
  unfold lowerRamificationGroup
  simp only [ofAdd_sub, ofAdd_neg, Subtype.forall, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · exact hs
  · intro a ha
    apply le_trans (val_map_sub_le_one hs ⟨a, ha⟩)
    change (1 : ℤₘ₀) ≤ ↑(Multiplicative.ofAdd (-u - 1))
    exact WithZero.coe_le_coe.mpr <| (Multiplicative.ofAdd_le).mpr (by linarith [hu])

-- the type of `n` should be changed
-- instead, change when use this theorem
open Multiplicative in
theorem mem_lowerRamificationGroup_iff_of_generator
  {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤)
  {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) (n : ℕ) :
    s ∈ G(L/K)_[n] ↔ n + 1 ≤ i_[L/K] s := by
  simp only [lowerRamificationGroup, Subtype.forall, Subgroup.mem_mk,
    Set.mem_setOf_eq, AlgEquiv.lowerIndex]
  by_cases hrefl : s = .refl
  · subst hrefl
    constructor
    · intro _
      simp only [AlgEquiv.lowerIndex, AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, ciSup_const,
        ↓reduceDIte, le_top]
    · intro _
      refine ⟨refl_mem_decompositionGroup K L, ?_⟩
      intro a ha
      simp only [AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, ofAdd_sub, ofAdd_neg, zero_le']
  · have hne0 : ¬ ⨆ x : vL.v.integer, vL.v (s x - x) = 0 := by
      rw [iSup_val_map_sub_eq_zero_iff_eq_refl hs']; exact hrefl
    constructor
    · intro hs_mem
      rcases hs_mem with ⟨_, hs_bound⟩
      have hsup :
          ⨆ x : vL.v.integer, vL.v (s x - x) ≤ (↑(Multiplicative.ofAdd (-(n + 1 : ℤ))) : ℤₘ₀) := by
        apply ciSup_le
        intro x
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, neg_add'] using hs_bound x.1 x.2
      have hunzero_le : WithZero.unzero hne0 ≤ Multiplicative.ofAdd (-(n + 1 : ℤ)) := by
        rw [← WithZero.coe_le_coe, WithZero.coe_unzero hne0]
        exact hsup
      have htoAdd : Multiplicative.toAdd (WithZero.unzero hne0) ≤ -(n + 1 : ℤ) := by
        exact Multiplicative.toAdd_le.mp hunzero_le
      have hznonneg : 0 ≤ -Multiplicative.toAdd (WithZero.unzero hne0) := by
        exact neg_nonneg.mpr (toAdd_iSup_val_map_sub_le_zero_of_ne_zero hs' hne0)
      have hz : (n + 1 : ℤ) ≤ -Multiplicative.toAdd (WithZero.unzero hne0) := by
        linarith [htoAdd]
      have hnat : n + 1 ≤ (-Multiplicative.toAdd (WithZero.unzero hne0)).toNat :=
        (Int.le_toNat hznonneg).2 hz
      simp only [hne0, ↓reduceDIte, ge_iff_le]
      exact WithTop.coe_le_coe.mpr hnat
    · intro h
      have hnat : n + 1 ≤ (-Multiplicative.toAdd (WithZero.unzero hne0)).toNat := by
        have h' : (↑(n + 1) : ℕ∞) ≤ ↑((-Multiplicative.toAdd (WithZero.unzero hne0)).toNat) := by
          simpa only [hne0, AlgEquiv.lowerIndex, ↓reduceDIte, ge_iff_le] using h
        exact WithTop.coe_le_coe.mp h'
      have hznonneg : 0 ≤ -Multiplicative.toAdd (WithZero.unzero hne0) := by
        exact neg_nonneg.mpr (toAdd_iSup_val_map_sub_le_zero_of_ne_zero hs' hne0)
      have hz : (n + 1 : ℤ) ≤ -Multiplicative.toAdd (WithZero.unzero hne0) :=
        (Int.le_toNat hznonneg).1 hnat
      have htoAdd : Multiplicative.toAdd (WithZero.unzero hne0) ≤ -(n + 1 : ℤ) := by
        linarith [hz]
      have hunzero_le : WithZero.unzero hne0 ≤ Multiplicative.ofAdd (-(n + 1 : ℤ)) := by
        exact (Multiplicative.toAdd_le).2 htoAdd
      have hsup :
          ⨆ x : vL.v.integer, vL.v (s x - x) ≤ (↑(Multiplicative.ofAdd (-(n + 1 : ℤ))) : ℤₘ₀) := by
        have hsup' :
            (↑(WithZero.unzero hne0) : ℤₘ₀) ≤ (↑(Multiplicative.ofAdd (-(n + 1 : ℤ))) : ℤₘ₀) :=
          WithZero.coe_le_coe.mpr hunzero_le
        simpa [WithZero.coe_unzero hne0] using hsup'
      refine ⟨hs', ?_⟩
      intro x hx
      have hbdd : BddAbove (Set.range fun x : vL.v.integer ↦ v (s x - x)) := by
        refine ⟨1, ?_⟩
        rintro y ⟨z, rfl⟩
        exact val_map_sub_le_one hs' z
      have hxle :
          v (s x - x) ≤ (↑(Multiplicative.ofAdd (-(n + 1 : ℤ))) : ℤₘ₀) :=
        le_trans (le_ciSup (f := fun (x : vL.v.integer) ↦ v (s x - x)) hbdd ⟨x, hx⟩) hsup
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, neg_add'] using hxle


theorem mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one {s : L ≃ₐ[K] L} (hs' : s ∈ decompositionGroup K L) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {u r : ℚ} (h : u ≤ i_[L/K]ₜ r s - 1) : s ∈ G(L/K)_[⌈u⌉] := by
  unfold AlgEquiv.truncatedLowerIndex at h
  by_cases hu : u ≤ -1
  · apply mem_lowerRamificationGroup_of_le_neg_one hs'
    exact Int.ceil_le.mpr hu
  · push_neg at hu
    have hu' : ⌈u⌉.toNat = ⌈u⌉ := by
      apply Int.toNat_of_nonneg
      apply Int.le_ceil_iff.2
      simp only [Int.cast_zero, zero_sub, hu]
    by_cases hs : i_[L/K] s = ⊤
    · simp [hs] at h
      --maybe there is a better way
      have : (⌈u⌉.toNat + 1) ≤ i_[L/K] s := by simp [hs]
      convert (mem_lowerRamificationGroup_iff_of_generator hgen hs' ⌈u⌉.toNat).2 this
      rw [hu']
    · simp [hs] at h
      have : (⌈u⌉.toNat + 1) ≤ i_[L/K] s := by
        have h' : u + 1 ≤ min r ↑(WithTop.untop (i_[L/K] s) hs) := by linarith [h]
        rw [← WithTop.coe_untop (i_[L/K] s) hs]
        convert (le_min_iff.1 h').right
        constructor <;> intro hle
        · -- there might be a better way, it's too long :(
          have : u + 1 ≤ ⌈u⌉.toNat + 1 := by
            simp only [add_le_add_iff_right]
            apply le_trans (Int.le_ceil u)
            rw [← Int.cast_natCast]
            simp only [Int.ofNat_toNat, Int.cast_max, Int.cast_zero, le_max_iff, le_refl, Int.cast_nonpos, true_or]
          simp only [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add] at hle
          apply WithTop.coe_le_coe.1 at hle
          apply le_trans this
          simp only [← Nat.cast_one (R := ℚ), ← Nat.cast_add]
          norm_cast
        · simp only [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add]
          apply WithTop.coe_le_coe.2
          simp only [Nat.cast_add, Nat.cast_id, Nat.cast_one]
          apply Int.ceil_le.2 at hle
          rw [Int.ceil_add_one, ← hu'] at hle
          exact Int.ofNat_le.mp hle
      convert (mem_lowerRamificationGroup_iff_of_generator hgen hs' ⌈u⌉.toNat).2 this
      exact Eq.symm hu'

variable [IsDiscrete vK.v] [IsDiscrete vL.v] [CompleteSpace K] [FiniteDimensional K L]


theorem le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup (s : L ≃ₐ[K] L) (u : ℚ) (r : ℚ) (h : u + 1 ≤ r) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : u ≤ i_[L/K]ₜ r s - 1 ↔ s ∈ G(L/K)_[⌈u⌉] := by
  by_cases hu : u ≤ -1
  · constructor <;> intro hu'
    · apply mem_lowerRamificationGroup_of_le_neg_one
      rw [decompositionGroup_eq_top]
      apply Subgroup.mem_top
      apply Int.ceil_le.2
      simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one]
      apply hu
    · unfold AlgEquiv.truncatedLowerIndex
      by_cases hc : i_[L/K] s = ⊤
      · simp only [hc, ↓reduceDIte]
        linarith
      · simp only [hc, ↓reduceDIte]
        by_cases hr : r ≤ (WithTop.untop (i_[L/K] s) hc)
        · rw [min_eq_left hr]
          linarith
        · push_neg at hr
          rw [min_eq_right (le_of_lt hr)]
          have : 0 ≤ ((WithTop.untop (i_[L/K] s) hc : ℕ) : ℚ) := Nat.cast_nonneg' (WithTop.untop ( i_[L/K] s) hc)
          linarith
  · push_neg at hu
    have hu' : ⌈u⌉.toNat = ⌈u⌉ := by
      apply Int.toNat_of_nonneg
      apply Int.le_ceil_iff.2
      simp only [Int.cast_zero, zero_sub, hu]
    constructor
    · apply mem_lowerRamificationGroup_of_le_truncatedLowerIndex_sub_one _ hgen
      rw [decompositionGroup_eq_top]
      apply Subgroup.mem_top
    · intro hs
      have h1 : (⌈u⌉.toNat + 1) ≤ i_[L/K] s := by
        apply (mem_lowerRamificationGroup_iff_of_generator hgen ?_ ⌈u⌉.toNat).1
        --the type of N and Z make some truble
        rw [hu']
        exact hs
        rw [decompositionGroup_eq_top]
        apply Subgroup.mem_top
      unfold AlgEquiv.truncatedLowerIndex
      by_cases hc : i_[L/K] s = ⊤
      · simp [hc]
        linarith [h]
      · simp [hc]
        have hle : u + 1 ≤ min r ↑(WithTop.untop ( i_[L/K] s) (of_eq_false (eq_false hc) : ¬ i_[L/K] s = ⊤)) := by
          apply le_min_iff.2
          constructor
          · exact h
          · have hle' : u + 1 ≤ ⌈u⌉.toNat + 1 := by
              simp only [add_le_add_iff_right]
              apply le_trans (Int.le_ceil u)
              rw [← Int.cast_natCast]
              simp only [Int.ofNat_toNat, Int.cast_max, Int.cast_zero, le_max_iff, le_refl, Int.cast_nonpos, true_or]
            apply le_trans hle'
            rw [← Nat.cast_one, ← Nat.cast_add]
            apply Nat.mono_cast
            exact (WithTop.le_untop_iff (of_eq_false (eq_false hc))).mpr h1
        linarith [hle]

end K_is_field

end lowerIndex_inequality
--independent of the existence of the generator of ring ext.
@[simp]
theorem lowerIndex_restrictScalars (s : S ≃ₐ[R'] S) : i_[S/R] (s.restrictScalars R) =  i_[S/R'] s := rfl

@[simp]
theorem truncatedLowerIndex_restrictScalars (u : ℚ) (s : S ≃ₐ[R'] S) : i_[S/R]ₜ u (s.restrictScalars R) = i_[S/R']ₜ u s := rfl

@[simp]
theorem lowerRamificationGroup_restrictScalars (u : ℤ) : G(S/R)_[u].comap (AlgEquiv.restrictScalarsHom R) = G(S/R')_[u] := rfl

end ScalarTower

section ExhausiveSeperated

section lower_eq_decomp

variable {R : Type*} {R' S: Type*} {ΓR ΓS ΓA ΓB : outParam Type*} [CommRing R] [CommRing R'] [Ring S]
[vS : Valued S ℤₘ₀] [Algebra R S] [Algebra R R'] [Algebra R' S] [IsScalarTower R R' S]

theorem lowerRamificationGroup_eq_decompositionGroup {u : ℤ} (h : u ≤ -1) :
G(S/R)_[u] = decompositionGroup R S := by
  ext s
  constructor
  · intro hs
    exact hs.1
  · intro hs
    refine ⟨hs, ?_⟩
    intro a
    calc
      _ ≤ max (v (s (a : S))) (v (a : S)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((val_map_le_one_iff hs a).mpr a.2) a.2
      _ ≤ _ := by
        show (.coe (0 : ℤ) : ℤₘ₀) ≤ .coe ((- u - 1) : ℤ)
        norm_cast
        show (0 : ℤ) ≤ - u - 1
        linarith

end lower_eq_decomp

section eq_top

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [Algebra K L] [FiniteDimensional K L]

theorem lowerRamificationGroup_eq_top [IsValExtension vK.v vL.v] [CompleteSpace K] {u : ℤ} (h : u ≤ -1) : G(L/K)_[u] = ⊤ := by
  rw [lowerRamificationGroup_eq_decompositionGroup h, decompositionGroup_eq_top]

end eq_top

section eq_bot

open ExtDVR IsValExtension Polynomial

-- `IsDiscrete vK.v` may be weakened to `Nontrivial vK.v`.
variable (K L : Type*) [Field K] [Field L] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [Algebra K L] [IsValExtension vK.v vL.v] [FiniteDimensional K L]

variable {K L}
variable [CompleteSpace K]

omit [CompleteSpace K] in
theorem AlgEquiv.mem_decompositionGroup [CompleteSpace K] (s : L ≃ₐ[K] L) : s ∈ decompositionGroup K L := by
  rw [decompositionGroup_eq_top]
  exact Subgroup.mem_top s

--it's already in ValExtension
instance : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) where
    map_nonunit r hr := by
      by_cases h : r = 0
      · simp [h] at hr
      · apply Valuation.Integers.isUnit_of_one (v := vK.v)
        · exact Valuation.integer.integers (v := vK.v)
        · simpa only [Algebra.algebraMap_ofSubring_apply, isUnit_iff_ne_zero, ne_eq,
          ZeroMemClass.coe_eq_zero]
        · apply Valuation.Integers.one_of_isUnit (Valuation.integer.integers (v := vL.v)) at hr
          change v (((algebraMap ↥𝒪[K] ↥𝒪[L]) r) : L) = 1 at hr
          norm_cast at hr
          rw [IsValExtension.val_map_eq_one_iff (vA := vL.v) (vR := vK.v)] at hr
          exact hr

instance [Algebra.IsSeparable K L] : Module.Finite 𝒪[K] 𝒪[L] := Module.IsNoetherian.finite 𝒪[K] 𝒪[L]

theorem lowerIndex_inf_le_mul (s t : L ≃ₐ[K] L) {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) : min (i_[L/K] s) (i_[L/K] t) ≤ i_[L/K] (s * t) := by
  by_cases hc : i_[L/K] (s * t) = ⊤
  · rw [hc]
    exact le_top
  · have h1 : ∃ n : ℕ, i_[L/K] (s * t) = n := by
      use (WithTop.untop (i_[L/K] (s * t)) hc)
      symm
      apply WithTop.coe_untop
    obtain ⟨n, hn⟩ := h1
    have h2 : s * t ∉ G(L/K)_[n] := by
      by_contra hc'
      absurd hn
      have hn' : n + 1 ≤ i_[L/K] (s * t) := by
        apply (mem_lowerRamificationGroup_iff_of_generator hgen _ _).1 hc'
        exact AlgEquiv.mem_decompositionGroup (s * t)
      absurd hn
      apply ne_of_gt
      apply (ENat.add_one_le_iff (ENat.coe_ne_top n)).1 hn'
    by_contra hc'
    absurd h2
    push_neg at hc'
    rw [lt_min_iff, hn] at hc'
    have h3 : s ∈ G(L/K)_[n] := by
      apply (mem_lowerRamificationGroup_iff_of_generator hgen _ _).2
      exact Order.add_one_le_of_lt hc'.1
      exact AlgEquiv.mem_decompositionGroup s
    have h4 : t ∈ G(L/K)_[n] := by
      apply (mem_lowerRamificationGroup_iff_of_generator hgen _ _).2
      exact Order.add_one_le_of_lt hc'.2
      exact AlgEquiv.mem_decompositionGroup t
    exact (Subgroup.mul_mem_cancel_right G(L/K)_[↑n] h4).mpr h3


set_option synthInstance.maxHeartbeats 1000000

omit [CompleteSpace K] in
theorem AlgEquiv.Simple_Extension_of_CDVR [CompleteSpace K] [Algebra.IsSeparable K L] [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])] : ∃ gen : 𝒪[L], Algebra.adjoin 𝒪[K] {gen} = ⊤ := by
  apply ExtDVR.exists_primitive (A := 𝒪[K]) (B := 𝒪[L])
  exact Valuation.HasExtension.algebraMap_injective (vK := vK.v) (vA := vL.v)

--can delete the assumption of generator.
/-- Should be strenthened to ` > 0`-/
theorem AlgEquiv.val_map_generator_sub_ne_zero {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) {s : L ≃ₐ[K] L} (hs : s ≠ .refl) : vL.v (s gen - gen) ≠ 0 := by
  by_contra h
  rw [zero_iff, sub_eq_zero] at h
  apply hs
  rw [AlgEquiv.eq_iff_ValuationSubring]
  apply Algebra.algHomClass_ext_generator hgen
  ext; simp only [AlgEquiv.restrictValuationSubring_apply, h, AlgEquiv.coe_refl, id_eq]


/--  The orginal proof uses `PowerBasis.adjoin_gen_eq_top`.
Should be strenthened to ` > 0`-/
theorem AlgEquiv.val_map_powerBasis_sub_ne_zero (pb : PowerBasis 𝒪[K] 𝒪[L]) {s : L ≃ₐ[K] L} (hs : s ≠ .refl) :
  vL.v (s pb.gen - pb.gen) ≠ 0 :=
  s.val_map_generator_sub_ne_zero (PowerBasis.adjoin_gen_eq_top pb) hs

open Polynomial in
theorem AlgEquiv.val_map_sub_le_generator {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) (s : L ≃ₐ[K] L) (x : 𝒪[L]) : v (s x - x) ≤ v (s gen - gen) := by
  by_cases hs : s = .refl
  · subst hs
    simp only [AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, le_refl]
  rcases Algebra.exists_eq_aeval_generator hgen x with ⟨f, hf⟩
  subst hf
  rcases taylor_order_zero_apply_aeval f gen ((AlgEquiv.restrictValuationSubring s) gen - gen) with ⟨b, hb⟩
  rw [add_sub_cancel, add_comm, ← sub_eq_iff_eq_add, aeval_algHom_apply, Subtype.ext_iff] at hb
  simp only [AddSubgroupClass.coe_sub, AlgEquiv.restrictValuationSubring_apply, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subring.coe_toSubsemiring] at hb
  rw [hb]
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, AlgEquiv.restrictValuationSubring_apply,
    _root_.map_mul]
  nth_rw 2 [← mul_one (v (s gen - gen))]
  exact mul_le_mul_of_nonneg_left b.2 (WithZero.zero_le (v (s ↑gen - ↑gen)))

open Polynomial in
/-- The orginal proof uses `PowerBasis.exists_eq_aeval`. -/
theorem AlgEquiv.val_map_sub_le_powerBasis (pb : PowerBasis 𝒪[K] 𝒪[L]) (s : L ≃ₐ[K] L) (x : 𝒪[L]) : vL.v (s x - x) ≤ vL.v (s pb.gen - pb.gen) := AlgEquiv.val_map_sub_le_generator (PowerBasis.adjoin_gen_eq_top pb) s x

theorem AlgEquiv.iSup_val_map_sub_eq_generator {gen : 𝒪[L]} (hgen : Algebra.adjoin 𝒪[K] {gen} = ⊤) (s : L ≃ₐ[K] L) :
  ⨆ x : vL.v.integer, v (s x - x) = v (s gen - gen) := by
  apply le_antisymm
  · letI : Nonempty 𝒪[L] := inferInstanceAs (Nonempty vL.v.integer)
    apply ciSup_le <| AlgEquiv.val_map_sub_le_generator hgen s
  · apply le_ciSup (f := fun (x : 𝒪[L]) ↦ v (s x - x)) _ gen
    use v (s gen - gen)
    intro y hy
    simp only [Set.mem_range, Subtype.exists, exists_prop] at hy
    rcases hy with ⟨a, ha⟩
    rw [← ha.2, show s a - a = s (⟨a, ha.1⟩ : 𝒪[L]) - (⟨a, ha.1⟩ : 𝒪[L]) by rfl]
    apply AlgEquiv.val_map_sub_le_generator hgen

/-- The original proof uses `AlgEquiv.val_map_sub_le_powerBasis`. -/
theorem AlgEquiv.iSup_val_map_sub_eq_powerBasis (pb : PowerBasis 𝒪[K] 𝒪[L]) (s : L ≃ₐ[K] L) :
  ⨆ x : vL.v.integer, v (s x - x) = v (s pb.gen - pb.gen) :=
  AlgEquiv.iSup_val_map_sub_eq_generator (PowerBasis.adjoin_gen_eq_top pb) s

open Classical in
/-- Should I `open Classical`? -/
theorem lowerIndex_of_powerBasis (pb : PowerBasis 𝒪[K] 𝒪[L]) (s : L ≃ₐ[K] L) :
  i_[L/K] s = if h : s = .refl then (⊤ : ℕ∞)
    else (- Multiplicative.toAdd (WithZero.unzero (AlgEquiv.val_map_powerBasis_sub_ne_zero pb h))).toNat := by
  by_cases h : s = .refl
  · simp only [h, lowerIndex_refl, ↓reduceDIte]
  · unfold AlgEquiv.lowerIndex
    simp only [h, AlgEquiv.iSup_val_map_sub_eq_powerBasis pb, AlgEquiv.val_map_powerBasis_sub_ne_zero pb h, ↓reduceDIte]

@[simp]
theorem lowerIndex_ne_refl {s : L ≃ₐ[K] L} (hs : s ≠ .refl) : i_[L/K] s ≠ ⊤ := by
  apply lowerIndex_ne_one
  rw [decompositionGroup_eq_top]
  apply Subgroup.mem_top s
  exact hs

variable (K L) in
theorem iSup_ne_refl_lowerIndex_ne_top [Nontrivial (L ≃ₐ[K] L)] :
  ⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s ≠ ⊤ := by
  rw [← lt_top_iff_ne_top, iSup_lt_iff]
  let f : {s : (L ≃ₐ[K] L) // s ≠ .refl} → ℕ :=
    fun s ↦ WithTop.untop _ (lowerIndex_ne_refl s.2)
  letI : Nonempty {s : (L ≃ₐ[K] L) // s ≠ .refl} := Exists.casesOn (exists_ne AlgEquiv.refl)
    fun s hs ↦ Nonempty.intro ⟨s, hs⟩
  rcases Finite.exists_max f with ⟨a, ha⟩
  use f a
  constructor
  · exact WithTop.coe_lt_top _
  · intro s
    have : i_[L/K] s = (f s : ℕ∞) := by
      exact (WithTop.coe_untop (i_[L/K] s) (lowerIndex_ne_refl s.2)).symm
    simp only [ne_eq, this, Nat.cast_le, ha]


-- if n > sup_{s ≠ 1} i_G s then G_n = {1}.
theorem aux7 [Algebra.IsSeparable K L] [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])]
  {n : ℕ} (hu : n > ⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s)
  {s : L ≃ₐ[K] L} (hs : s ∈ G(L/K)_[n]) : s = .refl := by
  apply (mem_lowerRamificationGroup_iff_of_generator (PowerBasis.adjoin_gen_eq_top (PowerBasisValExtension K L)) s.mem_decompositionGroup n).mp at hs
  by_contra! h
  rw [ENat.add_one_le_iff (by simp only [ne_eq, ENat.coe_ne_top, not_false_eq_true])] at hs
  have : i_[L/K] s < n := by
    apply lt_of_le_of_lt _ hu
    rw [show s = (⟨s, h⟩ : {s // s ≠ .refl}).1 by rfl]
    exact le_iSup_iff.mpr fun b a ↦ a ⟨s, h⟩
  apply lt_asymm hs this

-- this uses local fields and bichang's work, check if the condition is too strong..., It should be O_L is finitely generated over O_K
omit [CompleteSpace K] in
theorem exist_lowerRamificationGroup_eq_bot [CompleteSpace K] [Algebra.IsSeparable K L][Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])] :
    ∃ u : ℤ, G(L/K)_[u] = ⊥ := by
  by_cases h : Nontrivial (L ≃ₐ[K] L)
  · let n0 : ℕ := (WithTop.untop _ (iSup_ne_refl_lowerIndex_ne_top K L) : ℕ) + 1
    use (n0 : ℤ)
    ext s
    constructor
    · intro hs
      rw [Subgroup.mem_bot]
      have hu : n0 > ⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s := by
        have hsup :
            ⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s =
              ((WithTop.untop (⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s)
                (iSup_ne_refl_lowerIndex_ne_top K L) : ℕ) : ℕ∞) := by
          exact
            (WithTop.coe_untop
              (⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s)
              (iSup_ne_refl_lowerIndex_ne_top K L)).symm
        have hlt :
            ((WithTop.untop (⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s)
              (iSup_ne_refl_lowerIndex_ne_top K L) : ℕ) : ℕ∞) <
              (((WithTop.untop (⨆ s : {s : (L ≃ₐ[K] L) // s ≠ .refl}, i_[L/K] s)
                (iSup_ne_refl_lowerIndex_ne_top K L) : ℕ) + 1 : ℕ) : ℕ∞) := by
          exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self _)
        simpa [n0, gt_iff_lt, hsup] using hlt
      simpa [AlgEquiv.aut_one] using (aux7 (n := n0) hu hs)
    · intro hs
      rw [Subgroup.mem_bot] at hs
      subst hs
      exact (G(L/K)_[(n0 : ℤ)]).one_mem
  · use 0
    ext s
    constructor
    · intro _
      rw [Subgroup.mem_bot, AlgEquiv.aut_one]
      letI : Subsingleton (L ≃ₐ[K] L) := not_nontrivial_iff_subsingleton.mp h
      exact Subsingleton.elim s 1
    · intro hs
      rw [Subgroup.mem_bot] at hs
      subst hs
      exact (G(L/K)_[0]).one_mem


end eq_bot

end ExhausiveSeperated
