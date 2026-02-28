import Mathlib.Order.SetNotation
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.WithBot
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Real


theorem sSup_eq_aux (n : ℕ) : sSup {n1 | n1 ≤ n} = n := by
  apply le_antisymm
  · exact csSup_le' fun ⦃a⦄ a ↦ a
  · apply le_csSup
    use n
    unfold upperBounds
    simp only [Set.mem_setOf_eq, imp_self, implies_true]
    simp only [Set.mem_setOf_eq, le_refl]

theorem ceil_nonpos {u : ℚ} (h : u ≤ 0) : ⌈u⌉ ≤ 0 := by
  by_contra h
  push_neg at *
  have : ¬u ≤ 0 := by linarith [Int.ceil_pos.1 h]
  contradiction

theorem insert_Icc_left (a b : ℤ) (ha : a ≤ b): Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
  ext x
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 h
    rw [Finset.insert_eq]
    apply Finset.mem_union.2
    by_cases h : x = a
    · left
      simp [h]
    · right
      push_neg at *
      apply Finset.mem_Icc.2
      constructor
      · apply Int.le_of_sub_one_lt
        simp [lt_of_le_of_ne h1 h.symm]
      exact h2
  · rw [Finset.insert_eq, Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
    rintro h
    rcases h with h | ⟨h1, h2⟩
    · constructor
      · apply le_of_eq (Finset.mem_singleton.1 h).symm
      · apply le_trans (le_of_eq (Finset.mem_singleton.1 h)) ha
    · constructor
      · linarith [h1]
      · exact h2

theorem insert_Icc_right (a b : ℤ) (h : a ≤ b) : Finset.Icc a b = insert b (Finset.Icc a (b - 1)) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.insert_eq b (Finset.Icc a (b - 1))]
    apply Finset.mem_union.2
    by_cases h : x = b
    · left
      simp [h]
    · right
      simp at hx
      simp
      constructor
      · exact hx.1
      · apply Int.le_of_sub_one_lt
        apply lt_of_le_of_ne
        linarith
        push_neg at h
        simp [h]
  · rw [Finset.insert_eq b (Finset.Icc a (b - 1))]
    apply Finset.union_subset
    simp [h]
    apply Finset.Icc_subset_Icc
    rfl; linarith

theorem sum_insert_left_aux (a b : ℤ) (ha : a ≤ b) (f : ℤ → ℕ) : (∑ x ∈ Finset.Icc a b, f x) - f a = (∑ x ∈ Finset.Icc (a + 1) b, f x):= by
  calc
    _ = ∑ x ∈ insert a (Finset.Icc (a + 1) b), f x - f a := by
      rw [insert_Icc_left _ _ ha]
    _ = (∑ x ∈ Finset.Icc (a + 1) b, f x) := by simp

theorem sum_insert_left_aux' (a b : ℤ) (h : a ≤ b) (f : ℤ → ℤ) : (∑ x ∈ Finset.Icc a b, f x) - f a = (∑ x ∈ Finset.Icc (a + 1) b, f x) := by
  calc
    _ = ∑ x ∈ insert a (Finset.Icc (a + 1) b), f x - f a := by
      rw [insert_Icc_left _ _ h]
    _ = (∑ x ∈ Finset.Icc (a + 1) b, f x) := by simp

theorem sum_insert_right_aux' (a b : ℤ) (h : a ≤ b) (f : ℤ → ℤ) : (∑ x ∈ Finset.Icc a b, f x) = (∑ x ∈ Finset.Icc a (b - 1), f x) + f b := by
  calc
    _ = ∑ x ∈ insert b (Finset.Icc a (b - 1)), f x := by
      rw [insert_Icc_right _ _ h]
    _ = (∑ x ∈ Finset.Icc a (b - 1), f x) + f b := by simp [add_comm]

theorem sum_insert_right_aux (a b : ℤ) (h : a ≤ b) (f : ℚ → ℚ) : (∑ x ∈ Finset.Icc a b, f x) - f b = (∑ x ∈ Finset.Icc a (b - 1), f x) := by
  apply tsub_eq_of_eq_add
  calc
    _ = ∑ x ∈ insert b (Finset.Icc a (b - 1)), f x := by
      rw [insert_Icc_right _ _ h]
    _ = (∑ x ∈ Finset.Icc a (b - 1), f x) + f b := by simp [add_comm]

theorem sum_insert_right_aux'' (a b : ℤ) (h : a ≤ b) (f : ℤ → ℚ) : (∑ x ∈ Finset.Icc a b, f x) - f b = (∑ x ∈ Finset.Icc a (b - 1), f x) := by
  apply tsub_eq_of_eq_add
  calc
    _ = ∑ x ∈ insert b (Finset.Icc a (b - 1)), f x := by
      rw [insert_Icc_right _ _ h]
    _ = (∑ x ∈ Finset.Icc a (b - 1), f x) + f b := by simp [add_comm]

theorem sum_insert_right_aux''' (a b : ℤ) (h : a ≤ b) (f : ℤ → ℕ) : (∑ x ∈ Finset.Icc a b, f x) = (∑ x ∈ Finset.Icc a (b - 1), f x) + f b := by
  calc
    _ = ∑ x ∈ insert b (Finset.Icc a (b - 1)), f x := by
      rw [insert_Icc_right _ _ h]
    _ = (∑ x ∈ Finset.Icc a (b - 1), f x) + f b := by simp [add_comm]

theorem Int.aux {a b : ℤ} (h1 : a ≤ b) (h2 : b < a + 1) : a = b := by
  by_contra hc
  have h3 : a < b := by exact lt_of_le_of_ne h1 hc
  have h4 : a + 1 ≤ b := by exact h3
  absurd h4; push_neg; exact h2

theorem Finset.sum_untop {α : Type*} {s : Finset α} {β : Type*} [AddCommMonoid β] [LT β] {f : α → WithTop β} (h : ∑ x : s, f x ≠ ⊤) : ∑ x : s, ((f x).untop (WithTop.lt_top_iff_ne_top.1 ((WithTop.sum_lt_top).1 (WithTop.lt_top_iff_ne_top.2
h) x (mem_univ x)))) = (∑ x : s, f x).untop h := by
  symm
  apply (WithTop.untop_eq_iff h).2
  simp only [univ_eq_attach, WithTop.coe_sum, WithTop.coe_untop]

@[simp]
theorem Function.comp_left_cancel {α β γ: Type*} [Nonempty α] {f1 f2 : β → γ} {g : α → β} (h : Bijective g) (h1 : f1 ∘ g = f2 ∘ g) : f1 = f2 := by
  ext x
  have hsurj : ∀ (x : β), ∃ (y : α), g y = x := by
    apply Function.Bijective.surjective h
  obtain ⟨y, hy⟩ := hsurj x
  rw [← hy, ← (Function.comp_apply (f := f1) (g := g) (x := y)), ← (Function.comp_apply (f := f2) (g := g) (x := y)), h1]

open QuotientGroup

noncomputable def Subgroup_map {G H : Type*} [Group G] [Group H] {N : Subgroup G} {f : G →* H} : N.map f ≃ N ⧸ (N ⊓ f.ker).subgroupOf N := by
  symm
  let φ : N →* (N.map f) := {
    toFun := fun x => ⟨f x, by
      simp only [Subgroup.mem_map]
      use x
      constructor
      · exact SetLike.coe_mem x
      · rfl⟩
    map_one' := by
      ext
      apply f.map_one'
    map_mul' := by
      intro x y
      ext
      apply f.map_mul'
  }
  haveI h' : Function.Surjective φ := by
    intro y
    dsimp [φ]
    have hy : y.1 ∈ Subgroup.map f N := by exact SetLike.coe_mem y
    obtain ⟨t, ht1, ht2⟩ := Subgroup.mem_map.1 hy
    use ⟨t, ht1⟩
    exact SetCoe.ext ht2
  haveI h1 : N ⧸ φ.ker ≃* (Subgroup.map f N) := by
    apply QuotientGroup.quotientKerEquivOfSurjective (G := N) (H := (N.map f)) (φ := φ) h'
  have h2 : φ.ker = (N ⊓ f.ker).subgroupOf N := by
    ext x
    constructor
    <;> intro hx
    · simp only [Subgroup.inf_subgroupOf_left]
      refine Subgroup.mem_subgroupOf.mpr ?h.mp.a
      rw [MonoidHom.mem_ker] at *
      exact (Submonoid.mk_eq_one (Subgroup.map f N).toSubmonoid).mp hx
    · simp only [Subgroup.inf_subgroupOf_left] at hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker] at *
      exact OneMemClass.coe_eq_one.mp hx
  rw [← h2]
  apply h1.toEquiv

theorem Int.ceil_eq_ceil {a b : ℝ} (h : a ≤ b) (h' : b - a ≤ ⌈a⌉ - a) : ⌈b⌉ = ⌈a⌉ := by
  by_contra hc
  have h : ⌈a⌉ < b := by
    apply lt_of_le_of_lt (b := (⌈b⌉ - 1 : ℝ))
    norm_cast
    push_neg at hc
    apply Int.le_sub_one_of_lt (lt_of_le_of_ne (Int.ceil_le_ceil h) hc.symm)
    rw [sub_lt_iff_lt_add]
    apply Int.ceil_lt_add_one
  simp only [tsub_le_iff_right, sub_add_cancel] at h'
  absurd h'
  push_neg
  exact_mod_cast h

theorem Finset.Icc_union_Icc_eq_Icc {a b c : ℤ} (h : a ≤ b) (h' : b ≤ c) : Finset.Icc a b ∪ Finset.Icc (b + 1) c = Finset.Icc a c := by
  ext x
  constructor
  <;> intro hx
  · simp only [mem_union, mem_Icc] at *
    match hx with
        | Or.inl hx =>
                      refine ⟨hx.1, le_trans hx.2 h'⟩
        | Or.inr hx =>
                      refine ⟨by linarith [h, hx], hx.2⟩
  · simp only [mem_union, mem_Icc] at *
    by_cases hx' : x ≤ b
    · left
      refine ⟨hx.1, hx'⟩
    · right
      refine ⟨by linarith [hx'], hx.2⟩
