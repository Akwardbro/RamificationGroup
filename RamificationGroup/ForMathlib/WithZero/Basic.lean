import Mathlib.FieldTheory.KrullTopology

def WithZero.some {α : Type*} : α → WithZero α :=
  Option.some

def WithZero.MulHom {α : Type*} [Monoid α] : α →* WithZero α where
  toFun := WithZero.some
  map_one' := rfl
  map_mul' _ _ := rfl

theorem WithZero.coe_prod {α β : Type*} [CommMonoid β] {s : Finset α} {f : α → β} : (↑(∏ x ∈ s, f x) : WithZero β) =  (∏ x ∈ s, ↑(f x : WithZero β)) := by
  simp only [WithZero.coe]
  apply map_prod WithZero.MulHom f s

theorem WithTop.untop_add_one (x : WithTop ℕ) (h : x ≠ ⊤) : WithTop.untop x h + 1 = WithTop.untop (x + 1) (WithTop.add_ne_top.2 ⟨h, WithTop.one_ne_top⟩) := by
  symm
  apply (WithTop.untop_eq_iff _).2
  simp only [coe_add, coe_untop, coe_one]

theorem WithTop.untop_lt_untop {a b : WithTop ℕ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : WithTop.untop a ha < WithTop.untop b hb ↔ a < b := by
  constructor <;> intro h
  · have h' : a < ((WithTop.untop b hb : ℕ) : WithTop ℕ) :=
      (WithTop.untop_lt_iff ha).1 h
    exact lt_of_lt_of_eq h' (WithTop.coe_untop b hb)
  · have h' : a < ((WithTop.untop b hb : ℕ) : WithTop ℕ) := by
      exact lt_of_lt_of_eq h (WithTop.coe_untop b hb).symm
    exact (WithTop.untop_lt_iff ha).2 h'
