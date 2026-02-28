import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Basic


section semiring
variable {A : Type _} {B : Type _} [CommSemiring A] [Semiring B] [Algebra A B]

def AlgEquiv.ofTop {S : Subalgebra A B} (hS : S = ⊤) : S ≃ₐ[A] B := { S.val with
    invFun := fun x ↦ ⟨x, hS.symm ▸ trivial⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
  }

section adjoin
namespace Algebra
open Polynomial
variable {x : B}

theorem pow_mem_adjoin_singleton (n : ℕ) : x ^ n ∈ adjoin A {x} := by
  induction n with
  | zero =>
      simpa using (one_mem (adjoin A ({x} : Set B)))
  | succ n ih =>
      simpa [pow_succ'] using mul_mem (self_mem_adjoin_singleton A x) ih


end Algebra
end adjoin

end semiring
