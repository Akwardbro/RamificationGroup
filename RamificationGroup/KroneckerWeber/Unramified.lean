import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Invariant.Basic

section IsUnramifiedAt

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

open IsLocalRing

/--
Compatibility alias for older code: this is `Algebra.isUnramifiedAt_iff_map_eq` in current mathlib.
-/
lemma Algebra.isUnramifiedAt_iff_map_eq2 [EssFiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Algebra.IsUnramifiedAt R q ↔
      Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal _ := by
  simpa using (Algebra.isUnramifiedAt_iff_map_eq (R := R) p q)

end IsUnramifiedAt
