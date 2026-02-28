--import RamificationGroup.Valued.Hom.ValExtension
import RamificationGroup.ForMathlib.LocalRing.Basic
import RamificationGroup.Valuation.Discrete
import RamificationGroup.Valuation.Extension

/-!
This file is a continuation of the file ValExtension.

We break this file to simplify the import temporarily

-/
open Valuation Valued IsValExtension DiscreteValuation

section nontrivial

variable {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [IsNontrivial vR.v] [vA : Valued A ΓA] [IsValExtension vR.v vA.v]



variable (R A) in
theorem nontrivial_of_valExtension  [vR : Valued R ΓR] [IsNontrivial vR.v] [IsValExtension vR.v vA.v] : IsNontrivial vA.v where
  exists_val_nontrivial := by
    obtain ⟨r, hr0, hr1⟩ := (inferInstance : IsNontrivial vR.v).exists_val_nontrivial
    refine ⟨algebraMap R A r, ?_, ?_⟩
    · intro h
      exact hr0 <| by
        have h' := (IsValExtension.val_map_eq_iff (vR := vR.v) (vA := vA.v) r 0).mp (by
          simpa [map_zero] using h)
        simpa [map_zero] using h'
    · intro h
      exact hr1 <| (IsValExtension.val_map_eq_one_iff (vR := vR.v) (vA := vA.v) r).mp h


end nontrivial
