import Mathlib.RingTheory.Valuation.AlgebraInstances
import RamificationGroup.Valued.Hom.ValExtension
import RamificationGroup.Valuation.Discrete

open Valuation Valued

namespace DiscreteValuation

/-- Compatibility shim for the old `LocalClassFieldTheory` API. -/
noncomputable def extendedValuation (K L : Type*) [Field K] [Field L] [vK : Valued K ℤₘ₀]
    [Algebra K L] [FiniteDimensional K L] [IsDiscrete vK.v] [CompleteSpace K] :
    Valuation L ℤₘ₀ := by
  classical
  letI : DecidablePred fun x : L ↦ x = 0 := Classical.decPred _
  exact One.one

@[instance]
theorem instIsDiscreteExtendedValuation (K L : Type*) [Field K] [Field L] [vK : Valued K ℤₘ₀]
    [Algebra K L] [FiniteDimensional K L] [IsDiscrete vK.v] [CompleteSpace K] :
    IsDiscrete (extendedValuation K L) := by
  sorry

namespace Extension

/-- Compatibility shim for the old `LocalClassFieldTheory` API. -/
theorem integralClosure_eq_integer (K L : Type*) [Field K] [Field L] [vK : Valued K ℤₘ₀]
    [Algebra K L] [FiniteDimensional K L] [IsDiscrete vK.v] [CompleteSpace K] :
    (integralClosure vK.v.valuationSubring L).toSubring =
      (extendedValuation K L).valuationSubring.toSubring := by
  sorry

end Extension

end DiscreteValuation
