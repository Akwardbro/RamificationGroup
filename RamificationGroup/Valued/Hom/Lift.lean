import RamificationGroup.Valued.Hom.Basic


open Valued

variable {K L : Type*} [Field K] [Field L] {ΓK ΓL: Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ΓK] [vL : Valued L ΓL] [ValAlgebra K L]

-- `valuation_subring.algebra` instance as algebra Maria and Phillip
instance : ValAlgebra 𝒪[K] 𝒪[L] := sorry

variable {K L L' : Type*} [Field K] [Field L] [Field L'] {ΓK ΓL ΓL': Type*} [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL] [LinearOrderedCommGroupWithZero ΓL'] [vK : Valued K ΓK] [vL : Valued L ΓL] [vL' : Valued L' ΓL'] [ValAlgebra K L] [ValAlgebra K L'] -- [FiniteDimensional K L]

def ValAlgHom.liftInteger  (s : L →ₐv[K] L') : 𝒪[L] →ₐv[𝒪[K]] 𝒪[L']  := sorry

-- def ValAlgIso.liftInteger (s : L ≃ₐv[K] L) : 𝒪[L] ≃ₐv[𝒪[K]] 𝒪[L]  := sorry

instance : Coe (ValAlgHom K L L') (ValAlgHom 𝒪[K] 𝒪[L] 𝒪[L']) := ⟨ValAlgHom.liftInteger⟩

-- instance : Coe (ValAlgIso K L L') (ValAlgIso 𝒪[K] 𝒪[L] 𝒪[L']) := ⟨ValAlgIso.liftInteger⟩



/-
def ValAlgHom.liftValuationIntegerQuotientLEIdeal (s : L →ₐv[K] L) (γ : ΓL') : 𝒪[L]⧸(vL'.v.LEIdeal γ) →ₐ[𝒪[K]] 𝒪[L']⧸(vL.LEIdeal γ) := sorry

def ValAlgIso.liftValuationIntegerQuotientLEIdeal (s : L ≃ₐ[K] L) (γ : ΓL) : (𝒪[vL]⧸(vL.LEIdeal γ)) ≃ₐ[𝒪[vK]] (𝒪[vL]⧸(vL.LEIdeal γ)) := sorry

-- `LT version`

def AlgHom.liftResidueField (s : L →ₐ[K] L) : 𝓀[vL] →ₐ[𝓀[vK]] 𝓀[vL] := sorry

def AlgEquiv.liftResidueField (s : L ≃ₐ[K] L) : 𝓀[vL] ≃ₐ[𝓀[vK]] 𝓀[vL] := sorry

-/
