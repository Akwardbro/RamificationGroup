import RamificationGroup.Valued.Defs
import RamificationGroup.Valuation.Discrete

/-!
# Extension of Valuation

In this file, we define the typeclass for valuation extensions and prove basic facts about
extension of valuations.

## Main Definition

* `IsValExtension R A` : The valuation on `A` is an extension of the valuation on `R`.

## References

-/
open Valued Valuation

namespace Valued

variable {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
  [vR : Valued R ΓR] [vS : Valued S ΓS] {f : R →+* S} (hf : vR.v.IsEquiv <| vS.v.comap f)

@[simp]
theorem val_map_le_iff (x y : R) : v (f x) ≤ v (f y) ↔ v x ≤ v y :=
  (hf x y).symm

@[simp]
theorem val_map_lt_iff (x y : R) : v (f x) < v (f y) ↔ v x < v y := by
  convert (val_map_le_iff hf y x).not <;>
  push_neg <;> rfl

@[simp]
theorem val_map_eq_iff (x y : R) : v (f x) = v (f y) ↔ v x = v y := by
  calc
    _ ↔ v (f x) ≤ v (f y) ∧ v (f y) ≤ v (f x) := le_antisymm_iff
    _ ↔ v x ≤ v y ∧ v y ≤ v x := by
      apply and_congr <;>
      exact val_map_le_iff hf _ _
    _ ↔ _ := le_antisymm_iff.symm

@[simp]
theorem val_map_le_one_iff (x : R) : v (f x) ≤ 1 ↔ v x ≤ 1 := by
  convert val_map_le_iff hf x 1 <;>
  simp only [_root_.map_one]

@[simp]
theorem val_map_lt_one_iff (x : R) : v (f x) < 1 ↔ v x < 1 := by
  convert val_map_lt_iff hf x 1 <;>
  simp only [_root_.map_one]

@[simp]
theorem val_map_eq_one_iff (x : R) : v (f x) = 1 ↔ v x = 1 := by
  convert val_map_eq_iff hf x 1 <;>
  simp only [_root_.map_one]

end Valued

-- is injectivity needed here?
/--
An instance of `IsValExtension R A` states that the valuation of `A` is an extension of the valuation on `R`.
-/
class IsValExtension (R A : Type*) {ΓR ΓA : outParam Type*} [CommRing R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] : Prop where
  /-- the valuation on `R` is equivlent to the comap of the valuation on `A` -/
  val_isEquiv_comap : vR.v.IsEquiv <| vA.v.comap (algebraMap R A)

namespace IsValExtension

section CoeLemma

variable {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension R A]

@[simp, norm_cast]
theorem val_map_le_iff (x y : R) : v (algebraMap R A x) ≤ v (algebraMap R A y) ↔ v x ≤ v y :=
  Valued.val_map_le_iff val_isEquiv_comap x y

@[simp, norm_cast]
theorem val_map_lt_iff (x y : R) : v (algebraMap R A x) < v (algebraMap R A y) ↔ v x < v y :=
  Valued.val_map_lt_iff val_isEquiv_comap x y

@[simp, norm_cast]
theorem val_map_eq_iff (x y : R) : v (algebraMap R A x) = v (algebraMap R A y) ↔ v x = v y :=
  Valued.val_map_eq_iff val_isEquiv_comap x y

@[simp, norm_cast]
theorem val_map_le_one_iff (x : R) : v (algebraMap R A x) ≤ 1 ↔ v x ≤ 1 :=
  Valued.val_map_le_one_iff val_isEquiv_comap x

@[simp, norm_cast]
theorem val_map_lt_one_iff (x : R) : v (algebraMap R A x) < 1 ↔ v x < 1 :=
  Valued.val_map_lt_one_iff val_isEquiv_comap x

@[simp, norm_cast]
theorem val_map_eq_one_iff (x : R) : v (algebraMap R A x) = 1 ↔ v x = 1 :=
  Valued.val_map_eq_one_iff val_isEquiv_comap x

instance id : IsValExtension R R where
  val_isEquiv_comap := by
    simp only [Algebra.id.map_eq_id, comap_id]
    rfl

end CoeLemma

section mk'

def of_integer_comap {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension R A] (h : vA.v.integer.comap (algebraMap R A) = vR.v.integer) : IsValExtension R A where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [← Valuation.mem_integer_iff, ← Valuation.mem_integer_iff]
    rw [← h]
    rfl

def of_valuationSubring_comap {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Field A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension R A] (h : 𝒪[A].comap (algebraMap R A) = 𝒪[R]) : IsValExtension R A := by
    apply of_integer_comap
    rw [show vR.v.integer = 𝒪[R].toSubring by rfl, ← h]
    rfl

end mk'

section lift

section Integer

variable {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension R A]

instance integerAlgebra : Algebra vR.v.integer vA.v.integer where
    smul r a := {
      val := r • a,
      property := by
        rw [Valuation.mem_integer_iff,
          show r • ↑a = algebraMap R A r * a by exact (Algebra.smul_def r (a : A))]
        norm_num
        apply mul_le_one'
        · simp only [val_map_le_one_iff]
          exact r.2
        · exact a.2
    }
    toFun r := {
      val := algebraMap R A r,
      property := by
        simp only [Valuation.mem_integer_iff,
          val_map_le_one_iff]
        exact r.2
    }
    map_one' := by
      ext
      simp
    map_mul' _ _ := by
      ext
      simp
    map_zero' := by
      ext
      simp
    map_add' _ _ := by
      ext
      simp
    commutes' _ _ := by
      ext
      exact Algebra.commutes _ _
    smul_def' _ _ := by
      ext
      exact Algebra.smul_def _ _

@[simp, norm_cast]
theorem coe_algebraMap_integer (r : vR.v.integer) : ((algebraMap vR.v.integer vA.v.integer) r : A) = (algebraMap R A) (r : R) := rfl

end Integer

section ValuationSubring

variable {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Field A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension R A]

instance valuationSubringAlgebra : Algebra 𝒪[R] 𝒪[A] := inferInstanceAs <| Algebra vR.v.integer vA.v.integer

variable (R A) in
theorem subtype_comp_algebraMap_eq_algebraMap : RingHom.comp 𝒪[A].subtype (algebraMap 𝒪[R] 𝒪[A]) = algebraMap 𝒪[R] A := rfl

theorem subtype_comp_algebraMap_eq_algebraMap_apply (x : 𝒪[R]) : (algebraMap 𝒪[R] 𝒪[A] x).val = (algebraMap 𝒪[R] A) x := rfl

@[simp, norm_cast]
theorem coe_algebraMap_valuationSubring (r : 𝒪[R]) : ((algebraMap 𝒪[R] 𝒪[A]) r : A) = (algebraMap R A) (r : R) := rfl

instance : IsLocalRingHom (algebraMap 𝒪[R] 𝒪[A]) where
    map_nonunit r hr := by
      by_cases h : r = 0
      · simp [h] at hr
      · apply Valuation.Integers.isUnit_of_one (v := vR.v)
        · exact Valuation.integer.integers (v := vR.v)
        · simpa only [ValuationSubring.algebraMap_apply, isUnit_iff_ne_zero, ne_eq,
          ZeroMemClass.coe_eq_zero]
        · apply Valuation.Integers.one_of_isUnit (Valuation.integer.integers (v := vA.v)) at hr
          change v (((algebraMap ↥𝒪[R] ↥𝒪[A]) r) : A) = 1 at hr
          simp only [coe_algebraMap_valuationSubring, val_map_eq_one_iff] at hr
          exact hr

variable (R A) in
theorem integerAlgebra_injective : Function.Injective (algebraMap 𝒪[R] 𝒪[A]) := by
  intro x y h
  simp only [Subtype.ext_iff, coe_algebraMap_valuationSubring] at h
  ext
  apply RingHom.injective (algebraMap R A) h

section scalar_tower

attribute [local instance 1001] Algebra.toSMul

instance instIsScalarTowerToValuationSubringToField : IsScalarTower 𝒪[R] 𝒪[A] A where
  smul_assoc x y z := by
    simp only [Algebra.smul_def]
    calc
      _ = (algebraMap 𝒪[A] A) ((algebraMap 𝒪[R] 𝒪[A]) x) * (algebraMap 𝒪[A] A) y * z := by simp only [_root_.map_mul,
        ValuationSubring.algebraMap_apply, coe_algebraMap_valuationSubring]
      _ = (algebraMap 𝒪[A] A) ((algebraMap 𝒪[R] 𝒪[A]) x) * ((algebraMap 𝒪[A] A) y * z) := mul_assoc _ _ _

end scalar_tower

end ValuationSubring

end lift

section nontrivial

variable {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [Ring A]
  [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
  [Algebra R A] [vR : Valued R ΓR] [Nontrivial vR.v] [vA : Valued A ΓA] [IsValExtension R A]

variable (R A) in
theorem nontrivial_of_valExtension : Nontrivial vA.v where
  nontrivial := by
    rcases vR.v.nontrivial_def with ⟨r, h0, h1⟩
    use (algebraMap R A) r
    simp [h1]
    rw [show (0 : ΓA) = vA.v (0) by simp, show (0 : A) = (algebraMap R A) 0 by simp, val_map_eq_iff]
    simp [h0]

end nontrivial

end IsValExtension
