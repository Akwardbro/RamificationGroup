/-
Copyright (c) 2024 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Bichang Lei
-/
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.RingTheory.Valuation.Extension
-- import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Extension of Valuation

In this file, we define the typeclass for valuation extensions and prove basic facts about
extension of valuations. Let `A` be an `R` algebra, both `R` and `A` are equipped with valued
instance. Here, extension of valuation means that the pullback of valuation on `A` is equivalent
to the valuation on `R`. We only require equivalence, not equality of valuations here.

Note that we do not require the ring map from `R` to `A` to be injective. It holds automatically
when `R` is a division ring and `A` is nontrivial.

## Main Definition

* `IsValExtension R A` : The valuation on `A` is an extension of the valuation on `R`.

## References

* [Bourbaki, Nicolas. *Commutative algebra*] Chapter VI §3, Valuations.
* <https://en.wikipedia.org/wiki/Valuation_(algebra)#Extension_of_valuations>

## Tags
Valued, Valuation, Extension of Valuation

-/
open Valued Valuation

abbrev IsValExtension {R A : Type*} {ΓR ΓA : Type*} [CommRing R] [Ring A]
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
    [Algebra R A] (vR : Valuation R ΓR) (vA : Valuation A ΓA) : Prop :=
  vR.HasExtension vA

namespace IsValExtension

variable {R A : Type*} {ΓR ΓA : Type*} [CommRing R] [Ring A]
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
    [Algebra R A] {vR : Valuation R ΓR} {vA : Valuation A ΓA}
    [IsValExtension vR vA]

theorem val_isEquiv_comap : vR.IsEquiv <| vA.comap (algebraMap R A) :=
  Valuation.HasExtension.val_isEquiv_comap (vR := vR) (vA := vA)

theorem val_map_le_iff (x y : R) :
    vA (algebraMap R A x) ≤ vA (algebraMap R A y) ↔ vR x ≤ vR y :=
  Valuation.HasExtension.val_map_le_iff (vR := vR) (vA := vA) x y

theorem val_map_lt_iff (x y : R) :
    vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y :=
  Valuation.HasExtension.val_map_lt_iff (vR := vR) (vA := vA) x y

theorem val_map_eq_iff (x y : R) :
    vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y :=
  Valuation.HasExtension.val_map_eq_iff (vR := vR) (vA := vA) x y

theorem val_map_le_one_iff (x : R) : vA (algebraMap R A x) ≤ 1 ↔ vR x ≤ 1 :=
  Valuation.HasExtension.val_map_le_one_iff (vR := vR) (vA := vA) x

theorem val_map_lt_one_iff (x : R) : vA (algebraMap R A x) < 1 ↔ vR x < 1 :=
  Valuation.HasExtension.val_map_lt_one_iff (vR := vR) (vA := vA) x

theorem val_map_eq_one_iff (x : R) : vA (algebraMap R A x) = 1 ↔ vR x = 1 :=
  Valuation.HasExtension.val_map_eq_one_iff (vR := vR) (vA := vA) x

@[simp, norm_cast]
theorem val_algebraMap {K : Type*} {ΓK : Type*} [Field K]
    [LinearOrderedCommGroupWithZero ΓK]
    [Algebra K A] {vK : Valuation K ΓK} [IsValExtension vK vA] (r : vK.integer) :
    ((algebraMap vK.integer vA.integer) r : A) = (algebraMap K A) (r : K) :=
  Valuation.HasExtension.val_algebraMap (vR := vK) (vA := vA) r

end IsValExtension

namespace Valued

variable {R S : Type*} {ΓR ΓS : outParam Type*} [Ring R] [Ring S]
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓS]
    [vR : Valued R ΓR] [vS : Valued S ΓS]

variable {F : Type*} [FunLike F R S] [RingHomClass F R S] {f : F}
    (hf : vR.v.IsEquiv <| vS.v.comap f)

include hf

theorem val_map_le_iff (x y : R) : v (f x) ≤ v (f y) ↔ v x ≤ v y :=
  (hf x y).symm

theorem val_map_lt_iff (x y : R) : v (f x) < v (f y) ↔ v x < v y := by
  convert (val_map_le_iff hf y x).not <;>
  push_neg <;> rfl

theorem val_map_eq_iff (x y : R) : v (f x) = v (f y) ↔ v x = v y := by
  calc
    _ ↔ v (f x) ≤ v (f y) ∧ v (f y) ≤ v (f x) := le_antisymm_iff
    _ ↔ v x ≤ v y ∧ v y ≤ v x := by
      apply and_congr <;>
      exact val_map_le_iff hf _ _
    _ ↔ _ := le_antisymm_iff.symm

theorem val_map_le_one_iff (x : R) : v (f x) ≤ 1 ↔ v x ≤ 1 := by
  convert val_map_le_iff hf x 1 <;>
  simp only [_root_.map_one]

theorem val_map_lt_one_iff (x : R) : v (f x) < 1 ↔ v x < 1 := by
  convert val_map_lt_iff hf x 1 <;>
  simp only [_root_.map_one]

theorem val_map_eq_one_iff (x : R) : v (f x) = 1 ↔ v x = 1 := by
  convert val_map_eq_iff hf x 1 <;>
  simp only [_root_.map_one]

end Valued

namespace IsValExtension

variable {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [Ring A]
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
    [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension vR.v vA.v]

section mk'

def ofIntegerComap {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Ring A]
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
    [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension vR.v vA.v]
    (h : vA.v.integer.comap (algebraMap R A) = vR.v.integer) : IsValExtension vR.v vA.v where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [← Valuation.mem_integer_iff, ← Valuation.mem_integer_iff]
    rw [← h]
    rfl

def ofValuationSubringComap {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Field A]
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
    [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension vR.v vA.v]
    (h : 𝒪[A].comap (algebraMap R A) = 𝒪[R]) : IsValExtension vR.v vA.v := by
  apply ofIntegerComap
  rw [show vR.v.integer = 𝒪[R] by rfl, ← h]

end mk'

section lift

section Integer

variable {R A : Type*} {ΓR ΓA : outParam Type*} [CommRing R] [Ring A]
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
    [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension vR.v vA.v]

instance integerAlgebra : Algebra vR.v.integer vA.v.integer where
    smul r a := {
      val := r • a,
      property := by
        rw [Valuation.mem_integer_iff,
          show r • ↑a = algebraMap R A r * a by exact (Algebra.smul_def r (a : A))]
        norm_num
        apply mul_le_one'
        · rw [val_map_le_one_iff (vR := vR.v)]
          exact r.2
        · exact a.2
    }
    algebraMap :=
    {
      toFun r := {
        val := algebraMap R A r,
        property := by
          simp only [Valuation.mem_integer_iff,
            val_map_le_one_iff (vR := vR.v)]
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
        simp}
    commutes' _ _ := by
      ext
      exact Algebra.commutes _ _
    smul_def' _ _ := by
      ext
      exact Algebra.smul_def _ _

@[simp, norm_cast]
theorem coe_algebraMap_integer (r : vR.v.integer) :
    ((algebraMap vR.v.integer vA.v.integer) r : A) = (algebraMap R A) (r : R) := by
  rfl

end Integer

section ValuationSubring

variable {R A : Type*} {ΓR ΓA : outParam Type*} [Field R] [Field A]
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA]
    [Algebra R A] [vR : Valued R ΓR] [vA : Valued A ΓA] [IsValExtension vR.v vA.v]

instance : Algebra 𝒪[R] 𝒪[A] := inferInstanceAs (Algebra vR.v.integer vA.v.integer)

@[simp, norm_cast]
theorem coe_algebraMap_valuationSubring (r : 𝒪[R]) :
    ((algebraMap 𝒪[R] 𝒪[A]) r : A) = (algebraMap R A) (r : R) := rfl

#synth Algebra 𝒪[R] R
instance : IsLocalHom (algebraMap 𝒪[R] 𝒪[A]) where
    map_nonunit r hr := by
      by_cases h : r = 0
      · simp [h] at hr
      · apply Valuation.Integers.isUnit_of_one (v := vR.v)
        · exact Valuation.integer.integers (v := vR.v)
        · simpa only [Algebra.algebraMap_ofSubring_apply, isUnit_iff_ne_zero, ne_eq,
          ZeroMemClass.coe_eq_zero]
        · apply Valuation.Integers.one_of_isUnit (Valuation.integer.integers (v := vA.v)) at hr
          change v (((algebraMap ↥𝒪[R] ↥𝒪[A]) r) : A) = 1 at hr
          norm_cast at hr
          simp only [val_map_eq_one_iff (vR := vR.v)] at hr
          exact hr

variable (R A) in
theorem integerAlgebra_injective : Function.Injective (algebraMap 𝒪[R] 𝒪[A]) := by
  intro x y h
  simp only [Subtype.ext_iff, coe_algebraMap_valuationSubring] at h
  ext
  apply RingHom.injective (algebraMap R A) h

end ValuationSubring

end lift

end IsValExtension
