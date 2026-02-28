-- import Mathlib.Algebra.GroupWithZero.Action.Faithful
-- import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.Galois
-- import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.Dvr
import RamificationGroup.KroneckerWeber.Unramified
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.Tactic
-- import Mathlib.RingTheory.Henselian
-- import Mathlib.Algebra.Algebra.Subalgebra.Operations.lean

section Quotient

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

instance (H : Subgroup G) [H.Normal] :
    MulSemiringAction (G ⧸ H) (FixedPoints.subring B H) where
  smul := Quotient.lift (fun g x ↦ ⟨g • x, fun h ↦ by
    simpa [mul_smul] using congr(g • $(x.2 ⟨_, ‹H.Normal›.conj_mem' _ h.2 g⟩))⟩) (by
    rintro _ a ⟨⟨b, hb⟩, rfl⟩
    induction' b with b
    ext c
    simpa [mul_smul] using congr(a • $(c.2 ⟨b, hb⟩)))
  one_smul b := Subtype.ext (one_smul G b.1)
  mul_smul := Quotient.ind₂ fun _ _ _ ↦ Subtype.ext (mul_smul _ _ _)
  smul_zero := Quotient.ind fun _ ↦ Subtype.ext (smul_zero _)
  smul_add := Quotient.ind fun _ _ _ ↦ Subtype.ext (smul_add _ _ _)
  smul_one := Quotient.ind fun _ ↦ Subtype.ext (smul_one _)
  smul_mul := Quotient.ind fun _ _ _ ↦ Subtype.ext (MulSemiringAction.smul_mul _ _ _)

instance (H : Subgroup G) [H.Normal] :
    MulSemiringAction (G ⧸ H) (FixedPoints.subalgebra A B H) :=
  inferInstanceAs (MulSemiringAction (G ⧸ H) (FixedPoints.subring B H))

instance (H : Subgroup G) [H.Normal] :
    SMulCommClass (G ⧸ H) A (FixedPoints.subalgebra A B H)  where
  smul_comm := Quotient.ind fun g r h ↦ Subtype.ext (smul_comm g r h.1)

instance (H : Subgroup G) [H.Normal] [Algebra.IsInvariant A B G] :
    Algebra.IsInvariant A (FixedPoints.subalgebra A B H) (G ⧸ H) where
  isInvariant x hx := by
    obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) x.1
      (fun g ↦ congr_arg Subtype.val (hx g))
    exact ⟨y, Subtype.ext hy⟩

instance : Algebra.IsInvariant (FixedPoints.subring B G) B G where
  isInvariant x hx := ⟨⟨x, hx⟩, rfl⟩

instance : SMulCommClass G (FixedPoints.subring B G) B where
  smul_comm σ a b := by simp [Subring.smul_def, a.2 σ]

end Quotient

section normal

variable {A B k : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Finite G] [Group G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
  [CommRing k] [Algebra (A ⧸ P) k] [Algebra (B ⧸ Q) k] [IsScalarTower (A ⧸ P) (B ⧸ Q) k]
  [IsDomain k] [FaithfulSMul (B ⧸ Q) k]

attribute [local instance] Ideal.Quotient.field

include G in
lemma Ideal.Quotient.finiteDimensional_of_isInvariant [P.IsMaximal] [Q.IsMaximal]
    [SMulCommClass G A B]
    [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)] :
    FiniteDimensional (A ⧸ P) (B ⧸ Q) := by
  have : IsGalois (A ⧸ P) (B ⧸ Q) := { __ := Ideal.Quotient.normal (A := A) G P Q }
  letI : Finite (Gal((B ⧸ Q) / (A ⧸ P))) :=
    Finite.of_surjective _ (Ideal.Quotient.stabilizerHom_surjective G P Q)
  exact IsGalois.finiteDimensional_of_finite (F := A ⧸ P) (E := B ⧸ Q)

end normal

namespace Algebra.IsInvariant

open scoped Pointwise

variable {R S : Type*}[CommRing R] [CommRing S] [Algebra R S] (G : Type*)
    [Finite G] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [IsInvariant R S G]

lemma ncard_primesOver_mul_card_stabilizer (G : Type*) (p : Ideal R) [p.IsPrime]
    [Finite G] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [IsInvariant R S G]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] :
    (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
  rw [← Algebra.IsInvariant.orbit_eq_primesOver (A := R) (B := S) (G := G) p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

attribute [local instance 1001] Ideal.Quotient.field Module.Free.of_divisionRing
lemma ncard_primesOver_mul_card_inertia_mul_finrank (G : Type*) (p : Ideal R) [p.IsMaximal]
    [Finite G] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [IsInvariant R S G]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    (p.primesOver S).ncard * Nat.card (P.toAddSubgroup.inertia G) *
      Module.finrank (R ⧸ p) (S ⧸ P) = Nat.card G := by
  classical
  rw [mul_assoc, ← ncard_primesOver_mul_card_stabilizer G p P]
  cases nonempty_fintype G
  have : IsGalois (R ⧸ p) (S ⧸ P) := { __ := Ideal.Quotient.normal (A := R) G p P }
  have := Ideal.Quotient.finiteDimensional_of_isInvariant G p P
  congr 1
  have : Subgroup.index _ = _ := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (Ideal.Quotient.stabilizerHom P p G)
      (Ideal.Quotient.stabilizerHom_surjective G p P)).toEquiv
  rw [← IsGalois.card_aut_eq_finrank, ← this]
  convert (Ideal.Quotient.stabilizerHom P p G).ker.card_mul_index using 2
  have : (Ideal.Quotient.stabilizerHom P p G).ker = (P.toAddSubgroup.inertia G).subgroupOf _ := by
    ext σ
    simp [DFunLike.ext_iff, Ideal.Quotient.mk_surjective.forall, Ideal.Quotient.eq]
  rw [this]
  refine Nat.card_congr (Subgroup.subgroupOfEquivOfLe ?_).toEquiv.symm
  intro σ hσ
  ext x
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  convert P.add_mem_iff_right (inv_mem hσ x) (b := x) using 2
  simp

attribute [local instance 1001] Ideal.Quotient.field Module.Free.of_divisionRing
  FractionRing.liftAlgebra

open nonZeroDivisors

def _root_.AlgEquiv.extendScalarsOfIsLocalization {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (σ : S ≃ₐ[R] T)
    (M : Submonoid R) (Rₘ : Type*)
    [CommRing Rₘ] [Algebra Rₘ S] [Algebra Rₘ T]
    [Algebra R Rₘ] [IsScalarTower R Rₘ S] [IsScalarTower R Rₘ T] [IsLocalization M Rₘ] :
    S ≃ₐ[Rₘ] T where
  __ := σ
  commutes' r := by
    show ((σ.toAlgHom : S →+* T).comp (algebraMap Rₘ S)) r = _
    congr 1
    refine IsLocalization.ringHom_ext M ?_
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, AlgHom.comp_algebraMap]

@[simp]
lemma _root_.AlgEquiv.coe_extendScalarsOfIsLocalization {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (σ : S ≃ₐ[R] T)
    (M : Submonoid R) (Rₘ : Type*)
    [CommRing Rₘ] [Algebra Rₘ S] [Algebra Rₘ T]
    [Algebra R Rₘ] [IsScalarTower R Rₘ S] [IsScalarTower R Rₘ T] [IsLocalization M Rₘ] :
    (σ.extendScalarsOfIsLocalization M Rₘ : S → T) = σ := rfl

lemma isLocalization_fractionRing (G : Type*)
    [Finite G] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [IsInvariant R S G]
    (K : Type*) [Field K] [Algebra S K] [IsFractionRing S K] [FaithfulSMul R S]
    [IsDomain R] [IsDomain S] :
    IsLocalization (algebraMapSubmonoid S R⁰) K := by
  letI : Algebra.IsAlgebraic R S := (Algebra.IsInvariant.isIntegral R S G).isAlgebraic
  infer_instance

lemma isGalois_fractionRing (G : Type*)
    [Finite G] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [IsInvariant R S G]
    (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [FaithfulSMul R S] [IsDomain R] [IsDomain S] [Module.Finite R S] :
    IsGalois K L := by
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) L :=
    isLocalization_fractionRing G _
  haveI : FiniteDimensional K L :=
    by
      letI : Module.Finite K L := by
        simpa [Algebra.algebraMapSubmonoid] using
          (Module.Finite.of_isLocalization R S R⁰ : Module.Finite K L)
      infer_instance
  apply IsGalois.of_fixedField_eq_bot
  rw [← le_bot_iff]
  intro x hx
  obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (algebraMapSubmonoid S R⁰) x
  obtain ⟨x, rfl⟩ := IsInvariant.isInvariant (A := R) (G := G) x <| by
    intro σ
    have := hx ⟨(IsLocalization.algEquivOfAlgEquiv
      (M := algebraMapSubmonoid S R⁰) L
      (T := algebraMapSubmonoid S R⁰) L
      (MulSemiringAction.toAlgEquiv R S σ) (by
        have H : (MulDistribMulAction.toMonoidHom S σ).comp (algebraMap R S).toMonoidHom =
            (algebraMap R S).toMonoidHom :=
          MonoidHom.ext (MulSemiringAction.toAlgHom R S σ).commutes
        replace H := congr((R⁰).map $H)
        rwa [← Submonoid.map_map] at H)).extendScalarsOfIsLocalization R⁰ _, trivial⟩
    simpa [Subgroup.smul_def, IsFractionRing.algEquivOfAlgEquiv, IsLocalization.map_mk'] using
      congr(algebraMap S L (algebraMap R S s) * $this)
  use IsLocalization.mk' K x ⟨s, hs⟩
  have : FaithfulSMul R L := .of_injective (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective
  have H : algebraMap R L s ≠ 0 := by
    simpa [mem_nonZeroDivisors_iff_ne_zero] using hs
  simp [IsLocalization.eq_mk'_iff_mul_eq, ← IsScalarTower.algebraMap_apply, H]

lemma surjective_galRestrict_comp_galRestrict_symm
    (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [IsDomain R] [IsDomain S]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [Algebra.IsAlgebraic K L]
    [FaithfulSMul R S] [Module.Finite R S] [NoZeroSMulDivisors R S] :
    Function.Surjective ((galRestrict R K L S).symm.toMonoidHom.comp
      (MulSemiringAction.toAlgAut G R S)) := by
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) L :=
    isLocalization_fractionRing G _
  haveI : FiniteDimensional K L :=
    by
      letI : Module.Finite K L := by
        simpa [Algebra.algebraMapSubmonoid] using
          (Module.Finite.of_isLocalization R S R⁰ : Module.Finite K L)
      infer_instance
  have : IsGalois K L :=
    isGalois_fractionRing G (R := R) (S := S) _ _
  have : FaithfulSMul R L := .of_injective (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective
  rw [← MonoidHom.range_eq_top]
  have hrange : ⊤ ≤ ((galRestrict R K L S).symm.toMonoidHom.comp
      (MulSemiringAction.toAlgAut G R S)).range := by
    have hfixed : IntermediateField.fixedField ((galRestrict R K L S).symm.toMonoidHom.comp
        (MulSemiringAction.toAlgAut G R S)).range ≤ ⊥ := by
      intro x hx
      wlog hx' : x ∈ (algebraMap S _).range generalizing x
      · obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ :=
          IsLocalization.exists_mk'_eq (algebraMapSubmonoid S R⁰) x
        have H : algebraMap S L x ∈ IntermediateField.fixedField
          ((galRestrict R K L S).symm.toMonoidHom.comp (MulSemiringAction.toAlgAut G R S)).range := by
          convert IntermediateField.smul_mem _ (x := algebraMap R K s) hx
          rw [algebraMap_smul, ← algebraMap_smul S, Algebra.smul_def, IsLocalization.mk'_spec'_mk]
        obtain ⟨y, e : algebraMap _ _ y = _⟩ := this H ⟨x, rfl⟩
        refine ⟨y * IsLocalization.mk' _ 1 ⟨s, hs⟩, ?_⟩
        have H0 : algebraMap R L s ≠ 0 := by simpa using hs
        simp [IsLocalization.eq_mk'_iff_mul_eq, ← IsScalarTower.algebraMap_apply, H0, e]
      rcases hx' with ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := IsInvariant.isInvariant (A := R) (G := G) x fun σ ↦ by
        apply IsFractionRing.injective (R := S) (K := L)
        have hσ :
            (galRestrict R K L S).symm (MulSemiringAction.toAlgAut G R S σ) (algebraMap S L x) =
              algebraMap S L x := by
          simpa [Subgroup.smul_def] using hx ⟨_, σ, rfl⟩
        have hσ' :
            (galRestrict R K L S).symm (MulSemiringAction.toAlgAut G R S σ) (algebraMap S L x) =
              algebraMap S L (σ • x) := by
          simpa [Subgroup.smul_def] using
            (galRestrict_symm_algebraMap_apply (A := R) (K := K) (L := L) (B := S)
              (MulSemiringAction.toAlgAut G R S σ) x)
        exact hσ'.symm.trans hσ
      refine ⟨algebraMap _ _ x, by simp [← IsScalarTower.algebraMap_apply]⟩
    have hfixed' : IntermediateField.fixedField ((galRestrict R K L S).symm.toMonoidHom.comp
        (MulSemiringAction.toAlgAut G R S)).range ≤
        IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by
      simpa using hfixed
    exact (IsGalois.intermediateFieldEquivSubgroup (F := K) (E := L)).symm.le_iff_le.mp hfixed'
  have hle : ((galRestrict R K L S).symm.toMonoidHom.comp
      (MulSemiringAction.toAlgAut G R S)).range ≤ (⊤ : Subgroup Gal(L/K)) := by
    intro σ hσ
    simp
  exact le_antisymm hle hrange

lemma surjective_toAlgAut
    [IsDomain R] [IsDomain S]
    [FaithfulSMul R S] [Module.Finite R S] [NoZeroSMulDivisors R S]
    [IsIntegrallyClosed S] :
    Function.Surjective (MulSemiringAction.toAlgAut G R S) := by
  convert (galRestrict R (FractionRing R) (FractionRing S) S).surjective.comp
    (surjective_galRestrict_comp_galRestrict_symm (R := R) (S := S) G _ _)
  ext
  simp

lemma bijective_toAlgAut [FaithfulSMul G S]
    [IsDomain R] [IsDomain S]
    [FaithfulSMul R S] [Module.Finite R S] [NoZeroSMulDivisors R S]
    [IsIntegrallyClosed S]  :
    Function.Bijective (MulSemiringAction.toAlgAut G R S) := by
  constructor
  · intro σ₁ σ₂ H
    exact FaithfulSMul.eq_of_smul_eq_smul (α := S) fun x ↦ DFunLike.congr_fun H x
  · exact surjective_toAlgAut G

lemma bijective_galRestrict_comp_galRestrict_symm [FaithfulSMul G S]
    (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [IsDomain R] [IsDomain S]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [Algebra.IsAlgebraic K L]
    [FaithfulSMul R S] [Module.Finite R S] [NoZeroSMulDivisors R S] :
    Function.Bijective ((galRestrict R K L S).symm.toMonoidHom.comp
      (MulSemiringAction.toAlgAut G R S)) := by
  refine ⟨(galRestrict R K L S).symm.injective.comp ?_,
    surjective_galRestrict_comp_galRestrict_symm G _ _⟩
  intro σ₁ σ₂ H
  exact FaithfulSMul.eq_of_smul_eq_smul (α := S) fun x ↦ DFunLike.congr_fun H x

lemma finrank_eq_card [FaithfulSMul G S]
    (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [IsDomain R] [IsDomain S]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [Algebra.IsAlgebraic K L]
    [FaithfulSMul R S] [Module.Finite R S] [NoZeroSMulDivisors R S] :
    Module.finrank K L = Nat.card G := by
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) L :=
    isLocalization_fractionRing G _
  haveI : FiniteDimensional K L :=
    by
      letI : Module.Finite K L := by
        simpa [Algebra.algebraMapSubmonoid] using
          (Module.Finite.of_isLocalization R S R⁰ : Module.Finite K L)
      infer_instance
  have : IsGalois K L :=
    isGalois_fractionRing G (R := R) (S := S) _ _
  calc
    Module.finrank K L = Nat.card Gal(L/K) := (IsGalois.card_aut_eq_finrank K L).symm
    _ = Nat.card G := by
      symm
      exact Nat.card_congr (.ofBijective _
        (bijective_galRestrict_comp_galRestrict_symm (R := R) (S := S) G L K))

lemma ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (p : Ideal R) (hp : p ≠ ⊥) [p.IsMaximal]
    [FaithfulSMul G S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [NoZeroSMulDivisors R S] :
    (p.primesOver S).ncard * (p.ramificationIdxIn S * p.inertiaDegIn S) = Nat.card G := by
  letI : IsGaloisGroup G R S :=
    { faithful := inferInstance, commutes := inferInstance, isInvariant := inferInstance }
  simpa using
    (Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (A := R) (p := p) hp S G)

include G in
lemma ramificationIdxIn_eq_ramificationIdx
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.LiesOver p] [P.IsPrime]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S] :
    p.ramificationIdxIn S = p.ramificationIdx (algebraMap R S) P := by
  have h : ∃ Q : Ideal S, Q.IsPrime ∧ Q.LiesOver p := ⟨P, inferInstance, inferInstance⟩
  rw [Ideal.ramificationIdxIn, dif_pos h]
  let Q : Ideal S := h.choose
  letI : Q.IsPrime := (h.choose_spec).1
  letI : Q.LiesOver p := (h.choose_spec).2
  have hQunder : Q.under R = P.under R := by
    exact (show Q.under R = p from (inferInstance : Q.LiesOver p).over.symm).trans
      (show p = P.under R from ‹P.LiesOver p›.over)
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R S G Q P hQunder
  rw [hσ]
  exact (Ideal.ramificationIdx_map_eq (R := R) (S := S) (S₁ := S) (p := p)
    Q (MulSemiringAction.toAlgEquiv R S σ)).symm

include G in
lemma inertiaDegIn_eq_inertiaDeg
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.LiesOver p] [P.IsPrime]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S] :
    p.inertiaDegIn S = p.inertiaDeg P := by
  have h : ∃ Q : Ideal S, Q.IsPrime ∧ Q.LiesOver p := ⟨P, inferInstance, inferInstance⟩
  rw [Ideal.inertiaDegIn, dif_pos h]
  let Q : Ideal S := h.choose
  letI : Q.IsPrime := (h.choose_spec).1
  letI : Q.LiesOver p := (h.choose_spec).2
  have hQunder : Q.under R = P.under R := by
    exact (show Q.under R = p from (inferInstance : Q.LiesOver p).over.symm).trans
      (show p = P.under R from ‹P.LiesOver p›.over)
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R S G Q P hQunder
  rw [hσ]
  exact (Ideal.inertiaDeg_map_eq (R := R) (S := S) (S₁ := S) (p := p)
    Q (MulSemiringAction.toAlgEquiv R S σ)).symm

set_option maxHeartbeats 0 in
lemma card_inertia (p : Ideal R) (hp : p ≠ ⊥) [p.IsMaximal]
    [FaithfulSMul G S]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [NoZeroSMulDivisors R S]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (P.toAddSubgroup.inertia G) =
      Ideal.ramificationIdx (algebraMap R S) p P := by
  have := ncard_primesOver_mul_card_inertia_mul_finrank G p P
  rw [mul_right_comm] at this
  apply mul_right_injective₀ (a := (p.primesOver S).ncard * Module.finrank (R ⧸ p) (S ⧸ P))
  · intro e
    simp [e, eq_comm, Nat.card_eq_zero, ← not_finite_iff_infinite, ‹Finite G›] at this
  · simp only [this]
    rw [← Ideal.inertiaDeg_algebraMap]
    have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (R := R) (S := S) G _ hp
    rwa [← mul_assoc, mul_right_comm,
      ramificationIdxIn_eq_ramificationIdx G p P,
      inertiaDegIn_eq_inertiaDeg G p P, eq_comm] at this

attribute [local instance] Ideal.Quotient.field in
instance (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] : Algebra.IsSeparable p.ResidueField P.ResidueField :=
  inferInstance

open IntermediateField Pointwise in
lemma inertiaDeg_eq_inertia_relindex (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G] [SMulCommClass G A B]
    (P : Ideal B) (p : Ideal A) [P.LiesOver p] [p.IsPrime] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    Ideal.inertiaDeg p P = (P.toAddSubgroup.inertia G).relIndex (MulAction.stabilizer G P) := by
  have := Algebra.IsInvariant.isIntegral A B G
  have : p.IsMaximal := by
    rw [‹P.LiesOver p›.1]; exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) P
  have : IsGalois (A ⧸ p) (B ⧸ P) := { __ := Ideal.Quotient.normal (A := A) G p P }
  letI : Finite Gal((B ⧸ P)/(A ⧸ p)) := by
    exact Finite.of_surjective _ (Ideal.Quotient.stabilizerHom_surjective G p P)
  have : FiniteDimensional (A ⧸ p) (B ⧸ P) :=
    IsGalois.finiteDimensional_of_finite (F := A ⧸ p) (E := B ⧸ P)
  rw [Ideal.inertiaDeg_algebraMap, ← IsGalois.card_aut_eq_finrank, Subgroup.relIndex, Subgroup.index]
  simpa using
    (Nat.card_congr (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv).symm

lemma isUnramifiedAt_of_isInvariant_inertia
    {R S T G : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Finite G] [Group G] [MulSemiringAction G T]
    [SMulCommClass G R T] [FaithfulSMul G T]
    (P : Ideal T) [P.IsMaximal] (hP : P ≠ ⊥)
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R T]
    [NoZeroSMulDivisors R T]
    [NoZeroSMulDivisors S T]
    [Algebra.IsSeparable (R ⧸ P.under R) (T ⧸ P)]
    [IsInvariant R T G]
    [IsInvariant S T (P.toAddSubgroup.inertia G)]
    [SMulCommClass (P.toAddSubgroup.inertia G) S T] [IsDedekindDomain T] :
    Algebra.IsUnramifiedAt R (P.under S) := by
  have : Module.Finite S T := .of_restrictScalars_finite R S T
  have : Module.Finite R S := Module.Finite.of_injective (IsScalarTower.toAlgHom R S T).toLinearMap
    (FaithfulSMul.algebraMap_injective _ _)
  have hp' : P.under R ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP
  have hp'' : P.under S ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP
  letI : IsScalarTower (R ⧸ P.under R) (S ⧸ P.under S) (T ⧸ P) :=
    IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
  have : Algebra.IsSeparable (S ⧸ P.under S) (T ⧸ P) :=
    Algebra.isSeparable_tower_top_of_isSeparable (R ⧸ P.under R) _ _
  have : Algebra.IsSeparable (R ⧸ P.under R) (S ⧸ P.under S) :=
    Algebra.isSeparable_tower_bot_of_isSeparable (R ⧸ P.under R) _ (T ⧸ P)
  have h1 : ((Ideal.under S P).primesOver T).ncard = 1 := by
    simp only [Set.ncard_eq_one, Set.ext_iff, Set.mem_singleton_iff]
    refine ⟨P, fun Q ↦ ⟨fun H ↦ ?_, fun e ↦ ⟨e ▸ inferInstanceAs P.IsPrime,
      e ▸ inferInstanceAs (P.LiesOver (P.under S))⟩⟩⟩
    have := H.1
    obtain ⟨σ, rfl⟩ := Algebra.IsInvariant.exists_smul_of_under_eq S T
      (P.toAddSubgroup.inertia G) P Q H.2.1
    ext x
    simpa [Ideal.mem_pointwise_smul_iff_inv_smul_mem] using
      Ideal.add_mem_iff_left (a := x) _ ((σ⁻¹).2 x)
  have : (P.under S).LiesOver (P.under R) := ⟨by rw [Ideal.under_under]⟩
  have h2 : (Ideal.under S P).inertiaDegIn T = 1 := by
    rw [inertiaDegIn_eq_inertiaDeg (P.toAddSubgroup.inertia G) (P.under S) P]
    rw [inertiaDeg_eq_inertia_relindex (G := (P.toAddSubgroup.inertia G)) (A := S) (B := T)]
    simp +contextual [SetLike.le_def]
  letI : IsGaloisGroup (P.toAddSubgroup.inertia G) S T :=
    { faithful := inferInstance, commutes := inferInstance, isInvariant := inferInstance }
  have hmul := Algebra.IsInvariant.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (R := S) (S := T) (G := P.toAddSubgroup.inertia G) (P.under S) hp''
  rw [h1, h2, one_mul, mul_one,
    Algebra.IsInvariant.card_inertia (R := R) (S := T) (G := G) (P.under R) hp' P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (A := S) (B := T) (p := Ideal.under S P)
      (P := P) (G := P.toAddSubgroup.inertia G),
    Ideal.ramificationIdx_algebra_tower (p := P.under R) (P := P.under S)] at hmul
  have hramT : Ideal.ramificationIdx (algebraMap S T) (P.under S) P ≠ 0 := by
    refine Ideal.IsDedekindDomain.ramificationIdx_ne_zero ?_ inferInstance Ideal.map_comap_le
    exact Ideal.map_ne_bot_of_ne_bot hp''
  have hramS : Ideal.ramificationIdx (algebraMap R S) (P.under R) (P.under S) = 1 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hramT)
    simpa [Ideal.under_under, one_mul] using hmul.symm
  rw [isUnramifiedAt_iff_map_eq2 (p := P.under R)]
  refine ⟨inferInstance, ?_⟩
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hp'' Ideal.map_comap_le]
  exact hramS

def _root_.AlgHom.extendScalarsOfIsLocalization {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (σ : S →ₐ[R] T)
    (M : Submonoid R) (Rₘ : Type*)
    [CommRing Rₘ] [Algebra Rₘ S] [Algebra Rₘ T]
    [Algebra R Rₘ] [IsScalarTower R Rₘ S] [IsScalarTower R Rₘ T] [IsLocalization M Rₘ] :
    S →ₐ[Rₘ] T where
  __ := σ
  commutes' r := by
    show ((σ : S →+* T).comp (algebraMap Rₘ S)) r = _
    congr 1
    refine IsLocalization.ringHom_ext M ?_
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, AlgHom.comp_algebraMap]

@[simp]
lemma _root_.AlgHom.coe_extendScalarsOfIsLocalization {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (σ : S →ₐ[R] T)
    (M : Submonoid R) (Rₘ : Type*)
    [CommRing Rₘ] [Algebra Rₘ S] [Algebra Rₘ T]
    [Algebra R Rₘ] [IsScalarTower R Rₘ S] [IsScalarTower R Rₘ T] [IsLocalization M Rₘ] :
    (σ.extendScalarsOfIsLocalization M Rₘ : S → T) = σ := rfl

noncomputable
def IsLocalization.stabilizerHom (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] :
    MulAction.stabilizer G P →*
      (Localization.AtPrime P ≃ₐ[Localization.AtPrime p] Localization.AtPrime P) :=
  letI f : MulAction.stabilizer G P →*
    (Localization.AtPrime P →ₐ[Localization.AtPrime p] Localization.AtPrime P) :=
  { toFun σ := .extendScalarsOfIsLocalization
      ({ toRingHom := IsLocalization.map (M := P.primeCompl) (T := P.primeCompl) _
          (MulSemiringAction.toRingAut _ _ σ.1).toRingHom (by
            intro x hx
            show σ • x ∉ P
            convert (Ideal.smul_mem_pointwise_smul_iff (a := σ.1)).not.mpr hx
            exact σ.2.symm)
         commutes' r := by convert IsLocalization.map_eq _ (algebraMap R _ r); simp; rfl })
         p.primeCompl _
    map_one' := by
      ext
      dsimp [-MulSemiringAction.toRingAut_apply]
      simp_rw [map_one]
      exact IsLocalization.map_id _ _
    map_mul' f g := by
      ext
      dsimp [-MulSemiringAction.toRingAut_apply]
      simp_rw [map_mul]
      refine .trans ?_ (IsLocalization.map_map _ _ _).symm
      rfl }
  (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp f.toHomUnits

end Algebra.IsInvariant

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B]

attribute [local instance 1001] Ideal.Quotient.field Module.Free.of_divisionRing

open IntermediateField in
include G in
lemma bijective_quotient_of_inertia_eq_top [Algebra.IsInvariant A B G] [SMulCommClass G A B]
    (P : Ideal B) (p : Ideal A) [P.LiesOver p] [p.IsPrime] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (H : P.toAddSubgroup.inertia G = ⊤) :
    Function.Bijective (algebraMap (A ⧸ p) (B ⧸ P)) := by
  have := Algebra.IsInvariant.isIntegral A B G
  have : p.IsMaximal := by
    rw [‹P.LiesOver p›.1]; exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) P
  have : IsGalois (A ⧸ p) (B ⧸ P) := { __ := Ideal.Quotient.normal (A := A) G p P }
  letI : Finite Gal((B ⧸ P)/(A ⧸ p)) := by
    exact Finite.of_surjective _ (Ideal.Quotient.stabilizerHom_surjective G p P)
  have : FiniteDimensional (A ⧸ p) (B ⧸ P) :=
    IsGalois.finiteDimensional_of_finite (F := A ⧸ p) (E := B ⧸ P)
  refine ⟨RingHom.injective _, fun x ↦ ?_⟩
  suffices (⊤ : IntermediateField (A ⧸ p) (B ⧸ P)) = ⊥ from this.le trivial
  rw [←  IntermediateField.finrank_eq_one_iff, IntermediateField.finrank_top',
    ← IsGalois.card_aut_eq_finrank, Nat.card_eq_one_iff_exists]
  refine ⟨1, ?_⟩
  intro σ
  obtain ⟨τ, hτ⟩ := Ideal.Quotient.stabilizerHom_surjective G p P (σ.liftNormal (B ⧸ P))
  ext x
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (algebraMap _ (B ⧸ P) x)
  have H₁ := DFunLike.congr_fun hτ (algebraMap _ _ x)
  simp_rw [AlgEquiv.liftNormal_commutes, ← hy, Ideal.Quotient.stabilizerHom_apply,
    Subgroup.smul_def] at H₁
  simpa [← Ideal.Quotient.eq, H₁, hy] using H.ge (Subgroup.mem_top τ.1) y

variable (P : Ideal B) [P.IsMaximal]

local notation "Bᴵ" => FixedPoints.subring B (P.toAddSubgroup.inertia G)

include G in
lemma exists_mem_fixedPoints_inertia_sub_mem
    [Algebra.IsSeparable (Bᴵ ⧸ P.under Bᴵ) (B ⧸ P)] (x : B) :
    ∃ y ∈ Bᴵ, x - y ∈ P := by
  obtain ⟨y, hy⟩ := (bijective_quotient_of_inertia_eq_top Bᴵ B (P.toAddSubgroup.inertia G) P
    (P.under _) (by simp [SetLike.ext_iff])).2 (Ideal.Quotient.mk P x)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨y.1, y.2, Ideal.Quotient.eq.mp hy.symm⟩
