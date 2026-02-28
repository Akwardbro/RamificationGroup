import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Asymptotics

theorem nhds_neg_aux {x : ℝ} {k : Set ℝ} (h : k ∈ nhds x) : -k ∈ nhds (-x) := by
  rw [mem_nhds_iff] at *
  obtain ⟨m, hm1, hm2, hm3⟩ := h
  use -m
  constructor
  · simp only [Set.neg_subset_neg, hm1]
  · constructor
    · exact IsOpen.neg hm2
    · exact Set.neg_mem_neg.mpr hm3

theorem ContinuousOn_inv_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → E} {a b : ℝ} (hf : ∀x : ℝ, f x = g (-x)) (fcont : ContinuousOn f (Set.Icc a b)) : ContinuousOn g (Set.Icc (-b) (-a)) := by
  dsimp [ContinuousOn, ContinuousWithinAt, Tendsto]
  intro x hx
  have h' : g x = f (-x) := by rw [hf (-x), neg_neg]
  have h : Filter.map g (nhdsWithin x (Set.Icc (-b) (-a))) = Filter.map f (nhdsWithin (-x) (Set.Icc a b)) := by
    ext t
    constructor
    <;> intro ht
    · obtain ⟨k, hk1, hk2⟩ := ht
      use -k
      constructor
      · apply nhds_neg_aux hk1
      · obtain ⟨c, hc1, hc2⟩ := hk2
        use -c
        constructor
        · rw [mem_principal] at *
          have h'' : Set.Icc (-b) (-a) = -(Set.Icc a b) := by apply Eq.symm (Set.neg_Icc a b)
          rw [h''] at hc1
          exact Set.neg_subset.mp hc1
        · rw [Set.preimage] at *
          have h'' : {x | f x ∈ t} = -{x | g x ∈ t} := by
            ext k
            simp only [Set.mem_setOf_eq, Set.mem_neg]
            constructor
            <;> intro hk
            · rw [← hf k]
              exact hk
            · rw [hf k]
              exact hk
          have h''' : -k ∩ -c = - (k ∩ c) := by exact rfl
          rw [h'', h''']
          exact congrArg Neg.neg hc2
    · obtain ⟨k, hk1, hk2⟩ := ht
      use -k
      constructor
      · rw [← neg_neg x]
        apply nhds_neg_aux hk1
      · obtain ⟨c, hc1, hc2⟩ := hk2
        use -c
        constructor
        · rw [mem_principal] at *
          have h'' : Set.Icc (-b) (-a) = -(Set.Icc a b) := by apply Eq.symm (Set.neg_Icc a b)
          rw [h'']
          simp only [Set.neg_subset_neg, hc1]
        · rw [Set.preimage] at *
          have h'' : -{x | f x ∈ t} = {x | g x ∈ t} := by
            ext k
            simp only [Set.mem_setOf_eq, Set.mem_neg]
            constructor
            <;> intro hk
            · rw [← neg_neg k, ← hf (-k)]
              exact hk
            · rw [hf (-k), neg_neg]
              exact hk
          have h''' : -k ∩ -c = - (k ∩ c) := by exact rfl
          rw [←h'', h''']
          exact congrArg Neg.neg hc2
  rw [h, h']
  apply fcont
  apply Set.mem_neg.1
  rw [Set.neg_Icc]
  apply hx


theorem HasDerivWithinAt_inv_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f finv f' finv' : ℝ → E} {a b : ℝ} (derivf : ∀ x ∈ Set.Ioc a b, HasDerivWithinAt f (f' x) (Set.Iic x) x) (h : ∀ x : ℝ, f x = finv (-x)) (h' : ∀ x : ℝ, f' x = - finv' (-x)) : ∀ x ∈ Set.Ico (-b) (-a), HasDerivWithinAt finv (finv' x) (Set.Ici x) x := by
  intro x hx
  have hx' : -x ∈ Set.Ioc a b := by
    rcases hx with ⟨hx1, hx2⟩
    constructor <;> linarith
  have hmaps : Set.MapsTo (fun t : ℝ => -t) (Set.Ici x) (Set.Iic (-x)) := by
    intro t ht
    exact neg_le_neg (show x ≤ t from ht)
  have hcomp :
      HasDerivWithinAt (fun t : ℝ => f (-t)) ((-1 : ℝ) • f' (-x)) (Set.Ici x) x := by
    simpa [Function.comp] using
      (HasDerivWithinAt.scomp (x := x) (derivf (-x) hx')
        (hasDerivWithinAt_neg x (Set.Ici x)) hmaps)
  have hfun : (fun t : ℝ => f (-t)) = finv := by
    funext t
    simpa using (h (-t))
  have hderiv : ((-1 : ℝ) • f' (-x)) = finv' x := by
    have hfx : f' (-x) = -finv' x := by simpa [neg_neg] using h' (-x)
    calc
      ((-1 : ℝ) • f' (-x)) = -f' (-x) := by simp
      _ = -(-finv' x) := by rw [hfx]
      _ = finv' x := by simp
  simpa [hfun, hderiv] using hcomp

theorem eq_of_has_deriv_left_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ} {f' g : ℝ → E} (derivf : ∀ x ∈ Set.Ioc a b, HasDerivWithinAt f (f' x) (Set.Iic x) x) (derivg : ∀ x ∈ Set.Ioc a b, HasDerivWithinAt g (f' x) (Set.Iic x) x) (fcont : ContinuousOn f (Set.Icc a b)) (gcont : ContinuousOn g (Set.Icc a b)) (hi : f b = g b) (y : ℝ) : y ∈ Set.Icc a b → f y = g y := by
  let finv : ℝ → E := fun x => f (-x)
  let ginv : ℝ → E := fun x => g (-x)
  let finv' : ℝ → E := fun x => - f' (-x)
  have h : ∀x : ℝ, x ∈ Set.Icc (-b) (-a) → finv x = ginv x := by
    apply eq_of_has_deriv_right_eq (f' := finv')
    · apply HasDerivWithinAt_inv_aux derivf
      · intro x
        dsimp [finv]
        simp only [neg_neg]
      · intro x
        dsimp [finv']
        simp only [neg_neg]
    · apply HasDerivWithinAt_inv_aux derivg
      · intro x
        dsimp [ginv]
        simp only [neg_neg]
      · intro x
        dsimp [finv']
        simp only [neg_neg]
    · apply ContinuousOn_inv_aux (f := f) (g := finv) _ fcont
      intro x
      dsimp [finv]
      simp only [neg_neg]
    · apply ContinuousOn_inv_aux (f := g) (g := ginv) _ gcont
      intro x
      dsimp [ginv]
      simp only [neg_neg]
    · dsimp [finv, ginv]
      simp only [neg_neg, hi]
  intro hy
  have h' : finv (-y) = ginv (-y) := by
    apply h
    simp only [Set.mem_Icc, neg_le_neg_iff, And.comm]
    rw [← Set.mem_Icc (α := ℝ) (a := a) (b := b) (x := y)]
    exact hy
  dsimp [finv, ginv] at h'
  simp only [neg_neg] at h'
  exact h'
