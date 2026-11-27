/-
  T-H: the parametric Hadamard lemma and compact bounds for partial derivatives.

  If f : ℝ × Y → Z is smooth and f(0, y) = 0, then f(h, y) = h • g(h, y) with
  g(h, y) = ∫₀¹ ∂ₕf(sh, y) ds smooth and g(0, y) = ∂ₕf(0, y).
-/
import Sympnet.Smoothing.SymplecticApprox

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace SympNet

section Hadamard

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- Partial derivative in the first (real) variable. -/
def dT (f : ℝ × Y → Z) (p : ℝ × Y) : Z := fderiv ℝ f p (1, 0)

omit [CompleteSpace Z] in
theorem contDiff_dT {f : ℝ × Y → Z} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dT f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The Hadamard quotient `g(h, y) = ∫₀¹ ∂ₕf(sh, y) ds`. -/
def hadQ (f : ℝ × Y → Z) (p : ℝ × Y) : Z := ∫ s in (0 : ℝ)..1, dT f (s * p.1, p.2)

theorem contDiff_hadQ {f : ℝ × Y → Z} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (hadQ f) := by
  have h : hadQ f = fun p => ∫ s in Ioc (0 : ℝ) 1, (fun p (s : ℝ) => dT f (s * p.1, p.2)) p s := by
    funext p; simp only [hadQ, intervalIntegral.integral_of_le zero_le_one]
  rw [h]
  refine ContDiff.parametric_integral (k := Icc 0 1) isCompact_Icc Ioc_subset_Icc_self
    (by simp) ?_
  exact (contDiff_dT hf).comp ((contDiff_snd.mul (contDiff_fst.comp contDiff_fst)).prodMk
    (contDiff_snd.comp contDiff_fst))

theorem hadQ_zero {f : ℝ × Y → Z} (y : Y) : hadQ f (0, y) = dT f (0, y) := by
  simp [hadQ]

/-- **Hadamard's lemma.** -/
theorem hadamard_eq {f : ℝ × Y → Z} (hf : ContDiff ℝ ∞ f) (h0 : ∀ y, f (0, y) = 0)
    (p : ℝ × Y) : f p = p.1 • hadQ f p := by
  obtain ⟨t, y⟩ := p
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (s * t, y)) (t • dT f (s * t, y)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => ((s * t, y) : ℝ × Y)) ((t, 0) : ℝ × Y) s := by
      refine HasDerivAt.prodMk ?_ (hasDerivAt_const _ _)
      simpa using (hasDerivAt_id s).mul_const t
    have h2 := ((hf.differentiable (by simp)) (s * t, y)).hasFDerivAt.comp_hasDerivAt s h1
    have e : ((t, 0) : ℝ × Y) = t • ((1, 0) : ℝ × Y) := by simp
    rw [e, map_smul] at h2
    exact h2
  have hc : Continuous fun s : ℝ => t • dT f (s * t, y) :=
    continuous_const.smul ((contDiff_dT hf).continuous.comp
      ((continuous_id.mul continuous_const).prodMk continuous_const))
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  simp only [one_mul, zero_mul, h0, sub_zero] at this
  rw [← this, intervalIntegral.integral_smul]
  rfl

/-- Second-order Hadamard: if moreover ∂ₕf(0, ·) = 0 then f(h, y) = h² • g₂(h, y). -/
theorem hadamard2_eq {f : ℝ × Y → Z} (hf : ContDiff ℝ ∞ f) (h0 : ∀ y, f (0, y) = 0)
    (h1 : ∀ y, dT f (0, y) = 0) (p : ℝ × Y) : f p = (p.1 ^ 2) • hadQ (hadQ f) p := by
  rw [hadamard_eq hf h0 p, hadamard_eq (contDiff_hadQ hf) (fun y => by rw [hadQ_zero, h1]) p,
    smul_smul, sq]

end Hadamard

/-! ### Partial iterated derivatives and compact bounds -/

section Partial

variable {P Y Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The partial iterated derivative in `y` is bounded by the full iterated derivative. -/
theorem norm_iteratedFDeriv_partial_le {F : P × Y → Z} {n : ℕ∞ω} (hF : ContDiff ℝ n F)
    {l : ℕ} (hl : (l : ℕ∞ω) ≤ n) (c : P) (y : Y) :
    ‖iteratedFDeriv ℝ l (fun y => F (c, y)) y‖ ≤ ‖iteratedFDeriv ℝ l F (c, y)‖ := by
  have e : (fun y => F (c, y)) =
      (fun w => F ((c, 0) + w)) ∘ (ContinuousLinearMap.inr ℝ P Y) := by
    funext y; simp
  have hF' : ContDiff ℝ n (fun w => F ((c, 0) + w)) := hF.comp (contDiff_const.add contDiff_id)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hF' y hl,
    iteratedFDeriv_comp_add_left]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin l, ‖ContinuousLinearMap.inr ℝ P Y‖ ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ P Y)
  calc _ ≤ ‖iteratedFDeriv ℝ l F ((c, 0) + (ContinuousLinearMap.inr ℝ P Y) y)‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by simp

/-- Compact bound for all partial iterated derivatives of order ≤ k. -/
theorem exists_partial_bound {F : P × Y → Z} (hF : ContDiff ℝ ∞ F) (k : ℕ) {S : Set (P × Y)}
    (hS : IsCompact S) : ∃ C, 0 ≤ C ∧ ∀ p ∈ S, ∀ l ≤ k,
      ‖iteratedFDeriv ℝ l (fun y => F (p.1, y)) p.2‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_crBound k hS (hF.of_le (by exact_mod_cast le_top))
  refine ⟨C, hC0, fun p hp l hl => ?_⟩
  refine (norm_iteratedFDeriv_partial_le hF (by exact_mod_cast le_top) p.1 p.2).trans ?_
  exact hC l hl p hp

end Partial

end SympNet
