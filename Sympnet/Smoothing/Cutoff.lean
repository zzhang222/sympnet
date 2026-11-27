/-
  C3: smooth cutoffs with derivative bounds depending only on the gap.

  For ρ > 0 there is M such that every set T has a smooth χ with χ = 1 on the (ρ/4)-thickening
  of T, support in the (3ρ/4)-thickening, and ‖D^j χ‖ ≤ M for j ≤ 2. Construction: convolve the
  indicator of the (ρ/2)-thickening with a fixed normalized bump of radius ρ/4.
-/
import Sympnet.SympNetUniversal

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff Convolution

noncomputable section

namespace SympNet

section Conv
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V] {μ : Measure V} [μ.IsAddHaarMeasure] [μ.IsNegInvariant]
  {F' G' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedAddCommGroup G']
  [NormedSpace ℝ G']

/-- ‖(f ⋆[L] g) z‖ ≤ ‖L‖ ∫‖g‖ when |f| ≤ 1. -/
theorem norm_convolution_le_of_abs_le_one {f : V → ℝ} {g : V → F'} (L : ℝ →L[ℝ] F' →L[ℝ] G')
    (hf : ∀ t, |f t| ≤ 1) (hfm : AEStronglyMeasurable f μ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (z : V) :
    ‖(f ⋆[L, μ] g) z‖ ≤ ‖L‖ * ∫ t, ‖g t‖ ∂μ := by
  have hgi : Integrable g μ := hg.integrable_of_hasCompactSupport hgc
  have hshift : Integrable (fun t => ‖g (z - t)‖) μ := (hgi.comp_sub_left z).norm
  rw [convolution_def]
  calc ‖∫ t, L (f t) (g (z - t)) ∂μ‖ ≤ ∫ t, ‖L‖ * ‖g (z - t)‖ ∂μ := by
        refine norm_integral_le_of_norm_le (hshift.const_mul _) (Eventually.of_forall fun t => ?_)
        calc ‖L (f t) (g (z - t))‖ ≤ ‖L‖ * ‖f t‖ * ‖g (z - t)‖ := L.le_opNorm₂ _ _
          _ ≤ ‖L‖ * 1 * ‖g (z - t)‖ := by
              gcongr; rw [Real.norm_eq_abs]; exact hf t
          _ = ‖L‖ * ‖g (z - t)‖ := by ring
    _ = ‖L‖ * ∫ t, ‖g t‖ ∂μ := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun t => ‖g t‖) μ z

end Conv

variable {d : ℕ}

local notation "μH" => (Measure.addHaar : Measure (X d))

theorem thickening_mono_of_dist {T : Set (X d)} {a b : ℝ} {z t : X d}
    (hz : z ∈ thickening a T) (ht : dist z t < b) : t ∈ thickening (a + b) T := by
  rw [mem_thickening_iff] at hz ⊢
  obtain ⟨y, hy, hzy⟩ := hz
  exact ⟨y, hy, by linarith [dist_triangle_left t y z]⟩

set_option maxSynthPendingDepth 6 in
/-- **Uniform cutoffs.** -/
theorem exists_cutoff {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ M : ℝ, ∀ T : Set (X d), ∃ χ : X d → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ z ∈ thickening (ρ / 4) T, χ z = 1) ∧ Function.support χ ⊆ thickening (3 * ρ / 4) T ∧
      ∀ z, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j χ z‖ ≤ M := by
  let φ : ContDiffBump (0 : X d) := ⟨ρ / 8, ρ / 4, by positivity, by linarith⟩
  set ψ : X d → ℝ := φ.normed μH
  have hψs : ContDiff ℝ ∞ ψ := φ.contDiff_normed
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hψ1 : HasCompactSupport (fderiv ℝ ψ) := hψc.fderiv ℝ
  have hψ2 : HasCompactSupport (fderiv ℝ (fderiv ℝ ψ)) := hψ1.fderiv ℝ
  have hψs1 : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψs.fderiv_right (by simp)
  have hψs2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hψs1.fderiv_right (by simp)
  set L0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  set L1 : ℝ →L[ℝ] (X d →L[ℝ] ℝ) →L[ℝ] (X d →L[ℝ] ℝ) := L0.precompR (X d)
  set L2 : ℝ →L[ℝ] (X d →L[ℝ] X d →L[ℝ] ℝ) →L[ℝ] (X d →L[ℝ] X d →L[ℝ] ℝ) :=
    L1.precompR (X d)
  refine ⟨max (max (‖L0‖ * ∫ t, ‖ψ t‖ ∂μH) (‖L1‖ * ∫ t, ‖fderiv ℝ ψ t‖ ∂μH))
    (‖L2‖ * ∫ t, ‖fderiv ℝ (fderiv ℝ ψ) t‖ ∂μH), fun T => ?_⟩
  set A := thickening (ρ / 2) T
  set f : X d → ℝ := A.indicator 1
  have hAm : MeasurableSet A := isOpen_thickening.measurableSet
  have hfi : LocallyIntegrable f μH := (locallyIntegrable_const 1).indicator hAm
  have hfm : AEStronglyMeasurable f μH := hfi.aestronglyMeasurable
  have hf1 : ∀ t, |f t| ≤ 1 := fun t => by
    simp only [f, indicator]; split_ifs <;> simp
  set χ := f ⋆[L0, μH] ψ
  have hD1 : fderiv ℝ χ = f ⋆[L1, μH] fderiv ℝ ψ := by
    funext z
    exact (hψc.hasFDerivAt_convolution_right L0 hfi (hψs.of_le (by simp)) z).fderiv
  have hD2 : fderiv ℝ (fderiv ℝ χ) = f ⋆[L2, μH] fderiv ℝ (fderiv ℝ ψ) := by
    rw [hD1]; funext z
    exact (hψ1.hasFDerivAt_convolution_right L1 hfi (hψs1.of_le (by simp)) z).fderiv
  refine ⟨χ, hψc.contDiff_convolution_right L0 hfi hψs, ?_, ?_, ?_⟩
  · -- χ = 1 near T
    intro z hz
    have hint : ∀ t, L0 (f t) (ψ (z - t)) = ψ (z - t) := by
      intro t
      by_cases ht : ψ (z - t) = 0
      · simp [ht]
      · have hzt : dist z t < ρ / 4 := by
          have : z - t ∈ Function.support ψ := ht
          rw [φ.support_normed_eq, mem_ball, dist_zero_right, ← dist_eq_norm] at this
          exact this
        have htA : t ∈ A := by
          have := thickening_mono_of_dist hz hzt
          rwa [show ρ / 4 + ρ / 4 = ρ / 2 by ring] at this
        simp [f, L0, htA]
    show ∫ t, L0 (f t) (ψ (z - t)) ∂μH = 1
    simp_rw [hint]
    rw [integral_sub_left_eq_self (fun t => ψ t) μH z]
    exact φ.integral_normed
  · -- support
    intro z hz
    have hsub := support_convolution_subset (L := L0) (μ := μH) (f := f) (g := ψ) hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hsub
    have ha' : a ∈ A := by
      by_contra hna; exact ha (by simp [f, hna])
    rw [φ.support_normed_eq, mem_ball, dist_zero_right] at hb
    have := thickening_mono_of_dist ha' (t := a + b) (b := ρ / 4)
      (by rw [dist_eq_norm, sub_add_cancel_left, norm_neg]; exact hb)
    rwa [show ρ / 2 + ρ / 4 = 3 * ρ / 4 by ring] at this
  · -- derivative bounds
    intro z j hj
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]
      exact (norm_convolution_le_of_abs_le_one L0 hf1 hfm hψs.continuous hψc z).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · rw [norm_iteratedFDeriv_one, hD1]
      exact (norm_convolution_le_of_abs_le_one L1 hf1 hfm hψs1.continuous hψ1 z).trans
        ((le_max_right _ _).trans (le_max_left _ _))
    · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, hD2]
      exact (norm_convolution_le_of_abs_le_one L2 hf1 hfm hψs2.continuous hψ2 z).trans
        (le_max_right _ _)

end SympNet
