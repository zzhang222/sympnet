/-
  C2: mollification. For g : X → E' that is C^j with compact support, convolving with a normalized
  bump of small radius approximates g in C^j uniformly; convolution also preserves sup bounds.
-/
import Sympnet.SympNetUniversal

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff Convolution

noncomputable section

namespace SympNet

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

local notation "μH" => (Measure.addHaar : Measure V)

section Helpers
variable {V' W : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Building C^{j+1}-closeness from C⁰-closeness and C^j-closeness of the derivatives. -/
theorem CrCloseLe.of_fderiv {j : ℕ} {K : Set V'} {f g : V' → W} {ε : ℝ}
    (hf : ContDiff ℝ (j + 1 : ℕ) f) (hg : ContDiff ℝ (j + 1 : ℕ) g)
    (h0 : ∀ x ∈ K, ‖f x - g x‖ ≤ ε)
    (h1 : CrCloseLe j K (fun y => fderiv ℝ f y) (fun y => fderiv ℝ g y) ε) :
    CrCloseLe (j + 1) K f g ε := by
  intro k hk x hx
  rcases k with _ | m
  · rw [norm_iteratedFDeriv_zero_sub hf hg]; exact h0 x hx
  · have hm1 : ((m + 1 : ℕ) : ℕ∞ω) ≤ ((j + 1 : ℕ) : ℕ∞ω) := Nat.cast_le.mpr hk
    rw [norm_iteratedFDeriv_succ_sub (hf.of_le hm1) (hg.of_le hm1)]
    exact h1 m (by omega) x hx

end Helpers

section Moll
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']

theorem convolution_precompR_lsmul {G' : Type} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (f : V → ℝ) (g : V → (G' →L[ℝ] E')) :
    f ⋆[((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E' →L[ℝ] E').precompR G'), μH] g =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] g := by
  funext z
  simp only [convolution_def]
  congr 1

theorem fderiv_moll (φ : ContDiffBump (0 : V)) {g : V → E'} (hgc : HasCompactSupport g)
    (hg : ContDiff ℝ 1 g) :
    fderiv ℝ (φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] g) =
      φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] fderiv ℝ g := by
  funext z
  rw [(hgc.hasFDerivAt_convolution_right _ φ.continuous_normed.locallyIntegrable hg z).fderiv,
    convolution_precompR_lsmul]

theorem fderiv_conv_right {f : V → ℝ} (hf : MeasureTheory.LocallyIntegrable f μH) {g : V → E'}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] g) =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] fderiv ℝ g := by
  funext z
  rw [(hgc.hasFDerivAt_convolution_right _ hf hg z).fderiv, convolution_precompR_lsmul]

theorem contDiff_moll (φ : ContDiffBump (0 : V)) {g : V → E'} (hgc : HasCompactSupport g)
    {n : ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] g) :=
  hgc.contDiff_convolution_right _ φ.continuous_normed.locallyIntegrable hg

/-- Sup bounds are preserved by mollification. -/
theorem norm_moll_le (φ : ContDiffBump (0 : V)) {g : V → E'} {M : ℝ}
    (hgm : AEStronglyMeasurable g μH) (hM : ∀ z, ‖g z‖ ≤ M) (z : V) :
    ‖(φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] g) z‖ ≤ M := by
  rw [convolution_def]
  have hφi : Integrable (φ.normed μH) μH := φ.integrable_normed
  calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed μH t) (g (z - t)) ∂μH‖
      ≤ ∫ t, φ.normed μH t * M ∂μH := by
        refine norm_integral_le_of_norm_le (hφi.mul_const M) (Eventually.of_forall fun t => ?_)
        rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left (hM _) (φ.nonneg_normed t)
    _ = M := by rw [integral_mul_const, φ.integral_normed, one_mul]

set_option maxSynthPendingDepth 6 in
/-- **C^j approximation by mollification.** -/
theorem moll_close (j : ℕ) : ∀ {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] (g : V → E'), ContDiff ℝ j g → HasCompactSupport g → ∀ ε > 0,
    ∃ δ > 0, ∀ φ : ContDiffBump (0 : V), φ.rOut ≤ δ →
      CrCloseLe j univ (φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] g) g ε := by
  have zero_part : ∀ {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
      [CompleteSpace E'] (g : V → E'), Continuous g → HasCompactSupport g → ∀ ε > 0,
      ∃ δ > 0, ∀ φ : ContDiffBump (0 : V), φ.rOut ≤ δ → ∀ z,
        ‖(φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] g) z - g z‖ ≤ ε := by
    intro E' _ _ _ g hg hgc ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1
      (hgc.uniformContinuous_of_continuous hg) ε hε
    refine ⟨δ / 2, half_pos hδ, fun φ hφ z => ?_⟩
    rw [← dist_eq_norm]
    refine φ.dist_normed_convolution_le hg.aestronglyMeasurable fun x hx => ?_
    exact (hδ' (lt_of_lt_of_le (mem_ball.1 hx) (hφ.trans (by linarith)))).le
  induction j with
  | zero =>
    intro E' _ _ _ g hg hgc ε hε
    obtain ⟨δ, hδ, hδ'⟩ := zero_part g hg.continuous hgc ε hε
    refine ⟨δ, hδ, fun φ hφ k hk z _ => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    rw [norm_iteratedFDeriv_zero_sub (r := 0) (contDiff_moll φ hgc (n := 0)
      (by exact_mod_cast hg)) hg]
    exact hδ' φ hφ z
  | succ j ih =>
    intro E' _ _ _ g hg hgc ε hε
    haveI : CompleteSpace (V →L[ℝ] E') := ContinuousLinearMap.instCompleteSpace
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast Nat.le_add_left 1 j)
    have hdg : ContDiff ℝ j (fderiv ℝ g) := hg.fderiv_right (by push_cast; exact le_rfl)
    obtain ⟨δ₀, hδ₀, h₀⟩ := zero_part g hg.continuous hgc ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih (fderiv ℝ g) hdg (hgc.fderiv ℝ) ε hε
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun φ hφ => ?_⟩
    have hmc : ContDiff ℝ (j + 1 : ℕ) (φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] g) :=
      contDiff_moll φ hgc (n := (j + 1 : ℕ)) (by exact_mod_cast hg)
    refine CrCloseLe.of_fderiv hmc hg (fun z _ => h₀ φ (hφ.trans (min_le_left _ _)) z) ?_
    have := h₁ φ (hφ.trans (min_le_right _ _))
    rwa [← fderiv_moll φ hgc hg1] at this

end Moll

end SympNet
