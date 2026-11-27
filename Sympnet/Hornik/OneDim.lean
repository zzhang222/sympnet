/-
  H3: one-dimensional uniform density of nets (the Leshno–Lin–Pinkus–Schocken argument).

  `UApprox τ f`: f is a uniform limit on every [−R,R] of 1D nets. We show:
  * UApprox is closed under +, •, uniform limits and affine substitution;
  * ρ = φ ⋆ τ satisfies UApprox (finite sums of translates, H2);
  * if all dilates/translates of s^k ρ^{(k)} are UApprox, so are those of s^{k+1} ρ^{(k+1)}
    (difference quotients in the dilation parameter);
  * hence s^k ρ^{(k)}(b) is UApprox; if ρ^{(k)}(b) ≠ 0 we get s^k, so all polynomials;
  * Weierstrass.
-/
import Sympnet.Hornik.Net
import Sympnet.Hornik.FiniteSum

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Convolution

noncomputable section

namespace SympNet

/-- f is uniformly approximable by 1D nets on every compact interval. -/
def UApprox (τ : ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ R : ℝ, ∀ ε > 0, ∃ g ∈ netSpan1 τ, ∀ s ∈ Icc (-R) R, |f s - g s| < ε

theorem abs_le_abs_of_mem_Icc {s R : ℝ} (hs : s ∈ Icc (-R) R) : |s| ≤ |R| :=
  abs_le.2 ⟨by linarith [hs.1, le_abs_self R], by linarith [hs.2, le_abs_self R]⟩

namespace UApprox
variable {τ : ℝ → ℝ} {f g : ℝ → ℝ}

theorem of_mem (hf : f ∈ netSpan1 τ) : UApprox τ f :=
  fun _ ε hε => ⟨f, hf, fun s _ => by simpa using hε⟩

theorem of_approx (h : ∀ R : ℝ, ∀ ε > 0, ∃ f', UApprox τ f' ∧ ∀ s ∈ Icc (-R) R, |f s - f' s| < ε) :
    UApprox τ f := by
  intro R ε hε
  obtain ⟨f', hf', h1⟩ := h R (ε / 2) (half_pos hε)
  obtain ⟨g, hg, h2⟩ := hf' R (ε / 2) (half_pos hε)
  refine ⟨g, hg, fun s hs => ?_⟩
  calc |f s - g s| ≤ |f s - f' s| + |f' s - g s| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h1 s hs) (h2 s hs)
    _ = ε := add_halves ε

theorem add (hf : UApprox τ f) (hg : UApprox τ g) : UApprox τ (fun s => f s + g s) := by
  intro R ε hε
  obtain ⟨f', hf', h1⟩ := hf R (ε / 2) (half_pos hε)
  obtain ⟨g', hg', h2⟩ := hg R (ε / 2) (half_pos hε)
  refine ⟨f' + g', (netSpan1 τ).add_mem hf' hg', fun s hs => ?_⟩
  calc |f s + g s - (f' + g') s| = |(f s - f' s) + (g s - g' s)| := by simp; ring_nf
    _ ≤ |f s - f' s| + |g s - g' s| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h1 s hs) (h2 s hs)
    _ = ε := add_halves ε

theorem smul (c : ℝ) (hf : UApprox τ f) : UApprox τ (fun s => c * f s) := by
  intro R ε hε
  obtain ⟨f', hf', h1⟩ := hf R (ε / (|c| + 1)) (by positivity)
  refine ⟨c • f', (netSpan1 τ).smul_mem c hf', fun s hs => ?_⟩
  have h := h1 s hs
  calc |c * f s - (c • f') s| = |c| * |f s - f' s| := by
        rw [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul]
    _ ≤ (|c| + 1) * |f s - f' s| := by gcongr; linarith
    _ < (|c| + 1) * (ε / (|c| + 1)) := by gcongr
    _ = ε := by field_simp

theorem sub (hf : UApprox τ f) (hg : UApprox τ g) : UApprox τ (fun s => f s - g s) := by
  have := hf.add (hg.smul (-1))
  simpa [sub_eq_add_neg] using this

theorem sum {ι : Type*} (t : Finset ι) {F : ι → ℝ → ℝ} (h : ∀ i ∈ t, UApprox τ (F i)) :
    UApprox τ (fun s => ∑ i ∈ t, F i s) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact of_mem (show (fun _ => (0 : ℝ)) ∈ netSpan1 τ from (netSpan1 τ).zero_mem)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem affine (hf : UApprox τ f) (c b : ℝ) : UApprox τ (fun s => f (c * s + b)) := by
  intro R ε hε
  obtain ⟨g, hg, h1⟩ := hf (|c| * |R| + |b|) ε hε
  refine ⟨fun s => g (c * s + b), netSpan1_affine hg c b, fun s hs => h1 _ ?_⟩
  have hs' : |s| ≤ |R| := abs_le_abs_of_mem_Icc hs
  rw [mem_Icc, ← abs_le]
  calc |c * s + b| ≤ |c * s| + |b| := abs_add_le _ _
    _ = |c| * |s| + |b| := by rw [abs_mul]
    _ ≤ |c| * |R| + |b| := by gcongr

end UApprox

/-! ### The mollified activation is approximable -/

theorem uapprox_conv {τ : ℝ → ℝ} (hτ : Continuous τ) (φ : ContDiffBump (0 : ℝ)) :
    UApprox τ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] τ) := by
  intro R ε hε
  set L : Set ℝ := closedBall 0 φ.rOut
  set I : Set ℝ := Icc (-(|R| + φ.rOut)) (|R| + φ.rOut)
  have huc := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous (s := I) hτ.continuousOn)
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / 2) (half_pos hε)
  have hφi : Integrable (φ.normed volume) volume := φ.integrable_normed
  have hφL : ∀ y ∉ L, φ.normed volume y = 0 := fun y hy => by
    rw [← Function.notMem_support, φ.support_normed_eq]
    exact fun h => hy (ball_subset_closedBall h)
  obtain ⟨n, y, c, hyL, happrox⟩ := exists_finite_sum_approx volume hφi (isCompact_closedBall 0 _)
    hφL hδ
  refine ⟨fun s => ∑ i, c i * τ (1 * s + -y i), ?_, fun s hs => ?_⟩
  · have : (fun s => ∑ i, c i * τ (1 * s + -y i)) = ∑ i, c i • (fun s => τ (1 * s + -y i)) := by
      funext s; simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => (netSpan1 τ).smul_mem _ (unit_mem_netSpan1 τ _ _)
  · have hsI : ∀ t ∈ L, s - t ∈ I := fun t ht => by
      have ht' : |t| ≤ φ.rOut := by simpa [L, mem_closedBall, dist_zero_right] using ht
      have hs' : |s| ≤ |R| := abs_le_abs_of_mem_Icc hs
      rw [mem_Icc, ← abs_le]
      calc |s - t| ≤ |s| + |t| := abs_sub _ _
        _ ≤ |R| + φ.rOut := add_le_add hs' ht'
    have h := happrox ℝ (fun t => τ (s - t)) (ε / 2)
      (hτ.comp (continuous_const.sub continuous_id)).continuousOn
      (fun u hu v hv huv => by
        have hd : dist (s - u) (s - v) < δ := by
          rw [Real.dist_eq, show s - u - (s - v) = -(u - v) by ring, abs_neg, ← Real.dist_eq]
          exact huv
        have := hδ' _ (hsI u hu) _ (hsI v hv) hd
        rw [Real.dist_eq] at this; rw [Real.norm_eq_abs]; exact this.le)
    have hint : ∫ t, |φ.normed volume t| ∂volume = 1 := by
      simp_rw [abs_of_nonneg (φ.nonneg_normed _)]; exact φ.integral_normed
    rw [hint, mul_one] at h
    have e : (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] τ) s =
        ∫ t, φ.normed volume t • τ (s - t) := by
      rw [convolution_def]; rfl
    rw [e]
    simp only [one_mul, ← sub_eq_add_neg, smul_eq_mul, Real.norm_eq_abs] at h ⊢
    linarith

/-! ### Derivatives in the dilation parameter -/

theorem diff_quot_bound {g : ℝ → ℝ} (hg : Differentiable ℝ g) {y s h om : ℝ} (hh : 0 < h)
    (hom : ∀ t ∈ Icc 0 h, |deriv g (y + t * s) - deriv g y| ≤ om) :
    |(g (y + h * s) - g y) / h - s * deriv g y| ≤ |s| * om := by
  set F : ℝ → ℝ := fun t => g (y + t * s) - t * s * deriv g y
  have hF : ∀ t ∈ Icc 0 h, HasDerivWithinAt F (s * deriv g (y + t * s) - s * deriv g y)
      (Icc 0 h) t := by
    intro t _
    have h1 : HasDerivAt (fun t => y + t * s) s t := by
      simpa using ((hasDerivAt_id t).mul_const s).const_add y
    have h2 := (hg (y + t * s)).hasDerivAt.comp t h1
    have h3 := h2.sub (((hasDerivAt_id t).mul_const s).mul_const (deriv g y))
    refine (h3.congr_deriv ?_).hasDerivWithinAt
    simp; ring
  have hb : ∀ t ∈ Ico 0 h, ‖s * deriv g (y + t * s) - s * deriv g y‖ ≤ |s| * om := by
    intro t ht
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hom t (Ico_subset_Icc_self ht)) (abs_nonneg _)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hF hb h (right_mem_Icc.2 hh.le)
  simp only [F, zero_mul, add_zero, sub_zero, Real.norm_eq_abs, sub_zero] at this
  rw [show (g (y + h * s) - g y) / h - s * deriv g y =
      (g (y + h * s) - h * s * deriv g y - g y) / h by field_simp; ring, abs_div,
    abs_of_pos hh, div_le_iff₀ hh]
  linarith

theorem uapprox_succ {τ : ℝ → ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ)
    (h : ∀ c b, UApprox τ (fun s => s ^ k * g (c * s + b))) (c b : ℝ) :
    UApprox τ (fun s => s ^ (k + 1) * deriv g (c * s + b)) := by
  refine UApprox.of_approx fun R ε hε => ?_
  have hdg : Continuous (deriv g) := hg.continuous_deriv (by simp)
  set R' := |R| + 1
  have hR'0 : 0 < R' := by positivity
  set I : Set ℝ := Icc (-((|c| + 1) * R' + |b|)) ((|c| + 1) * R' + |b|)
  set om := ε / (2 * (R' ^ (k + 1) + 1))
  have hom : 0 < om := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous (s := I) hdg.continuousOn) om hom
  set hh := min (δ / (2 * R')) (1 / 2)
  have hh0 : 0 < hh := lt_min (by positivity) (by norm_num)
  refine ⟨fun s => (1 / hh) * (s ^ k * g ((c + hh) * s + b) - s ^ k * g (c * s + b)), ?_,
    fun s hs => ?_⟩
  · exact ((h (c + hh) b).sub (h c b)).smul _
  · have hsR : |s| ≤ R' := by
      have : |s| ≤ |R| := abs_le_abs_of_mem_Icc hs
      linarith
    have hyI : ∀ t ∈ Icc 0 hh, c * s + b + t * s ∈ I := by
      intro t ht
      have ht1 : t ≤ 1 := ht.2.trans (min_le_right _ _ |>.trans (by norm_num))
      rw [mem_Icc, ← abs_le]
      calc |c * s + b + t * s| ≤ |c * s| + |b| + |t * s| := by
            linarith [abs_add_le (c * s + b) (t * s), abs_add_le (c * s) b]
        _ = |c| * |s| + |b| + t * |s| := by rw [abs_mul, abs_mul, abs_of_nonneg ht.1]
        _ ≤ (|c| + 1) * R' + |b| := by nlinarith [abs_nonneg s, abs_nonneg c, ht.1]
    have hbound : |(g (c * s + b + hh * s) - g (c * s + b)) / hh - s * deriv g (c * s + b)| ≤
        |s| * om := by
      refine diff_quot_bound (hg.differentiable (by simp)) hh0 fun t ht => ?_
      have := hδ' _ (hyI t ht) _ (hyI 0 ⟨le_rfl, hh0.le⟩) (by
        rw [Real.dist_eq]; simp only [zero_mul, add_zero]
        rw [show c * s + b + t * s - (c * s + b) = t * s by ring, abs_mul, abs_of_nonneg ht.1]
        calc t * |s| ≤ hh * R' := mul_le_mul ht.2 hsR (abs_nonneg _) hh0.le
          _ ≤ δ / (2 * R') * R' := by gcongr; exact min_le_left _ _
          _ = δ / 2 := by field_simp [hR'0.ne']
          _ < δ := half_lt_self hδ)
      simp only [zero_mul, add_zero] at this
      rw [Real.dist_eq] at this; exact this.le
    have e : (1 / hh) * (s ^ k * g ((c + hh) * s + b) - s ^ k * g (c * s + b)) -
        s ^ (k + 1) * deriv g (c * s + b) =
        s ^ k * ((g (c * s + b + hh * s) - g (c * s + b)) / hh - s * deriv g (c * s + b)) := by
      rw [show (c + hh) * s + b = c * s + b + hh * s by ring]; field_simp; ring
    rw [abs_sub_comm, e, abs_mul, abs_pow]
    calc |s| ^ k * |(g (c * s + b + hh * s) - g (c * s + b)) / hh - s * deriv g (c * s + b)|
        ≤ R' ^ k * (|s| * om) := by gcongr
      _ ≤ R' ^ k * (R' * om) := by gcongr
      _ = R' ^ (k + 1) * om := by ring
      _ < ε := by
          rw [show R' ^ (k + 1) * om = ε * (R' ^ (k + 1) / (2 * (R' ^ (k + 1) + 1))) by
            simp only [om]; ring]
          have : R' ^ (k + 1) / (2 * (R' ^ (k + 1) + 1)) < 1 := by
            rw [div_lt_one (by positivity)]; nlinarith [pow_nonneg (show (0:ℝ) ≤ R' by positivity) (k + 1)]
          nlinarith

/-- All s^k ρ^{(k)}(c s + b) are approximable when ρ is. -/
theorem uapprox_iteratedDeriv {τ ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (h0 : UApprox τ ρ) :
    ∀ k c b, UApprox τ (fun s => s ^ k * iteratedDeriv k ρ (c * s + b)) := by
  intro k
  induction k with
  | zero => intro c b; simpa using h0.affine c b
  | succ k ih =>
    intro c b
    have hk : ContDiff ℝ ∞ (iteratedDeriv k ρ) := by
      rw [iteratedDeriv_eq_iterate]; exact hρ.iterate_deriv k
    have := uapprox_succ hk k ih c b
    simpa [iteratedDeriv_succ] using this

/-- **1D density, given a non-polynomial mollification.** -/
theorem uapprox_of_nonpoly {τ : ℝ → ℝ} (hτ : Continuous τ) (φ : ContDiffBump (0 : ℝ))
    (hnp : ∀ k, ∃ b, iteratedDeriv k (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] τ) b ≠ 0)
    {f : ℝ → ℝ} (hf : Continuous f) : UApprox τ f := by
  set ρ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] τ
  have hρ : ContDiff ℝ ∞ ρ :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hτ.locallyIntegrable
  have hall := uapprox_iteratedDeriv hρ (uapprox_conv hτ φ)
  have hmono : ∀ k, UApprox τ (fun s => s ^ k) := by
    intro k
    obtain ⟨b, hb⟩ := hnp k
    have := (hall k 0 b).smul (iteratedDeriv k ρ b)⁻¹
    simpa [mul_comm, mul_assoc, inv_mul_cancel₀ hb, mul_inv_cancel₀ hb] using this
  have hpoly : ∀ p : Polynomial ℝ, UApprox τ (fun s => p.eval s) := by
    intro p
    have := UApprox.sum (Finset.range (p.natDegree + 1))
      (F := fun i s => p.coeff i * s ^ i) fun i _ => (hmono i).smul _
    simpa [Polynomial.eval_eq_sum_range] using this
  refine UApprox.of_approx fun R ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R f hf.continuousOn ε hε
  exact ⟨_, hpoly p, fun s hs => by rw [abs_sub_comm]; exact hp s hs⟩

end SympNet
