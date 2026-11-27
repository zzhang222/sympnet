/-
  H5a: convolution estimates in C^j on ℝ^m.

  * `conv_close`: if g ≈ g' uniformly (within η) on a large ball, then g ⋆ h ≈ g' ⋆ h in C^j on a
    smaller ball, for h a compactly supported C^j function (derivatives fall on h).
  * `riemann_close`: Ṽ ⋆ h is C^j-approximated (uniformly) by finite sums Σ cᵢ h(· − yᵢ), with the
    points and weights of H2.
-/
import Sympnet.Smoothing.Mollify
import Sympnet.Counterexample
import Sympnet.Hornik.FiniteSum

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Convolution

noncomputable section

namespace SympNet

variable {m : ℕ}

local notation "μH" => (Measure.addHaar : Measure (E m))

theorem norm_iteratedFDeriv_succ_sub_eq {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (h : E m → E') (i : ℕ) (u v : E m) :
    ‖iteratedFDeriv ℝ i (fderiv ℝ h) u - iteratedFDeriv ℝ i (fderiv ℝ h) v‖ =
      ‖iteratedFDeriv ℝ (i + 1) h u - iteratedFDeriv ℝ (i + 1) h v‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]

theorem norm_iteratedFDeriv_zero_sub_pts {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (h : E m → E') (u v : E m) :
    ‖iteratedFDeriv ℝ 0 h u - iteratedFDeriv ℝ 0 h v‖ = ‖h u - h v‖ := by
  rw [iteratedFDeriv_zero_eq', iteratedFDeriv_zero_eq', ← LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.norm_map]

theorem hasCompactSupport_translate {E' : Type} [NormedAddCommGroup E'] {h : E m → E'}
    (hc : HasCompactSupport h) (x : E m) : HasCompactSupport fun t => h (x - t) :=
  hc.comp_homeomorph (Homeomorph.subLeft x)

/-! ### Comparing convolutions with nearby left factors -/

theorem conv_zero_close {R ρ₀ η : ℝ} {g g' : E m → ℝ} (hg : Continuous g) (hg' : Continuous g')
    (hgg : ∀ t ∈ closedBall (0 : E m) (R + ρ₀), |g t - g' t| ≤ η) {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] {h : E m → E'}
    (hh : Continuous h) (hc : HasCompactSupport h) (hs : tsupport h ⊆ closedBall 0 ρ₀)
    {x : E m} (hx : x ∈ closedBall (0 : E m) R) :
    ‖(g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] h) x - (g' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] h) x‖
      ≤ η * ∫ y, ‖h y‖ ∂μH := by
  have hct : HasCompactSupport fun t => h (x - t) := hasCompactSupport_translate hc x
  have hcont : Continuous fun t => h (x - t) := hh.comp (continuous_const.sub continuous_id)
  have hi : ∀ f : E m → ℝ, Continuous f → Integrable (fun t => f t • h (x - t)) μH := fun f hf =>
    (hf.smul hcont).integrable_of_hasCompactSupport hct.smul_left
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [← integral_sub (hi g hg) (hi g' hg')]
  calc ‖∫ t, (g t • h (x - t) - g' t • h (x - t)) ∂μH‖
      ≤ ∫ t, η * ‖h (x - t)‖ ∂μH := by
        refine norm_integral_le_of_norm_le ((hcont.norm.integrable_of_hasCompactSupport
          hct.norm).const_mul η) (Eventually.of_forall fun t => ?_)
        rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        by_cases ht : h (x - t) = 0
        · simp [ht]
        · refine mul_le_mul_of_nonneg_right (hgg t ?_) (norm_nonneg _)
          have h1 : x - t ∈ closedBall (0 : E m) ρ₀ := hs (subset_tsupport _ ht)
          rw [mem_closedBall, dist_zero_right] at h1 hx ⊢
          calc ‖t‖ = ‖x - (x - t)‖ := by abel_nf
            _ ≤ ‖x‖ + ‖x - t‖ := norm_sub_le _ _
            _ ≤ R + ρ₀ := add_le_add hx h1
    _ = η * ∫ y, ‖h y‖ ∂μH := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun y => ‖h y‖) μH x]

set_option maxSynthPendingDepth 6 in
theorem conv_close (j : ℕ) {R ρ₀ η : ℝ} (hη : 0 ≤ η) {g g' : E m → ℝ} (hg : Continuous g)
    (hg' : Continuous g') (hgg : ∀ t ∈ closedBall (0 : E m) (R + ρ₀), |g t - g' t| ≤ η) :
    ∀ {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (h : E m → E'),
      ContDiff ℝ j h → HasCompactSupport h → tsupport h ⊆ closedBall 0 ρ₀ → ∀ B : ℝ,
      (∀ i ≤ j, ∫ y, ‖iteratedFDeriv ℝ i h y‖ ∂μH ≤ B) →
      CrCloseLe j (closedBall 0 R) (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] h)
        (g' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] h) (η * B) := by
  induction j with
  | zero =>
    intro E' _ _ _ h hh hc hs B hB i hi x hx
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [norm_iteratedFDeriv_zero_sub']
    refine (conv_zero_close hg hg' hgg hh.continuous hc hs hx).trans ?_
    have := hB 0 le_rfl
    simp only [norm_iteratedFDeriv_zero] at this
    exact mul_le_mul_of_nonneg_left this hη
  | succ j ih =>
    intro E' _ _ _ h hh hc hs B hB
    have : CompleteSpace (E m →L[ℝ] E') := ContinuousLinearMap.instCompleteSpace
    have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast Nat.le_add_left 1 j)
    have hdh : ContDiff ℝ j (fderiv ℝ h) := hh.fderiv_right (by push_cast; exact le_rfl)
    have hc1 : ContDiff ℝ (j + 1 : ℕ) (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] h) :=
      hc.contDiff_convolution_right _ hg.locallyIntegrable (n := (j + 1 : ℕ)) (by exact_mod_cast hh)
    have hc2 : ContDiff ℝ (j + 1 : ℕ) (g' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] h) :=
      hc.contDiff_convolution_right _ hg'.locallyIntegrable (n := (j + 1 : ℕ)) (by exact_mod_cast hh)
    refine CrCloseLe.of_fderiv hc1 hc2 (fun x hx => ?_) ?_
    · refine (conv_zero_close hg hg' hgg hh.continuous hc hs hx).trans ?_
      have := hB 0 (Nat.zero_le _)
      simp only [norm_iteratedFDeriv_zero] at this
      exact mul_le_mul_of_nonneg_left this hη
    · have := ih (fderiv ℝ h) hdh (hc.fderiv ℝ) ((tsupport_fderiv_subset ℝ).trans hs) B
        (fun i hi => by
          have := hB (i + 1) (by omega)
          simpa [norm_iteratedFDeriv_fderiv] using this)
      rwa [fderiv_conv_right hg.locallyIntegrable hc hh1,
        fderiv_conv_right hg'.locallyIntegrable hc hh1]

/-! ### Finite sums of translates -/

set_option maxSynthPendingDepth 6 in
theorem riemann_close (j : ℕ) {Vt : E m → ℝ} (hVi : Integrable Vt μH) {L₀ : Set (E m)}
    {n : ℕ} {y : Fin n → E m} {c : Fin n → ℝ} {δ η₀ : ℝ}
    (hsum : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E m → F)
      (η : ℝ), ContinuousOn G L₀ → (∀ u ∈ L₀, ∀ v ∈ L₀, dist u v < δ → ‖G u - G v‖ ≤ η) →
      ‖∫ t, Vt t • G t ∂μH - ∑ i, c i • G (y i)‖ ≤ η * ∫ t, |Vt t| ∂μH) :
    ∀ {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (h : E m → E'),
      ContDiff ℝ j h → HasCompactSupport h →
      (∀ i ≤ j, ∀ u v, dist u v < δ →
        ‖iteratedFDeriv ℝ i h u - iteratedFDeriv ℝ i h v‖ ≤ η₀) →
      CrCloseLe j univ (Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] h)
        (fun x => ∑ i, c i • h (x - y i)) (η₀ * ∫ t, |Vt t| ∂μH) := by
  have zero_part : ∀ {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
      (h : E m → E'), Continuous h → (∀ u v, dist u v < δ → ‖h u - h v‖ ≤ η₀) → ∀ x,
      ‖(Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] h) x - ∑ i, c i • h (x - y i)‖ ≤
        η₀ * ∫ t, |Vt t| ∂μH := by
    intro E' _ _ _ h hh hmod x
    have := hsum E' (fun t => h (x - t)) η₀
      (hh.comp (continuous_const.sub continuous_id)).continuousOn
      (fun u _ v _ huv => hmod _ _ (by rwa [dist_sub_left]))
    simpa [convolution_def] using this
  have hcontsum : ∀ {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (h : E m → E')
      (k : ℕ∞ω), ContDiff ℝ k h → ContDiff ℝ k (fun x => ∑ i, c i • h (x - y i)) :=
    fun h k hh => ContDiff.sum fun i _ =>
      (hh.comp (contDiff_id.sub contDiff_const)).const_smul _
  induction j with
  | zero =>
    intro E' _ _ _ h hh hc hmod i hi x _
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [norm_iteratedFDeriv_zero_sub']
    exact zero_part h hh.continuous (fun u v huv => by
      have := hmod 0 le_rfl u v huv; rwa [norm_iteratedFDeriv_zero_sub_pts] at this) x
  | succ j ih =>
    intro E' _ _ _ h hh hc hmod
    have : CompleteSpace (E m →L[ℝ] E') := ContinuousLinearMap.instCompleteSpace
    have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast Nat.le_add_left 1 j)
    have hdh : ContDiff ℝ j (fderiv ℝ h) := hh.fderiv_right (by push_cast; exact le_rfl)
    have hc1 : ContDiff ℝ (j + 1 : ℕ) (Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] h) :=
      hc.contDiff_convolution_right _ hVi.locallyIntegrable (n := (j + 1 : ℕ)) (by exact_mod_cast hh)
    refine CrCloseLe.of_fderiv hc1 (hcontsum h _ hh) (fun x _ => zero_part h hh.continuous
      (fun u v huv => by
        have := hmod 0 (Nat.zero_le _) u v huv; rwa [norm_iteratedFDeriv_zero_sub_pts] at this) x) ?_
    have hfd : (fun x => fderiv ℝ (fun x => ∑ i, c i • h (x - y i)) x) =
        fun x => ∑ i, c i • fderiv ℝ h (x - y i) := by
      funext x
      have hd : HasFDerivAt (fun x => ∑ i, c i • h (x - y i)) (∑ i, c i • fderiv ℝ h (x - y i)) x := by
        refine HasFDerivAt.fun_sum fun i _ => ?_
        have := ((hh1.differentiable one_ne_zero (x - y i)).hasFDerivAt.comp x
          ((hasFDerivAt_id x).sub_const (y i))).const_smul (c i)
        have e : (fderiv ℝ h (x - y i)).comp (ContinuousLinearMap.id ℝ (E m)) =
            fderiv ℝ h (x - y i) := by ext; simp
        rw [e] at this; exact this
      exact hd.fderiv
    have := ih (fderiv ℝ h) hdh (hc.fderiv ℝ) (fun i hi u v huv => by
      rw [norm_iteratedFDeriv_succ_sub_eq]; exact hmod (i + 1) (by omega) u v huv)
    rw [← fderiv_conv_right hVi.locallyIntegrable hc hh1, ← hfd] at this
    exact this

end SympNet
