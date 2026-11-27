/-
  H3b: an r-finite activation has a non-polynomial mollification, hence 1D nets are uniformly
  dense (`oneDim_dense`).

  ρ = φ ⋆ τ has ρ^{(r)} = φ ⋆ τ^{(r)}, which is integrable and (for a narrow bump φ) nonzero.
  An integrable smooth function with a vanishing derivative of some order is zero (it would grow
  at least like a nonzero polynomial). So no derivative of ρ vanishes identically.
-/
import Sympnet.Hornik.OneDim

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Convolution

noncomputable section

namespace SympNet

/-! ### Differentiating a mollification -/

theorem conv_eq_integral (φ : ContDiffBump (0 : ℝ)) (g : ℝ → ℝ) (s : ℝ) :
    (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) s =
      ∫ t, φ.normed volume t * g (s - t) := by
  rw [convolution_def]; rfl

theorem deriv_conv (φ : ContDiffBump (0 : ℝ)) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    deriv (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv g := by
  funext s0
  set φn := φ.normed volume
  have hφc : Continuous φn := φ.continuous_normed
  have hφs : HasCompactSupport φn := φ.hasCompactSupport_normed
  have hgd : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hgdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  obtain ⟨M, hM⟩ := (isCompact_closedBall s0 (1 + φ.rOut)).exists_bound_of_continuousOn
    hgd.continuousOn
  have hsupp : ∀ t, φn t ≠ 0 → |t| < φ.rOut := fun t ht => by
    have : t ∈ Function.support φn := ht
    rw [φ.support_normed_eq, mem_ball, dist_zero_right, Real.norm_eq_abs] at this
    exact this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s t => φn t * g (s - t)) (F' := fun s t => φn t * deriv g (s - t))
    (bound := fun t => |φn t| * M) (x₀ := s0) (ball_mem_nhds s0 one_pos)
    (Eventually.of_forall fun s => (hφc.mul (hg.continuous.comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable)
    ((hφc.mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hφs.mul_right)
    ((hφc.mul (hgd.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (Eventually.of_forall fun t s hs => by
      rw [norm_mul, Real.norm_eq_abs]
      by_cases ht : φn t = 0
      · simp [ht]
      · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        apply hM
        rw [mem_closedBall, Real.dist_eq]
        have h1 := hsupp t ht
        rw [mem_ball, Real.dist_eq] at hs
        calc |s - t - s0| = |(s - s0) - t| := by ring_nf
          _ ≤ |s - s0| + |t| := abs_sub _ _
          _ ≤ 1 + φ.rOut := by linarith)
    (φ.integrable_normed.abs.mul_const M)
    (Eventually.of_forall fun t s _ => by
      have := ((hgdiff (s - t)).hasDerivAt.comp s ((hasDerivAt_id s).sub_const t)).const_mul (φn t)
      simpa using this)
  have h2 := key.2
  have e1 : (fun s => ∫ t, φn t * g (s - t)) =
      φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
    funext s; rw [conv_eq_integral]
  rw [e1] at h2
  rw [h2.deriv, conv_eq_integral]

theorem iteratedDeriv_conv (φ : ContDiffBump (0 : ℝ)) {τ : ℝ → ℝ} {r : ℕ} (hτ : ContDiff ℝ r τ) :
    ∀ j ≤ r, iteratedDeriv j (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] τ) =
      φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] iteratedDeriv j τ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [iteratedDeriv_succ, ih (by omega), iteratedDeriv_succ]
    apply deriv_conv
    rw [iteratedDeriv_eq_iterate]
    have : ContDiff ℝ ((1 + j : ℕ) : ℕ∞ω) τ := hτ.of_le (by exact_mod_cast (by omega : 1 + j ≤ r))
    exact ContDiff.iterate_deriv' 1 j this

/-! ### Growth of functions with a constant derivative -/

theorem iteratedDeriv_add' (a b : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv (a + b) f = iteratedDeriv a (iteratedDeriv b f) := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by ring, iteratedDeriv_succ, ih,
      iteratedDeriv_succ]

theorem eventually_abs_ge (k : ℕ) : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
    ∀ a : ℝ, a ≠ 0 → (∀ x, iteratedDeriv k g x = a) → ∃ η > 0, ∃ S, ∀ x ≥ S, η ≤ |g x| := by
  induction k with
  | zero =>
    intro g _ a ha hk
    exact ⟨|a|, abs_pos.2 ha, 0, fun x _ => by simp only [iteratedDeriv_zero] at hk; rw [hk x]⟩
  | succ k ih =>
    intro g hg a ha hk
    have hg' : ContDiff ℝ ∞ (deriv g) := hg.iterate_deriv 1
    obtain ⟨η, hη, S, hS⟩ := ih (deriv g) hg' a ha (fun x => by
      rw [← hk x, iteratedDeriv_succ'])
    have hdc : Continuous (deriv g) := hg'.continuous
    have hgd : Differentiable ℝ g := hg.differentiable (by simp)
    -- constant sign of g' on [S, ∞)
    have hsign : (∀ x ≥ S, η ≤ deriv g x) ∨ (∀ x ≥ S, η ≤ -deriv g x) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := hcon
      have hxn : deriv g x < 0 := by
        have := hS x hx; rw [le_abs] at this; rcases this with h | h <;> linarith
      have hyp : 0 < deriv g y := by
        have := hS y hy; rw [le_abs] at this; rcases this with h | h <;> linarith
      have hzero : ∃ z ≥ S, deriv g z = 0 := by
        rcases le_total x y with hxy | hxy
        · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hxy hdc.continuousOn
            (show (0 : ℝ) ∈ Icc (deriv g x) (deriv g y) from ⟨hxn.le, hyp.le⟩)
          exact ⟨z, hx.trans hz.1, hz0⟩
        · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hxy hdc.continuousOn
            (show (0 : ℝ) ∈ Icc (deriv g x) (deriv g y) from ⟨hxn.le, hyp.le⟩)
          exact ⟨z, hy.trans hz.1, hz0⟩
      obtain ⟨z, hz, hz0⟩ := hzero
      have := hS z hz
      rw [hz0, abs_zero] at this
      linarith
    have hmv : ∀ C : ℝ, (∀ x ≥ S, C ≤ deriv g x) → ∀ x ≥ S, C * (x - S) ≤ g x - g S := by
      intro C hC x hx
      refine (convex_Ici S).mul_sub_le_image_sub_of_le_deriv hgd.continuous.continuousOn
        hgd.differentiableOn (fun y hy => ?_) S (Set.mem_Ici.2 le_rfl) x hx hx
      rw [interior_Ici] at hy; exact hC y (le_of_lt hy)
    refine ⟨1, one_pos, S + (|g S| + 1) / η, fun x hx => ?_⟩
    have hxS : S ≤ x := le_trans (le_add_of_nonneg_right (by positivity)) hx
    have hxη : |g S| + 1 ≤ η * (x - S) := by
      have := (div_le_iff₀ hη).1 (by linarith : (|g S| + 1) / η ≤ x - S)
      linarith
    rcases hsign with h | h
    · have := hmv η h x hxS
      rw [le_abs]; left; linarith [neg_abs_le (g S)]
    · have hneg : ∀ x ≥ S, η ≤ deriv (fun y => -g y) x := fun y hy => by
        rw [deriv.fun_neg]; exact h y hy
      have := (convex_Ici S).mul_sub_le_image_sub_of_le_deriv hgd.neg.continuous.continuousOn
        hgd.neg.differentiableOn (fun y hy => by rw [interior_Ici] at hy; exact hneg y (le_of_lt hy))
        S (Set.mem_Ici.2 le_rfl) x hxS hxS
      have this' : η * (x - S) ≤ -g x - -g S := this
      rw [le_abs]; right; linarith [le_abs_self (g S), neg_abs_le (g S)]

/-- A smooth integrable function with an identically vanishing derivative of some order is 0. -/
theorem eq_zero_of_iteratedDeriv_eq_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hi : Integrable f)
    {n : ℕ} (hn : ∀ x, iteratedDeriv n f x = 0) : ∀ x, f x = 0 := by
  classical
  by_contra hne
  push Not at hne
  have hex : ∃ m, ∀ x, iteratedDeriv m f x = 0 := ⟨n, hn⟩
  set m := Nat.find hex
  have hm : ∀ x, iteratedDeriv m f x = 0 := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hne
    have := hm x; rw [h0] at this; simp at this; exact hx this
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  set g := iteratedDeriv m' f
  have hgs : ContDiff ℝ ∞ g := by
    simp only [g]; rw [iteratedDeriv_eq_iterate]; exact hf.iterate_deriv m'
  have hgd : ∀ x, deriv g x = 0 := fun x => by
    have := hm x; rw [hm', iteratedDeriv_succ] at this; exact this
  have hconst := is_const_of_deriv_eq_zero (hgs.differentiable (by simp)) hgd
  set a := g 0
  have ha : a ≠ 0 := by
    intro ha0
    have hlt : m' < m := by omega
    exact Nat.find_min hex hlt fun x => by
      show g x = 0; rw [hconst x 0]; exact ha0
  obtain ⟨η, hη, S, hS⟩ := eventually_abs_ge m' f hf a ha (fun x => hconst x 0)
  have h1 := hi.measure_norm_ge_lt_top hη
  have h2 : Ici S ⊆ {x | η ≤ ‖f x‖} := fun x hx => by
    simp only [mem_setOf_eq, Real.norm_eq_abs]; exact hS x hx
  have := (measure_mono h2).trans_lt h1
  rw [Real.volume_Ici] at this
  exact lt_irrefl _ this

/-! ### Non-polynomiality and 1D density -/

theorem exists_nonpoly_moll {r : ℕ} {τ : ℝ → ℝ} (hτ : RFinite r τ) :
    ∃ φ : ContDiffBump (0 : ℝ), ∀ k, ∃ b,
      iteratedDeriv k (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] τ) b ≠ 0 := by
  obtain ⟨hτc, hψi, hψpos⟩ := hτ
  set ψ := iteratedDeriv r τ
  have hψc : Continuous ψ := hτc.continuous_iteratedDeriv' r
  obtain ⟨s0, hs0⟩ : ∃ s0, ψ s0 ≠ 0 := by
    by_contra h
    push Not at h
    have : ∫ x, |ψ x| = 0 := by simp [h]
    linarith
  have hpos : 0 < |ψ s0| / 2 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 hψc s0 _ hpos
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  refine ⟨φ, ?_⟩
  set ρ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] τ
  have hρ : ContDiff ℝ ∞ ρ :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hτc.continuous.locallyIntegrable
  have hh : iteratedDeriv r ρ = φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ :=
    iteratedDeriv_conv φ hτc r le_rfl
  have hhs0 : iteratedDeriv r ρ s0 ≠ 0 := by
    rw [hh]
    have := φ.dist_normed_convolution_le (μ := volume) (x₀ := s0) hψc.aestronglyMeasurable
      (fun x hx => (hδ' x hx).le)
    intro h0
    rw [h0, Real.dist_eq, zero_sub, abs_neg] at this
    linarith
  have hhi : Integrable (iteratedDeriv r ρ) := by
    rw [hh]; exact φ.integrable_normed.integrable_convolution _ hψi
  have hhsm : ContDiff ℝ ∞ (iteratedDeriv r ρ) := by
    rw [iteratedDeriv_eq_iterate]; exact hρ.iterate_deriv r
  intro k
  by_contra hk
  push Not at hk
  rcases le_or_gt k r with hkr | hkr
  · apply hhs0
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hkr
    rw [add_comm, iteratedDeriv_add']
    have : iteratedDeriv k ρ = 0 := funext hk
    rw [this]; simp
  · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt hkr
    have hz : ∀ x, iteratedDeriv (c + 1) (iteratedDeriv r ρ) x = 0 := fun x => by
      rw [← iteratedDeriv_add', show c + 1 + r = k by omega]; exact hk x
    exact hhs0 (eq_zero_of_iteratedDeriv_eq_zero hhsm hhi hz s0)

/-- **1D uniform density of nets** for an r-finite activation. -/
theorem oneDim_dense {r : ℕ} {τ : ℝ → ℝ} (hτ : RFinite r τ) {f : ℝ → ℝ} (hf : Continuous f) :
    UApprox τ f := by
  obtain ⟨φ, hφ⟩ := exists_nonpoly_moll hτ
  exact uapprox_of_nonpoly hτ.1.continuous φ hφ hf

end SympNet
