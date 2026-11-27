/-
  C8: the Alexander family F_t and its uniform constants.

  Part 1 (linear algebra + antilipschitz):
  * a symplectic derivative is injective;
  * `exists_equiv_of_lower_bound`: ‖T v‖ ≥ a‖v‖ ⇒ T is an equivalence with ‖T⁻¹‖ ≤ 1/a;
  * `exists_antilipschitz`: an injective C¹ map with invertible derivative is antilipschitz on
    every compact subset of its (open) domain;
  * `lower_bound_fderiv`: the derivative of an antilipschitz map at an interior point satisfies
    the same lower bound.
-/
import Sympnet.SympNetUniversal

open Set Filter Topology Metric
open scoped ContDiff NNReal

noncomputable section

namespace SympNet

variable {d : ℕ}

/-! ### Linear algebra -/

theorem symplecticForm_self_J (v : X d) :
    symplecticForm v (-v.2, v.1) = ∑ i, (v.1 i ^ 2 + v.2 i ^ 2) := by
  simp only [symplecticForm]; refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

theorem eq_zero_of_symplecticForm {v : X d} (h : ∀ w, symplecticForm v w = 0) : v = 0 := by
  have h1 := h (-v.2, v.1)
  rw [symplecticForm_self_J] at h1
  have hi : ∀ i ∈ Finset.univ, v.1 i ^ 2 + v.2 i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => by positivity).1 h1
  ext i
  · have := hi i (Finset.mem_univ _); simp; nlinarith [sq_nonneg (v.1 i), sq_nonneg (v.2 i)]
  · have := hi i (Finset.mem_univ _); simp; nlinarith [sq_nonneg (v.1 i), sq_nonneg (v.2 i)]

theorem injective_of_symplectic {L : X d →L[ℝ] X d}
    (hL : ∀ v w, symplecticForm (L v) (L w) = symplecticForm v w) : Function.Injective L := by
  refine (injective_iff_map_eq_zero L).2 fun v hv => ?_
  apply eq_zero_of_symplecticForm
  intro w
  rw [← hL, show L v = 0 from hv]
  simp [symplecticForm]

/-- A linear map with a lower bound is an equivalence with a bounded inverse. -/
theorem exists_equiv_of_lower_bound {T : X d →L[ℝ] X d} {a : ℝ} (ha : 0 < a)
    (hT : ∀ v, a * ‖v‖ ≤ ‖T v‖) :
    ∃ e : X d ≃L[ℝ] X d, (e : X d →L[ℝ] X d) = T ∧ ∀ w, ‖e.symm w‖ ≤ a⁻¹ * ‖w‖ := by
  have hinj : Function.Injective T := by
    intro v w hvw
    have := hT (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at this
    have : ‖v - w‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (v - w)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective (f := T.toLinearMap)).1 hinj
  let e := ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj)
  refine ⟨e, ContinuousLinearMap.ext fun v => by simp [e], fun w => ?_⟩
  have h1 := hT (e.symm w)
  have h2 : T (e.symm w) = w := by
    have := e.apply_symm_apply w
    simpa [e] using this
  rw [h2] at h1
  rw [inv_mul_eq_div, le_div_iff₀ ha]
  linarith

theorem exists_lower_bound_of_injective {L : X d →L[ℝ] X d} (hL : Function.Injective L) :
    ∃ c > 0, ∀ v, c * ‖v‖ ≤ ‖L v‖ := by
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective (f := L.toLinearMap)).1 hL
  let e := ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.2 hL)
    (LinearMap.range_eq_top.2 hsurj)
  refine ⟨(‖(e.symm : X d →L[ℝ] X d)‖ + 1)⁻¹, by positivity, fun v => ?_⟩
  have h1 : ‖v‖ ≤ ‖(e.symm : X d →L[ℝ] X d)‖ * ‖L v‖ := by
    have := (e.symm : X d →L[ℝ] X d).le_opNorm (L v)
    have h2 : (e.symm : X d →L[ℝ] X d) (L v) = v := by
      have := e.symm_apply_apply v; simpa [e] using this
    rwa [h2] at this
  rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (L v), norm_nonneg (e.symm : X d →L[ℝ] X d)]

/-! ### Antilipschitz bounds -/

/-- Local antilipschitz bound from an injective strict derivative. -/
theorem exists_local_antilipschitz {F : X d → X d} {L : X d →L[ℝ] X d} {x : X d}
    (hF : HasStrictFDerivAt F L x) (hL : Function.Injective L) :
    ∃ c > 0, ∃ r > 0, ∀ a ∈ ball x r, ∀ b ∈ ball x r, c * ‖a - b‖ ≤ ‖F a - F b‖ := by
  obtain ⟨cL, hcL, hcL'⟩ := exists_lower_bound_of_injective hL
  obtain ⟨s, hs, hsF⟩ := hF.approximates_deriv_on_nhds (c := ⟨cL / 2, by positivity⟩)
    (Or.inr (by exact_mod_cast half_pos hcL))
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  refine ⟨cL / 2, half_pos hcL, r, hr, fun a ha b hb => ?_⟩
  have h1 : ‖F a - F b - L (a - b)‖ ≤ cL / 2 * ‖a - b‖ := hsF a (hrs ha) b (hrs hb)
  have h2 := hcL' (a - b)
  have h3 : ‖L (a - b)‖ ≤ ‖F a - F b‖ + ‖F a - F b - L (a - b)‖ := by
    have := norm_sub_le (F a - F b) (F a - F b - L (a - b))
    simpa using this
  linarith

/-- **Uniform antilipschitz bound on a compact set.** -/
theorem exists_antilipschitz {F : X d → X d} {U D : Set (X d)} (hU : IsOpen U)
    (hD : IsCompact D) (hDU : D ⊆ U) (hF : ContDiffOn ℝ 1 F U) (hinj : InjOn F U)
    (hDF : ∀ x ∈ U, Function.Injective (fderiv ℝ F x)) :
    ∃ c > 0, ∀ x ∈ D, ∀ y ∈ D, c * ‖x - y‖ ≤ ‖F x - F y‖ := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ p : X d × X d, p.1 ∈ D ∧ p.2 ∈ D ∧
      ‖F p.1 - F p.2‖ < (1 / (n + 1 : ℝ)) * ‖p.1 - p.2‖ := by
    intro n
    obtain ⟨x, hx, y, hy, hxy⟩ := hcon (1 / (n + 1 : ℝ)) (by positivity)
    exact ⟨(x, y), hx, hy, hxy⟩
  choose p hp1 hp2 hp3 using hseq
  have hDD : IsCompact (D ×ˢ D) := hD.prod hD
  obtain ⟨q, hq, φ, hφ, hlim⟩ := hDD.tendsto_subseq (fun n => mk_mem_prod (hp1 n) (hp2 n))
  have hcont : ContinuousOn F U := hF.continuousOn
  have hFq1 : Tendsto (fun n => F (p (φ n)).1) atTop (𝓝 (F q.1)) :=
    ((hcont q.1 (hDU hq.1)).continuousAt (hU.mem_nhds (hDU hq.1))).tendsto.comp
      ((continuous_fst.tendsto q).comp hlim)
  have hFq2 : Tendsto (fun n => F (p (φ n)).2) atTop (𝓝 (F q.2)) :=
    ((hcont q.2 (hDU hq.2)).continuousAt (hU.mem_nhds (hDU hq.2))).tendsto.comp
      ((continuous_snd.tendsto q).comp hlim)
  obtain ⟨R, hR⟩ := hD.isBounded.exists_norm_le
  set B := 2 * R
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR _ (hp1 0))
  have hB : ∀ n, ‖(p n).1 - (p n).2‖ ≤ B := fun n => by
    have := norm_sub_le (p n).1 (p n).2
    linarith [hR _ (hp1 n), hR _ (hp2 n)]
  by_cases hq12 : q.1 = q.2
  · -- local contradiction
    set x := q.1
    have hxU : x ∈ U := hDU hq.1
    have hFx : HasStrictFDerivAt F (fderiv ℝ F x) x :=
      (hF.contDiffAt (hU.mem_nhds hxU)).hasStrictFDerivAt' (by
        exact ((hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt one_ne_zero).hasFDerivAt)
        one_ne_zero
    obtain ⟨c, hc, r, hr, hloc⟩ := exists_local_antilipschitz hFx (hDF x hxU)
    have hev1 : ∀ᶠ n in atTop, (p (φ n)).1 ∈ ball x r :=
      ((continuous_fst.tendsto q).comp hlim).eventually (ball_mem_nhds x hr)
    have hev2 : ∀ᶠ n in atTop, (p (φ n)).2 ∈ ball x r := by
      have := ((continuous_snd.tendsto q).comp hlim).eventually (ball_mem_nhds q.2 hr)
      rwa [← hq12] at this
    have hev3 : ∀ᶠ n in atTop, 1 / ((φ n : ℝ) + 1) < c := by
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact (h1.comp hφ.tendsto_atTop).eventually (gt_mem_nhds hc)
    obtain ⟨n, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
    have h4 := hloc _ h1 _ h2
    have h5 := hp3 (φ n)
    have hne : 0 < ‖(p (φ n)).1 - (p (φ n)).2‖ := by
      by_contra h0
      push Not at h0
      have h00 : ‖(p (φ n)).1 - (p (φ n)).2‖ = 0 := le_antisymm h0 (norm_nonneg _)
      rw [h00, mul_zero] at h5
      exact absurd h5 (not_lt.2 (norm_nonneg _))
    nlinarith
  · -- global contradiction with injectivity
    apply hq12
    apply hinj (hDU hq.1) (hDU hq.2)
    have hlim0 : Tendsto (fun n => F (p (φ n)).1 - F (p (φ n)).2) atTop (𝓝 0) := by
      have hz : Tendsto (fun n => 1 / ((φ n : ℝ) + 1) * B) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).mul_const B
        simpa using this
      refine squeeze_zero_norm (fun n => ?_) hz
      exact (hp3 (φ n)).le.trans (mul_le_mul_of_nonneg_left (hB _) (by positivity))
    have := hFq1.sub hFq2
    exact sub_eq_zero.1 (tendsto_nhds_unique this hlim0)

/-- The derivative of an antilipschitz map at an interior point has the same lower bound. -/
theorem lower_bound_fderiv {F : X d → X d} {L : X d →L[ℝ] X d} {x : X d} {S : Set (X d)}
    (hS : S ∈ 𝓝 x) (hF : HasFDerivAt F L x) {c : ℝ}
    (hc : ∀ a ∈ S, ∀ b ∈ S, c * ‖a - b‖ ≤ ‖F a - F b‖) (v : X d) : c * ‖v‖ ≤ ‖L v‖ := by
  -- along the ray x + h v, h → 0⁺
  have hray : Tendsto (fun h : ℝ => x + h • v) (𝓝[>] 0) (𝓝 x) := by
    have : Continuous fun h : ℝ => x + h • v := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hder : Tendsto (fun h : ℝ => h⁻¹ • (F (x + h • v) - F x)) (𝓝[>] 0) (𝓝 (L v)) :=
    (hF.hasLineDerivAt v).tendsto_slope_zero_right
  have hev : ∀ᶠ h : ℝ in 𝓝[>] 0, c * ‖v‖ ≤ ‖h⁻¹ • (F (x + h • v) - F x)‖ := by
    filter_upwards [hray.eventually hS, self_mem_nhdsWithin] with h hh hpos
    have hpos' : (0 : ℝ) < h := hpos
    have := hc _ hh x (mem_of_mem_nhds hS)
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hpos'.le] at this
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos'.le)]
    rw [show c * ‖v‖ = h⁻¹ * (c * (h * ‖v‖)) by field_simp]
    exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 hpos'.le)
  exact ge_of_tendsto hder.norm hev

end SympNet
