/-
  T-I: interpolation. A function that is C⁰-small and C^{r+1}-bounded on a thickening of K is
  C^r-small on K (Taylor's formula along segments, by induction on the order).
-/
import Sympnet.Turaev.Hadamard

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace SympNet

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- One interpolation step: `‖D^{j+1} f x‖ ≤ 2e/τ + Mτ`. -/
theorem interp_step {f : V → W} {j : ℕ} (hf : ContDiff ℝ (j + 2 : ℕ) f) {S : Set V}
    {e M τ : ℝ} (hτ : 0 < τ) {x : V} (hx : closedBall x τ ⊆ S)
    (he : ∀ y ∈ S, ‖iteratedFDeriv ℝ j f y‖ ≤ e)
    (hM : ∀ y ∈ S, ‖iteratedFDeriv ℝ (j + 2) f y‖ ≤ M) :
    ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ 2 * e / τ + M * τ := by
  have hxS : x ∈ S := hx (mem_closedBall_self hτ.le)
  have he0 : 0 ≤ e := (norm_nonneg _).trans (he x hxS)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hxS)
  set g := iteratedFDeriv ℝ j f
  have hg : ContDiff ℝ 1 g := hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + j ≤ j + 2 by omega))
  have hg1 : ContDiff ℝ 1 (iteratedFDeriv ℝ (j + 1) f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + (j + 1) ≤ j + 2 by omega))
  set Dg := fderiv ℝ g
  have hDg : ∀ y, Dg y = continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => V) W
      (iteratedFDeriv ℝ (j + 1) f y) := fun y => by
    simp only [Dg, g, fderiv_iteratedFDeriv, Function.comp_apply]
  -- (a) Lipschitz bound for `D^{j+1} f` on the ball
  have ha : ∀ y ∈ closedBall x τ, ‖Dg y - Dg x‖ ≤ M * ‖y - x‖ := by
    intro y hy
    rw [hDg, hDg, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
    refine (convex_closedBall x τ).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hg1.differentiable one_ne_zero) z) (fun z hz => ?_)
      (mem_closedBall_self hτ.le) hy
    rw [norm_fderiv_iteratedFDeriv]; exact hM z (hx hz)
  -- (b) the remainder ψ(y) = g y − Dg x (y − x)
  set ψ : V → _ := fun y => g y - Dg x (y - x)
  have hψ : ∀ y, HasFDerivAt ψ (Dg y - Dg x) y := by
    intro y
    have h1 : HasFDerivAt g (Dg y) y := ((hg.differentiable one_ne_zero) y).hasFDerivAt
    have h2 : HasFDerivAt (fun y => Dg x (y - x)) (Dg x) y := by
      have := (Dg x).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
      rwa [ContinuousLinearMap.comp_id] at this
    exact h1.sub h2
  have hb : ∀ v, ‖v‖ ≤ τ → ‖ψ (x + v) - ψ x‖ ≤ M * τ * ‖v‖ := by
    intro v hv
    have hxv : x + v ∈ closedBall x τ := by simpa [mem_closedBall, dist_eq_norm] using hv
    have := (convex_closedBall x τ).norm_image_sub_le_of_norm_fderiv_le (C := M * τ)
      (fun z _ => (hψ z).differentiableAt) (fun z hz => by
        rw [(hψ z).fderiv]
        calc ‖Dg z - Dg x‖ ≤ M * ‖z - x‖ := ha z hz
          _ ≤ M * τ := by
            gcongr; simpa [mem_closedBall, dist_eq_norm] using hz)
      (mem_closedBall_self hτ.le) hxv
    simpa using this
  -- (c) bound on vectors of norm ≤ τ
  have hc : ∀ v, ‖v‖ ≤ τ → ‖Dg x v‖ ≤ 2 * e + M * τ * ‖v‖ := by
    intro v hv
    have hxv : x + v ∈ S := hx (by simpa [mem_closedBall, dist_eq_norm] using hv)
    have eq : Dg x v = g (x + v) - g x - (ψ (x + v) - ψ x) := by
      simp only [ψ, add_sub_cancel_left, sub_self, map_zero, sub_zero]; abel
    rw [eq]
    calc ‖g (x + v) - g x - (ψ (x + v) - ψ x)‖
        ≤ ‖g (x + v)‖ + ‖g x‖ + ‖ψ (x + v) - ψ x‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr; exact norm_sub_le _ _
      _ ≤ e + e + M * τ * ‖v‖ := by gcongr; exacts [he _ hxv, he _ hxS, hb v hv]
      _ = 2 * e + M * τ * ‖v‖ := by ring
  -- (d) operator norm
  have hfin : ‖Dg x‖ ≤ 2 * e / τ + M * τ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
    set w := (τ / ‖v‖) • v
    have hw : ‖w‖ = τ := by
      simp only [w, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hτ, abs_norm]
      field_simp
    have h1 := hc w hw.le
    rw [hw, map_smul, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hτ, abs_norm] at h1
    have h2 : ‖Dg x v‖ ≤ (2 * e + M * τ * τ) * ‖v‖ / τ := by
      rw [le_div_iff₀ hτ]
      have := mul_le_mul_of_nonneg_right h1 hn.le
      have e2 : τ / ‖v‖ * ‖Dg x v‖ * ‖v‖ = ‖Dg x v‖ * τ := by field_simp
      linarith
    calc ‖Dg x v‖ ≤ (2 * e + M * τ * τ) * ‖v‖ / τ := h2
      _ = (2 * e / τ + M * τ) * ‖v‖ := by field_simp
  have : ‖Dg x‖ = ‖iteratedFDeriv ℝ (j + 1) f x‖ := norm_fderiv_iteratedFDeriv
  rw [← this]; exact hfin

/-- **Interpolation.** -/
theorem interp (r : ℕ) (K : Set V) {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∀ η > 0, ∃ ε₀ > 0, ∀ f : V → W, ContDiff ℝ (r + 1 : ℕ) f →
      (∀ l ≤ r + 1, ∀ x ∈ cthickening δ K, ‖iteratedFDeriv ℝ l f x‖ ≤ M) →
      (∀ x ∈ cthickening δ K, ‖f x‖ ≤ ε₀) →
      ∀ l ≤ r, ∀ x ∈ K, ‖iteratedFDeriv ℝ l f x‖ ≤ η := by
  set M' := max M 0
  have aux : ∀ n ≤ r, ∀ η > 0, ∃ ε₀ > 0, ∀ f : V → W, ContDiff ℝ (r + 1 : ℕ) f →
      (∀ l ≤ r + 1, ∀ x ∈ cthickening δ K, ‖iteratedFDeriv ℝ l f x‖ ≤ M) →
      (∀ x ∈ cthickening δ K, ‖f x‖ ≤ ε₀) →
      ∀ l ≤ n, ∀ x ∈ cthickening (δ / 2 ^ n) K, ‖iteratedFDeriv ℝ l f x‖ ≤ η := by
    intro n
    induction n with
    | zero =>
      intro _ η hη
      refine ⟨η, hη, fun f _ _ h0 l hl x hx => ?_⟩
      obtain rfl := Nat.le_zero.1 hl
      rw [norm_iteratedFDeriv_zero]; exact h0 x (by simpa using hx)
    | succ n ih =>
      intro hn η hη
      set τ := min (δ / 2 ^ (n + 1)) (η / (2 * (M' + 1)))
      have hM' : 0 ≤ M' := le_max_right _ _
      have hτ : 0 < τ := lt_min (by positivity) (by positivity)
      set e := η * τ / 4
      have he : 0 < e := by positivity
      obtain ⟨ε₀, hε₀, hε₀'⟩ := ih (by omega) (min e η) (lt_min he hη)
      refine ⟨ε₀, hε₀, fun f hf hb h0 l hl x hx => ?_⟩
      have hsub : cthickening (δ / 2 ^ (n + 1)) K ⊆ cthickening (δ / 2 ^ n) K :=
        cthickening_mono (div_le_div_of_nonneg_left hδ.le (by positivity)
          (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))) K
      rcases Nat.lt_or_ge l (n + 1) with hl' | hl'
      · exact (hε₀' f hf hb h0 l (by omega) x (hsub hx)).trans (min_le_right _ _)
      obtain rfl : l = n + 1 := le_antisymm hl hl'
      have hball : closedBall x τ ⊆ cthickening (δ / 2 ^ n) K := by
        refine (closedBall_subset_cthickening hx τ).trans
          ((cthickening_cthickening_subset hτ.le (by positivity) K).trans
            (cthickening_mono ?_ K))
        have h1 : τ ≤ δ / 2 ^ (n + 1) := min_le_left _ _
        have h2 : δ / 2 ^ (n + 1) + δ / 2 ^ (n + 1) = δ / 2 ^ n := by
          rw [pow_succ]; field_simp; ring
        linarith
      have hS : cthickening (δ / 2 ^ n) K ⊆ cthickening δ K :=
        cthickening_mono (div_le_self hδ.le (one_le_pow₀ (by norm_num))) K
      have key := interp_step (j := n) (hf.of_le (by exact_mod_cast (by omega : n + 2 ≤ r + 1)))
        hτ hball (fun y hy => (hε₀' f hf hb h0 n le_rfl y hy).trans (min_le_left _ _))
        (fun y hy => hb (n + 2) (by omega) y (hS hy))
      refine key.trans ?_
      have h1 : 2 * e / τ = η / 2 := by simp only [e]; field_simp; ring
      have h2 : M * τ ≤ η / 2 := by
        calc M * τ ≤ M' * τ := by gcongr; exact le_max_left _ _
          _ ≤ (M' + 1) * (η / (2 * (M' + 1))) := by
            gcongr; · linarith
            exact min_le_right _ _
          _ = η / 2 := by field_simp
      linarith
  intro η hη
  obtain ⟨ε₀, hε₀, h⟩ := aux r le_rfl η hη
  exact ⟨ε₀, hε₀, fun f hf hb h0 l hl x hx => h f hf hb h0 l hl x (self_subset_cthickening _ hx)⟩

end SympNet
