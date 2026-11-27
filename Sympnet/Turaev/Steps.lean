/-
  T-E: estimates for the exact steps A(h, t) = Gt(t + h) ∘ Git(t) of the Alexander isotopy, and
  the ridge approximation of its velocity field.
-/
import Sympnet.Turaev.Blocks

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace SympNet

variable {d : ℕ}

/-- J as a continuous linear map on covectors. -/
def JopL (d : ℕ) : (X d →L[ℝ] ℝ) →L[ℝ] X d := (-(clmQ d)).prod (clmP d)

theorem JopL_apply (ℓ : X d →L[ℝ] ℝ) : JopL d ℓ = Jop d ℓ := rfl

theorem hasFDerivAt_Nr (ρs : List (Ridge d)) (t : ℝ) (z : X d) :
    HasFDerivAt (fun z => Nr ρs (t, z))
      (ρs.map fun ρ => (ρ.1 * deriv bumpAct (ρ.2.2 (t, z) + ρ.2.1)) • ρ.ell).sum z := by
  induction ρs with
  | nil => simpa [Nr] using hasFDerivAt_const (0 : ℝ) z
  | cons ρ ρs ih =>
    have hin : HasFDerivAt (fun z : X d => ρ.2.2 (t, z) + ρ.2.1) ρ.ell z := by
      have : HasFDerivAt (fun z : X d => ρ.2.2 (t, z)) ρ.ell z :=
        ρ.2.2.hasFDerivAt.comp z ((hasFDerivAt_const t z).prodMk (hasFDerivAt_id z))
      exact this.add_const _
    have h1 := (((contDiff_bumpAct.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt z
      hin).const_mul ρ.1
    have h2 := h1.add ih
    simp only [List.map_cons, List.sum_cons]
    convert h2 using 1
    · funext z; simp [Nr]
    · rw [smul_smul]

theorem Xa_eq (ρs : List (Ridge d)) (t : ℝ) (z : X d) :
    Xa ρs (t, z) = -JopL d (fderiv ℝ (fun z => Nr ρs (t, z)) z) := by
  rw [(hasFDerivAt_Nr ρs t z).fderiv]
  induction ρs with
  | nil => simp [Xa]
  | cons ρ ρs ih =>
    have e1 : Xa (ρ :: ρs) (t, z) = rterm ρ (t, z) + Xa ρs (t, z) := by simp [Xa]
    rw [e1, ih, List.map_cons, List.sum_cons, map_add, neg_add]
    congr 1
    rw [map_smul, JopL_apply, rterm, neg_smul]

section Exact

variable {G : X d → X d} (hG : G ∈ SympDiffeo d) (h0 : G 0 = 0)
include hG h0

theorem hasDerivAt_alexT_shift (t : ℝ) (x : X d) :
    HasDerivAt (fun h => alexT G (t + h, x)) (velY G (t, x)) 0 := by
  have h1 := dT_eq_deriv (p := (t, x)) (((contDiff_alexT hG.1).differentiable (by simp)) _)
  have h1' : HasDerivAt (fun s => alexT G (s, x)) (velY G (t, x)) (t + 0) := by
    rw [add_zero]; exact h1
  exact h1'.comp_const_add t 0

/-- C⁰ consistency of the exact step: A(h, t) z − z − h X(t, z) = O(h²). -/
theorem exact_step_consistency {R : Set (X d)} (hR : IsCompact R) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ R,
      ‖alexT G (t + h, alexT (sdInv G) (t, z)) - z - h • velX G (t, z)‖ ≤ h ^ 2 * C := by
  set F := alexT G
  set Fi := alexT (sdInv G)
  have hF : ContDiff ℝ ∞ F := contDiff_alexT hG.1
  have hFi : ContDiff ℝ ∞ Fi := contDiff_alexT (sd_contDiff_inv hG)
  set f : ℝ × (ℝ × X d) → X d := fun q => F (q.2.1 + q.1, q.2.2) - F q.2 - q.1 • velY G q.2
  have hf : ContDiff ℝ ∞ f :=
    ((hF.comp (((contDiff_fst.comp contDiff_snd).add contDiff_fst).prodMk
      (contDiff_snd.comp contDiff_snd))).sub (hF.comp contDiff_snd)).sub
      (contDiff_fst.smul ((contDiff_velY hG h0).comp contDiff_snd))
  have hf0 : ∀ y, f (0, y) = 0 := fun y => by simp [f]
  have hf1 : ∀ y, dT f (0, y) = 0 := by
    intro y
    have h1 := dT_eq_deriv (p := ((0 : ℝ), y)) ((hf.differentiable (by simp)) _)
    have h2 : HasDerivAt (fun h => f (h, y)) 0 0 := by
      have := (((hasDerivAt_alexT_shift hG h0 y.1 y.2).sub (hasDerivAt_const (0 : ℝ) (F y))).sub
        ((hasDerivAt_id (0 : ℝ)).smul_const (velY G y))).congr_deriv
        (show velY G y - 0 - (1 : ℝ) • velY G y = 0 by simp)
      exact this
    exact h1.unique h2
  set g := hadQ (hadQ f)
  have hg : ContDiff ℝ ∞ g := contDiff_hadQ (contDiff_hadQ hf)
  set S : Set (ℝ × (ℝ × X d)) := Icc (0 : ℝ) 1 ×ˢ
    ((fun p : ℝ × X d => (p.1, Fi p)) '' (Icc (0 : ℝ) 1 ×ˢ R))
  have hS : IsCompact S := isCompact_Icc.prod ((isCompact_Icc.prod hR).image
    (continuous_fst.prodMk hFi.continuous))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hg.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun h hh t ht z hz => ?_⟩
  have hz' : F (t, Fi (t, z)) = z := alexT_inv_right hG h0 t z
  have heq : F (t + h, Fi (t, z)) - z - h • velX G (t, z) = (h ^ 2) • g (h, (t, Fi (t, z))) := by
    have := hadamard2_eq hf hf0 hf1 (h, (t, Fi (t, z)))
    simp only [f, add_comm t h] at this
    rw [← this, hz', add_comm t h]; rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
  exact mul_le_mul_of_nonneg_left ((hC _ ⟨hh, ⟨(t, z), ⟨ht, hz⟩, rfl⟩⟩).trans (le_max_left _ _))
    (sq_nonneg h)

/-- Lipschitz bound of the exact step on a convex compact set: Lip ≤ 1 + hL. -/
theorem exact_step_lip {R : Set (X d)} (hR : IsCompact R) (hRc : Convex ℝ R) :
    ∃ L, 0 ≤ L ∧ ∀ h ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ R, ∀ z' ∈ R,
      ‖alexT G (t + h, alexT (sdInv G) (t, z)) - alexT G (t + h, alexT (sdInv G) (t, z'))‖ ≤
        (1 + h * L) * ‖z - z'‖ := by
  set F := alexT G
  set Fi := alexT (sdInv G)
  have hF : ContDiff ℝ ∞ F := contDiff_alexT hG.1
  have hFi : ContDiff ℝ ∞ Fi := contDiff_alexT (sd_contDiff_inv hG)
  set f : ℝ × (ℝ × X d) → X d := fun q => F (q.2.1 + q.1, q.2.2) - F q.2
  have hf : ContDiff ℝ ∞ f :=
    (hF.comp (((contDiff_fst.comp contDiff_snd).add contDiff_fst).prodMk
      (contDiff_snd.comp contDiff_snd))).sub (hF.comp contDiff_snd)
  have hf0 : ∀ y, f (0, y) = 0 := fun y => by simp [f]
  set g := hadQ f
  have hg : ContDiff ℝ ∞ g := contDiff_hadQ hf
  set W : ℝ × (ℝ × X d) → X d := fun q => g (q.1, (q.2.1, Fi q.2))
  have hW : ContDiff ℝ ∞ W := hg.comp (contDiff_fst.prodMk
    ((contDiff_fst.comp contDiff_snd).prodMk (hFi.comp contDiff_snd)))
  obtain ⟨L, hL0, hL⟩ := exists_bound3 hW 1 hR
  refine ⟨L, hL0, fun h hh t ht z hz z' hz' => ?_⟩
  have hA : ∀ w, F (t + h, Fi (t, w)) = w + h • W (h, (t, w)) := by
    intro w
    have h1 := hadamard_eq hf hf0 (h, (t, Fi (t, w)))
    have hz' : F (t, Fi (t, w)) = w := alexT_inv_right hG h0 t w
    calc F (t + h, Fi (t, w)) = F (t, Fi (t, w)) + f (h, (t, Fi (t, w))) := by
          simp only [f]; abel
      _ = w + h • W (h, (t, w)) := by rw [hz', h1]
  have hWs : ContDiff ℝ ∞ (fun w => W (h, (t, w))) := by
    have h2 : ContDiff ℝ ∞ (fun w : X d => ((h, (t, w)) : ℝ × (ℝ × X d))) :=
      contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
    exact hW.comp h2
  have hmv : ‖W (h, (t, z)) - W (h, (t, z'))‖ ≤ L * ‖z - z'‖ :=
    hRc.norm_image_sub_le_of_norm_fderiv_le (f := fun w => W (h, (t, w)))
      (fun w _ => (hWs.differentiable (by simp)) w)
      (fun w hw => by rw [← norm_iteratedFDeriv_one]; exact hL h hh t ht w hw 1 le_rfl) hz' hz
  rw [hA, hA]
  calc ‖z + h • W (h, (t, z)) - (z' + h • W (h, (t, z')))‖
      = ‖(z - z') + h • (W (h, (t, z)) - W (h, (t, z')))‖ := by rw [smul_sub]; congr 1; abel
    _ ≤ ‖z - z'‖ + h * (L * ‖z - z'‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh.1]
        exact mul_le_mul_of_nonneg_left hmv hh.1
    _ = (1 + h * L) * ‖z - z'‖ := by ring

/-- **Ridge approximation of the velocity field** in C^k on [0,1] × R. -/
theorem velX_approx {R : Set (X d)} (hR : IsCompact R) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρs : List (Ridge d), ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ R, ∀ l ≤ k,
      ‖iteratedFDeriv ℝ l (fun z => velX G (t, z) - Xa ρs (t, z)) y‖ ≤ δ := by
  set c := ‖JopL d‖ + 1
  have hc : 0 < c := by positivity
  have hH : ContDiff ℝ ∞ (hamF G) := contDiff_hamF hG h0
  obtain ⟨n, Λ, a, b, hN⟩ := hornik_fd (P := ℝ × X d) (k + 1) (rFinite_bumpAct (k + 1))
    (hH.of_le (by exact_mod_cast le_top)) (isCompact_Icc.prod hR) (ε := δ / c) (by positivity)
  set ρs : List (Ridge d) := List.ofFn fun j => (a j, b j, Λ j)
  have hNr : Nr ρs = fun p => ∑ j, a j * bumpAct (Λ j p + b j) := by
    funext p; simp [Nr, ρs, List.sum_ofFn]
  refine ⟨ρs, fun t ht y hy l hl => ?_⟩
  set D : ℝ × X d → ℝ := hamF G - Nr ρs
  have hD : ContDiff ℝ ∞ D := hH.sub (contDiff_Nr ρs)
  have hDs : ContDiff ℝ ∞ (fun z => D (t, z)) := by
    have h2 : ContDiff ℝ ∞ (fun z : X d => ((t, z) : ℝ × X d)) :=
      contDiff_const.prodMk contDiff_id
    exact hD.comp h2
  have heq : (fun z => velX G (t, z) - Xa ρs (t, z)) =
      ⇑(-JopL d) ∘ fderiv ℝ (fun z => D (t, z)) := by
    funext z
    have h1 := (hasFDerivAt_partial (((hH.differentiable (by simp))) (t, z))).differentiableAt
    have h2 := (hasFDerivAt_partial (((contDiff_Nr ρs).differentiable (by simp)) (t, z))).differentiableAt
    have h3 : fderiv ℝ (fun z => hamF G (t, z) - Nr ρs (t, z)) z =
        fderiv ℝ (fun z => hamF G (t, z)) z - fderiv ℝ (fun z => Nr ρs (t, z)) z :=
      (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv
    rw [velX_eq_Jop hG h0, Xa_eq, Function.comp_apply,
      show (fun z => D (t, z)) = fun z => hamF G (t, z) - Nr ρs (t, z) from rfl, h3,
      ← JopL_apply]
    simp [map_sub]
  rw [heq]
  have hdD : ContDiff ℝ ∞ (fderiv ℝ (fun z => D (t, z))) := hDs.fderiv_right (m := ∞) (by simp)
  refine ((-JopL d).norm_iteratedFDeriv_comp_left hdD.contDiffAt
    (by exact_mod_cast le_top)).trans ?_
  rw [norm_neg, norm_iteratedFDeriv_fderiv]
  have h3 := norm_iteratedFDeriv_partial_le hD (l := l + 1) (by exact_mod_cast le_top) t y
  have h4 : ‖iteratedFDeriv ℝ (l + 1) D (t, y)‖ < δ / c := by
    have := hN (l + 1) (by omega) (t, y) ⟨ht, hy⟩
    rw [← hNr] at this
    rwa [show D = hamF G - Nr ρs from rfl, iteratedFDeriv_sub_apply
      ((hH.of_le (by exact_mod_cast le_top)).contDiffAt)
      (((contDiff_Nr ρs).of_le (by exact_mod_cast le_top)).contDiffAt)]
  calc ‖JopL d‖ * ‖iteratedFDeriv ℝ (l + 1) (fun z => D (t, z)) y‖
      ≤ ‖JopL d‖ * (δ / c) := mul_le_mul_of_nonneg_left (h3.trans h4.le) (norm_nonneg (JopL d))
    _ ≤ c * (δ / c) := mul_le_mul_of_nonneg_right (by simp [c]) (by positivity)
    _ = δ := by field_simp

end Exact

end SympNet
