/-
  C1: composition stability with the inner map valued in a finite-dimensional space `Z`
  (generalizes `comp_two_stable`; needed for D(Ψ⁻¹) = J ∘ (Dg ∘ Ψ⁻¹)).
-/
import Sympnet.SympNetUniversal

open scoped ContDiff

noncomputable section

namespace SympNet

variable {d : ℕ}

/-- The zeroth-order estimate for compositions (uniform continuity on the enlargement). -/
theorem comp_zero_estimate' {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X d → Z} {h : Z → Y} (hf : Continuous f) (hh : Continuous h)
    {K : Set (X d)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ S, Metric.cthickening 1 (f '' K) ⊆ S → ∀ (g : X d → Z) (u : Z → Y),
      (∀ x ∈ K, ‖f x - g x‖ ≤ δ) → (∀ y ∈ S, ‖h y - u y‖ ≤ δ) →
        ∀ x ∈ K, ‖h (f x) - u (g x)‖ ≤ ε := by
  have huc := ((hK.image hf).cthickening (r := 1)).uniformContinuousOn_of_continuous hh.continuousOn
  obtain ⟨δ', hδ', hδ'h⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
  refine ⟨min (min (δ' / 2) 1) (ε / 2), by positivity,
    (min_le_left _ _).trans (min_le_right _ _), fun S hS g u hfg hhu x hx => ?_⟩
  have hδ1 : min (min (δ' / 2) 1) (ε / 2) ≤ δ' / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : min (min (δ' / 2) 1) (ε / 2) ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : min (min (δ' / 2) 1) (ε / 2) ≤ ε / 2 := min_le_right _ _
  have hd : dist (g x) (f x) ≤ min (min (δ' / 2) 1) (ε / 2) := by
    rw [dist_eq_norm, norm_sub_rev]; exact hfg x hx
  have hgx : g x ∈ Metric.cthickening 1 (f '' K) :=
    Metric.mem_cthickening_of_dist_le _ (f x) 1 _ ⟨x, hx, rfl⟩ (hd.trans hδ2)
  have hfx : f x ∈ Metric.cthickening 1 (f '' K) :=
    Metric.mem_cthickening_of_dist_le _ (f x) 1 _ ⟨x, hx, rfl⟩ (by simp)
  have e1 : dist (h (f x)) (h (g x)) < ε / 2 :=
    hδ'h _ hfx _ hgx (by rw [dist_comm]; linarith)
  have e2 := hhu (g x) (hS hgx)
  rw [dist_eq_norm] at e1
  calc ‖h (f x) - u (g x)‖ = ‖(h (f x) - h (g x)) + (h (g x) - u (g x))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖h (f x) - h (g x)‖ + ‖h (g x) - u (g x)‖ := norm_add_le _ _
    _ ≤ ε := by linarith

/-- Two-map `C^r` stability of composition, with the inner map valued in a finite-dimensional
space `Z`. Closeness of the inner maps is only needed on `K`.  The outer map takes values
in an arbitrary normed space, since the inductive step is applied to `Dh : X → L(X, Y)`. -/
theorem comp_two_stable' (r : ℕ) : ∀ {Z Y : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X d → Z) (h : Z → Y), ContDiff ℝ r f → ContDiff ℝ r h →
    ∀ K : Set (X d), IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ S : Set Z,
      Metric.cthickening 1 (f '' K) ⊆ S →
    ∀ (g : X d → Z) (u : Z → Y), ContDiff ℝ r g → ContDiff ℝ r u →
      CrCloseLe r K f g δ → CrCloseLe r S h u δ → CrCloseLe r K (h ∘ f) (u ∘ g) ε := by
  induction r with
  | zero =>
    intro Z Y _ _ _ _ _ f h hf hh K hK ε hε
    obtain ⟨δ, hδ, -, hδ'⟩ := comp_zero_estimate' hf.continuous hh.continuous hK hε
    refine ⟨δ, hδ, fun S hS g u hg hu hfg hhu k hk x hx => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    rw [norm_iteratedFDeriv_zero_sub (hh.comp hf) (hu.comp hg)]
    exact hδ' S hS g u
      (fun y hy => hfg.norm_sub_le hf hg hy)
      (fun y hy => hhu.norm_sub_le hh hu hy) x hx
  | succ r ih =>
    intro Z Y _ _ _ _ _ f h hf hh K hK ε hε
    have hr1 : ((r + 1 : ℕ) : ℕ∞ω) = ((r : ℕ) : ℕ∞ω) + 1 := by push_cast; ring
    have hrle : ((r : ℕ) : ℕ∞ω) ≤ ((r + 1 : ℕ) : ℕ∞ω) := Nat.cast_le.mpr (Nat.le_succ r)
    have hdh : ContDiff ℝ r (fun y => fderiv ℝ h y) := hh.fderiv_right (by rw [hr1])
    have hfr : ContDiff ℝ r f := hf.of_le hrle
    obtain ⟨Mf, hMf0, hMf⟩ := exists_crBound (r + 1) hK hf
    obtain ⟨Ma, hMa0, hMa⟩ := exists_crBound r hK (hdh.comp hfr)
    set C : ℝ := 2 ^ r * (Mf + Ma + 2) with hC
    have hCpos : 0 < C := by positivity
    set t : ℝ := ε / (2 * C) with ht
    have ht0 : 0 < t := by positivity
    have hCt : C * t = ε / 2 := by rw [ht]; field_simp
    set η : ℝ := min 1 t with hη
    have hη0 : 0 < η := lt_min one_pos ht0
    obtain ⟨δa, hδa, hδa'⟩ := ih f (fun y => fderiv ℝ h y) hfr hdh K hK η hη0
    obtain ⟨δ₀, hδ₀, -, hδ₀'⟩ := comp_zero_estimate' hf.continuous hh.continuous hK hε
    refine ⟨min (min δa δ₀) t, lt_min (lt_min hδa hδ₀) ht0,
      fun S hS g u hg hu hfg hhu => ?_⟩
    set δ := min (min δa δ₀) t
    have hδa_le : δ ≤ δa := (min_le_left _ _).trans (min_le_left _ _)
    have hδ₀_le : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_right _ _)
    have hδt : δ ≤ t := min_le_right _ _
    have hδ0 : 0 ≤ δ := le_of_lt (lt_min (lt_min hδa hδ₀) ht0)
    have hgr : ContDiff ℝ r g := hg.of_le hrle
    have hdu : ContDiff ℝ r (fun y => fderiv ℝ u y) := hu.fderiv_right (by rw [hr1])
    have hdf : ContDiff ℝ r (fun y => fderiv ℝ f y) := hf.fderiv_right (by rw [hr1])
    have hdg : ContDiff ℝ r (fun y => fderiv ℝ g y) := hg.fderiv_right (by rw [hr1])
    -- the induction hypothesis, applied to `Dh ∘ f` versus `Du ∘ g`
    have hA : CrCloseLe r K ((fun y => fderiv ℝ h y) ∘ f) ((fun y => fderiv ℝ u y) ∘ g) η :=
      hδa' S hS g (fun y => fderiv ℝ u y) hgr hdu
        ((hfg.of_le (Nat.le_succ r)).mono_eps hδa_le) ((hhu.fderiv' hh hu).mono_eps hδa_le)
    have hθ : CrCloseLe r K (fun y => fderiv ℝ f y) (fun y => fderiv ℝ g y) δ :=
      hfg.fderiv' hf hg
    intro k hk x hx
    rcases k with _ | m
    · rw [norm_iteratedFDeriv_zero_sub (hh.comp hf) (hu.comp hg)]
      exact hδ₀' S hS g u
        (fun y hy => (hfg.norm_sub_le hf hg hy).trans hδ₀_le)
        (fun y hy => (hhu.norm_sub_le hh hu hy).trans hδ₀_le) x hx
    · have hm : m ≤ r := by omega
      have hmle : ((m : ℕ) : ℕ∞ω) ≤ ((r : ℕ) : ℕ∞ω) := Nat.cast_le.mpr hm
      have hm1 : ((m + 1 : ℕ) : ℕ∞ω) ≤ ((r + 1 : ℕ) : ℕ∞ω) := Nat.cast_le.mpr (by omega)
      rw [norm_iteratedFDeriv_succ_sub ((hh.comp hf).of_le hm1) ((hu.comp hg).of_le hm1) x]
      have ef : (fun y => fderiv ℝ (h ∘ f) y) = fun y =>
          ContinuousLinearMap.compL ℝ (X d) Z Y (fderiv ℝ h (f y)) (fderiv ℝ f y) := by
        funext y
        rw [fderiv_comp y ((hh.differentiable (by positivity)) (f y))
          ((hf.differentiable (by positivity)) y)]
        rfl
      have eg : (fun y => fderiv ℝ (u ∘ g) y) = fun y =>
          ContinuousLinearMap.compL ℝ (X d) Z Y (fderiv ℝ u (g y)) (fderiv ℝ g y) := by
        funext y
        rw [fderiv_comp y ((hu.differentiable (by positivity)) (g y))
          ((hg.differentiable (by positivity)) y)]
        rfl
      rw [ef, eg]
      have hη1 : η ≤ 1 := min_le_left _ _
      have hηt : η ≤ t := min_le_right _ _
      have h2m : (2 : ℝ) ^ m ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hm
      have hbil := bilinear_diff_estimate (ContinuousLinearMap.compL ℝ (X d) Z Y)
        (ContinuousLinearMap.norm_compL_le ℝ (X d) Z Y)
        (p₁ := fun y => fderiv ℝ h (f y)) (p₂ := fun y => fderiv ℝ u (g y))
        (q₁ := fun y => fderiv ℝ f y) (q₂ := fun y => fderiv ℝ g y)
        ((hdh.comp hfr).of_le hmle) ((hdu.comp hgr).of_le hmle) (hdf.of_le hmle)
        (hdg.of_le hmle) x hη0.le hδ0 hMa0 hMf0
        (fun i hi => hA i (hi.trans hm) x hx)
        (fun i hi => by
          rw [norm_iteratedFDeriv_fderiv]; exact hMf (i + 1) (by omega) x hx)
        (fun i hi => hMa i (hi.trans hm) x hx)
        (fun i hi => hθ i (hi.trans hm) x hx)
      refine hbil.trans ?_
      have hp : 0 ≤ (2 : ℝ) ^ r * t := by positivity
      calc (2 : ℝ) ^ m * (η * Mf + (Ma + η) * δ)
          ≤ 2 ^ r * (t * Mf + (Ma + 1) * t) := by
            gcongr
        _ ≤ C * t := by rw [hC]; nlinarith
        _ = ε / 2 := hCt
        _ ≤ ε := by linarith

end SympNet
