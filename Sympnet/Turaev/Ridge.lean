/-
  T-R: ridge-function approximation (Hornik) on an arbitrary finite-dimensional space, with a
  smooth compactly supported activation that is r-finite for every r.
-/
import Sympnet.Turaev.Isotopy
import Sympnet.Hornik.MultiCr

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace SympNet

/-- A smooth bump on ℝ, used as activation. -/
def bumpAct : ℝ → ℝ := ⇑(⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ))

theorem contDiff_bumpAct : ContDiff ℝ ∞ bumpAct := ContDiffBump.contDiff _

theorem hasCompactSupport_bumpAct : HasCompactSupport bumpAct := ContDiffBump.hasCompactSupport _

theorem integrable_iteratedDeriv_bumpAct (k : ℕ) : Integrable (iteratedDeriv k bumpAct) := by
  refine Continuous.integrable_of_hasCompactSupport
    (contDiff_bumpAct.continuous_iteratedDeriv k (by exact_mod_cast le_top)) ?_
  refine (hasCompactSupport_bumpAct.iteratedFDeriv (𝕜 := ℝ) k).mono' ?_
  intro x hx
  rw [Function.mem_support, iteratedDeriv_eq_iteratedFDeriv] at hx
  exact subset_closure (Function.mem_support.2 fun h => hx (by rw [h]; rfl))

theorem rFinite_bumpAct (k : ℕ) : RFinite k bumpAct := by
  refine ⟨contDiff_bumpAct.of_le (by exact_mod_cast le_top), integrable_iteratedDeriv_bumpAct k, ?_⟩
  have hcont : Continuous (iteratedDeriv k bumpAct) :=
    contDiff_bumpAct.continuous_iteratedDeriv k (by exact_mod_cast le_top)
  have hne : ∃ x, iteratedDeriv k bumpAct x ≠ 0 := by
    by_contra h
    push Not at h
    have := eq_zero_of_iteratedDeriv_eq_zero contDiff_bumpAct
      (by simpa using integrable_iteratedDeriv_bumpAct 0) h 0
    have h1 : bumpAct 0 = 1 := ContDiffBump.one_of_mem_closedBall _ (by simp)
    rw [h1] at this; exact one_ne_zero this
  obtain ⟨x, hx⟩ := hne
  rw [integral_pos_iff_support_of_nonneg (fun _ => abs_nonneg _)
    (integrable_iteratedDeriv_bumpAct k).abs]
  have hopen : IsOpen (Function.support fun y => |iteratedDeriv k bumpAct y|) :=
    isOpen_ne_fun hcont.abs continuous_const
  exact hopen.measure_pos volume ⟨x, by simpa using hx⟩

/-! ### Transfer of C^r closeness along a linear map -/

theorem crClose_comp_clm {V W Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {k : ℕ} (L : V →L[ℝ] W) {f g : W → Y} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g)
    {K : Set V} {ε : ℝ} (h : CrClose k (L '' K) f g ε) :
    CrClose k K (f ∘ L) (g ∘ L) (ε * (‖L‖ + 1) ^ k) := by
  intro i hi x hx
  have hik : ((i : ℕ) : ℕ∞ω) ≤ k := by exact_mod_cast hi
  rw [L.iteratedFDeriv_comp_right hf x hik, L.iteratedFDeriv_comp_right hg x hik]
  have e : ((iteratedFDeriv ℝ i f (L x)).compContinuousLinearMap fun _ => L) -
      ((iteratedFDeriv ℝ i g (L x)).compContinuousLinearMap fun _ => L) =
      (iteratedFDeriv ℝ i f (L x) - iteratedFDeriv ℝ i g (L x)).compContinuousLinearMap
        fun _ => L := by ext v; simp
  rw [e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_lt ?_
  have h1 := h i hi (L x) ⟨x, hx, rfl⟩
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ‖L‖ ^ i ≤ (‖L‖ + 1) ^ k :=
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg L]) hi)
  have h3 : 0 < (‖L‖ + 1) ^ k := by positivity
  calc ‖iteratedFDeriv ℝ i f (L x) - iteratedFDeriv ℝ i g (L x)‖ * ‖L‖ ^ i
      ≤ ‖iteratedFDeriv ℝ i f (L x) - iteratedFDeriv ℝ i g (L x)‖ * (‖L‖ + 1) ^ k :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ < ε * (‖L‖ + 1) ^ k := mul_lt_mul_of_pos_right h1 h3

/-- **Hornik on a finite-dimensional space**: ridge sums `Σ aⱼ τ(Λⱼ p + bⱼ)` are C^k-dense. -/
theorem hornik_fd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (k : ℕ) {τ : ℝ → ℝ} (hτ : RFinite k τ) {V : P → ℝ} (hV : ContDiff ℝ k V) {K : Set P}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (Λ : Fin n → P →L[ℝ] ℝ) (a b : Fin n → ℝ),
      CrClose k K V (fun p => ∑ j, a j * τ (Λ j p + b j)) ε := by
  set m := Module.finrank ℝ P
  let e : P ≃L[ℝ] E m := ContinuousLinearEquiv.ofFinrankEq (by simp [m])
  set C := (‖(e : P →L[ℝ] E m)‖ + 1) ^ k
  have hC : 0 < C := by positivity
  obtain ⟨n, W, a, b, hN⟩ := hornikDensity m k τ hτ (V ∘ e.symm)
    (hV.comp e.symm.contDiff) (e '' K) (hK.image e.continuous) (ε / C) (by positivity)
  refine ⟨n, fun j => (rowCLM W j).comp (e : P →L[ℝ] E m), a, b, ?_⟩
  have h := crClose_comp_clm (e : P →L[ℝ] E m) (hV.comp e.symm.contDiff)
    (contDiff_shallowNet (hτ.1) W a b) (K := K) (by simpa using hN)
  rw [div_mul_cancel₀ _ hC.ne'] at h
  convert h using 1
  · funext p; simp
  · funext p; simp [shallowNet, rowCLM_apply]

end SympNet
