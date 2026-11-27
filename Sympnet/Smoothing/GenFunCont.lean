/-
  C5: continuity of s ↦ genMap s in C^k on compacta, and smoothing by mollification.

  * `inv_stable`: inverses of maps id + g (‖Dg‖ ≤ 1/2) depend continuously on g in C^k,
    via D(u) = J(Dg ∘ u), J(T) = (1 + T)⁻¹ (made globally smooth with a bump).
  * `genMap_stable`: s' close to s in C^{k+1} ⇒ genMap s' close to genMap s in C^k.
  * `exists_smooth_genMap_close`: mollifying s gives a smooth generating function whose map is
    C^k-close to genMap s on a given compact set.
-/
import Sympnet.Smoothing.GenFun
import Sympnet.Smoothing.CompStable
import Sympnet.Smoothing.Mollify

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Convolution NNReal

noncomputable section

namespace SympNet

variable {d : ℕ}

/-! ### Norm bounds for the gradient maps -/

theorem norm_gradCLM_apply_le (L : E d →L[ℝ] ℝ) : ‖gradCLM d L‖ ≤ ‖L‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg L)).2 fun i => ?_
  rw [gradCLM_apply]
  calc ‖L (Pi.single i 1)‖ ≤ ‖L‖ * ‖(Pi.single i 1 : E d)‖ := L.le_opNorm _
    _ ≤ ‖L‖ * 1 := by gcongr; rw [Pi.norm_single]; simp
    _ = ‖L‖ := mul_one _

theorem norm_comp_inl_le (L : X d →L[ℝ] ℝ) :
    ‖L.comp (ContinuousLinearMap.inl ℝ (E d) (E d))‖ ≤ ‖L‖ :=
  (L.opNorm_comp_le _).trans (by
    calc ‖L‖ * ‖ContinuousLinearMap.inl ℝ (E d) (E d)‖ ≤ ‖L‖ * 1 := by
          gcongr; exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
      _ = ‖L‖ := mul_one _)

theorem norm_comp_inr_le (L : X d →L[ℝ] ℝ) :
    ‖L.comp (ContinuousLinearMap.inr ℝ (E d) (E d))‖ ≤ ‖L‖ :=
  (L.opNorm_comp_le _).trans (by
    calc ‖L‖ * ‖ContinuousLinearMap.inr ℝ (E d) (E d)‖ ≤ ‖L‖ * 1 := by
          gcongr; exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
      _ = ‖L‖ := mul_one _)

theorem norm_clmP_le : ‖clmP d‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => by
    rw [one_mul]; exact (norm_gradCLM_apply_le _).trans (norm_comp_inl_le L)

theorem norm_clmQ_le : ‖clmQ d‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => by
    rw [one_mul]; exact (norm_gradCLM_apply_le _).trans (norm_comp_inr_le L)

theorem norm_inl_le : ‖ContinuousLinearMap.inl ℝ (E d) (E d)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp

theorem norm_inr_le : ‖ContinuousLinearMap.inr ℝ (E d) (E d)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp

theorem norm_comp_le_one {V W W' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']
    {A : W →L[ℝ] W'} {B : V →L[ℝ] W} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A.comp B‖ ≤ 1 :=
  (A.opNorm_comp_le B).trans (by nlinarith [norm_nonneg A, norm_nonneg B])

/-- GFHyp from a Hessian bound. -/
theorem GFHyp.of_hess {s : X d → ℝ} (hs : ContDiff ℝ 2 s) (hh : ∀ z, ‖hess s z‖ ≤ 1 / 2) :
    GFHyp s := by
  have hm : ((1 : ℕ∞ω)) + 1 ≤ 2 := by norm_num
  refine ⟨hs, ?_, ?_⟩
  · refine lipschitzWith_of_nnNorm_fderiv_le
      ((contDiff_gradP hs hm).differentiable one_ne_zero) fun z => ?_
    have hd : HasFDerivAt (gradP s) ((clmP d).comp (hess s z)) z :=
      (clmP d).hasFDerivAt.comp z (hasFDerivAt_fderiv hs z)
    rw [hd.fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
    calc ‖(clmP d).comp (hess s z)‖ ≤ ‖clmP d‖ * ‖hess s z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (1 / 2) := by gcongr; exacts [norm_clmP_le, hh z]
      _ = ((1 / 2 : ℝ≥0) : ℝ) := by norm_num
  · refine lipschitzWith_of_nnNorm_fderiv_le
      ((contDiff_gradQ hs hm).differentiable one_ne_zero) fun z => ?_
    have hd : HasFDerivAt (gradQ s) ((clmQ d).comp (hess s z)) z :=
      (clmQ d).hasFDerivAt.comp z (hasFDerivAt_fderiv hs z)
    rw [hd.fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
    calc ‖(clmQ d).comp (hess s z)‖ ≤ ‖clmQ d‖ * ‖hess s z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (1 / 2) := by gcongr; exacts [norm_clmQ_le, hh z]
      _ = ((1 / 2 : ℝ≥0) : ℝ) := by norm_num

/-! ### Closeness under linear post-composition and adding the identity -/

section Closeness
variable {V W W' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']

theorem CrCloseLe.clm_comp {j : ℕ} {K : Set V} {f f' : V → W} {ε : ℝ} (A : W →L[ℝ] W')
    (hA : ‖A‖ ≤ 1) (hf : ContDiff ℝ j f) (hf' : ContDiff ℝ j f') (h : CrCloseLe j K f f' ε) :
    CrCloseLe j K (A ∘ f) (A ∘ f') ε := by
  intro i hi x hx
  have hi' : (i : ℕ∞ω) ≤ j := by exact_mod_cast hi
  have hsub : ∀ a b : ContinuousMultilinearMap ℝ (fun _ : Fin i => V) W,
      A.compContinuousMultilinearMap a - A.compContinuousMultilinearMap b =
        A.compContinuousMultilinearMap (a - b) := fun a b => by ext m; simp
  rw [A.iteratedFDeriv_comp_left hf.contDiffAt hi', A.iteratedFDeriv_comp_left hf'.contDiffAt hi',
    hsub]
  calc _ ≤ ‖A‖ * ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f' x‖ :=
        A.norm_compContinuousMultilinearMap_le _
    _ ≤ 1 * ε := by gcongr; exact h i hi x hx
    _ = ε := one_mul _

theorem CrCloseLe.id_add {j : ℕ} {K : Set V} {F F' : V → V} {ε : ℝ} (hF : ContDiff ℝ j F)
    (hF' : ContDiff ℝ j F') (h : CrCloseLe j K F F' ε) :
    CrCloseLe j K (fun z => z + F z) (fun z => z + F' z) ε := by
  intro i hi x hx
  have hi' : (i : ℕ∞ω) ≤ j := by exact_mod_cast hi
  have e1 : (fun z => z + F z) = id + F := rfl
  have e2 : (fun z => z + F' z) = id + F' := rfl
  rw [e1, e2, iteratedFDeriv_add_apply (contDiff_id.contDiffAt.of_le le_top)
      ((hF.contDiffAt).of_le hi'),
    iteratedFDeriv_add_apply (contDiff_id.contDiffAt.of_le le_top) ((hF'.contDiffAt).of_le hi'),
    add_sub_add_left_eq_sub]
  exact h i hi x hx

theorem CrCloseLe.symm' {j : ℕ} {K : Set V} {f g : V → W} {ε : ℝ} (h : CrCloseLe j K f g ε) :
    CrCloseLe j K g f ε := fun i hi x hx => by rw [norm_sub_rev]; exact h i hi x hx

end Closeness

/-! ### A globally smooth version of T ↦ (1 + T)⁻¹ -/

/-- Bump on operators: 1 on ‖T‖ ≤ 1/2, supported in ‖T‖ < 3/4. -/
def bumpJ (d : ℕ) : ContDiffBump (0 : X d →L[ℝ] X d) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

/-- J(T) = (1 + T)⁻¹ for ‖T‖ ≤ 1/2, smooth everywhere. -/
def invJ (T : X d →L[ℝ] X d) : X d →L[ℝ] X d := bumpJ d T • Ring.inverse (1 + T)

theorem invJ_eq {T : X d →L[ℝ] X d} (hT : ‖T‖ ≤ 1 / 2) : invJ T = Ring.inverse (1 + T) := by
  rw [invJ, (bumpJ d).one_of_mem_closedBall (by simpa [bumpJ, mem_closedBall_zero_iff] using hT),
    one_smul]

theorem one_add_eq_unit {T : X d →L[ℝ] X d} (hT : ‖T‖ < 1) :
    (1 + T : X d →L[ℝ] X d) = ((Units.oneSub (-T) (by rwa [norm_neg]) : (X d →L[ℝ] X d)ˣ) :
      X d →L[ℝ] X d) := by
  rw [Units.val_oneSub, sub_neg_eq_add]

theorem contDiff_invJ : ContDiff ℝ ∞ (invJ (d := d)) := by
  rw [contDiff_iff_contDiffAt]
  intro T
  by_cases hT : ‖T‖ < 1
  · have hinv : ContDiffAt ℝ ∞ (fun S : X d →L[ℝ] X d => Ring.inverse (1 + S)) T := by
      have h1 := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) (Units.oneSub (-T) (by rwa [norm_neg]))
      rw [← one_add_eq_unit hT] at h1
      exact h1.comp T (contDiffAt_const.add contDiffAt_id)
    exact ((bumpJ d).contDiff.contDiffAt).smul hinv
  · have hev : invJ =ᶠ[𝓝 T] fun _ => 0 := by
      have hopen : IsOpen {S : X d →L[ℝ] X d | 3 / 4 < ‖S‖} := isOpen_lt continuous_const
        continuous_norm
      filter_upwards [hopen.mem_nhds (show 3 / 4 < ‖T‖ by push Not at hT; linarith)] with S hS
      have : bumpJ d S = 0 := by
        rw [← Function.notMem_support, (bumpJ d).support_eq, mem_ball_zero_iff]
        simp only [bumpJ]; exact not_lt.2 hS.le
      simp [invJ, this]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- Derivative of an inverse of id + g. -/
theorem fderiv_inv_eq {g u : X d → X d} (hu : Differentiable ℝ u) (hg : Differentiable ℝ g)
    (hgu : ∀ z, u z + g (u z) = z) (hDg : ∀ w, ‖fderiv ℝ g w‖ ≤ 1 / 2) (z : X d) :
    fderiv ℝ u z = invJ (fderiv ℝ g (u z)) := by
  have h : HasFDerivAt (fun z => u z + g (u z))
      (fderiv ℝ u z + (fderiv ℝ g (u z)).comp (fderiv ℝ u z)) z :=
    (hu z).hasFDerivAt.add ((hg (u z)).hasFDerivAt.comp z (hu z).hasFDerivAt)
  have e : (fun z => u z + g (u z)) = id := funext hgu
  rw [e] at h
  have hprod := h.unique (hasFDerivAt_id z)
  have hT : ‖fderiv ℝ g (u z)‖ < 1 := (hDg _).trans_lt (by norm_num)
  set U := Units.oneSub (-fderiv ℝ g (u z)) (by rwa [norm_neg])
  have hU : (U : X d →L[ℝ] X d) * fderiv ℝ u z = 1 := by
    rw [← one_add_eq_unit hT, add_mul, one_mul]
    exact hprod
  rw [invJ_eq (hDg _), one_add_eq_unit hT, Ring.inverse_unit]
  calc fderiv ℝ u z = ((U⁻¹ : (X d →L[ℝ] X d)ˣ) : X d →L[ℝ] X d) * (U * fderiv ℝ u z) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [hU, mul_one]

/-! ### Stability of inverses -/

theorem inv_stable (k : ℕ) (hk : 1 ≤ k) {g u : X d → X d} (hg : ContDiff ℝ k g)
    (hu : ContDiff ℝ k u) (hgu : ∀ z, u z + g (u z) = z) (hDg : ∀ w, ‖fderiv ℝ g w‖ ≤ 1 / 2)
    (B : ℝ) {L : Set (X d)} (hL : IsCompact L) :
    ∃ L' : Set (X d), IsCompact L' ∧ ∀ ε > 0, ∃ δ > 0, ∀ g' u' : X d → X d,
      ContDiff ℝ k g' → ContDiff ℝ k u' → (∀ z, u' z + g' (u' z) = z) →
      (∀ w, ‖fderiv ℝ g' w‖ ≤ 1 / 2) → (∀ w, ‖g' w‖ ≤ B) →
      CrCloseLe k L' g g' δ → CrCloseLe k L u u' ε := by
  set L' := cthickening B L ∪ cthickening 1 (u '' L)
  have hL' : IsCompact L' := hL.cthickening.union (hL.image hu.continuous).cthickening
  refine ⟨L', hL', ?_⟩
  have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hglip : LipschitzWith (1 / 2) g := lipschitzWith_of_nnNorm_fderiv_le
    (hg.differentiable hk0) fun w => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]; exact (hDg w).trans (by norm_num)
  -- zeroth order
  have P0 : ∀ ε > 0, ∃ δ > 0, ∀ g' u' : X d → X d,
      ContDiff ℝ k g' → ContDiff ℝ k u' → (∀ z, u' z + g' (u' z) = z) →
      (∀ w, ‖fderiv ℝ g' w‖ ≤ 1 / 2) → (∀ w, ‖g' w‖ ≤ B) →
      CrCloseLe k L' g g' δ → ∀ z ∈ L, ‖u z - u' z‖ ≤ ε := by
    intro ε hε
    refine ⟨ε / 2, half_pos hε, fun g' u' hg' hu' hgu' _ hB hc z hz => ?_⟩
    have hz' : u' z ∈ L' := by
      refine Or.inl (mem_cthickening_of_dist_le (u' z) z B L hz ?_)
      have e0 : u' z - z = -g' (u' z) := by
        calc u' z - z = u' z - (u' z + g' (u' z)) := by rw [hgu' z]
          _ = -g' (u' z) := by abel
      rw [dist_eq_norm, e0, norm_neg]
      exact hB _
    have h1 : ‖g (u' z) - g' (u' z)‖ ≤ ε / 2 := hc.norm_sub_le hg hg' hz'
    have h2 : ‖g (u' z) - g (u z)‖ ≤ 1 / 2 * ‖u' z - u z‖ := by
      have := hglip.dist_le_mul (u' z) (u z)
      simpa [dist_eq_norm] using this
    have e : u z - u' z = (g' (u' z) - g (u' z)) + (g (u' z) - g (u z)) := by
      calc u z - u' z = (u z + g (u z)) - (u' z + g' (u' z)) + (g' (u' z) - g (u z)) := by abel
        _ = z - z + (g' (u' z) - g (u z)) := by rw [hgu z, hgu' z]
        _ = _ := by abel
    have : ‖u z - u' z‖ ≤ ε / 2 + 1 / 2 * ‖u z - u' z‖ := by
      calc ‖u z - u' z‖ ≤ ‖g' (u' z) - g (u' z)‖ + ‖g (u' z) - g (u z)‖ := by
            rw [e]; exact norm_add_le _ _
        _ ≤ ε / 2 + 1 / 2 * ‖u z - u' z‖ := by
            rw [norm_sub_rev (g' (u' z)), norm_sub_rev (u z)]; linarith
    linarith
  -- induction on the order
  suffices H : ∀ j ≤ k, ∀ ε > 0, ∃ δ > 0, ∀ g' u' : X d → X d,
      ContDiff ℝ k g' → ContDiff ℝ k u' → (∀ z, u' z + g' (u' z) = z) →
      (∀ w, ‖fderiv ℝ g' w‖ ≤ 1 / 2) → (∀ w, ‖g' w‖ ≤ B) →
      CrCloseLe k L' g g' δ → CrCloseLe j L u u' ε from H k le_rfl
  intro j
  induction j with
  | zero =>
    intro _ ε hε
    obtain ⟨δ, hδ, h⟩ := P0 ε hε
    refine ⟨δ, hδ, fun g' u' hg' hu' hgu' hDg' hB hc i hi z hz => ?_⟩
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [norm_iteratedFDeriv_zero_sub (r := k) hu hu']
    exact h g' u' hg' hu' hgu' hDg' hB hc z hz
  | succ j ih =>
    intro hj ε hε
    have hjk : (j : ℕ∞ω) ≤ k := by exact_mod_cast (by omega : j ≤ k)
    have hj1k : (j : ℕ∞ω) + 1 ≤ k := by exact_mod_cast (by omega : j + 1 ≤ k)
    have hdg : ContDiff ℝ j (fderiv ℝ g) := hg.fderiv_right hj1k
    have hG1 : ContDiff ℝ j (fun z => fderiv ℝ g (u z)) := hdg.comp (hu.of_le hjk)
    obtain ⟨δb, hδb, hb⟩ := comp_two_stable' j (fun z => fderiv ℝ g (u z)) invJ hG1
      (contDiff_invJ.of_le (by exact_mod_cast le_top)) L hL ε hε
    obtain ⟨δa, hδa, ha⟩ := comp_two_stable' j u (fderiv ℝ g) (hu.of_le hjk) hdg L hL δb hδb
    obtain ⟨δi, hδi, hi⟩ := ih (by omega) δa hδa
    obtain ⟨δ0, hδ0, h0⟩ := P0 ε hε
    refine ⟨min (min δi δa) δ0, lt_min (lt_min hδi hδa) hδ0,
      fun g' u' hg' hu' hgu' hDg' hB hc => ?_⟩
    have hδ_i : min (min δi δa) δ0 ≤ δi := (min_le_left _ _).trans (min_le_left _ _)
    have hδ_a : min (min δi δa) δ0 ≤ δa := (min_le_left _ _).trans (min_le_right _ _)
    have hδ_0 : min (min δi δa) δ0 ≤ δ0 := min_le_right _ _
    have hU := hi g' u' hg' hu' hgu' hDg' hB (fun i hi' x hx => (hc i hi' x hx).trans hδ_i)
    have hdg' : ContDiff ℝ j (fderiv ℝ g') := hg'.fderiv_right hj1k
    have hD : CrCloseLe j (cthickening 1 (u '' L)) (fderiv ℝ g) (fderiv ℝ g') δa := by
      have h1 : CrCloseLe (j + 1) L' g g' (min (min δi δa) δ0) := hc.of_le (by omega)
      have h2 := h1.fderiv' (hg.of_le (by exact_mod_cast (by omega : j + 1 ≤ k)))
        (hg'.of_le (by exact_mod_cast (by omega : j + 1 ≤ k)))
      exact fun i hi' x hx => (h2 i hi' x (Or.inr hx)).trans hδ_a
    have hA := ha (cthickening 1 (u '' L)) le_rfl u' (fderiv ℝ g') (hu'.of_le hjk) hdg' hU hD
    have hG1' : ContDiff ℝ j (fun z => fderiv ℝ g' (u' z)) := hdg'.comp (hu'.of_le hjk)
    have hB' := hb univ (subset_univ _) (fun z => fderiv ℝ g' (u' z)) invJ hG1'
      (contDiff_invJ.of_le (by exact_mod_cast le_top)) hA (fun i _ x _ => by simp; exact hδb.le)
    have ef : (fun y => fderiv ℝ u y) = invJ ∘ fun z => fderiv ℝ g (u z) :=
      funext fun z => fderiv_inv_eq (hu.differentiable hk0) (hg.differentiable hk0) hgu hDg z
    have ef' : (fun y => fderiv ℝ u' y) = invJ ∘ fun z => fderiv ℝ g' (u' z) :=
      funext fun z => fderiv_inv_eq (hu'.differentiable hk0) (hg'.differentiable hk0) hgu' hDg' z
    refine CrCloseLe.of_fderiv (hu.of_le (by exact_mod_cast hj)) (hu'.of_le (by exact_mod_cast hj))
      (fun z hz => h0 g' u' hg' hu' hgu' hDg' hB (fun i hi' x hx => (hc i hi' x hx).trans hδ_0) z hz)
      ?_
    rw [ef, ef']
    exact hB'

/-! ### Stability and smoothing of generating-function maps -/

/-- The perturbation g_s = (∇_q s, 0), so that Ψ₁ = id + g_s. -/
def gfun (s : X d → ℝ) (w : X d) : X d := (gradQ s w, 0)

/-- g_s = A ∘ Ds. -/
def gfunCLM (d : ℕ) : (X d →L[ℝ] ℝ) →L[ℝ] X d :=
  (ContinuousLinearMap.inl ℝ (E d) (E d)).comp (clmQ d)

/-- Ψ₂ = id + B ∘ Ds. -/
def psi2CLM (d : ℕ) : (X d →L[ℝ] ℝ) →L[ℝ] X d :=
  (ContinuousLinearMap.inr ℝ (E d) (E d)).comp (clmP d)

theorem gfun_eq (s : X d → ℝ) : gfun s = gfunCLM d ∘ fderiv ℝ s := rfl

theorem psi2_eq (s : X d → ℝ) : psi2 s = fun w => w + (psi2CLM d ∘ fderiv ℝ s) w := rfl

theorem norm_gfunCLM_le : ‖gfunCLM d‖ ≤ 1 := norm_comp_le_one norm_inl_le norm_clmQ_le

theorem norm_psi2CLM_le : ‖psi2CLM d‖ ≤ 1 := norm_comp_le_one norm_inr_le norm_clmP_le

theorem norm_fderiv_gfun_le {s : X d → ℝ} (h : GFHyp s) (w : X d) :
    ‖fderiv ℝ (gfun s) w‖ ≤ 1 / 2 := by
  have hd : HasFDerivAt (gfun s) ((gfunCLM d).comp (hess s w)) w :=
    (gfunCLM d).hasFDerivAt.comp w (hasFDerivAt_fderiv h.contDiff w)
  rw [hd.fderiv]
  exact norm_comp_hess_le h w

theorem psi1_symm_spec {s : X d → ℝ} (h : GFHyp s) (z : X d) :
    (psi1Homeo h).symm z + gfun s ((psi1Homeo h).symm z) = z :=
  (psi1Homeo h).apply_symm_apply z

theorem norm_gfun_le {s : X d → ℝ} {B : ℝ} (hB : ∀ w, ‖fderiv ℝ s w‖ ≤ B) (w : X d) :
    ‖gfun s w‖ ≤ B := by
  rw [gfun_eq, Function.comp_apply]
  calc ‖gfunCLM d (fderiv ℝ s w)‖ ≤ ‖gfunCLM d‖ * ‖fderiv ℝ s w‖ := (gfunCLM d).le_opNorm _
    _ ≤ 1 * B := mul_le_mul norm_gfunCLM_le (hB w) (norm_nonneg _) zero_le_one
    _ = B := one_mul _

/-- **Continuity of s ↦ genMap s.** -/
theorem genMap_stable (k : ℕ) (hk : 1 ≤ k) {s : X d → ℝ} (h : GFHyp s)
    (hs : ContDiff ℝ (k + 1 : ℕ) s) (B : ℝ) {L : Set (X d)} (hL : IsCompact L) :
    ∃ L' : Set (X d), IsCompact L' ∧ ∀ ε > 0, ∃ δ > 0, ∀ (s' : X d → ℝ) (h' : GFHyp s'),
      ContDiff ℝ (k + 1 : ℕ) s' → (∀ w, ‖fderiv ℝ s' w‖ ≤ B) →
      CrCloseLe (k + 1) L' s s' δ → CrCloseLe k L (genMap h) (genMap h') ε := by
  have hkk : ((k : ℕ) : ℕ∞ω) + 1 ≤ ((k + 1 : ℕ) : ℕ∞ω) := by push_cast; exact le_rfl
  set u := (psi1Homeo h).symm
  have hu : ContDiff ℝ k u := contDiff_psi1Homeo_symm h hs hkk
  have hds : ContDiff ℝ k (fderiv ℝ s) := hs.fderiv_right hkk
  have hg : ContDiff ℝ k (gfun s) := (gfunCLM d).contDiff.comp hds
  have hp2 : ContDiff ℝ k (psi2 s) := contDiff_psi2 hs hkk
  set S := enlarge u L
  have hS : IsCompact S := isCompact_enlarge hu.continuous hL
  obtain ⟨L'', hL'', hinv⟩ := inv_stable k hk hg hu (psi1_symm_spec h) (norm_fderiv_gfun_le h)
    B hS
  refine ⟨L'' ∪ S, hL''.union hS, fun ε hε => ?_⟩
  obtain ⟨δ₁, hδ₁, h₁⟩ := comp_two_stable k u (psi2 s) hu hp2 L hL ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hinv δ₁ hδ₁
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s' h' hs' hB' hc => ?_⟩
  have hds' : ContDiff ℝ k (fderiv ℝ s') := hs'.fderiv_right hkk
  have hD : CrCloseLe k (L'' ∪ S) (fderiv ℝ s) (fderiv ℝ s') (min δ₁ δ₂) := hc.fderiv' hs hs'
  have hgg := hD.clm_comp (gfunCLM d) norm_gfunCLM_le hds hds'
  have hpp := (hD.clm_comp (psi2CLM d) norm_psi2CLM_le hds hds').id_add
    ((psi2CLM d).contDiff.comp hds) ((psi2CLM d).contDiff.comp hds')
  set u' := (psi1Homeo h').symm
  have hu' : ContDiff ℝ k u' := contDiff_psi1Homeo_symm h' hs' hkk
  have hU : CrCloseLe k S u u' δ₁ := h₂ (gfun s') u' ((gfunCLM d).contDiff.comp hds') hu'
    (psi1_symm_spec h') (norm_fderiv_gfun_le h') (norm_gfun_le hB')
    (fun i hi x hx => (hgg i hi x (Or.inl hx)).trans (min_le_right _ _))
  have hP : CrCloseLe k S (psi2 s) (psi2 s') δ₁ := by
    rw [psi2_eq, psi2_eq]
    exact fun i hi x hx => (hpp i hi x (Or.inr hx)).trans (min_le_left _ _)
  exact h₁ S le_rfl u' (psi2 s') hu' (contDiff_psi2 hs' hkk) hU hP

local notation "μH" => (Measure.addHaar : Measure (X d))

set_option maxSynthPendingDepth 6 in
/-- **Smoothing a generating-function map.** -/
theorem exists_smooth_genMap_close (k : ℕ) (hk : 1 ≤ k) {s : X d → ℝ} (h : GFHyp s)
    (hs : ContDiff ℝ (k + 1 : ℕ) s) (hsc : HasCompactSupport s)
    (hhess : ∀ z, ‖hess s z‖ ≤ 1 / 2) {L : Set (X d)} (hL : IsCompact L) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s' : X d → ℝ) (h' : GFHyp s'), ContDiff ℝ ∞ s' ∧
      CrCloseLe k L (genMap h) (genMap h') ε := by
  have : CompleteSpace (X d →L[ℝ] ℝ) := ContinuousLinearMap.instCompleteSpace
  have hk1 : (1 : ℕ∞ω) ≤ ((k + 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (by omega : 1 ≤ k + 1)
  have hk2 : (2 : ℕ∞ω) ≤ ((k + 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (by omega : 2 ≤ k + 1)
  have hs1 : ContDiff ℝ 1 s := hs.of_le hk1
  have hds1 : ContDiff ℝ 1 (fderiv ℝ s) := (hs.of_le hk2).fderiv_right (by norm_num)
  obtain ⟨B, hB⟩ := (hs1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hsc.fderiv ℝ)
  obtain ⟨L', hL', hst⟩ := genMap_stable k hk h hs B hL
  obtain ⟨δ, hδ, hδ'⟩ := hst ε hε
  obtain ⟨δφ, hδφ, hmoll⟩ := moll_close (k + 1) s hs hsc δ hδ
  let φ : ContDiffBump (0 : X d) := ⟨δφ / 2, δφ, half_pos hδφ, half_lt_self hδφ⟩
  set s' := φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] s
  have hs'sm : ContDiff ℝ ∞ s' :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hs.continuous.locallyIntegrable
  have hD1 : fderiv ℝ s' = φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] fderiv ℝ s :=
    fderiv_moll φ hsc hs1
  have hD2 : fderiv ℝ (fderiv ℝ s') =
      φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] fderiv ℝ (fderiv ℝ s) := by
    rw [hD1]; exact fderiv_moll φ (hsc.fderiv ℝ) hds1
  have hh' : ∀ z, ‖hess s' z‖ ≤ 1 / 2 := fun z => by
    show ‖fderiv ℝ (fderiv ℝ s') z‖ ≤ 1 / 2
    rw [hD2]
    exact norm_moll_le φ (hds1.continuous_fderiv one_ne_zero).aestronglyMeasurable hhess z
  have hG' : GFHyp s' := GFHyp.of_hess (by simpa using contDiff_infty.1 hs'sm 2) hh'
  have hB' : ∀ w, ‖fderiv ℝ s' w‖ ≤ B := fun w => by
    rw [hD1]; exact norm_moll_le φ (hs1.continuous_fderiv one_ne_zero).aestronglyMeasurable hB w
  refine ⟨s', hG', hs'sm, hδ' s' hG' (contDiff_infty.1 hs'sm (k + 1)) hB' ?_⟩
  exact fun i hi x _ => ((hmoll φ le_rfl).symm' i hi x (mem_univ x))

end SympNet
