/-
  C4: global symplectic diffeomorphisms from generating functions.

  For s : X → ℝ with partial gradients ∇_P s, ∇_q s that are (1/2)-Lipschitz, put
    Ψ₁(P, q) = (P + ∇_q s(P,q), q),   Ψ₂(P, q) = (P, q + ∇_P s(P,q)).
  Both are homeomorphisms (perturbations of the identity), and
    genMap s = Ψ₂ ∘ Ψ₁⁻¹ : (p, q) ↦ (P, Q),   p = P + ∂_q s,  Q = q + ∂_P s
  is a C^m symplectic bijection when s is C^{m+1}.
-/
import Sympnet.SympNetUniversal

open Set Filter Topology
open scoped ContDiff NNReal

noncomputable section

namespace SympNet

variable {d : ℕ}

/-- `L ↦ ∇_P` part of a covector on `X d`. -/
def clmP (d : ℕ) : (X d →L[ℝ] ℝ) →L[ℝ] E d :=
  (gradCLM d).comp
    ((ContinuousLinearMap.compL ℝ (E d) (X d) ℝ).flip (ContinuousLinearMap.inl ℝ (E d) (E d)))

/-- `L ↦ ∇_q` part of a covector on `X d`. -/
def clmQ (d : ℕ) : (X d →L[ℝ] ℝ) →L[ℝ] E d :=
  (gradCLM d).comp
    ((ContinuousLinearMap.compL ℝ (E d) (X d) ℝ).flip (ContinuousLinearMap.inr ℝ (E d) (E d)))

theorem sum_clmP_mul (L : X d →L[ℝ] ℝ) (t : E d) : ∑ i, clmP d L i * t i = L (t, 0) :=
  sum_gradCLM_mul _ t

theorem sum_clmQ_mul (L : X d →L[ℝ] ℝ) (t : E d) : ∑ i, clmQ d L i * t i = L (0, t) :=
  sum_gradCLM_mul _ t

theorem sum_mul_clmP (L : X d →L[ℝ] ℝ) (t : E d) : ∑ i, t i * clmP d L i = L (t, 0) := by
  rw [← sum_clmP_mul]; simp [mul_comm]

theorem sum_mul_clmQ (L : X d →L[ℝ] ℝ) (t : E d) : ∑ i, t i * clmQ d L i = L (0, t) := by
  rw [← sum_clmQ_mul]; simp [mul_comm]

/-- ∇_P s. -/
def gradP (s : X d → ℝ) (z : X d) : E d := clmP d (fderiv ℝ s z)

/-- ∇_q s. -/
def gradQ (s : X d → ℝ) (z : X d) : E d := clmQ d (fderiv ℝ s z)

/-- Ψ₁(P, q) = (P + ∇_q s, q). -/
def psi1 (s : X d → ℝ) (z : X d) : X d := z + (gradQ s z, 0)

/-- Ψ₂(P, q) = (P, q + ∇_P s). -/
def psi2 (s : X d → ℝ) (z : X d) : X d := z + (0, gradP s z)

/-! ### Regularity -/

theorem contDiff_gradP {s : X d → ℝ} {m n : ℕ∞ω} (hs : ContDiff ℝ n s) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (gradP s) :=
  (clmP d).contDiff.comp (hs.fderiv_right hmn)

theorem contDiff_gradQ {s : X d → ℝ} {m n : ℕ∞ω} (hs : ContDiff ℝ n s) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (gradQ s) :=
  (clmQ d).contDiff.comp (hs.fderiv_right hmn)

theorem contDiff_psi1 {s : X d → ℝ} {m n : ℕ∞ω} (hs : ContDiff ℝ n s) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (psi1 s) :=
  contDiff_id.add ((contDiff_gradQ hs hmn).prodMk contDiff_const)

theorem contDiff_psi2 {s : X d → ℝ} {m n : ℕ∞ω} (hs : ContDiff ℝ n s) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (psi2 s) :=
  contDiff_id.add (contDiff_const.prodMk (contDiff_gradP hs hmn))

/-- The Hessian of a C² function. -/
abbrev hess (s : X d → ℝ) (w : X d) : X d →L[ℝ] X d →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ s) w

theorem hasFDerivAt_fderiv {s : X d → ℝ} (hs : ContDiff ℝ 2 s) (w : X d) :
    HasFDerivAt (fderiv ℝ s) (hess s w) w :=
  (((hs.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero) w).hasFDerivAt

theorem hess_symm {s : X d → ℝ} (hs : ContDiff ℝ 2 s) (w u v : X d) :
    hess s w u v = hess s w v u :=
  second_derivative_symmetric (fun y => (hs.differentiable (by norm_num) y).hasFDerivAt)
    (hasFDerivAt_fderiv hs w) u v

/-- Derivative of Ψ₁. -/
def dpsi1 (H : X d →L[ℝ] X d →L[ℝ] ℝ) : X d →L[ℝ] X d :=
  ContinuousLinearMap.id ℝ (X d) +
    (ContinuousLinearMap.inl ℝ (E d) (E d)).comp ((clmQ d).comp H)

/-- Derivative of Ψ₂. -/
def dpsi2 (H : X d →L[ℝ] X d →L[ℝ] ℝ) : X d →L[ℝ] X d :=
  ContinuousLinearMap.id ℝ (X d) +
    (ContinuousLinearMap.inr ℝ (E d) (E d)).comp ((clmP d).comp H)

theorem hasFDerivAt_psi1 {s : X d → ℝ} (hs : ContDiff ℝ 2 s) (w : X d) :
    HasFDerivAt (psi1 s) (dpsi1 (hess s w)) w := by
  have hQ : HasFDerivAt (gradQ s) ((clmQ d).comp (hess s w)) w :=
    (clmQ d).hasFDerivAt.comp w (hasFDerivAt_fderiv hs w)
  exact (hasFDerivAt_id w).add ((ContinuousLinearMap.inl ℝ (E d) (E d)).hasFDerivAt.comp w hQ)

theorem hasFDerivAt_psi2 {s : X d → ℝ} (hs : ContDiff ℝ 2 s) (w : X d) :
    HasFDerivAt (psi2 s) (dpsi2 (hess s w)) w := by
  have hP : HasFDerivAt (gradP s) ((clmP d).comp (hess s w)) w :=
    (clmP d).hasFDerivAt.comp w (hasFDerivAt_fderiv hs w)
  exact (hasFDerivAt_id w).add ((ContinuousLinearMap.inr ℝ (E d) (E d)).hasFDerivAt.comp w hP)

/-! ### Symplecticity: ω(DΨ₂ a, DΨ₂ b) = ω(DΨ₁ a, DΨ₁ b) -/

theorem symplecticForm_dpsi (H : X d →L[ℝ] X d →L[ℝ] ℝ) (hH : ∀ u v, H u v = H v u)
    (a b : X d) :
    symplecticForm (dpsi2 H a) (dpsi2 H b) = symplecticForm (dpsi1 H a) (dpsi1 H b) := by
  have key : ∀ x y : X d, symplecticForm (dpsi1 H x) (dpsi1 H y) =
      symplecticForm x y + H x (0, y.2) - H y (0, x.2) := by
    intro x y
    simp only [symplecticForm, dpsi1, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, Prod.snd_zero, Pi.zero_apply, add_zero]
    rw [← sum_clmQ_mul (H x) y.2, ← sum_mul_clmQ (H y) x.2]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have key2 : ∀ x y : X d, symplecticForm (dpsi2 H x) (dpsi2 H y) =
      symplecticForm x y + H y (x.1, 0) - H x (y.1, 0) := by
    intro x y
    simp only [symplecticForm, dpsi2, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, Prod.fst_zero, Pi.zero_apply, add_zero]
    rw [← sum_clmP_mul (H y) x.1, ← sum_mul_clmP (H x) y.1]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [key, key2]
  have ha' : H a = H (a.1, 0) + H (0, a.2) := by
    rw [← map_add]; congr 1; ext <;> simp
  have hb' : H b = H (b.1, 0) + H (0, b.2) := by
    rw [← map_add]; congr 1; ext <;> simp
  have h1 : H a (0, b.2) - H b (0, a.2) = H (a.1, 0) (0, b.2) - H (b.1, 0) (0, a.2) := by
    rw [ha', hb']
    simp only [ContinuousLinearMap.add_apply]
    rw [hH (0, b.2) (0, a.2)]; ring
  have h2 : H b (a.1, 0) - H a (b.1, 0) = H (0, b.2) (a.1, 0) - H (0, a.2) (b.1, 0) := by
    rw [ha', hb']
    simp only [ContinuousLinearMap.add_apply]
    rw [hH (b.1, 0) (a.1, 0)]; ring
  linarith [hH (0, b.2) (a.1, 0), hH (0, a.2) (b.1, 0)]

/-! ### The homeomorphisms Ψ₁, Ψ₂ -/

/-- Hypotheses on a generating function: C² with (1/2)-Lipschitz partial gradients. -/
structure GFHyp (s : X d → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 s
  lipP : LipschitzWith (1 / 2) (gradP s)
  lipQ : LipschitzWith (1 / 2) (gradQ s)

theorem hc_half : Subsingleton (X d) ∨
    ((1 / 2 : ℝ≥0) < ‖((ContinuousLinearEquiv.refl ℝ (X d)).symm : X d →L[ℝ] X d)‖₊⁻¹) := by
  by_cases h : Subsingleton (X d)
  · exact Or.inl h
  · haveI := not_subsingleton_iff_nontrivial.1 h
    right
    simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id, inv_one]
    rw [div_lt_one (by norm_num)]; norm_num

theorem approx_psi1 {s : X d → ℝ} (h : GFHyp s) :
    ApproximatesLinearOn (psi1 s) ((ContinuousLinearEquiv.refl ℝ (X d)) : X d →L[ℝ] X d) univ
      (1 / 2) := by
  intro x _ y _
  have e : psi1 s x - psi1 s y - (ContinuousLinearEquiv.refl ℝ (X d) : X d →L[ℝ] X d) (x - y) =
      (gradQ s x - gradQ s y, 0) := by
    simp only [psi1, ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]
    ext <;> simp; abel
  rw [e, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _), ← dist_eq_norm, ← dist_eq_norm]
  exact h.lipQ.dist_le_mul x y

theorem approx_psi2 {s : X d → ℝ} (h : GFHyp s) :
    ApproximatesLinearOn (psi2 s) ((ContinuousLinearEquiv.refl ℝ (X d)) : X d →L[ℝ] X d) univ
      (1 / 2) := by
  intro x _ y _
  have e : psi2 s x - psi2 s y - (ContinuousLinearEquiv.refl ℝ (X d) : X d →L[ℝ] X d) (x - y) =
      (0, gradP s x - gradP s y) := by
    simp only [psi2, ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]
    ext <;> simp; abel
  rw [e, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), ← dist_eq_norm, ← dist_eq_norm]
  exact h.lipP.dist_le_mul x y

def psi1Homeo {s : X d → ℝ} (h : GFHyp s) : X d ≃ₜ X d :=
  (approx_psi1 h).toHomeomorph (psi1 s) hc_half

def psi2Homeo {s : X d → ℝ} (h : GFHyp s) : X d ≃ₜ X d :=
  (approx_psi2 h).toHomeomorph (psi2 s) hc_half

@[simp] theorem psi1Homeo_apply {s : X d → ℝ} (h : GFHyp s) (z : X d) :
    psi1Homeo h z = psi1 s z := rfl

@[simp] theorem psi2Homeo_apply {s : X d → ℝ} (h : GFHyp s) (z : X d) :
    psi2Homeo h z = psi2 s z := rfl

/-- The map generated by `s`: Φ_s = Ψ₂ ∘ Ψ₁⁻¹. -/
def genMap {s : X d → ℝ} (h : GFHyp s) : X d → X d := psi2 s ∘ (psi1Homeo h).symm

/-- The defining property: Φ_s (Ψ₁ w) = Ψ₂ w. -/
theorem genMap_psi1 {s : X d → ℝ} (h : GFHyp s) (w : X d) : genMap h (psi1 s w) = psi2 s w := by
  simp only [genMap, Function.comp_apply]
  congr 1
  exact (psi1Homeo h).symm_apply_apply w

theorem bijective_genMap {s : X d → ℝ} (h : GFHyp s) : Function.Bijective (genMap h) :=
  (psi2Homeo h).bijective.comp (psi1Homeo h).symm.bijective

/-! ### Derivatives of Ψ₁⁻¹ and Φ_s -/

theorem norm_comp_hess_le {s : X d → ℝ} (h : GFHyp s) (w : X d) :
    ‖(ContinuousLinearMap.inl ℝ (E d) (E d)).comp ((clmQ d).comp (hess s w))‖ ≤ 1 / 2 := by
  have hQ : HasFDerivAt (gradQ s) ((clmQ d).comp (hess s w)) w :=
    (clmQ d).hasFDerivAt.comp w (hasFDerivAt_fderiv h.contDiff w)
  have hb : ‖(clmQ d).comp (hess s w)‖ ≤ 1 / 2 := by
    rw [← hQ.fderiv]
    exact_mod_cast norm_fderiv_le_of_lipschitz ℝ h.lipQ
  calc _ ≤ ‖ContinuousLinearMap.inl ℝ (E d) (E d)‖ * ‖(clmQ d).comp (hess s w)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 / 2) := by
        gcongr
        exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
    _ = 1 / 2 := one_mul _

/-- DΨ₁ as a continuous linear equivalence. -/
def dpsi1Equiv {s : X d → ℝ} (h : GFHyp s) (w : X d) : X d ≃L[ℝ] X d :=
  ContinuousLinearEquiv.unitsEquiv ℝ (X d)
    (Units.oneSub (-((ContinuousLinearMap.inl ℝ (E d) (E d)).comp ((clmQ d).comp (hess s w))))
      (by rw [norm_neg]; exact (norm_comp_hess_le h w).trans_lt (by norm_num)))

theorem dpsi1Equiv_coe {s : X d → ℝ} (h : GFHyp s) (w : X d) :
    (dpsi1Equiv h w : X d →L[ℝ] X d) = dpsi1 (hess s w) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp [dpsi1Equiv, dpsi1, Units.val_oneSub, sub_neg_eq_add, add_comm]

theorem hasFDerivAt_psi1Homeo_symm {s : X d → ℝ} (h : GFHyp s) (z : X d) :
    HasFDerivAt (psi1Homeo h).symm
      ((dpsi1Equiv h ((psi1Homeo h).symm z)).symm : X d →L[ℝ] X d) z := by
  apply HasFDerivAt.of_local_left_inverse (psi1Homeo h).symm.continuous.continuousAt
  · rw [dpsi1Equiv_coe]
    exact hasFDerivAt_psi1 h.contDiff _
  · exact Eventually.of_forall fun y => (psi1Homeo h).apply_symm_apply y

theorem contDiff_psi1Homeo_symm {s : X d → ℝ} (h : GFHyp s) {m n : ℕ∞ω} (hs : ContDiff ℝ n s)
    (hmn : m + 1 ≤ n) : ContDiff ℝ m (psi1Homeo h).symm := by
  refine (psi1Homeo h).contDiff_symm (f₀' := dpsi1Equiv h) (fun a => ?_) (contDiff_psi1 hs hmn)
  rw [dpsi1Equiv_coe]
  exact hasFDerivAt_psi1 h.contDiff a

theorem contDiff_genMap {s : X d → ℝ} (h : GFHyp s) {m n : ℕ∞ω} (hs : ContDiff ℝ n s)
    (hmn : m + 1 ≤ n) : ContDiff ℝ m (genMap h) :=
  (contDiff_psi2 hs hmn).comp (contDiff_psi1Homeo_symm h hs hmn)

theorem isSymplecticAt_genMap {s : X d → ℝ} (h : GFHyp s) (z : X d) :
    IsSymplecticAt (genMap h) z := by
  set w := (psi1Homeo h).symm z
  have hd : HasFDerivAt (genMap h)
      ((dpsi2 (hess s w)).comp ((dpsi1Equiv h w).symm : X d →L[ℝ] X d)) z :=
    (hasFDerivAt_psi2 h.contDiff w).comp z (hasFDerivAt_psi1Homeo_symm h z)
  intro v v'
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    symplecticForm_dpsi _ (hess_symm h.contDiff w), ← dpsi1Equiv_coe h w,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

end SympNet
