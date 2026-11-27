/-
  T-L: every linear symplectic map of ℝ^{2d} is a finite composition of linear gradient shears.

  (1) After an upper shear by t·I the block A becomes A + tC, invertible for some t
      (det(A + tC) is a polynomial in t that does not vanish at t = i).
  (2) A lower shear kills the C block, (3) an upper shear on the right kills the B block,
  (4) (x, q) ↦ (Mx, M⁻ᵀq) is handled by Gaussian elimination: every elementary factor is a
      product S₁S₂ of symmetric invertible matrices, and (Mx, M⁻ᵀq) for M = S₁S₂ is
      R(S₁, S₁⁻¹) ∘ R(−S₂⁻¹, −S₂) with R(S, T)(p, q) = (Sq, −Tp) = up(S) ∘ low(−T) ∘ up(S).
-/
import Sympnet.Turaev.ShearProd

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace SympNet

variable {d : ℕ}

theorem symplecticForm_eq_dot (v w : X d) :
    symplecticForm v w = v.1 ⬝ᵥ w.2 - v.2 ⬝ᵥ w.1 := by
  simp [symplecticForm, dotProduct, Finset.sum_sub_distrib]

/-! ### The polynomial argument -/

theorem exists_det_add_smul_ne_zero (A C : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ x y : Fin d → ℝ, A.mulVec x = C.mulVec y → C.mulVec x = -(A.mulVec y) → x = 0) :
    ∃ t : ℝ, (A + t • C).det ≠ 0 := by
  by_contra hne
  push Not at hne
  set P : Polynomial ℝ := (A.map Polynomial.C + (Polynomial.X : Polynomial ℝ) • C.map Polynomial.C).det
  have hev : ∀ t, P.eval t = (A + t • C).det := by
    intro t
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1; ext i j; simp; ring
  have hP : P = 0 := Polynomial.funext fun t => by rw [hev, hne, Polynomial.eval_zero]
  have hCdet : (A.map (algebraMap ℝ ℂ) + Complex.I • C.map (algebraMap ℝ ℂ)).det = 0 := by
    have := congrArg (Polynomial.aeval Complex.I) hP
    rw [map_zero, AlgHom.map_det] at this
    rw [← this]; congr 1; ext i j; simp; ring
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hCdet
  set x : Fin d → ℝ := fun i => (v i).re
  set y : Fin d → ℝ := fun i => (v i).im
  have hk : ∀ k, A.mulVec x k = C.mulVec y k ∧ C.mulVec x k = -(A.mulVec y k) := by
    intro k
    have hk := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      Pi.zero_apply] at hk
    have h1 := congrArg Complex.re hk
    have h2 := congrArg Complex.im hk
    simp only [Complex.re_sum, Complex.im_sum, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, smul_eq_mul, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im] at h1 h2
    simp only [Matrix.mulVec, dotProduct, x, y]
    constructor
    · have : ∑ i, (A k i * (v i).re - C k i * (v i).im) = 0 := by
        rw [← h1]; refine Finset.sum_congr rfl fun i _ => ?_; simp
      rw [Finset.sum_sub_distrib] at this; linarith
    · have : ∑ i, (A k i * (v i).im + C k i * (v i).re) = 0 := by
        rw [← h2]; refine Finset.sum_congr rfl fun i _ => ?_; simp
      rw [Finset.sum_add_distrib] at this; linarith
  have hx : x = 0 := h x y (funext fun k => (hk k).1) (funext fun k => (hk k).2)
  have hy : y = 0 := by
    refine h y (-x) (funext fun k => ?_) (funext fun k => ?_)
    · simp [Matrix.mulVec_neg, (hk k).2]
    · simp [Matrix.mulVec_neg, (hk k).1]
  apply hv0
  funext i
  exact Complex.ext (congrFun hx i) (congrFun hy i)

/-! ### Matrices: (p, q) ↦ (Mp, M⁻ᵀq) -/

section Matrices

open Matrix

def diagMap (M : Matrix (Fin d) (Fin d) ℝ) (z : X d) : X d :=
  (M.mulVec z.1, (M⁻¹).transpose.mulVec z.2)

theorem symm_mulVec {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.transpose = S) :
    ∀ u v, S.mulVec u ⬝ᵥ v = S.mulVec v ⬝ᵥ u := by
  intro u v
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hS]

theorem upShear_mat_mem {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.transpose = S) :
    upShear (fun q => S.mulVec q) ∈ ShearProd d :=
  upShear_lin_mem (Matrix.mulVecLin S) (symm_mulVec hS)

theorem lowShear_mat_mem {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.transpose = S) :
    lowShear (fun q => S.mulVec q) ∈ ShearProd d :=
  lowShear_lin_mem (Matrix.mulVecLin S) (symm_mulVec hS)

/-- R(S, T)(p, q) = (Sq, −Tp), for S, T symmetric and mutually inverse. -/
theorem rot_mem {S T : Matrix (Fin d) (Fin d) ℝ} (hS : S.transpose = S) (hT : T.transpose = T)
    (hST : S * T = 1) (hTS : T * S = 1) :
    (fun z : X d => (S.mulVec z.2, -(T.mulVec z.1))) ∈ ShearProd d := by
  have hT' : (-T).transpose = -T := by rw [transpose_neg, hT]
  have h := ShearProd.comp (ShearProd.comp (upShear_mat_mem hS) (lowShear_mat_mem hT'))
    (upShear_mat_mem hS)
  convert h using 1
  funext z
  rcases z with ⟨p, q⟩
  simp only [Function.comp_apply, upShear, lowShear, Matrix.neg_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_neg, mulVec_mulVec, hST, hTS, one_mulVec]
  refine Prod.ext ?_ ?_ <;> simp

theorem inv_symm {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.transpose = S) :
    (S⁻¹).transpose = S⁻¹ := by rw [transpose_nonsing_inv, hS]

theorem diagMap_symm_mul {S₁ S₂ : Matrix (Fin d) (Fin d) ℝ} (h₁ : S₁.transpose = S₁)
    (h₂ : S₂.transpose = S₂) (d₁ : S₁.det ≠ 0) (d₂ : S₂.det ≠ 0) :
    diagMap (S₁ * S₂) ∈ ShearProd d := by
  have u₁ : IsUnit S₁.det := isUnit_iff_ne_zero.2 d₁
  have u₂ : IsUnit S₂.det := isUnit_iff_ne_zero.2 d₂
  have hA := rot_mem h₁ (inv_symm h₁) (mul_nonsing_inv _ u₁) (nonsing_inv_mul _ u₁)
  have hB := rot_mem (S := -S₂⁻¹) (T := -S₂) (by rw [transpose_neg, inv_symm h₂])
    (by rw [transpose_neg, h₂]) (by rw [neg_mul_neg, nonsing_inv_mul _ u₂])
    (by rw [neg_mul_neg, mul_nonsing_inv _ u₂])
  have h := ShearProd.comp hB hA
  convert h using 1
  funext z
  rcases z with ⟨p, q⟩
  simp only [diagMap, Function.comp_apply, Matrix.neg_mulVec, neg_neg, Matrix.mulVec_neg,
    mulVec_mulVec, Matrix.mul_inv_rev, transpose_mul, inv_symm h₁, inv_symm h₂]

theorem diagMap_mul {A B : Matrix (Fin d) (Fin d) ℝ} :
    diagMap (A * B) = diagMap A ∘ diagMap B := by
  funext z
  simp only [diagMap, Function.comp_apply, mulVec_mulVec, Matrix.mul_inv_rev, transpose_mul]

theorem diagMap_mem (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.det ≠ 0) :
    diagMap M ∈ ShearProd d := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => diagMap M ∈ ShearProd d) M hM ?_ ?_ ?_
  · intro D hD
    have := diagMap_symm_mul (diagonal_transpose D) transpose_one hD (by simp)
    rwa [Matrix.mul_one] at this
  · intro t
    let σ := Equiv.swap t.i t.j
    let P : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun k l => if σ k = l then 1 else 0
    let S : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun k l =>
      (if σ k = l then 1 else 0) + (if k = t.j ∧ l = t.j then t.c else 0)
    have hss : ∀ k, σ (σ k) = k := fun k => Equiv.swap_apply_self _ _ _
    have hsw : ∀ k, σ k = t.j ↔ k = t.i := fun k => by
      simp only [σ]; rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    have hσ : ∀ k l, σ l = k ↔ σ k = l :=
      fun k l => ⟨fun h => by rw [← h, hss], fun h => by rw [← h, hss]⟩
    have hPM : ∀ (M : Matrix (Fin d) (Fin d) ℝ) k l, (P * M) k l = M (σ k) l := by
      intro M k l
      rw [Matrix.mul_apply]
      simp [P, ite_mul, Finset.sum_ite_eq]
    have hPS : P * S = t.toMatrix := by
      ext k l
      rw [hPM]
      simp only [S, of_apply, hss, hsw, TransvectionStruct.toMatrix, transvection, add_apply,
        one_apply, single_apply]
      congr 1
      exact if_congr ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl
    have hPP : P * P = 1 := by
      ext k l
      rw [hPM]
      simp only [P, of_apply, hss]
      exact (Matrix.one_apply).symm
    have hPt : P.transpose = P := by
      ext k l; simp only [P, transpose_apply, of_apply]
      exact if_congr (hσ k l) rfl rfl
    have hSt : S.transpose = S := by
      ext k l; simp only [S, transpose_apply, of_apply]
      congr 1
      · exact if_congr (hσ k l) rfl rfl
      · exact if_congr ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩ rfl rfl
    have hPd : P.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hPP
      rw [det_mul, h0, zero_mul, det_one] at this
      exact zero_ne_one this
    have hSd : S.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hPS
      rw [det_mul, h0, mul_zero, TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]
        at this
      exact zero_ne_one this
    rw [← hPS]
    exact diagMap_symm_mul hPt hSt hPd hSd
  · intro A B _ _ hA hB
    rw [diagMap_mul]
    exact ShearProd.comp hB hA

end Matrices

/-! ### Linear symplectic maps -/

/-- A linear self-map of `X d` preserving ω. -/
def IsSympLin (L : X d →ₗ[ℝ] X d) : Prop :=
  ∀ v w, symplecticForm (L v) (L w) = symplecticForm v w

/-- The linear upper shear (p, q) ↦ (p + f q, q). -/
def upLin (f : E d →ₗ[ℝ] E d) : X d →ₗ[ℝ] X d :=
  (LinearMap.fst ℝ (E d) (E d) + f ∘ₗ LinearMap.snd ℝ (E d) (E d)).prod (LinearMap.snd ℝ _ _)

/-- The linear lower shear (p, q) ↦ (p, q + f p). -/
def lowLin (f : E d →ₗ[ℝ] E d) : X d →ₗ[ℝ] X d :=
  (LinearMap.fst ℝ (E d) (E d)).prod (LinearMap.snd ℝ _ _ + f ∘ₗ LinearMap.fst ℝ (E d) (E d))

theorem coe_upLin (f : E d →ₗ[ℝ] E d) : ⇑(upLin f) = upShear f := rfl

theorem coe_lowLin (f : E d →ₗ[ℝ] E d) : ⇑(lowLin f) = lowShear f := rfl

def IsSymmLin (f : E d →ₗ[ℝ] E d) : Prop := ∀ u v, f u ⬝ᵥ v = f v ⬝ᵥ u

theorem IsSympLin.comp {L L' : X d →ₗ[ℝ] X d} (h : IsSympLin L) (h' : IsSympLin L') :
    IsSympLin (L ∘ₗ L') := fun v w => by rw [LinearMap.comp_apply, LinearMap.comp_apply, h, h']

theorem isSympLin_upLin {f : E d →ₗ[ℝ] E d} (hf : IsSymmLin f) : IsSympLin (upLin f) := by
  intro v w
  rw [symplecticForm_eq_dot, symplecticForm_eq_dot]
  simp only [coe_upLin, upShear, add_dotProduct, dotProduct_add]
  rw [hf v.2 w.2, dotProduct_comm v.2 (f w.2)]; ring

theorem isSympLin_lowLin {f : E d →ₗ[ℝ] E d} (hf : IsSymmLin f) : IsSympLin (lowLin f) := by
  intro v w
  rw [symplecticForm_eq_dot, symplecticForm_eq_dot]
  simp only [coe_lowLin, lowShear, add_dotProduct, dotProduct_add]
  rw [hf v.1 w.1, dotProduct_comm v.1 (f w.1)]; ring

theorem IsSymmLin.neg {f : E d →ₗ[ℝ] E d} (hf : IsSymmLin f) : IsSymmLin (-f) := neg_symm hf

theorem mem_of_up {L : X d →ₗ[ℝ] X d} {f : E d →ₗ[ℝ] E d} (hf : IsSymmLin f)
    (h : ⇑(upLin f ∘ₗ L) ∈ ShearProd d) : ⇑L ∈ ShearProd d := by
  have := ShearProd.comp h (upShear_lin_mem (-f) hf.neg)
  convert this using 1
  funext z; simp [upShear, coe_upLin]

theorem mem_of_low {L : X d →ₗ[ℝ] X d} {f : E d →ₗ[ℝ] E d} (hf : IsSymmLin f)
    (h : ⇑(lowLin f ∘ₗ L) ∈ ShearProd d) : ⇑L ∈ ShearProd d := by
  have := ShearProd.comp h (lowShear_lin_mem (-f) hf.neg)
  convert this using 1
  funext z; simp [lowShear, coe_lowLin]

theorem mem_of_comp_up {L : X d →ₗ[ℝ] X d} {f : E d →ₗ[ℝ] E d} (hf : IsSymmLin f)
    (h : ⇑(L ∘ₗ upLin f) ∈ ShearProd d) : ⇑L ∈ ShearProd d := by
  have := ShearProd.comp (upShear_lin_mem (-f) hf.neg) h
  convert this using 1
  funext z; simp [upShear, coe_upLin]

/-- Block A: x ↦ (L(x,0)).1, etc. -/
def blkA (L : X d →ₗ[ℝ] X d) : E d →ₗ[ℝ] E d :=
  LinearMap.fst ℝ (E d) (E d) ∘ₗ L ∘ₗ LinearMap.inl ℝ (E d) (E d)
def blkC (L : X d →ₗ[ℝ] X d) : E d →ₗ[ℝ] E d :=
  LinearMap.snd ℝ (E d) (E d) ∘ₗ L ∘ₗ LinearMap.inl ℝ (E d) (E d)
def blkB (L : X d →ₗ[ℝ] X d) : E d →ₗ[ℝ] E d :=
  LinearMap.fst ℝ (E d) (E d) ∘ₗ L ∘ₗ LinearMap.inr ℝ (E d) (E d)
def blkD (L : X d →ₗ[ℝ] X d) : E d →ₗ[ℝ] E d :=
  LinearMap.snd ℝ (E d) (E d) ∘ₗ L ∘ₗ LinearMap.inr ℝ (E d) (E d)

theorem L_inl (L : X d →ₗ[ℝ] X d) (x : E d) : L (x, 0) = (blkA L x, blkC L x) := rfl
theorem L_inr (L : X d →ₗ[ℝ] X d) (q : E d) : L (0, q) = (blkB L q, blkD L q) := rfl

theorem L_apply (L : X d →ₗ[ℝ] X d) (z : X d) :
    L z = (blkA L z.1 + blkB L z.2, blkC L z.1 + blkD L z.2) := by
  have : z = (z.1, 0) + (0, z.2) := by simp
  conv_lhs => rw [this]
  rw [map_add, L_inl, L_inr]; rfl

theorem IsSympLin.I1 {L : X d →ₗ[ℝ] X d} (h : IsSympLin L) (x y : E d) :
    blkA L x ⬝ᵥ blkC L y = blkC L x ⬝ᵥ blkA L y := by
  have := h (x, 0) (y, 0)
  rw [symplecticForm_eq_dot, symplecticForm_eq_dot, L_inl, L_inl] at this
  simp at this; linarith

theorem IsSympLin.I2 {L : X d →ₗ[ℝ] X d} (h : IsSympLin L) (x q : E d) :
    blkA L x ⬝ᵥ blkD L q - blkC L x ⬝ᵥ blkB L q = x ⬝ᵥ q := by
  have := h (x, 0) (0, q)
  rw [symplecticForm_eq_dot, symplecticForm_eq_dot, L_inl, L_inr] at this
  simpa using this

theorem IsSympLin.I3 {L : X d →ₗ[ℝ] X d} (h : IsSympLin L) (q q' : E d) :
    blkB L q ⬝ᵥ blkD L q' = blkD L q ⬝ᵥ blkB L q' := by
  have := h (0, q) (0, q')
  rw [symplecticForm_eq_dot, symplecticForm_eq_dot, L_inr, L_inr] at this
  simp at this; linarith

theorem IsSympLin.injective {L : X d →ₗ[ℝ] X d} (h : IsSympLin L) : Function.Injective L := by
  refine (injective_iff_map_eq_zero L).2 fun v hv => eq_zero_of_symplecticForm fun w => ?_
  rw [← h, hv]; simp [symplecticForm]

/-- Step 4: (x, q) ↦ (a x, e q) with ⟨a x, e q⟩ = ⟨x, q⟩. -/
theorem diag_mem (a e : E d →ₗ[ℝ] E d) (ha : Function.Injective a)
    (hae : ∀ x q, a x ⬝ᵥ e q = x ⬝ᵥ q) : (fun z : X d => (a z.1, e z.2)) ∈ ShearProd d := by
  set M := LinearMap.toMatrix' a
  have hMa : ∀ x, M.mulVec x = a x := LinearMap.toMatrix'_mulVec a
  have hMinj : Function.Injective M.mulVec := by
    intro x y hxy; exact ha (by rw [← hMa, ← hMa, hxy])
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1
    (Matrix.mulVec_injective_iff_isUnit.1 hMinj)
  have hMt : ∀ q, M.transpose.mulVec (e q) = q := by
    intro q
    funext i
    have h1 := hae (Pi.single i 1) q
    rw [← hMa, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_comm] at h1
    simpa [single_dotProduct] using h1
  have he : ∀ q, e q = (M⁻¹).transpose.mulVec q := by
    intro q
    have hu : IsUnit M.transpose.det := by rwa [Matrix.det_transpose]
    calc e q = (M.transpose)⁻¹.mulVec (M.transpose.mulVec (e q)) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      _ = (M⁻¹).transpose.mulVec q := by rw [hMt, Matrix.transpose_nonsing_inv]
  have := diagMap_mem M (isUnit_iff_ne_zero.1 hMu)
  convert this using 1
  funext z; simp [diagMap, hMa, he]

/-- Step 3: the C block vanishes and A is injective. -/
theorem mem_of_C_zero (L : X d →ₗ[ℝ] X d) (hL : IsSympLin L) (hC : ∀ x, blkC L x = 0)
    (hA : Function.Injective (blkA L)) : ⇑L ∈ ShearProd d := by
  set a := blkA L
  set b := blkB L
  set e := blkD L
  have hI2 : ∀ x q, a x ⬝ᵥ e q = x ⬝ᵥ q := fun x q => by
    have := hL.I2 x q; rw [hC] at this; simpa using this
  set ae := LinearEquiv.ofInjectiveEndo a hA
  set T : E d →ₗ[ℝ] E d := ae.symm.toLinearMap ∘ₗ b
  have haT : ∀ q, a (T q) = b q := fun q => by
    show ae (ae.symm (b q)) = b q
    exact ae.apply_symm_apply _
  have hT : IsSymmLin T := by
    intro q q'
    rw [← hI2, haT, hL.I3, dotProduct_comm, ← haT q', hI2, dotProduct_comm]
  refine mem_of_comp_up (f := -T) hT.neg ?_
  have := diag_mem a e hA hI2
  convert this using 1
  funext z
  rw [LinearMap.comp_apply, L_apply, coe_upLin]
  simp only [upShear, LinearMap.neg_apply, map_add, map_neg, haT, hC, zero_add]
  refine Prod.ext ?_ rfl
  dsimp only
  rw [show blkA L (T z.2) = blkB L z.2 from haT z.2]
  abel

/-- Step 2: A is injective. -/
theorem mem_of_A_inj (L : X d →ₗ[ℝ] X d) (hL : IsSympLin L) (hA : Function.Injective (blkA L)) :
    ⇑L ∈ ShearProd d := by
  set a := blkA L
  set c := blkC L
  set ae := LinearEquiv.ofInjectiveEndo a hA
  set S : E d →ₗ[ℝ] E d := c ∘ₗ ae.symm.toLinearMap
  have hS : IsSymmLin S := by
    intro u v
    obtain ⟨x, rfl⟩ : ∃ x, ae x = u := ⟨ae.symm u, ae.apply_symm_apply u⟩
    obtain ⟨y, rfl⟩ : ∃ y, ae y = v := ⟨ae.symm v, ae.apply_symm_apply v⟩
    simp only [S, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    show c x ⬝ᵥ a y = c y ⬝ᵥ a x
    rw [← hL.I1, dotProduct_comm]
  set L' := lowLin (-S) ∘ₗ L
  have hL' : IsSympLin L' := (isSympLin_lowLin hS.neg).comp hL
  have hA' : blkA L' = a := LinearMap.ext fun x => rfl
  have hSa : ∀ x, S (a x) = c x := fun x => by
    simp only [S, LinearMap.comp_apply, LinearEquiv.coe_coe]
    congr 1; exact ae.symm_apply_apply x
  have hC' : ∀ x, blkC L' x = 0 := fun x => by
    have : blkC L' x = c x + (-S) (a x) := rfl
    rw [this, LinearMap.neg_apply, hSa, add_neg_cancel]
  refine mem_of_low (f := -S) hS.neg ?_
  exact mem_of_C_zero L' hL' hC' (by rw [hA']; exact hA)

/-- **Every linear symplectic map is a finite composition of linear gradient shears.** -/
theorem linSymp_mem (L : X d →ₗ[ℝ] X d) (hL : IsSympLin L) : ⇑L ∈ ShearProd d := by
  set A := LinearMap.toMatrix' (blkA L)
  set C := LinearMap.toMatrix' (blkC L)
  have hAx : ∀ x, A.mulVec x = blkA L x := LinearMap.toMatrix'_mulVec _
  have hCx : ∀ x, C.mulVec x = blkC L x := LinearMap.toMatrix'_mulVec _
  have key : ∀ x y : E d, A.mulVec x = C.mulVec y → C.mulVec x = -(A.mulVec y) → x = 0 := by
    intro x y h1 h2
    rw [hAx, hCx] at h1; rw [hAx, hCx] at h2
    have h := hL.I1 x y
    rw [← h1, show blkA L y = -blkC L x by rw [h2, neg_neg], dotProduct_neg] at h
    have hs : blkA L x ⬝ᵥ blkA L x + blkC L x ⬝ᵥ blkC L x = 0 := by linarith
    have n1 : 0 ≤ blkA L x ⬝ᵥ blkA L x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have n2 : 0 ≤ blkC L x ⬝ᵥ blkC L x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have ha : blkA L x = 0 := dotProduct_self_eq_zero.1 (by linarith)
    have hc : blkC L x = 0 := dotProduct_self_eq_zero.1 (by linarith)
    have : L (x, 0) = L 0 := by rw [L_inl, ha, hc, map_zero]; rfl
    exact congrArg Prod.fst (hL.injective this)
  obtain ⟨t, ht⟩ := exists_det_add_smul_ne_zero A C key
  have hinj : Function.Injective (A + t • C).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ht))
  set f : E d →ₗ[ℝ] E d := t • LinearMap.id
  have hf : IsSymmLin f := fun u v => by simp [f, smul_dotProduct, dotProduct_comm]
  refine mem_of_up (f := f) hf ?_
  refine mem_of_A_inj _ ((isSympLin_upLin hf).comp hL) ?_
  intro x y hxy
  apply hinj
  have e : ∀ x, (A + t • C).mulVec x = blkA (upLin f ∘ₗ L) x := fun x => by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, hAx, hCx]; rfl
  rw [e, e, hxy]

end SympNet
