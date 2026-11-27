/-
  T-A: the Alexander isotopy of a global symplectic diffeomorphism G with G 0 = 0.

  Gt(t, x) = G(t x)/t (t ≠ 0), Gt(0, x) = DG(0) x is smooth in (t, x) (Hadamard), symplectic in
  x for every t, with smooth inverse Git(t, ·) built the same way from G⁻¹. Its velocity field
  X(t, z) = ∂ₜGt(t, Git(t, z)) is Hamiltonian: X(t, ·) = J∇ₓ(−H(t, ·)) with
  H(t, z) = ∫₀¹ ω(X(t, sz), z) ds jointly smooth.
-/
import Sympnet.Turaev.LinSymp

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace SympNet

variable {d : ℕ}

/-! ### Generalities -/

/-- ω as a continuous bilinear map. -/
def omL (d : ℕ) : X d →L[ℝ] X d →L[ℝ] ℝ :=
  (toCov d).comp ((-(ContinuousLinearMap.snd ℝ (E d) (E d))).prod
    (ContinuousLinearMap.fst ℝ (E d) (E d)))

theorem omL_apply (v w : X d) : omL d v w = symplecticForm v w := by
  simp only [omL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    neg_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    toCov_apply, symplecticForm, Pi.neg_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symplecticForm_antisymm (v w : X d) : symplecticForm v w = -symplecticForm w v := by
  simp only [symplecticForm, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dT_eq_deriv {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : ℝ × Y → Z} {p : ℝ × Y}
    (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun s => f (s, p.2)) (dT f p) p.1 := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, p.2) : ℝ × Y)) ((1, 0) : ℝ × Y) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const _ _)
  have := hf.hasFDerivAt.comp_hasDerivAt (x := p.1) (f := fun s : ℝ => ((s, p.2) : ℝ × Y))
    (by simpa using h1)
  exact this

/-- The partial derivative in `x` of a function of `(t, x)`. -/
theorem hasFDerivAt_partial {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : ℝ × Y → Z} {t : ℝ} {x : Y}
    (hf : DifferentiableAt ℝ f (t, x)) :
    HasFDerivAt (fun y => f (t, y)) ((fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Y)) x := by
  have h1 : HasFDerivAt (fun y : Y => ((t, y) : ℝ × Y)) (ContinuousLinearMap.inr ℝ ℝ Y) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  exact hf.hasFDerivAt.comp x h1

/-! ### The inverse of G -/

section Inverse

/-- The inverse map. -/
def sdInv (G : X d → X d) : X d → X d := Function.invFunOn G univ

variable {G : X d → X d} (hG : G ∈ SympDiffeo d)
include hG

theorem sd_injective_fderiv (x : X d) : Function.Injective (fderiv ℝ G x) :=
  injective_of_symplectic (hG.2.2 x)

/-- The derivative as a linear equivalence. -/
def sdEquiv (x : X d) : X d ≃L[ℝ] X d :=
  (LinearEquiv.ofInjectiveEndo (fderiv ℝ G x : X d →ₗ[ℝ] X d)
    (sd_injective_fderiv hG x)).toContinuousLinearEquiv

theorem sdEquiv_coe (x : X d) : (sdEquiv hG x : X d →L[ℝ] X d) = fderiv ℝ G x :=
  ContinuousLinearMap.ext fun v => rfl

theorem sd_apply_inv (z : X d) : G (sdInv G z) = z :=
  Function.invFunOn_eq (f := G) (s := univ) (by
    obtain ⟨x, rfl⟩ := hG.2.1.2 z; exact ⟨x, mem_univ _, rfl⟩)

theorem sd_inv_apply (x : X d) : sdInv G (G x) = x :=
  invFunOn_apply_self (hG.2.1.1.injOn) (mem_univ x)

theorem sd_contDiff_inv : ContDiff ℝ ∞ (sdInv G) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rw [← sd_apply_inv hG z]
  refine contDiffAt_invFunOn (e := sdEquiv hG) isOpen_univ hG.1.contDiffOn (by simp)
    (fun x _ => ?_) hG.2.1.1.injOn (mem_univ _)
  rw [sdEquiv_coe]
  exact ((hG.1.differentiable (by simp)) x).hasFDerivAt

theorem sd_inv_zero (h0 : G 0 = 0) : sdInv G 0 = 0 :=
  calc sdInv G 0 = sdInv G (G 0) := by rw [h0]
    _ = 0 := sd_inv_apply hG 0

end Inverse

/-! ### The isotopy -/

/-- Alexander isotopy `Gt(t, x) = G(t x)/t`, smooth through `t = 0`. -/
def alexT (G : X d → X d) : ℝ × X d → X d := hadQ (fun p : ℝ × X d => G (p.1 • p.2))

section Isotopy

variable {G : X d → X d} (hG : ContDiff ℝ ∞ G) (h0 : G 0 = 0)
include hG

theorem contDiff_alexT : ContDiff ℝ ∞ (alexT G) :=
  contDiff_hadQ (hG.comp (contDiff_fst.smul contDiff_snd))

include h0

theorem alexT_smul (t : ℝ) (x : X d) : t • alexT G (t, x) = G (t • x) :=
  (hadamard_eq (f := fun p : ℝ × X d => G (p.1 • p.2)) (hG.comp (contDiff_fst.smul contDiff_snd))
    (fun y => by simp [h0]) (t, x)).symm

theorem alexT_of_ne {t : ℝ} (ht : t ≠ 0) (x : X d) : alexT G (t, x) = t⁻¹ • G (t • x) := by
  rw [← alexT_smul hG h0, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem alexT_one (x : X d) : alexT G (1, x) = G x := by
  simpa using alexT_smul hG h0 1 x

theorem alexT_zero (x : X d) : alexT G (0, x) = fderiv ℝ G 0 x := by
  rw [alexT, hadQ_zero]
  have hf : ContDiff ℝ ∞ (fun p : ℝ × X d => G (p.1 • p.2)) :=
    hG.comp (contDiff_fst.smul contDiff_snd)
  have h1 := dT_eq_deriv (p := ((0 : ℝ), x)) ((hf.differentiable (by simp)) _)
  have h2 : HasDerivAt (fun s : ℝ => G (s • x)) (fderiv ℝ G 0 x) 0 := by
    have h3 : HasDerivAt (fun s : ℝ => s • x) x 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const x
    exact ((hG.differentiable (by simp)) 0).hasFDerivAt.comp_hasDerivAt_of_eq 0 h3 (by simp)
  exact h1.unique h2

theorem alexT_zero_fun : (fun x => alexT G (0, x)) = ⇑(fderiv ℝ G 0) :=
  funext (alexT_zero hG h0)

theorem hasFDerivAt_alexT_slice (t : ℝ) (x : X d) :
    HasFDerivAt (fun y => alexT G (t, y)) (fderiv ℝ G (t • x)) x := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [alexT_zero_fun hG h0, zero_smul]; exact (fderiv ℝ G 0).hasFDerivAt
  · have e : (fun y => alexT G (t, y)) = fun y => t⁻¹ • G (t • y) :=
      funext (alexT_of_ne hG h0 ht)
    rw [e]
    have h : HasFDerivAt (fun y => t⁻¹ • G (t • y))
        (t⁻¹ • (fderiv ℝ G (t • x)).comp (t • ContinuousLinearMap.id ℝ (X d))) x :=
      (((hG.differentiable (by simp)) (t • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul t)).const_smul t⁻¹
    convert h using 1
    refine ContinuousLinearMap.ext fun v => ?_
    simp [smul_smul, inv_mul_cancel₀ ht]

theorem isSymplecticAt_alexT (hs : ∀ x, IsSymplecticAt G x) (t : ℝ) (x : X d) :
    IsSymplecticAt (fun y => alexT G (t, y)) x := by
  intro v w
  rw [(hasFDerivAt_alexT_slice hG h0 t x).fderiv]
  exact hs _ v w

end Isotopy

/-! ### Inverse of the isotopy -/

section InverseIsotopy

variable {G : X d → X d} (hG : G ∈ SympDiffeo d) (h0 : G 0 = 0)
include hG h0

theorem alexT_inv_left (t : ℝ) (x : X d) : alexT (sdInv G) (t, alexT G (t, x)) = x := by
  have hGi := sd_contDiff_inv hG
  have hi0 := sd_inv_zero hG h0
  rcases eq_or_ne t 0 with rfl | ht
  · rw [alexT_zero hG.1 h0, alexT_zero hGi hi0]
    have hcomp : sdInv G ∘ G = id := funext (sd_inv_apply hG)
    have hd := fderiv_comp (0 : X d) ((hGi.differentiable (by simp)) (G 0))
      ((hG.1.differentiable (by simp)) 0)
    rw [hcomp, fderiv_id, h0] at hd
    have := congrArg (fun L : X d →L[ℝ] X d => L x) hd
    simpa using this.symm
  · rw [alexT_of_ne hG.1 h0 ht, alexT_of_ne hGi hi0 ht, smul_smul, mul_inv_cancel₀ ht,
      one_smul, sd_inv_apply hG, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem alexT_inv_right (t : ℝ) (z : X d) : alexT G (t, alexT (sdInv G) (t, z)) = z := by
  have hGi := sd_contDiff_inv hG
  have hi0 := sd_inv_zero hG h0
  rcases eq_or_ne t 0 with rfl | ht
  · rw [alexT_zero hG.1 h0, alexT_zero hGi hi0]
    have hcomp : G ∘ sdInv G = id := funext (sd_apply_inv hG)
    have hd := fderiv_comp (0 : X d) ((hG.1.differentiable (by simp)) (sdInv G 0))
      ((hGi.differentiable (by simp)) 0)
    rw [hcomp, fderiv_id, hi0] at hd
    have := congrArg (fun L : X d →L[ℝ] X d => L z) hd
    simpa using this.symm
  · rw [alexT_of_ne hGi hi0 ht, alexT_of_ne hG.1 h0 ht, smul_smul, mul_inv_cancel₀ ht,
      one_smul, sd_apply_inv hG, smul_smul, inv_mul_cancel₀ ht, one_smul]

end InverseIsotopy

/-! ### The velocity field and its Hamiltonian -/

/-- ∂ₜGt. -/
def velY (G : X d → X d) : ℝ × X d → X d := dT (alexT G)

/-- The velocity field X(t, z) = ∂ₜGt(t, Git(t, z)). -/
def velX (G : X d → X d) (p : ℝ × X d) : X d := velY G (p.1, alexT (sdInv G) p)

/-- The Hamiltonian H(t, z) = ∫₀¹ ω(X(t, sz), z) ds. -/
def hamF (G : X d → X d) (p : ℝ × X d) : ℝ :=
  ∫ s in (0 : ℝ)..1, symplecticForm (velX G (p.1, s • p.2)) p.2

theorem Jop_omL (w : X d) : Jop d (omL d w) = -w := by
  have h1 : clmP d (omL d w) = -w.2 := by
    rw [omL, ContinuousLinearMap.comp_apply, clmP_toCov]; rfl
  have h2 : clmQ d (omL d w) = w.1 := by
    rw [omL, ContinuousLinearMap.comp_apply, clmQ_toCov]; rfl
  simp only [Jop, h1, h2]; rfl

theorem Jop_neg (L : X d →L[ℝ] ℝ) : Jop d (-L) = -Jop d L := by
  simp [Jop, map_neg]

section Velocity

variable {G : X d → X d} (hG : G ∈ SympDiffeo d) (h0 : G 0 = 0)
include hG h0

theorem contDiff_velY : ContDiff ℝ ∞ (velY G) := contDiff_dT (contDiff_alexT hG.1)

theorem contDiff_velX : ContDiff ℝ ∞ (velX G) :=
  (contDiff_velY hG h0).comp (contDiff_fst.prodMk (contDiff_alexT (sd_contDiff_inv hG)))

theorem velX_skew (t : ℝ) (z u v : X d) :
    symplecticForm (fderiv ℝ (fun z => velX G (t, z)) z u) v +
      symplecticForm u (fderiv ℝ (fun z => velX G (t, z)) z v) = 0 := by
  set F := alexT G
  set Fi := alexT (sdInv G)
  have hF : ContDiff ℝ ∞ F := contDiff_alexT hG.1
  have hFi : ContDiff ℝ ∞ Fi := contDiff_alexT (sd_contDiff_inv hG)
  have hdF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by simp)
  set x := Fi (t, z)
  set D := fderiv ℝ F (t, x)
  set D2 := fderiv ℝ (fderiv ℝ F) (t, x)
  -- Step A: derivative of the symplectic identity in t
  have hA : ∀ a b : X d, symplecticForm (D2 (1, 0) (0, a)) (D (0, b)) +
      symplecticForm (D (0, a)) (D2 (1, 0) (0, b)) = 0 := by
    intro a b
    have hc : HasDerivAt (fun s => fderiv ℝ F (s, x)) (D2 (1, 0)) t :=
      dT_eq_deriv (p := (t, x)) ((hdF.differentiable (by simp)) _)
    have ha := hc.clm_apply (hasDerivAt_const t ((0, a) : ℝ × X d))
    have hb := hc.clm_apply (hasDerivAt_const t ((0, b) : ℝ × X d))
    have hφ := ((omL d).hasFDerivAt.comp_hasDerivAt t ha).clm_apply hb
    simp only [map_zero, add_zero] at hφ
    have hconst : (fun s => (omL d) (fderiv ℝ F (s, x) (0, a)) (fderiv ℝ F (s, x) (0, b))) =
        fun _ => symplecticForm a b := by
      funext s
      have hs := isSymplecticAt_alexT hG.1 h0 hG.2.2 s x a b
      rw [(hasFDerivAt_partial ((hF.differentiable (by simp)) (s, x))).fderiv] at hs
      rw [omL_apply]; simpa using hs
    rw [Function.comp_def] at hφ
    simp only at hφ
    rw [hconst] at hφ
    have := hφ.unique (hasDerivAt_const t _)
    simpa [omL_apply] using this
  -- Step B: symmetry of mixed partials
  have hB : ∀ a : X d, D2 (0, a) (1, 0) = D2 (1, 0) (0, a) := fun a =>
    ((hF.contDiffAt).isSymmSndFDerivAt (by simp)) _ _
  -- Step C: the x-derivative of velY
  have hY : HasFDerivAt (fun y => velY G (t, y))
      ((D2.flip (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ (X d))) x := by
    have h1 : HasFDerivAt (fun p => fderiv ℝ F p (1, 0)) (D.comp 0 + D2.flip (1, 0)) (t, x) :=
      ((hdF.differentiable (by simp)) _).hasFDerivAt.clm_apply (hasFDerivAt_const _ _)
    simp only [ContinuousLinearMap.comp_zero, zero_add] at h1
    have h2 : HasFDerivAt (fun y : X d => ((t, y) : ℝ × X d)) (ContinuousLinearMap.inr ℝ ℝ (X d)) x :=
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    exact h1.comp x h2
  -- Step D: derivative of the inverse slice
  set Dzi := (fderiv ℝ Fi (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ (X d))
  have hzi : HasFDerivAt (fun z => Fi (t, z)) Dzi z :=
    hasFDerivAt_partial ((hFi.differentiable (by simp)) _)
  have hDF : HasFDerivAt (fun y => F (t, y)) (D.comp (ContinuousLinearMap.inr ℝ ℝ (X d))) x :=
    hasFDerivAt_partial ((hF.differentiable (by simp)) _)
  have hinv : ∀ w, D (0, Dzi w) = w := by
    intro w
    have hc := hDF.comp z hzi
    have heq : ((fun y => F (t, y)) ∘ fun z => Fi (t, z)) = id :=
      funext fun z => alexT_inv_right hG h0 t z
    rw [heq] at hc
    have := congrArg (fun L : X d →L[ℝ] X d => L w) (hc.unique (hasFDerivAt_id z))
    simpa using this
  -- Step E: derivative of velX
  have hX : HasFDerivAt (fun z => velX G (t, z))
      (((D2.flip (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ (X d))).comp Dzi) z := by
    have hX0 := hY.comp z hzi
    exact hX0
  rw [hX.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inr_apply, hB]
  have := hA (Dzi u) (Dzi v)
  rwa [hinv, hinv] at this

theorem hasFDerivAt_velX_slice (t : ℝ) (z : X d) :
    HasFDerivAt (fun z => velX G (t, z)) (fderiv ℝ (fun z => velX G (t, z)) z) z :=
  (hasFDerivAt_partial (((contDiff_velX hG h0).differentiable (by simp)) (t, z))).differentiableAt.hasFDerivAt

theorem contDiff_hamF : ContDiff ℝ ∞ (hamF G) := by
  have h : hamF G = fun p => ∫ s in Ioc (0 : ℝ) 1,
      (fun (p : ℝ × X d) (s : ℝ) => omL d (velX G (p.1, s • p.2)) p.2) p s := by
    funext p; simp only [hamF, intervalIntegral.integral_of_le zero_le_one, omL_apply]
  rw [h]
  refine ContDiff.parametric_integral (k := Icc 0 1) isCompact_Icc Ioc_subset_Icc_self
    (by simp) ?_
  refine ((omL d).contDiff.comp ((contDiff_velX hG h0).comp ?_)).clm_apply
    (contDiff_snd.comp contDiff_fst)
  exact (contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.smul (contDiff_snd.comp contDiff_fst))

/-- **The velocity field is Hamiltonian**: D_z H(t, z) = ω(X(t, z), ·). -/
theorem hasFDerivAt_hamF (t : ℝ) (z : X d) :
    HasFDerivAt (fun z => hamF G (t, z)) (omL d (velX G (t, z))) z := by
  set β : X d → X d →L[ℝ] ℝ := fun z => omL d (velX G (t, z))
  have hβd : ∀ z, HasFDerivAt β ((omL d).comp (fderiv ℝ (fun z => velX G (t, z)) z)) z :=
    fun z => (omL d).hasFDerivAt.comp z (hasFDerivAt_velX_slice hG h0 t z)
  obtain ⟨P, hP⟩ := convex_univ.exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_univ
    (show DifferentiableOn ℝ β univ from
      fun z _ => (hβd z).differentiableAt.differentiableWithinAt) (fun z _ u v => by
      rw [(hβd z).fderiv]
      simp only [ContinuousLinearMap.comp_apply, omL_apply]
      have := velX_skew hG h0 t z u v
      rw [symplecticForm_antisymm u] at this
      linarith)
  have heq : (fun z => hamF G (t, z)) = fun z => P z - P 0 := by
    funext z
    rw [← segInt_eq_sub (fun y _ => hP y (mem_univ y))
      (fun y _ => (hβd y).continuousAt.continuousWithinAt)]
    simp [segInt, hamF, β, omL_apply]
  rw [heq]
  exact (hP z (mem_univ z)).sub_const _

/-- X(t, z) = J∇(−H(t, ·))(z). -/
theorem velX_eq_Jop (t : ℝ) (z : X d) :
    velX G (t, z) = -Jop d (fderiv ℝ (fun z => hamF G (t, z)) z) := by
  rw [(hasFDerivAt_hamF hG h0 t z).fderiv, Jop_omL, neg_neg]

end Velocity

end SympNet
