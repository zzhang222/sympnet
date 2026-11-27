/-
  C7: the generating function of a pair of symplectic maps.

  Given C^r symplectic maps A, B on a convex open set R', put
    μ = (B_p, A_q),   Ỹ = (B_q − A_q, A_p − B_p).
  If μ is injective on R' with invertible derivative, then on W = μ(R') there is a C^{r+1}
  function s with  ∇_P s(μ x) = B_q x − A_q x,  ∇_q s(μ x) = A_p x − B_p x.
  Consequently Ψ₁(μ x) = A x and Ψ₂(μ x) = B x for the maps of `GenFun.lean`.
-/
import Sympnet.Smoothing.GenFun
import Sympnet.Smoothing.Goursat

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace SympNet

variable {d : ℕ}

/-! ### Covectors from vectors -/

/-- Y ↦ (w ↦ Y₁·w₁ + Y₂·w₂). -/
def toCov (d : ℕ) : X d →L[ℝ] (X d →L[ℝ] ℝ) :=
  ∑ i : Fin d,
    ((((ContinuousLinearMap.proj i : E d →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ (E d) (E d))).smulRight
        ((ContinuousLinearMap.proj i : E d →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ (E d) (E d)))) +
      (((ContinuousLinearMap.proj i : E d →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ (E d) (E d))).smulRight
        ((ContinuousLinearMap.proj i : E d →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ (E d) (E d)))))

theorem toCov_apply (Y w : X d) : toCov d Y w = ∑ i, (Y.1 i * w.1 i + Y.2 i * w.2 i) := by
  simp [toCov, ContinuousLinearMap.sum_apply, mul_comm]

theorem clmP_toCov (Y : X d) : clmP d (toCov d Y) = Y.1 := by
  funext i
  simp only [clmP, ContinuousLinearMap.comp_apply, gradCLM_apply]
  simp [toCov_apply, Pi.single_apply]

theorem clmQ_toCov (Y : X d) : clmQ d (toCov d Y) = Y.2 := by
  funext i
  simp only [clmQ, ContinuousLinearMap.comp_apply, gradCLM_apply]
  simp [toCov_apply, Pi.single_apply]

/-! ### The pair maps -/

/-- μ = (B_p, A_q). -/
def mu (A B : X d → X d) (x : X d) : X d := ((B x).1, (A x).2)

/-- Ỹ = (B_q − A_q, A_p − B_p). -/
def Yt (A B : X d → X d) (x : X d) : X d := ((B x).2 - (A x).2, (A x).1 - (B x).1)

/-- Derivative of μ. -/
def dmu (DA DB : X d →L[ℝ] X d) : X d →L[ℝ] X d :=
  ((ContinuousLinearMap.fst ℝ (E d) (E d)).comp DB).prod
    ((ContinuousLinearMap.snd ℝ (E d) (E d)).comp DA)

/-- Derivative of Ỹ. -/
def dYt (DA DB : X d →L[ℝ] X d) : X d →L[ℝ] X d :=
  ((ContinuousLinearMap.snd ℝ (E d) (E d)).comp DB -
      (ContinuousLinearMap.snd ℝ (E d) (E d)).comp DA).prod
    ((ContinuousLinearMap.fst ℝ (E d) (E d)).comp DA -
      (ContinuousLinearMap.fst ℝ (E d) (E d)).comp DB)

theorem hasFDerivAt_mu {A B : X d → X d} {DA DB : X d →L[ℝ] X d} {x : X d}
    (hA : HasFDerivAt A DA x) (hB : HasFDerivAt B DB x) : HasFDerivAt (mu A B) (dmu DA DB) x :=
  ((ContinuousLinearMap.fst ℝ (E d) (E d)).hasFDerivAt.comp x hB).prodMk
    ((ContinuousLinearMap.snd ℝ (E d) (E d)).hasFDerivAt.comp x hA)

theorem hasFDerivAt_Yt {A B : X d → X d} {DA DB : X d →L[ℝ] X d} {x : X d}
    (hA : HasFDerivAt A DA x) (hB : HasFDerivAt B DB x) : HasFDerivAt (Yt A B) (dYt DA DB) x :=
  (((ContinuousLinearMap.snd ℝ (E d) (E d)).hasFDerivAt.comp x hB).sub
      ((ContinuousLinearMap.snd ℝ (E d) (E d)).hasFDerivAt.comp x hA)).prodMk
    (((ContinuousLinearMap.fst ℝ (E d) (E d)).hasFDerivAt.comp x hA).sub
      ((ContinuousLinearMap.fst ℝ (E d) (E d)).hasFDerivAt.comp x hB))

/-- The closedness identity: the antisymmetric part of ⟨DỸ a, Dμ b⟩ is ω∘DA − ω∘DB. -/
theorem pairing_antisymm (DA DB : X d →L[ℝ] X d) (a b : X d) :
    toCov d (dYt DA DB a) (dmu DA DB b) - toCov d (dYt DA DB b) (dmu DA DB a) =
      symplecticForm (DA a) (DA b) - symplecticForm (DB a) (DB b) := by
  simp only [toCov_apply, dYt, dmu, symplecticForm, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Pi.sub_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Inverting an injective local diffeomorphism on an open set -/

section Inverse
variable {f : X d → X d} {R : Set (X d)} {n : ℕ∞ω} {e : X d → X d ≃L[ℝ] X d}

theorem eventually_invFunOn_eq (hR : IsOpen R) (hf : ContDiffOn ℝ n f R) (hn : n ≠ 0)
    (he : ∀ x ∈ R, HasFDerivAt f (e x : X d →L[ℝ] X d) x) (hinj : InjOn f R) {x : X d}
    (hx : x ∈ R) :
    ∀ᶠ y in 𝓝 (f x), Function.invFunOn f R y =
      ((hf.contDiffAt (hR.mem_nhds hx)).localInverse (he x hx) hn) y ∧
      ((hf.contDiffAt (hR.mem_nhds hx)).localInverse (he x hx) hn) y ∈ R ∧
      f (((hf.contDiffAt (hR.mem_nhds hx)).localInverse (he x hx) hn) y) = y := by
  set hfa := hf.contDiffAt (hR.mem_nhds hx)
  have hs := hfa.hasStrictFDerivAt (he x hx) hn
  have h1 := hs.eventually_right_inverse
  have h2 : ∀ᶠ y in 𝓝 (f x), hs.localInverse f (e x) x y ∈ R := by
    apply hs.localInverse_continuousAt.preimage_mem_nhds
    rw [hs.localInverse_apply_image]; exact hR.mem_nhds hx
  filter_upwards [h1, h2] with y hy1 hy2
  have hyim : y ∈ f '' R := ⟨_, hy2, hy1⟩
  refine ⟨?_, hy2, hy1⟩
  exact hinj (Function.invFunOn_mem hyim) hy2
    ((Function.invFunOn_eq hyim).trans hy1.symm)

theorem isOpen_image_of_injOn (hR : IsOpen R) (hf : ContDiffOn ℝ n f R) (hn : n ≠ 0)
    (he : ∀ x ∈ R, HasFDerivAt f (e x : X d →L[ℝ] X d) x) (hinj : InjOn f R) :
    IsOpen (f '' R) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  filter_upwards [eventually_invFunOn_eq hR hf hn he hinj hx] with y hy
  exact ⟨_, hy.2.1, hy.2.2⟩

theorem contDiffAt_invFunOn (hR : IsOpen R) (hf : ContDiffOn ℝ n f R) (hn : n ≠ 0)
    (he : ∀ x ∈ R, HasFDerivAt f (e x : X d →L[ℝ] X d) x) (hinj : InjOn f R) {x : X d}
    (hx : x ∈ R) : ContDiffAt ℝ n (Function.invFunOn f R) (f x) :=
  ((hf.contDiffAt (hR.mem_nhds hx)).to_localInverse (he x hx) hn).congr_of_eventuallyEq
    ((eventually_invFunOn_eq hR hf hn he hinj hx).mono fun _ h => h.1)

theorem hasFDerivAt_invFunOn (hR : IsOpen R) (hf : ContDiffOn ℝ n f R) (hn : n ≠ 0)
    (he : ∀ x ∈ R, HasFDerivAt f (e x : X d →L[ℝ] X d) x) (hinj : InjOn f R) {x : X d}
    (hx : x ∈ R) :
    HasFDerivAt (Function.invFunOn f R) ((e x).symm : X d →L[ℝ] X d) (f x) := by
  set hfa := hf.contDiffAt (hR.mem_nhds hx)
  have hs := hfa.hasStrictFDerivAt (he x hx) hn
  exact hs.to_localInverse.hasFDerivAt.congr_of_eventuallyEq
    ((eventually_invFunOn_eq hR hf hn he hinj hx).mono fun _ h => h.1)

theorem invFunOn_apply_self (hinj : InjOn f R) {x : X d} (hx : x ∈ R) :
    Function.invFunOn f R (f x) = x :=
  hinj.leftInvOn_invFunOn hx

end Inverse

/-! ### The generating function of a pair -/

/-- Hypotheses on the pair (A, B) on the convex open set R'. -/
structure PairHyp (A B : X d → X d) (R : Set (X d)) (r : ℕ) : Prop where
  isOpen : IsOpen R
  convex : Convex ℝ R
  one_le : 1 ≤ r
  contDiffA : ContDiffOn ℝ r A R
  contDiffB : ContDiffOn ℝ r B R
  sympA : ∀ x ∈ R, IsSymplecticAt A x
  sympB : ∀ x ∈ R, IsSymplecticAt B x
  inj : InjOn (mu A B) R
  invertible : ∀ x ∈ R, ∃ e : X d ≃L[ℝ] X d,
    (e : X d →L[ℝ] X d) = dmu (fderiv ℝ A x) (fderiv ℝ B x)

namespace PairHyp

variable {A B : X d → X d} {R : Set (X d)} {r : ℕ}

theorem r_ne_zero (h : PairHyp A B R r) : (r : ℕ∞ω) ≠ 0 := by
  have := h.one_le; exact_mod_cast (by omega : r ≠ 0)

theorem hasFDerivAt_A (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) : HasFDerivAt A (fderiv ℝ A x) x :=
  ((h.contDiffA.contDiffAt (h.isOpen.mem_nhds hx)).differentiableAt h.r_ne_zero).hasFDerivAt

theorem hasFDerivAt_B (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) : HasFDerivAt B (fderiv ℝ B x) x :=
  ((h.contDiffB.contDiffAt (h.isOpen.mem_nhds hx)).differentiableAt h.r_ne_zero).hasFDerivAt

theorem hasFDerivAt_mu' (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) :
    HasFDerivAt (mu A B) (dmu (fderiv ℝ A x) (fderiv ℝ B x)) x :=
  hasFDerivAt_mu (h.hasFDerivAt_A hx) (h.hasFDerivAt_B hx)

theorem contDiffOn_mu (h : PairHyp A B R r) : ContDiffOn ℝ r (mu A B) R :=
  (contDiff_fst.comp_contDiffOn h.contDiffB).prodMk (contDiff_snd.comp_contDiffOn h.contDiffA)

theorem contDiffOn_Yt (h : PairHyp A B R r) : ContDiffOn ℝ r (Yt A B) R :=
  ((contDiff_snd.comp_contDiffOn h.contDiffB).sub (contDiff_snd.comp_contDiffOn h.contDiffA)).prodMk
    ((contDiff_fst.comp_contDiffOn h.contDiffA).sub (contDiff_fst.comp_contDiffOn h.contDiffB))

open Classical in
/-- The chosen inverse derivative. -/
def eq (h : PairHyp A B R r) (x : X d) : X d ≃L[ℝ] X d :=
  if hx : x ∈ R then Classical.choose (h.invertible x hx) else ContinuousLinearEquiv.refl ℝ _

theorem eq_coe (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) :
    (h.eq x : X d →L[ℝ] X d) = dmu (fderiv ℝ A x) (fderiv ℝ B x) := by
  simp only [PairHyp.eq, dif_pos hx]; exact Classical.choose_spec (h.invertible x hx)

theorem he (h : PairHyp A B R r) : ∀ x ∈ R, HasFDerivAt (mu A B) (h.eq x : X d →L[ℝ] X d) x := fun x hx => by
  rw [h.eq_coe hx]; exact h.hasFDerivAt_mu' hx

/-- The inverse ν of μ on W = μ(R'). -/
def nu (h : PairHyp A B R r) : X d → X d := Function.invFunOn (mu A B) R

/-- W = μ(R'). -/
def W (h : PairHyp A B R r) : Set (X d) := mu A B '' R

theorem isOpen_W (h : PairHyp A B R r) : IsOpen h.W :=
  isOpen_image_of_injOn h.isOpen h.contDiffOn_mu h.r_ne_zero h.he h.inj

theorem nu_mu (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) : h.nu (mu A B x) = x := invFunOn_apply_self h.inj hx

theorem nu_mem (h : PairHyp A B R r) {z : X d} (hz : z ∈ h.W) : h.nu z ∈ R := Function.invFunOn_mem hz

theorem mu_nu (h : PairHyp A B R r) {z : X d} (hz : z ∈ h.W) : mu A B (h.nu z) = z := Function.invFunOn_eq hz

theorem hasFDerivAt_nu (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) :
    HasFDerivAt h.nu ((h.eq x).symm : X d →L[ℝ] X d) (mu A B x) :=
  hasFDerivAt_invFunOn h.isOpen h.contDiffOn_mu h.r_ne_zero h.he h.inj hx

theorem contDiffAt_nu (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) : ContDiffAt ℝ r h.nu (mu A B x) :=
  contDiffAt_invFunOn h.isOpen h.contDiffOn_mu h.r_ne_zero h.he h.inj hx

/-- The 1-form θ on W. -/
def theta (h : PairHyp A B R r) (z : X d) : X d →L[ℝ] ℝ := toCov d (Yt A B (h.nu z))

theorem hasFDerivAt_theta (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) :
    HasFDerivAt h.theta ((toCov d).comp ((dYt (fderiv ℝ A x) (fderiv ℝ B x)).comp
      ((h.eq x).symm : X d →L[ℝ] X d))) (mu A B x) := by
  have hY : HasFDerivAt (Yt A B) (dYt (fderiv ℝ A x) (fderiv ℝ B x)) (h.nu (mu A B x)) := by
    rw [h.nu_mu hx]; exact hasFDerivAt_Yt (h.hasFDerivAt_A hx) (h.hasFDerivAt_B hx)
  exact (toCov d).hasFDerivAt.comp _ (hY.comp _ (h.hasFDerivAt_nu hx))

theorem theta_symm (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) (w w' : X d) :
    fderiv ℝ h.theta (mu A B x) w w' = fderiv ℝ h.theta (mu A B x) w' w := by
  rw [(h.hasFDerivAt_theta hx).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  set a := (h.eq x).symm w
  set b := (h.eq x).symm w'
  have hw : w = dmu (fderiv ℝ A x) (fderiv ℝ B x) a := by
    rw [← h.eq_coe hx]; simp [a]
  have hw' : w' = dmu (fderiv ℝ A x) (fderiv ℝ B x) b := by
    rw [← h.eq_coe hx]; simp [b]
  have key := pairing_antisymm (fderiv ℝ A x) (fderiv ℝ B x) a b
  rw [h.sympA x hx a b, h.sympB x hx a b, sub_self, sub_eq_zero] at key
  conv_lhs => rw [hw']
  conv_rhs => rw [hw]
  exact key

theorem differentiableAt_theta (h : PairHyp A B R r) {z : X d} (hz : z ∈ h.W) : DifferentiableAt ℝ h.theta z := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact (h.hasFDerivAt_theta hx).differentiableAt

/-- The 1-form β = μ*θ on R'. -/
def beta (h : PairHyp A B R r) (x : X d) : X d →L[ℝ] ℝ := (toCov d (Yt A B x)).comp (fderiv ℝ (mu A B) x)

theorem continuousOn_beta (h : PairHyp A B R r) : ContinuousOn h.beta R := by
  have h1 : ContinuousOn (fun x => toCov d (Yt A B x)) R :=
    (toCov d).continuous.comp_continuousOn h.contDiffOn_Yt.continuousOn
  have h2 : ContinuousOn (fderiv ℝ (mu A B)) R :=
    h.contDiffOn_mu.continuousOn_fderiv_of_isOpen h.isOpen (by exact_mod_cast h.one_le)
  exact h1.clm_comp h2

theorem locallyExact_beta (h : PairHyp A B R r) : ∀ x ∈ R, ∃ ε > 0, ∃ f : X d → ℝ,
    ∀ y ∈ ball x ε, HasFDerivAt f (h.beta y) y := by
  intro x hx
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 h.isOpen_W _ ⟨x, hx, rfl⟩
  have hdiff : DifferentiableOn ℝ h.theta (ball (mu A B x) ρ) := fun z hz =>
    (h.differentiableAt_theta (hρW hz)).differentiableWithinAt
  obtain ⟨σ, hσ⟩ := (convex_ball (mu A B x) ρ).exists_forall_hasFDerivAt_of_fderiv_symmetric
    isOpen_ball hdiff
    (fun z hz w w' => by
      obtain ⟨y, hy, rfl⟩ := hρW hz
      exact h.theta_symm hy w w')
  have hcont : ContinuousAt (mu A B) x := (h.hasFDerivAt_mu' hx).continuousAt
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.continuousAt_iff.1 hcont ρ hρ
  obtain ⟨ε₂, hε₂, hε₂R⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, σ ∘ mu A B, fun y hy => ?_⟩
  have hyR : y ∈ R := hε₂R (ball_subset_ball (min_le_right _ _) hy)
  have hyb : mu A B y ∈ ball (mu A B x) ρ :=
    hε₁' (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))
  have := (hσ _ hyb).comp y (h.hasFDerivAt_mu' hyR)
  have e : h.theta (mu A B y) = toCov d (Yt A B y) := by simp [PairHyp.theta, h.nu_mu hyR]
  rw [PairHyp.beta, (h.hasFDerivAt_mu' hyR).fderiv, ← e]
  exact this

/-- The primitive S of β on R' (Goursat). -/
theorem exists_S (h : PairHyp A B R r) : ∃ S : X d → ℝ, ∀ x ∈ R, HasFDerivAt S (h.beta x) x :=
  exists_primitive_of_locallyExact h.convex h.isOpen h.continuousOn_beta h.locallyExact_beta

/-- The generating function s = S ∘ ν on W. -/
def S (h : PairHyp A B R r) : X d → ℝ := Classical.choose h.exists_S

theorem hasFDerivAt_S (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) : HasFDerivAt h.S (h.beta x) x :=
  Classical.choose_spec h.exists_S x hx

def s (h : PairHyp A B R r) : X d → ℝ := h.S ∘ h.nu

theorem hasFDerivAt_s (h : PairHyp A B R r) {z : X d} (hz : z ∈ h.W) :
    HasFDerivAt h.s (h.theta z) z := by
  obtain ⟨x, hx, rfl⟩ := hz
  have hS' : HasFDerivAt h.S (h.beta x) (h.nu (mu A B x)) := by
    rw [h.nu_mu hx]; exact h.hasFDerivAt_S hx
  have hc := hS'.comp (mu A B x) (h.hasFDerivAt_nu hx)
  have e : (h.beta x).comp ((h.eq x).symm : X d →L[ℝ] X d) = h.theta (mu A B x) := by
    refine ContinuousLinearMap.ext fun w => ?_
    have h1 : fderiv ℝ (mu A B) x ((h.eq x).symm w) = w := by
      rw [(h.hasFDerivAt_mu' hx).fderiv, ← h.eq_coe hx]; simp
    simp only [PairHyp.beta, PairHyp.theta, h.nu_mu hx, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearEquiv.coe_coe, h1]
  rw [← e]; exact hc

theorem fderiv_s (h : PairHyp A B R r) {z : X d} (hz : z ∈ h.W) : fderiv ℝ h.s z = h.theta z := (h.hasFDerivAt_s hz).fderiv

theorem contDiffOn_s (h : PairHyp A B R r) : ContDiffOn ℝ (r + 1 : ℕ) h.s h.W := by
  rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen h.isOpen_W]
  refine ⟨fun z hz => (h.hasFDerivAt_s hz).differentiableAt.differentiableWithinAt,
    fun hω => absurd hω (by simp), ?_⟩
  refine (contDiffOn_congr fun z hz => h.fderiv_s hz).2 ?_
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hY : ContDiffAt ℝ r (Yt A B) (h.nu (mu A B x)) := by
    rw [h.nu_mu hx]; exact h.contDiffOn_Yt.contDiffAt (h.isOpen.mem_nhds hx)
  exact ((toCov d).contDiff.contDiffAt.comp _ (hY.comp _ (h.contDiffAt_nu hx))).contDiffWithinAt

theorem gradP_s (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) : gradP h.s (mu A B x) = (B x).2 - (A x).2 := by
  rw [gradP, h.fderiv_s ⟨x, hx, rfl⟩, PairHyp.theta, clmP_toCov, h.nu_mu hx]; rfl

theorem gradQ_s (h : PairHyp A B R r) {x : X d} (hx : x ∈ R) : gradQ h.s (mu A B x) = (A x).1 - (B x).1 := by
  rw [gradQ, h.fderiv_s ⟨x, hx, rfl⟩, PairHyp.theta, clmQ_toCov, h.nu_mu hx]; rfl

end PairHyp

/-- The key identity: if ∇s agrees with the pair gradient at μ x, then Ψ₁(μ x) = A x and
Ψ₂(μ x) = B x. -/
theorem psi_mu_of_grad {A B : X d → X d} {s : X d → ℝ} {x : X d}
    (hP : gradP s (mu A B x) = (B x).2 - (A x).2) (hQ : gradQ s (mu A B x) = (A x).1 - (B x).1) :
    psi1 s (mu A B x) = A x ∧ psi2 s (mu A B x) = B x := by
  constructor
  · rw [psi1, hQ]; ext <;> simp [mu]
  · rw [psi2, hP]; ext <;> simp [mu]

end SympNet
