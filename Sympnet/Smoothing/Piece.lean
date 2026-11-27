/-
  C9a: one step of the exact Alexander scheme.

  Given symplectic C^r maps A, B on a convex open set R' with uniform constants for A (lower
  bound c, derivative bound M, modulus of continuity of DA, ...) there is κ > 0 depending only on
  these constants such that if B is κ-close to A in C¹ on R', then there is a C^{r+1} generating
  function s̃ with compact support and ‖D²s̃‖ ≤ 1/2 whose map Φ = genMap s̃ satisfies
  Φ (A x) = B x for all x ∈ R0.
-/
import Sympnet.Smoothing.PairGenFun
import Sympnet.Smoothing.Cutoff
import Sympnet.Smoothing.GenFunCont
import Sympnet.Smoothing.Alexander

open Set Filter Topology Metric
open scoped ContDiff NNReal

noncomputable section

namespace SympNet

variable {d : ℕ}

/-! ### Elementary norm bounds -/

theorem norm_dmu_sub_apply_le (DA DB : X d →L[ℝ] X d) (w : X d) :
    ‖dmu DA DB w - DA w‖ ≤ ‖(DB - DA) w‖ := by
  have : dmu DA DB w - DA w = (((DB - DA) w).1, 0) := by
    ext <;> simp [dmu]
  rw [this, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
  exact norm_fst_le _

theorem norm_dmu_sub_le (DA DB : X d →L[ℝ] X d) : ‖dmu DA DB - DA‖ ≤ ‖DB - DA‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w =>
    (norm_dmu_sub_apply_le DA DB w).trans ((DB - DA).le_opNorm w)

theorem norm_dYt_le (DA DB : X d →L[ℝ] X d) : ‖dYt DA DB‖ ≤ ‖DB - DA‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => by
    have : dYt DA DB w = (((DB - DA) w).2, -((DB - DA) w).1) := by
      ext <;> simp [dYt]
    rw [this, Prod.norm_mk, norm_neg]
    refine (max_le (norm_snd_le _) (norm_fst_le _)).trans ?_
    exact (DB - DA).le_opNorm w

theorem norm_Yt_le (A B : X d → X d) (x : X d) : ‖Yt A B x‖ ≤ ‖A x - B x‖ := by
  have : Yt A B x = (-(A x - B x).2, (A x - B x).1) := by ext <;> simp [Yt]
  rw [this, Prod.norm_mk, norm_neg, max_comm, ← Prod.norm_def]

theorem norm_mu_sub_le (A B : X d → X d) (x : X d) : ‖mu A B x - A x‖ ≤ ‖A x - B x‖ := by
  have : mu A B x - A x = (-(A x - B x).1, 0) := by ext <;> simp [mu]
  rw [this, Prod.norm_mk, norm_zero, norm_neg, max_eq_left (norm_nonneg _)]
  exact norm_fst_le _

theorem norm_symm_le_of_lower_bound {e : X d ≃L[ℝ] X d} {a : ℝ} (ha : 0 < a)
    (he : ∀ v, a * ‖v‖ ≤ ‖e v‖) : ‖(e.symm : X d →L[ℝ] X d)‖ ≤ a⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => by
    have := he (e.symm w)
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    rw [ContinuousLinearEquiv.coe_coe, inv_mul_eq_div, le_div_iff₀ ha]
    linarith

/-! ### The step -/

theorem exists_piece (r : ℕ) (hr : 1 ≤ r) {c γ M Rd : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    (hM : 0 ≤ M) (hRd : 0 ≤ Rd) :
    ∃ κ > 0, ∀ (A B : X d → X d) (R0 R' : Set (X d)) (x0 : X d) (MA : ℝ),
      IsOpen R' → Convex ℝ R' → x0 ∈ R0 → R0 ⊆ R' → (∀ x ∈ R0, ball x γ ⊆ R') →
      ContDiffOn ℝ r A R' → ContDiffOn ℝ r B R' →
      (∀ x ∈ R', IsSymplecticAt A x) → (∀ x ∈ R', IsSymplecticAt B x) →
      (∀ x ∈ R', ∀ y ∈ R', c * ‖x - y‖ ≤ ‖A x - A y‖) →
      (∀ x ∈ R', ∀ v, c * ‖v‖ ≤ ‖fderiv ℝ A x v‖) →
      (∀ x ∈ R', ‖fderiv ℝ A x‖ ≤ M) →
      (∀ x ∈ R0, ∀ y ∈ ball x γ, ‖fderiv ℝ A y - fderiv ℝ A x‖ ≤ c / 16) →
      (∀ x ∈ R', ‖x - x0‖ ≤ Rd) → (∀ x ∈ R0, ‖A x‖ ≤ MA) →
      (∀ x ∈ R', ‖fderiv ℝ B x - fderiv ℝ A x‖ ≤ κ) → (∀ x ∈ R', ‖A x - B x‖ ≤ κ) →
      ∃ (s : X d → ℝ) (h : GFHyp s), ContDiff ℝ (r + 1 : ℕ) s ∧ HasCompactSupport s ∧
        (∀ z, ‖hess s z‖ ≤ 1 / 2) ∧ ∀ x ∈ R0, genMap h (A x) = B x := by
  set ρ := c * γ / 8 with hρdef
  have hρ : 0 < ρ := by positivity
  obtain ⟨Mχ, hMχ⟩ := exists_cutoff (d := d) hρ
  set Mχ' := max Mχ 0
  set Cc := ‖toCov d‖
  set K := (Mχ' + 1) * (Cc + 1) * ((M + c) * Rd + 2 + 2 / c) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min (c / 16) (1 / (4 * K)), lt_min (by positivity) (by positivity), ?_⟩
  intro A B R0 R' x0 MA hR'o hR'c hx0 hR0 hball hA hB hsA hsB hantA hlowA hMA hmod hRd' hAb
    hDBA hAB
  set κ := min (c / 16) (1 / (4 * K))
  have hκc : κ ≤ c / 16 := min_le_left _ _
  have hκK : κ ≤ 1 / (4 * K) := min_le_right _ _
  have hκ0 : 0 < κ := lt_min (by positivity) (by positivity)
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hdA : ∀ x ∈ R', HasFDerivAt A (fderiv ℝ A x) x := fun x hx =>
    ((hA.contDiffAt (hR'o.mem_nhds hx)).differentiableAt hr0).hasFDerivAt
  have hdB : ∀ x ∈ R', HasFDerivAt B (fderiv ℝ B x) x := fun x hx =>
    ((hB.contDiffAt (hR'o.mem_nhds hx)).differentiableAt hr0).hasFDerivAt
  -- derivative of μ, and its lower bound
  have hdmu_low : ∀ x ∈ R', ∀ v, c / 2 * ‖v‖ ≤ ‖dmu (fderiv ℝ A x) (fderiv ℝ B x) v‖ := by
    intro x hx v
    have h1 := hlowA x hx v
    have h2 := norm_dmu_sub_apply_le (fderiv ℝ A x) (fderiv ℝ B x) v
    have h3 : ‖(fderiv ℝ B x - fderiv ℝ A x) v‖ ≤ c / 16 * ‖v‖ :=
      ((fderiv ℝ B x - fderiv ℝ A x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ((hDBA x hx).trans hκc) (norm_nonneg _))
    have h4 : ‖fderiv ℝ A x v‖ ≤ ‖dmu (fderiv ℝ A x) (fderiv ℝ B x) v‖ +
        ‖dmu (fderiv ℝ A x) (fderiv ℝ B x) v - fderiv ℝ A x v‖ := by
      calc ‖fderiv ℝ A x v‖ = ‖dmu (fderiv ℝ A x) (fderiv ℝ B x) v -
            (dmu (fderiv ℝ A x) (fderiv ℝ B x) v - fderiv ℝ A x v)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have h5 : ‖(fderiv ℝ B x - fderiv ℝ A x) v‖ = ‖fderiv ℝ B x v - fderiv ℝ A x v‖ := by
      rw [ContinuousLinearMap.sub_apply]
    linarith [mul_nonneg hc.le (norm_nonneg v)]
  -- μ is injective on R'
  have hE : ∀ x ∈ R', ‖mu A B x - A x - (mu A B x - A x)‖ = 0 := fun _ _ => by simp
  have hinj : InjOn (mu A B) R' := by
    intro x hx y hy hxy
    have hEd : ∀ z ∈ R', HasFDerivWithinAt (fun z => mu A B z - A z)
        (dmu (fderiv ℝ A z) (fderiv ℝ B z) - fderiv ℝ A z) R' z := fun z hz =>
      ((hasFDerivAt_mu (hdA z hz) (hdB z hz)).sub (hdA z hz)).hasFDerivWithinAt
    have hEb : ∀ z ∈ R', ‖dmu (fderiv ℝ A z) (fderiv ℝ B z) - fderiv ℝ A z‖ ≤ c / 16 :=
      fun z hz => (norm_dmu_sub_le _ _).trans ((hDBA z hz).trans hκc)
    have hmv := hR'c.norm_image_sub_le_of_norm_hasFDerivWithin_le hEd hEb hy hx
    have hcx := hantA x hx y hy
    have : A x - A y = -((mu A B x - A x) - (mu A B y - A y)) := by rw [hxy]; abel
    rw [this, norm_neg] at hcx
    have h0 : ‖x - y‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith [mul_pos hc hpos]
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  -- the pair hypotheses
  have hP : PairHyp A B R' r := by
    refine ⟨hR'o, hR'c, hr, hA, hB, hsA, hsB, hinj, fun x hx => ?_⟩
    obtain ⟨e, he, -⟩ := exists_equiv_of_lower_bound (half_pos hc) (hdmu_low x hx)
    exact ⟨e, he⟩
  have heq_low : ∀ x ∈ R', ∀ v, c / 2 * ‖v‖ ≤ ‖hP.eq x v‖ := fun x hx v => by
    have := hdmu_low x hx v
    rwa [← hP.eq_coe hx, ContinuousLinearEquiv.coe_coe] at this
  have heq_symm : ∀ x ∈ R', ‖((hP.eq x).symm : X d →L[ℝ] X d)‖ ≤ 2 / c := fun x hx => by
    have := norm_symm_le_of_lower_bound (half_pos hc) (heq_low x hx)
    rwa [inv_div] at this
  set W := hP.W
  set s := hP.s
  -- gap: balls of radius ρ around μ(R0) lie in W
  have hgap : ∀ x ∈ R0, ball (mu A B x) ρ ⊆ W := by
    intro x hx
    have hxR : x ∈ R' := hR0 hx
    set L := dmu (fderiv ℝ A x) (fderiv ℝ B x)
    obtain ⟨e, he, hes⟩ := exists_equiv_of_lower_bound (half_pos hc) (hdmu_low x hxR)
    set n2 : ℝ≥0 := ⟨2 / c, by positivity⟩
    have hn2 : (n2 : ℝ) = 2 / c := rfl
    let Ls : L.NonlinearRightInverse :=
      { toFun := e.symm
        nnNorm := n2
        bound' := fun w => by
          rw [hn2]; have := hes w; rwa [inv_div] at this
        right_inv' := fun w => by
          have h1 : (e : X d →L[ℝ] X d) (e.symm w) = w := by simp
          rw [he] at h1; exact h1 }
    have hcb : closedBall x (γ / 2) ⊆ R' :=
      (closedBall_subset_ball (half_lt_self hγ)).trans (hball x hx)
    set c4 : ℝ≥0 := ⟨c / 4, by positivity⟩
    have hc4 : (c4 : ℝ) = c / 4 := rfl
    have happrox : ApproximatesLinearOn (mu A B) L (closedBall x (γ / 2)) c4 := by
      intro y hy y' hy'
      have hder : ∀ z ∈ closedBall x (γ / 2), HasFDerivWithinAt (fun z => mu A B z - L z)
          (dmu (fderiv ℝ A z) (fderiv ℝ B z) - L) (closedBall x (γ / 2)) z := fun z hz =>
        ((hasFDerivAt_mu (hdA z (hcb hz)) (hdB z (hcb hz))).sub L.hasFDerivAt).hasFDerivWithinAt
      have hbd : ∀ z ∈ closedBall x (γ / 2), ‖dmu (fderiv ℝ A z) (fderiv ℝ B z) - L‖ ≤ c / 4 := by
        intro z hz
        have hzR := hcb hz
        have hzb : z ∈ ball x γ := closedBall_subset_ball (half_lt_self hγ) hz
        have e1 : dmu (fderiv ℝ A z) (fderiv ℝ B z) - L =
            (dmu (fderiv ℝ A z) (fderiv ℝ B z) - fderiv ℝ A z) +
            (fderiv ℝ A z - fderiv ℝ A x) - (L - fderiv ℝ A x) := by abel
        rw [e1]
        have t1 := (norm_dmu_sub_le (fderiv ℝ A z) (fderiv ℝ B z)).trans ((hDBA z hzR).trans hκc)
        have t2 := hmod x hx z hzb
        have t3 : ‖L - fderiv ℝ A x‖ ≤ c / 16 :=
          (norm_dmu_sub_le (fderiv ℝ A x) (fderiv ℝ B x)).trans ((hDBA x hxR).trans hκc)
        calc _ ≤ ‖dmu (fderiv ℝ A z) (fderiv ℝ B z) - fderiv ℝ A z +
              (fderiv ℝ A z - fderiv ℝ A x)‖ + ‖L - fderiv ℝ A x‖ := norm_sub_le _ _
          _ ≤ ‖dmu (fderiv ℝ A z) (fderiv ℝ B z) - fderiv ℝ A z‖ +
              ‖fderiv ℝ A z - fderiv ℝ A x‖ + ‖L - fderiv ℝ A x‖ := by
              gcongr; exact norm_add_le _ _
          _ ≤ c / 4 := by linarith
      have hmv := (convex_closedBall x (γ / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        hder hbd hy' hy
      rw [hc4]
      have e2 : mu A B y - mu A B y' - L (y - y') = (mu A B y - L y) - (mu A B y' - L y') := by
        rw [map_sub]; abel
      rw [e2]; exact hmv
    have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse Ls (by positivity) le_rfl
    intro w hw
    have hw' : w ∈ closedBall (mu A B x) (((Ls.nnNorm : ℝ)⁻¹ - (c4 : ℝ)) * (γ / 2)) := by
      show w ∈ closedBall (mu A B x) (((n2 : ℝ)⁻¹ - (c4 : ℝ)) * (γ / 2))
      rw [hc4, hn2, inv_div]
      rw [mem_closedBall]
      have := mem_ball.1 hw
      have hcalc : (c / 2 - c / 4) * (γ / 2) = ρ := by rw [hρdef]; ring
      linarith
    obtain ⟨y, hy, rfl⟩ := hsurj hw'
    exact ⟨y, hcb hy, rfl⟩
  -- the cutoff
  obtain ⟨χ, hχs, hχ1, hχsupp, hχb⟩ := hMχ (mu A B '' R0)
  have hχb' : ∀ z, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j χ z‖ ≤ Mχ' := fun z j hj =>
    (hχb z j hj).trans (le_max_left _ _)
  have hthickW : thickening ρ (mu A B '' R0) ⊆ W := by
    intro z hz
    obtain ⟨y, ⟨x, hx, rfl⟩, hzy⟩ := mem_thickening_iff.1 hz
    exact hgap x hx (mem_ball.2 hzy)
  have htsupp : tsupport χ ⊆ cthickening (3 * ρ / 4) (mu A B '' R0) :=
    (closure_mono hχsupp).trans (closure_thickening_subset_cthickening _ _)
  have htsuppW : tsupport χ ⊆ W :=
    htsupp.trans ((cthickening_subset_thickening' hρ (by linarith) _).trans hthickW)
  have hTb : Bornology.IsBounded (mu A B '' R0) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨MA + κ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h1 := norm_mu_sub_le A B x
    have h2 := hAB x (hR0 hx)
    have h3 := hAb x hx
    have := norm_le_insert' (mu A B x) (A x)
    linarith [norm_sub_norm_le (mu A B x) (A x)]
  have hχc : HasCompactSupport χ :=
    (isCompact_of_isClosed_isBounded isClosed_cthickening hTb.cthickening).of_isClosed_subset
      (isClosed_tsupport χ) htsupp
  -- the normalized generating function and the cut-off one
  set s₀ : X d → ℝ := fun z => s z - s (mu A B x0)
  set st : X d → ℝ := fun z => χ z * s₀ z
  have hWo : IsOpen W := hP.isOpen_W
  have hs₀ : ContDiffOn ℝ (r + 1 : ℕ) s₀ W := hP.contDiffOn_s.sub contDiffOn_const
  have hzero : ∀ z ∉ W, st =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    have : z ∉ tsupport χ := fun h => hz (htsuppW h)
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 this)] with y hy
    simp [st, hy]
  have hst : ContDiff ℝ (r + 1 : ℕ) st := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ W
    · exact (hχs.of_le (by exact_mod_cast le_top)).contDiffAt.mul
        (hs₀.contDiffAt (hWo.mem_nhds hz))
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero z hz)
  have hstc : HasCompactSupport st := hχc.mul_right
  -- bounds on s on W
  have hDs : ∀ z ∈ W, ‖fderiv ℝ s z‖ ≤ Cc * κ := by
    intro z hz
    rw [hP.fderiv_s hz, PairHyp.theta]
    have hx := hP.nu_mem hz
    calc ‖toCov d (Yt A B (hP.nu z))‖ ≤ Cc * ‖Yt A B (hP.nu z)‖ := (toCov d).le_opNorm _
      _ ≤ Cc * κ := by
          gcongr; exact (norm_Yt_le A B _).trans (hAB _ hx)
  have hD2s : ∀ z ∈ W, ‖hess s z‖ ≤ Cc * κ * (2 / c) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hev : fderiv ℝ s =ᶠ[𝓝 (mu A B x)] hP.theta := by
      filter_upwards [hWo.mem_nhds ⟨x, hx, rfl⟩] with y hy using hP.fderiv_s hy
    show ‖fderiv ℝ (fderiv ℝ s) (mu A B x)‖ ≤ _
    rw [hev.fderiv_eq, (hP.hasFDerivAt_theta hx).fderiv]
    calc _ ≤ Cc * ‖(dYt (fderiv ℝ A x) (fderiv ℝ B x)).comp
            ((hP.eq x).symm : X d →L[ℝ] X d)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Cc * (‖dYt (fderiv ℝ A x) (fderiv ℝ B x)‖ * ‖((hP.eq x).symm : X d →L[ℝ] X d)‖) := by
          gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Cc * (κ * (2 / c)) := by
          gcongr
          · exact (norm_dYt_le _ _).trans (hDBA x hx)
          · exact heq_symm x hx
      _ = Cc * κ * (2 / c) := by ring
  have hs0 : ∀ z ∈ W, |s₀ z| ≤ Cc * κ * (M + c) * Rd := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hβ : ∀ y ∈ R', ‖hP.beta y‖ ≤ Cc * κ * (M + c) := by
      intro y hy
      have hmu : ‖fderiv ℝ (mu A B) y‖ ≤ M + c := by
        rw [(hP.hasFDerivAt_mu' hy).fderiv]
        have e1 : dmu (fderiv ℝ A y) (fderiv ℝ B y) =
            (dmu (fderiv ℝ A y) (fderiv ℝ B y) - fderiv ℝ A y) + fderiv ℝ A y := by abel
        rw [e1]
        have := (norm_dmu_sub_le (fderiv ℝ A y) (fderiv ℝ B y)).trans ((hDBA y hy).trans hκc)
        linarith [norm_add_le (dmu (fderiv ℝ A y) (fderiv ℝ B y) - fderiv ℝ A y) (fderiv ℝ A y),
          hMA y hy]
      calc ‖hP.beta y‖ ≤ ‖toCov d (Yt A B y)‖ * ‖fderiv ℝ (mu A B) y‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (Cc * κ) * (M + c) := by
            gcongr
            calc ‖toCov d (Yt A B y)‖ ≤ Cc * ‖Yt A B y‖ := (toCov d).le_opNorm _
              _ ≤ Cc * κ := by gcongr; exact (norm_Yt_le A B _).trans (hAB _ hy)
        _ = Cc * κ * (M + c) := rfl
    have hmv := hR'c.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => (hP.hasFDerivAt_S hy).hasFDerivWithinAt) hβ (hR0 hx0) hx
    have e : s₀ (mu A B x) = hP.S x - hP.S x0 := by
      simp only [s₀, s, PairHyp.s, Function.comp_apply, hP.nu_mu hx, hP.nu_mu (hR0 hx0)]
    rw [e, ← Real.norm_eq_abs]
    calc _ ≤ Cc * κ * (M + c) * ‖x - x0‖ := hmv
      _ ≤ Cc * κ * (M + c) * Rd := by gcongr; exact hRd' x hx
  -- the Hessian bound for the cut-off function
  have hhess : ∀ z, ‖hess st z‖ ≤ 1 / 2 := by
    intro z
    by_cases hz : z ∈ W
    · have hW2 : ((2 : ℕ) : ℕ∞ω) ≤ ((r + 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (by omega)
      have hprod := norm_iteratedFDerivWithin_mul_le (n := 2)
        ((hχs.of_le (by exact_mod_cast le_top)).contDiffOn (s := W)) hs₀ hWo.uniqueDiffOn hz hW2
      have hconv : ∀ (g : X d → ℝ) (n : ℕ),
          iteratedFDerivWithin ℝ n g W z = iteratedFDeriv ℝ n g z :=
        fun g n => iteratedFDerivWithin_of_isOpen n hWo hz
      simp only [hconv] at hprod
      have e2 : ∀ g : X d → ℝ, ‖iteratedFDeriv ℝ 2 g z‖ = ‖hess g z‖ := fun g => by
        rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
      have hs₀1 : fderiv ℝ s₀ z = fderiv ℝ s z := by
        simp [s₀, fderiv_sub_const]
      have hs₀2 : hess s₀ z = hess s z := by
        show fderiv ℝ (fderiv ℝ s₀) z = fderiv ℝ (fderiv ℝ s) z
        congr 1; funext y; simp [s₀, fderiv_sub_const]
      have q0 : ∀ g : X d → ℝ, ‖iteratedFDeriv ℝ 0 g z‖ = ‖g z‖ := fun g => norm_iteratedFDeriv_zero
      have q1 : ∀ g : X d → ℝ, ‖iteratedFDeriv ℝ 1 g z‖ = ‖fderiv ℝ g z‖ :=
        fun g => norm_iteratedFDeriv_one g
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, q0, q1,
        e2, Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.cast_ofNat, hs₀1, hs₀2] at hprod
      have b0 : ‖χ z‖ ≤ Mχ' := by
        have := hχb' z 0 (by norm_num); rwa [norm_iteratedFDeriv_zero] at this
      have b1 : ‖fderiv ℝ χ z‖ ≤ Mχ' := by
        have := hχb' z 1 (by norm_num); rwa [norm_iteratedFDeriv_one] at this
      have b2 : ‖hess χ z‖ ≤ Mχ' := by rw [← e2]; exact hχb' z 2 le_rfl
      have c0 : ‖s₀ z‖ ≤ Cc * κ * (M + c) * Rd := by rw [Real.norm_eq_abs]; exact hs0 z hz
      have c1 := hDs z hz
      have c2 := hD2s z hz
      have hMχ0 : 0 ≤ Mχ' := le_max_right _ _
      have hCc : 0 ≤ Cc := norm_nonneg (toCov d)
      have hbound : Mχ' * (Cc * κ * (2 / c)) + 2 * (Mχ' * (Cc * κ)) +
          Mχ' * (Cc * κ * (M + c) * Rd) ≤ 1 / 2 := by
        have : Mχ' * (Cc * κ * (2 / c)) + 2 * (Mχ' * (Cc * κ)) + Mχ' * (Cc * κ * (M + c) * Rd)
            ≤ κ * K := by
          rw [hK]
          have hc2 : 0 ≤ 2 / c := by positivity
          nlinarith [mul_nonneg hMχ0 hCc, mul_nonneg (mul_nonneg hMχ0 hCc) hκ0.le,
            mul_nonneg (mul_nonneg (mul_nonneg hMχ0 hCc) hκ0.le) hc2,
            mul_nonneg (mul_nonneg (mul_nonneg hMχ0 hCc) hκ0.le) (by positivity : 0 ≤ (M + c) * Rd)]
        have h2 : κ * K ≤ 1 / 4 := by
          calc κ * K ≤ 1 / (4 * K) * K := by gcongr
            _ = 1 / 4 := by field_simp
        linarith
      calc ‖hess st z‖ ≤ ‖χ z‖ * ‖hess s z‖ + 2 * ‖fderiv ℝ χ z‖ * ‖fderiv ℝ s z‖ +
            ‖hess χ z‖ * ‖s₀ z‖ := by
            linarith
        _ ≤ Mχ' * (Cc * κ * (2 / c)) + 2 * (Mχ' * (Cc * κ)) +
            Mχ' * (Cc * κ * (M + c) * Rd) := by
            have t0 := mul_le_mul b0 c2 (norm_nonneg (hess s z)) hMχ0
            have t1 := mul_le_mul b1 c1 (norm_nonneg (fderiv ℝ s z)) hMχ0
            have t2 := mul_le_mul b2 c0 (norm_nonneg (s₀ z)) hMχ0
            linarith
        _ ≤ 1 / 2 := hbound
    · have h1 : fderiv ℝ st =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [(hzero z hz).eventuallyEq_nhds] with y hy
        rw [hy.fderiv_eq]; simp
      show ‖fderiv ℝ (fderiv ℝ st) z‖ ≤ 1 / 2
      rw [h1.fderiv_eq, fderiv_const_apply, ContinuousLinearMap.opNorm_zero]; norm_num
  have hG : GFHyp st := GFHyp.of_hess (hst.of_le (by exact_mod_cast (by omega : 2 ≤ r + 1)))
    hhess
  refine ⟨st, hG, hst, hstc, hhess, fun x hx => ?_⟩
  -- agreement
  have hxR := hR0 hx
  have hμW : mu A B x ∈ W := ⟨x, hxR, rfl⟩
  have hnear : st =ᶠ[𝓝 (mu A B x)] s₀ := by
    have hmem : thickening (ρ / 4) (mu A B '' R0) ∈ 𝓝 (mu A B x) :=
      isOpen_thickening.mem_nhds (self_subset_thickening (by positivity) _ ⟨x, hx, rfl⟩)
    filter_upwards [hmem] with y hy
    simp [st, hχ1 y hy]
  have hfd : fderiv ℝ st (mu A B x) = fderiv ℝ s (mu A B x) := by
    rw [hnear.fderiv_eq]; simp [s₀, fderiv_sub_const]
  have hP' : gradP st (mu A B x) = (B x).2 - (A x).2 := by
    rw [gradP, hfd]; exact hP.gradP_s hxR
  have hQ' : gradQ st (mu A B x) = (A x).1 - (B x).1 := by
    rw [gradQ, hfd]; exact hP.gradQ_s hxR
  obtain ⟨h1, h2⟩ := psi_mu_of_grad hP' hQ'
  rw [← h1, genMap_psi1, h2]

end SympNet
