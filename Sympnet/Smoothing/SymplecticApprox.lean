/-
  C9b: assembly. Every C^r symplectic map that is injective on a convex open set U is
  C^r-approximated on compact subsets of U by smooth symplectic diffeomorphisms of ℝ^{2d}.

  Proof: Alexander family F_t (F_0 affine, F_1 = F), cut [0,1] into N pieces; each step
  F_{t_i} ↦ F_{t_{i+1}} is realised exactly near K by a global generating-function map Φ_i
  (`exists_piece`); then smooth every Φ_i (`exists_smooth_genMap_close`) and use `comp_stable`.
-/
import Sympnet.Smoothing.Piece
import Sympnet.TuraevReduction

open Set Filter Topology Metric
open scoped ContDiff NNReal

noncomputable section

namespace SympNet

variable {d : ℕ}

/-! ### Inner parallel sets of a convex open set -/

/-- `{x | some closed ball of radius > δ around x lies in U}`. -/
def innerSet (U : Set (X d)) (δ : ℝ) : Set (X d) := {x | ∃ δ' > δ, closedBall x δ' ⊆ U}

theorem isOpen_innerSet (U : Set (X d)) (δ : ℝ) : IsOpen (innerSet U δ) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨δ', hδ', hsub⟩
  refine ⟨(δ' - δ) / 2, by linarith, fun y hy => ⟨(δ' + δ) / 2, by linarith, ?_⟩⟩
  intro z hz
  apply hsub
  rw [mem_closedBall] at hz ⊢
  rw [mem_ball] at hy
  linarith [dist_triangle z y x]

theorem convex_innerSet {U : Set (X d)} (hU : Convex ℝ U) (δ : ℝ) : Convex ℝ (innerSet U δ) := by
  rintro x ⟨δx, hδx, hx⟩ y ⟨δy, hδy, hy⟩ a b ha hb hab
  refine ⟨min δx δy, lt_min hδx hδy, fun w hw => ?_⟩
  set z := a • x + b • y
  have hwz : w = a • (x + (w - z)) + b • (y + (w - z)) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]; simp [z]
  rw [hwz]
  have hd : ‖w - z‖ ≤ min δx δy := by rw [← dist_eq_norm]; exact hw
  refine hU (hx ?_) (hy ?_) ha hb hab
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hd.trans (min_le_left _ _)
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hd.trans (min_le_right _ _)

theorem innerSet_subset {U : Set (X d)} {δ : ℝ} (hδ : 0 ≤ δ) : innerSet U δ ⊆ U :=
  fun _ ⟨_, hδ', h⟩ => h (mem_closedBall_self (by linarith))

theorem innerSet_anti {U : Set (X d)} {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) : innerSet U δ₂ ⊆ innerSet U δ₁ :=
  fun _ ⟨δ', hδ', hs⟩ => ⟨δ', by linarith, hs⟩

theorem ball_subset_innerSet {U : Set (X d)} {δ γ : ℝ} {x : X d} (hx : x ∈ innerSet U (δ + γ)) :
    ball x γ ⊆ innerSet U δ := by
  obtain ⟨δ', hδ', hs⟩ := hx
  intro y hy
  refine ⟨δ' - dist y x, by rw [mem_ball] at hy; linarith, fun z hz => hs ?_⟩
  rw [mem_closedBall] at hz ⊢
  linarith [dist_triangle z y x]

theorem closure_innerSet_subset {U : Set (X d)} {δ : ℝ} (hδ : 0 < δ) :
    closure (innerSet U δ) ⊆ U := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx δ hδ
  obtain ⟨δ', hδ', hs⟩ := hy
  exact hs (by rw [mem_closedBall]; linarith)

/-! ### The Alexander family -/

/-- F_t(x) = F x0 + (F(x0 + t(x − x0)) − F x0)/t, and F_0 = the affine part at x0. -/
def alex (F : X d → X d) (x0 : X d) (t : ℝ) (x : X d) : X d :=
  if t = 0 then F x0 + fderiv ℝ F x0 (x - x0) else F x0 + t⁻¹ • (F (x0 + t • (x - x0)) - F x0)

theorem alex_x0 (F : X d → X d) (x0 : X d) (t : ℝ) : alex F x0 t x0 = F x0 := by
  unfold alex; split_ifs <;> simp

theorem alex_one (F : X d → X d) (x0 x : X d) : alex F x0 1 x = F x := by
  simp [alex]

theorem alex_zero (F : X d → X d) (x0 : X d) :
    alex F x0 0 = fun x => F x0 + fderiv ℝ F x0 (x - x0) := by
  funext x; simp [alex]

theorem hasFDerivAt_alex {F : X d → X d} {x0 x : X d} {t : ℝ}
    (hF : HasFDerivAt F (fderiv ℝ F (x0 + t • (x - x0))) (x0 + t • (x - x0))) :
    HasFDerivAt (alex F x0 t) (fderiv ℝ F (x0 + t • (x - x0))) x := by
  by_cases ht : t = 0
  · subst ht
    rw [alex_zero, zero_smul ℝ (x - x0), add_zero]
    have h1 : HasFDerivAt (fun y => F x0 + fderiv ℝ F x0 (y - x0))
        ((fderiv ℝ F x0).comp (ContinuousLinearMap.id ℝ (X d))) x :=
      ((fderiv ℝ F x0).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x0)).const_add (F x0)
    exact h1.congr_fderiv (ContinuousLinearMap.ext fun v => by simp)
  · have hin : HasFDerivAt (fun x => x0 + t • (x - x0))
        (t • ContinuousLinearMap.id ℝ (X d)) x := by
      have h0 : HasFDerivAt (fun y : X d => y - x0) (ContinuousLinearMap.id ℝ (X d)) x :=
        (hasFDerivAt_id x).sub_const x0
      exact (h0.const_smul t).const_add x0
    have h : HasFDerivAt (fun y => F x0 + t⁻¹ • (F (x0 + t • (y - x0)) - F x0))
        (t⁻¹ • ((fderiv ℝ F (x0 + t • (x - x0))).comp (t • ContinuousLinearMap.id ℝ (X d)))) x :=
      (((hF.comp x hin).sub_const (F x0)).const_smul t⁻¹).const_add (F x0)
    have e : alex F x0 t = fun x => F x0 + t⁻¹ • (F (x0 + t • (x - x0)) - F x0) := by
      funext y; simp [alex, ht]
    rw [e]
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [smul_smul, inv_mul_cancel₀ ht]

theorem contDiffOn_alex {F : X d → X d} {U S : Set (X d)} {r : ℕ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ r F U) {x0 : X d} {t : ℝ} (hS : ∀ x ∈ S, x0 + t • (x - x0) ∈ U) :
    ContDiffOn ℝ r (alex F x0 t) S := by
  by_cases ht : t = 0
  · subst ht
    rw [alex_zero]
    exact (contDiff_const.add ((fderiv ℝ F x0).contDiff.comp
      (contDiff_id.sub contDiff_const))).contDiffOn
  · have e : alex F x0 t = fun x => F x0 + t⁻¹ • (F (x0 + t • (x - x0)) - F x0) := by
      funext y; simp [alex, ht]
    rw [e]
    have hin : ContDiff ℝ r (fun x : X d => x0 + t • (x - x0)) := by fun_prop
    exact contDiffOn_const.add (((hF.comp hin.contDiffOn hS).sub contDiffOn_const).const_smul _)

theorem alexPt_mem {S : Set (X d)} (hS : Convex ℝ S) {x0 x : X d} (hx0 : x0 ∈ S) (hx : x ∈ S)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : x0 + t • (x - x0) ∈ S :=
  hS.add_smul_sub_mem hx0 hx ht

/-! ### Compositions -/

theorem bijective_compList {α : Type*} (l : List (α → α)) (h : ∀ f ∈ l, Function.Bijective f) :
    Function.Bijective (compList l) := by
  induction l with
  | nil => exact Function.bijective_id
  | cons f fs ih =>
    exact (ih fun g hg => h g (List.mem_cons_of_mem _ hg)).comp (h f List.mem_cons_self)

theorem bijective_affine {L : X d →L[ℝ] X d} (hL : Function.Injective L) (a x0 : X d) :
    Function.Bijective (fun x => a + L (x - x0)) := by
  have hs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective (f := L.toLinearMap)).1 hL
  refine ⟨fun x y h => ?_, fun z => ?_⟩
  · have : L (x - x0) = L (y - x0) := add_left_cancel h
    exact sub_left_injective (hL this)
  · obtain ⟨w, hw⟩ := hs (z - a)
    exact ⟨w + x0, by simp [hw]⟩

/-! ### The main approximation theorem -/

/-- Smooth global symplectic diffeomorphisms approximate injective symplectic maps on convex
sets. -/
def SymplecticApprox : Prop :=
  ∀ (m r : ℕ), 1 ≤ r → ∀ U : Set (X m), IsOpen U → Convex ℝ U →
    ∀ F ∈ SP r U, Set.InjOn F U → ∀ K : Set (X m), IsCompact K → K ⊆ U → ∀ ε > 0,
      ∃ G ∈ SympDiffeo m, CrClose r K F G ε

theorem symplecticApprox : SymplecticApprox := by
  intro m r hr U hU hUc F hF hinj K hK hKU ε hε
  -- trivial case
  rcases K.eq_empty_or_nonempty with rfl | ⟨x0, hx0K⟩
  · refine ⟨id, ⟨contDiff_id, Function.bijective_id, fun x v w => by simp [fderiv_id]⟩,
      fun k _ x hx => hx.elim⟩
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hFU : ContDiffOn ℝ r F U := hF.1
  have hFs : ∀ y ∈ U, IsSymplecticAt F y := hF.2
  have hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℝ F y) y := fun y hy =>
    ((hFU.contDiffAt (hU.mem_nhds hy)).differentiableAt hr0).hasFDerivAt
  have hDFinj : ∀ y ∈ U, Function.Injective (fderiv ℝ F y) := fun y hy =>
    injective_of_symplectic (hFs y hy)
  have hDFc : ContinuousOn (fderiv ℝ F) U :=
    hFU.continuousOn_fderiv_of_isOpen hU (by exact_mod_cast hr)
  -- convex neighbourhoods
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  set γ := δ / 8 with hγdef
  have hγ : 0 < γ := by positivity
  obtain ⟨Rk, hRk⟩ := hK.isBounded.exists_norm_le
  set R0 := innerSet U (4 * γ) ∩ ball 0 (Rk + 1)
  set R' := innerSet U (2 * γ) ∩ ball 0 (Rk + 1 + γ)
  set D := closure R'
  have hR0o : IsOpen R0 := (isOpen_innerSet _ _).inter isOpen_ball
  have hR'o : IsOpen R' := (isOpen_innerSet _ _).inter isOpen_ball
  have hR'c : Convex ℝ R' := (convex_innerSet hUc _).inter (convex_ball _ _)
  have hDc : Convex ℝ D := hR'c.closure
  have hDcpt : IsCompact D := by
    refine isCompact_of_isClosed_isBounded isClosed_closure ?_
    exact (isBounded_ball.subset inter_subset_right).closure
  have hDU : D ⊆ U :=
    (closure_mono inter_subset_left).trans (closure_innerSet_subset (by positivity))
  have hR'D : R' ⊆ D := subset_closure
  have hR'U : R' ⊆ U := hR'D.trans hDU
  have hgapR : ∀ x ∈ R0, ball x γ ⊆ R' := by
    rintro x ⟨hx1, hx2⟩ y hy
    refine ⟨innerSet_anti (show 2 * γ ≤ 3 * γ by linarith)
      (ball_subset_innerSet (by rwa [show 3 * γ + γ = 4 * γ by ring]) hy), ?_⟩
    rw [mem_ball, dist_zero_right] at hx2 ⊢
    rw [mem_ball, dist_eq_norm] at hy
    linarith [norm_sub_norm_le y x]
  have hR0R' : R0 ⊆ R' := fun x hx => hgapR x hx (mem_ball_self hγ)
  have hKR0 : K ⊆ R0 := by
    intro x hx
    refine ⟨⟨δ, by linarith, (closedBall_subset_cthickening hx δ).trans hδU⟩, ?_⟩
    rw [mem_ball, dist_zero_right]; linarith [hRk x hx]
  have hx0 : x0 ∈ R0 := hKR0 hx0K
  have hx0' : x0 ∈ R' := hR0R' hx0
  -- constants from F
  obtain ⟨c, hc, hcD⟩ := exists_antilipschitz hU hDcpt hDU (hFU.of_le (by exact_mod_cast hr))
    hinj hDFinj
  have hlow : ∀ y ∈ R', ∀ v, c * ‖v‖ ≤ ‖fderiv ℝ F y v‖ := fun y hy v =>
    lower_bound_fderiv (Filter.mem_of_superset (hR'o.mem_nhds hy) hR'D) (hFd y (hR'U hy)) hcD v
  obtain ⟨M₀, hM₀⟩ := hDcpt.exists_bound_of_continuousOn (hDFc.mono hDU)
  set M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hMb : ∀ y ∈ D, ‖fderiv ℝ F y‖ ≤ M := fun y hy => (hM₀ y hy).trans (le_max_left _ _)
  obtain ⟨Rd₀, hRd₀⟩ := (hDcpt.isBounded.sub (Bornology.isBounded_singleton (x := x0))).exists_norm_le
  set Rd := max Rd₀ 0
  have hRd : 0 ≤ Rd := le_max_right _ _
  have hRdb : ∀ x ∈ D, ‖x - x0‖ ≤ Rd := fun x hx =>
    (hRd₀ _ (Set.sub_mem_sub hx (Set.mem_singleton x0))).trans (le_max_left _ _)
  have huc := Metric.uniformContinuousOn_iff.1
    (hDcpt.uniformContinuousOn_of_continuous (hDFc.mono hDU))
  obtain ⟨δm, hδm, hδm'⟩ := huc (c / 16) (by positivity)
  set γ' := min γ δm
  have hγ' : 0 < γ' := lt_min hγ hδm
  obtain ⟨κ, hκ, hpiece⟩ := exists_piece (d := m) r hr hc hγ' hM hRd
  obtain ⟨δκ, hδκ, hδκ'⟩ := huc (κ / (Rd + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (Rd / δκ)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  set tt : ℕ → ℝ := fun i => min ((i : ℝ) / N) 1
  have htt : ∀ i, tt i ∈ Icc (0 : ℝ) 1 := fun i => ⟨le_min (by positivity) zero_le_one,
    min_le_right _ _⟩
  have htt0 : tt 0 = 0 := by simp [tt]
  have httN : tt N = 1 := by simp [tt, div_self hNpos.ne']
  have httd : ∀ i, |tt (i + 1) - tt i| ≤ 1 / N := by
    intro i
    simp only [tt]
    have h1 : ((i + 1 : ℕ) : ℝ) / N = (i : ℝ) / N + 1 / N := by push_cast; ring
    rw [h1]
    rw [abs_le]
    constructor
    · have := min_le_min_right (1 : ℝ) (show (i : ℝ) / N ≤ (i : ℝ) / N + 1 / N by
        linarith [one_div_pos.2 hNpos])
      linarith [one_div_pos.2 hNpos]
    · have : min ((i : ℝ) / N + 1 / N) 1 ≤ min ((i : ℝ) / N) 1 + 1 / N := by
        rcases le_total ((i : ℝ) / N) 1 with h | h
        · rw [min_eq_left h]; exact min_le_left _ _
        · rw [min_eq_right h]; linarith [min_le_right ((i : ℝ) / N + 1 / N) 1,
            one_div_pos.2 hNpos]
      linarith
  -- facts about F_t on R'
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ R', x0 + t • (x - x0) ∈ R' := fun t ht x hx =>
    alexPt_mem hR'c hx0' hx ht
  have hdalex : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ R',
      HasFDerivAt (alex F x0 t) (fderiv ℝ F (x0 + t • (x - x0))) x := fun t ht x hx =>
    hasFDerivAt_alex (hFd _ (hR'U (hpt t ht x hx)))
  have hfd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ R',
      fderiv ℝ (alex F x0 t) x = fderiv ℝ F (x0 + t • (x - x0)) := fun t ht x hx =>
    (hdalex t ht x hx).fderiv
  have hpiece_i : ∀ i : ℕ, ∃ (s : X m → ℝ) (h : GFHyp s), ContDiff ℝ (r + 1 : ℕ) s ∧
      HasCompactSupport s ∧ (∀ z, ‖hess s z‖ ≤ 1 / 2) ∧
      ∀ x ∈ R0, genMap h (alex F x0 (tt i) x) = alex F x0 (tt (i + 1)) x := by
    intro i
    set t := tt i
    set t' := tt (i + 1)
    have ht := htt i
    have ht' := htt (i + 1)
    have hAcd : ContDiffOn ℝ r (alex F x0 t) R' :=
      contDiffOn_alex hU hFU fun x hx => hR'U (hpt t ht x hx)
    have hBcd : ContDiffOn ℝ r (alex F x0 t') R' :=
      contDiffOn_alex hU hFU fun x hx => hR'U (hpt t' ht' x hx)
    have hsymp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ R', IsSymplecticAt (alex F x0 s) x := by
      intro s hs x hx v w
      rw [hfd s hs x hx]
      exact hFs _ (hR'U (hpt s hs x hx)) v w
    have hant : ∀ x ∈ R', ∀ y ∈ R', c * ‖x - y‖ ≤ ‖alex F x0 t x - alex F x0 t y‖ := by
      intro x hx y hy
      by_cases ht0 : t = 0
      · rw [ht0, alex_zero]
        simp only [add_sub_add_left_eq_sub, ← map_sub, sub_sub_sub_cancel_right]
        exact hlow x0 hx0' (x - y)
      · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        have e : alex F x0 t x - alex F x0 t y =
            t⁻¹ • (F (x0 + t • (x - x0)) - F (x0 + t • (y - x0))) := by
          simp only [alex, ht0, if_false]; module
        rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 htpos.le)]
        have h1 := hcD _ (hR'D (hpt t ht x hx)) _ (hR'D (hpt t ht y hy))
        have e2 : x0 + t • (x - x0) - (x0 + t • (y - x0)) = t • (x - y) := by
          rw [add_sub_add_left_eq_sub, ← smul_sub, sub_sub_sub_cancel_right]
        rw [e2, norm_smul, Real.norm_of_nonneg htpos.le] at h1
        rw [show c * ‖x - y‖ = t⁻¹ * (c * (t * ‖x - y‖)) by field_simp]
        exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 htpos.le)
    have hlowA : ∀ x ∈ R', ∀ v, c * ‖v‖ ≤ ‖fderiv ℝ (alex F x0 t) x v‖ := fun x hx v => by
      rw [hfd t ht x hx]; exact hlow _ (hpt t ht x hx) v
    have hMA : ∀ x ∈ R', ‖fderiv ℝ (alex F x0 t) x‖ ≤ M := fun x hx => by
      rw [hfd t ht x hx]; exact hMb _ (hR'D (hpt t ht x hx))
    have hmod : ∀ x ∈ R0, ∀ y ∈ ball x γ',
        ‖fderiv ℝ (alex F x0 t) y - fderiv ℝ (alex F x0 t) x‖ ≤ c / 16 := by
      intro x hx y hy
      have hyR : y ∈ R' := hgapR x hx (ball_subset_ball (min_le_left _ _) hy)
      rw [hfd t ht y hyR, hfd t ht x (hR0R' hx), ← dist_eq_norm]
      refine (hδm' _ (hR'D (hpt t ht y hyR)) _ (hR'D (hpt t ht x (hR0R' hx))) ?_).le
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
        Real.norm_of_nonneg ht.1]
      have := mem_ball.1 hy
      rw [dist_eq_norm] at this
      calc t * ‖y - x‖ ≤ 1 * ‖y - x‖ := by gcongr; exact ht.2
        _ < δm := by rw [one_mul]; exact this.trans_le (min_le_right _ _)
    have hdist : ∀ x ∈ R', dist (x0 + t' • (x - x0)) (x0 + t • (x - x0)) < δκ := by
      intro x hx
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
      calc |t' - t| * ‖x - x0‖ ≤ 1 / N * Rd := by
            gcongr; exacts [httd i, hRdb x (hR'D hx)]
        _ < δκ := by
            rw [one_div, inv_mul_eq_div, div_lt_iff₀ hNpos]
            rw [div_lt_iff₀ hδκ] at hN; linarith
    have hDBA' : ∀ x ∈ R', ‖fderiv ℝ (alex F x0 t') x - fderiv ℝ (alex F x0 t) x‖ ≤
        κ / (Rd + 1) := by
      intro x hx
      rw [hfd t' ht' x hx, hfd t ht x hx, ← dist_eq_norm]
      exact (hδκ' _ (hR'D (hpt t' ht' x hx)) _ (hR'D (hpt t ht x hx)) (hdist x hx)).le
    have hκRd : κ / (Rd + 1) ≤ κ := div_le_self hκ.le (by linarith)
    have hAB : ∀ x ∈ R', ‖alex F x0 t x - alex F x0 t' x‖ ≤ κ := by
      intro x hx
      have hmv := hR'c.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun y => alex F x0 t' y - alex F x0 t y)
        (fun y hy => ((hdalex t' ht' y hy).sub (hdalex t ht y hy)).hasFDerivWithinAt)
        (fun y hy => by
          have := hDBA' y hy; rwa [hfd t' ht' y hy, hfd t ht y hy] at this) hx0' hx
      simp only [alex_x0, sub_self, sub_zero] at hmv
      rw [norm_sub_rev]
      calc _ ≤ κ / (Rd + 1) * ‖x - x0‖ := hmv
        _ ≤ κ / (Rd + 1) * (Rd + 1) := by gcongr; linarith [hRdb x (hR'D hx)]
        _ = κ := by field_simp
    have hAbd : ∀ x ∈ R0, ‖alex F x0 t x‖ ≤ ‖F x0‖ + M * Rd := by
      intro x hx
      have hmv := hR'c.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y hy => (hdalex t ht y hy).hasFDerivWithinAt)
        (fun y hy => hMb _ (hR'D (hpt t ht y hy))) hx0' (hR0R' hx)
      rw [alex_x0] at hmv
      have := norm_le_insert' (alex F x0 t x) (F x0)
      calc ‖alex F x0 t x‖ ≤ ‖F x0‖ + ‖alex F x0 t x - F x0‖ := by
            linarith [norm_sub_norm_le (alex F x0 t x) (F x0)]
        _ ≤ ‖F x0‖ + M * Rd := by
            gcongr; exact hmv.trans (mul_le_mul_of_nonneg_left (hRdb x (hR'D (hR0R' hx))) hM)
    exact hpiece (alex F x0 t) (alex F x0 t') R0 R' x0 (‖F x0‖ + M * Rd) hR'o hR'c hx0 hR0R'
      (fun x hx => (ball_subset_ball (min_le_left _ _)).trans (hgapR x hx)) hAcd hBcd
      (hsymp t ht) (hsymp t' ht') hant hlowA hMA hmod (fun x hx => hRdb x (hR'D hx)) hAbd
      (fun x hx => (hDBA' x hx).trans hκRd) hAB
  choose S H hS1 hS2 hS3 hS4 using hpiece_i
  -- the exact composition
  set F₀ := alex F x0 0
  set fam : ℕ → X m → X m := fun i => Nat.casesOn i F₀ fun j => genMap (H j)
  have hrange : ∀ k, (List.range (k + 1)).map fam = F₀ :: (List.range k).map (fun j => genMap (H j)) := by
    intro k
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  have hexact : ∀ k, ∀ x ∈ R0, compList ((List.range (k + 1)).map fam) x = alex F x0 (tt k) x := by
    intro k
    induction k with
    | zero =>
      intro x _
      show compList [fam 0] x = _
      simp only [compList, Function.comp_apply, id, htt0]
      rfl
    | succ k ih =>
      intro x hx
      rw [List.range_succ, List.map_append, compList_append, Function.comp_apply, ih x hx]
      simp only [List.map_cons, List.map_nil, compList, Function.comp_apply, id]
      exact hS4 k x hx
  have hFeq : ∀ x ∈ R0, compList ((List.range (N + 1)).map fam) x = F x := fun x hx => by
    rw [hexact N x hx, httN, alex_one]
  -- smoothness of the factors
  have hF₀sm : ContDiff ℝ ∞ F₀ := by
    rw [show F₀ = fun x => F x0 + fderiv ℝ F x0 (x - x0) from alex_zero F x0]
    exact contDiff_const.add ((fderiv ℝ F x0).contDiff.comp (contDiff_id.sub contDiff_const))
  have hfamr : ∀ i ∈ List.range (N + 1), ContDiff ℝ r (fam i) := by
    intro i _
    rcases i with _ | j
    · exact hF₀sm.of_le (by exact_mod_cast le_top)
    · exact contDiff_genMap (H j) (hS1 j) (by push_cast; exact le_rfl)
  obtain ⟨δc, hδc, K', hK', hstab⟩ := comp_stable r (List.range (N + 1)) fam hfamr K hK hε
  have hsmooth : ∀ j : ℕ, ∃ (s' : X m → ℝ) (h' : GFHyp s'), ContDiff ℝ ∞ s' ∧
      CrCloseLe r K' (genMap (H j)) (genMap h') (δc / 2) := fun j =>
    exists_smooth_genMap_close r hr (H j) (hS1 j) (hS2 j) (hS3 j) hK' (half_pos hδc)
  choose S' H' hS'1 hS'2 using hsmooth
  set gam : ℕ → X m → X m := fun i => Nat.casesOn i F₀ fun j => genMap (H' j)
  have hclose := hstab gam (fun i _ => by
    rcases i with _ | j
    · exact ⟨hF₀sm.of_le (by exact_mod_cast le_top), fun k _ x _ => by simp [gam, fam]; exact hδc⟩
    · exact ⟨contDiff_genMap (H' j) (hS'1 j) (by exact_mod_cast le_top),
        (hS'2 j).lt (half_lt_self hδc)⟩)
  set G := compList ((List.range (N + 1)).map gam)
  -- G is a smooth symplectic diffeomorphism
  have hgam_sm : ∀ f ∈ (List.range (N + 1)).map gam, ContDiff ℝ ∞ f := by
    intro f hf
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hf
    rcases i with _ | j
    · exact hF₀sm
    · exact contDiff_genMap (H' j) (hS'1 j) (by exact_mod_cast le_top)
  have hL0 : Function.Injective (fderiv ℝ F x0) := hDFinj x0 (hR'U hx0')
  have hgam_bij : ∀ f ∈ (List.range (N + 1)).map gam, Function.Bijective f := by
    intro f hf
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hf
    rcases i with _ | j
    · show Function.Bijective F₀
      rw [show F₀ = fun x => F x0 + fderiv ℝ F x0 (x - x0) from alex_zero F x0]
      exact bijective_affine hL0 _ _
    · exact bijective_genMap (H' j)
  have hgam_symp : ∀ f ∈ (List.range (N + 1)).map gam, ∀ x, IsSymplecticAt f x := by
    intro f hf x
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hf
    rcases i with _ | j
    · show IsSymplecticAt F₀ x
      intro v w
      have hd : HasFDerivAt F₀ (fderiv ℝ F x0) x := by
        rw [show F₀ = fun x => F x0 + fderiv ℝ F x0 (x - x0) from alex_zero F x0]
        have := ((fderiv ℝ F x0).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x0)).const_add
          (F x0)
        simpa using this
      rw [hd.fderiv]
      exact hFs x0 (hR'U hx0') v w
    · exact isSymplecticAt_genMap (H' j) x
  have hG : G ∈ SympDiffeo m :=
    ⟨contDiff_compList _ hgam_sm, bijective_compList _ hgam_bij,
      isSymplecticAt_compList _ (fun f hf => (hgam_sm f hf).differentiable (by simp)) hgam_symp⟩
  refine ⟨G, hG, fun k hk x hx => ?_⟩
  have hev : F =ᶠ[𝓝 x] compList ((List.range (N + 1)).map fam) := by
    filter_upwards [hR0o.mem_nhds (hKR0 hx)] with y hy using (hFeq y hy).symm
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hclose k hk x hx

/-! ### Consequences -/

/-- `SymplecticApprox` + Turaev's literal theorem ⇒ the convex/injective Lemma 4. -/
theorem TuraevHenon_of_literal' (hT : TuraevLiteral) : TuraevHenon := by
  intro m r hr U hU hUc F hF hinj K hK hKU ε hε
  obtain ⟨G, hG, hFG⟩ := symplecticApprox m r hr U hU hUc F hF hinj K hK hKU (ε / 2) (half_pos hε)
  obtain ⟨η, V, k, hV, hGT⟩ := hT m G hG K hK r (ε / 2) (half_pos hε)
  refine ⟨(List.replicate k [V, linPot (-η), 0, 0, 0]).flatten, fun W hW => ?_, ?_⟩
  · obtain ⟨l, hl, hWl⟩ := List.mem_flatten.1 hW
    rw [(List.mem_replicate.1 hl).2] at hWl
    have hsm : ContDiff ℝ ∞ W := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hWl
      rcases hWl with rfl | rfl | rfl | rfl | rfl
      exacts [hV, (linPot (-η)).contDiff, contDiff_const, contDiff_const, contDiff_const]
    exact contDiff_infty.1 hsm _
  · have h := hFG.trans hGT
    rw [add_halves, turaevMap_iterate] at h
    exact h

/-- **Theorem 5 for convex U and injective maps, assuming only Hornik et al. (Lemma 2) and
Turaev's theorem as Turaev states it.** -/
theorem G_SympNet_universal_turaev (hH : HornikDensity) (hT : TuraevLiteral)
    (r : ℕ) (hr : 1 ≤ r) (σ : ℝ → ℝ) (hσ : RFinite r σ)
    (U : Set (X d)) (hU : IsOpen U) (hUc : Convex ℝ U) :
    UDense r U (GSympNet (d := d) σ) {F | F ∈ SP r U ∧ Set.InjOn F U} :=
  G_SympNet_universal hH (TuraevHenon_of_literal' hT) r hr σ hσ U hU hUc

end SympNet
