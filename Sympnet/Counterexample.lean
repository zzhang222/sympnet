/-
  The paper's Lemma 4 (and hence its Theorem 5) is false for a general open set U.

  Turaev's theorem is about symplectic *diffeomorphisms of ℝ^{2n}*. The paper restates it for
  every F ∈ SP^r(U) with U an arbitrary open set. (The main file uses it only for convex U and
  injective F, see `TuraevHenon`.) The general version fails: every composition of Hénon maps
  (and every G-SympNet) is injective, while a map in SP^r(U) need not be.

  Counterexample (any d ≥ 1): U = B(0,1) ∪ B(a,1) with ‖a‖ = 4, and F = id on B(0,1),
  F = (· − a) on B(a,1). Then F ∈ SP^r(U) and F(0) = F(a) = 0. If an injective C¹ map G were
  C¹-close (within 1/8) to F on the two closed balls of radius 1/2, then
  φ(y) = y − G y + G 0 would be a contraction of the closed ball B̄(a,1/2) into itself. Its
  fixed point y would satisfy G y = G 0 with y ≠ 0, a contradiction.

  We also check the identity (p,q) ↦ (p − c, q) = H[0]³ ∘ H[⟨c,·⟩], which shows that Turaev's
  maps (x,y) ↦ (y+η, −x+∇V(y)) are compositions of Hénon maps (used in the docstring of
  `TuraevHenon`).
-/
import Sympnet.SympNetUniversal

open Set Filter Topology Metric
open scoped ContDiff NNReal

noncomputable section

namespace SympNet

variable {d : ℕ}

/-! ### Iterated derivatives of order 0 and 1 as linear isometric images -/

section
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem iteratedFDeriv_zero_eq' (f : V → W) (x : V) :
    iteratedFDeriv ℝ 0 f x = (continuousMultilinearCurryFin0 ℝ V W).symm (f x) := by
  ext m; simp

theorem iteratedFDeriv_one_eq' (f : V → W) (x : V) :
    iteratedFDeriv ℝ 1 f x = (continuousMultilinearCurryFin1 ℝ V W).symm (fderiv ℝ f x) := by
  ext m; simp

theorem norm_iteratedFDeriv_zero_sub' (f g : V → W) (x : V) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 g x‖ = ‖f x - g x‖ := by
  rw [iteratedFDeriv_zero_eq', iteratedFDeriv_zero_eq', ← map_sub, LinearIsometryEquiv.norm_map]

theorem norm_iteratedFDeriv_one_sub' (f g : V → W) (x : V) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 g x‖ = ‖fderiv ℝ f x - fderiv ℝ g x‖ := by
  rw [iteratedFDeriv_one_eq', iteratedFDeriv_one_eq', ← map_sub, LinearIsometryEquiv.norm_map]

end

/-! ### The counterexample -/

/-- Centre of the second ball. -/
def cA (d : ℕ) : X d := (fun _ => (4 : ℝ), 0)

/-- The open set U = B(0,1) ∪ B(a,1). -/
def cU (d : ℕ) : Set (X d) := ball 0 1 ∪ ball (cA d) 1

/-- The compact set K = B̄(0,1/2) ∪ B̄(a,1/2) ⊆ U. -/
def cK (d : ℕ) : Set (X d) := closedBall 0 (1 / 2) ∪ closedBall (cA d) (1 / 2)

open Classical in
/-- F = id on B(0,1) and F = (· − a) on B(a,1): symplectic on U, but F 0 = F a = 0. -/
def cF (d : ℕ) (x : X d) : X d := if x ∈ ball (cA d) 1 then x - cA d else x

theorem dist_zero_cA (hd : 0 < d) : dist (0 : X d) (cA d) = 4 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [dist_zero_left, cA, Prod.norm_mk, pi_norm_const, norm_zero]
  norm_num

theorem isOpen_cU : IsOpen (cU d) := isOpen_ball.union isOpen_ball

theorem isCompact_cK : IsCompact (cK d) :=
  (isCompact_closedBall _ _).union (isCompact_closedBall _ _)

theorem cK_subset_cU : cK d ⊆ cU d :=
  union_subset_union (closedBall_subset_ball (by norm_num))
    (closedBall_subset_ball (by norm_num))

theorem not_mem_ball_cA_of_mem_ball_zero (hd : 0 < d) {x : X d} (hx : x ∈ ball 0 1) :
    x ∉ ball (cA d) 1 := by
  intro h
  have := dist_triangle (0 : X d) x (cA d)
  rw [dist_zero_cA hd, dist_comm] at this
  rw [mem_ball] at hx h
  linarith

theorem cF_eventually_zero (hd : 0 < d) {x : X d} (hx : x ∈ ball 0 1) :
    cF d =ᶠ[𝓝 x] id := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  simp [cF, not_mem_ball_cA_of_mem_ball_zero hd hy]

theorem cF_eventually_cA {x : X d} (hx : x ∈ ball (cA d) 1) :
    cF d =ᶠ[𝓝 x] fun y => y - cA d := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  simp [cF, hy]

theorem fderiv_cF (hd : 0 < d) {x : X d} (hx : x ∈ cU d) :
    fderiv ℝ (cF d) x = ContinuousLinearMap.id ℝ (X d) := by
  rcases hx with hx | hx
  · rw [(cF_eventually_zero hd hx).fderiv_eq, fderiv_id]
  · rw [(cF_eventually_cA hx).fderiv_eq, fderiv_sub_const, fderiv_fun_id]

theorem cF_mem_SP (hd : 0 < d) (r : ℕ) : cF d ∈ SP r (cU d) := by
  refine ⟨fun x hx => ?_, fun x hx v w => by rw [fderiv_cF hd hx]; rfl⟩
  rcases hx with hx | hx
  · exact (contDiff_id.contDiffAt.congr_of_eventuallyEq (cF_eventually_zero hd hx)).contDiffWithinAt
  · exact ((contDiff_id.sub contDiff_const).contDiffAt.congr_of_eventuallyEq
      (cF_eventually_cA hx)).contDiffWithinAt

theorem cF_zero (hd : 0 < d) : cF d 0 = 0 := by
  simp [cF, not_mem_ball_cA_of_mem_ball_zero hd (mem_ball_self one_pos)]

theorem cF_cA : cF d (cA d) = 0 := by simp [cF]

/-- No injective differentiable map is C¹-close (within 1/8) to `cF` on `cK`. -/
theorem not_crClose_cF_of_injective (hd : 0 < d) {G : X d → X d} (hG : Differentiable ℝ G)
    (hinj : Function.Injective G) : ¬ CrClose 1 (cK d) (cF d) G (1 / 8) := by
  intro h
  have h0 : ∀ x ∈ cK d, ‖cF d x - G x‖ < 1 / 8 := fun x hx => by
    rw [← norm_iteratedFDeriv_zero_sub']; exact h 0 (Nat.zero_le _) x hx
  set s : Set (X d) := closedBall (cA d) (1 / 2)
  have hsK : s ⊆ cK d := subset_union_right
  have h1 : ∀ x ∈ s, ‖ContinuousLinearMap.id ℝ (X d) - fderiv ℝ G x‖ ≤ 1 / 8 := fun x hx => by
    have := h 1 le_rfl x (hsK hx)
    rw [norm_iteratedFDeriv_one_sub', fderiv_cF hd (cK_subset_cU (hsK hx))] at this
    exact this.le
  -- the contraction φ y = y − G y + G 0
  set φ : X d → X d := fun y => y - G y + G 0
  have hφ' : ∀ x, HasFDerivAt φ (ContinuousLinearMap.id ℝ (X d) - fderiv ℝ G x) x := fun x =>
    ((hasFDerivAt_id x).sub (hG x).hasFDerivAt).add_const (G 0)
  have hlip : ∀ x ∈ s, ∀ y ∈ s, ‖φ y - φ x‖ ≤ 1 / 8 * ‖y - x‖ := fun x hx y hy =>
    (convex_closedBall _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hφ' z).hasFDerivWithinAt) h1 hx hy
  have hA : cA d ∈ s := mem_closedBall_self (by norm_num)
  have h0K : (0 : X d) ∈ cK d := subset_union_left (mem_closedBall_self (by norm_num))
  have hφA : ‖φ (cA d) - cA d‖ < 1 / 4 := by
    have e : φ (cA d) - cA d = (cF d (cA d) - G (cA d)) - (cF d 0 - G 0) := by
      simp only [φ, cF_cA, cF_zero hd]; abel
    rw [e]
    calc _ ≤ ‖cF d (cA d) - G (cA d)‖ + ‖cF d 0 - G 0‖ := norm_sub_le _ _
      _ < 1 / 8 + 1 / 8 := add_lt_add (h0 _ (hsK hA)) (h0 _ h0K)
      _ = 1 / 4 := by norm_num
  have hmaps : MapsTo φ s s := fun y hy => by
    have hy' : ‖y - cA d‖ ≤ 1 / 2 := by simpa [s, dist_eq_norm] using hy
    rw [mem_closedBall, dist_eq_norm]
    calc ‖φ y - cA d‖ ≤ ‖φ y - φ (cA d)‖ + ‖φ (cA d) - cA d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1 / 8 * (1 / 2) + 1 / 4 := add_le_add
          ((hlip _ hA _ hy).trans (by gcongr)) hφA.le
      _ ≤ 1 / 2 := by norm_num
  have hcontr : ContractingWith (1 / 8 : ℝ≥0) (hmaps.restrict φ s s) := by
    refine ⟨by rw [div_lt_one (by norm_num)]; norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
    push_cast
    exact hlip _ y.property _ x.property
  obtain ⟨y, hys, hfix, -⟩ :=
    ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hcontr hA
      (edist_ne_top _ _)
  have hGy : G y = G 0 := by
    have h' : y - G y + G 0 - y = 0 := sub_eq_zero.2 hfix
    calc G y = G y + (y - G y + G 0 - y) := by rw [h', add_zero]
      _ = G 0 := by abel
  have hy0 : y = 0 := hinj hGy
  have : dist (0 : X d) (cA d) ≤ 1 / 2 := by
    rw [← hy0]; exact hys
  rw [dist_zero_cA hd] at this
  norm_num at this

/-- **The paper's Lemma 4 is false.** -/
theorem not_TuraevHenonPaper : ¬ TuraevHenonPaper := by
  intro hT
  obtain ⟨Vs, hVs, hc⟩ := hT 1 1 le_rfl (cU 1) isOpen_cU (cF 1) (cF_mem_SP one_pos 1) (cK 1)
    isCompact_cK cK_subset_cU (1 / 8) (by norm_num)
  refine not_crClose_cF_of_injective one_pos ?_ ?_ hc
  · refine differentiable_compList _ fun f hf => ?_
    obtain ⟨V, hV, rfl⟩ := List.mem_map.1 hf
    have hg : Differentiable ℝ (grad V) :=
      (contDiff_grad (r := 1) (hVs V hV)).differentiable one_ne_zero
    exact differentiable_snd.prodMk (differentiable_fst.neg.add (hg.comp differentiable_snd))
  · refine injective_compList _ fun f hf => ?_
    obtain ⟨V, -, rfl⟩ := List.mem_map.1 hf
    exact injective_henon V

/-- **The paper's Theorem 5, as stated, is false**: for every d ≥ 1, r ≥ 1 and r-finite σ there is
an open U ⊆ ℝ^{2d} such that G-SympNets are not r-uniformly dense on compacta in SP^r(U). -/
theorem paper_theorem5_false (hd : 0 < d) (r : ℕ) (hr : 1 ≤ r) (σ : ℝ → ℝ) (hσ : RFinite r σ) :
    ∃ U : Set (X d), IsOpen U ∧ ¬ UDense r U (GSympNet (d := d) σ) (SP r U) := by
  refine ⟨cU d, isOpen_cU, fun ⟨_, h⟩ => ?_⟩
  obtain ⟨g, ⟨l, rfl⟩, hc⟩ :=
    h (cF d) (cF_mem_SP hd r) (cK d) isCompact_cK cK_subset_cU (1 / 8) (by norm_num)
  refine not_crClose_cF_of_injective hd ?_ (GSympNet.injective ⟨l, rfl⟩)
    fun k hk x hx => hc k (hk.trans hr) x hx
  refine differentiable_compList _ fun f hf => ?_
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hf
  exact (m.contDiff r σ hσ).differentiable (by exact_mod_cast (by omega : r ≠ 0))

/-! ### Turaev's maps are compositions of Hénon maps -/

/-- The linear potential x ↦ ⟨c, x⟩, as a continuous linear functional. -/
def linPot (c : E d) : E d →L[ℝ] ℝ := ∑ i, c i • ContinuousLinearMap.proj i

theorem grad_linPot (c : E d) : grad (linPot c) = fun _ => c := by
  funext x i
  simp [grad, ContinuousLinearMap.fderiv, linPot, Pi.single_apply]

theorem grad_zero' : grad (0 : E d → ℝ) = fun _ => 0 := by
  funext x i
  simp [grad]

/-- (p, q) ↦ (p − c, q) = H[0]³ ∘ H[⟨c,·⟩]. Hence Turaev's map (x,y) ↦ (y+η, −x+∇V(y)) equals
H[0]³ ∘ H[⟨−η,·⟩] ∘ H[V], a composition of Hénon maps with polynomial potentials. -/
theorem translation_eq_henon (c : E d) :
    (fun z : X d => (z.1 - c, z.2)) =
      compList [henon (linPot c), henon 0, henon 0, henon 0] := by
  funext z
  simp [compList, henon, grad_linPot, grad_zero', sub_eq_add_neg, add_comm]

end SympNet
