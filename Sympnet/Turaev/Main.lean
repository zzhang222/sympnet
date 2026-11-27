/-
  T-M: **Turaev's theorem in the form needed for Theorem 5** (`turaevShear`): every smooth
  symplectic diffeomorphism of ℝ^{2d} is C^r-approximated on compacts, for every r, by finite
  compositions of gradient shears (equivalently of Hénon maps). Hence `TuraevHenon` is a theorem
  and Theorem 5 (convex U, injective maps) holds with no hypotheses.

  Proof (Euler scheme for the Alexander isotopy). With G(0) = 0, G = Q ∘ DG(0) where
  Q = Gt(1) ∘ Git(0). Split [0, 1] into N steps of size h; the exact steps A_i = Gt(t_{i+1}) ∘
  Git(t_i) compose to Q. Replace A_i by a block B_i of transvections (one per ridge term of a
  Hornik approximation of the Hamiltonian). Then
  * C⁰: Gronwall with Lip(A_i) ≤ 1 + hL and ‖A_i − B_i‖ ≤ h²C_E + hδ + h²C_B;
  * C^{r+1}: the products of the B_i are bounded uniformly in N (Faà di Bruno), because
    ‖B_i − id‖_{C^{r+1}} ≤ h(M_X + 2);
  * interpolation turns C⁰-closeness into C^r-closeness.
-/
import Sympnet.Turaev.Steps

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Nat

noncomputable section

namespace SympNet

variable {d : ℕ}

/-- The Euler product of blocks. -/
def eulerProd (ρs : List (Ridge d)) (h : ℝ) : ℕ → X d → X d
  | 0 => id
  | i + 1 => blk ρs h (i * h) ∘ eulerProd ρs h i

theorem eulerProd_mem (ρs : List (Ridge d)) (h : ℝ) (i : ℕ) : eulerProd ρs h i ∈ ShearProd d := by
  induction i with
  | zero => exact ShearProd.id_mem
  | succ i ih => exact ShearProd.comp ih (blk_mem ρs h _)

theorem contDiff_blk (ρs : List (Ridge d)) (h t : ℝ) : ContDiff ℝ ∞ (blk ρs h t) :=
  ShearProd.contDiff (blk_mem ρs h t)

theorem contDiff_Xa_slice (ρs : List (Ridge d)) (t : ℝ) : ContDiff ℝ ∞ (fun z => Xa ρs (t, z)) := by
  have h2 : ContDiff ℝ ∞ (fun z : X d => ((t, z) : ℝ × X d)) := contDiff_const.prodMk contDiff_id
  exact (contDiff_Xa ρs).comp h2

/-- **Core: the Euler scheme converges in C^r.** -/
theorem euler_core {G : X d → X d} (hG : G ∈ SympDiffeo d) (h0 : G 0 = 0) {K' : Set (X d)}
    (hK' : IsCompact K') (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P ∈ ShearProd d, CrClose r K' (fun z => alexT G (1, alexT (sdInv G) (0, z))) P ε := by
  set F := alexT G
  set Fi := alexT (sdInv G)
  have hF : ContDiff ℝ ∞ F := contDiff_alexT hG.1
  have hFi : ContDiff ℝ ∞ Fi := contDiff_alexT (sd_contDiff_inv hG)
  set Q : X d → X d := fun z => F (1, Fi (0, z))
  have hQ : ContDiff ℝ ∞ Q := by
    have h2 : ContDiff ℝ ∞ (fun z : X d => ((0 : ℝ), z)) := contDiff_const.prodMk contDiff_id
    exact hF.comp (contDiff_const.prodMk (hFi.comp h2))
  set k := r + 1
  set K1 := cthickening 1 K'
  have hK1 : IsCompact K1 := hK'.cthickening
  -- the exact orbits stay in a ball
  set orb : ℝ × X d → X d := fun p => F (p.1, Fi (0, p.2))
  have horb : Continuous orb := hF.continuous.comp (continuous_fst.prodMk
    (hFi.continuous.comp (continuous_const.prodMk continuous_snd)))
  obtain ⟨ρ0, hρ0⟩ := ((isCompact_Icc.prod hK1).image horb).isBounded.exists_norm_le
  set ρ1 := max ρ0 0
  have hρ1 : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K1, ‖orb (t, x)‖ ≤ ρ1 := fun t ht x hx =>
    (hρ0 _ ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)
  set R := closedBall (0 : X d) (ρ1 + 2)
  have hR : IsCompact R := isCompact_closedBall _ _
  have hRc : Convex ℝ R := convex_closedBall _ _
  have hmemR : ∀ y : X d, ‖y‖ ≤ ρ1 + 2 → y ∈ R := fun y hy => by
    simpa [R, mem_closedBall, dist_zero_right] using hy
  -- net-independent constants
  obtain ⟨CE, hCE0, hCE⟩ := exact_step_consistency hG h0 hR
  obtain ⟨LA, hLA0, hLA⟩ := exact_step_lip hG h0 hR hRc
  obtain ⟨MX, hMX0, hMX⟩ := exists_partial_bound (contDiff_velX hG h0) k (isCompact_Icc.prod hR)
  obtain ⟨MQ, hMQ0, hMQ⟩ := exists_crBound k hK1 (hQ.of_le (by exact_mod_cast le_top))
  set Dst := Real.exp (k ! * (MX + 2))
  have hDst : 1 ≤ Dst := Real.one_le_exp (by positivity)
  set MP := max (ρ1 + 2) (Dst ^ k)
  set M := MQ + MP
  obtain ⟨ε0', hε0', hint⟩ := interp (W := X d) r K' one_pos M (ε / 2) (half_pos hε)
  set ε0 := min ε0' 1
  have hε0 : 0 < ε0 := lt_min hε0' one_pos
  set eL := Real.exp LA
  have heL : 1 ≤ eL := Real.one_le_exp hLA0
  set δ := ε0 / (3 * eL)
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [min_le_right ε0' 1]
  -- the ridge approximation and its block constant
  obtain ⟨ρs, hρs⟩ := velX_approx hG h0 hR k hδ
  obtain ⟨CB, hCB0, hCB⟩ := blk_estimate ρs k hR
  -- the step size
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * eL * (CE + CB) / ε0 + CB + 1)
  have hNpos : (0 : ℝ) < N := by
    have : 0 ≤ 3 * eL * (CE + CB) / ε0 := by positivity
    linarith
  set h := 1 / (N : ℝ)
  have hh0 : 0 ≤ h := by positivity
  have hNh : (N : ℝ) * h = 1 := by simp [h, hNpos.ne']
  have hh1 : h ≤ 1 := by
    rw [div_le_one hNpos]
    have : 0 ≤ 3 * eL * (CE + CB) / ε0 := by positivity
    linarith
  have hhCB : h * CB ≤ 1 := by
    rw [show h * CB = CB / N by simp [h, div_eq_inv_mul]]
    rw [div_le_one hNpos]
    have : 0 ≤ 3 * eL * (CE + CB) / ε0 := by positivity
    linarith
  have hhE : eL * (h * (CE + CB)) ≤ ε0 / 3 := by
    have h1 : 3 * eL * (CE + CB) / ε0 < N := by
      have : 0 ≤ CB := hCB0; linarith
    rw [div_lt_iff₀ hε0] at h1
    have h2 : eL * (h * (CE + CB)) = (3 * eL * (CE + CB)) / (3 * N) := by
      simp only [h]; field_simp
    rw [h2, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set η := h ^ 2 * CE + h * δ + h ^ 2 * CB
  have hη : 0 ≤ η := by positivity
  have hNη : (N : ℝ) * η = h * CE + δ + h * CB := by
    simp only [η]
    have : (N : ℝ) * h = 1 := hNh
    linear_combination (h * CE + δ + h * CB) * this
  have hLip : ∀ i ≤ N, (1 + h * LA) ^ i ≤ eL := by
    intro i hi
    calc (1 + h * LA) ^ i ≤ (1 + h * LA) ^ N :=
          pow_le_pow_right₀ (by nlinarith) hi
      _ ≤ Real.exp (h * LA) ^ N := pow_le_pow_left₀ (by nlinarith)
          (by linarith [Real.add_one_le_exp (h * LA)]) N
      _ = eL := by rw [← Real.exp_nat_mul, ← mul_assoc, hNh, one_mul]
  have hEbound : ∀ i ≤ N, (1 + h * LA) ^ i * (i * η) ≤ 2 * ε0 / 3 := by
    intro i hi
    have h1 : (i : ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hη
    calc (1 + h * LA) ^ i * (i * η) ≤ eL * (N * η) :=
          mul_le_mul (hLip i hi) h1 (by positivity) (by positivity)
      _ = eL * δ + eL * (h * (CE + CB)) := by rw [hNη]; ring
      _ ≤ ε0 / 3 + ε0 / 3 := by
          gcongr
          · simp only [δ]; field_simp; linarith
      _ = 2 * ε0 / 3 := by ring
  have hε01 : ε0 ≤ 1 := min_le_right _ _
  have hti : ∀ i ≤ N, (i : ℝ) * h ∈ Icc (0 : ℝ) 1 := fun i hi =>
    ⟨by positivity, by
      calc (i : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh0
        _ = 1 := hNh⟩
  have hhI : h ∈ Icc (0 : ℝ) 1 := ⟨hh0, hh1⟩
  -- C⁰ tracking (Gronwall)
  set P := eulerProd ρs h
  have htrack : ∀ x ∈ K1, ∀ i ≤ N, ‖orb (i * h, x) - P i x‖ ≤ (1 + h * LA) ^ i * (i * η) := by
    intro x hx i
    induction i with
    | zero =>
      intro _
      simp [orb, P, eulerProd, F, Fi, alexT_inv_right hG h0]
    | succ i ih =>
      intro hi
      have hi' : i ≤ N := by omega
      have hE := ih hi'
      set t := (i : ℝ) * h
      have ht := hti i hi'
      set a := orb (t, x)
      set b := P i x
      have ha : ‖a‖ ≤ ρ1 := hρ1 t ht x hx
      have hab : ‖a - b‖ ≤ 1 := hE.trans ((hEbound i hi').trans (by linarith))
      have haR : a ∈ R := hmemR a (by linarith)
      have hbR : b ∈ R := hmemR b (by
        have := norm_sub_norm_le b a; rw [norm_sub_rev] at hab; linarith)
      have ha' : orb (((i + 1 : ℕ) : ℝ) * h, x) = F (t + h, Fi (t, a)) := by
        have e1 : Fi (t, a) = Fi (0, x) := alexT_inv_left hG h0 t (Fi (0, x))
        rw [e1]; simp only [orb, t]; congr 2; push_cast; ring
      have hb' : P (i + 1) x = blk ρs h t b := rfl
      rw [ha', hb']
      have hX0 := hρs t ht b hbR 0 (by omega)
      rw [norm_iteratedFDeriv_zero] at hX0
      have hB0 := hCB h hhI t ht b hbR 0 (by omega)
      rw [norm_iteratedFDeriv_zero] at hB0
      have hA0 := hCE h hhI t ht b hbR
      have hL := hLA h hhI t ht a haR b hbR
      have step : ‖F (t + h, Fi (t, b)) - blk ρs h t b‖ ≤ η := by
        have e : F (t + h, Fi (t, b)) - blk ρs h t b =
            (F (t + h, Fi (t, b)) - b - h • velX G (t, b)) +
              h • (velX G (t, b) - Xa ρs (t, b)) - (blk ρs h t b - b - h • Xa ρs (t, b)) := by
          rw [smul_sub]; abel
        rw [e]
        have n2 : ‖h • (velX G (t, b) - Xa ρs (t, b))‖ ≤ h * δ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh0]
          exact mul_le_mul_of_nonneg_left hX0 hh0
        set A1 := F (t + h, Fi (t, b)) - b - h • velX G (t, b)
        set B1 := h • (velX G (t, b) - Xa ρs (t, b))
        set C1 := blk ρs h t b - b - h • Xa ρs (t, b)
        have m1 := norm_sub_le (A1 + B1) C1
        have m2 := norm_add_le A1 B1
        have m3 : ‖A1‖ ≤ h ^ 2 * CE := hA0
        have m4 : ‖C1‖ ≤ h ^ 2 * CB := hB0
        linarith
      calc ‖F (t + h, Fi (t, a)) - blk ρs h t b‖
          ≤ ‖F (t + h, Fi (t, a)) - F (t + h, Fi (t, b))‖ +
              ‖F (t + h, Fi (t, b)) - blk ρs h t b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (1 + h * LA) * ((1 + h * LA) ^ i * (i * η)) + η :=
            add_le_add (hL.trans (mul_le_mul_of_nonneg_left hE (by nlinarith))) step
        _ = (1 + h * LA) ^ (i + 1) * (i * η) + η := by rw [pow_succ]; ring
        _ ≤ (1 + h * LA) ^ (i + 1) * (i * η) + (1 + h * LA) ^ (i + 1) * η := by
            have h1 : 1 ≤ (1 + h * LA) ^ (i + 1) := one_le_pow₀ (by nlinarith)
            have := mul_le_mul_of_nonneg_right h1 hη
            linarith
        _ = (1 + h * LA) ^ (i + 1) * (((i + 1 : ℕ) : ℝ) * η) := by push_cast; ring
  have hPR : ∀ x ∈ K1, ∀ i ≤ N, ‖P i x‖ ≤ ρ1 + 1 := by
    intro x hx i hi
    have h1 : ‖orb (i * h, x) - P i x‖ ≤ 1 :=
      (htrack x hx i hi).trans ((hEbound i hi).trans (by linarith))
    have h2 := hρ1 _ (hti i hi) x hx
    have := norm_sub_norm_le (P i x) (orb (i * h, x))
    rw [norm_sub_rev] at h1
    linarith
  have hQN : ∀ x, orb ((N : ℝ) * h, x) = Q x := fun x => by simp only [orb, hNh, Q]
  -- C^k bound of the products
  set bb : ℕ → X d → X d := fun i y => blk ρs h (i * h) y - y
  have hbb : ∀ i, ContDiff ℝ k (bb i) := fun i =>
    ((contDiff_blk ρs h _).sub contDiff_id).of_le (by exact_mod_cast le_top)
  have hbbR : ∀ i < N, ∀ y ∈ R, ∀ l ≤ k, ‖iteratedFDeriv ℝ l (bb i) y‖ ≤ h * (MX + 2) := by
    intro i hi y hy l hl
    set t := (i : ℝ) * h
    have ht := hti i hi.le
    have e : bb i = (fun z => blk ρs h t z - z - h • Xa ρs (t, z)) + h • fun z => Xa ρs (t, z) := by
      funext z; simp [bb, t]
    have c1 : ContDiff ℝ ∞ (fun z => blk ρs h t z - z - h • Xa ρs (t, z)) :=
      ((contDiff_blk ρs h t).sub contDiff_id).sub ((contDiff_Xa_slice ρs t).const_smul h)
    have hl' : ((l : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
    have c2 : ContDiffAt ℝ l (h • fun z => Xa ρs (t, z)) y :=
      (((contDiff_Xa_slice ρs t).const_smul h).of_le hl').contDiffAt
    rw [e, iteratedFDeriv_add_apply (c1.of_le hl').contDiffAt c2,
      iteratedFDeriv_const_smul_apply ((contDiff_Xa_slice ρs t).of_le hl').contDiffAt]
    have hv : ContDiff ℝ ∞ (fun z => velX G (t, z)) := by
      have h2 : ContDiff ℝ ∞ (fun z : X d => ((t, z) : ℝ × X d)) :=
        contDiff_const.prodMk contDiff_id
      exact (contDiff_velX hG h0).comp h2
    have hXa : ‖iteratedFDeriv ℝ l (fun z => Xa ρs (t, z)) y‖ ≤ MX + 1 := by
      have h1 := hρs t ht y hy l hl
      have h2 := hMX (t, y) ⟨ht, hy⟩ l hl
      rw [show (fun z => velX G (t, z) - Xa ρs (t, z)) =
          (fun z => velX G (t, z)) - fun z => Xa ρs (t, z) from rfl,
        iteratedFDeriv_sub_apply (hv.of_le hl').contDiffAt
          ((contDiff_Xa_slice ρs t).of_le hl').contDiffAt] at h1
      have := norm_le_insert' (iteratedFDeriv ℝ l (fun z => Xa ρs (t, z)) y)
        (iteratedFDeriv ℝ l (fun z => velX G (t, z)) y)
      rw [norm_sub_rev] at this
      simp only at h2
      linarith
    have hb1 := hCB h hhI t ht y hy l hl
    calc _ ≤ ‖iteratedFDeriv ℝ l (fun z => blk ρs h t z - z - h • Xa ρs (t, z)) y‖ +
          ‖h • iteratedFDeriv ℝ l (fun z => Xa ρs (t, z)) y‖ := norm_add_le _ _
      _ ≤ h ^ 2 * CB + h * (MX + 1) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh0]
          exact mul_le_mul_of_nonneg_left hXa hh0
      _ ≤ h * (MX + 2) := by nlinarith
  have hP0 : P 0 = id := rfl
  have hPs : ∀ j, P (j + 1) = fun x => P j x + bb j (P j x) := fun j => by
    funext x; simp [P, eulerProd, bb]
  have hPbound : ∀ x ∈ K1, ∀ l ≤ k, ‖iteratedFDeriv ℝ l (P N) x‖ ≤ MP := by
    intro x hx l hl
    rcases Nat.eq_zero_or_pos l with rfl | hl1
    · rw [norm_iteratedFDeriv_zero]
      exact ((hPR x hx N le_rfl).trans (by linarith)).trans (le_max_left _ _)
    have hpb := prod_bound k hP0 hPs hbb x R (fun _ => h * (MX + 2)) (fun _ => by positivity) N
      (fun j hj => hmemR _ (by linarith [hPR x hx j hj.le])) hbbR l hl1 hl
    refine hpb.trans ((pow_le_pow_left₀ (by positivity) ?_ l).trans
      ((pow_le_pow_right₀ hDst hl).trans (le_max_right _ _)))
    refine (prod_one_add_le_exp N _ (fun _ => by positivity)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    apply le_of_eq
    simp only [Dst]
    congr 1
    calc (N : ℝ) * (k ! * (h * (MX + 2))) = (N * h) * (k ! * (MX + 2)) := by ring
      _ = _ := by rw [hNh, one_mul]
  -- interpolation
  refine ⟨P N, eulerProd_mem ρs h N, fun l hl x hx => ?_⟩
  have hPN : ContDiff ℝ ∞ (P N) := ShearProd.contDiff (eulerProd_mem ρs h N)
  have hfd : ContDiff ℝ (r + 1 : ℕ) (Q - P N) := (hQ.sub hPN).of_le (by exact_mod_cast le_top)
  have hkb : ∀ l ≤ r + 1, ∀ x ∈ cthickening 1 K', ‖iteratedFDeriv ℝ l (Q - P N) x‖ ≤ M := by
    intro l hl x hx
    have hl' : ((l : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
    rw [iteratedFDeriv_sub_apply (hQ.of_le hl').contDiffAt (hPN.of_le hl').contDiffAt]
    exact (norm_sub_le _ _).trans (add_le_add (hMQ l hl x hx) (hPbound x hx l hl))
  have hc0 : ∀ x ∈ cthickening 1 K', ‖(Q - P N) x‖ ≤ ε0' := by
    intro x hx
    have h1 := htrack x hx N le_rfl
    rw [hQN] at h1
    have h2 : (1 + h * LA) ^ N * (N * η) ≤ ε0 := (hEbound N le_rfl).trans (by linarith)
    exact (h1.trans h2).trans (min_le_left _ _)
  have key := hint (Q - P N) hfd hkb hc0 l hl x hx
  have hl' : ((l : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  rw [iteratedFDeriv_sub_apply (hQ.of_le hl').contDiffAt (hPN.of_le hl').contDiffAt] at key
  exact key.trans_lt (half_lt_self hε)

/-! ### Turaev's theorem (shear form) -/

theorem turaev_shear_zero {G : X d → X d} (hG : G ∈ SympDiffeo d) (h0 : G 0 = 0) {K : Set (X d)}
    (hK : IsCompact K) (r : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ Φ ∈ ShearProd d, CrClose r K G Φ ε := by
  set L0 := fderiv ℝ G 0
  have hL0 : IsSympLin (L0 : X d →ₗ[ℝ] X d) := hG.2.2 0
  have hL0m : ⇑L0 ∈ ShearProd d := linSymp_mem _ hL0
  set C := (‖L0‖ + 1) ^ r
  have hC : 0 < C := by positivity
  obtain ⟨P, hP, hc⟩ := euler_core hG h0 (hK.image L0.continuous) r (ε := ε / C) (by positivity)
  have hF : ContDiff ℝ ∞ (alexT G) := contDiff_alexT hG.1
  have hFi : ContDiff ℝ ∞ (alexT (sdInv G)) := contDiff_alexT (sd_contDiff_inv hG)
  have hQ : ContDiff ℝ ∞ (fun z => alexT G (1, alexT (sdInv G) (0, z))) := by
    have h2 : ContDiff ℝ ∞ (fun z : X d => ((0 : ℝ), z)) := contDiff_const.prodMk contDiff_id
    exact hF.comp (contDiff_const.prodMk (hFi.comp h2))
  have h := crClose_comp_clm L0 (hQ.of_le (by exact_mod_cast le_top))
    ((ShearProd.contDiff hP).of_le (by exact_mod_cast le_top)) hc
  rw [div_mul_cancel₀ _ hC.ne'] at h
  refine ⟨P ∘ L0, ShearProd.comp hL0m hP, ?_⟩
  convert h using 1
  funext x
  simp only [Function.comp_apply, L0]
  rw [← alexT_zero hG.1 h0, alexT_inv_left hG h0, alexT_one hG.1 h0]

/-- **Turaev's theorem, in the form needed for Theorem 5**: every smooth symplectic
diffeomorphism of ℝ^{2d} is C^r-approximated on every compact set, for every r, by finite
compositions of gradient shears with smooth potentials. -/
theorem turaevShear (G : X d → X d) (hG : G ∈ SympDiffeo d) {K : Set (X d)} (hK : IsCompact K)
    (r : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ Φ ∈ ShearProd d, CrClose r K G Φ ε := by
  set G' : X d → X d := fun x => G x - G 0
  have hG'd : ∀ x, fderiv ℝ G' x = fderiv ℝ G x := fun x => fderiv_sub_const _
  have hG' : G' ∈ SympDiffeo d := by
    refine ⟨hG.1.sub contDiff_const, ⟨fun x y hxy => hG.2.1.1 (sub_left_injective hxy),
      fun z => ?_⟩, fun x v w => by rw [hG'd]; exact hG.2.2 x v w⟩
    obtain ⟨x, hx⟩ := hG.2.1.2 (z + G 0)
    exact ⟨x, by simp [G', hx]⟩
  obtain ⟨Φ', hΦ', hc⟩ := turaev_shear_zero hG' (by simp [G']) hK r hε
  refine ⟨fun z => G 0 + Φ' z, const_add_mem hΦ' (G 0), fun k hk x hx => ?_⟩
  have hk' : ((k : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hΦs : ContDiff ℝ ∞ Φ' := ShearProd.contDiff hΦ'
  have hGs : ContDiff ℝ ∞ (fun z => G 0 + Φ' z) := contDiff_const.add hΦs
  have e1 : G = fun z => G 0 + G' z := by funext z; simp [G']
  rw [← iteratedFDeriv_sub_apply (hG.1.of_le hk').contDiffAt (hGs.of_le hk').contDiffAt]
  have e2 : (G - fun z => G 0 + Φ' z) = G' - Φ' := by funext z; simp [G']; abel
  rw [e2, iteratedFDeriv_sub_apply ((hG'.1).of_le hk').contDiffAt (hΦs.of_le hk').contDiffAt]
  exact hc k hk x hx

/-- **Lemma 4 of the paper (convex U, injective F) is a theorem.** -/
theorem turaevHenon : TuraevHenon := by
  intro m r hr U hU hUc F hF hinj K hK hKU ε hε
  obtain ⟨G, hG, hFG⟩ := symplecticApprox m r hr U hU hUc F hF hinj K hK hKU (ε / 2) (half_pos hε)
  obtain ⟨Φ, hΦ, hGΦ⟩ := turaevShear G hG hK r (half_pos hε)
  obtain ⟨Vs, hVs, rfl⟩ := ShearProd.exists_henon hΦ
  refine ⟨Vs, fun V hV => (hVs V hV).of_le (by exact_mod_cast le_top), ?_⟩
  have := hFG.trans hGΦ
  rwa [add_halves] at this

/-- **Theorem 5 of the paper, for convex U and injective maps, with no hypotheses**: for r ≥ 1,
U ⊆ ℝ^{2d} open and convex and σ r-finite, G-SympNets are r-uniformly dense on compacta in
the injective C^r symplectic maps on U. -/
theorem G_SympNet_universal_unconditional {d : ℕ} (r : ℕ) (hr : 1 ≤ r) (σ : ℝ → ℝ)
    (hσ : RFinite r σ) (U : Set (X d)) (hU : IsOpen U) (hUc : Convex ℝ U) :
    UDense r U (GSympNet (d := d) σ) {F | F ∈ SP r U ∧ Set.InjOn F U} :=
  G_SympNet_universal hornikDensity turaevHenon r hr σ hσ U hU hUc

end SympNet
