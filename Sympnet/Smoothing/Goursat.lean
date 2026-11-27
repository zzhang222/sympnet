/-
  C6: A continuous, locally exact 1-form on a convex open set is exact (Goursat's subdivision
  argument). We need this because the generating-function 1-form of a C¹ symplectic map is only
  continuous, so Mathlib's Poincaré lemma (which needs a differentiable, closed form) does not
  apply directly.
-/
import Mathlib

open Set Filter Topology Metric

noncomputable section

namespace SympNet

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Integral of the 1-form `β` along the oriented segment from `a` to `b`. -/
def segInt (β : V → V →L[ℝ] ℝ) (a b : V) : ℝ :=
  ∫ t in (0 : ℝ)..1, β (a + t • (b - a)) (b - a)

theorem segment_param_mem {a b : V} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    a + t • (b - a) ∈ segment ℝ a b := by
  rw [segment_eq_image']; exact ⟨t, ht, rfl⟩

theorem intervalIntegrable_segInt {β : V → V →L[ℝ] ℝ} {a b : V}
    (hβ : ContinuousOn β (segment ℝ a b)) (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t : ℝ => β (a + t • (b - a)) (b - a)) MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  have hsub : uIcc u v ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc hu hv
  have hpath : ContinuousOn (fun t : ℝ => a + t • (b - a)) (uIcc u v) := by fun_prop
  have h1 : ContinuousOn (fun t : ℝ => β (a + t • (b - a))) (uIcc u v) :=
    hβ.comp hpath fun t ht => segment_param_mem (hsub ht)
  exact h1.clm_apply continuousOn_const

/-- Fundamental theorem of calculus along a segment. -/
theorem segInt_eq_sub {β : V → V →L[ℝ] ℝ} {f : V → ℝ} {a b : V}
    (hf : ∀ y ∈ segment ℝ a b, HasFDerivAt f (β y) y) (hβ : ContinuousOn β (segment ℝ a b)) :
    segInt β a b = f b - f a := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => f (a + t • (b - a)))
    (f' := fun t : ℝ => β (a + t • (b - a)) (b - a)) (a := 0) (b := 1) ?_
    (intervalIntegrable_segInt hβ 0 1 (by simp) (by simp))
  · simpa [segInt] using h
  · intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hp : HasDerivAt (fun t : ℝ => a + t • (b - a)) (b - a) t := by
      simpa using ((hasDerivAt_id t).smul_const (b - a)).const_add a
    exact (hf _ (segment_param_mem ht)).comp_hasDerivAt t hp

theorem segInt_symm (β : V → V →L[ℝ] ℝ) (a b : V) : segInt β b a = -segInt β a b := by
  have e : ∀ t : ℝ, β (b + t • (a - b)) (a - b) = -β (a + (1 - t) • (b - a)) (b - a) := by
    intro t
    have h1 : b + t • (a - b) = a + (1 - t) • (b - a) := by module
    have h2 : a - b = -(b - a) := by abel
    rw [h1, h2, map_neg]
  simp only [segInt, e, intervalIntegral.integral_neg]
  congr 1
  simpa using intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => β (a + t • (b - a)) (b - a)) (1 : ℝ) (a := 0) (b := 1)

/-- The midpoint of the segment from `a` to `b`, written as `a + ½ (b − a)`. -/
def mid (a b : V) : V := a + (1 / 2 : ℝ) • (b - a)

theorem segInt_split {β : V → V →L[ℝ] ℝ} {a b : V} (hβ : ContinuousOn β (segment ℝ a b)) :
    segInt β a b = segInt β a (mid a b) + segInt β (mid a b) b := by
  set h : ℝ → ℝ := fun t => β (a + t • (b - a)) (b - a)
  have e1 : ∀ t : ℝ, β (a + t • (mid a b - a)) (mid a b - a) = (1 / 2 : ℝ) * h (t / 2) := by
    intro t
    have h1 : a + t • (mid a b - a) = a + (t / 2) • (b - a) := by simp only [mid]; module
    have h2 : mid a b - a = (1 / 2 : ℝ) • (b - a) := by simp only [mid]; module
    rw [h1, h2, map_smul, smul_eq_mul]
  have e2 : ∀ t : ℝ, β (mid a b + t • (b - mid a b)) (b - mid a b) =
      (1 / 2 : ℝ) * h (t / 2 + 1 / 2) := by
    intro t
    have h1 : mid a b + t • (b - mid a b) = a + (t / 2 + 1 / 2) • (b - a) := by
      simp only [mid]; module
    have h2 : b - mid a b = (1 / 2 : ℝ) • (b - a) := by simp only [mid]; module
    rw [h1, h2, map_smul, smul_eq_mul]
  have i1 : ∫ t in (0 : ℝ)..1, h (t / 2) = 2 * ∫ t in (0 : ℝ)..(1 / 2), h t := by
    rw [intervalIntegral.integral_comp_div h (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have i2 : ∫ t in (0 : ℝ)..1, h (t / 2 + 1 / 2) = 2 * ∫ t in (1 / 2 : ℝ)..1, h t := by
    rw [intervalIntegral.integral_comp_div_add h (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_segInt hβ 0 (1 / 2) (by norm_num) (by norm_num))
    (intervalIntegrable_segInt hβ (1 / 2) 1 (by norm_num) (by norm_num))
  simp only [segInt, e1, e2, intervalIntegral.integral_const_mul, i1, i2]
  change ∫ t in (0 : ℝ)..1, h t = _
  rw [← hadd]
  ring

/-! ### Triangles -/

/-- Integral of `β` around the oriented triangle `a → b → c → a`. -/
def defect (β : V → V →L[ℝ] ℝ) (a b c : V) : ℝ := segInt β a b + segInt β b c + segInt β c a

theorem defect_eq_zero_of_exact {β : V → V →L[ℝ] ℝ} {f : V → ℝ} {S : Set V} (hS : Convex ℝ S)
    (hf : ∀ y ∈ S, HasFDerivAt f (β y) y) (hβ : ContinuousOn β S) {a b c : V} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) : defect β a b c = 0 := by
  have h : ∀ {x y : V}, x ∈ S → y ∈ S → segInt β x y = f y - f x := fun hx hy =>
    segInt_eq_sub (fun z hz => hf z (hS.segment_subset hx hy hz)) (hβ.mono (hS.segment_subset hx hy))
  rw [defect, h ha hb, h hb hc, h hc ha]; ring

theorem mid_mem {S : Set V} (hS : Convex ℝ S) {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    mid a b ∈ S :=
  hS.segment_subset ha hb (segment_param_mem (by norm_num))

/-- The four subtriangles of the midpoint subdivision. -/
def subTri (T : V × V × V) : Fin 4 → V × V × V :=
  let a := T.1; let b := T.2.1; let c := T.2.2
  ![(a, mid a b, mid c a), (mid a b, b, mid b c), (mid c a, mid b c, c),
    (mid b c, mid c a, mid a b)]

def triDefect (β : V → V →L[ℝ] ℝ) (T : V × V × V) : ℝ := defect β T.1 T.2.1 T.2.2

theorem triDefect_subdivide {β : V → V →L[ℝ] ℝ} {S : Set V} (hS : Convex ℝ S)
    (hβ : ContinuousOn β S) {T : V × V × V} (ha : T.1 ∈ S) (hb : T.2.1 ∈ S) (hc : T.2.2 ∈ S) :
    triDefect β T = ∑ j, triDefect β (subTri T j) := by
  obtain ⟨a, b, c⟩ := T
  simp only at ha hb hc
  have sab := segInt_split (β := β) (hβ.mono (hS.segment_subset ha hb))
  have sbc := segInt_split (β := β) (hβ.mono (hS.segment_subset hb hc))
  have sca := segInt_split (β := β) (hβ.mono (hS.segment_subset hc ha))
  have r1 := segInt_symm β (mid a b) (mid c a)
  have r2 := segInt_symm β (mid b c) (mid a b)
  have r3 := segInt_symm β (mid c a) (mid b c)
  simp only [triDefect, subTri, defect, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  linarith

/-- Size of a triangle: its longest side. -/
def triSize (T : V × V × V) : ℝ := max (max ‖T.2.1 - T.1‖ ‖T.2.2 - T.2.1‖) ‖T.1 - T.2.2‖

theorem triSize_subTri (T : V × V × V) (j : Fin 4) : triSize (subTri T j) = triSize T / 2 := by
  obtain ⟨a, b, c⟩ := T
  have e1 : mid a b - a = (1 / 2 : ℝ) • (b - a) := by simp only [mid]; module
  have e2 : b - mid a b = (1 / 2 : ℝ) • (b - a) := by simp only [mid]; module
  have e3 : mid b c - b = (1 / 2 : ℝ) • (c - b) := by simp only [mid]; module
  have e4 : c - mid b c = (1 / 2 : ℝ) • (c - b) := by simp only [mid]; module
  have e5 : mid c a - c = (1 / 2 : ℝ) • (a - c) := by simp only [mid]; module
  have e6 : a - mid c a = (1 / 2 : ℝ) • (a - c) := by simp only [mid]; module
  have e7 : mid c a - mid a b = (1 / 2 : ℝ) • (c - b) := by simp only [mid]; module
  have e8 : mid a b - mid c a = (1 / 2 : ℝ) • (b - c) := by simp only [mid]; module
  have e9 : mid b c - mid a b = (1 / 2 : ℝ) • (c - a) := by simp only [mid]; module
  have e10 : mid a b - mid b c = (1 / 2 : ℝ) • (a - c) := by simp only [mid]; module
  have e11 : mid c a - mid b c = (1 / 2 : ℝ) • (a - b) := by simp only [mid]; module
  have e12 : mid b c - mid c a = (1 / 2 : ℝ) • (b - a) := by simp only [mid]; module
  have n : ∀ v : V, ‖(1 / 2 : ℝ) • v‖ = ‖v‖ / 2 := fun v => by
    rw [norm_smul]; norm_num; ring
  have s1 : ‖b - c‖ = ‖c - b‖ := norm_sub_rev _ _
  have s2 : ‖c - a‖ = ‖a - c‖ := norm_sub_rev _ _
  have s3 : ‖a - b‖ = ‖b - a‖ := norm_sub_rev _ _
  fin_cases j <;>
  simp only [triSize, subTri, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, n, s1, s2, s3] <;>
  rw [max_div_div_right (by norm_num : (0 : ℝ) ≤ 2),
    max_div_div_right (by norm_num : (0 : ℝ) ≤ 2)] <;> ac_rfl

/-- **Goursat**: around every triangle in a convex set, a continuous locally exact form
integrates to zero. -/
theorem defect_eq_zero {β : V → V →L[ℝ] ℝ} {C : Set V} (hC : Convex ℝ C)
    (hβ : ContinuousOn β C)
    (hloc : ∀ x ∈ C, ∃ ε > 0, ∃ f : V → ℝ, ∀ y ∈ ball x ε, HasFDerivAt f (β y) y)
    {a b c : V} (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) : defect β a b c = 0 := by
  by_contra hne
  set K0 : Set V := convexHull ℝ {a, b, c}
  have hK0c : IsCompact K0 := (Set.toFinite _).isCompact_convexHull ℝ
  have hK0v : Convex ℝ K0 := convex_convexHull ℝ _
  have hK0C : K0 ⊆ C := convexHull_min (by simp [insert_subset_iff, ha, hb, hc]) hC
  set P : V × V × V → Prop := fun T => T.1 ∈ K0 ∧ T.2.1 ∈ K0 ∧ T.2.2 ∈ K0
  -- choosing a subtriangle carrying at least a quarter of the defect
  have hstep : ∀ T, P T → ∃ j, |triDefect β T| / 4 ≤ |triDefect β (subTri T j)| := by
    intro T hT
    by_contra hcon
    push Not at hcon
    have hsum := triDefect_subdivide hK0v (hβ.mono hK0C) hT.1 hT.2.1 hT.2.2
    have : |triDefect β T| < |triDefect β T| := by
      calc |triDefect β T| = |∑ j, triDefect β (subTri T j)| := by rw [← hsum]
        _ ≤ ∑ j, |triDefect β (subTri T j)| := Finset.abs_sum_le_sum_abs _ _
        _ < ∑ _j : Fin 4, |triDefect β T| / 4 := Finset.sum_lt_sum_of_nonempty
            Finset.univ_nonempty fun j _ => hcon j
        _ = |triDefect β T| := by simp; ring
    exact lt_irrefl _ this
  have hsubP : ∀ T, P T → ∀ j, P (subTri T j) := by
    rintro ⟨a', b', c'⟩ ⟨h1, h2, h3⟩ j
    have m1 := mid_mem hK0v h1 h2; have m2 := mid_mem hK0v h2 h3; have m3 := mid_mem hK0v h3 h1
    fin_cases j <;> exact ⟨by simp [subTri, *], by simp [subTri, *], by simp [subTri, *]⟩
  classical
  let next : V × V × V → V × V × V := fun T =>
    if h : P T then subTri T (Classical.choose (hstep T h)) else T
  let seq : ℕ → V × V × V := fun n => next^[n] (a, b, c)
  have hP0 : P (a, b, c) := ⟨subset_convexHull ℝ _ (by simp), subset_convexHull ℝ _ (by simp),
    subset_convexHull ℝ _ (by simp)⟩
  have hseqP : ∀ n, P (seq n) := by
    intro n
    induction n with
    | zero => exact hP0
    | succ n ih =>
      simp only [seq, Function.iterate_succ_apply'] at ih ⊢
      simp only [next, dite_eq_left ih]
      exact hsubP _ ih _
  have hseq_succ : ∀ n, seq (n + 1) = subTri (seq n) (Classical.choose (hstep _ (hseqP n))) := by
    intro n
    simp only [seq, Function.iterate_succ_apply']
    exact dite_eq_left (hseqP n)
  have hdef : ∀ n, |triDefect β (a, b, c)| / 4 ^ n ≤ |triDefect β (seq n)| := by
    intro n
    induction n with
    | zero => simp [seq]
    | succ n ih =>
      rw [hseq_succ, pow_succ, ← div_div]
      exact (div_le_div_of_nonneg_right ih (by norm_num)).trans
        (Classical.choose_spec (hstep _ (hseqP n)))
  have hsize : ∀ n, triSize (seq n) = triSize (a, b, c) / 2 ^ n := by
    intro n
    induction n with
    | zero => simp [seq]
    | succ n ih => rw [hseq_succ, triSize_subTri, ih, pow_succ, div_div]
  -- a limit point of the first vertices
  obtain ⟨z, hzK, φ, hφ, hlim⟩ := hK0c.tendsto_subseq fun n => (hseqP n).1
  obtain ⟨ε, hε, f, hf⟩ := hloc z (hK0C hzK)
  have hsmall : Tendsto (fun n => triSize (seq (φ n))) atTop (𝓝 0) := by
    simp only [hsize]
    have : Tendsto (fun n : ℕ => triSize (a, b, c) / 2 ^ n) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul (triSize (a, b, c))
    exact this.comp hφ.tendsto_atTop
  have hev : ∀ᶠ n in atTop, dist (seq (φ n)).1 z < ε / 2 ∧ triSize (seq (φ n)) < ε / 2 :=
    ((tendsto_iff_dist_tendsto_zero.1 hlim).eventually (gt_mem_nhds (half_pos hε))).and
      (hsmall.eventually (gt_mem_nhds (half_pos hε)))
  obtain ⟨n, hn1, hn2⟩ := hev.exists
  set T := seq (φ n)
  rw [dist_eq_norm] at hn1
  have hTa : T.1 ∈ ball z ε := by rw [mem_ball, dist_eq_norm]; linarith
  have hTb : T.2.1 ∈ ball z ε := by
    have : ‖T.2.1 - T.1‖ ≤ triSize T := (le_max_left _ _).trans (le_max_left _ _)
    rw [mem_ball, dist_eq_norm]
    calc ‖T.2.1 - z‖ ≤ ‖T.2.1 - T.1‖ + ‖T.1 - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε := by linarith
  have hTc : T.2.2 ∈ ball z ε := by
    have : ‖T.1 - T.2.2‖ ≤ triSize T := le_max_right _ _
    rw [mem_ball, dist_eq_norm]
    calc ‖T.2.2 - z‖ ≤ ‖T.2.2 - T.1‖ + ‖T.1 - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε := by rw [norm_sub_rev T.2.2]; linarith
  have hzero : triDefect β T = 0 := by
    have hP := hseqP (φ n)
    exact defect_eq_zero_of_exact ((convex_ball z ε).inter hK0v) (fun y hy => hf y hy.1)
      (hβ.mono (inter_subset_right.trans hK0C)) ⟨hTa, hP.1⟩ ⟨hTb, hP.2.1⟩ ⟨hTc, hP.2.2⟩
  have hpos : 0 < |triDefect β (a, b, c)| / 4 ^ (φ n) := by
    have : triDefect β (a, b, c) ≠ 0 := hne
    positivity
  have := hdef (φ n)
  rw [hzero, abs_zero] at this
  linarith

/-- **Exactness**: a continuous, locally exact 1-form on a convex open set has a primitive. -/
theorem exists_primitive_of_locallyExact {β : V → V →L[ℝ] ℝ} {C : Set V} (hC : Convex ℝ C)
    (hCo : IsOpen C) (hβ : ContinuousOn β C)
    (hloc : ∀ x ∈ C, ∃ ε > 0, ∃ f : V → ℝ, ∀ y ∈ ball x ε, HasFDerivAt f (β y) y) :
    ∃ T : V → ℝ, ∀ x ∈ C, HasFDerivAt T (β x) x := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · exact ⟨0, fun x hx => hx.elim⟩
  refine ⟨fun x => segInt β x0 x, fun x hx => ?_⟩
  obtain ⟨ε, hε, f, hf⟩ := hloc x hx
  obtain ⟨δ, hδ, hδC⟩ := Metric.isOpen_iff.1 hCo x hx
  set ρ := min ε δ
  have hρ : 0 < ρ := lt_min hε hδ
  have hS : ball x ρ ⊆ C ∩ ball x ε := fun y hy =>
    ⟨hδC (ball_subset_ball (min_le_right _ _) hy), ball_subset_ball (min_le_left _ _) hy⟩
  have heq : (fun y => segInt β x0 y) =ᶠ[𝓝 x] fun y => segInt β x0 x + (f y - f x) := by
    filter_upwards [ball_mem_nhds x hρ] with y hy
    have hyC := (hS hy).1
    have h0 := defect_eq_zero hC hβ hloc hx0 hx hyC
    have hsym := segInt_symm β x0 y
    have hxy : segInt β x y = f y - f x :=
      segInt_eq_sub (fun z hz => hf z ((hS ((convex_ball x ρ).segment_subset (mem_ball_self hρ)
        hy hz)).2)) (hβ.mono fun z hz => (hS ((convex_ball x ρ).segment_subset
        (mem_ball_self hρ) hy hz)).1)
    rw [defect] at h0
    linarith
  have hd : HasFDerivAt (fun y => segInt β x0 x + (f y - f x)) (β x) x :=
    ((hf x (mem_ball_self hε)).sub_const (f x)).const_add _
  exact hd.congr_of_eventuallyEq heq

end SympNet
