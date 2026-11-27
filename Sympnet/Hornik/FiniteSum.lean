/-
  H2: approximating ∫ g(y) G(y) dy by finite sums Σ cᵢ G(yᵢ), with points and weights depending
  only on a modulus δ (not on G): partition supp g into finitely many sets of diameter < δ.
-/
import Mathlib

open MeasureTheory Set Metric Function

noncomputable section

namespace SympNet

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopology Y]

/-- Disjoint pieces of a finite ball cover. -/
def coverPiece {n : ℕ} (L : Set Y) (z : Fin n → Y) (r : ℝ) (i : Fin n) : Set Y :=
  (L ∩ ball (z i) r) \ ⋃ j ∈ {j : Fin n | j < i}, ball (z j) r

theorem measurableSet_coverPiece {n : ℕ} {L : Set Y} (hL : MeasurableSet L) (z : Fin n → Y)
    (r : ℝ) (i : Fin n) : MeasurableSet (coverPiece L z r i) :=
  (hL.inter measurableSet_ball).diff
    (MeasurableSet.biUnion (Set.to_countable _) fun _ _ => measurableSet_ball)

theorem pairwise_disjoint_coverPiece {n : ℕ} (L : Set Y) (z : Fin n → Y) (r : ℝ) :
    Pairwise (Disjoint on coverPiece L z r) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · refine Set.disjoint_left.2 fun x hx hx' => hx'.2 ?_
    exact Set.mem_biUnion (show i ∈ {k : Fin n | k < j} from h) hx.1.2
  · refine Set.disjoint_left.2 fun x hx hx' => hx.2 ?_
    exact Set.mem_biUnion (show j ∈ {k : Fin n | k < i} from h) hx'.1.2

theorem iUnion_coverPiece {n : ℕ} {L : Set Y} (z : Fin n → Y) (r : ℝ)
    (hcov : L ⊆ ⋃ i, ball (z i) r) : ⋃ i, coverPiece L z r i = L := by
  classical
  apply Subset.antisymm
  · exact iUnion_subset fun i => fun x hx => hx.1.1
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hx)
    set T := Finset.univ.filter fun j : Fin n => x ∈ ball (z j) r
    have hT : T.Nonempty := ⟨i, by simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
    set i0 := T.min' hT
    have hi0 : x ∈ ball (z i0) r := by
      have := T.min'_mem hT
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    refine mem_iUnion.2 ⟨i0, ⟨hx, hi0⟩, fun hmem => ?_⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hmem
    have : i0 ≤ j := T.min'_le j (by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact hxj)
    exact absurd hj (not_lt.2 this)

/-- **Finite-sum approximation of integrals.** -/
theorem exists_finite_sum_approx (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] {g : Y → ℝ}
    (hg : Integrable g μ) {L : Set Y} (hL : IsCompact L) (hgL : ∀ y ∉ L, g y = 0) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (n : ℕ) (y : Fin n → Y) (c : Fin n → ℝ), (∀ i, y i ∈ L) ∧
      ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : Y → F)
        (η : ℝ), ContinuousOn G L → (∀ u ∈ L, ∀ v ∈ L, dist u v < δ → ‖G u - G v‖ ≤ η) →
        ‖∫ t, g t • G t ∂μ - ∑ i, c i • G (y i)‖ ≤ η * ∫ t, |g t| ∂μ := by
  classical
  obtain ⟨t, htL, htfin, hcov⟩ := finite_cover_balls_of_compact hL (half_pos hδ)
  set n := htfin.toFinset.card
  let e := htfin.toFinset.equivFin
  let z : Fin n → Y := fun i => (e.symm i : Y)
  have hzL : ∀ i, z i ∈ L := fun i => htL (htfin.mem_toFinset.1 (e.symm i).2)
  have hcov' : L ⊆ ⋃ i, ball (z i) (δ / 2) := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.1 (hcov hx)
    refine mem_iUnion.2 ⟨e ⟨w, htfin.mem_toFinset.2 hw⟩, ?_⟩
    simp [z, hxw]
  set A := coverPiece L z (δ / 2)
  have hLm : MeasurableSet L := hL.measurableSet
  have hAm : ∀ i, MeasurableSet (A i) := measurableSet_coverPiece hLm z _
  have hAd : Pairwise (Disjoint on A) := pairwise_disjoint_coverPiece L z _
  have hAU : ⋃ i, A i = L := iUnion_coverPiece z _ hcov'
  have hAL : ∀ i, A i ⊆ L := fun i x hx => hx.1.1
  refine ⟨n, z, fun i => ∫ t in A i, g t ∂μ, hzL, ?_⟩
  intro F _ _ _ G η hGc hGm
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn hGc
  have hGmeas : AEStronglyMeasurable G (μ.restrict L) := hGc.aestronglyMeasurable hLm
  have hint : IntegrableOn (fun t => g t • G t) L μ := by
    refine Integrable.smul_of_top_left hg.integrableOn ?_
    exact memLp_top_of_bound hGmeas M ((ae_restrict_iff' hLm).2 (Filter.Eventually.of_forall hM))
  have hintA : ∀ i, IntegrableOn (fun t => g t • G t) (A i) μ := fun i => hint.mono_set (hAL i)
  have habs : IntegrableOn (fun t => |g t|) L μ := hg.abs.integrableOn
  have h1 : ∫ t, g t • G t ∂μ = ∑ i, ∫ t in A i, g t • G t ∂μ := by
    rw [← integral_iUnion_fintype hAm hAd hintA, hAU,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hgL x hx])]
  have h2 : ∫ t, |g t| ∂μ ≥ ∑ i, ∫ t in A i, |g t| ∂μ := by
    rw [← integral_iUnion_fintype hAm hAd fun i => habs.mono_set (hAL i), hAU]
    exact setIntegral_le_integral hg.abs (Filter.Eventually.of_forall fun x => abs_nonneg _)
  have hpiece : ∀ i, ‖∫ t in A i, g t • G t ∂μ - (∫ t in A i, g t ∂μ) • G (z i)‖ ≤
      η * ∫ t in A i, |g t| ∂μ := by
    intro i
    have hgi : IntegrableOn g (A i) μ := hg.integrableOn
    rw [← integral_smul_const, ← integral_sub (hintA i) (hgi.smul_const _)]
    calc ‖∫ t in A i, (g t • G t - g t • G (z i)) ∂μ‖
        ≤ ∫ t in A i, η * |g t| ∂μ := by
          refine norm_integral_le_of_norm_le ((hg.abs.integrableOn).const_mul η) ?_
          refine (ae_restrict_iff' (hAm i)).2 (Filter.Eventually.of_forall fun x hx => ?_)
          rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_comm]
          gcongr
          exact hGm x (hAL i hx) (z i) (hzL i) (by have := mem_ball.1 hx.1.2; linarith)
      _ = η * ∫ t in A i, |g t| ∂μ := integral_const_mul _ _
  rw [h1, ← Finset.sum_sub_distrib]
  calc ‖∑ i, (∫ t in A i, g t • G t ∂μ - (∫ t in A i, g t ∂μ) • G (z i))‖
      ≤ ∑ i, η * ∫ t in A i, |g t| ∂μ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
        hpiece i)
    _ = η * ∑ i, ∫ t in A i, |g t| ∂μ := (Finset.mul_sum _ _ _).symm
    _ ≤ η * ∫ t, |g t| ∂μ := by
        rcases isEmpty_or_nonempty (Fin n) with h | ⟨⟨i⟩⟩
        · have hL0 : L = ∅ := by rw [← hAU]; exact iUnion_of_empty _
          have hg0 : ∀ t, g t = 0 := fun t => hgL t (by simp [hL0])
          simp [hg0]
        · have hη : 0 ≤ η := by
            have := hGm (z i) (hzL i) (z i) (hzL i) (by simp [hδ])
            simpa using (norm_nonneg _).trans this
          exact mul_le_mul_of_nonneg_left h2 hη

end SympNet
