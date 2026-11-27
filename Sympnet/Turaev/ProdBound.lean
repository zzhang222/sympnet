/-
  T-P: uniform C^k bounds for long compositions of near-identity maps (Faà di Bruno).
  If P_{j+1} = (id + b_j) ∘ P_j, P_0 = id and ‖D^i b_j‖ ≤ c_j (i ≤ k) along the orbit, then
  ‖D^i P_n x‖ ≤ (∏_{j<n} (1 + k!·c_j))^i for 1 ≤ i ≤ k.
-/
import Sympnet.Turaev.Interp

open Set Filter Topology Metric
open scoped ContDiff Nat

noncomputable section

namespace SympNet

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_iteratedFDeriv_id_le {i : ℕ} (hi : 1 ≤ i) (x : V) :
    ‖iteratedFDeriv ℝ i (id : V → V) x‖ ≤ 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have : fderiv ℝ (id : V → V) = fun _ => ContinuousLinearMap.id ℝ V := funext fun _ => fderiv_id
  rw [this]
  rcases n with _ | n
  · simpa using ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne (by simp)]; simp

theorem prod_bound (k : ℕ) {P b : ℕ → V → V} (hP0 : P 0 = id)
    (hP : ∀ j, P (j + 1) = fun x => P j x + b j (P j x)) (hb : ∀ j, ContDiff ℝ k (b j))
    (x : V) (R : Set V) (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) :
    ∀ n : ℕ, (∀ j < n, P j x ∈ R) →
      (∀ j < n, ∀ y ∈ R, ∀ i ≤ k, ‖iteratedFDeriv ℝ i (b j) y‖ ≤ c j) →
      ∀ i, 1 ≤ i → i ≤ k →
        ‖iteratedFDeriv ℝ i (P n) x‖ ≤ (∏ j ∈ Finset.range n, (1 + k ! * c j)) ^ i := by
  have hPs : ∀ j, ContDiff ℝ k (P j) := by
    intro j
    induction j with
    | zero => rw [hP0]; exact contDiff_id
    | succ j ih => rw [hP j]; exact ih.add ((hb j).comp ih)
  intro n
  induction n with
  | zero =>
    intro _ _ i hi _
    simpa [hP0] using norm_iteratedFDeriv_id_le hi x
  | succ n ih =>
    intro hR hbR i hi hik
    set D := ∏ j ∈ Finset.range n, (1 + k ! * c j)
    have hk0 : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
    have hD1 : 1 ≤ D := Finset.one_le_prod₀ fun j _ => by
      have := hc j; nlinarith
    have hIH := ih (fun j hj => hR j (by omega)) (fun j hj => hbR j (by omega))
    have hik' : ((i : ℕ) : ℕ∞ω) ≤ k := by exact_mod_cast hik
    rw [hP n, show (fun x => P n x + b n (P n x)) = P n + b n ∘ P n from rfl,
      iteratedFDeriv_add_apply ((hPs n).of_le hik').contDiffAt
      (((hb n).comp (hPs n)).of_le hik').contDiffAt]
    have hcomp : ‖iteratedFDeriv ℝ i (b n ∘ P n) x‖ ≤ i ! * c n * D ^ i :=
      norm_iteratedFDeriv_comp_le (hb n) (hPs n) hik' x
        (fun i' hi' => hbR n (by omega) _ (hR n (by omega)) i' (hi'.trans hik))
        (fun i' h1 h2 => hIH i' h1 (h2.trans hik))
    have hfac : (i ! : ℝ) ≤ k ! := by exact_mod_cast Nat.factorial_le hik
    have hcn := hc n
    have hDi : 0 ≤ D ^ i := by positivity
    calc ‖iteratedFDeriv ℝ i (P n) x + iteratedFDeriv ℝ i (b n ∘ P n) x‖
        ≤ D ^ i + i ! * c n * D ^ i := (norm_add_le _ _).trans (add_le_add (hIH i hi hik) hcomp)
      _ ≤ D ^ i * (1 + k ! * c n) := by nlinarith [mul_le_mul_of_nonneg_right hfac (mul_nonneg hcn hDi)]
      _ ≤ D ^ i * (1 + k ! * c n) ^ i := by
        gcongr
        exact le_self_pow₀ (by nlinarith) (by omega)
      _ = (∏ j ∈ Finset.range (n + 1), (1 + k ! * c j)) ^ i := by
        rw [Finset.prod_range_succ, mul_pow]

/-- `∏ (1 + a_j) ≤ exp (∑ a_j)`. -/
theorem prod_one_add_le_exp (n : ℕ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∏ j ∈ Finset.range n, (1 + a j) ≤ Real.exp (∑ j ∈ Finset.range n, a j) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun j _ => by linarith [ha j])
    (fun j _ => by linarith [Real.add_one_le_exp (a j)])

end SympNet
