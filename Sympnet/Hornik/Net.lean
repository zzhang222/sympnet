/-
  H1: networks as a linear span of units.

  `netSpan τ m` is the span of the units x ↦ τ(w·x + b) on ℝ^m, `netSpan1 τ` the span of
  s ↦ τ(c s + b) on ℝ. Both are closed under translation/affine substitution, 1D nets composed with
  a linear form are m-dimensional nets, and every element of `netSpan τ m` is a `shallowNet`.
-/
import Sympnet.SympNetUniversal

open Set
open scoped ContDiff

noncomputable section

namespace SympNet

variable {d : ℕ}

/-- The span of the units x ↦ τ(w·x + b). -/
def netSpan (τ : ℝ → ℝ) (m : ℕ) : Submodule ℝ (E m → ℝ) :=
  Submodule.span ℝ (range fun p : E m × ℝ => fun x => τ (dotProduct p.1 x + p.2))

/-- The span of the 1D units s ↦ τ(c s + b). -/
def netSpan1 (τ : ℝ → ℝ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ (range fun p : ℝ × ℝ => fun s => τ (p.1 * s + p.2))

theorem unit_mem_netSpan (τ : ℝ → ℝ) {m : ℕ} (w : E m) (b : ℝ) :
    (fun x => τ (dotProduct w x + b)) ∈ netSpan τ m :=
  Submodule.subset_span ⟨(w, b), rfl⟩

theorem unit_mem_netSpan1 (τ : ℝ → ℝ) (c b : ℝ) : (fun s => τ (c * s + b)) ∈ netSpan1 τ :=
  Submodule.subset_span ⟨(c, b), rfl⟩

/-- Translation invariance. -/
theorem netSpan_translate {τ : ℝ → ℝ} {m : ℕ} {f : E m → ℝ} (hf : f ∈ netSpan τ m) (y : E m) :
    (fun x => f (x + y)) ∈ netSpan τ m := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨w, b⟩, rfl⟩ := hg
    have : (fun x => τ (dotProduct w (x + y) + b)) = fun x => τ (dotProduct w x + (dotProduct w y + b)) := by
      funext x; rw [dotProduct_add]; ring_nf
    simp only at this ⊢
    rw [this]; exact unit_mem_netSpan τ w _
  | zero => exact (netSpan τ m).zero_mem
  | add f g _ _ hf hg => exact (netSpan τ m).add_mem hf hg
  | smul c f _ hf => exact (netSpan τ m).smul_mem c hf

theorem netSpan_sub_translate {τ : ℝ → ℝ} {m : ℕ} {f : E m → ℝ} (hf : f ∈ netSpan τ m) (y : E m) :
    (fun x => f (x - y)) ∈ netSpan τ m := by
  simpa [sub_eq_add_neg] using netSpan_translate hf (-y)

/-- Affine substitution in 1D. -/
theorem netSpan1_affine {τ : ℝ → ℝ} {g : ℝ → ℝ} (hg : g ∈ netSpan1 τ) (c b : ℝ) :
    (fun s => g (c * s + b)) ∈ netSpan1 τ := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨c', b'⟩, rfl⟩ := hg
    have : (fun s => τ (c' * (c * s + b) + b')) = fun s => τ ((c' * c) * s + (c' * b + b')) := by
      funext s; ring_nf
    simp only at this ⊢
    rw [this]; exact unit_mem_netSpan1 τ _ _
  | zero => exact (netSpan1 τ).zero_mem
  | add f g _ _ hf hg => exact (netSpan1 τ).add_mem hf hg
  | smul a f _ hf => exact (netSpan1 τ).smul_mem a hf

/-- A 1D net composed with a linear form is an m-dimensional net. -/
theorem netSpan1_comp_dot {τ : ℝ → ℝ} {g : ℝ → ℝ} (hg : g ∈ netSpan1 τ) {m : ℕ} (w : E m) :
    (fun x => g (dotProduct w x)) ∈ netSpan τ m := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨c, b⟩, rfl⟩ := hg
    have : (fun x => τ (c * dotProduct w x + b)) = fun x => τ (dotProduct (c • w) x + b) := by
      funext x; rw [smul_dotProduct, smul_eq_mul]
    simp only at this ⊢
    rw [this]; exact unit_mem_netSpan τ _ _
  | zero => exact (netSpan τ m).zero_mem
  | add f g _ _ hf hg => exact (netSpan τ m).add_mem hf hg
  | smul a f _ hf => exact (netSpan τ m).smul_mem a hf

/-- Finite combinations of translates of a net are nets. -/
theorem netSpan_sum_translate {τ : ℝ → ℝ} {m n : ℕ} {f : E m → ℝ} (hf : f ∈ netSpan τ m)
    (c : Fin n → ℝ) (y : Fin n → E m) :
    (fun x => ∑ i, c i * f (x - y i)) ∈ netSpan τ m := by
  have : (fun x => ∑ i, c i * f (x - y i)) = ∑ i, c i • (fun x => f (x - y i)) := by
    funext x; simp [Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => (netSpan τ m).smul_mem _ (netSpan_sub_translate hf _)

/-- Every net is a `shallowNet`. -/
theorem exists_shallowNet_of_mem {τ : ℝ → ℝ} {m : ℕ} {f : E m → ℝ} (hf : f ∈ netSpan τ m) :
    ∃ (n : ℕ) (W : Matrix (Fin n) (Fin m) ℝ) (a b : Fin n → ℝ), f = shallowNet τ W a b := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨w, b⟩, rfl⟩ := hg
    refine ⟨1, Matrix.of fun _ i => w i, fun _ => 1, fun _ => b, ?_⟩
    funext x
    simp [shallowNet, Matrix.mulVec, dotProduct]
  | zero => exact ⟨0, 0, 0, 0, by funext x; simp [shallowNet]⟩
  | add f g _ _ hf hg =>
    obtain ⟨n, W, a, b, rfl⟩ := hf
    obtain ⟨n', W', a', b', rfl⟩ := hg
    refine ⟨n + n', Matrix.of (Fin.append (fun j => W j) (fun j => W' j)), Fin.append a a',
      Fin.append b b', ?_⟩
    funext x
    simp only [Pi.add_apply, shallowNet, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Matrix.mulVec, Matrix.of_apply]
  | smul c f _ hf =>
    obtain ⟨n, W, a, b, rfl⟩ := hf
    refine ⟨n, W, c • a, b, ?_⟩
    funext x
    simp [shallowNet, Finset.mul_sum, mul_assoc]

theorem contDiff_of_mem_netSpan {τ : ℝ → ℝ} {m : ℕ} {r : ℕ∞ω} (hτ : ContDiff ℝ r τ)
    {f : E m → ℝ} (hf : f ∈ netSpan τ m) : ContDiff ℝ r f := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨w, b⟩, rfl⟩ := hg
    have : ContDiff ℝ r (fun x : E m => dotProduct w x + b) := by
      simp only [dotProduct]; fun_prop
    exact hτ.comp this
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact contDiff_const.smul hf

end SympNet
