/-
  H4: uniform density of nets on compact subsets of ℝ^m.

  Exponentials x ↦ exp(w·x) span a point-separating subalgebra (Stone–Weierstrass), and each is a
  ridge function, hence a uniform limit of nets by the 1D result.
-/
import Sympnet.Hornik.OneDimNP

open Set Filter Topology Metric

noncomputable section

namespace SympNet

/-- f is uniformly approximable by nets on every compact set. -/
def UApproxM (τ : ℝ → ℝ) (m : ℕ) (f : E m → ℝ) : Prop :=
  ∀ K : Set (E m), IsCompact K → ∀ ε > 0, ∃ g ∈ netSpan τ m, ∀ x ∈ K, |f x - g x| < ε

namespace UApproxM
variable {τ : ℝ → ℝ} {m : ℕ} {f g : E m → ℝ}

theorem zero : UApproxM τ m 0 :=
  fun _ _ ε hε => ⟨0, (netSpan τ m).zero_mem, fun x _ => by simpa using hε⟩

theorem add (hf : UApproxM τ m f) (hg : UApproxM τ m g) : UApproxM τ m (f + g) := by
  intro K hK ε hε
  obtain ⟨f', hf', h1⟩ := hf K hK (ε / 2) (half_pos hε)
  obtain ⟨g', hg', h2⟩ := hg K hK (ε / 2) (half_pos hε)
  refine ⟨f' + g', (netSpan τ m).add_mem hf' hg', fun x hx => ?_⟩
  calc |(f + g) x - (f' + g') x| = |(f x - f' x) + (g x - g' x)| := by simp; ring_nf
    _ ≤ |f x - f' x| + |g x - g' x| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h1 x hx) (h2 x hx)
    _ = ε := add_halves ε

theorem smul (c : ℝ) (hf : UApproxM τ m f) : UApproxM τ m (c • f) := by
  intro K hK ε hε
  obtain ⟨f', hf', h1⟩ := hf K hK (ε / (|c| + 1)) (by positivity)
  refine ⟨c • f', (netSpan τ m).smul_mem c hf', fun x hx => ?_⟩
  have h := h1 x hx
  calc |(c • f) x - (c • f') x| = |c| * |f x - f' x| := by
        simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_sub, abs_mul]
    _ ≤ (|c| + 1) * |f x - f' x| := by gcongr; linarith
    _ < (|c| + 1) * (ε / (|c| + 1)) := by gcongr
    _ = ε := by field_simp

end UApproxM

theorem continuous_dot {m : ℕ} (w : E m) : Continuous fun x : E m => dotProduct w x :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

/-- Exponential ridge functions are approximable. -/
theorem uapproxM_exp {r : ℕ} {τ : ℝ → ℝ} (hτ : RFinite r τ) {m : ℕ} (w : E m) :
    UApproxM τ m (fun x => Real.exp (dotProduct w x)) := by
  intro K hK ε hε
  have hcont : Continuous fun x : E m => dotProduct w x := continuous_dot w
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨g₁, hg₁, h₁⟩ := oneDim_dense hτ Real.continuous_exp R ε hε
  refine ⟨fun x => g₁ (dotProduct w x), netSpan1_comp_dot hg₁ w, fun x hx => h₁ _ ?_⟩
  have := hR x hx
  rw [Real.norm_eq_abs, abs_le] at this
  exact ⟨this.1, this.2⟩

/-- The span of exponential ridge functions. -/
def expSpan (m : ℕ) : Submodule ℝ (E m → ℝ) :=
  Submodule.span ℝ (range fun w : E m => fun x => Real.exp (dotProduct w x))

theorem exp_mem_expSpan {m : ℕ} (w : E m) : (fun x => Real.exp (dotProduct w x)) ∈ expSpan m :=
  Submodule.subset_span ⟨w, rfl⟩

theorem one_mem_expSpan {m : ℕ} : (1 : E m → ℝ) ∈ expSpan m := by
  have h : (fun x : E m => Real.exp (dotProduct (0 : E m) x)) = 1 := by funext x; simp
  rw [← h]; exact exp_mem_expSpan 0

theorem mul_mem_expSpan {m : ℕ} {f g : E m → ℝ} (hf : f ∈ expSpan m) (hg : g ∈ expSpan m) :
    f * g ∈ expSpan m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨w', rfl⟩ := hg
      have : ((fun x => Real.exp (dotProduct w x)) * fun x => Real.exp (dotProduct w' x)) =
          fun x => Real.exp (dotProduct (w + w') x) := by
        funext x; simp [add_dotProduct, Real.exp_add]
      rw [this]; exact exp_mem_expSpan _
    | zero => simpa using (expSpan m).zero_mem
    | add g g' _ _ h1 h2 => rw [mul_add]; exact (expSpan m).add_mem h1 h2
    | smul c g _ h => rw [mul_smul_comm]; exact (expSpan m).smul_mem c h
  | zero => simpa using (expSpan m).zero_mem
  | add f f' _ _ h1 h2 => rw [add_mul]; exact (expSpan m).add_mem h1 h2
  | smul c f _ h => rw [smul_mul_assoc]; exact (expSpan m).smul_mem c h

theorem uapproxM_of_mem_expSpan {r : ℕ} {τ : ℝ → ℝ} (hτ : RFinite r τ) {m : ℕ} {f : E m → ℝ}
    (hf : f ∈ expSpan m) : UApproxM τ m f := by
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨w, rfl⟩ := hf; exact uapproxM_exp hτ w
  | zero => exact UApproxM.zero
  | add f g _ _ h1 h2 => exact h1.add h2
  | smul c f _ h => exact h.smul c

theorem continuous_of_mem_expSpan {m : ℕ} {f : E m → ℝ} (hf : f ∈ expSpan m) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, rfl⟩ := hf
    exact Real.continuous_exp.comp (continuous_dot w)
  | zero => exact continuous_const
  | add f g _ _ h1 h2 => exact h1.add h2
  | smul c f _ h => exact h.const_smul c

/-- **Stone–Weierstrass for exponentials** on a compact set. -/
theorem exists_expSpan_near {m : ℕ} {K : Set (E m)} (hK : IsCompact K) {f : E m → ℝ}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ F ∈ expSpan m, ∀ x ∈ K, |f x - F x| < ε := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let A : Subalgebra ℝ C(K, ℝ) :=
    { carrier := {h | ∃ F ∈ expSpan m, ∀ x : K, h x = F x}
      mul_mem' := by
        rintro a b ⟨F, hF, ha⟩ ⟨G, hG, hb⟩
        exact ⟨F * G, mul_mem_expSpan hF hG, fun x => by simp [ha x, hb x]⟩
      add_mem' := by
        rintro a b ⟨F, hF, ha⟩ ⟨G, hG, hb⟩
        exact ⟨F + G, (expSpan m).add_mem hF hG, fun x => by simp [ha x, hb x]⟩
      algebraMap_mem' := by
        intro c
        exact ⟨c • 1, (expSpan m).smul_mem c one_mem_expSpan, fun x => by simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have hne : (x : E m) ≠ y := fun h => hxy (Subtype.ext h)
    obtain ⟨i, hi⟩ : ∃ i, (x : E m) i ≠ (y : E m) i := by
      by_contra h; push Not at h; exact hne (funext h)
    let h : C(K, ℝ) := ⟨fun z => Real.exp (dotProduct (Pi.single i 1) (z : E m)),
      Real.continuous_exp.comp ((continuous_dot _).comp continuous_subtype_val)⟩
    refine ⟨h, ⟨h, ⟨fun z => Real.exp (dotProduct (Pi.single i 1) z), exp_mem_expSpan _,
      fun z => rfl⟩, rfl⟩, ?_⟩
    simp only [h, ContinuousMap.coe_mk, single_dotProduct, one_mul]
    exact fun he => hi (Real.exp_injective he)
  obtain ⟨⟨g, ⟨F, hF, hg⟩⟩, hgf⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hsep
      (fun x : K => f x) (hf.comp continuous_subtype_val) ε hε
  refine ⟨F, hF, fun x hx => ?_⟩
  have := hgf ⟨x, hx⟩
  simp only [hg, Real.norm_eq_abs] at this
  rw [abs_sub_comm]; exact this

/-- **Uniform density of nets in ℝ^m** for an r-finite activation. -/
theorem multiC0_dense {r : ℕ} {τ : ℝ → ℝ} (hτ : RFinite r τ) {m : ℕ} {f : E m → ℝ}
    (hf : Continuous f) : UApproxM τ m f := by
  intro K hK ε hε
  obtain ⟨F, hF, h1⟩ := exists_expSpan_near hK hf (half_pos hε)
  obtain ⟨g, hg, h2⟩ := uapproxM_of_mem_expSpan hτ hF K hK (ε / 2) (half_pos hε)
  refine ⟨g, hg, fun x hx => ?_⟩
  calc |f x - g x| ≤ |f x - F x| + |F x - g x| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h1 x hx) (h2 x hx)
    _ = ε := add_halves ε

end SympNet
