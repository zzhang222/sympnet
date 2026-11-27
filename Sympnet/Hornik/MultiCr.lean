/-
  H5b: C^r density of nets on compact subsets of ℝ^m, i.e. **Hornik–Stinchcombe–White** (the
  paper's Lemma 2), and the final form of Theorem 5.

  V ≈ Ṽ := χV (cutoff) ≈ φ ⋆ Ṽ (mollify) ≈ q ⋆ Ṽ (q a net uniformly close to φ, `conv_close`)
    = Ṽ ⋆ q̃ near K ≈ Σ cᵢ q(· − yᵢ) (`riemann_close`), which is a net.
-/
import Sympnet.Hornik.ConvTools
import Sympnet.Hornik.MultiC0
import Sympnet.Smoothing.SymplecticApprox

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff Convolution

noncomputable section

namespace SympNet

variable {m : ℕ}

local notation "μH" => (Measure.addHaar : Measure (E m))

theorem exists_common_delta (r : ℕ) (P : ℕ → ℝ → Prop)
    (hmono : ∀ i δ δ', P i δ → 0 < δ' → δ' ≤ δ → P i δ') (h : ∀ i ≤ r, ∃ δ > 0, P i δ) :
    ∃ δ > 0, ∀ i ≤ r, P i δ := by
  induction r with
  | zero =>
    obtain ⟨δ, hδ, hP⟩ := h 0 le_rfl
    exact ⟨δ, hδ, fun i hi => by obtain rfl := Nat.le_zero.1 hi; exact hP⟩
  | succ r ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih fun i hi => h i (by omega)
    obtain ⟨δ₂, hδ₂, h₂⟩ := h (r + 1) le_rfl
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i (r + 1) with h' | h'
    · exact hmono i δ₁ _ (h₁ i (by omega)) (lt_min hδ₁ hδ₂) (min_le_left _ _)
    · obtain rfl : i = r + 1 := by omega
      exact hmono _ δ₂ _ h₂ (lt_min hδ₁ hδ₂) (min_le_right _ _)

theorem lsmul_flip_eq : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
    ContinuousLinearMap.lsmul ℝ ℝ := by
  ext a b; simp [mul_comm]

theorem norm_sub_le_three {F : Type*} [NormedAddCommGroup F] (a b c e : F) :
    ‖a - e‖ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - e‖ :=
  calc ‖a - e‖ ≤ ‖a - c‖ + ‖c - e‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖a - b‖ + ‖b - c‖ + ‖c - e‖ := by
        gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- **C^r density of nets** (Hornik–Stinchcombe–White). -/
theorem multiCr_dense {r : ℕ} {τ : ℝ → ℝ} (hτ : RFinite r τ) {V : E m → ℝ} (hV : ContDiff ℝ r V)
    {K : Set (E m)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ netSpan τ m, CrClose r K V g ε := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => (hR₀ x hx).trans (le_max_left _ _)
  set ε' := ε / 5
  have hε' : 0 < ε' := by positivity
  -- cutoff of V
  let χ : ContDiffBump (0 : E m) := ⟨R + 1, R + 2, by positivity, by linarith⟩
  set Vt : E m → ℝ := fun x => χ x * V x
  have hVt : ContDiff ℝ r Vt := χ.contDiff.mul hV
  have hVtc : HasCompactSupport Vt := χ.hasCompactSupport.mul_right
  have hVts : tsupport Vt ⊆ closedBall 0 (R + 2) := by
    refine (tsupport_mul_subset_left (f := fun x => χ x)).trans ?_
    rw [χ.tsupport_eq]
  have hVtV : ∀ x ∈ K, Vt =ᶠ[𝓝 x] V := by
    intro x hx
    have hb : ball (0 : E m) (R + 1) ∈ 𝓝 x :=
      isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; linarith [hKR x hx])
    filter_upwards [hb] with y hy
    simp only [Vt, χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  have hVi : Integrable Vt μH := hVt.continuous.integrable_of_hasCompactSupport hVtc
  -- mollification
  obtain ⟨δ₁, hδ₁, h₁⟩ := moll_close r Vt hVt hVtc ε' hε'
  let φ : ContDiffBump (0 : E m) := ⟨δ₁ / 2, δ₁, half_pos hδ₁, half_lt_self hδ₁⟩
  have hM := h₁ φ le_rfl
  -- uniform approximation of the bump by a net
  set B := ∑ i ∈ Finset.range (r + 1), ∫ y, ‖iteratedFDeriv ℝ i Vt y‖ ∂μH
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => norm_nonneg _
  have hB : ∀ i ≤ r, ∫ y, ‖iteratedFDeriv ℝ i Vt y‖ ∂μH ≤ B := fun i hi =>
    Finset.single_le_sum (f := fun i => ∫ y, ‖iteratedFDeriv ℝ i Vt y‖ ∂μH)
      (fun i _ => integral_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  set η := ε' / (B + 1)
  have hη : 0 < η := by positivity
  obtain ⟨q, hq, hqφ⟩ := multiC0_dense hτ (m := m) φ.continuous_normed
    (closedBall 0 (R + (R + 2))) (isCompact_closedBall _ _) η hη
  have hqs : ContDiff ℝ r q := contDiff_of_mem_netSpan hτ.1 hq
  have hC := conv_close r (m := m) (R := R) (ρ₀ := R + 2) hη.le φ.continuous_normed hqs.continuous
    (fun t ht => (hqφ t ht).le) Vt hVt hVtc hVts B hB
  have hηB : η * B ≤ ε' := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  -- q ⋆ Ṽ = Ṽ ⋆ q̃ near K
  have hflip : q ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] Vt =
      Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] q := by
    rw [← convolution_flip, lsmul_flip_eq]
  let χ₂ : ContDiffBump (0 : E m) := ⟨2 * R + 3, 2 * R + 4, by positivity, by linarith⟩
  set qt : E m → ℝ := fun x => χ₂ x * q x
  have hqt : ContDiff ℝ r qt := χ₂.contDiff.mul hqs
  have hqtc : HasCompactSupport qt := χ₂.hasCompactSupport.mul_right
  have hqtq : ∀ z, ‖z‖ < 2 * R + 3 → qt z = q z := fun z hz => by
    simp only [qt]
    rw [χ₂.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hz.le), one_mul]
  have hsuppV : ∀ t, Vt t ≠ 0 → ‖t‖ ≤ R + 2 := fun t ht => by
    have := hVts (subset_tsupport _ ht); rwa [mem_closedBall, dist_zero_right] at this
  have hconvq : ∀ x, ‖x‖ < R + 1 → (Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] q) x =
      (Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] qt) x := by
    intro x hx
    simp only [convolution_def]
    congr 1; funext t
    by_cases ht : Vt t = 0
    · simp [ht]
    · rw [hqtq]
      calc ‖x - t‖ ≤ ‖x‖ + ‖t‖ := norm_sub_le _ _
        _ < R + 1 + (R + 2) := add_lt_add_of_lt_of_le hx (hsuppV t ht)
        _ = 2 * R + 3 := by ring
  -- finite sums
  set Iv := ∫ t, |Vt t| ∂μH
  set η₀ := ε' / (Iv + 1)
  have hIv : 0 ≤ Iv := integral_nonneg fun _ => abs_nonneg _
  have hη₀ : 0 < η₀ := by positivity
  obtain ⟨δ₂, hδ₂, hmod⟩ := exists_common_delta r
    (fun i δ => ∀ u v, dist u v < δ → ‖iteratedFDeriv ℝ i qt u - iteratedFDeriv ℝ i qt v‖ ≤ η₀)
    (fun i δ δ' hP _ hle u v huv => hP u v (lt_of_lt_of_le huv hle))
    (fun i hi => by
      have hcont : Continuous (iteratedFDeriv ℝ i qt) :=
        hqt.continuous_iteratedFDeriv (by exact_mod_cast hi)
      obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1
        ((hqtc.iteratedFDeriv i).uniformContinuous_of_continuous hcont) η₀ hη₀
      exact ⟨δ, hδ, fun u v huv => by
        have := hδ' huv; rw [dist_eq_norm] at this; exact this.le⟩)
  obtain ⟨n, y, c, hyL, hsum⟩ := exists_finite_sum_approx μH hVi (isCompact_closedBall 0 (R + 2))
    (fun t ht => image_eq_zero_of_notMem_tsupport fun h => ht (hVts h)) hδ₂
  have hRS := riemann_close r (Vt := Vt) hVi hsum qt hqt hqtc hmod
  have hη₀I : η₀ * Iv ≤ ε' := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  -- the net
  set N : E m → ℝ := fun x => ∑ i, c i * q (x - y i)
  have hN : N ∈ netSpan τ m := netSpan_sum_translate hq c y
  refine ⟨N, hN, fun k hk x hx => ?_⟩
  have hxR : ‖x‖ < R + 1 := by linarith [hKR x hx]
  have hnear : ∀ᶠ z in 𝓝 x, ‖z‖ < R + 1 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hxR
  have e1 : iteratedFDeriv ℝ k V x = iteratedFDeriv ℝ k Vt x :=
    ((hVtV x hx).iteratedFDeriv ℝ k).eq_of_nhds.symm
  have e2 : iteratedFDeriv ℝ k (q ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] Vt) x =
      iteratedFDeriv ℝ k (Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] qt) x := by
    rw [hflip]
    exact ((show (Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] q) =ᶠ[𝓝 x]
      (Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] qt) from
        hnear.mono fun z hz => hconvq z hz).iteratedFDeriv ℝ k).eq_of_nhds
  have hev3 : N =ᶠ[𝓝 x] (fun z => ∑ i, c i • qt (z - y i)) := by
    refine hnear.mono fun z hz => ?_
    simp only [N, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hqtq]
    have hyi : ‖y i‖ ≤ R + 2 := by
      have := hyL i; rwa [mem_closedBall, dist_zero_right] at this
    calc ‖z - y i‖ ≤ ‖z‖ + ‖y i‖ := norm_sub_le _ _
      _ < R + 1 + (R + 2) := add_lt_add_of_lt_of_le hz hyi
      _ = 2 * R + 3 := by ring
  have e3 : iteratedFDeriv ℝ k N x = iteratedFDeriv ℝ k (fun z => ∑ i, c i • qt (z - y i)) x :=
    (hev3.iteratedFDeriv ℝ k).eq_of_nhds
  have b1 := hM k hk x (mem_univ x)
  have b2 := hC k hk x (by rw [mem_closedBall, dist_zero_right]; exact hKR x hx)
  have b3 := hRS k hk x (mem_univ x)
  rw [e1, e3]
  rw [e2] at b2
  calc ‖iteratedFDeriv ℝ k Vt x - iteratedFDeriv ℝ k (fun z => ∑ i, c i • qt (z - y i)) x‖
      ≤ ‖iteratedFDeriv ℝ k Vt x -
          iteratedFDeriv ℝ k (φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] Vt) x‖ +
        ‖iteratedFDeriv ℝ k (φ.normed μH ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] Vt) x -
          iteratedFDeriv ℝ k (Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] qt) x‖ +
        ‖iteratedFDeriv ℝ k (Vt ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μH] qt) x -
          iteratedFDeriv ℝ k (fun z => ∑ i, c i • qt (z - y i)) x‖ :=
        norm_sub_le_three _ _ _ _
    _ ≤ ε' + ε' + ε' := by
        rw [norm_sub_rev] at b1
        exact add_le_add (add_le_add b1 (b2.trans hηB)) (b3.trans hη₀I)
    _ < ε := by simp only [ε']; linarith

/-- **Lemma 2 (Hornik–Stinchcombe–White 1990) is a theorem.** -/
theorem hornikDensity : HornikDensity := by
  intro m r τ hτ V hV K hK ε hε
  obtain ⟨g, hg, hc⟩ := multiCr_dense hτ hV hK hε
  obtain ⟨n, W, a, b, rfl⟩ := exists_shallowNet_of_mem hg
  exact ⟨n, W, a, b, hc⟩

/-- **Theorem 5 (convex U, injective maps), assuming only Turaev's theorem as Turaev states it.** -/
theorem G_SympNet_universal_final (hT : TuraevLiteral) {d : ℕ}
    (r : ℕ) (hr : 1 ≤ r) (σ : ℝ → ℝ) (hσ : RFinite r σ)
    (U : Set (X d)) (hU : IsOpen U) (hUc : Convex ℝ U) :
    UDense r U (GSympNet (d := d) σ) {F | F ∈ SP r U ∧ Set.InjOn F U} :=
  G_SympNet_universal_turaev hornikDensity hT r hr σ hσ U hU hUc

end SympNet
