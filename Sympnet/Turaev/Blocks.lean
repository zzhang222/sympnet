/-
  T-B: the building blocks of the Euler scheme.

  * blocks of transvections B(h, t) = Π_ρ (id + h·X_ρ(t, ·)) with B − id − h·Xa = O(h²) in C^k;
  * the exact step A(h, t) = Gt(t+h) ∘ Git(t) with A − id − h·X = O(h²) and Lip(A) ≤ 1 + hL;
  * the C^k approximation of the velocity field X by ridge fields Xa (Hornik).
-/
import Sympnet.Turaev.Ridge

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace SympNet

variable {d : ℕ}

/-! ### Generic bounds -/

/-- Compact bound of partial derivatives for a function of `(h, (t, z))`. -/
theorem exists_bound3 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : ℝ × (ℝ × X d) → Z} (hg : ContDiff ℝ ∞ g) (k : ℕ) {R : Set (X d)} (hR : IsCompact R) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ R, ∀ l ≤ k,
      ‖iteratedFDeriv ℝ l (fun z => g (h, (t, z))) y‖ ≤ C := by
  set g' : (ℝ × ℝ) × X d → Z := fun q => g (q.1.1, (q.1.2, q.2))
  have hg' : ContDiff ℝ ∞ g' :=
    hg.comp ((contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  obtain ⟨C, hC0, hC⟩ := exists_partial_bound hg' k
    ((isCompact_Icc.prod isCompact_Icc).prod hR)
  exact ⟨C, hC0, fun h hh t ht y hy l hl => hC ((h, t), y) ⟨⟨hh, ht⟩, hy⟩ l hl⟩

/-- Partial derivatives of `h² • g` in z. -/
theorem norm_iteratedFDeriv_sq_smul {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : X d → Z} (hg : ContDiff ℝ ∞ g) (h : ℝ) (l : ℕ) (y : X d) :
    ‖iteratedFDeriv ℝ l (fun z => (h ^ 2) • g z) y‖ = h ^ 2 * ‖iteratedFDeriv ℝ l g y‖ := by
  rw [show (fun z => (h ^ 2) • g z) = (h ^ 2) • g from rfl,
    iteratedFDeriv_const_smul_apply ((hg.of_le (by exact_mod_cast le_top)).contDiffAt),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]

/-! ### Ridge data and transvection blocks -/

/-- A ridge term `(a, b, Λ)`: Hamiltonian `a·τ(Λ(t, z) + b)`. -/
abbrev Ridge (d : ℕ) := ℝ × ℝ × (ℝ × X d →L[ℝ] ℝ)

/-- The z-part of the ridge direction. -/
def Ridge.ell (ρ : Ridge d) : X d →L[ℝ] ℝ := ρ.2.2.comp (ContinuousLinearMap.inr ℝ ℝ (X d))

/-- The Hamiltonian vector field of one ridge term (for `−a τ`). -/
def rterm (ρ : Ridge d) (p : ℝ × X d) : X d :=
  (-(ρ.1 * deriv bumpAct (ρ.2.2 p + ρ.2.1))) • Jop d ρ.ell

/-- The ridge approximation of the velocity field. -/
def Xa (ρs : List (Ridge d)) (p : ℝ × X d) : X d := (ρs.map fun ρ => rterm ρ p).sum

/-- The ridge Hamiltonian. -/
def Nr (ρs : List (Ridge d)) (p : ℝ × X d) : ℝ := (ρs.map fun ρ => ρ.1 * bumpAct (ρ.2.2 p + ρ.2.1)).sum

/-- One factor: z ↦ z + h·X_ρ(t, z), a transvection. -/
def tfac (ρ : Ridge d) (h t : ℝ) (z : X d) : X d := z + h • rterm ρ (t, z)

/-- A block. -/
def blk (ρs : List (Ridge d)) (h t : ℝ) : X d → X d := compList (ρs.map fun ρ => tfac ρ h t)

theorem contDiff_deriv_bumpAct : ContDiff ℝ ∞ (deriv bumpAct) := contDiff_bumpAct.deriv'

theorem contDiff_rterm (ρ : Ridge d) : ContDiff ℝ ∞ (rterm ρ) :=
  ((contDiff_const.mul (contDiff_deriv_bumpAct.comp
    (ρ.2.2.contDiff.add contDiff_const))).neg).smul contDiff_const

theorem contDiff_Xa (ρs : List (Ridge d)) : ContDiff ℝ ∞ (Xa ρs) := by
  unfold Xa
  induction ρs with
  | nil => simpa using contDiff_const
  | cons ρ ρs ih => simpa using (contDiff_rterm ρ).add ih

theorem contDiff_Nr (ρs : List (Ridge d)) : ContDiff ℝ ∞ (Nr ρs) := by
  unfold Nr
  induction ρs with
  | nil => simpa using contDiff_const
  | cons ρ ρs ih =>
    simpa using (contDiff_const.mul (contDiff_bumpAct.comp (ρ.2.2.contDiff.add contDiff_const))).add ih

theorem tfac_mem (ρ : Ridge d) (h t : ℝ) : tfac ρ h t ∈ ShearProd d := by
  set c := ρ.2.2 (t, 0) + ρ.2.1
  set φ : ℝ → ℝ := fun u => -(h * ρ.1) * bumpAct (u + c)
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.mul (contDiff_bumpAct.comp (contDiff_id.add contDiff_const))
  have h1 := transv_mem hφ ρ.ell
  convert h1 using 1
  funext z
  have hd' : ∀ u, HasDerivAt φ (-(h * ρ.1) * deriv bumpAct (u + c)) u := fun u => by
    have h0 := ((contDiff_bumpAct.differentiable (by simp)) (u + c)).hasDerivAt
    exact (h0.comp_add_const u c).const_mul (-(h * ρ.1))
  have hd : deriv φ (ρ.ell z) = -(h * ρ.1) * deriv bumpAct (ρ.2.2 (t, z) + ρ.2.1) := by
    have : ρ.2.2 (t, z) = ρ.2.2 (t, 0) + ρ.ell z := by
      rw [Ridge.ell, ContinuousLinearMap.comp_apply, ← map_add]; simp
    rw [(hd' _).deriv, this]
    congr 2; simp only [c]; ring
  simp only [tfac, transv, rterm, hd, smul_smul]
  congr 2; ring

theorem blk_mem (ρs : List (Ridge d)) (h t : ℝ) : blk ρs h t ∈ ShearProd d := by
  unfold blk
  induction ρs with
  | nil => exact ShearProd.id_mem
  | cons ρ ρs ih => exact ShearProd.comp (tfac_mem ρ h t) ih

theorem blk_cons (ρ : Ridge d) (ρs : List (Ridge d)) (h t : ℝ) :
    blk (ρ :: ρs) h t = blk ρs h t ∘ tfac ρ h t := rfl

theorem blk_zero (ρs : List (Ridge d)) (t : ℝ) : blk ρs 0 t = id := by
  induction ρs with
  | nil => rfl
  | cons ρ ρs ih => rw [blk_cons, ih]; funext z; simp [tfac]

/-- The block as a function of `(h, (t, z))`. -/
def blkF (ρs : List (Ridge d)) (q : ℝ × (ℝ × X d)) : X d := blk ρs q.1 q.2.1 q.2.2

theorem contDiff_blkF (ρs : List (Ridge d)) : ContDiff ℝ ∞ (blkF (d := d) ρs) := by
  induction ρs with
  | nil => exact contDiff_snd.comp contDiff_snd
  | cons ρ ρs ih =>
    have ht : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × X d) => tfac ρ q.1 q.2.1 q.2.2) :=
      (contDiff_snd.comp contDiff_snd).add (contDiff_fst.smul ((contDiff_rterm ρ).comp
        ((contDiff_fst.comp contDiff_snd).prodMk (contDiff_snd.comp contDiff_snd))))
    have : blkF (ρ :: ρs) = fun q => blkF ρs (q.1, (q.2.1, tfac ρ q.1 q.2.1 q.2.2)) := rfl
    rw [this]
    exact ih.comp (contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).prodMk ht))

/-- ∂ₕ B(0, t) z = Xa(t, z). -/
theorem hasDerivAt_blk (ρs : List (Ridge d)) (t : ℝ) (z : X d) :
    HasDerivAt (fun h => blk ρs h t z) (Xa ρs (t, z)) 0 := by
  induction ρs generalizing z with
  | nil => simpa [blk, Xa, compList] using hasDerivAt_const (0 : ℝ) z
  | cons ρ ρs ih =>
    set Φ : ℝ × X d → X d := fun q => blk ρs q.1 t q.2
    have hΦ : ContDiff ℝ ∞ Φ := by
      have h2 : ContDiff ℝ ∞ (fun q : ℝ × X d => ((q.1, (t, q.2)) : ℝ × (ℝ × X d))) :=
        contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
      have h3 := (contDiff_blkF ρs).comp h2
      simp only [Function.comp_def, blkF] at h3
      exact h3
    set D := fderiv ℝ Φ (0, z)
    have hγ : HasDerivAt (fun h : ℝ => ((h, tfac ρ h t z) : ℝ × X d)) ((1, rterm ρ (t, z))) 0 := by
      refine (hasDerivAt_id 0).prodMk ?_
      exact (((hasDerivAt_id (0 : ℝ)).smul_const (rterm ρ (t, z))).const_add z).congr_deriv
        (by simp)
    have hc := ((hΦ.differentiable (by simp)) (0, z)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ
      (by simp [tfac])
    have h1 : D (1, 0) = Xa ρs (t, z) :=
      (dT_eq_deriv (p := ((0 : ℝ), z)) ((hΦ.differentiable (by simp)) _)).unique (ih z)
    have h2 : D (0, rterm ρ (t, z)) = rterm ρ (t, z) := by
      have hs := hasFDerivAt_partial (t := 0) (x := z) ((hΦ.differentiable (by simp)) (0, z))
      have he : (fun y => Φ (0, y)) = id := by funext y; simp [Φ, blk_zero]
      rw [he] at hs
      have := congrArg (fun L : X d →L[ℝ] X d => L (rterm ρ (t, z))) (hs.unique (hasFDerivAt_id z))
      simpa using this
    have hD : D (1, rterm ρ (t, z)) = Xa (ρ :: ρs) (t, z) := by
      have : ((1, rterm ρ (t, z)) : ℝ × X d) = (1, 0) + (0, rterm ρ (t, z)) := by simp
      rw [this, map_add, h1, h2]; simp [Xa, add_comm]
    rw [← hD]
    exact hc

/-- **Block estimate**: B(h, t) − id − h Xa(t, ·) = O(h²) in C^k on compacts. -/
theorem blk_estimate (ρs : List (Ridge d)) (k : ℕ) {R : Set (X d)} (hR : IsCompact R) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ R, ∀ l ≤ k,
      ‖iteratedFDeriv ℝ l (fun z => blk ρs h t z - z - h • Xa ρs (t, z)) y‖ ≤ h ^ 2 * C := by
  set f : ℝ × (ℝ × X d) → X d := fun q => blkF ρs q - q.2.2 - q.1 • Xa ρs q.2
  have hf : ContDiff ℝ ∞ f :=
    ((contDiff_blkF ρs).sub (contDiff_snd.comp contDiff_snd)).sub
      (contDiff_fst.smul ((contDiff_Xa ρs).comp contDiff_snd))
  have hf0 : ∀ y, f (0, y) = 0 := fun y => by simp [f, blkF, blk_zero]
  have hf1 : ∀ y, dT f (0, y) = 0 := by
    intro y
    have h1 := dT_eq_deriv (p := ((0 : ℝ), y)) ((hf.differentiable (by simp)) _)
    have h2 : HasDerivAt (fun h => f (h, y)) 0 0 := by
      have := (((hasDerivAt_blk ρs y.1 y.2).sub (hasDerivAt_const (0 : ℝ) y.2)).sub
        ((hasDerivAt_id (0 : ℝ)).smul_const (Xa ρs y))).congr_deriv
        (show Xa ρs y - 0 - (1 : ℝ) • Xa ρs y = 0 by simp)
      exact this
    exact h1.unique h2
  set g := hadQ (hadQ f)
  have hg : ContDiff ℝ ∞ g := contDiff_hadQ (contDiff_hadQ hf)
  obtain ⟨C, hC0, hC⟩ := exists_bound3 hg k hR
  refine ⟨C, hC0, fun h hh t ht y hy l hl => ?_⟩
  have he : (fun z => blk ρs h t z - z - h • Xa ρs (t, z)) = fun z => (h ^ 2) • g (h, (t, z)) := by
    funext z
    exact hadamard2_eq hf hf0 hf1 (h, (t, z))
  have hgs : ContDiff ℝ ∞ (fun z => g (h, (t, z))) := by
    have h2 : ContDiff ℝ ∞ (fun z : X d => ((h, (t, z)) : ℝ × (ℝ × X d))) :=
      contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
    exact hg.comp h2
  rw [he, norm_iteratedFDeriv_sq_smul hgs]
  exact mul_le_mul_of_nonneg_left (hC h hh t ht y hy l hl) (sq_nonneg h)

end SympNet
