/-
  Formalization of the main theorem of Appendix A of

    P. Jin, Z. Zhang, A. Zhu, Y. Tang, G. E. Karniadakis,
    "SympNets: Intrinsic structure-preserving symplectic networks for
     identifying Hamiltonian systems", arXiv:2001.03750v3.

  Main result formalized: **Theorem 5** (approximation theorem for G-SympNets), for convex U and
    injective maps: for r ≥ 1, U ⊆ ℝ^{2d} open and convex, and an r-finite activation σ, the
    G-SympNets are r-uniformly dense on compacta in {F ∈ SP^r(U) | F injective on U}.
    The paper claims this for all of SP^r(U) and arbitrary open U. That is false
    (G-SympNets are injective, maps in SP^r(U) need not be; see `Sympnet/Counterexample.lean`).
    The error is in Lemma 4, which overstates Turaev's theorem.

  How this file is organized
  --------------------------
  * §1  Definitions: phase space, symplectic maps SP^r(U), C^r-closeness on a compact
        set, "r-uniformly dense on compacta", r-finite activations, gradient modules,
        G-SympNets, Hénon-like maps.
  * §2  The two external results that the paper cites without proof, stated as `Prop`s:
          - `HornikDensity`  (Lemma 2, Hornik–Stinchcombe–White 1990)
          - `TuraevHenon`    (Lemma 4, Turaev 2003, for convex U and injective F)
        plus `TuraevHenonPaper`, the paper's (false) Lemma 4, kept for reference.
        `G_SympNet_universal` below takes `HornikDensity` and `TuraevHenon` as hypotheses.
        Both are now *proved*:
          - `hornikDensity : HornikDensity`            (`Sympnet/Hornik/`);
          - `turaevHenon : TuraevHenon`                (`Sympnet/Turaev/`, via `symplecticApprox`
            and `turaevShear`, a version of Turaev's theorem with shears instead of his iterates).
        Final result, with no hypotheses: `G_SympNet_universal_unconditional` in
        `Sympnet/Turaev/Main.lean`.
  * §3  Algebra, fully proved: the Hénon factorization
          H[V] = lowShear(∇V) ∘ upShear(id) ∘ lowShear(-id) ∘ upShear(id),
        list composition lemmas, and the triangle inequality for C^r-closeness.
  * §4  Calculus toolbox: `grad` as a CLM applied to `fderiv`, `V₀` (∇V₀ = id), smoothness
        of shears, `σ̂` and gradient modules (`V₀_facts`, `contDiff_shearOf`,
        `GradModule.contDiff`).
  * §5  Symplecticity (`GSympNet_subset_SP`): a shear's Jacobian is symplectic iff its
        off-diagonal block is symmetric; σ̂_{K,a,b} = ∇(aᵀ(∫σ)(Kx+b)), so it is a Hessian
        block and symmetric by `second_derivative_symmetric`; compositions by the chain rule.
  * §6  Lemma 3 (`shear_approx`): Hornik applied to the (r+1)-finite activation ∫σ, with the
        explicit constant ‖∇V − ∇φ‖_{C^r} ≤ ‖gradCLM‖·‖V − φ‖_{C^{r+1}}.
  * §7  The composition estimate (`comp_stable`). Instead of the paper's Faà di Bruno
        argument we induct on r using D(h∘f) = B(Dh∘f, Df) with B bilinear of norm ≤ 1
        and Leibniz' rule (`comp_two_stable`), then induct on the list of factors.
  * Main theorem `G_SympNet_universal`, proved from the above, with Hornik and Turaev as
    hypotheses; both are discharged in `G_SympNet_universal_unconditional`. No `sorry` anywhere;
    `#print axioms` shows only [propext, Classical.choice, Quot.sound].

  Conventions that differ from the paper (both are harmless):
  * The paper's C^r norm is a max over multi-indices |α| ≤ r. Here we use operator norms of
    `iteratedFDeriv`. The two are equivalent up to constants, so "dense" means the same.
  * Symplecticity is stated with the bilinear form ω(v,w) = vᵀJw, J = [[0,I],[-I,0]]:
    `ω (DF v) (DF w) = ω v w` for all v w, which is equivalent to (∂F)ᵀ J (∂F) = J.
-/
import Mathlib

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace SympNet

/-! ## §1 Definitions -/

/-- Configuration space ℝ^d (with the sup norm, as in the paper's proof). -/
abbrev E (d : ℕ) := Fin d → ℝ

/-- Phase space ℝ^{2d} = ℝ^d × ℝ^d, points written (p, q). -/
abbrev X (d : ℕ) := E d × E d

variable {d : ℕ}

/-- The canonical symplectic form ω(v, w) = vᵀ J w with J = [[0, I], [-I, 0]]. -/
def symplecticForm (v w : X d) : ℝ :=
  ∑ i, (v.1 i * w.2 i - v.2 i * w.1 i)

/-- `F` is symplectic at `x`: its Jacobian preserves ω, i.e. (∂F)ᵀ J (∂F) = J. -/
def IsSymplecticAt (F : X d → X d) (x : X d) : Prop :=
  ∀ v w : X d, symplecticForm (fderiv ℝ F x v) (fderiv ℝ F x w) = symplecticForm v w

/-- `SP^r(U)`: C^r symplectic maps on the open set `U`. -/
def SP (r : ℕ) (U : Set (X d)) : Set (X d → X d) :=
  {F | ContDiffOn ℝ r F U ∧ ∀ x ∈ U, IsSymplecticAt F x}

/-- `CrClose r K f g ε`: ‖f − g‖_{C^r(K)} < ε (all derivatives of order ≤ r, uniformly on K). -/
def CrClose {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (r : ℕ) (K : Set V) (f g : V → W) (ε : ℝ) : Prop :=
  ∀ k ≤ r, ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k g x‖ < ε

/-- Definition 8: `S₂` is r-uniformly dense on compacta in `S₁` (relative to the open set `U`). -/
def UDense {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (r : ℕ) (U : Set V) (S₂ S₁ : Set (V → W)) : Prop :=
  S₂ ⊆ S₁ ∧ ∀ f ∈ S₁, ∀ K : Set V, IsCompact K → K ⊆ U → ∀ ε > 0,
    ∃ g ∈ S₂, CrClose r K f g ε

/-- Definition 7: σ is r-finite if σ ∈ C^r(ℝ) and 0 < ∫ |σ^{(r)}| < ∞. -/
def RFinite (r : ℕ) (σ : ℝ → ℝ) : Prop :=
  ContDiff ℝ r σ ∧ Integrable (iteratedDeriv r σ) ∧ 0 < ∫ x, |iteratedDeriv r σ x|

/-- σ̂_{K,a,b}(x) = Kᵀ diag(a) σ(Kx + b). -/
def sigmaHat (σ : ℝ → ℝ) {n : ℕ} (K : Matrix (Fin n) (Fin d) ℝ) (a b : Fin n → ℝ)
    (x : E d) : E d :=
  K.transpose.mulVec (fun j => a j * σ (K.mulVec x j + b j))

/-- Upper shear (p, q) ↦ (p + g(q), q). -/
def upShear (g : E d → E d) (z : X d) : X d := (z.1 + g z.2, z.2)

/-- Lower shear (p, q) ↦ (p, q + g(p)). -/
def lowShear (g : E d → E d) (z : X d) : X d := (z.1, z.2 + g z.1)

/-- Parameters of one gradient module (an element of M_G). `up = true` means "up" module. -/
structure GradModule (d : ℕ) where
  n : ℕ
  up : Bool
  K : Matrix (Fin n) (Fin d) ℝ
  a : Fin n → ℝ
  b : Fin n → ℝ

/-- The map realised by a gradient module. -/
def GradModule.toFun (m : GradModule d) (σ : ℝ → ℝ) : X d → X d :=
  cond m.up (upShear (sigmaHat σ m.K m.a m.b)) (lowShear (sigmaHat σ m.K m.a m.b))

/-- Compose a list of maps; the head is applied first: `compList [f₁,…,fₙ] = fₙ ∘ ⋯ ∘ f₁`. -/
def compList {α : Type*} : List (α → α) → α → α
  | [] => id
  | f :: fs => compList fs ∘ f

/-- G-SympNets Ψ_G: finite compositions of gradient modules. -/
def GSympNet (σ : ℝ → ℝ) : Set (X d → X d) :=
  {Φ | ∃ l : List (GradModule d), Φ = compList (l.map fun m => m.toFun σ)}

/-- Gradient of V : ℝ^d → ℝ as a vector. -/
def grad (V : E d → ℝ) (x : E d) : E d := fun i => fderiv ℝ V x (Pi.single i 1)

/-- Definition 9: Hénon-like map H[V](p, q) = (q, −p + ∇V(q)). -/
def henon (V : E d → ℝ) (z : X d) : X d := (z.2, -z.1 + grad V z.2)

/-- One-hidden-layer network x ↦ aᵀ τ(Wx + b) (an element of Σ_m[τ]). -/
def shallowNet (τ : ℝ → ℝ) {n : ℕ} (W : Matrix (Fin n) (Fin d) ℝ) (a b : Fin n → ℝ)
    (x : E d) : ℝ :=
  ∑ j, a j * τ (W.mulVec x j + b j)

/-! ## §2 External results cited by the paper (taken as hypotheses) -/

/-- **Lemma 2** (Hornik, Stinchcombe & White 1990): for r-finite τ, Σ_m[τ] is r-uniformly
dense on compacta in C^r(ℝ^m). -/
def HornikDensity : Prop :=
  ∀ (m r : ℕ) (τ : ℝ → ℝ), RFinite r τ → ∀ V : E m → ℝ, ContDiff ℝ r V →
    ∀ K : Set (E m), IsCompact K → ∀ ε > 0,
      ∃ (n : ℕ) (W : Matrix (Fin n) (Fin m) ℝ) (a b : Fin n → ℝ),
        CrClose r K V (shallowNet τ W a b) ε

/-- **Lemma 4 as stated in the paper** (attributed to Turaev 2002): every F ∈ SP^r(U), for an
*arbitrary* open U, is C^r-approximated on compacta by finite compositions of Hénon-like maps.
This is strictly stronger than what Turaev proved, and it is **false**: see
`SympNet.not_TuraevHenonPaper` in `Sympnet/Counterexample.lean`. -/
def TuraevHenonPaper : Prop :=
  ∀ (m r : ℕ), 1 ≤ r → ∀ U : Set (X m), IsOpen U → ∀ F ∈ SP r U,
    ∀ K : Set (X m), IsCompact K → K ⊆ U → ∀ ε > 0,
      ∃ Vs : List (E m → ℝ), (∀ V ∈ Vs, ContDiff ℝ (r + 1 : ℕ) V) ∧
        CrClose r K F (compList (Vs.map henon)) ε

/-- **Lemma 4, restricted to convex U and injective F** (Turaev 2003). Every injective
F ∈ SP^r(U), with U open and convex, is C^r-approximated on compacta by finite compositions of
Hénon-like maps H[V] with V ∈ C^{r+1}(ℝ^d).

How this relates to Turaev's statement: he approximates symplectic diffeomorphisms of ℝ^{2n}, in
C^∞ on compacta, by iterates of (x,y) ↦ (y+η, −x+∇V(y)), V polynomial. Such a map is a composition
of Hénon maps, since (p,q) ↦ (p+η, q) = H[0]³ ∘ H[⟨−η,·⟩] (`translation_eq_henon` in
`Sympnet/Counterexample.lean`). Going from his class to ours needs two standard steps, which are
*not* formalized here:
  * extension: an injective symplectic F on a convex U is symplectically isotopic to an affine
    map (Alexander trick F_t(x) = (F(x₀ + t(x−x₀)) − F(x₀))/t + F(x₀)), and cutting off the
    Hamiltonian of this isotopy gives a global symplectic diffeomorphism equal to F near K;
  * smoothing: C^r symplectic maps are C^r-approximated by C^∞ ones.
Both hypotheses are needed: without them the statement is false (`not_TuraevHenonPaper`). -/
def TuraevHenon : Prop :=
  ∀ (m r : ℕ), 1 ≤ r → ∀ U : Set (X m), IsOpen U → Convex ℝ U →
    ∀ F ∈ SP r U, Set.InjOn F U →
    ∀ K : Set (X m), IsCompact K → K ⊆ U → ∀ ε > 0,
      ∃ Vs : List (E m → ℝ), (∀ V ∈ Vs, ContDiff ℝ (r + 1 : ℕ) V) ∧
        CrClose r K F (compList (Vs.map henon)) ε

/-! ## §3 Algebraic part (proved) -/

/-- Triangle inequality for C^r-closeness. -/
theorem CrClose.trans {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {r : ℕ} {K : Set V} {f₁ f₂ f₃ : V → W}
    {a b : ℝ} (h₁ : CrClose r K f₁ f₂ a) (h₂ : CrClose r K f₂ f₃ b) :
    CrClose r K f₁ f₃ (a + b) := by
  intro k hk x hx
  calc ‖iteratedFDeriv ℝ k f₁ x - iteratedFDeriv ℝ k f₃ x‖
      = ‖(iteratedFDeriv ℝ k f₁ x - iteratedFDeriv ℝ k f₂ x) +
          (iteratedFDeriv ℝ k f₂ x - iteratedFDeriv ℝ k f₃ x)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖iteratedFDeriv ℝ k f₁ x - iteratedFDeriv ℝ k f₂ x‖ +
          ‖iteratedFDeriv ℝ k f₂ x - iteratedFDeriv ℝ k f₃ x‖ := norm_add_le _ _
    _ < a + b := add_lt_add (h₁ k hk x hx) (h₂ k hk x hx)

theorem compList_append {α : Type*} (l₁ l₂ : List (α → α)) :
    compList (l₁ ++ l₂) = compList l₂ ∘ compList l₁ := by
  induction l₁ with
  | nil => rfl
  | cons f l ih => simp only [List.cons_append, compList, ih, Function.comp_assoc]

/-- The matrix identity from the proof of Theorem 5:
[[0, I], [−I, ∇V]] = [[I, 0], [∇V, I]] · [[I, I], [0, I]] · [[I, 0], [−I, I]] · [[I, I], [0, I]]. -/
theorem henon_eq (V : E d → ℝ) :
    henon V = lowShear (grad V) ∘ upShear id ∘ lowShear (fun x => -x) ∘ upShear id := by
  funext z
  rcases z with ⟨p, q⟩
  have h₁ : p + q + (q + -(p + q)) = q := by abel
  have h₁' : p + q + -p = q := by abel
  have h₂ : q + -(p + q) = -p := by abel
  simp only [Function.comp_apply, henon, upShear, lowShear, id_eq, h₁, h₁', h₂]

/-- V₀(x) = |x|²/2, so ∇V₀ = id and ∇(−V₀) = −id (the linear shears are gradient shears). -/
def V₀ : E d → ℝ := fun x => ∑ i, x i ^ 2 / 2

def negV₀ : E d → ℝ := fun x => -V₀ x

/-- A shear factor: `(true, V)` ↦ upper shear by ∇V, `(false, V)` ↦ lower shear by ∇V. -/
def shearOf (p : Bool × (E d → ℝ)) : X d → X d :=
  cond p.1 (upShear (grad p.2)) (lowShear (grad p.2))

/-- The four factors of H[V], listed in the order they are applied. -/
def henonFactors (V : E d → ℝ) : List (Bool × (E d → ℝ)) :=
  [(true, V₀), (false, negV₀), (true, V₀), (false, V)]

/-! ## §4 A calculus toolbox for `grad` and for the shears -/

/-- The canonical isomorphism `(ℝ^d)^* ≃ ℝ^d` that turns `DV x` into `∇V x`. -/
def gradCLM (d : ℕ) : (E d →L[ℝ] ℝ) →L[ℝ] E d :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : E d)

@[simp] theorem gradCLM_apply (L : E d →L[ℝ] ℝ) (i : Fin d) :
    gradCLM d L i = L (Pi.single i 1) := rfl

theorem grad_eq_gradCLM (V : E d → ℝ) : grad V = fun x => gradCLM d (fderiv ℝ V x) := rfl

/-- Every vector is the sum of its coordinates times the standard basis vectors. -/
theorem eq_sum_single (w : E d) : w = ∑ i, w i • (Pi.single i 1 : E d) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']

/-- The pairing identity `⟪∇V x, w⟫ = DV x w`. -/
theorem sum_grad_mul (V : E d → ℝ) (x w : E d) :
    ∑ i, grad V x i * w i = fderiv ℝ V x w := by
  conv_rhs => rw [eq_sum_single w]
  rw [map_sum]
  simp only [map_smul, grad, smul_eq_mul, mul_comm]

/-- `V ∈ C^{r+1}` implies `∇V ∈ C^r`. -/
theorem contDiff_grad {r : ℕ} {V : E d → ℝ} (hV : ContDiff ℝ (r + 1 : ℕ) V) :
    ContDiff ℝ r (grad V) := by
  rw [grad_eq_gradCLM]
  exact (gradCLM d).contDiff.comp (hV.fderiv_right (by exact_mod_cast le_rfl))

/-! ### `V₀` and its gradient -/

theorem hasFDerivAt_V₀ (x : E d) :
    HasFDerivAt (V₀ (d := d))
      (∑ i, (x i) • (ContinuousLinearMap.proj i : E d →L[ℝ] ℝ)) x := by
  have h : ∀ i : Fin d, HasFDerivAt (fun y : E d => y i ^ 2 / 2)
      ((x i) • (ContinuousLinearMap.proj i : E d →L[ℝ] ℝ)) x := by
    intro i
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) (x i) (x i) := by
      simpa using (hasDerivAt_pow 2 (x i)).div_const 2
    exact h1.comp_hasFDerivAt x
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj i : E d →L[ℝ] ℝ))
  have heq : (∑ i : Fin d, fun y : E d => y i ^ 2 / 2) = (V₀ (d := d)) := by
    funext y; simp [V₀, Finset.sum_apply]
  rw [← heq]
  exact HasFDerivAt.sum fun i _ => h i

theorem contDiff_V₀ (n : ℕ∞ω) : ContDiff ℝ n (V₀ (d := d)) := by
  unfold V₀
  exact ContDiff.sum fun i _ =>
    (((contDiff_apply ℝ (fun _ : Fin d => ℝ) i).pow 2).div_const 2)

theorem grad_V₀ : grad (V₀ (d := d)) = id := by
  funext x i
  rw [grad, (hasFDerivAt_V₀ x).fderiv]
  simp [Pi.single_apply, Finset.sum_ite_eq']

theorem contDiff_negV₀ (n : ℕ∞ω) : ContDiff ℝ n (negV₀ (d := d)) :=
  (contDiff_V₀ n).neg

theorem hasFDerivAt_negV₀ (x : E d) :
    HasFDerivAt (negV₀ (d := d))
      (-∑ i, (x i) • (ContinuousLinearMap.proj i : E d →L[ℝ] ℝ)) x :=
  (hasFDerivAt_V₀ x).neg

theorem grad_negV₀ : grad (negV₀ (d := d)) = fun x => -x := by
  funext x i
  rw [grad, (hasFDerivAt_negV₀ x).fderiv]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Routine calculus: V₀ and −V₀ are smooth, ∇V₀ = id, ∇(−V₀) = −id. -/
theorem V₀_facts (n : ℕ) :
    ContDiff ℝ n (V₀ (d := d)) ∧ ContDiff ℝ n (negV₀ (d := d)) ∧
      grad (V₀ (d := d)) = id ∧ grad (negV₀ (d := d)) = fun x => -x :=
  ⟨contDiff_V₀ n, contDiff_negV₀ n, grad_V₀, grad_negV₀⟩

/-! ### Smoothness of shears -/

/-- An upper shear is as smooth as its shear function. -/
theorem contDiff_upShear {n : ℕ∞ω} {g : E d → E d} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (upShear g) := by
  exact (contDiff_fst.add (hg.comp contDiff_snd)).prodMk contDiff_snd

/-- A lower shear is as smooth as its shear function. -/
theorem contDiff_lowShear {n : ℕ∞ω} {g : E d → E d} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (lowShear g) := by
  exact contDiff_fst.prodMk (contDiff_snd.add (hg.comp contDiff_fst))

/-- Routine: V ∈ C^{r+1} ⇒ ∇V ∈ C^r ⇒ the shear is C^r. -/
theorem contDiff_shearOf (r : ℕ) (p : Bool × (E d → ℝ)) (hp : ContDiff ℝ (r + 1 : ℕ) p.2) :
    ContDiff ℝ r (shearOf p) := by
  rcases p with ⟨b, V⟩
  cases b
  · exact contDiff_lowShear (contDiff_grad hp)
  · exact contDiff_upShear (contDiff_grad hp)

/-! ### Smoothness of `σ̂` and of gradient modules -/

theorem contDiff_sigmaHat {n : ℕ∞ω} {σ : ℝ → ℝ} (hσ : ContDiff ℝ n σ) {k : ℕ}
    (K : Matrix (Fin k) (Fin d) ℝ) (a b : Fin k → ℝ) :
    ContDiff ℝ n (sigmaHat σ K a b) := by
  have hlin : ContDiff ℝ n (fun v : Fin k → ℝ => K.transpose.mulVec v) :=
    (Matrix.mulVecLin K.transpose).toContinuousLinearMap.contDiff
  refine hlin.comp (contDiff_pi.2 fun j => ?_)
  have hKx : ContDiff ℝ n (fun x : E d => K.mulVec x j + b j) := by
    have : ContDiff ℝ n (fun x : E d => K.mulVec x) :=
      (Matrix.mulVecLin K).toContinuousLinearMap.contDiff
    exact ((contDiff_apply ℝ (fun _ : Fin k => ℝ) j).comp this).add contDiff_const
  exact (hσ.comp hKx).const_smul (a j)

/-- Routine: σ ∈ C^r ⇒ every gradient module is C^r. -/
theorem GradModule.contDiff (m : GradModule d) (r : ℕ) (σ : ℝ → ℝ) (hσ : RFinite r σ) :
    ContDiff ℝ r (m.toFun σ) := by
  have h := contDiff_sigmaHat (n := (r : ℕ∞ω)) hσ.1 m.K m.a m.b
  rcases m with ⟨k, up, K, a, b⟩
  cases up
  · exact contDiff_lowShear h
  · exact contDiff_upShear h

/-! ## §5 Symplecticity of gradient modules

The Jacobian of an upper shear `(p,q) ↦ (p + g q, q)` is `[[I, Dg], [0, I]]`, and such a
matrix is symplectic exactly when `Dg` is symmetric.  For `g = ∇V` this is the symmetry of
the Hessian; a gradient module is a shear by `∇V` for `V` a one-hidden-layer network with
activation `∫σ`, which is how `GSympNet_subset_SP` is obtained. -/

/-- A self-map of `ℝ^d` whose matrix is symmetric for the Euclidean pairing. -/
def IsSymmetricCLM (G : E d →L[ℝ] E d) : Prop :=
  ∀ v w : E d, ∑ i, G v i * w i = ∑ i, G w i * v i

/-- `v ↦ (v₁ + G v₂, v₂)`: the Jacobian of an upper shear. -/
def upShearCLM (G : E d →L[ℝ] E d) : X d →L[ℝ] X d :=
  (ContinuousLinearMap.fst ℝ (E d) (E d) +
      G.comp (ContinuousLinearMap.snd ℝ (E d) (E d))).prod
    (ContinuousLinearMap.snd ℝ (E d) (E d))

@[simp] theorem upShearCLM_apply (G : E d →L[ℝ] E d) (v : X d) :
    upShearCLM G v = (v.1 + G v.2, v.2) := rfl

/-- `v ↦ (v₁, v₂ + G v₁)`: the Jacobian of a lower shear. -/
def lowShearCLM (G : E d →L[ℝ] E d) : X d →L[ℝ] X d :=
  (ContinuousLinearMap.fst ℝ (E d) (E d)).prod
    (ContinuousLinearMap.snd ℝ (E d) (E d) +
      G.comp (ContinuousLinearMap.fst ℝ (E d) (E d)))

@[simp] theorem lowShearCLM_apply (G : E d →L[ℝ] E d) (v : X d) :
    lowShearCLM G v = (v.1, v.2 + G v.1) := rfl

theorem hasFDerivAt_upShear {g : E d → E d} {G : E d →L[ℝ] E d} {z : X d}
    (hg : HasFDerivAt g G z.2) : HasFDerivAt (upShear g) (upShearCLM G) z :=
  (hasFDerivAt_fst.add (hg.comp z hasFDerivAt_snd)).prodMk hasFDerivAt_snd

theorem hasFDerivAt_lowShear {g : E d → E d} {G : E d →L[ℝ] E d} {z : X d}
    (hg : HasFDerivAt g G z.1) : HasFDerivAt (lowShear g) (lowShearCLM G) z :=
  hasFDerivAt_fst.prodMk (hasFDerivAt_snd.add (hg.comp z hasFDerivAt_fst))

theorem isSymplecticAt_upShear {g : E d → E d} {G : E d →L[ℝ] E d} {z : X d}
    (hg : HasFDerivAt g G z.2) (hsym : IsSymmetricCLM G) : IsSymplecticAt (upShear g) z := by
  intro v w
  rw [(hasFDerivAt_upShear hg).fderiv]
  have key : ∑ i, ((v.1 + G v.2) i * w.2 i - v.2 i * (w.1 + G w.2) i) =
      (∑ i, (v.1 i * w.2 i - v.2 i * w.1 i)) +
        ((∑ i, G v.2 i * w.2 i) - (∑ i, G w.2 i * v.2 i)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  simpa only [symplecticForm, upShearCLM_apply, key, hsym v.2 w.2, sub_self, add_zero]

theorem isSymplecticAt_lowShear {g : E d → E d} {G : E d →L[ℝ] E d} {z : X d}
    (hg : HasFDerivAt g G z.1) (hsym : IsSymmetricCLM G) : IsSymplecticAt (lowShear g) z := by
  intro v w
  rw [(hasFDerivAt_lowShear hg).fderiv]
  have key : ∑ i, (v.1 i * (w.2 + G w.1) i - (v.2 + G v.1) i * w.1 i) =
      (∑ i, (v.1 i * w.2 i - v.2 i * w.1 i)) +
        ((∑ i, G w.1 i * v.1 i) - (∑ i, G v.1 i * w.1 i)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  simpa only [symplecticForm, lowShearCLM_apply, key, hsym w.1 v.1, sub_self, add_zero]

/-! ### The Hessian is a symmetric operator -/

theorem sum_gradCLM_mul (L : E d →L[ℝ] ℝ) (t : E d) : ∑ i, gradCLM d L i * t i = L t := by
  conv_rhs => rw [eq_sum_single t]
  rw [map_sum]
  simp only [map_smul, gradCLM_apply, smul_eq_mul, mul_comm]

theorem hasFDerivAt_grad {V : E d → ℝ} (hV : ContDiff ℝ 2 V) (q : E d) :
    HasFDerivAt (grad V) ((gradCLM d).comp (fderiv ℝ (fderiv ℝ V) q)) q := by
  have h2 : HasFDerivAt (fun y => fderiv ℝ V y) (fderiv ℝ (fderiv ℝ V) q) q :=
    (((hV.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero) q).hasFDerivAt
  exact (gradCLM d).hasFDerivAt.comp q h2

theorem isSymmetricCLM_hessian {V : E d → ℝ} (hV : ContDiff ℝ 2 V) (q : E d) :
    IsSymmetricCLM ((gradCLM d).comp (fderiv ℝ (fderiv ℝ V) q)) := by
  have hpair : ∀ u t : E d,
      ∑ i, ((gradCLM d).comp (fderiv ℝ (fderiv ℝ V) q)) u i * t i =
        (fderiv ℝ (fderiv ℝ V) q) u t := fun u t => sum_gradCLM_mul _ t
  intro v w
  rw [hpair, hpair]
  have hd : ∀ y, HasFDerivAt V (fderiv ℝ V y) y := fun y =>
    (hV.differentiable (by norm_num) y).hasFDerivAt
  have hx : HasFDerivAt (fun y => fderiv ℝ V y) (fderiv ℝ (fderiv ℝ V) q) q :=
    (((hV.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero) q).hasFDerivAt
  exact second_derivative_symmetric hd hx v w

/-- A shear by a gradient of a `C²` potential is symplectic everywhere. -/
theorem isSymplecticAt_shearOf {V : E d → ℝ} (hV : ContDiff ℝ 2 V) (up : Bool) (z : X d) :
    IsSymplecticAt (shearOf (up, V)) z := by
  cases up
  · exact isSymplecticAt_lowShear (hasFDerivAt_grad hV z.1) (isSymmetricCLM_hessian hV z.1)
  · exact isSymplecticAt_upShear (hasFDerivAt_grad hV z.2) (isSymmetricCLM_hessian hV z.2)

/-! ### Symplecticity is stable under composition -/

theorem IsSymplecticAt.comp {F G : X d → X d} {x : X d} (hG : IsSymplecticAt G (F x))
    (hF : IsSymplecticAt F x) (hFd : DifferentiableAt ℝ F x)
    (hGd : DifferentiableAt ℝ G (F x)) : IsSymplecticAt (G ∘ F) x := by
  intro v w
  rw [fderiv_comp x hGd hFd]
  simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply] using
    (hG (fderiv ℝ F x v) (fderiv ℝ F x w)).trans (hF v w)

theorem contDiff_compList {n : ℕ∞ω} (l : List (X d → X d)) (h : ∀ f ∈ l, ContDiff ℝ n f) :
    ContDiff ℝ n (compList l) := by
  induction l with
  | nil => exact contDiff_id
  | cons f fs ih =>
    exact (ih fun g hg => h g (List.mem_cons_of_mem _ hg)).comp (h f List.mem_cons_self)

theorem differentiable_compList (l : List (X d → X d)) (hd : ∀ f ∈ l, Differentiable ℝ f) :
    Differentiable ℝ (compList l) := by
  induction l with
  | nil => exact differentiable_id
  | cons f fs ih =>
    exact (ih fun g hg => hd g (List.mem_cons_of_mem _ hg)).comp (hd f List.mem_cons_self)

theorem isSymplecticAt_compList (l : List (X d → X d))
    (hd : ∀ f ∈ l, Differentiable ℝ f) (hs : ∀ f ∈ l, ∀ x, IsSymplecticAt f x) (x : X d) :
    IsSymplecticAt (compList l) x := by
  induction l generalizing x with
  | nil => intro v w; simp [compList, symplecticForm]
  | cons f fs ih =>
    have hdf : Differentiable ℝ f := hd f List.mem_cons_self
    have hdfs : Differentiable ℝ (compList fs) :=
      differentiable_compList fs fun g hg => hd g (List.mem_cons_of_mem _ hg)
    exact IsSymplecticAt.comp
      (ih (fun g hg => hd g (List.mem_cons_of_mem _ hg))
        (fun g hg => hs g (List.mem_cons_of_mem _ hg)) (f x))
      (hs f List.mem_cons_self x) (hdf x) (hdfs (f x))

/-! ### The antiderivative of the activation -/

/-- `Σσ(x) = ∫₀ˣ σ`, the antiderivative used to realise `σ̂` as a gradient. -/
def primitive (σ : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, σ t

theorem hasDerivAt_primitive {σ : ℝ → ℝ} (hσ : Continuous σ) (x : ℝ) :
    HasDerivAt (primitive σ) (σ x) x :=
  intervalIntegral.integral_hasDerivAt_right (hσ.intervalIntegrable _ _)
    hσ.aestronglyMeasurable.stronglyMeasurableAtFilter hσ.continuousAt

theorem deriv_primitive {σ : ℝ → ℝ} (hσ : Continuous σ) : deriv (primitive σ) = σ :=
  funext fun x => (hasDerivAt_primitive hσ x).deriv

theorem contDiff_primitive {n : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ n σ) :
    ContDiff ℝ (n + 1 : ℕ) (primitive σ) := by
  rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by push_cast; ring, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_primitive hσ.continuous x).differentiableAt, fun h => ?_, ?_⟩
  · exact absurd h (by simp)
  · rw [deriv_primitive hσ.continuous]; exact hσ

theorem iteratedDeriv_primitive (n : ℕ) {σ : ℝ → ℝ} (hσ : Continuous σ) :
    iteratedDeriv (n + 1) (primitive σ) = iteratedDeriv n σ := by
  rw [iteratedDeriv_succ', deriv_primitive hσ]

/-- If σ is r-finite then its antiderivative is (r+1)-finite; this is the activation that
Lemma 3 feeds into Hornik's theorem. -/
theorem RFinite.primitive {r : ℕ} {σ : ℝ → ℝ} (hσ : RFinite r σ) :
    RFinite (r + 1) (SympNet.primitive σ) := by
  refine ⟨contDiff_primitive hσ.1, ?_, ?_⟩
  · rw [iteratedDeriv_primitive r hσ.1.continuous]; exact hσ.2.1
  · rw [iteratedDeriv_primitive r hσ.1.continuous]; exact hσ.2.2

/-! ### `σ̂` is the gradient of a one-hidden-layer network -/

/-- The CLM `v ↦ (Wv)ⱼ`. -/
def rowCLM {n : ℕ} (W : Matrix (Fin n) (Fin d) ℝ) (j : Fin n) : E d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (Matrix.mulVecLin W).toContinuousLinearMap

@[simp] theorem rowCLM_apply {n : ℕ} (W : Matrix (Fin n) (Fin d) ℝ) (j : Fin n) (v : E d) :
    rowCLM W j v = W.mulVec v j := rfl

theorem contDiff_shallowNet {m : ℕ∞ω} {τ : ℝ → ℝ} (hτ : ContDiff ℝ m τ) {n : ℕ}
    (W : Matrix (Fin n) (Fin d) ℝ) (a b : Fin n → ℝ) :
    ContDiff ℝ m (shallowNet τ W a b) := by
  unfold shallowNet
  exact ContDiff.sum fun j _ =>
    contDiff_const.mul (hτ.comp ((rowCLM W j).contDiff.add contDiff_const))

theorem hasFDerivAt_shallowNet {τ σ : ℝ → ℝ} (hτ : ∀ y, HasDerivAt τ (σ y) y)
    {n : ℕ} (W : Matrix (Fin n) (Fin d) ℝ) (a b : Fin n → ℝ) (x : E d) :
    HasFDerivAt (shallowNet τ W a b)
      (∑ j, (a j * σ (W.mulVec x j + b j)) • rowCLM W j) x := by
  have h : ∀ j : Fin n, HasFDerivAt (fun y : E d => a j * τ (W.mulVec y j + b j))
      ((a j * σ (W.mulVec x j + b j)) • rowCLM W j) x := by
    intro j
    have h1 : HasFDerivAt (fun y : E d => W.mulVec y j + b j) (rowCLM W j) x :=
      (rowCLM W j).hasFDerivAt.add_const (b j)
    have h3 := ((hτ (W.mulVec x j + b j)).comp_hasFDerivAt x h1).const_mul (a j)
    rwa [smul_smul] at h3
  have heq : (∑ j : Fin n, fun y : E d => a j * τ (W.mulVec y j + b j)) =
      shallowNet τ W a b := by
    funext y; simp [shallowNet, Finset.sum_apply]
  rw [← heq]
  exact HasFDerivAt.sum fun j _ => h j

/-- The key identity of Lemma 3: `∇(aᵀ(∫σ)(Wx+b)) = Wᵀ diag(a) σ(Wx+b) = σ̂_{W,a,b}`. -/
theorem grad_shallowNet_primitive {σ : ℝ → ℝ} (hσ : Continuous σ) {n : ℕ}
    (W : Matrix (Fin n) (Fin d) ℝ) (a b : Fin n → ℝ) :
    grad (shallowNet (primitive σ) W a b) = sigmaHat σ W a b := by
  funext x i
  rw [grad, (hasFDerivAt_shallowNet (hasDerivAt_primitive hσ) W a b x).fderiv]
  have hcol : ∀ j : Fin n, W.mulVec (Pi.single i 1 : E d) j = W j i := fun j => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, rowCLM_apply, smul_eq_mul, hcol]
  simp only [sigmaHat, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A gradient module is the shear by the gradient of the `C^{r+1}` potential
`aᵀ(∫σ)(Kx+b)`. -/
theorem GradModule.toFun_eq_shearOf (m : GradModule d) {σ : ℝ → ℝ} (hσ : Continuous σ) :
    m.toFun σ = shearOf (m.up, shallowNet (primitive σ) m.K m.a m.b) := by
  rcases m with ⟨k, up, K, a, b⟩
  simp only [GradModule.toFun, shearOf, grad_shallowNet_primitive hσ]

theorem GradModule.isSymplecticAt (m : GradModule d) {r : ℕ} (hr : 1 ≤ r) {σ : ℝ → ℝ}
    (hσ : RFinite r σ) (z : X d) : IsSymplecticAt (m.toFun σ) z := by
  have hpot : ContDiff ℝ 2 (shallowNet (primitive σ) m.K m.a m.b) := by
    refine contDiff_shallowNet (ContDiff.of_le (contDiff_primitive hσ.1) ?_) _ _ _
    exact_mod_cast Nat.succ_le_succ hr
  rw [m.toFun_eq_shearOf hσ.1.continuous]
  exact isSymplecticAt_shearOf hpot m.up z

/-- Theorem 1 / Theorem 2 of the paper restricted to Ψ_G: every G-SympNet is a C^r symplectic
map. -/
theorem GSympNet_subset_SP (r : ℕ) (hr : 1 ≤ r) (σ : ℝ → ℝ) (hσ : RFinite r σ)
    (U : Set (X d)) : GSympNet σ ⊆ SP r U := by
  rintro Φ ⟨l, rfl⟩
  have hmem : ∀ f ∈ l.map (fun m : GradModule d => m.toFun σ),
      ContDiff ℝ (r : ℕ∞ω) f ∧ ∀ z, IsSymplecticAt f z := by
    intro f hf
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hf
    exact ⟨m.contDiff r σ hσ, m.isSymplecticAt hr hσ⟩
  refine ⟨((contDiff_compList _ fun f hf => (hmem f hf).1).contDiffOn), fun x _ => ?_⟩
  refine isSymplecticAt_compList _ (fun f hf => ?_) (fun f hf => (hmem f hf).2) x
  exact ((hmem f hf).1.of_le (Nat.one_le_cast.mpr hr)).differentiable one_ne_zero

/-! ## §6 Lemma 3: a gradient shear is one gradient module away -/

/-- Transfer of `C^r`-closeness along a factorisation `f₁ - f₂ = L ∘ (u₁ - u₂) ∘ P` with
`‖L‖ ≤ 1` and `‖P‖ ≤ 1`.  This is what reduces closeness of shears to closeness of the
shear functions. -/
theorem crClose_sandwich {r : ℕ} {ε : ℝ} {K : Set (X d)}
    {u₁ u₂ : E d → E d} (hu₁ : ContDiff ℝ r u₁) (hu₂ : ContDiff ℝ r u₂)
    {f₁ f₂ : X d → X d} (hf₁ : ContDiff ℝ r f₁) (hf₂ : ContDiff ℝ r f₂)
    (L : E d →L[ℝ] X d) (hL : ‖L‖ ≤ 1) (P : X d →L[ℝ] E d) (hP : ‖P‖ ≤ 1)
    (hdiff : f₁ - f₂ = (L : E d → X d) ∘ ((u₁ - u₂) ∘ (P : X d → E d)))
    (hu : CrClose r ((P : X d → E d) '' K) u₁ u₂ ε) :
    CrClose r K f₁ f₂ ε := by
  intro k hk z hz
  have hkr : ((k : ℕ) : ℕ∞ω) ≤ ((r : ℕ) : ℕ∞ω) := Nat.cast_le.mpr hk
  have hdu : ContDiff ℝ ((r : ℕ) : ℕ∞ω) (u₁ - u₂) := hu₁.sub hu₂
  have hlt : ‖iteratedFDeriv ℝ k (u₁ - u₂) (P z)‖ < ε := by
    rw [iteratedFDeriv_sub_apply (hu₁.of_le hkr).contDiffAt (hu₂.of_le hkr).contDiffAt]
    exact hu k hk (P z) ⟨z, hz, rfl⟩
  have e1 : iteratedFDeriv ℝ k f₁ z - iteratedFDeriv ℝ k f₂ z
      = iteratedFDeriv ℝ k (f₁ - f₂) z :=
    (iteratedFDeriv_sub_apply (hf₁.of_le hkr).contDiffAt (hf₂.of_le hkr).contDiffAt).symm
  rw [e1, hdiff]
  calc ‖iteratedFDeriv ℝ k ((L : E d → X d) ∘ ((u₁ - u₂) ∘ (P : X d → E d))) z‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ k ((u₁ - u₂) ∘ (P : X d → E d)) z‖ :=
        L.norm_iteratedFDeriv_comp_left (hdu.comp P.contDiff).contDiffAt hkr
    _ ≤ ‖iteratedFDeriv ℝ k ((u₁ - u₂) ∘ (P : X d → E d)) z‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hL
    _ = ‖(iteratedFDeriv ℝ k (u₁ - u₂) (P z)).compContinuousLinearMap fun _ => P‖ := by
        rw [P.iteratedFDeriv_comp_right hdu z hkr]
    _ ≤ ‖iteratedFDeriv ℝ k (u₁ - u₂) (P z)‖ * ∏ _i : Fin k, ‖P‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k (u₁ - u₂) (P z)‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hP
    _ < ε := by rwa [mul_one]

theorem crClose_upShear {r : ℕ} {ε : ℝ} {K : Set (X d)} {g₁ g₂ : E d → E d}
    (h₁ : ContDiff ℝ r g₁) (h₂ : ContDiff ℝ r g₂)
    (hg : CrClose r (Prod.snd '' K) g₁ g₂ ε) : CrClose r K (upShear g₁) (upShear g₂) ε := by
  refine crClose_sandwich h₁ h₂ (contDiff_upShear h₁) (contDiff_upShear h₂)
    (ContinuousLinearMap.inl ℝ (E d) (E d)) (ContinuousLinearMap.norm_inl_le_one ℝ (E d) (E d))
    (ContinuousLinearMap.snd ℝ (E d) (E d)) (ContinuousLinearMap.norm_snd_le ℝ (E d) (E d))
    ?_ hg
  funext z
  refine Prod.ext ?_ ?_ <;> simp [upShear] <;> abel

theorem crClose_lowShear {r : ℕ} {ε : ℝ} {K : Set (X d)} {g₁ g₂ : E d → E d}
    (h₁ : ContDiff ℝ r g₁) (h₂ : ContDiff ℝ r g₂)
    (hg : CrClose r (Prod.fst '' K) g₁ g₂ ε) : CrClose r K (lowShear g₁) (lowShear g₂) ε := by
  refine crClose_sandwich h₁ h₂ (contDiff_lowShear h₁) (contDiff_lowShear h₂)
    (ContinuousLinearMap.inr ℝ (E d) (E d)) (ContinuousLinearMap.norm_inr_le_one ℝ (E d) (E d))
    (ContinuousLinearMap.fst ℝ (E d) (E d)) (ContinuousLinearMap.norm_fst_le ℝ (E d) (E d))
    ?_ hg
  funext z
  refine Prod.ext ?_ ?_ <;> simp [lowShear] <;> abel

/-- `‖∇V − ∇φ‖_{C^r} ≤ C‖V − φ‖_{C^{r+1}}` with the explicit constant `C = ‖gradCLM d‖`. -/
theorem crClose_grad {r : ℕ} {ε C : ℝ} {Kc : Set (E d)} {V φ : E d → ℝ}
    (hV : ContDiff ℝ (r + 1 : ℕ) V) (hφ : ContDiff ℝ (r + 1 : ℕ) φ)
    (h : CrClose (r + 1) Kc V φ ε) (hCε : ‖gradCLM d‖ * ε < C) :
    CrClose r Kc (grad V) (grad φ) C := by
  intro k hk x hx
  have hkr : ((k : ℕ) : ℕ∞ω) ≤ ((r : ℕ) : ℕ∞ω) := Nat.cast_le.mpr hk
  have hVd : Differentiable ℝ V := hV.differentiable (by positivity)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by positivity)
  have hdV : ContDiff ℝ ((r : ℕ) : ℕ∞ω) (fun y => fderiv ℝ V y) := by
    refine hV.fderiv_right ?_
    rw [show ((r + 1 : ℕ) : ℕ∞ω) = ((r : ℕ) : ℕ∞ω) + 1 by push_cast; ring]
  have hdφ : ContDiff ℝ ((r : ℕ) : ℕ∞ω) (fun y => fderiv ℝ φ y) := by
    refine hφ.fderiv_right ?_
    rw [show ((r + 1 : ℕ) : ℕ∞ω) = ((r : ℕ) : ℕ∞ω) + 1 by push_cast; ring]
  have hfun : grad V - grad φ =
      (gradCLM d : (E d →L[ℝ] ℝ) → E d) ∘ (fun y => fderiv ℝ V y - fderiv ℝ φ y) := by
    funext y
    simp only [Pi.sub_apply, grad_eq_gradCLM, Function.comp_apply, map_sub]
  have e1 : iteratedFDeriv ℝ k (grad V) x - iteratedFDeriv ℝ k (grad φ) x
      = iteratedFDeriv ℝ k (grad V - grad φ) x :=
    (iteratedFDeriv_sub_apply ((contDiff_grad hV).of_le hkr).contDiffAt
      ((contDiff_grad hφ).of_le hkr).contDiffAt).symm
  rw [e1, hfun]
  calc ‖iteratedFDeriv ℝ k ((gradCLM d : (E d →L[ℝ] ℝ) → E d) ∘
          (fun y => fderiv ℝ V y - fderiv ℝ φ y)) x‖
      ≤ ‖gradCLM d‖ * ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ V y - fderiv ℝ φ y) x‖ :=
        (gradCLM d).norm_iteratedFDeriv_comp_left (hdV.sub hdφ).contDiffAt hkr
    _ ≤ ‖gradCLM d‖ * ε := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hsub : (fun y => fderiv ℝ V y - fderiv ℝ φ y) = fderiv ℝ (V - φ) := by
          funext y
          rw [fderiv_sub (hVd y) (hφd y)]
        rw [hsub, norm_iteratedFDeriv_fderiv]
        have hk1 : k + 1 ≤ r + 1 := Nat.succ_le_succ hk
        have := h (k + 1) hk1 x hx
        rw [← iteratedFDeriv_sub_apply (hV.of_le (Nat.cast_le.mpr hk1)).contDiffAt
          (hφ.of_le (Nat.cast_le.mpr hk1)).contDiffAt] at this
        exact this.le
    _ < C := hCε

/-- The analytic core of Lemma 3: Hornik's theorem applied to the antiderivative activation
produces a one-hidden-layer `φ` whose gradient `σ̂` is `C^r`-close to `∇V`. -/
theorem grad_approx_core (hH : HornikDensity) (r : ℕ) (σ : ℝ → ℝ) (hσ : RFinite r σ)
    (V : E d → ℝ) (hV : ContDiff ℝ (r + 1 : ℕ) V) (Kc : Set (E d)) (hKc : IsCompact Kc)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (W : Matrix (Fin n) (Fin d) ℝ) (a b : Fin n → ℝ),
      CrClose r Kc (grad V) (sigmaHat σ W a b) ε := by
  have hC0 : (0:ℝ) ≤ ‖gradCLM d‖ := norm_nonneg _
  have hden : (0:ℝ) < ‖gradCLM d‖ + 1 := by positivity
  have hε' : 0 < ε / (‖gradCLM d‖ + 1) := div_pos hε hden
  obtain ⟨n, W, a, b, hclose⟩ :=
    hH d (r + 1) (primitive σ) hσ.primitive V hV Kc hKc _ hε'
  refine ⟨n, W, a, b, ?_⟩
  rw [← grad_shallowNet_primitive hσ.1.continuous W a b]
  refine crClose_grad hV (contDiff_shallowNet (contDiff_primitive hσ.1) W a b) hclose ?_
  have hlt1 : ‖gradCLM d‖ / (‖gradCLM d‖ + 1) < 1 := by
    rw [div_lt_one hden]; linarith
  have : ‖gradCLM d‖ * (ε / (‖gradCLM d‖ + 1))
      = (‖gradCLM d‖ / (‖gradCLM d‖ + 1)) * ε := by ring
  rw [this]
  nlinarith

/-- **Lemma 3** (with its symmetric "lower" version): a shear by ∇V, V ∈ C^{r+1}, is
C^r-approximated on compacta by a single gradient module. -/
theorem shear_approx (hH : HornikDensity) (r : ℕ) (hr : 1 ≤ r) (σ : ℝ → ℝ) (hσ : RFinite r σ)
    (p : Bool × (E d → ℝ)) (hp : ContDiff ℝ (r + 1 : ℕ) p.2)
    (K : Set (X d)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : GradModule d, CrClose r K (shearOf p) (m.toFun σ) ε := by
  rcases p with ⟨up, V⟩
  simp only at hp
  cases up
  · obtain ⟨n, W, a, b, hclose⟩ :=
      grad_approx_core hH r σ hσ V hp _ (hK.image continuous_fst) hε
    exact ⟨⟨n, false, W, a, b⟩,
      crClose_lowShear (contDiff_grad hp) (contDiff_sigmaHat hσ.1 W a b) hclose⟩
  · obtain ⟨n, W, a, b, hclose⟩ :=
      grad_approx_core hH r σ hσ V hp _ (hK.image continuous_snd) hε
    exact ⟨⟨n, true, W, a, b⟩,
      crClose_upShear (contDiff_grad hp) (contDiff_sigmaHat hσ.1 W a b) hclose⟩

/-! ## §7 The composition estimate

This section proves `comp_stable`: replacing each factor of a finite composition by a
`C^r`-close map perturbs the composition by an arbitrarily small amount in `C^r` on a
compact set.  The paper argues with the Faà di Bruno expansion; we instead induct on `r`,
using the identity `D(h ∘ f) = B (Dh ∘ f) (Df)` with `B` the (norm ≤ 1) bilinear
composition map, so that one derivative is traded for one level of the induction. -/

section Toolbox

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Non-strict variant of `CrClose`, convenient for arithmetic. -/
def CrCloseLe (r : ℕ) (K : Set V) (f g : V → W) (ε : ℝ) : Prop :=
  ∀ k ≤ r, ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k g x‖ ≤ ε

/-- A uniform bound for all derivatives of order ≤ `r` on a set. -/
def CrBound (r : ℕ) (K : Set V) (f : V → W) (M : ℝ) : Prop :=
  ∀ k ≤ r, ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ M

variable {r r' : ℕ} {K K' : Set V} {f g : V → W} {ε ε' M : ℝ}

theorem CrClose.le (h : CrClose r K f g ε) : CrCloseLe r K f g ε :=
  fun k hk x hx => (h k hk x hx).le

theorem CrCloseLe.lt (h : CrCloseLe r K f g ε) (hlt : ε < ε') : CrClose r K f g ε' :=
  fun k hk x hx => lt_of_le_of_lt (h k hk x hx) hlt

theorem CrCloseLe.mono_set (h : CrCloseLe r K f g ε) (hS : K' ⊆ K) : CrCloseLe r K' f g ε :=
  fun k hk x hx => h k hk x (hS hx)

theorem CrCloseLe.mono_eps (h : CrCloseLe r K f g ε) (hε : ε ≤ ε') : CrCloseLe r K f g ε' :=
  fun k hk x hx => (h k hk x hx).trans hε

theorem CrCloseLe.of_le (h : CrCloseLe r K f g ε) (hr : r' ≤ r) : CrCloseLe r' K f g ε :=
  fun k hk x hx => h k (hk.trans hr) x hx

theorem CrClose.mono_set (h : CrClose r K f g ε) (hS : K' ⊆ K) : CrClose r K' f g ε :=
  fun k hk x hx => h k hk x (hS hx)

theorem CrBound.mono_set (h : CrBound r K f M) (hS : K' ⊆ K) : CrBound r K' f M :=
  fun k hk x hx => h k hk x (hS hx)

theorem CrBound.of_le (h : CrBound r K f M) (hr : r' ≤ r) : CrBound r' K f M :=
  fun k hk x hx => h k (hk.trans hr) x hx

/-- Zeroth-order information contained in `CrCloseLe`. -/
theorem CrCloseLe.norm_sub_le (h : CrCloseLe r K f g ε) (hf : ContDiff ℝ r f)
    (hg : ContDiff ℝ r g) {x : V} (hx : x ∈ K) : ‖f x - g x‖ ≤ ε := by
  have hz : ((0 : ℕ) : ℕ∞ω) ≤ ((r : ℕ) : ℕ∞ω) := Nat.cast_le.mpr (Nat.zero_le r)
  have h0 := h 0 (Nat.zero_le r) x hx
  rw [← iteratedFDeriv_sub_apply (hf.of_le hz).contDiffAt (hg.of_le hz).contDiffAt,
    norm_iteratedFDeriv_zero] at h0
  simpa using h0

/-- Trading one derivative: closeness in `C^{r+1}` of `h, u` gives closeness in `C^r`
of their derivatives. -/
theorem CrCloseLe.fderiv' {h u : V → W} (hc : CrCloseLe (r + 1) K h u ε)
    (hh : ContDiff ℝ (r + 1 : ℕ) h) (hu : ContDiff ℝ (r + 1 : ℕ) u) :
    CrCloseLe r K (fun y => fderiv ℝ h y) (fun y => fderiv ℝ u y) ε := by
  intro k hk x hx
  have hk1 : ((k : ℕ) : ℕ∞ω) ≤ ((r + 1 : ℕ) : ℕ∞ω) := Nat.cast_le.mpr (by omega)
  have hkk1 : ((k + 1 : ℕ) : ℕ∞ω) ≤ ((r + 1 : ℕ) : ℕ∞ω) := Nat.cast_le.mpr (by omega)
  have hdh : ContDiff ℝ ((k : ℕ) : ℕ∞ω) (fun y => fderiv ℝ h y) := by
    refine hh.fderiv_right ?_
    rw [show ((r + 1 : ℕ) : ℕ∞ω) = ((r : ℕ) : ℕ∞ω) + 1 by push_cast; ring]
    exact add_le_add (Nat.cast_le.mpr hk) le_rfl
  have hdu : ContDiff ℝ ((k : ℕ) : ℕ∞ω) (fun y => fderiv ℝ u y) := by
    refine hu.fderiv_right ?_
    rw [show ((r + 1 : ℕ) : ℕ∞ω) = ((r : ℕ) : ℕ∞ω) + 1 by push_cast; ring]
    exact add_le_add (Nat.cast_le.mpr hk) le_rfl
  rw [← iteratedFDeriv_sub_apply hdh.contDiffAt hdu.contDiffAt]
  have e1 : (fun y => fderiv ℝ h y) - (fun y => fderiv ℝ u y) = fderiv ℝ (h - u) := by
    funext y
    rw [fderiv_sub ((hh.differentiable (by positivity)) y)
      ((hu.differentiable (by positivity)) y)]
    rfl
  rw [e1, norm_iteratedFDeriv_fderiv,
    iteratedFDeriv_sub_apply (hh.of_le hkk1).contDiffAt (hu.of_le hkk1).contDiffAt]
  exact hc (k + 1) (by omega) x hx

end Toolbox

/-- Every `C^r` map is uniformly bounded in `C^r` on a compact set. -/
theorem exists_crBound {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (r : ℕ) {K : Set V} (hK : IsCompact K)
    {f : V → W} (hf : ContDiff ℝ r f) : ∃ M : ℝ, 0 ≤ M ∧ CrBound r K f M := by
  induction r with
  | zero =>
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
      ((hf.continuous_iteratedFDeriv (m := 0) le_rfl).continuousOn)
    refine ⟨max M 0, le_max_right _ _, fun k hk x hx => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    exact (hM x hx).trans (le_max_left _ _)
  | succ n ih =>
    obtain ⟨M₁, hM₁0, hM₁⟩ := ih (hf.of_le (Nat.cast_le.mpr (Nat.le_succ n)))
    obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn
      ((hf.continuous_iteratedFDeriv (m := n + 1) le_rfl).continuousOn)
    refine ⟨max M₁ M₂, hM₁0.trans (le_max_left _ _), fun k hk x hx => ?_⟩
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · exact (hM₁ k (by omega) x hx).trans (le_max_left _ _)
    · obtain rfl : k = n + 1 := le_antisymm hk h
      exact (hM₂ x hx).trans (le_max_right _ _)


section Estimates

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem norm_iteratedFDeriv_zero_sub {r : ℕ} {F G : V → W} (hF : ContDiff ℝ r F)
    (hG : ContDiff ℝ r G) (x : V) :
    ‖iteratedFDeriv ℝ 0 F x - iteratedFDeriv ℝ 0 G x‖ = ‖F x - G x‖ := by
  have hz : ((0 : ℕ) : ℕ∞ω) ≤ ((r : ℕ) : ℕ∞ω) := Nat.cast_le.mpr (Nat.zero_le r)
  rw [← iteratedFDeriv_sub_apply (hF.of_le hz).contDiffAt (hG.of_le hz).contDiffAt,
    norm_iteratedFDeriv_zero]
  rfl

/-- `‖D^{m+1}F − D^{m+1}G‖ = ‖D^m(DF) − D^m(DG)‖`. -/
theorem norm_iteratedFDeriv_succ_sub {m : ℕ} {F G : V → W} (hF : ContDiff ℝ (m + 1 : ℕ) F)
    (hG : ContDiff ℝ (m + 1 : ℕ) G) (x : V) :
    ‖iteratedFDeriv ℝ (m + 1) F x - iteratedFDeriv ℝ (m + 1) G x‖ =
      ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ F y) x -
        iteratedFDeriv ℝ m (fun y => fderiv ℝ G y) x‖ := by
  have hm : ((m + 1 : ℕ) : ℕ∞ω) = ((m : ℕ) : ℕ∞ω) + 1 := by push_cast; ring
  have hdF : ContDiff ℝ ((m : ℕ) : ℕ∞ω) (fun y => fderiv ℝ F y) :=
    hF.fderiv_right (by rw [hm])
  have hdG : ContDiff ℝ ((m : ℕ) : ℕ∞ω) (fun y => fderiv ℝ G y) :=
    hG.fderiv_right (by rw [hm])
  rw [← iteratedFDeriv_sub_apply hdF.contDiffAt hdG.contDiffAt,
    ← iteratedFDeriv_sub_apply hF.contDiffAt hG.contDiffAt]
  have e1 : (fun y => fderiv ℝ F y) - (fun y => fderiv ℝ G y) = fderiv ℝ (F - G) := by
    funext y
    rw [fderiv_sub ((hF.differentiable (by positivity)) y)
      ((hG.differentiable (by positivity)) y)]
    rfl
  rw [e1, norm_iteratedFDeriv_fderiv]

theorem sum_choose_mul_le {m : ℕ} {a b : ℕ → ℝ} {A B : ℝ} (hA : 0 ≤ A)
    (ha : ∀ i ≤ m, 0 ≤ a i ∧ a i ≤ A) (hb : ∀ i ≤ m, 0 ≤ b i ∧ b i ≤ B) :
    ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * a i * b (m - i) ≤ 2 ^ m * (A * B) := by
  calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * a i * b (m - i)
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (A * B) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact mul_le_mul (ha i hi').2 (hb (m - i) (Nat.sub_le _ _)).2
          (hb (m - i) (Nat.sub_le _ _)).1 hA
    _ = 2 ^ m * (A * B) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose m

end Estimates

/-- The bilinear difference estimate:
`B(p₁,q₁) − B(p₂,q₂) = B(p₁−p₂, q₁) + B(p₂, q₁−q₂)` and Leibniz' rule. -/
theorem bilinear_diff_estimate {D P Q R : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (B : P →L[ℝ] Q →L[ℝ] R) (hB : ‖B‖ ≤ 1) {m : ℕ}
    {p₁ p₂ : D → P} {q₁ q₂ : D → Q} (hp₁ : ContDiff ℝ m p₁) (hp₂ : ContDiff ℝ m p₂)
    (hq₁ : ContDiff ℝ m q₁) (hq₂ : ContDiff ℝ m q₂) (x : D) {η θ Mp Mq : ℝ}
    (hη : 0 ≤ η) (hθ : 0 ≤ θ) (hMp : 0 ≤ Mp) (hMq : 0 ≤ Mq)
    (h1 : ∀ i ≤ m, ‖iteratedFDeriv ℝ i p₁ x - iteratedFDeriv ℝ i p₂ x‖ ≤ η)
    (h2 : ∀ i ≤ m, ‖iteratedFDeriv ℝ i q₁ x‖ ≤ Mq)
    (h3 : ∀ i ≤ m, ‖iteratedFDeriv ℝ i p₁ x‖ ≤ Mp)
    (h4 : ∀ i ≤ m, ‖iteratedFDeriv ℝ i q₁ x - iteratedFDeriv ℝ i q₂ x‖ ≤ θ) :
    ‖iteratedFDeriv ℝ m (fun y => B (p₁ y) (q₁ y)) x -
        iteratedFDeriv ℝ m (fun y => B (p₂ y) (q₂ y)) x‖ ≤
      2 ^ m * (η * Mq + (Mp + η) * θ) := by
  have hle : ∀ i ≤ m, ((i : ℕ) : ℕ∞ω) ≤ ((m : ℕ) : ℕ∞ω) := fun i hi => Nat.cast_le.mpr hi
  have hdp : ContDiff ℝ m (p₁ - p₂) := hp₁.sub hp₂
  have hdq : ContDiff ℝ m (q₁ - q₂) := hq₁.sub hq₂
  have hF₁ : ContDiff ℝ m (fun y => B (p₁ y) (q₁ y)) := B.isBoundedBilinearMap.contDiff.comp
    (hp₁.prodMk hq₁)
  have hF₂ : ContDiff ℝ m (fun y => B (p₂ y) (q₂ y)) := B.isBoundedBilinearMap.contDiff.comp
    (hp₂.prodMk hq₂)
  have hT₁ : ContDiff ℝ m (fun y => B ((p₁ - p₂) y) (q₁ y)) :=
    B.isBoundedBilinearMap.contDiff.comp (hdp.prodMk hq₁)
  have hT₂ : ContDiff ℝ m (fun y => B (p₂ y) ((q₁ - q₂) y)) :=
    B.isBoundedBilinearMap.contDiff.comp (hp₂.prodMk hdq)
  have hsplit : (fun y => B (p₁ y) (q₁ y)) - (fun y => B (p₂ y) (q₂ y)) =
      (fun y => B ((p₁ - p₂) y) (q₁ y)) + (fun y => B (p₂ y) ((q₁ - q₂) y)) := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [← iteratedFDeriv_sub_apply hF₁.contDiffAt hF₂.contDiffAt, hsplit,
    iteratedFDeriv_add_apply hT₁.contDiffAt hT₂.contDiffAt]
  have b1 : ‖iteratedFDeriv ℝ m (fun y => B ((p₁ - p₂) y) (q₁ y)) x‖ ≤ 2 ^ m * (η * Mq) := by
    refine (B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hdp hq₁ x le_rfl hB).trans ?_
    refine sum_choose_mul_le (a := fun i => ‖iteratedFDeriv ℝ i (p₁ - p₂) x‖)
      (b := fun i => ‖iteratedFDeriv ℝ i q₁ x‖) hη (fun i hi => ⟨norm_nonneg _, ?_⟩)
      (fun i hi => ⟨norm_nonneg _, h2 i hi⟩)
    rw [iteratedFDeriv_sub_apply (hp₁.of_le (hle i hi)).contDiffAt
      (hp₂.of_le (hle i hi)).contDiffAt]
    exact h1 i hi
  have b2 : ‖iteratedFDeriv ℝ m (fun y => B (p₂ y) ((q₁ - q₂) y)) x‖ ≤
      2 ^ m * ((Mp + η) * θ) := by
    refine (B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hp₂ hdq x le_rfl hB).trans ?_
    refine sum_choose_mul_le (a := fun i => ‖iteratedFDeriv ℝ i p₂ x‖)
      (b := fun i => ‖iteratedFDeriv ℝ i (q₁ - q₂) x‖) (by positivity)
      (fun i hi => ⟨norm_nonneg _, ?_⟩) (fun i hi => ⟨norm_nonneg _, ?_⟩)
    · have := norm_sub_norm_le (iteratedFDeriv ℝ i p₂ x) (iteratedFDeriv ℝ i p₁ x)
      rw [norm_sub_rev] at this
      have := h1 i hi
      have := h3 i hi
      linarith
    · rw [iteratedFDeriv_sub_apply (hq₁.of_le (hle i hi)).contDiffAt
        (hq₂.of_le (hle i hi)).contDiffAt]
      exact h4 i hi
  calc _ ≤ ‖iteratedFDeriv ℝ m (fun y => B ((p₁ - p₂) y) (q₁ y)) x‖ +
        ‖iteratedFDeriv ℝ m (fun y => B (p₂ y) ((q₁ - q₂) y)) x‖ := norm_add_le _ _
    _ ≤ 2 ^ m * (η * Mq) + 2 ^ m * ((Mp + η) * θ) := add_le_add b1 b2
    _ = _ := by ring

/-! ### The compact enlargement `K ∪ T[f(K)]` of the paper -/

/-- `K ∪ {y | dist(y, f(K)) ≤ 1}`: the paper's `W ∪ T[f(W)]`. -/
def enlarge (f : X d → X d) (K : Set (X d)) : Set (X d) :=
  K ∪ Metric.cthickening 1 (f '' K)

theorem isCompact_enlarge {f : X d → X d} (hf : Continuous f) {K : Set (X d)}
    (hK : IsCompact K) : IsCompact (enlarge f K) :=
  hK.union (hK.image hf).cthickening

theorem subset_enlarge (f : X d → X d) (K : Set (X d)) : K ⊆ enlarge f K :=
  Set.subset_union_left

theorem mem_enlarge_of_dist_le {f : X d → X d} {K : Set (X d)} {x y : X d} (hx : x ∈ K)
    (hy : dist y (f x) ≤ 1) : y ∈ enlarge f K :=
  Or.inr (Metric.mem_cthickening_of_dist_le y (f x) 1 _ ⟨x, hx, rfl⟩ hy)

/-- The zeroth-order estimate for compositions (uniform continuity on the enlargement). -/
theorem comp_zero_estimate {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X d → X d} {h : X d → Y} (hf : Continuous f) (hh : Continuous h)
    {K : Set (X d)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ S, enlarge f K ⊆ S → ∀ (g : X d → X d) (u : X d → Y),
      (∀ x ∈ K, ‖f x - g x‖ ≤ δ) → (∀ y ∈ S, ‖h y - u y‖ ≤ δ) →
        ∀ x ∈ K, ‖h (f x) - u (g x)‖ ≤ ε := by
  have huc := (isCompact_enlarge hf hK).uniformContinuousOn_of_continuous hh.continuousOn
  obtain ⟨δ', hδ', hδ'h⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
  refine ⟨min (min (δ' / 2) 1) (ε / 2), by positivity,
    (min_le_left _ _).trans (min_le_right _ _), fun S hS g u hfg hhu x hx => ?_⟩
  have hδ1 : min (min (δ' / 2) 1) (ε / 2) ≤ δ' / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : min (min (δ' / 2) 1) (ε / 2) ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : min (min (δ' / 2) 1) (ε / 2) ≤ ε / 2 := min_le_right _ _
  have hd : dist (g x) (f x) ≤ min (min (δ' / 2) 1) (ε / 2) := by
    rw [dist_eq_norm, norm_sub_rev]; exact hfg x hx
  have hgx : g x ∈ enlarge f K := mem_enlarge_of_dist_le hx (hd.trans hδ2)
  have hfx : f x ∈ enlarge f K := mem_enlarge_of_dist_le hx (by simp)
  have e1 : dist (h (f x)) (h (g x)) < ε / 2 :=
    hδ'h _ hfx _ hgx (by rw [dist_comm]; linarith)
  have e2 := hhu (g x) (hS hgx)
  rw [dist_eq_norm] at e1
  calc ‖h (f x) - u (g x)‖ = ‖(h (f x) - h (g x)) + (h (g x) - u (g x))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖h (f x) - h (g x)‖ + ‖h (g x) - u (g x)‖ := norm_add_le _ _
    _ ≤ ε := by linarith

theorem CrClose.mono_eps {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {r : ℕ} {K : Set V} {f g : V → W} {ε ε' : ℝ}
    (h : CrClose r K f g ε) (hε : ε ≤ ε') : CrClose r K f g ε' :=
  fun k hk x hx => lt_of_lt_of_le (h k hk x hx) hε

/-- Two-map `C^r` stability of composition, by induction on `r`.  The outer map takes values
in an arbitrary normed space, since the inductive step is applied to `Dh : X → L(X, Y)`. -/
theorem comp_two_stable (r : ℕ) : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X d → X d) (h : X d → Y), ContDiff ℝ r f → ContDiff ℝ r h →
    ∀ K : Set (X d), IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ S : Set (X d), enlarge f K ⊆ S →
    ∀ (g : X d → X d) (u : X d → Y), ContDiff ℝ r g → ContDiff ℝ r u →
      CrCloseLe r S f g δ → CrCloseLe r S h u δ → CrCloseLe r K (h ∘ f) (u ∘ g) ε := by
  induction r with
  | zero =>
    intro Y _ _ f h hf hh K hK ε hε
    obtain ⟨δ, hδ, -, hδ'⟩ := comp_zero_estimate hf.continuous hh.continuous hK hε
    refine ⟨δ, hδ, fun S hS g u hg hu hfg hhu k hk x hx => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    rw [norm_iteratedFDeriv_zero_sub (hh.comp hf) (hu.comp hg)]
    exact hδ' S hS g u
      (fun y hy => hfg.norm_sub_le hf hg ((subset_enlarge f K).trans hS hy))
      (fun y hy => hhu.norm_sub_le hh hu hy) x hx
  | succ r ih =>
    intro Y _ _ f h hf hh K hK ε hε
    have hr1 : ((r + 1 : ℕ) : ℕ∞ω) = ((r : ℕ) : ℕ∞ω) + 1 := by push_cast; ring
    have hrle : ((r : ℕ) : ℕ∞ω) ≤ ((r + 1 : ℕ) : ℕ∞ω) := Nat.cast_le.mpr (Nat.le_succ r)
    have hdh : ContDiff ℝ r (fun y => fderiv ℝ h y) := hh.fderiv_right (by rw [hr1])
    have hfr : ContDiff ℝ r f := hf.of_le hrle
    obtain ⟨Mf, hMf0, hMf⟩ := exists_crBound (r + 1) hK hf
    obtain ⟨Ma, hMa0, hMa⟩ := exists_crBound r hK (hdh.comp hfr)
    set C : ℝ := 2 ^ r * (Mf + Ma + 2) with hC
    have hCpos : 0 < C := by positivity
    set t : ℝ := ε / (2 * C) with ht
    have ht0 : 0 < t := by positivity
    have hCt : C * t = ε / 2 := by rw [ht]; field_simp
    set η : ℝ := min 1 t with hη
    have hη0 : 0 < η := lt_min one_pos ht0
    obtain ⟨δa, hδa, hδa'⟩ := ih f (fun y => fderiv ℝ h y) hfr hdh K hK η hη0
    obtain ⟨δ₀, hδ₀, -, hδ₀'⟩ := comp_zero_estimate hf.continuous hh.continuous hK hε
    refine ⟨min (min δa δ₀) t, lt_min (lt_min hδa hδ₀) ht0,
      fun S hS g u hg hu hfg hhu => ?_⟩
    set δ := min (min δa δ₀) t
    have hδa_le : δ ≤ δa := (min_le_left _ _).trans (min_le_left _ _)
    have hδ₀_le : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_right _ _)
    have hδt : δ ≤ t := min_le_right _ _
    have hδ0 : 0 ≤ δ := le_of_lt (lt_min (lt_min hδa hδ₀) ht0)
    have hKS : K ⊆ S := (subset_enlarge f K).trans hS
    have hgr : ContDiff ℝ r g := hg.of_le hrle
    have hdu : ContDiff ℝ r (fun y => fderiv ℝ u y) := hu.fderiv_right (by rw [hr1])
    have hdf : ContDiff ℝ r (fun y => fderiv ℝ f y) := hf.fderiv_right (by rw [hr1])
    have hdg : ContDiff ℝ r (fun y => fderiv ℝ g y) := hg.fderiv_right (by rw [hr1])
    -- the induction hypothesis, applied to `Dh ∘ f` versus `Du ∘ g`
    have hA : CrCloseLe r K ((fun y => fderiv ℝ h y) ∘ f) ((fun y => fderiv ℝ u y) ∘ g) η :=
      hδa' S hS g (fun y => fderiv ℝ u y) hgr hdu
        ((hfg.of_le (Nat.le_succ r)).mono_eps hδa_le) ((hhu.fderiv' hh hu).mono_eps hδa_le)
    have hθ : CrCloseLe r S (fun y => fderiv ℝ f y) (fun y => fderiv ℝ g y) δ :=
      hfg.fderiv' hf hg
    intro k hk x hx
    rcases k with _ | m
    · rw [norm_iteratedFDeriv_zero_sub (hh.comp hf) (hu.comp hg)]
      exact hδ₀' S hS g u
        (fun y hy => (hfg.norm_sub_le hf hg (hKS hy)).trans hδ₀_le)
        (fun y hy => (hhu.norm_sub_le hh hu hy).trans hδ₀_le) x hx
    · have hm : m ≤ r := by omega
      have hmle : ((m : ℕ) : ℕ∞ω) ≤ ((r : ℕ) : ℕ∞ω) := Nat.cast_le.mpr hm
      have hm1 : ((m + 1 : ℕ) : ℕ∞ω) ≤ ((r + 1 : ℕ) : ℕ∞ω) := Nat.cast_le.mpr (by omega)
      rw [norm_iteratedFDeriv_succ_sub ((hh.comp hf).of_le hm1) ((hu.comp hg).of_le hm1) x]
      have ef : (fun y => fderiv ℝ (h ∘ f) y) = fun y =>
          ContinuousLinearMap.compL ℝ (X d) (X d) Y (fderiv ℝ h (f y)) (fderiv ℝ f y) := by
        funext y
        rw [fderiv_comp y ((hh.differentiable (by positivity)) (f y))
          ((hf.differentiable (by positivity)) y)]
        rfl
      have eg : (fun y => fderiv ℝ (u ∘ g) y) = fun y =>
          ContinuousLinearMap.compL ℝ (X d) (X d) Y (fderiv ℝ u (g y)) (fderiv ℝ g y) := by
        funext y
        rw [fderiv_comp y ((hu.differentiable (by positivity)) (g y))
          ((hg.differentiable (by positivity)) y)]
        rfl
      rw [ef, eg]
      have hη1 : η ≤ 1 := min_le_left _ _
      have hηt : η ≤ t := min_le_right _ _
      have h2m : (2 : ℝ) ^ m ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hm
      have hbil := bilinear_diff_estimate (ContinuousLinearMap.compL ℝ (X d) (X d) Y)
        (ContinuousLinearMap.norm_compL_le ℝ (X d) (X d) Y)
        (p₁ := fun y => fderiv ℝ h (f y)) (p₂ := fun y => fderiv ℝ u (g y))
        (q₁ := fun y => fderiv ℝ f y) (q₂ := fun y => fderiv ℝ g y)
        ((hdh.comp hfr).of_le hmle) ((hdu.comp hgr).of_le hmle) (hdf.of_le hmle)
        (hdg.of_le hmle) x hη0.le hδ0 hMa0 hMf0
        (fun i hi => hA i (hi.trans hm) x hx)
        (fun i hi => by
          rw [norm_iteratedFDeriv_fderiv]; exact hMf (i + 1) (by omega) x hx)
        (fun i hi => hMa i (hi.trans hm) x hx)
        (fun i hi => hθ i (hi.trans hm) x (hKS hx))
      refine hbil.trans ?_
      have hp : 0 ≤ (2 : ℝ) ^ r * t := by positivity
      calc (2 : ℝ) ^ m * (η * Mf + (Ma + η) * δ)
          ≤ 2 ^ r * (t * Mf + (Ma + 1) * t) := by
            gcongr
        _ ≤ C * t := by rw [hC]; nlinarith
        _ = ε / 2 := hCt
        _ ≤ ε := by linarith

/-- C^r stability of finite compositions (the main estimate in the proof of Theorem 5):
if each Fᵢ is C^r, there are δ > 0 and a compact enlargement K' ⊇ K (the paper's W̃) such that
replacing every Fᵢ by a C^r map Gᵢ that is δ-close in C^r(K') changes the composition by < ε
in C^r(K).  Proved by induction on the list using `comp_two_stable`. -/
theorem comp_stable (r : ℕ) {ι : Type*} (l : List ι) (F : ι → X d → X d)
    (hF : ∀ i ∈ l, ContDiff ℝ r (F i)) (K : Set (X d)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ K' : Set (X d), IsCompact K' ∧
      ∀ G : ι → X d → X d, (∀ i ∈ l, ContDiff ℝ r (G i) ∧ CrClose r K' (F i) (G i) δ) →
        CrClose r K (compList (l.map F)) (compList (l.map G)) ε := by
  induction l generalizing K ε with
  | nil =>
    refine ⟨1, one_pos, K, hK, fun G _ k _ x _ => ?_⟩
    simpa [compList] using hε
  | cons i rest ih =>
    have hFi : ContDiff ℝ r (F i) := hF i List.mem_cons_self
    have hFrest : ∀ j ∈ rest, ContDiff ℝ r (F j) :=
      fun j hj => hF j (List.mem_cons_of_mem _ hj)
    have hH : ContDiff ℝ r (compList (rest.map F)) := contDiff_compList _ fun f hf => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf; exact hFrest j hj
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ :=
      comp_two_stable r (F i) (compList (rest.map F)) hFi hH K hK (ε / 2) (half_pos hε)
    have hS₀ : IsCompact (enlarge (F i) K) := isCompact_enlarge hFi.continuous hK
    obtain ⟨δ₁, hδ₁, K₁, hK₁, h₁⟩ := ih hFrest (enlarge (F i) K) hS₀ hδ₀
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, K₁ ∪ enlarge (F i) K, hK₁.union hS₀,
      fun G hG => ?_⟩
    have hGi := hG i List.mem_cons_self
    have hrest : CrClose r (enlarge (F i) K) (compList (rest.map F))
        (compList (rest.map G)) δ₀ :=
      h₁ G fun j hj => ⟨(hG j (List.mem_cons_of_mem _ hj)).1,
        ((hG j (List.mem_cons_of_mem _ hj)).2.mono_set Set.subset_union_left).mono_eps
          (min_le_right _ _)⟩
    have hGrest : ContDiff ℝ r (compList (rest.map G)) := contDiff_compList _ fun f hf => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
      exact (hG j (List.mem_cons_of_mem _ hj)).1
    have hc := hδ₀' (enlarge (F i) K) subset_rfl (G i) (compList (rest.map G)) hGi.1 hGrest
      ((hGi.2.mono_set Set.subset_union_right).mono_eps (min_le_left _ _)).le hrest.le
    exact hc.lt (half_lt_self hε)

/-! ## §3' More algebra (proved), using `V₀_facts` -/

theorem compList_henonFactors (V : E d → ℝ) :
    compList ((henonFactors V).map shearOf) = henon V := by
  obtain ⟨-, -, hg₀, hg₁⟩ := V₀_facts (d := d) 0
  rw [henon_eq]
  simp only [henonFactors, List.map_cons, List.map_nil, compList, shearOf, Bool.cond_true,
    Bool.cond_false, hg₀, hg₁, Function.id_comp, Function.comp_assoc]

theorem compList_henon (Vs : List (E d → ℝ)) :
    compList (Vs.map henon) = compList ((Vs.flatMap henonFactors).map shearOf) := by
  induction Vs with
  | nil => rfl
  | cons V Vs ih =>
    simp only [List.map_cons, compList]
    rw [ih, List.flatMap_cons, List.map_append, compList_append, compList_henonFactors]

/-! ### Injectivity of G-SympNets -/

theorem injective_upShear (g : E d → E d) : Function.Injective (upShear g) := by
  rintro ⟨p₁, q₁⟩ ⟨p₂, q₂⟩ h
  simp only [upShear, Prod.mk.injEq] at h
  obtain ⟨h₁, rfl⟩ := h
  simp [add_right_cancel h₁]

theorem injective_lowShear (g : E d → E d) : Function.Injective (lowShear g) := by
  rintro ⟨p₁, q₁⟩ ⟨p₂, q₂⟩ h
  simp only [lowShear, Prod.mk.injEq] at h
  obtain ⟨rfl, h₂⟩ := h
  simp [add_right_cancel h₂]

theorem injective_henon (V : E d → ℝ) : Function.Injective (henon V) := by
  rintro ⟨p₁, q₁⟩ ⟨p₂, q₂⟩ h
  simp only [henon, Prod.mk.injEq] at h
  obtain ⟨rfl, h₂⟩ := h
  simp [neg_inj.1 (add_right_cancel h₂)]

theorem GradModule.injective (m : GradModule d) (σ : ℝ → ℝ) :
    Function.Injective (m.toFun σ) := by
  rcases m with ⟨k, up, K, a, b⟩
  cases up
  · exact injective_lowShear _
  · exact injective_upShear _

theorem injective_compList {α : Type*} (l : List (α → α)) (h : ∀ f ∈ l, Function.Injective f) :
    Function.Injective (compList l) := by
  induction l with
  | nil => exact Function.injective_id
  | cons f fs ih =>
    exact (ih fun g hg => h g (List.mem_cons_of_mem _ hg)).comp (h f List.mem_cons_self)

theorem GSympNet.injective {σ : ℝ → ℝ} {Φ : X d → X d} (hΦ : Φ ∈ GSympNet σ) :
    Function.Injective Φ := by
  obtain ⟨l, rfl⟩ := hΦ
  refine injective_compList _ fun f hf => ?_
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hf
  exact m.injective σ

/-! ## §5 Main theorem -/

/-- **Theorem 5** for convex U and injective maps. For r ≥ 1, U ⊆ ℝ^{2d} open and convex, and
σ r-finite, the G-SympNets are r-uniformly dense on compacta in the injective maps of SP^r(U).
(The paper states this for all of SP^r(U) and arbitrary open U, which is false:
`paper_theorem5_false` in `Sympnet/Counterexample.lean`.)
Hypotheses `hH`, `hT` are the cited results (Lemma 2 = Hornik et al., Lemma 4 = Turaev). -/
theorem G_SympNet_universal (hH : HornikDensity) (hT : TuraevHenon)
    (r : ℕ) (hr : 1 ≤ r) (σ : ℝ → ℝ) (hσ : RFinite r σ)
    (U : Set (X d)) (hU : IsOpen U) (hUc : Convex ℝ U) :
    UDense r U (GSympNet (d := d) σ) {F | F ∈ SP r U ∧ Set.InjOn F U} := by
  refine ⟨fun Φ hΦ => ⟨GSympNet_subset_SP r hr σ hσ U hΦ, (GSympNet.injective hΦ).injOn⟩, ?_⟩
  rintro F ⟨hF, hFinj⟩ K hK hKU ε hε
  -- Step 1 (Turaev): F ≈ H[Vₙ] ∘ ⋯ ∘ H[V₁] within ε/2.
  obtain ⟨Vs, hVs, hFH⟩ := hT d r hr U hU hUc F hF hFinj K hK hKU (ε / 2) (half_pos hε)
  -- Each Hénon map splits into four gradient shears with C^{r+1} potentials.
  have hfac : ∀ V : E d → ℝ, ContDiff ℝ (r + 1 : ℕ) V →
      ∀ p ∈ henonFactors V, ContDiff ℝ (r + 1 : ℕ) p.2 := by
    intro V hV p hp
    simp [henonFactors] at hp
    rcases hp with rfl | rfl | rfl | rfl
    exacts [(V₀_facts (r + 1)).1, (V₀_facts (r + 1)).2.1, (V₀_facts (r + 1)).1, hV]
  have hps : ∀ p ∈ Vs.flatMap henonFactors, ContDiff ℝ (r + 1 : ℕ) p.2 := by
    intro p hp
    obtain ⟨V, hV, hp⟩ := List.mem_flatMap.1 hp
    exact hfac V (hVs V hV) p hp
  -- Step 2 (stability of compositions): tolerance δ on an enlarged compact K'.
  obtain ⟨δ, hδ, K', hK', hstab⟩ :=
    comp_stable r (Vs.flatMap henonFactors) shearOf
      (fun p hp => contDiff_shearOf r p (hps p hp)) K hK (half_pos hε)
  -- Step 3 (Lemma 3): approximate each shear by one gradient module.
  have hM : ∀ p : Bool × (E d → ℝ), ∃ m : GradModule d,
      ContDiff ℝ (r + 1 : ℕ) p.2 → CrClose r K' (shearOf p) (m.toFun σ) δ := by
    intro p
    by_cases hp : ContDiff ℝ (r + 1 : ℕ) p.2
    · obtain ⟨m, hm⟩ := shear_approx hH r hr σ hσ p hp K' hK' hδ
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, true, 0, 0, 0⟩, fun h => absurd h hp⟩
  choose M hM using hM
  -- Step 4: the resulting G-SympNet is ε-close to F.
  refine ⟨compList ((Vs.flatMap henonFactors).map fun p => (M p).toFun σ),
    ⟨(Vs.flatMap henonFactors).map M, by rw [List.map_map]; rfl⟩, ?_⟩
  have h₁ : CrClose r K F (compList ((Vs.flatMap henonFactors).map shearOf)) (ε / 2) := by
    rw [← compList_henon]
    exact hFH
  have h₂ := hstab (fun p => (M p).toFun σ)
    (fun p hp => ⟨GradModule.contDiff (M p) r σ hσ, hM p (hps p hp)⟩)
  have h := h₁.trans h₂
  rwa [add_halves] at h

end SympNet
