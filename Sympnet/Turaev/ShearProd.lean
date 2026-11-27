/-
  T-S: finite compositions of gradient shears with smooth potentials (`ShearProd`), and the
  elementary maps that belong to it: shears by symmetric linear maps, translations, and
  symplectic transvections z ↦ z + φ'(ℓ z)·Jℓ (the time-one maps of ridge Hamiltonians).
-/
import Sympnet.Turaev.ProdBound

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace SympNet

variable {d : ℕ}

/-- Finite compositions of gradient shears with smooth potentials. -/
def ShearProd (d : ℕ) : Set (X d → X d) :=
  {Φ | ∃ l : List (Bool × (E d → ℝ)), (∀ p ∈ l, ContDiff ℝ ∞ p.2) ∧ Φ = compList (l.map shearOf)}

namespace ShearProd

theorem id_mem : (id : X d → X d) ∈ ShearProd d := ⟨[], by simp, rfl⟩

theorem comp {f g : X d → X d} (hf : f ∈ ShearProd d) (hg : g ∈ ShearProd d) :
    g ∘ f ∈ ShearProd d := by
  obtain ⟨lf, hlf, rfl⟩ := hf
  obtain ⟨lg, hlg, rfl⟩ := hg
  refine ⟨lf ++ lg, fun p hp => ?_, by rw [List.map_append, compList_append]⟩
  rcases List.mem_append.1 hp with h | h
  exacts [hlf p h, hlg p h]

theorem shearOf_mem (p : Bool × (E d → ℝ)) (hp : ContDiff ℝ ∞ p.2) :
    shearOf p ∈ ShearProd d :=
  ⟨[p], by simpa using hp, by simp [compList]⟩

theorem upShear_mem {V : E d → ℝ} (hV : ContDiff ℝ ∞ V) : upShear (grad V) ∈ ShearProd d :=
  shearOf_mem (true, V) hV

theorem lowShear_mem {V : E d → ℝ} (hV : ContDiff ℝ ∞ V) : lowShear (grad V) ∈ ShearProd d :=
  shearOf_mem (false, V) hV

theorem contDiff {Φ : X d → X d} (h : Φ ∈ ShearProd d) : ContDiff ℝ ∞ Φ := by
  obtain ⟨l, hl, rfl⟩ := h
  refine contDiff_compList _ fun f hf => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hf
  have h2 : ContDiff ℝ ∞ (grad p.2) := by
    rw [grad_eq_gradCLM]
    exact (gradCLM d).contDiff.comp ((hl p hp).fderiv_right (m := ∞) (by simp))
  rcases p with ⟨b, V⟩
  cases b
  · exact contDiff_lowShear h2
  · exact contDiff_upShear h2

end ShearProd

/-! ### Shears are Hénon products -/

theorem grad_neg (V : E d → ℝ) : grad (fun x => -V x) = fun x => -grad V x := by
  funext x i; simp [grad]

theorem grad_zero_fun : grad (0 : E d → ℝ) = 0 := by
  funext x i; simp [grad]

/-- Hénon factors of a shear. -/
def shearHenon : Bool × (E d → ℝ) → List (E d → ℝ)
  | (true, V) => [fun x => -V x, 0, 0, 0]
  | (false, V) => [0, 0, 0, V]

theorem compList_shearHenon (p : Bool × (E d → ℝ)) :
    compList ((shearHenon p).map henon) = shearOf p := by
  rcases p with ⟨b, V⟩
  funext z
  rcases z with ⟨x, y⟩
  cases b <;> simp [shearHenon, compList, henon, shearOf, upShear, lowShear, grad_neg,
    grad_zero_fun] <;> exact add_comm _ _

theorem ShearProd.exists_henon {Φ : X d → X d} (h : Φ ∈ ShearProd d) :
    ∃ Vs : List (E d → ℝ), (∀ V ∈ Vs, ContDiff ℝ ∞ V) ∧ Φ = compList (Vs.map henon) := by
  obtain ⟨l, hl, rfl⟩ := h
  refine ⟨l.flatMap shearHenon, fun V hV => ?_, ?_⟩
  · obtain ⟨p, hp, hV⟩ := List.mem_flatMap.1 hV
    have := hl p hp
    rcases p with ⟨b, W⟩
    cases b <;> simp [shearHenon] at hV <;> rcases hV with rfl | rfl <;>
      first | exact contDiff_const | exact this | exact this.neg
  · induction l with
    | nil => rfl
    | cons p l ih =>
      simp only [List.map_cons, compList, List.flatMap_cons, List.map_append, compList_append,
        compList_shearHenon]
      rw [ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]

/-! ### Linear shears -/

/-- Potential `½⟨f x, x⟩` of a symmetric linear map. -/
def qpot (f : E d →ₗ[ℝ] E d) (x : E d) : ℝ := 1 / 2 * (f x ⬝ᵥ x)

theorem contDiff_qpot (f : E d →ₗ[ℝ] E d) : ContDiff ℝ ∞ (qpot f) := by
  have hf : ContDiff ℝ ∞ (fun x => f x) := (LinearMap.toContinuousLinearMap f).contDiff
  unfold qpot
  simp only [dotProduct]
  refine contDiff_const.mul (ContDiff.sum fun i _ => ?_)
  exact ((contDiff_apply ℝ (fun _ : Fin d => ℝ) i).comp hf).mul (contDiff_apply ℝ _ i)

theorem grad_qpot (f : E d →ₗ[ℝ] E d) (hf : ∀ u v, f u ⬝ᵥ v = f v ⬝ᵥ u) :
    grad (qpot f) = f := by
  set F := LinearMap.toContinuousLinearMap f
  funext x i
  have hterm : ∀ k : Fin d, HasFDerivAt (fun y : E d => f y k * y k)
      (f x k • (ContinuousLinearMap.proj k : E d →L[ℝ] ℝ) +
        x k • ((ContinuousLinearMap.proj k : E d →L[ℝ] ℝ).comp F)) x := by
    intro k
    have h1 : HasFDerivAt (fun y : E d => f y k) ((ContinuousLinearMap.proj k).comp F) x :=
      ((ContinuousLinearMap.proj k).comp F).hasFDerivAt
    have h2 : HasFDerivAt (fun y : E d => y k) (ContinuousLinearMap.proj k : E d →L[ℝ] ℝ) x :=
      hasFDerivAt_apply k x
    exact h1.mul h2
  have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => hterm k).const_mul (1 / 2 : ℝ)
  have heq : (fun y => 1 / 2 * ∑ k ∈ Finset.univ, f y k * y k) = qpot f := by
    funext y; simp [qpot, dotProduct]
  rw [heq] at hsum
  rw [grad, hsum.fderiv]
  have hs := hf x (Pi.single i 1)
  have e1 : f x ⬝ᵥ Pi.single i 1 = f x i := by simp [dotProduct, Pi.single_apply]
  have e2 : f (Pi.single i 1) ⬝ᵥ x = ∑ k, x k * f (Pi.single i 1) k := by
    simp [dotProduct, mul_comm]
  rw [e1, e2] at hs
  simp [F, Pi.single_apply, Finset.sum_add_distrib, ← hs]
  ring

theorem upShear_lin_mem (f : E d →ₗ[ℝ] E d) (hf : ∀ u v, f u ⬝ᵥ v = f v ⬝ᵥ u) :
    upShear f ∈ ShearProd d := by
  have := ShearProd.upShear_mem (contDiff_qpot f)
  rwa [grad_qpot f hf] at this

theorem lowShear_lin_mem (f : E d →ₗ[ℝ] E d) (hf : ∀ u v, f u ⬝ᵥ v = f v ⬝ᵥ u) :
    lowShear f ∈ ShearProd d := by
  have := ShearProd.lowShear_mem (contDiff_qpot f)
  rwa [grad_qpot f hf] at this

theorem neg_symm {f : E d →ₗ[ℝ] E d} (hf : ∀ u v, f u ⬝ᵥ v = f v ⬝ᵥ u) :
    ∀ u v, (-f) u ⬝ᵥ v = (-f) v ⬝ᵥ u := fun u v => by simp [neg_dotProduct, hf u v]

/-! ### Translations -/

theorem translate_mem (c : X d) : (fun z : X d => z + c) ∈ ShearProd d := by
  have h1 := ShearProd.upShear_mem (linPot c.1).contDiff
  have h2 := ShearProd.lowShear_mem (linPot c.2).contDiff
  rw [grad_linPot] at h1 h2
  have := ShearProd.comp h2 h1
  convert this using 1
  funext z; rfl

theorem const_add_mem {Φ : X d → X d} (h : Φ ∈ ShearProd d) (c : X d) :
    (fun z => c + Φ z) ∈ ShearProd d := by
  have := ShearProd.comp h (translate_mem c)
  convert this using 1; funext z; simp [add_comm]

theorem comp_add_mem {Φ : X d → X d} (h : Φ ∈ ShearProd d) (c : X d) :
    (fun z => Φ (z + c)) ∈ ShearProd d := ShearProd.comp (translate_mem c) h

/-! ### Transvections -/

/-- The symplectic dual vector `Jℓ = (−∇_q ℓ, ∇_p ℓ)` of a covector. -/
def Jop (d : ℕ) (ℓ : X d →L[ℝ] ℝ) : X d := (-(clmQ d ℓ), clmP d ℓ)

/-- The transvection z ↦ z + φ'(ℓ z) • Jℓ: time-one map of the ridge Hamiltonian φ ∘ ℓ. -/
def transv (φ : ℝ → ℝ) (ℓ : X d →L[ℝ] ℝ) (z : X d) : X d := z + deriv φ (ℓ z) • Jop d ℓ

theorem dot_clmP (L : X d →L[ℝ] ℝ) (t : E d) : clmP d L ⬝ᵥ t = L (t, 0) := sum_clmP_mul L t

theorem dot_clmQ (L : X d →L[ℝ] ℝ) (t : E d) : clmQ d L ⬝ᵥ t = L (0, t) := sum_clmQ_mul L t

theorem clm_eq_dot (L : X d →L[ℝ] ℝ) (z : X d) :
    L z = clmP d L ⬝ᵥ z.1 + clmQ d L ⬝ᵥ z.2 := by
  rw [dot_clmP, dot_clmQ, ← map_add]; simp

theorem linPot_eq_dot (a : E d) : (fun x => a ⬝ᵥ x) = ⇑(linPot a) := by
  funext x; simp [linPot, dotProduct]

/-- Gradient of a ridge potential. -/
theorem grad_ridge {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (a : E d) :
    grad (fun x => φ (a ⬝ᵥ x)) = fun x => deriv φ (a ⬝ᵥ x) • a := by
  funext x i
  have h1 : HasFDerivAt (fun x => a ⬝ᵥ x) (linPot a) x := by
    rw [linPot_eq_dot]; exact (linPot a).hasFDerivAt
  have h := (hφ (a ⬝ᵥ x)).hasDerivAt.comp_hasFDerivAt x h1
  rw [grad, show (fun x => φ (a ⬝ᵥ x)) = φ ∘ dotProduct a from rfl, h.fderiv]
  simp [linPot, Pi.single_apply]

theorem contDiff_ridge {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (a : E d) :
    ContDiff ℝ ∞ (fun x : E d => φ (a ⬝ᵥ x)) := by
  rw [show (fun x : E d => φ (a ⬝ᵥ x)) = φ ∘ ⇑(linPot a) by
    funext x; simp [← linPot_eq_dot]]
  exact hφ.comp (linPot a).contDiff

/-- The symmetric linear map with `S b = −a` (for `b ≠ 0`). -/
def symmMap (a b : E d) : E d →ₗ[ℝ] E d where
  toFun q := (-(b ⬝ᵥ b)⁻¹) • ((b ⬝ᵥ q) • a + (a ⬝ᵥ q) • b) +
    ((a ⬝ᵥ b) * ((b ⬝ᵥ b)⁻¹) ^ 2 * (b ⬝ᵥ q)) • b
  map_add' u v := by
    funext i; simp only [dotProduct_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  map_smul' c u := by
    funext i
    simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply, Pi.add_apply, Pi.smul_apply]
    ring

theorem symmMap_symm (a b : E d) : ∀ u v, symmMap a b u ⬝ᵥ v = symmMap a b v ⬝ᵥ u := by
  intro u v
  simp only [symmMap, LinearMap.coe_mk, AddHom.coe_mk, add_dotProduct, smul_dotProduct,
    smul_eq_mul]
  rw [dotProduct_comm a v, dotProduct_comm b v, dotProduct_comm a u, dotProduct_comm b u]
  ring

theorem symmMap_b {a b : E d} (hb : b ⬝ᵥ b ≠ 0) : symmMap a b b = -a := by
  simp only [symmMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dotProduct_comm a b]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  field_simp
  ring

theorem transv_mem {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (ℓ : X d →L[ℝ] ℝ) :
    transv φ ℓ ∈ ShearProd d := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  set a := clmP d ℓ
  set b := clmQ d ℓ
  have hℓ : ∀ z : X d, ℓ z = a ⬝ᵥ z.1 + b ⬝ᵥ z.2 := clm_eq_dot ℓ
  by_cases hb : b ⬝ᵥ b = 0
  · have hb0 : b = 0 := dotProduct_self_eq_zero.1 hb
    have h := ShearProd.lowShear_mem (contDiff_ridge hφ a)
    rw [grad_ridge hφd] at h
    have hb0' : clmQ d ℓ = 0 := hb0
    convert h using 1
    funext z
    refine Prod.ext ?_ ?_ <;> simp [transv, Jop, lowShear, hℓ, hb0', hb0] <;> rfl
  · set S := symmMap a b
    have hS := symmMap_symm a b
    have hSb : S b = -a := symmMap_b hb
    have h1 := lowShear_lin_mem (-S) (neg_symm hS)
    have h2 := ShearProd.upShear_mem (contDiff_ridge hφ b).neg
    have h3 := lowShear_lin_mem S hS
    have h := ShearProd.comp (ShearProd.comp h1 h2) h3
    convert h using 1
    funext z
    rcases z with ⟨p, q⟩
    have hgrad := congrFun (grad_neg (fun x => φ (b ⬝ᵥ x))) (q + (-S) p)
    rw [grad_ridge hφd] at hgrad
    have hdot : b ⬝ᵥ (q + (-S) p) = a ⬝ᵥ p + b ⬝ᵥ q := by
      rw [dotProduct_add, LinearMap.neg_apply, dotProduct_neg, dotProduct_comm b (S p),
        hS p b, hSb, neg_dotProduct, neg_neg, add_comm]
    simp only [Function.comp_apply, lowShear, upShear, hgrad, hdot, transv, Jop, hℓ]
    refine Prod.ext ?_ ?_
    · simp [smul_neg]; rfl
    · simp only [Prod.snd_add, Prod.smul_snd, map_add, map_neg, map_smul, hSb, LinearMap.neg_apply]
      simp only [smul_neg, neg_neg]
      abel

end SympNet
