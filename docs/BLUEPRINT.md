# Blueprint: proving `SymplecticApprox` (removes Smoothing + Extension hypotheses)

Goal (`SymplecticApprox`): for r ≥ 1, U ⊆ X open convex, F ∈ SP^r(U) injective on U, K ⊆ U compact,
ε > 0: ∃ G ∈ SympDiffeo (global C^∞ symplectic bijection) with CrClose r K F G ε.
Then `TuraevLiteral + SymplecticApprox → TuraevHenon` (easy, like `TuraevHenon_of_literal`).

Notation: X = E × E, z = (p,q), ω(u,v) = u.1·v.2 − u.2·v.1 (`symplecticForm`).

## Strategy (exact Alexander scheme, smoothing at the end)
WLOG K ⊆ R0 ⋐ R'' ⋐ R' ⋐ U, all open convex (thickenings of convex hull of K), x0 ∈ K.
Alexander family: F_t(x) = y0 + (F(x0 + t(x−x0)) − y0)/t (t>0), F_0(x) = y0 + DF(x0)(x−x0).
DF_t(x) = DF(x0 + t(x−x0)) ⇒ symplectic; F_t injective on U; F_1 = F; F_0 affine global diffeo.
Partition 0 = t_0 < … < t_N = 1. Piece i: A = F_{t_{i-1}}, B = F_{t_i}.

### C7 pair generating function (A, B close in C^1 on R')
β_x(v) = (A_p − B_p)·DA_q v + (B_q − A_q)·DB_p v   (continuous 1-form on convex R')
μ = (B_p, A_q) : R' → X  (injective, local diffeo; μ⁻¹ C^r)
θ(z')(w) = (B_q − A_q)∘μ⁻¹ · w1 + (A_p − B_p)∘μ⁻¹ · w2  is C^1 & closed on μ(R')  [algebra: uses ω∘DA = ω = ω∘DB]
β = μ*θ, locally exact (Mathlib Poincaré on balls) ⇒ (C6 Goursat) S on R' with dS = β
s := S ∘ μ⁻¹ on μ(R'), ds = θ, s ∈ C^{r+1}.  s̃ := χ·s, χ = 1 near μ(R0), tsupport χ ⊆ μ(R'').
KEY IDENTITY: Ψ₁(μ x) = A x, Ψ₂(μ x) = B x  where Ψ₁(P,q) = (P + ∂_q s̃, q), Ψ₂(P,q) = (P, q + ∂_P s̃).
Hence Φ_{s̃}(A x) = B x for x ∈ R0  (Φ_s := Ψ₂ ∘ Ψ₁⁻¹).

### C4 global map from generating function
s : X → ℝ, C^{k+1}, compact support, ‖D(∇s)‖ ≤ 1/2 everywhere ⇒ Ψ₁ = id + g homeomorph
(`ApproximatesLinearOn.toHomeomorph`), Ψ₁⁻¹ C^k (`Homeomorph.contDiff_symm`), Φ_s C^k bijective,
symplectic: ω(DΨ₂a, DΨ₂b) = ω(DΨ₁a, DΨ₁b) (Hessian symmetry).

### Assembly C9
Ψ_0 = F_0, Ψ_i = Φ_i ∘ Ψ_{i-1}; induction: Ψ_i = F_{t_i} on R0. So F = Ψ_N on R0 ⊇ K.
Smoothing: mollify s̃_i (C2) ⇒ Φ_i^δ smooth, → Φ_i in C^r on compacta (C5 inverse continuity),
`comp_stable` ⇒ Ψ^δ → Ψ_N on K. Ψ^δ ∈ SympDiffeo.

### Uniform constants (C8), all over t ∈ [0,1]
* ‖DF_t(x)⁻¹‖ ≤ sup_{y ∈ cl R'} ‖DF(y)⁻¹‖ (x0 + t(x−x0) ∈ cl R').
* antilipschitz: |F x − F y| ≥ c|x−y| on cl R' (compactness + `ApproximatesLinearOn.antilipschitz`)
  ⇒ same c for every F_t.
* ‖DF_t − DF_{t'}‖, |F_t − F_{t'}| ≤ modulus(|t − t'|) on cl R' (uniform continuity of DF).
* uniform gap ρ: cthickening 3ρ (μ_i(R0)) ⊆ μ_i(R'') (quantitative open mapping).
* cutoff χ_i = 1_{thickening ρ T_i} ⋆ φ_ρ with fixed bump φ_ρ: C^2 bounds uniform in i (C3).

## Components / files
* C1 generalize `comp_two_stable` to f : V → Z, h : Z → Y (finite-dim)        [Sympnet/Smoothing/CompStable.lean]
* C2 mollification in C^k on compacta; preserves sup ‖Dg‖ bounds               [Sympnet/Smoothing/Mollify.lean]
* C3 uniform cutoffs                                                            [Sympnet/Smoothing/Mollify.lean]
* C4 generating-function global map                                             [Sympnet/Smoothing/GenFun.lean]
* C5 inverse continuity: s_n → s in C^{k+1} ⇒ Φ_{s_n} → Φ_s in C^k              [Sympnet/Smoothing/GenFun.lean]
* C6 Goursat: continuous locally exact 1-form on convex open set is exact       [Sympnet/Smoothing/Goursat.lean]
* C7 pair generating function                                                   [Sympnet/Smoothing/PairGenFun.lean]
* C8 Alexander family + uniform constants                                       [Sympnet/Smoothing/Alexander.lean]
* C9 assembly                                                                   [Sympnet/Smoothing/SymplecticApprox.lean]

## Status: COMPLETE

`SympNet.symplecticApprox` is proved (no sorry, axioms: propext, Classical.choice, Quot.sound),
hence `SympNet.G_SympNet_universal_turaev (hH : HornikDensity) (hT : TuraevLiteral)`.

Remaining files: C8 = `Sympnet/Smoothing/Alexander.lean` (antilipschitz lemmas), C9 = `Sympnet/Smoothing/Piece.lean`
(one step, `exists_piece`) + `Sympnet/Smoothing/SymplecticApprox.lean` (inner parallel sets instead of convex
hulls, Alexander family `alex`, assembly).

- C6 DONE: `Sympnet/Smoothing/Goursat.lean` (`exists_primitive_of_locallyExact`).
- C4 DONE: `Sympnet/Smoothing/GenFun.lean` (`GFHyp`, `genMap`, `genMap_psi1`,
  `bijective_genMap`, `contDiff_genMap`, `isSymplecticAt_genMap`).
- C7 core DONE: `Sympnet/Smoothing/PairGenFun.lean` (`PairHyp`, `PairHyp.s`, `gradP_s`, `gradQ_s`,
  `contDiffOn_s`, `psi_mu_of_grad`). Estimates/cutoff application still TODO (part of C9).
- C3 DONE: `Sympnet/Smoothing/Cutoff.lean` (`exists_cutoff`: χ=1 on thickening ρ/4, supp ⊆ thickening 3ρ/4,
  ‖D^jχ‖ ≤ M(ρ), j ≤ 2).
- C1 DONE: `Sympnet/Smoothing/CompStable.lean` (`comp_two_stable'`).
- C2 DONE: `Sympnet/Smoothing/Mollify.lean` (`moll_close`, `fderiv_moll`, `norm_moll_le`).
- C5 DONE: `Sympnet/Smoothing/GenFunCont.lean` (`inv_stable`, `genMap_stable`,
  `exists_smooth_genMap_close`, `GFHyp.of_hess`).

# Blueprint 2: Hornik's theorem (`HornikDensity`)

Goal: τ r-finite, V ∈ C^r(ℝ^m), K compact, ε ⇒ ∃ shallow net N with ‖D^j(V − N)‖ < ε on K, j ≤ r.
Proof route (no polynomials in m variables, no Fourier):
* H1 `Sympnet/Hornik/Net.lean`: nets = span of units x ↦ τ(w·x+b); closed under +, •, translation,
  composition with affine maps; every net is a `shallowNet`.
* H2 `Sympnet/Hornik/FiniteSum.lean`: ∫ g(y) G(y) dy ≈ Σ cᵢ G(yᵢ) with (yᵢ,cᵢ) depending only on a
  modulus δ (finite partition of supp g into sets of diameter < δ).
* H3 `Sympnet/Hornik/OneDim.lean` (LLPS argument, C⁰, ℝ): S = uniform-on-compacts closure of 1D nets.
  ρ = φ ⋆ τ: ρ(cs+b) ∈ S (H2); s^k ρ^{(k)}(cs+b) ∈ S by c-difference quotients; ρ^{(k)} ≢ 0
  (ρ^{(r)} = φ ⋆ τ^{(r)} integrable, nonzero; integrable polynomial = 0); so polynomials ⊆ S;
  Weierstrass ⇒ S = C(ℝ).
* H4 `Sympnet/Hornik/MultiC0.lean`: exponentials e^{w·x} span a point-separating subalgebra
  (Stone–Weierstrass) and each is a uniform limit of nets (H3 ∘ (w·x)) ⇒ nets C⁰-dense in ℝ^m.
* H5 `Sympnet/Hornik/MultiCr.lean`: cutoff Ṽ; φ ⋆ Ṽ ≈ Ṽ (mollify); q ⋆ Ṽ ≈ φ ⋆ Ṽ in C^r when q ≈ φ
  in C⁰ on K − supp Ṽ (derivatives on Ṽ); q ⋆ Ṽ = Ṽ ⋆ q̃ ≈ Σ cᵢ q(· − yᵢ) in C^r (H2, derivatives on q̃).
* H6: `hornikDensity : HornikDensity`, final theorem needs only `TuraevLiteral`.

## Status (Hornik): COMPLETE
`SympNet.hornikDensity : HornikDensity` (files `Sympnet/Hornik/*.lean`), hence
`SympNet.G_SympNet_universal_final (hT : TuraevLiteral)`.

# Blueprint 3: Turaev (weak form) — `TuraevShear`, hence `TuraevHenon` is a theorem

Target `TuraevShear`: ∀ G ∈ SympDiffeo d, K compact, r, ε>0, ∃ Φ ∈ ShearProd d (finite composition
of gradient shears, smooth potentials) with CrClose r K G Φ ε. Shears are Hénon products
(low(∇V) = H[V]∘H0³, up(∇V) = H0³∘H[−V]), so with `symplecticApprox` this gives `TuraevHenon`
and `G_SympNet_universal hornikDensity turaevHenon` (no hypotheses).

Files `Sympnet/Turaev/`:
* `ShearProd.lean`: ShearProd group; linear shears (symmetric f, potential ½⟨fx,x⟩); translations;
  transvection transv φ ℓ z = z + φ'(ℓ z)·(−clmQ ℓ, clmP ℓ) ∈ ShearProd
  (b := clmQ ℓ = 0: lowShear; else low(S)∘up(∇(−φ(b·q)))∘low(−S), S sym, Sb = −a).
* `LinSymp.lean`: every linear symplectic L ∈ ShearProd. (1) ∃t, x ↦ (L(x,0)).1 + t(L(x,0)).2 injective
  (det(A+tC) polynomial, nonzero at t = i since Ax=Cy, Cx=−Ay ⇒ x=y=0 by ω(L(x,0),L(y,0))=0);
  (2) kill C-block by low(−c∘a⁻¹); (3) kill B-block by up(−a⁻¹b); (4) (x,q) ↦ (Mx, M⁻ᵀq) via
  `diagonal_transvection_induction_of_det_ne_zero`, M = S1 S2 (sym) ⇒ R(S1)∘R(−S2⁻¹),
  R(S) = up(S)low(−S⁻¹)up(S) = (p,q) ↦ (Sq, −S⁻¹p); transvection = P·(P T), P swap matrix.
* `Hadamard.lean`: f : ℝ×Y→Z smooth, f(0,·)=0 ⇒ f(h,y) = h•g(h,y), g smooth, g(0,y)=∂ₕf(0,y).
  Compact sup bounds of partial iterated derivatives.
* `Interp.lean`: C⁰-small + C^{r+1}-bounded on cthickening ⇒ C^r-small (Taylor, induction).
* `ProdBound.lean`: Faà di Bruno product bound for Π(id+b_i): ‖D^lΠ‖ ≤ (Π(1+k!c_i))^l.
* `Isotopy.lean`: G(0)=0, Gt(t,x) := Hadamard(G(t•x)), Ginv likewise from G⁻¹; Y = ∂ₜGt,
  X(t,z) = Y(t,Ginv(t,z)); ω(X,·) closed ⇒ H(t,z) = ∫₀¹ ω(X(t,sz),z)ds jointly smooth, D_zH = ω(X,·).
* `Ridge.lean`: Hornik (bump activation, RFinite all orders) on ℝ×X ≅ E(2d+1): ridge sum
  Ñ(t,z)=Σ cⱼ τ(γⱼt+ℓⱼz+bⱼ) C^{r+2}-close to −H on [0,1]×R.
* `Main.lean`: blocks B(h,t,·) = Π_j (id + h vⱼ(t,·)), vⱼ = sgrad of ridge term (transvections);
  B − id − hΣvⱼ = h²·(smooth) (Hadamard twice); exact step Gt(t+h)∘Ginv(t) − id − hX = h²·(smooth);
  Gronwall in C⁰ with Lipschitz of the exact step (net-independent);
  C^{r+1} bound of the product uniform in N (block sizes h(M_X+1+hC)); interpolation ⇒ C^r.
  Order: M_X → ε₀ (interp) → δ → net → N.

## Status (Turaev): COMPLETE
`SympNet.turaevShear`, `SympNet.turaevHenon : TuraevHenon`, and
`SympNet.G_SympNet_universal_unconditional` (no hypotheses) in `Sympnet/Turaev/Main.lean`.
Axioms: propext, Classical.choice, Quot.sound.
