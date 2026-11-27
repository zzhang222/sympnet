/-
  Reducing Lemma 4 (convex U, injective F) to Turaev's theorem *as Turaev states it*.

  Turaev, Nonlinearity 16 (2003) 123–135, abstract: "every symplectic diffeomorphism of ℝ^{2n} can
  be approximated, in the C^∞-topology, on any compact set, by some iteration of some map of the
  form (x,y) ↦ (y+η, −x+∇V(y))", V polynomial. This is `TuraevLiteral` below (we only ask for V
  smooth, which is weaker than polynomial, so Turaev's statement implies ours).

  Getting from Turaev's class (global C^∞ symplectic diffeomorphisms) to the class used in the
  paper's Lemma 4 (C^r symplectic maps, injective on a convex open U) takes two classical steps:
  * `SymplecticSmoothing` (Zehnder 1977, "Note on smoothing symplectic and volume preserving
    diffeomorphisms"): C^r symplectic embeddings are C^r-approximated by C^∞ ones;
  * `SymplecticExtension` (Alexander trick + Hamiltonian cut-off): a C^∞ symplectic embedding of
    a convex open set agrees, near any compact subset, with a global symplectic diffeomorphism.
  `TuraevHenon_of_literal` proves Lemma 4 from these three; `G_SympNet_universal_literal` is the
  resulting main theorem.

  UPDATE: both classical steps are now *proved* (combined into `SymplecticApprox`, see
  `Sympnet/Smoothing/SymplecticApprox.lean`), so `TuraevHenon_of_literal'` and
  `G_SympNet_universal_turaev` there need only Turaev's literal theorem (and Hornik's).
  UPDATE 2: `TuraevLiteral` is not needed either: `Sympnet/Turaev/Main.lean` proves
  `turaevShear` (approximation by finite compositions of shears / Hénon maps rather than by
  iterates of one map) and hence `turaevHenon : TuraevHenon`.
-/
import Sympnet.Counterexample

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace SympNet

variable {d : ℕ}

/-- Smooth symplectic diffeomorphisms of the whole phase space ℝ^{2d}. (Smoothness of the inverse
is automatic by the inverse function theorem, since a symplectic Jacobian is invertible.) -/
def SympDiffeo (d : ℕ) : Set (X d → X d) :=
  {F | ContDiff ℝ ∞ F ∧ Function.Bijective F ∧ ∀ x, IsSymplecticAt F x}

/-- Turaev's map (x, y) ↦ (y + η, −x + ∇V(y)). -/
def turaevMap (η : E d) (V : E d → ℝ) (z : X d) : X d := (z.2 + η, -z.1 + grad V z.2)

/-- **Turaev's theorem**, as stated in his abstract (with "V polynomial" weakened to "V ∈ C^∞").
"Approximated in the C^∞ topology on any compact set" = for every r and ε. -/
def TuraevLiteral : Prop :=
  ∀ (m : ℕ), ∀ F ∈ SympDiffeo m, ∀ K : Set (X m), IsCompact K → ∀ (r : ℕ), ∀ ε > 0,
    ∃ (η : E m) (V : E m → ℝ) (k : ℕ), ContDiff ℝ ∞ V ∧
      CrClose r K F (turaevMap η V)^[k] ε

/-- **Smoothing** (Zehnder 1977): a C^r (r ≥ 1) symplectic map, injective on a convex open set U,
is C^r-approximated on any compact K ⊆ U by a C^∞ symplectic map injective on some convex open
neighbourhood of K. -/
def SymplecticSmoothing : Prop :=
  ∀ (m r : ℕ), 1 ≤ r → ∀ U : Set (X m), IsOpen U → Convex ℝ U →
    ∀ F ∈ SP r U, Set.InjOn F U → ∀ K : Set (X m), IsCompact K → K ⊆ U → ∀ ε > 0,
      ∃ U' : Set (X m), IsOpen U' ∧ Convex ℝ U' ∧ K ⊆ U' ∧
        ∃ F' : X m → X m, ContDiffOn ℝ ∞ F' U' ∧ (∀ x ∈ U', IsSymplecticAt F' x) ∧
          Set.InjOn F' U' ∧ CrClose r K F F' ε

/-- **Extension**: a C^∞ symplectic map injective on a convex open U agrees, on a neighbourhood
of any compact K ⊆ U, with a global smooth symplectic diffeomorphism. -/
def SymplecticExtension : Prop :=
  ∀ (m : ℕ) (U : Set (X m)), IsOpen U → Convex ℝ U →
    ∀ F : X m → X m, ContDiffOn ℝ ∞ F U → (∀ x ∈ U, IsSymplecticAt F x) → Set.InjOn F U →
      ∀ K : Set (X m), IsCompact K → K ⊆ U → ∃ G ∈ SympDiffeo m, F =ᶠ[𝓝ˢ K] G

/-! ### Turaev's iterates are compositions of Hénon maps -/

theorem compList_iterate {α : Type*} (l : List (α → α)) (k : ℕ) :
    (compList l)^[k] = compList (List.replicate k l).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ, ih, List.replicate_succ, List.flatten_cons, compList_append]

/-- Turaev's map is the composition H[0]³ ∘ H[⟨−η,·⟩] ∘ H[V]. -/
theorem turaevMap_eq (η : E d) (V : E d → ℝ) :
    turaevMap η V = compList [henon V, henon (linPot (-η)), henon 0, henon 0, henon 0] := by
  have h := translation_eq_henon (d := d) (-η)
  have e : [henon V, henon (linPot (-η)), henon 0, henon 0, henon 0] =
      [henon V] ++ [henon (linPot (-η)), henon 0, henon 0, henon 0] := rfl
  rw [e, compList_append, ← h]
  funext z
  simp [turaevMap, henon, compList, sub_neg_eq_add]

theorem turaevMap_iterate (η : E d) (V : E d → ℝ) (k : ℕ) :
    (turaevMap η V)^[k] =
      compList ((List.replicate k [V, linPot (-η), 0, 0, 0]).flatten.map henon) := by
  rw [turaevMap_eq, compList_iterate, List.map_flatten, List.map_replicate]
  rfl

/-! ### The reduction -/

theorem CrClose.congr_of_eventuallyEq {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {r : ℕ} {K : Set V} {f g h : V → W} {ε : ℝ}
    (hfg : CrClose r K f g ε) (hgh : g =ᶠ[𝓝ˢ K] h) : CrClose r K f h ε := by
  intro k hk x hx
  rw [← ((hgh.filter_mono (nhds_le_nhdsSet hx)).iteratedFDeriv ℝ k).eq_of_nhds]
  exact hfg k hk x hx

/-- **Lemma 4 (convex U, injective F) from Turaev's literal theorem**, plus smoothing and
extension. -/
theorem TuraevHenon_of_literal (hT : TuraevLiteral) (hS : SymplecticSmoothing)
    (hE : SymplecticExtension) : TuraevHenon := by
  intro m r hr U hU hUc F hF hinj K hK hKU ε hε
  obtain ⟨U', hU', hU'c, hKU', F', hF'smooth, hF'symp, hF'inj, hFF'⟩ :=
    hS m r hr U hU hUc F hF hinj K hK hKU (ε / 2) (half_pos hε)
  obtain ⟨G, hG, hF'G⟩ := hE m U' hU' hU'c F' hF'smooth hF'symp hF'inj K hK hKU'
  obtain ⟨η, V, k, hV, hGT⟩ := hT m G hG K hK r (ε / 2) (half_pos hε)
  refine ⟨(List.replicate k [V, linPot (-η), 0, 0, 0]).flatten, fun W hW => ?_, ?_⟩
  · obtain ⟨l, hl, hWl⟩ := List.mem_flatten.1 hW
    rw [(List.mem_replicate.1 hl).2] at hWl
    have hsm : ContDiff ℝ ∞ W := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hWl
      rcases hWl with rfl | rfl | rfl | rfl | rfl
      exacts [hV, (linPot (-η)).contDiff, contDiff_const, contDiff_const, contDiff_const]
    exact contDiff_infty.1 hsm _
  · have h := (hFF'.congr_of_eventuallyEq hF'G).trans hGT
    rw [add_halves, turaevMap_iterate] at h
    exact h

/-- **Theorem 5 for convex U and injective maps, from the literal cited results**: Hornik et al.
(Lemma 2), Turaev's theorem as he states it, Zehnder's smoothing, and the extension lemma. -/
theorem G_SympNet_universal_literal (hH : HornikDensity) (hT : TuraevLiteral)
    (hS : SymplecticSmoothing) (hE : SymplecticExtension)
    (r : ℕ) (hr : 1 ≤ r) (σ : ℝ → ℝ) (hσ : RFinite r σ)
    (U : Set (X d)) (hU : IsOpen U) (hUc : Convex ℝ U) :
    UDense r U (GSympNet (d := d) σ) {F | F ∈ SP r U ∧ Set.InjOn F U} :=
  G_SympNet_universal hH (TuraevHenon_of_literal hT hS hE) r hr σ hσ U hU hUc

end SympNet
