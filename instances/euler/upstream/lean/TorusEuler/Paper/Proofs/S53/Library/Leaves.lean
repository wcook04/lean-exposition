import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.S34A.Statements
import TorusEuler.Paper.Proofs.S5a.Library.Relay
import TorusEuler.OscillatoryDerivativeEstimates

/-!
# S53 library: the leaf hypotheses of the copied chain behind Lemma 5.3

The library chain behind (5.20)-(5.22) (`exists_paper_hierarchy_inverse`,
`exists_parent_seed_leadingScaledJetBounds`) reaches the content lemmas of Lemmas 3.1, D.1, D.2, D.3. The copies of the chain in `Paper.Lib.S53` take these results
through the class `Leaves`, discharged in `Proof.lemma_5_3_of` from `h3_1`, `hD_1`, `hD_2`, `hD_3`.
-/

open Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S53

noncomputable section

/-- The weighted derivative recurrence on a slab (the library form of Lemma D.3 for the linear ODE
`x' = A x + f` with weight `g`, (5.18)-(5.23)): for the amplification factor `Φ`, which depends only on the order
`N` and on a bound of `K (r - l) C`, all derivative words of order `≤ N` of the solution are bounded by
`Φ N (K (r - l) C) · K (B + (r - l) H)`. The original `linearODE_wordBounds_Icc` has the explicit factor
`linearODEWordFactor`; Lemma D.3 only provides some factor `Φ`. -/
@[reducible] def OdeWordBoundWith (Φ : ℕ → ℝ → ℝ) : Prop :=
  ∀ {ι P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d : ι → P) (N : ℕ) {A : ℝ → P → E →L[ℝ] E} {f x : ℝ → P → E}
    {g dg : ℝ → ℝ} {S : Set P} {l r K C B H : ℝ},
    l < r → 0 ≤ K → 0 ≤ C → 0 ≤ B → 0 ≤ H →
    ContDiffOn ℝ ∞ (Function.uncurry A) (Icc l r ×ˢ (univ : Set P)) →
    ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ (univ : Set P)) →
    ContDiffOn ℝ ∞ (Function.uncurry x) (Icc l r ×ˢ (univ : Set P)) →
    (∀ p t, t ∈ Icc l r →
      HasDerivWithinAt (fun s => x s p) (A t p (x t p) + f t p) (Icc l r) t) →
    (∀ u ∈ Icc l r, 0 < g u) →
    (∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u) →
    ContinuousOn dg (Icc l r) →
    (∀ p ∈ S, ∀ y : ℝ → E,
      (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u)) →
    (∀ w : List ι, w.length ≤ N → ∀ p ∈ S,
      ‖phaseOperatorWord (fun i _ => d i) w (x l) p‖ / g l ≤ B) →
    (∀ w : List ι, w.length ≤ N → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (fun i _ => d i) w (f u) p‖ / g u ≤ H) →
    (∀ w : List ι, w.length ≤ N → w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (fun i _ => d i) w (A u) p‖ ≤ C) →
    ∀ w : List ι, w.length ≤ N → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (fun i _ => d i) w (x u) p‖ / g u ≤ Φ N (K * (r - l) * C) * (K * (B + (r - l) * H))

/-- Lemma D.3 for the ODE: some monotone nonnegative factor `Φ` satisfies `OdeWordBoundWith`. It is derived
from `hD_3` by `odeWordBound_of_D3` (`Library/OdeFinal.lean`). -/
def OdeWordBound : Prop :=
  ∃ Φ : ℕ → ℝ → ℝ, (∀ {q : ℝ}, 0 ≤ q → ∀ n, 0 ≤ Φ n q) ∧
    (∀ {q r : ℝ}, 0 ≤ q → q ≤ r → ∀ n, Φ n q ≤ Φ n r) ∧ OdeWordBoundWith Φ

/-- The facts of Lemmas 3.1, D.1, D.2, D.3 that the library chain consumes. -/
class Leaves where
  /-- Lemma D.1. -/
  d1 : Statement.lemma_D_1
  /-- Lemma D.2. -/
  d2 : Statement.lemma_D_2
  /-- Lemma 3.1. -/
  t31 : Statement.lemma_3_1
  /-- The amplification factor. -/
  Φ : ℕ → ℝ → ℝ
  Φ_nonneg : ∀ {q : ℝ}, 0 ≤ q → ∀ n, 0 ≤ Φ n q
  Φ_mono : ∀ {q r : ℝ}, 0 ≤ q → q ≤ r → ∀ n, Φ n q ≤ Φ n r
  /-- The weighted derivative recurrence on a slab. -/
  ode : OdeWordBoundWith Φ

/-- The class `Leaves` from `h3_1`, `hD_1` and the weighted derivative recurrence. -/
@[instance_reducible] def leavesOf (h31 : Statement.lemma_3_1) (hD1 : Statement.lemma_D_1)
    (hD2 : Statement.lemma_D_2) (hode : OdeWordBound) : Leaves :=
  { d1 := hD1, d2 := hD2, t31 := h31, Φ := hode.choose, Φ_nonneg := hode.choose_spec.1,
    Φ_mono := hode.choose_spec.2.1, ode := hode.choose_spec.2.2 }

variable [L : Leaves]

/-- The amplification factor of the word recurrence (shadow of `linearODEWordFactor`, whose explicit
recursion is replaced by the factor of Lemma D.3). -/
def linearODEWordFactor (q : ℝ) (n : ℕ) : ℝ := L.Φ n q

/-- Nonnegativity of the weight factor (`linearODEWordFactor_nonneg`). -/
theorem linearODEWordFactor_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : 0 ≤ linearODEWordFactor q n :=
  L.Φ_nonneg hq n

/-- The amplification factor `linearODEWordFactor` is monotone. -/
theorem linearODEWordFactor_mono {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (n : ℕ) :
    linearODEWordFactor q n ≤ linearODEWordFactor r n :=
  L.Φ_mono hq hqr n

/-- The weighted derivative recurrence on a slab (shadow of `linearODE_wordBounds_Icc`): the field `ode`
of `Leaves`. -/
theorem linearODE_wordBounds_Icc : OdeWordBoundWith (L.Φ) := L.ode

/-- The phase primitive of a linear combination of two zero-mean profiles costs no additional word
length (shadow of `hierarchyRelayWordBound_linearPrimitive`, by (D.5) of Lemma D.1 through
`Lib.S5a.relayWordBound_linearPrimitive_of_D1`; the positivity of `ℓ` and `h` is needed by (D.1)). -/
theorem hierarchyRelayWordBound_linearPrimitive {T E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {ℓ h A B V₀ F₀ : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {n : ℕ}
    {a b : T → Vec3 → Vec3 →L[ℝ] E} {V f : T → Vec3 × ℝ → Vec3}
    (ha : ∀ t, ContDiff ℝ ∞ (fun x : Vec3 × ℝ => a t x.1))
    (hb : ∀ t, ContDiff ℝ ∞ (fun x : Vec3 × ℝ => b t x.1))
    (hV : ∀ t, ContDiff ℝ ∞ (V t)) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hVp : ∀ t x, Function.Periodic (fun s => V t (x,s)) 1)
    (hfp : ∀ t x, Function.Periodic (fun s => f t (x,s)) 1)
    (hVz : ∀ t x, phaseMean (fun s => V t (x,s)) = 0)
    (hfz : ∀ t x, phaseMean (fun s => f t (x,s)) = 0)
    (haN : HierarchyRelayWordBound ℓ h n A (fun t x => a t x.1))
    (hbN : HierarchyRelayWordBound ℓ h n B (fun t x => b t x.1))
    (hVN : HierarchyRelayWordBound ℓ h n V₀ V) (hfN : HierarchyRelayWordBound ℓ h n F₀ f) :
    let P (t : T) (x : Vec3 × ℝ) :=
      phasePrimitive (fun s => a t x.1 (V t (x.1,s)) + b t x.1 (f t (x.1,s))) x.2
    (∀ t, ContDiff ℝ ∞ (P t)) ∧
      HierarchyRelayWordBound ℓ h n
        (2 * ((hierarchyAdmissibleWords (Fin 4) n).card *
          ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B * F₀))) P :=
  Lib.S5a.relayWordBound_linearPrimitive_of_D1 L.d1 hℓ hh ha hb hV hf hVp hfp hVz hfz haN hbN hVN hfN

/-- The profile bounds of Lemma 3.1 in the form consumed by the chain: constants `C`, `C_j` independent of
`h`, from `L.t31`. -/
theorem waveProfile_bounds :
    ∃ C : ℝ, 0 < C ∧ (∀ h, 0 < h → h ≤ 1 → ∀ s,
      -C * h ≤ deriv (waveProfile h) s ∧ deriv (waveProfile h) s ≤ 1 ∧ ‖waveProfile h s‖ ≤ C * h) ∧
    ∀ j : ℕ, 2 ≤ j → ∃ Cj : ℝ, 0 < Cj ∧ ∀ h, 0 < h → h ≤ 1 → ∀ s,
      ‖iteratedDeriv j (waveProfile h) s‖ ≤ Cj * h ^ (1 - (j : ℤ)) := by
  obtain ⟨C, hC, h1, h2⟩ := L.t31
  exact ⟨C, hC, fun h hh h₁ s => (h1 h hh h₁).2.2.2.2.2.2.2.2 s, h2⟩

end

end TorusEuler.Paper.Lib.S53
