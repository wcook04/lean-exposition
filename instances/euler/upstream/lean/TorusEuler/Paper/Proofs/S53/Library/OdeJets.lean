import TorusEuler.Paper.Proofs.S53.Library.OdeD3
import TorusEuler.Paper.Proofs.S53.Library.OdeTime
import TorusEuler.HierarchySourceBounds
import TorusEuler.HierarchyProductEstimates

/-!
# S53 library: the jets of the actual solution as elements of the jet spaces
-/

open Set
open scoped ContDiff


namespace TorusEuler.Paper.Lib.S53

noncomputable section

open TorusEuler

/-- The sum over splits only depends on the terms whose word lengths add up to the word length. -/
theorem lsum_congr_len {Idx X : Type} [AddCommMonoid X] (w : List Idx)
    {F G : List Idx → List Idx → X}
    (h : ∀ a b, a.length + b.length = w.length → F a b = G a b) : lsum w F = lsum w G := by
  induction w generalizing F G with
  | nil =>
    simp only [lsum]
    exact h [] [] rfl
  | cons i w ih =>
    simp only [lsum]
    rw [ih (fun a b hab => h (i :: a) b (by simp only [List.length_cons]; omega)),
      ih (fun a b hab => h a (i :: b) (by simp only [List.length_cons]; omega))]

/-- The data of the linear ODE `x' = A x + f` on `[l, r]` at a fixed point `p`. -/
structure OdeData (Idx P E : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] where
  d : Idx → P
  A : ℝ → P → E →L[ℝ] E
  f : ℝ → P → E
  x : ℝ → P → E
  g : ℝ → ℝ
  dg : ℝ → ℝ
  l : ℝ
  r : ℝ
  K : ℝ
  p : P
  hlr : l < r
  hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc l r ×ˢ (univ : Set P))
  hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ (univ : Set P))
  hx : ContDiffOn ℝ ∞ (Function.uncurry x) (Icc l r ×ˢ (univ : Set P))
  hxt : ∀ p t, t ∈ Icc l r →
    HasDerivWithinAt (fun s => x s p) (A t p (x t p) + f t p) (Icc l r) t
  hg0 : ∀ u ∈ Icc l r, 0 < g u
  hg : ∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u
  hdg : ContinuousOn dg (Icc l r)
  hStable : ∀ y : ℝ → E,
    (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
    ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u)

variable {Idx P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace OdeData

variable (D : OdeData Idx P E)

/-- The slab of the data. -/
def slab : Slab where
  l := D.l
  r := D.r
  g := D.g
  hlr := D.hlr
  hg0 := D.hg0
  hgc := fun t ht => (D.hg t ht).continuousWithinAt

/-- The jets `∂^w x(t, p)` of order `≤ n` (zero otherwise and outside the slab). -/
def xj (n : ℕ) : List Idx → ℝ → E := fun w t =>
  if w.length ≤ n ∧ t ∈ Icc D.l D.r then
    phaseOperatorWord (fun i _ => D.d i) w (D.x t) D.p else 0

/-- The jets `∂^w A(t, p)` of order `≤ n` (zero otherwise and outside the slab). -/
def aj (n : ℕ) : List Idx → ℝ → E →L[ℝ] E := fun w t =>
  if w.length ≤ n ∧ t ∈ Icc D.l D.r then
    phaseOperatorWord (fun i _ => D.d i) w (D.A t) D.p else 0

/-- Auxiliary fact `xj_of_mem` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem xj_of_mem {n : ℕ} {w : List Idx} (hw : w.length ≤ n) {t : ℝ} (ht : t ∈ Icc D.l D.r) :
    D.xj n w t = phaseOperatorWord (fun i _ => D.d i) w (D.x t) D.p := by
  simp [xj, hw, ht]

/-- Auxiliary fact `aj_of_mem` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem aj_of_mem {n : ℕ} {w : List Idx} (hw : w.length ≤ n) {t : ℝ} (ht : t ∈ Icc D.l D.r) :
    D.aj n w t = phaseOperatorWord (fun i _ => D.d i) w (D.A t) D.p := by
  simp [aj, hw, ht]

/-- The jets are symmetric under permutations of the derivative words (`xj_symm`). -/
theorem xj_symm (n : ℕ) : IsSymm (D.xj n) := by
  intro w w' h
  funext t
  by_cases ht : t ∈ Icc D.l D.r
  · by_cases hw : w.length ≤ n
    · rw [xj_of_mem D hw ht, xj_of_mem D (h.length_eq ▸ hw) ht]
      exact congrFun (phaseOperatorWord_constantDirections_perm D.d
        (contDiff_slabSlice D.hx ht) h) D.p
    · have : ¬ w'.length ≤ n := h.length_eq ▸ hw
      simp [xj, hw, this]
  · simp [xj, ht]

/-- The jets are symmetric under permutations of the derivative words (`aj_symm`). -/
theorem aj_symm (n : ℕ) : IsSymm (D.aj n) := by
  intro w w' h
  funext t
  by_cases ht : t ∈ Icc D.l D.r
  · by_cases hw : w.length ≤ n
    · rw [aj_of_mem D hw ht, aj_of_mem D (h.length_eq ▸ hw) ht]
      exact congrFun (phaseOperatorWord_constantDirections_perm D.d
        (contDiff_slabSlice D.hA ht) h) D.p
    · have : ¬ w'.length ≤ n := h.length_eq ▸ hw
      simp [aj, hw, this]
  · simp [aj, ht]

end OdeData

end

end TorusEuler.Paper.Lib.S53
