import TorusEuler.Paper.Proofs.S53.Library.Leaves
import TorusEuler.Paper.SBD.Statements
import TorusEuler.PaperAppendixDLifting

/-!
# S53 library: the jet spaces for Lemma D.3 applied to the linear ODE

For a fixed point `p`, the derivative jets of the solution of `x' = A x + f` in constant spatial
directions are packaged as symmetric families `List Idx → ℝ → V` (the word is the list of directions).
The spaces `Esub` (solutions), `Fsub` (forcings with initial data), `Asub` (coefficients), the
derivative maps, the operators `L₀`, `T` and the seminorms are the abstract data of
`Statement.lemma_D_3` in this setting; the zero-order seminorms are weighted sup norms on the slab.
-/

open Set

namespace TorusEuler.Paper.Lib.S53

noncomputable section

/-- A slab `[l, r]` with a positive continuous weight `g`. -/
structure Slab where
  l : ℝ
  r : ℝ
  g : ℝ → ℝ
  hlr : l < r
  hg0 : ∀ t ∈ Icc l r, 0 < g t
  hgc : ContinuousOn g (Icc l r)

/-- Permutation-invariant families indexed by words. -/
def IsSymm {Idx X : Type} (u : List Idx → X) : Prop := ∀ {w w' : List Idx}, w.Perm w' → u w = u w'

/-- Auxiliary fact `isSymm_cons` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem isSymm_cons {Idx X : Type} {u : List Idx → X} (hu : IsSymm u) (i : Idx) :
    IsSymm (fun w => u (i :: w)) := fun h => hu (h.cons i)

/-- The Leibniz sum over the splits of a word. -/
def lsum {Idx X : Type} [AddCommMonoid X] : List Idx → (List Idx → List Idx → X) → X
  | [], F => F [] []
  | i :: w, F => lsum w (fun a b => F (i :: a) b) + lsum w (fun a b => F a (i :: b))

/-- Algebraic property `lsum_add` of the Leibniz sum `lsum`. -/
theorem lsum_add {Idx X : Type} [AddCommMonoid X] (w : List Idx) (F G : List Idx → List Idx → X) :
    lsum w (fun a b => F a b + G a b) = lsum w F + lsum w G := by
  induction w generalizing F G with
  | nil => rfl
  | cons i w ih =>
    simp only [lsum]
    rw [ih, ih]
    abel

/-- Algebraic property `lsum_smul` of the Leibniz sum `lsum`. -/
theorem lsum_smul {Idx X : Type} [AddCommGroup X] [Module ℝ X] (w : List Idx) (c : ℝ)
    (F : List Idx → List Idx → X) :
    lsum w (fun a b => c • F a b) = c • lsum w F := by
  induction w generalizing F with
  | nil => rfl
  | cons i w ih => simp only [lsum, ih, smul_add]

/-- Algebraic property `lsum_neg` of the Leibniz sum `lsum`. -/
theorem lsum_neg {Idx X : Type} [AddCommGroup X] (w : List Idx) (F : List Idx → List Idx → X) :
    lsum w (fun a b => - F a b) = - lsum w F := by
  induction w generalizing F with
  | nil => rfl
  | cons i w ih => simp only [lsum, ih, neg_add]

/-- Algebraic property `lsum_congr` of the Leibniz sum `lsum`. -/
theorem lsum_congr {Idx X : Type} [AddCommMonoid X] (w : List Idx) {F G : List Idx → List Idx → X}
    (h : ∀ a b, F a b = G a b) : lsum w F = lsum w G := by
  have : F = G := funext fun a => funext fun b => h a b
  rw [this]

/-- The weighted derivative maps commute (`lsum_comm_swap`), as required by Lemma D.3. -/
theorem lsum_comm_swap {Idx X : Type} [AddCommMonoid X] (w : List Idx) (F : List Idx → List Idx → X) :
    lsum w F = lsum w (fun a b => F a b) := rfl

/-- The sum over splits is the list sum over `hierarchyLeibnizSplits`. -/
theorem lsum_eq_splits {Idx X : Type} [AddCommMonoid X] (w : List Idx) (F : List Idx → List Idx → X) :
    lsum w F = ((hierarchyLeibnizSplits w).map fun p => F p.1 p.2).sum := by
  induction w generalizing F with
  | nil => simp [lsum, hierarchyLeibnizSplits]
  | cons i w ih =>
    simp only [lsum, hierarchyLeibnizSplits, List.map_append, List.sum_append, List.map_map]
    rw [ih, ih]
    rfl

/-- Symmetry of the sum over splits. -/
theorem lsum_perm {Idx X Y Z : Type} [AddCommMonoid Z] (B : X → Y → Z)
    {w w' : List Idx} (h : w.Perm w') :
    ∀ (a : List Idx → X) (u : List Idx → Y), IsSymm a → IsSymm u →
      lsum w (fun v₁ v₂ => B (a v₁) (u v₂)) = lsum w' (fun v₁ v₂ => B (a v₁) (u v₂)) := by
  induction h with
  | nil => intro a u _ _; rfl
  | cons i h ih =>
    intro a u ha hu
    simp only [lsum]
    rw [ih (fun v => a (i :: v)) u (isSymm_cons ha i) hu,
      ih a (fun v => u (i :: v)) ha (isSymm_cons hu i)]
  | swap i j w =>
    intro a u ha hu
    simp only [lsum]
    have h1 : ∀ v, a (i :: j :: v) = a (j :: i :: v) := fun v => ha (List.Perm.swap j i v)
    have h2 : ∀ v, u (i :: j :: v) = u (j :: i :: v) := fun v => hu (List.Perm.swap j i v)
    simp only [h1, h2]
    abel
  | trans _ _ ih₁ ih₂ =>
    intro a u ha hu
    exact (ih₁ a u ha hu).trans (ih₂ a u ha hu)

end

end TorusEuler.Paper.Lib.S53
