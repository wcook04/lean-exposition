import TorusEuler.Paper.Proofs.S678a.Library.StepObjects
import TorusEuler.Paper.Proofs.S678a.Library.StepApprox
import TorusEuler.Paper.Proofs.S678a.Library.StepLemmas

/-! # One step of Theorem 7.1 from the Section 5 statements (package S678a)

Items 4-5 of the proof of Theorem 7.1 (sections/08b_induction.tex:376-461): for the parent
`U = U_{j-1}` and the expansion of Subsection 5.5 at depth `P = 6K_{j+1}` with
`V = U + W^♮`, Lemmas 5.8-5.10 and Proposition 5.11 (the instances `Body58 a b Γ K`, `Body59`,
`Body510`, `Body511`) give the bounds that make `S_{Λ_j}V` the next stage of the construction.
`exists_child_of_section5` is the conversion; the numerical inequalities of the schedule are
hypotheses (they are the entries of the cost table, discharged where the constants are chosen). -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler HierarchyTwistedProfile

noncomputable section

/-- A deformation bound with constant `C` gives the bound with any larger constant `C'`. -/
theorem deformationOn_mono {u : Velocity} {Y : ℝ → Velocity} {T C C' : ℝ}
    (h : ChildFlow.DeformationOn u Y T C) (hC : C ≤ C') : ChildFlow.DeformationOn u Y T C' :=
  ⟨h.flow, h.lattice, fun t ht =>
    let ⟨a, b, c⟩ := h.bounds t ht
    ⟨a, fun x => ⟨(b x).1, (b x).2.trans hC⟩, fun x => ⟨(c x).1, (c x).2.trans hC⟩⟩⟩

/-- `graphRead` commutes with subtraction, pointwise. -/
theorem graphRead_sub_apply {T : ℝ} {k : Vec3} (A : Velocity)
    (f g : HierarchyTwistedProfile T k Vec3) (t : ℝ) (x : Vec3) :
    graphRead A (f - g) t x = graphRead A f t x - graphRead A g t x := rfl

/-- The tail bounds of the cutoff child (output of `tails_of_lemma_B_1`). -/
def TailBounds (ψ : Vec3 → ℝ) (Ct : ℕ → ℝ) : Prop :=
  ∀ {T Λ : ℝ}, 0 < Λ → ∀ {V : Velocity} (s : CutoffChild T Λ ψ V) (M : ℕ),
    (∀ t ∈ Icc 0 T, SpatialHolderHalf M (V t)) →
      ∀ m ≤ M, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (s.velocity t - V t) ∧
        spatialHolderHalfNorm m (s.velocity t - V t) ≤
          Ct M * Λ ^ ((m : ℤ) - M) * spatialHolderHalfNorm M (V t)

end

end TorusEuler.Paper.Lib.S678a
