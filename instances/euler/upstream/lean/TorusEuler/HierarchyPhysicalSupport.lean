import TorusEuler.HierarchyPhysicalSolvers
import TorusEuler.HierarchySupportPropagation

/-! Inactive-region support for the canonical physical hierarchy. -/

open Set

namespace TorusEuler.HierarchyTwistedProfile

variable {T τ : ℝ} {k : Vec3} {S : Set Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

/-- The canonical physical solvers preserve support on the inactive region
for any activation time. At zero activation the region consists of the
labels outside the common envelope on the closed slab. -/
theorem physicalConstruct_support_and_tail_on_inactive
    (hT : 0 < T) (hT₁ : T ≤ 1) (hS : IsClosed S)
    (G M : MP) (κ : VP) (mean : MeanCoefficients G M) (osc : TransverseCoefficients M κ)
    {P : ℕ} (hP : 1 ≤ P) (completionSwitch parentResidual : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    (hLeadingV : EqOn leading.V.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hLeadingp : EqOn leading.p.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hSwitch : EqOn completionSwitch.val.val.val 0 (hierarchyInactiveRegion T τ S)) :
    let A := twistedHierarchyOperators hT G M κ
    let u := (physicalSolvers hT hT₁ G M κ mean osc).construct P completionSwitch parentResidual hR leading
    let U := hierarchyInactiveRegion T τ S
    (∀ i, EqOn (u.V i).val.val.val 0 U ∧ EqOn (u.C i).val.val.val 0 U ∧ EqOn (u.p i).val.val.val 0 U) ∧
    (∀ i ∈ Finset.Icc 2 P,
      let H := A.sourceBeforeMean u P completionSwitch i
      let f := -(H - A.average H) - hierarchyAdvectionAtLevel P 1 i (A.meanPhaseProduct u)
      EqOn f.val.val.val 0 U) ∧
    EqOn (A.remainder u P).val.val.val
      (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)).val.val.val U := by
  let solvers := physicalSolvers hT hT₁ G M κ mean osc
  refine construct_support_and_tail_on_inactive hT hS G M κ mean.inverse_independent osc.covector_ne_zero
    solvers hP completionSwitch parentResidual hR leading hLeadingV hLeadingp hSwitch ?_ ?_
  · intro f hf hzero
    let r := solveTransverse hT G M κ osc f hf
    have hz := r.inactive τ S (fun t ht a s hs => hzero (x := (t, a, s)) ⟨⟨ht, mem_univ _⟩, hs⟩)
    constructor
    · rintro ⟨t, a, s⟩ hx
      exact (hz t hx.1.1 a s hx.2).1
    · rintro ⟨t, a, s⟩ hx
      exact (hz t hx.1.1 a s hx.2).2
  · intro v hv
    exact complete_val_val_of_phaseMean_zero hT G κ osc.covector_independent osc.covector_ne_zero v hv

/-- The canonical physical solvers preserve the common label support and
vanish in the oscillatory components through a positive activation time.
On the inactive region their exact tail consists of slow mean products. -/
theorem physicalConstruct_support_and_tail
    (hT : 0 < T) (hT₁ : T ≤ 1) (hτ : 0 < τ) (hS : IsClosed S)
    (G M : MP) (κ : VP) (mean : MeanCoefficients G M) (osc : TransverseCoefficients M κ)
    {P : ℕ} (hP : 1 ≤ P) (completionSwitch parentResidual : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    (hLeadingV : EqOn leading.V.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hLeadingp : EqOn leading.p.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hSwitch : EqOn completionSwitch.val.val.val 0 (hierarchyInactiveRegion T τ S)) :
    let A := twistedHierarchyOperators hT G M κ
    let u := (physicalSolvers hT hT₁ G M κ mean osc).construct P completionSwitch parentResidual hR leading
    let U := hierarchyInactiveThroughActivation T τ S
    (∀ i, EqOn (u.V i).val.val.val 0 U ∧ EqOn (u.C i).val.val.val 0 U ∧ EqOn (u.p i).val.val.val 0 U) ∧
    (∀ i ∈ Finset.Icc 2 P,
      let H := A.sourceBeforeMean u P completionSwitch i
      let f := -(H - A.average H) - hierarchyAdvectionAtLevel P 1 i (A.meanPhaseProduct u)
      EqOn f.val.val.val 0 U) ∧
    EqOn (A.remainder u P).val.val.val
      (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)).val.val.val U := by
  let solvers := physicalSolvers hT hT₁ G M κ mean osc
  refine construct_support_and_tail hT hτ hS G M κ mean.inverse_independent osc.covector_ne_zero
    solvers hP completionSwitch parentResidual hR leading hLeadingV hLeadingp hSwitch ?_ ?_
  · intro f hf hzero
    let r := solveTransverse hT G M κ osc f hf
    have hz := r.inactive τ S (fun t ht a s hs => hzero (x := (t, a, s)) ⟨⟨ht, mem_univ _⟩, hs⟩)
    constructor
    · rintro ⟨t, a, s⟩ hx
      exact (hz t hx.1.1 a s hx.2).1
    · rintro ⟨t, a, s⟩ hx
      exact (hz t hx.1.1 a s hx.2).2
  · intro v hv
    exact complete_val_val_of_phaseMean_zero hT G κ osc.covector_independent osc.covector_ne_zero v hv

end TorusEuler.HierarchyTwistedProfile
