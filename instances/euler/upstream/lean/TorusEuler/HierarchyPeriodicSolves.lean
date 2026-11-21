import TorusEuler.HierarchyConcreteMean
import TorusEuler.HierarchyPeriodicProfiles

/-! The mean and transverse equations in the periodic profile hierarchy. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

namespace HierarchyPeriodicProfile

variable {T : ℝ}

local notation "VP" => HierarchyPeriodicProfile T Vec3
local notation "SP" => HierarchyPeriodicProfile T ℝ
local notation "VPmap" => HierarchyPeriodicProfile T (Vec3 →L[ℝ] Vec3)

set_option maxHeartbeats 1200000 in
/-- The actual transverse output, including its canonical pressure, lies in the
periodic profile space used by the hierarchy. -/
theorem exists_periodicHierarchyTransverseOutput {m : ℝ → Vec3 → Vec3 →L[ℝ] Vec3}
    {k : ℝ → Vec3 → Vec3} (hT : 0 < T) (G M : VPmap) (κ : VP)
    (hm : ContDiffOn ℝ ∞ (Function.uncurry m) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hk : ContDiffOn ℝ ∞ (Function.uncurry k) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hM : ∀ x ∈ hierarchyProfileSlab T, M.val.val x = m x.1 x.2.1)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ.val.val x = k x.1 x.2.1)
    (hκ₀ : ∀ a, k 0 a ≠ 0)
    (hκt : ∀ a t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun r => k r a) (-((m t a).adjoint (k t a))) (Icc 0 T) t)
    (F : VP) (hFMean : profilePhaseAverage hT F = 0) :
    let A := periodicHierarchyOperators hT G M κ
    ∃ o : HierarchyTransverseOutput A,
      A.material o.V + A.phaseGrad o.p = F ∧
      ∀ a s, o.V.val.val (0, a, s) = 0 := by
  intro A
  have hMean : HierarchySmoothProfile.profilePhaseAverage hT F.val = 0 :=
    congrArg (fun u : VP => u.val) hFMean
  obtain ⟨o, hEq, hper, h0⟩ :=
    HierarchySmoothProfile.exists_hierarchyConcreteTransverseOutput hT G.val M.val κ.val
      hm hk hM hκ hκ₀ hκt F.val (fun a t _ => phasePeriodic F t a) hMean
  let v := ofPeriodicSlices o.V fun t ht a => (hper a t ht).1
  let p := ofPeriodicSlices o.p fun t ht a => (hper a t ht).2
  have hmean : A.average v = 0 := by
    apply Subtype.ext
    exact o.average_V
  have htrans (f : VP) : A.phaseAdv v f = 0 := by
    apply Subtype.ext
    exact o.phaseAdv_V f.val
  refine ⟨⟨v, p, hmean, htrans⟩, ?_, h0⟩
  apply Subtype.ext
  exact hEq

set_option maxHeartbeats 1200000 in
/-- The phase-independent smooth mean output and its pressure also lie in the
periodic profile space. -/
theorem exists_periodicHierarchyMeanOutput (hT : 0 < T) (G M : VPmap) (κ F : VP)
    (B : ℝ → Vec3 → Vec3) (q : ℝ → Vec3 → ℝ)
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hq : ContDiffOn ℝ ∞ (Function.uncurry q) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (heq : ∀ (t : ℝ) (a : Vec3) (s : ℝ), t ∈ Icc 0 T →
      derivWithin (fun r => B r a) (Icc 0 T) t + M.val.val (t, a, s) (B t a) +
          (G.val.val (t, a, s)).adjoint (gradient (q t) a) = F.val.val (t, a, s)) :
    let A := periodicHierarchyOperators hT G M κ
    ∃ o : HierarchyMeanOutput A,
      A.material o.B + A.labelGrad o.q = F ∧
      ∀ (t : ℝ) (a : Vec3) (s : ℝ), t ∈ Icc 0 T →
        o.B.val.val (t, a, s) = B t a ∧ o.q.val.val (t, a, s) = q t a := by
  intro A
  obtain ⟨o, hEq, hVal⟩ :=
    HierarchySmoothProfile.exists_hierarchyConcreteMeanOutput hT G.val M.val κ.val F.val B q hB hq heq
  let v := ofPhaseIndependent o.B fun x hx σ =>
    (hVal x.1 x.2.1 σ hx.1).1.trans (hVal x.1 x.2.1 x.2.2 hx.1).1.symm
  let p := ofPhaseIndependent o.q fun x hx σ =>
    (hVal x.1 x.2.1 σ hx.1).2.trans (hVal x.1 x.2.1 x.2.2 hx.1).2.symm
  have hmean : A.average v = v := by
    apply Subtype.ext
    exact o.average_B
  have hphase (f : VP) : A.phaseAdv f v = 0 := by
    apply Subtype.ext
    exact o.phaseAdv_B f.val
  have hp : A.phaseGrad p = 0 := by
    apply Subtype.ext
    exact o.phaseGrad_q
  refine ⟨⟨v, p, hmean, hphase, hp⟩, ?_, hVal⟩
  apply Subtype.ext
  exact hEq

end HierarchyPeriodicProfile

end

end TorusEuler
