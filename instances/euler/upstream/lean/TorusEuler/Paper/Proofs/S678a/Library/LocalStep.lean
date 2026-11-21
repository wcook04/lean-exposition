import TorusEuler.Paper.Proofs.S678a.Library.StepLemmas
import TorusEuler.Paper.S678.StepData
import TorusEuler.InductiveStageConstruction

/-! # The local step data and `Theorem71Steps` (package S678a)

`LocalStep` is the clause list of `Theorem71StepData` for one parent stage, child stage and wave;
`steps_of_local` (sections/08b_induction.tex:142-179)
turns the local data of the base and of every selected step into `Theorem71Steps`. -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler HierarchyTwistedProfile

noncomputable section

/-- The clause `approximate` of `Theorem71StepData` (the first three groups of the conclusion of
Lemma 5.8, (5.46)) for a parent `(U, X, pU)` and an expansion `u` at depth `depth`. -/
def ApproxClause {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}
    (d : ParentGeometry hT U X k) (pU : Pressure)
    (S : HierarchyTwistedProfile T k Vec3)
    (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ))
    (depth : ℕ) : Prop :=
  let Y : Velocity := fun r => X r 0
  let V : Velocity := U + graphRead Y (S5.expansion u depth)
  let Pres : Pressure := pU + graphRead Y (S5.expansionPressure u depth)
  let RV : Velocity :=
    graphRead Y (S5.remainder (S5.ops d) u depth + (S + S5.curlCorrection d S))
  (ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
    ∀ r ∈ Icc 0 T, SpatiallyPeriodic (V r) ∧ Function.Odd (V r) ∧
      ∀ x, divergence (V r) x = 0) ∧
  (ContDiffOn ℝ ∞ (Function.uncurry Pres) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
    ∀ r ∈ Icc 0 T, SpatiallyPeriodic (Pres r)) ∧
  ∀ r ∈ Icc 0 T, ∀ x, momentumResidual (Icc 0 T) V Pres r x = RV r x

/-- The data of one step, stated for a parent stage, the child stage and the wave between them,
activated at `t` (the clauses of `Theorem71StepData`). -/
def LocalStep {P : InductiveEulerParameters} {n : ℕ} {tOld t next : ℝ}
    (parent : InductiveEulerStage P n tOld) (child : InductiveEulerStage P (n + 1) t)
    (wave : InductiveEulerWave P n parent child next) (a : ℕ) (ψ : Vec3 → ℝ) : Prop :=
  ∃ (hT : 0 < P.slab (n + 1) t) (k : Vec3) (center : ℝ → Vec3) (amp : ℝ → Vec3 → Vec3)
    (d : ParentGeometry hT parent.velocity parent.flow k)
    (χ : PaperWaveCutoff t (P.slab (n + 1) t))
    (R S : HierarchyTwistedProfile (P.slab (n + 1) t) k Vec3)
    (u : HierarchyProfiles (HierarchyTwistedProfile (P.slab (n + 1) t) k Vec3)
      (HierarchyTwistedProfile (P.slab (n + 1) t) k ℝ)),
    S5.Parent (P.slab (n + 1) t) parent.velocity parent.flow parent.pressure
      (P.frequency n ^ 9) (P.frequency (n + 1)) ∧
    S5.Launch (P.slab (n + 1) t) parent.flow k (P.frequency (n + 1)) t ∧
    S5.Origin (P.slab (n + 1) t) parent.velocity parent.flow k (P.frequency n ^ 9)
      (P.frequency (n + 1)) t center ∧
    (∀ r ∈ Icc t (P.slab (n + 1) t), center r = wave.amplitude r) ∧
    S5.IsSeed parent.velocity parent.flow k t (P.slab (n + 1) t) center amp ∧
    (∀ r ∈ Icc 0 (P.slab (n + 1) t), χ.value r = wave.cutoff r) ∧
    S5.IsExpansion d parent.pressure χ (S5.radius (P.frequency n ^ 9) a)
      (S5.width (P.frequency (n + 1))) amp
      (6 * frequencyExponent P.exponentParameter (P.order (n + 2))) R S u ∧
    ApproxClause d parent.pressure S u
      (6 * frequencyExponent P.exponentParameter (P.order (n + 2))) ∧
    S5.IsTruncation (P.slab (n + 1) t) ψ (P.frequency (n + 1) ^ 5)
      (parent.velocity + graphRead (fun r => parent.flow r 0)
        (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (n + 2)))))
      child.velocity child.pressure ∧
    ∀ r ∈ Icc 0 (P.slab (n + 1) t), wave.oscillation r =
      graphRead (fun r => parent.flow r 0)
        (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (n + 2))) -
          (S5.ops d).average
            (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (n + 2))))) r

/-- If the base and every selected step carry the local data, `Theorem71Steps` holds
(sections/08b_induction.tex:142-179; the indices, slabs, activations, stages and waves of
`Theorem71StepData` are definitionally those of the base and the selected steps). -/
theorem steps_of_local {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)
    (a : ℕ) (ψ : Vec3 → ℝ)
    (hbase : LocalStep c.base.stationary c.base.first c.base.wave a ψ)
    (hstep : ∀ n, LocalStep (c.tip n).parent (c.selectedStep n).child (c.selectedStep n).wave a ψ) :
    Theorem71Steps c a ψ := by
  intro j hj
  match j, hj with
  | 1, _ =>
    obtain ⟨hT, k, center, amp, d, χ, R, S, u, hP, hL, hO, hc, hs, hcut, hexp, happ,
      htr, hosc⟩ := hbase
    exact ⟨hT, k, center, amp, d, χ, R, S, u,
      ⟨hP, hL, hO, hc, hs, hcut, hexp, happ, htr, hosc⟩⟩
  | n + 2, _ =>
    obtain ⟨hT, k, center, amp, d, χ, R, S, u, hP, hL, hO, hc, hs, hcut, hexp, happ,
      htr, hosc⟩ := hstep n
    exact ⟨hT, k, center, amp, d, χ, R, S, u,
      ⟨hP, hL, hO, hc, hs, hcut, hexp, happ, htr, hosc⟩⟩

end

end TorusEuler.Paper.Lib.S678a
