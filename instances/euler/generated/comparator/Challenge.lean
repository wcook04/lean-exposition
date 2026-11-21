import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.UniformSpace.UniformConvergence

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace TorusEuler

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)
abbrev Velocity := ℝ → Vec3 → Vec3
abbrev Pressure := ℝ → Vec3 → ℝ

def latticeVector (n : Fin 3 → ℤ) : Vec3 :=
  WithLp.toLp 2 (fun i => (n i : ℝ))

/-- Period-one functions in the three spatial coordinates descend to the flat torus. -/
def SpatiallyPeriodic {α : Type*} (f : Vec3 → α) : Prop :=
  ∀ (n : Fin 3 → ℤ) (x : Vec3), f (x + latticeVector n) = f x

def centeredCell : Set Vec3 :=
  {x | ∀ i, x i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)}

def offOrigin : Set Vec3 :=
  (range latticeVector)ᶜ

noncomputable def torusLInf {F : Type*} [NormedAddCommGroup F] (f : Vec3 → F) : ℝ≥0∞ :=
  eLpNormEssSup f (volume.restrict centeredCell)

noncomputable def divergence (v : Vec3 → Vec3) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i 1)) i

noncomputable def curlOfDerivative (D : Vec3 →L[ℝ] Vec3) : Vec3 :=
  let D₀ := D (EuclideanSpace.single 0 1)
  let D₁ := D (EuclideanSpace.single 1 1)
  let D₂ := D (EuclideanSpace.single 2 1)
  WithLp.toLp 2 ![D₁ 2 - D₂ 1, D₂ 0 - D₀ 2, D₀ 1 - D₁ 0]

noncomputable def curl (v : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  curlOfDerivative (fderiv ℝ v x)

noncomputable def timeDerivative (T : ℝ) (u : Velocity) (t : ℝ) (x : Vec3) : Vec3 :=
  derivWithin (fun r => u r x) (Ico 0 T) t

/-- Smooth Euler flow on the half-open time slab, with mean-zero pressure.
    Derivatives in time at zero are taken from within the slab. -/
structure IsEulerSolution (T : ℝ) (u : Velocity) (p : Pressure) : Prop where
  time_pos : 0 < T
  smooth_velocity : ContDiffOn ℝ ∞ (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set Vec3))
  smooth_pressure : ContDiffOn ℝ ∞ (Function.uncurry p) (Ico 0 T ×ˢ (univ : Set Vec3))
  periodic_velocity : ∀ t ∈ Ico 0 T, SpatiallyPeriodic (u t)
  periodic_pressure : ∀ t ∈ Ico 0 T, SpatiallyPeriodic (p t)
  mean_zero_pressure : ∀ t ∈ Ico 0 T, (∫ x in centeredCell, p t x) = 0
  momentum : ∀ t ∈ Ico 0 T, ∀ x,
    timeDerivative T u t x + fderiv ℝ (u t) x (u t x) + gradient (p t) x = 0
  incompressible : ∀ t ∈ Ico 0 T, ∀ x, divergence (u t) x = 0

theorem IsEulerSolution.contDiff_velocity_slice {T : ℝ} {u : Velocity} {p : Pressure}
    (h : IsEulerSolution T u p) {t : ℝ} (ht : t ∈ Ico 0 T) : ContDiff ℝ ∞ (u t) := by
  rw [← contDiffOn_univ]
  exact h.smooth_velocity.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩)

theorem IsEulerSolution.hasDerivWithinAt_velocity {T : ℝ} {u : Velocity} {p : Pressure}
    (h : IsEulerSolution T u p) {t : ℝ} (ht : t ∈ Ico 0 T) (x : Vec3) :
    HasDerivWithinAt (fun r => u r x) (timeDerivative T u t x) (Ico 0 T) t := by
  have htraj : ContDiffOn ℝ ∞ (fun r => u r x) (Ico 0 T) :=
    h.smooth_velocity.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun r hr => ⟨hr, mem_univ x⟩)
  exact (htraj.differentiableOn (by simp) t ht).hasDerivWithinAt

theorem isEulerSolution_zero {T : ℝ} (hT : 0 < T) :
    IsEulerSolution T (fun _ _ => 0) (fun _ _ => 0) where
  time_pos := hT
  smooth_velocity := contDiffOn_const
  smooth_pressure := contDiffOn_const
  periodic_velocity := fun _ _ _ _ => rfl
  periodic_pressure := fun _ _ _ _ => rfl
  mean_zero_pressure := by simp
  momentum := by simp [timeDerivative]
  incompressible := by simp [divergence]

theorem terminalTime_neBot {T : ℝ} (hT : 0 < T) : NeBot (𝓝[Ico 0 T] T) := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  rw [closure_Ico hT.ne]
  exact ⟨hT.le, le_rfl⟩

/-- The velocity has no smooth Euler continuation to any longer time interval. -/
def IsMaximalEulerSolution (T : ℝ) (u : Velocity) (p : Pressure) : Prop :=
  IsEulerSolution T u p ∧
    ∀ S > T, ¬ ∃ (v : Velocity) (q : Pressure),
      IsEulerSolution S v q ∧ ∀ t ∈ Ico 0 T, v t = u t

/-- Convergence of the ambient spatial jets on compact subsets of the punctured lift. -/
def HasOffOriginLimits (T : ℝ) (f : Velocity) : Prop :=
  ∀ K : Set Vec3, IsCompact K → K ⊆ offOrigin → ∀ m : ℕ,
    ∃ (U : Set Vec3) (g : Vec3 → Vec3),
      IsOpen U ∧ K ⊆ U ∧ U ⊆ offOrigin ∧ ContDiffOn ℝ m g U ∧
        ∀ j ≤ m, TendstoUniformlyOn
          (fun t => iteratedFDeriv ℝ j (f t)) (iteratedFDeriv ℝ j g) (𝓝[Ico 0 T] T) K

/-- The conclusions of Theorem 1.1 for a given Euler solution and initial datum. -/
def EulerSingularityWitness (u₀ : Vec3 → Vec3) (T : ℝ) (u : Velocity) (p : Pressure) : Prop :=
    ContDiff ℝ ∞ u₀ ∧ SpatiallyPeriodic u₀ ∧ Function.Odd u₀ ∧
    (∀ x, divergence u₀ x = 0) ∧
    IsMaximalEulerSolution T u p ∧
    u 0 = u₀ ∧
    (∀ t ∈ Ico 0 T, Function.Odd (u t)) ∧
    (∫⁻ t in Ico 0 T, torusLInf (fderiv ℝ (u t))) = ⊤ ∧
    (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤ ∧
    (∃ C : ℝ, ∀ t ∈ Ico 0 T, torusLInf (u t) ≤ ENNReal.ofReal C) ∧
    Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T) atTop ∧
    HasOffOriginLimits T u ∧ HasOffOriginLimits T (timeDerivative T u)

/-- The proposition of frozen Theorem 1.1 (label cc:target:unforced). -/
def Theorem11 : Prop :=
  ∃ (u₀ : Vec3 → Vec3) (T : ℝ) (u : Velocity) (p : Pressure), EulerSingularityWitness u₀ T u p

end TorusEuler

open Set

namespace TorusEuler.Paper

def Statement.theorem_1_1 : Prop :=
  ∃ (u₀ : Vec3 → Vec3) (T : ℝ) (u : Velocity) (p : Pressure),
    EulerSingularityWitness u₀ T u p ∧
      ∀ (T' : ℝ) (v : Velocity) (q : Pressure),
        IsMaximalEulerSolution T' v q → v 0 = u₀ → T' = T ∧ EqOn v u (Ico 0 T)

end TorusEuler.Paper

theorem TorusEuler.theorem11 : TorusEuler.Theorem11 := sorry

theorem TorusEuler.Paper.theorem_1_1 : TorusEuler.Paper.Statement.theorem_1_1 := sorry
