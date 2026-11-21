import Breakdown.Torus.Lattice

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

def IsMildOn (u : ℝ → V) (a b : ℝ) : Prop :=
  ContinuousOn u (Ico a b) ∧
    ∀ t ∈ Ico a b, IntervalIntegrable (fun s => kernel (t - s) (u s) (u s)) volume a t ∧
      u t = heat (t - a) (u a) + ∫ s in a..t, kernel (t - s) (u s) (u s)

def IsMildOnIcc (u : ℝ → V) (a b : ℝ) : Prop :=
  ContinuousOn u (Icc a b) ∧
    ∀ t ∈ Icc a b, IntervalIntegrable (fun s => kernel (t - s) (u s) (u s)) volume a t ∧
      u t = heat (t - a) (u a) + ∫ s in a..t, kernel (t - s) (u s) (u s)

end Breakdown.Periodic
