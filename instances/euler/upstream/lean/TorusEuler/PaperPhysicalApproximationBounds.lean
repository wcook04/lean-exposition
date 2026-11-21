import TorusEuler.PaperPhysicalStepStatements

/-! The physical approximation of Lemmas 5.8–5.10 on one common hierarchy. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

open ChildFlow

noncomputable section

local notation "I(" T ")" => Icc (0 : ℝ) T
local notation "J(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

/-- The physical approximation estimates, all for the same depth and parent graph. -/
structure PaperPhysicalApproximationBounds
    {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
    {k : Vec3} {d : ParentGeometry hT U X k} {depth : ℕ}
    (b : PhysicalApproximationData d p depth)
    (t₀ D freq stepConstant : ℝ) (stepPower : ℕ) (cutoff : ℝ → ℝ) (switchSize : ℝ) (center : ℝ → Vec3)
    (oscCost meanCost : ℕ → ℝ) : Prop where
  properties : PhysicalApproximationProperties b
  oscillation_sup : ∀ t ∈ I(T), ∀ x, ‖b.oscillation t x‖ ≤
    stepConstant * D ^ stepPower * freq ^ (-5 / 4 : ℝ)
  oscillation_holder : ∀ m : ℕ, ∀ t ∈ I(T), SpatialHolderHalf m (b.oscillation t) ∧
    spatialHolderHalfNorm m (b.oscillation t) ≤
      oscCost m * D ^ (stepPower * (m + 2)) * freq ^ ((3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4)
  mean_holder : ∀ m : ℕ, ∀ t ∈ I(T), SpatialHolderHalf m (b.meanCorrection t) ∧
    spatialHolderHalfNorm m (b.meanCorrection t) ≤
      meanCost m * D ^ (stepPower * (m + 2)) * freq ^ (-5 / 2 : ℝ)
  residual_holder : ∀ t ∈ I(T), SpatialHolderHalf 1 (b.residual t) ∧
    spatialHolderHalfNorm 1 (b.residual t) ≤
      (stepConstant * D ^ stepPower) * freq ^ (2 : ℝ) *
        (freq ^ (-2 * (depth : ℝ) / 3) + switchSize)
  pressure_hessian : ∀ t ∈ I(T), ∀ x v,
    ⟪v, fderiv ℝ (gradient (b.pressure t - p t)) x v⟫_ℝ ≤
      ((stepConstant * D ^ stepPower) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2
  central_gradient : ∃ E : ℝ → Vec3 →L[ℝ] Vec3, ∀ t ∈ Icc t₀ T,
    fderiv ℝ (b.velocity t) 0 = fderiv ℝ (U t) 0 +
      cutoff t • InnerProductSpace.rankOne ℝ (center t) (labelWaveVector X 0 0 k t) + E t ∧
    ‖E t‖ ≤ freq ^ (-1 / 3 : ℝ)
  deformation : ∀ v : Velocity,
    ContDiffOn ℝ ∞ (Function.uncurry v) J(T) →
    (∀ t ∈ I(T), SpatiallyPeriodic (v t)) →
    (∀ t ∈ I(T), ∀ x, divergence (v t) x = 0) →
    (∀ t ∈ I(T), PhaseJetBound 2 (freq ^ (-5 / 2 : ℝ)) (v t)) →
    ∃ Y : ℝ → Velocity, DeformationOn (b.velocity + v) Y T
      (stepConstant * D ^ stepPower * freq ^ (1 / 4 : ℝ))

/-- The level constant through order `m + 1` used by the mean graph bound. -/
def paperPhysicalLevelCostThrough (C : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 2), C j

def paperPhysicalOscillationHolderCost (depth : ℕ) (C L : ℕ → ℝ) (m : ℕ) : ℝ :=
  (3 * (m + 1) : ℝ) * oscillatoryGraphJetCost (L (m + 1)) (m + 1) *
    (2 * ((Finset.Icc 1 depth).card : ℝ) * C (m + 1))

def paperPhysicalMeanHolderCost (depth : ℕ) (C L : ℕ → ℝ) (m : ℕ) : ℝ :=
  (3 * (m + 1) : ℝ) * ((3 : ℝ) * (2 : ℝ) ^ (m + 1) * L (m + 1)) ^ (m + 1) *
    (4 : ℝ) ^ (m + 1) * (((Finset.Icc 1 depth).card : ℝ) * paperPhysicalLevelCostThrough C m)

namespace PhysicalApproximationData

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
  {k : Vec3} {d : ParentGeometry hT U X k} {depth : ℕ}

/-- The all-order Hölder estimates on the same actual hierarchy, with the
order-dependent constants fixed by the two input tables. -/
theorem paperLemma58_profileHolder_of_levels (b : PhysicalApproximationData d p depth)
    (hDepth : 1 ≤ depth) (props : PhysicalApproximationProperties b)
    {D freq ell h t₀ : ℝ} {a r stepPower : ℕ} (C L : ℕ → ℝ)
    (hC : ∀ n, 0 ≤ C n) (hL : ∀ n, 1 ≤ L n)
    (hD : 1 ≤ D) (hf : 1 ≤ freq) (hell : 0 < ell) (hh : 0 < h)
    (hLabel : ell⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hGraph : max a 1 + 1 ≤ stepPower) (hLoss : 6 * r ≤ stepPower)
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγmax : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hinactive : ∀ t ∈ I(T), t < t₀ → b.oscillation t = 0)
    (hLevels : ∀ n, ∀ i ∈ Finset.Icc 1 depth, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles depth b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ell h hT ht₀ htT γ hγ hpos) freq (D ^ r) (C n) n i)
    (B : ℝ → Vec3 → Vec3 →L[ℝ] Vec3)
    (hA : ∀ t ∈ I(T), ContDiff ℝ ∞ (X t 0))
    (hB : ∀ t ∈ I(T), ∀ x, B t (X t 0 x) = fderiv ℝ (X t 0) x)
    (hBreg : ∀ t ∈ I(T), ContDiff ℝ ∞ (B t))
    (hCoeff : ∀ n, ∀ t ∈ I(T), ∀ j ≤ n, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j (B t) x‖ ≤ L n * D) :
    (∀ m, ∀ t ∈ I(T), SpatialHolderHalf m (b.oscillation t) ∧
      spatialHolderHalfNorm m (b.oscillation t) ≤ paperPhysicalOscillationHolderCost depth C L m *
        D ^ (stepPower * (m + 2)) * freq ^ ((3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4)) ∧
    ∀ m, ∀ t ∈ I(T), SpatialHolderHalf m (b.meanCorrection t) ∧
      spatialHolderHalfNorm m (b.meanCorrection t) ≤ paperPhysicalMeanHolderCost depth C L m *
        D ^ (stepPower * (m + 2)) * freq ^ (-5 / 2 : ℝ) := by
  constructor
  · intro m
    exact b.paperLemma58_oscillationHolder hDepth hf (hC (m + 1)) hell hh hD (hL (m + 1))
      hLabel hWidth hCarrier hGraph (by omega : 2 * r ≤ stepPower) ht₀ htT γ hγ hpos hγmax
      hinactive (hLevels (m + 1)) B hA hB hBreg (hCoeff (m + 1))
  · intro m
    let Clevel := paperPhysicalLevelCostThrough C m
    have hClevel : 0 ≤ Clevel := Finset.sum_nonneg fun j _ => hC j
    have hCbound (j : ℕ) (hj : j ≤ m) : C (j + 1) ≤ Clevel :=
      Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (by omega))
    have hGraphMean : a + 1 ≤ stepPower := (Nat.succ_le_succ (le_max_left _ _)).trans hGraph
    exact b.meanCorrection_holder_of_actualLevels hDepth props hf (one_le_pow₀ hD) hClevel
      hell hD (hL (m + 1)) hLabel (show D ^ r ≤ 1 * D ^ r by rw [one_mul]) hGraphMean hLoss
      ht₀ htT γ hγ hpos (fun j hj i hi => (hLevels (j + 1) i hi).mono hf (one_le_pow₀ hD) (hCbound j hj))
      B hA hB hBreg (hCoeff (m + 1)) (by simp only [paperPhysicalMeanHolderCost, Clevel, one_pow, mul_one, le_refl])
      m le_rfl

end PhysicalApproximationData

end

end TorusEuler.HierarchyTwistedProfile
