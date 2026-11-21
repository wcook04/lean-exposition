import TorusEuler.PaperAppendixAInverse
import TorusEuler.PaperMeanPressureCompatibility

/-! Recover the projected formulation from the equation with pressure in Theorem A.1. -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "I" => Icc (0 : ℝ) 1
local notation "S" => endpointHalfHolderSolenoidal
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "V½" => HalfHolder A Vec3

local instance : NormedAddCommGroup S := inferInstance
local instance : NormedSpace ℝ S := inferInstance

/-- A solenoidal displacement in the regularity class of Theorem A.1 is
the time primitive of its velocity, with the specified initial trace. -/
theorem paperA1_displacement_eq_primitive (z v : ℝ → S)
    (hz₀ : z 0 = 0) (hv : ContinuousOn v I)
    (hz : ∀ t ∈ I, HasDerivWithinAt z (v t) I t) :
    EqOn z (endpointPrimitive v) I := by
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  have hc : ContinuousOn z I := fun t ht => (hz t ht).continuousWithinAt
  intro t ht
  have hi : IntervalIntegrable v volume 0 t :=
    (hv.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hh (r : ℝ) (hr : r ∈ Ioo 0 t) : HasDerivAt z (v r) r :=
    (hz r ⟨hr.1.le, hr.2.le.trans ht.2⟩).hasDerivAt (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hc.mono (Icc_subset_Icc_right ht.2)) hh hi
  rw [hz₀, sub_zero] at he
  exact he.symm

/-- The equation with a periodic scalar pressure has exactly the
projected form used in Theorem A.1 for uniqueness. -/
theorem paperA1_solution_of_unprojected_equation
    (K Ω : ℝ → K½) (src G : ℝ → V½) (z v : ℝ → S)
    (c : S) (φ : Pressure) (hz₀ : z 0 = 0) (hz₁ : z 1 = 0)
    (hv : ContinuousOn v I) (hz : ∀ t ∈ I, HasDerivWithinAt z (v t) I t)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (φ t))
    (hgrad : ∀ t ∈ I, ∀ x, HasGradientAt (φ t) (HalfHolder.eval (toUnitTorus x) (G t)) x)
    (heq : ∀ t ∈ I, paperMeanIntegratedMomentum K Ω src v t = (c : V½) + G t) :
    ∃ s : PaperMeanIntegratedSolution 1 K Ω src, s.velocity = v ∧ s.constant = c ∧
      EqOn z (endpointPrimitive s.velocity) I := by
  have hprim := paperA1_displacement_eq_primitive z v hz₀ hv hz
  have hc : endpointStrongSpatialProjection c.val = c :=
    Subtype.ext ((endpointStrongSpatialLeray_fixed_iff c.val).2 c.property)
  have hEnd : endpointPrimitive v 1 = 0 :=
    (hprim ⟨zero_le_one, le_rfl⟩).symm.trans hz₁
  refine ⟨⟨v, c, hv, hEnd, ?_⟩, rfl, rfl, hprim⟩
  intro t ht
  have hgd := hgrad t ht
  let Gt := fun x => HalfHolder.eval (toUnitTorus x) (G t)
  have hGtc : Continuous Gt :=
    ((spatialHolderHalf_zero_iff Gt).mp (spatialHolderHalf_zero_of_halfHolder (G t)).1).1
  have hf : fderiv ℝ (φ t) = (InnerProductSpace.toDual ℝ Vec3) ∘ Gt :=
    funext fun x => (hgd x).hasFDerivAt.fderiv
  have hC1 : ContDiff ℝ 1 (φ t) := contDiff_one_iff_fderiv.mpr
    ⟨fun x => (hgd x).hasFDerivAt.differentiableAt,
      hf.symm ▸ (InnerProductSpace.toDual ℝ Vec3).continuous.comp hGtc⟩
  have hG := paperMean_projection_C1_gradient_zero (G t) (φ t) hC1 (hper t ht)
    (fun x => (hgd x).gradient.symm)
  rw [heq t ht, map_add, hc, hG, add_zero]

end

end TorusEuler
