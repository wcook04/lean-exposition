import TorusEuler.EndpointCoefficientCompatibility
import TorusEuler.EndpointWeakInstantaneous

/-! Assembling fixed-time endpoint recovery and the zero terminal primitive from
the weak product equation of Appendix A. -/

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "timeMeasure" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "X" => endpointHalfHolderSolenoidal
local notation "H" => Lp Vec3 2 unitTorusMeasure
local notation "Y" => endpointSpatialSolenoidal

local instance : NormedAddCommGroup C½ := inferInstance
local instance : NormedAddCommGroup X := inferInstance
local instance : NormedSpace ℝ C½ := inferInstance
local instance : NormedSpace ℝ X := inferInstance

/-- A continuous spatial representative of a joint weak path has the same
time integral as the original path. -/
theorem intervalIntegral_endpointSpatial_of_ae {T : ℝ} (hT : 0 ≤ T)
    (v : EndpointTorusL2 T) {g : ℝ → H} (hg : ContinuousOn g (Icc 0 T))
    (hae : g =ᵐ[timeMeasure T] endpointSpatialSlice v) :
    (∫ t in (0 : ℝ)..T, g t) = endpointTorusTimeIntegral hT v := by
  have hgi : Integrable g (timeMeasure T) := (hg.intervalIntegrable_of_Icc hT).1
  apply ext_inner_right ℝ
  intro y
  calc
    ⟪∫ t in (0 : ℝ)..T, g t, y⟫_ℝ = ∫ t, ⟪g t, y⟫_ℝ ∂timeMeasure T := by
      rw [intervalIntegral.integral_of_le hT, real_inner_comm, ← integral_inner (𝕜 := ℝ) hgi]
      exact integral_congr_ae (ae_of_all _ fun _ => real_inner_comm _ _)
    _ = ∫ t, ⟪endpointSpatialSlice v t, y⟫_ℝ ∂timeMeasure T :=
      integral_congr_ae (hae.mono fun t ht => congrArg (fun x : H => ⟪x, y⟫_ℝ) ht)
    _ = _ := integral_inner_endpointSpatialSlice hT v y

/-- The recovered projected path inherits the zero terminal time integral
from the weak product constraint. -/
theorem endpointRecoveredPrimitive_of_joint {T : ℝ} (hT : 0 ≤ T)
    (v : endpointTorusSpace T) {g : ℝ → X} (hg : ContinuousOn g (Icc 0 T))
    (hae : (fun t => endpointHalfHolderToL2 ((g t : X) : C½))
      =ᵐ[timeMeasure T] endpointSpatialSlice (v : EndpointTorusL2 T)) :
    endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0 ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (endpointPrimitive g) (g t) (Icc 0 T) t := by
  let _ : CompleteSpace X := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  let _ : CompleteSpace Y := isClosed_endpointSpatialSolenoidal.completeSpace_coe
  let P : X →L[ℝ] Y := endpointSolenoidalEmbedding
  have htime : endpointTorusTimeIntegral hT (v : EndpointTorusL2 T) = 0 :=
    (endpointTimeIntegral_eq_zero_iff hT _).mpr
      ((mem_endpointTorusSpace_iff_slices T _).mp v.property).1
  have hmean : (∫ t in (0 : ℝ)..T, P (g t)) = 0 := by
    apply Subtype.ext
    have hc := P.continuous.comp_continuousOn hg
    change endpointSpatialSolenoidal.subtypeL (∫ t in (0 : ℝ)..T, P (g t)) = 0
    calc
      _ = ∫ t in (0 : ℝ)..T, endpointHalfHolderToL2 ((g t : X) : C½) :=
        (endpointSpatialSolenoidal.subtypeL.intervalIntegral_comp_comm
          (hc.intervalIntegrable_of_Icc hT)).symm
      _ = _ := (intervalIntegral_endpointSpatial_of_ae hT _
        ((endpointSpatialSolenoidal.subtypeL.comp P).continuous.comp_continuousOn hg) hae).trans htime
  exact endpointRecoveredPrimitive_hasDerivWithinAt_and_zero_endpoints hT P
    endpointSolenoidalEmbedding_injective hg (ae_eq_refl _) hmean

set_option maxHeartbeats 1000000 in
/-- A product weak solution with a compatible instantaneous right side has a
continuous half-Hölder representative and an endpoint primitive. The assumptions
on the strong fixed-time inverses and the compatible right side are the outputs
of the spatial solve and the mixed-space representation, respectively. -/
theorem exists_endpointTorusContinuousRepresentative {T κ : ℝ} (hT : 0 < T)
    (v : endpointTorusSpace T) (P : C½ →L[ℝ] X)
    (hP : ∀ f, endpointWeakSpatialProjection (endpointHalfHolderToL2 f) =
      endpointSolenoidalEmbedding (P f))
    (K : ℝ → K½)
    (hκ : 0 < κ)
    (helliptic : ∀ t ∈ Icc 0 T, ∀ a (z : Vec3), κ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) z, z⟫_ℝ)
    (S : ℝ → X ≃L[ℝ] X)
    (hS : ∀ t ∈ Icc 0 T, ∀ f : X, S t f = P ((K t).coefficientMul (f : C½)))
    (hInv : ContinuousOn (fun t => ((S t).symm : X →L[ℝ] X)) (Icc 0 T))
    (c : X) {JΩ L : ℝ → C½} {M CJ CL : ℝ}
    (hJ : ContinuousOn JΩ (Icc 0 T)) (hL : ContinuousOn L (Icc 0 T))
    (hM : 0 ≤ M) (hBound : ∀ t ∈ Icc 0 T, ‖((S t).symm : X →L[ℝ] X)‖ ≤ M)
    (hJBound : ∀ t ∈ Icc 0 T, ‖JΩ t‖ ≤ CJ) (hLBound : ∀ t ∈ Icc 0 T, ‖L t‖ ≤ CL)
    (hWeak : ∀ᵐ t ∂timeMeasure T,
      endpointWeakSpatialProjection (endpointWeakCoefficient (K t)
        (endpointSpatialSlice (v : EndpointTorusL2 T) t)) =
        endpointSolenoidalEmbedding (c + P (JΩ t) - P (L t))) :
    ∃ g : ℝ → X, ContinuousOn g (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, S t (g t) = c + P (JΩ t) - P (L t)) ∧
      ((fun t => endpointHalfHolderToL2 ((g t : X) : C½)) =ᵐ[timeMeasure T]
        endpointSpatialSlice (v : EndpointTorusL2 T)) ∧
      (∀ t ∈ Icc 0 T, ‖g t‖ ≤ M * (‖c‖ + ‖P‖ * (CJ + CL))) ∧
      endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0 ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (endpointPrimitive g) (g t) (Icc 0 T) t := by
  classical
  let W (t : ℝ) : Y :=
    if ht : endpointSpatialSlice (v : EndpointTorusL2 T) t ∈ endpointSpatialSolenoidal then
      ⟨_, ht⟩ else 0
  have hW : (fun t => ((W t : Y) : H)) =ᵐ[timeMeasure T] endpointSpatialSlice (v : EndpointTorusL2 T) := by
    filter_upwards [ae_endpointSpatialSlice_solenoidal v.property] with t ht
    simp [W, ht]
  let Sweak (t : ℝ) : Y →L[ℝ] Y :=
    endpointWeakSpatialProjection.comp ((endpointWeakCoefficient (K t)).comp
      endpointSpatialSolenoidal.subtypeL)
  have hcompat (t : ℝ) (ht : t ∈ Icc 0 T) (f : X) :
      Sweak t (endpointSolenoidalEmbedding f) = endpointSolenoidalEmbedding (S t f) := by
    rw [hS t ht f]
    exact endpointCompressedCoefficient_compat (K t) P endpointWeakSpatialProjection hP f
  have hinjective (t : ℝ) (ht : t ∈ Icc 0 T) : Function.Injective (Sweak t) := by
    let e := endpointWeakCoefficientEquiv (K t) hκ (helliptic t ht)
    have h (f : Y) : Sweak t f = e f :=
      (endpointWeakCoefficientEquiv_apply (K t) hκ (helliptic t ht) f).symm
    exact fun _ _ hEq => e.injective ((h _).symm.trans (hEq.trans (h _)))
  have hWweak : ∀ᵐ t ∂timeMeasure T,
      Sweak t (W t) = endpointSolenoidalEmbedding (c + P (JΩ t) - P (L t)) := by
    filter_upwards [hW, hWeak] with t ht he
    change endpointWeakSpatialProjection (endpointWeakCoefficient (K t) ((W t : Y) : H)) = _
    rw [ht]
    exact he
  obtain ⟨g, hg, hEq, hrep, hbound⟩ := exists_endpointContinuousRepresentative
    endpointSolenoidalEmbedding P c hInv hJ hL hM hBound hJBound hLBound hcompat hinjective hWweak
  have hgrepr : (fun t => endpointHalfHolderToL2 ((g t : X) : C½)) =ᵐ[timeMeasure T]
      endpointSpatialSlice (v : EndpointTorusL2 T) := by
    filter_upwards [hrep, hW] with t hr hw
    exact (congrArg Subtype.val hr).trans hw
  exact ⟨g, hg, hEq, hgrepr, hbound, endpointRecoveredPrimitive_of_joint hT.le v hg hgrepr⟩

end

end TorusEuler
