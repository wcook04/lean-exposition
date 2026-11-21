import TorusEuler.Maximality
import TorusEuler.WaveCurl
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TorusEuler

/-- Curl as a bounded linear function of the velocity gradient. -/
noncomputable def curlOfDerivativeCLM : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 where
  toFun := curlOfDerivative
  map_add' D₁ D₂ := by
    ext i
    fin_cases i <;> simp [curlOfDerivative] <;> ring
  map_smul' c D := curlOfDerivative_smul c D
  cont := continuous_curlOfDerivative

theorem torusLInf_curl_le (v : Vec3 → Vec3) :
    torusLInf (curl v) ≤ ENNReal.ofReal ‖curlOfDerivativeCLM‖ * torusLInf (fderiv ℝ v) := by
  refine eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
    (Eventually.of_forall fun x => ?_)
  have h : ‖curl v x‖ ≤ ‖curlOfDerivativeCLM‖ * ‖fderiv ℝ v x‖ :=
    curlOfDerivativeCLM.le_opNorm (fderiv ℝ v x)
  simpa only [ENNReal.ofReal_mul (norm_nonneg curlOfDerivativeCLM),
    ofReal_norm (curl v x), ofReal_norm (fderiv ℝ v x)] using ENNReal.ofReal_le_ofReal h

/-- The second integral conclusion of Corollary 8.3 follows from curl divergence in time. -/
theorem gradientIntegral_eq_top_of_curlIntegral_eq_top {T : ℝ} {u : Velocity}
    (hcurl : (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤) :
    (∫⁻ t in Ico 0 T, torusLInf (fderiv ℝ (u t))) = ⊤ := by
  by_contra hgrad
  have hbound : (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) ≤
      ∫⁻ t in Ico 0 T, ENNReal.ofReal ‖curlOfDerivativeCLM‖ * torusLInf (fderiv ℝ (u t)) :=
    lintegral_mono fun t => torusLInf_curl_le (u t)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hcurl] at hbound
  exact (not_le_of_gt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hgrad))) hbound

/-- Certify the exact solution used in the terminal bounds. -/
theorem theorem11Witness_of_solution_and_terminal_bounds {T : ℝ} {u : Velocity} {p : Pressure}
    (hu : IsEulerSolution T u p)
    (hodd : ∀ t ∈ Ico 0 T, Function.Odd (u t))
    (hbounded : ∃ C : ℝ, ∀ t ∈ Ico 0 T, torusLInf (u t) ≤ ENNReal.ofReal C)
    (hcentral : Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T) atTop)
    (huLimit : HasOffOriginLimits T u) (hdtLimit : HasOffOriginLimits T (timeDerivative T u))
    (hcurl : (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤) : EulerSingularityWitness (u 0) T u p := by
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hu.time_pos⟩
  exact ⟨hu.contDiff_velocity_slice h0, hu.periodic_velocity 0 h0, hodd 0 h0,
    hu.incompressible 0 h0, hu.isMaximal_of_tendsto_curl_atTop hcentral, rfl, hodd,
    gradientIntegral_eq_top_of_curlIntegral_eq_top hcurl, hcurl, hbounded, hcentral, huLimit, hdtLimit⟩

/-- Assembles Theorem 1.1 from a constructed solution and its terminal bounds. -/
theorem theorem11_of_solution_and_terminal_bounds {T : ℝ} {u : Velocity} {p : Pressure}
    (hu : IsEulerSolution T u p)
    (hodd : ∀ t ∈ Ico 0 T, Function.Odd (u t))
    (hbounded : ∃ C : ℝ, ∀ t ∈ Ico 0 T, torusLInf (u t) ≤ ENNReal.ofReal C)
    (hcentral : Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T) atTop)
    (huLimit : HasOffOriginLimits T u) (hdtLimit : HasOffOriginLimits T (timeDerivative T u))
    (hcurl : (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤) : Theorem11 :=
  ⟨u 0, T, u, p, theorem11Witness_of_solution_and_terminal_bounds hu hodd hbounded
    hcentral huLimit hdtLimit hcurl⟩

/-- The same assembly when the curl integral is deduced via a continuation criterion. -/
theorem theorem11_of_continuation_and_terminal_bounds {T : ℝ} {u : Velocity} {p : Pressure}
    (hu : IsEulerSolution T u p)
    (hodd : ∀ t ∈ Ico 0 T, Function.Odd (u t))
    (hbounded : ∃ C : ℝ, ∀ t ∈ Ico 0 T, torusLInf (u t) ≤ ENNReal.ofReal C)
    (hcentral : Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T) atTop)
    (huLimit : HasOffOriginLimits T u) (hdtLimit : HasOffOriginLimits T (timeDerivative T u))
    (continue_of_finite_curl :
      (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) < ⊤ →
        ∃ S > T, ∃ (v : Velocity) (q : Pressure), IsEulerSolution S v q ∧
          ∀ t ∈ Ico 0 T, v t = u t) : Theorem11 := by
  apply theorem11_of_solution_and_terminal_bounds hu hodd hbounded hcentral huLimit hdtLimit
  by_contra hfinite
  obtain ⟨S, hS, hextend⟩ := continue_of_finite_curl (lt_top_iff_ne_top.2 hfinite)
  exact (hu.isMaximal_of_tendsto_curl_atTop hcentral).2 S hS hextend

end TorusEuler
