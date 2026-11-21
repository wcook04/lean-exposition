import TorusEuler.Paper.Proofs.S678b.Library.Common
import TorusEuler.Maximality
import TorusEuler.TerminalIntegrals
import TorusEuler.InductiveActivationClock

/-! # Proof of Corollary 8.3 (no cited numbered result; setting 7.1, 8.1, 8.2) -/

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace TorusEuler.Paper

open MovingWaveVector (frame entry)
open Lib.S678b

/-- Proof of **Corollary 8.3** (`cc:uf:terminal:time`), following
sections/09b_terminal_properties.tex:73-84. The ledger lists no cited numbered result; the
setting predicates of Theorem 7.1, Proposition 8.1 and Proposition 8.2 are hypotheses of the
statement itself.

* `T_* = T_∞` (09b:74-78). `u` admits no smooth continuation past `T_∞`: smoothness on a
  compact interval would bound `curl u(t,0)`, contrary to `|curl u(t,0)| → ∞`
  (`h82.central_curl`); this is `IsEulerSolution.isMaximal_of_tendsto_curl_atTop` applied to
  `h81.euler`. Every maximal solution from `u(0)` has `T_* ≥ T_∞` and agrees with `u`
  (`h81.maximal_agreement`); if `T_* > T_∞` it would continue `u`, so `T_* = T_∞`.
* `T_∞ ∈ (0,∞)` (09b:78) from `h71.lifetime`.
* Curl integral in (1.2) (09b:79-81). Documented deviation (DESIGN §7, ledger `exports` of
  8.2): the periodic Beale–Kato–Majda criterion is not formalized; instead the curl lower bound
  (8.2) of the proof of Proposition 8.2, exported as `h82.curl_lower`, is integrated over the
  crossing intervals `[t_j, t_{j+1}]`, whose normalized lengths are bounded below by the
  crossing selected in item 3 of the proof of Theorem 7.1 (sections/08b_induction.tex:330-349:
  normalized time at least `τ_m ≥ 2/ε > 1`; `c.centralWaves.crossing`, `crossing_time`, the data
  carried by the construction), with the values (7.3) of `h71.T4_late_values`
  (`curlIntegral_eq_top_of_inductive_physical_crossings`, content of 8.3).
* Gradient integral in (1.2) (09b:82-83): `‖curl u‖_∞ ≤ C‖∇u‖_∞`
  (`gradientIntegral_eq_top_of_curlIntegral_eq_top`). -/
theorem Proof.corollary_8_3 : Statement.corollary_8_3 := by
  intro P c C T u p h71 h81 h82
  have hmax : IsMaximalEulerSolution T u p :=
    h81.euler.isMaximal_of_tendsto_curl_atTop h82.central_curl
  have hcurl : (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤ := by
    obtain ⟨c₁, C₁, hc₁, hev⟩ := h82.curl_lower
    have hC : 0 < C := zero_lt_two.trans_le h71.strength_constant
    have hinit := two_le_frequency_zero P
    have hfreq : Tendsto P.frequency atTop atTop :=
      frequencySchedule_frequency_tendsto_atTop P.exponentParameter P.order P.frequency
        P.exponentParameter_ge (one_lt_two.trans_le hinit) P.frequency_step
    let w := c.centralWaves
    have hS (j : ℕ) : (w.physical j).initialStrength =
        ‖w.amplitude (j + 1) (c.stages.activation (j + 2))‖ *
          ‖w.waveVector (j + 1) (c.stages.activation (j + 2))‖ := by
      rw [MovingWaveVector.PhysicalAmplification.initialStrength, w.preceding_vector,
        w.preceding_amplitude, mul_comm]
    have hN (j : ℕ) : (w.physical j).firstCoupling =
        entry (frame (w.waveVector (j + 1)) (w.amplitude (j + 1)) (c.stages.activation (j + 2)))
          (fderiv ℝ (c.stages.velocity j (c.stages.activation (j + 2))) 0) 0 1 := by
      unfold MovingWaveVector.PhysicalAmplification.firstCoupling
        MovingWaveVector.PhysicalAmplification.basis
      rw [w.preceding_vector, w.preceding_amplitude,
        w.older_gradient j _ (w.physical j).activation]
    apply curlIntegral_eq_top_of_inductive_physical_crossings
      (σ := fun j => (w.physical j).initialStrength) (ν := fun j => (w.physical j).firstCoupling)
      (c := c₁) (B := C₁) hc₁ (inv_pos.mpr hC) hC hfreq (activation_mono h71) (activation_lt h71)
      (fun t ht => (h81.euler.contDiff_velocity_slice ht).of_le (by simp))
    · refine Eventually.of_forall fun j => ?_
      have h := h71.T4_late_values (j + 1) (by omega)
      simp only [hS]
      exact ⟨h.2.2.2.1, h.2.2.2.2⟩
    · refine Eventually.of_forall fun j => ?_
      have h := h71.T4_late_values (j + 1) (by omega)
      simp only [hN]
      exact ⟨h.2.1, h.2.2.1⟩
    · exact Eventually.of_forall fun j =>
        ⟨_, w.window j, w.physical j, w.crossing j, w.crossing_time j, rfl, rfl,
          w.prescribed_ratio j⟩
    · have h2 := (tendsto_add_atTop_nat 2).eventually hev
      filter_upwards [h2] with j hj
      refine ⟨(activation_mono h71) (Nat.zero_le _) |>.trans'
        (by simp [c.stages.activation_zero]), ?_⟩
      intro t ht
      simpa using hj t ht
  refine ⟨hmax, fun T₁ v q hv hv0 => ?_, h71.lifetime.1,
    gradientIntegral_eq_top_of_curlIntegral_eq_top hcurl, hcurl⟩
  obtain ⟨hle, heq⟩ := h81.maximal_agreement T₁ v q hv hv0
  refine le_antisymm ?_ hle
  by_contra hlt
  push Not at hlt
  exact hmax.2 T₁ hlt ⟨v, q, hv.1, fun t ht => heq ht⟩

end TorusEuler.Paper
