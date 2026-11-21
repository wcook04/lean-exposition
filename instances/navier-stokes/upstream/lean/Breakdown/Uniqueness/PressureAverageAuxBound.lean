import Breakdown.Uniqueness.PressureMollifyAux
import Breakdown.Uniqueness.LocalEnergyAuxTime

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.Internal

theorem exists_energy_bound {T : ℝ} {v : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (hv : IsSolutionOn T v q) (hE : EnergyBoundedOn T v) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc 0 T, Continuous (v t) ∧
      Integrable (fun x => ‖v t x‖ ^ 2) ∧ ∫ x, ‖v t x‖ ^ 2 ≤ A := by
  obtain ⟨A, hA⟩ := hE
  refine ⟨max A 0, le_max_right _ _, fun t ht => ?_⟩
  have hc : Continuous (v t) := (CutoffEnergy.contDiff_slice hv.smooth_velocity ht).continuous
  have hi : Integrable (fun x => ‖v t x‖ ^ 2) := PressureMollify.integrable_norm_sq hc (hA t ht)
  refine ⟨hc, hi, ?_⟩
  have h1 : ENNReal.ofReal (∫ x, ‖v t x‖ ^ 2) ≤ ENNReal.ofReal A := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => sq_nonneg _)]
    exact hA t ht
  rcases le_total A 0 with h | h
  · rw [ENNReal.ofReal_eq_zero.2 h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
    exact h1.trans (le_max_right _ _)
  · exact ((ENNReal.ofReal_le_ofReal_iff h).1 h1).trans (le_max_left _ _)

theorem exists_volume_closedBall_eq : ∃ V : ℝ, 0 ≤ V ∧ ∀ r : ℝ, 0 ≤ r →
    volume.real (closedBall (0 : Space) r) = V * r ^ 3 := by
  refine ⟨volume.real (ball (0 : Space) 1), measureReal_nonneg, fun r hr => ?_⟩
  rw [Measure.addHaar_real_closedBall volume 0 hr, finrank_euclideanSpace, Fintype.card_fin]
  ring

theorem abs_integral_inner_le_of_support {w Φ : Space → Space} (hw : Continuous w)
    (hwi : Integrable (fun x => ‖w x‖ ^ 2)) (hΦ : Continuous Φ) {M r ε : ℝ}
    (hM : ∀ x, ‖Φ x‖ ≤ M) (hs : ∀ x, r < ‖x‖ → Φ x = 0) (hε : 0 < ε) :
    |∫ x, inner ℝ (w x) (Φ x)| ≤
      ε * (∫ x, ‖w x‖ ^ 2) + ε⁻¹ * (M ^ 2 * volume.real (closedBall (0 : Space) r)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hε' : 0 < ε⁻¹ := inv_pos.2 hε
  have hind : Integrable ((closedBall (0 : Space) r).indicator (fun _ => M ^ 2)) :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  set g : Space → ℝ := fun x =>
    ε * ‖w x‖ ^ 2 + ε⁻¹ * (closedBall (0 : Space) r).indicator (fun _ => M ^ 2) x with hg
  have hgi : Integrable g := (hwi.const_mul ε).add (hind.const_mul ε⁻¹)
  have hpt : ∀ x, ‖inner ℝ (w x) (Φ x)‖ ≤ g x := by
    intro x
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ closedBall (0 : Space) r
    · simp only [hg, indicator_of_mem hx]
      have h1 := abs_real_inner_le_norm (w x) (Φ x)
      have h2 := hM x
      have ha := norm_nonneg (w x)
      have hb := norm_nonneg (Φ x)
      have e : ε⁻¹ * (ε * ‖w x‖ - ‖Φ x‖) ^ 2 =
          ε * ‖w x‖ ^ 2 - 2 * (‖w x‖ * ‖Φ x‖) + ε⁻¹ * ‖Φ x‖ ^ 2 := by
        field_simp
        ring
      have hb2 : ε⁻¹ * ‖Φ x‖ ^ 2 ≤ ε⁻¹ * M ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb h2 2) hε'.le
      nlinarith [mul_nonneg hε'.le (sq_nonneg (ε * ‖w x‖ - ‖Φ x‖)), mul_nonneg ha hb]
    · have hx' : r < ‖x‖ := by simpa [mem_closedBall, dist_zero_right, not_le] using hx
      rw [hs x hx', inner_zero_right, abs_zero]
      simp only [hg, indicator_of_notMem hx, mul_zero, add_zero]
      positivity
  calc |∫ x, inner ℝ (w x) (Φ x)| = ‖∫ x, inner ℝ (w x) (Φ x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, g x := norm_integral_le_of_norm_le hgi (ae_of_all _ hpt)
    _ = _ := by
      simp only [hg]
      rw [integral_add (hwi.const_mul ε) (hind.const_mul ε⁻¹), integral_const_mul,
        integral_const_mul, integral_indicator_const _ measurableSet_closedBall, smul_eq_mul,
        mul_comm (volume.real _)]

private theorem norm_unitVector_eq (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private theorem norm_sumSecondPartialsAt_le (Φ : Space → Space) (x : Space) :
    ‖sumSecondPartialsAt Φ x‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 Φ x‖ := by
  have h : ∀ i : Fin 3, ‖iteratedFDeriv ℝ 2 Φ x ![unitVector i, unitVector i]‖ ≤
      ‖iteratedFDeriv ℝ 2 Φ x‖ := by
    intro i
    have h := (iteratedFDeriv ℝ 2 Φ x).le_opNorm ![unitVector i, unitVector i]
    simpa [Fin.prod_univ_two, norm_unitVector_eq] using h
  calc ‖sumSecondPartialsAt Φ x‖ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ 2 Φ x ![unitVector i, unitVector i]‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖iteratedFDeriv ℝ 2 Φ x‖ := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖iteratedFDeriv ℝ 2 Φ x‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

private theorem continuous_sumSecondPartialsAt_of {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (sumSecondPartialsAt Φ) := by
  have hc := hΦ.continuous_iteratedFDeriv PressureMollify.two_le_infty
  unfold sumSecondPartialsAt
  exact continuous_finsetSum _ fun i _ =>
    (continuous_eval_const _).comp hc

private theorem sumSecondPartialsAt_eq_zero_of {Φ : Space → Space} {r : ℝ}
    (hs : ∀ x, r < ‖x‖ → Φ x = 0) {x : Space} (hx : r < ‖x‖) : sumSecondPartialsAt Φ x = 0 := by
  have hts : tsupport Φ ⊆ closedBall (0 : Space) r := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    exact hy (hs y (not_le.1 h))
  have hxt : x ∉ tsupport Φ := fun h => by
    have := hts h
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have h0 : iteratedFDeriv ℝ 2 Φ x = 0 := by
    by_contra h
    exact hxt (support_iteratedFDeriv_subset 2 h)
  simp [sumSecondPartialsAt, h0]

theorem abs_integral_inner_sumSecondPartialsAt_le {w Φ : Space → Space} (hw : Continuous w)
    (hwi : Integrable (fun x => ‖w x‖ ^ 2)) (hΦ : ContDiff ℝ ∞ Φ) {M r ε : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ 2 Φ x‖ ≤ M) (hs : ∀ x, r < ‖x‖ → Φ x = 0) (hε : 0 < ε) :
    |∫ x, inner ℝ (w x) (sumSecondPartialsAt Φ x)| ≤
      ε * (∫ x, ‖w x‖ ^ 2) + ε⁻¹ * ((3 * M) ^ 2 * volume.real (closedBall (0 : Space) r)) :=
  abs_integral_inner_le_of_support hw hwi (continuous_sumSecondPartialsAt_of hΦ)
    (fun x => (norm_sumSecondPartialsAt_le Φ x).trans (by linarith [hM x]))
    (fun x hx => sumSecondPartialsAt_eq_zero_of hs hx) hε

private theorem abs_integral_sum_stress_le {w : Space → Space}
    (hwi : Integrable (fun x => ‖w x‖ ^ 2)) {a : Fin 3 → Fin 3 → Space → ℝ} {M : ℝ}
    (hM : ∀ i j x, |a i j x| ≤ M) :
    |∫ x, ∑ i, ∑ j, w x i * w x j * a i j x| ≤ 9 * M * ∫ x, ‖w x‖ ^ 2 := by
  have hpt : ∀ x, ‖∑ i, ∑ j, w x i * w x j * a i j x‖ ≤ 9 * M * ‖w x‖ ^ 2 := by
    intro x
    rw [Real.norm_eq_abs]
    have hc : ∀ i j, |w x i * w x j * a i j x| ≤ M * ‖w x‖ ^ 2 := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |w x i| ≤ ‖w x‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (w x) i
      have h2 : |w x j| ≤ ‖w x‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (w x) j
      have h3 := hM i j x
      calc |w x i| * |w x j| * |a i j x| ≤ ‖w x‖ * ‖w x‖ * M := by gcongr
        _ = M * ‖w x‖ ^ 2 := by ring
    calc |∑ i, ∑ j, w x i * w x j * a i j x|
        ≤ ∑ i, |∑ j, w x i * w x j * a i j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |w x i * w x j * a i j x| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, M * ‖w x‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hc i j
      _ = 9 * M * ‖w x‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc |∫ x, ∑ i, ∑ j, w x i * w x j * a i j x|
      = ‖∫ x, ∑ i, ∑ j, w x i * w x j * a i j x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, 9 * M * ‖w x‖ ^ 2 := norm_integral_le_of_norm_le (hwi.const_mul _) (ae_of_all _ hpt)
    _ = 9 * M * ∫ x, ‖w x‖ ^ 2 := integral_const_mul _ _

theorem abs_integral_fderiv_stress_le {w Φ : Space → Space} (hw : Continuous w)
    (hwi : Integrable (fun x => ‖w x‖ ^ 2)) (hΦ : ContDiff ℝ ∞ Φ) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ Φ x‖ ≤ M) :
    |∫ x, ∑ i, ∑ j, w x i * w x j * fderiv ℝ Φ x (unitVector i) j| ≤
      9 * M * ∫ x, ‖w x‖ ^ 2 := by
  refine abs_integral_sum_stress_le hwi (a := fun i j x => fderiv ℝ Φ x (unitVector i) j)
    fun i j x => ?_
  have h1 : |fderiv ℝ Φ x (unitVector i) j| ≤ ‖fderiv ℝ Φ x (unitVector i)‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (fderiv ℝ Φ x (unitVector i)) j
  have h2 := (fderiv ℝ Φ x).le_opNorm (unitVector i)
  rw [norm_unitVector_eq, mul_one] at h2
  exact h1.trans (h2.trans (hM x))

theorem abs_stressPairing_self_le {w : Space → Space} (hw : Continuous w)
    (hwi : Integrable (fun x => ‖w x‖ ^ 2)) {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) {M : ℝ}
    (hM : ∀ i j x, |FundSol.secondPartial θ i j x| ≤ M) :
    |stressPairing w w θ| ≤ 9 * M * ∫ x, ‖w x‖ ^ 2 := by
  unfold stressPairing
  exact abs_integral_sum_stress_le hwi (a := fun i j x => FundSol.secondPartial θ i j x) hM

end Breakdown.Internal
