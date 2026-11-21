import Breakdown.CertCell.AssemblyRowExpansionLowTransport
import Breakdown.CertCell.AssemblyRowExpansionLowCoupling
import Breakdown.CertCell.AssemblyRemainderRegular
import Breakdown.CertCell.HarmonicProfiles

open scoped ENNReal NNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.RowIdentity

open Breakdown Breakdown.CertCell CellCalculus CellCert CellCert.CellAnalysis
open Instance.Internal.MomentUpper

theorem locallyIntegrable_of_localSquare {X : ℝ → Space → Space}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) (hp : IsTimePeriodic X)
    (hs : ∀ R : ℝ, ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖X σ y‖ ^ 2) < ⊤) :
    LocallyIntegrable (fun z : ℝ × Space => X z.1 z.2) volume := by
  intro x
  set R : ℝ := ‖x.2‖ + 1 with hR
  set S : Set (ℝ × Space) := Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 1 with hS
  set T : Set (ℝ × Space) := Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.closedBall (0 : Space) R with hT
  refine ⟨S, prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) (Metric.ball_mem_nhds _ one_pos), ?_⟩
  refine ⟨hm.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hsub : S ⊆ T := by
    rintro ⟨σ, y⟩ ⟨h1, h2⟩
    refine ⟨Ioo_subset_Ioc_self h1, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Metric.mem_ball, dist_eq_norm] at h2
    calc ‖y‖ = ‖(y - x.2) + x.2‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x.2‖ + ‖x.2‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith
  have hper : Function.Periodic
      (fun σ => ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖X σ y‖ ^ 2)) 1 := fun σ => by
    simp only [hp σ]
  have hΦ : ∫⁻ σ in Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1), ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖X σ y‖ ^ 2) < ⊤ := by
    rw [Cert.Internal.CoerciveBordered.lintegral_Ioc_periodic _ hper]
    exact hs R
  have hm2 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖X z.1 z.2‖ ^ 2)) volume :=
    (hm.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hSf : volume S < ⊤ := ((Metric.isBounded_Ioo _ _).prod Metric.isBounded_ball).measure_lt_top
  calc ∫⁻ z in S, ‖X z.1 z.2‖ₑ ≤ ∫⁻ z in S, (1 + ENNReal.ofReal (‖X z.1 z.2‖ ^ 2)) := by
        refine lintegral_mono fun z => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (X z.1 z.2)])
    _ = volume S + ∫⁻ z in S, ENNReal.ofReal (‖X z.1 z.2‖ ^ 2) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    _ ≤ volume S + ∫⁻ z in T, ENNReal.ofReal (‖X z.1 z.2‖ ^ 2) :=
        add_le_add le_rfl (lintegral_mono_set hsub)
    _ = volume S + ∫⁻ σ in Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1), ∫⁻ y in Metric.closedBall (0 : Space) R,
          ENNReal.ofReal (‖X σ y‖ ^ 2) := by
        rw [hT, Measure.volume_eq_prod]
        rw [setLIntegral_prod (fun z : ℝ × Space => ENNReal.ofReal (‖X z.1 z.2‖ ^ 2))
          (by rw [← Measure.volume_eq_prod]; exact hm2.restrict)]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hSf, hΦ⟩

theorem locallyIntegrable_of_bound {E F' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F']
    [NormedSpace ℝ F'] {f : ℝ × Space → E} {h : ℝ × Space → F'} (hh : LocallyIntegrable h volume)
    (hf : AEStronglyMeasurable f volume) (c : ℝ) (hb : ∀ z, ‖f z‖ ≤ c * ‖h z‖) :
    LocallyIntegrable f volume := by
  refine (hh.smul c).mono hf (Filter.Eventually.of_forall fun z => ?_)
  refine (hb z).trans ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)

theorem norm_trace_le_three (A : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondDerivTrace A‖ ≤ 3 * ‖A‖ := by
  have hu : ∀ j : Fin 3, ‖A (unitVector j) (unitVector j)‖ ≤ ‖A‖ := fun j => by
    have h1 := (A (unitVector j)).le_opNorm (unitVector j)
    have h2 := A.le_opNorm (unitVector j)
    rw [Internal.RemainderRegular.norm_unitVector] at h1 h2
    nlinarith [norm_nonneg (A (unitVector j))]
  calc ‖secondDerivTrace A‖ ≤ ∑ j : Fin 3, ‖A (unitVector j) (unitVector j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖A‖ := Finset.sum_le_sum fun j _ => hu j
    _ = 3 * ‖A‖ := by simp

def traceColumn (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (c : Fin 3) : ℝ → Space → Space :=
  fun σ w => H σ w (frameUnit (pointAngle w) c) (frameUnit (pointAngle w) c)

theorem trace_frame (A : Space →L[ℝ] Space →L[ℝ] Space) (θ : ℝ) :
    secondDerivTrace A = ∑ c : Fin 3, A (frameUnit θ c) (frameUnit θ c) := by
  have h0 : frameUnit θ 0 = Real.cos θ • unitVector 0 + Real.sin θ • unitVector 1 := by
    simp only [frameUnit, radialUnit, Matrix.cons_val_zero, single_smul_unit]
  have h1 : frameUnit θ 1 = (-Real.sin θ) • unitVector 0 + Real.cos θ • unitVector 1 := by
    simp only [frameUnit, angularUnit, Matrix.cons_val_one, Matrix.cons_val_zero, single_smul_unit]
  have h2 : frameUnit θ 2 = unitVector 2 := by
    simp only [frameUnit, axialUnit, unitVector]
    rfl
  have hs := Real.sin_sq_add_cos_sq θ
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp only [secondDerivTrace, Fin.sum_univ_three, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linear_combination (-(A (unitVector 0) (unitVector 0) i + A (unitVector 1) (unitVector 1) i)) * hs

theorem labelVel_traceColumn (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (m : ℕ) (ι : ℤ × ℤ)
    {p : ℝ × ℝ} (hp : 0 < p.1) (a c : Fin 3) :
    labelVel m ι (traceColumn H c) p a = slopeAt m ι H a c c p := by
  have hpt : ∀ τ φ : ℝ, axialRot (-φ) (traceColumn H c (0 + τ) (axialRot φ (planePoint p))) a =
      axialRot (-φ) (H (0 + τ) (axialRot φ (planePoint p)) (axialRot φ (unitVector c))
        (axialRot φ (unitVector c))) a := by
    intro τ φ
    obtain ⟨k, hk⟩ := pointAngle_orbit hp φ
    simp only [traceColumn, hk, frameUnit_sub, CellCalculus.Internal.HarmonicProfiles.rot_unitVector]
  simp only [labelVel, modeVel, slopeAt, labelHess, modeSecondDeriv, modeAverage, hpt]

theorem measurable_traceColumn {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (c : Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Space => traceColumn H c z.1 z.2) volume := by
  have hu : Measurable (fun z : ℝ × Space => frameUnit (pointAngle z.2) c) :=
    (continuous_frameUnit c).measurable.comp (measurable_pointAngle'.comp measurable_snd)
  have hc : Continuous (fun q : (Space →L[ℝ] Space →L[ℝ] Space) × Space => q.1 q.2 q.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  exact hc.comp_aestronglyMeasurable (hH.prodMk hu.aestronglyMeasurable)

theorem norm_traceColumn_le (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (c : Fin 3) (σ : ℝ) (w : Space) :
    ‖traceColumn H c σ w‖ ≤ 1 * ‖H σ w‖ := by
  have hn := norm_frameUnit (pointAngle w) c
  calc ‖traceColumn H c σ w‖ ≤ ‖H σ w (frameUnit (pointAngle w) c)‖ * ‖frameUnit (pointAngle w) c‖ :=
        (H σ w (frameUnit (pointAngle w) c)).le_opNorm _
    _ ≤ ‖H σ w‖ * ‖frameUnit (pointAngle w) c‖ * ‖frameUnit (pointAngle w) c‖ :=
        mul_le_mul_of_nonneg_right ((H σ w).le_opNorm _) (norm_nonneg _)
    _ = 1 * ‖H σ w‖ := by rw [hn]; ring

theorem labelVel_right_plane {k : ℕ} {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP : 0 < P) {m : ℕ}
    (hclass : Bridge.IsModeClass Γ m) {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ} (hW : CoerciveWeak.IsWeakSecondDerivState W HW B)
    {S : Finset (ℤ × ℤ)} (hS : Bridge.IsHarmonicExpansion S W HW) (L : Finset (ℤ × ℤ))
    (hL : ∀ α, α ∈ L ↔ labelHarmonic m α ∈ S) {b : Fin k → ℝ → Space → Space}
    (hbm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => b i z.1 z.2) volume)
    (hbb : ∀ i, ∃ C : ℝ, ∀ σ y, ‖b i σ y‖ ≤ C) (κ : Fin k → ℝ) {F Pg : ℝ → Space → Space}
    (hPg : IsPeriodicPressure Pg) (hF : IsStrongRightSide W b κ v G H g F Pg) (ι : ℤ × ℤ) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → ∀ a : Fin 3, labelVel m ι F p a =
      ((labelTimeFreq P ι : ℂ) * Complex.I + 1 / 2) * velAt m ι v a p
        + (1 / 2 : ℂ) * ((p.1 : ℂ) * gradAt m ι G a 0 p + (p.2 : ℂ) * gradAt m ι G a 2 p)
        - ∑ c : Fin 3, slopeAt m ι H a c c p
        + ∑ α ∈ L, ∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol a j l : ℂ) *
            (curlComp (gradArray m (ι - α) G p) j * labelVel m α W p l
              + labelVel m α (vorticityOf W) p j * velAt m (ι - α) v l p)
        + ∑ i, (κ i : ℂ) * labelVel m ι (b i) p a
        + velAt m ι Pg a p := by
  obtain ⟨lv, lG, lH⟩ := Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have lg := Coercive.FrequencySeminorm.Internal.derivative_locallyIntegrable hv
  have mT : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivTrace (H z.1 z.2)) volume :=
    Internal.RemainderRegular.continuous_secondDerivTrace.comp_aestronglyMeasurable hv.measurable_secondDeriv
  have lT : LocallyIntegrable (fun z : ℝ × Space => secondDerivTrace (H z.1 z.2)) volume :=
    locallyIntegrable_of_bound lH mT 3 fun z => norm_trace_le_three _
  have hB0 : 0 ≤ B := by
    have h := (hW.decay 0 0).1
    rw [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  have hWb : ∀ σ y, ‖W σ y‖ ≤ B := fun σ y =>
    (hW.decay σ y).1.trans (div_le_self hB0 (by linarith [norm_nonneg y]))
  have hDWb : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ B := fun σ y =>
    (hW.decay σ y).2.1.trans (div_le_self hB0 (one_le_pow₀ (by linarith [norm_nonneg y])))
  have cW : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have cDW := Internal.RemainderRegular.continuous_slice_fderiv hW.smooth
  have mG1 := Internal.RemainderRegular.continuous_curlVec.comp_aestronglyMeasurable hv.measurable_gradient
  have mP1 := mG1.prodMk cW.aestronglyMeasurable
  have mC1' := Internal.RemainderRegular.continuous_crossVec.comp_aestronglyMeasurable mP1
  have mC1 : AEStronglyMeasurable (fun z : ℝ × Space => CellCalculus.crossVec (curlVec (G z.1 z.2)) (W z.1 z.2))
      volume := mC1'
  have mG2 := (Internal.RemainderRegular.continuous_curlVec.comp cDW).aestronglyMeasurable (μ := volume)
  have mP2 := mG2.prodMk hv.measurable_velocity
  have mC2' := Internal.RemainderRegular.continuous_crossVec.comp_aestronglyMeasurable mP2
  have mC2 : AEStronglyMeasurable (fun z : ℝ × Space => CellCalculus.crossVec (vorticityOf W z.1 z.2) (v z.1 z.2))
      volume := mC2'
  have lC1 : LocallyIntegrable (fun z : ℝ × Space => CellCalculus.crossVec (curlVec (G z.1 z.2)) (W z.1 z.2)) volume := by
    refine locallyIntegrable_of_bound lG mC1 (27 * 27 * B) fun z => ?_
    calc ‖CellCalculus.crossVec (curlVec (G z.1 z.2)) (W z.1 z.2)‖
        ≤ 27 * (‖curlVec (G z.1 z.2)‖ * ‖W z.1 z.2‖) := Internal.RemainderRegular.norm_crossVec_le _ _
      _ ≤ 27 * ((27 * ‖G z.1 z.2‖) * B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (Internal.RemainderRegular.norm_curlVec_le _) (hWb _ _)
            (norm_nonneg _) (by positivity)) (by norm_num)
      _ = 27 * 27 * B * ‖G z.1 z.2‖ := by ring
  have lC2 : LocallyIntegrable (fun z : ℝ × Space => CellCalculus.crossVec (vorticityOf W z.1 z.2) (v z.1 z.2)) volume := by
    refine locallyIntegrable_of_bound lv mC2 (27 * 27 * B) fun z => ?_
    calc ‖CellCalculus.crossVec (vorticityOf W z.1 z.2) (v z.1 z.2)‖
        ≤ 27 * (‖curlVec (fderiv ℝ (W z.1) z.2)‖ * ‖v z.1 z.2‖) := Internal.RemainderRegular.norm_crossVec_le _ _
      _ ≤ 27 * ((27 * B) * ‖v z.1 z.2‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((Internal.RemainderRegular.norm_curlVec_le _).trans
            (mul_le_mul_of_nonneg_left (hDWb _ _) (by norm_num))) (norm_nonneg _)) (by norm_num)
      _ = 27 * 27 * B * ‖v z.1 z.2‖ := by ring
  have lC : LocallyIntegrable (fun z : ℝ × Space => couplingField W v G z.1 z.2) volume := lC1.add lC2
  have lb : ∀ i, LocallyIntegrable (fun z : ℝ × Space => b i z.1 z.2) volume := by
    intro i
    obtain ⟨C, hC⟩ := hbb i
    refine (locallyIntegrable_const C).mono (hbm i) (Filter.Eventually.of_forall fun z => ?_)
    exact (hC z.1 z.2).trans (le_abs_self C)
  have lK : LocallyIntegrable (fun z : ℝ × Space => ∑ i, κ i • b i z.1 z.2) volume := by
    have h := locallyIntegrable_finsetSum Finset.univ fun i _ => (lb i).smul (κ i)
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.smul_apply]
  have lP : LocallyIntegrable (fun z : ℝ × Space => Pg z.1 z.2) volume :=
    locallyIntegrable_of_localSquare hPg.measurable hPg.periodic hPg.local_square
  have lX : ∀ c, LocallyIntegrable (fun z : ℝ × Space => traceColumn H c z.1 z.2) volume := fun c =>
    locallyIntegrable_of_bound lH (measurable_traceColumn hv.measurable_secondDeriv c) 1
      fun z => norm_traceColumn_le H c z.1 z.2
  set X : Fin 5 → ℝ → Space → Space :=
    ![g, fun σ y => secondDerivTrace (H σ y), couplingField W v G, fun σ y => ∑ i, κ i • b i σ y, Pg] with hXdef
  set cf : Fin 5 → ℝ := ![1, -1, 1, 1, 1] with hcf
  have lXs : ∀ j, LocallyIntegrable (fun z : ℝ × Space => X j z.1 z.2) volume := by
    intro j
    fin_cases j
    · exact lg
    · exact lT
    · exact lC
    · exact lK
    · exact lP
  have x0 : X 0 = g := rfl
  have x1 : X 1 = fun σ y => secondDerivTrace (H σ y) := rfl
  have x2 : X 2 = couplingField W v G := rfl
  have x3 : X 3 = fun σ y => ∑ i, κ i • b i σ y := rfl
  have x4 : X 4 = Pg := rfl
  have c0 : cf 0 = 1 := rfl
  have c1 : cf 1 = -1 := rfl
  have c2 : cf 2 = 1 := rfl
  have c3 : cf 3 = 1 := rfl
  have c4 : cf 4 = 1 := rfl
  have hdec : ∀ᵐ z : ℝ × Space, F z.1 z.2 = ∑ j, cf j • X j z.1 z.2 := by
    filter_upwards [hF] with z hz
    rw [hz, Fin.sum_univ_five, x0, x1, x2, x3, x4, c0, c1, c2, c3, c4]
    simp only [one_smul, neg_one_smul]
    abel
  have hsl := ae_slice_of_ae hdec
  have hXi := ae_all_iff.2 fun j => ae_slice_integrable (lXs j)
  have hbi := ae_all_iff.2 fun i => ae_slice_integrable (lb i)
  have hci := ae_all_iff.2 fun c => ae_slice_integrable (lX c)
  have htr := labelVel_transport_plane hv hP m ι
  have hcp := labelVel_coupling_plane hv hclass hW hS L hL ι
  filter_upwards [hsl, hXi, hbi, hci, htr, hcp] with p h1 h2 h3 h4 h5 h6 hp1 a
  have e1 := labelVel_sum_of_slice Finset.univ cf X (fun j _ => h2 j hp1) (h1 hp1) m ι a
  have eT : labelVel m ι (fun σ y => secondDerivTrace (H σ y)) p a = ∑ c : Fin 3, slopeAt m ι H a c c p := by
    have hpt : ∀ t : ℝ × ℝ, secondDerivTrace (H t.1 (axialRot t.2 (planePoint p)))
        = ∑ c ∈ Finset.univ, (1 : ℝ) • traceColumn H c t.1 (axialRot t.2 (planePoint p)) := by
      intro t
      simp only [one_smul, traceColumn]
      exact trace_frame _ _
    rw [labelVel_sum_of_slice Finset.univ (fun _ => (1 : ℝ)) (fun c => traceColumn H c)
      (fun c _ => h4 c hp1) (Filter.Eventually.of_forall hpt) m ι a]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [labelVel_traceColumn H m ι hp1 a c, Complex.ofReal_one, one_mul]
  have eK : labelVel m ι (fun σ y => ∑ i, κ i • b i σ y) p a = ∑ i, (κ i : ℂ) * labelVel m ι (b i) p a :=
    labelVel_sum_of_slice Finset.univ κ b (fun i _ => h3 i hp1) (Filter.Eventually.of_forall fun t => rfl) m ι a
  rw [e1, Fin.sum_univ_five, x0, x1, x2, x3, x4, c0, c1, c2, c3, c4]
  rw [eT, eK, h5 hp1 a, h6 hp1 a]
  simp only [velAt, Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul]
  ring

end Breakdown.CertCell.Assembly.Internal.RowIdentity
