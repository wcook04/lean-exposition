import Breakdown.Cert.Nodes
import Breakdown.Cert.CoerciveBordered
import Breakdown.Cert.JointRepresentative
import Breakdown.Cert.PeriodIntegral

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.HeldMapsTo

theorem ofReal_sq_norm_Lp {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : Lp E 2 μ) : ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow,
    ENNReal.ofReal_toReal (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)),
    JointRepresentativeInternal.sq_eLpNorm_two]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem periodLIntegral_curve {F : ℝ → Space → Space} (c : Lp L2R 2 (volume : Measure TimeCircle))
    (hc : ∀ᵐ σ : ℝ, (c (σ : TimeCircle) : Space → Space) =ᵐ[volume] F σ) :
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) = ENNReal.ofReal (‖c‖ ^ 2) := by
  have hmeas : AEMeasurable (fun t : TimeCircle => ENNReal.ofReal (‖c t‖ ^ 2)) volume :=
    ((Lp.aestronglyMeasurable c).norm.aemeasurable.pow_const 2).ennreal_ofReal
  unfold periodLIntegral
  rw [ofReal_sq_norm_Lp c, ← lintegral_Icc_coe _ hmeas]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hc] with σ hσ
  rw [ofReal_sq_norm_Lp (c (σ : TimeCircle))]
  refine lintegral_congr_ae ?_
  filter_upwards [hσ] with y hy
  rw [hy]

theorem contDiff_fderiv_slice {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {V : E → Space → G} {m n : WithTop ℕ∞}
    (hV : ContDiff ℝ m (fun z : E × Space => V z.1 z.2)) (hnm : n + 1 ≤ m) :
    ContDiff ℝ n (fun z : E × Space => fderiv ℝ (V z.1) z.2) :=
  ContDiff.fderiv (f := fun (z : E × Space) (y : Space) => V z.1 y) (g := fun z => z.2)
    (hV.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd hnm

theorem aestronglyMeasurable_defectField {k : ℕ} {P : ℝ} {V : ℝ → Space → Space}
    {Q : ℝ → Space → ℝ} {b : Fin k → ℝ → Space → Space} (lam : Fin k → ℝ)
    (hV : ContDiff ℝ 2 (fun z : ℝ × Space => V z.1 z.2))
    (hQ : ContDiff ℝ 1 (fun z : ℝ × Space => Q z.1 z.2))
    (hb : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => b i z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => defectField P V Q b lam z.1 z.2) volume := by
  have hVc : Continuous (fun z : ℝ × Space => V z.1 z.2) := hV.continuous
  have h1 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (V z.1) z.2) :=
    contDiff_fderiv_slice hV one_add_one_eq_two.le
  have h2 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun y => fderiv ℝ (V z.1) y) z.2) :=
    contDiff_fderiv_slice (V := fun (s : ℝ) y => fderiv ℝ (V s) y) h1 (by rw [zero_add])
  have ht : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fun s => V s z.2) z.1) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (s : ℝ) => V s z.2) (g := fun z => z.1)
      (hV.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst one_add_one_eq_two.le
  have htc : Continuous (fun z : ℝ × Space => deriv (fun s => V s z.2) z.1) :=
    ht.continuous.clm_apply continuous_const
  have hssp : (fun z : ℝ × Space => sumSecondPartialsAt (V z.1) z.2) = fun z =>
      ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (V z.1) y) z.2 (unitVector i) (unitVector i) := by
    funext z
    simp [sumSecondPartialsAt, iteratedFDeriv_two_apply]
  have hsspc : Continuous (fun z : ℝ × Space => sumSecondPartialsAt (V z.1) z.2) := by
    rw [hssp]
    exact continuous_finsetSum _ fun i _ =>
      (h2.continuous.clm_apply continuous_const).clm_apply continuous_const
  have hq : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (Q z.1) z.2) :=
    contDiff_fderiv_slice hQ (by rw [zero_add])
  have hgc : Continuous (fun z : ℝ × Space => gradientAt (Q z.1) z.2) :=
    continuous_finsetSum _ fun i _ => (hq.continuous.clm_apply continuous_const).smul continuous_const
  have hC : Continuous (fun z : ℝ × Space => (1 / P) • deriv (fun s => V s z.2) z.1
      + (1 / 2 : ℝ) • V z.1 z.2 + (1 / 2 : ℝ) • fderiv ℝ (V z.1) z.2 z.2
      - sumSecondPartialsAt (V z.1) z.2 + advectionAt (V z.1) z.2) :=
    ((((htc.const_smul (1 / P)).add (hVc.const_smul (1 / 2 : ℝ))).add
      ((h1.continuous.clm_apply continuous_snd).const_smul (1 / 2 : ℝ))).sub hsspc).add
      (h1.continuous.clm_apply hVc)
  have hS : AEStronglyMeasurable (fun z : ℝ × Space => ∑ i, lam i • b i z.1 z.2) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hb i).const_smul (lam i)
  exact (hC.aestronglyMeasurable.add hS).add hgc.aestronglyMeasurable

theorem defectField_periodic {k : ℕ} {P : ℝ} {V : ℝ → Space → Space} {Q : ℝ → Space → ℝ}
    {b : Fin k → ℝ → Space → Space} (lam : Fin k → ℝ) (hV : IsTimePeriodic V)
    (hQ : IsTimePeriodic Q) (hb : ∀ i, IsTimePeriodic (b i)) :
    IsTimePeriodic (defectField P V Q b lam) := by
  intro σ y
  have e1 : V (σ + 1) = V σ := funext (hV σ)
  have e2 : Q (σ + 1) = Q σ := funext (hQ σ)
  have e3 : deriv (fun s => V s y) (σ + 1) = deriv (fun s => V s y) σ := by
    rw [← deriv_comp_add_const]
    exact congrArg (fun g : ℝ → Space => deriv g σ) (funext fun s => hV s y)
  have e4 : ∀ i, b i (σ + 1) y = b i σ y := fun i => hb i σ y
  simp only [defectField, e1, e2, e3, e4]

theorem periodNorm_eq_of_curve {F : ℝ → Space → Space} (c : Lp L2R 2 (volume : Measure TimeCircle))
    (hc : ∀ᵐ σ : ℝ, (c (σ : TimeCircle) : Space → Space) =ᵐ[volume] F σ) :
    periodNorm F = ‖c‖ := by
  unfold periodNorm
  rw [periodLIntegral_curve c hc, ENNReal.toReal_ofReal (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

theorem curve_neg_sub {F₁ F₂ : ℝ → Space → Space} (c₁ : Lp L2R 2 (volume : Measure TimeCircle))
    (c₂ : Lp L2R 2 (volume : Measure TimeCircle)) (c : Lp L2R 2 (volume : Measure TimeCircle))
    (hc : c = -c₁ - c₂) (h₁ : ∀ᵐ σ : ℝ, (c₁ (σ : TimeCircle) : Space → Space) =ᵐ[volume] F₁ σ)
    (h₂ : ∀ᵐ σ : ℝ, (c₂ (σ : TimeCircle) : Space → Space) =ᵐ[volume] F₂ σ) :
    ∀ᵐ σ : ℝ, (c (σ : TimeCircle) : Space → Space) =ᵐ[volume] fun y => -F₁ σ y - F₂ σ y := by
  have h : ∀ᵐ t : TimeCircle, c t = -c₁ t - c₂ t := by
    rw [hc]
    filter_upwards [Lp.coeFn_sub (-c₁) c₂, Lp.coeFn_neg c₁] with t ht ht'
    rw [ht, Pi.sub_apply, ht', Pi.neg_apply]
  have hs := (ae_coe_iff (fun t => c t = -c₁ t - c₂ t)).1 h
  filter_upwards [hs, h₁, h₂] with σ hσ hσ₁ hσ₂
  rw [hσ]
  filter_upwards [Lp.coeFn_sub (-c₁ (σ : TimeCircle)) (c₂ (σ : TimeCircle)),
    Lp.coeFn_neg (c₁ (σ : TimeCircle)), hσ₁, hσ₂] with y hy hy' hy₁ hy₂
  rw [hy, Pi.sub_apply, hy', Pi.neg_apply, hy₁, hy₂]

theorem neg_sub_periodic {F₁ F₂ : ℝ → Space → Space} (h₁ : IsPeriodicField F₁)
    (h₂ : IsPeriodicField F₂) :
    IsPeriodicField (fun σ y => -F₁ σ y - F₂ σ y) ∧
      periodNorm (fun σ y => -F₁ σ y - F₂ σ y) ≤ periodNorm F₁ + periodNorm F₂ := by
  obtain ⟨c₁, hc₁, -⟩ := exists_curve_of_joint F₁ h₁.1 h₁.2.1 h₁.2.2
  obtain ⟨c₂, hc₂, -⟩ := exists_curve_of_joint F₂ h₂.1 h₂.2.1 h₂.2.2
  have hc := curve_neg_sub c₁ c₂ (-c₁ - c₂) rfl hc₁ hc₂
  refine ⟨⟨h₁.1.neg.sub h₂.1, fun σ y => by simp only [h₁.2.1 σ y, h₂.2.1 σ y], ?_⟩, ?_⟩
  · rw [periodLIntegral_curve _ hc]
    exact ENNReal.ofReal_lt_top
  · rw [periodNorm_eq_of_curve _ hc, periodNorm_eq_of_curve _ hc₁, periodNorm_eq_of_curve _ hc₂]
    calc ‖-c₁ - c₂‖ ≤ ‖-c₁‖ + ‖c₂‖ := norm_sub_le _ _
      _ = ‖c₁‖ + ‖c₂‖ := by rw [norm_neg]

def ballPart (R : ℝ) (F : ℝ → Space → Space) : ℝ → Space → Space :=
  fun σ y => (Metric.closedBall (0 : Space) R).indicator (F σ) y

theorem periodBallNorm_eq (R : ℝ) (F : ℝ → Space → Space) :
    periodBallNorm R F = periodNorm (ballPart R F) := by
  have h : ∀ σ, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖F σ y‖ ^ 2) =
      ∫⁻ y, ENNReal.ofReal (‖ballPart R F σ y‖ ^ 2) := by
    intro σ
    rw [← lintegral_indicator measurableSet_closedBall]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · simp [ballPart, Set.indicator_of_mem hy]
    · simp [ballPart, Set.indicator_of_notMem hy]
  unfold periodBallNorm periodNorm periodBallLIntegral periodLIntegral
  simp only [h]

theorem periodNorm_mono {F G : ℝ → Space → Space}
    (hG : periodLIntegral (fun σ y => ‖G σ y‖ ^ 2) < ⊤) (h : ∀ σ y, ‖F σ y‖ ≤ ‖G σ y‖) :
    periodNorm F ≤ periodNorm G :=
  Real.sqrt_le_sqrt (ENNReal.toReal_mono hG.ne (Internal.CoerciveBordered.periodLIntegral_mono
    fun σ y => pow_le_pow_left₀ (norm_nonneg _) (h σ y) 2))

theorem ballPart_periodic (R : ℝ) {F : ℝ → Space → Space} (h : IsPeriodicField F) :
    IsPeriodicField (ballPart R F) := by
  have e : (fun z : ℝ × Space => ballPart R F z.1 z.2) =
      (Set.univ ×ˢ Metric.closedBall (0 : Space) R).indicator (fun z => F z.1 z.2) := by
    funext z
    by_cases hz : z.2 ∈ Metric.closedBall (0 : Space) R
    · have hz' : z ∈ Set.univ ×ˢ Metric.closedBall (0 : Space) R := ⟨Set.mem_univ _, hz⟩
      simp only [ballPart, Set.indicator_of_mem hz, Set.indicator_of_mem hz']
    · have hz' : z ∉ Set.univ ×ˢ Metric.closedBall (0 : Space) R := fun h => hz h.2
      simp only [ballPart, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
  refine ⟨?_, fun σ y => ?_, ?_⟩
  · rw [e]
    exact h.1.indicator (MeasurableSet.univ.prod measurableSet_closedBall)
  · have hσ : F (σ + 1) = F σ := funext (h.2.1 σ)
    simp only [ballPart, hσ]
  · refine lt_of_le_of_lt (Internal.CoerciveBordered.periodLIntegral_mono fun σ y =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_indicator_le_norm_self (F σ) y) 2) h.2.2

theorem ballPart_neg_sub (R : ℝ) (F₁ F₂ : ℝ → Space → Space) :
    ballPart R (fun σ y => -F₁ σ y - F₂ σ y) = fun σ y => -ballPart R F₁ σ y - ballPart R F₂ σ y := by
  funext σ y
  by_cases hy : y ∈ Metric.closedBall (0 : Space) R
  · simp [ballPart, Set.indicator_of_mem hy]
  · simp [ballPart, Set.indicator_of_notMem hy]

theorem periodBallNorm_neg_sub_le (R : ℝ) {F₁ F₂ : ℝ → Space → Space} (h₁ : IsPeriodicField F₁)
    (h₂ : IsPeriodicField F₂) :
    periodBallNorm R (fun σ y => -F₁ σ y - F₂ σ y) ≤ periodBallNorm R F₁ + periodBallNorm R F₂ := by
  rw [periodBallNorm_eq, periodBallNorm_eq, periodBallNorm_eq, ballPart_neg_sub]
  exact (neg_sub_periodic (ballPart_periodic R h₁) (ballPart_periodic R h₂)).2

theorem periodBallNorm_le_periodNorm (R : ℝ) {F : ℝ → Space → Space} (h : IsPeriodicField F) :
    periodBallNorm R F ≤ periodNorm F := by
  rw [periodBallNorm_eq]
  exact periodNorm_mono h.2.2 fun σ y => norm_indicator_le_norm_self (F σ) y

theorem periodNorm_le_of {F : ℝ → Space → Space} {b : ℝ} (hb : 0 ≤ b)
    (h : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) ≤ ENNReal.ofReal (b ^ 2)) : periodNorm F ≤ b := by
  unfold periodNorm
  calc Real.sqrt (periodLIntegral (fun σ y => ‖F σ y‖ ^ 2)).toReal ≤ Real.sqrt (b ^ 2) :=
        Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal (sq_nonneg b) h)
    _ = b := Real.sqrt_sq hb

theorem periodBallNorm_le_of {R : ℝ} {F : ℝ → Space → Space} {b : ℝ} (hb : 0 ≤ b)
    (h : periodBallLIntegral R (fun σ y => ‖F σ y‖ ^ 2) ≤ ENNReal.ofReal (b ^ 2)) :
    periodBallNorm R F ≤ b := by
  unfold periodBallNorm
  calc Real.sqrt (periodBallLIntegral R (fun σ y => ‖F σ y‖ ^ 2)).toReal ≤ Real.sqrt (b ^ 2) :=
        Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal (sq_nonneg b) h)
    _ = b := Real.sqrt_sq hb

theorem defect_periodicField {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {p : Fin k → ℝ} (hp : p ∈ d.box) :
    IsPeriodicField (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator
      (d.multiplier p)) :=
  ⟨aestronglyMeasurable_defectField (d.multiplier p)
      (hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id)) (hd.pressure_smooth p hp)
      hd.actuator_measurable,
    defectField_periodic (d.multiplier p) (hd.profile_periodic p)
      (hd.pressure_periodic p hp) hd.actuator_periodic,
    lt_of_le_of_lt (hd.defect_l2 p hp) ENNReal.ofReal_lt_top⟩

theorem energyW_nonneg {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) : 0 ≤ energyW w u := by
  unfold energyW
  refine add_nonneg (sq_nonneg _) (integral_nonneg fun t => ?_)
  unfold sliceWeightedGrad
  exact integral_nonneg fun y => mul_nonneg (hw y) (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem sqrt_energy_le_sizeZ {k : ℕ} (w : Space → ℝ) (u : XX) (κ : Fin k → ℝ) :
    Real.sqrt (energyW w u) ≤ sizeZ w u κ :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem vecNorm_le_sizeZ {k : ℕ} {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) (κ : Fin k → ℝ) :
    vecNorm κ ≤ sizeZ w u κ :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_left (energyW_nonneg hw u))

theorem energy_le_sq {k : ℕ} {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) (κ : Fin k → ℝ) {b : ℝ}
    (h : sizeZ w u κ ≤ b) : energyW w u ≤ b ^ 2 := by
  have h0 := energyW_nonneg hw u
  have hk : 0 ≤ ∑ i, κ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs : 0 ≤ energyW w u + ∑ i, κ i ^ 2 := add_nonneg h0 hk
  have h1 : energyW w u + ∑ i, κ i ^ 2 ≤ b ^ 2 := by
    rw [← Real.sq_sqrt hs]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  linarith

theorem borderedInv_spec {k : ℕ} {d : CertificateData k} {p : Fin k → ℝ}
    (h : ∃ T, BorderedInvSpec d p T) : BorderedInvSpec d p (borderedInv d p) := by
  unfold borderedInv
  rw [dif_pos h]
  exact h.choose_spec

theorem bordered_snd {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (f : HH) (κ : Fin k → ℝ) :
    (bordered d p (f, κ)).2 = pinMap d (freeInv (d.period p) f) := by
  simp only [bordered, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst']

theorem size_arith {Z cL cB cP N NB vn dB dBB A ρ cT af r : ℝ}
    (hZ : Z ≤ cL * N + cB * NB + cP * vn) (hN : N ≤ dB + A) (hNB : NB ≤ dBB + A)
    (hcL : 0 ≤ cL) (hcB : 0 ≤ cB) (hsize : cL * dB + cB * dBB + cP * vn ≤ ρ)
    (hT : cL + cB ≤ cT) (hcT : 0 < cT) (hA0 : 0 ≤ A) (hA : A ≤ af * (2 * ρ) * r)
    (hsmall : 2 * cT * af * r < 1) (hρ : 0 ≤ ρ) : Z ≤ 2 * ρ := by
  have h1 := mul_le_mul_of_nonneg_left hN hcL
  have h2 := mul_le_mul_of_nonneg_left hNB hcB
  have h3 : (cL + cB) * A ≤ cT * A := mul_le_mul_of_nonneg_right hT hA0
  have h4 : cT * A ≤ cT * (af * (2 * ρ) * r) := mul_le_mul_of_nonneg_left hA hcT.le
  have h5 : ρ * (2 * cT * af * r) ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsmall.le hρ
  have e : cT * (af * (2 * ρ) * r) = ρ * (2 * cT * af * r) := by ring
  linarith

theorem sup_arith {S c cm E q qm B Bm a v s ρ r : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ cm) (hE0 : 0 ≤ E)
    (hE : E ≤ (2 * ρ) ^ 2) (hq0 : 0 ≤ q) (hq : q ≤ qm) (hB0 : 0 ≤ B) (hB : B ≤ Bm) (ha : 0 ≤ a)
    (hv0 : 0 ≤ v) (hv : v ≤ 2 * ρ) (hs0 : 0 ≤ s) (hs : s ≤ 2 * ρ) (hρ : 0 ≤ ρ)
    (hS : S ^ 2 ≤ c * E + 2 * q * (B + a * v) * s)
    (hsmall : 4 * cm * ρ ^ 2 + 4 * qm * ρ * (Bm + 2 * a * ρ) ≤ r ^ 2) : S ^ 2 ≤ r ^ 2 := by
  have h1 : c * E ≤ cm * (2 * ρ) ^ 2 := mul_le_mul hc hE hE0 (hc0.trans hc)
  have h2 : B + a * v ≤ Bm + a * (2 * ρ) := add_le_add hB (mul_le_mul_of_nonneg_left hv ha)
  have h3 : 2 * q * (B + a * v) ≤ 2 * qm * (Bm + a * (2 * ρ)) :=
    mul_le_mul (by linarith) h2 (add_nonneg hB0 (mul_nonneg ha hv0)) (by linarith)
  have h4 : 2 * q * (B + a * v) * s ≤ 2 * qm * (Bm + a * (2 * ρ)) * (2 * ρ) :=
    mul_le_mul h3 hs hs0 (mul_nonneg (by linarith) (by nlinarith))
  have e1 : cm * (2 * ρ) ^ 2 = 4 * cm * ρ ^ 2 := by ring
  have e2 : 2 * qm * (Bm + a * (2 * ρ)) * (2 * ρ) = 4 * qm * ρ * (Bm + 2 * a * ρ) := by ring
  linarith

theorem step_bounds (h2 : CoerciveBorderedHolds) (h3 : SupBoundHolds) {k : ℕ}
    {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ} (hp : p ∈ d.box) (u : XX)
    (f : HH) (κ : Fin k → ℝ) (D Pf : ℝ → Space → Space) (A : ℝ)
    (hf : f ∈ invariantHH d.symmetries) (hb : bordered d p (f, κ) = heldRight d p u)
    (hDF : IsPeriodicField D) (hPF : IsPeriodicField Pf)
    (hDn : periodNorm D ≤ d.defectBound p) (hDb : periodBallNorm d.ballRadius D ≤ d.defectBallBound p)
    (hprodN : periodNorm Pf ≤ A) (hprodH : ‖productH u u‖ ≤ A) (hA0 : 0 ≤ A)
    (hAle : A ≤ supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound)
    (hdat1 : ∀ φ, IsSpaceTimeTestField φ → inner ℝ (defectH d p) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (D z.1 z.2) (φ z.1 z.2))
    (hdat2 : ‖defectH d p‖ ≤ d.defectBound p)
    (h5 : ∀ φ, IsSpaceTimeTestField φ → inner ℝ (productH u u) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (Pf z.1 z.2) (φ z.1 z.2)) :
    sizeZ d.weightFn (freeInv (d.period p) f) κ ≤ 2 * d.sizeBound ∧
      supGrad (freeInv (d.period p) f) ≤ ENNReal.ofReal d.supBound := by
  have hP := hd.period_pos p hp
  have hw : ∀ y, 0 ≤ d.weightFn y := fun y => hd.weight_pos.le.trans (hd.weightFn_lower y)
  have hsup0 := hd.supBound_pos
  have hρ := hd.sizeBound_nonneg
  have hFP := neg_sub_periodic hDF hPF
  have hFper := hFP.1
  have hFnorm := hFP.2
  have hFball := periodBallNorm_neg_sub_le d.ballRadius hDF hPF
  have hPb := periodBallNorm_le_periodNorm d.ballRadius hPF
  have hb1 : (bordered d p (f, κ)).1 = -(defectH d p) - productH u u := congrArg Prod.fst hb
  have hpair : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, inner ℝ (-D z.1 z.2 - Pf z.1 z.2) (φ z.1 z.2) =
        inner ℝ (bordered d p (f, κ)).1 (testInHH φ) := by
    intro φ hφ
    have i1 := Internal.CoerciveBordered.integrable_inner_of_periodic hDF.1 hDF.2.1 hDF.2.2 (Internal.CoerciveBordered.continuous_test hφ) hφ.2.1
    have i2 := Internal.CoerciveBordered.integrable_inner_of_periodic hPF.1 hPF.2.1 hPF.2.2 (Internal.CoerciveBordered.continuous_test hφ)
      hφ.2.1
    have e : (fun z : ℝ × Space => inner ℝ (-D z.1 z.2 - Pf z.1 z.2) (φ z.1 z.2))
        = fun z => -(inner ℝ (D z.1 z.2) (φ z.1 z.2)
          + inner ℝ (Pf z.1 z.2) (φ z.1 z.2)) := by
      funext z
      rw [inner_sub_left, inner_neg_left]
      ring
    have e2 : inner ℝ (bordered d p (f, κ)).1 (testInHH φ) =
        -(inner ℝ (defectH d p) (testInHH φ)) - inner ℝ (productH u u) (testInHH φ) :=
      (congrArg (fun v : HH => inner ℝ v (testInHH φ)) hb1).trans
        ((inner_sub_left (𝕜 := ℝ) (-(defectH d p)) (productH u u) (testInHH φ)).trans
          (congrArg (fun a : ℝ => a - inner ℝ (productH u u) (testInHH φ))
            (inner_neg_left (𝕜 := ℝ) (defectH d p) (testInHH φ))))
    have e3 : ∫ z : ℝ × Space, inner ℝ (-D z.1 z.2 - Pf z.1 z.2) (φ z.1 z.2) =
        -(inner ℝ (defectH d p) (testInHH φ) + inner ℝ (productH u u) (testInHH φ)) :=
      (congrArg (fun g : ℝ × Space → ℝ => ∫ z, g z) e).trans ((integral_neg _).trans
        (congrArg Neg.neg ((integral_add i1 i2).trans
          (congrArg₂ (fun a b : ℝ => a + b) (hdat1 φ hφ).symm (h5 φ hφ).symm))))
    exact e3.trans ((neg_add' _ _).trans e2.symm)
  have hcoer := h2 d hd p hp f hf κ (fun σ y => -D σ y - Pf σ y) hFper hpair
  have hpin : pinMap d (freeInv (d.period p) f) = targetGap d p :=
    (bordered_snd d p f κ).symm.trans (congrArg Prod.snd hb)
  have hvn : d.coercivePin * vecNorm (pinMap d (freeInv (d.period p) f)) =
      d.coercivePin * vecNorm (targetGap d p) := congrArg (fun v => d.coercivePin * vecNorm v) hpin
  have hsz0 : d.coerciveL2 * d.defectBound p + d.coerciveBall * d.defectBallBound p
      + d.coercivePin * vecNorm (targetGap d p) ≤ d.sizeBound := hd.size p hp
  have hsz : d.coerciveL2 * d.defectBound p + d.coerciveBall * d.defectBallBound p
      + d.coercivePin * vecNorm (pinMap d (freeInv (d.period p) f)) ≤ d.sizeBound :=
    (add_le_add le_rfl hvn.le).trans hsz0
  have hN : periodNorm (fun σ y => -D σ y - Pf σ y) ≤ d.defectBound p + A :=
    hFnorm.trans (add_le_add hDn hprodN)
  have hNB : periodBallNorm d.ballRadius (fun σ y => -D σ y - Pf σ y) ≤ d.defectBallBound p + A :=
    hFball.trans (add_le_add hDb (hPb.trans hprodN))
  have hZ : sizeZ d.weightFn (freeInv (d.period p) f) κ ≤ 2 * d.sizeBound :=
    size_arith hcoer hN hNB hd.coerciveL2_nonneg hd.coerciveBall_nonneg hsz
      hd.coerciveTotal_ge hd.coerciveTotal_pos hA0 hAle hd.small_first hρ
  refine ⟨hZ, ?_⟩
  have hSB := h3 d hd p hp f hf κ
  have hlt := hSB.1
  have hsq := hSB.2
  have hn : ‖-(defectH d p) - productH u u‖ ≤ ‖defectH d p‖ + ‖productH u u‖ :=
    (norm_sub_le _ _).trans_eq (congrArg (fun a : ℝ => a + ‖productH u u‖) (norm_neg (defectH d p)))
  have hAe : supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound =
      2 * supBoundFactor d.weight * d.sizeBound * d.supBound := by ring
  have hB : ‖(bordered d p (f, κ)).1‖ ≤
      d.defectMax + 2 * supBoundFactor d.weight * d.sizeBound * d.supBound :=
    (congrArg norm hb1).trans_le (hn.trans (add_le_add (hdat2.trans (hd.defect_le p hp))
      (hprodH.trans (hAle.trans_eq hAe))))
  have htw : (0 : ℝ) < d.twist := Nat.cast_pos.2 hd.twist_pos
  have hq0 : 0 ≤ d.period p / d.twist := div_nonneg hP.le htw.le
  have hq : d.period p / d.twist ≤ d.periodMax / d.twist :=
    div_le_div_of_nonneg_right (hd.period_le p hp) htw.le
  have hc0 : 0 ≤ 1 / d.weight + 2 * (d.period p / d.twist) * d.formBound :=
    add_nonneg (one_div_pos.2 hd.weight_pos).le
      (mul_nonneg (mul_nonneg zero_le_two hq0) hd.formBound_nonneg)
  have hc : 1 / d.weight + 2 * (d.period p / d.twist) * d.formBound ≤
      1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq zero_le_two)
      hd.formBound_nonneg)
  have hS := sup_arith hc0 hc (energyW_nonneg hw _) (energy_le_sq hw _ κ hZ) hq0 hq (norm_nonneg _)
    hB hd.actuatorBound_nonneg (Real.sqrt_nonneg _) ((vecNorm_le_sizeZ hw _ κ).trans hZ)
    (Real.sqrt_nonneg _) ((sqrt_energy_le_sizeZ _ _ κ).trans hZ) hρ hsq hd.small_third
  have hle : (supGrad (freeInv (d.period p) f)).toReal ≤ d.supBound :=
    (sq_le_sq₀ ENNReal.toReal_nonneg hsup0.le).1 hS
  calc supGrad (freeInv (d.period p) f) = ENNReal.ofReal (supGrad (freeInv (d.period p) f)).toReal :=
        (ENNReal.ofReal_toReal hlt.ne).symm
    _ ≤ ENNReal.ofReal d.supBound := ENNReal.ofReal_le_ofReal hle

end Internal.HeldMapsTo

open Internal.HeldMapsTo Internal.CoerciveBordered

theorem heldMapsToHolds_of (h1 : BorderedInvertibleHolds) (h2 : CoerciveBorderedHolds)
    (h3 : SupBoundHolds) (h4 : ProductBoundHolds) (h5 : ProductPairingHolds) (h6 : DataHolds)
    (h7 : InvarianceHolds) (h8 : FreeEquivariantHolds) : HeldMapsToHolds := by
  intro k d hd p hp x hx
  simp only [heldSet, Set.mem_ofPred_eq] at hx
  obtain ⟨hxi, hxs, hxg⟩ := hx
  have hP := hd.period_pos p hp
  have hadm : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hw : ∀ y, 0 ≤ d.weightFn y := fun y => hd.weight_pos.le.trans (hd.weightFn_lower y)
  have hsup0 := hd.supBound_pos
  have hρ := hd.sizeBound_nonneg
  have hfin : supGrad x.1 < ⊤ := lt_of_le_of_lt hxg ENNReal.ofReal_lt_top
  have hsupu : (supGrad x.1).toReal ≤ d.supBound := ENNReal.toReal_le_of_le_ofReal hsup0.le hxg
  have hEu : Real.sqrt (energyW d.weightFn x.1) ≤ 2 * d.sizeBound :=
    (sqrt_energy_le_sizeZ _ _ x.2).trans hxs
  have haf : 0 ≤ supBoundFactor d.weight := by
    unfold supBoundFactor
    positivity
  obtain ⟨hprodF, hprodN, hprodH⟩ := h4 d.weightFn d.weight hadm x.1 x.1 hfin
  have hA0 : 0 ≤ supBoundFactor d.weight * Real.sqrt (energyW d.weightFn x.1) *
      (supGrad x.1).toReal :=
    mul_nonneg (mul_nonneg haf (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg
  have hAle : supBoundFactor d.weight * Real.sqrt (energyW d.weightFn x.1) * (supGrad x.1).toReal ≤
      supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound :=
    mul_le_mul (mul_le_mul_of_nonneg_left hEu haf) hsupu ENNReal.toReal_nonneg
      (mul_nonneg haf (by linarith))
  obtain ⟨hinv1, -, hinv3⟩ := h7 d hd p hp
  have hyinv : (heldRight d p x.1).1 ∈ invariantHH d.symmetries :=
    Submodule.sub_mem _ (Submodule.neg_mem _ hinv3) (hinv1 x.1 hxi).2
  have hspec := borderedInv_spec (h1 d hd p hp).1 (heldRight d p x.1) hyinv
  suffices H : ∀ z : HH × (Fin k → ℝ), z.1 ∈ invariantHH d.symmetries →
      bordered d p z = heldRight d p x.1 → (freeInv (d.period p) z.1, z.2) ∈ heldSet d by
    exact H (borderedInv d p (heldRight d p x.1)) hspec.1 hspec.2
  intro z hz hb
  obtain ⟨f, κ⟩ := z
  have hf : f ∈ invariantHH d.symmetries := hz
  clear hz hspec
  simp only [heldSet, Set.mem_ofPred_eq]
  have hdat1 := (h6 d hd p hp).1
  have hdat2 := (h6 d hd p hp).2.1
  have hDF := defect_periodicField hd hp
  have hDn := periodNorm_le_of (hd.defect_nonneg p hp).1 (hd.defect_l2 p hp)
  have hDb := periodBallNorm_le_of (hd.defect_nonneg p hp).2 (hd.defect_ball p hp)
  have hSB := step_bounds h2 h3 hd hp x.1 f κ
    (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator (d.multiplier p))
    (productField x.1 x.1) (supBoundFactor d.weight * Real.sqrt (energyW d.weightFn x.1) * (supGrad x.1).toReal)
    hf hb hDF hprodF hDn hDb hprodN hprodH hA0 hAle hdat1 hdat2 (h5 x.1 x.1 hfin)
  exact ⟨h8 d.symmetries (d.period p) hP f hf, hSB.1, hSB.2⟩

end Breakdown.Cert
