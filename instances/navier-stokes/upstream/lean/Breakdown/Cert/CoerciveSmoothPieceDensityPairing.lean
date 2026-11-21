import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePieceAbsorb
import Breakdown.Cert.CoerciveSmoothPiecePairingSplitWeight

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceDensity

section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

theorem slab_integrable_inner {A B : ℝ → Space → Space}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume)
    (hA2 : periodLIntegral (fun σ y => ‖A σ y‖ ^ 2) < ⊤)
    (hB2 : periodLIntegral (fun σ y => ‖B σ y‖ ^ 2) < ⊤) :
    Integrable (fun z : ℝ × Space => inner ℝ (A z.1 z.2) (B z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hμ' : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hsq : ∀ (u : ℝ × Space → Space), AEStronglyMeasurable u volume →
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖u (σ, y)‖ ^ 2)) < ⊤ →
      Integrable (fun z => ‖u z‖ ^ 2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    intro u hu hfin
    have hu' : AEStronglyMeasurable u ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
      rw [hμ']
      exact hu.restrict
    have e : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖u (σ, y)‖ ^ 2)
        = ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
      (lintegral_prod (fun z => ENNReal.ofReal (‖u z‖ ^ 2))
        ((hu'.norm.aemeasurable.pow_const 2).ennreal_ofReal)).symm
    rw [e] at hfin
    refine (integrable_toReal_of_lintegral_ne_top (hu'.norm.pow 2).aemeasurable.ennreal_ofReal
      hfin.ne).congr ?_
    exact ae_of_all _ (fun z => ENNReal.toReal_ofReal (sq_nonneg _))
  have hAi := hsq _ hA hA2
  have hBi := hsq _ hB hB2
  have hAμ : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [hμ']
    exact hA.restrict
  have hBμ : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [hμ']
    exact hB.restrict
  refine Integrable.mono' ((hAi.add hBi).div_const 2) (hAμ.inner hBμ) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  show ‖A z.1 z.2‖ * ‖B z.1 z.2‖ ≤ (‖A z.1 z.2‖ ^ 2 + ‖B z.1 z.2‖ ^ 2) / 2
  nlinarith [sq_nonneg (‖A z.1 z.2‖ - ‖B z.1 z.2‖)]

theorem slab_pairing_eq {A B : ℝ → Space → Space}
    (hi : Integrable (fun z : ℝ × Space => inner ℝ (A z.1 z.2) (B z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)) :
    periodPairing A B = ∫ z, inner ℝ (A z.1 z.2) (B z.1 z.2)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  rw [integral_prod _ hi]
  rfl

theorem pairing_linear {k : ℕ} (F0 M : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) (κ : Fin k → ℝ)
    (hF0 : AEStronglyMeasurable (fun z : ℝ × Space => F0 z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F0 σ y‖ ^ 2) < ⊤)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (hMm : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume)
    (hM2 : periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤) :
    periodPairing (fun σ y => F0 σ y + ∑ i, κ i • act i σ y) M
      = periodPairing F0 M + ∑ i, κ i * periodPairing (act i) M := by
  have i0 := slab_integrable_inner hF0 hMm hF2 hM2
  have ii := fun i => slab_integrable_inner (hactm i) hMm (hact2 i) hM2
  have iS : Integrable (fun z : ℝ × Space => ∑ i, κ i * inner ℝ (act i z.1 z.2) (M z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    integrable_finsetSum _ fun i _ => (ii i).const_mul (κ i)
  have heq : (fun z : ℝ × Space => inner ℝ (F0 z.1 z.2 + ∑ i, κ i • act i z.1 z.2) (M z.1 z.2))
      = fun z => inner ℝ (F0 z.1 z.2) (M z.1 z.2) + ∑ i, κ i * inner ℝ (act i z.1 z.2) (M z.1 z.2) := by
    funext z
    rw [inner_add_left, sum_inner]
    simp only [real_inner_smul_left]
  have hiC : Integrable (fun z : ℝ × Space => inner ℝ (F0 z.1 z.2 + ∑ i, κ i • act i z.1 z.2) (M z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [heq]
    exact i0.add iS
  rw [slab_pairing_eq (A := fun σ y => F0 σ y + ∑ i, κ i • act i σ y) (B := M) hiC, heq,
    integral_add i0 iS, integral_finsetSum _ fun i _ => (ii i).const_mul (κ i),
    slab_pairing_eq (A := F0) (B := M) i0]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, slab_pairing_eq (A := act i) (B := M) (ii i)]

theorem period_add_lt_top {f g : ℝ → Space → ℝ} (hf0 : ∀ σ y, 0 ≤ f σ y) (hg0 : ∀ σ y, 0 ≤ g σ y)
    (hg : Measurable (fun z : ℝ × Space => g z.1 z.2))
    (hf2 : periodLIntegral f < ⊤) (hg2 : periodLIntegral g < ⊤) :
    periodLIntegral (fun σ y => f σ y + g σ y) < ⊤ := by
  unfold periodLIntegral at hf2 hg2 ⊢
  have e : ∀ σ y, ENNReal.ofReal (f σ y + g σ y) = ENNReal.ofReal (f σ y) + ENNReal.ofReal (g σ y) :=
    fun σ y => ENNReal.ofReal_add (hf0 σ y) (hg0 σ y)
  simp_rw [e]
  rw [Internal.PieceAbsorb.lintegral_add_iter (ENNReal.measurable_ofReal.comp hg).aemeasurable]
  exact ENNReal.add_lt_top.2 ⟨hf2, hg2⟩

theorem smoothRight_sq_le {D : ℝ} (hD0 : 0 ≤ D) (bW : ∀ σ y, ‖W σ y‖ ≤ D)
    (bDW : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2)
    (hL : ∀ σ y, ‖secondDerivTrace (secondDerivField v σ y)‖ ≤ 3 * ‖secondDerivField v σ y‖) (σ : ℝ) (y : Space) :
    ‖smoothRight P W v σ y‖ ^ 2 ≤ (4 * (9 + D ^ 2)) *
        ((‖transportPart P v σ y‖ ^ 2 + ‖secondDerivField v σ y‖ ^ 2) + (‖fderiv ℝ (v σ) y‖ ^ 2
          + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)) := by
  have ht := norm_nonneg (transportPart P v σ y)
  have hh := norm_nonneg (secondDerivField v σ y)
  have hg := norm_nonneg (fderiv ℝ (v σ) y)
  have hvn := norm_nonneg (v σ y)
  have hy : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have e1 : smoothRight P W v σ y = transportPart P v σ y - secondDerivTrace (secondDerivField v σ y)
      + fderiv ℝ (v σ) y (W σ y) + fderiv ℝ (W σ) y (v σ y) := rfl
  have n3 : ‖fderiv ℝ (v σ) y (W σ y)‖ ≤ D * ‖fderiv ℝ (v σ) y‖ := by
    refine ((fderiv ℝ (v σ) y).le_opNorm _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (bW σ y) hg
  set q := ‖v σ y‖ / (1 + ‖y‖) with hq
  have hq0 : 0 ≤ q := div_nonneg hvn hy.le
  have n4 : ‖fderiv ℝ (W σ) y (v σ y)‖ ≤ D * q := by
    refine ((fderiv ℝ (W σ) y).le_opNorm _).trans ?_
    have h2 := bDW σ y
    have h3 : D / (1 + ‖y‖) ^ 2 ≤ D / (1 + ‖y‖) :=
      div_le_div_of_nonneg_left hD0 hy (by nlinarith [norm_nonneg y])
    calc ‖fderiv ℝ (W σ) y‖ * ‖v σ y‖ ≤ D / (1 + ‖y‖) * ‖v σ y‖ :=
          mul_le_mul_of_nonneg_right (h2.trans h3) hvn
      _ = D * q := by rw [hq]; ring
  have hqsq : ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 = q ^ 2 := by rw [hq, div_pow]
  rw [hqsq]
  have nsum : ‖smoothRight P W v σ y‖ ≤ ‖transportPart P v σ y‖ + 3 * ‖secondDerivField v σ y‖
      + D * ‖fderiv ℝ (v σ) y‖ + D * q := by
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add le_rfl (hL σ y))) n3)) n4)
  have hs0 : 0 ≤ ‖smoothRight P W v σ y‖ := norm_nonneg _
  have hsq : ‖smoothRight P W v σ y‖ ^ 2 ≤ (‖transportPart P v σ y‖ + 3 * ‖secondDerivField v σ y‖
      + D * ‖fderiv ℝ (v σ) y‖ + D * q) ^ 2 := pow_le_pow_left₀ hs0 nsum 2
  refine hsq.trans ?_
  nlinarith [sq_nonneg (‖transportPart P v σ y‖ - 3 * ‖secondDerivField v σ y‖),
    sq_nonneg (‖transportPart P v σ y‖ - D * ‖fderiv ℝ (v σ) y‖), sq_nonneg (‖transportPart P v σ y‖ - D * q),
    sq_nonneg (3 * ‖secondDerivField v σ y‖ - D * ‖fderiv ℝ (v σ) y‖), sq_nonneg (3 * ‖secondDerivField v σ y‖ - D * q),
    sq_nonneg (D * ‖fderiv ℝ (v σ) y‖ - D * q), sq_nonneg D, mul_nonneg (sq_nonneg D) (sq_nonneg q),
    mul_nonneg (sq_nonneg D) (sq_nonneg ‖fderiv ℝ (v σ) y‖)]

theorem smoothRight_eq (σ : ℝ) (y : Space) :
    smoothRight P W v σ y = transportPart P v σ y - secondDerivTrace (secondDerivField v σ y)
      + fderiv ℝ (v σ) y (W σ y) + fderiv ℝ (W σ) y (v σ y) := rfl

theorem deriv_time_eq (hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2)) (σ : ℝ) (y : Space) :
    deriv (fun s => v s y) σ = fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (σ, y) ((1 : ℝ), (0 : Space)) := by
  have h1 : HasFDerivAt (fun z : ℝ × Space => v z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) (σ, y)) (σ, y) :=
    ((hv2.differentiable (by simp)) (σ, y)).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : Space)) σ :=
    (hasDerivAt_id σ).prodMk (hasDerivAt_const σ y)
  exact (h1.comp_hasDerivAt σ h2).deriv

theorem continuous_transportPart (hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2)) :
    Continuous (fun z : ℝ × Space => transportPart P v z.1 z.2) := by
  have cT : Continuous (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) := by
    have e : (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1)
        = fun z => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) z ((1 : ℝ), (0 : Space)) :=
      funext fun z => deriv_time_eq v hv2 z.1 z.2
    rw [e]
    exact (hv2.continuous_fderiv (by simp)).clm_apply continuous_const
  have cDv := Internal.PieceAbsorb.continuous_fderiv_slice hv2
  unfold transportPart
  exact ((cT.const_smul (1 / P)).add (hv2.continuous.const_smul (1 / 2 : ℝ))).add
    ((cDv.clm_apply continuous_snd).const_smul (1 / 2 : ℝ))

theorem measurable_sumSecondPartials (hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2)) :
    Measurable (fun z : ℝ × Space => secondDerivTrace (secondDerivField v z.1 z.2)) := by
  have mH := Internal.PieceAbsorb.measurable_secondDeriv_slice hv2
  unfold secondDerivTrace
  refine Finset.measurable_fun_sum _ fun j _ => ?_
  have hc : Continuous fun H : Space →L[ℝ] Space →L[ℝ] Space => H (unitVector j) (unitVector j) :=
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  exact hc.measurable.comp mH

theorem aesm_smoothRight (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2)) :
    AEStronglyMeasurable (fun z : ℝ × Space => smoothRight P W v z.1 z.2) volume := by
  have cDv := Internal.PieceAbsorb.continuous_fderiv_slice hv2
  have cDW := Internal.PieceAbsorb.continuous_fderiv_slice hW
  have c3 : Continuous fun z : ℝ × Space => fderiv ℝ (v z.1) z.2 (W z.1 z.2) := cDv.clm_apply hW.continuous
  have c4 : Continuous fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2) := cDW.clm_apply hv2.continuous
  have hs : AEStronglyMeasurable (fun z : ℝ × Space => transportPart P v z.1 z.2
      - secondDerivTrace (secondDerivField v z.1 z.2) + fderiv ℝ (v z.1) z.2 (W z.1 z.2)
      + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume :=
    (((continuous_transportPart P v hv2).aestronglyMeasurable.sub
      (measurable_sumSecondPartials v hv2).aestronglyMeasurable).add c3.aestronglyMeasurable).add c4.aestronglyMeasurable
  have e : (fun z : ℝ × Space => smoothRight P W v z.1 z.2) = fun z => transportPart P v z.1 z.2
      - secondDerivTrace (secondDerivField v z.1 z.2) + fderiv ℝ (v z.1) z.2 (W z.1 z.2)
      + fderiv ℝ (W z.1) z.2 (v z.1 z.2) := funext fun z => smoothRight_eq P W v z.1 z.2
  rw [e]
  exact hs

theorem periodic_smoothRight (hWp : IsTimePeriodic W) (hv : IsSmoothPerturbation P v) :
    IsTimePeriodic (smoothRight P W v) := by
  intro σ y
  have pv : v (σ + 1) = v σ := funext (hv.periodic σ)
  have pW : W (σ + 1) = W σ := funext (hWp σ)
  have pd : deriv (fun s => v s y) (σ + 1) = deriv (fun s => v s y) σ := by
    rw [← deriv_comp_add_const]
    congr 1
    funext s
    exact hv.periodic s y
  simp only [smoothRight, secondDerivField]
  rw [pd, pv, pW]

theorem right_side_sq (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) :
    AEStronglyMeasurable (fun z : ℝ × Space => smoothRight P W v z.1 z.2) volume ∧
      IsTimePeriodic (smoothRight P W v) ∧
      periodLIntegral (fun σ y => ‖smoothRight P W v σ y‖ ^ 2) < ⊤ := by
  obtain ⟨D, hD⟩ := hWdecay
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨aesm_smoothRight P W v hW hv2, periodic_smoothRight P W v hWp hv, ?_⟩
  have hD0 : 0 ≤ D := by
    have := hD 0 0 0 (by norm_num)
    simp only [norm_zero, add_zero, div_one, zero_add, pow_one] at this
    exact (norm_nonneg _).trans this
  have bW : ∀ σ y, ‖W σ y‖ ≤ D := fun σ y => by
    have := hD σ y 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at this
    exact this.trans (div_le_self hD0 (by linarith [norm_nonneg y]))
  have bDW : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 := fun σ y => by
    have := hD σ y 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at this
  have hL : ∀ σ y, ‖secondDerivTrace (secondDerivField v σ y)‖ ≤ 3 * ‖secondDerivField v σ y‖ := by
    intro σ y
    unfold secondDerivTrace
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin 3, ‖secondDerivField v σ y (unitVector j) (unitVector j)‖ ≤ ∑ _j : Fin 3, ‖secondDerivField v σ y‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          have a := (secondDerivField v σ y).le_opNorm₂ (unitVector j) (unitVector j)
          rw [Internal.PerturbationFacts.norm_unitVector_eq, mul_one, mul_one] at a
          exact a
      _ = 3 * ‖secondDerivField v σ y‖ := by simp
  have hHn : ∀ σ y, ‖secondDerivField v σ y‖ = ‖iteratedFDeriv ℝ 2 (v σ) y‖ := by
    intro σ y
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rfl
  have hpt := fun σ y => smoothRight_sq_le P W v hD0 bW bDW hL σ y
  refine Internal.SmoothWeightSplit.periodLIntegral_lt_top_of_le (by positivity) hpt ?_
  have f0 : periodLIntegral (fun σ y => ‖transportPart P v σ y‖ ^ 2) < ⊤ := by
    have := hv.transport_finite 0
    simpa only [norm_iteratedFDeriv_zero] using this
  have f2 : periodLIntegral (fun σ y => ‖secondDerivField v σ y‖ ^ 2) < ⊤ := by
    have := hv.derivatives_finite 2 (by norm_num)
    simpa only [hHn] using this
  have f1 : periodLIntegral (fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2) < ⊤ := by
    have := hv.derivatives_finite 1 le_rfl
    simpa only [norm_iteratedFDeriv_one] using this
  have fw := hv.weighted_finite
  have mv : Measurable (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) := by
    have : Continuous (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) :=
      Continuous.div (by fun_prop) (by fun_prop) (fun z => by positivity)
    exact this.measurable
  refine period_add_lt_top (fun σ y => by positivity) (fun σ y => by positivity) ?_
    (period_add_lt_top (fun σ y => by positivity) (fun σ y => by positivity)
      ((Internal.PieceAbsorb.measurable_secondDeriv_slice hv2).norm.pow_const 2) f0 f2)
    (period_add_lt_top (fun σ y => by positivity) (fun σ y => by positivity) mv f1 fw)
  exact (((Internal.PieceAbsorb.continuous_fderiv_slice hv2).norm.pow 2).measurable).add mv


end Pieces

end Internal.SmoothPieceDensity

end Coercive

end Breakdown
