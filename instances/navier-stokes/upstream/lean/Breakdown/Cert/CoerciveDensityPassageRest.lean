import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.CoercivePieceAbsorbMeasure
import Breakdown.Cert.CoerciveDensityPassageRestMeasurable
import Breakdown.Cert.CoerciveDensityPassageRestBoundAll
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoercivePieceDensityPassageRight
import Breakdown.Cert.CoerciveField
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveDensityPassageModes

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassageRest

def ampSq (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (modeSecondDeriv ι H σ y) + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y)) + cnormSq (modeGrad ι G σ y)
    + cnormSq (curlOfGrad (modeGrad ι G σ y)) + cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2

def ampTot (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∑' ι : ℤ × ℤ, ENNReal.ofReal (ampSq v G H ι σ y)

def diffSq (u : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
    (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (modeSecondDeriv ι Hu σ y - modeSecondDeriv ι H σ y)
    + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι Hu σ y) - curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    + cnormSq (modeGrad ι Gu σ y - modeGrad ι G σ y)
    + cnormSq (curlOfGrad (modeGrad ι Gu σ y) - curlOfGrad (modeGrad ι G σ y))
    + cnormSq (modeVel ι u σ y - modeVel ι v σ y) / (1 + ‖y‖) ^ 2

def diffTot (u : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
    (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∑' ι : ℤ × ℤ, ENNReal.ofReal (diffSq u Gu Hu v G H ι σ y)

theorem rest_pointwise_bound {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hWs : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWp : IsTimePeriodic W)
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwB : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ σ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (|modeRest m w W v G H ι σ y|)
        ≤ ENNReal.ofReal K * ampTot v G H σ y) ∧
      ∀ t : ℝ, 0 < t → ∀ (u : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
        (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) σ y,
        ∑' ι : ℤ × ℤ, ENNReal.ofReal (|modeRest m w W u Gu Hu ι σ y - modeRest m w W v G H ι σ y|)
          ≤ ENNReal.ofReal (K * (1 + 1 / t)) * diffTot u Gu Hu v G H σ y
            + ENNReal.ofReal (K * t) * ampTot v G H σ y := by
  exact DensityPassageRestBound.rest_pointwise_bound hA hWs hWp hWdec hwB v G H

private theorem continuous_curlGradOfSecondDeriv :
    Continuous (fun h : Fin 3 × Fin 3 × Fin 3 → ℂ => curlGradOfSecondDeriv h) :=
  continuous_pi fun il => by
    simp only [curlGradOfSecondDeriv]
    fun_prop

private theorem continuous_curlOfGrad : Continuous (fun g : Fin 3 × Fin 3 → ℂ => curlOfGrad g) :=
  continuous_pi fun i => by
    simp only [curlOfGrad]
    fun_prop

private theorem aem_terms {μ : Measure (ℝ × Space)} {h : ℝ × Space → Fin 3 × Fin 3 × Fin 3 → ℂ}
    {g : ℝ × Space → Fin 3 × Fin 3 → ℂ} {x : ℝ × Space → Fin 3 → ℂ}
    (hh : AEMeasurable h μ) (hg : AEMeasurable g μ) (hx : AEMeasurable x μ) :
    AEMeasurable (fun z => ENNReal.ofReal (cnormSq (h z) + cnormSq (curlGradOfSecondDeriv (h z)) + cnormSq (g z)
      + cnormSq (curlOfGrad (g z)) + cnormSq (x z) / (1 + ‖z.2‖) ^ 2)) μ := by
  have c3 : Continuous (fun x : Fin 3 × Fin 3 × Fin 3 → ℂ => cnormSq x) := Internal.FieldModes.continuous_cnormSq
  have c2 : Continuous (fun x : Fin 3 × Fin 3 → ℂ => cnormSq x) := Internal.FieldModes.continuous_cnormSq
  have c1 : Continuous (fun x : Fin 3 → ℂ => cnormSq x) := Internal.FieldModes.continuous_cnormSq
  have hr : AEMeasurable (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) μ :=
    ((measurable_snd.norm.const_add 1).pow_const 2).aemeasurable
  exact ENNReal.measurable_ofReal.comp_aemeasurable (((((c3.measurable.comp_aemeasurable hh).add
    ((c2.comp continuous_curlGradOfSecondDeriv).measurable.comp_aemeasurable hh)).add
    (c2.measurable.comp_aemeasurable hg)).add ((c1.comp continuous_curlOfGrad).measurable.comp_aemeasurable hg)).add
    ((c1.measurable.comp_aemeasurable hx).div hr))

private theorem aem_diff_terms {μ : Measure (ℝ × Space)} {h h' : ℝ × Space → Fin 3 × Fin 3 × Fin 3 → ℂ}
    {g g' : ℝ × Space → Fin 3 × Fin 3 → ℂ} {x x' : ℝ × Space → Fin 3 → ℂ}
    (hh : AEMeasurable h μ) (hh' : AEMeasurable h' μ) (hg : AEMeasurable g μ) (hg' : AEMeasurable g' μ)
    (hx : AEMeasurable x μ) (hx' : AEMeasurable x' μ) :
    AEMeasurable (fun z => ENNReal.ofReal (cnormSq (h z - h' z)
      + cnormSq (curlGradOfSecondDeriv (h z) - curlGradOfSecondDeriv (h' z)) + cnormSq (g z - g' z)
      + cnormSq (curlOfGrad (g z) - curlOfGrad (g' z)) + cnormSq (x z - x' z) / (1 + ‖z.2‖) ^ 2)) μ := by
  have c3 : Continuous (fun x : Fin 3 × Fin 3 × Fin 3 → ℂ => cnormSq x) := Internal.FieldModes.continuous_cnormSq
  have c2 : Continuous (fun x : Fin 3 × Fin 3 → ℂ => cnormSq x) := Internal.FieldModes.continuous_cnormSq
  have c1 : Continuous (fun x : Fin 3 → ℂ => cnormSq x) := Internal.FieldModes.continuous_cnormSq
  have hr : AEMeasurable (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) μ :=
    ((measurable_snd.norm.const_add 1).pow_const 2).aemeasurable
  have e3 := continuous_curlGradOfSecondDeriv.measurable.comp_aemeasurable hh
  have e3' := continuous_curlGradOfSecondDeriv.measurable.comp_aemeasurable hh'
  have e2 := continuous_curlOfGrad.measurable.comp_aemeasurable hg
  have e2' := continuous_curlOfGrad.measurable.comp_aemeasurable hg'
  exact ENNReal.measurable_ofReal.comp_aemeasurable (((((c3.measurable.comp_aemeasurable (hh.sub hh')).add
    (c2.measurable.comp_aemeasurable (e3.sub e3'))).add
    (c2.measurable.comp_aemeasurable (hg.sub hg'))).add (c1.measurable.comp_aemeasurable (e2.sub e2'))).add
    ((c1.measurable.comp_aemeasurable (hx.sub hx')).div hr))

theorem ampTot_aemeasurable {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) :
    AEMeasurable (fun z : ℝ × Space => ampTot v G H z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  unfold ampTot ampSq
  exact AEMeasurable.ennreal_tsum fun ι => aem_terms (Internal.PieceAbsorb.aemeasurable_modeSecondDeriv hH ι)
    (Internal.FieldModes.aemeasurable_modeGrad hG ι) (Internal.FieldModes.aemeasurable_modeVel hv ι)

theorem diffTot_aemeasurable {u v : ℝ → Space → Space} {Gu G : ℝ → Space → (Space →L[ℝ] Space)}
    {Hu H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) volume)
    (hGu : AEStronglyMeasurable (fun z : ℝ × Space => Gu z.1 z.2) volume)
    (hHu : AEStronglyMeasurable (fun z : ℝ × Space => Hu z.1 z.2) volume)
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) :
    AEMeasurable (fun z : ℝ × Space => diffTot u Gu Hu v G H z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  unfold diffTot diffSq
  exact AEMeasurable.ennreal_tsum fun ι => aem_diff_terms (Internal.PieceAbsorb.aemeasurable_modeSecondDeriv hHu ι)
    (Internal.PieceAbsorb.aemeasurable_modeSecondDeriv hH ι) (Internal.FieldModes.aemeasurable_modeGrad hGu ι)
    (Internal.FieldModes.aemeasurable_modeGrad hG ι) (Internal.FieldModes.aemeasurable_modeVel hu ι)
    (Internal.FieldModes.aemeasurable_modeVel hv ι)

theorem restDiff_aemeasurable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {Γ : Set Symmetry}
    (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hWs : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hSP : SmoothPerturbationIsPerturbationHolds) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {u : ℕ → ℝ → Space → Space}
    (hu : IsSmoothApproximation P v G H g u) (n : ℕ) :
    AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (|modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι z.1 z.2
          - modeRest m w W v G H ι z.1 z.2|)) PairingSplitInternal.periodMeasure := by
  exact DensityPassageRestMeasurable.rest_difference_aemeasurable hA hWs hSP hv hu n

private theorem cnormSq_modeVel_weight (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    cnormSq (modeVel ι (fun σ y => (1 / (1 + ‖y‖)) • v σ y) σ y)
      = cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 := by
  have e : modeVel ι (fun σ y => (1 / (1 + ‖y‖)) • v σ y) σ y = modeVel ι ((1 / (1 + ‖y‖)) • v) σ y := by
    unfold modeVel
    congr 1
    funext τ φ i
    simp only [Pi.smul_apply, Internal.ModeRotation.norm_axialRot axialRotationHolds_proof]
  rw [e, Internal.Field.modeVel_smul]
  unfold cnormSq
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have : 0 < 1 + ‖y‖ := by positivity
  field_simp

private theorem weighted_squareSum (hPars : ModeSquareSumHolds) {v : ℝ → Space → Space}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume) (hp : IsTimePeriodic v)
    (h2 : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤) :
    ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2)
      = periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
  have hc : Continuous (fun z : ℝ × Space => 1 / (1 + ‖z.2‖)) :=
    continuous_const.div (continuous_const.add continuous_snd.norm) fun z => by positivity
  have hXm : AEStronglyMeasurable (fun z : ℝ × Space => (1 / (1 + ‖z.2‖)) • v z.1 z.2) volume :=
    hc.aestronglyMeasurable.smul hm
  have hXp : IsTimePeriodic (fun σ y => (1 / (1 + ‖y‖)) • v σ y) := fun σ y => by
    simp only [hp σ y]
  have hXn : (fun σ y => ‖(1 / (1 + ‖y‖)) • v σ y‖ ^ 2) = fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := by
    funext σ y
    have h0 : 0 < 1 + ‖y‖ := by positivity
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  have hX2 : periodLIntegral (fun σ y => ‖(1 / (1 + ‖y‖)) • v σ y‖ ^ 2) < ⊤ := by
    rw [hXn]
    exact h2
  have hP := hPars.1 _ hXm hXp hX2
  rw [hXn] at hP
  rw [hP]
  simp only [cnormSq_modeVel_weight]

private theorem ampTot_le {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hvm : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hHm : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ampTot v G H σ y)
      ≤ ENNReal.ofReal 730 * (∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeSecondDeriv ι H σ y)))
          + ENNReal.ofReal 244 * (∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G σ y)))
          + ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2) := by
  have hr : AEMeasurable (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    ((measurable_snd.norm.const_add 1).pow_const 2).aemeasurable
  have mA : ∀ ι : ℤ × ℤ, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeSecondDeriv ι H z.1 z.2))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := fun ι =>
    Internal.PieceAbsorb.aemeasurable_ofReal_cnormSq (Internal.PieceAbsorb.aemeasurable_modeSecondDeriv hHm ι)
  have mB : ∀ ι : ℤ × ℤ, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := fun ι =>
    ENNReal.measurable_ofReal.comp_aemeasurable (Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
      (Internal.FieldModes.aemeasurable_modeGrad hGm ι))
  have mC : ∀ ι : ℤ × ℤ, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (cnormSq (modeVel ι v z.1 z.2) / (1 + ‖z.2‖) ^ 2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := fun ι =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
      (Internal.FieldModes.aemeasurable_modeVel hvm ι)).div hr)
  have mT : ∀ ι : ℤ × ℤ, AEMeasurable (fun z : ℝ × Space => (ENNReal.ofReal 730 * ENNReal.ofReal (cnormSq (modeSecondDeriv ι H z.1 z.2)) + ENNReal.ofReal 244 * ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2)) + ENNReal.ofReal (cnormSq (modeVel ι v z.1 z.2) / (1 + ‖z.2‖) ^ 2))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := fun ι =>
    (((mA ι).const_mul _).add ((mB ι).const_mul _)).add (mC ι)
  have hpt : ∀ σ y, ampTot v G H σ y ≤ ∑' ι : ℤ × ℤ, (ENNReal.ofReal 730 * ENNReal.ofReal (cnormSq (modeSecondDeriv ι H σ y)) + ENNReal.ofReal 244 * ENNReal.ofReal (cnormSq (modeGrad ι G σ y)) + ENNReal.ofReal (cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2)) := fun σ y => by
    unfold ampTot
    refine ENNReal.tsum_le_tsum fun ι => ?_
    have h1 := Internal.PieceAbsorb.cnormSq_curlGradOfSecondDeriv_le (modeSecondDeriv ι H σ y)
    have h2 := Internal.PieceAbsorb.cnormSq_curlOfGrad_le (modeGrad ι G σ y)
    have a0 := Internal.PieceAbsorb.cnormSq_nonneg' (modeSecondDeriv ι H σ y)
    have b0 := Internal.PieceAbsorb.cnormSq_nonneg' (modeGrad ι G σ y)
    have c0 : 0 ≤ cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 :=
      div_nonneg (Internal.PieceAbsorb.cnormSq_nonneg' _) (by positivity)
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) c0]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold ampSq
    linarith
  have hF : AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ, (ENNReal.ofReal 730 * ENNReal.ofReal (cnormSq (modeSecondDeriv ι H z.1 z.2)) + ENNReal.ofReal 244 * ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2)) + ENNReal.ofReal (cnormSq (modeVel ι v z.1 z.2) / (1 + ‖z.2‖) ^ 2))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    AEMeasurable.ennreal_tsum mT
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ampTot v G H σ y)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, (ENNReal.ofReal 730 * ENNReal.ofReal (cnormSq (modeSecondDeriv ι H σ y)) + ENNReal.ofReal 244 * ENNReal.ofReal (cnormSq (modeGrad ι G σ y)) + ENNReal.ofReal (cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2)) :=
        lintegral_mono fun σ => lintegral_mono fun y => hpt σ y
    _ = ∫⁻ z, ∑' ι : ℤ × ℤ, (ENNReal.ofReal 730 * ENNReal.ofReal (cnormSq (modeSecondDeriv ι H z.1 z.2)) + ENNReal.ofReal 244 * ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2)) + ENNReal.ofReal (cnormSq (modeVel ι v z.1 z.2) / (1 + ‖z.2‖) ^ 2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := (lintegral_prod _ hF).symm
    _ = ∑' ι : ℤ × ℤ, (ENNReal.ofReal 730 * ∫⁻ z, ENNReal.ofReal (cnormSq (modeSecondDeriv ι H z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)
          + ENNReal.ofReal 244 * ∫⁻ z, ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) + ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι v z.1 z.2) / (1 + ‖z.2‖) ^ 2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)) := by
        rw [lintegral_tsum mT]
        refine tsum_congr fun ι => ?_
        have hA' : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal 730
            * ENNReal.ofReal (cnormSq (modeSecondDeriv ι H z.1 z.2))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := (mA ι).const_mul _
        have hAB : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal 730
            * ENNReal.ofReal (cnormSq (modeSecondDeriv ι H z.1 z.2))
            + ENNReal.ofReal 244 * ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
          hA'.add ((mB ι).const_mul _)
        rw [lintegral_add_left' hAB, lintegral_add_left' hA', lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        simp only [lintegral_prod _ (mA _), lintegral_prod _ (mB _), lintegral_prod _ (mC _)]

theorem ampTot_finite (hPars : ModeSquareSumHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {u : ℕ → ℝ → Space → Space}
    (hu : IsSmoothApproximation P v G H g u) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ampTot v G H σ y) < ⊤ := by
  have hHs : periodLIntegral (fun σ y => secondDerivSq (H σ y)) < ⊤ :=
    (perturbationSecondDerivBoundHolds_proof Γ P v G H g hv).trans_lt hv.sumSecondPartials_finite
  have hw := Internal.PassageLimit.weightedVelocity_lt_top hv hu
  refine (ampTot_le hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv).trans_lt ?_
  rw [← hPars.2.2.1 H hv.measurable_secondDeriv hv.periodic_secondDeriv hHs,
    ← hPars.2.1 G hv.measurable_gradient hv.periodic_gradient hv.gradient_finite,
    weighted_squareSum hPars hv.measurable_velocity hv.periodic_velocity hw]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHs,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.gradient_finite⟩, hw⟩

private theorem curlGradOfSecondDeriv_sub (a b : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    curlGradOfSecondDeriv (a - b) = curlGradOfSecondDeriv a - curlGradOfSecondDeriv b := by
  funext il
  simp only [curlGradOfSecondDeriv, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem curlOfGrad_sub (a b : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad (a - b) = curlOfGrad a - curlOfGrad b := by
  funext i
  simp only [curlOfGrad, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem diffTot_tendsto (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {u : ℕ → ℝ → Space → Space}
    (hu : IsSmoothApproximation P v G H g u) :
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      diffTot (u n) (gradField (u n)) (secondDerivField (u n)) v G H σ y) atTop (𝓝 0) := by
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hae : ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume), ∀ n, ∀ κ : ℤ × ℤ,
      modeVel κ (fun σ y => u n σ y - v σ y) z.1 z.2 = modeVel κ (u n) z.1 z.2 - modeVel κ v z.1 z.2 ∧
      modeGrad κ (fun σ y => gradField (u n) σ y - G σ y) z.1 z.2 =
        modeGrad κ (gradField (u n)) z.1 z.2 - modeGrad κ G z.1 z.2 ∧
      modeSecondDeriv κ (fun σ y => secondDerivField (u n) σ y - H σ y) z.1 z.2 =
        modeSecondDeriv κ (secondDerivField (u n)) z.1 z.2 - modeSecondDeriv κ H z.1 z.2 := by
    have h := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)
      (Internal.DensityPassageModes.ae_modes_sub hSP hv hu)
    rw [← Internal.FieldModes.slab_eq] at h
    exact h
  have hmV : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => u n z.1 z.2 - v z.1 z.2) volume := fun n =>
    (hpn n).measurable_velocity.sub hv.measurable_velocity
  have hmG : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => gradField (u n) z.1 z.2 - G z.1 z.2) volume :=
    fun n => (hpn n).measurable_gradient.sub hv.measurable_gradient
  have hmH : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField (u n) z.1 z.2 - H z.1 z.2) volume :=
    fun n => (hpn n).measurable_secondDeriv.sub hv.measurable_secondDeriv
  have heq : ∀ n, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      diffTot (u n) (gradField (u n)) (secondDerivField (u n)) v G H σ y)
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ampTot (fun σ y => u n σ y - v σ y)
        (fun σ y => gradField (u n) σ y - G σ y) (fun σ y => secondDerivField (u n) σ y - H σ y) σ y := fun n => by
    have m1 := diffTot_aemeasurable (hpn n).measurable_velocity (hpn n).measurable_gradient
      (hpn n).measurable_secondDeriv hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv
    have m2 := ampTot_aemeasurable (v := fun σ y => u n σ y - v σ y) (G := fun σ y => gradField (u n) σ y - G σ y) (H := fun σ y => secondDerivField (u n) σ y - H σ y) (hmV n) (hmG n) (hmH n)
    rw [← lintegral_prod _ m1, ← lintegral_prod _ m2]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with z hz
    unfold diffTot ampTot
    refine tsum_congr fun ι => ?_
    obtain ⟨e1, e2, e3⟩ := hz n ι
    unfold diffSq ampSq
    rw [e1, e2, e3, curlGradOfSecondDeriv_sub, curlOfGrad_sub]
  have hH := hu.2.2.1
  have hG := hu.2.1
  have hV := hu.2.2.2.1
  have hfin : ∀ᶠ n in atTop,
      periodLIntegral (fun σ y => secondDerivSq (secondDerivField (u n) σ y - H σ y)) < ⊤ ∧
      periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y)) < ⊤ ∧
      periodLIntegral (fun σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤ :=
    ((hH.eventually (gt_mem_nhds zero_lt_one)).and ((hG.eventually (gt_mem_nhds zero_lt_one)).and
      (hV.eventually (gt_mem_nhds zero_lt_one)))).mono fun n hn =>
        ⟨hn.1.trans ENNReal.one_lt_top, hn.2.1.trans ENNReal.one_lt_top, hn.2.2.trans ENNReal.one_lt_top⟩
  have hR : Tendsto (fun n => ENNReal.ofReal 730 * periodLIntegral (fun σ y => secondDerivSq (secondDerivField (u n) σ y - H σ y))
      + ENNReal.ofReal 244 * periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y))
      + periodLIntegral (fun σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)) atTop (𝓝 0) := by
    have h := ((ENNReal.Tendsto.const_mul hH (Or.inr (ENNReal.ofReal_ne_top (r := 730)))).add
      (ENNReal.Tendsto.const_mul hG (Or.inr (ENNReal.ofReal_ne_top (r := 244))))).add hV
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hfin] with n hn
  rw [heq n]
  refine (ampTot_le (v := fun σ y => u n σ y - v σ y) (G := fun σ y => gradField (u n) σ y - G σ y) (H := fun σ y => secondDerivField (u n) σ y - H σ y) (hmV n) (hmG n) (hmH n)).trans (le_of_eq ?_)
  have hHp : IsTimePeriodic (fun σ y => secondDerivField (u n) σ y - H σ y) := fun σ y => by
    simp only [(hpn n).periodic_secondDeriv σ y, hv.periodic_secondDeriv σ y]
  have hGp : IsTimePeriodic (fun σ y => gradField (u n) σ y - G σ y) := fun σ y => by
    simp only [(hpn n).periodic_gradient σ y, hv.periodic_gradient σ y]
  have hVp : IsTimePeriodic (fun σ y => u n σ y - v σ y) := fun σ y => by
    simp only [(hpn n).periodic_velocity σ y, hv.periodic_velocity σ y]
  rw [← hPars.2.2.1 (fun σ y => secondDerivField (u n) σ y - H σ y) (hmH n) hHp hn.1,
    ← hPars.2.1 (fun σ y => gradField (u n) σ y - G σ y) (hmG n) hGp hn.2.1,
    weighted_squareSum hPars (v := fun σ y => u n σ y - v σ y) (hmV n) hVp hn.2.2]

theorem rest_abs_converges_of (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {Γ : Set Symmetry}
    (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hWs : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWp : IsTimePeriodic W)
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwB : ∃ B, ∀ y, w y ≤ B) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {u : ℕ → ℝ → Space → Space}
    (hu : IsSmoothApproximation P v G H g u) :
    (∀ n, AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (|modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι z.1 z.2
          - modeRest m w W v G H ι z.1 z.2|)) PairingSplitInternal.periodMeasure) ∧
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (|modeRest m w W v G H ι σ y|)) < ⊤ ∧
      Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (|modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y
          - modeRest m w W v G H ι σ y|)) atTop (𝓝 0) := by
  obtain ⟨K, -, hKv, hKd⟩ := rest_pointwise_bound hA hWs hWp hWdec hwB v G H
  have hmA := ampTot_aemeasurable hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv
  have hmD : ∀ n, AEMeasurable (fun z : ℝ × Space =>
      diffTot (u n) (gradField (u n)) (secondDerivField (u n)) v G H z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := fun n =>
    diffTot_aemeasurable (hSP P (u n) (hu.1 n)).measurable_velocity (hSP P (u n) (hu.1 n)).measurable_gradient
      (hSP P (u n) (hu.1 n)).measurable_secondDeriv hv.measurable_velocity hv.measurable_gradient hv.measurable_secondDeriv
  have hmR := restDiff_aemeasurable hA hWs hSP hv hu
  have hfin := ampTot_finite hPars hv hu
  have hD := diffTot_tendsto hPars hSP hv hu
  refine ⟨hmR, ?_, ?_⟩
  · calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (|modeRest m w W v G H ι σ y|))
        ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal K * ampTot v G H σ y :=
          lintegral_mono fun σ => lintegral_mono fun y => hKv σ y
      _ = ENNReal.ofReal K * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ampTot v G H σ y := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun σ => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  · have hb : ∀ t : ℝ, 0 < t → ∀ n, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
        ENNReal.ofReal (|modeRest m w W (u n) (gradField (u n)) (secondDerivField (u n)) ι σ y
          - modeRest m w W v G H ι σ y|))
        ≤ ENNReal.ofReal (K * (1 + 1 / t)) * (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            diffTot (u n) (gradField (u n)) (secondDerivField (u n)) v G H σ y)
          + ENNReal.ofReal (K * t) * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ampTot v G H σ y := by
      intro t ht n
      have hmd := (hmD n).const_mul (ENNReal.ofReal (K * (1 + 1 / t)))
      have hma := hmA.const_mul (ENNReal.ofReal (K * t))
      calc _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            (ENNReal.ofReal (K * (1 + 1 / t)) * diffTot (u n) (gradField (u n)) (secondDerivField (u n)) v G H σ y
              + ENNReal.ofReal (K * t) * ampTot v G H σ y) :=
            lintegral_mono fun σ => lintegral_mono fun y => hKd t ht (u n) _ _ σ y
        _ = ∫⁻ z, (ENNReal.ofReal (K * (1 + 1 / t))
              * diffTot (u n) (gradField (u n)) (secondDerivField (u n)) v G H z.1 z.2
              + ENNReal.ofReal (K * t) * ampTot v G H z.1 z.2)
              ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
            (lintegral_prod _ (hmd.add hma)).symm
        _ = ENNReal.ofReal (K * (1 + 1 / t)) * (∫⁻ z,
              diffTot (u n) (gradField (u n)) (secondDerivField (u n)) v G H z.1 z.2
              ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
            + ENNReal.ofReal (K * t) * ∫⁻ z, ampTot v G H z.1 z.2
              ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
            rw [lintegral_add_left' hmd, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = _ := by rw [lintegral_prod _ (hmD n), lintegral_prod _ hmA]
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (K * t)) (𝓝[>] 0) (𝓝 0) := by
      have hct : Continuous (fun t : ℝ => ENNReal.ofReal (K * t)) :=
        ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
      have h := (hct.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    have hc := ENNReal.Tendsto.mul_const h1 (Or.inr hfin.ne)
    rw [zero_mul] at hc
    obtain ⟨t, htJ, ht⟩ := ((hc.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne'))).and
      self_mem_nhdsWithin).exists
    have hI := ENNReal.Tendsto.const_mul hD (Or.inr (ENNReal.ofReal_ne_top (r := K * (1 + 1 / t))))
    rw [mul_zero] at hI
    filter_upwards [hI.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne'))] with n hn
    calc _ ≤ _ := hb t ht n
      _ ≤ ε / 2 + ε / 2 := add_le_add hn.le htJ.le
      _ = ε := ENNReal.add_halves ε

end Internal.DensityPassageRest

end Coercive

end Breakdown
