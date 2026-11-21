import Breakdown.CertCell.BridgeStatements
import Breakdown.Cert.CoerciveSquareSum
import Breakdown.Cert.CoerciveTorus
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveModeL2
import Breakdown.Cert.CoerciveDensityPassageModes
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveBordered

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

open Coercive.ModeL2Internal

private theorem cnormSq_mat_sub (a b : Fin 3 × Fin 3 → ℂ) :
    cnormSq (a - b) = cnormSq a + cnormSq b - 2 * (cdotMat a b).re := by
  unfold cnormSq cdotMat
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Complex.sq_norm, Complex.normSq_sub]

private theorem matSq_sub (A B : Space →L[ℝ] Space) :
    matSq (A - B) = matSq A + matSq B - 2 * matInner A B := by
  unfold matSq matInner
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_apply, norm_sub_sq_real]
  ring

private theorem matSq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem matSq_sub_le (A B : Space →L[ℝ] Space) :
    matSq (A - B) ≤ 2 * matSq A + 2 * matSq B := by
  unfold matSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [sub_apply]
  nlinarith [norm_sub_sq_real (A (unitVector i)) (B (unitVector i)),
    norm_add_sq_real (A (unitVector i)) (B (unitVector i)), sq_nonneg ‖A (unitVector i) + B (unitVector i)‖]

private theorem aestronglyMeasurable_cnormSq_mat {μ : Measure (ℝ × Space)} {a : ℝ × Space → Fin 3 × Fin 3 → ℂ}
    (ha : ∀ ij, AEStronglyMeasurable (fun z => a z ij) μ) :
    AEStronglyMeasurable (fun z => cnormSq (a z)) μ := by
  unfold cnormSq
  exact Finset.aestronglyMeasurable_fun_sum _ (fun ij _ => (ha ij).norm.pow 2)

private theorem aestronglyMeasurable_matSq {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) volume := by
  unfold matSq
  exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
    ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hG).norm.pow 2)

private theorem integrable_cnormSq_modeGrad (hPars : Coercive.ModeSquareSumHolds)
    {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hp : IsTimePeriodic G)
    (hf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => cnormSq (modeGrad ι G z.1 z.2)) slab := by
  have hP := hPars.2.1 G hm hp hf
  have hms : AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeGrad ι G z.1 z.2)) slab :=
    (aestronglyMeasurable_cnormSq_mat (fun ij => aestronglyMeasurable_modeGrad hm ι ij)).mono_ac slab_ac
  have hle : periodLIntegral (fun σ y => cnormSq (modeGrad ι G σ y)) ≤
      periodLIntegral (fun σ y => matSq (G σ y)) := by
    rw [hP]
    exact ENNReal.le_tsum ι
  exact integrable_of_periodLIntegral (fun σ y => cnormSq (modeGrad ι G σ y)) hms
    (fun σ y => cnormSq_nonneg _) (lt_of_le_of_lt hle hf)

private theorem hasSum_cnormSq_modeGrad (hPars : Coercive.ModeSquareSumHolds)
    {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hp : IsTimePeriodic G)
    (hf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) :
    HasSum (fun ι : ℤ × ℤ => ∫ z, cnormSq (modeGrad ι G z.1 z.2) ∂slab)
      (periodLIntegral (fun σ y => matSq (G σ y))).toReal := by
  have hP : periodLIntegral (fun σ y => matSq (G σ y)) =
      ∑' ι : ℤ × ℤ, periodLIntegral (fun σ y => cnormSq (modeGrad ι G σ y)) := hPars.2.1 G hm hp hf
  have hms : ∀ ι : ℤ × ℤ, AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeGrad ι G z.1 z.2)) slab :=
    fun ι => (aestronglyMeasurable_cnormSq_mat (fun ij => aestronglyMeasurable_modeGrad hm ι ij)).mono_ac slab_ac
  have hA : ∀ ι : ℤ × ℤ, periodLIntegral (fun σ y => cnormSq (modeGrad ι G σ y)) ≠ ⊤ := fun ι =>
    ne_top_of_le_ne_top hf.ne (hP ▸ ENNReal.le_tsum ι)
  have hfun : (fun ι : ℤ × ℤ => ∫ z, cnormSq (modeGrad ι G z.1 z.2) ∂slab) =
      fun ι => (periodLIntegral (fun σ y => cnormSq (modeGrad ι G σ y))).toReal :=
    funext fun ι => (toReal_periodLIntegral (fun σ y => cnormSq (modeGrad ι G σ y)) (hms ι)
      (fun σ y => cnormSq_nonneg _)).symm
  rw [hfun, hP, ENNReal.tsum_toReal_eq hA]
  exact (ENNReal.summable_toReal (hP ▸ hf.ne)).hasSum

private theorem locallyIntegrable_of_matSq {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hp : IsTimePeriodic G)
    (hf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) :
    LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume := by
  have hcol : ∀ i, LocallyIntegrable (fun z : ℝ × Space => ‖G z.1 z.2 (unitVector i)‖) volume :=
    fun i => Cert.Internal.CoerciveBordered.column_locallyIntegrable hm hp hf i
  have hs := locallyIntegrable_finsetSum Finset.univ fun i _ => hcol i
  refine hs.mono hm (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  exact Coercive.Internal.PerturbationFacts.opNorm_le_sum_apply _

private theorem ae_modeGrad_sub {A B : ℝ → Space → (Space →L[ℝ] Space)}
    (hA : LocallyIntegrable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hB : LocallyIntegrable (fun z : ℝ × Space => B z.1 z.2) volume) :
    ∀ᵐ z ∂slab, ∀ ι : ℤ × ℤ,
      modeGrad ι (fun σ y => A σ y - B σ y) z.1 z.2 = modeGrad ι A z.1 z.2 - modeGrad ι B z.1 z.2 := by
  have h := (Coercive.Internal.ModeRotation.ae_integrable_orbit Coercive.axialRotationHolds_proof hA).and
    (Coercive.Internal.ModeRotation.ae_integrable_orbit Coercive.axialRotationHolds_proof hB)
  refine slab_ac.ae_le (h.mono fun z hz ι => ?_)
  exact Coercive.Internal.DensityPassageModes.modeGrad_sub_of hz.1 hz.2 ι

theorem pairingModeIdentity : PairingModeIdentityHolds := by
  intro A B hA hB hAp hBp hAf hBf
  have hPars := Coercive.modeSquareSumHolds_of Coercive.torusSquareSumHolds_proof Coercive.axialRotationHolds_proof
  set D : ℝ → Space → (Space →L[ℝ] Space) := fun σ y => A σ y - B σ y with hDdef
  have hD : AEStronglyMeasurable (fun z : ℝ × Space => D z.1 z.2) volume := hA.sub hB
  have hDp : IsTimePeriodic D := fun σ y => by
    show A (σ + 1) y - B (σ + 1) y = A σ y - B σ y
    rw [hAp σ y, hBp σ y]
  have hmA : AEStronglyMeasurable (fun z : ℝ × Space => matSq (A z.1 z.2)) slab :=
    (aestronglyMeasurable_matSq hA).mono_ac slab_ac
  have hmB : AEStronglyMeasurable (fun z : ℝ × Space => matSq (B z.1 z.2)) slab :=
    (aestronglyMeasurable_matSq hB).mono_ac slab_ac
  have hmD : AEStronglyMeasurable (fun z : ℝ × Space => matSq (D z.1 z.2)) slab :=
    (aestronglyMeasurable_matSq hD).mono_ac slab_ac
  have hiA := integrable_of_periodLIntegral (fun σ y => matSq (A σ y)) hmA (fun σ y => matSq_nonneg _) hAf
  have hiB := integrable_of_periodLIntegral (fun σ y => matSq (B σ y)) hmB (fun σ y => matSq_nonneg _) hBf
  have hiD : Integrable (fun z : ℝ × Space => matSq (D z.1 z.2)) slab := by
    refine ((hiA.const_mul 2).add (hiB.const_mul 2)).mono' hmD (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (matSq_nonneg _)]
    exact matSq_sub_le _ _
  have hDf : periodLIntegral (fun σ y => matSq (D σ y)) < ⊤ := by
    rw [periodLIntegral_eq_slab _ hmD]
    exact lt_top_iff_ne_top.2 ((lintegral_ofReal_ne_top_iff_integrable hmD
      (Filter.Eventually.of_forall fun z => matSq_nonneg _)).2 hiD)
  have hsA := hasSum_cnormSq_modeGrad hPars hA hAp hAf
  have hsB := hasSum_cnormSq_modeGrad hPars hB hBp hBf
  have hsD := hasSum_cnormSq_modeGrad hPars hD hDp hDf
  have hae := ae_modeGrad_sub (locallyIntegrable_of_matSq hA hAp hAf) (locallyIntegrable_of_matSq hB hBp hBf)
  have hpt : ∀ᵐ z ∂slab, ∀ ι : ℤ × ℤ,
      (cdotMat (modeGrad ι A z.1 z.2) (modeGrad ι B z.1 z.2)).re =
        (cnormSq (modeGrad ι A z.1 z.2) + cnormSq (modeGrad ι B z.1 z.2) -
          cnormSq (modeGrad ι D z.1 z.2)) / 2 := by
    filter_upwards [hae] with z hz ι
    rw [show modeGrad ι D z.1 z.2 = modeGrad ι A z.1 z.2 - modeGrad ι B z.1 z.2 from hz ι, cnormSq_mat_sub]
    ring
  have hterm : ∀ ι : ℤ × ℤ,
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdotMat (modeGrad ι A σ y) (modeGrad ι B σ y)).re =
        ((∫ z, cnormSq (modeGrad ι A z.1 z.2) ∂slab) + (∫ z, cnormSq (modeGrad ι B z.1 z.2) ∂slab) -
          ∫ z, cnormSq (modeGrad ι D z.1 z.2) ∂slab) / 2 := by
    intro ι
    have hiA' := integrable_cnormSq_modeGrad hPars hA hAp hAf ι
    have hiB' := integrable_cnormSq_modeGrad hPars hB hBp hBf ι
    have hiD' := integrable_cnormSq_modeGrad hPars hD hDp hDf ι
    have hq : Integrable (fun z : ℝ × Space => (cnormSq (modeGrad ι A z.1 z.2) + cnormSq (modeGrad ι B z.1 z.2) -
        cnormSq (modeGrad ι D z.1 z.2)) / 2) slab := ((hiA'.add hiB').sub hiD').div_const 2
    have hre : Integrable (fun z : ℝ × Space => (cdotMat (modeGrad ι A z.1 z.2) (modeGrad ι B z.1 z.2)).re) slab :=
      hq.congr (hpt.mono fun z h => (h ι).symm)
    calc ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdotMat (modeGrad ι A σ y) (modeGrad ι B σ y)).re
        = ∫ z, (cdotMat (modeGrad ι A z.1 z.2) (modeGrad ι B z.1 z.2)).re ∂slab := (integral_prod _ hre).symm
      _ = ∫ z, (cnormSq (modeGrad ι A z.1 z.2) + cnormSq (modeGrad ι B z.1 z.2) -
          cnormSq (modeGrad ι D z.1 z.2)) / 2 ∂slab := integral_congr_ae (hpt.mono fun z h => h ι)
      _ = _ := by
          have hAB : Integrable (fun z : ℝ × Space =>
              cnormSq (modeGrad ι A z.1 z.2) + cnormSq (modeGrad ι B z.1 z.2)) slab := hiA'.add hiB'
          rw [integral_div, integral_sub hAB hiD', integral_add hiA' hiB']
  have hval : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (A σ y) (B σ y) =
      ((periodLIntegral (fun σ y => matSq (A σ y))).toReal + (periodLIntegral (fun σ y => matSq (B σ y))).toReal -
        (periodLIntegral (fun σ y => matSq (D σ y))).toReal) / 2 := by
    have hfi : ∀ σ y, matInner (A σ y) (B σ y) = (matSq (A σ y) + matSq (B σ y) - matSq (D σ y)) / 2 := by
      intro σ y
      rw [show D σ y = A σ y - B σ y from rfl, matSq_sub]
      ring
    have hq : Integrable (fun z : ℝ × Space => (matSq (A z.1 z.2) + matSq (B z.1 z.2) - matSq (D z.1 z.2)) / 2)
        slab := ((hiA.add hiB).sub hiD).div_const 2
    calc ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (A σ y) (B σ y)
        = ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (matSq (A σ y) + matSq (B σ y) - matSq (D σ y)) / 2 := by
          simp_rw [hfi]
      _ = ∫ z, (matSq (A z.1 z.2) + matSq (B z.1 z.2) - matSq (D z.1 z.2)) / 2 ∂slab :=
          (integral_prod _ hq).symm
      _ = ((∫ z, matSq (A z.1 z.2) ∂slab) + (∫ z, matSq (B z.1 z.2) ∂slab) -
          ∫ z, matSq (D z.1 z.2) ∂slab) / 2 := by
          have hAB : Integrable (fun z : ℝ × Space => matSq (A z.1 z.2) + matSq (B z.1 z.2)) slab :=
            hiA.add hiB
          rw [integral_div, integral_sub hAB hiD, integral_add hiA hiB]
      _ = _ := by
          rw [toReal_periodLIntegral _ hmA (fun σ y => matSq_nonneg _),
            toReal_periodLIntegral _ hmB (fun σ y => matSq_nonneg _),
            toReal_periodLIntegral _ hmD (fun σ y => matSq_nonneg _)]
  have hsum : HasSum (fun ι : ℤ × ℤ =>
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdotMat (modeGrad ι A σ y) (modeGrad ι B σ y)).re)
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (A σ y) (B σ y)) := by
    rw [funext hterm, hval]
    exact ((hsA.add hsB).sub hsD).div_const 2
  exact ⟨hsum.summable, hsum.tsum_eq.symm⟩

end Bridge

end CertCell

end Breakdown
