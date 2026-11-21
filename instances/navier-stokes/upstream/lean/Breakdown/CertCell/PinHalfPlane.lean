import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.TailFlipDecay
import Breakdown.Cert.CoerciveMain
import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.CoerciveFrequencySeminormTransportModes
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveBordered
import Breakdown.FracCell.CylinderComp

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.PinHalf

open Coercive Coercive.Internal.ModeRotation

def pairDensity (ξ : ℤ × ℤ) (A B : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : ℝ :=
  (cdotMat (modeGrad ξ A σ y) (modeGrad ξ B σ y)).re

theorem cdotMat_phase (c : ℂ) (hc : ‖c‖ = 1) (x z : Fin 3 × Fin 3 → ℂ) :
    cdotMat (fun ij => c * x ij) (fun ij => c * z ij) = cdotMat x z := by
  have h : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  unfold cdotMat
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [map_mul]
  linear_combination (x ij * (starRingEnd ℂ) (z ij)) * h

theorem cnormSq_phase (c : ℂ) (hc : ‖c‖ = 1) (x : Fin 3 × Fin 3 → ℂ) :
    cnormSq (fun ij => c * x ij) = cnormSq x := by
  unfold cnormSq
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [norm_mul, hc, one_mul]

theorem pairDensity_shift {A B : ℝ → Space → (Space →L[ℝ] Space)} (hA : IsTimePeriodic A)
    (hB : IsTimePeriodic B) (ξ : ℤ × ℤ) (σ : ℝ) (y : Space) :
    pairDensity ξ A B σ y = pairDensity ξ A B 0 y := by
  unfold pairDensity
  rw [FrequencySeminorm.Internal.modeGrad_shift ξ hA σ y, FrequencySeminorm.Internal.modeGrad_shift ξ hB σ y,
    cdotMat_phase _ (Complex.norm_exp_ofReal_mul_I _)]

theorem cnormSq_shift {A : ℝ → Space → (Space →L[ℝ] Space)} (hA : IsTimePeriodic A) (ξ : ℤ × ℤ) (σ : ℝ)
    (y : Space) : cnormSq (modeGrad ξ A σ y) = cnormSq (modeGrad ξ A 0 y) := by
  rw [FrequencySeminorm.Internal.modeGrad_shift ξ hA σ y, cnormSq_phase _ (Complex.norm_exp_ofReal_mul_I _)]

theorem sum_orth_pair {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (K : ι → κ → ℝ)
    (hK : ∀ p q, ∑ i, K i p * K i q = if p = q then 1 else 0) (x z : κ → ℂ) :
    ∑ i, (∑ p, (K i p : ℂ) * x p) * (starRingEnd ℂ) (∑ q, (K i q : ℂ) * z q) =
      ∑ p, x p * (starRingEnd ℂ) (z p) := by
  simp_rw [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  have e : ∀ q, ∑ i, (K i p : ℂ) * x p * ((K i q : ℂ) * (starRingEnd ℂ) (z q)) =
      ((∑ i, K i p * K i q : ℝ) : ℂ) * (x p * (starRingEnd ℂ) (z q)) := by
    intro q
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e, hK]
  simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem rot_transpose (ψ : ℝ) (j c : Fin 3) :
    axialRot (-ψ) (unitVector j) c = axialRot ψ (unitVector c) j := by
  fin_cases j <;> fin_cases c <;> simp [axialRot, unitVector]

theorem rot_orth (ψ : ℝ) (a b : Fin 3) :
    ∑ i : Fin 3, axialRot ψ (unitVector a) i * axialRot ψ (unitVector b) i = if a = b then 1 else 0 := by
  have h := Real.sin_sq_add_cos_sq ψ
  fin_cases a <;> fin_cases b <;> simp [axialRot, unitVector, Fin.sum_univ_three] <;> nlinarith [h]

theorem rot_pair_orth (ψ : ℝ) (p q : Fin 3 × Fin 3) :
    ∑ ij : Fin 3 × Fin 3, (axialRot ψ (unitVector p.1) ij.1 * axialRot ψ (unitVector p.2) ij.2) *
      (axialRot ψ (unitVector q.1) ij.1 * axialRot ψ (unitVector q.2) ij.2) = if p = q then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  have e : ∀ i j : Fin 3, (axialRot ψ (unitVector p.1) i * axialRot ψ (unitVector p.2) j) *
      (axialRot ψ (unitVector q.1) i * axialRot ψ (unitVector q.2) j) =
      (axialRot ψ (unitVector p.1) i * axialRot ψ (unitVector q.1) i) *
      (axialRot ψ (unitVector p.2) j * axialRot ψ (unitVector q.2) j) := fun i j => by ring
  simp_rw [e, ← Finset.mul_sum, ← Finset.sum_mul, rot_orth]
  obtain ⟨a, c⟩ := p
  obtain ⟨b, d⟩ := q
  by_cases hab : a = b <;> by_cases hcd : c = d <;> simp [hab, hcd]

theorem rotCMat_eq_sum (ψ : ℝ) (g : Fin 3 × Fin 3 → ℂ) (ij : Fin 3 × Fin 3) :
    rotCMat ψ g ij = ∑ p : Fin 3 × Fin 3,
      ((axialRot ψ (unitVector p.1) ij.1 * axialRot ψ (unitVector p.2) ij.2 : ℝ) : ℂ) * g p := by
  unfold rotCMat
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [rot_transpose]
  push_cast
  ring

theorem cdotMat_rot (ψ : ℝ) (x z : Fin 3 × Fin 3 → ℂ) :
    cdotMat (rotCMat ψ x) (rotCMat ψ z) = cdotMat x z := by
  unfold cdotMat
  simp_rw [rotCMat_eq_sum]
  have h := sum_orth_pair (fun ij p : Fin 3 × Fin 3 => axialRot ψ (unitVector p.1) ij.1 *
    axialRot ψ (unitVector p.2) ij.2) (rot_pair_orth ψ) x z
  beta_reduce at h
  rw [← h]

theorem pairDensity_rot {A B : ℝ → Space → (Space →L[ℝ] Space)} {z : ℝ × Space}
    (hA : Integrable (fun p : ℝ × ℝ => A (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (hB : Integrable (fun p : ℝ × ℝ => B (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) (ξ : ℤ × ℤ) (ψ : ℝ) :
    pairDensity ξ A B z.1 (axialRot ψ z.2) = pairDensity ξ A B z.1 z.2 := by
  unfold pairDensity
  rw [modeGrad_rotation_of axialRotationHolds_proof ξ ψ hA, modeGrad_rotation_of axialRotationHolds_proof ξ ψ hB,
    cdotMat_phase _ (Complex.norm_exp_ofReal_mul_I _), cdotMat_rot]

theorem abs_pair_le (x z : Fin 3 × Fin 3 → ℂ) : |(cdotMat x z).re| ≤ cnormSq x + cnormSq z := by
  unfold cdotMat cnormSq
  rw [← Finset.sum_add_distrib]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg (x i), norm_nonneg (z i), sq_nonneg (‖x i‖ - ‖z i‖)]

theorem flip_rot (φ : ℝ) (y : Space) : axialRot φ (flipPoint y) = flipPoint (axialRot (-φ) y) := by
  ext i
  fin_cases i <;> simp [axialRot, flipPoint, unitVector, add_comm]

theorem rot_unit_flip (φ : ℝ) (b : Fin 3) :
    axialRot φ (unitVector b) = frameSign b • flipPoint (axialRot (-φ) (unitVector b)) := by
  fin_cases b <;> ext i <;> fin_cases i <;> simp [axialRot, flipPoint, unitVector, frameSign]

theorem rot_smul_apply (φ c : ℝ) (X : Space) (a : Fin 3) : axialRot φ (c • X) a = c * axialRot φ X a := by
  rw [RotationInternal.axialRot_map_smul]
  rfl

open TailBand.Internal.FlipDecay in
theorem modeGrad_flip_of {B : ℝ → Space → (Space →L[ℝ] Space)}
    (hB : ∀ σ y a, B σ (flipPoint y) (flipPoint a) = flipPoint (B σ y a)) (ξ : ℤ × ℤ) (σ : ℝ) (y : Space)
    (ab : Fin 3 × Fin 3) :
    modeGrad (flipLabel ξ) B σ (flipPoint y) ab =
      ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ B σ y ab := by
  obtain ⟨a, b⟩ := ab
  set g : ℝ → ℝ → ℂ := fun τ φ => expFactor ξ τ φ *
    ((axialRot (-φ) (B (σ + τ) (axialRot φ y) (axialRot φ (unitVector b))) a : ℝ) : ℂ) with hg
  have hper : ∀ τ, Function.Periodic (g τ) (2 * Real.pi) := by
    intro τ φ
    simp only [hg, expFactor_add_period, axialRot_add_period, axialRot_neg_add_period]
  have hinner : ∀ τ, ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ (-φ) = ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ φ := by
    intro τ
    rw [intervalIntegral.integral_comp_neg, neg_zero]
    have h := (hper τ).intervalIntegral_add_eq (-(2 * Real.pi)) 0
    rw [neg_add_cancel, zero_add] at h
    exact h
  have hpt : ∀ τ φ, expFactor (flipLabel ξ) τ φ *
      ((axialRot (-φ) (B (σ + τ) (axialRot φ (flipPoint y)) (axialRot φ (unitVector b))) a : ℝ) : ℂ) =
      ((frameSign a * frameSign b : ℝ) : ℂ) * g τ (-φ) := by
    intro τ φ
    have he : expFactor (flipLabel ξ) τ φ = expFactor ξ τ (-φ) := by
      have h := expFactor_flip_neg ξ τ (-φ)
      rw [neg_neg] at h
      exact h
    rw [he, flip_rot, rot_unit_flip φ b, map_smul, hB, rot_smul_apply, rot_neg_flip]
    simp only [hg, neg_neg]
    push_cast
    ring
  unfold modeGrad
  rw [modeAverage_eq, modeAverage_eq]
  calc (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor (flipLabel ξ) τ φ * ((axialRot (-φ) (B (σ + τ) (axialRot φ (flipPoint y))
            (axialRot φ (unitVector b))) a : ℝ) : ℂ)
        = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1,
            ((frameSign a * frameSign b : ℝ) : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ (-φ) := by
          congr 1
          refine intervalIntegral.integral_congr fun τ _ => ?_
          rw [← intervalIntegral.integral_const_mul]
          exact intervalIntegral.integral_congr fun φ _ => hpt τ φ
      _ = ((frameSign a * frameSign b : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1,
            ∫ φ in (0 : ℝ)..(2 * Real.pi), g τ φ) := by
          simp_rw [hinner]
          rw [intervalIntegral.integral_const_mul]
          ring

theorem pairDensity_flip_of {A B : ℝ → Space → (Space →L[ℝ] Space)} {ξ : ℤ × ℤ} {σ : ℝ} {y : Space}
    (hA : modeGrad (flipLabel ξ) A σ (flipPoint y)
      = fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ A σ y ab)
    (hB : modeGrad (flipLabel ξ) B σ (flipPoint y)
      = fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ B σ y ab) :
    pairDensity (flipLabel ξ) A B σ (flipPoint y) = pairDensity ξ A B σ y := by
  unfold pairDensity cdotMat
  rw [hA, hB]
  congr 1
  refine Finset.sum_congr rfl fun ab _ => ?_
  have hs : (frameSign ab.1 * frameSign ab.2) * (frameSign ab.1 * frameSign ab.2) = 1 := by
    unfold frameSign
    split_ifs <;> norm_num
  have hc : ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) = 1 := by
    exact_mod_cast hs
  rw [map_mul, Complex.conj_ofReal]
  linear_combination (modeGrad ξ A σ y ab * (starRingEnd ℂ) (modeGrad ξ B σ y ab)) * hc


theorem ae_of_snd {Q : Space → Prop} (h : ∀ᵐ z : ℝ × Space, Q z.2) : ∀ᵐ y : Space, Q y := by
  rw [Measure.volume_eq_prod] at h
  obtain ⟨σ, hσ⟩ := (Measure.ae_ae_of_ae_prod h).exists
  exact hσ

theorem aesm_of_snd {f : Space → ℝ} (h : AEStronglyMeasurable (fun z : ℝ × Space => f z.2) volume) :
    AEStronglyMeasurable f volume := by
  rw [Measure.volume_eq_prod] at h
  obtain ⟨σ, hσ⟩ := h.prodMk_left.exists
  exact hσ

theorem aesm_pairDensity {A B : ℝ → Space → (Space →L[ℝ] Space)}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume) (ξ : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => pairDensity ξ A B z.1 z.2) volume := by
  unfold pairDensity cdotMat
  refine Complex.continuous_re.comp_aestronglyMeasurable ?_
  refine Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin 3 × Fin 3)) fun ij _ => ?_
  exact (Internal.FieldModes.aestronglyMeasurable_modeGrad hA ξ ij).mul
    (Complex.continuous_conj.comp_aestronglyMeasurable (Internal.FieldModes.aestronglyMeasurable_modeGrad hB ξ ij))

theorem aesm_pairDensity_zero {A B : ℝ → Space → (Space →L[ℝ] Space)}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume)
    (hAp : IsTimePeriodic A) (hBp : IsTimePeriodic B) (ξ : ℤ × ℤ) :
    AEStronglyMeasurable (fun y => pairDensity ξ A B 0 y) volume := by
  refine aesm_of_snd ((aesm_pairDensity hA hB ξ).congr (Filter.Eventually.of_forall fun z => ?_))
  exact pairDensity_shift hAp hBp ξ z.1 z.2

theorem aemeas_cnormSq_zero {A : ℝ → Space → (Space →L[ℝ] Space)}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume) (hAp : IsTimePeriodic A) (ξ : ℤ × ℤ) :
    AEMeasurable (fun y => ENNReal.ofReal (cnormSq (modeGrad ξ A 0 y))) volume := by
  have h : AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeGrad ξ A z.1 z.2)) volume := by
    unfold cnormSq
    exact Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin 3 × Fin 3)) fun ij _ =>
      ((Internal.FieldModes.aestronglyMeasurable_modeGrad hA ξ ij).norm).pow 2
  have h2 : AEStronglyMeasurable (fun y => cnormSq (modeGrad ξ A 0 y)) volume :=
    aesm_of_snd (h.congr (Filter.Eventually.of_forall fun z => cnormSq_shift hAp ξ z.1 z.2))
  exact h2.aemeasurable.ennreal_ofReal

theorem modeNorm_tsum_lt_top {A : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume) (hp : IsTimePeriodic A)
    (hf : periodLIntegral (fun σ y => matSq (A σ y)) < ⊤) :
    ∑' ξ : ℤ × ℤ, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ A 0 y)) < ⊤ := by
  have h := modeSquareSumHolds_proved.2.1 A hm hp hf
  have e : ∀ ξ : ℤ × ℤ, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ A σ y))) =
      ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ A 0 y)) := by
    intro ξ
    simp_rw [cnormSq_shift hp ξ]
    rw [setLIntegral_const, Real.volume_Icc]
    simp
  simp_rw [e] at h
  rw [← h]
  exact hf

theorem locallyIntegrable_of_squareSum {A : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume) (hp : IsTimePeriodic A)
    (hf : periodLIntegral (fun σ y => matSq (A σ y)) < ⊤) :
    LocallyIntegrable (fun z : ℝ × Space => A z.1 z.2) volume := by
  have hcol : ∀ i, LocallyIntegrable (fun z : ℝ × Space => ‖A z.1 z.2 (unitVector i)‖) volume :=
    fun i => Cert.Internal.CoerciveBordered.column_locallyIntegrable hm hp hf i
  have hs := locallyIntegrable_finsetSum Finset.univ fun i _ => hcol i
  refine hs.mono hm (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  exact Coercive.Internal.PerturbationFacts.opNorm_le_sum_apply _

def goodSet (A B : ℝ → Space → (Space →L[ℝ] Space)) : Set Space :=
  {y | ∀ (ξ : ℤ × ℤ) (φ : ℝ), pairDensity ξ A B 0 (axialRot φ y) = pairDensity ξ A B 0 y}

theorem goodSet_rot (A B : ℝ → Space → (Space →L[ℝ] Space)) (φ : ℝ) (y : Space) :
    axialRot φ y ∈ goodSet A B ↔ y ∈ goodSet A B := by
  have fwd : ∀ (ψ : ℝ) (w : Space), w ∈ goodSet A B → axialRot ψ w ∈ goodSet A B := by
    intro ψ w hw
    simp only [goodSet, Set.mem_ofPred_eq] at hw ⊢
    intro ξ φ'
    rw [← RotationInternal.axialRot_add, hw ξ (φ' + ψ), hw ξ ψ]
  refine ⟨fun h => ?_, fwd φ y⟩
  have h' := fwd (-φ) _ h
  rwa [RotationInternal.axialRot_neg_self] at h'

theorem ae_goodSet {A B : ℝ → Space → (Space →L[ℝ] Space)} (hAp : IsTimePeriodic A) (hBp : IsTimePeriodic B)
    (hAl : LocallyIntegrable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hBl : LocallyIntegrable (fun z : ℝ × Space => B z.1 z.2) volume) :
    ∀ᵐ y, y ∈ goodSet A B := by
  refine ae_of_snd ?_
  filter_upwards [ae_integrable_orbit axialRotationHolds_proof hAl,
    ae_integrable_orbit axialRotationHolds_proof hBl] with z hA hB
  simp only [goodSet, Set.mem_ofPred_eq]
  intro ξ φ
  rw [← pairDensity_shift hAp hBp ξ z.1 (axialRot φ z.2), ← pairDensity_shift hAp hBp ξ z.1 z.2]
  exact pairDensity_rot hA hB ξ φ

open CellCert.CellAnalysis.LowEntry.Internal (cylArg) in
theorem aesm_plane {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) (S : Set Space)
    (hSr : ∀ φ y, axialRot φ y ∈ S ↔ y ∈ S) (hSa : ∀ᵐ y, y ∈ S)
    (hrot : ∀ φ, ∀ y ∈ S, f (axialRot φ y) = f y) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f (planePoint p)) volume := by
  have hq := CellCert.CellAnalysis.CylinderCompInternal.qmp_full
  have h1 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => f (cylArg q)) volume :=
    hf.comp_quasiMeasurePreserving hq
  have h2 : ∀ᵐ q : (ℝ × ℝ) × ℝ, f (cylArg q) = f (planePoint q.1) := by
    filter_upwards [hq.ae hSa] with q hqS
    have e : cylArg q = axialRot q.2 (planePoint q.1) := TailBand.Internal.FlipDecay.cylArg_eq q.1 q.2
    rw [e] at hqS ⊢
    exact hrot q.2 _ ((hSr q.2 _).1 hqS)
  have h3 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => f (planePoint q.1))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact h1.congr h2
  obtain ⟨θ, hθ⟩ := h3.prod_swap.prodMk_left.exists
  exact hθ

theorem lattice_flip (hL : LabelArithmeticHolds) {m : ℕ} (hm : 1 ≤ m) (ξ : ℤ × ℤ) :
    IsLatticeHarmonic m (flipLabel ξ) ↔ IsLatticeHarmonic m ξ := by
  have hf := (hL m hm).2.1
  have hinv : ∀ ζ : ℤ × ℤ, flipLabel (flipLabel ζ) = ζ := fun ζ => by simp [flipLabel]
  constructor
  · rintro ⟨ι, hι⟩
    exact ⟨labelFlip ι, by rw [hf, hι, hinv]⟩
  · rintro ⟨ι, hι⟩
    exact ⟨labelFlip ι, by rw [hf, hι]⟩

open Classical in
def latticePart (m : ℕ) (A B : ℝ → Space → (Space →L[ℝ] Space)) (ξ : ℤ × ℤ) (y : Space) : ℝ :=
  if IsLatticeHarmonic m ξ then pairDensity ξ A B 0 y else 0

theorem ofReal_abs_eq (a : ℝ) : ENNReal.ofReal |a| = ENNReal.ofReal a + ENNReal.ofReal (-a) := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -a ≤ 0), add_zero]
  · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]

theorem lint_identity (hH : HalfPlaneReductionHolds) (k : ℤ × ℤ → Space → ℝ)
    (hm : ∀ ξ, AEStronglyMeasurable (k ξ) volume) (S : Set Space)
    (hSr : ∀ φ y, axialRot φ y ∈ S ↔ y ∈ S) (hSa : ∀ᵐ y, y ∈ S)
    (hrot : ∀ ξ φ, ∀ y ∈ S, k ξ (axialRot φ y) = k ξ y)
    (hflip : ∀ ξ, ∀ᵐ y, k (flipLabel ξ) (flipPoint y) = k ξ y) :
    ∑' ξ, ∫⁻ y, ENNReal.ofReal (k ξ y) = ENNReal.ofReal (4 * Real.pi) *
      ∑' ξ, ∫⁻ p in halfPlane, ENNReal.ofReal (k ξ (planePoint p)) * ENNReal.ofReal p.1 := by
  have hmeas : ∀ ξ, AEMeasurable (fun y => ENNReal.ofReal (k ξ y)) volume :=
    fun ξ => (hm ξ).aemeasurable.ennreal_ofReal
  rw [← lintegral_tsum hmeas]
  refine hH (fun ξ y => ENNReal.ofReal (k ξ y)) hmeas S hSr hSa ?_ ?_
  · intro ξ φ y hy
    simp only [hrot ξ φ y hy]
  · intro ξ
    filter_upwards [hflip ξ] with y hy
    simp only [hy]

theorem measurableSet_halfPlane : MeasurableSet halfPlane := by
  unfold halfPlane
  exact measurableSet_Ioi.prod measurableSet_Ioi

theorem signed_reduction (hH : HalfPlaneReductionHolds) (h : ℤ × ℤ → Space → ℝ)
    (hm : ∀ ξ, AEStronglyMeasurable (h ξ) volume) (S : Set Space)
    (hSr : ∀ φ y, axialRot φ y ∈ S ↔ y ∈ S) (hSa : ∀ᵐ y, y ∈ S)
    (hrot : ∀ ξ φ, ∀ y ∈ S, h ξ (axialRot φ y) = h ξ y)
    (hflip : ∀ ξ, ∀ᵐ y, h (flipLabel ξ) (flipPoint y) = h ξ y)
    (hfin : ∑' ξ, ∫⁻ y, ENNReal.ofReal |h ξ y| < ⊤)
    (hhp : ∀ ξ, AEStronglyMeasurable (fun p : ℝ × ℝ => h ξ (planePoint p)) (volume.restrict halfPlane)) :
    ∑' ξ, ∫ y, h ξ y = 4 * Real.pi * ∑' ξ, ∫ p in halfPlane, h ξ (planePoint p) * p.1 := by
  have hA := lint_identity hH h hm S hSr hSa hrot hflip
  have hB := lint_identity hH (fun ξ y => -h ξ y) (fun ξ => (hm ξ).neg) S hSr hSa
    (fun ξ φ y hy => by simp only [hrot ξ φ y hy]) (fun ξ => by
      filter_upwards [hflip ξ] with y hy
      simp only [hy])
  beta_reduce at hB
  set a : ℤ × ℤ → ℝ≥0∞ := fun ξ => ∫⁻ y, ENNReal.ofReal (h ξ y) with ha
  set b : ℤ × ℤ → ℝ≥0∞ := fun ξ => ∫⁻ y, ENNReal.ofReal (-h ξ y) with hb
  set a' : ℤ × ℤ → ℝ≥0∞ := fun ξ => ∫⁻ p in halfPlane, ENNReal.ofReal (h ξ (planePoint p)) * ENNReal.ofReal p.1
    with ha'
  set b' : ℤ × ℤ → ℝ≥0∞ := fun ξ => ∫⁻ p in halfPlane, ENNReal.ofReal (-h ξ (planePoint p)) * ENNReal.ofReal p.1
    with hb'
  have habs : ∀ ξ, ∫⁻ y, ENNReal.ofReal |h ξ y| = a ξ + b ξ := by
    intro ξ
    simp only [ha, hb, ofReal_abs_eq]
    exact lintegral_add_left' (hm ξ).aemeasurable.ennreal_ofReal _
  have hsum : ∑' ξ, (a ξ + b ξ) < ⊤ := by
    simp_rw [← habs]
    exact hfin
  rw [ENNReal.tsum_add] at hsum
  have haT : ∑' ξ, a ξ ≠ ⊤ := (ENNReal.add_lt_top.1 hsum).1.ne
  have hbT : ∑' ξ, b ξ ≠ ⊤ := (ENNReal.add_lt_top.1 hsum).2.ne
  have h4 : ENNReal.ofReal (4 * Real.pi) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have ha'T : ∑' ξ, a' ξ ≠ ⊤ := by
    intro hT
    apply haT
    rw [hA, hT, ENNReal.mul_top h4]
  have hb'T : ∑' ξ, b' ξ ≠ ⊤ := by
    intro hT
    apply hbT
    rw [hB, hT, ENNReal.mul_top h4]
  have haf : ∀ ξ, a ξ ≠ ⊤ := fun ξ => ne_top_of_le_ne_top haT (ENNReal.le_tsum ξ)
  have hbf : ∀ ξ, b ξ ≠ ⊤ := fun ξ => ne_top_of_le_ne_top hbT (ENNReal.le_tsum ξ)
  have ha'f : ∀ ξ, a' ξ ≠ ⊤ := fun ξ => ne_top_of_le_ne_top ha'T (ENNReal.le_tsum ξ)
  have hb'f : ∀ ξ, b' ξ ≠ ⊤ := fun ξ => ne_top_of_le_ne_top hb'T (ENNReal.le_tsum ξ)
  have hint : ∀ ξ, ∫ y, h ξ y = (a ξ).toReal - (b ξ).toReal := by
    intro ξ
    refine integral_eq_lintegral_pos_part_sub_lintegral_neg_part ⟨hm ξ, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal_abs]
    rw [habs]
    exact ENNReal.add_lt_top.2 ⟨(haf ξ).lt_top, (hbf ξ).lt_top⟩
  have hpos : ∀ ξ, ∀ p ∈ halfPlane, ENNReal.ofReal (h ξ (planePoint p) * p.1) =
      ENNReal.ofReal (h ξ (planePoint p)) * ENNReal.ofReal p.1 := by
    intro ξ p hp
    exact ENNReal.ofReal_mul' (le_of_lt hp.1)
  have hneg : ∀ ξ, ∀ p ∈ halfPlane, ENNReal.ofReal (-(h ξ (planePoint p) * p.1)) =
      ENNReal.ofReal (-h ξ (planePoint p)) * ENNReal.ofReal p.1 := by
    intro ξ p hp
    rw [← ENNReal.ofReal_mul' (le_of_lt hp.1), neg_mul]
  have hhint : ∀ ξ, ∫ p in halfPlane, h ξ (planePoint p) * p.1 = (a' ξ).toReal - (b' ξ).toReal := by
    intro ξ
    have hm' : AEStronglyMeasurable (fun p : ℝ × ℝ => h ξ (planePoint p) * p.1) (volume.restrict halfPlane) :=
      (hhp ξ).mul continuous_fst.aestronglyMeasurable
    have hfi : HasFiniteIntegral (fun p : ℝ × ℝ => h ξ (planePoint p) * p.1) (volume.restrict halfPlane) := by
      rw [hasFiniteIntegral_iff_enorm]
      have e : ∫⁻ p in halfPlane, ‖h ξ (planePoint p) * p.1‖ₑ = a' ξ + b' ξ := by
        have hmA : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (h ξ (planePoint p)) * ENNReal.ofReal p.1)
            (volume.restrict halfPlane) :=
          ((hhp ξ).aemeasurable.ennreal_ofReal).mul continuous_fst.measurable.ennreal_ofReal.aemeasurable
        rw [ha', hb']
        dsimp only
        rw [← lintegral_add_left' hmA]
        refine setLIntegral_congr_fun measurableSet_halfPlane fun p hp => ?_
        rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (a := p.1) hp.1, ENNReal.ofReal_mul' (le_of_lt hp.1),
          ofReal_abs_eq, add_mul]
      rw [e]
      exact ENNReal.add_lt_top.2 ⟨(ha'f ξ).lt_top, (hb'f ξ).lt_top⟩
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part ⟨hm', hfi⟩,
      setLIntegral_congr_fun measurableSet_halfPlane (hpos ξ),
      setLIntegral_congr_fun measurableSet_halfPlane (hneg ξ)]
  simp_rw [hint, hhint]
  rw [(ENNReal.summable_toReal haT).tsum_sub (ENNReal.summable_toReal hbT),
    (ENNReal.summable_toReal ha'T).tsum_sub (ENNReal.summable_toReal hb'T),
    ← ENNReal.tsum_toReal_eq haf, ← ENNReal.tsum_toReal_eq hbf, ← ENNReal.tsum_toReal_eq ha'f,
    ← ENNReal.tsum_toReal_eq hb'f, hA, hB, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  ring

theorem ae_pairDensity_flip (hX : ModeFlipHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hfl : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) {B : ℝ → Space → (Space →L[ℝ] Space)}
    (hBp : IsTimePeriodic B) (hB : ∀ σ y a, B σ (flipPoint y) (flipPoint a) = flipPoint (B σ y a))
    (ξ : ℤ × ℤ) : ∀ᵐ y, pairDensity (flipLabel ξ) G B 0 (flipPoint y) = pairDensity ξ G B 0 y := by
  refine ae_of_snd ?_
  filter_upwards [hX Γ P v G H g hv hfl ξ] with z hz
  rw [← pairDensity_shift hv.periodic_gradient hBp (flipLabel ξ) z.1 (flipPoint z.2),
    ← pairDensity_shift hv.periodic_gradient hBp ξ z.1 z.2]
  exact pairDensity_flip_of hz.2.1 (funext fun ab => modeGrad_flip_of hB ξ z.1 z.2 ab)

theorem ae_pairDensity_zero (hC : ClassSupportHolds) {Γ : Set Symmetry} {m : ℕ} (hclass : IsModeClass Γ m)
    {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {B : ℝ → Space → (Space →L[ℝ] Space)} (hBp : IsTimePeriodic B)
    (ξ : ℤ × ℤ) (hξ : ¬ IsLatticeHarmonic m ξ) : ∀ᵐ y, pairDensity ξ G B 0 y = 0 := by
  refine ae_of_snd ?_
  filter_upwards [hC Γ m P v G H g hclass hv ξ hξ] with z hz
  rw [← pairDensity_shift hv.periodic_gradient hBp ξ z.1 z.2]
  unfold pairDensity cdotMat
  rw [hz.2.1]
  simp

theorem term_eq {A B : ℝ → Space → (Space →L[ℝ] Space)} (hAp : IsTimePeriodic A) (hBp : IsTimePeriodic B)
    (ξ : ℤ × ℤ) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdotMat (modeGrad ξ A σ y) (modeGrad ξ B σ y)).re =
      ∫ y, pairDensity ξ A B 0 y := by
  have e : ∀ σ, ∫ y, (cdotMat (modeGrad ξ A σ y) (modeGrad ξ B σ y)).re = ∫ y, pairDensity ξ A B 0 y := by
    intro σ
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact pairDensity_shift hAp hBp ξ σ y
  simp only [e]
  rw [setIntegral_const]
  simp

theorem pin_identity (hP : PairingModeIdentityHolds) (hH : HalfPlaneReductionHolds) (hC : ClassSupportHolds)
    (hL : LabelArithmeticHolds) (hX : ModeFlipHolds) {Γ : Set Symmetry} {m : ℕ} (hclass : IsModeClass Γ m)
    {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {B : ℝ → Space → (Space →L[ℝ] Space)}
    (hBm : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume) (hBp : IsTimePeriodic B)
    (hBf : periodLIntegral (fun σ y => matSq (B σ y)) < ⊤)
    (hBflip : ∀ σ y a, B σ (flipPoint y) (flipPoint a) = flipPoint (B σ y a)) :
    pinValue B G = 4 * Real.pi * ∑' ι : ℤ × ℤ, ∫ p in halfPlane,
      (cdotMat (labelGrad m ι G p) (labelGrad m ι B p)).re * p.1 := by
  have hGp := hv.periodic_gradient
  have hGm := hv.measurable_gradient
  have hGf := hv.gradient_finite
  have hlat : ∀ ξ, ¬ IsLatticeHarmonic m ξ → latticePart m G B ξ = fun _ => 0 := by
    intro ξ hξ
    funext y
    simp [latticePart, hξ]
  have hon : ∀ ξ, IsLatticeHarmonic m ξ → latticePart m G B ξ = fun y => pairDensity ξ G B 0 y := by
    intro ξ hξ
    funext y
    simp [latticePart, hξ]
  have step1 : pinValue B G = ∑' ξ, ∫ y, latticePart m G B ξ y := by
    unfold pinValue
    rw [(hP G B hGm hBm hGp hBp hGf hBf).2]
    congr 1
    funext ξ
    rw [term_eq hGp hBp ξ]
    by_cases hξ : IsLatticeHarmonic m ξ
    · rw [hon ξ hξ]
    · rw [hlat ξ hξ, integral_eq_zero_of_ae (ae_pairDensity_zero hC hclass hv hBp ξ hξ)]
      simp
  have hm : ∀ ξ, AEStronglyMeasurable (latticePart m G B ξ) volume := by
    intro ξ
    by_cases hξ : IsLatticeHarmonic m ξ
    · rw [hon ξ hξ]
      exact aesm_pairDensity_zero hGm hBm hGp hBp ξ
    · rw [hlat ξ hξ]
      exact aestronglyMeasurable_const
  have hSa := ae_goodSet hGp hBp (locallyIntegrable_of_squareSum hGm hGp hGf) (locallyIntegrable_of_squareSum hBm hBp hBf)
  have hrot : ∀ ξ φ, ∀ y ∈ goodSet G B, latticePart m G B ξ (axialRot φ y) = latticePart m G B ξ y := by
    intro ξ φ y hy
    by_cases hξ : IsLatticeHarmonic m ξ
    · rw [hon ξ hξ]
      exact hy ξ φ
    · rw [hlat ξ hξ]
  have hflip : ∀ ξ, ∀ᵐ y, latticePart m G B (flipLabel ξ) (flipPoint y) = latticePart m G B ξ y := by
    intro ξ
    by_cases hξ : IsLatticeHarmonic m ξ
    · have hξ' : IsLatticeHarmonic m (flipLabel ξ) := (lattice_flip hL hclass.order_pos ξ).2 hξ
      rw [hon ξ hξ, hon _ hξ']
      exact ae_pairDensity_flip hX hv hclass.flip hBp hBflip ξ
    · have hξ' : ¬ IsLatticeHarmonic m (flipLabel ξ) := fun h => hξ ((lattice_flip hL hclass.order_pos ξ).1 h)
      rw [hlat ξ hξ, hlat _ hξ']
      exact Filter.Eventually.of_forall fun _ => rfl
  have hfin : ∑' ξ, ∫⁻ y, ENNReal.ofReal |latticePart m G B ξ y| < ⊤ := by
    have hle : ∀ ξ, ∫⁻ y, ENNReal.ofReal |latticePart m G B ξ y| ≤
        (∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ G 0 y))) + ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ B 0 y)) := by
      intro ξ
      rw [← lintegral_add_left' (aemeas_cnormSq_zero hGm hGp ξ)]
      refine lintegral_mono fun y => ?_
      rw [← ENNReal.ofReal_add (Internal.FieldModes.cnormSq_nonneg _) (Internal.FieldModes.cnormSq_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hξ : IsLatticeHarmonic m ξ
      · rw [hon ξ hξ]
        exact abs_pair_le _ _
      · rw [hlat ξ hξ, abs_zero]
        exact add_nonneg (Internal.FieldModes.cnormSq_nonneg _) (Internal.FieldModes.cnormSq_nonneg _)
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_
    rw [ENNReal.tsum_add]
    exact ENNReal.add_lt_top.2 ⟨modeNorm_tsum_lt_top hGm hGp hGf, modeNorm_tsum_lt_top hBm hBp hBf⟩
  have hhp : ∀ ξ, AEStronglyMeasurable (fun p : ℝ × ℝ => latticePart m G B ξ (planePoint p))
      (volume.restrict halfPlane) :=
    fun ξ => (aesm_plane (hm ξ) (goodSet G B) (goodSet_rot G B) hSa (hrot ξ)).restrict
  have step2 := signed_reduction hH (latticePart m G B) hm (goodSet G B) (goodSet_rot G B) hSa hrot hflip
    hfin hhp
  have hinj := (hL m hclass.order_pos).1
  have step3 : ∑' ξ, ∫ p in halfPlane, latticePart m G B ξ (planePoint p) * p.1 =
      ∑' ι : ℤ × ℤ, ∫ p in halfPlane, (cdotMat (labelGrad m ι G p) (labelGrad m ι B p)).re * p.1 := by
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun ι => ?_
      rw [hon _ ⟨ι, rfl⟩]
      rfl
    · intro ξ hξ
      by_contra hr
      apply hξ
      have hnl : ¬ IsLatticeHarmonic m ξ := fun ⟨ι, hι⟩ => hr ⟨ι, hι⟩
      simp only [hlat ξ hnl, zero_mul, integral_zero]
  rw [step1, step2, step3]

end Internal.PinHalf

open Internal.PinHalf in
theorem pinHalfPlane (hP : PairingModeIdentityHolds) (hH : HalfPlaneReductionHolds) (hC : ClassSupportHolds)
    (hL : LabelArithmeticHolds) (hS : ModeShiftRotateTensorHolds) (hX : ModeFlipHolds) : PinHalfPlaneHolds := by
  have _ := hS
  intro k C nE nM D hclass hinv hmeas hper hfin P v G H g hv i
  obtain ⟨γ, hγ, hγ1, hγ2⟩ := hclass.flip
  have hflipB : ∀ σ y a, D.cert.pin i σ (flipPoint y) (flipPoint a) = flipPoint (D.cert.pin i σ y a) := by
    intro σ y a
    have h := hinv i γ hγ σ y a
    rwa [hγ2, add_zero, hγ1, hγ1, hγ1] at h
  exact pin_identity hP hH hC hL hX hclass hv (hmeas i) (hper i) (hfin i) hflipB

end Bridge

end CertCell

end Breakdown
