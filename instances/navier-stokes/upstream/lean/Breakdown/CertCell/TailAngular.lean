import Breakdown.CertCell.TailStatements
import Breakdown.Cert.CoerciveGain
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveRotation

open scoped Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

def AngularModePointwise : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → 0 < P → ∀ ι : ℤ × ℤ,
    ∀ᵐ z : ℝ × Space, AngularRelations |(ι.2 : ℝ)| (cylRadius z.2)
      (Real.sqrt (cnormSq (modeSecondDeriv ι H z.1 z.2))) (Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H z.1 z.2))))
      (Real.sqrt (cnormSq (modeGrad ι G z.1 z.2))) (Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))))
      (Real.sqrt (cnormSq (modeVel ι v z.1 z.2)))

namespace Internal

open Coercive Coercive.GainInternal

private theorem sqrt_cnormSq_eq {β : Type*} [Fintype β] (x : β → ℂ) :
    Real.sqrt (cnormSq x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ β)‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

private theorem lower_of_identity {β : Type*} [Fintype β] (w u Bw : β → ℂ) (k c : ℝ) (hc : 0 ≤ c)
    (hB : cnormSq Bw ≤ c ^ 2 * cnormSq w) (hid : ∀ b, u b = (k : ℂ) * Complex.I * w b + Bw b) :
    (|k| - c) * Real.sqrt (cnormSq w) ≤ Real.sqrt (cnormSq u) := by
  have hBn : ‖(WithLp.toLp 2 Bw : EuclideanSpace ℂ β)‖ ≤ c * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ β)‖ := by
    have h := Real.sqrt_le_sqrt hB
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc, sqrt_cnormSq_eq, sqrt_cnormSq_eq] at h
    exact h
  have hu : (WithLp.toLp 2 u : EuclideanSpace ℂ β)
      = ((k : ℂ) * Complex.I) • (WithLp.toLp 2 w : EuclideanSpace ℂ β) + WithLp.toLp 2 Bw := by
    rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
    congr 1
    funext b
    simp [hid b]
  have h1 := norm_sub_norm_le (((k : ℂ) * Complex.I) • (WithLp.toLp 2 w : EuclideanSpace ℂ β))
    (-(WithLp.toLp 2 Bw : EuclideanSpace ℂ β))
  rw [sub_neg_eq_add, norm_neg, norm_smul, ← hu] at h1
  have hk : ‖(k : ℂ) * Complex.I‖ = |k| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hk] at h1
  rw [sqrt_cnormSq_eq, sqrt_cnormSq_eq]
  linarith

private theorem contract_le {β : Type*} [Fintype β] (g : β → Fin 3 → ℂ) (y : Space) :
    Real.sqrt (cnormSq (fun b => ∑ j, g b j * (azimuthalField y j : ℂ)))
      ≤ cylRadius y * Real.sqrt (∑ b, ∑ j, ‖g b j‖ ^ 2) := by
  have hrow : ∀ b, ‖∑ j, g b j * (azimuthalField y j : ℂ)‖ ^ 2 ≤ (∑ j, ‖g b j‖ ^ 2) * cylRadius y ^ 2 := by
    intro b
    have h1 : ‖∑ j, g b j * (azimuthalField y j : ℂ)‖ ≤ ∑ j, ‖g b j‖ * |azimuthalField y j| := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖g b j‖) (fun j => |azimuthalField y j|)
    simp only [sq_abs] at h2
    rw [azimuthalField_sq y] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hle : cnormSq (fun b => ∑ j, g b j * (azimuthalField y j : ℂ))
      ≤ cylRadius y ^ 2 * ∑ b, ∑ j, ‖g b j‖ ^ 2 := by
    rw [cnormSq, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => (hrow b).trans (le_of_eq (mul_comm _ _))
  have hr : 0 ≤ cylRadius y := Real.sqrt_nonneg _
  calc Real.sqrt (cnormSq (fun b => ∑ j, g b j * (azimuthalField y j : ℂ)))
      ≤ Real.sqrt (cylRadius y ^ 2 * ∑ b, ∑ j, ‖g b j‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = cylRadius y * Real.sqrt (∑ b, ∑ j, ‖g b j‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr]

private theorem gain_max {β : Type*} [Fintype β] (w : β → ℂ) (g : β → Fin 3 → ℂ) (Bw : β → ℂ)
    (y : Space) (k c : ℝ) (hc : 0 ≤ c) (hB : cnormSq Bw ≤ c ^ 2 * cnormSq w)
    (hid : ∀ b, ∑ j, g b j * (azimuthalField y j : ℂ) = (k : ℂ) * Complex.I * w b + Bw b) :
    max (|k| - c) 0 * Real.sqrt (cnormSq w) ≤ cylRadius y * Real.sqrt (∑ b, ∑ j, ‖g b j‖ ^ 2) := by
  rcases le_total (|k| - c) 0 with h | h
  · rw [max_eq_right h, zero_mul]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · rw [max_eq_left h]
    exact (lower_of_identity w (fun b => ∑ j, g b j * (azimuthalField y j : ℂ)) Bw k c hc hB hid).trans
      (contract_le g y)

private theorem sq_norm_sub_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have h0 := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

private theorem curlOfGrad_zero (g : Fin 3 × Fin 3 → ℂ) : curlOfGrad g 0 = g (2, 1) - g (1, 2) := by
  simp [curlOfGrad, alternatingSymbol, Fin.sum_univ_three]
  ring

private theorem curlOfGrad_one (g : Fin 3 × Fin 3 → ℂ) : curlOfGrad g 1 = g (0, 2) - g (2, 0) := by
  simp [curlOfGrad, alternatingSymbol, Fin.sum_univ_three]
  ring

private theorem curlOfGrad_two (g : Fin 3 × Fin 3 → ℂ) : curlOfGrad g 2 = g (1, 0) - g (0, 1) := by
  simp [curlOfGrad, alternatingSymbol, Fin.sum_univ_three]
  ring

private theorem cnormSq_curlOfGrad_le (g : Fin 3 × Fin 3 → ℂ) :
    cnormSq (curlOfGrad g) ≤ 2 * cnormSq g := by
  have e : cnormSq (curlOfGrad g) = ‖g (2, 1) - g (1, 2)‖ ^ 2 + ‖g (0, 2) - g (2, 0)‖ ^ 2
      + ‖g (1, 0) - g (0, 1)‖ ^ 2 := by
    rw [cnormSq, Fin.sum_univ_three, curlOfGrad_zero, curlOfGrad_one, curlOfGrad_two]
  have f : cnormSq g = ∑ i : Fin 3, ∑ j : Fin 3, ‖g (i, j)‖ ^ 2 := by
    rw [cnormSq, Fintype.sum_prod_type]
  rw [e, f]
  simp only [Fin.sum_univ_three]
  have hn : ∀ i j, 0 ≤ ‖g (i, j)‖ ^ 2 := fun _ _ => sq_nonneg _
  nlinarith [sq_norm_sub_le (g (2, 1)) (g (1, 2)), sq_norm_sub_le (g (0, 2)) (g (2, 0)),
    sq_norm_sub_le (g (1, 0)) (g (0, 1)), hn 0 0, hn 1 1, hn 2 2]

private def pairGen (b c : Fin 3 × Fin 3) : ℂ :=
  ((azimuthalField (unitVector c.1) b.1 : ℝ) : ℂ) * (if b.2 = c.2 then 1 else 0)
    + (if b.1 = c.1 then 1 else 0) * ((-azimuthalField (unitVector b.2) c.2 : ℝ) : ℂ)

private def vecGen (b c : Fin 3) : ℂ := ((azimuthalField (unitVector c) b : ℝ) : ℂ)

private theorem curl_identity (M : Fin 3 × Fin 3 → ℂ) (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ)
    (k : ℂ) (hid : ∀ b : Fin 3 × Fin 3, ∑ j, h (b.1, j, b.2) * a j = k * M b + ∑ c, pairGen b c * M c) (i : Fin 3) :
    ∑ l, curlGradOfSecondDeriv h (i, l) * a l = k * curlOfGrad M i + ∑ c, vecGen i c * curlOfGrad M c := by
  have h21 := hid (2, 1)
  have h12 := hid (1, 2)
  have h02 := hid (0, 2)
  have h20 := hid (2, 0)
  have h10 := hid (1, 0)
  have h01 := hid (0, 1)
  simp only [pairGen, Fintype.sum_prod_type, Fin.sum_univ_three] at h21 h12 h02 h20 h10 h01
  simp [azimuthalField, unitVector] at h21 h12 h02 h20 h10 h01
  simp only [Fin.sum_univ_three, vecGen, curlOfGrad_zero, curlOfGrad_one, curlOfGrad_two]
  simp [curlGradOfSecondDeriv, alternatingSymbol, azimuthalField, unitVector, Fin.sum_univ_three]
  fin_cases i
  · simp [curlOfGrad_zero]
    linear_combination h21 - h12
  · simp [curlOfGrad_one]
    linear_combination h02 - h20
  · simp [curlOfGrad_two]
    linear_combination h10 - h01

end Internal

open Coercive Coercive.GainInternal Internal in
theorem angularModePointwise_of (hD : Coercive.ModeDerivativeHolds) (hR : Coercive.ModeRotationHolds) :
    AngularModePointwise := by
  intro Γ P v G H g hv _ ι
  have hRot := axialRotationHolds_proof
  obtain ⟨hD1, hD2, -⟩ := hD Γ P v G H g hv ι
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsdef
  have hs0 : ∀ n, s n ≠ 0 := fun n => by positivity
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hR1 := Measure.ae_ae_of_ae_prod (ae_all_iff.2 (fun n => (hR Γ P v G H g hv ι (s n)).1))
  have hR2 := Measure.ae_ae_of_ae_prod (ae_all_iff.2 (fun n => (hR Γ P v G H g hv ι (s n)).2))
  have hslice : ∀ᵐ σ, ∀ᵐ y,
      max (|(ι.2 : ℝ)| - 1) 0 * Real.sqrt (cnormSq (modeVel ι v σ y))
          ≤ cylRadius y * Real.sqrt (cnormSq (modeGrad ι G σ y)) ∧
        max (|(ι.2 : ℝ)| - 2) 0 * Real.sqrt (cnormSq (modeGrad ι G σ y))
          ≤ cylRadius y * Real.sqrt (cnormSq (modeSecondDeriv ι H σ y)) ∧
        max (|(ι.2 : ℝ)| - 1) 0 * Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G σ y)))
          ≤ cylRadius y * Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))) := by
    filter_upwards [hD1, hD2, hR1, hR2] with σ h1 h2 h3 h4
    obtain ⟨hw1, hg1, hweak1⟩ := weak_components (fun y => modeVel ι v σ y)
      (fun y => modeGrad ι G σ y) h1.1 h1.2
    have hc2 := fun l => weak_components (fun y i => modeGrad ι G σ y (i, l))
      (fun y ij => modeSecondDeriv ι H σ y (ij.1, ij.2, l)) (h2 l).1 (h2 l).2
    have hid1 := angular_identity hRot (fun y => modeVel ι v σ y) (fun y b j => modeGrad ι G σ y (b, j))
      (ι.2 : ℝ) (fun ψ b c => ((axialRot ψ (unitVector c) b : ℝ) : ℂ))
      (fun b c => ((azimuthalField (unitVector c) b : ℝ) : ℂ)) hw1 (fun b j => hg1 b j)
      (fun φ hφ b j => hweak1 φ hφ b j)
      (fun b c => by simp only [unit_apply hRot]; split_ifs <;> simp)
      (fun b c => (hasDerivAt_axialRot (unitVector c) b).ofReal_comp) s hs0 hs
      (fun n => by
        filter_upwards [h3] with y hy b
        have := congrFun (hy n) b
        simpa [rotC] using this)
    have hid2 := angular_identity hRot (β := Fin 3 × Fin 3) (fun y => modeGrad ι G σ y)
      (fun y b j => modeSecondDeriv ι H σ y (b.1, j, b.2)) (ι.2 : ℝ)
      (fun ψ b c => ((axialRot ψ (unitVector c.1) b.1 : ℝ) : ℂ) * ((axialRot (-ψ) (unitVector b.2) c.2 : ℝ) : ℂ))
      pairGen
      (fun b => (hc2 b.2).1 b.1) (fun b j => (hc2 b.2).2.1 b.1 j)
      (fun φ hφ b j => (hc2 b.2).2.2 φ hφ b.1 j)
      (fun b c => by
        have e2 : axialRot (-0) (unitVector b.2) c.2 = if b.2 = c.2 then 1 else 0 := by
          rw [neg_zero, unit_apply hRot]; exact if_congr eq_comm rfl rfl
        rw [unit_apply hRot, e2]
        obtain ⟨b1, b2⟩ := b
        obtain ⟨c1, c2⟩ := c
        by_cases h1 : b1 = c1 <;> by_cases h2 : b2 = c2 <;> simp [h1, h2, Prod.ext_iff])
      (fun b c => by
        have d1 := (hasDerivAt_axialRot (unitVector c.1) b.1).ofReal_comp
        have d2 := (hasDerivAt_axialRot_neg (unitVector b.2) c.2).ofReal_comp
        have e1 : ((axialRot 0 (unitVector c.1) b.1 : ℝ) : ℂ) = if b.1 = c.1 then 1 else 0 := by
          rw [unit_apply hRot]; split_ifs <;> simp
        have e2 : ((axialRot (-0) (unitVector b.2) c.2 : ℝ) : ℂ) = if b.2 = c.2 then 1 else 0 := by
          rw [neg_zero, unit_apply hRot, if_congr eq_comm rfl rfl]; split_ifs <;> simp
        have := d1.mul d2
        rw [e1, e2] at this
        unfold pairGen
        exact this)
      s hs0 hs
      (fun n => by
        filter_upwards [h4] with y hy b
        have := congrFun (hy n) b
        rw [this]
        simp only [rotCMat, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        ring)
    filter_upwards [hid1, hid2] with y hy1 hy2
    have eG : ∑ b : Fin 3, ∑ j : Fin 3, ‖modeGrad ι G σ y (b, j)‖ ^ 2 = cnormSq (modeGrad ι G σ y) := by
      rw [cnormSq, Fintype.sum_prod_type]
    have eH : ∑ b : Fin 3 × Fin 3, ∑ j : Fin 3, ‖modeSecondDeriv ι H σ y (b.1, j, b.2)‖ ^ 2
        = cnormSq (modeSecondDeriv ι H σ y) := by
      simp only [cnormSq, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    have eC : ∑ b : Fin 3, ∑ j : Fin 3, ‖curlGradOfSecondDeriv (modeSecondDeriv ι H σ y) (b, j)‖ ^ 2
        = cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y)) := by
      rw [cnormSq, Fintype.sum_prod_type]
    refine ⟨?_, ?_, ?_⟩
    · have := gain_max (modeVel ι v σ y) (fun b j => modeGrad ι G σ y (b, j))
        (fun b => ∑ c, ((azimuthalField (unitVector c) b : ℝ) : ℂ) * modeVel ι v σ y c) y (ι.2 : ℝ) 1
        zero_le_one (vel_bound _) hy1
      rwa [eG] at this
    · have := gain_max (β := Fin 3 × Fin 3) (modeGrad ι G σ y) (fun b j => modeSecondDeriv ι H σ y (b.1, j, b.2))
        (fun b => ∑ c, pairGen b c * modeGrad ι G σ y c) y (ι.2 : ℝ) 2 zero_le_two (grad_bound _) hy2
      rwa [eH] at this
    · have hc := curl_identity (modeGrad ι G σ y) (modeSecondDeriv ι H σ y) (fun j => (azimuthalField y j : ℂ))
        (((ι.2 : ℝ) : ℂ) * Complex.I) hy2
      have := gain_max (curlOfGrad (modeGrad ι G σ y)) (fun b j => curlGradOfSecondDeriv (modeSecondDeriv ι H σ y) (b, j))
        (fun b => ∑ c, vecGen b c * curlOfGrad (modeGrad ι G σ y) c) y (ι.2 : ℝ) 1 zero_le_one
        (vel_bound _) hc
      rwa [eC] at this
  have hcn : ∀ {β : Type} [Fintype β], Continuous (fun x : β → ℂ => Real.sqrt (cnormSq x)) := by
    intro β _
    unfold cnormSq
    fun_prop
  have hcurl : Continuous (fun x : Fin 3 × Fin 3 → ℂ => Real.sqrt (cnormSq (curlOfGrad x))) := by
    unfold cnormSq curlOfGrad
    fun_prop
  have hcgh : Continuous (fun x : Fin 3 × Fin 3 × Fin 3 → ℂ => Real.sqrt (cnormSq (curlGradOfSecondDeriv x))) := by
    unfold cnormSq curlGradOfSecondDeriv
    fun_prop
  have aG := modeGrad_aesm hRot ι G hv.measurable_gradient
  have aH := modeSecondDeriv_aesm hRot ι H hv.measurable_secondDeriv
  have mV := hcn.comp_aestronglyMeasurable (modeVel_aesm hRot ι v hv.measurable_velocity)
  have mG := hcn.comp_aestronglyMeasurable aG
  have mH := hcn.comp_aestronglyMeasurable aH
  have mC := hcurl.comp_aestronglyMeasurable aG
  have mCH := hcgh.comp_aestronglyMeasurable aH
  have mr : AEStronglyMeasurable (fun z : ℝ × Space => cylRadius z.2) volume := by
    have hc : Continuous (fun z : ℝ × Space => cylRadius z.2) := by
      unfold cylRadius
      fun_prop
    exact hc.aestronglyMeasurable
  have hall := ae_of_ae_ae (p := fun z : ℝ × Space =>
      max (|(ι.2 : ℝ)| - 1) 0 * Real.sqrt (cnormSq (modeVel ι v z.1 z.2))
          ≤ cylRadius z.2 * Real.sqrt (cnormSq (modeGrad ι G z.1 z.2)) ∧
        max (|(ι.2 : ℝ)| - 2) 0 * Real.sqrt (cnormSq (modeGrad ι G z.1 z.2))
          ≤ cylRadius z.2 * Real.sqrt (cnormSq (modeSecondDeriv ι H z.1 z.2)) ∧
        max (|(ι.2 : ℝ)| - 1) 0 * Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)))
          ≤ cylRadius z.2 * Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H z.1 z.2)))) ?_ hslice
  · filter_upwards [hall] with z hz
    obtain ⟨a1, a2, a3⟩ := hz
    refine ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, Real.sqrt_nonneg _, Real.sqrt_nonneg _,
      Real.sqrt_nonneg _, ?_, a1, a2, a3⟩
    rw [Real.sq_sqrt (by unfold cnormSq; positivity), Real.sq_sqrt (by unfold cnormSq; positivity)]
    exact cnormSq_curlOfGrad_le _
  · refine NullMeasurableSet.inter ?_ (NullMeasurableSet.inter ?_ ?_)
    · exact AEStronglyMeasurable.nullMeasurableSet_le (aestronglyMeasurable_const.mul mV) (mr.mul mG)
    · exact AEStronglyMeasurable.nullMeasurableSet_le (aestronglyMeasurable_const.mul mG) (mr.mul mH)
    · exact AEStronglyMeasurable.nullMeasurableSet_le (aestronglyMeasurable_const.mul mC) (mr.mul mCH)

theorem angularModePointwise : AngularModePointwise :=
  angularModePointwise_of
    (Coercive.modeDerivativeHolds_of Coercive.axialRotationHolds_proof
      Coercive.perturbationLocalIntegrabilityHolds_proof)
    (Coercive.modeRotationHolds_of Coercive.axialRotationHolds_proof
      Coercive.perturbationLocalIntegrabilityHolds_proof)

end TailBand

end CertCell

end Breakdown
