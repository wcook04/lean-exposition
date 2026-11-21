import Breakdown.Cert.CoerciveSmoothEpsSetting
import Breakdown.Cert.CoerciveSmoothPieceEpsCoreModes
import Breakdown.Cert.CoerciveSmoothEpsPointwiseModes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

theorem frameRest_lower {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y + epsGradTerm m v ι σ y
      ≤ (Complex.I * (m.epsW (m.classOf ι) y : ℂ)
          * cdot (Internal.SmoothPieceEpsCore.vortMode v ι σ y)
            (modeVel ι (Internal.SmoothPieceEpsCore.frameRest (m.rate (m.classOf ι) y) W v) σ y)).re := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hS.smooth.smooth 1
  set a := m.rate (m.classOf ι) y with ha
  set e := m.epsW (m.classOf ι) y with he
  set om := Internal.SmoothPieceEpsCore.vortMode v ι σ y with homdef
  have hom : om = modeVel ι (Internal.SmoothPieceEpsCore.vortField v) σ y :=
    Internal.SmoothPieceEpsCore.vortMode_eq_modeVel hv1 ι σ y
  obtain ⟨R, hR, hRle⟩ := Internal.SmoothEpsPointwise.stretch_split hS ι σ y
  rw [Internal.SmoothEpsPointwise.frame_split hS a, hR]
  set A := fderiv ℝ (meanField W) y
  set T1 := modeVel ι (Internal.SmoothPieceEpsCore.transportRest a W v) σ y
  set T3 := modeVel ι (Internal.SmoothPieceEpsCore.vortTransportRest W v) σ y
  set T4 := modeVel ι (Internal.SmoothPieceEpsCore.vortStretchRest W v) σ y
  set T5 := modeVel ι (Internal.SmoothPieceEpsCore.rotationRest a v) σ y
  set Aom : Fin 3 → ℂ := fun i => ∑ j : Fin 3, ((A (unitVector j) i : ℝ) : ℂ) * om j
  have hsplit : (Complex.I * (e : ℂ) * cdot om (T1 - (Aom + R) + T3 - T4 + T5)).re
      = (Complex.I * (e : ℂ) * cdot om T1).re - (Complex.I * (e : ℂ) * cdot om Aom).re
        - (Complex.I * (e : ℂ) * cdot om R).re + (Complex.I * (e : ℂ) * cdot om T3).re
        - (Complex.I * (e : ℂ) * cdot om T4).re + (Complex.I * (e : ℂ) * cdot om T5).re := by
    simp only [Internal.SmoothPieceEpsCore.cdot_add, Internal.SmoothPieceEpsCore.cdot_sub, mul_add, mul_sub,
      Complex.add_re, Complex.sub_re]
    ring
  rw [hsplit]
  set vA := vortAmp (gradField v) ι σ y
  have hvA : Internal.MuSmooth.cnorm3 om = vA := rfl
  have hvA0 : 0 ≤ vA := Real.sqrt_nonneg _
  have hsq : cnormSq om = vA ^ 2 := by rw [← hvA, Internal.MuSmooth.cnorm3_sq]
  have he0 : 0 ≤ |e| * vA := mul_nonneg (abs_nonneg e) hvA0
  have h1 := Internal.SmoothEpsPointwise.re_cdot_abs_le e om T1
  have h1' := mul_le_mul_of_nonneg_left (Internal.SmoothEpsPointwise.transport_le hS (m.classOf ι) ι σ y) he0
  have hA := Internal.SmoothEpsPointwise.mean_stretch_re_le e A om
  have hRb := Internal.SmoothEpsPointwise.re_cdot_abs_le e om R
  have hR' := mul_le_mul_of_nonneg_left hRle he0
  have h3 := Internal.SmoothEpsPointwise.re_cdot_abs_le e om T3
  have h3' := mul_le_mul_of_nonneg_left (Internal.SmoothEpsPointwise.vortTransport_le hS ι σ y) he0
  have h4 := Internal.SmoothEpsPointwise.re_cdot_abs_le e om T4
  have h4' := mul_le_mul_of_nonneg_left (Internal.SmoothEpsPointwise.vortStretch_le hS ι σ y) he0
  have h5 : |(Complex.I * (e : ℂ) * cdot om T5).re| ≤ |e| * |a| * cnormSq om := by
    obtain ⟨r0, r1, r2⟩ := Internal.SmoothPieceEpsCore.modeVel_rotationRest a v ι σ y
    rw [← hom] at r0 r1
    exact Internal.SmoothPieceEpsCore.rotation_term_le e a om T5 r0 r1 r2
  rw [hvA] at h1 hRb h3 h4
  rw [hsq] at hA h5
  have key : modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y + epsGradTerm m v ι σ y
      = -(|e| * vA * (‖relativeVelocity W (m.rate (m.classOf ι)) y‖ * vortGradAmp (secondDerivField v) ι σ y
          + ∑ α ∈ m.waves, velAmp W α σ y * vortGradAmp (secondDerivField v) (ι - α) σ y))
        - |e| * ((1 / 2) * ‖curlVec A‖) * vA ^ 2 - |e| * |a| * vA ^ 2
        - |e| * vA * (‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * velAmp v ι σ y
          + ∑ α ∈ m.waves, vortGradAmp (secondDerivField W) α σ y * velAmp v (ι - α) σ y)
        - |e| * vA * (‖curlVec A‖ * gradAmp (gradField v) ι σ y
          + ∑ α ∈ m.waves, vortAmp (gradField W) α σ y * gradAmp (gradField v) (ι - α) σ y)
        - |e| * vA * ∑ α ∈ m.waves, gradAmp (gradField W) α σ y * vortAmp (gradField v) (ι - α) σ y := by
    unfold modeEpsRest epsGradTerm ModeWeights.eps
    simp only [Finset.sum_add_distrib]
    ring
  rw [key]
  have := abs_le.mp h1
  have := abs_le.mp hRb
  have := abs_le.mp h3
  have := abs_le.mp h4
  have := abs_le.mp h5
  nlinarith

theorem re_split (e F : ℝ) (x L Z S : Fin 3 → ℂ)
    (hS : ∀ i, S i - L i = ((F : ℂ) * Complex.I) * x i + x i + Z i) :
    (Complex.I * (e : ℂ) * cdot x S).re
      = (Complex.I * (e : ℂ) * cdot x L).re + e * F * cnormSq x + (Complex.I * (e : ℂ) * cdot x Z).re := by
  have hS' : S = fun i => L i + (((F : ℂ) * Complex.I) * x i + x i + Z i) := funext fun i => by
    rw [← hS i]; ring
  subst hS'
  simp only [cdot, cnormSq, Fin.sum_univ_three, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem epsIntegrand_lower {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeEpsPos m P (gradField v) ι σ y + modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y
        + epsGradTerm m v ι σ y + epsIntegrand m v (negSumSecondPartialsOfField v) ι σ y
      ≤ epsIntegrand m v (smoothRight P W v) ι σ y := by
  have hid := Internal.SmoothPieceEpsCore.mode_identity (P := P) (a := m.rate (m.classOf ι) y) hS.smooth
    hS.flow_smooth hS.flow_periodic hS.flow_div ι σ y
  have hb := frameRest_lower hS ι σ y
  have hsplit := re_split (m.epsW (m.classOf ι) y) (PieceWeights.frameFreq P (m.rate (m.classOf ι) y) ι)
    (Internal.SmoothPieceEpsCore.vortMode v ι σ y)
    (Internal.SmoothPieceEpsCore.vortMode (Internal.SmoothPieceEpsCore.negSumSecondPartials v) ι σ y)
    (modeVel ι (Internal.SmoothPieceEpsCore.frameRest (m.rate (m.classOf ι) y) W v) σ y)
    (Internal.SmoothPieceEpsCore.vortMode (smoothRight P W v) ι σ y) hid
  have hF : PieceWeights.frameFreq P (m.rate (m.classOf ι) y) ι = m.dop P ι y := by
    simp only [PieceWeights.frameFreq, ModeWeights.dop, shiftedFrequency]
    ring
  have hsign := hS.admissible.epsW_sign ι y
  have hpos : modeEpsPos m P (gradField v) ι σ y
      = m.epsW (m.classOf ι) y * PieceWeights.frameFreq P (m.rate (m.classOf ι) y) ι
        * cnormSq (Internal.SmoothPieceEpsCore.vortMode v ι σ y) := by
    have hc : 0 ≤ cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y)) := by
      unfold cnormSq; positivity
    have he : |m.epsW (m.classOf ι) y| * |m.dop P ι y| = m.epsW (m.classOf ι) y * m.dop P ι y := by
      rw [← abs_mul]
      exact abs_of_nonneg (by rw [mul_comm]; exact hsign)
    unfold modeEpsPos vortAmp ModeWeights.eps
    rw [Real.sq_sqrt hc, hF, he]
    rfl
  have e1 : epsIntegrand m v (smoothRight P W v) ι σ y
      = (Complex.I * (m.epsW (m.classOf ι) y : ℂ) * cdot (Internal.SmoothPieceEpsCore.vortMode v ι σ y)
          (Internal.SmoothPieceEpsCore.vortMode (smoothRight P W v) ι σ y)).re := rfl
  have e2 : epsIntegrand m v (negSumSecondPartialsOfField v) ι σ y
      = (Complex.I * (m.epsW (m.classOf ι) y : ℂ) * cdot (Internal.SmoothPieceEpsCore.vortMode v ι σ y)
          (Internal.SmoothPieceEpsCore.vortMode (Internal.SmoothPieceEpsCore.negSumSecondPartials v) ι σ y)).re := rfl
  rw [e1, e2, hsplit, hpos]
  linarith

end SmoothEpsInternal

end Coercive

end Breakdown
