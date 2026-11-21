import Breakdown.Cert.CoerciveField
import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoerciveSmoothPieceMuSumSecondPartials
import Breakdown.Cert.CoerciveSmoothPieceEpsSeries
import Breakdown.Cert.CoerciveSmoothPiecePairingSplitWeight
import Breakdown.Cert.CoercivePieceAbsorbMeasure
import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.CoerciveSmoothMuModeCalc
import Breakdown.Cert.CoerciveSmoothPieceMuHarmonics
import Breakdown.Cert.CoerciveTorus

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceMuTransport

def axisTurn (x : Fin 3 → ℂ) : Fin 3 → ℂ := ![-x 1, x 0, 0]

def innerField (P : ℝ) (W v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)

def turnDir (x : Space) : Space := -(x 1) • unitVector 0 + x 0 • unitVector 1

def frameAdvection (W v : ℝ → Space → Space) (a : ℝ) (σ : ℝ) (y : Space) : Space :=
  fderiv ℝ (v σ) y (W σ y + (1 / 2 : ℝ) • y - a • turnDir y)

def negSumSecondPartialsField (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  -secondDerivTrace (secondDerivField v σ y)

def fieldTerm (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (v X : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  (Complex.I * ((PieceWeights.sgn T ι * φ y : ℝ) : ℂ) * cdot (modeVel ι v σ y) (modeVel ι X σ y)).re

def turnTerm (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (a : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  (Complex.I * ((PieceWeights.sgn T ι * φ y : ℝ) : ℂ)
    * ((a : ℂ) * cdot (modeVel ι v σ y) (axisTurn (modeVel ι v σ y)))).re

def freqTerm (P : ℝ) (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (a : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) : ℝ :=
  ModeWeights.ind (PieceWeights.inPiece T ι) * φ y * |PieceWeights.frameFreq P a ι| * velAmp v ι σ y ^ 2

def freqSeries (P : ℝ) (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (a : ℝ) (v : ℝ → Space → Space) : ℝ≥0∞ :=
  ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (freqTerm P T φ a v ι σ y)

def edgeSeries (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (W v : ℝ → Space → Space) : ℝ≥0∞ :=
  ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (φ y * velAmp v ι σ y
    * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι)

def turnBlock (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (a : ℝ) (v : ℝ → Space → Space) : ℝ≥0∞ :=
  ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
    ENNReal.ofReal (φ y * |a| * pieceNorm T (fun κ => velAmp v κ σ y) ^ 2)

def advectionBlock (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (W : ℝ → Space → Space) (a : ℝ)
    (v : ℝ → Space → Space) : ℝ≥0∞ :=
  ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (φ y * frameSpeedSup W a y
    * pieceNorm T (fun κ => gradAmp (gradField v) κ σ y) * pieceNorm T (fun κ => velAmp v κ σ y))

def sumSecondPartialsBlock (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (v : ℝ → Space → Space) : ℝ≥0∞ :=
  ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (PieceWeights.wtGrad φ y
    * pieceNorm T (fun κ => gradAmp (gradField v) κ σ y) * pieceNorm T (fun κ => velAmp v κ σ y))


def timeDerivField (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space := deriv (fun s => v s y) σ

def turnField (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  fderiv ℝ (v σ) y (turnDir y)

private theorem time_mode {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) :
    modeVel ι (timeDerivField v) σ y = fun i => ((2 * Real.pi * ι.1 : ℝ) * Complex.I) * modeVel ι v σ y i :=
  Internal.ModeCalc.time_mode P v hv ι σ y

private theorem turn_mode {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) :
    modeVel ι (turnField v) σ y = fun i => ((ι.2 : ℝ) * Complex.I) * modeVel ι v σ y i
      + axisTurn (modeVel ι v σ y) i :=
  Internal.ModeCalc.azim_mode P v hv ι σ y

theorem innerField_decomp (P : ℝ) (W v : ℝ → Space → Space) (a : ℝ) (s : ℝ) (x : Space) :
    innerField P W v s x = (1 / P) • timeDerivField v s x + (1 / 2 : ℝ) • v s x
      + frameAdvection W v a s x + a • turnField v s x + negSumSecondPartialsField v s x := by
  unfold innerField smoothRight timeDerivField frameAdvection turnField negSumSecondPartialsField
  simp only [map_add, map_sub, map_smul]
  module

private theorem rotated_decomp (P : ℝ) (W v : ℝ → Space → Space) (a σ τ φ : ℝ) (y : Space) (j : Fin 3) :
    axialRot (-φ) (innerField P W v (σ + τ) (axialRot φ y)) j
      = (1 / P) * axialRot (-φ) (timeDerivField v (σ + τ) (axialRot φ y)) j
        + (1 / 2 : ℝ) * axialRot (-φ) (v (σ + τ) (axialRot φ y)) j
        + axialRot (-φ) (frameAdvection W v a (σ + τ) (axialRot φ y)) j
        + a * axialRot (-φ) (turnField v (σ + τ) (axialRot φ y)) j
        + axialRot (-φ) (negSumSecondPartialsField v (σ + τ) (axialRot φ y)) j := by
  rw [innerField_decomp P W v a (σ + τ) (axialRot φ y)]
  simp only [Internal.Field.axialRot_add, Internal.Field.axialRot_smul]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

private theorem timeDerivField_continuous {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => timeDerivField v z.1 z.2) := by
  have hd : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.differentiable (by simp)
  have e : (fun z : ℝ × Space => timeDerivField v z.1 z.2)
      = fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) z (1, 0) := by
    funext z
    unfold timeDerivField
    have h := (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
    exact h.deriv
  rw [e]
  exact ((hv.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)

private theorem gradSlice_continuous {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
  (PairingSplitInternal.contDiff_slice (n := 0) hv.smooth
    (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).continuous

private theorem negSumSecondPartialsField_continuous {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => negSumSecondPartialsField v z.1 z.2) := by
  have h2 : Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
    (PairingSplitInternal.contDiff_slice (n := 0) (V := fun s x => fderiv ℝ (v s) x)
      (PairingSplitInternal.contDiff_slice (n := ∞) hv.smooth (by exact_mod_cast le_rfl))
        (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).continuous
  unfold negSumSecondPartialsField secondDerivField
  exact (Internal.Field.secondDerivTrace_continuous.comp h2).neg

private theorem applied_integrand_continuous {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : Continuous (fun z : ℝ × Space => G z.1 z.2)) {u : ℝ × ℝ → Space} (hu : Continuous u)
    (σ : ℝ) (y : Space) (i : Fin 3) :
    Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (G (σ + p.1) (axialRot p.2 y) (u p)) i) := by
  have h1 : Continuous (fun p : ℝ × ℝ => ((σ + p.1, axialRot p.2 y) : ℝ × Space)) :=
    (continuous_const.add continuous_fst).prodMk
      (Internal.Field.axialRot_comp_continuous continuous_snd continuous_const)
  have h2 : Continuous (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y) (u p)) :=
    (hG.comp h1).clm_apply hu
  have h3 := Internal.Field.axialRot_comp_continuous continuous_snd.neg h2
  exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp h3

private theorem mode_split_of {P : ℝ} {W v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (hW : Continuous (fun z : ℝ × Space => W z.1 z.2)) (a : ℝ) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (innerField P W v) σ y = fun i =>
      ((PieceWeights.frameFreq P a ι : ℂ) * Complex.I) * modeVel ι v σ y i
        + (a : ℂ) * axisTurn (modeVel ι v σ y) i + (1 / 2 : ℂ) * modeVel ι v σ y i
        + modeVel ι (frameAdvection W v a) σ y i + modeVel ι (negSumSecondPartialsField v) σ y i := by
  have hG := gradSlice_continuous hv
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hrot : Continuous (fun p : ℝ × ℝ => axialRot p.2 y) :=
    Internal.Field.axialRot_comp_continuous continuous_snd continuous_const
  have haz : Continuous turnDir := by
    unfold turnDir
    fun_prop
  funext i
  have cT := Internal.Field.mode_integrand_continuous (timeDerivField_continuous hv) σ y i
  have cV := Internal.Field.mode_integrand_continuous hvc σ y i
  have cL := Internal.Field.mode_integrand_continuous (negSumSecondPartialsField_continuous hv) σ y i
  have cA : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (turnField v (σ + p.1) (axialRot p.2 y)) i) := by
    unfold turnField
    exact applied_integrand_continuous (G := fun s x => fderiv ℝ (v s) x) hG
      (u := fun p : ℝ × ℝ => turnDir (axialRot p.2 y)) (haz.comp hrot) σ y i
  have cR : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (frameAdvection W v a (σ + p.1) (axialRot p.2 y)) i) := by
    have hu : Continuous (fun p : ℝ × ℝ => W (σ + p.1) (axialRot p.2 y) + (1 / 2 : ℝ) • axialRot p.2 y
        - a • turnDir (axialRot p.2 y)) := by
      have h0 : Continuous (fun p : ℝ × ℝ => ((σ + p.1, axialRot p.2 y) : ℝ × Space)) :=
        (continuous_const.add continuous_fst).prodMk hrot
      have h1 : Continuous (fun p : ℝ × ℝ => W (σ + p.1) (axialRot p.2 y)) := hW.comp h0
      have h2 : Continuous (fun p : ℝ × ℝ => turnDir (axialRot p.2 y)) := haz.comp hrot
      exact (h1.add ((continuous_const (y := (1 / 2 : ℝ))).smul hrot)).sub
        ((continuous_const (y := a)).smul h2)
    unfold frameAdvection
    exact applied_integrand_continuous (G := fun s x => fderiv ℝ (v s) x) hG hu σ y i
  have hpt : (fun τ φ (j : Fin 3) => axialRot (-φ) (innerField P W v (σ + τ) (axialRot φ y)) j)
      = fun τ φ j => (1 / P) * axialRot (-φ) (timeDerivField v (σ + τ) (axialRot φ y)) j
        + (1 / 2 : ℝ) * axialRot (-φ) (v (σ + τ) (axialRot φ y)) j
        + axialRot (-φ) (frameAdvection W v a (σ + τ) (axialRot φ y)) j
        + a * axialRot (-φ) (turnField v (σ + τ) (axialRot φ y)) j
        + axialRot (-φ) (negSumSecondPartialsField v (σ + τ) (axialRot φ y)) j := by
    funext τ φ j
    exact rotated_decomp P W v a σ τ φ y j
  have ht := congrFun (time_mode hv ι σ y) i
  have hz := congrFun (turn_mode hv ι σ y) i
  unfold modeVel at ht hz ⊢
  rw [hpt]
  rw [Internal.Field.modeAverage_add _ _ _ _ (by
        exact (((continuous_const.mul cT).add (continuous_const.mul cV)).add cR).add
          (continuous_const.mul cA)) cL,
    Internal.Field.modeAverage_add _ _ _ _ (by
        exact ((continuous_const.mul cT).add (continuous_const.mul cV)).add cR) (continuous_const.mul cA),
    Internal.Field.modeAverage_add _ _ _ _ (by
        exact (continuous_const.mul cT).add (continuous_const.mul cV)) cR,
    Internal.Field.modeAverage_add _ _ _ _ (continuous_const.mul cT) (continuous_const.mul cV),
    Internal.Field.modeAverage_const_mul, Internal.Field.modeAverage_const_mul,
    Internal.Field.modeAverage_const_mul, ht, hz]
  unfold PieceWeights.frameFreq
  push_cast
  ring

def advectionLoss (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (W : ℝ → Space → Space) (a : ℝ)
    (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : ℝ :=
  φ y * |a| * pieceNorm T (fun κ => velAmp v κ σ y) ^ 2
    + φ y * frameSpeedSup W a y * pieceNorm T (fun κ => gradAmp (gradField v) κ σ y)
      * pieceNorm T (fun κ => velAmp v κ σ y)
    + ∑' ι : ℤ × ℤ, φ y * velAmp v ι σ y
      * edgeSum h T (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι

theorem frameFreq_neg (P a : ℝ) (ι : ℤ × ℤ) :
    PieceWeights.frameFreq P a (-ι) = -PieceWeights.frameFreq P a ι := by
  unfold PieceWeights.frameFreq
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

theorem sgn_mul_frameFreq (P a : ℝ) (T : Set (ℤ × ℤ))
    (hT : ∃ Ωs > 0, ∀ ι ∈ T, Ωs ≤ PieceWeights.frameFreq P a ι) (ι : ℤ × ℤ) :
    PieceWeights.sgn T ι * PieceWeights.frameFreq P a ι
      = ModeWeights.ind (PieceWeights.inPiece T ι) * |PieceWeights.frameFreq P a ι| := by
  obtain ⟨Ωs, hΩ, hT⟩ := hT
  unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
  by_cases h1 : ι ∈ T
  · have := hT ι h1
    rw [if_pos h1, if_pos (Or.inl h1), abs_of_pos (by linarith)]
    try ring
  · by_cases h2 : -ι ∈ T
    · have := hT (-ι) h2
      rw [frameFreq_neg] at this
      rw [if_neg h1, if_pos h2, if_pos (Or.inr h2), abs_of_neg (by linarith)]
      try ring
    · rw [if_neg h1, if_neg h2, if_neg (by tauto)]
      try ring

theorem term_expand (μ d a : ℝ) (x J R L : Fin 3 → ℂ) :
    (Complex.I * (μ : ℂ) * cdot x (fun i => ((d : ℂ) * Complex.I) * x i + (a : ℂ) * J i
        + (1 / 2 : ℂ) * x i + R i + L i)).re
      = μ * d * cnormSq x + (Complex.I * (μ : ℂ) * ((a : ℂ) * cdot x J)).re
        + (Complex.I * (μ : ℂ) * cdot x R).re + (Complex.I * (μ : ℂ) * cdot x L).re := by
  simp only [cdot, cnormSq, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, map_add, map_mul, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply, Complex.conj_ofReal,
    Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im]
  ring

theorem fieldTerm_split (P : ℝ) (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (a : ℝ) (W v : ℝ → Space → Space)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space)
    (hmode : modeVel ι (innerField P W v) σ y = fun i =>
      ((PieceWeights.frameFreq P a ι : ℂ) * Complex.I) * modeVel ι v σ y i
        + (a : ℂ) * axisTurn (modeVel ι v σ y) i + (1 / 2 : ℂ) * modeVel ι v σ y i
        + modeVel ι (frameAdvection W v a) σ y i + modeVel ι (negSumSecondPartialsField v) σ y i)
    (hsf : PieceWeights.sgn T ι * PieceWeights.frameFreq P a ι
      = ModeWeights.ind (PieceWeights.inPiece T ι) * |PieceWeights.frameFreq P a ι|) :
    fieldTerm T φ v (innerField P W v) ι σ y
      = freqTerm P T φ a v ι σ y + turnTerm T φ a v ι σ y + fieldTerm T φ v (frameAdvection W v a) ι σ y
        + fieldTerm T φ v (negSumSecondPartialsField v) ι σ y := by
  unfold fieldTerm turnTerm freqTerm
  rw [hmode, term_expand]
  have hc : velAmp v ι σ y ^ 2 = cnormSq (modeVel ι v σ y) :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hc]
  have : PieceWeights.sgn T ι * φ y * PieceWeights.frameFreq P a ι * cnormSq (modeVel ι v σ y)
      = ModeWeights.ind (PieceWeights.inPiece T ι) * φ y * |PieceWeights.frameFreq P a ι|
        * cnormSq (modeVel ι v σ y) := by
    rw [show PieceWeights.sgn T ι * φ y * PieceWeights.frameFreq P a ι
      = (PieceWeights.sgn T ι * PieceWeights.frameFreq P a ι) * φ y by ring, hsf]
    ring
  linarith

theorem lintegral_three_le (f1 f2 f3 : ℝ → Space → ℝ≥0∞) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f1 σ y) + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f2 σ y)
        + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f3 σ y)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f1 σ y + f2 σ y + f3 σ y) := by
  refine ((add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _)).trans ?_
  exact lintegral_mono fun σ => (add_le_add (le_lintegral_add _ _) le_rfl).trans (le_lintegral_add _ _)

private theorem piece_sum_mul_le (T : Set (ℤ × ℤ)) {q : ℝ} (hq : 0 ≤ q) (g u : ℤ × ℤ → ℝ)
    (hg0 : ∀ κ, 0 ≤ g κ) (hu0 : ∀ κ, 0 ≤ u κ) (hgs : Summable (fun κ => g κ ^ 2))
    (hus : Summable (fun κ => u κ ^ 2)) :
    ∑' κ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece T κ) * (q * g κ * u κ))
      ≤ ENNReal.ofReal (q * pieceNorm T g * pieceNorm T u) := by
  have hi0 : ∀ κ, 0 ≤ ModeWeights.ind (PieceWeights.inPiece T κ) := fun κ => by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hi1 : ∀ κ, ModeWeights.ind (PieceWeights.inPiece T κ) ≤ 1 := fun κ => by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hsq : ∀ κ, Real.sqrt (ModeWeights.ind (PieceWeights.inPiece T κ) * g κ ^ 2)
      * Real.sqrt (ModeWeights.ind (PieceWeights.inPiece T κ) * u κ ^ 2)
      = ModeWeights.ind (PieceWeights.inPiece T κ) * (g κ * u κ) := by
    intro κ
    unfold ModeWeights.ind
    split_ifs
    · rw [one_mul, one_mul, one_mul, Real.sqrt_sq (hg0 κ), Real.sqrt_sq (hu0 κ)]
    · simp
  have sg : Summable (fun κ => ModeWeights.ind (PieceWeights.inPiece T κ) * g κ ^ 2) :=
    Summable.of_nonneg_of_le (fun κ => mul_nonneg (hi0 κ) (sq_nonneg _))
      (fun κ => mul_le_of_le_one_left (sq_nonneg _) (hi1 κ)) hgs
  have su : Summable (fun κ => ModeWeights.ind (PieceWeights.inPiece T κ) * u κ ^ 2) :=
    Summable.of_nonneg_of_le (fun κ => mul_nonneg (hi0 κ) (sq_nonneg _))
      (fun κ => mul_le_of_le_one_left (sq_nonneg _) (hi1 κ)) hus
  obtain ⟨hs, hle⟩ := Internal.FieldModes.tsum_sqrt_mul_le (fun κ => mul_nonneg (hi0 κ) (sq_nonneg (g κ)))
    (fun κ => mul_nonneg (hi0 κ) (sq_nonneg (u κ))) sg su
  simp only [hsq] at hs hle
  have e : ∀ κ, ModeWeights.ind (PieceWeights.inPiece T κ) * (q * g κ * u κ)
      = q * (ModeWeights.ind (PieceWeights.inPiece T κ) * (g κ * u κ)) := fun κ => by ring
  have hn : ∀ κ, 0 ≤ q * (ModeWeights.ind (PieceWeights.inPiece T κ) * (g κ * u κ)) :=
    fun κ => mul_nonneg hq (mul_nonneg (hi0 κ) (mul_nonneg (hg0 κ) (hu0 κ)))
  simp only [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn (hs.mul_left q), tsum_mul_left]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hle hq

private theorem tsum_eq_toReal_ofReal {f : ℤ × ℤ → ℝ} (hf : ∀ ι, 0 ≤ f ι) :
    ∑' ι, f ι = (∑' ι, ENNReal.ofReal (f ι)).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun ι => (ENNReal.toReal_ofReal (hf ι)).symm

private theorem aem_pieceNorm_of {μ : Measure (ℝ × Space)} (T : Set (ℤ × ℤ)) {g : ℤ × ℤ → ℝ × Space → ℝ}
    (hg : ∀ κ, AEMeasurable (g κ) μ) : AEMeasurable (fun z => pieceNorm T (fun κ => g κ z)) μ := by
  have he : ∀ z, pieceNorm T (fun κ => g κ z)
      = Real.sqrt (∑' κ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece T κ) * g κ z ^ 2)).toReal := by
    intro z
    unfold pieceNorm
    congr 1
    exact tsum_eq_toReal_ofReal (f := fun κ => ModeWeights.ind (PieceWeights.inPiece T κ) * g κ z ^ 2)
      (fun κ => mul_nonneg (Internal.PieceAbsorb.ind_nonneg _) (sq_nonneg _))
  simp only [he]
  exact Real.continuous_sqrt.measurable.comp_aemeasurable (AEMeasurable.ennreal_toReal
    (AEMeasurable.tsum fun κ => ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_const.mul ((hg κ).pow_const 2))))

private theorem aem_edgeSum {μ : Measure (ℝ × Space)} (h : HarmonicBounds) (T : Set (ℤ × ℤ))
    {X g : ℤ × ℤ → ℝ × Space → ℝ} (hX : ∀ α, AEMeasurable (X α) μ) (hg : ∀ κ, AEMeasurable (g κ) μ)
    (ι : ℤ × ℤ) : AEMeasurable (fun z => edgeSum h T (fun α => X α z) (fun κ => g κ z) ι) μ := by
  classical
  unfold edgeSum
  by_cases h1 : ι ∈ T
  · simp only [if_pos h1]
    refine Finset.aemeasurable_fun_sum _ fun β _ => ?_
    by_cases h2 : ι - β ∈ T
    · simp only [if_pos h2]
      exact aemeasurable_const
    · simp only [if_neg h2]
      exact (hX β).mul (hg _)
  · by_cases h3 : -ι ∈ T
    · simp only [if_neg h1, if_pos h3]
      refine Finset.aemeasurable_fun_sum _ fun β _ => ?_
      by_cases h2 : -ι - β ∈ T
      · simp only [if_pos h2]
        exact aemeasurable_const
      · simp only [if_neg h2]
        exact (hX β).mul (hg _)
    · simp only [if_neg h1, if_neg h3]
      exact aemeasurable_const

private theorem frame_term_le {W : ℝ → Space → Space} {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (a : ℝ) (y : Space)
    (p : ℝ × ℝ) :
    ‖W p.1 (axialRot p.2 y) + (1 / 2 : ℝ) • axialRot p.2 y
      - a • (-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1)‖
        ≤ D + (1 / 2 + 2 * |a|) * ‖y‖ := by
  have hD0 := Internal.SmoothPieceEps.decay_const_nonneg W hD
  have hb : ‖W p.1 (axialRot p.2 y)‖ ≤ D := by
    have := hD p.1 (axialRot p.2 y) 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at this
    refine le_trans this (div_le_self hD0 ?_)
    linarith [norm_nonneg (axialRot p.2 y)]
  have hr := RotationInternal.axialRot_norm p.2 y
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hr]
  have hp := Internal.SmoothPieceEps.norm_perp_le (axialRot p.2 y)
  rw [hr] at hp
  have : |a| * ‖-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1‖ ≤ |a| * (2 * ‖y‖) :=
    mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [abs_nonneg a, norm_nonneg y]

private theorem frameSpeedSup_measurable {W : ℝ → Space → Space}
    (hW : Continuous (fun z : ℝ × Space => W z.1 z.2)) {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (a : ℝ) :
    Measurable (frameSpeedSup W a) := by
  unfold frameSpeedSup
  refine (lowerSemicontinuous_ciSup (fun y => ⟨D + (1 / 2 + 2 * |a|) * ‖y‖, ?_⟩) (fun p => ?_)).measurable
  · rintro _ ⟨p, rfl⟩
    exact frame_term_le hD a y p
  · have hr : Continuous (fun y : Space => axialRot p.2 y) :=
      Internal.Field.axialRot_comp_continuous continuous_const continuous_id
    have hWs : Continuous (fun y : Space => W p.1 (axialRot p.2 y)) :=
      hW.comp (continuous_const.prodMk hr)
    have c0 : Continuous (fun y : Space => axialRot p.2 y 1) :=
      (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp hr
    have c1 : Continuous (fun y : Space => axialRot p.2 y 0) :=
      (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp hr
    have cu0 : Continuous (fun y : Space => -(axialRot p.2 y 1) • unitVector 0) := c0.neg.smul continuous_const
    have cu1 : Continuous (fun y : Space => axialRot p.2 y 0 • unitVector 1) := c1.smul continuous_const
    have cv : Continuous (fun y : Space => (1 / 2 : ℝ) • axialRot p.2 y) := (continuous_const (y := (1 / 2 : ℝ))).smul hr
    have ct : Continuous (fun y : Space => a • (-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1)) :=
      (continuous_const (y := a)).smul (cu0.add cu1)
    have hF : Continuous (fun y : Space => ‖W p.1 (axialRot p.2 y) + (1 / 2 : ℝ) • axialRot p.2 y
        - a • (-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1)‖) :=
      ((hWs.add cv).sub ct).norm
    exact hF.lowerSemicontinuous

theorem abs_sgn_eq_ind (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) :
    |PieceWeights.sgn T ι| = ModeWeights.ind (PieceWeights.inPiece T ι) := by
  unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
  by_cases h1 : ι ∈ T <;> by_cases h2 : -ι ∈ T <;> simp [h1, h2]

theorem ind_nonneg_of (p : Prop) : 0 ≤ ModeWeights.ind p := by
  unfold ModeWeights.ind; split_ifs <;> norm_num

theorem ind_le_one_of (p : Prop) : ModeWeights.ind p ≤ 1 := by
  unfold ModeWeights.ind; split_ifs <;> norm_num

theorem turnTerm_abs_le (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (a : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) (hφ : 0 ≤ φ y) :
    |turnTerm T φ a v ι σ y| ≤ φ y * |a| * (ModeWeights.ind (PieceWeights.inPiece T ι) * velAmp v ι σ y ^ 2) := by
  unfold turnTerm
  have hxq : velAmp v ι σ y ^ 2 = cnormSq (modeVel ι v σ y) :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hxq]
  set x := modeVel ι v σ y
  have h1 := Internal.FieldModes.abs_re_I_mul_le (PieceWeights.sgn T ι * φ y) ((a : ℂ) * cdot x (axisTurn x))
  have hJx : cnormSq (axisTurn x) ≤ cnormSq x := by
    unfold cnormSq axisTurn
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, norm_neg, norm_zero]
    nlinarith [sq_nonneg ‖x 2‖]
  have h2 := Internal.Field.norm_cdot_le_sqrt x (axisTurn x)
  have hx0 : 0 ≤ cnormSq x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs : Real.sqrt (cnormSq (axisTurn x)) ≤ Real.sqrt (cnormSq x) := Real.sqrt_le_sqrt hJx
  have hcd : ‖cdot x (axisTurn x)‖ ≤ cnormSq x := by
    refine h2.trans ?_
    calc Real.sqrt (cnormSq x) * Real.sqrt (cnormSq (axisTurn x))
        ≤ Real.sqrt (cnormSq x) * Real.sqrt (cnormSq x) := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = cnormSq x := Real.mul_self_sqrt hx0
  rw [abs_mul, abs_sgn_eq_ind, abs_of_nonneg hφ, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
  have hi := ind_nonneg_of (PieceWeights.inPiece T ι)
  calc _ ≤ _ := h1
    _ ≤ ModeWeights.ind (PieceWeights.inPiece T ι) * φ y * (|a| * cnormSq x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcd (abs_nonneg a)) (mul_nonneg hi hφ)
    _ = _ := by ring

theorem fieldTerm_abs_le (T : Set (ℤ × ℤ)) (φ : Space → ℝ) (v X : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) (hφ : 0 ≤ φ y) :
    |fieldTerm T φ v X ι σ y| ≤ φ y * (ModeWeights.ind (PieceWeights.inPiece T ι) * velAmp v ι σ y * velAmp X ι σ y) := by
  unfold fieldTerm
  have h1 := Internal.FieldModes.abs_re_I_mul_le (PieceWeights.sgn T ι * φ y) (cdot (modeVel ι v σ y) (modeVel ι X σ y))
  have h2 := Internal.Field.norm_cdot_le_sqrt (modeVel ι v σ y) (modeVel ι X σ y)
  rw [abs_mul, abs_sgn_eq_ind, abs_of_nonneg hφ] at h1
  have hi := ind_nonneg_of (PieceWeights.inPiece T ι)
  calc _ ≤ _ := h1
    _ ≤ ModeWeights.ind (PieceWeights.inPiece T ι) * φ y * (velAmp v ι σ y * velAmp X ι σ y) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hi hφ)
    _ = _ := by ring

open Classical in
def innerMode (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (W v : ℝ → Space → Space) (a σ : ℝ) (y : Space)
    (ι : ℤ × ℤ) : Fin 3 → ℂ :=
  fun i => ∑ j : Fin 3, (((((1 / 2 : ℝ) • y - a • turnDir y) j : ℝ) : ℂ) * modeGrad ι (gradField v) σ y (i, j)
    + ∑ α ∈ h.harmonics, if PieceWeights.inPiece T (ι - α)
      then modeVel α W σ y j * modeGrad (ι - α) (gradField v) σ y (i, j) else 0)

open Classical in
def outerMode (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (W v : ℝ → Space → Space) (σ : ℝ) (y : Space)
    (ι : ℤ × ℤ) : Fin 3 → ℂ :=
  fun i => ∑ j : Fin 3, ∑ α ∈ h.harmonics, if PieceWeights.inPiece T (ι - α)
    then 0 else modeVel α W σ y j * modeGrad (ι - α) (gradField v) σ y (i, j)

theorem edgeSum_nonneg (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g : ℤ × ℤ → ℝ) (hX : ∀ α, 0 ≤ X α)
    (hg : ∀ κ, 0 ≤ g κ) (ι : ℤ × ℤ) : 0 ≤ edgeSum h T X g ι := by
  unfold edgeSum
  split_ifs
  · exact Finset.sum_nonneg fun β _ => by split_ifs <;> first | exact le_rfl | exact mul_nonneg (hX _) (hg _)
  · exact Finset.sum_nonneg fun β _ => by split_ifs <;> first | exact le_rfl | exact mul_nonneg (hX _) (hg _)
  · exact le_rfl

theorem turnDir_axialRot (ψ : ℝ) (x : Space) : turnDir (axialRot ψ x) = axialRot ψ (turnDir x) := by
  unfold turnDir
  ext j
  fin_cases j <;> simp [axialRot, unitVector] <;> ring

theorem frame_vector_rot (φ a : ℝ) (w y : Space) (j : Fin 3) :
    axialRot (-φ) (w + (1 / 2 : ℝ) • axialRot φ y - a • turnDir (axialRot φ y)) j
      = axialRot (-φ) w j + ((1 / 2 : ℝ) • y - a • turnDir y) j := by
  rw [← Internal.ModeCalc.rotCoord_apply, map_sub, map_add, map_smul, map_smul, Internal.ModeCalc.rotCoord_apply,
    Internal.ModeCalc.rotCoord_apply, Internal.ModeCalc.rotCoord_apply, turnDir_axialRot,
    RotationInternal.axialRot_neg_self, RotationInternal.axialRot_neg_self]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem clm_orbit_continuous {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : Continuous (fun z : ℝ × Space => G z.1 z.2)) (σ : ℝ) (y : Space) (i j : Fin 3) :
    Continuous fun p : ℝ × ℝ =>
      ((axialRot (-p.2) (G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector j))) i : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (applied_integrand_continuous hG
    (u := fun p : ℝ × ℝ => axialRot p.2 (unitVector j))
    (Internal.Field.axialRot_comp_continuous continuous_snd continuous_const) σ y i)

private theorem clm_mode_product (s : Finset (ℤ × ℤ)) (G : ℝ → Space → (Space →L[ℝ] Space))
    (U : ℝ → Space → Space) (hG : Continuous fun z : ℝ × Space => G z.1 z.2) (σ : ℝ) (y : Space)
    (c : Fin 3 → ℝ) (d : ℤ × ℤ → Fin 3 → ℂ)
    (hE : ∀ τ φ : ℝ, ∀ j : Fin 3, ((axialRot (-φ) (U (σ + τ) (axialRot φ y)) j : ℝ) : ℂ)
      = (c j : ℂ) + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * d α j)
    (ι : ℤ × ℤ) (i : Fin 3) :
    modeVel ι (fun σ y => G σ y (U σ y)) σ y i
      = ∑ j : Fin 3, ((c j : ℂ) * modeGrad ι G σ y (i, j) + ∑ α ∈ s, d α j * modeGrad (ι - α) G σ y (i, j)) := by
  set E : ℤ × ℤ → ℝ → ℝ → ℂ := fun κ τ φ =>
    Complex.exp (-(((2 * Real.pi * κ.1 * τ + κ.2 * φ : ℝ) : ℂ) * Complex.I)) with hEdef
  set M : Fin 3 → ℝ → ℝ → ℂ := fun j τ φ =>
    ((axialRot (-φ) (G (σ + τ) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ) with hMdef
  have hMc : ∀ j, Continuous fun p : ℝ × ℝ => M j p.1 p.2 := fun j => clm_orbit_continuous hG σ y i j
  have hEc : ∀ κ, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 := fun κ => Internal.MuSmooth.cont_exp_pair κ
  have hmg : ∀ κ j, modeGrad κ G σ y (i, j)
      = (1 / (2 * Real.pi) : ℂ) * Internal.MuSmooth.boxInt (fun τ φ => E κ τ φ * M j τ φ) := fun κ j => rfl
  have hpt : ∀ τ φ, E ι τ φ * ((axialRot (-φ) (G (σ + τ) (axialRot φ y) (U (σ + τ) (axialRot φ y))) i : ℝ) : ℂ)
      = ∑ j : Fin 3, ((c j : ℂ) * (E ι τ φ * M j τ φ) + ∑ α ∈ s, d α j * (E (ι - α) τ φ * M j τ φ)) := by
    intro τ φ
    rw [Internal.MuSmooth.rot_apply_clm]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hE τ φ j, hEdef, hMdef]
    simp only
    simp only [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Internal.MuSmooth.exp_pair_mul ι α τ φ]
      ring
  have hlhs : modeVel ι (fun σ y => G σ y (U σ y)) σ y i
      = (1 / (2 * Real.pi) : ℂ) * Internal.MuSmooth.boxInt (fun τ φ => ∑ j : Fin 3,
        ((c j : ℂ) * (E ι τ φ * M j τ φ) + ∑ α ∈ s, d α j * (E (ι - α) τ φ * M j τ φ))) := by
    rw [← funext fun τ => funext fun φ => hpt τ φ]
    rfl
  have hc1 : ∀ κ j, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 * M j p.1 p.2 := fun κ j => (hEc κ).mul (hMc j)
  rw [hlhs, Internal.MuSmooth.boxInt_sum _ _ (fun j => ((continuous_const.mul (hc1 ι j)).add
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j))))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Internal.MuSmooth.boxInt_add _ _ (continuous_const.mul (hc1 ι j))
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j)),
    Internal.MuSmooth.boxInt_sum _ _ (fun α => continuous_const.mul (hc1 (ι - α) j)),
    Internal.MuSmooth.boxInt_const_mul]
  simp_rw [Internal.MuSmooth.boxInt_const_mul, hmg]
  rw [mul_add, Finset.mul_sum, mul_left_comm]
  congr 1
  exact Finset.sum_congr rfl fun α _ => mul_left_comm _ _ _

open Classical in
theorem outerMode_le_sum (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (W v : ℝ → Space → Space) (σ : ℝ) (y : Space)
    (ι : ℤ × ℤ) :
    Real.sqrt (cnormSq (outerMode h T W v σ y ι))
      ≤ ∑ α ∈ h.harmonics, if PieceWeights.inPiece T (ι - α) then 0
        else velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y := by
  have e : outerMode h T W v σ y ι = ∑ α ∈ h.harmonics, fun i => ∑ j : Fin 3,
      (if PieceWeights.inPiece T (ι - α) then 0 else modeGrad (ι - α) (gradField v) σ y (i, j))
        * modeVel α W σ y j := by
    funext i
    simp only [outerMode, Finset.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  show Internal.MuSmooth.cnorm3 _ ≤ _
  rw [e]
  refine (Internal.MuSmooth.cnorm3_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  by_cases hα : PieceWeights.inPiece T (ι - α)
  · simp [hα, Internal.MuSmooth.cnorm3, cnormSq]
  · simp only [hα, if_false]
    exact (Internal.MuSmooth.cnorm3_mat_le _ _).trans (le_of_eq (mul_comm _ _))

theorem orbit_mode_summable (g : ℝ → ℝ → ℝ) (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) :
    Summable (fun ι : ℤ × ℤ => ‖modeAverage ι (fun τ φ (_ : Unit) => g τ φ) ()‖ ^ 2) := by
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))).exists_bound_of_continuousOn hg.continuousOn
  have hfin : (∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (g τ φ ^ 2)) < ⊤ := by
    calc (∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (g τ φ ^ 2))
        ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (M ^ 2) := by
          refine setLIntegral_mono measurable_const fun τ hτ => setLIntegral_mono measurable_const fun φ hφ => ?_
          have h1 := hM (τ, φ) ⟨hτ, hφ⟩
          rw [Real.norm_eq_abs] at h1
          have h2 : |g τ φ| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          rw [sq_abs] at h2
          exact ENNReal.ofReal_le_ofReal h2
      _ < ⊤ := by
          simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top
  have hT := torusSquareSumHolds_proof g hg.aestronglyMeasurable hfin
  have hne : ∑' ι : ℤ × ℤ, ENNReal.ofReal (‖modeAverage ι (fun τ φ (_ : Unit) => g τ φ) ()‖ ^ 2) ≠ ⊤ := by
    rw [hT]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  exact (ENNReal.summable_toReal hne).congr fun ι => ENNReal.toReal_ofReal (sq_nonneg _)

private theorem integral_exp_linear (c L : ℝ) (n : ℤ) (hL : c * L = 2 * Real.pi * n) :
    ∫ x in (0 : ℝ)..L, Complex.exp (-(((c * x : ℝ) : ℂ) * Complex.I)) = if c = 0 then (L : ℂ) else 0 := by
  split_ifs with hc
  · subst hc
    simp
  · have hc' : (-(c : ℂ) * Complex.I) ≠ 0 := by simp [hc, Complex.I_ne_zero]
    have e : ∀ x : ℝ, Complex.exp (-(((c * x : ℝ) : ℂ) * Complex.I))
        = Complex.exp ((-(c : ℂ) * Complex.I) * x) := by
      intro x
      congr 1
      push_cast
      ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc']
    have h1 : (-(c : ℂ) * Complex.I) * (L : ℂ) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have : (c : ℂ) * L = 2 * Real.pi * n := by exact_mod_cast hL
      push_cast
      linear_combination (-Complex.I) * this
    rw [h1, Complex.exp_int_mul_two_pi_mul_I]
    simp

private theorem mode_one (κ : ℤ × ℤ) :
    modeAverage κ (fun _ _ (_ : Unit) => (1 : ℝ)) () = if κ = 0 then 1 else 0 := by
  unfold modeAverage
  have e : ∀ τ φ : ℝ, Complex.exp (-(((2 * Real.pi * κ.1 * τ + κ.2 * φ : ℝ) : ℂ) * Complex.I)) * ((1 : ℝ) : ℂ)
      = Complex.exp (-((((2 * Real.pi * κ.1) * τ : ℝ) : ℂ) * Complex.I))
        * Complex.exp (-((((κ.2 : ℝ) * φ : ℝ) : ℂ) * Complex.I)) := by
    intro τ φ
    rw [Complex.ofReal_one, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [e, intervalIntegral.integral_const_mul]
  rw [integral_exp_linear (κ.2 : ℝ) (2 * Real.pi) κ.2 (by ring)]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_exp_linear (2 * Real.pi * κ.1) 1 κ.1 (by ring)]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  by_cases h1 : κ.1 = 0 <;> by_cases h2 : κ.2 = 0
  · have hk : κ = 0 := Prod.ext h1 h2
    rw [if_pos hk]
    have a1 : (2 * Real.pi * (κ.1 : ℝ)) = 0 := by rw [h1]; simp
    have a2 : (κ.2 : ℝ) = 0 := by rw [h2]; simp
    rw [if_pos a1, if_pos a2]
    push_cast
    field_simp
  · have hk : κ ≠ 0 := fun h0 => h2 (by rw [h0]; rfl)
    have h2' : (κ.2 : ℝ) ≠ 0 := by exact_mod_cast h2
    simp [h2', hk]
  · have hk : κ ≠ 0 := fun h0 => h1 (by rw [h0]; rfl)
    have h1' : (2 * Real.pi * κ.1 : ℝ) ≠ 0 := by
      have : (κ.1 : ℝ) ≠ 0 := by exact_mod_cast h1
      positivity
    simp [h1', hk]
  · have hk : κ ≠ 0 := fun h0 => h1 (by rw [h0]; rfl)
    have h1' : (2 * Real.pi * κ.1 : ℝ) ≠ 0 := by
      have : (κ.1 : ℝ) ≠ 0 := by exact_mod_cast h1
      positivity
    simp [h1', hk]

theorem mode_re_exp (μ κ : ℤ × ℤ) (z : ℂ) :
    modeAverage μ (fun τ φ (_ : Unit) =>
        (Complex.exp (((2 * Real.pi * κ.1 * τ + κ.2 * φ : ℝ) : ℂ) * Complex.I) * z).re) ()
      = ((if μ = κ then z else 0) + (if μ = -κ then (starRingEnd ℂ) z else 0)) / 2 := by
  have h := Internal.MuSmooth.mode_re_mul μ κ z (fun _ _ => (1 : ℝ)) continuous_const ()
  simp only [mul_one] at h
  rw [h, mode_one, mode_one]
  congr 1
  congr 1
  · by_cases hh : μ = κ
    · simp [hh]
    · have : μ - κ ≠ 0 := sub_ne_zero.2 hh
      simp [hh, this]
  · by_cases hh : μ = -κ
    · simp [hh]
    · have : μ + κ ≠ 0 := fun h0 => hh (eq_neg_of_add_eq_zero_left h0)
      simp [hh, this]

theorem torus_squareSum_cont (f : ℝ → ℝ → ℝ) (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (‖modeAverage ι (fun τ φ (_ : Unit) => f τ φ) ()‖ ^ 2)
      = ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (f τ φ ^ 2) := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal (f τ φ ^ 2) ≤ ENNReal.ofReal (M ^ 2) := by
    intro τ hτ φ hφ
    have hx := hM (τ, φ) ⟨hτ, hφ⟩
    rw [Real.norm_eq_abs] at hx
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ |f τ φ| := abs_nonneg _
    nlinarith [sq_abs (f τ φ)]
  have hfin : (∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (f τ φ ^ 2)) < ⊤ := by
    calc (∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (f τ φ ^ 2))
        ≤ ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (M ^ 2) :=
          setLIntegral_mono' measurableSet_Icc fun τ hτ =>
            setLIntegral_mono' measurableSet_Icc fun φ hφ => hb τ hτ φ hφ
      _ < ⊤ := by
          simp only [setLIntegral_const, Real.volume_Icc]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top
  exact torusSquareSumHolds_proof f hf.aestronglyMeasurable hfin

def truncGrad (F : Finset (ℤ × ℤ)) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) (ij : Fin 3 × Fin 3)
    (τ φ : ℝ) : ℝ :=
  ∑ κ ∈ F, (Complex.exp (((2 * Real.pi * κ.1 * τ + κ.2 * φ : ℝ) : ℂ) * Complex.I)
    * modeGrad κ (gradField v) σ y ij).re

def orbitFrame (h : HarmonicBounds) (W : ℝ → Space → Space) (a σ : ℝ) (y : Space) (j : Fin 3) (τ φ : ℝ) : ℝ :=
  ((1 / 2 : ℝ) • y - a • turnDir y) j + ∑ β ∈ h.harmonics,
    (Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel β W σ y j).re

def truncProduct (F : Finset (ℤ × ℤ)) (h : HarmonicBounds) (W v : ℝ → Space → Space) (a σ : ℝ) (y : Space)
    (i : Fin 3) (τ φ : ℝ) : ℝ :=
  ∑ j : Fin 3, truncGrad F v σ y (i, j) τ φ * orbitFrame h W a σ y j τ φ

theorem truncGrad_continuous (F : Finset (ℤ × ℤ)) (v : ℝ → Space → Space) (σ : ℝ) (y : Space)
    (ij : Fin 3 × Fin 3) : Continuous (fun p : ℝ × ℝ => truncGrad F v σ y ij p.1 p.2) := by
  unfold truncGrad
  fun_prop

theorem truncProduct_continuous (F : Finset (ℤ × ℤ)) (h : HarmonicBounds) (W v : ℝ → Space → Space)
    (a σ : ℝ) (y : Space) (i : Fin 3) : Continuous (fun p : ℝ × ℝ => truncProduct F h W v a σ y i p.1 p.2) := by
  unfold truncProduct truncGrad orbitFrame
  fun_prop

private theorem modeAverage_finset_sum {κ : Type*} (s : Finset κ) (f : κ → ℝ → ℝ → ℝ)
    (hf : ∀ k, Continuous (fun p : ℝ × ℝ => f k p.1 p.2)) (μ : ℤ × ℤ) :
    modeAverage μ (fun τ φ (_ : Unit) => ∑ k ∈ s, f k τ φ) ()
      = ∑ k ∈ s, modeAverage μ (fun τ φ (_ : Unit) => f k τ φ) () := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [modeAverage]
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [Internal.Field.modeAverage_add, ih]
    · exact hf a
    · exact continuous_finsetSum _ fun k _ => hf k

private theorem sum_neg_index (s : Finset (ℤ × ℤ)) (hs : ∀ κ ∈ s, -κ ∈ s) (f : ℤ × ℤ → ℂ) :
    ∑ κ ∈ s, f (-κ) = ∑ κ ∈ s, f κ :=
  Finset.sum_nbij' (fun κ => -κ) (fun κ => -κ) (fun κ hk => hs κ hk) (fun κ hk => hs κ hk)
    (fun κ _ => neg_neg κ) (fun κ _ => neg_neg κ) fun _ _ => rfl

theorem truncGrad_mode (F : Finset (ℤ × ℤ)) (hF : ∀ κ ∈ F, -κ ∈ F) (v : ℝ → Space → Space) (σ : ℝ)
    (y : Space) (ij : Fin 3 × Fin 3) (μ : ℤ × ℤ) :
    modeAverage μ (fun τ φ (_ : Unit) => truncGrad F v σ y ij τ φ) ()
      = if μ ∈ F then modeGrad μ (gradField v) σ y ij else 0 := by
  unfold truncGrad
  rw [modeAverage_finset_sum F _ (fun κ => by fun_prop) μ]
  simp_rw [mode_re_exp]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_ite_eq]
  have h2 : ∑ κ ∈ F, (if μ = -κ then (starRingEnd ℂ) (modeGrad κ (gradField v) σ y ij) else 0)
      = if -μ ∈ F then (starRingEnd ℂ) (modeGrad (-μ) (gradField v) σ y ij) else 0 := by
    rw [← Finset.sum_ite_eq F (-μ) (fun κ => (starRingEnd ℂ) (modeGrad κ (gradField v) σ y ij))]
    refine Finset.sum_congr rfl fun κ _ => ?_
    by_cases hk : μ = -κ
    · rw [if_pos hk, if_pos (by rw [hk, neg_neg])]
    · rw [if_neg hk, if_neg (fun h' => hk (by rw [← h', neg_neg]))]
  rw [h2]
  have hc : (starRingEnd ℂ) (modeGrad (-μ) (gradField v) σ y ij) = modeGrad μ (gradField v) σ y ij := by
    rw [Internal.MuSmooth.modeGrad_neg, Complex.conj_conj]
  rw [hc]
  by_cases hμ : μ ∈ F
  · rw [if_pos hμ, if_pos (hF μ hμ)]
    ring
  · have hn : -μ ∉ F := fun h' => hμ (by simpa using hF (-μ) h')
    rw [if_neg hμ, if_neg hn]
    ring

private theorem truncProduct_term (F : Finset (ℤ × ℤ)) (hF : ∀ κ ∈ F, -κ ∈ F) (h : HarmonicBounds)
    (W v : ℝ → Space → Space) (a σ : ℝ) (y : Space) (ι : ℤ × ℤ) (i j : Fin 3) :
    modeAverage ι (fun τ φ (_ : Unit) => truncGrad F v σ y (i, j) τ φ * orbitFrame h W a σ y j τ φ) ()
      = ((((1 / 2 : ℝ) • y - a • turnDir y) j : ℝ) : ℂ) * (if ι ∈ F then modeGrad ι (gradField v) σ y (i, j) else 0)
        + ∑ β ∈ h.harmonics, (modeVel β W σ y j * (if ι - β ∈ F then modeGrad (ι - β) (gradField v) σ y (i, j) else 0)
          + (starRingEnd ℂ) (modeVel β W σ y j)
            * (if ι + β ∈ F then modeGrad (ι + β) (gradField v) σ y (i, j) else 0)) / 2 := by
  have hu := truncGrad_continuous F v σ y (i, j)
  have e : (fun τ φ (_ : Unit) => truncGrad F v σ y (i, j) τ φ * orbitFrame h W a σ y j τ φ)
      = fun τ φ (_ : Unit) => (((1 / 2 : ℝ) • y - a • turnDir y) j) * truncGrad F v σ y (i, j) τ φ
        + ∑ β ∈ h.harmonics, (Complex.exp (((2 * Real.pi * β.1 * τ + β.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeVel β W σ y j).re * truncGrad F v σ y (i, j) τ φ := by
    funext τ φ _
    unfold orbitFrame
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun β _ => mul_comm _ _
  have hc2 : ∀ β : ℤ × ℤ, Continuous (fun p : ℝ × ℝ =>
      (Complex.exp (((2 * Real.pi * β.1 * p.1 + β.2 * p.2 : ℝ) : ℂ) * Complex.I) * modeVel β W σ y j).re
        * truncGrad F v σ y (i, j) p.1 p.2) := fun β => by
    refine Continuous.mul ?_ hu
    fun_prop
  rw [e, Internal.Field.modeAverage_add, Internal.Field.modeAverage_const_mul,
    modeAverage_finset_sum h.harmonics _ hc2 ι, truncGrad_mode F hF v σ y (i, j) ι]
  · congr 1
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Internal.MuSmooth.mode_re_mul ι β (modeVel β W σ y j) (fun τ φ => truncGrad F v σ y (i, j) τ φ) hu (),
      truncGrad_mode F hF v σ y (i, j), truncGrad_mode F hF v σ y (i, j)]
  · exact continuous_const.mul hu
  · exact continuous_finsetSum _ fun β _ => hc2 β

theorem truncProduct_mode (F : Finset (ℤ × ℤ)) (hF : ∀ κ ∈ F, -κ ∈ F) (h : HarmonicBounds)
    (hH : ∀ β ∈ h.harmonics, -β ∈ h.harmonics) (T : Set (ℤ × ℤ)) (W v : ℝ → Space → Space) (a σ : ℝ)
    (y : Space) (ι : ℤ × ℤ) (hι : ι ∈ F) (hFι : ∀ α ∈ h.harmonics, (PieceWeights.inPiece T (ι - α) ↔ ι - α ∈ F))
    (i : Fin 3) :
    modeAverage ι (fun τ φ (_ : Unit) => truncProduct F h W v a σ y i τ φ) () = innerMode h T W v a σ y ι i := by
  unfold truncProduct
  simp only [innerMode]
  rw [modeAverage_finset_sum Finset.univ _ (fun j => (truncGrad_continuous F v σ y (i, j)).mul
    (by unfold orbitFrame; fun_prop)) ι]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [truncProduct_term F hF h W v a σ y ι i j, if_pos hι]
  congr 1
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hneg : ∑ β ∈ h.harmonics, (starRingEnd ℂ) (modeVel β W σ y j)
        * (if ι + β ∈ F then modeGrad (ι + β) (gradField v) σ y (i, j) else 0)
      = ∑ β ∈ h.harmonics, modeVel β W σ y j
        * (if ι - β ∈ F then modeGrad (ι - β) (gradField v) σ y (i, j) else 0) := by
    rw [← sum_neg_index h.harmonics hH]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Internal.SmoothPieceMuDivergence.modeVel_neg, Complex.conj_conj, ← sub_eq_add_neg]
  rw [hneg, add_self_div_two]
  refine Finset.sum_congr rfl fun α hα => ?_
  by_cases hF' : ι - α ∈ F
  · rw [if_pos hF', if_pos ((hFι α hα).2 hF')]
  · rw [if_neg hF', if_neg (fun hp => hF' ((hFι α hα).1 hp)), mul_zero]

theorem lintegral_box_sum {κ : Type*} (s : Finset κ) (f : κ → ℝ → ℝ → ℝ≥0∞)
    (hf : ∀ k, Measurable (fun p : ℝ × ℝ => f k p.1 p.2)) :
    ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ∑ k ∈ s, f k τ φ
      = ∑ k ∈ s, ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f k τ φ := by
  have h1 : ∀ τ, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ∑ k ∈ s, f k τ φ
      = ∑ k ∈ s, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f k τ φ := fun τ =>
    lintegral_finsetSum s fun k _ => (hf k).comp measurable_prodMk_left
  simp_rw [h1]
  exact lintegral_finsetSum s fun k _ => (hf k).lintegral_prod_right'

theorem lintegral_box_const_mul (c : ℝ≥0∞) (hc : c ≠ ⊤) (f : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), c * f τ φ
      = c * ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), f τ φ := by
  simp_rw [lintegral_const_mul' _ _ hc]

theorem modeSq_sum_le_of_pointwise (P : Fin 3 → ℝ → ℝ → ℝ) (G : Fin 3 × Fin 3 → ℝ → ℝ → ℝ)
    (hP : ∀ i, Continuous (fun p : ℝ × ℝ => P i p.1 p.2)) (hG : ∀ ij, Continuous (fun p : ℝ × ℝ => G ij p.1 p.2))
    (K : ℝ) (hK : 0 ≤ K) (hpt : ∀ τ φ, ∑ i, P i τ φ ^ 2 ≤ K * ∑ ij, G ij τ φ ^ 2) (S : Finset (ℤ × ℤ)) :
    ∑ ι ∈ S, ∑ i, ENNReal.ofReal (‖modeAverage ι (fun τ φ (_ : Unit) => P i τ φ) ()‖ ^ 2)
      ≤ ENNReal.ofReal K * ∑ ij, ∑' μ : ℤ × ℤ, ENNReal.ofReal (‖modeAverage μ (fun τ φ (_ : Unit) => G ij τ φ) ()‖ ^ 2) := by
  have mP : ∀ i, Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (P i p.1 p.2 ^ 2)) := fun i =>
    ENNReal.measurable_ofReal.comp ((hP i).pow 2).measurable
  have mG : ∀ ij, Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (G ij p.1 p.2 ^ 2)) := fun ij =>
    ENNReal.measurable_ofReal.comp ((hG ij).pow 2).measurable
  have hpt' : ∀ τ φ, ∑ i, ENNReal.ofReal (P i τ φ ^ 2) ≤ ENNReal.ofReal K * ∑ ij, ENNReal.ofReal (G ij τ φ ^ 2) := by
    intro τ φ
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _), ← ENNReal.ofReal_sum_of_nonneg (fun ij _ => sq_nonneg _),
      ← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (hpt τ φ)
  calc ∑ ι ∈ S, ∑ i, ENNReal.ofReal (‖modeAverage ι (fun τ φ (_ : Unit) => P i τ φ) ()‖ ^ 2)
      = ∑ i, ∑ ι ∈ S, ENNReal.ofReal (‖modeAverage ι (fun τ φ (_ : Unit) => P i τ φ) ()‖ ^ 2) := Finset.sum_comm
    _ ≤ ∑ i, ∑' ι : ℤ × ℤ, ENNReal.ofReal (‖modeAverage ι (fun τ φ (_ : Unit) => P i τ φ) ()‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => ENNReal.sum_le_tsum S
    _ = ∑ i, ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (P i τ φ ^ 2) := Finset.sum_congr rfl fun i _ => torus_squareSum_cont (P i) (hP i)
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∑ i, ENNReal.ofReal (P i τ φ ^ 2) := by
        rw [lintegral_box_sum _ _ mP, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal K * ∑ ij, ENNReal.ofReal (G ij τ φ ^ 2) := by
        gcongr with τ φ
        exact hpt' τ φ
    _ = ENNReal.ofReal K * ∑ ij, ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Set.Icc (0 : ℝ) 1,
          ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (G ij τ φ ^ 2) := by
        rw [lintegral_box_const_mul _ ENNReal.ofReal_ne_top, lintegral_box_sum _ _ mG, ← Finset.mul_sum]
        ring
    _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun ij _ => (torus_squareSum_cont (G ij) (hG ij)).symm

theorem rot_sub_of (φ : ℝ) (x z : Space) : axialRot φ (x - z) = axialRot φ x - axialRot φ z := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

theorem turnDir_rot (ψ : ℝ) (x : Space) : axialRot ψ (turnDir x) = turnDir (axialRot ψ x) := by
  ext j
  fin_cases j <;> simp [axialRot, turnDir, unitVector] <;> ring

theorem rot_frame_eq (W : ℝ → Space → Space) (a σ τ φ : ℝ) (y : Space) :
    axialRot (-φ) (W (σ + τ) (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y - a • turnDir (axialRot φ y))
      = axialRot (-φ) (W (σ + τ) (axialRot φ y)) + ((1 / 2 : ℝ) • y - a • turnDir y) := by
  have hb : axialRot (-φ) (axialRot φ y) = y := by
    have := RotationInternal.axialRot_self_neg (-φ) y
    rwa [neg_neg] at this
  rw [rot_sub_of, Internal.Field.axialRot_add, Internal.Field.axialRot_smul, Internal.Field.axialRot_smul,
    turnDir_rot, hb]
  abel

section Bounds

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nM)
    (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds)

include hm hW hWp hWdiv hWdecay hwb hv hPars hDer hRotM hSolenoidal hSP hSsp

private theorem mode_split (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (innerField P W v) σ y = fun i =>
      ((PieceWeights.frameFreq P (m.muP β).frame ι : ℂ) * Complex.I) * modeVel ι v σ y i
        + ((m.muP β).frame : ℂ) * axisTurn (modeVel ι v σ y) i + (1 / 2 : ℂ) * modeVel ι v σ y i
        + modeVel ι (frameAdvection W v (m.muP β).frame) σ y i + modeVel ι (negSumSecondPartialsField v) σ y i :=
  mode_split_of hv hW.continuous (m.muP β).frame ι σ y

private theorem freq_integrable (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hp := hSP P v hv
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ (volume : Measure (ℝ × Space)) := ModeL2Internal.slab_ac
  have hV := ModeL2Internal.integrable_cnormSq_modeVel hPars (Internal.SmoothWeightSplit.scaledField_square hv) ι
  set c := |PieceWeights.frameFreq P (m.muP β).frame ι|
  have hc0 : 0 ≤ c := abs_nonneg _
  have hind0 : 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) := by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hind1 : ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) ≤ 1 := by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hm1 : AEStronglyMeasurable (fun z : ℝ × Space => freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    unfold freqTerm
    have a1 : Measurable (fun z : ℝ × Space => (m.muP β).wt z.2) := hK.continuous.measurable.comp measurable_snd
    exact ((((aemeasurable_const.mul a1.aemeasurable).mul aemeasurable_const).mul
      (((Internal.PieceAbsorb.aem_velAmp hp.measurable_velocity ι).mono_ac hac).pow_const 2))).aestronglyMeasurable
  refine (hV.const_mul (c * (4 * B))).mono' hm1 (ae_of_all _ fun z => ?_)
  have hu0 : 0 ≤ velAmp v ι z.1 z.2 := Real.sqrt_nonneg _
  have ht : 0 < 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
  have hw := Internal.SmoothPieceEps.cnormSq_modeVel_weighted v ι z.1 z.2
  obtain ⟨b1, b2, -⟩ := hB β z.2
  have hφt : (1 + ‖z.2‖) ^ 2 * (m.muP β).wt z.2 ≤ 4 * B := by
    nlinarith [sq_nonneg (‖z.2‖ - 1), hφ0 z.2, norm_nonneg z.2]
  have hf0 : 0 ≤ freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 := by
    unfold freqTerm
    exact mul_nonneg (mul_nonneg (mul_nonneg hind0 (hφ0 _)) hc0) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hf0]
  show _ ≤ c * (4 * B) * cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2)
  rw [hw]
  unfold freqTerm
  set u := velAmp v ι z.1 z.2
  set t := 1 + ‖z.2‖
  set q := (m.muP β).wt z.2
  have e : u ^ 2 = t ^ 2 * (u / t) ^ 2 := by field_simp
  have hq0 := hφ0 z.2
  calc ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * q * c * u ^ 2 ≤ 1 * q * c * u ^ 2 := by
        gcongr
    _ = c * (t ^ 2 * q) * (u / t) ^ 2 := by rw [e]; ring
    _ ≤ c * (4 * B) * (u / t) ^ 2 := by gcongr

private theorem frameAdvection_square :
    ModeL2Internal.IsSquareField (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) := by
  obtain ⟨D, hD⟩ := hWdecay
  have hD0 : 0 ≤ D := by
    have := hD 0 0 0 (by norm_num)
    exact le_trans (norm_nonneg _) (this.trans (by simp))
  have hG := gradSlice_continuous hv
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have htd : Continuous turnDir := by
    unfold turnDir
    fun_prop
  have hVc : Continuous (fun z : ℝ × Space => W z.1 z.2 + (1 / 2 : ℝ) • z.2 - (m.muP β).frame • turnDir z.2) :=
    (hWc.add ((continuous_const (y := (1 / 2 : ℝ))).smul continuous_snd)).sub
      ((continuous_const (y := (m.muP β).frame)).smul (htd.comp continuous_snd))
  have hAc : Continuous (fun z : ℝ × Space => frameAdvection W v (m.muP β).frame z.1 z.2) := by
    unfold frameAdvection
    exact (hG.clm_apply hVc)
  refine ⟨?_, ?_, ?_⟩
  · have hi : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖)⁻¹) :=
      Continuous.inv₀ (by fun_prop) (fun z => by show (1 : ℝ) + ‖z.2‖ ≠ 0; positivity)
    exact (hi.smul hAc).aestronglyMeasurable
  · intro σ y
    have hvp : v (σ + 1) = v σ := funext (hv.periodic σ)
    unfold frameAdvection
    beta_reduce
    rw [hvp, hWp σ y]
  · set C : ℝ := D + 1 / 2 + 2 * |(m.muP β).frame|
    have hC0 : 0 ≤ C := by positivity
    have hle : ∀ σ y, ‖(1 + ‖y‖)⁻¹ • frameAdvection W v (m.muP β).frame σ y‖ ^ 2
        ≤ C ^ 2 * ‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2 := by
      intro σ y
      have ht : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
      have hW0 : ‖W σ y‖ ≤ D := by
        have := hD σ y 0 (by norm_num)
        rw [norm_iteratedFDeriv_zero] at this
        refine this.trans ?_
        rw [div_le_iff₀ (by positivity)]
        have : 1 ≤ (1 + ‖y‖) ^ (0 + 1) := by simp
        nlinarith
      have hV : ‖W σ y + (1 / 2 : ℝ) • y - (m.muP β).frame • turnDir y‖ ≤ C * (1 + ‖y‖) := by
        have h1 := Internal.SmoothPieceEps.norm_perp_le y
        have h2 : ‖turnDir y‖ ≤ 2 * ‖y‖ := h1
        calc ‖W σ y + (1 / 2 : ℝ) • y - (m.muP β).frame • turnDir y‖
            ≤ ‖W σ y‖ + ‖(1 / 2 : ℝ) • y‖ + ‖(m.muP β).frame • turnDir y‖ := by
              refine (norm_sub_le _ _).trans ?_
              exact add_le_add (norm_add_le _ _) le_rfl
          _ ≤ D + 1 / 2 * ‖y‖ + |(m.muP β).frame| * (2 * ‖y‖) := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
              gcongr
          _ ≤ C * (1 + ‖y‖) := by
              simp only [C]
              nlinarith [norm_nonneg y, abs_nonneg (m.muP β).frame]
      have hA : ‖frameAdvection W v (m.muP β).frame σ y‖ ≤ ‖fderiv ℝ (v σ) y‖ * (C * (1 + ‖y‖)) := by
        unfold frameAdvection
        exact ((fderiv ℝ (v σ) y).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
      rw [norm_iteratedFDeriv_one, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht)]
      have hA' : (1 + ‖y‖)⁻¹ * ‖frameAdvection W v (m.muP β).frame σ y‖ ≤ C * ‖fderiv ℝ (v σ) y‖ := by
        rw [inv_mul_le_iff₀ ht]
        nlinarith [norm_nonneg (fderiv ℝ (v σ) y)]
      have h0 : 0 ≤ (1 + ‖y‖)⁻¹ * ‖frameAdvection W v (m.muP β).frame σ y‖ :=
        mul_nonneg (inv_nonneg.2 ht.le) (norm_nonneg _)
      calc ((1 + ‖y‖)⁻¹ * ‖frameAdvection W v (m.muP β).frame σ y‖) ^ 2 ≤ (C * ‖fderiv ℝ (v σ) y‖) ^ 2 :=
            pow_le_pow_left₀ h0 hA' 2
        _ = C ^ 2 * ‖fderiv ℝ (v σ) y‖ ^ 2 := by ring
    have hg := hv.derivatives_finite 1 le_rfl
    unfold periodLIntegral at hg ⊢
    calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖(1 + ‖y‖)⁻¹ • frameAdvection W v (m.muP β).frame σ y‖ ^ 2))
        ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2) :=
          lintegral_mono fun σ => lintegral_mono fun y => by
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (hle σ y)
      _ = ENNReal.ofReal (C ^ 2) * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          funext σ
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg

private theorem frameAdvection_integrable (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hB0 : 0 ≤ B := (hφ0 0).trans (hB β 0).1
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ (volume : Measure (ℝ × Space)) := ModeL2Internal.slab_ac
  have hAsq := frameAdvection_square m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  have hV := ModeL2Internal.integrable_cnormSq_modeVel hPars (Internal.SmoothWeightSplit.scaledField_square hv) ι
  have hAi := ModeL2Internal.integrable_cnormSq_modeVel hPars hAsq ι
  have hAc : Continuous (fun z : ℝ × Space => frameAdvection W v (m.muP β).frame z.1 z.2) := by
    have hG := gradSlice_continuous hv
    have htd : Continuous turnDir := by
      unfold turnDir
      fun_prop
    have hVc : Continuous (fun z : ℝ × Space => W z.1 z.2 + (1 / 2 : ℝ) • z.2 - (m.muP β).frame • turnDir z.2) :=
      (hW.continuous.add ((continuous_const (y := (1 / 2 : ℝ))).smul continuous_snd)).sub
        ((continuous_const (y := (m.muP β).frame)).smul (htd.comp continuous_snd))
    unfold frameAdvection
    exact hG.clm_apply hVc
  have hx : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι v z.1 z.2 i) volume :=
    fun i => ModeL2Internal.aestronglyMeasurable_modeVel hv.smooth.continuous.aestronglyMeasurable ι i
  have hl : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2 i) volume :=
    fun i => ModeL2Internal.aestronglyMeasurable_modeVel hAc.aestronglyMeasurable ι i
  have hc := ModeL2Internal.aestronglyMeasurable_cdot hx hl
  have hw : Continuous (fun z : ℝ × Space => Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul (hK.continuous.comp continuous_snd)))
  have hf : AEStronglyMeasurable (fun z : ℝ × Space => fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2) volume :=
    Complex.continuous_re.comp_aestronglyMeasurable (hw.aestronglyMeasurable.mul hc)
  have hs1 : |PieceWeights.sgn (m.muP β).modes ι| ≤ 1 := by
    unfold PieceWeights.sgn
    split_ifs <;> norm_num
  refine ((hV.add hAi).const_mul (4 * B)).mono' (hf.mono_ac hac) (ae_of_all _ fun z => ?_)
  have ht : 0 < 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
  have hw' := Internal.SmoothPieceEps.cnormSq_modeVel_weighted v ι z.1 z.2
  have hwA := Internal.SmoothPieceEps.cnormSq_modeVel_weighted (frameAdvection W v (m.muP β).frame) ι z.1 z.2
  obtain ⟨b1, b2, -⟩ := hB β z.2
  have hφt : (1 + ‖z.2‖) ^ 2 * (m.muP β).wt z.2 ≤ 4 * B := by
    nlinarith [sq_nonneg (‖z.2‖ - 1), hφ0 z.2, norm_nonneg z.2]
  have hμ : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| ≤ (m.muP β).wt z.2 := by
    rw [abs_mul, abs_of_nonneg (hφ0 z.2)]
    exact mul_le_of_le_one_left (hφ0 z.2) hs1
  have h1 := Internal.FieldModes.abs_re_I_mul_le (PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2)
    (cdot (modeVel ι v z.1 z.2) (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2))
  have h2 := Internal.FieldModes.norm_cdot_le (modeVel ι v z.1 z.2) (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2)
  have hxq : cnormSq (modeVel ι v z.1 z.2) = velAmp v ι z.1 z.2 ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
  have haq : cnormSq (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2) = velAmp (frameAdvection W v (m.muP β).frame) ι z.1 z.2 ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
  rw [Real.norm_eq_abs]
  show |(Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ)
      * cdot (modeVel ι v z.1 z.2) (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2)).re|
    ≤ 4 * B * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2)
      + cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2))
  rw [hw', hwA]
  rw [hxq, haq] at h2
  set u := velAmp v ι z.1 z.2
  set r := velAmp (frameAdvection W v (m.muP β).frame) ι z.1 z.2
  set t := 1 + ‖z.2‖
  set q := (m.muP β).wt z.2
  have hq0 := hφ0 z.2
  have e : u ^ 2 = t ^ 2 * (u / t) ^ 2 := by field_simp
  have e' : r ^ 2 = t ^ 2 * (r / t) ^ 2 := by field_simp
  have k1 : q * u ^ 2 ≤ 4 * B * (u / t) ^ 2 := by
    rw [e]
    calc q * (t ^ 2 * (u / t) ^ 2) = (t ^ 2 * q) * (u / t) ^ 2 := by ring
      _ ≤ 4 * B * (u / t) ^ 2 := by gcongr
  have k2 : q * r ^ 2 ≤ 4 * B * (r / t) ^ 2 := by
    rw [e']
    calc q * (t ^ 2 * (r / t) ^ 2) = (t ^ 2 * q) * (r / t) ^ 2 := by ring
      _ ≤ 4 * B * (r / t) ^ 2 := by gcongr
  have h3 : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| * ‖cdot (modeVel ι v z.1 z.2) (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2)‖
      ≤ q * ((u ^ 2 + r ^ 2) / 2) :=
    mul_le_mul hμ h2 (norm_nonneg _) hq0
  nlinarith [sq_nonneg (u / t), sq_nonneg (r / t)]

private theorem turn_integrable (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ (volume : Measure (ℝ × Space)) := ModeL2Internal.slab_ac
  have hV := ModeL2Internal.integrable_cnormSq_modeVel hPars (Internal.SmoothWeightSplit.scaledField_square hv) ι
  have hx : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι v z.1 z.2 i) volume :=
    fun i => ModeL2Internal.aestronglyMeasurable_modeVel hv.smooth.continuous.aestronglyMeasurable ι i
  have hJ : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => axisTurn (modeVel ι v z.1 z.2) i) volume := by
    intro i
    fin_cases i
    · exact (hx 1).neg
    · exact hx 0
    · exact aestronglyMeasurable_const
  have hc := ModeL2Internal.aestronglyMeasurable_cdot hx hJ
  have hw : Continuous (fun z : ℝ × Space => Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul (hK.continuous.comp continuous_snd)))
  have hf : AEStronglyMeasurable (fun z : ℝ × Space => turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2) volume :=
    Complex.continuous_re.comp_aestronglyMeasurable (hw.aestronglyMeasurable.mul (aestronglyMeasurable_const.mul hc))
  have hs1 : |PieceWeights.sgn (m.muP β).modes ι| ≤ 1 := by
    unfold PieceWeights.sgn
    split_ifs <;> norm_num
  refine (hV.const_mul (|(m.muP β).frame| * (4 * B))).mono' (hf.mono_ac hac) (ae_of_all _ fun z => ?_)
  have hw' := Internal.SmoothPieceEps.cnormSq_modeVel_weighted v ι z.1 z.2
  obtain ⟨b1, b2, -⟩ := hB β z.2
  have hφt : (1 + ‖z.2‖) ^ 2 * (m.muP β).wt z.2 ≤ 4 * B := by
    nlinarith [sq_nonneg (‖z.2‖ - 1), hφ0 z.2, norm_nonneg z.2]
  have hμ : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| ≤ (m.muP β).wt z.2 := by
    rw [abs_mul, abs_of_nonneg (hφ0 z.2)]
    exact mul_le_of_le_one_left (hφ0 z.2) hs1
  set x := modeVel ι v z.1 z.2
  have hJx : cnormSq (axisTurn x) ≤ cnormSq x := by
    unfold cnormSq axisTurn
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, norm_neg, norm_zero]
    nlinarith [sq_nonneg ‖x 2‖]
  have h1 := Internal.FieldModes.abs_re_I_mul_le (PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2)
    (((m.muP β).frame : ℂ) * cdot x (axisTurn x))
  have h2 := Internal.FieldModes.norm_cdot_le x (axisTurn x)
  have hx0 : 0 ≤ cnormSq x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hxq : cnormSq x = velAmp v ι z.1 z.2 ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
  rw [Real.norm_eq_abs]
  show |(Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ) * (((m.muP β).frame : ℂ) * cdot x (axisTurn x))).re|
    ≤ |(m.muP β).frame| * (4 * B) * cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2)
  rw [hw']
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
  set u := velAmp v ι z.1 z.2
  set t := 1 + ‖z.2‖
  set q := (m.muP β).wt z.2
  have ht : 0 < t := by simp only [t]; linarith [norm_nonneg z.2]
  have hq0 := hφ0 z.2
  have e : u ^ 2 = t ^ 2 * (u / t) ^ 2 := by field_simp
  have k1 : q * cnormSq x ≤ 4 * B * (u / t) ^ 2 := by
    rw [hxq, e]
    calc q * (t ^ 2 * (u / t) ^ 2) = (t ^ 2 * q) * (u / t) ^ 2 := by ring
      _ ≤ 4 * B * (u / t) ^ 2 := by gcongr
  have hcd : ‖cdot x (axisTurn x)‖ ≤ cnormSq x := by linarith
  have h3 : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| * (|(m.muP β).frame| * ‖cdot x (axisTurn x)‖) ≤ q * (|(m.muP β).frame| * cnormSq x) :=
    mul_le_mul hμ (mul_le_mul_of_nonneg_left hcd (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hq0
  have ha0 := abs_nonneg (m.muP β).frame
  nlinarith [mul_le_mul_of_nonneg_left k1 ha0]

private theorem advection_integrable (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
  (turn_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι).add
    (frameAdvection_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι)

private theorem sumSecondPartials_integrable (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hB0 : 0 ≤ B := (hφ0 0).trans (hB β 0).1
  have hp := hSP P v hv
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ (volume : Measure (ℝ × Space)) := ModeL2Internal.slab_ac
  have hLsq : ModeL2Internal.IsSquareField (negSumSecondPartialsField v) := by
    refine ⟨(negSumSecondPartialsField_continuous hv).aestronglyMeasurable, fun σ y => ?_, ?_⟩
    · unfold negSumSecondPartialsField
      rw [hp.periodic_secondDeriv σ y]
    · simpa [negSumSecondPartialsField, norm_neg] using hp.sumSecondPartials_finite
  have hV := ModeL2Internal.integrable_cnormSq_modeVel hPars (Internal.SmoothWeightSplit.scaledField_square hv) ι
  have hLi := ModeL2Internal.integrable_cnormSq_modeVel hPars hLsq ι
  have hx : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι v z.1 z.2 i) volume :=
    fun i => ModeL2Internal.aestronglyMeasurable_modeVel hv.smooth.continuous.aestronglyMeasurable ι i
  have hl : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι (negSumSecondPartialsField v) z.1 z.2 i) volume :=
    fun i => ModeL2Internal.aestronglyMeasurable_modeVel (negSumSecondPartialsField_continuous hv).aestronglyMeasurable ι i
  have hc := ModeL2Internal.aestronglyMeasurable_cdot hx hl
  have hw : Continuous (fun z : ℝ × Space => Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul (hK.continuous.comp continuous_snd)))
  have hf : AEStronglyMeasurable (fun z : ℝ × Space => fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2) volume :=
    Complex.continuous_re.comp_aestronglyMeasurable (hw.aestronglyMeasurable.mul hc)
  have hs1 : |PieceWeights.sgn (m.muP β).modes ι| ≤ 1 := by
    unfold PieceWeights.sgn
    split_ifs <;> norm_num
  refine ((hV.add hLi).const_mul (4 * B)).mono' (hf.mono_ac hac) (ae_of_all _ fun z => ?_)
  have ht : 0 < 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
  have hw' := Internal.SmoothPieceEps.cnormSq_modeVel_weighted v ι z.1 z.2
  obtain ⟨b1, b2, -⟩ := hB β z.2
  have hφt : (1 + ‖z.2‖) ^ 2 * (m.muP β).wt z.2 ≤ 4 * B := by
    nlinarith [sq_nonneg (‖z.2‖ - 1), hφ0 z.2, norm_nonneg z.2]
  have hμ : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| ≤ (m.muP β).wt z.2 := by
    rw [abs_mul, abs_of_nonneg (hφ0 z.2)]
    exact mul_le_of_le_one_left (hφ0 z.2) hs1
  have h1 := Internal.FieldModes.abs_re_I_mul_le (PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2)
    (cdot (modeVel ι v z.1 z.2) (modeVel ι (negSumSecondPartialsField v) z.1 z.2))
  have h2 := Internal.FieldModes.norm_cdot_le (modeVel ι v z.1 z.2) (modeVel ι (negSumSecondPartialsField v) z.1 z.2)
  have hxq : cnormSq (modeVel ι v z.1 z.2) = velAmp v ι z.1 z.2 ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
  have hL0 : 0 ≤ cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hx0 : 0 ≤ cnormSq (modeVel ι v z.1 z.2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_eq_abs]
  show |(Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ)
      * cdot (modeVel ι v z.1 z.2) (modeVel ι (negSumSecondPartialsField v) z.1 z.2)).re|
    ≤ 4 * B * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2)
      + cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2))
  rw [hw']
  set u := velAmp v ι z.1 z.2
  set t := 1 + ‖z.2‖
  set q := (m.muP β).wt z.2
  have hq0 := hφ0 z.2
  have e : u ^ 2 = t ^ 2 * (u / t) ^ 2 := by field_simp
  have hqB : q ≤ B := b1
  have k1 : q * cnormSq (modeVel ι v z.1 z.2) ≤ 4 * B * (u / t) ^ 2 := by
    rw [hxq, e]
    calc q * (t ^ 2 * (u / t) ^ 2) = (t ^ 2 * q) * (u / t) ^ 2 := by ring
      _ ≤ 4 * B * (u / t) ^ 2 := by gcongr
  have k2 : q * cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2) ≤ 4 * B * cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2) := by
    have : q ≤ 4 * B := by linarith
    exact mul_le_mul_of_nonneg_right this hL0
  have h3 : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| * ‖cdot (modeVel ι v z.1 z.2) (modeVel ι (negSumSecondPartialsField v) z.1 z.2)‖
      ≤ q * ((cnormSq (modeVel ι v z.1 z.2) + cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2)) / 2) :=
    mul_le_mul hμ h2 (norm_nonneg _) hq0
  nlinarith [sq_nonneg (u / t)]

private theorem rest_integrable (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ∧
      Integrable (fun z : ℝ × Space => fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
  ⟨advection_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι,
    sumSecondPartials_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι⟩

private theorem pairing_integrable (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ∧
      Integrable (fun z : ℝ × Space => (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ∧
      Integrable (fun z : ℝ × Space => fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
  ⟨freq_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι,
    rest_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι⟩

private theorem freq_tsum_eq (hA : freqSeries P (m.muP β).modes (m.muP β).wt (m.muP β).frame v < ⊤) :
    Summable (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y)
      ∧ ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y
        = (freqSeries P (m.muP β).modes (m.muP β).wt (m.muP β).frame v).toReal := by
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hnn : ∀ ι σ y, 0 ≤ freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y := by
    intro ι σ y
    unfold freqTerm
    have hind0 : 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) := by
      unfold ModeWeights.ind; split_ifs <;> norm_num
    exact mul_nonneg (mul_nonneg (mul_nonneg hind0 (hφ0 _)) (abs_nonneg _)) (sq_nonneg _)
  have hI := fun ι => freq_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι
  have hF : ∀ ι : ℤ × ℤ, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    fun ι => (hI ι).aemeasurable.ennreal_ofReal
  have ha0 : ∀ ι : ℤ × ℤ, 0 ≤ ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y :=
    fun ι => integral_nonneg fun σ => integral_nonneg fun y => hnn ι σ y
  have he : ∀ ι : ℤ × ℤ, ENNReal.ofReal (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y)
      = ∫⁻ z, ENNReal.ofReal (freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    intro ι
    rw [← integral_prod _ (hI ι)]
    exact ofReal_integral_eq_lintegral_ofReal (hI ι) (ae_of_all _ fun z => hnn ι z.1 z.2)
  have e1 := lintegral_prod (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (ν := (volume : Measure Space))
    (fun z : ℝ × Space => ∑' ι : ℤ × ℤ, ENNReal.ofReal (freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2)) (AEMeasurable.tsum hF)
  have hS : freqSeries P (m.muP β).modes (m.muP β).wt (m.muP β).frame v
      = ∑' ι : ℤ × ℤ, ENNReal.ofReal (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y) := by
    unfold freqSeries
    rw [← e1, lintegral_tsum hF]
    exact tsum_congr fun ι => (he ι).symm
  have hne : ∑' ι : ℤ × ℤ, ENNReal.ofReal (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y) ≠ ⊤ := hS ▸ hA.ne
  have hs := ENNReal.summable_toReal hne
  simp only [ENNReal.toReal_ofReal (ha0 _)] at hs
  refine ⟨hs, ?_⟩
  rw [hS, ENNReal.tsum_toReal_eq (fun ι => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (ha0 _)]

private theorem sumSecondPartials_term_le : ∃ B : ℝ, ∀ ι : ℤ × ℤ, ∀ z : ℝ × Space,
    ‖fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2‖ ≤ 4 * B * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2)
      + cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2)) := by
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  refine ⟨B, fun ι z => ?_⟩
  have hs1 : |PieceWeights.sgn (m.muP β).modes ι| ≤ 1 := by
    unfold PieceWeights.sgn
    split_ifs <;> norm_num
  have ht : 0 < 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
  have hw' := Internal.SmoothPieceEps.cnormSq_modeVel_weighted v ι z.1 z.2
  obtain ⟨b1, b2, -⟩ := hB β z.2
  have hφt : (1 + ‖z.2‖) ^ 2 * (m.muP β).wt z.2 ≤ 4 * B := by
    nlinarith [sq_nonneg (‖z.2‖ - 1), hφ0 z.2, norm_nonneg z.2]
  have hμ : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| ≤ (m.muP β).wt z.2 := by
    rw [abs_mul, abs_of_nonneg (hφ0 z.2)]
    exact mul_le_of_le_one_left (hφ0 z.2) hs1
  have h1 := Internal.FieldModes.abs_re_I_mul_le (PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2)
    (cdot (modeVel ι v z.1 z.2) (modeVel ι (negSumSecondPartialsField v) z.1 z.2))
  have h2 := Internal.FieldModes.norm_cdot_le (modeVel ι v z.1 z.2) (modeVel ι (negSumSecondPartialsField v) z.1 z.2)
  have hxq : cnormSq (modeVel ι v z.1 z.2) = velAmp v ι z.1 z.2 ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
  have hL0 : 0 ≤ cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hx0 : 0 ≤ cnormSq (modeVel ι v z.1 z.2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_eq_abs]
  show |(Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ)
      * cdot (modeVel ι v z.1 z.2) (modeVel ι (negSumSecondPartialsField v) z.1 z.2)).re|
    ≤ 4 * B * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2)
      + cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2))
  rw [hw']
  set u := velAmp v ι z.1 z.2
  set t := 1 + ‖z.2‖
  set q := (m.muP β).wt z.2
  have hq0 := hφ0 z.2
  have e : u ^ 2 = t ^ 2 * (u / t) ^ 2 := by field_simp
  have hqB : q ≤ B := b1
  have k1 : q * cnormSq (modeVel ι v z.1 z.2) ≤ 4 * B * (u / t) ^ 2 := by
    rw [hxq, e]
    calc q * (t ^ 2 * (u / t) ^ 2) = (t ^ 2 * q) * (u / t) ^ 2 := by ring
      _ ≤ 4 * B * (u / t) ^ 2 := by gcongr
  have k2 : q * cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2) ≤ 4 * B * cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2) := by
    have : q ≤ 4 * B := by linarith
    exact mul_le_mul_of_nonneg_right this hL0
  have h3 : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| * ‖cdot (modeVel ι v z.1 z.2) (modeVel ι (negSumSecondPartialsField v) z.1 z.2)‖
      ≤ q * ((cnormSq (modeVel ι v z.1 z.2) + cnormSq (modeVel ι (negSumSecondPartialsField v) z.1 z.2)) / 2) :=
    mul_le_mul hμ h2 (norm_nonneg _) hq0
  nlinarith [sq_nonneg (u / t)]

private theorem sumSecondPartials_family_summable :
    Summable (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y) := by
  have hp := hSP P v hv
  have hLsq : ModeL2Internal.IsSquareField (negSumSecondPartialsField v) := by
    refine ⟨(negSumSecondPartialsField_continuous hv).aestronglyMeasurable, fun σ y => ?_, ?_⟩
    · unfold negSumSecondPartialsField
      rw [hp.periodic_secondDeriv σ y]
    · simpa [negSumSecondPartialsField, norm_neg] using hp.sumSecondPartials_finite
  have hsV := ModeL2Internal.hasSum_cnormSq_modeVel hPars (Internal.SmoothWeightSplit.scaledField_square hv)
  have hsL := ModeL2Internal.hasSum_cnormSq_modeVel hPars hLsq
  obtain ⟨B, hB⟩ := sumSecondPartials_term_le m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  refine Summable.of_norm_bounded ((hsV.add hsL).summable.mul_left (4 * B)) (fun ι => ?_)
  have hI := sumSecondPartials_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι
  have hV := ModeL2Internal.integrable_cnormSq_modeVel hPars (Internal.SmoothWeightSplit.scaledField_square hv) ι
  have hLi := ModeL2Internal.integrable_cnormSq_modeVel hPars hLsq ι
  rw [← integral_prod _ hI]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono hI.norm ((hV.add hLi).const_mul (4 * B)) (fun z => hB ι z)).trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  exact integral_add hV hLi

private theorem advection_term_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : ℤ × ℤ) (z : ℝ × Space),
      ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖
        ≤ C * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2) + cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2)) := by
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hB0 : 0 ≤ B := (hφ0 0).trans (hB β 0).1
  refine ⟨(|(m.muP β).frame| + 1) * (4 * B), by positivity, fun ι z => ?_⟩
  have hs1 : |PieceWeights.sgn (m.muP β).modes ι| ≤ 1 := by
    unfold PieceWeights.sgn
    split_ifs <;> norm_num
  have hμ : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| ≤ (m.muP β).wt z.2 := by
    rw [abs_mul, abs_of_nonneg (hφ0 z.2)]
    exact mul_le_of_le_one_left (hφ0 z.2) hs1
  obtain ⟨b1, b2, -⟩ := hB β z.2
  have hφt : (1 + ‖z.2‖) ^ 2 * (m.muP β).wt z.2 ≤ 4 * B := by
    nlinarith [sq_nonneg (‖z.2‖ - 1), hφ0 z.2, norm_nonneg z.2]
  have ht : 0 < 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
  have hVpos : 0 ≤ cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA0 : 0 ≤ cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT : ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2‖ ≤ |(m.muP β).frame| * (4 * B) * cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2) := by
    have hw' := Internal.SmoothPieceEps.cnormSq_modeVel_weighted v ι z.1 z.2
    set x := modeVel ι v z.1 z.2
    have hJx : cnormSq (axisTurn x) ≤ cnormSq x := by
      unfold cnormSq axisTurn
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, norm_neg, norm_zero]
      nlinarith [sq_nonneg ‖x 2‖]
    have h1 := Internal.FieldModes.abs_re_I_mul_le (PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2)
      (((m.muP β).frame : ℂ) * cdot x (axisTurn x))
    have h2 := Internal.FieldModes.norm_cdot_le x (axisTurn x)
    have hx0 : 0 ≤ cnormSq x := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hxq : cnormSq x = velAmp v ι z.1 z.2 ^ 2 :=
      (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
    rw [Real.norm_eq_abs]
    show |(Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ) * (((m.muP β).frame : ℂ) * cdot x (axisTurn x))).re|
      ≤ |(m.muP β).frame| * (4 * B) * cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2)
    rw [hw']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
    set u := velAmp v ι z.1 z.2
    set t := 1 + ‖z.2‖
    set q := (m.muP β).wt z.2
    have hq0 := hφ0 z.2
    have e : u ^ 2 = t ^ 2 * (u / t) ^ 2 := by field_simp
    have k1 : q * cnormSq x ≤ 4 * B * (u / t) ^ 2 := by
      rw [hxq, e]
      calc q * (t ^ 2 * (u / t) ^ 2) = (t ^ 2 * q) * (u / t) ^ 2 := by ring
        _ ≤ 4 * B * (u / t) ^ 2 := by gcongr
    have hcd : ‖cdot x (axisTurn x)‖ ≤ cnormSq x := by linarith
    have h3 : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| * (|(m.muP β).frame| * ‖cdot x (axisTurn x)‖) ≤ q * (|(m.muP β).frame| * cnormSq x) :=
      mul_le_mul hμ (mul_le_mul_of_nonneg_left hcd (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hq0
    have ha0 := abs_nonneg (m.muP β).frame
    nlinarith [mul_le_mul_of_nonneg_left k1 ha0]
  have hF : ‖fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖ ≤ 4 * B * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2) + cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2)) := by
    have hw' := Internal.SmoothPieceEps.cnormSq_modeVel_weighted v ι z.1 z.2
    have hwA := Internal.SmoothPieceEps.cnormSq_modeVel_weighted (frameAdvection W v (m.muP β).frame) ι z.1 z.2
    have h1 := Internal.FieldModes.abs_re_I_mul_le (PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2)
      (cdot (modeVel ι v z.1 z.2) (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2))
    have h2 := Internal.FieldModes.norm_cdot_le (modeVel ι v z.1 z.2) (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2)
    have hxq : cnormSq (modeVel ι v z.1 z.2) = velAmp v ι z.1 z.2 ^ 2 :=
      (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
    have haq : cnormSq (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2) = velAmp (frameAdvection W v (m.muP β).frame) ι z.1 z.2 ^ 2 :=
      (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
    rw [Real.norm_eq_abs]
    show |(Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ)
        * cdot (modeVel ι v z.1 z.2) (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2)).re|
      ≤ 4 * B * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2)
        + cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2))
    rw [hw', hwA]
    rw [hxq, haq] at h2
    set u := velAmp v ι z.1 z.2
    set r := velAmp (frameAdvection W v (m.muP β).frame) ι z.1 z.2
    set t := 1 + ‖z.2‖
    set q := (m.muP β).wt z.2
    have hq0 := hφ0 z.2
    have e : u ^ 2 = t ^ 2 * (u / t) ^ 2 := by field_simp
    have e' : r ^ 2 = t ^ 2 * (r / t) ^ 2 := by field_simp
    have k1 : q * u ^ 2 ≤ 4 * B * (u / t) ^ 2 := by
      rw [e]
      calc q * (t ^ 2 * (u / t) ^ 2) = (t ^ 2 * q) * (u / t) ^ 2 := by ring
        _ ≤ 4 * B * (u / t) ^ 2 := by gcongr
    have k2 : q * r ^ 2 ≤ 4 * B * (r / t) ^ 2 := by
      rw [e']
      calc q * (t ^ 2 * (r / t) ^ 2) = (t ^ 2 * q) * (r / t) ^ 2 := by ring
        _ ≤ 4 * B * (r / t) ^ 2 := by gcongr
    have h3 : |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2| * ‖cdot (modeVel ι v z.1 z.2) (modeVel ι (frameAdvection W v (m.muP β).frame) z.1 z.2)‖
        ≤ q * ((u ^ 2 + r ^ 2) / 2) :=
      mul_le_mul hμ h2 (norm_nonneg _) hq0
    nlinarith [sq_nonneg (u / t), sq_nonneg (r / t)]
  have hY : 0 ≤ |(m.muP β).frame| * (4 * B) * cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) hA0
  calc ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖
      ≤ ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2‖ + ‖fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖ := norm_add_le _ _
    _ ≤ |(m.muP β).frame| * (4 * B) * cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2)
        + 4 * B * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2) + cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2)) := add_le_add hT hF
    _ ≤ (|(m.muP β).frame| + 1) * (4 * B) * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2) + cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2)) := by
        nlinarith [hY]

private theorem advection_norm_summable :
    Summable (fun ι : ℤ × ℤ => ∫ z, ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) := by
  obtain ⟨C, hC0, hC⟩ := advection_term_le m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  have hAsq := frameAdvection_square m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  have hVsq := Internal.SmoothWeightSplit.scaledField_square hv
  have sV := (ModeL2Internal.hasSum_cnormSq_modeVel hPars hVsq).summable
  have sA := (ModeL2Internal.hasSum_cnormSq_modeVel hPars hAsq).summable
  refine Summable.of_nonneg_of_le (fun ι => integral_nonneg fun z => norm_nonneg _) (fun ι => ?_)
    ((sV.add sA).mul_left C)
  have iV := ModeL2Internal.integrable_cnormSq_modeVel hPars hVsq ι
  have iA := ModeL2Internal.integrable_cnormSq_modeVel hPars hAsq ι
  have e : C * ((∫ z, cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) + ∫ z, cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)))
      = ∫ z, C * (cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2) + cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    rw [integral_const_mul]
    congr 1
    exact (integral_add iV iA).symm
  show _ ≤ C * ((∫ z, cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) + ∫ z, cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • frameAdvection W v (m.muP β).frame s x) z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)))
  rw [e]
  exact integral_mono_of_nonneg (ae_of_all _ fun z => norm_nonneg _) ((iV.add iA).const_mul C)
    (ae_of_all _ fun z => hC ι z)

private theorem advection_family_summable :
    Summable (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y)) := by
  have hs := advection_norm_summable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  refine hs.of_norm_bounded (fun ι => ?_)
  have hi := advection_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι
  have e : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y))
      = ∫ z, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := (integral_prod _ hi).symm
  rw [e]
  exact norm_integral_le_integral_norm _

private theorem pairing_summable (hA : freqSeries P (m.muP β).modes (m.muP β).wt (m.muP β).frame v < ⊤) :
    Summable (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y) ∧ Summable (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y))
      ∧ Summable (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y)
      ∧ ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y = (freqSeries P (m.muP β).modes (m.muP β).wt (m.muP β).frame v).toReal := by
  obtain ⟨s1, e1⟩ := freq_tsum_eq m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp hA
  exact ⟨s1, advection_family_summable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp, sumSecondPartials_family_summable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp, e1⟩

private theorem pairing_decomp (hA : freqSeries P (m.muP β).modes (m.muP β).wt (m.muP β).frame v < ⊤) :
    muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v (innerField P W v)
      = (freqSeries P (m.muP β).modes (m.muP β).wt (m.muP β).frame v).toReal
        + (∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y
          + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y))
        + ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y := by
  obtain ⟨s1, s2, s3, hA'⟩ := pairing_summable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp hA
  have key : ∀ ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (innerField P W v) ι σ y
      = (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y) + (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y)) + ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y := by
    intro ι
    obtain ⟨i1, i2, i3⟩ := pairing_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι
    have hpt : ∀ σ y, fieldTerm (m.muP β).modes (m.muP β).wt v (innerField P W v) ι σ y = freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y) + fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y := by
      intro σ y
      rw [fieldTerm_split P (m.muP β).modes (m.muP β).wt (m.muP β).frame W v ι σ y
        (mode_split m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι σ y)
        (sgn_mul_frameFreq P (m.muP β).frame (m.muP β).modes (hm.mu_oneSided β) ι)]
      ring
    have e0 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (innerField P W v) ι σ y)
        = ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y) + fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y) := by
      simp_rw [hpt]
    have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y) + fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y))
        = ∫ z, (freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2) + fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
      (integral_prod (fun z : ℝ × Space => freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2) + fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2)
        ((i1.add i2).add i3)).symm
    have q1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y) = ∫ z, freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
      (integral_prod (fun z : ℝ × Space => freqTerm P (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2) i1).symm
    have q2 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y)) = ∫ z, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
      (integral_prod (fun z : ℝ × Space => (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2)) i2).symm
    have q3 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y) = ∫ z, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2 ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
      (integral_prod (fun z : ℝ × Space => fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2) i3).symm
    have a1 := integral_add i1 i2
    have a2 := integral_add (i1.add i2) i3
    simp only [Pi.add_apply] at a1 a2
    rw [e0, e1, a2, a1, q1, q2, q3]
  show ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (innerField P W v) ι σ y = _
  rw [tsum_congr key, (s1.add s2).tsum_add s3, s1.tsum_add s2, hA']

private theorem piece_vel_summable :
    ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      Summable (fun ι : ℤ × ℤ => ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * velAmp v ι z.1 z.2 ^ 2) := by
  have hfin := Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv
  have hp := hSP P v hv
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ (volume : Measure (ℝ × Space)) :=
    ModeL2Internal.slab_ac
  have hFm : AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    refine AEMeasurable.tsum fun ι => ?_
    have h1 := (Internal.PieceAbsorb.aem_velAmp hp.measurable_velocity ι).mono_ac hac
    have h2 : Measurable (fun z : ℝ × Space => 1 + ‖z.2‖) := measurable_const.add measurable_snd.norm
    exact ENNReal.measurable_ofReal.comp_aemeasurable ((h1.div h2.aemeasurable).pow_const 2)
  have hlt : ∫⁻ z, ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) < ⊤ := by
    rw [lintegral_prod _ hFm]
    refine lt_of_le_of_lt ?_ hfin
    exact lintegral_mono fun σ => lintegral_mono fun y => le_add_self
  filter_upwards [ae_lt_top' hFm hlt.ne] with z hz
  have hs := ENNReal.summable_toReal hz.ne
  have ht : (1 + ‖z.2‖) ≠ 0 := by positivity
  have hs2 : Summable (fun ι : ℤ × ℤ => (1 + ‖z.2‖) ^ 2 * (velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2) := by
    refine (hs.mul_left ((1 + ‖z.2‖) ^ 2)).congr fun ι => ?_
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  refine Summable.of_nonneg_of_le (fun ι => mul_nonneg (ind_nonneg_of _) (sq_nonneg _)) (fun ι => ?_) hs2
  have e : (1 + ‖z.2‖) ^ 2 * (velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2 = velAmp v ι z.1 z.2 ^ 2 := by
    field_simp
  rw [e]
  exact mul_le_of_le_one_left (sq_nonneg _) (ind_le_one_of _)

private theorem amp_summable (σ : ℝ) (y : Space) :
    Summable (fun κ : ℤ × ℤ => gradAmp (gradField v) κ σ y ^ 2) ∧ Summable (fun ι : ℤ × ℤ => velAmp v ι σ y ^ 2) := by
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hG := gradSlice_continuous hv
  refine ⟨?_, ?_⟩
  · have hs : ∀ ij : Fin 3 × Fin 3, Summable (fun κ : ℤ × ℤ => ‖modeGrad κ (gradField v) σ y ij‖ ^ 2) := by
      intro ij
      have := orbit_mode_summable
        (fun τ φ => axialRot (-φ) (gradField v (σ + τ) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1)
        (applied_integrand_continuous (G := gradField v) hG (u := fun p : ℝ × ℝ => axialRot p.2 (unitVector ij.2))
          (Internal.Field.axialRot_comp_continuous continuous_snd continuous_const) σ y ij.1)
      exact this
    refine (summable_sum (s := Finset.univ) fun ij _ => hs ij).congr fun κ => ?_
    unfold gradAmp
    exact (Real.sq_sqrt (show 0 ≤ cnormSq (modeGrad κ (gradField v) σ y) from
      Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
  · have hs : ∀ i : Fin 3, Summable (fun ι : ℤ × ℤ => ‖modeVel ι v σ y i‖ ^ 2) := by
      intro i
      have := orbit_mode_summable (fun τ φ => axialRot (-φ) (v (σ + τ) (axialRot φ y)) i)
        (Internal.Field.mode_integrand_continuous hvc σ y i)
      exact this
    refine (summable_sum (s := Finset.univ) fun i _ => hs i).congr fun ι => ?_
    unfold velAmp
    exact (Real.sq_sqrt (show 0 ≤ cnormSq (modeVel ι v σ y) from
      Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm

private theorem frameAdvection_mode_split (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (frameAdvection W v (m.muP β).frame) σ y
      = innerMode h (m.muP β).modes W v (m.muP β).frame σ y ι + outerMode h (m.muP β).modes W v σ y ι := by
  funext i
  set a := (m.muP β).frame
  set T := (m.muP β).modes
  set c : Fin 3 → ℝ := fun j => ((1 / 2 : ℝ) • y - a • turnDir y) j with hc
  have hE : ∀ τ φ : ℝ, ∀ j : Fin 3,
      ((axialRot (-φ) ((fun s x => W s x + (1 / 2 : ℝ) • x - a • turnDir x) (σ + τ) (axialRot φ y)) j : ℝ) : ℂ)
        = (c j : ℂ) + ∑ α ∈ h.harmonics, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeVel α W σ y j := by
    intro τ φ j
    simp only
    rw [frame_vector_rot, Complex.ofReal_add,
      Internal.SmoothPieceMuHarmonics.orbit_expansion m P h w W hm hW hWp σ y τ φ j, add_comm]
  have hG : Continuous fun z : ℝ × Space => gradField v z.1 z.2 := gradSlice_continuous hv
  have hp := clm_mode_product h.harmonics (gradField v) (fun s x => W s x + (1 / 2 : ℝ) • x - a • turnDir x) hG σ y
    c (fun α j => modeVel α W σ y j) hE ι i
  have e : modeVel ι (frameAdvection W v a) σ y i
      = modeVel ι (fun σ y => gradField v σ y ((fun s x => W s x + (1 / 2 : ℝ) • x - a • turnDir x) σ y)) σ y i := rfl
  rw [e, hp]
  simp only [innerMode, outerMode, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs <;> simp

open Classical in
private theorem outerMode_le (σ : ℝ) (y : Space) (ι : ℤ × ℤ) (hι : PieceWeights.inPiece (m.muP β).modes ι) :
    Real.sqrt (cnormSq (outerMode h (m.muP β).modes W v σ y ι))
      ≤ edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι := by
  set T := (m.muP β).modes
  refine (outerMode_le_sum h T W v σ y ι).trans ?_
  have hg0 : ∀ κ, 0 ≤ gradAmp (gradField v) κ σ y := fun κ => Real.sqrt_nonneg _
  have hX0 : ∀ α, 0 ≤ velAmp W α σ y := fun α => Real.sqrt_nonneg _
  unfold edgeSum
  by_cases h1 : ι ∈ T
  · rw [if_pos h1]
    refine Finset.sum_le_sum fun α _ => ?_
    by_cases h2 : ι - α ∈ T
    · have h3 : PieceWeights.inPiece T (ι - α) := Or.inl h2
      rw [if_pos h3, if_pos h2]
    · by_cases h3 : PieceWeights.inPiece T (ι - α)
      · rw [if_pos h3, if_neg h2]
        exact mul_nonneg (hX0 α) (hg0 _)
      · rw [if_neg h3, if_neg h2]
  · have h1' : -ι ∈ T := hι.resolve_left h1
    rw [if_neg h1, if_pos h1']
    have hre : ∑ α ∈ h.harmonics, (if PieceWeights.inPiece T (ι - α) then 0
          else velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y)
        = ∑ b ∈ h.harmonics, (if PieceWeights.inPiece T (ι + b) then 0
          else velAmp W b σ y * gradAmp (gradField v) (ι + b) σ y) := by
      refine Finset.sum_nbij' (fun α => -α) (fun b => -b) (fun α hα => hm.harmonics_neg α hα)
        (fun b hb => hm.harmonics_neg b hb) (fun α _ => neg_neg α) (fun b _ => neg_neg b) fun α _ => ?_
      rw [sub_eq_add_neg, Internal.SmoothPieceMuHarmonics.velAmp_neg]
    rw [hre]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases h2 : -ι - b ∈ T
    · have h3 : PieceWeights.inPiece T (ι + b) := Or.inr (by rw [neg_add']; exact h2)
      rw [if_pos h3, if_pos h2]
    · rw [if_neg h2]
      by_cases h3 : PieceWeights.inPiece T (ι + b)
      · rw [if_pos h3]
        exact mul_nonneg (hX0 b) (hg0 _)
      · rw [if_neg h3]

private theorem edge_summable (σ : ℝ) (y : Space) :
    Summable (fun ι : ℤ × ℤ => velAmp v ι σ y
      * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι) := by
  obtain ⟨hg2, hu2⟩ := amp_summable m P h w W hm hW hWp hWdiv hWdecay hwb v hv hPars hDer hRotM hSolenoidal hSP hSsp σ y
  set X : ℤ × ℤ → ℝ := fun α => velAmp W α σ y
  set g : ℤ × ℤ → ℝ := fun κ => gradAmp (gradField v) κ σ y
  set u : ℤ × ℤ → ℝ := fun ι => velAmp v ι σ y
  have hX : ∀ α, 0 ≤ X α := fun α => Real.sqrt_nonneg _
  have hg : ∀ κ, 0 ≤ g κ := fun κ => Real.sqrt_nonneg _
  have hu : ∀ ι, 0 ≤ u ι := fun ι => Real.sqrt_nonneg _
  have hedge : ∀ ι, edgeSum h (m.muP β).modes X g ι ≤ ∑ α ∈ h.harmonics, X α * (g (ι - α) + g (ι + α)) := by
    intro ι
    have hnn : 0 ≤ ∑ α ∈ h.harmonics, X α * (g (ι - α) + g (ι + α)) :=
      Finset.sum_nonneg fun α _ => mul_nonneg (hX α) (add_nonneg (hg _) (hg _))
    unfold edgeSum
    split_ifs
    · refine Finset.sum_le_sum fun α _ => ?_
      split_ifs
      · exact mul_nonneg (hX α) (add_nonneg (hg _) (hg _))
      · nlinarith [mul_nonneg (hX α) (hg (ι + α))]
    · refine Finset.sum_le_sum fun α _ => ?_
      split_ifs
      · exact mul_nonneg (hX α) (add_nonneg (hg _) (hg _))
      · nlinarith [mul_nonneg (hX α) (hg (ι - α))]
    · exact hnn
  have hbound : ∀ ι, u ι * edgeSum h (m.muP β).modes X g ι
      ≤ ∑ α ∈ h.harmonics, X α * (u ι ^ 2 + (g (ι - α) ^ 2 + g (ι + α) ^ 2) / 2) := by
    intro ι
    refine (mul_le_mul_of_nonneg_left (hedge ι) (hu ι)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun α _ => ?_
    have h1 := two_mul_le_add_sq (u ι) (g (ι - α))
    have h2 := two_mul_le_add_sq (u ι) (g (ι + α))
    nlinarith [hX α, mul_le_mul_of_nonneg_left h1 (hX α), mul_le_mul_of_nonneg_left h2 (hX α)]
  have hsR : Summable (fun ι => ∑ α ∈ h.harmonics, X α * (u ι ^ 2 + (g (ι - α) ^ 2 + g (ι + α) ^ 2) / 2)) := by
    refine summable_sum fun α _ => ?_
    have s1 : Summable (fun ι : ℤ × ℤ => g (ι - α) ^ 2) := by
      simpa only [Function.comp_def, Equiv.subRight_apply] using (Equiv.subRight α).summable_iff.2 hg2
    have s2 : Summable (fun ι : ℤ × ℤ => g (ι + α) ^ 2) := by
      simpa only [Function.comp_def, Equiv.coe_addRight] using (Equiv.addRight α).summable_iff.2 hg2
    exact (hu2.add ((s1.add s2).div_const 2)).mul_left (X α)
  exact Summable.of_nonneg_of_le (fun ι => mul_nonneg (hu ι) (edgeSum_nonneg h _ X g hX hg ι)) hbound hsR

private theorem orbitFrame_sq_le (σ : ℝ) (y : Space) (τ φ : ℝ) :
    ∑ j : Fin 3, orbitFrame h W (m.muP β).frame σ y j τ φ ^ 2 ≤ frameSpeedSup W (m.muP β).frame y ^ 2 := by
  obtain ⟨D, hD⟩ := hWdecay
  set a := (m.muP β).frame
  have hD0 : 0 ≤ D := by
    have := hD 0 0 0 (by norm_num)
    exact le_trans (norm_nonneg _) (this.trans (by simp))
  have hWb : ∀ s x, ‖W s x‖ ≤ D := by
    intro s x
    have := hD s x 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at this
    refine this.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ (1 + ‖x‖) ^ (0 + 1) := by simp
    nlinarith
  have hexp : ∀ j, orbitFrame h W a σ y j τ φ
      = (axialRot (-φ) (W (σ + τ) (axialRot φ y)) + ((1 / 2 : ℝ) • y - a • turnDir y)) j := by
    intro j
    unfold orbitFrame
    rw [PiLp.add_apply, Internal.SmoothPieceMuHarmonics.orbit_expansion_re h.harmonics W hW.continuous hWp
      hm.harmonics_span σ y τ φ j]
    ring
  have hsq : ∑ j : Fin 3, orbitFrame h W a σ y j τ φ ^ 2
      = ‖W (σ + τ) (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y - a • turnDir (axialRot φ y)‖ ^ 2 := by
    simp_rw [hexp]
    rw [← rot_frame_eq, ← Internal.MuSmooth.space_norm_sq, RotationInternal.axialRot_norm]
  have hbdd : BddAbove (Set.range fun p : ℝ × ℝ => ‖W p.1 (axialRot p.2 y) + (1 / 2 : ℝ) • axialRot p.2 y
      - a • (-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1)‖) := by
    refine ⟨D + (1 / 2 + 2 * |a|) * ‖y‖, ?_⟩
    rintro _ ⟨p, rfl⟩
    have h1 := Internal.SmoothPieceEps.norm_perp_le (axialRot p.2 y)
    have h2 := RotationInternal.axialRot_norm p.2 y
    calc ‖W p.1 (axialRot p.2 y) + (1 / 2 : ℝ) • axialRot p.2 y
          - a • (-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1)‖
        ≤ ‖W p.1 (axialRot p.2 y)‖ + ‖(1 / 2 : ℝ) • axialRot p.2 y‖
          + ‖a • (-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ D + 1 / 2 * ‖y‖ + |a| * (2 * ‖y‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), h2]
          rw [h2] at h1
          gcongr
          exact hWb _ _
      _ = D + (1 / 2 + 2 * |a|) * ‖y‖ := by ring
  have hle : ‖W (σ + τ) (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y - a • turnDir (axialRot φ y)‖
      ≤ frameSpeedSup W a y := by
    unfold frameSpeedSup
    exact le_ciSup hbdd ((σ + τ, φ) : ℝ × ℝ)
  rw [hsq]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

private theorem inner_finset_bound (S F : Finset (ℤ × ℤ)) (hF : ∀ κ ∈ F, -κ ∈ F)
    (hSF : ∀ ι ∈ S, ι ∈ F ∧ ∀ α ∈ h.harmonics, (PieceWeights.inPiece (m.muP β).modes (ι - α) ↔ ι - α ∈ F))
    (σ : ℝ) (y : Space) :
    ∑ ι ∈ S, cnormSq (innerMode h (m.muP β).modes W v (m.muP β).frame σ y ι)
      ≤ frameSpeedSup W (m.muP β).frame y ^ 2 * ∑ κ ∈ F, cnormSq (modeGrad κ (gradField v) σ y) := by
  set T := (m.muP β).modes
  set a := (m.muP β).frame
  have hpt : ∀ τ φ, ∑ i, truncProduct F h W v a σ y i τ φ ^ 2
      ≤ frameSpeedSup W a y ^ 2 * ∑ ij : Fin 3 × Fin 3, truncGrad F v σ y ij τ φ ^ 2 := by
    intro τ φ
    have hV := orbitFrame_sq_le m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp σ y τ φ
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    unfold truncProduct
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hV (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hb := modeSq_sum_le_of_pointwise (fun i τ φ => truncProduct F h W v a σ y i τ φ) (fun ij τ φ => truncGrad F v σ y ij τ φ)
    (fun i => truncProduct_continuous F h W v a σ y i) (fun ij => truncGrad_continuous F v σ y ij)
    (frameSpeedSup W a y ^ 2) (sq_nonneg _) hpt S
  have hl : ∀ ι ∈ S, ∑ i, ENNReal.ofReal (‖modeAverage ι (fun τ φ (_ : Unit) => truncProduct F h W v a σ y i τ φ) ()‖ ^ 2)
      = ENNReal.ofReal (cnormSq (innerMode h T W v a σ y ι)) := by
    intro ι hι
    obtain ⟨h1, h2⟩ := hSF ι hι
    unfold cnormSq
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [truncProduct_mode F hF h hm.harmonics_neg T W v a σ y ι h1 h2 i]
  have hr : ∀ ij : Fin 3 × Fin 3, ∑' μ : ℤ × ℤ, ENNReal.ofReal (‖modeAverage μ (fun τ φ (_ : Unit) => truncGrad F v σ y ij τ φ) ()‖ ^ 2)
      = ∑ μ ∈ F, ENNReal.ofReal (‖modeGrad μ (gradField v) σ y ij‖ ^ 2) := by
    intro ij
    rw [tsum_eq_sum (s := F) (fun μ hμ => by rw [truncGrad_mode F hF v σ y ij μ, if_neg hμ]; simp)]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [truncGrad_mode F hF v σ y ij μ, if_pos hμ]
  rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl (fun ij _ => hr ij), Finset.sum_comm] at hb
  have e1 : ∑ ι ∈ S, ENNReal.ofReal (cnormSq (innerMode h T W v a σ y ι))
      = ENNReal.ofReal (∑ ι ∈ S, cnormSq (innerMode h T W v a σ y ι)) :=
    (ENNReal.ofReal_sum_of_nonneg fun ι _ => Finset.sum_nonneg fun _ _ => sq_nonneg _).symm
  have e2 : ∑ μ ∈ F, ∑ ij : Fin 3 × Fin 3, ENNReal.ofReal (‖modeGrad μ (gradField v) σ y ij‖ ^ 2)
      = ENNReal.ofReal (∑ κ ∈ F, cnormSq (modeGrad κ (gradField v) σ y)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (s := F) (f := fun κ => cnormSq (modeGrad κ (gradField v) σ y))
      (fun κ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    unfold cnormSq
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
  rw [e1, e2, ← ENNReal.ofReal_mul (sq_nonneg _)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun κ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))).1 hb

private theorem innerMode_piece_bound (σ : ℝ) (y : Space) :
    Summable (fun ι : ℤ × ℤ => ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * velAmp v ι σ y
      * Real.sqrt (cnormSq (innerMode h (m.muP β).modes W v (m.muP β).frame σ y ι)))
    ∧ ∑' ι : ℤ × ℤ, ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * velAmp v ι σ y
      * Real.sqrt (cnormSq (innerMode h (m.muP β).modes W v (m.muP β).frame σ y ι))
      ≤ frameSpeedSup W (m.muP β).frame y * pieceNorm (m.muP β).modes (fun κ => gradAmp (gradField v) κ σ y)
        * pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y) := by
  classical
  set T := (m.muP β).modes
  set a := (m.muP β).frame
  obtain ⟨hg2, hu2⟩ := amp_summable m P h w W hm hW hWp hWdiv hWdecay hwb v hv hPars hDer hRotM hSolenoidal hSP hSsp σ y
  set g : ℤ × ℤ → ℝ := fun κ => gradAmp (gradField v) κ σ y with hgdef
  set u : ℤ × ℤ → ℝ := fun ι => velAmp v ι σ y with hudef
  set In : ℤ × ℤ → ℝ := fun ι => Real.sqrt (cnormSq (innerMode h T W v a σ y ι)) with hIndef
  set fS := frameSpeedSup W a y
  have hfS : 0 ≤ fS := Real.iSup_nonneg fun _ => norm_nonneg _
  have hi0 : ∀ ι, 0 ≤ ModeWeights.ind (PieceWeights.inPiece T ι) := fun ι => ind_nonneg_of _
  have hi1 : ∀ ι, ModeWeights.ind (PieceWeights.inPiece T ι) ≤ 1 := fun ι => ind_le_one_of _
  have sg : Summable (fun κ => ModeWeights.ind (PieceWeights.inPiece T κ) * g κ ^ 2) :=
    Summable.of_nonneg_of_le (fun κ => mul_nonneg (hi0 κ) (sq_nonneg _))
      (fun κ => mul_le_of_le_one_left (sq_nonneg _) (hi1 κ)) hg2
  have su : Summable (fun κ => ModeWeights.ind (PieceWeights.inPiece T κ) * u κ ^ 2) :=
    Summable.of_nonneg_of_le (fun κ => mul_nonneg (hi0 κ) (sq_nonneg _))
      (fun κ => mul_le_of_le_one_left (sq_nonneg _) (hi1 κ)) hu2
  have hpg : pieceNorm T g ^ 2 = ∑' κ, ModeWeights.ind (PieceWeights.inPiece T κ) * g κ ^ 2 :=
    Real.sq_sqrt (tsum_nonneg fun κ => mul_nonneg (hi0 κ) (sq_nonneg _))
  have hpu : pieceNorm T u ^ 2 = ∑' κ, ModeWeights.ind (PieceWeights.inPiece T κ) * u κ ^ 2 :=
    Real.sq_sqrt (tsum_nonneg fun κ => mul_nonneg (hi0 κ) (sq_nonneg _))
  have hpN0 : 0 ≤ pieceNorm T g := Real.sqrt_nonneg _
  have hpN1 : 0 ≤ pieceNorm T u := Real.sqrt_nonneg _
  have hR0 : 0 ≤ fS * pieceNorm T g * pieceNorm T u := mul_nonneg (mul_nonneg hfS hpN0) hpN1
  have hneg : ∀ κ, PieceWeights.inPiece T (-κ) ↔ PieceWeights.inPiece T κ := by
    intro κ
    unfold PieceWeights.inPiece
    rw [neg_neg]
    tauto
  have hind1 : ∀ κ, PieceWeights.inPiece T κ → ModeWeights.ind (PieceWeights.inPiece T κ) = 1 := by
    intro κ hκ
    unfold ModeWeights.ind
    rw [if_pos hκ]
  have hnn : ∀ ι, 0 ≤ ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * In ι := fun ι =>
    mul_nonneg (mul_nonneg (hi0 ι) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hfin : ∀ S : Finset (ℤ × ℤ), ∑ ι ∈ S, ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * In ι
      ≤ fS * pieceNorm T g * pieceNorm T u := by
    intro S
    set S' := S.filter (fun ι => PieceWeights.inPiece T ι)
    set K := S' ∪ (S'.biUnion fun ι => h.harmonics.image fun α => ι - α).filter (fun κ => PieceWeights.inPiece T κ)
    set F := K ∪ K.image (fun κ => -κ)
    have hKp : ∀ κ ∈ K, PieceWeights.inPiece T κ := by
      intro κ hκ
      rcases Finset.mem_union.1 hκ with h1 | h1
      · exact (Finset.mem_filter.1 h1).2
      · exact (Finset.mem_filter.1 h1).2
    have hFp : ∀ κ ∈ F, PieceWeights.inPiece T κ := by
      intro κ hκ
      rcases Finset.mem_union.1 hκ with h1 | h1
      · exact hKp κ h1
      · obtain ⟨κ', hκ', rfl⟩ := Finset.mem_image.1 h1
        exact (hneg κ').2 (hKp κ' hκ')
    have hF : ∀ κ ∈ F, -κ ∈ F := by
      intro κ hκ
      rcases Finset.mem_union.1 hκ with h1 | h1
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h1)
      · obtain ⟨κ', hκ', rfl⟩ := Finset.mem_image.1 h1
        rw [neg_neg]
        exact Finset.mem_union_left _ hκ'
    have hSF : ∀ ι ∈ S', ι ∈ F ∧ ∀ α ∈ h.harmonics, (PieceWeights.inPiece T (ι - α) ↔ ι - α ∈ F) := by
      intro ι hι
      refine ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hι), fun α hα => ⟨fun hp => ?_, hFp _⟩⟩
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2
        ⟨Finset.mem_biUnion.2 ⟨ι, hι, Finset.mem_image.2 ⟨α, hα, rfl⟩⟩, hp⟩))
    have hb := inner_finset_bound m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
      S' F hF hSF σ y
    have e1 : ∑ ι ∈ S, ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * In ι = ∑ ι ∈ S', u ι * In ι := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun ι _ => ?_
      unfold ModeWeights.ind
      split_ifs <;> ring
    have hIn2 : ∑ ι ∈ S', In ι ^ 2 = ∑ ι ∈ S', cnormSq (innerMode h T W v a σ y ι) :=
      Finset.sum_congr rfl fun ι _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hG2 : ∑ κ ∈ F, cnormSq (modeGrad κ (gradField v) σ y) ≤ pieceNorm T g ^ 2 := by
      rw [hpg]
      calc ∑ κ ∈ F, cnormSq (modeGrad κ (gradField v) σ y)
          = ∑ κ ∈ F, ModeWeights.ind (PieceWeights.inPiece T κ) * g κ ^ 2 :=
            Finset.sum_congr rfl fun κ hκ => by
              rw [hind1 κ (hFp κ hκ), one_mul, hgdef]
              exact (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
        _ ≤ _ := sg.sum_le_tsum F (fun κ _ => mul_nonneg (hi0 κ) (sq_nonneg _))
    have hU2 : ∑ ι ∈ S', u ι ^ 2 ≤ pieceNorm T u ^ 2 := by
      rw [hpu]
      calc ∑ ι ∈ S', u ι ^ 2 = ∑ ι ∈ S', ModeWeights.ind (PieceWeights.inPiece T ι) * u ι ^ 2 :=
            Finset.sum_congr rfl fun ι hι => by rw [hind1 ι (Finset.mem_filter.1 hι).2, one_mul]
        _ ≤ _ := su.sum_le_tsum S' (fun κ _ => mul_nonneg (hi0 κ) (sq_nonneg _))
    have cs := Finset.sum_mul_sq_le_sq_mul_sq S' u In
    have hsq : (∑ ι ∈ S', u ι * In ι) ^ 2 ≤ (fS * pieceNorm T g * pieceNorm T u) ^ 2 := by
      refine cs.trans ?_
      rw [hIn2]
      calc (∑ ι ∈ S', u ι ^ 2) * ∑ ι ∈ S', cnormSq (innerMode h T W v a σ y ι)
          ≤ pieceNorm T u ^ 2 * (fS ^ 2 * pieceNorm T g ^ 2) :=
            mul_le_mul hU2 (hb.trans (mul_le_mul_of_nonneg_left hG2 (sq_nonneg _)))
              (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
        _ = (fS * pieceNorm T g * pieceNorm T u) ^ 2 := by ring
    have hL0 : 0 ≤ ∑ ι ∈ S', u ι * In ι :=
      Finset.sum_nonneg fun ι _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [e1]
    nlinarith
  exact ⟨summable_of_sum_le hnn hfin, tsum_le_of_sum_le' hR0 hfin⟩

private theorem frame_piece_bound :
    ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      Summable (fun ι : ℤ × ℤ => ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * velAmp v ι z.1 z.2
        * velAmp (frameAdvection W v (m.muP β).frame) ι z.1 z.2)
      ∧ ∑' ι : ℤ × ℤ, ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * velAmp v ι z.1 z.2
          * velAmp (frameAdvection W v (m.muP β).frame) ι z.1 z.2
        ≤ frameSpeedSup W (m.muP β).frame z.2 * pieceNorm (m.muP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
            * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2)
          + ∑' ι : ℤ × ℤ, velAmp v ι z.1 z.2
            * edgeSum h (m.muP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι := by
  refine ae_of_all _ fun z => ?_
  set T := (m.muP β).modes
  set a := (m.muP β).frame
  obtain ⟨hI1, hI2⟩ := innerMode_piece_bound m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp z.1 z.2
  have hE := edge_summable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp z.1 z.2
  set X : ℤ × ℤ → ℝ := fun α => velAmp W α z.1 z.2
  set g : ℤ × ℤ → ℝ := fun κ => gradAmp (gradField v) κ z.1 z.2
  set u : ℤ × ℤ → ℝ := fun ι => velAmp v ι z.1 z.2
  set In : ℤ × ℤ → ℝ := fun ι => Real.sqrt (cnormSq (innerMode h T W v a z.1 z.2 ι))
  have hu0 : ∀ ι, 0 ≤ u ι := fun ι => Real.sqrt_nonneg _
  have hIn0 : ∀ ι, 0 ≤ In ι := fun ι => Real.sqrt_nonneg _
  have hr0 : ∀ ι, 0 ≤ velAmp (frameAdvection W v a) ι z.1 z.2 := fun ι => Real.sqrt_nonneg _
  have hed0 : ∀ ι, 0 ≤ edgeSum h T X g ι :=
    edgeSum_nonneg h T X g (fun α => Real.sqrt_nonneg _) (fun κ => Real.sqrt_nonneg _)
  have hpt : ∀ ι, ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * velAmp (frameAdvection W v a) ι z.1 z.2
      ≤ ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * In ι + u ι * edgeSum h T X g ι := by
    intro ι
    by_cases hι : PieceWeights.inPiece T ι
    · have hsplit := frameAdvection_mode_split m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp ι z.1 z.2
      have hout := outerMode_le m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp z.1 z.2 ι hι
      have htri : velAmp (frameAdvection W v a) ι z.1 z.2
          ≤ In ι + Real.sqrt (cnormSq (outerMode h T W v z.1 z.2 ι)) := by
        show Internal.MuSmooth.cnorm3 (modeVel ι (frameAdvection W v a) z.1 z.2) ≤ _
        rw [hsplit]
        exact Internal.MuSmooth.cnorm3_add_le _ _
      have hind : ModeWeights.ind (PieceWeights.inPiece T ι) = 1 := by
        unfold ModeWeights.ind; rw [if_pos hι]
      rw [hind]
      nlinarith [mul_le_mul_of_nonneg_left htri (hu0 ι), mul_le_mul_of_nonneg_left hout (hu0 ι)]
    · have hind : ModeWeights.ind (PieceWeights.inPiece T ι) = 0 := by
        unfold ModeWeights.ind; rw [if_neg hι]
      rw [hind]
      simp only [zero_mul, zero_add]
      exact mul_nonneg (hu0 ι) (hed0 ι)
  have hsum : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * In ι + u ι * edgeSum h T X g ι) :=
    hI1.add hE
  have hs : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * velAmp (frameAdvection W v a) ι z.1 z.2) :=
    Summable.of_nonneg_of_le (fun ι => mul_nonneg (mul_nonneg (ind_nonneg_of _) (hu0 ι)) (hr0 ι)) hpt hsum
  refine ⟨hs, ?_⟩
  calc ∑' ι, ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * velAmp (frameAdvection W v a) ι z.1 z.2
      ≤ ∑' ι, (ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * In ι + u ι * edgeSum h T X g ι) :=
        hs.tsum_le_tsum hpt hsum
    _ = ∑' ι, ModeWeights.ind (PieceWeights.inPiece T ι) * u ι * In ι + ∑' ι, u ι * edgeSum h T X g ι :=
        hI1.tsum_add hE
    _ ≤ _ := by linarith [hI2]

private theorem advection_pointwise :
    ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)), Summable (fun ι : ℤ × ℤ => (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2))
      ∧ -advectionLoss h (m.muP β).modes (m.muP β).wt W (m.muP β).frame v z.1 z.2 ≤ ∑' ι : ℤ × ℤ, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2) := by
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  filter_upwards [piece_vel_summable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp,
    frame_piece_bound m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp] with z hS hF
  obtain ⟨hF1, hF2⟩ := hF
  set T := (m.muP β).modes
  set φ := (m.muP β).wt
  set a := (m.muP β).frame
  set A := frameAdvection W v a
  have hq := hφ0 z.2
  set b : ℤ × ℤ → ℝ := fun ι => φ z.2 * |a| * (ModeWeights.ind (PieceWeights.inPiece T ι) * velAmp v ι z.1 z.2 ^ 2)
      + φ z.2 * (ModeWeights.ind (PieceWeights.inPiece T ι) * velAmp v ι z.1 z.2 * velAmp A ι z.1 z.2) with hb
  have hbs : Summable b := (hS.mul_left (φ z.2 * |a|)).add (hF1.mul_left (φ z.2))
  have hle : ∀ ι, |turnTerm T φ a v ι z.1 z.2 + fieldTerm T φ v A ι z.1 z.2| ≤ b ι := fun ι =>
    (abs_add_le _ _).trans (add_le_add (turnTerm_abs_le T φ a v ι z.1 z.2 hq) (fieldTerm_abs_le T φ v A ι z.1 z.2 hq))
  have hsum : Summable (fun ι => turnTerm T φ a v ι z.1 z.2 + fieldTerm T φ v A ι z.1 z.2) :=
    Summable.of_norm_bounded hbs (fun ι => by rw [Real.norm_eq_abs]; exact hle ι)
  refine ⟨hsum, ?_⟩
  have h1 : -∑' ι, b ι ≤ ∑' ι, (turnTerm T φ a v ι z.1 z.2 + fieldTerm T φ v A ι z.1 z.2) := by
    rw [← tsum_neg]
    exact hbs.neg.tsum_le_tsum (fun ι => neg_le_of_abs_le (hle ι)) hsum
  have h2 : ∑' ι, b ι = φ z.2 * |a| * ∑' ι, ModeWeights.ind (PieceWeights.inPiece T ι) * velAmp v ι z.1 z.2 ^ 2
      + φ z.2 * ∑' ι, ModeWeights.ind (PieceWeights.inPiece T ι) * velAmp v ι z.1 z.2 * velAmp A ι z.1 z.2 := by
    rw [hb, (hS.mul_left _).tsum_add (hF1.mul_left _), tsum_mul_left, tsum_mul_left]
  have hpn : pieceNorm T (fun κ => velAmp v κ z.1 z.2) ^ 2
      = ∑' ι, ModeWeights.ind (PieceWeights.inPiece T ι) * velAmp v ι z.1 z.2 ^ 2 :=
    Real.sq_sqrt (tsum_nonneg fun ι => mul_nonneg (ind_nonneg_of _) (sq_nonneg _))
  have h3 : ∑' ι, φ z.2 * velAmp v ι z.1 z.2
        * edgeSum h T (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι
      = φ z.2 * ∑' ι, velAmp v ι z.1 z.2
        * edgeSum h T (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ι => by ring
  unfold advectionLoss
  rw [h3, hpn]
  have h4 := mul_le_mul_of_nonneg_left hF2 hq
  rw [h2] at h1
  nlinarith [h4, h1]

private theorem advection_swap :
    Integrable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      ∧ ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y)
        = ∫ z, (∑' ι : ℤ × ℤ, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
  have hint := advection_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  have hs := advection_norm_summable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  refine ⟨⟨AEStronglyMeasurable.tsum fun ι => (hint ι).aestronglyMeasurable, ?_⟩, ?_⟩
  · have e : ∀ ι : ℤ × ℤ, ∫⁻ z, ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖ₑ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
        = ENNReal.ofReal (∫ z, ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) :=
      fun ι => (ofReal_integral_norm_eq_lintegral_enorm (hint ι)).symm
    show ∫⁻ z, ‖∑' ι : ℤ × ℤ, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2)‖ₑ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) < ⊤
    calc ∫⁻ z, ‖∑' ι : ℤ × ℤ, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2)‖ₑ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
        ≤ ∫⁻ z, ∑' ι : ℤ × ℤ, ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖ₑ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
          lintegral_mono fun z => enorm_tsum_le_tsum_enorm
      _ = ∑' ι : ℤ × ℤ, ∫⁻ z, ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖ₑ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
          lintegral_tsum fun ι => (hint ι).aestronglyMeasurable.enorm
      _ = ∑' ι : ℤ × ℤ, ENNReal.ofReal (∫ z, ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) := tsum_congr e
      _ = ENNReal.ofReal (∑' ι : ℤ × ℤ, ∫ z, ‖turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι z.1 z.2 + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι z.1 z.2‖ ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun ι => integral_nonneg fun z => norm_nonneg _) hs).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  · rw [← integral_tsum_of_summable_integral_norm hint hs]
    exact tsum_congr fun ι => (integral_prod _ (hint ι)).symm

private theorem advection_loss_le (hE : edgeSeries h (m.muP β).modes (m.muP β).wt W v < ⊤)
    (h1 : turnBlock (m.muP β).modes (m.muP β).wt (m.muP β).frame v < ⊤) (h2 : advectionBlock (m.muP β).modes (m.muP β).wt W (m.muP β).frame v < ⊤) :
    Integrable (fun z : ℝ × Space => advectionLoss h (m.muP β).modes (m.muP β).wt W (m.muP β).frame v z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      ∧ ∫ z, advectionLoss h (m.muP β).modes (m.muP β).wt W (m.muP β).frame v z.1 z.2 ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
        ≤ (edgeSeries h (m.muP β).modes (m.muP β).wt W v).toReal + (turnBlock (m.muP β).modes (m.muP β).wt (m.muP β).frame v).toReal
          + (advectionBlock (m.muP β).modes (m.muP β).wt W (m.muP β).frame v).toReal := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  obtain ⟨D, hD⟩ := hWdecay
  have hp := hSP P v hv
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ (volume : Measure (ℝ × Space)) := ModeL2Internal.slab_ac
  have hφ : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hpN : ∀ g : ℤ × ℤ → ℝ, 0 ≤ pieceNorm (m.muP β).modes g := fun _ => Real.sqrt_nonneg _
  have hfs : ∀ y, 0 ≤ frameSpeedSup W (m.muP β).frame y := fun y => Real.iSup_nonneg fun _ => norm_nonneg _
  have hedge : ∀ ι σ y, 0 ≤ edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι := by
    intro ι σ y
    unfold edgeSum
    split_ifs
    · exact Finset.sum_nonneg fun β _ => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · exact Finset.sum_nonneg fun β _ => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · exact le_rfl
  have mφ : Measurable (fun z : ℝ × Space => (m.muP β).wt z.2) := hK.continuous.measurable.comp measurable_snd
  have mV : ∀ κ, AEMeasurable (fun z : ℝ × Space => velAmp v κ z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    fun κ => (Internal.PieceAbsorb.aem_velAmp hp.measurable_velocity κ).mono_ac hac
  have mG : ∀ κ, AEMeasurable (fun z : ℝ × Space => gradAmp (gradField v) κ z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    fun κ => (Internal.PieceAbsorb.aem_gradAmp hp.measurable_gradient κ).mono_ac hac
  have mW : ∀ α, AEMeasurable (fun z : ℝ × Space => velAmp W α z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    fun α => (Internal.PieceAbsorb.aem_velAmp hW.continuous.aestronglyMeasurable α).mono_ac hac
  have mS : Measurable (fun z : ℝ × Space => frameSpeedSup W (m.muP β).frame z.2) :=
    (frameSpeedSup_measurable hW.continuous hD (m.muP β).frame).comp measurable_snd
  have mNV : AEMeasurable (fun z : ℝ × Space => pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    aem_pieceNorm_of (m.muP β).modes mV
  have mNG : AEMeasurable (fun z : ℝ × Space => pieceNorm (m.muP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    aem_pieceNorm_of (m.muP β).modes mG
  have mE : ∀ ι, AEMeasurable (fun z : ℝ × Space => edgeSum h (m.muP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    aem_edgeSum h (m.muP β).modes mW mG
  have m1 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ((m.muP β).wt z.2 * |(m.muP β).frame| * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2) ^ 2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((mφ.aemeasurable.mul aemeasurable_const).mul (mNV.pow_const 2))
  have m2 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal ((m.muP β).wt z.2 * frameSpeedSup W (m.muP β).frame z.2 * pieceNorm (m.muP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2) * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (((mφ.aemeasurable.mul mS.aemeasurable).mul mNG).mul mNV)
  have m3 : AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt z.2 * velAmp v ι z.1 z.2 * edgeSum h (m.muP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable ((mφ.aemeasurable.mul (mV ι)).mul (mE ι))
  have e1 : turnBlock (m.muP β).modes (m.muP β).wt (m.muP β).frame v = ∫⁻ z, ENNReal.ofReal ((m.muP β).wt z.2 * |(m.muP β).frame| * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2) ^ 2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    unfold turnBlock
    exact (lintegral_prod _ m1).symm
  have e2 : advectionBlock (m.muP β).modes (m.muP β).wt W (m.muP β).frame v = ∫⁻ z, ENNReal.ofReal ((m.muP β).wt z.2 * frameSpeedSup W (m.muP β).frame z.2 * pieceNorm (m.muP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2) * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    unfold advectionBlock
    exact (lintegral_prod _ m2).symm
  have e3 : edgeSeries h (m.muP β).modes (m.muP β).wt W v = ∫⁻ z, ∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt z.2 * velAmp v ι z.1 z.2 * edgeSum h (m.muP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    unfold edgeSeries
    exact (lintegral_prod _ m3).symm
  have n1 : (∫⁻ z, ENNReal.ofReal ((m.muP β).wt z.2 * |(m.muP β).frame| * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2) ^ 2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) ≠ ⊤ := by rw [← e1]; exact h1.ne
  have n2 : (∫⁻ z, ENNReal.ofReal ((m.muP β).wt z.2 * frameSpeedSup W (m.muP β).frame z.2 * pieceNorm (m.muP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2) * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) ≠ ⊤ := by rw [← e2]; exact h2.ne
  have n3 : (∫⁻ z, ∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt z.2 * velAmp v ι z.1 z.2 * edgeSum h (m.muP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) ≠ ⊤ := by rw [← e3]; exact hE.ne
  have hpt : ∀ z : ℝ × Space, advectionLoss h (m.muP β).modes (m.muP β).wt W (m.muP β).frame v z.1 z.2
      = (ENNReal.ofReal ((m.muP β).wt z.2 * |(m.muP β).frame| * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2) ^ 2)).toReal + (ENNReal.ofReal ((m.muP β).wt z.2 * frameSpeedSup W (m.muP β).frame z.2 * pieceNorm (m.muP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2) * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2))).toReal + (∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt z.2 * velAmp v ι z.1 z.2 * edgeSum h (m.muP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι)).toReal := by
    intro z
    unfold advectionLoss
    rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (hφ _) (abs_nonneg _)) (sq_nonneg _)),
      ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (mul_nonneg (hφ _) (hfs _)) (hpN _)) (hpN _)),
      tsum_eq_toReal_ofReal (f := fun ι : ℤ × ℤ => (m.muP β).wt z.2 * velAmp v ι z.1 z.2 * edgeSum h (m.muP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι)
        (fun ι => mul_nonneg (mul_nonneg (hφ _) (Real.sqrt_nonneg _)) (hedge ι z.1 z.2))]
  have hfun : (fun z : ℝ × Space => advectionLoss h (m.muP β).modes (m.muP β).wt W (m.muP β).frame v z.1 z.2)
      = fun z : ℝ × Space => (ENNReal.ofReal ((m.muP β).wt z.2 * |(m.muP β).frame| * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2) ^ 2)).toReal + (ENNReal.ofReal ((m.muP β).wt z.2 * frameSpeedSup W (m.muP β).frame z.2 * pieceNorm (m.muP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2) * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2))).toReal + (∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt z.2 * velAmp v ι z.1 z.2 * edgeSum h (m.muP β).modes (fun α => velAmp W α z.1 z.2) (fun κ => gradAmp (gradField v) κ z.1 z.2) ι)).toReal := funext hpt
  have i1 := integrable_toReal_of_lintegral_ne_top m1 n1
  have i2 := integrable_toReal_of_lintegral_ne_top m2 n2
  have i3 := integrable_toReal_of_lintegral_ne_top m3 n3
  have j1 := integral_toReal m1 (ae_lt_top' m1 n1)
  have j2 := integral_toReal m2 (ae_lt_top' m2 n2)
  have j3 := integral_toReal m3 (ae_lt_top' m3 n3)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (i1.add i2).add i3
  · have a1 := integral_add i1 i2
    have a2 := integral_add (i1.add i2) i3
    simp only [Pi.add_apply] at a1 a2
    rw [hfun, a2, a1, j1, j2, j3, ← e1, ← e2, ← e3]
    linarith

private theorem advection_bound (hE : edgeSeries h (m.muP β).modes (m.muP β).wt W v < ⊤)
    (h1 : turnBlock (m.muP β).modes (m.muP β).wt (m.muP β).frame v < ⊤)
    (h2 : advectionBlock (m.muP β).modes (m.muP β).wt W (m.muP β).frame v < ⊤) :
    -((edgeSeries h (m.muP β).modes (m.muP β).wt W v).toReal
        + (turnBlock (m.muP β).modes (m.muP β).wt (m.muP β).frame v).toReal
        + (advectionBlock (m.muP β).modes (m.muP β).wt W (m.muP β).frame v).toReal)
      ≤ ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (turnTerm (m.muP β).modes (m.muP β).wt (m.muP β).frame v ι σ y
          + fieldTerm (m.muP β).modes (m.muP β).wt v (frameAdvection W v (m.muP β).frame) ι σ y) := by
  obtain ⟨hi, hsw⟩ := advection_swap m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  obtain ⟨hl, hle⟩ := advection_loss_le m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
    hE h1 h2
  have hae := advection_pointwise m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  have hl' : Integrable (fun z : ℝ × Space => -advectionLoss h (m.muP β).modes (m.muP β).wt W (m.muP β).frame v z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := hl.neg
  have hmono := integral_mono_ae hl' hi (hae.mono fun z hz => hz.2)
  rw [integral_neg] at hmono
  rw [hsw]
  linarith

private theorem sumSecondPartials_term_measurable (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun σ => ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      ≪ (volume : Measure (ℝ × Space)) := ModeL2Internal.slab_ac
  have hx : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι v z.1 z.2 i) volume :=
    fun i => ModeL2Internal.aestronglyMeasurable_modeVel hv.smooth.continuous.aestronglyMeasurable ι i
  have hl : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι (negSumSecondPartialsField v) z.1 z.2 i) volume :=
    fun i => ModeL2Internal.aestronglyMeasurable_modeVel (negSumSecondPartialsField_continuous hv).aestronglyMeasurable ι i
  have hc := ModeL2Internal.aestronglyMeasurable_cdot hx hl
  have hw : Continuous (fun z : ℝ × Space => Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt z.2 : ℝ) : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul (hK.continuous.comp continuous_snd)))
  have hf : AEStronglyMeasurable (fun z : ℝ × Space => fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι z.1 z.2) volume :=
    Complex.continuous_re.comp_aestronglyMeasurable (hw.aestronglyMeasurable.mul hc)
  exact (hf.mono_ac hac).integral_prod_right'

private theorem sumSecondPartials_weight_integrable (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => PieceWeights.wtGrad (m.muP β).wt z.2 * gradAmp (gradField v) ι z.1 z.2
        * velAmp v ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hB0 : 0 ≤ B := (hφ0 0).trans (hB β 0).1
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hp := hSP P v hv
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ (volume : Measure (ℝ × Space)) := ModeL2Internal.slab_ac
  have hG := Internal.FieldModes.integrable_cnormSq_modeGrad hPars hp.measurable_gradient hp.periodic_gradient
    hp.gradient_finite ι
  have hV := ModeL2Internal.integrable_cnormSq_modeVel hPars (Internal.SmoothWeightSplit.scaledField_square hv) ι
  have hg : ∀ y, (1 + ‖y‖) * PieceWeights.wtGrad (m.muP β).wt y ≤ K + B := by
    intro y
    obtain ⟨-, -, b3⟩ := hB β y
    have := norm_fderiv_le_of_lipschitz ℝ hK (x₀ := y)
    unfold PieceWeights.wtGrad at b3 ⊢
    nlinarith
  have hm1 : AEStronglyMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.muP β).wt z.2
      * gradAmp (gradField v) ι z.1 z.2 * velAmp v ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    have a1 : Measurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.muP β).wt z.2) :=
      (measurable_fderiv ℝ (m.muP β).wt).norm.comp measurable_snd
    exact ((a1.aemeasurable.mul ((Internal.PieceAbsorb.aem_gradAmp hp.measurable_gradient ι).mono_ac hac)).mul
      ((Internal.PieceAbsorb.aem_velAmp hp.measurable_velocity ι).mono_ac hac)).aestronglyMeasurable
  refine ((hG.add hV).const_mul (K + B)).mono' hm1 (ae_of_all _ fun z => ?_)
  have hg0 : 0 ≤ gradAmp (gradField v) ι z.1 z.2 := Real.sqrt_nonneg _
  have hu0 : 0 ≤ velAmp v ι z.1 z.2 := Real.sqrt_nonneg _
  have hw0 : 0 ≤ PieceWeights.wtGrad (m.muP β).wt z.2 := norm_nonneg _
  have ht : 0 < 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
  have hgA : cnormSq (modeGrad ι (gradField v) z.1 z.2) = gradAmp (gradField v) ι z.1 z.2 ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
  have hw := Internal.SmoothPieceEps.cnormSq_modeVel_weighted v ι z.1 z.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hw0 hg0) hu0)]
  show _ ≤ (K + B) * (cnormSq (modeGrad ι (gradField v) z.1 z.2)
    + cnormSq (modeVel ι (fun s x => (1 + ‖x‖)⁻¹ • v s x) z.1 z.2))
  rw [hgA, hw]
  set g := gradAmp (gradField v) ι z.1 z.2
  set u := velAmp v ι z.1 z.2
  set t := 1 + ‖z.2‖
  set q := PieceWeights.wtGrad (m.muP β).wt z.2
  have e : q * g * u = (t * q) * (g * (u / t)) := by field_simp
  have hq : g * (u / t) ≤ g ^ 2 + (u / t) ^ 2 := by
    nlinarith [sq_nonneg (g - u / t), div_nonneg hu0 ht.le]
  rw [e]
  calc (t * q) * (g * (u / t)) ≤ (K + B) * (g * (u / t)) :=
        mul_le_mul_of_nonneg_right (hg z.2) (mul_nonneg hg0 (div_nonneg hu0 ht.le))
    _ ≤ (K + B) * (g ^ 2 + (u / t) ^ 2) := mul_le_mul_of_nonneg_left hq (by linarith)

private theorem sumSecondPartials_mode_le (ι : ℤ × ℤ) :
    -(ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
        PieceWeights.wtGrad (m.muP β).wt y * gradAmp (gradField v) ι σ y * velAmp v ι σ y)
      ≤ ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y := by
  have hYi := sumSecondPartials_weight_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM
    hSolenoidal hSP hSsp ι
  have hXm := sumSecondPartials_term_measurable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM
    hSolenoidal hSP hSsp ι
  obtain ⟨K, hK⟩ := hm.mu_increment β
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hφ0 : ∀ y, 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β
  have hB0 : 0 ≤ B := (hφ0 0).trans (hB β 0).1
  have hK0 : (0 : ℝ) ≤ K := K.2
  have haB : ∀ y, (1 + ‖y‖) ^ 2 * |(m.muP β).wt y| ≤ 4 * B + K := by
    intro y
    obtain ⟨b1, b2, -⟩ := hB β y
    rw [abs_of_nonneg (hφ0 y)]
    nlinarith [sq_nonneg (‖y‖ - 1), hφ0 y, norm_nonneg y]
  have hgB : ∀ y, (1 + ‖y‖) * ‖fderiv ℝ (m.muP β).wt y‖ ≤ 4 * B + K := by
    intro y
    obtain ⟨-, -, b3⟩ := hB β y
    have := norm_fderiv_le_of_lipschitz ℝ hK (x₀ := y)
    unfold PieceWeights.wtGrad at b3
    nlinarith
  have hgen := Internal.ModeSumSecondPartials.sumSecondPartials_mode_bound hPars hSsp hv (m.muP β).wt hK haB hgB ι
  set s := PieceWeights.sgn (m.muP β).modes ι
  have hs : |s| = ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) := by
    simp only [s]
    unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
    by_cases h1 : ι ∈ (m.muP β).modes <;> by_cases h2 : -ι ∈ (m.muP β).modes <;> simp [h1, h2]
  have e : ∀ σ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y
      = s * (Complex.I * (((m.muP β).wt y : ℝ) : ℂ) * cdot (modeVel ι v σ y)
          (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)).re := by
    intro σ y
    unfold fieldTerm negSumSecondPartialsField
    rw [Complex.ofReal_mul, show Complex.I * ((s : ℂ) * (((m.muP β).wt y : ℝ) : ℂ)) * cdot (modeVel ι v σ y)
        (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)
      = (s : ℂ) * (Complex.I * (((m.muP β).wt y : ℝ) : ℂ) * cdot (modeVel ι v σ y)
        (modeVel ι (fun s x => -secondDerivTrace (secondDerivField v s x)) σ y)) by ring, Complex.re_ofReal_mul]
  have hY := hYi.integral_prod_left
  have hbound : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y‖
        ≤ ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * ∫ y, PieceWeights.wtGrad (m.muP β).wt y
          * gradAmp (gradField v) ι σ y * velAmp v ι σ y := by
    filter_upwards [hgen] with σ hσ
    obtain ⟨-, -, h3⟩ := hσ
    simp_rw [e]
    rw [integral_const_mul, Real.norm_eq_abs, abs_mul, hs]
    exact mul_le_mul_of_nonneg_left h3 (by rw [← hs]; exact abs_nonneg _)
  have hXi : Integrable (fun σ => ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    Integrable.mono' (hY.const_mul _) hXm hbound
  have hl' : Integrable (fun σ => -(ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * ∫ y,
      PieceWeights.wtGrad (m.muP β).wt y * gradAmp (gradField v) ι σ y * velAmp v ι σ y))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := (hY.const_mul _).neg
  have hmono := integral_mono_ae hl' hXi
    (hbound.mono fun σ hσ => by
      have := neg_abs_le (∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y)
      rw [Real.norm_eq_abs] at hσ
      linarith)
  rw [integral_neg, integral_const_mul] at hmono
  exact hmono

private theorem sumSecondPartials_series_le (h3 : sumSecondPartialsBlock (m.muP β).modes (m.muP β).wt v < ⊤) :
    Summable (fun ι : ℤ × ℤ => ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
        PieceWeights.wtGrad (m.muP β).wt y * gradAmp (gradField v) ι σ y * velAmp v ι σ y) ∧
      ∑' ι : ℤ × ℤ, ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
        PieceWeights.wtGrad (m.muP β).wt y * gradAmp (gradField v) ι σ y * velAmp v ι σ y)
        ≤ (sumSecondPartialsBlock (m.muP β).modes (m.muP β).wt v).toReal := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  have hp := hSP P v hv
  have hac : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪ (volume : Measure (ℝ × Space)) := ModeL2Internal.slab_ac
  have hw0 : ∀ y, 0 ≤ PieceWeights.wtGrad (m.muP β).wt y := fun y => norm_nonneg _
  have hind0 : ∀ ι, 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) := fun ι => by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hG : ∀ ι, AEMeasurable (fun z : ℝ × Space => gradAmp (gradField v) ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    fun ι => (Internal.PieceAbsorb.aem_gradAmp hp.measurable_gradient ι).mono_ac hac
  have hU : ∀ ι, AEMeasurable (fun z : ℝ × Space => velAmp v ι z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    fun ι => (Internal.PieceAbsorb.aem_velAmp hp.measurable_velocity ι).mono_ac hac
  have hWg : AEMeasurable (fun z : ℝ × Space => PieceWeights.wtGrad (m.muP β).wt z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    ((measurable_fderiv ℝ (m.muP β).wt).norm.comp measurable_snd).aemeasurable
  have hF0 : ∀ ι (z : ℝ × Space), 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * (PieceWeights.wtGrad (m.muP β).wt z.2 * gradAmp (gradField v) ι z.1 z.2 * velAmp v ι z.1 z.2) :=
    fun ι z => mul_nonneg (hind0 ι) (mul_nonneg (mul_nonneg (hw0 _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hFm : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * (PieceWeights.wtGrad (m.muP β).wt z.2 * gradAmp (gradField v) ι z.1 z.2 * velAmp v ι z.1 z.2))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_const.mul ((hWg.mul (hG ι)).mul (hU ι)))
  have hYi := sumSecondPartials_weight_integrable m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp
  have key : ∀ ι, ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
        PieceWeights.wtGrad (m.muP β).wt y * gradAmp (gradField v) ι σ y * velAmp v ι σ y)
      = (∫⁻ z, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
          * (PieceWeights.wtGrad (m.muP β).wt z.2 * gradAmp (gradField v) ι z.1 z.2 * velAmp v ι z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))).toReal := by
    intro ι
    rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hF0 ι)) (((hYi ι).const_mul _).aestronglyMeasurable),
      integral_const_mul, integral_prod _ (hYi ι)]
  have hsumA : ∑' ι : ℤ × ℤ, ∫⁻ z, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
          * (PieceWeights.wtGrad (m.muP β).wt z.2 * gradAmp (gradField v) ι z.1 z.2 * velAmp v ι z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
          * (PieceWeights.wtGrad (m.muP β).wt y * gradAmp (gradField v) ι σ y * velAmp v ι σ y)) := by
    rw [← lintegral_tsum hFm, lintegral_prod _ (AEMeasurable.tsum hFm)]
  have hS : AEMeasurable (fun z : ℝ × Space => ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)
      + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable ((hG ι).pow_const 2)).add
      (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
        (((hU ι).div (measurable_const.add (measurable_norm.comp measurable_snd)).aemeasurable).pow_const 2))
  have hSfin : (∫⁻ z, (∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2)
      + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) ≠ ⊤ := by
    rw [lintegral_prod _ hS]
    refine ne_top_of_le_ne_top (Internal.SmoothPieceEps.amplitudeSeries_finite hPars hSP P v hv).ne
      (lintegral_mono fun σ => lintegral_mono fun y => ?_)
    have e4 : ∀ a b c d : ℝ≥0∞, c + d ≤ a + b + c + d := fun a b c d => add_le_add le_add_self le_rfl
    exact e4 _ _ _ _
  have hpt : ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)), ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
          * (PieceWeights.wtGrad (m.muP β).wt z.2 * gradAmp (gradField v) ι z.1 z.2 * velAmp v ι z.1 z.2))
      ≤ ENNReal.ofReal (PieceWeights.wtGrad (m.muP β).wt z.2
        * pieceNorm (m.muP β).modes (fun κ => gradAmp (gradField v) κ z.1 z.2)
        * pieceNorm (m.muP β).modes (fun κ => velAmp v κ z.1 z.2)) := by
    filter_upwards [ae_lt_top' hS hSfin] with z hz
    have h1 : ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι z.1 z.2 ^ 2) ≠ ⊤ :=
      (lt_of_le_of_lt le_self_add hz).ne
    have h2 : ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι z.1 z.2 / (1 + ‖z.2‖)) ^ 2) ≠ ⊤ :=
      (lt_of_le_of_lt le_add_self hz).ne
    have s1 : Summable (fun κ => gradAmp (gradField v) κ z.1 z.2 ^ 2) := by
      have := ENNReal.summable_toReal h1
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using this
    have s2 : Summable (fun κ => (velAmp v κ z.1 z.2 / (1 + ‖z.2‖)) ^ 2) := by
      have := ENNReal.summable_toReal h2
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using this
    have ht : (1 + ‖z.2‖) ≠ 0 := by positivity
    have s3 : Summable (fun κ => velAmp v κ z.1 z.2 ^ 2) := by
      refine (s2.mul_left ((1 + ‖z.2‖) ^ 2)).congr fun κ => ?_
      field_simp
    exact piece_sum_mul_le (m.muP β).modes (hw0 _) _ _ (fun _ => Real.sqrt_nonneg _)
      (fun _ => Real.sqrt_nonneg _) s1 s3
  have hle : ∑' ι : ℤ × ℤ, ∫⁻ z, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
          * (PieceWeights.wtGrad (m.muP β).wt z.2 * gradAmp (gradField v) ι z.1 z.2 * velAmp v ι z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      ≤ sumSecondPartialsBlock (m.muP β).modes (m.muP β).wt v := by
    rw [hsumA]
    unfold sumSecondPartialsBlock
    exact lintegral_mono_ae ((Measure.ae_ae_of_ae_prod hpt).mono fun σ hσ => lintegral_mono_ae hσ)
  have hne : ∀ ι, (∫⁻ z, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * (PieceWeights.wtGrad (m.muP β).wt z.2 * gradAmp (gradField v) ι z.1 z.2 * velAmp v ι z.1 z.2)) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) ≠ ⊤ :=
    fun ι => ne_top_of_le_ne_top (hle.trans_lt h3).ne (ENNReal.le_tsum ι)
  refine ⟨?_, ?_⟩
  · rw [funext key]
    exact ENNReal.summable_toReal (hle.trans_lt h3).ne
  · rw [tsum_congr key, ← ENNReal.tsum_toReal_eq hne]
    exact ENNReal.toReal_mono h3.ne hle

private theorem sumSecondPartials_bound (h3 : sumSecondPartialsBlock (m.muP β).modes (m.muP β).wt v < ⊤) :
    -(sumSecondPartialsBlock (m.muP β).modes (m.muP β).wt v).toReal
      ≤ ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y := by
  obtain ⟨hs, hle⟩ := sumSecondPartials_series_le m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp h3
  by_cases hX : Summable (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      fieldTerm (m.muP β).modes (m.muP β).wt v (negSumSecondPartialsField v) ι σ y)
  · have hm' := hs.neg.tsum_le_tsum (fun ι => sumSecondPartials_mode_le m P h w W hm hW hWp hWdiv hWdecay hwb v hv β
      hPars hDer hRotM hSolenoidal hSP hSsp ι) hX
    rw [tsum_neg] at hm'
    linarith
  · rw [tsum_eq_zero_of_not_summable hX]
    have h0 : 0 ≤ (sumSecondPartialsBlock (m.muP β).modes (m.muP β).wt v).toReal := ENNReal.toReal_nonneg
    linarith

theorem transport_bound
    (hA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt y
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι σ y ^ 2)) < ⊤)
    (hE : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
        * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι)) < ⊤)
    (hBk : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y)) < ⊤) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (m.muP β).wt y
        * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι σ y ^ 2)).toReal - (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
        * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp (gradField v) κ σ y) ι)).toReal - (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y)).toReal ≤ muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) := by
  set T := (m.muP β).modes
  set φ := (m.muP β).wt
  set a := (m.muP β).frame
  have hφ : ∀ y, 0 ≤ φ y := hm.mu_wt_nonneg β
  have hpN : ∀ g : ℤ × ℤ → ℝ, 0 ≤ pieceNorm T g := fun _ => Real.sqrt_nonneg _
  have hfs : ∀ y, 0 ≤ frameSpeedSup W a y := fun y => Real.iSup_nonneg fun _ => norm_nonneg _
  have hwg : ∀ y, 0 ≤ PieceWeights.wtGrad φ y := fun y => norm_nonneg _
  have hblk : ∀ σ y, ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y)
      = ENNReal.ofReal (φ y * |a| * pieceNorm T (fun κ => velAmp v κ σ y) ^ 2)
        + ENNReal.ofReal (φ y * frameSpeedSup W a y
          * pieceNorm T (fun κ => gradAmp (gradField v) κ σ y) * pieceNorm T (fun κ => velAmp v κ σ y))
        + ENNReal.ofReal (PieceWeights.wtGrad φ y
          * pieceNorm T (fun κ => gradAmp (gradField v) κ σ y) * pieceNorm T (fun κ => velAmp v κ σ y)) := by
    intro σ y
    have e1 := mul_nonneg (mul_nonneg (hφ y) (abs_nonneg a)) (sq_nonneg (pieceNorm T (fun κ => velAmp v κ σ y)))
    have e2 := mul_nonneg (mul_nonneg (mul_nonneg (hφ y) (hfs y)) (hpN (fun κ => gradAmp (gradField v) κ σ y)))
      (hpN (fun κ => velAmp v κ σ y))
    have e3 := mul_nonneg (mul_nonneg (hwg y) (hpN (fun κ => gradAmp (gradField v) κ σ y)))
      (hpN (fun κ => velAmp v κ σ y))
    rw [← ENNReal.ofReal_add e1 e2, ← ENNReal.ofReal_add (add_nonneg e1 e2) e3]
    congr 1
    unfold pieceMuBlock
    ring
  have hsum : turnBlock T φ a v + advectionBlock T φ W a v + sumSecondPartialsBlock T φ v
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-pieceMuBlock m W v (gradField v) β σ y) := by
    simp only [hblk]
    exact lintegral_three_le _ _ _
  have h123 := hsum.trans_lt hBk
  have h12 : turnBlock T φ a v + advectionBlock T φ W a v < ⊤ := (le_self_add).trans_lt h123
  have h1 : turnBlock T φ a v < ⊤ := (le_self_add).trans_lt h12
  have h2 : advectionBlock T φ W a v < ⊤ := (le_add_self).trans_lt h12
  have h3 : sumSecondPartialsBlock T φ v < ⊤ := (le_add_self).trans_lt h123
  have hmono := ENNReal.toReal_mono hBk.ne hsum
  rw [ENNReal.toReal_add h12.ne h3.ne, ENNReal.toReal_add h1.ne h2.ne] at hmono
  have hdec := pairing_decomp m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp hA
  have hadv := advection_bound m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp hE h1 h2
  have hssp := sumSecondPartials_bound m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hPars hDer hRotM hSolenoidal hSP hSsp h3
  change _ ≤ muPairing (fun ι y => PieceWeights.sgn T ι * φ y) v (innerField P W v)
  rw [hdec]
  change (freqSeries P T φ a v).toReal - (edgeSeries h T φ W v).toReal - _ ≤ _
  linarith

end Bounds

end Internal.SmoothPieceMuTransport

end Coercive

end Breakdown
