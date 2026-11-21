import Breakdown.Cert.CoerciveSmoothMuWave
import Breakdown.Cert.CoerciveSmoothMuModeCalc
import Breakdown.Cert.CoerciveSmoothPieceMuSumSecondPartials
import Breakdown.Cert.CoerciveSmoothMuDecay

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuTransport

open Internal.MuSmooth Internal.ModeCalc

def slabVol : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume

def sumSecondPartialsPart (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space := -secondDerivTrace (secondDerivField v σ y)

def gradLoss {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  m.muGrad ι y * gradAmp (gradField v) ι σ y * velAmp v ι σ y



def relField (W v : ℝ → Space → Space) (rate : Space → ℝ) (σ : ℝ) (y : Space) : Space :=
  fderiv ℝ (v σ) y (relativeVelocity W rate y)

def waveField (W v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  fderiv ℝ (v σ) y (W σ y - meanField W y)

theorem innerPart_decomp (P : ℝ) (W v : ℝ → Space → Space) (r : Space → ℝ) (s : ℝ) (x : Space) :
    innerPart P W v s x = (1 / P) • timeField v s x + (1 / 2 : ℝ) • v s x + relField W v r s x
      + r x • azimField v s x + waveField W v s x + sumSecondPartialsPart v s x := by
  unfold innerPart transportPart timeField relField azimField waveField sumSecondPartialsPart relativeVelocity
  simp only [map_add, map_sub, map_smul]
  module

theorem timeField_continuous (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => timeField v z.1 z.2) := by
  have hd : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.differentiable (by simp)
  have e : (fun z : ℝ × Space => timeField v z.1 z.2)
      = fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) z (1, 0) := by
    funext z
    unfold timeField
    have h := (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
    exact h.deriv
  rw [e]
  exact ((hv.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem gradField_continuous (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
  (PairingSplitInternal.contDiff_slice (n := 0) hv.smooth
    (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).continuous

theorem sumSecondPartialsPart_continuous (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => sumSecondPartialsPart v z.1 z.2) := by
  have h2 : Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
    (PairingSplitInternal.contDiff_slice (n := 0) (V := fun s x => fderiv ℝ (v s) x)
      (PairingSplitInternal.contDiff_slice (n := ∞) hv.smooth (by simp)) (by simp)).continuous
  unfold sumSecondPartialsPart secondDerivField
  exact (Internal.Field.secondDerivTrace_continuous.comp h2).neg

theorem clm_integrand_continuous {G : ℝ → Space → (Space →L[ℝ] Space)}
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

theorem rotJ_comm (ψ : ℝ) (x : Space) :
    axialRot ψ (-(x 1) • unitVector 0 + x 0 • unitVector 1)
      = -(axialRot ψ x 1) • unitVector 0 + axialRot ψ x 0 • unitVector 1 := by
  ext j
  fin_cases j <;> simp [axialRot, unitVector] <;> ring

theorem rot_neg_rot (φ : ℝ) (x : Space) : axialRot (-φ) (axialRot φ x) = x := by
  have h := rot_rot_neg (-φ) x
  rwa [neg_neg] at h

theorem meanField_rot_coord {W : ℝ → Space → Space} (hWc : Continuous (fun z : ℝ × Space => W z.1 z.2))
    (hWp : IsTimePeriodic W) (φ : ℝ) (x : Space) (i : Fin 3) :
    axialRot (-φ) (meanField W (axialRot φ x)) i = meanField W x i := by
  have h1 := Internal.SmoothPieceMuDivergence.modeVel_shiftRot (0, 0) W hWp 0 φ 0 x i
  have h2 := rot_modeVel_eq hWc (0, 0) 0 0 φ x i
  rw [h2] at h1
  have h3 := congrArg Complex.re h1
  rw [re_sum_real_mul] at h3
  simp only [Int.cast_zero, mul_zero, zero_mul, add_zero, Complex.ofReal_zero, Complex.exp_zero, one_mul] at h3
  unfold meanField
  rw [space_sum_apply]
  rw [← h3, ← rotCoord_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rotCoord_apply, smul_eq_mul, mul_comm]

theorem mode_product_vec (s : Finset (ℤ × ℤ)) (G : ℝ → Space → (Space →L[ℝ] Space)) (U : ℝ → Space → Space)
    (hGc : Continuous fun z : ℝ × Space => G z.1 z.2) (σ : ℝ) (y : Space)
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
  have hMc : ∀ j, Continuous fun p : ℝ × ℝ => M j p.1 p.2 := fun j =>
    Complex.continuous_ofReal.comp (clm_integrand_continuous hGc (u := fun p : ℝ × ℝ => axialRot p.2 (unitVector j))
      (Internal.Field.axialRot_comp_continuous continuous_snd continuous_const) σ y i)
  have hEc : ∀ κ, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 := fun κ => cont_exp_pair κ
  have hmg : ∀ κ j, modeGrad κ G σ y (i, j) = (1 / (2 * Real.pi) : ℂ) * boxInt (fun τ φ => E κ τ φ * M j τ φ) :=
    fun κ j => rfl
  have hpt : ∀ τ φ, E ι τ φ * ((axialRot (-φ) (G (σ + τ) (axialRot φ y) (U (σ + τ) (axialRot φ y))) i : ℝ) : ℂ)
      = ∑ j : Fin 3, ((c j : ℂ) * (E ι τ φ * M j τ φ) + ∑ α ∈ s, d α j * (E (ι - α) τ φ * M j τ φ)) := by
    intro τ φ
    rw [rot_apply_clm]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hE τ φ j, hEdef, hMdef]
    simp only
    simp only [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [← exp_pair_mul ι α τ φ]
      ring
  have hlhs : modeVel ι (fun σ y => G σ y (U σ y)) σ y i
      = (1 / (2 * Real.pi) : ℂ) * boxInt (fun τ φ => ∑ j : Fin 3, ((c j : ℂ) * (E ι τ φ * M j τ φ)
        + ∑ α ∈ s, d α j * (E (ι - α) τ φ * M j τ φ))) := by
    rw [← funext fun τ => funext fun φ => hpt τ φ]
    rfl
  have hc1 : ∀ κ j, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 * M j p.1 p.2 := fun κ j => (hEc κ).mul (hMc j)
  rw [hlhs, boxInt_sum _ _ (fun j => ((continuous_const.mul (hc1 ι j)).add
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j))))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [boxInt_add _ _ (continuous_const.mul (hc1 ι j))
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j)),
    boxInt_sum _ _ (fun α => continuous_const.mul (hc1 (ι - α) j)), boxInt_const_mul]
  simp_rw [boxInt_const_mul, hmg]
  rw [mul_add, Finset.mul_sum, mul_left_comm]
  congr 1
  exact Finset.sum_congr rfl fun α _ => mul_left_comm _ _ _

theorem cnorm3_real (u : Space) : cnorm3 (fun j => ((u j : ℝ) : ℂ)) = ‖u‖ := by
  unfold cnorm3 cnormSq
  rw [← Real.sqrt_sq (norm_nonneg u), space_norm_sq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem rel_mode_le (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    Real.sqrt (cnormSq (modeVel ι (relField W v (m.rate (m.classOf ι))) σ y))
      ≤ ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ * gradAmp (gradField v) ι σ y := by
  set r := m.rate (m.classOf ι) with hrdef
  set u := relativeVelocity W r with hudef
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have hcov : ∀ φ j, axialRot (-φ) (u (axialRot φ y)) j = u y j := by
    intro φ j
    rw [hudef]
    unfold relativeVelocity
    have hr : r (axialRot φ y) = r y := hm.rate_axi _ φ y
    rw [hr, ← rotCoord_apply, map_sub, map_add, map_smul, map_smul, rotCoord_apply,
      rotCoord_apply, rotCoord_apply, meanField_rot_coord hWc hWp, rotJ_comm, rot_neg_rot]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have hG : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) := gradField_continuous P v hv
  have hmode : ∀ i, modeVel ι (relField W v r) σ y i
      = ∑ j : Fin 3, modeGrad ι (gradField v) σ y (i, j) * ((u y j : ℝ) : ℂ) := by
    intro i
    have h := mode_product_vec ∅ (gradField v) (fun _ x => u x) hG σ y (fun j => u y j) (fun _ _ => 0)
      (fun τ φ j => by rw [hcov]; simp) ι i
    rw [show modeVel ι (relField W v r) σ y i = modeVel ι (fun σ y => gradField v σ y (u y)) σ y i from rfl, h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_empty, add_zero]
    ring
  have e : modeVel ι (relField W v r) σ y = fun i => ∑ j : Fin 3, modeGrad ι (gradField v) σ y (i, j) * ((u y j : ℝ) : ℂ) :=
    funext hmode
  show cnorm3 (modeVel ι (relField W v r) σ y) ≤ ‖u y‖ * gradAmp (gradField v) ι σ y
  rw [e]
  refine (cnorm3_mat_le _ _).trans ?_
  rw [cnorm3_real, mul_comm]
  rfl

theorem wave_mode_le (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    Real.sqrt (cnormSq (modeVel ι (waveField W v) σ y))
      ≤ ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y := by
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have hG : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) := gradField_continuous P v hv
  have hE : ∀ τ φ : ℝ, ∀ j : Fin 3,
      ((axialRot (-φ) ((fun s x => W s x - meanField W x) (σ + τ) (axialRot φ y)) j : ℝ) : ℂ)
        = ((0 : ℝ) : ℂ) + ∑ α ∈ m.waves, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeVel α W σ y j := by
    intro τ φ j
    simp only
    rw [← rotCoord_apply, map_sub, rotCoord_apply, rotCoord_apply, meanField_rot_coord hWc hWp,
      rot_field_expansion hWc hWp m.waves hb.harmonics σ τ φ y j, modeVel_mean_shift hWp σ y j]
    have hm0 : meanField W y j = (modeVel (0, 0) W 0 y j).re := by
      unfold meanField
      rw [space_sum_apply]
    rw [hm0, add_sub_cancel_left, Complex.ofReal_zero, zero_add]
    refine re_sum_sym m.waves hm.waves_neg _ fun α => ?_
    rw [phase_neg, Internal.SmoothPieceMuDivergence.modeVel_neg, map_mul]
  have h := fun i => mode_product_vec m.waves (gradField v) (fun s x => W s x - meanField W x) hG σ y
    (fun _ => 0) (fun α j => modeVel α W σ y j) hE ι i
  have e : modeVel ι (waveField W v) σ y
      = ∑ α ∈ m.waves, fun i => ∑ j : Fin 3, modeGrad (ι - α) (gradField v) σ y (i, j) * modeVel α W σ y j := by
    funext i
    rw [Finset.sum_apply, show modeVel ι (waveField W v) σ y i
      = modeVel ι (fun σ y => gradField v σ y ((fun s x => W s x - meanField W x) σ y)) σ y i from rfl, h i]
    simp only [Complex.ofReal_zero, zero_mul, zero_add]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  show cnorm3 (modeVel ι (waveField W v) σ y) ≤ _
  rw [e]
  refine (cnorm3_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  refine (cnorm3_mat_le _ _).trans ?_
  rw [mul_comm]
  rfl

theorem inner_mode_linear (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (innerPart P W v) σ y = fun i =>
      (1 / P : ℂ) * modeVel ι (timeField v) σ y i + (1 / 2 : ℂ) * modeVel ι v σ y i
        + modeVel ι (relField W v (m.rate (m.classOf ι))) σ y i
        + (m.rate (m.classOf ι) y : ℂ) * modeVel ι (azimField v) σ y i
        + modeVel ι (waveField W v) σ y i + modeVel ι (sumSecondPartialsPart v) σ y i := by
  set r := m.rate (m.classOf ι) with hrdef
  have hr : ∀ φ, r (axialRot φ y) = r y := fun φ => hm.rate_axi _ φ y
  have hG := gradField_continuous P v hv
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hmF : Continuous (meanField W) := meanField_continuous hW.continuous
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have hrot : Continuous (fun p : ℝ × ℝ => axialRot p.2 y) :=
    Internal.Field.axialRot_comp_continuous continuous_snd continuous_const
  have haz : Continuous (fun x : Space => -(x 1) • unitVector 0 + x 0 • unitVector 1) := by
    fun_prop
  funext i
  have cT := Internal.Field.mode_integrand_continuous (timeField_continuous P v hv) σ y i
  have cV := Internal.Field.mode_integrand_continuous hvc σ y i
  have cL := Internal.Field.mode_integrand_continuous (sumSecondPartialsPart_continuous P v hv) σ y i
  have cA : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (azimField v (σ + p.1) (axialRot p.2 y)) i) :=
    by
      unfold azimField
      exact clm_integrand_continuous (G := fun s x => fderiv ℝ (v s) x)
        (u := fun p : ℝ × ℝ => -(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1) hG (haz.comp hrot) σ y i
  have cR : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (relField W v r (σ + p.1) (axialRot p.2 y)) i) := by
    have hu : Continuous (fun p : ℝ × ℝ => relativeVelocity W r (axialRot p.2 y)) := by
      have e : (fun p : ℝ × ℝ => relativeVelocity W r (axialRot p.2 y)) = fun p : ℝ × ℝ =>
          meanField W (axialRot p.2 y) + (1 / 2 : ℝ) • axialRot p.2 y
            - r y • (-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1) := by
        funext p
        unfold relativeVelocity
        rw [hr]
      rw [e]
      exact ((hmF.comp hrot).add ((continuous_const (y := (1 / 2 : ℝ))).smul hrot)).sub
        ((continuous_const (y := r y)).smul (haz.comp hrot))
    unfold relField
    exact clm_integrand_continuous (G := fun s x => fderiv ℝ (v s) x)
      (u := fun p : ℝ × ℝ => relativeVelocity W r (axialRot p.2 y)) hG hu σ y i
  have cWv : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (waveField W v (σ + p.1) (axialRot p.2 y)) i) := by
    have hu : Continuous (fun p : ℝ × ℝ => W (σ + p.1) (axialRot p.2 y) - meanField W (axialRot p.2 y)) :=
      (hWc.comp ((continuous_const.add continuous_fst).prodMk hrot)).sub (hmF.comp hrot)
    unfold waveField
    exact clm_integrand_continuous (G := fun s x => fderiv ℝ (v s) x)
      (u := fun p : ℝ × ℝ => W (σ + p.1) (axialRot p.2 y) - meanField W (axialRot p.2 y)) hG hu σ y i
  have hpt : (fun τ φ (j : Fin 3) => axialRot (-φ) (innerPart P W v (σ + τ) (axialRot φ y)) j)
      = fun τ φ j => (1 / P) * axialRot (-φ) (timeField v (σ + τ) (axialRot φ y)) j
        + (1 / 2 : ℝ) * axialRot (-φ) (v (σ + τ) (axialRot φ y)) j
        + axialRot (-φ) (relField W v r (σ + τ) (axialRot φ y)) j
        + r y * axialRot (-φ) (azimField v (σ + τ) (axialRot φ y)) j
        + axialRot (-φ) (waveField W v (σ + τ) (axialRot φ y)) j
        + axialRot (-φ) (sumSecondPartialsPart v (σ + τ) (axialRot φ y)) j := by
    funext τ φ j
    rw [innerPart_decomp P W v r, hr]
    simp only [Internal.Field.axialRot_add, Internal.Field.axialRot_smul, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
  unfold modeVel
  rw [hpt]
  rw [Internal.Field.modeAverage_add _ _ _ _ (by
        exact ((((continuous_const.mul cT).add (continuous_const.mul cV)).add cR).add
          (continuous_const.mul cA)).add cWv) cL,
    Internal.Field.modeAverage_add _ _ _ _ (by
        exact (((continuous_const.mul cT).add (continuous_const.mul cV)).add cR).add
          (continuous_const.mul cA)) cWv,
    Internal.Field.modeAverage_add _ _ _ _ (by
        exact ((continuous_const.mul cT).add (continuous_const.mul cV)).add cR) (continuous_const.mul cA),
    Internal.Field.modeAverage_add _ _ _ _ (by
        exact (continuous_const.mul cT).add (continuous_const.mul cV)) cR,
    Internal.Field.modeAverage_add _ _ _ _ (continuous_const.mul cT) (continuous_const.mul cV),
    Internal.Field.modeAverage_const_mul, Internal.Field.modeAverage_const_mul,
    Internal.Field.modeAverage_const_mul]
  push_cast
  ring


theorem inner_mode_split (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    ∃ R S : Fin 3 → ℂ,
      Real.sqrt (cnormSq R) ≤ ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ * gradAmp (gradField v) ι σ y ∧
      Real.sqrt (cnormSq S) ≤ ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y ∧
      modeVel ι (innerPart P W v) σ y = fun i =>
        ((m.dop P ι y : ℂ) * Complex.I) * modeVel ι v σ y i
          + (m.rate (m.classOf ι) y : ℂ) * rotZ (modeVel ι v σ y) i
          + (1 / 2 : ℂ) * modeVel ι v σ y i + R i + S i + modeVel ι (sumSecondPartialsPart v) σ y i := by
  refine ⟨_, _, rel_mode_le hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι σ y,
    wave_mode_le hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι σ y, ?_⟩
  rw [inner_mode_linear hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι σ y,
    Internal.ModeCalc.time_mode P v hv ι σ y, Internal.ModeCalc.azim_mode P v hv ι σ y]
  have hP : P ≠ 0 := hm.period_pos.ne'
  funext i
  simp only [ModeWeights.dop, shiftedFrequency]
  push_cast
  field_simp
  ring


theorem norm_cdot_le_amp (x z : Fin 3 → ℂ) :
    ‖cdot x z‖ ≤ Real.sqrt (cnormSq x) * Real.sqrt (cnormSq z) := by
  unfold cdot cnormSq
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ‖x i * (starRingEnd ℂ) (z i)‖ = ‖x i‖ * ‖z i‖ :=
    fun i _ => by rw [norm_mul, Complex.norm_conj]
  rw [Finset.sum_congr rfl h]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem cnormSq_rotZ_le (x : Fin 3 → ℂ) : cnormSq (rotZ x) ≤ cnormSq x := by
  unfold cnormSq rotZ
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, norm_neg, norm_zero]
  nlinarith [sq_nonneg ‖x 2‖]

theorem pairTerm_expand (μ d r : ℝ) (x J R S L : Fin 3 → ℂ) :
    (Complex.I * (μ : ℂ) * cdot x (fun i => ((d : ℂ) * Complex.I) * x i + (r : ℂ) * J i
        + (1 / 2 : ℂ) * x i + R i + S i + L i)).re
      = μ * d * cnormSq x + (Complex.I * (μ : ℂ) * ((r : ℂ) * cdot x J)).re
        + (Complex.I * (μ : ℂ) * cdot x R).re + (Complex.I * (μ : ℂ) * cdot x S).re
        + (Complex.I * (μ : ℂ) * cdot x L).re := by
  simp only [cdot, cnormSq, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, map_add, map_mul, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply, Complex.conj_ofReal,
    Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im]
  ring

theorem abs_re_I_mul_le (μ : ℝ) (z : ℂ) : |(Complex.I * (μ : ℂ) * z).re| ≤ |μ| * ‖z‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem transport_pointwise (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    dopDensity m P v ι σ y - (transportLoss m W v ι σ y - gradLoss m v ι σ y)
        + pairTerm m v (sumSecondPartialsPart v) ι σ y
      ≤ pairTerm m v (innerPart P W v) ι σ y := by
  obtain ⟨R, S, hR, hS, hX⟩ :=
    inner_mode_split hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι σ y
  set x := modeVel ι v σ y with hxdef
  set μt := m.muW (m.classOf ι) y
  set d := m.dop P ι y with hddef
  set r := m.rate (m.classOf ι) y with hrdef
  set c := cnormSq x with hcdef
  have hc0 : 0 ≤ c := cnorm_nonneg x
  have hva : velAmp v ι σ y = Real.sqrt c := rfl
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
  have hmu : m.mu ι y = |μt| := rfl
  have hdop : μt * d = |μt| * |d| := by
    rw [← abs_mul, abs_of_nonneg (by rw [mul_comm]; exact hm.muW_sign ι y)]
  have e : pairTerm m v (innerPart P W v) ι σ y
      = μt * d * c + (Complex.I * (μt : ℂ) * ((r : ℂ) * cdot x (rotZ x))).re
        + (Complex.I * (μt : ℂ) * cdot x R).re + (Complex.I * (μt : ℂ) * cdot x S).re
        + pairTerm m v (sumSecondPartialsPart v) ι σ y := by
    unfold pairTerm
    rw [hX]
    exact pairTerm_expand μt d r x (rotZ x) R S (modeVel ι (sumSecondPartialsPart v) σ y)
  have hJ : |(Complex.I * (μt : ℂ) * ((r : ℂ) * cdot x (rotZ x))).re| ≤ |μt| * |r| * c := by
    refine (abs_re_I_mul_le μt _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)) (abs_nonneg μt)
    refine (norm_cdot_le_amp x (rotZ x)).trans ?_
    have := Real.sqrt_le_sqrt (cnormSq_rotZ_le x)
    calc Real.sqrt c * Real.sqrt (cnormSq (rotZ x)) ≤ Real.sqrt c * Real.sqrt c :=
          mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = c := Real.mul_self_sqrt hc0
  have hRb : |(Complex.I * (μt : ℂ) * cdot x R).re|
      ≤ |μt| * Real.sqrt c * (‖relativeVelocity W (m.rate (m.classOf ι)) y‖ * gradAmp (gradField v) ι σ y) := by
    refine (abs_re_I_mul_le μt _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_cdot_le_amp x R).trans
      (mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _))) (abs_nonneg μt)
  have hSb : |(Complex.I * (μt : ℂ) * cdot x S).re|
      ≤ |μt| * Real.sqrt c * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y := by
    refine (abs_re_I_mul_le μt _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_cdot_le_amp x S).trans
      (mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _))) (abs_nonneg μt)
  have hL : dopDensity m P v ι σ y - (transportLoss m W v ι σ y - gradLoss m v ι σ y)
      = |μt| * |d| * c - (|μt| * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ * gradAmp (gradField v) ι σ y * Real.sqrt c
        + |μt| * |r| * c + |μt| * Real.sqrt c
          * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y) := by
    unfold dopDensity transportLoss gradLoss
    rw [hmu, hva, hsq]
    simp only [← hddef, ← hrdef, ← hxdef, ← hcdef]
    ring
  rw [hL, e, hdop]
  have k1 := neg_abs_le (Complex.I * (μt : ℂ) * ((r : ℂ) * cdot x (rotZ x))).re
  have k2 := neg_abs_le (Complex.I * (μt : ℂ) * cdot x R).re
  have k3 := neg_abs_le (Complex.I * (μt : ℂ) * cdot x S).re
  nlinarith [k1, k2, k3, hJ, hRb, hSb]


theorem sumSecondPartials_slice (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      -(∫ y, gradLoss m v ι σ y) ≤ ∫ y, pairTerm m v (sumSecondPartialsPart v) ι σ y := by
  obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
  obtain ⟨B, hB⟩ := hm.muW_decay
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (m.classOf ι) 0).1
  have haB : ∀ y, (1 + ‖y‖) ^ 2 * |m.muW (m.classOf ι) y| ≤ 4 * B := by
    intro y
    obtain ⟨h1, h2, -⟩ := hB (m.classOf ι) y
    have hy := norm_nonneg y
    have ha := abs_nonneg (m.muW (m.classOf ι) y)
    nlinarith [sq_nonneg (‖y‖ - 1), mul_nonneg ha (sq_nonneg (‖y‖ - 1))]
  have hgB : ∀ y, (1 + ‖y‖) * ‖fderiv ℝ (m.muW (m.classOf ι)) y‖ ≤ K + B := by
    intro y
    obtain ⟨-, -, h3⟩ := hB (m.classOf ι) y
    have hk : ‖fderiv ℝ (m.muW (m.classOf ι)) y‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ hK
    nlinarith
  have hL := Internal.ModeSumSecondPartials.sumSecondPartials_mode_bound hPars hSsp hv (m.muW (m.classOf ι)) hK
    (B := max (4 * B) (K + B)) (fun y => (haB y).trans (le_max_left _ _)) (fun y => (hgB y).trans (le_max_right _ _)) ι
  filter_upwards [hL] with σ hσ
  exact (neg_le_neg hσ.2.2).trans (neg_abs_le _)
theorem integrable_dopDensity (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => dopDensity m P v ι z.1 z.2) slabVol := by
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  obtain ⟨Bm, hBm⟩ := hm.muW_decay
  obtain ⟨Br, hBr⟩ := hm.rate_bounded
  set Dd := |2 * Real.pi * (ι.1 : ℝ) / P| + |(ι.2 : ℝ)| * Br with hDd
  have hWv := (Internal.FieldModes.integrable_cnormSq_modeVel hPars (X := Internal.MuSmooth.weighted v)
        ⟨(Internal.MuSmooth.weighted_continuous v hvc).aestronglyMeasurable,
          Internal.MuSmooth.weighted_periodic v hv.periodic, Internal.MuSmooth.weighted_square P v hv⟩ ι)
  have hmeas : Measurable (fun z : ℝ × Space => dopDensity m P v ι z.1 z.2) := by
    have h := (dop_measurable_of m P b w hm v hv ι).ennreal_toReal
    convert h using 1
    funext z
    exact (ENNReal.toReal_ofReal (dopDensity_nonneg m P v ι z.1 z.2)).symm
  refine (hWv.const_mul (4 * Bm * Dd)).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_of_nonneg (dopDensity_nonneg m P v ι z.1 z.2)]
  obtain ⟨hb1, hb2, -⟩ := hBm (m.classOf ι) z.2
  have hmu0 : 0 ≤ m.mu ι z.2 := abs_nonneg _
  have hmu1 : m.mu ι z.2 ≤ Bm := hb1
  have hmu2 : ‖z.2‖ ^ 2 * m.mu ι z.2 ≤ Bm := hb2
  have ht : 0 ≤ ‖z.2‖ := norm_nonneg _
  have hmu : m.mu ι z.2 * (1 + ‖z.2‖) ^ 2 ≤ 4 * Bm := by
    nlinarith [mul_nonneg hmu0 (sq_nonneg (‖z.2‖ - 1))]
  have hdop : |m.dop P ι z.2| ≤ Dd := by
    unfold ModeWeights.dop shiftedFrequency
    refine (abs_add_le _ _).trans ?_
    rw [hDd, abs_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hBr _ _) (abs_nonneg _))
  have hX : 0 ≤ cnormSq (modeVel ι v z.1 z.2) := cnorm_nonneg _
  have hu : 0 < (1 + ‖z.2‖) ^ 2 := by positivity
  have key : m.mu ι z.2 * (1 + ‖z.2‖) ^ 2 * |m.dop P ι z.2| ≤ 4 * Bm * Dd :=
    mul_le_mul hmu hdop (abs_nonneg _) (by linarith [mul_nonneg hmu0 hu.le])
  unfold dopDensity
  rw [Internal.MuSmooth.cnormSq_weighted, mul_div_assoc', le_div_iff₀ hu]
  nlinarith [mul_le_mul_of_nonneg_right key hX]

theorem integrable_transportLoss (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => transportLoss m W v ι z.1 z.2) slabVol := by
  obtain ⟨K, hK0, hK⟩ := Internal.MuSmooth.rest_pointwise m P b w W hm hb hW hWp hWdecay v hv
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hGv : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) :=
    (PairingSplitInternal.contDiff_slice (n := 0) hv.smooth (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).continuous
  have hG : periodLIntegral (fun σ y => matSq (gradField v σ y)) < ⊤ := by
    have h1 := hv.derivatives_finite 1 le_rfl
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := 3)) h1)
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun σ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    show matSq (gradField v σ y) ≤ 3 * ‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2
    rw [norm_iteratedFDeriv_one]
    set A := fderiv ℝ (v σ) y
    unfold matSq
    have h : ∀ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ‖A‖ ^ 2 := fun i => by
      have := A.le_opNorm (unitVector i)
      rw [show ‖unitVector i‖ = 1 by unfold unitVector; simp, mul_one] at this
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    calc ∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖A‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
      _ = 3 * ‖A‖ ^ 2 := by simp
  have hGp : IsTimePeriodic (gradField v) := fun σ y => by
    unfold gradField
    rw [show v (σ + 1) = v σ from funext (hv.periodic σ)]
  have i1 : ∀ κ, Integrable (fun z : ℝ × Space => Internal.MuSmooth.modeEnergy v κ z.1 z.2) slabVol := fun κ =>
    (Internal.FieldModes.integrable_cnormSq_modeGrad hPars hGv.aestronglyMeasurable hGp hG κ).add
      (Internal.FieldModes.integrable_cnormSq_modeVel hPars (X := Internal.MuSmooth.weighted v)
        ⟨(Internal.MuSmooth.weighted_continuous v hvc).aestronglyMeasurable,
          Internal.MuSmooth.weighted_periodic v hv.periodic, Internal.MuSmooth.weighted_square P v hv⟩ κ)
  have hE : Integrable (fun z : ℝ × Space => K * (Internal.MuSmooth.modeEnergy v ι z.1 z.2
      + ∑ α ∈ m.waves, Internal.MuSmooth.modeEnergy v (ι - α) z.1 z.2)) slabVol :=
    ((i1 ι).add (integrable_finsetSum _ fun α _ => i1 (ι - α))).const_mul K
  refine hE.mono' (Internal.MuSmooth.loss_measurable_of m P b w W hm hW v hv ι).1.aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_of_nonneg (Internal.MuSmooth.transportLoss_nonneg m W v ι z.1 z.2)]
  exact (le_add_of_nonneg_right (Internal.MuSmooth.pressureLoss_nonneg m hm.eta_pos W v ι z.1 z.2)).trans
    (hK ι z.1 z.2)

theorem integrable_gradLoss (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => gradLoss m v ι z.1 z.2) slabVol := by
  have hT := integrable_transportLoss hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hGv : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) :=
    (PairingSplitInternal.contDiff_slice (n := 0) hv.smooth (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).continuous
  have hmg : Measurable (fun z : ℝ × Space => m.muGrad ι z.2) :=
    (measurable_fderiv ℝ (m.muW (m.classOf ι))).norm.comp measurable_snd
  have hga : Continuous (fun z : ℝ × Space => gradAmp (gradField v) ι z.1 z.2) := by
    unfold gradAmp cnormSq
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ((continuous_modeGrad hGv ι i).norm).pow 2)
  have hva : Continuous (fun z : ℝ × Space => velAmp v ι z.1 z.2) :=
    Real.continuous_sqrt.comp (continuous_cnormSq_modeVel hvc ι)
  refine hT.mono' ((hmg.mul hga.measurable).mul hva.measurable).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have hg0 : 0 ≤ gradLoss m v ι z.1 z.2 :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg hg0]
  unfold gradLoss transportLoss
  have h1 : 0 ≤ m.mu ι z.2 := abs_nonneg _
  have h2 : 0 ≤ ‖relativeVelocity W (m.rate (m.classOf ι)) z.2‖ := norm_nonneg _
  have h3 : 0 ≤ gradAmp (gradField v) ι z.1 z.2 := Real.sqrt_nonneg _
  have h4 : 0 ≤ velAmp v ι z.1 z.2 := Real.sqrt_nonneg _
  have h5 : 0 ≤ m.mu ι z.2 * |m.rate (m.classOf ι) z.2| * velAmp v ι z.1 z.2 ^ 2 := by positivity
  have h6 : 0 ≤ ∑ α ∈ m.waves, velAmp W α z.1 z.2 * gradAmp (gradField v) (ι - α) z.1 z.2 :=
    Finset.sum_nonneg fun α _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h7 : 0 ≤ m.mu ι z.2 * ‖relativeVelocity W (m.rate (m.classOf ι)) z.2‖
      * gradAmp (gradField v) ι z.1 z.2 * velAmp v ι z.1 z.2 := by positivity
  nlinarith [mul_nonneg (mul_nonneg h1 h4) h6]

theorem gradLoss_nonneg {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    0 ≤ gradLoss m v ι σ y := by
  unfold gradLoss
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem pairTerm_continuous {C : Type} (m : ModeWeights C) {K : NNReal} (ι : ℤ × ℤ)
    (hK : LipschitzWith K (m.muW (m.classOf ι))) {v Q : ℝ → Space → Space}
    (hv : Continuous (fun z : ℝ × Space => v z.1 z.2)) (hQ : Continuous (fun z : ℝ × Space => Q z.1 z.2)) :
    Continuous (fun z : ℝ × Space => pairTerm m v Q ι z.1 z.2) := by
  unfold pairTerm cdot
  exact Complex.continuous_re.comp ((continuous_const.mul (Complex.continuous_ofReal.comp
    (hK.continuous.comp continuous_snd))).mul (continuous_finsetSum _ fun i _ =>
      (continuous_modeVel hv ι i).mul (Complex.continuous_conj.comp (continuous_modeVel hQ ι i))))

theorem sumSecondPartialsPart_square (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    Internal.FieldModes.IsSquareField (sumSecondPartialsPart v) := by
  refine ⟨(sumSecondPartialsPart_continuous P v hv).aestronglyMeasurable, fun σ y => ?_, ?_⟩
  · unfold sumSecondPartialsPart secondDerivField
    rw [show v (σ + 1) = v σ from funext (hv.periodic σ)]
  · have h := (SmoothBaseInternal.smooth_fields_finite hv (w := fun _ => 0) (fun _ => le_rfl) (B := 0)
      (fun _ => le_rfl) measurable_const).2.2.1
    have e : (fun σ y => ‖sumSecondPartialsPart v σ y‖ ^ 2) = fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 := by
      funext σ y
      unfold sumSecondPartialsPart
      rw [norm_neg]
    rw [e]
    exact h

theorem pairTerm_weighted_le {C : Type} (m : ModeWeights C) (v Q : ℝ → Space → Space) (ι : ℤ × ℤ) {B : ℝ}
    (hB : ∀ y, (1 + ‖y‖) ^ 2 * |m.muW (m.classOf ι) y| ≤ 4 * B) (σ : ℝ) (y : Space) :
    ‖pairTerm m v Q ι σ y‖ ≤ 2 * B * (cnormSq (modeVel ι (weighted v) σ y) + cnormSq (modeVel ι Q σ y)) := by
  set μt := m.muW (m.classOf ι) y
  set c := cnormSq (modeVel ι v σ y) with hcdef
  set q := cnormSq (modeVel ι Q σ y) with hqdef
  have hc0 : 0 ≤ c := cnorm_nonneg _
  have hq0 : 0 ≤ q := cnorm_nonneg _
  have ht : 1 ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
  have ht0 : 0 < 1 + ‖y‖ := by linarith
  set t := 1 + ‖y‖ with htdef
  set a := Real.sqrt c / t with hadef
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) ht0.le
  have hac : Real.sqrt c = a * t := by rw [hadef]; field_simp
  have hwa : cnormSq (modeVel ι (weighted v) σ y) = a ^ 2 := by
    rw [cnormSq_weighted, hadef, div_pow, Real.sq_sqrt hc0]
  have hqb : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  have hM0 : 0 ≤ |μt| := abs_nonneg _
  have hMt : |μt| * t ≤ 4 * B := by
    have h1 := hB y
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr ht), mul_nonneg hM0 ht0.le]
  have hB0 : 0 ≤ B := by nlinarith [mul_nonneg hM0 ht0.le]
  have h1 : ‖pairTerm m v Q ι σ y‖ ≤ |μt| * (Real.sqrt c * Real.sqrt q) := by
    unfold pairTerm
    rw [Real.norm_eq_abs]
    refine (abs_re_I_mul_le μt _).trans (mul_le_mul_of_nonneg_left (norm_cdot_le_amp _ _) hM0)
  rw [hwa]
  refine h1.trans ?_
  rw [hac]
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have h2 : |μt| * (a * t * Real.sqrt q) ≤ 4 * B * (a * Real.sqrt q) := by
    have := mul_le_mul_of_nonneg_right hMt (mul_nonneg ha0 hs0)
    nlinarith
  nlinarith [sq_nonneg (a - Real.sqrt q), mul_nonneg hB0 (sq_nonneg (a - Real.sqrt q))]

theorem integrable_pairSumSecondPartials (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => pairTerm m v (sumSecondPartialsPart v) ι z.1 z.2) slabVol := by
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
  obtain ⟨B, hB⟩ := hm.muW_decay
  have haB : ∀ y, (1 + ‖y‖) ^ 2 * |m.muW (m.classOf ι) y| ≤ 4 * B := by
    intro y
    obtain ⟨h1, h2, -⟩ := hB (m.classOf ι) y
    have hy := norm_nonneg y
    have ha := abs_nonneg (m.muW (m.classOf ι) y)
    nlinarith [sq_nonneg (‖y‖ - 1), mul_nonneg ha (sq_nonneg (‖y‖ - 1))]
  have hWv := Internal.FieldModes.integrable_cnormSq_modeVel hPars (X := Internal.MuSmooth.weighted v)
    ⟨(Internal.MuSmooth.weighted_continuous v hvc).aestronglyMeasurable,
      Internal.MuSmooth.weighted_periodic v hv.periodic, Internal.MuSmooth.weighted_square P v hv⟩ ι
  have hLv := Internal.FieldModes.integrable_cnormSq_modeVel hPars (sumSecondPartialsPart_square P v hv) ι
  refine ((hWv.add hLv).const_mul (2 * B)).mono'
    (pairTerm_continuous m ι hK hvc (sumSecondPartialsPart_continuous P v hv)).aestronglyMeasurable
    (ae_of_all _ fun z => pairTerm_weighted_le m v (sumSecondPartialsPart v) ι haB z.1 z.2)

theorem inner_pointwise_abs (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    |pairTerm m v (innerPart P W v) ι σ y - pairTerm m v (sumSecondPartialsPart v) ι σ y - dopDensity m P v ι σ y|
      ≤ transportLoss m W v ι σ y - gradLoss m v ι σ y := by
  obtain ⟨R, S, hR, hS, hX⟩ :=
    inner_mode_split hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι σ y
  set x := modeVel ι v σ y with hxdef
  set μt := m.muW (m.classOf ι) y
  set d := m.dop P ι y with hddef
  set r := m.rate (m.classOf ι) y with hrdef
  set c := cnormSq x with hcdef
  have hc0 : 0 ≤ c := cnorm_nonneg x
  have hva : velAmp v ι σ y = Real.sqrt c := rfl
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
  have hmu : m.mu ι y = |μt| := rfl
  have hdop : μt * d = |μt| * |d| := by
    rw [← abs_mul, abs_of_nonneg (by rw [mul_comm]; exact hm.muW_sign ι y)]
  have e : pairTerm m v (innerPart P W v) ι σ y
      = μt * d * c + (Complex.I * (μt : ℂ) * ((r : ℂ) * cdot x (rotZ x))).re
        + (Complex.I * (μt : ℂ) * cdot x R).re + (Complex.I * (μt : ℂ) * cdot x S).re
        + pairTerm m v (sumSecondPartialsPart v) ι σ y := by
    unfold pairTerm
    rw [hX]
    exact pairTerm_expand μt d r x (rotZ x) R S (modeVel ι (sumSecondPartialsPart v) σ y)
  have hJ : |(Complex.I * (μt : ℂ) * ((r : ℂ) * cdot x (rotZ x))).re| ≤ |μt| * |r| * c := by
    refine (abs_re_I_mul_le μt _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)) (abs_nonneg μt)
    refine (norm_cdot_le_amp x (rotZ x)).trans ?_
    have := Real.sqrt_le_sqrt (cnormSq_rotZ_le x)
    calc Real.sqrt c * Real.sqrt (cnormSq (rotZ x)) ≤ Real.sqrt c * Real.sqrt c :=
          mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = c := Real.mul_self_sqrt hc0
  have hRb : |(Complex.I * (μt : ℂ) * cdot x R).re|
      ≤ |μt| * Real.sqrt c * (‖relativeVelocity W (m.rate (m.classOf ι)) y‖ * gradAmp (gradField v) ι σ y) := by
    refine (abs_re_I_mul_le μt _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_cdot_le_amp x R).trans
      (mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _))) (abs_nonneg μt)
  have hSb : |(Complex.I * (μt : ℂ) * cdot x S).re|
      ≤ |μt| * Real.sqrt c * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y := by
    refine (abs_re_I_mul_le μt _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_cdot_le_amp x S).trans
      (mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _))) (abs_nonneg μt)
  have hL : dopDensity m P v ι σ y - (transportLoss m W v ι σ y - gradLoss m v ι σ y)
      = |μt| * |d| * c - (|μt| * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ * gradAmp (gradField v) ι σ y * Real.sqrt c
        + |μt| * |r| * c + |μt| * Real.sqrt c
          * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y) := by
    unfold dopDensity transportLoss gradLoss
    rw [hmu, hva, hsq]
    simp only [← hddef, ← hrdef, ← hxdef, ← hcdef]
    ring
  have hD : dopDensity m P v ι σ y = |μt| * |d| * c := rfl
  have hTG : transportLoss m W v ι σ y - gradLoss m v ι σ y
      = |μt| * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ * gradAmp (gradField v) ι σ y * Real.sqrt c
        + |μt| * |r| * c + |μt| * Real.sqrt c
          * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y := by
    linarith [hL, hD]
  rw [hTG, e, hD, hdop]
  have k1 := abs_le.mp hJ
  have k2 := abs_le.mp hRb
  have k3 := abs_le.mp hSb
  have k4 := le_abs_self (Complex.I * (μt : ℂ) * ((r : ℂ) * cdot x (rotZ x))).re
  have k5 := neg_abs_le (Complex.I * (μt : ℂ) * ((r : ℂ) * cdot x (rotZ x))).re
  rw [abs_le]
  constructor <;> nlinarith [k1, k2, k3, hJ, hRb, hSb]

theorem innerPart_continuous (P : ℝ) (W v : ℝ → Space → Space) (hW : Continuous (fun z : ℝ × Space => W z.1 z.2))
    (hv : IsSmoothPerturbation P v) :
    Continuous (fun z : ℝ × Space => innerPart P W v z.1 z.2) := by
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hG := gradField_continuous P v hv
  have hmF : Continuous (meanField W) := meanField_continuous hW
  have e : (fun z : ℝ × Space => innerPart P W v z.1 z.2) = fun z : ℝ × Space =>
      (1 / P) • timeField v z.1 z.2 + (1 / 2 : ℝ) • v z.1 z.2 + relField W v (fun _ => 0) z.1 z.2
        + waveField W v z.1 z.2 + sumSecondPartialsPart v z.1 z.2 := by
    funext z
    rw [innerPart_decomp P W v (fun _ => 0) z.1 z.2]
    simp only [zero_smul, add_zero]
  have hrv : Continuous (fun z : ℝ × Space => relativeVelocity W (fun _ => (0 : ℝ)) z.2) := by
    unfold relativeVelocity
    simp only [zero_smul, sub_zero]
    have h2 : Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) • z.2) := continuous_snd.const_smul (1 / 2 : ℝ)
    exact (hmF.comp continuous_snd).add h2
  have cR : Continuous (fun z : ℝ × Space => relField W v (fun _ => 0) z.1 z.2) := by
    unfold relField
    exact hG.clm_apply hrv
  have cW : Continuous (fun z : ℝ × Space => waveField W v z.1 z.2) := by
    have hu : Continuous (fun z : ℝ × Space => W z.1 z.2 - meanField W z.2) := hW.sub (hmF.comp continuous_snd)
    unfold waveField
    exact hG.clm_apply hu
  have cT : Continuous (fun z : ℝ × Space => (1 / P) • timeField v z.1 z.2) :=
    (timeField_continuous P v hv).const_smul (1 / P)
  have cV : Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) • v z.1 z.2) := hvc.const_smul (1 / 2 : ℝ)
  rw [e]
  exact (((cT.add cV).add cR).add cW).add (sumSecondPartialsPart_continuous P v hv)

theorem integrable_pairInner (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => pairTerm m v (innerPart P W v) ι z.1 z.2) slabVol := by
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
  have hD := integrable_dopDensity hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι
  have hT := integrable_transportLoss hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι
  have hL := integrable_pairSumSecondPartials hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι
  refine ((hD.add hT).add hL.norm).mono'
    (pairTerm_continuous m ι hK hvc (innerPart_continuous P W v hW.continuous hv)).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  have h := abs_le.mp (inner_pointwise_abs hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι z.1 z.2)
  have hg := gradLoss_nonneg m v ι z.1 z.2
  have hd := dopDensity_nonneg m P v ι z.1 z.2
  have hl1 := le_abs_self (pairTerm m v (sumSecondPartialsPart v) ι z.1 z.2)
  have hl2 := neg_abs_le (pairTerm m v (sumSecondPartialsPart v) ι z.1 z.2)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

theorem transport_integrable (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => pairTerm m v (innerPart P W v) ι z.1 z.2) slabVol ∧
      Integrable (fun z : ℝ × Space => dopDensity m P v ι z.1 z.2) slabVol ∧
      Integrable (fun z : ℝ × Space => transportLoss m W v ι z.1 z.2) slabVol ∧
      Integrable (fun z : ℝ × Space => pairTerm m v (sumSecondPartialsPart v) ι z.1 z.2) slabVol ∧
      Integrable (fun z : ℝ × Space => gradLoss m v ι z.1 z.2) slabVol := by
  exact ⟨integrable_pairInner hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι,
    integrable_dopDensity hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι,
    integrable_transportLoss hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι,
    integrable_pairSumSecondPartials hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι,
    integrable_gradLoss hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι⟩

theorem slab_integral_eq {f : ℝ → Space → ℝ} (hf : Integrable (fun z : ℝ × Space => f z.1 z.2) slabVol) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, f σ y = ∫ z, f z.1 z.2 ∂slabVol :=
  (integral_prod (fun z : ℝ × Space => f z.1 z.2) hf).symm

theorem slab_lintegral_eq {f : ℝ → Space → ℝ} (hf : Integrable (fun z : ℝ × Space => f z.1 z.2) slabVol)
    (h0 : ∀ σ y, 0 ≤ f σ y) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y) = ENNReal.ofReal (∫ z, f z.1 z.2 ∂slabVol) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall fun z => h0 z.1 z.2)]
  exact (lintegral_prod (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) hf.aemeasurable.ennreal_ofReal).symm

theorem transport_bound_of (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    dopMode m P v ι + ENNReal.ofReal (-pairMode m v (innerPart P W v) ι)
      ≤ ENNReal.ofReal (pairMode m v (innerPart P W v) ι)
        + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (transportLoss m W v ι σ y) := by
  obtain ⟨hI, hD, hT, hL, hG⟩ :=
    transport_integrable hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι
  have hpt := transport_pointwise hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι
  have hssp := sumSecondPartials_slice hPars hDer hRotM hSP hSsp m P b w W hm hb hW hWp hWdiv hWdecay v hv ι
  have hX : pairMode m v (innerPart P W v) ι = ∫ z, pairTerm m v (innerPart P W v) ι z.1 z.2 ∂slabVol :=
    slab_integral_eq hI
  have hDm : dopMode m P v ι = ENNReal.ofReal (∫ z, dopDensity m P v ι z.1 z.2 ∂slabVol) :=
    slab_lintegral_eq hD (dopDensity_nonneg m P v ι)
  have hTm : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (transportLoss m W v ι σ y)
      = ENNReal.ofReal (∫ z, transportLoss m W v ι z.1 z.2 ∂slabVol) :=
    slab_lintegral_eq hT (transportLoss_nonneg m W v ι)
  have hTG : Integrable (fun z : ℝ × Space => transportLoss m W v ι z.1 z.2 - gradLoss m v ι z.1 z.2) slabVol :=
    hT.sub hG
  have hDTG : Integrable (fun z : ℝ × Space => dopDensity m P v ι z.1 z.2
      - (transportLoss m W v ι z.1 z.2 - gradLoss m v ι z.1 z.2)) slabVol := hD.sub hTG
  have hS : Integrable (fun z : ℝ × Space => dopDensity m P v ι z.1 z.2
      - (transportLoss m W v ι z.1 z.2 - gradLoss m v ι z.1 z.2) + pairTerm m v (sumSecondPartialsPart v) ι z.1 z.2) slabVol :=
    hDTG.add hL
  have h1 : ∫ z, (dopDensity m P v ι z.1 z.2 - (transportLoss m W v ι z.1 z.2 - gradLoss m v ι z.1 z.2)
        + pairTerm m v (sumSecondPartialsPart v) ι z.1 z.2) ∂slabVol
      ≤ ∫ z, pairTerm m v (innerPart P W v) ι z.1 z.2 ∂slabVol :=
    integral_mono hS hI fun z => hpt z.1 z.2
  rw [integral_add hDTG hL, integral_sub hD hTG, integral_sub hT hG] at h1
  have h2 : -(∫ z, gradLoss m v ι z.1 z.2 ∂slabVol) ≤ ∫ z, pairTerm m v (sumSecondPartialsPart v) ι z.1 z.2 ∂slabVol := by
    rw [← slab_integral_eq hG, ← slab_integral_eq hL, ← integral_neg]
    exact integral_mono_ae hG.integral_prod_left.neg hL.integral_prod_left hssp
  rw [hDm, hTm]
  refine ennreal_bound (integral_nonneg fun z => dopDensity_nonneg m P v ι z.1 z.2)
    (integral_nonneg fun z => transportLoss_nonneg m W v ι z.1 z.2) ?_
  rw [hX]
  linarith

end Internal.MuTransport

end Coercive

end Breakdown
