import Breakdown.CertCell.TopStatements
import Breakdown.CertCell.FormNegativeInverseSquare
import Breakdown.CertCell.FormNegativeSquareSum
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.CertCell.StretchMeanIntegral
import Breakdown.CertCell.TailAngularPlane
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveFieldModes

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal.FormNegative

theorem measurable_majorant {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    ∃ F : α → ℝ≥0∞, Measurable F ∧ (∀ x, f x ≤ F x) ∧ ∫⁻ x, F x ∂μ = ∫⁻ x, f x ∂μ := by
  set T := toMeasurable μ {x | f x ≠ hf.mk f x} with hTdef
  have hT : μ T = 0 := by
    rw [hTdef, measure_toMeasurable]
    exact ae_iff.1 hf.ae_eq_mk
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  refine ⟨fun x => hf.mk f x + T.indicator (fun _ => ⊤) x,
    hf.measurable_mk.add (measurable_const.indicator hTm), fun x => ?_, ?_⟩
  · by_cases hx : x ∈ T
    · simp [indicator_of_mem hx]
    · have e : f x = hf.mk f x := by
        by_contra h
        exact hx (subset_toMeasurable _ _ h)
      rw [e]
      exact le_self_add
  · rw [lintegral_add_left hf.measurable_mk, lintegral_indicator hTm, setLIntegral_measure_zero _ _ hT, add_zero]
    exact (lintegral_congr_ae hf.ae_eq_mk).symm

theorem axialRot_add_two_pi (φ : ℝ) (y : Space) : axialRot (φ + 2 * Real.pi) y = axialRot φ y := by
  unfold axialRot
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem measurable_orbitMap :
    Measurable (fun w : ((ℝ × ℝ) × ℝ) × ℝ => (w.1.2, axialRot w.2 (planePoint w.1.1))) := by
  have hc : Continuous (fun w : ((ℝ × ℝ) × ℝ) × ℝ => axialRot w.2 (planePoint w.1.1)) := by
    simp only [TailBand.Internal.AngularPlane.planePoint_eq]
    unfold axialRot
    fun_prop
  have h1 : Measurable (fun w : ((ℝ × ℝ) × ℝ) × ℝ => w.1.2) := by fun_prop
  exact h1.prodMk hc.measurable

theorem stretchNeg_lt_top {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) :
    ∫⁻ p in halfPlane, D.stretchNegMean v G p * ENNReal.ofReal p.1 < ⊤ := by
  set μ : Measure (ℝ × Space) := (volume.restrict (Icc (0 : ℝ) 1)).prod volume with hμ
  set S : ℝ × Space → ℝ := fun z => CoerciveWeak.stretchFormWith D.given D.givenHess v G z.1 z.2 with hS
  have hi : Integrable S μ := Bridge.Internal.StretchMeanParts.stretch_integrable hW hv
  obtain ⟨F, hFm, hle, hFi⟩ := measurable_majorant (μ := μ) (f := fun z => ‖S z‖ₑ) hi.1.enorm
  have hFt : ∫⁻ z, F z ∂μ < ⊤ := by
    rw [hFi]
    exact hi.2
  set K : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun w =>
    ENNReal.ofReal w.1.1 * ∫⁻ φ in Ioo (-Real.pi) Real.pi, F (w.2, axialRot φ (planePoint w.1)) with hK
  have hKm : Measurable K :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).mul
      ((hFm.comp measurable_orbitMap).lintegral_prod_right')
  have hper : ∀ (τ : ℝ) (p : ℝ × ℝ),
      Function.Periodic (fun φ => F (τ, axialRot φ (planePoint p))) (2 * Real.pi) := by
    intro τ p φ
    simp only
    rw [axialRot_add_two_pi]
  have hpt : ∀ p : ℝ × ℝ, D.stretchNegMean v G p * ENNReal.ofReal p.1
      ≤ ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1, K (p, τ) := by
    intro p
    have h1 : ∀ τ, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal (-CoerciveWeak.stretchFormWith D.given D.givenHess v G τ (axialRot φ (planePoint p)))
        ≤ ∫⁻ φ in Ioo (-Real.pi) Real.pi, F (τ, axialRot φ (planePoint p)) := by
      intro τ
      rw [Bridge.Internal.StretchMeanParts.lintegral_angle_shift _ (hper τ p),
        ← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))]
      refine lintegral_mono fun φ => ?_
      refine le_trans ?_ (hle (τ, axialRot φ (planePoint p)))
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
    unfold CellLayerData.stretchNegMean
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [mul_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun τ => mul_le_mul_of_nonneg_left (h1 τ) zero_le
  have hsub : halfPlane ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨hp.1, trivial⟩
  have hcyl : ∀ τ, ∫⁻ p in halfPlane, K (p, τ) ≤ ∫⁻ y, F (τ, y) := by
    intro τ
    rw [TailBand.lintegral_eq_cylindrical (fun y => F (τ, y)) (hFm.comp measurable_prodMk_left)]
    exact lintegral_mono_set hsub
  calc ∫⁻ p in halfPlane, D.stretchNegMean v G p * ENNReal.ofReal p.1
      ≤ ∫⁻ p in halfPlane, ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1, K (p, τ) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ p in halfPlane, K (p, τ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_lintegral_swap hKm.aemeasurable]
    _ ≤ ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, F (τ, y) :=
mul_le_mul_of_nonneg_left (lintegral_mono hcyl) zero_le
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ z, F z ∂μ := by
        rw [hμ, lintegral_prod _ hFm.aemeasurable]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFt


theorem continuous_cnormSq_local {β : Type*} [Fintype β] : Continuous (fun x : β → ℂ => cnormSq x) := by
  unfold cnormSq
  fun_prop

theorem cnormSq_nonneg_local {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x := by
  unfold cnormSq
  positivity

theorem cnormSq_curlGradSecond_le (h : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    cnormSq (curlGradOfSecondDeriv h) ≤ 2 * cnormSq h := by
  have e1 : cnormSq (curlGradOfSecondDeriv h)
      = ∑ l : Fin 3, cnormSq (curlOfGrad (fun ab : Fin 3 × Fin 3 => h (ab.1, l, ab.2))) := by
    unfold cnormSq curlGradOfSecondDeriv curlOfGrad
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have e2 : cnormSq h = ∑ l : Fin 3, cnormSq (fun ab : Fin 3 × Fin 3 => h (ab.1, l, ab.2)) := by
    unfold cnormSq
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  rw [e1, e2, Finset.mul_sum]
  exact Finset.sum_le_sum fun l _ => Coercive.Internal.FieldModes.cnormSq_curlOfGrad_le _

theorem neg_value_le (a : ModeCoefficients) (B s : ℝ) (hs : 0 < s) (h1 : -B ≤ a.hess)
    (h2 : -B ≤ a.curlHess) (h3 : -B ≤ a.curl) (h4 : -B ≤ a.strain) (h5 : -B ≤ s * a.velocity)
    (x2 xc x1 xo x0 : ℝ) :
    -a.value x2 xc x1 xo x0 ≤ |B| * (x2 ^ 2 + xc ^ 2 + xo ^ 2 + x1 ^ 2 + x0 ^ 2 / s) := by
  unfold ModeCoefficients.value
  have hB := le_abs_self B
  set t := x0 ^ 2 / s with ht
  have t0 : 0 ≤ t := div_nonneg (sq_nonneg _) hs.le
  have hst : x0 ^ 2 = s * t := by rw [ht]; field_simp
  rw [hst]
  have k1 : -|B| ≤ a.hess := le_trans (by linarith) h1
  have k2 : -|B| ≤ a.curlHess := le_trans (by linarith) h2
  have k3 : -|B| ≤ a.curl := le_trans (by linarith) h3
  have k4 : -|B| ≤ a.strain := le_trans (by linarith) h4
  have k5 : -|B| ≤ s * a.velocity := le_trans (by linarith) h5
  nlinarith [mul_le_mul_of_nonneg_right k1 (sq_nonneg x2), mul_le_mul_of_nonneg_right k2 (sq_nonneg xc),
    mul_le_mul_of_nonneg_right k3 (sq_nonneg xo), mul_le_mul_of_nonneg_right k4 (sq_nonneg x1),
    mul_le_mul_of_nonneg_right k5 t0]

theorem modes_lt_top {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (q : Fin k → ℝ) (B : ℝ)
    (hb : ∀ ι : ℤ × ℤ, ∀ p ∈ halfPlane,
      -B ≤ (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn D.azimuthOrder ι p).hess ∧
      -B ≤ (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn D.azimuthOrder ι p).curlHess ∧
      -B ≤ (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn D.azimuthOrder ι p).curl ∧
      -B ≤ (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn D.azimuthOrder ι p).strain ∧
      -B ≤ (p.1 ^ 2 + p.2 ^ 2) * (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q)
        (D.bounds q) D.cert.weightFn D.azimuthOrder ι p).velocity)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g)
    (hVs : ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal
      (cnormSq (modeVel (labelHarmonic D.azimuthOrder ι) v 0 (planePoint p)) / (p.1 ^ 2 + p.2 ^ 2) * p.1) < ⊤)
    (hGs : ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal
      (cnormSq (modeGrad (labelHarmonic D.azimuthOrder ι) G 0 (planePoint p)) * p.1) < ⊤)
    (hHs : ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal
      (cnormSq (modeSecondDeriv (labelHarmonic D.azimuthOrder ι) H 0 (planePoint p)) * p.1) < ⊤) :
    ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1)) < ⊤ := by
  set m := D.azimuthOrder with hm
  set aH : ℤ × ℤ → ℝ × ℝ → ℝ≥0∞ := fun ι p =>
    ENNReal.ofReal (cnormSq (modeSecondDeriv (labelHarmonic m ι) H 0 (planePoint p)) * p.1) with haH
  set aG : ℤ × ℤ → ℝ × ℝ → ℝ≥0∞ := fun ι p =>
    ENNReal.ofReal (cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) * p.1) with haG
  set aV : ℤ × ℤ → ℝ × ℝ → ℝ≥0∞ := fun ι p =>
    ENNReal.ofReal (cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) / (p.1 ^ 2 + p.2 ^ 2) * p.1)
    with haV
  have hmH : ∀ ι, AEMeasurable (aH ι) (volume.restrict halfPlane) := fun ι =>
    ((continuous_cnormSq_local.comp_aestronglyMeasurable
      (TailBand.aestronglyMeasurable_labelFields hv m ι).2.2).aemeasurable.mul
      measurable_fst.aemeasurable).ennreal_ofReal
  have hmG : ∀ ι, AEMeasurable (aG ι) (volume.restrict halfPlane) := fun ι =>
    ((continuous_cnormSq_local.comp_aestronglyMeasurable
      (TailBand.aestronglyMeasurable_labelFields hv m ι).2.1).aemeasurable.mul
      measurable_fst.aemeasurable).ennreal_ofReal
  have hpt : ∀ ι, ∀ p ∈ halfPlane, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1))
      ≤ ENNReal.ofReal |B| * (3 * aH ι p + 3 * aG ι p + aV ι p) := by
    intro ι p hp
    have hr : 0 < p.1 := hp.1
    have hs : 0 < p.1 ^ 2 + p.2 ^ 2 := by positivity
    obtain ⟨h1, h2, h3, h4, h5⟩ := hb ι p hp
    set cH := cnormSq (modeSecondDeriv (labelHarmonic m ι) H 0 (planePoint p)) with hcH
    set cG := cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) with hcG
    set cV := cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) with hcV
    set cCH := cnormSq (curlGradOfSecondDeriv (modeSecondDeriv (labelHarmonic m ι) H 0 (planePoint p))) with hcCH
    set cCG := cnormSq (curlOfGrad (modeGrad (labelHarmonic m ι) G 0 (planePoint p))) with hcCG
    have eD : D.labelDensity q v G H ι p = (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q)
        D.cert.weightFn m ι p).value (Real.sqrt cH) (Real.sqrt cCH) (Real.sqrt cG) (Real.sqrt cCG)
          (Real.sqrt cV) := by
      unfold CellLayerData.labelDensity PieceWeights.modeTerm
      exact ModeCoefficients.modeDensity_eq_value _ _ _ _ _ _ _ _ _ _ _ _
    have hN := neg_value_le _ B _ hs h1 h2 h3 h4 h5 (Real.sqrt cH) (Real.sqrt cCH) (Real.sqrt cG)
      (Real.sqrt cCG) (Real.sqrt cV)
    rw [← eD, Real.sq_sqrt (cnormSq_nonneg_local _), Real.sq_sqrt (cnormSq_nonneg_local _),
      Real.sq_sqrt (cnormSq_nonneg_local _), Real.sq_sqrt (cnormSq_nonneg_local _),
      Real.sq_sqrt (cnormSq_nonneg_local _)] at hN
    have q1 : cCH ≤ 2 * cH := cnormSq_curlGradSecond_le _
    have q2 : cCG ≤ 2 * cG := Coercive.Internal.FieldModes.cnormSq_curlOfGrad_le _
    have hB0 := abs_nonneg B
    have hreal : -(D.labelDensity q v G H ι p * p.1)
        ≤ |B| * (3 * (cH * p.1) + 3 * (cG * p.1) + cV / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
      have hx : -(D.labelDensity q v G H ι p) ≤ |B| * (3 * cH + 3 * cG + cV / (p.1 ^ 2 + p.2 ^ 2)) := by
        refine hN.trans (mul_le_mul_of_nonneg_left ?_ hB0)
        linarith
      have := mul_le_mul_of_nonneg_right hx hr.le
      nlinarith [this]
    have n1 : 0 ≤ cH * p.1 := mul_nonneg (cnormSq_nonneg_local _) hr.le
    have n2 : 0 ≤ cG * p.1 := mul_nonneg (cnormSq_nonneg_local _) hr.le
    have n3 : 0 ≤ cV / (p.1 ^ 2 + p.2 ^ 2) * p.1 :=
      mul_nonneg (div_nonneg (cnormSq_nonneg_local _) hs.le) hr.le
    refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hB0, ENNReal.ofReal_add (by positivity) n3, ENNReal.ofReal_add (by positivity)
      (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
  have hint : ∀ ι, ∫⁻ p in halfPlane, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1))
      ≤ ENNReal.ofReal |B| * (3 * (∫⁻ p in halfPlane, aH ι p) + 3 * (∫⁻ p in halfPlane, aG ι p)
        + (∫⁻ p in halfPlane, aV ι p)) := by
    intro ι
    refine (lintegral_mono_ae ((ae_restrict_mem Bridge.Internal.StretchMeanParts.measurableSet_halfPlane).mono
      fun p hp => hpt ι p hp)).trans (le_of_eq ?_)
    have m1 : AEMeasurable (fun p => 3 * aH ι p + 3 * aG ι p) (volume.restrict halfPlane) :=
      ((hmH ι).const_mul 3).add ((hmG ι).const_mul 3)
    have m2 : AEMeasurable (fun p => 3 * aH ι p) (volume.restrict halfPlane) := (hmH ι).const_mul 3
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' m1, lintegral_add_left' m2,
      lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
  refine (ENNReal.tsum_le_tsum hint).trans_lt ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2
    ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hHs, ENNReal.mul_lt_top (by simp) hGs⟩, hVs⟩)

theorem axialRot_smul_apply (φ c : ℝ) (w : Space) (i : Fin 3) :
    axialRot φ (c • w) i = c * axialRot φ w i := by
  simp only [axialRot, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem modeAverage_const_mul {β : Type*} (ι : ℤ × ℤ) (c : ℝ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage ι (fun τ φ b => c * f τ φ b) b = (c : ℂ) * modeAverage ι f b := by
  unfold modeAverage
  simp only [Complex.ofReal_mul, mul_left_comm _ (c : ℂ), intervalIntegral.integral_const_mul]

theorem modeVel_inv_norm_smul (ι : ℤ × ℤ) (v : ℝ → Space → Space) (y : Space) :
    modeVel ι (fun σ x => ‖x‖⁻¹ • v σ x) 0 y = fun i => ((‖y‖⁻¹ : ℝ) : ℂ) * modeVel ι v 0 y i := by
  funext i
  unfold modeVel
  simp only [Coercive.RotationInternal.axialRot_norm, axialRot_smul_apply]
  exact modeAverage_const_mul ι _ (fun τ φ j => axialRot (-φ) (v (0 + τ) (axialRot φ y)) j) i

theorem cnormSq_const_mul {β : Type*} [Fintype β] (c : ℝ) (x : β → ℂ) :
    cnormSq (fun i => (c : ℂ) * x i) = c ^ 2 * cnormSq x := by
  unfold cnormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem norm_planePoint_sq (p : ℝ × ℝ) : ‖planePoint p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [TailBand.Internal.AngularPlane.planePoint_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three, unitVector]

theorem velocity_inverse_sum_lt_top (m : ℕ) (hm : 1 ≤ m) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal
      (cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) / (p.1 ^ 2 + p.2 ^ 2) * p.1) < ⊤ := by
  have hX : AEStronglyMeasurable (fun z : ℝ × Space => ‖z.2‖⁻¹ • v z.1 z.2) volume :=
    (measurable_snd.norm.inv).aestronglyMeasurable.smul hv.measurable_velocity
  have hXp : IsTimePeriodic (fun σ x => ‖x‖⁻¹ • v σ x) := fun σ y => by
    simp only [hv.periodic_velocity σ y]
  have h := labelAmplitude_sum_le m hm (fun σ x => ‖x‖⁻¹ • v σ x) hX hXp
  have e : ∀ ι : ℤ × ℤ, ∀ p : ℝ × ℝ,
      cnormSq (modeVel (labelHarmonic m ι) (fun σ x => ‖x‖⁻¹ • v σ x) 0 (planePoint p))
        = cnormSq (modeVel (labelHarmonic m ι) v 0 (planePoint p)) / (p.1 ^ 2 + p.2 ^ 2) := by
    intro ι p
    rw [modeVel_inv_norm_smul, cnormSq_const_mul, inv_pow, ← div_eq_inv_mul, norm_planePoint_sq]
  simp only [e] at h
  have hL : periodLIntegral (fun σ y => ‖‖y‖⁻¹ • v σ y‖ ^ 2)
      = periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / ‖y‖ ^ 2) := by
    unfold periodLIntegral
    congr 1
    funext σ
    congr 1
    funext y
    dsimp only
    rw [norm_smul, norm_inv, norm_norm, mul_pow, inv_pow, div_eq_inv_mul]
  rw [hL] at h
  refine h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact (perturbation_inverseSquare Γ P v G H g hv).trans_lt
    (ENNReal.mul_lt_top (by simp) hv.gradient_finite)

theorem gradient_sum_lt_top (m : ℕ) (hm : 1 ≤ m) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal
      (cnormSq (modeGrad (labelHarmonic m ι) G 0 (planePoint p)) * p.1) < ⊤ :=
  (labelGradAmplitude_sum_le m hm G hv.measurable_gradient hv.periodic_gradient).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.gradient_finite)

theorem secondDeriv_sum_lt_top (m : ℕ) (hm : 1 ≤ m) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, ENNReal.ofReal
      (cnormSq (modeSecondDeriv (labelHarmonic m ι) H 0 (planePoint p)) * p.1) < ⊤ :=
  (labelSecondDerivAmplitude_sum_le m hm H hv.measurable_secondDeriv hv.periodic_secondDeriv).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((Coercive.perturbationSecondDerivBoundHolds_proof Γ P v G H g hv).trans_lt hv.sumSecondPartials_finite))

end Internal.FormNegative

theorem formNegFinite : FormNegFiniteHolds := by
  intro k C nE nM D cForm B hm hCoef hW q hq v G H g hv
  obtain ⟨Bc, hBc⟩ := hCoef
  unfold CellLayerData.formNeg
  refine ENNReal.add_lt_top.2 ⟨?_, Internal.FormNegative.stretchNeg_lt_top _ hW hv⟩
  exact Internal.FormNegative.modes_lt_top (D.withFormCoercivity cForm) q Bc (fun ι p hp => hBc q hq ι p hp) hv
    (Internal.FormNegative.velocity_inverse_sum_lt_top _ hm hv)
    (Internal.FormNegative.gradient_sum_lt_top _ hm hv)
    (Internal.FormNegative.secondDeriv_sum_lt_top _ hm hv)


end CertCell

end Breakdown
