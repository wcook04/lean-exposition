import Breakdown.CertCell.TailRayBound
import Breakdown.CertCell.TailFlipDecay
import Breakdown.Cert.ExtendedCoerciveMain
import Breakdown.Cert.CoerciveFrequencySeminormAngular
import Breakdown.FracCell.RelTrace
import Breakdown.CertCell.TailAngularPlane

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

namespace RayModesInternal

open Coercive Coercive.GainInternal

private theorem reMat_apply (g : Fin 3 × Fin 3 → ℂ) (x : Space) (i : Fin 3) :
    reMat g x i = ∑ j : Fin 3, (g (i, j)).re * x j := by
  fin_cases i <;> simp [reMat, unitVector, EuclideanSpace.inner_single_left, Fin.sum_univ_three] <;> ring

private theorem imMat_apply (g : Fin 3 × Fin 3 → ℂ) (x : Space) (i : Fin 3) :
    imMat g x i = ∑ j : Fin 3, (g (i, j)).im * x j := by
  fin_cases i <;> simp [imMat, unitVector, EuclideanSpace.inner_single_left, Fin.sum_univ_three] <;> ring

private theorem reVec_apply (x : Fin 3 → ℂ) (i : Fin 3) : reVec x i = (x i).re := by
  simp [reVec, unitVector, Fin.sum_univ_three]
  fin_cases i <;> simp

private theorem imVec_apply (x : Fin 3 → ℂ) (i : Fin 3) : imVec x i = (x i).im := by
  simp [imVec, unitVector, Fin.sum_univ_three]
  fin_cases i <;> simp

private theorem norm_sq_three (x : Space) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

private theorem cnormSq_three (x : Fin 3 → ℂ) :
    cnormSq x = (x 0).re ^ 2 + (x 0).im ^ 2 + (x 1).re ^ 2 + (x 1).im ^ 2 + (x 2).re ^ 2 + (x 2).im ^ 2 := by
  simp only [cnormSq, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem cnormSq_re_im (x : Fin 3 → ℂ) : cnormSq x = ‖reVec x‖ ^ 2 + ‖imVec x‖ ^ 2 := by
  rw [cnormSq_three, norm_sq_three, norm_sq_three]
  simp only [reVec_apply, imVec_apply]
  ring

private theorem row_bound (a0 a1 a2 y0 y1 y2 : ℝ) (hr : 0 < y0 ^ 2 + y1 ^ 2) :
    (a0 * y0 + a1 * y1 + a2 * y2) ^ 2 / (y0 ^ 2 + y1 ^ 2 + y2 ^ 2)
      + (a1 * y0 - a0 * y1) ^ 2 / (y0 ^ 2 + y1 ^ 2) ≤ a0 ^ 2 + a1 ^ 2 + a2 ^ 2 := by
  have hs : 0 < y0 ^ 2 + y1 ^ 2 + y2 ^ 2 := by positivity
  rw [div_add_div _ _ hs.ne' hr.ne', div_le_iff₀ (mul_pos hs hr)]
  nlinarith [sq_nonneg (a2 * (y0 ^ 2 + y1 ^ 2) - (a0 * y0 + a1 * y1) * y2)]

private theorem contract_apply (M : Fin 3 × Fin 3 → ℂ) (y : Space) (b : Fin 3) :
    ∑ j, M (b, j) * (azimuthalField y j : ℂ)
      = ((M (b, 1)).re * y 0 - (M (b, 0)).re * y 1 : ℝ) + ((M (b, 1)).im * y 0 - (M (b, 0)).im * y 1 : ℝ) * Complex.I := by
  apply Complex.ext <;> simp [Fin.sum_univ_three, azimuthalField] <;> ring

private theorem grad_row (M : Fin 3 × Fin 3 → ℂ) (y : Space) (hr : 0 < y 0 ^ 2 + y 1 ^ 2) (b : Fin 3) :
    radialApply (reMat M) y b ^ 2 + radialApply (imMat M) y b ^ 2
      + ‖∑ j, M (b, j) * (azimuthalField y j : ℂ)‖ ^ 2 / (y 0 ^ 2 + y 1 ^ 2)
      ≤ ‖M (b, 0)‖ ^ 2 + ‖M (b, 1)‖ ^ 2 + ‖M (b, 2)‖ ^ 2 := by
  have hy : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := norm_sq_three y
  have hslope : ∀ (A : Space →L[ℝ] Space) (i : Fin 3), radialApply A y i = ‖y‖⁻¹ * A y i := by
    intro A i
    simp [radialApply, map_smul]
  have hrow : ∀ a0 a1 a2 : ℝ, (‖y‖⁻¹ * (a0 * y 0 + a1 * y 1 + a2 * y 2)) ^ 2
      + (a1 * y 0 - a0 * y 1) ^ 2 / (y 0 ^ 2 + y 1 ^ 2) ≤ a0 ^ 2 + a1 ^ 2 + a2 ^ 2 := by
    intro a0 a1 a2
    rw [mul_pow, inv_pow, hy, ← div_eq_inv_mul]
    exact row_bound a0 a1 a2 (y 0) (y 1) (y 2) hr
  have e := hrow (M (b, 0)).re (M (b, 1)).re (M (b, 2)).re
  have f := hrow (M (b, 0)).im (M (b, 1)).im (M (b, 2)).im
  rw [hslope, hslope, reMat_apply, imMat_apply, contract_apply, Complex.sq_norm, Complex.normSq_add_mul_I]
  simp only [Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  rw [add_div]
  nlinarith [e, f]

private theorem grad_split (M : Fin 3 × Fin 3 → ℂ) (y : Space) (hr : 0 < y 0 ^ 2 + y 1 ^ 2) :
    ‖radialApply (reMat M) y‖ ^ 2 + ‖radialApply (imMat M) y‖ ^ 2
      + cnormSq (fun b => ∑ j, M (b, j) * (azimuthalField y j : ℂ)) / (y 0 ^ 2 + y 1 ^ 2) ≤ cnormSq M := by
  have h0 := grad_row M y hr 0
  have h1 := grad_row M y hr 1
  have h2 := grad_row M y hr 2
  rw [norm_sq_three, norm_sq_three]
  simp only [cnormSq, Fintype.sum_prod_type, Fin.sum_univ_three, add_div]
  simp only [Fin.sum_univ_three] at h0 h1 h2
  linarith

private theorem gain_sq (w u : Fin 3 → ℂ) (k : ℝ)
    (hid : ∀ b, u b = (k : ℂ) * Complex.I * w b + ∑ c, ((azimuthalField (unitVector c) b : ℝ) : ℂ) * w c) :
    max (|k| - 1) 0 ^ 2 * cnormSq w ≤ cnormSq u := by
  have hu0 : 0 ≤ cnormSq u := Finset.sum_nonneg fun _ _ => by positivity
  rcases le_total (|k| - 1) 0 with h | h
  · rw [max_eq_right h]
    simpa using hu0
  rw [max_eq_left h]
  set Bw : Fin 3 → ℂ := fun b => ∑ c, ((azimuthalField (unitVector c) b : ℝ) : ℂ) * w c with hBw
  have hnorm : ∀ x : Fin 3 → ℂ, cnormSq x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 3))‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hB : ‖(WithLp.toLp 2 Bw : EuclideanSpace ℂ (Fin 3))‖ ≤ ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ := by
    have h1 := vel_bound w
    rw [one_pow, one_mul, hnorm, hnorm] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  have hu : (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin 3))
      = ((k : ℂ) * Complex.I) • (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3)) + WithLp.toLp 2 Bw := by
    rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
    congr 1
    funext b
    simp [hid b, hBw]
  have h1 := norm_sub_norm_le (((k : ℂ) * Complex.I) • (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3)))
    (-(WithLp.toLp 2 Bw : EuclideanSpace ℂ (Fin 3)))
  rw [sub_neg_eq_add, norm_neg, norm_smul, ← hu] at h1
  have hk : ‖(k : ℂ) * Complex.I‖ = |k| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hk] at h1
  rw [hnorm w, hnorm u, ← mul_pow]
  have hw0 := norm_nonneg (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))
  exact pow_le_pow_left₀ (mul_nonneg h hw0) (by nlinarith) 2

private theorem cnormSq_const_mul {β : Type*} [Fintype β] (c : ℂ) (x : β → ℂ) :
    cnormSq (fun i => c * x i) = ‖c‖ ^ 2 * cnormSq x := by
  simp only [cnormSq, norm_mul, mul_pow, Finset.mul_sum]

private theorem cnormSq_rotC (ψ : ℝ) (x : Fin 3 → ℂ) : cnormSq (rotC ψ x) = cnormSq x := by
  rw [cnormSq_three, cnormSq_three]
  simp [rotC, axialRot, unitVector, Fin.sum_univ_three, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  linear_combination ((x 0).re ^ 2 + (x 1).re ^ 2 + (x 0).im ^ 2 + (x 1).im ^ 2) * Real.sin_sq_add_cos_sq ψ

private theorem rot_transpose (ψ : ℝ) (j c : Fin 3) :
    axialRot (-ψ) (unitVector j) c = axialRot ψ (unitVector c) j := by
  fin_cases j <;> fin_cases c <;> simp [axialRot, unitVector, Real.cos_neg, Real.sin_neg]

private theorem cnormSq_rotCMat (ψ : ℝ) (g : Fin 3 × Fin 3 → ℂ) : cnormSq (rotCMat ψ g) = cnormSq g := by
  set h : Fin 3 → Fin 3 → ℂ := fun a j => rotC ψ (fun c => g (a, c)) j with hh
  have hcol : ∀ i j, rotCMat ψ g (i, j) = rotC ψ (fun a => h a j) i := by
    intro i j
    simp only [rotCMat, rotC, hh, Finset.mul_sum, rot_transpose]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  calc cnormSq (rotCMat ψ g) = ∑ j, cnormSq (rotC ψ (fun a => h a j)) := by
        simp only [cnormSq, Fintype.sum_prod_type, hcol]
        exact Finset.sum_comm
    _ = ∑ j, cnormSq (fun a => h a j) := Finset.sum_congr rfl fun j _ => cnormSq_rotC ψ _
    _ = ∑ a, cnormSq (rotC ψ (fun c => g (a, c))) := by
        simp only [cnormSq, hh]
        exact Finset.sum_comm
    _ = cnormSq g := by
        simp only [cnormSq_rotC]
        simp only [cnormSq, Fintype.sum_prod_type]

private theorem modeAverage_shift {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ)
    (hf : ∀ t φ b, f (t + 1) φ b = f t φ b) (σ : ℝ) (b : β) :
    modeAverage ι (fun τ φ b => f (σ + τ) φ b) b
      = Complex.exp (((2 * Real.pi * ι.1 * σ : ℝ) : ℂ) * Complex.I) * modeAverage ι f b := by
  set K : ℝ → ℂ := fun t => ∫ φ in (0 : ℝ)..(2 * Real.pi),
    Complex.exp (-(((ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f t φ b : ℝ) : ℂ) with hK
  set E : ℝ → ℂ := fun t => Complex.exp (-(((2 * Real.pi * ι.1 * t : ℝ) : ℂ) * Complex.I)) * K t with hEdef
  have hin : ∀ t s : ℝ, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * t + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f s φ b : ℝ) : ℂ)
        = Complex.exp (-(((2 * Real.pi * ι.1 * t : ℝ) : ℂ) * Complex.I)) * K s := by
    intro t s
    rw [hK, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hone : Complex.exp (-(((2 * Real.pi * ι.1 : ℝ) : ℂ) * Complex.I)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-ι.1)
    rw [← this]
    congr 1
    push_cast
    ring
  have hKp : ∀ t, K (t + 1) = K t := by
    intro t
    refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [hf]
  have hE : Function.Periodic E 1 := by
    intro t
    simp only [hEdef, hKp]
    congr 1
    rw [← mul_one (Complex.exp (-(((2 * Real.pi * ι.1 * t : ℝ) : ℂ) * Complex.I))), ← hone,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpt : ∀ τ : ℝ, Complex.exp (-(((2 * Real.pi * ι.1 * τ : ℝ) : ℂ) * Complex.I)) * K (σ + τ)
      = Complex.exp (((2 * Real.pi * ι.1 * σ : ℝ) : ℂ) * Complex.I) * E (σ + τ) := by
    intro τ
    simp only [hEdef]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  unfold modeAverage
  simp only [hin, hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_left (fun t => E t) σ,
    add_zero, hE.intervalIntegral_add_eq σ 0, zero_add]
  simp only [hEdef]
  ring

private theorem cnormSq_modeVel_shift {v : ℝ → Space → Space} (hv : IsTimePeriodic v) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) : cnormSq (modeVel ι v σ y) = cnormSq (modeVel ι v 0 y) := by
  set f : ℝ → ℝ → Fin 3 → ℝ := fun t φ i => axialRot (-φ) (v t (axialRot φ y)) i with hf
  have hper : ∀ t φ i, f (t + 1) φ i = f t φ i := fun t φ i => by
    simp only [hf]
    rw [hv t]
  have h1 : modeVel ι v σ y = fun i => Complex.exp (((2 * Real.pi * ι.1 * σ : ℝ) : ℂ) * Complex.I) *
      modeAverage ι f i := funext fun i => modeAverage_shift ι f hper σ i
  have h0 : modeVel ι v 0 y = fun i => Complex.exp (((2 * Real.pi * ι.1 * 0 : ℝ) : ℂ) * Complex.I) *
      modeAverage ι f i := funext fun i => modeAverage_shift ι f hper 0 i
  rw [h1, h0, cnormSq_const_mul, cnormSq_const_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_exp_ofReal_mul_I]

private theorem cnormSq_modeGrad_shift {G : ℝ → Space → (Space →L[ℝ] Space)} (hG : IsTimePeriodic G)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : cnormSq (modeGrad ι G σ y) = cnormSq (modeGrad ι G 0 y) := by
  set f : ℝ → ℝ → Fin 3 × Fin 3 → ℝ := fun t φ ij =>
    axialRot (-φ) (G t (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1 with hf
  have hper : ∀ t φ ij, f (t + 1) φ ij = f t φ ij := fun t φ ij => by
    simp only [hf]
    rw [hG t]
  have h1 : modeGrad ι G σ y = fun ij => Complex.exp (((2 * Real.pi * ι.1 * σ : ℝ) : ℂ) * Complex.I) *
      modeAverage ι f ij := funext fun ij => modeAverage_shift ι f hper σ ij
  have h0 : modeGrad ι G 0 y = fun ij => Complex.exp (((2 * Real.pi * ι.1 * 0 : ℝ) : ℂ) * Complex.I) *
      modeAverage ι f ij := funext fun ij => modeAverage_shift ι f hper 0 ij
  rw [h1, h0, cnormSq_const_mul, cnormSq_const_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_exp_ofReal_mul_I]

open CellCert.CellAnalysis (cylPoint) in
private theorem rot_cyl (r θ z : ℝ) : axialRot (-θ) (cylPoint r θ z) = planePoint (r, z) := by
  ext i
  fin_cases i <;> simp [axialRot, cylPoint, planePoint, unitVector, Real.cos_neg, Real.sin_neg]
  · linear_combination r * Real.sin_sq_add_cos_sq θ
  · ring

open CellCert.CellAnalysis (cylPoint) in
private theorem pointPlane_cyl {r : ℝ} (hr : 0 ≤ r) (θ z : ℝ) : pointPlane (cylPoint r θ z) = (r, z) := by
  have h : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ
  simp [pointPlane, cylPoint, h, Real.sqrt_sq hr]

open CellCert.CellAnalysis (cylPoint) in
private theorem norm_cyl (r θ z : ℝ) : ‖cylPoint r θ z‖ = planeRadius (r, z) := by
  have h : ‖cylPoint r θ z‖ ^ 2 = r ^ 2 + z ^ 2 := by
    rw [norm_sq_three]
    simp [cylPoint]
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [planeRadius, ← h, Real.sqrt_sq (norm_nonneg _)]

private theorem pointPlane_measurable : Measurable pointPlane := by
  unfold pointPlane
  fun_prop

private theorem planeRayRegion_measurable {R : ℝ × ℝ → ℝ} (hR : Measurable R) :
    MeasurableSet (planeRayRegion R) := by
  have h1 : MeasurableSet halfPlane := measurableSet_Ioi.prod measurableSet_Ioi
  have h2 : Measurable planeRadius := by
    unfold planeRadius
    fun_prop
  exact h1.inter (measurableSet_lt hR h2)

private theorem rayExterior_lift {R : ℝ × ℝ → ℝ} {R₀ R₁ : ℝ} (hR : IsDirectionRadius R R₀ R₁) :
    IsRayExterior (pointPlane ⁻¹' planeRayRegion R) := by
  refine ⟨pointPlane_measurable (planeRayRegion_measurable hR.measurable), fun e he => ?_⟩
  set q := pointPlane e with hq
  have hsc : ∀ t : ℝ, 0 < t → pointPlane (t • e) = t • q := by
    intro t ht
    have h : (t * e 0) ^ 2 + (t * e 1) ^ 2 = t ^ 2 * (e 0 ^ 2 + e 1 ^ 2) := by ring
    simp [pointPlane, hq, h, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  have hq1 : planeRadius q = 1 := by
    have h2 := norm_sq_three e
    rw [he] at h2
    simp only [planeRadius, hq, pointPlane]
    rw [Real.sq_sqrt (by positivity), ← h2, one_pow, Real.sqrt_one]
  have hrad : ∀ t : ℝ, 0 < t → planeRadius (t • q) = t := by
    intro t ht
    have h : (t * q.1) ^ 2 + (t * q.2) ^ 2 = t ^ 2 * (q.1 ^ 2 + q.2 ^ 2) := by ring
    have h1 : planeRadius (t • q) = t * planeRadius q := by
      simp only [planeRadius, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, h]
      rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
    rw [h1, hq1, mul_one]
  have hhalf : ∀ t : ℝ, 0 < t → (t • q ∈ halfPlane ↔ q ∈ halfPlane) := by
    intro t ht
    simp only [halfPlane, mem_prod, mem_Ioi, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 ht.le, pos_of_mul_pos_right h2 ht.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos ht h1, mul_pos ht h2⟩
  by_cases hin : q ∈ halfPlane
  · right
    refine ⟨R q, lt_of_lt_of_le hR.lower_pos (hR.between q).1, fun t ht => ?_⟩
    simp only [mem_preimage, planeRayRegion, mem_ofPred_eq, hsc t ht, hR.homogeneous t q ht, hrad t ht,
      (hhalf t ht).2 hin, true_and]
  · left
    intro t ht hmem
    simp only [mem_preimage, planeRayRegion, mem_ofPred_eq, hsc t ht] at hmem
    exact hin ((hhalf t ht).1 hmem.1)

open CellCert.CellFormula.Internal.RelTrace in
private theorem cyl_transfer (h : Space → ℝ≥0∞) (g : ℝ × ℝ → ℝ≥0∞)
    (hg : AEMeasurable g (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))))
    (hae : ∀ᵐ x ∂(volume.restrict region), h (cylF x) = g x.1) :
    ∫⁻ y, h y = ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 * g p := by
  rw [← lintegral_cyl]
  have hreg : (volume : Measure ((ℝ × ℝ) × ℝ)).restrict region =
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    rw [Measure.prod_restrict]
    rfl
  have hf : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * g p)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) :=
    (measurable_fst.ennreal_ofReal.aemeasurable).mul hg
  calc ∫⁻ x in region, ENNReal.ofReal x.1.1 * h (cylF x)
      = ∫⁻ x in region, (ENNReal.ofReal x.1.1 * g x.1) * (fun _ : ℝ => (1 : ℝ≥0∞)) x.2 :=
        lintegral_congr_ae (hae.mono fun x hx => by simp only [hx, mul_one])
    _ = (∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 * g p) *
          ∫⁻ _θ in Ioo (-Real.pi) Real.pi, (1 : ℝ≥0∞) := by
        rw [hreg]
        exact lintegral_prod_mul hf aemeasurable_const
    _ = _ := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo,
          one_mul, mul_comm]
        congr 2
        ring

open CellCert.CellFormula.Internal.RelTrace in
private theorem ae_region_of_ae {Q : Space → Prop} (hQ : ∀ᵐ y, Q y) :
    ∀ᵐ x ∂(volume.restrict region), Q (cylF x) := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hQ)
  rw [ae_iff]
  exact measure_mono_null (fun x hx => hsub hx) (region_null hNm hN0)

private theorem cnormSq_nonneg {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem memLp_six_of {f : Space → Space} (hf : AEStronglyMeasurable f volume) (B : Space → ℝ)
    (hB : ∀ y, ‖f y‖ ^ 2 ≤ B y) (hfin : ∫⁻ y, ENNReal.ofReal (B y ^ 3) < ⊤) : MemLp f 6 volume := by
  have hi : Integrable (fun y => ‖f y‖ ^ 6) := by
    refine ⟨hf.norm.pow 6, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by positivity)]
    refine lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_) hfin
    have h0 : 0 ≤ ‖f y‖ ^ 2 := by positivity
    calc ‖f y‖ ^ 6 = (‖f y‖ ^ 2) ^ 3 := by ring
      _ ≤ B y ^ 3 := pow_le_pow_left₀ h0 (hB y) 3
  refine (integrable_norm_rpow_iff hf (by norm_num) (by norm_num)).1 ?_
  simpa using hi

private theorem entrySq_cont : Continuous SteadyCert.entrySq := by
  unfold SteadyCert.entrySq
  fun_prop

private theorem integrable_entrySq_of {A : Space → (Space →L[ℝ] Space)} (hA : AEStronglyMeasurable A volume)
    (B : Space → ℝ) (hB : ∀ y, SteadyCert.entrySq (A y) ≤ B y) (hfin : ∫⁻ y, ENNReal.ofReal (B y) < ⊤) :
    Integrable (fun y => SteadyCert.entrySq (A y)) :=
  ⟨entrySq_cont.comp_aestronglyMeasurable hA,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
      (lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hB y)) hfin)⟩

private theorem entrySq_re_im (M : Fin 3 × Fin 3 → ℂ) :
    SteadyCert.entrySq (reMat M) + SteadyCert.entrySq (imMat M) = cnormSq M := by
  simp only [SteadyCert.entrySq, norm_sq_three, reMat_apply, imMat_apply, Fin.sum_univ_three, cnormSq,
    Fintype.sum_prod_type, Complex.sq_norm, Complex.normSq_apply]
  simp [unitVector]
  ring

private theorem entrySq_reMat_le (M : Fin 3 × Fin 3 → ℂ) : SteadyCert.entrySq (reMat M) ≤ cnormSq M := by
  rw [← entrySq_re_im]
  have : 0 ≤ SteadyCert.entrySq (imMat M) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

private theorem entrySq_imMat_le (M : Fin 3 × Fin 3 → ℂ) : SteadyCert.entrySq (imMat M) ≤ cnormSq M := by
  rw [← entrySq_re_im]
  have : 0 ≤ SteadyCert.entrySq (reMat M) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

private theorem reVec_le (x : Fin 3 → ℂ) : ‖reVec x‖ ^ 2 ≤ cnormSq x := by
  rw [cnormSq_re_im]
  nlinarith [sq_nonneg ‖imVec x‖]

private theorem imVec_le (x : Fin 3 → ℂ) : ‖imVec x‖ ^ 2 ≤ cnormSq x := by
  rw [cnormSq_re_im]
  nlinarith [sq_nonneg ‖reVec x‖]

open Coercive.Internal.ModeRotation in
private theorem slice_choice {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (ξ : ℤ × ℤ) :
    ∃ σ : ℝ, (IsWeakGradient (fun y => reVec (modeVel ξ v σ y)) (fun y => reMat (modeGrad ξ G σ y)) ∧
        IsWeakGradient (fun y => imVec (modeVel ξ v σ y)) (fun y => imMat (modeGrad ξ G σ y))) ∧
      (∀ᵐ y, ∀ b, ∑ j, modeGrad ξ G σ y (b, j) * (azimuthalField y j : ℂ) =
        ((ξ.2 : ℝ) : ℂ) * Complex.I * modeVel ξ v σ y b
          + ∑ c, ((azimuthalField (unitVector c) b : ℝ) : ℂ) * modeVel ξ v σ y c) ∧
      (∀ᵐ y, Integrable (fun p : ℝ × ℝ => v (σ + p.1) (axialRot p.2 y)) boxMeasure) ∧
      (∀ᵐ y, Integrable (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y)) boxMeasure) := by
  have hRot := axialRotationHolds_proof
  obtain ⟨hD1, -, -⟩ := CoerciveWeak.modeDerivativeHolds_closed Γ P v G H g hv ξ
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsdef
  have hs0 : ∀ n, s n ≠ 0 := fun n => ne_of_gt (by positivity)
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hR1 := Measure.ae_ae_of_ae_prod
    (ae_all_iff.2 fun n => (CoerciveWeak.modeRotationHolds_closed Γ P v G H g hv ξ (s n)).1)
  obtain ⟨hlv, hlG, -⟩ := perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hOv := Measure.ae_ae_of_ae_prod (ae_integrable_orbit hRot hlv)
  have hOG := Measure.ae_ae_of_ae_prod (ae_integrable_orbit hRot hlG)
  have hall : ∀ᵐ σ : ℝ, ((IsWeakGradient (fun y => reVec (modeVel ξ v σ y)) (fun y => reMat (modeGrad ξ G σ y)) ∧
        IsWeakGradient (fun y => imVec (modeVel ξ v σ y)) (fun y => imMat (modeGrad ξ G σ y))) ∧
      (∀ᵐ y, ∀ b, ∑ j, modeGrad ξ G σ y (b, j) * (azimuthalField y j : ℂ) =
        ((ξ.2 : ℝ) : ℂ) * Complex.I * modeVel ξ v σ y b
          + ∑ c, ((azimuthalField (unitVector c) b : ℝ) : ℂ) * modeVel ξ v σ y c) ∧
      (∀ᵐ y, Integrable (fun p : ℝ × ℝ => v (σ + p.1) (axialRot p.2 y)) boxMeasure) ∧
      (∀ᵐ y, Integrable (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y)) boxMeasure)) := by
    filter_upwards [hD1, hR1, hOv, hOG] with σ h1 h3 h4 h5
    refine ⟨h1, ?_, h4, h5⟩
    obtain ⟨hw1, hg1, hweak1⟩ := weak_components (fun y => modeVel ξ v σ y) (fun y => modeGrad ξ G σ y)
      h1.1 h1.2
    exact angular_identity hRot (fun y => modeVel ξ v σ y) (fun y b j => modeGrad ξ G σ y (b, j)) (ξ.2 : ℝ)
      (fun ψ b c => ((axialRot ψ (unitVector c) b : ℝ) : ℂ))
      (fun b c => ((azimuthalField (unitVector c) b : ℝ) : ℂ)) hw1 (fun b j => hg1 b j)
      (fun φ hφ b j => hweak1 φ hφ b j)
      (fun b c => by
        simp only [unit_apply hRot]
        split_ifs <;> simp)
      (fun b c => (hasDerivAt_axialRot (unitVector c) b).ofReal_comp) s hs0 hs
      (fun n => by
        filter_upwards [h3] with y hy b
        have := congrFun (hy n) b
        simpa [rotC] using this)
  exact hall.exists

open Coercive.Internal.ModeRotation in
private theorem cnormSq_vel_rot {v : ℝ → Space → Space} {σ : ℝ} {y : Space}
    (hy : Integrable (fun p : ℝ × ℝ => v (σ + p.1) (axialRot p.2 y)) boxMeasure) (ξ : ℤ × ℤ) (ψ : ℝ) :
    cnormSq (modeVel ξ v σ (axialRot ψ y)) = cnormSq (modeVel ξ v σ y) := by
  have h := modeVel_rotation_of axialRotationHolds_proof ξ ψ (z := (σ, y)) hy
  dsimp only at h
  rw [h, cnormSq_const_mul, Complex.norm_exp_ofReal_mul_I, one_pow, one_mul, cnormSq_rotC]

open Coercive.Internal.ModeRotation in
private theorem cnormSq_grad_rot {G : ℝ → Space → (Space →L[ℝ] Space)} {σ : ℝ} {y : Space}
    (hy : Integrable (fun p : ℝ × ℝ => G (σ + p.1) (axialRot p.2 y)) boxMeasure) (ξ : ℤ × ℤ) (ψ : ℝ) :
    cnormSq (modeGrad ξ G σ (axialRot ψ y)) = cnormSq (modeGrad ξ G σ y) := by
  have h := modeGrad_rotation_of axialRotationHolds_proof ξ ψ (z := (σ, y)) hy
  dsimp only at h
  rw [h, cnormSq_const_mul, Complex.norm_exp_ofReal_mul_I, one_pow, one_mul, cnormSq_rotCMat]

end RayModesInternal

namespace RayModesInternal

open Coercive Coercive.GainInternal Coercive.Internal.ModeRotation CellCert.CellFormula.Internal.RelTrace

private theorem plane_sub {R : ℝ × ℝ → ℝ} : planeRayRegion R ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
  fun _ hp => ⟨hp.1.1, mem_univ _⟩

private theorem plane_integral {R : ℝ × ℝ → ℝ} (hSm : MeasurableSet (planeRayRegion R)) (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 * (planeRayRegion R).indicator f p
      = ∫⁻ p in planeRayRegion R, ENNReal.ofReal p.1 * f p := by
  have h : ∀ p, ENNReal.ofReal p.1 * (planeRayRegion R).indicator f p
      = (planeRayRegion R).indicator (fun p => ENNReal.ofReal p.1 * f p) p := by
    intro p
    by_cases hp : p ∈ planeRayRegion R
    · rw [indicator_of_mem hp, indicator_of_mem hp]
    · rw [indicator_of_notMem hp, indicator_of_notMem hp, mul_zero]
  simp_rw [h]
  rw [setLIntegral_indicator hSm, inter_eq_left.2 plane_sub]

private theorem indicator_aemeasurable {R : ℝ × ℝ → ℝ} (hSm : MeasurableSet (planeRayRegion R))
    {f : ℝ × ℝ → ℝ≥0∞} (hf : AEMeasurable f (volume.restrict halfPlane)) :
    AEMeasurable ((planeRayRegion R).indicator f) (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  rw [aemeasurable_indicator_iff hSm, Measure.restrict_restrict hSm]
  exact hf.mono_measure (Measure.restrict_mono (fun p hp => hp.1.1) le_rfl)

private theorem region_pos : ∀ᵐ x ∂(volume.restrict region), 0 < x.1.1 :=
  (ae_restrict_mem measurableSet_region).mono fun _ hx => hx.1.1

end RayModesInternal

open RayModesInternal Coercive Coercive.GainInternal Coercive.Internal.ModeRotation
  CellCert.CellFormula.Internal.RelTrace CellCert.CellAnalysis in
theorem modeRayInverseSquare : ModeRayInverseSquare := by
  intro R R₀ R₁ hR Γ P v G H g hv hP mm ι
  set ξ := labelHarmonic mm ι with hξ
  set Hk : ℝ := rayInverseSquareConst |(labelAzimuth mm ι : ℝ)| with hHk
  set S := planeRayRegion R with hSdef
  set S3 : Set Space := pointPlane ⁻¹' S with hS3
  have hSm : MeasurableSet S := planeRayRegion_measurable hR.measurable
  have hS3e : IsRayExterior S3 := rayExterior_lift hR
  have hS3m : MeasurableSet S3 := hS3e.1
  have hH0 : 0 ≤ Hk := by
    simp only [hHk, rayInverseSquareConst]
    positivity
  obtain ⟨σ, hW, hAng, hOv, hOG⟩ := slice_choice hv ξ
  have h6 : ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ξ v σ y) ^ 3) < ⊤ := by
    simp only [cnormSq_modeVel_shift hv.periodic_velocity ξ σ]
    exact modeVelSixthFinite Γ P v G H g hv ξ
  have hGf : ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ G σ y)) < ⊤ := by
    have hpars := (CoerciveWeak.modeSquareSumHolds_closed).2.1 G hv.measurable_gradient
      hv.periodic_gradient hv.gradient_finite
    have hle : ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ξ G τ y))
        ≤ periodLIntegral (fun τ y => matSq (G τ y)) := by
      rw [hpars]
      exact ENNReal.le_tsum ξ
    simp only [cnormSq_modeGrad_shift hv.periodic_gradient ξ _ _] at hle ⊢
    rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at hle
    exact lt_of_le_of_lt hle hv.gradient_finite
  have hFr6 : MemLp (fun y => reVec (modeVel ξ v σ y)) 6 volume :=
    memLp_six_of hW.1.1.aestronglyMeasurable _ (fun y => reVec_le _) h6
  have hFi6 : MemLp (fun y => imVec (modeVel ξ v σ y)) 6 volume :=
    memLp_six_of hW.2.1.aestronglyMeasurable _ (fun y => imVec_le _) h6
  have hGrE := integrable_entrySq_of hW.1.2.1.aestronglyMeasurable _ (fun y => entrySq_reMat_le _) hGf
  have hGiE := integrable_entrySq_of hW.2.2.1.aestronglyMeasurable _ (fun y => entrySq_imMat_le _) hGf
  have hr := radialRay S3 hS3e _ _ hFr6 hW.1.2.1.aestronglyMeasurable hGrE hW.1
  have hi := radialRay S3 hS3e _ _ hFi6 hW.2.2.1.aestronglyMeasurable hGiE hW.2
  set C : Space → ℝ≥0∞ := fun y => ENNReal.ofReal
    (cnormSq (fun b => ∑ j, modeGrad ξ G σ y (b, j) * (azimuthalField y j : ℂ)) / (y 0 ^ 2 + y 1 ^ 2)) with hC
  have hpos : ∀ y ∈ S3, 0 < y 0 ^ 2 + y 1 ^ 2 := by
    intro y hy
    have h1 : 0 < (pointPlane y).1 := hy.1.1
    simp only [pointPlane] at h1
    exact Real.sqrt_pos.1 h1
  have hA : AEMeasurable (fun y => ENNReal.ofReal (‖reVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2)) volume :=
    ((hW.1.1.aestronglyMeasurable.norm.pow 2).aemeasurable.div
      (measurable_norm.pow_const 2).aemeasurable).ennreal_ofReal
  have hB : AEMeasurable (fun y => ENNReal.ofReal (‖imVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2)) volume :=
    ((hW.2.1.aestronglyMeasurable.norm.pow 2).aemeasurable.div
      (measurable_norm.pow_const 2).aemeasurable).ennreal_ofReal
  have hquart : ENNReal.ofReal (1 / 4) * 4 = 1 := by
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have key3 : ∫⁻ y in S3, ENNReal.ofReal (Hk * (cnormSq (modeVel ξ v σ y) / ‖y‖ ^ 2))
      ≤ ∫⁻ y in S3, ENNReal.ofReal (cnormSq (modeGrad ξ G σ y)) := by
    have hpt1 : ∀ᵐ y ∂(volume.restrict S3), ENNReal.ofReal (Hk * (cnormSq (modeVel ξ v σ y) / ‖y‖ ^ 2))
        ≤ ENNReal.ofReal (1 / 4) * ENNReal.ofReal (‖reVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2)
          + (ENNReal.ofReal (1 / 4) * ENNReal.ofReal (‖imVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2) + C y) := by
      rw [ae_restrict_iff' hS3m]
      filter_upwards [hAng] with y hy hyS
      have hr2 := hpos y hyS
      have hny : y 0 ^ 2 + y 1 ^ 2 ≤ ‖y‖ ^ 2 := by rw [norm_sq_three]; nlinarith [sq_nonneg (y 2)]
      have hn0 : 0 < ‖y‖ ^ 2 := lt_of_lt_of_le hr2 hny
      have hg := gain_sq (modeVel ξ v σ y) _ (ξ.2 : ℝ) fun b => hy b
      have hsplit := cnormSq_re_im (modeVel ξ v σ y)
      set X := cnormSq (modeVel ξ v σ y) with hX
      set U := cnormSq (fun b => ∑ j, modeGrad ξ G σ y (b, j) * (azimuthalField y j : ℂ)) with hU
      have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => by positivity
      have hk : |(labelAzimuth mm ι : ℝ)| = |(ξ.2 : ℝ)| := rfl
      have hc : max (|(ξ.2 : ℝ)| - 1) 0 ^ 2 * X / ‖y‖ ^ 2 ≤ U / (y 0 ^ 2 + y 1 ^ 2) := by
        calc max (|(ξ.2 : ℝ)| - 1) 0 ^ 2 * X / ‖y‖ ^ 2
            ≤ max (|(ξ.2 : ℝ)| - 1) 0 ^ 2 * X / (y 0 ^ 2 + y 1 ^ 2) :=
              div_le_div_of_nonneg_left (by positivity) hr2 hny
          _ ≤ U / (y 0 ^ 2 + y 1 ^ 2) := div_le_div_of_nonneg_right hg hr2.le
      have hreal : Hk * (X / ‖y‖ ^ 2) ≤ 1 / 4 * (‖reVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2)
          + (1 / 4 * (‖imVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2) + U / (y 0 ^ 2 + y 1 ^ 2)) := by
        have e1 : Hk * (X / ‖y‖ ^ 2) = 1 / 4 * (‖reVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2)
            + 1 / 4 * (‖imVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2)
            + max (|(ξ.2 : ℝ)| - 1) 0 ^ 2 * X / ‖y‖ ^ 2 := by
          rw [hHk, rayInverseSquareConst, hk, hsplit]
          ring
        rw [e1]
        linarith
      have hU0 : 0 ≤ U / (y 0 ^ 2 + y 1 ^ 2) := div_nonneg (cnormSq_nonneg _) hr2.le
      have ha0 : 0 ≤ 1 / 4 * (‖reVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2) := by positivity
      have hb0 : 0 ≤ 1 / 4 * (‖imVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2) := by positivity
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add hb0 hU0, ← ENNReal.ofReal_add ha0 (add_nonneg hb0 hU0)]
      exact ENNReal.ofReal_le_ofReal hreal
    have hpt2 : ∀ᵐ y ∂(volume.restrict S3),
        ENNReal.ofReal (‖radialApply (reMat (modeGrad ξ G σ y)) y‖ ^ 2)
          + (ENNReal.ofReal (‖radialApply (imMat (modeGrad ξ G σ y)) y‖ ^ 2) + C y)
        ≤ ENNReal.ofReal (cnormSq (modeGrad ξ G σ y)) := by
      rw [ae_restrict_iff' hS3m]
      refine Eventually.of_forall fun y hyS => ?_
      have hr2 := hpos y hyS
      have hgs := grad_split (modeGrad ξ G σ y) y hr2
      have hU0 : 0 ≤ cnormSq (fun b => ∑ j, modeGrad ξ G σ y (b, j) * (azimuthalField y j : ℂ))
          / (y 0 ^ 2 + y 1 ^ 2) := div_nonneg (cnormSq_nonneg _) hr2.le
      have hb0 : 0 ≤ ‖radialApply (imMat (modeGrad ξ G σ y)) y‖ ^ 2 := by positivity
      simp only [hC]
      rw [← ENNReal.ofReal_add hb0 hU0, ← ENNReal.ofReal_add (by positivity) (add_nonneg hb0 hU0)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc ∫⁻ y in S3, ENNReal.ofReal (Hk * (cnormSq (modeVel ξ v σ y) / ‖y‖ ^ 2))
        ≤ ∫⁻ y in S3, (ENNReal.ofReal (1 / 4) * ENNReal.ofReal (‖reVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2)
          + (ENNReal.ofReal (1 / 4) * ENNReal.ofReal (‖imVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2) + C y)) :=
          lintegral_mono_ae hpt1
      _ = ENNReal.ofReal (1 / 4) * (∫⁻ y in S3, ENNReal.ofReal (‖reVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2))
          + (ENNReal.ofReal (1 / 4) * (∫⁻ y in S3, ENNReal.ofReal (‖imVec (modeVel ξ v σ y)‖ ^ 2 / ‖y‖ ^ 2))
            + ∫⁻ y in S3, C y) := by
          rw [lintegral_add_left' (hA.const_mul _).restrict, lintegral_add_left' (hB.const_mul _).restrict,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 / 4) * (4 * ∫⁻ y in S3, ENNReal.ofReal (‖radialApply (reMat (modeGrad ξ G σ y)) y‖ ^ 2))
          + (ENNReal.ofReal (1 / 4) * (4 * ∫⁻ y in S3,
              ENNReal.ofReal (‖radialApply (imMat (modeGrad ξ G σ y)) y‖ ^ 2))
            + ∫⁻ y in S3, C y) := by
          gcongr
      _ = (∫⁻ y in S3, ENNReal.ofReal (‖radialApply (reMat (modeGrad ξ G σ y)) y‖ ^ 2))
          + ((∫⁻ y in S3, ENNReal.ofReal (‖radialApply (imMat (modeGrad ξ G σ y)) y‖ ^ 2))
            + ∫⁻ y in S3, C y) := by
          rw [← mul_assoc, ← mul_assoc, hquart, one_mul, one_mul]
      _ ≤ ∫⁻ y in S3, (ENNReal.ofReal (‖radialApply (reMat (modeGrad ξ G σ y)) y‖ ^ 2)
          + (ENNReal.ofReal (‖radialApply (imMat (modeGrad ξ G σ y)) y‖ ^ 2) + C y)) :=
          (add_le_add le_rfl (le_lintegral_add _ _)).trans (le_lintegral_add _ _)
      _ ≤ ∫⁻ y in S3, ENNReal.ofReal (cnormSq (modeGrad ξ G σ y)) := lintegral_mono_ae hpt2
  obtain ⟨hVm, hGm2, -⟩ := aestronglyMeasurable_labelFields hv mm ι
  have hρm : Measurable planeRadius := by
    unfold planeRadius
    fun_prop
  have hcn3 : Continuous (cnormSq : (Fin 3 → ℂ) → ℝ) := by
    unfold cnormSq
    fun_prop
  have hcn9 : Continuous (cnormSq : (Fin 3 × Fin 3 → ℂ) → ℝ) := by
    unfold cnormSq
    fun_prop
  set g1 : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Hk * (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2)) with hg1def
  set g2 : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (cnormSq (labelGrad mm ι G p)) with hg2def
  have hg1 : AEMeasurable g1 (volume.restrict halfPlane) :=
    ((((hcn3.comp_aestronglyMeasurable hVm).aemeasurable.div
      (hρm.pow_const 2).aemeasurable).const_mul Hk)).ennreal_ofReal
  have hg2 : AEMeasurable g2 (volume.restrict halfPlane) :=
    (hcn9.comp_aestronglyMeasurable hGm2).aemeasurable.ennreal_ofReal
  have hcylL : ∀ᵐ x ∂(volume.restrict region),
      S3.indicator (fun y => ENNReal.ofReal (Hk * (cnormSq (modeVel ξ v σ y) / ‖y‖ ^ 2))) (cylF x)
        = S.indicator g1 x.1 := by
    filter_upwards [ae_region_of_ae hOv, region_pos] with x hx hx0
    obtain ⟨⟨r, z⟩, θ⟩ := x
    have hmem : cylPoint r θ z ∈ S3 ↔ (r, z) ∈ S := by
      simp only [hS3, mem_preimage, pointPlane_cyl hx0.le]
    have hrot := cnormSq_vel_rot (y := cylPoint r θ z) hx ξ (-θ)
    show S3.indicator _ (cylPoint r θ z) = S.indicator g1 (r, z)
    by_cases hS : (r, z) ∈ S
    · rw [indicator_of_mem (hmem.2 hS), indicator_of_mem hS, hg1def]
      simp only
      rw [norm_cyl, ← hrot, rot_cyl, cnormSq_modeVel_shift hv.periodic_velocity]
      rfl
    · rw [indicator_of_notMem (fun h => hS (hmem.1 h)), indicator_of_notMem hS]
  have hcylR : ∀ᵐ x ∂(volume.restrict region),
      S3.indicator (fun y => ENNReal.ofReal (cnormSq (modeGrad ξ G σ y))) (cylF x) = S.indicator g2 x.1 := by
    filter_upwards [ae_region_of_ae hOG, region_pos] with x hx hx0
    obtain ⟨⟨r, z⟩, θ⟩ := x
    have hmem : cylPoint r θ z ∈ S3 ↔ (r, z) ∈ S := by
      simp only [hS3, mem_preimage, pointPlane_cyl hx0.le]
    have hrot := cnormSq_grad_rot (y := cylPoint r θ z) hx ξ (-θ)
    show S3.indicator _ (cylPoint r θ z) = S.indicator g2 (r, z)
    by_cases hS : (r, z) ∈ S
    · rw [indicator_of_mem (hmem.2 hS), indicator_of_mem hS, hg2def]
      simp only
      rw [← hrot, rot_cyl, cnormSq_modeGrad_shift hv.periodic_gradient]
      rfl
    · rw [indicator_of_notMem (fun h => hS (hmem.1 h)), indicator_of_notMem hS]
  have eqL : ∫⁻ y in S3, ENNReal.ofReal (Hk * (cnormSq (modeVel ξ v σ y) / ‖y‖ ^ 2))
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ p in S, ENNReal.ofReal p.1 * g1 p := by
    rw [← lintegral_indicator hS3m, cyl_transfer _ (S.indicator g1) (indicator_aemeasurable hSm hg1) hcylL,
      plane_integral hSm]
  have eqR : ∫⁻ y in S3, ENNReal.ofReal (cnormSq (modeGrad ξ G σ y))
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ p in S, ENNReal.ofReal p.1 * g2 p := by
    rw [← lintegral_indicator hS3m, cyl_transfer _ (S.indicator g2) (indicator_aemeasurable hSm hg2) hcylR,
      plane_integral hSm]
  rw [eqL, eqR] at key3
  have h2pi : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have key2 := (ENNReal.mul_le_mul_iff_right h2pi ENNReal.ofReal_ne_top).1 key3
  have hL : ∫⁻ p in S, ENNReal.ofReal p.1 * g1 p
      = ENNReal.ofReal Hk * ∫⁻ p in S, ENNReal.ofReal (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2 * p.1) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun hSm fun p hp => ?_
    rw [hg1def]
    simp only
    rw [← ENNReal.ofReal_mul hp.1.1.le, ← ENNReal.ofReal_mul hH0]
    congr 1
    ring
  have hR' : ∫⁻ p in S, ENNReal.ofReal p.1 * g2 p
      = ∫⁻ p in S, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1) := by
    refine setLIntegral_congr_fun hSm fun p hp => ?_
    rw [hg2def]
    simp only
    rw [← ENNReal.ofReal_mul hp.1.1.le]
    congr 1
    ring
  rw [hL, hR'] at key2
  exact key2

end TailBand

end CertCell

end Breakdown
