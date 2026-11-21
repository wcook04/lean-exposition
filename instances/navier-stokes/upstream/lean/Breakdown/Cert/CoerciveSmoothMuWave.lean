import Breakdown.Cert.CoerciveSmoothMuGlue
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveSmoothPieceMuDivergence
import Breakdown.Cert.CoercivePieceFieldCurlWeightTest

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuSmooth


theorem exp_pair_mul (ι α : ℤ × ℤ) (τ φ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-(((2 * Real.pi * (ι - α).1 * τ + (ι - α).2 * φ : ℝ) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  push_cast
  ring

theorem exp_pair_mul_conj (ι α : ℤ × ℤ) (τ φ : ℝ) :
    Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * Complex.exp (-(((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I))
      = Complex.exp (-(((2 * Real.pi * (ι + α).1 * τ + (ι + α).2 * φ : ℝ) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  push_cast
  ring

theorem re_exp_mul_eq (θ : ℝ) (z : ℂ) :
    (((Complex.exp ((θ : ℂ) * Complex.I) * z).re : ℝ) : ℂ)
      = (Complex.exp ((θ : ℂ) * Complex.I) * z + Complex.exp (-((θ : ℂ) * Complex.I)) * (starRingEnd ℂ) z) / 2 := by
  rw [Complex.re_eq_add_conj, map_mul, ← Complex.exp_conj]
  congr 3
  simp [Complex.conj_ofReal]

theorem mode_re_mul {β : Type*} (ι α : ℤ × ℤ) (z : ℂ) (u : ℝ → ℝ → ℝ)
    (hu : Continuous fun p : ℝ × ℝ => u p.1 p.2) (b : β) :
    modeAverage ι (fun τ φ (_ : β) =>
        (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * z).re * u τ φ) b
      = (z * modeAverage (ι - α) (fun τ φ (_ : β) => u τ φ) b
        + (starRingEnd ℂ) z * modeAverage (ι + α) (fun τ φ (_ : β) => u τ φ) b) / 2 := by
  unfold modeAverage
  set E : ℤ × ℤ → ℝ → ℝ → ℂ := fun κ τ φ =>
    Complex.exp (-(((2 * Real.pi * κ.1 * τ + κ.2 * φ : ℝ) : ℂ) * Complex.I)) with hE
  have hEc : ∀ κ, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 := fun κ => by rw [hE]; fun_prop
  have hf : ∀ κ, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 * ((u p.1 p.2 : ℝ) : ℂ) := fun κ =>
    (hEc κ).mul (Complex.continuous_ofReal.comp hu)
  have hpt : ∀ τ φ, Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * (((Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * z).re * u τ φ : ℝ) : ℂ)
      = (z / 2) * (E (ι - α) τ φ * ((u τ φ : ℝ) : ℂ))
        + ((starRingEnd ℂ) z / 2) * (E (ι + α) τ φ * ((u τ φ : ℝ) : ℂ)) := by
    intro τ φ
    rw [Complex.ofReal_mul, re_exp_mul_eq, hE]
    simp only
    rw [← exp_pair_mul ι α τ φ, ← exp_pair_mul_conj ι α τ φ]
    ring
  simp_rw [hpt]
  have hin : ∀ κ τ, IntervalIntegrable (fun φ => E κ τ φ * ((u τ φ : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    fun κ τ => ((hf κ).comp (Continuous.prodMk_right τ)).intervalIntegrable _ _
  have hout : ∀ κ, IntervalIntegrable (fun τ => ∫ φ in (0 : ℝ)..(2 * Real.pi), E κ τ φ * ((u τ φ : ℝ) : ℂ))
      volume 0 1 := fun κ =>
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun τ φ => E κ τ φ * ((u τ φ : ℝ) : ℂ)) (hf κ) 0 (2 * Real.pi)).intervalIntegrable _ _
  have s1 : ∀ τ, (∫ φ in (0 : ℝ)..(2 * Real.pi), ((z / 2) * (E (ι - α) τ φ * ((u τ φ : ℝ) : ℂ))
        + ((starRingEnd ℂ) z / 2) * (E (ι + α) τ φ * ((u τ φ : ℝ) : ℂ))))
      = (z / 2) * (∫ φ in (0 : ℝ)..(2 * Real.pi), E (ι - α) τ φ * ((u τ φ : ℝ) : ℂ))
        + ((starRingEnd ℂ) z / 2) * ∫ φ in (0 : ℝ)..(2 * Real.pi), E (ι + α) τ φ * ((u τ φ : ℝ) : ℂ) := by
    intro τ
    rw [intervalIntegral.integral_add ((hin _ τ).const_mul _) ((hin _ τ).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [s1]
  rw [intervalIntegral.integral_add ((hout _).const_mul _) ((hout _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

def boxInt (F : ℝ → ℝ → ℂ) : ℂ := ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), F τ φ

theorem boxInt_add (F G : ℝ → ℝ → ℂ) (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2) :
    boxInt (fun τ φ => F τ φ + G τ φ) = boxInt F + boxInt G := by
  unfold boxInt
  have h1 : ∀ τ, (∫ φ in (0 : ℝ)..(2 * Real.pi), (F τ φ + G τ φ))
      = (∫ φ in (0 : ℝ)..(2 * Real.pi), F τ φ) + ∫ φ in (0 : ℝ)..(2 * Real.pi), G τ φ := fun τ =>
    intervalIntegral.integral_add ((hF.comp (Continuous.prodMk_right τ)).intervalIntegrable _ _)
      ((hG.comp (Continuous.prodMk_right τ)).intervalIntegrable _ _)
  simp_rw [h1]
  exact intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := F) hF 0 (2 * Real.pi)).intervalIntegrable _ _)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := G) hG 0 (2 * Real.pi)).intervalIntegrable _ _)

theorem boxInt_const_mul (c : ℂ) (F : ℝ → ℝ → ℂ) : boxInt (fun τ φ => c * F τ φ) = c * boxInt F := by
  unfold boxInt
  simp_rw [intervalIntegral.integral_const_mul]

theorem boxInt_zero : boxInt (fun _ _ => (0 : ℂ)) = 0 := by
  simp [boxInt]

theorem boxInt_sum {κ : Type*} (s : Finset κ) (F : κ → ℝ → ℝ → ℂ)
    (hF : ∀ k, Continuous fun p : ℝ × ℝ => F k p.1 p.2) :
    boxInt (fun τ φ => ∑ k ∈ s, F k τ φ) = ∑ k ∈ s, boxInt (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using boxInt_zero
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [boxInt_add _ _ (hF a) (continuous_finsetSum _ fun k _ => hF k), ih]

theorem modeAverage_eq_boxInt {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage ι f b = (1 / (2 * Real.pi) : ℂ) * boxInt (fun τ φ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b : ℝ) : ℂ)) := rfl

theorem rot_rot_neg (φ : ℝ) (x : Space) : axialRot φ (axialRot (-φ) x) = x := by
  ext i
  fin_cases i
  · simp [axialRot, unitVector, Real.cos_neg, Real.sin_neg]
    linear_combination x 0 * Real.sin_sq_add_cos_sq φ
  · simp [axialRot, unitVector, Real.cos_neg, Real.sin_neg]
    linear_combination x 1 * Real.sin_sq_add_cos_sq φ
  · simp [axialRot, unitVector]

theorem vec_expand (x : Space) : x = ∑ j : Fin 3, x j • unitVector j := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem rot_sum (ψ : ℝ) (c : Fin 3 → ℝ) (X : Fin 3 → Space) :
    axialRot ψ (∑ k : Fin 3, c k • X k) = ∑ k : Fin 3, c k • axialRot ψ (X k) := by
  simp only [Fin.sum_univ_three]
  ext i
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

theorem rot_apply_clm (L : Space →L[ℝ] Space) (φ : ℝ) (x : Space) (i : Fin 3) :
    axialRot (-φ) (L x) i
      = ∑ j : Fin 3, axialRot (-φ) (L (axialRot φ (unitVector j))) i * axialRot (-φ) x j := by
  have hx : x = ∑ j : Fin 3, axialRot (-φ) x j • axialRot φ (unitVector j) := by
    conv_lhs => rw [← rot_rot_neg φ x, vec_expand (axialRot (-φ) x)]
    rw [rot_sum]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp_rw [map_smul]
  rw [rot_sum]
  simp only [Fin.sum_univ_three]
  simp [mul_comm]

theorem cont_rot_field (v : ℝ → Space → Space) (hvc : Continuous fun z : ℝ × Space => v z.1 z.2) (σ : ℝ)
    (y : Space) (j : Fin 3) :
    Continuous fun p : ℝ × ℝ => ((axialRot (-p.2) (v (σ + p.1) (axialRot p.2 y)) j : ℝ) : ℂ) := by
  have h0 : Continuous fun p : ℝ × ℝ => ((σ + p.1, axialRot p.2 y) : ℝ × Space) := by
    unfold axialRot
    fun_prop
  have h1 : Continuous fun p : ℝ × ℝ => v (σ + p.1) (axialRot p.2 y) := hvc.comp h0
  have h2 : Continuous fun p : ℝ × ℝ => axialRot (-p.2) (v (σ + p.1) (axialRot p.2 y)) := by
    unfold axialRot
    fun_prop
  exact Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j).comp h2)

theorem cont_exp_pair (κ : ℤ × ℤ) :
    Continuous fun p : ℝ × ℝ => Complex.exp (-(((2 * Real.pi * κ.1 * p.1 + κ.2 * p.2 : ℝ) : ℂ) * Complex.I)) := by
  fun_prop

theorem mode_product (s : Finset (ℤ × ℤ)) (W v : ℝ → Space → Space)
    (hvc : Continuous fun z : ℝ × Space => v z.1 z.2) (σ : ℝ) (y : Space)
    (D : Fin 3 → Fin 3 → ℝ) (g : ℤ × ℤ → Fin 3 × Fin 3 → ℂ)
    (hE : ∀ τ φ : ℝ, ∀ i j : Fin 3,
      ((axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ)
        = (D i j : ℂ) + ∑ α ∈ s, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * g α (i, j))
    (ι : ℤ × ℤ) (i : Fin 3) :
    modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y i
      = ∑ j : Fin 3, ((D i j : ℂ) * modeVel ι v σ y j + ∑ α ∈ s, g α (i, j) * modeVel (ι - α) v σ y j) := by
  set E : ℤ × ℤ → ℝ → ℝ → ℂ := fun κ τ φ =>
    Complex.exp (-(((2 * Real.pi * κ.1 * τ + κ.2 * φ : ℝ) : ℂ) * Complex.I)) with hEdef
  set U : Fin 3 → ℝ → ℝ → ℂ := fun j τ φ => ((axialRot (-φ) (v (σ + τ) (axialRot φ y)) j : ℝ) : ℂ) with hUdef
  have hUc : ∀ j, Continuous fun p : ℝ × ℝ => U j p.1 p.2 := fun j => cont_rot_field v hvc σ y j
  have hEc : ∀ κ, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 := fun κ => cont_exp_pair κ
  have hmv : ∀ κ j, modeVel κ v σ y j = (1 / (2 * Real.pi) : ℂ) * boxInt (fun τ φ => E κ τ φ * U j τ φ) :=
    fun κ j => rfl
  have hpt : ∀ τ φ, E ι τ φ * ((axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y)
        (v (σ + τ) (axialRot φ y))) i : ℝ) : ℂ)
      = ∑ j : Fin 3, ((D i j : ℂ) * (E ι τ φ * U j τ φ)
        + ∑ α ∈ s, g α (i, j) * (E (ι - α) τ φ * U j τ φ)) := by
    intro τ φ
    rw [rot_apply_clm]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hE τ φ i j, hEdef, hUdef]
    simp only
    rw [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [← exp_pair_mul ι α τ φ]
      ring
  have hlhs : modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y i
      = (1 / (2 * Real.pi) : ℂ) * boxInt (fun τ φ => ∑ j : Fin 3, ((D i j : ℂ) * (E ι τ φ * U j τ φ)
        + ∑ α ∈ s, g α (i, j) * (E (ι - α) τ φ * U j τ φ))) := by
    rw [← funext fun τ => funext fun φ => hpt τ φ]
    rfl
  have hc1 : ∀ κ j, Continuous fun p : ℝ × ℝ => E κ p.1 p.2 * U j p.1 p.2 := fun κ j => (hEc κ).mul (hUc j)
  rw [hlhs, boxInt_sum _ _ (fun j => ((continuous_const.mul (hc1 ι j)).add
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j))))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [boxInt_add _ _ (continuous_const.mul (hc1 ι j))
    (continuous_finsetSum _ fun α _ => continuous_const.mul (hc1 (ι - α) j)),
    boxInt_sum _ _ (fun α => continuous_const.mul (hc1 (ι - α) j)), boxInt_const_mul, hmv]
  simp_rw [boxInt_const_mul, hmv]
  rw [mul_add, Finset.mul_sum, mul_left_comm]
  congr 1
  exact Finset.sum_congr rfl fun α _ => mul_left_comm _ _ _

end Internal.MuSmooth

namespace Internal.MuSmooth

theorem rot_modeVel_eq {W : ℝ → Space → Space} (hWc : Continuous (fun z : ℝ × Space => W z.1 z.2))
    (ι : ℤ × ℤ) (σ τ φ : ℝ) (x : Space) (i : Fin 3) :
    modeVel ι (fun s x => axialRot (-φ) (W (s + τ) (axialRot φ x))) σ x i
      = ∑ k : Fin 3, ((axialRot (-φ) (unitVector k) i : ℝ) : ℂ) * modeVel ι W (σ + τ) (axialRot φ x) k := by
  have hRot := axialRotationHolds_proof
  have hpt : ∀ τ' φ' : ℝ, axialRot (-φ') (axialRot (-φ) (W (σ + τ' + τ) (axialRot φ (axialRot φ' x)))) i
      = ∑ k : Fin 3, axialRot (-φ) (unitVector k) i
          * axialRot (-φ') (W (σ + τ + τ') (axialRot φ' (axialRot φ x))) k := by
    intro τ' φ'
    rw [← hRot.2.1, ← hRot.2.1, ← hRot.2.1, show -φ' + -φ = -φ + -φ' by ring, show φ + φ' = φ' + φ by ring,
      show σ + τ' + τ = σ + τ + τ' by ring, hRot.2.1 (-φ) (-φ'), hRot.2.1 φ' φ]
    exact Internal.ModeRotation.axialRot_apply (-φ) _ i
  have ha : ∀ k : Fin 3, Integrable (fun p : ℝ × ℝ =>
      axialRot (-p.2) (W (σ + τ + p.1) (axialRot p.2 (axialRot φ x))) k) Internal.ModeRotation.boxMeasure := by
    intro k
    apply CurlWeight.Internal.TestModes.integrable_box_of_continuous
    have h0 : Continuous fun p : ℝ × ℝ => ((σ + τ + p.1, axialRot p.2 (axialRot φ x)) : ℝ × Space) := by
      unfold axialRot
      fun_prop
    have h1 : Continuous fun p : ℝ × ℝ => W (σ + τ + p.1) (axialRot p.2 (axialRot φ x)) := hWc.comp h0
    have h2 : Continuous fun p : ℝ × ℝ => axialRot (-p.2) (W (σ + τ + p.1) (axialRot p.2 (axialRot φ x))) := by
      unfold axialRot
      fun_prop
    exact (PiLp.continuous_apply 2 _ k).comp h2
  unfold modeVel
  rw [Internal.ModeRotation.modeAverage_eq]
  simp only [hpt]
  rw [Internal.ModeRotation.modeAverage_sum ι (fun k => axialRot (-φ) (unitVector k) i)
    (fun k τ' φ' => axialRot (-φ') (W (σ + τ + τ') (axialRot φ' (axialRot φ x))) k) ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Internal.ModeRotation.modeAverage_eq]
  ring

theorem re_sum_real_mul (c : Fin 3 → ℝ) (z : Fin 3 → ℂ) :
    (∑ k : Fin 3, ((c k : ℝ) : ℂ) * z k).re = ∑ k : Fin 3, c k * (z k).re := by
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun k _ => Complex.re_ofReal_mul _ _

theorem rot_field_expansion {W : ℝ → Space → Space} (hWc : Continuous (fun z : ℝ × Space => W z.1 z.2))
    (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ))
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (x : Space) (i : Fin 3) :
    axialRot (-φ) (W (σ + τ) (axialRot φ x)) i = (modeVel (0, 0) W σ x i).re
      + ∑ α ∈ s, (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel α W σ x i).re := by
  have hS : ∀ ι : ℤ × ℤ, Complex.exp (((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I) * modeVel ι W σ x i
      = ∑ k : Fin 3, ((axialRot (-φ) (unitVector k) i : ℝ) : ℂ) * modeVel ι W (σ + τ) (axialRot φ x) k := by
    intro ι
    rw [← Internal.SmoothPieceMuDivergence.modeVel_shiftRot ι W hWp τ φ σ x i, rot_modeVel_eq hWc]
  have h0 : modeVel (0, 0) W σ x i
      = ∑ k : Fin 3, ((axialRot (-φ) (unitVector k) i : ℝ) : ℂ) * modeVel (0, 0) W (σ + τ) (axialRot φ x) k := by
    rw [← hS (0, 0)]
    simp
  rw [h0, re_sum_real_mul]
  simp_rw [hS, re_sum_real_mul]
  rw [Internal.ModeRotation.axialRot_apply (-φ) _ i, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hh (σ + τ) (axialRot φ x) k, mul_add, Finset.mul_sum]

theorem modeVel_mean_shift {W : ℝ → Space → Space} (hWp : IsTimePeriodic W) (σ : ℝ) (x : Space) (i : Fin 3) :
    modeVel (0, 0) W σ x i = modeVel (0, 0) W 0 x i := by
  have hRot := axialRotationHolds_proof
  have h := Internal.SmoothPieceMuDivergence.modeVel_shiftRot (0, 0) W hWp σ 0 0 x i
  have e : (fun s y => axialRot (-0) (W (s + σ) (axialRot 0 y))) = fun s y => W (s + σ) y := by
    funext s y
    rw [neg_zero, hRot.2.2.1, hRot.2.2.1]
  rw [e] at h
  simp only [Int.cast_zero, mul_zero, zero_mul, add_zero, Complex.ofReal_zero, Complex.exp_zero, one_mul] at h
  rw [← h]
  unfold modeVel
  congr 1
  funext τ φ j
  beta_reduce
  rw [add_comm σ τ, zero_add]

end Internal.MuSmooth

namespace Internal.MuSmooth

open Filter

open Internal.ModeRotation ModeDerivative.Internal CurlWeight.Internal.TestModes

theorem slice_contDiff_of {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (s : ℝ) : ContDiff ℝ 2 (W s) :=
  hW.comp (contDiff_const.prodMk contDiff_id)

theorem continuous_slice_fderiv_of {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
  (ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => W z.1 y) (g := fun z => z.2)
    (hW.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
    (n := 1) (by norm_num)).continuous

theorem hasFDerivAt_integrand_of {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (ι : ℤ × ℤ)
    (σ : ℝ) (l : Fin 3) (x : Space) (p : ℝ × ℝ) :
    HasFDerivAt (fun x => modeTestIntegrand W ι σ l x p) (modeTestIntegrandDeriv W ι σ l x p) x := by
  have hRot := axialRotationHolds_proof
  have e1 : (fun x => axialRot p.2 x) = ⇑((rotIso hRot p.2 : Space ≃ₗᵢ[ℝ] Space).toContinuousLinearEquiv
      : Space →L[ℝ] Space) := by
    funext x
    exact (rotIso_apply hRot p.2 x).symm
  have h1 : HasFDerivAt (fun x => axialRot p.2 x)
      ((rotIso hRot p.2).toContinuousLinearEquiv : Space →L[ℝ] Space) x := by
    rw [e1]
    exact ContinuousLinearMap.hasFDerivAt _
  have h2 : HasFDerivAt (W (σ + p.1)) (fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)) (axialRot p.2 x) :=
    ((slice_contDiff_of hW (σ + p.1)).differentiable (by norm_num) _).hasFDerivAt
  have e3 : (fun w : Space => axialRot (-p.2) w) = ⇑((rotIso hRot p.2).symm.toContinuousLinearEquiv
      : Space →L[ℝ] Space) := by
    funext w
    exact (rotIso_symm_apply hRot p.2 w).symm
  have h3 : ∀ w, HasFDerivAt (fun w : Space => axialRot (-p.2) w)
      ((rotIso hRot p.2).symm.toContinuousLinearEquiv : Space →L[ℝ] Space) w := by
    intro w
    rw [e3]
    exact ContinuousLinearMap.hasFDerivAt _
  have h4 := (h3 _).comp x (h2.comp x h1)
  have h5 := ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).hasFDerivAt).comp x h4
  have h6 := (Complex.ofRealCLM.hasFDerivAt).comp x h5
  have h7 := h6.const_mul (expFactor ι p.1 p.2)
  refine HasFDerivAt.congr_of_eventuallyEq (h7.congr_fderiv ?_) (Filter.Eventually.of_forall fun y => ?_)
  · refine ContinuousLinearMap.ext fun u => ?_
    simp [modeTestIntegrandDeriv, rotConj_apply, rotIso_apply, rotIso_symm_apply]
  · simp [modeTestIntegrand]

theorem continuous_integrandDeriv_of {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (x : Space) :
    Continuous (fun p => modeTestIntegrandDeriv W ι σ l x p) := by
  have hA : Continuous (fun p : ℝ × ℝ => fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)) :=
    (continuous_slice_fderiv_of hW).comp ((continuous_const.add continuous_fst).prodMk
      (continuous_axialRot_comp continuous_snd continuous_const))
  have hB : Continuous (fun p : ℝ × ℝ =>
      rotConj axialRotationHolds_proof p.2 (fderiv ℝ (W (σ + p.1)) (axialRot p.2 x))) :=
    Continuous.comp (g := fun q : ℝ × (Space →L[ℝ] Space) => rotConj axialRotationHolds_proof q.1 q.2)
      (f := fun p : ℝ × ℝ => (p.2, fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)))
      (continuous_rotConj axialRotationHolds_proof) (continuous_snd.prodMk hA)
  refine continuous_clm_apply.2 fun u => ?_
  have e : (fun p => modeTestIntegrandDeriv W ι σ l x p u) = fun p => expFactor ι p.1 p.2 *
      ((rotConj axialRotationHolds_proof p.2 (fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)) u l : ℝ) : ℂ) := by
    funext p
    simp [modeTestIntegrandDeriv]
  rw [e]
  exact (continuous_expFactor ι).mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp (hB.clm_apply continuous_const)))

theorem continuous_integrand_of {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (x : Space) :
    Continuous (fun p => modeTestIntegrand W ι σ l x p) := by
  have hA : Continuous (fun p : ℝ × ℝ => W (σ + p.1) (axialRot p.2 x)) :=
    hW.continuous.comp ((continuous_const.add continuous_fst).prodMk
      (continuous_axialRot_comp continuous_snd continuous_const))
  have hB : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (W (σ + p.1) (axialRot p.2 x))) :=
    continuous_axialRot_comp continuous_snd.neg hA
  unfold modeTestIntegrand
  exact (continuous_expFactor ι).mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp hB))

theorem modeVel_eq_box_of {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (ι : ℤ × ℤ) (σ : ℝ)
    (l : Fin 3) (x : Space) :
    modeVel ι W σ x l = (1 / (2 * Real.pi) : ℂ) * ∫ p, modeTestIntegrand W ι σ l x p ∂boxMeasure := by
  unfold modeVel
  rw [modeAverage_eq]
  congr 1
  exact iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (W (σ + τ) (axialRot φ x)) l : ℝ) : ℂ))
    (integrable_box_of_continuous (continuous_integrand_of hW ι σ l x))

theorem modeVel_hasFDerivAt_of {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (ι : ℤ × ℤ) (σ : ℝ) (l : Fin 3) (y : Space) :
    ∃ L : Space →L[ℝ] ℂ, HasFDerivAt (fun x => modeVel ι W σ x l) L y ∧
      ∀ j, L (unitVector j) = modeGrad ι (gradField W) σ y (l, j) := by
  have hbound : ∀ᵐ p ∂boxMeasure, ∀ x ∈ (Set.univ : Set Space),
      ‖modeTestIntegrandDeriv W ι σ l x p‖ ≤ B :=
    Filter.Eventually.of_forall fun p x _ => (norm_modeTestIntegrandDeriv_le ι σ l x p).trans (hB _ _)
  refine ⟨(1 / (2 * Real.pi) : ℂ) • ∫ p, modeTestIntegrandDeriv W ι σ l y p ∂boxMeasure, ?_, ?_⟩
  · have hfun : (fun x => modeVel ι W σ x l) =
        fun x => (1 / (2 * Real.pi) : ℂ) * ∫ p, modeTestIntegrand W ι σ l x p ∂boxMeasure := by
      funext x
      exact modeVel_eq_box_of hW ι σ l x
    rw [hfun]
    have hI := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := boxMeasure) (x₀ := y)
      (F := fun x p => modeTestIntegrand W ι σ l x p) (F' := fun x p => modeTestIntegrandDeriv W ι σ l x p)
      (bound := fun _ => B) Filter.univ_mem
      (Filter.Eventually.of_forall fun x => (continuous_integrand_of hW ι σ l x).aestronglyMeasurable)
      (integrable_box_of_continuous (continuous_integrand_of hW ι σ l y))
      (continuous_integrandDeriv_of hW ι σ l y).aestronglyMeasurable hbound
      (integrable_box_of_continuous continuous_const)
      (Filter.Eventually.of_forall fun p x _ => hasFDerivAt_integrand_of hW ι σ l x p)
    exact hI.const_mul _
  · intro j
    have hint := integrable_box_of_continuous (continuous_integrandDeriv_of hW ι σ l y)
    rw [smul_apply, ContinuousLinearMap.integral_apply hint, smul_eq_mul]
    unfold modeGrad
    rw [modeAverage_eq]
    congr 1
    rw [iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (gradField W (σ + τ) (axialRot φ y)
      (axialRot φ (unitVector (l, j).2))) (l, j).1 : ℝ) : ℂ))]
    · congr 1
      funext p
      simp [modeTestIntegrandDeriv, rotConj_apply, gradField]
    · refine (hint.apply_continuousLinearMap (unitVector j)).congr (Filter.Eventually.of_forall fun p => ?_)
      simp [modeTestIntegrandDeriv, rotConj_apply, gradField]

end Internal.MuSmooth

namespace Internal.MuSmooth

open ModeDerivative.Internal

theorem modeAverage_neg {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage (-ι) f b = (starRingEnd ℂ) (modeAverage ι f b) := by
  unfold modeAverage
  simp only [map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Prod.fst_neg, Prod.snd_neg,
    Int.cast_neg]
  rw [← intervalIntegral.intervalIntegral_conj]
  refine congrArg (fun t => (1 / (2 * (Real.pi : ℂ))) * t) (intervalIntegral.integral_congr fun τ _ => ?_)
  rw [← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem modeGrad_neg (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space)
    (ij : Fin 3 × Fin 3) : modeGrad (-ι) G σ y ij = (starRingEnd ℂ) (modeGrad ι G σ y ij) := by
  unfold modeGrad
  exact modeAverage_neg _ _ _

theorem phase_neg (α : ℤ × ℤ) (τ φ : ℝ) :
    Complex.exp (((2 * Real.pi * (-α).1 * τ + (-α).2 * φ : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  push_cast
  ring

theorem re_sum_sym (s : Finset (ℤ × ℤ)) (hs : ∀ α ∈ s, -α ∈ s) (z : ℤ × ℤ → ℂ)
    (hz : ∀ α, z (-α) = (starRingEnd ℂ) (z α)) :
    (((∑ α ∈ s, (z α).re : ℝ)) : ℂ) = ∑ α ∈ s, z α := by
  have hc : ∑ α ∈ s, (starRingEnd ℂ) (z α) = ∑ α ∈ s, z α :=
    Finset.sum_nbij' (fun α => -α) (fun α => -α) (fun a ha => hs a ha) (fun a ha => hs a ha)
      (fun a _ => neg_neg a) (fun a _ => neg_neg a) (fun a _ => (hz a).symm)
  push_cast
  simp_rw [Complex.re_eq_add_conj]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hc]
  ring

def cnorm3 (x : Fin 3 → ℂ) : ℝ := Real.sqrt (cnormSq x)

theorem cnorm3_eq (x : Fin 3 → ℂ) : cnorm3 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 3))‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

theorem cnorm3_nonneg (x : Fin 3 → ℂ) : 0 ≤ cnorm3 x := Real.sqrt_nonneg _

theorem cnorm3_add_le (a b : Fin 3 → ℂ) : cnorm3 (a + b) ≤ cnorm3 a + cnorm3 b := by
  rw [cnorm3_eq, cnorm3_eq, cnorm3_eq, WithLp.toLp_add]
  exact norm_add_le _ _

theorem cnorm3_zero : cnorm3 0 = 0 := by
  simp [cnorm3, cnormSq]

theorem cnorm3_sum_le {κ : Type*} (s : Finset κ) (f : κ → Fin 3 → ℂ) :
    cnorm3 (∑ k ∈ s, f k) ≤ ∑ k ∈ s, cnorm3 (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cnorm3_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (cnorm3_add_le _ _).trans (by linarith)

theorem cnorm3_le_of_sq {x : Fin 3 → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : cnormSq x ≤ c ^ 2) : cnorm3 x ≤ c := by
  unfold cnorm3
  rw [← Real.sqrt_sq hc]
  exact Real.sqrt_le_sqrt h

theorem cnorm3_sq (x : Fin 3 → ℂ) : cnorm3 x ^ 2 = cnormSq x := Real.sq_sqrt (cnorm_nonneg _)

theorem cnorm3_mat_le (g : Fin 3 × Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    cnorm3 (fun i => ∑ j : Fin 3, g (i, j) * w j) ≤ Real.sqrt (cnormSq g) * cnorm3 w := by
  refine cnorm3_le_of_sq (mul_nonneg (Real.sqrt_nonneg _) (cnorm3_nonneg _)) ?_
  rw [mul_pow, Real.sq_sqrt (cnorm_nonneg _), cnorm3_sq]
  unfold cnormSq
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖∑ j : Fin 3, g (i, j) * w j‖ ^ 2 ≤ (∑ j : Fin 3, ‖g (i, j)‖ * ‖w j‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
    _ ≤ (∑ j : Fin 3, ‖g (i, j)‖ ^ 2) * ∑ j : Fin 3, ‖w j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem space_sum_apply (c : Fin 3 → ℝ) (i : Fin 3) : (∑ j : Fin 3, c j • unitVector j) i = c i := by
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem clm_coord (A : Space →L[ℝ] Space) (c : Fin 3 → ℝ) (i : Fin 3) :
    A (∑ j : Fin 3, c j • unitVector j) i = ∑ j : Fin 3, c j * A (unitVector j) i := by
  rw [map_sum]
  simp only [map_smul, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem space_norm_sq (a : Space) : ‖a‖ ^ 2 = ∑ i : Fin 3, a i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs]

theorem cnorm3_clm_le (A : Space →L[ℝ] Space) (z : Fin 3 → ℂ) :
    cnorm3 (fun i => ∑ j : Fin 3, ((A (unitVector j) i : ℝ) : ℂ) * z j) ≤ ‖A‖ * cnorm3 z := by
  refine cnorm3_le_of_sq (mul_nonneg (norm_nonneg _) (cnorm3_nonneg _)) ?_
  set a : Space := ∑ j : Fin 3, (z j).re • unitVector j
  set b : Space := ∑ j : Fin 3, (z j).im • unitVector j
  have hpt : ∀ i, ∑ j : Fin 3, ((A (unitVector j) i : ℝ) : ℂ) * z j
      = ((A a i : ℝ) : ℂ) + ((A b i : ℝ) : ℂ) * Complex.I := by
    intro i
    rw [clm_coord, clm_coord]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← Complex.re_add_im (z j)]
    ring
  have hn : cnormSq (fun i => ∑ j : Fin 3, ((A (unitVector j) i : ℝ) : ℂ) * z j) = ‖A a‖ ^ 2 + ‖A b‖ ^ 2 := by
    unfold cnormSq
    simp_rw [hpt, space_norm_sq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hz : cnormSq z = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    unfold cnormSq
    have ha : ∀ i, a i = (z i).re := fun i => space_sum_apply (fun j => (z j).re) i
    have hb : ∀ i, b i = (z i).im := fun i => space_sum_apply (fun j => (z j).im) i
    simp_rw [space_norm_sq, ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hn, mul_pow, cnorm3_sq, hz]
  have h1 : ‖A a‖ ≤ ‖A‖ * ‖a‖ := A.le_opNorm a
  have h2 : ‖A b‖ ≤ ‖A‖ * ‖b‖ := A.le_opNorm b
  have e1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith

theorem slice_differentiable_of {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (s : ℝ) : Differentiable ℝ (W s) :=
  ((hW.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) : Differentiable ℝ (fun y => W s y))

theorem grad_expansion {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (hWp : IsTimePeriodic W) (s : Finset (ℤ × ℤ))
    (hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ s, (modeVel α W σ y i).re)
    (σ τ φ : ℝ) (y : Space) (i j : Fin 3) :
    axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i
      = (modeGrad (0, 0) (gradField W) σ y (i, j)).re
        + ∑ α ∈ s, (Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * modeGrad α (gradField W) σ y (i, j)).re := by
  have hRot := axialRotationHolds_proof
  set Rp : Space →L[ℝ] Space := ((rotIso hRot φ).toContinuousLinearEquiv : Space →L[ℝ] Space)
  set Rm : Space →L[ℝ] Space := ((rotIso hRot φ).symm.toContinuousLinearEquiv : Space →L[ℝ] Space)
  have hRp : ∀ x, Rp x = axialRot φ x := fun x => rotIso_apply hRot φ x
  have hRm : ∀ x, Rm x = axialRot (-φ) x := fun x => rotIso_symm_apply hRot φ x
  set c : ℤ × ℤ → ℂ := fun α => Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
  have hf : HasFDerivAt (fun x => axialRot (-φ) (W (σ + τ) (axialRot φ x)) i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (Rm.comp ((fderiv ℝ (W (σ + τ)) (Rp y)).comp Rp))) y := by
    have h1 : HasFDerivAt (fun x => W (σ + τ) (Rp x)) ((fderiv ℝ (W (σ + τ)) (Rp y)).comp Rp) y :=
      ((slice_differentiable_of hW (σ + τ)) (Rp y)).hasFDerivAt.comp y Rp.hasFDerivAt
    have h2 := (Rm.hasFDerivAt (x := W (σ + τ) (Rp y))).comp y h1
    have h3 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y h2
    have hfun : (fun x => axialRot (-φ) (W (σ + τ) (axialRot φ x)) i)
        = (⇑(EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ ⇑Rm ∘ fun x => W (σ + τ) (Rp x)) := by
      funext x
      simp only [Function.comp, hRp, hRm]
      rfl
    rw [hfun]
    exact h3
  choose L hL hLe using fun α => modeVel_hasFDerivAt_of hW hB α σ i y
  have hg : HasFDerivAt (fun x => (modeVel (0, 0) W σ x i).re
        + ∑ α ∈ s, (c α * modeVel α W σ x i).re)
      (Complex.reCLM.comp (L (0, 0)) + ∑ α ∈ s, Complex.reCLM.comp (c α • L α)) y := by
    refine (Complex.reCLM.hasFDerivAt.comp y (hL (0, 0))).add ?_
    refine HasFDerivAt.fun_sum fun α _ => ?_
    exact Complex.reCLM.hasFDerivAt.comp y ((hL α).const_mul (c α))
  have heq : (fun x => axialRot (-φ) (W (σ + τ) (axialRot φ x)) i)
      = fun x => (modeVel (0, 0) W σ x i).re + ∑ α ∈ s, (c α * modeVel α W σ x i).re :=
    funext fun x => rot_field_expansion hW.continuous hWp s hh σ τ φ x i
  rw [heq] at hf
  have hu := congrArg (fun T : Space →L[ℝ] ℝ => T (unitVector j)) (hf.unique hg)
  simp only [ContinuousLinearMap.comp_apply, add_apply, FunLike.coe_sum,
    Finset.sum_apply, smul_apply, Complex.reCLM_apply, smul_eq_mul, hLe] at hu
  rw [← hu]
  simp only [hRp, hRm]
  rfl

theorem meanField_fderiv_apply {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {B : ℝ} (hB : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ B) (hWp : IsTimePeriodic W) (σ : ℝ) (y : Space) (i j : Fin 3) :
    fderiv ℝ (meanField W) y (unitVector j) i = (modeGrad (0, 0) (gradField W) σ y (i, j)).re := by
  have hm : meanField W = fun x => ∑ k : Fin 3, (modeVel (0, 0) W σ x k).re • unitVector k := by
    funext x
    unfold meanField
    simp_rw [modeVel_mean_shift hWp σ x]
  choose L hL hLe using fun k => modeVel_hasFDerivAt_of hW hB (0, 0) σ k y
  have hd : HasFDerivAt (meanField W)
      (∑ k : Fin 3, (Complex.reCLM.comp (L k)).smulRight (unitVector k)) y := by
    rw [hm]
    exact HasFDerivAt.fun_sum fun k _ => (Complex.reCLM.hasFDerivAt.comp y (hL k)).smul_const (unitVector k)
  rw [hd.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.reCLM_apply, hLe]
  exact space_sum_apply (fun k => (modeGrad (0, 0) (gradField W) σ y (k, j)).re) i

theorem stretch_mode_le {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    Real.sqrt (cnormSq (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y))
      ≤ ‖fderiv ℝ (meanField W) y‖ * velAmp v ι σ y
        + ∑ α ∈ m.waves, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y := by
  obtain ⟨D, hD⟩ := hWdecay
  have hB : ∀ s x, ‖fderiv ℝ (W s) x‖ ≤ |D| := by
    intro s x
    have h := hD s x 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h
    refine h.trans ?_
    have hp : 1 ≤ (1 + ‖x‖) ^ (1 + 1) := one_le_pow₀ (by linarith [norm_nonneg x])
    calc D / (1 + ‖x‖) ^ (1 + 1) ≤ |D| / (1 + ‖x‖) ^ (1 + 1) :=
          div_le_div_of_nonneg_right (le_abs_self D) (by positivity)
      _ ≤ |D| := div_le_self (abs_nonneg D) hp
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  set g : ℤ × ℤ → Fin 3 × Fin 3 → ℂ := fun α ij => modeGrad α (gradField W) σ y ij with hgdef
  set D' : Fin 3 → Fin 3 → ℝ := fun i j => (modeGrad (0, 0) (gradField W) σ y (i, j)).re with hD'
  have hE : ∀ τ φ : ℝ, ∀ i j : Fin 3,
      ((axialRot (-φ) (fderiv ℝ (W (σ + τ)) (axialRot φ y) (axialRot φ (unitVector j))) i : ℝ) : ℂ)
        = (D' i j : ℂ) + ∑ α ∈ m.waves, Complex.exp (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
          * g α (i, j) := by
    intro τ φ i j
    rw [grad_expansion hW hB hWp m.waves hb.harmonics σ τ φ y i j, Complex.ofReal_add]
    congr 1
    refine re_sum_sym m.waves hm.waves_neg _ fun α => ?_
    rw [phase_neg, modeGrad_neg, map_mul]
  have hmp := fun i => mode_product m.waves W v hvc σ y D' g hE ι i
  set A := fderiv ℝ (meanField W) y
  have hA : ∀ i j, D' i j = A (unitVector j) i := fun i j =>
    (meanField_fderiv_apply hW hB hWp σ y i j).symm
  have hsplit : modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y
      = (fun i => ∑ j : Fin 3, ((A (unitVector j) i : ℝ) : ℂ) * modeVel ι v σ y j)
        + ∑ α ∈ m.waves, (fun i => ∑ j : Fin 3, g α (i, j) * modeVel (ι - α) v σ y j) := by
    funext i
    rw [hmp i, Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib, Finset.sum_comm (s := m.waves)]
    simp_rw [hA]
  have hc : cnorm3 (modeVel ι (fun σ y => fderiv ℝ (W σ) y (v σ y)) σ y)
      ≤ ‖A‖ * velAmp v ι σ y + ∑ α ∈ m.waves, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y := by
    rw [hsplit]
    refine (cnorm3_add_le _ _).trans (add_le_add (cnorm3_clm_le A _) ?_)
    refine (cnorm3_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    exact cnorm3_mat_le (g α) _
  exact hc

end Internal.MuSmooth

end Coercive

end Breakdown
