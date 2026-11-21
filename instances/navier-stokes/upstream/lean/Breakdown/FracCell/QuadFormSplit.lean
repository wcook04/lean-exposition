import Breakdown.FracCell.StAssembly
import Breakdown.FracCell.ModelPin

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace FracInternal

namespace QuadFormSplit

open SteadyCert CellCert CellCert.Assembly CellCert.Finite

theorem norm_sq_coord (u : Space) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three, sq_abs]

theorem coord_abs_le (u : Space) (i : Fin 3) : |u i| ≤ ‖u‖ := by
  have h2 : u i ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq_coord]
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
  have h3 := sq_le_sq.mp h2
  rwa [abs_norm] at h3

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem entry_abs_le (E : Space →L[ℝ] Space) (a b : Fin 3) : |entry E a b| ≤ ‖E‖ := by
  unfold entry
  refine (coord_abs_le _ _).trans ?_
  have h := E.le_opNorm (unitVector b)
  rwa [unit_norm, mul_one] at h

theorem entrySq_nonneg (D : Space →L[ℝ] Space) : 0 ≤ entrySq D :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem col_sq_le (D : Space →L[ℝ] Space) (l : Fin 3) : ‖D (unitVector l)‖ ^ 2 ≤ entrySq D :=
  Finset.single_le_sum (f := fun j => ‖D (unitVector j)‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ l)

theorem sign_abs_le (i j l : Fin 3) : |permSign i j l| ≤ 1 := by
  unfold permSign
  split_ifs <;> simp

theorem row_term_le (E : Space →L[ℝ] Space) (v : Space) (i l : Fin 3) :
    |-(∑ j : Fin 3, permSign i l j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3, permSign i j q * v q * entry E l j|
      ≤ 8 * (‖E‖ * ‖v‖) := by
  have hEv : ‖E v‖ ≤ ‖E‖ * ‖v‖ := E.le_opNorm v
  have hn := mul_nonneg (norm_nonneg E) (norm_nonneg v)
  have t1 : ∀ j : Fin 3, |permSign i l j * (E v) j| ≤ ‖E‖ * ‖v‖ := by
    intro j
    rw [abs_mul]
    have a := coord_abs_le (E v) j
    have b := sign_abs_le i l j
    have c0 := abs_nonneg (permSign i l j)
    have c1 := abs_nonneg ((E v) j)
    nlinarith
  have h1 : |∑ j : Fin 3, permSign i l j * (E v) j| ≤ 3 * (‖E‖ * ‖v‖) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin 3, |permSign i l j * (E v) j| ≤ ∑ _j : Fin 3, ‖E‖ * ‖v‖ := Finset.sum_le_sum fun j _ => t1 j
      _ = 3 * (‖E‖ * ‖v‖) := by simp
  have t2 : ∀ j q : Fin 3, |permSign i j q * v q * entry E l j| ≤ ‖E‖ * ‖v‖ := by
    intro j q
    rw [abs_mul, abs_mul]
    have a := coord_abs_le v q
    have b := sign_abs_le i j q
    have c := entry_abs_le E l j
    have c0 := abs_nonneg (permSign i j q)
    have c1 := abs_nonneg (v q)
    have c2 := abs_nonneg (entry E l j)
    calc |permSign i j q| * |v q| * |entry E l j| ≤ 1 * ‖v‖ * ‖E‖ := by gcongr
      _ = ‖E‖ * ‖v‖ := by ring
  have h2 : |∑ j : Fin 3, ∑ q : Fin 3, permSign i j q * v q * entry E l j| ≤ 9 * (‖E‖ * ‖v‖) := by
    calc _ ≤ ∑ j : Fin 3, |∑ q : Fin 3, permSign i j q * v q * entry E l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3, ∑ q : Fin 3, |permSign i j q * v q * entry E l j| :=
          Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, ∑ _q : Fin 3, ‖E‖ * ‖v‖ :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun q _ => t2 j q
      _ = 9 * (‖E‖ * ‖v‖) := by simp; ring
  calc _ ≤ |-(∑ j : Fin 3, permSign i l j * (E v) j)|
        + |(1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3, permSign i j q * v q * entry E l j| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith

theorem part_abs_le (E D : Space →L[ℝ] Space) (v : Space) :
    |∑ i : Fin 3, ∑ l : Fin 3,
      (-(∑ j : Fin 3, permSign i l j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3, permSign i j q * v q * entry E l j)
        * entry D i l| ≤ 36 * ((‖E‖ * ‖v‖) ^ 2 + entrySq D) := by
  have hn := mul_nonneg (norm_nonneg E) (norm_nonneg v)
  have t : ∀ i l : Fin 3, |(-(∑ j : Fin 3, permSign i l j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3,
      permSign i j q * v q * entry E l j) * entry D i l| ≤ 4 * (‖E‖ * ‖v‖) ^ 2 + 4 * ‖D (unitVector l)‖ ^ 2 := by
    intro i l
    rw [abs_mul]
    have a := row_term_le E v i l
    have b : |entry D i l| ≤ ‖D (unitVector l)‖ := coord_abs_le _ _
    have b0 := abs_nonneg (entry D i l)
    have a0 := abs_nonneg (-(∑ j : Fin 3, permSign i l j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3,
      permSign i j q * v q * entry E l j)
    nlinarith [sq_nonneg (‖E‖ * ‖v‖ - ‖D (unitVector l)‖), norm_nonneg (D (unitVector l)),
      mul_le_mul a b b0 (by positivity)]
  calc _ ≤ ∑ i : Fin 3, |∑ l : Fin 3, (-(∑ j : Fin 3, permSign i l j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3,
      permSign i j q * v q * entry E l j) * entry D i l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ l : Fin 3, |(-(∑ j : Fin 3, permSign i l j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3,
      permSign i j q * v q * entry E l j) * entry D i l| := Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ∑ l : Fin 3, (4 * (‖E‖ * ‖v‖) ^ 2 + 4 * ‖D (unitVector l)‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => t i l
    _ = 36 * (‖E‖ * ‖v‖) ^ 2 + 12 * entrySq D := by
      simp only [entrySq, Fin.sum_univ_three]; ring
    _ ≤ _ := by nlinarith [entrySq_nonneg D]

theorem entrySq_coords (D : Space →L[ℝ] Space) : entrySq D = ∑ i : Fin 3, ∑ l : Fin 3, entry D i l ^ 2 := by
  simp only [entrySq, norm_sq_coord, entry, Fin.sum_univ_three]
  ring

theorem curl_sq_le (M : Space →L[ℝ] Space) : ‖curlOf M‖ ^ 2 ≤ 2 * entrySq M := by
  rw [entrySq_coords, norm_sq_coord]
  simp [curlOf, Fin.sum_univ_three, permSign, unitVector]
  nlinarith [sq_nonneg (entry M 2 1 + entry M 1 2), sq_nonneg (entry M 0 2 + entry M 2 0),
    sq_nonneg (entry M 1 0 + entry M 0 1), sq_nonneg (entry M 0 0), sq_nonneg (entry M 1 1), sq_nonneg (entry M 2 2)]

theorem sign_sum_sq_le (z : Fin 3 → Fin 3 → ℝ) :
    ∑ i : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * z j l) ^ 2 ≤ 2 * ∑ j : Fin 3, ∑ l : Fin 3, z j l ^ 2 := by
  simp [Fin.sum_univ_three, permSign]
  nlinarith [sq_nonneg (z 1 2 + z 2 1), sq_nonneg (z 2 0 + z 0 2), sq_nonneg (z 0 1 + z 1 0),
    sq_nonneg (z 0 0), sq_nonneg (z 1 1), sq_nonneg (z 2 2)]

theorem curlGradSq_le (H : Space →L[ℝ] Space →L[ℝ] Space) : curlGradSq H ≤ 2 * CellCert.fullSecondSq H := by
  unfold curlGradSq CellCert.fullSecondSq
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have h := sign_sum_sq_le (fun j l => H (unitVector a) (unitVector j) l)
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_sq_coord, Fin.sum_univ_three]

theorem curlGradSq_nonneg (H : Space →L[ℝ] Space →L[ℝ] Space) : 0 ≤ curlGradSq H :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_curlOf : Continuous curlOf := by
  unfold curlOf entry
  fun_prop

theorem continuous_curlGradSq : Continuous curlGradSq := by
  unfold curlGradSq
  fun_prop

theorem continuous_jForm :
    Continuous fun q : (Space →L[ℝ] Space) × (Space →L[ℝ] Space) × (Space →L[ℝ] Space) × Space =>
      jForm q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  unfold jForm curlOf entry
  fun_prop

theorem curlGradMatrix_add (H H' : Space →L[ℝ] Space →L[ℝ] Space) :
    curlGradMatrix (H + H') = curlGradMatrix H + curlGradMatrix H' := by
  unfold curlGradMatrix
  simp only [_root_.add_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib, add_smul]

theorem curlGradMatrix_smul (r : ℝ) (H : Space →L[ℝ] Space →L[ℝ] Space) :
    curlGradMatrix (r • H) = r • curlGradMatrix H := by
  unfold curlGradMatrix
  simp only [_root_.smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem curlGradMatrix_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ H, ‖curlGradMatrix H‖ ≤ L * ‖H‖ := by
  let Lm : (Space →L[ℝ] Space →L[ℝ] Space) →ₗ[ℝ] (Space →L[ℝ] Space) :=
    { toFun := curlGradMatrix, map_add' := curlGradMatrix_add, map_smul' := curlGradMatrix_smul }
  refine ⟨‖LinearMap.toContinuousLinearMap Lm‖, norm_nonneg _, fun H => ?_⟩
  have h := (LinearMap.toContinuousLinearMap Lm).le_opNorm H
  simpa [Lm] using h


theorem weight_abs_le {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c) (y : Space) :
    |c.weight y| ≤ c.weightMax := by
  have h1 := hc.base.weight_lower y
  have h2 := hc.base.weight_upper y
  have h0 := hc.base.weightMin_pos
  rw [abs_of_pos (by linarith)]
  exact h2

theorem strain_bound {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖c.modelStrain y‖ ≤ B := by
  obtain ⟨C, hC⟩ := hc.model_bounded
  obtain ⟨Cc, hCc⟩ := hc.centre_bounds
  refine ⟨|C| + |Cc|, by positivity, fun y => ?_⟩
  by_cases hy : y ∈ c.cellRegion
  · have := (hC y hy).2.2.1
    have := le_abs_self C
    have := abs_nonneg Cc
    linarith
  · rw [(hc.model_outside y hy).1]
    have hg := (hCc y).2.1
    have hr : (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
    have hr0 : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by linarith [norm_nonneg y]) _
    have hs : ‖FracCellData.centreStrain c y‖ ≤ ‖c.centreGrad y‖ := by
      unfold FracCellData.centreStrain symPart
      rw [norm_smul]
      have ha : ‖ContinuousLinearMap.adjoint (c.centreGrad y)‖ = ‖c.centreGrad y‖ :=
        LinearIsometryEquiv.norm_map _ _
      have := norm_add_le (c.centreGrad y) (ContinuousLinearMap.adjoint (c.centreGrad y))
      rw [ha] at this
      have h12 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
      rw [h12]
      linarith
    have := le_abs_self Cc
    have := abs_nonneg C
    have := abs_nonneg Cc
    have : Cc * (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ |Cc| := by nlinarith
    linarith

theorem decay_bound {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖c.modelCurlGrad y‖ ≤ B * ((1 + ‖y‖) ^ 3)⁻¹ := by
  obtain ⟨C, hC⟩ := hc.model_bounded
  obtain ⟨Cc, hCc⟩ := hc.centre_bounds
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hc.cellRegion_bounded
  obtain ⟨L, hL0, hL⟩ := curlGradMatrix_bound
  refine ⟨|C| * (1 + |R|) ^ 3 + L * |Cc|, by positivity, fun y => ?_⟩
  have hp : 0 < (1 + ‖y‖) ^ 3 := by positivity
  have hu : 0 ≤ ((1 + ‖y‖) ^ 3)⁻¹ := inv_nonneg.mpr hp.le
  have hu1 : ((1 + ‖y‖) ^ 3)⁻¹ * (1 + ‖y‖) ^ 3 = 1 := inv_mul_cancel₀ hp.ne'
  by_cases hy : y ∈ c.cellRegion
  · have h1 := (hC y hy).2.2.2
    have hyR : ‖y‖ ≤ |R| := (hR y hy).trans (le_abs_self R)
    have hpow : (1 + ‖y‖) ^ 3 ≤ (1 + |R|) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    have h2 : 1 ≤ (1 + |R|) ^ 3 * ((1 + ‖y‖) ^ 3)⁻¹ := by nlinarith
    have h3 : C ≤ |C| * ((1 + |R|) ^ 3 * ((1 + ‖y‖) ^ 3)⁻¹) := by
      have := le_abs_self C
      have := abs_nonneg C
      nlinarith
    have h4 : 0 ≤ L * |Cc| * ((1 + ‖y‖) ^ 3)⁻¹ := by positivity
    nlinarith
  · rw [(hc.model_outside y hy).2]
    unfold FracCellData.centreCurlGrad
    have h1 := hL (c.centreSecond y)
    have h2 := (hCc y).2.2
    have he : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      norm_cast
    rw [he] at h2
    have h3 : Cc * ((1 + ‖y‖) ^ 3)⁻¹ ≤ |Cc| * ((1 + ‖y‖) ^ 3)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_abs_self Cc) hu
    have h4 : 0 ≤ |C| * (1 + |R|) ^ 3 * ((1 + ‖y‖) ^ 3)⁻¹ := by positivity
    have h5 : L * ‖c.centreSecond y‖ ≤ L * (|Cc| * ((1 + ‖y‖) ^ 3)⁻¹) :=
      mul_le_mul_of_nonneg_left (h2.trans h3) hL0
    nlinarith

theorem cubic_mean_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : s ^ 2 * t ≤ s ^ 3 + t ^ 3 := by
  rcases le_total s t with h | h
  · have : s ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs h 2
    nlinarith [pow_nonneg hs 3]
  · have : s ^ 2 * t ≤ s ^ 2 * s := mul_le_mul_of_nonneg_left h (sq_nonneg s)
    nlinarith [pow_nonneg ht 3]

theorem decay_sq_integrable {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField c.order v G H) :
    Integrable (fun y => (‖c.modelCurlGrad y‖ * ‖v y‖) ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := decay_bound hc
  have hi9 : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(9 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  have hi6 : Integrable (fun y => ‖v y‖ ^ 6) := by
    have h := hs.velocity_six.integrable_norm_rpow (by norm_num) (by norm_num)
    refine h.congr (ae_of_all _ fun y => ?_)
    simp only
    rw [show ((6 : ℝ≥0∞).toReal) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hm : AEStronglyMeasurable (fun y => (‖c.modelCurlGrad y‖ * ‖v y‖) ^ 2) volume :=
    ((hc.model_measurable.2.2.2.norm).mul hs.measurable_velocity.norm).pow 2
  refine Integrable.mono' ((hi9.add hi6).const_mul (B ^ 2)) hm (ae_of_all _ fun y => ?_)
  have hp : 0 < (1 + ‖y‖) ^ 3 := by positivity
  set w := ((1 + ‖y‖) ^ 3)⁻¹ with hw
  have hw0 : 0 ≤ w := inv_nonneg.mpr hp.le
  have h9 : (1 + ‖y‖) ^ (-(9 : ℝ)) = w ^ 3 := by
    rw [Real.rpow_neg (by positivity), hw, inv_pow, ← pow_mul]
    norm_cast
  have hb := hB y
  have hn := norm_nonneg (c.modelCurlGrad y)
  have hv := norm_nonneg (v y)
  have hy := cubic_mean_le hw0 (sq_nonneg ‖v y‖)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show _ ≤ B ^ 2 * ((1 + ‖y‖) ^ (-(9 : ℝ)) + ‖v y‖ ^ 6)
  rw [h9]
  have e1 : (‖c.modelCurlGrad y‖ * ‖v y‖) ^ 2 ≤ (B * w * ‖v y‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hb hv) 2
  have e2 : (B * w * ‖v y‖) ^ 2 = B ^ 2 * (w ^ 2 * ‖v y‖ ^ 2) := by ring
  have e3 : (‖v y‖ ^ 2) ^ 3 = ‖v y‖ ^ 6 := by ring
  rw [e3] at hy
  nlinarith [sq_nonneg B]


theorem density_parts {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c) {x : FieldTuple k}
    (hx : IsAdmissible c x) :
    Integrable (fun y => CellSplit.localDensity c α x y) ∧
      ∫ y, CellSplit.localDensity c α x y =
        c.formOf α x.1 x.2.1 x.2.2.1 x.2.2.2.1 - c.coercivity * weightedEnergy c.weight x.2.1 x.2.2.1 := by
  obtain ⟨v, G, H, κ, Q⟩ := x
  have hs : IsSecondOrderField c.order v G H := hx.1
  have hG2 : Integrable (fun y => entrySq (G y)) := hs.gradient_two
  have i1 : Integrable (fun y => CellCert.fullSecondSq (H y)) := hs.second_two
  have i2 : Integrable (fun y => curlGradSq (H y)) := by
    refine Integrable.mono' (i1.const_mul 2)
      (continuous_curlGradSq.comp_aestronglyMeasurable hs.measurable_second) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (curlGradSq_nonneg _)]
    exact curlGradSq_le _
  have i3a : Integrable (fun y => ‖curlOf (G y)‖ ^ 2) := by
    refine Integrable.mono' (hG2.const_mul 2)
      ((continuous_curlOf.comp_aestronglyMeasurable hs.measurable_gradient).norm.pow 2) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact curl_sq_le _
  have i3b : Integrable (fun y => (c.curlWeight - c.coercivity * c.weight y) * entrySq (G y)) := by
    have hm : AEStronglyMeasurable (fun y => (c.curlWeight - c.coercivity * c.weight y) * entrySq (G y)) volume :=
      ((aestronglyMeasurable_const.sub (aestronglyMeasurable_const.mul
        hc.base.weight_measurable.aestronglyMeasurable)).mul hG2.aestronglyMeasurable)
    refine Integrable.mono' (hG2.const_mul (|c.curlWeight| + |c.coercivity| * c.weightMax)) hm
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (entrySq_nonneg _)]
    refine mul_le_mul_of_nonneg_right ?_ (entrySq_nonneg _)
    calc |c.curlWeight - c.coercivity * c.weight y| ≤ |c.curlWeight| + |c.coercivity * c.weight y| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul]
        have := weight_abs_le hc y
        have := abs_nonneg c.coercivity
        nlinarith
  have i3 : Integrable (fun y => (1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G y)‖ ^ 2
      + (c.curlWeight - c.coercivity * c.weight y) * entrySq (G y)) := (i3a.const_mul _).add i3b
  have i4 : Integrable (fun y => jForm (c.modelStrain y) (c.modelCurlGrad y) (G y) (v y)) := by
    obtain ⟨B, hB0, hB⟩ := strain_bound hc
    have hd := decay_sq_integrable hc hs
    have hprod : AEStronglyMeasurable (fun y => (c.modelStrain y, c.modelCurlGrad y, G y, v y)) volume :=
      hc.model_measurable.2.2.1.prodMk
        (hc.model_measurable.2.2.2.prodMk (hs.measurable_gradient.prodMk hs.measurable_velocity))
    have hm : AEStronglyMeasurable (fun y => jForm (c.modelStrain y) (c.modelCurlGrad y) (G y) (v y)) volume := by
      have h := continuous_jForm.comp_aestronglyMeasurable hprod
      exact h
    refine Integrable.mono' ((hG2.const_mul (2 * B + 36)).add (hd.const_mul 36)) hm (ae_of_all _ fun y => ?_)
    have hp := part_abs_le (c.modelCurlGrad y) (G y) (v y)
    have hc1 : |inner ℝ (curlOf (G y)) (c.modelStrain y (curlOf (G y)))| ≤ B * (2 * entrySq (G y)) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have h1 := (c.modelStrain y).le_opNorm (curlOf (G y))
      have h2 := curl_sq_le (G y)
      have h3 := hB y
      have h4 := norm_nonneg (curlOf (G y))
      have h5 : ‖curlOf (G y)‖ * ‖c.modelStrain y (curlOf (G y))‖ ≤ B * ‖curlOf (G y)‖ ^ 2 := by
        calc _ ≤ ‖curlOf (G y)‖ * (‖c.modelStrain y‖ * ‖curlOf (G y)‖) := mul_le_mul_of_nonneg_left h1 h4
          _ ≤ ‖curlOf (G y)‖ * (B * ‖curlOf (G y)‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h4) h4
          _ = B * ‖curlOf (G y)‖ ^ 2 := by ring
      nlinarith
    show ‖jForm (c.modelStrain y) (c.modelCurlGrad y) (G y) (v y)‖ ≤
      (2 * B + 36) * entrySq (G y) + 36 * (‖c.modelCurlGrad y‖ * ‖v y‖) ^ 2
    rw [Real.norm_eq_abs]
    unfold jForm
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith
  have i5 : Integrable (fun y => ∑ i, κ i * entryInner (G y) (c.modelActuatorGrad i y)) :=
    integrable_finsetSum _ fun i _ => (ModelPinInternal.integrable_entryInner hs.measurable_gradient
      (hc.modelActuatorGrad_data i).1 hG2 (hc.modelActuatorGrad_data i).2.1).const_mul _
  have hall : Integrable (fun y => CellSplit.localDensity c α (v, G, H, κ, Q) y) :=
    ((((i1.const_mul _).add (i2.const_mul _)).add i3).add i4).add i5
  refine ⟨hall, ?_⟩
  unfold CellSplit.localDensity FracCellData.formOf
  dsimp only
  have j2 : Integrable (fun y => (c.innerWeight - c.coercivity) * CellCert.fullSecondSq (H y)
      + (c.splitVisc - c.innerWeight) * curlGradSq (H y)) := (i1.const_mul _).add (i2.const_mul _)
  have j3 : Integrable (fun y => (c.innerWeight - c.coercivity) * CellCert.fullSecondSq (H y)
      + (c.splitVisc - c.innerWeight) * curlGradSq (H y) + ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G y)‖ ^ 2
      + (c.curlWeight - c.coercivity * c.weight y) * entrySq (G y))) := j2.add i3
  have j4 : Integrable (fun y => (c.innerWeight - c.coercivity) * CellCert.fullSecondSq (H y)
      + (c.splitVisc - c.innerWeight) * curlGradSq (H y) + ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G y)‖ ^ 2
      + (c.curlWeight - c.coercivity * c.weight y) * entrySq (G y))
      + jForm (c.modelStrain y) (c.modelCurlGrad y) (G y) (v y)) := j3.add i4
  rw [integral_add j4 i5, integral_add j3 i4, integral_add j2 i3,
    integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => (ModelPinInternal.integrable_entryInner hs.measurable_gradient
      (hc.modelActuatorGrad_data i).1 hG2 (hc.modelActuatorGrad_data i).2.1).const_mul _)]
  simp only [integral_const_mul]
  ring

theorem cell_split {α : ℝ} {k N : ℕ} {c : FracCellData k N} {S : CellSplit k N} (hS : S.IsCellSplit c α)
    {f : Space → ℝ} (hf : Integrable f) :
    (∑ K, ∫ y in S.cell K, f y) + ∫ y in (⋃ K, S.cell K)ᶜ, f y = ∫ y, f y := by
  have hU : MeasurableSet (⋃ K, S.cell K) := MeasurableSet.iUnion hS.cell_measurable
  rw [← integral_add_compl hU hf, integral_iUnion_ae (fun K => (hS.cell_measurable K).nullMeasurableSet)
    (fun K L hKL => hS.cells_apart K L hKL) hf.integrableOn, tsum_fintype]

theorem cell_sum {α : ℝ} {k N : ℕ} {c : FracCellData k N} {S : CellSplit k N} (hS : S.IsCellSplit c α)
    {f : Space → ℝ} (hf : Integrable f) (h0 : ∀ y ∉ c.cellRegion, f y = 0) :
    ∑ K, ∫ y in S.cell K, f y = ∫ y, f y := by
  have h := cell_split hS hf
  have hz : ∫ y in (⋃ K, S.cell K)ᶜ, f y = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => h0 y ?_
    rw [← hS.cells_cover]
    exact hy
  linarith

theorem rows_split {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c) (S : CellSplit k N)
    (F : Space → Space) :
    ∑ K, ∑ a ∈ Finset.univ.filter (fun a => S.rowCell a = K), c.rowWeight a * l2Pair F (c.row a) ^ 2
      = c.toFracCertData.rows F ^ 2 := by
  rw [Finset.sum_fiberwise]
  unfold FracCertData.rows rowSize
  rw [Real.sq_sqrt (Finset.sum_nonneg fun a _ => mul_nonneg (hc.base.rowWeight_pos a).le (sq_nonneg _))]

theorem global_value {α : ℝ} {k N : ℕ} {c : FracCellData k N} {S : CellSplit k N} (hS : S.IsCellSplit c α)
    {x : FieldTuple k} (hx : IsAdmissible c x) (ζ : Fin k → ℝ) :
    quadValue (S.globalMatrix c) (S.stateOf x ζ) =
      -(c.coercivity * c.multiplierScale ^ 2) * ∑ i, x.2.2.2.1 i ^ 2 - ∑ i, ζ i ^ 2 / c.pinWeight := by
  unfold quadValue CellSplit.globalMatrix CellSplit.stateOf
  simp only [dotProduct, Matrix.mulVec_diagonal, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have h1 : ∀ j, (S.moment x j + (S.freeMap *ᵥ ζ) j) *
      ((if ∃ i, S.kappaSlot i = j then -(c.coercivity * c.multiplierScale ^ 2) else 0) *
        (S.moment x j + (S.freeMap *ᵥ ζ) j)) =
      if j ∈ Finset.univ.image S.kappaSlot then
        -(c.coercivity * c.multiplierScale ^ 2) * (S.moment x j + (S.freeMap *ᵥ ζ) j) ^ 2 else 0 := by
    intro j
    by_cases h : ∃ i, S.kappaSlot i = j
    · rw [if_pos h, if_pos (by simpa using h)]
      ring
    · rw [if_neg h, if_neg (by simpa using h)]
      ring
  simp only [Pi.add_apply] at h1 ⊢
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_image fun a _ b _ h => hS.kappa_slot_injective h]
  have h2 : ∀ i, S.moment x (S.kappaSlot i) + (S.freeMap *ᵥ ζ) (S.kappaSlot i) = x.2.2.2.1 i := by
    intro i
    rw [hS.kappa_slot_value x hx i]
    simp [Matrix.mulVec, dotProduct, hS.kappa_slot_free]
  simp only [h2]
  rw [← Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


end QuadFormSplit

end FracInternal

namespace CellCert

namespace Assembly

open SteadyCert _root_.Breakdown.CellCert.Finite FracInternal.QuadFormSplit

theorem quadFormSplit : QuadFormSplitStatement := by
  intro α _ _ k N c hc S hS x hx ζ
  obtain ⟨hf, hfe⟩ := density_parts hc hx
  have hsplit := cell_split hS hf
  have hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1 := hx.1
  have hpin : ∀ i, ∑ K, ∫ y in S.cell K, entryInner (x.2.1 y) (c.modelPinField i y) = c.pinOf x.2.1 i := by
    intro i
    refine cell_sum hS (ModelPinInternal.integrable_entryInner hs.measurable_gradient (hc.modelPin_data i).1
      hs.gradient_two (hc.modelPin_data i).2.1) fun y hy => ?_
    rw [(hc.modelPin_data i).2.2 y hy]
    simp [entryInner]
  have hrows := rows_split hc S (fun y => c.modelFieldOf α x.1 x.2.1 x.2.2.1 x.2.2.2.1 y + x.2.2.2.2 y)
  have hglob := global_value hS hx ζ
  have hsum : ∑ K, S.cellPart c α K x ζ = (∑ K, ∫ y in S.cell K, CellSplit.localDensity c α x y)
      + c.toFracCertData.rows (fun y => c.modelFieldOf α x.1 x.2.1 x.2.2.1 x.2.2.2.1 y + x.2.2.2.2 y) ^ 2
      + ∑ i, 2 * ζ i * c.pinOf x.2.1 i := by
    unfold CellSplit.cellPart
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hrows, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hpin i]
  have ht := hc.base.pinWeight_pos
  have hpinq : ∀ i, 2 * ζ i * c.pinOf x.2.1 i - ζ i ^ 2 / c.pinWeight ≤ c.pinWeight * c.pinOf x.2.1 i ^ 2 := by
    intro i
    have e : c.pinWeight * c.pinOf x.2.1 i ^ 2 - (2 * ζ i * c.pinOf x.2.1 i - ζ i ^ 2 / c.pinWeight)
        = c.pinWeight * (c.pinOf x.2.1 i - ζ i / c.pinWeight) ^ 2 := by
      field_simp
      ring
    have : 0 ≤ c.pinWeight * (c.pinOf x.2.1 i - ζ i / c.pinWeight) ^ 2 := by positivity
    linarith
  have hq := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpinq i
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hq
  unfold CellSplit.exteriorPart FracCellData.quadForm
  rw [hsum, hglob]
  linarith

end Assembly

end CellCert

end Breakdown
