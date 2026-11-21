import Breakdown.CellReduction.AdjointRemainderAzimuthalSlice

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

namespace Internal

open CellCert.Reduction

variable {N : ℕ}

theorem continuous_complexComponent (c : Fin 3) : Continuous (complexComponent c) := by
  unfold complexComponent
  fin_cases c <;> simp <;> fun_prop

theorem continuous_squareSum : Continuous (fun M : Space →L[ℝ] Space => matSq M) := by
  unfold matSq
  fun_prop

theorem componentMap_norm_sq_le (c : Fin 3) (x : Space) : ‖componentMap c x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := componentMap_coords c x
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three, h0, h1, h2]
  fin_cases c <;> simp <;> nlinarith [sq_nonneg ‖x 0‖, sq_nonneg ‖x 1‖, sq_nonneg ‖x 2‖]

theorem componentMap_norm_le (c : Fin 3) (x : Space) : ‖componentMap c x‖ ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (componentMap_norm_sq_le c x)

theorem squareSum_componentMap_le (c : Fin 3) (M : Space →L[ℝ] Space) :
    matSq ((componentMap c).comp M) ≤ matSq M := by
  unfold matSq
  exact Finset.sum_le_sum fun i _ => by
    rw [ContinuousLinearMap.comp_apply]
    exact componentMap_norm_sq_le c _

theorem squareSum_nonneg_component (M : Space →L[ℝ] Space) : 0 ≤ matSq M :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem modeWeight_pos (m : ℤ) : 0 < modeWeight m := by
  unfold modeWeight
  positivity

theorem componentWeight_nonneg (c : Fin 3) : 0 ≤ componentWeight c := by
  unfold componentWeight
  split_ifs <;> norm_num

theorem slice_bound (hM : ModeInverseSquareWeakHolds) (hP : ModePairingHolds)
    (amp : Fin N → Space → ℂ) (comp : Fin N → Fin 3) (order : Fin N → ℤ) (coef : Fin N → ℂ)
    (hampm : ∀ p, AEStronglyMeasurable (amp p) volume)
    (hrot : ∀ p α y, amp p (axisRotation α y) = Complex.exp ((order p : ℂ) * (α : ℂ) * Complex.I) * amp p y)
    (hfin : ∀ p, ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖amp p y‖ ^ 2) < ⊤)
    (V r : Space → Space) (D : Space → (Space →L[ℝ] Space))
    (hV : AEStronglyMeasurable V volume) (hD : AEStronglyMeasurable D volume) (hw : IsWeakGradient V D)
    (h6 : ∫⁻ y, ENNReal.ofReal (‖V y‖ ^ 6) < ⊤) (hE : ∫⁻ y, ENNReal.ofReal (matSq (D y)) < ⊤)
    (hrep : ∀ᵐ y ∂(volume : Measure Space), ∀ c, complexComponent c (r y) =
      ∑ p ∈ Finset.univ.filter (fun p => comp p = c), coef p * amp p y) :
    Integrable (fun y => inner ℝ (V y) (r y)) volume ∧
    ENNReal.ofReal |∫ y, inner ℝ (V y) (r y)| ^ 2 ≤ (∫⁻ y, ENNReal.ofReal (matSq (D y))) *
      ∑ c : Fin 3, ∑ m ∈ orderSet comp order c, ENNReal.ofReal (componentWeight c / modeWeight m ^ 2) *
        ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖groupField amp coef comp order c m y‖ ^ 2) := by
  classical
  set u : Fin 3 → Space → ℂ := fun c y => complexComponent c (V y) with hu
  set B : Fin 3 → ℤ → Space → ℂ := fun c m => groupField amp coef comp order c m with hB
  set J : Fin 3 → ℤ → ℝ≥0∞ := fun c m => ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖B c m y‖ ^ 2) with hJ
  set EC : Fin 3 → ℝ≥0∞ := fun c => ∫⁻ y, ENNReal.ofReal (matSq ((componentMap c).comp (D y))) with hEC
  set ET : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (matSq (D y)) with hET
  have hBm : ∀ c m, AEStronglyMeasurable (B c m) volume := fun c m => group_meas amp coef comp order hampm c m
  have hBfin : ∀ c m, J c m < ⊤ := fun c m => group_finite amp coef comp order hampm hfin c m
  have hum : ∀ c, AEStronglyMeasurable (u c) volume := fun c =>
    (continuous_complexComponent c).comp_aestronglyMeasurable hV
  have hLV : ∀ c, AEStronglyMeasurable (fun y => componentMap c (V y)) volume := fun c =>
    (componentMap c).continuous.comp_aestronglyMeasurable hV
  have hLD : ∀ c, AEStronglyMeasurable (fun y => (componentMap c).comp (D y)) volume := fun c =>
    (ContinuousLinearMap.compL ℝ Space Space Space (componentMap c)).continuous.comp_aestronglyMeasurable hD
  have hLw : ∀ c, IsWeakGradient (fun y => componentMap c (V y)) (fun y => (componentMap c).comp (D y)) :=
    fun c => weakGradient_comp _ hw
  have hL6 : ∀ c, ∫⁻ y, ENNReal.ofReal (‖componentMap c (V y)‖ ^ 6) < ⊤ := fun c =>
    lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (componentMap_norm_le c _) 6)) h6
  have hLE : ∀ c, EC c ≤ ET := fun c =>
    lintegral_mono fun y => ENNReal.ofReal_le_ofReal (squareSum_componentMap_le c _)
  have hLEfin : ∀ c, EC c < ⊤ := fun c => lt_of_le_of_lt (hLE c) hE
  have hmode : ∀ c, ∑' k : ℤ, ENNReal.ofReal (modeWeight k ^ 2) * modeInverseSquare (u c) k ≤ EC c := by
    intro c
    have h := hM _ _ (hLV c) (hLD c) (hLw c) (hL6 c) (hLEfin c)
    rwa [horizontal_componentMap] at h
  have hpair : ∀ c m, ENNReal.ofReal ‖∫ y, starRingEnd ℂ (u c y) * B c m y‖ ^ 2 ≤
      modeInverseSquare (u c) m * J c m := fun c m =>
    hP (u c) (B c m) m (hum c) (hBm c m) (group_rotation amp coef comp order hrot c m)
  have hhardy : ∀ c, ∫⁻ y, ENNReal.ofReal (‖u c y‖ ^ 2 / ‖y‖ ^ 2) < ⊤ := by
    intro c
    have h := CertCell.Internal.slice_inverseSquare_lintegral (fun y => componentMap c (V y))
      (fun y => (componentMap c).comp (D y)) (hLV c) (hLD c) (hLw c) (hL6 c)
    have e : ∀ y, ‖componentMap c (V y)‖ ^ 2 = ‖u c y‖ ^ 2 := fun y => componentMap_norm_sq c (V y)
    simp only [e] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top (by simp) (hLEfin c))
  have hint : ∀ c m, Integrable (fun y => starRingEnd ℂ (u c y) * B c m y) volume := fun c m =>
    pair_integrable (hum c) (hBm c m) (hhardy c) (hBfin c m)
  have hintre : ∀ c m, Integrable (fun y => (starRingEnd ℂ (u c y) * B c m y).re) volume := fun c m => by
    simpa using Complex.reCLM.integrable_comp (hint c m)
  have hpt : ∀ᵐ y ∂(volume : Measure Space), inner ℝ (V y) (r y) = ∑ c : Fin 3, ∑ m ∈ orderSet comp order c,
      componentWeight c * (starRingEnd ℂ (u c y) * B c m y).re := by
    filter_upwards [hrep] with y hy
    rw [inner_components]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hy c, group_split, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  have hI : ∫ y, inner ℝ (V y) (r y) = ∑ c : Fin 3, ∑ m ∈ orderSet comp order c,
      componentWeight c * (∫ y, starRingEnd ℂ (u c y) * B c m y).re := by
    rw [integral_congr_ae hpt, integral_finsetSum _ (fun c _ =>
      integrable_finsetSum _ fun m _ => (hintre c m).const_mul _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ (fun m _ => (hintre c m).const_mul _)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul]
    congr 1
    have h := Complex.reCLM.integral_comp_comm (hint c m)
    simpa using h
  set X : Fin 3 → ℤ → ℝ := fun c m => ‖∫ y, starRingEnd ℂ (u c y) * B c m y‖ with hX
  have hmi : ∀ c m, modeInverseSquare (u c) m < ⊤ := by
    intro c m
    have h1 : ENNReal.ofReal (modeWeight m ^ 2) * modeInverseSquare (u c) m ≤ EC c :=
      (ENNReal.le_tsum m).trans (hmode c)
    have h2 : ENNReal.ofReal (modeWeight m ^ 2) * modeInverseSquare (u c) m ≠ ⊤ :=
      (lt_of_le_of_lt h1 (hLEfin c)).ne
    have h3 : ENNReal.ofReal (modeWeight m ^ 2) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (pow_pos (modeWeight_pos m) 2)).ne'
    exact ENNReal.lt_top_of_mul_ne_top_right h2 h3
  have hXle : ∀ c m, X c m ^ 2 ≤ (modeInverseSquare (u c) m).toReal * (J c m).toReal := by
    intro c m
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (hmi c m).ne (hBfin c m).ne) (hpair c m)
    rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul] at h
  have hMsum : ∀ c, ∑ m ∈ orderSet comp order c, modeWeight m ^ 2 * (modeInverseSquare (u c) m).toReal ≤
      (EC c).toReal := by
    intro c
    have h1 : ∑ m ∈ orderSet comp order c, ENNReal.ofReal (modeWeight m ^ 2) * modeInverseSquare (u c) m ≤ EC c :=
      (ENNReal.sum_le_tsum _).trans (hmode c)
    have h2 := ENNReal.toReal_mono (hLEfin c).ne h1
    rw [ENNReal.toReal_sum (fun m _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmi c m).ne)] at h2
    refine le_trans (le_of_eq ?_) h2
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hEsum : ∑ c : Fin 3, componentWeight c * (EC c).toReal = ET.toReal := by
    have hmeas : ∀ c, AEMeasurable (fun y => ENNReal.ofReal (matSq ((componentMap c).comp (D y)))) volume :=
      fun c => (continuous_squareSum.comp_aestronglyMeasurable (hLD c)).aemeasurable.ennreal_ofReal
    have h1 : ET = ∑ c : Fin 3, ENNReal.ofReal (componentWeight c) * EC c := by
      rw [hET]
      have e : ∀ y, ENNReal.ofReal (matSq (D y)) = ∑ c : Fin 3, ENNReal.ofReal (componentWeight c) *
          ENNReal.ofReal (matSq ((componentMap c).comp (D y))) := by
        intro y
        rw [← weighted_squareSum (D y), ENNReal.ofReal_sum_of_nonneg (fun c _ =>
          mul_nonneg (componentWeight_nonneg c) (squareSum_nonneg_component _))]
        exact Finset.sum_congr rfl fun c _ => ENNReal.ofReal_mul (componentWeight_nonneg c)
      simp_rw [e]
      rw [lintegral_finsetSum' _ fun c _ => (hmeas c).const_mul _]
      exact Finset.sum_congr rfl fun c _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [h1, ENNReal.toReal_sum (fun c _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hLEfin c).ne)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (componentWeight_nonneg c)]
  set S : ℝ≥0∞ := ∑ c : Fin 3, ∑ m ∈ orderSet comp order c,
    ENNReal.ofReal (componentWeight c / modeWeight m ^ 2) * J c m with hS
  have hSreal : S.toReal = ∑ c : Fin 3, ∑ m ∈ orderSet comp order c,
      componentWeight c / modeWeight m ^ 2 * (J c m).toReal := by
    rw [hS, ENNReal.toReal_sum (fun c _ => ENNReal.sum_ne_top.2 fun m _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hBfin c m).ne)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ENNReal.toReal_sum (fun m _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hBfin c m).ne)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (div_nonneg (componentWeight_nonneg c) (sq_nonneg _))]
  have habs : |∫ y, inner ℝ (V y) (r y)| ≤ ∑ c : Fin 3, ∑ m ∈ orderSet comp order c, componentWeight c * X c m := by
    rw [hI]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul, abs_of_nonneg (componentWeight_nonneg c)]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (componentWeight_nonneg c)
  set s : Finset (Σ _ : Fin 3, ℤ) := Finset.univ.sigma (orderSet comp order) with hs
  have hCS := sq_sum_le_of_sq_le_mul s (fun i => componentWeight i.1 * X i.1 i.2)
    (fun i => componentWeight i.1 * (modeWeight i.2 ^ 2 * (modeInverseSquare (u i.1) i.2).toReal))
    (fun i => componentWeight i.1 / modeWeight i.2 ^ 2 * (J i.1 i.2).toReal)
    (fun i _ => mul_nonneg (componentWeight_nonneg _) (norm_nonneg _))
    (fun i _ => mul_nonneg (componentWeight_nonneg _) (mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg))
    (fun i _ => mul_nonneg (div_nonneg (componentWeight_nonneg _) (sq_nonneg _)) ENNReal.toReal_nonneg)
    (fun i _ => by
      have hw1 : modeWeight i.2 ≠ 0 := (modeWeight_pos i.2).ne'
      have e : componentWeight i.1 * (modeWeight i.2 ^ 2 * (modeInverseSquare (u i.1) i.2).toReal) *
          (componentWeight i.1 / modeWeight i.2 ^ 2 * (J i.1 i.2).toReal) =
          componentWeight i.1 ^ 2 * ((modeInverseSquare (u i.1) i.2).toReal * (J i.1 i.2).toReal) := by
        field_simp
      rw [e, mul_pow]
      exact mul_le_mul_of_nonneg_left (hXle i.1 i.2) (sq_nonneg _))
  simp only [hs, Finset.sum_sigma] at hCS
  have hA : ∑ c : Fin 3, ∑ m ∈ orderSet comp order c,
      componentWeight c * (modeWeight m ^ 2 * (modeInverseSquare (u c) m).toReal) ≤ ET.toReal := by
    rw [← hEsum]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hMsum c) (componentWeight_nonneg c)
  have hfinal : |∫ y, inner ℝ (V y) (r y)| ^ 2 ≤ ET.toReal * S.toReal := by
    rw [hSreal]
    refine (pow_le_pow_left₀ (abs_nonneg _) habs 2).trans (hCS.trans ?_)
    exact mul_le_mul_of_nonneg_right hA (Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun m _ =>
      mul_nonneg (div_nonneg (componentWeight_nonneg c) (sq_nonneg _)) ENNReal.toReal_nonneg)
  have hintI : Integrable (fun y => inner ℝ (V y) (r y)) volume :=
    (integrable_congr hpt).2 (integrable_finsetSum _ fun c _ =>
      integrable_finsetSum _ fun m _ => (hintre c m).const_mul _)
  refine ⟨hintI, ?_⟩
  rw [← ENNReal.ofReal_pow (abs_nonneg _)]
  refine (ENNReal.ofReal_le_ofReal hfinal).trans ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact mul_le_mul' ENNReal.ofReal_toReal_le ENNReal.ofReal_toReal_le

end Internal

end AzimuthalParts

end AdjointDefect

end Breakdown
