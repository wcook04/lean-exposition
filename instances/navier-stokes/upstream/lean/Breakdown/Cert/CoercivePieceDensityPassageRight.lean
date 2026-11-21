import Breakdown.Cert.CoercivePieceDensityPassageLimit
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PassageLimit

theorem rightSideLimit_memL2 {k : ℕ} {Γ : Set Symmetry} {P : ℝ} {W : ℝ → Space → Space}
    {act : Fin k → ℝ → Space → Space} (κ : Fin k → ℝ) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (hvw : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤) :
    AEStronglyMeasurable (fun z : ℝ × Space => rightSideLimit W act κ v G H g z.1 z.2) volume ∧
      periodLIntegral (fun σ y => ‖rightSideLimit W act κ v G H g σ y‖ ^ 2) < ⊤ := by
  obtain ⟨D, hD⟩ := hWdecay
  have hW0 : ∀ σ y, ‖W σ y‖ ≤ |D| := fun σ y => by
    have h0 := hD σ y 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at h0
    have hr : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have : D / (1 + ‖y‖) ≤ |D| := by
      rcases le_or_gt 0 D with hD0 | hD0
      · exact (div_le_self hD0 hr).trans (le_abs_self D)
      · exact (div_neg_of_neg_of_pos hD0 (by linarith)).le.trans (abs_nonneg D)
    exact h0.trans this
  have hDW : ∀ σ y, ‖fderiv ℝ (W σ) y (v σ y)‖ ^ 2 ≤ D ^ 2 * (‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := fun σ y => by
    have h1 := hD σ y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h1
    set a := ‖fderiv ℝ (W σ) y‖ with ha
    set r := 1 + ‖y‖ with hr
    have hr1 : 1 ≤ r := by rw [hr]; linarith [norm_nonneg y]
    have hr0 : 0 < r := by linarith
    have ha0 : 0 ≤ a := norm_nonneg _
    have har : a * r ^ 2 ≤ D := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < r ^ (1 + 1))).1 h1
      simpa using this
    have har' : a * r ≤ D :=
      (mul_le_mul_of_nonneg_left (by nlinarith : r ≤ r ^ 2) ha0).trans har
    have hD0 : 0 ≤ D := le_trans (by positivity) har'
    have happ : ‖fderiv ℝ (W σ) y (v σ y)‖ ≤ a * ‖v σ y‖ := ContinuousLinearMap.le_opNorm _ _
    have hsq : ‖fderiv ℝ (W σ) y (v σ y)‖ ^ 2 ≤ (a * r) ^ 2 * (‖v σ y‖ ^ 2 / r ^ 2) := by
      rw [show (a * r) ^ 2 * (‖v σ y‖ ^ 2 / r ^ 2) = (a * ‖v σ y‖) ^ 2 by field_simp]
      exact pow_le_pow_left₀ (norm_nonneg _) happ 2
    refine hsq.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact pow_le_pow_left₀ (mul_nonneg ha0 hr0.le) har' 2
  have mg := hv.measurable_derivative
  have mt : AEStronglyMeasurable (fun z : ℝ × Space => -secondDerivTrace (H z.1 z.2)) volume :=
    (continuous_secondDerivTrace.comp_aestronglyMeasurable hv.measurable_secondDeriv).neg
  have mGW : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (W z.1 z.2)) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hv.measurable_gradient.prodMk hW.continuous.aestronglyMeasurable)
  have mDW : AEStronglyMeasurable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((continuous_fderiv_of_contDiff_two hW).aestronglyMeasurable.prodMk hv.measurable_velocity)
  have hs := periodL2_sum (A := fun i σ y => κ i • act i σ y) Finset.univ
    (fun i => (hactm i).const_smul (κ i)) (fun i => periodL2_of_le (C := κ i ^ 2) (sq_nonneg _)
      (fun σ y => by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]) (hact2 i))
  have l1 := periodL2_add (A := g) (B := fun σ y => -secondDerivTrace (H σ y)) mg mt hv.derivative_finite
    (by simpa only [norm_neg] using hv.sumSecondPartials_finite)
  have m1 : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2 + -secondDerivTrace (H z.1 z.2)) volume := mg.add mt
  have l2 := periodL2_add (A := fun σ y => g σ y + -secondDerivTrace (H σ y)) (B := fun σ y => G σ y (W σ y))
    m1 mGW l1 (periodL2_of_le (f := fun σ y => matSq (G σ y)) (C := 3 * |D| ^ 2) (by positivity)
      (fun σ y => by
        have e1 : ‖G σ y (W σ y)‖ ≤ ‖G σ y‖ * |D| :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hW0 σ y) (norm_nonneg _))
        have e2 := Breakdown.Coercive.Internal.PerturbationFacts.sq_norm_le_three_matNorm (G σ y)
        calc ‖G σ y (W σ y)‖ ^ 2 ≤ (‖G σ y‖ * |D|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e1 2
          _ = ‖G σ y‖ ^ 2 * |D| ^ 2 := by ring
          _ ≤ (3 * matSq (G σ y)) * |D| ^ 2 := mul_le_mul_of_nonneg_right e2 (by positivity)
          _ = 3 * |D| ^ 2 * matSq (G σ y) := by ring) hv.gradient_finite)
  have m2 : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2 + -secondDerivTrace (H z.1 z.2)
      + G z.1 z.2 (W z.1 z.2)) volume := m1.add mGW
  have l3 := periodL2_add (A := fun σ y => g σ y + -secondDerivTrace (H σ y) + G σ y (W σ y))
    (B := fun σ y => fderiv ℝ (W σ) y (v σ y)) m2 mDW l2
    (periodL2_of_le (C := D ^ 2) (sq_nonneg _) hDW hvw)
  have m3 : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2 + -secondDerivTrace (H z.1 z.2)
      + G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume := m2.add mDW
  have l4 := periodL2_add (A := fun σ y => g σ y + -secondDerivTrace (H σ y) + G σ y (W σ y)
      + fderiv ℝ (W σ) y (v σ y)) (B := fun σ y => ∑ i, κ i • act i σ y) m3 hs.1 l3 hs.2
  have e : ∀ σ y, rightSideLimit W act κ v G H g σ y = g σ y + -secondDerivTrace (H σ y) + G σ y (W σ y)
      + fderiv ℝ (W σ) y (v σ y) + ∑ i, κ i • act i σ y := fun σ y => by
    simp only [rightSideLimit, sub_eq_add_neg]
  simp only [e]
  exact ⟨m3.add hs.1, l4⟩

theorem weightedVelocity_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hu : IsSmoothApproximation P v G H g u) :
    periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤ := by
  obtain ⟨n, hn⟩ := (hu.2.2.2.1.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
  have hc : Continuous (fun z : ℝ × Space => u n z.1 z.2) := (hu.1 n).smooth.continuous
  have hr : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) := by fun_prop
  have m1 : AEMeasurable (fun z : ℝ × Space => 2 * (‖u n z.1 z.2 - v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2)) volume :=
    (((hc.aestronglyMeasurable.sub hv.measurable_velocity).norm.aemeasurable.pow_const 2).div
      hr.aemeasurable).const_mul 2
  have m2 : AEMeasurable (fun z : ℝ × Space => 2 * (‖u n z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2)) volume :=
    ((hc.norm.aemeasurable.pow_const 2).div hr.aemeasurable).const_mul 2
  have hle := periodLIntegral_mono (f := fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
    (g := fun σ y => 2 * (‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) + 2 * (‖u n σ y‖ ^ 2 / (1 + ‖y‖) ^ 2))
    fun σ y => by
      have hr0 : 0 < (1 + ‖y‖) ^ 2 := by positivity
      have htri : ‖v σ y‖ ≤ ‖u n σ y - v σ y‖ + ‖u n σ y‖ := by
        have := norm_sub_le (u n σ y) (u n σ y - v σ y)
        rw [sub_sub_cancel] at this
        linarith
      rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
      refine div_le_div_of_nonneg_right ?_ hr0.le
      nlinarith [norm_nonneg (v σ y), norm_nonneg (u n σ y - v σ y), norm_nonneg (u n σ y),
        sq_nonneg (‖u n σ y - v σ y‖ - ‖u n σ y‖)]
  rw [periodLIntegral_add (f := fun σ y => 2 * (‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2))
    (g := fun σ y => 2 * (‖u n σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)) m1 m2 (fun σ y => by positivity)
    (fun σ y => by positivity)] at hle
  refine lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · exact lt_of_le_of_lt (periodLIntegral_le_mul (g := fun σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
      (by norm_num) fun σ y => le_refl _) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hn)
  · exact lt_of_le_of_lt (periodLIntegral_le_mul (g := fun σ y => ‖u n σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
      (by norm_num) fun σ y => le_refl _) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hu.1 n).weighted_finite)

theorem smoothRight_add_eq {k : ℕ} (P : ℝ) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space)
    (κ : Fin k → ℝ) (u : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    smoothRight P W u σ y + ∑ i, κ i • act i σ y
      = rightSideLimit W act κ u (gradField u) (secondDerivField u) (transportPart P u) σ y := by
  simp only [smoothRight, rightSideLimit, transportPart, gradField]

theorem smoothRight_memL2 {k : ℕ} {P : ℝ} {W : ℝ → Space → Space} {act : Fin k → ℝ → Space → Space}
    (κ : Fin k → ℝ) {u : ℝ → Space → Space} (hSP : SmoothPerturbationIsPerturbationHolds)
    (hu : IsSmoothPerturbation P u)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) :
    AEStronglyMeasurable (fun z : ℝ × Space => smoothRight P W u z.1 z.2 + ∑ i, κ i • act i z.1 z.2) volume ∧
      periodLIntegral (fun σ y => ‖smoothRight P W u σ y + ∑ i, κ i • act i σ y‖ ^ 2) < ⊤ := by
  have h := rightSideLimit_memL2 κ (hSP P u hu) hW hWdecay hactm hact2 hu.weighted_finite
  simp only [smoothRight_add_eq]
  exact h

theorem norm_field_le_abs {W : ℝ → Space → Space} {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (σ : ℝ) (y : Space) :
    ‖W σ y‖ ≤ |D| := by
  have h0 := hD σ y 0 (by norm_num)
  rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at h0
  have hr : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have : D / (1 + ‖y‖) ≤ |D| := by
    rcases le_or_gt 0 D with hD0 | hD0
    · exact (div_le_self hD0 hr).trans (le_abs_self D)
    · exact (div_neg_of_neg_of_pos hD0 (by linarith)).le.trans (abs_nonneg D)
  exact h0.trans this

theorem norm_fderiv_field_apply_sq_le {W : ℝ → Space → Space} {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (σ : ℝ) (y x : Space) :
    ‖fderiv ℝ (W σ) y x‖ ^ 2 ≤ D ^ 2 * (‖x‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
  have h1 := hD σ y 1 (by norm_num)
  rw [norm_iteratedFDeriv_one] at h1
  set a := ‖fderiv ℝ (W σ) y‖ with ha
  set r := 1 + ‖y‖ with hr
  have hr1 : 1 ≤ r := by rw [hr]; linarith [norm_nonneg y]
  have hr0 : 0 < r := by linarith
  have ha0 : 0 ≤ a := norm_nonneg _
  have har : a * r ^ 2 ≤ D := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < r ^ (1 + 1))).1 h1
    simpa using this
  have har' : a * r ≤ D :=
    (mul_le_mul_of_nonneg_left (by nlinarith : r ≤ r ^ 2) ha0).trans har
  have happ : ‖fderiv ℝ (W σ) y x‖ ≤ a * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
  have hsq : ‖fderiv ℝ (W σ) y x‖ ^ 2 ≤ (a * r) ^ 2 * (‖x‖ ^ 2 / r ^ 2) := by
    rw [show (a * r) ^ 2 * (‖x‖ ^ 2 / r ^ 2) = (a * ‖x‖) ^ 2 by field_simp]
    exact pow_le_pow_left₀ (norm_nonneg _) happ 2
  refine hsq.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_left₀ (mul_nonneg ha0 hr0.le) har' 2

theorem continuous_secondDerivSq : Continuous secondDerivSq := by
  unfold secondDerivSq
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun l _ =>
    ((continuous_id.clm_apply continuous_const).clm_apply continuous_const).norm.pow 2

theorem secondDerivSq_nonneg (A : Space →L[ℝ] Space →L[ℝ] Space) : 0 ≤ secondDerivSq A := by
  unfold secondDerivSq; positivity

theorem matSq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ matSq A := by
  unfold matSq; positivity

theorem traceSq_le_three_secondDerivSq (A : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖secondDerivTrace A‖ ^ 2 ≤ 3 * secondDerivSq A := by
  have h := norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => A (unitVector j) (unitVector j))
  unfold secondDerivTrace
  unfold secondDerivSq
  simp only [Fin.sum_univ_three] at h ⊢
  have n0 := norm_nonneg (A (unitVector 0) (unitVector 0))
  have n1 := norm_nonneg (A (unitVector 1) (unitVector 1))
  have n2 := norm_nonneg (A (unitVector 2) (unitVector 2))
  have nt := norm_nonneg (A (unitVector 0) (unitVector 0) + A (unitVector 1) (unitVector 1)
    + A (unitVector 2) (unitVector 2))
  nlinarith [sq_nonneg (‖A (unitVector 0) (unitVector 0)‖ - ‖A (unitVector 1) (unitVector 1)‖),
    sq_nonneg (‖A (unitVector 1) (unitVector 1)‖ - ‖A (unitVector 2) (unitVector 2)‖),
    sq_nonneg (‖A (unitVector 0) (unitVector 0)‖ - ‖A (unitVector 2) (unitVector 2)‖),
    sq_nonneg ‖A (unitVector 0) (unitVector 1)‖, sq_nonneg ‖A (unitVector 0) (unitVector 2)‖,
    sq_nonneg ‖A (unitVector 1) (unitVector 0)‖, sq_nonneg ‖A (unitVector 1) (unitVector 2)‖,
    sq_nonneg ‖A (unitVector 2) (unitVector 0)‖, sq_nonneg ‖A (unitVector 2) (unitVector 1)‖]

theorem rightSideLimit_sub {k : ℕ} (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space)
    (κ : Fin k → ℝ) (u v : ℝ → Space → Space) (G₁ G : ℝ → Space → (Space →L[ℝ] Space))
    (H₁ H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g₁ g : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    rightSideLimit W act κ u G₁ H₁ g₁ σ y - rightSideLimit W act κ v G H g σ y
      = (g₁ σ y - g σ y) + -secondDerivTrace (H₁ σ y - H σ y) + (G₁ σ y - G σ y) (W σ y)
        + fderiv ℝ (W σ) y (u σ y - v σ y) := by
  simp only [rightSideLimit, secondDerivTrace, ContinuousLinearMap.sub_apply, map_sub, Finset.sum_sub_distrib]
  abel

theorem norm_add_four_sq_le (a b c d : Space) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h1 := norm_add_le (a + b + c) d
  have h2 := norm_add_le (a + b) c
  have h3 := norm_add_le a b
  have h : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by linarith
  have h0 := norm_nonneg (a + b + c + d)
  have := norm_nonneg a; have := norm_nonneg b; have := norm_nonneg c; have := norm_nonneg d
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

theorem smoothRight_tendsto {k : ℕ} {Γ : Set Symmetry} {P : ℝ} {W : ℝ → Space → Space}
    {act : Fin k → ℝ → Space → Space} (κ : Fin k → ℝ) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space} (hSP : SmoothPerturbationIsPerturbationHolds)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y
      - rightSideLimit W act κ v G H g σ y‖ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := hWdecay
  set C : ℝ := 4 * (3 + 3 * |D| ^ 2 + D ^ 2) with hC
  have hC0 : 0 ≤ C := by positivity
  set f : ℕ → ℝ → Space → ℝ := fun n σ y => ‖transportPart P (u n) σ y - g σ y‖ ^ 2
    + secondDerivSq (secondDerivField (u n) σ y - H σ y) + matSq (gradField (u n) σ y - G σ y)
    + ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 with hf
  have hpt : ∀ n σ y, ‖smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y
      - rightSideLimit W act κ v G H g σ y‖ ^ 2 ≤ C * f n σ y := fun n σ y => by
    rw [smoothRight_add_eq, rightSideLimit_sub]
    refine (norm_add_four_sq_le _ _ _ _).trans ?_
    have e2 : ‖-secondDerivTrace (secondDerivField (u n) σ y - H σ y)‖ ^ 2 ≤ 3 * secondDerivSq (secondDerivField (u n) σ y - H σ y) := by
      rw [norm_neg]; exact traceSq_le_three_secondDerivSq _
    have e3 : ‖(gradField (u n) σ y - G σ y) (W σ y)‖ ^ 2 ≤ 3 * |D| ^ 2 * matSq (gradField (u n) σ y - G σ y) := by
      have e1 : ‖(gradField (u n) σ y - G σ y) (W σ y)‖ ≤ ‖gradField (u n) σ y - G σ y‖ * |D| :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (norm_field_le_abs hD σ y)
          (norm_nonneg _))
      have e2 := Breakdown.Coercive.Internal.PerturbationFacts.sq_norm_le_three_matNorm (gradField (u n) σ y - G σ y)
      calc ‖(gradField (u n) σ y - G σ y) (W σ y)‖ ^ 2 ≤ (‖gradField (u n) σ y - G σ y‖ * |D|) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) e1 2
        _ = ‖gradField (u n) σ y - G σ y‖ ^ 2 * |D| ^ 2 := by ring
        _ ≤ (3 * matSq (gradField (u n) σ y - G σ y)) * |D| ^ 2 := mul_le_mul_of_nonneg_right e2 (by positivity)
        _ = 3 * |D| ^ 2 * matSq (gradField (u n) σ y - G σ y) := by ring
    have e4 := norm_fderiv_field_apply_sq_le hD σ y (u n σ y - v σ y)
    have p1 := sq_nonneg ‖transportPart P (u n) σ y - g σ y‖
    have p2 := secondDerivSq_nonneg (secondDerivField (u n) σ y - H σ y)
    have p3 := matSq_nonneg' (gradField (u n) σ y - G σ y)
    have p4 : 0 ≤ ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := by positivity
    have q1 : 0 ≤ |D| ^ 2 := by positivity
    have q2 : 0 ≤ D ^ 2 := by positivity
    simp only [hf, hC]
    nlinarith [mul_nonneg q1 p3, mul_nonneg q2 p4, mul_nonneg q1 p1, mul_nonneg q1 p2, mul_nonneg q1 p4,
      mul_nonneg q2 p1, mul_nonneg q2 p2, mul_nonneg q2 p3]
  have hm : ∀ n, IsPerturbation ∅ P (u n) (gradField (u n)) (secondDerivField (u n)) (transportPart P (u n)) :=
    fun n => hSP P (u n) (hu.1 n)
  have hr : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) := by fun_prop
  have m1 : ∀ n, AEMeasurable (fun z : ℝ × Space => ‖transportPart P (u n) z.1 z.2 - g z.1 z.2‖ ^ 2) volume :=
    fun n => ((hm n).measurable_derivative.sub hv.measurable_derivative).norm.aemeasurable.pow_const 2
  have m2 : ∀ n, AEMeasurable (fun z : ℝ × Space => secondDerivSq (secondDerivField (u n) z.1 z.2 - H z.1 z.2)) volume :=
    fun n => (continuous_secondDerivSq.comp_aestronglyMeasurable
      ((hm n).measurable_secondDeriv.sub hv.measurable_secondDeriv)).aemeasurable
  have m3 : ∀ n, AEMeasurable (fun z : ℝ × Space => matSq (gradField (u n) z.1 z.2 - G z.1 z.2)) volume :=
    fun n => (Breakdown.Coercive.Internal.PerturbationFacts.continuous_matNorm.comp_aestronglyMeasurable
      ((hm n).measurable_gradient.sub hv.measurable_gradient)).aemeasurable
  have m4 : ∀ n, AEMeasurable (fun z : ℝ × Space => ‖u n z.1 z.2 - v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) volume :=
    fun n => (((hm n).measurable_velocity.sub hv.measurable_velocity).norm.aemeasurable.pow_const 2).div
      hr.aemeasurable
  have hsplit : ∀ n, periodLIntegral (f n) =
      periodLIntegral (fun σ y => ‖transportPart P (u n) σ y - g σ y‖ ^ 2)
      + periodLIntegral (fun σ y => secondDerivSq (secondDerivField (u n) σ y - H σ y))
      + periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y))
      + periodLIntegral (fun σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := fun n => by
    rw [hf]
    rw [periodLIntegral_add (f := fun σ y => ‖transportPart P (u n) σ y - g σ y‖ ^ 2
        + secondDerivSq (secondDerivField (u n) σ y - H σ y) + matSq (gradField (u n) σ y - G σ y))
      (g := fun σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) (((m1 n).add (m2 n)).add (m3 n)) (m4 n)
      (fun σ y => by have := secondDerivSq_nonneg (secondDerivField (u n) σ y - H σ y);
                     have := matSq_nonneg' (gradField (u n) σ y - G σ y); positivity)
      (fun σ y => by positivity)]
    rw [periodLIntegral_add (f := fun σ y => ‖transportPart P (u n) σ y - g σ y‖ ^ 2
        + secondDerivSq (secondDerivField (u n) σ y - H σ y))
      (g := fun σ y => matSq (gradField (u n) σ y - G σ y)) ((m1 n).add (m2 n)) (m3 n)
      (fun σ y => by have := secondDerivSq_nonneg (secondDerivField (u n) σ y - H σ y); positivity)
      (fun σ y => matSq_nonneg' _)]
    rw [periodLIntegral_add (f := fun σ y => ‖transportPart P (u n) σ y - g σ y‖ ^ 2)
      (g := fun σ y => secondDerivSq (secondDerivField (u n) σ y - H σ y)) (m1 n) (m2 n)
      (fun σ y => by positivity) (fun σ y => secondDerivSq_nonneg _)]
  have hsum : Tendsto (fun n => periodLIntegral (f n)) atTop (𝓝 0) := by
    simp only [hsplit]
    have := ((hu.2.2.2.2.add hu.2.2.1).add hu.2.1).add hu.2.2.2.1
    simpa using this
  have hup : Tendsto (fun n => ENNReal.ofReal C * periodLIntegral (f n)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hsum (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => bot_le)
    (fun n => periodLIntegral_le_mul hC0 (hpt n))

end Internal.PassageLimit

end Coercive

end Breakdown
