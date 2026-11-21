import Breakdown.Cert.CoerciveSmoothMuPress
import Breakdown.Cert.CoerciveSmoothMuDecay

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuSmooth

theorem unitVector_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  unfold unitVector
  simp

theorem matSq_le (A : Space →L[ℝ] Space) : matSq A ≤ 3 * ‖A‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ‖A‖ ^ 2 := fun i => by
    have := A.le_opNorm (unitVector i)
    rw [unitVector_norm, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc ∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖A‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖A‖ ^ 2 := by simp

theorem continuous_cnormSq_modeGrad {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : Continuous (fun z : ℝ × Space => G z.1 z.2)) (ι : ℤ × ℤ) :
    Continuous (fun z : ℝ × Space => cnormSq (modeGrad ι G z.1 z.2)) := by
  unfold cnormSq
  exact continuous_finsetSum _ fun i _ => ((continuous_modeGrad hG ι i).norm).pow 2

theorem energy_measurable (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Measurable (fun p : ℝ × Space => ENNReal.ofReal (modeEnergy v ι p.1 p.2)) := by
  have hvc : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have hGv : Continuous (fun z : ℝ × Space => gradField v z.1 z.2) :=
    (PairingSplitInternal.contDiff_slice (n := 0) hv.smooth (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).continuous
  exact ((continuous_cnormSq_modeGrad hGv ι).add
    (continuous_cnormSq_modeVel (weighted_continuous v hvc) ι)).measurable.ennreal_ofReal

theorem energy_slice_measurable (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) : Measurable (fun y : Space => ENNReal.ofReal (modeEnergy v ι σ y)) := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (y : Space) => ENNReal.ofReal (modeEnergy v ι s y)) :=
    energy_measurable P v hv ι
  exact h.of_uncurry_left

theorem energy_outer_measurable (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ) :
    Measurable (fun σ : ℝ => ∫⁻ y, ENNReal.ofReal (modeEnergy v ι σ y)) :=
  (energy_measurable P v hv ι).lintegral_prod_right' (ν := volume)

theorem energy_tsum_lt_top (hPars : ModeSquareSumHolds) (P : ℝ) (v : ℝ → Space → Space)
    (hv : IsSmoothPerturbation P v) :
    ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (modeEnergy v ι σ y) < ⊤ := by
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
    exact matSq_le _
  have hGp : IsTimePeriodic (gradField v) := fun σ y => by
    unfold gradField
    rw [show v (σ + 1) = v σ from funext (hv.periodic σ)]
  have e1 := hPars.2.1 (gradField v) hGv.aestronglyMeasurable hGp hG
  have hA := tsum_mode_lt_top hPars (weighted v) (weighted_continuous v hvc).aestronglyMeasurable
    (weighted_periodic v hv.periodic) (weighted_square P v hv)
  have hcg : ∀ ι, Measurable (fun p : ℝ × Space => ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) p.1 p.2))) :=
    fun ι => (continuous_cnormSq_modeGrad hGv ι).measurable.ennreal_ofReal
  have hsplit : ∀ ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (modeEnergy v ι σ y)
      = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι (gradField v) σ y)))
        + 1 * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι (weighted v) σ y)) := by
    intro ι
    rw [← split_const _ (hcg ι) 1 ENNReal.one_ne_top]
    refine lintegral_congr fun σ => lintegral_congr fun y => ?_
    rw [one_mul, modeEnergy, ENNReal.ofReal_add (cnorm_nonneg _) (cnorm_nonneg _)]
  simp_rw [hsplit, one_mul]
  rw [ENNReal.tsum_add]
  refine ENNReal.add_lt_top.2 ⟨?_, hA⟩
  rw [← e1]
  exact hG

theorem rest_finite_of (hPars : ModeSquareSumHolds) {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    ∑' ι, restMode m W v ι < ⊤ := by
  obtain ⟨K, hK0, hK⟩ := rest_pointwise m P b w W hm hb hW hWp hWdecay v hv
  obtain ⟨e, hedef⟩ : ∃ e : ℤ × ℤ → ℝ≥0∞,
      e = fun ι => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (modeEnergy v ι σ y) := ⟨_, rfl⟩
  have hE : ∑' ι, e ι < ⊤ := by
    rw [hedef]
    exact energy_tsum_lt_top hPars P v hv
  have hmE := energy_measurable P v hv
  have h1 : ∀ ι, restMode m W v ι ≤ ENNReal.ofReal K * (e ι + ∑ α ∈ m.waves, e (ι - α)) := by
    intro ι
    have hpt : ∀ σ y, ENNReal.ofReal (-modeMuRest m W v (gradField v) ι σ y)
        ≤ ENNReal.ofReal K * (ENNReal.ofReal (modeEnergy v ι σ y)
          + ∑ α ∈ m.waves, ENNReal.ofReal (modeEnergy v (ι - α) σ y)) := fun σ y => by
      have hn : ∀ κ, 0 ≤ modeEnergy v κ σ y := fun κ => add_nonneg (cnorm_nonneg _) (cnorm_nonneg _)
      rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ => hn _), ← ENNReal.ofReal_add (hn ι)
        (Finset.sum_nonneg fun α _ => hn _), ← ENNReal.ofReal_mul hK0, neg_rest_eq]
      exact ENNReal.ofReal_le_ofReal (hK ι σ y)
    have hin : ∀ σ, ∫⁻ y, (ENNReal.ofReal (modeEnergy v ι σ y)
          + ∑ α ∈ m.waves, ENNReal.ofReal (modeEnergy v (ι - α) σ y))
        = (∫⁻ y, ENNReal.ofReal (modeEnergy v ι σ y))
          + ∑ α ∈ m.waves, ∫⁻ y, ENNReal.ofReal (modeEnergy v (ι - α) σ y) := fun σ => by
      have hm1 := energy_slice_measurable P v hv ι σ
      have hm2 : ∀ α ∈ m.waves, Measurable (fun y => ENNReal.ofReal (modeEnergy v (ι - α) σ y)) :=
        fun α _ => energy_slice_measurable P v hv (ι - α) σ
      rw [lintegral_add_left hm1, lintegral_finsetSum _ hm2]
    calc restMode m W v ι ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal K *
          (ENNReal.ofReal (modeEnergy v ι σ y) + ∑ α ∈ m.waves, ENNReal.ofReal (modeEnergy v (ι - α) σ y)) :=
          lintegral_mono fun σ => lintegral_mono fun y => hpt σ y
      _ = ENNReal.ofReal K * (e ι + ∑ α ∈ m.waves, e (ι - α)) := by
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          simp_rw [hin]
          have ho1 := energy_outer_measurable P v hv ι
          have ho2 : ∀ α ∈ m.waves, Measurable (fun σ => ∫⁻ y, ENNReal.ofReal (modeEnergy v (ι - α) σ y)) :=
            fun α _ => energy_outer_measurable P v hv (ι - α)
          rw [lintegral_add_left ho1, lintegral_finsetSum _ ho2, hedef]
  have hshift : ∀ α : ℤ × ℤ, ∑' ι, e (ι - α) = ∑' ι, e ι := fun α =>
    (Equiv.subRight α).tsum_eq e
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum h1) ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, Summable.tsum_finsetSum (fun α _ => ENNReal.summable)]
  simp_rw [hshift]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.2 ⟨hE, ENNReal.sum_lt_top.2 fun α _ => hE⟩)

end Internal.MuSmooth

end Coercive

end Breakdown
