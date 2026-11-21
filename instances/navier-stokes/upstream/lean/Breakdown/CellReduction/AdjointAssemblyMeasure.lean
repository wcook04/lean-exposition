import Breakdown.CellReduction.AdjointAssemblyAlgebra

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

abbrev periodMeasure : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume

theorem periodMeasure_ac : periodMeasure ≪ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod Measure.AbsolutelyContinuous.rfl

theorem aesm_period {E : Type*} [TopologicalSpace E] {f : ℝ × Space → E}
    (hf : AEStronglyMeasurable f volume) : AEStronglyMeasurable f periodMeasure :=
  hf.mono_ac periodMeasure_ac

theorem iterated_eq {f : ℝ → Space → ℝ} (hf : Integrable (fun z : ℝ × Space => f z.1 z.2) periodMeasure) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, f σ y = ∫ z, f z.1 z.2 ∂periodMeasure :=
  (integral_prod _ hf).symm

theorem periodL_eq {f : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) periodMeasure) :
    periodLIntegral f = ∫⁻ z, ENNReal.ofReal (f z.1 z.2) ∂periodMeasure :=
  (lintegral_prod _ hf).symm

theorem space_weight_integrable {r : ℝ} (hr : 3 < r) : Integrable (fun y : Space => (1 + ‖y‖) ^ (-r)) := by
  apply integrable_one_add_norm
  rw [finrank_euclideanSpace, Fintype.card_fin]
  exact_mod_cast hr

theorem rpow_succ_le {x γ : ℝ} (hx : 0 ≤ x) : (1 + x) ^ γ ≤ (1 + x) ^ (γ + 1) :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem div_succ_le {x γ C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) :
    C / (1 + x) ^ (γ + 1) ≤ C / (1 + x) ^ γ :=
  div_le_div_of_nonneg_left hC (by positivity) (rpow_succ_le hx)

theorem mul_div_succ_le {x γ C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) :
    x * (C / (1 + x) ^ (γ + 1)) ≤ C / (1 + x) ^ γ := by
  have h1 : (1 + x) ^ (γ + 1) = (1 + x) ^ γ * (1 + x) := Real.rpow_add_one (by positivity) γ
  have hp : 0 < (1 + x) ^ γ := by positivity
  rw [h1, mul_div_assoc', div_le_div_iff₀ (by positivity) hp]
  have : x * C * (1 + x) ^ γ ≤ C * ((1 + x) ^ γ * (1 + x)) := by nlinarith
  linarith

theorem weighted_sq_le {x γ C t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (h : t ≤ C / (1 + x) ^ γ) :
    x ^ 2 * t ^ 2 ≤ C ^ 2 * (1 + x) ^ (-(2 * γ - 2)) := by
  have hp : 0 < 1 + x := by linarith
  have h1 : t ^ 2 ≤ (C / (1 + x) ^ γ) ^ 2 := pow_le_pow_left₀ ht h 2
  have h2 : x ^ 2 ≤ (1 + x) ^ 2 := pow_le_pow_left₀ hx (by linarith) 2
  have e : (1 + x) ^ 2 * (C / (1 + x) ^ γ) ^ 2 = C ^ 2 * (1 + x) ^ (-(2 * γ - 2)) := by
    rw [div_pow, ← Real.rpow_natCast ((1 + x) ^ γ), ← Real.rpow_mul hp.le, Real.rpow_neg hp.le,
      Real.rpow_sub hp, ← Real.rpow_natCast (1 + x) 2]
    push_cast
    field_simp
  calc x ^ 2 * t ^ 2 ≤ (1 + x) ^ 2 * (C / (1 + x) ^ γ) ^ 2 :=
        mul_le_mul h2 h1 (sq_nonneg _) (sq_nonneg _)
    _ = _ := e

theorem weighted_period_finite {T : ℝ → Space → Space} {C γ : ℝ} (hγ : 5 / 2 < γ)
    (h : ∀ σ y, ‖T σ y‖ ≤ C / (1 + ‖y‖) ^ γ) :
    periodLIntegral (fun σ y => ‖y‖ ^ 2 * ‖T σ y‖ ^ 2) < ⊤ := by
  have hint : Integrable (fun y : Space => C ^ 2 * (1 + ‖y‖) ^ (-(2 * γ - 2))) :=
    (space_weight_integrable (by linarith)).const_mul _
  have hA := hint.lintegral_lt_top
  unfold periodLIntegral
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖T σ y‖ ^ 2)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (C ^ 2 * (1 + ‖y‖) ^ (-(2 * γ - 2))) := by
        refine lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
        exact weighted_sq_le (norm_nonneg y) (norm_nonneg _) (h σ y)
    _ = (∫⁻ y, ENNReal.ofReal (C ^ 2 * (1 + ‖y‖) ^ (-(2 * γ - 2)))) * volume (Set.Icc (0 : ℝ) 1) :=
        setLIntegral_const _ _
    _ < ⊤ := by
        rw [Real.volume_Icc]
        exact ENNReal.mul_lt_top hA ENNReal.ofReal_lt_top

theorem pairing_integrable (hA : WeightedPairingIntegrableHolds) {Γ : Set Symmetry} {P : ℝ}
    {v g : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hp : IsPerturbation Γ P v G H g)
    {T : ℝ → Space → Space} {C γ : ℝ} (hγ : 5 / 2 < γ)
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => T z.1 z.2) volume)
    (h : ∀ σ y, ‖T σ y‖ ≤ C / (1 + ‖y‖) ^ γ) :
    Integrable (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (T z.1 z.2)) periodMeasure :=
  hA v T G hp.measurable_velocity hp.measurable_gradient hp.weak_gradient hp.sixth_power hp.gradient_finite hm
    (weighted_period_finite hγ h)

theorem continuous_entrySq : Continuous matSq := by
  unfold matSq
  fun_prop

theorem entrySq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A := by
  unfold matSq
  positivity

theorem continuous_matrixPairing : Continuous (fun p : (Space →L[ℝ] Space) × (Space →L[ℝ] Space) => matInner p.1 p.2) := by
  unfold matInner
  fun_prop

theorem entrySq_le (A : Space →L[ℝ] Space) : matSq A ≤ 3 * ‖A‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    intro i
    have := A.le_opNorm (unitVector i)
    rw [norm_unitVector, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc ∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖A‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖A‖ ^ 2 := by simp

theorem abs_matrixPairing_le (A B : Space →L[ℝ] Space) : |matInner A B| ≤ matSq A / 2 + matSq B / 2 := by
  unfold matInner matSq
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (abs_real_inner_le_norm _ _).trans ?_
  nlinarith [sq_nonneg (‖A (unitVector i)‖ - ‖B (unitVector i)‖)]

theorem gradient_integrable {Γ : Set Symmetry} {P : ℝ} {v g : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hp : IsPerturbation Γ P v G H g) :
    Integrable (fun z : ℝ × Space => matSq (G z.1 z.2)) periodMeasure := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) periodMeasure :=
    continuous_entrySq.comp_aestronglyMeasurable (aesm_period hp.measurable_gradient)
  have e : periodLIntegral (fun σ y => matSq (G σ y)) =
      ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂periodMeasure := periodL_eq hm.aemeasurable.ennreal_ofReal
  have hL : ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂periodMeasure < ⊤ := e ▸ hp.gradient_finite
  exact ⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => entrySq_nonneg _)).2 hL⟩

theorem matrix_integrable {Γ : Set Symmetry} {P : ℝ} {v g : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hp : IsPerturbation Γ P v G H g) {M : ℝ → Space → (Space →L[ℝ] Space)} {B β : ℝ} (hβ : 3 / 2 < β)
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume)
    (h : ∀ σ y, ‖M σ y‖ ≤ B / (1 + ‖y‖) ^ β) :
    Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (M z.1 z.2)) periodMeasure := by
  have hG1 : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) periodMeasure :=
    aesm_period hp.measurable_gradient
  have hStrain : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) periodMeasure := aesm_period hm
  have hm' : AEStronglyMeasurable (fun z : ℝ × Space => matInner (G z.1 z.2) (M z.1 z.2)) periodMeasure := by
    unfold matInner
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (hG1.apply_continuousLinearMap _).inner (hStrain.apply_continuousLinearMap _)
  have hw : Integrable (fun z : ℝ × Space => (1 : ℝ) * (B ^ 2 * (1 + ‖z.2‖) ^ (-(2 * β)))) periodMeasure :=
    (integrable_const (1 : ℝ)).mul_prod ((space_weight_integrable (by linarith)).const_mul _)
  have hdom := ((gradient_integrable hp).div_const 2).add (hw.const_mul (3 / 2))
  refine hdom.mono' hm' (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_matrixPairing_le _ _).trans ?_
  have hM := h z.1 z.2
  have hp0 : 0 < 1 + ‖z.2‖ := by positivity
  have h2 : ‖M z.1 z.2‖ ^ 2 ≤ B ^ 2 * (1 + ‖z.2‖) ^ (-(2 * β)) := by
    have e : B ^ 2 * (1 + ‖z.2‖) ^ (-(2 * β)) = (B / (1 + ‖z.2‖) ^ β) ^ 2 := by
      rw [div_pow, ← Real.rpow_natCast ((1 + ‖z.2‖) ^ β), ← Real.rpow_mul hp0.le, Real.rpow_neg hp0.le]
      push_cast
      ring_nf
    rw [e]
    exact pow_le_pow_left₀ (norm_nonneg _) hM 2
  have h3 := entrySq_le (M z.1 z.2)
  simp only [one_mul, Pi.add_apply]
  linarith

end Internal

end AdjointDefect

end Breakdown
