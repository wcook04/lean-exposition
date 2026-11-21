import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal

theorem eLpNorm_two_le_of_pointwise {f : Space → CSpace} {g : Space → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ η, ‖g η‖ ^ 2 ≤ K * hsWeight 1 η * ‖f η‖ ^ 2) :
    eLpNorm g 2 volume ≤ (ENNReal.ofReal K * hsNormSq 1 f) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [hsNormSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun η => ?_
  have hw : 0 ≤ hsWeight 1 η := by unfold hsWeight; positivity
  rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hw, ← ENNReal.ofReal_mul hK]
  refine ENNReal.ofReal_le_ofReal ?_
  have := h η
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  linarith

theorem eLpNorm_component_le (f : Space → CSpace) (j : Fin 3) :
    eLpNorm (fun η => f η j) 2 volume ≤ (ENNReal.ofReal 1 * hsNormSq 1 f) ^ (1 / 2 : ℝ) := by
  refine eLpNorm_two_le_of_pointwise zero_le_one fun η => ?_
  have h1 : ‖f η j‖ ≤ ‖f η‖ := PiLp.norm_apply_le _ _
  have h2 : 1 ≤ hsWeight 1 η := by unfold hsWeight; simp
  have h3 : ‖f η j‖ ^ 2 ≤ ‖f η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg ‖f η‖]

theorem eLpNorm_weighted_le (f : Space → CSpace) (i j : Fin 3) :
    eLpNorm (fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) 2 volume ≤
      (ENNReal.ofReal (4 * π ^ 2) * hsNormSq 1 f) ^ (1 / 2 : ℝ) := by
  refine eLpNorm_two_le_of_pointwise (by positivity) fun η => ?_
  have h1 : ‖f η i‖ ≤ ‖f η‖ := PiLp.norm_apply_le _ _
  have h2 : |η j| ≤ ‖η‖ := by simpa using PiLp.norm_apply_le η j
  have e1 : ‖2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i‖ = 2 * π * |η j| * ‖f η i‖ := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [e1]
  have h4 : |η j| ^ 2 ≤ ‖η‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h5 : ‖f η i‖ ^ 2 ≤ ‖f η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h6 : hsWeight 1 η = 1 + ‖η‖ ^ 2 := by simp [hsWeight]
  rw [h6]
  have hp : 0 ≤ π ^ 2 := by positivity
  have : (2 * π * |η j| * ‖f η i‖) ^ 2 = 4 * π ^ 2 * (|η j| ^ 2 * ‖f η i‖ ^ 2) := by ring
  rw [this, mul_assoc (4 * π ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |η j| ^ 2 * ‖f η i‖ ^ 2 ≤ ‖η‖ ^ 2 * ‖f η‖ ^ 2 :=
        mul_le_mul h4 h5 (by positivity) (by positivity)
    _ ≤ (1 + ‖η‖ ^ 2) * ‖f η‖ ^ 2 := by nlinarith [sq_nonneg ‖f η‖]

theorem tendsto_rpow_const_mul {l : Filter ℝ} {X : ℝ → ℝ≥0∞} (hX : Tendsto X l (𝓝 0)) (c : ℝ≥0∞)
    (hc : c ≠ ⊤) : Tendsto (fun s => (c * X s) ^ (1 / 2 : ℝ)) l (𝓝 0) := by
  have h1 : Tendsto (fun s => c * X s) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hX (Or.inr hc)
  have h2 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp h1
  simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using h2

theorem continuousOn_integral_mul {S : Set ℝ} {a b : ℝ → Space → ℂ}
    (ha : ∀ s ∈ S, MemLp (a s) 2 volume) (hb : ∀ s ∈ S, MemLp (b s) 2 volume)
    (ha' : ∀ t ∈ S, Tendsto (fun s => eLpNorm (a s - a t) 2 volume) (𝓝[S] t) (𝓝 0))
    (hb' : ∀ t ∈ S, Tendsto (fun s => eLpNorm (b s - b t) 2 volume) (𝓝[S] t) (𝓝 0)) :
    ContinuousOn (fun s => ∫ η, a s η * b s η) S := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
  have hA : eLpNorm (a t) 2 volume ≠ ⊤ := (ha t ht).eLpNorm_ne_top
  have hB : eLpNorm (b t) 2 volume ≠ ⊤ := (hb t ht).eLpNorm_ne_top
  have hlim : Tendsto (fun s => eLpNorm (a s - a t) 2 volume *
      (eLpNorm (b s - b t) 2 volume + eLpNorm (b t) 2 volume) +
      eLpNorm (a t) 2 volume * eLpNorm (b s - b t) 2 volume) (𝓝[S] t) (𝓝 0) := by
    have h0 : Tendsto (fun s => eLpNorm (b s - b t) 2 volume + eLpNorm (b t) 2 volume) (𝓝[S] t)
        (𝓝 (0 + eLpNorm (b t) 2 volume)) := (hb' t ht).add tendsto_const_nhds
    have h1 := ENNReal.Tendsto.mul (ha' t ht) (Or.inr (by simpa using hB)) h0
      (Or.inr ENNReal.zero_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (hb' t ht) (Or.inr hA)
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have has := ha s hs
  have hbs := hb s hs
  have hat := ha t ht
  have hbt := hb t ht
  have i1 : Integrable (fun η => a s η * b s η) volume := has.integrable_mul hbs
  have i2 : Integrable (fun η => a t η * b t η) volume := hat.integrable_mul hbt
  have m1 : AEStronglyMeasurable (a s - a t) volume := has.1.sub hat.1
  have m2 : AEStronglyMeasurable (b s - b t) volume := hbs.1.sub hbt.1
  have hbs' : eLpNorm (b s) 2 volume ≤ eLpNorm (b s - b t) 2 volume + eLpNorm (b t) 2 volume := by
    have := eLpNorm_add_le m2 hbt.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa using this
  rw [edist_eq_enorm_sub, ← integral_sub i1 i2]
  calc ‖∫ η, (a s η * b s η - a t η * b t η)‖ₑ
      ≤ ∫⁻ η, ‖a s η * b s η - a t η * b t η‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm ((a s - a t) • b s + a t • (b s - b t)) 1 volume := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        congr 1
        ext η
        show _ = ‖(a s η - a t η) * b s η + a t η * (b s η - b t η)‖ₑ
        congr 1
        ring
    _ ≤ eLpNorm ((a s - a t) • b s) 1 volume + eLpNorm (a t • (b s - b t)) 1 volume :=
        eLpNorm_add_le (m1.smul hbs.1) (hat.1.smul m2) le_rfl
    _ ≤ eLpNorm (a s - a t) 2 volume * eLpNorm (b s) 2 volume +
          eLpNorm (a t) 2 volume * eLpNorm (b s - b t) 2 volume :=
        add_le_add (eLpNorm_smul_le_mul_eLpNorm hbs.1 m1) (eLpNorm_smul_le_mul_eLpNorm m2 hat.1)
    _ ≤ _ := by gcongr

end Internal

open Internal in
theorem continuousOn_advectionSymbol_apply {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve 1 F 0 T) (ξ : Space) :
    ContinuousOn (fun s => advectionSymbol (F s) ξ) (Icc 0 T) := by
  have hmp : MeasurePreserving (fun η : Space => ξ - η) volume volume :=
    Measure.measurePreserving_sub_left volume ξ
  have key : ∀ i j : Fin 3, ContinuousOn (fun s => convC (fun η => F s η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * F s η i) ξ) (Icc 0 T) := by
    intro i j
    set c : ℝ → Space → ℂ := fun s η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * F s η i with hc
    have hcm : ∀ s ∈ Icc 0 T, MemLp (c s) 2 volume := by
      intro s hs
      refine ⟨?_, (eLpNorm_weighted_le (F s) i j).trans_lt ?_⟩
      · have hm := (hF.1 s hs).1
        exact (aestronglyMeasurable_const.mul (Complex.continuous_ofReal.comp
          (PiLp.continuous_apply 2 _ j)).aestronglyMeasurable).mul
          ((PiLp.continuous_apply 2 _ i).comp_aestronglyMeasurable hm)
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hF.1 s hs).2.ne)
    have hcs : ∀ s t, c s - c t = fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * (F s - F t) η i := by
      intro s t
      ext η
      simp only [hc, Pi.sub_apply, PiLp.sub_apply]
      ring
    unfold convC
    refine continuousOn_integral_mul (a := fun s η => F s η j) (b := fun s η => c s (ξ - η)) ?_ ?_ ?_ ?_
    · intro s hs
      refine ⟨(PiLp.continuous_apply 2 _ j).comp_aestronglyMeasurable (hF.1 s hs).1,
        (eLpNorm_component_le (F s) j).trans_lt ?_⟩
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hF.1 s hs).2.ne)
    · intro s hs
      exact (hcm s hs).comp_measurePreserving hmp
    · intro t ht
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_rpow_const_mul (hF.2 t ht) (ENNReal.ofReal 1) ENNReal.ofReal_ne_top)
        (fun _ => zero_le) fun s => ?_
      have : (fun η => F s η j) - (fun η => F t η j) = fun η => (F s - F t) η j := by
        ext η; simp
      simp only [this]
      exact eLpNorm_component_le _ j
    · intro t ht
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_rpow_const_mul (hF.2 t ht) (ENNReal.ofReal (4 * π ^ 2)) ENNReal.ofReal_ne_top)
        (Eventually.of_forall fun _ => zero_le) ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have e1 : (fun η => c s (ξ - η)) - (fun η => c t (ξ - η)) = (c s - c t) ∘ fun η => ξ - η := by
        ext η; simp
      rw [e1, eLpNorm_comp_measurePreserving ((hcm s hs).1.sub (hcm t ht).1) hmp, hcs]
      exact eLpNorm_weighted_le _ i j
  show ContinuousOn (fun s => WithLp.toLp 2 (fun i => ∑ j, convC (fun η => F s η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * F s η i) ξ)) (Icc 0 T)
  exact (PiLp.continuous_toLp 2 _).comp_continuousOn
    (continuousOn_pi.2 fun i => continuousOn_finsetSum _ fun j _ => key i j)

theorem hasDerivWithinAt_apply_of_varConst {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace}
    (hd : IsVarConstSymbol F 0 T) {ξ : Space}
    (hc : ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => F τ ξ)
      (-(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • F t ξ + nonlinSymbol (F t) ξ) (Icc 0 T) t := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 4 * π ^ 2 * ‖ξ‖ ^ 2 := ⟨_, rfl⟩
  rw [← hcdef]
  let g : ℝ → CSpace := fun s => ((Real.exp (c * s) : ℝ) : ℂ) • nonlinSymbol (F s) ξ
  have hg : ContinuousOn g (Icc 0 T) := by
    have h0 : ContinuousOn (fun s : ℝ => ((Real.exp (c * s) : ℝ) : ℂ)) (Icc 0 T) :=
      (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
    exact h0.smul hc
  let p : ℝ → ℝ := fun s => (projIcc 0 T hT.le s : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  let g' : ℝ → CSpace := fun s => g (p s)
  have hg' : Continuous g' := hg.comp_continuous hp (fun s => (projIcc 0 T hT.le s).2)
  let e : ℝ → ℂ := fun τ => ((Real.exp (-c * τ) : ℝ) : ℂ)
  let G : ℝ → CSpace := fun τ => F 0 ξ + ∫ s in (0 : ℝ)..τ, g' s
  have hpeq : ∀ τ ∈ Icc 0 T, p τ = τ := fun τ hτ => by simp [p, projIcc_of_mem _ hτ]
  have hrep : ∀ τ ∈ Icc 0 T, F τ ξ = e τ • G τ := by
    intro τ hτ
    rw [hd τ hτ ξ]
    have h1 : ∫ s in (0 : ℝ)..τ, ((heatSymbol (τ - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ =
        ∫ s in (0 : ℝ)..τ, e τ • g' s := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [uIcc_of_le hτ.1] at hs
      have hps : p s = s := hpeq s ⟨hs.1, hs.2.trans hτ.2⟩
      simp only [g', g, hps, e, heatSymbol, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 4
      rw [hcdef]
      ring
    rw [h1, intervalIntegral.integral_smul, smul_add]
    congr 3
    simp only [heatSymbol, sub_zero, hcdef]
    ring_nf
  have he : HasDerivAt e ((Real.exp (-c * t) * (-c) : ℝ) : ℂ) t := by
    have : HasDerivAt (fun τ => Real.exp (-c * τ)) (Real.exp (-c * t) * (-c)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-c)).exp
    exact this.ofReal_comp
  have hG : HasDerivAt G (g' t) t :=
    ((hg'.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (F 0 ξ)
  have hder := (he.smul hG).hasDerivWithinAt (s := Icc 0 T)
  refine (hder.congr_of_mem hrep ht).congr_deriv ?_
  have h1 : e t • g' t = nonlinSymbol (F t) ξ := by
    simp only [g', g, hpeq t ht, e, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -c * t + c * t = 0 by ring]
    simp
  have h2 : ((Real.exp (-c * t) * (-c) : ℝ) : ℂ) • G t = -((c : ℝ) : ℂ) • (e t • G t) := by
    rw [smul_smul]
    congr 1
    simp only [e]
    push_cast
    ring
  rw [h1, h2, ← hrep t ht, add_comm]

end Breakdown.SmoothFlow
