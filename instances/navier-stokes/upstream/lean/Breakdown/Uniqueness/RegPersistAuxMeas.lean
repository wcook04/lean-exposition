import Breakdown.Uniqueness.RegPersistAuxDefs

open scoped ContDiff ENNReal FourierTransform Topology InnerProductSpace
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem continuous_coordC (k : Fin 3) : Continuous fun z : CSpace => z k := by
  fun_prop

private theorem continuous_coordR (k : Fin 3) : Continuous fun z : Space => z k := by
  fun_prop

private theorem measurable_divFreeC : Measurable fun p : Space × CSpace => divFreeC p.1 p.2 := by
  unfold divFreeC freqVec
  have h1 : Measurable fun p : Space × CSpace => ((((‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_fst.norm.pow_const 2).inv)
  have h2 : Measurable fun p : Space × CSpace => ∑ i, ((p.1 i : ℝ) : ℂ) * p.2 i := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (Complex.measurable_ofReal.comp ((continuous_coordR i).measurable.comp measurable_fst)).mul
      ((continuous_coordC i).measurable.comp measurable_snd)
  have h3 : Measurable fun p : Space × CSpace => complexifyVec p.1 :=
    complexifyVec.continuous.measurable.comp measurable_fst
  exact measurable_snd.sub ((h1.mul h2).smul h3)

private theorem convC_congr_ae {f f' g g' : Space → ℂ} (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g')
    (ξ : Space) : convC f g ξ = convC f' g' ξ := by
  unfold convC
  refine integral_congr_ae ?_
  have hg' : (g ∘ fun η => ξ - η) =ᵐ[volume] (g' ∘ fun η => ξ - η) :=
    (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hf, hg'] with η h1 h2
  simp only [Function.comp_apply] at h2
  rw [h1, h2]

private theorem nonlinSymbol_eq_of_ae {f f' : Space → CSpace} (h : f =ᵐ[volume] f') :
    nonlinSymbol f = nonlinSymbol f' := by
  funext ξ
  unfold nonlinSymbol advectionSymbol advectionBilin
  congr 3
  funext i
  refine Finset.sum_congr rfl fun j _ => convC_congr_ae ?_ ?_ ξ
  · filter_upwards [h] with η hη
    rw [hη]
  · filter_upwards [h] with η hη
    rw [hη]

private theorem measurable_convC {f g : Space → ℂ} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : Measurable (convC f g) := by
  have h : StronglyMeasurable (Function.uncurry fun ξ η : Space => f η * g (ξ - η)) :=
    (hf.comp_measurable measurable_snd).mul (hg.comp_measurable (measurable_fst.sub measurable_snd))
  exact (h.integral_prod_right (ν := volume)).measurable

private theorem measurable_nonlinSymbol {f : Space → CSpace} (hf : AEStronglyMeasurable f volume) :
    Measurable (nonlinSymbol f) := by
  rw [nonlinSymbol_eq_of_ae hf.ae_eq_mk]
  have hm := hf.stronglyMeasurable_mk
  have hA : Measurable (advectionSymbol (hf.mk f)) := by
    unfold advectionSymbol advectionBilin
    refine (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ => measurable_convC ?_ ?_)
    · exact (continuous_coordC j).comp_stronglyMeasurable hm
    · have hc : Continuous fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) := by
        have := continuous_coordR j
        fun_prop
      exact hc.stronglyMeasurable.mul ((continuous_coordC i).comp_stronglyMeasurable hm)
  unfold nonlinSymbol
  exact (measurable_divFreeC.comp (measurable_id.prodMk hA)).neg

private theorem memLp_two_of_lintegral {g : Space → ℂ} (hg : AEStronglyMeasurable g volume)
    (h : ∫⁻ η, ‖g η‖ₑ ^ 2 < ⊤) : MemLp g 2 volume := by
  refine ⟨hg, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

private theorem eLpNorm_two_eq (g : Space → ℂ) :
    eLpNorm g 2 volume = (∫⁻ η, ‖g η‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

open scoped Classical in
private def toL2C (g : Space → ℂ) : Lp ℂ 2 (volume : Measure Space) :=
  if h : MemLp g 2 volume then h.toLp g else 0

private theorem toL2C_eq {g : Space → ℂ} (h : MemLp g 2 volume) : toL2C g = h.toLp g := by
  unfold toL2C
  rw [dif_pos h]

private theorem tendsto_toL2C {S : Set ℝ} {s₀ : ℝ} (hs₀ : s₀ ∈ S) {p : ℝ → Space → ℂ}
    (hp : ∀ s ∈ S, MemLp (p s) 2 volume)
    (hpt : Tendsto (fun s => ∫⁻ η, ‖p s η - p s₀ η‖ₑ ^ 2) (𝓝[S] s₀) (𝓝 0)) :
    Tendsto (fun s => toL2C (p s)) (𝓝[S] s₀) (𝓝 (toL2C (p s₀))) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have e : ∀ᶠ s in 𝓝[S] s₀, (∫⁻ η, ‖p s η - p s₀ η‖ₑ ^ 2) ^ (1 / 2 : ℝ) =
      eLpNorm (⇑(toL2C (p s)) - ⇑(toL2C (p s₀))) 2 volume := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [toL2C_eq (hp s hs), toL2C_eq (hp s₀ hs₀),
      eLpNorm_congr_ae (((hp s hs).coeFn_toLp).sub ((hp s₀ hs₀).coeFn_toLp)), eLpNorm_two_eq]
    rfl
  refine Tendsto.congr' e ?_
  have h0 : (0 : ℝ≥0∞) = 0 ^ (1 / 2 : ℝ) := by rw [ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [h0]
  exact ((ENNReal.continuous_rpow_const).tendsto 0).comp hpt

private theorem tendsto_integral_mul {S : Set ℝ} {s₀ : ℝ} (hs₀ : s₀ ∈ S) {p q : ℝ → Space → ℂ}
    (hp : ∀ s ∈ S, MemLp (p s) 2 volume) (hq : ∀ s ∈ S, MemLp (q s) 2 volume)
    (hpt : Tendsto (fun s => ∫⁻ η, ‖p s η - p s₀ η‖ₑ ^ 2) (𝓝[S] s₀) (𝓝 0))
    (hqt : Tendsto (fun s => ∫⁻ η, ‖q s η - q s₀ η‖ₑ ^ 2) (𝓝[S] s₀) (𝓝 0)) :
    Tendsto (fun s => ∫ η, p s η * q s η) (𝓝[S] s₀) (𝓝 (∫ η, p s₀ η * q s₀ η)) := by
  have hps : ∀ s ∈ S, MemLp (star (p s)) 2 volume := fun s hs => (hp s hs).star
  have hpst : Tendsto (fun s => ∫⁻ η, ‖star (p s) η - star (p s₀) η‖ₑ ^ 2) (𝓝[S] s₀) (𝓝 0) := by
    refine hpt.congr fun s => ?_
    congr 1
    funext η
    simp only [Pi.star_apply, ← star_sub]
    rw [← ofReal_norm, ← ofReal_norm, norm_star]
  have key : ∀ s ∈ S, ∫ η, p s η * q s η = ⟪toL2C (star (p s)), toL2C (q s)⟫_ℂ := by
    intro s hs
    rw [toL2C_eq (hps s hs), toL2C_eq (hq s hs), L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hps s hs).coeFn_toLp, (hq s hs).coeFn_toLp] with η h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have ht := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_toL2C hs₀ hps hpst) (tendsto_toL2C hs₀ hq hqt)
  rw [← key s₀ hs₀] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (key s hs).symm

private theorem one_le_hsWeight (k : ℕ) (η : Space) : 1 ≤ hsWeight k η :=
  one_le_pow₀ (le_add_of_nonneg_right (by positivity))

private theorem enorm_sq_eq {E : Type*} [NormedAddCommGroup E] (z : E) :
    ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

private theorem lintegral_coord_le (f : Space → CSpace) (k : Fin 3) :
    ∫⁻ η, ‖f η k‖ₑ ^ 2 ≤ hsNormSq 3 f := by
  unfold hsNormSq
  refine lintegral_mono fun η => ?_
  rw [enorm_sq_eq, enorm_sq_eq, ← ENNReal.ofReal_mul (by unfold hsWeight; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := PiLp.norm_apply_le (f η) k
  have h2 := one_le_hsWeight 3 η
  calc ‖f η k‖ ^ 2 ≤ ‖f η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ hsWeight 3 η * ‖f η‖ ^ 2 := le_mul_of_one_le_left (by positivity) h2

private theorem lintegral_grad_le (f : Space → CSpace) (j i : Fin 3) :
    ∫⁻ η, ‖2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * π ^ 2) * hsNormSq 3 f := by
  unfold hsNormSq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun η => ?_
  have hw0 : 0 ≤ hsWeight 3 η := by unfold hsWeight; positivity
  rw [enorm_sq_eq, enorm_sq_eq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hw0)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := PiLp.norm_apply_le (f η) i
  have h3 : |η j| ≤ ‖η‖ := by simpa using PiLp.norm_apply_le η j
  have hw : ‖η‖ ^ 2 ≤ hsWeight 3 η := by
    have := one_le_hsWeight 2 η
    unfold hsWeight at this ⊢
    calc ‖η‖ ^ 2 ≤ 1 + ‖η‖ ^ 2 := le_add_of_nonneg_left zero_le_one
      _ = (1 + ‖η‖ ^ 2) * 1 := by ring
      _ ≤ (1 + ‖η‖ ^ 2) * (1 + ‖η‖ ^ 2) ^ 2 := by gcongr
      _ = (1 + ‖η‖ ^ 2) ^ 3 := by ring
  have hnorm : ‖2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i‖ = 2 * π * |η j| * ‖f η i‖ := by
    simp [abs_of_pos Real.pi_pos]
  have hj : |η j| ^ 2 ≤ hsWeight 3 η := (pow_le_pow_left₀ (abs_nonneg _) h3 2).trans hw
  calc ‖2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i‖ ^ 2
      = 4 * π ^ 2 * |η j| ^ 2 * ‖f η i‖ ^ 2 := by rw [hnorm]; ring
    _ ≤ 4 * π ^ 2 * hsWeight 3 η * ‖f η‖ ^ 2 := by
      have hf2 : ‖f η i‖ ^ 2 ≤ ‖f η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h4 := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ 4 * π ^ 2)
      exact mul_le_mul h4 hf2 (sq_nonneg _) (mul_nonneg (by positivity) hw0)

private theorem continuousWithinAt_convC {F : ℝ → Space → CSpace} {a b : ℝ}
    (h3 : IsHsCurve 3 F a b) (j i : Fin 3) (ξ : Space) {s₀ : ℝ} (hs₀ : s₀ ∈ Icc a b) :
    ContinuousWithinAt (fun s => convC (fun η => F s η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * F s η i) ξ) (Icc a b) s₀ := by
  set gg : ℝ → Space → ℂ := fun s η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * F s η i with hgg
  have hc : Continuous fun η : Space => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) := by
    have := continuous_coordR j
    fun_prop
  have hmC : ∀ s ∈ Icc a b, ∀ k : Fin 3, AEStronglyMeasurable (fun η => F s η k) volume :=
    fun s hs k => (continuous_coordC k).comp_aestronglyMeasurable (h3.1 s hs).1
  have hmemp : ∀ s ∈ Icc a b, MemLp (fun η => F s η j) 2 volume := fun s hs =>
    memLp_two_of_lintegral (hmC s hs j) ((lintegral_coord_le _ j).trans_lt (h3.1 s hs).2)
  have hmemg : ∀ s ∈ Icc a b, MemLp (gg s) 2 volume := fun s hs =>
    memLp_two_of_lintegral (hc.aestronglyMeasurable.mul (hmC s hs i))
      ((lintegral_grad_le _ j i).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h3.1 s hs).2))
  have hmemq : ∀ s ∈ Icc a b, MemLp (fun η => gg s (ξ - η)) 2 volume := fun s hs =>
    (hmemg s hs).comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
  have tp : Tendsto (fun s => ∫⁻ η, ‖F s η j - F s₀ η j‖ₑ ^ 2) (𝓝[Icc a b] s₀) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h3.2 s₀ hs₀)
      (fun _ => zero_le) fun s => ?_
    have e : (fun η => ‖F s η j - F s₀ η j‖ₑ ^ 2) = fun η => ‖(F s - F s₀) η j‖ₑ ^ 2 := by
      funext η
      simp
    rw [e]
    exact lintegral_coord_le _ j
  have tq : Tendsto (fun s => ∫⁻ η, ‖gg s (ξ - η) - gg s₀ (ξ - η)‖ₑ ^ 2) (𝓝[Icc a b] s₀) (𝓝 0) := by
    have hlim : Tendsto (fun s => ENNReal.ofReal (4 * π ^ 2) * hsNormSq 3 (F s - F s₀))
        (𝓝[Icc a b] s₀) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (h3.2 s₀ hs₀) (Or.inr (ENNReal.ofReal_ne_top (r := 4 * π ^ 2)))
      rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun s => ?_
    rw [lintegral_sub_left_eq_self (fun η => ‖gg s η - gg s₀ η‖ₑ ^ 2) ξ]
    have e : (fun η => ‖gg s η - gg s₀ η‖ₑ ^ 2) =
        fun η => ‖2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * (F s - F s₀) η i‖ₑ ^ 2 := by
      funext η
      simp [hgg, mul_sub]
    rw [e]
    exact lintegral_grad_le _ j i
  exact tendsto_integral_mul hs₀ hmemp hmemq tp tq

private theorem continuousOn_nonlinSymbol {F : ℝ → Space → CSpace} {a b : ℝ}
    (h3 : IsHsCurve 3 F a b) (ξ : Space) :
    ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc a b) := by
  have hA : ContinuousOn (fun s => advectionSymbol (F s) ξ) (Icc a b) := by
    unfold advectionSymbol advectionBilin
    exact (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i =>
      continuousOn_finsetSum _ fun j _ => fun s hs => continuousWithinAt_convC h3 j i ξ hs)
  have hL : Continuous (divFreeC ξ) := by
    unfold divFreeC
    have := continuous_coordC
    fun_prop
  unfold nonlinSymbol
  exact (hL.comp_continuousOn hA).neg

theorem aemeasurable_enorm_nonlinSymbol {F : ℝ → Space → CSpace} {a b : ℝ}
    (h3 : IsHsCurve 3 F a b) (hs : ∀ t ∈ Icc a b, IsSolenoidalSymbol (F t)) :
    AEMeasurable (fun p : ℝ × Space => ‖nonlinSymbol (F p.1) p.2‖ₑ)
      ((volume.restrict (Icc a b)).prod volume) := by
  rcases lt_or_ge b a with hba | hab
  · have h0 : volume.restrict (Icc a b) = 0 := by
      rw [Icc_eq_empty (not_le.mpr hba), Measure.restrict_empty]
    rw [h0, Measure.zero_prod]
    exact aemeasurable_zero_measure
  set c : ℝ → ℝ := fun s => (projIcc a b hab s : ℝ) with hcdef
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcm : ∀ s, c s ∈ Icc a b := fun s => (projIcc a b hab s).2
  have hmeas : Measurable (Function.uncurry fun s ξ => ‖nonlinSymbol (F (c s)) ξ‖ₑ) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun ξ => ?_) (fun s => ?_)
    · exact continuous_enorm.comp ((continuousOn_nonlinSymbol h3 ξ).comp_continuous hc hcm)
    · exact (measurable_nonlinSymbol (h3.1 (c s) (hcm s)).1).enorm
  refine hmeas.aemeasurable.congr ?_
  have hae : ∀ᵐ p ∂((volume.restrict (Icc a b)).prod volume), p.1 ∈ Icc a b :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc a b)) (ν := (volume : Measure Space))).ae
      (p := fun s => s ∈ Icc a b) (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hae] with p hp
  simp only [Function.uncurry, hcdef, projIcc_of_mem hab hp]

end Breakdown.SmoothFlow
