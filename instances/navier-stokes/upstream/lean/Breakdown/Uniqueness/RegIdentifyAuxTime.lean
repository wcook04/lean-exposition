import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal

lemma lintegral_comp_sub_left (g : Space → ℝ≥0∞) (ξ : Space) :
    ∫⁻ η, g (ξ - η) = ∫⁻ η, g η :=
  (Measure.measurePreserving_sub_left (volume : Measure Space) ξ).lintegral_comp_emb
    (MeasurableEquiv.subLeft ξ).measurableEmbedding g

lemma enorm_convC_le (u v : Space → ℂ) (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (ξ : Space) :
    ‖convC u v ξ‖ₑ ≤ (∫⁻ η, ‖u η‖ₑ ^ 2) ^ (1 / (2 : ℝ)) * (∫⁻ η, ‖v η‖ₑ ^ 2) ^ (1 / (2 : ℝ)) := by
  have hv' : AEStronglyMeasurable (fun η => v (ξ - η)) volume :=
    hv.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Space)
    Real.HolderConjugate.two_two hu.enorm hv'.enorm
  simp only [ENNReal.rpow_two, Pi.mul_apply] at hH
  calc ‖convC u v ξ‖ₑ ≤ ∫⁻ η, ‖u η * v (ξ - η)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ η, ‖u η‖ₑ * ‖v (ξ - η)‖ₑ := by simp only [enorm_mul]
    _ ≤ (∫⁻ η, ‖u η‖ₑ ^ 2) ^ (1 / (2 : ℝ)) * (∫⁻ η, ‖v (ξ - η)‖ₑ ^ 2) ^ (1 / (2 : ℝ)) := hH
    _ = _ := by rw [lintegral_comp_sub_left (fun η => ‖v η‖ₑ ^ 2) ξ]

lemma convC_sub_eq {u v u₀ v₀ : Space → ℂ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hu₀ : MemLp u₀ 2 volume) (hv₀ : MemLp v₀ 2 volume) (ξ : Space) :
    convC u v ξ - convC u₀ v₀ ξ =
      convC (u - u₀) (v - v₀) ξ + convC (u - u₀) v₀ ξ + convC u₀ (v - v₀) ξ := by
  have hsub := Measure.measurePreserving_sub_left (volume : Measure Space) ξ
  have hi : ∀ {a b : Space → ℂ}, MemLp a 2 volume → MemLp b 2 volume →
      Integrable (fun η => a η * b (ξ - η)) volume :=
    fun ha hb => ha.integrable_mul (hb.comp_measurePreserving hsub)
  have h3 : Integrable (fun η => (u - u₀) η * (v - v₀) (ξ - η) + (u - u₀) η * v₀ (ξ - η))
      volume := (hi (hu.sub hu₀) (hv.sub hv₀)).add (hi (hu.sub hu₀) hv₀)
  simp only [convC]
  rw [← integral_sub (hi hu hv) (hi hu₀ hv₀),
    ← integral_add (hi (hu.sub hu₀) (hv.sub hv₀)) (hi (hu.sub hu₀) hv₀),
    ← integral_add h3 (hi hu₀ (hv.sub hv₀))]
  congr 1
  funext η
  simp only [Pi.sub_apply]
  ring

lemma tendsto_rpow_half_zero {l : Filter ℝ} {Y : ℝ → ℝ≥0∞} (h : Tendsto Y l (𝓝 0)) :
    Tendsto (fun s => Y s ^ (1 / (2 : ℝ))) l (𝓝 0) := by
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  exact this.comp h

lemma tendsto_convC {S : Set ℝ} {t : ℝ} {u v : ℝ → Space → ℂ}
    (hm : ∀ s ∈ S, MemLp (u s) 2 volume ∧ MemLp (v s) 2 volume) (ht : t ∈ S)
    (hu : Tendsto (fun s => ∫⁻ η, ‖(u s - u t) η‖ₑ ^ 2) (𝓝[S] t) (𝓝 0))
    (hv : Tendsto (fun s => ∫⁻ η, ‖(v s - v t) η‖ₑ ^ 2) (𝓝[S] t) (𝓝 0)) (ξ : Space) :
    Tendsto (fun s => convC (u s) (v s) ξ) (𝓝[S] t) (𝓝 (convC (u t) (v t) ξ)) := by
  rw [tendsto_iff_edist_tendsto_0]
  set X : ℝ → ℝ≥0∞ := fun s => (∫⁻ η, ‖(u s - u t) η‖ₑ ^ 2) ^ (1 / (2 : ℝ))
  set Y : ℝ → ℝ≥0∞ := fun s => (∫⁻ η, ‖(v s - v t) η‖ₑ ^ 2) ^ (1 / (2 : ℝ))
  set A : ℝ≥0∞ := (∫⁻ η, ‖u t η‖ₑ ^ 2) ^ (1 / (2 : ℝ))
  set B : ℝ≥0∞ := (∫⁻ η, ‖v t η‖ₑ ^ 2) ^ (1 / (2 : ℝ))
  have hfin : ∀ {w : Space → ℂ}, MemLp w 2 volume → (∫⁻ η, ‖w η‖ₑ ^ 2) ^ (1 / (2 : ℝ)) ≠ ⊤ := by
    intro w hw
    have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top).1 hw.2
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h2
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) h2.ne
  have hA : A ≠ ⊤ := hfin (hm t ht).1
  have hB : B ≠ ⊤ := hfin (hm t ht).2
  have hX : Tendsto X (𝓝[S] t) (𝓝 0) := tendsto_rpow_half_zero hu
  have hY : Tendsto Y (𝓝[S] t) (𝓝 0) := tendsto_rpow_half_zero hv
  have hG : Tendsto (fun s => X s * Y s + X s * B + A * Y s) (𝓝[S] t) (𝓝 0) := by
    have h1 : Tendsto (fun s => X s * Y s) (𝓝[S] t) (𝓝 (0 * 0)) :=
      ENNReal.Tendsto.mul hX (Or.inr ENNReal.zero_ne_top) hY (Or.inr ENNReal.zero_ne_top)
    have h2 : Tendsto (fun s => X s * B) (𝓝[S] t) (𝓝 (0 * B)) :=
      ENNReal.Tendsto.mul_const hX (Or.inr hB)
    have h3 : Tendsto (fun s => A * Y s) (𝓝[S] t) (𝓝 (A * 0)) :=
      ENNReal.Tendsto.const_mul hY (Or.inr hA)
    simpa using (h1.add h2).add h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  obtain ⟨hus, hvs⟩ := hm s hs
  obtain ⟨hut, hvt⟩ := hm t ht
  rw [edist_eq_enorm_sub, convC_sub_eq hus hvs hut hvt]
  calc ‖convC (u s - u t) (v s - v t) ξ + convC (u s - u t) (v t) ξ + convC (u t) (v s - v t) ξ‖ₑ
      ≤ ‖convC (u s - u t) (v s - v t) ξ‖ₑ + ‖convC (u s - u t) (v t) ξ‖ₑ +
          ‖convC (u t) (v s - v t) ξ‖ₑ := by
        refine (enorm_add_le _ _).trans ?_
        gcongr
        exact enorm_add_le _ _
    _ ≤ X s * Y s + X s * B + A * Y s := by
        gcongr
        · exact enorm_convC_le _ _ (hus.sub hut).1 (hvs.sub hvt).1 ξ
        · exact enorm_convC_le _ _ (hus.sub hut).1 hvt.1 ξ
        · exact enorm_convC_le _ _ hut.1 (hvs.sub hvt).1 ξ

lemma component_sq_le (f : Space → CSpace) (η : Space) (i : Fin 3) :
    ‖f η i‖ₑ ^ 2 ≤ ENNReal.ofReal (hsWeight 1 η) * ‖f η‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by unfold hsWeight; positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖f η i‖ ^ 2 ≤ ‖f η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (f η) i) 2
  have h2 : (1 : ℝ) ≤ hsWeight 1 η := by unfold hsWeight; nlinarith [sq_nonneg ‖η‖]
  nlinarith [sq_nonneg ‖f η‖]

lemma coord_sq_le (c : ℂ) (f : Space → CSpace) (η : Space) (i j : Fin 3) :
    ‖c * ((η j : ℝ) : ℂ) * f η i‖ₑ ^ 2 ≤
      ‖c‖ₑ ^ 2 * (ENNReal.ofReal (hsWeight 1 η) * ‖f η‖ₑ ^ 2) := by
  rw [show c * ((η j : ℝ) : ℂ) * f η i = c * (((η j : ℝ) : ℂ) * f η i) by ring, enorm_mul,
    mul_pow]
  gcongr
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by unfold hsWeight; positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul, Complex.norm_real, mul_pow]
  have h1 : ‖f η i‖ ^ 2 ≤ ‖f η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (f η) i) 2
  have h1' : ‖η j‖ ^ 2 ≤ ‖η‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le η j) 2
  have h3 : ‖η j‖ ^ 2 * ‖f η i‖ ^ 2 ≤ ‖η‖ ^ 2 * ‖f η‖ ^ 2 :=
    mul_le_mul h1' h1 (by positivity) (by positivity)
  unfold hsWeight
  nlinarith [sq_nonneg ‖f η‖]

lemma lintegral_component_le (f : Space → CSpace) (i : Fin 3) :
    ∫⁻ η, ‖f η i‖ₑ ^ 2 ≤ hsNormSq 1 f :=
  lintegral_mono fun η => component_sq_le f η i

lemma lintegral_coord_le (c : ℂ) (f : Space → CSpace) (i j : Fin 3) :
    ∫⁻ η, ‖c * ((η j : ℝ) : ℂ) * f η i‖ₑ ^ 2 ≤ ‖c‖ₑ ^ 2 * hsNormSq 1 f := by
  rw [hsNormSq, ← lintegral_const_mul' _ _ (by simp)]
  exact lintegral_mono fun η => coord_sq_le c f η i j

lemma memLp_of_lintegral_sq {w : Space → ℂ} (hw : AEStronglyMeasurable w volume)
    (h : ∫⁻ η, ‖w η‖ₑ ^ 2 < ⊤) : MemLp w 2 volume := by
  refine ⟨hw, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa using h

lemma aestronglyMeasurable_component {f : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (i : Fin 3) : AEStronglyMeasurable (fun η => f η i) volume :=
  (PiLp.continuous_apply 2 _ i).comp_aestronglyMeasurable hf

lemma aestronglyMeasurable_coord {f : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (c : ℂ) (i j : Fin 3) : AEStronglyMeasurable (fun η => c * ((η j : ℝ) : ℂ) * f η i) volume :=
  (aestronglyMeasurable_const.mul
    (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)).aestronglyMeasurable).mul
    (aestronglyMeasurable_component hf i)

lemma tendsto_convC_component {T : ℝ} {F : ℝ → Space → CSpace} (hF : IsHsCurve 1 F 0 T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (c : ℂ) (i j : Fin 3) (ξ : Space) :
    Tendsto (fun s => convC (fun η => F s η j) (fun η => c * ((η j : ℝ) : ℂ) * F s η i) ξ)
      (𝓝[Icc 0 T] t)
      (𝓝 (convC (fun η => F t η j) (fun η => c * ((η j : ℝ) : ℂ) * F t η i) ξ)) := by
  have hc : ‖c‖ₑ ^ 2 ≠ ⊤ := by simp
  refine tendsto_convC (u := fun s η => F s η j) (v := fun s η => c * ((η j : ℝ) : ℂ) * F s η i)
    (fun s hs => ⟨?_, ?_⟩) ht ?_ ?_ ξ
  · exact memLp_of_lintegral_sq (aestronglyMeasurable_component (hF.1 s hs).1 j)
      ((lintegral_component_le _ j).trans_lt (hF.1 s hs).2)
  · exact memLp_of_lintegral_sq (aestronglyMeasurable_coord (hF.1 s hs).1 c i j)
      ((lintegral_coord_le c _ i j).trans_lt (ENNReal.mul_lt_top hc.lt_top (hF.1 s hs).2))
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hF.2 t ht)
      (fun _ => bot_le) (fun s => ?_)
    have heq : ∀ η, ((fun η => F s η j) - fun η => F t η j) η = (F s - F t) η j := fun η => by
      simp
    simp only [heq]
    exact lintegral_component_le _ j
  · have h0 : Tendsto (fun s => ‖c‖ₑ ^ 2 * hsNormSq 1 (F s - F t)) (𝓝[Icc 0 T] t) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hF.2 t ht) (Or.inr hc)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun _ => bot_le) (fun s => ?_)
    have heq : ∀ η, ((fun η => c * ((η j : ℝ) : ℂ) * F s η i) -
        fun η => c * ((η j : ℝ) : ℂ) * F t η i) η = c * ((η j : ℝ) : ℂ) * (F s - F t) η i :=
      fun η => by simp [mul_sub]
    simp only [heq]
    exact lintegral_coord_le c _ i j

lemma continuous_divFreeC (ξ : Space) : Continuous (divFreeC ξ) := by
  unfold divFreeC
  fun_prop

lemma convC_congr {u u' v v' : Space → ℂ} (hu : u =ᵐ[volume] u') (hv : v =ᵐ[volume] v')
    (ξ : Space) : convC u v ξ = convC u' v' ξ := by
  unfold convC
  apply integral_congr_ae
  have hv' : (fun η => v (ξ - η)) =ᵐ[volume] fun η => v' (ξ - η) :=
    (Measure.measurePreserving_sub_left (volume : Measure Space) ξ).quasiMeasurePreserving.ae_eq_comp hv
  filter_upwards [hu, hv'] with η h1 h2
  change v (ξ - η) = v' (ξ - η) at h2
  rw [h1, h2]

lemma stronglyMeasurable_convC {u v : Space → ℂ} (hu : StronglyMeasurable u)
    (hv : StronglyMeasurable v) : StronglyMeasurable (convC u v) := by
  unfold convC
  exact StronglyMeasurable.integral_prod_right (f := fun ξ η => u η * v (ξ - η))
    ((hu.comp_measurable measurable_snd).mul (hv.comp_measurable (measurable_fst.sub measurable_snd)))

lemma stronglyMeasurable_nonlinSymbol {f : Space → CSpace} (hf : AEStronglyMeasurable f volume) :
    StronglyMeasurable (nonlinSymbol f) := by
  set f' := hf.mk f
  have hf' : StronglyMeasurable f' := hf.stronglyMeasurable_mk
  have h1 : ∀ j : Fin 3, (fun η => f η j) =ᵐ[volume] fun η => f' η j := fun j =>
    hf.ae_eq_mk.mono fun η h => congrArg (fun z : CSpace => z j) h
  have h2 : ∀ i j : Fin 3, (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f η i) =ᵐ[volume]
      fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * f' η i := fun i j =>
    hf.ae_eq_mk.mono fun η h =>
      congrArg (fun z : CSpace => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * z i) h
  have hA : advectionSymbol f = advectionSymbol f' := by
    funext ξ
    simp only [advectionSymbol, advectionBilin]
    congr 1
    funext i
    exact Finset.sum_congr rfl fun j _ => convC_congr (h1 j) (h2 i j) ξ
  have hcm : ∀ i : Fin 3, Measurable fun η => f' η i := fun i =>
    (PiLp.continuous_apply 2 _ i).measurable.comp hf'.measurable
  have hAm : Measurable (advectionSymbol f') := by
    unfold advectionSymbol advectionBilin
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
    refine Finset.measurable_sum _ fun j _ => (stronglyMeasurable_convC ?_ ?_).measurable
    · exact (hcm j).stronglyMeasurable
    · exact ((measurable_const.mul (Complex.measurable_ofReal.comp
        (PiLp.continuous_apply 2 _ j).measurable)).mul (hcm i)).stronglyMeasurable
  have hAi : ∀ i : Fin 3, Measurable fun ξ => advectionSymbol f' ξ i := fun i =>
    (PiLp.continuous_apply 2 _ i).measurable.comp hAm
  have hxi : ∀ i : Fin 3, Measurable fun ξ : Space => ((ξ i : ℝ) : ℂ) := fun i =>
    Complex.measurable_ofReal.comp (PiLp.continuous_apply 2 _ i).measurable
  have hn : Measurable fun ξ : Space => (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have hfv : Measurable freqVec := complexifyVec.continuous.measurable
  unfold nonlinSymbol
  rw [hA]
  refine Measurable.stronglyMeasurable ?_
  unfold divFreeC
  exact (hAm.sub ((hn.mul (Finset.measurable_sum _ fun i _ => (hxi i).mul (hAi i))).smul hfv)).neg

end Internal

open Internal

theorem continuousOn_nonlinSymbol_apply {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) (ξ : Space) :
    ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc 0 T) := by
  intro t ht
  unfold nonlinSymbol
  refine ((continuous_divFreeC ξ).tendsto _).comp ?_ |>.neg
  unfold advectionSymbol advectionBilin
  refine (PiLp.continuous_toLp 2 _).tendsto _ |>.comp (tendsto_pi_nhds.2 fun i => ?_)
  exact tendsto_finsetSum _ fun j _ =>
    tendsto_convC_component (hF 1) ht (2 * (π : ℂ) * Complex.I) i j ξ

theorem aestronglyMeasurable_uncurry_nonlinSymbol {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) :
    AEStronglyMeasurable (Function.uncurry fun s ξ => nonlinSymbol (F s) ξ)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  by_cases hT : 0 ≤ T
  swap
  · rw [Icc_eq_empty (by linarith), Measure.restrict_empty, Measure.zero_prod]
    exact aestronglyMeasurable_zero_measure _
  set G : ℝ → Space → CSpace := fun s => nonlinSymbol (F (projIcc 0 T hT s))
  have hGc : ∀ ξ, Continuous fun s => G s ξ := fun ξ =>
    (continuousOn_nonlinSymbol_apply hF hs ξ).comp_continuous
      (continuous_subtype_val.comp continuous_projIcc) (fun s => (projIcc 0 T hT s).2)
  have hGm : ∀ s, StronglyMeasurable (G s) := fun s =>
    stronglyMeasurable_nonlinSymbol ((hF 0).1 _ (projIcc 0 T hT s).2).1
  have hJ := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hGc hGm
  have hae : ∀ᵐ p ∂((volume.restrict (Icc 0 T)).prod (volume : Measure Space)), p.1 ∈ Icc 0 T := by
    rw [ae_iff]
    have hset : {p : ℝ × Space | ¬ p.1 ∈ Icc 0 T} = (Icc 0 T)ᶜ ×ˢ univ := by
      ext p
      simp
    rw [hset, Measure.prod_prod, Measure.restrict_apply measurableSet_Icc.compl, compl_inter_self,
      measure_empty, zero_mul]
  refine hJ.aestronglyMeasurable.congr ?_
  filter_upwards [hae] with p hp
  simp only [Function.uncurry, G, projIcc_of_mem hT hp]

end Breakdown.SmoothFlow
