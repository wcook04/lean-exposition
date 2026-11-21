import Breakdown.CertTorus.RegularStatements
import Breakdown.Uniqueness.RegIdentifyAuxHeat
import Breakdown.Uniqueness.RegIdentifyAuxDivFree
import Breakdown.Uniqueness.RegIdentifyAuxSymbol
import Breakdown.Uniqueness.RegIdentifyAuxTime

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology InnerProductSpace ComplexConjugate

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

private theorem floor_step_mem {a s h : ℝ} (hh : 0 < h) (hs : a ≤ s) :
    a ≤ a + h * ⌊(s - a) / h⌋ ∧ a + h * ⌊(s - a) / h⌋ ≤ s ∧ s - (a + h * ⌊(s - a) / h⌋) < h := by
  have h0 : 0 ≤ (s - a) / h := div_nonneg (sub_nonneg.2 hs) hh.le
  have h1 : ((⌊(s - a) / h⌋ : ℤ) : ℝ) ≤ (s - a) / h := Int.floor_le _
  have h2 : (s - a) / h < ((⌊(s - a) / h⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (0 : ℝ) ≤ ((⌊(s - a) / h⌋ : ℤ) : ℝ) := by exact_mod_cast Int.floor_nonneg.2 h0
  have e : h * ((s - a) / h) = s - a := by field_simp
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

private theorem exists_joint_version {a b : ℝ} {c : ℝ → L2C} (hc : ContinuousOn c (Icc a b)) :
    ∃ L : ℝ × Space → CSpace, StronglyMeasurable L ∧
      ∀ s ∈ Icc a b, (fun ξ => L (s, ξ)) =ᵐ[volume] (c s : Space → CSpace) := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff] at hu
  have hδ : ∀ k : ℕ, ∃ δ > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, dist x y < δ →
      dist (c x) (c y) < (2⁻¹ : ℝ) ^ k := fun k => hu _ (by positivity)
  choose δ hδpos hδ using hδ
  set q : ℕ → ℝ → ℝ := fun k s => a + δ k / 2 * ⌊(s - a) / (δ k / 2)⌋ with hq
  set Ψ : ℕ → ℝ × Space → CSpace := fun k p => (c (q k p.1) : Space → CSpace) p.2 with hΨ
  have hΨm : ∀ k, StronglyMeasurable (Ψ k) := by
    intro k
    have hf : Measurable (fun p : ℤ × Space => (c (a + δ k / 2 * p.1) : Space → CSpace) p.2) :=
      measurable_from_prod_countable_right (fun m =>
        (Lp.stronglyMeasurable (c (a + δ k / 2 * m))).measurable)
    have hfl : Measurable (fun p : ℝ × Space => ((⌊(p.1 - a) / (δ k / 2)⌋ : ℤ), p.2)) :=
      (((measurable_fst.sub_const a).div_const _).floor).prodMk measurable_snd
    exact (hf.comp hfl).stronglyMeasurable
  have hstep : ∀ k, ∀ s ∈ Icc a b, ‖c (q k s) - c s‖ₑ ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k s hs
    have hh : 0 < δ k / 2 := by linarith [hδpos k]
    obtain ⟨m1, m2, m3⟩ := floor_step_mem hh hs.1
    change a ≤ q k s at m1
    change q k s ≤ s at m2
    change s - q k s < δ k / 2 at m3
    have hmem : q k s ∈ Icc a b := ⟨m1, m2.trans hs.2⟩
    have hd : dist (q k s) s < δ k := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith [hδpos k]
    have h1 := hδ k (q k s) hmem s hs hd
    rw [dist_eq_norm] at h1
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖c (q k s) - c s‖ ≤ ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) :=
          ENNReal.ofReal_le_ofReal h1.le
      _ = (2⁻¹ : ℝ≥0∞) ^ k := by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
  have hconv : ∀ s ∈ Icc a b, ∀ᵐ ξ ∂volume,
      Tendsto (fun k => Ψ k (s, ξ)) atTop (𝓝 ((c s : Space → CSpace) ξ)) := by
    intro s hs
    set e : ℕ → Space → ℝ≥0∞ := fun k ξ => ‖Ψ k (s, ξ) - (c s : Space → CSpace) ξ‖ₑ ^ (2 : ℝ)
    have hemm : ∀ k, Measurable (e k) := fun k =>
      (((hΨm k).comp_measurable measurable_prodMk_left).measurable.sub
        (Lp.stronglyMeasurable (c s)).measurable).enorm.pow_const _
    have hem : ∀ k, AEMeasurable (e k) volume := fun k => (hemm k).aemeasurable
    have hle : ∀ k, ∫⁻ ξ, e k ξ ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
      intro k
      have hae : (fun ξ => e k ξ) =ᵐ[volume]
          fun ξ => ‖((c (q k s) - c s : L2C) : Space → CSpace) ξ‖ₑ ^ (2 : ℝ) := by
        filter_upwards [Lp.coeFn_sub (c (q k s)) (c s)] with ξ hξ
        simp only [e, hΨ, hξ, Pi.sub_apply]
      have hn : eLpNorm' (((c (q k s) - c s : L2C) : Space → CSpace)) 2 volume =
          ‖c (q k s) - c s‖ₑ := by
        rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
        simp
      rw [lintegral_congr_ae hae, lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num), hn]
      have hb := hstep k s hs
      have h1 : ‖c (q k s) - c s‖ₑ ≤ 1 :=
        hb.trans (pow_le_one₀ (by norm_num) (by norm_num))
      exact (ENNReal.rpow_le_self_of_le_one h1 (by norm_num)).trans hb
    have hsum : ∫⁻ ξ, ∑' k, e k ξ ∂volume ≠ ⊤ := by
      rw [lintegral_tsum hem]
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
      rw [ENNReal.tsum_geometric]
      simp
    have hfin := ae_lt_top' (Measurable.tsum hemm).aemeasurable hsum
    filter_upwards [hfin] with ξ hξ
    have h0 : Tendsto (fun k => e k ξ) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hξ.ne
    have h1 : Tendsto (fun k => (e k ξ) ^ (2⁻¹ : ℝ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (2⁻¹ : ℝ))).tendsto 0).comp h0
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
      exact this
    rw [tendsto_iff_edist_tendsto_0]
    refine h1.congr fun k => ?_
    simp only [e, edist_eq_enorm_sub]
    rw [← ENNReal.rpow_mul]
    norm_num
  refine ⟨fun p => limUnder atTop (fun k => Ψ k p), StronglyMeasurable.limUnder hΨm, ?_⟩
  intro s hs
  filter_upwards [hconv s hs] with ξ hξ
  exact hξ.limUnder_eq

private theorem lintegral_restrict_enorm_le (f : L2C) (K : Set Space) :
    ∫⁻ ξ in K, ‖(f : Space → CSpace) ξ‖ₑ ≤ ‖f‖ₑ * volume K ^ (2⁻¹ : ℝ) := by
  have hm : AEStronglyMeasurable (f : Space → CSpace) (volume.restrict K) :=
    (Lp.aestronglyMeasurable f).restrict
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm
  rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at h1
  refine h1.trans ?_
  have h2 : eLpNorm (f : Space → CSpace) 2 (volume.restrict K) ≤ ‖f‖ₑ := by
    rw [Lp.enorm_def]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have h3 : (1 : ℝ≥0∞).toReal⁻¹ - (2 : ℝ≥0∞).toReal⁻¹ = 2⁻¹ := by norm_num
  simp only [one_div] at h3 ⊢
  rw [h3]
  gcongr

private theorem integrable_prod_restrict {S : Set ℝ} {c : ℝ → L2C} (hc : IntegrableOn c S)
    {g : ℝ → Space → CSpace}
    (hg : AEStronglyMeasurable (Function.uncurry g) ((volume.restrict S).prod volume))
    (hcg : ∀ᵐ s ∂(volume.restrict S), (c s : Space → CSpace) =ᵐ[volume] g s)
    {K : Set Space} (hKf : volume K < ⊤) :
    Integrable (Function.uncurry g) ((volume.restrict S).prod (volume.restrict K)) := by
  have hm : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict S).prod (volume.restrict K)) := by
    have e : (volume.restrict S).prod (volume.restrict K) =
        ((volume.restrict S).prod volume).restrict (univ ×ˢ K) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    exact hg.restrict
  refine ⟨hm, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hm.enorm]
  have hb : ∀ᵐ s ∂(volume.restrict S), ∫⁻ ξ in K, ‖Function.uncurry g (s, ξ)‖ₑ ≤
      ‖c s‖ₑ * volume K ^ (2⁻¹ : ℝ) := by
    filter_upwards [hcg] with s hs
    have e : ∫⁻ ξ in K, ‖Function.uncurry g (s, ξ)‖ₑ = ∫⁻ ξ in K, ‖(c s : Space → CSpace) ξ‖ₑ := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hs] with ξ hξ
      simp [Function.uncurry, hξ]
    rw [e]
    exact lintegral_restrict_enorm_le (c s) K
  refine (lintegral_mono_ae hb).trans_lt ?_
  rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKf.ne)]
  exact ENNReal.mul_lt_top hc.2 (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKf.ne)

private theorem coeFn_setIntegral_ae {S : Set ℝ} {c : ℝ → L2C} (hc : IntegrableOn c S)
    {g : ℝ → Space → CSpace}
    (hg : AEStronglyMeasurable (Function.uncurry g) ((volume.restrict S).prod volume))
    (hcg : ∀ᵐ s ∂(volume.restrict S), (c s : Space → CSpace) =ᵐ[volume] g s) :
    ((∫ s in S, c s : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => ∫ s in S, g s ξ := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun K hK hKf => ?_) (fun K hK hKf => ?_)
    (fun K hK hKf => ?_)
  · have : IsFiniteMeasure (volume.restrict K) := ⟨by rwa [Measure.restrict_apply_univ]⟩
    exact ((Lp.memLp _).restrict K).integrable (by norm_num)
  · exact (integrable_prod_restrict hc hg hcg hKf).integral_prod_right
  · have hKi := integrable_prod_restrict hc hg hcg hKf
    have hFi : IntegrableOn ((∫ s in S, c s : L2C) : Space → CSpace) K := by
      have : IsFiniteMeasure (volume.restrict K) := ⟨by rwa [Measure.restrict_apply_univ]⟩
      exact ((Lp.memLp _).restrict K).integrable (by norm_num)
    have hGi : IntegrableOn (fun ξ => ∫ s in S, g s ξ) K := hKi.integral_prod_right
    refine ext_inner_left ℂ fun v => ?_
    rw [← integral_inner hFi v, ← integral_inner hGi v,
      ← L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ _ hK v hKf.ne, ← integral_inner hc]
    have h2 : ∀ᵐ s ∂(volume.restrict S), ⟪indicatorConstLp 2 hK hKf.ne v, c s⟫_ℂ =
        ∫ ξ in K, ⟪v, g s ξ⟫_ℂ := by
      filter_upwards [hcg] with s hs
      rw [L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ _ hK v hKf.ne]
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hs] with ξ hξ
      rw [hξ]
    have hvi : Integrable (Function.uncurry fun s ξ => ⟪v, g s ξ⟫_ℂ)
        ((volume.restrict S).prod (volume.restrict K)) := hKi.const_inner v
    rw [integral_congr_ae h2, integral_integral_swap hvi]
    refine integral_congr_ae ?_
    filter_upwards [hKi.prod_left_ae] with ξ hξ
    exact integral_inner hξ v

private theorem measurable_divFreeC_pair : Measurable fun q : Space × CSpace => divFreeC q.1 q.2 := by
  unfold divFreeC freqVec
  fun_prop

private theorem stronglyMeasurable_nonlinSymbol_param {W : ℝ × Space → CSpace}
    (hW : StronglyMeasurable W) :
    StronglyMeasurable (fun p : ℝ × Space => nonlinSymbol (fun η => W (p.1, η)) p.2) := by
  have hc : ∀ i : Fin 3, Measurable fun p : ℝ × Space => W p i := fun i =>
    (PiLp.continuous_apply 2 _ i).measurable.comp hW.measurable
  have hconv : ∀ i j : Fin 3, Measurable fun p : ℝ × Space =>
      convC (fun η => W (p.1, η) j)
        (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * W (p.1, η) i) p.2 := by
    intro i j
    unfold convC
    refine (StronglyMeasurable.integral_prod_right
      (f := fun (p : ℝ × Space) (η : Space) => W (p.1, η) j *
        (2 * (π : ℂ) * Complex.I * ((((p.2 - η) : Space) j : ℝ) : ℂ) * W (p.1, p.2 - η) i))
      ?_).measurable
    refine Measurable.stronglyMeasurable ?_
    have m1 : Measurable fun r : (ℝ × Space) × Space => W (r.1.1, r.2) j :=
      (hc j).comp (measurable_fst.fst.prodMk measurable_snd)
    have m2 : Measurable fun r : (ℝ × Space) × Space => W (r.1.1, r.1.2 - r.2) i :=
      (hc i).comp (measurable_fst.fst.prodMk (measurable_fst.snd.sub measurable_snd))
    have m3 : Measurable fun r : (ℝ × Space) × Space => ((((r.1.2 - r.2) : Space) j : ℝ) : ℂ) :=
      (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).comp
        (continuous_fst.snd.sub continuous_snd))).measurable
    exact m1.mul ((measurable_const.mul m3).mul m2)
  have hadv : Measurable fun p : ℝ × Space => advectionSymbol (fun η => W (p.1, η)) p.2 := by
    unfold advectionSymbol advectionBilin
    exact (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ => hconv i j)
  unfold nonlinSymbol
  exact (measurable_divFreeC_pair.comp (measurable_snd.prodMk hadv)).neg.stronglyMeasurable

private theorem nonlinSymbol_congr {f f' : Space → CSpace} (h : f =ᵐ[volume] f') :
    nonlinSymbol f = nonlinSymbol f' := by
  have hA : advectionSymbol f = advectionSymbol f' := by
    funext ξ
    unfold advectionSymbol advectionBilin
    congr 1
    funext i
    refine Finset.sum_congr rfl fun j _ => Breakdown.SmoothFlow.Internal.convC_congr ?_ ?_ ξ
    · exact h.mono fun η hη => by simp only [hη]
    · exact h.mono fun η hη => by simp only [hη]
  funext ξ
  unfold nonlinSymbol
  rw [hA]

private theorem conjVec_conjVec (z : CSpace) : conjVec (conjVec z) = z := by
  ext i
  simp [conjVec]

private theorem conjVec_ofReal_smul (r : ℝ) (z : CSpace) :
    conjVec ((r : ℂ) • z) = (r : ℂ) • conjVec z := by
  ext i
  simp [conjVec]

private theorem lerayC_neg_conjVec (ξ : Space) (z : CSpace) :
    divFreeC (-ξ) (conjVec z) = conjVec (divFreeC ξ z) := by
  rw [← Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.conjVec_divFreeC_neg ξ z, conjVec_conjVec]

private theorem lerayC_add (ξ : Space) (z w : CSpace) :
    divFreeC ξ (z + w) = divFreeC ξ z + divFreeC ξ w := by
  ext i
  simp [divFreeC, mul_add, Finset.sum_add_distrib]
  ring

private theorem lerayC_smul (ξ : Space) (r : ℂ) (z : CSpace) :
    divFreeC ξ (r • z) = r • divFreeC ξ z := by
  unfold divFreeC
  have hs : ∑ i, ((ξ i : ℝ) : ℂ) * (r • z) i = r * ∑ i, ((ξ i : ℝ) : ℂ) * z i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hs, smul_sub, smul_smul]
  congr 2
  ring

private theorem lerayC_nonlinSymbol (f : Space → CSpace) (ξ : Space) :
    divFreeC ξ (nonlinSymbol f ξ) = nonlinSymbol f ξ := by
  have hneg : ∀ z : CSpace, -z = (-1 : ℂ) • z := fun z => by simp
  unfold nonlinSymbol
  rw [hneg, lerayC_smul, Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.divFreeC_eq_sub ξ (divFreeC ξ _), Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.longitudinal_divFreeC, sub_zero]

private theorem velSymbol_neg (x : X) (ξ : Space) : velSymbol x (-ξ) = conjVec (velSymbol x ξ) := by
  have hw : (1 / 2 : ℝ) • (symX x (-ξ) + conjVec (symX x (- -ξ))) =
      conjVec ((1 / 2 : ℝ) • (symX x ξ + conjVec (symX x (-ξ)))) := by
    rw [neg_neg, ContinuousLinearMap.map_smul, map_add, conjVec_conjVec, add_comm]
  simp only [velSymbol]
  rw [hw, lerayC_neg_conjVec, norm_neg, ContinuousLinearMap.map_smul]

private theorem advectionSymbol_neg_of_herm {f : Space → CSpace}
    (hf : ∀ η, f (-η) = conjVec (f η)) (ξ : Space) :
    advectionSymbol f (-ξ) = conjVec (advectionSymbol f ξ) := by
  ext i
  simp only [advectionSymbol, advectionBilin, PiLp.toLp_apply,
    Breakdown.SmoothFlow.Internal.conjVec_coord, map_sum]
  refine Finset.sum_congr rfl fun j _ =>
    Breakdown.SmoothFlow.Internal.convC_neg_conj (fun η => ?_) (fun η => ?_) ξ
  · rw [hf, Breakdown.SmoothFlow.Internal.conjVec_coord]
  · rw [hf, Breakdown.SmoothFlow.Internal.conjVec_coord]
    simp [map_mul, Complex.conj_ofReal, map_ofNat]

private theorem nonlinSymbol_neg_of_herm {f : Space → CSpace}
    (hf : ∀ η, f (-η) = conjVec (f η)) (ξ : Space) :
    nonlinSymbol f (-ξ) = conjVec (nonlinSymbol f ξ) := by
  unfold nonlinSymbol
  rw [advectionSymbol_neg_of_herm hf, lerayC_neg_conjVec, map_neg]

private theorem integral_conjVec {μ : Measure ℝ} (f : ℝ → CSpace) :
    ∫ s, conjVec (f s) ∂μ = conjVec (∫ s, f s ∂μ) := by
  by_cases hf : Integrable f μ
  · exact conjVec.integral_comp_comm hf
  · have hf' : ¬ Integrable (fun s => conjVec (f s)) μ := fun h =>
      hf (by simpa [conjVec_conjVec] using conjVec.integrable_comp h)
    rw [integral_undef hf, integral_undef hf', map_zero]

private theorem lerayC_integral {μ : Measure ℝ} {ξ : Space} {f : ℝ → CSpace}
    (hf : ∀ s, divFreeC ξ (f s) = f s) : divFreeC ξ (∫ s, f s ∂μ) = ∫ s, f s ∂μ := by
  have hl : ∀ s, longitudinal ξ (f s) = 0 := fun s => by
    rw [← hf s, Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.longitudinal_divFreeC]
  rw [Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.divFreeC_eq_sub, sub_eq_self]
  by_cases hi : Integrable f μ
  · rw [← (longitudinal ξ).integral_comp_comm hi]
    simp [hl]
  · rw [integral_undef hi, map_zero]

private theorem velSymbol_of_pointwise {μ : Measure ℝ} {Nf : ℝ → Space → CSpace} {h : ℝ → Space → ℝ}
    (hherm : ∀ s ξ, Nf s (-ξ) = conjVec (Nf s ξ)) (hfix : ∀ s ξ, divFreeC ξ (Nf s ξ) = Nf s ξ)
    (hh : ∀ s ξ, h s (-ξ) = h s ξ) {x y : X} {c : ℝ} {ξ : Space} (hξ : ξ ≠ 0)
    (h1 : symX y ξ = ((c : ℝ) : ℂ) • symX x ξ +
      ∫ s, ((2 * π * ‖ξ‖ * h s ξ : ℝ) : ℂ) • Nf s ξ ∂μ)
    (h2 : symX y (-ξ) = ((c : ℝ) : ℂ) • symX x (-ξ) +
      ∫ s, ((2 * π * ‖-ξ‖ * h s (-ξ) : ℝ) : ℂ) • Nf s (-ξ) ∂μ) :
    velSymbol y ξ = ((c : ℝ) : ℂ) • velSymbol x ξ + ∫ s, ((h s ξ : ℝ) : ℂ) • Nf s ξ ∂μ := by
  set J : CSpace := ∫ s, ((h s ξ : ℝ) : ℂ) • Nf s ξ ∂μ with hJ
  set r : ℝ := 2 * π * ‖ξ‖ with hr
  have hr0 : r ≠ 0 := by
    have : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    positivity
  have eI : ∫ s, ((2 * π * ‖ξ‖ * h s ξ : ℝ) : ℂ) • Nf s ξ ∂μ = r • J := by
    rw [hJ, ← integral_smul]
    congr 1
    funext s
    rw [Complex.ofReal_mul, mul_smul, Complex.coe_smul]
  have eI' : ∫ s, ((2 * π * ‖-ξ‖ * h s (-ξ) : ℝ) : ℂ) • Nf s (-ξ) ∂μ = conjVec (r • J) := by
    rw [← eI, ← integral_conjVec]
    congr 1
    funext s
    rw [norm_neg, hh, hherm, conjVec_ofReal_smul]
  have hJfix : divFreeC ξ J = J := by
    rw [hJ]
    refine lerayC_integral fun s => ?_
    rw [lerayC_smul, hfix]
  have key : (1 / 2 : ℝ) • (((c : ℝ) : ℂ) • symX x ξ + r • J +
      conjVec (((c : ℝ) : ℂ) • symX x (-ξ) + conjVec (r • J))) =
      ((c : ℝ) : ℂ) • ((1 / 2 : ℝ) • (symX x ξ + conjVec (symX x (-ξ)))) + r • J := by
    rw [map_add, conjVec_ofReal_smul, conjVec_conjVec]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  simp only [velSymbol]
  rw [h1, h2, eI, eI', key, lerayC_add, lerayC_smul, ← Complex.coe_smul r J, lerayC_smul, hJfix,
    smul_add, smul_comm ((2 * π * ‖ξ‖)⁻¹ : ℝ) ((c : ℝ) : ℂ)]
  congr 1
  rw [Complex.coe_smul, smul_smul, ← hr, inv_mul_cancel₀ hr0, one_smul]

private theorem velOfJoint_measurable {L : ℝ × Space → CSpace} (hL : StronglyMeasurable L) :
    StronglyMeasurable fun p : ℝ × Space => ((2 * π * ‖p.2‖)⁻¹ : ℝ) •
      divFreeC p.2 ((1 / 2 : ℝ) • (L (p.1, p.2) + conjVec (L (p.1, -p.2)))) := by
  have h1 : Measurable fun p : ℝ × Space => L (p.1, -p.2) :=
    hL.measurable.comp (measurable_fst.prodMk measurable_snd.neg)
  have h0 : Measurable fun p : ℝ × Space => L (p.1, p.2) :=
    hL.measurable.comp (measurable_fst.prodMk measurable_snd)
  have h2 : Measurable fun p : ℝ × Space =>
      (1 / 2 : ℝ) • (L (p.1, p.2) + conjVec (L (p.1, -p.2))) :=
    (h0.add (conjVec.continuous.measurable.comp h1)).const_smul (1 / 2 : ℝ)
  have h3 : Measurable fun p : ℝ × Space => ((2 * π * ‖p.2‖)⁻¹ : ℝ) := by fun_prop
  exact (h3.smul (measurable_divFreeC_pair.comp (measurable_snd.prodMk h2))).stronglyMeasurable

private theorem exists_joint_velSymbol {u : ℝ → X} {a b : ℝ} (hu : ContinuousOn u (Icc a b)) :
    ∃ V₀ : ℝ × Space → CSpace, StronglyMeasurable V₀ ∧
      ∀ s ∈ Icc a b, (fun ξ => V₀ (s, ξ)) =ᵐ[volume] velSymbol (u s) := by
  have hcont : ContinuousOn (fun s => ((u s : X) : L2C)) (Icc a b) :=
    continuous_subtype_val.comp_continuousOn hu
  obtain ⟨L, hLm, hL⟩ := exists_joint_version hcont
  refine ⟨_, velOfJoint_measurable hLm, fun s hs => ?_⟩
  have h1 := hL s hs
  have h2 : (fun ξ => L (s, -ξ)) =ᵐ[volume] fun ξ => ((u s : X) : L2C) (-ξ) :=
    (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with ξ e1 e2
  simp only [velSymbol, symX]
  rw [e1, e2]

private theorem exists_joint_nonlinSymbol {u : ℝ → X} {a b : ℝ} (hu : ContinuousOn u (Icc a b)) :
    ∃ N₀ : ℝ × Space → CSpace, StronglyMeasurable N₀ ∧
      ∀ s ∈ Icc a b, ∀ ξ, nonlinSymbol (velSymbol (u s)) ξ = N₀ (s, ξ) := by
  obtain ⟨V₀, hV₀m, hV₀⟩ := exists_joint_velSymbol hu
  exact ⟨fun p => nonlinSymbol (fun η => V₀ (p.1, η)) p.2,
    stronglyMeasurable_nonlinSymbol_param hV₀m,
    fun s hs ξ => congrFun (nonlinSymbol_congr (hV₀ s hs).symm) ξ⟩

private theorem aestronglyMeasurable_duhamel_integrand {u : ℝ → X} {a b t : ℝ}
    (hu : ContinuousOn u (Icc a b)) (htb : t ≤ b) :
    AEStronglyMeasurable (Function.uncurry fun s ξ =>
      ((2 * π * ‖ξ‖ * heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (velSymbol (u s)) ξ)
      ((volume.restrict (Ioc a t)).prod volume) := by
  obtain ⟨N₀, hN₀m, hN₀⟩ := exists_joint_nonlinSymbol hu
  have hmem : ∀ᵐ p ∂((volume.restrict (Ioc a t)).prod (volume : Measure Space)), p.1 ∈ Ioc a t := by
    rw [ae_iff]
    have hset : {p : ℝ × Space | ¬ p.1 ∈ Ioc a t} = (Ioc a t)ᶜ ×ˢ univ := by
      ext p
      simp
    rw [hset, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc.compl, compl_inter_self,
      measure_empty, zero_mul]
  have hcf : Continuous fun p : ℝ × Space =>
      ((2 * π * ‖p.2‖ * heatSymbol (t - p.1) p.2 : ℝ) : ℂ) := by
    unfold heatSymbol
    fun_prop
  refine ((hcf.stronglyMeasurable.smul hN₀m).aestronglyMeasurable).congr ?_
  filter_upwards [hmem] with p hp
  simp only [Function.uncurry, Pi.smul_apply']
  rw [hN₀ p.1 ⟨hp.1.le, hp.2.trans htb⟩ p.2]

private theorem coe_add_integral_ae {z x : X} {F : ℝ → X} {a t : ℝ} (hat : a ≤ t)
    (hF : IntervalIntegrable F volume a t) (h : z = x + ∫ s in a..t, F s) :
    ((z : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => ((x : L2C) : Space → CSpace) ξ +
      ((∫ s in Ioc a t, (F s : L2C) : L2C) : Space → CSpace) ξ := by
  have e1 : ((∫ s in a..t, F s : X) : L2C) = ∫ s in Ioc a t, (F s : L2C) := by
    rw [← intervalIntegral.integral_of_le hat]
    exact ((Sig.subtypeL).intervalIntegral_comp_comm hF).symm
  have e2 : (z : L2C) = (x : L2C) + ∫ s in Ioc a t, (F s : L2C) := by
    rw [h, ← e1]
    rfl
  rw [e2]
  exact Lp.coeFn_add _ _

private theorem symX_mild_ae (hB : BilinSymbol) {u : ℝ → X} {a b : ℝ} (hm : IsMildX u a b)
    (hsmooth : ∀ s ∈ Icc a b, IsSmoothX (u s)) {t : ℝ} (ht : t ∈ Icc a b) :
    symX (u t) =ᵐ[volume] fun ξ => ((heatFactor (t - a) ξ : ℝ) : ℂ) • symX (u a) ξ +
      ∫ s in Ioc a t, ((2 * π * ‖ξ‖ * heatSymbol (t - s) ξ : ℝ) : ℂ) •
        nonlinSymbol (velSymbol (u s)) ξ := by
  obtain ⟨hint, heq⟩ := hm.2 t ht
  have hcg : ∀ᵐ s ∂(volume.restrict (Ioc a t)),
      (((bilinX (t - s) (u s) (u s) : X) : L2C) : Space → CSpace) =ᵐ[volume]
        fun ξ => ((2 * π * ‖ξ‖ * heatSymbol (t - s) ξ : ℝ) : ℂ) •
          nonlinSymbol (velSymbol (u s)) ξ := by
    have hIoo : ∀ᵐ s ∂(volume.restrict (Ioc a t)), s ∈ Ioo a t := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hIoo] with s hs
    exact hB (t - s) (sub_pos.2 hs.2) (u s) (hsmooth s ⟨hs.1.le, hs.2.le.trans ht.2⟩)
  have hci : IntegrableOn (fun s => ((bilinX (t - s) (u s) (u s) : X) : L2C)) (Ioc a t) :=
    (Sig.subtypeL).integrable_comp hint.1
  have hI := coeFn_setIntegral_ae hci (aestronglyMeasurable_duhamel_integrand hm.1 ht.2) hcg
  have e0 := coe_add_integral_ae ht.1 hint heq
  filter_upwards [e0, coe_heatX_ae heat_holds fieldOpRealized_holds (t - a) (u a), hI]
    with ξ h0 h1 h2
  simp only [symX]
  rw [h0, h1, h2]

theorem duhamelSymbolOfBilinSymbol_holds : DuhamelSymbolOfBilinSymbol := by
  intro hB _ u a b _ hm hH t ht
  have hsmooth : ∀ s ∈ Icc a b, IsSmoothX (u s) := fun s hs k => (hH k).1 s hs
  have hat : a ≤ t := ht.1
  have hS := symX_mild_ae hB hm hsmooth ht
  have hSneg := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp hS
  have hne : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
    have h0 : (volume : Measure Space) {0} = 0 := measure_singleton 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ξ hξ
    simpa using hξ
  have hherm : ∀ s ξ, nonlinSymbol (velSymbol (u s)) (-ξ) =
      conjVec (nonlinSymbol (velSymbol (u s)) ξ) := fun s ξ =>
    nonlinSymbol_neg_of_herm (velSymbol_neg (u s)) ξ
  have hfix : ∀ s ξ, divFreeC ξ (nonlinSymbol (velSymbol (u s)) ξ) =
      nonlinSymbol (velSymbol (u s)) ξ := fun s ξ => lerayC_nonlinSymbol _ ξ
  have hh : ∀ s ξ, heatSymbol (t - s) (-ξ) = heatSymbol (t - s) ξ := fun s ξ => by
    simp [heatSymbol]
  have hfac : ∀ ξ, heatFactor (t - a) ξ = heatSymbol (t - a) ξ := fun ξ => by
    simp [heatFactor, heatSymbol, max_eq_left (sub_nonneg.2 hat)]
  filter_upwards [hS, hSneg, hne] with ξ h1 h2 h3
  simp only [Function.comp_apply] at h2
  rw [hfac] at h1
  rw [show heatFactor (t - a) (-ξ) = heatSymbol (t - a) ξ by rw [hfac, hh]] at h2
  rw [velSymbol_of_pointwise (μ := volume.restrict (Ioc a t))
    (Nf := fun s ξ => nonlinSymbol (velSymbol (u s)) ξ)
    (h := fun s ξ => heatSymbol (t - s) ξ) hherm hfix hh h3 h1 h2,
    intervalIntegral.integral_of_le hat]

end Breakdown.FarField
