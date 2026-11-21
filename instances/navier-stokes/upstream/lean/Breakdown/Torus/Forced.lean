import Breakdown.Torus.StatementsForce
import Breakdown.Torus.VarConst
import Breakdown.Torus.Basic
import Breakdown.Torus.TimeCoef
import Breakdown.Torus.ForceSmoothing
import Breakdown.Torus.CoefCalculus
import Breakdown.Torus.FreqTrSeries
import Breakdown.Torus.Advection

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Forced.Internal

open TimeCoef.Internal

abbrev slab (a b : ℝ) : Set (ℝ × Space) := Icc a b ×ˢ (univ : Set Space)

theorem sliceContDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    {g : ℝ × Space → E} (hg : ContDiffOn ℝ ∞ g (slab a b)) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    ContDiff ℝ ∞ (fun y => g (τ, y)) :=
  contDiffOn_univ.mp (hg.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun y _ => ⟨hτ, mem_univ y⟩))

theorem sliceContinuous {E : Type*} [TopologicalSpace E] {a b : ℝ} {g : ℝ × Space → E}
    (hc : ContinuousOn g (slab a b)) {τ : ℝ} (hτ : τ ∈ Icc a b) : Continuous fun x => g (τ, x) :=
  hc.comp_continuous (by fun_prop) fun x => ⟨hτ, mem_univ x⟩

theorem timeDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    {g : ℝ × Space → E} (hg : ContDiffOn ℝ ∞ g (slab a b)) {τ : ℝ} (hτ : τ ∈ Ioo a b) (x : Space) :
    HasDerivAt (fun σ => g (σ, x)) (fderivWithin ℝ g (slab a b) (τ, x) (1, 0)) τ := by
  have hd : DifferentiableWithinAt ℝ g (slab a b) (τ, x) :=
    (hg.differentiableOn (by simp)) _ ⟨Ioo_subset_Icc_self hτ, mem_univ _⟩
  have hp : HasDerivAt (fun σ : ℝ => (σ, x)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
  have h := hd.hasFDerivWithinAt.comp_hasDerivWithinAt τ hp.hasDerivWithinAt
    (show MapsTo (fun σ : ℝ => (σ, x)) (Icc a b) (slab a b) from fun σ hσ => ⟨hσ, mem_univ x⟩)
  exact h.hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)

theorem continuousOn_freqTrCoef_slab {a b : ℝ} {g : ℝ × Space → Space}
    (hg : ContinuousOn g (slab a b)) (k : Lattice) :
    ContinuousOn (fun τ => freqTrCoef (fun x => g (τ, x)) k) (Icc a b) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_cell).exists_bound_of_continuousOn
    (hg.mono (prod_mono subset_rfl (subset_univ _)))
  unfold freqTrCoef
  refine continuousOn_of_dominated (bound := fun _ => C) (fun τ hτ => ?_) (fun τ hτ => ?_)
    (integrable_const C) (Eventually.of_forall fun x => ?_)
  · exact (continuous_integrand k (sliceContinuous hg hτ)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_cell fun x hx => ?_
    rw [norm_smul, norm_character, one_mul, norm_complexify]
    exact hC _ ⟨hτ, hx⟩
  · exact (continuousOn_const (c := character k x)).smul (complexifyL.continuous.comp_continuousOn
      (hg.comp (Continuous.continuousOn (by fun_prop))
        (show MapsTo (fun τ : ℝ => (τ, x)) (Icc a b) (slab a b) from fun τ hτ => ⟨hτ, mem_univ x⟩)))

theorem hasDerivAt_freqTrCoef_slab {a b : ℝ} {g : ℝ × Space → Space}
    (hg : ContDiffOn ℝ ∞ g (slab a b)) (hab : a < b) (k : Lattice) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun τ => freqTrCoef (fun x => g (τ, x)) k)
      (freqTrCoef (fun x => deriv (fun τ => g (τ, x)) t) k) t := by
  have hU : UniqueDiffOn ℝ (slab a b) := (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
  set D : ℝ × Space → Space := fun z => fderivWithin ℝ g (slab a b) z (1, 0) with hDdef
  have hDc : ContinuousOn D (slab a b) :=
    ((hg.fderivWithin hU infty_add_one_le).clm_apply contDiffOn_const).continuousOn
  have e : (fun x => deriv (fun τ => g (τ, x)) t) = fun x => D (t, x) :=
    funext fun x => (timeDeriv hg ht x).deriv
  have h₁ : a < (a + t) / 2 := by linarith [ht.1]
  have h₂ : (t + b) / 2 < b := by linarith [ht.2]
  have h₃ : (a + t) / 2 < t := by linarith [ht.1]
  have h₄ : t < (t + b) / 2 := by linarith [ht.2]
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (a + t) / 2) (b := (t + b) / 2)).prod
    isCompact_cell).exists_bound_of_continuousOn
    (hDc.mono (prod_mono (Icc_subset_Icc h₁.le h₂.le) (subset_univ _)))
  have hgc := hg.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict cell)
    (F := fun τ x => character k x • complexify (g (τ, x)))
    (F' := fun τ x => character k x • complexify (D (τ, x)))
    (x₀ := t) (bound := fun _ => C) (Ioo_mem_nhds h₃ h₄) ?_ ?_ ?_ ?_ (integrable_const C) ?_
  · rw [e]
    exact key.2
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
    exact (continuous_integrand k (sliceContinuous hgc (Ioo_subset_Icc_self hτ))).aestronglyMeasurable
  · exact (continuous_integrand k (sliceContinuous hgc (Ioo_subset_Icc_self ht))).continuousOn.integrableOn_compact
      isCompact_cell
  · exact (continuous_integrand k (sliceContinuous hDc (Ioo_subset_Icc_self ht))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_cell fun x hx τ hτ => ?_
    rw [norm_smul, norm_character, one_mul, norm_complexify]
    exact hC (τ, x) ⟨Ioo_subset_Icc_self hτ, hx⟩
  · refine Eventually.of_forall fun x τ hτ => ?_
    exact (hasDerivAt_complexify
      (timeDeriv hg ⟨by linarith [hτ.1], by linarith [hτ.2]⟩ x)).const_smul (character k x)

def clampTime (a b τ : ℝ) : ℝ := a + (b - a) * ((1 - Real.cos τ) / 2)

def unclampTime (a b t : ℝ) : ℝ := Real.arccos (1 - 2 * ((t - a) / (b - a)))

theorem clampTime_mem {a b : ℝ} (hab : a < b) (τ : ℝ) : clampTime a b τ ∈ Icc a b := by
  have h1 := Real.neg_one_le_cos τ
  have h2 := Real.cos_le_one τ
  have h3 : 0 < b - a := sub_pos.2 hab
  unfold clampTime
  constructor <;> nlinarith

theorem clampTime_unclampTime {a b : ℝ} (hab : a < b) {t : ℝ} (ht : t ∈ Icc a b) :
    clampTime a b (unclampTime a b t) = t := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hq0 : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith [ht.1]) hba.le
  have hq1 : (t - a) / (b - a) ≤ 1 := (div_le_one hba).2 (by linarith [ht.2])
  unfold clampTime unclampTime
  rw [Real.cos_arccos (by linarith) (by linarith)]
  field_simp
  ring

theorem continuousOn_toV {u : ℝ → Space → Space} {a b : ℝ} (hab : a < b)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (slab a b))
    (hper : ∀ t ∈ Icc a b, IsPeriodic (u t)) (hdiv : ∀ t ∈ Icc a b, ∀ x, divergenceAt (u t) x = 0) :
    ContinuousOn (fun t => toV (u t)) (Icc a b) := by
  have hsm : ContDiff ℝ ∞ (clampTime a b) := by
    unfold clampTime
    exact contDiff_const.add (contDiff_const.mul ((contDiff_const.sub Real.contDiff_cos).div_const 2))
  have hm : ContDiff ℝ ∞ (fun z : ℝ × Space => (clampTime a b z.1, z.2)) :=
    (hsm.comp contDiff_fst).prodMk contDiff_snd
  have hw : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u (clampTime a b z.1) z.2) (Ici 0 ×ˢ univ) :=
    hu.comp hm.contDiffOn (fun z _ => ⟨clampTime_mem hab z.1, mem_univ _⟩)
  have hC := toVContinuous coefDeriv (freqTrSeriesSpec coefDeriv)
    (fun τ => u (clampTime a b τ)) hw
    (fun t _ => hper _ (clampTime_mem hab t)) (fun t _ => hdiv _ (clampTime_mem hab t))
  have hψ : Continuous (unclampTime a b) := by
    unfold unclampTime
    exact Real.continuous_arccos.comp (continuous_const.sub (continuous_const.mul
      ((continuous_id.sub continuous_const).div_const _)))
  have h2 : ContinuousOn (fun t => toV (u (clampTime a b (unclampTime a b t)))) (Icc a b) :=
    hC.comp hψ.continuousOn (fun t _ => Real.arccos_nonneg _)
  refine h2.congr fun t ht => ?_
  simp only [clampTime_unclampTime hab ht]

theorem freqTrCoef_add {f g : Space → Space} (hf : Continuous f) (hg : Continuous g) (k : Lattice) :
    freqTrCoef (fun x => f x + g x) k = freqTrCoef f k + freqTrCoef g k := by
  unfold freqTrCoef
  rw [← integral_add (Internal.Mild.integrableOn_cell hf k) (Internal.Mild.integrableOn_cell hg k)]
  congr 1
  funext x
  rw [show complexify (f x + g x) = complexify (f x) + complexify (g x) from complexifyL.map_add _ _,
    smul_add]

theorem mode_deriv {u : ℝ → Space → Space} {p : ℝ → Space → ℝ} {F : ℝ → Space → Space} {a b : ℝ}
    (hab : a < b) (h : IsForcedPeriodicSolution u p F a b) (k : Lattice) {τ : ℝ} (hτ : τ ∈ Ioo a b) :
    HasDerivAt (fun σ => freqTrCoef (u σ) k)
      ((-(4 * π ^ 2 * ‖freq k‖ ^ 2)) • freqTrCoef (u τ) k
        - (divFree k (advCoef (toV (u τ)) (toV (u τ)) k) - divFree k (freqTrCoef (F τ) k))) τ := by
  obtain ⟨hu, hp, hFc, hper, hdiv, hmom⟩ := h
  have hτ' : τ ∈ Icc a b := Ioo_subset_Icc_self hτ
  have hφ : ContDiff ℝ ∞ (u τ) := sliceContDiff (g := fun z : ℝ × Space => u z.1 z.2) hu hτ'
  have hq : ContDiff ℝ ∞ (p τ) := sliceContDiff (g := fun z : ℝ × Space => p z.1 z.2) hp hτ'
  have hFτ : Continuous (F τ) := sliceContinuous (g := fun z : ℝ × Space => F z.1 z.2) hFc hτ'
  have hd : HasDerivAt (fun σ => freqTrCoef (u σ) k)
      (freqTrCoef (fun x => deriv (fun σ => u σ x) τ) k) τ :=
    hasDerivAt_freqTrCoef_slab (g := fun z : ℝ × Space => u z.1 z.2) hu hab k hτ
  have hm : (fun x => deriv (fun σ => u σ x) τ) =
      fun x => ((sumSecondPartialsAt (u τ) x - gradientAt (p τ) x) - advectionAt (u τ) x) + F τ x := by
    funext x
    rw [← hmom τ hτ x]
    abel
  have hlg : Continuous (fun x => sumSecondPartialsAt (u τ) x - gradientAt (p τ) x) :=
    (Internal.Mild.continuous_sumSecondPartialsAt hφ).sub (Internal.Mild.continuous_gradientAt hq)
  have hX : Continuous (fun x => (sumSecondPartialsAt (u τ) x - gradientAt (p τ) x) - advectionAt (u τ) x) :=
    hlg.sub (Internal.Mild.continuous_advectionAt hφ)
  rw [hm, freqTrCoef_add hX hFτ, Internal.Mild.freqTrCoef_sub hlg (Internal.Mild.continuous_advectionAt hφ),
    Internal.Mild.freqTrCoef_sub (Internal.Mild.continuous_sumSecondPartialsAt hφ)
      (Internal.Mild.continuous_gradientAt hq),
    coefSumSecondPartials _ (hφ.of_le ENat.LEInfty.out) (hper τ hτ').1,
    coefGradient _ (hq.of_le ENat.LEInfty.out) (hper τ hτ').2.1,
    coefAdvection coefDeriv (freqTrSeriesSpec coefDeriv) _ hφ (hper τ hτ').1 (hdiv τ hτ')] at hd
  have hfix : ∀ σ ∈ Icc a b, divFree k (freqTrCoef (u σ) k) = freqTrCoef (u σ) k := by
    intro σ hσ
    rw [← (freqTrSeriesSpec coefDeriv _ (sliceContDiff (g := fun z : ℝ × Space => u z.1 z.2) hu hσ)
      (hper σ hσ).1 (hdiv σ hσ)).1 k, Internal.Mild.divFree_coeff]
  set LR : Coef →L[ℝ] Coef := (Internal.Mild.divFreeL k).restrictScalars ℝ with hLR
  have hL' := LR.hasFDerivAt.comp_hasDerivAt τ hd
  have hev : (fun σ => freqTrCoef (u σ) k) =ᶠ[𝓝 τ] (LR ∘ fun σ => freqTrCoef (u σ) k) := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with σ hσ
    exact (hfix σ (Ioo_subset_Icc_self hσ)).symm
  refine (hL'.congr_of_eventuallyEq hev).congr_deriv ?_
  have e2 : LR ((2 * π * Complex.I * scalarCoef (p τ) k) • latVec k) = 0 := by
    show Internal.Mild.divFreeL k ((2 * π * Complex.I * scalarCoef (p τ) k) • latVec k) = 0
    rw [map_smul, Internal.Mild.divFreeL_apply, Internal.Mild.divFree_latVec, smul_zero]
  rw [map_add, map_sub, map_sub, map_smul, e2, sub_zero]
  show _ • divFree k _ - divFree k _ + divFree k _ = _
  rw [hfix τ hτ']
  abel

theorem variation_of_constants {c B : ℝ → Coef} {l a t : ℝ} (ht : a ≤ t)
    (hc : ContinuousOn c (Icc a t)) (hB : ContinuousOn B (Icc a t))
    (hd : ∀ s ∈ Ioo a t, HasDerivAt c ((-l) • c s - B s) s) :
    c t = Real.exp (-(l * (t - a))) • c a + ∫ s in a..t, (-Real.exp (-(l * (t - s)))) • B s := by
  have hg : ∀ s ∈ Ioo a t, HasDerivAt (fun s => Real.exp (l * s) • c s)
      (-(Real.exp (l * s) • B s)) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (l * s)) (Real.exp (l * s) * l) s := by
      simpa using ((hasDerivAt_id s).const_mul l).exp
    refine (he.smul (hd s hs)).congr_deriv ?_
    rw [smul_sub, smul_smul, mul_neg, neg_smul]
    abel
  have hexp : Continuous (fun s : ℝ => Real.exp (l * s)) := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s => Real.exp (l * s) • c s) (f' := fun s => -(Real.exp (l * s) • B s)) ht
    (hexp.continuousOn.smul hc) hg
    ((hexp.continuousOn.smul hB).neg.intervalIntegrable_of_Icc ht)
  have e1 : (fun s => (-Real.exp (-(l * (t - s)))) • B s) =
      fun s => Real.exp (-(l * t)) • (-(Real.exp (l * s) • B s)) := by
    funext s
    rw [show -(l * (t - s)) = -(l * t) + l * s by ring, smul_neg, smul_smul, ← Real.exp_add,
      neg_smul]
  rw [e1, intervalIntegral.integral_smul, hint, smul_sub, smul_smul, smul_smul, ← Real.exp_add,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul,
    show -(l * t) + l * a = -(l * (t - a)) by ring]
  abel

theorem coeff_forceV {τ : ℝ} (hτ : 0 < τ) (G : Space → Space) (k : Lattice) :
    coeff (forceV τ G) k = heatFactor τ k • divFree k (freqTrCoef G k) := by
  show (Real.sqrt (weight k))⁻¹ • forceSeq τ G k = _
  unfold forceSeq
  rw [if_pos hτ, smul_smul, ← mul_assoc, inv_mul_cancel₀ (Internal.sqrt_weight_pos k).ne', one_mul]

theorem forceV_eq_heat {σ τ : ℝ} (hσ : 0 < σ) (h : σ ≤ τ) (G : Space → Space) :
    forceV τ G = heat (τ - σ) (forceV σ G) := by
  apply Subtype.ext
  apply lp.ext
  funext k
  rw [Internal.heat_apply]
  show forceSeq τ G k = heatFactor (τ - σ) k • forceSeq σ G k
  unfold forceSeq
  rw [if_pos (hσ.trans_le h), if_pos hσ, smul_smul]
  congr 1
  have e := Internal.heatFactor_add (sub_nonneg.2 h) hσ.le k
  rw [sub_add_cancel] at e
  rw [e]
  ring

theorem norm_forceV_le {τ : ℝ} (hτ : 0 < τ) {G : Space → Space} (hG : Continuous G) (hp : IsPeriodic G) :
    ‖forceV τ G‖ ≤ (forceSmoothing.choose * τ ^ (-(1 / 2 : ℝ)) + forceSmoothing.choose) *
      Real.sqrt (∫ x in cell, ‖G x‖ ^ 2) := by
  obtain ⟨hC0, hC⟩ := forceSmoothing.choose_spec
  set C := forceSmoothing.choose
  have hS := Real.sqrt_nonneg (∫ x in cell, ‖G x‖ ^ 2)
  have hT : 0 ≤ C * τ ^ (-(1 / 2 : ℝ)) := mul_nonneg hC0.le (rpow_nonneg hτ.le _)
  rcases le_or_gt τ 1 with h1 | h1
  · have := hC τ hτ h1 G hG hp
    nlinarith
  · rw [forceV_eq_heat one_pos h1.le]
    have h2 := hC 1 one_pos le_rfl G hG hp
    rw [one_rpow, mul_one] at h2
    have h3 : ‖heat (τ - 1) (forceV 1 G)‖ ≤ ‖forceV 1 G‖ := by
      calc ‖heat (τ - 1) (forceV 1 G)‖ ≤ ‖heat (τ - 1)‖ * ‖forceV 1 G‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖forceV 1 G‖ := by gcongr; exact norm_heat_le _
        _ = ‖forceV 1 G‖ := one_mul _
    nlinarith

theorem continuousOn_force {F : ℝ → Space → Space} {a b t : ℝ} (htb : t ≤ b)
    (hFc : ContinuousOn (fun z : ℝ × Space => F z.1 z.2) (slab a b)) :
    ContinuousOn (fun s => forceV (t - s) (F s)) (Ioo a t) := by
  intro s₀ hs₀
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_cell).exists_bound_of_continuousOn
    (hFc.mono (prod_mono (subset_refl (Icc a b)) (subset_univ _)))
  have hsub : Ioo a t ⊆ Icc a b := fun s hs => ⟨hs.1.le, hs.2.le.trans htb⟩
  have hA : ∀ s ∈ Icc a b, ∀ k, ‖freqTrCoef (F s) k‖ ≤ M * volume.real cell := fun s hs k =>
    norm_freqTrCoef_le (fun x hx => hM (s, x) ⟨hs, hx⟩) k
  have hσ : 0 < (t - s₀) / 2 := half_pos (sub_pos.2 hs₀.2)
  rw [ContinuousWithinAt, tendsto_subtype_rng]
  apply Internal.tendsto_seq
    (b := fun k => 2 * (M * volume.real cell) * (Real.sqrt (weight k) * heatFactor ((t - s₀) / 2) k))
  · refine ((Internal.summable_weight_heat hσ).mul_left ((2 * (M * volume.real cell)) ^ 2)).congr
      fun k => ?_
    simp only [mul_pow, Real.sq_sqrt (Internal.weight_pos k).le]
  · intro k
    have h1 : Continuous fun s => Real.sqrt (weight k) * heatFactor (t - s) k :=
      continuous_const.mul ((Internal.continuous_heatFactor k).comp (continuous_const.sub continuous_id))
    have h2 : ContinuousWithinAt (fun s => freqTrCoef (F s) k) (Ioo a t) s₀ :=
      ((continuousOn_freqTrCoef_slab (g := fun z : ℝ × Space => F z.1 z.2) hFc k) s₀
        (hsub hs₀)).mono hsub
    have h3 : ContinuousWithinAt (fun s => divFree k (freqTrCoef (F s) k)) (Ioo a t) s₀ :=
      (Internal.Mild.divFreeL k).continuous.continuousAt.comp_continuousWithinAt h2
    have hc : ContinuousWithinAt (fun s => (Real.sqrt (weight k) * heatFactor (t - s) k) •
        divFree k (freqTrCoef (F s) k)) (Ioo a t) s₀ :=
      h1.continuousWithinAt.smul h3
    have e : ∀ s ∈ Ioo a t, forceSeq (t - s) (F s) k =
        (Real.sqrt (weight k) * heatFactor (t - s) k) • divFree k (freqTrCoef (F s) k) :=
      fun s hs => if_pos (sub_pos.2 hs.2)
    exact hc.congr (fun s hs => e s hs) (e s₀ hs₀)
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iic_mem_nhds (show s₀ < (s₀ + t) / 2 by linarith [hs₀.2]))] with s hs hs' k
    show ‖forceSeq (t - s) (F s) k‖ ≤ _
    have hpos : 0 < t - s := sub_pos.2 hs.2
    have hle : (t - s₀) / 2 ≤ t - s := by linarith [mem_Iic.1 hs']
    refine (Force.Internal.norm_forceSeq_le hpos (F s) k).trans ?_
    have h1 := Internal.heatFactor_anti hle k
    have h2 := hA s (hsub hs) k
    have h3 := Internal.heatFactor_nonneg (t - s) k
    have h4 := Real.sqrt_nonneg (weight k)
    have h5 := Internal.heatFactor_nonneg ((t - s₀) / 2) k
    calc Real.sqrt (weight k) * heatFactor (t - s) k * (2 * ‖freqTrCoef (F s) k‖)
        ≤ Real.sqrt (weight k) * heatFactor ((t - s₀) / 2) k * (2 * (M * volume.real cell)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 h4) (by linarith) (by positivity)
            (mul_nonneg h4 h5)
      _ = 2 * (M * volume.real cell) * (Real.sqrt (weight k) * heatFactor ((t - s₀) / 2) k) := by ring

theorem integrable_force {F : ℝ → Space → Space} {a b t : ℝ} (ht : t ∈ Icc a b)
    (hFc : ContinuousOn (fun z : ℝ × Space => F z.1 z.2) (slab a b))
    (hFp : ∀ s ∈ Icc a b, IsPeriodic (F s)) :
    IntervalIntegrable (fun s => forceV (t - s) (F s)) volume a t := by
  obtain ⟨hC0, -⟩ := forceSmoothing.choose_spec
  set C := forceSmoothing.choose
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_cell).exists_bound_of_continuousOn
    (hFc.mono (prod_mono (subset_refl (Icc a b)) (subset_univ _)))
  set R := Real.sqrt (M ^ 2 * volume.real cell)
  have hsub : Ioo a t ⊆ Icc a b := fun s hs => ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hR : ∀ s ∈ Icc a b, Real.sqrt (∫ x in cell, ‖F s x‖ ^ 2) ≤ R := by
    intro s hs
    refine Real.sqrt_le_sqrt ?_
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cell)
      (f := fun x => ‖F s x‖ ^ 2) (C := M ^ 2) isCompact_cell.measure_lt_top (fun x hx => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hM (s, x) ⟨hs, hx⟩) 2)
    exact (Real.le_norm_self _).trans h
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  have hg : IntegrableOn (fun s => (C * (t - s) ^ (-(1 / 2 : ℝ)) + C) * R) (Ioo a t) := by
    have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) volume a t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := t - a) (b := 0)
        (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left t
      simpa using this
    have h0 : IntervalIntegrable (fun _ : ℝ => C) volume a t := intervalIntegrable_const
    have h2 := ((h1.const_mul C).add h0).mul_const R
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).1 h2
  refine Integrable.mono' hg ?_ ?_
  · exact (continuousOn_force ht.2 hFc).aestronglyMeasurable_of_isSeparable measurableSet_Ioo
      (TopologicalSpace.IsSeparable.of_separableSpace _)
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
    have hst : 0 < t - s := sub_pos.2 hs.2
    have hA : 0 ≤ C * (t - s) ^ (-(1 / 2 : ℝ)) + C :=
      add_nonneg (mul_nonneg hC0.le (rpow_nonneg hst.le _)) hC0.le
    calc ‖forceV (t - s) (F s)‖
        ≤ (C * (t - s) ^ (-(1 / 2 : ℝ)) + C) * Real.sqrt (∫ x in cell, ‖F s x‖ ^ 2) :=
          norm_forceV_le hst (sliceContinuous (g := fun z : ℝ × Space => F z.1 z.2) hFc (hsub hs))
            (hFp s (hsub hs))
      _ ≤ (C * (t - s) ^ (-(1 / 2 : ℝ)) + C) * R := mul_le_mul_of_nonneg_left (hR s (hsub hs)) hA

theorem integrable_kernel (hK : KernelSharpBound) {U : ℝ → V} {a t : ℝ} (ht : a ≤ t)
    (hU : ContinuousOn U (Icc a t)) :
    IntervalIntegrable (fun s => kernel (t - s) (U s) (U s)) volume a t := by
  obtain ⟨C, hC, hb⟩ := Internal.Mild.kernel_norm_le hK
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hU
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht]
  have hg : IntegrableOn (fun s => (C * (t - s) ^ (-(3 / 4 : ℝ)) + C) * M * M) (Ioo a t) := by
    have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) volume a t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := t - a) (b := 0)
        (r := -(3 / 4 : ℝ)) (by norm_num)).comp_sub_left t
      simpa using this
    have h0 : IntervalIntegrable (fun _ : ℝ => C) volume a t := intervalIntegrable_const
    have h2 := (((h1.const_mul C).add h0).mul_const M).mul_const M
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).1 h2
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable_of_isSeparable (fun s hs => ?_) measurableSet_Ioo
      (TopologicalSpace.IsSeparable.of_separableSpace _)
    have hUs : ContinuousWithinAt U (Ioo a t) s :=
      (hU s (Ioo_subset_Icc_self hs)).mono Ioo_subset_Icc_self
    exact Internal.Mild.kernel_tendsto (sub_pos.2 hs.2)
      (((continuous_const.sub continuous_id).tendsto s).mono_left nhdsWithin_le_nhds) hUs hUs
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
    have hu := hM s (Ioo_subset_Icc_self hs)
    have hA : 0 ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) + C :=
      add_nonneg (mul_nonneg hC.le (rpow_nonneg (sub_pos.2 hs.2).le _)) hC.le
    calc ‖kernel (t - s) (U s) (U s)‖
        ≤ (C * (t - s) ^ (-(3 / 4 : ℝ)) + C) * ‖U s‖ * ‖U s‖ := hb _ (sub_pos.2 hs.2) _ _
      _ ≤ (C * (t - s) ^ (-(3 / 4 : ℝ)) + C) * M * M :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu hA) hu (norm_nonneg _)
            (mul_nonneg hA ((norm_nonneg _).trans hu))

theorem intervalIntegrable_coeff {f : ℝ → V} {a t : ℝ} (hf : IntervalIntegrable f volume a t)
    (k : Lattice) : IntervalIntegrable (fun s => coeff (f s) k) volume a t :=
  ⟨(Internal.Mild.coeffL k).integrable_comp hf.1, (Internal.Mild.coeffL k).integrable_comp hf.2⟩

theorem mode_identity {u : ℝ → Space → Space} {p : ℝ → Space → ℝ} {F : ℝ → Space → Space} {a b : ℝ}
    (hab : a < b) (h : IsForcedPeriodicSolution u p F a b)
    (hUc : ContinuousOn (fun t => toV (u t)) (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b)
    (hI : IntervalIntegrable (fun s => kernel (t - s) (toV (u s)) (toV (u s))) volume a t)
    (hJ : IntervalIntegrable (fun s => forceV (t - s) (F s)) volume a t) (k : Lattice) :
    coeff (toV (u t)) k = heatFactor (t - a) k • coeff (toV (u a)) k +
      (∫ s in a..t, coeff (kernel (t - s) (toV (u s)) (toV (u s))) k) +
      ∫ s in a..t, coeff (forceV (t - s) (F s)) k := by
  have hu := h.1
  have hFc := h.2.2.1
  have hper := h.2.2.2.1
  have hdiv := h.2.2.2.2.1
  have hcU : ∀ s ∈ Icc a b, coeff (toV (u s)) k = freqTrCoef (u s) k := fun s hs =>
    (freqTrSeriesSpec coefDeriv _ (sliceContDiff (g := fun z : ℝ × Space => u z.1 z.2) hu hs)
      (hper s hs).1 (hdiv s hs)).1 k
  have hpos : 0 < heatFactor 1 k := Real.exp_pos _
  have hB : ∀ s, divFree k (advCoef (toV (u s)) (toV (u s)) k) =
      (-(heatFactor 1 k)⁻¹) • coeff (kernel 1 (toV (u s)) (toV (u s))) k := by
    intro s
    rw [coeff_kernel 1 one_pos, Internal.Mild.divFree_add, ← two_smul ℝ (divFree k _), smul_smul, smul_smul,
      show -(heatFactor 1 k)⁻¹ * (-(1 / 2) * heatFactor 1 k) * 2 = 1 by field_simp, one_smul]
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hUt : ContinuousOn (fun s => toV (u s)) (Icc a t) := hUc.mono hsub
  have hAc : ContinuousOn (fun s => divFree k (advCoef (toV (u s)) (toV (u s)) k)) (Icc a t) := by
    simp only [hB]
    exact ((Internal.Mild.coeffL k).continuous.comp_continuousOn
      (((kernel 1).continuous.comp_continuousOn hUt).clm_apply hUt)).const_smul (-(heatFactor 1 k)⁻¹)
  have hFk : ContinuousOn (fun s => freqTrCoef (F s) k) (Icc a b) :=
    continuousOn_freqTrCoef_slab (g := fun z : ℝ × Space => F z.1 z.2) hFc k
  have hFl : ContinuousOn (fun s => divFree k (freqTrCoef (F s) k)) (Icc a t) :=
    (Internal.Mild.divFreeL k).continuous.comp_continuousOn (hFk.mono hsub)
  have hcc : ContinuousOn (fun s => freqTrCoef (u s) k) (Icc a t) :=
    ((Internal.Mild.coeffL k).continuous.comp_continuousOn hUt).congr
      (fun s hs => (hcU s (hsub hs)).symm)
  have hv := variation_of_constants ht.1 hcc (hAc.sub hFl)
    (fun s hs => mode_deriv hab h k ⟨hs.1, hs.2.trans_le ht.2⟩)
  beta_reduce at hv
  have hh : heatFactor (t - a) k = Real.exp (-(4 * π ^ 2 * ‖freq k‖ ^ 2 * (t - a))) := by
    simp only [heatFactor, max_eq_left (sub_nonneg.2 ht.1)]
  rw [hcU t ht, hcU a ⟨le_rfl, hab.le⟩, hv, hh, add_assoc]
  congr 1
  rw [← intervalIntegral.integral_add (intervalIntegrable_coeff hI k) (intervalIntegrable_coeff hJ k)]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with s hs hmem
  rw [uIoc_of_le ht.1] at hmem
  have hst : 0 < t - s := sub_pos.2 (lt_of_le_of_ne hmem.2 hs)
  rw [coeff_kernel _ hst, coeff_forceV hst, Internal.Mild.divFree_add, ← two_smul ℝ (divFree k _), smul_smul,
    heatFactor, max_eq_left hst.le, Pi.sub_apply, smul_sub, show ∀ z : ℝ, -(1 / 2) * z * 2 = -z from fun z => by ring,
    neg_smul, neg_smul, sub_neg_eq_add]

end Forced.Internal

open Forced.Internal in
theorem forcedPeriodicIsMild (hK : KernelSharpBound) : ForcedPeriodicIsMild := by
  intro u p F a b hab h
  have hUc : ContinuousOn (fun t => toV (u t)) (Icc a b) :=
    continuousOn_toV hab h.1 (fun t ht => (h.2.2.2.1 t ht).1) h.2.2.2.2.1
  refine ⟨hUc, fun t ht => ?_⟩
  have hI : IntervalIntegrable (fun s => kernel (t - s) (toV (u s)) (toV (u s))) volume a t :=
    integrable_kernel (U := fun s => toV (u s)) hK ht.1 (hUc.mono (Icc_subset_Icc_right ht.2))
  have hJ : IntervalIntegrable (fun s => forceV (t - s) (F s)) volume a t :=
    integrable_force ht h.2.2.1 (fun s hs => (h.2.2.2.1 s hs).2.2)
  refine ⟨hI, hJ, ?_⟩
  apply coeff_injective
  intro k
  have e : coeff (heat (t - a) (toV (u a)) + (∫ s in a..t, kernel (t - s) (toV (u s)) (toV (u s))) +
      ∫ s in a..t, forceV (t - s) (F s)) k =
      coeff (heat (t - a) (toV (u a))) k +
        (∫ s in a..t, coeff (kernel (t - s) (toV (u s)) (toV (u s))) k) +
        ∫ s in a..t, coeff (forceV (t - s) (F s)) k := by
    rw [← Internal.Mild.coeffL_apply, map_add, map_add,
      ← (Internal.Mild.coeffL k).intervalIntegral_comp_comm hI,
      ← (Internal.Mild.coeffL k).intervalIntegral_comp_comm hJ]
    rfl
  rw [e, coeff_heat]
  exact mode_identity hab h hUc ht hI hJ k

end Breakdown.Periodic
