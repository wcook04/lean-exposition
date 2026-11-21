import Breakdown.CertCell.ScalarHeightRadialTest

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

open Internal.ScalarHeight

private def sliceGood (q : ℝ → Space → ℝ) (dq : ℝ → Space → Space) (r : ℝ) : Prop :=
  ∀ N : ℕ,
    IntegrableOn (fun u : (ℝ × ℝ) × ℝ => (q u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ))
      {u | |u.2| ≤ N} boxMeasure ∧
    IntegrableOn (fun u : (ℝ × ℝ) × ℝ => (dq u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) 2 : ℂ))
      {u | |u.2| ≤ N} boxMeasure

private lemma ae_sliceGood {q : ℝ → Space → ℝ} {dq : ℝ → Space → Space}
    (hq : AEStronglyMeasurable (fun z : ℝ × Space => q z.1 z.2) volume)
    (hdq : AEStronglyMeasurable (fun z : ℝ × Space => dq z.1 z.2) volume)
    (hL : ∀ R : ℝ, periodLIntegral (fun σ y => if ‖y‖ ≤ R then q σ y ^ 2 + ‖dq σ y‖ ^ 2 else 0) < ⊤) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), sliceGood q dq r := by
  have hc2 : Continuous (fun p : ℝ × Space => p.2 2) := (contDiff_coord 2).continuous.comp continuous_snd
  have hS : ∀ M : ℝ, MeasurableSet {p : ℝ × Space | planeRadius p.2 ≤ M ∧ |p.2 2| ≤ M} := fun M =>
    (measurableSet_le (continuous_planeRadius.measurable.comp measurable_snd) measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp hc2.measurable) measurable_const)
  set c : ℝ → ℝ × Space → ℂ := fun M => {p : ℝ × Space | planeRadius p.2 ≤ M ∧ |p.2 2| ≤ M}.indicator 1
    with hcdef
  have hcm : ∀ M, AEStronglyMeasurable (c M) slabMeasure := fun M =>
    (measurable_one.indicator (hS M)).aestronglyMeasurable
  have hcC : ∀ M p, ‖c M p‖ ≤ 1 := fun M p => by
    rw [hcdef]
    by_cases h : p ∈ {p : ℝ × Space | planeRadius p.2 ≤ M ∧ |p.2 2| ≤ M} <;> simp [h]
  have hcR : ∀ (M : ℝ) (p : ℝ × Space), M + M < ‖p.2‖ → c M p = 0 := fun M p hp => by
    rw [hcdef]
    refine indicator_of_notMem (fun h => ?_) _
    linarith [norm_le_planeRadius_add p.2, h.1, h.2]
  have hslice : ∀ M : ℕ, ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      Integrable (fun u => c M (cellMap (r, u)) * (q (cellMap (r, u)).1 (cellMap (r, u)).2 : ℂ) +
        0 * (dq (cellMap (r, u)).1 (cellMap (r, u)).2 2 : ℂ)) boxMeasure ∧
      Integrable (fun u => 0 * (q (cellMap (r, u)).1 (cellMap (r, u)).2 : ℂ) +
        c M (cellMap (r, u)) * (dq (cellMap (r, u)).1 (cellMap (r, u)).2 2 : ℂ)) boxMeasure := by
    intro M
    have h1 := integrable_slab_mul hq hdq hL (hcm M) aestronglyMeasurable_const (hcC M)
      (fun _ => by simp) (hcR M) (fun _ _ => rfl)
    have h2 := integrable_slab_mul hq hdq hL aestronglyMeasurable_const (hcm M)
      (fun _ => by simp) (hcC M) (fun _ _ => rfl) (hcR M)
    filter_upwards [ae_integrable_slice h1, ae_integrable_slice h2] with r hr1 hr2
    exact ⟨hr1, hr2⟩
  filter_upwards [ae_all_iff.2 hslice, ae_restrict_mem measurableSet_Ioi] with r hr hr0
  intro N
  have hr0' : (0 : ℝ) ≤ r := le_of_lt hr0
  set M : ℕ := max N ⌈r⌉₊
  have hrM : r ≤ (M : ℝ) := (Nat.le_ceil r).trans (by exact_mod_cast le_max_right N ⌈r⌉₊)
  have hNM : (N : ℝ) ≤ M := by exact_mod_cast le_max_left N ⌈r⌉₊
  have hT : MeasurableSet {u : (ℝ × ℝ) × ℝ | |u.2| ≤ (M : ℝ)} :=
    measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const
  have hsub : {u : (ℝ × ℝ) × ℝ | |u.2| ≤ (N : ℝ)} ⊆ {u | |u.2| ≤ (M : ℝ)} := fun u hu =>
    le_trans (show |u.2| ≤ (N : ℝ) from hu) hNM
  have hcell : ∀ u : (ℝ × ℝ) × ℝ, c M (cellMap (r, u)) =
      {u : (ℝ × ℝ) × ℝ | |u.2| ≤ (M : ℝ)}.indicator 1 u := by
    intro u
    rw [hcdef]
    simp [indicator, cellMap, planeRadius_cylPoint hr0', cylPoint_apply_two, hrM]
  constructor
  · have h := (hr M).1
    simp only [hcell, zero_mul, add_zero] at h
    have h' : Integrable ({u : (ℝ × ℝ) × ℝ | |u.2| ≤ (M : ℝ)}.indicator
        (fun u => (q u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ))) boxMeasure := by
      refine h.congr (Eventually.of_forall fun u => ?_)
      by_cases hu : u ∈ {u : (ℝ × ℝ) × ℝ | |u.2| ≤ (M : ℝ)} <;> simp [hu, cellMap]
    exact ((integrable_indicator_iff hT).1 h').mono_set hsub
  · have h := (hr M).2
    simp only [hcell, zero_mul, zero_add] at h
    have h' : Integrable ({u : (ℝ × ℝ) × ℝ | |u.2| ≤ (M : ℝ)}.indicator
        (fun u => (dq u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) 2 : ℂ))) boxMeasure := by
      refine h.congr (Eventually.of_forall fun u => ?_)
      by_cases hu : u ∈ {u : (ℝ × ℝ) × ℝ | |u.2| ≤ (M : ℝ)} <;> simp [hu, cellMap]
    exact ((integrable_indicator_iff hT).1 h').mono_set hsub

private lemma modeFactor_periodic (ξ : ℤ × ℤ) (τ : ℝ) : Function.Periodic (modeFactor ξ τ) (2 * Real.pi) := by
  intro θ
  rw [modeFactor, modeFactor]
  have e : -(((2 * Real.pi * ξ.1 * τ + ξ.2 * (θ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      -(((2 * Real.pi * ξ.1 * τ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) +
        ((-ξ.2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma cylPoint_add_two_pi (r θ z : ℝ) :
    CellCert.CellAnalysis.cylPoint r (θ + 2 * Real.pi) z = CellCert.CellAnalysis.cylPoint r θ z := by
  simp only [CellCert.CellAnalysis.cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

private lemma modeAverage_plane (ξ : ℤ × ℤ) (f : ℝ → Space → ℝ) (r z : ℝ) :
    modeAverage ξ (fun τ φ (_ : Unit) => f τ (axialRot φ (planePoint (r, z)))) () =
      (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi,
        modeFactor ξ τ θ * (f τ (CellCert.CellAnalysis.cylPoint r θ z) : ℂ) := by
  rw [modeAverage]
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  have hp : Function.Periodic (fun θ => modeFactor ξ τ θ *
      (f τ (CellCert.CellAnalysis.cylPoint r θ z) : ℂ)) (2 * Real.pi) := by
    intro θ
    simp only [modeFactor_periodic ξ τ θ, cylPoint_add_two_pi]
  have h := hp.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
  simp only [axialRot_planePoint]
  exact h

private lemma box_slice_integral {G : (ℝ × ℝ) × ℝ → ℂ} {z : ℝ}
    (hG : Integrable (fun v : ℝ × ℝ => G (v, z))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Ioo (-Real.pi) Real.pi)))) :
    ∫ v, G (v, z) ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) =
      ∫ τ in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi, G ((τ, θ), z) := by
  rw [integral_prod _ hG, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

private lemma slice_mode (ξ : ℤ × ℤ) (f : ℝ → Space → ℝ) {r N : ℝ}
    (hf : IntegrableOn (fun u : (ℝ × ℝ) × ℝ => (f u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ))
      {u | |u.2| ≤ N} boxMeasure) :
    IntegrableOn (fun z => modeAverage ξ (fun τ φ (_ : Unit) => f τ (axialRot φ (planePoint (r, z)))) ())
      (Icc (-N) N) ∧
    ∀ a : ℝ → ℝ, Continuous a → (∀ z, N < |z| → a z = 0) →
      Integrable (fun u : (ℝ × ℝ) × ℝ => modeFactor ξ u.1.1 u.1.2 *
        (f u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ) * (a u.2 : ℂ)) boxMeasure ∧
      ∫ u, modeFactor ξ u.1.1 u.1.2 * (f u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ) *
          (a u.2 : ℂ) ∂boxMeasure =
        (2 * Real.pi : ℂ) * ∫ z, modeAverage ξ (fun τ φ (_ : Unit) => f τ (axialRot φ (planePoint (r, z)))) () *
          (a z : ℂ) := by
  set S : Set ((ℝ × ℝ) × ℝ) := {u | |u.2| ≤ N} with hSdef
  have hS : MeasurableSet S := measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const
  set G : (ℝ × ℝ) × ℝ → ℂ := fun u => modeFactor ξ u.1.1 u.1.2 *
    (f u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ) with hGdef
  set Pm : ℝ → ℂ := fun z => modeAverage ξ (fun τ φ (_ : Unit) => f τ (axialRot φ (planePoint (r, z)))) ()
    with hPm
  have hmF : Continuous (fun u : (ℝ × ℝ) × ℝ => modeFactor ξ u.1.1 u.1.2) :=
    (continuous_modeFactor ξ).comp continuous_fst
  have hGS : IntegrableOn G S boxMeasure :=
    hf.bdd_mul (c := 1) hmF.aestronglyMeasurable (Eventually.of_forall fun u => by rw [norm_modeFactor])
  have hGi : Integrable (S.indicator G) boxMeasure := (integrable_indicator_iff hS).2 hGS
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'
  have hsl : ∀ᵐ z, ∫ v, S.indicator G (v, z) ∂((volume.restrict (Icc (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi))) = (Icc (-N) N).indicator (fun z => (2 * Real.pi : ℂ) * Pm z) z := by
    filter_upwards [hGi.prod_left_ae] with z hz
    by_cases hzN : |z| ≤ N
    · rw [indicator_of_mem (show z ∈ Icc (-N) N from abs_le.1 hzN)]
      have e : (fun v : ℝ × ℝ => S.indicator G (v, z)) = fun v => G (v, z) :=
        funext fun v => indicator_of_mem (show (v, z) ∈ S from hzN) _
      rw [e] at hz ⊢
      rw [box_slice_integral hz, hPm]
      beta_reduce
      rw [modeAverage_plane]
      field_simp
      rfl
    · rw [indicator_of_notMem (show z ∉ Icc (-N) N from fun h => hzN (abs_le.2 h))]
      have e : ∀ v : ℝ × ℝ, S.indicator G (v, z) = 0 := fun v =>
        indicator_of_notMem (show (v, z) ∉ S from hzN) _
      simp only [e, integral_zero]
  refine ⟨?_, fun a ha haN => ?_⟩
  · have h1 : Integrable ((Icc (-N) N).indicator (fun z => (2 * Real.pi : ℂ) * Pm z)) :=
      hGi.integral_prod_right.congr hsl
    have h2 := ((integrable_indicator_iff measurableSet_Icc).1 h1).const_mul ((2 * Real.pi : ℂ)⁻¹)
    exact (show IntegrableOn (fun z => (2 * Real.pi : ℂ)⁻¹ * ((2 * Real.pi : ℂ) * Pm z)) (Icc (-N) N) volume from h2).congr_fun
      (fun z _ => inv_mul_cancel_left₀ h2pi (Pm z)) measurableSet_Icc
  · obtain ⟨Ca, hCa⟩ := (hasCompactSupport_of_far haN).exists_bound_of_continuous ha
    have e : (fun u => G u * (a u.2 : ℂ)) = fun u => S.indicator G u * (a u.2 : ℂ) := by
      funext u
      by_cases hu : u ∈ S
      · rw [indicator_of_mem hu]
      · rw [indicator_of_notMem hu, haN _ (not_le.mp hu)]
        simp
    have hint : Integrable (fun u => S.indicator G u * (a u.2 : ℂ)) boxMeasure :=
      hGi.mul_bdd (c := Ca) (Complex.continuous_ofReal.comp (ha.comp continuous_snd)).aestronglyMeasurable
        (Eventually.of_forall fun u => by rw [Complex.norm_real]; exact hCa _)
    refine ⟨e ▸ hint, ?_⟩
    show ∫ u, G u * (a u.2 : ℂ) ∂boxMeasure = _
    rw [e, boxMeasure, integral_prod_symm _ hint, ← integral_const_mul]
    refine integral_congr_ae (hsl.mono fun z hz => ?_)
    simp only
    rw [integral_mul_const, hz]
    by_cases hzI : z ∈ Icc (-N) N
    · rw [indicator_of_mem hzI]
      ring
    · rw [indicator_of_notMem hzI, haN z (by
        rw [mem_Icc, not_and_or, not_le, not_le] at hzI
        rcases hzI with h | h
        · exact lt_of_lt_of_le (by linarith) (neg_le_abs z)
        · exact lt_of_lt_of_le h (le_abs_self z))]
      simp

private lemma continuous_setIntegral_mul {F : ℝ → ℂ} {a b : ℝ} (hF : IntegrableOn F (Icc a b)) :
    Continuous (fun u : C(ℝ, ℝ) => ∫ z in Icc a b, F z * (u z : ℂ)) := by
  refine continuous_iff_continuousAt.2 fun u0 => ?_
  have hloc : TendstoLocallyUniformly (fun (u : C(ℝ, ℝ)) (z : ℝ) => u z) u0 (𝓝 u0) :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 tendsto_id
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 hloc) _ (isCompact_Icc (a := a) (b := b))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn u0.continuous.continuousOn
  have hev : ∀ᶠ u in 𝓝 u0, ∀ z ∈ Icc a b, dist (u0 z) (u z) < 1 :=
    Metric.tendstoUniformlyOn_iff.1 hunif 1 one_pos
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖F z‖ * (C + 1)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun u =>
      hF.1.mul (Complex.continuous_ofReal.comp u.continuous).aestronglyMeasurable
  · filter_upwards [hev] with u hu
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun z hz => ?_)
    rw [norm_mul, Complex.norm_real]
    have h1 := hC z hz
    have h2 := hu z hz
    rw [Real.dist_eq] at h2
    gcongr
    rw [Real.norm_eq_abs] at h1 ⊢
    linarith [abs_sub_abs_le_abs_sub (u z) (u0 z), abs_sub_comm (u0 z) (u z)]
  · exact hF.norm.mul_const _
  · exact Eventually.of_forall fun z => tendsto_const_nhds.mul
      ((Complex.continuous_ofReal.comp (continuous_eval_const z : Continuous fun u : C(ℝ, ℝ) => u z)).tendsto u0)

private def testPairs (N : ℕ) : Set (C(ℝ, ℝ) × C(ℝ, ℝ)) :=
  {p | ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ tsupport ψ ⊆ Icc (-(N : ℝ)) N ∧ ⇑p.1 = ψ ∧ ⇑p.2 = deriv ψ}

private lemma line_test_density : ∃ D : Set (ℝ → ℝ), D.Countable ∧
    (∀ ψ ∈ D, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ) ∧
    ∀ F Fz : ℝ → ℂ, (∀ N : ℕ, IntegrableOn F (Icc (-(N : ℝ)) N) ∧ IntegrableOn Fz (Icc (-(N : ℝ)) N)) →
      (∀ ψ ∈ D, ∫ z, F z * ((deriv ψ z : ℝ) : ℂ) = -∫ z, Fz z * (ψ z : ℂ)) →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        ∫ z, F z * ((deriv ψ z : ℝ) : ℂ) = -∫ z, Fz z * (ψ z : ℂ) := by
  choose T hTc hTd using fun N : ℕ => TopologicalSpace.exists_countable_dense (testPairs N)
  refine ⟨⋃ N, (fun p : testPairs N => ⇑p.1.1) '' T N, countable_iUnion fun N => (hTc N).image _, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨N, hN⟩ := mem_iUnion.1 hψ
    obtain ⟨p, -, rfl⟩ := hN
    obtain ⟨φ, hφ, hsupp, h1, -⟩ := p.2
    show ContDiff ℝ ∞ (⇑p.1.1) ∧ HasCompactSupport (⇑p.1.1)
    rw [h1]
    exact ⟨hφ, IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp⟩
  · intro F Fz hint hD ψ hψ hψc
    obtain ⟨N0, hN0, hψN0⟩ := exists_support_bound hψc
    set N : ℕ := ⌈N0⌉₊
    have hsupp : tsupport ψ ⊆ Icc (-(N : ℝ)) N :=
      (tsupport_subset_Icc hψN0).trans (Icc_subset_Icc (by linarith [Nat.le_ceil N0]) (Nat.le_ceil N0))
    have hres : ∀ φ : ℝ → ℝ, tsupport φ ⊆ Icc (-(N : ℝ)) N →
        (∫ z, F z * ((deriv φ z : ℝ) : ℂ) = ∫ z in Icc (-(N : ℝ)) N, F z * ((deriv φ z : ℝ) : ℂ)) ∧
        (∫ z, Fz z * (φ z : ℂ) = ∫ z in Icc (-(N : ℝ)) N, Fz z * (φ z : ℂ)) := by
      intro φ hφ
      constructor
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
        rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hφ (tsupport_deriv_subset h)))]
        simp
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
        rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hφ h))]
        simp
    set Φ : C(ℝ, ℝ) × C(ℝ, ℝ) → ℂ := fun p => (∫ z in Icc (-(N : ℝ)) N, F z * (p.2 z : ℂ)) +
      ∫ z in Icc (-(N : ℝ)) N, Fz z * (p.1 z : ℂ) with hΦdef
    have hΦ : Continuous Φ := ((continuous_setIntegral_mul (hint N).1).comp continuous_snd).add
      ((continuous_setIntegral_mul (hint N).2).comp continuous_fst)
    have hzero : (fun p : testPairs N => Φ p.1) = fun _ => 0 := by
      refine Continuous.ext_on (hTd N) (hΦ.comp continuous_subtype_val) continuous_const fun p hp => ?_
      obtain ⟨φ, -, hφs, h1, h2⟩ := p.2
      have hmem : ⇑p.1.1 ∈ ⋃ N, (fun p : testPairs N => ⇑p.1.1) '' T N := mem_iUnion.2 ⟨N, p, hp, rfl⟩
      have key := hD _ hmem
      rw [h1] at key
      simp only [hΦdef, h1, h2]
      rw [← (hres φ hφs).1, ← (hres φ hφs).2, key, neg_add_cancel]
    have hp : ((⟨ψ, hψ.continuous⟩ : C(ℝ, ℝ)), (⟨deriv ψ, hψ.continuous_deriv (by simp)⟩ : C(ℝ, ℝ))) ∈
        testPairs N := ⟨ψ, hψ, hsupp, rfl, rfl⟩
    have h0 := congrFun hzero ⟨_, hp⟩
    simp only [hΦdef, ContinuousMap.coe_mk] at h0
    rw [(hres ψ hsupp).1, (hres ψ hsupp).2]
    linear_combination h0

private lemma lineMoment_eq {q : ℝ → Space → ℝ} {dq : ℝ → Space → Space} (ξ : ℤ × ℤ) {r : ℝ}
    (hr : sliceGood q dq r) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    lineMoment q dq ξ ψ r = (2 * Real.pi : ℂ) * ((∫ z, planeScalar ξ q r z * ((deriv ψ z : ℝ) : ℂ)) +
      ∫ z, planeScalarHeight ξ dq r z * (ψ z : ℂ)) := by
  obtain ⟨N0, hN0, hψN0⟩ := exists_support_bound hψc
  have hψN : ∀ z, ((⌈N0⌉₊ : ℕ) : ℝ) < |z| → ψ z = 0 := fun z hz =>
    hψN0 z (lt_of_le_of_lt (Nat.le_ceil N0) hz)
  have h1 := (slice_mode ξ q (hr ⌈N0⌉₊).1).2 (deriv ψ) (hψ.continuous_deriv (by simp))
    (deriv_eq_zero_of_far hψN)
  have h2 := (slice_mode ξ (fun τ y => dq τ y 2) (hr ⌈N0⌉₊).2).2 ψ hψ.continuous hψN
  have e : (fun u : (ℝ × ℝ) × ℝ => modeFactor ξ u.1.1 u.1.2 *
      ((q u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ) * ((deriv ψ u.2 : ℝ) : ℂ) +
        (dq u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) 2 : ℂ) * (ψ u.2 : ℂ))) =
      fun u => modeFactor ξ u.1.1 u.1.2 * (q u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) : ℂ) *
          ((deriv ψ u.2 : ℝ) : ℂ) +
        modeFactor ξ u.1.1 u.1.2 * (dq u.1.1 (CellCert.CellAnalysis.cylPoint r u.1.2 u.2) 2 : ℂ) *
          (ψ u.2 : ℂ) := by
    funext u
    ring
  rw [lineMoment, e, integral_add h1.1 h2.1, h1.2, h2.2, mul_add]
  rfl

theorem scalarHeightDeriv : ScalarHeightDerivHolds := by
  intro q dq hq hdq _ _ hw hL _ ξ
  obtain ⟨D, hDc, hDs, hdense⟩ := line_test_density
  have hmom : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ ψ ∈ D, lineMoment q dq ξ ψ r = 0 := by
    refine (ae_ball_iff hDc).2 fun ψ hψ => ?_
    obtain ⟨N, hN, hψN⟩ := exists_support_bound (hDs ψ hψ).2
    exact ae_lineMoment_eq_zero hq hdq hL hw ξ (hDs ψ hψ).1 hN hψN
  filter_upwards [ae_sliceGood hq hdq hL, hmom] with r hr hm
  have hint : ∀ N : ℕ, IntegrableOn (planeScalar ξ q r) (Icc (-(N : ℝ)) N) ∧
      IntegrableOn (planeScalarHeight ξ dq r) (Icc (-(N : ℝ)) N) :=
    fun N => ⟨(slice_mode ξ q (hr N).1).1, (slice_mode ξ (fun τ y => dq τ y 2) (hr N).2).1⟩
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'
  have hall := hdense (planeScalar ξ q r) (planeScalarHeight ξ dq r) hint (fun ψ hψ => by
    have h0 := hm ψ hψ
    rw [lineMoment_eq ξ hr (hDs ψ hψ).1 (hDs ψ hψ).2] at h0
    have h1 := (mul_eq_zero.1 h0).resolve_left h2pi
    linear_combination h1)
  intro h hh
  obtain ⟨N, hN⟩ := exists_nat_ge h
  have hsub : Ioo (-h) h ⊆ Icc (-(N : ℝ)) N :=
    Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith) hN)
  refine ⟨(hint N).1.mono_set hsub, (hint N).2.mono_set hsub, fun ψ hψ hψc hψs => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hz (hψs (tsupport_deriv_subset h')))]
      simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hz (hψs h'))]
      simp)]
  exact hall ψ hψ hψc

end Bridge

end CertCell

end Breakdown
