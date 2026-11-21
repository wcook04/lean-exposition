import Breakdown.CertCell.InstanceMomentUpper

open scoped ENNReal NNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.RowIdentity

open Breakdown Breakdown.CertCell
open Instance.Internal.MomentUpper

theorem orbit_quasiMeasurePreserving : Measure.QuasiMeasurePreserving orbit orbitMeasure periodMeasure := by
  refine ⟨measurable_orbit, ?_⟩
  have h := orbitMeasure_ac.map measurable_orbit
  rwa [map_orbit] at h

theorem orbitMeasure_eq : orbitMeasure = (volume.restrict openHalf).prod sliceMeasure := rfl

theorem ae_slice_of_ae {Q : ℝ × Space → Prop} (h : ∀ᵐ z : ℝ × Space, Q z) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → ∀ᵐ s ∂sliceMeasure, Q (s.1, axialRot s.2 (planePoint p)) := by
  have h1 : ∀ᵐ z ∂periodMeasure, Q z := by
    rw [periodMeasure_eq]; exact ae_restrict_of_ae h
  have h2 : ∀ᵐ w ∂orbitMeasure, Q (orbit w) := orbit_quasiMeasurePreserving.ae h1
  rw [orbitMeasure_eq] at h2
  have h3 := Measure.ae_ae_of_ae_prod h2
  rw [ae_restrict_iff' measurableSet_openHalf] at h3
  filter_upwards [h3] with p hp hp1
  exact hp ⟨hp1, trivial⟩

theorem sliceMeasure_eq : sliceMeasure = volume.restrict (Ioc (0 : ℝ) 1 ×ˢ Ioc 0 (2 * Real.pi)) := by
  rw [sliceMeasure, Measure.prod_restrict, Measure.volume_eq_prod]

theorem sliceMeasure_ne_zero : sliceMeasure ≠ 0 := by
  intro h
  have h1 : sliceMeasure univ = 0 := by rw [h]; rfl
  rw [sliceMeasure_eq, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioc, Real.volume_Ioc] at h1
  simp only [sub_zero, mul_eq_zero, ENNReal.ofReal_eq_zero] at h1
  rcases h1 with h1 | h1
  · norm_num at h1
  · have := Real.pi_pos; linarith

theorem norm_orbit_sq (p : ℝ × ℝ) (hp : 0 ≤ p.1) (φ : ℝ) :
    ‖axialRot φ (planePoint p)‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [norm_sq_pointPlane, pointPlane_orbit hp]

theorem ae_slice_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : ℝ × Space → E}
    (hX : LocallyIntegrable X volume) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → Integrable (fun s : ℝ × ℝ => X (s.1, axialRot s.2 (planePoint p))) sliceMeasure := by
  set T : ℕ → Set (ℝ × Space) := fun n => Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) n with hT
  have hTc : ∀ n, IsCompact (T n) := fun n => isCompact_Icc.prod (isCompact_closedBall _ _)
  have hTm : ∀ n, MeasurableSet (T n) := fun n => measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hg : ∀ n, Integrable ((T n).indicator X) periodMeasure := fun n => by
    rw [periodMeasure_eq]
    exact ((integrable_indicator_iff (hTm n)).2 ((hX.integrableOn_isCompact (hTc n)))).restrict
  have hn : ∀ n, ∀ᵐ p ∂(volume.restrict openHalf),
      Integrable (fun s : ℝ × ℝ => p.1 • (T n).indicator X (orbit (p, s))) sliceMeasure := by
    intro n
    have h := (integral_orbit (hg n)).1
    rw [orbitMeasure_eq] at h
    exact h.prod_right_ae
  have hall := ae_all_iff.2 hn
  rw [ae_restrict_iff' measurableSet_openHalf] at hall
  filter_upwards [hall] with p hp hp1
  have hp1' : 0 < p.1 := hp1
  obtain ⟨n, hn⟩ := exists_nat_ge (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
  have h1 := (hp ⟨hp1, trivial⟩ n).smul (p.1⁻¹)
  refine h1.congr ?_
  have hmem : ∀ᵐ s ∂sliceMeasure, s ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc 0 (2 * Real.pi) := by
    rw [sliceMeasure_eq]; exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  filter_upwards [hmem] with s hs
  have hin : orbit (p, s) ∈ T n := by
    refine ⟨Ioc_subset_Icc_self hs.1, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have e := norm_orbit_sq p hp1'.le s.2
    have h0 : ‖axialRot s.2 (planePoint p)‖ = Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := by
      rw [← e, Real.sqrt_sq (norm_nonneg _)]
    show ‖axialRot s.2 (planePoint p)‖ ≤ n
    rw [h0]; exact hn
  simp only [Pi.smul_apply, indicator_of_mem hin, smul_smul, inv_mul_cancel₀ hp1'.ne', one_smul]
  rfl

theorem ae_plane_of_ae_space {β : Type*} [Zero β] {E : Space → β} (h0 : ∀ᵐ y : Space, E y = 0)
    (hcov : ∀ᵐ p : ℝ × ℝ, 0 < p.1 → ∀ φ : ℝ, E (axialRot φ (planePoint p)) = 0 → E (planePoint p) = 0) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → E (planePoint p) = 0 := by
  have h1 : ∀ᵐ z : ℝ × Space, E z.2 = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))).ae h0
  have h2 := ae_slice_of_ae h1
  have : (ae sliceMeasure).NeBot := ae_neBot.2 sliceMeasure_ne_zero
  filter_upwards [h2, hcov] with p hp hc hp1
  obtain ⟨s, hs⟩ := (hp hp1).exists
  exact hc hp1 s.2 hs

theorem labelVel_sum_of_slice {κ : Type*} (s : Finset κ) (c : κ → ℝ) (X : κ → ℝ → Space → Space)
    {F : ℝ → Space → Space} {p : ℝ × ℝ}
    (hX : ∀ k ∈ s, Integrable (fun t : ℝ × ℝ => X k t.1 (axialRot t.2 (planePoint p))) sliceMeasure)
    (hF : ∀ᵐ t ∂sliceMeasure, F t.1 (axialRot t.2 (planePoint p))
      = ∑ k ∈ s, c k • X k t.1 (axialRot t.2 (planePoint p))) (m : ℕ) (ι : ℤ × ℤ) (a : Fin 3) :
    labelVel m ι F p a = ∑ k ∈ s, (c k : ℂ) * labelVel m ι (X k) p a := by
  have hΦ : Integrable (fun t : ℝ × ℝ => F t.1 (axialRot t.2 (planePoint p))) sliceMeasure :=
    (integrable_finsetSum s fun k hk => (hX k hk).smul (c k)).congr (by
      filter_upwards [hF] with t ht; rw [ht]; simp only [Pi.smul_apply])
  rw [labelVel_eq hΦ m ι a]
  have hI : ∀ k ∈ s, Integrable (fun t : ℝ × ℝ => starRingEnd ℂ (labelPhase m ι t.1 t.2) *
      ((inner ℝ (X k t.1 (axialRot t.2 (planePoint p))) (frameUnit t.2 a) : ℝ) : ℂ)) sliceMeasure :=
    fun k hk => integrable_phase (hX k hk) (fun t => starRingEnd ℂ (labelPhase m ι t.1 t.2))
      (Complex.continuous_conj.comp (continuous_labelPhase m ι))
      (fun t => by rw [Complex.norm_conj, norm_labelPhase]) a
  have e : (fun t : ℝ × ℝ => starRingEnd ℂ (labelPhase m ι t.1 t.2) *
      ((inner ℝ (F t.1 (axialRot t.2 (planePoint p))) (frameUnit t.2 a) : ℝ) : ℂ)) =ᵐ[sliceMeasure]
      fun t => ∑ k ∈ s, (c k : ℂ) * (starRingEnd ℂ (labelPhase m ι t.1 t.2) *
        ((inner ℝ (X k t.1 (axialRot t.2 (planePoint p))) (frameUnit t.2 a) : ℝ) : ℂ)) := by
    filter_upwards [hF] with t ht
    rw [ht, sum_inner, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, Complex.ofReal_mul]
    ring
  rw [integral_congr_ae e, integral_finsetSum s fun k hk => (hI k hk).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [labelVel_eq (hX k hk) m ι a, integral_const_mul]
  ring

end Breakdown.CertCell.Assembly.Internal.RowIdentity
