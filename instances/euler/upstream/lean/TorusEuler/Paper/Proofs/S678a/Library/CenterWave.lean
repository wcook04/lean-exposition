import TorusEuler.Paper.Proofs.S678a.Library.GrowingCrossing
import TorusEuler.LocalizedAmplitudeComparison

/-! # The center data of a later wave from Lemma 2.6 (package S678a)

Copy of `LocalizedAmplitude.exists_laterWave_centerWaveOn_threshold`
(LocalizedAmplitudeComparison.lean:1518) with the growth bound (`exists_physical_growth_bound_threshold`,
content of 2.6) replaced by the last clause of `h2_6` (`Statement.lemma_2_6`, sections/03_amplification.tex
Lemma 2.6): the transfer maps `Φ` between the transverse planes have norm at most
`252 e S ‖a(τ₂)‖/‖a(τ₁)‖`. This is (5.5) of the later wave (sections/08b_induction.tex:60-93), the
`CenterWaveOn` hypothesis of the seed construction, with `D = λ^9`. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler TorusEuler.MovingWaveVector TorusEuler.MovingWaveVector.PhysicalAmplification
open NormedSpace (normalize)

noncomputable section

/-- The amplitude of a crossing, divided by the seed factor, is an amplitude vector of Lemma 2.6
started at the transverse seed. -/
theorem unit_amplitude' {t₀ finish T scale Ustar next : ℝ}
    {w : PhysicalAmplification (Icc t₀ finish) t₀} (hfin : w.clock T = finish)
    (d : w.GrowingCrossing T scale Ustar next) (hscale : 0 < scale) :
    NewWaveVector w scale d.waveVector ∧
      AmplitudeVector w d.waveVector (fun t => d.seedFactor⁻¹ • d.amplitude t) ∧
      (fun t => d.seedFactor⁻¹ • d.amplitude t) t₀ =
        (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1 := by
  have hslab : w.activeSlab T = Icc t₀ finish := by unfold activeSlab; rw [hfin]
  have hc := d.seedFactor_pos
  refine ⟨⟨hscale, d.initial_waveVector, fun t ht => by
    have := d.waveVector_derivative t (by rwa [hslab]); rwa [hslab] at this⟩, ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    have h := (d.amplitude_derivative t (by rwa [hslab])).const_smul d.seedFactor⁻¹
    rw [hslab] at h
    refine h.congr_deriv ?_
    simp only [affineWaveAmplitudeOperator_apply, affineWavePressureCoeff, map_smul,
      real_inner_smul_right, smul_add, smul_neg, smul_smul]
    ring_nf
  · intro t ht
    rw [real_inner_comm, real_inner_smul_right, (d.transverse t (by rwa [hslab])).2.2, mul_zero]
  · simp only [d.initial_amplitude, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- **Center data of the later wave** (the `center` field of the wave selection;
sections/08b_induction.tex:60-93). If `h2_6` holds for `C₀ ≥ N` and `D ≥ 252 e S`,
`D ≥ 2/(ν ε)`, the crossing satisfies `CenterWaveOn` of the parent gradient on `[t₀, finish]`:
(5.5) of the later wave, with the transport bound from the last clause of Lemma 2.6 and the coupling
bound from `ν₊ ≥ εν/2` of Lemma 2.7 (`first_coupling_lower`). -/
theorem centerWaveOn_of_growingCrossingV (h2_6 : Statement.lemma_2_6) :
    ∃ N : ℕ, ∀ {t₀ finish T scale Ustar next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (w : PhysicalAmplification (Icc t₀ finish) t₀), w.clock T = finish → 2 ≤ T → 0 < scale →
      (C₀ : ℝ) * w.ratio ≤ 1 → (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
      ∀ d : w.GrowingCrossing T scale Ustar next,
      ∀ D : ℝ, 252 * Real.exp 1 * w.shear ≤ D → 2 / (w.firstCoupling * w.ratio) ≤ D →
        LocalizedAmplitude.CenterWaveOn w.gradient d.waveVector d.amplitude t₀ finish D := by
  obtain ⟨C, p, N, h6⟩ := h2_6
  refine ⟨N, ?_⟩
  intro t₀ finish T scale Ustar next C₀ hC w hfin hT hscale hsmallε hsmallδ d D hDS hDν
  have hslab : w.activeSlab T = Icc t₀ finish := by unfold activeSlab; rw [hfin]
  have hc := d.seedFactor_pos
  have hmap : MapsTo w.clock (Icc 0 T) (Icc t₀ finish) := fun τ hτ => by
    have := clock_mem_activeSlab' w hτ
    rwa [hslab] at this
  obtain ⟨hNW, hAV, ha0⟩ := unit_amplitude' hfin d hscale
  have hFS : FiniteSmallness w T C₀ := ⟨hsmallε, hsmallδ⟩
  obtain ⟨-, -, -, -, hΦ⟩ := h6 hC w hT hmap hFS hNW hAV ha0
  have hbase : 0 < w.firstCoupling * w.ratio / 2 :=
    half_pos (mul_pos w.first_coupling_positive w.ratio_pos)
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · have := d.waveVector_derivative t (by rwa [hslab]); rwa [hslab] at this
  · have := d.transverse t (by rwa [hslab])
    exact ⟨this.1, this.2.1, by rw [real_inner_comm] at this; rw [real_inner_comm]; exact this.2.2⟩
  · have := d.amplitude_derivative t (by rwa [hslab]); rwa [hslab] at this
  · intro z hz hperp u v hu hv huv
    have hzA : AmplitudeVector w d.waveVector z := by
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · simpa only [affineWaveAmplitudeOperator_apply, affineWavePressureCoeff] using hz t ht
      · rw [real_inner_comm]; exact hperp t ht
    have hu' : u ∈ w.activeSlab T := by rwa [hslab]
    have hv' : v ∈ w.activeSlab T := by rwa [hslab]
    have hτu := elapsed_mem_activeSlab' w hu'
    have hτv := elapsed_mem_activeSlab' w hv'
    obtain ⟨Φ, hΦb, hΦn⟩ := hΦ (w.elapsed u) (w.elapsed v) hτu.1
      (w.strictMono_elapsed.monotone huv) hτv.2
    have hzu : z (w.clock (w.elapsed u)) ∈
        transversePlane (d.waveVector (w.clock (w.elapsed u))) := by
      rw [clock_elapsed]
      change ⟪d.waveVector u, z u⟫_ℝ = 0
      exact hperp u hu
    let x : transversePlane (d.waveVector (w.clock (w.elapsed u))) :=
      ⟨z (w.clock (w.elapsed u)), hzu⟩
    have hz' := hΦb z hzA x rfl
    have hnorm : ‖z (w.clock (w.elapsed v))‖ ≤
        ‖Φ.toContinuousLinearMap‖ * ‖z (w.clock (w.elapsed u))‖ := by
      have h : ‖Φ x‖ ≤ ‖Φ.toContinuousLinearMap‖ * ‖x‖ := Φ.toContinuousLinearMap.le_opNorm x
      have e1 : ‖Φ x‖ = ‖z (w.clock (w.elapsed v))‖ := by
        rw [← hz']; rfl
      have hx : ‖x‖ = ‖z (w.clock (w.elapsed u))‖ := rfl
      rw [e1, hx] at h
      exact h
    simp only [clock_elapsed] at hnorm hΦn
    have hau := (d.transverse u hu').2.1
    have hav := (d.transverse v hv').2.1
    have hnu : 0 < ‖d.amplitude u‖ := norm_pos_iff.mpr hau
    have hnv : 0 < ‖d.amplitude v‖ := norm_pos_iff.mpr hav
    have hscaleN (x : ℝ) : ‖d.seedFactor⁻¹ • d.amplitude x‖ = d.seedFactor⁻¹ * ‖d.amplitude x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    rw [hscaleN, hscaleN] at hΦn
    have hS : 0 ≤ 252 * Real.exp 1 * w.shear := by
      have := w.initialStrength_pos
      have : 0 < w.shear := div_pos w.initialStrength_pos w.rate_pos
      positivity
    have h1 : ‖Φ.toContinuousLinearMap‖ ≤ 252 * Real.exp 1 * w.shear *
        (‖d.amplitude v‖ / ‖d.amplitude u‖) := by
      refine hΦn.trans_eq ?_
      field_simp
    rw [div_le_iff₀ hnv]
    calc ‖z v‖ ≤ ‖Φ.toContinuousLinearMap‖ * ‖z u‖ := hnorm
      _ ≤ (252 * Real.exp 1 * w.shear * (‖d.amplitude v‖ / ‖d.amplitude u‖)) * ‖z u‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ (D * (‖d.amplitude v‖ / ‖d.amplitude u‖)) * ‖z u‖ := by
        gcongr
      _ = D * (‖z u‖ / ‖d.amplitude u‖) * ‖d.amplitude v‖ := by field_simp
  · have ht' : t ∈ w.activeSlab T := by rwa [hslab]
    obtain ⟨hk0, ha0', -⟩ := d.transverse t ht'
    have hnu := d.first_coupling_lower t ht'
    have hInv : (w.firstCoupling * w.ratio / 2)⁻¹ = 2 / (w.firstCoupling * w.ratio) := inv_div _ _
    have hDinv : D⁻¹ ≤ w.firstCoupling * w.ratio / 2 := by
      have h := inv_anti₀ (inv_pos.mpr hbase) (hInv.trans_le hDν)
      exact h.trans_eq (inv_inv _)
    have hkn : 0 < ‖d.waveVector t‖ := norm_pos_iff.mpr hk0
    have han : 0 < ‖d.amplitude t‖ := norm_pos_iff.mpr ha0'
    have hid : ⟪d.waveVector t, w.gradient t (d.amplitude t)⟫_ℝ =
        ‖d.waveVector t‖ * ‖d.amplitude t‖ * w.physicalNu d.waveVector d.amplitude t := by
      unfold physicalNu NormedSpace.normalize
      simp only [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      field_simp
    rw [hid]
    have := mul_le_mul_of_nonneg_left (hDinv.trans hnu) (mul_pos hkn han).le
    linarith [mul_comm D⁻¹ (‖d.waveVector t‖ * ‖d.amplitude t‖)]

end

end TorusEuler.Paper.Lib.S678a
