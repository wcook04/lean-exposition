import TorusEuler.PhysicalAmplification
import TorusEuler.AmplificationCouplings

/-! Central data at the first physical crossing after the reference turning time. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.AmplificationCrossing

/-- The level set of a continuous ratio on a compact interval has a first crossing
whenever it has a crossing. -/
theorem exists_least_crossing_Icc {a b next : ℝ} {ρ : ℝ → ℝ}
    (hρ : ContinuousOn ρ (Icc a b)) (hexists : ∃ t ∈ Icc a b, ρ t = next) :
    ∃ t ∈ Icc a b, ρ t = next ∧ ∀ s ∈ Icc a b, ρ s = next → t ≤ s := by
  let I := Icc a b
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let level : Set I := {u | ρ u = next}
  have hclosed : IsClosed level := isClosed_eq hρ.domRestrict continuous_const
  let crossings := (fun u : I => (u : ℝ)) '' level
  have hcompact : IsCompact crossings := hclosed.isCompact.image continuous_subtype_val
  obtain ⟨v, hv, hcross⟩ := hexists
  have hnonempty : crossings.Nonempty := ⟨v, ⟨⟨v, hv⟩, hcross, rfl⟩⟩
  obtain ⟨t, ht⟩ := hcompact.exists_isLeast hnonempty
  obtain ⟨u, hu, rfl⟩ := ht.1
  exact ⟨u, u.property, hu, fun s hs hse => ht.2 ⟨⟨s, hs⟩, hse, rfl⟩⟩

end TorusEuler.AmplificationCrossing

namespace TorusEuler.ReferenceAmplitude

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A prescribed positive peak is obtained by a single positive constant rescaling of an
amplitude with an attained positive maximum. -/
theorem exists_positive_vector_peak_rescaling {a : ℝ → W} {J : Set ℝ} {peak Ustar : ℝ}
    (hpeak : IsGreatest ((fun t => ‖a t‖) '' J) peak) (hpeak₀ : 0 < peak)
    (hUstar : 0 < Ustar) :
    ∃ c > 0, c * peak = Ustar ∧
      IsGreatest ((fun t => ‖c • a t‖) '' J) Ustar := by
  let c := Ustar / peak
  have hc : 0 < c := div_pos hUstar hpeak₀
  have hcPeak : c * peak = Ustar := div_mul_cancel₀ _ hpeak₀.ne'
  refine ⟨c, hc, hcPeak, ?_⟩
  constructor
  · obtain ⟨t, ht, htpeak⟩ := hpeak.1
    refine ⟨t, ht, ?_⟩
    change ‖a t‖ = peak at htpeak
    change ‖c • a t‖ = Ustar
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, htpeak, hcPeak]
  · rintro _ ⟨t, ht, rfl⟩
    change ‖c • a t‖ ≤ Ustar
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← hcPeak]
    exact mul_le_mul_of_nonneg_left (hpeak.2 (mem_image_of_mem _ ht)) hc.le

/-- Rescaling to the prescribed peak preserves the strength divided by the physical
frequency scale and the peak. -/
theorem peak_relative_strength_smul (a k : W) {c peak Ustar scale : ℝ}
    (hc : 0 < c) (hcPeak : c * peak = Ustar) :
    ‖c • a‖ * ‖k‖ / (scale * Ustar) = ‖a‖ * ‖k‖ / (scale * peak) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← hcPeak]
  have hnum : c * ‖a‖ * ‖k‖ = c * (‖a‖ * ‖k‖) := mul_assoc _ _ _
  have hden : scale * (c * peak) = c * (scale * peak) := mul_left_comm _ _ _
  rw [hnum, hden, mul_div_mul_left _ _ hc.ne']

/-- A gain estimate expressed relative to the old attained peak is equivalent to
the same gain estimate relative to the prescribed new peak. -/
theorem peak_relative_gain_smul_iff (a : W) {c peak Ustar gain : ℝ}
    (hc : 0 < c) (hcPeak : c * peak = Ustar) :
    ‖c • a‖ ≤ gain * Ustar ↔ ‖a‖ ≤ gain * peak := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← hcPeak, mul_left_comm gain c,
    mul_le_mul_iff_right₀ hc]

end TorusEuler.ReferenceAmplitude

namespace TorusEuler.MovingWaveVector

private theorem affineWaveAmplitudeOperator_smul_strain_apply
    (d : Space →L[ℝ] Space) (k a : Space) (c : ℝ) :
    affineWaveAmplitudeOperator (c • d) k a = c • affineWaveAmplitudeOperator d k a := by
  simp only [affineWaveAmplitudeOperator_apply, smul_apply, real_inner_smul_right, smul_add,
    smul_neg, smul_smul]
  congr 2
  ring

theorem mapsTo_inverse_amplificationTime_Icc {r t₀ T : ℝ} (hr : 0 < r) :
    MapsTo (fun t => r * (t - t₀)) (Icc t₀ (t₀ + T / r)) (Icc 0 T) := by
  intro t ht
  refine ⟨mul_nonneg hr.le (sub_nonneg.mpr ht.1), ?_⟩
  have h : t - t₀ ≤ T / r := by linarith [ht.2]
  simpa only [mul_comm r (t - t₀)] using (le_div_iff₀ hr).mp h

/-- The physical clock restores both affine-wave derivatives, with any constant
amplitude scaling. The derivatives are taken within the entire closed slab. -/
theorem physical_affineWave_derivatives {k a : ℝ → Space}
    {M : ℝ → Space →L[ℝ] Space} {r t₀ T c : ℝ} (hr : 0 < r)
    (hk : ∀ τ ∈ Icc 0 T, HasDerivWithinAt k
      (-(((1 / r) • M (t₀ + τ / r)).adjoint (k τ))) (Icc 0 T) τ)
    (ha : ∀ τ ∈ Icc 0 T, HasDerivWithinAt a
      (affineWaveAmplitudeOperator ((1 / r) • M (t₀ + τ / r)) (k τ) (a τ)) (Icc 0 T) τ) :
    let J := Icc t₀ (t₀ + T / r)
    let K := fun t => k (r * (t - t₀))
    let A := fun t => c • a (r * (t - t₀))
    (∀ t ∈ J, HasDerivWithinAt K (-((M t).adjoint (K t))) J t) ∧
    (∀ t ∈ J, HasDerivWithinAt A (affineWaveAmplitudeOperator (M t) (K t) (A t)) J t) := by
  let τ := fun t => r * (t - t₀)
  let J := Icc t₀ (t₀ + T / r)
  have hmap : MapsTo τ J (Icc 0 T) := mapsTo_inverse_amplificationTime_Icc hr
  have hinv (t : ℝ) : t₀ + τ t / r = t := by
    dsimp only [τ]
    field_simp
    ring
  have hclock (t : ℝ) : HasDerivWithinAt τ r J t := by
    simpa only [mul_one, τ, id_eq] using
      (((hasDerivAt_id t).sub_const t₀).const_mul r).hasDerivWithinAt
  have hcancel : r * (1 / r) = 1 := by field_simp
  constructor
  · intro t ht
    refine ((hk _ (hmap ht)).scomp t (hclock t) hmap).congr_deriv ?_
    change r • (-(((1 / r) • M (t₀ + τ t / r)).adjoint (k (τ t)))) = _
    simp only [hinv, map_smul, smul_apply, smul_neg, smul_smul, hcancel, one_smul]
    rfl
  · intro t ht
    refine (((ha _ (hmap ht)).scomp t (hclock t) hmap).const_smul c).congr_deriv ?_
    change c • (r • affineWaveAmplitudeOperator ((1 / r) • M (t₀ + τ t / r))
      (k (τ t)) (a (τ t))) = _
    rw [hinv, affineWaveAmplitudeOperator_smul_strain_apply, smul_smul r, hcancel, one_smul,
      map_smul]

end TorusEuler.MovingWaveVector

namespace TorusEuler.MovingWaveVector.PhysicalAmplification

open NormedSpace (normalize)
open AmplificationCrossing (crossingHorizon exists_least_crossing_Icc)
open ReferenceAmplitude (exists_positive_vector_peak_rescaling peak_relative_strength_smul peak_relative_gain_smul_iff)
open GrowingCoupling (normalizedNu normalizedEta)

noncomputable section

variable {I : Set ℝ} {t₀ T : ℝ} {C₀ : ℕ} (w : PhysicalAmplification I t₀)

/-- The gradient on the normalized window is the full physical gradient
evaluated at the corresponding physical time and divided by the growth rate. -/
theorem toNormalized_gradient_eq
    (hT : 2 ≤ T) (hC₀ : 240 ≤ C₀) (hclock : MapsTo w.clock (Icc 0 T) I)
    (hsmallε : (C₀ : ℝ) * w.ratio ≤ 1)
    (hsmallδ : (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (w.toNormalized hT hC₀ hclock hsmallε hsmallδ).gradient t =
      (1 / w.rate) • w.gradient (w.clock t) := by
  obtain ⟨hk₀, ha₀, _⟩ := w.preceding_data t₀ w.activation
  obtain ⟨hk, ha, _⟩ := w.preceding_data (w.clock t) (hclock ht)
  have h := normalized_strain_eq
    (kp := fun τ => w.kp (w.clock τ)) (ap := fun τ => w.ap (w.clock τ))
    (B := w.B (w.clock t)) (E := w.E (w.clock t)) w.rate_pos.ne'
    (by simpa only [clock_zero] using hk₀) (by simpa only [clock_zero] using ha₀) hk ha
  simpa only [toNormalized, AmplificationWindow.gradient, AmplificationWindow.basis,
    AmplificationWindow.shearRatio, shear, initialStrength, clock_zero,
    PhysicalAmplification.gradient] using h

/-- The physical value of each new coupling divided by the activation
coupling equals its normalized-coordinate counterpart. -/
theorem toNormalized_couplings_eq
    (hT : 2 ≤ T) (hC₀ : 240 ≤ C₀) (hclock : MapsTo w.clock (Icc 0 T) I)
    (hsmallε : (C₀ : ℝ) * w.ratio ≤ 1)
    (hsmallδ : (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio)
    {t : ℝ} (ht : t ∈ Icc 0 T) (k a : Space) :
    let W := w.toNormalized hT hC₀ hclock hsmallε hsmallδ
    let M := w.gradient (w.clock t)
    normalizedNu (W.gradient t) k a w.shear =
        ⟪normalize k, M (normalize a)⟫_ℝ / w.firstCoupling ∧
      normalizedEta (W.gradient t) k a w.shear =
        ⟪cross3 (normalize k) (normalize a), M (normalize a)⟫_ℝ / w.firstCoupling := by
  have hr_sq : w.rate ^ 2 = 2 * w.initialStrength * w.firstCoupling :=
    amplificationGrowthRate_sq w.initialStrength_pos w.first_coupling_positive
  have hf : 2 * w.shear * (1 / w.rate) = 1 / w.firstCoupling := by
    calc
      _ = 2 * w.initialStrength / w.rate ^ 2 := by
        unfold shear
        field_simp
      _ = _ := by rw [hr_sq]; field_simp [w.initialStrength_pos.ne', w.first_coupling_positive.ne']
  have hf_apply (b : ℝ) : 2 * w.shear * ((1 / w.rate) * b) = b / w.firstCoupling := by
    rw [← mul_assoc, hf, one_div_mul_eq_div]
  dsimp only
  rw [w.toNormalized_gradient_eq hT hC₀ hclock hsmallε hsmallδ ht]
  constructor <;> simp only [normalizedNu, normalizedEta, smul_apply, real_inner_smul_right,
    hf_apply]

/-- The normalized time of a point on the physical clock. -/
def elapsed (t : ℝ) : ℝ := w.rate * (t - t₀)

/-- The physical interval corresponding to the normalized slab. -/
def activeSlab (T : ℝ) : Set ℝ := Icc t₀ (w.clock T)

@[simp] theorem elapsed_clock (τ : ℝ) : w.elapsed (w.clock τ) = τ := by
  unfold elapsed clock
  rw [add_sub_cancel_left, mul_div_cancel₀ _ w.rate_pos.ne']

@[simp] theorem clock_elapsed (t : ℝ) : w.clock (w.elapsed t) = t := by
  unfold clock elapsed
  rw [mul_comm w.rate, mul_div_cancel_right₀ _ w.rate_pos.ne', add_sub_cancel]

theorem strictMono_clock : StrictMono w.clock := by
  intro a b hab
  exact add_lt_add_of_le_of_lt le_rfl (div_lt_div_of_pos_right hab w.rate_pos)

theorem strictMono_elapsed : StrictMono w.elapsed := by
  intro a b hab
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hab _) w.rate_pos

private theorem elapsed_mem_Icc {a b t : ℝ} (ht : t ∈ Icc (w.clock a) (w.clock b)) :
    w.elapsed t ∈ Icc a b := by
  have ha := w.strictMono_elapsed.monotone ht.1
  have hb := w.strictMono_elapsed.monotone ht.2
  exact ⟨by simpa only [elapsed_clock] using ha, by simpa only [elapsed_clock] using hb⟩

private theorem elapsed_mem_activeSlab {T t : ℝ} (ht : t ∈ w.activeSlab T) :
    w.elapsed t ∈ Icc 0 T :=
  w.elapsed_mem_Icc (a := 0) (by simpa only [clock_zero, activeSlab] using ht)

private theorem clock_mem_activeSlab {T τ : ℝ} (ht : τ ∈ Icc 0 T) : w.clock τ ∈ w.activeSlab T := by
  exact ⟨by simpa only [clock_zero] using w.strictMono_clock.monotone ht.1,
    w.strictMono_clock.monotone ht.2⟩

/-- First coupling of the physical strain in the frame of a new wave. -/
def physicalNu (k a : ℝ → Space) (t : ℝ) : ℝ :=
  ⟪normalize (k t), w.gradient t (normalize (a t))⟫_ℝ

/-- Third-axis coupling in the same physical frame. -/
def physicalEta (k a : ℝ → Space) (t : ℝ) : ℝ :=
  ⟪cross3 (normalize (k t)) (normalize (a t)), w.gradient t (normalize (a t))⟫_ℝ

private theorem abs_log_le_of_close_one {u ε : ℝ} (hε : ε ≤ 1 / 2)
    (h : |u - 1| ≤ ε) : |Real.log u| ≤ 2 * ε := by
  have hu : 1 / 2 ≤ u := by linarith [(abs_le.mp h).1]
  have hlog := ReferenceAmplitude.log_amplitude_ratio_le
    (g := 1) (h := u) (h₀ := 1) (F := 0) (φ := 0) (m := 1 / 2) (δ := ε)
    (by norm_num) (by norm_num) hu (by norm_num) h (by norm_num) (by norm_num)
  convert hlog using 1
  · simp
  · ring

/-- Physical central data for a wave with prescribed peak. The search is
restricted to the bracket after the reference turning time, as in §6. -/
structure GrowingCrossing (T scale Ustar next : ℝ) where
  waveVector : ℝ → Space
  amplitude : ℝ → Space
  referenceSlope : ℝ → ℝ
  seedFactor : ℝ
  referenceTurn : ℝ
  crossing : ℝ
  seedFactor_pos : 0 < seedFactor
  slab_in_window : w.activeSlab T ⊆ I
  initial_waveVector : waveVector t₀ = scale • w.basis t₀ 2
  initial_amplitude : amplitude t₀ = seedFactor • ((-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1)
  waveVector_derivative : ∀ t ∈ w.activeSlab T,
    HasDerivWithinAt waveVector (-((w.gradient t).adjoint (waveVector t))) (w.activeSlab T) t
  amplitude_derivative : ∀ t ∈ w.activeSlab T,
    HasDerivWithinAt amplitude (affineWaveAmplitudeOperator (w.gradient t) (waveVector t) (amplitude t))
      (w.activeSlab T) t
  transverse : ∀ t ∈ w.activeSlab T,
    waveVector t ≠ 0 ∧ amplitude t ≠ 0 ∧ ⟪waveVector t, amplitude t⟫_ℝ = 0
  peak : IsGreatest ((fun t => ‖amplitude t‖) '' w.activeSlab T) Ustar
  first_coupling_lower : ∀ t ∈ w.activeSlab T,
    w.firstCoupling * w.ratio / 2 ≤ w.physicalNu waveVector amplitude t
  reference_initial : referenceSlope 0 = 1
  reference_derivative : ∀ t ∈ Ici 0,
    HasDerivWithinAt referenceSlope (ReferenceRiccati.rhs w.ratio t (referenceSlope t)) (Ici 0) t
  turning_bounds : referenceTurn ∈ Icc (2 / w.ratio) (3 / w.ratio)
  turning_zero : referenceSlope referenceTurn = 0
  crossing_in_bracket : crossing ∈ Icc (w.clock referenceTurn) (w.clock (crossingHorizon w.ratio next))
  crossing_in_slab : crossing ∈ w.activeSlab T
  crossing_after_switch : w.clock 1 < crossing
  crossing_ratio : w.physicalEta waveVector amplitude crossing / w.physicalNu waveVector amplitude crossing = next
  crossing_least : ∀ t ∈ Icc (w.clock referenceTurn) (w.clock (crossingHorizon w.ratio next)),
    w.physicalEta waveVector amplitude t / w.physicalNu waveVector amplitude t = next → crossing ≤ t
  crossing_strength : ∀ t ∈ Icc (w.clock referenceTurn) (w.clock (crossingHorizon w.ratio next)),
    w.physicalEta waveVector amplitude t / w.physicalNu waveVector amplitude t = next →
      (Real.exp (-1) / 4) * (Real.sqrt (w.ratio * next))⁻¹ ≤
        ‖amplitude t‖ * ‖waveVector t‖ / (scale * Ustar) ∧
      ‖amplitude t‖ * ‖waveVector t‖ / (scale * Ustar) ≤
        18 * Real.exp 3 * (Real.sqrt (w.ratio * next))⁻¹
  crossing_coupling_log :
    |Real.log (w.physicalNu waveVector amplitude crossing / w.firstCoupling)| ≤ 2 * w.ratio
  early_gain : ∀ t ∈ Icc t₀ (w.clock 1),
    ‖amplitude t‖ ≤ Real.exp (3 - (Real.sqrt w.ratio)⁻¹) * Ustar

/-- The smallness in (2.5) gives a growing physical wave, positively
rescaled to the requested peak, and its first crossing in the bracket
used in §6 and Theorem 7.1. -/
theorem exists_growingCrossing :
    ∃ N : ℕ, 240 ≤ N ∧ ∀ {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {C₀ : ℕ},
      N ≤ C₀ → ∀ (w : PhysicalAmplification I t₀), 2 ≤ T → 0 < scale → 0 < Ustar →
      MapsTo w.clock (Icc 0 T) I →
      (C₀ : ℝ) * w.ratio ≤ 1 → (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
      0 < next → next ≤ w.ratio / 32 → crossingHorizon w.ratio next ≤ T →
      Nonempty (w.GrowingCrossing T scale Ustar next) := by
  obtain ⟨N, hN, hasCrossing⟩ := AmplificationWindow.exists_growingWave_crossing
  refine ⟨N, hN, ?_⟩
  intro I t₀ T scale Ustar next C₀ hNbound w hT hscale hUstar hcmap hsmallε hsmallδ hnext hnext' hH
  have hC₀ := hN.trans hNbound
  let W := w.toNormalized hT hC₀ hcmap hsmallε hsmallδ
  obtain ⟨k, a, Y, hk₀, ha₀, hY₀, hY, hk, ha, hpath, hν, hcoupling,
      τm, hm, hYm, peak, hpeak, _hpeakRef, hexists, hstrength, hgain⟩ :=
    hasCrossing hNbound W hscale hsmallε hsmallδ hnext hnext' hH
  let H := crossingHorizon w.ratio next
  let ρ (t : ℝ) := W.growingEta k a t / W.growingNu k a t
  have hK₀ (t : ℝ) (ht : t ∈ Icc 0 T) : k t ≠ 0 := (hpath t ht).1
  have hA₀ (t : ℝ) (ht : t ∈ Icc 0 T) : a t ≠ 0 := (hpath t ht).2.1
  have hρ : ContinuousOn ρ (Icc 0 T) :=
    GrowingCoupling.continuousOn_normalized_coupling_ratio (HasDerivWithinAt.continuousOn hk)
      (HasDerivWithinAt.continuousOn ha) W.continuousOn_gradient hK₀ hA₀
      (fun t ht => ((half_pos w.ratio_pos).trans_le (hν t ht)).ne')
  have hm₀ : 0 ≤ τm := (div_nonneg (by norm_num) w.ratio_pos.le).trans hm.1
  have hbracket : Icc τm H ⊆ Icc 0 T := Icc_subset_Icc hm₀ hH
  obtain ⟨u, hu, hue⟩ := hexists
  obtain ⟨τ, hτ, hτCross, hτleast⟩ := exists_least_crossing_Icc (hρ.mono hbracket)
    ⟨u, Ioo_subset_Icc_self hu, hue⟩
  have hτT := hbracket hτ
  have hp₀ : 0 < peak := by
    obtain ⟨t, ht, hnorm⟩ := hpeak.1
    change ‖a t‖ = peak at hnorm
    rw [← hnorm]
    exact norm_pos_iff.mpr (hA₀ t ht)
  obtain ⟨c, hc, hcPeak, hpeakScaled⟩ := exists_positive_vector_peak_rescaling hpeak hp₀ hUstar
  let K (t : ℝ) := k (w.elapsed t)
  let A (t : ℝ) := c • a (w.elapsed t)
  have hKclock (t : ℝ) : K (w.clock t) = k t := by simp only [K, elapsed_clock]
  have hAclock (t : ℝ) : A (w.clock t) = c • a t := by simp only [A, elapsed_clock]
  have hνClock (t : ℝ) (ht : t ∈ Icc 0 T) :
      w.physicalNu K A (w.clock t) / w.firstCoupling = W.growingNu k a t := by
    rw [physicalNu, hKclock, hAclock, NormedSpace.normalize_smul_of_pos hc]
    exact (w.toNormalized_couplings_eq hT hC₀ hcmap hsmallε hsmallδ ht (k t) (a t)).1.symm
  have hηClock (t : ℝ) (ht : t ∈ Icc 0 T) :
      w.physicalEta K A (w.clock t) / w.firstCoupling = W.growingEta k a t := by
    rw [physicalEta, hKclock, hAclock, NormedSpace.normalize_smul_of_pos hc]
    exact (w.toNormalized_couplings_eq hT hC₀ hcmap hsmallε hsmallδ ht (k t) (a t)).2.symm
  have hRatioClock (t : ℝ) (ht : t ∈ Icc 0 T) :
      w.physicalEta K A (w.clock t) / w.physicalNu K A (w.clock t) = ρ t := by
    change _ = W.growingEta k a t / W.growingNu k a t
    rw [← hνClock t ht, ← hηClock t ht]
    have hfirst : w.firstCoupling ≠ 0 := w.first_coupling_positive.ne'
    exact (div_div_div_cancel_right₀ hfirst _ _).symm
  have hPeak : IsGreatest ((fun t => ‖A t‖) '' w.activeSlab T) Ustar := by
    constructor
    · obtain ⟨t, ht, hEq⟩ := hpeakScaled.1
      refine ⟨w.clock t, w.clock_mem_activeSlab ht, ?_⟩
      change ‖A (w.clock t)‖ = Ustar
      rwa [hAclock]
    · rintro _ ⟨t, ht, rfl⟩
      exact hpeakScaled.2 (mem_image_of_mem _ (w.elapsed_mem_activeSlab ht))
  have hBasis₀ : W.basis 0 = w.basis t₀ := by
    funext i
    simp only [W, toNormalized, AmplificationWindow.basis, frame, clock_zero]
  have hGrad (t : ℝ) (ht : t ∈ Icc 0 T) :
      W.gradient t = (1 / w.rate) • w.gradient (t₀ + t / w.rate) :=
    w.toNormalized_gradient_eq hT hC₀ hcmap hsmallε hsmallδ ht
  have hODE := physical_affineWave_derivatives (c := c) (M := w.gradient) w.rate_pos
    (fun t ht => by simpa only [hGrad t ht] using hk t ht)
    (fun t ht => by simpa only [hGrad t ht] using ha t ht)
  refine ⟨{
    waveVector := K
    amplitude := A
    referenceSlope := Y
    seedFactor := c
    referenceTurn := τm
    crossing := w.clock τ
    seedFactor_pos := hc
    slab_in_window := ?_
    initial_waveVector := ?_
    initial_amplitude := ?_
    waveVector_derivative := hODE.1
    amplitude_derivative := hODE.2
    transverse := ?_
    peak := hPeak
    first_coupling_lower := ?_
    reference_initial := hY₀
    reference_derivative := hY
    turning_bounds := hm
    turning_zero := hYm
    crossing_in_bracket := ⟨w.strictMono_clock.monotone hτ.1, w.strictMono_clock.monotone hτ.2⟩
    crossing_in_slab := w.clock_mem_activeSlab hτT
    crossing_after_switch := ?_
    crossing_ratio := (hRatioClock τ hτT).trans hτCross
    crossing_least := ?_
    crossing_strength := ?_
    crossing_coupling_log := ?_
    early_gain := ?_ }⟩
  · intro t ht
    exact w.clock_elapsed t ▸ hcmap (w.elapsed_mem_activeSlab ht)
  · simp only [K, elapsed, sub_self, mul_zero, hk₀, hBasis₀]
  · simp only [A, elapsed, sub_self, mul_zero, ha₀, hBasis₀]
  · intro t ht
    have ht' := w.elapsed_mem_activeSlab ht
    refine ⟨hK₀ _ ht', smul_ne_zero hc.ne' (hA₀ _ ht'), ?_⟩
    change ⟪k (w.elapsed t), c • a (w.elapsed t)⟫_ℝ = 0
    rw [real_inner_smul_right, (hpath _ ht').2.2.1, mul_zero]
  · intro t ht
    have ht' := w.elapsed_mem_activeSlab ht
    have h := hν (w.elapsed t) ht'
    rw [← hνClock _ ht', clock_elapsed] at h
    have h' := (le_div_iff₀ w.first_coupling_positive).mp h
    change w.ratio / 2 * w.firstCoupling ≤ w.physicalNu K A t at h'
    calc
      _ = w.ratio / 2 * w.firstCoupling := by ring
      _ ≤ _ := h'
  · apply w.strictMono_clock
    have h₁ : 1 < 2 / w.ratio :=
      (lt_div_iff₀ w.ratio_pos).2 (by linarith only [W.ratioSmall])
    exact h₁.trans_le (hm.1.trans hτ.1)
  · intro t ht hcross
    have ht' := w.elapsed_mem_Icc ht
    have heq := hRatioClock (w.elapsed t) (hbracket ht')
    rw [clock_elapsed, hcross] at heq
    simpa only [clock_elapsed] using w.strictMono_clock.monotone (hτleast _ ht' heq.symm)
  · intro t ht hcross
    have ht' := w.elapsed_mem_Icc ht
    have heq := hRatioClock (w.elapsed t) (hbracket ht')
    rw [clock_elapsed, hcross] at heq
    have hb := hstrength (w.elapsed t) ht' heq.symm
    have hval : ‖A t‖ * ‖K t‖ / (scale * Ustar) =
        ‖a (w.elapsed t)‖ * ‖k (w.elapsed t)‖ / (scale * peak) := by
      calc
        _ = ‖A (w.clock (w.elapsed t))‖ * ‖K (w.clock (w.elapsed t))‖ / (scale * Ustar) :=
          by rw [clock_elapsed]
        _ = _ := by rw [hKclock, hAclock, peak_relative_strength_smul _ _ hc hcPeak]
    rw [hval]
    exact hb
  · have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
      exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    have hlate := (div_le_div_of_nonneg_right hsqrt2 w.ratio_pos.le).trans (hm.1.trans hτ.1)
    rw [hνClock τ hτT]
    exact abs_log_le_of_close_one W.ratioSmall (hcoupling τ hτT hlate).1
  · intro t ht
    have ht' : w.elapsed t ∈ Icc 0 1 := w.elapsed_mem_Icc (a := 0)
      (by simpa only [clock_zero] using ht)
    exact (peak_relative_gain_smul_iff _ hc hcPeak).2 (hgain _ ht')


/-- The first crossing is after the first unit of normalized time and
within the physical time allowed by the crossing horizon. -/
theorem GrowingCrossing.delay_bounds {T scale Ustar next : ℝ}
    (d : w.GrowingCrossing T scale Ustar next) :
    1 / w.rate < d.crossing - t₀ ∧
      d.crossing - t₀ ≤ crossingHorizon w.ratio next / w.rate := by
  constructor
  · have h := d.crossing_after_switch
    unfold clock at h
    linarith only [h]
  · have h := d.crossing_in_bracket.2
    unfold clock at h
    linarith only [h]

/-- At the induction peak `scale⁻³ᐟ⁴`, the strength denominator is
`scale¹ᐟ⁴`, as in the late central bounds of Theorem 7.1. -/
theorem GrowingCrossing.strength_at_induction_peak {T scale next : ℝ} (hscale : 0 < scale)
    (d : w.GrowingCrossing T scale (scale ^ (-(3 / 4 : ℝ))) next) :
    (Real.exp (-1) / 4) * (Real.sqrt (w.ratio * next))⁻¹ ≤
      ‖d.amplitude d.crossing‖ * ‖d.waveVector d.crossing‖ / scale ^ (1 / 4 : ℝ) ∧
    ‖d.amplitude d.crossing‖ * ‖d.waveVector d.crossing‖ / scale ^ (1 / 4 : ℝ) ≤
      18 * Real.exp 3 * (Real.sqrt (w.ratio * next))⁻¹ := by
  have hden : scale * scale ^ (-(3 / 4 : ℝ)) = scale ^ (1 / 4 : ℝ) := by
    calc
      _ = scale ^ (1 : ℝ) * scale ^ (-(3 / 4 : ℝ)) := by rw [Real.rpow_one]
      _ = scale ^ (1 + -(3 / 4 : ℝ)) := (Real.rpow_add hscale _ _).symm
      _ = _ := by norm_num
  simpa only [hden] using d.crossing_strength _ d.crossing_in_bracket d.crossing_ratio


end

end TorusEuler.MovingWaveVector.PhysicalAmplification
