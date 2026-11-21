import TorusEuler.Paper.Proofs.S678a.Library.StageParent
import TorusEuler.PhysicalAmplificationCrossing
import TorusEuler.AffineExistence
import TorusEuler.Paper.S2.Statements
import TorusEuler.Paper.Proofs.S2a.Library.Angle

/-! # The growing crossing of a later wave from Lemmas 2.7 and Proposition 2.8 (package S678a)

Copy of `PhysicalAmplification.exists_growingCrossing` (PhysicalAmplificationCrossing.lean:292)
whose comparison input (the normalized window of Lemma 2.4, the Riccati solution of Lemma 2.5 and
`exists_growingWave_crossing`, content of 2.8) is replaced by the cited statements
`h2_7` (`Statement.lemma_2_7`, (2.19)) and `h2_8` (`Statement.proposition_2_8`, (2.23), (2.24)),
applied to the amplitude vector of Lemma 2.6 that solves the affine-wave equations on the window.
This is the construction of the later wave in sections/08b_induction.tex:60-93, with the crossing
of sections/03_amplification.tex:894 (Proposition 2.8).

The reference solution `Y` of (2.12) and its turning time `ε τ_m ∈ [2, 3]` (fields `referenceSlope`,
`reference_*`, `turning_*` of the library `GrowingCrossing`) come from `h2_5` (`Statement.lemma_2_5`, decision D23:
the statements 2.6-2.8 are about the reference solution of Lemma 2.5), identified with the turning
time of `h2_8` by its characterization (`Y τ = 0 ↔ τ = τ_m` for every solution of (2.12)). -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler TorusEuler.MovingWaveVector TorusEuler.MovingWaveVector.PhysicalAmplification
open NormedSpace (normalize)
open TorusEuler.AmplificationCrossing (crossingHorizon exists_least_crossing_Icc)
open TorusEuler.ReferenceAmplitude (exists_positive_vector_peak_rescaling
  peak_relative_strength_smul peak_relative_gain_smul_iff)

noncomputable section

section Helpers

variable {I : Set ℝ} {t₀ : ℝ} (w : PhysicalAmplification I t₀)

/-- If `t` lies between the clock values of `a` and `b`, the elapsed time at `t` lies in `[a,b]` (primed glue copy). -/
theorem elapsed_mem_Icc' {a b t : ℝ} (ht : t ∈ Icc (w.clock a) (w.clock b)) :
    w.elapsed t ∈ Icc a b := by
  have ha := w.strictMono_elapsed.monotone ht.1
  have hb := w.strictMono_elapsed.monotone ht.2
  exact ⟨by simpa only [elapsed_clock] using ha, by simpa only [elapsed_clock] using hb⟩

/-- The elapsed time of a point of the active slab lies in `[0,T]` (primed glue copy). -/
theorem elapsed_mem_activeSlab' {T t : ℝ} (ht : t ∈ w.activeSlab T) :
    w.elapsed t ∈ Icc 0 T :=
  elapsed_mem_Icc' w (a := 0) (by simpa only [clock_zero, activeSlab] using ht)

/-- The clock of a time in `[0,T]` lies in the active slab (primed glue copy). -/
theorem clock_mem_activeSlab' {T τ : ℝ} (ht : τ ∈ Icc 0 T) : w.clock τ ∈ w.activeSlab T :=
  ⟨by simpa only [clock_zero] using w.strictMono_clock.monotone ht.1,
    w.strictMono_clock.monotone ht.2⟩

end Helpers

/-- If `|u-1| ≤ ε ≤ 1/2` then `|log u| ≤ 2ε` (elementary, primed glue copy). -/
theorem abs_log_le_of_close_one' {u ε : ℝ} (hε : ε ≤ 1 / 2) (h : |u - 1| ≤ ε) :
    |Real.log u| ≤ 2 * ε := by
  have hu : 1 / 2 ≤ u := by linarith [(abs_le.mp h).1]
  have hlog := ReferenceAmplitude.log_amplitude_ratio_le
    (g := 1) (h := u) (h₀ := 1) (F := 0) (φ := 0) (m := 1 / 2) (δ := ε)
    (by norm_num) (by norm_num) hu (by norm_num) h (by norm_num) (by norm_num)
  convert hlog using 1
  · simp
  · ring

/-- Normalization of a continuous nonvanishing vector function is continuous (elementary, primed glue copy). -/
theorem continuousOn_normalize' {J : Set ℝ} {v : ℝ → Space} (hv : ContinuousOn v J)
    (hv₀ : ∀ t ∈ J, v t ≠ 0) : ContinuousOn (fun t => normalize (v t)) J := by
  unfold NormedSpace.normalize
  exact (hv.norm.inv₀ (fun t ht => norm_ne_zero_iff.2 (hv₀ t ht))).smul hv

/-- The cross product of two continuous vector functions is continuous (elementary, primed glue copy). -/
theorem continuousOn_cross3' {J : Set ℝ} {u v : ℝ → Space}
    (hu : ContinuousOn u J) (hv : ContinuousOn v J) :
    ContinuousOn (fun t => cross3 (u t) (v t)) J := by
  unfold cross3
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
    (continuousOn_pi.mpr ?_)
  have hu' (i : Fin 3) : ContinuousOn (fun t => (u t).ofLp i) J :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp_continuousOn hu
  have hv' (i : Fin 3) : ContinuousOn (fun t => (v t).ofLp i) J :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp_continuousOn hv
  intro i
  fin_cases i
  · exact ((hu' 1).mul (hv' 2)).sub ((hu' 2).mul (hv' 1))
  · exact ((hu' 2).mul (hv' 0)).sub ((hu' 0).mul (hv' 2))
  · exact ((hu' 0).mul (hv' 1)).sub ((hu' 1).mul (hv' 0))

/-- The gradient of a physical window is continuous on a compact interval window. -/
theorem continuousOn_gradient_Icc {t₀ finish : ℝ} (w : PhysicalAmplification (Icc t₀ finish) t₀) :
    ContinuousOn w.gradient (Icc t₀ finish) := by
  have hkc : ContinuousOn w.kp (Icc t₀ finish) := HasDerivWithinAt.continuousOn w.preceding_vector
  have hac : ContinuousOn w.ap (Icc t₀ finish) := HasDerivWithinAt.continuousOn w.preceding_amplitude
  have hR : ContinuousOn (fun t => InnerProductSpace.rankOne ℝ (w.ap t) (w.kp t))
      (Icc t₀ finish) := by
    let L : Space →L[ℝ] Space →L[ℝ] (Space →L[ℝ] Space) := InnerProductSpace.rankOne ℝ
    exact (L.continuous.comp_continuousOn hac).clm_apply hkc
  exact (w.older_continuous.add hR).add w.error_continuous

/-- Physical couplings are unchanged by a positive rescaling of the amplitude. -/
theorem physicalNu_smul {I : Set ℝ} {t₀ : ℝ} (w : PhysicalAmplification I t₀) (k a : ℝ → Space)
    {c : ℝ} (hc : 0 < c) (t : ℝ) :
    w.physicalNu k (fun s => c • a s) t = w.physicalNu k a t := by
  simp only [physicalNu, NormedSpace.normalize_smul_of_pos hc]

/-- The physical amplitude direction does not change when the amplitude is multiplied by a positive scalar (elementary glue). -/
theorem physicalEta_smul {I : Set ℝ} {t₀ : ℝ} (w : PhysicalAmplification I t₀) (k a : ℝ → Space)
    {c : ℝ} (hc : 0 < c) (t : ℝ) :
    w.physicalEta k (fun s => c • a s) t = w.physicalEta k a t := by
  simp only [physicalEta, NormedSpace.normalize_smul_of_pos hc]

/-- Copy of `affineWave_exists_Icc` (AffineExistence.lean:13) with the propagation of the nonzero
perpendicular data proved in place from the linear-ODE lemmas, for an arbitrary continuous `D`. This is
glue, not the content of Lemma 2.1: Lemma 2.1 (`h2_1`) assumes that `D' + D²` is symmetric, which
fails for `D = ∇U_{j-1}(t,0)` of an approximate parent, whereas `(k·a)' = 0` and the nonvanishing hold
for every continuous `D`; the TeX (sections/08b_induction.tex:20-31) uses this outside the hypotheses of
Lemma 2.1 and does not cite it. Row 2.1 therefore stays `notation_only` for 7.1. -/
theorem affineWave_exists_Icc' {D : ℝ → Space →L[ℝ] Space} {l r t₀ : ℝ} {k₀ a₀ : Space}
    (ht₀ : t₀ ∈ Icc l r) (hD : ContinuousOn D (Icc l r))
    (hk₀ : k₀ ≠ 0) (ha₀ : a₀ ≠ 0) (hperp₀ : ⟪k₀, a₀⟫_ℝ = 0) :
    ∃ k a : ℝ → Space, k t₀ = k₀ ∧ a t₀ = a₀ ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt k (-((D t).adjoint (k t))) (Icc l r) t) ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt a
        (-((D t) (a t)) + (2 * ⟪k t, D t (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) (Icc l r) t) ∧
      ∀ t ∈ Icc l r, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0 := by
  have hDadj : ContinuousOn (fun t => -(D t).adjoint) (Icc l r) :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hD).neg
  obtain ⟨k, hk_init, hk_linear⟩ := linearODE_exists_Icc_of_mem ht₀ hDadj k₀
  have hk_ne₀ : k t₀ ≠ 0 := by rwa [hk_init]
  have hk_ne := linearODE_ne_zero_of_mem ordConnected_Icc ht₀ hDadj hk_linear hk_ne₀
  have hk_cont : ContinuousOn k (Icc l r) := fun t ht => (hk_linear t ht).continuousWithinAt
  have hA := continuousOn_affineWaveAmplitudeOperator hD hk_cont hk_ne
  obtain ⟨a, ha_init, ha_linear⟩ := linearODE_exists_Icc_of_mem ht₀ hA a₀
  have hk (t : ℝ) (ht : t ∈ Icc l r) :
      HasDerivWithinAt k (-((D t).adjoint (k t))) (Icc l r) t := by
    simpa only [neg_apply] using hk_linear t ht
  have ha (t : ℝ) (ht : t ∈ Icc l r) :
      HasDerivWithinAt a
        (-((D t) (a t)) + (2 * ⟪k t, D t (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) (Icc l r) t := by
    simpa only [affineWaveAmplitudeOperator_apply] using ha_linear t ht
  have ha₀' : a t₀ ≠ 0 := by rwa [ha_init]
  have ha_ne : ∀ t ∈ Icc l r, a t ≠ 0 :=
    linearODE_ne_zero_of_mem ordConnected_Icc ht₀ hA ha_linear ha₀'
  have hperp : EqOn (fun t => ⟪k t, a t⟫_ℝ) (fun _ => (0 : ℝ)) (Icc l r) :=
    linearODE_unique_of_mem (A := fun _ => 0) ordConnected_Icc ht₀ continuousOn_const
      (fun t ht => by simpa only [zero_apply] using
        hasDerivWithinAt_affineWavePairing_zero (hk_ne t ht) (hk t ht) (ha t ht))
      (fun t _ => by simpa only [zero_apply] using
        hasDerivWithinAt_const t (Icc l r) (0 : ℝ)) (by rwa [hk_init, ha_init])
  exact ⟨k, a, hk_init, ha_init, hk, ha, fun t ht => ⟨hk_ne t ht, ha_ne t ht, hperp ht⟩⟩

/-- **The later wave from Lemma 2.7 and Proposition 2.8** (sections/08b_induction.tex:60-93;
sections/03_amplification.tex:718, :894). For a physical window `[t₀, finish]` with
`finish = w.clock T` satisfying (2.7), the amplitude vector of Lemma 2.6 started at the
transverse seed `(-S⁻¹)E₁ + E₂` (solution of (2.1) on the window), rescaled to the peak `Ustar`, has a
least crossing `η₊/ν₊ = next` in the bracket `[τ_m, 2(ε ε₊)^{-1/2}]`, with (2.23), (2.19) and (2.24).
`h2_5` gives the reference solution and its turning time (sections/03_amplification.tex, Lemma 2.5); `h2_7` gives `ν₊ ≥ εν/2` and (2.19); `h2_8` gives the turning time, the crossing, the peak,
(2.23) and (2.24). -/
theorem exists_growingCrossingV (h2_5 : Statement.lemma_2_5) (h2_7 : Statement.lemma_2_7) (h2_8 : Statement.proposition_2_8) :
    ∃ N : ℕ, 240 ≤ N ∧ ∀ {t₀ finish T scale Ustar next : ℝ} {C₀ : ℕ}, N ≤ C₀ →
      ∀ (w : PhysicalAmplification (Icc t₀ finish) t₀), w.clock T = finish → 2 ≤ T → 0 < scale →
      0 < Ustar → (C₀ : ℝ) * w.ratio ≤ 1 → (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio →
      0 < next → next ≤ w.ratio / 32 → crossingHorizon w.ratio next ≤ T →
      Nonempty (w.GrowingCrossing T scale Ustar next) := by
  obtain ⟨N7, h7⟩ := h2_7
  obtain ⟨N8, h8⟩ := h2_8
  refine ⟨max (max N7 N8) 240, le_max_right _ _, ?_⟩
  intro t₀ finish T scale Ustar next C₀ hC w hfin hT hscale hUstar hsmallε hsmallδ hnext hnext' hH
  have hN7 : N7 ≤ C₀ := (le_max_left _ _).trans ((le_max_left _ _).trans hC)
  have hN8 : N8 ≤ C₀ := (le_max_right _ _).trans ((le_max_left _ _).trans hC)
  have h240 : 240 ≤ C₀ := (le_max_right _ _).trans hC
  have hslab : w.activeSlab T = Icc t₀ finish := by unfold activeSlab; rw [hfin]
  have hmap : MapsTo w.clock (Icc 0 T) (Icc t₀ finish) := fun τ hτ => by
    have := clock_mem_activeSlab' w hτ
    rwa [hslab] at this
  have hMc := continuousOn_gradient_Icc w
  -- the seed at the activation time
  have h0 : t₀ ∈ Icc t₀ finish := w.activation
  have hp₀ := w.preceding_data t₀ h0
  have he : Orthonormal ℝ (w.basis t₀) := orthonormal_movingFrame hp₀.1 hp₀.2.1 hp₀.2.2
  have hinner := orthonormal_iff_ite.mp he
  have hk₀ : w.basis t₀ 2 ≠ 0 := by
    have h := he.norm_eq_one 2
    intro hzero
    rw [hzero, norm_zero] at h
    norm_num at h
  have ha₀ : (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1 ≠ 0 := by
    have h : ⟪w.basis t₀ 1, (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1⟫_ℝ = 1 := by
      simp [inner_add_right, real_inner_smul_right, hinner, he.norm_eq_one]
    intro hzero
    rw [hzero, inner_zero_right] at h
    norm_num at h
  have hperp : ⟪scale • w.basis t₀ 2, (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1⟫_ℝ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, inner_add_right, hinner]
  obtain ⟨k, a, hk0, ha0, hk', ha', hprop⟩ :=
    affineWave_exists_Icc' h0 hMc (smul_ne_zero hscale.ne' hk₀) ha₀ hperp
  have hNW : NewWaveVector w scale k := ⟨hscale, hk0, hk'⟩
  have hAV : AmplitudeVector w k a :=
    ⟨fun t ht => by simpa only [affineWavePressureCoeff] using ha' t ht,
      fun t ht => by rw [real_inner_comm]; exact (hprop t ht).2.2⟩
  have hFS : FiniteSmallness w T C₀ := ⟨hsmallε, hsmallδ⟩
  obtain ⟨hν₁, hν₂⟩ := h7 hN7 w hT hmap hFS hNW hAV ha0
  have hH' : 2 / Real.sqrt (w.ratio * next) ≤ T := hH
  obtain ⟨τm, hchar, hτm, ⟨τ₁, hτ₁, hτ₁e⟩, peak, hpeak, hstr, hgain⟩ :=
    h8 hN8 w hT hmap hFS hNW hAV ha0 hnext hnext' hH'
  have hεle : w.ratio ≤ 1 / 240 := by
    have h : (240 : ℝ) ≤ C₀ := by exact_mod_cast h240
    have h1 : (240 : ℝ) * w.ratio ≤ 1 := (mul_le_mul_of_nonneg_right h w.ratio_pos.le).trans hsmallε
    linarith
  -- bracket and continuity of the coupling ratio
  set H := crossingHorizon w.ratio next with hHdef
  have hτm₀ : 0 ≤ τm := (div_nonneg (by norm_num) w.ratio_pos.le).trans hτm
  have hHle : H = 2 / Real.sqrt (w.ratio * next) := rfl
  have hbr : Icc (w.clock τm) (w.clock H) ⊆ Icc t₀ finish := by
    intro t ht
    refine ⟨?_, ?_⟩
    · have := w.strictMono_clock.monotone hτm₀
      rw [clock_zero] at this
      exact this.trans ht.1
    · exact ht.2.trans ((w.strictMono_clock.monotone hH).trans_eq hfin)
  have hkc := HasDerivWithinAt.continuousOn hk'
  have hac := HasDerivWithinAt.continuousOn ha'
  have hk₁ : ∀ t ∈ Icc t₀ finish, k t ≠ 0 := fun t ht => (hprop t ht).1
  have ha₁ : ∀ t ∈ Icc t₀ finish, a t ≠ 0 := fun t ht => (hprop t ht).2.1
  have hkn := continuousOn_normalize' hkc hk₁
  have han := continuousOn_normalize' hac ha₁
  have hNuC : ContinuousOn (fun t => w.physicalNu k a t) (Icc t₀ finish) :=
    hkn.inner (hMc.clm_apply han)
  have hEtaC : ContinuousOn (fun t => w.physicalEta k a t) (Icc t₀ finish) :=
    (continuousOn_cross3' hkn han).inner (hMc.clm_apply han)
  have hνpos (t : ℝ) (ht : t ∈ Icc t₀ finish) : w.firstCoupling * w.ratio / 2 ≤ w.physicalNu k a t := by
    have hm := elapsed_mem_Icc' w (a := 0) (b := T) (t := t)
      (by rw [clock_zero]; exact ⟨ht.1, by rw [hfin]; exact ht.2⟩)
    have h := hν₁ _ hm
    simp only [clock_elapsed] at h
    linarith [h, mul_comm w.firstCoupling w.ratio]
  have hfc := w.first_coupling_positive
  have hνne (t : ℝ) (ht : t ∈ Icc t₀ finish) : w.physicalNu k a t ≠ 0 :=
    (lt_of_lt_of_le (by positivity [w.ratio_pos]) (hνpos t ht)).ne'
  have hρ : ContinuousOn (fun t => w.physicalEta k a t / w.physicalNu k a t) (Icc t₀ finish) :=
    hEtaC.div hNuC hνne
  obtain ⟨t', ht', ht'e, ht'l⟩ := exists_least_crossing_Icc (a := w.clock τm) (b := w.clock H)
    (hρ.mono hbr) ⟨w.clock τ₁, ⟨w.strictMono_clock.monotone hτ₁.1, w.strictMono_clock.monotone hτ₁.2⟩,
      by simpa only using hτ₁e⟩
  have hρclock (t : ℝ) (ht : t ∈ Icc (w.clock τm) (w.clock H)) :
      w.physicalEta k a t / w.physicalNu k a t = next → _ := fun h => h
  -- peak rescaling
  have hpeakSlab : IsGreatest ((fun t => ‖a t‖) '' w.activeSlab T) peak := by
    constructor
    · obtain ⟨τ, hτ, hEq⟩ := hpeak.1
      exact ⟨w.clock τ, clock_mem_activeSlab' w hτ, hEq⟩
    · rintro _ ⟨t, ht, rfl⟩
      have := hpeak.2 (mem_image_of_mem (fun τ => ‖a (w.clock τ)‖) (elapsed_mem_activeSlab' w ht))
      simpa only [clock_elapsed] using this
  have hp₀ : 0 < peak := by
    obtain ⟨t, ht, hEq⟩ := hpeakSlab.1
    rw [← hEq]
    exact norm_pos_iff.mpr (ha₁ t (by rwa [hslab] at ht))
  obtain ⟨c, hc, hcPeak, hpeakScaled⟩ := exists_positive_vector_peak_rescaling hpeakSlab hp₀ hUstar
  have hε2 : w.ratio ≤ 1 / 2 := hεle.trans (by norm_num)
  obtain ⟨⟨Y, hYs⟩, hrest⟩ := h2_5 w.ratio_pos (hε2.trans (by norm_num))
  obtain ⟨-, -, _e, -, -, -, τm', hzero, hτ2, hτ3, -⟩ := hrest Y hYs
  obtain ⟨hY0, hYd⟩ := Lib.S2a.referenceSlope_iff.1 hYs
  have hτm'0 : 0 ≤ τm' := by
    by_contra h
    rw [not_le] at h
    have := mul_neg_of_pos_of_neg w.ratio_pos h
    linarith
  have hYz' : Y τm' = 0 := (hzero τm' hτm'0).2 rfl
  have hτeq : τm' = τm := (hchar Y hYs τm' hτm'0).1 hYz'
  have hτm3 : τm ≤ 3 / w.ratio := hτeq ▸ (le_div_iff₀ w.ratio_pos).2 (by linarith [mul_comm τm' w.ratio])
  have hYz : Y τm = 0 := hτeq ▸ hYz'
  have h1τm : 1 < τm := by
    have : (1 : ℝ) < 2 / w.ratio := (lt_div_iff₀ w.ratio_pos).2 (by linarith)
    exact this.trans_le hτm
  have hamp_nu := physicalNu_smul w k a hc
  have hamp_eta := physicalEta_smul w k a hc
  refine ⟨{
    waveVector := k
    amplitude := fun t => c • a t
    seedFactor := c
    referenceTurn := τm
    crossing := t'
    seedFactor_pos := hc
    slab_in_window := hslab.subset
    initial_waveVector := by rw [hk0]
    initial_amplitude := by simp only [ha0]
    waveVector_derivative := fun t ht => by rw [hslab] at ht ⊢; exact hk' t ht
    amplitude_derivative := fun t ht => ?_
    transverse := fun t ht => ?_
    peak := hpeakScaled
    first_coupling_lower := fun t ht => ?_
    turning_bounds := ⟨hτm, hτm3⟩
    referenceSlope := Y
    reference_initial := hY0
    reference_derivative := hYd
    turning_zero := hYz
    crossing_in_bracket := ht'
    crossing_in_slab := by rw [hslab]; exact hbr ht'
    crossing_after_switch := ?_
    crossing_ratio := ?_
    crossing_least := ?_
    crossing_strength := ?_
    crossing_coupling_log := ?_
    early_gain := ?_ }⟩
  · rw [hslab] at ht ⊢
    have h := (ha' t ht).const_smul c
    refine h.congr_deriv ?_
    simp only [affineWaveAmplitudeOperator_apply, map_smul, smul_add, smul_neg, smul_smul]
  · rw [hslab] at ht
    exact ⟨(hprop t ht).1, smul_ne_zero hc.ne' (hprop t ht).2.1, by
      rw [real_inner_smul_right, (hprop t ht).2.2, mul_zero]⟩
  · rw [hslab] at ht
    have := hνpos t ht
    simp only [hamp_nu]
    exact this
  · exact w.strictMono_clock h1τm |>.trans_le ht'.1
  · simp only [hamp_nu, hamp_eta]; exact ht'e
  · intro t ht he'
    simp only [hamp_nu, hamp_eta] at he'
    exact ht'l t ht he'
  · intro t ht he'
    simp only [hamp_nu, hamp_eta] at he'
    have hte := elapsed_mem_Icc' w ht
    have h := hstr _ hte (by simpa only [clock_elapsed] using he')
    simp only [clock_elapsed] at h
    simp only [peak_relative_strength_smul _ _ hc hcPeak]
    exact h
  · have hτ't := elapsed_mem_Icc' w ht'
    have hlate : Real.sqrt 2 / w.ratio ≤ w.elapsed t' := by
      have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
      exact (div_le_div_of_nonneg_right hsqrt2 w.ratio_pos.le).trans (hτm.trans hτ't.1)
    have h := (hν₂ _ ⟨hτ't.1.trans' hτm₀, hτ't.2.trans hH⟩ hlate).1
    simp only [clock_elapsed] at h
    simp only [hamp_nu]
    exact abs_log_le_of_close_one' hε2 h
  · intro t ht
    have ht' : w.elapsed t ∈ Icc 0 1 := elapsed_mem_Icc' w (a := 0) (b := 1)
      (by simpa only [clock_zero] using ht)
    have h := hgain _ ht'
    simp only [clock_elapsed] at h
    exact (peak_relative_gain_smul_iff _ hc hcPeak).2 h

end

end TorusEuler.Paper.Lib.S678a
