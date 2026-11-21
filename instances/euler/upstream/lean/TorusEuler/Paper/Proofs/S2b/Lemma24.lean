import TorusEuler.Paper.Proofs.S2b.Library.Lemma24Copies
import TorusEuler.Paper.Proofs.S2b.Library.Normalized

/-! # Conditional proof of Lemma 2.4

`TorusEuler.Paper.Proof.lemma_2_4_of`, following the proof of Lemma 2.4
(`cc:uf:exact:lem:additive`) in
`paper/craik_criminale_rewrite/sections/03_amplification.tex:288-417`.
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper

open MovingWaveVector MovingAmplitude ReferenceRiccati Lib.S2b

/-- Proof of **Lemma 2.4** (`cc:uf:exact:lem:additive`) following
`sections/03_amplification.tex:288-417`, in normalized time `τ` (`t = t₀ + τ/r`).

* Normalization (`:289-301`): the equations (2.1) of the preceding wave, of the wave
  vector and of the amplitude vectors in `τ` have their coefficients divided by `r`
  (`normalized_affineWave_derivatives`, `Lib.S2b.rescale_waveVector`,
  `Lib.S2b.rescale_amplitude`); the bounds `|b_ij| ≤ δ`, `|2Sb₁₂ - 1| ≤ δ`,
  `|2Sb₃₂ - ε| ≤ δ` (`:296-300`), `|E_c|/r ≤ δ/S` follow from (2.6), and (2.8) holds
  (`Lib.S2b.normalized_facts`).
* `h2_2` (Lemma 2.2) is applied to the preceding wave in normalized time
  (`J = [0, T]`, `B/r`): it gives the orthonormality of the frame and (2.2). The
  orthonormality (`he`) is used at `t₀` in `Lib.S2b.normalized_facts` (the bounds on the
  quantities (2.9), `:296-300`), on `[0, T]` in the two copies below, in the bound on the
  error operator (`errorOperator_le_on_normalized_window`, `:384-416`), in
  `|k|² = λ²m` (`wave_norm_sq_eq`) for the second bound of (2.10) (`:354-357`), and in the
  amplitude system (`normalized_amplitude_perturbed`, `:359-383`). Its last
  equation `(log σ_p)' = b₃₃` gives `sup|σ_p/σ - 1| ≤ 2Tδ` (`:302-309`,
  `Lib.S2b.strengthRatio_bound_of_log`), the last conclusion of the statement (ledger
  export of row 2.4). Its first three equations give the equations of `ζ` (`:311-333`,
  `normalized_waveVector_derivatives` inside `Lib.S2b.waveVector_polynomial_error_of_frame`,
  a copy of the library carrier `moving_waveVector_polynomial_error` with the
  orthonormality and (2.2) as hypotheses), whose comparison with `ζ₀` (`:335-357`) gives
  (2.10) with the explicit bound `|ζ₁ - tan φ| + |ζ₂ + ετ| + |ζ₃ - 1| ≤ 120δT⁶ ≤ 1/2`, and
  they give the amplitude equations (`:359-383`, `normalized_amplitude_perturbed`, from
  `E₁'`, `E₂'`).
* (2.11) from (2.10) (`waveVector_coordinate_bounds`, `Lib.S2b.norm_zeta_le`); the second
  bound of (2.10) from `|k|² = λ²m` (`wave_norm_sq_eq`), `cos²φ = (1 + tan²φ)⁻¹` and
  `Lib.S2b.normFactor_cos_bound` (`:354-357`).
* The error `ℰ = PRP` (`P = diag(-1, 1)`) where `R` is the library error operator
  `errorOperator` of the raw system for `(U, V) = (-α₁, α₂)`; its bound (`:384-407`) is
  `errorOperator_le_on_normalized_window` with the coefficient bounds above and (2.10),
  including the contribution of `E_c` (`:409-416`); `ℰ` depends only on `k`, so it is the
  same for all amplitude vectors; its continuity (ledger export of row 2.4) is
  `continuousOn_errorOperator`.

Constants: `C = max(C_R, 242)`, `p = max(n_R, 8)` with `(C_R, n_R)` from
`errorOperator_le_on_normalized_window`. Equations: (2.1)-(2.4), (2.6)-(2.11). -/
theorem Proof.lemma_2_4_of (h2_2 : Statement.lemma_2_2) : Statement.lemma_2_4 := by
  obtain ⟨C', hC', n, hbound⟩ := errorOperator_le_on_normalized_window
  refine ⟨max C' 242, max n 8, 240 + max n 8 + Nat.ceil (2 * max C' 242), ?_⟩
  intro C₀ hN I t₀ T lam w k hT hclock hsmall hk ε δ ζ
  set C := max C' 242 with hCdef
  set p := max n 8 with hpdef
  have h240 : 240 ≤ C₀ := by omega
  have hpC : p ≤ C₀ := by omega
  have h2C : 2 * C ≤ (C₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (2 * C) ≤ C₀ by omega))
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hC242 : (242 : ℝ) ≤ C := le_max_right _ _
  have hCC' : C' ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  have hTp8 : T ^ 8 ≤ T ^ p := pow_le_pow_right₀ hT1 (le_max_right _ _)
  have hTpn : T ^ n ≤ T ^ p := pow_le_pow_right₀ hT1 (le_max_left _ _)
  have hT68 : T ^ 6 ≤ T ^ 8 := pow_le_pow_right₀ hT1 (by norm_num)
  have hT28 : T ^ 2 ≤ T ^ 8 := pow_le_pow_right₀ hT1 (by norm_num)
  -- The preceding wave in normalized time.
  let kp' := w.kp ∘ w.clock
  let ap' := w.ap ∘ w.clock
  let B' := fun τ => (1 / w.rate) • w.B (w.clock τ)
  let E' := fun τ => (1 / w.rate) • w.E (w.clock τ)
  let K := k ∘ w.clock
  let e := frame kp' ap'
  have hp' : ∀ τ ∈ Icc 0 T, kp' τ ≠ 0 ∧ ap' τ ≠ 0 ∧ ⟪kp' τ, ap' τ⟫_ℝ = 0 :=
    fun τ hτ => w.preceding_data _ (hclock hτ)
  have hpre (τ : ℝ) (hτ : τ ∈ Icc 0 T) :=
    normalized_affineWave_derivatives hclock (w.preceding_vector _ (hclock hτ))
      (by simpa only [affineWaveAmplitudeOperator_apply, PhysicalAmplification.clock] using
        w.preceding_amplitude _ (hclock hτ))
  have hkp' (τ : ℝ) (hτ : τ ∈ Icc 0 T) :
      HasDerivWithinAt kp' (-((B' τ).adjoint (kp' τ))) (Icc 0 T) τ := (hpre τ hτ).1
  have hap' (τ : ℝ) (hτ : τ ∈ Icc 0 T) : HasDerivWithinAt ap'
      (-(B' τ (ap' τ)) + affineWavePressureCoeff (B' τ) (kp' τ) (ap' τ) • kp' τ) (Icc 0 T) τ :=
    (hpre τ hτ).2
  have htrace' : ∀ τ ∈ Icc 0 T, LinearMap.trace ℝ Vec3 (B' τ).toLinearMap = 0 :=
    fun τ hτ => normalized_trace_zero (w.trace_zero _ (hclock hτ))
  -- Lemma 2.2: orthonormality and the frame equations (2.2) in normalized time.
  have hF := h2_2 htrace' ⟨hkp', hap'⟩ hp'
  have he (τ : ℝ) (hτ : τ ∈ Icc 0 T) : Orthonormal ℝ (e τ) := (hF τ hτ).1
  -- The normalized coefficient bounds from (2.6)-(2.8), with the orthonormality of the
  -- frame at `t₀ = t₀ + 0/r` from Lemma 2.2.
  have he₀ : Orthonormal ℝ (w.basis t₀) := by
    have h := he 0 ⟨le_rfl, by linarith⟩
    change Orthonormal ℝ (w.basis (w.clock 0)) at h
    rwa [PhysicalAmplification.clock_zero] at h
  obtain ⟨hεpos, hεhalf, hδ, hS0, hS1, hSinv, hS2inv, h240', hTδ, -, hcoef⟩ :=
    normalized_facts w he₀ hT h240 hsmall
  have hε1 : w.ratio ≤ 1 := by linarith
  have hE₁ (τ : ℝ) (hτ : τ ∈ Icc 0 T) := (hF τ hτ).2.1
  have hE₂ (τ : ℝ) (hτ : τ ∈ Icc 0 T) := (hF τ hτ).2.2.1
  have hE₃ (τ : ℝ) (hτ : τ ∈ Icc 0 T) := (hF τ hτ).2.2.2.1
  have hlog (τ : ℝ) (hτ : τ ∈ Icc 0 T) := (hF τ hτ).2.2.2.2
  -- `|σ_p/σ - 1| ≤ 2Tδ` from `(log σ_p)' = b₃₃`.
  have hσ := strengthRatio_bound_of_log hTδ hp' he hlog (fun τ hτ => (hcoef _ (hclock hτ)).1)
  -- The wave vector: (2.10) with the explicit bound `120δT⁶`.
  have hk' (τ : ℝ) (hτ : τ ∈ Icc 0 T) :
      HasDerivWithinAt K (-((strain (e τ) (B' τ) (E' τ) w.shear
        (strengthRatio kp' ap' τ)).adjoint (K τ))) (Icc 0 T) τ :=
    rescale_waveVector w hclock hk hτ
  have hk₀' : K 0 = lam • e 0 2 := by
    change k (w.clock 0) = lam • w.basis (w.clock 0) 2
    rw [PhysicalAmplification.clock_zero]
    exact hk.2.1
  have hwave := waveVector_polynomial_error_of_frame (kp := kp') (ap := ap') (k := K) (B := B')
    (E := E') (ε := ε) (scale := lam) (S := w.shear) hεpos.le hε1 hT hδ hk.1.ne' hS1 h240' hp'
    he hE₁ hE₂ hE₃ hlog hk' hk₀' (fun τ hτ => (hcoef _ (hclock hτ)).1)
    (fun τ hτ => (hcoef _ (hclock hτ)).2.1) (fun τ hτ => (hcoef _ (hclock hτ)).2.2.2)
  have hgeo (τ : ℝ) (hτ : τ ∈ Icc 0 T) :=
    waveVector_coordinate_bounds (S := w.shear) hεpos.le hεhalf hT hτ
      ((hwave τ hτ).1.trans (hwave τ hτ).2)
  have hZne (τ : ℝ) (hτ : τ ∈ Icc 0 T) : Z e K lam τ ≠ 0 := by
    have := (hgeo τ hτ).1; intro h; rw [h] at this; norm_num at this
  -- The error operator of the raw amplitude system.
  let M := fun τ => strain (e τ) (B' τ) (E' τ) w.shear (strengthRatio kp' ap' τ)
  let R := fun τ => errorOperator ε τ (entry (e τ) (B' τ)) (entry (e τ) (M τ))
    (X e K lam τ) (Q e K lam w.shear τ) (Z e K lam τ) w.shear
  have hRb (τ : ℝ) (hτ : τ ∈ Icc 0 T) : ‖R τ‖ ≤ C' * T ^ n * δ :=
    hbound (he τ hτ) (B' τ) (E' τ) hT hτ.1 hτ.2 hεpos.le hε1 hS1 hSinv hδ (hwave τ hτ).2
      (hwave τ hτ).1 (hcoef _ (hclock hτ)).1 (hcoef _ (hclock hτ)).2.1
      (hcoef _ (hclock hτ)).2.2.1 (hcoef _ (hclock hτ)).2.2.2 (hσ τ hτ)
  -- Continuity of the error operator.
  have hkpC : ContinuousOn kp' (Icc 0 T) := HasDerivWithinAt.continuousOn hkp'
  have hapC : ContinuousOn ap' (Icc 0 T) := HasDerivWithinAt.continuousOn hap'
  have heC (i : Fin 3) : ContinuousOn (fun τ => e τ i) (Icc 0 T) :=
    continuousOn_frame hkpC hapC (fun τ hτ => (hp' τ hτ).1) (fun τ hτ => (hp' τ hτ).2.1) i
  have hB'C : ContinuousOn B' (Icc 0 T) :=
    (continuousOn_comp_clock w hclock w.older_continuous).const_smul (1 / w.rate)
  have hE'C : ContinuousOn E' (Icc 0 T) :=
    (continuousOn_comp_clock w hclock w.error_continuous).const_smul (1 / w.rate)
  have hσC : ContinuousOn (fun τ => strengthRatio kp' ap' τ) (Icc 0 T) :=
    (hkpC.norm.mul hapC.norm).div_const _
  have hrank : ContinuousOn (fun τ => InnerProductSpace.rankOne ℝ (e τ 1) (e τ 0)) (Icc 0 T) :=
    ((InnerProductSpace.rankOne ℝ).continuous.comp_continuousOn (heC 1)).clm_apply (heC 0)
  have hMC : ContinuousOn M (Icc 0 T) :=
    (hB'C.add ((hσC.const_mul w.shear).smul hrank)).add hE'C
  have hKC : ContinuousOn K (Icc 0 T) := HasDerivWithinAt.continuousOn hk'
  have hRC : ContinuousOn R (Icc 0 T) :=
    continuousOn_errorOperator (b := fun τ => entry (e τ) (B' τ))
      (A := fun τ => entry (e τ) (M τ)) (x := X e K lam) (q := Q e K lam w.shear)
      (z := Z e K lam) hS0.ne' hZne
      (fun i j => (heC i).inner (hB'C.clm_apply (heC j)))
      (fun i j => (heC i).inner (hMC.clm_apply (heC j)))
      (((heC 0).inner hKC).div_const lam) ((((heC 1).inner hKC).const_mul w.shear).div_const lam)
      (((heC 2).inner hKC).div_const lam)
  have hbig {a : ℝ} (ha : 0 ≤ a) (haC : a ≤ C) {m : ℕ} (hm : T ^ m ≤ T ^ p) :
      a * T ^ m * δ ≤ C * T ^ p * δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul haC hm (by positivity) hC0) hδ
  refine ⟨absorb hT hδ hC0 hpC h2C hsmall.2 hε1, fun τ hτ => ?_, fun τ hτ => ?_,
    fun τ hτ => ?_, ⟨conjError R, fun τ hτ => ?_, fun a ha τ hτ => ?_,
      continuousOn_conjError hRC⟩, fun τ hτ => ?_⟩
  · -- (2.10), first bound, in the Euclidean norm.
    refine le_trans (norm_zeta_sub_le w lam k τ) (le_trans (hwave τ hτ).1 ?_)
    rw [show 120 * δ * T ^ 6 = 120 * T ^ 6 * δ by ring]
    exact hbig (by norm_num) (by linarith) (hT68.trans hTp8)
  · -- (2.10), second bound: `||k|²cos²φ/λ² - 1| ≤ CT^Cδ`.
    have hm := wave_norm_sq_eq (e := e) (k := K) (t := τ) (scale := lam) (S := w.shear)
      (he τ hτ) hk.1.ne' hS0.ne'
    have hlam : lam ≠ 0 := hk.1.ne'
    have hrw : ‖k (w.clock τ)‖ ^ 2 * Real.cos (referenceAngle ε τ) ^ 2 / lam ^ 2 =
        (X e K lam τ ^ 2 + Q e K lam w.shear τ ^ 2 / w.shear ^ 2 + Z e K lam τ ^ 2) *
          (1 + x ε τ ^ 2)⁻¹ := by
      rw [show ‖k (w.clock τ)‖ ^ 2 = ‖K τ‖ ^ 2 from rfl, hm, cos_referenceAngle_sq, normFactor]
      field_simp [hlam]
    rw [hrw]
    have hsum := (hwave τ hτ).1
    have hXx : |X e K lam τ - x ε τ| ≤ 120 * δ * T ^ 6 := by
      linarith [abs_nonneg (Q e K lam w.shear τ + ε * τ), abs_nonneg (Z e K lam τ - 1)]
    have hZ1 : |Z e K lam τ - 1| ≤ 120 * δ * T ^ 6 := by
      linarith [abs_nonneg (Q e K lam w.shear τ + ε * τ), abs_nonneg (X e K lam τ - x ε τ)]
    have hxT : x ε τ ≤ T ^ 2 / 4 := by
      have hττ : τ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hτ.1 hτ.2 2
      unfold x
      nlinarith [mul_le_mul hεhalf hττ (sq_nonneg τ) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine (normFactor_cos_bound hT hS2inv (x_nonneg hεpos.le τ) hxT hXx (hwave τ hτ).2
      (hgeo τ hτ).2.2.2.1 hZ1).trans ?_
    have h1 : 2 * T ^ 2 * (120 * δ * T ^ 6) + 2 * T ^ 2 * δ ≤ 242 * T ^ 8 * δ := by
      have : T ^ 2 * T ^ 6 = T ^ 8 := by ring
      nlinarith [mul_le_mul_of_nonneg_right hT28 hδ]
    exact h1.trans (hbig (by norm_num) hC242 hTp8)
  · -- (2.11).
    exact ⟨(hgeo τ hτ).1, (hgeo τ hτ).2.1,
      norm_zeta_le w hT (hgeo τ hτ).2.2.1 (hgeo τ hτ).2.2.2.1 (hgeo τ hτ).1 (hgeo τ hτ).2.1⟩
  · -- `sup|ℰ| ≤ CT^Cδ`.
    exact (norm_conjError_le R τ).trans ((hRb τ hτ).trans (hbig hC' hCC' hTpn))
  · -- The system for `(α₁, α₂)` of every amplitude vector, with the same `ℰ`.
    have hperp : ⟪K τ, (a ∘ w.clock) τ⟫_ℝ = 0 := by
      rw [real_inner_comm]; exact ha.2 _ (hclock hτ)
    obtain ⟨hU, hV⟩ := normalized_amplitude_perturbed (e := e) (k := K) (a := a ∘ w.clock)
      (B := B' τ) (M := M τ) (ε := ε) (scale := lam) (S := w.shear) (he τ hτ) hk.1.ne'
      hS0.ne' (hZne τ hτ) hperp (hE₁ τ hτ) (hE₂ τ hτ) (rescale_amplitude w hclock hk ha hτ)
    exact alpha_system_of_raw w (R := R) hU hV
  · -- `sup|σ_p/σ - 1| ≤ 2Tδ`.
    rw [← strengthRatio_clock]
    exact hσ τ hτ

end TorusEuler.Paper
