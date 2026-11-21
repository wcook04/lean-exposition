import TorusEuler.Paper.Proofs.S2b.Library.Restrict
import TorusEuler.Paper.Proofs.S2b.Library.Comparison

/-! # Conditional proof of Lemma 2.6

`TorusEuler.Paper.Proof.lemma_2_6_of`, following the proof of Lemma 2.6
(`cc:lem:finite-comparison`) in
`paper/craik_criminale_rewrite/sections/03_amplification.tex:620-703`, with the
normalized coordinates and the triangular system of `:537-584`.
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper

open MovingWaveVector MovingAmplitude ReferenceRiccati ReferenceAmplitude ReferencePropagator
  ReferenceComparison Lib.S2b

/-- Proof of **Lemma 2.6** (`cc:lem:finite-comparison`) following
`sections/03_amplification.tex:620-703` (with the normalized coordinates `(h, l)` of
(2.15) and the triangular system (2.16), `:537-584`), in normalized time `τ`
(`t = t₀ + τ/r`). The library coordinates are `(U, V) = (-α₁, α₂)`.

* `h2_4` (Lemma 2.4) is used where the text writes "By Lemma 2.4, `(h, l)` solves (2.16)
  with the additional coefficient matrix `RℰR⁻¹`" (`:634`): the error `ℰ` with
  `sup|ℰ| ≤ CT^Cδ`, the system for `(α₁, α₂)` of every amplitude vector (for `a`, and,
  for the bound on `Φ`, for the amplitude vectors of the slab), and the exported
  continuity of `ℰ` needed by the variation of constants (`:640-648`); further, the first
  bound of (2.10) (`|ζ - ζ₀| ≤ CT^Cδ ≤ 1/2`, `:690`) and, of (2.11), only
  `1/2 ≤ ζ₃ ≤ 3/2` (`:665`, `:686`), which also gives `k ≠ 0` on the slab. The text reads
  the bounds on `ζ₁, ζ₂` at `:665` and `:686` from `|ζ| ≤ 3T²` in (2.11). The library
  lemmas used here need the sharper bounds `|ζ₁| ≤ T²` and `|ζ₂| ≤ T`, hence `≤ S`
  (`normCorrection_le_of_growing_geometry` inside `Lib.S2b.norm_bounds_of_state_close` and
  `log_growing_physical_norm_le`, and the geometry hypotheses of
  `Lib.S2b.norm_movingAmplitude_le_from_of_dev`). These bounds are therefore taken from the
  first bound of (2.10) through `Lib.S2b.geometry_of_close`, and the conjunct
  `|ζ| ≤ 3T²` of (2.11) is not used.
* `h2_5` (Lemma 2.5): the reference solution `Y` of (2.12) (existence clause; `a_ref` is
  built from it), `|Y| ≤ 1` (`:636`, `:663`), the form (2.13) with `e ≥ 0`, which gives the
  propagator bound `|Ψ₀| ≤ 2` of the triangular system (2.16) (`:567-584`, used at
  `:640-648` and, through `|Ψ| ≤ 4`, at `:696`), and its uniqueness, which identifies `Y`
  with every solution of (2.12) in the first bound of (2.17) and in (2.18). Change of
  route: the text obtains the second equation of (2.16) from Liouville's formula and
  (2.14) (`:553-569`). Here (2.16) is obtained by differentiating (2.15) using (2.12),
  with `e` the function `deviation ε Y` determined by (2.13)
  (`ReferencePropagator.hasDerivWithinAt_normalized` and
  `ReferenceComparison.hasDerivWithinAt_normalized_perturbed`, inside
  `Lib.S2b.raw_matrix_comparison_of_dev` and the other propagator copies of
  `Library/Propagator.lean`). So the (2.14) clause of `h2_5` is not used in this proof.

Steps: the variation-of-constants estimate `sup|(h - 1, l)| ≤ CT^Cδ ≤ 1/2`
(`:640-656`) is `Lib.S2b.normalized_close_to_growing_of_dev` (a copy of
`ReferenceAmplitude.normalized_close_to_growing_of_raw_matrix` taking `e ≥ 0` from Lemma 2.5)
with the integrated budget `integrated_growing_error_le`; then `α₂ = a_ref h > 0` and
`|α₁/α₂ + Y| ≤ 2|l|` (`:658-664`, `raw_ratio_close_of_growing_state_close`); the second
bound of (2.17) from `|a|² = α₂² + S⁻²(α₁² + α₃²)` and (2.8) (`:663-672`,
`Lib.S2b.norm_bounds_of_state_close`); (2.18) (`:672-675`,
`log_growing_physical_norm_le`). For `Φ` (`:677-702`): the transverse transport on the slab
is a linear equivalence of the transverse planes (`exists_affineWave_transverse_equiv_Icc`),
equal to the transport of every amplitude vector by uniqueness for linear equations.
Deviation: the claim of the statement that `Φ(τ₂, τ₁)` maps the plane perpendicular to
`k(τ₁)` onto the plane perpendicular to `k(τ₂)` is left implicit in the text: the proof
(`:620-703`) does not argue it and cites no result for it. It is the perpendicularity
clause of Lemma 2.1 (`02_affine.tex:20-22`, from `(k·a)' = -2k·Da + p_w|k|² = 0`,
`02_affine.tex:43-44`) for the background `M`. This proof does not cite Lemma 2.1, and
`Statement.lemma_2_1` would not apply in any case: it assumes that the background `D` is
differentiable with `D' + D²` self-adjoint, which `M` need not satisfy. The claim is
supplied by the library transport `exists_affineWave_transverse_equiv_Icc`, which proves
the propagation of perpendicularity again for a continuous background, from either end of
the slab (its private step `affineWave_perp_of_mem_Icc`, through
`hasDerivWithinAt_affineWavePairing_zero`). Neither lemma is ledger content. The
bound is the propagator bound `Lib.S2b.norm_movingAmplitude_le_from_of_dev` (a copy of
`ReferenceComparison.norm_movingAmplitude_le_from` taking `e ≥ 0` from Lemma 2.5: the
coordinate maps `L_h, L_l` and `|Ψ| ≤ 4`) applied to the amplitude vectors of the slab
(the setting restricted to the slab, `Lib.S2b.restrictSlab`, whose `δ` is at most `δ`),
followed by (2.18) at `τ₁` and `τ₂`. Constants: `C = 64|C₄| + 80`, `p = p₄ + 4`.
Equations: (2.3), (2.6)-(2.8), (2.10)-(2.18). -/
theorem Proof.lemma_2_6_of (h2_4 : Statement.lemma_2_4) (h2_5 : Statement.lemma_2_5) :
    Statement.lemma_2_6 := by
  obtain ⟨C4, p4, N4, h4⟩ := h2_4
  refine ⟨64 * |C4| + 80, p4 + 4, max N4 (240 + (p4 + 3) + Nat.ceil (64 * |C4| + 40)), ?_⟩
  intro C₀ hN I t₀ T lam w k a hT hclock hsmall hk ha ha₀ ε δ α
  simp only [max_le_iff] at hN
  obtain ⟨hN4, hNL⟩ := hN
  have h240 : 240 ≤ C₀ := by omega
  have hCL : 64 * |C4| + 40 ≤ (C₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (64 * |C4| + 40) ≤ C₀ by omega))
  obtain ⟨hεpos, hεhalf, hδ, hS0, hS1, -, hS2inv, -, -, hTS, -⟩ :=
    normalized_facts w (basis_orthonormal w w.activation) hT h240 hsmall
  have hε1 : w.ratio ≤ 1 := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA0 : 0 ≤ |C4| := abs_nonneg C4
  -- Lemma 2.5: the reference solution `Y` and `|Y| ≤ 1`.
  obtain ⟨⟨Y, hYs⟩, h5⟩ := h2_5 hεpos hε1
  obtain ⟨hYuniq, hYb, e5, he5, hform5, -⟩ := h5 Y hYs
  obtain ⟨hY₀, hY⟩ := referenceSlope_iff.1 hYs
  have hdev0 (r : ℝ) (hr : r ∈ Icc 0 T) : 0 ≤ deviation ε Y r := by
    rw [deviation_eq_of_form (hform5 r hr.1)]
    exact (he5 r hr.1).1
  have hYw (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r :=
    (hY r hr.1).mono Icc_subset_Ici_self
  have hYbT (r : ℝ) (hr : r ∈ Icc 0 T) : |Y r| ≤ 1 := hYb r hr.1
  -- Lemma 2.4: (2.10), (2.11), the error `ℰ` and the system for `(α₁, α₂)`.
  obtain ⟨h4half, h4zeta, -, h4geom, ⟨ℰ, hℰb, hℰsys, hℰc⟩, -⟩ := h4 hN4 w hT hclock hsmall hk
  set η := |C4| * T ^ p4 * w.errorSize with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hRη (r : ℝ) (hr : r ∈ Icc 0 T) : ‖conjError ℰ r‖ ≤ η :=
    (norm_conjError_le ℰ r).trans ((hℰb r hr).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C4) (by positivity)) hδ))
  have hclose (r : ℝ) (hr : r ∈ Icc 0 T) :=
    coordinates_close_of_zeta w ((h4zeta r hr).trans h4half)
  have hgeo (r : ℝ) (hr : r ∈ Icc 0 T) :=
    geometry_of_close hεpos.le hεhalf hT hr (hclose r hr).1 (hclose r hr).2.1
  have hZ (r : ℝ) (hr : r ∈ Icc 0 T) :
      1 / 2 ≤ Z (nbasis w) (k ∘ w.clock) lam r ∧ Z (nbasis w) (k ∘ w.clock) lam r ≤ 3 / 2 := by
    rw [← zeta_two]
    exact ⟨(h4geom r hr).1, (h4geom r hr).2.1⟩
  have hperpa (r : ℝ) (hr : r ∈ Icc 0 T) :
      ⟪(k ∘ w.clock) r, (a ∘ w.clock) r⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact ha.2 _ (hclock hr)
  -- The raw system for `(U, V) = (-α₁, α₂)` of `a`, with error `PℰP`.
  have hsys (r : ℝ) (hr : r ∈ Icc 0 T) := raw_system_of_alpha w (hℰsys a ha r hr)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0⟩
  obtain ⟨hU₀, hV₀⟩ := growing_components (e := nbasis w) (a := a ∘ w.clock) (t := 0)
    (basis_orthonormal w (hclock h0)) hS0.ne'
    (by simpa only [Function.comp_apply, nbasis, PhysicalAmplification.clock_zero] using ha₀)
  have hBudget := growing_budget_of_polynomial_smallness hT hA0 hδ
    (show p4 + 3 ≤ C₀ by omega) (show 4 ≤ C₀ by omega) hCL hsmall.2
  set d := 32 * |C4| * T ^ (p4 + 3) * w.errorSize with hddef
  have hd : d ≤ 1 / 2 := by
    nlinarith [hBudget, hε1, show 0 ≤ 40 * T ^ 4 * w.errorSize by positivity]
  -- Variation of constants: `sup|(h - 1, l)| ≤ d ≤ 1/2`.
  have hstate (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖normalizedState ε Y (U (nbasis w) (a ∘ w.clock) w.shear)
        (V (nbasis w) (a ∘ w.clock)) t - (1, 0)‖ ≤ d := by
    obtain ⟨hD₀, hDraw⟩ := integrated_growing_error_le hεpos.le hε1 hT ht hη0
      (HasDerivWithinAt.continuousOn hYw) hYbT
    set D := ∫ r in (0 : ℝ)..t, ((1 + |Y r|) ^ 2 / s ε r) * η with hDdef
    have hD₁ : D ≤ 4 * |C4| * T ^ (p4 + 3) * w.errorSize := by
      refine hDraw.trans (le_of_eq ?_)
      rw [hηdef, pow_add]
      ring
    have hDle : D ≤ 1 / 4 := by
      nlinarith [hD₁, hBudget, hε1, show 0 ≤ 40 * T ^ 4 * w.errorSize by positivity]
    have hExp : Real.exp (2 * D) ≤ 2 := by
      have h := Real.abs_exp_sub_one_le (x := 2 * D)
        (by rw [abs_of_nonneg (by positivity)]; linarith)
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * D)] at h
      linarith [(abs_le.mp h).2]
    have hcl := normalized_close_to_growing_of_dev (η := fun _ => η) hY₀ hU₀ hV₀
      hYw hdev0 (continuousOn_conjError hℰc) continuousOn_const hRη (fun r hr => (hsys r hr).1)
      (fun r hr => (hsys r hr).2) ht
    change _ ≤ 4 * Real.exp (2 * D) * D at hcl
    calc
      _ ≤ 4 * Real.exp (2 * D) * D := hcl
      _ ≤ 8 * D := by nlinarith only [mul_nonneg hD₀ (sub_nonneg.mpr hExp)]
      _ ≤ d := by rw [hddef]; nlinarith only [hD₁]
  have hratio (r : ℝ) (hr : r ∈ Icc 0 T) :=
    raw_ratio_close_of_growing_state_close hd (hstate r hr)
  -- (2.18) for `Y`.
  have hlogA (r : ℝ) (hr : r ∈ Icc 0 T) :
      |Real.log (‖a (w.clock r)‖ / growingFactor Y r)| ≤ ε := by
    have h := log_growing_physical_norm_le (e := nbasis w) (k := k ∘ w.clock)
      (a := a ∘ w.clock) (t := r) (scale := lam) (S := w.shear) (basis_orthonormal w (hclock hr)) hk.1.ne' hS0
      (hperpa r hr) hT1 (hgeo r hr).1 (hgeo r hr).2 (hZ r hr).1 (hYbT r hr) hd (hstate r hr)
    refine h.trans ?_
    calc
      _ ≤ 2 * d + 20 * T ^ 4 * (2 * w.errorSize) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hS2inv (by positivity))
      _ = 64 * |C4| * T ^ (p4 + 3) * w.errorSize + 40 * T ^ 4 * w.errorSize := by
        rw [hddef]; ring
      _ ≤ ε := hBudget
  have hpow3 : T ^ (p4 + 3) ≤ T ^ (p4 + 4) := pow_le_pow_right₀ hT1 (by omega)
  have hpow4 : T ^ 4 ≤ T ^ (p4 + 4) := pow_le_pow_right₀ hT1 (by omega)
  have hApos (r : ℝ) (hr : r ∈ Icc 0 T) : 0 < ‖a (w.clock r)‖ :=
    (hratio r hr).1.trans_le (norm_bounds_of_state_close (e := nbasis w) (k := k ∘ w.clock)
      (a := a ∘ w.clock) (t := r) (scale := lam) (S := w.shear) (basis_orthonormal w (hclock hr))
      hk.1.ne' hS0 (hperpa r hr) hT1 (hgeo r hr).1 (hgeo r hr).2 (hZ r hr).1 (hYbT r hr) hd
      (hstate r hr)).1
  have hfactor {Z' : ℝ → ℝ} (hZ' : ReferenceSlope ε Z') {r : ℝ} (hr : r ∈ Icc 0 T) :
      referenceAmplitude Z' r = growingFactor Y r := by
    unfold referenceAmplitude growingFactor
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hr.1] at hy
    exact (hYuniq Z' hZ' hy.1).symm
  refine ⟨fun r hr => ?_, fun Z' hZ' r hr => ?_, fun r hr => ?_, fun Z' hZ' r hr => ?_, ?_⟩
  · -- `α₂ > 0`.
    rw [alpha_one]
    exact (hratio r hr).1
  · -- The first bound of (2.17).
    have key (u v y : ℝ) : |-u / v + y| = |u / v - y| := by
      rw [show -u / v + y = -(u / v - y) by ring, abs_neg]
    rw [← hYuniq Z' hZ' hr.1, alpha_zero, alpha_one, key]
    refine (hratio r hr).2.trans ?_
    rw [hddef]
    have := mul_le_mul_of_nonneg_left hpow3 (show 0 ≤ 64 * |C4| by positivity)
    nlinarith [mul_nonneg (show 0 ≤ T ^ (p4 + 4) by positivity) hδ,
      mul_le_mul_of_nonneg_right this hδ]
  · -- The second bound of (2.17).
    obtain ⟨hlo, hhi⟩ := norm_bounds_of_state_close (e := nbasis w) (k := k ∘ w.clock)
      (a := a ∘ w.clock) (t := r) (scale := lam) (S := w.shear) (basis_orthonormal w (hclock hr))
      hk.1.ne' hS0 (hperpa r hr) hT1 (hgeo r hr).1 (hgeo r hr).2 (hZ r hr).1 (hYbT r hr) hd
      (hstate r hr)
    rw [alpha_one]
    refine ⟨hlo, hhi.trans (mul_le_mul_of_nonneg_right ?_ (hratio r hr).1.le)⟩
    have h1 : 40 * T ^ 4 * (w.shear ^ 2)⁻¹ ≤ 80 * T ^ 4 * w.errorSize := by
      nlinarith [mul_le_mul_of_nonneg_left hS2inv (show 0 ≤ 40 * T ^ 4 by positivity)]
    have h2 : 80 * T ^ 4 * w.errorSize ≤ (64 * |C4| + 80) * T ^ (p4 + 4) * w.errorSize := by
      have := mul_le_mul_of_nonneg_left hpow4 (show (0 : ℝ) ≤ 80 by norm_num)
      nlinarith [mul_nonneg (mul_nonneg hA0 (show 0 ≤ T ^ (p4 + 4) by positivity)) hδ]
    linarith
  · -- (2.18).
    rw [hfactor hZ' hr]
    exact hlogA r hr
  · -- The transport `Φ` between the transverse planes and its bound.
    intro τ₁ τ₂ h0τ₁ hτ₁τ₂ hτ₂T
    have hτ₁ : τ₁ ∈ Icc 0 T := ⟨h0τ₁, hτ₁τ₂.trans hτ₂T⟩
    have hτ₂ : τ₂ ∈ Icc 0 T := ⟨h0τ₁.trans hτ₁τ₂, hτ₂T⟩
    have hsub := slab_subset w hclock
    have hs : w.clock τ₁ ∈ Icc t₀ (w.clock T) := clock_mem_slab w hτ₁
    have ht : w.clock τ₂ ∈ Icc t₀ (w.clock T) := clock_mem_slab w hτ₂
    have hkJ0 (q : ℝ) (hq : q ∈ Icc t₀ (w.clock T)) : k q ≠ 0 := by
      have he := elapsed_mem_Icc w hq
      rw [← w.clock_elapsed q]
      refine ne_zero_of_zeta_two_pos w (lam := lam) ?_
      linarith [(h4geom _ he).1]
    have hDc : ContinuousOn w.gradient (Icc t₀ (w.clock T)) :=
      (gradient_continuousOn w).mono hsub
    have hkJ (q : ℝ) (hq : q ∈ Icc t₀ (w.clock T)) :
        HasDerivWithinAt k (-((w.gradient q).adjoint (k q))) (Icc t₀ (w.clock T)) q :=
      (hk.2.2 q (hsub hq)).mono hsub
    obtain ⟨Φ, hΦ⟩ := exists_affineWave_transverse_equiv_Icc hs ht hDc hkJ0 hkJ
    refine ⟨Φ, ?_, ?_⟩
    · -- `Φ` transports every amplitude vector.
      intro b hb v hv
      obtain ⟨c, hc₀, hc₁, hc, -⟩ := hΦ v
      have hA := continuousOn_affineWaveAmplitudeOperator hDc
        (HasDerivWithinAt.continuousOn hkJ) hkJ0
      have hbJ (q : ℝ) (hq : q ∈ Icc t₀ (w.clock T)) : HasDerivWithinAt b
          (affineWaveAmplitudeOperator (w.gradient q) (k q) (b q)) (Icc t₀ (w.clock T)) q := by
        have := (hb.1 q (hsub hq)).mono hsub
        rw [affineWaveAmplitudeOperator_apply]
        exact this
      have heq := linearODE_unique_of_mem ordConnected_Icc hs hA hc hbJ (hc₀.trans hv)
      exact hc₁.symm.trans (heq ht)
    · -- The bound `‖Φ‖ ≤ 252e S |a(τ₂)|/|a(τ₁)|`.
      have hM0 : 0 ≤ 252 * Real.exp 1 * w.shear *
          (‖a (w.clock τ₂)‖ / ‖a (w.clock τ₁)‖) :=
        mul_nonneg (mul_nonneg (by positivity) hS0.le)
          (div_nonneg (norm_nonneg _) (norm_nonneg _))
      apply ContinuousLinearMap.opNorm_le_bound _ hM0
      intro v
      obtain ⟨b, hb₀, hb₁, hb, hperp⟩ := hΦ v
      change ‖(Φ v : Vec3)‖ ≤ _ * ‖(v : Vec3)‖
      rw [← hb₀, ← hb₁]
      -- Lemma 2.4 on the slab, for the amplitude vector `b`.
      let w' := restrictSlab w hT0 hclock
      have hsmall' := finiteSmallness_restrictSlab w hT0 hclock hsmall
      obtain ⟨-, -, hδ', -⟩ :=
        normalized_facts w' (basis_orthonormal w' w'.activation) hT h240 hsmall'
      obtain ⟨-, -, -, -, ⟨ℰ', hℰ'b, hℰ'sys, hℰ'c⟩, -⟩ :=
        h4 hN4 w' hT (mapsTo_restrictSlab w hT0 hclock) hsmall'
          (newWaveVector_restrictSlab w hT0 hclock hk)
      have hRη' (r : ℝ) (hr : r ∈ Icc 0 T) : ‖conjError ℰ' r‖ ≤ η :=
        (norm_conjError_le ℰ' r).trans ((hℰ'b r hr).trans (mul_le_mul
          (mul_le_mul_of_nonneg_right (le_abs_self C4) (by positivity))
          (errorSize_restrictSlab_le w hT0 hclock) hδ' (by positivity)))
      have hbAmp : AmplitudeVector w' k b :=
        ⟨fun q hq => by
            have := hb q hq
            rw [affineWaveAmplitudeOperator_apply] at this
            exact this,
          fun q hq => by rw [real_inner_comm]; exact hperp q hq⟩
      have hbsys (r : ℝ) (hr : r ∈ Icc 0 T) := raw_system_of_alpha w' (hℰ'sys b hbAmp r hr)
      have hGeom (r : ℝ) (hr : r ∈ Icc τ₁ τ₂) :
          Orthonormal ℝ (nbasis w r) ∧ ⟪(k ∘ w.clock) r, (b ∘ w.clock) r⟫_ℝ = 0 ∧
            |X (nbasis w) (k ∘ w.clock) lam r| ≤ w.shear ∧
            |Q (nbasis w) (k ∘ w.clock) lam w.shear r| ≤ w.shear ∧
            1 / 2 ≤ Z (nbasis w) (k ∘ w.clock) lam r ∧
            Z (nbasis w) (k ∘ w.clock) lam r ≤ 3 / 2 ∧
            |Y r| ≤ 1 ∧ |X (nbasis w) (k ∘ w.clock) lam r - x ε r| ≤ 1 / 2 := by
        have hr' : r ∈ Icc 0 T := ⟨h0τ₁.trans hr.1, hr.2.trans hτ₂T⟩
        have hTT : T ≤ T ^ 2 := by nlinarith
        exact ⟨basis_orthonormal w (hclock hr'), hperp _ (clock_mem_slab w hr'),
          (hgeo r hr').1.trans hTS, (hgeo r hr').2.trans (hTT.trans hTS), (hZ r hr').1,
          (hZ r hr').2, hYbT r hr', (hclose r hr').1⟩
      have hGrow := norm_movingAmplitude_le_from_of_dev (e := nbasis w) (k := k ∘ w.clock)
        (b := b ∘ w.clock) (Y := Y) (η := fun _ => η) (R := conjError ℰ') (scale := lam)
        (S := w.shear) hYw hdev0 hτ₁ ⟨hτ₁τ₂, hτ₂T⟩ hk.1.ne' hS1 hGeom
        ((continuousOn_conjError hℰ'c).mono (Icc_subset_Icc_left h0τ₁)) continuousOn_const
        (fun r hr => hRη' r ⟨h0τ₁.trans hr.1, hr.2⟩) (fun r hr => (hbsys r hr).1)
        (fun r hr => (hbsys r hr).2)
      have hE := exp_integrated_growing_error_Icc_le hεpos.le hεhalf hT hτ₁ hτ₂ hτ₁τ₂ hA0 hδ
        hBudget (HasDerivWithinAt.continuousOn hYw) hYbT
      have hCompare (r : ℝ) (hr : r ∈ Icc 0 T) :=
        reference_comparison_of_growing_log_bound (A := fun q => ‖a (w.clock q)‖) (Y := Y)
          (t := r) (hApos r hr) (hlogA r hr)
      have hG := growingFactor_ratio_le (Y := Y) (A := fun q => ‖a (w.clock q)‖)
        (by linarith) (hApos τ₁ hτ₁) (hCompare τ₂ hτ₂).1 (hCompare τ₁ hτ₁).2
      have hGnn : 0 ≤ growingFactor Y τ₂ / growingFactor Y τ₁ :=
        div_nonneg (growingFactor_pos Y τ₂).le (growingFactor_pos Y τ₁).le
      calc
        _ ≤ _ := hGrow
        _ ≤ 126 * w.shear * 2 * (Real.exp 1 * (‖a (w.clock τ₂)‖ / ‖a (w.clock τ₁)‖)) *
            ‖b (w.clock τ₁)‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_left hE (by linarith)) hG hGnn
              (by linarith)) (norm_nonneg _)
        _ = _ := by ring

end TorusEuler.Paper
