import TorusEuler.Paper.Proofs.S678b.Library.Limit
import TorusEuler.Paper.S2.Statements
import TorusEuler.Paper.SBD.Statements

/-! # Proposition 8.2: the central curl lower bound (8.2) with the cited results as hypotheses

Copies (package S678b, Proposition 8.2's own content) of the private library lemma
`InductiveEulerCentralWaves.eventually_curl_lower_bound` (Theorem11FromInductiveStages.lean:520)
and of its private helpers, with every use of another row's content replaced by a hypothesis,
where the TeX proof (sections/09b_terminal_properties.tex:12-66) uses the cited result:

* Lemma B.1 (Bernstein (B.1), through (7.6) `‖∇U_{j-2}‖_∞ ≤ λ_{j-2}^9`, 09b:39-40, 09b:48): the
  library's `eventually_central_gradient_bound` calls `exists_bandBernsteinJetBounds`; the
  copy `eventually_central_gradient_bound` uses `hB_1`.
* Lemma 2.2 (the frame equation `(log σ)' = B_{33}` of (2.2), 09b:38-39): the library's
  `preceding_strength_retained_on_short_interval` calls `hasDerivWithinAt_movingFrame`; the copy
  `preceding_strength_retained` uses `h2_2`.
* Lemma 2.4 ((2.10), (2.11): the `E_3` component of `κ_j/λ_j` is at least `1/2` and its length
  is at most `C(1+τ^2)`, 09b:25-27): the library's `GrowingCrossing.wave_geometry` calls
  `AmplificationWindow.wave_geometry`; the copy `wave_geometry_of_lemma24` uses `h2_4`.
* Lemma 1.3 ((1.15), 09b:45-46): the library's private `frequency_log_bound` calls
  `frequencySchedule_log_bound_of_maxima`; here (1.15) comes from `h1_3`
  (`lemma13_schedule`).

The comparison hypothesis (2.7) for `h2_4` (with the threshold `N` of `h2_4`) is an explicit
argument `hcomp` of `CentralWaves.eventually_curl_lower_bound`, supplied by `h71.comparison`
(item 2 of the proof of Theorem 7.1). -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S678b

open MovingWaveVector (PhysicalAmplification frame entry X Q Z)

local notation "Labels" => UnitAddTorus (Fin 3)

/-! ## Fourier bands -/

/-- Fourier coefficients commute with continuous complex-linear maps (copy of the library's
private `mFourierCoeff_comp_complexCLM`, TruncationFourierCommutation.lean:19). -/
theorem mFourierCoeff_comp_complexCLM
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (g : C(Labels, E)) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun z => L (g z)) k = L (mFourierCoeff g k) := by
  have hcont : Continuous (fun z => mFourier (-k) z • g z) :=
    (mFourier (-k)).continuous.smul g.continuous
  have hint : Integrable (fun z => mFourier (-k) z • g z) unitTorusMeasure := by
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact (μ := unitTorusMeasure) isCompact_univ
  change (∫ z, mFourier (-k) z • L (g z) ∂unitTorusMeasure) =
    L (∫ z, mFourier (-k) z • g z ∂unitTorusMeasure)
  rw [← L.integral_comp_comm hint]
  simp only [map_smul]

/-- A coordinate of a vector of `ℝ³` is bounded by its norm. -/
theorem abs_apply_le_norm (v : Vec3) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ) : Vec3) v
  rw [EuclideanSpace.inner_single_left] at h
  simpa using h

/-- A field whose complexified Fourier coefficients vanish above `R` has every scalar
measurement band-limited by `R`: `RealTorusFourierBand` (the band of (T1)) implies the
band hypothesis `RealNormedTorusFourierBand` of (B.1). -/
theorem realNormedBand_of_realTorusBand {R : ℝ} {g : C(Labels, Vec3)}
    (h : RealTorusFourierBand R g) : RealNormedTorusFourierBand R g := by
  intro l k hk
  let L : ComplexEuclideanVec3 →L[ℂ] ℂ :=
    ∑ i : Fin 3, ((l (EuclideanSpace.single i 1) : ℝ) : ℂ) • EuclideanSpace.proj i
  let G : C(Labels, ComplexEuclideanVec3) :=
    ⟨fun z => periodicComplexifyVector (g z), periodicComplexifyVector.continuous.comp g.continuous⟩
  have hpt (z : Labels) : realFourierScalarization l g z = L (G z) := by
    change ((l (g z) : ℝ) : ℂ) = _
    have hv : g z = ∑ i : Fin 3, (g z) i • (EuclideanSpace.single i 1 : Vec3) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (g z)]
      simp [EuclideanSpace.basisFun_apply]
    conv_lhs => rw [hv]
    simp [L, G, map_sum, map_smul, mul_comm]
  have hfun : (fun z => realFourierScalarization l g z) = fun z => L (G z) := funext hpt
  change mFourierCoeff (fun z => realFourierScalarization l g z) k = 0
  rw [hfun, mFourierCoeff_comp_complexCLM]
  have h0 : mFourierCoeff G k = 0 := h k hk
  rw [h0, map_zero]

/-- The operator norm of a linear map on `ℝ³` is at most the sum of its values on the
coordinate vectors. -/
theorem opNorm_le_sum_single {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Vec3 →L[ℝ] F) : ‖A‖ ≤ ∑ i : Fin 3, ‖A (EuclideanSpace.single i 1)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = ∑ i : Fin 3, v i • (EuclideanSpace.single i 1 : Vec3) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_apply]
  calc ‖A v‖ = ‖∑ i : Fin 3, v i • A (EuclideanSpace.single i 1)‖ := by
        conv_lhs => rw [hv]
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • A (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖A (EuclideanSpace.single i 1)‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_apply_le_norm v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖A (EuclideanSpace.single i 1)‖) * ‖v‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-! ## (7.6) from Lemma B.1 -/

/-- (7.6) at the origin, `‖∇U_n(t,0)‖ ≤ λ_n^9` for large `n` (sections/08b_induction.tex:205-219,
used at 09b:39-40 and 09b:48): Bernstein's inequality (B.1) of `hB_1` at order one, for the
field `U_n(t)` with frequencies at most `2λ_n^5 ≤ 4Λ`, `Λ = λ_n^5` (`h71.T1`), and
`‖U_n(t)‖_∞ ≤ λ_n` ((T2)). Copy of the library's private
`InductiveEulerStages.eventually_central_gradient_bound`, with `hB_1` in place of
`exists_bandBernsteinJetBounds`. -/
theorem eventually_central_gradient_bound (hB_1 : Statement.lemma_B_1)
    {P : InductiveEulerParameters} {c : InductiveEulerConstruction P} {C T : ℝ}
    (h71 : Theorem71Conclusions c C T) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc 0 (c.stages.slab n),
      ‖fderiv ℝ (c.stages.velocity n t) 0‖ ≤ P.frequency n ^ 9 := by
  obtain ⟨Cop, Cb, Ct, -, hCb, -, hB⟩ := hB_1 _ AppendixB.cutoffSymbol_dyadicMultiplierCutoff
  have hinit := two_le_frequency_zero P
  have hfreq : Tendsto P.frequency atTop atTop :=
    frequencySchedule_frequency_tendsto_atTop P.exponentParameter P.order P.frequency
      P.exponentParameter_ge (one_lt_two.trans_le hinit) P.frequency_step
  filter_upwards [hfreq.eventually_ge_atTop (3 * Cb 1), hfreq.eventually_ge_atTop 1]
    with n hn hn1 t ht
  have hpos : 0 < P.frequency n := zero_lt_one.trans_le hn1
  let Λ := P.frequency n ^ 5
  have hΛ : 0 < Λ := pow_pos hpos 5
  let g := c.stages.torusVelocity n t
  have hband : RealNormedTorusFourierBand (4 * Λ) g :=
    realNormedBand_of_realTorusBand fun k hk => ((h71.T1 n).2 t ht).2.2.2 k
      ((show 2 * P.frequency n ^ 5 ≤ 4 * Λ by
        have := pow_pos hpos 5
        dsimp only [Λ]
        linarith).trans_lt hk)
  have hb := (hB Λ hΛ).2.2 1 Vec3 g hband
  have hg : ‖g‖ ≤ P.frequency n := c.stages.velocity_bound n t ht
  have hterm (i : Fin 3) :
      ‖fderiv ℝ (c.stages.velocity n t) 0 (EuclideanSpace.single i 1)‖ ≤ Cb 1 * Λ * ‖g‖ := by
    let β : Fin 1 → Fin 3 := fun _ => i
    have hβ : β ∈ Finset.univ.filter (fun β : Fin 1 → Fin 3 => Monotone β) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun a b _ => le_rfl
    have h1 : ‖iteratedFDeriv ℝ 1 (fun z => g (toUnitTorus z)) 0
        (fun j => EuclideanSpace.single (β j) 1)‖ ≤
          ⨆ x : Vec3, ‖iteratedFDeriv ℝ 1 (fun z => g (toUnitTorus z)) x
            (fun j => EuclideanSpace.single (β j) 1)‖ := le_ciSup (hb.1 β) 0
    have h2 := Finset.single_le_sum (f := fun β : Fin 1 → Fin 3 => ⨆ x : Vec3,
      ‖iteratedFDeriv ℝ 1 (fun z => g (toUnitTorus z)) x
        (fun j => EuclideanSpace.single (β j) 1)‖)
      (fun β _ => Real.iSup_nonneg fun _ => norm_nonneg _) hβ
    rw [iteratedFDeriv_one_apply] at h1
    have := (h1.trans h2).trans hb.2
    rw [pow_one] at this
    exact this
  calc ‖fderiv ℝ (c.stages.velocity n t) 0‖
      ≤ ∑ i : Fin 3, ‖fderiv ℝ (c.stages.velocity n t) 0 (EuclideanSpace.single i 1)‖ :=
        opNorm_le_sum_single _
    _ ≤ ∑ _i : Fin 3, Cb 1 * Λ * ‖g‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = 3 * Cb 1 * Λ * ‖g‖ := by simp; ring
    _ ≤ P.frequency n * Λ * P.frequency n := by
        have hCb1 := hCb 1
        gcongr
    _ = P.frequency n ^ 7 := by dsimp only [Λ]; ring
    _ ≤ P.frequency n ^ 9 := pow_le_pow_right₀ hn1 (by decide)

/-! ## The preceding strength, from Lemma 2.2 -/

/-- The preceding wave retains its strength on a short interval (09b:36-44): by the frame
equation `(log σ)' = B_{33}` of (2.2) (`h2_2`), `|∂_t log σ| ≤ |B| ≤ μ^{1/32}` on an interval
of length at most `μ^{-1/16}`, so `log σ` changes by at most one. Copy of the library's
`preceding_strength_retained_on_short_interval` (InductiveVorticityBounds.lean:155) with `h2_2`
(its log-strength clause and the orthonormality of the frame) in place of
`hasDerivWithinAt_movingFrame`. -/
theorem preceding_strength_retained (h2_2 : Statement.lemma_2_2)
    {k a : ℝ → Vec3} {B : ℝ → Vec3 →L[ℝ] Vec3} {l r μ : ℝ}
    (hμ : 1 ≤ μ) (hshort : r - l ≤ μ ^ (-1 / 16 : ℝ))
    (hframe : ∀ t ∈ Icc l r, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0)
    (htrace : ∀ t ∈ Icc l r, LinearMap.trace ℝ Vec3 (B t).toLinearMap = 0)
    (hk : ∀ t ∈ Icc l r, HasDerivWithinAt k (-((B t).adjoint (k t))) (Icc l r) t)
    (ha : ∀ t ∈ Icc l r, HasDerivWithinAt a
      (-((B t) (a t)) + (2 * ⟪k t, B t (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) (Icc l r) t)
    (hB : ∀ t ∈ Icc l r, ‖B t‖ ≤ μ ^ (1 / 32 : ℝ))
    {t : ℝ} (ht : t ∈ Icc l r) :
    Real.exp (-1) * (‖k l‖ * ‖a l‖) ≤ ‖k t‖ * ‖a t‖ := by
  let σ (s : ℝ) := ‖k s‖ * ‖a s‖
  let E (s : ℝ) := frame k a s 2
  have hWave : WaveOn (Icc l r) B k a := ⟨hk, fun s hs => by
    simpa only [affineWavePressureCoeff] using ha s hs⟩
  have hFrameEq (s : ℝ) (hs : s ∈ Icc l r) :=
    h2_2 (J := Icc l r) (B := B) (k := k) (a := a) htrace hWave hframe s hs
  have hlog (s : ℝ) (hs : s ∈ Icc l r) :
      HasDerivWithinAt (fun u => Real.log (σ u)) ⟪E s, B s (E s)⟫_ℝ (Icc l r) s :=
    (hFrameEq s hs).2.2.2.2
  have hderivBound (s : ℝ) (hs : s ∈ Ico l r) :
      ‖⟪E s, B s (E s)⟫_ℝ‖ ≤ μ ^ (1 / 32 : ℝ) := by
    have hs' := Ico_subset_Icc_self hs
    have hunit : ‖E s‖ = 1 := (hFrameEq s hs').1.norm_eq_one 2
    have hinner := abs_real_inner_le_norm (E s) (B s (E s))
    have hop := (B s).le_opNorm (E s)
    rw [hunit, one_mul] at hinner
    rw [hunit, mul_one] at hop
    simpa only [Real.norm_eq_abs] using (hinner.trans hop).trans (hB s hs')
  have hμ₀ := zero_lt_one.trans_le hμ
  have hsmall : μ ^ (1 / 32 : ℝ) * μ ^ (-1 / 16 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hμ₀]
    exact Real.rpow_le_one_of_one_le_of_nonpos hμ (by norm_num)
  have habs : |Real.log (σ t) - Real.log (σ l)| ≤ 1 := by
    have hh := norm_image_sub_le_of_norm_deriv_le_segment' hlog hderivBound t ht
    rw [Real.norm_eq_abs] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l)
      (Real.rpow_nonneg hμ₀.le _)).trans
        ((mul_le_mul_of_nonneg_left hshort (Real.rpow_nonneg hμ₀.le _)).trans hsmall))
  have hσ (s : ℝ) (hs : s ∈ Icc l r) : 0 < σ s :=
    mul_pos (norm_pos_iff.mpr (hframe s hs).1) (norm_pos_iff.mpr (hframe s hs).2.1)
  have hleft : l ∈ Icc l r := ⟨le_rfl, ht.1.trans ht.2⟩
  calc
    Real.exp (-1) * σ l = Real.exp (-1 + Real.log (σ l)) := by
      rw [Real.exp_add, Real.exp_log (hσ l hleft)]
    _ ≤ Real.exp (Real.log (σ t)) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp habs).1])
    _ = σ t := Real.exp_log (hσ t ht)

/-! ## The geometry of the new wave, from Lemma 2.4 -/

/-- The bounds on the scaled wave vector of the new wave that the projection (8.1) uses
(09b:25-27), from Lemma 2.4: with `ζ` the scaled components (2.3) of the crossing's wave vector
at normalized time `τ` (`t = t_0 + τ/r`), (2.11) gives `1/2 ≤ ζ_3 ≤ 3/2` and
`|ζ_1| ≤ |ζ| ≤ 3T^2 ≤ (2T)^2`, and (2.10) gives `|ζ_2 + ετ| ≤ 1/2`, so `|ζ_2| ≤ T + 1/2 ≤ 2T`.
These are the bounds `|X| ≤ (2T)^2`, `|Q| ≤ 2T`, `|Z - 1| ≤ 1/2` in the library's notation
`X, Q, Z` (the `E_1`, scaled `E_2` and `E_3` components of `k/λ` in the preceding frame).
Replaces the library's `GrowingCrossing.wave_geometry` (content of Lemma 2.4). The hypotheses:
the window `I` of `w` is the active slab `[t_0, t_0 + T/r]`, and (2.7) holds with a constant
`C₀ ≥ N`, `N` the threshold of `h2_4`. -/
theorem wave_geometry_of_lemma24 (h2_4 : Statement.lemma_2_4) :
    ∃ N : ℕ, ∀ {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {C₀ : ℕ}
      {w : PhysicalAmplification I t₀} (d : w.GrowingCrossing T scale Ustar next),
      N ≤ C₀ → 1 ≤ C₀ → 2 ≤ T → 0 < scale → I = w.activeSlab T →
      FiniteSmallness w T C₀ → ∀ {t : ℝ}, t ∈ w.activeSlab T →
        |X w.basis d.waveVector scale t| ≤ (2 * T) ^ 2 ∧
          |Q w.basis d.waveVector scale w.shear t| ≤ 2 * T ∧
          |Z w.basis d.waveVector scale t - 1| ≤ 1 / 2 := by
  obtain ⟨Cc, p, N, h24⟩ := h2_4
  refine ⟨N, fun {I t₀ T scale Ustar next C₀ w} d hN hC₀ hT hscale hI hsmall t ht => ?_⟩
  have hr := w.rate_pos
  have hmaps : MapsTo w.clock (Icc 0 T) I := by
    intro τ hτ
    refine (Set.ext_iff.mp hI _).mpr ⟨?_, w.strictMono_clock.monotone hτ.2⟩
    simpa only [MovingWaveVector.PhysicalAmplification.clock_zero] using
      w.strictMono_clock.monotone hτ.1
  have hk : NewWaveVector w scale d.waveVector := by
    refine ⟨hscale, d.initial_waveVector, fun s hs => ?_⟩
    have hs' : s ∈ w.activeSlab T := (Set.ext_iff.mp hI s).mp hs
    exact (d.waveVector_derivative s hs').mono fun x hx => (Set.ext_iff.mp hI x).mp hx
  obtain ⟨hδ, hζ, -, h211, -⟩ := h24 hN w hT hmaps hsmall hk
  have hτ : w.elapsed t ∈ Icc 0 T := by
    have h1 := w.strictMono_elapsed.monotone ht.1
    have h2 := w.strictMono_elapsed.monotone ht.2
    simp only [MovingWaveVector.PhysicalAmplification.elapsed_clock] at h1 h2
    exact ⟨by simpa [MovingWaveVector.PhysicalAmplification.elapsed] using h1, h2⟩
  have hclock : w.clock (w.elapsed t) = t := w.clock_elapsed t
  set τ := w.elapsed t
  have hζτ := hζ τ hτ
  obtain ⟨hz3lo, hz3hi, hznorm⟩ := h211 τ hτ
  have hε₀ : 0 < w.ratio := w.ratio_pos
  have hε₁ : w.ratio ≤ 1 := by
    have h := hsmall.1
    have hC : (1 : ℝ) ≤ C₀ := by exact_mod_cast hC₀
    nlinarith
  have hcomp (i : Fin 3) : |zeta w scale d.waveVector τ i - zetaRef w.ratio τ i| ≤ 1 / 2 := by
    have := abs_apply_le_norm (zeta w scale d.waveVector τ - zetaRef w.ratio τ) i
    simp only [PiLp.sub_apply] at this
    linarith
  have hX : X w.basis d.waveVector scale t = zeta w scale d.waveVector τ 0 := by
    simp [zeta, MovingWaveVector.X, hclock]
  have hQ : Q w.basis d.waveVector scale w.shear t = zeta w scale d.waveVector τ 1 := by
    simp [zeta, MovingWaveVector.Q, hclock]
  have hZ : Z w.basis d.waveVector scale t = zeta w scale d.waveVector τ 2 := by
    simp [zeta, MovingWaveVector.Z, hclock]
  have href1 : zetaRef w.ratio τ 1 = -(w.ratio * τ) := by simp [zetaRef]
  refine ⟨?_, ?_, ?_⟩
  · rw [hX]
    calc |zeta w scale d.waveVector τ 0| ≤ ‖zeta w scale d.waveVector τ‖ := abs_apply_le_norm _ 0
      _ ≤ 3 * T ^ 2 := hznorm
      _ ≤ (2 * T) ^ 2 := by nlinarith
  · rw [hQ]
    have h1 := hcomp 1
    rw [href1] at h1
    have hετ : w.ratio * τ ≤ T := by nlinarith [hτ.1, hτ.2]
    have hετ0 : 0 ≤ w.ratio * τ := mul_nonneg hε₀.le hτ.1
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  · rw [hZ, abs_le]
    constructor <;> linarith

end TorusEuler.Paper.Lib.S678b
