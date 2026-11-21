import TorusEuler.Paper.Proofs.S2b.Library.Glue

/-! # Copy of the library carrier of Proposition 2.8 with the facts of Lemma 2.5 as hypotheses

`ReferenceAmplitude.growing_amplitude_crossing_strength_and_gain` (ledger content of
row 2.8) derives from the Riccati equation of `Y` the facts of Lemma 2.5 that the proof of
Proposition 2.8 uses: the zero `τ_m ∈ [2/ε, 3/ε]` of `Y`, the maximum of `a_ref` at `τ_m`,
the gain `log a_ref(τ_m) ≥ ε^{-1/2} - 1`, `Y ≤ 1`, the form (2.13) and formula (2.14).
The copy `crossing_strength_and_gain_of_reference` takes them as hypotheses, so that the
proof of Proposition 2.8 supplies them from `Statement.lemma_2_5`.

Two steps differ from the library proof. (i) The ratio `a_ref(τ)/a_ref(τ_m)` is obtained
by dividing (2.14) at `τ` by (2.14) at `τ_m` (`referenceV_ratio_of_amplitude`,
`sections/03_amplification.tex:946-951`); the library instead integrates (2.13)
(`ReferenceRiccati.referenceV_ratio_decomposition`, which is the derivation of (2.14) in
the proof of Lemma 2.5). The library glue that consumed that ratio is copied with the ratio
as a hypothesis:

| Library (namespace `TorusEuler.ReferenceRiccati`) | Copy (namespace `TorusEuler.Paper.Lib.S2b`) |
| --- | --- |
| `continuous_damping_quarter` (private) | `continuous_damping_quarter` (verbatim) |
| `continuousOn_deviation_envelope` (private) | `continuousOn_deviation_envelope` (verbatim) |
| `s_ratio_bounds` (private) | `s_ratio_bounds` (verbatim) |
| `referenceV_late_ratio_bounds` | `referenceV_late_ratio_bounds_of_ratio` |
| `referenceV_late_strength_bounds` | `referenceV_late_strength_bounds_of_ratio` |
| `amplitude_late_strength_bounds_of_reference_comparison` | `amplitude_late_strength_bounds_of_ratio` |

(ii) "`|k|` is comparable to `λ/cos φ`, by (2.10)" (`:954-955`) is read from the second
bound of (2.10) (`wave_norm_comparable_of_norm_bound`, new glue), in place of the library's
`ReferenceAmplitude.wave_norm_comparable_to_late_clock`, which recomputes `|k|` from the
first bound. The private helper `sqrt_clock_bounds_at_crossing` is copied verbatim.
Namespace `TorusEuler.Paper.Lib.S2b`.
-/

open Set

namespace TorusEuler.Paper.Lib.S2b

open ReferenceRiccati ReferencePropagator ReferenceAmplitude
open AmplificationCrossing MovingAmplitude MovingWaveVector

/-- Copy of the private `ReferenceAmplitude.sqrt_clock_bounds_at_crossing`. -/
theorem sqrt_clock_bounds_at_crossing {ε next t : ℝ} (hε : 0 < ε) (hn : 0 < next)
    (hlo : 1 / (4 * next) ≤ x ε t) (hhi : x ε t ≤ 3 / (2 * next)) :
    (Real.sqrt (ε * next))⁻¹ / 2 ≤ Real.sqrt (x ε t / ε) ∧
      Real.sqrt (x ε t / ε) ≤ 2 * (Real.sqrt (ε * next))⁻¹ := by
  have hp := mul_pos hε hn
  have hx := x_nonneg hε.le t
  have hd : 0 ≤ x ε t / ε := div_nonneg hx hε.le
  have hlo' : (ε * next * 4)⁻¹ ≤ x ε t / ε := by
    apply (le_div_iff₀ hε).mpr
    calc
      _ = 1 / (4 * next) := by field_simp
      _ ≤ _ := hlo
  have hhi' : x ε t / ε ≤ 4 / (ε * next) := by
    apply (div_le_iff₀ hε).mpr
    calc
      _ ≤ 3 / (2 * next) := hhi
      _ ≤ (4 / (ε * next)) * ε := by
        have h := (show (3 : ℝ) / 2 ≤ 4 by norm_num)
        calc
          _ = (3 / 2) / next := by ring
          _ ≤ 4 / next := div_le_div_of_nonneg_right h hn.le
          _ = _ := by field_simp
  constructor
  · apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hd]
    refine le_trans ?_ hlo'
    rw [div_pow, inv_pow, Real.sq_sqrt hp.le]
    exact le_of_eq (by ring)
  · apply le_of_sq_le_sq _ (by positivity)
    rw [Real.sq_sqrt hd, mul_pow, inv_pow, Real.sq_sqrt hp.le]
    simpa [div_eq_mul_inv, show (2 : ℝ) ^ 2 = 4 by norm_num] using hhi'

/-- Copy of the private `ReferenceRiccati.continuous_damping_quarter`. -/
theorem continuous_damping_quarter (ε : ℝ) : Continuous (fun t => damping ε t / 4) :=
  continuous_iff_continuousAt.mpr fun t => by
    have hs := (hasDerivAt_s ε t).continuousAt
    have hx := (hasDerivAt_x ε t).continuousAt
    unfold damping
    fun_prop

/-- Copy of the private `ReferenceRiccati.continuousOn_deviation_envelope`: if
`Y = s(1 + e) - damping/4` is continuous, so is `(1 + e)cos φ = s(1 + e)`. -/
theorem continuousOn_deviation_envelope {ε : ℝ} {Y e : ℝ → ℝ}
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0)) :
    ContinuousOn (fun t => s ε t * (1 + e t)) (Ici 0) := by
  have heq : (fun t => s ε t * (1 + e t)) = fun t => Y t + damping ε t / 4 := by
    funext t
    rw [hform, referenceY]
    ring
  rw [heq]
  exact hY.add ((continuous_damping_quarter ε).continuousOn)

/-- Formula (2.14) at `τ` divided by (2.14) at `τ_m`, for `0 ≤ τ_m ≤ τ`:
`a_ref(τ)/a_ref(τ_m) = (cos φ(τ)/cos φ(τ_m))^{1/2} exp ∫_{τ_m}^τ (1 + e)cos φ`
(`sections/03_amplification.tex:946-951`), with `cos φ = s` and `a_ref = referenceV`. -/
theorem referenceV_ratio_of_amplitude {ε τm τ : ℝ} {Y e : ℝ → ℝ}
    (hamp : ∀ t ∈ Ici (0 : ℝ), referenceV Y t =
      Real.sqrt (s ε t) * Real.exp (∫ r in (0 : ℝ)..t, s ε r * (1 + e r)))
    (hc : ContinuousOn (fun t => s ε t * (1 + e t)) (Ici 0))
    (hm₀ : 0 ≤ τm) (hτ : τm ≤ τ) :
    referenceV Y τ / referenceV Y τm =
      Real.sqrt (s ε τ / s ε τm) * Real.exp (∫ t in τm..τ, s ε t * (1 + e t)) := by
  have hτ₀ : 0 ≤ τ := hm₀.trans hτ
  have hi (b : ℝ) (hb : 0 ≤ b) :
      IntervalIntegrable (fun t => s ε t * (1 + e t)) MeasureTheory.volume 0 b :=
    (hc.mono (fun _ ht => ((uIcc_of_le hb).subset ht).1)).intervalIntegrable
  have hsub := intervalIntegral.integral_interval_sub_left (hi τ hτ₀) (hi τm hm₀)
  rw [hamp τ hτ₀, hamp τm hm₀, mul_div_mul_comm, ← Real.exp_sub, hsub,
    Real.sqrt_div (s_pos ε τ).le]

/-- Copy of the private `ReferenceRiccati.s_ratio_bounds`. -/
theorem s_ratio_bounds {ε a b : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (ha : a ∈ Icc (2 / ε) (3 / ε)) (hab : a ≤ b) :
    (ε * x ε b)⁻¹ ≤ s ε b / s ε a ∧ s ε b / s ε a ≤ 9 / (ε * x ε b) := by
  obtain ⟨halow, hahigh⟩ := x_bounds_of_turning_time hε ha
  have ha₀ : 0 ≤ a := (by positivity : 0 ≤ 2 / ε).trans ha.1
  have ha₁ : 1 ≤ x ε a := ((le_div_iff₀ hε).mpr (by linarith)).trans halow
  have habx : x ε a ≤ x ε b := by
    unfold x
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha₀ hab 2) hε.le
    linarith
  have hb₁ := ha₁.trans habx
  have hapos : 0 < x ε a := zero_lt_one.trans_le ha₁
  have hbpos : 0 < x ε b := zero_lt_one.trans_le hb₁
  have hsainv_lo : x ε a ≤ (s ε a)⁻¹ := by
    simpa using inv_anti₀ (s_pos ε a) (s_le_inv_x hapos)
  have hsainv_hi : (s ε a)⁻¹ ≤ 2 * x ε a := by
    simpa using inv_anti₀ (by positivity : 0 < (2 * x ε a)⁻¹) (inv_two_mul_x_le_s ha₁)
  rw [div_eq_mul_inv]
  constructor
  · calc
      _ = ((2 * x ε b)⁻¹) * (2 / ε) := by ring
      _ ≤ _ := mul_le_mul (inv_two_mul_x_le_s hb₁) (halow.trans hsainv_lo)
        (by positivity) (s_pos ε b).le
  · have has : (s ε a)⁻¹ ≤ 9 / ε := by
      apply hsainv_hi.trans
      calc
        2 * x ε a ≤ 2 * (9 / (2 * ε)) := mul_le_mul_of_nonneg_left hahigh (by norm_num)
        _ = 9 / ε := by ring
    calc
      _ ≤ (x ε b)⁻¹ * (9 / ε) :=
        mul_le_mul (s_le_inv_x hbpos) has (inv_nonneg.mpr (s_pos ε a).le)
          (inv_nonneg.mpr hbpos.le)
      _ = 9 / (ε * x ε b) := by ring

/-- Copy of `ReferenceRiccati.referenceV_late_ratio_bounds` with the ratio
`a_ref(τ)/a_ref(τ_m)` given by `hratio` (obtained from (2.14)) in place of the library's
`referenceV_ratio_decomposition`: after the peak, `a_ref(τ)/a_ref(τ_m)` is comparable to
`(εx(τ))^{-1/2}`, because the integral in the ratio lies in `[0, 2]`
(`sections/03_amplification.tex:946-953`). -/
theorem referenceV_late_ratio_bounds_of_ratio {ε τm τ : ℝ} {Y e : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : τm ∈ Icc (2 / ε) (3 / ε)) (hτ : τm ≤ τ)
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0))
    (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hratio : referenceV Y τ / referenceV Y τm =
      Real.sqrt (s ε τ / s ε τm) * Real.exp (∫ t in τm..τ, s ε t * (1 + e t))) :
    (Real.sqrt (ε * x ε τ))⁻¹ ≤ referenceV Y τ / referenceV Y τm ∧
      referenceV Y τ / referenceV Y τm ≤ 3 * Real.exp 2 * (Real.sqrt (ε * x ε τ))⁻¹ := by
  rw [hratio]
  obtain ⟨his₀, his₂⟩ := reference_tail_integral_bounds hε hε₁ hm.1 hτ hform hY he
  obtain ⟨hlo, hhi⟩ := s_ratio_bounds hε hε₁ hm hτ
  have hlo' := Real.sqrt_le_sqrt hlo
  rw [Real.sqrt_inv] at hlo'
  have hhi' := Real.sqrt_le_sqrt hhi
  have hsqrt9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 9), hsqrt9] at hhi'
  constructor
  · calc
      _ ≤ Real.sqrt (s ε τ / s ε τm) := hlo'
      _ = Real.sqrt (s ε τ / s ε τm) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp his₀) (Real.sqrt_nonneg _)
  · calc
      _ ≤ (3 / Real.sqrt (ε * x ε τ)) * Real.exp 2 :=
        mul_le_mul hhi' (Real.exp_le_exp.mpr his₂) (Real.exp_pos _).le
          (by positivity)
      _ = _ := by ring

/-- Copy of `ReferenceRiccati.referenceV_late_strength_bounds` with the hypothesis `hratio`
of `referenceV_late_ratio_bounds_of_ratio`. -/
theorem referenceV_late_strength_bounds_of_ratio {ε τm τ : ℝ} {Y e : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : τm ∈ Icc (2 / ε) (3 / ε)) (hτ : τm ≤ τ)
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0))
    (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hratio : referenceV Y τ / referenceV Y τm =
      Real.sqrt (s ε τ / s ε τm) * Real.exp (∫ t in τm..τ, s ε t * (1 + e t))) :
    Real.sqrt (x ε τ / ε) ≤ x ε τ * (referenceV Y τ / referenceV Y τm) ∧
      x ε τ * (referenceV Y τ / referenceV Y τm) ≤ 3 * Real.exp 2 * Real.sqrt (x ε τ / ε) := by
  have hm₀ : 0 < τm := (by positivity : 0 < 2 / ε).trans_le hm.1
  have hτ₀ : 0 < τ := hm₀.trans_le hτ
  have hx : 0 < x ε τ := by unfold x; positivity
  obtain ⟨hlow, hhigh⟩ := referenceV_late_ratio_bounds_of_ratio hε hε₁ hm hτ hform hY he hratio
  have heq : x ε τ * (Real.sqrt (ε * x ε τ))⁻¹ = Real.sqrt (x ε τ / ε) := by
    rw [Real.sqrt_mul hε.le, Real.sqrt_div hx.le]
    field_simp [(Real.sqrt_pos.2 hε).ne', (Real.sqrt_pos.2 hx).ne']
    exact (Real.sq_sqrt hx.le).symm
  constructor
  · rw [← heq]
    exact mul_le_mul_of_nonneg_left hlow hx.le
  · calc
      _ ≤ x ε τ * (3 * Real.exp 2 * (Real.sqrt (ε * x ε τ))⁻¹) :=
        mul_le_mul_of_nonneg_left hhigh hx.le
      _ = 3 * Real.exp 2 * (x ε τ * (Real.sqrt (ε * x ε τ))⁻¹) := by ring
      _ = _ := by rw [heq]

/-- Copy of `ReferenceRiccati.amplitude_late_strength_bounds_of_reference_comparison` with
the hypothesis `hratio` of `referenceV_late_ratio_bounds_of_ratio`: the late strength
estimate of Proposition 2.8 before inserting the bounds on the clock at a crossing
(`sections/03_amplification.tex:940-957`). -/
theorem amplitude_late_strength_bounds_of_ratio
    {ε T τm τ M c C kmin kmax k : ℝ} {Y e A : ℝ → ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hm : τm ∈ Icc (2 / ε) (3 / ε))
    (hτm : τm ≤ τ) (hτT : τ ≤ T)
    (hform : Y = referenceY ε e) (hY : ContinuousOn Y (Ici 0))
    (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hratio : referenceV Y τ / referenceV Y τm =
      Real.sqrt (s ε τ / s ε τm) * Real.exp (∫ t in τm..τ, s ε t * (1 + e t)))
    (hc : 0 < c) (hC : 0 < C) (hkmin : 0 ≤ kmin) (hkmax : 0 ≤ kmax)
    (hpeak : ∀ t ∈ Icc 0 T, referenceV Y t ≤ referenceV Y τm)
    (hcompare : ∀ t ∈ Icc 0 T,
      c * referenceV Y t ≤ A t ∧ A t ≤ C * referenceV Y t)
    (hmax : IsGreatest (A '' Icc 0 T) M)
    (hklo : kmin * x ε τ ≤ k) (hkhi : k ≤ kmax * x ε τ) :
    kmin * (c / C) * Real.sqrt (x ε τ / ε) ≤ k * (A τ / M) ∧
      k * (A τ / M) ≤ kmax * (C / c) * (3 * Real.exp 2) * Real.sqrt (x ε τ / ε) := by
  have hm₀ : 0 ≤ τm := (by positivity : 0 ≤ 2 / ε).trans hm.1
  have hτ : τ ∈ Icc 0 T := ⟨hm₀.trans hτm, hτT⟩
  have hx := x_nonneg hε.le τ
  obtain ⟨hrlo, hrhi⟩ := amplitude_ratio_of_reference_comparison hc hC
    ⟨hm₀, hτm.trans hτT⟩ hτ hpeak hcompare hmax
  have hrpos : 0 ≤ A τ / M :=
    (by positivity [referenceV_pos Y τ, referenceV_pos Y τm] :
      0 ≤ c / C * (referenceV Y τ / referenceV Y τm)).trans hrlo
  obtain ⟨hslo, hshi⟩ :=
    referenceV_late_strength_bounds_of_ratio hε hε₁ hm hτm hform hY he hratio
  constructor
  · calc
      _ ≤ kmin * (c / C) * (x ε τ * (referenceV Y τ / referenceV Y τm)) :=
        mul_le_mul_of_nonneg_left hslo (by positivity)
      _ = (kmin * x ε τ) * (c / C * (referenceV Y τ / referenceV Y τm)) := by ring
      _ ≤ (kmin * x ε τ) * (A τ / M) :=
        mul_le_mul_of_nonneg_left hrlo (mul_nonneg hkmin hx)
      _ ≤ _ := mul_le_mul_of_nonneg_right hklo hrpos
  · calc
      _ ≤ (kmax * x ε τ) * (A τ / M) := mul_le_mul_of_nonneg_right hkhi hrpos
      _ ≤ (kmax * x ε τ) * (C / c * (referenceV Y τ / referenceV Y τm)) :=
        mul_le_mul_of_nonneg_left hrhi (mul_nonneg hkmax hx)
      _ = kmax * (C / c) * (x ε τ * (referenceV Y τ / referenceV Y τm)) := by ring
      _ ≤ kmax * (C / c) * (3 * Real.exp 2 * Real.sqrt (x ε τ / ε)) :=
        mul_le_mul_of_nonneg_left hshi (by positivity)
      _ = _ := by ring

/-- The second bound of (2.10) with `CT^Cδ ≤ 1/2`, `|‖k‖²cos²φ/λ² - 1| ≤ 1/2` (here
`cos φ = s` and `K = ‖k(τ)‖`), makes `‖k‖/λ` comparable to the clock `x = tan φ` for
`τ ≥ 2/ε`: "`|k|` is comparable to `λ/cos φ`, by (2.10)"
(`sections/03_amplification.tex:954-955`), with `x ≤ 1/cos φ ≤ 2x`. -/
theorem wave_norm_comparable_of_norm_bound {ε t scale K : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (ht : 2 / ε ≤ t) (hscale : 0 < scale) (hK : 0 ≤ K)
    (hk : |K ^ 2 * s ε t ^ 2 / scale ^ 2 - 1| ≤ 1 / 2) :
    x ε t / 2 ≤ K / scale ∧ K / scale ≤ 3 * x ε t := by
  have ht₂ : 2 ≤ t := (show (2 : ℝ) ≤ 2 / ε by
    apply (le_div_iff₀ hε).mpr
    linarith).trans ht
  have hεt : 2 ≤ ε * t := by
    rw [mul_comm]
    exact (div_le_iff₀ hε).mp ht
  have hprod : 2 * 2 ≤ (ε * t) * t :=
    mul_le_mul hεt ht₂ (by norm_num) (by linarith)
  have hx : 1 ≤ x ε t := by
    unfold x
    nlinarith
  have hx₀ : 0 < x ε t := zero_lt_one.trans_le hx
  have hs := s_pos ε t
  have hsx : s ε t * x ε t ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (s_le_inv_x hx₀) hx₀.le
    rwa [inv_mul_cancel₀ hx₀.ne'] at h
  have hsx2 : 1 ≤ 2 * x ε t * s ε t := by
    have h := mul_le_mul_of_nonneg_left (inv_two_mul_x_le_s hx) (by linarith : 0 ≤ 2 * x ε t)
    rwa [mul_inv_cancel₀ (by linarith : 2 * x ε t ≠ 0)] at h
  have hq0 : 0 ≤ K / scale := div_nonneg hK hscale.le
  have hqs : (K / scale) ^ 2 * s ε t ^ 2 = K ^ 2 * s ε t ^ 2 / scale ^ 2 := by
    rw [div_pow]
    ring
  rw [← hqs] at hk
  obtain ⟨hlo, hhi⟩ := abs_le.mp hk
  have hp : 0 ≤ K / scale * s ε t := mul_nonneg hq0 hs.le
  have hsq : (K / scale) ^ 2 * s ε t ^ 2 = (K / scale * s ε t) ^ 2 := by ring
  rw [hsq] at hlo hhi
  refine ⟨not_lt.mp fun hcon => ?_, not_lt.mp fun hcon => ?_⟩
  · have h1 : K / scale * s ε t < x ε t / 2 * s ε t := mul_lt_mul_of_pos_right hcon hs
    have h2 : K / scale * s ε t < 1 / 2 := by linarith
    nlinarith
  · have h1 : 3 * x ε t * s ε t < K / scale * s ε t := mul_lt_mul_of_pos_right hcon hs
    have h2 : 3 / 2 < K / scale * s ε t := by linarith
    nlinarith

/-- Copy of `ReferenceAmplitude.growing_amplitude_crossing_strength_and_gain` (content of
Proposition 2.8) in which the facts of Lemma 2.5 are hypotheses: `2/ε ≤ τ_m ≤ 3/ε` for the
zero `τ_m` of `Y` (`hm`), the maximum of `a_ref` at `τ_m` (`hpeak`), the gain (`hgain`,
the integral form of `log a_ref(τ_m) ≥ ε^{-1/2} - 1`), `Y ≤ 1` (`hcap`), the form (2.13)
with `0 ≤ e ≤ ε/8` (`hform`, `hdev`) and formula (2.14) (`hamp`, with `cos φ = s`). From
(2.18) (`hlog`), the second bound of (2.10) (`hk`) and the bounds of the ratio
`ρ = η₊/ν₊` (`hcomp`): a crossing in `(τ_m, 2(εε₊)^{-1/2})`, the bounds (2.23) at every
crossing in `[τ_m, 2(εε₊)^{-1/2}]`, and (2.24) (`sections/03_amplification.tex:915-969`).
The ratio `a_ref(τ)/a_ref(τ_m)` comes from (2.14) by `referenceV_ratio_of_amplitude`. -/
theorem crossing_strength_and_gain_of_reference
    {ε next T scale τm : ℝ} {Y ρ e' : ℝ → ℝ} {k a : ℝ → Space}
    (hε : 0 < ε) (hεsmall : 2 * ε ≤ 1) (hn : 0 < next) (hnsmall : next ≤ ε / 32)
    (hT : crossingHorizon ε next ≤ T) (hscale : 0 < scale)
    (hYc : ContinuousOn Y (Ici 0))
    (hm : τm ∈ Icc (2 / ε) (3 / ε))
    (hpeak : ∀ t ∈ Ici 0, referenceV Y t ≤ referenceV Y τm)
    (hgain : (Real.sqrt ε)⁻¹ - 1 ≤ ∫ t in (0 : ℝ)..τm, Y t)
    (hcap : ∀ t ∈ Ici 0, Y t ≤ 1)
    (hform : Y = referenceY ε e') (hdev : MapsTo e' (Ici 0) (Icc 0 (ε / 8)))
    (hamp : ∀ t ∈ Ici (0 : ℝ), referenceV Y t =
      Real.sqrt (s ε t) * Real.exp (∫ r in (0 : ℝ)..t, s ε r * (1 + e' r)))
    (ha : ContinuousOn a (Icc 0 T)) (ha₀ : ∀ r ∈ Icc 0 T, a r ≠ 0)
    (hlog : ∀ r ∈ Icc 0 T, |Real.log (‖a r‖ / growingFactor Y r)| ≤ ε)
    (hk : ∀ r ∈ Icc (2 / ε) T, |‖k r‖ ^ 2 * s ε r ^ 2 / scale ^ 2 - 1| ≤ 1 / 2)
    (hρ : ContinuousOn ρ (Icc 0 T))
    (hcomp : ∀ r ∈ Icc (Real.sqrt 2 / ε) T, s ε r / 2 ≤ ρ r ∧ ρ r ≤ 3 / 2 * s ε r) :
    ∃ peak : ℝ, IsGreatest ((fun r => ‖a r‖) '' Icc 0 T) peak ∧
      (∃ τ ∈ Ioo τm (crossingHorizon ε next), ρ τ = next) ∧
      (∀ τ ∈ Icc τm (crossingHorizon ε next), ρ τ = next →
        (Real.exp (-1) / 4) * (Real.sqrt (ε * next))⁻¹ ≤
          ‖a τ‖ * ‖k τ‖ / (scale * peak) ∧
        ‖a τ‖ * ‖k τ‖ / (scale * peak) ≤
          18 * Real.exp 3 * (Real.sqrt (ε * next))⁻¹) ∧
      (∀ τ ∈ Icc 0 1, ‖a τ‖ ≤ Real.exp (3 - (Real.sqrt ε)⁻¹) * peak) := by
  have hε₁ : ε ≤ 1 := by linarith
  have hmh : τm ≤ crossingHorizon ε next := (hm.2.trans
    (div_le_div_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 8) hε.le)).trans
      (eight_div_le_crossingHorizon hε hn hnsmall)
  have htm : τm ∈ Icc 0 T :=
    ⟨(by positivity : 0 ≤ 2 / ε).trans hm.1, hmh.trans hT⟩
  let A (r : ℝ) := ‖a r‖
  have hcompare (r : ℝ) (hr : r ∈ Icc 0 T) :
      Real.exp (-ε) * referenceV Y r ≤ A r ∧ A r ≤ Real.exp ε * referenceV Y r :=
    reference_comparison_of_growing_log_bound (norm_pos_iff.mpr (ha₀ r hr)) (hlog r hr)
  obtain ⟨τa, hta, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨τm, htm⟩ ha.norm
  let peak := A τa
  have hgreat : IsGreatest (A '' Icc 0 T) peak := by
    refine ⟨mem_image_of_mem A hta, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact isMaxOn_iff.mp hmax r hr
  obtain ⟨hcross, hcrossBounds⟩ :=
    exists_crossing_of_couplingRatio hε hε₁ hn hnsmall hm hT
      (hρ.mono (Icc_subset_Icc_left htm.1)) hcomp
  refine ⟨peak, hgreat, hcross, ?_, ?_⟩
  · intro τ hτ hρτ
    have hτT : τ ≤ T := hτ.2.trans hT
    have hlate : τ ∈ Icc (2 / ε) T := ⟨hm.1.trans hτ.1, hτT⟩
    obtain ⟨hlo, hhi⟩ := hcrossBounds τ ⟨hτ.1, hτT⟩ hρτ
    obtain ⟨hclocklo, hclockhi⟩ := sqrt_clock_bounds_at_crossing hε hn hlo hhi
    obtain ⟨hklo, hkhi⟩ := wave_norm_comparable_of_norm_bound hε hε₁ hlate.1 hscale
      (norm_nonneg _) (hk τ hlate)
    rw [show x ε τ / 2 = (1 / 2) * x ε τ by ring] at hklo
    -- (2.14) at `τ` divided by (2.14) at `τ_m`.
    have hratio := referenceV_ratio_of_amplitude hamp
      (continuousOn_deviation_envelope hform hYc) htm.1 hτ.1
    obtain ⟨hslo, hshi⟩ := amplitude_late_strength_bounds_of_ratio
      hε hε₁ hm hτ.1 hτT hform hYc hdev hratio (Real.exp_pos _) (Real.exp_pos _)
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (3 : ℝ))
      (fun r hr => hpeak r hr.1) hcompare hgreat hklo hkhi
    have hloexp : Real.exp (-1) ≤ Real.exp (-ε) / Real.exp ε := by
      rw [← Real.exp_sub]
      exact Real.exp_le_exp.mpr (by linarith)
    have hhiexp : Real.exp ε / Real.exp (-ε) ≤ Real.exp 1 := by
      rw [← Real.exp_sub]
      exact Real.exp_le_exp.mpr (by linarith)
    have hstrength :
        (‖k τ‖ / scale) * (A τ / peak) = ‖a τ‖ * ‖k τ‖ / (scale * peak) := by
      rw [div_mul_div_comm, mul_comm ‖k τ‖]
    rw [hstrength] at hslo hshi
    constructor
    · calc
        _ = (1 / 2) * Real.exp (-1) * ((Real.sqrt (ε * next))⁻¹ / 2) := by ring
        _ ≤ (1 / 2) * (Real.exp (-ε) / Real.exp ε) * Real.sqrt (x ε τ / ε) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hloexp (by norm_num)) hclocklo
            (by positivity) (by positivity)
        _ ≤ _ := hslo
    · calc
        _ ≤ 3 * (Real.exp ε / Real.exp (-ε)) * (3 * Real.exp 2) *
            Real.sqrt (x ε τ / ε) := hshi
        _ ≤ 3 * Real.exp 1 * (3 * Real.exp 2) * (2 * (Real.sqrt (ε * next))⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hhiexp (by norm_num)) (by positivity)) hclockhi
            (by positivity) (by positivity)
        _ = _ := by
          rw [show Real.exp (3 : ℝ) = Real.exp 1 * Real.exp 2 by rw [← Real.exp_add]; norm_num]
          ring
  · intro τ hτ
    have hT₁ : 1 ≤ T :=
      ((le_div_iff₀ hε).mpr (by linarith : 1 * ε ≤ 8)).trans <|
        (eight_div_le_crossingHorizon hε hn hnsmall).trans hT
    exact (amplitude_initial_window_of_reference_comparison hεsmall hYc hcap hgain hτ
      (hτ.2.trans hT₁) htm hcompare).trans
      (mul_le_mul_of_nonneg_left (hgreat.2 (mem_image_of_mem A htm)) (by positivity))

end TorusEuler.Paper.Lib.S2b
