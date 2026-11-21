import TorusEuler.Paper.Proofs.S2b.Library.Crossing

/-! # Conditional proof of Proposition 2.8

`TorusEuler.Paper.Proof.proposition_2_8_of`, following the proof of
Proposition 2.8 (`cc:prop:finite-return`) in
`paper/craik_criminale_rewrite/sections/03_amplification.tex:915-969`.
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper

open MovingWaveVector MovingAmplitude ReferenceRiccati ReferenceAmplitude Lib.S2b

/-- Proof of **Proposition 2.8** (`cc:prop:finite-return`) following
`sections/03_amplification.tex:915-969`, in normalized time `τ` (`t = t₀ + τ/r`).

* `h2_5` (Lemma 2.5): the reference solution `Y` of (2.12) (existence clause) and its
  uniqueness; the unique zero `τ_m` with `2 ≤ ετ_m ≤ 3` (`:916`), which is also the zero of
  every solution of (2.12) (the first two conclusions); the maximum of `a_ref` at `τ_m`
  (`:943`); the gain `log a_ref(τ_m) ≥ ε^{-1/2} - 1` and `Y ≤ 1` (`:963-965`, for (2.24));
  formula (2.14), divided at `τ` and at `τ_m` to give the ratio `a_ref(τ)/a_ref(τ_m)`
  (`:946-951`, `Lib.S2b.referenceV_ratio_of_amplitude`); and the form (2.13) with
  `0 ≤ e ≤ ε/8`, which bounds the integral in that ratio by `2` (`:952-953`) and gives the
  continuity of `(1 + e)cos φ = Y + ετ sin 2φ/4` used to split the integral of (2.14).
* `h2_7` (Lemma 2.7): `ν₊ ≥ εν/2 > 0` (so `η₊/ν₊` is continuous on `[0, T]`) and the
  second bound of (2.19), `|(η₊/ν₊)/cos φ - 1| ≤ 1/2` for `√2/ε ≤ τ ≤ T`, which gives
  `cos φ/2 ≤ η₊/ν₊ ≤ 3cos φ/2` (`:920-928`) and hence the crossing by continuity.
* `h2_6` (Lemma 2.6): (2.18), `|log(|a|/a_ref)| ≤ ε` (`:940`, `:965`), and `|a| ≥ α₂ > 0`
  ((2.17)).
* `h2_4` (Lemma 2.4): the second bound of (2.10) with `CT^Cδ ≤ 1/2`,
  `||k|²cos²φ/λ² - 1| ≤ 1/2`, i.e. "`|k|` is comparable to `λ/cos φ`, by (2.10)"
  (`:954-955`, `Lib.S2b.wave_norm_comparable_of_norm_bound`); and (2.11), `ζ₃ ≥ 1/2`,
  hence `k ≠ 0` (continuity of `E₁,₊ = k/|k|` in `ν₊`, `η₊`).

The rest of the argument (the bounds on `tan φ` at `τ_m` and at a crossing, the comparison
of `|a(τ)|/max|a|` with `a_ref(τ)/a_ref(τ_m)`, and (2.24)) is
`Lib.S2b.crossing_strength_and_gain_of_reference`, a copy of the library carrier of this
proposition (`ReferenceAmplitude.growing_amplitude_crossing_strength_and_gain`) that takes
the facts of Lemma 2.5 and Lemma 2.4 listed above as hypotheses, applied to `e = E(t₀ + ·/r)`,
`k(t₀ + ·/r)`, `a(t₀ + ·/r)` and the ratio `η₊/ν₊`.
Equations: (2.10)-(2.14), (2.17)-(2.19), (2.23), (2.24). -/
theorem Proof.proposition_2_8_of (h2_4 : Statement.lemma_2_4) (h2_5 : Statement.lemma_2_5)
    (h2_6 : Statement.lemma_2_6) (h2_7 : Statement.lemma_2_7) :
    Statement.proposition_2_8 := by
  obtain ⟨C4, p4, N4, h4⟩ := h2_4
  obtain ⟨C6, p6, N6, h6⟩ := h2_6
  obtain ⟨N7, h7⟩ := h2_7
  refine ⟨max (max N4 N6) (max N7 240), ?_⟩
  intro C₀ hN I t₀ T lam εplus w k a hT hclock hsmall hk ha ha₀ hn hnsmall hH ε H ratioPlus
    σplus
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN4, hN6⟩, hN7, h240⟩ := hN
  obtain ⟨hεpos, hεhalf, -⟩ :=
    normalized_facts w (basis_orthonormal w w.activation) hT h240 hsmall
  have hε1 : w.ratio ≤ 1 := by linarith
  -- Lemma 2.5: the reference solution `Y`, its zero `τ_m ∈ [2/ε, 3/ε]`, the maximum of
  -- `a_ref` at `τ_m`, the gain, `|Y| ≤ 1`, the form (2.13) and formula (2.14).
  obtain ⟨⟨Y, hYs⟩, h5⟩ := h2_5 hεpos hε1
  obtain ⟨hYuniq, hYb, e, he, hform, hamp, τm, hzero, hτm2, hτm3, -, -, hmax, hgain⟩ :=
    h5 Y hYs
  obtain ⟨-, hY⟩ := referenceSlope_iff.1 hYs
  have hm : τm ∈ Icc (2 / ε) (3 / ε) :=
    ⟨(div_le_iff₀ hεpos).mpr (by linarith [mul_comm ε τm]),
      (le_div_iff₀ hεpos).mpr (by linarith [mul_comm ε τm])⟩
  have hgain' : (Real.sqrt ε)⁻¹ - 1 ≤ ∫ t in (0 : ℝ)..τm, Y t := by
    rwa [referenceAmplitude, Real.log_exp] at hgain
  have hdev : MapsTo (deviation ε Y) (Ici 0) (Icc 0 (ε / 8)) := by
    intro τ hτ
    rw [deviation_eq_of_form (hform τ hτ)]
    exact he τ hτ
  -- (2.14) in the library variables: `cos φ = s`, `a_ref = referenceV`, and the function
  -- `e` of (2.13) is the library deviation of `Y` on `τ ≥ 0`.
  have hamp' : ∀ t ∈ Ici (0 : ℝ), referenceV Y t = Real.sqrt (s ε t) *
      Real.exp (∫ r in (0 : ℝ)..t, s ε r * (1 + deviation ε Y r)) := by
    intro t ht
    have h := hamp t ht
    simp only [cos_referenceAngle] at h
    change referenceV Y t = _ at h
    rw [h]
    congr 2
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    have hr0 : r ∈ Ici (0 : ℝ) := by
      rw [uIcc_of_le ht] at hr
      exact hr.1
    show (1 + e r) * s ε r = s ε r * (1 + deviation ε Y r)
    rw [deviation_eq_of_form (hform r hr0), mul_comm]
  -- Lemma 2.4: the second bound of (2.10) with `CT^Cδ ≤ 1/2`, and (2.11), so `k ≠ 0`.
  obtain ⟨h4half, -, h4k, h4z, -⟩ := h4 hN4 w hT hclock hsmall hk
  have hkne (r : ℝ) (hr : r ∈ Icc 0 T) : k (w.clock r) ≠ 0 := by
    exact ne_zero_of_zeta_two_pos w (lam := lam) (lt_of_lt_of_le (by norm_num) (h4z r hr).1)
  have hsub2 : Icc (2 / ε) T ⊆ Icc 0 T :=
    Icc_subset_Icc_left (div_nonneg (by norm_num) hεpos.le)
  have hk2 (r : ℝ) (hr : r ∈ Icc (2 / ε) T) :
      |‖(k ∘ w.clock) r‖ ^ 2 * s ε r ^ 2 / lam ^ 2 - 1| ≤ 1 / 2 := by
    have h := (h4k r (hsub2 hr)).trans h4half
    rw [cos_referenceAngle] at h
    exact h
  -- Lemma 2.6: `|a| ≥ α₂ > 0` and (2.18).
  obtain ⟨h6pos, -, h6norm, h6log, -⟩ := h6 hN6 w hT hclock hsmall hk ha ha₀
  have hane (r : ℝ) (hr : r ∈ Icc 0 T) : a (w.clock r) ≠ 0 :=
    norm_pos_iff.mp ((h6pos r hr).trans_le (h6norm r hr).1)
  -- Lemma 2.7: `ν₊ ≥ εν/2 > 0` and the second bound of (2.19).
  obtain ⟨h7nu, h7late⟩ := h7 hN7 w hT hclock hsmall hk ha ha₀
  have hνpos (r : ℝ) (hr : r ∈ Icc 0 T) : 0 < w.physicalNu k a (w.clock r) :=
    (by have := w.first_coupling_positive; positivity : 0 < w.ratio * w.firstCoupling / 2).trans_le
      (h7nu r hr)
  obtain ⟨hNuC, hEtaC⟩ := continuousOn_physicalCouplings w hclock
    (HasDerivWithinAt.continuousOn hk.2.2) (HasDerivWithinAt.continuousOn ha.1) hkne hane
  have hρ : ContinuousOn ratioPlus (Icc 0 T) :=
    hEtaC.div hNuC (fun r hr => (hνpos r hr).ne')
  have hcomp (r : ℝ) (hr : r ∈ Icc (Real.sqrt 2 / ε) T) :
      s ε r / 2 ≤ ratioPlus r ∧ ratioPlus r ≤ 3 / 2 * s ε r := by
    have hr' : r ∈ Icc 0 T :=
      ⟨(div_nonneg (Real.sqrt_nonneg _) hεpos.le).trans hr.1, hr.2⟩
    have h := (h7late r hr' hr.1).2
    rw [cos_referenceAngle] at h
    obtain ⟨hlo, hhi⟩ := abs_le.mp h
    have hs := s_pos ε r
    have hl : 1 / 2 ≤ ratioPlus r / s ε r := by
      change 1 / 2 ≤ w.physicalEta k a (w.clock r) / w.physicalNu k a (w.clock r) / s ε r
      linarith only [hlo]
    have hh : ratioPlus r / s ε r ≤ 3 / 2 := by
      change w.physicalEta k a (w.clock r) / w.physicalNu k a (w.clock r) / s ε r ≤ 3 / 2
      linarith only [hhi]
    exact ⟨((le_div_iff₀ hs).mp hl).trans_eq' (by ring), (div_le_iff₀ hs).mp hh⟩
  -- The library carrier of Proposition 2.8 in normalized time.
  obtain ⟨peak, hpeak, hexists, hstrength, hgain24⟩ :=
    crossing_strength_and_gain_of_reference (k := k ∘ w.clock)
      (a := a ∘ w.clock) (Y := Y) (ρ := ratioPlus) (scale := lam) hεpos
      (by linarith) hn hnsmall hH hk.1 (HasDerivWithinAt.continuousOn hY) hm hmax hgain'
      (fun t ht => (abs_le.mp (hYb t ht)).2) (referenceY_deviation ε Y).symm hdev hamp'
      (continuousOn_comp_clock w hclock (HasDerivWithinAt.continuousOn ha.1)) hane
      (fun r hr => h6log Y hYs r hr) hk2 hρ hcomp
  refine ⟨τm, ?_, hm.1, ?_, peak, hpeak, hstrength, hgain24⟩
  · -- `τ_m` is the zero of every solution of (2.12).
    intro Z hZ τ hτ
    rw [← hYuniq Z hZ hτ]
    exact hzero τ hτ
  · obtain ⟨τ, hτ, hρτ⟩ := hexists
    exact ⟨τ, Ioo_subset_Icc_self hτ, hρτ⟩

end TorusEuler.Paper
