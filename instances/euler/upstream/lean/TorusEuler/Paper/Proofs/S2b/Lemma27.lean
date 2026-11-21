import TorusEuler.Paper.Proofs.S2b.Library.Couplings

/-! # Conditional proof of Lemma 2.7

`TorusEuler.Paper.Proof.lemma_2_7_of`, following the proof of Lemma 2.7
(`cc:lem:new-wave-couplings`) in
`paper/craik_criminale_rewrite/sections/03_amplification.tex:735-872`.
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper

open MovingWaveVector MovingAmplitude ReferenceRiccati ReferenceAmplitude Lib.S2b

/-- Proof of **Lemma 2.7** (`cc:lem:new-wave-couplings`) following
`sections/03_amplification.tex:735-872`, in normalized time `τ` (`t = t₀ + τ/r`).

The algebra of the proof, the rational formulas (2.20)-(2.21) for `ν₊/ν` and `η₊/ν` in
`q = α₁/α₂`, `z`, `n`, `ζ`, the reference values (2.22) and the perturbation estimate
(`:744-860`), is the library lemma `GrowingCoupling.normalized_couplings_sub_reference_le`;
the conclusions from the reference values (`:832-871`) are
`Lib.S2b.coupling_conclusions_of_polynomial_budget_of_pos`, a copy of
`GrowingCoupling.coupling_conclusions_of_polynomial_budget` that takes `Y > 0` on
`ετ ≤ √2` as a hypothesis. The cited results enter as follows.

* `h2_5` (Lemma 2.5): the reference solution `Y` of (2.12) (existence clause); `|Y| ≤ 1`,
  which the text uses implicitly in the bound `CT²` on the numerators (`:855-856`, where
  `q` is close to `-Y`), an argument of `normalized_couplings_sub_reference_le`; the form
  (2.13) ("write `Y = (1+e-u)cos φ`", `:802-803`, for the reference values (2.22)) with
  `0 ≤ e ≤ ε/8` (late range, `:832-838`), passed as the deviation bounds of the library
  form of `Y`; and the sign clause: `Y > 0` before its zero `τ_m`, with `ετ_m ≥ 2`. Since
  `√2/ε < 2/ε ≤ τ_m`, this gives `Y > 0` for `ετ ≤ √2` ("hence `Y > 0` by Lemma 2.5",
  `:842-843`), the hypothesis `hpos` of the copy.
* `h2_6` (Lemma 2.6): `α₂ > 0` and the first bound of (2.17), `|α₁/α₂ + Y| ≤ CT^Cδ`,
  i.e. "`q` differs from `-Y` by at most `CT^Cδ`" (`:852-853`).
* `h2_4` (Lemma 2.4): the first bound of (2.10), "`ζ` differs from `ζ₀` by at most
  `CT^Cδ`" (`:850`), and the bound `|σ_p/σ - 1| ≤ 2Tδ` exported from its proof
  (`:302-309`), which enters the coefficient `f₂` (`:751`, "the coefficients differ from
  their reference values by at most `CTδ`", `:849-850`). The text uses the bounds
  `ζ₃ ≥ 1/2` (`:853-854`) and `|ζ| ≤ CT²` (`:855-856`) of (2.11).
  Here both are derived inside `normalized_couplings_sub_reference_le` (its step
  `coupling_coordinate_bounds`) from the first bound of (2.10), `|ζ - ζ₀| ≤ κ ≤ 1/2`, so
  the (2.11) conjunct of `h2_4` is not used.

The remaining coefficient bounds `|b_ij| ≤ δ`, `|2Sb₁₂ - 1| ≤ δ`, `|2Sb₃₂ - ε| ≤ δ`,
`|E_c|/r ≤ δ/S` and `S⁻² ≤ 2δ` are the definition (2.6) of `δ` and (2.8)
(`Lib.S2b.normalized_facts`). Equations: (2.6)-(2.8), (2.10), (2.12), (2.13), (2.17),
(2.19)-(2.22). -/
theorem Proof.lemma_2_7_of (h2_4 : Statement.lemma_2_4) (h2_5 : Statement.lemma_2_5)
    (h2_6 : Statement.lemma_2_6) : Statement.lemma_2_7 := by
  obtain ⟨C4, p4, N4, h4⟩ := h2_4
  obtain ⟨C6, p6, N6, h6⟩ := h2_6
  let Cκ : ℝ := |C4| + |C6| + 23
  let q : ℕ := p4 + p6 + 3
  let L : ℝ := 8 * (256 * Cκ + 2)
  refine ⟨max (max N4 N6) (240 + (q + 10) + Nat.ceil L), ?_⟩
  intro C₀ hN I t₀ T lam w k a hT hclock hsmall hk ha ha₀ ε ν νplus ηplus
  simp only [max_le_iff] at hN
  obtain ⟨⟨hN4, hN6⟩, hNL⟩ := hN
  have h240 : 240 ≤ C₀ := by omega
  have hCL : L ≤ (C₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil L ≤ C₀ by omega))
  have hCκ : 0 ≤ Cκ := by positivity
  obtain ⟨hεpos, hεhalf, hδ, -, hS1, -, hS2inv, -, -, -, hcoef⟩ :=
    normalized_facts w (basis_orthonormal w w.activation) hT h240 hsmall
  have hε1 : w.ratio ≤ 1 := by linarith
  -- Lemma 2.5: the reference solution `Y`, `|Y| ≤ 1`, the form (2.13) and the sign of `Y`
  -- before its zero `τ_m ≥ 2/ε`.
  obtain ⟨⟨Y, hYs⟩, h5⟩ := h2_5 hεpos hε1
  obtain ⟨-, hYb, e, he, hform, -, τm, -, hτm2, -, hpos, -⟩ := h5 Y hYs
  have hYpos : ∀ τ ∈ Icc 0 (Real.sqrt 2 / ε), 0 < Y τ := by
    intro τ hτ
    have hsqrt : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    have hlt : Real.sqrt 2 / ε < 2 / ε := div_lt_div_of_pos_right hsqrt hεpos
    have hτm : 2 / ε ≤ τm := (div_le_iff₀ hεpos).mpr (by linarith [mul_comm ε τm])
    exact hpos τ ⟨hτ.1, lt_of_le_of_lt hτ.2 (lt_of_lt_of_le hlt hτm)⟩
  have hform' : Y = referenceY ε (deviation ε Y) := (referenceY_deviation ε Y).symm
  have hdev : MapsTo (deviation ε Y) (Ici 0) (Icc 0 (ε / 8)) := by
    intro τ hτ
    rw [deviation_eq_of_form (hform τ hτ)]
    exact he τ hτ
  -- Lemma 2.4: (2.10) and the strength bound `|σ_p/σ - 1| ≤ 2Tδ`.
  obtain ⟨-, h4zeta, -, -, -, h4σ⟩ := h4 hN4 w hT hclock hsmall hk
  -- Lemma 2.6: `α₂ > 0` and the first bound of (2.17).
  obtain ⟨h6pos, h6ratio, -⟩ := h6 hN6 w hT hclock hsmall hk ha ha₀
  -- The budget `κ`.
  obtain ⟨hκ0, hκ4, hκ2, hκ6, hκhalf⟩ := coupling_budget (C4 := C4) (C6 := C6) (p4 := p4)
    (p6 := p6) hT hδ (show q ≤ C₀ by omega)
    (show 2 * Cκ ≤ (C₀ : ℝ) by
      exact (show 2 * Cκ ≤ L by simp only [L]; linarith).trans hCL) hsmall.2 hε1
  set κ := Cκ * T ^ q * w.errorSize with hκdef
  let σr (τ : ℝ) := strengthRatio (w.kp ∘ w.clock) (w.ap ∘ w.clock) τ
  let M (τ : ℝ) := strain (nbasis w τ) ((1 / w.rate) • w.B (w.clock τ))
      ((1 / w.rate) • w.E (w.clock τ)) w.shear (σr τ)
  let νn (τ : ℝ) := GrowingCoupling.normalizedNu (M τ) (k (w.clock τ)) (a (w.clock τ)) w.shear
  let ηn (τ : ℝ) := GrowingCoupling.normalizedEta (M τ) (k (w.clock τ)) (a (w.clock τ)) w.shear
  have herrors (τ : ℝ) (hτ : τ ∈ Icc 0 T) :
      |νn τ - referenceNu ε τ Y| ≤ 256 * T ^ 8 * κ + 2 * w.errorSize ∧
        |ηn τ - referenceEta ε τ Y| ≤ 256 * T ^ 8 * κ + 2 * w.errorSize := by
    have hzeta : ‖zeta w lam k τ - zetaRef w.ratio τ‖ ≤ κ :=
      ((h4zeta τ hτ).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C4) (by positivity)) hδ)).trans hκ4
    obtain ⟨hX, hQ, hZ⟩ := coordinates_close_of_zeta w hzeta
    have hU : U (nbasis w) (a ∘ w.clock) w.shear τ = -alpha w a τ 0 := by
      rw [alpha_zero, neg_neg]
    have hV : V (nbasis w) (a ∘ w.clock) τ = alpha w a τ 1 := (alpha_one w a τ).symm
    have hw : |U (nbasis w) (a ∘ w.clock) w.shear τ / V (nbasis w) (a ∘ w.clock) τ - Y τ| +
        21 * T ^ 3 * w.errorSize ≤ κ := by
      rw [hU, hV, neg_div, ← neg_add', abs_neg]
      refine le_trans ?_ hκ6
      gcongr
      exact (h6ratio Y hYs τ hτ).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C6) (by positivity)) hδ)
    have hσ : |σr τ - 1| ≤ 2 * T * w.errorSize := by
      simp only [σr, strengthRatio_clock]
      exact h4σ τ hτ
    obtain ⟨hB, hE, h12, h32⟩ := hcoef (w.clock τ) (hclock hτ)
    exact GrowingCoupling.normalized_couplings_sub_reference_le (e := nbasis w)
      (k := k ∘ w.clock) (a := a ∘ w.clock) (Y := Y) (scale := lam) (S := w.shear)
      (σratio := σr τ) ((1 / w.rate) • w.B (w.clock τ)) ((1 / w.rate) • w.E (w.clock τ))
      hT hτ hεpos.le hε1 (hYb τ hτ.1) (basis_orthonormal w (hclock hτ)) rfl hk.1 hS1
      (by rw [hV]; exact h6pos τ hτ) (by rw [real_inner_comm]; exact ha.2 _ (hclock hτ))
      hδ hκ0 hκhalf hX hQ hZ (hS2inv.trans hκ2) hw hB h12 h32 hσ hE
  obtain ⟨hν, hlate⟩ := coupling_conclusions_of_polynomial_budget_of_pos
    (C := Cκ) (p := q) (ν := νn) (η := ηn) hεpos hT hδ
    (by exact_mod_cast (show 16 ≤ C₀ by omega)) (show q + 10 ≤ C₀ by omega) hCL
    hsmall.1 hsmall.2 hform' hdev hYpos le_rfl herrors
  have hνpos : 0 < w.firstCoupling := w.first_coupling_positive
  have hcpl (τ : ℝ) (hτ : τ ∈ Icc 0 T) :
      νn τ = w.physicalNu k a (w.clock τ) / w.firstCoupling ∧
        ηn τ = w.physicalEta k a (w.clock τ) / w.firstCoupling :=
    normalizedCouplings_eq w (hclock hτ) k a
  refine ⟨fun τ hτ => ?_, fun τ hτ hlateτ => ?_⟩
  · have h := hν τ hτ
    change ε / 2 ≤ νn τ at h
    rw [(hcpl τ hτ).1, le_div_iff₀ hνpos] at h
    change ε * ν / 2 ≤ w.physicalNu k a (w.clock τ)
    linarith
  · obtain ⟨h1, h2⟩ := hlate τ hτ hlateτ
    change |νn τ - 1| ≤ ε at h1
    change |ηn τ / νn τ / s ε τ - 1| ≤ 1 / 2 at h2
    rw [(hcpl τ hτ).1] at h1
    rw [(hcpl τ hτ).1, (hcpl τ hτ).2, div_div_div_cancel_right₀ hνpos.ne'] at h2
    rw [cos_referenceAngle]
    exact ⟨h1, h2⟩

end TorusEuler.Paper
