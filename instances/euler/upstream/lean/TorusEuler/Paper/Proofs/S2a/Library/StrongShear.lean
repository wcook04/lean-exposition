import Mathlib.Analysis.ODE.Gronwall
import TorusEuler.Paper.Proofs.S2a.Library.Angle

/-! # Glue for the proof of Lemma 2.3

Generic lemmas used by `TorusEuler.Paper.Proof.lemma_2_3_of`
(`cc:lem:strong-shear`, `sections/03_amplification.tex:113-195`). None of them carries the
content of a numbered result; the citation of Lemma 2.2 enters the proof of Lemma 2.3
only through its hypothesis `h2_2`, in `TorusEuler.Paper.Proofs.S2a.Lemma23`.

* Frame entries and the model case: `entry_smul`, `modelEntries_apply`,
  `smul_modelEntries`, `strain_modelEntries`.
* The scalar identities of `sections/03_amplification.tex:167-171`: `rate_sq` (`r² = 2σν`),
  `nu_div_rate` (`ν/r = 1/(2S)`, equivalently `νS/r = 1/2`), `eta_div_rate`
  (`η/r = ε/(2S)`, equivalently `ηS/r = ε/2`).
* The strong-shear limit of the wave vector (`:177-182`): the mean value inequality
  `abs_sub_le_of_hasDerivWithinAt` (used for `σ_p = σ`), the estimate `zeta_bounds`, which
  carries out the Gronwall step of `:180-181` (`norm_le_gronwallBound_of_norm_deriv_right_le`
  for `ζ - ζ₀` in the sup norm of `ℝ × ℝ × ℝ`), so that each component of `ζ - ζ₀` is at
  most `μK(ε,T)` in absolute value, `μ = 1/(2S²)`, and `norm_le_abs_add_abs_add_abs`, which
  turns this into the Euclidean bound `|ζ - ζ₀| ≤ 3μK(ε,T)`.
* The limit of the coefficients (`:182-194`): `shearCoefficients`, the coefficients of the
  `(α₁, α₂)` system as continuous functions of `(ζ, S⁻²)` on a compact box
  (`continuousOn_shearCoefficients`), uniformly continuous there
  (`exists_coefficient_delta`); at `S⁻² = 0`, `ζ = ζ₀` they are the coefficients of (2.5)
  (`referenceSystemMatrix_eq`, the limits displayed at `sections/03_amplification.tex:185-192`,
  `2ζ₁ζ₂/m → -ετ sin 2φ` and `-1 + ζ₁(ζ₁+εζ₃)/m → -cos²φ(1 - ε tan φ)`, using
  `tan φ = ετ²/2` of (2.4)), and at `S⁻² = 1/S²` they are the entries of
  `strongShearMatrix` (`strongShearMatrix_eq`).
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S2a

open MovingWaveVector MovingAmplitude

/-- Entries of a scalar multiple. -/
theorem entry_smul (e : Fin 3 → Space) (c : ℝ) (A : Space →L[ℝ] Space) (i j : Fin 3) :
    entry e (c • A) i j = c * entry e A i j := by
  simp only [entry, smul_apply, real_inner_smul_right]

/-- Scaling the model entries. -/
theorem smul_modelEntries (c ν η : ℝ) (i j : Fin 3) :
    c * modelEntries ν η i j = modelEntries (c * ν) (c * η) i j := by
  fin_cases i <;> fin_cases j <;> simp [modelEntries]

/-- The nine entries of `modelEntries`. -/
theorem modelEntries_apply (ν η : ℝ) :
    modelEntries ν η 0 0 = 0 ∧ modelEntries ν η 0 1 = ν ∧ modelEntries ν η 0 2 = 0 ∧
    modelEntries ν η 1 0 = 0 ∧ modelEntries ν η 1 1 = 0 ∧ modelEntries ν η 1 2 = 0 ∧
    modelEntries ν η 2 0 = 0 ∧ modelEntries ν η 2 1 = η ∧ modelEntries ν η 2 2 = 0 := by
  simp [modelEntries]

/-- The entries of `strain e B E S 1` when the entries of `B` are those of the model case
and `E = 0`. -/
theorem strain_modelEntries {e : Fin 3 → Space} (he : Orthonormal ℝ e) {B E : Space →L[ℝ] Space}
    {S β γ : ℝ} (hb : ∀ i j, entry e B i j = modelEntries β γ i j)
    (hd : ∀ i j, entry e E i j = 0) :
    let A := entry e (strain e B E S 1)
    A 0 0 = 0 ∧ A 0 1 = β ∧ A 0 2 = 0 ∧ A 1 0 = S ∧ A 1 1 = 0 ∧ A 1 2 = 0 ∧
      A 2 0 = 0 ∧ A 2 1 = γ ∧ A 2 2 = 0 := by
  intro A
  simp only [A, entry_strain he, hb, hd]
  simp [modelEntries]

variable {I : Set ℝ} {t₀ : ℝ}

/-- `r² = 2σν`. -/
theorem rate_sq (w : PhysicalAmplification I t₀) :
    w.rate ^ 2 = 2 * w.initialStrength * w.firstCoupling := by
  have hσ := w.initialStrength_pos
  have hν : 0 < w.firstCoupling := w.first_coupling_positive
  simp only [PhysicalAmplification.rate, amplificationGrowthRate]
  rw [Real.sq_sqrt (by positivity)]

/-- `S > 0`. -/
theorem shear_pos (w : PhysicalAmplification I t₀) : 0 < w.shear :=
  div_pos w.initialStrength_pos w.rate_pos

/-- `ν/r = 1/(2S)`. -/
theorem nu_div_rate (w : PhysicalAmplification I t₀) :
    1 / w.rate * w.firstCoupling = 1 / (2 * w.shear) := by
  have hσ := w.initialStrength_pos
  have hr := w.rate_pos
  have h2 := rate_sq w
  simp only [PhysicalAmplification.shear]
  field_simp
  linear_combination -h2

/-- `η/r = ε/(2S)`. -/
theorem eta_div_rate (w : PhysicalAmplification I t₀) :
    1 / w.rate * w.thirdCoupling = w.ratio / (2 * w.shear) := by
  have hσ := w.initialStrength_pos
  have hr := w.rate_pos
  have hν : 0 < w.firstCoupling := w.first_coupling_positive
  have h2 := rate_sq w
  simp only [PhysicalAmplification.shear, PhysicalAmplification.ratio]
  field_simp
  linear_combination -w.thirdCoupling * h2

/-- The Euclidean norm on `ℝ³` is at most the sum of the absolute values of the
components: the public library estimate `MovingWaveVector.euclidean_error_le_sum` for the
square root of the sum of squares, written for a vector of `Vec3`. -/
theorem norm_le_abs_add_abs_add_abs (v : Vec3) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simpa only [Real.norm_eq_abs, sq_abs] using euclidean_error_le_sum (v 0) (v 1) (v 2)

/-- Mean value inequality on `[0, T]` for a real function. -/
theorem abs_sub_le_of_hasDerivWithinAt {f f' : ℝ → ℝ} {T C : ℝ}
    (hf : ∀ τ ∈ Icc 0 T, HasDerivWithinAt f (f' τ) (Icc 0 T) τ)
    (hb : ∀ τ ∈ Ico 0 T, |f' τ| ≤ C) : ∀ τ ∈ Icc 0 T, |f τ - f 0| ≤ C * τ := by
  intro τ hτ
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hf
    (fun x hx => by simpa only [Real.norm_eq_abs] using hb x hx) τ hτ
  simpa only [Real.norm_eq_abs, sub_zero] using h

/-- The constant `K(ε, T)` of Gronwall's inequality in `‖ζ - ζ₀‖_∞ ≤ μK(ε, T)`
(`zeta_bounds`): the Gronwall bound with zero initial value, Lipschitz constant `2 + ε` and
inhomogeneity `μ·εT(1 + ε)`, evaluated at `T` and divided by `μ`
(`gronwallBound_eq_zetaBound`). -/
noncomputable def zetaBound (ε T : ℝ) : ℝ :=
  ε * T * (1 + ε) / (2 + ε) * (Real.exp ((2 + ε) * T) - 1)

/-- `K(ε,T) ≥ 0`. -/
theorem zetaBound_nonneg {ε T : ℝ} (hε : 0 ≤ ε) (hT : 0 ≤ T) : 0 ≤ zetaBound ε T := by
  unfold zetaBound
  have h := Real.one_le_exp (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + ε) hT)
  exact mul_nonneg (by positivity) (by linarith)

/-- The Gronwall bound of `zeta_bounds` at time `T` is `μK(ε, T)`. -/
theorem gronwallBound_eq_zetaBound {μ ε T : ℝ} (hε : 0 ≤ ε) :
    gronwallBound 0 (2 + ε) (μ * (ε * T * (1 + ε))) T = μ * zetaBound ε T := by
  rw [gronwallBound_of_K_ne_0 (by positivity : (2 : ℝ) + ε ≠ 0)]
  simp only [zetaBound, zero_mul, zero_add]
  ring

/-- Gronwall's inequality for the wave vector in the strong-shear limit
(`sections/03_amplification.tex:177-181`). Let `z = (z₁, z₂, z₃)` solve the linear system
`z₁' = -(1+μ)z₂`, `z₂' = -εz₃`, `z₃' = εμz₂` on `[0, T]` with `z(0) = (0,0,1)` (the system
for `ζ` of Lemma 2.3 with `μ = 1/(2S²)`), and let `ζ₀ = (ετ²/2, -ετ, 1)` be the solution
of the limiting system `μ = 0` with the same initial value. The difference `d = z - ζ₀`
solves `d' = A_μ d + (A_μ - A_0)ζ₀`, where `A_μ` is the coefficient matrix, whose rows have
absolute sums at most `2 + ε` (as `μ ≤ 1`), and `(A_μ - A_0)ζ₀ = (μετ, 0, -με²τ)` has sup
norm at most `μ·εT(1 + ε)`. Since `d(0) = 0`, Gronwall's inequality
(`norm_le_gronwallBound_of_norm_deriv_right_le`, in the sup norm of `ℝ × ℝ × ℝ`) gives
`‖d‖_∞ ≤ μK(ε, T)`, that is, each component of `z - ζ₀` is at most `μK(ε, T)` in absolute
value. -/
theorem zeta_bounds {μ ε T : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hε : 0 ≤ ε)
    {z₁ z₂ z₃ : ℝ → ℝ}
    (h₁ : ∀ τ ∈ Icc 0 T, HasDerivWithinAt z₁ (-(1 + μ) * z₂ τ) (Icc 0 T) τ)
    (h₂ : ∀ τ ∈ Icc 0 T, HasDerivWithinAt z₂ (-(ε * z₃ τ)) (Icc 0 T) τ)
    (h₃ : ∀ τ ∈ Icc 0 T, HasDerivWithinAt z₃ (ε * μ * z₂ τ) (Icc 0 T) τ)
    (h01 : z₁ 0 = 0) (h02 : z₂ 0 = 0) (h03 : z₃ 0 = 1) :
    ∀ τ ∈ Icc 0 T,
      |z₁ τ - ε * τ ^ 2 / 2| ≤ μ * zetaBound ε T ∧ |z₂ τ + ε * τ| ≤ μ * zetaBound ε T ∧
        |z₃ τ - 1| ≤ μ * zetaBound ε T := by
  -- the equation `d' = A_μ d + (A_μ - A_0)ζ₀` of the difference `d = z - ζ₀`
  have hD : ∀ τ ∈ Icc 0 T, HasDerivWithinAt
      (fun s => (z₁ s - ε * s ^ 2 / 2, z₂ s + ε * s, z₃ s - 1))
      (-(1 + μ) * (z₂ τ + ε * τ) + μ * (ε * τ), -(ε * (z₃ τ - 1)),
        ε * μ * (z₂ τ + ε * τ) - μ * (ε * (ε * τ))) (Icc 0 T) τ := by
    intro τ hτ
    have hsq : HasDerivWithinAt (fun s : ℝ => ε * s ^ 2 / 2) (ε * τ) (Icc 0 T) τ := by
      have := (((hasDerivWithinAt_id τ (Icc 0 T)).pow 2).const_mul ε).div_const 2
      exact this.congr_deriv (by simp; ring)
    have e₁ : HasDerivWithinAt (fun s => z₁ s - ε * s ^ 2 / 2)
        (-(1 + μ) * (z₂ τ + ε * τ) + μ * (ε * τ)) (Icc 0 T) τ :=
      ((h₁ τ hτ).sub hsq).congr_deriv (by ring)
    have e₂ : HasDerivWithinAt (fun s => z₂ s + ε * s) (-(ε * (z₃ τ - 1))) (Icc 0 T) τ :=
      ((h₂ τ hτ).add ((hasDerivWithinAt_id τ _).const_mul ε)).congr_deriv (by ring)
    have e₃ : HasDerivWithinAt (fun s => z₃ s - 1)
        (ε * μ * (z₂ τ + ε * τ) - μ * (ε * (ε * τ))) (Icc 0 T) τ :=
      ((h₃ τ hτ).sub_const 1).congr_deriv (by ring)
    exact e₁.prodMk (e₂.prodMk e₃)
  -- the coefficient bound `‖d'‖ ≤ (2 + ε)‖d‖ + μεT(1 + ε)` in the sup norm
  have hbound : ∀ τ ∈ Ico 0 T,
      ‖((-(1 + μ) * (z₂ τ + ε * τ) + μ * (ε * τ), -(ε * (z₃ τ - 1)),
        ε * μ * (z₂ τ + ε * τ) - μ * (ε * (ε * τ))) : ℝ × ℝ × ℝ)‖ ≤
      (2 + ε) * ‖((z₁ τ - ε * τ ^ 2 / 2, z₂ τ + ε * τ, z₃ τ - 1) : ℝ × ℝ × ℝ)‖ +
        μ * (ε * T * (1 + ε)) := by
    intro τ hτ
    set D : ℝ × ℝ × ℝ := (z₁ τ - ε * τ ^ 2 / 2, z₂ τ + ε * τ, z₃ τ - 1) with hD_def
    have hd₂ : |z₂ τ + ε * τ| ≤ ‖D‖ := by
      have h := (norm_fst_le D.2).trans (norm_snd_le D)
      simpa only [hD_def, Real.norm_eq_abs] using h
    have hd₃ : |z₃ τ - 1| ≤ ‖D‖ := by
      have h := (norm_snd_le D.2).trans (norm_snd_le D)
      simpa only [hD_def, Real.norm_eq_abs] using h
    have hN : 0 ≤ ‖D‖ := norm_nonneg _
    have hτ0 : 0 ≤ τ := hτ.1
    have hT0 : 0 ≤ T := hτ0.trans hτ.2.le
    have hετ : 0 ≤ ε * τ := mul_nonneg hε hτ0
    have hετT : ε * τ ≤ ε * T := mul_le_mul_of_nonneg_left hτ.2.le hε
    have hμετ : μ * (ε * τ) ≤ μ * (ε * T) := mul_le_mul_of_nonneg_left hετT hμ
    have hμεεT : 0 ≤ μ * (ε * T) * ε := mul_nonneg (mul_nonneg hμ (mul_nonneg hε hT0)) hε
    have hμεT : 0 ≤ μ * (ε * T) := mul_nonneg hμ (mul_nonneg hε hT0)
    have hεN : 0 ≤ ε * ‖D‖ := mul_nonneg hε hN
    have hεd₂ : ε * μ * |z₂ τ + ε * τ| ≤ ε * ‖D‖ := by
      have h1 : μ * |z₂ τ + ε * τ| ≤ ‖D‖ := by nlinarith [abs_nonneg (z₂ τ + ε * τ)]
      nlinarith
    have hd₂' : (1 + μ) * |z₂ τ + ε * τ| ≤ 2 * ‖D‖ := by
      nlinarith [abs_nonneg (z₂ τ + ε * τ)]
    have hεd₃ : ε * |z₃ τ - 1| ≤ ε * ‖D‖ := mul_le_mul_of_nonneg_left hd₃ hε
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
    · rw [Real.norm_eq_abs]
      calc |-(1 + μ) * (z₂ τ + ε * τ) + μ * (ε * τ)|
          ≤ |-(1 + μ) * (z₂ τ + ε * τ)| + |μ * (ε * τ)| := abs_add_le _ _
        _ = (1 + μ) * |z₂ τ + ε * τ| + μ * (ε * τ) := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ 1 + μ),
            abs_of_nonneg hμ, abs_of_nonneg hετ]
        _ ≤ (2 + ε) * ‖D‖ + μ * (ε * T * (1 + ε)) := by linarith
    · rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hε]
      linarith
    · rw [Real.norm_eq_abs]
      calc |ε * μ * (z₂ τ + ε * τ) - μ * (ε * (ε * τ))|
          ≤ |ε * μ * (z₂ τ + ε * τ)| + |μ * (ε * (ε * τ))| := by
            rw [sub_eq_add_neg, ← abs_neg (μ * (ε * (ε * τ)))]
            exact abs_add_le _ _
        _ = ε * μ * |z₂ τ + ε * τ| + μ * (ε * τ) * ε := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg hε hμ),
            abs_of_nonneg (mul_nonneg hμ (mul_nonneg hε hετ))]
          ring
        _ ≤ (2 + ε) * ‖D‖ + μ * (ε * T * (1 + ε)) := by
          have : μ * (ε * τ) * ε ≤ μ * (ε * T) * ε := mul_le_mul_of_nonneg_right hμετ hε
          linarith
  -- Gronwall's inequality with `d(0) = 0`
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0)
    (fun τ hτ => (hD τ hτ).continuousWithinAt)
    (fun τ hτ => (hD τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hτ))
    (by simp [h01, h02, h03]) hbound
  intro τ hτ
  have hT0 : 0 ≤ T := hτ.1.trans hτ.2
  have hmono := gronwallBound_mono (δ := 0) (K := 2 + ε) le_rfl
    (mul_nonneg hμ (mul_nonneg (mul_nonneg hε hT0) (by linarith : (0 : ℝ) ≤ 1 + ε)))
    (by linarith : (0 : ℝ) ≤ 2 + ε) hτ.2
  rw [gronwallBound_eq_zetaBound hε] at hmono
  have hGτ := hG τ hτ
  rw [sub_zero] at hGτ
  have hN := hGτ.trans hmono
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs] using (norm_fst_le _).trans hN
  · simpa only [Real.norm_eq_abs] using ((norm_fst_le _).trans (norm_snd_le _)).trans hN
  · simpa only [Real.norm_eq_abs] using ((norm_snd_le _).trans (norm_snd_le _)).trans hN

/-- The four coefficients of the `(α₁, α₂)` system of Lemma 2.3 as functions of
`p = (ζ₁, ζ₂, ζ₃, S⁻²)`. -/
noncomputable def shearCoefficients (ε : ℝ) (p : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (2 * p.1 * p.2.1 / (p.1 ^ 2 + p.2.1 ^ 2 * p.2.2.2 + p.2.2.1 ^ 2),
    -1 + p.1 * (p.1 + ε * p.2.2.1) / (p.1 ^ 2 + p.2.1 ^ 2 * p.2.2.2 + p.2.2.1 ^ 2),
    -(1 - p.2.2.2 / 2) + ε * p.2.2.2 / 2 * (p.1 / p.2.2.1) +
      p.2.1 * p.2.2.2 * (2 * p.2.1 / (p.1 ^ 2 + p.2.1 ^ 2 * p.2.2.2 + p.2.2.1 ^ 2)),
    ε * p.2.2.2 / 2 * (p.2.1 / p.2.2.1) +
      p.2.1 * p.2.2.2 * ((p.1 + ε * p.2.2.1) / (p.1 ^ 2 + p.2.1 ^ 2 * p.2.2.2 + p.2.2.1 ^ 2)))

/-- The compact box on which the coefficients are compared. -/
def coefficientBox (R : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  Icc (-R) R ×ˢ Icc (-R) R ×ˢ Icc (1 / 2) (3 / 2) ×ˢ Icc 0 1

/-- The coefficients are continuous on the box, where `ζ₃ ≥ 1/2` and `m ≥ ζ₃² > 0`. -/
theorem continuousOn_shearCoefficients (ε R : ℝ) :
    ContinuousOn (shearCoefficients ε) (coefficientBox R) := by
  have hc : ∀ p ∈ coefficientBox R, p.2.2.1 ≠ 0 := by
    intro p hp
    have := hp.2.2.1.1
    linarith
  have hm : ∀ p ∈ coefficientBox R, p.1 ^ 2 + p.2.1 ^ 2 * p.2.2.2 + p.2.2.1 ^ 2 ≠ 0 := by
    intro p hp
    have h1 := hp.2.2.1.1
    have h2 := hp.2.2.2.1
    have : 0 ≤ p.2.1 ^ 2 * p.2.2.2 := mul_nonneg (sq_nonneg _) h2
    nlinarith [sq_nonneg p.1]
  have hmC : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      p.1 ^ 2 + p.2.1 ^ 2 * p.2.2.2 + p.2.2.1 ^ 2) (coefficientBox R) := by fun_prop
  have hcC : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1) (coefficientBox R) := by fun_prop
  unfold shearCoefficients
  refine ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ ?_))
  · exact ContinuousOn.div (by fun_prop) hmC hm
  · exact continuousOn_const.add (ContinuousOn.div (by fun_prop) hmC hm)
  · exact (ContinuousOn.add (by fun_prop) ((by fun_prop : ContinuousOn
      (fun p : ℝ × ℝ × ℝ × ℝ => ε * p.2.2.2 / 2) _).mul (ContinuousOn.div (by fun_prop) hcC hc)))
      |>.add ((by fun_prop : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => p.2.1 * p.2.2.2) _).mul
        (ContinuousOn.div (by fun_prop) hmC hm))
  · exact ((by fun_prop : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => ε * p.2.2.2 / 2) _).mul
      (ContinuousOn.div (by fun_prop) hcC hc)).add
      ((by fun_prop : ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ => p.2.1 * p.2.2.2) _).mul
        (ContinuousOn.div (by fun_prop) hmC hm))

/-- Uniform continuity of the coefficients on the box: one `δ` for every tolerance. -/
theorem exists_coefficient_delta (ε R : ℝ) {tol : ℝ} (htol : 0 < tol) :
    ∃ δ > 0, ∀ p ∈ coefficientBox R, ∀ q ∈ coefficientBox R,
      |p.1 - q.1| < δ → |p.2.1 - q.2.1| < δ → |p.2.2.1 - q.2.2.1| < δ →
        |p.2.2.2 - q.2.2.2| < δ →
      |(shearCoefficients ε p).1 - (shearCoefficients ε q).1| < tol ∧
      |(shearCoefficients ε p).2.1 - (shearCoefficients ε q).2.1| < tol ∧
      |(shearCoefficients ε p).2.2.1 - (shearCoefficients ε q).2.2.1| < tol ∧
      |(shearCoefficients ε p).2.2.2 - (shearCoefficients ε q).2.2.2| < tol := by
  have hK : IsCompact (coefficientBox R) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hU := hK.uniformContinuousOn_of_continuous (continuousOn_shearCoefficients ε R)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp hU tol htol
  refine ⟨δ, hδ, fun p hp q hq h1 h2 h3 h4 => ?_⟩
  have hd : dist p q < δ := by
    simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨h1, h2, h3, h4⟩
  have := h p hp q hq hd
  simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff] at this
  exact this

/-- The entries of `strongShearMatrix` are the coefficient functions at `(ζ, S⁻²)`. -/
theorem strongShearMatrix_eq (S ε : ℝ) (ζ : Vec3) :
    let c := shearCoefficients ε (ζ 0, ζ 1, ζ 2, 1 / S ^ 2)
    strongShearMatrix S ε ζ 0 0 = c.1 ∧ strongShearMatrix S ε ζ 0 1 = c.2.1 ∧
      strongShearMatrix S ε ζ 1 0 = c.2.2.1 ∧ strongShearMatrix S ε ζ 1 1 = c.2.2.2 := by
  simp only [strongShearMatrix, scaledNormSq, shearCoefficients, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- The entries of the matrix of (2.5) are the coefficient functions at
`(tan φ, -ετ, 1, 0) = (ζ₀, 0)`. -/
theorem referenceSystemMatrix_eq (ε τ : ℝ) :
    let c := shearCoefficients ε (ε * τ ^ 2 / 2, -(ε * τ), 1, 0)
    referenceSystemMatrix ε τ 0 0 = c.1 ∧ referenceSystemMatrix ε τ 0 1 = c.2.1 ∧
      referenceSystemMatrix ε τ 1 0 = c.2.2.1 ∧ referenceSystemMatrix ε τ 1 1 = c.2.2.2 := by
  have hm : 1 + (ε * τ ^ 2 / 2) ^ 2 ≠ 0 := by positivity
  have hs : ReferenceRiccati.s ε τ ^ 2 = 1 / (1 + (ε * τ ^ 2 / 2) ^ 2) := by
    rw [eq_div_iff hm]
    simpa only [ReferenceRiccati.x] using ReferenceRiccati.s_sq_mul ε τ
  simp only [referenceSystemMatrix, shearCoefficients, Matrix.neg_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, sin_two_referenceAngle, driving_referenceAngle,
    ReferenceRiccati.damping, ReferenceRiccati.driving, ReferenceRiccati.x, hs]
  refine ⟨?_, ?_, by ring, by ring⟩
  · field_simp
    ring
  · field_simp
    ring

end TorusEuler.Paper.Lib.S2a
