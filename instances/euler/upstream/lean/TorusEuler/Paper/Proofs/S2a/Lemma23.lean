import TorusEuler.Paper.Proofs.S2a.Library.StrongShear

/-! # Proof of Lemma 2.3

The conditional proof `TorusEuler.Paper.Proof.lemma_2_3_of` of
`TorusEuler.Paper.Statement.lemma_2_3` (`cc:lem:strong-shear`,
`sections/03_amplification.tex:113-195`). Lemma 2.3 cites Lemma 2.2 (ledger row 2.3,
`cites = [2.2]`), which enters only through the hypothesis `h2_2`. The proof is new: no
earlier library lemma carries the row's content. The two theorems `Lib.S2a.model_case_equations`
and `Lib.S2a.strongShear_limit` below carry it (the two conjuncts of the statement, each
from `h2_2` alone), and the package notes request that the ledger list them as the
`content` of row 2.3, so that the checker `VerifySpine.lean` detects any use of them by another row. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper

namespace Lib.S2a

open MovingWaveVector MovingAmplitude

/-- The model-case equations of **Lemma 2.3** (first part of the statement, without the
standing assumption `T ≥ 2`, which it does not need), following
`sections/03_amplification.tex:145-175`. Here `h2_2` is Lemma 2.2, applied to the preceding
wave `(k_p, a_p)` over `B` on the window `I` (`hframe`): the frame `(E₁, E₂, E₃)` is
orthonormal and satisfies (2.2).

* `σ_p = σ` (`:146-149`): the last equation of (2.2) from `h2_2`,
  `(log σ_p)' = B₃₃ = 0` in the model case, composed with the clock `t = t₀ + τ/r`, and the
  mean value inequality on `[0, T]`.
* The equations for `ζ` (`:150-156`, `:165-172`): the first three equations of (2.2) from
  `h2_2`, divided by `r` to pass to the time `τ` (`hE`); the wave-vector equation
  `k' = -Mᵀk` in the time `τ`, where `M/r` is `strain` with shear `S` and strength ratio
  `σ_p/σ = 1` (`hstrain`, which uses `σ_p = σ`); the projection onto the frame
  (`normalized_waveVector_derivatives`), and the identities `ν/r = 1/(2S)`,
  `η/r = ε/(2S)` of `:167-171` (`hb`).
* The equations for `α₁ = S a·E₁ = -U` and `α₂ = a·E₂ = V` (`:157-164`, `:172-175`):
  the amplitude equation in the time `τ` (`haτ`), its projection onto `E₁, E₂` with the
  derivatives of `E₁, E₂` from `h2_2` and with `α₃` eliminated by transversality
  (`normalized_amplitude_derivatives`, valid where `ζ₃ ≠ 0`), and the model entries of
  `B/r` and `M/r` (`strain_modelEntries`); `λSp_w/r = Π` is the final algebra. -/
theorem model_case_equations (h2_2 : Statement.lemma_2_2) {I : Set ℝ} {t₀ T lam : ℝ}
    (w : PhysicalAmplification I t₀) {k : ℝ → Vec3}
    (hclock : MapsTo w.clock (Icc 0 T) I) (hmodel : ModelCase w T)
    (hk : NewWaveVector w lam k) :
    let S := w.shear
    let ε := w.ratio
    let ζ := zeta w lam k
    (∀ τ ∈ Icc 0 T, ‖w.kp (w.clock τ)‖ * ‖w.ap (w.clock τ)‖ = w.initialStrength) ∧
    (∀ τ ∈ Icc 0 T,
      HasDerivWithinAt (fun s => ζ s 0) (-(1 + 1 / (2 * S ^ 2)) * ζ τ 1) (Icc 0 T) τ ∧
      HasDerivWithinAt (fun s => ζ s 1) (-(ε * ζ τ 2)) (Icc 0 T) τ ∧
      HasDerivWithinAt (fun s => ζ s 2) (ε / (2 * S ^ 2) * ζ τ 1) (Icc 0 T) τ) ∧
    (∀ a : ℝ → Vec3, AmplitudeVector w k a → ∀ τ ∈ Icc 0 T, ζ τ 2 ≠ 0 →
      let α := alpha w a
      let Pm := strongShearPressure S ε (ζ τ) (α τ 0) (α τ 1)
      HasDerivWithinAt (fun s => α s 0) (-α τ 1 + ζ τ 0 * Pm) (Icc 0 T) τ ∧
      HasDerivWithinAt (fun s => α s 1)
        (-(1 - 1 / (2 * S ^ 2)) * α τ 0 +
          ε / (2 * S ^ 2) * ((ζ τ 0 * α τ 0 + ζ τ 1 * α τ 1) / ζ τ 2) +
          ζ τ 1 / S ^ 2 * Pm) (Icc 0 T) τ) := by
  intro S ε ζ
  have hr : 0 < w.rate := w.rate_pos
  have hσ : 0 < w.initialStrength := w.initialStrength_pos
  have hS : 0 < S := shear_pos w
  have hlam : lam ≠ 0 := hk.1.ne'
  -- Lemma 2.2 for the preceding wave over `B` on the window
  have hframe := h2_2 (J := I) (B := w.B) (k := w.kp) (a := w.ap) w.trace_zero
    ⟨w.preceding_vector, fun t ht => by
      simpa only [affineWaveAmplitudeOperator_apply, affineWavePressureCoeff] using
        w.preceding_amplitude t ht⟩ w.preceding_data
  have hchange (τ : ℝ) : HasDerivAt w.clock (1 / w.rate) τ :=
    ((hasDerivAt_id τ).div_const w.rate).const_add t₀
  -- `σ_p = σ`
  have hσp : ∀ τ ∈ Icc 0 T, ‖w.kp (w.clock τ)‖ * ‖w.ap (w.clock τ)‖ = w.initialStrength := by
    have hd : ∀ τ ∈ Icc 0 T, HasDerivWithinAt
        (fun s => Real.log (‖w.kp (w.clock s)‖ * ‖w.ap (w.clock s)‖)) 0 (Icc 0 T) τ := by
      intro τ hτ
      obtain ⟨-, -, -, -, hlog⟩ := hframe (w.clock τ) (hclock hτ)
      have h33 : entry (frame w.kp w.ap (w.clock τ)) (w.B (w.clock τ)) 2 2 = 0 := by
        have h := (hmodel τ hτ).1 2 2
        simpa [modelEntries] using h
      have h := hlog.scomp τ (hchange τ).hasDerivWithinAt hclock
      rw [h33, smul_zero] at h
      exact h
    intro τ hτ
    have h := abs_sub_le_of_hasDerivWithinAt (C := 0) hd (fun _ _ => by rw [abs_zero]) τ hτ
    rw [zero_mul, abs_nonpos_iff, sub_eq_zero, PhysicalAmplification.clock_zero] at h
    obtain ⟨hkτ, haτ, -⟩ := w.preceding_data _ (hclock hτ)
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 hσ) h
  -- the frame equations (2.2) in the time `τ`
  have hE : ∀ τ ∈ Icc 0 T,
      let e := fun s => w.basis (w.clock s)
      let b := (1 / w.rate) • w.B (w.clock τ)
      Orthonormal ℝ (e τ) ∧
      HasDerivWithinAt (fun u => e u 0)
        ((-entry (e τ) b 0 1) • e τ 1 - entry (e τ) b 0 2 • e τ 2) (Icc 0 T) τ ∧
      HasDerivWithinAt (fun u => e u 1)
        (entry (e τ) b 0 1 • e τ 0 - entry (e τ) b 2 1 • e τ 2) (Icc 0 T) τ ∧
      HasDerivWithinAt (fun u => e u 2)
        (entry (e τ) b 0 2 • e τ 0 + entry (e τ) b 2 1 • e τ 1) (Icc 0 T) τ := by
    intro τ hτ e b
    obtain ⟨hON, hE₁, hE₂, hE₃, -⟩ := hframe (w.clock τ) (hclock hτ)
    refine ⟨hON, (hasDerivWithinAt_normalized_time hclock hE₁).congr_deriv ?_,
      (hasDerivWithinAt_normalized_time hclock hE₂).congr_deriv ?_,
      (hasDerivWithinAt_normalized_time hclock hE₃).congr_deriv ?_⟩ <;>
    · simp only [e, b, entry_smul]
      module
  -- the full gradient in the time `τ`: `M/r = strain` with shear `S` and ratio `σ_p/σ = 1`
  have hstrain : ∀ τ ∈ Icc 0 T,
      strain (w.basis (w.clock τ)) ((1 / w.rate) • w.B (w.clock τ))
        ((1 / w.rate) • w.E (w.clock τ)) S 1 = (1 / w.rate) • w.gradient (w.clock τ) := by
    intro τ hτ
    obtain ⟨hkτ, haτ, -⟩ := w.preceding_data _ (hclock hτ)
    obtain ⟨hk0, ha0, -⟩ := w.preceding_data _ w.activation
    have h := normalized_strain_eq (kp := fun s => w.kp (w.clock s))
      (ap := fun s => w.ap (w.clock s)) (B := w.B (w.clock τ)) (E := w.E (w.clock τ))
      (t := τ) hr.ne' (by simpa using hk0) (by simpa using ha0) hkτ haτ
    have h1 : strengthRatio (fun s => w.kp (w.clock s)) (fun s => w.ap (w.clock s)) τ = 1 := by
      simp only [strengthRatio, PhysicalAmplification.clock_zero]
      rw [hσp τ hτ]
      exact div_self hσ.ne'
    have h2 : (‖(fun s => w.kp (w.clock s)) 0‖ * ‖(fun s => w.ap (w.clock s)) 0‖) / w.rate =
        S := by
      simp only [PhysicalAmplification.clock_zero]
      rfl
    rw [h1, h2] at h
    exact h
  -- the wave vector in the time `τ`
  have hkτ : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => k (w.clock s))
      (-((strain (w.basis (w.clock τ)) ((1 / w.rate) • w.B (w.clock τ))
        ((1 / w.rate) • w.E (w.clock τ)) S 1).adjoint (k (w.clock τ)))) (Icc 0 T) τ := by
    intro τ hτ
    rw [hstrain τ hτ]
    exact (hasDerivWithinAt_normalized_time hclock (hk.2.2 _ (hclock hτ))).congr_deriv
      (by simp only [map_smul, smul_apply, smul_neg]; rfl)
  -- model entries in the time `τ`
  have hb : ∀ τ ∈ Icc 0 T, ∀ i j,
      entry (w.basis (w.clock τ)) ((1 / w.rate) • w.B (w.clock τ)) i j =
        modelEntries (1 / (2 * S)) (ε / (2 * S)) i j := by
    intro τ hτ i j
    rw [entry_smul, (hmodel τ hτ).1 i j, smul_modelEntries, nu_div_rate, eta_div_rate]
  have hd : ∀ τ ∈ Icc 0 T, ∀ i j,
      entry (w.basis (w.clock τ)) ((1 / w.rate) • w.E (w.clock τ)) i j = 0 := by
    intro τ hτ i j
    rw [(hmodel τ hτ).2]
    simp only [entry, smul_apply, zero_apply, smul_zero, inner_zero_right]
  have hζ : ∀ s, (ζ s).ofLp 0 = X (fun s => w.basis (w.clock s)) (fun s => k (w.clock s)) lam s ∧
      (ζ s).ofLp 1 = Q (fun s => w.basis (w.clock s)) (fun s => k (w.clock s)) lam S s ∧
      (ζ s).ofLp 2 = Z (fun s => w.basis (w.clock s)) (fun s => k (w.clock s)) lam s :=
    fun s => ⟨rfl, rfl, rfl⟩
  have hS0 : S ≠ 0 := hS.ne'
  obtain ⟨m00, m01, m02, m10, m11, m12, m20, m21, m22⟩ :=
    modelEntries_apply (1 / (2 * S)) (ε / (2 * S))
  refine ⟨hσp, fun τ hτ => ?_, fun a ha τ hτ hz => ?_⟩
  · obtain ⟨hON, hE₁, hE₂, hE₃⟩ := hE τ hτ
    obtain ⟨hX, hQ, hZ⟩ := normalized_waveVector_derivatives
      (e := fun s => w.basis (w.clock s)) (k := fun s => k (w.clock s)) (t := τ)
      (scale := lam) hON hlam hS0 hE₁ hE₂ hE₃ (hkτ τ hτ)
    simp only [hb τ hτ, hd τ hτ] at hX hQ hZ
    simp only [hζ]
    refine ⟨hX.congr_deriv ?_, hQ.congr_deriv ?_, hZ.congr_deriv ?_⟩ <;>
    · simp only [m00, m01, m02, m10, m11, m12, m20, m21, m22]
      field_simp
      ring
  · obtain ⟨hON, hE₁, hE₂, -⟩ := hE τ hτ
    have haτ : HasDerivWithinAt (fun s => a (w.clock s))
        (-((strain (w.basis (w.clock τ)) ((1 / w.rate) • w.B (w.clock τ))
          ((1 / w.rate) • w.E (w.clock τ)) S 1) (a (w.clock τ))) +
          (2 * ⟪k (w.clock τ), (strain (w.basis (w.clock τ)) ((1 / w.rate) • w.B (w.clock τ))
            ((1 / w.rate) • w.E (w.clock τ)) S 1) (a (w.clock τ))⟫_ℝ /
              ‖k (w.clock τ)‖ ^ 2) • k (w.clock τ)) (Icc 0 T) τ := by
      rw [hstrain τ hτ]
      have ha' := ha.1 _ (hclock hτ)
      simp only [affineWavePressureCoeff] at ha'
      exact (normalized_affineWave_derivatives (r := w.rate) (t₀ := t₀) (τ := τ)
        (D := w.gradient (w.clock τ)) hclock (hk.2.2 _ (hclock hτ)) ha').2
    have hperp : ⟪k (w.clock τ), a (w.clock τ)⟫_ℝ = 0 := by
      rw [real_inner_comm]; exact ha.2 _ (hclock hτ)
    have hZ : Z (fun s => w.basis (w.clock s)) (fun s => k (w.clock s)) lam τ ≠ 0 := by
      rw [← (hζ τ).2.2]; exact hz
    obtain ⟨hU, hV⟩ := normalized_amplitude_derivatives
      (e := fun s => w.basis (w.clock s)) (k := fun s => k (w.clock s))
      (a := fun s => a (w.clock s)) (t := τ) (scale := lam) (S := S)
      (B := (1 / w.rate) • w.B (w.clock τ)) hON hlam hS0 hZ hperp hE₁ hE₂ haτ
    have hα : ∀ s, (alpha w a s).ofLp 0 =
        -(U (fun s => w.basis (w.clock s)) (fun s => a (w.clock s)) S s) ∧
        (alpha w a s).ofLp 1 = V (fun s => w.basis (w.clock s)) (fun s => a (w.clock s)) s :=
      fun s => ⟨by simp only [alpha, U, Matrix.cons_val_zero]; ring, rfl⟩
    obtain ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ :=
      strain_modelEntries (S := S) hON (hb τ hτ) (hd τ hτ)
    have hm : normFactor (X (fun s => w.basis (w.clock s)) (fun s => k (w.clock s)) lam τ)
        (Q (fun s => w.basis (w.clock s)) (fun s => k (w.clock s)) lam S τ)
        (Z (fun s => w.basis (w.clock s)) (fun s => k (w.clock s)) lam τ) S ≠ 0 := by
      unfold normFactor
      have := sq_pos_of_ne_zero hZ
      positivity
    simp only [hα, hζ]
    simp only [hb τ hτ, m01, m02, m21, a00, a01, a02, a10, a11,
      a12, a20, a21, a22, pairOperator_apply, rawMatrix, pressureU, pressureV,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at hU hV
    unfold normFactor at hU hV hm
    refine ⟨hU.neg.congr_deriv ?_, hV.congr_deriv ?_⟩
    · simp only [strongShearPressure, scaledNormSq, hζ]
      field_simp
      ring
    · simp only [strongShearPressure, scaledNormSq, hζ]
      field_simp
      ring
/-- The strong-shear limit of **Lemma 2.3** (second part of the statement), following
`sections/03_amplification.tex:177-194`. Here `h2_2` (Lemma 2.2) enters twice: through
`model_case_equations` (the equations for `ζ` in the model case) and through the
orthonormality of the frame at `t₀`, which with `k(t₀) = λE₃` gives `ζ(0) = (0, 0, 1)`.

* `ζ → ζ₀` uniformly on `[0, T]` (`:177-182`): `zeta_bounds` is the Gronwall step of
  `:180-181`. The difference `ζ - ζ₀` solves the system for `ζ` (bounded coefficients, as
  `1/(2S²) ≤ 1`) with the inhomogeneity `(A_S - A_∞)ζ₀ = O(1/S²)` and vanishes at `0`, so
  Gronwall's inequality bounds each component of `ζ - ζ₀` by `μK(ε,T)` with
  `μ = 1/(2S²)`; hence `|ζ - ζ₀| ≤ 3μK(ε,T)` (`norm_le_abs_add_abs_add_abs`), and
  `ζ₃ ≥ 1/2` for `S` large.
* The coefficients converge (`:182-194`): the entries of `strongShearMatrix` and of the
  matrix of (2.5) are one continuous function `shearCoefficients` evaluated at
  `(ζ, S⁻²)` and at `(ζ₀, 0)` (`strongShearMatrix_eq`, `referenceSystemMatrix_eq`), and
  uniform continuity on a compact box (`exists_coefficient_delta`) turns
  `|ζ - ζ₀| + S⁻² → 0` into uniform convergence on `[0, T]`.

The threshold `S₀` depends only on `ε`, `T` and the tolerance; for `ε ≤ 0` no
configuration has ratio `ε` (`ν, η > 0`). -/
theorem strongShear_limit (h2_2 : Statement.lemma_2_2) :
    ∀ ε T : ℝ, 2 ≤ T → ∀ tol : ℝ, 0 < tol → ∃ S₀ : ℝ,
      ∀ {I : Set ℝ} {t₀ lam : ℝ} (w : PhysicalAmplification I t₀) {k : ℝ → Vec3},
        MapsTo w.clock (Icc 0 T) I → ModelCase w T → NewWaveVector w lam k →
        w.ratio = ε → S₀ ≤ w.shear →
        ∀ τ ∈ Icc 0 T,
          ‖zeta w lam k τ - zetaRef ε τ‖ ≤ tol ∧ zeta w lam k τ 2 ≠ 0 ∧
          ∀ i j, |strongShearMatrix w.shear ε (zeta w lam k τ) i j -
            referenceSystemMatrix ε τ i j| ≤ tol := by
  intro ε T hT tol htol
  rcases le_or_gt ε 0 with hε | hε
  · refine ⟨0, fun {_ _ _} w {_} _ _ _ hratio _ => ?_⟩
    exact absurd (hratio ▸ w.ratio_pos) (not_lt.2 hε)
  have hT0 : 0 ≤ T := by linarith
  set K := zetaBound ε T with hK_def
  have hK : 0 ≤ K := zetaBound_nonneg hε.le hT0
  set R := ε * T ^ 2 + ε * T + 1 with hR_def
  obtain ⟨δ, hδ, hcoef⟩ := exists_coefficient_delta ε R htol
  set μ₀ := min (1 / 2) (min (1 / (2 * (K + 1))) (min (tol / (3 * (K + 1)))
    (δ / (2 * (K + 2))))) with hμ₀_def
  have hμ₀ : 0 < μ₀ := by
    simp only [hμ₀_def, lt_min_iff]
    refine ⟨by norm_num, by positivity, by positivity, by positivity⟩
  refine ⟨1 + 1 / μ₀, fun {I t₀ lam} w {k} hclock hmodel hk hratio hS₀ τ hτ => ?_⟩
  subst hratio
  set S := w.shear with hS_def
  have hS1 : 1 ≤ S := by
    have : 0 < 1 / μ₀ := by positivity
    linarith
  have hS0 : 0 < S := by linarith
  set μ := 1 / (2 * S ^ 2) with hμ_def
  have hμ0 : 0 ≤ μ := by positivity
  have hμμ₀ : μ ≤ μ₀ := by
    have h1 : 1 / μ₀ ≤ S := by linarith
    have h2 : 1 / (2 * S ^ 2) ≤ 1 / S := by
      apply one_div_le_one_div_of_le hS0
      nlinarith
    have h3 : 1 / S ≤ μ₀ := by
      rw [div_le_iff₀ hS0]
      rw [div_le_iff₀ hμ₀] at h1
      linarith
    exact h2.trans h3
  have hμ1 : μ ≤ 1 / 2 := hμμ₀.trans (min_le_left _ _)
  have hμK : μ ≤ 1 / (2 * (K + 1)) := hμμ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hμtol : μ ≤ tol / (3 * (K + 1)) :=
    hμμ₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hμδ : μ ≤ δ / (2 * (K + 2)) :=
    hμμ₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- the equations for `ζ` (model case) and `ζ(0) = (0, 0, 1)`
  obtain ⟨-, hζ, -⟩ := model_case_equations h2_2 w hclock hmodel hk
  have hON₀ : Orthonormal ℝ (w.basis t₀) := by
    have hframe := h2_2 (J := I) (B := w.B) (k := w.kp) (a := w.ap) w.trace_zero
      ⟨w.preceding_vector, fun t ht => by
        simpa only [affineWaveAmplitudeOperator_apply, affineWavePressureCoeff] using
          w.preceding_amplitude t ht⟩ w.preceding_data
    exact (hframe t₀ w.activation).1
  obtain ⟨h01, h02, h03⟩ := coordinate_initial_values (e := w.basis) (k := k) (scale := lam)
    (S := S) hON₀ hk.1.ne' hk.2.1
  have hb := zeta_bounds (μ := μ) (ε := w.ratio) (T := T) hμ0 (by linarith) hε.le
    (z₁ := fun s => zeta w lam k s 0) (z₂ := fun s => zeta w lam k s 1)
    (z₃ := fun s => zeta w lam k s 2)
    (fun s hs => (hζ s hs).1) (fun s hs => (hζ s hs).2.1)
    (fun s hs => (hζ s hs).2.2.congr_deriv (by rw [hμ_def]; ring))
    (by
      rw [show zeta w lam k 0 0 = X w.basis k lam (w.clock 0) from rfl,
        PhysicalAmplification.clock_zero]
      exact h01)
    (by
      rw [show zeta w lam k 0 1 = Q w.basis k lam S (w.clock 0) from rfl,
        PhysicalAmplification.clock_zero]
      exact h02)
    (by
      rw [show zeta w lam k 0 2 = Z w.basis k lam (w.clock 0) from rfl,
        PhysicalAmplification.clock_zero]
      exact h03) τ hτ
  obtain ⟨hb₁, hb₂, hb₃⟩ := hb
  -- size of the errors
  have hμK' : μ * K ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hμK hK
    calc μ * K ≤ 1 / (2 * (K + 1)) * K := this
      _ ≤ 1 / 2 := by rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  have hμtol' : 3 * (μ * K) ≤ tol := by
    have := mul_le_mul_of_nonneg_right hμtol hK
    calc 3 * (μ * K) ≤ 3 * (tol / (3 * (K + 1)) * K) := by linarith
      _ ≤ tol := by
        rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
  have hμδ₁ : μ * K < δ := by
    have := mul_le_mul_of_nonneg_right hμδ hK
    calc μ * K ≤ δ / (2 * (K + 2)) * K := this
      _ < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  have hμδ₂ : 2 * μ < δ := by
    calc 2 * μ ≤ 2 * (δ / (2 * (K + 2))) := by linarith
      _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hτ0 := hτ.1
  have hτT := hτ.2
  have hz₃ : 1 / 2 ≤ zeta w lam k τ 2 := by
    have := (abs_le.mp (hb₃.trans hμK')).1
    linarith
  have hx : w.ratio * τ ^ 2 / 2 ≤ w.ratio * T ^ 2 / 2 := by
    have := pow_le_pow_left₀ hτ0 hτT 2
    have := mul_le_mul_of_nonneg_left this hε.le
    linarith
  have hy : w.ratio * τ ≤ w.ratio * T := mul_le_mul_of_nonneg_left hτT hε.le
  have hεT : 0 ≤ w.ratio * T := by positivity
  have hεT2 : 0 ≤ w.ratio * T ^ 2 := by positivity
  have hετ : 0 ≤ w.ratio * τ := by positivity
  have hετ2 : 0 ≤ w.ratio * τ ^ 2 / 2 := by positivity
  refine ⟨?_, (lt_of_lt_of_le (by norm_num) hz₃).ne', ?_⟩
  · -- `|ζ - ζ₀| ≤ 3μK ≤ tol`
    refine (norm_le_abs_add_abs_add_abs _).trans ?_
    simp only [zetaRef, PiLp.sub_apply, tan_referenceAngle]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, sub_neg_eq_add]
    linarith
  · -- the coefficients
    have hp : ((zeta w lam k τ) 0, (zeta w lam k τ) 1, (zeta w lam k τ) 2, 1 / S ^ 2) ∈
        coefficientBox R := by
      have h1 := abs_le.mp (hb₁.trans hμK')
      have h2 := abs_le.mp (hb₂.trans hμK')
      have h3 := abs_le.mp (hb₃.trans hμK')
      have hS2 : 1 / S ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
        ⟨by linarith, by linarith⟩, ⟨by positivity, hS2⟩⟩
    have hq : (w.ratio * τ ^ 2 / 2, -(w.ratio * τ), (1 : ℝ), (0 : ℝ)) ∈ coefficientBox R :=
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by norm_num, by norm_num⟩,
        ⟨le_rfl, zero_le_one⟩⟩
    have hι : 1 / S ^ 2 = 2 * μ := by rw [hμ_def]; field_simp
    obtain ⟨c00, c01, c10, c11⟩ := hcoef _ hp _ hq (hb₁.trans_lt hμδ₁)
      (by
        show |zeta w lam k τ 1 - -(w.ratio * τ)| < δ
        rw [sub_neg_eq_add]
        exact hb₂.trans_lt hμδ₁)
      (hb₃.trans_lt hμδ₁)
      (by
        show |1 / S ^ 2 - 0| < δ
        rw [sub_zero, hι, abs_of_nonneg (by positivity)]
        exact hμδ₂)
    obtain ⟨s00, s01, s10, s11⟩ := strongShearMatrix_eq S w.ratio (zeta w lam k τ)
    obtain ⟨r00, r01, r10, r11⟩ := referenceSystemMatrix_eq w.ratio τ
    intro i j
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, s00, r00]; exact c00.le
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, s01, r01]; exact c01.le
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, s10, r10]; exact c10.le
    · simp only [Fin.isValue, Fin.mk_one, s11, r11]; exact c11.le

end Lib.S2a

/-- Proof of **Lemma 2.3** (`cc:lem:strong-shear`) following
`sections/03_amplification.tex:144-195`, with the equation numbers (2.2) (frame),
(2.3) (`ζ`, `α`), (2.4) (`φ`, `ζ₀`) and (2.5) (the reference system) of the latest
manuscript. The hypothesis `h2_2` is Lemma 2.2, the only result the proof cites.

* First part (`:145-175`), `Lib.S2a.model_case_equations h2_2`: `h2_2` gives the frame
  equations (2.2) of the preceding wave; their last equation gives `σ_p = σ`, the other
  three give, after the change of time `τ = r(t - t₀)` and the projection of the
  equations (2.1) for `k` and `a` onto the frame, the systems for `ζ` and for
  `(α₁, α₂)`.
* Second part (`:177-194`), `Lib.S2a.strongShear_limit h2_2`: the equations for `ζ` from
  the first part and `ζ(0) = (0,0,1)` (orthonormality of the frame at `t₀`, from `h2_2`)
  give, by Gronwall's inequality as in the text (`Lib.S2a.zeta_bounds`), a bound
  `K(ε,T)/(2S²)` for each component of `ζ - ζ₀` on `[0, T]`, hence
  `|ζ - ζ₀| ≤ 3K(ε,T)/(2S²)`, and continuity
  of the coefficients in `(ζ, S⁻²)`, uniform on a compact box, gives their uniform
  convergence to those of (2.5). -/
theorem Proof.lemma_2_3_of (h2_2 : Statement.lemma_2_2) : Statement.lemma_2_3 :=
  ⟨fun {_ _ _ _} w {_} _ hclock hmodel hk => Lib.S2a.model_case_equations h2_2 w hclock hmodel hk,
    Lib.S2a.strongShear_limit h2_2⟩

end TorusEuler.Paper
