import TorusEuler.ExactAffineEuler
import TorusEuler.PhysicalAmplificationCrossing
import TorusEuler.PhysicalGrowthPropagator

/-! # Vocabulary for the statements of Section 2

Definitions used by `TorusEuler.Paper.Statement.lemma_2_1` through
`TorusEuler.Paper.Statement.proposition_2_8`, in the notation of the latest
manuscript (`sections/02_affine.tex`, `sections/03_amplification.tex`).

## The setting of Subsection 2.2.1

The standing data of Subsection 2.2.1 (`cc:sec:comparison`,
`sections/03_amplification.tex:22-66`) are the fields of the library structure
`MovingWaveVector.PhysicalAmplification I t₀`, whose definition matches the text:

* `w.kp`, `w.ap`: the preceding wave `(k_p, a_p)`, nonzero and perpendicular on `I`
  and solving (2.1) with `D = B` (`preceding_data`, `preceding_vector`,
  `preceding_amplitude`);
* `w.B`: the older gradient `B`, continuous and trace free on `I`;
* `w.E`: the continuous error matrix `E_c`;
* `t₀ ∈ I`: the activation time; `I` is a compact window of physical time;
* `w.basis t = (E₁, E₂, E₃)(t)`: the frame of the preceding wave (Lemma 2.2), and
  `MovingWaveVector.entry (w.basis t) (w.B t) i j = B_{i+1, j+1}(t)` (indices from 0);
* `w.gradient = M = B + a_p ⊗ k_p + E_c`;
* `w.initialStrength = σ = σ_p(t₀)`, `w.firstCoupling = ν = B₁₂(t₀) > 0`,
  `w.thirdCoupling = η = B₃₂(t₀) > 0` (the positivity is a field of the structure);
* `w.rate = r = √(2σν)`, `w.shear = S = σ/r`, `w.ratio = ε = η/ν`;
* `w.clock τ = t₀ + τ/r`, the physical time at normalized time `τ = r(t - t₀)`;
* `w.errorSize = δ` of (2.6), with the four suprema taken over `I`; the matrix norms
  `|B|` and `|E_c|` in (2.6) are operator norms for the Euclidean norm on `ℝ³`
  (`B t, E t : Vec3 →L[ℝ] Vec3`). The text does not name a matrix norm; the operator
  norm is the smallest norm compatible with its uses `|B| ≥ |E₁·BE₂|` and
  `|E_c v| ≤ |E_c||v|`.

The text works on `0 ≤ τ ≤ T`, that is, on `I = [t₀, t₀ + T/r]`. The Lean statements
allow any compact window `I` containing this slab (hypothesis
`MapsTo w.clock (Icc 0 T) I`); the text is the case `I = w.activeSlab T`, in which `δ`
is exactly (2.6). The activation frequency `λ` is written `lam`.
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper

open MovingWaveVector

noncomputable section

/-! ## Subsection 2.1 -/

/-- The first two equations of (2.1) on a time set `J`, with the pressure coefficient
of the third equation: `k' = -Dᵀk` and `a' = -Da + p_w k` with `p_w = 2 k·Da/|k|²`
(`affineWavePressureCoeff`). Derivatives are taken within `J`. The fourth relation
`k·a = 0` of (2.1) is stated separately wherever the text assumes it. -/
def WaveOn (J : Set ℝ) (D : ℝ → Vec3 →L[ℝ] Vec3) (k a : ℝ → Vec3) : Prop :=
  (∀ t ∈ J, HasDerivWithinAt k (-((D t).adjoint (k t))) J t) ∧
  (∀ t ∈ J, HasDerivWithinAt a
    (-(D t (a t)) + affineWavePressureCoeff (D t) (k t) (a t) • k t) J t)

/-! ## Subsection 2.2.1: the new wave in the preceding frame -/

variable {I : Set ℝ} {t₀ : ℝ}

/-- The wave vector `k` of the new wave (`sections/03_amplification.tex:35-37`): it solves
the first equation of (2.1) with `D = M` on the window `I` and equals `λ E₃` at the
activation time, with `λ = lam > 0`. -/
def NewWaveVector (w : PhysicalAmplification I t₀) (lam : ℝ) (k : ℝ → Vec3) : Prop :=
  0 < lam ∧ k t₀ = lam • w.basis t₀ 2 ∧
    ∀ t ∈ I, HasDerivWithinAt k (-((w.gradient t).adjoint (k t))) I t

/-- An amplitude vector for the wave vector `k` (`sections/03_amplification.tex:38-40`): a
solution of the second equation of (2.1) with `D = M` on the window `I` that is
perpendicular to `k`. -/
def AmplitudeVector (w : PhysicalAmplification I t₀) (k a : ℝ → Vec3) : Prop :=
  (∀ t ∈ I, HasDerivWithinAt a
    (-(w.gradient t (a t)) + affineWavePressureCoeff (w.gradient t) (k t) (a t) • k t) I t) ∧
  ∀ t ∈ I, ⟪a t, k t⟫_ℝ = 0

/-- The scaled components `ζ = (ζ₁, ζ₂, ζ₃)` of the wave vector, (2.3), at normalized time
`τ`: `k = λ(ζ₁E₁ + (ζ₂/S)E₂ + ζ₃E₃)` at `t = t₀ + τ/r`. Since the frame is orthonormal,
`ζ₁ = k·E₁/λ`, `ζ₂ = S k·E₂/λ`, `ζ₃ = k·E₃/λ`. Indices start at `0`. -/
def zeta (w : PhysicalAmplification I t₀) (lam : ℝ) (k : ℝ → Vec3) (τ : ℝ) : Vec3 :=
  WithLp.toLp 2 ![⟪w.basis (w.clock τ) 0, k (w.clock τ)⟫_ℝ / lam,
    w.shear * ⟪w.basis (w.clock τ) 1, k (w.clock τ)⟫_ℝ / lam,
    ⟪w.basis (w.clock τ) 2, k (w.clock τ)⟫_ℝ / lam]

/-- The scaled components `α = (α₁, α₂, α₃)` of an amplitude vector, (2.3), at
normalized time `τ`: `a = (α₁/S)E₁ + α₂E₂ + (α₃/S)E₃` at `t = t₀ + τ/r`, that is
`α₁ = S a·E₁`, `α₂ = a·E₂`, `α₃ = S a·E₃`. Indices start at `0`. -/
def alpha (w : PhysicalAmplification I t₀) (a : ℝ → Vec3) (τ : ℝ) : Vec3 :=
  WithLp.toLp 2 ![w.shear * ⟪w.basis (w.clock τ) 0, a (w.clock τ)⟫_ℝ,
    ⟪w.basis (w.clock τ) 1, a (w.clock τ)⟫_ℝ,
    w.shear * ⟪w.basis (w.clock τ) 2, a (w.clock τ)⟫_ℝ]

/-- The angle `φ` of (2.4): `tan φ = ετ²/2` and `0 ≤ φ < π/2` (for `ε ≥ 0`). -/
def referenceAngle (ε τ : ℝ) : ℝ := Real.arctan (ε * τ ^ 2 / 2)

/-- The limiting scaled wave vector `ζ₀ = (tan φ, -ετ, 1)` of (2.4). -/
def zetaRef (ε τ : ℝ) : Vec3 :=
  WithLp.toLp 2 ![Real.tan (referenceAngle ε τ), -(ε * τ), 1]

/-- The coefficient matrix of the reference system (2.5),
`(α₁, α₂)' = referenceSystemMatrix ε τ (α₁, α₂)`, that is
`-[[ετ sin 2φ, cos²φ (1 - ε tan φ)], [1, 0]]`. It is also the matrix displayed in
Lemma 2.4. -/
def referenceSystemMatrix (ε τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -!![ε * τ * Real.sin (2 * referenceAngle ε τ),
      Real.cos (referenceAngle ε τ) ^ 2 * (1 - ε * Real.tan (referenceAngle ε τ));
      1, 0]

/-- The entries of `B` in the frame in the model case of Lemma 2.3: `B₁₂ = ν`,
`B₃₂ = η`, all other entries zero (indices from `0`). -/
def modelEntries (ν η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, ν, 0; 0, 0, 0; 0, η, 0]

/-- The model case of Lemma 2.3 on `0 ≤ τ ≤ T`: the entries of `B` in the frame are
`B₁₂ = ν`, `B₃₂ = η` and `B_ij = 0` otherwise, and `E_c = 0`. -/
def ModelCase (w : PhysicalAmplification I t₀) (T : ℝ) : Prop :=
  ∀ τ ∈ Icc 0 T,
    (∀ i j, entry (w.basis (w.clock τ)) (w.B (w.clock τ)) i j =
      modelEntries w.firstCoupling w.thirdCoupling i j) ∧ w.E (w.clock τ) = 0

/-- The factor `m = ζ₁² + ζ₂²/S² + ζ₃²` of Subsection 2.2.1, so that `|k|² = λ²m`. -/
def scaledNormSq (S : ℝ) (ζ : Vec3) : ℝ := ζ 0 ^ 2 + ζ 1 ^ 2 / S ^ 2 + ζ 2 ^ 2

/-- The pressure term `Π = (2ζ₂α₁ + (ζ₁ + εζ₃)α₂)/m` of Lemma 2.3. -/
def strongShearPressure (S ε : ℝ) (ζ : Vec3) (α₁ α₂ : ℝ) : ℝ :=
  (2 * ζ 1 * α₁ + (ζ 0 + ε * ζ 2) * α₂) / scaledNormSq S ζ

/-- The coefficients of the system for `(α₁, α₂)` in Lemma 2.3: the right-hand sides
of that system are `strongShearMatrix S ε ζ` applied to `(α₁, α₂)`
(`strongShearMatrix_mulVec`). -/
def strongShearMatrix (S ε : ℝ) (ζ : Vec3) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * ζ 0 * ζ 1 / scaledNormSq S ζ,
      -1 + ζ 0 * (ζ 0 + ε * ζ 2) / scaledNormSq S ζ;
    -(1 - 1 / (2 * S ^ 2)) + ε / (2 * S ^ 2) * (ζ 0 / ζ 2) +
        ζ 1 / S ^ 2 * (2 * ζ 1 / scaledNormSq S ζ),
      ε / (2 * S ^ 2) * (ζ 1 / ζ 2) + ζ 1 / S ^ 2 * ((ζ 0 + ε * ζ 2) / scaledNormSq S ζ)]

/-- The smallness condition (2.7) with the absolute constant `C₀`:
`C₀ε ≤ 1` and `C₀T^{C₀}δ ≤ ε`. -/
def FiniteSmallness (w : PhysicalAmplification I t₀) (T : ℝ) (C₀ : ℕ) : Prop :=
  (C₀ : ℝ) * w.ratio ≤ 1 ∧ (C₀ : ℝ) * T ^ C₀ * w.errorSize ≤ w.ratio

/-! ## Subsection 2.2.2: the reference solution -/

/-- `Y` solves the Riccati problem (2.12) on `τ ≥ 0`:
`Y' = cos²φ (1 - ε tan φ) - ετ sin 2φ Y - Y²`, `Y(0) = 1`, with `φ` from (2.4).
Derivatives are taken within `[0, ∞)`. -/
def ReferenceSlope (ε : ℝ) (Y : ℝ → ℝ) : Prop :=
  Y 0 = 1 ∧ ∀ τ ∈ Ici (0 : ℝ), HasDerivWithinAt Y
    (Real.cos (referenceAngle ε τ) ^ 2 * (1 - ε * Real.tan (referenceAngle ε τ)) -
      ε * τ * Real.sin (2 * referenceAngle ε τ) * Y τ - Y τ ^ 2) (Ici 0) τ

/-- The reference amplitude `a_ref(τ) = exp ∫₀^τ Y`
(`sections/03_amplification.tex:445-450`). -/
def referenceAmplitude (Y : ℝ → ℝ) (τ : ℝ) : ℝ := Real.exp (∫ s in (0 : ℝ)..τ, Y s)

/-! ## Sanity lemmas for the definitions -/

/-- The angle of (2.4) satisfies `0 ≤ φ < π/2` for `ε ≥ 0`. -/
theorem referenceAngle_mem {ε : ℝ} (hε : 0 ≤ ε) (τ : ℝ) :
    0 ≤ referenceAngle ε τ ∧ referenceAngle ε τ < Real.pi / 2 :=
  ⟨Real.arctan_nonneg.mpr (by positivity), Real.arctan_lt_pi_div_two _⟩

/-- The angle of (2.4) satisfies `tan φ = ετ²/2`. -/
theorem tan_referenceAngle (ε τ : ℝ) : Real.tan (referenceAngle ε τ) = ε * τ ^ 2 / 2 :=
  Real.tan_arctan _

/-- The right-hand sides of the system for `(α₁, α₂)` in Lemma 2.3 are the products of
`strongShearMatrix` with `(α₁, α₂)`. -/
theorem strongShearMatrix_mulVec (S ε : ℝ) (ζ : Vec3) (α₁ α₂ : ℝ) :
    strongShearMatrix S ε ζ 0 0 * α₁ + strongShearMatrix S ε ζ 0 1 * α₂ =
        -α₂ + ζ 0 * strongShearPressure S ε ζ α₁ α₂ ∧
      strongShearMatrix S ε ζ 1 0 * α₁ + strongShearMatrix S ε ζ 1 1 * α₂ =
        -(1 - 1 / (2 * S ^ 2)) * α₁ + ε / (2 * S ^ 2) * ((ζ 0 * α₁ + ζ 1 * α₂) / ζ 2) +
          ζ 1 / S ^ 2 * strongShearPressure S ε ζ α₁ α₂ := by
  simp only [strongShearMatrix, strongShearPressure, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  constructor <;> ring

end

end TorusEuler.Paper
