import TorusEuler.Paper.S2.Vocabulary

/-! # Statements of Section 2

The faithful statements `TorusEuler.Paper.Statement.lemma_2_1` through
`TorusEuler.Paper.Statement.proposition_2_8` of the latest manuscript
(`sections/02_affine.tex`, `sections/03_amplification.tex`), in its notation and
numbering. The vocabulary and the dictionary between the setting of Subsection 2.2.1
and the library structure `MovingWaveVector.PhysicalAmplification` are in
`TorusEuler.Paper.S2.Vocabulary`.

Common representation choices, recalled in each docstring:

* "Fix an absolute constant `C₀`, sufficiently large" is `∃ N, ∀ C₀ ≥ N` with
  `C₀ : ℕ`; every other constant `C` and exponent of the subsection is chosen before
  `N`, hence independent of `C₀`. A bound `CT^Cδ` is written `C * T ^ p * δ` with a
  real factor `C` and a natural exponent `p`.
* Physical time: a compact window `I` containing the slab `t₀ ≤ t ≤ t₀ + T/r`, on
  which the wave equations hold and over which `δ` takes its suprema; the text is the
  case `I = [t₀, t₀ + T/r]`. Functions of `τ` are evaluated at `t = w.clock τ`, and
  derivatives in `τ` are taken within `[0, T]`.
* "sup over `0 ≤ τ ≤ T`" is `∀ τ ∈ Icc 0 T`; `|·|` of a vector is the Euclidean norm;
  the norm of the 2×2 matrix `ℰ` is the operator norm on `ℝ × ℝ` with the max norm.
* The matrix norms `|B|` and `|E_c|` in `δ` of (2.6) (`w.errorSize`) are operator norms
  for the Euclidean norm on `ℝ³`. The text does not name a matrix norm; the operator
  norm is the smallest norm compatible with the uses `|B| ≥ |E₁·BE₂|` and
  `|E_c v| ≤ |E_c||v|` in the text, so the hypothesis (2.7) is the weakest and the
  conclusions `CT^Cδ` are the strongest among the natural readings.
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper

open MovingWaveVector

namespace Statement

/-- **Lemma 2.1** (`cc:lem:wave`, sections/02_affine.tex:9). Let the wave vector `k` and
the amplitude vector `a` satisfy (2.1) over a trace-free `D` with `D' + D²` symmetric.
If `k·a = 0`, then `Dx + aF(k·x)` is divergence free and solves the Euler equations on
`ℝ³` with pressure `-x·(D'+D²)x/2 - p_w P(k·x)`. If `k(t₀) ≠ 0`, `a(t₀) ≠ 0` and
`k(t₀)·a(t₀) = 0`, both vectors stay nonzero and perpendicular.

Equations: (2.1) (`WaveOn` and the relation `k·a = 0`).

Representation: time runs over an order-connected set `J` with unique derivatives (the
interval of existence of `D`), with derivatives within `J`; `D'` is the derivative of
`D` and the symmetry of `D' + D²` is self-adjointness; the profile `F` is only assumed
differentiable and `P' = F` (the text's `F` is smooth, odd, `1`-periodic with
`F'(0) = 1`, and `⟨P⟩ = 0`), and `k ≠ 0` is not assumed in the Euler part: both are
generalizations. "Solves the Euler equations" is the momentum equation
`∂ₜu + (u·∇)u + ∇p = 0` with `∂ₜ` the derivative within `J`, together with the
differentiability of `u` in `t` and `x` and of the pressure in `x`. Persistence is
stated for every `t ∈ J` (the text: every `t ≥ t₀`). -/
def lemma_2_1 : Prop :=
  ∀ {J : Set ℝ}, J.OrdConnected → UniqueDiffOn ℝ J →
  ∀ {F P : ℝ → ℝ}, Differentiable ℝ F → (∀ z, HasDerivAt P (F z) z) →
  ∀ {D D' : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3},
    (∀ t ∈ J, HasDerivWithinAt D (D' t) J t) →
    (∀ t ∈ J, IsSelfAdjoint (D' t + (D t).comp (D t))) →
    (∀ t ∈ J, LinearMap.trace ℝ Vec3 (D t).toLinearMap = 0) →
    WaveOn J D k a →
    ((∀ t ∈ J, ⟪k t, a t⟫_ℝ = 0) → ∀ t ∈ J, ∀ x : Vec3,
      let u := affineWaveVelocity F D k a
      let p := affineWavePressure P (D' t + (D t).comp (D t))
        (affineWavePressureCoeff (D t) (k t) (a t)) (k t)
      DifferentiableWithinAt ℝ (fun r => u r x) J t ∧ DifferentiableAt ℝ (u t) x ∧
        DifferentiableAt ℝ p x ∧
        derivWithin (fun r => u r x) J t + fderiv ℝ (u t) x (u t x) + gradient p x = 0 ∧
        divergence (u t) x = 0) ∧
    (∀ ⦃t₀ : ℝ⦄, t₀ ∈ J → k t₀ ≠ 0 → a t₀ ≠ 0 → ⟪k t₀, a t₀⟫_ℝ = 0 →
      ∀ t ∈ J, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0)

/-- **Lemma 2.2** (`cc:lem:frame`, sections/02_affine.tex:65). Let `B` be trace free and
let `k ≠ 0`, `a ≠ 0` satisfy (2.1) with `D = B`. With `E₁ = k/|k|`, `E₂ = a/|a|`,
`E₃ = E₁ × E₂`, `B_ij = E_i·BE_j`, `σ = |k||a|`, `ν = B₁₂`, `η = B₃₂`, the frame is
orthonormal and (2.2) holds: `E₁' = -νE₂ - B₁₃E₃`, `E₂' = νE₁ - ηE₃`,
`E₃' = B₁₃E₁ + ηE₂`, `(log σ)' = B₃₃`.

Equations: (2.1), (2.2).

Representation: time runs over an arbitrary set `J`, derivatives within `J`; `B` need
not be smooth (only trace free on `J`); the frame is `MovingWaveVector.frame k a`
and `B_ij` is `MovingWaveVector.entry (E t) (B t) (i-1) (j-1)` (indices from `0`); the
orthonormality of the frame, asserted in the text ("this orthonormal frame"), is
stated explicitly. -/
def lemma_2_2 : Prop :=
  ∀ {J : Set ℝ} {B : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3},
    (∀ t ∈ J, LinearMap.trace ℝ Vec3 (B t).toLinearMap = 0) →
    WaveOn J B k a →
    (∀ t ∈ J, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0) →
    ∀ t ∈ J,
      let E := frame k a
      let ν := entry (E t) (B t) 0 1
      let η := entry (E t) (B t) 2 1
      Orthonormal ℝ (E t) ∧
        HasDerivWithinAt (fun u => E u 0) (-ν • E t 1 - entry (E t) (B t) 0 2 • E t 2) J t ∧
        HasDerivWithinAt (fun u => E u 1) (ν • E t 0 - η • E t 2) J t ∧
        HasDerivWithinAt (fun u => E u 2) (entry (E t) (B t) 0 2 • E t 0 + η • E t 1) J t ∧
        HasDerivWithinAt (fun u => Real.log (‖k u‖ * ‖a u‖)) (entry (E t) (B t) 2 2) J t

/-- **Lemma 2.3** (`cc:lem:strong-shear`, sections/03_amplification.tex:113). In the model
case on `0 ≤ τ ≤ T` (`B₁₂ = ν`, `B₃₂ = η`, other entries of `B` in the frame zero,
`E_c = 0`): `σ_p = σ`; the scaled components of the wave vector satisfy
`ζ₁' = -(1 + 1/(2S²))ζ₂`, `ζ₂' = -εζ₃`, `ζ₃' = (ε/(2S²))ζ₂`; where `ζ₃ ≠ 0`, the
components `α₁, α₂` of every amplitude vector satisfy
`α₁' = -α₂ + ζ₁Π`,
`α₂' = -(1 - 1/(2S²))α₁ + (ε/(2S²))(ζ₁α₁ + ζ₂α₂)/ζ₃ + (ζ₂/S²)Π`,
`Π = (2ζ₂α₁ + (ζ₁ + εζ₃)α₂)/m`. As `S → ∞` with `ε` and `T` fixed, `ζ → ζ₀`
uniformly on `[0, T]` and the coefficients of the `(α₁, α₂)` system converge uniformly
on `[0, T]` to those of (2.5).

Equations: (2.3) (`zeta`, `alpha`), (2.4) (`referenceAngle`, `zetaRef`), (2.5)
(`referenceSystemMatrix`).

Representation: the setting of Subsection 2.2.1 is a `PhysicalAmplification` on a
window `I` containing the slab (see the module docstring of `Paper.S2.Vocabulary`);
the standing assumption `T ≥ 2` is a hypothesis; primes are derivatives in `τ`
within `[0, T]` at `t = t₀ + τ/r`; `Π` is `strongShearPressure` and
`m = scaledNormSq S ζ`. The limit "as `S → ∞` with `ε` and `T` fixed, uniformly on
`[0, T]`" is: for every tolerance there is `S₀` such that every model configuration
with ratio `ε` and `S ≥ S₀` satisfies the bounds at every `τ ∈ [0, T]` (in the model
case `ζ` depends only on `S` and `ε`). "The coefficients of this system" are the
entries of `strongShearMatrix` (`strongShearMatrix_mulVec`), defined where `ζ₃ ≠ 0`,
which the limit clause asserts; `|ζ - ζ₀|` is the Euclidean norm. -/
def lemma_2_3 : Prop :=
  (∀ {I : Set ℝ} {t₀ T lam : ℝ} (w : PhysicalAmplification I t₀) {k : ℝ → Vec3},
    2 ≤ T → MapsTo w.clock (Icc 0 T) I → ModelCase w T → NewWaveVector w lam k →
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
          ζ τ 1 / S ^ 2 * Pm) (Icc 0 T) τ)) ∧
  (∀ ε T : ℝ, 2 ≤ T → ∀ tol : ℝ, 0 < tol → ∃ S₀ : ℝ,
    ∀ {I : Set ℝ} {t₀ lam : ℝ} (w : PhysicalAmplification I t₀) {k : ℝ → Vec3},
      MapsTo w.clock (Icc 0 T) I → ModelCase w T → NewWaveVector w lam k →
      w.ratio = ε → S₀ ≤ w.shear →
      ∀ τ ∈ Icc 0 T,
        ‖zeta w lam k τ - zetaRef ε τ‖ ≤ tol ∧ zeta w lam k τ 2 ≠ 0 ∧
        ∀ i j, |strongShearMatrix w.shear ε (zeta w lam k τ) i j -
          referenceSystemMatrix ε τ i j| ≤ tol)

/-- **Lemma 2.4** (`cc:uf:exact:lem:additive`, sections/03_amplification.tex:265). Assume
(2.7). The scaled components of the wave vector satisfy (2.10),
`sup|ζ - ζ₀| ≤ CT^Cδ ≤ 1/2` and `sup| |k|²cos²φ/λ² - 1 | ≤ CT^Cδ ≤ 1/2`, hence (2.11),
`1/2 ≤ ζ₃ ≤ 3/2` and `|ζ| ≤ 3T²`. The components `α₁, α₂` of every amplitude vector
satisfy `d/dτ (α₁, α₂) = {-[[ετ sin 2φ, cos²φ(1 - ε tan φ)], [1, 0]] + ℰ(τ)}(α₁, α₂)`
with `sup|ℰ| ≤ CT^Cδ`, where `ℰ` is the same for all amplitude vectors.

Equations: (2.3), (2.4), (2.6) (`w.errorSize`), (2.7) (`FiniteSmallness`), (2.10),
(2.11); the displayed matrix is `referenceSystemMatrix`, the matrix of (2.5).

Exports (the ledger `exports` of row 2.4; extra conclusions that the statement of the
text does not contain): (a) `ℰ` is continuous on `[0, T]` (true by construction; the
variation of constants for `Ψ` in the proof of Lemma 2.6,
sections/03_amplification.tex:640-648, needs it); (b) `sup|σ_p/σ - 1| ≤ 2Tδ`, proved at
the beginning of the proof (sections/03_amplification.tex:302-309) and read by the proof
of Lemma 2.7 (sections/03_amplification.tex:847-850, "the coefficients differ from their
reference values by at most `CTδ`"; `σ_p/σ` enters (2.20)-(2.21) through the
coefficient `f₂`, sections/03_amplification.tex:751).

Representation: common choices of this module (`∃ C p N, ∀ C₀ ≥ N`; window `I`
containing the slab with `δ` over `I`; operator norms for `|B|`, `|E_c|` in `δ`;
derivatives within `[0, T]`); `ℰ(τ)` is a continuous linear map on `ℝ × ℝ`, `|ℰ|` its
operator norm for the max norm, and the reference part is
`MovingAmplitude.pairOperator (referenceSystemMatrix ε τ)`; `|ζ - ζ₀|` and `|ζ|` are
Euclidean norms. -/
def lemma_2_4 : Prop :=
  ∃ (C : ℝ) (p N : ℕ), ∀ {C₀ : ℕ}, N ≤ C₀ →
  ∀ {I : Set ℝ} {t₀ T lam : ℝ} (w : PhysicalAmplification I t₀) {k : ℝ → Vec3},
    2 ≤ T → MapsTo w.clock (Icc 0 T) I → FiniteSmallness w T C₀ → NewWaveVector w lam k →
    let ε := w.ratio
    let δ := w.errorSize
    let ζ := zeta w lam k
    C * T ^ p * δ ≤ 1 / 2 ∧
    (∀ τ ∈ Icc 0 T, ‖ζ τ - zetaRef ε τ‖ ≤ C * T ^ p * δ) ∧
    (∀ τ ∈ Icc 0 T,
      |‖k (w.clock τ)‖ ^ 2 * Real.cos (referenceAngle ε τ) ^ 2 / lam ^ 2 - 1| ≤
        C * T ^ p * δ) ∧
    (∀ τ ∈ Icc 0 T, 1 / 2 ≤ ζ τ 2 ∧ ζ τ 2 ≤ 3 / 2 ∧ ‖ζ τ‖ ≤ 3 * T ^ 2) ∧
    (∃ ℰ : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      (∀ τ ∈ Icc 0 T, ‖ℰ τ‖ ≤ C * T ^ p * δ) ∧
      (∀ a : ℝ → Vec3, AmplitudeVector w k a → ∀ τ ∈ Icc 0 T,
        HasDerivWithinAt (fun s => (alpha w a s 0, alpha w a s 1))
          (MovingAmplitude.pairOperator (referenceSystemMatrix ε τ)
              (alpha w a τ 0, alpha w a τ 1) + ℰ τ (alpha w a τ 0, alpha w a τ 1))
          (Icc 0 T) τ) ∧
      ContinuousOn ℰ (Icc 0 T)) ∧
    (∀ τ ∈ Icc 0 T,
      |‖w.kp (w.clock τ)‖ * ‖w.ap (w.clock τ)‖ / w.initialStrength - 1| ≤ 2 * T * δ)

/-- **Lemma 2.5** (`cc:lem:model`, sections/03_amplification.tex:452). Let `0 < ε ≤ 1`. The
solution `Y` of (2.12) exists for all `τ ≥ 0`, satisfies `|Y| ≤ 1` and has the form
(2.13), `Y = (1 + e)cos φ - (1/4)ετ sin 2φ` with `0 ≤ e ≤ ε/8`. The reference amplitude
satisfies (2.14), `a_ref(τ) = √(cos φ(τ)) exp ∫₀^τ (1 + e)cos φ`. `Y` has exactly one
zero `τ_m`, with `2 ≤ ετ_m ≤ 3`; it is positive before and negative after, so `a_ref`
is largest at `τ_m`, and `log a_ref(τ_m) ≥ ε^{-1/2} - 1`.

Equations: (2.4) (`referenceAngle`), (2.12) (`ReferenceSlope`), (2.13), (2.14); the
reference amplitude `a_ref` is `referenceAmplitude`.

Representation: "the solution `Y`" is rendered as existence of a solution on
`[0, ∞)` (derivatives within `[0, ∞)`), uniqueness on `[0, ∞)`, and the remaining
assertions for every solution; the function `e` of (2.13) is the same in (2.14); all
assertions concern `τ ≥ 0`; "exactly one zero" is `Y τ = 0 ↔ τ = τ_m` for `τ ≥ 0`;
"largest" is over `τ ≥ 0`; `ε^{-1/2}` is `(√ε)⁻¹`. -/
def lemma_2_5 : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    (∃ Y : ℝ → ℝ, ReferenceSlope ε Y) ∧
    ∀ Y : ℝ → ℝ, ReferenceSlope ε Y →
      (∀ Z : ℝ → ℝ, ReferenceSlope ε Z → EqOn Y Z (Ici 0)) ∧
      (∀ τ ∈ Ici (0 : ℝ), |Y τ| ≤ 1) ∧
      ∃ e : ℝ → ℝ, (∀ τ ∈ Ici (0 : ℝ), 0 ≤ e τ ∧ e τ ≤ ε / 8) ∧
        (∀ τ ∈ Ici (0 : ℝ), Y τ = (1 + e τ) * Real.cos (referenceAngle ε τ) -
          ε * τ * Real.sin (2 * referenceAngle ε τ) / 4) ∧
        (∀ τ ∈ Ici (0 : ℝ), referenceAmplitude Y τ =
          Real.sqrt (Real.cos (referenceAngle ε τ)) *
            Real.exp (∫ s in (0 : ℝ)..τ, (1 + e s) * Real.cos (referenceAngle ε s))) ∧
        ∃ τm : ℝ, (∀ τ ∈ Ici (0 : ℝ), Y τ = 0 ↔ τ = τm) ∧ 2 ≤ ε * τm ∧ ε * τm ≤ 3 ∧
          (∀ τ ∈ Ico 0 τm, 0 < Y τ) ∧ (∀ τ ∈ Ioi τm, Y τ < 0) ∧
          (∀ τ ∈ Ici (0 : ℝ), referenceAmplitude Y τ ≤ referenceAmplitude Y τm) ∧
          (Real.sqrt ε)⁻¹ - 1 ≤ Real.log (referenceAmplitude Y τm)

/-- **Lemma 2.6** (`cc:lem:finite-comparison`, sections/03_amplification.tex:597). Assume
(2.7) and let `a` be the amplitude vector with `a(t₀) = -E₁(t₀)/S + E₂(t₀)`, that is
`(α₁, α₂)(0) = (-1, 1)`. Then `α₂ > 0` on `0 ≤ τ ≤ T` and (2.17) holds:
`|α₁/α₂ + Y| ≤ CT^Cδ` and `α₂ ≤ |a| ≤ (1 + CT^Cδ)α₂`; moreover (2.18),
`|log(|a|/a_ref)| ≤ ε`. For `0 ≤ τ₁ ≤ τ₂ ≤ T` the map `Φ(τ₂, τ₁)` sending `b(τ₁)` to
`b(τ₂)` for every amplitude vector `b` maps the plane perpendicular to `k(τ₁)` onto the
plane perpendicular to `k(τ₂)`, and `‖Φ(τ₂, τ₁)‖ ≤ CS|a(τ₂)|/|a(τ₁)|`.

Equations: (2.3), (2.7), (2.12) (`Y`), (2.17), (2.18); `a_ref` is `referenceAmplitude`.

Representation: common choices of this module (`∃ C p N, ∀ C₀ ≥ N`; window `I`
containing the slab with `δ` over `I`; operator norms for `|B|`, `|E_c|` in `δ`); "the
solution `Y` of (2.12)" (with
`ε = w.ratio`, unique by Lemma 2.5) is rendered as "every solution `Y` of (2.12)",
quantified only over the two assertions that mention `Y` or `a_ref` (the first bound of
(2.17) and (2.18)); `Φ(τ₂, τ₁)` is a continuous linear equivalence between the planes
`transversePlane (k(τ₁))` and `transversePlane (k(τ₂))` (so it is onto), characterized
by `Φ (b(τ₁)) = b(τ₂)` for every amplitude vector `b`; the constant of the `Φ` bound is
the explicit absolute constant `252e`. -/
def lemma_2_6 : Prop :=
  ∃ (C : ℝ) (p N : ℕ), ∀ {C₀ : ℕ}, N ≤ C₀ →
  ∀ {I : Set ℝ} {t₀ T lam : ℝ} (w : PhysicalAmplification I t₀) {k a : ℝ → Vec3},
    2 ≤ T → MapsTo w.clock (Icc 0 T) I → FiniteSmallness w T C₀ → NewWaveVector w lam k →
    AmplitudeVector w k a → a t₀ = (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1 →
    let ε := w.ratio
    let δ := w.errorSize
    let α := alpha w a
    (∀ τ ∈ Icc 0 T, 0 < α τ 1) ∧
    (∀ Y : ℝ → ℝ, ReferenceSlope ε Y →
      ∀ τ ∈ Icc 0 T, |α τ 0 / α τ 1 + Y τ| ≤ C * T ^ p * δ) ∧
    (∀ τ ∈ Icc 0 T,
      α τ 1 ≤ ‖a (w.clock τ)‖ ∧ ‖a (w.clock τ)‖ ≤ (1 + C * T ^ p * δ) * α τ 1) ∧
    (∀ Y : ℝ → ℝ, ReferenceSlope ε Y →
      ∀ τ ∈ Icc 0 T, |Real.log (‖a (w.clock τ)‖ / referenceAmplitude Y τ)| ≤ ε) ∧
    (∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ T →
      ∃ Φ : transversePlane (k (w.clock τ₁)) ≃L[ℝ] transversePlane (k (w.clock τ₂)),
        (∀ b : ℝ → Vec3, AmplitudeVector w k b →
          ∀ v : transversePlane (k (w.clock τ₁)), (v : Vec3) = b (w.clock τ₁) →
            (Φ v : Vec3) = b (w.clock τ₂)) ∧
        ‖Φ.toContinuousLinearMap‖ ≤
          252 * Real.exp 1 * w.shear * (‖a (w.clock τ₂)‖ / ‖a (w.clock τ₁)‖))

/-- **Lemma 2.7** (`cc:lem:new-wave-couplings`, sections/03_amplification.tex:718). Assume
(2.7) and let `a` be the amplitude vector of Lemma 2.6. With `E₁,₊ = k/|k|`,
`E₂,₊ = a/|a|`, `E₃,₊ = E₁,₊ × E₂,₊`, `ν₊ = E₁,₊·ME₂,₊` and `η₊ = E₃,₊·ME₂,₊`:
`ν₊ ≥ εν/2` on `0 ≤ τ ≤ T`, and where `ε tan φ ≥ 1`, that is for `√2/ε ≤ τ ≤ T`,
(2.19) holds: `|ν₊/ν - 1| ≤ ε` and `|(η₊/ν₊)/cos φ - 1| ≤ 1/2`.

Equations: (2.4), (2.7), (2.19).

Representation: common choices of this module (`∃ N, ∀ C₀ ≥ N`; window `I` containing
the slab with `δ` over `I`; operator norms for `|B|`, `|E_c|` in `δ`); `ν₊` and `η₊` at
`t = t₀ + τ/r` are `νplus τ` and `ηplus τ`, the library couplings
`w.physicalNu k a t = ⟪k/|k|, M (a/|a|)⟫` and
`w.physicalEta k a t = ⟪(k/|k|) × (a/|a|), M (a/|a|)⟫`; the late range is written
`√2/ε ≤ τ`. -/
def lemma_2_7 : Prop :=
  ∃ N : ℕ, ∀ {C₀ : ℕ}, N ≤ C₀ →
  ∀ {I : Set ℝ} {t₀ T lam : ℝ} (w : PhysicalAmplification I t₀) {k a : ℝ → Vec3},
    2 ≤ T → MapsTo w.clock (Icc 0 T) I → FiniteSmallness w T C₀ → NewWaveVector w lam k →
    AmplitudeVector w k a → a t₀ = (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1 →
    let ε := w.ratio
    let ν := w.firstCoupling
    let νplus := fun τ => w.physicalNu k a (w.clock τ)
    let ηplus := fun τ => w.physicalEta k a (w.clock τ)
    (∀ τ ∈ Icc 0 T, ε * ν / 2 ≤ νplus τ) ∧
    (∀ τ ∈ Icc 0 T, Real.sqrt 2 / ε ≤ τ →
      |νplus τ / ν - 1| ≤ ε ∧
        |ηplus τ / νplus τ / Real.cos (referenceAngle ε τ) - 1| ≤ 1 / 2)

/-- **Proposition 2.8** (`cc:prop:finite-return`, sections/03_amplification.tex:894).
Assume (2.7), let `a` be the amplitude vector of Lemma 2.6 with the couplings of
Lemma 2.7, and suppose `0 < ε₊ ≤ ε/32` and `T ≥ 2(εε₊)^{-1/2}`. Then the interval
`τ_m ≤ τ ≤ 2(εε₊)^{-1/2}`, where `τ_m ≥ 2/ε` is the zero of `Y` (Lemma 2.5), contains a
crossing (`η₊/ν₊ = ε₊`). At every crossing there, `σ₊ = |a(τ)||k(τ)|` satisfies (2.23),
`C⁻¹(εε₊)^{-1/2} ≤ σ₊/(λ max_{[0,T]}|a|) ≤ C(εε₊)^{-1/2}`, and (2.24) holds:
`|a(τ)| ≤ exp(3 - ε^{-1/2}) max_{[0,T]}|a|` for `0 ≤ τ ≤ 1`.

Equations: (2.7), (2.12) (`Y`), (2.23), (2.24).

Representation: common choices of this module (`∃ N, ∀ C₀ ≥ N`; window `I` containing
the slab with `δ` over `I`; operator norms for `|B|`, `|E_c|` in `δ`); `ε₊` is `εplus`,
the strength `σ₊ = |a(τ)||k(τ)|` of the new wave is `σplus τ` (not the strength `σ_p` of
the preceding wave), `ratioPlus τ` is the ratio `η₊/ν₊` of the couplings of Lemma 2.7
(`w.physicalEta k a t / w.physicalNu k a t` at `t = t₀ + τ/r`), and `H` is the right end
`2(εε₊)^{-1/2}` of the interval; `τ_m` is given by an existence clause with its
defining property, "the zero in `[0, ∞)` of every solution `Y` of (2.12) with
`ε = w.ratio`" (`Y` and its zero are unique by Lemma 2.5), together with the recalled
bound `τ_m ≥ 2/ε`; `max_{[0,T]}|a|` is the greatest element `peak` of
`{|a(t₀ + τ/r)| : 0 ≤ τ ≤ T}`, whose existence is asserted; the constant `C` of (2.23) is
explicit: `e⁻¹/4` in the lower bound and `18e³` in the upper bound (so `C = 18e³` works
on both sides); `(εε₊)^{-1/2}` is `(√(εε₊))⁻¹`. -/
def proposition_2_8 : Prop :=
  ∃ N : ℕ, ∀ {C₀ : ℕ}, N ≤ C₀ →
  ∀ {I : Set ℝ} {t₀ T lam εplus : ℝ} (w : PhysicalAmplification I t₀) {k a : ℝ → Vec3},
    2 ≤ T → MapsTo w.clock (Icc 0 T) I → FiniteSmallness w T C₀ → NewWaveVector w lam k →
    AmplitudeVector w k a → a t₀ = (-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1 →
    0 < εplus → εplus ≤ w.ratio / 32 → 2 / Real.sqrt (w.ratio * εplus) ≤ T →
    let ε := w.ratio
    let H := 2 / Real.sqrt (ε * εplus)
    let ratioPlus := fun τ => w.physicalEta k a (w.clock τ) / w.physicalNu k a (w.clock τ)
    let σplus := fun τ => ‖a (w.clock τ)‖ * ‖k (w.clock τ)‖
    ∃ τm : ℝ, (∀ Y : ℝ → ℝ, ReferenceSlope ε Y → ∀ τ ∈ Ici (0 : ℝ), Y τ = 0 ↔ τ = τm) ∧
      2 / ε ≤ τm ∧
      (∃ τ ∈ Icc τm H, ratioPlus τ = εplus) ∧
      ∃ peak : ℝ, IsGreatest ((fun τ => ‖a (w.clock τ)‖) '' Icc 0 T) peak ∧
        (∀ τ ∈ Icc τm H, ratioPlus τ = εplus →
          Real.exp (-1) / 4 * (Real.sqrt (ε * εplus))⁻¹ ≤ σplus τ / (lam * peak) ∧
          σplus τ / (lam * peak) ≤ 18 * Real.exp 3 * (Real.sqrt (ε * εplus))⁻¹) ∧
        (∀ τ ∈ Icc (0 : ℝ) 1, ‖a (w.clock τ)‖ ≤ Real.exp (3 - (Real.sqrt ε)⁻¹) * peak)

end Statement

end TorusEuler.Paper
