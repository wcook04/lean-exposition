import TorusEuler.Paper.SBD.Vocabulary

/-! # Statements of Lemma B.1, Lemmas D.1, D.2, D.3 and display (D.2)

Faithful statements, as closed propositions, of the numbered results of
Appendix B (`sections/appB_cutoff.tex`) and Appendix D
(`sections/appD_finite_norms.tex`) of the latest manuscript, and of the
display (D.2) before Lemma D.1, which later proofs cite
(`Statement.Text.eq_D_2`, proposed to the ledger as the node `Text eq_D_2`).
Equation numbers are those of the compiled latest manuscript (`main.aux`):
(B.1) `cc:uf:trunc:eq:lp`, (B.2) `cc:uf:trunc:eq:tail`, (D.1)
`cc:uf:trunc:eq:field-norm`, (D.2) `cc:uf:trunc:eq:holder-sup`, (D.3)
`cc:uf:trunc:eq:deriv`, (D.4) `cc:uf:trunc:eq:product`, (D.5)
`cc:uf:trunc:eq:phase-ops`, (D.6) `cc:uf:trunc:eq:power`, (D.7)
`cc:uf:trunc:eq:slow`.

All five are leaves of the proof spine: their proofs cite no other numbered
result. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff ENNReal

namespace TorusEuler.Paper

local notation "Labels" => UnitAddTorus (Fin 3)

open AppendixB AppendixD

/-- **Lemma B.1** (`cc:uf:trunc:lem:cutoff`, sections/appB_cutoff.tex:12).
For a cutoff symbol `ψ` as fixed at the start of Appendix B, let `S_Λ`
multiply the Fourier mode `e^{2πiξ·x}`, `ξ ∈ ℤ³`, by `ψ(ξ/Λ)`. Then `S_Λ`
commutes with derivatives, preserves parity and divergence freeness, and maps
into fields with frequencies at most `2Λ`; its operator norms on `L^∞` and on
`C^{0,1/2}` are bounded by a constant depending only on `ψ`; Bernstein's
inequality (B.1) `∑_{|β|=m} ‖∂^β f‖_∞ ≤ C_m Λ^m ‖f‖_∞` holds for every
normed-space-valued field `f` with frequencies at most `4Λ`; and the tail
bound (B.2) `‖(Id - S_Λ) f‖_{C^{s,1/2}} ≤ C_M Λ^{s-M} ‖f‖_{C^{M,1/2}}`
holds for `0 ≤ s ≤ M`. The constants `C_m`, `C_M` depend only on their
index and on `ψ`: they are chosen (as `Cb`, `Ct`, together with the operator
bound `Cop`) after `ψ` and before `Λ`, the target space and the field.

The cutoff is stated for two classes of fields. (i) Fields with values in a
complex Banach space `E`, where `S_Λ` is `smoothFourierCutoff ψ Λ`, the
finite Fourier synthesis whose coefficients are `ψ(k/Λ) ĝ(k)` (first
conjunct); a field with values in another real space `Q` is cut off as
`R ∘ S_Λ ∘ J` for a complexification `J : Q → Q_ℂ` with real part `R` (as in
`realTensorFourierCutoff`). (ii) Real velocity fields, where
`S_Λ` is `realVectorFourierCutoff ψ Λ` (the real part of the complex cutoff
of the complexification), with the same multiplier (first conjunct of the
real block). The clauses are, in order: multiplier; commutation with spatial
derivatives (every coordinate word `β`, for the complex cutoff; first-order
coordinate derivatives, for the real cutoff) and with time derivatives on a
closed time slab (real cutoff); parity (`g(-z) = c g(z)` for any real `c`,
covering odd and even fields); divergence freeness (smooth real fields);
frequencies at most `2Λ`; `L^∞` (essential supremum, complex) and uniform
norm and `C^{0,1/2}` operator bounds; (B.2); and finally (B.1).

Representation: the torus `𝕋³` is `UnitAddTorus (Fin 3)` and spatial norms
and derivatives are taken on the `ℤ³`-periodic lift `x ↦ g (toUnitTorus x)`
to `ℝ³`; the frequency of the mode `k ∈ ℤ³` is `‖latticeVector k‖`; the
`C^{m,1/2}` norm is `spatialHolderHalfNorm m` (the sum over orders `j ≤ m` of
the supremum and the 1/2-Hölder seminorm of the `j`-th Fréchet derivative,
operator norm) and membership is `SpatialHolderHalf m`; multi-indices of
order `m` in (B.1) are the nondecreasing coordinate words `Fin m → Fin 3`;
"frequencies at most `4Λ`" for a field with values in a real normed space `V`
is `RealNormedTorusFourierBand (4Λ)` (vanishing of the Fourier coefficients
of every scalar measurement `l ∘ g`, `l ∈ V*`), and (B.1) also records that
each supremum is finite; the radial symbol is weakened to an even one
(`CutoffSymbol`); the statement holds for every `Λ > 0`, which contains the
manuscript's range `Λ ≥ 1`. -/
def Statement.lemma_B_1 : Prop :=
  ∀ ψ : Vec3 → ℝ, CutoffSymbol ψ →
  ∃ (Cop : ℝ) (Cb Ct : ℕ → ℝ), 0 ≤ Cop ∧ (∀ m, 0 ≤ Cb m) ∧ (∀ M, 0 ≤ Ct M) ∧
  ∀ Λ : ℝ, 0 < Λ →
    -- (i) complex-Banach-valued fields, `S_Λ = smoothFourierCutoff ψ Λ`
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
      -- multiplier: `(S_Λ g)^(k) = ψ(k/Λ) ĝ(k)`
      (∀ (g : Labels → E) (k : Fin 3 → ℤ),
        mFourierCoeff (smoothFourierCutoff ψ Λ g) k =
          ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff g k) ∧
      -- commutes with spatial derivatives: `∂^β S_Λ g = S_Λ ∂^β g`
      (∀ (m : ℕ) (β : Fin m → Fin 3) (g d : C(Labels, E)),
        ContDiff ℝ m (fun x => g (toUnitTorus x)) →
        (∀ x, d (toUnitTorus x) = iteratedFDeriv ℝ m (fun y => g (toUnitTorus y)) x
          (fun i => EuclideanSpace.single (β i) 1)) →
        ∀ x, iteratedFDeriv ℝ m (fun y => smoothFourierCutoff ψ Λ g (toUnitTorus y)) x
          (fun i => EuclideanSpace.single (β i) 1) = smoothFourierCutoff ψ Λ d (toUnitTorus x)) ∧
      -- preserves parity
      (∀ (g : Labels → E) (c : ℝ), (∀ z, g (-z) = c • g z) →
        ∀ z, smoothFourierCutoff ψ Λ g (-z) = c • smoothFourierCutoff ψ Λ g z) ∧
      -- frequencies at most `2Λ`
      (∀ (g : Labels → E) (k : Fin 3 → ℤ), 2 * Λ < ‖latticeVector k‖ →
        mFourierCoeff (smoothFourierCutoff ψ Λ g) k = 0) ∧
      -- operator norm on `L^∞`
      (∀ g : Labels → E, MemLp g ∞ unitTorusMeasure →
        eLpNormEssSup (smoothFourierCutoff ψ Λ g) unitTorusMeasure ≤
          ENNReal.ofReal Cop * eLpNormEssSup g unitTorusMeasure) ∧
      -- operator norm on continuous fields with the uniform norm
      (∀ g : C(Labels, E),
        spatialSupNorm (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) ≤ Cop * ‖g‖) ∧
      -- operator norm on `C^{0,1/2}`
      (∀ g : C(Labels, E), SpatialHolderHalf 0 (fun x => g (toUnitTorus x)) →
        SpatialHolderHalf 0 (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) ∧
          spatialHolderHalfNorm 0 (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) ≤
            Cop * spatialHolderHalfNorm 0 (fun x => g (toUnitTorus x))) ∧
      -- (B.2)
      (∀ (M s : ℕ), s ≤ M → ∀ g : C(Labels, E),
        SpatialHolderHalf M (fun x => g (toUnitTorus x)) →
        SpatialHolderHalf s
            (fun x => g (toUnitTorus x) - smoothFourierCutoff ψ Λ g (toUnitTorus x)) ∧
          spatialHolderHalfNorm s
              (fun x => g (toUnitTorus x) - smoothFourierCutoff ψ Λ g (toUnitTorus x)) ≤
            Ct M * Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M (fun x => g (toUnitTorus x)))) ∧
    -- (ii) real velocity fields, `S_Λ = realVectorFourierCutoff ψ Λ`
    ((∀ (g : C(Labels, Vec3)) (k : Fin 3 → ℤ),
        mFourierCoeff (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ g z)) k =
          ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff (fun z => periodicComplexifyVector (g z)) k) ∧
      -- commutes with spatial derivatives
      (∀ (g d : C(Labels, Vec3)) (i : Fin 3), ContDiff ℝ 1 (fun x => g (toUnitTorus x)) →
        (∀ x, d (toUnitTorus x) =
          fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single i 1)) →
        ∀ x, fderiv ℝ (fun y => realVectorFourierCutoff ψ Λ g (toUnitTorus y)) x
          (EuclideanSpace.single i 1) = realVectorFourierCutoff ψ Λ d (toUnitTorus x)) ∧
      -- commutes with the time derivative on a closed time slab `[a, b]`
      (∀ (a b : ℝ), a < b → ∀ V : Velocity,
        ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)) →
        ∀ g gt : ℝ → C(Labels, Vec3),
        (∀ t ∈ Icc a b, ∀ x, g t (toUnitTorus x) = V t x) →
        (∀ t ∈ Icc a b, ∀ x, gt t (toUnitTorus x) = derivWithin (fun r => V r x) (Icc a b) t) →
        ∀ t ∈ Icc a b, ∀ x,
          HasDerivWithinAt (fun r => realVectorFourierCutoff ψ Λ (g r) (toUnitTorus x))
            (realVectorFourierCutoff ψ Λ (gt t) (toUnitTorus x)) (Icc a b) t) ∧
      -- preserves parity
      (∀ (g : C(Labels, Vec3)) (c : ℝ), (∀ z, g (-z) = c • g z) →
        ∀ z, realVectorFourierCutoff ψ Λ g (-z) = c • realVectorFourierCutoff ψ Λ g z) ∧
      -- preserves divergence freeness
      (∀ g : C(Labels, Vec3), ContDiff ℝ ∞ (fun x => g (toUnitTorus x)) →
        (∀ x, divergence (fun y => g (toUnitTorus y)) x = 0) →
        ∀ x, divergence (fun y => realVectorFourierCutoff ψ Λ g (toUnitTorus y)) x = 0) ∧
      -- frequencies at most `2Λ`
      (∀ (g : C(Labels, Vec3)) (k : Fin 3 → ℤ), 2 * Λ < ‖latticeVector k‖ →
        mFourierCoeff (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ g z)) k = 0) ∧
      -- operator norm on continuous fields with the uniform norm
      (∀ g : C(Labels, Vec3),
        spatialSupNorm (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) ≤ Cop * ‖g‖) ∧
      -- operator norm on `C^{0,1/2}`
      (∀ g : C(Labels, Vec3), SpatialHolderHalf 0 (fun x => g (toUnitTorus x)) →
        SpatialHolderHalf 0 (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) ∧
          spatialHolderHalfNorm 0 (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) ≤
            Cop * spatialHolderHalfNorm 0 (fun x => g (toUnitTorus x))) ∧
      -- (B.2)
      (∀ (M s : ℕ), s ≤ M → ∀ g : C(Labels, Vec3),
        SpatialHolderHalf M (fun x => g (toUnitTorus x)) →
        SpatialHolderHalf s
            (fun x => g (toUnitTorus x) - realVectorFourierCutoff ψ Λ g (toUnitTorus x)) ∧
          spatialHolderHalfNorm s
              (fun x => g (toUnitTorus x) - realVectorFourierCutoff ψ Λ g (toUnitTorus x)) ≤
            Ct M * Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M (fun x => g (toUnitTorus x)))) ∧
    -- (B.1), for fields with values in any real normed space
    (∀ (m : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (g : C(Labels, V)),
      RealNormedTorusFourierBand (4 * Λ) g →
      (∀ β : Fin m → Fin 3, BddAbove (range fun x : Vec3 =>
          ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
            (fun i => EuclideanSpace.single (β i) 1)‖)) ∧
        (∑ β ∈ Finset.univ.filter (fun β : Fin m → Fin 3 => Monotone β), ⨆ x : Vec3,
            ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
              (fun i => EuclideanSpace.single (β i) 1)‖) ≤ Cb m * Λ ^ m * ‖g‖)

/-- **Display (D.2)** (`cc:uf:trunc:eq:holder-sup`, sections/appD_finite_norms.tex:35,
before Lemma D.1). For a phase-independent field `c(t, a)` and `0 < ℓ_* ≤ 1`,
`ℓ_*^m |c|_{m,1/2} ≤ C ℓ_*^{-1/2} (ℓ_*^m |c|_m + ℓ_*^{m+1} |c|_{m+1})` for every
`m ≥ 0`, hence `‖c‖_{[n]} ≤ ‖c‖_{[n],1/2} ≤ C ℓ_*^{-1/2} ‖c‖_{[n+1]}` for every
`n ≥ 0`. Equation: (D.2). It is not part of Lemma D.1; the proof of
Proposition 5.2 (sections/06d_mean_estimates.tex:18,40,59,64) and the joint
proof of Lemmas 1.2 and 1.3 of the auxiliary note, in its time-derivative
induction (auxiliary/terminal_smoothness.tex:262), cite it.

Representation: fields are `c : I → Vec3 → E` over an arbitrary time domain,
with values in a real normed space and labels in `ℝ³`; `|c|_m`, `|c|_{m,1/2}`,
`‖c‖_{[n]}`, `‖c‖_{[n],1/2}` are `AppendixD.coefficientOrderNorm`,
`AppendixD.holderOrderNorm`, `AppendixD.coefficientNorm` and
`AppendixD.holderFieldNorm` (one nondecreasing coordinate word per multi-index;
the `C^{0,1/2}` norm is the maximum, not the sum, of the supremum and the
seminorm); finiteness of the right sides is `CoefficientNormFinite (m + 1) c`
(resp. `CoefficientNormFinite (n + 1) c`), which also includes the lower
orders; each part also states that the half-Hölder quantities on its left are
finite; the constant is explicit, `C = 4`; `ℓ_* ≤ 1` is the hypothesis the text
uses. -/
def Statement.Text.eq_D_2 : Prop :=
  ∀ (I E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 →
    ∀ c : I → Vec3 → E,
    -- the first bound, at every order `m`
    (∀ m : ℕ, CoefficientNormFinite (m + 1) c →
      (∀ w ∈ appendixCoefficientOrderWords m,
          BddAbove (hierarchyJetValues True (hierarchyLabelDirection 1) w c)) ∧
        ℓ ^ m * holderOrderNorm m c ≤
          4 * (Real.sqrt ℓ)⁻¹ * (ℓ ^ m * coefficientOrderNorm m c +
            ℓ ^ (m + 1) * coefficientOrderNorm (m + 1) c)) ∧
    -- hence the comparison of the norms
    ∀ n : ℕ, CoefficientNormFinite (n + 1) c →
      HolderFieldNormFinite ℓ n c ∧ coefficientNorm ℓ n c ≤ holderFieldNorm ℓ n c ∧
        holderFieldNorm ℓ n c ≤ 4 * (Real.sqrt ℓ)⁻¹ * coefficientNorm ℓ (n + 1) c

/-- **Lemma D.1** (`cc:uf:trunc:lem:fields`, sections/appD_finite_norms.tex:42).
For every `n ≥ 0` and fields `f, g` with finite norms (D.1)
`‖f‖_{[n]} = ∑_{m+j≤n} ℓ_*^m h^j |∂_s^j f|_m`, `‖f‖_{[n],γ} = ‖f/γ‖_{[n]}`:
(D.3) `∑_i ‖∂_{a_i} f‖_{[n],γ} ≤ C ℓ_*^{-1} ‖f‖_{[n+1],γ}` and
`‖∂_s f‖_{[n],γ} ≤ h^{-1} ‖f‖_{[n+1],γ}`;
(D.4) `‖f g‖_{[n],γ} ≤ C_n ‖f‖_{[n]} ‖g‖_{[n],γ}`;
(D.5) `‖⟨f⟩‖_{[n],γ} ≤ ‖f‖_{[n],γ}`, `‖f - ⟨f⟩‖_{[n],γ} ≤ 2 ‖f‖_{[n],γ}` and,
when `⟨f⟩ = 0`, `‖∂_s^{-1} f‖_{[n],γ} ≤ C ‖f‖_{[n],γ}`, for fields of period
one in `s`; and, for phase-independent fields, (D.4) with `‖·‖_{[n],1/2}`
in place of `‖·‖_{[n]}` and `γ ≡ 1`. Each clause also states that the norm on
its left side is finite, as the inequalities of the manuscript assert.

Representation: fields are `f : I → Vec3 × ℝ → E` (time `t ∈ I`, label
`a ∈ ℝ³`, phase `s`), smooth in `(a, s)` at each time, with values in a real
normed space, which in (D.5) is assumed complete (the phase average and the
primitive are Bochner integrals in `s`, which vanish by convention in an
incomplete space; the fields of the manuscript are finite-dimensional); the
time domain `I` is arbitrary (for example `[t₀, T]`), and
`γ : I → ℝ` is a positive weight; norms are `AppendixD.fieldNorm`,
`AppendixD.weightedFieldNorm` and `AppendixD.holderFieldNorm` (see their
docstrings: one nondecreasing weighted coordinate word per multi-index; in
the half-Hölder norm the supremum and the seminorm are combined by a maximum,
not a sum), and "finite norm" is `FieldNormFinite` (of `f/γ` for weighted
norms) or `HolderFieldNormFinite`, both for the hypotheses and for the
finiteness of the left sides; for a phase-independent factor `c(t, a)`,
written `fun t x => c t x.1`, `AppendixD.fieldNorm_phaseIndependent` and
`AppendixD.CoefficientNormFinite.fieldNormFinite` identify its norm with
`‖c‖_{[n]} = ∑_{m≤n} ℓ_*^m |c|_m` and give its finiteness; the product `f g`
is `B(f, g)` for any continuous bilinear map `B` (matrix and scalar products
have `‖B‖ ≤ 1`), with the factor `‖B‖` in the constant; the constants are
explicit: `C = 3` in
(D.3), `C_n = 2 · 2^n · #W_n` in (D.4) with `#W_n` the number of
nondecreasing words of length at most `n` in the four (resp. three, for the
half-Hölder version) weighted directions, and `C = 2` for the primitive in
(D.5); periodicity in `s` is assumed only in (D.5), where it is used. -/
def Statement.lemma_D_1 : Prop :=
  ∀ (I : Type) (ℓ h : ℝ), 0 < ℓ → 0 < h → ∀ γ : I → ℝ, (∀ t, 0 < γ t) → ∀ n : ℕ,
    -- (D.3)
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : I → Vec3 × ℝ → E),
      FieldNormFinite ℓ h (n + 1) (weighted γ f) →
      (∀ i : Fin 3, FieldNormFinite ℓ h n (weighted γ (labelPartial i f))) ∧
        FieldNormFinite ℓ h n (weighted γ (phasePartial f)) ∧
        (∑ i : Fin 3, weightedFieldNorm ℓ h γ n (labelPartial i f)) ≤
          3 * ℓ⁻¹ * weightedFieldNorm ℓ h γ (n + 1) f ∧
        weightedFieldNorm ℓ h γ n (phasePartial f) ≤ h⁻¹ * weightedFieldNorm ℓ h γ (n + 1) f) ∧
    -- (D.4)
    (∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
      (B : E →L[ℝ] F →L[ℝ] G) (f : I → Vec3 × ℝ → E) (g : I → Vec3 × ℝ → F),
      FieldNormFinite ℓ h n f → FieldNormFinite ℓ h n (weighted γ g) →
      FieldNormFinite ℓ h n (weighted γ (fun t x => B (f t x) (g t x))) ∧
        weightedFieldNorm ℓ h γ n (fun t x => B (f t x) (g t x)) ≤
          ((hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n * (2 * ‖B‖)) *
            fieldNorm ℓ h n f * weightedFieldNorm ℓ h γ n g) ∧
    -- (D.5)
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : I → Vec3 × ℝ → E),
      FieldNormFinite ℓ h n (weighted γ f) →
      (∀ t a, Function.Periodic (fun s => f t (a, s)) 1) →
      FieldNormFinite ℓ h n (weighted γ (phaseAverage f)) ∧
        FieldNormFinite ℓ h n (weighted γ (f - phaseAverage f)) ∧
        weightedFieldNorm ℓ h γ n (phaseAverage f) ≤ weightedFieldNorm ℓ h γ n f ∧
        weightedFieldNorm ℓ h γ n (f - phaseAverage f) ≤ 2 * weightedFieldNorm ℓ h γ n f ∧
        ((∀ t a, phaseMean (fun s => f t (a, s)) = 0) →
          FieldNormFinite ℓ h n (weighted γ (phaseInverse f)) ∧
            weightedFieldNorm ℓ h γ n (phaseInverse f) ≤ 2 * weightedFieldNorm ℓ h γ n f)) ∧
    -- (D.4) for phase-independent fields in `‖·‖_{[n],1/2}` with `γ ≡ 1`
    (∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
      (B : E →L[ℝ] F →L[ℝ] G) (c : I → Vec3 → E) (d : I → Vec3 → F),
      HolderFieldNormFinite ℓ n c → HolderFieldNormFinite ℓ n d →
      HolderFieldNormFinite ℓ n (fun t x => B (c t x) (d t x)) ∧
        holderFieldNorm ℓ n (fun t x => B (c t x) (d t x)) ≤
          ((hierarchyAdmissibleWords (Fin 3) n).card * (2 : ℝ) ^ n * (2 * ‖B‖)) *
            holderFieldNorm ℓ n c * holderFieldNorm ℓ n d)

/-- **Lemma D.2** (`cc:uf:trunc:lem:coefficients`,
sections/appD_finite_norms.tex:93). Let `c, d` be smooth phase-independent
matrix fields satisfying (D.6) `|c|_m ≤ C_m 𝖣^{C(m+1)}` (`m ≥ 0`), with
fixed-order constants `C_m` and an absolute exponent `C` that may depend on
the coefficient. (a) The product `c d` satisfies (D.6). (b) If `c` is
invertible and `sup_{t,a} |c^{-1}|` is at most a power of `𝖣` with an
absolute exponent, then `c^{-1}` satisfies (D.6). (c) If `ℓ_* ≤ 𝖣^{-C}` with
the exponent `C` of (D.6) for `c`, then `‖c‖_{[n]} ≤ C_n 𝖣^C` for every
`n ≥ 0` (norm (D.1)) and `ℓ_*^m |c|_m ≤ C_m 𝖣^{2C} ℓ_*` for every `m ≥ 1`.

The output constants are nonnegative and depend only on the value spaces,
the input constants, the exponents and the order: in each part they are
chosen after the value spaces (`X, Y, Z` in (a), the algebra `A` in (b), `X`
in (c)), the input constants `C`, `C'` and the exponents, and before the
time domain, `𝖣`, `ℓ_*` and the coefficients (and, in (a), the product `B`).
This is the uniformity of fixed-order constants
(sections/01b_parameters.tex:13-17), which may depend on the fixed matrix
sizes.

Representation: coefficients are `c : I → Vec3 → X` over an arbitrary time
domain `I`, with labels in `ℝ³`; matrix fields take values in normed spaces
of linear maps with the operator norm; (D.6) is `AppendixD.CoefficientPower C
𝖣 a c` with explicit exponent `a`, and `|c|_m`, `‖c‖_{[n]}` are
`AppendixD.coefficientOrderNorm` and `AppendixD.coefficientNorm` (the norm (D.1)
of the field `(t, a, s) ↦ c(t, a)` by `AppendixD.fieldNorm_phaseIndependent`);
all exponents are natural numbers: since `𝖣 ≥ 1`, a real absolute exponent `C`
may be rounded up to `⌈C⌉`, which in (c) means that the scale condition is
`ℓ_* ≤ 𝖣^{-⌈C⌉}` and the conclusions carry `𝖣^{⌈C⌉}` and `𝖣^{2⌈C⌉}`
(harmless: the manuscript takes `ℓ_*` a large negative power of `𝖣`); the matrix
product in (a) is `B(c, d)` for any continuous bilinear `B` with `‖B‖ ≤ 1`
(products of rectangular matrices included); the inverse in (b) is
`Ring.inverse` in a complete normed `ℝ`-algebra `A` (square matrices), whose
choice is fixed before the constants; the exponents are explicit:
`2 max(a, b)` in (a) and `3 max(a, e)` in (b), where `‖c^{-1}‖ ≤ 𝖣^e`;
`𝖣 ≥ 1` and `ℓ_* > 0`. -/
def Statement.lemma_D_2 : Prop :=
  -- (a) products
  (∀ (X Y Z : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (C C' : ℕ → ℝ) (a b : ℕ),
    ∃ C'' : ℕ → ℝ, (∀ m, 0 ≤ C'' m) ∧ ∀ B : X →L[ℝ] Y →L[ℝ] Z, ‖B‖ ≤ 1 →
      ∀ (I : Type) (D : ℝ), 1 ≤ D → ∀ (c : I → Vec3 → X) (d : I → Vec3 → Y),
        CoefficientPower C D a c → CoefficientPower C' D b d →
        CoefficientPower C'' D (2 * max a b) (fun t x => B (c t x) (d t x))) ∧
  -- (b) inverses
  (∀ (A : Type) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (C : ℕ → ℝ) (a e : ℕ),
    ∃ C'' : ℕ → ℝ, (∀ m, 0 ≤ C'' m) ∧ ∀ (I : Type) (D : ℝ), 1 ≤ D → ∀ c : I → Vec3 → A,
      CoefficientPower C D a c → (∀ t x, IsUnit (c t x)) →
      (∀ t x, ‖Ring.inverse (c t x)‖ ≤ D ^ e) →
      CoefficientPower C'' D (3 * max a e) (fun t x => Ring.inverse (c t x))) ∧
  -- (c) weighted norms under `ℓ_* ≤ 𝖣^{-C}`
  (∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (C : ℕ → ℝ) (a : ℕ),
    ∃ C' : ℕ → ℝ, (∀ m, 0 ≤ C' m) ∧ ∀ (I : Type) (D ℓ : ℝ), 1 ≤ D → 0 < ℓ → ℓ ≤ (D ^ a)⁻¹ →
      ∀ c : I → Vec3 → X, CoefficientPower C D a c →
        (∀ n, coefficientNorm ℓ n c ≤ C' n * D ^ a) ∧
          ∀ m, 1 ≤ m → ℓ ^ m * coefficientOrderNorm m c ≤ C' m * D ^ (2 * a) * ℓ)

/-- **Lemma D.3** (`cc:uf:trunc:lem:lifting`, sections/appD_finite_norms.tex:133).
Consider a linear equation `ℒ v = ℒ₀ v + ∑_ν T_ν(c_ν v) = F` with finitely
many phase-independent coefficients `c_ν`, where `ℒ₀` and the `T_ν` commute
with label and phase derivatives, and which may hold modulo a fixed subspace
preserved by differentiation. Write `f` for the forcing together with the
prescribed data. Suppose that `‖v‖_{[0],γ} ≤ C_low ‖f‖_{[0],γ}` for every
admissible source, let `b_ν` be the operator norm of `T_ν` from
`‖·‖_{[0],γ}` to the forcing norm, and assume (D.7)
`C_low ∑_ν b_ν ℓ_*^m |c_ν|_m ≤ C_m` for `m ≥ 1`. Then every smooth solution
satisfies `‖v‖_{[n],γ} ≤ C_n C_low ‖f‖_{[n],γ}` for `n ≥ 0`, where `C_n`
depends only on `n` and the bounds `C_m`, `m ≤ n`. The same holds for
phase-independent fields with `γ ≡ 1` in the norms `‖·‖_{[n],1/2}`,
`|c_ν|_{m,1/2}`.

Representation: the lemma is stated abstractly. Solutions, forcings (with
data) and coefficients form real vector spaces `E`, `F`, `A` with zero-order
seminorms `pE` (`‖·‖_{[0],γ}`, or the zero-order half-Hölder norm), `pF`
(the forcing norm with the data) and `pA` (`|·|_0`, or `|·|_{0,1/2}`); an
equation modulo a fixed subspace `W` preserved by differentiation is the
case of a quotient space `F`; the linear constraints on `v` are encoded in
`E`. The weighted label and phase derivatives (`ℓ_* ∂_{a_i}`, `h ∂_s`) are
commuting linear maps `DE i`, `DF i`, `DA i` indexed by a finite ordered set
`Idx` (four directions, or three in the half-Hölder version), so that the
norm (D.1) `‖v‖_{[n],γ}` is `appendixFiniteDerivativeNorm pE DE n v` (one
nondecreasing word per mixed multi-index) and `ℓ_*^m |c_ν|_m` is
`appendixExactOrderDerivativeNorm pA DA m (c ν)` (the words with a phase
letter vanish on phase-independent coefficients). The coefficient action
`v ↦ T_ν(c_ν v)` is a bilinear map `T ν` obeying Leibniz' rule; the bound
`pF (T ν a u) ≤ b ν · pA a · pE u` combines the operator norm `b_ν` with the
zero-order product inequality. "For every admissible source" is the
zero-order estimate applied to every `u ∈ E` with its own forcing `ℒ u`.
Hypothesis (D.7) is required only for `1 ≤ m ≤ n`, the constants `C_m` are
arbitrary reals, and `C_n ≥ 0` is chosen after `Idx`, `n` and `(C_m)` and
before the spaces, operators, coefficients and solution. -/
def Statement.lemma_D_3 : Prop :=
  ∀ (Idx : Type) [Fintype Idx] [LinearOrder Idx] (n : ℕ) (Cm : ℕ → ℝ),
  ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ (J A E F : Type) [Fintype J] [AddCommGroup A] [Module ℝ A]
      [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
      (DA : Idx → A →ₗ[ℝ] A) (DE : Idx → E →ₗ[ℝ] E) (DF : Idx → F →ₗ[ℝ] F)
      (pA : Seminorm ℝ A) (pE : Seminorm ℝ E) (pF : Seminorm ℝ F)
      (L₀ : E →ₗ[ℝ] F) (T : J → A →ₗ[ℝ] E →ₗ[ℝ] F) (c : J → A) (b : J → ℝ) (Clow : ℝ),
    -- `ℒ₀` commutes with the derivatives
    (∀ i u, DF i (L₀ u) = L₀ (DE i u)) →
    -- `T_ν` commutes with the derivatives, and Leibniz' rule for `c_ν v`
    (∀ j i a u, DF i (T j a u) = T j (DA i a) u + T j a (DE i u)) →
    -- the derivatives commute
    (∀ i i' g, DF i (DF i' g) = DF i' (DF i g)) →
    (∀ i i' a, DA i (DA i' a) = DA i' (DA i a)) →
    -- `b_ν` bounds `T_ν(a u)` from the zero-order norms
    (∀ j, 0 ≤ b j) → (∀ j a u, pF (T j a u) ≤ b j * pA a * pE u) →
    -- the zero-order estimate for every admissible source
    0 ≤ Clow → (∀ u, pE u ≤ Clow * pF (L₀ u + ∑ j, T j (c j) u)) →
    -- (D.7)
    (∀ m, 1 ≤ m → m ≤ n →
      Clow * ∑ j, b j * appendixExactOrderDerivativeNorm pA DA m (c j) ≤ Cm m) →
    ∀ (v : E) (f : F), L₀ v + ∑ j, T j (c j) v = f →
      appendixFiniteDerivativeNorm pE DE n v ≤ Cn * Clow * appendixFiniteDerivativeNorm pF DF n f

end TorusEuler.Paper
