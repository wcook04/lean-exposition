import TorusEuler.Paper.S34A.Vocabulary

/-! Statements of Lemma 3.1, Lemma 4.1, Theorem 4.2, Theorem A.1 and Lemma A.2
of the latest manuscript (package S34A). Each `Statement.<name>` is a closed
proposition; the conditional proofs and spine nodes live in other modules. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "P" => endpointStrongSpatialProjection
local notation "J(" T ")" => Icc (0 : ℝ) T
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)
local notation "Paths" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) 1))

local instance statementsS34ASolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance statementsS34ASolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- **Lemma 3.1** (`cc:uf:exact:lem:profile`, sections/04_localized_wave.tex:152).
There are odd smooth `1`-periodic functions `F_h`, `0 < h ≤ 1`, with zero-mean
primitives `P_h`, such that `F_h'(0) = 1`, `-C h ≤ F_h' ≤ 1`,
`‖F_h‖_∞ ≤ C h` and `‖∂_s^j F_h‖_∞ ≤ C_j h^{1-j}` for `j ≥ 2`. The lemma has no
numbered equation; its first two conditions are the profile conditions (1.10),
which give the curvature bound (1.11), and the family is the profile of Section 5.

Representation: the TeX asserts existence; the statement names the family
constructed in the TeX proof, `waveProfile h` (the primitive vanishing at `0` of
`F_h'(s) = (ψ(s/h) - c_h)/(1 - c_h)`) and its zero-mean primitive
`wavePressurePrimitive h`, which is the profile `F_0 = F_h` fixed in Section 5.
The TeX existential is `∃ F P, ProfileFamily F P`, which follows by taking these
witnesses. The constants `C` and `C_j` are positive and independent of `h`;
supremum bounds are stated pointwise in the phase. -/
def Statement.lemma_3_1 : Prop :=
  ProfileFamily waveProfile wavePressurePrimitive

/-- **Lemma 4.1** (`cc:uf:mean:hardy`, sections/06b_mean_inverse.tex:104).
In the setting of Section 4 (`0 < T ≤ 1`, a smooth divergence-free parent `u` on
`I × 𝕋³`, `I = [0,T]`, with flow `X`, and the coefficients (4.1)), assume
`H^# ≤ Id` on `I × 𝕋³` as quadratic forms. Then for every label `a`, every
`z ∈ H¹₀(I; ℝ³)` and `ξ = D_aX(·,a) z`,
`∫_I H^# ξ·ξ ≤ ½ ∫_I |ξ_t|²`, and hence (4.8)
`∫_I (K z_t·z_t + Ω z_t·z) ≥ ½ ∫_I |ξ_t|²`.
The proof uses (4.5) and (4.7); the setting is (4.1)–(4.4).

Representation: the torus is `ℤ³`-periodic `ℝ³` and labels are points of `ℝ³`;
the parent and its flow are `MeanParentFlow T U X`. A path `z ∈ H¹₀(I;ℝ³)` is the
primitive `z(t) = ∫_0^t v` of its derivative `v = z_t ∈ L²(I;ℝ³)` with
`∫_I v = 0` (this parametrizes `H¹₀` exactly). The derivative `ξ_t` is written
through (4.4) as `M ξ + D_aX z_t`. -/
def Statement.lemma_4_1 : Prop :=
  ∀ (T : ℝ) (U : Velocity) (X : ℝ → Velocity), MeanParentFlow T U X →
    (∀ t ∈ J(T), ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2) →
    ∀ (a : Vec3) (v : Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) T))), endpointIntegral T v = 0 →
      let z : ℝ → Vec3 := endpointPrimitive v
      let ξ : ℝ → Vec3 := fun t => meanDeformation X t a (z t)
      let ξt : ℝ → Vec3 := fun t => meanGradient U X t a (ξ t) + meanDeformation X t a (v t)
      (∫ t in (0 : ℝ)..T, ⟪meanHsharp T U X t a (ξ t), ξ t⟫_ℝ) ≤
          (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, ‖ξt t‖ ^ 2 ∧
        (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..T, ‖ξt t‖ ^ 2) ≤
          ∫ t in (0 : ℝ)..T,
            (⟪meanKinetic X t a (v t), v t⟫_ℝ + ⟪meanVorticity U X t a (v t), z t⟫_ℝ)

/-- **Theorem 4.2** (`cc:uf:mean:inverse`, sections/06b_mean_inverse.tex:143).
In the setting of Section 4 with the coefficients (4.1) and
`D_- ≥ max{1, sup |(D_aX)⁻¹|}`, assume `H^# ≤ Id` on `I × 𝕋³`. Then:

* for every `L ∈ C(I; C^{0,1/2})` the system (4.9)
  `K v - ∫_0^t Ω v + L = c + ∇_a φ`, `v = z_t`, `z(0) = z(T) = 0`, `div_a z = 0`
  has a unique solution with `z ∈ C¹(I; C^{0,1/2})`, `c ∈ C^{0,1/2}` divergence
  free and `∇_a φ ∈ C(I; C^{0,1/2})`; there are absolute `C, p` such that with
  (4.10) `A = C (D_- + ‖M‖_∞ + ‖K‖_{C_t C^{1,1/2}} + ‖Ω‖_{C_t C^{1,1/2}})^p` one
  has `‖v‖_{C_t C^{0,1/2}} ≤ A ‖L‖_{C_t C^{0,1/2}}`;
* for a smooth field `f` on `I × 𝕋³` and `L = -∫_0^t g`, `g = (D_aX)ᵀ (f∘X)`,
  `z` is smooth; with `B = D_aX v` and `𝒟 = 2 (D_aX)ᵀ ∂_t D_aX` there is
  a smooth zero-mean label pressure `𝗊` (`qLabel`) with (4.11)
  `K v_t + ∇_a 𝗊 = g - 𝒟 v`, and `b = B∘X⁻¹`, `q = 𝗊∘X⁻¹` are smooth and solve
  (4.12) `div b = 0`, `b_t + u·∇b + b·∇u + ∇q = f`; the endpoint conditions
  select the initial velocity `b(0)`;
* `A` bounds, uniformly in `t`, the operator norm on `C^{0,1/2}` of the
  fixed-time inverse `(P K(t))⁻¹ P`, where `(P K(t))⁻¹` inverts
  `v ↦ P(K(t) v)` on the divergence-free fields of `C^{0,1/2}`.

The setting uses (4.1) and (4.2); the proof uses (4.6) and (A.3).

Representation: the parent is `MeanParentFlow T U X` (`ℤ³`-periodic fields on
`ℝ³`). The TeX source `L` is called `src`; the Lean `L` is an upper bound for
`‖M‖_∞`. `D_-`, `‖M‖_∞`, `‖K‖_{C_tC^{1,1/2}}`, `‖Ω‖_{C_tC^{1,1/2}}` are replaced
by upper bounds `D ≥ 1`, `L`, and `K₀ + K₁`, `Ω₀ + Ω₁`, where `K₀`, `K₁` bound the
supremum of `K` and of its first label derivative (similarly for `Ω`); since
`K₀ + K₁ ≤ 2‖K‖_{C_tC^{1,1/2}}` for the optimal choice, this bound is stronger
than (4.10). Matrix norms are operator norms on `𝓛(ℝ³)`, and the first label
derivative is normed in `𝓛(ℝ³, 𝓛(ℝ³))`. `(D_aX)⁻¹` is the derivative of the
back-to-label map (`meanDeformationInv`). The coefficients `K`, `Ω` enter as curves
`K Ω : ℝ → C^{0,1/2}(𝕋³; 𝓛(ℝ³))` whose lifts are (4.1) on `I`; such curves exist
and are unique on `I`. The sentence on `b(0)` is stated as `b(0) = c`.
Solutions are in the class `EndpointSystemSolution` (velocity
`v = z_t` and displacement `z` in the divergence-free subspace, pressure
gradient a continuous curve `G` with periodic potential `φ`); uniqueness of `z`,
`v`, `c`, `∇φ` is stated on `I`. `‖·‖_{C_tC^{0,1/2}}` is `endpointClosedTimeNorm`.
In the second item `src` is any curve whose lift is `-∫_0^t g` on `I`; the solution
exists by the first item, and every solution has the listed properties.
Smoothness on `I × 𝕋³` is joint smoothness of the lifts on the closed slab
`[0,T] × ℝ³`; `v_t`, `∂_t D_aX` are derivatives within `[0,T]`; the material
derivative `b_t + u·∇b` is the slab derivative of `b` in the direction `(1, u)`,
and `b·∇u = (∇u) b`. The operator `P` is the Leray projection
`endpointStrongSpatialProjection` onto the divergence-free subspace. -/
def Statement.theorem_4_2 : Prop :=
  ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
  ∀ (T : ℝ) (U : Velocity) (X : ℝ → Velocity), MeanParentFlow T U X →
  (∀ t ∈ J(T), ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2) →
  ∀ (D L K₀ K₁ Ω₀ Ω₁ : ℝ), 1 ≤ D →
  (∀ t ∈ J(T), ∀ a, ‖meanDeformationInv X t a‖ ≤ D) →
  (∀ t ∈ J(T), ∀ a, ‖meanGradient U X t a‖ ≤ L) →
  (∀ t ∈ J(T), ∀ a, ‖meanKinetic X t a‖ ≤ K₀) →
  (∀ t ∈ J(T), ∀ a, ‖fderiv ℝ (meanKinetic X t) a‖ ≤ K₁) →
  (∀ t ∈ J(T), ∀ a, ‖meanVorticity U X t a‖ ≤ Ω₀) →
  (∀ t ∈ J(T), ∀ a, ‖fderiv ℝ (meanVorticity U X t) a‖ ≤ Ω₁) →
  ∀ (K Ω : ℝ → K½),
  (∀ t ∈ J(T), ∀ a, HalfHolder.eval (toUnitTorus a) (K t) = meanKinetic X t a) →
  (∀ t ∈ J(T), ∀ a, HalfHolder.eval (toUnitTorus a) (Ω t) = meanVorticity U X t a) →
  let A : ℝ := C * (D + L + K₀ + K₁ + Ω₀ + Ω₁) ^ p
  -- the inverse for every Hölder source, with the bound (4.10)
  (∀ src : ℝ → C½, ContinuousOn src J(T) →
    ∃ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
      EndpointSystemSolution T K Ω src z v c φ G ∧
      endpointClosedTimeNorm T v ≤ A * endpointClosedTimeNorm T src ∧
      ∀ (z' v' : ℝ → S) (c' : S) (φ' : Pressure) (G' : ℝ → C½),
        EndpointSystemSolution T K Ω src z' v' c' φ' G' →
        EqOn z' z J(T) ∧ EqOn v' v J(T) ∧ c' = c ∧ EqOn G' G J(T)) ∧
  -- smooth forces: smoothness, (4.11) and (4.12)
  (∀ f : Velocity, ContDiffOn ℝ ∞ (Function.uncurry f) Slab(T) →
    (∀ t ∈ J(T), SpatiallyPeriodic (f t)) →
    ∀ src : ℝ → C½,
    (∀ t ∈ J(T), ∀ a, HalfHolder.eval (toUnitTorus a) (src t) =
      -∫ s in (0 : ℝ)..t, (meanDeformation X s a).adjoint (f s (X 0 s a))) →
    (∃ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
      EndpointSystemSolution T K Ω src z v c φ G) ∧
    ∀ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
      EndpointSystemSolution T K Ω src z v c φ G →
      let vl : ℝ → Vec3 → Vec3 := fun t a => HalfHolder.eval (toUnitTorus a) (v t : C½)
      let b : ℝ → Vec3 → Vec3 := fun t x => meanDeformation X t (X t 0 x) (vl t (X t 0 x))
      ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (z q.1 : C½))
        Slab(T) ∧
      (∀ x, b 0 x = HalfHolder.eval (toUnitTorus x) (c : C½)) ∧
      ∃ qLabel : Pressure, ContDiffOn ℝ ∞ (Function.uncurry qLabel) Slab(T) ∧
        (∀ t ∈ J(T), SpatiallyPeriodic (qLabel t) ∧ (∫ x in centeredCell, qLabel t x) = 0) ∧
        (∀ t ∈ J(T), ∀ a,
          meanKinetic X t a (derivWithin (fun r => vl r a) J(T) t) + gradient (qLabel t) a =
            (meanDeformation X t a).adjoint (f t (X 0 t a)) -
              (2 : ℝ) • (meanDeformation X t a).adjoint
                (derivWithin (fun r => meanDeformation X r a) J(T) t (vl t a))) ∧
        let q : ℝ → Vec3 → ℝ := fun t x => qLabel t (X t 0 x)
        ContDiffOn ℝ ∞ (Function.uncurry b) Slab(T) ∧
        ContDiffOn ℝ ∞ (Function.uncurry q) Slab(T) ∧
        (∀ t ∈ J(T), SpatiallyPeriodic (b t) ∧ SpatiallyPeriodic (q t)) ∧
        ∀ t ∈ J(T), ∀ x, divergence (b t) x = 0 ∧
          fderivWithin ℝ (Function.uncurry b) Slab(T) (t, x) (1, U t x) +
            fderiv ℝ (U t) x (b t x) + gradient (q t) x = f t x) ∧
  -- the fixed-time inverse
  ∀ t ∈ J(T), ∃ e : S ≃L[ℝ] S,
    (∀ w : S, e w = P ((K t).coefficientMul (w : C½))) ∧
    ‖(e.symm : S →L[ℝ] S).comp P‖ ≤ A

/-- **Theorem A.1** (`cc:holder:linear`, sections/appA_mean_regularity.tex:26).
On `I = [0,1]` let `K(t,a)` be symmetric and `Ω(t,a)` skew-symmetric, continuous
in time with values in `C^{1,1/2}`, with (A.1) `K ≥ κ I` and (A.2)
`∫_I (K z_t·z_t + Ω z_t·z) ≥ μ ∫_I |z_t|²` for every label `a` and
`z ∈ H¹₀(I; ℝ³)`, and put `Q = 2 + κ⁻¹ + μ⁻¹ + ‖K‖₁ + ‖Ω‖₁`. For
`L ∈ C(I; C^{0,1/2})` there are unique `z ∈ C¹(I; C^{0,1/2})`, `c ∈ C^{0,1/2}`
divergence free and `∇φ ∈ C(I; C^{0,1/2})` with
`K z_t - J(Ω z_t) + L = c + ∇φ`, `div z = 0`, `z(0) = z(1) = 0`; they obey (A.3)
`‖z_t‖₀ ≤ C Q^p ‖L‖₀`, with `C, p` depending only on the dimension. If `K`, `Ω`
and `L` are smooth on `I × 𝕋³`, then so are `z`, `c` and `∇φ`. The proof uses
(A.8) and (A.9).

Representation: symmetry is `IsSelfAdjoint` and skew-symmetry is
`Ωᵀ = -Ω`, pointwise. The regularity "continuous in time with values in
`C^{1,1/2}`" and the norms `‖K‖₁`, `‖Ω‖₁` are replaced by
`EndpointCoefficientC1Bound K K₀ K₁` (continuity in `C^{0,1/2}` and the bounds
`K₀`, `K₁` on the supremum of the lift and of its first derivative) and by
`K₀ + K₁` in `Q`; this weakens the hypothesis and strengthens the bound.
Matrix norms are operator norms on `𝓛(ℝ³)`, and the first label derivative is
normed in `𝓛(ℝ³, 𝓛(ℝ³))`.
(A.2) is `EndpointSobolevEnergyBound K Ω μ`, with `z = J v` for `v ∈ L²(I;ℝ³)` of
zero time mean (which parametrizes `H¹₀`). Solutions are in the class
`EndpointSystemSolution 1` (see `Statement.theorem_4_2`), `‖·‖₀` is
`endpointClosedTimeNorm 1`, and smoothness on `I × 𝕋³` is joint smoothness of the
lifts on `[0,1] × ℝ³`. -/
def Statement.theorem_A_1 : Prop :=
  ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
  ∀ (K Ω : ℝ → K½) (κ μ K₀ K₁ Ω₀ Ω₁ : ℝ),
    (∀ t ∈ J(1), ∀ a, IsSelfAdjoint (HalfHolder.eval a (K t))) →
    (∀ t ∈ J(1), ∀ a, (HalfHolder.eval a (Ω t)).adjoint = -HalfHolder.eval a (Ω t)) →
    EndpointCoefficientC1Bound K K₀ K₁ → EndpointCoefficientC1Bound Ω Ω₀ Ω₁ →
    0 < κ → (∀ t ∈ J(1), ∀ a (w : Vec3), κ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) w, w⟫_ℝ) →
    0 < μ → EndpointSobolevEnergyBound K Ω μ →
    let Q : ℝ := 2 + κ⁻¹ + μ⁻¹ + K₀ + K₁ + Ω₀ + Ω₁
    ∀ L : ℝ → C½, ContinuousOn L J(1) →
      ∃ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
        EndpointSystemSolution 1 K Ω L z v c φ G ∧
        (∀ (z' v' : ℝ → S) (c' : S) (φ' : Pressure) (G' : ℝ → C½),
          EndpointSystemSolution 1 K Ω L z' v' c' φ' G' →
          EqOn z' z J(1) ∧ EqOn v' v J(1) ∧ c' = c ∧ EqOn G' G J(1)) ∧
        endpointClosedTimeNorm 1 v ≤ C * Q ^ p * endpointClosedTimeNorm 1 L ∧
        (ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (K q.1)) Slab(1) →
          ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (Ω q.1)) Slab(1) →
          ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (L q.1)) Slab(1) →
          ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (z q.1 : C½))
              Slab(1) ∧
            ContDiff ℝ ∞ (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (c : C½)) ∧
            ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (G q.1)) Slab(1))

/-- **Lemma A.2** (`cc:holder:freezing`, sections/appA_mean_regularity.tex:71).
Let either `H = ℝ³`, `R = P`, or `H = L²(I; ℝ³)`, `R = P Q` with
`Q v = v - ∫_0^1 v`. Let `B ∈ C^{1,1/2}(𝕋³; 𝓛(H))` and `μ > 0` with (A.4)
`⟨B(a) w, w⟩_H ≥ μ ‖w‖_H²` for every `a` and every `w ∈ H` (with `Q w = w` in the
second case). Then `R B` is an isomorphism on `R C^{0,1/2}(𝕋³; H)` with (A.5)
`‖v‖_{C^{0,1/2}_a(H)} ≤ C (2 + μ⁻¹ + ‖B‖_{C¹_a 𝓛(H)})^p ‖R B v‖_{C^{0,1/2}_a(H)}`.
If moreover `B ∈ C^{k,1/2}` for an integer `k ≥ 1`, the same operator is an
isomorphism on `R C^{k,1/2}(𝕋³; H)`. The constants `C, p` depend only on the
dimension. The proof uses (A.6), (A.7) and Lax–Milgram.

Representation: `R C^{0,1/2}(𝕋³;H)` is the fixed space `freezingFixedSpace R`
of `R` in `HalfHolder (UnitAddTorus (Fin 3)) H`, and `R B` is
`freezingCompression R B.coefficientMul`; `P` is `endpointStrongSpatialLeray`
and `P Q` is `endpointStrongMixedLeray 1`, which imposes both the spatial
divergence and the zero time mean; `L²(I;ℝ³)` is `Lp Vec3 2` on `(0,1]` and
`Q w = w` is `∫_0^1 w = 0`. The hypothesis `B ∈ C^{1,1/2}` and the norm
`‖B‖_{C¹_a 𝓛(H)}` of the base clause are replaced by a Lipschitz constant `Lip`
of `B` on the flat torus and by `‖B‖_∞ + Lip`. This is a generalization: for
`B ∈ C^{1,1/2}` one may take `Lip = 2 sup ‖∇B‖`
(`halfHolder_lipschitz_of_spatialHolderHalf_one`), which gives (A.5) after
enlarging `C`. The higher-order clause keeps `B ∈ C^{k,1/2}` and is spelled out
in `FreezingConclusion`. One pair `C, p` serves both cases. -/
def Statement.lemma_A_2 : Prop :=
  ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
    (∀ (B : HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)) (μ Lip : ℝ), 0 < μ → 0 ≤ Lip →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ Lip * dist a b) →
      (∀ a (w : Vec3), μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ) →
      FreezingConclusion endpointStrongSpatialLeray endpointStrongSpatialLeray_idempotent
        C p B μ Lip) ∧
    (∀ (B : HalfHolder (UnitAddTorus (Fin 3)) (Paths →L[ℝ] Paths)) (μ Lip : ℝ), 0 < μ → 0 ≤ Lip →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ Lip * dist a b) →
      (∀ a (w : Paths), endpointIntegral 1 w = 0 → μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ) →
      FreezingConclusion (endpointStrongMixedLeray 1)
        (endpointStrongMixedLeray_idempotent zero_lt_one) C p B μ Lip)

end

end TorusEuler.Paper
