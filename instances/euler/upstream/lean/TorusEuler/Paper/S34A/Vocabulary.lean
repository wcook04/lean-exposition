import TorusEuler.WaveProfile
import TorusEuler.PaperAppendixAInverse
import TorusEuler.FreezingSolvability
import TorusEuler.EndpointConcreteProjection
import TorusEuler.FourierHolderTail
import TorusEuler.TorusLabelFlow

/-! Vocabulary for the statements of Lemma 3.1, Lemma 4.1, Theorem 4.2,
Theorem A.1 and Lemma A.2 of the latest manuscript (package S34A).

Every definition here is an explicit formula or a list of properties. None of
them chooses an object from the content of a numbered result.

Conventions. The torus `𝕋³` is represented by `ℤ³`-periodic objects on
`Vec3 = ℝ³` (labels `a : Vec3`, lifted through `toUnitTorus`) or by the flat
torus `UnitAddTorus (Fin 3)`. A label flow `X : ℝ → Velocity` is the two-time
flow of the parent: `X s t a` is the position at time `t` of the particle that
is at `a` at time `s`, so the flow `X(t,a)` of the manuscript is `X 0 t a` and
the back-to-label map `X(t,·)⁻¹` is `X t 0`. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

/-! ### Lemma 3.1 -/

/-- The property list of **Lemma 3.1** (`cc:uf:exact:lem:profile`,
sections/04_localized_wave.tex:152) for a family `F h` of profiles and a family
`P h` of primitives, `0 < h ≤ 1`: `F h` is odd, smooth and `1`-periodic, `P h`
is a smooth `1`-periodic primitive of `F h` with zero mean over a period,
`F_h'(0) = 1`, `-C h ≤ F_h' ≤ 1`, `‖F_h‖_∞ ≤ C h`, and
`‖∂_s^j F_h‖_∞ ≤ C_j h^{1-j}` for `j ≥ 2`, with `C` and `C_j` independent of
`h`.

Representation: the supremum bounds are stated pointwise in the phase `s`;
`phaseMean` is the integral over `[0,1]`. -/
def ProfileFamily (F P : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∀ h, 0 < h → h ≤ 1 →
      ContDiff ℝ ∞ (F h) ∧ Function.Odd (F h) ∧ Function.Periodic (F h) 1 ∧
      ContDiff ℝ ∞ (P h) ∧ Function.Periodic (P h) 1 ∧ phaseMean (P h) = 0 ∧
      (∀ s, HasDerivAt (P h) (F h s) s) ∧ deriv (F h) 0 = 1 ∧
      ∀ s, -C * h ≤ deriv (F h) s ∧ deriv (F h) s ≤ 1 ∧ ‖F h s‖ ≤ C * h) ∧
    ∀ j : ℕ, 2 ≤ j → ∃ Cj : ℝ, 0 < Cj ∧ ∀ h, 0 < h → h ≤ 1 → ∀ s,
      ‖iteratedDeriv j (F h) s‖ ≤ Cj * h ^ (1 - (j : ℤ))

/-! ### The parent of Section 4 and the coefficients (4.1) -/

/-- The standing setting of Section 4 (sections/06b_mean_inverse.tex:8–10):
`0 < T ≤ 1`, the parent `U` is a smooth divergence-free field on
`[0,T] × 𝕋³` (not assumed to solve any equation), and `X` is its flow.

Representation: `U` is `ℤ³`-periodic on `ℝ³` and smooth on the closed slab
`[0,T] × ℝ³`; the flow is the two-time label flow `IsLabelFlowOn U X [0,T]`,
which contains the flow `X(t,a) = X 0 t a` and its inverse `X t 0`. The flow is
volume preserving because `U` is divergence free. -/
structure MeanParentFlow (T : ℝ) (U : Velocity) (X : ℝ → Velocity) : Prop where
  time_pos : 0 < T
  time_le_one : T ≤ 1
  smooth : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3))
  periodic : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)
  divergence_free : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0
  flow : IsLabelFlowOn U X (Icc 0 T)

/-- The deformation `D_aX(t,a)` of the flow `X(t,a) = X 0 t a`. -/
def meanDeformation (X : ℝ → Velocity) (t : ℝ) (a : Vec3) : Vec3 →L[ℝ] Vec3 :=
  fderiv ℝ (X 0 t) a

/-- The inverse deformation `(D_aX(t,a))⁻¹`, written as the derivative of the
back-to-label map `X t 0` at the position `X(t,a)`. For a label flow of a
smooth periodic parent this is the two-sided inverse of `meanDeformation X t a`
(`IsLabelFlowOn.labelDerivative_inverse`). -/
def meanDeformationInv (X : ℝ → Velocity) (t : ℝ) (a : Vec3) : Vec3 →L[ℝ] Vec3 :=
  fderiv ℝ (X t 0) (X 0 t a)

/-- The velocity gradient along the flow, `M = (∇u)∘X` in (4.1), with
`(∇u)_{ij} = ∂_j u_i` (the Fréchet derivative). -/
def meanGradient (U : Velocity) (X : ℝ → Velocity) (t : ℝ) (a : Vec3) : Vec3 →L[ℝ] Vec3 :=
  fderiv ℝ (U t) (X 0 t a)

/-- The label time derivative `M_t` of `M` at fixed label, taken within `[0,T]`. -/
def meanGradientRate (T : ℝ) (U : Velocity) (X : ℝ → Velocity) (t : ℝ) (a : Vec3) :
    Vec3 →L[ℝ] Vec3 :=
  derivWithin (fun r => meanGradient U X r a) (Icc 0 T) t

/-- The matrix `H^# = -(M_t + M²)` of (4.1). -/
def meanHsharp (T : ℝ) (U : Velocity) (X : ℝ → Velocity) (t : ℝ) (a : Vec3) :
    Vec3 →L[ℝ] Vec3 :=
  endpointHessian (meanGradient U X t a) (meanGradientRate T U X t a)

/-- The kinetic coefficient `K = (D_aX)ᵀ D_aX` of (4.1). -/
def meanKinetic (X : ℝ → Velocity) (t : ℝ) (a : Vec3) : Vec3 →L[ℝ] Vec3 :=
  kineticForm (meanDeformation X t a)

/-- The pulled-back vorticity `Ω = (D_aX)ᵀ (Mᵀ - M) D_aX` of (4.1). -/
def meanVorticity (U : Velocity) (X : ℝ → Velocity) (t : ℝ) (a : Vec3) : Vec3 →L[ℝ] Vec3 :=
  vorticityForm (meanDeformation X t a) (meanGradient U X t a)

/-! ### The endpoint system (4.9) and the system of Theorem A.1 -/

/-- A solution of the integrated endpoint system on `I = [0,T]` in the class of
Theorem 4.2 and Theorem A.1 (system (4.9), sections/06b_mean_inverse.tex:130;
sections/appA_mean_regularity.tex:30–33):
`K z_t - ∫_0^t Ω z_t + L = c + ∇φ`, `div z = 0`, `z(0) = z(T) = 0`, with
`z ∈ C¹(I; C^{0,1/2})`, `c ∈ C^{0,1/2}` divergence free and
`∇φ ∈ C(I; C^{0,1/2})`.

Representation: `C^{0,1/2}` is the space `HalfHolder (UnitAddTorus (Fin 3)) Vec3`
(maximum of the supremum and the `1/2`-seminorm). The displacement `z` and its
velocity `v = z_t` take values in the closed subspace
`endpointHalfHolderSolenoidal` of weakly divergence-free fields, which encodes
`div z = 0` and `div c = 0`; `z ∈ C¹` is the derivative `v` of `z` within `I`
together with continuity of `v`. The pressure gradient is a continuous curve
`G` in `C^{0,1/2}` whose lift is the gradient of the periodic potential `φ t`.
The left side of the equation is `paperMeanIntegratedMomentum K Ω L v t`
`= K(t)v(t) - ∫_0^t Ω(s)v(s) ds + L(t)`, with pointwise coefficient
multiplication. -/
structure EndpointSystemSolution (T : ℝ) (K Ω : ℝ → K½) (L : ℝ → C½) (z v : ℝ → S) (c : S)
    (φ : Pressure) (G : ℝ → C½) : Prop where
  velocity_continuous : ContinuousOn v (Icc 0 T)
  displacement_deriv : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (v t) (Icc 0 T) t
  initial : z 0 = 0
  terminal : z T = 0
  gradient_continuous : ContinuousOn G (Icc 0 T)
  potential : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (φ t) ∧
    ∀ x, HasGradientAt (φ t) (HalfHolder.eval (toUnitTorus x) (G t)) x
  equation : ∀ t ∈ Icc 0 T, paperMeanIntegratedMomentum K Ω L v t = (c : C½) + G t

/-! ### Lemma A.2 -/

/-- The conclusions of **Lemma A.2** (`cc:holder:freezing`,
sections/appA_mean_regularity.tex:71) for an idempotent `R` on
`C^{0,1/2}(𝕋³; H)`, a coefficient `B ∈ C^{0,1/2}(𝕋³; 𝓛(H))` with Lipschitz
constant `Lip`, and coercivity `μ`:

* `R B` is an isomorphism `e` of `R C^{0,1/2}(𝕋³;H)` (the fixed space of `R`),
  with the bound (A.5)
  `‖v‖_{C^{0,1/2}} ≤ C (2 + μ⁻¹ + ‖B‖_∞ + Lip)^p ‖R B v‖_{C^{0,1/2}}`;
* for every integer `k ≥ 1` with `B ∈ C^{k,1/2}`, the same operator is an
  isomorphism of `R C^{k,1/2}(𝕋³;H)`: `v` lies in `C^{k,1/2}` exactly when
  `R B v` does, and the `C^{k,1/2}` norms of `v` and `R B v` are comparable.

Representation: `R C^{k,1/2}` is the set of elements of the fixed space whose
periodic lift satisfies `SpatialHolderHalf k`, normed by
`spatialHolderHalfNorm k` (sum over orders `j ≤ k` of the supremum and the
`1/2`-seminorm of the `j`-th Fréchet derivative). The `C¹` norm
`‖B‖_{C¹_a 𝓛(H)}` of (A.5) is replaced by `‖B‖_∞ + Lip`; see
`Statement.lemma_A_2`. -/
def FreezingConclusion {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (R : HalfHolder (UnitAddTorus (Fin 3)) H →L[ℝ] HalfHolder (UnitAddTorus (Fin 3)) H)
    (hR : ∀ f, R (R f) = R f) (C : ℝ) (p : ℕ)
    (B : HalfHolder (UnitAddTorus (Fin 3)) (H →L[ℝ] H)) (μ Lip : ℝ) : Prop :=
  ∃ e : freezingFixedSpace R ≃L[ℝ] freezingFixedSpace R,
    (e : freezingFixedSpace R →L[ℝ] freezingFixedSpace R) =
      freezingCompression R B.coefficientMul hR ∧
    (∀ v : freezingFixedSpace R, ‖v‖ ≤ C * (2 + μ⁻¹ + ‖B.val.1‖ + Lip) ^ p * ‖e v‖) ∧
    ∀ k : ℕ, 1 ≤ k →
      SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) B) →
      (∀ v : freezingFixedSpace R,
        SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) ↔
          SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (e v).val)) ∧
      ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ v : freezingFixedSpace R,
        SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) →
        spatialHolderHalfNorm k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (e v).val) ≤
            Ck * spatialHolderHalfNorm k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) ∧
          spatialHolderHalfNorm k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) ≤
            Ck * spatialHolderHalfNorm k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (e v).val)

end

end TorusEuler.Paper
