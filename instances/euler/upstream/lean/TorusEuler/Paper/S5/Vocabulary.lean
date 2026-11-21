import TorusEuler.PaperPhysicalLaterStep
import TorusEuler.PaperPhysicalCutoff
import TorusEuler.PaperHierarchyInverse
import TorusEuler.PaperHierarchyRelay
import TorusEuler.PaperGraphReadout
import TorusEuler.PaperPhysicalMeanStatements
import TorusEuler.PaperParentCoefficientStatements

/-!
# Vocabulary for the statements of Section 5 of the latest manuscript

This module fixes, in the notation of the latest manuscript
(`paper/craik_criminale_rewrite/sections/08a_parent_step.tex`,
`05b_parent_coefficients.tex`, `06c_finite_hierarchy.tex`,
`06d_mean_estimates.tex`, `08_exact_wave.tex`), the objects that the statements
of Propositions 5.1–5.11 talk about:

* the standing hypotheses of §5.1 on the parent (`Parent`), on the wave vector
  and the activation time (`Launch`) and on the central seed (`Origin`);
* the seed of (3.2), (5.4) in predicate form (`IsSeed`), the leading
  oscillation `A₁ = g 𝐚 F_h` and its pressure `𝗉[A₁]` of (3.3);
* the finite norms `‖·‖_{[n],γ}`, `‖·‖_{[n]}` of (D.1) (`wNorm`, `uNorm`,
  `launchNorm`);
* the sources (5.25)–(5.28), the remainder (5.30) and the expansion of §5.5 in
  predicate form (`IsExpansion`): every family of profiles satisfying the
  defining recursions. The divergence corrections use the latest indexing
  `C₁ = 0`, `C_{p+1} = C[V_p]` (`Cd`).

No definition here chooses an object from the content of a numbered result:
every object fixed in the text enters through a predicate that it satisfies.
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5

open HierarchyTwistedProfile LocalizedAmplitude ChildFlow

noncomputable section

/-! ## Finite norms (D.1) -/

section Norms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm (D.1) `‖τ f‖_{[n]}` of a field `f(t,a,s)` on a time set `A`,
`∑_{m+j≤n} ℓ_*^m h^j |∂_s^j τ f|_m`, with a time multiplier `τ`. It is the
library word norm `hierarchyFiniteWordNorm` over ordered derivative words in
the three scaled label directions `ℓ_* ∂_{a_i}` and the scaled phase direction
`h ∂_s`, each word contributing the supremum over `t ∈ A` and all labels and
phases. -/
def fieldNorm (ℓ h : ℝ) (A : Set ℝ) (τ : ℝ → ℝ) (n : ℕ) (f : ℝ → Vec3 × ℝ → E) : ℝ :=
  hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n (fun (t : A) x => τ t • f t x)

variable {T : ℝ} {k : Vec3}

/-- The weighted norm `‖f‖_{[n],γ} = ‖f/γ‖_{[n]}` of (D.1) on `[t₀,T]` for a
profile. It agrees with the library seminorm `amplitudeSeminorm False ℓ h n`
(by `amplitudeSeminorm_apply`). -/
def wNorm (ℓ h t₀ : ℝ) (γ : ℝ → ℝ) (n : ℕ) (f : HierarchyTwistedProfile T k E) : ℝ :=
  fieldNorm ℓ h (Icc t₀ T) (fun t => (γ t)⁻¹) n (fun t x => f.val.val.val (t, x))

/-- The unweighted norm `‖f‖_{[n]}` of (D.1) on the whole slab `[0,T]` for a
profile. It agrees with the library seminorm `unweightedSeminorm False ℓ h n`. -/
def uNorm (ℓ h : ℝ) (n : ℕ) (f : HierarchyTwistedProfile T k E) : ℝ :=
  fieldNorm ℓ h (Icc 0 T) (fun _ => 1) n (fun t x => f.val.val.val (t, x))

/-- The norm `‖f(t₀)‖_{[n]}` of the slice at one time, as in (5.20). -/
def launchNorm (ℓ h t₀ : ℝ) (n : ℕ) (f : HierarchyTwistedProfile T k E) : ℝ :=
  fieldNorm ℓ h {t₀} (fun _ => 1) n (fun t x => f.val.val.val (t, x))

end Norms

/-! ## The standing hypotheses of §5.1 (`08a_parent_step.tex`) -/

/-- The standing hypotheses of §5.1 on the parent `U` on `[0,T] × 𝕋³`
(`08a_parent_step.tex:9-33, 99-104`): `T ≤ 1`, `𝖣 ≥ 2`, `λ ≥ 1`; `U` smooth,
periodic, odd and divergence free with flow `X`; `U` supported on frequencies at
most `2𝖣`; the bounds (5.1); the residual `R_U = U_t + U·∇U + ∇p_U` odd,
supported on frequencies at most `4𝖣` and of size (5.6); and the coercivity
(5.2) `D²p_U - ∇R_U ≤ Id`.

Representation: the torus is represented by `ℤ³`-periodic fields on `ℝ³`;
"supported on frequencies at most `Λ`" is `RealTorusFourierBand Λ` of the
continuous torus field that lifts to the given field; the label flow is
`X s t` (transition from time `s` to time `t`), so `D_aX(t,a)` is
`fderiv ℝ (X 0 t) a` and `(D_aX(t,a))⁻¹` is `fderiv ℝ (X t 0) (X 0 t a)`;
matrix norms are operator norms. The pressure `p` is any smooth periodic
pressure whose residual has the properties that §5.1 derives for the zero-mean
pressure `p_U` with `Δp_U = -tr((∇U)²)`: odd, band limited by `4𝖣`, of size
(5.6); in particular `p = p_U` is admitted. -/
structure Parent (T : ℝ) (U : Velocity) (X : ℝ → Velocity) (pU : Pressure) (D lam : ℝ) :
    Prop where
  time_le_one : T ≤ 1
  scale_ge_two : 2 ≤ D
  frequency_ge_one : 1 ≤ lam
  flow : IsLabelFlowOn U X (Icc 0 T)
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3))
  velocity_periodic : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)
  velocity_odd : ∀ t ∈ Icc 0 T, Function.Odd (U t)
  divergence_free : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0
  velocity_band : ∃ v : ℝ → C(UnitAddTorus (Fin 3), Vec3), ∀ t ∈ Icc 0 T,
    (∀ x, v t (toUnitTorus x) = U t x) ∧ RealTorusFourierBand (2 * D) (v t)
  /-- (5.1), first bound. -/
  gradient_le : ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (U t) x‖ ≤ D
  /-- (5.1), second bound for `D_aX`. -/
  deformation_le : ∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D
  /-- (5.1), second bound for `(D_aX)⁻¹`. -/
  inverse_deformation_le : ∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry pU) (Icc 0 T ×ˢ (univ : Set Vec3))
  pressure_periodic : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (pU t)
  residual_odd : ∀ t ∈ Icc 0 T, Function.Odd (momentumResidual (Icc 0 T) U pU t)
  /-- `R_U` is supported on frequencies at most `4𝖣`, and (5.6). -/
  residual_band : ∃ r : ℝ → C(UnitAddTorus (Fin 3), Vec3), ∀ t ∈ Icc 0 T,
    (∀ x, r t (toUnitTorus x) = momentumResidual (Icc 0 T) U pU t x) ∧
      RealTorusFourierBand (4 * D) (r t) ∧ ‖r t‖ ≤ lam ^ (-5 / 2 : ℝ)
  /-- (5.2). -/
  coercive : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
    ⟪(fderiv ℝ (gradient (pU t)) x - fderiv ℝ (momentumResidual (Icc 0 T) U pU t) x) v, v⟫_ℝ ≤
      ‖v‖ ^ 2

/-- The transported wave vector `κ(t,a) = (D_aX(t,a))^{-T} k_*` of §3.1. -/
def waveVector (X : ℝ → Velocity) (k : Vec3) (t : ℝ) (a : Vec3) : Vec3 :=
  labelWaveVector X 0 a k t

/-- The matrix `M(t,a) = (D_xU)(t, X(t,a))` of §3.1. -/
def strainField (U : Velocity) (X : ℝ → Velocity) (t : ℝ) (a : Vec3) : Vec3 →L[ℝ] Vec3 :=
  fderiv ℝ (U t) (X 0 t a)

/-- The wave vector `k_* ≠ 0`, the activation time `t₀ ∈ [0,T)` and the
frequency `λ = |κ(t₀,0)|` of the wave of §5.1 (`08a_parent_step.tex:35-40`). -/
structure Launch (T : ℝ) (X : ℝ → Velocity) (k : Vec3) (lam t₀ : ℝ) : Prop where
  start_nonneg : 0 ≤ t₀
  start_lt : t₀ < T
  carrier_ne_zero : k ≠ 0
  frequency : ‖waveVector X k t₀ 0‖ = lam

/-- The seed at the origin `𝐚(t,0) = center t`, `t₀ ≤ t ≤ T`, of §5.1
(`08a_parent_step.tex:47-53, 78-94`): a nonzero solution of the seed equation
(3.2) at `a = 0`, perpendicular to `κ(t,0)`, with the two conditions (5.5)
(`CenterWaveOn`: growth of transverse solutions relative to the seed, and the
coupling `ν(t,0) ≥ 𝖣⁻¹`), normalized so that `γ(t) = λ^{3/4}|𝐚(t,0)| ≤ 1`.

Representation: the normalization `max_{t₀≤t≤T} |𝐚(t,0)| = λ^{-3/4}` of §5.1 is
weakened to `γ ≤ 1`, which is all that is used; the coupling condition of (5.5)
is written as `𝖣⁻¹ |κ||𝐚| ≤ κ·M𝐚` at the origin. The library structure
`CenterWaveOn` also records, on `[t₀,T]`, the covector equation
`κ(t,0)_t = -M(t,0)^T κ(t,0)` (field `covector`, time derivative within `[t₀,T]`)
and `κ(t,0) ≠ 0` (in `nonzero`, with `𝐚(t,0) ≠ 0` and `κ·𝐚 = 0` at the origin).
These two are not assumptions of the text: they hold for every parent with its
flow, since `κ = (D_aX)^{-T} k_*` with `k_* ≠ 0`, and they are kept for the library
interface. -/
structure Origin (T : ℝ) (U : Velocity) (X : ℝ → Velocity) (k : Vec3) (D lam t₀ : ℝ)
    (center : ℝ → Vec3) : Prop where
  wave : CenterWaveOn (fun t => strainField U X t 0) (fun t => waveVector X k t 0) center t₀ T D
  normalized : ∀ t ∈ Icc t₀ T, lam ^ (3 / 4 : ℝ) * ‖center t‖ ≤ 1

/-- The envelope radius `ℓ_* = 𝖣^{-a}` with the absolute exponent `a`. -/
def radius (D : ℝ) (a : ℕ) : ℝ := (D ^ a)⁻¹

/-- The profile width `h = λ^{-1/2}`. -/
def width (lam : ℝ) : ℝ := lam ^ (-1 / 2 : ℝ)

/-- The weight `γ(t) = λ^{3/4}|𝐚(t,0)|` of §5.1. -/
def weight (lam : ℝ) (center : ℝ → Vec3) (t : ℝ) : ℝ := lam ^ (3 / 4 : ℝ) * ‖center t‖

/-- The support `supp g` of the envelope `g(a) = χ(|a|/ℓ_*)`, repeated over the
label lattice. -/
def envelopeSupport (ℓ : ℝ) : Set Vec3 := tsupport (periodizeCentered (radialEnvelope ℓ))

/-- The seed of §5.1 in predicate form: on `[t₀,T]` it solves the seed equation
(3.2) at every label, starts from (5.4)
`𝐚(t₀,a) = (Id - P_{κ(t₀,a)}) 𝐚(t₀,0)`, and equals the central seed at the origin.
It stays perpendicular to `κ` (§3.1, after (3.2)) and is smooth; both
properties hold for the unique solution and are recorded with it.

Representation: the seed operator `-M𝐚 + 2κ(κ·M𝐚)/|κ|²` is
`affineWaveAmplitudeOperator M κ`; `Id - P_κ` is `oscillatoryTransverseProjection κ`. -/
structure IsSeed (U : Velocity) (X : ℝ → Velocity) (k : Vec3) (t₀ T : ℝ) (center : ℝ → Vec3)
    (amp : ℝ → Vec3 → Vec3) : Prop where
  at_origin : ∀ t ∈ Icc t₀ T, amp t 0 = center t
  start : ∀ a, amp t₀ a = oscillatoryTransverseProjection (waveVector X k t₀ a) (center t₀)
  equation : ∀ a, ∀ t ∈ Icc t₀ T, HasDerivWithinAt (fun r => amp r a)
    (affineWaveAmplitudeOperator (strainField U X t a) (waveVector X k t a) (amp t a)) (Icc t₀ T) t
  transverse : ∀ a, ∀ t ∈ Icc t₀ T, ⟪waveVector X k t a, amp t a⟫_ℝ = 0
  smooth : ContDiffOn ℝ ∞ (Function.uncurry amp) (Icc t₀ T ×ˢ (univ : Set Vec3))

/-- The leading oscillation `A₁ = g 𝐚 F_h` of (3.3), with the envelope
`g = radialEnvelope ℓ_*` and the profile `F_h = waveProfile h` of Lemma 3.1. -/
def leading (ℓ h : ℝ) (amp : ℝ → Vec3 → Vec3) (t : ℝ) (a : Vec3) (s : ℝ) : Vec3 :=
  (radialEnvelope ℓ a * waveProfile h s) • amp t a

/-- The leading pressure `𝗉[A₁] = -p_w g P_h` of (3.3), with
`p_w = 2 κ·M𝐚/|κ|²` and the zero-mean primitive `P_h = wavePressurePrimitive h`. -/
def leadingPressure (U : Velocity) (X : ℝ → Velocity) (k : Vec3) (ℓ h : ℝ)
    (amp : ℝ → Vec3 → Vec3) (t : ℝ) (a : Vec3) (s : ℝ) : ℝ :=
  -wavePressureCoefficient (radialEnvelope ℓ a) (waveVector X k t a) (amp t a) (strainField U X t a) *
    wavePressurePrimitive h s

/-! ## The operators of the expansion -/

section Operators

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

/-- The actions of `∂_t + M`, `𝐝`, `κ∂_s`, `(Z·𝐝)Z'`, `(Z·κ)∂_sY` and the phase
average `⟨·⟩` on the profiles of a parent with coefficient profiles
`(D_aX)⁻¹`, `M`, `κ` (represented by a `ParentGeometry`). -/
abbrev ops (d : ParentGeometry hT U X k) :
    HierarchyOperators (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ) :=
  twistedHierarchyOperators hT d.inverse d.strain d.covector

/-- The divergence correction `C[V] = 𝐝 × Q[V]` of (3.5). -/
def curlCorrection (d : ParentGeometry hT U X k) (V : HierarchyTwistedProfile T k Vec3) :
    HierarchyTwistedProfile T k Vec3 :=
  complete hT d.inverse d.covector d.oscillation.covector_independent
    d.oscillation.covector_ne_zero V

/-- The divergence `𝐝̃ · W` with `𝐝̃ = 𝐝 + κ∂_s` of §3.1. -/
def totalDivergence (d : ParentGeometry hT U X k) (W : HierarchyTwistedProfile T k Vec3) :
    HierarchySmoothProfile T ℝ :=
  HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val W.val.val

/-- A solution `(B, q̄)` of the mean equation (5.11) with source `f̄`:
`B_t + MB + 𝐝q̄ = f̄`, `B` and `q̄` independent of the phase, and
`B = D_aX z_t` with a smooth periodic displacement `z`, `z(0) = z(T) = 0`, whose
velocity `v = z_t` is divergence free.

Representation: `𝐝·B = 0` is written as `div_a v = 0` for `v = (D_aX)⁻¹B`; the two
are equivalent by the Piola identity, since `det D_aX = 1`. -/
structure MeanSolution (d : ParentGeometry hT U X k) (f B : HierarchyTwistedProfile T k Vec3)
    (q : HierarchyTwistedProfile T k ℝ) : Prop where
  momentum : (ops d).material B + (ops d).labelGrad q = f
  phase_independent : (ops d).average B = B
  pressure_phase_independent : (ops d).phaseGrad q = 0
  endpoint : ∃ v z : Velocity,
    ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
    ContDiffOn ℝ ∞ (Function.uncurry z) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
    (∀ t ∈ Icc 0 T, SpatiallyPeriodic (v t) ∧ SpatiallyPeriodic (z t)) ∧
    z 0 = 0 ∧ z T = 0 ∧
    (∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt (fun r => z r a) (v t a) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, ∀ a, divergence (v t) a = 0) ∧
    ∀ t ∈ Icc 0 T, ∀ a s, B.val.val.val (t, a, s) = fderiv ℝ (X 0 t) a (v t a)

/-- A solution `(V, 𝗉)` of the transverse equation (5.15) with source `f` that
starts from zero: `V_t + MV + κ∂_s𝗉 = f`, `κ·V = 0`, `⟨V⟩ = 0`, `V(0) = 0`, and
`𝗉` has zero phase mean (it is the zero-mean primitive of (5.16)). -/
structure TransverseSolution (d : ParentGeometry hT U X k) (f V : HierarchyTwistedProfile T k Vec3)
    (q : HierarchyTwistedProfile T k ℝ) : Prop where
  momentum : (ops d).material V + (ops d).phaseGrad q = f
  transverse : ∀ t ∈ Icc 0 T, ∀ a s, ⟪waveVector X k t a, V.val.val.val (t, a, s)⟫_ℝ = 0
  mean_zero : (ops d).average V = 0
  initial : ∀ a s, V.val.val.val (0, a, s) = 0
  pressure_mean_zero : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun s => q.val.val.val (t, a, s)) = 0

end Operators

/-! ## The finite expansion of §5.5 (`06c_finite_hierarchy.tex:222-302`) -/

section Algebra

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The divergence correction of level `q` in the latest indexing:
`C_q = C[V_{q-1}]` for `q ≥ 2` and `C₁ = 0`. The library field `u.C` is indexed
by the level of the source oscillation, so `Cd u q = u.C (q - 1)`. -/
def Cd (u : HierarchyProfiles E F) (q : ℕ) : E := u.C (q - 1)

/-- `Y_p = V_p + C_p`. -/
def Yd (u : HierarchyProfiles E F) (p : ℕ) : E := u.V p + Cd u p

/-- `Z_p = Y_p + B_p`. -/
def Zd (u : HierarchyProfiles E F) (p : ℕ) : E := Yd u p + u.B p

/-- The expansion `W = ∑_{p=1}^P (V_p + C_{p+1} + B_p)` of Proposition 5.4. -/
def expansion (u : HierarchyProfiles E F) (P : ℕ) : E :=
  ∑ p ∈ Finset.Icc 1 P, (u.V p + Cd u (p + 1) + u.B p)

/-- The pressure `𝖯 = ∑_{p=1}^P (𝗉_p + q̄_p)` of Proposition 5.4. -/
def expansionPressure (u : HierarchyProfiles E F) (P : ℕ) : F :=
  ∑ p ∈ Finset.Icc 1 P, (u.p p + u.q p)

/-- The terms `H_p` left at level `p ≥ 2`, (5.25)–(5.26):
`H_p = (∂_t+M)C_p + 𝐝𝗉_{p-1} + ∑_{i+j=p} (Z_i·𝐝)Z_j + ∑_{i+j=p+1, i≥2} (C_i·κ)∂_sY_j`,
where at `p = 2` the activation term `C[χ̃'A₁] = χ̃'C[A₁]` (argument `cS`) is
removed, so that the linear part of `H₂` is `χ̃[(∂_t+M)C[A₁] + 𝐝𝗉[A₁]]` as in
(5.25) (`C₂ = χ̃C[A₁]`, `𝗉₁ = χ̃𝗉[A₁]`). -/
def levelSource (A : HierarchyOperators E F) (u : HierarchyProfiles E F) (cS : E) (p : ℕ) : E :=
  A.material (Cd u p) + A.labelGrad (u.p (p - 1)) - (if p = 2 then cS else 0) +
    (∑ ij ∈ (Finset.Icc 1 p ×ˢ Finset.Icc 1 p).filter (fun ij => ij.1 + ij.2 = p),
      A.labelAdv (Zd u ij.1) (Zd u ij.2)) +
    ∑ ij ∈ (Finset.Icc 2 p ×ˢ Finset.Icc 1 p).filter (fun ij => ij.1 + ij.2 = p + 1),
      A.phaseAdv (Cd u ij.1) (Yd u ij.2)

/-- The oscillatory source `f_p = -(H_p - ⟨H_p⟩)` of (5.27). -/
def oscSource (A : HierarchyOperators E F) (u : HierarchyProfiles E F) (cS : E) (p : ℕ) : E :=
  -(levelSource A u cS p - A.average (levelSource A u cS p))

/-- The mean source `f̄_p = -⟨H_p⟩` (`p ≥ 3`), `f̄₂ = -⟨H₂⟩ - R_U∘X` of (5.27);
the argument `R` is the pulled-back parent residual `R_U∘X`. -/
def meanSource (A : HierarchyOperators E F) (u : HierarchyProfiles E F) (cS R : E) (p : ℕ) : E :=
  -A.average (levelSource A u cS p) - (if p = 2 then R else 0)

/-- The source `f_p^S = -∑_{i=2}^p (B_i·κ)∂_s Y_{p+1-i}` of (5.28). -/
def suppSource (A : HierarchyOperators E F) (u : HierarchyProfiles E F) (p : ℕ) : E :=
  -∑ i ∈ Finset.Icc 2 p, A.phaseAdv (u.B i) (Yd u (p + 1 - i))

/-- The remainder `R_P` of (5.30):
`(∂_t+M)C_{P+1} + 𝐝𝗉_P + ∑_{i,j≤P+1, i+j≥P+1} (Z_i·𝐝)Z_j
 + ∑_{i,j≤P+1, i+j≥P+2} (Z_i·κ)∂_sY_j`. -/
def remainder (A : HierarchyOperators E F) (u : HierarchyProfiles E F) (P : ℕ) : E :=
  A.material (Cd u (P + 1)) + A.labelGrad (u.p P) +
    (∑ ij ∈ (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter (fun ij => P + 1 ≤ ij.1 + ij.2),
      A.labelAdv (Zd u ij.1) (Zd u ij.2)) +
    ∑ ij ∈ (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter (fun ij => P + 2 ≤ ij.1 + ij.2),
      A.phaseAdv (Zd u ij.1) (Yd u ij.2)

end Algebra

section Expansion

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

/-- The expansion of depth `P` of §5.5 in predicate form: `u` is a family of
profiles `V_p, C_p, B_p, 𝗉_p, q̄_p` obtained from the defining recursions.

* `R` is the pulled-back parent residual `R_U∘X`, and `S` is the activation term
  `χ̃'A₁` of (3.8) (so `R_χ̃ = S + C[S]`).
* Level one (3.7): `V₁ = χ̃A₁`, `𝗉₁ = χ̃𝗉[A₁]` on the label cell, `B₁ = 0`,
  `q̄₁ = 0`, `C₁ = 0`.
* `C_{p+1} = C[V_p]` for `1 ≤ p ≤ P` (in particular `C₂ = C[V₁] = χ̃C[A₁]`).
* For `2 ≤ p ≤ P`: `(B_p, q̄_p)` solves the mean equation (5.11) with source `f̄_p`
  of (5.27), `q̄_p` with zero mean over the label cell (the pressure `𝗊` of
  Theorem 4.2); `(V_p, 𝗉_p)` solves (5.15) with `V_p(0) = 0` and source
  `f_p + f_p^S` of (5.27), (5.28).
* `V_{P+1} = B_{P+1} = 0` (convention stated in Proposition 5.4).

Representation: profiles are lattice-twisted smooth profiles on the closed slab
(`HierarchyTwistedProfile`), so the profiles on the label cell `[-1/2,1/2]³`
extend periodically as in §3.1, and joint smoothness is part of the type; the
values on the cell determine a profile. The library field `u.C q` stores
`C_{q+1}` (see `Cd`). -/
structure IsExpansion (d : ParentGeometry hT U X k) (pU : Pressure) {t₀ : ℝ}
    (χ : PaperWaveCutoff t₀ T) (ℓ h : ℝ) (amp : ℝ → Vec3 → Vec3) (P : ℕ)
    (R S : HierarchyTwistedProfile T k Vec3)
    (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)) :
    Prop where
  /-- `R = R_U∘X`. -/
  residual : ∀ z ∈ hierarchyProfileSlab T,
    R.val.val.val z = momentumResidual (Icc 0 T) U pU z.1 (X 0 z.1 z.2.1)
  /-- `S = χ̃'A₁`, the activation term of (3.8). -/
  activation : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
    S.val.val.val (t, a, s) = χ.derivative t • leading ℓ h amp t a s
  /-- `V₁ = χ̃A₁`, (3.7). -/
  leading_velocity : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
    (u.V 1).val.val.val (t, a, s) = χ.value t • leading ℓ h amp t a s
  /-- `𝗉₁ = χ̃𝗉[A₁]`, (3.7). -/
  leading_pressure : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
    (u.p 1).val.val.val (t, a, s) = χ.value t * leadingPressure U X k ℓ h amp t a s
  /-- `C₁ = 0`. -/
  first_correction : Cd u 1 = 0
  /-- `B₁ = 0` and `q̄₁ = 0`. -/
  first_mean : u.B 1 = 0 ∧ u.q 1 = 0
  /-- `C_{p+1} = C[V_p]`, `1 ≤ p ≤ P`. -/
  correction : ∀ p ∈ Finset.Icc 1 P, Cd u (p + 1) = curlCorrection d (u.V p)
  /-- `(B_p, q̄_p)` solves (5.11) with source `f̄_p`, `q̄_p` of zero mean. -/
  mean : ∀ p ∈ Finset.Icc 2 P,
    MeanSolution d (meanSource (ops d) u (curlCorrection d S) R p) (u.B p) (u.q p) ∧
      ∀ t ∈ Icc 0 T, (∫ a in centeredCell, (u.q p).val.val.val (t, a, 0)) = 0
  /-- `(V_p, 𝗉_p)` solves (5.15) from `V_p(0) = 0` with source `f_p + f_p^S`. -/
  transverse : ∀ p ∈ Finset.Icc 2 P,
    TransverseSolution d (oscSource (ops d) u (curlCorrection d S) p + suppSource (ops d) u p)
      (u.V p) (u.p p)
  /-- `V_{P+1} = B_{P+1} = 0`. -/
  top : u.V (P + 1) = 0 ∧ u.B (P + 1) = 0

end Expansion

/-! ## Frequency truncation (Appendix B, §5.7) -/

/-- The symbol `ψ` of the frequency cutoff of Appendix B: radial, smooth,
`0 ≤ ψ ≤ 1`, `ψ = 1` on `|ζ| ≤ 1` and `supp ψ ⊆ {|ζ| ≤ 2}`. -/
structure CutoffSymbol (ψ : Vec3 → ℝ) : Prop where
  radial : ∀ ξ η : Vec3, ‖ξ‖ = ‖η‖ → ψ ξ = ψ η
  smooth : ContDiff ℝ ∞ ψ
  range : ∀ ξ, 0 ≤ ψ ξ ∧ ψ ξ ≤ 1
  unit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1
  support : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0

/-- The truncation of §5.7 (5.55) in predicate form: `u = S_Λ V` on `[0,T]`
and `p` is the smooth periodic function of zero mean with
`Δp = -tr((∇u)²)`.

Representation: `S_Λ V` is the real Fourier cutoff `realVectorFourierCutoff ψ Λ`
applied at each time to the continuous torus field that lifts to `V t`. -/
structure IsTruncation (T : ℝ) (ψ : Vec3 → ℝ) (Λ : ℝ) (V : Velocity) (u : Velocity)
    (p : Pressure) : Prop where
  cutoff : ∀ t ∈ Icc 0 T, ∀ c : C(UnitAddTorus (Fin 3), Vec3),
    (∀ x, c (toUnitTorus x) = V t x) → ∀ x, u t x = realVectorFourierCutoff ψ Λ c (toUnitTorus x)
  pressure_smooth : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (p t)
  pressure_periodic : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (p t)
  pressure_mean_zero : ∀ t ∈ Icc 0 T, (∫ x in centeredCell, p t x) = 0
  poisson : ∀ t ∈ Icc 0 T, ∀ x, divergence (gradient (p t)) x =
    -LinearMap.trace ℝ Vec3 ((fderiv ℝ (u t) x).comp (fderiv ℝ (u t) x)).toLinearMap

end

end TorusEuler.Paper.S5
