import TorusEuler.TruncatedParentAdmissibility
import TorusEuler.TruncatedParentPoissonPressure
import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.S5Bridge.Norms
import TorusEuler.Paper.Proofs.S5Bridge.Children
import TorusEuler.TruncatedChildStage

/-! # The cutoff child of a step (package S678a)

Own glue of row 7.1 (item 4 of the proof, sections/08b_induction.tex:376-381; the truncation (5.55) of
Proposition 5.11, sections/08_exact_wave.tex:379-416).

`CutoffChild` is `TruncatedChildStage` (TruncatedChildStage.lean:234) without its three fields about
the residual of the approximate velocity (`approximateResidualTorus`, `approximateResidual_rep` and
`residual_cutoff`, the identity (5.58) of the proof of Proposition 5.11, which the proof of Theorem 7.1
does not use). `exists_cutoffChild` builds it from the clauses (T1) of Proposition 5.11 (hypotheses) and
`exists_truncatedParentPoissonPressure`, which reaches no content lemma. -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

local notation "Labels" => UnitAddTorus (Fin 3)

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler

noncomputable section

/-- `TruncatedChildStage` without the fields `approximateResidualTorus`, `approximateResidual_rep`,
`residual_cutoff`. -/
structure CutoffChild (T Λ : ℝ) (ψ : Vec3 → ℝ) (V : Velocity) where
  approximateTorus : ℝ → C(Labels, Vec3)
  torusVelocity : ℝ → C(Labels, Vec3)
  pressure : Pressure
  approximate_rep : ∀ t ∈ Icc 0 T, ∀ x, approximateTorus t (toUnitTorus x) = V t x
  cutoff : ∀ t z, torusVelocity t z = realVectorFourierCutoff ψ Λ (approximateTorus t) z
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => torusVelocity z.1 (toUnitTorus z.2))
    (Icc 0 T ×ˢ (univ : Set Vec3))
  odd_velocity : ∀ t ∈ Icc 0 T, Function.Odd (fun x => torusVelocity t (toUnitTorus x))
  divergence_free : ∀ t ∈ Icc 0 T, ∀ x, divergence (fun y => torusVelocity t (toUnitTorus y)) x = 0
  velocity_band : ∀ t ∈ Icc 0 T, RealTorusFourierBand (2 * Λ) (torusVelocity t)
  smooth_pressure : ContDiffOn ℝ ∞ (Function.uncurry pressure) (Icc 0 T ×ˢ (univ : Set Vec3))
  periodic_pressure : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (pressure t)
  mean_zero_pressure : ∀ t ∈ Icc 0 T, (∫ x in centeredCell, pressure t x) = 0
  poisson : ∀ t ∈ Icc 0 T, ∀ x, divergence (gradient (pressure t)) x =
    -LinearMap.trace ℝ Vec3 ((fderiv ℝ (fun y => torusVelocity t (toUnitTorus y)) x).comp
      (fderiv ℝ (fun y => torusVelocity t (toUnitTorus y)) x)).toLinearMap
  projected_eq : ∀ t ∈ Icc 0 T,
    momentumResidual (Icc 0 T) (fun r x => torusVelocity r (toUnitTorus x)) pressure t =
      closedSlabLerayMomentum 0 T (fun r x => torusVelocity r (toUnitTorus x)) t

namespace CutoffChild

variable {T Λ : ℝ} {ψ : Vec3 → ℝ} {V : Velocity}

/-- Real velocity on the Euclidean lift. -/
def velocity (s : CutoffChild T Λ ψ V) : Velocity := fun t x => s.torusVelocity t (toUnitTorus x)

/-- The true momentum residual computed using the selected pressure. -/
def residual (s : CutoffChild T Λ ψ V) : Velocity :=
  momentumResidual (Icc 0 T) s.velocity s.pressure

/-- The velocity of a cutoff child is spatially periodic at every time. -/
theorem periodic_velocity (s : CutoffChild T Λ ψ V) (t : ℝ) : SpatiallyPeriodic (s.velocity t) := by
  intro n x
  exact congrArg (s.torusVelocity t) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)

/-- The velocity of a cutoff child is the real Fourier cutoff of its approximate torus field. -/
theorem velocity_eq_cutoff (s : CutoffChild T Λ ψ V) (t : ℝ) :
    s.velocity t = fun x => realVectorFourierCutoff ψ Λ (s.approximateTorus t) (toUnitTorus x) :=
  funext fun x => s.cutoff t (toUnitTorus x)

end CutoffChild

/-- **The cutoff child exists** (the construction of `u = S_Λ V` and of its zero-mean pressure in
Proposition 5.11, sections/08_exact_wave.tex:379-416, without the display (5.58)). The facts (T1) of
`u` (smooth, odd, divergence free, frequencies at most `2Λ`) are the first conclusion clause of
Proposition 5.11 (`hT1`), applied to a truncation `(u₀, p₀)` obtained from its existence clause
(`hex`); the remaining glue is the torus lift of `V`, the identification of the lifted cutoff with
`u₀`, the joint smoothness of the Poisson pressure (`exists_truncatedParentPoissonPressure`) and the
Leray identity. -/
theorem exists_cutoffChild {T Λ : ℝ} (hT : 0 < T) {V : Velocity}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    {ψ : Vec3 → ℝ}
    (hex : ∃ (u : Velocity) (p : Pressure), S5.IsTruncation T ψ Λ V u p)
    (hT1 : ∀ (u : Velocity) (p : Pressure), S5.IsTruncation T ψ Λ V u p →
      ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
        ∀ t ∈ Icc 0 T, Function.Odd (u t) ∧ (∀ x, divergence (u t) x = 0) ∧
          ∃ c : C(UnitAddTorus (Fin 3), Vec3),
            (∀ x, c (toUnitTorus x) = u t x) ∧ RealTorusFourierBand (2 * Λ) c) :
    Nonempty (CutoffChild T Λ ψ V) := by
  classical
  have hslice (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (V t) := by
    have hj : ContDiff ℝ ∞ (fun x : Vec3 => (t, x)) := contDiff_const.prodMk contDiff_id
    exact contDiffOn_univ.1 (hV.comp hj.contDiffOn (fun x _ => ⟨ht, mem_univ x⟩))
  have hExists (t : ℝ) (ht : t ∈ Icc 0 T) :
      ∃ u : C(UnitAddTorus (Fin 3), Vec3), ∀ x, u (toUnitTorus x) = V t x :=
    (hVper t ht).exists_continuousTorusFunction (hslice t ht).continuous
  let gV (t : ℝ) : C(UnitAddTorus (Fin 3), Vec3) :=
    if ht : t ∈ Icc 0 T then (hExists t ht).choose else 0
  have hgV (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) : gV t (toUnitTorus x) = V t x := by
    simp only [gV, dite_eq_left ht]
    exact (hExists t ht).choose_spec x
  let U (t : ℝ) : C(Labels, Vec3) := by
    refine ⟨realVectorFourierCutoff ψ Λ (gV t), periodicRealPartVector.continuous.comp ?_⟩
    unfold smoothFourierCutoff finiteFourierSum
    exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const
  obtain ⟨u₀, p₀, hTr⟩ := hex
  have hu₀ (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) : u₀ t x = U t (toUnitTorus x) :=
    hTr.cutoff t ht (gV t) (hgV t ht) x
  obtain ⟨hs₀, hprop⟩ := hT1 u₀ p₀ hTr
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => U z.1 (toUnitTorus z.2))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hs₀.congr fun z hz => (hu₀ z.1 hz.1 z.2).symm
  have hBand : ∀ t ∈ Icc 0 T, RealTorusFourierBand (2 * Λ) (U t) := by
    intro t ht
    obtain ⟨-, -, c, hc, hband⟩ := hprop t ht
    have hceq : c = U t :=
      Bridge.torusField_eq_of_lift fun y => (hc y).trans (hu₀ t ht y)
    rw [← hceq]
    exact hband
  have hDiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (fun y => U t (toUnitTorus y)) x = 0 := by
    intro t ht x
    have : (fun y => U t (toUnitTorus y)) = u₀ t := funext fun y => (hu₀ t ht y).symm
    rw [this]
    exact (hprop t ht).2.1 x
  obtain ⟨p, hp, hP⟩ := exists_truncatedParentPoissonPressure hT U hs hBand hDiv
  exact ⟨{
    approximateTorus := gV
    torusVelocity := U
    pressure := p
    approximate_rep := hgV
    cutoff := fun _ _ => rfl
    smooth_velocity := hs
    odd_velocity := fun t ht => by
      have : (fun y => U t (toUnitTorus y)) = u₀ t := funext fun y => (hu₀ t ht y).symm
      rw [this]
      exact (hprop t ht).1
    divergence_free := hDiv
    velocity_band := hBand
    smooth_pressure := hp
    periodic_pressure := fun t ht => (hP t ht).1
    mean_zero_pressure := fun t ht => (hP t ht).2.1
    poisson := fun t ht => (hP t ht).2.2.1
    projected_eq := fun t ht => (hP t ht).2.2.2 }⟩

end

end TorusEuler.Paper.Lib.S678a
