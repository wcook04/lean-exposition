import TorusEuler.Paper.Proofs.S5Bridge.Norms
import TorusEuler.TruncatedChildStage

/-!
# S5 bridge: the truncation of §5.7

Glue between the truncation of the Section 5 statements (`S5.IsTruncation`: `u = S_Λ V`
on `[0,T]` and the zero-mean periodic pressure with `Δp = -tr((∇u)²)`) and the library
child stage `TruncatedChildStage T Λ ψ V R_V`.

* Every `TruncatedChildStage` gives an `S5.IsTruncation` with its velocity and pressure
  (`isTruncation_of_stage`).
* The velocity of any `S5.IsTruncation` is the velocity of any child stage of the same `V`
  on `[0,T]` (`IsTruncation.velocity_eq`).
* The pressures agree once the uniqueness of zero-mean periodic solutions of the Poisson
  equation is supplied (`IsTruncation.pressure_eq`; that uniqueness is the library lemma
  `periodicPoissonPressure_unique`, listed as content of Proposition 5.11, so it enters
  here as a hypothesis and only the proof of Proposition 5.11 can supply it). A proof
  citing 5.11, such as that of Theorem 7.1, needs no pressure identification: it applies
  the clause of `Statement.proposition_5_11` for every truncation to
  `isTruncation_of_stage s`.
* The library hypotheses on the symbol (`Function.Even ψ`) follow from `S5.CutoffSymbol`
  (`CutoffSymbol.even`, in `Norms`).
-/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler.Paper.Bridge

noncomputable section

variable {T Λ : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity}

/-- Two continuous torus fields with the same lift are equal. -/
theorem torusField_eq_of_lift {E : Type*} [TopologicalSpace E] {c c' : C(UnitAddTorus (Fin 3), E)}
    (h : ∀ x, c (toUnitTorus x) = c' (toUnitTorus x)) : c = c' :=
  ContinuousMap.ext fun z => by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    exact h x

/-- A library child stage is a truncation in the sense of §5.7, with its velocity and
pressure. -/
theorem isTruncation_of_stage (s : TruncatedChildStage T Λ ψ V RV) :
    S5.IsTruncation T ψ Λ V s.velocity s.pressure where
  cutoff := fun t ht c hc x => by
    have hceq : c = s.approximateTorus t :=
      torusField_eq_of_lift fun y => (hc y).trans (s.approximate_rep t ht y).symm
    rw [hceq]
    exact s.cutoff t (toUnitTorus x)
  pressure_smooth := fun t ht =>
    contDiffOn_univ.mp (s.smooth_pressure.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  pressure_periodic := s.periodic_pressure
  pressure_mean_zero := s.mean_zero_pressure
  poisson := s.poisson

/-- A child stage gives a truncation. -/
theorem exists_isTruncation_of_stage (s : TruncatedChildStage T Λ ψ V RV) :
    ∃ (u : Velocity) (p : Pressure), S5.IsTruncation T ψ Λ V u p :=
  ⟨s.velocity, s.pressure, isTruncation_of_stage s⟩

/-- The velocity of a truncation is the velocity of any child stage of the same field on
`[0,T]`. -/
theorem IsTruncation.velocity_eq {u : Velocity} {p : Pressure}
    (hu : S5.IsTruncation T ψ Λ V u p) (s : TruncatedChildStage T Λ ψ V RV) :
    ∀ t ∈ Icc 0 T, u t = s.velocity t := fun t ht => funext fun x =>
  (hu.cutoff t ht (s.approximateTorus t) (s.approximate_rep t ht) x).trans (s.cutoff t _).symm

/-- Two truncations of the same field have the same velocity on `[0,T]`, provided the
field has a continuous torus lift at each time (every child stage provides one). -/
theorem IsTruncation.velocity_unique {u u' : Velocity} {p p' : Pressure}
    (hu : S5.IsTruncation T ψ Λ V u p) (hu' : S5.IsTruncation T ψ Λ V u' p')
    (hlift : ∀ t ∈ Icc 0 T, ∃ c : C(UnitAddTorus (Fin 3), Vec3), ∀ x, c (toUnitTorus x) = V t x) :
    ∀ t ∈ Icc 0 T, u t = u' t := fun t ht => by
  obtain ⟨c, hc⟩ := hlift t ht
  exact funext fun x => (hu.cutoff t ht c hc x).trans (hu'.cutoff t ht c hc x).symm

/-- The pressures of two truncations with the same velocity agree on `[0,T]`, given the
uniqueness of zero-mean periodic solutions of the Poisson equation (`huniq`; it is content
of Proposition 5.11, so only the proof of 5.11 can supply it). -/
theorem IsTruncation.pressure_eq {u u' : Velocity} {p p' : Pressure}
    (hu : S5.IsTruncation T ψ Λ V u p) (hu' : S5.IsTruncation T ψ Λ V u' p')
    (hvel : ∀ t ∈ Icc 0 T, u t = u' t)
    (huniq : ∀ q q' : Vec3 → ℝ, ContDiff ℝ ∞ q → ContDiff ℝ ∞ q' → SpatiallyPeriodic q →
      SpatiallyPeriodic q' → (∫ x in centeredCell, q x) = 0 → (∫ x in centeredCell, q' x) = 0 →
      (∀ x, divergence (gradient q) x = divergence (gradient q') x) → q = q') :
    ∀ t ∈ Icc 0 T, p t = p' t := fun t ht =>
  huniq _ _ (hu.pressure_smooth t ht) (hu'.pressure_smooth t ht) (hu.pressure_periodic t ht)
    (hu'.pressure_periodic t ht) (hu.pressure_mean_zero t ht) (hu'.pressure_mean_zero t ht)
    fun x => by rw [hu.poisson t ht x, hu'.poisson t ht x, hvel t ht]

/-- The truncation of a field and a child stage of the same field have the same pressure on
`[0,T]`, given the uniqueness of zero-mean periodic Poisson solutions (`huniq`, which only
the proof of Proposition 5.11 can supply). -/
theorem IsTruncation.pressure_eq_stage {u : Velocity} {p : Pressure}
    (hu : S5.IsTruncation T ψ Λ V u p) (s : TruncatedChildStage T Λ ψ V RV)
    (huniq : ∀ q q' : Vec3 → ℝ, ContDiff ℝ ∞ q → ContDiff ℝ ∞ q' → SpatiallyPeriodic q →
      SpatiallyPeriodic q' → (∫ x in centeredCell, q x) = 0 → (∫ x in centeredCell, q' x) = 0 →
      (∀ x, divergence (gradient q) x = divergence (gradient q') x) → q = q') :
    ∀ t ∈ Icc 0 T, p t = s.pressure t :=
  IsTruncation.pressure_eq hu (isTruncation_of_stage s) (IsTruncation.velocity_eq hu s) huniq

end

end TorusEuler.Paper.Bridge
