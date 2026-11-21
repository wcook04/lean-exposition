import TorusEuler.EndpointPhysicalJetData
import TorusEuler.TerminalTimeJet
import TorusEuler.TruncatedChildStage
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The fixed Fourier cutoff and periodic Leray projection on all closed-slab time jets. -/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

/-- Every time jet of a jointly smooth periodic field has a continuous torus representative. -/
theorem exists_continuousTorusTimeJets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (hT : 0 < T) {V : ℝ → Vec3 → E}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t)) :
    ∃ g : ℕ → ℝ → C(Labels, E), ∀ j t, t ∈ Icc 0 T → ∀ x,
      g j t (toUnitTorus x) = slabTimeJet 0 T j V t x := by
  classical
  have h (j : ℕ) (t : ℝ) : ∃ g : C(Labels, E), t ∈ Icc 0 T →
      ∀ x, g (toUnitTorus x) = slabTimeJet 0 T j V t x := by
    by_cases ht : t ∈ Icc 0 T
    · obtain ⟨g, hg⟩ := (slabTimeJet_periodic hper j ht).exists_continuousTorusFunction
        (slabTimeJet_slice_smooth hT hV j ht).continuous
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun ht' => (ht ht').elim⟩
  choose g hg using h
  exact ⟨g, hg⟩

/-- At all time orders the cutoff commutes with the actual within-slab Eulerian jet. -/
theorem slabTimeJet_realVectorFourierCutoff {T Λ : ℝ} (hT : 0 < T) {V : Velocity}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (g : ℕ → ℝ → C(Labels, Vec3))
    (hg : ∀ j t, t ∈ Icc 0 T → ∀ x, g j t (toUnitTorus x) = slabTimeJet 0 T j V t x)
    (ψ : Vec3 → ℝ) (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    slabTimeJet 0 T j (fun r y => realVectorFourierCutoff ψ Λ (g 0 r) (toUnitTorus y)) t x =
      realVectorFourierCutoff ψ Λ (g j t) (toUnitTorus x) := by
  induction j generalizing t with
  | zero => rw [slabTimeJet_zero]
  | succ j ih =>
    rw [slabTimeJet_succ]
    have hd := hasDerivWithinAt_realVectorFourierCutoff_time hT (slabTimeJet_smooth hT hV j)
      (g j) (g (j + 1)) (hg j) (fun r hr y => by rw [hg (j + 1) r hr, slabTimeJet_succ]) ψ Λ ht x
    exact (hd.congr_of_mem (fun r hr => ih hr) ht).derivWithin (uniqueDiffOn_Icc hT t ht)

/-- The actual cutoff child uses the Fourier cutoff of each Eulerian time jet. -/
theorem TruncatedChildStage.slabTimeJet_velocity {T Λ : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity}
    (s : TruncatedChildStage T Λ ψ V RV) (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (g : ℕ → ℝ → C(Labels, Vec3))
    (hg : ∀ j t, t ∈ Icc 0 T → ∀ x, g j t (toUnitTorus x) = slabTimeJet 0 T j V t x)
    (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    slabTimeJet 0 T j s.velocity t x = realVectorFourierCutoff ψ Λ (g j t) (toUnitTorus x) := by
  refine (iteratedDerivWithin_congr (g := fun r => realVectorFourierCutoff ψ Λ (g 0 r) (toUnitTorus x))
    ?_ ht).trans (slabTimeJet_realVectorFourierCutoff hT hV g hg ψ j ht x)
  intro r hr
  have hrep : s.approximateTorus r = g 0 r := by
    ext z
    obtain ⟨y, rfl⟩ := toUnitTorus_surjective z
    rw [s.approximate_rep r hr y, hg 0 r hr y, slabTimeJet_zero]
  change s.velocity r x = realVectorFourierCutoff ψ Λ (g 0 r) (toUnitTorus x)
  rw [s.velocity_eq_cutoff r, hrep]

/-- Time differentiation commutes with the actual Leray operator, via the
smooth time curves in the torus half-Hölder space. -/
theorem slabTimeJet_periodicLerayHolderLift {T : ℝ} (hT : 0 < T) {V : Velocity}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    slabTimeJet 0 T j (fun r => periodicLerayHolderLift (V r)) t x =
      periodicLerayHolderLift (slabTimeJet 0 T j V t) x := by
  obtain ⟨U, hU, hEval, _⟩ := exists_halfHolder_timeCurves_of_periodic_jets hT
    (fun j => slabTimeJet 0 T j V) (slabTimeJet_smooth hT hV) (slabTimeJet_periodic hper)
    (fun j _ ht x => hasDerivWithinAt_slabTimeJet hT hV j ht x)
  let L := (HalfHolder.eval (E := Vec3) (toUnitTorus x)).comp endpointStrongSpatialLeray
  have hP (j : ℕ) (r : ℝ) (hr : r ∈ Icc 0 T) :
      periodicLerayHolderLift (slabTimeJet 0 T j V r) x = L (U j r) := by
    have hE := funext (hEval j r hr)
    rw [← hE, periodicLerayHolderLift_pullback]
    rfl
  have hD (j : ℕ) (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivWithinAt (U j)
      (U (j + 1) r) (Icc 0 T) r := by
    apply hasDerivWithinAt_halfHolder_of_eval_hasDerivWithinAt (hU j).continuousOn
      (hU (j + 1)).continuousOn _ hr
    intro z r' hr'
    obtain ⟨y, rfl⟩ := toUnitTorus_surjective z
    rw [hEval (j + 1) r' hr' y]
    exact (hasDerivWithinAt_slabTimeJet hT hV j hr' y).congr_of_mem (fun s hs => hEval j s hs y) hr'
  induction j generalizing t with
  | zero => rw [slabTimeJet_zero, slabTimeJet_zero]
  | succ j ih =>
    rw [slabTimeJet_succ, hP (j + 1) t ht]
    have hd := L.hasFDerivAt.comp_hasDerivWithinAt t (hD j t ht)
    exact (hd.congr_of_mem (fun r hr => (ih hr).trans (hP j r hr)) ht).derivWithin
      (uniqueDiffOn_Icc hT t ht)

end

end TorusEuler
