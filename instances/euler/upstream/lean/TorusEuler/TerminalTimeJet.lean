import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TorusEuler.TruncatedParentProjectedMomentum

/-! Fixed-spatial-point time derivatives on a closed Euler time slab. -/

open Set
open scoped ContDiff

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Eulerian time jet evaluates the within-time derivative at a fixed spatial point. -/
noncomputable abbrev slabTimeJet (a b : ℝ) (q : ℕ) (f : ℝ → Vec3 → E) (t : ℝ) (x : Vec3) :=
  iteratedDerivWithin q (fun r => f r x) (Icc a b) t

@[simp] theorem slabTimeJet_zero (a b : ℝ) (f : ℝ → Vec3 → E) :
    slabTimeJet a b 0 f = f := by
  funext t x
  change iteratedDerivWithin 0 (fun r => f r x) (Icc a b) t = f t x
  simp only [iteratedDerivWithin_zero]

theorem slabTimeJet_succ (a b : ℝ) (q : ℕ) (f : ℝ → Vec3 → E) (t : ℝ) (x : Vec3) :
    slabTimeJet a b (q + 1) f t x =
      derivWithin (fun r => slabTimeJet a b q f r x) (Icc a b) t := by
  rw [slabTimeJet, iteratedDerivWithin_succ]

theorem slabTimeJet_succ' (a b : ℝ) (q : ℕ) (f : ℝ → Vec3 → E) :
    slabTimeJet a b (q + 1) f =
      slabTimeJet a b q (fun t x => derivWithin (fun r => f r x) (Icc a b) t) := by
  funext t x
  exact congrFun (iteratedDerivWithin_succ' (n := q) (f := fun r => f r x) (s := Icc a b)) t

theorem slabTimeJet_smooth {a b : ℝ} {f : ℝ → Vec3 → E} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3))) (q : ℕ) :
    ContDiffOn ℝ ∞ (Function.uncurry (slabTimeJet a b q f)) (Icc a b ×ˢ (univ : Set Vec3)) := by
  induction q with
  | zero => simpa only [slabTimeJet_zero] using hf
  | succ q ih =>
    have h : slabTimeJet a b (q + 1) f =
      (fun t x => derivWithin (fun r => slabTimeJet a b q f r x) (Icc a b) t) :=
      funext fun t => funext fun x => slabTimeJet_succ a b q f t x
    rw [h]
    exact contDiffOn_sliceTimeDerivWithin_Icc hab ih

theorem slabTimeJet_slice_smooth {a b : ℝ} {f : ℝ → Vec3 → E} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (slabTimeJet a b q f t) := by
  have h := slabTimeJet_smooth hab hf q
  exact contDiffOn_univ.mp
    (h.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨ht, mem_univ x⟩))

theorem hasDerivWithinAt_slabTimeJet {a b : ℝ} {f : ℝ → Vec3 → E} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc a b) (x : Vec3) :
    HasDerivWithinAt (fun r => slabTimeJet a b q f r x)
      (slabTimeJet a b (q + 1) f t x) (Icc a b) t := by
  rw [slabTimeJet_succ]
  have h := (slabTimeJet_smooth hab hf q).comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (fun r hr => ⟨hr, mem_univ x⟩)
  exact (h.differentiableOn (by simp) t ht).hasDerivWithinAt

theorem slabTimeJet_periodic {a b : ℝ} {f : ℝ → Vec3 → E}
    (hf : ∀ t ∈ Icc a b, SpatiallyPeriodic (f t)) (q : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    SpatiallyPeriodic (slabTimeJet a b q f t) := by
  induction q generalizing t with
  | zero => simpa only [slabTimeJet_zero] using hf t ht
  | succ q ih =>
    intro k x
    simp_rw [slabTimeJet_succ]
    exact derivWithin_congr (fun r hr => ih hr k x) (ih ht k x)

/-- A time jet on a smaller nondegenerate slab agrees with the parent jet, including its endpoints. -/
theorem slabTimeJet_eq_of_subset {a b c d : ℝ} {f : ℝ → Vec3 → E}
    (hcd : c < d) (hsub : Icc c d ⊆ Icc a b)
    (hab : a < b) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc c d) (x : Vec3) :
    slabTimeJet c d q f t x = slabTimeJet a b q f t x := by
  induction q generalizing t with
  | zero => simp
  | succ q ih =>
    rw [slabTimeJet_succ c d]
    refine (derivWithin_congr (fun r hr => ih hr) (ih ht)).trans ?_
    exact ((hasDerivWithinAt_slabTimeJet hab hf q (hsub ht) x).mono hsub).derivWithin
      (uniqueDiffOn_Icc hcd t ht)

end TorusEuler
