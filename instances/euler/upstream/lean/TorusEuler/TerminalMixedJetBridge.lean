import TorusEuler.EulerJointRegularity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Bounds on mixed partial derivatives control the joint jets on a closed slab. -/

open Set Filter ContinuousLinearMap
open scoped ContDiff

namespace TorusEuler

noncomputable section

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set E)

private theorem uniqueDiffOn_terminalSlab {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ (Slab(T)) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

private abbrev timeEval : ((ℝ × E) →L[ℝ] F) →L[ℝ] F :=
  ContinuousLinearMap.apply ℝ F (1, 0)

private abbrev spatialRestrict : ((ℝ × E) →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  (ContinuousLinearMap.inr ℝ ℝ E).precomp F

private abbrev timePartial (T : ℝ) (f : (ℝ × E) → F) (p : ℝ × E) : F :=
  timeEval (fderivWithin ℝ f (Slab(T)) p)

private abbrev spatialPartial (T : ℝ) (f : (ℝ × E) → F) (p : ℝ × E) : E →L[ℝ] F :=
  spatialRestrict (fderivWithin ℝ f (Slab(T)) p)

private theorem timePartial_smooth {T : ℝ} (hT : 0 < T)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Slab(T))) :
    ContDiffOn ℝ ∞ (timePartial T f) (Slab(T)) :=
  timeEval.contDiff.comp_contDiffOn (hf.fderivWithin (uniqueDiffOn_terminalSlab hT) (by simp))

private theorem timePartial_iterate_smooth {T : ℝ} (hT : 0 < T)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Slab(T))) (q : ℕ) :
    ContDiffOn ℝ ∞ ((timePartial T)^[q] f) (Slab(T)) := by
  induction q with
  | zero => exact hf
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact timePartial_smooth hT ih

private theorem spatialPartial_smooth {T : ℝ} (hT : 0 < T)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Slab(T))) :
    ContDiffOn ℝ ∞ (spatialPartial T f) (Slab(T)) :=
  spatialRestrict.contDiff.comp_contDiffOn (hf.fderivWithin (uniqueDiffOn_terminalSlab hT) (by simp))

private theorem derivWithin_terminalTimeSlice {T : ℝ} (hT : 0 < T)
    {f : (ℝ × E) → F} {t : ℝ} (ht : t ∈ Icc 0 T) (x : E)
    (hf : HasFDerivWithinAt f (fderivWithin ℝ f (Slab(T)) (t, x)) (Slab(T)) (t, x)) :
    derivWithin (fun r => f (r, x)) (Icc 0 T) t = timePartial T f (t, x) := by
  let L := ContinuousLinearMap.inl ℝ ℝ E
  have hcurve : HasDerivWithinAt (fun r : ℝ => (r, x)) ((1, 0) : ℝ × E) (Icc 0 T) t := by
    have hc := (L.hasFDerivAt (x := t)).add_const ((0, x) : ℝ × E)
    simpa only [L, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] using
      hc.hasFDerivWithinAt.hasDerivWithinAt (s := Icc 0 T)
  have hmap : MapsTo (fun r : ℝ => (r, x)) (Icc 0 T) (Slab(T)) :=
    fun _ hr => ⟨hr, mem_univ x⟩
  exact (hf.comp_hasDerivWithinAt t hcurve hmap).derivWithin (uniqueDiffOn_Icc hT t ht)

private theorem fderiv_terminalSpaceSlice {T : ℝ}
    {f : (ℝ × E) → F} {t : ℝ} (ht : t ∈ Icc 0 T) (x : E)
    (hf : HasFDerivWithinAt f (fderivWithin ℝ f (Slab(T)) (t, x)) (Slab(T)) (t, x)) :
    fderiv ℝ (fun y => f (t, y)) x = spatialPartial T f (t, x) := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  have hcurve : HasFDerivAt (fun y : E => (t, y)) L x := by
    have hc := (L.hasFDerivAt (x := x)).add_const ((t, 0) : ℝ × E)
    simpa only [L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using hc
  exact (hf.comp_hasFDerivAt x hcurve (Filter.Eventually.of_forall
    (fun y => ⟨ht, mem_univ y⟩))).fderiv

private theorem spatialPartial_timePartial_commute {T : ℝ} (hT : 0 < T)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Slab(T)))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    timePartial T (spatialPartial T f) (t, x) =
      spatialPartial T (timePartial T f) (t, x) := by
  have hu : UniqueDiffOn ℝ (Slab(T)) := uniqueDiffOn_terminalSlab hT
  have hp : (t, x) ∈ Slab(T) := ⟨ht, mem_univ x⟩
  have hcl : (t, x) ∈ closure (interior (Slab(T))) := by
    change (t, x) ∈ closure (interior (Icc (0 : ℝ) T ×ˢ (univ : Set E)))
    rw [interior_prod_eq, interior_Icc, interior_univ, closure_prod_eq,
      closure_Ioo hT.ne, closure_univ]
    exact hp
  have hs := (hf (t, x) hp).isSymmSndFDerivWithinAt (by simp) hu hcl hp
  have hdf := ((hf.fderivWithin hu (m := ∞) (by simp)).differentiableOn (by simp) (t, x) hp)
    |>.hasFDerivWithinAt
  have hsp := (spatialRestrict (E := E) (F := F)).hasFDerivAt.comp_hasFDerivWithinAt (t, x) hdf
  have htm := (timeEval (E := E) (F := F)).hasFDerivAt.comp_hasFDerivWithinAt (t, x) hdf
  ext v
  change (fderivWithin ℝ (spatialRestrict ∘ fderivWithin ℝ f (Slab(T))) (Slab(T))
    (t, x) (1, 0)) v = fderivWithin ℝ (timeEval ∘ fderivWithin ℝ f (Slab(T))) (Slab(T))
      (t, x) (0, v)
  rw [hsp.fderivWithin (hu _ hp), htm.fderivWithin (hu _ hp)]
  exact hs (1, 0) (0, v)

private def timeJet {T : ℝ} (q : ℕ) (f : (ℝ × E) → F) (p : ℝ × E) : F :=
  iteratedDerivWithin q (fun r => f (r, p.2)) (Icc 0 T) p.1

private theorem timeJet_eq_partialIterate {T : ℝ} (hT : 0 < T)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Slab(T))) (q : ℕ) :
    EqOn (timeJet (T := T) q f) ((timePartial T)^[q] f) (Slab(T)) := by
  have hu : UniqueDiffOn ℝ (Slab(T)) := uniqueDiffOn_terminalSlab hT
  have hsm := timePartial_iterate_smooth hT hf
  induction q with
  | zero => intro p hp; rfl
  | succ q ih =>
    intro p hp
    rcases p with ⟨t,x⟩
    have ht : t ∈ Icc 0 T := hp.1
    have heq : EqOn (iteratedDerivWithin q (fun r => f (r,x)) (Icc 0 T))
        (fun r => ((timePartial T)^[q] f) (r,x)) (Icc 0 T) :=
      fun r hr => ih (show (r,x) ∈ Slab(T) from ⟨hr, mem_univ x⟩)
    rw [Function.iterate_succ_apply']
    change iteratedDerivWithin (q + 1) (fun r => f (r,x)) (Icc 0 T) t =
      timePartial T ((timePartial T)^[q] f) (t,x)
    rw [iteratedDerivWithin_succ, derivWithin_congr heq (heq ht)]
    exact derivWithin_terminalTimeSlice hT ht x
      (((hsm q).differentiableOn (by simp) (t,x) hp).hasFDerivWithinAt)

private theorem timePartial_eqOn_congr {T : ℝ}
    {f g : (ℝ × E) → F} (h : EqOn f g (Slab(T))) :
    EqOn (timePartial T f) (timePartial T g) (Slab(T)) := by
  intro p hp
  change timeEval (fderivWithin ℝ f (Slab(T)) p) =
    timeEval (fderivWithin ℝ g (Slab(T)) p)
  rw [fderivWithin_congr h (h hp)]

private theorem timeJet_spatialPartial {T : ℝ} (hT : 0 < T)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Slab(T)))
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun y => timeJet (T := T) q (spatialPartial T f) (t,y)) =
      fderiv ℝ (fun y => timeJet (T := T) q f (t,y)) := by
  have hu : UniqueDiffOn ℝ (Slab(T)) := uniqueDiffOn_terminalSlab hT
  have hsm := timePartial_iterate_smooth hT hf
  have hcomm : ∀ j : ℕ, EqOn ((timePartial T)^[j] (spatialPartial T f))
      (spatialPartial T ((timePartial T)^[j] f)) (Slab(T)) := by
    intro j
    induction j with
    | zero => intro p hp; rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine (timePartial_eqOn_congr ih).trans ?_
      rintro ⟨r,y⟩ hr
      exact spatialPartial_timePartial_commute hT (hsm j) hr.1 y
  have heq : (fun y => timeJet (T := T) q f (t,y)) =
      fun y => ((timePartial T)^[q] f) (t,y) := by
    funext y
    exact timeJet_eq_partialIterate hT hf q ⟨ht, mem_univ y⟩
  rw [heq]
  funext y
  have hp : (t,y) ∈ Slab(T) := ⟨ht, mem_univ y⟩
  exact (timeJet_eq_partialIterate hT (spatialPartial_smooth hT hf) q hp).trans
    ((hcomm q hp).trans (fderiv_terminalSpaceSlice ht y
      (((hsm q).differentiableOn (by simp) (t,y) hp).hasFDerivWithinAt)).symm)

private theorem timeJet_timePartial {T : ℝ} (hT : 0 < T)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Slab(T)))
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun y => timeJet (T := T) q (timePartial T f) (t,y)) =
      fun y => timeJet (T := T) (q + 1) f (t,y) := by
  funext y
  have hp : (t,y) ∈ Slab(T) := ⟨ht, mem_univ y⟩
  rw [timeJet_eq_partialIterate hT (timePartial_smooth hT hf) q hp,
    timeJet_eq_partialIterate hT hf (q + 1) hp, Function.iterate_succ_apply]

private theorem norm_iteratedFDerivWithin_succ_le_partial {T : ℝ} (hT : 0 < T)
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Slab(T))) (n : ℕ)
    {p : ℝ × E} (hp : p ∈ Slab(T)) :
    ‖iteratedFDerivWithin ℝ (n + 1) f (Slab(T)) p‖ ≤
      ‖iteratedFDerivWithin ℝ n (timePartial T f) (Slab(T)) p‖ +
        ‖iteratedFDerivWithin ℝ n (spatialPartial T f) (Slab(T)) p‖ := by
  let J := iteratedFDerivWithin ℝ n (fderivWithin ℝ f (Slab(T))) (Slab(T)) p
  let Jt := iteratedFDerivWithin ℝ n (timePartial T f) (Slab(T)) p
  let Jx := iteratedFDerivWithin ℝ n (spatialPartial T f) (Slab(T)) p
  have hu : UniqueDiffOn ℝ (Slab(T)) := uniqueDiffOn_terminalSlab hT
  have hdf := (hf.fderivWithin hu (m := ∞) (by simp)) p hp
  have hJt : Jt = timeEval.compContinuousMultilinearMap J :=
    timeEval.iteratedFDerivWithin_comp_left hdf hu hp (by simp)
  have hJx : Jx = spatialRestrict.compContinuousMultilinearMap J :=
    spatialRestrict.iteratedFDerivWithin_comp_left hdf hu hp (by simp)
  rw [← norm_iteratedFDerivWithin_fderivWithin hu hp]
  change ‖J‖ ≤ ‖Jt‖ + ‖Jx‖
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun v => ?_)
  have hvprod : 0 ≤ ∏ i, ‖v i‖ := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) hvprod) (fun w => ?_)
  have hv : J v w = w.1 • Jt v + Jx v w.2 := by
    have hw : w.1 • ((1, 0) : ℝ × E) + (0, w.2) = w := by
      ext <;> simp
    conv_lhs => rw [← hw]
    rw [map_add, map_smul, hJt, hJx]
    rfl
  rw [hv]
  calc
    _ ≤ ‖w.1‖ * ‖Jt v‖ + ‖Jx v‖ * ‖w.2‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      exact add_le_add le_rfl ((Jx v).le_opNorm w.2)
    _ ≤ ‖w‖ * (‖Jt‖ * ∏ i, ‖v i‖) + (‖Jx‖ * ∏ i, ‖v i‖) * ‖w‖ :=
      add_le_add (mul_le_mul (norm_fst_le w) (Jt.le_opNorm v) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (Jx.le_opNorm v) (norm_snd_le w) (norm_nonneg _) (by positivity))
    _ = _ := by ring

private theorem norm_iteratedFDerivWithin_le_mixedTerm {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
      {f : (ℝ × E) → G} (_hf : ContDiffOn ℝ ∞ f (Slab(T))) {C : ℝ} (_hC : 0 ≤ C)
      {t : ℝ} (_ht : t ∈ Icc 0 T) (x : E),
      (∀ q m : ℕ, q + m = n →
        ‖iteratedFDeriv ℝ m (fun y => timeJet (T := T) q f (t,y)) x‖ ≤ C) →
      ‖iteratedFDerivWithin ℝ n f (Slab(T)) (t,x)‖ ≤ (2 : ℝ)^n * C := by
  induction n with
  | zero =>
    intro G _ _ f hf C hC t ht x hm
    simpa only [norm_iteratedFDerivWithin_zero, pow_zero, one_mul, norm_iteratedFDeriv_zero,
      timeJet, iteratedDerivWithin_zero] using hm 0 0 rfl
  | succ n ih =>
    intro G _ _ f hf C hC t ht x hm
    have htime := ih (timePartial_smooth hT hf) hC ht x (fun q m hqm => by
      rw [timeJet_timePartial hT hf q ht]
      exact hm (q + 1) m (by omega))
    have hspace := ih (spatialPartial_smooth hT hf) hC ht x (fun q m hqm => by
      rw [timeJet_spatialPartial hT hf q ht, norm_iteratedFDeriv_fderiv]
      exact hm q (m + 1) (by omega))
    calc
      _ ≤ ‖iteratedFDerivWithin ℝ n (timePartial T f) (Slab(T)) (t,x)‖ +
          ‖iteratedFDerivWithin ℝ n (spatialPartial T f) (Slab(T)) (t,x)‖ :=
        norm_iteratedFDerivWithin_succ_le_partial hT hf n ⟨ht, mem_univ x⟩
      _ ≤ (2 : ℝ)^n * C + (2 : ℝ)^n * C := add_le_add htime hspace
      _ = (2 : ℝ)^(n + 1) * C := by rw [pow_succ]; ring

/-- At every point of the closed slab, the norm of the joint derivative of order
`n` is bounded by `2^n` times a bound for all mixed partials of total order `n`. -/
theorem norm_iteratedFDerivWithin_uncurry_le_of_mixed {T : ℝ} (hT : 0 < T)
    (g : ℝ → E → F) (hSmooth : ContDiffOn ℝ ∞ (Function.uncurry g) (Slab(T)))
    {n : ℕ} {C : ℝ} (hC : 0 ≤ C) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E)
    (hMixed : ∀ q m : ℕ, q + m = n →
      ‖iteratedFDeriv ℝ m (fun y => iteratedDerivWithin q (fun r => g r y) (Icc 0 T) t) x‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (Function.uncurry g) (Slab(T)) (t, x)‖ ≤ (2 : ℝ)^n * C :=
  norm_iteratedFDerivWithin_le_mixedTerm hT n hSmooth hC ht x hMixed

end

end TorusEuler
