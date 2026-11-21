import TorusEuler.TerminalTimeJet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Time and spatial differentiation on a nondegenerate closed slab. -/

open Filter Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → Vec3 → E}

local notation "I" => Icc a b
local notation "J" => Set.prod (Icc a b) (univ : Set Vec3)

private theorem hasFDerivAt_slabSpaceSlice
    {g : ℝ × Vec3 → E} (hg : DifferentiableOn ℝ g J)
    {t : ℝ} (ht : t ∈ I) (x : Vec3) :
    HasFDerivAt (fun y => g (t, y))
      ((fderivWithin ℝ g J (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Vec3)) x :=
  (hg (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt.comp_hasFDerivAt x
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
    (Eventually.of_forall fun y => ⟨ht, mem_univ y⟩)

private theorem hasDerivWithinAt_slabTimeSlice
    {g : ℝ × Vec3 → E} (hg : DifferentiableOn ℝ g J)
    {t : ℝ} (ht : t ∈ I) (x : Vec3) :
    HasDerivWithinAt (fun r => g (r, x))
      (fderivWithin ℝ g J (t, x) (1, 0)) I t := by
  have h := (hg (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt.comp t
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).hasFDerivWithinAt
    (fun r hr => show (r, x) ∈ J from ⟨hr, mem_univ x⟩)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply] using h.hasDerivWithinAt

/-- Every spatial slice of a jointly smooth field is smooth. -/
theorem terminal_contDiff_spaceSlice
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.1 (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    fun x _ => ⟨ht, mem_univ x⟩)

/-- Every time slice of a jointly smooth field is smooth within the slab. -/
theorem terminal_contDiffOn_timeSlice
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J) (x : Vec3) :
    ContDiffOn ℝ ∞ (fun t => f t x) I :=
  hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _t ht => ⟨ht, mem_univ x⟩

/-- Spatial differentiation preserves joint smoothness. -/
theorem terminal_contDiffOn_spaceDerivative (hab : a < b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (f z.1) z.2) J := by
  let D := fderivWithin ℝ (Function.uncurry f) J
  let L := (ContinuousLinearMap.compL ℝ Vec3 (ℝ × Vec3) E).flip
    (ContinuousLinearMap.inr ℝ ℝ Vec3)
  have hD : ContDiffOn ℝ ∞ D J := hf.fderivWithin
    ((uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ) (by simp)
  apply (L.contDiff.comp_contDiffOn hD).congr
  rintro ⟨t, x⟩ ⟨ht, _⟩
  exact (hasFDerivAt_slabSpaceSlice (hf.differentiableOn (by simp)) ht x).fderiv

/-- A partial time derivative commutes with the spatial Fréchet derivative
at every point of the slab, including both endpoints. -/
theorem terminal_derivWithin_fderiv_comm (hab : a < b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J)
    {t : ℝ} (ht : t ∈ I) (x : Vec3) :
    derivWithin (fun r => fderiv ℝ (f r) x) I t =
      fderiv ℝ (fun y => derivWithin (fun r => f r y) I t) x := by
  let D := fderivWithin ℝ (Function.uncurry f) J
  let L := (ContinuousLinearMap.compL ℝ Vec3 (ℝ × Vec3) E).flip
    (ContinuousLinearMap.inr ℝ ℝ Vec3)
  let v : ℝ × Vec3 := (1, 0)
  let B := ContinuousLinearMap.apply ℝ E v
  have hI := uniqueDiffOn_Icc hab
  have hJ := hI.prod (uniqueDiffOn_univ (𝕜 := ℝ) (E := Vec3))
  have htJ : (t,x) ∈ J := ⟨ht, mem_univ x⟩
  have hD : ContDiffOn ℝ ∞ D J := hf.fderivWithin hJ (by simp)
  have hDf := hf.differentiableOn (by simp)
  have hDD := hD.differentiableOn (by simp)
  have hleft (r : ℝ) (hr : r ∈ I) :
      fderiv ℝ (f r) x = L (D (r,x)) :=
    (hasFDerivAt_slabSpaceSlice hDf hr x).fderiv
  have hright (y : Vec3) :
      derivWithin (fun r => f r y) I t = B (D (t,y)) :=
    (hasDerivWithinAt_slabTimeSlice hDf ht y).derivWithin (hI t ht)
  have htD := L.hasFDerivAt.comp_hasDerivWithinAt t
    (hasDerivWithinAt_slabTimeSlice hDD ht x)
  have hxD := B.hasFDerivAt.comp x (hasFDerivAt_slabSpaceSlice hDD ht x)
  rw [(htD.congr_of_mem hleft ht).derivWithin (hI t ht),
    (hxD.congr_of_eventuallyEq (Eventually.of_forall hright)).fderiv]
  have hcl : (t,x) ∈ closure (interior J) := by
    change (t, x) ∈ closure (interior (I ×ˢ (univ : Set Vec3)))
    rw [interior_prod_eq, interior_univ, closure_prod_eq, closure_univ,
      closure_interior_Icc hab.ne]
    exact htJ
  have hsym := (hf (t,x) htJ).isSymmSndFDerivWithinAt
    (show minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) from by simp)
    hJ hcl htJ
  ext y
  exact hsym v (0, y)

/-- A spatial derivative commutes with every time jet on the slab. -/
theorem terminal_iteratedDerivWithin_fderiv_comm (hab : a < b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J) (q : ℕ)
    {t : ℝ} (ht : t ∈ I) (x : Vec3) :
    slabTimeJet a b q (fun r y => fderiv ℝ (f r) y) t x =
      fderiv ℝ (slabTimeJet a b q f t) x := by
  induction q generalizing t with
  | zero =>
    rw [show slabTimeJet a b 0 (fun r y => fderiv ℝ (f r) y) = _
      from slabTimeJet_zero _ _ _]
    rw [slabTimeJet_zero]
  | succ q ih =>
    simp only [slabTimeJet_succ]
    refine (derivWithin_congr (fun r hr => ih hr) (ih ht)).trans ?_
    rw [show slabTimeJet a b (q + 1) f t =
      (fun y => derivWithin (fun r => slabTimeJet a b q f r y) I t) from
        funext (slabTimeJet_succ a b q f t)]
    exact terminal_derivWithin_fderiv_comm hab
      (f := slabTimeJet a b q f)
      (slabTimeJet_smooth hab hf q) ht x

end

end TorusEuler
