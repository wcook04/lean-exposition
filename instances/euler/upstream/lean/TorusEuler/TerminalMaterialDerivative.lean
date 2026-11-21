import TorusEuler.TerminalMixedDerivatives
import TorusEuler.LocalizedSeedRegularity

/-! Material time differentiation and its exact readout in the label flow. -/

open Filter Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The material derivative on a closed slab, with spatial points held fixed in
the partial time derivative. -/
def terminalMaterialStep (a b : ℝ) (U : Velocity) (f : ℝ → Vec3 → E) : ℝ → Vec3 → E :=
  fun t x => derivWithin (fun s => f s x) (Icc a b) t + fderiv ℝ (f t) x (U t x)

/-- Repeated material derivatives on a closed time slab. -/
def terminalMaterialIterate (a b : ℝ) (U : Velocity) (q : ℕ) (f : ℝ → Vec3 → E) :
    ℝ → Vec3 → E :=
  (terminalMaterialStep a b U)^[q] f

@[simp] theorem terminalMaterialIterate_zero (a b : ℝ) (U : Velocity) (f : ℝ → Vec3 → E) :
    terminalMaterialIterate a b U 0 f = f := rfl

@[simp] theorem terminalMaterialIterate_succ (a b : ℝ) (U : Velocity) (q : ℕ)
    (f : ℝ → Vec3 → E) :
    terminalMaterialIterate a b U (q + 1) f =
      terminalMaterialStep a b U (terminalMaterialIterate a b U q f) :=
  Function.iterate_succ_apply' _ q f

variable {a b : ℝ} {f : ℝ → Vec3 → E} {U : Velocity} {X : ℝ → Velocity}

local notation "I" => Icc a b
local notation "J" => Set.prod (Icc a b) (univ : Set Vec3)

/-- Material differentiation preserves joint smoothness in the time and space
coordinates on the closed slab. -/
theorem terminal_contDiffOn_materialStep (hab : a < b)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J) :
    ContDiffOn ℝ ∞ (Function.uncurry (terminalMaterialStep a b U f)) J :=
  (contDiffOn_sliceTimeDerivWithin_Icc hab hf).add
    ((terminal_contDiffOn_spaceDerivative hab hf).clm_apply hU)

/-- Iterated material derivatives of the smooth field are jointly smooth. -/
theorem terminal_contDiffOn_materialIterate (hab : a < b)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J) (q : ℕ) :
    ContDiffOn ℝ ∞ (Function.uncurry (terminalMaterialIterate a b U q f)) J := by
  induction q with
  | zero => simpa only [terminalMaterialIterate_zero] using hf
  | succ q ih =>
    simpa only [terminalMaterialIterate_succ] using terminal_contDiffOn_materialStep hab hU ih

/-- A trajectory converts the material derivative to a within-slab ordinary
derivative, including at the two temporal endpoints. -/
theorem IsLabelFlowOn.terminal_hasDerivWithinAt_pullback (hX : IsLabelFlowOn U X I)
    (hab : a < b) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (x : Vec3) :
    HasDerivWithinAt (fun r => f r (X s r x))
      (terminalMaterialStep a b U f t (X s t x)) I t := by
  let y := X s t x
  let D := fderivWithin ℝ (Function.uncurry f) J (t,y)
  have hDiff := (hf.differentiableOn (by simp) (t,y) ⟨ht, mem_univ y⟩).hasFDerivWithinAt
  have hPath := hDiff.comp_hasDerivWithinAt t
    ((hasDerivWithinAt_id t I).prodMk (hX.trajectory s hs x t ht))
    (fun r hr => (show (r, X s r x) ∈ J from ⟨hr, mem_univ _⟩))
  have hTime := hDiff.comp_hasDerivWithinAt t
    ((hasDerivWithinAt_id t I).prodMk (hasDerivWithinAt_const t I y))
    (fun r hr => (show (r,y) ∈ J from ⟨hr, mem_univ y⟩))
  have hSpace := hDiff.comp_hasFDerivAt y (hasFDerivAt_prodMk_right (𝕜 := ℝ) t y)
    (Eventually.of_forall fun z => (show (t,z) ∈ J from ⟨ht, mem_univ z⟩))
  have hEq : (1, U t y) = ((1, 0) : ℝ × Vec3) + (0, U t y) := by simp
  have hVal : terminalMaterialStep a b U f t y = D (1, U t y) := by
    unfold terminalMaterialStep
    rw [show derivWithin (fun r => f r y) I t = D (1,0) from
      hTime.derivWithin (uniqueDiffOn_Icc hab t ht)]
    rw [show fderiv ℝ (f t) y = D.comp (ContinuousLinearMap.inr ℝ ℝ Vec3) from hSpace.fderiv]
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hEq, map_add]
  rw [hVal]
  exact hPath

/-- The material time jets are exactly the time jets of the label-space
readout of a smooth Eulerian field. -/
theorem IsLabelFlowOn.terminal_iteratedDerivWithin_pullback (hX : IsLabelFlowOn U X I)
    (hab : a < b) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J)
    {s : ℝ} (hs : s ∈ I) (q : ℕ) {t : ℝ} (ht : t ∈ I) (x : Vec3) :
    iteratedDerivWithin q (fun r => f r (X s r x)) I t =
      terminalMaterialIterate a b U q f t (X s t x) := by
  induction q generalizing t with
  | zero => simp only [iteratedDerivWithin_zero, terminalMaterialIterate_zero]
  | succ q ih =>
    simp only [iteratedDerivWithin_succ, terminalMaterialIterate_succ]
    refine (derivWithin_congr (fun r hr => ih hr) (ih ht)).trans ?_
    exact (hX.terminal_hasDerivWithinAt_pullback hab
      (terminal_contDiffOn_materialIterate hab hU hf q) hs ht x).derivWithin
      (uniqueDiffOn_Icc hab t ht)

end

end TorusEuler
