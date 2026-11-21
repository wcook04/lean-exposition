import Breakdown.CellReduction.InstMovedParams

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

def movePhase (j : ℤ) (moving : ℝ → ℝ) (a : ℝ) (y : Space) : ℂ :=
  Complex.exp ((((j : ℝ) * a * moving (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)

theorem movePhase_sub_one_mul (j : ℤ) (moving : ℝ → ℝ) (a : ℝ) (y : Space) :
    movePhase j moving (a - 1) y * movePhase j moving 1 y = movePhase j moving a y := by
  unfold movePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem radialPhase_differentiableAt {f : ℝ → ℝ} (hf : IsRadialPhase f) {s : ℝ} (hs : 0 ≤ s) :
    DifferentiableAt ℝ f s := by
  obtain ⟨δ, hδ, h⟩ := hf.smooth
  exact (radialPhase_contDiffAt h hδ hs).differentiableAt (by norm_num)

theorem phaseSlope_moved (P : ShapeParams) (moving : ℝ → ℝ) (hP : IsRadialPhase P.radialPhase)
    (hm : IsRadialPhase moving) (a t : ℝ) :
    phaseSlope (movedParams P moving a) t =
      phaseSlope P t + a * (2 * chartRadius P t ^ 2 * deriv moving (chartRadius P t ^ 2)) := by
  have hs : 0 ≤ chartRadius P t ^ 2 := sq_nonneg _
  have d₁ := (radialPhase_differentiableAt hP hs).hasDerivAt
  have d₂ := (radialPhase_differentiableAt hm hs).hasDerivAt
  have hd : deriv (fun s => P.radialPhase s + a * moving s) (chartRadius P t ^ 2) =
      deriv P.radialPhase (chartRadius P t ^ 2) + a * deriv moving (chartRadius P t ^ 2) :=
    (d₁.add (d₂.const_mul a)).deriv
  show 2 * chartRadius P t ^ 2 * deriv (fun s => P.radialPhase s + a * moving s) (chartRadius P t ^ 2) = _
  rw [hd]
  unfold phaseSlope
  ring

theorem reducedComps_moved (P : ShapeParams) (moving : ℝ → ℝ) (hP : IsRadialPhase P.radialPhase)
    (hm : IsRadialPhase moving) (κ : FieldKey) (A : KeyAmp) (a t x : ℝ) (c : Fin 3) :
    reducedComps (movedParams P moving a) κ A t x c =
      ((1 - a : ℝ) : ℂ) * reducedComps P κ A t x c + (a : ℂ) * reducedComps (movedParams P moving 1) κ A t x c := by
  have ha := phaseSlope_moved P moving hP hm a t
  have h1 := phaseSlope_moved P moving hP hm 1 t
  have hs : ∀ b, streamValue (movedParams P moving b) A = streamValue P A := fun _ => rfl
  have hz : ∀ b, (movedParams P moving b).azimuthOrder = P.azimuthOrder := fun _ => rfl
  unfold reducedComps shiftedScale
  simp only [hs, hz, ha, h1]
  split_ifs <;> fin_cases c <;> simp <;> ring

theorem keyPhase_moved (P : ShapeParams) (moving : ℝ → ℝ) (κ : FieldKey) (a σ : ℝ) (y : Space) :
    keyPhase (movedParams P moving a) κ σ y = keyPhase P κ σ y * movePhase κ.phaseIndex moving a y := by
  unfold keyPhase movePhase
  rw [← Complex.exp_add]
  congr 1
  show (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (labelAzimuth P.azimuthOrder κ.label : ℝ) * pointAngle y +
      (κ.phaseIndex : ℝ) * (P.radialPhase (‖y‖ ^ 2) + a * moving (‖y‖ ^ 2)) : ℝ) : ℂ) * Complex.I) = _
  push_cast
  ring

theorem keyVector_moved (P : ShapeParams) (moving : ℝ → ℝ) (hP : IsRadialPhase P.radialPhase)
    (hm : IsRadialPhase moving) (κ : FieldKey) (A : KeyAmp) (a σ : ℝ) (y : Space) :
    keyVector (movedParams P moving a) κ A σ y =
      (((1 - a : ℝ) : ℂ) * movePhase κ.phaseIndex moving a y) • keyVector P κ A σ y +
        ((a : ℂ) * movePhase κ.phaseIndex moving (a - 1) y) • keyVector (movedParams P moving 1) κ A σ y := by
  have hc : ∀ b, chartCoord (movedParams P moving b) y = chartCoord P y := fun _ => rfl
  funext i
  simp only [keyVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc, keyPhase_moved,
    reducedComps_moved P moving hP hm κ A a]
  rw [← movePhase_sub_one_mul κ.phaseIndex moving a y]
  ring

theorem contDiff_movePhase (j : ℤ) {moving : ℝ → ℝ} (hm : IsRadialPhase moving) :
    ContDiff ℝ 1 (fun z : ℝ × Space => movePhase j moving z.1 z.2) := by
  obtain ⟨δ, hδ, h⟩ := hm.smooth
  have hX : ContDiff ℝ 1 (fun y : Space => moving (‖y‖ ^ 2)) :=
    (h.of_le (by norm_num)).comp_contDiff (contDiff_norm_sq ℝ)
      (fun y => Set.mem_Ioi.mpr (by have := sq_nonneg ‖y‖; linarith))
  unfold movePhase
  refine Complex.contDiff_exp.comp (ContDiff.mul ?_ contDiff_const)
  refine Complex.ofRealCLM.contDiff.comp ?_
  exact (contDiff_const.mul contDiff_fst).mul (hX.comp contDiff_snd)

end Internal

end Instantiation

end CellReduction

end Breakdown
