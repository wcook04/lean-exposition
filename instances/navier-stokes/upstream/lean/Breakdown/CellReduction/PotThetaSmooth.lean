import Breakdown.CellReduction.PotThetaScalar
import Breakdown.CertCell.ShapeFieldWeak

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

namespace Internal

theorem slopeOn_closedBall_of_pieces {E : Type*} [NormedAddCommGroup E] {G : Space → E} (hc : Continuous G)
    {δ : ℝ} (hδ : 0 < δ) {L₁ : NNReal} (h₁ : LipschitzOnWith L₁ G (Metric.closedBall 0 δ))
    (h₂ : ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L G {y : Space | δ / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ R}) (R : ℝ) :
    ∃ L : NNReal, LipschitzOnWith L G (Metric.closedBall 0 R) := by
  obtain ⟨L₂, hL₂⟩ := h₂ R
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hc.continuousOn
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨max L₁ L₂ + Real.toNNReal (8 * max M 0 / δ), LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hK : ((max L₁ L₂ + Real.toNNReal (8 * max M 0 / δ) : NNReal) : ℝ) =
      max (L₁ : ℝ) L₂ + 8 * max M 0 / δ := by
    rw [NNReal.coe_add, NNReal.coe_max, Real.coe_toNNReal _ (by positivity)]
  rw [hK]
  have hd0 : 0 ≤ dist x y := dist_nonneg
  have hL1 : (L₁ : ℝ) ≤ max (L₁ : ℝ) L₂ := le_max_left _ _
  have hL2 : (L₂ : ℝ) ≤ max (L₁ : ℝ) L₂ := le_max_right _ _
  have hL0 : 0 ≤ max (L₁ : ℝ) L₂ := le_trans L₁.2 hL1
  have hB : 0 ≤ 8 * max M 0 / δ * dist x y := by positivity
  by_cases hfar : δ / 4 ≤ dist x y
  · have h1 : dist (G x) (G y) ≤ 2 * max M 0 := by
      rw [dist_eq_norm]
      have e1 := norm_sub_le (G x) (G y)
      have e2 := (hM x hx).trans (le_max_left M 0)
      have e3 := (hM y hy).trans (le_max_left M 0)
      linarith
    have h2 : 2 * max M 0 ≤ 8 * max M 0 / δ * dist x y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      nlinarith
    have h3 : 0 ≤ max (L₁ : ℝ) L₂ * dist x y := mul_nonneg hL0 hd0
    nlinarith
  · rw [not_le] at hfar
    have habs := abs_norm_sub_norm_le x y
    rw [← dist_eq_norm] at habs
    have hab := abs_le.1 habs
    by_cases hin : ‖x‖ ≤ δ / 2 ∨ ‖y‖ < δ / 2
    · have hxδ : x ∈ Metric.closedBall (0 : Space) δ := by
        rw [mem_closedBall_zero_iff]
        rcases hin with h | h <;> linarith
      have hyδ : y ∈ Metric.closedBall (0 : Space) δ := by
        rw [mem_closedBall_zero_iff]
        rcases hin with h | h <;> linarith
      have e := h₁.dist_le_mul x hxδ y hyδ
      have e2 : (L₁ : ℝ) * dist x y ≤ max (L₁ : ℝ) L₂ * dist x y := mul_le_mul_of_nonneg_right hL1 hd0
      nlinarith
    · rw [not_or, not_le, not_lt] at hin
      have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 hx
      have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 hy
      have e := hL₂.dist_le_mul x ⟨hin.1.le, hxR⟩ y ⟨hin.2, hyR⟩
      have e2 : (L₂ : ℝ) * dist x y ≤ max (L₁ : ℝ) L₂ * dist x y := mul_le_mul_of_nonneg_right hL2 hd0
      nlinarith

def plusCoords : Fin 3 → ℂ := ![1 / 2, 1 / (2 * Complex.I), 0]

def minusCoords : Fin 3 → ℂ := ![1 / 2, -(1 / (2 * Complex.I)), 0]

def axialCoords : Fin 3 → ℂ := ![0, 0, 1]

theorem coordsOfComponents_eq_smul (a b c : ℂ) :
    coordsOfComponents a b c = a • plusCoords + b • minusCoords + c • axialCoords := by
  funext i
  fin_cases i <;> simp [coordsOfComponents, plusCoords, minusCoords, axialCoords] <;> field_simp <;> ring_nf <;>
    simp only [Complex.I_sq] <;> ring

def scaleToVector (u : Fin 3 → ℂ) : ℂ →L[ℝ] (Fin 3 → ℂ) := (ContinuousLinearMap.id ℝ ℂ).smulRight u

theorem scaleToVector_apply (u : Fin 3 → ℂ) (a : ℂ) : scaleToVector u a = a • u := rfl

theorem smulRight_eq_comp (u : Fin 3 → ℂ) (X : Space →L[ℝ] ℂ) : X.smulRight u = (scaleToVector u).comp X := by
  ext v i
  simp [scaleToVector]

theorem slopeOn_smulRight {g : Space → ℂ} {s : Set Space} {L : NNReal} (u : Fin 3 → ℂ)
    (h : LipschitzOnWith L (fderiv ℝ g) s) :
    LipschitzOnWith (‖ContinuousLinearMap.compL ℝ Space ℂ (Fin 3 → ℂ) (scaleToVector u)‖₊ * L)
      (fun y => (fderiv ℝ g y).smulRight u) s := by
  have e : (fun y => (fderiv ℝ g y).smulRight u) =
      fun y => ContinuousLinearMap.compL ℝ Space ℂ (Fin 3 → ℂ) (scaleToVector u) (fderiv ℝ g y) := by
    funext y
    rw [smulRight_eq_comp]
    rfl
  rw [e]
  exact (ContinuousLinearMap.compL ℝ Space ℂ (Fin 3 → ℂ) (scaleToVector u)).lipschitz.comp_lipschitzOnWith h

theorem keyField_smooth {gp gn gz : Space → ℂ}
    (hp : ContDiff ℝ 1 gp ∧ ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ gp) (Metric.closedBall 0 R))
    (hn : ContDiff ℝ 1 gn ∧ ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ gn) (Metric.closedBall 0 R))
    (hz : ContDiff ℝ 1 gz ∧ ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ gz) (Metric.closedBall 0 R)) :
    IsKeyFieldSmooth (fun y => coordsOfComponents (gp y) (gn y) (gz y)) := by
  have e : (fun y => coordsOfComponents (gp y) (gn y) (gz y)) =
      fun y => gp y • plusCoords + gn y • minusCoords + gz y • axialCoords := by
    funext y
    exact coordsOfComponents_eq_smul _ _ _
  rw [e]
  have hd : ∀ y, HasFDerivAt (fun y => gp y • plusCoords + gn y • minusCoords + gz y • axialCoords)
      ((fderiv ℝ gp y).smulRight plusCoords + (fderiv ℝ gn y).smulRight minusCoords +
        (fderiv ℝ gz y).smulRight axialCoords) y := fun y =>
    ((((hp.1.differentiable one_ne_zero) y).hasFDerivAt.smul_const plusCoords).add
      (((hn.1.differentiable one_ne_zero) y).hasFDerivAt.smul_const minusCoords)).add
      (((hz.1.differentiable one_ne_zero) y).hasFDerivAt.smul_const axialCoords)
  refine ⟨((hp.1.smul contDiff_const).add (hn.1.smul contDiff_const)).add (hz.1.smul contDiff_const), fun R => ?_⟩
  have hf : fderiv ℝ (fun y => gp y • plusCoords + gn y • minusCoords + gz y • axialCoords) =
      fun y => (fderiv ℝ gp y).smulRight plusCoords + (fderiv ℝ gn y).smulRight minusCoords +
        (fderiv ℝ gz y).smulRight axialCoords := by
    funext y
    exact (hd y).fderiv
  rw [hf]
  obtain ⟨L1, h1⟩ := hp.2 R
  obtain ⟨L2, h2⟩ := hn.2 R
  obtain ⟨L3, h3⟩ := hz.2 R
  exact ⟨_, ((slopeOn_smulRight plusCoords h1).add (slopeOn_smulRight minusCoords h2)).add
    (slopeOn_smulRight axialCoords h3)⟩

theorem isWeakGradient_congr_ae {f : Space → Space} {g g' : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) (he : g =ᵐ[volume] g') : IsWeakGradient f g' := by
  refine ⟨h.1, h.2.1.congr he, fun φ hφ i => ?_⟩
  rw [← h.2.2 φ hφ i]
  refine integral_congr_ae ?_
  filter_upwards [he] with y hy
  rw [hy]

end Internal

theorem scalarValue_time (P : ShapeParams) (κ : FieldKey) (M : ℤ) (withSine : Bool) (S : PotScalar) (σ : ℝ)
    (y : Space) :
    scalarValue P κ M withSine S σ y =
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
        scalarValue P κ M withSine S 0 y := by
  have key : ∀ a b : ℝ, Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) := fun a b => by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  simp only [scalarValue]
  rw [show 2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle y +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) = 2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (2 * Real.pi * (labelTime κ.label : ℝ) * 0 + (M : ℝ) * pointAngle y +
        (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2)) by ring, key]
  ring

theorem scalar_smooth_of (hoff : ScalarSmoothAwayFromOrigin) (hnear : ScalarSmoothNearOrigin) {h : ℕ}
    {P : ShapeParams} {κ : FieldKey} {M : ℤ} {withSine : Bool} {S : PotScalar} (σ : ℝ) (hP : IsShapeParams P)
    (hS : IsPotentialScalar 2 h S) (hA : AxisAdmissible M withSine S) :
    ContDiff ℝ 1 (scalarValue P κ M withSine S σ) ∧
      ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (scalarValue P κ M withSine S σ)) (Metric.closedBall 0 R) := by
  obtain ⟨hc, hl⟩ := hoff P κ M withSine S σ hP hS.smooth_class hA
  obtain ⟨h0, δ, hδ, L₁, hL₁⟩ := hnear P κ M withSine S σ hP hS.smooth_class hA hS.start_order
  have hcd : ContDiff ℝ 1 (scalarValue P κ M withSine S σ) := contDiff_iff_contDiffAt.2 fun y => by
    by_cases hy : y = 0
    · subst hy
      exact h0
    · exact hc y hy
  exact ⟨hcd, Internal.slopeOn_closedBall_of_pieces (hcd.continuous_fderiv one_ne_zero) hδ hL₁
    fun R => hl (δ / 2) R (by positivity)⟩

theorem component_smooth_of (hoff : ScalarSmoothAwayFromOrigin) (hnear : ScalarSmoothNearOrigin) {h : ℕ}
    {P : ShapeParams} {F : PotentialSeries} {pick : PotKeyData → PotComponent → PotScalar} (hP : IsShapeParams P)
    (hF : IsPotentialPick h F pick) {κ : FieldKey} (hκ : κ ∈ F.keys) (c : PotComponent) (σ : ℝ) :
    ContDiff ℝ 1 (componentValue P κ (pick (F.data κ)) c σ) ∧
      ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (componentValue P κ (pick (F.data κ)) c σ))
        (Metric.closedBall 0 R) :=
  scalar_smooth_of hoff hnear σ hP (hF.scalar κ hκ c) (axisAdmissible_of_pick hF P.azimuthOrder hκ c)

theorem vectorPotential_contDiff_of (hoff : ScalarSmoothAwayFromOrigin) (hnear : ScalarSmoothNearOrigin) {h : ℕ}
    {P : ShapeParams} {F : PotentialSeries} {pick : PotKeyData → PotComponent → PotScalar} (hP : IsShapeParams P)
    (hF : IsPotentialPick h F pick) :
    ContDiff ℝ 1 (fun z : ℝ × Space => vectorPotential P F pick z.1 z.2) := by
  have key : ∀ κ c σ y, componentValue P κ (pick (F.data κ)) c σ y =
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
        componentValue P κ (pick (F.data κ)) c 0 y := fun κ c σ y => scalarValue_time _ _ _ _ _ _ _
  have e : (fun z : ℝ × Space => vectorPotential P F pick z.1 z.2) = fun z => realPartVec (∑ κ ∈ F.keys,
      ((Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * z.1 : ℝ) : ℂ) * Complex.I) *
          componentValue P κ (pick (F.data κ)) .plus 0 z.2) • Internal.plusCoords +
        (Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * z.1 : ℝ) : ℂ) * Complex.I) *
          componentValue P κ (pick (F.data κ)) .minus 0 z.2) • Internal.minusCoords +
        (Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * z.1 : ℝ) : ℂ) * Complex.I) *
          componentValue P κ (pick (F.data κ)) .axial 0 z.2) • Internal.axialCoords)) := by
    funext z
    simp only [vectorPotential]
    congr 1
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Internal.coordsOfComponents_eq_smul, key κ .plus z.1, key κ .minus z.1, key κ .axial z.1]
  rw [e]
  refine realPartVec.contDiff.comp (ContDiff.sum fun κ hκ => ?_)
  have he : ContDiff ℝ 1 fun z : ℝ × Space =>
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * z.1 : ℝ) : ℂ) * Complex.I) :=
    Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)).mul contDiff_const)
  have hc : ∀ c, ContDiff ℝ 1 fun z : ℝ × Space => componentValue P κ (pick (F.data κ)) c 0 z.2 := fun c =>
    (component_smooth_of hoff hnear hP hF hκ c 0).1.comp contDiff_snd
  exact (((he.mul (hc .plus)).smul contDiff_const).add ((he.mul (hc .minus)).smul contDiff_const)).add
    ((he.mul (hc .axial)).smul contDiff_const)

theorem vectorPotential_weakSecond_of (hoff : ScalarSmoothAwayFromOrigin) (hnear : ScalarSmoothNearOrigin) {h : ℕ}
    {P : ShapeParams} {F : PotentialSeries} {pick : PotKeyData → PotComponent → PotScalar} (hP : IsShapeParams P)
    (hF : IsPotentialPick h F pick) (σ : ℝ) (j : Fin 3) :
    IsWeakGradient (fun y => fderiv ℝ (vectorPotential P F pick σ) y (unitVector j))
      (fun y => (secondDeriv (vectorPotential P F pick σ) y).flip (unitVector j)) := by
  set f : FieldKey → Space → Fin 3 → ℂ := fun κ y =>
    coordsOfComponents (componentValue P κ (pick (F.data κ)) .plus σ y)
      (componentValue P κ (pick (F.data κ)) .minus σ y) (componentValue P κ (pick (F.data κ)) .axial σ y) with hfdef
  have hf : ∀ κ ∈ F.keys, IsKeyFieldSmooth (f κ) := fun κ hκ =>
    Internal.keyField_smooth (component_smooth_of hoff hnear hP hF hκ .plus σ)
      (component_smooth_of hoff hnear hP hF hκ .minus σ) (component_smooth_of hoff hnear hP hF hκ .axial σ)
  have hV : vectorPotential P F pick σ = fun x => realPartVec (∑ κ ∈ F.keys, f κ x) := rfl
  have hw := CertCell.GivenShape.Internal.weakSecondDeriv_of_keys hf j
  rw [hV]
  refine Internal.isWeakGradient_congr_ae hw ?_
  set L := ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec with hLdef
  have hLapp : ∀ X : Space →L[ℝ] (Fin 3 → ℂ), L X = realPartVec.comp X := fun X => rfl
  have hW : ∀ y, fderiv ℝ (fun x => realPartVec (∑ κ ∈ F.keys, f κ x)) y = ∑ κ ∈ F.keys, L (fderiv ℝ (f κ) y) := by
    intro y
    have hs : HasFDerivAt (fun x => ∑ κ ∈ F.keys, f κ x) (∑ κ ∈ F.keys, fderiv ℝ (f κ) y) y :=
      HasFDerivAt.fun_sum fun κ hκ => (((hf κ hκ).smooth.differentiable one_ne_zero) y).hasFDerivAt
    rw [← map_sum, hLapp]
    exact (realPartVec.hasFDerivAt.comp y hs).fderiv
  have hWf : (fun x => fderiv ℝ (fun x => realPartVec (∑ κ ∈ F.keys, f κ x)) x) =
      fun x => ∑ κ ∈ F.keys, L (fderiv ℝ (f κ) x) := funext hW
  have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ κ ∈ F.keys, DifferentiableAt ℝ (fderiv ℝ (f κ)) y :=
    (Filter.eventually_all_finset F.keys).2 fun κ hκ =>
      CertCell.GivenShape.Internal.ae_differentiableAt_of_ball_slopeBound (hf κ hκ).gradient_slope_bound
  filter_upwards [hall] with y hy
  have hd : HasFDerivAt (fun x => ∑ κ ∈ F.keys, L (fderiv ℝ (f κ) x))
      (∑ κ ∈ F.keys, L.comp (fderiv ℝ (fun x => fderiv ℝ (f κ) x) y)) y :=
    HasFDerivAt.fun_sum fun κ hκ => L.hasFDerivAt.comp y (hy κ hκ).hasFDerivAt
  simp only [secondDeriv]
  rw [hWf, hd.fderiv]

theorem vectorPotential_gradientSlope_of (hoff : ScalarSmoothAwayFromOrigin) (hnear : ScalarSmoothNearOrigin) {h : ℕ}
    {P : ShapeParams} {F : PotentialSeries} {pick : PotKeyData → PotComponent → PotScalar} (hP : IsShapeParams P)
    (hF : IsPotentialPick h F pick) (σ : ℝ) :
    ContDiff ℝ 1 (vectorPotential P F pick σ) ∧
      ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (vectorPotential P F pick σ)) (Metric.closedBall 0 R) := by
  set f : FieldKey → Space → Fin 3 → ℂ := fun κ y =>
    coordsOfComponents (componentValue P κ (pick (F.data κ)) .plus σ y)
      (componentValue P κ (pick (F.data κ)) .minus σ y) (componentValue P κ (pick (F.data κ)) .axial σ y) with hfdef
  have hf : ∀ κ ∈ F.keys, IsKeyFieldSmooth (f κ) := fun κ hκ =>
    Internal.keyField_smooth (component_smooth_of hoff hnear hP hF hκ .plus σ)
      (component_smooth_of hoff hnear hP hF hκ .minus σ) (component_smooth_of hoff hnear hP hF hκ .axial σ)
  have hV : vectorPotential P F pick σ = fun x => realPartVec (∑ κ ∈ F.keys, f κ x) := rfl
  rw [hV]
  have hsum : ContDiff ℝ 1 fun x => ∑ κ ∈ F.keys, f κ x := ContDiff.sum fun κ hκ => (hf κ hκ).smooth
  refine ⟨realPartVec.contDiff.comp hsum, fun R => ?_⟩
  set L := ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec with hLdef
  have hW : fderiv ℝ (fun x => realPartVec (∑ κ ∈ F.keys, f κ x)) = fun y => ∑ κ ∈ F.keys, (1 : ℝ) • L (fderiv ℝ (f κ) y) := by
    funext y
    have hs : HasFDerivAt (fun x => ∑ κ ∈ F.keys, f κ x) (∑ κ ∈ F.keys, fderiv ℝ (f κ) y) y :=
      HasFDerivAt.fun_sum fun κ hκ => (((hf κ hκ).smooth.differentiable one_ne_zero) y).hasFDerivAt
    simp only [one_smul]
    rw [← map_sum]
    exact (realPartVec.hasFDerivAt.comp y hs).fderiv
  rw [hW]
  exact FracInternal.slopeOn_finset_sum F.keys (fun _ => (1 : ℝ)) (fun κ y => L (fderiv ℝ (f κ) y))
    (fun κ hκ R => by
      obtain ⟨C, hC⟩ := (hf κ hκ).gradient_slope_bound R
      exact ⟨‖L‖₊ * C, L.lipschitz.comp_lipschitzOnWith hC⟩) R

end PotentialShape

end Breakdown
