import Breakdown.Cert.Nodes
import Breakdown.FreqTr.Realization

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown.Cert

open Freq

open scoped Classical

namespace Internal.FreeEquivariant

theorem coeFn_shiftLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (x : Lp (α := TimeCircle) E 2) :
    (shiftLp a x : TimeCircle → E) =ᵐ[volume] fun t => x (t + (a : TimeCircle)) :=
  Lp.coeFn_compMeasurePreserving x (measurePreserving_add_right volume (a : TimeCircle))

theorem shiftLp_compLpL {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (a : ℝ)
    (x : Lp (α := TimeCircle) E 2) :
    shiftLp a (ContinuousLinearMap.compLpL 2 volume L x) =
      ContinuousLinearMap.compLpL 2 volume L (shiftLp a x) := by
  have hq := (measurePreserving_add_right volume (a : TimeCircle)).quasiMeasurePreserving
  apply Lp.ext
  filter_upwards [coeFn_shiftLp a (ContinuousLinearMap.compLpL 2 volume L x),
    ContinuousLinearMap.coeFn_compLpL L (shiftLp a x), hq.ae (ContinuousLinearMap.coeFn_compLpL L x),
    coeFn_shiftLp a x] with t h1 h2 h3 h4
  rw [h1, h2, h3, h4]

theorem shiftLp_shiftLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℝ)
    (x : Lp (α := TimeCircle) E 2) : shiftLp a (shiftLp b x) = shiftLp b (shiftLp a x) := by
  have ha := (measurePreserving_add_right volume (a : TimeCircle)).quasiMeasurePreserving
  have hb := (measurePreserving_add_right volume (b : TimeCircle)).quasiMeasurePreserving
  apply Lp.ext
  filter_upwards [coeFn_shiftLp a (shiftLp b x), coeFn_shiftLp b (shiftLp a x),
    ha.ae (coeFn_shiftLp b x), hb.ae (coeFn_shiftLp a x)] with t h1 h2 h3 h4
  rw [h1, h2, h3, h4, add_right_comm]

theorem compLpL_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M N K : E →L[ℝ] E) (h : ∀ y, L (M y) = N (K y)) (x : Lp (α := TimeCircle) E 2) :
    ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) L
        (ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) M x) =
      ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) N
        (ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) K x) := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL L
      (ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) M x),
    ContinuousLinearMap.coeFn_compLpL M x,
    ContinuousLinearMap.coeFn_compLpL N
      (ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) K x),
    ContinuousLinearMap.coeFn_compLpL K x] with t h1 h2 h3 h4
  rw [h1, h2, h3, h4, h]

theorem rotX_smoothH (R : Space ≃ₗᵢ[ℝ] Space) {t : ℝ} (ht : 0 < t) (x : HBar) :
    rotX R (smoothH t x) = smoothH t (rotX R x) := by
  by_cases h : ∀ y ∈ Sig,
      fieldOp id (fun ξ => phiFactor t ξ • ContinuousLinearMap.id ℝ CSpace) y ∈ Sig
  · apply Subtype.ext
    have e1 := (rotation_holds R).1 (smoothH t x)
    have e2 := (rotation_holds R).1 x
    have e3 : (smoothH t x : L2C) =
        fieldOp id (fun ξ => phiFactor t ξ • ContinuousLinearMap.id ℝ CSpace) x :=
      restrictX_coe h x
    have e4 : (smoothH t (rotX R x) : L2C) =
        fieldOp id (fun ξ => phiFactor t ξ • ContinuousLinearMap.id ℝ CSpace) (rotX R x) :=
      restrictX_coe h (rotX R x)
    rw [e1, e4, e3, e2]
    exact (Freq.Internal.BilinRotate.phiOp_rot fieldOpRealized_holds t ht R x).symm
  · have h0 : smoothH t = 0 := by
      rw [smoothH, restrictX, dif_neg h]
    simp only [h0, zero_apply, map_zero]

theorem rotX_slicePropagator (R : Space ≃ₗᵢ[ℝ] Space) {τ : ℝ} (hτ : 0 < τ) (x : HBar) :
    rotX R (slicePropagator τ x) = slicePropagator τ (rotX R x) := by
  have ht : 0 < 1 - Real.exp (-τ) := sub_pos.2 (Real.exp_lt_one_iff.2 (neg_neg_of_pos hτ))
  calc rotX R (slicePropagator τ x)
      = rotX R (dilX (Real.exp (-τ)) (smoothH (1 - Real.exp (-τ)) x)) := rfl
    _ = dilX (Real.exp (-τ)) (rotX R (smoothH (1 - Real.exp (-τ)) x)) :=
        (rotation_holds R).2.2 _ _
    _ = dilX (Real.exp (-τ)) (smoothH (1 - Real.exp (-τ)) (rotX R x)) :=
        congrArg (dilX (Real.exp (-τ))) (rotX_smoothH R ht x)
    _ = slicePropagator τ (rotX R x) := rfl

theorem rotHH_compLpL_slicePropagator (R : Space ≃ₗᵢ[ℝ] Space) {τ : ℝ} (hτ : 0 < τ) (w : HH) :
    rotHH R (ContinuousLinearMap.compLpL 2 volume (slicePropagator τ) w) =
      ContinuousLinearMap.compLpL 2 volume (slicePropagator τ) (rotHH R w) :=
  compLpL_comm _ _ _ _ (fun y => rotX_slicePropagator R hτ y) w

theorem mem_invariantHH_iff {Γ : Set Symmetry} {f : HH} :
    f ∈ invariantHH Γ ↔ ∀ γ ∈ Γ, (shiftLp γ.2 : HH →L[ℝ] HH) f = rotHH γ.1 f := by
  constructor
  · intro hf γ hγ
    have h0 : f ∈ LinearMap.ker
        (((shiftLp γ.2 : HH →L[ℝ] HH) - rotHH γ.1 : HH →L[ℝ] HH) : HH →ₗ[ℝ] HH) :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf γ) hγ
    exact sub_eq_zero.1 (LinearMap.mem_ker.1 h0)
  · intro hf
    refine (Submodule.mem_iInf _).2 fun γ => (Submodule.mem_iInf _).2 fun hγ => ?_
    refine LinearMap.mem_ker.2 ?_
    exact sub_eq_zero.2 (hf γ hγ)

theorem propagatorIntegrand_mem {Γ : Set Symmetry} {P : ℝ} {f : HH} (hf : f ∈ invariantHH Γ)
    {τ : ℝ} (hτ : 0 < τ) : propagatorIntegrand P f τ ∈ invariantHH Γ := by
  refine mem_invariantHH_iff.2 fun γ hγ => ?_
  unfold propagatorIntegrand
  calc (shiftLp γ.2 : HH →L[ℝ] HH) (ContinuousLinearMap.compLpL 2 volume (slicePropagator τ)
          ((shiftLp (-(τ / P)) : HH →L[ℝ] HH) f))
      = ContinuousLinearMap.compLpL 2 volume (slicePropagator τ)
          ((shiftLp γ.2 : HH →L[ℝ] HH) ((shiftLp (-(τ / P)) : HH →L[ℝ] HH) f)) :=
        shiftLp_compLpL _ _ _
    _ = ContinuousLinearMap.compLpL 2 volume (slicePropagator τ)
          ((shiftLp (-(τ / P)) : HH →L[ℝ] HH) ((shiftLp γ.2 : HH →L[ℝ] HH) f)) :=
        congrArg (ContinuousLinearMap.compLpL 2 volume (slicePropagator τ))
          (shiftLp_shiftLp _ _ _)
    _ = ContinuousLinearMap.compLpL 2 volume (slicePropagator τ)
          ((shiftLp (-(τ / P)) : HH →L[ℝ] HH) (rotHH γ.1 f)) :=
        congrArg (fun g : HH => ContinuousLinearMap.compLpL 2 volume (slicePropagator τ)
          ((shiftLp (-(τ / P)) : HH →L[ℝ] HH) g)) (mem_invariantHH_iff.1 hf γ hγ)
    _ = ContinuousLinearMap.compLpL 2 volume (slicePropagator τ)
          (rotHH γ.1 ((shiftLp (-(τ / P)) : HH →L[ℝ] HH) f)) :=
        congrArg (ContinuousLinearMap.compLpL 2 volume (slicePropagator τ))
          (shiftLp_compLpL _ _ _)
    _ = rotHH γ.1 (ContinuousLinearMap.compLpL 2 volume (slicePropagator τ)
          ((shiftLp (-(τ / P)) : HH →L[ℝ] HH) f)) :=
        (rotHH_compLpL_slicePropagator γ.1 hτ _).symm

theorem integral_mem {Γ : Set Symmetry} {P : ℝ} {f : HH} (hf : f ∈ invariantHH Γ) :
    (∫ τ in Set.Ioi (0 : ℝ), propagatorIntegrand P f τ) ∈ invariantHH Γ := by
  refine mem_invariantHH_iff.2 fun γ hγ => sub_eq_zero.1 ?_
  refine (sub_apply _ _ _).symm.trans ?_
  by_cases hi : Integrable (propagatorIntegrand P f) (volume.restrict (Set.Ioi (0 : ℝ)))
  · refine (ContinuousLinearMap.integral_comp_comm _ hi).symm.trans ?_
    have hz : Set.EqOn (fun τ => ((shiftLp γ.2 : HH →L[ℝ] HH) - rotHH γ.1 : HH →L[ℝ] HH)
        (propagatorIntegrand P f τ)) (fun _ => (0 : HH)) (Set.Ioi 0) := fun τ hτ =>
      (sub_apply _ _ _).trans
        (sub_eq_zero.2 (mem_invariantHH_iff.1 (propagatorIntegrand_mem (P := P) hf hτ) γ hγ))
    exact (setIntegral_congr_fun measurableSet_Ioi hz).trans (integral_zero _ _)
  · exact (congrArg _ (integral_undef hi)).trans (map_zero _)

theorem gradInv_eq (P : ℝ) (hg : ∃ T, GradInvSpec P T) : gradInv P = hg.choose := by
  unfold gradInv
  exact dif_pos hg

theorem gradInv_eq_zero (P : ℝ) (hg : ¬ ∃ T, GradInvSpec P T) : gradInv P = 0 := by
  unfold gradInv
  exact dif_neg hg

theorem gradInv_mem {Γ : Set Symmetry} {P : ℝ} {f : HH} (hf : f ∈ invariantHH Γ) :
    gradInv P f ∈ invariantHH Γ := by
  by_cases hg : ∃ T, GradInvSpec P T
  · have e : gradInv P f = ∫ τ in Set.Ioi (0 : ℝ), propagatorIntegrand P f τ :=
      (DFunLike.congr_fun (gradInv_eq P hg) f).trans (hg.choose_spec f)
    exact Eq.mpr (congrArg (fun x : HH => x ∈ invariantHH Γ) e) (integral_mem hf)
  · have e : gradInv P f = 0 := DFunLike.congr_fun (gradInv_eq_zero P hg) f
    exact Eq.mpr (congrArg (fun x : HH => x ∈ invariantHH Γ) e) (Submodule.zero_mem _)

theorem freeInv_eq (P : ℝ) (hx : ∃ T, FreeInvSpec P T) : freeInv P = hx.choose := by
  unfold freeInv
  exact dif_pos hx

end Internal.FreeEquivariant

open Internal.FreeEquivariant in
theorem freeEquivariantHolds_of (h : FreeInvHolds) : FreeEquivariantHolds := by
  intro Γ P hP f hf
  have hx := (h P hP).1
  have e : gradCLM (freeInv P f) = gradInv P f :=
    (congrArg gradCLM (DFunLike.congr_fun (freeInv_eq P hx) f)).trans (hx.choose_spec f)
  exact Eq.mpr (congrArg (fun x : HH => x ∈ invariantHH Γ) e) (gradInv_mem hf)

end Breakdown.Cert
