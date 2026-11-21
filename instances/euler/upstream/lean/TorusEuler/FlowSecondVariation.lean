import TorusEuler.HigherFlowBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! The second spatial variational equation used in
`cc:uf:trunc:eq:recursion`. -/

open Asymptotics ContinuousLinearMap Filter MeasureTheory Set
open scoped NNReal Topology

namespace TorusEuler

section LinearFamily

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "End" => E →L[ℝ] E
local notation "Compose" => ContinuousLinearMap.compL ℝ E E E

/-- In a product with one vanishing factor, differentiability of the other
factor can be replaced by continuity. -/
private theorem hasFDerivAt_comp_of_zero_left {f g : P → End} {df : P →L[ℝ] End}
    {p : P} (hf : HasFDerivAt f df p) (hzero : f p = 0) (hg : ContinuousAt g p) :
    HasFDerivAt (fun q => (f q).comp (g q)) (((Compose).flip (g p)).comp df) p := by
  have hrem : (fun q => f q - df (q - p)) =o[𝓝 p] (fun q => q - p) := by
    simpa only [hzero, sub_zero] using (hasFDerivAt_iff_isLittleO.mp hf)
  have hfirst : (fun q => (f q - df (q - p)).comp (g p)) =o[𝓝 p] (fun q => q - p) :=
    (IsBigO.of_bound ‖g p‖ (Eventually.of_forall fun q => by
      simpa only [mul_comm] using opNorm_comp_le (f q - df (q - p)) (g p))).trans_isLittleO hrem
  have hfO : (fun q => ‖f q‖) =O[𝓝 p] (fun q => ‖q - p‖) := by
    simpa only [hzero, sub_zero] using hf.isBigO_sub.norm_left.norm_right
  have hg' : ContinuousAt (fun q => g q - g p) p := hg.sub continuousAt_const
  have hgSmall : (fun q => ‖g q - g p‖) =o[𝓝 p] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (by simpa only [sub_self, norm_zero] using hg'.norm.tendsto)
  have hprod : (fun q => ‖f q‖ * ‖g q - g p‖) =o[𝓝 p] (fun q => ‖q - p‖) := by
    simpa only [mul_one] using hfO.mul_isLittleO hgSmall
  have hcomp : (fun q => (f q).comp (g q - g p)) =O[𝓝 p]
      (fun q => ‖f q‖ * ‖g q - g p‖) :=
    IsBigO.of_norm_le fun q => opNorm_comp_le (f q) (g q - g p)
  have hsecond : (fun q => (f q).comp (g q - g p)) =o[𝓝 p] (fun q => q - p) :=
    isLittleO_norm_right.mp (hcomp.trans_isLittleO hprod)
  apply hasFDerivAt_iff_isLittleO.mpr
  refine (hfirst.add hsecond).congr_left fun q => ?_
  simp only [hzero, zero_comp, sub_zero, comp_apply, flip_apply, compL_apply, sub_comp, comp_sub]
  abel

variable [CompleteSpace E]

/-- Differentiate the fundamental solution with respect to its parameter.
A dominated difference formula uses the derivative of the coefficient at
the parameter in question and only continuity of the fundamental solution
there. -/
theorem linearFundamental_parameterDerivative
    {A F : ℝ → P → End} {DA : ℝ → P →L[ℝ] End}
    {T C : ℝ} {L : ℝ≥0} (hT : 0 ≤ T) (p : P)
    (hA : ∀ q, ContinuousOn (fun s => A s q) (Icc 0 T))
    (hLip : ∀ s ∈ Icc 0 T, LipschitzWith L (A s))
    (hDA : ∀ s ∈ Icc 0 T, HasFDerivAt (A s) (DA s) p)
    (hDAcont : ContinuousOn DA (Icc 0 T))
    (hF₀ : ∀ q, F 0 q = .id ℝ E)
    (hF : ∀ q, ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun d => F d q)
      ((A s q).comp (F s q)) (Icc 0 T) s)
    (hFcont : ∀ s ∈ Icc 0 T, ContinuousAt (F s) p)
    (hFnorm : ∀ q, ∀ s ∈ Icc 0 T, ‖F s q‖ ≤ C) :
    ∃ W : ℝ → P →L[ℝ] End, W 0 = 0 ∧
      (∀ s ∈ Icc 0 T, HasFDerivAt (F s) (W s) p) ∧
      ∀ s ∈ Icc 0 T, HasDerivWithinAt W
        (((Compose (A s p)).comp (W s)) + (((Compose).flip (F s p)).comp (DA s))) (Icc 0 T) s := by
  let B (s : ℝ) : End →L[ℝ] End := Compose (A s p)
  have hB : ContinuousOn B (Icc 0 T) := (Compose).continuous.comp_continuousOn (hA p)
  let postcompose := ContinuousLinearMap.compL ℝ P End End
  let forcing (s : ℝ) := ((Compose).flip (F s p)).comp (DA s)
  have hFc (q : P) : ContinuousOn (fun s => F s q) (Icc 0 T) :=
    HasDerivWithinAt.continuousOn (hF q)
  have hforcing : ContinuousOn forcing (Icc 0 T) :=
    ((Compose).flip.continuous.comp_continuousOn (hFc p)).clm_comp hDAcont
  have hleft : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT
  obtain ⟨W, hW₀, hW⟩ := linearODE_inhom_exists_Icc hleft
    (postcompose.continuous.comp_continuousOn hB) hforcing (0 : P →L[ℝ] End)
  refine ⟨W, hW₀, ?_, fun s hs => hW s hs⟩
  intro t ht
  let Ξ := ContinuousLinearMap.compL ℝ End End End
  obtain ⟨Φ, hΦ₀, hΦ⟩ := linearODE_exists_Icc (E := End →L[ℝ] End)
    (A := fun s => Ξ (B s)) hT (Ξ.continuous.comp_continuousOn hB)
    (ContinuousLinearMap.id ℝ End)
  obtain ⟨Ψ, hΨ₀, hΨ⟩ := linearODE_exists_Icc (E := End →L[ℝ] End)
    (A := fun s => -(Ξ.flip (B s))) hT (Ξ.flip.continuous.comp_continuousOn hB).neg
    (ContinuousLinearMap.id ℝ End)
  let K (s : ℝ) := (Φ t).comp (Ψ s)
  let N (q : P) (s : ℝ) := (A s q - A s p).comp (F s q)
  let integrand (q : P) (s : ℝ) := K s (N q s)
  let diffIntegrand (s : ℝ) := (K s).comp (forcing s)
  have hΨc : ContinuousOn Ψ (Icc 0 T) := HasDerivWithinAt.continuousOn hΨ
  have hK : ContinuousOn K (Icc 0 T) := continuousOn_const.clm_comp hΨc
  have hN (q : P) : ContinuousOn (N q) (Icc 0 T) := ((hA q).sub (hA p)).clm_comp (hFc q)
  have hIntegrand (q : P) : ContinuousOn (integrand q) (Icc 0 T) := hK.clm_apply (hN q)
  have hDiffIntegrand : ContinuousOn diffIntegrand (Icc 0 T) := hK.clm_comp hforcing
  have hformula (q : P) : F t q - F t p = ∫ s in (0 : ℝ)..t, integrand q s := by
    have hEq (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivWithinAt
        (fun d => F d q - F d p) (B s (F s q - F s p) + N q s) (Icc 0 T) s := by
      apply ((hF q s hs).sub (hF p s hs)).congr_deriv
      simp only [B, N, compL_apply, comp_sub, sub_comp]
      abel
    simpa only [hF₀, sub_self, map_zero, zero_add, integrand, K, comp_apply] using
      linearODE_variation_of_constants hB (hN q) hΦ₀ hΨ₀ hΦ hΨ hEq ht
  let μ := volume.restrict (Ioc (0 : ℝ) t)
  have hsub : Ioc (0 : ℝ) t ⊆ Icc 0 T := Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)
  have hC : 0 ≤ C := (norm_nonneg (F 0 p)).trans (hFnorm p 0 hleft)
  let bound (s : ℝ) := ‖K s‖ * L * C
  have hNorm : Continuous (fun M : End →L[ℝ] End => ‖M‖) :=
    continuous_norm (E := End →L[ℝ] End)
  have hKnorm : ContinuousOn (fun s => ‖K s‖) (Icc 0 T) :=
    hNorm.comp_continuousOn hK
  have hboundC : ContinuousOn bound (Icc 0 T) :=
    (hKnorm.mul (continuousOn_const (c := (L : ℝ)))).mul (continuousOn_const (c := C))
  have hboundInt : IntervalIntegrable bound volume 0 t :=
    (hboundC.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hInt : IntervalIntegrable (integrand p) volume 0 t :=
    ((hIntegrand p).mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hSlope : ∀ᵐ s ∂μ, ∀ q ∈ (univ : Set P),
      ‖integrand q s - integrand p s‖ ≤ bound s * ‖q - p‖ := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc (0 : ℝ) t) measurableSet_Ioc] with s hs q _
    have hs' := hsub hs
    have hAs : ‖A s q - A s p‖ ≤ (L : ℝ) * ‖q - p‖ := (hLip s hs').norm_sub_le q p
    have hbase : integrand p s = 0 := by simp [integrand, N]
    rw [hbase, sub_zero]
    calc
      ‖integrand q s‖ ≤ ‖K s‖ * (‖A s q - A s p‖ * ‖F s q‖) :=
        ((K s).le_opNorm _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ ‖K s‖ * (((L : ℝ) * ‖q - p‖) * C) := by
        gcongr
        exact hFnorm q s hs'
      _ = _ := by dsimp only [bound]; ring
  have hDeriv : ∀ᵐ s ∂μ, HasFDerivAt (fun q => integrand q s) (diffIntegrand s) p := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc (0 : ℝ) t) measurableSet_Ioc] with s hs
    have hAshift : HasFDerivAt (fun q => A s q - A s p) (DA s) p :=
      (hDA s (hsub hs)).sub_const (A s p)
    have hNdiff : HasFDerivAt (fun q => N q s) (forcing s) p :=
      hasFDerivAt_comp_of_zero_left hAshift (sub_self _) (hFcont s (hsub hs))
    exact (K s).hasFDerivAt.comp p hNdiff
  have hMeas (q : P) : AEStronglyMeasurable (integrand q) μ :=
    (hIntegrand q).aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_Ioc hsub
  have hDInt := ContinuousOn.integrableOn_Icc (E := P →L[ℝ] End) (μ := volume) hDiffIntegrand
  have hDMeas : AEStronglyMeasurable diffIntegrand μ :=
    (hDInt.mono_set hsub).aestronglyMeasurable
  obtain ⟨hDiffInt, hUnderInt⟩ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip' (μ := μ) univ_mem
      (fun q _ => hMeas q) hInt.1 hDMeas hSlope hboundInt.1 hDeriv
  have hWformula : W t = ∫ s, diffIntegrand s ∂μ := by
    ext q : 1
    have hEq (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivWithinAt
        (fun d => W d q) (B s (W s q) + forcing s q) (Icc 0 T) s := by
      simpa only [postcompose, Function.comp_def, compL_apply, comp_apply, _root_.add_apply,
        _root_.map_zero, add_zero] using
        (hW s hs).clm_apply (hasDerivWithinAt_const s (Icc 0 T) q)
    rw [ContinuousLinearMap.integral_apply hDiffInt]
    simpa only [hW₀, zero_apply, map_zero, zero_add, diffIntegrand, K, comp_apply,
      intervalIntegral.integral_of_le ht.1, μ] using
      linearODE_variation_of_constants hB (hforcing.clm_apply continuousOn_const) hΦ₀ hΨ₀ hΦ hΨ hEq ht
  rw [← hWformula] at hUnderInt
  have hAt : HasFDerivAt (fun q => ∫ s in (0 : ℝ)..t, integrand q s) (W t) p := by
    simpa only [intervalIntegral.integral_of_le ht.1] using hUnderInt
  have hSum : HasFDerivAt (fun q => (∫ s in (0 : ℝ)..t, integrand q s) + F t p) (W t) p :=
    hAt.add_const (F t p)
  refine hSum.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun q => (sub_add_cancel (F t q) (F t p)).symm.trans
    (congrArg (fun z => z + F t p) (hformula q))

end LinearFamily

private theorem hasFDerivAt_spatialSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : ℝ × Vec3 → E} {T s : ℝ}
    (hV : DifferentiableOn ℝ V (Icc 0 T ×ˢ (univ : Set Vec3))) (hs : s ∈ Icc 0 T) (a : Vec3) :
    HasFDerivAt (fun x => V (s, x))
      ((fderivWithin ℝ V (Icc 0 T ×ˢ (univ : Set Vec3)) (s, a)).comp
        (ContinuousLinearMap.inr ℝ ℝ Vec3)) a :=
  (hV (s, a) ⟨hs, mem_univ _⟩).hasFDerivWithinAt.comp_hasFDerivAt a
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) s a) (Eventually.of_forall fun x => ⟨hs, mem_univ x⟩)

private theorem fderiv_spatiallyPeriodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec3 → E} (hper : ∀ n a, f (a + latticeVector n) = f a)
    (n : Fin 3 → ℤ) (a : Vec3) : fderiv ℝ f (a + latticeVector n) = fderiv ℝ f a := by
  have heq := congrArg (fun g => fderiv ℝ g a) (funext (hper n))
  rwa [fderiv_comp_add_right] at heq

/-- The spatial derivative of the actual label Jacobian exists and obeys
the Hessian-forced time equation on the closed slab. -/
theorem IsLabelFlowOn.labelSecondDerivative_evolves
    {U : Velocity} {X : ℝ → Velocity} {T : ℝ} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ s ∈ Icc 0 T, SpatiallyPeriodic (U s)) (a : Vec3) :
    let Z (s : ℝ) := fderiv ℝ (fderiv ℝ (X 0 s)) a
    Z 0 = 0 ∧ ∀ t ∈ Icc 0 T, HasFDerivAt (fderiv ℝ (X 0 t)) (Z t) a ∧
      ∀ u v : Vec3, HasDerivWithinAt (fun s => Z s u v)
        (fderiv ℝ (U t) (X 0 t a) (Z t u v) +
          fderiv ℝ (fderiv ℝ (U t)) (X 0 t a)
            (fderiv ℝ (X 0 t) a u) (fderiv ℝ (X 0 t) a v)) (Icc 0 T) t := by
  let S := Icc 0 T ×ˢ (univ : Set Vec3)
  let lift := ContinuousLinearMap.inr ℝ ℝ Vec3
  let grad (q : ℝ × Vec3) := (fderivWithin ℝ (Function.uncurry U) S q).comp lift
  let hess (q : ℝ × Vec3) := (fderivWithin ℝ grad S q).comp lift
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hgrad : ContDiffOn ℝ 1 grad S :=
    (hU.fderivWithin hS (m := 1) (by norm_num)).clm_comp contDiffOn_const
  have hhess : ContinuousOn hess S :=
    (hgrad.continuousOn_fderivWithin hS le_rfl).clm_comp continuousOn_const
  have hD (s : ℝ) (hs : s ∈ Icc 0 T) (x : Vec3) : HasFDerivAt (U s) (grad (s, x)) x :=
    hasFDerivAt_spatialSlice (hU.differentiableOn (by norm_num)) hs x
  have hH (s : ℝ) (hs : s ∈ Icc 0 T) (x : Vec3) :
      HasFDerivAt (fderiv ℝ (U s)) (hess (s, x)) x :=
    (hasFDerivAt_spatialSlice hgrad.differentiableOn_one hs x).congr_of_eventuallyEq
      (Eventually.of_forall fun y => (hD s hs y).fderiv)
  have hCell : IsCompact (Icc 0 T ×ˢ centeredCell) := isCompact_Icc.prod isCompact_centeredCell
  obtain ⟨L₀, hL₀⟩ := hCell.exists_bound_of_continuousOn (f := hess)
    (hhess.mono (prod_subset_prod_right (subset_univ centeredCell)))
  let L := Real.toNNReal L₀
  have hL (s : ℝ) (hs : s ∈ Icc 0 T) : LipschitzWith L (fderiv ℝ (U s)) := by
    refine lipschitzWith_of_nnnorm_fderiv_le (fun x => (hH s hs x).differentiableAt) fun x => ?_
    obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell x
    have hShift := fderiv_spatiallyPeriodic (fderiv_spatiallyPeriodic (hper s hs)) n (x - latticeVector n)
    rw [sub_add_cancel, (hH s hs (x - latticeVector n)).fderiv] at hShift
    change ‖fderiv ℝ (fderiv ℝ (U s)) x‖ ≤ (L : ℝ)
    rw [hShift]
    exact (hL₀ (s, x - latticeVector n) ⟨hs, hn⟩).trans (Real.le_coe_toNNReal L₀)
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by norm_num)) hper
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  let B := Real.toNNReal (Real.exp ((K : ℝ) * T))
  have hXLip (s : ℝ) (hs : s ∈ Icc 0 T) : LipschitzWith B (X 0 s) := by
    simpa only [sub_zero, B] using hX.lipschitzWith_labels hK h₀ hs
  let A (s : ℝ) (x : Vec3) := fderiv ℝ (U s) (X 0 s x)
  let J (s : ℝ) (x : Vec3) := fderiv ℝ (X 0 s) x
  let H (s : ℝ) := fderiv ℝ (fderiv ℝ (U s)) (X 0 s a)
  have htraj (x : Vec3) : ContinuousOn (fun s => (s, X 0 s x)) (Icc 0 T) :=
    continuousOn_id.prodMk (HasDerivWithinAt.continuousOn (hX.trajectory 0 h₀ x))
  have hA (x : Vec3) : ContinuousOn (fun s => A s x) (Icc 0 T) :=
    (hgrad.continuousOn.comp (htraj x) (fun s hs => ⟨hs, mem_univ (X 0 s x)⟩)).congr
      (fun s hs => (hD s hs (X 0 s x)).fderiv)
  have hHc : ContinuousOn H (Icc 0 T) :=
    (hhess.comp (htraj a) (fun s hs => ⟨hs, mem_univ (X 0 s a)⟩)).congr
      (fun s hs => (hH s hs (X 0 s a)).fderiv)
  have hJ (x : Vec3) : J 0 x = .id ℝ Vec3 ∧
      ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun d => J d x) ((A s x).comp (J s x)) (Icc 0 T) s :=
    hX.labelDerivative_evolves hT hU hper h₀ x
  have hJoint := hX.continuousOn_labelDerivative_from_left hT hU hper hK hL
  have hJc (s : ℝ) (hs : s ∈ Icc 0 T) : ContinuousAt (J s) a :=
    (continuousOn_univ.mp (hJoint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ => ⟨hs, mem_univ x⟩))).continuousAt
  obtain ⟨W, hW₀, hW, hWt⟩ := linearFundamental_parameterDerivative
    (A := A) (F := J) (DA := fun s => (H s).comp (J s a)) (C := (B : ℝ)) hT.le a hA
    (fun s hs => (hL s hs).comp (hXLip s hs))
    (fun s hs => ((hH s hs (X 0 s a)).comp a
      (hX.differentiableAt_transition hT hU hper h₀ hs a).hasFDerivAt).congr_fderiv
        (congrArg (fun v => v.comp (J s a)) (hH s hs (X 0 s a)).fderiv.symm))
    (hHc.clm_comp (HasDerivWithinAt.continuousOn (hJ a).2))
    (fun x => (hJ x).1) (fun x => (hJ x).2) hJc
    (fun x s hs => norm_fderiv_le_of_lipschitz ℝ (hXLip s hs))
  have heq (s : ℝ) (hs : s ∈ Icc 0 T) : fderiv ℝ (fderiv ℝ (X 0 s)) a = W s :=
    (hW s hs).fderiv
  dsimp only
  refine ⟨(heq 0 h₀).trans hW₀, fun t ht => ⟨?_, ?_⟩⟩
  · rw [heq t ht]
    exact hW t ht
  · intro u v
    have hu := (hWt t ht).clm_apply (hasDerivWithinAt_const t (Icc 0 T) u)
    have huv := hu.clm_apply (hasDerivWithinAt_const t (Icc 0 T) v)
    rw [heq t ht]
    refine (huv.congr_deriv ?_).congr_of_mem ?_ ht
    · simp [A, J, H]
    · intro s hs
      rw [heq s hs]

end TorusEuler
