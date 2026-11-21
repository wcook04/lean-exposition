import TorusEuler.HierarchySourceAssembly
import TorusEuler.HierarchyPhysicalGraph
import TorusEuler.HierarchyTwistedCompletion
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Phase averaging of the actual lattice-twisted sources in (5.25)–(5.28). -/

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Interval Topology

namespace TorusEuler

noncomputable section

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

private abbrev independent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchyTwistedProfile T k E) : Prop :=
  HierarchyPeriodicProfile.PhaseIndependent f.val.val

/-- The coefficient-independent twisted phase average is the actual unit-period integral. -/
theorem average_apply_phaseMean (hT : 0 < T) (G M : MP) (κ f : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    ((twistedHierarchyOperators hT G M κ).average f).val.val.val (t, a, s) =
      phaseMean (fun r => f.val.val.val (t, a, r)) :=
  HierarchySmoothProfile.profilePhaseAverage_apply hT f.val.val ⟨ht, mem_univ _⟩

private theorem phaseMean_eq_zero_of_average_eq_zero (hT : 0 < T) (G M : MP) (κ f : VP)
    (hf : (twistedHierarchyOperators hT G M κ).average f = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    phaseMean (fun r => f.val.val.val (t, a, r)) = 0 := by
  rw [← average_apply_phaseMean hT G M κ f ht a 0, hf]
  rfl

private theorem independent_of_average_eq_self (hT : 0 < T) (G M : MP) (κ f : VP)
    (hf : (twistedHierarchyOperators hT G M κ).average f = f) :
    independent f := by
  have heq := congrArg Subtype.val
    (hf : (twistedHierarchyOperators hT G M κ).average f = f)
  exact HierarchyPeriodicProfile.phaseIndependent_of_profilePhaseAverage_eq_self hT f.val heq

private theorem average_eq_self_of_independent (hT : 0 < T) (G M : MP) (κ f : VP)
    (hf : independent f) :
    (twistedHierarchyOperators hT G M κ).average f = f :=
  Subtype.ext (HierarchyPeriodicProfile.profilePhaseAverage_eq_self_of_independent hT f.val hf)

private theorem continuous_phaseSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchyTwistedProfile T k E) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    Continuous (fun r => f.val.val.val (t, a, r)) :=
  (HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val ht).continuous.comp
    (continuous_const.prodMk continuous_id)

private theorem labelSlot_deriv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchySmoothProfile T E) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) (v : Vec3) :
    fderivWithin ℝ f.val (hierarchyProfileSlab T) (t, a, s) (0, v, 0) =
      fderiv ℝ (fun b => f.val (t, b, s)) a v := by
  let I := (ContinuousLinearMap.inr ℝ ℝ (Vec3 × ℝ)).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)
  have hI : HasFDerivAt (fun b : Vec3 => (t, b, s)) I a :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (a, s)).comp a
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) a s)
  have hD := ((HierarchySmoothProfile.smooth f).differentiableOn (by simp) (t, a, s)
    ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hm : ∀ᶠ b : Vec3 in 𝓝 a, (t, b, s) ∈ hierarchyProfileSlab T :=
    Eventually.of_forall fun _ => ⟨ht, mem_univ _⟩
  exact (congrArg (fun D : Vec3 →L[ℝ] E => D v) (hD.comp_hasFDerivAt a hI hm).fderiv).symm

/-- The slow advection uses the actual label derivative and the coframe. -/
theorem labelAdv_apply_label_fderiv (hT : 0 < T) (G M : MP) (κ f g : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    ((twistedHierarchyOperators hT G M κ).labelAdv f g).val.val.val (t, a, s) =
      fderiv ℝ (fun b => g.val.val.val (t, b, s)) a
        (G.val.val.val (t, a, s) (f.val.val.val (t, a, s))) := by
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.labelDirections G.val.val)
    f.val.val g.val.val).val (t, a, s) = _
  rw [HierarchySmoothProfile.advect_apply hT _ _ _ hx,
    HierarchySmoothProfile.labelDirections_apply G.val.val f.val.val hx]
  exact labelSlot_deriv_eq g.val.val ht a s _

private theorem label_fderiv_phase_eq_of_independent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : HierarchyTwistedProfile T k E} (hf : independent f)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    fderiv ℝ (fun b => f.val.val.val (t, b, s)) a =
      fderiv ℝ (fun b => f.val.val.val (t, b, 0)) a :=
  congrArg (fun g : Vec3 → E => fderiv ℝ g a)
    (funext fun b => hf (t, b, 0) ⟨ht, mem_univ _⟩ s)

private theorem phaseMean_labelFDeriv_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : HierarchyTwistedProfile T k E)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hf : ∀ a, phaseMean (fun r => f.val.val.val (t, a, r)) = 0) (a : Vec3) :
    phaseMean (fun r => fderiv ℝ (fun b => f.val.val.val (t, b, r)) a) = 0 := by
  rw [← fderiv_phaseMean_eq_phaseMean_fderiv
    (f := fun b r => f.val.val.val (t, b, r))
    (HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val ht) a,
    show (fun b => phaseMean (fun r => f.val.val.val (t, b, r))) = fun _ => 0 from funext hf]
  simp

private theorem continuous_phaseLabelFDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : HierarchyTwistedProfile T k E) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) :
    Continuous (fun s => fderiv ℝ (fun b => f.val.val.val (t, b, s)) a) := by

  let H : Vec3 × ℝ → E := fun bs => f.val.val.val (t, bs)
  have hH : ContDiff ℝ ∞ H := HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val ht
  let I := ContinuousLinearMap.inl ℝ Vec3 ℝ
  let L : ((Vec3 × ℝ) →L[ℝ] E) →L[ℝ] (Vec3 →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ Vec3 (Vec3 × ℝ) E).flip I
  have heq (s : ℝ) :
      fderiv ℝ (fun b => f.val.val.val (t, b, s)) a = L (fderiv ℝ H (a, s)) := by
    have hD : HasFDerivAt H (fderiv ℝ H (a, s)) (a, s) :=
      (hH.differentiable (by simp) (a, s)).hasFDerivAt
    change fderiv ℝ (H ∘ fun b => (b, s)) a = (fderiv ℝ H (a, s)).comp I
    exact (hD.comp a (hasFDerivAt_prodMk_left (𝕜 := ℝ) a s)).fderiv
  simp_rw [heq]
  exact L.continuous.comp ((hH.continuous_fderiv (by simp)).comp
    (continuous_const.prodMk continuous_id))

/-- The slow advection of a phase-independent profile by a centered profile is centered. -/
theorem average_labelAdv_centered_independent (hT : 0 < T) (G M : MP) (κ Y B : VP)
    (hG : independent G)
    (hY : (twistedHierarchyOperators hT G M κ).average Y = 0)
    (hB : (twistedHierarchyOperators hT G M κ).average B = B) :
    (twistedHierarchyOperators hT G M κ).average
      ((twistedHierarchyOperators hT G M κ).labelAdv Y B) = 0 := by
  have hBind := independent_of_average_eq_self hT G M κ B hB
  apply ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  rw [average_apply_phaseMean hT G M κ _ ht a s]
  let L := (fderiv ℝ (fun b => B.val.val.val (t, b, 0)) a).comp (G.val.val.val (t, a, 0))
  have hs (r : ℝ) :
      ((twistedHierarchyOperators hT G M κ).labelAdv Y B).val.val.val (t, a, r) =
        L (Y.val.val.val (t, a, r)) := by
    rw [labelAdv_apply_label_fderiv hT G M κ Y B ht a r,
      label_fderiv_phase_eq_of_independent hBind ht a r, hG (t, a, 0) ⟨ht, mem_univ _⟩ r]
    rfl
  rw [funext hs]
  exact hierarchy_phaseMean_apply_eq_zero L (continuous_phaseSlice Y ht a)
    (phaseMean_eq_zero_of_average_eq_zero hT G M κ Y hY ht a)

/-- A phase-independent advector preserves phase centering under slow advection. -/
theorem average_labelAdv_independent_centered (hT : 0 < T) (G M : MP) (κ B Y : VP)
    (hG : independent G)
    (hB : (twistedHierarchyOperators hT G M κ).average B = B)
    (hY : (twistedHierarchyOperators hT G M κ).average Y = 0) :
    (twistedHierarchyOperators hT G M κ).average
      ((twistedHierarchyOperators hT G M κ).labelAdv B Y) = 0 := by
  have hBind := independent_of_average_eq_self hT G M κ B hB
  apply ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  rw [average_apply_phaseMean hT G M κ _ ht a s]
  let v := G.val.val.val (t, a, 0) (B.val.val.val (t, a, 0))
  let L : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 := ContinuousLinearMap.apply ℝ Vec3 v
  have hs (r : ℝ) :
      ((twistedHierarchyOperators hT G M κ).labelAdv B Y).val.val.val (t, a, r) =
        L (fderiv ℝ (fun b => Y.val.val.val (t, b, r)) a) := by
    rw [labelAdv_apply_label_fderiv hT G M κ B Y ht a r,
      hG (t, a, 0) ⟨ht, mem_univ _⟩ r, hBind (t, a, 0) ⟨ht, mem_univ _⟩ r]
    rfl
  rw [funext hs]
  exact hierarchy_phaseMean_apply_eq_zero L (continuous_phaseLabelFDeriv Y ht a)
    (phaseMean_labelFDeriv_eq_zero Y ht
      (fun b => phaseMean_eq_zero_of_average_eq_zero hT G M κ Y hY ht b) a)

/-- The product of two phase-independent means under slow advection is phase independent. -/
theorem average_labelAdv_independent_independent (hT : 0 < T) (G M : MP) (κ B D : VP)
    (hG : independent G)
    (hB : (twistedHierarchyOperators hT G M κ).average B = B)
    (hD : (twistedHierarchyOperators hT G M κ).average D = D) :
    (twistedHierarchyOperators hT G M κ).average
      ((twistedHierarchyOperators hT G M κ).labelAdv B D) =
      (twistedHierarchyOperators hT G M κ).labelAdv B D := by
  have hBind := independent_of_average_eq_self hT G M κ B hB
  have hDind := independent_of_average_eq_self hT G M κ D hD
  apply average_eq_self_of_independent hT G M κ
  rintro ⟨t, a, s⟩ hx r
  have ht : t ∈ Icc 0 T := hx.1
  simp only [labelAdv_apply_label_fderiv hT G M κ B D ht,
    label_fderiv_phase_eq_of_independent hDind ht a,
    hG (t, a, 0) ⟨ht, mem_univ _⟩, hBind (t, a, 0) ⟨ht, mem_univ _⟩]

private theorem timeSlot_hasDerivWithinAt (f : HierarchySmoothProfile T Vec3)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt (fun r => f.val (r, a, s))
      (fderivWithin ℝ f.val (hierarchyProfileSlab T) (t, a, s) (1, 0, 0)) (Icc 0 T) t := by
  have hD := ((HierarchySmoothProfile.smooth f).differentiableOn (by simp) (t, a, s)
    ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hm : MapsTo (fun r : ℝ => (r, a, s)) (Icc 0 T) (hierarchyProfileSlab T) :=
    fun _ hr => ⟨hr, mem_univ _⟩
  exact (hD.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t (a, s)).hasFDerivWithinAt
    hm).hasDerivWithinAt

private theorem phaseMean_timeSlot_eq_zero (hT : 0 < T) (f : VP)
    (hf : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun r => f.val.val.val (t, a, r)) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    phaseMean (fun r =>
      fderivWithin ℝ f.val.val.val (hierarchyProfileSlab T) (t, a, r) (1, 0, 0)) = 0 := by
  let D := HierarchySmoothProfile.derivativeAlong hT
    (HierarchySmoothProfile.constant (1, 0, 0)) f.val.val
  let F (u s : ℝ) := f.val.val.val (u, a, s)
  let F' (u s : ℝ) := D.val (u, a, s)
  have hD (u : ℝ) (hu : u ∈ Icc 0 T) (s : ℝ) :
      F' u s = fderivWithin ℝ f.val.val.val (hierarchyProfileSlab T) (u, a, s) (1, 0, 0) := by
    have hx : (u, a, s) ∈ hierarchyProfileSlab T := ⟨hu, mem_univ _⟩
    simp only [F', D, HierarchySmoothProfile.derivativeAlong_apply _ _ _ hx,
      HierarchySmoothProfile.constant_apply _ hx]
  have hF' (u : ℝ) (hu : u ∈ Icc 0 T) : Continuous (F' u) :=
    ((HierarchySmoothProfile.smooth D).continuousOn.comp_continuous
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)) (fun _ => ⟨hu, mem_univ _⟩))
  have hcont : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Icc 0 T ×ˢ Icc 0 1) :=
    (HierarchySmoothProfile.smooth D).continuousOn.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  have hz : EqOn (fun u => phaseMean (F' u)) (fun _ => 0) (Ioo 0 T) := by
    intro u hu
    have hn : Ioo 0 T ∈ 𝓝 u := isOpen_Ioo.mem_nhds hu
    have hC : u ∈ Icc 0 T := Ioo_subset_Icc_self hu
    have hmeanD := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (a := 0) (b := 1) (μ := volume) (F := F) (F' := F') (bound := fun _ => K)
      hn (mem_of_superset hn fun r hr =>
        (continuous_phaseSlice f (Ioo_subset_Icc_self hr) a).aestronglyMeasurable)
      ((continuous_phaseSlice f hC a).intervalIntegrable 0 1)
      ((hF' u hC).aestronglyMeasurable)
      (Eventually.of_forall fun s hs r hr => hK (r, s)
        ⟨Ioo_subset_Icc_self hr, by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc hs⟩)
      (continuous_const.intervalIntegrable 0 1)
      (Eventually.of_forall fun s _ r hr => by
        rw [hD r (Ioo_subset_Icc_self hr)]
        exact (timeSlot_hasDerivWithinAt f.val.val (Ioo_subset_Icc_self hr) a s).hasDerivAt
          (mem_of_superset (isOpen_Ioo.mem_nhds hr) Ioo_subset_Icc_self))).2
    have heq : (fun r => phaseMean (F r)) =ᶠ[𝓝 u] fun _ => 0 :=
      mem_of_superset hn fun r hr => hf r (Ioo_subset_Icc_self hr) a
    change HasDerivAt (fun r => phaseMean (F r)) (phaseMean (F' u)) u at hmeanD
    change phaseMean (F' u) = 0
    rw [← hmeanD.deriv, heq.deriv_eq, deriv_const]
  have hmeanContinuous : ContinuousOn (fun u => phaseMean (F' u)) (Icc 0 T) := by
    refine ((HierarchySmoothProfile.smooth
      (HierarchySmoothProfile.profilePhaseAverage hT D)).continuousOn.comp
      (continuous_id.prodMk (continuous_const (y := (a, (0 : ℝ))))).continuousOn
      (fun u hu => ⟨hu, mem_univ _⟩)).congr ?_
    intro u hu
    have hx : (u, a, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨hu, mem_univ _⟩
    exact (HierarchySmoothProfile.profilePhaseAverage_apply hT D hx).symm
  have hclosed := hz.of_subset_closure hmeanContinuous continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (ne_of_lt hT)])
  rw [← show F' t = _ from funext (hD t ht)]
  exact hclosed ht

/-- The label-coordinate material relay preserves the unit-period phase mean zero. -/
theorem average_material_centered (hT : 0 < T) (G M : MP) (κ f : VP)
    (hM : independent M)
    (hf : (twistedHierarchyOperators hT G M κ).average f = 0) :
    (twistedHierarchyOperators hT G M κ).average
      ((twistedHierarchyOperators hT G M κ).material f) = 0 := by
  apply ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  let J (r : ℝ) :=
    fderivWithin ℝ f.val.val.val (hierarchyProfileSlab T) (t, a, r) (1, 0, 0)
  let L := M.val.val.val (t, a, 0)
  have hs (r : ℝ) :
      ((twistedHierarchyOperators hT G M κ).material f).val.val.val (t, a, r) =
        J r + L (f.val.val.val (t, a, r)) := by
    change ((HierarchySmoothProfile.hierarchyConcreteOperators hT G.val.val M.val.val
      κ.val.val).material f.val.val).val (t, a, r) = _
    rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT _ _ _ _
      ⟨ht, mem_univ _⟩, hM (t, a, 0) ⟨ht, mem_univ _⟩ r]
  have hJ : Continuous J :=
    (((HierarchySmoothProfile.smooth f.val.val).continuousOn_fderivWithin
      (uniqueDiffOn_hierarchyProfileSlab hT) (by simp)).comp_continuous
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      (fun _ => ⟨ht, mem_univ _⟩)).clm_apply continuous_const
  have hL : Continuous (fun r => L (f.val.val.val (t, a, r))) :=
    L.continuous.comp (continuous_phaseSlice f ht a)
  rw [average_apply_phaseMean hT G M κ _ ht a s, funext hs, phaseMean_add hJ hL,
    phaseMean_timeSlot_eq_zero hT f
      (fun u hu b => phaseMean_eq_zero_of_average_eq_zero hT G M κ f hf hu b) ht a,
    hierarchy_phaseMean_apply_eq_zero L (continuous_phaseSlice f ht a)
      (phaseMean_eq_zero_of_average_eq_zero hT G M κ f hf ht a),
    zero_add]
  rfl

/-- The slow pressure-gradient term is centered when its scalar pressure is normalized. -/
theorem average_labelGrad_of_phaseMean_zero (hT : 0 < T) (G M : MP) (κ : VP) (q : SP)
    (hG : independent G)
    (hq : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun r => q.val.val.val (t, a, r)) = 0) :
    (twistedHierarchyOperators hT G M κ).average
      ((twistedHierarchyOperators hT G M κ).labelGrad q) = 0 := by
  apply ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  let L : (Vec3 →L[ℝ] ℝ) →L[ℝ] Vec3 :=
    ∑ i : Fin 3, (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i 1)).comp
      (ContinuousLinearMap.apply ℝ ℝ (G.val.val.val (t, a, 0) (EuclideanSpace.single i 1)))
  let J (r : ℝ) := fderiv ℝ (fun b => q.val.val.val (t, b, r)) a
  have hs (r : ℝ) :
      ((twistedHierarchyOperators hT G M κ).labelGrad q).val.val.val (t, a, r) = L (J r) := by
    change (HierarchySmoothProfile.labelGradient hT G.val.val q.val.val).val (t, a, r) = _
    rw [HierarchySmoothProfile.labelGradient_apply hT G.val.val q.val.val ⟨ht, mem_univ _⟩]
    simp only [L, J, _root_.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.toSpanSingleton_apply,
      labelSlot_deriv_eq q.val.val ht a r, hG (t, a, 0) ⟨ht, mem_univ _⟩ r]
    rfl
  rw [average_apply_phaseMean hT G M κ _ ht a s, funext hs]
  exact hierarchy_phaseMean_apply_eq_zero L (continuous_phaseLabelFDeriv q ht a)
    (phaseMean_labelFDeriv_eq_zero q ht (hq t ht) a)

/-- Multiplying a centered completion by a scalar depending on time preserves centering. -/
theorem average_eq_zero_of_timeScalar_mul (hT : 0 < T) (G M : MP) (κ C D : VP)
    (hC : (twistedHierarchyOperators hT G M κ).average C = 0) (w : ℝ → ℝ)
    (hD : ∀ t ∈ Icc 0 T, ∀ a s, D.val.val.val (t, a, s) = w t • C.val.val.val (t, a, s)) :
    (twistedHierarchyOperators hT G M κ).average D = 0 := by
  apply ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  rw [average_apply_phaseMean hT G M κ D ht a s, funext (hD t ht a),
    phaseMean_const_smul, phaseMean_eq_zero_of_average_eq_zero hT G M κ C hC ht a, smul_zero]
  rfl

local notation "slowDiv" => HierarchySmoothProfile.profileLabelDivergence

set_option maxHeartbeats 800000 in
/-- The slow Eulerian divergence of a lattice-twisted vector profile, with the
fast phase held fixed. -/
def slowLabelDivergence (hT : 0 < T) (G : MP) (V : VP) : SP := by
  let d := slowDiv hT G.val.val V.val.val
  let q := HierarchyPeriodicProfile.ofPeriodicSlices d (fun t ht a s => by
    change d.val (t, a, s + 1) = d.val (t, a, s)
    have hV : (fun b => V.val.val.val (t, b, s + 1)) = (fun b => V.val.val.val (t, b, s)) :=
      funext fun b => HierarchyPeriodicProfile.phasePeriodic V.val t b s
    have hG : G.val.val.val (t, a, s + 1) = G.val.val.val (t, a, s) :=
      HierarchyPeriodicProfile.phasePeriodic G.val t a s
    simp only [d, HierarchySmoothProfile.profileLabelDivergence_apply hT G.val.val V.val.val ht]
    rw [hV, hG])
  refine ofTwistedSlices q ?_
  intro t ht a s n
  change d.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = d.val (t, a, s)
  let f (b : Vec3) := V.val.val.val (t, b, s + ⟪k, latticeVector n⟫_ℝ)
  have hV : (fun b => f (b + latticeVector n)) = (fun b => V.val.val.val (t, b, s)) :=
    funext fun b => twistedSlice V t b s n
  have hD : fderiv ℝ f (a + latticeVector n) =
      fderiv ℝ (fun b => V.val.val.val (t, b, s)) a := by
    rw [← fderiv_comp_add_right, hV]
  simp only [d, HierarchySmoothProfile.profileLabelDivergence_apply hT G.val.val V.val.val ht]
  rw [show (fun b => V.val.val.val (t, b, s + ⟪k, latticeVector n⟫_ℝ)) = f from rfl,
    hD, twistedSlice G t a s n]

@[simp] theorem slowLabelDivergence_val_val (hT : 0 < T) (G : MP) (V : VP) :
    (slowLabelDivergence hT G V).val.val = slowDiv hT G.val.val V.val.val := rfl

/-- The slow divergence times a second vector profile in the averaged
completion source. -/
def slowLabelDivergenceProduct (hT : 0 < T) (G : MP) (V Y : VP) : VP :=
  applyField (map (smulRightL ℝ ℝ Vec3 (ContinuousLinearMap.id ℝ ℝ)) Y)
    (slowLabelDivergence hT G V)

theorem slowLabelDivergenceProduct_apply (hT : 0 < T) (G : MP) (V Y : VP)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (slowLabelDivergenceProduct hT G V Y).val.val.val x =
      (slowDiv hT G.val.val V.val.val).val x • Y.val.val.val x := by
  simp only [slowLabelDivergenceProduct, applyField_val, HierarchyPeriodicProfile.applyField_val,
    HierarchySmoothProfile.applyField_eval _ _ hx, map_val, HierarchyPeriodicProfile.map_val,
    HierarchySmoothProfile.map_apply _ _ hx, slowLabelDivergence_val_val]
  rfl

private theorem completionAvg_continuous_phase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchySmoothProfile T E) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    Continuous (fun s => f.val (t, a, s)) :=
  (HierarchySmoothProfile.smooth f).continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_const.prodMk continuous_id)) (fun _ => ⟨ht, mem_univ _⟩)

private theorem completionAvg_phaseAdv_apply (hT : 0 < T) (G M : MP) (κ C Y : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    ((twistedHierarchyOperators hT G M κ).phaseAdv C Y).val.val.val (t, a, s) =
      ⟪κ.val.val.val (t, a, s), C.val.val.val (t, a, s)⟫_ℝ •
        fderivWithin ℝ Y.val.val.val (hierarchyProfileSlab T) (t, a, s) (0, 0, 1) := by
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.phaseDirections κ.val.val)
      C.val.val Y.val.val).val (t, a, s) = _
  rw [HierarchySmoothProfile.advect_apply hT _ _ _ hx,
    HierarchySmoothProfile.phaseDirections_apply κ.val.val C.val.val hx]
  rw [show ((0, 0, ⟪κ.val.val.val (t, a, s), C.val.val.val (t, a, s)⟫_ℝ) :
    HierarchyProfilePoint) =
      ⟪κ.val.val.val (t, a, s), C.val.val.val (t, a, s)⟫_ℝ • (0, 0, 1) by simp, map_smul]

set_option maxHeartbeats 1000000 in
/-- The averaged fast completion interaction is exactly the averaged slow
divergence product, using the physical longitudinal derivative and the
mean-zero periodic completion. -/
theorem average_phaseAdv_complete (hT : 0 < T) (G M : MP) (κ : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    {A : Velocity}
    (hA : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (A t))
    (hsurj : ∀ t ∈ Icc 0 T, Function.Surjective (A t))
    (hG : ∀ t ∈ Icc 0 T, ∀ y s, G.val.val.val (t, A t y, s) = fderiv ℝ (A t) y)
    (hκflow : ∀ t ∈ Icc 0 T, ∀ y, κ.val.val.val (t, A t y, 0) = (fderiv ℝ (A t) y).adjoint k)
    (V Y : VP) (hVmean : profilePhaseAverage hT V = 0)
    (htrans : ∀ t ∈ Icc 0 T, ∀ a s, ⟪κ.val.val.val (t, a, 0), V.val.val.val (t, a, s)⟫_ℝ = 0) :
    let ops := twistedHierarchyOperators hT G M κ
    ops.average (ops.phaseAdv (complete hT G κ hκPhase hκ V) Y) =
      ops.average (slowLabelDivergenceProduct hT G V Y) := by
  let C := complete hT G κ hκPhase hκ V
  let ops := twistedHierarchyOperators hT G M κ
  have hCmean := average_complete hT G M κ hGPhase hκPhase hκ V
  have hCs := complete_val_val_of_phaseMean_zero hT G κ hκPhase hκ V hVmean
  apply ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  obtain ⟨x, rfl⟩ := hsurj t ht a
  let d := slowDiv hT G.val.val V.val.val
  let Ys (r : ℝ) := fderivWithin ℝ Y.val.val.val (hierarchyProfileSlab T) (t, A t x, r) (0, 0, 1)
  have hκsame (r : ℝ) : κ.val.val.val (t, A t x, r) = κ.val.val.val (t, A t x, 0) :=
    hκPhase (t, A t x, 0) ⟨ht, mem_univ _⟩ r
  have hC₀ : phaseMean (fun r => C.val.val.val (t, A t x, r)) = 0 := by
    have h := congrArg (fun f : VP => f.val.val.val (t, A t x, 0)) hCmean
    change (HierarchySmoothProfile.profilePhaseAverage hT C.val.val).val (t, A t x, 0) = 0 at h
    rwa [HierarchySmoothProfile.profilePhaseAverage_apply hT _ ⟨ht, mem_univ _⟩] at h
  have hYs : Continuous Ys :=
    (((HierarchySmoothProfile.smooth Y.val.val).continuousOn_fderivWithin
      (uniqueDiffOn_hierarchyProfileSlab hT) (by simp)).comp_continuous
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      (fun _ => ⟨ht, mem_univ _⟩)).clm_apply continuous_const
  have hLong (r : ℝ) : HasDerivAt
      (fun σ => ⟪κ.val.val.val (t, A t x, 0), C.val.val.val (t, A t x, σ)⟫_ℝ)
      (-d.val (t, A t x, r)) r := by
    change HasDerivAt
      (fun σ => ⟪κ.val.val.val (t, A t x, 0), C.val.val.val (t, A t x, σ)⟫_ℝ)
      (-(slowDiv hT G.val.val V.val.val).val (t, A t x, r)) r
    rw [show C.val.val = (HierarchySmoothProfile.profileCompletion hT G.val.val κ.val.val hκ V.val.val)
      from hCs, HierarchySmoothProfile.profileLabelDivergence_apply hT G.val.val V.val.val ht, hG t ht]
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left] using
      HierarchySmoothProfile.profileCompletion_longitudinal_derivative hT G.val.val κ.val.val
        V.val.val hκ ht (hA t ht) k (hG t ht) (hκflow t ht) (htrans t ht) x r
  change (HierarchySmoothProfile.profilePhaseAverage hT (ops.phaseAdv C Y).val.val).val (t, A t x, s) =
    (HierarchySmoothProfile.profilePhaseAverage hT
      (slowLabelDivergenceProduct hT G V Y).val.val).val (t, A t x, s)
  rw [HierarchySmoothProfile.profilePhaseAverage_apply hT _ hx,
    HierarchySmoothProfile.profilePhaseAverage_apply hT _ hx]
  change phaseMean (fun r => ((twistedHierarchyOperators hT G M κ).phaseAdv C Y).val.val.val
    (t, A t x, r)) = phaseMean (fun r => (slowLabelDivergenceProduct hT G V Y).val.val.val
      (t, A t x, r))
  simp_rw [completionAvg_phaseAdv_apply hT G M κ C Y ht, hκsame]
  have hProd (r : ℝ) : (slowLabelDivergenceProduct hT G V Y).val.val.val (t, A t x, r) =
      d.val (t, A t x, r) • Y.val.val.val (t, A t x, r) :=
    slowLabelDivergenceProduct_apply hT G V Y ⟨ht, mem_univ _⟩
  simp_rw [hProd]
  exact hierarchy_phaseMean_completion (κ.val.val.val (t, A t x, 0))
    (fun r => C.val.val.val (t, A t x, r)) (fun r => Y.val.val.val (t, A t x, r)) Ys
    (fun r => d.val (t, A t x, r)) (completionAvg_continuous_phase C.val.val ht _)
    (HierarchyPeriodicProfile.phasePeriodic C.val t _) hC₀
    (HierarchyPeriodicProfile.phasePeriodic Y.val t _)
    (fun r => HierarchySmoothProfile.hasDerivAt_profilePhase Y.val.val ht _ r) hYs
    (completionAvg_continuous_phase d ht _) hLong

/-- The coframe directions give the coordinate sum of the slow divergence. -/
theorem slowLabelDivergence_apply (hT : 0 < T) (G : MP) (V : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (slowLabelDivergence hT G V).val.val.val (t, a, s) =
      ∑ i : Fin 3, (fderiv ℝ (fun b => V.val.val.val (t, b, s)) a
        (G.val.val.val (t, a, s) (EuclideanSpace.single i 1))) i := by
  rw [slowLabelDivergence_val_val,
    HierarchySmoothProfile.profileLabelDivergence_apply hT G.val.val V.val.val ht,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

/-- Fast advection is the phase derivative times the covector pairing. -/
theorem phaseAdv_apply_phase_fderiv (hT : 0 < T) (G M : MP) (κ C Y : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    ((twistedHierarchyOperators hT G M κ).phaseAdv C Y).val.val.val (t, a, s) =
      ⟪κ.val.val.val (t, a, s), C.val.val.val (t, a, s)⟫_ℝ •
        fderivWithin ℝ Y.val.val.val (hierarchyProfileSlab T) (t, a, s) (0, 0, 1) :=
  completionAvg_phaseAdv_apply hT G M κ C Y ht a s

/-- The equivalent trace contraction by rows puts the label derivative in a
fixed coordinate direction before applying the coframe. -/
theorem slowLabelDivergence_apply_labelRows (hT : 0 < T) (G : MP) (V : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (slowLabelDivergence hT G V).val.val.val (t, a, s) =
      ∑ i : Fin 3, (G.val.val.val (t, a, s)
        (fderiv ℝ (fun b => V.val.val.val (t, b, s)) a (EuclideanSpace.single i 1))) i := by
  rw [slowLabelDivergence_val_val, HierarchySmoothProfile.profileLabelDivergence_apply hT G.val.val V.val.val ht]
  let D := fderiv ℝ (fun b => V.val.val.val (t, b, s)) a
  let F := G.val.val.val (t, a, s)
  change LinearMap.trace ℝ Vec3 (D.toLinearMap.comp F.toLinearMap) = _
  rw [LinearMap.trace_comp_comm', LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [D, F, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]


/-- The retained material, pressure, and activation relay has zero phase mean. -/
theorem average_relayAtLevel_eq_zero (hT : 0 < T) (G M : MP) (κ : VP)
    (hG : independent G) (hM : independent M)
    (u : HierarchyProfiles VP SP) (completionSwitch : VP) (p : ℕ)
    (hC : (twistedHierarchyOperators hT G M κ).average (u.C (p - 1)) = 0)
    (hpressure : ∀ t ∈ Icc 0 T, ∀ a,
      phaseMean (fun r => (u.p (p - 1)).val.val.val (t, a, r)) = 0)
    (hSwitch : (twistedHierarchyOperators hT G M κ).average completionSwitch = 0) :
    let ops := twistedHierarchyOperators hT G M κ
    ops.average (ops.relayAtLevel u completionSwitch p) = 0 := by
  have hm := average_material_centered hT G M κ (u.C (p - 1)) hM hC
  have hp := average_labelGrad_of_phaseMean_zero hT G M κ (u.p (p - 1)) hG hpressure
  have hS : (twistedHierarchyOperators hT G M κ).average
      (if p = 2 then completionSwitch else 0) = 0 := by
    split_ifs
    · exact hSwitch
    · exact map_zero _
  dsimp only
  rw [HierarchyOperators.relayAtLevel, map_sub, map_add, hm, hp, hS, add_zero, sub_zero]

private theorem slowLabelDivergenceProduct_zero_left (hT : 0 < T) (G : MP) (Y : VP) :
    slowLabelDivergenceProduct hT G 0 Y = 0 := by
  apply ext
  rintro ⟨t, a, s⟩ hx
  rw [slowLabelDivergenceProduct_apply hT G _ _ hx]
  change (slowLabelDivergence hT G 0).val.val.val (t, a, s) • Y.val.val.val (t, a, s) = 0
  rw [slowLabelDivergence_apply hT G _ hx.1]
  simp

set_option maxHeartbeats 1000000 in
/-- The actual retained twisted source averages to the three slow interactions
in (5.27). The exact curl completion and transported coframe supply the
integrated-by-parts term. -/
theorem average_sourceBeforeMean_eq_slowProducts (hT : 0 < T) (G M : MP) (κ : VP)
    (hGPhase : independent G) (hMPhase : independent M) (hκPhase : independent κ)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    {A : Velocity}
    (hA : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (A t))
    (hsurj : ∀ t ∈ Icc 0 T, Function.Surjective (A t))
    (hG : ∀ t ∈ Icc 0 T, ∀ y s, G.val.val.val (t, A t y, s) = fderiv ℝ (A t) y)
    (hκflow : ∀ t ∈ Icc 0 T, ∀ y, κ.val.val.val (t, A t y, 0) = (fderiv ℝ (A t) y).adjoint k)
    {P p : ℕ} (hp : p ≤ P) (u : HierarchyProfiles VP SP) (completionSwitch : VP)
    (hV : ∀ i, (twistedHierarchyOperators hT G M κ).average (u.V i) = 0)
    (hB : ∀ i, (twistedHierarchyOperators hT G M κ).average (u.B i) = u.B i)
    (hC : ∀ i, u.C i = complete hT G κ hκPhase hκ (u.V i) ∨ u.V i = 0 ∧ u.C i = 0)
    (htrans : ∀ i t, t ∈ Icc 0 T → ∀ a s, ⟪κ.val.val.val (t, a, 0), (u.V i).val.val.val (t, a, s)⟫_ℝ = 0)
    (hpressure : ∀ t ∈ Icc 0 T, ∀ a,
      phaseMean (fun r => (u.p (p - 1)).val.val.val (t, a, r)) = 0)
    (hSwitch : (twistedHierarchyOperators hT G M κ).average completionSwitch = 0) :
    let ops := twistedHierarchyOperators hT G M κ
    ops.average (ops.sourceBeforeMean u P completionSwitch p) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p,
        (ops.average (ops.labelAdv (u.Y ij.1) (u.Y ij.2)) +
          ops.average (slowLabelDivergenceProduct hT G (u.V ij.1) (u.Y ij.2)) +
          ops.labelAdv (u.B ij.1) (u.B ij.2)) := by
  let ops := twistedHierarchyOperators hT G M κ
  have hCmean (i : ℕ) : ops.average (u.C i) = 0 := by
    rcases hC i with hcomp | ⟨_, hzero⟩
    · rw [hcomp]
      exact average_complete hT G M κ hGPhase hκPhase hκ _
    · rw [hzero, map_zero]
  have hY (i : ℕ) : ops.average (u.Y i) = 0 := by
    simpa only [HierarchyProfiles.Y, map_add, hCmean, add_zero] using hV i
  refine ops.average_sourceBeforeMean_eq u hp completionSwitch
    (fun i j => slowLabelDivergenceProduct hT G (u.V i) (u.Y j))
    (average_relayAtLevel_eq_zero hT G M κ hGPhase hMPhase u completionSwitch p
      (hCmean _) hpressure hSwitch)
    (fun i j => ⟨average_labelAdv_centered_independent hT G M κ _ _ hGPhase (hY i) (hB j),
      average_labelAdv_independent_centered hT G M κ _ _ hGPhase (hB i) (hY j)⟩)
    (fun i j => average_labelAdv_independent_independent hT G M κ _ _ hGPhase (hB i) (hB j)) ?_
  intro i j
  rcases hC i with hcomp | ⟨hv, hc⟩
  · rw [hcomp]
    exact average_phaseAdv_complete hT G M κ hGPhase hκPhase hκ hA hsurj hG hκflow
      (u.V i) (u.Y j) (hV i) (htrans i)
  · rw [hv, hc, slowLabelDivergenceProduct_zero_left, map_zero, LinearMap.zero_apply]

set_option maxHeartbeats 1600000 in
/-- The selected finite hierarchy satisfies the averaged source identity once
its scalar pressure outputs are normalized and its completion is physical. -/
theorem average_construct_sourceBeforeMean_eq_slowProducts (hT : 0 < T) (G M : MP) (κ : VP)
    (hGPhase : independent G) (hMPhase : independent M) (hκPhase : independent κ)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    {A : Velocity}
    (hA : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (A t))
    (hsurj : ∀ t ∈ Icc 0 T, Function.Surjective (A t))
    (hG : ∀ t ∈ Icc 0 T, ∀ y s, G.val.val.val (t, A t y, s) = fderiv ℝ (A t) y)
    (hκflow : ∀ t ∈ Icc 0 T, ∀ y, κ.val.val.val (t, A t y, 0) = (fderiv ℝ (A t) y).adjoint k)
    (S : FiniteHierarchySolvers (twistedHierarchyOperators hT G M κ))
    (hcomplete : ∀ v, S.complete v = complete hT G κ hκPhase hκ v)
    {P p : ℕ} (hP : 1 ≤ P) (hp : p ≤ P) (completionSwitch parentResidual : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    (hLeadingP : ∀ t ∈ Icc 0 T, ∀ a,
      phaseMean (fun r => leading.p.val.val.val (t, a, r)) = 0)
    (hSelectedP : ∀ f hf, ∀ t ∈ Icc 0 T, ∀ a,
      phaseMean (fun r => (S.solveTransverse f hf).val.p.val.val.val (t, a, r)) = 0)
    (hSwitch : (twistedHierarchyOperators hT G M κ).average completionSwitch = 0) :
    let ops := twistedHierarchyOperators hT G M κ
    let u := S.construct P completionSwitch parentResidual hR leading
    ops.average (ops.sourceBeforeMean u P completionSwitch p) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p,
        (ops.average (ops.labelAdv (u.Y ij.1) (u.Y ij.2)) +
          ops.average (slowLabelDivergenceProduct hT G (u.V ij.1) (u.Y ij.2)) +
          ops.labelAdv (u.B ij.1) (u.B ij.2)) := by
  let ops := twistedHierarchyOperators hT G M κ
  let u := S.construct P completionSwitch parentResidual hR leading
  have hosc (i : ℕ) : ops.average (u.V i) = 0 ∧ (∀ v, ops.phaseAdv (u.V i) v = 0) ∧
      (∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun r => (u.p i).val.val.val (t, a, r)) = 0) := by
    by_cases hzero : i = 0 ∨ P < i
    · obtain ⟨hv, _, _, hpressure, _⟩ :=
        S.construct_eq_zero_of_index hP hzero completionSwitch parentResidual hR leading
      change u.V i = 0 at hv
      change u.p i = 0 at hpressure
      rw [hv, hpressure]
      refine ⟨map_zero _, fun v => ?_, fun t ht a => ?_⟩
      · rw [map_zero, LinearMap.zero_apply]
      · exact phaseMean_const (0 : ℝ)
    by_cases hi : i = 1
    · subst i
      obtain ⟨hv, hpressure, _, _⟩ :=
        S.construct_leading P completionSwitch parentResidual hR leading
      change u.V 1 = leading.V at hv
      change u.p 1 = leading.p at hpressure
      rw [hv, hpressure]
      exact ⟨leading.average_V, leading.phaseAdv_V, hLeadingP⟩
    · have hiP : i ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      obtain ⟨hf, hv, hpressure⟩ :=
        S.construct_transverse_selected hiP completionSwitch parentResidual hR leading
      rw [hv, hpressure]
      exact ⟨(S.solveTransverse _ hf).val.average_V, (S.solveTransverse _ hf).val.phaseAdv_V,
        hSelectedP _ hf⟩
  have hC (i : ℕ) : u.C i = complete hT G κ hκPhase hκ (u.V i) ∨ u.V i = 0 ∧ u.C i = 0 := by
    by_cases hzero : i = 0 ∨ P < i
    · obtain ⟨hv, hc, _, _, _⟩ :=
        S.construct_eq_zero_of_index hP hzero completionSwitch parentResidual hR leading
      exact Or.inr ⟨hv, hc⟩
    · have hiP : i ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hc := S.construct_completion hiP completionSwitch parentResidual hR leading
      change u.C i = S.complete (u.V i) at hc
      exact Or.inl (hc.trans (hcomplete _))
  exact average_sourceBeforeMean_eq_slowProducts hT G M κ hGPhase hMPhase hκPhase hκ
    hA hsurj hG hκflow hp u completionSwitch (fun i => (hosc i).1)
    (S.construct_average_B P completionSwitch parentResidual hR leading) hC
    (fun i t ht a s => by
      have h := transverse_of_phaseAdv_eq_zero hT G M κ (u.V i) (hosc i).2.1
        (t, a, s) ⟨ht, mem_univ _⟩
      rwa [hκPhase (t, a, 0) ⟨ht, mem_univ _⟩ s] at h)
    (hosc (p - 1)).2.2 hSwitch

end HierarchyTwistedProfile
end
end TorusEuler
