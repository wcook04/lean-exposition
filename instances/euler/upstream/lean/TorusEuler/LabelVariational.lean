import TorusEuler.LinearFlowExistence
import TorusEuler.TorusLabelFlow

open Asymptotics Filter Set
open scoped NNReal Topology

namespace TorusEuler

private theorem norm_le_gronwallBound_of_hasDerivWithinAt_Icc_left
    {f d : ℝ → Vec3} {l r K δ ε : ℝ}
    (hf : ∀ t ∈ Icc l r, HasDerivWithinAt f (d t) (Icc l r) t)
    (hd : ∀ t ∈ Icc l r, ‖d t‖ ≤ K * ‖f t‖ + ε)
    (h₀ : ‖f l‖ ≤ δ) {t : ℝ} (ht : t ∈ Icc l r) :
    ‖f t‖ ≤ gronwallBound δ K ε (t - l) :=
  norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivWithinAt.continuousOn hf)
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    h₀ (fun t ht => hd t (Ico_subset_Icc_self ht)) t ht

private theorem norm_le_gronwallBound_of_hasDerivWithinAt_Icc
    {f d : ℝ → Vec3} {l r s K δ ε : ℝ} (hs : s ∈ Icc l r)
    (hf : ∀ t ∈ Icc l r, HasDerivWithinAt f (d t) (Icc l r) t)
    (hd : ∀ t ∈ Icc l r, ‖d t‖ ≤ K * ‖f t‖ + ε)
    (h₀ : ‖f s‖ ≤ δ) {t : ℝ} (ht : t ∈ Icc l r) :
    ‖f t‖ ≤ gronwallBound δ K ε |t - s| := by
  rcases le_total s t with hst | hts
  · have hsub : Icc s r ⊆ Icc l r := Icc_subset_Icc_left hs.1
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact norm_le_gronwallBound_of_hasDerivWithinAt_Icc_left
      (fun u hu => (hf u (hsub hu)).mono hsub) (fun u hu => hd u (hsub hu)) h₀ ⟨hst, ht.2⟩
  · have hmap : MapsTo (fun u : ℝ => -u) (Icc (-s) (-l)) (Icc l r) := by
      intro u hu
      exact ⟨le_neg.mp hu.2, (neg_le.mp hu.1).trans hs.2⟩
    have hrev (u : ℝ) (hu : u ∈ Icc (-s) (-l)) :
        HasDerivWithinAt (fun v => f (-v)) (-d (-u)) (Icc (-s) (-l)) u := by
      simpa only [Function.comp_def, neg_one_smul] using
        (hf (-u) (hmap hu)).scomp u (hasDerivWithinAt_neg u _) hmap
    have hnorm (u : ℝ) (hu : u ∈ Icc (-s) (-l)) :
        ‖-d (-u)‖ ≤ K * ‖f (-u)‖ + ε := by
      simpa only [norm_neg] using hd (-u) (hmap hu)
    rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
    have harg : -t - -s = s - t := by ring
    simpa only [neg_neg, harg] using norm_le_gronwallBound_of_hasDerivWithinAt_Icc_left hrev hnorm
      (by simpa only [neg_neg] using h₀) (t := -t) ⟨neg_le_neg hts, neg_le_neg ht.1⟩

variable {U : Velocity} {X : ℝ → Velocity} {l r s t : ℝ} {K : ℝ≥0}

/-- The distance between two trajectories obeys the usual Grönwall bound
in either time direction. -/
theorem IsLabelFlowOn.norm_sub_le (hX : IsLabelFlowOn U X (Icc l r))
    (hLip : ∀ u ∈ Icc l r, LipschitzWith K (U u)) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r)
    (a b : Vec3) :
    ‖X s t a - X s t b‖ ≤ Real.exp (K * |t - s|) * ‖a - b‖ := by
  rw [mul_comm, ← gronwallBound_ε0]
  refine norm_le_gronwallBound_of_hasDerivWithinAt_Icc hs
    (fun u hu => (hX.trajectory s hs a u hu).sub (hX.trajectory s hs b u hu))
    (fun u hu => ?_) (by simp only [Pi.sub_apply, hX.initial s hs, le_refl]) ht
  simpa only [Pi.sub_apply, dist_eq_norm, add_zero] using
    (hLip u hu).dist_le_mul (X s u a) (X s u b)

private theorem abs_time_difference_le (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    |t - s| ≤ r - l :=
  abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩

/-- A single Lipschitz constant in the label variable works over the whole slab. -/
theorem IsLabelFlowOn.lipschitzWith_labels (hX : IsLabelFlowOn U X (Icc l r))
    (hLip : ∀ u ∈ Icc l r, LipschitzWith K (U u)) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    LipschitzWith (Real.toNNReal (Real.exp (K * (r - l)))) (X s t) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le]
  exact (hX.norm_sub_le hLip hs ht a b).trans <|
    mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_time_difference_le hs ht) K.coe_nonneg))
      (norm_nonneg _)

/-- For a fixed starting time the flow is jointly continuous in time and label. -/
theorem IsLabelFlowOn.continuousOn_time_label (hX : IsLabelFlowOn U X (Icc l r))
    (hLip : ∀ u ∈ Icc l r, LipschitzWith K (U u)) (hs : s ∈ Icc l r) :
    ContinuousOn (Function.uncurry (X s)) (Icc l r ×ˢ (univ : Set Vec3)) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith'
    _ (Real.toNNReal (Real.exp (K * (r - l))))
    (fun _ ht => (hX.lipschitzWith_labels hLip hs ht).lipschitzOnWith)
    (fun a _ => HasDerivWithinAt.continuousOn (hX.trajectory s hs a))

private theorem norm_taylor_remainder_le {f : Vec3 → Vec3} (hf : Differentiable ℝ f)
    {L : ℝ≥0} (hLip : LipschitzWith L (fderiv ℝ f)) (x y : Vec3) :
    ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ (L : ℝ) * ‖y - x‖ ^ 2 := by
  rw [pow_two, ← mul_assoc]
  refine (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf z) (fun z hz => ?_) (Metric.mem_closedBall_self (norm_nonneg _))
    (by simp only [Metric.mem_closedBall, dist_eq_norm, le_refl])
  exact (by simpa only [dist_eq_norm] using hLip.dist_le_mul z x :
    ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ (L : ℝ) * ‖z - x‖).trans
    (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
      L.coe_nonneg)

private theorem gronwallBound_zero_initial_mul (K ε c t : ℝ) :
    gronwallBound 0 K (ε * c) t = gronwallBound 0 K ε t * c := by
  by_cases hK : K = 0 <;> simp only [gronwallBound, hK, ↓reduceIte, zero_mul, zero_add] <;> ring

/-- The variational matrix is the Fréchet derivative of the flow in the starting
label, when the field has a uniformly Lipschitz spatial derivative continuous along
the reference trajectory. The time equation holds within the entire closed slab. -/
theorem IsLabelFlowOn.exists_variationalSolution (hX : IsLabelFlowOn U X (Icc l r))
    (hLip : ∀ u ∈ Icc l r, LipschitzWith K (U u)) (hs : s ∈ Icc l r) (a : Vec3)
    (hU : ∀ u ∈ Icc l r, Differentiable ℝ (U u))
    {L : ℝ≥0} (hDlip : ∀ u ∈ Icc l r, LipschitzWith L (fderiv ℝ (U u)))
    (hDcont : ContinuousOn (fun u => fderiv ℝ (U u) (X s u a)) (Icc l r)) :
    ∃ F : ℝ → Vec3 →L[ℝ] Vec3, F s = ContinuousLinearMap.id ℝ Vec3 ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt F
        ((fderiv ℝ (U t) (X s t a)).comp (F t)) (Icc l r) t) ∧
      ∀ t ∈ Icc l r, HasFDerivAt (X s t) (F t) a := by
  let D (u : ℝ) : Vec3 →L[ℝ] Vec3 := fderiv ℝ (U u) (X s u a)
  let A (u : ℝ) := ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3 (D u)
  have hA : ContinuousOn A (Icc l r) :=
    (ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3).continuous.comp_continuousOn hDcont
  obtain ⟨F, hFs, hFlinear⟩ := linearODE_exists_Icc_of_mem hs hA
    (ContinuousLinearMap.id ℝ Vec3)
  have hF (u : ℝ) (hu : u ∈ Icc l r) :
      HasDerivWithinAt F ((D u).comp (F u)) (Icc l r) u := hFlinear u hu
  refine ⟨F, hFs, hF, fun t ht => ?_⟩
  let B := Real.exp ((K : ℝ) * (r - l))
  let C := (L : ℝ) * B ^ 2
  let P := gronwallBound 0 K C |t - s|
  have hErr (h : Vec3) :
      ‖X s t (a + h) - X s t a - F t h‖ ≤ P * ‖h‖ ^ 2 := by
    let Δ (u : ℝ) := X s u (a + h) - X s u a
    let err (u : ℝ) := Δ u - F u h
    let dErr (u : ℝ) :=
      (D u) (err u) + (U u (X s u (a + h)) - U u (X s u a) - D u (Δ u))
    have hDeriv (u : ℝ) (hu : u ∈ Icc l r) : HasDerivWithinAt err (dErr u) (Icc l r) u := by
      have hΔ := (hX.trajectory s hs (a + h) u hu).sub (hX.trajectory s hs a u hu)
      have hFh : HasDerivWithinAt (fun v => F v h) (D u (F u h)) (Icc l r) u := by
        simpa using (hF u hu).clm_apply (hasDerivWithinAt_const u (Icc l r) h)
      refine (hΔ.sub hFh).congr_deriv ?_
      simp only [err, dErr, map_sub]
      abel
    have hInitial : ‖err s‖ ≤ 0 := by
      simp [err, Δ, hX.initial s hs, hFs]
    have hNorm (u : ℝ) (hu : u ∈ Icc l r) : ‖dErr u‖ ≤ (K : ℝ) * ‖err u‖ + C * ‖h‖ ^ 2 := by
      have hΔ : ‖Δ u‖ ≤ B * ‖h‖ := by
        simpa only [Δ, dist_eq_norm, add_sub_cancel_left, Real.coe_toNNReal _ (Real.exp_pos _).le, B]
          using (hX.lipschitzWith_labels hLip hs hu).dist_le_mul (a + h) a
      have hD : ‖D u‖ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hLip u hu)
      have hR := norm_taylor_remainder_le (hU u hu) (hDlip u hu) (X s u a) (X s u (a + h))
      calc
        ‖dErr u‖ ≤ ‖D u (err u)‖ + (L : ℝ) * ‖Δ u‖ ^ 2 :=
          (norm_add_le _ _).trans (add_le_add (le_refl _) hR)
        _ ≤ (K : ℝ) * ‖err u‖ + (L : ℝ) * (B * ‖h‖) ^ 2 :=
          add_le_add (((D u).le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hΔ 2) L.coe_nonneg)
        _ = _ := by rw [mul_pow, mul_assoc]
    have hb := norm_le_gronwallBound_of_hasDerivWithinAt_Icc hs hDeriv hNorm hInitial ht
    rw [gronwallBound_zero_initial_mul] at hb
    exact hb
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  have hcont : Continuous (fun h : Vec3 => P * ‖h‖) := by fun_prop
  have hP : Tendsto (fun h : Vec3 => P * ‖h‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using (hcont.continuousAt (x := (0 : Vec3))).tendsto
  filter_upwards [hP (Iio_mem_nhds hc)] with h hh
  exact (hErr h).trans <| calc
    P * ‖h‖ ^ 2 = (P * ‖h‖) * ‖h‖ := by ring
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right (mem_Iio.mp hh).le (norm_nonneg _)

private theorem hasFDerivAt_labelSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : ℝ × Vec3 → E} (hV : DifferentiableOn ℝ V (Icc l r ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc l r) (a : Vec3) :
    HasFDerivAt (fun x => V (t, x))
      ((fderivWithin ℝ V (Icc l r ×ˢ (univ : Set Vec3)) (t, a)).comp
        (ContinuousLinearMap.inr ℝ ℝ Vec3)) a :=
  (hV (t, a) ⟨ht, mem_univ _⟩).hasFDerivWithinAt.comp_hasFDerivAt a
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t a) (Eventually.of_forall fun x => ⟨ht, mem_univ x⟩)

private theorem fderiv_add_latticeVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Vec3 → E} (hV : ∀ n b, V (b + latticeVector n) = V b)
    (n : Fin 3 → ℤ) (a : Vec3) :
    fderiv ℝ V (a + latticeVector n) = fderiv ℝ V a := by
  have h := congrArg (fun v => fderiv ℝ v a) (funext (hV n))
  rwa [fderiv_comp_add_right] at h

/-- A jointly twice continuously differentiable periodic velocity supplies the
hypotheses of the label variational equation on the closed slab. -/
theorem IsLabelFlowOn.exists_variationalSolution_of_contDiffOn_periodic
    (hX : IsLabelFlowOn U X (Icc l r)) (hlr : l < r)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hperiodic : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u)) (hs : s ∈ Icc l r) (a : Vec3) :
    ∃ F : ℝ → Vec3 →L[ℝ] Vec3, F s = ContinuousLinearMap.id ℝ Vec3 ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt F
        ((fderiv ℝ (U t) (X s t a)).comp (F t)) (Icc l r) t) ∧
      ∀ t ∈ Icc l r, HasFDerivAt (X s t) (F t) a := by
  let S := Icc l r ×ˢ (univ : Set Vec3)
  let inr := ContinuousLinearMap.inr ℝ ℝ Vec3
  let D (q : ℝ × Vec3) := (fderivWithin ℝ (Function.uncurry U) S q).comp inr
  let H (q : ℝ × Vec3) := (fderivWithin ℝ D S q).comp inr
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hlr).prod uniqueDiffOn_univ
  have hD : ContDiffOn ℝ 1 D S :=
    (hU.fderivWithin hS (m := 1) (by norm_num)).clm_comp contDiffOn_const
  have hH : ContinuousOn H S :=
    (hD.continuousOn_fderivWithin hS le_rfl).clm_comp continuousOn_const
  have hGrad (u : ℝ) (hu : u ∈ Icc l r) (x : Vec3) : HasFDerivAt (U u) (D (u, x)) x :=
    hasFDerivAt_labelSlice (hU.differentiableOn (by norm_num)) hu x
  have hHess (u : ℝ) (hu : u ∈ Icc l r) (x : Vec3) :
      HasFDerivAt (fderiv ℝ (U u)) (H (u, x)) x :=
    (hasFDerivAt_labelSlice hD.differentiableOn_one hu x).congr_of_eventuallyEq
      (Eventually.of_forall fun y => (hGrad u hu y).fderiv)
  have hc : IsCompact (Icc l r ×ˢ centeredCell) := isCompact_Icc.prod isCompact_centeredCell
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (f := H)
    (hH.mono (prod_subset_prod_right (subset_univ _)))
  have hDLip (u : ℝ) (hu : u ∈ Icc l r) :
      LipschitzWith (Real.toNNReal C) (fderiv ℝ (U u)) := by
    refine lipschitzWith_of_nnnorm_fderiv_le (fun x => (hHess u hu x).differentiableAt) (fun x => ?_)
    obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell x
    have hperD := fderiv_add_latticeVector (hperiodic u hu)
    have hShift := fderiv_add_latticeVector hperD n (x - latticeVector n)
    rw [sub_add_cancel, (hHess u hu (x - latticeVector n)).fderiv] at hShift
    change ‖fderiv ℝ (fderiv ℝ (U u)) x‖ ≤ (Real.toNNReal C : ℝ)
    rw [hShift]
    exact (hC (u, x - latticeVector n) ⟨hu, hn⟩).trans (Real.le_coe_toNNReal C)
  have htraj : ContinuousOn (fun u => (u, X s u a)) (Icc l r) :=
    continuousOn_id.prodMk (HasDerivWithinAt.continuousOn (hX.trajectory s hs a))
  have hAlong : ContinuousOn (fun u => fderiv ℝ (U u) (X s u a)) (Icc l r) :=
    (hD.continuousOn.comp htraj (fun _ hu => ⟨hu, mem_univ _⟩)).congr
      (fun u hu => (hGrad u hu (X s u a)).fderiv)
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hlr
    (hU.of_le (by norm_num)) hperiodic
  exact hX.exists_variationalSolution hK hs a
    (fun u hu x => (hGrad u hu x).differentiableAt) hDLip hAlong

/-- The periodic velocity perturbed in a real parameter has a family of
pointwise flows on the same closed slab. -/
theorem exists_perturbedLabelFlows {U b : Velocity} {l r : ℝ} (hlr : l < r)
    (hU : ContDiffOn ℝ 1 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hb : ContDiffOn ℝ 1 (Function.uncurry b) (Icc l r ×ˢ (univ : Set Vec3)))
    (hUper : ∀ t ∈ Icc l r, SpatiallyPeriodic (U t))
    (hbper : ∀ t ∈ Icc l r, SpatiallyPeriodic (b t)) :
    ∃ X : ℝ → ℝ → Velocity,
      ∀ ε : ℝ, IsLabelFlowOn (fun t x => U t x + ε • b t x) (X ε) (Icc l r) := by
  have hExists (ε : ℝ) :
      ∃ Y : ℝ → Velocity, IsLabelFlowOn (fun t x => U t x + ε • b t x) Y (Icc l r) := by
    obtain ⟨_, Y, _, hY⟩ := exists_labelFlow_on_Icc_of_contDiffOn_periodic hlr
      (U := fun t x => U t x + ε • b t x) (hU.add (hb.const_smul ε))
      (fun t ht n x => by simp only [hUper t ht n x, hbper t ht n x])
    exact ⟨Y, hY⟩
  choose X hX using hExists
  exact ⟨X, hX⟩

private theorem gronwall_zero_start_uniform {f d : ℝ → Vec3} {l r K D : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Icc l r, HasDerivWithinAt f (d t) (Icc l r) t) (h₀ : f l = 0)
    (hd : ∀ t ∈ Icc l r, ‖d t‖ ≤ K * ‖f t‖ + D) {t : ℝ} (ht : t ∈ Icc l r) :
    ‖f t‖ ≤ gronwallBound 0 K D (r - l) := by
  have h := norm_le_gronwallBound_of_hasDerivWithinAt_Icc_left hf hd
    (show ‖f l‖ ≤ 0 by simp [h₀]) ht
  exact h.trans (gronwallBound_mono le_rfl hD hK (sub_le_sub_right ht.2 l))

private theorem gronwall_zero_start_nonneg {K D d : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) (hd : 0 ≤ d) :
    0 ≤ gronwallBound 0 K D d := by
  simpa only [gronwallBound_x0] using gronwallBound_mono (δ := 0) le_rfl hD hK hd

/-- First variation in the velocity, with the initial label held fixed. The
parameter derivative solves the forced variational equation on the entire slab. -/
theorem labelFlow_firstVariation {U b : Velocity} {X : ℝ → ℝ → Velocity} {l r : ℝ}
    {K L J C : ℝ≥0} (hlr : l ≤ r)
    (hX : ∀ ε : ℝ, IsLabelFlowOn (fun t x => U t x + ε • b t x) (X ε) (Icc l r))
    (hUlip : ∀ t ∈ Icc l r, LipschitzWith K (U t))
    (hUdiff : ∀ t ∈ Icc l r, Differentiable ℝ (U t))
    (hDlip : ∀ t ∈ Icc l r, LipschitzWith L (fderiv ℝ (U t)))
    (hblip : ∀ t ∈ Icc l r, LipschitzWith J (b t))
    (hbnd : ∀ t ∈ Icc l r, ∀ x, ‖b t x‖ ≤ C)
    (hbc : ContinuousOn (Function.uncurry b) (Icc l r ×ˢ (univ : Set Vec3))) (a : Vec3)
    (hD : ContinuousOn (fun t => fderiv ℝ (U t) (X 0 l t a)) (Icc l r)) :
    ∃ ξ : ℝ → Vec3, ξ l = 0 ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt ξ
        (fderiv ℝ (U t) (X 0 l t a) (ξ t) + b t (X 0 l t a)) (Icc l r) t) ∧
      ∀ t ∈ Icc l r, HasDerivAt (fun ε : ℝ => X ε l t a) (ξ t) 0 := by
  let A (t : ℝ) := fderiv ℝ (U t) (X 0 l t a)
  let hl : l ∈ Icc l r := left_mem_Icc.2 hlr
  have hBc : ContinuousOn (fun t => b t (X 0 l t a)) (Icc l r) :=
    hbc.comp (continuousOn_id.prodMk (HasDerivWithinAt.continuousOn ((hX 0).trajectory l hl a)))
      (fun _ ht => ⟨ht, mem_univ _⟩)
  obtain ⟨ξ, hξ₀, hξ⟩ := linearODE_inhom_exists_Icc hl hD hBc (0 : Vec3)
  refine ⟨ξ, hξ₀, hξ, fun t ht => ?_⟩
  let B := gronwallBound 0 K C (r - l)
  let D := (L : ℝ) * B ^ 2 + (J : ℝ) * B
  let P := gronwallBound 0 K D (r - l)
  have hB₀ : 0 ≤ B := gronwall_zero_start_nonneg K.coe_nonneg C.coe_nonneg (sub_nonneg.mpr hlr)
  have hD₀ : 0 ≤ D := add_nonneg (mul_nonneg L.coe_nonneg (sq_nonneg _))
    (mul_nonneg J.coe_nonneg hB₀)
  have hErr (ε : ℝ) : ‖X ε l t a - X 0 l t a - ε • ξ t‖ ≤ P * ‖ε‖ ^ 2 := by
    let Δ (u : ℝ) := X ε l u a - X 0 l u a
    let dΔ (u : ℝ) := U u (X ε l u a) - U u (X 0 l u a) + ε • b u (X ε l u a)
    have hΔ₀ : Δ l = 0 := by simp [Δ, (hX _).initial l hl]
    have hΔ (u : ℝ) (hu : u ∈ Icc l r) : HasDerivWithinAt Δ (dΔ u) (Icc l r) u := by
      refine (((hX ε).trajectory l hl a u hu).sub ((hX 0).trajectory l hl a u hu)).congr_deriv ?_
      simp only [dΔ, zero_smul, add_zero]
      abel
    have hΔrate (u : ℝ) (hu : u ∈ Icc l r) : ‖dΔ u‖ ≤ (K : ℝ) * ‖Δ u‖ + (C : ℝ) * ‖ε‖ := by
      have h := (hUlip u hu).dist_le_mul (X ε l u a) (X 0 l u a)
      have hU : ‖U u (X ε l u a) - U u (X 0 l u a)‖ ≤ (K : ℝ) * ‖Δ u‖ := by
        simpa only [dist_eq_norm, Δ] using h
      calc
        ‖dΔ u‖ ≤ ‖U u (X ε l u a) - U u (X 0 l u a)‖ + ‖ε • b u (X ε l u a)‖ :=
          norm_add_le _ _
        _ ≤ _ := by
          rw [norm_smul, mul_comm (C : ℝ)]
          exact add_le_add hU (mul_le_mul_of_nonneg_left (hbnd u hu _) (norm_nonneg _))
    have hΔbound (u : ℝ) (hu : u ∈ Icc l r) : ‖Δ u‖ ≤ B * ‖ε‖ := by
      have h := gronwall_zero_start_uniform K.coe_nonneg (mul_nonneg C.coe_nonneg (norm_nonneg ε))
        hΔ hΔ₀ hΔrate hu
      rwa [gronwallBound_zero_initial_mul] at h
    let err (u : ℝ) := Δ u - ε • ξ u
    let dErr (u : ℝ) := A u (err u) +
      (U u (X ε l u a) - U u (X 0 l u a) - A u (Δ u)) +
      ε • (b u (X ε l u a) - b u (X 0 l u a))
    have herr₀ : err l = 0 := by simp only [err, hΔ₀, hξ₀, smul_zero, sub_zero]
    have herr (u : ℝ) (hu : u ∈ Icc l r) : HasDerivWithinAt err (dErr u) (Icc l r) u := by
      have hscaled : HasDerivWithinAt (fun v => ε • ξ v)
          (ε • (A u (ξ u) + b u (X 0 l u a))) (Icc l r) u :=
        (hξ u hu).const_smul ε
      refine ((hΔ u hu).sub hscaled).congr_deriv ?_
      simp only [err, dErr, dΔ, map_sub, map_smul, smul_sub, smul_add]
      abel
    have hrate (u : ℝ) (hu : u ∈ Icc l r) : ‖dErr u‖ ≤ (K : ℝ) * ‖err u‖ + D * ‖ε‖ ^ 2 := by
      have hA : ‖A u‖ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hUlip u hu)
      have hTaylor := norm_taylor_remainder_le (hUdiff u hu) (hDlip u hu) (X 0 l u a) (X ε l u a)
      have hbDiff : ‖b u (X ε l u a) - b u (X 0 l u a)‖ ≤ (J : ℝ) * (B * ‖ε‖) := by
        have h := (hblip u hu).dist_le_mul (X ε l u a) (X 0 l u a)
        rw [dist_eq_norm, dist_eq_norm] at h
        exact h.trans (mul_le_mul_of_nonneg_left (hΔbound u hu) J.coe_nonneg)
      calc
        ‖dErr u‖ ≤
            ‖A u (err u)‖ + (L : ℝ) * ‖Δ u‖ ^ 2 + ‖ε‖ * ‖b u (X ε l u a) - b u (X 0 l u a)‖ :=
          (norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add le_rfl hTaylor)) (by rw [norm_smul]))
        _ ≤ (K : ℝ) * ‖err u‖ + (L : ℝ) * (B * ‖ε‖) ^ 2 + ‖ε‖ * ((J : ℝ) * (B * ‖ε‖)) :=
          add_le_add (add_le_add (((A u).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hΔbound u hu) 2) L.coe_nonneg))
            (mul_le_mul_of_nonneg_left hbDiff (norm_nonneg _))
        _ = _ := by dsimp only [D]; ring
    have h := gronwall_zero_start_uniform K.coe_nonneg (mul_nonneg hD₀ (sq_nonneg ‖ε‖))
      herr herr₀ hrate ht
    rwa [gronwallBound_zero_initial_mul] at h
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hcont : Continuous (fun ε : ℝ => P * ‖ε‖) := by fun_prop
  have hlim : Tendsto (fun ε : ℝ => P * ‖ε‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto
  filter_upwards [hlim (Iio_mem_nhds hc)] with ε hε
  simp only [sub_zero]
  exact (hErr ε).trans <| calc
    P * ‖ε‖ ^ 2 = (P * ‖ε‖) * ‖ε‖ := by ring
    _ ≤ c * ‖ε‖ := mul_le_mul_of_nonneg_right (mem_Iio.mp hε).le (norm_nonneg _)

end TorusEuler
