import TorusEuler.FlowHigherVariations
import TorusEuler.LinearODEHigherParameter
import TorusEuler.OscillatoryHierarchySolve

/-! Joint time and label–phase regularity on the closed oscillatory slab. -/

open Asymptotics Filter Set
open scoped ContDiff InnerProductSpace Interval Topology

namespace TorusEuler

section ClosedSlab

universe u

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasFDerivWithinAt_time_param
    {X G : ℝ → P → E} {D : ℝ → P → P →L[ℝ] E} {T t : ℝ} {p : P}
    (ht : t ∈ Icc 0 T)
    (hG : ContinuousOn (Function.uncurry G) (Icc 0 T ×ˢ (univ : Set P)))
    (hXt : ∀ q u, u ∈ Icc 0 T → HasDerivWithinAt (fun v => X v q) (G u q) (Icc 0 T) u)
    (hD : HasFDerivAt (X t) (D t p) p) :
    HasFDerivWithinAt (Function.uncurry X)
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (G t p)).coprod (D t p))
      (Icc 0 T ×ˢ (univ : Set P)) (t, p) := by
  let S := Icc 0 T ×ˢ (univ : Set P)
  let b : ℝ × P := (t, p)
  have hb : b ∈ S := ⟨ht, mem_univ _⟩
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  have hcon : ∀ᶠ z in 𝓝[S] b, ‖G z.1 z.2 - G t p‖ < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp (hG b hb) (ε / 2) he)
    simpa only [dist_eq_norm, Function.uncurry] using h
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hcon
  have hd : ∀ᶠ q in 𝓝 p, ‖X t q - X t p - D t p (q - p)‖ ≤ ε / 2 * ‖q - p‖ :=
    isLittleO_iff.mp (hasFDerivAt_iff_isLittleO.mp hD) he
  have hdp : ∀ᶠ z in 𝓝[S] b, ‖X t z.2 - X t p - D t p (z.2 - p)‖ ≤ ε / 2 * ‖z.2 - p‖ :=
    ((continuous_snd.tendsto b).mono_left nhdsWithin_le_nhds).eventually hd
  have hclose : ∀ᶠ z in 𝓝[S] b, z ∈ Metric.ball b δ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds b hδ)
  filter_upwards [self_mem_nhdsWithin (s := S), hclose, hdp] with z hz hc hsp
  have hsub : uIcc t z.1 ⊆ Icc 0 T := ordConnected_Icc.uIcc_subset ht hz.1
  have hlocal (u : ℝ) (hu : u ∈ uIcc t z.1) : ‖G u z.2 - G t p‖ ≤ ε / 2 := by
    have hdist : dist (u, z.2) b ≤ dist z b := by
      rw [dist_eq_norm, dist_eq_norm, Prod.norm_def, Prod.norm_def]
      exact max_le_max (abs_sub_left_of_mem_uIcc hu) le_rfl
    have hmem : (u, z.2) ∈ Metric.ball b δ ∩ S :=
      ⟨Metric.mem_ball.mpr (hdist.trans_lt (Metric.mem_ball.mp hc)), ⟨hsub hu, mem_univ _⟩⟩
    exact (hball hmem).le
  let Y (u : ℝ) := X u z.2 - (u - t) • G t p
  have hY (u : ℝ) (hu : u ∈ uIcc t z.1) :
      HasDerivWithinAt Y (G u z.2 - G t p) (uIcc t z.1) u := by
    have hlin := ((hasDerivWithinAt_id u (uIcc t z.1)).sub_const t).smul_const (G t p)
    have hd := ((hXt z.2 u (hsub hu)).mono hsub).sub hlin
    change HasDerivWithinAt Y (G u z.2 - 1 • G t p) (uIcc t z.1) u at hd
    simpa only [one_smul] using hd
  have htime : ‖X z.1 z.2 - X t z.2 - (z.1 - t) • G t p‖ ≤ ε / 2 * ‖z.1 - t‖ := by
    have hm := (convex_uIcc t z.1).norm_image_sub_le_of_norm_hasDerivWithin_le
      hY hlocal left_mem_uIcc right_mem_uIcc
    have heq : X z.1 z.2 - X t z.2 - (z.1 - t) • G t p = Y z.1 - Y t := by
      simp only [Y, sub_self, zero_smul, sub_zero]
      abel
    rwa [heq]
  have hjoin :
      X z.1 z.2 - X t p -
        (((ContinuousLinearMap.id ℝ ℝ).smulRight (G t p)).coprod (D t p)) (z - b) =
        (X z.1 z.2 - X t z.2 - (z.1 - t) • G t p) + (X t z.2 - X t p - D t p (z.2 - p)) := by
    simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, b, Prod.fst_sub, Prod.snd_sub]
    abel
  change ‖X z.1 z.2 - X t p -
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (G t p)).coprod (D t p)) (z - b)‖ ≤ ε * ‖z - b‖
  rw [hjoin]
  calc
    _ ≤ ε / 2 * ‖z.1 - t‖ + ε / 2 * ‖z.2 - p‖ :=
      (norm_add_le _ _).trans (add_le_add htime hsp)
    _ ≤ ε / 2 * ‖z - b‖ + ε / 2 * ‖z - b‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le (z - b)) he.le)
        (mul_le_mul_of_nonneg_left (norm_snd_le (z - b)) he.le)
    _ = _ := by ring

private theorem contDiffOn_spatialDerivative {X : ℝ → P → E} {T : ℝ}
    (hT : 0 < T)
    (hX : ContDiffOn ℝ ∞ (Function.uncurry X) (Icc 0 T ×ˢ (univ : Set P))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × P => fderiv ℝ (X z.1) z.2) (Icc 0 T ×ˢ (univ : Set P)) := by
  let S := Icc 0 T ×ˢ (univ : Set P)
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  refine ((hX.fderivWithin hS (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ P))).congr ?_
  rintro ⟨t, p⟩ ht
  have h := (hX.differentiableOn (by simp) (t, p) ht).hasFDerivWithinAt
  exact (h.comp_hasFDerivAt p (hasFDerivAt_prodMk_right (𝕜 := ℝ) t p)
    (Eventually.of_forall fun y => ⟨ht.1, mem_univ y⟩)).fderiv

/-- View jointly continuous data on the closed slab as a family of continuous
time paths indexed by the parameter. -/
def currySlab {T : ℝ} {X : ℝ → P → E}
    (hX : ContinuousOn (Function.uncurry X) (Icc 0 T ×ˢ (univ : Set P))) (p : P) :
    C(Icc (0 : ℝ) T, E) :=
  ⟨fun t => X t p, (hX.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht, mem_univ p⟩)).domRestrict⟩

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
noncomputable def currySlabWithin {T : ℝ} {S : Set P} {X : ℝ → P → E}
    (hX : ContinuousOn (Function.uncurry X) (Icc 0 T ×ˢ S)) (p : P) : C(Icc (0 : ℝ) T, E) := by
  classical
  exact if hp : p ∈ S then
    ⟨fun t => X t p, (hX.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht => ⟨ht, hp⟩)).domRestrict⟩
  else 0

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem currySlabWithin_apply {T : ℝ} {S : Set P} {X : ℝ → P → E}
    (hX : ContinuousOn (Function.uncurry X) (Icc 0 T ×ˢ S)) {p : P} (hp : p ∈ S)
    (t : Icc (0 : ℝ) T) : currySlabWithin hX p t = X t p := by
  rw [currySlabWithin, dite_eq_left hp]
  rfl

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
private theorem continuousOn_currySlabWithin {T : ℝ} {S : Set P} {X : ℝ → P → E}
    (hX : ContinuousOn (Function.uncurry X) (Icc 0 T ×ˢ S)) :
    ContinuousOn (currySlabWithin hX) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hproj : Continuous (fun z : S × Icc (0 : ℝ) T => ((z.2 : ℝ), (z.1 : P))) :=
    (continuous_subtype_val.comp continuous_snd).prodMk (continuous_subtype_val.comp continuous_fst)
  apply continuousOn_univ.mp
  exact (hX.comp hproj.continuousOn (fun z _ => ⟨z.2.property, z.1.property⟩)).congr
    (fun z _ => currySlabWithin_apply hX z.1.property z.2)

private noncomputable def slabOperatorPath {T : ℝ}
    (A : C(Icc (0 : ℝ) T, P →L[ℝ] E)) : P →L[ℝ] C(Icc (0 : ℝ) T, E) := by
  let L : P →ₗ[ℝ] C(Icc (0 : ℝ) T, E) :=
    { toFun := fun p => ⟨fun t => A t p, A.continuous.clm_apply continuous_const⟩
      map_add' := fun p q => by ext t; exact (A t).map_add p q
      map_smul' := fun c p => by ext t; exact (A t).map_smul c p }
  exact L.mkContinuous ‖A‖ fun p =>
    ((L p).norm_le (mul_nonneg (norm_nonneg A) (norm_nonneg p))).2 fun t =>
      (A t).le_of_opNorm_le (A.norm_coe_le_norm t) p

private theorem slabOperatorPath_apply {T : ℝ}
    (A : C(Icc (0 : ℝ) T, P →L[ℝ] E)) (p : P) (t : Icc (0 : ℝ) T) :
    slabOperatorPath A p t = A t p := rfl

private noncomputable def slabOperatorPathCLM {T : ℝ} :
    C(Icc (0 : ℝ) T, P →L[ℝ] E) →L[ℝ] (P →L[ℝ] C(Icc (0 : ℝ) T, E)) := by
  let L : C(Icc (0 : ℝ) T, P →L[ℝ] E) →ₗ[ℝ] (P →L[ℝ] C(Icc (0 : ℝ) T, E)) :=
    { toFun := slabOperatorPath
      map_add' := fun A B => by
        ext p t
        simp only [add_apply, slabOperatorPath_apply, ContinuousMap.add_apply]
      map_smul' := fun c A => by
        ext p t
        simp only [smul_apply, slabOperatorPath_apply, ContinuousMap.smul_apply, RingHom.id_apply] }
  have hL (A : C(Icc (0 : ℝ) T, P →L[ℝ] E)) : ‖L A‖ ≤ 1 * ‖A‖ := by
    change ‖slabOperatorPath A‖ ≤ 1 * ‖A‖
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun p => ?_
    exact ((slabOperatorPath A p).norm_le (mul_nonneg (norm_nonneg A) (norm_nonneg p))).2 fun t => by
      rw [slabOperatorPath_apply]
      exact (A t).le_of_opNorm_le (A.norm_coe_le_norm t) p
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := C(Icc (0 : ℝ) T, P →L[ℝ] E))
    (F := P →L[ℝ] C(Icc (0 : ℝ) T, E)) (σ := RingHom.id ℝ) L 1 hL

private theorem hasFDerivWithinAt_currySlab {X : ℝ → P → E}
    {D : ℝ → P → P →L[ℝ] E} {T : ℝ} {S : Set P} (hS : Convex ℝ S)
    (hX : ContinuousOn (Function.uncurry X) (Icc 0 T ×ˢ S))
    (hD : ContinuousOn (Function.uncurry D) (Icc 0 T ×ˢ S))
    (hDer : ∀ t ∈ Icc 0 T, ∀ p ∈ S, HasFDerivWithinAt (X t) (D t p) S p)
    {p : P} (hp : p ∈ S) :
    HasFDerivWithinAt (currySlabWithin hX) (slabOperatorPathCLM (currySlabWithin hD p)) S p := by
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hb : ∀ᶠ q in 𝓝[S] p, ‖currySlabWithin hD q - currySlabWithin hD p‖ < ε := by
    simpa only [dist_eq_norm] using
      (Metric.tendsto_nhds.mp (continuousOn_currySlabWithin hD p hp) ε hε)
  obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhdsWithin_iff.mp hb
  have hball : ∀ᶠ q in 𝓝[S] p, q ∈ Metric.ball p δ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hball, self_mem_nhdsWithin (s := S)] with q hq hqS
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2
  intro t
  let R (u : P) := X t u - X t p - D t p (u - p)
  have hR (u : P) (hu : u ∈ Metric.ball p δ ∩ S) :
      HasFDerivWithinAt R (D t u - D t p) (Metric.ball p δ ∩ S) u := by
    have hlin := (D t p).hasFDerivAt.comp u ((hasFDerivAt_id u).sub_const p)
    exact ((((hDer t t.property u hu.2).sub_const (X t p)).sub hlin.hasFDerivWithinAt)).mono
      inter_subset_right
  have hBound (u : P) (hu : u ∈ Metric.ball p δ ∩ S) : ‖D t u - D t p‖ ≤ ε := by
    have hb := (currySlabWithin hD u - currySlabWithin hD p).norm_coe_le_norm t
    simp only [ContinuousMap.sub_apply, currySlabWithin_apply hD hu.2,
      currySlabWithin_apply hD hp] at hb
    exact hb.trans (hδb hu).le
  have hr := ((convex_ball p δ).inter hS).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hR hBound ⟨Metric.mem_ball_self hδ, hp⟩ ⟨hq, hqS⟩
  have hRp : R p = 0 := by simp [R]
  rw [hRp, sub_zero] at hr
  change ‖currySlabWithin hX q t - currySlabWithin hX p t -
    slabOperatorPath (currySlabWithin hD p) (q - p) t‖ ≤ ε * ‖q - p‖
  rw [slabOperatorPath_apply, currySlabWithin_apply hX hqS,
    currySlabWithin_apply hX hp, currySlabWithin_apply hD hp]
  exact hr

theorem contDiffOn_currySlabWithin {X : ℝ → P → E} {T : ℝ} {S : Set P}
    (hT : 0 < T) (hS : Convex ℝ S) (hSu : UniqueDiffOn ℝ S)
    (hX : ContDiffOn ℝ ∞ (Function.uncurry X) (Icc 0 T ×ˢ S)) :
    ContDiffOn ℝ ∞ (currySlabWithin hX.continuousOn) S := by
  apply contDiffOn_infty.2
  intro n
  induction n generalizing E with
  | zero =>
      simpa only [Nat.cast_zero, contDiffOn_zero] using continuousOn_currySlabWithin hX.continuousOn
  | succ n ih =>
      let D (t : ℝ) (p : P) := (fderivWithin ℝ (Function.uncurry X) (Icc 0 T ×ˢ S) (t, p)).comp
        (ContinuousLinearMap.inr ℝ ℝ P)
      have hD : ContDiffOn ℝ ∞ (Function.uncurry D) (Icc 0 T ×ˢ S) :=
        (hX.fderivWithin ((uniqueDiffOn_Icc hT).prod hSu) (m := ∞) (by simp)).clm_comp
          (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ P))
      have hDX (t : ℝ) (ht : t ∈ Icc 0 T) (p : P) (hp : p ∈ S) :
          HasFDerivWithinAt (X t) (D t p) S p := by
        exact ((hX.differentiableOn (by simp) (t, p) ⟨ht, hp⟩).hasFDerivWithinAt).comp p
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) t p).hasFDerivWithinAt (fun q hq => ⟨ht, hq⟩)
      have hd (p : P) (hp : p ∈ S) :=
        hasFDerivWithinAt_currySlab hS hX.continuousOn hD.continuousOn hDX hp
      have hn : ContDiffOn ℝ n (currySlabWithin hD.continuousOn) S := ih hD
      let L : C(Icc (0 : ℝ) T, P →L[ℝ] E) →L[ℝ] (P →L[ℝ] C(Icc (0 : ℝ) T, E)) :=
        slabOperatorPathCLM
      have hL : ContDiff ℝ n L :=
        ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (E := C(Icc (0 : ℝ) T, P →L[ℝ] E))
          (F := P →L[ℝ] C(Icc (0 : ℝ) T, E)) L
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderivWithin hSu]
      refine ⟨fun p hp => (hd p hp).differentiableWithinAt, ?_, ?_⟩
      · intro h
        simp at h
      · exact (hL.comp_contDiffOn hn).congr fun p hp => (hd p hp).fderivWithin (hSu p hp)

/-- Ordinary jointly smooth data on the closed slab are smooth as a map from
the parameter into continuous time paths with the uniform norm. -/
theorem contDiff_currySlab_of_contDiffOn {X : ℝ → P → E} {T : ℝ} (hT : 0 < T)
    (hX : ContDiffOn ℝ ∞ (Function.uncurry X) (Icc 0 T ×ˢ (univ : Set P))) :
    ContDiff ℝ ∞ (currySlab hX.continuousOn) := by
  apply contDiffOn_univ.mp
  refine (contDiffOn_currySlabWithin hT convex_univ uniqueDiffOn_univ hX).congr ?_
  intro p hp
  ext t
  exact (currySlabWithin_apply hX.continuousOn hp t).symm

private theorem phaseMean_congr_unit {f g : ℝ → E}
    (h : EqOn f g (Icc 0 1)) : phaseMean f = phaseMean g :=
  intervalIntegral.integral_congr (by rwa [uIcc_of_le zero_le_one])

private noncomputable def unitPhaseIntegralCLM : C(Icc (0 : ℝ) 1, E) →L[ℝ] E := by
  let π := projIcc (0 : ℝ) 1 zero_le_one
  have hπ : Continuous π := continuous_projIcc
  let L : C(Icc (0 : ℝ) 1, E) →ₗ[ℝ] E :=
    { toFun := fun f => phaseMean (f ∘ π)
      map_add' := fun f g => phaseMean_add (f.continuous.comp hπ) (g.continuous.comp hπ)
      map_smul' := fun c f => phaseMean_const_smul c (f ∘ π) }
  exact LinearMap.mkContinuous L 1 fun f => by
    rw [one_mul]
    exact norm_phaseMean_le (f := f ∘ π) fun s _ => f.norm_coe_le_norm (π s)

private theorem unitPhaseIntegralCLM_apply_eq
    {f : C(Icc (0 : ℝ) 1, E)} {g : ℝ → E}
    (h : ∀ s : Icc (0 : ℝ) 1, f s = g s) : unitPhaseIntegralCLM f = phaseMean g := by
  change phaseMean (f ∘ projIcc 0 1 zero_le_one) = _
  refine phaseMean_congr_unit fun s hs => ?_
  simpa only [Function.comp_apply, projIcc_of_mem zero_le_one hs] using h ⟨s, hs⟩

/-- Averaging jointly smooth data over a unit phase interval preserves
smoothness within a convex parameter domain, including its boundary. -/
theorem contDiffOn_phaseMean {S : Set P} {f : P → ℝ → E} (hS : Convex ℝ S)
    (hSu : UniqueDiffOn ℝ S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (S ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (fun p => phaseMean (f p)) S := by
  have hφ : ContDiffOn ℝ ∞ (Function.uncurry (fun s p => f p s)) (Icc 0 1 ×ˢ S) :=
    hf.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun z hz => ⟨hz.2, mem_univ z.1⟩)
  refine (unitPhaseIntegralCLM.contDiff.comp_contDiffOn
    (contDiffOn_currySlabWithin zero_lt_one hS hSu hφ)).congr ?_
  exact fun p hp => (unitPhaseIntegralCLM_apply_eq (currySlabWithin_apply hφ.continuousOn hp)).symm

private theorem hasDerivWithinAt_phaseMean {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X R : ℝ → ℝ → F} {S : Set ℝ}
    (hS : Convex ℝ S) (hX : ContinuousOn (Function.uncurry X) (Icc 0 1 ×ˢ S))
    (hR : ContinuousOn (Function.uncurry R) (Icc 0 1 ×ˢ S))
    (hXt : ∀ s ∈ Icc 0 1, ∀ t ∈ S, HasDerivWithinAt (X s) (R s t) S t)
    {t : ℝ} (ht : t ∈ S) :
    HasDerivWithinAt (fun u => phaseMean (fun s => X s u)) (phaseMean (fun s => R s t)) S t := by
  let J := ContinuousLinearMap.smulRightL ℝ ℝ F (ContinuousLinearMap.id ℝ ℝ)
  let D (s u : ℝ) := J (R s u)
  have hD : ContinuousOn (Function.uncurry D) (Icc 0 1 ×ˢ S) :=
    J.continuous.comp_continuousOn hR
  have hd (s : ℝ) (hs : s ∈ Icc 0 1) (u : ℝ) (hu : u ∈ S) :
      HasFDerivWithinAt (X s) (D s u) S u :=
    (hXt s hs u hu).hasFDerivWithinAt
  let L : C(Icc (0 : ℝ) 1, F) →L[ℝ] F := unitPhaseIntegralCLM
  have hPath := hasFDerivWithinAt_currySlab hS hX hD hd ht
  have h := (L.hasFDerivAt.comp_hasFDerivWithinAt t hPath).hasDerivWithinAt
  have hvalue : unitPhaseIntegralCLM (slabOperatorPathCLM (currySlabWithin hD t) 1) =
      phaseMean (fun s => R s t) := by
    apply unitPhaseIntegralCLM_apply_eq
    intro s
    change slabOperatorPath (currySlabWithin hD t) 1 s = R s t
    rw [slabOperatorPath_apply, currySlabWithin_apply hD ht]
    simp [D, J]
  change HasDerivWithinAt (fun u => unitPhaseIntegralCLM (currySlabWithin hX u))
    (unitPhaseIntegralCLM (slabOperatorPathCLM (currySlabWithin hD t) 1)) S t at h
  rw [hvalue] at h
  exact h.congr_of_mem (fun u hu => (unitPhaseIntegralCLM_apply_eq
    (currySlabWithin_apply hX hu)).symm) ht

/-- The normalized phase primitive preserves joint smoothness when the time
coordinate is restricted to a closed slab. -/
theorem contDiffOn_phasePrimitive {S : Set P} {f : P → ℝ → E} (hS : Convex ℝ S)
    (hSu : UniqueDiffOn ℝ S) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (S ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun p => phasePrimitive (f p))) (S ×ˢ (univ : Set ℝ)) := by
  let A (p : P) (s : ℝ) := ∫ σ in (0 : ℝ)..s, f p σ
  let D := S ×ˢ (univ : Set ℝ)
  have hrescale : ContDiffOn ℝ ∞ (fun z : (P × ℝ) × ℝ => f z.1.1 (z.1.2 * z.2)) (D ×ˢ univ) :=
    hf.comp (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.mul contDiffOn_snd))
      (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) D := by
    refine (contDiffOn_snd.smul
      (contDiffOn_phaseMean (hS.prod convex_univ) (hSu.prod uniqueDiffOn_univ)
        (f := fun (p : P × ℝ) σ => f p.1 (p.2 * σ)) hrescale)).congr ?_
    intro z _
    symm
    change z.2 • (∫ σ in (0 : ℝ)..1, f z.1 (z.2 * σ)) = ∫ σ in (0 : ℝ)..z.2, f z.1 σ
    simpa only [mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (f z.1) z.2
  exact hA.sub ((contDiffOn_phaseMean hS hSu hA).comp contDiffOn_fst (fun z hz => hz.1))

end ClosedSlab

set_option maxHeartbeats 800000 in
/-- A jointly continuous finite-dimensional trajectory family for a smooth
vector field is jointly smooth in time and the parameter on the closed slab. -/
theorem trajectoryFamily_joint_contDiff {P E : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {X : ℝ → P → E} {T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set E)))
    (hXc : ContinuousOn (Function.uncurry X) (Icc 0 T ×ˢ (univ : Set P)))
    (hXt : ∀ p t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => X s p) (f t (X t p)) (Icc 0 T) t)
    (hX₀ : ContDiff ℝ ∞ (X 0)) :
    ContDiffOn ℝ ∞ (Function.uncurry X) (Icc 0 T ×ˢ (univ : Set P)) := by
  apply contDiffOn_infty.2
  intro n
  induction n generalizing E with
  | zero =>
      simpa only [Nat.cast_zero, contDiffOn_zero] using hXc
  | succ n ih =>
      let S := Icc 0 T ×ˢ (univ : Set P)
      let J (t : ℝ) := fderiv ℝ (X t)
      let G (t : ℝ) (p : P) := f t (X t p)
      have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
      have hXn : ContDiffOn ℝ n (Function.uncurry X) S := ih hf hXc hXt hX₀
      have hGn : ContDiffOn ℝ n (Function.uncurry G) S :=
        (hf.of_le (by simp)).comp (contDiffOn_fst.prodMk hXn) (fun z hz => ⟨hz.1, mem_univ _⟩)
      obtain ⟨hP, hJc, hJt⟩ := trajectoryFamily_spatialDerivative hT hf hXc hXt hX₀
      let F (t : ℝ) (z : E × (P →L[ℝ] E)) := (f t z.1, (fderiv ℝ (f t) z.1).comp z.2)
      let Z (t : ℝ) (p : P) := (X t p, J t p)
      have hF : ContDiffOn ℝ ∞ (Function.uncurry F)
          (Icc 0 T ×ˢ (univ : Set (E × (P →L[ℝ] E)))) := by
        have hproj : ContDiffOn ℝ ∞ (fun z : ℝ × (E × (P →L[ℝ] E)) => (z.1, z.2.1))
            (Icc 0 T ×ˢ (univ : Set (E × (P →L[ℝ] E)))) :=
          contDiffOn_fst.prodMk contDiffOn_snd.fst
        have hm : MapsTo (fun z : ℝ × (E × (P →L[ℝ] E)) => (z.1, z.2.1))
            (Icc 0 T ×ˢ (univ : Set (E × (P →L[ℝ] E)))) (Icc 0 T ×ˢ (univ : Set E)) :=
          fun z hz => ⟨hz.1, mem_univ _⟩
        exact (hf.comp hproj hm).prodMk
          (((contDiffOn_spatialDerivative hT hf).comp hproj hm).clm_comp contDiffOn_snd.snd)
      have hZt (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
          HasDerivWithinAt (fun s => Z s p) (F t (Z t p)) (Icc 0 T) t :=
        (hXt p t ht).prodMk (hJt p t ht)
      have hZ₀ : ContDiff ℝ ∞ (Z 0) := hX₀.prodMk (hX₀.fderiv_right (by simp))
      have hZn : ContDiffOn ℝ n (Function.uncurry Z) S :=
        ih hF (hXc.prodMk hJc) hZt hZ₀
      let B (z : ℝ × P) :=
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (G z.1 z.2)).coprod (J z.1 z.2)
      have hB (z : ℝ × P) (hz : z ∈ S) :
          HasFDerivWithinAt (Function.uncurry X) (B z) S z :=
        hasFDerivWithinAt_time_param hz.1 hGn.continuousOn hXt
          (hP z.1 hz.1 z.2).hasFDerivAt
      have hBn : ContDiffOn ℝ n B S := by
        let b₁ := ContinuousLinearMap.smulRightL ℝ (ℝ × P) E (ContinuousLinearMap.fst ℝ ℝ P)
        let b₂ := (ContinuousLinearMap.compL ℝ (ℝ × P) P E).flip (ContinuousLinearMap.snd ℝ ℝ P)
        have h₁ : ContDiffOn ℝ n (fun z => b₁ (G z.1 z.2)) S :=
          b₁.contDiff.comp_contDiffOn hGn
        have h₂ : ContDiffOn ℝ n (fun z => b₂ (J z.1 z.2)) S :=
          b₂.contDiff.comp_contDiffOn hZn.snd
        refine (h₁.add h₂).congr ?_
        intro z _
        apply ContinuousLinearMap.ext
        intro d
        simp [B, b₁, b₂, ContinuousLinearMap.coprod_apply]
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderivWithin hS]
      refine ⟨fun z hz => (hB z hz).differentiableWithinAt, ?_, ?_⟩
      · intro h
        simp at h
      · exact hBn.congr fun z hz => (hB z hz).fderivWithin (hS z hz)

section OscillatorySolve

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem contDiffOn_transverseCoefficients {Q : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {S : Set Q}
    {M : Q → E →L[ℝ] E} {k : Q → E}
    (hM : ContDiffOn ℝ ∞ M S) (hk : ContDiffOn ℝ ∞ k S) (hk₀ : ∀ q ∈ S, k q ≠ 0) :
    ContDiffOn ℝ ∞ (fun q => affineWaveAmplitudeOperator (M q) (k q)) S ∧
      ContDiffOn ℝ ∞ (fun q => oscillatoryTransverseProjection (k q)) S := by
  let L : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hInner : ContDiffOn ℝ ∞ (fun q => L (k q)) S := L.contDiff.comp_contDiffOn hk
  have hRank : ContDiffOn ℝ ∞ (fun q => InnerProductSpace.rankOne ℝ (k q) (k q)) S :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := E) (F := E)).contDiff.comp_contDiffOn
      (hInner.prodMk hk)
  have hn : ContDiffOn ℝ ∞ (fun q => ‖k q‖ ^ 2) S := hk.norm_sq ℝ
  have hn₀ (q : Q) (hq : q ∈ S) : ‖k q‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (hk₀ q hq))
  have ht : ContDiffOn ℝ ∞ (fun q => 2 / ‖k q‖ ^ 2) S :=
    (contDiffOn_const (c := (2 : ℝ))).div hn hn₀
  have ho : ContDiffOn ℝ ∞ (fun q => (‖k q‖ ^ 2)⁻¹) S := hn.inv hn₀
  exact ⟨hM.neg.add (ht.smul (hRank.clm_comp hM)), contDiffOn_const.sub (ho.smul hRank)⟩

/-- Smooth wave-vector, strain and forcing profiles give a jointly smooth
zero-start transverse velocity, including both time endpoints. The
parameter may be the pair of a label and a phase. -/
theorem exists_jointSmooth_oscillatoryVelocity
    {M : ℝ → P → E →L[ℝ] E} {κ f : ℝ → P → E} {T : ℝ} (hT : 0 < T)
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc 0 T ×ˢ (univ : Set P)))
    (hκ : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc 0 T ×ˢ (univ : Set P)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set P)))
    (hκ₀ : ∀ p, κ 0 p ≠ 0)
    (hκt : ∀ p t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun u => κ u p) (-((M t p).adjoint (κ t p))) (Icc 0 T) t) :
    ∃ V : ℝ → P → E, V 0 = 0 ∧
      ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set P)) ∧
      ∀ p t, t ∈ Icc 0 T → κ t p ≠ 0 ∧ ⟪κ t p, V t p⟫_ℝ = 0 ∧
        HasDerivWithinAt (fun u => V u p)
          (affineWaveAmplitudeOperator (M t p) (κ t p) (V t p) +
            oscillatoryTransverseProjection (κ t p) (f t p)) (Icc 0 T) t ∧
        HasDerivWithinAt (fun u => V u p)
          (f t p - M t p (V t p) -
            oscillatoryPressureSlope (M t p) (κ t p) (f t p) (V t p) • κ t p) (Icc 0 T) t := by
  let S := Icc 0 T ×ˢ (univ : Set P)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hκne (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) : κ t p ≠ 0 := by
    have hMc : ContinuousOn (fun u => M u p) (Icc 0 T) :=
      hM.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => ⟨hu, mem_univ p⟩)
    have hAdj : ContinuousOn (fun u => -(M u p).adjoint) (Icc 0 T) :=
      ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hMc).neg
    exact linearODE_ne_zero_of_mem ordConnected_Icc h0 hAdj
      (fun u hu => by simpa only [neg_apply] using hκt p u hu) (hκ₀ p) t ht
  let A (t : ℝ) (p : P) := affineWaveAmplitudeOperator (M t p) (κ t p)
  let g (t : ℝ) (p : P) := oscillatoryTransverseProjection (κ t p) (f t p)
  obtain ⟨hA, hProj⟩ := contDiffOn_transverseCoefficients hM hκ
    (fun q hq => hκne q.2 q.1 hq.1)
  have hAc : ContDiffOn ℝ ∞ (Function.uncurry A) S := hA
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) S := hProj.clm_apply hf
  obtain ⟨x, hx, hx₀, hODE⟩ := exists_contDiff_parameterized_linearODE hT.le
    (contDiff_currySlab_of_contDiffOn hT hAc) (contDiff_currySlab_of_contDiffOn hT hg)
    (contDiff_const (c := (0 : E)))
  let V (t : ℝ) (p : P) := x p (projIcc 0 T hT.le t)
  have hV₀ : V 0 = 0 := by
    funext p
    change x p (projIcc 0 T hT.le 0) = 0
    rw [projIcc_of_mem hT.le h0]
    exact hx₀ p
  have hprojTime : Continuous (fun z : ℝ × P => projIcc 0 T hT.le z.1) :=
    continuous_projIcc.comp continuous_fst
  have hVc : Continuous (Function.uncurry V) :=
    continuous_eval.comp ((hx.continuous.comp continuous_snd).prodMk hprojTime)
  have hVt (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => V u p) (A t p (V t p) + g t p) (Icc 0 T) t := by
    have h := hODE p t ht
    change HasDerivWithinAt (fun u => V u p)
      (A t p (x p ⟨t, ht⟩) + g t p) (Icc 0 T) t at h
    have heq : V t p = x p ⟨t, ht⟩ := by
      change x p (projIcc 0 T hT.le t) = _
      rw [projIcc_of_mem hT.le ht]
    rwa [heq]
  let Y (t : ℝ) (p : P) := (V t p, p)
  let W (t : ℝ) (z : E × P) := (A t z.2 z.1 + g t z.2, (0 : P))
  have hW : ContDiffOn ℝ ∞ (Function.uncurry W) (Icc 0 T ×ˢ (univ : Set (E × P))) := by
    have hproj : ContDiffOn ℝ ∞ (fun z : ℝ × (E × P) => (z.1, z.2.2))
        (Icc 0 T ×ˢ (univ : Set (E × P))) := contDiffOn_fst.prodMk contDiffOn_snd.snd
    have hm : MapsTo (fun z : ℝ × (E × P) => (z.1, z.2.2))
        (Icc 0 T ×ˢ (univ : Set (E × P))) S := fun z hz => ⟨hz.1, mem_univ _⟩
    exact (((hAc.comp hproj hm).clm_apply contDiffOn_snd.fst).add
      (hg.comp hproj hm)).prodMk contDiffOn_const
  have hY₀ : ContDiff ℝ ∞ (Y 0) := by
    change ContDiff ℝ ∞ (fun p => (V 0 p, p))
    rw [hV₀]
    exact contDiff_const.prodMk contDiff_id
  have hY : ContDiffOn ℝ ∞ (Function.uncurry Y) S :=
    trajectoryFamily_joint_contDiff (f := W) hT hW (hVc.continuousOn.prodMk continuousOn_snd)
      (fun p t ht => by
        simpa only [Y, W] using (hVt p t ht).prodMk (hasDerivWithinAt_const t (Icc 0 T) p)) hY₀
  refine ⟨V, hV₀, hY.fst, fun p t ht => ⟨hκne p t ht, ?_, hVt p t ht, ?_⟩⟩
  · exact oscillatory_transverse_of_initial ordConnected_Icc h0 (hκne p) (hκt p) (hVt p)
      (by simp [hV₀]) t ht
  · simpa only [A, g, affineWaveAmplitudeOperator_add_transverseProjection] using hVt p t ht

set_option maxHeartbeats 200000 in
private theorem periodic_zeroMean_of_phase_linearODE
    {A B : ℝ → E →L[ℝ] E} {f V : ℝ → ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (hB : ContinuousOn B (Icc 0 T))
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set ℝ)))
    (hV : ContinuousOn (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set ℝ)))
    (hV₀ : ∀ s, V 0 s = 0)
    (hODE : ∀ s t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun u => V u s) (A t (V t s) + B t (f t s)) (Icc 0 T) t)
    (hfper : ∀ t ∈ Icc 0 T, Function.Periodic (f t) 1)
    (hfmean : ∀ t ∈ Icc 0 T, phaseMean (f t) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Function.Periodic (V t) 1 ∧ phaseMean (V t) = 0 := by
  let I := Icc (0 : ℝ) T
  have h0 : 0 ∈ I := ⟨le_rfl, hT⟩
  constructor
  · intro s
    let w (u : ℝ) := V u (s + 1) - V u s
    have hw (u : ℝ) (hu : u ∈ I) : HasDerivWithinAt w (A u (w u)) I u := by
      refine ((hODE (s + 1) u hu).sub (hODE s u hu)).congr_deriv ?_
      change A u (V u (s + 1)) + B u (f u (s + 1)) -
        (A u (V u s) + B u (f u s)) = A u (V u (s + 1) - V u s)
      rw [hfper u hu s, map_sub]
      abel
    have h := linearODE_unique_of_mem (y := fun _ => (0 : E)) ordConnected_Icc h0 hA hw
      (fun u _ => by simpa only [map_zero] using hasDerivWithinAt_const u I (0 : E))
      (by simp [w, hV₀])
    exact sub_eq_zero.mp (h ht)
  · let X (s u : ℝ) := V u s
    let R (s u : ℝ) := A u (V u s) + B u (f u s)
    let D := Icc (0 : ℝ) 1 ×ˢ I
    have hmaps : MapsTo Prod.swap D (I ×ˢ (univ : Set ℝ)) :=
      fun z hz => ⟨hz.2, mem_univ z.1⟩
    have hX : ContinuousOn (Function.uncurry X) D :=
      hV.comp continuous_swap.continuousOn hmaps
    have hF : ContinuousOn (fun z : ℝ × ℝ => f z.2 z.1) D :=
      hf.comp continuous_swap.continuousOn hmaps
    have hAd : ContinuousOn (fun z : ℝ × ℝ => A z.2) D :=
      hA.comp continuous_snd.continuousOn (fun z hz => hz.2)
    have hBd : ContinuousOn (fun z : ℝ × ℝ => B z.2) D :=
      hB.comp continuous_snd.continuousOn (fun z hz => hz.2)
    have hR : ContinuousOn (Function.uncurry R) D := (hAd.clm_apply hX).add (hBd.clm_apply hF)
    have hEq (u : ℝ) (hu : u ∈ I) :
        HasDerivWithinAt (fun v => phaseMean (V v)) (A u (phaseMean (V u))) I u := by
      have h := hasDerivWithinAt_phaseMean (convex_Icc (0 : ℝ) T) hX hR
        (fun s _ v hv => hODE s v hv) hu
      have hVc : Continuous (V u) := continuousOn_univ.mp
        (hV.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun s _ => ⟨hu, mem_univ s⟩))
      have hfc : Continuous (f u) := continuousOn_univ.mp
        (hf.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun s _ => ⟨hu, mem_univ s⟩))
      refine h.congr_deriv ?_
      change phaseMean (fun s => A u (V u s) + B u (f u s)) = _
      have hAV : Continuous (fun s => A u (V u s)) := (A u).continuous.comp hVc
      have hBf : Continuous (fun s => B u (f u s)) := (B u).continuous.comp hfc
      rw [phaseMean_add hAV hBf]
      have hAv : phaseMean (fun s => A u (V u s)) = A u (phaseMean (V u)) :=
        (A u).intervalIntegral_comp_comm (hVc.intervalIntegrable 0 1)
      have hBf' : phaseMean (fun s => B u (f u s)) = B u (phaseMean (f u)) :=
        (B u).intervalIntegral_comp_comm (hfc.intervalIntegrable 0 1)
      rw [hAv, hBf', hfmean u hu, map_zero, add_zero]
    have hinit : phaseMean (V 0) = 0 := by
      rw [show V 0 = fun _ => (0 : E) from funext hV₀, phaseMean_const]
    exact linearODE_unique_of_mem (y := fun _ => (0 : E)) ordConnected_Icc h0 hA hEq
      (fun u _ => by simpa only [map_zero] using hasDerivWithinAt_const u I (0 : E))
      hinit ht

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
private theorem contDiffOn_oscillatoryPhasePressure
    {M : ℝ → P → E →L[ℝ] E} {κ : ℝ → P → E} {f V : ℝ → (P × ℝ) → E} {T : ℝ}
    (hT : 0 < T)
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc 0 T ×ˢ (univ : Set P)))
    (hκ : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc 0 T ×ˢ (univ : Set P)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set (P × ℝ))))
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set (P × ℝ))))
    (hκne : ∀ a t, t ∈ Icc 0 T → κ t a ≠ 0) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun t (p : P × ℝ) =>
      oscillatoryPhasePressure (M t p.1) (κ t p.1)
        (fun s => f t (p.1, s)) (fun s => V t (p.1, s)) p.2))
      (Icc 0 T ×ˢ (univ : Set (P × ℝ))) := by
  let I := Icc (0 : ℝ) T
  let S := I ×ˢ (univ : Set (P × ℝ))
  let K := I ×ˢ (univ : Set P)
  let M' (t : ℝ) (p : P × ℝ) := M t p.1
  let κ' (t : ℝ) (p : P × ℝ) := κ t p.1
  have hproj : ContDiffOn ℝ ∞ (fun z : ℝ × (P × ℝ) => (z.1, z.2.1)) S :=
    contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hprojMem : MapsTo (fun z : ℝ × (P × ℝ) => (z.1, z.2.1)) S K :=
    fun z hz => ⟨hz.1, mem_univ z.2.1⟩
  have hM' : ContDiffOn ℝ ∞ (Function.uncurry M') S := hM.comp hproj hprojMem
  have hκ' : ContDiffOn ℝ ∞ (Function.uncurry κ') S := hκ.comp hproj hprojMem
  let q (t : ℝ) (p : P × ℝ) := oscillatoryPressureSlope (M' t p) (κ' t p) (f t p) (V t p)
  have hq : ContDiffOn ℝ ∞ (Function.uncurry q) S := by
    have hd := hκ'.norm_sq ℝ
    have hdn (z : ℝ × (P × ℝ)) (hz : z ∈ S) : ‖κ' z.1 z.2‖ ^ 2 ≠ 0 :=
      pow_ne_zero _ (norm_ne_zero_iff.mpr (hκne z.2.1 z.1 hz.1))
    exact ((hκ'.inner ℝ hf).sub (contDiffOn_const.mul (hκ'.inner ℝ (hM'.clm_apply hV)))).div hd hdn
  have hq' : ContDiffOn ℝ ∞ (Function.uncurry (fun (z : ℝ × P) s => q z.1 (z.2, s)))
      (K ×ˢ univ) :=
    hq.comp (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk contDiffOn_snd))
      (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  exact (contDiffOn_phasePrimitive ((convex_Icc _ _).prod convex_univ)
      ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) hq').comp
      ((contDiffOn_fst.prodMk contDiffOn_snd.fst).prodMk contDiffOn_snd.snd)
      (fun z hz => ⟨⟨hz.1, mem_univ z.2.1⟩, mem_univ _⟩)

set_option maxHeartbeats 1200000 in
/-- The smooth phased solve has zero initial velocity and preserves periodicity
and phase mean. Its normalized pressure is jointly smooth on the same slab, and
its phase derivative gives the pressure term in the momentum equation. -/
theorem exists_jointSmooth_oscillatoryPhaseSolve
    {M : ℝ → P → E →L[ℝ] E} {κ : ℝ → P → E} {f : ℝ → (P × ℝ) → E} {T : ℝ}
    (hT : 0 < T)
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc 0 T ×ˢ (univ : Set P)))
    (hκ : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc 0 T ×ˢ (univ : Set P)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set (P × ℝ))))
    (hκ₀ : ∀ a, κ 0 a ≠ 0)
    (hκt : ∀ a t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun u => κ u a) (-((M t a).adjoint (κ t a))) (Icc 0 T) t)
    (hfper : ∀ a t, t ∈ Icc 0 T → Function.Periodic (fun s => f t (a, s)) 1)
    (hfmean : ∀ a t, t ∈ Icc 0 T → phaseMean (fun s => f t (a, s)) = 0) :
    ∃ (V : ℝ → (P × ℝ) → E) (Q : ℝ → (P × ℝ) → ℝ), V 0 = 0 ∧
      ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set (P × ℝ))) ∧
      Q = (fun t p => oscillatoryPhasePressure (M t p.1) (κ t p.1)
          (fun s => f t (p.1, s)) (fun s => V t (p.1, s)) p.2) ∧
      ContDiffOn ℝ ∞ (Function.uncurry Q) (Icc 0 T ×ˢ (univ : Set (P × ℝ))) ∧
      ∀ a t, t ∈ Icc 0 T →
        Function.Periodic (fun s => V t (a, s)) 1 ∧ phaseMean (fun s => V t (a, s)) = 0 ∧
        Function.Periodic (fun s => Q t (a, s)) 1 ∧ phaseMean (fun s => Q t (a, s)) = 0 ∧
        ∀ s, ⟪κ t a, V t (a, s)⟫_ℝ = 0 ∧
          HasDerivWithinAt (fun u => V u (a, s))
            (affineWaveAmplitudeOperator (M t a) (κ t a) (V t (a, s)) +
              oscillatoryTransverseProjection (κ t a) (f t (a, s))) (Icc 0 T) t ∧
          HasDerivAt (fun σ => Q t (a, σ))
            (oscillatoryPressureSlope (M t a) (κ t a) (f t (a, s)) (V t (a, s))) s ∧
          HasDerivWithinAt (fun u => V u (a, s))
            (f t (a, s) - M t a (V t (a, s)) -
              deriv (fun σ => Q t (a, σ)) s • κ t a) (Icc 0 T) t := by
  let I := Icc (0 : ℝ) T
  let S := I ×ˢ (univ : Set (P × ℝ))
  let K := I ×ˢ (univ : Set P)
  let M' (t : ℝ) (p : P × ℝ) := M t p.1
  let κ' (t : ℝ) (p : P × ℝ) := κ t p.1
  have hproj : ContDiffOn ℝ ∞ (fun z : ℝ × (P × ℝ) => (z.1, z.2.1)) S :=
    contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hprojMem : MapsTo (fun z : ℝ × (P × ℝ) => (z.1, z.2.1)) S K :=
    fun z hz => ⟨hz.1, mem_univ z.2.1⟩
  have hM' : ContDiffOn ℝ ∞ (Function.uncurry M') S := hM.comp hproj hprojMem
  have hκ' : ContDiffOn ℝ ∞ (Function.uncurry κ') S := hκ.comp hproj hprojMem
  obtain ⟨V, hV₀, hV, hsol⟩ := exists_jointSmooth_oscillatoryVelocity
    (M := M') (κ := κ') (f := f) hT hM' hκ' hf
    (fun p => hκ₀ p.1) (fun p t ht => hκt p.1 t ht)
  let A (t : ℝ) (a : P) := affineWaveAmplitudeOperator (M t a) (κ t a)
  let B (t : ℝ) (a : P) := oscillatoryTransverseProjection (κ t a)
  have hκne (a : P) (t : ℝ) (ht : t ∈ I) : κ t a ≠ 0 := (hsol (a, 0) t ht).1
  let Q (t : ℝ) (p : P × ℝ) := oscillatoryPhasePressure (M t p.1) (κ t p.1)
    (fun s => f t (p.1, s)) (fun s => V t (p.1, s)) p.2
  have hQ : ContDiffOn ℝ ∞ (Function.uncurry Q) S :=
    contDiffOn_oscillatoryPhasePressure (M := M) (κ := κ) (f := f) (V := V) hT hM hκ hf hV hκne
  refine ⟨V, Q, hV₀, hV, rfl, hQ, fun a t ht => ?_⟩
  have htime : Continuous (fun u : ℝ => (u, a)) := continuous_id.prodMk continuous_const
  have htimeMem : MapsTo (fun u => (u, a)) I K := fun _ hu => ⟨hu, mem_univ a⟩
  have hMa : ContinuousOn (fun u => M u a) I := hM.continuousOn.comp htime.continuousOn htimeMem
  have hκa : ContinuousOn (fun u => κ u a) I := hκ.continuousOn.comp htime.continuousOn htimeMem
  have hAt : ContinuousOn (fun u => A u a) I :=
    continuousOn_affineWaveAmplitudeOperator hMa hκa (hκne a)
  have hBt : ContinuousOn (fun u => B u a) I :=
    continuousOn_oscillatoryTransverseProjection hκa (hκne a)
  let F (u s : ℝ) := f u (a, s)
  let U (u s : ℝ) := V u (a, s)
  have hslice : Continuous (fun z : ℝ × ℝ => (z.1, (a, z.2))) :=
    continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
  have hmaps : MapsTo (fun z : ℝ × ℝ => (z.1, (a, z.2))) (I ×ˢ (univ : Set ℝ)) S :=
    fun z hz => ⟨hz.1, mem_univ (a, z.2)⟩
  have hF : ContinuousOn (Function.uncurry F) (I ×ˢ (univ : Set ℝ)) :=
    hf.continuousOn.comp hslice.continuousOn hmaps
  have hU : ContinuousOn (Function.uncurry U) (I ×ˢ (univ : Set ℝ)) :=
    hV.continuousOn.comp hslice.continuousOn hmaps
  have hU₀ (s : ℝ) : U 0 s = 0 := by simp [U, hV₀]
  have hUd (s u : ℝ) (hu : u ∈ I) :
      HasDerivWithinAt (fun v => U v s) (A u a (U u s) + B u a (F u s)) I u :=
    (hsol (a, s) u hu).2.2.1
  obtain ⟨hper, hmean⟩ := periodic_zeroMean_of_phase_linearODE
    (A := fun u => A u a) (B := fun u => B u a) (f := F) (V := U) (t := t)
    hT.le hAt hBt hF hU hU₀ hUd (hfper a) (hfmean a) ht
  have htSlice : Continuous (fun s : ℝ => (t, s)) := continuous_const.prodMk continuous_id
  have htMem : MapsTo (fun s : ℝ => (t, s)) univ (I ×ˢ (univ : Set ℝ)) :=
    fun s _ => ⟨ht, mem_univ s⟩
  have hVc : Continuous (U t) := continuousOn_univ.mp (hU.comp htSlice.continuousOn htMem)
  have hfc : Continuous (F t) := continuousOn_univ.mp (hF.comp htSlice.continuousOn htMem)
  obtain ⟨hQmean, hQper, hQ'⟩ := oscillatoryPhasePressure_spec (M t a) (κ t a)
    hfc hVc (hfper a t ht) hper (hfmean a t ht) hmean
  refine ⟨hper, hmean, hQper, hQmean, fun s =>
    ⟨(hsol (a, s) t ht).2.1, (hsol (a, s) t ht).2.2.1, hQ' s, ?_⟩⟩
  have hD : deriv (fun σ => Q t (a, σ)) s =
      oscillatoryPressureSlope (M t a) (κ t a) (f t (a, s)) (V t (a, s)) :=
    (hQ' s).deriv
  rw [hD]
  exact (hsol (a, s) t ht).2.2.2

end OscillatorySolve

end TorusEuler
