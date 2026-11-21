import TorusEuler.HierarchyPhysicalSolvers
import TorusEuler.LocalizedSeedRegularity
import TorusEuler.InductionPressure
import TorusEuler.TruncatedParentProjectedMomentum

/-! The concrete hierarchy coefficients of an actual periodic parent flow. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

/-- Restriction of a two-time flow retains all of its trajectories on the smaller set. -/
theorem IsLabelFlowOn.mono {U : Velocity} {X : ℝ → Velocity} {I J : Set ℝ}
    (hX : IsLabelFlowOn U X I) (hJI : J ⊆ I) : IsLabelFlowOn U X J :=
  ⟨fun s hs a => hX.initial s (hJI hs) a,
    fun s hs a t ht => (hX.trajectory s (hJI hs) a t (hJI ht)).mono hJI⟩

/-- The material acceleration is unchanged on any positive closed subslab. -/
theorem materialAcceleration_restrict_Icc
    {a b c d : ℝ} {u : Velocity} (hcd : c < d) (hac : a ≤ c) (hdb : d ≤ b)
    (hu : ContDiffOn ℝ 1 (Function.uncurry u) (Icc a b ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc c d) :
    materialAcceleration (Icc c d) u t = materialAcceleration (Icc a b) u t := by
  funext x
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  have hslice : ContDiffOn ℝ 1 (fun r => u r x) (Icc a b) :=
    hu.comp (contDiffOn_id.prodMk contDiffOn_const) (fun r hr => ⟨hr, mem_univ x⟩)
  have hderiv := ((hslice.differentiableOn (by simp)) t (hsub ht)).hasDerivWithinAt
  unfold materialAcceleration
  rw [(hderiv.mono hsub).derivWithin (uniqueDiffOn_Icc hcd t ht)]

/-- The true parent momentum residual is unchanged on any positive closed subslab. -/
theorem momentumResidual_restrict_Icc
    {a b c d : ℝ} {u : Velocity} {p : Pressure} (hcd : c < d) (hac : a ≤ c) (hdb : d ≤ b)
    (hu : ContDiffOn ℝ 1 (Function.uncurry u) (Icc a b ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc c d) :
    momentumResidual (Icc c d) u p t = momentumResidual (Icc a b) u p t := by
  funext x
  unfold momentumResidual
  rw [materialAcceleration_restrict_Icc hcd hac hdb hu ht]

/-- The periodic projected momentum also agrees on the restricted slab. -/
theorem closedSlabLerayMomentum_restrict_Icc
    {a b c d : ℝ} {u : Velocity} (hcd : c < d) (hac : a ≤ c) (hdb : d ≤ b)
    (hu : ContDiffOn ℝ 1 (Function.uncurry u) (Icc a b ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc c d) :
    closedSlabLerayMomentum c d u t = closedSlabLerayMomentum a b u t :=
  congrArg periodicLerayHolderLift (materialAcceleration_restrict_Icc hcd hac hdb hu ht)

/-- The inductive pressure budget and residual derivative yield the Eulerian
quadratic inequality used to construct the endpoint coercive coefficients. -/
theorem inductionPressure_eulerianCoercivity
    {U : Velocity} {p : Pressure} {freq : ℕ → ℝ} {j : ℕ} {I : Set ℝ} {t : ℝ} {x : Vec3}
    (hN : 4 ≤ freq 0) (hgrow : ∀ n, 2 * freq n ≤ freq (n + 1))
    (hpress : ∀ w : Vec3, ⟪fderiv ℝ (gradient (p t)) x w, w⟫_ℝ ≤
      (∑ i ∈ Finset.range j, (freq i)⁻¹) * ‖w‖ ^ 2)
    (hres : ‖fderiv ℝ (momentumResidual I U p t) x‖ ≤ 1 / 2)
    (w : Vec3) :
    ⟪(fderiv ℝ (gradient (p t)) x - fderiv ℝ (momentumResidual I U p t) x) w, w⟫_ℝ ≤
      ‖w‖ ^ 2 := by
  let DR := fderiv ℝ (momentumResidual I U p t) x
  have hNpos : 0 < freq 0 := (by norm_num : (0 : ℝ) < 4).trans_le hN
  have hsum := (inductionPressure_sum_le hNpos hgrow j).trans
    ((div_le_iff₀ hNpos).2 (by linarith : (2 : ℝ) ≤ (1 / 2) * freq 0))
  have hpressure := (hpress w).trans (mul_le_mul_of_nonneg_right hsum (sq_nonneg _))
  have hresidual : -⟪DR w, w⟫_ℝ ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2 := by
    rw [← inner_neg_left]
    calc
      _ ≤ ‖-DR w‖ * ‖w‖ := real_inner_le_norm _ _
      _ ≤ (‖DR‖ * ‖w‖) * ‖w‖ := by
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_right (DR.le_opNorm w) (norm_nonneg _)
      _ = ‖DR‖ * ‖w‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hres (sq_nonneg _)
  rw [_root_.sub_apply, inner_sub_left]
  change ⟪fderiv ℝ (gradient (p t)) x w, w⟫_ℝ - ⟪DR w, w⟫_ℝ ≤ ‖w‖ ^ 2
  linarith

end TorusEuler

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)

/-- Embed a smooth periodic label field as a phase-independent profile. -/
def ofLabelField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : Vec3)
    (f : ℝ → Vec3 → E) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (f t)) : HierarchyTwistedProfile T k E := by
  let p (z : HierarchyProfilePoint) := f z.1 z.2.1
  have hp : ContDiffOn ℝ ∞ p (hierarchyProfileSlab T) :=
    hf.comp (contDiffOn_fst.prodMk contDiffOn_snd.fst) (fun z hz => ⟨hz.1, mem_univ z.2.1⟩)
  let w := HierarchySmoothProfile.ofSmooth p hp
  have hval (x : HierarchyProfilePoint) (hx : x ∈ hierarchyProfileSlab T) :
      w.val x = p x := HierarchySmoothProfile.ofSmooth_apply hp hx
  apply ofPhaseIndependent w
  · intro x hx s
    exact (hval (x.1,x.2.1,s) ⟨hx.1, mem_univ _⟩).trans (hval x hx).symm
  · intro t ht n a
    change w.val (t, a + latticeVector n, 0) = w.val (t, a, 0)
    rw [hval (t, a + latticeVector n, 0) ⟨ht, mem_univ _⟩,
      hval (t, a, 0) ⟨ht, mem_univ _⟩]
    exact hper t ht n a

theorem ofLabelField_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : Vec3)
    (f : ℝ → Vec3 → E) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (f t)) {x : HierarchyProfilePoint}
    (hx : x ∈ hierarchyProfileSlab T) : (ofLabelField k f hf hper).val.val.val x = f x.1 x.2.1 := by
  have hs : ContDiffOn ℝ ∞ (fun z : HierarchyProfilePoint => f z.1 z.2.1) (hierarchyProfileSlab T) :=
    hf.comp (contDiffOn_fst.prodMk contDiffOn_snd.fst) (fun z hz => ⟨hz.1, mem_univ z.2.1⟩)
  exact HierarchySmoothProfile.ofSmooth_apply hs hx

private def descendLabelField {E : Type*} (f : ℝ → Vec3 → E) : ℝ × UnitAddTorus (Fin 3) → E :=
  fun z => f z.1 (toUnitTorus_surjective z.2).choose

private theorem descendLabelField_eval {E : Type*} {f : ℝ → Vec3 → E}
    (hper : ∀ t ∈ I, SpatiallyPeriodic (f t)) {t : ℝ} (ht : t ∈ I) (a : Vec3) :
    descendLabelField f (t, toUnitTorus a) = f t a := by
  obtain ⟨n, hn⟩ := (toUnitTorus_eq_iff _ _).mp (toUnitTorus_surjective (toUnitTorus a)).choose_spec
  change f t (toUnitTorus_surjective (toUnitTorus a)).choose = _
  rw [hn, hper t ht n a]

private theorem fderiv_lattice_equivariant {f : Vec3 → Vec3}
    (hf : ∀ (n : Fin 3 → ℤ) a, f (a + latticeVector n) = f a + latticeVector n) :
    SpatiallyPeriodic (fderiv ℝ f) := by
  intro n a
  have h := congrArg (fun q : Vec3 → Vec3 => fderiv ℝ q a) (funext (hf n))
  simpa only [fderiv_comp_add_right, fderiv_add_const] using h

private theorem fderiv_label_periodic {f : Vec3 → Vec3} (hf : SpatiallyPeriodic f) :
    SpatiallyPeriodic (fderiv ℝ f) := by
  intro n a
  have h := congrArg (fun q : Vec3 → Vec3 => fderiv ℝ q a) (funext (hf n))
  simpa only [fderiv_comp_add_right] using h

/-- Exact coefficients with their physical values on the parent label slab. -/
structure ParentGeometry (hT : 0 < T) (U : Velocity) (X : ℝ → Velocity) (k : Vec3) where
  inverse : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
  strain : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
  covector : HierarchyTwistedProfile T k Vec3
  mean : MeanCoefficients inverse strain
  oscillation : TransverseCoefficients strain covector
  inverse_value : ∀ x ∈ hierarchyProfileSlab T,
    inverse.val.val.val x = fderiv ℝ (X x.1 0) (X 0 x.1 x.2.1)
  strain_value : ∀ x ∈ hierarchyProfileSlab T,
    strain.val.val.val x = fderiv ℝ (U x.1) (X 0 x.1 x.2.1)
  covector_value : ∀ x ∈ hierarchyProfileSlab T,
    covector.val.val.val x = labelWaveVector X 0 x.2.1 k x.1
  deformation_value : ∀ t ∈ I, ∀ a, mean.deformation (t, toUnitTorus a) = fderiv ℝ (X 0 t) a

set_option maxHeartbeats 2800000 in
/-- The actual flow, deformation, strain and transported covector satisfy the
physical solvers' coefficient hypotheses. The Eulerian coercivity input is
the pressure Hessian minus the gradient of the parent's actual residual. -/
theorem exists_parentGeometry_withBounds {U : Velocity} {p : Pressure} {X : ℝ → Velocity} {k : Vec3}
    {D L : ℝ} (hT : 0 < T) (hX : IsLabelFlowOn U X I) (hk : k ≠ 0)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hp : ∀ t ∈ I, ∀ x, DifferentiableAt ℝ (gradient (p t)) x)
    (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hG : ∀ t ∈ I, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D)
    (hM : ∀ t ∈ I, ∀ x, ‖fderiv ℝ (U t) x‖ ≤ L)
    (hupper : ∀ t ∈ I, ∀ x v : Vec3,
      ⟪(fderiv ℝ (gradient (p t)) x - fderiv ℝ (momentumResidual I U p t) x) v, v⟫_ℝ ≤ ‖v‖ ^ 2) :
    ∃ d : ParentGeometry hT U X k, d.mean.inverse_bound = D ∧ d.mean.strain_bound = L := by
  let F (t : ℝ) (a : Vec3) := fderiv ℝ (X 0 t) a
  let G (t : ℝ) (a : Vec3) := fderiv ℝ (X t 0) (X 0 t a)
  let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a)
  let κ (t : ℝ) (a : Vec3) := labelWaveVector X 0 a k t
  let Mt (t : ℝ) (a : Vec3) := derivWithin (fun r => M r a) I t
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, hT.le⟩
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) J := hU.of_le (by simp)
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hFsm : ContDiffOn ℝ ∞ (Function.uncurry F) J :=
    hX.contDiffOn_forwardLabelDerivative hT hU hper
  have hGsm : ContDiffOn ℝ ∞ (Function.uncurry G) J :=
    hX.contDiffOn_inverseLabelDerivative hT hU hper
  have hMsm : ContDiffOn ℝ ∞ (Function.uncurry M) J :=
    hX.contDiffOn_materialGradient hT hU hper
  have hκsm : ContDiffOn ℝ ∞ (Function.uncurry κ) J :=
    hX.contDiffOn_transportedCovector hT hU hper k
  have hFper (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (F t) :=
    fderiv_lattice_equivariant (hX.add_latticeVector hK hper h0 ht)
  have hGper (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (G t) := by
    intro n a
    change (fderiv ℝ (X t 0)) (X 0 t (a + latticeVector n)) = G t a
    rw [hX.add_latticeVector hK hper h0 ht n a,
      fderiv_lattice_equivariant (hX.add_latticeVector hK hper ht h0) n (X 0 t a)]
  have hMper (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (M t) := by
    intro n a
    change fderiv ℝ (U t) (X 0 t (a + latticeVector n)) = M t a
    rw [hX.add_latticeVector hK hper h0 ht n a, fderiv_label_periodic (hper t ht) n (X 0 t a)]
  have hκper (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (κ t) := by
    intro n a
    exact congrArg (fun g : Vec3 →L[ℝ] Vec3 => g.adjoint k) (hGper t ht n a)
  have hMtime (a : Vec3) : ContDiffOn ℝ ∞ (fun r => M r a) I :=
    hMsm.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hr => ⟨hr, mem_univ a⟩)
  have hMtper (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (Mt t) := by
    intro n a
    exact derivWithin_congr (fun r hr => hMper r hr n a) (hMper t ht n a)
  have hMtcont (a : Vec3) : ContinuousOn (fun r => Mt r a) I :=
    (hMtime a).continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by simp)
  let Gp := ofLabelField k G hGsm hGper
  let Mp := ofLabelField k M hMsm hMper
  let κp := ofLabelField k κ hκsm hκper
  let Ft := descendLabelField F
  let Gt := descendLabelField G
  let Mat := descendLabelField M
  let Mdt := descendLabelField Mt
  have hFd (t : ℝ) (ht : t ∈ I) (a : Vec3) : Ft (t,toUnitTorus a) = F t a :=
    descendLabelField_eval hFper ht a
  have hGd (t : ℝ) (ht : t ∈ I) (a : Vec3) : Gt (t,toUnitTorus a) = G t a :=
    descendLabelField_eval hGper ht a
  have hMd (t : ℝ) (ht : t ∈ I) (a : Vec3) : Mat (t,toUnitTorus a) = M t a :=
    descendLabelField_eval hMper ht a
  have hMtd (t : ℝ) (ht : t ∈ I) (a : Vec3) : Mdt (t,toUnitTorus a) = Mt t a :=
    descendLabelField_eval hMtper ht a
  let d : MeanCoefficients Gp Mp :=
    { deformation := Ft
      inverse := Gt
      strain := Mat
      strain_time := Mdt
      deformation_smooth := hFsm.congr fun x hx => hFd x.1 hx.1 x.2
      strain_smooth := hMsm.congr fun x hx => hMd x.1 hx.1 x.2
      inverse_value := fun x hx => (ofLabelField_eval k G hGsm hGper hx).trans (hGd x.1 hx.1 x.2.1).symm
      strain_value := fun x hx => (ofLabelField_eval k M hMsm hMper hx).trans (hMd x.1 hx.1 x.2.1).symm
      deformation_equation := by
        intro b t ht
        obtain ⟨a,rfl⟩ := toUnitTorus_surjective b
        rw [hMd t ht a, hFd t ht a]
        exact ((hX.labelDerivative_evolves hT hU₂ hper h0 a).2 t ht).congr_of_mem
          (fun r hr => hFd r hr a) ht
      strain_equation := by
        intro b t ht
        obtain ⟨a,rfl⟩ := toUnitTorus_surjective b
        rw [hMtd t ht a]
        exact (((hMtime a).differentiableOn (by simp) t ht).hasDerivWithinAt).congr_of_mem
          (fun r hr => hMd r hr a) ht
      strain_time_continuous := by
        intro b
        obtain ⟨a,rfl⟩ := toUnitTorus_surjective b
        exact (hMtcont a).congr (fun r hr => hMtd r hr a)
      inverse_left := by
        intro b t ht
        obtain ⟨a,rfl⟩ := toUnitTorus_surjective b
        rw [hGd t ht a, hFd t ht a]
        exact (hX.labelDerivative_inverse hT hU₂ hper h0 ht a).1
      inverse_right := by
        intro b t ht
        obtain ⟨a,rfl⟩ := toUnitTorus_surjective b
        rw [hGd t ht a, hFd t ht a]
        exact (hX.labelDerivative_inverse hT hU₂ hper h0 ht a).2
      inverse_bound := D
      strain_bound := L
      inverse_bound_ge_one := hD
      strain_bound_nonneg := hL
      norm_inverse_le := by
        intro b t ht
        obtain ⟨a,rfl⟩ := toUnitTorus_surjective b
        rw [hGd t ht a]
        exact hG t ht a
      norm_strain_le := by
        intro b t ht
        obtain ⟨a,rfl⟩ := toUnitTorus_surjective b
        rw [hMd t ht a]
        exact hM t ht (X 0 t a)
      coercivity := by
        intro b t ht v
        obtain ⟨a,rfl⟩ := toUnitTorus_surjective b
        rw [hMd t ht a, hMtd t ht a]
        change ⟪endpointHessian (fderiv ℝ (U t) (X 0 t a))
          (derivWithin (fun r => fderiv ℝ (U r) (X 0 r a)) I t) v, v⟫_ℝ ≤ _
        rw [endpointHessian_eq_pressureHessian_sub_residualGradient hT ht hU₂
          (hX.trajectory 0 h0 a t ht) (hp t ht (X 0 t a))]
        exact hupper t ht (X 0 t a) v }
  let w : TransverseCoefficients Mp κp :=
    { strain := M
      covector := κ
      strain_smooth := hMsm
      covector_smooth := hκsm
      strain_value := fun _ hx => ofLabelField_eval k M hMsm hMper hx
      covector_value := fun _ hx => ofLabelField_eval k κ hκsm hκper hx
      initial_nonzero := fun a => LocalizedAmplitude.transportedCovector_ne_zero_of_parent hT hX hU hper hk 0 h0 a
      covector_equation := fun a t ht => hX.hasDerivWithinAt_labelWaveVector hT hU₂ hper h0 ht a k }
  exact ⟨⟨Gp,Mp,κp,d,w,fun _ hx => ofLabelField_eval k G hGsm hGper hx,
    fun _ hx => ofLabelField_eval k M hMsm hMper hx, fun _ hx => ofLabelField_eval k κ hκsm hκper hx,
    hFd⟩, rfl, rfl⟩


/-- The parent flow gives coefficient profiles for both hierarchy solvers. -/
theorem exists_parentGeometry {U : Velocity} {p : Pressure} {X : ℝ → Velocity} {k : Vec3}
    {D L : ℝ} (hT : 0 < T) (hX : IsLabelFlowOn U X I) (hk : k ≠ 0)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hp : ∀ t ∈ I, ∀ x, DifferentiableAt ℝ (gradient (p t)) x)
    (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hG : ∀ t ∈ I, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D)
    (hM : ∀ t ∈ I, ∀ x, ‖fderiv ℝ (U t) x‖ ≤ L)
    (hupper : ∀ t ∈ I, ∀ x v : Vec3,
      ⟪(fderiv ℝ (gradient (p t)) x - fderiv ℝ (momentumResidual I U p t) x) v, v⟫_ℝ ≤ ‖v‖ ^ 2) :
    Nonempty (ParentGeometry hT U X k) := by
  obtain ⟨d, _, _⟩ := exists_parentGeometry_withBounds hT hX hk hU hper hp hD hL hG hM hupper
  exact ⟨d⟩


private theorem profileReflectionParity_of_slab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Vec3 → E} (q : HierarchySmoothProfile T E)
    (hq : ∀ x ∈ hierarchyProfileSlab T, q.val x = f x.1 x.2.1) {sign : ℝ}
    (hf : ∀ t ∈ I, ∀ a, f t (-a) = sign • f t a) : HierarchyProfileReflectionParity sign q.val := by
  intro x
  by_cases hx : x ∈ hierarchyProfileSlab T
  · rw [hq _ (hierarchyProfileReflection_mem_slab.mpr hx), hq _ hx]
    exact hf x.1 hx.1 x.2.1
  · rw [HierarchySmoothProfile.eq_zero_outside q (fun h => hx (hierarchyProfileReflection_mem_slab.mp h)),
      HierarchySmoothProfile.eq_zero_outside q hx, smul_zero]

/-- The actual residual pulled back along the forward parent flow is an
admissible mean source, with its value independent of phase. -/
theorem exists_pulledBackParentResidual {U : Velocity} {p : Pressure} {X : ℝ → Velocity} {k : Vec3}
    (hT : 0 < T) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hRs : ContDiffOn ℝ ∞ (Function.uncurry (momentumResidual I U p)) J)
    (hRp : ∀ t ∈ I, SpatiallyPeriodic (momentumResidual I U p t))
    (d : ParentGeometry hT U X k) :
    ∃ R : HierarchyTwistedProfile T k Vec3,
      (twistedHierarchyOperators hT d.inverse d.strain d.covector).average R = R ∧
      (∀ x ∈ hierarchyProfileSlab T, R.val.val.val x = momentumResidual I U p x.1 (X 0 x.1 x.2.1)) ∧
      ((∀ t ∈ I, Function.Odd (U t)) → (∀ t ∈ I, Function.Odd (momentumResidual I U p t)) →
        HierarchyProfileReflectionParity (-1) R.val.val.val) := by
  let r (t : ℝ) (a : Vec3) := momentumResidual I U p t (X 0 t a)
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, hT.le⟩
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hs : ContDiffOn ℝ ∞ (Function.uncurry r) J :=
    hRs.comp (contDiffOn_fst.prodMk (hX.contDiffOn_forwardLabelFlow hT hU hper))
      (fun z hz => ⟨hz.1, mem_univ (X 0 z.1 z.2)⟩)
  have hp (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (r t) := by
    intro n a
    change momentumResidual I U p t (X 0 t (a + latticeVector n)) = r t a
    rw [hX.add_latticeVector hK hper h0 ht n a, hRp t ht n (X 0 t a)]
  let R := ofLabelField k r hs hp
  have hval (x : HierarchyProfilePoint) (hx : x ∈ hierarchyProfileSlab T) :
      R.val.val.val x = r x.1 x.2.1 := ofLabelField_eval k r hs hp hx
  refine ⟨R, Subtype.ext (HierarchyPeriodicProfile.profilePhaseAverage_eq_self_of_independent hT R.val
    fun x hx s => (hval (x.1,x.2.1,s) ⟨hx.1, mem_univ _⟩).trans (hval x hx).symm), hval, ?_⟩
  intro hodd hRodd
  apply profileReflectionParity_of_slab R.val.val hval
  intro t ht a
  change momentumResidual I U p t (X 0 t (-a)) = (-1 : ℝ) • momentumResidual I U p t (X 0 t a)
  rw [hX.odd hK hodd h0 ht a, hRodd t ht]
  exact (neg_one_smul ℝ _).symm

/-- The deformation and coframe preserve the reflection of an odd parent. -/
theorem ParentGeometry.reflection {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {hT : 0 < T}
    (d : ParentGeometry hT U X k) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hodd : ∀ t ∈ I, Function.Odd (U t)) :
    HierarchyProfileReflectionParity 1 d.inverse.val.val.val ∧
    HierarchyProfileReflectionParity 1 d.strain.val.val.val ∧
    HierarchyProfileReflectionParity 1 d.covector.val.val.val ∧
    ∀ t ∈ I, Function.Even (fun a => d.mean.deformation (t,toUnitTorus a)) := by
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, hT.le⟩
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hGeven (t : ℝ) (ht : t ∈ I) : Function.Even (fun a => fderiv ℝ (X t 0) (X 0 t a)) := by
    intro a
    change fderiv ℝ (X t 0) (X 0 t (-a)) = fderiv ℝ (X t 0) (X 0 t a)
    rw [hX.odd hK hodd h0 ht a, even_fderiv_of_odd (hX.odd hK hodd ht h0)]
  have hParity (t : ℝ) (ht : t ∈ I) := hX.even_materialGradient_and_labelWaveVector hK hodd h0 ht k
  refine ⟨profileReflectionParity_of_slab (f := fun t a => fderiv ℝ (X t 0) (X 0 t a))
    d.inverse.val.val d.inverse_value (fun t ht a => by
    rw [one_smul]; exact hGeven t ht a),
    profileReflectionParity_of_slab (f := fun t a => fderiv ℝ (U t) (X 0 t a))
      d.strain.val.val d.strain_value (fun t ht a => by
      rw [one_smul]; exact (hParity t ht).1 a),
    profileReflectionParity_of_slab (f := fun t a => labelWaveVector X 0 a k t)
      d.covector.val.val d.covector_value (fun t ht a => by
      rw [one_smul]; exact (hParity t ht).2 a), ?_⟩
  intro t ht a
  change d.mean.deformation (t,toUnitTorus (-a)) = d.mean.deformation (t,toUnitTorus a)
  rw [d.deformation_value t ht, d.deformation_value t ht]
  exact even_fderiv_of_odd (hX.odd hK hodd h0 ht) a

/-- The exact selected mean coefficients are even for an odd parent. -/
theorem ParentGeometry.meanEven {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {hT : 0 < T}
    (d : ParentGeometry hT U X k) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hodd : ∀ t ∈ I, Function.Odd (U t)) : d.mean.Even := by
  obtain ⟨hG, hM, _, hF⟩ := d.reflection hX hU hper hodd
  refine ⟨hF, ?_, ?_⟩
  · intro t ht a
    have h := hG (t,a,0)
    simp only [hierarchyProfileReflection_apply, neg_zero, one_smul] at h
    change d.inverse.val.val.val (t,-a,0) = d.inverse.val.val.val (t,a,0) at h
    rw [d.mean.inverse_value _ ⟨ht, mem_univ _⟩, d.mean.inverse_value _ ⟨ht, mem_univ _⟩] at h
    exact h
  · intro t ht a
    have h := hM (t,a,0)
    simp only [hierarchyProfileReflection_apply, neg_zero, one_smul] at h
    change d.strain.val.val.val (t,-a,0) = d.strain.val.val.val (t,a,0) at h
    rw [d.mean.strain_value _ ⟨ht, mem_univ _⟩, d.mean.strain_value _ ⟨ht, mem_univ _⟩] at h
    exact h

/-- On the transported Eulerian graph, the coframe and covector are the
Jacobian of the actual inverse chart and its transpose applied to the carrier. -/
theorem ParentGeometry.inverseGraph_values {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {hT : 0 < T}
    (d : ParentGeometry hT U X k) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) :
    (∀ t ∈ I, Function.Surjective (X t 0)) ∧
    ∀ t ∈ I, ∀ x s, d.inverse.val.val.val (t, X t 0 x, s) = fderiv ℝ (X t 0) x ∧
      d.covector.val.val.val (t, X t 0 x, s) = (fderiv ℝ (X t 0) x).adjoint k := by
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, hT.le⟩
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  refine ⟨fun t ht a => ⟨X 0 t a, (hX.inverse hK h0 ht).1 a⟩, ?_⟩
  intro t ht x s
  have hInv := (hX.inverse hK h0 ht).2 x
  have hx : (t, X t 0 x, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  rw [d.inverse_value _ hx, d.covector_value _ hx]
  simp [labelWaveVector, hInv]

end

end TorusEuler.HierarchyTwistedProfile
