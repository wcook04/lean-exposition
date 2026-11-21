import Breakdown.Cert.Nodes
import Breakdown.Cert.PeriodIntegral
import Breakdown.FreqTr.Realization
import Breakdown.Cert.TestDense
import Breakdown.Cert.ProjectionSpec
import Breakdown.Cert.JointRepresentative

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.Invariance

theorem coe_circleRep (t : TimeCircle) : ((circleRep t : ℝ) : TimeCircle) = t :=
  AddCircle.coe_equivIco

theorem periodic_eq {β : Type*} {F : ℝ → Space → β} (hF : IsTimePeriodic F) {s σ : ℝ}
    (h : (s : TimeCircle) = σ) : F s = F σ := by
  have h0 : ((s - σ : ℝ) : TimeCircle) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h0
  have hs : s = σ + n • (1 : ℝ) := by rw [hn]; ring
  funext y
  rw [hs]
  exact (Function.Periodic.zsmul (f := fun τ => F τ y) (fun τ => hF τ y) n) σ

theorem periodic_shift {β : Type*} {F : ℝ → Space → β} (hF : IsTimePeriodic F) (t : TimeCircle)
    (a : ℝ) : F (circleRep (t + (a : TimeCircle))) = F (circleRep t + a) :=
  periodic_eq hF (by rw [coe_circleRep, AddCircle.coe_add, coe_circleRep])

theorem periodic_coe {β : Type*} {F : ℝ → Space → β} (hF : IsTimePeriodic F) (σ : ℝ) :
    F (circleRep (σ : TimeCircle)) = F σ :=
  periodic_eq hF (coe_circleRep _)

theorem mem_invariantHH_of {Γ : Set Symmetry} {f : HH}
    (h : ∀ γ ∈ Γ, (shiftLp γ.2 : HH →L[ℝ] HH) f = rotHH γ.1 f) : f ∈ invariantHH Γ :=
  (Submodule.mem_iInf _).2 fun γ => (Submodule.mem_iInf _).2 fun hγ =>
    LinearMap.mem_ker.2 (sub_eq_zero.2 (h γ hγ))

theorem shift_of_mem {Γ : Set Symmetry} {f : HH} (hf : f ∈ invariantHH Γ) {γ : Symmetry}
    (hγ : γ ∈ Γ) : (shiftLp γ.2 : HH →L[ℝ] HH) f = rotHH γ.1 f := by
  have h0 := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf γ) hγ)
  exact sub_eq_zero.1 h0

theorem shift_coe (a : ℝ) (f : HH) : ((shiftLp a : HH →L[ℝ] HH) f : TimeCircle → HBar) =ᵐ[volume]
    fun t => (f : TimeCircle → HBar) (t + (a : TimeCircle)) := by
  have hw : (shiftLp a : HH →L[ℝ] HH) f = Lp.compMeasurePreserving
      (fun t : TimeCircle => t + (a : TimeCircle)) (measurePreserving_add_right volume (a : TimeCircle)) f :=
    rfl
  rw [hw]
  exact Lp.coeFn_compMeasurePreserving _ _

theorem rot_coe (R : Space ≃ₗᵢ[ℝ] Space) (f : HH) : ((rotHH R f : HH) : TimeCircle → HBar) =ᵐ[volume]
    fun t => rotX R ((f : TimeCircle → HBar) t) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem ae_shift {p : TimeCircle → Prop} (a : ℝ) (h : ∀ᵐ t : TimeCircle, p t) :
    ∀ᵐ t : TimeCircle, p (t + (a : TimeCircle)) :=
  (measurePreserving_add_right (volume : Measure TimeCircle) (a : TimeCircle)).quasiMeasurePreserving.ae h

theorem shift_eq_rot_of_ae {a : ℝ} {R : Space ≃ₗᵢ[ℝ] Space} {f : HH}
    (h : ∀ᵐ t : TimeCircle, (f : TimeCircle → HBar) (t + (a : TimeCircle)) =
      rotX R ((f : TimeCircle → HBar) t)) :
    (shiftLp a : HH →L[ℝ] HH) f = rotHH R f := by
  refine Lp.ext ?_
  filter_upwards [shift_coe a f, rot_coe R f, h] with t h1 h2 h3
  exact h1.trans (h3.trans h2.symm)

theorem ae_of_shift_eq {a : ℝ} {R : Space ≃ₗᵢ[ℝ] Space} {f : HH}
    (h : (shiftLp a : HH →L[ℝ] HH) f = rotHH R f) :
    ∀ᵐ t : TimeCircle, (f : TimeCircle → HBar) (t + (a : TimeCircle)) =
      rotX R ((f : TimeCircle → HBar) t) := by
  filter_upwards [shift_coe a f, rot_coe R f] with t h1 h2
  exact h1.symm.trans ((congrArg (fun w : HH => (w : TimeCircle → HBar) t) h).trans h2)

theorem circleLpOrZero_shift {a : ℝ} {R : Space ≃ₗᵢ[ℝ] Space} {φ : TimeCircle → HBar}
    (h : ∀ᵐ t : TimeCircle, φ (t + (a : TimeCircle)) = rotX R (φ t)) :
    (shiftLp a : HH →L[ℝ] HH) (circleLpOrZero φ) = rotHH R (circleLpOrZero φ) := by
  by_cases hm : MemLp φ 2 volume
  · refine shift_eq_rot_of_ae ?_
    have e0 : circleLpOrZero φ = hm.toLp φ := dif_pos hm
    have e : ((circleLpOrZero φ : HH) : TimeCircle → HBar) =ᵐ[volume] φ :=
      (Filter.EventuallyEq.of_eq (congrArg (fun w : HH => (w : TimeCircle → HBar)) e0)).trans
        hm.coeFn_toLp
    filter_upwards [e, ae_shift a e, h] with t b1 b2 b3
    exact b2.trans (b3.trans (congrArg (rotX R) b1.symm))
  · have e0 : circleLpOrZero φ = 0 := dif_neg hm
    calc (shiftLp a : HH →L[ℝ] HH) (circleLpOrZero φ) = (shiftLp a : HH →L[ℝ] HH) 0 := congrArg _ e0
      _ = 0 := map_zero _
      _ = rotHH R 0 := (map_zero _).symm
      _ = rotHH R (circleLpOrZero φ) := congrArg _ e0.symm

theorem grad_shift {Γ : Set Symmetry} {u : XX} (hu : IsInvariantXX Γ u) {γ : Symmetry}
    (hγ : γ ∈ Γ) : ∀ᵐ t : TimeCircle, gradPart ((u : TimeCircle → XBar) (t + (γ.2 : TimeCircle))) =
      rotX γ.1 (gradPart ((u : TimeCircle → XBar) t)) := by
  have e : ((gradCLM u : HH) : TimeCircle → HBar) =ᵐ[volume]
      fun t => gradPart ((u : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  filter_upwards [e, ae_shift γ.2 e, ae_of_shift_eq (shift_of_mem hu hγ)] with t b1 b2 b3
  exact b2.symm.trans (b3.trans (congrArg (rotX γ.1) b1))

theorem pushForward_symm (R : Space ≃ₗᵢ[ℝ] Space) (F : Space → Space) :
    pushForward R.symm (pushForward R F) = F := by
  funext y
  simp [pushForward]

theorem memLp_pushForward (R : Space ≃ₗᵢ[ℝ] Space) {F : Space → Space} (hF : MemLp F 2 volume) :
    MemLp (pushForward R F) 2 volume :=
  ((R.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).comp_memLp'
    (hF.comp_measurePreserving R.symm.measurePreserving)

theorem solField_congr {F G : Space → Space} (h : F =ᵐ[volume] G) : solField F = solField G := by
  by_cases hF : MemLp F 2 volume
  · have hG : MemLp G 2 volume := (memLp_congr_ae h).1 hF
    simp only [solField, toLpOrZero, dif_pos hF, dif_pos hG]
    rw [MemLp.toLp_congr hF hG h]
  · have hG : ¬ MemLp G 2 volume := fun hG => hF ((memLp_congr_ae h).2 hG)
    simp only [solField, toLpOrZero, dif_neg hF, dif_neg hG]

theorem solField_sub {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    solField (f - g) = solField f - solField g := by
  simp only [solField, toLpOrZero, dif_pos hf, dif_pos hg, dif_pos (hf.sub hg)]
  rw [MemLp.toLp_sub hf hg, map_sub]

theorem rotX_rotX_symm (R : Space ≃ₗᵢ[ℝ] Space) (x : HBar) : rotX R (rotX R.symm x) = x := by
  apply Subtype.ext
  rw [(rotation_holds R).1, (rotation_holds R.symm).1]
  exact Internal.Rotation.rotL2_rotL2_symm fieldOpRealized_holds R x

theorem solField_pushForward
    (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    (R : Space ≃ₗᵢ[ℝ] Space) (F : Space → Space) :
    solField (pushForward R F) = rotX R (solField F) := by
  by_cases hF : MemLp F 2 volume
  · have hG := memLp_pushForward R hF
    refine ext_inner_right ℝ fun x => ?_
    have e1 : inner ℝ (rotX R (solField F)) x = inner ℝ (solField F) (rotX R.symm x) :=
      (congrArg (fun z => inner ℝ (rotX R (solField F)) z) (rotX_rotX_symm R x).symm).trans
        ((rotX R).inner_map_map _ _)
    have k3 : (toPhysH (rotX R.symm x) : Space → Space) =ᵐ[volume]
        pushForward R.symm (toPhysH x : Space → Space) := by
      have e : toPhysH (rotX R.symm x) = toPhys (rotL2 R.symm (x : L2C)) :=
        congrArg toPhys ((rotation_holds R.symm).1 x)
      exact (Filter.EventuallyEq.of_eq (congrArg (fun w : L2R => (w : Space → Space)) e)).trans
        (Internal.BilinRotate.toPhys_rotL2 fieldOpRealized_holds R.symm x)
    have e3 : ∀ y, inner ℝ (pushForward R F y) ((toPhysH x : Space → Space) y) =
        (fun z => inner ℝ (F z) (pushForward R.symm (toPhysH x : Space → Space) z)) (R.symm y) := by
      intro y
      simp only [pushForward, LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]
      rw [← R.symm.inner_map_map (R (F (R.symm y))), LinearIsometryEquiv.symm_apply_apply]
    have esG : solField (pushForward R F) = solProj (hG.toLp (pushForward R F)) :=
      congrArg solProj (dif_pos hG : toLpOrZero 2 (pushForward R F) = hG.toLp (pushForward R F))
    have esF : solField F = solProj (hF.toLp F) :=
      congrArg solProj (dif_pos hF : toLpOrZero 2 F = hF.toLp F)
    have lhs : inner ℝ (solField (pushForward R F)) x =
        ∫ y, inner ℝ (pushForward R F y) ((toPhysH x : Space → Space) y) := by
      refine (congrArg (fun w => inner ℝ w x) esG).trans ((hP _ x).trans ((L2.inner_def _ _).trans ?_))
      refine integral_congr_ae ?_
      filter_upwards [hG.coeFn_toLp] with y hy
      exact congrArg (fun v => inner ℝ v ((toPhysH x : Space → Space) y)) hy
    have rhs : inner ℝ (solField F) (rotX R.symm x) =
        ∫ z, inner ℝ (F z) ((toPhysH (rotX R.symm x) : Space → Space) z) := by
      refine (congrArg (fun w => inner ℝ w (rotX R.symm x)) esF).trans
        ((hP _ _).trans ((L2.inner_def _ _).trans ?_))
      refine integral_congr_ae ?_
      filter_upwards [hF.coeFn_toLp] with y hy
      exact congrArg (fun v => inner ℝ v ((toPhysH (rotX R.symm x) : Space → Space) y)) hy
    have hcv : ∫ y, (fun z => inner ℝ (F z) (pushForward R.symm (toPhysH x : Space → Space) z))
        (R.symm y) = ∫ z, inner ℝ (F z) (pushForward R.symm (toPhysH x : Space → Space) z) :=
      (LinearIsometryEquiv.measurePreserving R.symm).integral_comp
        R.symm.toHomeomorph.measurableEmbedding
        (fun z => inner ℝ (F z) (pushForward R.symm (toPhysH x : Space → Space) z))
    have hk : ∫ z, inner ℝ (F z) (pushForward R.symm (toPhysH x : Space → Space) z) =
        ∫ z, inner ℝ (F z) ((toPhysH (rotX R.symm x) : Space → Space) z) := by
      refine integral_congr_ae ?_
      filter_upwards [k3] with z hz
      exact congrArg (fun v => inner ℝ (F z) v) hz.symm
    exact lhs.trans ((integral_congr_ae (Filter.Eventually.of_forall e3)).trans
      (hcv.trans (hk.trans (rhs.symm.trans e1.symm))))
  · have hG : ¬ MemLp (pushForward R F) 2 volume := fun hG =>
      hF (by simpa [pushForward_symm] using memLp_pushForward R.symm hG)
    have esG : solField (pushForward R F) = 0 :=
      (congrArg solProj (dif_neg hG : toLpOrZero 2 (pushForward R F) = 0)).trans (map_zero _)
    have esF : solField F = 0 :=
      (congrArg solProj (dif_neg hF : toLpOrZero 2 F = 0)).trans (map_zero _)
    exact esG.trans ((map_zero (rotX R)).symm.trans (congrArg (rotX R) esF.symm))

theorem sum_coord_rot (R : Space ≃ₗᵢ[ℝ] Space) (w : Space) (l : Fin 3) :
    ∑ j : Fin 3, (R w) j * (R (unitVector l)) j = w l := by
  have h : ∑ j : Fin 3, (R w) j * (R (unitVector l)) j = inner ℝ (R (unitVector l)) (R w) := by
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [h, R.inner_map_map]
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem rot_sum (R : Space ≃ₗᵢ[ℝ] Space) (w : Space) (b : Fin 3 → Space) :
    ∑ j : Fin 3, (R w) j • ∑ l : Fin 3, R (unitVector l) j • R (b l) =
      R (∑ l : Fin 3, w l • b l) := by
  simp only [Finset.smul_sum, smul_smul, map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul, sum_coord_rot]

theorem fderiv_pushForward (R : Space ≃ₗᵢ[ℝ] Space) {W : Space → Space} (hW : Differentiable ℝ W)
    (y v : Space) : fderiv ℝ (pushForward R W) y v = R (fderiv ℝ W (R.symm y) (R.symm v)) := by
  have h1 : HasFDerivAt (fun y => R.symm y)
      ((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space) y :=
    (R.symm.toContinuousLinearEquiv).hasFDerivAt
  have h2 := (hW (R.symm y)).hasFDerivAt.comp y h1
  have h3 := ((R.toContinuousLinearEquiv : Space ≃L[ℝ] Space).hasFDerivAt
    (x := W (R.symm y))).comp y h2
  have h4 : HasFDerivAt (pushForward R W)
      (((R.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).comp
        ((fderiv ℝ W (R.symm y)).comp
          ((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space))) y := h3
  rw [h4.fderiv]
  rfl

theorem sliceConvection_pushForward (R : Space ≃ₗᵢ[ℝ] Space) {W : Space → Space}
    (hW : Differentiable ℝ W) (h : X) :
    sliceConvection (pushForward R W) (rotX R h) =ᵐ[volume] pushForward R (sliceConvection W h) := by
  filter_upwards [velocityCov_holds.1 R h, ae_all_iff.2 fun j =>
    Internal.BilinRotate.partialX_rot rotation_holds fieldOpRealized_holds R h j] with y hv hp
  simp only [sliceConvection]
  rw [fderiv_pushForward R hW]
  simp only [pushForward] at hv ⊢
  simp only [sliceConvection]
  rw [hv, LinearIsometryEquiv.symm_apply_apply, map_add]
  simp only [hp]
  rw [rot_sum]

theorem productSlice_rot (R : Space ≃ₗᵢ[ℝ] Space) (h h' : X) :
    productSlice (rotX R h) (rotX R h') =ᵐ[volume] pushForward R (productSlice h h') := by
  filter_upwards [velocityCov_holds.1 R h, ae_all_iff.2 fun j =>
    Internal.BilinRotate.partialX_rot rotation_holds fieldOpRealized_holds R h' j] with y hv hp
  simp only [productSlice, pushForward] at hv ⊢
  simp only [hv, hp]
  rw [rot_sum]

theorem convectionSpec_of {k : ℕ} {d : CertificateData k} {p : Fin k → ℝ}
    (h : ∃ T, ConvectionSpec d p T) : ConvectionSpec d p (convection d p) := by
  unfold convection
  rw [dif_pos h]
  exact h.choose_spec

theorem profile_shift {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) {γ : Symmetry} (hγ : γ ∈ d.symmetries) (σ : ℝ) :
    d.profile p (σ + γ.2) = pushForward γ.1 (d.profile p σ) := by
  funext y
  have := hd.profile_invariant p hp γ hγ σ (γ.1.symm y)
  simpa [pushForward] using this

theorem profile_contDiff {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (p : Fin k → ℝ)
    (σ : ℝ) : ContDiff ℝ 2 (d.profile p σ) :=
  hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

theorem convection_mem (h1 : ConvectionHolds)
    (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ} (hp : p ∈ d.box)
    {u : XX} (hu : IsInvariantXX d.symmetries u) : convection d p u ∈ invariantHH d.symmetries := by
  refine mem_invariantHH_of fun γ hγ => shift_eq_rot_of_ae ?_
  have hs := convectionSpec_of (h1 d hd p hp).1 u
  filter_upwards [hs, ae_shift γ.2 hs, grad_shift hu hγ] with t b1 b2 b3
  have eW : d.profile p (circleRep (t + (γ.2 : TimeCircle))) =
      pushForward γ.1 (d.profile p (circleRep t)) :=
    (periodic_shift (hd.profile_periodic p) t γ.2).trans (profile_shift hd hp hγ _)
  exact b2.trans ((congrArg₂ (fun W h => solField (sliceConvection W h)) eW b3).trans
    ((solField_congr (sliceConvection_pushForward γ.1
      ((profile_contDiff hd p _).differentiable (by norm_num)) _)).trans
      ((solField_pushForward hP _ _).trans (congrArg (rotX γ.1) b1.symm))))

theorem productH_mem (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    {Γ : Set Symmetry} {u : XX} (hu : IsInvariantXX Γ u) : productH u u ∈ invariantHH Γ := by
  unfold productH
  refine mem_invariantHH_of fun γ hγ => circleLpOrZero_shift ?_
  filter_upwards [grad_shift hu hγ] with t b
  exact (congrArg (fun h => solField (productSlice h h)) b).trans
    ((solField_congr (productSlice_rot γ.1 _ _)).trans (solField_pushForward hP _ _))

theorem physToHH_shift {F : ℝ → Space → Space} (hF : IsTimePeriodic F) {a : ℝ}
    {R : Space ≃ₗᵢ[ℝ] Space} (h : ∀ᵐ σ : ℝ, solField (F (σ + a)) = rotX R (solField (F σ))) :
    (shiftLp a : HH →L[ℝ] HH) (physToHH F) = rotHH R (physToHH F) := by
  unfold physToHH
  refine circleLpOrZero_shift ?_
  have h' : ∀ᵐ t : TimeCircle, solField (F (circleRep t + a)) =
      rotX R (solField (F (circleRep t))) := by
    refine (ae_coe_iff _).2 ?_
    filter_upwards [h] with σ hσ
    have e1 : F (circleRep (σ : TimeCircle) + a) = F (σ + a) :=
      periodic_eq hF (by rw [AddCircle.coe_add, coe_circleRep, AddCircle.coe_add])
    exact (congrArg solField e1).trans
      (hσ.trans (congrArg (fun G => rotX R (solField G)) (periodic_coe hF σ).symm))
  filter_upwards [h'] with t ht
  exact (congrArg solField (periodic_shift hF t a)).trans ht

theorem solField_shift_of_ae (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    {F : ℝ → Space → Space} {a : ℝ} {R : Space ≃ₗᵢ[ℝ] Space}
    (h : ∀ᵐ z : ℝ × Space, F (z.1 + a) (R z.2) = R (F z.1 z.2)) :
    ∀ᵐ σ : ℝ, solField (F (σ + a)) = rotX R (solField (F σ)) := by
  rw [Measure.volume_eq_prod] at h
  filter_upwards [Measure.ae_ae_of_ae_prod h] with σ hσ
  refine (solField_congr ?_).trans (solField_pushForward hP _ _)
  filter_upwards [R.symm.measurePreserving.quasiMeasurePreserving.ae hσ] with y hy
  simpa [pushForward] using hy

theorem actuatorH_apply {k : ℕ} (d : CertificateData k) (κ : Fin k → ℝ) :
    actuatorH d κ = ∑ i, κ i • actuatorSlice d i := by
  simp [actuatorH]

theorem actuatorH_mem (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (κ : Fin k → ℝ) :
    actuatorH d κ ∈ invariantHH d.symmetries := by
  refine (congrArg (fun w => w ∈ invariantHH d.symmetries) (actuatorH_apply d κ)).mpr ?_
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact mem_invariantHH_of fun γ hγ => physToHH_shift (hd.actuator_periodic i)
    (solField_shift_of_ae hP (hd.actuator_invariant i γ hγ))

def profilePart (P : ℝ) (W : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (1 / P) • deriv (fun s => W s y) σ + (1 / 2 : ℝ) • W σ y + (1 / 2 : ℝ) • fderiv ℝ (W σ) y y
    - sumSecondPartialsAt (W σ) y + advectionAt (W σ) y

theorem defectField_eq {k : ℕ} (P : ℝ) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (b : Fin k → ℝ → Space → Space) (lam : Fin k → ℝ) (σ : ℝ) (y : Space) :
    defectField P W q b lam σ y = profilePart P W σ y + ∑ i, lam i • b i σ y + gradientAt (q σ) y :=
  rfl

theorem vec_eq_sum (w : Space) : w = ∑ j : Fin 3, w j • unitVector j := by
  ext i
  simp [unitVector, Pi.single_apply]

theorem apply_eq_inner (L : Space →L[ℝ] ℝ) (v : Space) :
    L v = inner ℝ (∑ i : Fin 3, L (unitVector i) • unitVector i) v := by
  conv_lhs => rw [vec_eq_sum v]
  simp only [map_sum, map_smul, sum_inner, inner_smul_left, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [unitVector, EuclideanSpace.inner_single_left, mul_comm]

theorem gradientAt_pushForward (R : Space ≃ₗᵢ[ℝ] Space) {φ : Space → ℝ} (hφ : Differentiable ℝ φ)
    (y : Space) : gradientAt (fun z => φ (R.symm z)) y = R (gradientAt φ (R.symm y)) := by
  have hd : ∀ v, fderiv ℝ (fun z => φ (R.symm z)) y v = fderiv ℝ φ (R.symm y) (R.symm v) := by
    intro v
    have h1 := (hφ (R.symm y)).hasFDerivAt.comp y (R.symm.toContinuousLinearEquiv).hasFDerivAt
    have h2 : HasFDerivAt (fun z => φ (R.symm z)) ((fderiv ℝ φ (R.symm y)).comp
        ((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space)) y := h1
    rw [h2.fderiv]
    rfl
  simp only [gradientAt, hd]
  have hg : ∀ i, fderiv ℝ φ (R.symm y) (R.symm (unitVector i)) =
      (R (∑ j : Fin 3, fderiv ℝ φ (R.symm y) (unitVector j) • unitVector j)) i := by
    intro i
    rw [apply_eq_inner, ← R.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
    simp [unitVector, EuclideanSpace.inner_single_right]
  simp only [hg]
  exact (vec_eq_sum _).symm

theorem sumSecondPartialsAt_pushForward (R : Space ≃ₗᵢ[ℝ] Space) {W : Space → Space} (hW : ContDiff ℝ 2 W)
    (y : Space) : sumSecondPartialsAt (pushForward R W) y = R (sumSecondPartialsAt W (R.symm y)) := by
  have e1 : pushForward R W = ⇑(R.toContinuousLinearEquiv : Space ≃L[ℝ] Space) ∘
      (W ∘ ⇑((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space)) := rfl
  have hit : ∀ v : Fin 2 → Space, iteratedFDeriv ℝ 2 (pushForward R W) y v =
      R (iteratedFDeriv ℝ 2 W (R.symm y) (fun j => R.symm (v j))) := by
    intro v
    rw [e1, ContinuousLinearEquiv.iteratedFDeriv_comp_left,
      ContinuousLinearMap.iteratedFDeriv_comp_right _ hW _ (by norm_num)]
    rfl
  simp only [sumSecondPartialsAt, hit, ← map_sum]
  congr 1
  have hb := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis W
    ((EuclideanSpace.basisFun (Fin 3) ℝ).map R.symm)) (R.symm y)
  have hs := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis W
    (EuclideanSpace.basisFun (Fin 3) ℝ)) (R.symm y)
  beta_reduce at hb hs
  have hv : ∀ i : Fin 3, (fun j => R.symm (![unitVector i, unitVector i] j)) =
      ![((EuclideanSpace.basisFun (Fin 3) ℝ).map R.symm) i,
        ((EuclideanSpace.basisFun (Fin 3) ℝ).map R.symm) i] := by
    intro i
    funext j
    fin_cases j <;> simp [unitVector]
  simp only [hv]
  rw [← hb, hs]
  simp [unitVector]

theorem coord_hasCompactSupport {φ : Space → Space} (hc : HasCompactSupport φ) (i : Fin 3) :
    HasCompactSupport (fun y => φ y i) :=
  hc.comp_left (g := fun w : Space => w i) (by simp)

theorem coord_contDiff {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => φ y i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hφ

theorem coord_fderiv {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) (y v : Space) :
    fderiv ℝ (fun z => φ z i) y v = fderiv ℝ φ y v i := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := φ y)).comp y
    ((hφ.differentiable (by simp)) y).hasFDerivAt
  have h2 : HasFDerivAt (fun z => φ z i)
      ((EuclideanSpace.proj (𝕜 := ℝ) i : Space →L[ℝ] ℝ).comp (fderiv ℝ φ y)) y := h
  rw [h2.fderiv]
  rfl

theorem integrable_mul_of_compact {a b : Space → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hs : HasCompactSupport b) : Integrable (fun x => a x * b x) := by
  refine (ha.mul hb).integrable_of_hasCompactSupport (hs.mono' ?_)
  intro x hx
  apply subset_tsupport
  intro h0
  apply hx
  simp [h0]

theorem inner_gradientAt (ψ : Space → ℝ) (y w : Space) :
    inner ℝ (gradientAt ψ y) w = ∑ i : Fin 3, fderiv ℝ ψ y (unitVector i) * w i := by
  simp only [gradientAt, sum_inner, real_inner_smul_left, unitVector, EuclideanSpace.inner_single_left]
  simp

theorem integral_gradient_test {ψ : Space → ℝ} (hψ : ContDiff ℝ 1 ψ) {φ : Space → Space}
    (hφ : IsTestField φ) : ∫ y, inner ℝ (gradientAt ψ y) (φ y) = 0 := by
  obtain ⟨hs, hc, hdiv⟩ := hφ
  have hdψ : ∀ v, Continuous (fun y => fderiv ℝ ψ y v) := fun v =>
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdφ : ∀ i v, Continuous (fun y => fderiv ℝ (fun z => φ z i) y v) := fun i v =>
    ((coord_contDiff hs i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hibp : ∀ i : Fin 3, ∫ y, fderiv ℝ ψ y (unitVector i) * φ y i =
      -∫ y, ψ y * fderiv ℝ (fun z => φ z i) y (unitVector i) := fun i => by
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := unitVector i) (f := ψ) (g := fun y => φ y i)
      (integrable_mul_of_compact (hdψ _) (coord_contDiff hs i).continuous (coord_hasCompactSupport hc i))
      (integrable_mul_of_compact hψ.continuous (hdφ i _)
        ((coord_hasCompactSupport hc i).fderiv_apply (𝕜 := ℝ) _))
      (integrable_mul_of_compact hψ.continuous (coord_contDiff hs i).continuous
        (coord_hasCompactSupport hc i))
      (fun x _ => (hψ.differentiable (by norm_num)) x)
      (fun x _ => ((coord_contDiff hs i).differentiable (by simp)) x)
    rw [key, neg_neg]
  have e1 : (fun y => inner ℝ (gradientAt ψ y) (φ y)) =
      fun y => ∑ i : Fin 3, fderiv ℝ ψ y (unitVector i) * φ y i :=
    funext fun y => inner_gradientAt ψ y (φ y)
  have e2 : (fun y => ∑ i : Fin 3, ψ y * fderiv ℝ (fun z => φ z i) y (unitVector i)) = fun _ => 0 := by
    funext y
    rw [← Finset.mul_sum]
    have hd : ∑ i : Fin 3, fderiv ℝ (fun z => φ z i) y (unitVector i) = divergenceAt φ y := by
      simp only [divergenceAt, coord_fderiv hs]
    rw [hd, hdiv y, mul_zero]
  rw [e1, integral_finsetSum _ (fun i _ => integrable_mul_of_compact (hdψ _)
    (coord_contDiff hs i).continuous (coord_hasCompactSupport hc i))]
  simp only [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => integrable_mul_of_compact
    hψ.continuous (hdφ i _) ((coord_hasCompactSupport hc i).fderiv_apply (𝕜 := ℝ) _)), e2,
    integral_zero, neg_zero]

theorem solField_gradientAt {ψ : Space → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hm : MemLp (gradientAt ψ) 2 volume) : solField (gradientAt ψ) = 0 :=
  Internal.TestDense.eq_zero_of_forall_inner _ fun φ hφ =>
    (real_inner_comm (solField (gradientAt ψ)) (solField φ)).trans
      ((inner_solField_test φ hφ.1 hφ.2.1 hφ.2.2 (gradientAt ψ) hm).trans
        (integral_gradient_test hψ hφ))

theorem gradientAt_sub {f g : Space → ℝ} {y : Space} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) : gradientAt (fun z => f z - g z) y = gradientAt f y - gradientAt g y := by
  simp only [gradientAt]
  rw [fderiv_fun_sub hf hg]
  simp only [sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem deriv_shift {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) {γ : Symmetry} (hγ : γ ∈ d.symmetries) (σ : ℝ) (y : Space) :
    deriv (fun s => d.profile p s y) (σ + γ.2) = γ.1 (deriv (fun s => d.profile p s (γ.1.symm y)) σ) := by
  have hc : ContDiff ℝ 2 (fun s => d.profile p s (γ.1.symm y)) :=
    hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hg := (hc.differentiable (by norm_num) σ).hasDerivAt
  have h3 := ((γ.1.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).hasFDerivAt.comp_hasDerivAt σ hg
  have e : (fun s => d.profile p (s + γ.2) y) = fun s => γ.1 (d.profile p s (γ.1.symm y)) := by
    funext s
    rw [profile_shift hd hp hγ s]
    rfl
  have h4 : HasDerivAt (fun s => γ.1 (d.profile p s (γ.1.symm y)))
      (γ.1 (deriv (fun s => d.profile p s (γ.1.symm y)) σ)) σ := h3
  rw [← deriv_comp_add_const, e, h4.deriv]

theorem profilePart_shift {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) {γ : Symmetry} (hγ : γ ∈ d.symmetries) (σ : ℝ) (y : Space) :
    profilePart (d.period p) (d.profile p) (σ + γ.2) y =
      γ.1 (profilePart (d.period p) (d.profile p) σ (γ.1.symm y)) := by
  have hdiff := (profile_contDiff hd p σ).differentiable (by norm_num)
  simp only [profilePart, advectionAt]
  rw [profile_shift hd hp hγ σ, deriv_shift hd hp hγ σ y,
    sumSecondPartialsAt_pushForward γ.1 (profile_contDiff hd p σ)]
  simp only [fderiv_pushForward γ.1 hdiff]
  simp only [pushForward, map_add, map_sub, map_smul, LinearIsometryEquiv.symm_apply_apply]

theorem defect_periodic {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) : IsTimePeriodic (defectField (d.period p) (d.profile p) (d.pressure p)
      d.actuator (d.multiplier p)) := by
  intro σ y
  have hW : d.profile p (σ + 1) = d.profile p σ := funext (hd.profile_periodic p σ)
  have hq : d.pressure p (σ + 1) = d.pressure p σ := funext (hd.pressure_periodic p hp σ)
  have hb : ∀ i, d.actuator i (σ + 1) = d.actuator i σ := fun i => funext (hd.actuator_periodic i σ)
  have hdv : deriv (fun s => d.profile p s y) (σ + 1) = deriv (fun s => d.profile p s y) σ :=
    by
      rw [← deriv_comp_add_const]
      exact congrArg (fun f => deriv f σ) (funext fun s => hd.profile_periodic p s y)
  simp only [defectField, hW, hq, hb, hdv]

theorem contDiff_fderiv_slice {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {V : E → Space → G} {m n : WithTop ℕ∞}
    (hV : ContDiff ℝ m (fun z : E × Space => V z.1 z.2)) (hnm : n + 1 ≤ m) :
    ContDiff ℝ n (fun z : E × Space => fderiv ℝ (V z.1) z.2) :=
  ContDiff.fderiv (f := fun (z : E × Space) (y : Space) => V z.1 y) (g := Prod.snd)
    (hV.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd hnm

theorem continuous_profilePart (P : ℝ) {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => profilePart P W z.1 z.2) := by
  have hD : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    contDiff_fderiv_slice hW (by norm_num)
  have hDD : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun y => fderiv ℝ (W z.1) y) z.2) :=
    contDiff_fderiv_slice (V := fun (s : ℝ) y => fderiv ℝ (W s) y) hD (by norm_num)
  have hT : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fun s => W s z.2) z.1) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (s : ℝ) => W s z.2) (g := Prod.fst)
      (hW.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst (by norm_num)
  have hTc : Continuous (fun z : ℝ × Space => deriv (fun s => W s z.2) z.1) :=
    hT.continuous.clm_apply continuous_const
  have hL : (fun z : ℝ × Space => sumSecondPartialsAt (W z.1) z.2) = fun z =>
      ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (W z.1) y) z.2 (unitVector i) (unitVector i) := by
    funext z
    simp [sumSecondPartialsAt, iteratedFDeriv_two_apply]
  have hLc : Continuous (fun z : ℝ × Space => sumSecondPartialsAt (W z.1) z.2) := by
    rw [hL]
    exact continuous_finsetSum _ fun i _ =>
      (hDD.continuous.clm_apply continuous_const).clm_apply continuous_const
  exact ((((hTc.const_smul (1 / P)).add (hW.continuous.const_smul (1 / 2 : ℝ))).add
    ((hD.continuous.clm_apply continuous_snd).const_smul (1 / 2 : ℝ))).sub hLc).add
    (hD.continuous.clm_apply hW.continuous)

theorem continuous_gradientAt_slice {Q : ℝ → Space → ℝ}
    (hQ : ContDiff ℝ 1 (fun z : ℝ × Space => Q z.1 z.2)) :
    Continuous (fun z : ℝ × Space => gradientAt (Q z.1) z.2) := by
  have hq : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (Q z.1) z.2) :=
    contDiff_fderiv_slice hQ (by norm_num)
  exact continuous_finsetSum _ fun i _ =>
    (hq.continuous.clm_apply continuous_const).smul continuous_const

theorem defect_memLp_ae {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) : ∀ᵐ σ : ℝ, MemLp (defectField (d.period p) (d.profile p) (d.pressure p)
      d.actuator (d.multiplier p) σ) 2 volume := by
  have hW : ContDiff ℝ 2 (fun z : ℝ × Space => d.profile p z.1 z.2) :=
    hd.profile_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hS : AEStronglyMeasurable (fun z : ℝ × Space => ∑ i, d.multiplier p i • d.actuator i z.1 z.2)
      volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((hd.actuator_measurable i).const_smul (d.multiplier p i) :
        AEStronglyMeasurable (fun z : ℝ × Space => d.multiplier p i • d.actuator i z.1 z.2) volume)
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => defectField (d.period p) (d.profile p)
      (d.pressure p) d.actuator (d.multiplier p) z.1 z.2) volume :=
    ((continuous_profilePart (d.period p) hW).aestronglyMeasurable.add hS).add
      (continuous_gradientAt_slice (hd.pressure_smooth p hp)).aestronglyMeasurable
  obtain ⟨c, hc, -⟩ := exists_curve_of_joint _ hm (defect_periodic hd hp)
    (lt_of_le_of_lt (hd.defect_l2 p hp) ENNReal.ofReal_lt_top)
  filter_upwards [hc] with σ hσ
  exact (Lp.memLp (c (σ : TimeCircle))).ae_eq hσ

theorem defect_shift (hP : ∀ F (x : HBar), inner ℝ (solProj F) x = inner ℝ F (toPhysH x))
    {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ} (hp : p ∈ d.box)
    {γ : Symmetry} (hγ : γ ∈ d.symmetries) :
    ∀ᵐ σ : ℝ, solField (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator
      (d.multiplier p) (σ + γ.2)) = rotX γ.1 (solField (defectField (d.period p) (d.profile p)
        (d.pressure p) d.actuator (d.multiplier p) σ)) := by
  have hb : ∀ i, ∀ᵐ σ : ℝ, ∀ᵐ y : Space,
      d.actuator i (σ + γ.2) (γ.1 y) = γ.1 (d.actuator i σ y) := fun i => by
    have h := hd.actuator_invariant i γ hγ
    rw [Measure.volume_eq_prod] at h
    exact Measure.ae_ae_of_ae_prod h
  have hm := defect_memLp_ae hd hp
  filter_upwards [hm, (measurePreserving_add_right volume γ.2).quasiMeasurePreserving.ae hm,
    ae_all_iff.2 hb] with σ m1 m2 m3
  have hq1 : ContDiff ℝ 1 (d.pressure p (σ + γ.2)) :=
    (hd.pressure_smooth p hp).comp (contDiff_const.prodMk contDiff_id)
  have hq0 : ContDiff ℝ 1 (d.pressure p σ) :=
    (hd.pressure_smooth p hp).comp (contDiff_const.prodMk contDiff_id)
  have hq2 : ContDiff ℝ 1 (fun z => d.pressure p σ (γ.1.symm z)) :=
    hq0.comp γ.1.symm.contDiff
  have hψ : ContDiff ℝ 1 (fun z => d.pressure p (σ + γ.2) z - d.pressure p σ (γ.1.symm z)) :=
    hq1.sub hq2
  have hgrad : ∀ y, gradientAt (fun z => d.pressure p (σ + γ.2) z - d.pressure p σ (γ.1.symm z)) y =
      gradientAt (d.pressure p (σ + γ.2)) y - γ.1 (gradientAt (d.pressure p σ) (γ.1.symm y)) := by
    intro y
    rw [gradientAt_sub ((hq1.differentiable (by norm_num)) y) ((hq2.differentiable (by norm_num)) y),
      gradientAt_pushForward γ.1 (hq0.differentiable (by norm_num))]
  have hG := memLp_pushForward γ.1 m1
  have hdiff : (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator (d.multiplier p)
      (σ + γ.2) - pushForward γ.1 (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator
        (d.multiplier p) σ)) =ᵐ[volume]
      gradientAt (fun z => d.pressure p (σ + γ.2) z - d.pressure p σ (γ.1.symm z)) := by
    filter_upwards [γ.1.symm.measurePreserving.quasiMeasurePreserving.ae (ae_all_iff.2 m3)]
      with y hy
    simp only [LinearIsometryEquiv.apply_symm_apply] at hy
    rw [Pi.sub_apply, hgrad y]
    simp only [pushForward, defectField_eq, profilePart_shift hd hp hγ σ y, hy, map_add, map_sum,
      map_smul]
    abel
  have hz : solField (defectField (d.period p) (d.profile p) (d.pressure p) d.actuator
      (d.multiplier p) (σ + γ.2) - pushForward γ.1 (defectField (d.period p) (d.profile p)
        (d.pressure p) d.actuator (d.multiplier p) σ)) = 0 := by
    exact (solField_congr hdiff).trans
      (solField_gradientAt hψ ((memLp_congr_ae hdiff).1 (m2.sub hG)))
  exact (sub_eq_zero.1 ((solField_sub m2 hG).symm.trans hz)).trans (solField_pushForward hP _ _)

end Internal.Invariance

open Internal.Invariance

theorem invarianceHolds_of (h1 : ConvectionHolds) (h2 : ProjectionHolds) : InvarianceHolds := by
  intro k d hd p hp
  have hP := h2.2.2.1
  refine ⟨fun u hu => ⟨convection_mem h1 hP hd hp hu, productH_mem hP hu⟩,
    fun κ => actuatorH_mem hP hd κ, ?_⟩
  unfold defectH
  exact mem_invariantHH_of fun γ hγ => physToHH_shift (defect_periodic hd hp) (defect_shift hP hd hp hγ)

end Breakdown.Cert
