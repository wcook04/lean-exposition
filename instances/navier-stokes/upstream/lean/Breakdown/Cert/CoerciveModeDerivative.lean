import Breakdown.Cert.CoercivePerturbationFacts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace ModeDerivative.Internal

theorem continuous_axialRot_prod : Continuous (fun q : ℝ × Space => axialRot q.1 q.2) := by
  unfold axialRot
  fun_prop

theorem axialRot_neg_apply (hRot : AxialRotationHolds) (φ : ℝ) (y : Space) :
    axialRot (-φ) (axialRot φ y) = y := by
  rw [← hRot.2.1, neg_add_cancel, hRot.2.2.1]

theorem axialRot_apply_neg (hRot : AxialRotationHolds) (φ : ℝ) (y : Space) :
    axialRot φ (axialRot (-φ) y) = y := by
  rw [← hRot.2.1, add_neg_cancel, hRot.2.2.1]

theorem norm_axialRot (hRot : AxialRotationHolds) (φ : ℝ) (y : Space) : ‖axialRot φ y‖ = ‖y‖ := by
  obtain ⟨R, hR⟩ := hRot.1 φ
  rw [← hR, R.norm_map]

def rotSkew (hRot : AxialRotationHolds) : (ℝ × ℝ) × Space ≃ᵐ (ℝ × ℝ) × Space where
  toFun q := (q.1, axialRot q.1.2 q.2)
  invFun q := (q.1, axialRot (-q.1.2) q.2)
  left_inv q := Prod.ext rfl (axialRot_neg_apply hRot q.1.2 q.2)
  right_inv q := Prod.ext rfl (axialRot_apply_neg hRot q.1.2 q.2)
  measurable_toFun := (continuous_fst.prodMk
    (continuous_axialRot_prod.comp (continuous_fst.snd.prodMk continuous_snd))).measurable
  measurable_invFun := (continuous_fst.prodMk
    (continuous_axialRot_prod.comp (continuous_fst.snd.neg.prodMk continuous_snd))).measurable

theorem rotSkew_apply (hRot : AxialRotationHolds) (q : (ℝ × ℝ) × Space) :
    rotSkew hRot q = (q.1, axialRot q.1.2 q.2) := rfl

theorem rotSkew_measurePreserving (hRot : AxialRotationHolds) (μ : Measure (ℝ × ℝ)) [SFinite μ]
    {B : Set Space} (hB : MeasurableSet B) (hBr : ∀ φ y, axialRot φ y ∈ B ↔ y ∈ B) :
    MeasurePreserving (rotSkew hRot) (μ.prod (volume.restrict B)) (μ.prod (volume.restrict B)) := by
  have hg : Measurable (Function.uncurry fun (p : ℝ × ℝ) (y : Space) => axialRot p.2 y) :=
    (continuous_axialRot_prod.comp (continuous_fst.snd.prodMk continuous_snd)).measurable
  have h := MeasurePreserving.skew_product (MeasurePreserving.id μ) hg
    (μc := volume.restrict B) (μd := volume.restrict B) (Filter.Eventually.of_forall fun p => ?_)
  · exact h
  · obtain ⟨R, hR⟩ := hRot.1 p.2
    have hf : (R : Space → Space) = axialRot p.2 := funext hR
    have hpre : (R : Space → Space) ⁻¹' B = B := by
      ext y; simp only [Set.mem_preimage, hR, hBr]
    have hm := R.measurePreserving.restrict_preimage hB
    rw [hpre] at hm
    rw [← hf]
    exact hm.map_eq

abbrev angleMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))

theorem quasiMeasurePreserving_rotated (hRot : AxialRotationHolds) (σ : ℝ) :
    Measure.QuasiMeasurePreserving (fun q : Space × (ℝ × ℝ) => ((σ + q.2.1, axialRot q.2.2 q.1) : ℝ × Space))
      ((volume : Measure Space).prod ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))) volume := by
  have hT := rotSkew_measurePreserving hRot angleMeasure MeasurableSet.univ (fun _ _ => by simp)
  rw [Measure.restrict_univ] at hT
  have hS := hT.comp (Measure.measurePreserving_swap (μ := (volume : Measure Space)) (ν := angleMeasure))
  have hId : Measure.QuasiMeasurePreserving (id : ℝ → ℝ) (volume.restrict (Set.Ioc (0 : ℝ) 1)) volume :=
    ⟨measurable_id, by rw [Measure.map_id]; exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self⟩
  have hf : Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ => σ + p.1) angleMeasure volume :=
    (measurePreserving_add_left (volume : Measure ℝ) σ).quasiMeasurePreserving.comp
      (hId.comp Measure.quasiMeasurePreserving_fst)
  have hΨ := MeasureTheory.QuasiMeasurePreserving.prodMap hf (Measure.QuasiMeasurePreserving.id (volume : Measure Space))
  rw [← Measure.volume_eq_prod] at hΨ
  exact hΨ.comp hS.quasiMeasurePreserving

theorem integrable_rotated {E : Type*} [NormedAddCommGroup E] (hRot : AxialRotationHolds) {F : ℝ → Space → E}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (σ : ℝ) {K : Set Space} (hK : IsCompact K) :
    Integrable (fun q : Space × (ℝ × ℝ) => F (σ + q.2.1) (axialRot q.2.2 q.1))
      ((volume.restrict K).prod ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))) := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Space)
  set B : Set Space := Metric.closedBall (0 : Space) r with hBdef
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hBr : ∀ φ y, axialRot φ y ∈ B ↔ y ∈ B := by
    intro φ y; simp only [hBdef, Metric.mem_closedBall, dist_zero_right, norm_axialRot hRot]
  refine Integrable.mono_measure ?_ (Measure.prod_mono (Measure.restrict_mono hr le_rfl) le_rfl)
  have hT := rotSkew_measurePreserving hRot angleMeasure hBm hBr
  have hS := hT.comp (Measure.measurePreserving_swap (μ := volume.restrict B) (ν := angleMeasure))
  have hSe : MeasurableEmbedding (rotSkew hRot ∘ Prod.swap) :=
    (rotSkew hRot).measurableEmbedding.comp MeasurableEquiv.prodComm.measurableEmbedding
  have e1 : (fun q : Space × (ℝ × ℝ) => F (σ + q.2.1) (axialRot q.2.2 q.1)) =
      (fun q : (ℝ × ℝ) × Space => F (σ + q.1.1) q.2) ∘ (rotSkew hRot ∘ Prod.swap) := rfl
  rw [e1, hS.integrable_comp_emb hSe]
  have hA : MeasurePreserving (fun q : (ℝ × ℝ) × Space => ((q.1.1, q.2), q.1.2))
      (angleMeasure.prod (volume.restrict B))
      (((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict B)).prod
        (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
    have ha := measurePreserving_prodAssoc (volume.restrict (Set.Ioc (0 : ℝ) 1))
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) (volume.restrict B)
    have hb := (MeasurePreserving.id (volume.restrict (Set.Ioc (0 : ℝ) 1))).prod
      (Measure.measurePreserving_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
        (ν := volume.restrict B))
    have hc := (measurePreserving_prodAssoc (volume.restrict (Set.Ioc (0 : ℝ) 1)) (volume.restrict B)
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))).symm MeasurableEquiv.prodAssoc
    exact hc.comp (hb.comp ha)
  have hAe : MeasurableEmbedding (fun q : (ℝ × ℝ) × Space => ((q.1.1, q.2), q.1.2)) :=
    ((MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm)).trans
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := Space) (γ := ℝ)).symm).measurableEmbedding
  have e2 : (fun q : (ℝ × ℝ) × Space => F (σ + q.1.1) q.2) =
      (fun w : (ℝ × Space) × ℝ => F (σ + w.1.1) w.1.2) ∘ (fun q : (ℝ × ℝ) × Space => ((q.1.1, q.2), q.1.2)) :=
    rfl
  rw [e2, hA.integrable_comp_emb hAe]
  have hν : (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioc]
    simp [Real.pi_pos]
  refine (Integrable.comp_fst_iff (f := fun z : ℝ × Space => F (σ + z.1) z.2) hν).2 ?_
  have hpre : (fun t : ℝ => σ + t) ⁻¹' Set.Ioc σ (σ + 1) = Set.Ioc (0 : ℝ) 1 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hτ := (measurePreserving_add_left (volume : Measure ℝ) σ).restrict_preimage
    (measurableSet_Ioc (a := σ) (b := σ + 1))
  rw [hpre] at hτ
  have hM := hτ.prod (MeasurePreserving.id (volume.restrict B))
  have hMe : MeasurableEmbedding (Prod.map (fun t : ℝ => σ + t) (id : Space → Space)) :=
    ((MeasurableEquiv.addLeft σ).prodCongr (MeasurableEquiv.refl Space)).measurableEmbedding
  have e3 : (fun z : ℝ × Space => F (σ + z.1) z.2) =
      (fun z : ℝ × Space => F z.1 z.2) ∘ Prod.map (fun t : ℝ => σ + t) (id : Space → Space) := rfl
  rw [e3, hM.integrable_comp_emb hMe, Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hFl.integrableOn_isCompact (isCompact_Icc.prod (isCompact_closedBall (0 : Space) r))).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self le_rfl)

theorem vec_eq_sum (u : Space) : u = ∑ k : Fin 3, u k • unitVector k := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr u
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at h
  exact h.symm

theorem weakGradient_apply {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) {φ : Space → ℝ} (hφ : IsTestFunction φ) (u : Space) :
    ∫ y, φ y • g y u = -∫ y, fderiv ℝ φ y u • f y := by
  have hL : ∀ k : Fin 3, Integrable (fun y => φ y • g y (unitVector k)) volume := by
    intro k
    have hi : Integrable (fun y => φ y • g y) volume :=
      h.2.1.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    exact hi.apply_continuousLinearMap (unitVector k)
  have hR : ∀ k : Fin 3, Integrable (fun y => fderiv ℝ φ y (unitVector k) • f y) volume := by
    intro k
    have hc : Continuous (fun y => fderiv ℝ φ y (unitVector k)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h.1.integrable_smul_left_of_hasCompactSupport hc (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have e1 : (fun y => φ y • g y u) = fun y => ∑ k : Fin 3, u k • (φ y • g y (unitVector k)) := by
    funext y
    conv_lhs => rw [vec_eq_sum u]
    simp only [map_sum, map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm]
  have e2 : (fun y => fderiv ℝ φ y u • f y) =
      fun y => ∑ k : Fin 3, u k • (fderiv ℝ φ y (unitVector k) • f y) := by
    funext y
    conv_lhs => rw [vec_eq_sum u]
    simp only [map_sum, map_smul, Finset.sum_smul, smul_eq_mul, mul_smul]
  rw [e1, e2, integral_finsetSum (f := fun k y => u k • (φ y • g y (unitVector k))) Finset.univ
      (fun k _ => (hL k).smul (u k)),
    integral_finsetSum (f := fun k y => u k • (fderiv ℝ φ y (unitVector k) • f y)) Finset.univ
      (fun k _ => (hR k).smul (u k)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul, integral_smul, h.2.2 φ hφ k, smul_neg]

theorem locallyIntegrable_comp_isometry {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : LocallyIntegrable f volume) (R : Space ≃ₗᵢ[ℝ] Space) :
    LocallyIntegrable (fun y => f (R y)) volume := by
  have h := (locallyIntegrable_map_homeomorph (μ := (volume : Measure Space)) R.toHomeomorph (f := f)).1
  rw [show Measure.map R.toHomeomorph volume = (volume : Measure Space) from
    R.measurePreserving.map_eq] at h
  exact h hf

theorem integral_comp_isometry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Space → E)
    (R : Space ≃ₗᵢ[ℝ] Space) : ∫ y, F (R y) = ∫ x, F x :=
  R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding F

theorem weakGradient_rotate {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) (R : Space ≃ₗᵢ[ℝ] Space) {f' : Space → Space}
    {g' : Space → (Space →L[ℝ] Space)} (hf' : ∀ y, f' y = R.symm (f (R y)))
    (hg' : ∀ y u, g' y u = R.symm (g (R y) (R u))) : IsWeakGradient f' g' := by
  have hfR := locallyIntegrable_comp_isometry h.1 R
  have hgR := locallyIntegrable_comp_isometry h.2.1 R
  have ef : f' = fun y => R.symm (f (R y)) := funext hf'
  let Rc : Space →L[ℝ] Space := R.toContinuousLinearEquiv.toContinuousLinearMap
  let Rs : Space →L[ℝ] Space := R.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have eg : g' = fun y => Rs.comp ((g (R y)).comp Rc) := by
    funext y; ext1 u; rw [hg']; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [ef]
    refine hfR.mono (R.symm.continuous.comp_aestronglyMeasurable hfR.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun y => by simp
  · rw [eg]
    refine hgR.mono ((continuous_const.clm_comp (continuous_id.clm_comp continuous_const)).comp_aestronglyMeasurable
      hgR.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
    have e : (Rs.comp ((g (R y)).comp Rc)) u = R.symm (g (R y) (R u)) := rfl
    rw [e, LinearIsometryEquiv.norm_map]
    calc ‖g (R y) (R u)‖ ≤ ‖g (R y)‖ * ‖R u‖ := (g (R y)).le_opNorm _
      _ = ‖g (R y)‖ * ‖u‖ := by rw [LinearIsometryEquiv.norm_map]
  · intro φ hφ i
    have hψ : IsTestFunction (fun x => φ (R.symm x)) :=
      ⟨hφ.1.comp R.symm.toContinuousLinearEquiv.contDiff, hφ.2.comp_homeomorph R.symm.toHomeomorph⟩
    have key := weakGradient_apply h hψ (R (unitVector i))
    have hd : ∀ x, fderiv ℝ (fun x => φ (R.symm x)) x (R (unitVector i)) =
        fderiv ℝ φ (R.symm x) (unitVector i) := by
      intro x
      have hx : HasFDerivAt (fun x => φ (R.symm x))
          ((fderiv ℝ φ (R.symm x)).comp (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space)) x :=
        (hφ.1.differentiable (by simp) (R.symm x)).hasFDerivAt.comp x
          R.symm.toContinuousLinearEquiv.hasFDerivAt
      rw [hx.fderiv]
      simp
    simp_rw [hd] at key
    have l1 : ∫ y, φ y • g' y (unitVector i) = R.symm (∫ y, φ y • g (R y) (R (unitVector i))) := by
      have c := R.symm.toLinearIsometry.integral_comp_comm (μ := volume)
        (fun y => φ y • g (R y) (R (unitVector i)))
      simp only [LinearIsometryEquiv.coe_toLinearIsometry] at c
      rw [← c]
      congr 1; funext y; rw [hg', map_smul]
    have l2 : ∫ y, fderiv ℝ φ y (unitVector i) • f' y =
        R.symm (∫ y, fderiv ℝ φ y (unitVector i) • f (R y)) := by
      have c := R.symm.toLinearIsometry.integral_comp_comm (μ := volume)
        (fun y => fderiv ℝ φ y (unitVector i) • f (R y))
      simp only [LinearIsometryEquiv.coe_toLinearIsometry] at c
      rw [← c]
      congr 1; funext y; rw [hf', map_smul]
    have l3 : ∫ y, φ y • g (R y) (R (unitVector i)) = ∫ x, φ (R.symm x) • g x (R (unitVector i)) := by
      rw [← integral_comp_isometry (fun x => φ (R.symm x) • g x (R (unitVector i))) R]
      simp
    have l4 : ∫ y, fderiv ℝ φ y (unitVector i) • f (R y) =
        ∫ x, fderiv ℝ φ (R.symm x) (unitVector i) • f x := by
      rw [← integral_comp_isometry (fun x => fderiv ℝ φ (R.symm x) (unitVector i) • f x) R]
      simp
    rw [l1, l2, l3, l4, key, map_neg]

theorem integrable_of_restrict_tsupport {E : Type*} [NormedAddCommGroup E] {θ : Space → ℝ}
    (hθ : IsTestFunction θ) {μ : Measure (ℝ × ℝ)} [SFinite μ] {F : Space × (ℝ × ℝ) → E}
    (hF : Integrable F ((volume.restrict (tsupport θ)).prod μ))
    (h0 : ∀ q : Space × (ℝ × ℝ), q.1 ∉ tsupport θ → F q = 0) :
    Integrable F ((volume : Measure Space).prod μ) := by
  have hK : MeasurableSet (tsupport θ) := (isClosed_tsupport θ).measurableSet
  rw [← Measure.restrict_univ (μ := μ), Measure.prod_restrict] at hF
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero hF fun q hq => h0 q fun h => hq ⟨h, trivial⟩

theorem average_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {θ : Space → ℝ}
    (hθ : IsTestFunction θ) {μ : Measure (ℝ × ℝ)} [SFinite μ] (w : Space → ℝ) (hw : Continuous w)
    (hw0 : ∀ y, y ∉ tsupport θ → w y = 0) (c : ℝ × ℝ → ℝ) (hcm : Measurable c) (hc : ∀ p, |c p| ≤ 1)
    {a : ℝ × ℝ → Space → E}
    (ha : Integrable (fun q : Space × (ℝ × ℝ) => a q.2 q.1) ((volume.restrict (tsupport θ)).prod μ)) :
    ∫ y, w y • (∫ p, c p • a p y ∂μ) = ∫ p, c p • (∫ y, w y • a p y) ∂μ := by
  have hK : MeasurableSet (tsupport θ) := (isClosed_tsupport θ).measurableSet
  obtain ⟨B, hB⟩ : ∃ B, ∀ y, ‖w y‖ ≤ B := by
    have hcs : HasCompactSupport w := by
      refine hθ.2.mono' ?_
      intro y hy
      by_contra h
      exact hy (hw0 y h)
    exact hw.bounded_above_of_compact_support hcs
  have hF : Integrable (fun q : Space × (ℝ × ℝ) => w q.1 • (c q.2 • a q.2 q.1))
      ((volume : Measure Space).prod μ) := by
    refine integrable_of_restrict_tsupport hθ ?_ fun q hq => by simp [hw0 q.1 hq]
    refine Integrable.mono' (ha.norm.const_mul B) ?_ ?_
    · exact ((hw.comp continuous_fst).aestronglyMeasurable).smul
        (((hcm.comp measurable_snd).aestronglyMeasurable).smul ha.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun q => ?_
      rw [norm_smul, norm_smul]
      have h1 : ‖c q.2‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hc _
      calc ‖w q.1‖ * (‖c q.2‖ * ‖a q.2 q.1‖) ≤ B * (1 * ‖a q.2 q.1‖) := by
            gcongr
            · exact (norm_nonneg _).trans (hB q.1)
            · exact hB q.1
        _ = B * ‖a q.2 q.1‖ := by ring
  have e1 : (fun y => w y • (∫ p, c p • a p y ∂μ)) =ᵐ[volume] fun y => ∫ p, w y • (c p • a p y) ∂μ := by
    have hl := ha.prod_right_ae
    rw [ae_restrict_iff' hK] at hl
    filter_upwards [hl] with y hy
    by_cases hyK : y ∈ tsupport θ
    · rw [integral_smul]
    · simp [hw0 y hyK]
  rw [integral_congr_ae e1]
  have hs := integral_integral_swap (μ := (volume : Measure Space)) (ν := μ)
    (f := fun y p => w y • (c p • a p y)) hF
  rw [hs]
  congr 1
  funext p
  simp_rw [smul_comm (w _) (c p)]
  rw [integral_smul]

theorem integrable_weight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : Measure (Space × (ℝ × ℝ))}
    (c : ℝ × ℝ → ℝ) (hcm : Measurable c) (hc : ∀ p, |c p| ≤ 1) {a : ℝ × ℝ → Space → E}
    (ha : Integrable (fun q : Space × (ℝ × ℝ) => a q.2 q.1) m) :
    Integrable (fun q : Space × (ℝ × ℝ) => c q.2 • a q.2 q.1) m := by
  refine Integrable.mono' ha.norm ?_ ?_
  · exact ((hcm.comp measurable_snd).aestronglyMeasurable).smul ha.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun q => ?_
    rw [norm_smul]
    have h1 : ‖c q.2‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hc _
    calc ‖c q.2‖ * ‖a q.2 q.1‖ ≤ 1 * ‖a q.2 q.1‖ := by gcongr
      _ = ‖a q.2 q.1‖ := one_mul _

theorem weakGradient_average {μ : Measure (ℝ × ℝ)} [SFinite μ] (c : ℝ × ℝ → ℝ) (hcm : Measurable c)
    (hc : ∀ p, |c p| ≤ 1) {a : ℝ × ℝ → Space → Space} {b : ℝ × ℝ → Space → (Space →L[ℝ] Space)}
    (ha : ∀ K : Set Space, IsCompact K →
      Integrable (fun q : Space × (ℝ × ℝ) => a q.2 q.1) ((volume.restrict K).prod μ))
    (hb : ∀ K : Set Space, IsCompact K →
      Integrable (fun q : Space × (ℝ × ℝ) => b q.2 q.1) ((volume.restrict K).prod μ))
    (hw : ∀ᵐ p ∂μ, IsWeakGradient (a p) (b p)) :
    IsWeakGradient (fun y => ∫ p, c p • a p y ∂μ) (fun y => ∫ p, c p • b p y ∂μ) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (locallyIntegrable_iff).2 fun K hK => ?_
    exact (integrable_weight c hcm hc (ha K hK)).integral_prod_left
  · refine (locallyIntegrable_iff).2 fun K hK => ?_
    exact (integrable_weight c hcm hc (hb K hK)).integral_prod_left
  · intro θ hθ i
    have hKc : IsCompact (tsupport θ) := hθ.2
    have hK : MeasurableSet (tsupport θ) := (isClosed_tsupport θ).measurableSet
    have hθ0 : ∀ y, y ∉ tsupport θ → θ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
    have hd0 : ∀ y, y ∉ tsupport θ → fderiv ℝ θ y (unitVector i) = 0 := by
      intro y hy
      have : y ∉ tsupport (fderiv ℝ θ) := fun h => hy (tsupport_fderiv_subset ℝ h)
      rw [image_eq_zero_of_notMem_tsupport this]; rfl
    have hdc : Continuous (fun y => fderiv ℝ θ y (unitVector i)) :=
      (hθ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hbi := (hb _ hKc).apply_continuousLinearMap (unitVector i)
    have e0 : (fun y => θ y • (∫ p, c p • b p y ∂μ) (unitVector i)) =ᵐ[volume]
        fun y => θ y • ∫ p, c p • b p y (unitVector i) ∂μ := by
      have hl := (integrable_weight c hcm hc (hb _ hKc)).prod_right_ae
      rw [ae_restrict_iff' hK] at hl
      filter_upwards [hl] with y hy
      by_cases hyK : y ∈ tsupport θ
      · rw [ContinuousLinearMap.integral_apply (hy hyK)]
        rfl
      · simp [hθ0 y hyK]
    rw [integral_congr_ae e0, average_swap hθ θ hθ.1.continuous hθ0 c hcm hc hbi,
      average_swap hθ _ hdc hd0 c hcm hc (ha _ hKc), ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hw] with p hp
    rw [hp.2.2 θ hθ i, smul_neg]

def rotIso (hRot : AxialRotationHolds) (φ : ℝ) : Space ≃ₗᵢ[ℝ] Space := (hRot.1 φ).choose

theorem rotIso_apply (hRot : AxialRotationHolds) (φ : ℝ) (y : Space) : rotIso hRot φ y = axialRot φ y :=
  (hRot.1 φ).choose_spec y

theorem rotIso_symm_apply (hRot : AxialRotationHolds) (φ : ℝ) (y : Space) :
    (rotIso hRot φ).symm y = axialRot (-φ) y := by
  rw [LinearIsometryEquiv.symm_apply_eq, rotIso_apply, axialRot_apply_neg hRot]

def modePhase (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ := 2 * Real.pi * ι.1 * p.1 + ι.2 * p.2

def weightRe (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ := Real.cos (modePhase ι p) / (2 * Real.pi)

def weightIm (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ := -Real.sin (modePhase ι p) / (2 * Real.pi)

def rotConj (hRot : AxialRotationHolds) (φ : ℝ) (A : Space →L[ℝ] Space) : Space →L[ℝ] Space :=
  ((rotIso hRot φ).symm.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
    (A.comp ((rotIso hRot φ).toContinuousLinearEquiv : Space →L[ℝ] Space))

theorem rotConj_apply (hRot : AxialRotationHolds) (φ : ℝ) (A : Space →L[ℝ] Space) (u : Space) :
    rotConj hRot φ A u = axialRot (-φ) (A (axialRot φ u)) := by
  show (rotIso hRot φ).symm (A (rotIso hRot φ u)) = _
  rw [rotIso_symm_apply, rotIso_apply]

def velFamily (v : ℝ → Space → Space) (σ : ℝ) (p : ℝ × ℝ) (y : Space) : Space :=
  axialRot (-p.2) (v (σ + p.1) (axialRot p.2 y))

def gradFamily (hRot : AxialRotationHolds) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (p : ℝ × ℝ)
    (y : Space) : Space →L[ℝ] Space :=
  rotConj hRot p.2 (G (σ + p.1) (axialRot p.2 y))

def columnFamily (G : ℝ → Space → (Space →L[ℝ] Space)) (l : Fin 3) (σ : ℝ) (p : ℝ × ℝ) (y : Space) :
    Space :=
  axialRot (-p.2) (G (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector l)))

def secondDerivFamily (hRot : AxialRotationHolds) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (l : Fin 3)
    (σ : ℝ) (p : ℝ × ℝ) (y : Space) : Space →L[ℝ] Space :=
  rotConj hRot p.2 ((H (σ + p.1) (axialRot p.2 y)).flip (axialRot p.2 (unitVector l)))

theorem abs_weightRe_le (ι : ℤ × ℤ) (p : ℝ × ℝ) : |weightRe ι p| ≤ 1 := by
  unfold weightRe
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.pi), div_le_one (by linarith)]
  exact (Real.abs_cos_le_one _).trans hpi

theorem abs_weightIm_le (ι : ℤ × ℤ) (p : ℝ × ℝ) : |weightIm ι p| ≤ 1 := by
  unfold weightIm
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  rw [abs_div, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.pi), div_le_one (by linarith)]
  exact (Real.abs_sin_le_one _).trans hpi

theorem measurable_weightRe (ι : ℤ × ℤ) : Measurable (weightRe ι) := by
  unfold weightRe modePhase; fun_prop

theorem measurable_weightIm (ι : ℤ × ℤ) : Measurable (weightIm ι) := by
  unfold weightIm modePhase; fun_prop

theorem modePhase_apply (ι : ℤ × ℤ) (τ φ : ℝ) :
    modePhase ι (τ, φ) = 2 * Real.pi * ι.1 * τ + ι.2 * φ := rfl

theorem modeAverage_eq_integral {β : Type*} (ι : ℤ × ℤ) {f : ℝ → ℝ → β → ℝ} (b : β)
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2 b) angleMeasure) :
    modeAverage ι f b = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ p,
      Complex.exp (((-modePhase ι p : ℝ) : ℂ) * Complex.I) * ((f p.1 p.2 b : ℝ) : ℂ) ∂angleMeasure := by
  have hE : Integrable (fun p : ℝ × ℝ =>
      Complex.exp (((-modePhase ι p : ℝ) : ℂ) * Complex.I) * ((f p.1 p.2 b : ℝ) : ℂ)) angleMeasure := by
    refine Integrable.mono' hf.norm ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_).mul ?_
      · unfold modePhase; fun_prop
      · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  unfold modeAverage
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [angleMeasure, integral_prod _ hE]
  push_cast
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [modePhase_apply]
  push_cast
  ring_nf

theorem re_modeAverage {β : Type*} (ι : ℤ × ℤ) {f : ℝ → ℝ → β → ℝ} (b : β)
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2 b) angleMeasure) :
    (modeAverage ι f b).re = ∫ p, weightRe ι p * f p.1 p.2 b ∂angleMeasure := by
  have hE : Integrable (fun p : ℝ × ℝ =>
      Complex.exp (((-modePhase ι p : ℝ) : ℂ) * Complex.I) * ((f p.1 p.2 b : ℝ) : ℂ)) angleMeasure := by
    refine Integrable.mono' hf.norm ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_).mul ?_
      · unfold modePhase; fun_prop
      · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  rw [modeAverage_eq_integral ι b hf, Complex.re_ofReal_mul, ← Complex.reCLM_apply,
    ← Complex.reCLM.integral_comp_comm hE, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Complex.reCLM_apply, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
    weightRe]
  ring

theorem im_modeAverage {β : Type*} (ι : ℤ × ℤ) {f : ℝ → ℝ → β → ℝ} (b : β)
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2 b) angleMeasure) :
    (modeAverage ι f b).im = ∫ p, weightIm ι p * f p.1 p.2 b ∂angleMeasure := by
  have hE : Integrable (fun p : ℝ × ℝ =>
      Complex.exp (((-modePhase ι p : ℝ) : ℂ) * Complex.I) * ((f p.1 p.2 b : ℝ) : ℂ)) angleMeasure := by
    refine Integrable.mono' hf.norm ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_).mul ?_
      · unfold modePhase; fun_prop
      · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  rw [modeAverage_eq_integral ι b hf, Complex.im_ofReal_mul, ← Complex.imCLM_apply,
    ← Complex.imCLM.integral_comp_comm hE, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Complex.imCLM_apply, Complex.im_mul_ofReal, Complex.exp_ofReal_mul_I_im, Real.sin_neg,
    weightIm]
  ring

theorem integrable_weight_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ × ℝ → ℝ}
    (hcm : Measurable c) (hc : ∀ p, |c p| ≤ 1) {F : ℝ × ℝ → E} (hF : Integrable F angleMeasure) :
    Integrable (fun p => c p • F p) angleMeasure := by
  refine Integrable.mono' hF.norm (hcm.aestronglyMeasurable.smul hF.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun p => ?_
  rw [norm_smul]
  have h1 : ‖c p‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hc _
  calc ‖c p‖ * ‖F p‖ ≤ 1 * ‖F p‖ := by gcongr
    _ = ‖F p‖ := one_mul _

theorem integral_coord {F : ℝ × ℝ → Space} (hF : Integrable F angleMeasure) (i : Fin 3) :
    (∫ p, F p ∂angleMeasure) i = ∫ p, F p i ∂angleMeasure := by
  simpa using ((EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hF).symm

theorem integrable_coord {F : ℝ × ℝ → Space} (hF : Integrable F angleMeasure) (i : Fin 3) :
    Integrable (fun p => F p i) angleMeasure := by
  simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hF

theorem clm_ext_unitVector {A B : Space →L[ℝ] Space} (h : ∀ j, A (unitVector j) = B (unitVector j)) :
    A = B := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [vec_eq_sum u]
  simp only [map_sum, map_smul, h]

theorem reMat_apply_unitVector (g : Fin 3 × Fin 3 → ℂ) (j : Fin 3) :
    reMat g (unitVector j) = ∑ i : Fin 3, (g (i, j)).re • unitVector i := by
  unfold reMat
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem imMat_apply_unitVector (g : Fin 3 × Fin 3 → ℂ) (j : Fin 3) :
    imMat g (unitVector j) = ∑ i : Fin 3, (g (i, j)).im • unitVector i := by
  unfold imMat
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem reVec_modeAverage (ι : ℤ × ℤ) {f : ℝ → ℝ → Space}
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2) angleMeasure) :
    reVec (modeAverage ι (fun τ φ i => f τ φ i)) = ∫ p, weightRe ι p • f p.1 p.2 ∂angleMeasure := by
  have hw := integrable_weight_smul (measurable_weightRe ι) (abs_weightRe_le ι) hf
  conv_rhs => rw [vec_eq_sum (∫ p, weightRe ι p • f p.1 p.2 ∂angleMeasure)]
  unfold reVec
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [re_modeAverage ι (f := fun τ φ i => f τ φ i) i (integrable_coord hf i), integral_coord hw i]
  simp [smul_eq_mul]

theorem imVec_modeAverage (ι : ℤ × ℤ) {f : ℝ → ℝ → Space}
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2) angleMeasure) :
    imVec (modeAverage ι (fun τ φ i => f τ φ i)) = ∫ p, weightIm ι p • f p.1 p.2 ∂angleMeasure := by
  have hw := integrable_weight_smul (measurable_weightIm ι) (abs_weightIm_le ι) hf
  conv_rhs => rw [vec_eq_sum (∫ p, weightIm ι p • f p.1 p.2 ∂angleMeasure)]
  unfold imVec
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [im_modeAverage ι (f := fun τ φ i => f τ φ i) i (integrable_coord hf i), integral_coord hw i]
  simp [smul_eq_mul]

theorem reMat_modeAverage (ι : ℤ × ℤ) {M : ℝ → ℝ → (Space →L[ℝ] Space)}
    (hM : Integrable (fun p : ℝ × ℝ => M p.1 p.2) angleMeasure) :
    reMat (modeAverage ι (fun τ φ ij => M τ φ (unitVector ij.2) ij.1)) =
      ∫ p, weightRe ι p • M p.1 p.2 ∂angleMeasure := by
  have hw := integrable_weight_smul (measurable_weightRe ι) (abs_weightRe_le ι) hM
  refine clm_ext_unitVector fun j => ?_
  rw [ContinuousLinearMap.integral_apply hw, reMat_apply_unitVector]
  have h := reVec_modeAverage ι (f := fun τ φ => M τ φ (unitVector j)) (hM.apply_continuousLinearMap _)
  unfold reVec at h
  exact h

theorem imMat_modeAverage (ι : ℤ × ℤ) {M : ℝ → ℝ → (Space →L[ℝ] Space)}
    (hM : Integrable (fun p : ℝ × ℝ => M p.1 p.2) angleMeasure) :
    imMat (modeAverage ι (fun τ φ ij => M τ φ (unitVector ij.2) ij.1)) =
      ∫ p, weightIm ι p • M p.1 p.2 ∂angleMeasure := by
  have hw := integrable_weight_smul (measurable_weightIm ι) (abs_weightIm_le ι) hM
  refine clm_ext_unitVector fun j => ?_
  rw [ContinuousLinearMap.integral_apply hw, imMat_apply_unitVector]
  have h := imVec_modeAverage ι (f := fun τ φ => M τ φ (unitVector j)) (hM.apply_continuousLinearMap _)
  unfold imVec at h
  exact h

theorem isWeakGradient_congr_ae {f f' : Space → Space} {g g' : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') : IsWeakGradient f' g' := by
  refine ⟨h.1.congr hf, h.2.1.congr hg, fun φ hφ i => ?_⟩
  have e1 : (fun y => φ y • g' y (unitVector i)) =ᵐ[volume] fun y => φ y • g y (unitVector i) := by
    filter_upwards [hg] with y hy; rw [hy]
  have e2 : (fun y => fderiv ℝ φ y (unitVector i) • f' y) =ᵐ[volume]
      fun y => fderiv ℝ φ y (unitVector i) • f y := by
    filter_upwards [hf] with y hy; rw [hy]
  rw [integral_congr_ae e1, integral_congr_ae e2]
  exact h.2.2 φ hφ i

theorem ae_slice_integrable {E : Type*} [NormedAddCommGroup E] {F : ℝ × ℝ → Space → E}
    (hF : ∀ K : Set Space, IsCompact K →
      Integrable (fun q : Space × (ℝ × ℝ) => F q.2 q.1) ((volume.restrict K).prod angleMeasure)) :
    ∀ᵐ y, Integrable (fun p => F p y) angleMeasure := by
  have hn : ∀ n : ℕ, ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) n)),
      Integrable (fun p => F p y) angleMeasure :=
    fun n => (hF _ (isCompact_closedBall 0 n)).prod_right_ae
  have hU : (⋃ n : ℕ, Metric.closedBall (0 : Space) n) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ‖y‖
    exact Set.mem_iUnion.2 ⟨n, by simpa using hn⟩
  have := (ae_restrict_iUnion_iff (fun n : ℕ => Metric.closedBall (0 : Space) n) _).2 hn
  rwa [hU, Measure.restrict_univ] at this

theorem weakGradient_sum {f : Fin 3 → Space → Space} {g : Fin 3 → Space → (Space →L[ℝ] Space)}
    (h : ∀ k, IsWeakGradient (f k) (g k)) (c : Fin 3 → ℝ) :
    IsWeakGradient (fun y => ∑ k : Fin 3, c k • f k y) (fun y => ∑ k : Fin 3, c k • g k y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact locallyIntegrable_finsetSum _ fun k _ => (h k).1.smul (c k)
  · exact locallyIntegrable_finsetSum _ fun k _ => (h k).2.1.smul (c k)
  · intro θ hθ i
    have hL : ∀ k : Fin 3, Integrable (fun y => c k • (θ y • g k y (unitVector i))) volume := by
      intro k
      have hi : Integrable (fun y => θ y • g k y) volume :=
        (h k).2.1.integrable_smul_left_of_hasCompactSupport hθ.1.continuous hθ.2
      exact (hi.apply_continuousLinearMap (unitVector i)).smul (c k)
    have hR : ∀ k : Fin 3, Integrable (fun y => c k • (fderiv ℝ θ y (unitVector i) • f k y)) volume := by
      intro k
      have hc : Continuous (fun y => fderiv ℝ θ y (unitVector i)) :=
        (hθ.1.continuous_fderiv (by simp)).clm_apply continuous_const
      exact ((h k).1.integrable_smul_left_of_hasCompactSupport hc (hθ.2.fderiv_apply (𝕜 := ℝ) _)).smul (c k)
    have e1 : (fun y => θ y • (∑ k : Fin 3, c k • g k y) (unitVector i)) =
        fun y => ∑ k : Fin 3, c k • (θ y • g k y (unitVector i)) := by
      funext y
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_comm]
    have e2 : (fun y => fderiv ℝ θ y (unitVector i) • ∑ k : Fin 3, c k • f k y) =
        fun y => ∑ k : Fin 3, c k • (fderiv ℝ θ y (unitVector i) • f k y) := by
      funext y
      simp only [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_comm]
    rw [e1, e2, integral_finsetSum (f := fun k y => c k • (θ y • g k y (unitVector i))) Finset.univ
        (fun k _ => hL k),
      integral_finsetSum (f := fun k y => c k • (fderiv ℝ θ y (unitVector i) • f k y)) Finset.univ
        (fun k _ => hR k), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul, integral_smul, (h k).2.2 θ hθ i, smul_neg]

theorem weakGradient_column_apply {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (u : Space) : IsWeakGradient (fun y => G y u) (fun y => (H y).flip u) := by
  have hs := weakGradient_sum h (fun k => u k)
  have ef : (fun y => G y u) = fun y => ∑ k : Fin 3, u k • G y (unitVector k) := by
    funext y
    conv_lhs => rw [vec_eq_sum u]
    simp only [map_sum, map_smul]
  have eg : (fun y => (H y).flip u) = fun y => ∑ k : Fin 3, u k • (H y).flip (unitVector k) := by
    funext y
    conv_lhs => rw [vec_eq_sum u]
    simp only [map_sum, map_smul]
  rw [ef, eg]
  exact hs

theorem ae_shift {p : ℝ → Prop} (hp : ∀ᵐ s, p s) (σ : ℝ) : ∀ᵐ q ∂angleMeasure, p (σ + q.1) := by
  have h1 : ∀ᵐ τ ∂(volume : Measure ℝ), p (σ + τ) :=
    (measurePreserving_add_left (volume : Measure ℝ) σ).quasiMeasurePreserving.ae hp
  have h2 : ∀ᵐ τ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), p (σ + τ) := ae_restrict_of_ae h1
  exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (ν := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))).ae h2

theorem ae_weakGradient_vel (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (σ : ℝ) :
    ∀ᵐ p ∂angleMeasure, IsWeakGradient (velFamily v σ p) (gradFamily hRot G σ p) := by
  filter_upwards [ae_shift hv.weak_gradient σ] with p hp
  refine weakGradient_rotate hp (rotIso hRot p.2) (fun y => ?_) (fun y u => ?_)
  · simp only [velFamily, rotIso_symm_apply, rotIso_apply]
  · simp only [gradFamily, rotConj_apply, rotIso_symm_apply, rotIso_apply]

theorem ae_weakGradient_column (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (σ : ℝ) (l : Fin 3) :
    ∀ᵐ p ∂angleMeasure, IsWeakGradient (columnFamily G l σ p) (secondDerivFamily hRot H l σ p) := by
  filter_upwards [ae_shift hv.weak_secondDeriv σ] with p hp
  have hc := weakGradient_column_apply hp (axialRot p.2 (unitVector l))
  refine weakGradient_rotate hc (rotIso hRot p.2) (fun y => ?_) (fun y u => ?_)
  · simp only [columnFamily, rotIso_symm_apply, rotIso_apply]
  · simp only [secondDerivFamily, rotConj_apply, rotIso_symm_apply, rotIso_apply, ContinuousLinearMap.flip_apply]

theorem integrable_of_rot {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {m : Measure (Space × (ℝ × ℝ))} {u : Space × (ℝ × ℝ) → E} (hu : Integrable u m) (Φ : ℝ → E → F)
    (hΦ : Continuous (fun q : ℝ × E => Φ q.1 q.2)) (hb : ∀ φ A, ‖Φ φ A‖ ≤ ‖A‖) :
    Integrable (fun q => Φ q.2.2 (u q)) m := by
  refine Integrable.mono' hu.norm ?_ (Filter.Eventually.of_forall fun q => hb _ _)
  exact hΦ.comp_aestronglyMeasurable
    ((continuous_snd.snd.aestronglyMeasurable).prodMk hu.aestronglyMeasurable)

theorem continuous_axialRot_comp {X : Type*} [TopologicalSpace X] {a : X → ℝ} {w : X → Space}
    (ha : Continuous a) (hw : Continuous w) : Continuous (fun x => axialRot (a x) (w x)) := by
  unfold axialRot
  fun_prop

theorem norm_unitVector_one (l : Fin 3) : ‖unitVector l‖ = 1 := by
  simp [unitVector]

theorem continuous_rotConj (hRot : AxialRotationHolds) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space) => rotConj hRot q.1 q.2) := by
  refine continuous_clm_apply.2 fun u => ?_
  have e : (fun q : ℝ × (Space →L[ℝ] Space) => rotConj hRot q.1 q.2 u) =
      fun q => axialRot (-q.1) (q.2 (axialRot q.1 u)) := by
    funext q; rw [rotConj_apply]
  rw [e]
  exact continuous_axialRot_comp continuous_fst.neg
    (continuous_snd.clm_apply (continuous_axialRot_comp continuous_fst continuous_const))

theorem norm_rotConj_le (hRot : AxialRotationHolds) (φ : ℝ) (A : Space →L[ℝ] Space) :
    ‖rotConj hRot φ A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  rw [rotConj_apply, norm_axialRot hRot]
  calc ‖A (axialRot φ u)‖ ≤ ‖A‖ * ‖axialRot φ u‖ := A.le_opNorm _
    _ = ‖A‖ * ‖u‖ := by rw [norm_axialRot hRot]

theorem integrable_velFamily (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hvl : LocallyIntegrable (fun z : ℝ × Space => v z.1 z.2) volume) (σ : ℝ) {K : Set Space} (hK : IsCompact K) :
    Integrable (fun q : Space × (ℝ × ℝ) => velFamily v σ q.2 q.1) ((volume.restrict K).prod angleMeasure) :=
  integrable_of_rot (integrable_rotated hRot hv.measurable_velocity hvl σ hK) (fun φ w => axialRot (-φ) w)
    (continuous_axialRot_comp (X := ℝ × Space) continuous_fst.neg continuous_snd)
    (fun _ _ => (norm_axialRot hRot _ _).le)

theorem integrable_gradFamily (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hGl : LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume) (σ : ℝ) {K : Set Space} (hK : IsCompact K) :
    Integrable (fun q : Space × (ℝ × ℝ) => gradFamily hRot G σ q.2 q.1) ((volume.restrict K).prod angleMeasure) :=
  integrable_of_rot (integrable_rotated hRot hv.measurable_gradient hGl σ hK) (fun φ A => rotConj hRot φ A)
    (continuous_rotConj hRot) (fun φ A => norm_rotConj_le hRot φ A)

theorem integrable_columnFamily (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hGl : LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume) (σ : ℝ) (l : Fin 3)
    {K : Set Space} (hK : IsCompact K) :
    Integrable (fun q : Space × (ℝ × ℝ) => columnFamily G l σ q.2 q.1) ((volume.restrict K).prod angleMeasure) := by
  refine integrable_of_rot (integrable_rotated hRot hv.measurable_gradient hGl σ hK)
    (fun φ A => axialRot (-φ) (A (axialRot φ (unitVector l)))) ?_ ?_
  · exact continuous_axialRot_comp (X := ℝ × (Space →L[ℝ] Space)) continuous_fst.neg
      (continuous_snd.clm_apply (continuous_axialRot_comp continuous_fst continuous_const))
  · intro φ A
    rw [norm_axialRot hRot]
    calc ‖A (axialRot φ (unitVector l))‖ ≤ ‖A‖ * ‖axialRot φ (unitVector l)‖ := A.le_opNorm _
      _ = ‖A‖ := by rw [norm_axialRot hRot, norm_unitVector_one, mul_one]

theorem continuous_secondDerivConj (hRot : AxialRotationHolds) (l : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      rotConj hRot q.1 (q.2.flip (axialRot q.1 (unitVector l)))) := by
  refine continuous_clm_apply.2 fun u => ?_
  have e : (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      rotConj hRot q.1 (q.2.flip (axialRot q.1 (unitVector l))) u) =
      fun q => axialRot (-q.1) (q.2 (axialRot q.1 u) (axialRot q.1 (unitVector l))) := by
    funext q; rw [rotConj_apply]; rfl
  rw [e]
  have h1 : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => q.2 (axialRot q.1 u)) :=
    continuous_snd.clm_apply (continuous_axialRot_comp continuous_fst continuous_const)
  have h2 : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => axialRot q.1 (unitVector l)) :=
    continuous_axialRot_comp continuous_fst continuous_const
  exact continuous_axialRot_comp continuous_fst.neg (h1.clm_apply h2)

theorem integrable_secondDerivFamily (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hHl : LocallyIntegrable (fun z : ℝ × Space => H z.1 z.2) volume) (σ : ℝ) (l : Fin 3)
    {K : Set Space} (hK : IsCompact K) :
    Integrable (fun q : Space × (ℝ × ℝ) => secondDerivFamily hRot H l σ q.2 q.1) ((volume.restrict K).prod angleMeasure) := by
  refine integrable_of_rot (integrable_rotated hRot hv.measurable_secondDeriv hHl σ hK)
    (fun φ B => rotConj hRot φ (B.flip (axialRot φ (unitVector l)))) ?_ ?_
  · beta_reduce
    exact continuous_secondDerivConj hRot l
  · intro φ B
    refine (norm_rotConj_le hRot φ _).trans ?_
    calc ‖B.flip (axialRot φ (unitVector l))‖ ≤ ‖B.flip‖ * ‖axialRot φ (unitVector l)‖ := B.flip.le_opNorm _
      _ = ‖B‖ := by rw [norm_axialRot hRot, norm_unitVector_one, mul_one, ContinuousLinearMap.opNorm_flip]

theorem sum_diag_eq_trace (B : Space →L[ℝ] Space) :
    ∑ i : Fin 3, (B (unitVector i)) i = LinearMap.trace ℝ Space (B : Space →ₗ[ℝ] Space) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp [unitVector]

theorem diag_sum_rotate (hRot : AxialRotationHolds) (φ : ℝ) (A : Space →L[ℝ] Space) :
    ∑ i : Fin 3, (axialRot (-φ) (A (axialRot φ (unitVector i)))) i = ∑ i : Fin 3, (A (unitVector i)) i := by
  have h := sum_diag_eq_trace (rotConj hRot φ A)
  simp only [rotConj_apply] at h
  rw [h, sum_diag_eq_trace A]
  have e : (rotConj hRot φ A : Space →ₗ[ℝ] Space) =
      ((rotIso hRot φ).symm.toLinearEquiv : Space →ₗ[ℝ] Space) ∘ₗ
        ((A : Space →ₗ[ℝ] Space) ∘ₗ ((rotIso hRot φ).toLinearEquiv : Space →ₗ[ℝ] Space)) := rfl
  rw [e, LinearMap.trace_comp_comm']
  congr 1
  ext1 w
  simp

theorem measurePreserving_shiftRot (hRot : AxialRotationHolds) :
    MeasurePreserving (fun q : (ℝ × ℝ) × (ℝ × Space) => (q.1, ((q.2.1 + q.1.1, axialRot q.1.2 q.2.2) : ℝ × Space)))
      (angleMeasure.prod (volume : Measure (ℝ × Space))) (angleMeasure.prod (volume : Measure (ℝ × Space))) := by
  have hr : Continuous (fun x : (ℝ × ℝ) × (ℝ × Space) => axialRot x.1.2 x.2.2) := by
    unfold axialRot; fun_prop
  have ha : Continuous (fun x : (ℝ × ℝ) × (ℝ × Space) => x.2.1 + x.1.1) := by fun_prop
  have hc : Continuous (fun x : (ℝ × ℝ) × (ℝ × Space) => ((x.2.1 + x.1.1, axialRot x.1.2 x.2.2) : ℝ × Space)) :=
    ha.prodMk hr
  have hg : Measurable (Function.uncurry fun (p : ℝ × ℝ) (w : ℝ × Space) =>
      ((w.1 + p.1, axialRot p.2 w.2) : ℝ × Space)) := hc.measurable
  have h := MeasurePreserving.skew_product (MeasurePreserving.id angleMeasure) hg
    (μc := (volume : Measure (ℝ × Space))) (μd := (volume : Measure (ℝ × Space)))
    (Filter.Eventually.of_forall fun p => ?_)
  · exact h
  obtain ⟨R, hR⟩ := hRot.1 p.2
  have hm := (measurePreserving_add_right (volume : Measure ℝ) p.1).prod R.measurePreserving
  rw [← Measure.volume_eq_prod] at hm
  have hf : (Prod.map (fun x : ℝ => x + p.1) (R : Space → Space)) =
      fun w : ℝ × Space => ((w.1 + p.1, axialRot p.2 w.2) : ℝ × Space) := by
    funext w; simp [Prod.map, hR]
  rw [← hf]
  exact hm.map_eq

theorem quasiMeasurePreserving_shiftRot (hRot : AxialRotationHolds) :
    Measure.QuasiMeasurePreserving
      (fun q : (ℝ × Space) × (ℝ × ℝ) => ((q.1.1 + q.2.1, axialRot q.2.2 q.1.2) : ℝ × Space))
      ((volume : Measure (ℝ × Space)).prod angleMeasure) volume :=
  Measure.quasiMeasurePreserving_snd.comp
    ((measurePreserving_shiftRot hRot).comp Measure.measurePreserving_swap).quasiMeasurePreserving

theorem ae_zero_of_ae_ae {u : ℝ × Space → ℝ} (hu : AEStronglyMeasurable u volume)
    (h : ∀ᵐ σ, ∀ᵐ y, u (σ, y) = 0) : ∀ᵐ w, u w = 0 := by
  have hm := hu.stronglyMeasurable_mk.measurable
  have he : ∀ᵐ w ∂((volume : Measure ℝ).prod (volume : Measure Space)), u w = hu.mk u w := hu.ae_eq_mk
  show ∀ᵐ w ∂((volume : Measure ℝ).prod (volume : Measure Space)), u w = 0
  have h2 := Measure.ae_ae_of_ae_prod he
  have h3 : ∀ᵐ σ, ∀ᵐ y, hu.mk u (σ, y) = 0 := by
    filter_upwards [h, h2] with σ h1 h2
    filter_upwards [h1, h2] with y a b
    rw [← b, a]
  have hS : MeasurableSet {w : ℝ × Space | hu.mk u w = 0} := hm (measurableSet_singleton 0)
  have h4 := (Measure.ae_prod_iff_ae_ae hS).2 h3
  filter_upwards [h4, he] with w a b
  rw [b]; exact a

theorem ae_trace_zero {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ w : ℝ × Space, ∑ i : Fin 3, (G w.1 w.2 (unitVector i)) i = 0 := by
  have hc : Continuous (fun A : Space →L[ℝ] Space => ∑ i : Fin 3, (A (unitVector i)) i) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (PiLp.continuous_apply 2 _ i).comp (continuous_id.clm_apply continuous_const)
  exact ae_zero_of_ae_ae (hc.comp_aestronglyMeasurable hv.measurable_gradient) hv.divergence_free

theorem ae_ae_trace_rot (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ z : ℝ × Space, ∀ᵐ p ∂angleMeasure,
      ∑ i : Fin 3, (G (z.1 + p.1) (axialRot p.2 z.2) (unitVector i)) i = 0 :=
  Measure.ae_ae_of_ae_prod ((quasiMeasurePreserving_shiftRot hRot).ae (ae_trace_zero hv))

theorem integrable_shiftRot_box {E : Type*} [NormedAddCommGroup E] (hRot : AxialRotationHolds)
    {F : ℝ → Space → E} (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) (n : ℕ) :
    Integrable (fun q : (ℝ × Space) × (ℝ × ℝ) => F (q.1.1 + q.2.1) (axialRot q.2.2 q.1.2))
      ((volume.restrict (Set.Icc (-(n : ℝ)) n ×ˢ Metric.closedBall (0 : Space) n)).prod angleMeasure) := by
  set box : Set (ℝ × Space) := Set.Icc (-(n : ℝ)) n ×ˢ Metric.closedBall (0 : Space) n with hbox
  set B' : Set (ℝ × Space) := Set.Icc (-(n : ℝ)) (n + 1) ×ˢ Metric.closedBall (0 : Space) n with hB'
  have hboxm : MeasurableSet box := measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hB'm : MeasurableSet B' := measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hB'c : IsCompact B' := isCompact_Icc.prod (isCompact_closedBall (0 : Space) n)
  set Fb : ℝ × Space → ℝ := B'.indicator (fun w => ‖F w.1 w.2‖) with hFbdef
  have hFb : Integrable Fb volume := (integrable_indicator_iff hB'm).2 (hFl.integrableOn_isCompact hB'c).norm
  have h1 : Integrable (fun r : (ℝ × ℝ) × (ℝ × Space) => Fb r.2) (angleMeasure.prod volume) :=
    hFb.comp_snd angleMeasure
  have hm := (measurePreserving_shiftRot hRot).comp
    (Measure.measurePreserving_swap (μ := (volume : Measure (ℝ × Space))) (ν := angleMeasure))
  have hFbΦ : Integrable (fun q : (ℝ × Space) × (ℝ × ℝ) => Fb (q.1.1 + q.2.1, axialRot q.2.2 q.1.2))
      ((volume : Measure (ℝ × Space)).prod angleMeasure) :=
    (hm.integrable_comp h1.aestronglyMeasurable).2 h1
  have hle : (volume.restrict box).prod angleMeasure ≤ (volume : Measure (ℝ × Space)).prod angleMeasure :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  refine Integrable.mono' (hFbΦ.mono_measure hle)
    ((hFm.comp_quasiMeasurePreserving (quasiMeasurePreserving_shiftRot hRot)).mono_measure hle) ?_
  have hq1 : ∀ᵐ q ∂((volume.restrict box).prod angleMeasure), q.1 ∈ box :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hboxm)
  have hq2 : ∀ᵐ q ∂((volume.restrict box).prod angleMeasure), q.2.1 ∈ Set.Ioc (0 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc))
  filter_upwards [hq1, hq2] with q a b
  have hmem : ((q.1.1 + q.2.1, axialRot q.2.2 q.1.2) : ℝ × Space) ∈ B' := by
    rw [hbox] at a
    obtain ⟨⟨a1, a2⟩, a3⟩ := a
    refine ⟨⟨by linarith [b.1], by linarith [b.2]⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_axialRot hRot]
    rwa [Metric.mem_closedBall, dist_zero_right] at a3
  rw [hFbdef, Set.indicator_of_mem hmem]

theorem ae_integrable_shiftRot {E : Type*} [NormedAddCommGroup E] (hRot : AxialRotationHolds)
    {F : ℝ → Space → E} (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFl : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume) :
    ∀ᵐ z : ℝ × Space, Integrable (fun p : ℝ × ℝ => F (z.1 + p.1) (axialRot p.2 z.2)) angleMeasure := by
  have hn : ∀ n : ℕ, ∀ᵐ z : ℝ × Space, z ∈ Set.Icc (-(n : ℝ)) n ×ˢ Metric.closedBall (0 : Space) n →
      Integrable (fun p : ℝ × ℝ => F (z.1 + p.1) (axialRot p.2 z.2)) angleMeasure := fun n =>
    (ae_restrict_iff' (measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet)).1
      (integrable_shiftRot_box hRot hFm hFl n).prod_right_ae
  filter_upwards [ae_all_iff.2 hn] with z hz
  obtain ⟨n, hn⟩ := exists_nat_ge (max |z.1| ‖z.2‖)
  refine hz n ⟨⟨?_, ?_⟩, ?_⟩
  · linarith [neg_abs_le z.1, le_max_left |z.1| ‖z.2‖]
  · linarith [le_abs_self z.1, le_max_left |z.1| ‖z.2‖]
  · rw [Metric.mem_closedBall, dist_zero_right]; linarith [le_max_right |z.1| ‖z.2‖]

theorem iterated_intervalIntegral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → ℝ → E}
    (hF : Integrable (fun p : ℝ × ℝ => F p.1 p.2) angleMeasure) :
    ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), F τ φ = ∫ p, F p.1 p.2 ∂angleMeasure := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  exact (integral_prod _ hF).symm

theorem divergence_part (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hGl : LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume) (ι : ℤ × ℤ) :
    ∀ᵐ z : ℝ × Space, ∑ i : Fin 3, modeGrad ι G z.1 z.2 (i, i) = 0 := by
  filter_upwards [ae_ae_trace_rot hRot hv, ae_integrable_shiftRot hRot hv.measurable_gradient hGl] with z hz hint
  set E : ℝ × ℝ → ℂ := fun p => Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))
    with hE
  set f : Fin 3 → ℝ × ℝ → ℝ := fun i p =>
    (axialRot (-p.2) (G (z.1 + p.1) (axialRot p.2 z.2) (axialRot p.2 (unitVector i)))) i with hfdef
  have hEc : Continuous E := by rw [hE]; fun_prop
  have hEn : ∀ p, ‖E p‖ = 1 := fun p => by rw [hE, Complex.norm_exp]; simp
  have hf : ∀ i, Integrable (fun p => E p * ((f i p : ℝ) : ℂ)) angleMeasure := by
    intro i
    have hc : Continuous (fun x : (ℝ × ℝ) × (Space →L[ℝ] Space) =>
        (axialRot (-x.1.2) (x.2 (axialRot x.1.2 (unitVector i)))) i) := by
      unfold axialRot; fun_prop
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (p, G (z.1 + p.1) (axialRot p.2 z.2))) angleMeasure :=
      aestronglyMeasurable_id.prodMk hint.aestronglyMeasurable
    have hfm : AEStronglyMeasurable (f i) angleMeasure := (hc.comp_aestronglyMeasurable h2 : _)
    refine Integrable.mono' hint.norm (hEc.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hfm)) (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul, hEn, one_mul, Complex.norm_real]
    calc ‖f i p‖ ≤ ‖axialRot (-p.2) (G (z.1 + p.1) (axialRot p.2 z.2) (axialRot p.2 (unitVector i)))‖ :=
          PiLp.norm_apply_le _ i
      _ = ‖G (z.1 + p.1) (axialRot p.2 z.2) (axialRot p.2 (unitVector i))‖ := norm_axialRot hRot _ _
      _ ≤ ‖G (z.1 + p.1) (axialRot p.2 z.2)‖ * ‖axialRot p.2 (unitVector i)‖ := (G _ _).le_opNorm _
      _ = ‖G (z.1 + p.1) (axialRot p.2 z.2)‖ := by
          rw [norm_axialRot hRot]; simp [unitVector]
  have hmode : ∀ i, modeGrad ι G z.1 z.2 (i, i) =
      (1 / (2 * Real.pi) : ℂ) * ∫ p, E p * ((f i p : ℝ) : ℂ) ∂angleMeasure := by
    intro i
    have h := iterated_intervalIntegral_eq (F := fun τ φ => E (τ, φ) * ((f i (τ, φ) : ℝ) : ℂ)) (hf i)
    exact congrArg (fun w => (1 / (2 * Real.pi) : ℂ) * w) h
  rw [Finset.sum_congr rfl fun i _ => hmode i, ← Finset.mul_sum,
    ← integral_finsetSum (f := fun i p => E p * ((f i p : ℝ) : ℂ)) Finset.univ (fun i _ => hf i)]
  have h0 : (fun p => ∑ i : Fin 3, E p * ((f i p : ℝ) : ℂ)) =ᵐ[angleMeasure] 0 := by
    filter_upwards [hz] with p hp
    rw [← Finset.mul_sum, ← Complex.ofReal_sum]
    have hs : ∑ i : Fin 3, f i p = ∑ i : Fin 3, (G (z.1 + p.1) (axialRot p.2 z.2) (unitVector i)) i :=
      diag_sum_rotate hRot p.2 _
    rw [hs, hp]
    simp
  rw [integral_congr_ae h0]
  simp

theorem modeGrad_eq_average (hRot : AxialRotationHolds) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (σ : ℝ) (y : Space) :
    modeGrad ι G σ y = modeAverage ι (fun τ φ ij => gradFamily hRot G σ (τ, φ) y (unitVector ij.2) ij.1) := by
  unfold modeGrad
  congr 1
  funext τ φ ij
  simp only [gradFamily, rotConj_apply]

theorem modeSecondDeriv_eq_average (hRot : AxialRotationHolds) (ι : ℤ × ℤ)
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (l : Fin 3) (σ : ℝ) (y : Space) :
    (fun ij : Fin 3 × Fin 3 => modeSecondDeriv ι H σ y (ij.1, ij.2, l)) =
      modeAverage ι (fun τ φ ij => secondDerivFamily hRot H l σ (τ, φ) y (unitVector ij.2) ij.1) := by
  funext ij
  unfold modeSecondDeriv modeAverage
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  refine intervalIntegral.integral_congr fun φ _ => ?_
  simp only [secondDerivFamily, rotConj_apply, ContinuousLinearMap.flip_apply]

theorem velocity_part (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hvl : LocallyIntegrable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hGl : LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume) (ι : ℤ × ℤ) :
    ∀ᵐ σ, IsWeakGradient (fun y => reVec (modeVel ι v σ y)) (fun y => reMat (modeGrad ι G σ y)) ∧
      IsWeakGradient (fun y => imVec (modeVel ι v σ y)) (fun y => imMat (modeGrad ι G σ y)) := by
  refine Filter.Eventually.of_forall fun σ => ?_
  have hav := fun (K : Set Space) (hK : IsCompact K) => integrable_velFamily hRot hv hvl σ hK
  have hag := fun (K : Set Space) (hK : IsCompact K) => integrable_gradFamily hRot hv hGl σ hK
  have hw := ae_weakGradient_vel hRot hv σ
  have sv := ae_slice_integrable hav
  have sg := ae_slice_integrable hag
  constructor
  · refine isWeakGradient_congr_ae
      (weakGradient_average (weightRe ι) (measurable_weightRe ι) (abs_weightRe_le ι) hav hag hw) ?_ ?_
    · filter_upwards [sv] with y hy
      exact (reVec_modeAverage ι (f := fun τ φ => velFamily v σ (τ, φ) y) hy).symm
    · filter_upwards [sg] with y hy
      rw [modeGrad_eq_average hRot]
      exact (reMat_modeAverage ι (M := fun τ φ => gradFamily hRot G σ (τ, φ) y) hy).symm
  · refine isWeakGradient_congr_ae
      (weakGradient_average (weightIm ι) (measurable_weightIm ι) (abs_weightIm_le ι) hav hag hw) ?_ ?_
    · filter_upwards [sv] with y hy
      exact (imVec_modeAverage ι (f := fun τ φ => velFamily v σ (τ, φ) y) hy).symm
    · filter_upwards [sg] with y hy
      rw [modeGrad_eq_average hRot]
      exact (imMat_modeAverage ι (M := fun τ φ => gradFamily hRot G σ (τ, φ) y) hy).symm

theorem secondDeriv_part (hRot : AxialRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hGl : LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hHl : LocallyIntegrable (fun z : ℝ × Space => H z.1 z.2) volume) (ι : ℤ × ℤ) :
    ∀ᵐ σ, ∀ l : Fin 3,
      IsWeakGradient (fun y => reVec (fun i => modeGrad ι G σ y (i, l)))
          (fun y => reMat (fun ij => modeSecondDeriv ι H σ y (ij.1, ij.2, l))) ∧
        IsWeakGradient (fun y => imVec (fun i => modeGrad ι G σ y (i, l)))
          (fun y => imMat (fun ij => modeSecondDeriv ι H σ y (ij.1, ij.2, l))) := by
  refine Filter.Eventually.of_forall fun σ l => ?_
  have hac := fun (K : Set Space) (hK : IsCompact K) => integrable_columnFamily hRot hv hGl σ l hK
  have hah := fun (K : Set Space) (hK : IsCompact K) => integrable_secondDerivFamily hRot hv hHl σ l hK
  have hw := ae_weakGradient_column hRot hv σ l
  have sc := ae_slice_integrable hac
  have sh := ae_slice_integrable hah
  have ec : ∀ y, (fun i => modeGrad ι G σ y (i, l)) =
      modeAverage ι (fun τ φ i => columnFamily G l σ (τ, φ) y i) := fun y => rfl
  constructor
  · refine isWeakGradient_congr_ae
      (weakGradient_average (weightRe ι) (measurable_weightRe ι) (abs_weightRe_le ι) hac hah hw) ?_ ?_
    · filter_upwards [sc] with y hy
      rw [ec]
      exact (reVec_modeAverage ι (f := fun τ φ => columnFamily G l σ (τ, φ) y) hy).symm
    · filter_upwards [sh] with y hy
      rw [modeSecondDeriv_eq_average hRot]
      exact (reMat_modeAverage ι (M := fun τ φ => secondDerivFamily hRot H l σ (τ, φ) y) hy).symm
  · refine isWeakGradient_congr_ae
      (weakGradient_average (weightIm ι) (measurable_weightIm ι) (abs_weightIm_le ι) hac hah hw) ?_ ?_
    · filter_upwards [sc] with y hy
      rw [ec]
      exact (imVec_modeAverage ι (f := fun τ φ => columnFamily G l σ (τ, φ) y) hy).symm
    · filter_upwards [sh] with y hy
      rw [modeSecondDeriv_eq_average hRot]
      exact (imMat_modeAverage ι (M := fun τ φ => secondDerivFamily hRot H l σ (τ, φ) y) hy).symm

end ModeDerivative.Internal

open ModeDerivative.Internal in
theorem modeDerivativeHolds_of (hRot : AxialRotationHolds) (hLoc : PerturbationLocalIntegrabilityHolds) :
    ModeDerivativeHolds := by
  intro Γ P v G H g hv ι
  obtain ⟨hvl, hGl, hHl⟩ := hLoc Γ P v G H g hv
  exact ⟨velocity_part hRot hv hvl hGl ι, secondDeriv_part hRot hv hGl hHl ι, divergence_part hRot hv hGl ι⟩

end Coercive

end Breakdown
