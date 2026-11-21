import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace GainInternal

def azimuthalField (y : Space) : Fin 3 → ℝ := ![-(y 1), y 0, 0]

theorem azimuthalField_sq (y : Space) : ∑ j, azimuthalField y j ^ 2 = cylRadius y ^ 2 := by
  rw [cylRadius, Real.sq_sqrt (by positivity)]
  simp [azimuthalField, Fin.sum_univ_three]
  ring

theorem gain_of_identity {β : Type*} [Fintype β] (w : β → ℂ) (g : β → Fin 3 → ℂ) (Bw : β → ℂ)
    (X : Fin 3 → ℝ) (r k c : ℝ) (hX : ∑ j, X j ^ 2 = r ^ 2) (hc : 0 ≤ c) (hkc : c ≤ |k|)
    (hB : cnormSq Bw ≤ c ^ 2 * cnormSq w)
    (hid : ∀ b, ∑ j, g b j * (X j : ℂ) = (k : ℂ) * Complex.I * w b + Bw b) :
    (|k| - c) ^ 2 / r ^ 2 * cnormSq w ≤ ∑ b, ∑ j, ‖g b j‖ ^ 2 := by
  have hS : 0 ≤ ∑ b, ∑ j, ‖g b j‖ ^ 2 := by positivity
  have hrow : ∀ b, ‖∑ j, g b j * (X j : ℂ)‖ ^ 2 ≤ (∑ j, ‖g b j‖ ^ 2) * r ^ 2 := by
    intro b
    have h1 : ‖∑ j, g b j * (X j : ℂ)‖ ≤ ∑ j, ‖g b j‖ * |X j| := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖g b j‖) (fun j => |X j|)
    simp only [sq_abs] at h2
    rw [hX] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hnorm : ∀ x : β → ℂ, cnormSq x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ β)‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    rfl
  have hsum : (WithLp.toLp 2 (fun b => ∑ j, g b j * (X j : ℂ)) : EuclideanSpace ℂ β)
      = ((k : ℂ) * Complex.I) • (WithLp.toLp 2 w : EuclideanSpace ℂ β) + WithLp.toLp 2 Bw := by
    rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
    congr 1
    funext b
    simp [hid b]
  have hN : ‖(WithLp.toLp 2 (fun b => ∑ j, g b j * (X j : ℂ)) : EuclideanSpace ℂ β)‖ ^ 2 ≤ r ^ 2 *
      ∑ b, ∑ j, ‖g b j‖ ^ 2 := by
    rw [← hnorm, cnormSq, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => (hrow b).trans (le_of_eq (mul_comm _ _))
  have hBn : ‖(WithLp.toLp 2 Bw : EuclideanSpace ℂ β)‖ ≤ c * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ β)‖ := by
    rw [hnorm, hnorm] at hB
    rw [← mul_pow] at hB
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hB
  have hlow : (|k| - c) * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ β)‖ ≤
      ‖(WithLp.toLp 2 (fun b => ∑ j, g b j * (X j : ℂ)) : EuclideanSpace ℂ β)‖ := by
    rw [hsum]
    have h1 := norm_sub_norm_le (((k : ℂ) * Complex.I) • (WithLp.toLp 2 w : EuclideanSpace ℂ β))
      (-(WithLp.toLp 2 Bw : EuclideanSpace ℂ β))
    rw [sub_neg_eq_add, norm_neg, norm_smul] at h1
    have hk : ‖(k : ℂ) * Complex.I‖ = |k| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [hk] at h1
    nlinarith
  have hsq : (|k| - c) ^ 2 * cnormSq w ≤ r ^ 2 * ∑ b, ∑ j, ‖g b j‖ ^ 2 := by
    rw [hnorm, ← mul_pow]
    exact (pow_le_pow_left₀ (mul_nonneg (by linarith) (norm_nonneg _)) hlow 2).trans hN
  rcases eq_or_ne r 0 with hr | hr
  · simp [hr, hS]
  · have hr2 : 0 < r ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hr2]
    linarith [mul_comm (r ^ 2) (∑ b, ∑ j, ‖g b j‖ ^ 2)]

theorem ae_of_ae_ae {p : ℝ × Space → Prop} (hp : NullMeasurableSet {z | p z} volume)
    (h : ∀ᵐ σ, ∀ᵐ y, p (σ, y)) : ∀ᵐ z : ℝ × Space, p z := by
  obtain ⟨t, ht1, ht2, hpt⟩ := hp.exists_measurable_subset_ae_eq
  have h1 : ∀ᵐ z : ℝ × Space, z ∈ t := by
    have h2 : ∀ᵐ σ, ∀ᵐ y, (σ, y) ∈ t := by
      have h3 := Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
        (hpt.mem_iff)
      filter_upwards [h, h3] with σ hσ h3σ
      filter_upwards [hσ, h3σ] with y hy h3y
      exact h3y.2 hy
    exact (Measure.ae_prod_mem_iff_ae_ae_mem (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
      ht2).2 h2
  filter_upwards [h1] with z hz
  exact ht1 hz

theorem continuous_axialRot : Continuous (fun p : ℝ × Space => axialRot p.1 p.2) := by
  unfold axialRot
  fun_prop

theorem continuous_axialRot_comp {X : Type*} [TopologicalSpace X] {a : X → ℝ} {y : X → Space}
    (ha : Continuous a) (hy : Continuous y) : Continuous (fun x => axialRot (a x) (y x)) :=
  Continuous.comp (g := fun p : ℝ × Space => axialRot p.1 p.2) (f := fun x => (a x, y x))
    continuous_axialRot (ha.prodMk hy)

theorem continuous_coord {X : Type*} [TopologicalSpace X] {y : X → Space} (hy : Continuous y) (i : Fin 3) :
    Continuous (fun x => y x i) := by
  have h : Continuous (fun u : Space => u i) := by fun_prop
  exact Continuous.comp (g := fun u : Space => u i) (f := y) h hy

theorem measurable_axialRot : Measurable (fun p : ℝ × Space => axialRot p.1 p.2) :=
  continuous_axialRot.measurable

theorem shift_quasiMeasurePreserving (hRot : AxialRotationHolds) :
    Measure.QuasiMeasurePreserving
      (fun p : ((ℝ × Space) × ℝ) × ℝ => ((p.1.1.1 + p.1.2, axialRot p.2 p.1.1.2) : ℝ × Space))
      ((((volume : Measure ℝ).prod (volume : Measure Space)).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
  have hA := measurePreserving_prodAssoc ((volume : Measure ℝ).prod (volume : Measure Space))
    (volume : Measure ℝ) (volume : Measure ℝ)
  have hS := Measure.measurePreserving_swap (μ := ((volume : Measure ℝ).prod (volume : Measure Space)))
    (ν := (volume : Measure ℝ).prod (volume : Measure ℝ))
  have hmap : ∀ x : ℝ × ℝ, Measure.map (fun z : ℝ × Space => ((z.1 + x.1, axialRot x.2 z.2) : ℝ × Space))
      ((volume : Measure ℝ).prod (volume : Measure Space)) = ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    intro x
    obtain ⟨R, hR⟩ := hRot.1 x.2
    have he : (fun z : ℝ × Space => ((z.1 + x.1, axialRot x.2 z.2) : ℝ × Space)) =
        Prod.map (fun σ : ℝ => σ + x.1) R := by
      funext z
      rw [Prod.map_apply, hR]
    rw [he]
    exact ((measurePreserving_add_right (volume : Measure ℝ) x.1).prod
      (LinearIsometryEquiv.measurePreserving R)).map_eq
  have hgm : Measurable (Function.uncurry fun (x : ℝ × ℝ) (z : ℝ × Space) =>
      ((z.1 + x.1, axialRot x.2 z.2) : ℝ × Space)) := by
    have h1 : Measurable (fun p : (ℝ × ℝ) × (ℝ × Space) => p.2.1 + p.1.1) := by fun_prop
    have hm : Measurable (fun q : (ℝ × ℝ) × (ℝ × Space) => ((q.1.2, q.2.2) : ℝ × Space)) :=
      measurable_fst.snd.prodMk measurable_snd.snd
    have h2 : Measurable (fun p : (ℝ × ℝ) × (ℝ × Space) => axialRot p.1.2 p.2.2) :=
      Measurable.comp (g := fun p : ℝ × Space => axialRot p.1 p.2)
        (f := fun q : (ℝ × ℝ) × (ℝ × Space) => ((q.1.2, q.2.2) : ℝ × Space)) measurable_axialRot hm
    exact Measurable.prodMk (f := fun p : (ℝ × ℝ) × (ℝ × Space) => p.2.1 + p.1.1)
      (g := fun p : (ℝ × ℝ) × (ℝ × Space) => axialRot p.1.2 p.2.2) h1 h2
  have hK := MeasurePreserving.skew_product (μa := (volume : Measure ℝ).prod (volume : Measure ℝ))
    (μc := ((volume : Measure ℝ).prod (volume : Measure Space))) (f := id) (MeasurePreserving.id _) hgm
    (ae_of_all _ hmap)
  have q1 := Measure.QuasiMeasurePreserving.comp (g := Prod.swap)
    (f := (MeasurableEquiv.prodAssoc : ((ℝ × Space) × ℝ) × ℝ ≃ᵐ (ℝ × Space) × (ℝ × ℝ)))
    hS.quasiMeasurePreserving hA.quasiMeasurePreserving
  have q2 := Measure.QuasiMeasurePreserving.comp
    (g := fun q : (ℝ × ℝ) × (ℝ × Space) => (id q.1, ((q.2.1 + q.1.1, axialRot q.1.2 q.2.2) : ℝ × Space)))
    (f := Prod.swap ∘ (MeasurableEquiv.prodAssoc : ((ℝ × Space) × ℝ) × ℝ ≃ᵐ (ℝ × Space) × (ℝ × ℝ)))
    hK.quasiMeasurePreserving q1
  have q3 := Measure.QuasiMeasurePreserving.comp (g := Prod.snd)
    (f := (fun q : (ℝ × ℝ) × (ℝ × Space) => (id q.1, ((q.2.1 + q.1.1, axialRot q.1.2 q.2.2) : ℝ × Space))) ∘
      Prod.swap ∘ (MeasurableEquiv.prodAssoc : ((ℝ × Space) × ℝ) × ℝ ≃ᵐ (ℝ × Space) × (ℝ × ℝ)))
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ).prod (volume : Measure ℝ))
      (ν := ((volume : Measure ℝ).prod (volume : Measure Space)))) q2
  exact q3

theorem shift_quasiMeasurePreserving_restrict (hRot : AxialRotationHolds) (s t : Set ℝ) :
    Measure.QuasiMeasurePreserving
      (fun p : ((ℝ × Space) × ℝ) × ℝ => ((p.1.1.1 + p.1.2, axialRot p.2 p.1.1.2) : ℝ × Space))
      ((((volume : Measure ℝ).prod (volume : Measure Space)).prod ((volume : Measure ℝ).restrict s)).prod
        ((volume : Measure ℝ).restrict t))
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
  refine (shift_quasiMeasurePreserving hRot).mono_left ?_
  refine Measure.AbsolutelyContinuous.prod (Measure.AbsolutelyContinuous.prod
    (Measure.AbsolutelyContinuous.refl _) ?_) ?_
  · exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  · exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

theorem aesm_average {F : Type*} [TopologicalSpace F]
    (hRot : AxialRotationHolds) (ι : ℤ × ℤ)
    (V : ℝ → Space → F) (hV : AEStronglyMeasurable (fun z : ℝ × Space => V z.1 z.2) volume)
    {β : Type*} (L : β → ℝ → F → ℝ) (b : β) (hL : Continuous (fun p : ℝ × F => L b p.1 p.2)) :
    AEStronglyMeasurable (fun z : ℝ × Space =>
      modeAverage ι (fun τ φ c => L c φ (V (z.1 + τ) (axialRot φ z.2))) b) volume := by
  unfold modeAverage
  refine AEStronglyMeasurable.const_mul ?_ _
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  simp only [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le h2pi]
  set μτ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
  set μφ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  have hcomp : AEStronglyMeasurable (fun p : ((ℝ × Space) × ℝ) × ℝ => V (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2))
      ((((volume : Measure ℝ).prod (volume : Measure Space)).prod μτ).prod μφ) :=
    (show AEStronglyMeasurable (fun z : ℝ × Space => V z.1 z.2)
      ((volume : Measure ℝ).prod (volume : Measure Space)) from hV).comp_quasiMeasurePreserving
      (shift_quasiMeasurePreserving_restrict hRot _ _)
  have hf : AEStronglyMeasurable (fun p : ((ℝ × Space) × ℝ) × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1.2 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I)) *
        ((L b p.2 (V (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)) : ℝ) : ℂ))
      ((((volume : Measure ℝ).prod (volume : Measure Space)).prod μτ).prod μφ) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (by fun_prop : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ =>
        Complex.exp (-(((2 * Real.pi * ι.1 * p.1.2 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I)))).aestronglyMeasurable
    · have hL' : AEStronglyMeasurable (fun p : ((ℝ × Space) × ℝ) × ℝ =>
          L b p.2 (V (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)))
          ((((volume : Measure ℝ).prod (volume : Measure Space)).prod μτ).prod μφ) :=
        hL.comp_aestronglyMeasurable (AEStronglyMeasurable.prodMk
          continuous_snd.aestronglyMeasurable hcomp)
      exact Complex.continuous_ofReal.comp_aestronglyMeasurable hL'
  have h1 := hf.integral_prod_right'
  exact h1.integral_prod_right'

theorem modeVel_aesm (hRot : AxialRotationHolds) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι v z.1 z.2) volume := by
  have h : ∀ i : Fin 3, AEStronglyMeasurable (fun z : ℝ × Space => modeVel ι v z.1 z.2 i) volume := by
    intro i
    have hc : Continuous (fun p : ℝ × Space => axialRot (-p.1) p.2) :=
      continuous_axialRot_comp continuous_fst.neg continuous_snd
    exact aesm_average hRot ι v hv (fun c φ x => axialRot (-φ) x c) i (continuous_coord hc i)
  exact (aemeasurable_pi_lambda _ (fun i => (h i).aemeasurable)).aestronglyMeasurable

theorem modeGrad_aesm (hRot : AxialRotationHolds) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeGrad ι G z.1 z.2) volume := by
  have h : ∀ ij : Fin 3 × Fin 3,
      AEStronglyMeasurable (fun z : ℝ × Space => modeGrad ι G z.1 z.2 ij) volume := by
    intro ij
    have he : Continuous (fun p : ℝ × (Space →L[ℝ] Space) => axialRot p.1 (unitVector ij.2)) :=
      continuous_axialRot_comp continuous_fst continuous_const
    have hM : Continuous (fun p : ℝ × (Space →L[ℝ] Space) => p.2 (axialRot p.1 (unitVector ij.2))) :=
      continuous_snd.clm_apply he
    have hc : Continuous (fun p : ℝ × (Space →L[ℝ] Space) =>
        axialRot (-p.1) (p.2 (axialRot p.1 (unitVector ij.2)))) :=
      continuous_axialRot_comp continuous_fst.neg hM
    have := aesm_average hRot ι G hG (fun (c : Fin 3 × Fin 3) (φ : ℝ) (M : Space →L[ℝ] Space) =>
      axialRot (-φ) (M (axialRot φ (unitVector c.2))) c.1) ij
      (continuous_coord hc ij.1)
    unfold modeGrad
    exact this
  exact (aemeasurable_pi_lambda _ (fun ij => (h ij).aemeasurable)).aestronglyMeasurable

theorem modeSecondDeriv_aesm (hRot : AxialRotationHolds) (ι : ℤ × ℤ)
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeSecondDeriv ι H z.1 z.2) volume := by
  have h : ∀ ijl : Fin 3 × Fin 3 × Fin 3,
      AEStronglyMeasurable (fun z : ℝ × Space => modeSecondDeriv ι H z.1 z.2 ijl) volume := by
    intro ijl
    have he1 : Continuous (fun p : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot p.1 (unitVector ijl.2.1)) :=
      continuous_axialRot_comp continuous_fst continuous_const
    have he2 : Continuous (fun p : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot p.1 (unitVector ijl.2.2)) :=
      continuous_axialRot_comp continuous_fst continuous_const
    have hM : Continuous (fun p : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
        p.2 (axialRot p.1 (unitVector ijl.2.1)) (axialRot p.1 (unitVector ijl.2.2))) :=
      (continuous_snd.clm_apply he1).clm_apply he2
    have hc : Continuous (fun p : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot (-p.1) (p.2 (axialRot p.1 (unitVector ijl.2.1)) (axialRot p.1 (unitVector ijl.2.2)))) :=
      continuous_axialRot_comp continuous_fst.neg hM
    have := aesm_average hRot ι H hH
      (fun (c : Fin 3 × Fin 3 × Fin 3) (φ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot (-φ) (M (axialRot φ (unitVector c.2.1)) (axialRot φ (unitVector c.2.2))) c.1) ijl
      (continuous_coord hc ijl.1)
    unfold modeSecondDeriv
    exact this
  exact (aemeasurable_pi_lambda _ (fun ijl => (h ijl).aemeasurable)).aestronglyMeasurable

theorem reVec_apply (x : Fin 3 → ℂ) (i : Fin 3) : reVec x i = (x i).re := by
  fin_cases i <;> simp [reVec, unitVector, Fin.sum_univ_three]

theorem imVec_apply (x : Fin 3 → ℂ) (i : Fin 3) : imVec x i = (x i).im := by
  fin_cases i <;> simp [imVec, unitVector, Fin.sum_univ_three]

theorem reMat_apply (g : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) : reMat g (unitVector j) i = (g (i, j)).re := by
  fin_cases i <;> fin_cases j <;> simp [reMat, unitVector, Fin.sum_univ_three, EuclideanSpace.inner_single_left]

theorem imMat_apply (g : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) : imMat g (unitVector j) i = (g (i, j)).im := by
  fin_cases i <;> fin_cases j <;> simp [imMat, unitVector, Fin.sum_univ_three, EuclideanSpace.inner_single_left]

theorem li_coord {f : Space → Space} (hf : LocallyIntegrable f) (i : Fin 3) :
    LocallyIntegrable (fun y => ((f y i : ℝ) : ℂ)) := by
  have := (Complex.ofRealCLM.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)).locallyIntegrableOn_comp
    (hf.locallyIntegrableOn Set.univ)
  rw [locallyIntegrableOn_univ] at this
  exact this

theorem li_apply {f : Space → (Space →L[ℝ] Space)} (hf : LocallyIntegrable f) (j : Fin 3) :
    LocallyIntegrable (fun y => f y (unitVector j)) := by
  have := (ContinuousLinearMap.apply ℝ Space (unitVector j)).locallyIntegrableOn_comp
    (hf.locallyIntegrableOn Set.univ)
  rw [locallyIntegrableOn_univ] at this
  exact this

theorem li_complex {f : Space → ℂ} {a b : Space → Space} (ha : LocallyIntegrable a)
    (hb : LocallyIntegrable b) (i : Fin 3) (hre : ∀ y, (f y).re = a y i) (him : ∀ y, (f y).im = b y i) :
    LocallyIntegrable f := by
  have h := (li_coord ha i).add ((li_coord hb i).smul Complex.I)
  have e : f = (fun y => ((a y i : ℝ) : ℂ)) + Complex.I • (fun y => ((b y i : ℝ) : ℂ)) := by
    funext y
    apply Complex.ext <;> simp [hre, him]
  rw [e]
  exact h

theorem test_deriv_continuous {φ : Space → ℝ} (hφ : IsTestFunction φ) (j : Fin 3) :
    Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
  ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem test_deriv_support {φ : Space → ℝ} (hφ : IsTestFunction φ) (j : Fin 3) :
    HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
  (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)

theorem integral_coord {f : Space → Space} (hf : Integrable f) (i : Fin 3) :
    ∫ y, f y i = (∫ y, f y) i := by
  have := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hf
  simpa using this

theorem weak_component_real (w : Space → Space) (g : Space → (Space →L[ℝ] Space))
    (h : IsWeakGradient w g) (φ : Space → ℝ) (hφ : IsTestFunction φ) (i j : Fin 3) :
    ∫ y, φ y * g y (unitVector j) i = -∫ y, fderiv ℝ φ y (unitVector j) * w y i := by
  have h1 := (li_apply h.2.1 j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have h2 := h.1.integrable_smul_left_of_hasCompactSupport (test_deriv_continuous hφ j)
    (test_deriv_support hφ j)
  have e := congrArg (fun x : Space => x i) (h.2.2 φ hφ j)
  simp only [PiLp.neg_apply] at e
  rw [← integral_coord h1, ← integral_coord h2] at e
  simpa using e

theorem weak_components (w : Space → Fin 3 → ℂ) (g : Space → Fin 3 × Fin 3 → ℂ)
    (hre : IsWeakGradient (fun y => reVec (w y)) (fun y => reMat (g y)))
    (him : IsWeakGradient (fun y => imVec (w y)) (fun y => imMat (g y))) :
    (∀ i, LocallyIntegrable (fun y => w y i)) ∧ (∀ i j, LocallyIntegrable (fun y => g y (i, j))) ∧
      ∀ φ : Space → ℝ, IsTestFunction φ → ∀ i j,
        ∫ y, (φ y : ℂ) * g y (i, j) = -∫ y, (fderiv ℝ φ y (unitVector j) : ℂ) * w y i := by
  have hw : ∀ i, LocallyIntegrable (fun y => w y i) := fun i =>
    li_complex hre.1 him.1 i (fun y => (reVec_apply _ _).symm) (fun y => (imVec_apply _ _).symm)
  have hg : ∀ i j, LocallyIntegrable (fun y => g y (i, j)) := fun i j =>
    li_complex (li_apply hre.2.1 j) (li_apply him.2.1 j) i (fun y => (reMat_apply _ _ _).symm)
      (fun y => (imMat_apply _ _ _).symm)
  refine ⟨hw, hg, fun φ hφ i j => ?_⟩
  have i1 : Integrable (fun y => (φ y : ℂ) * g y (i, j)) := by
    have := (hg i j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    simpa [Complex.real_smul] using this
  have i2 : Integrable (fun y => (fderiv ℝ φ y (unitVector j) : ℂ) * w y i) := by
    have := (hw i).integrable_smul_left_of_hasCompactSupport (test_deriv_continuous hφ j)
      (test_deriv_support hφ j)
    simpa [Complex.real_smul] using this
  have er := weak_component_real _ _ hre φ hφ i j
  have ei := weak_component_real _ _ him φ hφ i j
  simp only [reMat_apply, reVec_apply] at er
  simp only [imMat_apply, imVec_apply] at ei
  apply Complex.ext
  · have a1 := Complex.reCLM.integral_comp_comm i1
    have a2 := Complex.reCLM.integral_comp_comm i2
    simp only [Complex.reCLM_apply] at a1 a2
    rw [Complex.neg_re, ← a1, ← a2]
    simpa using er
  · have a1 := Complex.imCLM.integral_comp_comm i1
    have a2 := Complex.imCLM.integral_comp_comm i2
    simp only [Complex.imCLM_apply] at a1 a2
    rw [Complex.neg_im, ← a1, ← a2]
    simpa using ei

theorem hasDerivAt_axialRot (y : Space) (i : Fin 3) :
    HasDerivAt (fun ψ => axialRot ψ y i) (azimuthalField y i) 0 := by
  have e0 : ∀ ψ, axialRot ψ y 0 = Real.cos ψ * y 0 - Real.sin ψ * y 1 := fun ψ => by
    simp [axialRot, unitVector]
  have e1 : ∀ ψ, axialRot ψ y 1 = Real.sin ψ * y 0 + Real.cos ψ * y 1 := fun ψ => by
    simp [axialRot, unitVector]
  have e2 : ∀ ψ, axialRot ψ y 2 = y 2 := fun ψ => by
    simp [axialRot, unitVector]
  fin_cases i
  · simp only [Fin.zero_eta, e0]
    have h : azimuthalField y 0 = -Real.sin 0 * y 0 - Real.cos 0 * y 1 := by simp [azimuthalField]
    rw [h]
    exact ((Real.hasDerivAt_cos 0).mul_const (y 0)).sub ((Real.hasDerivAt_sin 0).mul_const (y 1))
  · simp only [Fin.mk_one, e1]
    have h : azimuthalField y 1 = Real.cos 0 * y 0 + -Real.sin 0 * y 1 := by simp [azimuthalField]
    rw [h]
    exact ((Real.hasDerivAt_sin 0).mul_const (y 0)).add ((Real.hasDerivAt_cos 0).mul_const (y 1))
  · simp only [Fin.reduceFinMk, e2]
    have h : azimuthalField y 2 = 0 := by simp [azimuthalField]
    rw [h]
    exact hasDerivAt_const (0 : ℝ) (y 2)

def azimuthalDeriv (φ : Space → ℝ) (y : Space) : ℝ :=
  ∑ j, azimuthalField y j * fderiv ℝ φ y (unitVector j)

theorem azimuthal_linear (j : Fin 3) :
    ∃ L : Space →L[ℝ] ℝ, (∀ y, azimuthalField y j = L y) ∧ L (unitVector j) = 0 := by
  fin_cases j
  · exact ⟨-(EuclideanSpace.proj (1 : Fin 3)), fun y => by simp [azimuthalField],
      by simp [unitVector]⟩
  · exact ⟨EuclideanSpace.proj (0 : Fin 3), fun y => by simp [azimuthalField],
      by simp [unitVector]⟩
  · exact ⟨0, fun y => by simp [azimuthalField], by simp⟩

theorem rot_integral (hRot : AxialRotationHolds) (s : ℝ) (F : Space → ℂ) :
    ∫ y, F (axialRot s y) = ∫ y, F y := by
  obtain ⟨R, hR⟩ := hRot.1 s
  simp only [← hR]
  exact R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding F

theorem rot_inv (hRot : AxialRotationHolds) (s : ℝ) (y : Space) :
    axialRot (-s) (axialRot s y) = y := by
  rw [← hRot.2.1, neg_add_cancel, hRot.2.2.1]

theorem test_integrable (φ : Space → ℝ) (hφ : IsTestFunction φ) (u : Space → ℂ)
    (hu : LocallyIntegrable u) : Integrable (fun y => (φ y : ℂ) * u y) := by
  have h := hu.integrable_smul_left_of_hasCompactSupport (g := fun y => (φ y : ℂ))
    (Complex.continuous_ofReal.comp hφ.1.continuous) (hφ.2.comp_left Complex.ofReal_zero)
  simpa only [smul_eq_mul] using h

theorem weak_along (φ : Space → ℝ) (hφ : IsTestFunction φ) {β : Type*} (w : Space → β → ℂ)
    (g : Space → β → Fin 3 → ℂ) (b : β) (hw : LocallyIntegrable (fun y => w y b))
    (hg : ∀ j, LocallyIntegrable (fun y => g y b j))
    (hweak : ∀ φ : Space → ℝ, IsTestFunction φ → ∀ j,
      ∫ y, (φ y : ℂ) * g y b j = -∫ y, (fderiv ℝ φ y (unitVector j) : ℂ) * w y b) :
    ∫ y, (φ y : ℂ) * ∑ j, g y b j * (azimuthalField y j : ℂ) =
      -∫ y, (azimuthalDeriv φ y : ℂ) * w y b := by
  have hj : ∀ j, ∫ y, (φ y : ℂ) * (g y b j * (azimuthalField y j : ℂ)) =
      -∫ y, ((azimuthalField y j * fderiv ℝ φ y (unitVector j) : ℝ) : ℂ) * w y b := by
    intro j
    obtain ⟨L, hL, hLj⟩ := azimuthal_linear j
    have htest : IsTestFunction (fun y => L y * φ y) :=
      ⟨L.contDiff.mul hφ.1, hφ.2.mul_left⟩
    have h := hweak _ htest j
    have hd : ∀ y, fderiv ℝ (fun y => L y * φ y) y (unitVector j) = L y * fderiv ℝ φ y (unitVector j) := by
      intro y
      rw [fderiv_fun_mul L.differentiableAt (hφ.1.differentiable (by simp)).differentiableAt]
      simp [hLj]
    simp only [hd] at h
    simp only [hL]
    rw [← h]
    congr 1
    funext y
    push_cast
    ring
  have hφi : ∀ j, Integrable (fun y => (φ y : ℂ) * (g y b j * (azimuthalField y j : ℂ))) := by
    intro j
    obtain ⟨L, hL, -⟩ := azimuthal_linear j
    have := test_integrable φ hφ _ ((hg j).mul_continuous (Complex.continuous_ofReal.comp L.continuous))
    simp only [hL]
    exact this
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => hφi j]
  simp only [hj, Finset.sum_neg_distrib]
  rw [← integral_finsetSum]
  · congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [azimuthalDeriv]
    push_cast
    rw [Finset.sum_mul]
  · intro j _
    obtain ⟨L, hL, -⟩ := azimuthal_linear j
    have hc : Continuous (fun y => L y * fderiv ℝ φ y (unitVector j)) :=
      L.continuous.mul ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hcs : HasCompactSupport (fun y => L y * fderiv ℝ φ y (unitVector j)) := by
      have := (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Space →L[ℝ] ℝ => T (unitVector j)) (by simp)
      exact this.mul_left
    have := hw.integrable_smul_left_of_hasCompactSupport (g := fun y => ((L y * fderiv ℝ φ y (unitVector j) : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hc) (hcs.comp_left Complex.ofReal_zero)
    simpa only [smul_eq_mul, hL] using this

theorem slope_limit (hRot : AxialRotationHolds) (φ : Space → ℝ) (hφ : IsTestFunction φ)
    (u : Space → ℂ) (hu : LocallyIntegrable u)
    (s : ℕ → ℝ) (hs0 : ∀ n, s n ≠ 0) (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => (s n)⁻¹ * ((∫ y, (φ (axialRot (-s n) y) : ℂ) * u y) - ∫ y, (φ y : ℂ) * u y))
      atTop (𝓝 (-∫ y, (azimuthalDeriv φ y : ℂ) * u y)) := by
  have hnsq : ∀ x : Space, ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have hco : ∀ t (x : Space), axialRot t x 0 = Real.cos t * x 0 - Real.sin t * x 1 ∧
      axialRot t x 1 = Real.sin t * x 0 + Real.cos t * x 1 ∧ axialRot t x 2 = x 2 := by
    intro t x
    refine ⟨?_, ?_, ?_⟩ <;> simp [axialRot, unitVector]
  have hnorm : ∀ t (x : Space), ‖axialRot t x‖ = ‖x‖ := by
    intro t x
    obtain ⟨R, hR⟩ := hRot.1 t
    rw [← hR, R.norm_map]
  have hcontR : ∀ t, Continuous (axialRot t) := by
    intro t
    obtain ⟨R, hR⟩ := hRot.1 t
    have : axialRot t = R := funext fun x => (hR x).symm
    rw [this]
    exact R.continuous
  have hchord : ∀ t (x : Space), ‖axialRot t x - x‖ ≤ |t| * ‖x‖ := by
    intro t x
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hnsq, hnsq, sq_abs]
    obtain ⟨h0, h1, h2⟩ := hco t x
    have hs : (axialRot t x - x) 0 = axialRot t x 0 - x 0 := rfl
    have hs1 : (axialRot t x - x) 1 = axialRot t x 1 - x 1 := rfl
    have hs2 : (axialRot t x - x) 2 = axialRot t x 2 - x 2 := rfl
    rw [hs, hs1, hs2, h0, h1, h2]
    have hcos := Real.one_sub_sq_div_two_le_cos (x := t)
    have hsc := Real.sin_sq_add_cos_sq t
    have key : (Real.cos t * x 0 - Real.sin t * x 1 - x 0) ^ 2 + (Real.sin t * x 0 + Real.cos t * x 1 - x 1) ^ 2
        + (x 2 - x 2) ^ 2 = (2 - 2 * Real.cos t) * (x 0 ^ 2 + x 1 ^ 2) := by
      linear_combination (x 0 ^ 2 + x 1 ^ 2) * hsc
    rw [key]
    have hA : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
    nlinarith [sq_nonneg (x 2), mul_le_mul_of_nonneg_right (show 2 - 2 * Real.cos t ≤ t ^ 2 by linarith) hA]
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2 hφ.1 (by simp)
  obtain ⟨ρ, hρ⟩ := hφ.2.isCompact.isBounded.subset_closedBall (0 : Space)
  have hout : ∀ x : Space, x ∉ Metric.closedBall (0 : Space) ρ → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hρ h)
  set F : ℕ → Space → ℂ := fun n y => (((s n)⁻¹ * (φ (axialRot (-s n) y) - φ y) : ℝ) : ℂ) * u y with hF
  have hφR : ∀ t, IsTestFunction (fun y => φ (axialRot t y)) := by
    intro t
    obtain ⟨R, hR⟩ := hRot.1 t
    have : (fun y => φ (axialRot t y)) = φ ∘ R := funext fun x => by simp [hR]
    rw [this]
    exact ⟨hφ.1.comp R.contDiff, hφ.2.comp_homeomorph R.toHomeomorph⟩
  have hsplit : ∀ n, (s n)⁻¹ * ((∫ y, (φ (axialRot (-s n) y) : ℂ) * u y) - ∫ y, (φ y : ℂ) * u y) =
      ∫ y, F n y := by
    intro n
    rw [← integral_sub (test_integrable _ (hφR (-s n)) u hu) (test_integrable φ hφ u hu),
      ← integral_const_mul]
    congr 1
    funext y
    simp only [hF]
    push_cast
    ring
  simp only [hsplit]
  have hlimf : (-∫ y, (azimuthalDeriv φ y : ℂ) * u y) = ∫ y, ((-azimuthalDeriv φ y : ℝ) : ℂ) * u y := by
    rw [← integral_neg]
    congr 1
    funext y
    push_cast
    ring
  rw [hlimf]
  refine tendsto_integral_of_dominated_convergence
    (fun y => (Metric.closedBall (0 : Space) ρ).indicator (fun y => (C : ℝ) * ρ * ‖u y‖) y) ?_ ?_ ?_ ?_
  · intro n
    refine (Continuous.aestronglyMeasurable ?_).mul hu.aestronglyMeasurable
    refine Complex.continuous_ofReal.comp ?_
    exact continuous_const.mul ((hφ.1.continuous.comp (hcontR _)).sub hφ.1.continuous)
  · rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact ((hu.integrableOn_isCompact (isCompact_closedBall 0 ρ)).norm.const_mul _)
  · intro n
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ Metric.closedBall (0 : Space) ρ
    · rw [Set.indicator_of_mem hy]
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
      have h1 := hC.dist_le_mul (axialRot (-s n) y) y
      rw [Real.dist_eq, dist_eq_norm] at h1
      have h2 := hchord (-s n) y
      rw [abs_neg] at h2
      have hyρ : ‖y‖ ≤ ρ := by simpa using hy
      have hsn : 0 < |s n| := abs_pos.2 (hs0 n)
      have h3 : |s n|⁻¹ * |φ (axialRot (-s n) y) - φ y| ≤ C * ρ := by
        rw [inv_mul_le_iff₀ hsn]
        calc |φ (axialRot (-s n) y) - φ y| ≤ C * ‖axialRot (-s n) y - y‖ := h1
          _ ≤ C * (|s n| * ‖y‖) := mul_le_mul_of_nonneg_left h2 C.2
          _ ≤ |s n| * (C * ρ) := by
            rw [mul_left_comm]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyρ C.2) hsn.le
      exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy]
      have hy' : axialRot (-s n) y ∉ Metric.closedBall (0 : Space) ρ := by
        simpa [hnorm] using hy
      simp [hF, hout y hy, hout _ hy']
  · refine Eventually.of_forall fun y => ?_
    have hfun : (fun ψ : ℝ => axialRot (-ψ) y) = fun ψ =>
        (Real.cos ψ * y 0 + Real.sin ψ * y 1) • unitVector 0
          + (-Real.sin ψ * y 0 + Real.cos ψ * y 1) • unitVector 1 + y 2 • unitVector 2 := by
      funext ψ
      simp only [axialRot, Real.cos_neg, Real.sin_neg]
      ring_nf
    have hD : HasDerivAt (fun ψ : ℝ => axialRot (-ψ) y)
        ((-Real.sin 0 * y 0 + Real.cos 0 * y 1) • unitVector 0
          + (-Real.cos 0 * y 0 + -Real.sin 0 * y 1) • unitVector 1 + (0 : ℝ) • unitVector 2) 0 := by
      rw [hfun]
      refine ((((Real.hasDerivAt_cos 0).mul_const (y 0)).add ((Real.hasDerivAt_sin 0).mul_const (y 1))).smul_const
        (unitVector 0)).add ?_ |>.add ?_
      · exact ((((Real.hasDerivAt_sin 0).neg.mul_const (y 0)).add ((Real.hasDerivAt_cos 0).mul_const (y 1))).smul_const
          (unitVector 1))
      · exact (hasDerivAt_const (0 : ℝ) (y 2)).smul_const (unitVector 2)
    have h0 : axialRot (-0) y = y := by rw [neg_zero, hRot.2.2.1]
    have hφd := ((hφ.1.differentiable (by simp)) (axialRot (-0 : ℝ) y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD
    rw [h0] at hφd
    have hval : fderiv ℝ φ y ((-Real.sin 0 * y 0 + Real.cos 0 * y 1) • unitVector 0
          + (-Real.cos 0 * y 0 + -Real.sin 0 * y 1) • unitVector 1 + (0 : ℝ) • unitVector 2) =
        -azimuthalDeriv φ y := by
      simp only [map_add, map_smul, azimuthalDeriv, azimuthalField, Fin.sum_univ_three]
      simp
      ring
    rw [hval] at hφd
    have hsn : Tendsto s atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hs, Eventually.of_forall fun n => hs0 n⟩
    have hsl := hφd.tendsto_slope_zero.comp hsn
    have hsl' : Tendsto (fun n => (s n)⁻¹ * (φ (axialRot (-s n) y) - φ y)) atTop (𝓝 (-azimuthalDeriv φ y)) := by
      refine hsl.congr fun n => ?_
      simp only [Function.comp_apply, zero_add, smul_eq_mul, h0]
    exact ((Complex.continuous_ofReal.tendsto _).comp hsl').mul_const (u y)

theorem angular_identity {β : Type*} [Fintype β] [DecidableEq β] (hRot : AxialRotationHolds)
    (w : Space → β → ℂ) (g : Space → β → Fin 3 → ℂ) (k : ℝ)
    (A : ℝ → β → β → ℂ) (B : β → β → ℂ)
    (hw : ∀ b, LocallyIntegrable (fun y => w y b)) (hg : ∀ b j, LocallyIntegrable (fun y => g y b j))
    (hweak : ∀ φ : Space → ℝ, IsTestFunction φ → ∀ b j,
      ∫ y, (φ y : ℂ) * g y b j = -∫ y, (fderiv ℝ φ y (unitVector j) : ℂ) * w y b)
    (hA0 : ∀ b c, A 0 b c = if b = c then 1 else 0)
    (hA : ∀ b c, HasDerivAt (fun ψ => A ψ b c) (B b c) 0)
    (s : ℕ → ℝ) (hs0 : ∀ n, s n ≠ 0) (hs : Tendsto s atTop (𝓝 0))
    (hrot : ∀ n, ∀ᵐ y, ∀ b, w (axialRot (s n) y) b =
      Complex.exp (((k * s n : ℝ) : ℂ) * Complex.I) * ∑ c, A (s n) b c * w y c) :
    ∀ᵐ y, ∀ b, ∑ j, g y b j * (azimuthalField y j : ℂ) = (k : ℂ) * Complex.I * w y b + ∑ c, B b c * w y c := by
  have hint : ∀ φ : Space → ℝ, IsTestFunction φ → ∀ b,
      ∫ y, (φ y : ℂ) * ∑ j, g y b j * (azimuthalField y j : ℂ) =
        ∫ y, (φ y : ℂ) * ((k : ℂ) * Complex.I * w y b + ∑ c, B b c * w y c) := by
    intro φ hφ b
    set I : β → ℂ := fun c => ∫ y, (φ y : ℂ) * w y c with hI
    have hcov : ∀ n, ∫ y, (φ (axialRot (-s n) y) : ℂ) * w y b =
        Complex.exp (((k * s n : ℝ) : ℂ) * Complex.I) * ∑ c, A (s n) b c * I c := by
      intro n
      rw [← rot_integral hRot (s n) (fun y => (φ (axialRot (-s n) y) : ℂ) * w y b)]
      simp only [rot_inv hRot]
      rw [integral_congr_ae ((hrot n).mono fun y hy => by rw [hy b])]
      simp only [Finset.mul_sum, hI]
      rw [integral_finsetSum _ fun c _ => ?_]
      · refine Finset.sum_congr rfl fun c _ => ?_
        rw [← integral_const_mul, ← integral_const_mul]
        congr 1
        funext y
        ring
      · have := (test_integrable φ hφ _ (hw c)).const_mul (Complex.exp (((k * s n : ℝ) : ℂ) * Complex.I) * A (s n) b c)
        refine this.congr (Eventually.of_forall fun y => ?_)
        simp only
        ring
    have hder : HasDerivAt (fun ψ : ℝ => Complex.exp (((k * ψ : ℝ) : ℂ) * Complex.I) * ∑ c, A ψ b c * I c)
        ((k : ℂ) * Complex.I * I b + ∑ c, B b c * I c) 0 := by
      have he : HasDerivAt (fun ψ : ℝ => (((k * ψ : ℝ) : ℂ) * Complex.I)) ((k : ℂ) * Complex.I) 0 := by
        have := (((hasDerivAt_id (0 : ℝ)).const_mul k).ofReal_comp).mul_const Complex.I
        simpa using this
      have hS : HasDerivAt (fun ψ : ℝ => ∑ c, A ψ b c * I c) (∑ c, B b c * I c) 0 :=
        HasDerivAt.fun_sum fun c _ => (hA b c).mul_const (I c)
      have := he.cexp.mul hS
      refine this.congr_deriv ?_
      simp [hA0]
    have hlim1 := slope_limit hRot φ hφ (fun y => w y b) (hw b) s hs0 hs
    have hlim2 : Tendsto (fun n => (s n)⁻¹ * ((∫ y, (φ (axialRot (-s n) y) : ℂ) * w y b) - I b))
        atTop (𝓝 ((k : ℂ) * Complex.I * I b + ∑ c, B b c * I c)) := by
      have h1 := hder.tendsto_slope_zero
      have hsn : Tendsto s atTop (𝓝[≠] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨hs, Eventually.of_forall fun n => hs0 n⟩
      have h2 := h1.comp hsn
      refine h2.congr fun n => ?_
      simp only [Function.comp_apply, zero_add, hcov n]
      rw [Complex.real_smul]
      congr 2
      simp [hA0]
    have heq := tendsto_nhds_unique hlim1 hlim2
    rw [weak_along φ hφ w g b (hw b) (hg b) (fun φ hφ j => hweak φ hφ b j), heq]
    have hi : ∀ c, Integrable (fun y => (φ y : ℂ) * w y c) := fun c => test_integrable φ hφ _ (hw c)
    simp only [mul_add, Finset.mul_sum]
    rw [integral_add, integral_finsetSum]
    · congr 1
      · rw [← integral_const_mul]
        congr 1
        funext y
        ring
      · refine Finset.sum_congr rfl fun c _ => ?_
        rw [← integral_const_mul]
        congr 1
        funext y
        ring
    · intro c _
      exact ((hi c).const_mul (B b c)).congr (Eventually.of_forall fun y => by simp only; ring)
    · exact ((hi b).const_mul ((k : ℂ) * Complex.I)).congr (Eventually.of_forall fun y => by simp only; ring)
    · refine integrable_finsetSum _ fun c _ => ?_
      exact ((hi c).const_mul (B b c)).congr (Eventually.of_forall fun y => by simp only; ring)
  have hX : Continuous (fun y => fun j => (azimuthalField y j : ℂ)) := by
    refine continuous_pi fun j => Complex.continuous_ofReal.comp ?_
    obtain ⟨L, hL, -⟩ := azimuthal_linear j
    simp only [hL]
    exact L.continuous
  refine ae_all_iff.2 fun b => ?_
  refine ae_eq_of_integral_contDiff_smul_eq ?_ ?_ fun φ hφ1 hφ2 => ?_
  · refine locallyIntegrable_finsetSum _ fun j _ => ?_
    exact (hg b j).mul_continuous ((continuous_apply j).comp hX)
  · refine ((hw b).continuous_mul continuous_const).add ?_
    exact locallyIntegrable_finsetSum _ fun c _ => (hw c).continuous_mul continuous_const
  · simp_rw [Complex.real_smul]
    exact hint φ ⟨hφ1, hφ2⟩ b

theorem vel_bound (x : Fin 3 → ℂ) :
    cnormSq (fun b => ∑ c, ((azimuthalField (unitVector c) b : ℝ) : ℂ) * x c) ≤ (1 : ℝ) ^ 2 * cnormSq x := by
  simp [cnormSq, Fin.sum_univ_three, azimuthalField, unitVector]
  nlinarith [sq_nonneg ‖x 2‖, sq_nonneg ‖x 0‖, sq_nonneg ‖x 1‖]

theorem cnormSq_add_le {β : Type*} [Fintype β] (x y : β → ℂ) :
    cnormSq (x + y) ≤ 2 * cnormSq x + 2 * cnormSq y := by
  simp only [cnormSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := norm_add_le (x b) (y b)
  have h0 := norm_nonneg (x b + y b)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖x b‖ - ‖y b‖), norm_nonneg (x b), norm_nonneg (y b)]

theorem grad_bound (x : Fin 3 × Fin 3 → ℂ) :
    cnormSq (fun b : Fin 3 × Fin 3 => ∑ c : Fin 3 × Fin 3,
      (((azimuthalField (unitVector c.1) b.1 : ℝ) : ℂ) * (if b.2 = c.2 then 1 else 0)
        + (if b.1 = c.1 then 1 else 0) * ((-azimuthalField (unitVector b.2) c.2 : ℝ) : ℂ)) * x c)
      ≤ (2 : ℝ) ^ 2 * cnormSq x := by
  have key : (fun b : Fin 3 × Fin 3 => ∑ c : Fin 3 × Fin 3,
      (((azimuthalField (unitVector c.1) b.1 : ℝ) : ℂ) * (if b.2 = c.2 then 1 else 0)
        + (if b.1 = c.1 then 1 else 0) * ((-azimuthalField (unitVector b.2) c.2 : ℝ) : ℂ)) * x c) =
      (fun b : Fin 3 × Fin 3 => ∑ a : Fin 3, ((azimuthalField (unitVector a) b.1 : ℝ) : ℂ) * x (a, b.2))
        + (fun b : Fin 3 × Fin 3 => ∑ c : Fin 3, ((-azimuthalField (unitVector b.2) c : ℝ) : ℂ) * x (b.1, c)) := by
    funext b
    obtain ⟨b1, b2⟩ := b
    fin_cases b1 <;> fin_cases b2 <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_three, azimuthalField, unitVector] <;> ring
  rw [key]
  have h1 : cnormSq (fun b : Fin 3 × Fin 3 => ∑ a : Fin 3,
      ((azimuthalField (unitVector a) b.1 : ℝ) : ℂ) * x (a, b.2)) ≤ cnormSq x := by
    have hn : ∀ i j, 0 ≤ ‖x (i, j)‖ ^ 2 := fun _ _ => sq_nonneg _
    simp [cnormSq, Fintype.sum_prod_type, Fin.sum_univ_three, azimuthalField, unitVector]
    linarith [hn 0 0, hn 0 1, hn 0 2, hn 1 0, hn 1 1, hn 1 2, hn 2 0, hn 2 1, hn 2 2]
  have h2 : cnormSq (fun b : Fin 3 × Fin 3 => ∑ c : Fin 3,
      ((-azimuthalField (unitVector b.2) c : ℝ) : ℂ) * x (b.1, c)) ≤ cnormSq x := by
    have hn : ∀ i j, 0 ≤ ‖x (i, j)‖ ^ 2 := fun _ _ => sq_nonneg _
    simp [cnormSq, Fintype.sum_prod_type, Fin.sum_univ_three, azimuthalField, unitVector]
    linarith [hn 0 0, hn 0 1, hn 0 2, hn 1 0, hn 1 1, hn 1 2, hn 2 0, hn 2 1, hn 2 2]
  have := cnormSq_add_le (fun b : Fin 3 × Fin 3 => ∑ a : Fin 3,
      ((azimuthalField (unitVector a) b.1 : ℝ) : ℂ) * x (a, b.2))
    (fun b : Fin 3 × Fin 3 => ∑ c : Fin 3, ((-azimuthalField (unitVector b.2) c : ℝ) : ℂ) * x (b.1, c))
  linarith

theorem hasDerivAt_axialRot_neg (y : Space) (i : Fin 3) :
    HasDerivAt (fun ψ => axialRot (-ψ) y i) (-azimuthalField y i) 0 := by
  have h := hasDerivAt_axialRot y i
  rw [← neg_zero] at h
  have := h.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  rw [mul_neg_one] at this
  exact this

theorem unit_apply (hRot : AxialRotationHolds) (a b : Fin 3) :
    axialRot 0 (unitVector a) b = if b = a then 1 else 0 := by
  rw [hRot.2.2.1]
  simp [unitVector]

end GainInternal

open GainInternal in
theorem modeAzimuthalGainHolds_proof_of (hRot : AxialRotationHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) : ModeAzimuthalGainHolds := by
  intro P Γ v G H g hv ι hk
  have hk' : (2 : ℝ) ≤ |(ι.2 : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hk
  obtain ⟨hD1, hD2, -⟩ := hDer Γ P v G H g hv ι
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsdef
  have hs0 : ∀ n, s n ≠ 0 := fun n => by positivity
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hR1 := Measure.ae_ae_of_ae_prod (ae_all_iff.2 (fun n => (hRotM Γ P v G H g hv ι (s n)).1))
  have hR2 := Measure.ae_ae_of_ae_prod (ae_all_iff.2 (fun n => (hRotM Γ P v G H g hv ι (s n)).2))
  have hslice : ∀ᵐ σ, ∀ᵐ y,
      ((|ι.2| : ℝ) - 1) ^ 2 / cylRadius y ^ 2 * cnormSq (modeVel ι v σ y)
          ≤ cnormSq (modeGrad ι G σ y) ∧
        ((|ι.2| : ℝ) - 2) ^ 2 / cylRadius y ^ 2 * cnormSq (modeGrad ι G σ y)
          ≤ cnormSq (modeSecondDeriv ι H σ y) := by
    filter_upwards [hD1, hD2, hR1, hR2] with σ h1 h2 h3 h4
    obtain ⟨hw1, hg1, hweak1⟩ := weak_components (fun y => modeVel ι v σ y)
      (fun y => modeGrad ι G σ y) h1.1 h1.2
    have hc2 := fun l => weak_components (fun y i => modeGrad ι G σ y (i, l))
      (fun y ij => modeSecondDeriv ι H σ y (ij.1, ij.2, l)) (h2 l).1 (h2 l).2
    have hid1 := angular_identity hRot (fun y => modeVel ι v σ y) (fun y b j => modeGrad ι G σ y (b, j))
      (ι.2 : ℝ) (fun ψ b c => ((axialRot ψ (unitVector c) b : ℝ) : ℂ))
      (fun b c => ((azimuthalField (unitVector c) b : ℝ) : ℂ)) hw1 (fun b j => hg1 b j)
      (fun φ hφ b j => hweak1 φ hφ b j)
      (fun b c => by simp only [unit_apply hRot]; split_ifs <;> simp)
      (fun b c => (hasDerivAt_axialRot (unitVector c) b).ofReal_comp) s hs0 hs
      (fun n => by
        filter_upwards [h3] with y hy b
        have := congrFun (hy n) b
        simpa [rotC] using this)
    have hid2 := angular_identity hRot (β := Fin 3 × Fin 3) (fun y => modeGrad ι G σ y)
      (fun y b j => modeSecondDeriv ι H σ y (b.1, j, b.2)) (ι.2 : ℝ)
      (fun ψ b c => ((axialRot ψ (unitVector c.1) b.1 : ℝ) : ℂ) * ((axialRot (-ψ) (unitVector b.2) c.2 : ℝ) : ℂ))
      (fun b c => ((azimuthalField (unitVector c.1) b.1 : ℝ) : ℂ) * (if b.2 = c.2 then 1 else 0)
        + (if b.1 = c.1 then 1 else 0) * ((-azimuthalField (unitVector b.2) c.2 : ℝ) : ℂ))
      (fun b => (hc2 b.2).1 b.1) (fun b j => (hc2 b.2).2.1 b.1 j)
      (fun φ hφ b j => (hc2 b.2).2.2 φ hφ b.1 j)
      (fun b c => by
        have e2 : axialRot (-0) (unitVector b.2) c.2 = if b.2 = c.2 then 1 else 0 := by
          rw [neg_zero, unit_apply hRot]; exact if_congr eq_comm rfl rfl
        rw [unit_apply hRot, e2]
        obtain ⟨b1, b2⟩ := b
        obtain ⟨c1, c2⟩ := c
        by_cases h1 : b1 = c1 <;> by_cases h2 : b2 = c2 <;> simp [h1, h2, Prod.ext_iff])
      (fun b c => by
        have d1 := (hasDerivAt_axialRot (unitVector c.1) b.1).ofReal_comp
        have d2 := (hasDerivAt_axialRot_neg (unitVector b.2) c.2).ofReal_comp
        have e1 : ((axialRot 0 (unitVector c.1) b.1 : ℝ) : ℂ) = if b.1 = c.1 then 1 else 0 := by
          rw [unit_apply hRot]; split_ifs <;> simp
        have e2 : ((axialRot (-0) (unitVector b.2) c.2 : ℝ) : ℂ) = if b.2 = c.2 then 1 else 0 := by
          rw [neg_zero, unit_apply hRot, if_congr eq_comm rfl rfl]; split_ifs <;> simp
        have := d1.mul d2
        rw [e1, e2] at this
        exact this)
      s hs0 hs
      (fun n => by
        filter_upwards [h4] with y hy b
        have := congrFun (hy n) b
        rw [this]
        simp only [rotCMat, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        ring)
    filter_upwards [hid1, hid2] with y hy1 hy2
    have habs : ((|ι.2| : ℝ)) = |(ι.2 : ℝ)| := rfl
    constructor
    · have := gain_of_identity (modeVel ι v σ y) (fun b j => modeGrad ι G σ y (b, j)) _
        (azimuthalField y) (cylRadius y) (ι.2 : ℝ) 1 (azimuthalField_sq y) zero_le_one
        (le_trans one_le_two hk') (vel_bound _) hy1
      rw [habs]
      simpa [cnormSq, Fintype.sum_prod_type] using this
    · have := gain_of_identity (β := Fin 3 × Fin 3) (modeGrad ι G σ y)
        (fun b j => modeSecondDeriv ι H σ y (b.1, j, b.2)) _
        (azimuthalField y) (cylRadius y) (ι.2 : ℝ) 2 (azimuthalField_sq y) zero_le_two
        hk' (grad_bound _) hy2
      rw [habs]
      refine this.trans (le_of_eq ?_)
      simp only [cnormSq, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_comm
  refine ae_of_ae_ae ?_ hslice
  have hcyl : Continuous (fun z : ℝ × Space => cylRadius z.2) := by
    unfold cylRadius
    fun_prop
  have hcn : ∀ {β : Type} [Fintype β], Continuous (cnormSq : (β → ℂ) → ℝ) := by
    intro β _
    unfold cnormSq
    fun_prop
  have hq : ∀ c : ℝ, AEStronglyMeasurable (fun z : ℝ × Space => c / cylRadius z.2 ^ 2) volume :=
    fun c => (measurable_const.div (hcyl.measurable.pow_const 2)).aestronglyMeasurable
  have mV := hcn.comp_aestronglyMeasurable (modeVel_aesm hRot ι v hv.measurable_velocity)
  have mG := hcn.comp_aestronglyMeasurable (modeGrad_aesm hRot ι G hv.measurable_gradient)
  have mH := hcn.comp_aestronglyMeasurable (modeSecondDeriv_aesm hRot ι H hv.measurable_secondDeriv)
  refine NullMeasurableSet.inter ?_ ?_
  · exact AEStronglyMeasurable.nullMeasurableSet_le ((hq _).mul mV) mG
  · exact AEStronglyMeasurable.nullMeasurableSet_le ((hq _).mul mG) mH

end Coercive

end Breakdown
