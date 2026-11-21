import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace Breakdown.Freq

namespace Internal.BilinRotate

def rotCc (R : Space ≃ₗᵢ[ℝ] Space) : CSpace →L[ℂ] CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => ∑ j : Fin 3, ((R (unitVector j) i : ℝ) : ℂ) * z j)
      map_add' := fun a b => by ext i; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by ext i; simp [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring) }

theorem rotCc_apply (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : rotCc R z = rotC R z := rfl

theorem ae_comp_symm (R : Space ≃ₗᵢ[ℝ] Space) {β : Type*} {f₁ f₂ : Space → β}
    (h : f₁ =ᵐ[volume] f₂) : (fun y => f₁ (R.symm y)) =ᵐ[volume] fun y => f₂ (R.symm y) :=
  R.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp h

theorem rotL2_ae (h3 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (g : L2C) :
    (rotL2 R g : Space → CSpace) =ᵐ[volume] fun ξ => rotC R (g (R.symm ξ)) :=
  h3 R.symm.toContinuousLinearEquiv (fun _ => rotC R) ‖rotC R‖ aestronglyMeasurable_const
    (fun _ => le_rfl) g

def rotRapid (R : Space ≃ₗᵢ[ℝ] Space) (f : 𝓢(Space, CSpace)) : 𝓢(Space, CSpace) :=
  SchwartzMap.postcompCLM (rotCc R)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ R.symm.toContinuousLinearEquiv f)

theorem rotRapid_apply (R : Space ≃ₗᵢ[ℝ] Space) (f : 𝓢(Space, CSpace)) (x : Space) :
    rotRapid R f x = rotC R (f (R.symm x)) := by
  simp [rotRapid, SchwartzMap.postcompCLM_apply, rotCc_apply]

theorem rotL2_toLp (h3 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (f : 𝓢(Space, CSpace)) :
    rotL2 R (f.toLp 2) = (rotRapid R f).toLp 2 := by
  apply Lp.ext
  filter_upwards [rotL2_ae h3 R (f.toLp 2), ae_comp_symm R (f.coeFn_toLp 2 volume),
    (rotRapid R f).coeFn_toLp 2 volume] with x h1 h2 h4
  rw [h1, h4, rotRapid_apply]
  rw [h2]

theorem freqTrInv_rotRapid (R : Space ≃ₗᵢ[ℝ] Space) (f : 𝓢(Space, CSpace)) :
    𝓕⁻ (rotRapid R f) = rotRapid R (𝓕⁻ f) := by
  refine SchwartzMap.ext fun x => ?_
  rw [rotRapid_apply, SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  have hg : Integrable (fun v : Space => 𝐞 (inner ℝ v x) • f (R.symm v)) volume := by
    have hi : Integrable (fun v : Space => f (R.symm v)) volume :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ R.symm.toContinuousLinearEquiv f).integrable
    refine hi.mono ?_ (ae_of_all _ fun v => ?_)
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        (f.continuous.comp R.symm.continuous)).aestronglyMeasurable
    · simp [Circle.smul_def, norm_smul, Circle.norm_coe]
  have key : (fun v : Space => 𝐞 (inner ℝ v x) • rotRapid R f v) =
      fun v => rotCc R (𝐞 (inner ℝ v x) • f (R.symm v)) := by
    funext v
    rw [rotRapid_apply, ← rotCc_apply]
    simp only [Circle.smul_def, map_smul]
  have h5 : ∫ v : Space, 𝐞 (inner ℝ v x) • f (R.symm v) = 𝓕⁻ ((⇑f) ∘ R.symm) x :=
    (Real.fourierInv_eq _ _).symm
  rw [key, (rotCc R).integral_comp_comm hg, rotCc_apply, h5, Real.fourierInv_comp_linearIsometry]

theorem freqTrInv_rotL2 (h3 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (g : L2C) :
    freqTrL2.symm (rotL2 R g) = rotL2 R (freqTrL2.symm g) := by
  have hd := SchwartzMap.denseRange_toLpCLM (F := CSpace) (E := Space) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top
  have := hd.equalizer (g := fun g => freqTrL2.symm (rotL2 R g))
    (h := fun g => rotL2 R (freqTrL2.symm g))
    (freqTrL2.symm.continuous.comp (rotL2 R).continuous)
    ((rotL2 R).continuous.comp freqTrL2.symm.continuous) ?_
  · exact congrFun this g
  funext f
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply]
  rw [rotL2_toLp h3]
  change 𝓕⁻ ((rotRapid R f).toLp 2) = rotL2 R (𝓕⁻ (f.toLp 2))
  rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourierInv_eq, rotL2_toLp h3,
    freqTrInv_rotRapid]

theorem apply_coord (R : Space ≃ₗᵢ[ℝ] Space) (y : Space) (i : Fin 3) :
    R y i = ∑ j : Fin 3, R (unitVector j) i * y j := by
  have hy : y = ∑ j : Fin 3, y j • unitVector j := by
    ext i
    simp [unitVector, Pi.single_apply]
  conv_lhs => rw [hy]
  simp [map_sum, map_smul, mul_comm]

theorem realVec_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) :
    realVec (rotC R z) = R (realVec z) := by
  ext i
  rw [apply_coord]
  simp [realVec, rotC, Complex.re_sum]

theorem realPart_ae (h : L2C) : (realPart h : Space → Space) =ᵐ[volume] fun y => realVec (h y) :=
  ContinuousLinearMap.coeFn_compLpL realVec h

theorem toPhys_rotL2 (h3 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (g : L2C) :
    (toPhys (rotL2 R g) : Space → Space) =ᵐ[volume] pushForward R (toPhys g : Space → Space) := by
  have e1 : toPhys (rotL2 R g) = realPart (rotL2 R (freqTrL2.symm g)) := by
    rw [← freqTrInv_rotL2 h3]; rfl
  have e2 : toPhys g = realPart (freqTrL2.symm g) := rfl
  rw [e1, e2]
  filter_upwards [realPart_ae (rotL2 R (freqTrL2.symm g)), rotL2_ae h3 R (freqTrL2.symm g),
    ae_comp_symm R (realPart_ae (freqTrL2.symm g))] with y h1 h2 h4
  simp only [pushForward]
  rw [h1, h2, h4, realVec_rotC]

theorem fieldOp_id_ae (h3 : FieldOpRealized) (F : Space → CSpace →L[ℝ] CSpace) (C : ℝ)
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C) (g : L2C) :
    (fieldOp id F g : Space → CSpace) =ᵐ[volume] fun ξ => F ξ (g ξ) :=
  h3 (ContinuousLinearEquiv.refl ℝ Space) F C hF hC g

theorem cmul_apply (c : ℂ) (w : CSpace) : cmul c w = c • w := rfl

theorem cmul_eq (c : ℂ) : cmul c = c • ((ContinuousLinearMap.id ℂ CSpace).restrictScalars ℝ) := by
  ext w : 1
  rfl

theorem derivSymbol_norm_le (j : Fin 3) (ξ : Space) : ‖derivSymbol j ξ‖ ≤ 1 := by
  rw [derivSymbol, norm_div, norm_mul]
  simp only [Complex.norm_I, one_mul, Complex.norm_real, norm_norm]
  exact div_le_one_of_le₀ (PiLp.norm_apply_le ξ j) (norm_nonneg _)

theorem deriv_meas (j : Fin 3) :
    AEStronglyMeasurable (fun ξ : Space => cmul (derivSymbol j ξ)) volume := by
  simp_rw [cmul_eq]
  refine (Measurable.smul_const ?_ _).aestronglyMeasurable
  unfold derivSymbol
  fun_prop

theorem deriv_bound (j : Fin 3) (ξ : Space) : ‖cmul (derivSymbol j ξ)‖ ≤ 1 := by
  rw [cmul_eq]
  refine (norm_smul_le _ _).trans ?_
  calc ‖derivSymbol j ξ‖ * ‖(ContinuousLinearMap.id ℂ CSpace).restrictScalars ℝ‖
      ≤ 1 * 1 := by
        gcongr
        · exact derivSymbol_norm_le j ξ
        · rw [ContinuousLinearMap.norm_restrictScalars]
          exact ContinuousLinearMap.norm_id_le
    _ = 1 := one_mul 1

theorem scaled_exp_le (a r : ℝ) (ha : 0 < a) :
    r * Real.exp (-(a * r ^ 2)) ≤ 1 + a⁻¹ := by
  have he : 1 + a * r ^ 2 ≤ Real.exp (a * r ^ 2) := by
    linarith [Real.add_one_le_exp (a * r ^ 2)]
  have h1 : r ≤ (1 + a⁻¹) * (1 + a * r ^ 2) := by
    have e : (1 + a⁻¹) * (1 + a * r ^ 2) = 1 + a * r ^ 2 + a⁻¹ + r ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith [sq_nonneg (r - 1), inv_pos.2 ha, mul_pos ha ha, sq_nonneg r]
  have hkey : r ≤ (1 + a⁻¹) * Real.exp (a * r ^ 2) :=
    h1.trans (by gcongr)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact hkey

theorem phiFactor_le (τ : ℝ) (hτ : 0 < τ) (ξ : Space) :
    |phiFactor τ ξ| ≤ 2 * π * (1 + (4 * π ^ 2 * τ)⁻¹) := by
  have hpos : 0 ≤ phiFactor τ ξ := by unfold phiFactor; positivity
  rw [abs_of_nonneg hpos, phiFactor]
  have ha : 0 < 4 * π ^ 2 * τ := by positivity
  have := scaled_exp_le (4 * π ^ 2 * τ) ‖ξ‖ ha
  calc 2 * π * ‖ξ‖ * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2))
      = 2 * π * (‖ξ‖ * Real.exp (-(4 * π ^ 2 * τ * ‖ξ‖ ^ 2))) := by ring
    _ ≤ 2 * π * (1 + (4 * π ^ 2 * τ)⁻¹) := by gcongr

theorem phi_meas (τ : ℝ) :
    AEStronglyMeasurable (fun ξ : Space => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) volume := by
  refine (Measurable.smul_const ?_ _).aestronglyMeasurable
  unfold phiFactor
  fun_prop

theorem phi_bound (τ : ℝ) (hτ : 0 < τ) (ξ : Space) :
    ‖phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 2 * π * (1 + (4 * π ^ 2 * τ)⁻¹) := by
  refine (norm_smul_le _ _).trans ?_
  calc ‖phiFactor τ ξ‖ * ‖ContinuousLinearMap.id ℝ CSpace‖
      ≤ (2 * π * (1 + (4 * π ^ 2 * τ)⁻¹)) * 1 := by
        gcongr
        · exact phiFactor_le τ hτ ξ
        · exact ContinuousLinearMap.norm_id_le
    _ = _ := mul_one _

theorem phiOp_rot (h3 : FieldOpRealized) (τ : ℝ) (hτ : 0 < τ) (R : Space ≃ₗᵢ[ℝ] Space) (g : L2C) :
    fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) (rotL2 R g) =
      rotL2 R (fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) g) := by
  apply Lp.ext
  filter_upwards [fieldOp_id_ae h3 _ _ (phi_meas τ) (phi_bound τ hτ) (rotL2 R g), rotL2_ae h3 R g,
    rotL2_ae h3 R (fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) g),
    ae_comp_symm R (fieldOp_id_ae h3 _ _ (phi_meas τ) (phi_bound τ hτ) g)] with ξ h1 h2 h4 h5
  rw [h1, h4, h2, h5]
  simp [phiFactor, map_smul]

theorem coeFn_sum3 {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (f : Fin 3 → Lp (α := Space) E p) :
    ((∑ l, f l : Lp (α := Space) E p) : Space → E) =ᵐ[volume] fun x => ∑ l, (f l : Space → E) x := by
  simp only [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (f 0 + f 1) (f 2), Lp.coeFn_add (f 0) (f 1)] with x h1 h2
  rw [h1, Pi.add_apply, h2, Pi.add_apply]

theorem deriv_pt (R : Space ≃ₗᵢ[ℝ] Space) (ξ : Space) (z : CSpace) (j : Fin 3) :
    cmul (derivSymbol j ξ) (rotC R z) =
      ∑ l : Fin 3, R (unitVector l) j • rotC R (cmul (derivSymbol l (R.symm ξ)) z) := by
  simp only [cmul_apply, ← rotCc_apply, map_smul]
  have hξ : ((ξ j : ℝ) : ℂ) =
      ∑ l : Fin 3, ((R (unitVector l) j : ℝ) : ℂ) * ((R.symm ξ l : ℝ) : ℂ) := by
    have := apply_coord R (R.symm ξ) j
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    rw [this]
    push_cast
    rfl
  have hs : ∀ (r : ℝ) (y : CSpace), r • y = (r : ℂ) • y := fun _ _ => PiLp.ext fun _ => rfl
  simp_rw [hs, smul_smul, ← Finset.sum_smul]
  congr 1
  simp only [derivSymbol, LinearIsometryEquiv.norm_map, hξ, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem derivOp_rot (h3 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (g : L2C) (j : Fin 3) :
    fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (rotL2 R g) =
      ∑ l : Fin 3, R (unitVector l) j • rotL2 R (fieldOp id (fun ξ => cmul (derivSymbol l ξ)) g) := by
  apply Lp.ext
  filter_upwards [fieldOp_id_ae h3 _ 1 (deriv_meas j) (deriv_bound j) (rotL2 R g), rotL2_ae h3 R g,
    ae_all_iff.2 fun l => rotL2_ae h3 R (fieldOp id (fun ξ => cmul (derivSymbol l ξ)) g),
    ae_all_iff.2 fun l => ae_comp_symm R (fieldOp_id_ae h3 _ 1 (deriv_meas l) (deriv_bound l) g),
    coeFn_sum3 (fun l => R (unitVector l) j • rotL2 R (fieldOp id (fun ξ => cmul (derivSymbol l ξ)) g)),
    ae_all_iff.2 fun l => Lp.coeFn_smul (R (unitVector l) j)
      (rotL2 R (fieldOp id (fun ξ => cmul (derivSymbol l ξ)) g))] with ξ h1 h2 h4 h5 h6 h7
  rw [h1, h2, h6, deriv_pt]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h7 l, Pi.smul_apply, h4 l, h5 l]

theorem partialX_rot (h2 : RotationAlgebra) (h3 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space)
    (v : X) (j : Fin 3) :
    (partialX j (rotX R v) : Space → Space) =ᵐ[volume]
      fun y => ∑ l : Fin 3, R (unitVector l) j • R ((partialX l v : Space → Space) (R.symm y)) := by
  have e : partialX j (rotX R v) = ∑ l : Fin 3, R (unitVector l) j •
      toPhys (rotL2 R (fieldOp id (fun ξ => cmul (derivSymbol l ξ)) (v : L2C))) := by
    have e0 : partialX j (rotX R v) =
        toPhys (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (rotL2 R v)) := by
      simp only [partialX, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, (h2 R).1 v]
    rw [e0, derivOp_rot h3, map_sum]
    simp only [map_smul]
  rw [e]
  filter_upwards [coeFn_sum3 (fun l => R (unitVector l) j •
      toPhys (rotL2 R (fieldOp id (fun ξ => cmul (derivSymbol l ξ)) (v : L2C)))),
    ae_all_iff.2 fun l => Lp.coeFn_smul (R (unitVector l) j)
      (toPhys (rotL2 R (fieldOp id (fun ξ => cmul (derivSymbol l ξ)) (v : L2C)))),
    ae_all_iff.2 fun l => toPhys_rotL2 h3 R (fieldOp id (fun ξ => cmul (derivSymbol l ξ)) (v : L2C))]
    with y h1 h4 h5
  rw [h1]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h4 l, Pi.smul_apply, h5 l]
  rfl

theorem phiX_rot (h2 : RotationAlgebra) (h3 : FieldOpRealized) (τ : ℝ) (hτ : 0 < τ)
    (R : Space ≃ₗᵢ[ℝ] Space) (ψ : X) :
    (phiX τ (rotX R ψ) : Space → Space) =ᵐ[volume] pushForward R (phiX τ ψ : Space → Space) := by
  have e : phiX τ (rotX R ψ) = toPhys (rotL2 R
      (fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C))) := by
    rw [← phiOp_rot h3 τ hτ R]
    simp only [phiX, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, (h2 R).1 ψ]
  rw [e]
  exact toPhys_rotL2 h3 R _

theorem inner_unit_sum (R : Space ≃ₗᵢ[ℝ] Space) (a : Space) (l : Fin 3) :
    ∑ j : Fin 3, R a j * R (unitVector l) j = a l := by
  have e2 : inner ℝ a (unitVector l) = a l := by
    simp [unitVector, EuclideanSpace.inner_single_right]
  have e3 : inner ℝ (R a) (R (unitVector l)) = ∑ j : Fin 3, R a j * R (unitVector l) j := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  rw [← e3, R.inner_map_map, e2]

theorem integrand_pt (R : Space ≃ₗᵢ[ℝ] Space) (a c : Space) (b : Fin 3 → Space) :
    ∑ j : Fin 3, R a j * inner ℝ (∑ l : Fin 3, R (unitVector l) j • R (b l)) (R c) =
      ∑ j : Fin 3, a j * inner ℝ (b j) c := by
  simp only [sum_inner, real_inner_smul_left, LinearIsometryEquiv.inner_map_map, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, inner_unit_sum]

theorem trilinear_rot (h2 : RotationAlgebra) (h3 : FieldOpRealized) (h4 : VelocityRotate)
    (R : Space ≃ₗᵢ[ℝ] Space) (u v : X) (w : Space → Space) :
    trilinear (rotX R u) (rotX R v) (pushForward R w) = trilinear u v w := by
  unfold trilinear
  have hae : (fun y => ∑ j : Fin 3, (velocity (rotX R u) : Space → Space) y j *
      inner ℝ ((partialX j (rotX R v) : Space → Space) y) (pushForward R w y)) =ᵐ[volume]
      fun y => (fun x => ∑ j : Fin 3, (velocity u : Space → Space) x j *
        inner ℝ ((partialX j v : Space → Space) x) (w x)) (R.symm y) := by
    filter_upwards [h4 R u, ae_all_iff.2 fun j => partialX_rot h2 h3 R v j] with y hu hv
    simp only [hu, hv, pushForward]
    exact integrand_pt R ((velocity u : Space → Space) (R.symm y)) (w (R.symm y))
      (fun l => (partialX l v : Space → Space) (R.symm y))
  refine (integral_congr_ae hae).trans ?_
  exact (LinearIsometryEquiv.measurePreserving R.symm).integral_comp
    R.symm.toHomeomorph.measurableEmbedding (fun x => ∑ j : Fin 3, (velocity u : Space → Space) x j *
        inner ℝ ((partialX j v : Space → Space) x) (w x))

theorem trilinear_congr (u v : X) {w w' : Space → Space} (h : w =ᵐ[volume] w') :
    trilinear u v w = trilinear u v w' := by
  unfold trilinear
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem bilinForm_rot (h2 : RotationAlgebra) (h3 : FieldOpRealized) (h4 : VelocityRotate)
    (τ : ℝ) (hτ : 0 < τ) (R : Space ≃ₗᵢ[ℝ] Space) (u v ψ : X) :
    bilinForm τ (rotX R u) (rotX R v) (rotX R ψ) = bilinForm τ u v ψ := by
  unfold bilinForm
  rw [trilinear_congr _ _ (phiX_rot h2 h3 τ hτ R ψ), trilinear_congr _ _ (phiX_rot h2 h3 τ hτ R ψ),
    trilinear_rot h2 h3 h4, trilinear_rot h2 h3 h4]

end Internal.BilinRotate

open Internal.BilinRotate in
theorem bilinRotate (h1 : BilinExists) (h2 : RotationAlgebra) (h3 : FieldOpRealized)
    (h4 : VelocityRotate) (_h5 : TrilinearBound) : BilinRotate := by
  intro R τ u v
  by_cases hτ : 0 < τ
  · have hB : ∃ B, BilinSpec τ B := h1 τ hτ
    have hs : BilinSpec τ (bilinX τ) := by
      have h : 0 < τ ∧ ∃ B, BilinSpec τ B := ⟨hτ, hB⟩
      have e : bilinX τ = h.2.choose := dif_pos h
      rw [e]
      exact h.2.choose_spec
    refine ext_inner_right ℝ fun ψ => ?_
    obtain ⟨φ, rfl⟩ : ∃ φ, rotX R φ = ψ := ⟨(rotX R).symm ψ, (rotX R).apply_symm_apply ψ⟩
    rw [LinearIsometryEquiv.inner_map_map, hs, hs, bilinForm_rot h2 h3 h4 τ hτ]
  · have h0 : bilinX τ = 0 := by
      exact dif_neg (fun h => hτ h.1)
    simp [h0]

end Breakdown.Freq
