import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace Breakdown.FarField

open Freq

namespace Internal.TranslationCovariance

def phase (h ξ : Space) : ℂ := Complex.exp (-(((2 * π * inner ℝ h ξ : ℝ)) : ℂ) * Complex.I)

def modL2 (h : Space) : L2C →L[ℝ] L2C := fieldOp id (fun ξ => cmul (phase h ξ))

theorem shiftX_eq (h : Space) : shiftX h = restrictX (modL2 h) := rfl

theorem norm_phase (h ξ : Space) : ‖phase h ξ‖ = 1 := by
  rw [phase, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

theorem continuous_phase (h : Space) : Continuous (phase h) := by
  unfold phase
  fun_prop

theorem phase_mul_neg (h ξ : Space) : phase h ξ * phase (-h) ξ = 1 := by
  rw [phase, phase, ← Complex.exp_add, inner_neg_left]
  convert Complex.exp_zero using 2
  push_cast
  ring

theorem conj_phase_neg (h ξ : Space) : (starRingEnd ℂ) (phase h (-ξ)) = phase h ξ := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  simp only [inner_neg_right, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem meas_phase (h : Space) : AEStronglyMeasurable (fun ξ : Space => cmul (phase h ξ)) volume := by
  simp_rw [Breakdown.Freq.Internal.EmbedRot.cmul_eq]
  exact ((continuous_phase h).smul continuous_const).aestronglyMeasurable

theorem bound_phase (h ξ : Space) : ‖cmul (phase h ξ)‖ ≤ 1 :=
  Breakdown.Freq.Internal.EmbedRot.norm_cmul_le _ (norm_phase h ξ).le

theorem modL2_ae (h : Space) (g : L2C) :
    (modL2 h g : Space → CSpace) =ᵐ[volume] fun ξ => phase h ξ • g ξ :=
  Breakdown.Freq.Internal.BilinRotate.fieldOp_id_ae fieldOpRealized_holds
    (fun ξ => cmul (phase h ξ)) 1 (meas_phase h) (bound_phase h) g

theorem fieldOp_modL2 (h : Space) (F : Space → CSpace →L[ℝ] CSpace) (C : ℝ)
    (hF : AEStronglyMeasurable F volume) (hC : ∀ ξ, ‖F ξ‖ ≤ C)
    (hlin : ∀ ξ (c : ℂ) (z : CSpace), F ξ (c • z) = c • F ξ z) (g : L2C) :
    fieldOp id F (modL2 h g) = modL2 h (fieldOp id F g) := by
  apply Lp.ext
  filter_upwards [Breakdown.Freq.Internal.BilinRotate.fieldOp_id_ae fieldOpRealized_holds F C hF hC
      (modL2 h g), modL2_ae h g, modL2_ae h (fieldOp id F g),
    Breakdown.Freq.Internal.BilinRotate.fieldOp_id_ae fieldOpRealized_holds F C hF hC g]
    with ξ e1 e2 e3 e4
  rw [e1, e2, e3, e4, hlin]

theorem cmul_smul_comm (d c : ℂ) (z : CSpace) : cmul d (c • z) = c • cmul d z := by
  show d • (c • z) = c • (d • z)
  exact smul_comm _ _ _

theorem conjVec_smul (c : ℂ) (z : CSpace) : conjVec (c • z) = (starRingEnd ℂ) c • conjVec z := by
  ext i
  simp [conjVec]

theorem longitudinal_smul_comm (ξ : Space) (c : ℂ) (z : CSpace) :
    longitudinal ξ (c • z) = c • longitudinal ξ z := by
  rw [Breakdown.Freq.Internal.H1Consistency.longitudinal_apply,
    Breakdown.Freq.Internal.H1Consistency.longitudinal_apply, inner_smul_right, mul_smul]
  exact smul_comm _ _ _

theorem ae_comp_neg {β : Type*} {u v : Space → β} (hu : u =ᵐ[volume] v) :
    (fun ξ => u (-ξ)) =ᵐ[volume] fun ξ => v (-ξ) :=
  (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp hu

theorem modL2_mem_sig (h : Space) {x : L2C} (hx : x ∈ Sig) : modL2 h x ∈ Sig := by
  rw [Breakdown.Freq.Internal.H1Consistency.mem_sig_iff] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  constructor
  · apply Lp.ext
    have hsr := Breakdown.Freq.Internal.H1Consistency.reflConj_ae fieldOpRealized_holds x
    rw [h1] at hsr
    filter_upwards [Breakdown.Freq.Internal.H1Consistency.reflConj_ae fieldOpRealized_holds (modL2 h x),
      ae_comp_neg (modL2_ae h x), modL2_ae h x, hsr] with ξ e1 e2 e3 e4
    rw [e1, e2, e3, conjVec_smul, conj_phase_neg, ← e4]
  · rw [fieldOp_modL2 h longitudinal 1 Breakdown.Freq.Internal.H1Consistency.aesm_longitudinal
      Breakdown.Freq.Internal.H1Consistency.norm_longitudinal_le longitudinal_smul_comm, h2, map_zero]

theorem shiftX_coe (h : Space) (x : X) : (shiftX h x : L2C) = modL2 h x := by
  rw [shiftX_eq]
  unfold restrictX
  rw [dif_pos (fun y hy => modL2_mem_sig h hy)]
  rfl

theorem norm_modL2 (h : Space) (g : L2C) : ‖modL2 h g‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [modL2_ae h g] with ξ hξ
  rw [hξ, norm_smul, norm_phase, one_mul]

theorem norm_shiftX (h : Space) (x : X) : ‖shiftX h x‖ = ‖x‖ := by
  show ‖(shiftX h x : L2C)‖ = ‖(x : L2C)‖
  rw [shiftX_coe]
  exact norm_modL2 h x

theorem shiftX_shiftX_neg (h : Space) (x : X) : shiftX h (shiftX (-h) x) = x := by
  apply Subtype.ext
  rw [shiftX_coe, shiftX_coe]
  apply Lp.ext
  filter_upwards [modL2_ae h (modL2 (-h) x), modL2_ae (-h) x] with ξ e1 e2
  rw [e1, e2, smul_smul, phase_mul_neg, one_smul]

theorem inner_shiftX (h : Space) (x y : X) :
    inner ℝ (shiftX h x) y = inner ℝ x (shiftX (-h) y) := by
  let L : X →ₗᵢ[ℝ] X := { toLinearMap := (shiftX h : X →ₗ[ℝ] X), norm_map' := norm_shiftX h }
  calc inner ℝ (shiftX h x) y = inner ℝ (shiftX h x) (shiftX h (shiftX (-h) y)) := by
        rw [shiftX_shiftX_neg]
    _ = inner ℝ x (shiftX (-h) y) := L.inner_map_map x (shiftX (-h) y)

theorem ae_comp_sub (h : Space) {β : Type*} {u v : Space → β} (huv : u =ᵐ[volume] v) :
    (fun y => u (y - h)) =ᵐ[volume] fun y => v (y - h) :=
  (measurePreserving_sub_right (volume : Measure Space) h).quasiMeasurePreserving.ae_eq_comp huv

def transL2 (h : Space) : L2C →ₗᵢ[ℝ] L2C :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun y : Space => y - h) (measurePreserving_sub_right (volume : Measure Space) h)

theorem transL2_ae (h : Space) (k : L2C) :
    (transL2 h k : Space → CSpace) =ᵐ[volume] fun y => k (y - h) :=
  Lp.coeFn_compMeasurePreserving k _

theorem fourier_translate (h : Space) (f : Space → CSpace) (ξ : Space) :
    𝓕 (fun x => f (x - h)) ξ = phase h ξ • 𝓕 f ξ := by
  rw [Real.fourier_eq', Real.fourier_eq']
  set G : Space → CSpace := fun u =>
    Complex.exp (↑(-2 * π * inner ℝ (u + h) ξ) * Complex.I) • f u with hG
  have key : (fun v : Space => Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) • f (v - h)) =
      fun v => G (v - h) := by
    funext v
    simp only [hG, sub_add_cancel]
  rw [key, integral_sub_right_eq_self G h, ← integral_smul]
  congr 1
  funext u
  simp only [hG]
  rw [smul_smul]
  congr 1
  rw [phase, ← Complex.exp_add, inner_add_left]
  congr 1
  push_cast
  ring

theorem transL2_toLp (h : Space) (f : 𝓢(Space, CSpace)) :
    transL2 h (f.toLp 2) = (f.compSubConstCLM ℝ h).toLp 2 := by
  apply Lp.ext
  filter_upwards [transL2_ae h (f.toLp 2), ae_comp_sub h (f.coeFn_toLp 2 volume),
    (f.compSubConstCLM ℝ h).coeFn_toLp 2 volume] with y e1 e2 e3
  rw [e1, e3, e2, SchwartzMap.compSubConstCLM_apply]

theorem fourierL2_toLp (f : 𝓢(Space, CSpace)) : freqTrL2 (f.toLp 2) = (𝓕 f).toLp 2 :=
  SchwartzMap.toLp_fourier_eq f

theorem fourier_transL2 (h : Space) (g : L2C) : freqTrL2 (transL2 h g) = modL2 h (freqTrL2 g) := by
  have hd := SchwartzMap.denseRange_toLpCLM (F := CSpace) (E := Space) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top
  have := hd.equalizer (g := fun g => freqTrL2 (transL2 h g))
    (h := fun g => modL2 h (freqTrL2 g))
    (freqTrL2.continuous.comp (transL2 h).continuous)
    ((modL2 h).continuous.comp freqTrL2.continuous) ?_
  · exact congrFun this g
  funext f
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply]
  rw [transL2_toLp, fourierL2_toLp, fourierL2_toLp]
  apply Lp.ext
  filter_upwards [(𝓕 (f.compSubConstCLM ℝ h)).coeFn_toLp 2 volume, modL2_ae h ((𝓕 f).toLp 2),
    (𝓕 f).coeFn_toLp 2 volume] with ξ e1 e2 e3
  rw [e1, e2, e3, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  exact fourier_translate h f ξ

theorem fourierInv_modL2 (h : Space) (g : L2C) :
    freqTrL2.symm (modL2 h g) = transL2 h (freqTrL2.symm g) := by
  have := fourier_transL2 h (freqTrL2.symm g)
  rw [LinearIsometryEquiv.apply_symm_apply] at this
  rw [← this, LinearIsometryEquiv.symm_apply_apply]

theorem toPhys_modL2 (h : Space) (g : L2C) :
    (toPhys (modL2 h g) : Space → Space) =ᵐ[volume] fun y => (toPhys g : Space → Space) (y - h) := by
  have e1 : toPhys (modL2 h g) = realPart (transL2 h (freqTrL2.symm g)) := by
    rw [← fourierInv_modL2]
    rfl
  have e2 : toPhys g = realPart (freqTrL2.symm g) := rfl
  rw [e1, e2]
  filter_upwards [Breakdown.Freq.Internal.BilinRotate.realPart_ae (transL2 h (freqTrL2.symm g)),
    transL2_ae h (freqTrL2.symm g),
    ae_comp_sub h (Breakdown.Freq.Internal.BilinRotate.realPart_ae (freqTrL2.symm g))] with y e3 e4 e5
  rw [e3, e4, e5]

theorem partialX_shift (h : Space) (j : Fin 3) (v : X) :
    (partialX j (shiftX h v) : Space → Space) =ᵐ[volume]
      fun y => (partialX j v : Space → Space) (y - h) := by
  have e : partialX j (shiftX h v) =
      toPhys (modL2 h (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (v : L2C))) := by
    simp only [partialX, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [shiftX_coe, fieldOp_modL2 h _ 1 (Breakdown.Freq.Internal.BilinRotate.deriv_meas j)
      (Breakdown.Freq.Internal.BilinRotate.deriv_bound j) (fun ξ c z => cmul_smul_comm _ c z)]
  have e2 : partialX j v = toPhys (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (v : L2C)) := by
    simp only [partialX, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [e, e2]
  exact toPhys_modL2 h _

theorem phiX_shift (τ : ℝ) (hτ : 0 < τ) (h : Space) (ψ : X) :
    (phiX τ (shiftX h ψ) : Space → Space) =ᵐ[volume]
      fun y => (phiX τ ψ : Space → Space) (y - h) := by
  have e : phiX τ (shiftX h ψ) = toPhys (modL2 h
      (fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C))) := by
    simp only [phiX, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [shiftX_coe, fieldOp_modL2 h _ _ (Breakdown.Freq.Internal.BilinRotate.phi_meas τ)
      (Breakdown.Freq.Internal.BilinRotate.phi_bound τ hτ) (fun ξ c z => by
        show phiFactor τ ξ • (c • z) = c • (phiFactor τ ξ • z)
        exact smul_comm _ _ _)]
  have e2 : phiX τ ψ =
      toPhys (fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C)) := by
    simp only [phiX, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [e, e2]
  exact toPhys_modL2 h _

theorem test_translate (h : Space) {φ : Space → Space} (hφ : IsTestField φ) :
    IsTestField (fun y => φ (y - h)) := by
  obtain ⟨hs, hc, hd⟩ := hφ
  refine ⟨hs.comp (contDiff_id.sub contDiff_const), ?_, fun y => ?_⟩
  · exact hc.comp_homeomorph (Homeomorph.subRight h)
  · unfold divergenceAt
    rw [fderiv_comp_sub]
    exact hd (y - h)

theorem partialField_translate (h : Space) (φ : Space → Space) (k : Fin 3) :
    partialField (fun y => φ (y - h)) k = fun y => partialField φ k (y - h) := by
  funext y
  unfold partialField
  rw [fderiv_comp_sub]

theorem complexify_translate (h : Space) {g : Space → Space} (hg : MemLp g 2 volume) :
    complexify (toLpOrZero 2 (fun y => g (y - h))) = transL2 h (complexify (toLpOrZero 2 g)) := by
  apply Lp.ext
  filter_upwards [Breakdown.Freq.Internal.EmbedRot.ae_complexify (fun y => g (y - h))
      (hg.comp_measurePreserving (measurePreserving_sub_right (volume : Measure Space) h)),
    transL2_ae h (complexify (toLpOrZero 2 g)),
    ae_comp_sub h (Breakdown.Freq.Internal.EmbedRot.ae_complexify g hg)] with y e1 e2 e3
  rw [e1, e2, e3]

theorem ofGrad_translate (h : Space) {φ : Space → Space} (hφ : IsTestField φ) :
    ofGrad (fun y => φ (y - h)) = modL2 h (ofGrad φ) := by
  unfold ofGrad
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hm : MemLp (partialField φ k) 2 volume :=
    Breakdown.Freq.Internal.EmbedRot.memLp_dir φ
      (Breakdown.Freq.Internal.VelocityRotate.decay_of_test hφ) (unitVector k)
  have hf : freqTrR (transL2 h (complexify (toLpOrZero 2 (partialField φ k)))) =
      modL2 h (freqTrR (complexify (toLpOrZero 2 (partialField φ k)))) :=
    fourier_transL2 h _
  rw [partialField_translate, complexify_translate h hm, hf,
    fieldOp_modL2 h _ 1 ?_ (fun ξ => Breakdown.Freq.Internal.EmbedRot.norm_cmul_le _
      (Breakdown.Freq.Internal.EmbedRot.norm_gradSymbol_le k ξ)) (fun ξ c z => cmul_smul_comm _ c z)]
  simp_rw [Breakdown.Freq.Internal.EmbedRot.cmul_eq]
  exact (continuous_id.smul continuous_const).comp_aestronglyMeasurable
    (Breakdown.Freq.Internal.EmbedRot.measurable_gradSymbol k).aestronglyMeasurable

theorem embed_translate (h : Space) {φ : Space → Space} (hφ : IsTestField φ) :
    shiftX h (embedX φ) = embedX (fun y => φ (y - h)) := by
  have m1 : ofGrad φ ∈ Sig :=
    embedMem_holds φ (Breakdown.Freq.Internal.VelocityRotate.decay_of_test hφ)
  have m2 : ofGrad (fun y => φ (y - h)) ∈ Sig :=
    embedMem_holds _ (Breakdown.Freq.Internal.VelocityRotate.decay_of_test (test_translate h hφ))
  have e1 : ((embedX φ : X) : L2C) = ofGrad φ := by
    unfold embedX
    rw [dif_pos m1]
  have e2 : ((embedX (fun y => φ (y - h)) : X) : L2C) = ofGrad (fun y => φ (y - h)) := by
    unfold embedX
    rw [dif_pos m2]
  apply Subtype.ext
  rw [shiftX_coe, e1, e2, ofGrad_translate h hφ]

theorem velocity_shift (h : Space) (x : X) :
    (velocity (shiftX h x) : Space → Space) =ᵐ[volume]
      fun y => (velocity x : Space → Space) (y - h) := by
  have hA : MeasurePreserving (fun y : Space => y - h) volume ((1 : ℝ≥0∞) • volume) := by
    rw [one_smul]
    exact measurePreserving_sub_right (volume : Measure Space) h
  have key := Breakdown.Freq.Internal.VelocityRotate.eq_of_test testDense_holds.2 testSpan_holds
    (shiftX h).continuous
    (Breakdown.Freq.Internal.VelocityRotate.compOp hA ENNReal.one_ne_top
      (ContinuousLinearMap.id ℝ Space))
    (fun φ hφ => by
      rw [embed_translate h hφ,
        Breakdown.Freq.Internal.VelocityRotate.velocity_spec velocity_holds _ (test_translate h hφ),
        Breakdown.Freq.Internal.VelocityRotate.velocity_spec velocity_holds _ hφ,
        Breakdown.Freq.Internal.VelocityRotate.compOp_toLp hA _ _
          (Breakdown.Freq.Internal.VelocityRotate.memLp_test hφ)]
      rfl) x
  rw [key]
  exact Breakdown.Freq.Internal.VelocityRotate.compOp_ae hA _ _ (velocity x)

theorem trilinear_shift (h : Space) (u v : X) (w : Space → Space) :
    trilinear (shiftX h u) (shiftX h v) w = trilinear u v (fun y => w (y + h)) := by
  unfold trilinear
  have hae : (fun y => ∑ j : Fin 3, (velocity (shiftX h u) : Space → Space) y j *
      inner ℝ ((partialX j (shiftX h v) : Space → Space) y) (w y)) =ᵐ[volume]
      fun y => (fun x => ∑ j : Fin 3, (velocity u : Space → Space) x j *
        inner ℝ ((partialX j v : Space → Space) x) (w (x + h))) (y - h) := by
    filter_upwards [velocity_shift h u, ae_all_iff.2 fun j => partialX_shift h j v] with y hu hv
    simp only [hu, hv, sub_add_cancel]
  refine (integral_congr_ae hae).trans ?_
  exact integral_sub_right_eq_self (μ := volume) (fun x => ∑ j : Fin 3, (velocity u : Space → Space) x j *
    inner ℝ ((partialX j v : Space → Space) x) (w (x + h))) h

theorem bilinForm_shift (τ : ℝ) (hτ : 0 < τ) (h : Space) (u v ψ : X) :
    bilinForm τ (shiftX h u) (shiftX h v) ψ = bilinForm τ u v (shiftX (-h) ψ) := by
  have hw : (phiX τ (shiftX (-h) ψ) : Space → Space) =ᵐ[volume]
      fun y => (phiX τ ψ : Space → Space) (y + h) := by
    filter_upwards [phiX_shift τ hτ (-h) ψ] with y hy
    rw [hy, sub_neg_eq_add]
  unfold bilinForm
  rw [trilinear_shift, trilinear_shift, Breakdown.Freq.Internal.BilinRotate.trilinear_congr u v hw,
    Breakdown.Freq.Internal.BilinRotate.trilinear_congr v u hw]

theorem bilinX_spec {τ : ℝ} (hτ : 0 < τ) : BilinSpec τ (bilinX τ) := by
  have h : 0 < τ ∧ ∃ B, BilinSpec τ B := ⟨hτ, bilin_holds.1 τ hτ⟩
  have e : bilinX τ = h.2.choose := dif_pos h
  rw [e]
  exact h.2.choose_spec

end Internal.TranslationCovariance

open Internal.TranslationCovariance in
theorem shiftCovariance_holds : ShiftCovariance := by
  intro τ hτ h u v
  refine ext_inner_right ℝ fun ψ => ?_
  rw [bilinX_spec hτ, inner_shiftX, bilinX_spec hτ, bilinForm_shift τ hτ]

end Breakdown.FarField
