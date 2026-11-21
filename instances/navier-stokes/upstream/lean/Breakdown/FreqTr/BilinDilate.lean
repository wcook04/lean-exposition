import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.Freq

namespace Internal.BilinDilate

theorem freqTrInv_comp_smul_aux (f : Space → CSpace) (a : ℝ) (ha : 0 < a) (x : Space) :
    𝓕⁻ (fun ξ => f (a • ξ)) x = ((a ^ 3)⁻¹ : ℝ) • 𝓕⁻ f (a⁻¹ • x) := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  have h := Measure.integral_comp_smul (volume : Measure Space)
    (fun w => 𝐞 (inner ℝ (a⁻¹ • w) x) • f w) a
  simp only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul, finrank_euclideanSpace, Fintype.card_fin] at h
  rw [h, abs_of_pos (by positivity)]
  congr 1
  congr 1
  ext w
  rw [real_inner_smul_left, real_inner_smul_right]

def scaleEquiv (a : ℝ) (ha : a ≠ 0) : Space ≃L[ℝ] Space :=
  (LinearEquiv.smulOfNeZero ℝ Space a ha).toContinuousLinearEquiv

theorem scaleEquiv_apply (a : ℝ) (ha : a ≠ 0) (ξ : Space) : scaleEquiv a ha ξ = a • ξ := rfl

def scaleOp (a : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp (fun ξ => a • ξ) (fun _ => ContinuousLinearMap.id ℝ CSpace)

theorem scaleOp_ae (h3 : FieldOpRealized) {a : ℝ} (ha : a ≠ 0) (f : L2C) :
    (scaleOp a f : Space → CSpace) =ᵐ[volume] fun ξ => f (a • ξ) := by
  have := h3 (scaleEquiv a ha) (fun _ => ContinuousLinearMap.id ℝ CSpace) 1
    aestronglyMeasurable_const (fun _ => ContinuousLinearMap.norm_id_le)
  exact this f

theorem comp_smul_ae {β : Type*} {g g' : Space → β} (h : g =ᵐ[volume] g') {a : ℝ} (ha : a ≠ 0) :
    (fun ξ => g (a • ξ)) =ᵐ[volume] fun ξ => g' (a • ξ) :=
  h.comp_tendsto (Measure.quasiMeasurePreserving_smul volume ha).tendsto_ae

theorem freqTrInvR_scaleOp (h3 : FieldOpRealized) {a : ℝ} (ha : 0 < a) :
    freqTrInvR ∘L scaleOp a = ((a ^ 3)⁻¹ : ℝ) • (scaleOp a⁻¹ ∘L freqTrInvR) := by
  have hd := SchwartzMap.denseRange_toLpCLM (F := CSpace) (E := Space) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top
  have key := hd.equalizer (freqTrInvR ∘L scaleOp a).continuous
    (((a ^ 3)⁻¹ : ℝ) • (scaleOp a⁻¹ ∘L freqTrInvR)).continuous
  refine DFunLike.coe_injective (key ?_)
  funext f
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply, ContinuousLinearMap.coe_comp,
    FunLike.coe_smul, Pi.smul_apply]
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv a ha.ne') f with hg
  have h1 : scaleOp a (f.toLp 2) = g.toLp 2 := by
    apply Lp.ext
    refine (scaleOp_ae h3 ha.ne' _).trans ?_
    refine (comp_smul_ae (f.coeFn_toLp 2 volume) ha.ne').trans ?_
    exact (g.coeFn_toLp 2 volume).symm
  rw [h1]
  change 𝓕⁻ (g.toLp 2) = ((a ^ 3)⁻¹ : ℝ) • scaleOp a⁻¹ (𝓕⁻ (f.toLp 2))
  rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourierInv_eq]
  apply Lp.ext
  refine ((𝓕⁻ g).coeFn_toLp 2 volume).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  have h2 := scaleOp_ae h3 (inv_ne_zero ha.ne') ((𝓕⁻ f).toLp 2)
  have h3' := comp_smul_ae ((𝓕⁻ f).coeFn_toLp 2 volume) (inv_ne_zero ha.ne')
  filter_upwards [h2, h3'] with x hx hx'
  rw [Pi.smul_apply, hx, hx', SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe]
  exact freqTrInv_comp_smul_aux f a ha x

theorem freqTrInv_scaleOp_ae (h3 : FieldOpRealized) {a : ℝ} (ha : 0 < a) (f : L2C) :
    (freqTrL2.symm (scaleOp a f) : Space → CSpace) =ᵐ[volume]
      fun x => ((a ^ 3)⁻¹ : ℝ) • (freqTrL2.symm f : Space → CSpace) (a⁻¹ • x) := by
  have h := congrArg (fun T : L2C →L[ℝ] L2C => T f) (freqTrInvR_scaleOp h3 ha)
  change freqTrL2.symm (scaleOp a f) = ((a ^ 3)⁻¹ : ℝ) • scaleOp a⁻¹ (freqTrL2.symm f) at h
  rw [h]
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [scaleOp_ae h3 (inv_ne_zero ha.ne') (freqTrL2.symm f)] with x hx
  rw [Pi.smul_apply, hx]

theorem toPhys_ae (g : L2C) :
    (toPhys g : Space → Space) =ᵐ[volume] fun x => realVec ((freqTrL2.symm g : Space → CSpace) x) :=
  ContinuousLinearMap.coeFn_compLpL realVec _

theorem toPhys_scaleOp_ae (h3 : FieldOpRealized) {a : ℝ} (ha : 0 < a) (f : L2C) :
    (toPhys (scaleOp a f) : Space → Space) =ᵐ[volume]
      fun x => ((a ^ 3)⁻¹ : ℝ) • (toPhys f : Space → Space) (a⁻¹ • x) := by
  filter_upwards [toPhys_ae (scaleOp a f), freqTrInv_scaleOp_ae h3 ha f,
    comp_smul_ae (toPhys_ae f) (inv_ne_zero ha.ne')] with x h1 h2 h4
  rw [h1, h2, h4, map_smul]

theorem fieldOp_id_ae (h3 : FieldOpRealized) {T : Space → CSpace →L[ℝ] CSpace} {C : ℝ}
    (hT : AEStronglyMeasurable T volume) (hC : ∀ ξ, ‖T ξ‖ ≤ C) (f : L2C) :
    (fieldOp id T f : Space → CSpace) =ᵐ[volume] fun ξ => T ξ (f ξ) :=
  h3 (ContinuousLinearEquiv.refl ℝ Space) T C hT hC f

theorem fieldOp_id_scaleOp (h3 : FieldOpRealized) {S T : Space → CSpace →L[ℝ] CSpace} {C D : ℝ}
    (hS : AEStronglyMeasurable S volume) (hSC : ∀ ξ, ‖S ξ‖ ≤ C)
    (hT : AEStronglyMeasurable T volume) (hTD : ∀ ξ, ‖T ξ‖ ≤ D) {a k : ℝ} (ha : a ≠ 0)
    (hST : ∀ ξ w, S ξ w = k • T (a • ξ) w) (f : L2C) :
    fieldOp id S (scaleOp a f) = k • scaleOp a (fieldOp id T f) := by
  apply Lp.ext
  refine (fieldOp_id_ae h3 hS hSC _).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  filter_upwards [scaleOp_ae h3 ha f, scaleOp_ae h3 ha (fieldOp id T f),
    comp_smul_ae (fieldOp_id_ae h3 hT hTD f) ha] with ξ h1 h2 h4
  rw [Pi.smul_apply, h1, h2, h4, hST]

theorem cmul_cont : Continuous cmul := by unfold cmul; fun_prop

theorem derivSymbol_smul (j : Fin 3) {a : ℝ} (ha : 0 < a) (ξ : Space) :
    derivSymbol j (a • ξ) = derivSymbol j ξ := by
  unfold derivSymbol
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, PiLp.smul_apply, smul_eq_mul]
  have : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
  have ha' : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp

theorem norm_derivSymbol_le (j : Fin 3) (ξ : Space) : ‖derivSymbol j ξ‖ ≤ 1 := by
  unfold derivSymbol
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs (ξ j), Real.norm_eq_abs ‖ξ‖, abs_of_pos hpos, div_le_one hpos]
  have := PiLp.norm_apply_le ξ j
  rwa [Real.norm_eq_abs] at this

theorem norm_cmul_le (z : ℂ) : ‖cmul z‖ ≤ ‖z‖ := by
  unfold cmul
  rw [ContinuousLinearMap.norm_restrictScalars]
  refine (norm_smul_le _ _).trans ?_
  have := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := CSpace)
  nlinarith [norm_nonneg z]

theorem measurable_derivSymbol (j : Fin 3) : Measurable (derivSymbol j) := by
  unfold derivSymbol
  fun_prop

theorem aesm_derivOp (j : Fin 3) :
    AEStronglyMeasurable (fun ξ => cmul (derivSymbol j ξ)) volume :=
  (cmul_cont.measurable.comp (measurable_derivSymbol j)).aestronglyMeasurable

theorem norm_derivOp_le (j : Fin 3) (ξ : Space) : ‖cmul (derivSymbol j ξ)‖ ≤ 1 :=
  (norm_cmul_le _).trans (norm_derivSymbol_le j ξ)

theorem phiFactor_nonneg (τ : ℝ) (ξ : Space) : 0 ≤ phiFactor τ ξ := by
  unfold phiFactor; positivity

theorem phiFactor_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) : phiFactor τ ξ ≤ (Real.sqrt τ)⁻¹ := by
  unfold phiFactor
  set s := 2 * π * ‖ξ‖
  have hs : 0 ≤ s := by positivity
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have he : -(4 * π ^ 2 * τ * ‖ξ‖ ^ 2) = -((Real.sqrt τ * s) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hτ.le]; ring
  rw [he]
  have h1 : Real.sqrt τ * s ≤ Real.exp ((Real.sqrt τ * s) ^ 2) := by
    have := Real.add_one_le_exp ((Real.sqrt τ * s) ^ 2)
    nlinarith [sq_nonneg (Real.sqrt τ * s - 1)]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), le_inv_mul_iff₀ hst]
  exact h1

theorem aesm_phiOp (τ : ℝ) :
    AEStronglyMeasurable (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) volume := by
  have : Continuous (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) := by
    unfold phiFactor; fun_prop
  exact this.aestronglyMeasurable

theorem norm_phiOp_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    ‖phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ (Real.sqrt τ)⁻¹ := by
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (phiFactor_nonneg τ ξ)]
  have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := CSpace)
  have h2 := phiFactor_le hτ ξ
  nlinarith [phiFactor_nonneg τ ξ]

theorem phiFactor_scale {c : ℝ} (hc : 0 < c) (τ : ℝ) (ξ : Space) :
    phiFactor (c ^ 2 * τ) ξ = c⁻¹ * phiFactor τ (c • ξ) := by
  unfold phiFactor
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have : -(4 * π ^ 2 * (c ^ 2 * τ) * ‖ξ‖ ^ 2) = -(4 * π ^ 2 * τ * (c * ‖ξ‖) ^ 2) := by ring
  rw [this]
  field_simp

theorem dilX_coe (h2 : DilationAlgebra) (h3 : FieldOpRealized) {μ : ℝ} (hμ : 0 < μ) (x : X) :
    (dilX μ x : L2C) = (Real.sqrt μ)⁻¹ • scaleOp (Real.sqrt μ)⁻¹ (x : L2C) := by
  rw [h2.2.2.2.2 μ hμ x]
  have hc : (Real.sqrt μ)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hμ).ne'
  have hr := h3 (scaleEquiv _ hc) (fun _ => (Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ CSpace)
    (‖(Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ CSpace‖) aestronglyMeasurable_const (fun _ => le_rfl)
  apply Lp.ext
  refine (hr (x : L2C)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  filter_upwards [scaleOp_ae h3 hc (x : L2C)] with ξ h1
  rw [Pi.smul_apply, h1]
  rfl

theorem partialX_eq (j : Fin 3) (z : X) :
    partialX j z = toPhys (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (z : L2C)) := rfl

theorem phiX_eq (τ : ℝ) (z : X) :
    phiX τ z = toPhys (fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) (z : L2C)) := rfl

theorem partialX_dilX (h2 : DilationAlgebra) (h3 : FieldOpRealized) {μ : ℝ} (hμ : 0 < μ) (j : Fin 3)
    (x : X) :
    (partialX j (dilX μ x) : Space → Space) =ᵐ[volume]
      fun y => μ • (partialX j x : Space → Space) (Real.sqrt μ • y) := by
  have hc : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hci : 0 < (Real.sqrt μ)⁻¹ := inv_pos.mpr hc
  rw [partialX_eq, dilX_coe h2 h3 hμ, map_smul,
    fieldOp_id_scaleOp h3 (aesm_derivOp j) (norm_derivOp_le j) (aesm_derivOp j) (norm_derivOp_le j)
      hci.ne' (k := 1) (fun ξ w => by rw [derivSymbol_smul j hci, one_smul]),
    one_smul, map_smul]
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [toPhys_scaleOp_ae h3 hci (fieldOp id (fun ξ => cmul (derivSymbol j ξ)) (x : L2C))]
    with y hy
  rw [Pi.smul_apply, hy, inv_inv, smul_smul, partialX_eq]
  congr 1
  have hsq := Real.sq_sqrt hμ.le
  field_simp
  linarith

theorem phiX_dilX_inv (h2 : DilationAlgebra) (h3 : FieldOpRealized) {μ τ : ℝ} (hμ : 0 < μ)
    (hτ : 0 < τ) (ψ : X) :
    (phiX (μ * τ) (dilX μ⁻¹ ψ) : Space → Space) =ᵐ[volume]
      fun y => ((Real.sqrt μ ^ 3)⁻¹ : ℝ) • (phiX τ ψ : Space → Space) ((Real.sqrt μ)⁻¹ • y) := by
  have hc : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hμ' : μ * τ = Real.sqrt μ ^ 2 * τ := by rw [Real.sq_sqrt hμ.le]
  rw [phiX_eq, dilX_coe h2 h3 (inv_pos.mpr hμ), Real.sqrt_inv, inv_inv, map_smul, hμ',
    fieldOp_id_scaleOp h3 (aesm_phiOp _) (norm_phiOp_le (by positivity)) (aesm_phiOp τ)
      (norm_phiOp_le hτ) hc.ne' (k := (Real.sqrt μ)⁻¹)
      (fun ξ w => by
        show phiFactor _ ξ • w = (Real.sqrt μ)⁻¹ • (phiFactor τ (Real.sqrt μ • ξ) • w)
        rw [smul_smul, phiFactor_scale hc]),
    map_smul, map_smul]
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [Lp.coeFn_smul ((Real.sqrt μ)⁻¹) (toPhys (scaleOp (Real.sqrt μ) (fieldOp id
      (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C)))),
    toPhys_scaleOp_ae h3 hc (fieldOp id
      (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C))] with y hy1 hy2
  rw [Pi.smul_apply, hy1, Pi.smul_apply, hy2, smul_smul, smul_smul, phiX_eq]
  congr 1
  field_simp

theorem inner_scaleOp (h3 : FieldOpRealized) {a : ℝ} (ha : 0 < a) (f g : L2C) :
    inner ℝ (scaleOp a f) g = (a ^ 3)⁻¹ * inner ℝ f (scaleOp a⁻¹ g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have e1 : ∫ ξ, inner ℝ ((scaleOp a f : Space → CSpace) ξ) ((g : Space → CSpace) ξ) =
      ∫ ξ, (fun η => inner ℝ ((f : Space → CSpace) η) ((g : Space → CSpace) (a⁻¹ • η))) (a • ξ) := by
    apply integral_congr_ae
    filter_upwards [scaleOp_ae h3 ha.ne' f] with ξ hξ
    simp only [hξ, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  have e2 : ∫ η, inner ℝ ((f : Space → CSpace) η) ((g : Space → CSpace) (a⁻¹ • η)) =
      ∫ η, inner ℝ ((f : Space → CSpace) η) ((scaleOp a⁻¹ g : Space → CSpace) η) := by
    apply integral_congr_ae
    filter_upwards [scaleOp_ae h3 (inv_ne_zero ha.ne') g] with ξ hξ
    rw [hξ]
  rw [e1, Measure.integral_comp_smul volume
    (fun η => inner ℝ ((f : Space → CSpace) η) ((g : Space → CSpace) (a⁻¹ • η))) a, e2, finrank_euclideanSpace, Fintype.card_fin,
    abs_of_pos (by positivity), smul_eq_mul]

theorem dilX_adjoint (h2 : DilationAlgebra) (h3 : FieldOpRealized) {μ : ℝ} (hμ : 0 < μ) (x y : X) :
    inner ℝ (dilX μ x) y = Real.sqrt μ * inner ℝ x (dilX μ⁻¹ y) := by
  have hc : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  change inner ℝ (dilX μ x : L2C) (y : L2C) = Real.sqrt μ * inner ℝ (x : L2C) (dilX μ⁻¹ y : L2C)
  rw [dilX_coe h2 h3 hμ, dilX_coe h2 h3 (inv_pos.mpr hμ), Real.sqrt_inv, inv_inv,
    real_inner_smul_left, real_inner_smul_right, inner_scaleOp h3 (inv_pos.mpr hc), inv_inv]
  field_simp

theorem summand_scale {c μ : ℝ} (hsq : c ^ 2 = μ) (U P W : Space) (j : Fin 3) :
    (c • U) j * inner ℝ (μ • P) (c ^ 3 • W) = c ^ 6 * (U j * inner ℝ P W) := by
  rw [PiLp.smul_apply, smul_eq_mul, real_inner_smul_left, real_inner_smul_right, ← hsq]
  ring

theorem integral_scale_six {c : ℝ} (hc : 0 < c) (G : Space → ℝ) :
    ∫ x, c ^ 6 * G (c • x) = c ^ 3 * ∫ x, G x := by
  rw [integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace, Fintype.card_fin,
    smul_eq_mul, abs_of_pos (by positivity)]
  field_simp

theorem trilinear_dilX (h2 : DilationAlgebra) (h3 : FieldOpRealized) (h4 : VelocityDilate)
    {μ τ : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (u v ψ : X) :
    trilinear (dilX μ u) (dilX μ v) (phiX τ ψ) =
      Real.sqrt μ ^ 3 * trilinear u v (phiX (μ * τ) (dilX μ⁻¹ ψ)) := by
  have hc : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsq := Real.sq_sqrt hμ.le
  unfold trilinear
  have hU := h4 μ hμ u
  have hV : ∀ᵐ y ∂volume, ∀ j : Fin 3, (partialX j (dilX μ v) : Space → Space) y =
      μ • (partialX j v : Space → Space) (Real.sqrt μ • y) :=
    ae_all_iff.2 (fun j => partialX_dilX h2 h3 hμ j v)
  have hw := comp_smul_ae (phiX_dilX_inv h2 h3 hμ hτ ψ) hc.ne'
  have e1 : (fun x => ∑ j : Fin 3, (velocity (dilX μ u) : Space → Space) x j *
      inner ℝ ((partialX j (dilX μ v) : Space → Space) x) ((phiX τ ψ : Space → Space) x)) =ᵐ[volume]
      fun x => Real.sqrt μ ^ 6 * (fun y => ∑ j : Fin 3, (velocity u : Space → Space) y j *
        inner ℝ ((partialX j v : Space → Space) y)
          ((phiX (μ * τ) (dilX μ⁻¹ ψ) : Space → Space) y)) (Real.sqrt μ • x) := by
    filter_upwards [hU, hV, hw] with x hx1 hx2 hx3
    simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hx3
    have hx3' : (phiX τ ψ : Space → Space) x =
        Real.sqrt μ ^ 3 • (phiX (μ * τ) (dilX μ⁻¹ ψ) : Space → Space) (Real.sqrt μ • x) := by
      rw [hx3, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    beta_reduce
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hx1, hx2 j, hx3']
    exact summand_scale hsq _ _ _ j
  exact (integral_congr_ae e1).trans (integral_scale_six hc (fun y => ∑ j : Fin 3, (velocity u : Space → Space) y j *
        inner ℝ ((partialX j v : Space → Space) y)
          ((phiX (μ * τ) (dilX μ⁻¹ ψ) : Space → Space) y)))

theorem bilinX_spec (h1 : BilinExists) {τ : ℝ} (hτ : 0 < τ) : BilinSpec τ (bilinX τ) := by
  have hh : 0 < τ ∧ ∃ B, BilinSpec τ B := ⟨hτ, h1 τ hτ⟩
  unfold bilinX
  rw [dif_pos hh]
  exact hh.2.choose_spec

end Internal.BilinDilate

open Internal.BilinDilate

theorem bilinDilate (h1 : BilinExists) (h2 : DilationAlgebra) (h3 : FieldOpRealized) (h4 : VelocityDilate) (_h5 : TrilinearBound) (_h6 : HeatSemigroup) :
    BilinDilate := by
  intro μ τ hμ hτ u v
  apply ext_inner_right ℝ
  intro ψ
  have hsq := Real.sq_sqrt hμ.le
  rw [real_inner_smul_left, dilX_adjoint h2 h3 hμ, bilinX_spec h1 (mul_pos hμ hτ),
    bilinX_spec h1 hτ]
  unfold bilinForm
  rw [trilinear_dilX h2 h3 h4 hμ hτ u v ψ, trilinear_dilX h2 h3 h4 hμ hτ v u ψ]
  generalize trilinear u v (phiX (μ * τ) (dilX μ⁻¹ ψ)) = A
  generalize trilinear v u (phiX (μ * τ) (dilX μ⁻¹ ψ)) = B
  linear_combination ((1 / 2 : ℝ) * (A + B) * Real.sqrt μ) * hsq

end Breakdown.Freq
