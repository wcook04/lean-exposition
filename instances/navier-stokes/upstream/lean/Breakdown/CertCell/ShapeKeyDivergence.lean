import Breakdown.CertCell.ShapeSplineDeriv
import Breakdown.CertCell.ShapeOriginProfile

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline radialVec polarVecQ azimVecQ heightRatio heightDeriv radialScale weightPoly)

namespace Internal

private theorem typeOne_reduced_cancel (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (A : KeyAmp)
    (h : κ.label.1 ≠ 0) (t x : ℝ) :
    shiftedScale P κ.phaseIndex (fun t x => reducedComps P κ A t x 0) t x + 2 * reducedComps P κ A t x 0 -
      heightDeriv (fun t x => polarFactor x * reducedComps P κ A t x 1) t x +
      Complex.I * (labelAzimuth P.azimuthOrder κ.label : ℂ) * reducedComps P κ A t x 2 = 0 := by
  have hk : (labelAzimuth P.azimuthOrder κ.label : ℂ) ≠ 0 := by
    have hm : (P.azimuthOrder : ℤ) ≠ 0 := by exact_mod_cast hP.azimuthOrder_pos.ne'
    exact_mod_cast mul_ne_zero h hm
  simp only [reducedComps, if_neg h, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  generalize (labelAzimuth P.azimuthOrder κ.label : ℂ) = k at hk ⊢
  generalize shiftedScale P κ.phaseIndex _ t x + _ - _ = X
  field_simp
  rw [Complex.I_sq]
  ring

private theorem mixed_partials {Φ : ℝ → ℝ → ℂ} {t x : ℝ}
    (hΦ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => Φ z.1 z.2) (t, x)) :
    HasDerivAt (fun x' => deriv (fun t' => Φ t' x') t) (deriv (fun t' => deriv (fun x' => Φ t' x') x) t) x ∧
      DifferentiableAt ℝ (fun x' => Φ t x') x := by
  set G : ℝ × ℝ → ℂ := fun z => Φ z.1 z.2 with hGdef
  have hev : ∀ᶠ w in nhds ((t, x) : ℝ × ℝ), DifferentiableAt ℝ G w :=
    (hΦ.eventually (by simp)).mono fun w hw => hw.differentiableAt (by norm_num)
  have hDD : DifferentiableAt ℝ (fderiv ℝ G) (t, x) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := hΦ.isSymmSndFDerivAt (by simp)
  have lineX : ∀ a b : ℝ, HasDerivAt (fun x' : ℝ => ((a, x') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) b := fun a b =>
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have lineT : ∀ a b : ℝ, HasDerivAt (fun t' : ℝ => ((t', a) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) b := fun a b =>
    (hasDerivAt_id b).prodMk (hasDerivAt_const b a)
  have pX : ∀ w : ℝ × ℝ, DifferentiableAt ℝ G w →
      deriv (fun x' => Φ w.1 x') w.2 = fderiv ℝ G w ((0 : ℝ), (1 : ℝ)) := fun w hw => by
    have h := (hw.hasFDerivAt.comp_hasDerivAt w.2 (lineX w.1 w.2)).deriv
    exact h
  have pT : ∀ w : ℝ × ℝ, DifferentiableAt ℝ G w →
      deriv (fun t' => Φ t' w.2) w.1 = fderiv ℝ G w ((1 : ℝ), (0 : ℝ)) := fun w hw => by
    have h := (hw.hasFDerivAt.comp_hasDerivAt w.1 (lineT w.2 w.1)).deriv
    exact h
  have e1 : (fun t' => deriv (fun x' => Φ t' x') x) =ᶠ[nhds t]
      fun t' => fderiv ℝ G (t', x) ((0 : ℝ), (1 : ℝ)) :=
    ((lineT x t).continuousAt.tendsto.eventually hev).mono fun t' h => pX (t', x) h
  have e2 : (fun x' => deriv (fun t' => Φ t' x') t) =ᶠ[nhds x]
      fun x' => fderiv ℝ G (t, x') ((1 : ℝ), (0 : ℝ)) :=
    ((lineX t x).continuousAt.tendsto.eventually hev).mono fun x' h => pT (t, x') h
  have d1 : HasDerivAt (fun t' => fderiv ℝ G (t', x) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ (fderiv ℝ G) (t, x) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) t := by
    have := (hDD.hasFDerivAt.comp_hasDerivAt t (lineT x t))
    exact this.clm_apply (hasDerivAt_const t ((0 : ℝ), (1 : ℝ))) |>.congr_deriv (by simp)
  have d2 : HasDerivAt (fun x' => fderiv ℝ G (t, x') ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ (fderiv ℝ G) (t, x) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))) x := by
    have := (hDD.hasFDerivAt.comp_hasDerivAt x (lineX t x))
    exact this.clm_apply (hasDerivAt_const x ((1 : ℝ), (0 : ℝ))) |>.congr_deriv (by simp)
  refine ⟨?_, ?_⟩
  · rw [(d1.congr_of_eventuallyEq e1).deriv, hsym]
    exact d2.congr_of_eventuallyEq e2
  · exact (hev.self_of_nhds).comp x (lineX t x).differentiableAt

private theorem partial_cancel {Φ : ℝ → ℝ → ℂ} (c : ℝ → ℂ) {t x : ℝ}
    (hΦ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => Φ z.1 z.2) (t, x)) :
    ((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => -deriv (fun x' => Φ t' x') x) t +
        c t * -deriv (fun x' => Φ t x') x + 2 * -deriv (fun x' => Φ t x') x -
      deriv (fun x' => -(((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => Φ t' x') t + c t * Φ t x' + 2 * Φ t x')) x
      = 0 := by
  obtain ⟨hm, hd⟩ := mixed_partials hΦ
  have hsum : HasDerivAt (fun x' => -(((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => Φ t' x') t + c t * Φ t x' +
      2 * Φ t x')) (-(((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => deriv (fun x' => Φ t' x') x) t +
        c t * deriv (fun x' => Φ t x') x + 2 * deriv (fun x' => Φ t x') x)) x :=
    (((hm.const_mul _).add (hd.hasDerivAt.const_mul _)).add (hd.hasDerivAt.const_mul _)).neg
  have hn : deriv (fun t' => -deriv (fun x' => Φ t' x') x) t = -deriv (fun t' => deriv (fun x' => Φ t' x') x) t :=
    deriv.neg
  rw [hsum.deriv, hn]
  ring

private theorem typeTwo_reduced_cancel (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h : κ.label.1 = 0) {t x : ℝ}
    (hΦ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ =>
      weightPoly 1 A.highOrder z.1 * (polarFactor z.2 * streamValue P A z.1 z.2)) (t, x)) :
    shiftedScale P κ.phaseIndex (fun t x => reducedComps P κ A t x 0) t x + 2 * reducedComps P κ A t x 0 -
      heightDeriv (fun t x => polarFactor x * reducedComps P κ A t x 1) t x +
      Complex.I * (labelAzimuth P.azimuthOrder κ.label : ℂ) * reducedComps P κ A t x 2 = 0 := by
  set Φ : ℝ → ℝ → ℂ := fun t x => weightPoly 1 A.highOrder t * (polarFactor x * streamValue P A t x) with hΦdef
  set c : ℝ → ℂ := fun t => Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P t : ℝ) : ℂ) with hcdef
  have hk : (labelAzimuth P.azimuthOrder κ.label : ℂ) = 0 := by simp [labelAzimuth, h]
  have h0 : (fun t x => reducedComps P κ A t x 0) = fun t x => -deriv (fun x' => Φ t x') x := by
    funext t x
    simp only [reducedComps, if_pos h, Matrix.cons_val_zero, heightDeriv, hΦdef]
    rw [deriv_const_mul_field']
  have h1 : (fun t x => polarFactor x * reducedComps P κ A t x 1) =
      fun t x => -(((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => Φ t' x) t + c t * Φ t x + 2 * Φ t x) := by
    funext t x
    simp only [reducedComps, if_pos h, Matrix.cons_val_one, Matrix.cons_val_zero, shiftedScale, radialScale,
      hΦdef, hcdef]
    have : (fun t' => weightPoly 1 A.highOrder t' * (polarFactor x * streamValue P A t' x)) =
        fun t' => polarFactor x * (weightPoly 1 A.highOrder t' * streamValue P A t' x) := by
      funext t'
      ring
    rw [this, deriv_const_mul_field']
    ring
  have h0' : reducedComps P κ A t x 0 = -deriv (fun x' => Φ t x') x := congrFun (congrFun h0 t) x
  rw [hk, h0, h1, h0']
  unfold shiftedScale radialScale heightDeriv
  have := partial_cancel (Φ := Φ) c hΦ
  simp only [hcdef] at this ⊢
  linear_combination this

private theorem divergence_of_dense {f : Space → Fin 3 → ℂ} (hf : ContDiff ℝ 1 f)
    (h : ∀ y : Space, y 1 ≠ 0 → complexDivergence f y = 0) (y : Space) : complexDivergence f y = 0 := by
  have hc : Continuous (complexDivergence f) := by
    unfold complexDivergence
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i).comp ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  set g : ℝ → ℂ := fun ε => complexDivergence f (y + ε • unitVector 1) with hg
  have hgc : Continuous g := hc.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hext : g = fun _ => 0 := by
    refine Continuous.ext_on (dense_compl_singleton (-y 1)) hgc continuous_const fun ε hε => ?_
    apply h
    have hne : ε ≠ -y 1 := hε
    intro h0
    simp [unitVector] at h0
    exact hne (by linear_combination h0)
  have := congrFun hext 0
  simpa [hg] using this


private theorem ofReal_contDiff {n : ℕ∞ω} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) : ContDiff ℝ n (fun t => (g t : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hg

private theorem c2_deriv_diff {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) : Differentiable ℝ g ∧ Differentiable ℝ (deriv g) := by
  have h := (contDiff_succ_iff_deriv (n := 1)).1 (show ContDiff ℝ (1 + 1) g from hg)
  exact ⟨h.1, h.2.2.differentiable (by norm_num)⟩

private theorem weightPoly_c2 (e0 e1 : ℕ) : ContDiff ℝ 2 (weightPoly e0 e1) :=
  ofReal_contDiff (g := fun t : ℝ => t ^ e0 * (1 - t) ^ e1) (by fun_prop)

private theorem polarFactor_c2 : ContDiff ℝ 2 polarFactor :=
  ofReal_contDiff (g := fun x : ℝ => 1 - x ^ 2) (by fun_prop)

private theorem axisFactor_c2 : ContDiff ℝ 2 axisFactor :=
  ofReal_contDiff (g := fun x : ℝ => (1 - x ^ 2) ^ 2) (by fun_prop)

private theorem phaseSlope_differentiableAt {P : ShapeParams} (hP : IsShapeParams P) {t : ℝ} (ht : t < 1) :
    DifferentiableAt ℝ (phaseSlope P) t := by
  obtain ⟨δ, hδ, hf⟩ := hP.phase.smooth
  have hd : ContDiffOn ℝ 2 (deriv P.radialPhase) (Set.Ioi (-δ)) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 2) isOpen_Ioi).1 (show ContDiffOn ℝ (2 + 1) _ _ from hf)).2.2
  have hr : DifferentiableAt ℝ (chartRadius P) t := by
    unfold chartRadius
    exact (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => P.chartLength * t) t).div (by fun_prop)
      (sub_ne_zero.2 ht.ne')
  have hmem : chartRadius P t ^ 2 ∈ Set.Ioi (-δ) := by
    simp only [Set.mem_Ioi]
    nlinarith [sq_nonneg (chartRadius P t)]
  have hdd : DifferentiableAt ℝ (deriv P.radialPhase) (chartRadius P t ^ 2) :=
    (hd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hmem)
  unfold phaseSlope
  have hc := hdd.comp t (hr.pow 2)
  exact ((hr.pow 2).const_mul 2).mul hc

private theorem spline_differentiable (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S)
    (ha : 1 ≤ a) (hb : 1 ≤ b) : Differentiable ℝ (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) :=
  ((hsm a b S hS).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb))).differentiable one_ne_zero

private theorem spline_hasDerivAt_t (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (t x : ℝ) :
    HasDerivAt (fun t' => S.evalHalf t' x) ((tDerivSpline S).evalHalf t x) t := by
  have hl : HasDerivAt (fun t' : ℝ => ((t', x) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hd : DifferentiableAt ℝ (fun t' => S.evalHalf t' x) t := by
    have h := (spline_differentiable hsm hS ha hb (t, x)).comp t hl.differentiableAt
    exact h
  rw [← (splineDerivatives_holds a b S hS).1 ha |>.2 t x]
  exact hd.hasDerivAt

private theorem spline_hasDerivAt_x (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (t x : ℝ) :
    HasDerivAt (fun x' => S.evalHalf t x') ((xDerivSpline S).evalHalf t x) x := by
  have hl : HasDerivAt (fun x' : ℝ => ((t, x') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
  have hd : DifferentiableAt ℝ (fun x' => S.evalHalf t x') x := by
    have h := (spline_differentiable hsm hS ha hb (t, x)).comp x hl.differentiableAt
    exact h
  rw [← (splineDerivatives_holds a b S hS).2 hb |>.2 t x]
  exact hd.hasDerivAt


private theorem fst_differentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E} {t x : ℝ}
    (hg : DifferentiableAt ℝ g t) : DifferentiableAt ℝ (fun z : ℝ × ℝ => g z.1) (t, x) :=
  hg.comp (t, x) differentiableAt_fst

private theorem snd_differentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E} {t x : ℝ}
    (hg : DifferentiableAt ℝ g x) : DifferentiableAt ℝ (fun z : ℝ × ℝ => g z.2) (t, x) :=
  hg.comp (t, x) differentiableAt_snd

private theorem partials_differentiableAt {F : ℝ → ℝ → ℂ} {t x : ℝ}
    (hF : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => F z.1 z.2) (t, x)) :
    DifferentiableAt ℝ (fun z : ℝ × ℝ => deriv (fun t' => F t' z.2) z.1) (t, x) ∧
      DifferentiableAt ℝ (fun z : ℝ × ℝ => deriv (fun x' => F z.1 x') z.2) (t, x) := by
  set G : ℝ × ℝ → ℂ := fun z => F z.1 z.2 with hGdef
  have hev : ∀ᶠ w in nhds ((t, x) : ℝ × ℝ), DifferentiableAt ℝ G w :=
    (hF.eventually (by simp)).mono fun w hw => hw.differentiableAt (by norm_num)
  have hDD : DifferentiableAt ℝ (fderiv ℝ G) (t, x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have pX : ∀ w : ℝ × ℝ, DifferentiableAt ℝ G w →
      deriv (fun x' => F w.1 x') w.2 = fderiv ℝ G w ((0 : ℝ), (1 : ℝ)) := fun w hw => by
    have h := (hw.hasFDerivAt.comp_hasDerivAt w.2 ((hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2))).deriv
    exact h
  have pT : ∀ w : ℝ × ℝ, DifferentiableAt ℝ G w →
      deriv (fun t' => F t' w.2) w.1 = fderiv ℝ G w ((1 : ℝ), (0 : ℝ)) := fun w hw => by
    have h := (hw.hasFDerivAt.comp_hasDerivAt w.1 ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))).deriv
    exact h
  refine ⟨?_, ?_⟩
  · have hd : DifferentiableAt ℝ (fun w => fderiv ℝ G w ((1 : ℝ), (0 : ℝ))) (t, x) :=
      hDD.clm_apply (differentiableAt_const _)
    exact hd.congr_of_eventuallyEq (hev.mono fun w hw => pT w hw)
  · have hd : DifferentiableAt ℝ (fun w => fderiv ℝ G w ((0 : ℝ), (1 : ℝ))) (t, x) :=
      hDD.clm_apply (differentiableAt_const _)
    exact hd.congr_of_eventuallyEq (hev.mono fun w hw => pX w hw)

private theorem streamValue_contDiffAt (hsm : JoinedSplineSmooth) {P : ShapeParams} (hP : IsShapeParams P) {A : KeyAmp}
    (hS : IsJoinedSpline 2 2 A.stream) {t x : ℝ} (ht : t < 1) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => streamValue P A z.1 z.2) (t, x) := by
  have hg0 : ContDiffAt ℝ 2 P.origin.eval t :=
    ((originProfileSmooth P.origin hP.origin).1).contDiffAt (Iio_mem_nhds ht)
  have hg : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => P.origin.eval z.1 * z.2) (t, x) :=
    (hg0.comp (t, x) contDiffAt_fst).mul contDiffAt_snd
  have hc : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => ((P.origin.eval z.1 * z.2 : ℝ) : ℂ)) (t, x) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (t, x) hg
  have hs : ContDiff ℝ 2 (fun z : ℝ × ℝ => A.stream.evalHalf z.1 z.2) := by
    simpa using hsm 2 2 A.stream hS
  unfold streamValue
  exact (contDiffAt_const.mul hc).add hs.contDiffAt

private theorem typeTwo_product_contDiffAt (hsm : JoinedSplineSmooth) {P : ShapeParams} (hP : IsShapeParams P)
    {A : KeyAmp} (hS : IsJoinedSpline 2 2 A.stream) {t x : ℝ} (ht : t < 1) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ =>
      weightPoly 1 A.highOrder z.1 * (polarFactor z.2 * streamValue P A z.1 z.2)) (t, x) :=
  ((weightPoly_c2 1 A.highOrder).contDiffAt.comp (t, x) contDiffAt_fst).mul
    ((polarFactor_c2.contDiffAt.comp (t, x) contDiffAt_snd).mul (streamValue_contDiffAt hsm hP hS ht))

private theorem typeTwo_components_differentiableAt (hsm : JoinedSplineSmooth) {P : ShapeParams} (hP : IsShapeParams P)
    {κ : FieldKey} {A : KeyAmp} (h : κ.label.1 = 0) (hS : IsJoinedSpline 2 2 A.stream)
    (hG : IsJoinedSpline 1 1 A.swirl) {t x : ℝ} (ht : t < 1) (c : Fin 3) :
    DifferentiableAt ℝ (fun z : ℝ × ℝ => reducedComps P κ A z.1 z.2 c) (t, x) := by
  have hp := (weightPoly_c2 1 A.highOrder).differentiable (by norm_num)
  have hpf : DifferentiableAt ℝ (fun z : ℝ × ℝ => weightPoly 1 A.highOrder z.1) (t, x) :=
    fst_differentiableAt (hp t)
  have hΨ := streamValue_contDiffAt hsm hP hS (x := x) ht
  have hH : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => polarFactor z.2 * streamValue P A z.1 z.2) (t, x) :=
    (polarFactor_c2.contDiffAt.comp (t, x) contDiffAt_snd).mul hΨ
  have hK : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => weightPoly 1 A.highOrder z.1 * streamValue P A z.1 z.2) (t, x) :=
    ((weightPoly_c2 1 A.highOrder).contDiffAt.comp (t, x) contDiffAt_fst).mul hΨ
  have dH := (partials_differentiableAt (F := fun t x => polarFactor x * streamValue P A t x) hH).2
  have dK := (partials_differentiableAt (F := fun t x => weightPoly 1 A.highOrder t * streamValue P A t x) hK).1
  have dΨ : DifferentiableAt ℝ (fun z : ℝ × ℝ => streamValue P A z.1 z.2) (t, x) :=
    hΨ.differentiableAt (by norm_num)
  have dG : DifferentiableAt ℝ (fun z : ℝ × ℝ => A.swirl.evalHalf z.1 z.2) (t, x) :=
    spline_differentiable hsm hG le_rfl le_rfl (t, x)
  have hs : DifferentiableAt ℝ (fun z : ℝ × ℝ => phaseSlope P z.1) (t, x) :=
    fst_differentiableAt (phaseSlope_differentiableAt hP ht)
  have hs' : DifferentiableAt ℝ (fun z : ℝ × ℝ =>
      Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P z.1 : ℝ) : ℂ)) (t, x) :=
    (differentiableAt_const _).mul (Complex.ofRealCLM.differentiableAt.comp (t, x) (hs.const_mul _))
  have hr : DifferentiableAt ℝ (fun z : ℝ × ℝ => ((z.1 * (1 - z.1) : ℝ) : ℂ)) (t, x) :=
    fst_differentiableAt (g := fun s : ℝ => ((s * (1 - s) : ℝ) : ℂ))
      ((Complex.ofRealCLM.differentiable.comp (by fun_prop : Differentiable ℝ fun s : ℝ => s * (1 - s))) t)
  fin_cases c
  · simp only [reducedComps, if_pos h, heightDeriv]
    exact (hpf.mul dH).neg
  · simp only [reducedComps, if_pos h, shiftedScale, radialScale]
    exact (((hr.mul dK).add (hs'.mul (hpf.mul dΨ))).add ((differentiableAt_const _).mul (hpf.mul dΨ))).neg
  · simp only [reducedComps, if_pos h]
    exact hpf.mul dG


private theorem typeOne_components_differentiableAt (hsm : JoinedSplineSmooth) {P : ShapeParams} (hP : IsShapeParams P)
    {κ : FieldKey} {A : KeyAmp} (h : κ.label.1 ≠ 0) (hA : IsJoinedSpline 2 1 A.radial)
    (hB : IsJoinedSpline 1 2 A.polar) {t x : ℝ} (ht : t < 1) (c : Fin 3) :
    DifferentiableAt ℝ (fun z : ℝ × ℝ => reducedComps P κ A z.1 z.2 c) (t, x) := by
  obtain ⟨hw, hwd⟩ := c2_deriv_diff (weightPoly_c2 A.lowOrder A.highOrder)
  obtain ⟨hq, hqd⟩ := c2_deriv_diff polarFactor_c2
  obtain ⟨ha, had⟩ := c2_deriv_diff axisFactor_c2
  have dA := spline_differentiable hsm hA (by norm_num) (by norm_num)
  have dB := spline_differentiable hsm hB (by norm_num) (by norm_num)
  have dAt := spline_differentiable hsm ((splineDerivatives_holds 2 1 A.radial hA).1 (by norm_num)).1 le_rfl le_rfl
  have dBx := spline_differentiable hsm ((splineDerivatives_holds 1 2 A.polar hB).2 (by norm_num)).1 le_rfl le_rfl
  have wf : DifferentiableAt ℝ (fun z : ℝ × ℝ => weightPoly A.lowOrder A.highOrder z.1) (t, x) :=
    fst_differentiableAt (hw t)
  have wdf : DifferentiableAt ℝ (fun z : ℝ × ℝ => deriv (weightPoly A.lowOrder A.highOrder) z.1) (t, x) :=
    fst_differentiableAt (hwd t)
  have af : DifferentiableAt ℝ (fun z : ℝ × ℝ => axisFactor z.2) (t, x) := snd_differentiableAt (ha x)
  have adf : DifferentiableAt ℝ (fun z : ℝ × ℝ => deriv axisFactor z.2) (t, x) := snd_differentiableAt (had x)
  have qf : DifferentiableAt ℝ (fun z : ℝ × ℝ => polarFactor z.2) (t, x) := snd_differentiableAt (hq x)
  have qdf : DifferentiableAt ℝ (fun z : ℝ × ℝ => deriv polarFactor z.2) (t, x) := snd_differentiableAt (hqd x)
  have U0 : DifferentiableAt ℝ (fun z : ℝ × ℝ =>
      weightPoly A.lowOrder A.highOrder z.1 * axisFactor z.2 * A.radial.evalHalf z.1 z.2) (t, x) :=
    (wf.mul af).mul (dA (t, x))
  have U1 : DifferentiableAt ℝ (fun z : ℝ × ℝ =>
      weightPoly A.lowOrder A.highOrder z.1 * axisFactor z.2 * A.polar.evalHalf z.1 z.2) (t, x) :=
    (wf.mul af).mul (dB (t, x))
  have D1 : DifferentiableAt ℝ (fun z : ℝ × ℝ => deriv (fun t' =>
      weightPoly A.lowOrder A.highOrder t' * axisFactor z.2 * A.radial.evalHalf t' z.2) z.1) (t, x) := by
    have e : (fun z : ℝ × ℝ => deriv (fun t' =>
        weightPoly A.lowOrder A.highOrder t' * axisFactor z.2 * A.radial.evalHalf t' z.2) z.1) =
        fun z => deriv (weightPoly A.lowOrder A.highOrder) z.1 * axisFactor z.2 * A.radial.evalHalf z.1 z.2 +
          weightPoly A.lowOrder A.highOrder z.1 * axisFactor z.2 * (tDerivSpline A.radial).evalHalf z.1 z.2 := by
      funext z
      exact ((((hw z.1).hasDerivAt).mul_const (axisFactor z.2)).mul
        (spline_hasDerivAt_t hsm hA (by norm_num) (by norm_num) z.1 z.2)).deriv
    rw [e]
    exact ((wdf.mul af).mul (dA (t, x))).add ((wf.mul af).mul (dAt (t, x)))
  have D2 : DifferentiableAt ℝ (fun z : ℝ × ℝ => deriv (fun x' => polarFactor x' *
      (weightPoly A.lowOrder A.highOrder z.1 * axisFactor x' * A.polar.evalHalf z.1 x')) z.2) (t, x) := by
    have e : (fun z : ℝ × ℝ => deriv (fun x' => polarFactor x' *
        (weightPoly A.lowOrder A.highOrder z.1 * axisFactor x' * A.polar.evalHalf z.1 x')) z.2) =
        fun z => deriv polarFactor z.2 *
            (weightPoly A.lowOrder A.highOrder z.1 * axisFactor z.2 * A.polar.evalHalf z.1 z.2) +
          polarFactor z.2 * (weightPoly A.lowOrder A.highOrder z.1 * deriv axisFactor z.2 * A.polar.evalHalf z.1 z.2 +
            weightPoly A.lowOrder A.highOrder z.1 * axisFactor z.2 * (xDerivSpline A.polar).evalHalf z.1 z.2) := by
      funext z
      exact ((hq z.2).hasDerivAt.mul ((((ha z.2).hasDerivAt).const_mul (weightPoly A.lowOrder A.highOrder z.1)).mul
        (spline_hasDerivAt_x hsm hB (by norm_num) (by norm_num) z.1 z.2))).deriv
    rw [e]
    exact (qdf.mul U1).add (qf.mul (((wf.mul adf).mul (dB (t, x))).add ((wf.mul af).mul (dBx (t, x)))))
  have hs : DifferentiableAt ℝ (fun z : ℝ × ℝ => phaseSlope P z.1) (t, x) :=
    fst_differentiableAt (phaseSlope_differentiableAt hP ht)
  have hs' : DifferentiableAt ℝ (fun z : ℝ × ℝ =>
      Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P z.1 : ℝ) : ℂ)) (t, x) :=
    (differentiableAt_const _).mul (Complex.ofRealCLM.differentiableAt.comp (t, x) (hs.const_mul _))
  have hr : DifferentiableAt ℝ (fun z : ℝ × ℝ => ((z.1 * (1 - z.1) : ℝ) : ℂ)) (t, x) :=
    fst_differentiableAt (g := fun s : ℝ => ((s * (1 - s) : ℝ) : ℂ))
      ((Complex.ofRealCLM.differentiable.comp (by fun_prop : Differentiable ℝ fun s : ℝ => s * (1 - s))) t)
  fin_cases c
  · simp only [reducedComps, if_neg h]
    exact U0
  · simp only [reducedComps, if_neg h]
    exact U1
  · simp only [reducedComps, if_neg h, shiftedScale, radialScale, heightDeriv]
    exact (differentiableAt_const _).mul ((((hr.mul D1).add (hs'.mul U0)).add
      ((differentiableAt_const _).mul U0)).sub D2)

end Internal

def FramedDivergenceFormula : Prop :=
  ∀ (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (U : ℝ → ℝ → Fin 3 → ℂ) (y : Space), IsShapeParams P → y 1 ≠ 0 →
    (∀ c, DifferentiableAt ℝ (fun z : ℝ × ℝ => U z.1 z.2 c) (chartCoord P y, heightRatio y)) →
    complexDivergence (fun z i => keyPhase P κ σ z *
      (U (chartCoord P z) (heightRatio z) 0 * (radialVec z i : ℂ) +
        U (chartCoord P z) (heightRatio z) 1 * (polarVecQ z i : ℂ) +
        U (chartCoord P z) (heightRatio z) 2 * (azimVecQ z i : ℂ))) y =
      keyPhase P κ σ y / (‖y‖ : ℂ) *
        (shiftedScale P κ.phaseIndex (fun t x => U t x 0) (chartCoord P y) (heightRatio y) +
          2 * U (chartCoord P y) (heightRatio y) 0 -
          heightDeriv (fun t x => polarFactor x * U t x 1) (chartCoord P y) (heightRatio y) +
          Complex.I * (labelAzimuth P.azimuthOrder κ.label : ℂ) * U (chartCoord P y) (heightRatio y) 2)

theorem keyDivergenceFree_of (hdiv : FramedDivergenceFormula) (hsm : JoinedSplineSmooth)
    (h1 : TypeOneKeySmooth) (h2 : TypeTwoKeySmooth) : KeyDivergenceFree := by
  intro P D κ σ y hP hD hκ
  have hf : ContDiff ℝ 1 (keyVector P κ (D.amp κ) σ) := by
    by_cases h : κ.label.1 = 0
    · exact (h2 P D κ σ hP hD hκ h).smooth
    · exact (h1 P D κ σ hP hD hκ h).smooth
  refine Internal.divergence_of_dense hf (fun y hy => ?_) y
  have ht : chartCoord P y < 1 := by
    unfold chartCoord
    rw [div_lt_one (by positivity [hP.chartLength_pos])]
    linarith [hP.chartLength_pos]
  have hU : ∀ c, DifferentiableAt ℝ (fun z : ℝ × ℝ => reducedComps P κ (D.amp κ) z.1 z.2 c)
      (chartCoord P y, heightRatio y) := by
    intro c
    by_cases h : κ.label.1 = 0
    · exact Internal.typeTwo_components_differentiableAt hsm hP h (hD.stream_class κ hκ h)
        (hD.swirl_class κ hκ h) ht c
    · exact Internal.typeOne_components_differentiableAt hsm hP h (hD.radial_class κ hκ h)
        (hD.polar_class κ hκ h) ht c
  refine (hdiv P κ σ (reducedComps P κ (D.amp κ)) y hP hy hU).trans ?_
  by_cases h : κ.label.1 = 0
  · rw [Internal.typeTwo_reduced_cancel P κ (D.amp κ) h
      (Internal.typeTwo_product_contDiffAt hsm hP (hD.stream_class κ hκ h) ht), mul_zero]
  · rw [Internal.typeOne_reduced_cancel P hP κ (D.amp κ) h, mul_zero]

end GivenShape

end CertCell

end Breakdown
