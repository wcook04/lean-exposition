import Breakdown.FracCell.GivenToolkit

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace FieldJoint

open CellCert.GivenFields SteadyCert

def SmoothNear (f : ℝ → ℝ → ℂ) (p : ℝ × ℝ) : Prop :=
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => f q.1 q.2) U

theorem smoothNear_add {f g : ℝ → ℝ → ℂ} {p : ℝ × ℝ} (hf : SmoothNear f p) (hg : SmoothNear g p) :
    SmoothNear (fun t x => f t x + g t x) p := by
  obtain ⟨U, hU, hpU, hfU⟩ := hf
  obtain ⟨V, hV, hpV, hgV⟩ := hg
  exact ⟨U ∩ V, hU.inter hV, ⟨hpU, hpV⟩,
    (hfU.mono Set.inter_subset_left).add (hgV.mono Set.inter_subset_right)⟩

theorem smoothNear_mul {f g : ℝ → ℝ → ℂ} {p : ℝ × ℝ} (hf : SmoothNear f p) (hg : SmoothNear g p) :
    SmoothNear (fun t x => f t x * g t x) p := by
  obtain ⟨U, hU, hpU, hfU⟩ := hf
  obtain ⟨V, hV, hpV, hgV⟩ := hg
  exact ⟨U ∩ V, hU.inter hV, ⟨hpU, hpV⟩,
    (hfU.mono Set.inter_subset_left).mul (hgV.mono Set.inter_subset_right)⟩

theorem smoothNear_smooth {f : ℝ → ℝ → ℂ} {p : ℝ × ℝ} (hf : ContDiff ℝ ∞ (fun q : ℝ × ℝ => f q.1 q.2)) :
    SmoothNear f p :=
  ⟨Set.univ, isOpen_univ, Set.mem_univ _, hf.contDiffOn⟩

theorem smoothNear_derivT {f : ℝ → ℝ → ℂ} {p : ℝ × ℝ} (hf : SmoothNear f p) :
    SmoothNear (fun t x => deriv (fun t' => f t' x) t) p := by
  obtain ⟨U, hU, hpU, hfU⟩ := hf
  refine ⟨U, hU, hpU, ?_⟩
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) q ((1 : ℝ), (0 : ℝ))) U :=
    (hfU.fderiv_of_isOpen hU le_rfl).clm_apply contDiffOn_const
  refine h1.congr fun q hq => ?_
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => f q.1 q.2) q :=
    (hfU.differentiableOn (by simp) q hq).differentiableAt (hU.mem_nhds hq)
  have hc : HasDerivAt (fun t' : ℝ => ((t', q.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  have hcomp := (show HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2) (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) ((q.1, q.2) : ℝ × ℝ)) ((q.1, q.2) : ℝ × ℝ) from hd.hasFDerivAt).comp_hasDerivAt q.1 hc
  exact hcomp.deriv

theorem smoothNear_derivX {f : ℝ → ℝ → ℂ} {p : ℝ × ℝ} (hf : SmoothNear f p) :
    SmoothNear (fun t x => deriv (fun x' => f t x') x) p := by
  obtain ⟨U, hU, hpU, hfU⟩ := hf
  refine ⟨U, hU, hpU, ?_⟩
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) q ((0 : ℝ), (1 : ℝ))) U :=
    (hfU.fderiv_of_isOpen hU le_rfl).clm_apply contDiffOn_const
  refine h1.congr fun q hq => ?_
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => f q.1 q.2) q :=
    (hfU.differentiableOn (by simp) q hq).differentiableAt (hU.mem_nhds hq)
  have hc : HasDerivAt (fun x' : ℝ => ((q.1, x') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have hcomp := (show HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2) (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) ((q.1, q.2) : ℝ × ℝ)) ((q.1, q.2) : ℝ × ℝ) from hd.hasFDerivAt).comp_hasDerivAt q.2 hc
  exact hcomp.deriv

theorem smoothNear_spline (S : Spline) (odd : Bool) {t x : ℝ} (ht : t ∉ S.mesh.tBreaks)
    (hx : |x| ∉ S.mesh.xBreaks) (hx0 : x ≠ 0) : SmoothNear (fun t' x' => S.eval odd t' x') (t, x) := by
  obtain ⟨Q, hQ, hev⟩ := spline_eventually_poly S odd t x ht hx hx0
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.1 hev
  exact ⟨U, hU, hpU, hQ.contDiffOn.congr fun z hz => hUsub hz⟩

theorem smoothNear_contDiffAt {f : ℝ → ℝ → ℂ} {t x : ℝ} (hf : SmoothNear f (t, x)) (β : ℝ) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => f q.2.1 q.2.2) (β, t, x) := by
  obtain ⟨U, hU, hpU, hfU⟩ := hf
  have h : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => f q.1 q.2) (t, x) := hfU.contDiffAt (hU.mem_nhds hpU)
  exact h.comp (β, t, x) contDiffAt_snd


theorem ofReal_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ} {z : E}
    (hg : ContDiffAt ℝ ∞ g z) : ContDiffAt ℝ ∞ (fun w => (g w : ℂ)) z :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp z hg

theorem coreRatio_contDiffAt (P : ChartParams) (hP : IsChartParams P) (q0 : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => coreRatioT P q.2.1) q0 := by
  unfold coreRatioT
  have hden : P.L0 ^ 2 * q0.2.1 ^ 2 + P.rc ^ 2 * (1 - q0.2.1) ^ 2 ≠ 0 := by
    have h1 := hP.L0_pos
    have h2 := hP.rc_pos
    by_cases h : q0.2.1 = 0
    · rw [h]; simp; positivity
    · have : 0 < P.L0 ^ 2 * q0.2.1 ^ 2 := by positivity
      positivity
  exact ContDiffAt.div (by fun_prop) (by fun_prop) hden

theorem twisted_contDiffAt (P : ChartParams) (hP : IsChartParams P) (n : ℤ) {f : ℝ → ℝ → ℂ} {t x : ℝ}
    (hf : SmoothNear f (t, x)) (β0 : ℝ) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => twistedScale P n q.1 f q.2.1 q.2.2) (β0, t, x) := by
  unfold twistedScale radialScale
  have h1 := smoothNear_contDiffAt hf β0
  have h2 := smoothNear_contDiffAt (smoothNear_derivT hf) β0
  have h3 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => ((q.2.1 * (1 - q.2.1) : ℝ) : ℂ)) (β0, t, x) :=
    ofReal_contDiffAt (by fun_prop)
  have h4 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => (((n : ℝ) * q.1 * coreRatioT P q.2.1 : ℝ) : ℂ)) (β0, t, x) :=
    ofReal_contDiffAt ((contDiffAt_const.mul contDiffAt_fst).mul (coreRatio_contDiffAt P hP _))
  have h5 : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => ((2 * P.eps * q.2.1 : ℝ) : ℂ)) (β0, t, x) :=
    ofReal_contDiffAt (by fun_prop)
  exact (h3.mul h2).add (((contDiffAt_const.mul h4).sub h5).mul h1)

theorem smoothNear_real {g : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hg : ContDiff ℝ ∞ (fun q : ℝ × ℝ => g q.1 q.2)) :
    SmoothNear (fun t x => ((g t x : ℝ) : ℂ)) p :=
  smoothNear_smooth (Complex.ofRealCLM.contDiff.comp hg)

theorem smoothNear_pow {f : ℝ → ℝ → ℂ} {p : ℝ × ℝ} (hf : SmoothNear f p) (k : ℕ) :
    SmoothNear (fun t x => f t x ^ k) p := by
  obtain ⟨U, hU, hpU, hfU⟩ := hf
  exact ⟨U, hU, hpU, hfU.pow k⟩

theorem reduced_contDiffAt (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (n : ℤ) {t x : ℝ}
    (hx0 : x ≠ 0)
    (hgen : ∀ S ∈ [(D.amp n).radialAmp, (D.amp n).polarAmp, (D.amp n).streamAmp, (D.amp n).swirlAmp],
      t ∉ S.mesh.tBreaks ∧ |x| ∉ S.mesh.xBreaks)
    (β0 : ℝ) (k : Fin 3) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => reducedField P D n q.1 q.2.1 q.2.2 k) (β0, t, x) := by
  have hr := hgen (D.amp n).radialAmp (by simp)
  have hpo := hgen (D.amp n).polarAmp (by simp)
  have hs := hgen (D.amp n).streamAmp (by simp)
  have hw := hgen (D.amp n).swirlAmp (by simp)
  have hq : SmoothNear (fun _ x' => ((1 - x' ^ 2 : ℝ) : ℂ)) (t, x) := smoothNear_real (g := fun _ x' => 1 - x' ^ 2) (by fun_prop)
  by_cases hn : n = 0
  · subst hn
    let p : ℝ → ℂ := fun t' => weightPoly 1 D.highOrder t'
    have hp : SmoothNear (fun t' _ => p t') (t, x) := by
      unfold p weightPoly
      exact smoothNear_real (g := fun t' _ => t' ^ 1 * (1 - t') ^ D.highOrder) (by fun_prop)
    have hΨ := smoothNear_spline (D.amp 0).streamAmp true hs.1 hs.2 hx0
    have hG := smoothNear_spline (D.amp 0).swirlAmp false hw.1 hw.2 hx0
    have hpΨ : SmoothNear (fun t' x' => p t' * (D.amp 0).streamAmp.eval true t' x') (t, x) := smoothNear_mul hp hΨ
    have hqΨ : SmoothNear (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') (t, x) :=
      smoothNear_mul hq hΨ
    fin_cases k
    · have key : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => -(p q.2.1 * heightDeriv
          (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') q.2.1 q.2.2)) (β0, t, x) :=
        ((smoothNear_contDiffAt hp β0).mul (smoothNear_contDiffAt (smoothNear_derivX hqΨ) β0)).neg
      exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [reducedField]; rfl)
    · have key : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => -(twistedScale P 0 q.1
          (fun t' x' => p t' * (D.amp 0).streamAmp.eval true t' x') q.2.1 q.2.2 +
            2 * (p q.2.1 * (D.amp 0).streamAmp.eval true q.2.1 q.2.2))) (β0, t, x) :=
        ((twisted_contDiffAt P hP 0 hpΨ β0).add (contDiffAt_const.mul (smoothNear_contDiffAt hpΨ β0))).neg
      exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [reducedField]; rfl)
    · have key : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => p q.2.1 * (D.amp 0).swirlAmp.eval false q.2.1 q.2.2) (β0, t, x) :=
        smoothNear_contDiffAt (smoothNear_mul hp hG) β0
      exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [reducedField]; rfl)
  · let p : ℝ → ℂ := fun t' => weightPoly (D.lowOrder n) D.highOrder t'
    have hp : SmoothNear (fun t' _ => p t') (t, x) := by
      unfold p weightPoly
      exact smoothNear_real (g := fun t' _ => t' ^ D.lowOrder n * (1 - t') ^ D.highOrder) (by fun_prop)
    let ur : ℝ → ℝ → ℂ := fun t' x' => p t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
      (D.amp n).radialAmp.eval false t' x'
    let uθ : ℝ → ℝ → ℂ := fun t' x' => p t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
      (D.amp n).polarAmp.eval true t' x'
    have hur : SmoothNear ur (t, x) :=
      smoothNear_mul (smoothNear_mul hp (smoothNear_pow hq _)) (smoothNear_spline _ false hr.1 hr.2 hx0)
    have huθ : SmoothNear uθ (t, x) :=
      smoothNear_mul (smoothNear_mul hp (smoothNear_pow hq _)) (smoothNear_spline _ true hpo.1 hpo.2 hx0)
    fin_cases k
    · exact (smoothNear_contDiffAt hur β0).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun q => by simp only [reducedField, if_neg hn]; rfl)
    · exact (smoothNear_contDiffAt huθ β0).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun q => by simp only [reducedField, if_neg hn]; rfl)
    · have key : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => (Complex.I / ((n * P.m : ℤ) : ℂ)) *
          (twistedScale P n q.1 ur q.2.1 q.2.2 + 2 * ur q.2.1 q.2.2 -
            heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * uθ t' x') q.2.1 q.2.2)) (β0, t, x) :=
        contDiffAt_const.mul (((twisted_contDiffAt P hP n hur β0).add
          (contDiffAt_const.mul (smoothNear_contDiffAt hur β0))).sub
            (smoothNear_contDiffAt (smoothNear_derivX (smoothNear_mul hq huθ)) β0))
      exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [reducedField, if_neg hn]; rfl)

theorem joint_fieldOf (P : ChartParams) (hP : IsChartParams P) (F : FieldData) {y : Space}
    (hy0 : y ≠ 0) (hy1 : y 1 ≠ 0) (hx0 : heightRatio y ≠ 0)
    (hgen : ∀ n ∈ F.modes, ∀ S ∈ [(F.amp n).radialAmp, (F.amp n).polarAmp, (F.amp n).streamAmp, (F.amp n).swirlAmp],
      chartT P y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks) (β0 : ℝ) :
    ContDiffAt ℝ ∞ (fun q : ℝ × Space => fieldOf P F q.1 q.2) (β0, y) := by
  have hc : ∀ j : Fin 3, ContDiffAt ℝ ∞ (fun z : Space => z j) y := fun j => contDiffAt_piLp_apply 2
  have hn : ContDiffAt ℝ ∞ (fun z : Space => ‖z‖) y := contDiffAt_norm ℝ hy0
  have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
  have hL := hP.L0_pos
  have hden : ‖y‖ + P.L0 ≠ 0 := by positivity
  have hT : ContDiffAt ℝ ∞ (fun z : Space => chartT P z) y := hn.div (hn.add contDiffAt_const) hden
  have hH : ContDiffAt ℝ ∞ (fun z : Space => heightRatio z) y := (hc 2).div hn hne
  have hS : chartS P y ≠ 0 := by
    unfold chartS chartT
    have : ‖y‖ / (‖y‖ + P.L0) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    linarith
  have hDec : ContDiffAt ℝ ∞ (fun z : Space => decayFactor P z) y :=
    (contDiffAt_const.sub hT).rpow_const_of_ne hS
  have hlogpos : 1 + ‖y‖ ^ 2 / P.rc ^ 2 ≠ 0 := by positivity
  have hLog : ContDiffAt ℝ ∞ (fun z : Space => logPhase P z) y :=
    contDiffAt_const.mul ((contDiffAt_const.add ((contDiff_norm_sq ℝ).contDiffAt.div_const _)).log hlogpos)
  have hslit : ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using hy1
  have hcpx : ContDiffAt ℝ ∞ (fun z : Space => ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)) y :=
    (ofReal_contDiffAt (hc 0)).add ((ofReal_contDiffAt (hc 1)).mul contDiffAt_const)
  have hA : ContDiffAt ℝ ∞ (fun z : Space => angleOf z) y := by
    have h1 : ContDiffAt ℝ ∞ (fun z : Space => Complex.imCLM (Complex.log ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I))) y :=
      Complex.imCLM.contDiff.contDiffAt.comp y
        (ContDiffAt.comp (f := fun z : Space => ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)) y ((Complex.contDiffAt_log hslit).restrict_scalars ℝ) hcpx)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp only [angleOf, Complex.imCLM_apply, Complex.log_im]
    rw [Complex.mk_eq_add_mul_I]
  have hrad : ∀ i, ContDiffAt ℝ ∞ (fun z : Space => radialVec z i) y := fun i => (hc i).div hn hne
  have hpol : ∀ i, ContDiffAt ℝ ∞ (fun z : Space => polarVecQ z i) y := by
    intro i
    fin_cases i
    · show ContDiffAt ℝ ∞ (fun z : Space => heightRatio z * z 0 / ‖z‖) y
      exact (hH.mul (hc 0)).div hn hne
    · show ContDiffAt ℝ ∞ (fun z : Space => heightRatio z * z 1 / ‖z‖) y
      exact (hH.mul (hc 1)).div hn hne
    · show ContDiffAt ℝ ∞ (fun z : Space => -(1 - heightRatio z ^ 2)) y
      exact (contDiffAt_const.sub (hH.pow 2)).neg
  have hazi : ∀ i, ContDiffAt ℝ ∞ (fun z : Space => azimVecQ z i) y := by
    intro i
    fin_cases i
    · show ContDiffAt ℝ ∞ (fun z : Space => -(z 1) / ‖z‖) y
      exact (hc 1).neg.div hn hne
    · show ContDiffAt ℝ ∞ (fun z : Space => z 0 / ‖z‖) y
      exact (hc 0).div hn hne
    · show ContDiffAt ℝ ∞ (fun _ : Space => (0 : ℝ)) y
      exact contDiffAt_const
  have hsnd : ∀ {g : Space → ℝ}, ContDiffAt ℝ ∞ g y →
      ContDiffAt ℝ ∞ (fun q : ℝ × Space => ((g q.2 : ℝ) : ℂ)) (β0, y) :=
    fun hg => ofReal_contDiffAt (hg.comp (β0, y) contDiffAt_snd)
  have hTH : ContDiffAt ℝ ∞ (fun q : ℝ × Space => (q.1, chartT P q.2, heightRatio q.2)) (β0, y) :=
    contDiffAt_fst.prodMk ((hT.comp (β0, y) contDiffAt_snd).prodMk (hH.comp (β0, y) contDiffAt_snd))
  have hR : ∀ n ∈ F.modes, ∀ k : Fin 3,
      ContDiffAt ℝ ∞ (fun q : ℝ × Space => reducedField P F n q.1 (chartT P q.2) (heightRatio q.2) k) (β0, y) :=
    fun n hn k => ContDiffAt.comp (f := fun q : ℝ × Space => (q.1, chartT P q.2, heightRatio q.2)) (β0, y) (reduced_contDiffAt P hP F n hx0 (hgen n hn) β0 k) hTH
  have hPh : ∀ n : ℤ, ContDiffAt ℝ ∞ (fun q : ℝ × Space => modePhase P n q.1 q.2) (β0, y) := by
    intro n
    have he : ContDiffAt ℝ ∞ (fun q : ℝ × Space =>
        Complex.I * (((((n * P.m : ℤ) : ℝ) * angleOf q.2 + n * q.1 * logPhase P q.2 : ℝ)) : ℂ)) (β0, y) :=
      contDiffAt_const.mul (ofReal_contDiffAt ((contDiffAt_const.mul (hA.comp (β0, y) contDiffAt_snd)).add
        ((contDiffAt_const.mul contDiffAt_fst).mul (hLog.comp (β0, y) contDiffAt_snd))))
    exact Complex.contDiff_exp.contDiffAt.comp (β0, y) he
  refine (contDiffAt_piLp 2).2 fun i => ?_
  simp only [fieldOf, ofComponents_apply]
  refine Complex.reCLM.contDiff.contDiffAt.comp (β0, y) ((hsnd hDec).mul (ContDiffAt.sum fun n hn => ?_))
  exact (hPh n).mul ((((hR n hn 0).mul (hsnd (hrad i))).add ((hR n hn 1).mul (hsnd (hpol i)))).add
    ((hR n hn 2).mul (hsnd (hazi i))))

end FieldJoint

end FracInternal

end Breakdown
