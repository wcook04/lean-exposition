import Breakdown.Weak.StatementsOrbit
import Breakdown.Profile.Orbit

open MeasureTheory Set Real Filter
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

private theorem pushForward_ae_congr (R : Space ≃ₗᵢ[ℝ] Space) {f g : Space → Space}
    (h : f =ᵐ[volume] g) : pushForward R f =ᵐ[volume] pushForward R g := by
  have hq := (LinearIsometryEquiv.measurePreserving R.symm).quasiMeasurePreserving
  have h2 : (f ∘ R.symm) =ᵐ[volume] (g ∘ R.symm) := h.comp_tendsto hq.tendsto_ae
  filter_upwards [h2] with y hy
  simp only [Function.comp] at hy
  simp only [pushForward, hy]

private theorem eq_of_velocity_ae {a b : X}
    (h : (velocity a : Space → Space) =ᵐ[volume] (velocity b : Space → Space)) : a = b := by
  have h0 : (velocity (a - b) : Space → Space) =ᵐ[volume] 0 := by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (velocity a) (velocity b), h] with y h1 h2
    rw [h1, Pi.sub_apply, h2, sub_self, Pi.zero_apply]
  exact sub_eq_zero.mp (velocityInjective_holds _ h0)

private theorem isMildX_congr {u z : ℝ → X} {a b : ℝ} (h : EqOn u z (Icc a b))
    (hz : IsMildX z a b) : IsMildX u a b := by
  refine ⟨hz.1.congr h, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hz.2 t ht
  have hq : EqOn (fun s => bilinX (t - s) (u s) (u s)) (fun s => bilinX (t - s) (z s) (z s))
      (uIcc a t) := by
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have e : u s = z s := h ⟨hs.1, hs.2.trans ht.2⟩
    simp only [e]
  have e1 : (∫ s in a..t, bilinX (t - s) (u s) (u s)) = ∫ s in a..t, bilinX (t - s) (z s) (z s) :=
    intervalIntegral.integral_congr hq
  have e2 : u t = z t := h ht
  have e3 : u a = z a := h ⟨le_rfl, ht.1.trans ht.2⟩
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff] at h1 ⊢
    exact h1.congr_fun (fun s hs => (hq (uIoc_subset_uIcc hs)).symm) measurableSet_uIoc
  · exact e2.trans (h2.trans (congrArg₂ HAdd.hAdd (congrArg (heatX (t - a)) e3.symm) e1.symm))

private theorem physicalCurve_bound {x : ℝ → X} {M : ℝ} (hM : ∀ s, ‖x s‖ ≤ M) (s₀ r : ℝ)
    (hr : r < 1) : ∀ t ∈ Ioo (-1) r, ‖physicalCurve x s₀ t‖ ≤ ((1 - r)⁻¹) ^ (1 / 4 : ℝ) * M := by
  intro t ht
  have h1 : 0 < 1 - t := by linarith [ht.2]
  have h2 : 0 < 1 - r := by linarith
  unfold physicalCurve
  rw [dilation_holds.1 _ (inv_pos.mpr h1)]
  apply mul_le_mul _ (hM _) (norm_nonneg _) (by positivity)
  exact Real.rpow_le_rpow (by positivity) (inv_anti₀ h2 (by linarith [ht.2])) (by norm_num)

private theorem exp_timeChange (s₀ t : ℝ) (ht : t < 1) :
    exp (-((s₀ - Real.log (1 - t)) - s₀)) = 1 - t := by
  rw [show -((s₀ - Real.log (1 - t)) - s₀) = Real.log (1 - t) by ring, Real.exp_log (by linarith)]

private theorem dilX_inv_cancel {μ : ℝ} (hμ : 0 < μ) (v : X) : dilX μ (dilX μ⁻¹ v) = v := by
  have h := dilation_holds.2.2.1 μ μ⁻¹ hμ (inv_pos.mpr hμ)
  rw [mul_inv_cancel₀ hμ.ne', dilation_holds.2.1] at h
  have h' := congrArg (fun T : X →L[ℝ] X => T v) h
  simpa using h'.symm

private theorem dilX_joint : ContinuousOn (fun p : ℝ × X => dilX p.1 p.2) (Ioi 0 ×ˢ univ) :=
  dilateJointContinuous_holds X realization.F

private theorem dilX_comp_continuousOn {S : Set ℝ} {f : ℝ → ℝ} {g : ℝ → X}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S) (hpos : ∀ σ ∈ S, 0 < f σ) :
    ContinuousOn (fun σ => dilX (f σ) (g σ)) S :=
  dilX_joint.comp (hf.prodMk hg) (fun σ hσ => ⟨hpos σ hσ, mem_univ _⟩)

private theorem localMild (hDBR : ConstOfWeakDeriv) (hGT : GoodTimes) (hBI : BilinIntegrable)
    (hDI : VarConstInner) (hDG : VarConstGood) (hCD : ContinuousVarConst) (hMG : MildFromGood)
    (hPCM : PhysicalCurveMeasurable) {x : ℝ → X} {M : ℝ} (hM : ∀ s, ‖x s‖ ≤ M)
    (hxm : AEStronglyMeasurable x volume)
    (hphys : ∀ s₀, IsTensorWeak (physicalCurve x s₀) (-1) 1)
    (s₀ r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ t₀ : ℝ, -1 < t₀ ∧ t₀ < 0 ∧ ∃ z : ℝ → X, ContinuousOn z (Ico t₀ r) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo t₀ r)), z t = physicalCurve x s₀ t) ∧
      ∀ a b, t₀ ≤ a → a < b → b < r → IsMildX z a b := by
  have hb := physicalCurve_bound hM s₀ r hr1
  have hm : AEStronglyMeasurable (physicalCurve x s₀) (volume.restrict (Ioo (-1) r)) :=
    (hPCM s₀ x hxm).mono_set (fun t ht => show t < 1 from ht.2.trans hr1)
  have hw : IsTensorWeak (physicalCurve x s₀) (-1) r := fun θ φ h1 h2 h3 h4 =>
    hphys s₀ θ φ h1 h2 (h3.trans (Ioo_subset_Ioo_right hr1.le)) h4
  obtain ⟨E, hE⟩ := hGT hDBR _ (-1) r _ (by linarith) hb hm hw
  have hex : ∃ t₀ ∈ E, t₀ < 0 := by
    by_contra hne
    push Not at hne
    have hsub : Ioo (-1 : ℝ) 0 ⊆ Ioo (-1) r \ E := fun t ht =>
      ⟨⟨ht.1, ht.2.trans hr0⟩, fun htE => absurd (hne t htE) (not_le.mpr ht.2)⟩
    have h0 := measure_mono_null hsub hE.null
    rw [Real.volume_Ioo] at h0
    norm_num at h0
  obtain ⟨t₀, ht₀E, ht₀0⟩ := hex
  have ht₀ : t₀ ∈ Ioo (-1) r := hE.sub ht₀E
  have hcont := hCD hBI _ (-1) r _ hb hm t₀ ht₀
  have hgood : ∀ t ∈ E, t₀ ≤ t → varConst (physicalCurve x s₀) t₀ t = physicalCurve x s₀ t :=
    fun t ht htt => hDG hBI hDI _ (-1) r _ E hb hm hE t₀ ht₀E t ht htt
  refine ⟨t₀, ht₀.1, ht₀0, varConst (physicalCurve x s₀) t₀, hcont, ?_,
    hMG hBI _ (-1) r _ t₀ E hb hm hE.sub hE.null ht₀ hcont hgood⟩
  rw [ae_restrict_iff' measurableSet_Ioo]
  apply ae_iff.mpr
  apply measure_mono_null _ hE.null
  intro t ht
  simp only [mem_ofPred_eq, Classical.not_imp] at ht
  exact ⟨⟨ht₀.1.trans ht.1.1, ht.1.2⟩, fun htE => ht.2 (hgood t htE ht.1.1.le)⟩

private theorem representative {x : ℝ → X} (hTCN : TimeChangeNull)
    (hloc : ∀ s₀ r : ℝ, 0 < r → r < 1 → ∃ t₀ : ℝ, -1 < t₀ ∧ t₀ < 0 ∧ ∃ z : ℝ → X,
      ContinuousOn z (Ico t₀ r) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo t₀ r)), z t = physicalCurve x s₀ t) ∧
      ∀ a b, t₀ ≤ a → a < b → b < r → IsMildX z a b)
    (a b : ℝ) : ∃ c : ℝ → X, ContinuousOn c (Ioo a b) ∧
      ∀ᵐ σ ∂(volume.restrict (Ioo a b)), c σ = x σ := by
  by_cases hab : a < b
  swap
  · refine ⟨x, ?_, ae_of_all _ (fun _ => rfl)⟩
    rw [Ioo_eq_empty hab]
    exact continuousOn_empty _
  have hr0 : 0 < 1 - exp (-(b - a + 2)) := by
    have : exp (-(b - a + 2)) < exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hr1 : 1 - exp (-(b - a + 2)) < 1 := by linarith [Real.exp_pos (-(b - a + 2))]
  obtain ⟨t₀, ht₀1, ht₀0, z, hzc, hza, -⟩ := hloc (a - 1) _ hr0 hr1
  refine ⟨fun σ => dilX (exp (-(σ - (a - 1)))) (z (1 - exp (-(σ - (a - 1))))), ?_, ?_⟩
  · apply dilX_comp_continuousOn
    · exact (by fun_prop : Continuous fun σ : ℝ => exp (-(σ - (a - 1)))).continuousOn
    · refine hzc.comp (by fun_prop : Continuous fun σ : ℝ => 1 - exp (-(σ - (a - 1)))).continuousOn ?_
      intro σ hσ
      constructor
      · have : exp (-(σ - (a - 1))) < exp 0 := Real.exp_lt_exp.mpr (by linarith [hσ.1])
        rw [Real.exp_zero] at this
        linarith
      · have : exp (-(b - a + 2)) < exp (-(σ - (a - 1))) := Real.exp_lt_exp.mpr (by linarith [hσ.2])
        linarith
    · intro σ _
      exact Real.exp_pos _
  · rw [ae_restrict_iff' measurableSet_Ioo]
    apply (hTCN (a - 1) (fun σ => σ ∈ Ioo a b →
      dilX (exp (-(σ - (a - 1)))) (z (1 - exp (-(σ - (a - 1))))) = x σ)).mpr
    have hza' := (ae_restrict_iff' measurableSet_Ioo).mp hza
    rw [ae_restrict_iff' measurableSet_Iio]
    filter_upwards [hza'] with t ht ht1 hσ
    have ht1' : t < 1 := ht1
    have h1t : 0 < 1 - t := by linarith
    have e := Real.exp_log h1t
    have ht0 : 0 < t := by
      have : exp (Real.log (1 - t)) < exp 0 := Real.exp_lt_exp.mpr (by linarith [hσ.1])
      rw [e, Real.exp_zero] at this
      linarith
    have htr : t < 1 - exp (-(b - a + 2)) := by
      have : exp (-(b - a + 2)) < exp (Real.log (1 - t)) := Real.exp_lt_exp.mpr (by linarith [hσ.2])
      rw [e] at this
      linarith
    rw [exp_timeChange (a - 1) t ht1', sub_sub_cancel, ht ⟨by linarith, htr⟩]
    exact dilX_inv_cancel h1t _

theorem weakOrbitOfParts_holds : WeakOrbitOfParts := by
  intro hPV hVWG hZG hGF hSE hAdv hPD hTD hSM hSTF hSInt hSI hPI hDBR hGT hBI hDI hDG hCD hMG
    hGR hTCN hPCM hex
  obtain ⟨W, G, H, P, R, C, hP, hWm, hGm, hHm, hper, hgrad, hHgrad, hdiv, hsix, htwo, hHint,
    hweak, hne⟩ := hex
  have hslice : ∀ s, IsSlice (W s) (G s) C := fun s => ⟨hgrad s, hdiv s, hsix s, htwo s⟩
  choose x hxv hxp hxn using fun s => hSE hPV hVWG hZG hGF (W s) (G s) C (hslice s)
  have hx : IsSliceCurve x W G (Real.sqrt (3 * max C 0)) := ⟨hxv, hxp, fun s => by
    have h := Real.abs_le_sqrt (hxn s)
    rwa [abs_of_nonneg (norm_nonneg _)] at h⟩
  have hxm : AEStronglyMeasurable x volume := hSM hPV x W G _ hx hWm
  have hsim := hSI hSInt hSTF hPV hAdv x W G _ C hx hslice hweak
  have hphys : ∀ s₀, IsTensorWeak (physicalCurve x s₀) (-1) 1 := fun s₀ =>
    hPI hPD hTD x _ s₀ hx.bound hxm (fun α φ h1 h2 h3 => hsim α s₀ φ h1 h2 h3)
  have hloc := fun s₀ r hr0 hr1 =>
    localMild hDBR hGT hBI hDI hDG hCD hMG hPCM hx.bound hxm hphys s₀ r hr0 hr1
  obtain ⟨w, hwc, hwx⟩ := hGR x (fun a b _ => representative hTCN hloc a b)
  have hxper : ∀ s, x (s + P) = rotX R (x s) := by
    intro s
    apply eq_of_velocity_ae
    have hWP : W (s + P) = pushForward R (W s) := funext (hper s)
    have h1 := hx.vel (s + P)
    rw [hWP] at h1
    exact h1.trans ((pushForward_ae_congr R (hx.vel s).symm).trans
      (velocityCov_holds.1 R (x s)).symm)
  refine ⟨w, P, R, ⟨hwc, ?_, hP, ?_, ?_⟩⟩
  · by_contra hzero
    push Not at hzero
    have hx0 : ∀ᵐ s, x s = 0 := by
      filter_upwards [hwx] with s hs
      rw [← hs, hzero s]
    have hW0 : ∀ᵐ s, ∀ᵐ y, W s y = 0 := by
      filter_upwards [hx0] with s hs
      have h0 := hx.vel s
      rw [hs, map_zero] at h0
      filter_upwards [h0, Lp.coeFn_zero Space 6 (volume : Measure Space)] with y h1 h2
      rw [← h1, h2]
      rfl
    apply hne
    have hWe : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Space)),
        W z.1 z.2 = hWm.mk _ z := hWm.ae_eq_mk
    have hWe' := Measure.ae_ae_of_ae_prod hWe
    show ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Space)), W z.1 z.2 = 0
    have hmeas : MeasurableSet {z : ℝ × Space | hWm.mk _ z = 0} :=
      measurableSet_eq_fun hWm.stronglyMeasurable_mk.measurable measurable_const
    have hF0 : ∀ᵐ z ∂(volume.prod volume), hWm.mk _ z = (0 : Space) := by
      rw [Measure.ae_prod_iff_ae_ae hmeas]
      filter_upwards [hWe', hW0] with s h1 h2
      filter_upwards [h1, h2] with y h3 h4
      rw [← h3, h4]
    filter_upwards [hWe, hF0] with z h1 h2
    rw [h1, h2]
  · have hae : (fun s => w (s + P)) =ᵐ[volume] fun s => rotX R (w s) := by
      have hsh : (fun s => w (s + P)) =ᵐ[volume] fun s => x (s + P) :=
        (show w =ᵐ[volume] x from hwx).comp_tendsto
          (measurePreserving_add_right volume P).quasiMeasurePreserving.tendsto_ae
      filter_upwards [hsh, hwx] with s h1 h2
      rw [h1, hxper, h2]
    have hfun := ((hwc.comp (continuous_add_const P)).ae_eq_iff_eq volume
      ((rotX R).continuous.comp hwc)).mp hae
    intro s
    exact congrFun hfun s
  · intro s' s hss
    rcases eq_or_lt_of_le hss with heq | hlt
    · subst heq
      refine ⟨IntervalIntegrable.refl, ?_⟩
      simp [MildFramework.S, realization.F.D_one, realization.F.G_zero]
    · have hT0 : 0 < 1 - exp (-(s - s')) := by
        have : exp (-(s - s')) < exp 0 := Real.exp_lt_exp.mpr (by linarith)
        rw [Real.exp_zero] at this
        linarith
      have hT1 : 1 - exp (-(s - s')) < 1 := by linarith [Real.exp_pos (-(s - s'))]
      obtain ⟨t₀, ht₀1, ht₀0, z, hzc, hza, hzm⟩ :=
        hloc s' ((1 + (1 - exp (-(s - s')))) / 2) (by linarith) (by linarith)
      have hsub : Ioo t₀ ((1 + (1 - exp (-(s - s')))) / 2) ⊆ Iio 1 :=
        fun t ht => show t < 1 by linarith [ht.2]
      have hucont : ContinuousOn (fun t => dilX (1 - t)⁻¹ (w (s' - Real.log (1 - t))))
          (Ioo t₀ ((1 + (1 - exp (-(s - s')))) / 2)) := by
        have hne : ∀ t ∈ Ioo t₀ ((1 + (1 - exp (-(s - s')))) / 2), 1 - t ≠ 0 :=
          fun t ht => by linarith [ht.2]
        apply dilX_comp_continuousOn
        · exact (continuousOn_const.sub continuousOn_id).inv₀ hne
        · exact hwc.comp_continuousOn
            (continuousOn_const.sub ((continuousOn_const.sub continuousOn_id).log hne))
        · intro t ht
          exact inv_pos.mpr (by linarith [ht.2])
      have hw' := ae_restrict_of_ae_restrict_of_subset hsub
        ((hTCN s' (fun σ => w σ = x σ)).mp hwx)
      have hae : (fun t => dilX (1 - t)⁻¹ (w (s' - Real.log (1 - t)))) =ᵐ[volume.restrict
          (Ioo t₀ ((1 + (1 - exp (-(s - s')))) / 2))] z := by
        filter_upwards [hza, hw'] with t h1 h2
        rw [h1]
        unfold physicalCurve
        rw [h2]
      have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hucont (hzc.mono Ioo_subset_Ico_self)
      have hmild : IsMildX (fun t => dilX (1 - t)⁻¹ (w (s' - Real.log (1 - t)))) 0
          (1 - exp (-(s - s'))) :=
        isMildX_congr (fun t ht => heq ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          (hzm 0 _ ht₀0.le hT0 (by linarith))
      exact flowOfMild_unconditional X realization.F w _ s' s hlt hmild (fun r _ => rfl)

end Breakdown.WeakProfile
