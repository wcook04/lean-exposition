import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.CertCell.LocalModeWeak
import Breakdown.CertCell.LocalModeIntegrableParts
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.CertCell.LocalFaceStrip
import Breakdown.FracCell.RadialMixedWeak
import Breakdown.FracCell.ModeRectIntegrable
import Breakdown.FracCell.StrainFaceHeightTurn
import Breakdown.FracCell.AngularHeightMode
import Breakdown.FracCell.CircleWeak

open scoped ContDiff
open MeasureTheory Set

open private Breakdown.CellCert.CellFormula.hbase from Breakdown.FracCell.StrainFaceHeightNormal
open private Breakdown.CellCert.CellFormula.StrainFaceHeightTurn.strip_turn from
  Breakdown.FracCell.StrainFaceHeightTurn

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula

section HeightAxis

open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem localModeHeightAxis : LocalModeHeightAxisStatement := by
  intro m v G H hs n a R Z
  set ρ : ℝ := 2 * |R| + |Z| + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hχ : IsTestScalar (radialCutoff ρ) := ⟨contDiff_radialCutoff hρ0, hasCompactSupport_radialCutoff hρ0⟩
  have hχ1 : ∀ y, |radialCutoff ρ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (radialCutoff_nonneg ρ y)]
    exact radialCutoff_le_one ρ y
  have h6 := Internal.cutoff_memLp_six hs hχ hχ1
  have hint : IntegrableOn _ (Icc 0 R ×ˢ Icc (-Z) Z) :=
    (Breakdown.FracInternal.ModeRectIntegrable.six_int R Z h6 (gradKernel m n a 2) (gradKernel_cont m n a 2)
      (gradKernel_bound m n a 2)).const_mul (1 / (2 * Real.pi) : ℂ)
  refine IntegrableOn.congr_fun hint (fun p hp => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  rw [gradMode_eq]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  have hn : ‖cylPoint p.1 θ p.2‖ ≤ ρ := by
    refine (cylPoint_norm _ _ _).trans ?_
    have h1 : |p.1| ≤ |R| := by
      rw [abs_of_nonneg hp.1.1]
      exact hp.1.2.trans (le_abs_self R)
    have h2 : |p.2| ≤ |Z| :=
      abs_le.2 ⟨by linarith [hp.2.1, le_abs_self Z, neg_abs_le Z], hp.2.2.trans (le_abs_self Z)⟩
    rw [hρ]
    linarith
  simp only [radialCutoff_eq_one hρ0 hn, one_smul]

end HeightAxis

private theorem axial_second_meas {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable H volume) : AEStronglyMeasurable (fun y => H y axialUnit) volume :=
  (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) axialUnit).continuous.comp_aestronglyMeasurable hH

private theorem axial_second_sq {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    Integrable (fun y => entrySq (H y axialUnit)) := by
  have hc : Continuous (fun M : Space →L[ℝ] Space => entrySq M) := by
    unfold entrySq
    fun_prop
  refine h2.mono' (hc.comp_aestronglyMeasurable (axial_second_meas hH)) (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ entrySq (H y axialUnit) := by
    unfold entrySq
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  show ∑ j : Fin 3, ‖H y (unitVector 2) (unitVector j)‖ ^ 2 ≤ _
  exact Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ 2)

private theorem modeThird_axial (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) :
    modeThird m n H a 0 2 = gradMode m n (fun y => H y axialUnit) a 0 := rfl

theorem localRadialMixedWeak : LocalRadialMixedWeakStatement := by
  intro K hK m v G H hs n a ψ hψ hψ1 hψ2 t ht
  have hm : AEStronglyMeasurable (fun y => H y axialUnit) volume := axial_second_meas hs.measurable_second
  have hq : Integrable (fun y => entrySq (H y axialUnit)) := axial_second_sq hs.measurable_second hs.second_two
  have hloc : LocallyIntegrable (fun y => H y axialUnit) volume :=
    (ModeRadialWeakInternal.grad_memLp hm hq).locallyIntegrable (by norm_num)
  have hF : ∀ R Z, IntegrableOn (gradMode m n G a 2) (Icc 0 R ×ˢ Icc (-Z) Z) :=
    fun R Z => localModeHeightAxis m v G H hs n a R Z
  have hg : ∀ R Z, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a 0 2 p)
      (Icc 0 R ×ˢ Icc (-Z) Z) := by
    intro R Z
    rw [modeThird_axial]
    exact ModeRadialWeakInternal.grad_on hloc n a R Z
  have hW : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ p ∈ tsupport φ, 0 < p.1) →
      ∫ p, ((fderiv ℝ φ p (1, 0) : ℝ) : ℂ) * gradMode m n G a 2 p =
        -∫ p, (φ p : ℂ) * modeThird m n H a 0 2 p :=
    fun φ h1 h2 h3 => (localModeWeakIdentity m v G H hs n a φ h1 h2 h3).2.2.1
  have h0 : 0 ≤ K.r₁ := hK.r_order.1
  have h12 : K.r₁ < K.r₂ := hK.r_order.2
  have hz0 : 0 ≤ K.z₁ := hK.z_order.1
  have hsub : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ := fun p hp =>
    ⟨⟨h0.trans hp.1.1, hp.1.2⟩, ⟨by linarith [hp.2.1, hp.2.2], hp.2.2⟩⟩
  have hFr : IntegrableOn (gradMode m n G a 2) K.rect := (hF K.r₂ K.z₂).mono_set hsub
  have hgr : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeThird m n H a 0 2 p) K.rect := by
    rw [modeThird_axial]
    exact LowEntry.Internal.gradMode_int K hK m n hm hq a 0
  have hgm : AEStronglyMeasurable (modeThird m n H a 0 2) (volume.restrict K.rect) := by
    rw [modeThird_axial]
    exact (ModeRadialWeakInternal.grad_meas hm n a K.r₂ K.z₂).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hwpos : ∀ r, 0 < r → 0 < K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs <;> linarith
  have hwn : ∀ r ∈ Icc K.r₁ K.r₂, 0 ≤ K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs <;> linarith [hr.1]
  have hwl : ∀ r ∈ Icc K.r₁ K.r₂, r - K.r₁ ≤ (1 + (K.r₂ - K.r₁)) * K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs with h
    · rw [h, sub_zero]
      have : 0 ≤ r := h0.trans hr.1
      nlinarith
    · linarith [hr.2]
  exact ModeRadialWeakInternal.rect_psi hF hg hW h0 h12 (LowEntry.Internal.lineWeight_cont K) hwpos hwn hwl
    hFr hgr hgm hψ hψ1 hψ2 ht

theorem localHeightNormal : LocalHeightNormalStatement := by
  intro k N c K S B L hL x hx n e a t he ht
  have hK : IsCellBox K := hL.box_valid
  have hs : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1 := hx.1
  obtain ⟨hV, hG0, hW1⟩ := localModeRadialWeak K hK L.order x.1 x.2.1 x.2.2.1 hs n a
  have hW2 := localRadialMixedWeak K hK L.order x.1 x.2.1 x.2.2.1 hs n a
  have hG2 : IntegrableOn (gradMode L.order n x.2.1 a 2) K.rect := by
    refine (localModeHeightAxis L.order x.1 x.2.1 x.2.2.1 hs n a K.r₂ K.z₂).mono_set ?_
    intro p hp
    simp only [CellBox.rect, Set.mem_prod, Set.mem_Icc] at hp ⊢
    exact ⟨⟨hK.r_order.1.trans hp.1.1, hp.1.2⟩, ⟨by linarith [hK.z_order.1, hp.2.1], hp.2.2⟩⟩
  have hS : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird L.order n x.2.2.1 a 0 2 p) K.rect :=
    LowEntry.Internal.gradMode_int K hK L.order n (axial_second_meas hs.measurable_second)
      (axial_second_sq hs.measurable_second hs.second_two) a 0
  have hbox : L.box = K := hL.box_eq
  have hz : K.z₁ < K.z₂ := hK.z_order.2
  have he4 := e.isLt
  have hlt : ¬ e.val < 2 := by omega
  rcases (show e.val = 2 ∨ e.val = 3 by omega) with h2 | h3
  · have hj : CellLayout.sideHeightIndex e = 0 := by simp [CellLayout.sideHeightIndex, h2]
    simp only [CellLayout.cornerValue, CellLayout.sideVelocityValue, heightFaceMoment, hj, hlt, hbox]
    simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_false, if_true]
    exact Breakdown.CellCert.CellFormula.hbase K hK K.z₁ K.z₂ hz.ne (min_eq_left hz.le) (max_eq_right hz.le)
      _ _ _ _ hV hG0 hG2 hS hW1 hW2 t ht
  · have hj : CellLayout.sideHeightIndex e = 1 := by simp [CellLayout.sideHeightIndex, h3]
    simp only [CellLayout.cornerValue, CellLayout.sideVelocityValue, heightFaceMoment, hj, hlt, hbox]
    simp only [Fin.isValue, one_ne_zero, if_false, if_true]
    exact Breakdown.CellCert.CellFormula.hbase K hK K.z₂ K.z₁ hz.ne' (min_eq_right hz.le) (max_eq_left hz.le)
      _ _ _ _ hV hG0 hG2 hS hW1 hW2 t ht

section AngularHeight

open CellEnergy CellEnergy.Internal.AngularFrame
open Breakdown.CellCert.CellFormula.Internal.AngularHeightMode
open Breakdown.SteadyCert.SecondTraceSolenoidalInternal

private theorem angularGradMode_comb {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hF : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      angularGradMode m n H a b p =
        ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' p := by
  have locG : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i =>
    locInt_vec (meas_G hF.measurable_gradient i) hF.gradient_two fun y => G_sq_le (G y) i
  have locH : ∀ j i, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume := fun j i =>
    locInt_vec (meas_H hF.measurable_second j i) hF.second_two fun y => H_sq_le (H y) j i
  have locf : ∀ i l, LocallyIntegrable (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) volume :=
    fun i l => locInt_sq ((meas_G hF.measurable_gradient i).inner aestronglyMeasurable_const)
      hF.gradient_two fun y => (inner_sq_le _ l).trans (G_sq_le (G y) i)
  have locs : ∀ j i l, LocallyIntegrable (fun y => inner ℝ (H y (unitVector j) (unitVector i)) (unitVector l))
      volume := fun j i l => locInt_sq ((meas_H hF.measurable_second j i).inner aestronglyMeasurable_const)
      hF.second_two fun y => (inner_sq_le _ l).trans (H_sq_le (H y) j i)
  have locg : ∀ i l, LocallyIntegrable (fun y => gv (H y) i l) volume := by
    intro i l
    unfold gv
    refine locallyIntegrable_finsetSum Finset.univ fun j _ => ?_
    exact locallyIntegrable_iff.2 fun K hK => ((locs j i l).integrableOn_isCompact hK).smul_const _
  have hweak : ∀ i l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l) =
        -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
    intro i l φ hφ j
    have hw := hF.weak_second φ hφ i j
    have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have hi1 := (locG i).integrable_smul_left_of_hasCompactSupport hcont hsupp
    have hi2 := (locH j i).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l)
        = ∫ y, L (fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [L, innerSL_apply_apply, real_inner_comm]
      _ = L (∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := L.integral_comp_comm hi1
      _ = -L (∫ y, φ y • H y (unitVector j) (unitVector i)) := by rw [hw, map_neg]
      _ = -∫ y, L (φ y • H y (unitVector j) (unitVector i)) := by rw [L.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gv_inner]
          simp [L, innerSL_apply_apply, real_inner_comm]
  have hKer := fun i l => circleWeak (fun y => inner ℝ (G y (unitVector i)) (unitVector l))
    (fun y => gv (H y) i l) (locf i l) (locg i l) (hweak i l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l => (hKer i l).1
  have hid := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
    (hKer i l).2 (wgt (azimuth m n) a b i l) (wgt_smooth _ a b i l) (hk ▸ wgt_periodic _ a b i l)
  filter_upwards [hint, hid] with p h1 h2 hr
  obtain ⟨r, z⟩ := p
  exact point m n G H a b r z (fun i l => (h1 i l hr).1) (fun i l => (h1 i l hr).2) (fun i l => h2 i l hr)

private theorem second_symm_ae {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) :
    ∀ᵐ y ∂volume, ∀ i j : Fin 3, H y (unitVector i) (unitVector j) = H y (unitVector j) (unitVector i) := by
  have hloc : ∀ i j : Fin 3, LocallyIntegrable (fun y => H y (unitVector i) (unitVector j)) volume :=
    fun i j => locInt_vec (meas_H hs.measurable_second i j) hs.second_two fun y => H_sq_le (H y) i j
  have key : ∀ i j : Fin 3, ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, φ y • H y (unitVector j) (unitVector i) = ∫ y, dirDeriv i (dirDeriv j φ) y • v y := by
    intro i j φ hφ
    have hG := hs.weak_gradient (dirDeriv j φ) (test_dirDeriv hφ j) i
    have hH : ∫ y, φ y • H y (unitVector j) (unitVector i) =
        -∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i) := by
      rw [hs.weak_second φ hφ i j, neg_neg]
    rw [hH]
    exact hG.symm
  have hij : ∀ i j : Fin 3, ∀ᵐ y ∂volume,
      H y (unitVector j) (unitVector i) = H y (unitVector i) (unitVector j) := by
    intro i j
    refine ae_eq_of_integral_contDiff_smul_eq (hloc j i) (hloc i j) fun φ hφ hcφ => ?_
    rw [key i j φ ⟨hφ, hcφ⟩, key j i φ ⟨hφ, hcφ⟩, dirDeriv_comm hφ]
  have hall : ∀ᵐ y ∂volume, ∀ i j : Fin 3, H y (unitVector j) (unitVector i) = H y (unitVector i) (unitVector j) :=
    ae_all_iff.2 fun i => ae_all_iff.2 (hij i)
  filter_upwards [hall] with y hy i j
  exact hy j i

private theorem modeThird_swap_ae {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hF : IsLocalSecondOrderField v G H) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → ∀ a b c : Fin 3, modeThird m n H a b c p = modeThird m n H a c b p := by
  filter_upwards [Internal.PlaneDeleted.cyl_ae (second_symm_ae hF)] with p hp hpos a b c
  have e := Internal.PlaneDeleted.mode_congr m n 1
    (Φ := fun θ => (frameThird θ (H (cylPoint p.1 θ p.2)) a b c : ℂ))
    (Ψ := fun θ => (frameThird θ (H (cylPoint p.1 θ p.2)) a c b : ℂ)) ?_ ?_ ?_
  · rw [one_mul] at e
    exact e
  · intro θ
    simp only [Internal.PlaneDeleted.cyl_per, frameThird, frameUnit, Internal.PlaneDeleted.radial_per,
      Internal.PlaneDeleted.angular_per]
  · intro θ
    simp only [Internal.PlaneDeleted.cyl_per, frameThird, frameUnit, Internal.PlaneDeleted.radial_per,
      Internal.PlaneDeleted.angular_per]
  · filter_upwards [hp hpos] with θ h
    rw [one_mul, third_swap θ _ h]

theorem localAngularHeightMode : LocalAngularHeightModeStatement := by
  intro m v G H hF n
  filter_upwards [angularGradMode_comb (m := m) hF n 0 2, angularGradMode_comb (m := m) hF n 1 2,
    angularGradMode_comb (m := m) hF n 2 2, modeThird_swap_ae (m := m) hF n] with p h0 h1 h2 hsw hr
  have e0 := h0 hr
  have e1 := h1 hr
  have e2 := h2 hr
  simp [angularGradMode, Fin.sum_univ_three, angularComb, frameTurn] at e0 e1 e2
  rw [hsw hr 0 1 2, hsw hr 1 1 2, hsw hr 2 1 2]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e0
  · linear_combination e1
  · linear_combination e2

end AngularHeight

theorem localHeightTurn_of (hI : LocalSideStripIntegrableStatement) : LocalHeightTurnStatement := by
  intro k N c K S B L hL x hx n e a t he ht
  have hsec : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1 := hx.1
  have hK : IsCellBox L.box := hL.box_eq ▸ hL.box_valid
  have htc : Continuous t := by
    obtain ⟨q, hq⟩ := ht
    have e1 : t = fun u => q.eval u := funext hq
    rw [e1]
    exact q.continuous
  have hA := localAngularMode L.order x.1 x.2.1 x.2.2.1 hsec n
  have hS := localAngularHeightMode L.order x.1 x.2.1 x.2.2.1 hsec n
  have hI' : ∀ b : Fin 3, _ := fun b => (hI c K S B L hL x hx n e b (fun h => absurd h (by omega))).2 he
  have hlo : 0 ≤ L.box.r₁ := hK.r_order.1
  obtain ⟨co, oo, hface, hside, hint⟩ : ∃ co oo : ℝ,
      (∀ F dF : ℝ × ℝ → ℂ, heightFaceMoment L.box F dF (CellLayout.sideHeightIndex e) t =
        heightStripMoment co oo L.box.r₁ L.box.r₂ (fun r => r) F dF t) ∧
      (∀ b : Fin 3, L.sideVelocityValue n x e b t =
        heightStripMoment co oo L.box.r₁ L.box.r₂ (fun _ => 1) (L.velMode n x b) (L.gradModeOf n x b 2) t) ∧
      (∀ b : Fin 3, IntegrableOn (fun p : ℝ × ℝ => ((((1 / (co - oo) : ℝ)) : ℂ) * L.velMode n x b p
          + (((p.2 - oo) / (co - oo) : ℝ) : ℂ) * L.gradModeOf n x b 2 p) * ((1 : ℝ) : ℂ))
        (Set.Icc L.box.r₁ L.box.r₂ ×ˢ Set.Icc (min co oo) (max co oo))) := by
    have hcase : e = 2 ∨ e = 3 := by
      rcases e with ⟨e, hle⟩
      simp only [Fin.ext_iff, Fin.val_two]
      simp only at he
      omega
    rcases hcase with rfl | rfl
    · have hlev : L.sideLevel 2 = L.box.z₁ := by simp [CellLayout.sideLevel]
      have hoth : L.sideOther 2 = L.box.z₂ := by
        simp only [CellLayout.sideOther, hlev]
        simp
      refine ⟨L.box.z₁, L.box.z₂, fun F dF => ?_, fun b => ?_, fun b => ?_⟩
      · simp [heightFaceMoment, CellLayout.sideHeightIndex]
      · simp [CellLayout.sideVelocityValue, CellLayout.sideHeightIndex]
      · have h := hI' b
        rw [hlev, hoth] at h
        exact h.1
    · have hlev : L.sideLevel 3 = L.box.z₂ := by simp [CellLayout.sideLevel]
      have hoth : L.sideOther 3 = L.box.z₁ := by
        simp only [CellLayout.sideOther, hlev]
        simp
      refine ⟨L.box.z₂, L.box.z₁, fun F dF => ?_, fun b => ?_, fun b => ?_⟩
      · simp [heightFaceMoment, CellLayout.sideHeightIndex]
      · simp [CellLayout.sideVelocityValue, CellLayout.sideHeightIndex]
      · have h := hI' b
        rw [hlev, hoth] at h
        exact h.1
  rw [hface]
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · simp only [CellLayout.turnValue, if_true]
    rw [hside, hside, sub_eq_add_neg, neg_eq_neg_one_mul]
    refine Breakdown.CellCert.CellFormula.StrainFaceHeightTurn.strip_turn co oo L.box.r₁ L.box.r₂ hlo
      _ _ _ _ _ _ _ _ t htc ?_ (hint 0) (hint 1)
    filter_upwards [hA, hS] with p hp hq hr
    simp only [CellLayout.velMode, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [(hp hr).1, (hq hr).1]
    constructor <;> ring
  · simp only [CellLayout.turnValue, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true]
    rw [hside, hside, ← one_mul (heightStripMoment co oo _ _ (fun _ => 1) (L.velMode n x 0) _ t)]
    refine Breakdown.CellCert.CellFormula.StrainFaceHeightTurn.strip_turn co oo L.box.r₁ L.box.r₂ hlo
      _ _ _ _ _ _ _ _ t htc ?_ (hint 1) (hint 0)
    filter_upwards [hA, hS] with p hp hq hr
    simp only [CellLayout.velMode, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [(hp hr).2.1, (hq hr).2.1]
    constructor <;> ring
  · simp only [CellLayout.turnValue, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
    rw [hside, ← add_zero (_ * heightStripMoment co oo _ _ (fun _ => 1) (L.velMode n x 2) _ t),
      ← zero_mul (heightStripMoment co oo L.box.r₁ L.box.r₂ (fun _ => 1) (L.velMode n x 0) (L.gradModeOf n x 0 2) t)]
    refine Breakdown.CellCert.CellFormula.StrainFaceHeightTurn.strip_turn co oo L.box.r₁ L.box.r₂ hlo
      _ _ _ _ _ _ _ _ t htc ?_ (hint 2) (hint 0)
    filter_upwards [hA, hS] with p hp hq hr
    simp only [CellLayout.velMode, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [(hp hr).2.2, (hq hr).2.2]
    constructor <;> ring

theorem localHeightTurn : LocalHeightTurnStatement :=
  localHeightTurn_of localSideStripIntegrable

end LocalField

end CertCell

end Breakdown
