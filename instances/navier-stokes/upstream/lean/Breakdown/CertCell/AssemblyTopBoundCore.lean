import Breakdown.FracCell.SharpEnergyVelocityCoef
import Breakdown.FracCell.ProjCoef
import Breakdown.FracCell.SharpYDensityRegular
import Breakdown.FracCell.ReductionPointwiseWeightClauses_of
import Breakdown.CertCell.LabelModeFacts
import Breakdown.CertCell.RowLowPartVolume
import Breakdown.CertCell.LocalModeWeak
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.PeriodicSecondOrder
import Breakdown.CertCell.SecondDerivEnergyIdentity

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.Assembly.TopBound.Internal

open CellCert CellCert.CellAnalysis
open CellCert.CellAnalysis.SharpEnergyVelocityCoefInternal CellCert.CellAnalysis.SharpCoefTailInternal
  CellCert.CellAnalysis.CellSharpBoundInternal

theorem test_lift {K : CellBox} {F Fc Fs : ℝ × ℝ → ℂ}
    (h : ∀ᵐ p ∂(volume.restrict K.rect), F p = Fc p + Complex.I * Fs p)
    (hc : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Fc p) K.rect)
    (hs : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Fs p) K.rect) (φ : ℝ × ℝ → ℝ) (hφ : Continuous φ) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * ((φ p : ℝ) : ℂ)
      = (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fc p * ((φ p : ℝ) : ℂ))
        + Complex.I * ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fs p * ((φ p : ℝ) : ℂ) := by
  have hφc : ContinuousOn (fun p => ((φ p : ℝ) : ℂ)) K.rect := (Complex.continuous_ofReal.comp hφ).continuousOn
  have ic := hc.mul_continuousOn hφc (rect_cpt K)
  have is := hs.mul_continuousOn hφc (rect_cpt K)
  rw [← integral_const_mul, ← integral_add ic (is.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [h] with p hp
  rw [hp]
  ring

theorem coef_lift {K : CellBox} (B : CellBases) {F Fc Fs : ℝ × ℝ → ℂ}
    (h : ∀ᵐ p ∂(volume.restrict K.rect), F p = Fc p + Complex.I * Fs p)
    (hc : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Fc p) K.rect)
    (hs : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Fs p) K.rect) (j l : ℕ) :
    B.coef K F j l = B.coef K Fc j l + Complex.I * B.coef K Fs j l :=
  test_lift h hc hs (fun p => B.radialPoly j p.1 * B.heightPoly l p.2)
    (((rp_cont B j).comp continuous_fst).mul ((hp_cont B l).comp continuous_snd))

theorem coef_radial_of_weak {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {F s : ℝ × ℝ → ℂ} (hV : IntegrableOn F K.rect)
    (hGm : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * s p) K.rect)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 → ∀ t : ℝ → ℝ, Continuous t →
      ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * F p + ((ψ p.1 : ℝ) : ℂ) * s p) * ((t p.2 : ℝ) : ℂ) = 0)
    {j : ℕ} (hj : j ≠ 0) (l : ℕ) :
    ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * s p *
        (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
  have hr := hK.r_order.2
  set ψ : ℝ → ℝ := fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r with hψ
  have hd : ∀ r, HasDerivAt ψ (-(radialEigen K j) * K.lineWeight r * B.radialPoly j r) r :=
    radial_hasDeriv hr hB hj
  have hψd : ∀ r, deriv ψ r = -(radialEigen K j) * K.lineWeight r * B.radialPoly j r :=
    fun r => (hd r).deriv
  have hψc : ContDiff ℝ 1 ψ := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun r => (hd r).differentiableAt, ?_⟩
    rw [show deriv ψ = fun r => -(radialEigen K j) * K.lineWeight r * B.radialPoly j r from funext hψd]
    exact (continuous_const.mul (lw_cont K)).mul (rp_cont B j)
  have h0 := hw ψ hψc (by simp [hψ, refR_left K hr]) (by simp [hψ, refR_right K hr]) (B.heightPoly l)
    (hp_cont B l)
  simp only [hψd] at h0
  have iA : IntegrableOn (fun p : ℝ × ℝ =>
      ((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) * F p) K.rect :=
    IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp
      (((continuous_const.mul ((lw_cont K).comp continuous_fst)).mul ((rp_cont B j).comp continuous_fst)).mul
        ((hp_cont B l).comp continuous_snd))).continuousOn hV (rect_cpt K)
  have iB : IntegrableOn (fun p : ℝ × ℝ =>
      (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * s p)) K.rect :=
    IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp
      (((continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2)).mul ((rd_cont B j).comp continuous_fst)).mul
        ((hp_cont B l).comp continuous_snd))).continuousOn hGm (rect_cpt K)
  have h1 : (∫ p in K.rect, ((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
        * F p) + ∫ p in K.rect, (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
        * ((K.lineWeight p.1 : ℂ) * s p) = 0 := by
    rw [← integral_add iA iB, ← h0]
    congr 1
    funext p
    simp only [hψ]
    push_cast
    ring
  calc ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l
      = -∫ p in K.rect, ((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
          * F p := by
        rw [coef_eq, ← integral_const_mul, ← integral_neg]
        congr 1
        funext p
        push_cast
        ring
    _ = ∫ p in K.rect, (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
          * ((K.lineWeight p.1 : ℂ) * s p) := by
        linear_combination -h1
    _ = _ := by
        congr 1
        funext p
        ring

theorem coef_height_of_ibp {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {F s : ℝ × ℝ → ℂ}
    (hI : ∀ f h : ℝ → ℝ, Continuous f → ContDiff ℝ 1 h → h K.z₁ = 0 → h K.z₂ = 0 →
      ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * ((f p.1 * deriv h p.2 : ℝ) : ℂ) =
        -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * s p * ((f p.1 * h p.2 : ℝ) : ℂ))
    (j : ℕ) {l : ℕ} (hl : l ≠ 0) :
    ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * s p *
        ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ) := by
  have hz := hK.z_order.2
  have h := hI (B.radialPoly j) (fun z => (1 - K.refZ z ^ 2) * hd B l z) (rp_cont B j) (htF_cd K B l)
    (by simp [refZ_left K hz]) (by simp [refZ_right K hz])
  simp only [fun z => (height_hasDeriv hz hB hl z).deriv] at h
  rw [coef_eq, ← integral_const_mul]
  calc ∫ p in K.rect, ((heightEigen K l : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * F p *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
      = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p *
          ((B.radialPoly j p.1 * (-(heightEigen K l) * B.heightPoly l p.2) : ℝ) : ℂ) := by
        rw [← integral_neg]
        congr 1
        funext p
        push_cast
        ring
    _ = _ := by rw [h, neg_neg]

theorem radial_fin_gen {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {F s : ℝ × ℝ → ℂ} (hs : AEStronglyMeasurable s (volume.restrict K.rect))
    (hs2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖s p‖ ^ 2) K.rect)
    (hR : ∀ j l, j ≠ 0 → ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * s p *
        (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
    {Q : ℕ} (T U : Finset (ℕ × ℕ)) (hT : ∀ i ∈ T, Q ≤ i.1) (hQ : 1 ≤ Q) (hU : ∀ u ∈ U, u.1 + 2 ≤ Q) :
    ∑ i ∈ T, radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2 + ∑ u ∈ U, ‖B.coef K s u.1 u.2‖ ^ 2
      ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖s p‖ ^ 2 := by
  have h := proj_coef_le hB (wr K) (wr_cont K) (wr_nonneg hK) wr_le (br K B) (br_cont K B) s hs hs2 T U
    (fun i hi i' hi' => br_orth hK hB (by have := hT i hi; omega) (by have := hT i' hi'; omega))
    (fun u hu i hi => br_zero hK hB (by have := hU u hu; have := hT i hi; omega))
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hj : i.1 ≠ 0 := by have := hT i hi; omega
  unfold br
  rw [int_scale K (wr K) (fun p => rd B i.1 p.1 * B.heightPoly i.2 p.2) s]
  refine term_eq _ (radialEigen_pos hK.r_order.2 hj) _ _ ?_
  rw [hR i.1 i.2 hj]
  congr 1
  funext p
  simp only [wr]
  push_cast
  ring

theorem height_fin_gen {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {F s : ℝ × ℝ → ℂ} (hs : AEStronglyMeasurable s (volume.restrict K.rect))
    (hs2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖s p‖ ^ 2) K.rect)
    (hH : ∀ j l, l ≠ 0 → ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * s p *
        ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ))
    {Q : ℕ} (T U : Finset (ℕ × ℕ)) (hT : ∀ i ∈ T, i.1 < Q ∧ Q ≤ i.2) (hQ : 1 ≤ Q)
    (hU : ∀ u ∈ U, Q ≤ u.1 ∨ u.2 + 2 ≤ Q) :
    ∑ i ∈ T, heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2 + ∑ u ∈ U, ‖B.coef K s u.1 u.2‖ ^ 2
      ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖s p‖ ^ 2 := by
  have h := proj_coef_le hB (wz K) (wz_cont K) (wz_nonneg hK) wz_le (bz K B) (bz_cont K B) s hs hs2 T U
    (fun i hi i' hi' => bz_orth hK hB (by have := (hT i hi).2; omega) (by have := (hT i' hi').2; omega))
    (fun u hu i hi => bz_zero hK hB (by
      have h1 := hT i hi
      rcases hU u hu with h2 | h2
      · left; omega
      · right; omega))
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hl : i.2 ≠ 0 := by have := (hT i hi).2; omega
  unfold bz
  rw [int_scale K (wz K) (fun p => B.radialPoly i.1 p.1 * hd B i.2 p.2) s]
  refine term_eq _ (heightEigen_pos hK.z_order.2 hl) _ _ ?_
  rw [hH i.1 i.2 hl]
  congr 1
  funext p
  simp only [wz]
  push_cast
  ring

theorem tail_hasSum {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {F : ℝ × ℝ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) (d : ℕ) :
    HasSum (fun i : ℕ × ℕ => if max i.1 i.2 ≤ d then 0 else ‖B.coef K F i.1 i.2‖ ^ 2) (K.tailNormSq d F) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := projCoef_holds K B hK hB F ⟨hF, hF2⟩ d
  have h := coef_hasSum hK hB _ h1 h2
  have e : (fun i : ℕ × ℕ => ‖B.coef K (fun p => F p - K.proj d d F p) i.1 i.2‖ ^ 2)
      = fun i => if max i.1 i.2 ≤ d then 0 else ‖B.coef K F i.1 i.2‖ ^ 2 := by
    funext i
    rw [h3]
    split_ifs <;> simp
  rw [e] at h
  exact h

theorem tail_nonneg (K : CellBox) (d : ℕ) (F : ℝ × ℝ → ℂ) : 0 ≤ K.tailNormSq d F :=
  setIntegral_nonneg (rect_meas K) fun _ hp => mul_nonneg (lw_nonneg hp.1.1) (sq_nonneg _)

theorem split_eval (Q : ℕ) (g : ℕ × ℕ → ℝ) (P : ℕ → ℕ → Prop) [∀ j l, Decidable (P j l)] :
    (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), if P j l then g (j, l) else 0)
      = ∑ i ∈ (Finset.range (Q + 1) ×ˢ Finset.range (Q + 1)).filter (fun i => P i.1 i.2), g i := by
  rw [Finset.sum_filter, Finset.sum_product]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ l ∈ Finset.range (Q + 1), if P j l then g (j, l) else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => if P j l then g (j, l) else 0)]

theorem tail_top_bound {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {F sr sz : ℝ × ℝ → ℂ} (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect)
    (hr : AEStronglyMeasurable sr (volume.restrict K.rect))
    (hr2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖sr p‖ ^ 2) K.rect)
    (hz : AEStronglyMeasurable sz (volume.restrict K.rect))
    (hz2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖sz p‖ ^ 2) K.rect)
    (hR : ∀ j l, j ≠ 0 → ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * sr p *
        (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
    (hH : ∀ j l, l ≠ 0 → ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * sz p *
        ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ))
    {Q : ℕ} (hQ : 2 ≤ Q) :
    K.tailNormSq (Q - 1) F
      ≤ (radialEigen K Q)⁻¹ * (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
            if Q ≤ (j : ℕ) + 1 then ‖B.coef K sr j l‖ ^ 2 else 0)
        + (heightEigen K Q)⁻¹ * (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
            if (j : ℕ) + 1 ≤ Q ∧ Q ≤ (l : ℕ) + 1 then ‖B.coef K sz j l‖ ^ 2 else 0)
        + (K.tailNormSq Q sr + K.tailNormSq Q sz) / min (radialEigen K Q) (heightEigen K Q) := by
  set cF : ℕ × ℕ → ℝ := fun i => ‖B.coef K F i.1 i.2‖ ^ 2 with hcF
  set cr : ℕ × ℕ → ℝ := fun i => ‖B.coef K sr i.1 i.2‖ ^ 2 with hcr
  set cz : ℕ × ℕ → ℝ := fun i => ‖B.coef K sz i.1 i.2‖ ^ 2 with hcz
  have lr : 0 < radialEigen K Q := radialEigen_pos hK.r_order.2 (by omega)
  have lz : 0 < heightEigen K Q := heightEigen_pos hK.z_order.2 (by omega)
  have lm : 0 < min (radialEigen K Q) (heightEigen K Q) := lt_min lr lz
  have tF := tail_hasSum (B := B) hK hB hF hF2 (Q - 1)
  have tr := tail_hasSum (B := B) hK hB hr hr2 Q
  have tz := tail_hasSum (B := B) hK hB hz hz2 Q
  have Sr := coef_hasSum (B := B) hK hB sr hr hr2
  have Sz := coef_hasSum (B := B) hK hB sz hz hz2
  have TR0 := tail_nonneg K Q sr
  have TZ0 := tail_nonneg K Q sz
  set XR := ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), if Q ≤ (j : ℕ) + 1 then ‖B.coef K sr j l‖ ^ 2 else 0 with hXR
  set XZ := ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
    if (j : ℕ) + 1 ≤ Q ∧ Q ≤ (l : ℕ) + 1 then ‖B.coef K sz j l‖ ^ 2 else 0 with hXZ
  have eXR : XR = ∑ i ∈ (Finset.range (Q + 1) ×ˢ Finset.range (Q + 1)).filter (fun i => Q ≤ i.1 + 1), cr i :=
    split_eval Q cr (fun j _ => Q ≤ j + 1)
  have eXZ : XZ = ∑ i ∈ (Finset.range (Q + 1) ×ˢ Finset.range (Q + 1)).filter
      (fun i => i.1 + 1 ≤ Q ∧ Q ≤ i.2 + 1), cz i :=
    split_eval Q cz (fun j l => j + 1 ≤ Q ∧ Q ≤ l + 1)
  have eTR : (∑' i : ℕ × ℕ, if ¬ max i.1 i.2 ≤ Q then cr i else 0) = K.tailNormSq Q sr := by
    rw [← tr.tsum_eq]
    congr 1
    funext i
    exact ite_not _ _ _
  have eTZ : (∑' i : ℕ × ℕ, if ¬ max i.1 i.2 ≤ Q then cz i else 0) = K.tailNormSq Q sz := by
    rw [← tz.tsum_eq]
    congr 1
    funext i
    exact ite_not _ _ _
  have hXr : (∑' i : ℕ × ℕ, if Q ≤ i.1 + 1 then cr i else 0) ≤ XR + K.tailNormSq Q sr := by
    rw [eXR, ← eTR]
    refine split_le cr (fun _ => sq_nonneg _) Sr.summable _ _ _ fun i hi => ?_
    by_cases h2 : max i.1 i.2 ≤ Q
    · left
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      simp only [max_le_iff] at h2
      omega
    · right
      exact h2
  have hXz : (∑' i : ℕ × ℕ, if i.1 + 1 ≤ Q ∧ Q ≤ i.2 + 1 then cz i else 0) ≤ XZ + K.tailNormSq Q sz := by
    rw [eXZ, ← eTZ]
    refine split_le cz (fun _ => sq_nonneg _) Sz.summable _ _ _ fun i hi => ?_
    by_cases h2 : max i.1 i.2 ≤ Q
    · left
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      simp only [max_le_iff] at h2
      omega
    · right
      exact h2
  have hRt : ∀ T : Finset (ℕ × ℕ), (∀ i ∈ T, Q ≤ i.1) →
      radialEigen K Q * ∑ i ∈ T, cF i ≤ ∑' i : ℕ × ℕ, if Q ≤ i.1 + 1 then cr i else 0 := by
    intro T hT
    have h := tail_le cr (fun _ => sq_nonneg _) _ Sr (fun i => Q ≤ i.1 + 1)
      (∑ i ∈ T, radialEigen K i.1 * cF i) fun U hU =>
        radial_fin_gen hK hB hr hr2 hR T U hT (by omega) fun u hu => by have := hU u hu; omega
    refine le_trans ?_ h
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (Reduction.WeightClausesInternal.radial_mono K (hT i hi)) (sq_nonneg _)
  have hZt : ∀ T : Finset (ℕ × ℕ), (∀ i ∈ T, i.1 < Q ∧ Q ≤ i.2) →
      heightEigen K Q * ∑ i ∈ T, cF i ≤ ∑' i : ℕ × ℕ, if i.1 + 1 ≤ Q ∧ Q ≤ i.2 + 1 then cz i else 0 := by
    intro T hT
    have h := tail_le cz (fun _ => sq_nonneg _) _ Sz (fun i => i.1 + 1 ≤ Q ∧ Q ≤ i.2 + 1)
      (∑ i ∈ T, heightEigen K i.2 * cF i) fun U hU =>
        height_fin_gen hK hB hz hz2 hH T U hT (by omega) fun u hu => by
          have := hU u hu
          by_cases h1 : Q ≤ u.1
          · left; exact h1
          · right; omega
    refine le_trans ?_ h
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (Reduction.WeightClausesInternal.height_mono K (hT i hi).2) (sq_nonneg _)
  rw [← tF.tsum_eq]
  refine tF.summable.tsum_le_of_sum_le fun T => ?_
  set T1 := T.filter (fun i => Q ≤ i.1) with hT1
  set T2 := T.filter (fun i => i.1 < Q ∧ Q ≤ i.2) with hT2
  have esum : (∑ i ∈ T, if max i.1 i.2 ≤ Q - 1 then 0 else cF i) = ∑ i ∈ T1, cF i + ∑ i ∈ T2, cF i := by
    rw [hT1, hT2, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : max i.1 i.2 ≤ Q - 1
    · simp only [max_le_iff] at h1
      rw [if_pos (by simp only [max_le_iff]; exact h1), if_neg (by omega), if_neg (by omega), add_zero]
    · simp only [max_le_iff, not_and_or, not_le] at h1
      rw [if_neg (by simp only [max_le_iff, not_and_or, not_le]; exact h1)]
      by_cases h2 : Q ≤ i.1
      · rw [if_pos h2, if_neg (by omega), add_zero]
      · rw [if_neg h2, if_pos (by omega), zero_add]
  have h1 := le_trans (hRt T1 fun i hi => (Finset.mem_filter.1 hi).2) hXr
  have h2 := le_trans (hZt T2 fun i hi => (Finset.mem_filter.1 hi).2) hXz
  have hA : ∑ i ∈ T1, cF i ≤ (radialEigen K Q)⁻¹ * XR + K.tailNormSq Q sr / min (radialEigen K Q) (heightEigen K Q) := by
    have e1 : ∑ i ∈ T1, cF i ≤ (radialEigen K Q)⁻¹ * (XR + K.tailNormSq Q sr) := by
      rw [← div_eq_inv_mul, le_div_iff₀ lr, mul_comm]
      exact h1
    have e2 : K.tailNormSq Q sr / radialEigen K Q ≤ K.tailNormSq Q sr / min (radialEigen K Q) (heightEigen K Q) :=
      div_le_div_of_nonneg_left TR0 lm (min_le_left _ _)
    rw [mul_add, ← div_eq_inv_mul (K.tailNormSq Q sr)] at e1
    linarith
  have hB' : ∑ i ∈ T2, cF i ≤ (heightEigen K Q)⁻¹ * XZ + K.tailNormSq Q sz / min (radialEigen K Q) (heightEigen K Q) := by
    have e1 : ∑ i ∈ T2, cF i ≤ (heightEigen K Q)⁻¹ * (XZ + K.tailNormSq Q sz) := by
      rw [← div_eq_inv_mul, le_div_iff₀ lz, mul_comm]
      exact h2
    have e2 : K.tailNormSq Q sz / heightEigen K Q ≤ K.tailNormSq Q sz / min (radialEigen K Q) (heightEigen K Q) :=
      div_le_div_of_nonneg_left TZ0 lm (min_le_right _ _)
    rw [mul_add, ← div_eq_inv_mul (K.tailNormSq Q sz)] at e1
    linarith
  rw [esum, add_div]
  linarith

theorem weighted_of_lift {K : CellBox} {F Fc Fs : ℝ × ℝ → ℂ}
    (h : ∀ᵐ p ∂(volume.restrict K.rect), F p = Fc p + Complex.I * Fs p)
    (hc : AEStronglyMeasurable Fc (volume.restrict K.rect))
    (hc2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖Fc p‖ ^ 2) K.rect)
    (hs : AEStronglyMeasurable Fs (volume.restrict K.rect))
    (hs2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖Fs p‖ ^ 2) K.rect) :
    AEStronglyMeasurable F (volume.restrict K.rect) ∧
      IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect := by
  have hm : AEStronglyMeasurable F (volume.restrict K.rect) :=
    (hc.add (aestronglyMeasurable_const.mul hs)).congr (h.mono fun p hp => hp.symm)
  exact ⟨hm, CertCell.CellCalculus.LabelModeFacts.Internal.weighted_sq_int K ((lw_cont K).comp continuous_fst)
    (fun p hp => lw_nonneg hp.1.1) hm h hc2 hs2⟩

theorem weighted_of_tail {K : CellBox} {F : ℝ × ℝ → ℂ} (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (d : ℕ) (h : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p - K.proj d d F p‖ ^ 2) K.rect) :
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect := by
  have hP : Continuous (K.proj d d F) := SharpYDensityRegular.Internal.proj_cont K d d F
  have hPi : IntegrableOn (fun p => K.lineWeight p.1 * ‖K.proj d d F p‖ ^ 2) K.rect :=
    (((lw_cont K).comp continuous_fst).mul (hP.norm.pow 2)).continuousOn.integrableOn_compact (rect_cpt K)
  refine Integrable.mono' ((h.const_mul 2).add (hPi.const_mul 2))
    (((lw_cont K).comp continuous_fst).aestronglyMeasurable.mul (hF.norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
  have hw := lw_nonneg (K := K) hp.1.1
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  have hb : ‖F p‖ ^ 2 ≤ 2 * ‖F p - K.proj d d F p‖ ^ 2 + 2 * ‖K.proj d d F p‖ ^ 2 := by
    have e := norm_add_le (F p - K.proj d d F p) (K.proj d d F p)
    rw [sub_add_cancel] at e
    nlinarith [norm_nonneg (F p), norm_nonneg (F p - K.proj d d F p), norm_nonneg (K.proj d d F p),
      sq_nonneg (‖F p - K.proj d d F p‖ - ‖K.proj d d F p‖)]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left hb hw]

theorem tail_top_bound' {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {F sr sz : ℝ × ℝ → ℂ} (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hr : AEStronglyMeasurable sr (volume.restrict K.rect))
    (hr2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖sr p‖ ^ 2) K.rect)
    (hz : AEStronglyMeasurable sz (volume.restrict K.rect))
    (hz2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖sz p‖ ^ 2) K.rect)
    (hR : ∀ j l, j ≠ 0 → ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * sr p *
        (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
    (hH : ∀ j l, l ≠ 0 → ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * sz p *
        ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ))
    {Q : ℕ} (hQ : 2 ≤ Q) :
    K.tailNormSq (Q - 1) F
      ≤ (radialEigen K Q)⁻¹ * (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
            if Q ≤ (j : ℕ) + 1 then ‖B.coef K sr j l‖ ^ 2 else 0)
        + (heightEigen K Q)⁻¹ * (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
            if (j : ℕ) + 1 ≤ Q ∧ Q ≤ (l : ℕ) + 1 then ‖B.coef K sz j l‖ ^ 2 else 0)
        + (K.tailNormSq Q sr + K.tailNormSq Q sz) / min (radialEigen K Q) (heightEigen K Q) := by
  by_cases hi : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p - K.proj (Q - 1) (Q - 1) F p‖ ^ 2) K.rect
  · exact tail_top_bound hK hB hF (weighted_of_tail hF _ hi) hr hr2 hz hz2 hR hH hQ
  · have e : K.tailNormSq (Q - 1) F = 0 := integral_undef hi
    rw [e]
    have a1 : 0 ≤ ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
        if Q ≤ (j : ℕ) + 1 then ‖B.coef K sr j l‖ ^ 2 else 0 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
    have a2 : 0 ≤ ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
        if (j : ℕ) + 1 ≤ Q ∧ Q ≤ (l : ℕ) + 1 then ‖B.coef K sz j l‖ ^ 2 else 0 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
    have b1 := mul_nonneg (inv_nonneg.2 (radialEigen_nonneg (K := K) Q)) a1
    have b2 := mul_nonneg (inv_nonneg.2 (heightEigen_nonneg (K := K) Q)) a2
    have b3 : 0 ≤ (K.tailNormSq Q sr + K.tailNormSq Q sz) / min (radialEigen K Q) (heightEigen K Q) :=
      div_nonneg (add_nonneg (tail_nonneg K Q sr) (tail_nonneg K Q sz))
        (le_min (radialEigen_nonneg Q) (heightEigen_nonneg Q))
    linarith


open CellFormula CertCell.CellCalculus in
theorem label_component_bound {m : ℕ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hP : IsPeriodicSecondOrder v G H) (ι : ℤ × ℤ)
    {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {Q : ℕ} (hQ : 2 ≤ Q) (a : Fin 3) :
    K.tailNormSq (Q - 1) (fun p => velAt m ι v a p)
      ≤ (radialEigen K Q)⁻¹ * (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
            if Q ≤ (j : ℕ) + 1 then ‖B.coef K (fun p => gradAt m ι G a 0 p) j l‖ ^ 2 else 0)
        + (heightEigen K Q)⁻¹ * (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
            if (j : ℕ) + 1 ≤ Q ∧ Q ≤ (l : ℕ) + 1 then ‖B.coef K (fun p => gradAt m ι G a 2 p) j l‖ ^ 2 else 0)
        + (K.tailNormSq Q (fun p => gradAt m ι G a 0 p) + K.tailNormSq Q (fun p => gradAt m ι G a 2 p))
          / min (radialEigen K Q) (heightEigen K Q) := by
  set ν := labelTime ι with hν
  obtain ⟨hc, hs, -⟩ := harmonicLift_holds m v G H hP ν
  have hlift := RowLow.Internal.lift_rect harmonicLift_holds hP m ι hK
  have hgl : ∀ b, ∀ᵐ p ∂(volume.restrict K.rect), gradAt m ι G a b p
      = gradMode m ι.1 (harmonicCos ν G) a b p + Complex.I * gradMode m ι.1 (harmonicSin ν G) a b p :=
    fun b => hlift.mono fun p hp => hp.2.1 a b
  have hvl : ∀ᵐ p ∂(volume.restrict K.rect), velAt m ι v a p
      = modeVec m ι.1 (harmonicCos ν v) p.1 p.2 a + Complex.I * modeVec m ι.1 (harmonicSin ν v) p.1 p.2 a :=
    hlift.mono fun p hp => hp.1 a
  have lc := LocalField.localModeIntegrable m _ _ _ hc K hK ι.1 a
  have ls := LocalField.localModeIntegrable m _ _ _ hs K hK ι.1 a
  have gsq : ∀ b, AEStronglyMeasurable (fun p => gradAt m ι G a b p) (volume.restrict K.rect) ∧
      IntegrableOn (fun p => K.lineWeight p.1 * ‖gradAt m ι G a b p‖ ^ 2) K.rect := fun b =>
    weighted_of_lift (hgl b) (LocalField.localModeGradSquare K hK m _ _ _ hc ι.1 a b).1
      (LocalField.localModeGradSquare K hK m _ _ _ hc ι.1 a b).2
      (LocalField.localModeGradSquare K hK m _ _ _ hs ι.1 a b).1
      (LocalField.localModeGradSquare K hK m _ _ _ hs ι.1 a b).2
  obtain ⟨iVc, iGc, wc⟩ := LocalField.localModeRadialWeak K hK m _ _ _ hc ι.1 a
  obtain ⟨iVs, iGs, ws⟩ := LocalField.localModeRadialWeak K hK m _ _ _ hs ι.1 a
  obtain ⟨-, Ic⟩ := LocalField.localHeightModeIbp m ι.1 _ _ _ hc K hK a
  obtain ⟨-, Is⟩ := LocalField.localHeightModeIbp m ι.1 _ _ _ hs K hK a
  have hFm : AEStronglyMeasurable (fun p => velAt m ι v a p) (volume.restrict K.rect) :=
    (RowLow.Internal.velAt_int harmonicLift_holds hP m ι hK a).aestronglyMeasurable
  refine tail_top_bound' hK hB hFm (gsq 0).1 (gsq 0).2 (gsq 2).1 (gsq 2).2 ?_ ?_ hQ
  · intro j l hj
    have e0 := coef_lift B hvl lc.1 ls.1 j l
    have e1 := coef_radial_of_weak (B := B) hK hB iVc iGc wc hj l
    have e2 := coef_radial_of_weak (B := B) hK hB iVs iGs ws hj l
    have e3 := test_lift (hgl 0) (lc.2 0) (ls.2 0)
      (fun p => (1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2)
      (((continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2)).mul
        ((rd_cont B j).comp continuous_fst)).mul ((hp_cont B l).comp continuous_snd))
    beta_reduce at e3
    linear_combination ((radialEigen K j : ℝ) : ℂ) * e0 + e1 + Complex.I * e2 - e3
  · intro j l hl
    have e0 := coef_lift B hvl lc.1 ls.1 j l
    have e1 := coef_height_of_ibp (B := B) hK hB Ic j hl
    have e2 := coef_height_of_ibp (B := B) hK hB Is j hl
    have e3 := test_lift (hgl 2) (lc.2 2) (ls.2 2)
      (fun p => B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2))
      (((rp_cont B j).comp continuous_fst).mul ((continuous_const.sub
        (((refZ_cont K).comp continuous_snd).pow 2)).mul ((hd_cont B l).comp continuous_snd)))
    beta_reduce at e3
    linear_combination ((heightEigen K l : ℝ) : ℂ) * e0 + e1 + Complex.I * e2 - e3

open CellFormula CertCell.CellCalculus in
theorem label_tail_bound {m : ℕ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hP : IsPeriodicSecondOrder v G H) (ι : ℤ × ℤ)
    {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {Q : ℕ} (hQ : 2 ≤ Q) :
    ∑ a : Fin 3, K.tailNormSq (Q - 1) (fun p => velAt m ι v a p)
      ≤ (radialEigen K Q)⁻¹ * (∑ a : Fin 3, ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
            if Q ≤ (j : ℕ) + 1 then ‖B.coef K (fun p => gradAt m ι G a 0 p) j l‖ ^ 2 else 0)
        + (heightEigen K Q)⁻¹ * (∑ a : Fin 3, ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
            if (j : ℕ) + 1 ≤ Q ∧ Q ≤ (l : ℕ) + 1 then ‖B.coef K (fun p => gradAt m ι G a 2 p) j l‖ ^ 2 else 0)
        + (∑ a : Fin 3, ∑ b : Fin 3, K.tailNormSq Q (fun p => gradAt m ι G a b p))
          / min (radialEigen K Q) (heightEigen K Q) := by
  have lm : 0 < min (radialEigen K Q) (heightEigen K Q) :=
    lt_min (radialEigen_pos hK.r_order.2 (by omega)) (heightEigen_pos hK.z_order.2 (by omega))
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => label_component_bound (m := m) (B := B) hP ι hK hB hQ a
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div] at hsum
  have hT : ∑ a : Fin 3, (K.tailNormSq Q (fun p => gradAt m ι G a 0 p) + K.tailNormSq Q (fun p => gradAt m ι G a 2 p))
      ≤ ∑ a : Fin 3, ∑ b : Fin 3, K.tailNormSq Q (fun p => gradAt m ι G a b p) := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Fin.sum_univ_three]
    linarith [tail_nonneg K Q (fun p => gradAt m ι G a 1 p)]
  have := div_le_div_of_nonneg_right hT lm.le
  linarith

open CellFormula CertCell.CellCalculus in
theorem label_lowStrain_data {m : ℕ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hP : IsPeriodicSecondOrder v G H) (Pg : ℝ → Space → Space)
    (ι : ℤ × ℤ) (L : CellLayout) (hK : IsCellBox L.box) (hord : L.order = m) (hmodes : L.modes = {ι.1})
    (n : L.modes) (a b : Fin 3) (j l : Fin (L.degCoef + 1)) :
    harmonicData L (labelTime ι) v G H Pg (Sum.inl (n, a, b, j, l))
      = L.bases.coef L.box (fun p => gradAt m ι G a b p) j l := by
  have hn : (n : ℤ) = ι.1 := Finset.mem_singleton.1 (hmodes ▸ n.2)
  obtain ⟨hc, hs, -⟩ := harmonicLift_holds m v G H hP (labelTime ι)
  have hlift := RowLow.Internal.lift_rect harmonicLift_holds hP m ι hK
  rw [RowLow.Internal.data_lowStrain]
  dsimp only
  rw [hord, hn]
  exact (coef_lift L.bases (hlift.mono fun p hp => hp.2.1 a b)
    ((LocalField.localModeIntegrable m _ _ _ hc L.box hK ι.1 a).2 b)
    ((LocalField.localModeIntegrable m _ _ _ hs L.box hK ι.1 a).2 b) j l).symm

end Breakdown.CertCell.Assembly.TopBound.Internal
