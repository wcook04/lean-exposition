import Breakdown.FracCell.SharpYSharpEnergyTail
import Breakdown.FracCell.SharpCoefTail
import Breakdown.FracCell.ResolvedEnergy
import Breakdown.FracCell.ModeSquareIntegrable
import Breakdown.FracCell.ModeHeightParts
import Breakdown.FracCell.ModeRadialPartsA
import Breakdown.FracCell.EnergyDefs
import Breakdown.FracCell.AngularFrame
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.MeshFarPoly

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpEnergyTailParts CellEnergy

namespace SharpEnergyVorticityIdentityInternal

lemma anti_curl (s : Fin 3 → Fin 3 → ℂ) : 2 * antiSq s = ∑ i : Fin 3, ‖curlComp s i‖ ^ 2 := by
  have h : ∀ x y : ℂ, ‖(x - y) / 2‖ ^ 2 = ‖x - y‖ ^ 2 / 4 := by
    intro x y; rw [norm_div]; norm_num; ring
  simp only [antiSq, curlComp, Fin.sum_univ_three, CellCert.permSign, h]
  simp
  rw [← sub_eq_add_neg, ← sub_eq_add_neg, neg_add_eq_sub, norm_sub_rev (s 1 0), norm_sub_rev (s 2 0),
    norm_sub_rev (s 2 1)]
  ring

lemma curl_ang (k : ℝ) (s : Fin 3 → Fin 3 → ℂ) :
    curlComp (fun a b => ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * s a' b') 0 =
      Complex.I * k * curlComp s 0 - curlComp s 1 ∧
    curlComp (fun a b => ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * s a' b') 1 =
      Complex.I * k * curlComp s 1 + curlComp s 0 ∧
    curlComp (fun a b => ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * s a' b') 2 =
      Complex.I * k * curlComp s 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [curlComp, angularComb, frameTurn, CellCert.permSign, Fin.sum_univ_three] <;> ring

lemma ang_w (k : ℝ) (w0 w1 w2 : ℂ) :
    (max (|k| - 1) 0) ^ 2 * (‖w0‖ ^ 2 + ‖w1‖ ^ 2 + ‖w2‖ ^ 2) ≤
      ‖Complex.I * k * w0 - w1‖ ^ 2 + ‖Complex.I * k * w1 + w0‖ ^ 2 + ‖Complex.I * k * w2‖ ^ 2 := by
  have hm1 : (max (|k| - 1) 0) ^ 2 ≤ (|k| - 1) ^ 2 := by
    rcases le_total (|k| - 1) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (|k| - 1)]
    · rw [max_eq_left h]
  have hm2 : (max (|k| - 1) 0) ^ 2 ≤ k ^ 2 := by
    rcases le_total (|k| - 1) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg k]
    · rw [max_eq_left h, ← sq_abs k]
      exact pow_le_pow_left₀ h (by linarith) 2
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  set a := w0.re
  set b := w0.im
  set c := w1.re
  set d := w1.im
  set e := w2.re
  set f := w2.im
  have hS : 0 ≤ a * a + b * b + (c * c + d * d) := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hT : 0 ≤ e * e + f * f := by nlinarith [sq_nonneg e, sq_nonneg f]
  have key : (|k| - 1) ^ 2 * (a * a + b * b + (c * c + d * d)) ≤
      (k * b + c) ^ 2 + (k * a - d) ^ 2 + ((a - k * d) ^ 2 + (b + k * c) ^ 2) := by
    rcases le_total 0 k with h | h
    · rw [abs_of_nonneg h]
      nlinarith [mul_nonneg h (sq_nonneg (a - d)), mul_nonneg h (sq_nonneg (b + c))]
    · rw [abs_of_nonpos h]
      nlinarith [mul_nonneg (neg_nonneg.2 h) (sq_nonneg (a + d)), mul_nonneg (neg_nonneg.2 h) (sq_nonneg (b - c))]
  have k3 : k ^ 2 * (e * e + f * f) = (k * f) ^ 2 + (k * e) ^ 2 := by ring
  nlinarith [mul_le_mul_of_nonneg_right hm1 hS, mul_le_mul_of_nonneg_right hm2 hT]

lemma ang_ineq (k : ℝ) (s : Fin 3 → Fin 3 → ℂ) :
    (max (|k| - 1) 0) ^ 2 * ∑ i : Fin 3, ‖curlComp s i‖ ^ 2 ≤
      ∑ i : Fin 3, ‖curlComp (fun a b => ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * s a' b') i‖ ^ 2 := by
  obtain ⟨e0, e1, e2⟩ := curl_ang k s
  have h := ang_w k (curlComp s 0) (curlComp s 1) (curlComp s 2)
  rw [← e0, ← e1, ← e2] at h
  simpa only [Fin.sum_univ_three, add_assoc] using h

end SharpEnergyVorticityIdentityInternal

namespace SharpEnergyVorticityIdentityInternal

def ModeAngularRelationStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H → ∀ (n : ℤ) (a b : Fin 3),
      ∀ᵐ p ∂(volume.restrict K.rect),
        angularGradMode m n H a b p =
          ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' p

def PolyCoefTailStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (Q : ℕ) (P : ℝ × ℝ → ℂ),
    P ∈ polyFn Q Q → ∀ j l : ℕ, Q < max j l → B.coef K P j l = 0

def RadialTailStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (Q : ℕ) (F Fr : ℝ × ℝ → ℂ),
    AEStronglyMeasurable F (volume.restrict K.rect) → AEStronglyMeasurable Fr (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect →
    IntegrableOn (fun p => p.1 * ‖Fr p‖ ^ 2) K.rect →
    (∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr p * ψ p
          = -∫ p in K.rect, F p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) →
    ∀ T : Finset (ℕ × ℕ),
      (∑ jl ∈ T, (if Q < max jl.1 jl.2 then radialEigen K jl.1 * ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0)
        ≤ K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
            (fun p => Fr p - CellBox.radialDeriv (K.proj Q Q F) p))

def HeightTailStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (Q : ℕ) (F Fz : ℝ × ℝ → ℂ),
    AEStronglyMeasurable F (volume.restrict K.rect) → AEStronglyMeasurable Fz (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect →
    IntegrableOn (fun p => p.1 * ‖Fz p‖ ^ 2) K.rect →
    (∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz p * ψ p
          = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * CellBox.heightDeriv ψ p) →
    ∀ T : Finset (ℕ × ℕ),
      (∑ jl ∈ T, (if Q < max jl.1 jl.2 then heightEigen K jl.2 * ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0)
        ≤ K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
            (fun p => Fz p - CellBox.heightDeriv (K.proj Q Q F) p))

end SharpEnergyVorticityIdentityInternal

namespace SharpEnergyVorticityIdentityInternal

open CellEnergy.Internal.AngularFrame

lemma angular_relation : ModeAngularRelationStatement := by
  intro K hK m v G H hF n a b
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
    exact locallyIntegrable_iff.2 fun C hC => ((locs j i l).integrableOn_isCompact hC).smul_const _
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
  have hKer := fun i l => CellEnergy.circleWeak (fun y => inner ℝ (G y (unitVector i)) (unitVector l))
    (fun y => gv (H y) i l) (locf i l) (locg i l) (hweak i l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l => (hKer i l).1
  have hid := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
    (hKer i l).2 (wgt (azimuth m n) a b i l) (wgt_smooth _ a b i l) (hk ▸ wgt_periodic _ a b i l)
  have h0 : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
    have hnull : volume ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = 0 := by
      rw [show ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) by
        ext p; simp, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with p hp
    simpa using hp
  rw [ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)]
  filter_upwards [hint, hid, h0] with p h1 h2 h3 hp
  have hr : 0 < p.1 := lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm h3)
  obtain ⟨r, z⟩ := p
  exact point m n G H a b r z (fun i l => (h1 i l hr).1) (fun i l => (h1 i l hr).2) (fun i l => h2 i l hr)

end SharpEnergyVorticityIdentityInternal

namespace SharpEnergyVorticityIdentityInternal

open SharpCoefTailInternal CellSharpBoundInternal

lemma rad_fin {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F Fr : ℝ × ℝ → ℂ)
    (hFr : AEStronglyMeasurable Fr (volume.restrict K.rect))
    (hFr2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * ‖Fr p‖ ^ 2) K.rect)
    (T : Finset (ℕ × ℕ))
    (hR : ∀ jl ∈ T, jl.1 ≠ 0 → ((radialEigen K jl.1 : ℝ) : ℂ) * B.coef K F jl.1 jl.2 =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * Fr p *
        ((rd B jl.1 p.1 * B.heightPoly jl.2 p.2 : ℝ) : ℂ)) :
    ∑ jl ∈ T, radialEigen K jl.1 * ‖B.coef K F jl.1 jl.2‖ ^ 2
      ≤ ∫ p in K.rect, K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * ‖Fr p‖ ^ 2 := by
  have hr := hK.r_order.2
  set W : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) with hWdef
  have hWc : Continuous W :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2))
  have hW0 : ∀ p ∈ K.rect, 0 ≤ W p := fun p hp =>
    mul_nonneg (lw_nonneg hp.1.1) (refR_sq_le hr hp.1.1 hp.1.2)
  set b : ℕ × ℕ → ℝ × ℝ → ℝ := fun i p => rd B i.1 p.1 * B.heightPoly i.2 p.2 / Real.sqrt (radialEigen K i.1)
    with hbdef
  have hbc : ∀ i, Continuous (b i) := fun i =>
    (((rd_cont B _).comp continuous_fst).mul ((hp_cont B _).comp continuous_snd)).div_const _
  set T' := T.filter (fun i => i.1 ≠ 0)
  have e1 : ∑ i ∈ T, radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ∑ i ∈ T', radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2 := by
    refine (Finset.sum_filter_of_ne fun i _ hne => ?_).symm
    intro h0
    apply hne
    have : radialEigen K 0 = 0 := by unfold radialEigen; split_ifs <;> simp
    rw [h0, this, zero_mul]
  have e2 : ∀ i ∈ T', radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ‖∫ p in K.rect, (W p : ℂ) * Fr p * ((b i p : ℝ) : ℂ)‖ ^ 2 := by
    intro i hi
    have hj : i.1 ≠ 0 := (Finset.mem_filter.1 hi).2
    rw [hbdef]
    simp only
    rw [int_scale K W (fun p => rd B i.1 p.1 * B.heightPoly i.2 p.2) Fr]
    exact term_eq _ (radialEigen_pos hr hj) _ _ (hR i (Finset.mem_filter.1 hi).1 hj)
  rw [e1, Finset.sum_congr rfl e2]
  refine sq_coef_le K W hWc hW0 b hbc Fr hFr hFr2 T' ?_
  intro i hi i' hi'
  have hj : i.1 ≠ 0 := (Finset.mem_filter.1 hi).2
  have hj' : i'.1 ≠ 0 := (Finset.mem_filter.1 hi').2
  have e : ∀ p : ℝ × ℝ, W p * b i p * b i' p
      = (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * rd B i.1 p.1 * rd B i'.1 p.1
          / (Real.sqrt (radialEigen K i.1) * Real.sqrt (radialEigen K i'.1)))
        * (B.heightPoly i.2 p.2 * B.heightPoly i'.2 p.2) := by
    intro p; simp only [hWdef, hbdef]; field_simp
  simp_rw [e]
  rw [CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B i.1 r * rd B i'.1 r
        / (Real.sqrt (radialEigen K i.1) * Real.sqrt (radialEigen K i'.1)))
      (fun z => B.heightPoly i.2 z * B.heightPoly i'.2 z),
    integral_div, rad_orth hr hB, hB.height_orthonormal]
  obtain ⟨j, l⟩ := i
  obtain ⟨j', l'⟩ := i'
  simp only [Prod.mk.injEq] at hj hj' ⊢
  have hp := radialEigen_pos (K := K) hr hj
  by_cases h1 : j = j'
  · subst h1
    rw [if_pos rfl, Real.mul_self_sqrt hp.le, div_self hp.ne', one_mul]
    by_cases h2 : l = l' <;> simp [h2]
  · simp [h1]

lemma ht_fin {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F Fz : ℝ × ℝ → ℂ)
    (hFz : AEStronglyMeasurable Fz (volume.restrict K.rect))
    (hFz2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) * ‖Fz p‖ ^ 2) K.rect)
    (T : Finset (ℕ × ℕ))
    (hZ : ∀ jl ∈ T, jl.2 ≠ 0 → ((heightEigen K jl.2 : ℝ) : ℂ) * B.coef K F jl.1 jl.2 =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * Fz p *
        ((B.radialPoly jl.1 p.1 * hd B jl.2 p.2 : ℝ) : ℂ)) :
    ∑ jl ∈ T, heightEigen K jl.2 * ‖B.coef K F jl.1 jl.2‖ ^ 2
      ≤ ∫ p in K.rect, K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) * ‖Fz p‖ ^ 2 := by
  have hz := hK.z_order.2
  set W : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) with hWdef
  have hWc : Continuous W :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2))
  have hW0 : ∀ p ∈ K.rect, 0 ≤ W p := fun p hp =>
    mul_nonneg (lw_nonneg hp.1.1) (refZ_sq_le hz hp.2.1 hp.2.2)
  set b : ℕ × ℕ → ℝ × ℝ → ℝ := fun i p => B.radialPoly i.1 p.1 * hd B i.2 p.2 / Real.sqrt (heightEigen K i.2)
    with hbdef
  have hbc : ∀ i, Continuous (b i) := fun i =>
    (((rp_cont B _).comp continuous_fst).mul ((hd_cont B _).comp continuous_snd)).div_const _
  set T' := T.filter (fun i => i.2 ≠ 0)
  have e1 : ∑ i ∈ T, heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ∑ i ∈ T', heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2 := by
    refine (Finset.sum_filter_of_ne fun i _ hne => ?_).symm
    intro h0
    apply hne
    have : heightEigen K 0 = 0 := by unfold heightEigen; simp
    rw [h0, this, zero_mul]
  have e2 : ∀ i ∈ T', heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ‖∫ p in K.rect, (W p : ℂ) * Fz p * ((b i p : ℝ) : ℂ)‖ ^ 2 := by
    intro i hi
    have hl : i.2 ≠ 0 := (Finset.mem_filter.1 hi).2
    rw [hbdef]
    simp only
    rw [int_scale K W (fun p => B.radialPoly i.1 p.1 * hd B i.2 p.2) Fz]
    exact term_eq _ (heightEigen_pos hz hl) _ _ (hZ i (Finset.mem_filter.1 hi).1 hl)
  rw [e1, Finset.sum_congr rfl e2]
  refine sq_coef_le K W hWc hW0 b hbc Fz hFz hFz2 T' ?_
  intro i hi i' hi'
  have hl : i.2 ≠ 0 := (Finset.mem_filter.1 hi).2
  have hl' : i'.2 ≠ 0 := (Finset.mem_filter.1 hi').2
  have e : ∀ p : ℝ × ℝ, W p * b i p * b i' p
      = (K.lineWeight p.1 * B.radialPoly i.1 p.1 * B.radialPoly i'.1 p.1)
        * ((1 - K.refZ p.2 ^ 2) * hd B i.2 p.2 * hd B i'.2 p.2
          / (Real.sqrt (heightEigen K i.2) * Real.sqrt (heightEigen K i'.2))) := by
    intro p; simp only [hWdef, hbdef]; field_simp
  simp_rw [e]
  rw [CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * B.radialPoly i.1 r * B.radialPoly i'.1 r)
      (fun z => (1 - K.refZ z ^ 2) * hd B i.2 z * hd B i'.2 z
          / (Real.sqrt (heightEigen K i.2) * Real.sqrt (heightEigen K i'.2))),
    integral_div, ht_orth hz hB, hB.radial_orthonormal]
  obtain ⟨j, l⟩ := i
  obtain ⟨j', l'⟩ := i'
  simp only [Prod.mk.injEq] at hl hl' ⊢
  have hp := heightEigen_pos (K := K) hz hl
  by_cases h1 : l = l'
  · subst h1
    rw [if_pos rfl, Real.mul_self_sqrt hp.le, div_self hp.ne', mul_one]
    by_cases h2 : j = j' <;> simp [h2]
  · simp [h1]

lemma rad_id {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F Fr : ℝ × ℝ → ℂ)
    (hw : ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr p * ψ p
          = -∫ p in K.rect, F p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p)
    (j l : ℕ) (hj : j ≠ 0) :
    ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * Fr p *
        ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
  have hr := hK.r_order.2
  have h := hw (fun p => (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
    (prod_cd _ _ (radF_cd K B j) (hpoly_cd B l))
    (fun z => by simp [refR_left K hr]) (fun z => by simp [refR_right K hr])
  simp only [rderiv_psi hr hB hj] at h
  rw [coef_eq, ← integral_const_mul]
  calc ∫ p in K.rect, ((radialEigen K j : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * F p *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = -∫ p in K.rect, F p *
          ((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
          rw [← integral_neg]; congr 1; funext p; push_cast; ring
      _ = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr p *
          (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := h.symm
      _ = _ := by congr 1; funext p; push_cast; ring

lemma ht_id {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F Fz : ℝ × ℝ → ℂ)
    (hw : ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz p * ψ p
          = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * CellBox.heightDeriv ψ p)
    (j l : ℕ) (hl : l ≠ 0) :
    ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * Fz p *
        ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ) := by
  have hz := hK.z_order.2
  have h := hw (fun p => ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ))
    (prod_cd _ _ (rpoly_cd B j) (htF_cd K B l))
    (fun r => by simp [refZ_left K hz]) (fun r => by simp [refZ_right K hz])
  simp only [hderiv_psi hz hB j hl] at h
  rw [coef_eq, ← integral_const_mul]
  calc ∫ p in K.rect, ((heightEigen K l : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * F p *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p *
          ((B.radialPoly j p.1 * (-(heightEigen K l) * B.heightPoly l p.2) : ℝ) : ℂ) := by
          rw [← integral_neg]; congr 1; funext p; push_cast; ring
      _ = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz p *
          ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ) := h.symm
      _ = _ := by congr 1; funext p; push_cast; ring

lemma radial_full {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F Fr : ℝ × ℝ → ℂ)
    (hFr : AEStronglyMeasurable Fr (volume.restrict K.rect))
    (hFr2 : IntegrableOn (fun p => p.1 * ‖Fr p‖ ^ 2) K.rect)
    (hw : ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr p * ψ p
          = -∫ p in K.rect, F p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p)
    (T : Finset (ℕ × ℕ)) :
    ∑ jl ∈ T, radialEigen K jl.1 * ‖B.coef K F jl.1 jl.2‖ ^ 2
      ≤ K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) Fr :=
  rad_fin hK hB F Fr hFr (wmono _ hFr _ (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2)) (gR01 hK)
    (rmono hK _ hFr hFr2)) T (fun jl _ hj => rad_id hK hB F Fr hw jl.1 jl.2 hj)

lemma height_full {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F Fz : ℝ × ℝ → ℂ)
    (hFz : AEStronglyMeasurable Fz (volume.restrict K.rect))
    (hFz2 : IntegrableOn (fun p => p.1 * ‖Fz p‖ ^ 2) K.rect)
    (hw : ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz p * ψ p
          = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * CellBox.heightDeriv ψ p)
    (T : Finset (ℕ × ℕ)) :
    ∑ jl ∈ T, heightEigen K jl.2 * ‖B.coef K F jl.1 jl.2‖ ^ 2
      ≤ K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) Fz :=
  ht_fin hK hB F Fz hFz (wmono _ hFz _ (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2)) (gZ01 hK)
    (rmono hK _ hFz hFz2)) T (fun jl _ hl => ht_id hK hB F Fz hw jl.1 jl.2 hl)

end SharpEnergyVorticityIdentityInternal

namespace SharpEnergyVorticityIdentityInternal

open ResolvedEnergyInternal SharpCoefTailInternal CellSharpBoundInternal

lemma iR_pos {K : CellBox} (hK : IsCellBox K) : 0 < K.innerRadius := by
  unfold CellBox.innerRadius
  split_ifs with h
  · norm_num
  · exact lt_of_le_of_ne hK.r_order.1 (Ne.symm h)

lemma angW_nonneg {K : CellBox} (hK : IsCellBox K) (n : ℤ) : 0 ≤ K.angularWeight n := by
  have h2 : 0 < K.r₂ := lt_of_le_of_lt hK.r_order.1 hK.r_order.2
  unfold CellBox.angularWeight
  split_ifs <;> positivity


lemma bas_int {K : CellBox} {B : CellBases} (F : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) (j l : ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect :=
  g_int' K (fun p => K.lineWeight p.1) ((CellSharpBoundInternal.lw_cont K).comp continuous_fst) (fun _ hp => lw_nonneg hp.1.1)
    (fun jl p => B.radialPoly jl.1 p.1 * B.heightPoly jl.2 p.2)
    (fun _ => ((rp_cont B _).comp continuous_fst).mul ((hp_cont B _).comp continuous_snd)) F hF hF2 (j, l)

lemma coef_lin {K : CellBox} {B : CellBases} (g : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (κ : Fin 3 → Fin 3 → ℂ) (j l : ℕ)
    (hI : ∀ a b, IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * g a b p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect) :
    B.coef K (fun p => ∑ a : Fin 3, ∑ b : Fin 3, κ a b * g a b p) j l
      = ∑ a : Fin 3, ∑ b : Fin 3, κ a b * B.coef K (g a b) j l := by
  simp only [CellBases.coef]
  have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * (∑ a : Fin 3, ∑ b : Fin 3, κ a b * g a b p) *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) = fun p => ∑ a : Fin 3, ∑ b : Fin 3,
        κ a b * ((K.lineWeight p.1 : ℂ) * g a b p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
    funext p
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e, integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hI a b).const_mul _))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => (hI a b).const_mul _)]
  exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _

lemma coef_curl {K : CellBox} {B : CellBases} (g : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (hg : ∀ a b, AEStronglyMeasurable (g a b) (volume.restrict K.rect))
    (hg2 : ∀ a b, IntegrableOn (fun p => K.lineWeight p.1 * ‖g a b p‖ ^ 2) K.rect)
    (i : Fin 3) (j l : ℕ) :
    B.coef K (fun p => curlComp (fun a b => g a b p) i) j l = curlComp (fun a b => B.coef K (g a b) j l) i := by
  have e : (fun p => curlComp (fun a b => g a b p) i) = fun p => ∑ a : Fin 3, ∑ b : Fin 3, curlCoef i a b * g a b p :=
    funext fun p => (curl_sum i _).symm
  rw [e, coef_lin g (curlCoef i) j l (fun a b => bas_int (g a b) (hg a b) (hg2 a b) j l), curl_sum]

lemma curl_expand (A : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    curlComp (fun a b => ∑ a' : Fin 3, ∑ b' : Fin 3, A a b a' b' * s a' b') i =
      ∑ a' : Fin 3, ∑ b' : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3, curlCoef i a b * A a b a' b') * s a' b' := by
  rw [← curl_sum]
  simp only [Fin.sum_univ_three]
  ring

lemma two_anti {K : CellBox} {B : CellBases} (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (j l : ℕ) :
    2 * antiSq (fun a b => B.coef K (gradMode m n G a b) j l)
      = ∑ i : Fin 3, ‖B.coef K (fun p => curlComp (fun a b => gradMode m n G a b p) i) j l‖ ^ 2 := by
  rw [anti_curl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coef_curl _ (fun a b => (modeGradSquare K hK m v G H hs n a b).1)
    (fun a b => (modeGradSquare K hK m v G H hs n a b).2)]


lemma ang_coef {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hA : ModeAngularRelationStatement) {m : ℕ}
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (j l : ℕ) :
    (max (modeNumber m n - 1) 0) ^ 2 *
        ∑ i : Fin 3, ‖B.coef K (fun p => curlComp (fun a b => gradMode m n G a b p) i) j l‖ ^ 2
      ≤ ∑ i : Fin 3, ‖B.coef K (fun p => curlComp (fun a b => angularGradMode m n H a b p) i) j l‖ ^ 2 := by
  have hg := fun a b => (modeGradSquare K hK m v G H hs n a b).1
  have hg2 := fun a b => (modeGradSquare K hK m v G H hs n a b).2
  have eA : ∀ i, B.coef K (fun p => curlComp (fun a b => angularGradMode m n H a b p) i) j l =
      curlComp (fun a b => ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' *
        B.coef K (gradMode m n G a' b') j l) i := by
    intro i
    have hae : ∀ᵐ p ∂(volume.restrict K.rect), (fun p => curlComp (fun a b => angularGradMode m n H a b p) i) p =
        (fun p => ∑ a' : Fin 3, ∑ b' : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3, curlCoef i a b *
          angularComb (azimuth m n) a b a' b') * gradMode m n G a' b' p) p := by
      have h9 : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a b : Fin 3, angularGradMode m n H a b p =
          ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' p := by
        rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro b
        exact hA K hK m v G H hs n a b
      filter_upwards [h9] with p hp
      simp only [hp]
      exact curl_expand _ _ i
    have ec : B.coef K (fun p => curlComp (fun a b => angularGradMode m n H a b p) i) j l =
        B.coef K (fun p => ∑ a' : Fin 3, ∑ b' : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3, curlCoef i a b *
          angularComb (azimuth m n) a b a' b') * gradMode m n G a' b' p) j l := by
      unfold CellBases.coef
      refine integral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [hp]
    rw [ec, coef_lin _ _ j l (fun a b => bas_int _ (hg a b) (hg2 a b) j l), curl_expand]
  simp only [eA]
  unfold modeNumber
  rw [Finset.sum_congr rfl fun i _ => by rw [coef_curl _ hg hg2 i j l]]
  exact ang_ineq (azimuth m n) (fun a b => B.coef K (gradMode m n G a b) j l)



lemma omA_int {K : CellBox} (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (i : Fin 3) :
    AEStronglyMeasurable (fun p => curlComp (fun a b => angularGradMode m n H a b p) i) (volume.restrict K.rect) ∧
    IntegrableOn (fun p => K.lineWeight p.1 * ‖curlComp (fun a b => angularGradMode m n H a b p) i‖ ^ 2) K.rect := by
  obtain ⟨hm, hI⟩ := (modeSquareIntegrable K hK m v G H hs n (curlCoef i)).2.2 1
  have et : comboThird (curlCoef i) m n H 1 = fun p => curlComp (fun a b => modeThird m n H a b 1 p) i :=
    funext fun p => curl_sum i _
  rw [et] at hm hI
  beta_reduce at hI
  have ec : ∀ p : ℝ × ℝ, curlComp (fun a b => angularGradMode m n H a b p) i =
      (p.1 : ℂ) * curlComp (fun a b => modeThird m n H a b 1 p) i := fun p => curl_mul i (p.1 : ℂ) _
  simp only [ec]
  have hmA : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 : ℂ) * curlComp (fun a b => modeThird m n H a b 1 p) i)
      (volume.restrict K.rect) :=
    (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul hm
  refine ⟨hmA, ?_⟩
  have r2p : 0 < K.r₂ := lt_of_le_of_lt hK.r_order.1 hK.r_order.2
  refine Integrable.mono' (hI.const_mul (K.r₂ * (K.r₂ + 1)))
    (((CellSharpBoundInternal.lw_cont K).comp continuous_fst).aestronglyMeasurable.mul (hmA.norm.pow 2)) ?_
  refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have h1 : K.r₁ ≤ p.1 := hp.1.1
  have h2 : p.1 ≤ K.r₂ := hp.1.2
  have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 h1
  have w0 := lw_nonneg (K := K) h1
  have x0 := sq_nonneg ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖
  have hb : K.lineWeight p.1 * p.1 ≤ K.r₂ * (K.r₂ + 1) := by
    unfold CellBox.lineWeight
    split_ifs
    · nlinarith
    · nlinarith
  rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, mul_pow]
  have : K.lineWeight p.1 * (p.1 ^ 2 * ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2)
      = (K.lineWeight p.1 * p.1) * (p.1 * ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hb (mul_nonneg h0 x0)

lemma poly_cont {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') : Continuous P := by
  obtain ⟨c, hc⟩ := hP
  have e : P = fun p : ℝ × ℝ => ∑ j, ∑ l, c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) := funext hc
  rw [e]
  fun_prop

lemma proj_mem (K : CellBox) (Q : ℕ) (F : ℝ × ℝ → ℂ) : K.proj Q Q F ∈ polyFn Q Q := by
  unfold CellBox.proj
  split_ifs with h
  · exact h.choose_spec.1
  · exact ⟨fun _ _ => 0, fun p => by simp⟩

lemma sub_int {K : CellBox} (F P : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) (hP : Continuous P) :
    AEStronglyMeasurable (fun p => F p - P p) (volume.restrict K.rect) ∧
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p - P p‖ ^ 2) K.rect := by
  have hm : AEStronglyMeasurable (fun p => F p - P p) (volume.restrict K.rect) := hF.sub hP.aestronglyMeasurable
  refine ⟨hm, ?_⟩
  have hc : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖P p‖ ^ 2) K.rect :=
    ((((CellSharpBoundInternal.lw_cont K).comp continuous_fst).mul (hP.norm.pow 2)).continuousOn).integrableOn_compact
      (CellSharpBoundInternal.rect_cpt K)
  refine Integrable.mono' ((hF2.const_mul 2).add (hc.const_mul 2))
    (((CellSharpBoundInternal.lw_cont K).comp continuous_fst).aestronglyMeasurable.mul (hm.norm.pow 2)) ?_
  refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have w0 := lw_nonneg (K := K) hp.1.1
  have t := norm_sub_le (F p) (P p)
  have n1 := norm_nonneg (F p)
  have n2 := norm_nonneg (P p)
  have n3 := norm_nonneg (F p - P p)
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  have : ‖F p - P p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * ‖P p‖ ^ 2 := by nlinarith [sq_nonneg (‖F p‖ - ‖P p‖)]
  nlinarith [mul_le_mul_of_nonneg_left this w0]

lemma ang_full {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (i : Fin 3) (T : Finset (ℕ × ℕ)) :
    (∑ jl ∈ T, ‖B.coef K (fun p => curlComp (fun a b => angularGradMode m n H a b p) i) jl.1 jl.2‖ ^ 2)
      ≤ K.normSqOn K.lineWeightFn (fun p => curlComp (fun a b => angularGradMode m n H a b p) i) := by
  obtain ⟨hm, hI⟩ := omA_int hK hs n i
  exact coefEnergy_fin hB _ hm hI T

lemma ang_tail {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (hP : PolyCoefTailStatement)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (Q : ℕ) (i : Fin 3) (T : Finset (ℕ × ℕ)) :
    (∑ jl ∈ T, if Q < max jl.1 jl.2 then
        ‖B.coef K (fun p => curlComp (fun a b => angularGradMode m n H a b p) i) jl.1 jl.2‖ ^ 2 else 0)
      ≤ K.tailNormSq Q (fun p => curlComp (fun a b => angularGradMode m n H a b p) i) := by
  obtain ⟨hm, hI⟩ := omA_int hK hs n i
  set F : ℝ × ℝ → ℂ := fun p => curlComp (fun a b => angularGradMode m n H a b p) i with hFdef
  have hPm := proj_mem K Q F
  have hPc := poly_cont hPm
  obtain ⟨hm', hI'⟩ := sub_int F (K.proj Q Q F) hm hI hPc
  have hPI : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖K.proj Q Q F p‖ ^ 2) K.rect :=
    ((((CellSharpBoundInternal.lw_cont K).comp continuous_fst).mul (hPc.norm.pow 2)).continuousOn).integrableOn_compact
      (CellSharpBoundInternal.rect_cpt K)
  have ecoef : ∀ jl : ℕ × ℕ, Q < max jl.1 jl.2 →
      B.coef K (fun p => F p - K.proj Q Q F p) jl.1 jl.2 = B.coef K F jl.1 jl.2 := by
    intro jl hjl
    have h0 := hP K B hK hB Q _ hPm jl.1 jl.2 hjl
    have iF := bas_int (B := B) F hm hI jl.1 jl.2
    have iP := bas_int (B := B) _ hPc.aestronglyMeasurable hPI jl.1 jl.2
    unfold CellBases.coef at h0 ⊢
    have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * (F p - K.proj Q Q F p) *
        ((B.radialPoly jl.1 p.1 * B.heightPoly jl.2 p.2 : ℝ) : ℂ)) = fun p =>
        (K.lineWeight p.1 : ℂ) * F p * ((B.radialPoly jl.1 p.1 * B.heightPoly jl.2 p.2 : ℝ) : ℂ) -
        (K.lineWeight p.1 : ℂ) * K.proj Q Q F p * ((B.radialPoly jl.1 p.1 * B.heightPoly jl.2 p.2 : ℝ) : ℂ) := by
      funext p; ring
    rw [e, integral_sub iF iP, h0, sub_zero]
  have hb := coefEnergy_fin hB _ hm' hI' (T.filter fun jl => Q < max jl.1 jl.2)
  rw [← Finset.sum_filter]
  unfold CellBox.tailNormSq CellBox.normSqOn CellBox.lineWeightFn
  refine le_trans (le_of_eq ?_) hb
  refine Finset.sum_congr rfl fun jl hjl => ?_
  rw [ecoef jl (Finset.mem_filter.1 hjl).2]

lemma rad_curl {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (hR : RadialTailStatement)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (Q : ℕ) (i : Fin 3) (T : Finset (ℕ × ℕ)) :
    (∑ jl ∈ T, (if Q < max jl.1 jl.2 then radialEigen K jl.1 *
        ‖B.coef K (fun p => curlComp (fun a b => gradMode m n G a b p) i) jl.1 jl.2‖ ^ 2 else 0)
      ≤ K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
          (fun p => curlComp (fun a b => radialGradMode m n H a b p) i - CellBox.radialDeriv
            (K.proj Q Q (fun p => curlComp (fun a b => gradMode m n G a b p) i)) p)) ∧
      (∑ jl ∈ T, radialEigen K jl.1 *
        ‖B.coef K (fun p => curlComp (fun a b => gradMode m n G a b p) i) jl.1 jl.2‖ ^ 2
      ≤ K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
          (fun p => curlComp (fun a b => radialGradMode m n H a b p) i)) := by
  obtain ⟨hF, hF2, hT⟩ := modeSquareIntegrable K hK m v G H hs n (curlCoef i)
  have eg : comboGrad (curlCoef i) m n G = fun p => curlComp (fun a b => gradMode m n G a b p) i :=
    funext fun p => curl_sum i _
  have et : ∀ c, comboThird (curlCoef i) m n H c = fun p => curlComp (fun a b => modeThird m n H a b c p) i :=
    fun c => funext fun p => curl_sum i _
  obtain ⟨hr, hr2⟩ := hT 0
  rw [eg] at hF hF2
  rw [et] at hr hr2
  have hw := fun ψ hψ h1 h2 => by
    have := modeRadialParts K hK m v G H hs n (curlCoef i) ψ hψ h1 h2
    rw [eg, et] at this
    exact this
  exact ⟨hR K B hK hB Q _ _ hF hr hF2 hr2 hw T, radial_full hK hB _ _ hr hr2 hw T⟩


lemma ht_curl {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (hZ : HeightTailStatement)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (Q : ℕ) (i : Fin 3) (T : Finset (ℕ × ℕ)) :
    (∑ jl ∈ T, (if Q < max jl.1 jl.2 then heightEigen K jl.2 *
        ‖B.coef K (fun p => curlComp (fun a b => gradMode m n G a b p) i) jl.1 jl.2‖ ^ 2 else 0)
      ≤ K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
          (fun p => curlComp (fun a b => heightGradMode m n H a b p) i - CellBox.heightDeriv
            (K.proj Q Q (fun p => curlComp (fun a b => gradMode m n G a b p) i)) p)) ∧
      (∑ jl ∈ T, heightEigen K jl.2 *
        ‖B.coef K (fun p => curlComp (fun a b => gradMode m n G a b p) i) jl.1 jl.2‖ ^ 2
      ≤ K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
          (fun p => curlComp (fun a b => heightGradMode m n H a b p) i)) := by
  obtain ⟨hF, hF2, hT⟩ := modeSquareIntegrable K hK m v G H hs n (curlCoef i)
  have eg : comboGrad (curlCoef i) m n G = fun p => curlComp (fun a b => gradMode m n G a b p) i :=
    funext fun p => curl_sum i _
  have et : ∀ c, comboThird (curlCoef i) m n H c = fun p => curlComp (fun a b => modeThird m n H a b c p) i :=
    fun c => funext fun p => curl_sum i _
  obtain ⟨hr, hr2⟩ := hT 2
  rw [eg] at hF hF2
  rw [et] at hr hr2
  have hw := fun ψ hψ h1 h2 => by
    have := modeHeightParts K hK m v G H hs n (curlCoef i) ψ hψ h1 h2
    rw [eg, et] at this
    exact this
  exact ⟨hZ K B hK hB Q _ _ hF hr hF2 hr2 hw T, height_full hK hB _ _ hr hr2 hw T⟩

lemma unres_pt {K : CellBox} (hK : IsCellBox K)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) :
    ∑ i : Fin 3, (K.fullGradWeight (fun p => curlComp (fun a b => radialGradMode m n H a b p) i)
        (fun p => curlComp (fun a b => heightGradMode m n H a b p) i)
      + K.angularWeight n * K.normSqOn K.lineWeightFn (fun p => curlComp (fun a b => angularGradMode m n H a b p) i))
      ≤ ∫ p in K.rect, p.1 * curlGradModeSq m n H p := by
  have hr := hK.r_order.2
  have hz := hK.z_order.2
  have r2p : 0 < K.r₂ := lt_of_le_of_lt hK.r_order.1 hr
  have hI : ∀ i c, IntegrableOn (fun p => p.1 * ‖curlComp (fun a b => modeThird m n H a b c p) i‖ ^ 2) K.rect := by
    intro i c
    have h := ((modeSquareIntegrable K hK m v G H hs n (curlCoef i)).2.2 c).2
    have et : comboThird (curlCoef i) m n H c = fun p => curlComp (fun a b => modeThird m n H a b c p) i :=
      funext fun p => curl_sum i _
    rw [et] at h
    exact h
  have eR : ∫ p in K.rect, p.1 * curlGradModeSq m n H p = ∑ i : Fin 3, ∑ c : Fin 3,
      ∫ p in K.rect, p.1 * ‖curlComp (fun a b => modeThird m n H a b c p) i‖ ^ 2 := by
    unfold curlGradModeSq
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun c _ => hI i c))]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun c _ => hI i c)
  have pA : ∀ p ∈ K.rect, K.innerRadius * K.lineWeight p.1 ≤ p.1 := by
    intro p hp
    have h1 : K.r₁ ≤ p.1 := hp.1.1
    unfold CellBox.innerRadius CellBox.lineWeight
    split_ifs with h
    · linarith
    · linarith
  have pB : ∀ p ∈ K.rect, K.angularWeight n * K.lineWeight p.1 * p.1 ^ 2 ≤ p.1 := by
    intro p hp
    have h1 : K.r₁ ≤ p.1 := hp.1.1
    have h2 : p.1 ≤ K.r₂ := hp.1.2
    have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 h1
    have q1 : K.r₂⁻¹ * p.1 ≤ 1 := by rw [inv_mul_le_iff₀ r2p]; linarith
    have q0 : 0 ≤ K.r₂⁻¹ * p.1 := by positivity
    unfold CellBox.angularWeight CellBox.lineWeight
    split_ifs with h h'
    · simp only [zero_mul]; exact h0
    · have : K.r₂⁻¹ ^ 2 * p.1 * p.1 ^ 2 = (K.r₂⁻¹ * p.1) ^ 2 * p.1 := by ring
      rw [this]
      have : (K.r₂⁻¹ * p.1) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    · have : K.r₂⁻¹ * 1 * p.1 ^ 2 = (K.r₂⁻¹ * p.1) * p.1 := by ring
      rw [this]
      nlinarith
  rw [eR]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Fin.sum_univ_three]
  unfold CellBox.fullGradWeight CellBox.normSqOn CellBox.lineWeightFn
  have iR0 := (iR_pos hK).le
  have a1 : K.innerRadius * ∫ p in K.rect, K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) *
      ‖curlComp (fun a b => radialGradMode m n H a b p) i‖ ^ 2
      ≤ ∫ p in K.rect, p.1 * ‖curlComp (fun a b => modeThird m n H a b 0 p) i‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hI i 0) ?_
    · refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
      have := refR_sq_le hr hp.1.1 hp.1.2
      have := lw_nonneg (K := K) hp.1.1
      positivity
    · refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
      have g0 := refR_sq_le hr hp.1.1 hp.1.2
      have g1 : 1 - K.refR p.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (K.refR p.1)]
      have w0 := lw_nonneg (K := K) hp.1.1
      have x0 := sq_nonneg ‖curlComp (fun a b => modeThird m n H a b 0 p) i‖
      have e := pA p hp
      have : K.innerRadius * (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) ≤ p.1 := by
        nlinarith [mul_nonneg iR0 w0]
      change K.innerRadius * (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) *
        ‖curlComp (fun a b => modeThird m n H a b 0 p) i‖ ^ 2) ≤ p.1 * ‖curlComp (fun a b => modeThird m n H a b 0 p) i‖ ^ 2
      nlinarith
  have a2 : K.innerRadius * ∫ p in K.rect, K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) *
      ‖curlComp (fun a b => heightGradMode m n H a b p) i‖ ^ 2
      ≤ ∫ p in K.rect, p.1 * ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hI i 2) ?_
    · refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
      have := refZ_sq_le hz hp.2.1 hp.2.2
      have := lw_nonneg (K := K) hp.1.1
      positivity
    · refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
      have g0 := refZ_sq_le hz hp.2.1 hp.2.2
      have g1 : 1 - K.refZ p.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (K.refZ p.2)]
      have w0 := lw_nonneg (K := K) hp.1.1
      have x0 := sq_nonneg ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖
      have e := pA p hp
      have : K.innerRadius * (K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) ≤ p.1 := by
        nlinarith [mul_nonneg iR0 w0]
      change K.innerRadius * (K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) *
        ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖ ^ 2) ≤ p.1 * ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖ ^ 2
      nlinarith
  have a3 : K.angularWeight n * ∫ p in K.rect, K.lineWeight p.1 *
      ‖curlComp (fun a b => angularGradMode m n H a b p) i‖ ^ 2
      ≤ ∫ p in K.rect, p.1 * ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2 := by
    have wn := angW_nonneg hK n
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hI i 1) ?_
    · refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
      have := lw_nonneg (K := K) hp.1.1
      positivity
    · refine (ae_restrict_iff' (CellSharpBoundInternal.rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
      have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
      have ec : curlComp (fun a b => angularGradMode m n H a b p) i =
          (p.1 : ℂ) * curlComp (fun a b => modeThird m n H a b 1 p) i := curl_mul i (p.1 : ℂ) _
      have x0 := sq_nonneg ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖
      have e := pB p hp
      change K.angularWeight n * (K.lineWeight p.1 * ‖curlComp (fun a b => angularGradMode m n H a b p) i‖ ^ 2)
        ≤ p.1 * ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2
      rw [ec, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, mul_pow]
      nlinarith
  linarith


end SharpEnergyVorticityIdentityInternal

namespace SharpEnergyVorticityIdentityInternal

open SharpCoefTailInternal CellSharpBoundInternal

lemma rad_ibp {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {j : ℕ} (hj : j ≠ 0) (a : ℕ) :
    (a : ℝ) * ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r * r ^ (a - 1)
      = radialEigen K j * ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * B.radialPoly j r * r ^ a := by
  have hr := hK.r_order.2
  have hu : ∀ x ∈ Set.uIcc K.r₁ K.r₂, HasDerivAt (fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r)
      (-(radialEigen K j) * K.lineWeight x * B.radialPoly j x) x := fun x _ => radial_hasDeriv hr hB hj x
  have hv : ∀ x ∈ Set.uIcc K.r₁ K.r₂, HasDerivAt (fun r : ℝ => r ^ a) ((a : ℝ) * x ^ (a - 1)) x :=
    fun x _ => hasDerivAt_pow a x
  have hu' : IntervalIntegrable (fun x => -(radialEigen K j) * K.lineWeight x * B.radialPoly j x) volume K.r₁ K.r₂ :=
    ((continuous_const.mul (lw_cont K)).mul (rp_cont B j)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x : ℝ => (a : ℝ) * x ^ (a - 1)) volume K.r₁ K.r₂ :=
    (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have e1 : K.lineWeight K.r₂ * (1 - K.refR K.r₂ ^ 2) * rd B j K.r₂ = 0 := by rw [refR_right K hr]; ring
  have e0 : K.lineWeight K.r₁ * (1 - K.refR K.r₁ ^ 2) * rd B j K.r₁ = 0 := by rw [refR_left K hr]; ring
  rw [e1, e0, zero_mul, zero_mul, sub_zero, zero_sub] at h
  rw [icc_interval _ hr.le, icc_interval _ hr.le, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  have l1 : ∫ r in K.r₁..K.r₂, (a : ℝ) * (K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r * r ^ (a - 1))
      = ∫ r in K.r₁..K.r₂, K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r * ((a : ℝ) * r ^ (a - 1)) := by
    congr 1; funext r; ring
  have l2 : ∫ r in K.r₁..K.r₂, radialEigen K j * (K.lineWeight r * B.radialPoly j r * r ^ a)
      = -∫ r in K.r₁..K.r₂, -(radialEigen K j) * K.lineWeight r * B.radialPoly j r * r ^ a := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext r; ring
  rw [l1, l2, h]

lemma ht_ibp {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {l : ℕ} (hl : l ≠ 0) (b : ℕ) :
    (b : ℝ) * ∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * hd B l z * z ^ (b - 1)
      = heightEigen K l * ∫ z in Set.Icc K.z₁ K.z₂, B.heightPoly l z * z ^ b := by
  have hz := hK.z_order.2
  have hu : ∀ x ∈ Set.uIcc K.z₁ K.z₂, HasDerivAt (fun z => (1 - K.refZ z ^ 2) * hd B l z)
      (-(heightEigen K l) * B.heightPoly l x) x := fun x _ => height_hasDeriv hz hB hl x
  have hv : ∀ x ∈ Set.uIcc K.z₁ K.z₂, HasDerivAt (fun z : ℝ => z ^ b) ((b : ℝ) * x ^ (b - 1)) x :=
    fun x _ => hasDerivAt_pow b x
  have hu' : IntervalIntegrable (fun x => -(heightEigen K l) * B.heightPoly l x) volume K.z₁ K.z₂ :=
    (continuous_const.mul (hp_cont B l)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x : ℝ => (b : ℝ) * x ^ (b - 1)) volume K.z₁ K.z₂ :=
    (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have e1 : (1 - K.refZ K.z₂ ^ 2) * hd B l K.z₂ = 0 := by rw [refZ_right K hz]; ring
  have e0 : (1 - K.refZ K.z₁ ^ 2) * hd B l K.z₁ = 0 := by rw [refZ_left K hz]; ring
  rw [e1, e0, zero_mul, zero_mul, sub_zero, zero_sub] at h
  rw [icc_interval _ hz.le, icc_interval _ hz.le, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  have l1 : ∫ z in K.z₁..K.z₂, (b : ℝ) * ((1 - K.refZ z ^ 2) * hd B l z * z ^ (b - 1))
      = ∫ z in K.z₁..K.z₂, (1 - K.refZ z ^ 2) * hd B l z * ((b : ℝ) * z ^ (b - 1)) := by
    congr 1; funext z; ring
  have l2 : ∫ z in K.z₁..K.z₂, heightEigen K l * (B.heightPoly l z * z ^ b)
      = -∫ z in K.z₁..K.z₂, -(heightEigen K l) * B.heightPoly l z * z ^ b := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext z; ring
  rw [l1, l2, h]

lemma rderiv_poly {d : ℕ} (cf : Fin (d + 1) → Fin (d + 1) → ℂ) (P : ℝ × ℝ → ℂ)
    (hP : ∀ p : ℝ × ℝ, P p = ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ))) (p : ℝ × ℝ) :
    CellBox.radialDeriv P p =
      ∑ a, ∑ b, cf a b * (((a : ℕ) : ℂ) * (p.1 : ℂ) ^ ((a : ℕ) - 1)) * ((p.2 : ℂ) ^ (b : ℕ)) := by
  unfold CellBox.radialDeriv
  have e : (fun r : ℝ => P (r, p.2)) = fun r : ℝ => ∑ a, ∑ b, cf a b * ((r : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ)) :=
    funext fun r => hP (r, p.2)
  rw [e]
  refine HasDerivAt.deriv ?_
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  exact (((hasDerivAt_pow (a : ℕ) ((p.1 : ℝ) : ℂ)).comp_ofReal).const_mul (cf a b)).mul_const _

lemma hderiv_poly {d : ℕ} (cf : Fin (d + 1) → Fin (d + 1) → ℂ) (P : ℝ × ℝ → ℂ)
    (hP : ∀ p : ℝ × ℝ, P p = ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ))) (p : ℝ × ℝ) :
    CellBox.heightDeriv P p =
      ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * (((b : ℕ) : ℂ) * (p.2 : ℂ) ^ ((b : ℕ) - 1)) := by
  unfold CellBox.heightDeriv
  have e : (fun z : ℝ => P (p.1, z)) = fun z : ℝ => ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((z : ℂ) ^ (b : ℕ)) :=
    funext fun z => hP (p.1, z)
  rw [e]
  refine HasDerivAt.deriv ?_
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  exact ((hasDerivAt_pow (b : ℕ) ((p.2 : ℝ) : ℂ)).comp_ofReal).const_mul (cf a b * ((p.1 : ℂ) ^ (a : ℕ)))

lemma poly_rad_zero {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {Q : ℕ}
    (cf : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (P : ℝ × ℝ → ℂ) (hP : ∀ p : ℝ × ℝ, P p = ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ)))
    {j l : ℕ} (hj : j ≠ 0) (hjl : Q < max j l) :
    ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * CellBox.radialDeriv P p *
      ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) = 0 := by
  have hw := lw_cont K
  have hrr := refR_cont K
  have hrd := rd_cont B j
  have hql := hp_cont B l
  have hcomp : IsCompact K.rect := rect_cpt K
  have hfun : ∀ p : ℝ × ℝ, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * CellBox.radialDeriv P p *
      ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
      = ∑ a : Fin (Q + 1), ∑ b : Fin (Q + 1), cf a b *
        (((((a : ℕ) : ℝ) * (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * rd B j p.1 * p.1 ^ ((a : ℕ) - 1)) : ℝ) : ℂ)
          * ((B.heightPoly l p.2 * p.2 ^ (b : ℕ) : ℝ) : ℂ)) := by
    intro p
    rw [rderiv_poly cf P hP p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [integral_const_mul]
      have hprod : ∫ p in K.rect, (((((a : ℕ) : ℝ) * (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * rd B j p.1
            * p.1 ^ ((a : ℕ) - 1)) : ℝ) : ℂ) * ((B.heightPoly l p.2 * p.2 ^ (b : ℕ) : ℝ) : ℂ))
          = (∫ r in Set.Icc K.r₁ K.r₂, ((((a : ℕ) : ℝ) * (K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r
              * r ^ ((a : ℕ) - 1)) : ℝ) : ℂ))
            * ∫ z in Set.Icc K.z₁ K.z₂, ((B.heightPoly l z * z ^ (b : ℕ) : ℝ) : ℂ) := by
        unfold CellBox.rect
        rw [Measure.volume_eq_prod]
        exact setIntegral_prod_mul (fun r => ((((a : ℕ) : ℝ) * (K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r
              * r ^ ((a : ℕ) - 1)) : ℝ) : ℂ))
          (fun z => ((B.heightPoly l z * z ^ (b : ℕ) : ℝ) : ℂ)) _ _
      rw [hprod, integral_complex_ofReal, integral_complex_ofReal]
      rcases lt_max_iff.mp hjl with h | h
      · rw [integral_const_mul, rad_ibp hK hB hj, MeshFarPolyInternal.radial_orth K B hB a j (by omega)]
        simp
      · rw [MeshFarPolyInternal.height_orth K B hB b l (by omega)]
        simp
    · intro b _
      exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))
  · intro a _
    exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))

lemma poly_ht_zero {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {Q : ℕ}
    (cf : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (P : ℝ × ℝ → ℂ) (hP : ∀ p : ℝ × ℝ, P p = ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ)) * ((p.2 : ℂ) ^ (b : ℕ)))
    {j l : ℕ} (hl : l ≠ 0) (hjl : Q < max j l) :
    ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * CellBox.heightDeriv P p *
      ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ) = 0 := by
  have hw := lw_cont K
  have hzz := refZ_cont K
  have hhd := hd_cont B l
  have hpj := rp_cont B j
  have hcomp : IsCompact K.rect := rect_cpt K
  have hfun : ∀ p : ℝ × ℝ, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * CellBox.heightDeriv P p *
      ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ)
      = ∑ a : Fin (Q + 1), ∑ b : Fin (Q + 1), cf a b *
        (((K.lineWeight p.1 * B.radialPoly j p.1 * p.1 ^ (a : ℕ) : ℝ) : ℂ)
          * ((((b : ℕ) : ℝ) * ((1 - K.refZ p.2 ^ 2) * hd B l p.2 * p.2 ^ ((b : ℕ) - 1)) : ℝ) : ℂ)) := by
    intro p
    rw [hderiv_poly cf P hP p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [integral_const_mul]
      have hprod : ∫ p in K.rect, (((K.lineWeight p.1 * B.radialPoly j p.1 * p.1 ^ (a : ℕ) : ℝ) : ℂ)
            * ((((b : ℕ) : ℝ) * ((1 - K.refZ p.2 ^ 2) * hd B l p.2 * p.2 ^ ((b : ℕ) - 1)) : ℝ) : ℂ))
          = (∫ r in Set.Icc K.r₁ K.r₂, ((K.lineWeight r * B.radialPoly j r * r ^ (a : ℕ) : ℝ) : ℂ))
            * ∫ z in Set.Icc K.z₁ K.z₂, ((((b : ℕ) : ℝ) * ((1 - K.refZ z ^ 2) * hd B l z * z ^ ((b : ℕ) - 1)) : ℝ) : ℂ) := by
        unfold CellBox.rect
        rw [Measure.volume_eq_prod]
        exact setIntegral_prod_mul (fun r => ((K.lineWeight r * B.radialPoly j r * r ^ (a : ℕ) : ℝ) : ℂ))
          (fun z => ((((b : ℕ) : ℝ) * ((1 - K.refZ z ^ 2) * hd B l z * z ^ ((b : ℕ) - 1)) : ℝ) : ℂ)) _ _
      rw [hprod, integral_complex_ofReal, integral_complex_ofReal]
      rcases lt_max_iff.mp hjl with h | h
      · rw [MeshFarPolyInternal.radial_orth K B hB a j (by omega)]
        simp
      · rw [integral_const_mul, ht_ibp hK hB hl, MeshFarPolyInternal.height_orth K B hB b l (by omega)]
        simp
    · intro b _
      exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))
  · intro a _
    exact (ContinuousOn.integrableOn_compact hcomp (Continuous.continuousOn (by fun_prop)))

lemma subW_int {K : CellBox} (W : ℝ × ℝ → ℝ) (hW : Continuous W) (hW0 : ∀ p ∈ K.rect, 0 ≤ W p)
    (F P : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => W p * ‖F p‖ ^ 2) K.rect) (hP : Continuous P) :
    AEStronglyMeasurable (fun p => F p - P p) (volume.restrict K.rect) ∧
    IntegrableOn (fun p => W p * ‖F p - P p‖ ^ 2) K.rect := by
  have hm : AEStronglyMeasurable (fun p => F p - P p) (volume.restrict K.rect) := hF.sub hP.aestronglyMeasurable
  refine ⟨hm, ?_⟩
  have hc : IntegrableOn (fun p : ℝ × ℝ => W p * ‖P p‖ ^ 2) K.rect :=
    ((hW.mul (hP.norm.pow 2)).continuousOn).integrableOn_compact (rect_cpt K)
  refine Integrable.mono' ((hF2.const_mul 2).add (hc.const_mul 2))
    (hW.aestronglyMeasurable.mul (hm.norm.pow 2)) ?_
  refine (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have w0 := hW0 p hp
  have t := norm_sub_le (F p) (P p)
  have n1 := norm_nonneg (F p)
  have n2 := norm_nonneg (P p)
  have n3 := norm_nonneg (F p - P p)
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  have : ‖F p - P p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * ‖P p‖ ^ 2 := by nlinarith [sq_nonneg (‖F p‖ - ‖P p‖)]
  nlinarith [mul_le_mul_of_nonneg_left this w0]

lemma radial_tail : RadialTailStatement := by
  intro K B hK hB Q F Fr hF hFr hF2 hFr2 hw T
  have hr := hK.r_order.2
  obtain ⟨cf, hcf⟩ := proj_mem K Q F
  have hPr : Continuous (CellBox.radialDeriv (K.proj Q Q F)) := by
    rw [show CellBox.radialDeriv (K.proj Q Q F) = fun p : ℝ × ℝ => ∑ a, ∑ b, cf a b *
      (((a : ℕ) : ℂ) * (p.1 : ℂ) ^ ((a : ℕ) - 1)) * ((p.2 : ℂ) ^ (b : ℕ)) from funext (rderiv_poly cf _ hcf)]
    fun_prop
  have hWc : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2))
  have hW0 : ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) := fun p hp =>
    mul_nonneg (lw_nonneg hp.1.1) (refR_sq_le hr hp.1.1 hp.1.2)
  have hFrW : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * ‖Fr p‖ ^ 2) K.rect :=
    wmono _ hFr _ (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2)) (gR01 hK) (rmono hK _ hFr hFr2)
  obtain ⟨hm', hI'⟩ := subW_int _ hWc hW0 Fr _ hFr hFrW hPr
  have hb := rad_fin hK hB F (fun p => Fr p - CellBox.radialDeriv (K.proj Q Q F) p) hm' hI'
    (T.filter fun jl => Q < max jl.1 jl.2) (fun jl hjl hj => by
      have htail := (Finset.mem_filter.1 hjl).2
      rw [rad_id hK hB F Fr hw jl.1 jl.2 hj]
      have i1 := g_int' K _ hWc hW0 (fun jl p => rd B jl.1 p.1 * B.heightPoly jl.2 p.2)
        (fun _ => ((rd_cont B _).comp continuous_fst).mul ((hp_cont B _).comp continuous_snd)) Fr hFr hFrW jl
      have i2 : IntegrableOn (fun p : ℝ × ℝ => ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) *
          CellBox.radialDeriv (K.proj Q Q F) p * ((rd B jl.1 p.1 * B.heightPoly jl.2 p.2 : ℝ) : ℂ)) K.rect :=
        ContinuousOn.integrableOn_compact (rect_cpt K) (Continuous.continuousOn (by
          have := rd_cont B jl.1
          have := hp_cont B jl.2
          fun_prop))
      have e : (fun p : ℝ × ℝ => ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) *
          (Fr p - CellBox.radialDeriv (K.proj Q Q F) p) * ((rd B jl.1 p.1 * B.heightPoly jl.2 p.2 : ℝ) : ℂ)) =
          fun p => ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * Fr p *
            ((rd B jl.1 p.1 * B.heightPoly jl.2 p.2 : ℝ) : ℂ) -
          ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * CellBox.radialDeriv (K.proj Q Q F) p *
            ((rd B jl.1 p.1 * B.heightPoly jl.2 p.2 : ℝ) : ℂ) := by
        funext p; ring
      rw [e, integral_sub i1 i2, poly_rad_zero hK hB cf _ hcf hj htail, sub_zero])
  rw [← Finset.sum_filter]
  unfold CellBox.normSqOn
  exact hb

lemma height_tail : HeightTailStatement := by
  intro K B hK hB Q F Fz hF hFz hF2 hFz2 hw T
  have hz := hK.z_order.2
  obtain ⟨cf, hcf⟩ := proj_mem K Q F
  have hPz : Continuous (CellBox.heightDeriv (K.proj Q Q F)) := by
    rw [show CellBox.heightDeriv (K.proj Q Q F) = fun p : ℝ × ℝ => ∑ a, ∑ b, cf a b * ((p.1 : ℂ) ^ (a : ℕ))
      * (((b : ℕ) : ℂ) * (p.2 : ℂ) ^ ((b : ℕ) - 1)) from funext (hderiv_poly cf _ hcf)]
    fun_prop
  have hWc : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2))
  have hW0 : ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) := fun p hp =>
    mul_nonneg (lw_nonneg hp.1.1) (refZ_sq_le hz hp.2.1 hp.2.2)
  have hFzW : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) * ‖Fz p‖ ^ 2) K.rect :=
    wmono _ hFz _ (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2)) (gZ01 hK) (rmono hK _ hFz hFz2)
  obtain ⟨hm', hI'⟩ := subW_int _ hWc hW0 Fz _ hFz hFzW hPz
  have hb := ht_fin hK hB F (fun p => Fz p - CellBox.heightDeriv (K.proj Q Q F) p) hm' hI'
    (T.filter fun jl => Q < max jl.1 jl.2) (fun jl hjl hl => by
      have htail := (Finset.mem_filter.1 hjl).2
      rw [ht_id hK hB F Fz hw jl.1 jl.2 hl]
      have i1 := g_int' K _ hWc hW0 (fun jl p => B.radialPoly jl.1 p.1 * hd B jl.2 p.2)
        (fun _ => ((rp_cont B _).comp continuous_fst).mul ((hd_cont B _).comp continuous_snd)) Fz hFz hFzW jl
      have i2 : IntegrableOn (fun p : ℝ × ℝ => ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) *
          CellBox.heightDeriv (K.proj Q Q F) p * ((B.radialPoly jl.1 p.1 * hd B jl.2 p.2 : ℝ) : ℂ)) K.rect :=
        ContinuousOn.integrableOn_compact (rect_cpt K) (Continuous.continuousOn (by
          have := rp_cont B jl.1
          have := hd_cont B jl.2
          fun_prop))
      have e : (fun p : ℝ × ℝ => ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) *
          (Fz p - CellBox.heightDeriv (K.proj Q Q F) p) * ((B.radialPoly jl.1 p.1 * hd B jl.2 p.2 : ℝ) : ℂ)) =
          fun p => ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * Fz p *
            ((B.radialPoly jl.1 p.1 * hd B jl.2 p.2 : ℝ) : ℂ) -
          ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * CellBox.heightDeriv (K.proj Q Q F) p *
            ((B.radialPoly jl.1 p.1 * hd B jl.2 p.2 : ℝ) : ℂ) := by
        funext p; ring
      rw [e, integral_sub i1 i2, poly_ht_zero hK hB cf _ hcf hl htail, sub_zero])
  rw [← Finset.sum_filter]
  unfold CellBox.normSqOn
  exact hb

lemma poly_coef_tail : PolyCoefTailStatement := fun K B _ hB Q P hP j l h =>
  MeshFarPolyInternal.coef_poly_far K B hB Q P hP j l h

end SharpEnergyVorticityIdentityInternal

namespace SharpEnergyVorticityIdentityInternal

open ResolvedEnergyInternal SharpCoefTailInternal CellSharpBoundInternal

lemma term_bound (iR lamj mul w mm anti : ℝ) (C Aa : Fin 3 → ℝ) (h2 : 2 * anti = ∑ i, C i)
    (hang : mm * ∑ i, C i ≤ ∑ i, Aa i) (hw : 0 ≤ w) :
    2 * ((iR * (lamj + mul) + w * mm) * anti) ≤
      ∑ i : Fin 3, (iR * (lamj * C i) + iR * (mul * C i) + w * Aa i) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have h3 := mul_le_mul_of_nonneg_left hang hw
  have e : 2 * ((iR * (lamj + mul) + w * mm) * anti) = (iR * (lamj + mul) + w * mm) * (2 * anti) := by ring
  rw [e, h2]
  nlinarith

end SharpEnergyVorticityIdentityInternal

open Classical SharpEnergyVorticityIdentityInternal in
theorem modeVorticityIdentity_of (hP : PolyCoefTailStatement) (hR : RadialTailStatement) (hZ : HeightTailStatement) :
    ModeVorticityIdentityStatement := by
  have hA := angular_relation
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx n
  have hK := hd.box
  have hB := hd.bases
  have hs := hx.1
  set Q := S.degHigh with hQ
  set om : Fin 3 → ℝ × ℝ → ℂ := fun i p => curlComp (fun a b => gradMode c.order n x.2.1 a b p) i with hom
  set omA : Fin 3 → ℝ × ℝ → ℂ := fun i p => curlComp (fun a b => angularGradMode c.order n x.2.2.1 a b p) i
    with homA
  set C : Fin 3 → ℕ × ℕ → ℝ := fun i jl => ‖B.coef K (om i) jl.1 jl.2‖ ^ 2 with hC
  set Aa : Fin 3 → ℕ × ℕ → ℝ := fun i jl => ‖B.coef K (omA i) jl.1 jl.2‖ ^ 2 with hAa
  have hiR := iR_pos hK
  have hwn := angW_nonneg hK n
  have e2 : ∀ jl : ℕ × ℕ, 2 * antiCoefSq c K B x n jl = ∑ i, C i jl := fun jl =>
    two_anti hK hs n jl.1 jl.2
  have eA : ∀ jl : ℕ × ℕ, (max (modeNumber c.order n - 1) 0) ^ 2 * ∑ i, C i jl ≤ ∑ i, Aa i jl := fun jl =>
    ang_coef hK hA hs n jl.1 jl.2
  have hT : ∀ jl : ℕ × ℕ, (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl * 2 ≤
      ∑ i : Fin 3, (K.innerRadius * (radialEigen K jl.1 * C i jl) + K.innerRadius * (heightEigen K jl.2 * C i jl)
        + K.angularWeight n * Aa i jl) := by
    intro jl
    have := term_bound K.innerRadius (radialEigen K jl.1) (heightEigen K jl.2) (K.angularWeight n)
      ((max (modeNumber c.order n - 1) 0) ^ 2) (antiCoefSq c K B x n jl) (fun i => C i jl) (fun i => Aa i jl)
      (e2 jl) (eA jl) hwn
    unfold CellScalars.tailLam antiShift
    linarith
  have hnn : ∀ jl : ℕ × ℕ, 0 ≤ (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl := by
    intro jl
    have a0 : 0 ≤ antiCoefSq c K B x n jl := by unfold antiCoefSq antiSq; positivity
    have t0 : 0 ≤ CellScalars.tailLam K jl.1 jl.2 := by
      unfold CellScalars.tailLam
      exact mul_nonneg hiR.le (add_nonneg (SharpCoefTailInternal.radialEigen_nonneg _) (SharpCoefTailInternal.heightEigen_nonneg _))
    have s0 : 0 ≤ antiShift c K n := by unfold antiShift; exact mul_nonneg hwn (sq_nonneg _)
    positivity
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have hidx : ∀ jl : ℕ × ℕ, strainIdx S n jl ↔ Q < max jl.1 jl.2 := by
      intro jl; simp [strainIdx, hn, hQ]
    rw [← tsum_mul_left]
    refine Real.tsum_le_of_sum_le (fun jl => ?_) (fun T => ?_)
    · dsimp only
      split_ifs
      · exact mul_nonneg two_pos.le (hnn jl)
      · simp
    calc ∑ jl ∈ T, 2 * (if strainIdx S n jl then
            (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∑ jl ∈ T, ∑ i : Fin 3,
            (K.innerRadius * (if Q < max jl.1 jl.2 then radialEigen K jl.1 * C i jl else 0)
              + K.innerRadius * (if Q < max jl.1 jl.2 then heightEigen K jl.2 * C i jl else 0)
              + K.angularWeight n * (if Q < max jl.1 jl.2 then Aa i jl else 0)) := by
          refine Finset.sum_le_sum fun jl _ => ?_
          by_cases h : Q < max jl.1 jl.2
          · rw [if_pos ((hidx jl).2 h)]
            simp only [if_pos h]
            linarith [hT jl]
          · rw [if_neg (fun h' => h ((hidx jl).1 h'))]
            simp only [if_neg h, mul_zero, add_zero, Finset.sum_const_zero, le_refl]
      _ = ∑ i : Fin 3, ∑ jl ∈ T,
            (K.innerRadius * (if Q < max jl.1 jl.2 then radialEigen K jl.1 * C i jl else 0)
              + K.innerRadius * (if Q < max jl.1 jl.2 then heightEigen K jl.2 * C i jl else 0)
              + K.angularWeight n * (if Q < max jl.1 jl.2 then Aa i jl else 0)) := Finset.sum_comm
      _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          have r1 := (rad_curl hK hB hR hs n Q i T).1
          have r2 := (ht_curl hK hB hZ hs n Q i T).1
          have r3 := ang_tail hK hB hP hs n Q i T
          unfold CellBox.tailGradWeight
          have := mul_le_mul_of_nonneg_left r3 hwn
          nlinarith [mul_le_mul_of_nonneg_left r1 hiR.le, mul_le_mul_of_nonneg_left r2 hiR.le]
  · have hidx : ∀ jl : ℕ × ℕ, strainIdx S n jl := fun jl => Or.inl hn
    refine le_trans ?_ (unres_pt hK hs n)
    rw [← tsum_mul_left]
    refine Real.tsum_le_of_sum_le (fun jl => ?_) (fun T => ?_)
    · dsimp only
      split_ifs
      · exact mul_nonneg two_pos.le (hnn jl)
      · simp
    calc ∑ jl ∈ T, 2 * (if strainIdx S n jl then
            (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∑ jl ∈ T, ∑ i : Fin 3,
            (K.innerRadius * (radialEigen K jl.1 * C i jl) + K.innerRadius * (heightEigen K jl.2 * C i jl)
              + K.angularWeight n * Aa i jl) := by
          refine Finset.sum_le_sum fun jl _ => ?_
          rw [if_pos (hidx jl)]
          linarith [hT jl]
      _ = ∑ i : Fin 3, ∑ jl ∈ T,
            (K.innerRadius * (radialEigen K jl.1 * C i jl) + K.innerRadius * (heightEigen K jl.2 * C i jl)
              + K.angularWeight n * Aa i jl) := Finset.sum_comm
      _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          have r1 := (rad_curl hK hB hR hs n Q i T).2
          have r2 := (ht_curl hK hB hZ hs n Q i T).2
          have r3 := ang_full hK hB hs n i T
          unfold CellBox.fullGradWeight
          have := mul_le_mul_of_nonneg_left r3 hwn
          nlinarith [mul_le_mul_of_nonneg_left r1 hiR.le, mul_le_mul_of_nonneg_left r2 hiR.le]


open SharpEnergyVorticityIdentityInternal in
theorem modeVorticityIdentity_holds : ModeVorticityIdentityStatement :=
  modeVorticityIdentity_of poly_coef_tail radial_tail height_tail

end Breakdown.CellCert.CellAnalysis
