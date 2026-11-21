import Breakdown.CertCell.RowsMatchNormalLine
import Breakdown.CertCell.LocalFaceTurn
import Breakdown.CertCell.LocalFaceTangent
import Breakdown.CertCell.LocalFaceTraceFree
import Breakdown.CertCell.LocalFaceHeight
import Breakdown.CertCell.LocalModeWeak
import Breakdown.CertCell.LocalModeIntegrable

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.SegmentNormal

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula LocalField
  LocalField.Internal.FaceTraceFree SegmentLine

namespace Internal

theorem edgeSign_mul_self (c o : ℝ) : edgeSign c o * edgeSign c o = 1 := by
  unfold edgeSign
  split_ifs <;> norm_num

theorem edgeSign_of_lt {x y : ℝ} (h : y < x) : edgeSign x y = 1 := if_pos h

theorem edgeSign_of_gt {x y : ℝ} (h : x < y) : edgeSign x y = -1 := if_neg (not_lt.2 h.le)

theorem ae_fst_ne_zero : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have hnull : (volume : Measure (ℝ × ℝ)) ({0} ×ˢ Set.univ) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) hnull
  exact ⟨Set.mem_singleton_iff.mpr (not_not.mp hp), Set.mem_univ _⟩

theorem rect_measurable (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem ae_pos_on (K : CellBox) (hK : IsCellBox K) {P : ℝ × ℝ → Prop}
    (h : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → P p) : ∀ᵐ p ∂(volume.restrict K.rect), P p := by
  filter_upwards [ae_restrict_of_ae h, ae_restrict_of_ae ae_fst_ne_zero, ae_restrict_mem (rect_measurable K)]
    with p h1 h2 h3
  have h4 : K.r₁ ≤ p.1 := (show p ∈ Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc K.z₁ K.z₂ from h3).1.1
  exact h1 (lt_of_le_of_ne (hK.r_order.1.trans h4) (Ne.symm h2))

theorem offset_int (K : CellBox) {X : ℝ × ℝ → ℂ}
    (hX : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X p) K.rect) {o : ℝ} (hax : K.r₁ = 0 → o = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : Continuous φ) :
    IntegrableOn (fun p => ((p.1 - o : ℝ) : ℂ) * X p * φ p) K.rect := by
  by_cases h : K.r₁ = 0
  · refine (hX.mul_continuousOn hφ.continuousOn (rect_compact K)).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [CellBox.lineWeight, h, if_true, hax h, sub_zero]
  · have hX1 : IntegrableOn X K.rect := by
      refine hX.congr_fun (fun p _ => ?_) (rect_measurable K)
      simp only [CellBox.lineWeight, h, if_false, Complex.ofReal_one, one_mul]
    have hc : Continuous (fun p : ℝ × ℝ => ((p.1 - o : ℝ) : ℂ) * φ p) :=
      (Complex.continuous_ofReal.comp (continuous_fst.sub continuous_const)).mul hφ
    refine (hX1.mul_continuousOn hc.continuousOn (rect_compact K)).congr_fun (fun p _ => ?_) (rect_measurable K)
    ring

theorem turn_point (c o r : ℝ) (hc : c ≠ 0) (hco : c - o ≠ 0) (F dF W dW T : ℂ)
    (hW : (r : ℂ) * F = W) (hdW : (r : ℂ) * dF = dW - F) :
    ((((1 / (c - o) : ℝ)) : ℂ) * F + (((r - o) / (c - o) : ℝ) : ℂ) * dF) * T =
      ((1 / c : ℝ) : ℂ) * (((((1 / (c - o) : ℝ)) : ℂ) * W + (((r - o) / (c - o) : ℝ) : ℂ) * dW) * T)
        + ((((c + o - 2 * r) / (c * (c - o)) : ℝ) : ℂ) * F
          + ((((r - o) * (c - r)) / (c * (c - o)) : ℝ) : ℂ) * dF) * T := by
  subst hW
  have hdW' : dW = (r : ℂ) * dF + F := by linear_combination (-1 : ℂ) * hdW
  subst hdW'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hco' : (c : ℂ) - (o : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast hco
  push_cast
  field_simp
  ring

theorem strip_turn (K : CellBox) (hK : IsCellBox K) (c o : ℝ)
    (hco : (c = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) ∨ (c = K.r₂ ∧ o = K.r₁))
    (F dF V0 V1 G0 G1 : ℝ × ℝ → ℂ) (α β : ℂ) (t : ℝ → ℝ) (ht : Continuous t)
    (hF : ∀ᵐ p ∂(volume.restrict K.rect), (p.1 : ℂ) * F p = α * V0 p + β * V1 p)
    (hdF : ∀ᵐ p ∂(volume.restrict K.rect), (p.1 : ℂ) * dF p = α * G0 p + β * G1 p - F p)
    (hV0 : IntegrableOn V0 K.rect) (hV1 : IntegrableOn V1 K.rect)
    (hG0 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * G0 p) K.rect)
    (hG1 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * G1 p) K.rect)
    (hFi : IntegrableOn F K.rect)
    (hdFi : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * dF p) K.rect)
    (hW : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 →
      ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * F p + ((ψ p.1 : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ) = 0) :
    radialStripMoment c o K.z₁ K.z₂ F dF t =
      ((1 / c : ℝ) : ℂ) * (α * radialStripMoment c o K.z₁ K.z₂ V0 G0 t
        + β * radialStripMoment c o K.z₁ K.z₂ V1 G1 t) := by
  obtain ⟨⟨hr0, hr12⟩, _⟩ := hK
  have hS : Set.Icc (min c o) (max c o) ×ˢ Set.Icc K.z₁ K.z₂ = K.rect := by
    rcases hco with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl⟩
    · rw [min_eq_left hr12.le, max_eq_right hr12.le]
      rfl
    · rw [min_eq_right hr12.le, max_eq_left hr12.le]
      rfl
  have hc0 : c ≠ 0 := by
    rcases hco with ⟨rfl, _, h⟩ | ⟨rfl, _⟩
    · exact h
    · linarith
  have hcoz : c - o ≠ 0 := by
    rcases hco with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl⟩ <;> intro h <;> linarith
  have hax : K.r₁ = 0 → o = 0 := by
    rcases hco with ⟨_, _, h⟩ | ⟨_, rfl⟩
    · exact fun h' => absurd h' h
    · exact id
  have hcax : K.r₁ = 0 → c - K.r₂ = 0 ∨ True := fun _ => Or.inr trivial
  obtain ⟨η, hη⟩ : ∃ η : ℝ → ℝ, η = fun r => (r - o) * (c - r) / (c * (c - o)) := ⟨_, rfl⟩
  have hηd : ∀ r, HasDerivAt η ((c + o - 2 * r) / (c * (c - o))) r := by
    intro r
    rw [hη]
    have h := (((hasDerivAt_id' r).sub_const o).mul ((hasDerivAt_id' r).const_sub c)).div_const (c * (c - o))
    exact h.congr_deriv (by ring)
  have hηc : ContDiff ℝ 1 η := by
    rw [hη]
    exact ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id)).div_const _
  have hη1 : η K.r₁ = 0 := by
    rw [hη]
    rcases hco with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl⟩ <;> simp
  have hη2 : η K.r₂ = 0 := by
    rw [hη]
    rcases hco with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl⟩ <;> simp
  have hY0 := hW η hηc hη1 hη2
  rw [show deriv η = fun r => (c + o - 2 * r) / (c * (c - o)) from funext fun r => (hηd r).deriv] at hY0
  have hT : Continuous (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (ht.comp continuous_snd)
  have cst : ∀ a : ℝ, Continuous (fun p : ℝ × ℝ => ((a : ℝ) : ℂ) * ((t p.2 : ℝ) : ℂ)) := fun a =>
    continuous_const.mul hT
  have strip_int : ∀ V G : ℝ × ℝ → ℂ, IntegrableOn V K.rect →
      IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * G p) K.rect →
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * V p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G p)
        * ((t p.2 : ℝ) : ℂ)) K.rect := by
    intro V G hV hG
    have h1 := hV.mul_continuousOn (cst (1 / (c - o))).continuousOn (rect_compact K)
    have h2 := offset_int K hG hax _ (cst (1 / (c - o)))
    refine (h1.add h2).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [Pi.add_apply]
    push_cast
    ring
  have hX0 := strip_int V0 G0 hV0 hG0
  have hX1 := strip_int V1 G1 hV1 hG1
  have hYi : IntegrableOn (fun p : ℝ × ℝ => ((((c + o - 2 * p.1) / (c * (c - o)) : ℝ) : ℂ) * F p
      + ((η p.1 : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ)) K.rect := by
    have hd : Continuous (fun p : ℝ × ℝ => ((((c + o - 2 * p.1) / (c * (c - o)) : ℝ) : ℂ)) * ((t p.2 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp ((continuous_const.sub (continuous_const.mul continuous_fst)).div_const
        _)).mul hT
    have h1 := hFi.mul_continuousOn hd.continuousOn (rect_compact K)
    have h2 := offset_int K hdFi hax (fun p => ((((c - p.1) / (c * (c - o)) : ℝ) : ℂ)) * ((t p.2 : ℝ) : ℂ))
      ((Complex.continuous_ofReal.comp ((continuous_const.sub continuous_fst).div_const _)).mul hT)
    refine (h1.add h2).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [Pi.add_apply, hη]
    push_cast
    ring
  have hae : ∀ᵐ p ∂(volume.restrict K.rect),
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ) =
        ((1 / c : ℝ) : ℂ) * (α * (((((1 / (c - o) : ℝ)) : ℂ) * V0 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p)
            * ((t p.2 : ℝ) : ℂ))
          + β * (((((1 / (c - o) : ℝ)) : ℂ) * V1 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G1 p)
            * ((t p.2 : ℝ) : ℂ)))
        + ((((c + o - 2 * p.1) / (c * (c - o)) : ℝ) : ℂ) * F p + ((η p.1 : ℝ) : ℂ) * dF p)
          * ((t p.2 : ℝ) : ℂ) := by
    filter_upwards [hF, hdF] with p h1 h2
    rw [turn_point c o p.1 hc0 hcoz (F p) (dF p) _ _ ((t p.2 : ℝ) : ℂ) h1 h2]
    simp only [hη]
    ring
  have hA0 : IntegrableOn (fun p : ℝ × ℝ => α * (((((1 / (c - o) : ℝ)) : ℂ) * V0 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p) * ((t p.2 : ℝ) : ℂ))) K.rect := hX0.const_mul α
  have hA1 : IntegrableOn (fun p : ℝ × ℝ => β * (((((1 / (c - o) : ℝ)) : ℂ) * V1 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G1 p) * ((t p.2 : ℝ) : ℂ))) K.rect := hX1.const_mul β
  have hAB : IntegrableOn (fun p : ℝ × ℝ => ((1 / c : ℝ) : ℂ) * (α * (((((1 / (c - o) : ℝ)) : ℂ) * V0 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p) * ((t p.2 : ℝ) : ℂ))
      + β * (((((1 / (c - o) : ℝ)) : ℂ) * V1 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G1 p) * ((t p.2 : ℝ) : ℂ)))) K.rect :=
    (hA0.add hA1).const_mul _
  unfold radialStripMoment
  rw [hS, integral_congr_ae hae, integral_add hAB hYi, hY0, add_zero, integral_const_mul, integral_add hA0 hA1,
    integral_const_mul, integral_const_mul]
  ring

end Internal

end Breakdown.CertCell.SegmentNormal
