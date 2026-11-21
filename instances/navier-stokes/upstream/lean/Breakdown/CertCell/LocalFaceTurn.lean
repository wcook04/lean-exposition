import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.CertCell.LocalModeWeak
import Breakdown.CertCell.LocalModeIntegrable

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula

private theorem ae_fst_ne_zero : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have hnull : (volume : Measure (ℝ × ℝ)) ({0} ×ˢ Set.univ) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) hnull
  exact ⟨Set.mem_singleton_iff.mpr (not_not.mp hp), Set.mem_univ _⟩

private theorem rect_measurable (K : CellBox) : MeasurableSet K.rect :=
  measurableSet_Icc.prod measurableSet_Icc

private theorem rect_isCompact (K : CellBox) : IsCompact K.rect :=
  isCompact_Icc.prod isCompact_Icc

private theorem strip_pointwise_split (c o r : ℝ) (hc : c ≠ 0) (hco : c - o ≠ 0) (F dF W dW T : ℂ)
    (hW : (r : ℂ) * F = W) (hdW : (r : ℂ) * dF = dW - F) :
    ((((1 / (c - o) : ℝ)) : ℂ) * F + (((r - o) / (c - o) : ℝ) : ℂ) * dF) * T =
      ((1 / c : ℝ) : ℂ) * (((((1 / (c - o) : ℝ)) : ℂ) * W + (((r - o) / (c - o) : ℝ) : ℂ) * dW) * T)
        + ((((c + o - 2 * r) / (c * (c - o)) : ℝ) : ℂ) * F
          + ((((r - o) * (c - r)) / (c * (c - o)) : ℝ) : ℂ) * dF) * T := by
  have hdW' : dW = (r : ℂ) * dF + F := by linear_combination (-1 : ℂ) * hdW
  subst hW hdW'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hco' : (c : ℂ) - (o : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast hco
  push_cast
  field_simp
  ring

private theorem integrableOn_offset_weight (K : CellBox) (o : ℝ) (hax : K.r₁ = 0 → o = 0) (G : ℝ × ℝ → ℂ)
    (hG : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G p) K.rect) (μ : ℝ → ℝ) (hμ : Continuous μ)
    (T : ℝ × ℝ → ℂ) (hT : Continuous T) :
    IntegrableOn (fun p : ℝ × ℝ => ((((p.1 - o) * μ p.1 : ℝ)) : ℂ) * G p * T p) K.rect := by
  by_cases h : K.r₁ = 0
  · have hcont : Continuous (fun p : ℝ × ℝ => ((μ p.1 : ℝ) : ℂ) * T p) :=
      (Complex.continuous_ofReal.comp (hμ.comp continuous_fst)).mul hT
    refine (hG.mul_continuousOn hcont.continuousOn (rect_isCompact K)).congr_fun (fun p _ => ?_)
      (rect_measurable K)
    simp only [CellBox.lineWeight, h, if_true, hax h, sub_zero]
    push_cast
    ring
  · have hcont : Continuous (fun p : ℝ × ℝ => ((((p.1 - o) * μ p.1 : ℝ)) : ℂ) * T p) :=
      (Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).mul (hμ.comp continuous_fst))).mul hT
    refine (hG.mul_continuousOn hcont.continuousOn (rect_isCompact K)).congr_fun (fun p _ => ?_)
      (rect_measurable K)
    simp only [CellBox.lineWeight, h, if_false]
    push_cast
    ring

private theorem integrableOn_strip_integrand (K : CellBox) (c o : ℝ) (hax : K.r₁ = 0 → o = 0)
    (V G : ℝ × ℝ → ℂ) (hV : IntegrableOn V K.rect)
    (hG : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G p) K.rect) (t : ℝ → ℝ) (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * V p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G p)
      * ((t p.2 : ℝ) : ℂ)) K.rect := by
  have hT : Continuous (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (ht.comp continuous_snd)
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * (V p * ((t p.2 : ℝ) : ℂ))) K.rect :=
    (hV.mul_continuousOn hT.continuousOn (rect_isCompact K)).const_mul _
  have h2 := integrableOn_offset_weight K o hax G hG (fun _ => 1 / (c - o)) continuous_const _ hT
  refine (h1.add h2).congr_fun (fun p _ => ?_) (rect_measurable K)
  simp only [Pi.add_apply]
  push_cast
  ring

private theorem strip_integral_turn (K : CellBox) (hK : IsCellBox K) (c o : ℝ)
    (hco : (c = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) ∨ (c = K.r₂ ∧ o = K.r₁))
    (F dF V0 V1 G0 G1 : ℝ × ℝ → ℂ) (α β : ℂ) (t : ℝ → ℝ) (ht : Continuous t)
    (hF : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * F p = α * V0 p + β * V1 p)
    (hdF : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * dF p = α * G0 p + β * G1 p - F p)
    (hV0 : IntegrableOn V0 K.rect) (hV1 : IntegrableOn V1 K.rect)
    (hG0 : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G0 p) K.rect)
    (hG1 : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G1 p) K.rect)
    (hFi : IntegrableOn F K.rect)
    (hdFi : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * dF p) K.rect)
    (hW : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 →
      ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * F p + ((ψ p.1 : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ) = 0) :
    ∫ p in Set.Icc (min c o) (max c o) ×ˢ Set.Icc K.z₁ K.z₂,
        ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ) =
      ((1 / c : ℝ) : ℂ) * (α * (∫ p in Set.Icc (min c o) (max c o) ×ˢ Set.Icc K.z₁ K.z₂,
          ((((1 / (c - o) : ℝ)) : ℂ) * V0 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p) * ((t p.2 : ℝ) : ℂ))
        + β * ∫ p in Set.Icc (min c o) (max c o) ×ˢ Set.Icc K.z₁ K.z₂,
          ((((1 / (c - o) : ℝ)) : ℂ) * V1 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G1 p) * ((t p.2 : ℝ) : ℂ)) := by
  obtain ⟨⟨hr0, hr12⟩, _⟩ := hK
  have hS : Set.Icc (min c o) (max c o) ×ˢ Set.Icc K.z₁ K.z₂ = K.rect := by
    rcases hco with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl⟩
    · rw [min_eq_left hr12.le, max_eq_right hr12.le]
      rfl
    · rw [min_eq_right hr12.le, max_eq_left hr12.le]
      rfl
  have hc0 : 0 < c := by
    rcases hco with ⟨rfl, _, h⟩ | ⟨rfl, _⟩
    · exact lt_of_le_of_ne hr0 (Ne.symm h)
    · linarith
  have hcoz : c - o ≠ 0 := by
    rcases hco with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl⟩ <;> intro h <;> linarith
  have hax : K.r₁ = 0 → o = 0 := by
    rcases hco with ⟨_, _, h⟩ | ⟨_, rfl⟩
    · exact fun h' => absurd h' h
    · exact id
  set η : ℝ → ℝ := fun r => (r - o) * (c - r) / (c * (c - o)) with hη
  have hηd : ∀ r, deriv η r = (c + o - 2 * r) / (c * (c - o)) := by
    intro r
    have h : HasDerivAt η ((1 * (c - r) + (r - o) * (-1)) / (c * (c - o))) r :=
      (((hasDerivAt_id' r).sub_const o).mul ((hasDerivAt_id' r).const_sub c)).div_const (c * (c - o))
    rw [h.deriv]
    ring
  have hηc : ContDiff ℝ 1 η :=
    ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id)).div_const _
  have hη1 : η K.r₁ = 0 := by
    rcases hco with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl⟩ <;> simp [hη]
  have hη2 : η K.r₂ = 0 := by
    rcases hco with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl⟩ <;> simp [hη]
  have hY0 := hW η hηc hη1 hη2
  have hT : Continuous (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (ht.comp continuous_snd)
  have hYi : IntegrableOn (fun p : ℝ × ℝ => (((deriv η p.1 : ℝ) : ℂ) * F p + ((η p.1 : ℝ) : ℂ) * dF p)
      * ((t p.2 : ℝ) : ℂ)) K.rect := by
    have hd : Continuous (fun p : ℝ × ℝ => (((deriv η p.1 : ℝ) : ℂ)) * ((t p.2 : ℝ) : ℂ)) := by
      simp only [hηd]
      exact (Complex.continuous_ofReal.comp (((continuous_const.sub (continuous_const.mul continuous_fst)).div_const
        _))).mul hT
    have h1 := hFi.continuousOn_mul hd.continuousOn (rect_isCompact K)
    have h2 := integrableOn_offset_weight K o hax dF hdFi (fun r => (c - r) / (c * (c - o)))
      ((continuous_const.sub continuous_id).div_const _) _ hT
    refine (h1.add h2).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [Pi.add_apply, hη]
    push_cast
    ring
  have hX0 := integrableOn_strip_integrand K c o hax V0 G0 hV0 hG0 t ht
  have hX1 := integrableOn_strip_integrand K c o hax V1 G1 hV1 hG1 t ht
  have hae : ∀ᵐ p ∂(volume.restrict K.rect),
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ) =
        ((1 / c : ℝ) : ℂ) * (α * (((((1 / (c - o) : ℝ)) : ℂ) * V0 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p)
            * ((t p.2 : ℝ) : ℂ))
          + β * (((((1 / (c - o) : ℝ)) : ℂ) * V1 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G1 p)
            * ((t p.2 : ℝ) : ℂ)))
        + (((deriv η p.1 : ℝ) : ℂ) * F p + ((η p.1 : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ) := by
    filter_upwards [ae_restrict_mem (rect_measurable K), ae_restrict_of_ae hF, ae_restrict_of_ae hdF,
      ae_restrict_of_ae ae_fst_ne_zero] with p hp h1 h2 h3
    have hp1 : K.r₁ ≤ p.1 := (show p ∈ Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc K.z₁ K.z₂ from hp).1.1
    have hpos : 0 < p.1 := lt_of_le_of_ne (le_trans hr0 hp1) (Ne.symm h3)
    rw [strip_pointwise_split c o p.1 hc0.ne' hcoz (F p) (dF p) _ _ ((t p.2 : ℝ) : ℂ) (h1 hpos) (h2 hpos), hηd]
    simp only [hη]
    ring
  have hA0 : Integrable (fun p : ℝ × ℝ => α * (((((1 / (c - o) : ℝ)) : ℂ) * V0 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p) * ((t p.2 : ℝ) : ℂ))) (volume.restrict K.rect) :=
    hX0.const_mul α
  have hA1 : Integrable (fun p : ℝ × ℝ => β * (((((1 / (c - o) : ℝ)) : ℂ) * V1 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G1 p) * ((t p.2 : ℝ) : ℂ))) (volume.restrict K.rect) :=
    hX1.const_mul β
  have hAB : Integrable (fun p : ℝ × ℝ => ((1 / c : ℝ) : ℂ) * (α * (((((1 / (c - o) : ℝ)) : ℂ) * V0 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p) * ((t p.2 : ℝ) : ℂ))
      + β * (((((1 / (c - o) : ℝ)) : ℂ) * V1 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G1 p) * ((t p.2 : ℝ) : ℂ)))) (volume.restrict K.rect) :=
    (hA0.add hA1).const_mul _
  rw [hS, integral_congr_ae hae, integral_add hAB hYi, hY0, add_zero, integral_const_mul, integral_add hA0 hA1,
    integral_const_mul, integral_const_mul]

private theorem radialStripMoment_turn (K : CellBox) (hK : IsCellBox K) (c o : ℝ)
    (hco : (c = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) ∨ (c = K.r₂ ∧ o = K.r₁))
    (F dF V0 V1 G0 G1 : ℝ × ℝ → ℂ) (α β : ℂ) (t : ℝ → ℝ) (ht : Continuous t)
    (hF : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * F p = α * V0 p + β * V1 p)
    (hdF : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * dF p = α * G0 p + β * G1 p - F p)
    (hV0 : IntegrableOn V0 K.rect) (hV1 : IntegrableOn V1 K.rect)
    (hG0 : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G0 p) K.rect)
    (hG1 : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * G1 p) K.rect)
    (hFi : IntegrableOn F K.rect)
    (hdFi : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * dF p) K.rect)
    (hW : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 →
      ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * F p + ((ψ p.1 : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ) = 0) :
    radialStripMoment c o K.z₁ K.z₂ F dF t =
      ((1 / c : ℝ) : ℂ) * (α * radialStripMoment c o K.z₁ K.z₂ V0 G0 t
        + β * radialStripMoment c o K.z₁ K.z₂ V1 G1 t) := by
  unfold radialStripMoment
  rw [strip_integral_turn K hK c o hco F dF V0 V1 G0 G1 α β t ht hF hdF hV0 hV1 hG0 hG1 hFi hdFi hW]
  ring

section TurnSecond

open Set
open Breakdown.FracInternal.CornerModes LowEntry.Internal

private def turnKernel (m : ℕ) (n : ℤ) (a : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (frameThird θ M a 1 0 : ℂ)

private theorem turnKernel_continuous (m : ℕ) (n : ℤ) (a : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => turnKernel m n a q.1 q.2) := by
  unfold turnKernel
  refine (phase_cont m n).mul (Complex.continuous_ofReal.comp ?_)
  unfold frameThird frameUnit
  exact ((continuous_snd.clm_apply ((unit_cont 0).comp continuous_fst)).clm_apply
    ((unit_cont 1).comp continuous_fst)).inner ((unit_cont a).comp continuous_fst)

private theorem turnKernel_norm_le (m : ℕ) (n : ℤ) (a : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖turnKernel m n a θ M‖ ≤ ‖M‖ := by
  rw [turnKernel, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold frameThird
  refine (inner_unit_bound θ _ a).trans ?_
  have h0 : ‖frameUnit θ 0‖ ≤ 1 := unit_norm θ 0
  have h1 : ‖frameUnit θ 1‖ ≤ 1 := unit_norm θ 1
  calc ‖M (frameUnit θ 0) (frameUnit θ 1)‖ ≤ ‖M (frameUnit θ 0)‖ * ‖frameUnit θ 1‖ := (M _).le_opNorm _
    _ ≤ (‖M‖ * ‖frameUnit θ 0‖) * 1 := mul_le_mul (M.le_opNorm _) h1 (norm_nonneg _) (by positivity)
    _ ≤ ‖M‖ := by nlinarith [norm_nonneg M, norm_nonneg (frameUnit θ 0)]

private theorem modeThird_turn_eq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3)
    (p : ℝ × ℝ) :
    modeThird m n H a 1 0 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in Ioo (-Real.pi) Real.pi, turnKernel m n a θ (H (cylPoint p.1 θ p.2)) := by
  unfold modeThird
  rw [per_interval]
  · rfl
  · intro θ
    simp only [phase_per, cylPoint_per, frameThird, frameUnit, radialUnit, angularUnit, Real.cos_add_two_pi,
      Real.sin_add_two_pi]

private theorem compact_sub_offAxis_box (k : Set (ℝ × ℝ)) (hk : IsCompact k) (hU : ∀ p ∈ k, 0 < p.1) :
    ∃ δ R : ℝ, 0 < δ ∧ k ⊆ Icc δ R ×ˢ Icc (-R) R := by
  rcases k.eq_empty_or_nonempty with h | h
  · exact ⟨1, 0, one_pos, by simp [h]⟩
  obtain ⟨x, hx, hmin⟩ := hk.exists_isMinOn h continuous_fst.continuousOn
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  refine ⟨x.1, R, hU x hx, fun p hp => ?_⟩
  have hp' : ‖p‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hp
  have h1 : |p.1| ≤ R := by rw [← Real.norm_eq_abs]; exact (norm_fst_le p).trans hp'
  have h2 : |p.2| ≤ R := by rw [← Real.norm_eq_abs]; exact (norm_snd_le p).trans hp'
  exact ⟨⟨isMinOn_iff.1 hmin p hp, (abs_le.1 h1).2⟩, ⟨(abs_le.1 h2).1, (abs_le.1 h2).2⟩⟩

private theorem integrableOn_offAxis_of_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Space → E) (hX : LocallyIntegrable X volume) (φ : ℝ → E → ℂ)
    (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) (F : ℝ × ℝ → ℂ)
    (hF : ∀ p : ℝ × ℝ, F p = (1 / (2 * Real.pi) : ℂ) * ∫ θ in Ioo (-Real.pi) Real.pi, φ θ (X (cylPoint p.1 θ p.2)))
    (δ R : ℝ) (hδ : 0 < δ) : IntegrableOn F (Icc δ R ×ˢ Icc (-R) R) := by
  have hw0 : IntegrableOn (fun p : ℝ × ℝ => (1 / (2 * Real.pi) : ℂ) *
      ((p.1 : ℂ) * ∫ θ in Ioo (-Real.pi) Real.pi, φ θ (X (cylPoint p.1 θ p.2)))) (Icc 0 R ×ˢ Icc (-R) R) :=
    (weighted_int R R hX φ hφc hφb).const_mul _
  have hw : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc 0 R ×ˢ Icc (-R) R) :=
    hw0.congr_fun (fun p _ => by rw [hF]; ring) (measurableSet_Icc.prod measurableSet_Icc)
  have hm : AEStronglyMeasurable F (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) :=
    ((kmeas hX.aestronglyMeasurable φ hφc).const_mul (1 / (2 * Real.pi) : ℂ)).congr
      (Filter.Eventually.of_forall fun p => (hF p).symm)
  exact off_int δ R R hδ hw hm

private theorem integrable_test_mul (f : ℝ × ℝ → ℂ)
    (hf : ∀ δ R : ℝ, 0 < δ → IntegrableOn f (Icc δ R ×ˢ Icc (-R) R))
    (φ : ℝ × ℝ → ℝ) (hφ : Continuous φ) (hs : HasCompactSupport φ) (hpos : ∀ p ∈ tsupport φ, 0 < p.1) :
    Integrable (fun p => (φ p : ℂ) * f p) := by
  obtain ⟨δ, R, hδ, hsub⟩ := compact_sub_offAxis_box (tsupport φ) hs hpos
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Icc δ R ×ˢ Icc (-R) R) ?_ (fun p hp => ?_)
  · exact (hf δ R hδ).continuousOn_mul (Complex.continuous_ofReal.comp hφ).continuousOn
      (isCompact_Icc.prod isCompact_Icc)
  · have h0 : φ p = 0 := by
      by_contra h
      exact hp (hsub (subset_tsupport φ (Function.mem_support.2 h)))
    rw [h0, Complex.ofReal_zero, zero_mul]

private theorem locallyIntegrableOn_halfPlane (f : ℝ × ℝ → ℂ)
    (hf : ∀ δ R : ℝ, 0 < δ → IntegrableOn f (Icc δ R ×ˢ Icc (-R) R)) :
    LocallyIntegrableOn f {p : ℝ × ℝ | 0 < p.1} := by
  rw [locallyIntegrableOn_iff (isOpen_lt continuous_const continuous_fst).isLocallyClosed]
  intro k hk hkc
  obtain ⟨δ, R, hδ, hsub⟩ := compact_sub_offAxis_box k hkc (fun p hp => hk hp)
  exact (hf δ R hδ).mono_set hsub

private theorem space_eq_sum_basis (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

private theorem opNorm_le_sum_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Space →L[ℝ] E) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun u => ?_
  conv_lhs => rw [space_eq_sum_basis u]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (norm_nonneg _)

private theorem locallyIntegrable_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Space → (E →L[ℝ] F)) (hX : LocallyIntegrable X volume)
    (u : E) : LocallyIntegrable (fun y => X y u) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  refine (((hX.integrableOn_isCompact hk).norm).mul_const ‖u‖).mono'
    ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hX.aestronglyMeasurable).restrict
    (Filter.Eventually.of_forall fun y => (X y).le_opNorm u)

private theorem locallyIntegrable_second {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    LocallyIntegrable H volume := by
  have hij : ∀ i j : Fin 3, LocallyIntegrable (fun y => H y (unitVector i) (unitVector j)) volume := by
    intro i j
    have hmeas : AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
      ((continuous_id.clm_apply continuous_const).clm_apply continuous_const).comp_aestronglyMeasurable hm
    have hsq : Integrable (fun y => ‖H y (unitVector i) (unitVector j)‖ ^ 2) volume := by
      refine h2.mono' (hmeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖H y (unitVector i) (unitVector j)‖ ^ 2 ≤ ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2 :=
            Finset.single_le_sum (f := fun j' => ‖H y (unitVector i) (unitVector j')‖ ^ 2)
              (fun _ _ => by positivity) (Finset.mem_univ j)
        _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2 :=
            Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
    exact ((memLp_two_iff_integrable_sq_norm hmeas).2 hsq).locallyIntegrable (by norm_num)
  rw [locallyIntegrable_iff]
  intro k hk
  have hb : IntegrableOn (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖) k :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ((hij i j).integrableOn_isCompact hk).norm
  refine hb.mono' hm.restrict (Filter.Eventually.of_forall fun y => ?_)
  exact (opNorm_le_sum_basis (H y)).trans (Finset.sum_le_sum fun i _ => opNorm_le_sum_basis (H y (unitVector i)))

private def planeFrame (q : ℝ × ℝ) : Fin 3 → Space :=
  ![EuclideanSpace.single 0 q.1 + EuclideanSpace.single 1 q.2,
    EuclideanSpace.single 0 (-q.2) + EuclideanSpace.single 1 q.1, axialUnit]

private theorem planeFrame_circle (θ : ℝ) : planeFrame (Real.cos θ, Real.sin θ) = frameUnit θ := rfl

private theorem planeFrame_coord_smooth (a k : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => planeFrame q a k) := by
  fin_cases a <;> fin_cases k <;>
    simp [planeFrame, axialUnit] <;>
    first | exact contDiff_const | exact contDiff_fst | exact contDiff_snd | exact contDiff_snd.neg

private theorem planeFrame_smooth (a : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => planeFrame q a) :=
  (contDiff_piLp 2).2 fun k => planeFrame_coord_smooth a k

private def frameCoord (a : Fin 3) (q : ℝ × ℝ) : Space →L[ℝ] ℝ :=
  ∑ k : Fin 3, planeFrame q a k • EuclideanSpace.proj k

private theorem frameCoord_smooth (a : Fin 3) : ContDiff ℝ ∞ (frameCoord a) := by
  unfold frameCoord
  exact ContDiff.sum fun k _ => (planeFrame_coord_smooth a k).smul contDiff_const

private theorem frameCoord_circle (a : Fin 3) (θ : ℝ) (u : Space) :
    frameCoord a (Real.cos θ, Real.sin θ) u = inner ℝ u (frameUnit θ a) := by
  simp [frameCoord, planeFrame_circle, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private def angularColumnCoord (a : Fin 3) (q : ℝ × ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (frameCoord a q).comp (ContinuousLinearMap.apply ℝ Space (planeFrame q 1))

private theorem angularColumnCoord_smooth (a : Fin 3) : ContDiff ℝ ∞ (angularColumnCoord a) :=
  (frameCoord_smooth a).clm_comp ((ContinuousLinearMap.apply ℝ Space).contDiff.comp (planeFrame_smooth 1))

private theorem angularColumnCoord_circle (a : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    angularColumnCoord a (Real.cos θ, Real.sin θ) M = inner ℝ (M (frameUnit θ 1)) (frameUnit θ a) := by
  simp only [angularColumnCoord, planeFrame_circle, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  exact frameCoord_circle a θ _

private theorem weak_identity_scale {A B c d : ℝ × ℝ → ℂ} (k : ℂ) (h : ∫ p, c p * A p = -∫ p, d p * B p) :
    ∫ p, c p * (k * A p) = -∫ p, d p * (k * B p) := by
  have e1 : (fun p => c p * (k * A p)) = fun p => k * (c p * A p) := funext fun p => by ring
  have e2 : (fun p => d p * (k * B p)) = fun p => k * (d p * B p) := funext fun p => by ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h, mul_neg]

private theorem angularColumn_weak (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a : Fin 3)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * gradMode m n G a 1 p = -∫ p, (ψ p : ℂ) * modeThird m n H a 1 0 p := by
  have hG : LocallyIntegrable G volume :=
    (memLp_grad hs.measurable_gradient hs.gradient_two).locallyIntegrable (by norm_num)
  have hH : LocallyIntegrable H volume := locallyIntegrable_second hs.measurable_second hs.second_two
  have hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume :=
    fun j => locallyIntegrable_clm_apply H hH _
  have hweakG : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
    intro φ hφ j
    have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
      hG.integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
    have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
      (hHc j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
        (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
      intro i
      rw [neg_apply, ContinuousLinearMap.integral_apply i1, ContinuousLinearMap.integral_apply i2]
      simpa using hs.weak_second φ hφ i j
    refine ContinuousLinearMap.ext fun u => ?_
    rw [space_eq_sum_basis u]
    simp only [map_sum, map_smul, key]
  have hgm : ∀ p : ℝ × ℝ, gradMode m n G a 1 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (angularColumnCoord a (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [gradMode, modeMat, angularColumnCoord_circle]
    rfl
  have hth : ∀ p : ℝ × ℝ, modeThird m n H a 1 0 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (angularColumnCoord a (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ) := by
    intro p
    simp only [modeThird, angularColumnCoord_circle]
    rfl
  simp only [hgm, hth]
  exact weak_identity_scale _ (cylModeWeak (Space →L[ℝ] Space) G H hG hHc hweakG (angularColumnCoord a)
    (angularColumnCoord_smooth a) m n ψ hψ hc hpos).1

private theorem ae_radial_relation (F dF V0 V1 G0 G1 : ℝ × ℝ → ℂ) (α β : ℂ)
    (bF : ∀ δ R : ℝ, 0 < δ → IntegrableOn F (Icc δ R ×ˢ Icc (-R) R))
    (bdF : ∀ δ R : ℝ, 0 < δ → IntegrableOn dF (Icc δ R ×ˢ Icc (-R) R))
    (bV0 : ∀ δ R : ℝ, 0 < δ → IntegrableOn V0 (Icc δ R ×ˢ Icc (-R) R))
    (bV1 : ∀ δ R : ℝ, 0 < δ → IntegrableOn V1 (Icc δ R ×ˢ Icc (-R) R))
    (bG0 : ∀ δ R : ℝ, 0 < δ → IntegrableOn G0 (Icc δ R ×ˢ Icc (-R) R))
    (bG1 : ∀ δ R : ℝ, 0 < δ → IntegrableOn G1 (Icc δ R ×ˢ Icc (-R) R))
    (hA : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * F p = α * V0 p + β * V1 p)
    (wF : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * dF p)
    (w0 : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * V0 p = -∫ p, (ψ p : ℂ) * G0 p)
    (w1 : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * V1 p = -∫ p, (ψ p : ℂ) * G1 p) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * dF p = α * G0 p + β * G1 p - F p := by
  have hbox : ∀ δ R : ℝ, 0 < δ →
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p + F p - (α * G0 p + β * G1 p)) (Icc δ R ×ˢ Icc (-R) R) := by
    intro δ R hδ
    have h1 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Icc δ R ×ˢ Icc (-R) R) :=
      (bdF δ R hδ).continuousOn_mul (Complex.continuous_ofReal.comp continuous_fst).continuousOn
        (isCompact_Icc.prod isCompact_Icc)
    exact (h1.add (bF δ R hδ)).sub (((bG0 δ R hδ).const_mul α).add ((bG1 δ R hδ).const_mul β))
  have h0 := (isOpen_lt continuous_const continuous_fst).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_halfPlane _ hbox) (fun g hg hgc hgU => ?_)
  · filter_upwards [h0] with p hp hpos
    linear_combination hp hpos
  have hpos : ∀ p ∈ tsupport g, 0 < p.1 := fun p hp => hgU hp
  have hz : ∀ p : ℝ × ℝ, ¬ 0 < p.1 → fderiv ℝ g p = 0 := by
    intro p hp
    by_contra h
    exact hp (hpos p (support_fderiv_subset ℝ (Function.mem_support.2 h)))
  have hΨ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => q.1 * g q) := contDiff_fst.mul hg
  have hΨc : HasCompactSupport (fun q : ℝ × ℝ => q.1 * g q) := hgc.mul_left
  have hΨs : ∀ p ∈ tsupport (fun q : ℝ × ℝ => q.1 * g q), 0 < p.1 :=
    fun p hp => hpos p (tsupport_mul_subset_right hp)
  have hΨd : ∀ p : ℝ × ℝ, fderiv ℝ (fun q : ℝ × ℝ => q.1 * g q) p (1, 0) = p.1 * fderiv ℝ g p (1, 0) + g p := by
    intro p
    have h := (hasFDerivAt_fst (p := p) (𝕜 := ℝ)).mul ((hg.differentiable (by simp)) p).hasFDerivAt
    rw [show (fun q : ℝ × ℝ => q.1 * g q) = Prod.fst * g from rfl, h.fderiv]
    simp
  have hgd : ∀ u : ℝ × ℝ, Continuous (fun p => fderiv ℝ g p u) :=
    fun u => (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hΨd' : Continuous (fun p => fderiv ℝ (fun q : ℝ × ℝ => q.1 * g q) p (1, 0)) :=
    (hΨ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgs : ∀ p ∈ tsupport (fun p => fderiv ℝ g p (1, 0)), 0 < p.1 :=
    fun p hp => hpos p (tsupport_fderiv_apply_subset ℝ (1, 0) hp)
  have i1 := integrable_test_mul F bF _ hΨd' (hΨc.fderiv_apply (𝕜 := ℝ) (1, 0))
    (fun p hp => hΨs p (tsupport_fderiv_apply_subset ℝ (1, 0) hp))
  have i2 := integrable_test_mul dF bdF _ hΨ.continuous hΨc hΨs
  have i3 := integrable_test_mul V0 bV0 _ (hgd (1, 0)) (hgc.fderiv_apply (𝕜 := ℝ) (1, 0)) hgs
  have i4 := integrable_test_mul G0 bG0 g hg.continuous hgc hpos
  have i5 := integrable_test_mul V1 bV1 _ (hgd (1, 0)) (hgc.fderiv_apply (𝕜 := ℝ) (1, 0)) hgs
  have i6 := integrable_test_mul G1 bG1 g hg.continuous hgc hpos
  have j12 : Integrable (fun p => ((fderiv ℝ (fun q : ℝ × ℝ => q.1 * g q) p (1, 0) : ℝ) : ℂ) * F p
      + ((p.1 * g p : ℝ) : ℂ) * dF p) := i1.add i2
  have j34 : Integrable (fun p => α * (((fderiv ℝ g p (1, 0) : ℝ) : ℂ) * V0 p + (g p : ℂ) * G0 p)) :=
    (i3.add i4).const_mul α
  have j56 : Integrable (fun p => β * (((fderiv ℝ g p (1, 0) : ℝ) : ℂ) * V1 p + (g p : ℂ) * G1 p)) :=
    (i5.add i6).const_mul β
  have j1234 : Integrable (fun p => ((fderiv ℝ (fun q : ℝ × ℝ => q.1 * g q) p (1, 0) : ℝ) : ℂ) * F p
      + ((p.1 * g p : ℝ) : ℂ) * dF p - α * (((fderiv ℝ g p (1, 0) : ℝ) : ℂ) * V0 p + (g p : ℂ) * G0 p)) :=
    j12.sub j34
  have hae : ∀ᵐ p : ℝ × ℝ ∂volume, g p • ((p.1 : ℂ) * dF p + F p - (α * G0 p + β * G1 p)) =
      ((fderiv ℝ (fun q : ℝ × ℝ => q.1 * g q) p (1, 0) : ℝ) : ℂ) * F p + ((p.1 * g p : ℝ) : ℂ) * dF p
        - α * (((fderiv ℝ g p (1, 0) : ℝ) : ℂ) * V0 p + (g p : ℂ) * G0 p)
        - β * (((fderiv ℝ g p (1, 0) : ℝ) : ℂ) * V1 p + (g p : ℂ) * G1 p) := by
    filter_upwards [hA] with p hp
    have key : ((fderiv ℝ g p (1, 0) : ℝ) : ℂ) * ((p.1 : ℂ) * F p) =
        ((fderiv ℝ g p (1, 0) : ℝ) : ℂ) * (α * V0 p + β * V1 p) := by
      by_cases h : 0 < p.1
      · rw [hp h]
      · rw [hz p h]
        simp
    rw [hΨd p, Complex.real_smul]
    push_cast
    linear_combination (-1 : ℂ) * key
  rw [integral_congr_ae hae, integral_sub j1234 j56, integral_sub j12 j34, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_add i3 i4, integral_add i5 i6,
    wF _ hΨ hΨc hΨs, w0 g hg hgc hpos, w1 g hg hgc hpos]
  ring

theorem localTurnSecond : LocalTurnSecondStatement := by
  intro m v G H hs n
  have hv : LocallyIntegrable v volume := hs.velocity_six.locallyIntegrable (by norm_num)
  have hG : LocallyIntegrable G volume :=
    (memLp_grad hs.measurable_gradient hs.gradient_two).locallyIntegrable (by norm_num)
  have hH : LocallyIntegrable H volume := locallyIntegrable_second hs.measurable_second hs.second_two
  have bV : ∀ a : Fin 3, ∀ δ R : ℝ, 0 < δ →
      IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (Icc δ R ×ˢ Icc (-R) R) :=
    fun a δ R hδ => integrableOn_offAxis_of_kernel v hv (velKernel m n a) (velKernel_cont m n a)
      (velKernel_bound m n a) _ (fun p => modeVec_eq m n v a p) δ R hδ
  have bG : ∀ a b : Fin 3, ∀ δ R : ℝ, 0 < δ → IntegrableOn (gradMode m n G a b) (Icc δ R ×ˢ Icc (-R) R) :=
    fun a b δ R hδ => integrableOn_offAxis_of_kernel G hG (gradKernel m n a b) (gradKernel_cont m n a b)
      (gradKernel_bound m n a b) _ (fun p => gradMode_eq m n G a b p) δ R hδ
  have bT : ∀ a : Fin 3, ∀ δ R : ℝ, 0 < δ → IntegrableOn (modeThird m n H a 1 0) (Icc δ R ×ˢ Icc (-R) R) :=
    fun a δ R hδ => integrableOn_offAxis_of_kernel H hH (turnKernel m n a) (turnKernel_continuous m n a)
      (turnKernel_norm_le m n a) _ (fun p => modeThird_turn_eq m n H a p) δ R hδ
  have wT := angularColumn_weak m v G H hs n
  have wV : ∀ a : Fin 3, ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a = -∫ p, (ψ p : ℂ) * gradMode m n G a 0 p :=
    fun a ψ hψ hc hpos => (localModeWeakIdentity m v G H hs n a ψ hψ hc hpos).1
  have hAn := localAngularMode m v G H hs n
  have c0 := ae_radial_relation (gradMode m n G 0 1) (modeThird m n H 0 1 0) (fun p => modeVec m n v p.1 p.2 0)
    (fun p => modeVec m n v p.1 p.2 1) (gradMode m n G 0 0) (gradMode m n G 1 0)
    ((azimuth m n : ℂ) * Complex.I) (-1) (bG 0 1) (bT 0) (bV 0) (bV 1) (bG 0 0) (bG 1 0)
    (by filter_upwards [hAn] with p hp hpos; rw [(hp hpos).1]; ring) (wT 0) (wV 0) (wV 1)
  have c1 := ae_radial_relation (gradMode m n G 1 1) (modeThird m n H 1 1 0) (fun p => modeVec m n v p.1 p.2 1)
    (fun p => modeVec m n v p.1 p.2 0) (gradMode m n G 1 0) (gradMode m n G 0 0)
    ((azimuth m n : ℂ) * Complex.I) 1 (bG 1 1) (bT 1) (bV 1) (bV 0) (bG 1 0) (bG 0 0)
    (by filter_upwards [hAn] with p hp hpos; rw [(hp hpos).2.1]; ring) (wT 1) (wV 1) (wV 0)
  have c2 := ae_radial_relation (gradMode m n G 2 1) (modeThird m n H 2 1 0) (fun p => modeVec m n v p.1 p.2 2)
    (fun p => modeVec m n v p.1 p.2 0) (gradMode m n G 2 0) (gradMode m n G 0 0)
    ((azimuth m n : ℂ) * Complex.I) 0 (bG 2 1) (bT 2) (bV 2) (bV 0) (bG 2 0) (bG 0 0)
    (by filter_upwards [hAn] with p hp hpos; rw [(hp hpos).2.2]; ring) (wT 2) (wV 2) (wV 0)
  filter_upwards [c0, c1, c2] with p h0 h1 h2 hpos
  exact ⟨by rw [h0 hpos]; ring, by rw [h1 hpos]; ring, by rw [h2 hpos]; ring⟩

theorem localGradModeAxis : LocalGradModeAxisStatement :=
  fun m v G H hs n a b R Z => (localModeStripIntegrable m v G H hs n R (-Z) Z).2 a b

theorem localTurnRadialWeak : LocalTurnRadialWeakStatement := by
  intro K hK m v G H hs n a
  have hH : LocallyIntegrable H volume := locallyIntegrable_second hs.measurable_second hs.second_two
  have hF : ∀ R Z : ℝ, IntegrableOn (gradMode m n G a 1) (Icc 0 R ×ˢ Icc (-Z) Z) :=
    localGradModeAxis m v G H hs n a 1
  have hg : ∀ R Z : ℝ, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a 1 0 p)
      (Icc 0 R ×ˢ Icc (-Z) Z) := by
    intro R Z
    have hw : IntegrableOn (fun p : ℝ × ℝ => (1 / (2 * Real.pi) : ℂ) *
        ((p.1 : ℂ) * ∫ θ in Ioo (-Real.pi) Real.pi, turnKernel m n a θ (H (cylPoint p.1 θ p.2))))
        (Icc 0 R ×ˢ Icc (-Z) Z) :=
      (weighted_int R Z hH (turnKernel m n a) (turnKernel_continuous m n a) (turnKernel_norm_le m n a)).const_mul _
    refine hw.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    rw [modeThird_turn_eq]
    ring
  have hW := angularColumn_weak m v G H hs n a
  have h0 : 0 ≤ K.r₁ := hK.r_order.1
  have h12 : K.r₁ < K.r₂ := hK.r_order.2
  have hz0 : 0 ≤ K.z₁ := hK.z_order.1
  have hsub : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ := fun p hp =>
    ⟨⟨h0.trans hp.1.1, hp.1.2⟩, ⟨by linarith [hp.2.1, hp.2.2], hp.2.2⟩⟩
  have hFr : IntegrableOn (gradMode m n G a 1) K.rect := (hF K.r₂ K.z₂).mono_set hsub
  have hgm : AEStronglyMeasurable (modeThird m n H a 1 0) (volume.restrict K.rect) := by
    have h := ((kmeas hH.aestronglyMeasurable (turnKernel m n a) (turnKernel_continuous m n a)).mono_measure
      ((Measure.restrict_mono hsub le_rfl).trans (half_le K.r₂ K.z₂))).const_mul (1 / (2 * Real.pi) : ℂ)
    exact h.congr (Filter.Eventually.of_forall fun p => (modeThird_turn_eq m n H a p).symm)
  have hgr : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeThird m n H a 1 0 p) K.rect := by
    by_cases h : K.r₁ = 0
    · refine ((hg K.r₂ K.z₂).mono_set hsub).congr_fun (fun p _ => ?_) (rect_measurable K)
      simp only [CellBox.lineWeight, h, if_true]
    · have hδ : 0 < K.r₁ := lt_of_le_of_ne h0 (Ne.symm h)
      have hsub2 : K.rect ⊆ Icc K.r₁ (max K.r₂ K.z₂) ×ˢ Icc (-(max K.r₂ K.z₂)) (max K.r₂ K.z₂) :=
        fun p hp => ⟨⟨hp.1.1, hp.1.2.trans (le_max_left _ _)⟩,
          ⟨by linarith [hp.2.1, hp.2.2, le_max_right K.r₂ K.z₂], hp.2.2.trans (le_max_right _ _)⟩⟩
      have hI := (integrableOn_offAxis_of_kernel H hH (turnKernel m n a) (turnKernel_continuous m n a)
        (turnKernel_norm_le m n a) _ (fun p => modeThird_turn_eq m n H a p) K.r₁ (max K.r₂ K.z₂) hδ).mono_set hsub2
      refine hI.congr_fun (fun p _ => ?_) (rect_measurable K)
      simp only [CellBox.lineWeight, h, if_false, Complex.ofReal_one, one_mul]
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
  refine ⟨hFr, hgr, fun ψ hψ hψ1 hψ2 t ht => ?_⟩
  exact ModeRadialWeakInternal.rect_psi hF hg hW h0 h12 (lineWeight_cont K) hwpos hwn hwl
    hFr hgr hgm hψ hψ1 hψ2 ht

end TurnSecond

theorem localRadialTurn : LocalRadialTurnStatement := by
  intro k N c K S B L hL x hx n e a t he2 he0 ht
  have hb := hL.box_eq
  subst hb
  have hs : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1 := hx.1
  have hK := hL.box_valid
  have htc : Continuous t := by
    obtain ⟨q, hq⟩ := ht
    rw [show t = fun u => q.eval u from funext hq]
    exact q.continuous
  obtain ⟨cc, oo, hco, hrad, hmom⟩ : ∃ cc oo : ℝ,
      ((cc = L.box.r₁ ∧ oo = L.box.r₂ ∧ L.box.r₁ ≠ 0) ∨ (cc = L.box.r₂ ∧ oo = L.box.r₁)) ∧
      L.sideRadius e = cc ∧ ∀ F dF : ℝ × ℝ → ℂ,
        radialFaceMoment L.box F dF (CellLayout.sideRadialIndex e) t =
          radialStripMoment cc oo L.box.z₁ L.box.z₂ F dF t := by
    rcases (show e.val = 0 ∨ e.val = 1 by omega) with h | h
    · refine ⟨L.box.r₁, L.box.r₂, Or.inl ⟨rfl, rfl, he0 h⟩, ?_, fun F dF => ?_⟩
      · simp [CellLayout.sideRadius, h]
      · simp [radialFaceMoment, CellLayout.sideRadialIndex, h]
    · refine ⟨L.box.r₂, L.box.r₁, Or.inr ⟨rfl, rfl⟩, ?_, fun F dF => ?_⟩
      · simp [CellLayout.sideRadius, h]
      · simp [radialFaceMoment, CellLayout.sideRadialIndex, h]
  have hsv : ∀ a' : Fin 3, L.sideVelocityValue n x e a' t =
      radialStripMoment cc oo L.box.z₁ L.box.z₂ (L.velMode n x a') (L.gradModeOf n x a' 0) t := by
    intro a'
    rw [CellLayout.sideVelocityValue, if_pos he2, hmom]
  have hAn := localAngularMode L.order x.1 x.2.1 x.2.2.1 hs n
  have hSn := localTurnSecond L.order x.1 x.2.1 x.2.2.1 hs n
  have hWv := fun a' => localModeRadialWeak L.box hK L.order x.1 x.2.1 x.2.2.1 hs n a'
  have hTg := localTurnRadialWeak L.box hK L.order x.1 x.2.1 x.2.2.1 hs n a
  rw [hmom, hrad]
  have key := fun (V0 V1 G0 G1 : ℝ × ℝ → ℂ) (α β : ℂ) hF hdF hV0 hV1 hG0 hG1 =>
    radialStripMoment_turn L.box hK cc oo hco (L.gradModeOf n x a 1) (L.secondModeOf n x a 1 0) V0 V1 G0 G1 α β
      t htc hF hdF hV0 hV1 hG0 hG1 hTg.1 hTg.2.1 (fun ψ h1 h2 h3 => hTg.2.2 ψ h1 h2 h3 t htc)
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl
  · rw [key (L.velMode n x 0) (L.velMode n x 1) (L.gradModeOf n x 0 0) (L.gradModeOf n x 1 0)
      ((azimuth L.order n : ℂ) * Complex.I) (-1) ?_ ?_ (hWv 0).1 (hWv 1).1 (hWv 0).2.1 (hWv 1).2.1]
    · rw [CellLayout.turnValue, if_pos rfl, hsv, hsv]
      ring
    · filter_upwards [hAn] with p hp hpos
      simp only [CellLayout.gradModeOf, CellLayout.velMode]
      rw [(hp hpos).1]
      ring
    · filter_upwards [hSn] with p hp hpos
      simp only [CellLayout.gradModeOf, CellLayout.secondModeOf]
      rw [(hp hpos).1]
      ring
  · rw [key (L.velMode n x 1) (L.velMode n x 0) (L.gradModeOf n x 1 0) (L.gradModeOf n x 0 0)
      ((azimuth L.order n : ℂ) * Complex.I) 1 ?_ ?_ (hWv 1).1 (hWv 0).1 (hWv 1).2.1 (hWv 0).2.1]
    · rw [CellLayout.turnValue, if_neg (by decide), if_pos rfl, hsv, hsv]
      ring
    · filter_upwards [hAn] with p hp hpos
      simp only [CellLayout.gradModeOf, CellLayout.velMode]
      rw [(hp hpos).2.1]
      ring
    · filter_upwards [hSn] with p hp hpos
      simp only [CellLayout.gradModeOf, CellLayout.secondModeOf]
      rw [(hp hpos).2.1]
      ring
  · rw [key (L.velMode n x 2) (L.velMode n x 0) (L.gradModeOf n x 2 0) (L.gradModeOf n x 0 0)
      ((azimuth L.order n : ℂ) * Complex.I) 0 ?_ ?_ (hWv 2).1 (hWv 0).1 (hWv 2).2.1 (hWv 0).2.1]
    · rw [CellLayout.turnValue, if_neg (by decide), if_neg (by decide), hsv]
      ring
    · filter_upwards [hAn] with p hp hpos
      simp only [CellLayout.gradModeOf, CellLayout.velMode]
      rw [(hp hpos).2.2]
      ring
    · filter_upwards [hSn] with p hp hpos
      simp only [CellLayout.gradModeOf, CellLayout.secondModeOf]
      rw [(hp hpos).2.2]
      ring

end LocalField

end CertCell

end Breakdown
