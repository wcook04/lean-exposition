import Breakdown.CertCell.RowProfileDefs
import Breakdown.CertCell.LocalResolvedEnergy

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace LabelModeFacts.Internal

theorem exists_harmonic (ι : ℤ × ℤ) : ∃ ν n : ℤ, Even (n + ν) ∧ ι = harmonicMode ν n := by
  obtain ⟨i, j⟩ := ι
  refine ⟨2 * j - i, i, ⟨j, by ring⟩, ?_⟩
  simp only [harmonicMode, Prod.mk.injEq, true_and]
  omega

theorem ae_rect_pos (K : CellBox) (hK : IsCellBox K) : ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 := by
  have h0 : volume {p : ℝ × ℝ | p.1 = 0} = 0 := by
    have e : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hne : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
    rw [ae_iff]
    simpa using h0
  filter_upwards [ae_restrict_mem (LowEntry.Internal.rect_meas K), ae_restrict_of_ae hne] with p hp hp0
  exact lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm hp0)

theorem sq_bound (x y : ℂ) : ‖x + Complex.I * y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x (Complex.I * y)
  rw [norm_mul, Complex.norm_I, one_mul] at h
  nlinarith [norm_nonneg (x + Complex.I * y), norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]

theorem weighted_sq_int (K : CellBox) {w : ℝ × ℝ → ℝ} (hwc : Continuous w) (hw : ∀ p ∈ K.rect, 0 ≤ w p)
    {f g h : ℝ × ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict K.rect))
    (hfe : ∀ᵐ p ∂(volume.restrict K.rect), f p = g p + Complex.I * h p)
    (hg : IntegrableOn (fun p => w p * ‖g p‖ ^ 2) K.rect) (hh : IntegrableOn (fun p => w p * ‖h p‖ ^ 2) K.rect) :
    IntegrableOn (fun p => w p * ‖f p‖ ^ 2) K.rect := by
  refine Integrable.mono' ((hg.const_mul 2).add (hh.const_mul 2))
    (hwc.aestronglyMeasurable.mul (hf.norm.pow 2)) ?_
  filter_upwards [hfe, ae_restrict_mem (LowEntry.Internal.rect_meas K)] with p hp hpr
  have hw0 := hw p hpr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (by positivity)), hp]
  have := mul_le_mul_of_nonneg_left (sq_bound (g p) (h p)) hw0
  simp only [Pi.add_apply]
  linarith

theorem combine {μ : Measure (ℝ × ℝ)} {f g fc fs gc gs : ℝ × ℝ → ℂ}
    (hf : ∀ᵐ p ∂μ, f p = fc p + Complex.I * fs p) (hg : ∀ᵐ p ∂μ, g p = gc p + Complex.I * gs p)
    (hfc : Integrable fc μ) (hfs : Integrable fs μ) (hgc : Integrable gc μ) (hgs : Integrable gs μ)
    (hc : ∫ p, fc p ∂μ = -∫ p, gc p ∂μ) (hs : ∫ p, fs p ∂μ = -∫ p, gs p ∂μ) :
    ∫ p, f p ∂μ = -∫ p, g p ∂μ := by
  rw [integral_congr_ae hf, integral_congr_ae hg, integral_add hfc (hfs.const_mul _),
    integral_add hgc (hgs.const_mul _), integral_const_mul, integral_const_mul, hc, hs]
  ring

theorem combo_int (K : CellBox) {F : Fin 3 → Fin 3 → ℝ × ℝ → ℂ} (hF : ∀ a b, IntegrableOn (F a b) K.rect)
    (κ : Fin 3 → Fin 3 → ℂ) : IntegrableOn (fun p => ∑ a : Fin 3, ∑ b : Fin 3, κ a b * F a b p) K.rect :=
  integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hF a b).const_mul _

theorem radial_int (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsLocalSecondOrderField v G H) (n : ℤ) (κ : Fin 3 → Fin 3 → ℂ) (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (h1 : ∀ z, ψ (K.r₁, z) = 0) (h2 : ∀ z, ψ (K.r₂, z) = 0) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * comboThird κ m n H 0 p * ψ p) K.rect ∧
    IntegrableOn (fun p => comboGrad κ m n G p *
      CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) K.rect := by
  have P := fun a b => LocalField.Internal.entryRadialParts K hK (m := m) hs n a b ψ hψ h1 h2
  constructor
  · have e : (fun p => (K.lineWeight p.1 : ℂ) * comboThird κ m n H 0 p * ψ p) = fun p =>
        ∑ a : Fin 3, ∑ b : Fin 3, κ a b * ((K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * ψ p) := by
      funext p
      simp only [comboThird, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [e]
    exact combo_int K (fun a b => (P a b).1) κ
  · have e : (fun p => comboGrad κ m n G p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) =
        fun p => ∑ a : Fin 3, ∑ b : Fin 3, κ a b *
          (gradMode m n G a b p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) := by
      funext p
      simp only [comboGrad, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [e]
    exact combo_int K (fun a b => (P a b).2.1) κ

open Breakdown.FracInternal.ModeHeightParts in
theorem height_int (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsLocalSecondOrderField v G H) (n : ℤ) (κ : Fin 3 → Fin 3 → ℂ) (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ 1 ψ) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * comboThird κ m n H 2 p * ψ p) K.rect ∧
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * comboGrad κ m n G p * CellBox.heightDeriv ψ p) K.rect := by
  have hH1 : AEStronglyMeasurable (fun y => H y axialUnit) volume :=
    hs.measurable_second.apply_continuousLinearMap _
  have hH2 : Integrable (fun y => entrySq (H y axialUnit)) := col_entry hs.measurable_second hs.second_two 2
  have hGI := LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two
  have hHI := LowEntry.Internal.gradMode_int K hK m n hH1 hH2
  have F1 : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 2 p * ψ p) K.rect :=
    fun a b => bdd_int K (hHI a b) ψ hψ.continuous
  have F2 : ∀ a b, IntegrableOn
      (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p * CellBox.heightDeriv ψ p) K.rect :=
    fun a b => bdd_int K (hGI a b) (CellBox.heightDeriv ψ) (hd_cont hψ)
  constructor
  · have e : (fun p => (K.lineWeight p.1 : ℂ) * comboThird κ m n H 2 p * ψ p) =
        fun p => ∑ a, ∑ b, κ a b * ((K.lineWeight p.1 : ℂ) * modeThird m n H a b 2 p * ψ p) := by
      funext p
      simp only [comboThird, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [e]
    exact combo_int K F1 κ
  · have e : (fun p => (K.lineWeight p.1 : ℂ) * comboGrad κ m n G p * CellBox.heightDeriv ψ p) =
        fun p => ∑ a, ∑ b, κ a b * ((K.lineWeight p.1 : ℂ) * gradMode m n G a b p * CellBox.heightDeriv ψ p) := by
      funext p
      simp only [comboGrad, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [e]
    exact combo_int K F2 κ

theorem lineWeight_nonneg (K : CellBox) : ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 := by
  intro p hp
  have h : K.r₁ ≤ p.1 := hp.1.1
  unfold CellBox.lineWeight
  split_ifs with h0
  · linarith
  · exact zero_le_one

theorem fst_nonneg (K : CellBox) (hK : IsCellBox K) : ∀ p ∈ K.rect, 0 ≤ p.1 := fun _ hp =>
  hK.r_order.1.trans hp.1.1

end LabelModeFacts.Internal

open LabelModeFacts.Internal in
theorem labelModeFacts_holds (h1 : HarmonicLiftStatement) : LabelModeFactsStatement := by
  intro K hK m v G H hP ι C
  obtain ⟨ν, n, hev, rfl⟩ := exists_harmonic ι
  obtain ⟨hc, hs, hprof⟩ := h1 m v G H hP ν
  have hpt : ∀ᵐ p ∂(volume.restrict K.rect),
      (∑ a : Fin 3, ∑ b : Fin 3, C a b * gradAt m (harmonicMode ν n) G a b p)
          = comboGrad C m n (harmonicCos ν G) p + Complex.I * comboGrad C m n (harmonicSin ν G) p ∧
        ∀ c, (∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m (harmonicMode ν n) H a b c p)
          = comboThird C m n (harmonicCos ν H) c p + Complex.I * comboThird C m n (harmonicSin ν H) c p := by
    filter_upwards [ae_rect_pos K hK, ae_restrict_of_ae (hprof n hev)] with p hp hq
    obtain ⟨-, hg, hh⟩ := hq hp
    refine ⟨?_, fun c => ?_⟩
    · rw [comboGrad, comboGrad, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hg]
      ring
    · rw [comboThird, comboThird, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hh]
      ring
  have qc := localModeSquareIntegrable K hK m _ _ _ hc n C
  have qs := localModeSquareIntegrable K hK m _ _ _ hs n C
  have hFm : AEStronglyMeasurable (fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * gradAt m (harmonicMode ν n) G a b p)
      (volume.restrict K.rect) :=
    (qc.1.add (aestronglyMeasurable_const.mul qs.1)).congr (hpt.mono fun p hp => hp.1.symm)
  have hTm : ∀ c, AEStronglyMeasurable
      (fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m (harmonicMode ν n) H a b c p)
      (volume.restrict K.rect) := fun c =>
    (((qc.2.2 c).1).add (aestronglyMeasurable_const.mul (qs.2.2 c).1)).congr (hpt.mono fun p hp => (hp.2 c).symm)
  dsimp only
  refine ⟨hFm, ?_, fun c => ⟨hTm c, ?_⟩, ?_, ?_⟩
  · exact weighted_sq_int K ((LowEntry.Internal.lineWeight_cont K).comp continuous_fst) (lineWeight_nonneg K)
      hFm (hpt.mono fun p hp => hp.1) qc.2.1 qs.2.1
  · exact weighted_sq_int K continuous_fst (fst_nonneg K hK) (hTm c) (hpt.mono fun p hp => hp.2 c)
      (qc.2.2 c).2 (qs.2.2 c).2
  · intro ψ hψ e1 e2
    have rc := radial_int K hK (m := m) hc n C ψ hψ e1 e2
    have rs := radial_int K hK (m := m) hs n C ψ hψ e1 e2
    refine combine ?_ ?_ rc.1 rs.1 rc.2 rs.2 (localModeRadialParts K hK m _ _ _ hc n C ψ hψ e1 e2)
      (localModeRadialParts K hK m _ _ _ hs n C ψ hψ e1 e2)
    · filter_upwards [hpt] with p hp
      rw [hp.2 0]
      ring
    · filter_upwards [hpt] with p hp
      rw [hp.1]
      ring
  · intro ψ hψ e1 e2
    have rc := height_int K hK (m := m) hc n C ψ hψ
    have rs := height_int K hK (m := m) hs n C ψ hψ
    refine combine ?_ ?_ rc.1 rs.1 rc.2 rs.2 (localModeHeightParts K hK m _ _ _ hc n C ψ hψ e1 e2)
      (localModeHeightParts K hK m _ _ _ hs n C ψ hψ e1 e2)
    · filter_upwards [hpt] with p hp
      rw [hp.2 2]
      ring
    · filter_upwards [hpt] with p hp
      rw [hp.1]
      ring

end Breakdown.CertCell.CellCalculus
