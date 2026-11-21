import Breakdown.CertCell.LocalFieldDefs
import Breakdown.FracCell.ModeRadialPartsA
import Breakdown.FracCell.ModeHeightParts
import Breakdown.FracCell.ModeSquareIntegrable
import Breakdown.FracCell.ResolvedEnergy

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula

theorem localModeGradSquare : LocalModeGradSquareStatement := by
  intro K hK m v G H hs n a b
  exact ⟨ModeGradSquare.Internal.gm_meas K hK m n hs.measurable_gradient a b,
    ModeGradSquare.Internal.gm_sq K hK m n hs.measurable_gradient hs.gradient_two a b⟩

open ModeSquareIntegrable.Internal ModeGradSquare.Internal LowEntry.Internal in
theorem localModeSquareIntegrable : LocalModeSquareIntegrableStatement := by
  intro K hK m v G H hs n κ
  have hg := combo_sq K (fun p => K.lineWeight p.1)
    (((lineWeight_cont K).comp continuous_fst).aestronglyMeasurable)
    (fun p hp => by
      have h1 : K.r₁ ≤ p.1 := hp.1.1
      unfold CellBox.lineWeight
      split_ifs
      · linarith [hK.r_order.1]
      · exact zero_le_one)
    (gradMode m n G) (fun a b => gm_meas K hK m n hs.measurable_gradient a b)
    (fun a b => gm_sq K hK m n hs.measurable_gradient hs.gradient_two a b) κ
  refine ⟨hg.1, hg.2, fun c => ?_⟩
  exact combo_sq K (fun p => p.1) continuous_fst.aestronglyMeasurable
    (fun p hp => le_trans hK.r_order.1 hp.1.1)
    (fun a b => modeThird m n H a b c) (fun a b => th_meas K hK m n hs.measurable_second a b c)
    (fun a b => th_sq K hK m n hs.measurable_second hs.second_two a b c) κ

namespace Internal

open ModeRadialPartsA.Internal

theorem locGrad {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) :
    LocallyIntegrable G volume :=
  loc_of_cols hs.measurable_gradient fun j =>
    (memLp_col hs.measurable_gradient hs.gradient_two j).locallyIntegrable (by norm_num)

theorem locSecondCol {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (j : Fin 3) :
    LocallyIntegrable (fun y => H y (unitVector j)) volume :=
  loc_of_cols (hs.measurable_second.apply_continuousLinearMap (unitVector j)) fun i =>
    (memLp_col2 hs.measurable_second hs.second_two j i).locallyIntegrable (by norm_num)

theorem locSecond {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) :
    LocallyIntegrable H volume :=
  loc_of_cols hs.measurable_second (locSecondCol hs)

theorem weakGradOp {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) :
    ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
  intro φ hφ j
  have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
    (locGrad hs).integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
    (locSecondCol hs j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
      (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
    intro i
    rw [neg_apply, ContinuousLinearMap.integral_apply i1,
      ContinuousLinearMap.integral_apply i2]
    simpa using hs.weak_second φ hφ i j
  refine ContinuousLinearMap.ext fun u => ?_
  rw [vec_expand u]
  simp only [map_sum, map_smul, key]

theorem weakRadialPair {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hpos : ∀ p ∈ tsupport φ, 0 < p.1) :
    ∫ p, ((fderiv ℝ φ p (1, 0) : ℝ) : ℂ) * gradMode m n G a b p = -∫ p, (φ p : ℂ) * modeThird m n H a b 0 p := by
  have hgm : ∀ p : ℝ × ℝ, gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryQ a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [gradMode, modeMat, entryQ_apply]
    rfl
  have hth : ∀ p : ℝ × ℝ, modeThird m n H a b 0 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryQ a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ) := by
    intro p
    simp only [modeThird, entryQ_apply]
    rfl
  simp only [hth, hgm]
  exact scale _ (cylModeWeak (Space →L[ℝ] Space) G H (locGrad hs) (locSecondCol hs) (weakGradOp hs) (entryQ a b)
    (entryQ_smooth a b) m n φ hφ hc hpos).1

open LowEntry.Internal in
theorem thirdInt (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p) K.rect := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      gradKernel m n a b q.1 (q.2 (radialUnit q.1))) :=
    (gradKernel_cont m n a b).comp
      (continuous_fst.prodMk (continuous_snd.clm_apply (radialUnit_cont.comp continuous_fst)))
  have hb : ∀ θ (M : Space →L[ℝ] Space →L[ℝ] Space), ‖gradKernel m n a b θ (M (radialUnit θ))‖ ≤ ‖M‖ := by
    intro θ M
    refine (gradKernel_bound m n a b θ _).trans ((M.le_opNorm _).trans ?_)
    simpa using mul_le_mul_of_nonneg_left (unit_norm θ 0) (norm_nonneg M)
  have h := mode_int K hK (locSecond hs) (fun θ M => gradKernel m n a b θ (M (radialUnit θ))) hc hb
  have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p) = fun p =>
      (1 / (2 * Real.pi) : ℂ) * ((K.lineWeight p.1 : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        gradKernel m n a b θ (H (cylPoint p.1 θ p.2) (radialUnit θ))) := by
    funext p; rw [third_eq]; ring
  rw [e]
  exact h.const_mul _

theorem gradInt (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p) K.rect :=
  LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two a b

open LowEntry.Internal in
theorem thirdMeas (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3) :
    AEStronglyMeasurable (modeThird m n H a b 0) (volume.restrict K.rect) := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      gradKernel m n a b q.1 (q.2 (radialUnit q.1))) :=
    (gradKernel_cont m n a b).comp
      (continuous_fst.prodMk (continuous_snd.clm_apply (radialUnit_cont.comp continuous_fst)))
  have hF := ModeGradSquare.Internal.meas_gen hs.measurable_second
    (fun θ M => gradKernel m n a b θ (M (radialUnit θ))) hc
  have e : modeThird m n H a b 0 = fun p => (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, gradKernel m n a b θ (H (cylPoint p.1 θ p.2) (radialUnit θ)) :=
    funext fun p => third_eq m n H a b p
  rw [e]
  exact (hF.mono_measure (ModeGradSquare.Internal.hle K hK)).const_mul _

theorem realRadialParts (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3) (χ : ℝ × ℝ → ℝ) (hχ : ContDiff ℝ 1 χ)
    (e1 : ∀ z, χ (K.r₁, z) = 0) (e2 : ∀ z, χ (K.r₂, z) = 0) :
    IntegrableOn (fun p => gradMode m n G a b p *
      ((deriv (fun r => K.lineWeight r * χ (r, p.2)) p.1 : ℝ) : ℂ)) K.rect ∧
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * (χ p : ℂ)
      = -∫ p in K.rect, gradMode m n G a b p * ((deriv (fun r => K.lineWeight r * χ (r, p.2)) p.1 : ℝ) : ℂ) :=
  extend_c1 K hK (gradMode m n G a b) (modeThird m n H a b 0) (localModeGradSquare K hK m v G H hs n a b).1
    (thirdMeas K hK hs n a b) (gradInt K hK hs n a b) (thirdInt K hK hs n a b)
    (fun φ hφ hcφ hsφ => c1_of_smooth K hK (gradMode m n G a b) (modeThird m n H a b 0)
      (fun K' hK' => gradInt K' hK' hs n a b) (fun K' hK' => thirdInt K' hK' hs n a b) (weakRadialPair hs n a b)
      φ hφ hcφ hsφ) χ hχ e1 e2

theorem entryRadialParts (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3) (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (h1 : ∀ z, ψ (K.r₁, z) = 0) (h2 : ∀ z, ψ (K.r₂, z) = 0) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * ψ p) K.rect ∧
    IntegrableOn (fun p => gradMode m n G a b p *
      CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) K.rect ∧
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * ψ p
      = -∫ p in K.rect, gradMode m n G a b p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p := by
  have hT := thirdInt K hK (m := m) hs n a b
  have hcpt : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hre : ContDiff ℝ 1 (fun p => (ψ p).re) := Complex.reCLM.contDiff.comp hψ
  have him : ContDiff ℝ 1 (fun p => (ψ p).im) := Complex.imCLM.contDiff.comp hψ
  obtain ⟨iR, eR⟩ := realRadialParts K hK hs n a b (fun p => (ψ p).re) hre (fun z => by simp [h1])
    (fun z => by simp [h2])
  obtain ⟨iI, eI⟩ := realRadialParts K hK hs n a b (fun p => (ψ p).im) him (fun z => by simp [h1])
    (fun z => by simp [h2])
  have cR : ContinuousOn (fun p => (((ψ p).re : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp hre.continuous).continuousOn
  have cI : ContinuousOn (fun p => (((ψ p).im : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp him.continuous).continuousOn
  have jR := hT.mul_continuousOn cR hcpt
  have jI := hT.mul_continuousOn cI hcpt
  have eL : (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * ψ p) = fun p =>
      (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * (((ψ p).re : ℝ) : ℂ) +
        Complex.I * ((K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * (((ψ p).im : ℝ) : ℂ)) := by
    funext p
    conv_lhs => rw [← Complex.re_add_im (ψ p)]
    ring
  have eD : (fun p => gradMode m n G a b p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) =
      fun p => gradMode m n G a b p * ((deriv (fun r => K.lineWeight r * (ψ (r, p.2)).re) p.1 : ℝ) : ℂ) +
        Complex.I * (gradMode m n G a b p *
          ((deriv (fun r => K.lineWeight r * (ψ (r, p.2)).im) p.1 : ℝ) : ℂ)) := by
    funext p
    rw [split_deriv K ψ hψ p]
    ring
  refine ⟨hT.mul_continuousOn hψ.continuous.continuousOn hcpt, ?_, ?_⟩
  · rw [eD]
    exact iR.add (iI.const_mul _)
  · rw [eL, eD, integral_add jR (jI.const_mul _), integral_add iR (iI.const_mul _), integral_const_mul,
      integral_const_mul, eR, eI]
    ring

open Breakdown.FracInternal.ModeHeightParts in
theorem weakHeightPair {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a b p =
      -∫ p, (ψ p : ℂ) * gradMode m n (fun y => H y axialUnit) a b p := by
  have hG : LocallyIntegrable G volume :=
    (memLp_of_entry hs.measurable_gradient hs.gradient_two).locallyIntegrable (by norm_num)
  have hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume := fun j =>
    (memLp_of_entry (hs.measurable_second.apply_continuousLinearMap _)
      (col_entry hs.measurable_second hs.second_two j)).locallyIntegrable (by norm_num)
  have e := (cylModeWeak (Space →L[ℝ] Space) G H hG hHc (weak_clm hG hHc hs.weak_second) (entQ a b)
    (entQ_smooth a b) m n ψ hψ hc hpos).2
  have hgm : ∀ (A : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ), gradMode m n A a b p =
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (entQ a b (Real.cos θ, Real.sin θ) (A (cylPoint p.1 θ p.2)) : ℂ) := by
    intro A p
    simp only [gradMode, modeMat, entQ_apply]
  simp only [hgm]
  exact Breakdown.FracInternal.ModeHeightParts.scale _ e

end Internal

open Internal in
theorem localModeRadialParts : LocalModeRadialPartsStatement := by
  intro K hK m v G H hs n κ ψ hψ h1 h2
  have P := fun a b => entryRadialParts K hK (m := m) hs n a b ψ hψ h1 h2
  have eL : (fun p => (K.lineWeight p.1 : ℂ) * comboThird κ m n H 0 p * ψ p) = fun p =>
      ∑ a : Fin 3, ∑ b : Fin 3, κ a b * ((K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * ψ p) := by
    funext p
    simp only [comboThird, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have eR : (fun p => comboGrad κ m n G p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) =
      fun p => ∑ a : Fin 3, ∑ b : Fin 3, κ a b *
        (gradMode m n G a b p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) := by
    funext p
    simp only [comboGrad, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [eL, eR, integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (P a b).1.const_mul (κ a b)),
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (P a b).2.1.const_mul (κ a b)),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => (P a b).1.const_mul (κ a b)),
    integral_finsetSum _ (fun b _ => (P a b).2.1.const_mul (κ a b)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, integral_const_mul, (P a b).2.2, mul_neg]

open Internal Breakdown.FracInternal.ModeHeightParts in
theorem localModeHeightParts : LocalModeHeightPartsStatement := by
  intro K hK m v G H hs n κ ψ hψ h1 h2
  have hH1 : AEStronglyMeasurable (fun y => H y axialUnit) volume :=
    hs.measurable_second.apply_continuousLinearMap _
  have hH2 : Integrable (fun y => entrySq (H y axialUnit)) := col_entry hs.measurable_second hs.second_two 2
  have hGI := LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two
  have hHI := LowEntry.Internal.gradMode_int K hK m n hH1 hH2
  have hper : ∀ a b, ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeThird m n H a b 2 p * ψ p =
      -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a b p * CellBox.heightDeriv ψ p := fun a b =>
    parts_of_weak K hK (fun Ψ e1 e2 e3 => weakHeightPair hs n a b Ψ e1 e2 e3) (hGI a b) (hHI a b) ψ hψ h1 h2
  have F1 : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 2 p * ψ p) K.rect :=
    fun a b => bdd_int K (hHI a b) ψ hψ.continuous
  have F2 : ∀ a b, IntegrableOn
      (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p * CellBox.heightDeriv ψ p) K.rect :=
    fun a b => bdd_int K (hGI a b) (CellBox.heightDeriv ψ) (hd_cont hψ)
  have s1 := sum_int K F1 κ
  have s2 := sum_int K F2 κ
  have e1 : (fun p => (K.lineWeight p.1 : ℂ) * comboThird κ m n H 2 p * ψ p) =
      fun p => ∑ a, ∑ b, κ a b * ((K.lineWeight p.1 : ℂ) * modeThird m n H a b 2 p * ψ p) := by
    funext p
    simp only [comboThird, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have e2 : (fun p => (K.lineWeight p.1 : ℂ) * comboGrad κ m n G p * CellBox.heightDeriv ψ p) =
      fun p => ∑ a, ∑ b, κ a b * ((K.lineWeight p.1 : ℂ) * gradMode m n G a b p * CellBox.heightDeriv ψ p) := by
    funext p
    simp only [comboGrad, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e1, e2, s1, s2]
  simp only [hper, mul_neg, Finset.sum_neg_distrib]


namespace Internal

theorem comboBound (K : CellBox) (hK : IsCellBox K) (m : ℕ) (Q q : ℕ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hs : IsLocalSecondOrderField v G H) (n : ℤ) (hn : K.IsAxis → n = 0) (κ : Fin 3 → Fin 3 → ℂ) :
    K.radialEnergy Q q (comboGrad κ m n G) (comboThird κ m n H 0)
        + K.heightEnergy Q q (comboGrad κ m n G) (comboThird κ m n H 2)
        + K.angularEnergy Q (fun p => (p.1 : ℂ) * comboThird κ m n H 1 p)
        + (K.tailGradWeight Q (comboGrad κ m n G) (comboThird κ m n H 0) (comboThird κ m n H 2)
          + K.angularWeight n * K.tailNormSq Q (fun p => (p.1 : ℂ) * comboThird κ m n H 1 p))
      ≤ ∫ p in K.rect, p.1 * (‖comboThird κ m n H 0 p‖ ^ 2 + ‖comboThird κ m n H 1 p‖ ^ 2
          + ‖comboThird κ m n H 2 p‖ ^ 2) := by
  obtain ⟨hFm, hFi, hT⟩ := localModeSquareIntegrable K hK m v G H hs n κ
  exact resolvedComponent_of radialCross heightCross K hK Q q n hn _ _ _ _ hFm (hT 0).1 (hT 2).1 (hT 1).1 hFi
    (hT 0).2 (hT 2).2 (hT 1).2
    (fun ψ hψ h1 h2 => localModeRadialParts K hK m v G H hs n κ ψ hψ h1 h2)
    (fun ψ hψ h1 h2 => localModeHeightParts K hK m v G H hs n κ ψ hψ h1 h2)

theorem comboIntegrable (K : CellBox) (hK : IsCellBox K) (m : ℕ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hs : IsLocalSecondOrderField v G H) (n : ℤ) (κ : Fin 3 → Fin 3 → ℂ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖comboThird κ m n H 0 p‖ ^ 2 + ‖comboThird κ m n H 1 p‖ ^ 2
          + ‖comboThird κ m n H 2 p‖ ^ 2)) K.rect := by
  obtain ⟨-, -, hT⟩ := localModeSquareIntegrable K hK m v G H hs n κ
  have h := (((hT 0).2.add (hT 1).2).add (hT 2).2)
  refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  simp only [Pi.add_apply]
  ring

end Internal

open Internal ResolvedEnergyInternal in
theorem localResolvedEnergy : LocalResolvedEnergyStatement := by
  intro K hK m Q q _ _ v G H hs n hn
  constructor
  · have hb := fun a b => comboBound K hK m Q q v G H hs n hn (unitCoef a b)
    have hg : ∀ a b, comboGrad (unitCoef a b) m n G = gradMode m n G a b := fun a b => by
      funext p; exact unit_sum a b (fun a' b' => gradMode m n G a' b' p)
    have ht : ∀ a b c, comboThird (unitCoef a b) m n H c = fun p => modeThird m n H a b c p := fun a b c => by
      funext p; exact unit_sum a b (fun a' b' => modeThird m n H a' b' c p)
    simp only [hg, ht] at hb
    have hint : ∀ a b, IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖modeThird m n H a b 0 p‖ ^ 2
        + ‖modeThird m n H a b 1 p‖ ^ 2 + ‖modeThird m n H a b 2 p‖ ^ 2)) K.rect := fun a b => by
      have := comboIntegrable K hK m v G H hs n (unitCoef a b)
      simpa only [ht] using this
    calc _ = ∑ a : Fin 3, ∑ b : Fin 3,
          (K.radialEnergy Q q (gradMode m n G a b) (fun p => modeThird m n H a b 0 p)
            + K.heightEnergy Q q (gradMode m n G a b) (fun p => modeThird m n H a b 2 p)
            + K.angularEnergy Q (fun p => (p.1 : ℂ) * modeThird m n H a b 1 p)
            + (K.tailGradWeight Q (gradMode m n G a b) (fun p => modeThird m n H a b 0 p)
                (fun p => modeThird m n H a b 2 p)
              + K.angularWeight n * K.tailNormSq Q (fun p => (p.1 : ℂ) * modeThird m n H a b 1 p))) := by
          simp only [CellBox.strainEnergy, ← Finset.sum_add_distrib]
          rfl
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∫ p in K.rect, p.1 * (‖modeThird m n H a b 0 p‖ ^ 2
            + ‖modeThird m n H a b 1 p‖ ^ 2 + ‖modeThird m n H a b 2 p‖ ^ 2) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hb a b))
      _ = ∑ a : Fin 3, ∫ p in K.rect, ∑ b : Fin 3, p.1 * (‖modeThird m n H a b 0 p‖ ^ 2
            + ‖modeThird m n H a b 1 p‖ ^ 2 + ‖modeThird m n H a b 2 p‖ ^ 2) :=
          Finset.sum_congr rfl (fun a _ => (integral_finsetSum _ (fun b _ => hint a b)).symm)
      _ = ∫ p in K.rect, ∑ a : Fin 3, ∑ b : Fin 3, p.1 * (‖modeThird m n H a b 0 p‖ ^ 2
            + ‖modeThird m n H a b 1 p‖ ^ 2 + ‖modeThird m n H a b 2 p‖ ^ 2) :=
          (integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))).symm
      _ = ∫ p in K.rect, p.1 * secondModeSq m n H p := by
          congr 1
          funext p
          simp only [secondModeSq, Fin.sum_univ_three]
          ring
  · have hb := fun i => comboBound K hK m Q q v G H hs n hn (curlCoef i)
    have hg : ∀ i, comboGrad (curlCoef i) m n G = fun p => curlComp (fun a b => gradMode m n G a b p) i :=
      fun i => by funext p; exact curl_sum i (fun a b => gradMode m n G a b p)
    have ht : ∀ i c, comboThird (curlCoef i) m n H c =
        fun p => curlComp (fun a b => modeThird m n H a b c p) i :=
      fun i c => by funext p; exact curl_sum i (fun a b => modeThird m n H a b c p)
    simp only [hg, ht] at hb
    have hint : ∀ i, IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖curlComp (fun a b => modeThird m n H a b 0 p) i‖ ^ 2
        + ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2
        + ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖ ^ 2)) K.rect := fun i => by
      have := comboIntegrable K hK m v G H hs n (curlCoef i)
      simpa only [ht] using this
    have hang : ∀ i, (fun p : ℝ × ℝ => curlComp (fun a b => angularGradMode m n H a b p) i)
        = fun p => (p.1 : ℂ) * curlComp (fun a b => modeThird m n H a b 1 p) i := fun i => by
      funext p; exact curl_mul i (p.1 : ℂ) (fun a b => modeThird m n H a b 1 p)
    calc _ = ∑ i : Fin 3,
          (K.radialEnergy Q q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
              (fun p => curlComp (fun a b => modeThird m n H a b 0 p) i)
            + K.heightEnergy Q q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
              (fun p => curlComp (fun a b => modeThird m n H a b 2 p) i)
            + K.angularEnergy Q (fun p => (p.1 : ℂ) * curlComp (fun a b => modeThird m n H a b 1 p) i)
            + (K.tailGradWeight Q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
                (fun p => curlComp (fun a b => modeThird m n H a b 0 p) i)
                (fun p => curlComp (fun a b => modeThird m n H a b 2 p) i)
              + K.angularWeight n * K.tailNormSq Q
                (fun p => (p.1 : ℂ) * curlComp (fun a b => modeThird m n H a b 1 p) i))) := by
          simp only [CellBox.vorticityEnergy, ← Finset.sum_add_distrib, ← hang]
          rfl
      _ ≤ ∑ i : Fin 3, ∫ p in K.rect, p.1 * (‖curlComp (fun a b => modeThird m n H a b 0 p) i‖ ^ 2
            + ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2
            + ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖ ^ 2) :=
          Finset.sum_le_sum (fun i _ => hb i)
      _ = ∫ p in K.rect, ∑ i : Fin 3, p.1 * (‖curlComp (fun a b => modeThird m n H a b 0 p) i‖ ^ 2
            + ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2
            + ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖ ^ 2) :=
          (integral_finsetSum _ (fun i _ => hint i)).symm
      _ = ∫ p in K.rect, p.1 * curlGradModeSq m n H p := by
          congr 1
          funext p
          simp only [curlGradModeSq, Fin.sum_univ_three]
          ring

end Breakdown.CertCell.LocalField
