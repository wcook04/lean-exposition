import Breakdown.CertCell.LocalModeIntegrableParts
import Breakdown.FracCell.ModeStripIntegrable
import Breakdown.FracCell.AngularMode
import Breakdown.FracCell.AxisModeIntegrable
import Breakdown.FracCell.CircleWeak

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown.CertCell.LocalField

open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.Assembly Breakdown.CellCert.CellAnalysis
open Breakdown.CellCert.CellFormula Breakdown.CellCert.CellEnergy

theorem localModeIntegrable : LocalModeIntegrableStatement := by
  intro m v G H hs K hK n a
  exact ⟨LowEntry.Internal.modeVec_int K hK m n hs.velocity_six a,
    fun b => LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two a b⟩

open Breakdown.CellCert.CellFormula.Internal.AngularMode in
theorem localAngularMode : LocalAngularModeStatement := by
  intro m v G _ hs n
  have locv : LocallyIntegrable v volume := hs.velocity_six.locallyIntegrable (by norm_num)
  have locG := loc_col hs.measurable_gradient hs.gradient_two
  have locf : ∀ l, LocallyIntegrable (fc v l) volume := fun l => loc_inner locv (unitVector l)
  have locg : ∀ l, LocallyIntegrable (gc G l) volume := by
    intro l
    unfold gc
    refine locallyIntegrable_finsetSum Finset.univ fun i _ => ?_
    exact locallyIntegrable_iff.2 fun K hK =>
      ((loc_inner (locG i) (unitVector l)).integrableOn_isCompact hK).smul_const _
  have hweak : ∀ l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * fc v l y = -∫ y, φ y * inner ℝ (gc G l y) (unitVector j) := by
    intro l φ hφ j
    have hw := hs.weak_gradient φ hφ j
    have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have hi1 := locv.integrable_smul_left_of_hasCompactSupport hcont hsupp
    have hi2 := (locG j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * fc v l y
        = ∫ y, L (fderiv ℝ φ y (unitVector j) • v y) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [L, fc, innerSL_apply_apply, real_inner_comm]
      _ = L (∫ y, fderiv ℝ φ y (unitVector j) • v y) := L.integral_comp_comm hi1
      _ = -L (∫ y, φ y • G y (unitVector j)) := by rw [hw, map_neg]
      _ = -∫ y, L (φ y • G y (unitVector j)) := by rw [L.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gc G l y) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gc_inner]
          simp [L, innerSL_apply_apply, real_inner_comm, unitVector]
  have hK := fun l => circleWeak (fc v l) (gc G l) (locf l) (locg l) (hweak l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun l => (hK l).1
  have hid := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun l =>
    (hK l).2 (wt (azimuth m n) a l) (wt_smooth _ a l) (hk ▸ wt_periodic _ a l)
  filter_upwards [hint, hid] with p h1 h2 hr
  obtain ⟨r, z⟩ := p
  exact point m n v G r z (fun l => (h1 l hr).1) (fun l => (h1 l hr).2) (fun a l => h2 a l hr)

private lemma cylPoint_add_axial (r θ z c : ℝ) :
    cylPoint r θ z + EuclideanSpace.single 2 c = cylPoint r θ (z + c) := by
  ext i
  fin_cases i <;> simp [cylPoint]

private lemma gradMode_add_axial (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (c : ℝ) (a b : Fin 3)
    (p : ℝ × ℝ) :
    gradMode m n (fun y => G (y + EuclideanSpace.single 2 c)) a b p = gradMode m n G a b (p.1, p.2 + c) := by
  simp only [gradMode, modeMat, cylPoint_add_axial]

theorem localAxisModeIntegrable : LocalAxisModeIntegrableStatement := by
  intro m v G H hsec R z₁ z₂ n a b
  set c : ℝ := z₁
  set w : Space := EuclideanSpace.single 2 c
  set G' : Space → (Space →L[ℝ] Space) := fun y => G (y + w)
  have hG1 : AEStronglyMeasurable G' volume :=
    hsec.measurable_gradient.comp_measurePreserving (measurePreserving_add_right volume w)
  have hG2 : Integrable (fun y => entrySq (G' y)) :=
    hsec.gradient_two.comp_add_right w
  let K : CellBox := ⟨0, max R 1, 0, max (z₂ - z₁) 1⟩
  have hK : IsCellBox K :=
    ⟨⟨le_rfl, lt_of_lt_of_le one_pos (le_max_right _ _)⟩, ⟨le_rfl, lt_of_lt_of_le one_pos (le_max_right _ _)⟩⟩
  have h := LowEntry.Internal.gradMode_int K hK m n hG1 hG2 a b
  have hw : K.lineWeight = fun r => r := funext fun r => by simp [CellBox.lineWeight, K]
  rw [hw] at h
  set f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * gradMode m n G' a b p
  set e : ℝ × ℝ → ℝ × ℝ := fun p => p + ((0 : ℝ), -c)
  have he : MeasurePreserving e volume volume := measurePreserving_add_right volume _
  have hemb : MeasurableEmbedding e := (MeasurableEquiv.addRight ((0 : ℝ), -c)).measurableEmbedding
  have h2 : IntegrableOn (f ∘ e) (e ⁻¹' K.rect) volume := (he.integrableOn_comp_preimage hemb).2 h
  have hfe : (f ∘ e) = fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode m n G a b p := by
    funext p
    simp only [Function.comp, f, e, G', w, gradMode_add_axial, Prod.fst_add, Prod.snd_add, add_zero]
    congr 2
    simp [c]
  rw [hfe] at h2
  refine h2.mono_set ?_
  rintro ⟨r, z⟩ ⟨⟨hr0, hrR⟩, ⟨hz1, hz2⟩⟩
  simp only [Set.mem_preimage, e, CellBox.rect, K, Set.mem_prod, Set.mem_Icc, Prod.fst_add, Prod.snd_add]
  refine ⟨⟨by simpa using hr0, by simpa using le_trans hrR (le_max_left _ _)⟩, ?_, ?_⟩
  · simp only [c]; linarith
  · simp only [c]
    have := le_max_left (z₂ - z₁) 1
    linarith

section

open Set Real
open Breakdown.FracInternal.ModeRectIntegrable Breakdown.FracInternal.ModeHeightAxis
open Breakdown.FracInternal.ModeStripIntegrable
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem localModeRectIntegrable : LocalModeRectIntegrableStatement := by
  intro k N c K S B L hL x hx n a b
  have hs := hx.1
  have hK := hL.box_valid
  have hsub := rect_sub K hK
  have hKm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  constructor
  · have hint0 : IntegrableOn _ (Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂) :=
      (six_int K.r₂ K.z₂ hs.velocity_six (velKernel L.order n a) (velKernel_cont L.order n a)
        (velKernel_bound L.order n a)).const_mul (1 / (2 * π) : ℂ)
    have hint := hint0.mono_set hsub
    refine IntegrableOn.congr_fun hint (fun p _ => ?_) hKm
    simp only [CellLayout.velMode]
    rw [modeVec_eq]
  · set ρ : ℝ := 2 * |K.r₂| + |K.z₂| + 1 with hρ
    have hρ0 : 0 < ρ := by positivity
    have hχ : IsTestScalar (radialCutoff ρ) := ⟨contDiff_radialCutoff hρ0, hasCompactSupport_radialCutoff hρ0⟩
    have hχ1 : ∀ y, |radialCutoff ρ y| ≤ 1 := fun y => by
      rw [abs_of_nonneg (radialCutoff_nonneg ρ y)]
      exact radialCutoff_le_one ρ y
    have h6 := Internal.cutoff_memLp_six hs hχ hχ1
    have hint0 : IntegrableOn _ (Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂) :=
      (six_int K.r₂ K.z₂ h6 (gradKernel L.order n a b) (gradKernel_cont L.order n a b)
        (gradKernel_bound L.order n a b)).const_mul (1 / (2 * π) : ℂ)
    have hint := hint0.mono_set hsub
    refine IntegrableOn.congr_fun hint (fun p hp => ?_) hKm
    simp only [CellLayout.gradModeOf]
    rw [gradMode_eq]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    have hp' := hsub hp
    have hn : ‖cylPoint p.1 θ p.2‖ ≤ ρ := by
      refine (cylPoint_norm _ _ _).trans ?_
      have h1 : |p.1| ≤ |K.r₂| := by rw [abs_of_nonneg hp'.1.1]; exact hp'.1.2.trans (le_abs_self _)
      have h2 : |p.2| ≤ |K.z₂| :=
        abs_le.2 ⟨by linarith [hp'.2.1, le_abs_self K.z₂, neg_abs_le K.z₂], hp'.2.2.trans (le_abs_self _)⟩
      rw [hρ]
      linarith
    simp only [radialCutoff_eq_one hρ0 hn, one_smul]

theorem localModeStripIntegrable : LocalModeStripIntegrableStatement := by
  intro m v G H hs n R z₁ z₂
  set Z : ℝ := |z₁| + |z₂| with hZ
  have hsub := strip_sub R z₁ z₂
  have hSm : MeasurableSet (Icc (0 : ℝ) R ×ˢ Icc z₁ z₂) := measurableSet_Icc.prod measurableSet_Icc
  constructor
  · intro a
    have hint := IntegrableOn.mono_set ((six_int R Z hs.velocity_six (velKernel m n a) (velKernel_cont m n a)
      (velKernel_bound m n a)).const_mul (1 / (2 * π) : ℂ)) hsub
    refine IntegrableOn.congr_fun hint (fun p _ => ?_) hSm
    rw [modeVec_eq]
  · intro a b
    set ρ : ℝ := 2 * |R| + |Z| + 1 with hρ
    have hρ0 : 0 < ρ := by positivity
    have hχ : IsTestScalar (radialCutoff ρ) := ⟨contDiff_radialCutoff hρ0, hasCompactSupport_radialCutoff hρ0⟩
    have hχ1 : ∀ y, |radialCutoff ρ y| ≤ 1 := fun y => by
      rw [abs_of_nonneg (radialCutoff_nonneg ρ y)]
      exact radialCutoff_le_one ρ y
    have h6 := Internal.cutoff_memLp_six hs hχ hχ1
    have hint := IntegrableOn.mono_set ((six_int R Z h6 (gradKernel m n a b) (gradKernel_cont m n a b)
      (gradKernel_bound m n a b)).const_mul (1 / (2 * π) : ℂ)) hsub
    refine IntegrableOn.congr_fun hint (fun p hp => ?_) hSm
    rw [gradMode_eq]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    have hp' := hsub hp
    have hn : ‖cylPoint p.1 θ p.2‖ ≤ ρ := by
      refine (cylPoint_norm _ _ _).trans ?_
      have h1 : |p.1| ≤ |R| := by rw [abs_of_nonneg hp'.1.1]; exact hp'.1.2.trans (le_abs_self _)
      have h2 : |p.2| ≤ |Z| :=
        abs_le.2 ⟨by linarith [hp'.2.1, le_abs_self Z, neg_abs_le Z], hp'.2.2.trans (le_abs_self _)⟩
      rw [hρ]
      linarith
    simp only [radialCutoff_eq_one hρ0 hn, one_smul]

end

end Breakdown.CertCell.LocalField
