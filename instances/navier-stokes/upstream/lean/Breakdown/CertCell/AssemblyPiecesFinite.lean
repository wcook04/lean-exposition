import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.FormNegativeFinite

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal.PiecesFinite

theorem rect_ae_le_halfPlane {B : CellBox} (hB : IsCellBox B) : B.rect ≤ᵐ[volume] halfPlane := by
  rw [ae_le_set]
  refine measure_mono_null (t := ({0} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {0})) ?_ ?_
  · rintro ⟨r, z⟩ ⟨⟨⟨hr1, -⟩, ⟨hz1, -⟩⟩, hn⟩
    simp only [halfPlane, Set.mem_prod, Set.mem_Ioi, not_and_or, not_lt] at hn
    rcases hn with h | h
    · left
      exact ⟨le_antisymm h (hB.r_order.1.trans hr1), Set.mem_univ _⟩
    · right
      exact ⟨Set.mem_univ _, le_antisymm h (hB.z_order.1.trans hz1)⟩
  · refine measure_union_null ?_ ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp

theorem measurableSet_rect (B : CellBox) : MeasurableSet B.rect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem formNeg_withCoercivity {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (q : Fin k → ℝ) (hc : (D.pieces q).c = D.coercivity) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    (D.withFormCoercivity D.coercivity).formNeg q v G H = D.formNeg q v G H := by
  have hp : (D.withFormCoercivity D.coercivity).pieces q = D.pieces q := by
    simp only [CellLayerData.withFormCoercivity]
    rw [← hc]
  unfold CellLayerData.formNeg CellLayerData.labelDensity
  rw [hp]
  rfl

theorem cellNeg_le_formNeg {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (hM : IsCellMesh D.mesh) (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    cellNeg D K q v G H ≤ D.formNeg q v G H := by
  have h := rect_ae_le_halfPlane (hM.box_valid K)
  unfold cellNeg CellLayerData.formNeg
  exact add_le_add (ENNReal.tsum_le_tsum fun ι => lintegral_mono_set' h) (lintegral_mono_set' h)

theorem quad_gap_le (a : TailBand.PointCoef) (s st mg wg len cc gc vc c x2 xc x1 xo x0 : ℝ)
    (h1 : 0 ≤ x1) (h0 : 0 ≤ x0) (hs : |s| ≤ c) (hst : |st| ≤ c) (hmg : |mg| ≤ c) (hwg : |wg| ≤ c)
    (hcc : |cc| ≤ c) (hgc : |gc| ≤ c) (hvc : |vc| ≤ c) (hl1 : c⁻¹ ≤ len) (hl2 : len ≤ c) :
    |a.quad x2 xc x1 xo x0 - (a.withStretch s st mg wg len cc gc vc).quad x2 xc x1 xo x0|
      ≤ (2 * c + c ^ 3 + c ^ 2) * (xo ^ 2 + x1 ^ 2 + x0 ^ 2) := by
  have c0 : 0 ≤ c := (abs_nonneg s).trans hs
  have l0 : 0 ≤ len := (inv_nonneg.2 c0).trans hl1
  have li : len⁻¹ ≤ c := by
    rcases c0.lt_or_eq with h | h
    · have := inv_anti₀ (inv_pos.2 h) hl1
      rwa [inv_inv] at this
    · have : len = 0 := le_antisymm (hl2.trans h.ge) l0
      rw [this, inv_zero]
      exact c0
  have e : a.quad x2 xc x1 xo x0 - (a.withStretch s st mg wg len cc gc vc).quad x2 xc x1 xo x0
      = (st + cc) * xo ^ 2 + (s * wg * len / 2 + gc) * x1 ^ 2 + (s * wg * len⁻¹ / 2 + vc) * x0 ^ 2
        + s * mg * (x1 * x0) := by
    simp only [TailBand.PointCoef.quad, TailBand.PointCoef.withStretch]
    ring
  have swg : |s * wg| ≤ c * c := by
    rw [abs_mul]
    exact mul_le_mul hs hwg (abs_nonneg _) c0
  have k1 : |st + cc| ≤ 2 * c := (abs_add_le _ _).trans (by linarith)
  have k2 : |s * wg * len / 2 + gc| ≤ c ^ 3 / 2 + c := by
    have h3 : |s * wg * len| ≤ c * c * c := by
      rw [abs_mul, abs_of_nonneg l0]
      exact mul_le_mul swg hl2 l0 (by positivity)
    have e3 : c * c * c = c ^ 3 := by ring
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_two]
    linarith
  have k3 : |s * wg * len⁻¹ / 2 + vc| ≤ c ^ 3 / 2 + c := by
    have h3 : |s * wg * len⁻¹| ≤ c * c * c := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.2 l0)]
      exact mul_le_mul swg li (inv_nonneg.2 l0) (by positivity)
    have e3 : c * c * c = c ^ 3 := by ring
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_two]
    linarith
  have k4 : |s * mg| ≤ c * c := by
    rw [abs_mul]
    exact mul_le_mul hs hmg (abs_nonneg _) c0
  have p10 : 0 ≤ x1 * x0 := mul_nonneg h1 h0
  have t1 : |(st + cc) * xo ^ 2| ≤ 2 * c * xo ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg xo)]
    exact mul_le_mul_of_nonneg_right k1 (sq_nonneg _)
  have t2 : |(s * wg * len / 2 + gc) * x1 ^ 2| ≤ (c ^ 3 / 2 + c) * x1 ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg x1)]
    exact mul_le_mul_of_nonneg_right k2 (sq_nonneg _)
  have t3 : |(s * wg * len⁻¹ / 2 + vc) * x0 ^ 2| ≤ (c ^ 3 / 2 + c) * x0 ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg x0)]
    exact mul_le_mul_of_nonneg_right k3 (sq_nonneg _)
  have t4 : |s * mg * (x1 * x0)| ≤ c * c * (x1 * x0) := by
    rw [abs_mul, abs_of_nonneg p10]
    exact mul_le_mul_of_nonneg_right k4 p10
  rw [e]
  have a1 := abs_add_le ((st + cc) * xo ^ 2 + (s * wg * len / 2 + gc) * x1 ^ 2
    + (s * wg * len⁻¹ / 2 + vc) * x0 ^ 2) (s * mg * (x1 * x0))
  have a2 := abs_add_le ((st + cc) * xo ^ 2 + (s * wg * len / 2 + gc) * x1 ^ 2)
    ((s * wg * len⁻¹ / 2 + vc) * x0 ^ 2)
  have a3 := abs_add_le ((st + cc) * xo ^ 2) ((s * wg * len / 2 + gc) * x1 ^ 2)
  have q1 : 0 ≤ c * c * (x1 - x0) ^ 2 := by positivity
  have q2 : 0 ≤ c ^ 3 * x1 ^ 2 := by positivity
  have q3 : 0 ≤ c ^ 3 * x0 ^ 2 := by positivity
  have q4 : 0 ≤ c * x1 ^ 2 := by positivity
  have q5 : 0 ≤ c * x0 ^ 2 := by positivity
  have q6 : 0 ≤ c ^ 2 * xo ^ 2 := by positivity
  have q7 : 0 ≤ c ^ 3 * xo ^ 2 := by positivity
  nlinarith [t1, t2, t3, t4, a1, a2, a3]

theorem ofReal_split (u d M R2 X Y : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R2) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : u ≤ d + M * (3 * X + R2 * Y)) :
    ENNReal.ofReal u ≤ ENNReal.ofReal d
      + ENNReal.ofReal M * (3 * ENNReal.ofReal X + ENNReal.ofReal R2 * ENNReal.ofReal Y) := by
  refine (ENNReal.ofReal_le_ofReal h).trans (ENNReal.ofReal_add_le.trans (le_of_eq ?_))
  rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_mul hR, ENNReal.ofReal_ofNat]

def gradAmount (m : ℕ) (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cnormSq (labelGrad m ι G p) * p.1)

def velAmount (m : ℕ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cnormSq (labelVel m ι v p) / (p.1 ^ 2 + p.2 ^ 2) * p.1)

def chargeMajorant (M R2 : ℝ) (m : ℕ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal M * (3 * gradAmount m G ι p + ENNReal.ofReal R2 * velAmount m v ι p)

theorem aemeasurable_chargeMajorant {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (M R2 : ℝ) (m : ℕ) (ι : ℤ × ℤ) :
    AEMeasurable (chargeMajorant M R2 m v G ι) (volume.restrict halfPlane) := by
  have hG : AEMeasurable (gradAmount m G ι) (volume.restrict halfPlane) :=
    ((Internal.FormNegative.continuous_cnormSq_local.comp_aestronglyMeasurable
      (TailBand.aestronglyMeasurable_labelFields hv m ι).2.1).aemeasurable.mul
      measurable_fst.aemeasurable).ennreal_ofReal
  have hV : AEMeasurable (velAmount m v ι) (volume.restrict halfPlane) :=
    (((Internal.FormNegative.continuous_cnormSq_local.comp_aestronglyMeasurable
      (TailBand.aestronglyMeasurable_labelFields hv m ι).1).aemeasurable.div
      ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).aemeasurable).mul
      measurable_fst.aemeasurable).ennreal_ofReal
  exact ((hG.const_mul 3).add (hV.const_mul _)).const_mul _

theorem tsum_chargeMajorant_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (M R2 : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∑' ι : ℤ × ℤ, ∫⁻ p in halfPlane, chargeMajorant M R2 m v G ι p < ⊤ := by
  have hG : ∀ ι, AEMeasurable (fun p => 3 * gradAmount m G ι p) (volume.restrict halfPlane) := fun ι =>
    (((Internal.FormNegative.continuous_cnormSq_local.comp_aestronglyMeasurable
      (TailBand.aestronglyMeasurable_labelFields hv m ι).2.1).aemeasurable.mul
      measurable_fst.aemeasurable).ennreal_ofReal).const_mul 3
  have e : ∀ ι, ∫⁻ p in halfPlane, chargeMajorant M R2 m v G ι p
      = ENNReal.ofReal M * (3 * (∫⁻ p in halfPlane, gradAmount m G ι p)
        + ENNReal.ofReal R2 * ∫⁻ p in halfPlane, velAmount m v ι p) := by
    intro ι
    unfold chargeMajorant
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' (hG ι),
      lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [tsum_congr e, ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (by simp) (Internal.FormNegative.gradient_sum_lt_top m hm hv),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Internal.FormNegative.velocity_inverse_sum_lt_top m hm hv)⟩)

theorem setLIntegral_le_add {s t : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hst : s ≤ᵐ[volume] t)
    {f h w : ℝ × ℝ → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict t)) (hf : ∀ p ∈ s, f p ≤ h p + w p) :
    ∫⁻ p in s, f p ≤ (∫⁻ p in s, h p) + ∫⁻ p in t, w p :=
  calc ∫⁻ p in s, f p ≤ ∫⁻ p in s, (h p + w p) := setLIntegral_mono' hs hf
    _ = (∫⁻ p in s, h p) + ∫⁻ p in s, w p :=
      lintegral_add_right' _ (hw.mono_measure (Measure.restrict_mono_ae hst))
    _ ≤ (∫⁻ p in s, h p) + ∫⁻ p in t, w p := add_le_add le_rfl (lintegral_mono_set' hst)

theorem vel_le (p : ℝ × ℝ) (a r z : ℝ) (ha : 0 ≤ a) (h1 : 0 ≤ p.1) (h2 : 0 ≤ p.2) (hr : p.1 ≤ r)
    (hz : p.2 ≤ z) : a * p.1 ≤ (r ^ 2 + z ^ 2) * (a / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
  by_cases h0 : p.1 ^ 2 + p.2 ^ 2 = 0
  · have e : p.1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])
    simp [e]
  · have hpos : 0 < p.1 ^ 2 + p.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have hle : p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2 + z ^ 2 := by
      have := pow_le_pow_left₀ h1 hr 2
      have := pow_le_pow_left₀ h2 hz 2
      linarith
    have e : a * p.1 = (p.1 ^ 2 + p.2 ^ 2) * (a / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hle (mul_nonneg (div_nonneg ha hpos.le) h1)

end Internal.PiecesFinite

open Internal.PiecesFinite in
theorem cellPiecesFinite_of_azimuth {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : CellCalculusEntry D) (hm : 1 ≤ D.azimuthOrder) (hM : IsCellMesh D.mesh)
    (hN : FormNegFinite D D.coercivity) (hc : ∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity)
    (hreg : EntryChargesRegular D R) : CellPiecesFinite D R := by
  intro K q v G H g κ F Pg ht
  have hv := ht.perturbation
  have hB := hM.box_valid K
  have hae := rect_ae_le_halfPlane hB
  have hrect := measurableSet_rect (D.mesh.box K)
  obtain ⟨c, hcb⟩ := hreg.bounded K
  have hp0 : ((D.mesh.box K).r₁, (D.mesh.box K).z₁) ∈ (D.mesh.box K).rect :=
    ⟨⟨le_rfl, hB.r_order.2.le⟩, ⟨le_rfl, hB.z_order.2.le⟩⟩
  have c0 : 0 ≤ c := (abs_nonneg _).trans (hcb (0, 0) _ hp0).1
  obtain ⟨Mc, hMc⟩ : ∃ Mc : ℝ, Mc = 2 * c + c ^ 3 + c ^ 2 := ⟨_, rfl⟩
  have hM0 : 0 ≤ Mc := by rw [hMc]; positivity
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, R2 = (D.mesh.box K).r₂ ^ 2 + (D.mesh.box K).z₂ ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R2 := by rw [hR2]; positivity
  have hpt : ∀ ι, ∀ p ∈ (D.mesh.box K).rect,
      |D.labelDensity q v G H ι p - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q)
          D.cert.weightFn (D.charges (some K)) (R.entryCharges K ι) D.azimuthOrder ι v G H p| * p.1
        ≤ Mc * (3 * (cnormSq (labelGrad D.azimuthOrder ι G p) * p.1)
          + R2 * (cnormSq (labelVel D.azimuthOrder ι v p) / (p.1 ^ 2 + p.2 ^ 2) * p.1)) ∧
      0 ≤ p.1 := by
    intro ι p hp
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hcb ι p hp
    have hp1 : 0 ≤ p.1 := hB.r_order.1.trans hp.1.1
    have hp2 : 0 ≤ p.2 := hB.z_order.1.trans hp.2.1
    have eD : D.labelDensity q v G H ι p = TailBand.labelQuad (TailBand.modeCoef (D.pieces q) (D.cert.period q)
        (D.bounds q) D.cert.weightFn D.azimuthOrder ι p) D.azimuthOrder ι v G H p :=
      TailBand.modeTerm_eq_labelQuad _ _ _ _ _ _ _ _ _ _
    have hg := quad_gap_le (TailBand.modeCoef (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
        D.azimuthOrder ι p) (R.entryCharges K ι).stretchConst ((D.charges (some K)).curl ι p)
      ((D.charges (some K)).product ι p) ((D.charges (some K)).gradient ι p) ((D.charges (some K)).length ι p)
      ((R.entryCharges K ι).curlCharge p) ((R.entryCharges K ι).gradCharge p) ((R.entryCharges K ι).velCharge p) c
      (Real.sqrt (cnormSq (labelHess D.azimuthOrder ι H p)))
      (Real.sqrt (cnormSq (curlGradOfSecondDeriv (labelHess D.azimuthOrder ι H p))))
      (Real.sqrt (cnormSq (labelGrad D.azimuthOrder ι G p)))
      (Real.sqrt (cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p))))
      (Real.sqrt (cnormSq (labelVel D.azimuthOrder ι v p)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) b4 b5 b6 b7 b1 b2 b3 b8 b9
    rw [Real.sq_sqrt (Internal.FormNegative.cnormSq_nonneg_local _),
      Real.sq_sqrt (Internal.FormNegative.cnormSq_nonneg_local _),
      Real.sq_sqrt (Internal.FormNegative.cnormSq_nonneg_local _), ← hMc] at hg
    have q2 : cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p)) ≤ 2 * cnormSq (labelGrad D.azimuthOrder ι G p) :=
      Coercive.Internal.FieldModes.cnormSq_curlOfGrad_le _
    have hvel := vel_le p (cnormSq (labelVel D.azimuthOrder ι v p)) _ _
      (Internal.FormNegative.cnormSq_nonneg_local _) hp1 hp2 hp.1.2 hp.2.2
    rw [← hR2] at hvel
    refine ⟨?_, hp1⟩
    rw [eD]
    have hG0 := Internal.FormNegative.cnormSq_nonneg_local (labelGrad D.azimuthOrder ι G p)
    have hV0 := Internal.FormNegative.cnormSq_nonneg_local (labelVel D.azimuthOrder ι v p)
    have s1 := mul_le_mul_of_nonneg_right hg hp1
    have s2 : (cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p)) + cnormSq (labelGrad D.azimuthOrder ι G p)
        + cnormSq (labelVel D.azimuthOrder ι v p)) * p.1
        ≤ 3 * (cnormSq (labelGrad D.azimuthOrder ι G p) * p.1)
          + R2 * (cnormSq (labelVel D.azimuthOrder ι v p) / (p.1 ^ 2 + p.2 ^ 2) * p.1) := by
      nlinarith [mul_le_mul_of_nonneg_right q2 hp1]
    have s3 := mul_le_mul_of_nonneg_left s2 hM0
    unfold TailBand.offModeDensity
    unfold TailBand.labelQuad at s1 ⊢
    calc _ ≤ _ := s1
      _ = Mc * ((cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p)) + cnormSq (labelGrad D.azimuthOrder ι G p)
        + cnormSq (labelVel D.azimuthOrder ι v p)) * p.1) := by ring
      _ ≤ _ := s3
  have hneg : ∀ ι, ∀ p ∈ (D.mesh.box K).rect,
      ENNReal.ofReal (-(TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
          (D.charges (some K)) (R.entryCharges K ι) D.azimuthOrder ι v G H p * p.1))
        ≤ ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1)) + chargeMajorant Mc R2 D.azimuthOrder v G ι p := by
    intro ι p hp
    obtain ⟨h1, hp1⟩ := hpt ι p hp
    have hl := mul_le_mul_of_nonneg_right
      (le_abs_self (D.labelDensity q v G H ι p - TailBand.offModeDensity (D.pieces q) (D.cert.period q)
        (D.bounds q) D.cert.weightFn (D.charges (some K)) (R.entryCharges K ι) D.azimuthOrder ι v G H p)) hp1
    exact ofReal_split _ _ _ _ _ _ hM0 hR0 (mul_nonneg (Internal.FormNegative.cnormSq_nonneg_local _) hp1)
      (mul_nonneg (div_nonneg (Internal.FormNegative.cnormSq_nonneg_local _) (by positivity)) hp1)
      (by nlinarith [h1, hl])
  have hpos : ∀ ι, ∀ p ∈ (D.mesh.box K).rect,
      ENNReal.ofReal (TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
          (D.charges (some K)) (R.entryCharges K ι) D.azimuthOrder ι v G H p * p.1)
        ≤ ENNReal.ofReal (D.labelDensity q v G H ι p * p.1) + chargeMajorant Mc R2 D.azimuthOrder v G ι p := by
    intro ι p hp
    obtain ⟨h1, hp1⟩ := hpt ι p hp
    have hl := mul_le_mul_of_nonneg_right
      (neg_abs_le (D.labelDensity q v G H ι p - TailBand.offModeDensity (D.pieces q) (D.cert.period q)
        (D.bounds q) D.cert.weightFn (D.charges (some K)) (R.entryCharges K ι) D.azimuthOrder ι v G H p)) hp1
    exact ofReal_split _ _ _ _ _ _ hM0 hR0 (mul_nonneg (Internal.FormNegative.cnormSq_nonneg_local _) hp1)
      (mul_nonneg (div_nonneg (Internal.FormNegative.cnormSq_nonneg_local _) (by positivity)) hp1)
      (by nlinarith [h1, hl])
  have hW := tsum_chargeMajorant_lt_top hv Mc R2 D.azimuthOrder hm
  have hWm := aemeasurable_chargeMajorant hv Mc R2 D.azimuthOrder
  refine ⟨?_, ?_, ?_⟩
  · refine (cellNeg_le_formNeg D hM K q v G H).trans_lt ?_
    rw [← formNeg_withCoercivity D q (hc q ht.param)]
    exact hN q ht.param v G H g hv
  · have hP := ht.pos_finite
    unfold cellPos at hP
    unfold offPos
    calc _ ≤ ∑' ι : ℤ × ℤ, ((∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1))
          + ∫⁻ p in halfPlane, chargeMajorant Mc R2 D.azimuthOrder v G ι p) :=
          ENNReal.tsum_le_tsum fun ι => by
            split_ifs
            · exact zero_le
            · exact setLIntegral_le_add hrect hae (hWm ι) (hpos ι)
      _ = _ := ENNReal.tsum_add
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt le_self_add hP, hW⟩
  · have hNf : cellNeg D K q v G H < ⊤ := by
      refine (cellNeg_le_formNeg D hM K q v G H).trans_lt ?_
      rw [← formNeg_withCoercivity D q (hc q ht.param)]
      exact hN q ht.param v G H g hv
    unfold cellNeg at hNf
    unfold offNeg
    calc _ ≤ ∑' ι : ℤ × ℤ, ((∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1)))
          + ∫⁻ p in halfPlane, chargeMajorant Mc R2 D.azimuthOrder v G ι p) :=
          ENNReal.tsum_le_tsum fun ι => by
            split_ifs
            · exact zero_le
            · exact setLIntegral_le_add hrect hae (hWm ι) (hneg ι)
      _ = _ := ENNReal.tsum_add
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt le_self_add hNf, hW⟩

theorem cellPiecesFiniteHolds_of_azimuth :
    ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D),
      1 ≤ D.azimuthOrder → IsCellMesh D.mesh → CellCalculusConditions D R → CoefficientLowerBounds D D.coercivity →
      FormNegFinite D D.coercivity → (∀ q ∈ D.cert.params, (D.pieces q).c = D.coercivity) →
      EntryChargesRegular D R → CellPiecesFinite D R :=
  fun D R hm hM _ _ hN hc hreg => cellPiecesFinite_of_azimuth D R hm hM hN hc hreg

theorem cellPiecesFiniteHolds : CellPiecesFiniteHolds :=
  fun D R hA _ hM _ _ hN hc hreg => cellPiecesFinite_of_azimuth D R hA.field.azimuth_pos hM hN hc hreg

end Assembly

end CertCell

end Breakdown
