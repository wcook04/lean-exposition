import Breakdown.CertCell.InstancePairSharesCut
import Breakdown.Cert.CoerciveSmoothPressure

open scoped ENNReal ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

open Instance

namespace Internal

open Bridge.Internal.ModeFlip (flipPoint_apply frameSign_mul_self flipPoint_smul)

def flipLin : Space →ₗ[ℝ] Space where
  toFun := flipPoint
  map_add' x y := by
    ext i
    simp only [flipPoint_apply, PiLp.add_apply]
    ring
  map_smul' c x := flipPoint_smul c x

theorem flipLin_apply (y : Space) : flipLin y = flipPoint y := rfl

theorem labelFlip_labelFlip (ι : ℤ × ℤ) : labelFlip (labelFlip ι) = ι := by
  ext <;> simp [labelFlip]

theorem frameUnit_add_int (θ : ℝ) (k : ℤ) (a : Fin 3) :
    frameUnit (θ + 2 * Real.pi * k) a = frameUnit θ a := by
  have hc : Real.cos (θ + 2 * Real.pi * k) = Real.cos θ := by
    rw [show θ + 2 * Real.pi * k = θ + k * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi]
  have hs : Real.sin (θ + 2 * Real.pi * k) = Real.sin θ := by
    rw [show θ + 2 * Real.pi * k = θ + k * (2 * Real.pi) by ring, Real.sin_add_int_mul_two_pi]
  fin_cases a <;> simp [frameUnit, CellCert.CellAnalysis.radialUnit, CellCert.CellAnalysis.angularUnit, hc, hs]

theorem frameMap_add_int (θ : ℝ) (k : ℤ) (x : Fin 3 → Fin 3 → ℝ) :
    CellMatField.frameMap (θ + 2 * Real.pi * k) x = CellMatField.frameMap θ x := by
  simp only [CellMatField.frameMap, frameUnit_add_int]

theorem flipPoint_frameUnit (θ : ℝ) (a : Fin 3) :
    flipPoint (frameUnit θ a) = frameSign a • frameUnit (-θ) a := by
  ext i
  rw [flipPoint_apply, PiLp.smul_apply, smul_eq_mul]
  fin_cases a <;> fin_cases i <;>
    simp [frameUnit, frameSign, CellCert.CellAnalysis.radialUnit, CellCert.CellAnalysis.angularUnit,
      CellCert.CellAnalysis.axialUnit]

theorem inner_flipPoint (v u : Space) : inner ℝ v (flipPoint u) = inner ℝ (flipPoint v) u := by
  simp only [PiLp.inner_apply, flipPoint_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem frameMap_apply (θ : ℝ) (x : Fin 3 → Fin 3 → ℝ) (u : Space) :
    CellMatField.frameMap θ x u = ∑ a : Fin 3, ∑ b : Fin 3, (x a b * inner ℝ (frameUnit θ b) u) • frameUnit θ a := by
  simp only [CellMatField.frameMap, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_smul]

theorem frameMap_sum {ι : Type*} (θ : ℝ) (s : Finset ι) (x : ι → Fin 3 → Fin 3 → ℝ) :
    ∑ i ∈ s, CellMatField.frameMap θ (x i) = CellMatField.frameMap θ (fun a b => ∑ i ∈ s, x i a b) := by
  simp only [CellMatField.frameMap, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem flip_frameMap (θ : ℝ) (x : Fin 3 → Fin 3 → ℝ) (u : Space) :
    flipPoint (CellMatField.frameMap θ x (flipPoint u))
      = CellMatField.frameMap (-θ) (fun a b => frameSign a * frameSign b * x a b) u := by
  rw [frameMap_apply, frameMap_apply, ← flipLin_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, flipLin_apply, flipPoint_frameUnit, inner_flipPoint, flipPoint_frameUnit, inner_smul_left,
    smul_smul]
  congr 1
  simp only [conj_trivial]
  ring

theorem sum_labelFlip {S : Finset (ℤ × ℤ)} (hS : ∀ ι ∈ S, labelFlip ι ∈ S) (f : ℤ × ℤ → ℝ) :
    ∑ ι ∈ S, f (labelFlip ι) = ∑ ι ∈ S, f ι :=
  Finset.sum_nbij' labelFlip labelFlip hS hS (fun ι _ => labelFlip_labelFlip ι)
    (fun ι _ => labelFlip_labelFlip ι) (fun _ _ => rfl)

theorem pointAngle_flipPoint (y : Space) : ∃ k : ℤ, pointAngle (flipPoint y) = -pointAngle y + 2 * Real.pi * k := by
  obtain ⟨h0, h1, -⟩ := flipPoint_coord y
  have e : ((flipPoint y 0 : ℝ) : ℂ) + ((flipPoint y 1 : ℝ) : ℂ) * Complex.I
      = starRingEnd ℂ (((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I) := by
    rw [h0, h1]
    simp [Complex.conj_ofReal]
  unfold pointAngle
  rw [e, Complex.arg_conj]
  split_ifs with h
  · exact ⟨1, by rw [h]; push_cast; ring⟩
  · exact ⟨0, by push_cast; ring⟩

theorem labelPhase_flip_angle (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) (k : ℤ) :
    labelPhase m ι σ (-θ + 2 * Real.pi * k) = labelPhase m (labelFlip ι) σ θ := by
  unfold labelPhase
  have e : (((2 * Real.pi * (labelTime ι : ℝ) * σ + (labelAzimuth m ι : ℝ) * (-θ + 2 * Real.pi * k) : ℝ)) : ℂ)
        * Complex.I
      = (((2 * Real.pi * (labelTime (labelFlip ι) : ℝ) * σ + (labelAzimuth m (labelFlip ι) : ℝ) * θ : ℝ)) : ℂ)
        * Complex.I + ((labelAzimuth m ι * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [labelTime, labelAzimuth, labelFlip]
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem pointPlane_flipPoint (y : Space) : pointPlane (flipPoint y) = ((pointPlane y).1, -(pointPlane y).2) := by
  obtain ⟨h0, h1, h2⟩ := flipPoint_coord y
  simp only [pointPlane, h0, h1, h2, neg_sq]

theorem mem_solid_iff (K : CellCert.CellAnalysis.CellBox) (y : Space) :
    y ∈ K.solid ↔ cylFold y ∈ K.rect := by
  simp only [CellCert.CellAnalysis.CellBox.solid, CellCert.CellAnalysis.CellBox.rect, cylFold,
    CellCert.CellAnalysis.cylRadius, CellCert.CellAnalysis.cylHeight, Set.mem_ofPred_eq, Set.mem_prod,
    Set.mem_Icc]
  tauto

theorem planeValue_sum_flip {count : ℕ} (F : CellMatField count) (box : Fin count → CellCert.CellAnalysis.CellBox)
    (hF : ∀ K ι, ι ∈ F.labels K → labelFlip ι ∈ F.labels K) (m : ℕ) (K : Fin count) (a b : Fin 3) (σ θ : ℝ)
    (k : ℤ) (p : ℝ × ℝ) (hz : p.2 ≠ 0) :
    ∑ ι ∈ F.labels K, (labelPhase m ι σ (-θ + 2 * Real.pi * k) * F.planeValue box K ι a b (p.1, -p.2)).re
      = frameSign a * frameSign b * ∑ ι ∈ F.labels K, (labelPhase m ι σ θ * F.planeValue box K ι a b p).re := by
  simp only [labelPhase_flip_angle]
  have hS := hF K
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have h1 : ∀ ι, F.planeValue box K ι a b (p.1, -p.2) = (F.comp K ι a b).eval (box K) (p.1, -p.2) := by
      intro ι
      simp only [CellMatField.planeValue, labelValueAt]
      rw [if_pos (by linarith)]
    have h2 : ∀ ι, F.planeValue box K ι a b p
        = ((frameSign a * frameSign b : ℝ) : ℂ) * (F.comp K (labelFlip ι) a b).eval (box K) (p.1, -p.2) := by
      intro ι
      simp only [CellMatField.planeValue, labelValueAt]
      rw [if_neg (by linarith)]
    simp only [h1, h2]
    rw [← sum_labelFlip hS (fun ι => (labelPhase m ι σ θ * (((frameSign a * frameSign b : ℝ) : ℂ)
      * (F.comp K (labelFlip ι) a b).eval (box K) (p.1, -p.2))).re)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [labelFlip_labelFlip]
    have e : labelPhase m (labelFlip ι) σ θ * (((frameSign a * frameSign b : ℝ) : ℂ)
        * (F.comp K ι a b).eval (box K) (p.1, -p.2))
        = ((frameSign a * frameSign b : ℝ) : ℂ) * (labelPhase m (labelFlip ι) σ θ
          * (F.comp K ι a b).eval (box K) (p.1, -p.2)) := by ring
    rw [e, Complex.re_ofReal_mul]
    have ha := frameSign_mul_self a
    have hb := frameSign_mul_self b
    linear_combination (-(labelPhase m (labelFlip ι) σ θ * (F.comp K ι a b).eval (box K) (p.1, -p.2)).re)
      * (ha + frameSign a * frameSign a * hb)
  · have h1 : ∀ ι, F.planeValue box K ι a b (p.1, -p.2)
        = ((frameSign a * frameSign b : ℝ) : ℂ) * (F.comp K (labelFlip ι) a b).eval (box K) p := by
      intro ι
      simp only [CellMatField.planeValue, labelValueAt]
      rw [if_neg (by linarith), neg_neg]
    have h2 : ∀ ι, F.planeValue box K ι a b p = (F.comp K ι a b).eval (box K) p := by
      intro ι
      simp only [CellMatField.planeValue, labelValueAt]
      rw [if_pos hpos.le]
    simp only [h1, h2]
    rw [Finset.mul_sum]
    rw [← sum_labelFlip hS (fun ι => frameSign a * frameSign b * (labelPhase m ι σ θ
      * (F.comp K ι a b).eval (box K) p).re)]
    refine Finset.sum_congr rfl fun ι _ => ?_
    have e : labelPhase m (labelFlip ι) σ θ * (((frameSign a * frameSign b : ℝ) : ℂ)
        * (F.comp K (labelFlip ι) a b).eval (box K) p)
        = ((frameSign a * frameSign b : ℝ) : ℂ) * (labelPhase m (labelFlip ι) σ θ
          * (F.comp K (labelFlip ι) a b).eval (box K) p) := by ring
    rw [e, Complex.re_ofReal_mul]

theorem pin_field_flip {count : ℕ} (F : CellMatField count) (box : Fin count → CellCert.CellAnalysis.CellBox)
    (hF : ∀ K ι, ι ∈ F.labels K → labelFlip ι ∈ F.labels K) (m : ℕ) (σ : ℝ) (y : Space) (hy : y 2 ≠ 0)
    (u : Space) :
    F.field box m σ (flipPoint y) u = flipPoint (F.field box m σ y (flipPoint u)) := by
  obtain ⟨k, hk⟩ := pointAngle_flipPoint y
  unfold CellMatField.field
  rw [_root_.sum_apply, _root_.sum_apply]
  conv_rhs => rw [← flipLin_apply, map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [flipLin_apply]
  by_cases hs : y ∈ (box K).solid
  · have hs' : flipPoint y ∈ (box K).solid := by
      rw [mem_solid_iff, cylFold_flipPoint, ← mem_solid_iff]
      exact hs
    rw [Set.indicator_of_mem hs', Set.indicator_of_mem hs, frameMap_sum, frameMap_sum, flip_frameMap, hk,
      frameMap_add_int, pointPlane_flipPoint]
    congr 2
    funext a b
    rw [planeValue_sum_flip F box hF m K a b σ (pointAngle y) k (pointPlane y) hy]
  · have hs' : flipPoint y ∉ (box K).solid := by
      rw [mem_solid_iff, cylFold_flipPoint, ← mem_solid_iff]
      exact hs
    rw [Set.indicator_of_notMem hs', Set.indicator_of_notMem hs]
    simp [flipPoint_zero]

theorem pin_field_support {count : ℕ} (F : CellMatField count) (box : Fin count → CellCert.CellAnalysis.CellBox)
    (m : ℕ) (σ : ℝ) (y : Space) (h : F.field box m σ y ≠ 0) : ∃ K, cylFold y ∈ (box K).rect := by
  by_contra hno
  push Not at hno
  apply h
  unfold CellMatField.field
  refine Finset.sum_eq_zero fun K _ => Set.indicator_of_notMem (fun hs => hno K ?_) _
  exact (mem_solid_iff _ _).1 hs

open Coercive.RotationInternal (axialRot_apply_zero axialRot_apply_one axialRot_apply_two space_ext)

theorem planePoint_coord (p : ℝ × ℝ) : planePoint p 0 = p.1 ∧ planePoint p 1 = 0 ∧ planePoint p 2 = p.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [planePoint, CellCert.CellAnalysis.cylPoint]

theorem axialRot_unitVector (φ : ℝ) (b : Fin 3) : axialRot φ (unitVector b) = frameUnit φ b := by
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 by fin_cases b <;> simp) with rfl | rfl | rfl <;>
  apply space_ext <;>
    simp [axialRot_apply_zero, axialRot_apply_one, axialRot_apply_two, unitVector, frameUnit,
      CellCert.CellAnalysis.radialUnit, CellCert.CellAnalysis.angularUnit, CellCert.CellAnalysis.axialUnit]

theorem axialRot_neg_coord (φ : ℝ) (v : Space) (a : Fin 3) : axialRot (-φ) v a = inner ℝ v (frameUnit φ a) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl
  · rw [axialRot_apply_zero]
    simp [frameUnit, CellCert.CellAnalysis.radialUnit]
  · rw [axialRot_apply_one]
    simp [frameUnit, CellCert.CellAnalysis.angularUnit]
  · rw [axialRot_apply_two]
    simp [frameUnit, CellCert.CellAnalysis.axialUnit]

theorem frameUnit_orth (θ : ℝ) (i j : Fin 3) :
    inner ℝ (frameUnit θ i) (frameUnit θ j) = if i = j then 1 else 0 := by
  have h := Real.cos_sq_add_sin_sq θ
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [frameUnit, CellCert.CellAnalysis.radialUnit,
      CellCert.CellAnalysis.angularUnit, CellCert.CellAnalysis.axialUnit] <;> nlinarith [h]

theorem inner_frameMap_frame (θ : ℝ) (x : Fin 3 → Fin 3 → ℝ) (a b : Fin 3) :
    inner ℝ (CellMatField.frameMap θ x (frameUnit θ b)) (frameUnit θ a) = x a b := by
  rw [frameMap_apply]
  simp only [sum_inner, inner_smul_left, frameUnit_orth, conj_trivial, mul_ite, mul_one, mul_zero]
  simp

theorem labelPhase_add_int (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) (k : ℤ) :
    labelPhase m ι σ (θ + 2 * Real.pi * k) = labelPhase m ι σ θ := by
  unfold labelPhase
  have e : (((2 * Real.pi * (labelTime ι : ℝ) * σ + (labelAzimuth m ι : ℝ) * (θ + 2 * Real.pi * k) : ℝ)) : ℂ)
        * Complex.I
      = (((2 * Real.pi * (labelTime ι : ℝ) * σ + (labelAzimuth m ι : ℝ) * θ : ℝ)) : ℂ)
        * Complex.I + ((labelAzimuth m ι * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem rot_planePoint_coord (φ : ℝ) (p : ℝ × ℝ) :
    axialRot φ (planePoint p) 0 = Real.cos φ * p.1 ∧ axialRot φ (planePoint p) 1 = Real.sin φ * p.1 ∧
      axialRot φ (planePoint p) 2 = p.2 := by
  obtain ⟨h0, h1, h2⟩ := planePoint_coord p
  rw [axialRot_apply_zero, axialRot_apply_one, axialRot_apply_two, h0, h1, h2]
  refine ⟨by ring, by ring, rfl⟩

theorem pointAngle_rot (φ : ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ∃ k : ℤ, pointAngle (axialRot φ (planePoint p)) = φ + 2 * Real.pi * k := by
  obtain ⟨h0, h1, -⟩ := rot_planePoint_coord φ p
  have e : ((axialRot φ (planePoint p) 0 : ℝ) : ℂ) + ((axialRot φ (planePoint p) 1 : ℝ) : ℂ) * Complex.I
      = ((p.1 : ℝ) : ℂ) * (Complex.cos φ + Complex.sin φ * Complex.I) := by
    rw [h0, h1]
    push_cast
    ring
  refine ⟨⌊(Real.pi - φ) / (2 * Real.pi)⌋, ?_⟩
  unfold pointAngle
  rw [e]
  have h := Complex.arg_mul_cos_add_sin_mul_I_sub hp φ
  linarith

theorem pointPlane_rot (φ : ℝ) {p : ℝ × ℝ} (hp : p ∈ halfPlane) :
    pointPlane (axialRot φ (planePoint p)) = p := by
  have h := cylFold_axialRot φ (planePoint p)
  rw [cylFold_planePoint hp] at h
  obtain ⟨-, -, h2⟩ := rot_planePoint_coord φ p
  ext
  · show (cylFold (axialRot φ (planePoint p))).1 = p.1
    rw [h]
  · simp only [pointPlane, h2]

open Classical in
theorem pin_field_rot {count : ℕ} (F : CellMatField count) (box : Fin count → CellCert.CellAnalysis.CellBox)
    (m : ℕ) {p : ℝ × ℝ} (hp : p ∈ halfPlane) (a b : Fin 3) (τ φ : ℝ) :
    axialRot (-φ) (F.field box m τ (axialRot φ (planePoint p)) (axialRot φ (unitVector b))) a
      = ∑ K, if p ∈ (box K).rect then ∑ ι ∈ F.labels K, (labelPhase m ι τ φ * F.planeValue box K ι a b p).re
        else 0 := by
  classical
  obtain ⟨k, hk⟩ := pointAngle_rot φ (p := p) hp.1
  rw [axialRot_neg_coord, axialRot_unitVector]
  unfold CellMatField.field
  rw [_root_.sum_apply, sum_inner]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hmem : axialRot φ (planePoint p) ∈ (box K).solid ↔ p ∈ (box K).rect := by
    rw [mem_solid_iff, cylFold_axialRot, cylFold_planePoint hp]
  by_cases hK : p ∈ (box K).rect
  · rw [if_pos hK, Set.indicator_of_mem (hmem.2 hK)]
    beta_reduce
    rw [hk, pointPlane_rot φ hp, frameMap_sum, frameMap_add_int, inner_frameMap_frame]
    simp only [labelPhase_add_int]
  · rw [if_neg hK, Set.indicator_of_notMem (fun h => hK (hmem.1 h))]
    simp

def planeWave (k : ℤ × ℤ) (τ φ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * k.1 * τ + k.2 * φ : ℝ) : ℂ) * Complex.I)

def waveMean (k : ℤ × ℤ) (τ : ℝ) : ℂ :=
  (if k.2 = 0 then (2 * Real.pi : ℂ) else 0) * Complex.exp (((2 * Real.pi * k.1 * τ : ℝ) : ℂ) * Complex.I)

theorem planeWave_mul (a b : ℤ × ℤ) (τ φ : ℝ) : planeWave a τ φ * planeWave b τ φ = planeWave (a + b) τ φ := by
  unfold planeWave
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem planeWave_conj (k : ℤ × ℤ) (τ φ : ℝ) : starRingEnd ℂ (planeWave k τ φ) = planeWave (-k) τ φ := by
  unfold planeWave
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring

theorem expFactor_planeWave (ξ : ℤ × ℤ) (τ φ : ℝ) :
    Coercive.Internal.ModeRotation.expFactor ξ τ φ = planeWave (-ξ) τ φ := by
  unfold Coercive.Internal.ModeRotation.expFactor planeWave
  congr 1
  simp only [Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring

theorem labelPhase_planeWave (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) :
    labelPhase m ι σ θ = planeWave (labelHarmonic m ι) σ θ := rfl

theorem labelHarmonic_neg (m : ℕ) (ι : ℤ × ℤ) : labelHarmonic m (-ι) = -labelHarmonic m ι := by
  unfold labelHarmonic labelTime labelAzimuth
  ext
  · simp only [Prod.snd_neg, Prod.fst_neg, Prod.neg_mk]
    ring
  · simp only [Prod.fst_neg, Prod.neg_mk]
    ring

theorem continuous_planeWave_snd (k : ℤ × ℤ) (τ : ℝ) : Continuous (fun φ => planeWave k τ φ) := by
  unfold planeWave
  fun_prop

theorem continuous_waveMean (k : ℤ × ℤ) : Continuous (waveMean k) := by
  unfold waveMean
  fun_prop

theorem planeWave_integral (k : ℤ × ℤ) (c : ℂ) (τ : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), c * planeWave k τ φ = c * waveMean k τ := by
  have e : ∀ φ : ℝ, c * planeWave k τ φ
      = (c * Complex.exp (((2 * Real.pi * k.1 * τ : ℝ) : ℂ) * Complex.I))
        * Complex.exp (((k.2 * φ : ℝ) : ℂ) * Complex.I) := by
    intro φ
    unfold planeWave
    rw [mul_assoc c, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, Coercive.Internal.SmoothPressure.integral_exp_circle]
  unfold waveMean
  ring

theorem waveMean_integral {k : ℤ × ℤ} (hk : k ≠ 0) (c : ℂ) : ∫ τ in (0 : ℝ)..1, c * waveMean k τ = 0 := by
  unfold waveMean
  by_cases h2 : k.2 = 0
  · have h1 : k.1 ≠ 0 := fun h1 => hk (Prod.ext h1 h2)
    simp only [h2, if_true]
    simp_rw [← mul_assoc]
    rw [intervalIntegral.integral_const_mul, Coercive.Internal.SmoothPressure.integral_exp_period, if_neg h1,
      mul_zero]
  · simp [h2]

theorem modeSum_zero {α : Type*} (T : Finset α) (n : α → ℤ × ℤ) (V : α → ℂ) (ξ : ℤ × ℤ)
    (hn : ∀ x ∈ T, n x ≠ ξ ∧ -n x ≠ ξ) :
    ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), Coercive.Internal.ModeRotation.expFactor ξ τ φ
      * ((∑ x ∈ T, (planeWave (n x) τ φ * V x).re : ℝ) : ℂ) = 0 := by
  have hpt : ∀ τ φ, Coercive.Internal.ModeRotation.expFactor ξ τ φ
        * ((∑ x ∈ T, (planeWave (n x) τ φ * V x).re : ℝ) : ℂ)
      = ∑ x ∈ T, (V x / 2 * planeWave (-ξ + n x) τ φ
        + starRingEnd ℂ (V x) / 2 * planeWave (-ξ + -n x) τ φ) := by
    intro τ φ
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.re_eq_add_conj, map_mul, planeWave_conj, expFactor_planeWave, ← planeWave_mul, ← planeWave_mul]
    ring
  have hin : ∀ τ, ∫ φ in (0 : ℝ)..(2 * Real.pi), Coercive.Internal.ModeRotation.expFactor ξ τ φ
        * ((∑ x ∈ T, (planeWave (n x) τ φ * V x).re : ℝ) : ℂ)
      = ∑ x ∈ T, (V x / 2 * waveMean (-ξ + n x) τ + starRingEnd ℂ (V x) / 2 * waveMean (-ξ + -n x) τ) := by
    intro τ
    simp_rw [hpt τ]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [intervalIntegral.integral_add, planeWave_integral, planeWave_integral]
      · exact (continuous_const.mul (continuous_planeWave_snd _ τ)).intervalIntegrable _ _
      · exact (continuous_const.mul (continuous_planeWave_snd _ τ)).intervalIntegrable _ _
    · intro x _
      exact ((continuous_const.mul (continuous_planeWave_snd _ τ)).add
        (continuous_const.mul (continuous_planeWave_snd _ τ))).intervalIntegrable _ _
  simp_rw [hin]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨h1, h2⟩ := hn x hx
    have k1 : -ξ + n x ≠ 0 := fun h => h1 (by rw [neg_add_eq_zero] at h; exact h.symm)
    have k2 : -ξ + -n x ≠ 0 := fun h => h2 (by rw [neg_add_eq_zero] at h; exact h.symm)
    rw [intervalIntegral.integral_add, waveMean_integral k1, waveMean_integral k2, add_zero]
    · exact (continuous_const.mul (continuous_waveMean _)).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_waveMean _)).intervalIntegrable _ _
  · intro x _
    exact ((continuous_const.mul (continuous_waveMean _)).add
      (continuous_const.mul (continuous_waveMean _))).intervalIntegrable _ _

theorem pin_modes {count : ℕ} (F : CellMatField count) (box : Fin count → CellCert.CellAnalysis.CellBox)
    (m : ℕ) (L : Finset (ℤ × ℤ)) (hL : ∀ K, ∀ ι ∈ F.labels K, ι ∈ L ∧ -ι ∈ L) (ξ : ℤ × ℤ)
    (hξ : ∀ ι ∈ L, labelHarmonic m ι ≠ ξ) {p : ℝ × ℝ} (hp : p ∈ halfPlane) :
    modeGrad ξ (F.field box m) 0 (planePoint p) = 0 := by
  classical
  funext ab
  obtain ⟨a, b⟩ := ab
  simp only [modeGrad, Coercive.Internal.ModeRotation.modeAverage_eq, zero_add, Pi.zero_apply]
  have hT : ∀ τ φ, axialRot (-φ) (F.field box m τ (axialRot φ (planePoint p)) (axialRot φ (unitVector b))) a
      = ∑ x ∈ (Finset.univ.filter fun K => p ∈ (box K).rect).sigma F.labels,
          (planeWave (labelHarmonic m x.2) τ φ * F.planeValue box x.1 x.2 a b p).re := by
    intro τ φ
    rw [pin_field_rot F box m hp a b τ φ, Finset.sum_sigma, Finset.sum_filter]
    rfl
  simp_rw [hT]
  have hc : ∀ x ∈ (Finset.univ.filter fun K => p ∈ (box K).rect).sigma F.labels,
      labelHarmonic m x.2 ≠ ξ ∧ -labelHarmonic m x.2 ≠ ξ := by
    rintro ⟨K, ι⟩ hx
    obtain ⟨-, hι⟩ := Finset.mem_sigma.1 hx
    obtain ⟨h1, h2⟩ := hL K ι hι
    refine ⟨hξ ι h1, ?_⟩
    rw [← labelHarmonic_neg]
    exact hξ (-ι) h2
  have hz := modeSum_zero ((Finset.univ.filter fun K => p ∈ (box K).rect).sigma F.labels)
    (fun x => labelHarmonic m x.2) (fun x => F.planeValue box x.1 x.2 a b p) ξ hc
  beta_reduce at hz
  rw [hz, mul_zero]

theorem plane_two_null : volume {y : Space | y 2 = 0} = 0 := by
  let S : Submodule ℝ Space := LinearMap.ker (innerₛₗ ℝ (unitVector 2))
  have e : {y : Space | y 2 = 0} = (S : Set Space) := by
    ext y
    simp [S, unitVector, PiLp.inner_apply]
  rw [e]
  refine Measure.addHaar_submodule _ _ fun hS => ?_
  have h : unitVector 2 ∈ S := by
    rw [hS]
    trivial
  simp [S, unitVector] at h

theorem ae_height_ne_zero : ∀ᵐ z : ℝ × Space, z.2 2 ≠ 0 := by
  have e : {z : ℝ × Space | z.2 2 = 0} = Set.univ ×ˢ {y : Space | y 2 = 0} := by
    ext z
    simp
  have h : volume {z : ℝ × Space | z.2 2 = 0} = 0 := by
    rw [e, Measure.volume_eq_prod, Measure.prod_prod, plane_two_null, mul_zero]
  exact measure_eq_zero_iff_ae_notMem.1 h

theorem pin_input (hreg : CellMatFieldRegular) {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (S : Fin k → Finset (ℤ × ℤ))
    (hpin : IsPinInstance D) (hrec : IsPairEntry D R S) (i : Fin k) :
    PairInput D.azimuthOrder R.pairLabels (fun K => (D.mesh.box K).rect) (D.cert.pin i) := by
  have hpf : D.cert.pin i = (D.pinValues i).field D.mesh.box D.azimuthOrder := by
    rw [hpin.pin_eq]
    rfl
  obtain ⟨hm, hper, -, hfin⟩ := hreg D.mesh (D.pinValues i) D.azimuthOrder hpin.mesh_valid
  rw [hpf]
  refine ⟨hm, hper, hfin, ?_, ?_, ?_⟩
  · filter_upwards [ae_height_ne_zero] with z hz u
    exact pin_field_flip _ _ (fun K ι h => ((hpin.closed i).1 K ι h).2) _ _ _ hz u
  · intro ξ hξ
    exact Filter.Eventually.of_forall fun p hp =>
      pin_modes _ _ _ R.pairLabels (fun K ι h => hrec.pin_labels i K ι h) ξ hξ hp
  · intro σ y h
    exact pin_field_support _ _ _ σ y h

end Internal

end InstancePair

end CertCell

end Breakdown
