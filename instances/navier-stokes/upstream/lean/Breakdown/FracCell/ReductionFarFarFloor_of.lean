import Breakdown.FracCell.ReductionFarDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

namespace FarFloorInternal

private theorem radialEigen_mono {K : CellBox} {j j' : ℕ} (h : j ≤ j') : radialEigen K j ≤ radialEigen K j' := by
  have hj : (j : ℝ) ≤ j' := by exact_mod_cast h
  unfold radialEigen
  split_ifs <;> gcongr

private theorem heightEigen_mono {K : CellBox} {l l' : ℕ} (h : l ≤ l') : heightEigen K l ≤ heightEigen K l' := by
  have hl : (l : ℝ) ≤ l' := by exact_mod_cast h
  unfold heightEigen
  gcongr

private theorem radialEigen_zero (K : CellBox) : radialEigen K 0 = 0 := by
  unfold radialEigen; simp

private theorem heightEigen_zero (K : CellBox) : heightEigen K 0 = 0 := by
  unfold heightEigen; simp

private theorem innerRadius_nonneg {K : CellBox} (hK : IsCellBox K) : 0 ≤ CellBox.innerRadius K := by
  unfold CellBox.innerRadius
  split_ifs
  · norm_num
  · exact hK.r_order.1

private theorem tailLam_ge {K : CellBox} (hK : IsCellBox K) {d j l : ℕ} (h : d < max j l) :
    CellScalars.tailLam K (d + 1) 0 ≤ CellScalars.tailLam K j l ∨
      CellScalars.tailLam K 0 (d + 1) ≤ CellScalars.tailLam K j l := by
  unfold CellScalars.tailLam
  rcases lt_max_iff.1 h with hj | hl
  · left
    apply mul_le_mul_of_nonneg_left _ (innerRadius_nonneg hK)
    have h1 := radialEigen_mono (K := K) (show d + 1 ≤ j by omega)
    have h2 := heightEigen_mono (K := K) (Nat.zero_le l)
    rw [heightEigen_zero] at h2 ⊢
    linarith
  · right
    apply mul_le_mul_of_nonneg_left _ (innerRadius_nonneg hK)
    have h1 := radialEigen_mono (K := K) (Nat.zero_le j)
    have h2 := heightEigen_mono (K := K) (show d + 1 ≤ l by omega)
    rw [radialEigen_zero] at h1 ⊢
    linarith

private theorem floor_gen {K : CellBox} (hK : IsCellBox K) {d j l : ℕ} (h : d < max j l) {a A A' b x : ℝ}
    (ha : 0 ≤ a) (hA : A ≤ A')
    (h1 : x ≤ a * (CellScalars.tailLam K (d + 1) 0 + A) - b)
    (h2 : x ≤ a * (CellScalars.tailLam K 0 (d + 1) + A) - b) :
    x ≤ a * (CellScalars.tailLam K j l + A') - b := by
  rcases tailLam_ge hK h with ht | ht
  · nlinarith [mul_le_mul_of_nonneg_left (add_le_add ht hA) ha]
  · nlinarith [mul_le_mul_of_nonneg_left (add_le_add ht hA) ha]

private theorem angularWeight_nonneg {K : CellBox} (hK : IsCellBox K) (n : ℤ) : 0 ≤ CellBox.angularWeight K n := by
  have hr : 0 < K.r₂ := lt_of_le_of_lt hK.r_order.1 hK.r_order.2
  unfold CellBox.angularWeight
  split_ifs
  · norm_num
  · positivity
  · exact inv_nonneg.2 hr.le

private theorem angularWeight_ne_zero {K : CellBox} {n : ℤ} (hn : n ≠ 0) :
    CellBox.angularWeight K n = angularConst K := by
  unfold angularConst CellBox.angularWeight
  simp [hn]

private theorem strainAt_anti (W : WeightData) (K : CellBox) (S : CellScalars) {k k' : ℝ} (hk : 1 < k) (hkk : k ≤ k')
    (h1 : 0 ≤ W.meanConst * W.rHi * K.r₂) (h2 : 0 ≤ W.strainQuad * K.r₂ ^ 2) :
    W.strainAt K S k' true ≤ W.strainAt K S k true := by
  unfold WeightData.strainAt
  simp only [if_true, mul_zero, add_zero]
  have e1 : 2 * W.meanConst * W.rHi * K.r₂ = 2 * (W.meanConst * W.rHi * K.r₂) := by ring
  rw [e1]
  have hk1 : 0 < k - 1 := by linarith
  have hk2 : k - 1 ≤ k' - 1 := by linarith
  have q1 : 2 * (W.meanConst * W.rHi * K.r₂) / (k' - 1) ≤ 2 * (W.meanConst * W.rHi * K.r₂) / (k - 1) :=
    div_le_div_of_nonneg_left (by linarith) hk1 hk2
  have q2 : W.strainQuad * K.r₂ ^ 2 / (k' - 1) ^ 2 ≤ W.strainQuad * K.r₂ ^ 2 / (k - 1) ^ 2 :=
    div_le_div_of_nonneg_left h2 (by positivity) (by gcongr)
  linarith

private theorem modeNumber_eq (m : ℕ) (n : ℤ) : modeNumber m n = (n.natAbs : ℝ) * m := by
  unfold modeNumber azimuth
  rw [abs_mul, Nat.abs_cast, Nat.cast_natAbs, Int.cast_abs]

end FarFloorInternal

open FarFloorInternal

theorem farFloor_of : FarFloorStatement := by
  intro α k N c K S W F hK hF hT hdeg hFT n j l hjl
  have hr₂ : 0 < K.r₂ := lt_of_le_of_lt hK.r_order.1 hK.r_order.2
  have hrHi : 0 ≤ W.rHi := by
    have hp : (K.r₂, K.z₁) ∈ K.rect :=
      ⟨⟨hK.r_order.2.le, le_refl _⟩, ⟨le_refl _, hK.z_order.2.le⟩⟩
    have := hT.range_spec _ hp hr₂.ne'
    linarith [hT.range_pos]
  have hquad : 0 ≤ W.strainQuad := by
    have h0 : 0 ≤ W.rHi * W.waveConst / S.splitLength :=
      div_nonneg (mul_nonneg hrHi hT.consts_nonneg.2.1) hT.splitLength_pos.le
    linarith [hT.strain_quad_ge]
  have hmean : 0 ≤ W.meanConst * W.rHi * K.r₂ :=
    mul_nonneg (mul_nonneg hT.consts_nonneg.1 hrHi) hr₂.le
  have hquad2 : 0 ≤ W.strainQuad * K.r₂ ^ 2 := mul_nonneg hquad (sq_nonneg _)
  have he : 0 ≤ W.energy := hT.energy_pos.le
  have hev : 0 ≤ W.energy + 2 * W.vorticity := by linarith [hT.vorticity_nonneg]
  have hord : (3 : ℝ) ≤ c.order := by exact_mod_cast hT.order_ge
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · rw [hF.sym_form, hF.anti_form, hF.energy_form, hF.vorticity_form, hF.strain_form, hF.curl_form,
      hF.shift_form]
    rcases Finset.mem_union.1 hn with hr | hb
    · simp only [if_pos hr]
      have hA1 : (0 : ℝ) ≤ CellBox.angularWeight K n * (max (modeNumber c.order n - 2) 0) ^ 2 :=
        mul_nonneg (angularWeight_nonneg hK n) (sq_nonneg _)
      have hA2 : (0 : ℝ) ≤ CellBox.angularWeight K n * (max (modeNumber c.order n - 1) 0) ^ 2 :=
        mul_nonneg (angularWeight_nonneg hK n) (sq_nonneg _)
      constructor
      · have := floor_gen hK hjl (x := F.strainFloor) (a := W.energy) (A := 0) (b := W.resolvedStrain + W.shift) he hA1
          (by rw [add_zero]; linarith [hFT.strain_resolved_radial])
          (by rw [add_zero]; linarith [hFT.strain_resolved_height])
        linarith
      · have := floor_gen hK hjl (x := F.strainFloor) (a := W.energy + 2 * W.vorticity) (A := 0)
          (b := 2 * W.resolvedCurl + W.resolvedStrain + W.shift) hev hA2
          (by rw [add_zero]; linarith [hFT.anti_resolved_radial])
          (by rw [add_zero]; linarith [hFT.anti_resolved_height])
        linarith
    · have hb' := hb
      rw [hF.band_eq] at hb'
      have hnr : n ∉ S.resolved := by
        rw [hF.resolved_eq]; exact (Finset.mem_sdiff.1 hb').2
      have hin := (Finset.mem_sdiff.1 hb').1
      have hout := (Finset.mem_sdiff.1 hb').2
      rw [Finset.mem_Icc] at hin hout
      have habs_hi : n.natAbs ≤ W.J + W.JB := by omega
      have habs_lo : W.J + 1 ≤ n.natAbs := by omega
      have hn0 : n ≠ 0 := by omega
      have hkEff : W.kEff c.order n = modeNumber c.order n := by
        unfold WeightData.kEff
        rw [if_pos (le_trans habs_hi (le_max_left _ _))]
      have hmode : (((W.J + 1 : ℕ) : ℝ) * c.order) ≤ modeNumber c.order n := by
        rw [modeNumber_eq]
        have : ((W.J + 1 : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast habs_lo
        exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      have hk0 : (3 : ℝ) ≤ ((W.J + 1 : ℕ) : ℝ) * c.order := by
        have : (1 : ℝ) ≤ ((W.J + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos W.J
        nlinarith
      have hstr := strainAt_anti W K S (by linarith : (1 : ℝ) < ((W.J + 1 : ℕ) : ℝ) * c.order) hmode
        hmean hquad2
      have hang := angularWeight_ne_zero (K := K) hn0
      have hangc : 0 ≤ angularConst K := hang ▸ angularWeight_nonneg hK n
      simp only [if_neg hnr, if_pos hb, decide_eq_true hb, hkEff, hang, sub_zero]
      constructor
      · have hA : angularConst K * (max (((W.J + 1 : ℕ) : ℝ) * c.order - 2) 0) ^ 2 ≤
            angularConst K * (max (modeNumber c.order n - 2) 0) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hangc
          apply pow_le_pow_left₀ (le_max_right _ _)
          exact max_le_max (by linarith) (le_refl _)
        have := floor_gen hK hjl (x := F.strainFloor) (a := W.energy) (b := W.strainAt K S (((W.J + 1 : ℕ) : ℝ) * c.order) true)
          he hA hFT.strain_band_radial hFT.strain_band_height
        linarith
      · have hA : angularConst K * (max (((W.J + 1 : ℕ) : ℝ) * c.order - 1) 0) ^ 2 ≤
            angularConst K * (max (modeNumber c.order n - 1) 0) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hangc
          apply pow_le_pow_left₀ (le_max_right _ _)
          exact max_le_max (by linarith) (le_refl _)
        have := floor_gen hK hjl (x := F.strainFloor) (a := W.energy + 2 * W.vorticity)
          (b := 2 * W.curlBand + W.strainAt K S (((W.J + 1 : ℕ) : ℝ) * c.order) true)
          hev hA
          (by have := hFT.anti_band_radial; unfold WeightData.antiAt at this; simp only [if_true] at this; linarith)
          (by have := hFT.anti_band_height; unfold WeightData.antiAt at this; simp only [if_true] at this; linarith)
        linarith
  · rw [hF.vel_form, hF.shift_form, hF.velocity_form]
    simp only [if_pos hn]
    have hs := hT.shift_nonneg
    split_ifs with hj
    · have := mul_le_mul_of_nonneg_left (radialEigen_mono (K := K) hj) hs
      linarith [hFT.velocity_radial]
    · have hl : S.degNear + 1 ≤ l := by
        rcases lt_max_iff.1 hjl with h | h <;> omega
      have := mul_le_mul_of_nonneg_left (heightEigen_mono (K := K) hl) hs
      linarith [hFT.velocity_height]

end Reduction

end CellCert

end Breakdown
