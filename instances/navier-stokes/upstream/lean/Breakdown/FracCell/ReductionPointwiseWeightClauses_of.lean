import Breakdown.FracCell.ReductionPointwiseDefs

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open CellAnalysis

namespace WeightClausesInternal

theorem mode_eq (m : ℕ) (n : ℤ) : modeNumber m n = (n.natAbs : ℝ) * m := by
  unfold modeNumber azimuth
  rw [abs_mul, Nat.abs_cast, Nat.cast_natAbs, Int.cast_abs]

theorem mode_neg (m : ℕ) (n : ℤ) : modeNumber m (-n) = modeNumber m n := by
  rw [mode_eq, mode_eq, Int.natAbs_neg]

theorem rHi_nonneg {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {W : WeightData} (hK : IsCellBox K) (hT : IsWeightTests α c K S W) : 0 ≤ W.rHi := by
  have h1 := hK.r_order
  have hp : ((K.r₂, K.z₁) : ℝ × ℝ) ∈ K.rect := by
    simp only [CellBox.rect, Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨h1.2.le, le_rfl⟩, ⟨le_rfl, hK.z_order.2.le⟩⟩
  have h2 := hT.range_spec _ hp (ne_of_gt (lt_of_le_of_lt h1.1 h1.2))
  linarith [hT.range_pos, h2.1, h2.2]

theorem strainAt_anti {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {W : WeightData} (hK : IsCellBox K) (hT : IsWeightTests α c K S W) {x y : ℝ} (hx : 1 < x)
    (hxy : x ≤ y) (b : Bool) : W.strainAt K S y b ≤ W.strainAt K S x b := by
  have hr := rHi_nonneg hK hT
  have hr2 : 0 < K.r₂ := lt_of_le_of_lt hK.r_order.1 hK.r_order.2
  obtain ⟨hmc, hwc, -⟩ := hT.consts_nonneg
  obtain ⟨-, -, hpv⟩ := hT.penalties_nonneg
  have hq : 0 ≤ W.strainQuad :=
    le_trans (div_nonneg (mul_nonneg hr hwc) hT.splitLength_pos.le) hT.strain_quad_ge
  have hA : 0 ≤ 2 * W.meanConst * W.rHi * K.r₂ := by positivity
  have hi : 0 ≤ (if b then 0 else S.penaltyVelocity) := by split_ifs <;> linarith
  have hB : 0 ≤ (W.strainQuad + W.rHi * (if b then 0 else S.penaltyVelocity)) * K.r₂ ^ 2 :=
    mul_nonneg (add_nonneg hq (mul_nonneg hr hi)) (sq_nonneg _)
  have h1 : 0 < x - 1 := by linarith
  have h2 : x - 1 ≤ y - 1 := by linarith
  have e1 : 2 * W.meanConst * W.rHi * K.r₂ / (y - 1) ≤ 2 * W.meanConst * W.rHi * K.r₂ / (x - 1) :=
    div_le_div_of_nonneg_left hA h1 h2
  have e2 : (W.strainQuad + W.rHi * (if b then 0 else S.penaltyVelocity)) * K.r₂ ^ 2 / (y - 1) ^ 2 ≤
      (W.strainQuad + W.rHi * (if b then 0 else S.penaltyVelocity)) * K.r₂ ^ 2 / (x - 1) ^ 2 :=
    div_le_div_of_nonneg_left hB (by positivity) (pow_le_pow_left₀ h1.le h2 2)
  unfold WeightData.strainAt
  linarith

theorem inner_nonneg {K : CellBox} (hK : IsCellBox K) : 0 ≤ CellBox.innerRadius K := by
  unfold CellBox.innerRadius
  split_ifs
  · norm_num
  · exact hK.r_order.1

theorem radial_mono (K : CellBox) {j j' : ℕ} (h : j ≤ j') : radialEigen K j ≤ radialEigen K j' := by
  have hj : (j : ℝ) ≤ j' := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold radialEigen
  split_ifs
  · gcongr
  · gcongr

theorem height_mono (K : CellBox) {l l' : ℕ} (h : l ≤ l') : heightEigen K l ≤ heightEigen K l' := by
  have hl : (l : ℝ) ≤ l' := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  unfold heightEigen
  gcongr

theorem tail_mono {K : CellBox} (hK : IsCellBox K) {j j' l l' : ℕ} (hj : j ≤ j') (hl : l ≤ l') :
    CellScalars.tailLam K j l ≤ CellScalars.tailLam K j' l' := by
  unfold CellScalars.tailLam
  exact mul_le_mul_of_nonneg_left (add_le_add (radial_mono K hj) (height_mono K hl)) (inner_nonneg hK)

theorem ang_nonneg {K : CellBox} (hK : IsCellBox K) (n : ℤ) : 0 ≤ CellBox.angularWeight K n := by
  have hr2 : 0 < K.r₂ := lt_of_le_of_lt hK.r_order.1 hK.r_order.2
  unfold CellBox.angularWeight
  split_ifs
  · exact le_rfl
  · positivity
  · exact inv_nonneg.mpr hr2.le

theorem ang_eq (K : CellBox) {n : ℤ} (hn : n ≠ 0) : CellBox.angularWeight K n = angularConst K := by
  unfold angularConst CellBox.angularWeight
  simp [hn]

theorem prod_le {K : CellBox} (hK : IsCellBox K) {E d x y : ℝ} (j l : ℕ) (hE : 0 ≤ E) (hxy : x ≤ y) :
    E * (CellScalars.tailLam K 0 0 + angularConst K * (max (x - d) 0) ^ 2) ≤
      E * (CellScalars.tailLam K j l + angularConst K * (max (y - d) 0) ^ 2) := by
  apply mul_le_mul_of_nonneg_left _ hE
  apply add_le_add (tail_mono hK (Nat.zero_le _) (Nat.zero_le _))
  apply mul_le_mul_of_nonneg_left _ (ang_nonneg hK 1)
  have h : max (x - d) 0 ≤ max (y - d) 0 := max_le_max (by linarith) le_rfl
  exact pow_le_pow_left₀ (le_max_right _ _) h 2

theorem res_le {K : CellBox} (hK : IsCellBox K) {E a : ℝ} (n : ℤ) (j l : ℕ) (hE : 0 ≤ E) :
    E * CellScalars.tailLam K j l ≤ E * (CellScalars.tailLam K j l + CellBox.angularWeight K n * a ^ 2) :=
  mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg (ang_nonneg hK n) (sq_nonneg _))) hE

theorem mode_ge (m : ℕ) {n : ℤ} {A : ℕ} (h : A ≤ n.natAbs) : ((A : ℕ) : ℝ) * m ≤ modeNumber m n := by
  rw [mode_eq]
  have : ((A : ℕ) : ℝ) ≤ n.natAbs := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg m)

end WeightClausesInternal

open WeightClausesInternal

theorem weightClauses_of : WeightClausesStatement := by
  intro α k N c K S W hK hW hT
  have hres : ∀ n, n ∈ S.resolved ↔ n.natAbs ≤ W.J := by
    intro n
    rw [hW.resolved_eq, Finset.mem_Icc]
    omega
  have hband : ∀ n, n ∈ S.band ↔ W.J < n.natAbs ∧ n.natAbs ≤ W.J + W.JB := by
    intro n
    rw [hW.band_eq, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc]
    push_cast
    omega
  have hresn : ∀ n, -n ∈ S.resolved ↔ n ∈ S.resolved := by
    intro n
    rw [hres, hres, Int.natAbs_neg]
  have hbandn : ∀ n, -n ∈ S.band ↔ n ∈ S.band := by
    intro n
    rw [hband, hband, Int.natAbs_neg]
  have hord : (3 : ℝ) ≤ c.order := by exact_mod_cast hT.order_ge
  have hout : ∀ n, n ∉ S.resolved → W.J + 1 ≤ n.natAbs := by
    intro n hn
    rw [hres] at hn
    omega
  have hout2 : ∀ n, n ∉ S.resolved → n ∉ S.band → W.J + W.JB + 1 ≤ n.natAbs := by
    intro n hn hb
    rw [hres] at hn
    rw [hband] at hb
    omega
  have hne : ∀ n, n ∉ S.resolved → n ≠ 0 := by
    intro n hn h0
    exact hn ((hres n).2 (by rw [h0]; exact Nat.zero_le _))
  have hk0 : (1 : ℝ) < ((W.J + 1 : ℕ) : ℝ) * c.order := by
    have : (1 : ℝ) ≤ ((W.J + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos W.J
    nlinarith
  have hk1 : (1 : ℝ) < ((W.J + W.JB + 1 : ℕ) : ℝ) * c.order := by
    have : (1 : ℝ) ≤ ((W.J + W.JB + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (W.J + W.JB)
    nlinarith
  have hkb : ∀ n, n ∈ S.band → W.kEff c.order n = modeNumber c.order n := by
    intro n hb
    unfold WeightData.kEff
    rw [if_pos (le_trans ((hband n).1 hb).2 (le_max_left _ _))]
  have hko : ∀ n, n ∉ S.resolved → n ∉ S.band →
      ((W.J + W.JB + 1 : ℕ) : ℝ) * c.order ≤ W.kEff c.order n := by
    intro n hn hb
    unfold WeightData.kEff
    split_ifs
    · exact mode_ge _ (hout2 n hn hb)
    · exact le_rfl
  have hE := hT.energy_pos
  have hV := hT.vorticity_nonneg
  have hEV : 0 < W.energy + 2 * W.vorticity := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have h1 := mode_ge c.order (hout n hn)
    have : (3 : ℝ) ≤ ((W.J + 1 : ℕ) : ℝ) * c.order := by
      have : (1 : ℝ) ≤ ((W.J + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos W.J
      nlinarith
    linarith
  · intro n
    rw [hW.energy_form]
    exact hT.energy_pos
  · intro n
    rw [hW.energy_form]
    exact hT.energy_le
  · intro n
    rw [hW.vorticity_form]
    exact hT.vorticity_nonneg
  · intro n
    rw [hW.vorticity_form]
    exact hT.vorticity_le
  · intro n
    refine ⟨by rw [hW.energy_form, hW.energy_form], by rw [hW.vorticity_form, hW.vorticity_form], ?_, ?_, ?_, ?_⟩
    · simp only [hW.curl_form, hresn, hbandn]
    · simp only [hW.strain_form, hresn, hbandn, WeightData.kEff, Int.natAbs_neg, mode_neg]
    · simp only [hW.velocity_form, hresn]
    · simp only [hW.shift_form, hresn]
  · intro n
    rw [hW.shift_form]
    split_ifs
    · exact hT.shift_nonneg
    · exact le_rfl
  · intro n hn
    rw [hW.shift_form, if_neg hn]
  · intro n j l h
    refine ⟨?_, le_of_eq (hW.sym_form n j l)⟩
    rw [hW.sym_form, hW.energy_form]
    by_cases hn : n ∈ S.resolved
    · rw [hW.strain_form, if_pos hn, hW.shift_form, if_pos hn]
      have hd : S.degHigh < max j l := h.resolve_left (not_not.mpr hn)
      have hA := res_le hK (a := max (modeNumber c.order n - 2) 0) n j l hE.le
      rcases lt_max_iff.mp hd with hj | hl
      · have ht : CellScalars.tailLam K (S.degHigh + 1) 0 ≤ CellScalars.tailLam K j l :=
          tail_mono hK hj (Nat.zero_le l)
        have := mul_le_mul_of_nonneg_left ht hE.le
        linarith [hT.sym_resolved_radial]
      · have ht : CellScalars.tailLam K 0 (S.degHigh + 1) ≤ CellScalars.tailLam K j l :=
          tail_mono hK (Nat.zero_le j) hl
        have := mul_le_mul_of_nonneg_left ht hE.le
        linarith [hT.sym_resolved_height]
    · rw [hW.strain_form, if_neg hn, hW.shift_form, if_neg hn, ang_eq K (hne n hn)]
      by_cases hb : n ∈ S.band
      · rw [decide_eq_true hb, hkb n hb]
        have hm := mode_ge c.order (hout n hn)
        have hs := strainAt_anti hK hT hk0 hm true
        have hp := prod_le hK (d := 2) j l hE.le hm
        have ht : S.weightFloor ≤ W.energy * (CellScalars.tailLam K 0 0 + angularConst K *
            (max (((W.J + 1 : ℕ) : ℝ) * c.order - 2) 0) ^ 2) - W.strainAt K S (((W.J + 1 : ℕ) : ℝ) * c.order) true :=
          hT.sym_band
        linarith
      · rw [decide_eq_false hb]
        have hm := mode_ge c.order (hout2 n hn hb)
        have hs := strainAt_anti hK hT hk1 (hko n hn hb) false
        have hp := prod_le hK (d := 2) j l hE.le hm
        have ht : S.weightFloor ≤ W.energy * (CellScalars.tailLam K 0 0 + angularConst K *
            (max (((W.J + W.JB + 1 : ℕ) : ℝ) * c.order - 2) 0) ^ 2) - W.strainAt K S (((W.J + W.JB + 1 : ℕ) : ℝ) * c.order) false :=
          hT.sym_out
        linarith
  · intro n j l h
    refine ⟨?_, le_of_eq (hW.anti_form n j l)⟩
    rw [hW.anti_form, hW.energy_form, hW.vorticity_form]
    by_cases hn : n ∈ S.resolved
    · rw [hW.strain_form, if_pos hn, hW.shift_form, if_pos hn, hW.curl_form, if_pos hn]
      have hd : S.degHigh < max j l := h.resolve_left (not_not.mpr hn)
      have hA := res_le hK (a := max (modeNumber c.order n - 1) 0) n j l hEV.le
      rcases lt_max_iff.mp hd with hj | hl
      · have ht : CellScalars.tailLam K (S.degHigh + 1) 0 ≤ CellScalars.tailLam K j l :=
          tail_mono hK hj (Nat.zero_le l)
        have := mul_le_mul_of_nonneg_left ht hEV.le
        linarith [hT.anti_resolved_radial]
      · have ht : CellScalars.tailLam K 0 (S.degHigh + 1) ≤ CellScalars.tailLam K j l :=
          tail_mono hK (Nat.zero_le j) hl
        have := mul_le_mul_of_nonneg_left ht hEV.le
        linarith [hT.anti_resolved_height]
    · rw [hW.strain_form, if_neg hn, hW.shift_form, if_neg hn, hW.curl_form, if_neg hn, ang_eq K (hne n hn)]
      by_cases hb : n ∈ S.band
      · rw [decide_eq_true hb, hkb n hb, if_pos hb]
        have hm := mode_ge c.order (hout n hn)
        have hs := strainAt_anti hK hT hk0 hm true
        have hp := prod_le hK (d := 1) j l hEV.le hm
        have ht : S.weightFloor ≤ (W.energy + 2 * W.vorticity) * (CellScalars.tailLam K 0 0 + angularConst K *
            (max (((W.J + 1 : ℕ) : ℝ) * c.order - 1) 0) ^ 2) - 2 * W.curlBand
            - W.strainAt K S (((W.J + 1 : ℕ) : ℝ) * c.order) true :=
          hT.anti_band
        linarith
      · rw [decide_eq_false hb, if_neg hb]
        have hm := mode_ge c.order (hout2 n hn hb)
        have hs := strainAt_anti hK hT hk1 (hko n hn hb) false
        have hp := prod_le hK (d := 1) j l hEV.le hm
        have ht : S.weightFloor ≤ (W.energy + 2 * W.vorticity) * (CellScalars.tailLam K 0 0 + angularConst K *
            (max (((W.J + W.JB + 1 : ℕ) : ℝ) * c.order - 1) 0) ^ 2) - 2 * W.curlOut
            - W.strainAt K S (((W.J + W.JB + 1 : ℕ) : ℝ) * c.order) false :=
          hT.anti_out
        linarith
  · intro n hn j l h
    refine ⟨?_, le_of_eq (hW.vel_form n j l)⟩
    rw [hW.vel_form, hW.shift_form, if_pos hn, hW.velocity_form, if_pos hn]
    split_ifs with hj
    · have := mul_le_mul_of_nonneg_left (radial_mono K hj) hT.shift_nonneg
      linarith [hT.vel_radial]
    · have hl : S.degHigh ≤ l := by
        rcases le_max_iff.mp h with h' | h'
        · exact absurd h' hj
        · exact h'
      have := mul_le_mul_of_nonneg_left (height_mono K hl) hT.shift_nonneg
      linarith [hT.vel_height]

end Reduction

end CellCert

end Breakdown
