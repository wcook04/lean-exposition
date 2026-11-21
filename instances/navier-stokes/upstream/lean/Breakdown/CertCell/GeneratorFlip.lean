import Breakdown.CertCell.TopStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal.GeneratorFlip

open CellCert.CellAnalysis (CellBox radialUnit angularUnit axialUnit)

theorem sign_mul_self (a : Fin 3) : frameSign a * frameSign a = 1 := by
  unfold frameSign
  split_ifs <;> norm_num

theorem flip_coord (y : Space) (i : Fin 3) : flipPoint y i = frameSign i * y i := by
  fin_cases i <;> simp [flipPoint, frameSign, unitVector]

theorem flip_coord_zero (y : Space) : flipPoint y 0 = y 0 := by
  rw [flip_coord]
  simp [frameSign]

theorem flip_coord_one (y : Space) : flipPoint y 1 = -y 1 := by
  rw [flip_coord]
  simp [frameSign]

theorem flip_coord_two (y : Space) : flipPoint y 2 = -y 2 := by
  rw [flip_coord]
  simp [frameSign]

def flipLinear : Space →ₗ[ℝ] Space where
  toFun := flipPoint
  map_add' x y := by
    ext i
    simp only [flip_coord, PiLp.add_apply]
    ring
  map_smul' c x := by
    ext i
    simp only [flip_coord, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem flipLinear_apply (y : Space) : flipLinear y = flipPoint y := rfl

theorem labelFlip_involutive (ι : ℤ × ℤ) : labelFlip (labelFlip ι) = ι := by
  obtain ⟨a, b⟩ := ι
  simp [labelFlip]

theorem flip_mem_solid (K : CellBox) (y : Space) : flipPoint y ∈ K.solid ↔ y ∈ K.solid := by
  have h1 : CellCert.CellAnalysis.cylRadius (flipPoint y) = CellCert.CellAnalysis.cylRadius y := by
    simp only [CellCert.CellAnalysis.cylRadius, flip_coord_zero, flip_coord_one, neg_sq]
  have h2 : |CellCert.CellAnalysis.cylHeight (flipPoint y)| = |CellCert.CellAnalysis.cylHeight y| := by
    simp only [CellCert.CellAnalysis.cylHeight, flip_coord_two, abs_neg]
  unfold CellBox.solid
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, h1, h2]

theorem pointPlane_flip (y : Space) :
    pointPlane (flipPoint y) = ((pointPlane y).1, -(pointPlane y).2) := by
  simp only [pointPlane, flip_coord_zero, flip_coord_one, flip_coord_two, neg_sq]

theorem pointAngle_flip (y : Space) :
    pointAngle (flipPoint y) = -pointAngle y ∨ pointAngle (flipPoint y) = -pointAngle y + 2 * Real.pi := by
  have e : ((flipPoint y 0 : ℝ) : ℂ) + ((flipPoint y 1 : ℝ) : ℂ) * Complex.I
      = starRingEnd ℂ (((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I) := by
    rw [flip_coord_zero, flip_coord_one]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  unfold pointAngle
  rw [e, Complex.arg_conj]
  split_ifs with h
  · right
    rw [h]
    ring
  · left
    rfl

theorem flip_frameUnit (θ : ℝ) (a : Fin 3) :
    flipPoint (frameUnit θ a) = frameSign a • frameUnit (-θ) a := by
  ext i
  rw [flip_coord, PiLp.smul_apply, smul_eq_mul]
  fin_cases a <;> fin_cases i <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, frameSign, Real.cos_neg, Real.sin_neg]

theorem frameUnit_shift (θ : ℝ) (a : Fin 3) : frameUnit (θ + 2 * Real.pi) a = frameUnit θ a := by
  simp only [frameUnit, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem labelPhase_shift (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) :
    labelPhase m ι σ (θ + 2 * Real.pi) = labelPhase m ι σ θ := by
  unfold labelPhase
  have e : ((((2 * Real.pi * (labelTime ι : ℝ) * σ + (labelAzimuth m ι : ℝ) * (θ + 2 * Real.pi)) : ℝ) : ℂ)
      * Complex.I) = (((2 * Real.pi * (labelTime ι : ℝ) * σ + (labelAzimuth m ι : ℝ) * θ : ℝ) : ℂ)
        * Complex.I) + (labelAzimuth m ι : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem labelPhase_labelFlip (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) :
    labelPhase m (labelFlip ι) σ (-θ) = labelPhase m ι σ θ := by
  unfold labelPhase labelTime labelAzimuth labelFlip
  congr 1
  push_cast
  ring

theorem planeValue_flip {count : ℕ} (F : CellVecField count) (box : Fin count → CellBox)
    (K : Fin count) (ι : ℤ × ℤ) (a : Fin 3) (r z : ℝ) (hz : z ≠ 0) :
    F.planeValue box K (labelFlip ι) a (r, -z) = (frameSign a : ℂ) * F.planeValue box K ι a (r, z) := by
  unfold CellVecField.planeValue labelValueAt
  dsimp only
  rcases lt_or_gt_of_ne hz with h | h
  · have h1 : 0 ≤ -z := by linarith
    have h2 : ¬ 0 ≤ z := by linarith
    rw [if_pos h1, if_neg h2, ← mul_assoc, ← Complex.ofReal_mul, sign_mul_self,
      Complex.ofReal_one, one_mul]
  · have h1 : ¬ 0 ≤ -z := by linarith
    have h2 : 0 ≤ z := by linarith
    rw [if_neg h1, if_pos h2, labelFlip_involutive, neg_neg]

theorem phase_planeValue_flip {count : ℕ} (F : CellVecField count) (box : Fin count → CellBox)
    (m : ℕ) (K : Fin count) (ι : ℤ × ℤ) (a : Fin 3) (σ θ r z : ℝ) (hz : z ≠ 0) :
    labelPhase m ι σ (-θ) * F.planeValue box K ι a (r, -z)
      = (frameSign a : ℂ) * (labelPhase m (labelFlip ι) σ θ * F.planeValue box K (labelFlip ι) a (r, z)) := by
  have h1 := labelPhase_labelFlip m (labelFlip ι) σ θ
  have h2 := planeValue_flip F box K (labelFlip ι) a r z hz
  rw [labelFlip_involutive] at h1 h2
  rw [h1, h2]
  ring

theorem cell_sum_flip {count : ℕ} (F : CellVecField count) (box : Fin count → CellBox) (m : ℕ)
    (hflip : ∀ K ι, ι ∈ F.labels K → labelFlip ι ∈ F.labels K) (σ θ r z : ℝ) (hz : z ≠ 0)
    (K : Fin count) :
    (∑ ι ∈ F.labels K, ∑ a : Fin 3,
      (labelPhase m ι σ (-θ) * F.planeValue box K ι a (r, -z)).re • frameUnit (-θ) a)
      = flipPoint (∑ ι ∈ F.labels K, ∑ a : Fin 3,
      (labelPhase m ι σ θ * F.planeValue box K ι a (r, z)).re • frameUnit θ a) := by
  rw [← flipLinear_apply]
  simp only [map_sum, map_smul, flipLinear_apply, flip_frameUnit, smul_smul]
  refine Finset.sum_nbij' labelFlip labelFlip (fun ι h => hflip K ι h) (fun ι h => hflip K ι h)
    (fun ι _ => labelFlip_involutive ι) (fun ι _ => labelFlip_involutive ι) ?_
  intro ι _
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [phase_planeValue_flip F box m K ι a σ θ r z hz, Complex.re_ofReal_mul, mul_comm]

end Internal.GeneratorFlip

open Internal.GeneratorFlip in
theorem cellVecField_flip_equivariant {count : ℕ} (F : CellVecField count)
    (box : Fin count → CellCert.CellAnalysis.CellBox) (m : ℕ)
    (hflip : ∀ K ι, ι ∈ F.labels K → labelFlip ι ∈ F.labels K) (σ : ℝ) (y : Space) (hy : y 2 ≠ 0) :
    F.field box m σ (flipPoint y) = flipPoint (F.field box m σ y) := by
  have hz : (pointPlane y).2 ≠ 0 := hy
  have hang : ∀ K, (∑ ι ∈ F.labels K, ∑ a : Fin 3,
      (labelPhase m ι σ (pointAngle (flipPoint y))
        * F.planeValue box K ι a (pointPlane (flipPoint y))).re • frameUnit (pointAngle (flipPoint y)) a)
      = ∑ ι ∈ F.labels K, ∑ a : Fin 3,
      (labelPhase m ι σ (-pointAngle y)
        * F.planeValue box K ι a ((pointPlane y).1, -(pointPlane y).2)).re • frameUnit (-pointAngle y) a := by
    intro K
    rw [pointPlane_flip]
    rcases pointAngle_flip y with h | h
    · rw [h]
    · rw [h]
      simp only [labelPhase_shift, frameUnit_shift]
  unfold CellVecField.field
  conv_rhs => rw [← flipLinear_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  by_cases hK : y ∈ (box K).solid
  · rw [Set.indicator_of_mem ((flip_mem_solid _ _).2 hK), Set.indicator_of_mem hK]
    beta_reduce
    rw [hang K, cell_sum_flip F box m hflip σ (pointAngle y) _ _ hz K]
    rfl
  · rw [Set.indicator_of_notMem (mt (flip_mem_solid _ _).1 hK), Set.indicator_of_notMem hK, map_zero]

end CertCell

end Breakdown
