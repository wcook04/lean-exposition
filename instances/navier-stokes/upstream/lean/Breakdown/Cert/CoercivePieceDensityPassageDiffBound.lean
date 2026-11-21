import Breakdown.Cert.CoerciveDensityPassageRestBound
import Breakdown.Cert.CoerciveSmoothPieceDensityBase
import Breakdown.Cert.CoercivePieceDensityPassageDiffBoundBlock

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PiecePassageDiffBound

open DensityPassageRestBound

section General

variable {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}

theorem isRestBound_zero :
    IsRestBound (fun _ _ _ _ _ _ => (0 : ℝ)) v G H :=
  ⟨0, le_rfl, fun σ y => by simp, fun t ht u Gu Hu σ y => by simp⟩

theorem isRestBound_congr {R R' : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    (hR : IsRestBound R v G H) (e : ∀ v G H ι σ y, R v G H ι σ y = R' v G H ι σ y) :
    IsRestBound R' v G H := by
  have : R = R' := by
    funext a b c ι σ y
    exact e a b c ι σ y
  subst this
  exact hR

theorem isRestBound_sum {κ : Type} (s : Finset κ)
    {R : κ → (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
      (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    (hR : ∀ i ∈ s, IsRestBound (R i) v G H) :
    IsRestBound (fun v G H ι σ y => ∑ i ∈ s, R i v G H ι σ y) v G H := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isRestBound_zero
  | insert a s ha ih =>
    have hs := (hR a (Finset.mem_insert_self a s)).add (ih fun i hi => hR i (Finset.mem_insert_of_mem hi))
    refine isRestBound_congr hs fun _ _ _ _ _ _ => ?_
    rw [Finset.sum_insert ha]

def atOrigin (B : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℝ → Space → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  if ι = 0 then B v G H σ y else 0

theorem tsum_atOrigin_sub (a b : ℝ) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (|(if ι = 0 then a else 0) - (if ι = 0 then b else 0)|) =
      ENNReal.ofReal |a - b| := by
  have e : ∀ ι : ℤ × ℤ, ENNReal.ofReal (|(if ι = 0 then a else 0) - (if ι = 0 then b else 0)|) =
      if ι = 0 then ENNReal.ofReal |a - b| else 0 := fun ι => by
    by_cases h0 : ι = 0
    · simp only [if_pos h0]
    · simp only [if_neg h0, sub_zero, abs_zero, ENNReal.ofReal_zero]
  simp only [e]
  exact tsum_ite_eq 0 _

end General

section Pieces

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
  {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}

theorem base_coeff_bounds (hA : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hwB : ∃ B, ∀ y, w y ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : ℤ × ℤ) (y : Space),
      |m.convD (m.classOf ι) y - m.c| ≤ M ∧ |1 - m.convD (m.classOf ι) y| ≤ M ∧
      |1 / 4 - m.convZ (m.classOf ι) y| ≤ M ∧
      |m.convZ (m.classOf ι) y - ModeWeights.secondDerivNorm (m.convD (m.classOf ι)) y - m.c * w y| ≤ M ∧
      |ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * (1 + ‖y‖) ^ 2| ≤ M := by
  obtain ⟨BD, hBD⟩ := hA.convD_decay
  obtain ⟨BZ, hBZ⟩ := hA.convZ_decay
  obtain ⟨HD, -, hHD⟩ := SmoothPieceDensity.secondDerivNorm_convD_bound_base m P h w W hA
  obtain ⟨Bw, hBw⟩ := hwB
  refine ⟨1 + |BD| + |BZ| + |HD| + |Bw|, by positivity, fun ι y => ?_⟩
  set cl := m.classOf ι
  have hc0 := hA.c_pos
  have hc1 := hA.c_lt_one
  have hd0 := hA.convD_nonneg cl y
  have hdB : m.convD cl y ≤ |BD| := by
    have := hBD cl y 0 (by norm_num)
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_abs_self _))
  have hz : |m.convZ cl y| ≤ |BZ| := by
    have := hBZ cl y 0 (by norm_num)
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hhz : (1 + ‖y‖) ^ 2 * ModeWeights.secondDerivNorm (m.convZ cl) y ≤ |BZ| :=
    (hBZ cl y 2 le_rfl).trans (le_abs_self _)
  have hhz0 : 0 ≤ ModeWeights.secondDerivNorm (m.convZ cl) y := norm_nonneg _
  have hhd0 : 0 ≤ ModeWeights.secondDerivNorm (m.convD cl) y := norm_nonneg _
  have hhd : ModeWeights.secondDerivNorm (m.convD cl) y ≤ |HD| := (hHD cl y).trans (le_abs_self _)
  have hw0 : 0 ≤ w y := hA.weight_pos.le.trans (hA.weight_lower y)
  have hwb : w y ≤ |Bw| := (hBw y).trans (le_abs_self _)
  have hcw : 0 ≤ m.c * w y := mul_nonneg hc0.le hw0
  have hcw' : m.c * w y ≤ |Bw| := by nlinarith
  have a1 := abs_nonneg BD
  have a2 := abs_nonneg BZ
  have a3 := abs_nonneg HD
  have a4 := abs_nonneg Bw
  have hz' := abs_le.1 hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_of_nonneg (by positivity), mul_comm]; linarith

theorem base_bound (hA : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hwB : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y))
      v G H := by
  obtain ⟨M, hM0, hM⟩ := base_coeff_bounds hA hwB
  refine ⟨2 * M, by positivity, fun σ y => ?_, fun t ht u Gu Hu σ y => ?_⟩
  · unfold ampTotal
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ι => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := hM ι y
    have hy : 0 < 1 + ‖y‖ := by positivity
    have ex : ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * velAmp v ι σ y ^ 2
        = (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * (1 + ‖y‖) ^ 2) * (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 := by
      field_simp
    have hv2 : (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 = cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 := by
      rw [div_pow, velAmp, sqrt_cnormSq_sq]
    unfold modeVals baseDensity
    dsimp only
    rw [ex]
    have t1 := sq_term_abs_le (a := secondDerivAmp H ι σ y) c1
    have t2 := sq_term_abs_le (a := vortGradAmp H ι σ y) c2
    have t3 := sq_term_abs_le (a := vortAmp G ι σ y) c3
    have t4 := sq_term_abs_le (a := gradAmp G ι σ y) c4
    have t5 := sq_term_abs_le (a := velAmp v ι σ y / (1 + ‖y‖)) c5
    rw [secondDerivAmp, sqrt_cnormSq_sq] at t1
    rw [vortGradAmp, sqrt_cnormSq_sq] at t2
    rw [vortAmp, sqrt_cnormSq_sq] at t3
    rw [gradAmp, sqrt_cnormSq_sq] at t4
    rw [hv2] at t5
    rw [secondDerivAmp, vortGradAmp, vortAmp, gradAmp, sqrt_cnormSq_sq, sqrt_cnormSq_sq, sqrt_cnormSq_sq,
      sqrt_cnormSq_sq, hv2]
    have p1 := Internal.FieldModes.cnormSq_nonneg (modeSecondDeriv ι H σ y)
    have p2 := Internal.FieldModes.cnormSq_nonneg (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    have p3 := Internal.FieldModes.cnormSq_nonneg (modeGrad ι G σ y)
    have p4 := Internal.FieldModes.cnormSq_nonneg (curlOfGrad (modeGrad ι G σ y))
    have p5 : 0 ≤ cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 :=
      div_nonneg (Internal.FieldModes.cnormSq_nonneg _) (by positivity)
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) t5) |>.trans ?_
    nlinarith
  · unfold ampTotal diffTotal
    refine tsum_step fun ι => ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := hM ι y
    have hy : 0 < 1 + ‖y‖ := by positivity
    have exu : ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * velAmp u ι σ y ^ 2
        = (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * (1 + ‖y‖) ^ 2) * (velAmp u ι σ y / (1 + ‖y‖)) ^ 2 := by
      field_simp
    have exv : ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * velAmp v ι σ y ^ 2
        = (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * (1 + ‖y‖) ^ 2) * (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 := by
      field_simp
    unfold modeVals baseDensity
    dsimp only
    rw [exu, exv]
    have q0 : 0 < t := ht
    have t1 := sq_term_le (a := secondDerivAmp H ι σ y) (a' := secondDerivAmp Hu ι σ y) c1 (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (amp_sub_le _ _) q0
    have t2 := sq_term_le (a := vortGradAmp H ι σ y) (a' := vortGradAmp Hu ι σ y) c2 (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (amp_sub_le _ _) q0
    have t3 := sq_term_le (a := vortAmp G ι σ y) (a' := vortAmp Gu ι σ y) c3 (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (amp_sub_le _ _) q0
    have t4 := sq_term_le (a := gradAmp G ι σ y) (a' := gradAmp Gu ι σ y) c4 (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (amp_sub_le _ _) q0
    have t5 := sq_term_le (a := velAmp v ι σ y / (1 + ‖y‖)) (a' := velAmp u ι σ y / (1 + ‖y‖)) c5
      (div_nonneg (Real.sqrt_nonneg _) hy.le) (div_nonneg (Real.sqrt_nonneg _) hy.le) (amp_sub_div_le _ _ hy) q0
    have p1 := Internal.FieldModes.cnormSq_nonneg (modeSecondDeriv ι H σ y)
    have p2 := Internal.FieldModes.cnormSq_nonneg (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    have p3 := Internal.FieldModes.cnormSq_nonneg (modeGrad ι G σ y)
    have p4 := Internal.FieldModes.cnormSq_nonneg (curlOfGrad (modeGrad ι G σ y))
    have p5 : 0 ≤ cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 :=
      div_nonneg (Internal.FieldModes.cnormSq_nonneg _) (by positivity)
    have d1 := Internal.FieldModes.cnormSq_nonneg (modeSecondDeriv ι Hu σ y - modeSecondDeriv ι H σ y)
    have d2 := Internal.FieldModes.cnormSq_nonneg (curlGradOfSecondDeriv (modeSecondDeriv ι Hu σ y) - curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    have d3 := Internal.FieldModes.cnormSq_nonneg (modeGrad ι Gu σ y - modeGrad ι G σ y)
    have d4 := Internal.FieldModes.cnormSq_nonneg (curlOfGrad (modeGrad ι Gu σ y) - curlOfGrad (modeGrad ι G σ y))
    have d5 : 0 ≤ cnormSq (modeVel ι u σ y - modeVel ι v σ y) / (1 + ‖y‖) ^ 2 :=
      div_nonneg (Internal.FieldModes.cnormSq_nonneg _) (by positivity)
    refine ennreal_step (by positivity) (by positivity) (by linarith) (by linarith) ?_
    rw [five_split]
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) t5) |>.trans (le_of_eq ?_)
    simp only [secondDerivAmp, vortGradAmp, vortAmp, gradAmp, velAmp, div_pow, sqrt_cnormSq_sq]
    ring

theorem epsRest_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nE) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => pieceEpsRestMode m h W v G H β ι σ y) v G H :=
  PiecePassageDiffBoundEps.epsRest_bound hm hWdecay β v G H

theorem muRest_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nM) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G _ ι σ y => pieceMuRestMode m h W v G β ι σ y) v G H :=
  PiecePassageDiffBoundMu.muRest_bound hm hWdecay β v G H

theorem epsBlock_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nE) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (atOrigin fun v G H σ y => pieceEpsBlock m W v G H β σ y) v G H :=
  PiecePassageDiffBoundBlock.epsBlock_bound hm hW hWdecay β v G H

theorem muBlock_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nM) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (atOrigin fun v G _ σ y => pieceMuBlock m W v G β σ y) v G H :=
  PiecePassageDiffBoundBlock.muBlock_bound hm hWdecay β v G H

theorem rest_diff_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => pieceRest m h w W v G H ι σ y) v G H :=
  ((base_bound hm hwb v G H).add (isRestBound_sum Finset.univ fun β _ => epsRest_bound hm hW hWdecay β v G H)).add
    (isRestBound_sum Finset.univ fun β _ => muRest_bound hm hW hWdecay β v G H)

theorem block_diff_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (atOrigin fun v G H σ y => pieceBlock m W v G H σ y) v G H := by
  refine isRestBound_congr ((isRestBound_sum Finset.univ fun β _ => epsBlock_bound hm hW hWdecay β v G H).add
    (isRestBound_sum Finset.univ fun β _ => muBlock_bound hm hW hWdecay β v G H)) fun a b c ι σ y => ?_
  unfold atOrigin pieceBlock
  by_cases h0 : ι = 0
  · simp only [if_pos h0]
  · simp only [if_neg h0, Finset.sum_const_zero, add_zero]

end Pieces

end Internal.PiecePassageDiffBound

end Coercive

end Breakdown
