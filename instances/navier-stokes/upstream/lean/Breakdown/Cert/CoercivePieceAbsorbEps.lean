import Breakdown.Cert.CoercivePieceAbsorbEdge

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceAbsorb

section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

theorem base_summable (σ : ℝ) (y : Space) (hfin : Finite C) (hg : IsGoodPoint v G H σ y) :
    Summable (fun ι => modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)) := by
  obtain ⟨h2, hc, h1, ho, h0⟩ := hg
  have bnd : ∀ f : C → ℝ, ∃ K, ∀ c, |f c| ≤ K := fun f => by
    obtain ⟨K, hK⟩ := (Set.finite_range fun c => |f c|).bddAbove
    exact ⟨K, fun c => hK ⟨c, rfl⟩⟩
  obtain ⟨K1, hK1⟩ := bnd fun c => m.convD c y - m.c
  obtain ⟨K2, hK2⟩ := bnd fun c => 1 - m.convD c y
  obtain ⟨K3, hK3⟩ := bnd fun c => 1 / 4 - m.convZ c y
  obtain ⟨K4, hK4⟩ := bnd fun c => m.convZ c y - ModeWeights.secondDerivNorm (m.convD c) y - m.c * w y
  obtain ⟨K5, hK5⟩ := bnd fun c => ModeWeights.secondDerivNorm (m.convZ c) y
  have s := ((((summable_bdd_mul (fun ι => hK1 (m.classOf ι)) h2).add (summable_bdd_mul (fun ι => hK2 (m.classOf ι)) hc)).add
    (summable_bdd_mul (fun ι => hK3 (m.classOf ι)) ho)).add (summable_bdd_mul (fun ι => hK4 (m.classOf ι)) h1)).sub
    (summable_bdd_mul (fun ι => hK5 (m.classOf ι)) h0)
  exact s

open Classical in
theorem eps_density_identity (β : Fin nE) (ι : ℤ × ℤ) (y : Space) (xc xo x1 x0 : ℝ) :
    pieceEpsDensity m P h β ι y xc xo x1 x0
        - ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * (m.epsP β).wt y
          * |PieceWeights.frameFreq P (m.epsP β).frame ι| * xo ^ 2
      = -((ModeWeights.ind (0 < (m.epsP β).wt y + PieceWeights.wtGrad (m.epsP β).wt y) * (m.epsP β).share1 y)
            * (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * xc ^ 2)
          + (((m.epsP β).wt y * (m.epsP β).speed y + PieceWeights.wtGrad (m.epsP β).wt y) ^ 2
              / (4 * (m.epsP β).share1 y) + (m.epsP β).wt y * (|(m.epsP β).frame| + 1 / 2 * h.supVort y)
              + (m.epsP β).wt y * h.supGradVort y * (m.epsP β).len y / 2
              + (m.epsP β).wt y * h.supVort y * (m.epsP β).t0 y / 2)
            * (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * xo ^ 2)
          + ((m.epsP β).wt y * h.supVort y / (2 * (m.epsP β).t0 y))
            * (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * x1 ^ 2)
          + ((m.epsP β).wt y * h.supGradVort y / (2 * (m.epsP β).len y))
            * (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * x0 ^ 2))
        - (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι)
              * ((m.epsP β).wt y ^ 2 * (m.epsP β).scale y / (4 * (m.epsP β).share2 y))
              * PieceWeights.inward h (m.epsP β).modes h.ampW ι y * xo ^ 2
            + ModeWeights.ind (0 < (m.epsP β).wt y) * ((m.epsP β).share2 y / (m.epsP β).scale y)
              * PieceWeights.outward h (m.epsP β).modes h.ampW ι y * xc ^ 2
          + (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * ((m.epsP β).wt y * (m.epsP β).t1 y / 2)
              * PieceWeights.inward h (m.epsP β).modes h.ampGradW ι y * xo ^ 2
            + (m.epsP β).wt y / (2 * (m.epsP β).t1 y) * PieceWeights.outward h (m.epsP β).modes h.ampGradW ι y
              * xo ^ 2)
          + (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * ((m.epsP β).wt y * (m.epsP β).t2 y / 2)
              * PieceWeights.inward h (m.epsP β).modes h.ampGradVort ι y * xo ^ 2
            + (m.epsP β).wt y / (2 * (m.epsP β).t2 y) * PieceWeights.outward h (m.epsP β).modes h.ampGradVort ι y
              * x0 ^ 2)
          + (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * ((m.epsP β).wt y * (m.epsP β).t3 y / 2)
              * PieceWeights.inward h (m.epsP β).modes h.ampVort ι y * xo ^ 2
            + (m.epsP β).wt y / (2 * (m.epsP β).t3 y) * PieceWeights.outward h (m.epsP β).modes h.ampVort ι y
              * x1 ^ 2)) := by
  unfold pieceEpsDensity
  ring

theorem eps_piece_le {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (β : Fin nE) (σ : ℝ) (y : Space) (hg : IsGoodPoint v G H σ y) :
    Summable (fun ι => pieceEpsDensity m P h β ι y (vortGradAmp H ι σ y) (vortAmp G ι σ y) (gradAmp G ι σ y)
        (velAmp v ι σ y) - pieceEpsPos m P G β ι σ y) ∧
      Summable (fun ι => pieceEpsRestMode m h W v G H β ι σ y) ∧
      ∑' ι, (pieceEpsDensity m P h β ι y (vortGradAmp H ι σ y) (vortAmp G ι σ y) (gradAmp G ι σ y)
          (velAmp v ι σ y) - pieceEpsPos m P G β ι σ y)
        ≤ ∑' ι, pieceEpsRestMode m h W v G H β ι σ y + pieceEpsBlock m W v G H β σ y := by
  classical
  obtain ⟨-, hxc, hx1, hxo, hx0⟩ := hg
  have ha : 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β y
  have ha' : 0 ≤ PieceWeights.wtGrad (m.epsP β).wt y := norm_nonneg _
  obtain ⟨hs1, hs2, hlen, ht0, ht1, ht2, ht3, hsc⟩ := hm.eps_free_pos β y
  have hFS : frameSpeedSup W (m.epsP β).frame y ≤ (m.epsP β).speed y :=
    ciSup_le fun p => hm.epsSpeed_ge β p.1 p.2 y
  have hvS : vortSup W y ≤ h.supVort y := ciSup_le fun p => hm.supVort_ge p.1 p.2 y
  have hvGS : vortGradSup W y ≤ h.supGradVort y := ciSup_le fun p => hm.supGradVort_ge p.1 p.2 y
  have hFS0 : 0 ≤ frameSpeedSup W (m.epsP β).frame y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvS0 : 0 ≤ vortSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvGS0 : 0 ≤ vortGradSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hV : 0 ≤ h.supVort y := hvS0.trans hvS
  have hGV : 0 ≤ h.supGradVort y := hvGS0.trans hvGS
  have hind0 : ModeWeights.ind (0 < (m.epsP β).wt y) * ((m.epsP β).wt y ^ 2 * (m.epsP β).scale y
      / (4 * (m.epsP β).share2 y) * ((m.epsP β).share2 y / (m.epsP β).scale y)) = (m.epsP β).wt y ^ 2 / 4 := by
    rcases ha.eq_or_lt with h0 | h0
    · rw [← h0]
      ring
    · simp only [ModeWeights.ind, if_pos h0, one_mul]
      field_simp
  have eq2 : ∀ t : ℝ, 0 < t → 4 * ((m.epsP β).wt y * t / 2) * ((m.epsP β).wt y / (2 * t)) = (m.epsP β).wt y ^ 2 :=
    fun t ht => by field_simp; ring
  have hE1 := edge_le h (m.epsP β).modes (fun α => velAmp W α σ y) h.ampW y (fun α _ => Real.sqrt_nonneg _)
    (fun α hα => hm.ampW_ge α hα σ y) (fun κ => vortAmp G κ σ y) (fun κ => vortGradAmp H κ σ y) hxo hxc
    (c := (m.epsP β).wt y) (A := (m.epsP β).wt y ^ 2 * (m.epsP β).scale y / (4 * (m.epsP β).share2 y))
    (Bc := ModeWeights.ind (0 < (m.epsP β).wt y) * ((m.epsP β).share2 y / (m.epsP β).scale y)) (by positivity)
    (mul_nonneg (ind_nonneg _) (by positivity)) (by nlinarith [hind0])
  have hE2 := edge_le h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) h.ampGradW y
    (fun α _ => Real.sqrt_nonneg _) (fun α hα => hm.ampGradW_ge α hα σ y) (fun κ => vortAmp G κ σ y)
    (fun κ => vortAmp G κ σ y) hxo hxo (c := (m.epsP β).wt y) (A := (m.epsP β).wt y * (m.epsP β).t1 y / 2)
    (Bc := (m.epsP β).wt y / (2 * (m.epsP β).t1 y)) (by positivity) (by positivity) (eq2 _ ht1).ge
  have hE3 := edge_le h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y) h.ampGradVort y
    (fun α _ => Real.sqrt_nonneg _) (fun α hα => hm.ampGradVort_ge α hα σ y) (fun κ => vortAmp G κ σ y)
    (fun κ => velAmp v κ σ y) hxo hx0 (c := (m.epsP β).wt y) (A := (m.epsP β).wt y * (m.epsP β).t2 y / 2)
    (Bc := (m.epsP β).wt y / (2 * (m.epsP β).t2 y)) (by positivity) (by positivity) (eq2 _ ht2).ge
  have hE4 := edge_le h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) h.ampVort y
    (fun α _ => Real.sqrt_nonneg _) (fun α hα => hm.ampVort_ge α hα σ y) (fun κ => vortAmp G κ σ y)
    (fun κ => gradAmp G κ σ y) hxo hx1 (c := (m.epsP β).wt y) (A := (m.epsP β).wt y * (m.epsP β).t3 y / 2)
    (Bc := (m.epsP β).wt y / (2 * (m.epsP β).t3 y)) (by positivity) (by positivity) (eq2 _ ht3).ge
  have hK : (m.epsP β).wt y * frameSpeedSup W (m.epsP β).frame y + PieceWeights.wtGrad (m.epsP β).wt y
      ≤ (m.epsP β).wt y * (m.epsP β).speed y + PieceWeights.wtGrad (m.epsP β).wt y := by nlinarith
  have hcond1 : ((m.epsP β).wt y * (m.epsP β).speed y + PieceWeights.wtGrad (m.epsP β).wt y) ^ 2
      ≤ 4 * (ModeWeights.ind (0 < (m.epsP β).wt y + PieceWeights.wtGrad (m.epsP β).wt y) * (m.epsP β).share1 y)
        * (((m.epsP β).wt y * (m.epsP β).speed y + PieceWeights.wtGrad (m.epsP β).wt y) ^ 2
          / (4 * (m.epsP β).share1 y)) := by
    by_cases hp : 0 < (m.epsP β).wt y + PieceWeights.wtGrad (m.epsP β).wt y
    · simp only [ModeWeights.ind, if_pos hp, one_mul]
      apply le_of_eq
      field_simp
    · have e0 : (m.epsP β).wt y = 0 := le_antisymm (by linarith [not_lt.1 hp]) ha
      have e1 : PieceWeights.wtGrad (m.epsP β).wt y = 0 := le_antisymm (by linarith [not_lt.1 hp]) ha'
      rw [e0, e1]
      simp
  have hb1 := block_le (m.epsP β).modes (fun κ => vortGradAmp H κ σ y) (fun κ => vortAmp G κ σ y) hxc hxo
    (mul_nonneg (ind_nonneg _) hs1.le) (by positivity) hcond1
  have hb3 := block_le (m.epsP β).modes (fun κ => velAmp v κ σ y) (fun κ => vortAmp G κ σ y) hx0 hxo
    (c := (m.epsP β).wt y * h.supGradVort y) (A := (m.epsP β).wt y * h.supGradVort y / (2 * (m.epsP β).len y))
    (Bc := (m.epsP β).wt y * h.supGradVort y * (m.epsP β).len y / 2) (by positivity) (by positivity)
    (le_of_eq (by field_simp; ring))
  have hb4 := block_le (m.epsP β).modes (fun κ => gradAmp G κ σ y) (fun κ => vortAmp G κ σ y) hx1 hxo
    (c := (m.epsP β).wt y * h.supVort y) (A := (m.epsP β).wt y * h.supVort y / (2 * (m.epsP β).t0 y))
    (Bc := (m.epsP β).wt y * h.supVort y * (m.epsP β).t0 y / 2) (by positivity) (by positivity)
    (le_of_eq (by field_simp; ring))
  have hsq := pieceNorm_sq (m.epsP β).modes (fun κ => vortAmp G κ σ y) hxo
  have hSc : 0 ≤ pieceNorm (m.epsP β).modes (fun κ => vortGradAmp H κ σ y) := Real.sqrt_nonneg _
  have hSo : 0 ≤ pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) := Real.sqrt_nonneg _
  have hS0 : 0 ≤ pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y) := Real.sqrt_nonneg _
  have hS1 : 0 ≤ pieceNorm (m.epsP β).modes (fun κ => gradAmp G κ σ y) := Real.sqrt_nonneg _
  have m1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hSc) hSo
  have m2 : (m.epsP β).wt y * ((1 / 2) * vortSup W y + |(m.epsP β).frame|)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) ^ 2
      ≤ (m.epsP β).wt y * (|(m.epsP β).frame| + 1 / 2 * h.supVort y)
        * ∑' κ, ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes κ) * vortAmp G κ σ y ^ 2 := by
    rw [← hsq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha) (sq_nonneg _)
  have m3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvGS ha) hS0) hSo
  have m4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvS ha) hS1) hSo
  have sIc := summable_ind_term (m.epsP β).modes (fun κ => vortGradAmp H κ σ y) hxc
  have sIo := summable_ind_term (m.epsP β).modes (fun κ => vortAmp G κ σ y) hxo
  have sI1 := summable_ind_term (m.epsP β).modes (fun κ => gradAmp G κ σ y) hx1
  have sI0 := summable_ind_term (m.epsP β).modes (fun κ => velAmp v κ σ y) hx0
  have sf1 := summable_inward_term h (m.epsP β).modes h.ampW y
    ((m.epsP β).wt y ^ 2 * (m.epsP β).scale y / (4 * (m.epsP β).share2 y)) _ hxo
  have sg1 := summable_outward_term h (m.epsP β).modes h.ampW y
    (ModeWeights.ind (0 < (m.epsP β).wt y) * ((m.epsP β).share2 y / (m.epsP β).scale y)) _ hxc
  have sf2 := summable_inward_term h (m.epsP β).modes h.ampGradW y ((m.epsP β).wt y * (m.epsP β).t1 y / 2) _ hxo
  have sg2 := summable_outward_term h (m.epsP β).modes h.ampGradW y ((m.epsP β).wt y / (2 * (m.epsP β).t1 y)) _ hxo
  have sf3 := summable_inward_term h (m.epsP β).modes h.ampGradVort y ((m.epsP β).wt y * (m.epsP β).t2 y / 2) _ hxo
  have sg3 := summable_outward_term h (m.epsP β).modes h.ampGradVort y
    ((m.epsP β).wt y / (2 * (m.epsP β).t2 y)) _ hx0
  have sf4 := summable_inward_term h (m.epsP β).modes h.ampVort y ((m.epsP β).wt y * (m.epsP β).t3 y / 2) _ hxo
  have sg4 := summable_outward_term h (m.epsP β).modes h.ampVort y ((m.epsP β).wt y / (2 * (m.epsP β).t3 y)) _ hx1
  have hD := ((((sIc.hasSum.mul_left (ModeWeights.ind (0 < (m.epsP β).wt y + PieceWeights.wtGrad (m.epsP β).wt y)
      * (m.epsP β).share1 y)).add (sIo.hasSum.mul_left (((m.epsP β).wt y * (m.epsP β).speed y
        + PieceWeights.wtGrad (m.epsP β).wt y) ^ 2 / (4 * (m.epsP β).share1 y)
        + (m.epsP β).wt y * (|(m.epsP β).frame| + 1 / 2 * h.supVort y)
        + (m.epsP β).wt y * h.supGradVort y * (m.epsP β).len y / 2
        + (m.epsP β).wt y * h.supVort y * (m.epsP β).t0 y / 2))).add
      (sI1.hasSum.mul_left ((m.epsP β).wt y * h.supVort y / (2 * (m.epsP β).t0 y)))).add
      (sI0.hasSum.mul_left ((m.epsP β).wt y * h.supGradVort y / (2 * (m.epsP β).len y)))).neg.sub
    ((((sf1.hasSum.add sg1.hasSum).add (sf2.hasSum.add sg2.hasSum)).add (sf3.hasSum.add sg3.hasSum)).add
      (sf4.hasSum.add sg4.hasSum))
  have hR := (((hE1.1.hasSum.add hE2.1.hasSum).add hE3.1.hasSum).add hE4.1.hasSum).neg
  have hDeq : ∀ ι, pieceEpsDensity m P h β ι y (vortGradAmp H ι σ y) (vortAmp G ι σ y) (gradAmp G ι σ y)
      (velAmp v ι σ y) - pieceEpsPos m P G β ι σ y = _ := fun ι => eps_density_identity m P h β ι y _ _ _ _
  have hReq : ∀ ι, pieceEpsRestMode m h W v G H β ι σ y = -((m.epsP β).wt y * vortAmp G ι σ y
      * edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp H κ σ y) ι
      + (m.epsP β).wt y * vortAmp G ι σ y
        * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp G κ σ y) ι
      + (m.epsP β).wt y * vortAmp G ι σ y
        * edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y) (fun κ => velAmp v κ σ y) ι
      + (m.epsP β).wt y * vortAmp G ι σ y
        * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp G κ σ y) ι) := by
    intro ι
    unfold pieceEpsRestMode
    ring
  refine ⟨hD.summable.congr fun ι => (hDeq ι).symm, hR.summable.congr fun ι => (hReq ι).symm, ?_⟩
  rw [tsum_congr hDeq, hD.tsum_eq, tsum_congr hReq, hR.tsum_eq]
  have hB : pieceEpsBlock m W v G H β σ y = -(((m.epsP β).wt y * frameSpeedSup W (m.epsP β).frame y
      + PieceWeights.wtGrad (m.epsP β).wt y) * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y))
    - (m.epsP β).wt y * ((1 / 2) * vortSup W y + |(m.epsP β).frame|)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) ^ 2
    - (m.epsP β).wt y * vortGradSup W y * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y)
    - (m.epsP β).wt y * vortSup W y * pieceNorm (m.epsP β).modes (fun κ => gradAmp G κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) := rfl
  rw [hB]
  linarith [hE1.2, hE2.2, hE3.2, hE4.2]

end Pieces

end Internal.PieceAbsorb

end Coercive

end Breakdown
