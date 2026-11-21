import Breakdown.Cert.ExtendedCoerciveAbsorbStepMu

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.AbsorbStep

open Coercive Coercive.Internal.PieceAbsorb

section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

theorem eps_piece_le_weak {w₀ epsSup epsGradSup ratio : ℝ} (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (β : Fin nE) (σ : ℝ) (y : Space) (hg : IsGoodPoint v G H σ y) :
    Summable (fun ι => pieceEpsDensity m P h β ι y (vortGradAmp H ι σ y) (vortAmp G ι σ y) (gradAmp G ι σ y)
        (velAmp v ι σ y) - pieceEpsPos m P G β ι σ y) ∧
      Summable (fun ι => pieceEpsRestModeWith m h W HW v G H β ι σ y) ∧
      ∑' ι, (pieceEpsDensity m P h β ι y (vortGradAmp H ι σ y) (vortAmp G ι σ y) (gradAmp G ι σ y)
          (velAmp v ι σ y) - pieceEpsPos m P G β ι σ y)
        ≤ ∑' ι, pieceEpsRestModeWith m h W HW v G H β ι σ y + pieceEpsBlockWith m W HW v G H β σ y := by
  classical
  obtain ⟨-, hxc, hx1, hxo, hx0⟩ := hg
  have ha : 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β y
  have ha' : 0 ≤ PieceWeights.wtGrad (m.epsP β).wt y := norm_nonneg _
  obtain ⟨hs1, hs2, hlen, ht0, ht1, ht2, ht3, hsc⟩ := hm.eps_free_pos β y
  have hFS : frameSpeedSup W (m.epsP β).frame y ≤ (m.epsP β).speed y :=
    ciSup_le fun p => hm.epsSpeed_ge β p.1 p.2 y
  have hvS : vortSup W y ≤ h.supVort y := ciSup_le fun p => hm.supVort_ge p.1 p.2 y
  have hvGS : vortGradSupWith HW y ≤ h.supGradVort y := ciSup_le fun p => hm.supGradVort_ge p.1 p.2 y
  have hFS0 : 0 ≤ frameSpeedSup W (m.epsP β).frame y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvS0 : 0 ≤ vortSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvGS0 : 0 ≤ vortGradSupWith HW y := Real.iSup_nonneg fun _ => norm_nonneg _
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
  have hE3 := edge_le h (m.epsP β).modes (fun α => vortGradAmp HW α σ y) h.ampGradVort y
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
  have hReq : ∀ ι, pieceEpsRestModeWith m h W HW v G H β ι σ y = -((m.epsP β).wt y * vortAmp G ι σ y
      * edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp H κ σ y) ι
      + (m.epsP β).wt y * vortAmp G ι σ y
        * edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp G κ σ y) ι
      + (m.epsP β).wt y * vortAmp G ι σ y
        * edgeSum h (m.epsP β).modes (fun α => vortGradAmp HW α σ y) (fun κ => velAmp v κ σ y) ι
      + (m.epsP β).wt y * vortAmp G ι σ y
        * edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp G κ σ y) ι) := by
    intro ι
    unfold pieceEpsRestModeWith
    ring
  refine ⟨hD.summable.congr fun ι => (hDeq ι).symm, hR.summable.congr fun ι => (hReq ι).symm, ?_⟩
  rw [tsum_congr hDeq, hD.tsum_eq, tsum_congr hReq, hR.tsum_eq]
  have hB : pieceEpsBlockWith m W HW v G H β σ y = -(((m.epsP β).wt y * frameSpeedSup W (m.epsP β).frame y
      + PieceWeights.wtGrad (m.epsP β).wt y) * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y))
    - (m.epsP β).wt y * ((1 / 2) * vortSup W y + |(m.epsP β).frame|)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) ^ 2
    - (m.epsP β).wt y * vortGradSupWith HW y * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y)
    - (m.epsP β).wt y * vortSup W y * pieceNorm (m.epsP β).modes (fun κ => gradAmp G κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) := rfl
  rw [hB]
  linarith [hE1.2, hE2.2, hE3.2, hE4.2]



theorem pieceBlockWith_nonpos (hE : ∀ β y, 0 ≤ (m.epsP β).wt y) (hM : ∀ β y, 0 ≤ (m.muP β).wt y)
    (σ : ℝ) (y : Space) : pieceBlockWith m W HW v G H σ y ≤ 0 := by
  have hFS : ∀ a, 0 ≤ frameSpeedSup W a y := fun a => Real.iSup_nonneg fun _ => norm_nonneg _
  have hvS : 0 ≤ vortSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvGS : 0 ≤ vortGradSupWith HW y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hpn : ∀ T (g : ℤ × ℤ → ℝ), 0 ≤ pieceNorm T g := fun _ _ => Real.sqrt_nonneg _
  have hwg : ∀ f, 0 ≤ PieceWeights.wtGrad f y := fun _ => norm_nonneg _
  unfold pieceBlockWith pieceEpsBlockWith pieceMuBlock
  refine add_nonpos (Finset.sum_nonpos fun β _ => ?_) (Finset.sum_nonpos fun β _ => ?_)
  · have ha := hE β y
    have h1 := hpn (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
    have h2 := hpn (m.epsP β).modes (fun κ => vortAmp G κ σ y)
    have h3 := hpn (m.epsP β).modes (fun κ => velAmp v κ σ y)
    have h4 := hpn (m.epsP β).modes (fun κ => gradAmp G κ σ y)
    nlinarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha (hFS (m.epsP β).frame)) (hwg (m.epsP β).wt)) h1) h2,
      mul_nonneg (mul_nonneg ha (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hvS)
        (abs_nonneg (m.epsP β).frame))) (sq_nonneg (pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y))),
      mul_nonneg (mul_nonneg (mul_nonneg ha hvGS) h3) h2, mul_nonneg (mul_nonneg (mul_nonneg ha hvS) h4) h2]
  · have ha := hM β y
    have h1 := hpn (m.muP β).modes (fun κ => gradAmp G κ σ y)
    have h2 := hpn (m.muP β).modes (fun κ => velAmp v κ σ y)
    nlinarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha (hFS (m.muP β).frame)) (hwg (m.muP β).wt)) h1) h2,
      mul_nonneg (mul_nonneg ha (abs_nonneg (m.muP β).frame))
        (sq_nonneg (pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y)))]

theorem real_step_weak {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (σ : ℝ) (y : Space) (hg : IsGoodPoint v G H σ y) :
    Summable (fun ι => m.modeTerm P h w v G H ι σ y - piecePos m P v G ι σ y) ∧
      Summable (fun ι => pieceRestWith m h w W HW v G H ι σ y) ∧
      ∑' ι, (m.modeTerm P h w v G H ι σ y - piecePos m P v G ι σ y)
        ≤ ∑' ι, pieceRestWith m h w W HW v G H ι σ y + pieceBlockWith m W HW v G H σ y := by
  set bs := fun ι => modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y) with hbs
  set eD := fun (β : Fin nE) ι => pieceEpsDensity m P h β ι y (vortGradAmp H ι σ y) (vortAmp G ι σ y)
    (gradAmp G ι σ y) (velAmp v ι σ y) - pieceEpsPos m P G β ι σ y with heD
  set mD := fun (β : Fin nM) ι => pieceMuDensity m P h β ι y (gradAmp G ι σ y) (velAmp v ι σ y)
    - pieceMuPos m P v β ι σ y with hmD
  set eR := fun (β : Fin nE) ι => pieceEpsRestModeWith m h W HW v G H β ι σ y with heR
  set mR := fun (β : Fin nM) ι => pieceMuRestMode m h W v G β ι σ y with hmR
  have hsplit : ∀ ι, m.modeTerm P h w v G H ι σ y - piecePos m P v G ι σ y
      = bs ι + ∑ β, eD β ι + ∑ β, mD β ι := by
    intro ι
    simp only [hbs, heD, hmD, PieceWeights.modeTerm, piecePos, modeDensity_split, modeVals, secondDerivAmp, vortGradAmp,
      gradAmp, vortAmp, velAmp, Finset.sum_sub_distrib]
    ring
  have hrest : ∀ ι, pieceRestWith m h w W HW v G H ι σ y = bs ι + ∑ β, eR β ι + ∑ β, mR β ι := fun ι => rfl
  have hB : pieceBlockWith m W HW v G H σ y
      = ∑ β, pieceEpsBlockWith m W HW v G H β σ y + ∑ β, pieceMuBlock m W v G β σ y := rfl
  have hb := base_summable m w v G H σ y hm.finite_classes hg
  have he := fun β => eps_piece_le_weak m P h w W v G H HW hm β σ y hg
  have hmu := fun β => mu_piece_le_weak m P h w W v G H HW hm β σ y hg
  have sE : Summable fun ι => ∑ β, eD β ι := summable_sum fun β _ => (he β).1
  have sM : Summable fun ι => ∑ β, mD β ι := summable_sum fun β _ => (hmu β).1
  have sER : Summable fun ι => ∑ β, eR β ι := summable_sum fun β _ => (he β).2.1
  have sMR : Summable fun ι => ∑ β, mR β ι := summable_sum fun β _ => (hmu β).2.1
  simp only [hsplit, hrest, hB]
  refine ⟨(hb.add sE).add sM, (hb.add sER).add sMR, ?_⟩
  rw [(hb.add sE).tsum_add sM, hb.tsum_add sE, (hb.add sER).tsum_add sMR, hb.tsum_add sER,
    Summable.tsum_finsetSum fun β _ => (he β).1, Summable.tsum_finsetSum fun β _ => (hmu β).1,
    Summable.tsum_finsetSum fun β _ => (he β).2.1, Summable.tsum_finsetSum fun β _ => (hmu β).2.1]
  have i1 : ∑ β, ∑' ι, eD β ι ≤ ∑ β, (∑' ι, eR β ι + pieceEpsBlockWith m W HW v G H β σ y) :=
    Finset.sum_le_sum fun β _ => (he β).2.2
  have i2 : ∑ β, ∑' ι, mD β ι ≤ ∑ β, (∑' ι, mR β ι + pieceMuBlock m W v G β σ y) :=
    Finset.sum_le_sum fun β _ => (hmu β).2.2
  rw [Finset.sum_add_distrib] at i1 i2
  linarith

theorem pointwise_step_weak {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (σ : ℝ) (y : Space) (hg : IsGoodPoint v G H σ y) :
    (∑' ι, ENNReal.ofReal (m.modeTerm P h w v G H ι σ y))
        + ((∑' ι, ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι σ y))
          + ENNReal.ofReal (-pieceBlockWith m W HW v G H σ y))
      ≤ ((∑' ι, ENNReal.ofReal (piecePos m P v G ι σ y))
          + (∑' ι, ENNReal.ofReal (pieceRestWith m h w W HW v G H ι σ y))
          + ENNReal.ofReal (pieceBlockWith m W HW v G H σ y))
        + ∑' ι, ENNReal.ofReal (-m.modeTerm P h w v G H ι σ y) := by
  obtain ⟨he, hr, hle⟩ := real_step_weak m P h w W v G H HW hm σ y hg
  refine ennreal_of_real_sums (fun ι => ?_) he hr hle
  unfold piecePos pieceEpsPos pieceMuPos
  refine add_nonneg (Finset.sum_nonneg fun β _ => ?_) (Finset.sum_nonneg fun β _ => ?_)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (ind_nonneg _) (hm.eps_wt_nonneg β y)) (abs_nonneg _)) (sq_nonneg _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (ind_nonneg _) (sub_nonneg.2 hm.cμ_lt_one.le))
      (hm.mu_wt_nonneg β y)) (abs_nonneg _)) (sq_nonneg _)

theorem fderiv_slice_eq_of_one {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (σ : ℝ) (x : Space) :
    fderiv ℝ (W σ) x
      = (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (σ, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have h1 : HasFDerivAt (fun z : ℝ × Space => W z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) (σ, x)) (σ, x) :=
    ((hW.differentiable (by simp)) (σ, x)).hasFDerivAt
  exact (h1.comp x (hasFDerivAt_prodMk_right σ x)).fderiv

theorem continuous_fderiv_slice_of_one {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have : (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2)
      = fun z => (fderiv ℝ (fun z : ℝ × Space => W z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact fderiv_slice_eq_of_one hW z.1 z.2
  rw [this]
  exact (hW.continuous_fderiv (by simp)).clm_comp continuous_const

theorem aem_stretchFormWith {D : ℝ} (hW : IsWeakSecondDerivState W HW D)
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) :
    AEMeasurable (fun z : ℝ × Space => stretchFormWith W HW v G z.1 z.2) volume := by
  have ht : AEStronglyMeasurable (fun z : ℝ × Space =>
      (G z.1 z.2, fderiv ℝ (W z.1) z.2, HW z.1 z.2, v z.1 z.2)) volume :=
    hG.prodMk ((continuous_fderiv_slice_of_one hW.smooth).aestronglyMeasurable.prodMk
      (hW.secondDeriv_measurable.prodMk hv))
  exact (continuous_stretchOfData.comp_aestronglyMeasurable ht).aemeasurable

theorem aemeasurable_hypothesisSide_weak {Γ : Set Symmetry} {g : ℝ → Space → Space} {D : ℝ}
    {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : IsWeakSecondDerivState W HW D) (hv : IsPerturbation Γ P v G H g) :
    AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (piecePos m P v G ι z.1 z.2))
        + (∑' ι, ENNReal.ofReal (pieceRestWith m h w W HW v G H ι z.1 z.2))
        + ENNReal.ofReal (pieceBlockWith m W HW v G H z.1 z.2)
        + ENNReal.ofReal (stretchFormWith W HW v G z.1 z.2)) slabMeasure := by
  have hWc : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume :=
    hW.smooth.continuous.aestronglyMeasurable
  have hgW : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume :=
    (continuous_fderiv_slice_of_one hW.smooth).aestronglyMeasurable
  have hhW : AEStronglyMeasurable (fun z : ℝ × Space => HW z.1 z.2) volume := hW.secondDeriv_measurable
  have hwE : ∀ β, Measurable (m.epsP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.eps_increment β
    exact hK.continuous.measurable
  have hwM : ∀ β, Measurable (m.muP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.mu_increment β
    exact hK.continuous.measurable
  have hPos : ∀ ι, AEMeasurable (fun z : ℝ × Space => piecePos m P v G ι z.1 z.2) volume := by
    intro ι
    unfold piecePos pieceEpsPos pieceMuPos
    refine AEMeasurable.add (Finset.aemeasurable_fun_sum _ fun β _ => ?_)
      (Finset.aemeasurable_fun_sum _ fun β _ => ?_)
    · have h1 := hwE β
      have h2 := aem_vortAmp hv.measurable_gradient ι
      fun_prop
    · have h1 := hwM β
      have h2 := aem_velAmp hv.measurable_velocity ι
      fun_prop
  have hRest : ∀ ι, AEMeasurable (fun z : ℝ × Space => pieceRestWith m h w W HW v G H ι z.1 z.2) volume := by
    intro ι
    have a2 := aem_secondDerivAmp hv.measurable_secondDeriv ι
    have ac := aem_vortGradAmp hv.measurable_secondDeriv ι
    have a1 := aem_gradAmp hv.measurable_gradient ι
    have ao := aem_vortAmp hv.measurable_gradient ι
    have a0 := aem_velAmp hv.measurable_velocity ι
    have hD : Measurable (m.convD (m.classOf ι)) := (hm.convD_smooth _).continuous.measurable
    have hZ : Measurable (m.convZ (m.classOf ι)) := (hm.convZ_smooth _).continuous.measurable
    have hDD : Measurable (ModeWeights.secondDerivNorm (m.convD (m.classOf ι))) :=
      ((hm.convD_smooth _).continuous_iteratedFDeriv le_rfl).norm.measurable
    have hZZ : Measurable (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι))) :=
      ((hm.convZ_smooth _).continuous_iteratedFDeriv le_rfl).norm.measurable
    have hw := hm.weight_measurable
    unfold pieceRestWith modeVals baseDensity pieceEpsRestModeWith pieceMuRestMode
    refine AEMeasurable.add (AEMeasurable.add ?_ (Finset.aemeasurable_fun_sum _ fun β _ => ?_))
      (Finset.aemeasurable_fun_sum _ fun β _ => ?_)
    · fun_prop
    · have h1 := hwE β
      have e1 := aem_edgeSum h (m.epsP β).modes (X := fun z α => velAmp W α z.1 z.2)
        (g := fun z κ => vortGradAmp H κ z.1 z.2) (fun α => aem_velAmp hWc α)
        (fun κ => aem_vortGradAmp hv.measurable_secondDeriv κ) ι
      have e2 := aem_edgeSum h (m.epsP β).modes (X := fun z α => gradAmp (gradField W) α z.1 z.2)
        (g := fun z κ => vortAmp G κ z.1 z.2) (fun α => aem_gradAmp hgW α)
        (fun κ => aem_vortAmp hv.measurable_gradient κ) ι
      have e3 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortGradAmp HW α z.1 z.2)
        (g := fun z κ => velAmp v κ z.1 z.2) (fun α => aem_vortGradAmp hhW α)
        (fun κ => aem_velAmp hv.measurable_velocity κ) ι
      have e4 := aem_edgeSum h (m.epsP β).modes (X := fun z α => vortAmp (gradField W) α z.1 z.2)
        (g := fun z κ => gradAmp G κ z.1 z.2) (fun α => aem_vortAmp hgW α)
        (fun κ => aem_gradAmp hv.measurable_gradient κ) ι
      exact (((h1.comp_aemeasurable measurable_snd.aemeasurable).mul ao).mul
        (((e1.add e2).add e3).add e4)).neg
    · have h1 := hwM β
      have e1 := aem_edgeSum h (m.muP β).modes (X := fun z α => velAmp W α z.1 z.2)
        (g := fun z κ => gradAmp G κ z.1 z.2) (fun α => aem_velAmp hWc α)
        (fun κ => aem_gradAmp hv.measurable_gradient κ) ι
      have s1 : AEMeasurable (fun z : ℝ × Space =>
          ∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) volume :=
        Finset.aemeasurable_fun_sum _ fun α _ => (aem_gradAmp hgW α).mul (aem_velAmp hv.measurable_velocity _)
      have hw1 : AEMeasurable (fun z : ℝ × Space => (m.muP β).wt z.2) volume :=
        h1.comp_aemeasurable measurable_snd.aemeasurable
      have q1 : AEMeasurable (fun z : ℝ × Space =>
          (∑ α ∈ h.harmonics, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) ^ 2
              / (2 * (m.muP β).eta)
            + (1 / 2) * (m.muP β).eta * (m.muP β).wt z.2 ^ 2 * velAmp v ι z.1 z.2 ^ 2) volume :=
        ((s1.pow_const 2).div_const _).add ((aemeasurable_const.mul (hw1.pow_const 2)).mul (a0.pow_const 2))
      exact (((hw1.mul a0).mul e1).neg).sub (q1.const_mul (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)))
  have hB : ∀ z : ℝ × Space, ENNReal.ofReal (pieceBlockWith m W HW v G H z.1 z.2) = 0 := fun z =>
    ENNReal.ofReal_of_nonpos (pieceBlockWith_nonpos m W v G H HW hm.eps_wt_nonneg hm.mu_wt_nonneg z.1 z.2)
  simp only [hB, add_zero]
  rw [slabMeasure_eq]
  exact (((AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hPos ι)).add
    (AEMeasurable.tsum fun ι => ENNReal.measurable_ofReal.comp_aemeasurable (hRest ι))).add
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (aem_stretchFormWith W v G HW hW hv.measurable_velocity hv.measurable_gradient))).restrict

theorem aemeasurable_stretchNeg_weak {Γ : Set Symmetry} {g : ℝ → Space → Space} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) (hv : IsPerturbation Γ P v G H g) :
    AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-stretchFormWith W HW v G z.1 z.2)) slabMeasure := by
  rw [slabMeasure_eq]
  exact (ENNReal.measurable_ofReal.comp_aemeasurable
    (aem_stretchFormWith W v G HW hW hv.measurable_velocity hv.measurable_gradient).neg).restrict

end Pieces

end Internal.AbsorbStep

open Internal.AbsorbStep Coercive.Internal.PieceAbsorb in
theorem pieceAbsorbStepWeakHolds_of (hPar : Coercive.ModeSquareSumHolds)
    (hSecondDeriv : Coercive.PerturbationSecondDerivBoundHolds)
    (hL2 : Coercive.PerturbationLocalSquareIntegrabilityHolds) : PieceAbsorbStepWeakHolds := by
  intro C nE nM m P h w Γ W HW D w₀ epsSup epsGradSup ratio hm hW _hwb v G H g hv X hX
  obtain ⟨hN, hle⟩ := hX
  have hpt : ∀ᵐ z ∂slabMeasure,
      (∑' ι, ENNReal.ofReal (m.modeTerm P h w v G H ι z.1 z.2))
        + ((∑' ι, ENNReal.ofReal (-pieceRestWith m h w W HW v G H ι z.1 z.2))
          + ENNReal.ofReal (-pieceBlockWith m W HW v G H z.1 z.2))
      ≤ ((∑' ι, ENNReal.ofReal (Coercive.piecePos m P v G ι z.1 z.2))
          + (∑' ι, ENNReal.ofReal (pieceRestWith m h w W HW v G H ι z.1 z.2))
          + ENNReal.ofReal (pieceBlockWith m W HW v G H z.1 z.2))
        + ∑' ι, ENNReal.ofReal (-m.modeTerm P h w v G H ι z.1 z.2) := by
    filter_upwards [ae_goodPoint P v G H hPar hSecondDeriv hL2 hv] with z hz
    exact pointwise_step_weak m P h w W v G H HW hm z.1 z.2 hz
  exact transfer (aemeasurable_hypothesisSide_weak m P h w W v G H HW hm hW hv)
    (aemeasurable_stretchNeg_weak P W v G H HW hW hv) hpt hN hle

end CoerciveWeak

end Breakdown
