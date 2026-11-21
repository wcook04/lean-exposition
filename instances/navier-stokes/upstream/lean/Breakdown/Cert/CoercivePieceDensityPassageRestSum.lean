import Breakdown.Cert.CoercivePieceDensityPassageRestEps
import Breakdown.Cert.CoercivePieceDensityPassageRestMu
import Breakdown.Cert.CoercivePieceDensityPassageRestBase
import Breakdown.Cert.CoerciveDensityPassageRest
import Breakdown.Cert.CoercivePieceDensityPassageMeasurable

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceDensityPassageRestSum

private theorem sq_sqrt_cnormSq {β : Type*} [Fintype β] (x : β → ℂ) : Real.sqrt (cnormSq x) ^ 2 = cnormSq x :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem ampSq_eq (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    secondDerivAmp H ι σ y ^ 2 + vortGradAmp H ι σ y ^ 2 + gradAmp G ι σ y ^ 2 + vortAmp G ι σ y ^ 2
      + (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 = DensityPassageRest.ampSq v G H ι σ y := by
  simp only [secondDerivAmp, vortGradAmp, gradAmp, vortAmp, velAmp, DensityPassageRest.ampSq, div_pow, sq_sqrt_cnormSq]

private theorem families_le (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    ∑' ι, ENNReal.ofReal (vortAmp G ι σ y ^ 2) ≤ DensityPassageRest.ampTot v G H σ y ∧
    ∑' ι, ENNReal.ofReal (vortGradAmp H ι σ y ^ 2) ≤ DensityPassageRest.ampTot v G H σ y ∧
    ∑' ι, ENNReal.ofReal (gradAmp G ι σ y ^ 2) ≤ DensityPassageRest.ampTot v G H σ y ∧
    ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2) ≤ DensityPassageRest.ampTot v G H σ y := by
  have e := ampSq_eq v G H
  have p : ∀ ι, 0 ≤ secondDerivAmp H ι σ y ^ 2 ∧ 0 ≤ vortGradAmp H ι σ y ^ 2 ∧ 0 ≤ gradAmp G ι σ y ^ 2
      ∧ 0 ≤ vortAmp G ι σ y ^ 2 ∧ 0 ≤ (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 := fun ι =>
    ⟨sq_nonneg _, sq_nonneg _, sq_nonneg _, sq_nonneg _, sq_nonneg _⟩
  unfold DensityPassageRest.ampTot
  refine ⟨ENNReal.tsum_le_tsum fun ι => ENNReal.ofReal_le_ofReal ?_,
    ENNReal.tsum_le_tsum fun ι => ENNReal.ofReal_le_ofReal ?_,
    ENNReal.tsum_le_tsum fun ι => ENNReal.ofReal_le_ofReal ?_,
    ENNReal.tsum_le_tsum fun ι => ENNReal.ofReal_le_ofReal ?_⟩ <;>
  · rw [← e ι σ y]
    obtain ⟨a, b, c, d, f⟩ := p ι
    linarith

private theorem ofReal_abs_split {n k : ℕ} (a : ℝ) (e : Fin n → ℝ) (mm c d : Fin k → ℝ) (he : ∀ β, e β ≤ 0)
    (hmm : ∀ β, mm β = -(c β) - d β) (hc : ∀ β, 0 ≤ c β) (hd : ∀ β, 0 ≤ d β) :
    ENNReal.ofReal |a + ∑ β, e β + ∑ β, mm β| ≤
      ENNReal.ofReal |a| + ∑ β, ENNReal.ofReal (-e β) + ∑ β, (ENNReal.ofReal (c β) + ENNReal.ofReal (d β)) := by
  have h1 : |∑ β, e β| ≤ ∑ β, -e β := by
    rw [abs_of_nonpos (Finset.sum_nonpos fun β _ => he β), Finset.sum_neg_distrib]
  have h2 : |∑ β, mm β| ≤ ∑ β, (c β + d β) := by
    have hs : ∑ β, mm β = -∑ β, (c β + d β) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by rw [hmm β]; ring
    rw [hs, abs_neg, abs_of_nonneg (Finset.sum_nonneg fun β _ => add_nonneg (hc β) (hd β))]
  have h3 : |a + ∑ β, e β + ∑ β, mm β| ≤ |a| + ∑ β, -e β + ∑ β, (c β + d β) := by
    have := abs_add_le (a + ∑ β, e β) (∑ β, mm β)
    have := abs_add_le a (∑ β, e β)
    linarith
  have n1 : 0 ≤ ∑ β, -e β := Finset.sum_nonneg fun β _ => neg_nonneg.2 (he β)
  have n2 : 0 ≤ ∑ β, (c β + d β) := Finset.sum_nonneg fun β _ => add_nonneg (hc β) (hd β)
  calc ENNReal.ofReal |a + ∑ β, e β + ∑ β, mm β|
      ≤ ENNReal.ofReal (|a| + ∑ β, -e β + ∑ β, (c β + d β)) := ENNReal.ofReal_le_ofReal h3
    _ = _ := by
      rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) n1) n2, ENNReal.ofReal_add (abs_nonneg _) n1,
        ENNReal.ofReal_sum_of_nonneg (fun β _ => neg_nonneg.2 (he β)),
        ENNReal.ofReal_sum_of_nonneg (fun β _ => add_nonneg (hc β) (hd β))]
      congr 1
      exact Finset.sum_congr rfl fun β _ => ENNReal.ofReal_add (hc β) (hd β)

theorem rest_tsum_le {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space),
      ∑' ι : ℤ × ℤ, ENNReal.ofReal |pieceRest m h w W v G H ι σ y| ≤ K * DensityPassageRest.ampTot v G H σ y := by
  obtain ⟨D, hD⟩ := hWdecay
  obtain ⟨Kb, hKb0, hKb⟩ := PieceDensityPassageRestBase.base_pointwise m P h w W hm hwb
  choose Bm Bgm hBm using fun β => SmoothPieceMuNeg.weight_facts m P h w W hm β
  have hwtB : ∀ β y, (m.epsP β).wt y ≤ epsSup := fun β y =>
    (Finset.single_le_sum (fun b _ => hm.eps_wt_nonneg b y) (Finset.mem_univ β)).trans (hm.eps_sum_le y)
  set card : ℝ≥0∞ := (h.harmonics.card : ℝ≥0∞) with hcard
  set ce : ℝ≥0∞ := ENNReal.ofReal (epsSup * (729 * D)) * (12 * card) with hce
  set cz : Fin nM → ℝ≥0∞ := fun β => ENNReal.ofReal (Bm β * (3 * D)) * (3 * card) with hcz
  set cp : Fin nM → ℝ≥0∞ := fun β =>
    ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * (m.muP β).eta)) * card
      + ENNReal.ofReal ((1 / 2) * (m.muP β).eta * (4 * Bm β) ^ 2) with hcp
  refine ⟨ENNReal.ofReal Kb + ∑ _β : Fin nE, ce + ∑ β, (cz β + cp β), ?_, ?_⟩
  · simp only [hce, hcz, hcp, hcard]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))⟩,
      ENNReal.sum_ne_top.2 fun _ _ => ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)),
        ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _),
          ENNReal.ofReal_ne_top⟩⟩⟩
  intro v G H σ y
  obtain ⟨fv, fvg, fg, fl⟩ := families_le v G H σ y
  set A := DensityPassageRest.ampTot v G H σ y with hA
  have hpt : ∀ ι, ENNReal.ofReal |pieceRest m h w W v G H ι σ y| ≤
      ENNReal.ofReal |modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)|
        + ∑ β, ENNReal.ofReal (-pieceEpsRestMode m h W v G H β ι σ y)
        + ∑ β, (ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
            * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι)
          + ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2
                / (2 * (m.muP β).eta)
              + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) := by
    intro ι
    unfold pieceRest
    refine ofReal_abs_split _ _ _ _ _ (fun β => ?_) (fun β => ?_) (fun β => ?_) (fun β => ?_)
    · unfold pieceEpsRestMode
      refine neg_nonpos.2 (mul_nonneg (mul_nonneg (hm.eps_wt_nonneg β y) (Real.sqrt_nonneg _)) ?_)
      have hX : ∀ (X : ℤ × ℤ → ℝ), (∀ α, 0 ≤ X α) → ∀ (g : ℤ × ℤ → ℝ), (∀ κ, 0 ≤ g κ) →
          0 ≤ edgeSum h (m.epsP β).modes X g ι := fun X hX g hg =>
        SmoothPieceMuNeg.edgeSum_nonneg_of h _ X g hX hg ι
      exact add_nonneg (add_nonneg (add_nonneg (hX _ (fun _ => Real.sqrt_nonneg _) _ (fun _ => Real.sqrt_nonneg _))
        (hX _ (fun _ => Real.sqrt_nonneg _) _ (fun _ => Real.sqrt_nonneg _)))
        (hX _ (fun _ => Real.sqrt_nonneg _) _ (fun _ => Real.sqrt_nonneg _)))
        (hX _ (fun _ => Real.sqrt_nonneg _) _ (fun _ => Real.sqrt_nonneg _))
    · unfold pieceMuRestMode
      ring
    · exact mul_nonneg (mul_nonneg (hm.mu_wt_nonneg β y) (Real.sqrt_nonneg _))
        (SmoothPieceMuNeg.edgeSum_nonneg_of h _ _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) ι)
    · exact mul_nonneg (SmoothPieceMuNeg.ind_nonneg_of _) (add_nonneg
        (div_nonneg (sq_nonneg _) (by linarith [hm.mu_eta_pos β]))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hm.mu_eta_pos β).le) (sq_nonneg _)) (sq_nonneg _)))
  have hbase : ∑' ι, ENNReal.ofReal |modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)|
      ≤ ENNReal.ofReal Kb * A := by
    rw [hA, DensityPassageRest.ampTot, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ι => ?_
    rw [← ENNReal.ofReal_mul hKb0, ← ampSq_eq]
    exact ENNReal.ofReal_le_ofReal (hKb v G H ι σ y)
  have heps : ∀ β, ∑' ι, ENNReal.ofReal (-pieceEpsRestMode m h W v G H β ι σ y) ≤ ce * A := by
    intro β
    calc _ ≤ _ := PieceDensityPassageRestEps.epsRest_pointwise m h W v G H β hD (fun y => hm.eps_wt_nonneg β y)
          (fun y => hwtB β y) σ y
      _ ≤ ENNReal.ofReal (epsSup * (729 * D)) * (card * (A + 2 * A) + card * (A + 2 * A)
          + card * (A + 2 * A) + card * (A + 2 * A)) := by gcongr
      _ = ce * A := by rw [hce]; ring
  have hedge : ∀ β, ∑' ι, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
      * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι) ≤ cz β * A := by
    intro β
    obtain ⟨h0, h1, -, -⟩ := hBm β y
    calc _ ≤ _ := PieceDensityPassageRestMu.muEdge_pointwise h W v G hD (m.muP β).modes (m.muP β).wt σ y h0 h1
      _ ≤ ENNReal.ofReal (Bm β * (3 * D)) * (card * (A + 2 * A)) := by gcongr
      _ = cz β * A := by rw [hcz]; ring
  have hpress : ∀ β, ∑' ι, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
        + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2)) ≤ cp β * A := by
    intro β
    obtain ⟨h0, -, h4, -⟩ := hBm β y
    calc _ ≤ _ := SmoothPieceMuNeg.press_pointwise h W v hD (m.muP β).modes (m.muP β).wt (hm.mu_eta_pos β) σ y h0 h4
      _ ≤ ENNReal.ofReal ((h.harmonics.card : ℝ) * (81 * D ^ 2) / (2 * (m.muP β).eta)) * (card * A)
          + ENNReal.ofReal ((1 / 2) * (m.muP β).eta * (4 * Bm β) ^ 2) * A := by gcongr
      _ = cp β * A := by rw [hcp]; ring
  calc ∑' ι, ENNReal.ofReal |pieceRest m h w W v G H ι σ y|
      ≤ ∑' ι, (ENNReal.ofReal |modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)|
        + ∑ β, ENNReal.ofReal (-pieceEpsRestMode m h W v G H β ι σ y)
        + ∑ β, (ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
            * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι)
          + ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2
                / (2 * (m.muP β).eta)
              + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2)))) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' ι, ENNReal.ofReal |modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)|
        + ∑ β, ∑' ι, ENNReal.ofReal (-pieceEpsRestMode m h W v G H β ι σ y)
        + ∑ β, (∑' ι, ENNReal.ofReal ((m.muP β).wt y * velAmp v ι σ y
            * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι)
          + ∑' ι, ENNReal.ofReal (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2
                / (2 * (m.muP β).eta)
              + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2))) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
        Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      congr 1
      exact Finset.sum_congr rfl fun β _ => ENNReal.tsum_add
    _ ≤ ENNReal.ofReal Kb * A + ∑ _β : Fin nE, ce * A + ∑ β, (cz β * A + cp β * A) := by
      gcongr with β _ β _
      · exact heps β
      · exact hedge β
      · exact hpress β
    _ = (ENNReal.ofReal Kb + ∑ _β : Fin nE, ce + ∑ β, (cz β + cp β)) * A := by
      rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun β _ => (add_mul _ _ _).symm

theorem block_le {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space),
      ENNReal.ofReal |pieceBlock m W v G H σ y| ≤ K * DensityPassageRest.ampTot v G H σ y := by
  obtain ⟨D, hD⟩ := hWdecay
  obtain ⟨Bd, hBd⟩ := hm.eps_decay
  choose Ke hKe using hm.eps_increment
  choose Bm Bgm hBm using fun β => SmoothPieceMuNeg.weight_facts m P h w W hm β
  have hwtB : ∀ β y, (m.epsP β).wt y ≤ epsSup := fun β y =>
    (Finset.single_le_sum (fun b _ => hm.eps_wt_nonneg b y) (Finset.mem_univ β)).trans (hm.eps_sum_le y)
  have hg : ∀ β y, PieceWeights.wtGrad (m.epsP β).wt y ≤ (Ke β : ℝ) := fun β y => by
    unfold PieceWeights.wtGrad
    exact norm_fderiv_le_of_lipschitz ℝ (hKe β)
  set ce : Fin nE → ℝ≥0∞ := fun β => ENNReal.ofReal (4 * (epsSup * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd
      + (Ke β : ℝ) + epsSup * (27 * D + |(m.epsP β).frame|) + 27 * epsSup * D)) * 4 with hce
  set cm : Fin nM → ℝ≥0∞ := fun β => ENNReal.ofReal (2 * (4 * Bm β * (D + (1 / 2 + 2 * |(m.muP β).frame|))
      + Bgm β + |(m.muP β).frame| * (4 * Bm β))) * 2 with hcm
  refine ⟨∑ β, ce β + ∑ β, cm β, ?_, ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by norm_num), ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)⟩
  intro v G H σ y
  obtain ⟨fv, fvg, fg, fl⟩ := families_le v G H σ y
  set A := DensityPassageRest.ampTot v G H σ y with hA
  have hne := fun β => SmoothPieceDensity.epsBlock_nonpos m W v G H (fun β y => hm.eps_wt_nonneg β y) β σ y
  have hnm := fun β => SmoothPieceDensity.muBlock_nonpos m W v G (fun β y => hm.mu_wt_nonneg β y) β σ y
  have hsplit : ENNReal.ofReal |pieceBlock m W v G H σ y| =
      ∑ β, ENNReal.ofReal (-pieceEpsBlock m W v G H β σ y) + ∑ β, ENNReal.ofReal (-pieceMuBlock m W v G β σ y) := by
    unfold pieceBlock
    rw [abs_of_nonpos (add_nonpos (Finset.sum_nonpos fun β _ => hne β) (Finset.sum_nonpos fun β _ => hnm β)),
      neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ENNReal.ofReal_add (Finset.sum_nonneg fun β _ => neg_nonneg.2 (hne β))
        (Finset.sum_nonneg fun β _ => neg_nonneg.2 (hnm β)),
      ENNReal.ofReal_sum_of_nonneg (fun β _ => neg_nonneg.2 (hne β)),
      ENNReal.ofReal_sum_of_nonneg (fun β _ => neg_nonneg.2 (hnm β))]
  have he : ∀ β, ENNReal.ofReal (-pieceEpsBlock m W v G H β σ y) ≤ ce β * A := by
    intro β
    calc _ ≤ _ := PieceDensityPassageRestEps.epsBlock_pointwise m W v G H β hD hW (fun y => hm.eps_wt_nonneg β y)
          (fun y => hwtB β y) (fun y => hBd β y) (fun y => hg β y) σ y
      _ ≤ ENNReal.ofReal (4 * (epsSup * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd
          + (Ke β : ℝ) + epsSup * (27 * D + |(m.epsP β).frame|) + 27 * epsSup * D)) * (A + A + A + A) := by gcongr
      _ = ce β * A := by rw [hce]; ring
  have hmu : ∀ β, ENNReal.ofReal (-pieceMuBlock m W v G β σ y) ≤ cm β * A := by
    intro β
    obtain ⟨h0, -, h4, hg1⟩ := hBm β y
    calc _ ≤ _ := PieceDensityPassageRestMu.muBlock_pointwise m W v G β hD σ y h0 h4 hg1
      _ ≤ ENNReal.ofReal (2 * (4 * Bm β * (D + (1 / 2 + 2 * |(m.muP β).frame|))
          + Bgm β + |(m.muP β).frame| * (4 * Bm β))) * (A + A) := by gcongr
      _ = cm β * A := by rw [hcm]; ring
  rw [hsplit, add_mul, Finset.sum_mul, Finset.sum_mul]
  gcongr with β _ β _
  · exact he β
  · exact hmu β

end Internal.PieceDensityPassageRestSum

end Coercive

end Breakdown
