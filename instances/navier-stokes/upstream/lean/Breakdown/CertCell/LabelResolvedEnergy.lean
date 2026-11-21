import Breakdown.CertCell.RowProfileDefs
import Breakdown.FracCell.ResolvedEnergy

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace LabelResolvedEnergyInternal

def comboGradAt (C : Fin 3 → Fin 3 → ℂ) (m : ℕ) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (p : ℝ × ℝ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, C a b * gradAt m ι G a b p

def comboSlopeAt (C : Fin 3 → Fin 3 → ℂ) (m : ℕ) (ι : ℤ × ℤ)
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (c : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m ι H a b c p

theorem combo_bound (h1 : LabelModeFactsStatement) (K : CellBox) (hK : IsCellBox K) (m Q q : ℕ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hs : IsPeriodicSecondOrder v G H) (ι : ℤ × ℤ)
    (hn : K.IsAxis → ι.1 = 0) (C : Fin 3 → Fin 3 → ℂ) :
    K.radialEnergy Q q (comboGradAt C m ι G) (comboSlopeAt C m ι H 0)
        + K.heightEnergy Q q (comboGradAt C m ι G) (comboSlopeAt C m ι H 2)
        + K.angularEnergy Q (fun p => (p.1 : ℂ) * comboSlopeAt C m ι H 1 p)
        + (K.tailGradWeight Q (comboGradAt C m ι G) (comboSlopeAt C m ι H 0) (comboSlopeAt C m ι H 2)
          + K.angularWeight ι.1 * K.tailNormSq Q (fun p => (p.1 : ℂ) * comboSlopeAt C m ι H 1 p))
      ≤ ∫ p in K.rect, p.1 * (‖comboSlopeAt C m ι H 0 p‖ ^ 2 + ‖comboSlopeAt C m ι H 1 p‖ ^ 2
          + ‖comboSlopeAt C m ι H 2 p‖ ^ 2) := by
  obtain ⟨hFm, hFi, hT, hR, hZ⟩ := h1 K hK m v G H hs ι C
  exact resolvedComponent_of radialCross heightCross K hK Q q ι.1 hn (comboGradAt C m ι G)
    (comboSlopeAt C m ι H 0) (comboSlopeAt C m ι H 2) (comboSlopeAt C m ι H 1) hFm (hT 0).1 (hT 2).1
    (hT 1).1 hFi (hT 0).2 (hT 2).2 (hT 1).2 hR hZ

theorem combo_integrable (h1 : LabelModeFactsStatement) (K : CellBox) (hK : IsCellBox K) (m : ℕ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hs : IsPeriodicSecondOrder v G H) (ι : ℤ × ℤ)
    (C : Fin 3 → Fin 3 → ℂ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖comboSlopeAt C m ι H 0 p‖ ^ 2 + ‖comboSlopeAt C m ι H 1 p‖ ^ 2
          + ‖comboSlopeAt C m ι H 2 p‖ ^ 2)) K.rect := by
  obtain ⟨-, -, hT, -, -⟩ := h1 K hK m v G H hs ι C
  have h := (((hT 0).2.add (hT 1).2).add (hT 2).2)
  refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  simp only [Pi.add_apply, comboSlopeAt]
  ring

end LabelResolvedEnergyInternal

open LabelResolvedEnergyInternal CellCert.CellAnalysis.ResolvedEnergyInternal in
theorem labelResolvedEnergy_holds (h1 : LabelModeFactsStatement) : LabelResolvedEnergyStatement := by
  intro K hK m Q q v G H hs ι hn
  constructor
  · have hg : ∀ a b, comboGradAt (unitCoef a b) m ι G = gradAt m ι G a b := fun a b => by
      funext p; exact unit_sum a b (fun a' b' => gradAt m ι G a' b' p)
    have ht : ∀ a b c, comboSlopeAt (unitCoef a b) m ι H c = fun p => slopeAt m ι H a b c p :=
      fun a b c => by funext p; exact unit_sum a b (fun a' b' => slopeAt m ι H a' b' c p)
    have hb := fun a b => combo_bound h1 K hK m Q q v G H hs ι hn (unitCoef a b)
    simp only [hg, ht] at hb
    have hint : ∀ a b, IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖slopeAt m ι H a b 0 p‖ ^ 2
        + ‖slopeAt m ι H a b 1 p‖ ^ 2 + ‖slopeAt m ι H a b 2 p‖ ^ 2)) K.rect := fun a b => by
      have := combo_integrable h1 K hK m v G H hs ι (unitCoef a b)
      simpa only [ht] using this
    calc _ = ∑ a : Fin 3, ∑ b : Fin 3,
          (K.radialEnergy Q q (gradAt m ι G a b) (fun p => slopeAt m ι H a b 0 p)
            + K.heightEnergy Q q (gradAt m ι G a b) (fun p => slopeAt m ι H a b 2 p)
            + K.angularEnergy Q (fun p => (p.1 : ℂ) * slopeAt m ι H a b 1 p)
            + (K.tailGradWeight Q (gradAt m ι G a b) (fun p => slopeAt m ι H a b 0 p)
                (fun p => slopeAt m ι H a b 2 p)
              + K.angularWeight ι.1 * K.tailNormSq Q (fun p => (p.1 : ℂ) * slopeAt m ι H a b 1 p))) := by
          simp only [labelStrainEnergy, labelStrainTail, ← Finset.sum_add_distrib]
          rfl
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∫ p in K.rect, p.1 * (‖slopeAt m ι H a b 0 p‖ ^ 2
            + ‖slopeAt m ι H a b 1 p‖ ^ 2 + ‖slopeAt m ι H a b 2 p‖ ^ 2) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hb a b))
      _ = ∑ a : Fin 3, ∫ p in K.rect, ∑ b : Fin 3, p.1 * (‖slopeAt m ι H a b 0 p‖ ^ 2
            + ‖slopeAt m ι H a b 1 p‖ ^ 2 + ‖slopeAt m ι H a b 2 p‖ ^ 2) :=
          Finset.sum_congr rfl (fun a _ => (integral_finsetSum _ (fun b _ => hint a b)).symm)
      _ = ∫ p in K.rect, ∑ a : Fin 3, ∑ b : Fin 3, p.1 * (‖slopeAt m ι H a b 0 p‖ ^ 2
            + ‖slopeAt m ι H a b 1 p‖ ^ 2 + ‖slopeAt m ι H a b 2 p‖ ^ 2) :=
          (integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))).symm
      _ = ∫ p in K.rect, p.1 * slopeSq m ι H p := by
          congr 1
          funext p
          simp only [slopeSq, Fin.sum_univ_three]
          ring
  · have hg : ∀ i, comboGradAt (curlCoef i) m ι G = fun p => curlComp (fun a b => gradAt m ι G a b p) i :=
      fun i => by funext p; exact curl_sum i (fun a b => gradAt m ι G a b p)
    have ht : ∀ i c, comboSlopeAt (curlCoef i) m ι H c
        = fun p => curlComp (fun a b => slopeAt m ι H a b c p) i :=
      fun i c => by funext p; exact curl_sum i (fun a b => slopeAt m ι H a b c p)
    have hb := fun i => combo_bound h1 K hK m Q q v G H hs ι hn (curlCoef i)
    simp only [hg, ht] at hb
    have hint : ∀ i, IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖curlComp (fun a b => slopeAt m ι H a b 0 p) i‖ ^ 2
        + ‖curlComp (fun a b => slopeAt m ι H a b 1 p) i‖ ^ 2
        + ‖curlComp (fun a b => slopeAt m ι H a b 2 p) i‖ ^ 2)) K.rect := fun i => by
      have := combo_integrable h1 K hK m v G H hs ι (curlCoef i)
      simpa only [ht] using this
    have hang : ∀ i, (fun p : ℝ × ℝ => curlComp (fun a b => turnedSlopeAt m ι H a b p) i)
        = fun p => (p.1 : ℂ) * curlComp (fun a b => slopeAt m ι H a b 1 p) i := fun i => by
      funext p; exact curl_mul i (p.1 : ℂ) (fun a b => slopeAt m ι H a b 1 p)
    calc _ = ∑ i : Fin 3,
          (K.radialEnergy Q q (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
              (fun p => curlComp (fun a b => slopeAt m ι H a b 0 p) i)
            + K.heightEnergy Q q (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
              (fun p => curlComp (fun a b => slopeAt m ι H a b 2 p) i)
            + K.angularEnergy Q (fun p => (p.1 : ℂ) * curlComp (fun a b => slopeAt m ι H a b 1 p) i)
            + (K.tailGradWeight Q (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
                (fun p => curlComp (fun a b => slopeAt m ι H a b 0 p) i)
                (fun p => curlComp (fun a b => slopeAt m ι H a b 2 p) i)
              + K.angularWeight ι.1 * K.tailNormSq Q
                (fun p => (p.1 : ℂ) * curlComp (fun a b => slopeAt m ι H a b 1 p) i))) := by
          simp only [labelVorticityEnergy, labelVorticityTail, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hang i]
      _ ≤ ∑ i : Fin 3, ∫ p in K.rect, p.1 * (‖curlComp (fun a b => slopeAt m ι H a b 0 p) i‖ ^ 2
            + ‖curlComp (fun a b => slopeAt m ι H a b 1 p) i‖ ^ 2
            + ‖curlComp (fun a b => slopeAt m ι H a b 2 p) i‖ ^ 2) :=
          Finset.sum_le_sum (fun i _ => hb i)
      _ = ∫ p in K.rect, ∑ i : Fin 3, p.1 * (‖curlComp (fun a b => slopeAt m ι H a b 0 p) i‖ ^ 2
            + ‖curlComp (fun a b => slopeAt m ι H a b 1 p) i‖ ^ 2
            + ‖curlComp (fun a b => slopeAt m ι H a b 2 p) i‖ ^ 2) :=
          (integral_finsetSum _ (fun i _ => hint i)).symm
      _ = ∫ p in K.rect, p.1 * curlSlopeSq m ι H p := by
          congr 1
          funext p
          simp only [curlSlopeSq, Fin.sum_univ_three]
          ring

end CellCalculus

end CertCell

end Breakdown
