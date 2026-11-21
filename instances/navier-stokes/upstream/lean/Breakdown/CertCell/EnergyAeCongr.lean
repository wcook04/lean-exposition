import Breakdown.CertCell.LocalFieldDefs2

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.CellAnalysis

private theorem pairOn_congr_restrict_ae (K : CellBox) {F F' : ℝ × ℝ → ℂ}
    (hF : F =ᵐ[volume.restrict K.rect] F') (m : ℝ × ℝ → ℝ) (P : ℝ × ℝ → ℂ) :
    K.pairOn m F P = K.pairOn m F' P := by
  unfold CellBox.pairOn
  refine integral_congr_ae ?_
  filter_upwards [hF] with p hp
  rw [hp]

private theorem testSupremum_congr_restrict_ae (K : CellBox) {g g' : ℝ × ℝ → ℂ}
    (hg : g =ᵐ[volume.restrict K.rect] g') (m : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ → ℂ)) :
    K.testSupremum m V g = K.testSupremum m V g' := by
  unfold CellBox.testSupremum
  simp only [pairOn_congr_restrict_ae K hg]

private theorem dite_choose_congr_of_iff {α : Type*} {p q : α → Prop} (hpq : ∀ a, p a ↔ q a)
    [Decidable (∃ a, p a)] [Decidable (∃ a, q a)] (z : α) :
    (if h : ∃ a, p a then h.choose else z) = (if h : ∃ a, q a then h.choose else z) := by
  have e : p = q := funext fun a => propext (hpq a)
  subst e
  congr

open Classical in
private theorem proj_congr_restrict_ae (K : CellBox) {F F' : ℝ × ℝ → ℂ}
    (hF : F =ᵐ[volume.restrict K.rect] F') (d d' : ℕ) :
    K.proj d d' F = K.proj d d' F' := by
  have key : ∀ P T : ℝ × ℝ → ℂ, K.pairOn K.lineWeightFn (fun p => F p - P p) T =
      K.pairOn K.lineWeightFn (fun p => F' p - P p) T := fun P T =>
    pairOn_congr_restrict_ae K (hF.mono fun p hp => by simp only [hp]) _ _
  unfold CellBox.proj
  exact dite_choose_congr_of_iff (fun P => by simp only [key]) 0

theorem energyAeCongr : EnergyAeCongrStatement := by
  intro K _ Q q F F' dF dF' hF hdF
  have hr : (fun p : ℝ × ℝ => (K.refR p.1 : ℂ) * dF p) =ᵐ[volume.restrict K.rect]
      (fun p : ℝ × ℝ => (K.refR p.1 : ℂ) * dF' p) := hdF.mono fun p hp => by simp only [hp]
  have hz : (fun p : ℝ × ℝ => (K.refZ p.2 : ℂ) * dF p) =ᵐ[volume.restrict K.rect]
      (fun p : ℝ × ℝ => (K.refZ p.2 : ℂ) * dF' p) := hdF.mono fun p hp => by simp only [hp]
  have ha : (fun p : ℝ × ℝ => F p / (p.1 : ℂ)) =ᵐ[volume.restrict K.rect]
      (fun p : ℝ × ℝ => F' p / (p.1 : ℂ)) := hF.mono fun p hp => by simp only [hp]
  refine ⟨?_, ?_, ?_⟩
  · unfold CellBox.radialEnergy
    rw [proj_congr_restrict_ae K hF, testSupremum_congr_restrict_ae K hdF,
      testSupremum_congr_restrict_ae K hr]
  · unfold CellBox.heightEnergy
    rw [proj_congr_restrict_ae K hF, testSupremum_congr_restrict_ae K hdF,
      testSupremum_congr_restrict_ae K hz]
  · unfold CellBox.angularEnergy
    rw [proj_congr_restrict_ae K hF, testSupremum_congr_restrict_ae K hF,
      testSupremum_congr_restrict_ae K ha]

end LocalField

end CertCell

end Breakdown
