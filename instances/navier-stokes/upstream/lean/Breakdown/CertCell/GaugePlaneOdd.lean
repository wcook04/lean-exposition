import Breakdown.CertCell.GaugePlaneOddZero

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace PlaneOdd.Internal

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open CellCert.CellCoordinates CellCalculus LocalField PlaneFlipFacts

theorem keyHarmonic_velocity (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (lo hi : ℝ) (t : ℕ → ℕ → ℝ)
    (a : Fin 3) (d : ℕ) :
    keyHarmonic L ν v G H Pg (SkeletonKey.velocity 0 false 0 lo hi t a d)
      = heightStripMoment 0 (0 + 1) lo hi (fun _ => 1) (fun p => modeVec L.order 0 (harmonicCos ν v) p.1 p.2 a)
          (gradMode L.order 0 (harmonicCos ν G) a 2) ((keySeg false 0 lo hi t).test d)
        + Complex.I * heightStripMoment 0 (0 + 1) lo hi (fun _ => 1)
          (fun p => modeVec L.order 0 (harmonicSin ν v) p.1 p.2 a)
          (gradMode L.order 0 (harmonicSin ν G) a 2) ((keySeg false 0 lo hi t).test d) := rfl

theorem keyHarmonic_gradient (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (lo hi : ℝ) (t : ℕ → ℕ → ℝ)
    (a : Fin 3) (d : ℕ) :
    keyHarmonic L ν v G H Pg (SkeletonKey.gradient 0 false 0 lo hi t a d)
      = heightStripMoment 0 (0 + 1) lo hi (fun r => r) (gradMode L.order 0 (harmonicCos ν G) a 2)
          (modeThird L.order 0 (harmonicCos ν H) a 2 2) ((keySeg false 0 lo hi t).test d)
        + Complex.I * heightStripMoment 0 (0 + 1) lo hi (fun r => r) (gradMode L.order 0 (harmonicSin ν G) a 2)
          (modeThird L.order 0 (harmonicSin ν H) a 2 2) ((keySeg false 0 lo hi t).test d) := rfl

theorem keyHarmonic_corner (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (r : ℝ) (a : Fin 3) :
    keyHarmonic L ν v G H Pg (SkeletonKey.corner 0 (r, 0) a)
      = cornerMoment r (r + 1) 0 (0 + 1) (fun p => modeVec L.order 0 (harmonicCos ν v) p.1 p.2 a)
          (gradMode L.order 0 (harmonicCos ν G) a 0) (gradMode L.order 0 (harmonicCos ν G) a 2)
          (modeThird L.order 0 (harmonicCos ν H) a 0 2)
        + Complex.I * cornerMoment r (r + 1) 0 (0 + 1) (fun p => modeVec L.order 0 (harmonicSin ν v) p.1 p.2 a)
          (gradMode L.order 0 (harmonicSin ν G) a 0) (gradMode L.order 0 (harmonicSin ν G) a 2)
          (modeThird L.order 0 (harmonicSin ν H) a 0 2) := rfl

theorem keyHarmonic_stream (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (r : ℝ) :
    keyHarmonic L ν v G H Pg (SkeletonKey.stream (r, 0))
      = heightStripMoment 0 (0 + 1) 0 r (fun r => r) (fun p => modeVec L.order 0 (harmonicCos ν v) p.1 p.2 2)
          (gradMode L.order 0 (harmonicCos ν G) 2 2) (fun _ => 1)
        + Complex.I * heightStripMoment 0 (0 + 1) 0 r (fun r => r)
          (fun p => modeVec L.order 0 (harmonicSin ν v) p.1 p.2 2)
          (gradMode L.order 0 (harmonicSin ν G) 2 2) (fun _ => 1) := rfl

theorem keyHarmonic_planeOdd (hS : StripDataFlipAxisHolds) (hC : CornerDataFlipAxisHolds)
    (hL : HarmonicLiftStatement) (hP : PeriodicSecondOrderHolds) (L : CellLayout) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hp : IsPerturbation Γ P v G H g) (hf : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0)
    (Pg : ℝ → Space → Space) {ν : ℤ} (hν : Even ν) (key : SkeletonKey)
    (hm : GaugeKey.keyMode key = some 0) (hs : GaugeKey.planeSign key = some (-1))
    (hg : GaugeKey.KeyInHalfPlane key) : keyHarmonic L ν v G H Pg key = 0 := by
  have h1 : (0 : ℝ) < 0 + 1 := by norm_num
  cases key with
  | velocity n rad lev lo hi t a d =>
    simp only [GaugeKey.keyMode, Option.some.injEq] at hm
    subst hm
    simp only [GaugeKey.planeSign] at hs
    by_cases hrl : rad = false ∧ lev = 0
    · rw [if_pos hrl] at hs
      obtain ⟨rfl, rfl⟩ := hrl
      have ha : frameSign a = -1 := Option.some.inj hs
      have hlo : 0 ≤ lo := by simpa [GaugeKey.KeyInHalfPlane] using hg
      rw [keyHarmonic_velocity]
      exact strip_velocity_zero hS hL hP hp hf L.order hν a ha hlo h1 continuous_const (test_cont _ d)
    · rw [if_neg hrl] at hs
      exact absurd hs (by simp)
  | gradient n rad lev lo hi t a d =>
    simp only [GaugeKey.keyMode, Option.some.injEq] at hm
    subst hm
    simp only [GaugeKey.planeSign] at hs
    by_cases hrl : rad = false ∧ lev = 0
    · rw [if_pos hrl] at hs
      obtain ⟨rfl, rfl⟩ := hrl
      have ha : frameSign a = 1 := by
        have := Option.some.inj hs
        linarith
      have hlo : 0 ≤ lo := by simpa [GaugeKey.KeyInHalfPlane] using hg
      rw [keyHarmonic_gradient]
      exact strip_gradient_zero hS hL hP hp hf L.order hν a ha hlo h1 (test_cont _ d)
    · rw [if_neg hrl] at hs
      exact absurd hs (by simp)
  | pressure n rad lev lo hi t d =>
    simp only [GaugeKey.planeSign] at hs
    by_cases hrl : rad = false ∧ lev = 0
    · rw [if_pos hrl] at hs
      have := Option.some.inj hs
      norm_num at this
    · rw [if_neg hrl] at hs
      exact absurd hs (by simp)
  | corner n p a =>
    simp only [GaugeKey.keyMode, Option.some.injEq] at hm
    subst hm
    obtain ⟨r, z⟩ := p
    simp only [GaugeKey.planeSign] at hs
    by_cases hz : z = 0
    · subst hz
      rw [if_pos rfl] at hs
      have ha : frameSign a = -1 := Option.some.inj hs
      have hr : 0 < r := by simpa [GaugeKey.KeyInHalfPlane] using hg
      rw [keyHarmonic_corner]
      exact corner_zero hC hL hP hp hf L.order hν a ha hr h1
    · rw [if_neg hz] at hs
      exact absurd hs (by simp)
  | stream p =>
    obtain ⟨r, z⟩ := p
    simp only [GaugeKey.planeSign] at hs
    by_cases hz : z = 0
    · subst hz
      have ha : frameSign (2 : Fin 3) = -1 := by simp [frameSign]
      rw [keyHarmonic_stream]
      exact strip_velocity_zero hS hL hP hp hf L.order hν 2 ha (hi := r) le_rfl h1 (wt := fun r => r)
        continuous_id continuous_const
    · rw [if_neg hz] at hs
      exact absurd hs (by simp)
  | private_ =>
    simp [GaugeKey.keyMode] at hm

end PlaneOdd.Internal

namespace TreeEntry

open CellCalculus PlaneFlipFacts

theorem fieldPlaneOddZero_of (hS : StripDataFlipAxisHolds) (hC : CornerDataFlipAxisHolds)
    (hL : HarmonicLiftStatement) (hP : PeriodicSecondOrderHolds) {k : ℕ} {C : Type} {nE nM : ℕ}
    {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R) : T.FieldPlaneOddZero := by
  intro q v G H g Pg hyp ι key hodd hgeo
  obtain ⟨-, hmc, hpert, -, -⟩ := hyp
  obtain ⟨h1, hm, hs⟩ := hodd
  have hν : Even (labelTime ι) := ⟨ι.2, by simp only [labelTime, h1]; ring⟩
  exact PlaneOdd.Internal.keyHarmonic_planeOdd hS hC hL hP T.keyLayout hpert hmc.flip Pg hν key hm hs hgeo

end TreeEntry

end CertCell

end Breakdown
