import Breakdown.CertCell.RowsMatchKeyFlipParts

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace KeyFlip.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open CellCert.CellCoordinates CellCalculus LocalField PlaneFlipFacts PlaneOdd.Internal

variable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}

theorem back {X Y : ℂ} {s : ℝ} (hs : s * s = 1) (e : Y = (s : ℂ) * X) : X = (s : ℂ) * Y := by
  rw [e, ← mul_assoc, ← Complex.ofReal_mul, hs, Complex.ofReal_one, one_mul]

theorem stripVel_flip (hS : StripDataFlipAxisHolds) (hL : HarmonicLiftStatement) (hP : PeriodicSecondOrderHolds)
    (hp : IsPerturbation Γ P v G H g) (hf : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (m : ℕ) {ν n : ℤ}
    (hn : Even (n + ν)) (a : Fin 3) {lo hi h : ℝ} (hlo : 0 ≤ lo) (hh : 0 < h) {wt t : ℝ → ℝ}
    (hwt : Continuous wt) (ht : Continuous t) :
    stripVel m ν (-n) v G a lo hi h wt t = (frameSign a : ℂ) * stripVel m ν n v G a lo hi h wt t := by
  by_cases hlh : lo < hi
  swap
  · simp only [stripVel, strip_null _ _ _ _ _ _ _ _ hlh, mul_zero, add_zero]
  have hv := hP Γ P v G H g hp
  rw [stripVel_as_plane hL hv m (even_neg hn) a hlo hwt ht, stripVel_as_plane hL hv m hn a hlo hwt ht,
    label_flip m hn]
  exact (hS Γ P v G H g hp hf _ a lo hi h h wt t hlo hlh hh hh hwt ht).1

theorem stripGrad_flip (hS : StripDataFlipAxisHolds) (hL : HarmonicLiftStatement) (hP : PeriodicSecondOrderHolds)
    (hp : IsPerturbation Γ P v G H g) (hf : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (m : ℕ) {ν n : ℤ}
    (hn : Even (n + ν)) (a : Fin 3) {lo hi h : ℝ} (hlo : 0 ≤ lo) (hh : 0 < h) {t : ℝ → ℝ} (ht : Continuous t) :
    stripGrad m ν (-n) G H a lo hi h t = ((-frameSign a : ℝ) : ℂ) * stripGrad m ν n G H a lo hi h t := by
  by_cases hlh : lo < hi
  swap
  · simp only [stripGrad, strip_null _ _ _ _ _ _ _ _ hlh, mul_zero, add_zero]
  have hv := hP Γ P v G H g hp
  rw [stripGrad_as_plane hL hv m (even_neg hn) a hlo hlh hh ht, stripGrad_as_plane hL hv m hn a hlo hlh hh ht,
    label_flip m hn]
  rw [(hS Γ P v G H g hp hf _ a lo hi h h (fun r => r) t hlo hlh hh hh continuous_id ht).2 (axis_admissible hlo ht)]
  push_cast
  ring

theorem cornerVal_flip (hC : CornerDataFlipAxisHolds) (hL : HarmonicLiftStatement) (hP : PeriodicSecondOrderHolds)
    (hp : IsPerturbation Γ P v G H g) (hf : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (m : ℕ) {ν n : ℤ}
    (hn : Even (n + ν)) (a : Fin 3) {cr h : ℝ} (hcr : 0 < cr) (hh : 0 < h) :
    cornerVal m ν (-n) v G H a cr h = (frameSign a : ℂ) * cornerVal m ν n v G H a cr h := by
  have hv := hP Γ P v G H g hp
  rw [cornerVal_as_plane hL hv m (even_neg hn) a hcr hh, cornerVal_as_plane hL hv m hn a hcr hh, label_flip m hn]
  exact hC Γ P v G H g hp hf _ a cr (cr + 1) h h hcr (by linarith) (ne_of_lt (lt_add_one cr)) hh hh

theorem presKey_flip (hPS : PressureStripFlipHolds) (L : CellLayout) (hm : 1 ≤ L.order) (x : Assembly.FieldTuple 0)
    (hpot : IsPotentialOf x.2.2.2.2 (headPotential x.2.2.2.2)) (hsq : IsSquareIntegrableNear x.2.2.2.2)
    (hfl : ∀ᵐ y, x.2.2.2.2 (flipPoint y) = flipPoint (x.2.2.2.2 y)) (n : ℤ) {lo : ℝ} (hi : ℝ) (t : ℕ → ℕ → ℝ)
    (d : ℕ) (hlo : 0 ≤ lo) :
    keyValue L x (SkeletonKey.pressure (-n) false 0 lo hi t d) = keyValue L x (SkeletonKey.pressure n false 0 lo hi t d) := by
  rw [PlanePairInternal.keyValue_pressure_plane L x (-n) lo hi t d, PlanePairInternal.keyValue_pressure_plane L x n lo hi t d]
  have hS := test_cont (keySeg false 0 lo hi t) d
  rcases lt_or_ge lo hi with hlh | hlh
  · exact hPS L.order x.2.2.2.2 (headPotential x.2.2.2.2) hm hpot hsq hfl n lo hi 1 1 (fun r => r) _
      (axis_admissible hlo hS) hlh one_pos one_pos continuous_id hS
  · rw [strip_null _ _ _ _ _ _ _ _ (not_lt.2 hlh), strip_null _ _ _ _ _ _ _ _ (not_lt.2 hlh)]

end KeyFlip.Internal

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates PlaneFlipFacts
  PlaneOdd.Internal KeyFlip.Internal

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def OddStreamKeyZero (D : CellLayerData k C nE nM) (L : CellLayout) : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ ν : ℤ, Odd ν → ∀ r : ℝ, 0 ≤ r →
      keyHarmonic L ν v G H Pg (SkeletonKey.stream (r, 0)) = 0

theorem keyPlaneFlip_of (hF : PlanePairInternal.PlaneTraceFacts) {D : CellLayerData k C nE nM} (L : CellLayout)
    (hL : L.order = D.azimuthOrder) (hodd : OddStreamKeyZero D L) : KeyPlaneFlip D L := by
  intro q v G H g Pg hyp ι key hpriv hmode hgeo hplane
  obtain ⟨hq, hmc, hpert, hPP, hPf⟩ := hyp
  have hf := hmc.flip
  have hm1 : 1 ≤ L.order := hL ▸ hmc.order_pos
  have hn : Even (ι.1 + labelTime ι) := ⟨ι.2, by simp only [labelTime]; ring⟩
  cases key with
  | velocity n rad lev lo hi t a d =>
    obtain ⟨hr, hl⟩ := hplane
    subst hr hl
    have hnι : n = ι.1 := by
      rcases hmode with h | ⟨p, h⟩
      · simpa [GaugeKey.keyMode] using h
      · cases h
    subst hnι
    have hlo : 0 ≤ lo := by simpa [GaugeKey.KeyInHalfPlane] using hgeo
    have e := stripVel_flip hF.strip hF.lift hF.second hpert hf L.order hn a (hi := hi) hlo (h := 0 + 1) (by norm_num)
      (wt := fun _ => 1) continuous_const (test_cont (keySeg false 0 lo hi t) d)
    exact back (frameSign_sq a) e
  | gradient n rad lev lo hi t a d =>
    obtain ⟨hr, hl⟩ := hplane
    subst hr hl
    have hnι : n = ι.1 := by
      rcases hmode with h | ⟨p, h⟩
      · simpa [GaugeKey.keyMode] using h
      · cases h
    subst hnι
    have hlo : 0 ≤ lo := by simpa [GaugeKey.KeyInHalfPlane] using hgeo
    have e := stripGrad_flip hF.strip hF.lift hF.second hpert hf L.order hn a (hi := hi) hlo (h := 0 + 1) (by norm_num)
      (test_cont (keySeg false 0 lo hi t) d)
    exact back (by show (-frameSign a) * (-frameSign a) = 1; rw [neg_mul_neg]; exact frameSign_sq a) e
  | pressure n rad lev lo hi t d =>
    obtain ⟨hr, hl⟩ := hplane
    subst hr hl
    have hnι : n = ι.1 := by
      rcases hmode with h | ⟨p, h⟩
      · simpa [GaugeKey.keyMode] using h
      · cases h
    subst hnι
    have hlo : 0 ≤ lo := by simpa [GaugeKey.KeyInHalfPlane] using hgeo
    have hc := presKey_flip hF.pressure L hm1 (cosTuple (labelTime ι) v G H Pg)
      (hF.shift _ _ _ (MeshGaugeLinearPotential.potentialOf_spec _ (hPP.harmonic_gradient (labelTime ι)).1))
      (hF.square Pg hPP (labelTime ι)).1 (hF.flip Pg hPP hPf (labelTime ι)).1 ι.1 hi t d hlo
    have hs := presKey_flip hF.pressure L hm1 (sinTuple (labelTime ι) v G H Pg)
      (hF.shift _ _ _ (MeshGaugeLinearPotential.potentialOf_spec _ (hPP.harmonic_gradient (labelTime ι)).2))
      (hF.square Pg hPP (labelTime ι)).2 (hF.flip Pg hPP hPf (labelTime ι)).2 ι.1 hi t d hlo
    show keyHarmonic L (labelTime ι) v G H Pg (SkeletonKey.pressure ι.1 false 0 lo hi t d)
      = ((1 : ℝ) : ℂ) * keyHarmonic L (labelTime ι) v G H Pg (SkeletonKey.pressure (-ι.1) false 0 lo hi t d)
    simp only [keyHarmonic, hc, hs, Complex.ofReal_one, one_mul]
  | corner n p a =>
    obtain ⟨r, z⟩ := p
    have hz : z = 0 := hplane
    subst hz
    have hnι : n = ι.1 := by
      rcases hmode with h | ⟨p, h⟩
      · simpa [GaugeKey.keyMode] using h
      · cases h
    subst hnι
    have hr : 0 < r := hgeo
    have e := cornerVal_flip hF.corner hF.lift hF.second hpert hf L.order hn a hr (h := 0 + 1) (by norm_num)
    exact back (frameSign_sq a) e
  | stream p =>
    obtain ⟨r, z⟩ := p
    have hz : z = 0 := hplane
    subst hz
    have hr : 0 ≤ r := hgeo
    have h0 : keyHarmonic L (labelTime ι) v G H Pg (SkeletonKey.stream (r, 0)) = 0 := by
      rcases Int.even_or_odd (labelTime ι) with hν | hν
      · exact strip_velocity_zero hF.strip hF.lift hF.second hpert hf L.order hν 2 (by simp [frameSign]) le_rfl
          (h := 0 + 1) (by norm_num) (wt := fun r => r) continuous_id (t := fun _ => 1) continuous_const
      · exact hodd q v G H g Pg ⟨hq, hmc, hpert, hPP, hPf⟩ _ hν r hr
    show keyHarmonic L (labelTime ι) v G H Pg (SkeletonKey.stream (r, 0))
      = (keyFlipSign (SkeletonKey.stream (r, 0)) : ℂ) * keyHarmonic L (labelTime ι) v G H Pg (SkeletonKey.stream (r, 0))
    rw [h0, mul_zero]
  | private_ => exact absurd rfl hpriv

end Assembly

end CertCell

end Breakdown
