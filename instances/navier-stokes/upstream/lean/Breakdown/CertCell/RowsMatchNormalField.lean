import Breakdown.CertCell.RowsMatchNormalPoly

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.SegmentNormal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula LocalField SegmentLine
open Breakdown.CertCell.Assembly Breakdown.CertCell.SegmentNormal.Internal

theorem normalSegmentIdentity_trueData {k N : ℕ} {cd : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {L : CellLayout} (hL : IsCellLayout cd K S B L) (x : CellCert.Assembly.FieldTuple k)
    (hx : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1) : NormalSegmentIdentity L (L.trueData x) := by
  intro n s deg c₀ c₁ pcoef pdeg hend1 hc1 hok
  have hseg := hL.segment_valid s
  obtain ⟨⟨hr0, hr12⟩, ⟨hz0, hz12⟩⟩ := hL.box_valid
  have hlh : (L.segment s).lo < (L.segment s).hi := hseg.lo_lt_hi
  have hco : (L.segment s).level ≠ (L.segment s).other := fun h => hseg.other_ne h.symm
  have hdeg : (deg : ℕ) < L.degSide + 2 := by have := deg.2; omega
  have hvan : ∀ Q : Polynomial ℝ, Q.natDegree ≤ (deg : ℕ) + 1 →
      (∀ u, Q.eval u = ∑ i ∈ Finset.range (pdeg + 1), pcoef i * (L.segment s).test i u) →
      ∀ i, L.degSide + 2 ≤ i → i < pdeg + 1 → pcoef i = 0 := fun Q hQ hQe i hi hi' =>
    coef_zero_above (L.segment s) hseg.test_leading Q ((deg : ℕ) + 1) hQ (pdeg + 1) pcoef hQe i
      (by have := deg.2; omega) hi'
  have hVal : ∀ (a : Fin 3) (i : ℕ) (hi : i < L.degSide + 2), velVal L (L.trueData x) n s a i =
      (L.segment s).moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) i := by
    intro a i hi
    unfold velVal
    rw [dif_pos hi]
    rfl
  have hCor : ∀ (c : Fin L.cornerCount) (a : Fin 3), cornerVal L (L.trueData x) n (some c) a =
      cornerMoment (L.corner c).1 (L.cornerOther c).1 (L.corner c).2 (L.cornerOther c).2 (L.velMode n x a)
        (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) (L.secondModeOf n x a 0 2) := fun _ _ => rfl
  have hGrad : ∀ a : Fin 3, L.trueData x (CellDatum.sideGradient n s a deg) =
      if (L.segment s).radial then
        (L.segment s).moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) (L.secondModeOf n x a 0 2) deg
      else (L.segment s).moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0)
        (L.secondModeOf n x a 2 2) deg := fun _ => rfl
  constructor
  · intro hrad hlev hpoly
    obtain ⟨-, hlevel, hz1, hz2, -⟩ : (L.segment s).radial ∧ ((L.segment s).level = K.r₁ ∨
        (L.segment s).level = K.r₂) ∧ K.z₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.z₂ ∧
        (L.segment s).level ≠ 0 := by
      rcases hL.segment_on_side s with h | h
      · exact h
      · exact absurd hrad h.1
    have hoth : (L.segment s).other = K.r₁ + K.r₂ - (L.segment s).level := (hL.segment_other_in_box s).1 hrad
    have hc1' : L.corner c₁ = ((L.segment s).level, (L.segment s).hi) := by
      rw [hc1]
      simp [streamEnds, hrad]
    have hhi : (L.segment s).hi = K.z₂ := by
      rcases (hL.corner_is_corner c₁).2.1 with h | h
      · rw [hc1'] at h
        simp only at h
        linarith
      · rw [hc1'] at h
        exact h
    cases c₀ with
    | none => exact absurd hok.1 (by simp [hrad])
    | some c0 =>
      obtain ⟨-, hc0⟩ := hok
      have hc0' : L.corner c0 = ((L.segment s).level, (L.segment s).lo) := by
        rw [hc0]
        simp [streamEnds, hrad]
      have hlo : (L.segment s).lo = K.z₁ := by
        rcases (hL.corner_is_corner c0).2.1 with h | h
        · rw [hc0'] at h
          exact h
        · rw [hc0'] at h
          simp only at h
          linarith
      have ho1 : L.cornerOther c₁ = ((L.segment s).other, (L.segment s).lo) := by
        have h := hL.corner_other c₁
        rw [hc1'] at h
        refine Prod.ext ?_ ?_
        · rw [h.1, hoth]
        · rw [h.2, hhi, hlo]
          simp only
          ring
      have ho0 : L.cornerOther c0 = ((L.segment s).other, (L.segment s).hi) := by
        have h := hL.corner_other c0
        rw [hc0'] at h
        refine Prod.ext ?_ ?_
        · rw [h.1, hoth]
        · rw [h.2, hhi, hlo]
          simp only
          ring
      have hcpos : 0 < (L.segment s).level :=
        lt_of_le_of_ne (by rcases hlevel with h | h <;> rw [h] <;> linarith) (Ne.symm hlev)
      have hopos : 0 ≤ (L.segment s).other := by
        rw [hoth]
        rcases hlevel with h | h <;> rw [h] <;> linarith
      have hlo0 : 0 ≤ (L.segment s).lo := by linarith
      have hsum : ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) * velVal L (L.trueData x) n s 2 i =
          ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) * radialStripMoment (L.segment s).level
            (L.segment s).other (L.segment s).lo (L.segment s).hi (L.velMode n x 2) (L.gradModeOf n x 2 0)
            ((L.segment s).test i) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        by_cases h : i < L.degSide + 2
        · rw [hVal 2 i h]
          simp [FaceSegment.moment, hrad]
        · rw [hvan (slopePoly (L.segment s) deg) ((slopePoly_natDegree _ _).trans (Nat.le_succ _))
            (fun u => by rw [slopePoly_eval]; exact hpoly u) i (by omega) (Finset.mem_range.1 hi)]
          simp
      have hint := strip_int (m := L.order) hx n 2 0 (α := min (L.segment s).level (L.segment s).other)
        (β := max (L.segment s).level (L.segment s).other) (γ := (L.segment s).lo) (δ := (L.segment s).hi)
        (le_min hcpos.le hopos) ((1 / ((L.segment s).level - (L.segment s).other) : ℝ) : ℂ)
        (fun p => (((p.1 - (L.segment s).other) / ((L.segment s).level - (L.segment s).other) : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _))
      have hds : (fun u => ∑ i ∈ Finset.range (pdeg + 1), pcoef i * (L.segment s).test i u) =
          deriv ((L.segment s).test deg) := funext fun u => by rw [test_deriv]; exact (hpoly u).symm
      rw [hsum, ← radialStripMoment_sum (F := L.velMode n x 2) (dF := L.gradModeOf n x 2 0) hint _ pcoef (fun i => (L.segment s).test i)
        (fun i => (test_contDiff _ i).continuous), hds, hGrad 0, if_pos hrad, hVal 0 deg hdeg, hVal 1 deg hdeg,
        hCor c₁ 2, hCor c0 2, hc1', ho1, hc0', ho0]
      simp only [FaceSegment.moment, hrad, if_true]
      exact radial_identity (m := L.order) hx n hcpos hopos hco hlh hlo0 (test_contDiff _ _)
  · intro hrad hpoly
    have hnr : ¬ (L.segment s).radial := by simp [hrad]
    obtain ⟨-, hlevel, hr1, hr2⟩ : ¬ (L.segment s).radial ∧ ((L.segment s).level = K.z₁ ∨
        (L.segment s).level = K.z₂) ∧ K.r₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.r₂ := by
      rcases hL.segment_on_side s with h | h
      · exact absurd h.1 hnr
      · exact h
    have hoth : (L.segment s).other = K.z₁ + K.z₂ - (L.segment s).level := (hL.segment_other_in_box s).2 hnr
    have hc1' : L.corner c₁ = ((L.segment s).hi, (L.segment s).level) := by
      rw [hc1]
      simp [streamEnds, hrad]
    have hhi : (L.segment s).hi = K.r₂ := by
      rcases (hL.corner_is_corner c₁).1 with h | h
      · rw [hc1'] at h
        simp only at h
        linarith
      · rw [hc1'] at h
        exact h
    have hlor : (L.segment s).lo = K.r₁ := by
      cases c₀ with
      | none => linarith [hok.2]
      | some c0 =>
        have hc0' : L.corner c0 = ((L.segment s).lo, (L.segment s).level) := by
          rw [hok.2]
          simp [streamEnds, hrad]
        rcases (hL.corner_is_corner c0).1 with h | h
        · rw [hc0'] at h
          exact h
        · rw [hc0'] at h
          simp only at h
          linarith
    have ho1 : L.cornerOther c₁ = ((L.segment s).lo, (L.segment s).other) := by
      have h := hL.corner_other c₁
      rw [hc1'] at h
      refine Prod.ext ?_ ?_
      · rw [h.1, hhi, hlor]
        simp only
        ring
      · rw [h.2, hoth]
    have hcnn : 0 ≤ (L.segment s).level := by rcases hlevel with h | h <;> rw [h] <;> linarith
    have honn : 0 ≤ (L.segment s).other := by
      rw [hoth]
      rcases hlevel with h | h <;> rw [h] <;> linarith
    have hlo0 : 0 ≤ (L.segment s).lo := by linarith
    have hsum : ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) * velVal L (L.trueData x) n s 0 i =
        ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) * heightStripMoment (L.segment s).level
          (L.segment s).other (L.segment s).lo (L.segment s).hi (fun _ => 1) (L.velMode n x 0)
          (L.gradModeOf n x 0 2) ((L.segment s).test i) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      by_cases h : i < L.degSide + 2
      · rw [hVal 0 i h]
        simp [FaceSegment.moment, hrad]
      · have hQ : (Polynomial.X * slopePoly (L.segment s) deg).natDegree ≤ (deg : ℕ) + 1 := by
          have h1 := slopePoly_natDegree (L.segment s) deg
          have h2 := (Polynomial.natDegree_X_le : (Polynomial.X : Polynomial ℝ).natDegree ≤ 1)
          exact Polynomial.natDegree_mul_le.trans (by omega)
        rw [hvan _ hQ (fun u => by rw [Polynomial.eval_mul, Polynomial.eval_X, slopePoly_eval]; exact hpoly u) i
          (by omega) (Finset.mem_range.1 hi)]
        simp
    have hint := strip_int (m := L.order) hx n 0 2 (α := (L.segment s).lo) (β := (L.segment s).hi)
      (γ := min (L.segment s).level (L.segment s).other) (δ := max (L.segment s).level (L.segment s).other)
      hlo0 ((1 / ((L.segment s).level - (L.segment s).other) : ℝ) : ℂ)
      (fun p => (((p.2 - (L.segment s).other) / ((L.segment s).level - (L.segment s).other) : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _))
    have hds : (fun u => ∑ i ∈ Finset.range (pdeg + 1), pcoef i * (L.segment s).test i u) =
        fun u => u * deriv ((L.segment s).test deg) u := funext fun u => by rw [test_deriv]; exact (hpoly u).symm
    have key : heightStripMoment (L.segment s).level (L.segment s).other (L.segment s).lo (L.segment s).hi
        (fun r => r) (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 2) ((L.segment s).test deg) =
        -((((L.segment s).hi * (L.segment s).test deg (L.segment s).hi : ℝ) : ℂ) *
            cornerMoment (L.segment s).hi (L.segment s).lo (L.segment s).level (L.segment s).other
              (L.velMode n x 0) (L.gradModeOf n x 0 0) (L.gradModeOf n x 0 2) (L.secondModeOf n x 0 0 2))
          + (((L.segment s).lo * (L.segment s).test deg (L.segment s).lo : ℝ) : ℂ) *
            cornerMoment (L.segment s).lo (L.segment s).hi (L.segment s).level (L.segment s).other
              (L.velMode n x 0) (L.gradModeOf n x 0 0) (L.gradModeOf n x 0 2) (L.secondModeOf n x 0 0 2)
          + heightStripMoment (L.segment s).level (L.segment s).other (L.segment s).lo (L.segment s).hi
              (fun _ => 1) (L.velMode n x 0) (L.gradModeOf n x 0 2) (fun u => u * deriv ((L.segment s).test deg) u)
          - ((azimuth L.order n : ℂ) * Complex.I) *
            heightStripMoment (L.segment s).level (L.segment s).other (L.segment s).lo (L.segment s).hi
              (fun _ => 1) (L.velMode n x 1) (L.gradModeOf n x 1 2) ((L.segment s).test deg) :=
      height_identity (m := L.order) hx n hcnn honn hco hlh hlo0 (test_contDiff (L.segment s) deg)
    rw [hsum, ← heightStripMoment_sum (wt := fun _ => 1) (F := L.velMode n x 0) (dF := L.gradModeOf n x 0 2)
      continuous_const hint _ pcoef (fun i => (L.segment s).test i)
      (fun i => (test_contDiff _ i).continuous), hds, hGrad 2, if_neg hnr, hVal 1 deg hdeg, hCor c₁ 0, hc1', ho1]
    simp only [FaceSegment.moment, hrad, Bool.false_eq_true, if_false, if_true]
    cases c₀ with
    | none =>
      have hl0 : (L.segment s).lo = 0 := hok.2
      rw [key, show cornerVal L (L.trueData x) n none 0 = 0 from rfl, hl0]
      simp
    | some c0 =>
      have hc0' : L.corner c0 = ((L.segment s).lo, (L.segment s).level) := by
        rw [hok.2]
        simp [streamEnds, hrad]
      have ho0 : L.cornerOther c0 = ((L.segment s).hi, (L.segment s).other) := by
        have h := hL.corner_other c0
        rw [hc0'] at h
        refine Prod.ext ?_ ?_
        · rw [h.1, hhi, hlor]
          simp only
          ring
        · rw [h.2, hoth]
      rw [hCor c0 0, hc0', ho0]
      exact key

end Breakdown.CertCell.SegmentNormal
