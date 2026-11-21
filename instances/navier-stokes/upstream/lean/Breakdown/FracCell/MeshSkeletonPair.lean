import Breakdown.FracCell.StMesh
import Breakdown.FracCell.SegmentIndependence
import Breakdown.FracCell.CornerIndependence
import Breakdown.FracCell.GaugeShiftOf
import Breakdown.FracCell.MeshRootZero
import Breakdown.FracCell.MeshEdgeJump
import Breakdown.FracCell.MeshSkeletonSegment

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshSkeletonInternal


structure LayoutValid {k N : ℕ} (c : FracCellData k N) (L : CellLayout) : Prop where
  order : L.order = c.order
  seg : ∀ s, IsFaceSegment (L.segment s)
  pseg : ∀ s, IsFaceSegment (L.presSegment s)
  seg_rad : ∀ s, (L.segment s).radial →
    (L.segment s).level ≠ 0 ∧ 0 ≤ min (L.segment s).level (L.segment s).other
  pseg_rad : ∀ s, (L.presSegment s).radial →
    (L.presSegment s).level ≠ 0 ∧ 0 ≤ min (L.presSegment s).level (L.presSegment s).other
  corner : ∀ cr, (L.corner cr).1 ≠ 0 ∧ (L.cornerOther cr).1 ≠ (L.corner cr).1 ∧
    (L.cornerOther cr).2 ≠ (L.corner cr).2 ∧ 0 ≤ min (L.corner cr).1 (L.cornerOther cr).1

variable {k : ℕ} (x : FieldTuple k)

theorem velMode_congr {L₁ L₂ : CellLayout} (h : L₁.order = L₂.order) (n : ℤ) (a : Fin 3) :
    L₁.velMode n x a = L₂.velMode n x a := by
  unfold CellLayout.velMode; rw [h]

theorem gradMode_congr {L₁ L₂ : CellLayout} (h : L₁.order = L₂.order) (n : ℤ) (a b : Fin 3) :
    L₁.gradModeOf n x a b = L₂.gradModeOf n x a b := by
  unfold CellLayout.gradModeOf; rw [h]

theorem secondMode_congr {L₁ L₂ : CellLayout} (h : L₁.order = L₂.order) (n : ℤ) (a b e : Fin 3) :
    L₁.secondModeOf n x a b e = L₂.secondModeOf n x a b e := by
  unfold CellLayout.secondModeOf; rw [h]

theorem pressureGrad_congr {L₁ L₂ : CellLayout} (h : L₁.order = L₂.order) (n : ℤ) (a : Fin 3) :
    L₁.pressureGradMode n x a = L₂.pressureGradMode n x a := by
  unfold CellLayout.pressureGradMode; rw [h]

theorem pressMode_congr {L₁ L₂ : CellLayout} (h : L₁.order = L₂.order) (hg : L₁.gauge = L₂.gauge) (n : ℤ) :
    L₁.pressMode n x = L₂.pressMode n x := by
  unfold CellLayout.pressMode CellLayout.pressureOf CellLayout.gaugeValue CellLayout.gaugeUnit
    CellLayout.pressureGradMode
  rw [h, hg]


variable {N : ℕ} {c : FracCellData k N} {x}

theorem vel_case (hx : IsAdmissible c x) {L₁ L₂ : CellLayout} (h₁ : LayoutValid c L₁) (h₂ : LayoutValid c L₂)
    (g₁ g₂ : GaugeShift k) (q : L₁.modes × Fin L₁.segCount × Fin 3 × Fin (L₁.degSide + 2))
    (w : L₂.modes × Fin L₂.segCount × Fin 3 × Fin (L₂.degSide + 2))
    (hk : keyOf L₁ (Sum.inr (Sum.inr (Sum.inl q))) = keyOf L₂ (Sum.inr (Sum.inr (Sum.inl w)))) :
    L₁.shiftedData g₁ x (Sum.inr (Sum.inr (Sum.inl q))) = L₂.shiftedData g₂ x (Sum.inr (Sum.inr (Sum.inl w))) := by
  obtain ⟨n₁, s₁, a₁, e₁⟩ := q
  obtain ⟨n₂, s₂, a₂, e₂⟩ := w
  simp only [keyOf, Sum.elim_inl, Sum.elim_inr, SkeletonKey.velocity.injEq] at hk
  obtain ⟨hn, hr, hl, hlo, hhi, ht, ha, he⟩ := hk
  subst ha
  have hO : L₂.order = L₁.order := h₂.order.trans h₁.order.symm
  simp only [CellLayout.shiftedData, CellLayout.trueData, CellLayout.pressureShift, Sum.elim_inl, Sum.elim_inr,
    add_zero, velMode_congr x hO, gradMode_congr x hO]
  rw [← hn, ← he]
  exact (segmentIndependence_holds c x hx L₁ h₁.order n₁ _ _ (h₁.seg s₁) (h₂.seg s₂) hr hl hlo hhi ht
    (fun h => (h₁.seg_rad s₁ h).1) (fun h => ⟨(h₁.seg_rad s₁ h).2, (h₂.seg_rad s₂ (hr ▸ h)).2⟩) a₁ e₁).1

theorem grad_case (hx : IsAdmissible c x) {L₁ L₂ : CellLayout} (h₁ : LayoutValid c L₁) (h₂ : LayoutValid c L₂)
    (g₁ g₂ : GaugeShift k) (q : L₁.modes × Fin L₁.segCount × Fin 3 × Fin (L₁.degSide + 1))
    (w : L₂.modes × Fin L₂.segCount × Fin 3 × Fin (L₂.degSide + 1))
    (hk : keyOf L₁ (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))) = keyOf L₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inl w))))) :
    L₁.shiftedData g₁ x (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))) =
      L₂.shiftedData g₂ x (Sum.inr (Sum.inr (Sum.inr (Sum.inl w)))) := by
  obtain ⟨n₁, s₁, a₁, e₁⟩ := q
  obtain ⟨n₂, s₂, a₂, e₂⟩ := w
  simp only [keyOf, Sum.elim_inl, Sum.elim_inr, SkeletonKey.gradient.injEq] at hk
  obtain ⟨hn, hr, hl, hlo, hhi, ht, ha, he⟩ := hk
  subst ha
  have hO : L₂.order = L₁.order := h₂.order.trans h₁.order.symm
  simp only [CellLayout.shiftedData, CellLayout.trueData, CellLayout.pressureShift, Sum.elim_inl, Sum.elim_inr,
    add_zero, secondMode_congr x hO, gradMode_congr x hO]
  rw [← hn, ← he]
  exact (segmentIndependence_holds c x hx L₁ h₁.order n₁ _ _ (h₁.seg s₁) (h₂.seg s₂) hr hl hlo hhi ht
    (fun h => (h₁.seg_rad s₁ h).1) (fun h => ⟨(h₁.seg_rad s₁ h).2, (h₂.seg_rad s₂ (hr ▸ h)).2⟩) a₁ e₁).2.1

theorem corner_case (hx : IsAdmissible c x) {L₁ L₂ : CellLayout} (h₁ : LayoutValid c L₁) (h₂ : LayoutValid c L₂)
    (g₁ g₂ : GaugeShift k) (q : L₁.modes × Fin L₁.cornerCount × Fin 3) (w : L₂.modes × Fin L₂.cornerCount × Fin 3)
    (hk : keyOf L₁ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))))) =
      keyOf L₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl w))))))) :
    L₁.shiftedData g₁ x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))))) =
      L₂.shiftedData g₂ x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl w)))))) := by
  obtain ⟨n₁, c₁, a₁⟩ := q
  obtain ⟨n₂, c₂, a₂⟩ := w
  simp only [keyOf, Sum.elim_inl, Sum.elim_inr, SkeletonKey.corner.injEq] at hk
  obtain ⟨hn, hp, ha⟩ := hk
  subst ha
  have hO : L₂.order = L₁.order := h₂.order.trans h₁.order.symm
  simp only [CellLayout.shiftedData, CellLayout.trueData, CellLayout.pressureShift, Sum.elim_inl, Sum.elim_inr,
    add_zero, secondMode_congr x hO, gradMode_congr x hO, velMode_congr x hO]
  rw [← hn, ← hp]
  obtain ⟨a1, a2, a3, a4⟩ := h₁.corner c₁
  obtain ⟨b1, b2, b3, b4⟩ := h₂.corner c₂
  rw [← hp] at b1 b2 b3 b4
  exact cornerIndependence_holds c x hx L₁ h₁.order n₁ _ _ _ _ _ _ a1 a2 a3 b2 b3 a4 b4 a₁

theorem stream_case (hS : StreamIndependenceStatement) (hx : IsAdmissible c x) {L₁ L₂ : CellLayout}
    (h₁ : LayoutValid c L₁) (h₂ : LayoutValid c L₂)
    (g₁ g₂ : GaugeShift k) (q : Fin L₁.cornerCount) (w : Fin L₂.cornerCount)
    (hk : keyOf L₁ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))))) =
      keyOf L₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl w)))))))) :
    L₁.shiftedData g₁ x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))))) =
      L₂.shiftedData g₂ x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl w))))))) := by
  simp only [keyOf, Sum.elim_inl, Sum.elim_inr, SkeletonKey.stream.injEq] at hk
  have hO : L₂.order = L₁.order := h₂.order.trans h₁.order.symm
  simp only [CellLayout.shiftedData, CellLayout.trueData, CellLayout.pressureShift, Sum.elim_inl, Sum.elim_inr,
    add_zero, gradMode_congr x hO, velMode_congr x hO]
  rw [← hk]
  obtain ⟨a1, a2, a3, a4⟩ := h₁.corner q
  obtain ⟨b1, b2, b3, b4⟩ := h₂.corner w
  rw [← hk] at b3
  have hpos : 0 < (L₁.corner q).1 := lt_of_le_of_ne (le_trans a4 (min_le_left _ _)) (Ne.symm a1)
  exact hS c x hx L₁ h₁.order _ _ _ _ hpos a3 b3

theorem pres_case (hx : IsAdmissible c x) {L₁ L₂ : CellLayout} (h₁ : LayoutValid c L₁) (h₂ : LayoutValid c L₂)
    (hg : L₁.gauge = L₂.gauge) (l₁ r₁ l₂ r₂ : FieldTuple k → ℝ)
    (q : L₁.modes × Fin L₁.presCount × Fin L₁.degSide) (w : L₂.modes × Fin L₂.presCount × Fin L₂.degSide)
    (hk : keyOf L₁ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))) =
      keyOf L₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl w))))))
    (hnode : ∀ u ∈ pressurePositions L₁ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))),
      ∀ v ∈ pressurePositions L₂ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl w))))),
        u.1 = v.1 → (if u.2 then r₁ x else l₁ x) = (if v.2 then r₂ x else l₂ x)) :
    L₁.shiftedData (L₁.gaugeShiftOf l₁ r₁) x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))) =
      L₂.shiftedData (L₂.gaugeShiftOf l₂ r₂) x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl w))))) := by
  obtain ⟨n₁, s₁, j₁⟩ := q
  obtain ⟨n₂, s₂, j₂⟩ := w
  simp only [keyOf, Sum.elim_inl, Sum.elim_inr, SkeletonKey.pressure.injEq] at hk
  obtain ⟨hn, hr, hl, hlo, hhi, ht, hj⟩ := hk
  simp only [pressurePositions, Sum.elim_inl, Sum.elim_inr] at hnode
  have hO : L₂.order = L₁.order := h₂.order.trans h₁.order.symm
  have hm := (segmentIndependence_holds c x hx L₁ h₁.order n₁ _ _ (h₁.pseg s₁) (h₂.pseg s₂) hr hl hlo hhi ht
    (fun h => (h₁.pseg_rad s₁ h).1) (fun h => ⟨(h₁.pseg_rad s₁ h).2, (h₂.pseg_rad s₂ (hr ▸ h)).2⟩) 0 j₁).2.2
  have htest : (L₁.presSegment s₁).test j₁ = (L₂.presSegment s₂).test j₂ := by
    funext u
    simp only [FaceSegment.test, ht, hj]
  have hshift : L₁.pressureShift (L₁.gaugeShiftOf l₁ r₁) x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (n₁, s₁, j₁)))))) =
      L₂.pressureShift (L₂.gaugeShiftOf l₂ r₂) x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (n₂, s₂, j₂)))))) := by
    simp only [CellLayout.pressureShift, Sum.elim_inl, Sum.elim_inr, CellLayout.gaugeShiftOf]
    rw [hn]
    by_cases h0 : (n₂ : ℤ) = 0
    · simp only [h0, if_true]
      cases hrad : (L₂.presSegment s₂).radial
      · have hrad1 : (L₁.presSegment s₁).radial = false := hr.trans hrad
        have e1 := hnode ((L₁.presSegment s₁).lo, decide ((L₁.presSegment s₁).lo = L₁.box.r₂))
          (by simp [hrad1]) ((L₂.presSegment s₂).lo, decide ((L₂.presSegment s₂).lo = L₂.box.r₂)) (by simp [hrad]) hlo
        have e2 := hnode ((L₁.presSegment s₁).hi, decide ((L₁.presSegment s₁).hi = L₁.box.r₂))
          (by simp [hrad1]) ((L₂.presSegment s₂).hi, decide ((L₂.presSegment s₂).hi = L₂.box.r₂)) (by simp [hrad]) hhi
        have k1 : (if (L₁.presSegment s₁).lo = L₁.box.r₂ then r₁ x else l₁ x) =
            (if (L₂.presSegment s₂).lo = L₂.box.r₂ then r₂ x else l₂ x) := by simpa using e1
        have k2 : (if (L₁.presSegment s₁).hi = L₁.box.r₂ then r₁ x else l₁ x) =
            (if (L₂.presSegment s₂).hi = L₂.box.r₂ then r₂ x else l₂ x) := by simpa using e2
        simp only [hrad1, Bool.false_eq_true, if_false]
        rw [k1, k2, htest, hlo, hhi]
      · have hrad1 : (L₁.presSegment s₁).radial = true := hr.trans hrad
        have e1 := hnode ((L₁.presSegment s₁).level, decide ((L₁.presSegment s₁).level ≠ L₁.box.r₁))
          (by simp [hrad1]) ((L₂.presSegment s₂).level, decide ((L₂.presSegment s₂).level ≠ L₂.box.r₁)) (by simp [hrad]) hl
        have k1 : (if (L₁.presSegment s₁).level = L₁.box.r₁ then l₁ x else r₁ x) =
            (if (L₂.presSegment s₂).level = L₂.box.r₁ then l₂ x else r₂ x) := by
          by_cases a1 : (L₁.presSegment s₁).level = L₁.box.r₁ <;>
            by_cases a2 : (L₂.presSegment s₂).level = L₂.box.r₁ <;> simpa [a1, a2] using e1
        simp only [hrad1, if_true]
        rw [k1, htest, hlo, hhi]
    · simp only [h0, if_false]
  simp only [CellLayout.shiftedData]
  rw [hshift]
  congr 1
  simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, pressureGrad_congr x hO, pressMode_congr x hO hg.symm]
  rw [← hn, ← hj, hm]

theorem shifted_eq (hS : StreamIndependenceStatement) (hx : IsAdmissible c x) {L₁ L₂ : CellLayout}
    (h₁ : LayoutValid c L₁) (h₂ : LayoutValid c L₂) (hg : L₁.gauge = L₂.gauge) (l₁ r₁ l₂ r₂ : FieldTuple k → ℝ)
    (d₁ : L₁.Datum) (d₂ : L₂.Datum) (hk : keyOf L₁ d₁ = keyOf L₂ d₂) (hp : keyOf L₁ d₁ ≠ SkeletonKey.private_)
    (hnode : ∀ u ∈ pressurePositions L₁ d₁, ∀ v ∈ pressurePositions L₂ d₂,
        u.1 = v.1 → (if u.2 then r₁ x else l₁ x) = (if v.2 then r₂ x else l₂ x)) :
    L₁.shiftedData (L₁.gaugeShiftOf l₁ r₁) x d₁ = L₂.shiftedData (L₂.gaugeShiftOf l₂ r₂) x d₂ := by
  rcases d₁ with q|q|q|q|q|q|q|q <;> rcases d₂ with w|w|w|w|w|w|w|w
  all_goals first
    | exact vel_case hx h₁ h₂ _ _ q w hk
    | exact grad_case hx h₁ h₂ _ _ q w hk
    | exact pres_case hx h₁ h₂ hg l₁ r₁ l₂ r₂ q w hk hnode
    | exact corner_case hx h₁ h₂ _ _ q w hk
    | exact stream_case hS hx h₁ h₂ _ _ q w hk
    | (exfalso; simp [keyOf] at hk hp)

theorem scale_eq {L₁ L₂ : CellLayout} (v : ℝ) (d₁ : L₁.Datum) (d₂ : L₂.Datum) (hk : keyOf L₁ d₁ = keyOf L₂ d₂)
    (hp : keyOf L₁ d₁ ≠ SkeletonKey.private_) : presetScale L₁ v d₁ = presetScale L₂ v d₂ := by
  rcases d₁ with q|q|q|q|q|q|q|q <;> rcases d₂ with w|w|w|w|w|w|w|w
  all_goals first
    | (exfalso; simp [keyOf] at hk hp; done)
    | simp [presetScale, IsPressureDatum]

end MeshSkeletonInternal

namespace MeshSkeletonInternal


def keyData (L : CellLayout) {k : ℕ} (x : FieldTuple k) (ν : ℝ → ℝ) : SkeletonKey → ℂ
  | SkeletonKey.velocity n rad lev lo hi t a d =>
      (keySegment rad lev lo hi t).moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d
  | SkeletonKey.gradient n rad lev lo hi t a d =>
      if rad then (keySegment rad lev lo hi t).moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0)
          (L.secondModeOf n x a 0 2) d
      else (keySegment rad lev lo hi t).moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0)
          (L.secondModeOf n x a 2 2) d
  | SkeletonKey.pressure n rad lev lo hi t d =>
      (keySegment rad lev lo hi t).moment true (L.pressMode n x) (L.pressureGradMode n x 0)
          (L.pressureGradMode n x 2) d
        + (if n = 0 then
            ((if rad then ν lev * ∫ z in lo..hi, (keySegment rad lev lo hi t).test d z
              else ν hi * radialWeightIntegral ((keySegment rad lev lo hi t).test d) hi
                - ν lo * radialWeightIntegral ((keySegment rad lev lo hi t).test d) lo : ℝ) : ℂ)
          else 0)
  | SkeletonKey.corner _ _ _ => 0
  | SkeletonKey.stream p =>
      heightStripMoment p.2 (p.2 + 1) 0 p.1 (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1)
  | SkeletonKey.private_ => 0

variable {k N : ℕ} {c : FracCellData k N} {x : FieldTuple k}

theorem keySegment_valid (S : FaceSegment) (h : IsFaceSegment S) :
    IsFaceSegment (keySegment S.radial S.level S.lo S.hi S.testCoef) :=
  ⟨by simp [keySegment], h.lo_lt_hi, h.test_leading⟩

theorem vel_key (hx : IsAdmissible c x) {L₀ L₁ : CellLayout} (h₀ : L₀.order = c.order) (h₁ : LayoutValid c L₁)
    (g : GaugeShift k) (ν : ℝ → ℝ) (q : L₁.modes × Fin L₁.segCount × Fin 3 × Fin (L₁.degSide + 2)) :
    L₁.shiftedData g x (Sum.inr (Sum.inr (Sum.inl q))) = keyData L₀ x ν (keyOf L₁ (Sum.inr (Sum.inr (Sum.inl q)))) := by
  obtain ⟨n, s, a, e⟩ := q
  have hO : L₀.order = L₁.order := h₀.trans h₁.order.symm
  simp only [keyOf, Sum.elim_inl, Sum.elim_inr, keyData, CellLayout.shiftedData, CellLayout.trueData,
    CellLayout.pressureShift, add_zero, velMode_congr x hO, gradMode_congr x hO]
  have hv := h₁.seg s
  exact (segmentIndependence_holds c x hx L₁ h₁.order n _ _ hv (keySegment_valid _ hv) rfl rfl rfl rfl rfl
    (fun h => (h₁.seg_rad s h).1)
    (fun h => ⟨(h₁.seg_rad s h).2, by
      have := (h₁.seg_rad s h).2
      simp only [keySegment]
      exact le_min (le_trans this (min_le_left _ _)) (by linarith [le_trans this (min_le_left _ _)])⟩) a e).1

theorem grad_key (hx : IsAdmissible c x) {L₀ L₁ : CellLayout} (h₀ : L₀.order = c.order) (h₁ : LayoutValid c L₁)
    (g : GaugeShift k) (ν : ℝ → ℝ) (q : L₁.modes × Fin L₁.segCount × Fin 3 × Fin (L₁.degSide + 1)) :
    L₁.shiftedData g x (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))) =
      keyData L₀ x ν (keyOf L₁ (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))) := by
  obtain ⟨n, s, a, e⟩ := q
  have hO : L₀.order = L₁.order := h₀.trans h₁.order.symm
  simp only [keyOf, Sum.elim_inl, Sum.elim_inr, keyData, CellLayout.shiftedData, CellLayout.trueData,
    CellLayout.pressureShift, add_zero, secondMode_congr x hO, gradMode_congr x hO]
  have hv := h₁.seg s
  have := (segmentIndependence_holds c x hx L₁ h₁.order n _ _ hv (keySegment_valid _ hv) rfl rfl rfl rfl rfl
    (fun h => (h₁.seg_rad s h).1)
    (fun h => ⟨(h₁.seg_rad s h).2, by
      have := (h₁.seg_rad s h).2
      simp only [keySegment]
      exact le_min (le_trans this (min_le_left _ _)) (by linarith [le_trans this (min_le_left _ _)])⟩) a e).2.1
  rw [this]
  rfl


theorem pres_key (hx : IsAdmissible c x) {L₀ L₁ : CellLayout} (h₀ : L₀.order = c.order) (h₁ : LayoutValid c L₁)
    (hg : L₀.gauge = L₁.gauge) (l r : FieldTuple k → ℝ) (ν : ℝ → ℝ)
    (q : L₁.modes × Fin L₁.presCount × Fin L₁.degSide)
    (hν : ∀ u ∈ pressurePositions L₁ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))),
      (if u.2 then r x else l x) = ν u.1) :
    L₁.shiftedData (L₁.gaugeShiftOf l r) x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))) =
      keyData L₀ x ν (keyOf L₁ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))))) := by
  obtain ⟨n, s, j⟩ := q
  have hO : L₀.order = L₁.order := h₀.trans h₁.order.symm
  simp only [pressurePositions, Sum.elim_inl, Sum.elim_inr] at hν
  simp only [keyOf, Sum.elim_inl, Sum.elim_inr, keyData, CellLayout.shiftedData, CellLayout.trueData,
    pressMode_congr x hO hg, pressureGrad_congr x hO]
  have hv := h₁.pseg s
  congr 1
  · exact (segmentIndependence_holds c x hx L₁ h₁.order n _ _ hv (keySegment_valid _ hv) rfl rfl rfl rfl rfl
      (fun h => (h₁.pseg_rad s h).1)
      (fun h => ⟨(h₁.pseg_rad s h).2, by
        have := (h₁.pseg_rad s h).2
        simp only [keySegment]
        exact le_min (le_trans this (min_le_left _ _)) (by linarith [le_trans this (min_le_left _ _)])⟩) 0 j).2.2
  · simp only [CellLayout.pressureShift, Sum.elim_inl, Sum.elim_inr, CellLayout.gaugeShiftOf]
    by_cases h0 : (n : ℤ) = 0
    · simp only [h0, if_true]
      cases hrad : (L₁.presSegment s).radial
      · have e1 := hν ((L₁.presSegment s).lo, decide ((L₁.presSegment s).lo = L₁.box.r₂)) (by simp [hrad])
        have e2 := hν ((L₁.presSegment s).hi, decide ((L₁.presSegment s).hi = L₁.box.r₂)) (by simp [hrad])
        have k1 : (if (L₁.presSegment s).lo = L₁.box.r₂ then r x else l x) = ν (L₁.presSegment s).lo := by
          simpa using e1
        have k2 : (if (L₁.presSegment s).hi = L₁.box.r₂ then r x else l x) = ν (L₁.presSegment s).hi := by
          simpa using e2
        simp only [Bool.false_eq_true, if_false]
        rw [k1, k2]
        rfl
      · have e1 := hν ((L₁.presSegment s).level, decide ((L₁.presSegment s).level ≠ L₁.box.r₁)) (by simp [hrad])
        have k1 : (if (L₁.presSegment s).level = L₁.box.r₁ then l x else r x) = ν (L₁.presSegment s).level := by
          by_cases a1 : (L₁.presSegment s).level = L₁.box.r₁ <;> simpa [a1] using e1
        simp only [if_true]
        rw [k1]
        rfl
    · simp only [h0, if_false]

theorem stream_key (hS : StreamIndependenceStatement) (hx : IsAdmissible c x) {L₀ L₁ : CellLayout}
    (h₀ : L₀.order = c.order) (h₁ : LayoutValid c L₁) (g : GaugeShift k) (ν : ℝ → ℝ) (q : Fin L₁.cornerCount) :
    L₁.shiftedData g x (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q))))))) =
      keyData L₀ x ν (keyOf L₁ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))))))) := by
  have hO : L₀.order = L₁.order := h₀.trans h₁.order.symm
  simp only [keyOf, Sum.elim_inl, Sum.elim_inr, keyData, CellLayout.shiftedData, CellLayout.trueData,
    CellLayout.pressureShift, add_zero, velMode_congr x hO, gradMode_congr x hO]
  obtain ⟨a1, a2, a3, a4⟩ := h₁.corner q
  have hpos : 0 < (L₁.corner q).1 := lt_of_le_of_ne (le_trans a4 (min_le_left _ _)) (Ne.symm a1)
  exact hS c x hx L₁ h₁.order _ _ _ _ hpos a3 (by linarith)

theorem shifted_key (hS : StreamIndependenceStatement) (hx : IsAdmissible c x) {L₀ L₁ : CellLayout}
    (h₀ : L₀.order = c.order) (h₁ : LayoutValid c L₁) (hg : L₀.gauge = L₁.gauge) (l r : FieldTuple k → ℝ)
    (ν : ℝ → ℝ) (d : L₁.Datum) (hp : keyOf L₁ d ≠ SkeletonKey.private_)
    (hc : ∀ n p a, keyOf L₁ d ≠ SkeletonKey.corner n p a)
    (hν : ∀ u ∈ pressurePositions L₁ d, (if u.2 then r x else l x) = ν u.1) :
    L₁.shiftedData (L₁.gaugeShiftOf l r) x d = keyData L₀ x ν (keyOf L₁ d) := by
  rcases d with q|q|q|q|q|q|q|q
  all_goals first
    | exact vel_key hx h₀ h₁ _ ν q
    | exact grad_key hx h₀ h₁ _ ν q
    | exact pres_key hx h₀ h₁ hg l r ν q hν
    | exact stream_key hS hx h₀ h₁ _ ν q
    | (exfalso; exact hc _ _ _ rfl)
    | (exfalso; simp [keyOf] at hp)

def keyScale (v : ℝ) : SkeletonKey → ℝ
  | SkeletonKey.pressure _ _ _ _ _ _ _ => v
  | _ => 1

def keyLevelPos : SkeletonKey → Prop
  | SkeletonKey.velocity _ rad lev _ _ _ _ _ => rad = true → 0 < lev
  | SkeletonKey.gradient _ rad lev _ _ _ _ _ => rad = true → 0 < lev
  | SkeletonKey.pressure _ rad lev _ _ _ _ => rad = true → 0 < lev
  | _ => True

theorem scale_key (L : CellLayout) (v : ℝ) (d : L.Datum) : presetScale L v d = keyScale v (keyOf L d) := by
  rcases d with q|q|q|q|q|q|q|q <;> simp [presetScale, IsPressureDatum, keyOf, keyScale]

theorem split_kinds (key : SkeletonKey) (l : List (SkeletonKey × ℝ)) (h : SegmentSplit key l) :
    key ≠ SkeletonKey.private_ ∧ (∀ n p a, key ≠ SkeletonKey.corner n p a) ∧
    (∀ q ∈ l, q.1 ≠ SkeletonKey.private_ ∧ (∀ n p a, q.1 ≠ SkeletonKey.corner n p a) ∧
      ∀ v, keyScale v q.1 = keyScale v key) ∧
    (∀ q ∈ l, ∀ rad lev lo hi t dd, q.1 = SkeletonKey.pressure 0 rad lev lo hi t dd →
      ∃ rad' lev' lo' hi' t' dd', key = SkeletonKey.pressure 0 rad' lev' lo' hi' t' dd') := by
  cases key with
  | velocity n rad lev lo hi t a d =>
    obtain ⟨_, _, _, hp, _⟩ := h
    refine ⟨by simp, by simp, fun q hq => ?_, fun q hq => ?_⟩
    · obtain ⟨lo', hi', t', d', he, _⟩ := hp q hq
      rw [he]; exact ⟨by simp, by simp, fun v => rfl⟩
    · obtain ⟨lo', hi', t', d', he, _⟩ := hp q hq
      intro rad lev lo hi t dd h2; rw [he] at h2; cases h2
  | gradient n rad lev lo hi t a d =>
    obtain ⟨_, _, _, hp, _⟩ := h
    refine ⟨by simp, by simp, fun q hq => ?_, fun q hq => ?_⟩
    · obtain ⟨lo', hi', t', d', he, _⟩ := hp q hq
      rw [he]; exact ⟨by simp, by simp, fun v => rfl⟩
    · obtain ⟨lo', hi', t', d', he, _⟩ := hp q hq
      intro rad lev lo hi t dd h2; rw [he] at h2; cases h2
  | pressure n rad lev lo hi t d =>
    obtain ⟨_, _, _, hp, _⟩ := h
    refine ⟨by simp, by simp, fun q hq => ?_, fun q hq => ?_⟩
    · obtain ⟨lo', hi', t', d', he, _⟩ := hp q hq
      rw [he]; exact ⟨by simp, by simp, fun v => rfl⟩
    · obtain ⟨lo', hi', t', d', he, _⟩ := hp q hq
      intro rad' lev' lo'' hi'' t'' dd h2
      rw [he] at h2
      simp only [SkeletonKey.pressure.injEq] at h2
      exact ⟨rad, lev, lo, hi, t, d, by rw [h2.1]⟩
  | corner n p a => exact h.elim
  | stream p => exact h.elim
  | private_ => exact h.elim

theorem part_lin (b : Fin 2) (l : List (SkeletonKey × ℝ)) (V : SkeletonKey → ℂ) :
    (if b = 0 then ((l.map (fun p => (p.2 : ℂ) * V p.1)).sum).re
      else ((l.map (fun p => (p.2 : ℂ) * V p.1)).sum).im) =
      (l.map (fun p => p.2 * (if b = 0 then (V p.1).re else (V p.1).im))).sum := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    by_cases hb : b = 0
    · simp only [hb, if_true] at ih ⊢
      simp [ih, Complex.re_ofReal_mul]
    · simp only [hb, if_false] at ih ⊢
      simp [ih, Complex.im_ofReal_mul]


end MeshSkeletonInternal

namespace MeshSkeletonInternal


variable {α : ℝ} {k N : ℕ} {c : FracCellData k N} {Sp : CellSplit k N} {M : MeshData k N Sp}

theorem layoutValid (hM : IsMeshData α c Sp M) (K : Fin Sp.cellCount) : LayoutValid c (M.coords K).layout :=
  ⟨hM.same_order K, (hM.segments_valid K).1, (hM.segments_valid K).2, hM.radial_segments K,
    hM.radial_pressure_segments K, hM.corners_valid K⟩

theorem side_value (M : MeshData k N Sp) (K : Fin Sp.cellCount) (x : FieldTuple k) (b : Bool) :
    (if b then M.canonicalRight K x else M.canonicalLeft K x) = M.classValue x (M.nodeClass K b) := by
  cases b <;> rfl

theorem sum_rowEntries {n : ℕ} (parts : List (Fin n × ℝ)) (f : Fin n → ℝ) :
    ∑ i, rowEntries parts i * f i = (parts.map (fun p => p.2 * f p.1)).sum := by
  induction parts with
  | nil => simp [rowEntries]
  | cons p ps ih =>
    simp only [rowEntries, List.map_cons, List.sum_cons] at ih ⊢
    rw [Finset.sum_congr rfl (fun i _ => add_mul _ _ _), Finset.sum_add_distrib, ih]
    simp [ite_mul, Finset.sum_ite_eq]

theorem value_eq (hS : StreamIndependenceStatement) (hM : IsMeshData α c Sp M) {x : FieldTuple k}
    (hx : IsAdmissible c x) (K K' : Fin Sp.cellCount) (d : (M.coords K).layout.Datum)
    (d' : (M.coords K').layout.Datum) (hk : keyOf _ d = keyOf _ d') (hp : keyOf _ d ≠ SkeletonKey.private_)
    (hnode : ∀ u ∈ (pressurePositions (M.coords K).layout d).map (fun q => (q.1, M.nodeClass K q.2)),
      ∀ v ∈ (pressurePositions (M.coords K').layout d').map (fun q => (q.1, M.nodeClass K' q.2)),
        u.1 = v.1 → u.2 = v.2) :
    (M.coords K).layout.shiftedData ((M.coords K).layout.gaugeShiftOf (M.canonicalLeft K) (M.canonicalRight K)) x d =
      (M.coords K').layout.shiftedData
        ((M.coords K').layout.gaugeShiftOf (M.canonicalLeft K') (M.canonicalRight K')) x d' := by
  refine shifted_eq hS hx (layoutValid hM K) (layoutValid hM K') (hM.same_gauge K K') _ _ _ _ d d' hk hp ?_
  intro u hu v hv huv
  rw [side_value, side_value]
  have e := hnode (u.1, M.nodeClass K u.2) (List.mem_map.2 ⟨u, hu, rfl⟩) (v.1, M.nodeClass K' v.2)
      (List.mem_map.2 ⟨v, hv, rfl⟩) huv
  simp only at e
  rw [e]

theorem localValue_eq (hS : StreamIndependenceStatement) (hM : IsMeshData α c Sp M) {x : FieldTuple k}
    (hx : IsAdmissible c x) (K K' : Fin Sp.cellCount)
    (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card)
    (j' : Fin (systemSkeletonCoords (M.coords K').layout (M.coords K').param).card)
    (hk : M.rowKey K j = M.rowKey K' j') (hp : M.rowKey K j ≠ SkeletonKey.private_)
    (h2 : (M.rowDatum K j).2 = (M.rowDatum K' j').2)
    (hnode : ∀ u ∈ M.rowNodes K j ++ M.rowNodes K' j', ∀ v ∈ M.rowNodes K j ++ M.rowNodes K' j',
      u.1 = v.1 → u.2 = v.2) :
    M.localValue c K x j = M.localValue c K' x j' := by
  unfold MeshData.localValue
  simp only [CellLayout.realPart]
  rw [value_eq hS hM hx K K' _ _ hk hp
      (fun u hu v hv => hnode u (List.mem_append_left _ hu) v (List.mem_append_right _ hv)),
    scale_eq c.splitVisc _ _ hk hp, h2]

theorem mode_of_pressure {L : CellLayout} (d : L.Datum) {n : ℤ} {rad : Bool} {lev lo hi : ℝ} {t : ℕ → ℕ → ℝ}
    {dd : ℕ} (h : keyOf L d = SkeletonKey.pressure n rad lev lo hi t dd) : L.modeOf d = n := by
  rcases d with q|q|q|q|q|q|q|q <;> simp [keyOf] at h
  simp only [CellLayout.modeOf, Sum.elim_inr, Sum.elim_inl]
  exact h.1

theorem deleted_key {L : CellLayout} (d : L.Datum) (h : L.IsGaugeDeleted d) :
    ∃ (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) (dd : ℕ), keyOf L d = SkeletonKey.pressure 0 rad lev lo hi t dd := by
  rcases d with q|q|q|q|q|q|q|q <;> simp [CellLayout.IsGaugeDeleted] at h
  refine ⟨(L.presSegment q.2.1).radial, (L.presSegment q.2.1).level, (L.presSegment q.2.1).lo,
    (L.presSegment q.2.1).hi, (L.presSegment q.2.1).testCoef, q.2.2, ?_⟩
  simp only [keyOf, Sum.elim_inr, Sum.elim_inl]
  rw [h.1]

theorem deleted_zero (h1 : 1 < α) (h2 : α < 5 / 4) (hc : IsFormData α c) (hM : IsMeshData α c Sp M)
    {x : FieldTuple k} (hx : IsAdmissible c x) (K' : Fin Sp.cellCount) (d : (M.coords K').layout.Datum)
    (hdel : (M.coords K').layout.IsGaugeDeleted d) :
    ((M.coords K').layout.shiftedData
      ((M.coords K').layout.gaugeShiftOf (M.canonicalLeft K') (M.canonicalRight K')) x d).re = 0 := by
  have hsp := hM.gauge_specs K'
  rcases d with q|q|q|q|q|q|q|q <;> simp [CellLayout.IsGaugeDeleted] at hdel
  obtain ⟨n, s, jj⟩ := q
  have hz := hsp.zero_mode
  have hn : n = ⟨0, hz⟩ := Subtype.ext hdel.1
  subst hn
  simp only [CellLayout.shiftedData]
  rw [show (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨0, hz⟩, s, jj))))) : (M.coords K').layout.Datum) =
    CellDatum.sidePressure ⟨0, hz⟩ s jj from rfl,
    GaugeShiftOf.Internal.shift_eq _ _ _ x ⟨0, hz⟩ s jj rfl, Complex.add_re,
    ← GaugeShiftOf.Internal.pdv_eq _ hz x s jj, Complex.ofReal_re]
  rcases (hsp.deleted_eq (s, jj)).1 hdel.2 with he | hr
  · have hJ := meshEdgeJump α h1 h2 c hc Sp M hM K' (s, jj) he x hx
    have hb := hsp.edge_balanced _ he
    have hne := hsp.edge_right_ne _ he
    rw [hJ]
    unfold CellLayout.gaugeJump
    rw [he]
    simp only
    rw [show (M.coords K').layout.shiftCoefLeft (s, jj) = -(M.coords K').layout.shiftCoefRight (s, jj) by linarith]
    field_simp
    ring
  · have hR := meshRootZero α h1 h2 c hc Sp M hM K' (s, jj) hr x hx
    unfold CellLayout.rootShifted at hR
    linarith

theorem system_part (K : Fin Sp.cellCount) (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card)
    (h0 : (M.coords K).layout.modeOf (M.rowDatum K j).1 = 0) : (M.rowDatum K j).2 = 0 := by
  have hsystem : (M.coords K).layout.IsSystemCoord (M.rowDatum K j) := by
    classical
    unfold MeshData.rowDatum
    have hmem := ((systemSkeletonCoords (M.coords K).layout (M.coords K).param).equivFin.symm j).2
    unfold systemSkeletonCoords at hmem
    exact (Finset.mem_filter.1 hmem).2
  have hr1 := hsystem.1
  rw [h0] at hr1
  rcases hr1 with h | h
  · exact absurd h (lt_irrefl 0)
  · exact h.2


end MeshSkeletonInternal

namespace MeshSkeletonInternal


variable {α : ℝ} {k N : ℕ} {c : FracCellData k N} {Sp : CellSplit k N} {M : MeshData k N Sp} {x : FieldTuple k}

theorem level_pos {L : CellLayout} (h : LayoutValid c L) (d : L.Datum) : keyLevelPos (keyOf L d) := by
  rcases d with q|q|q|q|q|q|q|q <;> simp only [keyOf, Sum.elim_inl, Sum.elim_inr, keyLevelPos] <;> try trivial
  · intro hr
    obtain ⟨a1, a2⟩ := h.seg_rad q.2.1 hr
    exact lt_of_le_of_ne (le_trans a2 (min_le_left _ _)) (Ne.symm a1)
  · intro hr
    obtain ⟨a1, a2⟩ := h.seg_rad q.2.1 hr
    exact lt_of_le_of_ne (le_trans a2 (min_le_left _ _)) (Ne.symm a1)
  · intro hr
    obtain ⟨a1, a2⟩ := h.pseg_rad q.2.1 hr
    exact lt_of_le_of_ne (le_trans a2 (min_le_left _ _)) (Ne.symm a1)

theorem list_div {β : Type*} (l : List β) (w f : β → ℝ) (s : ℝ) :
    (l.map (fun p => w p * (f p / s))).sum = (l.map (fun p => w p * f p)).sum / s := by
  induction l with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring


end MeshSkeletonInternal

end Breakdown.CellCert.CellCoordinates
