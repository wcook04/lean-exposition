import Breakdown.CertCell.RowsMatchKeyFlipStatement
import Breakdown.FracCell.ConjugateData
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ}

section KeyData

def HarmonicTraceIndependence (D : CellLayerData k C nE nM) : Prop :=
  ∀ (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g Pg : ℝ → Space → Space),
    GaugeKey.fieldHyp D q v G H g Pg → ∀ (ν : ℤ) (x : CellCert.Assembly.FieldTuple 0),
    (x = cosTuple ν v G H Pg ∨ x = sinTuple ν v G H Pg) → ∀ L : CellLayout, L.order = D.azimuthOrder →
    (∀ (n : ℤ) (S S' : FaceSegment), IsFaceSegment S → IsFaceSegment S' → S.radial = S'.radial →
        S.level = S'.level → S.lo = S'.lo → S.hi = S'.hi → S.testCoef = S'.testCoef → (S.radial → S.level ≠ 0) →
        (S.radial → 0 ≤ min S.level S.other ∧ 0 ≤ min S'.level S'.other) → ∀ (a : Fin 3) (d : ℕ),
          S.moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d =
            S'.moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d ∧
          (if S.radial then S.moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0)
              (L.secondModeOf n x a 0 2) d
            else S.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) d) =
          (if S'.radial then S'.moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0)
              (L.secondModeOf n x a 0 2) d
            else S'.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) d) ∧
          S.moment true (headPressure L n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d =
            S'.moment true (headPressure L n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d) ∧
    (∀ (n : ℤ) (cr cz orr oz orr' oz' : ℝ), cr ≠ 0 → orr ≠ cr → oz ≠ cz → orr' ≠ cr → oz' ≠ cz →
        0 ≤ min cr orr → 0 ≤ min cr orr' → ∀ a : Fin 3,
          cornerMoment cr orr cz oz (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
              (L.secondModeOf n x a 0 2) =
            cornerMoment cr orr' cz oz' (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
              (L.secondModeOf n x a 0 2)) ∧
    (∀ (cr cz oz oz' : ℝ), 0 < cr → oz ≠ cz → oz' ≠ cz →
        heightStripMoment cz oz 0 cr (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1)
          = heightStripMoment cz oz' 0 cr (fun r => r) (L.velMode 0 x 2) (L.gradModeOf 0 x 2 2) (fun _ => 1))

namespace Internal.KeyData

theorem pair_facts {r₁ r₂ l : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ < r₂) (hl : l = r₁ ∨ l = r₂) :
    0 ≤ min l (r₁ + r₂ - l) ∧ r₁ + r₂ - l ≠ l ∧ 0 ≤ l ∧ 0 ≤ r₁ + r₂ - l := by
  rcases hl with rfl | rfl
  · refine ⟨le_min h0 (by linarith), by linarith, h0, by linarith⟩
  · refine ⟨le_min (by linarith) (by linarith), by linarith, by linarith, by linarith⟩

theorem keySeg_face (S : FaceSegment) (h : IsFaceSegment S) :
    IsFaceSegment (keySeg S.radial S.level S.lo S.hi S.testCoef) :=
  ⟨by simp [keySeg], h.lo_lt_hi, h.test_leading⟩

theorem headPressure_congr {L₁ L₂ : CellLayout} (h : L₁.order = L₂.order) {j : ℕ} (n : ℤ)
    (x : CellCert.Assembly.FieldTuple j) : headPressure L₁ n x = headPressure L₂ n x := by
  unfold headPressure
  rw [h]

theorem side_match {L L' : CellLayout} (hO : L'.order = L.order) (x : CellCert.Assembly.FieldTuple 0)
    (hI : ∀ (n : ℤ) (S S' : FaceSegment), IsFaceSegment S → IsFaceSegment S' → S.radial = S'.radial →
        S.level = S'.level → S.lo = S'.lo → S.hi = S'.hi → S.testCoef = S'.testCoef → (S.radial → S.level ≠ 0) →
        (S.radial → 0 ≤ min S.level S.other ∧ 0 ≤ min S'.level S'.other) → ∀ (a : Fin 3) (d : ℕ),
          S.moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d =
            S'.moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d ∧
          (if S.radial then S.moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0)
              (L.secondModeOf n x a 0 2) d
            else S.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) d) =
          (if S'.radial then S'.moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0)
              (L.secondModeOf n x a 0 2) d
            else S'.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) d) ∧
          S.moment true (headPressure L n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d =
            S'.moment true (headPressure L n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d)
    (S : FaceSegment) (hS : IsFaceSegment S) (hrad : S.radial → S.level ≠ 0 ∧ 0 ≤ min S.level S.other)
    (n : ℤ) (a : Fin 3) (d : ℕ) :
    S.moment false (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2) d =
        keyValue L' x (SkeletonKey.velocity n S.radial S.level S.lo S.hi S.testCoef a d) ∧
      (if S.radial then S.moment true (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) (L.secondModeOf n x a 0 2) d
        else S.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0) (L.secondModeOf n x a 2 2) d) =
        keyValue L' x (SkeletonKey.gradient n S.radial S.level S.lo S.hi S.testCoef a d) ∧
      S.moment true (headPressure L n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d =
        keyValue L' x (SkeletonKey.pressure n S.radial S.level S.lo S.hi S.testCoef d) := by
  have hk := hI n S (keySeg S.radial S.level S.lo S.hi S.testCoef) hS (keySeg_face S hS) rfl rfl rfl rfl rfl
    (fun h => (hrad h).1)
    (fun h => ⟨(hrad h).2, by
      have h0 := (hrad h).2
      simp only [keySeg]
      exact le_min (le_trans h0 (min_le_left _ _)) (by linarith [le_trans h0 (min_le_left _ _)])⟩) a d
  have eV := MeshSkeletonInternal.velMode_congr x hO n a
  have eG0 := MeshSkeletonInternal.gradMode_congr x hO n a 0
  have eG2 := MeshSkeletonInternal.gradMode_congr x hO n a 2
  have eT := fun b c => MeshSkeletonInternal.secondMode_congr x hO n a b c
  have eP0 := MeshSkeletonInternal.pressureGrad_congr x hO n 0
  have eP2 := MeshSkeletonInternal.pressureGrad_congr x hO n 2
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyValue, eV, eG0, eG2]
    exact hk.1
  · simp only [keyValue, eG0, eG2, eT]
    rw [hk.2.1]
    rfl
  · simp only [keyValue, headPressure_congr hO, eP0, eP2]
    exact hk.2.2

end Internal.KeyData


namespace Internal.KeyData

theorem head_key {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (hT : HarmonicTraceIndependence D)
    (hcc : CellCalculusConditions D R) {KL : CellLayout} (hKL : KL.order = D.azimuthOrder) {q : Fin k → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) (ν : ℤ) (x : CellCert.Assembly.FieldTuple 0)
    (hx : x = cosTuple ν v G H Pg ∨ x = sinTuple ν v G H Pg) (K : Fin D.mesh.count) (ι : D.mesh.resolved K)
    (d : ((R.layouts K).layout ι.1).Datum) (hp : keyOf ((R.layouts K).layout ι.1) d ≠ SkeletonKey.private_) :
    headData ((R.layouts K).layout ι.1) x d = keyValue KL x (keyOf ((R.layouts K).layout ι.1) d) := by
  obtain ⟨c, S, hco, -, hcl⟩ := (hcc.layouts_valid K).layout_valid ι.1 ι.2
  have hord : ((R.layouts K).layout ι.1).order = D.azimuthOrder := hcl.order_eq.trans hco
  obtain ⟨hI1, hI2, hI3⟩ := hT q v G H g Pg hfh ν x hx _ hord
  have hO : KL.order = ((R.layouts K).layout ι.1).order := hKL.trans hord.symm
  have hbox := hcl.box_valid
  have hr0 := hbox.r_order.1
  have hr12 := hbox.r_order.2
  have hz12 := hbox.z_order.2
  rcases d with w|w|w|w|w|w|w|w
  · exact absurd rfl hp
  · exact absurd rfl hp
  · obtain ⟨n, s, a, e⟩ := w
    have hrad : (((R.layouts K).layout ι.1).segment s).radial →
        (((R.layouts K).layout ι.1).segment s).level ≠ 0 ∧
          0 ≤ min (((R.layouts K).layout ι.1).segment s).level (((R.layouts K).layout ι.1).segment s).other := by
      intro hr
      rcases hcl.segment_on_side s with ⟨-, hl, -, -, hne⟩ | ⟨hnr, -⟩
      · refine ⟨hne, ?_⟩
        rw [(hcl.segment_other_in_box s).1 hr]
        exact (pair_facts hr0 hr12 hl).1
      · exact absurd hr hnr
    exact (side_match hO x hI1 _ (hcl.segment_valid s) hrad n a e).1
  · obtain ⟨n, s, a, e⟩ := w
    have hrad : (((R.layouts K).layout ι.1).segment s).radial →
        (((R.layouts K).layout ι.1).segment s).level ≠ 0 ∧
          0 ≤ min (((R.layouts K).layout ι.1).segment s).level (((R.layouts K).layout ι.1).segment s).other := by
      intro hr
      rcases hcl.segment_on_side s with ⟨-, hl, -, -, hne⟩ | ⟨hnr, -⟩
      · refine ⟨hne, ?_⟩
        rw [(hcl.segment_other_in_box s).1 hr]
        exact (pair_facts hr0 hr12 hl).1
      · exact absurd hr hnr
    exact (side_match hO x hI1 _ (hcl.segment_valid s) hrad n a e).2.1
  · obtain ⟨n, s, e⟩ := w
    obtain ⟨⟨hp1, -, -, -, hp5, -, -⟩, hpl⟩ := hcc.pressure_placed K ι.1 ι.2
    have hbe := hcl.box_eq
    have hrad : (((R.layouts K).layout ι.1).presSegment s).radial →
        (((R.layouts K).layout ι.1).presSegment s).level ≠ 0 ∧
          0 ≤ min (((R.layouts K).layout ι.1).presSegment s).level
            (((R.layouts K).layout ι.1).presSegment s).other := by
      intro hr
      refine ⟨hpl s hr, ?_⟩
      rcases hp1 s with ⟨-, hl⟩ | ⟨hnr, -⟩
      · rw [(hp5 s hr).2.2]
        rw [hbe] at hl ⊢
        exact (pair_facts hr0 hr12 hl).1
      · exact absurd hr hnr
    exact (side_match hO x hI1 _ (hcl.presSegment_valid s) hrad n 0 e).2.2
  · obtain ⟨n, c', a⟩ := w
    obtain ⟨hc1, -, hc0⟩ := hcl.corner_is_corner c'
    obtain ⟨-, hc2, -⟩ := hcl.corner_is_corner c'
    obtain ⟨ho1, ho2⟩ := hcl.corner_other c'
    obtain ⟨f1, f2, -, -⟩ := pair_facts hr0 hr12 hc1
    obtain ⟨-, g2, -, -⟩ := pair_facts hbox.z_order.1 hz12 hc2
    have e := hI2 n (((R.layouts K).layout ι.1).corner c').1 (((R.layouts K).layout ι.1).corner c').2
      (((R.layouts K).layout ι.1).cornerOther c').1 (((R.layouts K).layout ι.1).cornerOther c').2
      ((((R.layouts K).layout ι.1).corner c').1 + 1)
      ((((R.layouts K).layout ι.1).corner c').2 + 1) hc0 (by rw [ho1]; exact f2) (by rw [ho2]; exact g2)
      (by linarith) (by linarith) (by rw [ho1]; exact f1) (le_min (le_trans f1 (min_le_left _ _)) (by
        linarith [le_trans f1 (min_le_left _ _)])) a
    simp only [headData, CellLayout.trueData, keyOf, keyValue, Sum.elim_inr, Sum.elim_inl,
      MeshSkeletonInternal.velMode_congr x hO, MeshSkeletonInternal.gradMode_congr x hO,
      MeshSkeletonInternal.secondMode_congr x hO]
    exact e
  · obtain ⟨hc1, hc2, hc0⟩ := hcl.corner_is_corner w
    obtain ⟨-, ho2⟩ := hcl.corner_other w
    obtain ⟨f1, -, -, -⟩ := pair_facts hr0 hr12 hc1
    obtain ⟨-, g2, -, -⟩ := pair_facts hbox.z_order.1 hz12 hc2
    have hpos : 0 < (((R.layouts K).layout ι.1).corner w).1 :=
      lt_of_le_of_ne (le_trans f1 (min_le_left _ _)) (Ne.symm hc0)
    have e := hI3 (((R.layouts K).layout ι.1).corner w).1 (((R.layouts K).layout ι.1).corner w).2
      (((R.layouts K).layout ι.1).cornerOther w).2 ((((R.layouts K).layout ι.1).corner w).2 + 1) hpos (by rw [ho2]; exact g2) (by linarith)
    simp only [headData, CellLayout.trueData, keyOf, keyValue, Sum.elim_inr, Sum.elim_inl,
      MeshSkeletonInternal.velMode_congr x hO, MeshSkeletonInternal.gradMode_congr x hO]
    exact e
  · exact absurd rfl hp

end Internal.KeyData

open Internal.KeyData in
theorem keyHeadMatch_holds {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}
    (hT : HarmonicTraceIndependence D) (hcc : CellCalculusConditions D R) {L : CellLayout}
    (hL : L.order = D.azimuthOrder) : KeyHeadMatch D R L := by
  intro q v G H g Pg hfh K ι d hp
  unfold headHarmonic keyHarmonic
  rw [head_key hT hcc hL hfh _ _ (Or.inl rfl) K ι d hp, head_key hT hcc hL hfh _ _ (Or.inr rfl) K ι d hp]

theorem sideVelocityKeyMatch_holds {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}
    (hT : HarmonicTraceIndependence D) (hcc : CellCalculusConditions D R) {L : CellLayout}
    (hL : L.order = D.azimuthOrder) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g Pg : ℝ → Space → Space) (hfh : GaugeKey.fieldHyp D q v G H g Pg) (K : Fin D.mesh.count)
    (ι : D.mesh.resolved K) (n : ((R.layouts K).layout ι.1).modes) (s : Fin ((R.layouts K).layout ι.1).segCount)
    (a : Fin 3) (i : Fin (((R.layouts K).layout ι.1).degSide + 2)) :
    headHarmonic ((R.layouts K).layout ι.1) (labelTime ι.1) v G H Pg (CellDatum.sideVelocity n s a i)
      = keyHarmonic L (labelTime ι.1) v G H Pg (keyOf ((R.layouts K).layout ι.1) (CellDatum.sideVelocity n s a i)) :=
  keyHeadMatch_holds hT hcc hL q v G H g Pg hfh K ι _ (by simp [keyOf, CellDatum.sideVelocity])


namespace Internal.KeyData

open ConjugateDataInternal

theorem keyValue_conj (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (key : SkeletonKey) (n : ℤ)
    (hm : GaugeKey.keyMode key = some n) :
    keyValue L x (keyWithMode (-n) key) = conj (keyValue L x key) := by
  cases key with
  | velocity n' r l lo hi t a d =>
    simp only [GaugeKey.keyMode, Option.some.injEq] at hm
    subst hm
    simp only [keyWithMode, keyValue, velMode_neg, gradModeOf_neg, conj_segMoment]
  | gradient n' r l lo hi t a d =>
    simp only [GaugeKey.keyMode, Option.some.injEq] at hm
    subst hm
    cases r <;> simp only [keyWithMode, keyValue, gradModeOf_neg, secondModeOf_neg, conj_segMoment,
      if_true, Bool.false_eq_true, if_false]
  | pressure n' r l lo hi t d =>
    simp only [GaugeKey.keyMode, Option.some.injEq] at hm
    subst hm
    have hp : headPressure L (-n') x = fun p => conj (headPressure L n' x p) := by
      funext p
      simp only [headPressure, presMode]
      rw [conj_angle]
    simp only [keyWithMode, keyValue, hp, pressureGradMode_neg, conj_segMoment]
  | corner n' p a =>
    simp only [GaugeKey.keyMode, Option.some.injEq] at hm
    subst hm
    simp only [keyWithMode, keyValue, velMode_neg, gradModeOf_neg, secondModeOf_neg, conj_corner]
  | stream p =>
    simp only [GaugeKey.keyMode, Option.some.injEq] at hm
    subst hm
    have h1 := velMode_neg L x 0 2
    have h2 := gradModeOf_neg L x 0 2 2
    rw [neg_zero] at h1 h2
    simp only [keyWithMode, keyValue]
    rw [conj_heightStrip, ← h1, ← h2]
  | private_ => simp [GaugeKey.keyMode] at hm

theorem frameVec_neg (θ : ℝ) (u : Space) : frameVec θ (-u) = -frameVec θ u := by
  funext a
  fin_cases a <;> simp [frameVec, inner_neg_left]

theorem frameMat_neg (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) : frameMat θ (-M) a b = -frameMat θ M a b := by
  simp [frameMat, inner_neg_left]

theorem frameThird_neg (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    frameThird θ (-M) a b c = -frameThird θ M a b c := by
  simp [frameThird, inner_neg_left]

theorem modeVec_negField (m : ℕ) (n : ℤ) (v : Space → Space) (r z : ℝ) (a : Fin 3) :
    modeVec m n (-v) r z a = -modeVec m n v r z a := by
  simp only [modeVec, Pi.neg_apply, frameVec_neg, Complex.ofReal_neg, mul_neg, intervalIntegral.integral_neg]

theorem modeMat_negField (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) (a b : Fin 3) :
    modeMat m n (-G) r z a b = -modeMat m n G r z a b := by
  simp only [modeMat, Pi.neg_apply, frameMat_neg, Complex.ofReal_neg, mul_neg, intervalIntegral.integral_neg]

theorem modeThird_negField (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (p : ℝ × ℝ) : modeThird m n (-H) a b c p = -modeThird m n H a b c p := by
  simp only [modeThird, Pi.neg_apply, frameThird_neg, Complex.ofReal_neg, mul_neg, intervalIntegral.integral_neg]

theorem radial_neg (c o lo hi : ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    radialStripMoment c o lo hi (-F) (-dF) t = -radialStripMoment c o lo hi F dF t := by
  simp only [radialStripMoment, Pi.neg_apply, mul_neg, ← neg_add, neg_mul, integral_neg]

theorem height_neg (c o lo hi : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    heightStripMoment c o lo hi wt (-F) (-dF) t = -heightStripMoment c o lo hi wt F dF t := by
  simp only [heightStripMoment, Pi.neg_apply, mul_neg, ← neg_add, neg_mul, integral_neg]

theorem moment_neg' (S : FaceSegment) (w : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (d : ℕ) :
    S.moment w (-F) (-dFr) (-dFz) d = -S.moment w F dFr dFz d := by
  unfold FaceSegment.moment
  split_ifs <;> first
    | exact radial_neg _ _ _ _ _ _ _
    | exact height_neg _ _ _ _ _ _ _ _

theorem corner_neg (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) :
    cornerMoment cr orr cz oz (-F) (-Fr) (-Fz) (-Frz) = -cornerMoment cr orr cz oz F Fr Fz Frz := by
  simp only [cornerMoment, Pi.neg_apply, mul_neg, ← neg_add, integral_neg]

theorem moment_congr_ae' (S : FaceSegment) (w : Bool) {F F' : ℝ × ℝ → ℂ} (hF : ∀ᵐ p ∂volume, F' p = F p)
    (dFr dFz : ℝ × ℝ → ℂ) (d : ℕ) : S.moment w F' dFr dFz d = S.moment w F dFr dFz d := by
  unfold FaceSegment.moment radialStripMoment heightStripMoment
  split_ifs <;>
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hF] with p hp
    rw [hp]

end Internal.KeyData


namespace Internal.KeyData

theorem headPotential_neg_ae (m : ℕ) (n : ℤ) (Q : Space → Space) (hQ : SteadyCert.IsGradientField Q) :
    ∀ᵐ p : ℝ × ℝ ∂volume, presMode m n (headPotential (-Q)) p.1 p.2 = -presMode m n (headPotential Q) p.1 p.2 := by
  have hQQ : (-1 : ℝ) • Q + (0 : ℝ) • Q = -Q := by
    funext y
    simp
  obtain ⟨C, hC⟩ := MeshGaugeLinearPotential.potential_affine Q Q hQ hQ (-1) 0
  have hint : IntegrableOn (potentialOf Q) (Metric.ball (0 : Space) 1) :=
    ((FracInternal.MeshDataAffineModes.pot_locInt (MeshGaugeLinearPotential.potentialOf_spec Q hQ)).integrableOn_isCompact
      (isCompact_closedBall 0 1)).mono_set Metric.ball_subset_closedBall
  have hC' : potentialOf (-Q) =ᵐ[volume] fun y => -potentialOf Q y + C := by
    rw [← hQQ]
    filter_upwards [hC] with y hy
    rw [hy]
    ring
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  haveI : NeZero (volume.restrict (Metric.ball (0 : Space) 1)) :=
    ⟨by
      rw [Ne, Measure.restrict_eq_zero]
      exact (Metric.measure_ball_pos volume (0 : Space) one_pos).ne'⟩
  have hval : (⨍ z in Metric.ball (0 : Space) 1, potentialOf (-Q) z)
      = -(⨍ z in Metric.ball (0 : Space) 1, potentialOf Q z) + C := by
    have hr : (volume.restrict (Metric.ball (0 : Space) 1)).real Set.univ ≠ 0 := by
      simp only [Measure.real, Measure.restrict_apply_univ]
      exact (ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Space) one_pos).ne'
        measure_ball_lt_top.ne).ne'
    rw [average_congr (ae_restrict_of_ae hC'), average_eq, average_eq, integral_add (f := fun x => -potentialOf Q x) hint.neg (integrable_const C),
      integral_neg, integral_const, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    field_simp
  have hA := MeshDataAffineModes.gradient_modes_affine m Q Q hQ hQ (-1) 0 C
    (⨍ z in Metric.ball (0 : Space) 1, potentialOf Q z) 0
    (⨍ z in Metric.ball (0 : Space) 1, potentialOf (-Q) z) hC n
  filter_upwards [hA] with p hp
  obtain ⟨h1, -⟩ := hp
  rw [hQQ] at h1
  have hz : (C - (⨍ z in Metric.ball (0 : Space) 1, potentialOf (-Q) z)
      + -1 * (⨍ z in Metric.ball (0 : Space) 1, potentialOf Q z) + 0 * 0 : ℝ) = 0 := by
    rw [hval]
    ring
  show presMode m n (fun y => potentialOf (-Q) y - ⨍ z in Metric.ball (0 : Space) 1, potentialOf (-Q) z) p.1 p.2
    = -presMode m n (fun y => potentialOf Q y - ⨍ z in Metric.ball (0 : Space) 1, potentialOf Q z) p.1 p.2
  rw [h1, hz]
  push_cast
  ring

theorem velMode_negTuple (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (n : ℤ) (a : Fin 3) :
    L.velMode n (-x) a = -L.velMode n x a := by
  funext p
  simp only [CellLayout.velMode, Prod.fst_neg, modeVec_negField, Pi.neg_apply]

theorem gradModeOf_negTuple (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (n : ℤ) (a b : Fin 3) :
    L.gradModeOf n (-x) a b = -L.gradModeOf n x a b := by
  funext p
  simp only [CellLayout.gradModeOf, gradMode, Prod.fst_neg, Prod.snd_neg, modeMat_negField, Pi.neg_apply]

theorem secondModeOf_negTuple (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (n : ℤ)
    (a b c : Fin 3) : L.secondModeOf n (-x) a b c = -L.secondModeOf n x a b c := by
  funext p
  simp only [CellLayout.secondModeOf, Prod.fst_neg, Prod.snd_neg, modeThird_negField, Pi.neg_apply]

theorem pressureGradMode_negTuple (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (n : ℤ)
    (a : Fin 3) : L.pressureGradMode n (-x) a = -L.pressureGradMode n x a := by
  funext p
  simp only [CellLayout.pressureGradMode, Prod.snd_neg, modeVec_negField, Pi.neg_apply]

theorem keyValue_negTuple (L : CellLayout) (x : CellCert.Assembly.FieldTuple 0)
    (hQ : SteadyCert.IsGradientField x.2.2.2.2) (key : SkeletonKey) :
    keyValue L (-x) key = -keyValue L x key := by
  cases key with
  | velocity n r l lo hi t a d =>
    simp only [keyValue, velMode_negTuple, gradModeOf_negTuple, moment_neg']
  | gradient n r l lo hi t a d =>
    cases r <;> simp only [keyValue, gradModeOf_negTuple, secondModeOf_negTuple, moment_neg', if_true,
      Bool.false_eq_true, if_false]
  | pressure n r l lo hi t d =>
    have hp : ∀ᵐ p ∂volume, headPressure L n (-x) p = (-headPressure L n x) p := by
      filter_upwards [headPotential_neg_ae L.order n x.2.2.2.2 hQ] with p hp
      simp only [headPressure, Pi.neg_apply, Prod.snd_neg]
      exact hp
    simp only [keyValue]
    rw [moment_congr_ae' _ true hp, pressureGradMode_negTuple, pressureGradMode_negTuple, moment_neg']
  | corner n p a =>
    simp only [keyValue, velMode_negTuple, gradModeOf_negTuple, secondModeOf_negTuple, corner_neg]
  | stream p =>
    simp only [keyValue, velMode_negTuple, gradModeOf_negTuple, height_neg]
  | private_ => simp [keyValue]

theorem harmonicCos_negFreq {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (ν : ℤ) (f : ℝ → Space → β) :
    harmonicCos (-ν) f = harmonicCos ν f := by
  funext y
  simp only [harmonicCos, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]

theorem harmonicSin_negFreq {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (ν : ℤ) (f : ℝ → Space → β) :
    harmonicSin (-ν) f = -harmonicSin ν f := by
  funext y
  simp only [harmonicSin, Int.cast_neg, mul_neg, neg_mul, Real.sin_neg, neg_smul, integral_neg, Pi.neg_apply]

theorem cosTuple_negFreq (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) :
    cosTuple (-ν) v G H Pg = cosTuple ν v G H Pg := by
  simp only [cosTuple, harmonicCos_negFreq]

theorem sinTuple_negFreq (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) :
    sinTuple (-ν) v G H Pg = -sinTuple ν v G H Pg := by
  simp only [sinTuple, harmonicSin_negFreq, Prod.neg_mk, neg_zero]

theorem keyHarmonic_conj (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (hPg : SteadyCert.IsGradientField (harmonicSin ν Pg)) (key : SkeletonKey) (n : ℤ)
    (hm : GaugeKey.keyMode key = some n) :
    keyHarmonic L (-ν) v G H Pg (keyWithMode (-n) key) = conj (keyHarmonic L ν v G H Pg key) := by
  unfold keyHarmonic
  rw [cosTuple_negFreq, sinTuple_negFreq, keyValue_negTuple L (sinTuple ν v G H Pg) hPg,
    keyValue_conj L (cosTuple ν v G H Pg) key n hm, keyValue_conj L (sinTuple ν v G H Pg) key n hm]
  simp only [map_add, map_mul, Complex.conj_I]
  ring

end Internal.KeyData


namespace Internal.KeyData

theorem keyWithMode_self {key : SkeletonKey} {n : ℤ} (hm : GaugeKey.keyMode key = some n) :
    keyWithMode n key = key := by
  cases key <;> simp only [GaugeKey.keyMode, Option.some.injEq, reduceCtorEq] at hm <;> subst hm <;> rfl

theorem keyWithMode_twice (a b : ℤ) (key : SkeletonKey) : keyWithMode a (keyWithMode b key) = keyWithMode a key := by
  cases key <;> rfl

theorem keyMode_withMode {key : SkeletonKey} {n : ℤ} (hm : GaugeKey.keyMode key = some n) (a : ℤ) :
    GaugeKey.keyMode (keyWithMode a key) = some a ∨ ∃ p, keyWithMode a key = SkeletonKey.stream p := by
  cases key with
  | stream p => exact Or.inr ⟨p, rfl⟩
  | private_ => simp [GaugeKey.keyMode] at hm
  | _ => exact Or.inl rfl

theorem labelTime_negLabel (ι : ℤ × ℤ) : labelTime (-ι) = -labelTime ι := by
  simp only [labelTime, Prod.fst_neg, Prod.snd_neg]
  ring

theorem labelTime_flipLabel (ι : ℤ × ℤ) : labelTime (labelFlip ι) = labelTime ι := by
  simp only [labelTime, labelFlip]
  ring

theorem conj_evaluation (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (hPg : SteadyCert.IsGradientField (harmonicSin ν Pg)) {key : SkeletonKey} {m : ℤ}
    (hmode : GaugeKey.keyMode key = some m ∨ ∃ p, key = SkeletonKey.stream p) :
    keyHarmonic L (-ν) v G H Pg (keyWithMode (-m) key) = (starRingEnd ℂ) (keyHarmonic L ν v G H Pg key) := by
  rcases hmode with hm | ⟨p, rfl⟩
  · exact keyHarmonic_conj L ν v G H Pg hPg key m hm
  · have e := keyHarmonic_conj L ν v G H Pg hPg (SkeletonKey.stream p) 0 rfl
    simpa [keyWithMode] using e

end Internal.KeyData

open Internal.KeyData in
theorem keyEvalTransfer_holds {D : CellLayerData k C nE nM} {L : CellLayout} (hF : KeyPlaneFlip D L) :
    KeyEvalTransfer D L := by
  intro q v G H g Pg hfh ι key rd hp hmode hgeo hr
  have hPg : ∀ ν, SteadyCert.IsGradientField (harmonicSin ν Pg) := fun ν => (hfh.2.2.2.1.harmonic_gradient ν).2
  have hself : keyWithMode ι.1 key = key := by
    rcases hmode with hm | ⟨p, rfl⟩
    · exact keyWithMode_self hm
    · rfl
  unfold evalValue
  rcases hr with ⟨hl, hc, hs⟩ | ⟨hl, hc, hs⟩ | ⟨hl, hc, hon, hs⟩ | ⟨hl, hc, hon, hs⟩
  · rw [hl, hc, hs, hself]
    simp
  · rw [hl, hc, hs, labelTime_negLabel, Prod.fst_neg, conj_evaluation L _ v G H Pg (hPg _) hmode]
    simp
  · rw [hl, hc, hs, labelTime_flipLabel]
    simp only [Bool.false_eq_true, if_false]
    exact hF q v G H g Pg hfh ι key hp hmode hgeo hon
  · have h1 := hF q v G H g Pg hfh ι key hp hmode hgeo hon
    have hmode' : GaugeKey.keyMode (keyWithMode (-ι.1) key) = some (-ι.1) ∨
        ∃ p, keyWithMode (-ι.1) key = SkeletonKey.stream p := by
      rcases hmode with hm | ⟨p, rfl⟩
      · exact keyMode_withMode hm _
      · exact Or.inr ⟨p, rfl⟩
    have h2 := conj_evaluation L (labelTime ι) v G H Pg (hPg _) hmode'
    rw [neg_neg, keyWithMode_twice] at h2
    have hf1 : (-labelFlip ι).1 = ι.1 := by simp [labelFlip]
    rw [hl, hc, hs, labelTime_negLabel, labelTime_flipLabel, hf1, h2]
    simp only [if_true, Complex.conj_conj]
    exact h1

theorem keyRow_fields_of {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    (W : RowEntry D R T) (hHT : HarmonicTraceIndependence D) (hFl : KeyPlaneFlip D T.keyLayout)
    (horder : T.keyLayout.order = D.azimuthOrder) (hG : T.FieldGaugeHolds) (hchk : T.gauge.Conditions)
    (hRK : T.RealKeyConditions) (hT : T.GaugeRowTransport W.rowVec) (hcc : CellCalculusConditions D R)
    {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) (K : Fin D.mesh.count)
    (d : CellVar D.mesh K (R.layouts K)) (rd : KeyEvaluation) (re im : Option T.Slaved)
    (hw : W.KeyRow K d rd re im) :
    W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) :=
  keyRow_fields W (keyHeadMatch_holds hHT hcc horder) (keyEvalTransfer_holds hFl) hG hchk hRK hT hcc hfh κ K d rd
    re im hw

theorem splitRow_fields_of {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} {T : TreeEntry D R}
    (W : RowEntry D R T) (hHT : HarmonicTraceIndependence D) (hFl : KeyPlaneFlip D T.keyLayout)
    (hA : KeySplitAdditive D T.keyLayout) (horder : T.keyLayout.order = D.azimuthOrder) (hG : T.FieldGaugeHolds)
    (hchk : T.gauge.Conditions) (hRK : T.RealKeyConditions) (hT : T.GaugeRowTransport W.rowVec)
    (hcc : CellCalculusConditions D R) {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g Pg : ℝ → Space → Space}
    (hfh : GaugeKey.fieldHyp D q v G H g Pg) (κ : Fin k → ℝ) (K : Fin D.mesh.count)
    (d : CellVar D.mesh K (R.layouts K)) (w : SplitChoice T) (hw : W.SplitRow K d w)
    (hflux : ∀ {rad : Bool} {lev lo hi : ℝ} {t : ℕ → ℕ → ℝ} {deg : ℕ},
      sideKeyGeom (keyOf ((R.layouts K).layout d.1.1) d.2) = some (rad, lev, lo, hi, t, deg) →
      ∀ j, w.flux j = true →
        (haveI := T.slavedFintype; ∑ a, RowEntry.tileFlux rad lev w j a * ((T.fieldData v G H Pg κ a : ℝ) : ℂ))
          = keyHarmonic T.keyLayout (labelTime d.1.1) v G H Pg
              (retileKey (w.tlo j) (w.thi j) (w.ttest j) 0 (keyOf ((R.layouts K).layout d.1.1) d.2))) :
    W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) :=
  splitRow_fields W (keyHeadMatch_holds hHT hcc horder) (keyEvalTransfer_holds hFl) hA hG hchk hRK hT hcc hfh κ K d
    w hw hflux

end KeyData

end Assembly

end CertCell

end Breakdown
