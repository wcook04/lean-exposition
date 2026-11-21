import Breakdown.FracCell.StMesh
import Breakdown.FracCell.GaugeShiftOf
import Breakdown.FracCell.AdmissibleLinear

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

def constPressureData (L : CellLayout) : L.Datum → ℝ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
    (Sum.elim (fun i => if (i.1 : ℤ) = 0 then
        L.shiftCoefLeft (i.2.1, i.2.2) + L.shiftCoefRight (i.2.1, i.2.2) else 0)
      (fun _ => 0)))))

def DataAffineStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (g : FaceSegment) (x y : FieldTuple k) (a b : ℝ), IsAdmissible c x → IsAdmissible c y →
      ∃ C : ℝ, ∀ L : CellLayout, L.order = c.order → L.gauge = g →
        (∀ s, IsFaceSegment (L.segment s)) → (∀ s, IsFaceSegment (L.presSegment s)) →
        (∀ s, (L.segment s).radial →
          (L.segment s).level ≠ 0 ∧ 0 ≤ min (L.segment s).level (L.segment s).other) →
        (∀ s, (L.presSegment s).radial →
          (L.presSegment s).level ≠ 0 ∧ 0 ≤ min (L.presSegment s).level (L.presSegment s).other) →
        (∀ cr, (L.corner cr).1 ≠ 0 ∧ (L.cornerOther cr).1 ≠ (L.corner cr).1 ∧
          (L.cornerOther cr).2 ≠ (L.corner cr).2 ∧ 0 ≤ min (L.corner cr).1 (L.cornerOther cr).1) →
        ∀ d, L.trueData (a • x + b • y) d =
          (a : ℂ) * L.trueData x d + (b : ℂ) * L.trueData y d + ((C * constPressureData L d : ℝ) : ℂ)

namespace MeshMomentLinear

theorem list_sum_lin {ι : Type} (l : List ι) (f g h : ι → ℝ) (a b : ℝ)
    (hf : ∀ e ∈ l, f e = a * g e + b * h e) :
    (l.map f).sum = a * (l.map g).sum + b * (l.map h).sum := by
  induction l with
  | nil => simp
  | cons e t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hf e (by simp), ih (fun e' he' => hf e' (by simp [he']))]
    ring

section Layout

variable (L : CellLayout) {k : ℕ} {x y z : FieldTuple k} {a b C : ℝ}

theorem pdv_affine (hz : (0 : ℤ) ∈ L.modes)
    (hT : ∀ d, L.trueData z d =
      (a : ℂ) * L.trueData x d + (b : ℂ) * L.trueData y d + ((C * constPressureData L d : ℝ) : ℂ))
    (i : Fin L.presCount × Fin L.degSide) :
    L.pressureDatumValue z i = a * L.pressureDatumValue x i + b * L.pressureDatumValue y i +
      C * (L.shiftCoefLeft i + L.shiftCoefRight i) := by
  obtain ⟨s, j⟩ := i
  rw [GaugeShiftOf.Internal.pdv_eq L hz, GaugeShiftOf.Internal.pdv_eq L hz,
    GaugeShiftOf.Internal.pdv_eq L hz, hT]
  simp [constPressureData, CellDatum.sidePressure, Complex.add_re, Complex.mul_re]

theorem jump_linear (sp : GaugeSpec L) (hsp : IsGaugeSpec L sp)
    (hT : ∀ d, L.trueData z d =
      (a : ℂ) * L.trueData x d + (b : ℂ) * L.trueData y d + ((C * constPressureData L d : ℝ) : ℂ)) :
    L.gaugeJump sp z = a * L.gaugeJump sp x + b * L.gaugeJump sp y := by
  unfold CellLayout.gaugeJump
  rcases he : sp.edge with _ | e
  · simp
  · simp only
    have hb := hsp.edge_balanced e he
    rw [pdv_affine L hsp.zero_mode hT e, hb]
    ring

theorem shifted_affine (left right : FieldTuple k → ℝ)
    (hl : left z = a * left x + b * left y - C) (hr : right z = a * right x + b * right y - C)
    (hT : ∀ d, L.trueData z d =
      (a : ℂ) * L.trueData x d + (b : ℂ) * L.trueData y d + ((C * constPressureData L d : ℝ) : ℂ))
    (d : L.Datum) :
    L.shiftedData (L.gaugeShiftOf left right) z d =
      (a : ℂ) * L.shiftedData (L.gaugeShiftOf left right) x d +
        (b : ℂ) * L.shiftedData (L.gaugeShiftOf left right) y d := by
  unfold CellLayout.shiftedData
  rw [hT d]
  rcases d with i | i | i | i | ⟨n, s, j⟩ | i | i | i
  all_goals try (simp [CellLayout.pressureShift, constPressureData]; done)
  by_cases hn : (n : ℤ) = 0
  · have e1 := GaugeShiftOf.Internal.shift_eq L left right z n s j hn
    have e2 := GaugeShiftOf.Internal.shift_eq L left right x n s j hn
    have e3 := GaugeShiftOf.Internal.shift_eq L left right y n s j hn
    simp only [CellDatum.sidePressure] at e1 e2 e3
    rw [e1, e2, e3, hl, hr]
    simp only [constPressureData, Sum.elim_inl, Sum.elim_inr, if_pos hn]
    push_cast
    ring
  · simp [CellLayout.pressureShift, constPressureData, hn]

end Layout

section Mesh

variable {k N : ℕ} {Sp : CellSplit k N} (M : MeshData k N Sp) {x y z : FieldTuple k} {a b C : ℝ}

theorem classValue_affine {α : ℝ} {c : FracCellData k N} (hM : IsMeshData α c Sp M)
    (hT : ∀ K d, (M.coords K).layout.trueData z d = (a : ℂ) * (M.coords K).layout.trueData x d +
      (b : ℂ) * (M.coords K).layout.trueData y d + ((C * constPressureData (M.coords K).layout d : ℝ) : ℂ))
    (cl : Fin M.classCount) :
    M.classValue z cl = a * M.classValue x cl + b * M.classValue y cl - C := by
  unfold MeshData.classValue
  have hroot : M.rootValue z cl = a * M.rootValue x cl + b * M.rootValue y cl - C := by
    have hz := (hM.gauge_specs (M.classRoot cl)).zero_mode
    have hrc := hM.root_cells cl
    unfold MeshData.rootValue
    rw [pdv_affine _ hz (hT (M.classRoot cl))]
    cases hs : M.classRootSide cl
    · obtain ⟨hne, h0⟩ := hrc.2.2.2 hs
      simp only [Bool.false_eq_true, if_false]
      rw [h0]
      field_simp
      ring
    · obtain ⟨hne, h0⟩ := hrc.2.2.1 hs
      simp only [if_true]
      rw [h0]
      field_simp
      ring
  have hpath := list_sum_lin (M.classPath cl)
    (fun e => if e.2 then (M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec z
      else -(M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec z)
    (fun e => if e.2 then (M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec x
      else -(M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec x)
    (fun e => if e.2 then (M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec y
      else -(M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec y) a b (by
      rintro ⟨K', bb⟩ _
      have hj := jump_linear _ _ (hM.gauge_specs K') (hT K')
      cases bb
      · simp only [Bool.false_eq_true, if_false]
        rw [hj]; ring
      · simp only [if_true]
        exact hj)
  rw [hroot, hpath]
  ring

theorem localValue_affine {α : ℝ} {c : FracCellData k N} (hM : IsMeshData α c Sp M)
    (hT : ∀ K d, (M.coords K).layout.trueData z d = (a : ℂ) * (M.coords K).layout.trueData x d +
      (b : ℂ) * (M.coords K).layout.trueData y d + ((C * constPressureData (M.coords K).layout d : ℝ) : ℂ))
    (K : Fin Sp.cellCount) (j : Fin (systemSkeletonCoords (M.coords K).layout (M.coords K).param).card) :
    M.localValue c K z j = a * M.localValue c K x j + b * M.localValue c K y j := by
  have hl : M.canonicalLeft K z = a * M.canonicalLeft K x + b * M.canonicalLeft K y - C :=
    classValue_affine M hM hT _
  have hr : M.canonicalRight K z = a * M.canonicalRight K x + b * M.canonicalRight K y - C :=
    classValue_affine M hM hT _
  have hs := shifted_affine (M.coords K).layout (M.canonicalLeft K) (M.canonicalRight K) hl hr (hT K)
  unfold MeshData.localValue CellLayout.realPart
  rw [hs]
  split_ifs <;> simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im] <;> ring

theorem base_affine (hT : DataAffineStatement) {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {c : FracCellData k N} (hc : IsFormData α c) (hM : IsMeshData α c Sp M)
    (x y : FieldTuple k) (a b : ℝ) (hx : IsAdmissible c x) (hy : IsAdmissible c y) (i : Fin Sp.slots) :
    M.baseMoment c (a • x + b • y) i = a * M.baseMoment c x i + b * M.baseMoment c y i := by
  unfold MeshData.baseMoment
  split_ifs with hk
  · simp
  · obtain ⟨C, hC⟩ := hT α hα₁ hα₂ c hc (M.coords (M.ownerCell i)).layout.gauge x y a b hx hy
    have hT' : ∀ K d, (M.coords K).layout.trueData (a • x + b • y) d =
        (a : ℂ) * (M.coords K).layout.trueData x d + (b : ℂ) * (M.coords K).layout.trueData y d +
          ((C * constPressureData (M.coords K).layout d : ℝ) : ℂ) := fun K =>
      hC _ ((hM.same_order K).trans rfl) (hM.same_gauge K _) (hM.segments_valid K).1 (hM.segments_valid K).2
        (hM.radial_segments K) (hM.radial_pressure_segments K) (hM.corners_valid K)
    exact localValue_affine M hM hT' _ _

theorem moment_affine (hT : DataAffineStatement) {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {c : FracCellData k N} (hc : IsFormData α c) (hM : IsMeshData α c Sp M)
    (x y : FieldTuple k) (a b : ℝ) (hx : IsAdmissible c x) (hy : IsAdmissible c y) :
    M.canonicalMoment c (a • x + b • y) = a • M.canonicalMoment c x + b • M.canonicalMoment c y := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  unfold MeshData.canonicalMoment
  split_ifs with hd
  · exact list_sum_lin _ _ _ _ a b (fun p _ => by
      rw [base_affine M hT hα₁ hα₂ hc hM x y a b hx hy p.1]
      ring)
  · exact base_affine M hT hα₁ hα₂ hc hM x y a b hx hy i

end Mesh

end MeshMomentLinear

open MeshMomentLinear in
theorem meshMomentLinear (h : MeshGaugeLinearStatement) (hT : DataAffineStatement) :
    MeshMomentLinearStatement := by
  intro α hα₁ hα₂ k N c hc Sp M hM
  have h0 : IsAdmissible c 0 := (admissibleLinear c).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := moment_affine M hT hα₁ hα₂ hc hM 0 0 0 0 h0 h0
    simpa using e
  · intro x x' hx hx'
    have e := moment_affine M hT hα₁ hα₂ hc hM x x' 1 1 hx hx'
    simpa using e
  · intro r x hx
    have e := moment_affine M hT hα₁ hα₂ hc hM x x r 0 hx hx
    simpa using e
  · intro x _ a
    have hnd : ¬ M.IsDelaySlot (Sp.kappaSlot a) := fun ⟨j, hj⟩ => hM.delay_not_kappa j a hj
    have hex : ∃ a', Sp.kappaSlot a' = Sp.kappaSlot a := ⟨a, rfl⟩
    simp only [MeshData.canonicalMoment, hnd, if_false, MeshData.baseMoment, dif_pos hex]
    rw [hM.kappa_injective hex.choose_spec]

end CellCoordinates

end CellCert

end Breakdown
