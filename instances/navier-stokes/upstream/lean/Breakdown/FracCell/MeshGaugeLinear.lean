import Breakdown.FracCell.MeshGaugeLinearParts

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshGaugeLinearInternal

private theorem list_lin {ι : Type} {k : ℕ} (l : List ι) (f : ι → FieldTuple k → ℝ) (x y z : FieldTuple k) (a b : ℝ)
    (h : ∀ i ∈ l, f i z = a * f i x + b * f i y) :
    (l.map (fun i => f i z)).sum = a * (l.map (fun i => f i x)).sum + b * (l.map (fun i => f i y)).sum := by
  induction l with
  | nil => simp
  | cons i t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]
    ring

theorem classValue_linear {α : ℝ} {k N : ℕ} {c : FracCellData k N} {Sp : CellSplit k N} {M : MeshData k N Sp} (hM : IsMeshData α c Sp M)
    (hG : ∀ K, IsFaceSegment (M.coords K).layout.gauge ∧ (M.coords K).layout.gauge.testCoef 0 0 ≠ 0 ∧
      0 ≤ (M.coords K).layout.gauge.lo ∧ ((M.coords K).layout.gauge.radial →
        (M.coords K).layout.gauge.level ≠ 0 ∧ 0 ≤ min (M.coords K).layout.gauge.level (M.coords K).layout.gauge.other))
    (x y : FieldTuple k) (a b : ℝ) (hx : IsAdmissible c x) (hy : IsAdmissible c y) (cl : Fin M.classCount) :
    M.classValue (a • x + b • y) cl = a * M.classValue x cl + b * M.classValue y cl := by
  have hP : ∀ K (i : Fin (M.coords K).layout.presCount × Fin (M.coords K).layout.degSide),
      (M.coords K).layout.pressureDatumValue (a • x + b • y) i =
        a * (M.coords K).layout.pressureDatumValue x i + b * (M.coords K).layout.pressureDatumValue y i :=
    fun K i => MeshGaugeLinearParts.pressureDatum_linear (c := c) (M.coords K).layout
      (hM.gauge_specs K).zero_mode (hG K) (hM.segments_valid K).2 (hM.radial_pressure_segments K) i x y a b hx hy
  have hJ : ∀ K, (M.coords K).layout.gaugeJump (M.coords K).gaugeSpec (a • x + b • y) =
      a * (M.coords K).layout.gaugeJump (M.coords K).gaugeSpec x +
        b * (M.coords K).layout.gaugeJump (M.coords K).gaugeSpec y := by
    intro K
    unfold CellLayout.gaugeJump
    cases (M.coords K).gaugeSpec.edge with
    | none => simp
    | some e =>
      simp only
      rw [hP K e]
      ring
  have hR : M.rootValue (a • x + b • y) cl = a * M.rootValue x cl + b * M.rootValue y cl := by
    unfold MeshData.rootValue
    rw [hP]
    ring
  unfold MeshData.classValue
  rw [hR]
  have hS := list_lin (M.classPath cl)
    (fun e z => if e.2 then (M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec z
      else -(M.coords e.1).layout.gaugeJump (M.coords e.1).gaugeSpec z) x y (a • x + b • y) a b
    (fun e _ => by
      by_cases h : e.2
      · rw [if_pos h, if_pos h, if_pos h]
        exact hJ e.1
      · rw [if_neg h, if_neg h, if_neg h, hJ e.1]
        ring)
  rw [hS]
  ring

end MeshGaugeLinearInternal

theorem meshGaugeLinear_of_gauge : ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (Sp : CellSplit k N) (M : MeshData k N Sp), IsMeshData α c Sp M →
      (∀ K, IsFaceSegment (M.coords K).layout.gauge ∧ (M.coords K).layout.gauge.testCoef 0 0 ≠ 0 ∧
        0 ≤ (M.coords K).layout.gauge.lo ∧ ((M.coords K).layout.gauge.radial →
          (M.coords K).layout.gauge.level ≠ 0 ∧
            0 ≤ min (M.coords K).layout.gauge.level (M.coords K).layout.gauge.other)) →
      ∀ K (x y : FieldTuple k) (a b : ℝ), IsAdmissible c x → IsAdmissible c y →
          M.canonicalLeft K (a • x + b • y) = a * M.canonicalLeft K x + b * M.canonicalLeft K y ∧
            M.canonicalRight K (a • x + b • y) = a * M.canonicalRight K x + b * M.canonicalRight K y := by
  intro α _ _ k N c _ Sp M hM hG K x y a b hx hy
  exact ⟨MeshGaugeLinearInternal.classValue_linear hM hG x y a b hx hy _,
    MeshGaugeLinearInternal.classValue_linear hM hG x y a b hx hy _⟩

theorem meshGaugeLinear : MeshGaugeLinearStatement := by
  intro α h1 h2 k N c hc Sp M hM
  exact meshGaugeLinear_of_gauge α h1 h2 c hc Sp M hM hM.gauge_valid

end CellCoordinates

end CellCert

end Breakdown
