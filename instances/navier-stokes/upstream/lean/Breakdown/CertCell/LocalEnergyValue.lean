import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.FracCell.EnergyAssembly

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open CellCert.CellEnergy.EnergyAssemblyInternal

namespace Internal.EnergyValue

theorem modeSum_unit (a b : Fin 3) (F : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) : modeSum (unitArray a b) F = F a b := by
  funext p
  exact unit_sum a b (fun a' b' => F a' b' p)

theorem modeSum_curl (i : Fin 3) (F : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) :
    modeSum (curlArray i) F = fun p => curlComp (fun a b => F a b p) i := by
  funext p
  exact curl_sum i (fun a b => F a b p)

theorem component_value (hR : LocalComponentRadialStatement) (hH : LocalComponentHeightStatement)
    (hA : LocalComponentAngularStatement) {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (m : ℕ) (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ) (hK : IsCellBox K) (hB : IsCellBases K B)
    (hq : 1 ≤ q) (hQ : q + 1 ≤ Q) (hM : IsModeData m K B I F T u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) :
    quadFormValue (componentForm K B I m n C) u =
      K.radialEnergy Q q (modeSum C (F n)) (modeSum C (fun a b => T n a b 0))
        + K.heightEnergy Q q (modeSum C (F n)) (modeSum C (fun a b => T n a b 2))
        + K.angularEnergy Q (modeSum C (fun a b p => (p.1 : ℂ) * T n a b 1 p)) := by
  rw [← hR m K B I F T u hK hB hq hQ hM n C, ← hH m K B I F T u hK hB hq hQ hM n C,
    ← hA m K B I F T u hK hB hq hQ hM n C]
  unfold componentForm
  simp only [value_add]
  ring

end Internal.EnergyValue

open Internal.EnergyValue in
theorem localEnergyValue_of (hR : LocalComponentRadialStatement) (hH : LocalComponentHeightStatement)
    (hA : LocalComponentAngularStatement) : LocalEnergyValueStatement := by
  intro D _ _ modes Q q m K B I F T u hK hB hq hQ hM ew vw
  unfold energyForm
  rw [value_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [value_sub, value_add, value_smul, value_smul, value_smul, value_sum, value_sum]
  simp only [value_sum, component_value hR hH hA m K B I F T u hK hB hq hQ hM, modeSum_unit, modeSum_curl,
    zero_mul, sub_zero]

end Breakdown.CertCell.LocalField
