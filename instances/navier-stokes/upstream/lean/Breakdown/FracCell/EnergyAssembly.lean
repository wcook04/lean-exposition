import Breakdown.FracCell.StEnergyProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

namespace EnergyAssemblyInternal

variable {D : Type} [Fintype D] [DecidableEq D]

theorem value_add (A B : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (A + B) u = quadFormValue A u + quadFormValue B u := by
  unfold quadFormValue
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

theorem value_sub (A B : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (A - B) u = quadFormValue A u - quadFormValue B u := by
  unfold quadFormValue
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

theorem value_smul (r : ℝ) (A : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue ((r : ℂ) • A) u = r * quadFormValue A u := by
  unfold quadFormValue
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

def valueHom (u : D → ℂ) : Matrix D D ℂ →+ ℝ :=
  AddMonoidHom.mk' (fun A => quadFormValue A u) (fun A B => value_add A B u)

theorem value_sum {ι : Type} (s : Finset ι) (f : ι → Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (∑ i ∈ s, f i) u = ∑ i ∈ s, quadFormValue (f i) u :=
  map_sum (valueHom u) f s

theorem unit_sum (a b : Fin 3) (F : Fin 3 → Fin 3 → ℂ) :
    ∑ a' : Fin 3, ∑ b' : Fin 3, unitArray a b a' b' * F a' b' = F a b := by
  fin_cases a <;> fin_cases b <;> simp [unitArray, Fin.sum_univ_three]

theorem curl_sum (i : Fin 3) (F : Fin 3 → Fin 3 → ℂ) :
    ∑ a : Fin 3, ∑ b : Fin 3, curlArray i a b * F a b = curlComp F i := by
  simp only [curlArray, curlComp]
  exact Finset.sum_comm

theorem strain_unit (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) :
    strainField m n G (unitArray a b) = gradMode m n G a b := by
  funext p
  exact unit_sum a b (fun a' b' => gradMode m n G a' b' p)

theorem radial_unit (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b : Fin 3) :
    radialField m n H (unitArray a b) = radialGradMode m n H a b := by
  funext p
  exact unit_sum a b (fun a' b' => radialGradMode m n H a' b' p)

theorem height_unit (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b : Fin 3) :
    heightField m n H (unitArray a b) = heightGradMode m n H a b := by
  funext p
  exact unit_sum a b (fun a' b' => heightGradMode m n H a' b' p)

theorem angular_unit (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b : Fin 3) :
    angularField m n H (unitArray a b) = angularGradMode m n H a b := by
  funext p
  exact unit_sum a b (fun a' b' => angularGradMode m n H a' b' p)

theorem strain_curl (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (i : Fin 3) :
    strainField m n G (curlArray i) = fun p => curlComp (fun a b => gradMode m n G a b p) i := by
  funext p
  exact curl_sum i (fun a b => gradMode m n G a b p)

theorem radial_curl (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (i : Fin 3) :
    radialField m n H (curlArray i) = fun p => curlComp (fun a b => radialGradMode m n H a b p) i := by
  funext p
  exact curl_sum i (fun a b => radialGradMode m n H a b p)

theorem height_curl (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (i : Fin 3) :
    heightField m n H (curlArray i) = fun p => curlComp (fun a b => heightGradMode m n H a b p) i := by
  funext p
  exact curl_sum i (fun a b => heightGradMode m n H a b p)

theorem angular_curl (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (i : Fin 3) :
    angularField m n H (curlArray i) = fun p => curlComp (fun a b => angularGradMode m n H a b p) i := by
  funext p
  exact curl_sum i (fun a b => angularGradMode m n H a b p)

theorem component_value (hR : ComponentRadialStatement) (hH : ComponentHeightStatement)
    (hA : ComponentAngularStatement) (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ)
    (hS : EnergySetting α c K B S I v G H u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) :
    quadFormValue (componentForm K B I c.order n C) u =
      K.radialEnergy Q q (strainField c.order n G C) (radialField c.order n H C)
        + K.heightEnergy Q q (strainField c.order n G C) (heightField c.order n H C)
        + K.angularEnergy Q (angularField c.order n H C) := by
  rw [← hR α c K B S I v G H u hS n C, ← hH α c K B S I v G H u hS n C, ← hA α c K B S I v G H u hS n C]
  unfold componentForm
  simp only [value_add]
  ring

end EnergyAssemblyInternal

open EnergyAssemblyInternal in
theorem energyForm_of (hR : ComponentRadialStatement) (hH : ComponentHeightStatement)
    (hA : ComponentAngularStatement) (hT : TopFormStatement) : EnergyFormStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u hS
  have hm := hS.modes_eq
  have hQ := hS.degHigh_eq
  have hq := hS.degLow_eq
  subst hQ hq hm
  unfold energyForm CellScalars.energyTerm
  rw [value_sum, ← Finset.sum_coe_sort S.resolved]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [value_sub, value_add, value_smul, value_smul, value_smul, value_sum, value_sum,
    hT α c K B S I v G H u hS n]
  simp only [value_sum, component_value hR hH hA α c K B S I v G H u hS, strain_unit, radial_unit,
    height_unit, angular_unit, strain_curl, radial_curl, height_curl, angular_curl]
  rfl

end Breakdown.CellCert.CellEnergy
