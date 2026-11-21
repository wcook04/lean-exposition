import Breakdown.CertCell.EnergyLeafBoundForm

open MeasureTheory Matrix

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace EnergyLeafInternal

theorem value_add {X : Type} [Fintype X] (A B : Matrix X X ℂ) (u : X → ℂ) :
    quadFormValue (A + B) u = quadFormValue A u + quadFormValue B u := by
  unfold quadFormValue
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

theorem value_fromBlocks {X Y : Type} [Fintype X] [Fintype Y] (A : Matrix X X ℂ) (x : X → ℂ) (y : Y → ℂ) :
    quadFormValue (Matrix.fromBlocks A (0 : Matrix X Y ℂ) (0 : Matrix Y X ℂ) (0 : Matrix Y Y ℂ)) (Sum.elim x y)
      = quadFormValue A x := by
  unfold quadFormValue
  rw [Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, add_zero]
  simp only [dotProduct, Fintype.sum_sum_type, Pi.star_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero]

theorem mulVec_blockDiagonal' {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, Fintype (X i)]
    (M : (i : ι) → Matrix (X i) (X i) ℂ) (x : (Σ i, X i) → ℂ) (i : ι) (a : X i) :
    (Matrix.blockDiagonal' M *ᵥ x) ⟨i, a⟩ = (M i *ᵥ fun b => x ⟨i, b⟩) a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j _ hj
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne M a b (Ne.symm hj), zero_mul]
  · simp

theorem value_blockDiagonal' {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, Fintype (X i)]
    (M : (i : ι) → Matrix (X i) (X i) ℂ) (x : (Σ i, X i) → ℂ) :
    quadFormValue (Matrix.blockDiagonal' M) x = ∑ i, quadFormValue (M i) (fun b => x ⟨i, b⟩) := by
  unfold quadFormValue
  rw [← Complex.re_sum]
  congr 1
  simp only [dotProduct]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mulVec_blockDiagonal']
  rfl

theorem lineWeight_mul_rHat (K : CellBox) (p : ℝ × ℝ) : K.lineWeight p.1 * CellScalars.rHat K p = p.1 := by
  unfold CellScalars.rHat CellBox.lineWeight
  by_cases h : K.r₁ = 0
  · simp only [h, if_true]
    by_cases hp : p.1 = 0
    · simp [hp]
    · field_simp
  · simp [h]

end EnergyLeafInternal

namespace EnergyLeafInternal

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem modeBlock_le (h0 : HarmonicEnergyFormValueStatement) (h1 : LabelResolvedEnergyStatement)
    (h2 : LowSlotFormValueStatement) (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (hR : CellCalculusConditions D R) (K : Fin D.mesh.count) (q : Fin k → ℝ) (hq : q ∈ D.cert.params)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : IsPeriodicSecondOrder v G H)
    (Pg : ℝ → Space → Space) (hPg : IsPeriodicPressure Pg) (ι : ℤ × ℤ) (hι : ι ∈ D.mesh.resolved K) :
    quadFormValue (modeBlockForm D R K ⟨ι, hι⟩) (modeData (R.layouts K) ι v G H Pg)
      ≤ (R.leaves K).hessFloor ι * ((∫ p in (D.mesh.box K).rect, p.1 * slopeSq D.azimuthOrder ι H p)
            - labelStrainTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H)
          + (R.leaves K).curlHessFloor ι * ((∫ p in (D.mesh.box K).rect, p.1 * curlSlopeSq D.azimuthOrder ι H p)
            - labelVorticityTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H)
          + ∑ n : ((R.layouts K).layout ι).modes,
              (∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
                matrixSesq ((R.leaves K).localMatrix ι p)
                  (pairVec (lowStrainOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · · p)
                    (lowVelocityOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · p))
                  (pairVec (lowStrainOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · · p)
                    (lowVelocityOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · p))).re := by
  have hlay := (hR.layouts_valid K).layout_valid ι hι
  obtain ⟨c, S, _, _, hL⟩ := id hlay
  have hK : IsCellBox (D.mesh.box K) := hL.box_valid
  have hbox : ((R.layouts K).layout ι).box = D.mesh.box K := hL.box_eq
  have hT := hR.leaves_valid K q hq
  have hax : (D.mesh.box K).IsAxis → ι.1 = 0 := fun h => hR.axis_modes K h ι hι
  have hE := h1 (D.mesh.box K) hK D.azimuthOrder ((R.layouts K).layout ι).degCoef
    ((R.layouts K).layout ι).degSide v G H hv ι hax
  obtain ⟨hmeas, Cb, hCb⟩ := hT.matrix_regular ι hι
  have hbd : ∃ C : ℝ, ∀ p ∈ ((R.layouts K).layout ι).box.rect, ∀ i j, ‖(R.leaves K).localMatrix ι p i j‖ ≤ C :=
    ⟨Cb, fun p hp => hCb p (hbox ▸ hp)⟩
  have hlow := h2 ((R.layouts K).layout ι) ((R.leaves K).localMatrix ι) (modeData (R.layouts K) ι v G H Pg)
    hmeas hbd (hbox ▸ hK)
  have hen := h0 D.azimuthOrder (D.mesh.box K) (R.layouts K).bases ι ((R.layouts K).layout ι) hlay hax v G H Pg
    hv hPg ((R.leaves K).hessFloor ι) ((R.leaves K).curlHessFloor ι)
  unfold modeBlockForm
  rw [value_add]
  change quadFormValue (energyForm (D.mesh.box K) (R.layouts K).bases (layoutIndex ((R.layouts K).layout ι))
      D.azimuthOrder (fun _ => (R.leaves K).hessFloor ι) (fun _ => (R.leaves K).curlHessFloor ι) (fun _ => 0))
      (harmonicData ((R.layouts K).layout ι) (labelTime ι) v G H Pg) + _ ≤ _
  rw [hen, hlow, hbox]
  simp only [lineWeight_mul_rHat]
  have he : 0 ≤ (R.leaves K).hessFloor ι := (hT.hessFloor_pos ι hι).le
  have hw : 0 ≤ (R.leaves K).curlHessFloor ι := hT.curlHessFloor_nonneg ι hι
  have a1 := mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mpr hE.1) he
  have a2 := mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mpr hE.2) hw
  linarith

end EnergyLeafInternal

open EnergyLeafInternal in
theorem energyLeafBound_of_periodic (h0 : HarmonicEnergyFormValueStatement) (h1 : LabelResolvedEnergyStatement)
    (h2 : LowSlotFormValueStatement)
    (hP : ∀ Γ P v G H g, IsPerturbation Γ P v G H g → IsPeriodicSecondOrder v G H) :
    EnergyLeafBoundStatement := by
  intro k C nE nM D R hR K q hq v G H g hpert Pg hPg κ ζ η
  have hv := hP _ _ v G H g hpert
  unfold energyLeafForm cellState
  rw [value_fromBlocks, value_fromBlocks, value_blockDiagonal']
  unfold energyBudget
  rw [← Finset.sum_coe_sort (D.mesh.resolved K)]
  exact Finset.sum_le_sum fun ι _ => modeBlock_le h0 h1 h2 D R hR K q hq v G H hv Pg hPg ι.1 ι.2

end CellCalculus

end CertCell

end Breakdown
