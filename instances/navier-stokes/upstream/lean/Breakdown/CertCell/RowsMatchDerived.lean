import Breakdown.CertCell.AssemblyStatements

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}
  {T : TreeEntry D R}

instance slavedFintypeInst (T : TreeEntry D R) : Fintype T.Slaved := T.slavedFintype

theorem headData_of_not_pres (L : CellLayout) {j : ℕ} (x : CellCert.Assembly.FieldTuple j) (d : L.Datum)
    (h : isPressureDatum L d = false) : headData L x d = L.trueData x d := by
  rcases d with q | q | q | q | q | q | q | q <;> first | rfl | simp [isPressureDatum] at h

theorem headHarmonic_of_not_pres (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (d : L.Datum) (h : isPressureDatum L d = false) :
    headHarmonic L ν v G H Pg d = harmonicData L ν v G H Pg d := by
  unfold headHarmonic harmonicData
  rw [headData_of_not_pres L _ d h, headData_of_not_pres L _ d h]

theorem gaugeDir_of_not_pres (T : TreeEntry D R) (K : Fin D.mesh.count) (c : Fin T.gauge.count)
    (d : CellVar D.mesh K (R.layouts K)) (h : isPressureDatum ((R.layouts K).layout d.1.1) d.2 = false) :
    T.gaugeDir K c (Sum.inl (Sum.inl d)) = 0 := by
  obtain ⟨ι, e⟩ := d
  simp only [TreeEntry.gaugeDir, Sum.elim_inl, GaugeKey.GaugeKeyValues.dir]
  rcases e with q | q | q | q | q | q | q | q <;>
    first
    | (simp [keyOf, GaugeKey.GaugeKeyValues.dirReal]; done)
    | simp [isPressureDatum] at h

namespace RowEntry

variable (W : RowEntry D R T)

open Classical in
theorem rowValue_eq_sum (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (f : T.Slaved → ℝ) :
    W.rowValue K d f = ∑ a, W.rowVec K d a * (f a : ℂ) := by
  unfold rowValue rowVec
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

open Classical in
theorem derived_match (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (rows : Finset ((R.layouts K).layout d.1.1).RelIndex) (mult : ((R.layouts K).layout d.1.1).RelIndex → ℂ)
    (hw : W.DerivedRow K d rows mult) (f : T.Slaved → ℝ) (s : ((R.layouts K).layout d.1.1).Datum → ℂ)
    (hrel : ∑ d', relCoef K d rows mult d' * s d' = 0)
    (hlow : ∀ d', d' ≠ d.2 → relCoef K d rows mult d' ≠ 0 → W.rowValue K ⟨d.1, d'⟩ f = s d') :
    W.rowValue K d f = s d.2 := by
  obtain ⟨h1, -, -, hvec⟩ := hw
  have hsplit : ∑ d', relCoef K d rows mult d' * s d'
      = s d.2 + ∑ d' ∈ Finset.univ.filter (fun d' => d' ≠ d.2), relCoef K d rows mult d' * s d' := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun d' => d' ≠ d.2)]
    have hne : Finset.univ.filter (fun d' => ¬ d' ≠ d.2) = {d.2} := by
      ext d'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, Finset.mem_singleton]
    rw [hne, Finset.sum_singleton, h1, one_mul, add_comm]
  have hlow' : ∀ d' ∈ Finset.univ.filter (fun d' => d' ≠ d.2),
      relCoef K d rows mult d' * W.rowValue K ⟨d.1, d'⟩ f = relCoef K d rows mult d' * s d' := by
    intro d' hd'
    by_cases hz : relCoef K d rows mult d' = 0
    · simp [hz]
    · rw [hlow d' (Finset.mem_filter.1 hd').2 hz]
  rw [W.rowValue_eq_sum, hvec]
  have hexp : ∀ a, (-∑ d' ∈ Finset.univ.filter (fun d' => d' ≠ d.2),
        relCoef K d rows mult d' • W.rowVec K ⟨d.1, d'⟩) a * (f a : ℂ)
      = -∑ d' ∈ Finset.univ.filter (fun d' => d' ≠ d.2),
          relCoef K d rows mult d' * (W.rowVec K ⟨d.1, d'⟩ a * (f a : ℂ)) := by
    intro a
    rw [Pi.neg_apply, Finset.sum_apply, neg_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro d' _
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
  simp only [hexp]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  have hin : ∀ d' ∈ Finset.univ.filter (fun d' => d' ≠ d.2),
      ∑ a, relCoef K d rows mult d' * (W.rowVec K ⟨d.1, d'⟩ a * (f a : ℂ))
        = relCoef K d rows mult d' * s d' := by
    intro d' hd'
    rw [← Finset.mul_sum, ← W.rowValue_eq_sum]
    exact hlow' d' hd'
  rw [Finset.sum_congr rfl hin]
  linear_combination hsplit - hrel

open Classical in
theorem derived_row_fields (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (rows : Finset ((R.layouts K).layout d.1.1).RelIndex) (mult : ((R.layouts K).layout d.1.1).RelIndex → ℂ)
    (hw : W.DerivedRow K d rows mult) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    (hharm : ∀ ρ, ∑ d', ((R.layouts K).layout d.1.1).relationRow ρ d'
      * harmonicData ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg d' = 0)
    (hlow : ∀ d', d' ≠ d.2 → relCoef K d rows mult d' ≠ 0 →
      W.rowValue K ⟨d.1, d'⟩ (T.fieldData v G H Pg κ)
        = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl ⟨d.1, d'⟩))) :
    W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) := by
  have hpres := hw.2.1
  have hterm : ∀ d' : ((R.layouts K).layout d.1.1).Datum,
      relCoef K d rows mult d' * T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl ⟨d.1, d'⟩))
        = relCoef K d rows mult d' * harmonicData ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg d' := by
    intro d'
    by_cases hp : isPressureDatum ((R.layouts K).layout d.1.1) d' = true
    · rw [hpres d' hp, zero_mul, zero_mul]
    · have hp' : isPressureDatum ((R.layouts K).layout d.1.1) d' = false := by simpa using hp
      congr 1
      have hg : ∀ c, T.gaugeDir K c (Sum.inl (Sum.inl ⟨d.1, d'⟩)) = 0 :=
        fun c => gaugeDir_of_not_pres T K c ⟨d.1, d'⟩ hp'
      simp only [TreeEntry.fieldShifted, TreeEntry.fieldHead, Sum.elim_inl, hg, mul_zero,
        Finset.sum_const_zero, add_zero]
      exact headHarmonic_of_not_pres _ _ _ _ _ _ d' hp'
  refine W.derived_match K d rows mult hw (T.fieldData v G H Pg κ)
    (fun d' => T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl ⟨d.1, d'⟩))) ?_ hlow
  rw [Finset.sum_congr rfl (fun d' _ => hterm d')]
  unfold relCoef
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp [hharm]

end RowEntry

end Assembly

end CertCell

end Breakdown
