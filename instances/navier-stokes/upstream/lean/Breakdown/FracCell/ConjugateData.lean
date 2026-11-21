import Breakdown.FracCell.StCoordsProof

open MeasureTheory Matrix ComplexConjugate

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

namespace ConjugateDataInternal

theorem conj_intervalIntegral (a b : ℝ) (f : ℝ → ℂ) :
    conj (∫ t in a..b, f t) = ∫ t in a..b, conj (f t) := by
  simp only [intervalIntegral, map_sub, integral_conj]

theorem conj_angle (m : ℕ) (n : ℤ) (g : ℝ → ℝ) :
    conj ((1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (g θ : ℂ)) =
    (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m (-n) * θ : ℝ) * Complex.I) * (g θ : ℂ) := by
  rw [map_mul, conj_intervalIntegral]
  congr 1
  · simp [map_ofNat]
  · congr 1
    funext θ
    rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
    congr 2
    simp [azimuth, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]

theorem conj_edgeSign (c o : ℝ) : conj (edgeSign c o) = edgeSign c o := by
  unfold edgeSign
  split_ifs <;> simp

theorem conj_radialStrip (c o lo hi : ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    conj (radialStripMoment c o lo hi F dF t) =
      radialStripMoment c o lo hi (fun p => conj (F p)) (fun p => conj (dF p)) t := by
  simp only [radialStripMoment, map_mul, conj_edgeSign, ← integral_conj, map_add, Complex.conj_ofReal]

theorem conj_heightStrip (c o lo hi : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    conj (heightStripMoment c o lo hi wt F dF t) =
      heightStripMoment c o lo hi wt (fun p => conj (F p)) (fun p => conj (dF p)) t := by
  simp only [heightStripMoment, map_mul, conj_edgeSign, ← integral_conj, map_add, Complex.conj_ofReal]

theorem conj_corner (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) :
    conj (cornerMoment cr orr cz oz F Fr Fz Frz) =
      cornerMoment cr orr cz oz (fun p => conj (F p)) (fun p => conj (Fr p)) (fun p => conj (Fz p))
        (fun p => conj (Frz p)) := by
  simp only [cornerMoment, map_mul, conj_edgeSign, ← integral_conj, map_add, Complex.conj_ofReal]

theorem conj_segMoment (S : FaceSegment) (w : Bool) (F dFr dFz : ℝ × ℝ → ℂ) (d : ℕ) :
    conj (S.moment w F dFr dFz d) =
      S.moment w (fun p => conj (F p)) (fun p => conj (dFr p)) (fun p => conj (dFz p)) d := by
  unfold FaceSegment.moment
  split_ifs <;> first
    | exact conj_radialStrip _ _ _ _ _ _ _
    | exact conj_heightStrip _ _ _ _ _ _ _ _

theorem conj_coef (B : CellBases) (K : CellBox) (F : ℝ × ℝ → ℂ) (j l : ℕ) :
    conj (B.coef K F j l) = B.coef K (fun p => conj (F p)) j l := by
  simp only [CellBases.coef, ← integral_conj, map_mul, Complex.conj_ofReal]

variable (L : CellLayout) {k : ℕ} (x : FieldTuple k)

theorem velMode_neg (n : ℤ) (a : Fin 3) :
    L.velMode (-n) x a = fun p => conj (L.velMode n x a p) := by
  funext p
  simp only [CellLayout.velMode, modeVec]
  rw [conj_angle]

theorem gradModeOf_neg (n : ℤ) (a b : Fin 3) :
    L.gradModeOf (-n) x a b = fun p => conj (L.gradModeOf n x a b p) := by
  funext p
  simp only [CellLayout.gradModeOf, gradMode, modeMat]
  rw [conj_angle]

theorem secondModeOf_neg (n : ℤ) (a b c : Fin 3) :
    L.secondModeOf (-n) x a b c = fun p => conj (L.secondModeOf n x a b c p) := by
  funext p
  simp only [CellLayout.secondModeOf, modeThird]
  rw [conj_angle]

theorem pressureGradMode_neg (n : ℤ) (a : Fin 3) :
    L.pressureGradMode (-n) x a = fun p => conj (L.pressureGradMode n x a p) := by
  funext p
  simp only [CellLayout.pressureGradMode, modeVec]
  rw [conj_angle]

theorem pressMode_neg (n : ℤ) :
    L.pressMode (-n) x = fun p => conj (L.pressMode n x p) := by
  funext p
  simp only [CellLayout.pressMode, presMode]
  rw [conj_angle]

theorem extraValue_neg (n : ℤ) (e : Fin 4) (a : Fin 3) (d : ℕ) :
    L.extraValue (-n) x e a d = conj (L.extraValue n x e a d) := by
  unfold CellLayout.extraValue
  split_ifs <;>
    simp only [conj_radialStrip, conj_heightStrip, velMode_neg, gradModeOf_neg]

end ConjugateDataInternal

open ConjugateDataInternal in
theorem conjugateData_holds : ConjugateDataStatement := by
  intro k N c K S B L hL x _ d
  have hneg : ∀ n : L.modes, ((L.negMode n : L.modes) : ℤ) = -(n : ℤ) := by
    intro n
    simp [CellLayout.negMode, hL.modes_symm n.1 n.2]
  rcases d with i | i | i | i | i | i | c | i
  · simp only [CellLayout.conjDatum, Sum.map_inl, CellLayout.trueData, Sum.elim_inl]
    rw [hneg, conj_coef, gradModeOf_neg]
  · simp only [CellLayout.conjDatum, Sum.map_inl, Sum.map_inr, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [hneg, conj_coef, velMode_neg]
  · simp only [CellLayout.conjDatum, Sum.map_inl, Sum.map_inr, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [hneg, conj_segMoment, velMode_neg, gradModeOf_neg, gradModeOf_neg]
  · simp only [CellLayout.conjDatum, Sum.map_inl, Sum.map_inr, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [hneg]
    split_ifs
    · rw [conj_segMoment, gradModeOf_neg, secondModeOf_neg, secondModeOf_neg]
    · rw [conj_segMoment, gradModeOf_neg, secondModeOf_neg, secondModeOf_neg]
  · simp only [CellLayout.conjDatum, Sum.map_inl, Sum.map_inr, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [hneg, conj_segMoment, pressMode_neg, pressureGradMode_neg, pressureGradMode_neg]
  · simp only [CellLayout.conjDatum, Sum.map_inl, Sum.map_inr, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [hneg, conj_corner, velMode_neg, gradModeOf_neg, gradModeOf_neg, secondModeOf_neg]
  · simp only [CellLayout.conjDatum, Sum.map_inl, Sum.map_inr, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, id]
    rw [conj_heightStrip, ← velMode_neg, ← gradModeOf_neg, neg_zero]
  · simp only [CellLayout.conjDatum, Sum.map_inr, CellLayout.trueData, Sum.elim_inr]
    rw [hneg, extraValue_neg]

end Breakdown.CellCert.CellFormula
