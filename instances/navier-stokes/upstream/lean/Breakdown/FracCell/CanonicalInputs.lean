import Breakdown.FracCell.StFormulaProof
import Breakdown.FracCell.StEnergyProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

namespace CanonicalInputs.Internal

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

theorem moment_zero (s t : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (cf : ℕ → ℕ → ℝ)
    (hlead : ∀ j, cf j j ≠ 0)
    (horth : ∀ j j', ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) *
      (∑ i ∈ Finset.range (j' + 1), cf j' i * r ^ i) = if j = j' then 1 else 0) (j : ℕ) :
    ∀ a, a < j → ∫ r in Set.Icc s t, w r * r ^ a * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro haj
    have h0 := horth a j
    rw [if_neg (ne_of_lt haj)] at h0
    have hexp : ∀ r, w r * (∑ i ∈ Finset.range (a + 1), cf a i * r ^ i) *
        (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) =
        (∑ i ∈ Finset.range a, cf a i * (w r * r ^ i * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i))) +
          cf a a * (w r * r ^ a * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i)) := by
      intro r
      rw [Finset.sum_range_succ, mul_add, add_mul]
      congr 1
      · rw [Finset.mul_sum (s := Finset.range a), Finset.sum_mul (s := Finset.range a)]
        apply Finset.sum_congr rfl
        intro i _
        ring
      · ring
    simp_rw [hexp] at h0
    have hc : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f (Set.Icc s t) := fun f hf => hf.integrableOn_Icc
    rw [integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      integral_finsetSum _ (fun i _ => hc _ (by fun_prop)), integral_const_mul] at h0
    have hz : ∑ i ∈ Finset.range a, ∫ r in Set.Icc s t,
        cf a i * (w r * r ^ i * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [integral_const_mul, ih i (Finset.mem_range.mp hi) (lt_trans (Finset.mem_range.mp hi) haj), mul_zero]
    rw [hz, zero_add] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hlead a)

theorem lineWeight_continuous (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs <;> fun_prop

theorem radialPoly_continuous (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  fun_prop

theorem heightPoly_continuous (B : CellBases) (j : ℕ) : Continuous (B.heightPoly j) := by
  unfold CellBases.heightPoly
  fun_prop

theorem coef_poly_zero (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (d : ℕ) (P : ℝ × ℝ → ℂ)
    (hP : P ∈ polyFn d d) (j l : ℕ) (h : d < j ∨ d < l) : B.coef K P j l = 0 := by
  obtain ⟨c, hc⟩ := hP
  have hrad : ∀ a, a < j → ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * r ^ a * B.radialPoly j r = 0 :=
    moment_zero K.r₁ K.r₂ K.lineWeight (lineWeight_continuous K) B.radialCoef
      (fun j => (hB.radial_leading j).ne') hB.radial_orthonormal j
  have hhei : ∀ a, a < l → ∫ z in Set.Icc K.z₁ K.z₂, z ^ a * B.heightPoly l z = 0 := by
    intro a ha
    have := moment_zero K.z₁ K.z₂ (fun _ => 1) continuous_const B.heightCoef
      (fun j => (hB.height_leading j).ne') (fun j j' => by
        have h := hB.height_orthonormal j j'
        simp only [CellBases.heightPoly] at h
        simpa only [one_mul] using h) l a ha
    simp only [one_mul] at this
    exact this
  have hpt : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * P p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) =
      ∑ j' : Fin (d + 1), ∑ l' : Fin (d + 1), c j' l' *
        (((K.lineWeight p.1 * p.1 ^ (j' : ℕ) * B.radialPoly j p.1 : ℝ) : ℂ) *
          ((p.2 ^ (l' : ℕ) * B.heightPoly l p.2 : ℝ) : ℂ)) := by
    intro p
    rw [hc p]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j' _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l' _
    ring
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hw := lineWeight_continuous K
  have hr := radialPoly_continuous B j
  have hh := heightPoly_continuous B l
  have hint : ∀ f : ℝ × ℝ → ℂ, Continuous f → Integrable f (volume.restrict K.rect) :=
    fun f hf => hf.continuousOn.integrableOn_compact hcomp
  unfold CellBases.coef
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun j' _ => hint _ (by fun_prop))]
  apply Finset.sum_eq_zero
  intro j' _
  rw [integral_finsetSum _ (fun l' _ => hint _ (by fun_prop))]
  apply Finset.sum_eq_zero
  intro l' _
  rw [integral_const_mul]
  unfold CellBox.rect
  rw [Measure.volume_eq_prod, setIntegral_prod_mul
    (fun r : ℝ => ((K.lineWeight r * r ^ (j' : ℕ) * B.radialPoly j r : ℝ) : ℂ))
    (fun z : ℝ => ((z ^ (l' : ℕ) * B.heightPoly l z : ℝ) : ℂ))]
  rw [integral_complex_ofReal, integral_complex_ofReal]
  rcases h with h | h
  · rw [hrad j' (by omega)]
    simp
  · rw [hhei l' (by omega)]
    simp

theorem proj_mem (K : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : K.proj d d' F ∈ polyFn d d' := by
  unfold CellBox.proj
  split_ifs with h
  · exact h.choose_spec.1
  · exact ⟨0, fun p => by simp⟩


theorem pressureShift_low (L : CellLayout) {k : ℕ} (g : GaugeShift k) (x : FieldTuple k)
    (i : ℤ × Fin 3 × Fin 4 × ℕ × ℕ) (d : L.Datum) (h : L.lowEntry i = some d) : L.pressureShift g x d = 0 := by
  unfold CellLayout.lowEntry at h
  split_ifs at h
  · obtain rfl := Option.some.inj h
    rfl
  · obtain rfl := Option.some.inj h
    rfl

theorem lowEntry_agree_of (hLow : LowEntryStatement) {k N : ℕ} (c : FracCellData k N) (K : CellBox)
    (S : CellScalars) (B : CellBases) (L : CellLayout) (hL : IsCellLayout c K S B L) (g : GaugeShift k)
    (x : FieldTuple k) (hx : IsAdmissible c x) (i : LowSupp S) :
    (L.lowEntry i.1).elim 0 (L.shiftedData g x) = lowCoef c K S B x i.1 := by
  cases h : L.lowEntry i.1 with
  | some d =>
    simp only [Option.elim]
    rw [CellLayout.shiftedData, pressureShift_low L g x i.1 d h, add_zero]
    exact hLow c K S B L hL x hx i.1 d h
  | none =>
    simp only [Option.elim]
    obtain ⟨⟨n, a, b, j, l⟩, hi⟩ := i
    simp only [lowSupport, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and] at hi
    obtain ⟨hn, hj, hl⟩ := hi
    have hn' : n ∈ L.modes := hL.modes_eq ▸ hn
    have hQ := hL.degCoef_eq
    have h1 := hL.degSide_pos
    have h2 := hL.degSide_le
    unfold CellLayout.lowEntry at h
    rw [dif_pos hn'] at h
    by_cases hb : b.val < 3
    · rw [dif_pos hb, dif_pos (by constructor <;> simp <;> omega)] at h
      exact absurd h (by simp)
    · rw [dif_neg hb] at h
      split_ifs at h with hjl
      simp only at hjl
      show _ = lowCoef c K S B x (n, a, b, j, l)
      unfold lowCoef
      rw [dif_neg hb]
      symm
      apply coef_poly_zero K B hL.bases_valid (S.degHigh - 1)
      · exact proj_mem K _ _ _
      · show S.degHigh - 1 < j ∨ S.degHigh - 1 < l
        omega

theorem param_congr {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D) (u v : D → ℂ)
    (h : ∀ d, d ∉ P.solvedSet → u d = v d) : P.param u = P.param v := by
  have hf : P.freePart u = P.freePart v := by
    funext d
    unfold ParamData.freePart
    split_ifs with hd
    · rfl
    · exact h d hd
  unfold ParamData.param
  rw [hf]

theorem freePart_add {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D) (u v : D → ℂ) :
    P.freePart (u + v) = P.freePart u + P.freePart v := by
  funext d
  simp only [ParamData.freePart, Pi.add_apply]
  split_ifs <;> simp

theorem freePart_smul {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D) (r : ℝ) (u : D → ℂ) :
    P.freePart (r • u) = r • P.freePart u := by
  funext d
  simp only [ParamData.freePart, Pi.smul_apply]
  split_ifs <;> simp

theorem param_add {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D) (u v : D → ℂ) :
    P.param (u + v) = P.param u + P.param v := by
  unfold ParamData.param
  rw [freePart_add, Matrix.mulVec_add, Matrix.mulVec_add]
  simp only [Pi.add_apply, Pi.single_add, Finset.sum_add_distrib]
  abel

theorem param_smul {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D) (r : ℝ) (u : D → ℂ) :
    P.param (r • u) = r • P.param u := by
  unfold ParamData.param
  rw [freePart_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_sub, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.single_smul']

theorem realCoord_add (L : CellLayout) (w w' : L.Datum × Fin 2 → ℝ) :
    L.realCoord (w + w') = L.realCoord w + L.realCoord w' := by
  funext d
  simp only [CellLayout.realCoord, Pi.add_apply]
  push_cast
  ring

theorem realCoord_smul (L : CellLayout) (r : ℝ) (w : L.Datum × Fin 2 → ℝ) :
    L.realCoord (r • w) = r • L.realCoord w := by
  funext d
  simp only [CellLayout.realCoord, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem embed_add (L : CellLayout) (P : ParamData L.Datum)
    (w w' : Fin (skeletonCoords L P).card ⊕ Fin (interiorCoords L P).card → ℝ) :
    embedCoords L P (w + w') = embedCoords L P w + embedCoords L P w' := by
  funext p
  simp only [embedCoords, Pi.add_apply]
  split_ifs <;> simp

theorem embed_smul (L : CellLayout) (P : ParamData L.Datum) (r : ℝ)
    (w : Fin (skeletonCoords L P).card ⊕ Fin (interiorCoords L P).card → ℝ) :
    embedCoords L P (r • w) = r • embedCoords L P w := by
  funext p
  simp only [embedCoords, Pi.smul_apply]
  split_ifs <;> simp

theorem coord_linear_of (L : CellLayout) (P : ParamData L.Datum) :
    IsLinearMap ℝ (fun w => P.param (L.realCoord (embedCoords L P w))) := by
  refine ⟨fun w w' => ?_, fun r w => ?_⟩
  · simp only [embed_add, realCoord_add, param_add]
  · simp only [embed_smul, realCoord_smul, param_smul]

theorem data_represents_of {k : ℕ} (L : CellLayout) (P : ParamData L.Datum) (g : GaugeShift k)
    (x : FieldTuple k) (hP : P.param (L.shiftedData g x) = L.shiftedData g x) :
    P.param (L.realCoord (embedCoords L P (Sum.elim
      (fun i => L.realPart (L.shiftedData g x) ((skeletonCoords L P).equivFin.symm i).1)
      (fun i => L.realPart (L.shiftedData g x) ((interiorCoords L P).equivFin.symm i).1)))) =
      L.shiftedData g x := by
  conv_rhs => rw [← hP]
  apply param_congr
  intro d hd
  have he : ∀ i : Fin 2, embedCoords L P (Sum.elim
      (fun i => L.realPart (L.shiftedData g x) ((skeletonCoords L P).equivFin.symm i).1)
      (fun i => L.realPart (L.shiftedData g x) ((interiorCoords L P).equivFin.symm i).1)) (d, i) =
      L.realPart (L.shiftedData g x) (d, i) := by
    intro i
    unfold embedCoords
    split_ifs with h1 h2
    · simp
    · simp
    · exfalso
      simp only [skeletonCoords, interiorCoords, ParamData.interiorSet, ParamData.freeSet,
        Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h2 ⟨hd, h1⟩
  simp only [CellLayout.realCoord]
  rw [he 0, he 1]
  simp only [CellLayout.realPart]
  simp

theorem cornerAt_pres (L : CellLayout) (n : L.modes) (i j : Fin 2) (a : Fin 3)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.cornerAt n i j a (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  unfold CellLayout.cornerAt
  rcases h : L.cellCorner i j with _ | c
  · rfl
  · simp [CellLayout.unitAt, CellDatum.cornerVelocity]

theorem sideVelocityRow_pres (L : CellLayout) (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.sideVelocityRow n e a f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  simp [CellLayout.sideVelocityRow, CellLayout.unitAt, CellDatum.sideVelocity]

theorem sideGradientRow_pres (L : CellLayout) (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.sideGradientRow n e a f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  simp [CellLayout.sideGradientRow, CellLayout.unitAt, CellDatum.sideGradient]

theorem turnSideRow_pres (L : CellLayout) (n : L.modes) (e : Fin 4) (a : Fin 3) (f : ℝ → ℝ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.turnSideRow n e a f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  unfold CellLayout.turnSideRow
  split_ifs <;> simp [sideVelocityRow_pres]

theorem faceBaseRow_pres (L : CellLayout) (n : L.modes) (e : Fin 4) (a b : Fin 3) (l : ℕ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.faceBaseRow n e a b l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  unfold CellLayout.faceBaseRow
  split_ifs <;> simp [cornerAt_pres, sideVelocityRow_pres, sideGradientRow_pres, turnSideRow_pres]

theorem strainFaceRow_pres (L : CellLayout) (n : L.modes) (e : Fin 4) (a b : Fin 3) (l : ℕ)
    (d : L.modes × Fin L.presCount × Fin L.degSide) :
    L.strainFaceRow n e a b l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0 := by
  unfold CellLayout.strainFaceRow
  split_ifs <;> simp [faceBaseRow_pres]

theorem rowApply_shifted (L : CellLayout) {k : ℕ} (g : GaugeShift k) (x : FieldTuple k) (r : L.Datum → ℂ)
    (hr : ∀ d, r (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))) = 0) :
    CellEnergy.rowApply r (L.shiftedData g x) = CellEnergy.rowApply r (L.trueData x) := by
  have h0 : ∑ d, r d * L.pressureShift g x d = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    rcases d with d | d | d | d | d | d | d | d
    · simp [CellLayout.pressureShift]
    · simp [CellLayout.pressureShift]
    · simp [CellLayout.pressureShift]
    · simp [CellLayout.pressureShift]
    · simp [hr]
    · simp [CellLayout.pressureShift]
    · simp [CellLayout.pressureShift]
    · simp [CellLayout.pressureShift]
  unfold CellEnergy.rowApply CellLayout.shiftedData
  simp only [mul_add, Finset.sum_add_distrib, h0, add_zero]

theorem sideRadialIndex_eq (e : Fin 2) : CellLayout.sideRadialIndex ⟨e.val, by omega⟩ = e := by
  unfold CellLayout.sideRadialIndex
  fin_cases e <;> simp

theorem sideHeightIndex_eq (e : Fin 2) : CellLayout.sideHeightIndex ⟨e.val + 2, by omega⟩ = e := by
  unfold CellLayout.sideHeightIndex
  fin_cases e <;> simp

theorem represents_of (hSF : StrainFaceStatement) {k N : ℕ} (c : FracCellData k N) (K : CellBox)
    (S : CellScalars) (B : CellBases) (L : CellLayout) (hL : IsCellLayout c K S B L) (g : GaugeShift k)
    (x : FieldTuple k) (hx : IsAdmissible c x) :
    CellEnergy.Represents K B (CellEnergy.layoutIndex L) c.order x.1 x.2.1 x.2.2.1 (L.shiftedData g x) := by
  have ho := hL.order_eq
  have hb := hL.box_eq
  have hbs := hL.bases_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n a b j l
    show L.trueData x (CellDatum.lowStrain n a b j l) + L.pressureShift g x (CellDatum.lowStrain n a b j l) = _
    simp only [CellLayout.pressureShift, CellDatum.lowStrain, CellLayout.trueData, Sum.elim_inl, add_zero,
      CellLayout.gradModeOf]
    rw [ho, hb, hbs]
  · intro n a j l
    show L.trueData x (CellDatum.lowVelocity n a j l) + L.pressureShift g x (CellDatum.lowVelocity n a j l) = _
    simp only [CellLayout.pressureShift, CellDatum.lowVelocity, CellLayout.trueData, Sum.elim_inl,
      Sum.elim_inr, add_zero]
    unfold CellLayout.velMode
    rw [ho, hb, hbs]
  · intro n e a b l he
    show CellEnergy.rowApply (L.strainFaceRow n ⟨e.val, by omega⟩ a b l) (L.shiftedData g x) = _
    rw [rowApply_shifted L g x _ (strainFaceRow_pres L n _ a b l)]
    have hl : (l : ℕ) ≤ L.degSide := by have := l.isLt; omega
    have := hSF c K S B L hL x hx n ⟨e.val, by omega⟩ a b l hl (fun h => he (Fin.ext h))
    rw [CellEnergy.rowApply, ← this]
    simp only [CellLayout.strainFaceValue, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [if_pos (show e.val < 2 by omega), sideRadialIndex_eq, ho, hb, hbs]
    rfl
  · intro n e a b j
    show CellEnergy.rowApply (L.strainFaceRow n ⟨e.val + 2, by omega⟩ a b j) (L.shiftedData g x) = _
    rw [rowApply_shifted L g x _ (strainFaceRow_pres L n _ a b j)]
    have hl : (j : ℕ) ≤ L.degSide := by have := j.isLt; omega
    have := hSF c K S B L hL x hx n ⟨e.val + 2, by omega⟩ a b j hl (fun h => by simp at h)
    rw [CellEnergy.rowApply, ← this]
    simp only [CellLayout.strainFaceValue, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [if_neg (show ¬ (e.val + 2 < 2) by omega), sideHeightIndex_eq, ho, hb, hbs]
    rfl

end CanonicalInputs.Internal

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars CanonicalInputs.Internal in
theorem canonicalInputsValid_of (hL : LayoutRowValueStatement) (hG : GaugeInvarianceStatement)
    (hLF : CellEnergy.LocalFormBoundStatement) (hLow : LowEntryStatement) (hSP : ShiftedParamStatement)
    (hSR : ShiftedRealReductionStatement) (hSF : StrainFaceStatement) : CanonicalInputsValidStatement := by
  intro α hα₁ hα₂ k N slots c hc K S B Cl R hD hRS L P sel hPL hCP g hg htr hptr
  have hLay := hPL.layout
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact coord_linear_of L P
  · intro x hx
    exact data_represents_of L P g x (hSP c K S B L hLay P sel hCP g x hx)
  · intro x hx i
    exact lowEntry_agree_of hLow c K S B L hLay g x hx i
  · intro x hx a ha
    change lowRowValue c K S α x a = layoutRowValue c α L R a (L.shiftedData g x) x.2.2.2.1
    rw [hL α hα₁ hα₂ c hc K S B Cl R hD hRS L hPL htr hptr x hx a ha]
    exact (hG α hα₁ hα₂ c hc K S B Cl R hD hRS L hPL hptr g hg x hx a ha (L.trueData x) x.2.2.2.1).symm
  · intro x hx ζ
    exact hLF α c K B S Cl (CellEnergy.layoutIndex L) hLay.modes_eq hLay.degCoef_eq hLay.degSide_eq hD.box
      hD.bases hD.scalars hc hD.class_regular x.1 x.2.1 x.2.2.1 hx.1 (L.shiftedData g x)
      (represents_of hSF c K S B L hLay g x hx) x.2.2.2.1 ζ


end CellFormula

end CellCert

end Breakdown
