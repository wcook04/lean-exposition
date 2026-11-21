import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.CertCell.LocalFaceSides
import Breakdown.CertCell.LocalFaceTangent
import Breakdown.CertCell.LocalFaceHeight
import Breakdown.CertCell.LocalFaceStrip
import Breakdown.CertCell.LocalFaceTraceFree
import Breakdown.CertCell.LocalFaceTurn

open MeasureTheory Matrix Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy

namespace Internal.StrainFaceRows

def rowValue (L : CellLayout) {k : ℕ} (x : FieldTuple k) (R : L.Datum → ℂ) : ℂ := ∑ d, R d * L.trueData x d

theorem rowValue_add (L : CellLayout) {k : ℕ} (x : FieldTuple k) (R₁ R₂ : L.Datum → ℂ) :
    rowValue L x (R₁ + R₂) = rowValue L x R₁ + rowValue L x R₂ := by
  simp only [rowValue, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem rowValue_sub (L : CellLayout) {k : ℕ} (x : FieldTuple k) (R₁ R₂ : L.Datum → ℂ) :
    rowValue L x (R₁ - R₂) = rowValue L x R₁ - rowValue L x R₂ := by
  simp only [rowValue, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem rowValue_neg (L : CellLayout) {k : ℕ} (x : FieldTuple k) (R : L.Datum → ℂ) :
    rowValue L x (-R) = -rowValue L x R := by
  simp only [rowValue, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem rowValue_smul (L : CellLayout) {k : ℕ} (x : FieldTuple k) (s : ℂ) (R : L.Datum → ℂ) :
    rowValue L x (s • R) = s * rowValue L x R := by
  simp only [rowValue, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem rowValue_unit (L : CellLayout) {k : ℕ} (x : FieldTuple k) (d : L.Datum) :
    rowValue L x (L.unitAt d) = L.trueData x d := by
  unfold rowValue
  rw [Finset.sum_eq_single d]
  · rw [CellLayout.unitAt, Pi.single_eq_same, one_mul]
  · intro d' _ hd
    rw [CellLayout.unitAt, Pi.single_eq_of_ne hd, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem polyFn_sum (D : ℕ) (w : ℕ → ℝ) :
    IsPolyFn D (fun u => ∑ i ∈ Finset.range (D + 1), w i * u ^ i) := by
  refine ⟨∑ i ∈ Finset.range (D + 1), Polynomial.C (w i) * Polynomial.X ^ i, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_C_mul_X_pow_le (w i) i).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  · intro u
    simp [Polynomial.eval_finsetSum]

theorem polyFn_mono {D D' : ℕ} {f : ℝ → ℝ} (h : IsPolyFn D f) (hD : D ≤ D') : IsPolyFn D' f := by
  obtain ⟨P, hP, hf⟩ := h
  exact ⟨P, hP.trans hD, hf⟩

theorem polyFn_deriv {D : ℕ} {f : ℝ → ℝ} (h : IsPolyFn D f) : IsPolyFn (D - 1) (deriv f) := by
  obtain ⟨P, hP, hf⟩ := h
  have hfe : f = fun u => P.eval u := funext hf
  subst hfe
  exact ⟨Polynomial.derivative P, (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1),
    fun u => Polynomial.deriv P⟩

theorem polyFn_mulX {D : ℕ} {f : ℝ → ℝ} (h : IsPolyFn D f) : IsPolyFn (D + 1) (fun r => r * f r) := by
  obtain ⟨P, hP, hf⟩ := h
  refine ⟨Polynomial.X * P, ?_, fun u => by simp [hf u]⟩
  calc (Polynomial.X * P).natDegree ≤ Polynomial.X.natDegree + P.natDegree := Polynomial.natDegree_mul_le
    _ ≤ 1 + D := add_le_add Polynomial.natDegree_X_le hP
    _ = D + 1 := by ring

theorem polyFn_any {D : ℕ} {f : ℝ → ℝ} (h : IsPolyFn D f) : IsAnyPolyFn f := by
  obtain ⟨P, _, hf⟩ := h
  exact ⟨P, hf⟩

theorem cornerRow_value {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hL : IsCellLayout c K S B L) (x : FieldTuple k) (n : L.modes) (i j : Fin 2) (a : Fin 3)
    (hij : i = 1 ∨ K.r₁ ≠ 0) : rowValue L x (L.cornerAt n i j a) = L.cornerValue n x i j a := by
  have hne : L.cellCorner i j ≠ none := by
    intro h
    obtain ⟨h1, h2⟩ := hL.cellCorner_axis i j h
    rcases hij with h3 | h3
    · rw [h1] at h3
      exact absurd h3 (by decide)
    · exact h3 h2
  obtain ⟨cc, hc⟩ := Option.ne_none_iff_exists'.mp hne
  have hs := hL.cellCorner_spec i j cc hc
  obtain ⟨ho1, ho2⟩ := hL.corner_other cc
  have hb := hL.box_eq
  simp only [CellLayout.cornerAt, hc]
  rw [rowValue_unit]
  have e1 : (L.corner cc).1 = if i = 0 then L.box.r₁ else L.box.r₂ := by rw [hs, hb]
  have e2 : (L.corner cc).2 = if j = 0 then L.box.z₁ else L.box.z₂ := by rw [hs, hb]
  have e3 : (L.cornerOther cc).1 = if i = 0 then L.box.r₂ else L.box.r₁ := by
    rw [ho1, hs, hb]
    dsimp only
    split_ifs <;> ring
  have e4 : (L.cornerOther cc).2 = if j = 0 then L.box.z₂ else L.box.z₁ := by
    rw [ho2, hs, hb]
    dsimp only
    split_ifs <;> ring
  show cornerMoment (L.corner cc).1 (L.cornerOther cc).1 (L.corner cc).2 (L.cornerOther cc).2 _ _ _ _ = _
  rw [e1, e2, e3, e4]
  rfl

theorem radialIndex_val (e : Fin 2) : CellLayout.sideRadialIndex ⟨e.val, by omega⟩ = e := by
  unfold CellLayout.sideRadialIndex
  fin_cases e <;> simp

theorem heightIndex_val (e : Fin 2) : CellLayout.sideHeightIndex ⟨e.val + 2, by omega⟩ = e := by
  unfold CellLayout.sideHeightIndex
  fin_cases e <;> simp

end Internal.StrainFaceRows

open Internal.StrainFaceRows

theorem localStrainFace_of (hV : LocalSideVelocityEvalStatement) (hG : LocalSideGradientEvalStatement)
    (hRT : LocalRadialTangentStatement) (hRU : LocalRadialTurnStatement) (hHN : LocalHeightNormalStatement)
    (hHU : LocalHeightTurnStatement) (hTF : LocalFaceTraceFreeStatement) :
    LocalStrainFaceStatement := by
  intro k N c K S B L hL x hx n e a b l hl he
  have hb := hL.box_eq
  have hvel : ∀ (a' : Fin 3) (f : ℝ → ℝ), IsPolyFn (L.degSide + 1) f →
      rowValue L x (L.sideVelocityRow n e a' f) = L.sideVelocityValue n x e a' f :=
    fun a' f hf => hV c K S B L hL x hx n e a' f he hf
  have hgrad : ∀ (a' : Fin 3) (t : ℝ → ℝ), IsPolyFn L.degSide t →
      rowValue L x (L.sideGradientRow n e a' t) = L.sideGradientValue n x e a' t :=
    fun a' t ht => hG c K S B L hL x hx n e a' t he ht
  have hturn : ∀ (a' : Fin 3) (f : ℝ → ℝ), IsPolyFn (L.degSide + 1) f →
      rowValue L x (L.turnSideRow n e a' f) = L.turnValue n x e a' f := by
    intro a' f hf
    unfold CellLayout.turnSideRow CellLayout.turnValue
    dsimp only
    split_ifs
    · rw [rowValue_sub, rowValue_smul, hvel _ _ hf, hvel _ _ hf]
    · rw [rowValue_add, rowValue_smul, hvel _ _ hf, hvel _ _ hf]
    · rw [rowValue_smul, hvel _ _ hf]
  have pH : IsPolyFn l (L.bases.heightPoly l) := polyFn_sum l (L.bases.heightCoef l)
  have pR : IsPolyFn l (L.bases.radialPoly l) := polyFn_sum l (L.bases.radialCoef l)
  have hface : ∀ a' b' : Fin 3, rowValue L x (L.faceBaseRow n e a' b' l) = L.strainFaceValue n x e a' b' l := by
    intro a' b'
    unfold CellLayout.faceBaseRow CellLayout.strainFaceValue
    by_cases he2 : e.val < 2
    · rw [if_pos he2, if_pos he2]
      obtain rfl | rfl | rfl : b' = 0 ∨ b' = 1 ∨ b' = 2 := by fin_cases b' <;> simp
      · rw [if_neg (by decide), if_neg (by decide), hgrad _ _ (polyFn_mono pH hl)]
        unfold CellLayout.sideGradientValue
        rw [if_pos he2]
      · rw [if_neg (by decide), if_pos rfl, rowValue_smul, hturn _ _ (polyFn_mono pH (by omega))]
        exact (hRU c K S B L hL x hx n e a' _ he2 he (polyFn_any pH)).symm
      · have hri : CellLayout.sideRadialIndex e = 1 ∨ K.r₁ ≠ 0 := by
          by_cases h0 : e.val = 0
          · exact Or.inr (he h0)
          · left
            unfold CellLayout.sideRadialIndex
            rw [if_neg h0]
        rw [if_pos rfl, rowValue_sub, rowValue_sub, rowValue_smul, rowValue_smul, cornerRow_value hL x n _ _ a' hri,
          cornerRow_value hL x n _ _ a' hri, hvel _ _ (polyFn_mono (polyFn_deriv pH) (by omega))]
        exact (hRT c K S B L hL x hx n e a' _ he2 he (polyFn_any pH)).symm
    · rw [if_neg he2, if_neg he2]
      have he2' : 2 ≤ e.val := by omega
      obtain rfl | rfl | rfl : b' = 0 ∨ b' = 1 ∨ b' = 2 := by fin_cases b' <;> simp
      · rw [if_pos rfl, rowValue_sub, rowValue_sub, rowValue_smul, rowValue_smul,
          cornerRow_value hL x n 1 _ a' (Or.inl rfl),
          hvel _ _ (polyFn_mono (polyFn_deriv (polyFn_mulX pR)) (by omega)),
          hHN c K S B L hL x hx n e a' _ he2' (polyFn_any pR)]
        congr 1
        congr 1
        by_cases h0 : K.r₁ = 0
        · have h0' : L.box.r₁ = 0 := by rw [hb]; exact h0
          simp [h0']
        · rw [cornerRow_value hL x n 0 _ a' (Or.inr h0)]
      · rw [if_neg (by decide), if_pos rfl, hturn _ _ (polyFn_mono pR (by omega))]
        exact (hHU c K S B L hL x hx n e a' _ he2' (polyFn_any pR)).symm
      · rw [if_neg (by decide), if_neg (by decide), hgrad _ _ (polyFn_mono pR hl)]
        unfold CellLayout.sideGradientValue
        rw [if_neg he2]
  show L.strainFaceValue n x e a b l = rowValue L x (L.strainFaceRow n e a b l)
  unfold CellLayout.strainFaceRow
  split_ifs with h1 h2
  · obtain ⟨he2, rfl, rfl⟩ := h1
    rw [rowValue_neg, rowValue_add, hface, hface]
    have hri0 : CellLayout.sideRadialIndex e = 0 → K.r₁ ≠ 0 := by
      intro h0
      refine he ?_
      by_contra hne
      unfold CellLayout.sideRadialIndex at h0
      rw [if_neg hne] at h0
      exact absurd h0 (by decide)
    have htf := (hTF c K S B L hL x hx n (CellLayout.sideRadialIndex e) (L.bases.heightPoly l)
      (polyFn_any pH) hri0).1
    simp only [CellLayout.strainFaceValue, if_pos he2]
    linear_combination htf
  · obtain ⟨he2, rfl, rfl⟩ := h2
    rw [rowValue_neg, rowValue_add, hface, hface]
    have htf := localFaceHeightTraceFree c K S B L hL x hx n (CellLayout.sideHeightIndex e) (L.bases.radialPoly l) (polyFn_any pR)
    simp only [CellLayout.strainFaceValue, if_neg (show ¬ e.val < 2 by omega)]
    linear_combination htf
  · exact (hface a b).symm

theorem localStrainFace_of_turn (hRU : LocalRadialTurnStatement) : LocalStrainFaceStatement :=
  localStrainFace_of (localSideVelocityEval_of localSideStripIntegrable)
    (localSideGradientEval_of localSideStripIntegrable) localRadialTangent hRU localHeightNormal
    (localHeightTurn_of localSideStripIntegrable) localFaceTraceFree

theorem localRepresents_of (hSF : LocalStrainFaceStatement) : LocalRepresentsStatement := by
  intro k N c K S B L hL x hx
  have ho := hL.order_eq
  have hb := hL.box_eq
  have hbs := hL.bases_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n a b j l
    show L.trueData x (CellDatum.lowStrain n a b j l) = _
    simp only [CellDatum.lowStrain, CellLayout.trueData, Sum.elim_inl, CellLayout.gradModeOf]
    rw [ho, hb, hbs]
  · intro n a j l
    show L.trueData x (CellDatum.lowVelocity n a j l) = _
    simp only [CellDatum.lowVelocity, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    unfold CellLayout.velMode
    rw [ho, hb, hbs]
  · intro n e a b l he
    show rowApply (L.strainFaceRow n ⟨e.val, by omega⟩ a b l) (L.trueData x) = _
    have hl : (l : ℕ) ≤ L.degSide := by have := l.isLt; omega
    have h := hSF c K S B L hL x hx n ⟨e.val, by omega⟩ a b l hl (fun h => he (Fin.ext h))
    rw [rowApply, ← h]
    simp only [CellLayout.strainFaceValue, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [if_pos (show e.val < 2 by omega), radialIndex_val, ho, hb, hbs]
    rfl
  · intro n e a b j
    show rowApply (L.strainFaceRow n ⟨e.val + 2, by omega⟩ a b j) (L.trueData x) = _
    have hl : (j : ℕ) ≤ L.degSide := by have := j.isLt; omega
    have h := hSF c K S B L hL x hx n ⟨e.val + 2, by omega⟩ a b j hl (fun h => by simp at h)
    rw [rowApply, ← h]
    simp only [CellLayout.strainFaceValue, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [if_neg (show ¬ (e.val + 2 < 2) by omega), heightIndex_val, ho, hb, hbs]
    rfl

theorem localStrainFace : LocalStrainFaceStatement :=
  localStrainFace_of_turn localRadialTurn

theorem localRepresents : LocalRepresentsStatement :=
  localRepresents_of localStrainFace

end LocalField

end CertCell

end Breakdown
