import Breakdown.FracCell.StrainFaceSides

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

private def ev (L : CellLayout) {k : ℕ} (x : FieldTuple k) (R : L.Datum → ℂ) : ℂ := ∑ d, R d * L.trueData x d

private theorem ev_add (L : CellLayout) {k : ℕ} (x : FieldTuple k) (R₁ R₂ : L.Datum → ℂ) :
    ev L x (R₁ + R₂) = ev L x R₁ + ev L x R₂ := by
  simp only [ev, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem ev_sub (L : CellLayout) {k : ℕ} (x : FieldTuple k) (R₁ R₂ : L.Datum → ℂ) :
    ev L x (R₁ - R₂) = ev L x R₁ - ev L x R₂ := by
  simp only [ev, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem ev_neg (L : CellLayout) {k : ℕ} (x : FieldTuple k) (R : L.Datum → ℂ) :
    ev L x (-R) = -ev L x R := by
  simp only [ev, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private theorem ev_smul (L : CellLayout) {k : ℕ} (x : FieldTuple k) (c : ℂ) (R : L.Datum → ℂ) :
    ev L x (c • R) = c * ev L x R := by
  simp only [ev, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem ev_unit (L : CellLayout) {k : ℕ} (x : FieldTuple k) (d : L.Datum) :
    ev L x (L.unitAt d) = L.trueData x d := by
  unfold ev
  rw [Finset.sum_eq_single d]
  · rw [CellLayout.unitAt, Pi.single_eq_same, one_mul]
  · intro b _ hb
    rw [CellLayout.unitAt, Pi.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ d) h

private theorem poly_sum (D : ℕ) (c : ℕ → ℝ) :
    IsPolyFn D (fun u => ∑ i ∈ Finset.range (D + 1), c i * u ^ i) := by
  refine ⟨∑ i ∈ Finset.range (D + 1), Polynomial.C (c i) * Polynomial.X ^ i, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_C_mul_X_pow_le (c i) i).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  · intro u
    simp [Polynomial.eval_finsetSum]

private theorem poly_mono {D D' : ℕ} {f : ℝ → ℝ} (h : IsPolyFn D f) (hD : D ≤ D') : IsPolyFn D' f := by
  obtain ⟨p, hp, hf⟩ := h
  exact ⟨p, hp.trans hD, hf⟩

private theorem poly_deriv {D : ℕ} {f : ℝ → ℝ} (h : IsPolyFn D f) : IsPolyFn (D - 1) (deriv f) := by
  obtain ⟨p, hp, hf⟩ := h
  have hfe : f = fun u => p.eval u := funext hf
  subst hfe
  exact ⟨Polynomial.derivative p, (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp 1),
    fun u => Polynomial.deriv p⟩

private theorem poly_mulX {D : ℕ} {f : ℝ → ℝ} (h : IsPolyFn D f) : IsPolyFn (D + 1) (fun r => r * f r) := by
  obtain ⟨p, hp, hf⟩ := h
  refine ⟨Polynomial.X * p, ?_, fun u => by simp [hf u]⟩
  calc (Polynomial.X * p).natDegree ≤ Polynomial.X.natDegree + p.natDegree := Polynomial.natDegree_mul_le
    _ ≤ 1 + D := add_le_add Polynomial.natDegree_X_le hp
    _ = D + 1 := by ring

private theorem poly_any {D : ℕ} {f : ℝ → ℝ} (h : IsPolyFn D f) : IsAnyPolyFn f := by
  obtain ⟨p, _, hf⟩ := h
  exact ⟨p, hf⟩

private theorem corner_eval {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hL : IsCellLayout c K S B L) (x : FieldTuple k) (n : L.modes) (i j : Fin 2) (a : Fin 3)
    (hij : i = 1 ∨ K.r₁ ≠ 0) : ev L x (L.cornerAt n i j a) = L.cornerValue n x i j a := by
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
  rw [ev_unit]
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

theorem strainFace_of (hV : SideVelocityEvalStatement) (hG : SideGradientEvalStatement)
    (hRT : RadialTangentStatement) (hRU : RadialTurnStatement) (hHN : HeightNormalStatement)
    (hHU : HeightTurnStatement) (hTF : FaceTraceFreeStatement) : StrainFaceStatement := by
  intro k N c K S B L hL x hx n e a b l hl he
  have hb := hL.box_eq
  have hvel : ∀ (a' : Fin 3) (f : ℝ → ℝ), IsPolyFn (L.degSide + 1) f →
      ev L x (L.sideVelocityRow n e a' f) = L.sideVelocityValue n x e a' f :=
    fun a' f hf => hV c K S B L hL x hx n e a' f he hf
  have hgrad : ∀ (a' : Fin 3) (t : ℝ → ℝ), IsPolyFn L.degSide t →
      ev L x (L.sideGradientRow n e a' t) = L.sideGradientValue n x e a' t :=
    fun a' t ht => hG c K S B L hL x hx n e a' t he ht
  have hturn : ∀ (a' : Fin 3) (f : ℝ → ℝ), IsPolyFn (L.degSide + 1) f →
      ev L x (L.turnSideRow n e a' f) = L.turnValue n x e a' f := by
    intro a' f hf
    unfold CellLayout.turnSideRow CellLayout.turnValue
    dsimp only
    split_ifs
    · rw [ev_sub, ev_smul, hvel _ _ hf, hvel _ _ hf]
    · rw [ev_add, ev_smul, hvel _ _ hf, hvel _ _ hf]
    · rw [ev_smul, hvel _ _ hf]
  have pH : IsPolyFn l (L.bases.heightPoly l) := poly_sum l (L.bases.heightCoef l)
  have pR : IsPolyFn l (L.bases.radialPoly l) := poly_sum l (L.bases.radialCoef l)
  have hface : ∀ a' b' : Fin 3, ev L x (L.faceBaseRow n e a' b' l) = L.strainFaceValue n x e a' b' l := by
    intro a' b'
    unfold CellLayout.faceBaseRow CellLayout.strainFaceValue
    by_cases he2 : e.val < 2
    · rw [if_pos he2, if_pos he2]
      obtain rfl | rfl | rfl : b' = 0 ∨ b' = 1 ∨ b' = 2 := by fin_cases b' <;> simp
      · rw [if_neg (by decide), if_neg (by decide), hgrad _ _ (poly_mono pH hl)]
        unfold CellLayout.sideGradientValue
        rw [if_pos he2]
      · rw [if_neg (by decide), if_pos rfl, ev_smul, hturn _ _ (poly_mono pH (by omega))]
        exact (hRU c K S B L hL x hx n e a' _ he2 he (poly_any pH)).symm
      · have hri : CellLayout.sideRadialIndex e = 1 ∨ K.r₁ ≠ 0 := by
          by_cases h0 : e.val = 0
          · exact Or.inr (he h0)
          · left
            unfold CellLayout.sideRadialIndex
            rw [if_neg h0]
        rw [if_pos rfl, ev_sub, ev_sub, ev_smul, ev_smul, corner_eval hL x n _ _ a' hri,
          corner_eval hL x n _ _ a' hri, hvel _ _ (poly_mono (poly_deriv pH) (by omega))]
        exact (hRT c K S B L hL x hx n e a' _ he2 he (poly_any pH)).symm
    · rw [if_neg he2, if_neg he2]
      have he2' : 2 ≤ e.val := by omega
      obtain rfl | rfl | rfl : b' = 0 ∨ b' = 1 ∨ b' = 2 := by fin_cases b' <;> simp
      · rw [if_pos rfl, ev_sub, ev_sub, ev_smul, ev_smul, corner_eval hL x n 1 _ a' (Or.inl rfl),
          hvel _ _ (poly_mono (poly_deriv (poly_mulX pR)) (by omega)),
          hHN c K S B L hL x hx n e a' _ he2' (poly_any pR)]
        congr 1
        congr 1
        by_cases h0 : K.r₁ = 0
        · have h0' : L.box.r₁ = 0 := by rw [hb]; exact h0
          simp [h0']
        · rw [corner_eval hL x n 0 _ a' (Or.inr h0)]
      · rw [if_neg (by decide), if_pos rfl, hturn _ _ (poly_mono pR (by omega))]
        exact (hHU c K S B L hL x hx n e a' _ he2' (poly_any pR)).symm
      · rw [if_neg (by decide), if_neg (by decide), hgrad _ _ (poly_mono pR hl)]
        unfold CellLayout.sideGradientValue
        rw [if_neg he2]
  show L.strainFaceValue n x e a b l = ev L x (L.strainFaceRow n e a b l)
  unfold CellLayout.strainFaceRow
  split_ifs with h1 h2
  · obtain ⟨he2, rfl, rfl⟩ := h1
    rw [ev_neg, ev_add, hface, hface]
    have htf := (hTF c K S B L hL x hx n (CellLayout.sideRadialIndex e) (L.bases.heightPoly l) (poly_any pH)).1
    simp only [CellLayout.strainFaceValue, if_pos he2]
    linear_combination htf
  · obtain ⟨he2, rfl, rfl⟩ := h2
    rw [ev_neg, ev_add, hface, hface]
    have htf := (hTF c K S B L hL x hx n (CellLayout.sideHeightIndex e) (L.bases.radialPoly l) (poly_any pR)).2
    simp only [CellLayout.strainFaceValue, if_neg (show ¬ e.val < 2 by omega)]
    linear_combination htf
  · exact (hface a b).symm

theorem strainFace_of_traces (hI : SideStripIntegrableStatement) (hRT : RadialTangentStatement)
    (hRU : RadialTurnStatement) (hHN : HeightNormalStatement) (hHU : HeightTurnStatement)
    (hTF : FaceTraceFreeStatement) : StrainFaceStatement :=
  strainFace_of (sideVelocityEval_of hI) (sideGradientEval_of hI) hRT hRU hHN hHU hTF

end CellFormula

end CellCert

end Breakdown
