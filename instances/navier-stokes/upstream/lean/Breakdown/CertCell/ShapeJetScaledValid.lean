import Breakdown.CertCell.ShapeJetScaled
import Breakdown.CertCell.ShapeJetReflect

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (cellCount)

namespace Internal

theorem coeff_comp_neg_X_real (p : Polynomial ℝ) (s : ℕ) :
    (p.comp (-Polynomial.X)).coeff s = (-1) ^ s * p.coeff s := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial n a =>
    have hX : (-Polynomial.X : Polynomial ℝ) ^ n = Polynomial.C ((-1) ^ n) * Polynomial.X ^ n := by
      rw [neg_pow, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_1]
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, hX,
      ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs with h
    · subst h
      ring
    · simp

theorem symmetricJacobi_comp_neg (α j : ℕ) :
    (symmetricJacobi α j).comp (-Polynomial.X) = Polynomial.C ((-1) ^ j) * symmetricJacobi α j := by
  unfold symmetricJacobi
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.sum_comp]
  conv_rhs => rw [← Finset.sum_range_reflect]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  have h1 : i + k + 1 - 1 - i = k := by omega
  have h2 : i + k - i = k := by omega
  have h3 : i + k - k = i := by omega
  rw [h1, h2, h3]
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.one_comp, Nat.cast_mul, map_mul, map_pow, map_neg, map_one]
  have e1 : (-Polynomial.X - 1 : Polynomial ℝ) = -(Polynomial.X + 1) := by ring
  have e2 : (-Polynomial.X + 1 : Polynomial ℝ) = -(Polynomial.X - 1) := by ring
  have e3 : (-(Polynomial.X + 1) : Polynomial ℝ) ^ k = (-1) ^ k * (Polynomial.X + 1) ^ k := neg_pow _ _
  have e4 : (-(Polynomial.X - 1) : Polynomial ℝ) ^ i = (-1) ^ i * (Polynomial.X - 1) ^ i := neg_pow _ _
  rw [e1, e2, e3, e4]
  ring

theorem symmetricJacobi_coeff_parity (α j s : ℕ) :
    (-1 : ℝ) ^ j * (symmetricJacobi α j).coeff s = (-1) ^ s * (symmetricJacobi α j).coeff s := by
  have h := congrArg (fun p => Polynomial.coeff p s) (symmetricJacobi_comp_neg α j)
  simp only [coeff_comp_neg_X_real, Polynomial.coeff_C_mul] at h
  exact h.symm

theorem scaled_convert_conj (A : ScaledJetAxis) (d e : JetDof) :
    starRingEnd ℂ (A.convert d e) = A.convert d e := by
  cases d <;> cases e <;> simp only [ScaledJetAxis.convert] <;> (try split_ifs) <;>
    exact Complex.conj_ofReal _

theorem scale_getD_reflect (A : ScaledJetAxis) (hS : HasSymmetricScale A) (k : ℕ)
    (hk : k ≤ cellCount A.breaks) : A.scale.getD (cellCount A.breaks - k) 1 = A.scale.getD k 1 := by
  obtain ⟨hlen, hrev⟩ := hS
  unfold cellCount at hk ⊢
  rcases Nat.eq_zero_or_pos A.breaks.length with h0 | hpos
  · have hk0 : k = 0 := by omega
    subst hk0
    rw [h0]
  · conv_lhs => rw [← hrev]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_reverse, List.getD_eq_getElem _ _ (by omega)]
    congr 1
    omega

theorem scaled_convert_reflect (A : ScaledJetAxis) (hB : IsSymmetricAxis A.base) (hS : HasSymmetricScale A)
    (e e' : JetDof) (he : e ∈ A.base.dofs) (he' : e' ∈ A.base.dofs) :
    A.convert (A.base.reflectDof e) (A.base.reflectDof e') * JetAxis.dofSign e' =
      JetAxis.dofSign e * A.convert e e' := by
  have hb : A.base.breaks = A.breaks := rfl
  rw [mem_dofs, hb] at he he'
  unfold IsSymmetricAxis at hB
  rw [hb] at hB
  rcases he with ⟨k, p, hk, hp, rfl⟩ | ⟨i, s, hi, hs, rfl⟩ <;>
    rcases he' with ⟨k', p', hk', hp', rfl⟩ | ⟨i', j, hi', hj, rfl⟩
  · simp only [JetAxis.reflectDof, ScaledJetAxis.convert, JetAxis.dofSign, hb]
    by_cases h : k = k' ∧ p = p'
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, scale_getD_reflect A hS k hk]
      ring
    · rw [if_neg h, if_neg (fun h' => h ⟨by omega, h'.2⟩)]
      simp
  · simp [JetAxis.reflectDof, ScaledJetAxis.convert]
  · simp [JetAxis.reflectDof, ScaledJetAxis.convert]
  · simp only [JetAxis.reflectDof, ScaledJetAxis.convert, JetAxis.dofSign, hb]
    by_cases h : i = i'
    · subst h
      have hlen : i + 1 < A.breaks.length := by unfold cellCount at hi; omega
      have h0 : A.breaks.getD (cellCount A.breaks - 1 - i) 0 = -A.breaks.getD (i + 1) 0 := by
        rw [← getD_of_symmetric A.breaks hB (i + 1) hlen]
        congr 1
        unfold cellCount
        omega
      have h1 : A.breaks.getD (cellCount A.breaks - 1 - i + 1) 0 = -A.breaks.getD i 0 := by
        rw [← getD_of_symmetric A.breaks hB i (by omega)]
        congr 1
        unfold cellCount
        omega
      have hw : A.breaks.getD (cellCount A.breaks - 1 - i + 1) 0 - A.breaks.getD (cellCount A.breaks - 1 - i) 0 =
          A.breaks.getD (i + 1) 0 - A.breaks.getD i 0 := by
        rw [h0, h1]
        ring
      rw [if_pos rfl, if_pos rfl, hw]
      have hpar := symmetricJacobi_coeff_parity (2 * A.depth) j s
      have key : ∀ Y : ℝ, ((Y * (symmetricJacobi (2 * A.depth) j).coeff s : ℝ) : ℂ) * (-1) ^ j =
          (-1) ^ s * ((Y * (symmetricJacobi (2 * A.depth) j).coeff s : ℝ) : ℂ) := by
        intro Y
        have hr : (Y * (symmetricJacobi (2 * A.depth) j).coeff s) * (-1) ^ j =
            (-1) ^ s * (Y * (symmetricJacobi (2 * A.depth) j).coeff s) := by
          linear_combination Y * hpar
        exact_mod_cast hr
      exact key _
    · rw [if_neg h, if_neg (by omega)]
      simp

theorem sum_scaled_convert_reflect (A : ScaledJetAxis) (hB : IsSymmetricAxis A.base) (hS : HasSymmetricScale A)
    (c g : JetDof → ℂ) (τ : ℂ) (hfix : ∀ f ∈ A.base.dofs, c (A.base.reflectDof f) = τ * JetAxis.dofSign f * g f)
    (e : JetDof) (he : e ∈ A.base.dofs) :
    ∑ e' ∈ A.base.dofs, A.convert (A.base.reflectDof e) e' * c e' =
      τ * JetAxis.dofSign e * ∑ e' ∈ A.base.dofs, A.convert e e' * g e' := by
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_nbij' A.base.reflectDof A.base.reflectDof (fun f hf => reflectDof_mem _ _ hf)
    (fun f hf => reflectDof_mem _ _ hf) (fun f hf => reflectDof_reflectDof _ _ hf)
    (fun f hf => reflectDof_reflectDof _ _ hf) (fun f hf => ?_)
  rw [hfix f hf]
  have h := scaled_convert_reflect A hB hS e f he hf
  linear_combination (-(τ * g f)) * h

theorem scaled_toJet_coef (H : ScaledJetSpline) (d e : JetDof) :
    H.toJet.coef d e = ∑ d' ∈ H.tAxis.base.dofs, H.tAxis.convert d d' *
      ∑ e' ∈ H.xAxis.base.dofs, H.xAxis.convert e e' * H.coef d' e' := by
  simp only [ScaledJetSpline.toJet, Finset.mul_sum, mul_assoc]

theorem scaled_jetClass {a b : ℕ} (H : ScaledJetSpline) (h : IsJetClass a b H.coefValues) :
    IsJetClass a b H.toJet :=
  ⟨h.t_axis, h.x_axis, h.t_depth, h.x_depth⟩

theorem scaled_vanishesAtStart (H : ScaledJetSpline) (h : H.coefValues.VanishesAtStart) :
    H.toJet.VanishesAtStart := by
  intro e
  rw [scaled_toJet_coef]
  refine Finset.sum_eq_zero (fun d' _ => ?_)
  by_cases hd : d' = JetDof.node 0 0
  · subst hd
    have h' : ∀ e', H.coef (JetDof.node 0 0) e' = 0 := h
    simp [h']
  · have hc : H.tAxis.convert (JetDof.node 0 0) d' = 0 := by
      cases d' with
      | node k p =>
        simp only [ScaledJetAxis.convert]
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        exact hd rfl
      | bubble i s => simp [ScaledJetAxis.convert]
    rw [hc, zero_mul]

theorem scaled_realCoef (H : ScaledJetSpline) (h : H.coefValues.HasRealCoef) : H.toJet.HasRealCoef := by
  intro d e
  have h' : ∀ d e, starRingEnd ℂ (H.coef d e) = H.coef d e := h
  rw [scaled_toJet_coef]
  simp only [map_sum, map_mul, scaled_convert_conj, h']

theorem scaled_reflectFixed (H : ScaledJetSpline) (odd : Bool) (hB : IsSymmetricAxis H.xAxis.base)
    (hS : HasSymmetricScale H.xAxis) (h : H.coefValues.IsReflectFixed odd) : H.toJet.IsReflectFixed odd := by
  intro d e he
  have hx : H.toJet.xAxis = H.xAxis.base := rfl
  rw [hx] at he ⊢
  rw [scaled_toJet_coef, scaled_toJet_coef, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d' _ => ?_)
  rw [sum_scaled_convert_reflect H.xAxis hB hS (H.coef d') (H.coef d') _ (fun f hf => h d' f hf) e he]
  ring

theorem scaled_conjReflectFixed (H : ScaledJetSpline) (odd : Bool) (hB : IsSymmetricAxis H.xAxis.base)
    (hS : HasSymmetricScale H.xAxis) (h : H.coefValues.IsConjReflectFixed odd) :
    H.toJet.IsConjReflectFixed odd := by
  intro d e he
  have hx : H.toJet.xAxis = H.xAxis.base := rfl
  rw [hx] at he ⊢
  rw [scaled_toJet_coef, scaled_toJet_coef, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d' _ => ?_)
  simp only [map_mul, map_sum, scaled_convert_conj]
  rw [sum_scaled_convert_reflect H.xAxis hB hS (H.coef d') (fun f => starRingEnd ℂ (H.coef d' f)) _
    (fun f hf => h d' f hf) e he]
  ring

end Internal

open Internal in
theorem scaledJetDataHolds : ScaledJetDataHolds := by
  intro S hS
  have hT := hS.valueSets
  exact
    { one_per_orbit := hT.one_per_orbit
      radial_class := fun κ hκ h0 => scaled_jetClass _ (hT.radial_class κ hκ h0)
      polar_class := fun κ hκ h0 => scaled_jetClass _ (hT.polar_class κ hκ h0)
      stream_class := fun κ hκ h0 => scaled_jetClass _ (hT.stream_class κ hκ h0)
      swirl_class := fun κ hκ h0 => scaled_jetClass _ (hT.swirl_class κ hκ h0)
      lowOrder_ge := hT.lowOrder_ge
      highOrder_pos := hT.highOrder_pos
      typeTwo_symmetric := hT.typeTwo_symmetric
      typeTwo_odd := fun κ hκ h0 =>
        ⟨scaled_reflectFixed _ _ (hT.typeTwo_symmetric κ hκ h0).1 (hS.typeTwo_scales κ hκ h0).1
            (hT.typeTwo_odd κ hκ h0).1,
          scaled_reflectFixed _ _ (hT.typeTwo_symmetric κ hκ h0).2 (hS.typeTwo_scales κ hκ h0).2
            (hT.typeTwo_odd κ hκ h0).2⟩
      typeTwo_start := fun κ hκ h0 =>
        ⟨scaled_vanishesAtStart _ (hT.typeTwo_start κ hκ h0).1, scaled_vanishesAtStart _ (hT.typeTwo_start κ hκ h0).2⟩
      self_conj := fun κ hκ h =>
        ⟨scaled_realCoef _ (hT.self_conj κ hκ h).1, scaled_realCoef _ (hT.self_conj κ hκ h).2.1,
          (hT.self_conj κ hκ h).2.2⟩
      self_conj_flip := fun κ hκ h0 h =>
        ⟨(hT.self_conj_flip κ hκ h0 h).1, (hT.self_conj_flip κ hκ h0 h).2.1,
          scaled_conjReflectFixed _ _ (hT.self_conj_flip κ hκ h0 h).1 (hS.self_conj_flip_scales κ hκ h0 h).1
            (hT.self_conj_flip κ hκ h0 h).2.2.1,
          scaled_conjReflectFixed _ _ (hT.self_conj_flip κ hκ h0 h).2.1 (hS.self_conj_flip_scales κ hκ h0 h).2
            (hT.self_conj_flip κ hκ h0 h).2.2.2⟩ }

end GivenShape

end CertCell

end Breakdown
