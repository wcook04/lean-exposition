import Breakdown.FracCell.EnergyHeightParts

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy.HeightRows

open CellAnalysis CellFormula SteadyCert Assembly

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}

theorem poly_mem (Q : ℕ) (pt ps : Polynomial ℝ) (ht : pt.natDegree ≤ Q) (hs : ps.natDegree ≤ Q) :
    (fun p : ℝ × ℝ => ((pt.eval p.1 * ps.eval p.2 : ℝ) : ℂ)) ∈ polyFn Q Q := by
  refine ⟨fun i k => ((pt.coeff i * ps.coeff k : ℝ) : ℂ), fun p => ?_⟩
  show ((pt.eval p.1 * ps.eval p.2 : ℝ) : ℂ) = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
    ((pt.coeff j * ps.coeff l : ℝ) : ℂ) * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ)
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le ht), Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hs),
    ← Fin.sum_univ_eq_sum_range (fun i => pt.coeff i * p.1 ^ i),
    ← Fin.sum_univ_eq_sum_range (fun k => ps.coeff k * p.2 ^ k), Finset.sum_mul_sum]
  push_cast
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))

theorem expand (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (hB : IsCellBases K B) (n : modes)
    (C : Fin 3 → Fin 3 → ℂ) (F : ℝ × ℝ → ℂ) (u : D → ℂ)
    (hrow : ∀ j l : Fin (Q + 1), rowApply (lowRow I n C j l) u = B.coef K F j l)
    (hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect)
    (pt ps : Polynomial ℝ) (ht : pt.natDegree ≤ Q) (hs : ps.natDegree ≤ Q) :
    rowApply (lowPairRow K B I n C (fun p => K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2)) u
      = ∫ p in K.rect, ((K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2 : ℝ) : ℂ) * F p := by
  have hsum : rowApply (lowPairRow K B I n C (fun p => K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2)) u
      = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), ((rectIntegral K (fun p => basisFn B j l p *
          (K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2)) : ℝ) : ℂ) * B.coef K F j l := by
    simp only [← hrow, rowApply, lowPairRow, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun d _ => by ring))
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hlw := HeightProj.continuous_lineWeight K
  have hbc : ∀ j l : ℕ, Continuous (fun p : ℝ × ℝ => basisFn B j l p) := fun j l =>
    ((HeightProj.continuous_triPoly B.radialCoef j).comp continuous_fst).mul
      ((HeightProj.continuous_triPoly B.heightCoef l).comp continuous_snd)
  have hwc : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2) :=
    ((hlw.comp continuous_fst).mul ((Polynomial.continuous pt).comp continuous_fst)).mul
      ((Polynomial.continuous ps).comp continuous_snd)
  set P : ℝ × ℝ → ℂ := fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), B.coef K F j l * ((basisFn B j l p : ℝ) : ℂ)
    with hP
  have hPc : Continuous P := by
    simp only [hP]
    refine continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun l _ => ?_))
    exact continuous_const.mul (Complex.continuous_ofReal.comp (hbc j l))
  have hint1 := hF (fun r => pt.eval r) (fun z => ps.eval z) (Polynomial.continuous pt) (Polynomial.continuous ps)
  have hint2 : IntegrableOn (fun p => ((K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2 : ℝ) : ℂ) * P p) K.rect :=
    ((Complex.continuous_ofReal.comp hwc).mul hPc).continuousOn.integrableOn_compact hcomp
  have horth := HeightProj.proj_orth K B hB Q F hF _ (poly_mem Q pt ps ht hs)
  have e1 : ∫ p in K.rect, ((K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2 : ℝ) : ℂ) * F p
      = ∫ p in K.rect, ((K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2 : ℝ) : ℂ) * P p := by
    have h0 : ∫ p in K.rect, (((K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2 : ℝ) : ℂ) * F p
        - ((K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2 : ℝ) : ℂ) * P p) = 0 := by
      refine Eq.trans ?_ horth
      unfold CellBox.pairOn CellBox.lineWeightFn
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [hP, Complex.conj_ofReal]
      push_cast
      ring
    rw [integral_sub hint1 hint2] at h0
    exact sub_eq_zero.mp h0
  rw [hsum, e1]
  have e2 : (fun p => ((K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2 : ℝ) : ℂ) * P p)
      = fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), B.coef K F j l *
          ((basisFn B j l p * (K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2) : ℝ) : ℂ) := by
    funext p
    simp only [hP, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))
  have hint3 : ∀ j l : Fin (Q + 1), IntegrableOn (fun p : ℝ × ℝ =>
      ((basisFn B j l p * (K.lineWeight p.1 * pt.eval p.1 * ps.eval p.2) : ℝ) : ℂ)) K.rect := fun j l =>
    (Complex.continuous_ofReal.comp ((hbc j l).mul hwc)).continuousOn.integrableOn_compact hcomp
  rw [e2, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [integral_const_mul, integral_complex_ofReal, mul_comm]
      rfl
    · intro l _; exact (hint3 j l).const_mul _
  · intro j _; exact integrable_finsetSum _ (fun l _ => (hint3 j l).const_mul _)

theorem inner_rows (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (hK : IsCellBox K)
    (hB : IsCellBases K B) (hr : 0 < K.r₁) (n : modes) (C : Fin 3 → Fin 3 → ℂ) (F dF : ℝ × ℝ → ℂ)
    (hpair : HeightWeakPair K F dF) (u : D → ℂ)
    (hrow : ∀ j l : Fin (Q + 1), rowApply (lowRow I n C j l) u = B.coef K F j l) (i : Fin Q × Fin Q) :
    rowApply (lowPairRow K B I n C
        (fun p => -heightSlope (fun p' => heightInnerWeight K p' * monomial i.1 i.2 p') p)) u
      = ∫ p in K.rect, (heightInnerWeight K p : ℂ) * dF p * ((monomial i.1 i.2 p : ℝ) : ℂ) := by
  have hlw1 : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, hr.ne']
  have hd : K.z₂ - K.z₁ ≠ 0 := by linarith [hK.z_order.2]
  have hrefZ : ∀ z, K.refZ z = 2 / (K.z₂ - K.z₁) * z + -(K.z₁ + K.z₂) / (K.z₂ - K.z₁) := fun z => by
    unfold CellBox.refZ; field_simp; ring
  have hz1 : K.refZ K.z₁ = -1 := by unfold CellBox.refZ; field_simp; ring
  have hz2 : K.refZ K.z₂ = 1 := by unfold CellBox.refZ; field_simp; ring
  set polT : Polynomial ℝ := (Polynomial.X - Polynomial.C K.r₁) * Polynomial.X ^ (i.1 : ℕ) with hpolT
  set polS : Polynomial ℝ := (1 - (Polynomial.C (2 / (K.z₂ - K.z₁)) * Polynomial.X
    + Polynomial.C (-(K.z₁ + K.z₂) / (K.z₂ - K.z₁))) ^ 2) * Polynomial.X ^ (i.2 : ℕ) with hpolS
  have hT : ∀ r, polT.eval r = (r - K.r₁) * r ^ (i.1 : ℕ) := fun r => by simp [hpolT]
  have hS : ∀ z, polS.eval z = (1 - K.refZ z ^ 2) * z ^ (i.2 : ℕ) := fun z => by simp [hpolS, hrefZ]
  have hSd : ∀ z, deriv (fun z => polS.eval z) z = polS.derivative.eval z := fun z => Polynomial.deriv polS
  have hTdeg : polT.natDegree ≤ Q := by
    rw [hpolT]
    have h1 := (Polynomial.natDegree_mul_le (p := Polynomial.X - Polynomial.C K.r₁)
      (q := Polynomial.X ^ (i.1 : ℕ))).trans (add_le_add (Polynomial.natDegree_X_sub_C_le K.r₁)
        (Polynomial.natDegree_X_pow_le (R := ℝ) (i.1 : ℕ)))
    have := i.1.2
    omega
  have hSdeg : (-polS.derivative).natDegree ≤ Q := by
    rw [Polynomial.natDegree_neg]
    have h0 : polS.natDegree ≤ 2 + (i.2 : ℕ) := by
      rw [hpolS]
      compute_degree!
    have := Polynomial.natDegree_derivative_le polS
    have := i.2.2
    omega
  have hφ : (fun p : ℝ × ℝ => -heightSlope (fun p' => heightInnerWeight K p' * monomial i.1 i.2 p') p)
      = fun p => K.lineWeight p.1 * polT.eval p.1 * (-polS.derivative).eval p.2 := by
    funext p
    unfold heightSlope
    have e : (fun z => heightInnerWeight K (p.1, z) * monomial i.1 i.2 (p.1, z))
        = fun z => polT.eval p.1 * polS.eval z := by
      funext z; simp only [heightInnerWeight, monomial, hT, hS]; ring
    rw [e, deriv_const_mul _ polS.differentiableAt, hSd, hlw1, Polynomial.eval_neg]
    ring
  have hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect := by
    intro t s ht hs
    exact (hpair (fun r => K.lineWeight r * t r) s ((HeightProj.continuous_lineWeight K).mul ht) hs
      (Or.inl hr)).1
  rw [hφ, expand K B I hB n C F u hrow hF polT (-polS.derivative) hTdeg hSdeg]
  have hw := (hpair (fun r => polT.eval r) (fun z => polS.eval z) (Polynomial.continuous _)
    (Polynomial.continuous _) (Or.inl hr)).2.2
    (by rw [show (fun z => polS.eval z) = fun z => (1 - K.refZ z ^ 2) * z ^ (i.2 : ℕ) from funext hS]
        unfold CellBox.refZ; fun_prop)
    (by rw [hS, hz1]; ring) (by rw [hS, hz2]; ring)
  have lhs : ∫ p in K.rect, ((K.lineWeight p.1 * polT.eval p.1 * (-polS.derivative).eval p.2 : ℝ) : ℂ) * F p
      = -∫ p in K.rect, ((polT.eval p.1 * deriv (fun z => polS.eval z) p.2 : ℝ) : ℂ) * F p := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [hlw1, hSd, Polynomial.eval_neg]
    push_cast
    ring
  rw [lhs, ← hw]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [heightInnerWeight, monomial, hT, hS]
  push_cast
  ring

theorem rowApply_add (f g : D → ℂ) (u : D → ℂ) :
    rowApply (fun d => f d + g d) u = rowApply f u + rowApply g u := by
  simp only [rowApply, add_mul, Finset.sum_add_distrib]

theorem rowApply_mul (c : ℂ) (f : D → ℂ) (u : D → ℂ) :
    rowApply (fun d => c * f d) u = c * rowApply f u := by
  simp only [rowApply, mul_assoc, Finset.mul_sum]

theorem rowApply_sum {ι : Type} [Fintype ι] (f : ι → D → ℂ) (u : D → ℂ) :
    rowApply (fun d => ∑ k, f k d) u = ∑ k, rowApply (f k) u := by
  simp only [rowApply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem pow_expand (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (q j : ℕ) (hj : j ≤ q) (r : ℝ) :
    r ^ j = ∑ j' : Fin (q + 1), radialMoment K B j j' * B.radialPoly j' r := by
  obtain ⟨a, ha⟩ := HeightProj.pow_span B.radialCoef (fun j => (hB.radial_leading j).ne') q j hj
  have ha' : ∀ x : ℝ, x ^ j = ∑ j' : Fin (q + 1), a j' * B.radialPoly j' x := ha
  have hc : ∀ k : ℕ, Continuous (B.radialPoly k) := fun k => HeightProj.continuous_triPoly B.radialCoef k
  have hm : ∀ j' : Fin (q + 1), radialMoment K B j j' = a j' := by
    intro j'
    unfold radialMoment
    have e : (fun r => K.lineWeight r * r ^ j * B.radialPoly j' r) = fun r => ∑ k : Fin (q + 1),
        a k * (K.lineWeight r * B.radialPoly k r * B.radialPoly j' r) := by
      funext r; rw [ha' r, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e, integral_finsetSum]
    · simp only [integral_const_mul, hB.radial_orthonormal]
      rw [Finset.sum_eq_single j']
      · simp
      · intro b _ hb; simp [Fin.val_eq_val, hb]
      · simp
    · intro k _
      exact (((HeightProj.continuous_lineWeight K).mul (hc k)).mul (hc j')).integrableOn_Icc.const_mul _
  rw [ha' r]
  simp only [hm]

theorem outer_rows (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (hK : IsCellBox K)
    (hB : IsCellBases K B) (hqQ : q + 1 ≤ Q) (n : modes) (C : Fin 3 → Fin 3 → ℂ) (F dF : ℝ × ℝ → ℂ)
    (hpair : HeightWeakPair K F dF) (u : D → ℂ)
    (hrow : ∀ j l : Fin (Q + 1), rowApply (lowRow I n C j l) u = B.coef K F j l)
    (hface : ∀ (e : Fin 2) (j : Fin (q + 1)),
      rowApply (heightFaceComp I n C e j) u = heightFaceMoment K F dF e (B.radialPoly j))
    (i : Fin (q + 1) × Fin (Q + 1)) :
    rowApply (heightOuterRow K B I n C i.1 i.2) u
      = ∫ p in K.rect, ((p.1 : ℝ) : ℂ) * ((K.refZ p.2 : ℂ) * dF p) * ((monomial i.1 i.2 p : ℝ) : ℂ) := by
  have hz : K.z₁ < K.z₂ := hK.z_order.2
  have hd : K.z₂ - K.z₁ ≠ 0 := by linarith
  have hd' : K.z₁ - K.z₂ ≠ 0 := by linarith
  have hrefZ : ∀ z, K.refZ z = 2 / (K.z₂ - K.z₁) * z + -(K.z₁ + K.z₂) / (K.z₂ - K.z₁) := fun z => by
    unfold CellBox.refZ; field_simp; ring
  have hz1 : K.refZ K.z₁ = -1 := by unfold CellBox.refZ; field_simp; ring
  have hz2 : K.refZ K.z₂ = 1 := by unfold CellBox.refZ; field_simp; ring
  have hJ : (i.1 : ℕ) + 1 ≤ Q := by have := i.1.2; omega
  have hL : (i.2 : ℕ) ≤ Q := by have := i.2.2; omega
  have hside : ∀ t₀ : ℝ → ℝ, Continuous t₀ →
      (0 < K.r₁ ∨ ∃ t₁ : ℝ → ℝ, Continuous t₁ ∧ ∀ r, r * t₀ r = r * t₁ r) :=
    fun t₀ h => Or.inr ⟨t₀, h, fun r => rfl⟩
  have hside' : ∀ t₀ : ℝ → ℝ, Continuous t₀ →
      (0 < K.r₁ ∨ ∃ t₁ : ℝ → ℝ, Continuous t₁ ∧ ∀ r, K.lineWeight r * t₀ r = r * t₁ r) := by
    intro t₀ h
    by_cases h0 : K.r₁ = 0
    · exact Or.inr ⟨t₀, h, fun r => by simp [CellBox.lineWeight, h0]⟩
    · exact Or.inl (lt_of_le_of_ne hK.r_order.1 (Ne.symm h0))
  have hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect := by
    intro t s ht hs
    exact (hpair (fun r => K.lineWeight r * t r) s ((HeightProj.continuous_lineWeight K).mul ht) hs
      (hside' t ht)).1
  set α₁ : ℝ := 1 / (K.z₂ - K.z₁) with hα₁
  set α₀ : ℝ := 1 / (K.z₁ - K.z₂) with hα₀
  set A : ℝ := K.z₂ ^ (i.2 : ℕ) with hA
  set Bz : ℝ := K.z₁ ^ (i.2 : ℕ) with hBz
  have face1 : ∀ t : ℝ → ℝ, heightFaceMoment K F dF 1 t = ∫ p in K.rect,
      (((α₁ : ℝ) : ℂ) * F p + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p) * ((p.1 * t p.1 : ℝ) : ℂ) := by
    intro t
    simp only [heightFaceMoment, if_true, heightStripMoment, edgeSign, if_pos hz, one_mul,
      min_eq_right hz.le, max_eq_left hz.le]
    rfl
  have face0 : ∀ t : ℝ → ℝ, heightFaceMoment K F dF 0 t = -∫ p in K.rect,
      (((α₀ : ℝ) : ℂ) * F p + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p) * ((p.1 * t p.1 : ℝ) : ℂ) := by
    intro t
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    simp only [heightFaceMoment, if_neg h01, heightStripMoment, edgeSign, if_neg (not_lt.mpr hz.le),
      min_eq_left hz.le, max_eq_right hz.le, neg_one_mul]
    rfl
  have hX : ∀ (αc : ℝ) (o : ℝ) (c : ℝ) (t₀ : ℝ → ℝ), Continuous t₀ → IntegrableOn (fun p : ℝ × ℝ =>
      (((αc : ℝ) : ℂ) * F p + (((p.2 - o) / c : ℝ) : ℂ) * dF p) * ((p.1 * t₀ p.1 : ℝ) : ℂ)) K.rect := by
    intro αc o c t₀ ht₀
    have h1 := (hpair (fun r => r * t₀ r) (fun _ => αc) (by fun_prop) continuous_const (hside t₀ ht₀)).1
    have h2 := (hpair (fun r => r * t₀ r) (fun z => (z - o) / c) (by fun_prop) (by fun_prop) (hside t₀ ht₀)).2.1
    refine (h1.add h2).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [Pi.add_apply]; push_cast; ring
  have hcP : ∀ k : ℕ, Continuous (B.radialPoly k) := fun k => HeightProj.continuous_triPoly B.radialCoef k
  have hfaces : ∑ j' : Fin (q + 1), ((radialMoment K B i.1 j' : ℝ) : ℂ) *
      (((A : ℝ) : ℂ) * heightFaceMoment K F dF 1 (B.radialPoly j')
        + ((Bz : ℝ) : ℂ) * heightFaceMoment K F dF 0 (B.radialPoly j'))
      = ∫ p in K.rect, (((A : ℝ) : ℂ) * ((((α₁ : ℝ) : ℂ) * F p + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p))
          - ((Bz : ℝ) : ℂ) * ((((α₀ : ℝ) : ℂ) * F p + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p)))
          * ((p.1 * p.1 ^ (i.1 : ℕ) : ℝ) : ℂ) := by
    have e : ∀ p : ℝ × ℝ, (((A : ℝ) : ℂ) * ((((α₁ : ℝ) : ℂ) * F p + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p))
          - ((Bz : ℝ) : ℂ) * ((((α₀ : ℝ) : ℂ) * F p + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p)))
          * ((p.1 * p.1 ^ (i.1 : ℕ) : ℝ) : ℂ)
        = ∑ j' : Fin (q + 1), ((radialMoment K B i.1 j' : ℝ) : ℂ) *
          (((A : ℝ) : ℂ) * (((((α₁ : ℝ) : ℂ) * F p + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p))
              * ((p.1 * B.radialPoly j' p.1 : ℝ) : ℂ))
            - ((Bz : ℝ) : ℂ) * (((((α₀ : ℝ) : ℂ) * F p + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p))
              * ((p.1 * B.radialPoly j' p.1 : ℝ) : ℂ))) := by
      intro p
      rw [pow_expand K B hB q i.1 (by omega) p.1]
      push_cast
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j' _ => by ring)
    simp_rw [e]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [integral_const_mul, integral_sub, integral_const_mul, integral_const_mul, face1, face0]
      · ring
      · exact (hX α₁ K.z₁ (K.z₂ - K.z₁) _ (hcP j')).const_mul _
      · exact (hX α₀ K.z₂ (K.z₁ - K.z₂) _ (hcP j')).const_mul _
    · intro j' _
      exact (((hX α₁ K.z₁ (K.z₂ - K.z₁) _ (hcP j')).const_mul _).sub
        ((hX α₀ K.z₂ (K.z₁ - K.z₂) _ (hcP j')).const_mul _)).const_mul _
  have hsplit : rowApply (heightOuterRow K B I n C i.1 i.2) u = ∑ j' : Fin (q + 1), ((radialMoment K B i.1 j' : ℝ) : ℂ) *
      (((A : ℝ) : ℂ) * heightFaceMoment K F dF 1 (B.radialPoly j')
        + ((Bz : ℝ) : ℂ) * heightFaceMoment K F dF 0 (B.radialPoly j'))
      + rowApply (lowPairRow K B I n C
          (fun p => -heightSlope (fun p' => p'.1 * K.refZ p'.2 * monomial i.1 i.2 p') p)) u := by
    unfold heightOuterRow
    rw [rowApply_add, rowApply_sum]
    simp only [rowApply_mul, rowApply_add, hface]
    rfl
  set polR : Polynomial ℝ := (Polynomial.C (2 / (K.z₂ - K.z₁)) * Polynomial.X
    + Polynomial.C (-(K.z₁ + K.z₂) / (K.z₂ - K.z₁))) * Polynomial.X ^ (i.2 : ℕ) with hpolR
  have hR : ∀ z, polR.eval z = K.refZ z * z ^ (i.2 : ℕ) := fun z => by simp [hpolR, hrefZ]
  have hRdeg : (-polR.derivative).natDegree ≤ Q := by
    rw [Polynomial.natDegree_neg]
    have h0 : polR.natDegree ≤ 1 + (i.2 : ℕ) := by
      rw [hpolR]
      compute_degree!
    have := Polynomial.natDegree_derivative_le polR
    omega
  have hslope : ∀ p : ℝ × ℝ, heightSlope (fun p' => p'.1 * K.refZ p'.2 * monomial i.1 i.2 p') p
      = p.1 * p.1 ^ (i.1 : ℕ) * polR.derivative.eval p.2 := by
    intro p
    unfold heightSlope
    have e : (fun z => (p.1, z).1 * K.refZ (p.1, z).2 * monomial i.1 i.2 (p.1, z))
        = fun z => (p.1 * p.1 ^ (i.1 : ℕ)) * polR.eval z := by
      funext z; simp only [monomial, hR]; ring
    rw [e, deriv_const_mul _ polR.differentiableAt, Polynomial.deriv]
  have hlow : rowApply (lowPairRow K B I n C
      (fun p => -heightSlope (fun p' => p'.1 * K.refZ p'.2 * monomial i.1 i.2 p') p)) u
      = ∫ p in K.rect, ((-(p.1 * p.1 ^ (i.1 : ℕ) * polR.derivative.eval p.2) : ℝ) : ℂ) * F p := by
    by_cases h0 : K.r₁ = 0
    · have hφ : (fun p : ℝ × ℝ => -heightSlope (fun p' => p'.1 * K.refZ p'.2 * monomial i.1 i.2 p') p)
          = fun p => K.lineWeight p.1 * (Polynomial.X ^ (i.1 : ℕ) : Polynomial ℝ).eval p.1
              * (-polR.derivative).eval p.2 := by
        funext p; rw [hslope]
        simp only [CellBox.lineWeight, if_pos h0, Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
        ring
      rw [hφ, expand K B I hB n C F u hrow hF _ _ (by
        have := Polynomial.natDegree_X_pow_le (R := ℝ) (i.1 : ℕ); omega) hRdeg]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [CellBox.lineWeight, if_pos h0, Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
      push_cast; ring
    · have hφ : (fun p : ℝ × ℝ => -heightSlope (fun p' => p'.1 * K.refZ p'.2 * monomial i.1 i.2 p') p)
          = fun p => K.lineWeight p.1 * (Polynomial.X ^ ((i.1 : ℕ) + 1) : Polynomial ℝ).eval p.1
              * (-polR.derivative).eval p.2 := by
        funext p; rw [hslope]
        simp only [CellBox.lineWeight, if_neg h0, Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
        ring
      rw [hφ, expand K B I hB n C F u hrow hF _ _ (by
        have := Polynomial.natDegree_X_pow_le (R := ℝ) ((i.1 : ℕ) + 1); omega) hRdeg]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [CellBox.lineWeight, if_neg h0, Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
      push_cast; ring
  set polS : Polynomial ℝ := polR - Polynomial.C A * (Polynomial.C α₁ * (Polynomial.X - Polynomial.C K.z₁))
    + Polynomial.C Bz * (Polynomial.C α₀ * (Polynomial.X - Polynomial.C K.z₂)) with hpolS
  have hS : ∀ z, polS.eval z = K.refZ z * z ^ (i.2 : ℕ) - A * (α₁ * (z - K.z₁)) + Bz * (α₀ * (z - K.z₂)) :=
    fun z => by simp [hpolS, hR]
  have hSd : ∀ z, deriv (fun z => polS.eval z) z = polR.derivative.eval z - A * α₁ + Bz * α₀ := by
    intro z; rw [Polynomial.deriv]; simp [hpolS]
  have hw := (hpair (fun r => r * r ^ (i.1 : ℕ)) (fun z => polS.eval z) (by fun_prop)
    (Polynomial.continuous _) (hside _ (by fun_prop))).2.2
    (by rw [show (fun z => polS.eval z) = fun z => K.refZ z * z ^ (i.2 : ℕ) - A * (α₁ * (z - K.z₁))
          + Bz * (α₀ * (z - K.z₂)) from funext hS]
        unfold CellBox.refZ; fun_prop)
    (by rw [hS, hz1, hα₀, hBz]; field_simp; ring)
    (by rw [hS, hz2, hα₁, hA]; field_simp; ring)
  have iW1 := (hpair (fun r => r * r ^ (i.1 : ℕ)) (fun z => polS.eval z) (by fun_prop)
    (Polynomial.continuous _) (hside _ (by fun_prop))).2.1
  have iW2 := (hpair (fun r => r * r ^ (i.1 : ℕ)) (fun z => deriv (fun z => polS.eval z) z) (by fun_prop)
    (by simp only [hSd]; fun_prop) (hside _ (by fun_prop))).1
  have iT := (hpair (fun r => r * r ^ (i.1 : ℕ)) (fun z => K.refZ z * z ^ (i.2 : ℕ)) (by fun_prop)
    (by unfold CellBox.refZ; fun_prop) (hside _ (by fun_prop))).2.1
  have iL2 := (hpair (fun r => r * r ^ (i.1 : ℕ)) (fun z => -polR.derivative.eval z) (by fun_prop)
    (by fun_prop) (hside _ (by fun_prop))).1
  have iL1 : IntegrableOn (fun p : ℝ × ℝ => (((A : ℝ) : ℂ) * ((((α₁ : ℝ) : ℂ) * F p
      + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * dF p))
      - ((Bz : ℝ) : ℂ) * ((((α₀ : ℝ) : ℂ) * F p + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * dF p)))
      * ((p.1 * p.1 ^ (i.1 : ℕ) : ℝ) : ℂ)) K.rect := by
    refine IntegrableOn.congr_fun (((hX α₁ K.z₁ (K.z₂ - K.z₁) _ (continuous_pow (i.1 : ℕ))).const_mul
      ((A : ℝ) : ℂ)).sub ((hX α₀ K.z₂ (K.z₁ - K.z₂) _ (continuous_pow (i.1 : ℕ))).const_mul ((Bz : ℝ) : ℂ)))
      (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    rw [Pi.sub_apply]; ring
  rw [hsplit, hfaces, hlow, ← integral_add iL1 (iL2.congr_fun (fun p _ => by push_cast; ring)
    (measurableSet_Icc.prod measurableSet_Icc))]
  have hW : ∫ p in K.rect, (((p.1 * p.1 ^ (i.1 : ℕ) * polS.eval p.2 : ℝ) : ℂ) * dF p
      + ((p.1 * p.1 ^ (i.1 : ℕ) * deriv (fun z => polS.eval z) p.2 : ℝ) : ℂ) * F p) = 0 := by
    rw [integral_add iW1 iW2, hw, neg_add_cancel]
  have hT : ∫ p in K.rect, ((p.1 : ℝ) : ℂ) * ((K.refZ p.2 : ℂ) * dF p) * ((monomial i.1 i.2 p : ℝ) : ℂ)
      = ∫ p in K.rect, ((p.1 * p.1 ^ (i.1 : ℕ) * (K.refZ p.2 * p.2 ^ (i.2 : ℕ)) : ℝ) : ℂ) * dF p := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [monomial]; push_cast; ring
  have iW : IntegrableOn (fun p : ℝ × ℝ => ((p.1 * p.1 ^ (i.1 : ℕ) * polS.eval p.2 : ℝ) : ℂ) * dF p
      + ((p.1 * p.1 ^ (i.1 : ℕ) * deriv (fun z => polS.eval z) p.2 : ℝ) : ℂ) * F p) K.rect := iW1.add iW2
  rw [hT, ← sub_zero (∫ p in K.rect, ((p.1 * p.1 ^ (i.1 : ℕ) * (K.refZ p.2 * p.2 ^ (i.2 : ℕ)) : ℝ) : ℂ) * dF p),
    ← hW, ← integral_sub iT iW]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  have hdC : ((K.z₂ : ℂ) - K.z₁) ≠ 0 := by exact_mod_cast hd
  have hdC' : ((K.z₁ : ℂ) - K.z₂) ≠ 0 := by exact_mod_cast hd'
  simp only [hSd]
  simp only [hS, hα₁, hα₀]
  push_cast
  field_simp
  ring

end Breakdown.CellCert.CellEnergy.HeightRows
