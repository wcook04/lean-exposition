import Breakdown.FracCell.ReductionPointwiseDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

private lemma pair_integrable {w : ℝ → ℝ} {a b : ℝ} (hw : ContinuousOn w (Set.Icc a b))
    (P Q : Polynomial ℝ) :
    IntegrableOn (fun x => w x * P.eval x * Q.eval x) (Set.Icc a b) :=
  ((hw.mul P.continuous.continuousOn).mul Q.continuous.continuousOn).integrableOn_compact
    isCompact_Icc

private lemma pair_comm (w : ℝ → ℝ) (a b : ℝ) (P Q : Polynomial ℝ) :
    polyPair w a b P Q = polyPair w a b Q P := by
  unfold polyPair
  congr 1
  funext x
  ring

private lemma pair_sub_left {w : ℝ → ℝ} {a b : ℝ} (hw : ContinuousOn w (Set.Icc a b))
    (P Q R : Polynomial ℝ) :
    polyPair w a b (P - Q) R = polyPair w a b P R - polyPair w a b Q R := by
  unfold polyPair
  rw [← integral_sub (pair_integrable hw P R) (pair_integrable hw Q R)]
  congr 1
  funext x
  rw [Polynomial.eval_sub]
  ring

private lemma pair_smul_left (w : ℝ → ℝ) (a b : ℝ) (c : ℝ) (P R : Polynomial ℝ) :
    polyPair w a b (c • P) R = c * polyPair w a b P R := by
  unfold polyPair
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [Polynomial.eval_smul, smul_eq_mul]
  ring

private lemma pair_sum_left {w : ℝ → ℝ} {a b : ℝ} (hw : ContinuousOn w (Set.Icc a b))
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) (R : Polynomial ℝ) :
    polyPair w a b (∑ i ∈ s, f i) R = ∑ i ∈ s, polyPair w a b (f i) R := by
  unfold polyPair
  rw [← integral_finsetSum s (fun i _ => pair_integrable hw (f i) R)]
  congr 1
  funext x
  rw [Polynomial.eval_finsetSum, Finset.mul_sum, Finset.sum_mul]

private lemma pair_self_pos {w : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hw0 : ∀ x ∈ Set.Icc a b, 0 ≤ w x) (hwpos : ∀ x ∈ Set.Ioo a b, 0 < w x)
    (hw : ContinuousOn w (Set.Icc a b)) (q : Polynomial ℝ) (hq : q ≠ 0) :
    0 < polyPair w a b q q := by
  have hnn : 0 ≤ polyPair w a b q q := by
    unfold polyPair
    refine setIntegral_nonneg measurableSet_Icc (fun x hx => ?_)
    rw [mul_assoc]
    exact mul_nonneg (hw0 x hx) (mul_self_nonneg _)
  refine lt_of_le_of_ne hnn (fun h0 => hq ?_)
  have hae : (fun x => w x * q.eval x * q.eval x) =ᵐ[volume.restrict (Set.Icc a b)] 0 := by
    refine (setIntegral_eq_zero_iff_of_nonneg_ae ?_ (pair_integrable hw q q)).1 h0.symm
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    show (0 : ℝ) ≤ w x * q.eval x * q.eval x
    rw [mul_assoc]
    exact mul_nonneg (hw0 x hx) (mul_self_nonneg _)
  have hae' : (fun x => w x * q.eval x * q.eval x) =ᵐ[volume.restrict (Set.Ioo a b)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Icc_self hae
  have hcont : ContinuousOn (fun x => w x * q.eval x * q.eval x) (Set.Ioo a b) :=
    ((hw.mono Set.Ioo_subset_Icc_self).mul q.continuous.continuousOn).mul
      q.continuous.continuousOn
  have heq := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hcont continuousOn_const
  refine Polynomial.eq_zero_of_infinite_isRoot q ((Set.Ioo_infinite hab).mono (fun x hx => ?_))
  have h1 : w x * q.eval x * q.eval x = 0 := heq hx
  rw [mul_assoc] at h1
  have h2 := (mul_eq_zero.1 h1).resolve_left (hwpos x hx).ne'
  exact mul_self_eq_zero.1 h2

private lemma family_eq (w : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    orthoFamily w a b n =
      (Real.sqrt (polyPair w a b
        (Polynomial.X ^ n - ∑ i : Fin n, polyPair w a b (Polynomial.X ^ n) (orthoFamily w a b i) •
          orthoFamily w a b i)
        (Polynomial.X ^ n - ∑ i : Fin n, polyPair w a b (Polynomial.X ^ n) (orthoFamily w a b i) •
          orthoFamily w a b i)))⁻¹ •
      (Polynomial.X ^ n - ∑ i : Fin n, polyPair w a b (Polynomial.X ^ n) (orthoFamily w a b i) •
          orthoFamily w a b i) := by
  rw [orthoFamily]

private lemma family_step {w : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hw0 : ∀ x ∈ Set.Icc a b, 0 ≤ w x) (hwpos : ∀ x ∈ Set.Ioo a b, 0 < w x)
    (hw : ContinuousOn w (Set.Icc a b)) (n : ℕ)
    (ih : ∀ m < n, ∀ m' < n,
      polyPair w a b (orthoFamily w a b m) (orthoFamily w a b m') = if m = m' then 1 else 0)
    (hdeg : ∀ m < n, (orthoFamily w a b m).natDegree = m) :
    (orthoFamily w a b n).natDegree = n ∧ 0 < (orthoFamily w a b n).coeff n ∧
      (∀ m < n, polyPair w a b (orthoFamily w a b n) (orthoFamily w a b m) = 0) ∧
      polyPair w a b (orthoFamily w a b n) (orthoFamily w a b n) = 1 := by
  have hfam := family_eq w a b n
  set S : Polynomial ℝ := ∑ i : Fin n, polyPair w a b (Polynomial.X ^ n) (orthoFamily w a b i) •
    orthoFamily w a b i with hS
  set q : Polynomial ℝ := Polynomial.X ^ n - S with hq
  have hSdeg : S.degree < (Polynomial.X ^ n : Polynomial ℝ).degree := by
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 (fun i _ => ?_)
    refine lt_of_le_of_lt (Polynomial.degree_smul_le _ _)
      (lt_of_le_of_lt Polynomial.degree_le_natDegree ?_)
    rw [hdeg i i.2]
    exact WithBot.coe_lt_coe.2 i.2
  have hmonic : q.Monic := (Polynomial.monic_X_pow n).sub_of_left hSdeg
  have hqdeg : q.natDegree = n := by
    refine Polynomial.natDegree_eq_of_degree_eq_some ?_
    rw [hq, Polynomial.degree_sub_eq_left_of_degree_lt hSdeg, Polynomial.degree_X_pow]
  have hQ : 0 < polyPair w a b q q := pair_self_pos hab hw0 hwpos hw q hmonic.ne_zero
  have hkpos : 0 < (Real.sqrt (polyPair w a b q q))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hQ)
  have horth : ∀ m < n, polyPair w a b q (orthoFamily w a b m) = 0 := by
    intro m hm
    rw [hq, pair_sub_left hw, hS, pair_sum_left hw]
    simp_rw [pair_smul_left]
    rw [Fin.sum_univ_eq_sum_range (fun i => polyPair w a b (Polynomial.X ^ n) (orthoFamily w a b i) *
      polyPair w a b (orthoFamily w a b i) (orthoFamily w a b m)) n]
    rw [Finset.sum_eq_single m]
    · rw [ih m hm m hm, if_pos rfl, mul_one, sub_self]
    · intro i hi hne
      rw [ih i (Finset.mem_range.1 hi) m hm, if_neg hne, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 hm) h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfam, Polynomial.natDegree_smul _ hkpos.ne', hqdeg]
  · have hc := hmonic.coeff_natDegree
    rw [hqdeg] at hc
    rw [hfam, Polynomial.coeff_smul, smul_eq_mul, hc, mul_one]
    exact hkpos
  · intro m hm
    rw [hfam, pair_smul_left, horth m hm, mul_zero]
  · rw [hfam, pair_smul_left, pair_comm w a b q ((Real.sqrt (polyPair w a b q q))⁻¹ • q), pair_smul_left, ← mul_assoc, ← mul_inv,
      Real.mul_self_sqrt hQ.le, inv_mul_cancel₀ hQ.ne']

private lemma delta_of {w : ℝ → ℝ} {a b : ℝ} {m m' : ℕ}
    (hm : (∀ j < m, polyPair w a b (orthoFamily w a b m) (orthoFamily w a b j) = 0) ∧
      polyPair w a b (orthoFamily w a b m) (orthoFamily w a b m) = 1)
    (hm' : (∀ j < m', polyPair w a b (orthoFamily w a b m') (orthoFamily w a b j) = 0) ∧
      polyPair w a b (orthoFamily w a b m') (orthoFamily w a b m') = 1) :
    polyPair w a b (orthoFamily w a b m) (orthoFamily w a b m') = if m = m' then 1 else 0 := by
  rcases lt_trichotomy m m' with h | h | h
  · rw [if_neg h.ne, pair_comm]
    exact hm'.1 m h
  · subst h
    rw [if_pos rfl]
    exact hm.2
  · rw [if_neg h.ne']
    exact hm.1 m' h

theorem orthoFamily_spec : OrthoFamilyStatement := by
  intro w a b hab _ hw0 hwpos hw
  have key : ∀ n, (orthoFamily w a b n).natDegree = n ∧ 0 < (orthoFamily w a b n).coeff n ∧
      (∀ m < n, polyPair w a b (orthoFamily w a b n) (orthoFamily w a b m) = 0) ∧
      polyPair w a b (orthoFamily w a b n) (orthoFamily w a b n) = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      exact family_step hab hw0 hwpos hw n
        (fun m hm m' hm' => delta_of (ih m hm).2.2 (ih m' hm').2.2) (fun m hm => (ih m hm).1)
  intro n
  exact ⟨(key n).1, (key n).2.1, fun n' => delta_of (key n).2.2 (key n').2.2⟩

end Reduction

end CellCert

end Breakdown
