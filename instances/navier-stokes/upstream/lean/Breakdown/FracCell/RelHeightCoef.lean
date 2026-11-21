import Mathlib
import Breakdown.FracCell.StCoordsProof
import Breakdown.FracCell.HeightModeIbp

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

namespace Internal.RelHeightCoef

section
variable (a : ℕ → ℕ → ℝ) (z₁ z₂ : ℝ)

def hp (l : ℕ) : ℝ[X] := ∑ i ∈ Finset.range (l + 1), C (a l i) * X ^ i

theorem hp_eval (l : ℕ) (z : ℝ) : (hp a l).eval z = ∑ i ∈ Finset.range (l + 1), a l i * z ^ i := by
  simp [hp, eval_finsetSum]

theorem hp_natDegree (l : ℕ) : (hp a l).natDegree ≤ l := by
  unfold hp
  refine natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
  have := Finset.mem_range.1 hi
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem hp_coeff (l : ℕ) : (hp a l).coeff l = a l l := by
  simp [hp, coeff_C_mul, coeff_X_pow]

variable {a z₁ z₂}

theorem span (hlead : ∀ l, a l l ≠ 0) : ∀ d (q : ℝ[X]), q.natDegree ≤ d →
    ∃ c : ℕ → ℝ, ∀ z, q.eval z = ∑ i ∈ Finset.range (d + 1), c i * (hp a i).eval z := by
  intro d
  induction d with
  | zero =>
    intro q hq
    refine ⟨fun _ => q.coeff 0 / a 0 0, fun z => ?_⟩
    have h0 := hlead 0
    rw [eq_C_of_natDegree_le_zero hq]
    simp [hp]
    field_simp
  | succ d ih =>
    intro q hq
    have ha : a (d + 1) (d + 1) ≠ 0 := hlead _
    set q' := q - C (q.coeff (d + 1) / a (d + 1) (d + 1)) * hp a (d + 1) with hq'def
    have hq' : q'.natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      simp only [q', coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (d + 1) N with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq h),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hp_natDegree a _) h)]
        ring
      · have hN' : N = d + 1 := by omega
        subst hN'
        rw [hp_coeff]
        field_simp
        ring
    obtain ⟨c, hc⟩ := ih q' hq'
    refine ⟨fun i => if i = d + 1 then q.coeff (d + 1) / a (d + 1) (d + 1) else c i, fun z => ?_⟩
    have e1 : q.eval z = q'.eval z + q.coeff (d + 1) / a (d + 1) (d + 1) * (hp a (d + 1)).eval z := by
      simp [q']
    have e2 : ∑ i ∈ Finset.range (d + 1), c i * (hp a i).eval z = ∑ i ∈ Finset.range (d + 1),
        (if i = d + 1 then q.coeff (d + 1) / a (d + 1) (d + 1) else c i) * (hp a i).eval z :=
      Finset.sum_congr rfl (fun i hi => by rw [if_neg (by have := Finset.mem_range.1 hi; omega)])
    rw [e1, hc z, Finset.sum_range_succ _ (d + 1)]
    beta_reduce
    rw [e2]
    simp

theorem pair_of_span (horth : ∀ l l', ∫ z in z₁..z₂, (hp a l).eval z * (hp a l').eval z = if l = l' then 1 else 0)
    {d : ℕ} {q : ℝ[X]} {c : ℕ → ℝ}
    (hc : ∀ z, q.eval z = ∑ i ∈ Finset.range (d + 1), c i * (hp a i).eval z) (m : ℕ) :
    ∫ z in z₁..z₂, q.eval z * (hp a m).eval z = if m < d + 1 then c m else 0 := by
  simp_rw [hc, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (show Continuous (fun z => c i * eval z (hp a i) * eval z (hp a m)) from
      (continuous_const.mul (hp a i).continuous).mul (hp a m).continuous).intervalIntegrable _ _)]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul, horth]
  simp [Finset.mem_range]


variable (z₁ z₂) in
def zp : ℝ[X] :=
  C (1 - ((z₁ + z₂) / (z₂ - z₁)) ^ 2) + C (2 * (2 / (z₂ - z₁)) * ((z₁ + z₂) / (z₂ - z₁))) * X
    - C ((2 / (z₂ - z₁)) ^ 2) * X ^ 2

theorem zp_eval (z : ℝ) : (zp z₁ z₂).eval z = 1 - ((2 * z - z₁ - z₂) / (z₂ - z₁)) ^ 2 := by
  simp [zp]
  ring

theorem zp_left (hz : z₁ < z₂) : (zp z₁ z₂).eval z₁ = 0 := by
  have h : z₂ - z₁ ≠ 0 := sub_ne_zero.2 hz.ne'
  rw [zp_eval, show 2 * z₁ - z₁ - z₂ = -(z₂ - z₁) by ring, neg_div, div_self h]
  norm_num

theorem zp_right (hz : z₁ < z₂) : (zp z₁ z₂).eval z₂ = 0 := by
  have h : z₂ - z₁ ≠ 0 := sub_ne_zero.2 hz.ne'
  rw [zp_eval, show 2 * z₂ - z₁ - z₂ = z₂ - z₁ by ring, div_self h]
  norm_num

theorem zp_natDegree : (zp z₁ z₂).natDegree ≤ 2 := by
  unfold zp
  compute_degree

theorem zp_coeff : (zp z₁ z₂).coeff 2 = -(2 / (z₂ - z₁)) ^ 2 := by
  simp only [zp, coeff_add, coeff_sub, coeff_C, coeff_C_mul, coeff_X, coeff_X_pow]
  norm_num

variable (a z₁ z₂) in
def gp (l : ℕ) : ℝ[X] := zp z₁ z₂ * derivative (hp a l)

variable (a z₁ z₂) in
def tp (l : ℕ) : ℝ[X] := -derivative (gp a z₁ z₂ l)

theorem gp_natDegree (l : ℕ) : (gp a z₁ z₂ l).natDegree ≤ l + 1 := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h0 : derivative (hp a 0) = 0 :=
      derivative_of_natDegree_zero (Nat.le_zero.1 (hp_natDegree a 0))
    simp [gp, h0]
  · refine natDegree_mul_le.trans ?_
    have h1 := zp_natDegree (z₁ := z₁) (z₂ := z₂)
    have h2 := (natDegree_derivative_le (hp a l)).trans (Nat.sub_le_sub_right (hp_natDegree a l) 1)
    omega

theorem tp_natDegree (l : ℕ) : (tp a z₁ z₂ l).natDegree ≤ l := by
  unfold tp
  rw [natDegree_neg]
  exact (natDegree_derivative_le _).trans (by have := gp_natDegree (a := a) (z₁ := z₁) (z₂ := z₂) l; omega)

theorem tp_coeff {l : ℕ} (hl : 1 ≤ l) :
    (tp a z₁ z₂ l).coeff l = l * (l + 1) * (2 / (z₂ - z₁)) ^ 2 * a l l := by
  have hd : (derivative (hp a l)).natDegree ≤ l - 1 :=
    (natDegree_derivative_le _).trans (Nat.sub_le_sub_right (hp_natDegree a l) 1)
  have key : (gp a z₁ z₂ l).coeff (l + 1) = (zp z₁ z₂).coeff 2 * (derivative (hp a l)).coeff (l - 1) := by
    rw [show l + 1 = 2 + (l - 1) by omega]
    exact coeff_mul_add_eq_of_natDegree_le zp_natDegree hd
  have hc : ((l - 1 : ℕ) : ℝ) + 1 = l := by
    rw [Nat.cast_sub hl]
    ring
  unfold tp
  rw [coeff_neg, coeff_derivative, key, zp_coeff, coeff_derivative, show l - 1 + 1 = l by omega, hp_coeff, hc]
  ring

theorem ibp (p q : ℝ[X]) (h1 : p.eval z₁ * q.eval z₁ = 0) (h2 : p.eval z₂ * q.eval z₂ = 0) :
    ∫ z in z₁..z₂, p.eval z * (derivative q).eval z = -∫ z in z₁..z₂, (derivative p).eval z * q.eval z := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => p.hasDerivAt x) (fun x _ => q.hasDerivAt x)
    ((derivative p).continuous.intervalIntegrable _ _) ((derivative q).continuous.intervalIntegrable _ _), h1, h2]
  ring

variable (hlead : ∀ l, a l l ≠ 0)
  (horth : ∀ l l', ∫ z in z₁..z₂, (hp a l).eval z * (hp a l').eval z = if l = l' then 1 else 0)
include hlead horth

theorem orthog {q : ℝ[X]} {d m : ℕ} (hq : q.natDegree ≤ d) (hm : d < m) :
    ∫ z in z₁..z₂, q.eval z * (hp a m).eval z = 0 := by
  obtain ⟨c, hc⟩ := span hlead d q hq
  rw [pair_of_span horth hc, if_neg (by omega)]

theorem expand {q : ℝ[X]} {d : ℕ} (hq : q.natDegree ≤ d) (z : ℝ) :
    q.eval z = ∑ i ∈ Finset.range (d + 1), (∫ w in z₁..z₂, q.eval w * (hp a i).eval w) * (hp a i).eval z := by
  obtain ⟨c, hc⟩ := span hlead d q hq
  rw [hc z]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [pair_of_span horth hc, if_pos (Finset.mem_range.1 hi)]

theorem pair_lead {l : ℕ} (hl : 1 ≤ l) {q : ℝ[X]} (hq : q.natDegree ≤ l) :
    ∫ z in z₁..z₂, q.eval z * (hp a l).eval z = q.coeff l * ∫ z in z₁..z₂, z ^ l * (hp a l).eval z := by
  set r := q - C (q.coeff l) * X ^ l with hrdef
  have hr : r.natDegree ≤ l - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [r, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge l N with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq h), if_neg (by omega)]
      ring
    · have hN' : N = l := by omega
      subst hN'
      simp
  have e : ∀ z, q.eval z * (hp a l).eval z = r.eval z * (hp a l).eval z + q.coeff l * (z ^ l * (hp a l).eval z) := by
    intro z
    simp [r]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (f := fun z => eval z r * eval z (hp a l))
      (g := fun z => q.coeff l * (z ^ l * eval z (hp a l)))
      ((show Continuous (fun z => eval z r * eval z (hp a l)) from
        r.continuous.mul (hp a l).continuous).intervalIntegrable _ _)
      ((show Continuous (fun z => q.coeff l * (z ^ l * eval z (hp a l))) from
        continuous_const.mul ((continuous_pow l).mul (hp a l).continuous)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, orthog hlead horth hr (by omega : l - 1 < l)]
  ring


theorem tp_sym (hz : z₁ < z₂) {i l : ℕ} (hil : i < l) :
    ∫ z in z₁..z₂, (tp a z₁ z₂ l).eval z * (hp a i).eval z = 0 := by
  have A : ∫ z in z₁..z₂, (tp a z₁ z₂ l).eval z * (hp a i).eval z =
      -∫ z in z₁..z₂, (hp a i).eval z * (derivative (gp a z₁ z₂ l)).eval z := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun z _ => ?_)
    simp [tp]
    ring
  have B1 : ∫ z in z₁..z₂, (hp a i).eval z * (derivative (gp a z₁ z₂ l)).eval z =
      -∫ z in z₁..z₂, (derivative (hp a i)).eval z * (gp a z₁ z₂ l).eval z :=
    ibp _ _ (by simp [gp, zp_left hz]) (by simp [gp, zp_right hz])
  have C1 : ∫ z in z₁..z₂, (derivative (hp a i)).eval z * (gp a z₁ z₂ l).eval z =
      ∫ z in z₁..z₂, (gp a z₁ z₂ i).eval z * (derivative (hp a l)).eval z := by
    refine intervalIntegral.integral_congr (fun z _ => ?_)
    simp [gp]
    ring
  have D1 : ∫ z in z₁..z₂, (gp a z₁ z₂ i).eval z * (derivative (hp a l)).eval z =
      -∫ z in z₁..z₂, (derivative (gp a z₁ z₂ i)).eval z * (hp a l).eval z :=
    ibp _ _ (by simp [gp, zp_left hz]) (by simp [gp, zp_right hz])
  have E1 : ∫ z in z₁..z₂, (derivative (gp a z₁ z₂ i)).eval z * (hp a l).eval z =
      -∫ z in z₁..z₂, (tp a z₁ z₂ i).eval z * (hp a l).eval z := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun z _ => ?_)
    simp [tp]
  rw [A, B1, C1, D1, E1, orthog hlead horth (tp_natDegree i) hil]
  simp

theorem tp_eigen (hz : z₁ < z₂) {l : ℕ} (hl : 1 ≤ l) (z : ℝ) :
    (tp a z₁ z₂ l).eval z = l * (l + 1) * (2 / (z₂ - z₁)) ^ 2 * (hp a l).eval z := by
  rw [expand hlead horth (tp_natDegree l) z, Finset.sum_range_succ,
    Finset.sum_eq_zero (fun i hi => by rw [tp_sym hlead horth hz (Finset.mem_range.1 hi), zero_mul]),
    pair_lead hlead horth hl (tp_natDegree l), tp_coeff hl]
  have h1 := pair_lead hlead horth hl (hp_natDegree a l)
  rw [horth l l, if_pos rfl, hp_coeff] at h1
  linear_combination (-((l : ℝ) * (l + 1) * (2 / (z₂ - z₁)) ^ 2 * (hp a l).eval z)) * h1

theorem hp_of_gp (hz : z₁ < z₂) {l : ℕ} (hl : 1 ≤ l) (z : ℝ) :
    (hp a l).eval z = -(1 / ((l : ℝ) * (l + 1) * (2 / (z₂ - z₁)) ^ 2)) * (derivative (gp a z₁ z₂ l)).eval z := by
  have h := tp_eigen hlead horth hz hl z
  have hpos : (0 : ℝ) < (l : ℝ) * (l + 1) * (2 / (z₂ - z₁)) ^ 2 := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have : 0 < z₂ - z₁ := sub_pos.2 hz
    positivity
  simp only [tp, eval_neg] at h
  have hD : (derivative (gp a z₁ z₂ l)).eval z = -((l : ℝ) * (l + 1) * (2 / (z₂ - z₁)) ^ 2 * (hp a l).eval z) := by
    linarith
  rw [hD, neg_mul_neg, ← mul_assoc, one_div, inv_mul_cancel₀ hpos.ne', one_mul]

theorem gp_expand {l Q : ℕ} (hlQ : l + 1 ≤ Q) (z : ℝ) :
    (gp a z₁ z₂ l).eval z = ∑ i ∈ Finset.range (Q + 1),
      (∫ w in z₁..z₂, (gp a z₁ z₂ l).eval w * (hp a i).eval w) * (hp a i).eval z :=
  expand hlead horth ((gp_natDegree l).trans hlQ) z

end

theorem coef_height (hIbp : HeightModeIbpStatement) {m : ℕ} {n : ℤ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsSecondOrderField m v G H) {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    (a : Fin 3) (j : ℕ) {l Q : ℕ} (hl : 1 ≤ l) (hlQ : l + 1 ≤ Q) :
    B.coef K (fun p => modeVec m n v p.1 p.2 a) j l =
      ∑ i ∈ Finset.range (Q + 1),
        (((∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z) /
          heightEigen K l : ℝ) : ℂ) * B.coef K (gradMode m n G a 2) j i := by
  have hlead : ∀ l, B.heightCoef l l ≠ 0 := fun l => (hB.height_leading l).ne'
  have hz : K.z₁ < K.z₂ := hK.z_order.2
  have hpe : ∀ l z, (hp B.heightCoef l).eval z = B.heightPoly l z := by
    intro l z
    rw [hp_eval]
    rfl
  have hpf : ∀ l, B.heightPoly l = fun z => (hp B.heightCoef l).eval z := fun l => funext fun z => (hpe l z).symm
  have horth : ∀ l l', ∫ z in K.z₁..K.z₂, (hp B.heightCoef l).eval z * (hp B.heightCoef l').eval z =
      if l = l' then 1 else 0 := by
    intro l l'
    simp only [hpe]
    rw [intervalIntegral.integral_of_le hz.le, ← integral_Icc_eq_integral_Ioc]
    exact hB.height_orthonormal l l'
  have hstiff : ∀ i, ∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z =
      ∫ z in K.z₁..K.z₂, (gp B.heightCoef K.z₁ K.z₂ l).eval z * (hp B.heightCoef i).eval z := by
    intro i
    rw [intervalIntegral.integral_of_le hz.le, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
    rw [hpf l, Polynomial.deriv, ← hpe i]
    simp only [gp, eval_mul, zp_eval, CellBox.refZ]
  have hR : Continuous (B.radialPoly j) := by
    unfold CellBases.radialPoly
    fun_prop
  have hH : ∀ i, Continuous (B.heightPoly i) := fun i => by
    rw [hpf i]
    exact (hp B.heightCoef i).continuous
  set g : ℝ → ℝ := fun z => (gp B.heightCoef K.z₁ K.z₂ l).eval z with hgdef
  have hgz1 : g K.z₁ = 0 := by simp [g, gp, zp_left hz]
  have hgz2 : g K.z₂ = 0 := by simp [g, gp, zp_right hz]
  have hderiv : ∀ z, deriv g z = (derivative (gp B.heightCoef K.z₁ K.z₂ l)).eval z := fun z => Polynomial.deriv _
  have hg1 : ContDiff ℝ 1 g := contDiff_one_iff_deriv.2 ⟨(gp B.heightCoef K.z₁ K.z₂ l).differentiable, by
    rw [show deriv g = fun z => (derivative (gp B.heightCoef K.z₁ K.z₂ l)).eval z from funext hderiv]
    exact Polynomial.continuous _⟩
  obtain ⟨hint, hibp⟩ := hIbp m n v G H hv K hK a
  have key := hibp (B.radialPoly j) g hR hg1 hgz1 hgz2
  have heig : heightEigen K l = (l : ℝ) * (l + 1) * (2 / (K.z₂ - K.z₁)) ^ 2 := rfl
  have e1 : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) =
      ((-(1 / heightEigen K l) : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
        ((B.radialPoly j p.1 * deriv g p.2 : ℝ) : ℂ)) := by
    intro p
    rw [← hpe, hp_of_gp hlead horth hz hl, hderiv, heig]
    push_cast
    ring
  have hexp : ∀ z, g z = ∑ i ∈ Finset.range (Q + 1),
      (∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z) *
        B.heightPoly i z := by
    intro z
    show (gp B.heightCoef K.z₁ K.z₂ l).eval z = _
    rw [gp_expand hlead horth hlQ z]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hstiff i, hpe]
  have e2 : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((B.radialPoly j p.1 * g p.2 : ℝ) : ℂ) =
      ∑ i ∈ Finset.range (Q + 1),
        (((∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z) : ℝ) : ℂ) *
          ((K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((B.radialPoly j p.1 * B.heightPoly i p.2 : ℝ) : ℂ)) := by
    intro p
    rw [hexp p.2, Finset.mul_sum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hintI : ∀ i ∈ Finset.range (Q + 1), Integrable (fun p : ℝ × ℝ =>
      (((∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z) : ℝ) : ℂ) *
          ((K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((B.radialPoly j p.1 * B.heightPoly i p.2 : ℝ) : ℂ)))
        (volume.restrict K.rect) := by
    intro i _
    refine Integrable.const_mul ?_ _
    have hc : Continuous (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly i p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hR.comp continuous_fst).mul ((hH i).comp continuous_snd))
    exact hint.mul_continuousOn hc.continuousOn hcomp
  unfold CellBases.coef
  rw [integral_congr_ae (ae_of_all _ e1), integral_const_mul, key, integral_congr_ae (ae_of_all _ e2),
    integral_finsetSum _ hintI, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul]
  push_cast
  ring


theorem pair_sub {D : Type*} [Fintype D] (A : D → ℂ) (s : Finset ℕ) (c : ℕ → ℂ) (Bf : ℕ → D → ℂ) (T : D → ℂ) :
    ∑ d, (A - ∑ i ∈ s, c i • Bf i) d * T d = ∑ d, A d * T d - ∑ i ∈ s, c i * ∑ d, Bf i d * T d := by
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun d _ => by ring)))

theorem pair_unit (L : CellLayout) (d₀ : L.Datum) (T : L.Datum → ℂ) : ∑ d, L.unitAt d₀ d * T d = T d₀ := by
  simp [CellLayout.unitAt, Pi.single_apply]

theorem row_holds (hIbp : HeightModeIbpStatement) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (B : CellBases) (L : CellLayout) (hL : IsCellLayout c K S B L) (x : FieldTuple k) (hx : IsAdmissible c x)
    (ρ : L.modes × Fin 3 × Fin L.degCoef × Fin L.degCoef) :
    (∑ d, L.relationRow (Sum.inr (Sum.inl ρ)) d * L.trueData x d) = 0 := by
  obtain ⟨n, a, j, l⟩ := ρ
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl]
  split_ifs with hl0
  · simp
  have hj := j.isLt
  have hl := l.isLt
  rw [pair_sub]
  have hv : L.velocityAt n a j l = L.unitAt (CellDatum.lowVelocity n a ⟨j, hj⟩ ⟨l, hl⟩) := by
    unfold CellLayout.velocityAt
    rw [dif_pos ⟨hj, hl⟩]
  have hs : ∀ i ∈ Finset.range (L.degCoef + 1), ∑ d, L.strainAt n a 2 j i d * L.trueData x d =
      L.bases.coef L.box (L.gradModeOf n x a 2) j i := by
    intro i hi
    unfold CellLayout.strainAt
    rw [dif_pos ⟨by omega, Finset.mem_range.1 hi⟩, pair_unit]
    rfl
  rw [hv, pair_unit, Finset.sum_congr rfl (fun i hi => by rw [hs i hi])]
  have hT : L.trueData x (CellDatum.lowVelocity n a ⟨j, hj⟩ ⟨l, hl⟩) =
      L.bases.coef L.box (fun p => modeVec L.order n x.1 p.1 p.2 a) j l := rfl
  rw [hT, sub_eq_zero]
  have hord : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := hL.order_eq ▸ hx.1
  rw [coef_height hIbp hord (hL.box_eq ▸ hL.box_valid) (hL.box_eq ▸ hL.bases_eq ▸ hL.bases_valid) a j
    (Nat.one_le_iff_ne_zero.2 hl0) (by omega : (l : ℕ) + 1 ≤ L.degCoef)]
  rfl

end Internal.RelHeightCoef

open Internal.RelHeightCoef in
theorem relHeightCoef_of (hIbp : HeightModeIbpStatement) : RelHeightCoefStatement :=
  fun c K S B L hL x hx ρ => row_holds hIbp c K S B L hL x hx ρ

theorem relHeightCoef_holds : RelHeightCoefStatement := relHeightCoef_of heightModeIbp_holds

end Breakdown.CellCert.CellFormula
