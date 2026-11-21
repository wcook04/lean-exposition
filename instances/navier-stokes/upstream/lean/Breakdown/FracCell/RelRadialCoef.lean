import Breakdown.FracCell.StCoordsProof

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

def ModeRadialPartsStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable v volume → MemLp v 6 volume → AEStronglyMeasurable G volume →
    Integrable (fun y => entrySq (G y)) → IsWeakGradientOf v G →
    ∀ (n : ℤ) (a : Fin 3) (r₁ r₂ z₁ z₂ : ℝ), 0 ≤ r₁ → r₁ < r₂ → z₁ < z₂ →
    (∀ g q : ℝ → ℝ, ContinuousOn g (Set.Icc r₁ r₂) → Continuous q →
      IntegrableOn (fun p : ℝ × ℝ => ((p.1 * g p.1 * q p.2 : ℝ) : ℂ) * gradMode m n G a 0 p)
        (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂)) ∧
    ∀ ψ q : ℝ → ℝ, ContDiff ℝ 1 ψ → Continuous q → ψ r₁ = 0 → ψ r₂ = 0 →
      ∫ p in Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂, ((ψ p.1 * q p.2 : ℝ) : ℂ) * gradMode m n G a 0 p =
        -∫ p in Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂, ((deriv ψ p.1 * q p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a

namespace Internal.RelRadialCoef

variable (B : CellBases) (K : CellBox)

def poly (j : ℕ) : ℝ[X] := ∑ i ∈ Finset.range (j + 1), C (B.radialCoef j i) * X ^ i

theorem poly_eval (j : ℕ) (r : ℝ) : (poly B j).eval r = B.radialPoly j r := by
  simp [poly, CellBases.radialPoly, eval_finsetSum]

theorem poly_fun (j : ℕ) : B.radialPoly j = fun r => (poly B j).eval r :=
  funext fun r => (poly_eval B j r).symm

theorem poly_coeff (j n : ℕ) : (poly B j).coeff n = if n < j + 1 then B.radialCoef j n else 0 := by
  simp only [poly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem poly_natDegree (j : ℕ) : (poly B j).natDegree ≤ j := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [poly_coeff, if_neg (by omega)]

open Classical in
def wpoly : ℝ[X] := if K.r₁ = 0 then X else 1

theorem wpoly_eval (r : ℝ) : (wpoly K).eval r = K.lineWeight r := by
  unfold wpoly CellBox.lineWeight
  split_ifs <;> simp

def ip (f g : ℝ[X]) : ℝ := ∫ r in Set.Icc K.r₁ K.r₂, (wpoly K * f * g).eval r

theorem integ (f : ℝ[X]) (a b : ℝ) : IntegrableOn (fun r => f.eval r) (Set.Icc a b) :=
  (Polynomial.continuous f).integrableOn_Icc

theorem ip_sum (s : Finset ℕ) (c : ℕ → ℝ) (P : ℕ → ℝ[X]) (g : ℝ[X]) :
    ip K (∑ i ∈ s, C (c i) * P i) g = ∑ i ∈ s, c i * ip K (P i) g := by
  unfold ip
  have h : ∀ r, (wpoly K * (∑ i ∈ s, C (c i) * P i) * g).eval r =
      ∑ i ∈ s, c i * (wpoly K * P i * g).eval r := by
    intro r
    simp only [Finset.mul_sum, Finset.sum_mul, eval_finsetSum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [eval_mul, eval_C]
    ring
  simp_rw [h]
  rw [integral_finsetSum _ (fun i _ => (integ (wpoly K * P i * g) _ _).const_mul (c i))]
  simp_rw [integral_const_mul]

theorem span (hB : ∀ j, B.radialCoef j j ≠ 0) (D : ℕ) : ∀ f : ℝ[X], f.natDegree ≤ D →
    ∃ c : ℕ → ℝ, f = ∑ i ∈ Finset.range (D + 1), C (c i) * poly B i := by
  induction D with
  | zero =>
    intro f hf
    refine ⟨fun _ => f.coeff 0 / B.radialCoef 0 0, ?_⟩
    apply Polynomial.ext
    intro N
    simp only [zero_add, Finset.sum_range_one, coeff_C_mul, poly_coeff]
    rcases N with _ | N
    · rw [if_pos (by omega), div_mul_cancel₀ _ (hB 0)]
    · rw [if_neg (by omega), mul_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  | succ D ih =>
    intro f hf
    set t := f.coeff (D + 1) / B.radialCoef (D + 1) (D + 1) with ht
    obtain ⟨c, hc⟩ := ih (f - C t * poly B (D + 1)) (by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub, coeff_C_mul, poly_coeff]
      rcases Nat.lt_or_ge (D + 1) N with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), if_neg (by omega)]
        simp
      · have hN' : N = D + 1 := by omega
        subst hN'
        rw [if_pos (by omega), ht, div_mul_cancel₀ _ (hB _), sub_self])
    refine ⟨Function.update c (D + 1) t, ?_⟩
    rw [Finset.sum_range_succ, Function.update_self]
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [Function.update_of_ne (by simp only [Finset.mem_range] at hi; omega)])]
    rw [← hc]
    ring

theorem expand (hB : ∀ j, B.radialCoef j j ≠ 0)
    (horth : ∀ j j', ip K (poly B j) (poly B j') = if j = j' then 1 else 0) (D : ℕ) (f : ℝ[X])
    (hf : f.natDegree ≤ D) :
    f = ∑ i ∈ Finset.range (D + 1), C (ip K f (poly B i)) * poly B i := by
  obtain ⟨c, hc⟩ := span B hB D f hf
  have hck : ∀ k ∈ Finset.range (D + 1), ip K f (poly B k) = c k := by
    intro k hk
    rw [hc, ip_sum]
    simp only [horth, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', if_pos hk]
  calc f = _ := hc
    _ = _ := Finset.sum_congr rfl (fun i hi => by rw [hck i hi])

def rho : ℝ[X] := C (2 / (K.r₂ - K.r₁)) * X - C ((K.r₁ + K.r₂) / (K.r₂ - K.r₁))

theorem rho_eval (r : ℝ) : (rho K).eval r = K.refR r := by
  simp only [rho, eval_sub, eval_mul, eval_C, eval_X, CellBox.refR]
  ring

def Wp : ℝ[X] := wpoly K * (1 - rho K ^ 2)

theorem Wp_left (hK : K.r₁ < K.r₂) : (Wp K).eval K.r₁ = 0 := by
  have hne : K.r₂ - K.r₁ ≠ 0 := by linarith
  have h : K.refR K.r₁ = -1 := by
    unfold CellBox.refR
    field_simp
    ring
  simp [Wp, eval_mul, rho_eval, h]

theorem Wp_right (hK : K.r₁ < K.r₂) : (Wp K).eval K.r₂ = 0 := by
  have hne : K.r₂ - K.r₁ ≠ 0 := by linarith
  have h : K.refR K.r₂ = 1 := by
    unfold CellBox.refR
    field_simp
    ring
  simp [Wp, eval_mul, rho_eval, h]

def Upoly : ℝ[X] := C (4 / K.r₂) - C (4 / K.r₂ ^ 2) * X

open Classical in
def F (j : ℕ) : ℝ[X] :=
  if K.r₁ = 0 then
    Upoly K * derivative (poly B j) + Upoly K * derivative (poly B j)
      + X * derivative (Upoly K * derivative (poly B j))
  else derivative ((1 - rho K ^ 2) * derivative (poly B j))

theorem F_spec (hK : K.r₁ < K.r₂) (j : ℕ) :
    wpoly K * F B K j = derivative (Wp K * derivative (poly B j)) := by
  unfold F Wp wpoly
  split_ifs with h
  · have h2 : K.r₂ ≠ 0 := by rw [h] at hK; exact hK.ne'
    have hU : 1 - rho K ^ 2 = X * Upoly K := by
      apply Polynomial.funext
      intro r
      simp only [rho, Upoly, h, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_one]
      field_simp
      ring
    rw [hU]
    simp only [derivative_mul, derivative_X]
    ring
  · simp

theorem F_natDegree (j : ℕ) : (F B K j).natDegree ≤ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 : derivative (poly B 0) = 0 := by
      apply derivative_of_natDegree_zero
      have := poly_natDegree B 0
      omega
    unfold F
    split_ifs <;> simp [h0]
  · have hP : (derivative (poly B j)).natDegree ≤ j - 1 :=
      (natDegree_derivative_le _).trans (Nat.sub_le_sub_right (poly_natDegree B j) 1)
    have hU : (Upoly K).natDegree ≤ 1 := by
      unfold Upoly
      compute_degree
    have hQ : (1 - rho K ^ 2).natDegree ≤ 2 := by
      unfold rho
      compute_degree
    unfold F
    split_ifs
    · have h1 : (Upoly K * derivative (poly B j)).natDegree ≤ j :=
        (natDegree_mul_le_of_le hU hP).trans (by omega)
      have h2 : (X * derivative (Upoly K * derivative (poly B j))).natDegree ≤ j :=
        (natDegree_mul_le_of_le natDegree_X_le
          ((natDegree_derivative_le _).trans (Nat.sub_le_sub_right h1 1))).trans (by omega)
      exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 h1) h2
    · have h1 : ((1 - rho K ^ 2) * derivative (poly B j)).natDegree ≤ j + 1 :=
        (natDegree_mul_le_of_le hQ hP).trans (by omega)
      exact (natDegree_derivative_le _).trans (by omega)

theorem F_coeff (j : ℕ) (hj : j ≠ 0) :
    (F B K j).coeff j = -(radialEigen K j) * B.radialCoef j j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hd : ∀ n, (derivative (poly B (i + 1))).coeff n =
      (if n + 1 < i + 1 + 1 then B.radialCoef (i + 1) (n + 1) else 0) * ((n : ℝ) + 1) := by
    intro n
    rw [coeff_derivative, poly_coeff]
  unfold F radialEigen
  split_ifs with h
  · simp only [Upoly, coeff_add, coeff_X_mul, coeff_derivative, sub_mul, coeff_sub, mul_assoc,
      coeff_C_mul, hd]
    simp only [h, sub_zero]
    simp
    ring
  · have hQ : 1 - rho K ^ 2 = C (1 - ((K.r₁ + K.r₂) / (K.r₂ - K.r₁)) ^ 2)
        + X * (C (2 * (2 / (K.r₂ - K.r₁)) * ((K.r₁ + K.r₂) / (K.r₂ - K.r₁)))
          + X * C (-(2 / (K.r₂ - K.r₁)) ^ 2)) := by
      apply Polynomial.funext
      intro r
      simp only [rho, eval_sub, eval_mul, eval_C, eval_X, eval_pow, eval_one, eval_add]
      ring
    simp only [coeff_derivative, hQ, add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul, hd]
    simp
    ring

theorem ip_F (hK : K.r₁ < K.r₂) (i j : ℕ) :
    ip K (F B K j) (poly B i) =
      -∫ r in K.r₁..K.r₂, (Wp K * derivative (poly B i) * derivative (poly B j)).eval r := by
  unfold ip
  have h1 : ∀ r, (wpoly K * F B K j * poly B i).eval r =
      (poly B i).eval r * (derivative (Wp K * derivative (poly B j))).eval r := by
    intro r
    rw [← F_spec B K hK j]
    simp only [eval_mul]
    ring
  simp_rw [h1]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hK.le]
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => Polynomial.hasDerivAt _ x)
    (fun x _ => Polynomial.hasDerivAt _ x) ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)]
  simp only [eval_mul, Wp_left K hK, Wp_right K hK, zero_mul, mul_zero, sub_zero, zero_sub]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  ring

theorem eigen (hB : ∀ j, B.radialCoef j j ≠ 0)
    (horth : ∀ j j', ip K (poly B j) (poly B j') = if j = j' then 1 else 0) (hK : K.r₁ < K.r₂)
    (j : ℕ) (hj : j ≠ 0) : F B K j = C (-(radialEigen K j)) * poly B j := by
  have hexp := expand B K hB horth j (F B K j) (F_natDegree B K j)
  have hzero : ∀ i < j, ip K (F B K j) (poly B i) = 0 := by
    intro i hi
    rw [ip_F B K hK i j]
    have hs : ∫ r in K.r₁..K.r₂, (Wp K * derivative (poly B i) * derivative (poly B j)).eval r =
        ∫ r in K.r₁..K.r₂, (Wp K * derivative (poly B j) * derivative (poly B i)).eval r := by
      congr 1
      funext r
      simp only [eval_mul]
      ring
    rw [hs, ← ip_F B K hK j i]
    rw [expand B K hB horth i (F B K i) (F_natDegree B K i), ip_sum]
    apply Finset.sum_eq_zero
    intro k hk
    rw [horth, if_neg (by simp only [Finset.mem_range] at hk; omega), mul_zero]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
    rw [hzero i (by simpa using hi), C_0, zero_mul]), zero_add] at hexp
  have hc := congrArg (fun p => p.coeff j) hexp
  simp only [coeff_C_mul, poly_coeff, if_pos (Nat.lt_succ_self j)] at hc
  rw [F_coeff B K j hj] at hc
  have hv : ip K (F B K j) (poly B j) = -(radialEigen K j) := (mul_right_cancel₀ (hB j) hc).symm
  rw [hv] at hexp
  exact hexp

end Internal.RelRadialCoef


namespace Internal.RelRadialCoef

theorem stiff_eq (L : CellLayout) (j i : ℕ) :
    L.radialStiff j i =
      ip L.box ((1 - rho L.box ^ 2) * derivative (poly L.bases j)) (poly L.bases i) := by
  unfold CellLayout.radialStiff CellLayout.radialInt ip
  congr 1
  funext r
  simp only [poly_fun, Polynomial.deriv, eval_mul, eval_sub, eval_one, eval_pow, wpoly_eval, rho_eval]
  ring

theorem key (L : CellLayout) (hK : IsCellBox L.box) (hB : IsCellBases L.box L.bases)
    (j l : ℕ) (hj : j ≠ 0) (hjD : j < L.degCoef) (V Gm : ℝ × ℝ → ℂ)
    (hint : ∀ i, IntegrableOn (fun p : ℝ × ℝ => (L.box.lineWeight p.1 : ℂ) * Gm p *
      ((L.bases.radialPoly i p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ)) L.box.rect)
    (hparts : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ L.box.r₁ = 0 → ψ L.box.r₂ = 0 →
      ∫ p in L.box.rect, ((ψ p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ) * Gm p =
        -∫ p in L.box.rect, ((deriv ψ p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ) * V p) :
    ∑ i ∈ Finset.range (L.degCoef + 1),
        (((L.radialStiff j i / radialEigen L.box j : ℝ)) : ℂ) * L.bases.coef L.box Gm i l =
      L.bases.coef L.box V j l := by
  have hr : L.box.r₁ < L.box.r₂ := hK.r_order.2
  have hBl : ∀ j, L.bases.radialCoef j j ≠ 0 := fun j => (hB.radial_leading j).ne'
  have horth : ∀ j j', ip L.box (poly L.bases j) (poly L.bases j') = if j = j' then 1 else 0 := by
    intro j j'
    rw [← hB.radial_orthonormal j j']
    unfold ip
    congr 1
    funext r
    simp only [eval_mul, wpoly_eval, poly_eval]
  have hlam0 : radialEigen L.box j ≠ 0 := by
    have hj' : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hs : (0 : ℝ) < 2 / (L.box.r₂ - L.box.r₁) := div_pos two_pos (by linarith)
    unfold radialEigen
    split_ifs
    · exact (mul_pos (mul_pos hj' (by linarith)) (pow_pos hs 2)).ne'
    · exact (mul_pos (mul_pos hj' (by linarith)) (pow_pos hs 2)).ne'
  have hTdeg : ((1 - rho L.box ^ 2) * derivative (poly L.bases j)).natDegree ≤ L.degCoef := by
    have hP : (derivative (poly L.bases j)).natDegree ≤ j - 1 :=
      (natDegree_derivative_le _).trans (Nat.sub_le_sub_right (poly_natDegree L.bases j) 1)
    have hQ : (1 - rho L.box ^ 2).natDegree ≤ 2 := by
      unfold rho
      compute_degree
    exact (natDegree_mul_le_of_le hQ hP).trans (by omega)
  have hTexp := expand L.bases L.box hBl horth L.degCoef _ hTdeg
  have hψT : ∀ r, (Wp L.box * derivative (poly L.bases j)).eval r = L.box.lineWeight r *
      ∑ i ∈ Finset.range (L.degCoef + 1), L.radialStiff j i * L.bases.radialPoly i r := by
    intro r
    have h1 : (Wp L.box * derivative (poly L.bases j)).eval r =
        (wpoly L.box).eval r * ((1 - rho L.box ^ 2) * derivative (poly L.bases j)).eval r := by
      simp only [Wp, eval_mul]
      ring
    rw [h1, wpoly_eval]
    congr 1
    conv_lhs => rw [hTexp]
    simp only [eval_finsetSum, eval_mul, eval_C, poly_eval, stiff_eq]
  have hψd : ∀ r, deriv (fun r => (Wp L.box * derivative (poly L.bases j)).eval r) r =
      -radialEigen L.box j * (L.box.lineWeight r * L.bases.radialPoly j r) := by
    intro r
    rw [Polynomial.deriv, ← F_spec L.bases L.box hr j, eigen L.bases L.box hBl horth hr j hj]
    simp only [eval_mul, eval_C, wpoly_eval, poly_eval]
    ring
  have hsum : ∀ p : ℝ × ℝ, ∑ i ∈ Finset.range (L.degCoef + 1),
      (((L.radialStiff j i / radialEigen L.box j : ℝ)) : ℂ) * ((L.box.lineWeight p.1 : ℂ) * Gm p *
        ((L.bases.radialPoly i p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ)) =
      ((1 / radialEigen L.box j : ℝ) : ℂ) *
        ((((Wp L.box * derivative (poly L.bases j)).eval p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ) * Gm p) := by
    intro p
    rw [hψT p.1]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hC : ((radialEigen L.box j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlam0
  calc ∑ i ∈ Finset.range (L.degCoef + 1),
        (((L.radialStiff j i / radialEigen L.box j : ℝ)) : ℂ) * L.bases.coef L.box Gm i l
      = ∑ i ∈ Finset.range (L.degCoef + 1), ∫ p in L.box.rect,
          (((L.radialStiff j i / radialEigen L.box j : ℝ)) : ℂ) * ((L.box.lineWeight p.1 : ℂ) * Gm p *
            ((L.bases.radialPoly i p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        unfold CellBases.coef
        rw [integral_const_mul]
    _ = ∫ p in L.box.rect, ∑ i ∈ Finset.range (L.degCoef + 1),
          (((L.radialStiff j i / radialEigen L.box j : ℝ)) : ℂ) * ((L.box.lineWeight p.1 : ℂ) * Gm p *
            ((L.bases.radialPoly i p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ)) :=
        (integral_finsetSum _ (fun i _ => (hint i).const_mul _)).symm
    _ = ∫ p in L.box.rect, ((1 / radialEigen L.box j : ℝ) : ℂ) *
          ((((Wp L.box * derivative (poly L.bases j)).eval p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ) * Gm p) := by
        congr 1
        funext p
        exact hsum p
    _ = ((1 / radialEigen L.box j : ℝ) : ℂ) * ∫ p in L.box.rect,
          (((Wp L.box * derivative (poly L.bases j)).eval p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ) * Gm p :=
        integral_const_mul _ _
    _ = ((1 / radialEigen L.box j : ℝ) : ℂ) * -∫ p in L.box.rect,
          ((deriv (fun r => (Wp L.box * derivative (poly L.bases j)).eval r) p.1 *
            L.bases.heightPoly l p.2 : ℝ) : ℂ) * V p := by
        exact congrArg (fun t => ((1 / radialEigen L.box j : ℝ) : ℂ) * t)
          (hparts (fun r => (Wp L.box * derivative (poly L.bases j)).eval r)
            (by simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) (Wp L.box * derivative (poly L.bases j)) 1)
            (by simp [eval_mul, Wp_left L.box hr]) (by simp [eval_mul, Wp_right L.box hr]))
    _ = ((1 / radialEigen L.box j : ℝ) : ℂ) * -∫ p in L.box.rect,
          ((-radialEigen L.box j : ℝ) : ℂ) * ((L.box.lineWeight p.1 : ℂ) * V p *
            ((L.bases.radialPoly j p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ)) := by
        congr 3
        funext p
        rw [hψd]
        push_cast
        ring
    _ = L.bases.coef L.box V j l := by
        rw [integral_const_mul]
        unfold CellBases.coef
        push_cast
        field_simp

theorem sum_unit (L : CellLayout) (d0 : L.Datum) (f : L.Datum → ℂ) :
    ∑ d, L.unitAt d0 d * f d = f d0 := by
  simp [CellLayout.unitAt, Pi.single_apply]

end Internal.RelRadialCoef

open Internal.RelRadialCoef in
theorem relRadialCoef_of (h : ModeRadialPartsStatement) : RelRadialCoefStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, a, j, l⟩ := ρ
  have hK : IsCellBox L.box := hL.box_eq ▸ hL.box_valid
  have hB : IsCellBases L.box L.bases := by
    rw [hL.box_eq, hL.bases_eq]
    exact hL.bases_valid
  simp only [CellLayout.relationRow, Sum.elim_inl]
  split_ifs with hj0
  · simp
  · obtain ⟨hI, hP⟩ := h L.order x.1 x.2.1 hx.1.measurable_velocity hx.1.velocity_six
      hx.1.measurable_gradient hx.1.gradient_two hx.1.weak_gradient n a L.box.r₁ L.box.r₂ L.box.z₁ L.box.z₂
      hK.r_order.1 hK.r_order.2 hK.z_order.2
    have hq : Continuous (L.bases.heightPoly l) := by
      unfold CellBases.heightPoly
      fun_prop
    have hint : ∀ i, IntegrableOn (fun p : ℝ × ℝ => (L.box.lineWeight p.1 : ℂ) * L.gradModeOf n x a 0 p *
        ((L.bases.radialPoly i p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ)) L.box.rect := by
      intro i
      by_cases h0 : L.box.r₁ = 0
      · have := hI (L.bases.radialPoly i) (L.bases.heightPoly l)
          (by rw [poly_fun]; exact (Polynomial.continuous _).continuousOn) hq
        refine this.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        simp only [CellBox.lineWeight, h0, if_true, CellLayout.gradModeOf]
        push_cast
        ring
      · have hpos : 0 < L.box.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
        have := hI (fun r => L.bases.radialPoly i r / r) (L.bases.heightPoly l)
          (by
            rw [poly_fun]
            exact ContinuousOn.div (Polynomial.continuous _).continuousOn continuousOn_id
              (fun r hr => (lt_of_lt_of_le hpos hr.1).ne')) hq
        refine this.congr_fun (fun p hp => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        have hp1 : p.1 ≠ 0 := (lt_of_lt_of_le hpos hp.1.1).ne'
        have hp1' : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hp1
        simp only [CellBox.lineWeight, h0, if_false, CellLayout.gradModeOf]
        push_cast
        field_simp
        try ring
    have hparts : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ L.box.r₁ = 0 → ψ L.box.r₂ = 0 →
        ∫ p in L.box.rect, ((ψ p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ) * L.gradModeOf n x a 0 p =
          -∫ p in L.box.rect, ((deriv ψ p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ) * L.velMode n x a p :=
      fun ψ hψ h1 h2 => hP ψ (L.bases.heightPoly l) hψ hq h1 h2
    have hkey := key L hK hB j l (fun h' => hj0 h') j.isLt (L.velMode n x a) (L.gradModeOf n x a 0) hint hparts
    have hv : ∑ d, L.velocityAt n a j l d * L.trueData x d = L.bases.coef L.box (L.velMode n x a) j l := by
      unfold CellLayout.velocityAt
      rw [dif_pos ⟨j.isLt, l.isLt⟩, sum_unit]
      rfl
    have hs : ∀ i ∈ Finset.range (L.degCoef + 1), ∑ d, L.strainAt n a 0 i l d * L.trueData x d =
        L.bases.coef L.box (L.gradModeOf n x a 0) i l := by
      intro i hi
      unfold CellLayout.strainAt
      rw [dif_pos ⟨Finset.mem_range.1 hi, by omega⟩, sum_unit]
      rfl
    have hsplit : ∀ d, (L.velocityAt n a j l - ∑ i ∈ Finset.range (L.degCoef + 1),
        (((L.radialStiff j i / radialEigen L.box j : ℝ)) : ℂ) • L.strainAt n a 0 i l) d * L.trueData x d =
        L.velocityAt n a j l d * L.trueData x d - ∑ i ∈ Finset.range (L.degCoef + 1),
          (((L.radialStiff j i / radialEigen L.box j : ℝ)) : ℂ) * (L.strainAt n a 0 i l d * L.trueData x d) := by
      intro d
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [Finset.sum_congr rfl (fun d _ => hsplit d), Finset.sum_sub_distrib, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [hv, Finset.sum_congr rfl (fun i hi => by rw [hs i hi]), hkey, sub_self]

end CellFormula

end CellCert

end Breakdown
