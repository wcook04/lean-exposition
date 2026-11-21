import Breakdown.FracCell.UnresolvedRowClassSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace UnresolvedRowPoint

open CellCert CellCert.CellAnalysis

def tri (a b c : Fin 3 → ℂ) : ℂ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) + a 1 * (b 2 * c 0 - b 0 * c 2) + a 2 * (b 0 * c 1 - b 1 * c 0)

theorem tri_smul (x y z : ℂ) (a b c : Fin 3 → ℂ) :
    tri (fun k => a k * x) (fun k => b k * y) (fun k => c k * z) = x * y * z * tri a b c := by
  simp only [tri]; ring

theorem tri_sum_left {ι : Type*} (s : Finset ι) (a : ι → Fin 3 → ℂ) (b c : Fin 3 → ℂ) :
    tri (fun k => ∑ i ∈ s, a i k) b c = ∑ i ∈ s, tri (a i) b c := by
  simp only [tri, Finset.sum_mul, ← Finset.sum_add_distrib]

theorem tri_sum_mid {ι : Type*} (s : Finset ι) (a c : Fin 3 → ℂ) (b : ι → Fin 3 → ℂ) :
    tri a (fun k => ∑ i ∈ s, b i k) c = ∑ i ∈ s, tri a (b i) c := by
  simp only [tri, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

theorem tri_sum_right {ι : Type*} (s : Finset ι) (a b : Fin 3 → ℂ) (c : ι → Fin 3 → ℂ) :
    tri a b (fun k => ∑ i ∈ s, c i k) = ∑ i ∈ s, tri a b (c i) := by
  simp only [tri, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

theorem dotSq3 (x0 x1 x2 y0 y1 y2 : ℝ) :
    (x0 * y0 + x1 * y1 + x2 * y2) ^ 2 ≤ (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2) := by
  nlinarith [sq_nonneg (x0 * y1 - x1 * y0), sq_nonneg (x0 * y2 - x2 * y0), sq_nonneg (x1 * y2 - x2 * y1)]

theorem cross_sq (b c : Fin 3 → ℂ) :
    vecSq (crossC b c) ≤ vecSq b * vecSq c := by
  have h : vecSq b * vecSq c - vecSq (crossC b c) = ‖b 0 * (starRingEnd ℂ) (c 0) + b 1 * (starRingEnd ℂ) (c 1)
      + b 2 * (starRingEnd ℂ) (c 2)‖ ^ 2 := by
    simp only [vecSq, Fin.sum_univ_three, crossC, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im]
    ring
  nlinarith [sq_nonneg ‖b 0 * (starRingEnd ℂ) (c 0) + b 1 * (starRingEnd ℂ) (c 1) + b 2 * (starRingEnd ℂ) (c 2)‖]

theorem dot_sq (a d : Fin 3 → ℂ) :
    ‖a 0 * d 0 + a 1 * d 1 + a 2 * d 2‖ ^ 2 ≤ vecSq a * vecSq d := by
  have h1 : ‖a 0 * d 0 + a 1 * d 1 + a 2 * d 2‖ ≤ ‖a 0‖ * ‖d 0‖ + ‖a 1‖ * ‖d 1‖ + ‖a 2‖ * ‖d 2‖ := by
    refine (norm_add₃_le).trans ?_
    simp only [norm_mul, le_refl]
  have h0 : 0 ≤ ‖a 0 * d 0 + a 1 * d 1 + a 2 * d 2‖ := norm_nonneg _
  have h2 := dotSq3 ‖a 0‖ ‖a 1‖ ‖a 2‖ ‖d 0‖ ‖d 1‖ ‖d 2‖
  simp only [vecSq, Fin.sum_univ_three]
  nlinarith [pow_le_pow_left₀ h0 h1 2]

theorem tri_eq_dot (a b c : Fin 3 → ℂ) :
    tri a b c = a 0 * crossC b c 0 + a 1 * crossC b c 1 + a 2 * crossC b c 2 := by
  simp [tri, crossC]

theorem tri_sq (a b c : Fin 3 → ℂ) : ‖tri a b c‖ ^ 2 ≤ vecSq a * vecSq b * vecSq c := by
  rw [tri_eq_dot]
  have h1 := dot_sq a (crossC b c)
  have h2 := cross_sq b c
  have ha : 0 ≤ vecSq a := Finset.sum_nonneg (fun _ _ => by positivity)
  calc _ ≤ vecSq a * vecSq (crossC b c) := h1
    _ ≤ vecSq a * (vecSq b * vecSq c) := mul_le_mul_of_nonneg_left h2 ha
    _ = _ := by ring

theorem twoProductBound (ρ x y z : ℝ) (hρ : 0 < ρ) :
    2 * (x + y) * z ≤ 2 * ρ * (x ^ 2 + y ^ 2) + z ^ 2 / ρ := by
  have h : ρ * (2 * (x + y) * z) ≤ ρ * (2 * ρ * (x ^ 2 + y ^ 2) + z ^ 2 / ρ) := by
    have e : ρ * (2 * ρ * (x ^ 2 + y ^ 2) + z ^ 2 / ρ) = 2 * ρ ^ 2 * (x ^ 2 + y ^ 2) + z ^ 2 := by
      field_simp
    rw [e]
    nlinarith [sq_nonneg (ρ * (x + y) - z), sq_nonneg (ρ * (x - y))]
  exact le_of_mul_le_mul_left h hρ

def ee (N : ℕ) (k : ℤ) (j : ℕ) : ℂ :=
  Complex.exp ((((k : ℝ) * (2 * Real.pi * j / N)) : ℝ) * Complex.I)

theorem ee_mul (N : ℕ) (a b : ℤ) (j : ℕ) : ee N a j * ee N b j = ee N (a + b) j := by
  simp only [ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_conj (N : ℕ) (a : ℤ) (j : ℕ) : (starRingEnd ℂ) (ee N a j) = ee N (-a) j := by
  simp only [ee, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem ee_zero (N : ℕ) (j : ℕ) : ee N 0 j = 1 := by
  simp [ee]

theorem ee_pow (N : ℕ) (k : ℤ) (j : ℕ) : ee N k j = (ee N k 1) ^ j := by
  simp only [ee, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem ee_sum (N : ℕ) (hN : 0 < N) (k : ℤ) (hk1 : -(N : ℤ) < k) (hk2 : k < N) :
    ∑ j ∈ Finset.range N, ee N k j = if k = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp [ee_zero]
  · have hx : ee N k 1 ≠ 1 := by
      intro h1
      rw [ee, Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have him := congrArg Complex.im hn
      simp at him
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hk : (k : ℝ) = n * N := by
        field_simp at him
        nlinarith [Real.pi_pos]
      have hk' : k = n * N := by exact_mod_cast hk
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · nlinarith
      · subst hn0; simp at hk'; exact h hk'
      · nlinarith
    have hxN : (ee N k 1) ^ N = 1 := by
      rw [← ee_pow, ee]
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hr : (k : ℝ) * (2 * Real.pi * ((N : ℕ) : ℝ) / N) = k * (2 * Real.pi) := by
        field_simp
      have : ((((k : ℝ) * (2 * Real.pi * (N : ℕ) / N)) : ℝ) : ℂ) * Complex.I = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hr]
        push_cast
        ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [Finset.sum_congr rfl (fun j _ => ee_pow N k j), geom_sum_eq hx, hxN]
    simp


theorem norm_sq_eq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem sampleSumSq (N : ℕ) (hN : 0 < N) (M : Finset ℤ)
    (hM : ∀ m ∈ M, ∀ m' ∈ M, -(N : ℤ) < m + -m' ∧ m + -m' < N) (f : ℤ → ℂ) :
    ∑ j ∈ Finset.range N, ‖∑ m ∈ M, f m * ee N m j‖ ^ 2 = N * ∑ m ∈ M, ‖f m‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  simp only [norm_sq_eq, Complex.ofReal_natCast]
  have key : ∀ j, (∑ m ∈ M, f m * ee N m j) * (starRingEnd ℂ) (∑ m' ∈ M, f m' * ee N m' j)
      = ∑ m ∈ M, ∑ m' ∈ M, (f m * (starRingEnd ℂ) (f m')) * ee N (m + -m') j := by
    intro j
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
    rw [map_mul, ee_conj, ← ee_mul]
    ring
  simp only [key]
  rw [Finset.sum_comm]
  have h2 : ∀ m ∈ M, ∑ j ∈ Finset.range N, ∑ m' ∈ M, (f m * (starRingEnd ℂ) (f m')) * ee N (m + -m') j
      = N * (f m * (starRingEnd ℂ) (f m)) := by
    intro m hm
    rw [Finset.sum_comm]
    have h3 : ∀ m' ∈ M, ∑ j ∈ Finset.range N, (f m * (starRingEnd ℂ) (f m')) * ee N (m + -m') j
        = if m = m' then N * (f m * (starRingEnd ℂ) (f m)) else 0 := by
      intro m' hm'
      rw [← Finset.mul_sum, ee_sum N hN _ (hM m hm m' hm').1 (hM m hm m' hm').2]
      by_cases h : m = m'
      · subst h; simp; ring
      · have : m + -m' ≠ 0 := by omega
        simp [h, this]
    rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq, if_pos hm]
  rw [Finset.sum_congr rfl h2, Finset.mul_sum]

theorem sampleSumVecSq (N : ℕ) (hN : 0 < N) (M : Finset ℤ)
    (hM : ∀ m ∈ M, ∀ m' ∈ M, -(N : ℤ) < m + -m' ∧ m + -m' < N) (f : ℤ → Fin 3 → ℂ) :
    ∑ j ∈ Finset.range N, vecSq (fun b => ∑ m ∈ M, f m b * ee N m j) = N * ∑ m ∈ M, vecSq (f m) := by
  simp only [vecSq]
  rw [Finset.sum_comm]
  simp only [sampleSumSq N hN M hM]
  rw [← Finset.mul_sum, Finset.sum_comm]

theorem expand (N : ℕ) (hN : 0 < N) (F M Bs : Finset ℤ)
    (hfreq : ∀ n ∈ F, ∀ β ∈ Bs, ∀ m ∈ M, -(N : ℤ) < n + β + -m ∧ n + β + -m < N) (X Y Z : ℤ → Fin 3 → ℂ) :
    ∑ j ∈ Finset.range N, tri (fun k => ∑ n ∈ F, X n k * ee N n j) (fun k => ∑ β ∈ Bs, Y β k * ee N β j)
        (fun k => ∑ m ∈ M, Z m k * ee N (-m) j)
      = N * ∑ n ∈ F, ∑ m ∈ M, (if m - n ∈ Bs then tri (X n) (Y (m - n)) (Z m) else 0) := by
  have h1 : ∀ j, tri (fun k => ∑ n ∈ F, X n k * ee N n j) (fun k => ∑ β ∈ Bs, Y β k * ee N β j)
        (fun k => ∑ m ∈ M, Z m k * ee N (-m) j)
      = ∑ n ∈ F, ∑ β ∈ Bs, ∑ m ∈ M, tri (X n) (Y β) (Z m) * ee N (n + β + -m) j := by
    intro j
    refine (tri_sum_left F (fun n k => X n k * ee N n j) _ _).trans ?_
    refine Finset.sum_congr rfl (fun n _ => ?_)
    refine (tri_sum_mid Bs _ _ (fun β k => Y β k * ee N β j)).trans ?_
    refine Finset.sum_congr rfl (fun β _ => ?_)
    refine (tri_sum_right M _ _ (fun m k => Z m k * ee N (-m) j)).trans ?_
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [tri_smul, ← ee_mul, ← ee_mul]
    ring
  simp only [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hs : ∑ j ∈ Finset.range N, ∑ β ∈ Bs, ∑ m ∈ M, tri (X n) (Y β) (Z m) * ee N (n + β + -m) j
      = ∑ m ∈ M, ∑ β ∈ Bs, ∑ j ∈ Finset.range N, tri (X n) (Y β) (Z m) * ee N (n + β + -m) j := by
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl (fun β _ => Finset.sum_comm)).trans ?_
    exact Finset.sum_comm
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have h2 : ∀ β ∈ Bs, ∑ j ∈ Finset.range N, tri (X n) (Y β) (Z m) * ee N (n + β + -m) j
      = if β = m - n then N * tri (X n) (Y β) (Z m) else 0 := by
    intro β hβ
    rw [← Finset.mul_sum, ee_sum N hN _ (hfreq n hn β hβ m hm).1 (hfreq n hn β hβ m hm).2]
    by_cases h : β = m - n
    · have : n + β + -m = 0 := by omega
      simp [h, this]; ring
    · have : n + β + -m ≠ 0 := by omega
      simp [h, this]
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq']
  split_ifs <;> simp

theorem conj_sum_ee (N : ℕ) (M : Finset ℤ) (Ψ : ℤ → Fin 3 → ℂ) (j : ℕ) :
    (fun k => ∑ m ∈ M, conjVec3 (Ψ m) k * ee N (-m) j)
      = conjVec3 (fun k => ∑ m ∈ M, Ψ m k * ee N m j) := by
  funext k
  simp only [conjVec3, map_sum, map_mul, ee_conj]

theorem vecSq_conj (v : Fin 3 → ℂ) : vecSq (conjVec3 v) = vecSq v := by
  simp [vecSq, conjVec3]

theorem vecSq_nonneg (v : Fin 3 → ℂ) : 0 ≤ vecSq v := Finset.sum_nonneg (fun _ _ => by positivity)

theorem le_of_sq_le (a b : ℝ) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra h'
  push Not at h'
  nlinarith

theorem point_bound (ρ A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (o u v w c : Fin 3 → ℂ)
    (hu : vecSq u ≤ A ^ 2) (hw : vecSq w ≤ B ^ 2) :
    2 * ‖tri o u (conjVec3 c) - tri v w (conjVec3 c)‖
      ≤ 2 * ρ * (A ^ 2 * vecSq o + B ^ 2 * vecSq v) + vecSq c / ρ := by
  set x := Real.sqrt (vecSq o)
  set y := Real.sqrt (vecSq v)
  set z := Real.sqrt (vecSq c)
  have hx : x ^ 2 = vecSq o := Real.sq_sqrt (vecSq_nonneg _)
  have hy : y ^ 2 = vecSq v := Real.sq_sqrt (vecSq_nonneg _)
  have hz : z ^ 2 = vecSq c := Real.sq_sqrt (vecSq_nonneg _)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have h1 : ‖tri o u (conjVec3 c)‖ ≤ A * x * z := by
    apply le_of_sq_le _ _ (by positivity)
    have := tri_sq o u (conjVec3 c)
    rw [vecSq_conj] at this
    have ho := vecSq_nonneg o
    have hc := vecSq_nonneg c
    calc _ ≤ vecSq o * vecSq u * vecSq c := this
      _ ≤ vecSq o * A ^ 2 * vecSq c := by gcongr
      _ = (A * x * z) ^ 2 := by rw [mul_pow, mul_pow, hx, hz]; ring
  have h2 : ‖tri v w (conjVec3 c)‖ ≤ B * y * z := by
    apply le_of_sq_le _ _ (by positivity)
    have := tri_sq v w (conjVec3 c)
    rw [vecSq_conj] at this
    have ho := vecSq_nonneg v
    have hc := vecSq_nonneg c
    calc _ ≤ vecSq v * vecSq w * vecSq c := this
      _ ≤ vecSq v * B ^ 2 * vecSq c := by gcongr
      _ = (B * y * z) ^ 2 := by rw [mul_pow, mul_pow, hy, hz]; ring
  have h3 := twoProductBound ρ (A * x) (B * y) z hρ
  have h4 := norm_sub_le (tri o u (conjVec3 c)) (tri v w (conjVec3 c))
  rw [← hx, ← hy, ← hz]
  nlinarith

theorem classConvolutionBound (F M Bs : Finset ℤ) (Ω V U W Ψ : ℤ → Fin 3 → ℂ) (A B ρ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : 0 < ρ)
    (hU : F.Nonempty → ∀ φ : ℝ,
      vecSq (fun b => ∑ β ∈ Bs, U β b * Complex.exp ((((β : ℝ) * φ) : ℝ) * Complex.I)) ≤ A ^ 2)
    (hW : F.Nonempty → ∀ φ : ℝ,
      vecSq (fun b => ∑ β ∈ Bs, W β b * Complex.exp ((((β : ℝ) * φ) : ℝ) * Complex.I)) ≤ B ^ 2) :
    2 * ‖∑ n ∈ F, ∑ m ∈ M, (if m - n ∈ Bs then
        tri (Ω n) (U (m - n)) (conjVec3 (Ψ m)) - tri (V n) (W (m - n)) (conjVec3 (Ψ m)) else 0)‖
      ≤ 2 * ρ * (A ^ 2 * ∑ n ∈ F, vecSq (Ω n) + B ^ 2 * ∑ n ∈ F, vecSq (V n))
        + (∑ m ∈ M, vecSq (Ψ m)) / ρ := by
  rcases F.eq_empty_or_nonempty with hF | hF
  · subst hF
    have : 0 ≤ (∑ m ∈ M, vecSq (Ψ m)) / ρ :=
      div_nonneg (Finset.sum_nonneg (fun _ _ => vecSq_nonneg _)) hρ.le
    simpa using this
  set D := (F ∪ M ∪ Bs).sup Int.natAbs
  set N := 4 * D + 1 with hNdef
  have hN : 0 < N := by omega
  have hb : ∀ k ∈ F ∪ M ∪ Bs, -(D : ℤ) ≤ k ∧ k ≤ D := by
    intro k hk
    have h1 : k.natAbs ≤ D := Finset.le_sup (f := Int.natAbs) hk
    have h2 : |k| ≤ (D : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
    exact abs_le.mp h2
  have hF' : ∀ n ∈ F, -(D : ℤ) ≤ n ∧ n ≤ D := fun n hn => hb n (by simp [hn])
  have hM' : ∀ n ∈ M, -(D : ℤ) ≤ n ∧ n ≤ D := fun n hn => hb n (by simp [hn])
  have hB' : ∀ n ∈ Bs, -(D : ℤ) ≤ n ∧ n ≤ D := fun n hn => hb n (by simp [hn])
  have hNz : (N : ℤ) = 4 * D + 1 := by push_cast [hNdef]; ring
  have pF : ∀ m ∈ F, ∀ m' ∈ F, -(N : ℤ) < m + -m' ∧ m + -m' < N := by
    intro m hm m' hm'; have := hF' m hm; have := hF' m' hm'; omega
  have pM : ∀ m ∈ M, ∀ m' ∈ M, -(N : ℤ) < m + -m' ∧ m + -m' < N := by
    intro m hm m' hm'; have := hM' m hm; have := hM' m' hm'; omega
  have pX : ∀ n ∈ F, ∀ β ∈ Bs, ∀ m ∈ M, -(N : ℤ) < n + β + -m ∧ n + β + -m < N := by
    intro n hn β hβ m hm; have := hF' n hn; have := hB' β hβ; have := hM' m hm; omega
  set X := ∑ n ∈ F, ∑ m ∈ M, (if m - n ∈ Bs then
        tri (Ω n) (U (m - n)) (conjVec3 (Ψ m)) - tri (V n) (W (m - n)) (conjVec3 (Ψ m)) else 0)
  have hexp := expand N hN F M Bs pX Ω U (fun m => conjVec3 (Ψ m))
  have hexp2 := expand N hN F M Bs pX V W (fun m => conjVec3 (Ψ m))
  have hXN : (N : ℂ) * X = ∑ j ∈ Finset.range N,
      (tri (fun k => ∑ n ∈ F, Ω n k * ee N n j) (fun k => ∑ β ∈ Bs, U β k * ee N β j)
          (conjVec3 (fun k => ∑ m ∈ M, Ψ m k * ee N m j))
        - tri (fun k => ∑ n ∈ F, V n k * ee N n j) (fun k => ∑ β ∈ Bs, W β k * ee N β j)
          (conjVec3 (fun k => ∑ m ∈ M, Ψ m k * ee N m j))) := by
    simp only [← conj_sum_ee]
    rw [Finset.sum_sub_distrib, hexp, hexp2, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    split_ifs <;> simp
  have hpt : ∀ j ∈ Finset.range N, 2 * ‖tri (fun k => ∑ n ∈ F, Ω n k * ee N n j) (fun k => ∑ β ∈ Bs, U β k * ee N β j)
          (conjVec3 (fun k => ∑ m ∈ M, Ψ m k * ee N m j))
        - tri (fun k => ∑ n ∈ F, V n k * ee N n j) (fun k => ∑ β ∈ Bs, W β k * ee N β j)
          (conjVec3 (fun k => ∑ m ∈ M, Ψ m k * ee N m j))‖
      ≤ 2 * ρ * (A ^ 2 * vecSq (fun k => ∑ n ∈ F, Ω n k * ee N n j)
          + B ^ 2 * vecSq (fun k => ∑ n ∈ F, V n k * ee N n j))
        + vecSq (fun k => ∑ m ∈ M, Ψ m k * ee N m j) / ρ := by
    intro j _
    exact point_bound ρ A B hA hB hρ _ _ _ _ _ (hU hF _) (hW hF _)
  have hsum := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hsum
  rw [sampleSumVecSq N hN F pF, sampleSumVecSq N hN F pF, sampleSumVecSq N hN M pM] at hsum
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hnorm : ‖(N : ℂ) * X‖ = N * ‖X‖ := by rw [norm_mul]; simp
  have hsum2 : 2 * ∑ j ∈ Finset.range N, ‖tri (fun k => ∑ n ∈ F, Ω n k * ee N n j) (fun k => ∑ β ∈ Bs, U β k * ee N β j)
          (conjVec3 (fun k => ∑ m ∈ M, Ψ m k * ee N m j))
        - tri (fun k => ∑ n ∈ F, V n k * ee N n j) (fun k => ∑ β ∈ Bs, W β k * ee N β j)
          (conjVec3 (fun k => ∑ m ∈ M, Ψ m k * ee N m j))‖ ≥ 2 * (N * ‖X‖) := by
    rw [← hnorm, hXN]
    gcongr
    exact norm_sum_le _ _
  have key : (N : ℝ) * (2 * ‖X‖) ≤ N * (2 * ρ * (A ^ 2 * ∑ n ∈ F, vecSq (Ω n) + B ^ 2 * ∑ n ∈ F, vecSq (V n))
        + (∑ m ∈ M, vecSq (Ψ m)) / ρ) := by
    have e : (N : ℝ) * (2 * ρ * (A ^ 2 * ∑ n ∈ F, vecSq (Ω n) + B ^ 2 * ∑ n ∈ F, vecSq (V n))
        + (∑ m ∈ M, vecSq (Ψ m)) / ρ) = 2 * ρ * (A ^ 2 * (N * ∑ n ∈ F, vecSq (Ω n))) + 2 * ρ * (B ^ 2 * (N * ∑ n ∈ F, vecSq (V n)))
        + N * (∑ m ∈ M, vecSq (Ψ m)) / ρ := by ring
    rw [e]
    linarith
  exact le_of_mul_le_mul_left key hN'

def qterm (o v u w c : Fin 3 → ℂ) : ℂ := tri o u (conjVec3 c) - tri v w (conjVec3 c)

theorem qterm_zero_right (o v u w : Fin 3 → ℂ) : qterm o v u w 0 = 0 := by
  simp [qterm, tri, conjVec3]

theorem qterm_zero_mid (o v c : Fin 3 → ℂ) : qterm o v 0 0 c = 0 := by
  simp [qterm, tri]

theorem tri_scal_right (a b c : Fin 3 → ℂ) (t : ℂ) : tri a b (fun k => t * c k) = t * tri a b c := by
  simp only [tri]; ring

theorem qterm_sum {ι : Type*} (s : Finset ι) (o v u w : Fin 3 → ℂ) (μ : ι → ℝ) (ψ : ι → Fin 3 → ℂ) :
    qterm o v u w (fun b => ∑ a ∈ s, ((μ a : ℝ) : ℂ) * ψ a b) = ∑ a ∈ s, ((μ a : ℝ) : ℂ) * qterm o v u w (ψ a) := by
  have hc : conjVec3 (fun b => ∑ a ∈ s, ((μ a : ℝ) : ℂ) * ψ a b)
      = fun b => ∑ a ∈ s, ((μ a : ℝ) : ℂ) * conjVec3 (ψ a) b := by
    funext b
    simp [conjVec3, map_sum, map_mul, Complex.conj_ofReal]
  simp only [qterm, hc]
  rw [tri_sum_right s o u (fun a k => ((μ a : ℝ) : ℂ) * conjVec3 (ψ a) k),
    tri_sum_right s v w (fun a k => ((μ a : ℝ) : ℂ) * conjVec3 (ψ a) k), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tri_scal_right, tri_scal_right]
  ring

theorem entry_curlAdj (s : Fin 3 → Fin 3 → ℂ) (u ψ : Fin 3 → ℂ) :
    entryPairing s (curlAdj (crossC (conjVec3 u) ψ)) = tri (curlComp s) u (conjVec3 ψ) := by
  simp [entryPairing, curlAdj, curlComp, crossC, conjVec3, tri, Fin.sum_univ_three, CellCert.permSign]
  ring

theorem vecPair_cross (v ψ w : Fin 3 → ℂ) :
    CellScalars.vecPair v (crossC ψ (conjVec3 w)) = -tri v w (conjVec3 ψ) := by
  simp [CellScalars.vecPair, crossC, conjVec3, tri, Fin.sum_univ_three]
  ring

theorem entry_scal_sum (s : Fin 3 → Fin 3 → ℂ) (r : ℝ) (M : Finset ℤ) (f : ℤ → Fin 3 → Fin 3 → ℂ) :
    entryPairing s (fun i l => (r : ℂ) * ∑ m ∈ M, f m i l) = (r : ℂ) * ∑ m ∈ M, entryPairing s (f m) := by
  simp only [entryPairing, map_mul, map_sum, Complex.conj_ofReal, Finset.mul_sum]
  refine (Finset.sum_congr rfl (fun a _ => Finset.sum_comm)).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring)))

theorem vec_scal_sum (v : Fin 3 → ℂ) (r : ℝ) (M : Finset ℤ) (f : ℤ → Fin 3 → ℂ) :
    CellScalars.vecPair v (fun i => (r : ℂ) * ∑ m ∈ M, f m i) = (r : ℂ) * ∑ m ∈ M, CellScalars.vecPair v (f m) := by
  simp only [CellScalars.vecPair, map_mul, map_sum, Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun a _ => by ring))

theorem pair_generic (lw rh r : ℝ) (h : lw * rh = r) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (M : Finset ℤ)
    (U W ψ : ℤ → Fin 3 → ℂ) :
    (lw : ℂ) * (entryPairing s (fun i l => (rh : ℂ) * ∑ m ∈ M, curlAdj (crossC (conjVec3 (U m)) (ψ m)) i l)
      + CellScalars.vecPair v (fun i => (rh : ℂ) * ∑ m ∈ M, crossC (ψ m) (conjVec3 (W m)) i))
      = (r : ℂ) * ∑ m ∈ M, qterm (curlComp s) v (U m) (W m) (ψ m) := by
  rw [entry_scal_sum, vec_scal_sum]
  simp only [entry_curlAdj, vecPair_cross, qterm]
  rw [← h]
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib, mul_assoc]
  congr 2

theorem select {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k} (hd : IsCellData α c K S B Cl R)
    (p : ℝ × ℝ) (hp : p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) (hp0 : p.1 ≠ 0)
    (a : Fin N) (ha : a ∈ R.rowSet) (n : ℤ) (hn : n ∉ S.resolved ∪ S.band) (m : ℤ) (o v : Fin 3 → ℂ) :
    qterm o v (modeVec c.order (m - n) c.modelVelocity p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
        (CellScalars.rowMode c a m p)
      = ∑ i : Fin Cl.count, if m - n ∈ Cl.modes i ∧ R.rowModeOf a ∈ Cl.resolvedPart i then
          qterm o v (modeVec c.order (m - n) c.modelVelocity p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
            (CellScalars.rowMode c a m p) else 0 := by
  by_cases hq : qterm o v (modeVec c.order (m - n) c.modelVelocity p.1 p.2)
      (modeVec c.order (m - n) c.modelCurl p.1 p.2) (CellScalars.rowMode c a m p) = 0
  · rw [hq]; simp
  have hrect : p ∈ K.rect := ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hψ : CellScalars.rowMode c a m p ≠ 0 := fun h => hq (by rw [h]; exact qterm_zero_right _ _ _ _)
  have hUW : modeVec c.order (m - n) c.modelVelocity p.1 p.2 ≠ 0 ∨ modeVec c.order (m - n) c.modelCurl p.1 p.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    rw [h.1, h.2]
    exact qterm_zero_mid _ _ _
  have hm : m = R.rowModeOf a ∨ m = -R.rowModeOf a := by
    by_contra h
    push Not at h
    exact hψ (hd.row_mode_of a ha m h.1 h.2 p hrect)
  have hmres : m ∈ S.resolved := by
    rcases hm with h | h
    · rw [h]; exact hd.row_mode_resolved a ha
    · rw [h]; exact (hd.scalars.resolved_symm _).mp (hd.row_mode_resolved a ha)
  obtain ⟨i, hi⟩ := hd.class_cover m hmres n hn ⟨p, hp, hp0, by
    rcases hUW with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)⟩
  have hai : R.rowModeOf a ∈ Cl.resolvedPart i := by
    rcases hm with h | h
    · rw [← h]
      exact hd.class_resolved_cover i m hmres ⟨n, hn, hi⟩
    · have e : R.rowModeOf a = -m := by rw [h]; ring
      rw [e]
      refine hd.class_resolved_cover i (-m) ((hd.scalars.resolved_symm m).mp hmres) ⟨-n, ?_, ?_⟩
      · intro h'
        apply hn
        rw [Finset.mem_union] at h' ⊢
        rcases h' with h' | h'
        · exact Or.inl ((hd.scalars.resolved_symm n).mpr h')
        · exact Or.inr ((hd.scalars.band_symm n).mpr h')
      · have e2 : -m - -n = -(m - n) := by ring
        rw [e2]
        exact (hd.class_modes_symm i _).mp hi
  rw [Finset.sum_eq_single i]
  · simp [hi, hai]
  · intro j _ hj
    have : m - n ∉ Cl.modes j := fun h => Finset.disjoint_left.mp (hd.class_disjoint i j (Ne.symm hj)) hi h
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ i) h

end UnresolvedRowPoint

end FracInternal

namespace CellCert

namespace CellAnalysis

open FracInternal.UnresolvedRowPoint

theorem unresolvedRowPoint_holds : UnresolvedRowPointStatement := by
  intro α _ _ k N c _ K S B Cl slots R hd _ x _ μ _ p hp hp0 F
  have hp1 : 0 < p.1 := lt_of_le_of_lt hd.box.r_order.1 hp.1.1
  have hlw : K.lineWeight p.1 * CellScalars.rHat K p = p.1 := by
    have hne : K.lineWeight p.1 ≠ 0 := by
      unfold CellBox.lineWeight
      split_ifs
      · exact hp0
      · exact one_ne_zero
    unfold CellScalars.rHat
    field_simp
  have P1 : ∀ a n, CellScalars.unresolvedPairAt c K R x a n p = ((p.1 : ℝ) : ℂ) * ∑ m ∈ R.rowModes,
      qterm (curlComp (fun i q => gradMode c.order n x.2.1 i q p)) (modeVec c.order n x.1 p.1 p.2)
        (modeVec c.order (m - n) c.modelVelocity p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
        (CellScalars.rowMode c a m p) := by
    intro a n
    exact pair_generic _ _ _ hlw _ _ _ (fun m => modeVec c.order (m - n) c.modelVelocity p.1 p.2)
      (fun m => modeVec c.order (m - n) c.modelCurl p.1 p.2) (fun m => CellScalars.rowMode c a m p)
  set F' := F.filter (fun n => n ∉ S.resolved ∪ S.band) with hF'
  set Y : Fin Cl.count → ℂ := fun i => ∑ n ∈ F', ∑ m ∈ R.rowModes, (if m - n ∈ Cl.modes i then
      qterm (curlComp (fun i q => gradMode c.order n x.2.1 i q p)) (modeVec c.order n x.1 p.1 p.2)
        (modeVec c.order (m - n) c.modelVelocity p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
        (fun b => ∑ a ∈ R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i),
          ((μ a : ℝ) : ℂ) * CellScalars.rowMode c a m p b) else 0) with hY
  have P3 : ∀ n ∈ F', ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * CellScalars.unresolvedPairAt c K R x a n p
      = ((p.1 : ℝ) : ℂ) * ∑ i : Fin Cl.count, ∑ m ∈ R.rowModes, (if m - n ∈ Cl.modes i then
      qterm (curlComp (fun i q => gradMode c.order n x.2.1 i q p)) (modeVec c.order n x.1 p.1 p.2)
        (modeVec c.order (m - n) c.modelVelocity p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
        (fun b => ∑ a ∈ R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i),
          ((μ a : ℝ) : ℂ) * CellScalars.rowMode c a m p b) else 0) := by
    intro n hn
    have hn' : n ∉ S.resolved ∪ S.band := (Finset.mem_filter.mp hn).2
    simp only [P1]
    have e1 : ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * (((p.1 : ℝ) : ℂ) * ∑ m ∈ R.rowModes,
        qterm (curlComp (fun i q => gradMode c.order n x.2.1 i q p)) (modeVec c.order n x.1 p.1 p.2)
          (modeVec c.order (m - n) c.modelVelocity p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
          (CellScalars.rowMode c a m p))
        = ((p.1 : ℝ) : ℂ) * ∑ a ∈ R.rowSet, ∑ m ∈ R.rowModes, ∑ i : Fin Cl.count, ((μ a : ℝ) : ℂ) *
          (if m - n ∈ Cl.modes i ∧ R.rowModeOf a ∈ Cl.resolvedPart i then
          qterm (curlComp (fun i q => gradMode c.order n x.2.1 i q p)) (modeVec c.order n x.1 p.1 p.2)
            (modeVec c.order (m - n) c.modelVelocity p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
            (CellScalars.rowMode c a m p) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      conv_lhs => rw [select hd p hp hp0 a ha n hn' m]
      rw [Finset.mul_sum]
    rw [e1]
    congr 1
    have e2 : ∑ a ∈ R.rowSet, ∑ m ∈ R.rowModes, ∑ i : Fin Cl.count, ((μ a : ℝ) : ℂ) *
          (if m - n ∈ Cl.modes i ∧ R.rowModeOf a ∈ Cl.resolvedPart i then
          qterm (curlComp (fun i q => gradMode c.order n x.2.1 i q p)) (modeVec c.order n x.1 p.1 p.2)
            (modeVec c.order (m - n) c.modelVelocity p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
            (CellScalars.rowMode c a m p) else 0)
        = ∑ i : Fin Cl.count, ∑ m ∈ R.rowModes, ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
          (if m - n ∈ Cl.modes i ∧ R.rowModeOf a ∈ Cl.resolvedPart i then
          qterm (curlComp (fun i q => gradMode c.order n x.2.1 i q p)) (modeVec c.order n x.1 p.1 p.2)
            (modeVec c.order (m - n) c.modelVelocity p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
            (CellScalars.rowMode c a m p) else 0) := by
      refine (Finset.sum_congr rfl (fun a _ => Finset.sum_comm)).trans ?_
      refine Finset.sum_comm.trans ?_
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    rw [e2]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun m _ => ?_))
    by_cases hmi : m - n ∈ Cl.modes i
    · rw [if_pos hmi, qterm_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      by_cases h : R.rowModeOf a ∈ Cl.resolvedPart i
      · simp [hmi, h]
      · simp [h]
    · simp [hmi]
  have hL : ∑ a ∈ R.rowSet, μ a * ∑ n ∈ F, CellScalars.unresolvedPairPoint c K S R x a n p
      = ∑ i : Fin Cl.count, p.1 * (Y i).re := by
    have e1 : ∀ a, ∑ n ∈ F, CellScalars.unresolvedPairPoint c K S R x a n p
        = ∑ n ∈ F', (CellScalars.unresolvedPairAt c K R x a n p).re := by
      intro a
      rw [hF', Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      unfold CellScalars.unresolvedPairPoint
      split_ifs <;> simp_all
    simp only [e1, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∀ n ∈ F', ∑ a ∈ R.rowSet, μ a * (CellScalars.unresolvedPairAt c K R x a n p).re
        = (∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * CellScalars.unresolvedPairAt c K R x a n p).re := by
      intro n _
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Complex.re_ofReal_mul]
    rw [Finset.sum_congr rfl e2, ← Complex.re_sum]
    rw [Finset.sum_congr rfl P3, ← Finset.mul_sum, Complex.re_ofReal_mul, Finset.sum_comm, Complex.re_sum,
      Finset.mul_sum]
  have hR : p.1 * ∑ n ∈ F, CellScalars.unresolvedChargePoint c S Cl x n p
        + ∑ i, p.1 * CellScalars.classRowSq c R Cl μ i p / Cl.rowWeight i
      = ∑ i : Fin Cl.count, p.1 * (2 * Cl.rowWeight i * (Cl.velocityDev i p ^ 2 *
          ∑ n ∈ F', vecSq (curlComp (fun i q => gradMode c.order n x.2.1 i q p))
          + Cl.curlDev i p ^ 2 * ∑ n ∈ F', vecSq (modeVec c.order n x.1 p.1 p.2))
        + (∑ m ∈ R.rowModes, vecSq (fun b => ∑ a ∈ R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i),
          ((μ a : ℝ) : ℂ) * CellScalars.rowMode c a m p b)) / Cl.rowWeight i) := by
    have e1 : ∑ n ∈ F, CellScalars.unresolvedChargePoint c S Cl x n p
        = ∑ i : Fin Cl.count, 2 * Cl.rowWeight i * (Cl.velocityDev i p ^ 2 *
          ∑ n ∈ F', vecSq (curlComp (fun i q => gradMode c.order n x.2.1 i q p))
          + Cl.curlDev i p ^ 2 * ∑ n ∈ F', vecSq (modeVec c.order n x.1 p.1 p.2)) := by
      have e0 : ∑ n ∈ F, CellScalars.unresolvedChargePoint c S Cl x n p
          = ∑ n ∈ F', ∑ i : Fin Cl.count, 2 * Cl.rowWeight i * (Cl.velocityDev i p ^ 2 *
            vecSq (curlComp (fun i q => gradMode c.order n x.2.1 i q p))
            + Cl.curlDev i p ^ 2 * vecSq (modeVec c.order n x.1 p.1 p.2)) := by
        rw [hF', Finset.sum_filter]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        unfold CellScalars.unresolvedChargePoint
        split_ifs <;> simp_all [curlSq, vecSq]
      rw [e0, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    rw [e1, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold CellScalars.classRowSq
    ring
  rw [hL, hR, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hA := (hd.class_devs_nonneg i p).2.2.1
  have hB := (hd.class_devs_nonneg i p).2.2.2
  have hρ := (hd.class_weights_pos i).2
  have hfreq : F'.Nonempty → (c.order : ℝ) ≠ 0 := by
    rintro ⟨n, hn⟩ h0
    have hn' : n ∉ S.resolved := fun h => (Finset.mem_filter.mp hn).2 (Finset.mem_union_left _ h)
    have := hd.scalars.unresolved_large n hn'
    simp [modeNumber, azimuth, h0] at this
    linarith
  have hang : ∀ φ : ℝ, (c.order : ℝ) ≠ 0 → ∀ β : ℤ, azimuth c.order β * (φ / c.order) = β * φ := by
    intro φ h0 β
    unfold azimuth
    field_simp
  have hT := classConvolutionBound F' R.rowModes (Cl.modes i) (fun n => curlComp (fun i q => gradMode c.order n x.2.1 i q p))
    (fun n => modeVec c.order n x.1 p.1 p.2) (fun β => modeVec c.order β c.modelVelocity p.1 p.2)
    (fun β => modeVec c.order β c.modelCurl p.1 p.2)
    (fun m b => ∑ a ∈ R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i),
          ((μ a : ℝ) : ℂ) * CellScalars.rowMode c a m p b)
    (Cl.velocityDev i p) (Cl.curlDev i p) (Cl.rowWeight i) hA hB hρ
    (fun hne φ => by
      have h := (hd.class_bounds i p hp hp0 (φ / c.order)).2.2.1
      unfold classVec at h
      simp only [hang φ (hfreq hne)] at h
      exact h)
    (fun hne φ => by
      have h := (hd.class_bounds i p hp hp0 (φ / c.order)).2.2.2
      unfold classVec at h
      simp only [hang φ (hfreq hne)] at h
      exact h)
  have hY' : Y i = ∑ n ∈ F', ∑ m ∈ R.rowModes, (if m - n ∈ Cl.modes i then
      tri (curlComp (fun i q => gradMode c.order n x.2.1 i q p)) (modeVec c.order (m - n) c.modelVelocity p.1 p.2)
        (conjVec3 (fun b => ∑ a ∈ R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i),
          ((μ a : ℝ) : ℂ) * CellScalars.rowMode c a m p b))
      - tri (modeVec c.order n x.1 p.1 p.2) (modeVec c.order (m - n) c.modelCurl p.1 p.2)
        (conjVec3 (fun b => ∑ a ∈ R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i),
          ((μ a : ℝ) : ℂ) * CellScalars.rowMode c a m p b)) else 0) := rfl
  rw [← hY'] at hT
  have hre : -(Y i).re ≤ ‖Y i‖ := by
    have := Complex.abs_re_le_norm (Y i)
    linarith [neg_abs_le (Y i).re]
  have := mul_le_mul_of_nonneg_left hT hp1.le
  nlinarith

end CellAnalysis

end CellCert

end Breakdown

