import Breakdown.Cert.CoerciveStatement

noncomputable section

namespace Breakdown

namespace Coercive

namespace CurlWeight.Internal

private theorem cnormSq_eq_re_im (x : Fin 3 → ℂ) :
    cnormSq x = ∑ l : Fin 3, ((x l).re ^ 2 + (x l).im ^ 2) := by
  unfold cnormSq
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem sum_sub_sq_le (x y b c : Fin 3 → ℝ) :
    (∑ l : Fin 3, (x l * b l - y l * c l)) ^ 2 ≤
      (∑ l : Fin 3, (x l ^ 2 + y l ^ 2)) * ∑ l : Fin 3, (c l ^ 2 + b l ^ 2) := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 0 * b 1 - x 1 * b 0), sq_nonneg (x 0 * b 2 - x 2 * b 0),
    sq_nonneg (x 1 * b 2 - x 2 * b 1), sq_nonneg (y 0 * c 1 - y 1 * c 0),
    sq_nonneg (y 0 * c 2 - y 2 * c 0), sq_nonneg (y 1 * c 2 - y 2 * c 1),
    sq_nonneg (x 0 * c 0 + y 0 * b 0), sq_nonneg (x 1 * c 1 + y 1 * b 1), sq_nonneg (x 2 * c 2 + y 2 * b 2),
    sq_nonneg (x 0 * c 1 + y 1 * b 0), sq_nonneg (x 1 * c 0 + y 0 * b 1),
    sq_nonneg (x 0 * c 2 + y 2 * b 0), sq_nonneg (x 2 * c 0 + y 0 * b 2),
    sq_nonneg (x 1 * c 2 + y 2 * b 1), sq_nonneg (x 2 * c 1 + y 1 * b 2)]

private theorem sum_add_sq_le (x y b c : Fin 3 → ℝ) :
    (∑ l : Fin 3, (x l * b l + y l * c l)) ^ 2 ≤
      (∑ l : Fin 3, (x l ^ 2 + y l ^ 2)) * ∑ l : Fin 3, (b l ^ 2 + c l ^ 2) := by
  have h := sum_sub_sq_le x y b (fun l => -c l)
  simp only [mul_neg, sub_neg_eq_add, neg_sq] at h
  rw [Finset.sum_congr rfl (fun l _ => add_comm (c l ^ 2) (b l ^ 2))] at h
  exact h

private theorem cross_sq_le (p w : Fin 3 → ℝ) :
    ∑ l : Fin 3, (∑ i : Fin 3, ∑ j : Fin 3, alternatingSymbol i j l * p j * w i) ^ 2 ≤
      (∑ j : Fin 3, p j ^ 2) * ∑ i : Fin 3, w i ^ 2 := by
  simp only [Fin.sum_univ_three, alternatingSymbol, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  nlinarith [sq_nonneg (p 0 * w 0 + p 1 * w 1 + p 2 * w 2)]

private theorem abs_le_sqrt_mul_sqrt {S X Y : ℝ} (h : S ^ 2 ≤ X * Y) (hX : 0 ≤ X) :
    |S| ≤ Real.sqrt X * Real.sqrt Y := by
  rw [← Real.sqrt_mul hX, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

private theorem sum_rewrite {a : ℝ} {p : Fin 3 → ℝ} {d : Fin 3 → Fin 3 → ℂ} {Δ ω θ : Fin 3 → ℂ}
    {Cr Ci : Fin 3 → ℝ}
    (hLr : ∀ l, (Δ l).re = ∑ i, ∑ j, alternatingSymbol i j l * (d i j).re)
    (hLi : ∀ l, (Δ l).im = ∑ i, ∑ j, alternatingSymbol i j l * (d i j).im)
    (hCr : ∀ l, Cr l = ∑ i, ∑ j, alternatingSymbol i j l * p j * (ω i).re)
    (hCi : ∀ l, Ci l = ∑ i, ∑ j, alternatingSymbol i j l * p j * (ω i).im) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * (a * (θ l).re * (d i j).im
      + (θ l).re * p j * (ω i).im - a * (θ l).im * (d i j).re - (θ l).im * p j * (ω i).re)
      = ∑ l : Fin 3, ((θ l).re * (a * (Δ l).im + Ci l) - (θ l).im * (a * (Δ l).re + Cr l)) := by
  simp only [hLr, hLi, hCr, hCi, Fin.sum_univ_three]
  ring

private theorem final_bound {a A A' Nθ NΔ Nω NC M S Nb : ℝ} (ha : |a| ≤ A) (hA' : 0 ≤ A')
    (hθ0 : 0 ≤ Nθ) (hΔ0 : 0 ≤ NΔ) (hC0 : 0 ≤ NC)
    (h1 : S ^ 2 ≤ Nθ * Nb) (hNb : Nb = a ^ 2 * NΔ + 2 * a * M + NC) (h2 : M ^ 2 ≤ NΔ * NC)
    (hNC : NC ≤ A' ^ 2 * Nω) :
    |S| ≤ (A * Real.sqrt NΔ + A' * Real.sqrt Nω) * Real.sqrt Nθ := by
  have hsC : Real.sqrt NC ≤ A' * Real.sqrt Nω := by
    calc Real.sqrt NC ≤ Real.sqrt (A' ^ 2 * Nω) := Real.sqrt_le_sqrt hNC
      _ = A' * Real.sqrt Nω := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA']
  have hMabs : |M| ≤ Real.sqrt NΔ * Real.sqrt NC := abs_le_sqrt_mul_sqrt h2 hΔ0
  have hsΔ := Real.sq_sqrt hΔ0
  have hsCsq := Real.sq_sqrt hC0
  have hsΔ0 := Real.sqrt_nonneg NΔ
  have hsC0 := Real.sqrt_nonneg NC
  have hsθ0 := Real.sqrt_nonneg Nθ
  have haM : a * M ≤ |a| * (Real.sqrt NΔ * Real.sqrt NC) := by
    calc a * M ≤ |a * M| := le_abs_self _
      _ = |a| * |M| := abs_mul _ _
      _ ≤ |a| * (Real.sqrt NΔ * Real.sqrt NC) := mul_le_mul_of_nonneg_left hMabs (abs_nonneg _)
  have hb : Nb ≤ (|a| * Real.sqrt NΔ + Real.sqrt NC) ^ 2 := by
    have e : (|a| * Real.sqrt NΔ + Real.sqrt NC) ^ 2
        = |a| ^ 2 * Real.sqrt NΔ ^ 2 + 2 * (|a| * (Real.sqrt NΔ * Real.sqrt NC)) + Real.sqrt NC ^ 2 := by ring
    rw [e, sq_abs, hsΔ, hsCsq, hNb]
    linarith
  have h3 : S ^ 2 ≤ Nθ * (|a| * Real.sqrt NΔ + Real.sqrt NC) ^ 2 :=
    h1.trans (mul_le_mul_of_nonneg_left hb hθ0)
  have h4 := abs_le_sqrt_mul_sqrt h3 hθ0
  rw [Real.sqrt_sq (by positivity)] at h4
  refine h4.trans ?_
  rw [mul_comm (Real.sqrt Nθ)]
  refine mul_le_mul_of_nonneg_right ?_ hsθ0
  have : |a| * Real.sqrt NΔ ≤ A * Real.sqrt NΔ := mul_le_mul_of_nonneg_right ha hsΔ0
  linarith

theorem slice_pointwise_le {a A A' : ℝ} (ha : |a| ≤ A) {p : Fin 3 → ℝ} (hp : ∑ j, p j ^ 2 ≤ A' ^ 2) (hA' : 0 ≤ A')
    {d : Fin 3 → Fin 3 → ℂ} {Δ ω θ : Fin 3 → ℂ}
    (hL : ∀ l, ∑ i, ∑ j, (alternatingSymbol i j l : ℂ) * d i j = Δ l) :
    |∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * (a * (θ l).re * (d i j).im + (θ l).re * p j * (ω i).im
        - a * (θ l).im * (d i j).re - (θ l).im * p j * (ω i).re)|
      ≤ (A * Real.sqrt (cnormSq Δ) + A' * Real.sqrt (cnormSq ω)) * Real.sqrt (cnormSq θ) := by
  have hLr : ∀ l, (Δ l).re = ∑ i, ∑ j, alternatingSymbol i j l * (d i j).re := fun l => by
    rw [← hL l]
    simp [Complex.re_sum, Complex.mul_re]
  have hLi : ∀ l, (Δ l).im = ∑ i, ∑ j, alternatingSymbol i j l * (d i j).im := fun l => by
    rw [← hL l]
    simp [Complex.im_sum, Complex.mul_im]
  obtain ⟨Cr, hCr⟩ : ∃ Cr : Fin 3 → ℝ, ∀ l, Cr l = ∑ i, ∑ j, alternatingSymbol i j l * p j * (ω i).re :=
    ⟨fun l => _, fun l => rfl⟩
  obtain ⟨Ci, hCi⟩ : ∃ Ci : Fin 3 → ℝ, ∀ l, Ci l = ∑ i, ∑ j, alternatingSymbol i j l * p j * (ω i).im :=
    ⟨fun l => _, fun l => rfl⟩
  rw [sum_rewrite hLr hLi hCr hCi, cnormSq_eq_re_im, cnormSq_eq_re_im, cnormSq_eq_re_im]
  have h1 := sum_sub_sq_le (fun l => (θ l).re) (fun l => (θ l).im) (fun l => a * (Δ l).im + Ci l)
    (fun l => a * (Δ l).re + Cr l)
  have h2 := sum_add_sq_le (fun l => (Δ l).re) (fun l => (Δ l).im) Cr Ci
  have hcr := cross_sq_le p (fun i => (ω i).re)
  have hci := cross_sq_le p (fun i => (ω i).im)
  try simp only at h1
  try simp only at h2
  try simp only at hcr
  try simp only at hci
  have ecr : ∑ l : Fin 3, Cr l ^ 2 = ∑ l : Fin 3, (∑ i : Fin 3, ∑ j : Fin 3, alternatingSymbol i j l * p j * (ω i).re) ^ 2 :=
    Finset.sum_congr rfl fun l _ => by rw [hCr l]
  have eci : ∑ l : Fin 3, Ci l ^ 2 = ∑ l : Fin 3, (∑ i : Fin 3, ∑ j : Fin 3, alternatingSymbol i j l * p j * (ω i).im) ^ 2 :=
    Finset.sum_congr rfl fun l _ => by rw [hCi l]
  have hw0 : 0 ≤ ∑ i : Fin 3, (ω i).re ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw1 : 0 ≤ ∑ i : Fin 3, (ω i).im ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have a1 := mul_le_mul_of_nonneg_right hp hw0
  have a2 := mul_le_mul_of_nonneg_right hp hw1
  have hNC : ∑ l : Fin 3, (Cr l ^ 2 + Ci l ^ 2) ≤ A' ^ 2 * ∑ l : Fin 3, ((ω l).re ^ 2 + (ω l).im ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ecr, eci, mul_add]
    linarith
  refine final_bound ha hA' (Finset.sum_nonneg fun l _ => by positivity)
    (Finset.sum_nonneg fun l _ => by positivity) (Finset.sum_nonneg fun l _ => by positivity) h1 ?_ h2 hNC
  simp only [Fin.sum_univ_three]
  ring

end CurlWeight.Internal

end Coercive

end Breakdown
