import Breakdown.CertCell.AssemblyStatements

open scoped ComplexConjugate
open Filter Topology Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace Sharp

def wavePhase (ξ : ℤ × ℤ) (σ θ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I)

def symbolAt (B : Finset (ℤ × ℤ)) (M : ℤ × ℤ → Matrix (Fin 12) (Fin 12) ℂ) (σ θ : ℝ) :
    Matrix (Fin 12) (Fin 12) ℂ :=
  ∑ β ∈ B, wavePhase β σ θ • M β

def synthAt (m : ℕ) (F : Finset (ℤ × ℤ)) (X : ℤ × ℤ → Fin 12 → ℂ) (σ θ : ℝ) : Fin 12 → ℂ :=
  ∑ ι ∈ F, wavePhase (labelHarmonic m ι) σ θ • X ι

theorem wavePhase_add (a b : ℤ × ℤ) (σ θ : ℝ) :
    wavePhase (a + b) σ θ = wavePhase a σ θ * wavePhase b σ θ := by
  unfold wavePhase
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem conj_wavePhase (a : ℤ × ℤ) (σ θ : ℝ) : conj (wavePhase a σ θ) = wavePhase (-a) σ θ := by
  unfold wavePhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring

theorem wavePhase_zero (σ θ : ℝ) : wavePhase 0 σ θ = 1 := by
  unfold wavePhase
  simp

def gridRoot (k : ℤ) (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / n)

theorem wavePhase_grid (ξ : ℤ × ℤ) (n j l : ℕ) :
    wavePhase ξ ((j : ℝ) / n) (2 * Real.pi * l / n) = gridRoot ξ.1 n ^ j * gridRoot ξ.2 n ^ l := by
  unfold wavePhase gridRoot
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gridRoot_sum (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, gridRoot k n ^ j = if (n : ℤ) ∣ k then (n : ℂ) else 0 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpow : gridRoot k n ^ n = 1 := by
    unfold gridRoot
    rw [← Complex.exp_nat_mul]
    have : (n : ℂ) * (2 * Real.pi * Complex.I * k / n) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I k
  split_ifs with hd
  · obtain ⟨c, hc⟩ := hd
    have h1 : gridRoot k n = 1 := by
      unfold gridRoot
      have : 2 * Real.pi * Complex.I * (k : ℂ) / n = (c : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hc]
        push_cast
        field_simp
      rw [this]
      exact Complex.exp_int_mul_two_pi_mul_I c
    simp [h1]
  · have h1 : gridRoot k n ≠ 1 := by
      intro h
      unfold gridRoot at h
      obtain ⟨c, hc⟩ := Complex.exp_eq_one_iff.mp h
      apply hd
      refine ⟨c, ?_⟩
      have hpi : (2 * Real.pi * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have : (k : ℂ) = (n : ℂ) * c := by
        have h2 : 2 * Real.pi * Complex.I * (k : ℂ) = (c : ℂ) * (2 * Real.pi * Complex.I) * n := by
          rw [← hc]
          field_simp
        have h3 : (2 * Real.pi * Complex.I) * (k : ℂ) = (2 * Real.pi * Complex.I) * ((n : ℂ) * c) := by
          rw [h2]; ring
        exact mul_left_cancel₀ hpi h3
      exact_mod_cast this
    rw [geom_sum_eq h1, hpow]
    simp

theorem grid_phase_sum (ξ : ℤ × ℤ) (n : ℕ) (hn : 1 ≤ n) (h1 : |ξ.1| < n) (h2 : |ξ.2| < n) :
    ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n, wavePhase ξ ((j : ℝ) / n) (2 * Real.pi * l / n)
      = if ξ = 0 then (n : ℂ) ^ 2 else 0 := by
  simp_rw [wavePhase_grid]
  rw [← Finset.sum_mul_sum, gridRoot_sum _ _ hn, gridRoot_sum _ _ hn]
  by_cases hξ : ξ = 0
  · subst hξ
    simp [sq]
  · rw [if_neg hξ]
    have : ¬ ((n : ℤ) ∣ ξ.1 ∧ (n : ℤ) ∣ ξ.2) := by
      rintro ⟨d1, d2⟩
      apply hξ
      exact Prod.ext (Int.eq_zero_of_abs_lt_dvd d1 h1) (Int.eq_zero_of_abs_lt_dvd d2 h2)
    by_cases d1 : (n : ℤ) ∣ ξ.1
    · have d2 : ¬ (n : ℤ) ∣ ξ.2 := fun d2 => this ⟨d1, d2⟩
      simp [d2]
    · simp [d1]

theorem pull3 {a b c : Type*} (s : Finset a) (t : Finset b) (u : Finset c) (f : a → b → c → ℂ) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z = ∑ z ∈ u, ∑ x ∈ s, ∑ y ∈ t, f x y z := by
  calc ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z = ∑ x ∈ s, ∑ z ∈ u, ∑ y ∈ t, f x y z :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z ∈ u, ∑ x ∈ s, ∑ y ∈ t, f x y z := Finset.sum_comm

theorem sesq12_eq (M : Matrix (Fin 12) (Fin 12) ℂ) (U U' : Fin 12 → ℂ) :
    sesq12 M U U' = star U ⬝ᵥ (M *ᵥ U') := by
  unfold sesq12
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sesq12_smul_sum (B : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (M : ℤ × ℤ → Matrix (Fin 12) (Fin 12) ℂ)
    (U U' : Fin 12 → ℂ) :
    sesq12 (∑ β ∈ B, c β • M β) U U' = ∑ β ∈ B, c β * sesq12 (M β) U U' := by
  rw [sesq12_eq, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, sesq12_eq]

theorem sesq12_vec_sum (M : Matrix (Fin 12) (Fin 12) ℂ) (F : Finset (ℤ × ℤ)) (a b : ℤ × ℤ → ℂ)
    (X : ℤ × ℤ → Fin 12 → ℂ) :
    sesq12 M (∑ ι ∈ F, a ι • X ι) (∑ ι ∈ F, b ι • X ι)
      = ∑ ι ∈ F, ∑ ι' ∈ F, conj (a ι) * b ι' * sesq12 M (X ι) (X ι') := by
  rw [sesq12_eq, star_sum, Matrix.mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun ι' _ => ?_
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, sesq12_eq]
  simp only [RCLike.star_def]
  ring

theorem labelHarmonic_sub (m : ℕ) (a b : ℤ × ℤ) :
    labelHarmonic m (a - b) = labelHarmonic m a - labelHarmonic m b := by
  unfold labelHarmonic labelTime labelAzimuth
  ext <;> simp <;> ring

theorem sesq_synth (m : ℕ) (B : Finset (ℤ × ℤ)) (M : ℤ × ℤ → Matrix (Fin 12) (Fin 12) ℂ) (F : Finset (ℤ × ℤ))
    (X : ℤ × ℤ → Fin 12 → ℂ) (σ θ : ℝ) :
    sesq12 (symbolAt B M σ θ) (synthAt m F X σ θ) (synthAt m F X σ θ)
      = ∑ β ∈ B, ∑ ι ∈ F, ∑ ι' ∈ F,
          wavePhase (β + labelHarmonic m ι' - labelHarmonic m ι) σ θ * sesq12 (M β) (X ι) (X ι') := by
  unfold symbolAt synthAt
  rw [sesq12_smul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [sesq12_vec_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι' _ => ?_
  rw [conj_wavePhase, sub_eq_add_neg, wavePhase_add, wavePhase_add]
  ring

def gridBound (m : ℕ) (B F : Finset (ℤ × ℤ)) : ℕ :=
  1 + ∑ β ∈ B, (β.1.natAbs + β.2.natAbs) + 2 * ∑ ι ∈ F, ((labelHarmonic m ι).1.natAbs + (labelHarmonic m ι).2.natAbs)

theorem gridBound_pos (m : ℕ) (B F : Finset (ℤ × ℤ)) : 1 ≤ gridBound m B F := by
  unfold gridBound; omega

theorem gridBound_cast (m : ℕ) (B F : Finset (ℤ × ℤ)) :
    (gridBound m B F : ℤ) = 1 + ∑ β ∈ B, (|β.1| + |β.2|)
      + 2 * ∑ ι ∈ F, (|(labelHarmonic m ι).1| + |(labelHarmonic m ι).2|) := by
  unfold gridBound
  push_cast [Int.natCast_natAbs]
  ring

theorem gridBound_lt (m : ℕ) (B F : Finset (ℤ × ℤ)) (β : ℤ × ℤ) (hβ : β ∈ B) (ι ι' : ℤ × ℤ)
    (hι : ι ∈ F) (hι' : ι' ∈ F) :
    |(β + labelHarmonic m ι' - labelHarmonic m ι).1| < gridBound m B F ∧
      |(β + labelHarmonic m ι' - labelHarmonic m ι).2| < gridBound m B F := by
  have hB1 : |β.1| + |β.2| ≤ ∑ β ∈ B, (|β.1| + |β.2|) :=
    Finset.single_le_sum (f := fun β : ℤ × ℤ => |β.1| + |β.2|) (fun _ _ => by positivity) hβ
  have hF1 : |(labelHarmonic m ι).1| + |(labelHarmonic m ι).2|
      ≤ ∑ ι ∈ F, (|(labelHarmonic m ι).1| + |(labelHarmonic m ι).2|) :=
    Finset.single_le_sum (f := fun ι : ℤ × ℤ => |(labelHarmonic m ι).1| + |(labelHarmonic m ι).2|)
      (fun _ _ => by positivity) hι
  have hF2 : |(labelHarmonic m ι').1| + |(labelHarmonic m ι').2|
      ≤ ∑ ι ∈ F, (|(labelHarmonic m ι).1| + |(labelHarmonic m ι).2|) :=
    Finset.single_le_sum (f := fun ι : ℤ × ℤ => |(labelHarmonic m ι).1| + |(labelHarmonic m ι).2|)
      (fun _ _ => by positivity) hι'
  rw [gridBound_cast]
  simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add]
  have t1 := abs_sub (β.1 + (labelHarmonic m ι').1) (labelHarmonic m ι).1
  have t2 := abs_add_le β.1 (labelHarmonic m ι').1
  have t3 := abs_sub (β.2 + (labelHarmonic m ι').2) (labelHarmonic m ι).2
  have t4 := abs_add_le β.2 (labelHarmonic m ι').2
  have p1 := abs_nonneg β.1
  have p2 := abs_nonneg β.2
  have p3 := abs_nonneg (labelHarmonic m ι).1
  have p4 := abs_nonneg (labelHarmonic m ι).2
  have p5 := abs_nonneg (labelHarmonic m ι').1
  have p6 := abs_nonneg (labelHarmonic m ι').2
  constructor <;> linarith

theorem grid_total (m : ℕ) (B : Finset (ℤ × ℤ)) (M : ℤ × ℤ → Matrix (Fin 12) (Fin 12) ℂ) (F : Finset (ℤ × ℤ))
    (X : ℤ × ℤ → Fin 12 → ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hlt : ∀ β ∈ B, ∀ ι ∈ F, ∀ ι' ∈ F, |(β + labelHarmonic m ι' - labelHarmonic m ι).1| < n ∧
      |(β + labelHarmonic m ι' - labelHarmonic m ι).2| < n) :
    ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        sesq12 (symbolAt B M ((j : ℝ) / n) (2 * Real.pi * l / n))
          (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))
          (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))
      = (n : ℂ) ^ 2 * ∑ β ∈ B, ∑ ι ∈ F, ∑ ι' ∈ F,
          if β + labelHarmonic m ι' - labelHarmonic m ι = 0 then sesq12 (M β) (X ι) (X ι') else 0 := by
  simp_rw [sesq_synth]
  have step : ∀ β ∈ B, ∀ ι ∈ F, ∀ ι' ∈ F,
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        wavePhase (β + labelHarmonic m ι' - labelHarmonic m ι) ((j : ℝ) / n) (2 * Real.pi * l / n)
          * sesq12 (M β) (X ι) (X ι')
      = (n : ℂ) ^ 2 * if β + labelHarmonic m ι' - labelHarmonic m ι = 0 then sesq12 (M β) (X ι) (X ι') else 0 := by
    intro β hβ ι hι ι' hι'
    simp_rw [← Finset.sum_mul]
    obtain ⟨h1, h2⟩ := hlt β hβ ι hι ι' hι'
    rw [grid_phase_sum _ n hn h1 h2]
    split_ifs <;> ring
  calc _ = ∑ β ∈ B, ∑ ι ∈ F, ∑ ι' ∈ F, ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        wavePhase (β + labelHarmonic m ι' - labelHarmonic m ι) ((j : ℝ) / n) (2 * Real.pi * l / n)
          * sesq12 (M β) (X ι) (X ι') := by
        rw [pull3 (Finset.range n) (Finset.range n) B]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [pull3 (Finset.range n) (Finset.range n) F]
        refine Finset.sum_congr rfl fun ι _ => ?_
        rw [pull3 (Finset.range n) (Finset.range n) F]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun β hβ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ι hι => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ι' hι' => step β hβ ι hι ι' hι'

theorem reindex_sum (m : ℕ) (B H : Finset (ℤ × ℤ)) (hH : ∀ α, α ∈ H ↔ labelHarmonic m α ∈ B)
    (F : Finset (ℤ × ℤ)) (s : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ → ℂ) :
    ∑ β ∈ B, ∑ ι ∈ F, ∑ ι' ∈ F, (if β + labelHarmonic m ι' - labelHarmonic m ι = 0 then s β ι ι' else 0)
      = ∑ ι ∈ F, ∑ α ∈ H, if ι - α ∈ F then s (labelHarmonic m α) ι (ι - α) else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Finset.sum_comm]
  have e1 : ∀ ι' ∈ F, (∑ β ∈ B, if β + labelHarmonic m ι' - labelHarmonic m ι = 0 then s β ι ι' else 0)
      = if ι - ι' ∈ H then s (labelHarmonic m (ι - ι')) ι ι' else 0 := by
    intro ι' _
    have e : ∀ β, (β + labelHarmonic m ι' - labelHarmonic m ι = 0) ↔ (labelHarmonic m (ι - ι') = β) := by
      intro β
      rw [labelHarmonic_sub]
      constructor <;> intro h
      · calc labelHarmonic m ι - labelHarmonic m ι'
            = (labelHarmonic m ι - labelHarmonic m ι') + (β + labelHarmonic m ι' - labelHarmonic m ι) := by
              rw [h, add_zero]
          _ = β := by abel
      · rw [← h]; abel
    simp_rw [e]
    rw [Finset.sum_ite_eq B (labelHarmonic m (ι - ι')) (fun β => s β ι ι')]
    simp only [hH]
  rw [Finset.sum_congr rfl e1, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun ι' => ι - ι') (fun α => ι - α) ?_ ?_ ?_ ?_ ?_
  · intro ι' h
    simp only [Finset.mem_filter] at h ⊢
    refine ⟨h.2, ?_⟩
    simpa using h.1
  · intro α h
    simp only [Finset.mem_filter] at h ⊢
    refine ⟨h.2, ?_⟩
    simpa using h.1
  · intro ι' _; simp
  · intro α _; simp
  · intro ι' _; simp

theorem re_sesq_le (M : Matrix (Fin 12) (Fin 12) ℂ) (U U' : Fin 12 → ℂ) :
    |(sesq12 M U U').re| ≤ (∑ i, ∑ j, ‖M i j‖) * (cnormSq U + cnormSq U') := by
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold sesq12
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have hi : ‖U i‖ ^ 2 ≤ cnormSq U := by
    unfold cnormSq
    exact Finset.single_le_sum (f := fun b => ‖U b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have hj : ‖U' j‖ ^ 2 ≤ cnormSq U' := by
    unfold cnormSq
    exact Finset.single_le_sum (f := fun b => ‖U' b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have hM := norm_nonneg (M i j)
  have h1 : ‖U i‖ * ‖U' j‖ ≤ cnormSq U + cnormSq U' := by
    nlinarith [sq_nonneg (‖U i‖ - ‖U' j‖), norm_nonneg (U i), norm_nonneg (U' j)]
  calc ‖U i‖ * ‖M i j‖ * ‖U' j‖ = ‖M i j‖ * (‖U i‖ * ‖U' j‖) := by ring
    _ ≤ ‖M i j‖ * (cnormSq U + cnormSq U') := mul_le_mul_of_nonneg_left h1 hM

theorem re_ite (c : Prop) [Decidable c] (z : ℂ) : (if c then z else 0).re = if c then z.re else 0 := by
  split_ifs <;> simp

theorem symbolForm_finite (m : ℕ) (B H : Finset (ℤ × ℤ)) (hH : ∀ α, α ∈ H ↔ labelHarmonic m α ∈ B)
    (h0 : ∀ α, α ∈ ({0} : Finset (ℤ × ℤ)) ↔ labelHarmonic m α ∈ ({0} : Finset (ℤ × ℤ)))
    (M : ℤ × ℤ → Matrix (Fin 12) (Fin 12) ℂ) (N : Matrix (Fin 12) (Fin 12) ℂ)
    (hpt : ∀ σ θ : ℝ, ∀ U : Fin 12 → ℂ, -(sesq12 N U U).re ≤ (sesq12 (symbolAt B M σ θ) U U).re)
    (X : ℤ × ℤ → Fin 12 → ℂ) (F : Finset (ℤ × ℤ)) :
    -(∑ ι ∈ F, (sesq12 N (X ι) (X ι)).re)
      ≤ ∑ ι ∈ F, ∑ α ∈ H, if ι - α ∈ F then (sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re else 0 := by
  set n := gridBound m (B ∪ {0}) F with hn
  have hn1 : 1 ≤ n := gridBound_pos m (B ∪ {0}) F
  have hnR : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hlt := gridBound_lt m (B ∪ {0}) F
  have gS := grid_total m B M F X n hn1 (fun β hβ ι hι ι' hι' => hlt β (Finset.mem_union_left _ hβ) ι ι' hι hι')
  have gN := grid_total m {0} (fun _ => N) F X n hn1 (fun β hβ ι hι ι' hι' => hlt β (Finset.mem_union_right _ hβ) ι ι' hι hι')
  rw [reindex_sum m B H hH F (fun β ι ι' => sesq12 (M β) (X ι) (X ι'))] at gS
  rw [reindex_sum m {0} {0} h0 F (fun β ι ι' => sesq12 N (X ι) (X ι'))] at gN
  have hNsym : ∀ σ θ, symbolAt {0} (fun _ => N) σ θ = N := by
    intro σ θ; unfold symbolAt; simp [wavePhase_zero]
  simp only [hNsym] at gN
  have e0 : ∑ ι ∈ F, ∑ α ∈ ({0} : Finset (ℤ × ℤ)), (if ι - α ∈ F then sesq12 N (X ι) (X (ι - α)) else 0)
      = ∑ ι ∈ F, sesq12 N (X ι) (X ι) := by
    refine Finset.sum_congr rfl fun ι hι => ?_
    simp [hι]
  rw [e0] at gN
  have hsum : ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        (-(sesq12 N (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))
          (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))).re)
      ≤ ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        (sesq12 (symbolAt B M ((j : ℝ) / n) (2 * Real.pi * l / n))
          (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))
          (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))).re :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hpt _ _ _
  have hre : ∀ z : ℂ, ((n : ℂ) ^ 2 * z).re = (n : ℝ) ^ 2 * z.re := by
    intro z
    have : (n : ℂ) ^ 2 = (((n : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  have lhsN : ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        (sesq12 N (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))
          (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))).re
      = (n : ℝ) ^ 2 * ∑ ι ∈ F, (sesq12 N (X ι) (X ι)).re := by
    have h := congrArg Complex.re gN
    rw [hre, Complex.re_sum] at h
    simp only [Complex.re_sum] at h
    exact h
  have rhsS : ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range n,
        (sesq12 (symbolAt B M ((j : ℝ) / n) (2 * Real.pi * l / n))
          (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))
          (synthAt m F X ((j : ℝ) / n) (2 * Real.pi * l / n))).re
      = (n : ℝ) ^ 2 * ∑ ι ∈ F, ∑ α ∈ H,
          if ι - α ∈ F then (sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re else 0 := by
    have h := congrArg Complex.re gS
    rw [hre, Complex.re_sum] at h
    simp only [Complex.re_sum, re_ite] at h
    exact h
  simp only [Finset.sum_neg_distrib] at hsum
  rw [lhsN, rhsS] at hsum
  have h2 : (n : ℝ) ^ 2 * (-(∑ ι ∈ F, (sesq12 N (X ι) (X ι)).re))
      ≤ (n : ℝ) ^ 2 * ∑ ι ∈ F, ∑ α ∈ H,
          if ι - α ∈ F then (sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re else 0 := by
    linarith
  exact le_of_mul_le_mul_left h2 hnR

theorem symbolForm_lower (m : ℕ) (B H : Finset (ℤ × ℤ)) (hH : ∀ α, α ∈ H ↔ labelHarmonic m α ∈ B)
    (h0 : ∀ α, α ∈ ({0} : Finset (ℤ × ℤ)) ↔ labelHarmonic m α ∈ ({0} : Finset (ℤ × ℤ)))
    (M : ℤ × ℤ → Matrix (Fin 12) (Fin 12) ℂ) (N : Matrix (Fin 12) (Fin 12) ℂ)
    (hpt : ∀ σ θ : ℝ, ∀ U : Fin 12 → ℂ, -(sesq12 N U U).re ≤ (sesq12 (symbolAt B M σ θ) U U).re)
    (X : ℤ × ℤ → Fin 12 → ℂ) (hX : Summable fun ι => cnormSq (X ι)) :
    -(∑' ι, (sesq12 N (X ι) (X ι)).re)
      ≤ ∑' ι, ∑ α ∈ H, (sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re := by
  have hXs : ∀ α : ℤ × ℤ, Summable fun ι => cnormSq (X (ι - α)) := by
    intro α
    have h := hX.comp_injective (sub_left_injective (b := α))
    exact h
  have hT : ∀ α : ℤ × ℤ, Summable fun ι => (sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re := by
    intro α
    refine Summable.of_norm_bounded ((hX.add (hXs α)).mul_left (∑ i, ∑ j, ‖M (labelHarmonic m α) i j‖)) ?_
    intro ι
    rw [Real.norm_eq_abs]
    exact re_sesq_le _ _ _
  have hNs : Summable fun ι => (sesq12 N (X ι) (X ι)).re := by
    refine Summable.of_norm_bounded ((hX.add hX).mul_left (∑ i, ∑ j, ‖N i j‖)) ?_
    intro ι
    rw [Real.norm_eq_abs]
    exact re_sesq_le _ _ _
  have hL : Tendsto (fun F : Finset (ℤ × ℤ) => -(∑ ι ∈ F, (sesq12 N (X ι) (X ι)).re)) atTop
      (𝓝 (-(∑' ι, (sesq12 N (X ι) (X ι)).re))) := by
    have h := hNs.hasSum
    unfold HasSum at h
    exact h.neg
  have hR : Tendsto (fun F : Finset (ℤ × ℤ) => ∑ ι ∈ F, ∑ α ∈ H,
        if ι - α ∈ F then (sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re else 0) atTop
      (𝓝 (∑ α ∈ H, ∑' ι, (sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re)) := by
    have e : ∀ F : Finset (ℤ × ℤ), (∑ ι ∈ F, ∑ α ∈ H,
          if ι - α ∈ F then (sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re else 0)
        = ∑ α ∈ H, ∑' ι, (if ι ∈ F ∧ ι - α ∈ F then
            (sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re else 0) := by
      intro F
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [tsum_eq_sum (s := F)]
      · refine Finset.sum_congr rfl fun ι hι => ?_
        simp [hι]
      · intro ι hι
        simp [hι]
    simp_rw [e]
    refine tendsto_finsetSum H fun α _ => ?_
    refine tendsto_tsum_of_dominated_convergence (bound := fun ι =>
      |(sesq12 (M (labelHarmonic m α)) (X ι) (X (ι - α))).re|) (hT α).abs ?_ ?_
    · intro ι
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop ({ι, ι - α} : Finset (ℤ × ℤ))] with F hF
      have h1 : ι ∈ F := hF (by simp)
      have h2 : ι - α ∈ F := hF (by simp)
      simp [h1, h2]
    · refine Filter.Eventually.of_forall fun F ι => ?_
      split_ifs <;> simp [Real.norm_eq_abs]
  rw [Summable.tsum_finsetSum fun α _ => hT α]
  exact le_of_tendsto_of_tendsto' hL hR fun F => symbolForm_finite m B H hH h0 M N hpt X F

end Sharp

end Internal

end Assembly

end CertCell

end Breakdown
