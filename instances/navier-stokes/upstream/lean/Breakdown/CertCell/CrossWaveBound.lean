import Breakdown.CertCell.BridgeStatements

open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

private def gridPhase (N : ℕ) (n : ℤ) (k : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * n * k / N : ℝ) : ℂ) * Complex.I)

private lemma gridPhase_mul (N : ℕ) (a b : ℤ) (k : ℕ) :
    gridPhase N a k * gridPhase N b k = gridPhase N (a + b) k := by
  unfold gridPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma gridPhase_conj (N : ℕ) (a : ℤ) (k : ℕ) :
    (starRingEnd ℂ) (gridPhase N a k) = gridPhase N (-a) k := by
  unfold gridPhase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private lemma gridPhase_sum (N : ℕ) (j : ℤ) (hj : j.natAbs < N) :
    ∑ k ∈ Finset.range N, gridPhase N j k = if j = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp [gridPhase]
  · have hN : (N : ℝ) ≠ 0 := by
      have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hj
      exact_mod_cast this.ne'
    set z : ℂ := Complex.exp (((2 * Real.pi * j / N : ℝ) : ℂ) * Complex.I) with hz
    have hpow : ∀ k : ℕ, gridPhase N j k = z ^ k := by
      intro k
      rw [hz, ← Complex.exp_nat_mul]
      unfold gridPhase
      congr 1
      push_cast
      ring
    have hzN : z ^ N = 1 := by
      rw [hz, ← Complex.exp_nat_mul]
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
      have : (N : ℂ) * (((2 * Real.pi * j / N : ℝ) : ℂ) * Complex.I) = (j : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp
      rw [this]
      exact Complex.exp_int_mul_two_pi_mul_I j
    have hz1 : z ≠ 1 := by
      intro h1
      rw [hz, Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have him := congrArg Complex.im hn
      simp at him
      have h2 : (2 * Real.pi) * (j : ℝ) = (2 * Real.pi) * ((n : ℝ) * N) := by
        rw [div_eq_iff hN] at him
        linear_combination him
      have h3 : (j : ℝ) = (n : ℝ) * N := mul_left_cancel₀ (by positivity) h2
      have h4 : j = n * (N : ℤ) := by exact_mod_cast h3
      have h5 : j.natAbs = n.natAbs * N := by rw [h4, Int.natAbs_mul]; simp
      rcases eq_or_ne n 0 with hn0 | hn0
      · exact h (by rw [h4, hn0]; simp)
      · have : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn0
        have : N ≤ j.natAbs := by rw [h5]; nlinarith
        omega
    have hsum : (∑ k ∈ Finset.range N, z ^ k) * (z - 1) = 0 := by rw [geom_sum_mul, hzN, sub_self]
    rw [Finset.sum_congr rfl (fun k _ => hpow k)]
    exact (mul_eq_zero.mp hsum).resolve_right (sub_ne_zero.mpr hz1)

private lemma azimuthPhase_grid (m N : ℕ) (hm : m ≠ 0) (hN : N ≠ 0) (n : ℤ) (k : ℕ) :
    azimuthPhase m n (2 * Real.pi * k / ((m : ℝ) * N)) = gridPhase N n k := by
  unfold azimuthPhase gridPhase
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have : (n : ℝ) * m * (2 * Real.pi * k / ((m : ℝ) * N)) = 2 * Real.pi * n * k / N := by
    field_simp
  rw [this]

private lemma curlOfGrad_add (g g' : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    curlOfGrad (g + g') i = curlOfGrad g i + curlOfGrad g' i := by
  simp only [curlOfGrad, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma curlOfGrad_smul (c : ℂ) (g : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    curlOfGrad (c • g) i = c * curlOfGrad g i := by
  simp only [curlOfGrad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private lemma curlGradOfSecondDeriv_add (h h' : Fin 3 × Fin 3 × Fin 3 → ℂ) (il : Fin 3 × Fin 3) :
    curlGradOfSecondDeriv (h + h') il = curlGradOfSecondDeriv h il + curlGradOfSecondDeriv h' il := by
  simp only [curlGradOfSecondDeriv, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma curlGradOfSecondDeriv_smul (c : ℂ) (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (il : Fin 3 × Fin 3) :
    curlGradOfSecondDeriv (c • h) il = c * curlGradOfSecondDeriv h il := by
  simp only [curlGradOfSecondDeriv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private lemma stretchBilin_add_model (gW gW' : Fin 3 × Fin 3 → ℂ) (hW hW' : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    stretchBilin (gW + gW') (hW + hW') a g a' g'
      = stretchBilin gW hW a g a' g' + stretchBilin gW' hW' a g a' g' := by
  simp only [stretchBilin, Pi.add_apply, curlGradOfSecondDeriv_add, add_div, mul_add, add_mul, Finset.sum_add_distrib]
  ring

private lemma stretchBilin_smul_model (c : ℂ) (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    stretchBilin (c • gW) (c • hW) a g a' g' = c * stretchBilin gW hW a g a' g' := by
  simp only [stretchBilin, Pi.smul_apply, smul_eq_mul, curlGradOfSecondDeriv_smul, div_eq_mul_inv, mul_add, add_mul,
    mul_neg, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_comm, mul_assoc, mul_left_comm]

private lemma stretchBilin_add_left (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (a b : Fin 3 → ℂ) (g f : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    stretchBilin gW hW (a + b) (g + f) a' g'
      = stretchBilin gW hW a g a' g' + stretchBilin gW hW b f a' g' := by
  simp only [stretchBilin, Pi.add_apply, curlOfGrad_add, mul_add, add_mul, Finset.sum_add_distrib]
  ring

private lemma stretchBilin_smul_left (c : ℂ) (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    stretchBilin gW hW (c • a) (c • g) a' g' = c * stretchBilin gW hW a g a' g' := by
  simp only [stretchBilin, Pi.smul_apply, smul_eq_mul, curlOfGrad_smul, div_eq_mul_inv, mul_add, add_mul,
    mul_neg, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_comm, mul_assoc, mul_left_comm]

private lemma stretchBilin_add_right (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' b' : Fin 3 → ℂ) (g' f' : Fin 3 × Fin 3 → ℂ) :
    stretchBilin gW hW a g (a' + b') (g' + f')
      = stretchBilin gW hW a g a' g' + stretchBilin gW hW a g b' f' := by
  simp only [stretchBilin, Pi.add_apply, curlOfGrad_add, mul_add, Finset.sum_add_distrib]
  ring

private lemma stretchBilin_smul_right (c : ℂ) (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    stretchBilin gW hW a g (c • a') (c • g') = c * stretchBilin gW hW a g a' g' := by
  simp only [stretchBilin, Pi.smul_apply, smul_eq_mul, curlOfGrad_smul, div_eq_mul_inv, mul_add, add_mul,
    mul_neg, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_comm, mul_assoc, mul_left_comm]

private lemma curlOfGrad_sum (S : Finset ℤ) (c : ℤ → ℂ) (g : ℤ → Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    curlOfGrad (∑ n ∈ S, c n • g n) i = ∑ n ∈ S, c n * curlOfGrad (g n) i := by
  classical
  refine Finset.induction_on S (by simp [curlOfGrad]) ?_
  intro n S hn ih
  rw [Finset.sum_insert hn, Finset.sum_insert hn, curlOfGrad_add, curlOfGrad_smul, ih]

private lemma curlGradOfSecondDeriv_sum (S : Finset ℤ) (c : ℤ → ℂ) (h : ℤ → Fin 3 × Fin 3 × Fin 3 → ℂ)
    (il : Fin 3 × Fin 3) :
    curlGradOfSecondDeriv (∑ n ∈ S, c n • h n) il = ∑ n ∈ S, c n * curlGradOfSecondDeriv (h n) il := by
  classical
  refine Finset.induction_on S (by simp [curlGradOfSecondDeriv]) ?_
  intro n S hn ih
  rw [Finset.sum_insert hn, Finset.sum_insert hn, curlGradOfSecondDeriv_add, curlGradOfSecondDeriv_smul, ih]

private lemma curlOfGrad_star (g : Fin 3 × Fin 3 → ℂ) : curlOfGrad (star g) = star (curlOfGrad g) := by
  funext i
  simp [curlOfGrad, Complex.conj_ofReal]

private lemma cnormSq_star {ι : Type*} [Fintype ι] (z : ι → ℂ) : cnormSq (star z) = cnormSq z := by
  simp [cnormSq]

private lemma cnormSq_nonneg' {ι : Type*} [Fintype ι] (z : ι → ℂ) : 0 ≤ cnormSq z :=
  Finset.sum_nonneg fun _ _ => by positivity

private lemma cnormSq_ofReal {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ((cnormSq z : ℝ) : ℂ) = ∑ b, z b * (starRingEnd ℂ) (z b) := by
  simp only [cnormSq, Complex.ofReal_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

private lemma grid_mean_sq_complex {ι : Type*} [Fintype ι] (N : ℕ) (A : Finset ℤ) (e : ℤ → ℤ)
    (v : ℤ → ι → ℂ) (he : ∀ n ∈ A, ∀ n' ∈ A, (e n - e n').natAbs < N ∧ (e n = e n' → n = n')) :
    ∑ k ∈ Finset.range N, ∑ b, (∑ n ∈ A, gridPhase N (e n) k * v n b)
        * ∑ n' ∈ A, gridPhase N (-e n') k * (starRingEnd ℂ) (v n' b)
      = ∑ b, ∑ n ∈ A, (N : ℂ) * (v n b * (starRingEnd ℂ) (v n b)) := by
  classical
  have key : ∀ b, ∀ n ∈ A, ∀ n' ∈ A, ∑ k ∈ Finset.range N,
      gridPhase N (e n) k * v n b * (gridPhase N (-e n') k * (starRingEnd ℂ) (v n' b))
        = if n = n' then (N : ℂ) * (v n b * (starRingEnd ℂ) (v n b)) else 0 := by
    intro b n hn n' hn'
    have hk : ∀ k, gridPhase N (e n) k * v n b * (gridPhase N (-e n') k * (starRingEnd ℂ) (v n' b))
        = gridPhase N (e n - e n') k * (v n b * (starRingEnd ℂ) (v n' b)) := by
      intro k
      rw [sub_eq_add_neg, ← gridPhase_mul]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.sum_mul, gridPhase_sum N _ (he n hn n' hn').1]
    by_cases h : n = n'
    · subst h
      simp
    · have h0 : e n - e n' ≠ 0 := fun h0 => h ((he n hn n' hn').2 (sub_eq_zero.mp h0))
      simp [h0, h]
  calc ∑ k ∈ Finset.range N, ∑ b, (∑ n ∈ A, gridPhase N (e n) k * v n b)
        * ∑ n' ∈ A, gridPhase N (-e n') k * (starRingEnd ℂ) (v n' b)
      = ∑ b, ∑ n ∈ A, ∑ n' ∈ A, ∑ k ∈ Finset.range N,
          gridPhase N (e n) k * v n b * (gridPhase N (-e n') k * (starRingEnd ℂ) (v n' b)) := by
        simp only [Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ b, ∑ n ∈ A, (N : ℂ) * (v n b * (starRingEnd ℂ) (v n b)) := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.sum_congr rfl (fun n' hn' => key b n hn n' hn'), Finset.sum_ite_eq]
        simp [hn]

private lemma grid_mean_sq {ι : Type*} [Fintype ι] (N : ℕ) (A : Finset ℤ) (e : ℤ → ℤ) (v : ℤ → ι → ℂ)
    (he : ∀ n ∈ A, ∀ n' ∈ A, (e n - e n').natAbs < N ∧ (e n = e n' → n = n')) :
    ∑ k ∈ Finset.range N, cnormSq (fun b => ∑ n ∈ A, gridPhase N (e n) k * v n b)
      = N * ∑ n ∈ A, cnormSq (v n) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast]
  simp only [cnormSq_ofReal, map_sum, map_mul, gridPhase_conj]
  rw [grid_mean_sq_complex N A e v he, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]

private def tripleModelMap (p q : (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) :
    ((Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ)) →ₗ[ℂ] ℂ where
  toFun w := stretchTriple w.1 w.2 p.1 p.2 q.1 q.2
  map_add' w w' := by
    simp only [stretchTriple, Prod.fst_add, Prod.snd_add, stretchBilin_add_model]
    ring
  map_smul' c w := by
    simp only [stretchTriple, Prod.smul_fst, Prod.smul_snd, stretchBilin_smul_model, RingHom.id_apply,
      smul_eq_mul]
    ring

private def tripleLeftMap (w : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ))
    (q : (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) : ((Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) →ₗ[ℂ] ℂ where
  toFun p := stretchTriple w.1 w.2 p.1 p.2 q.1 q.2
  map_add' p p' := by
    simp only [stretchTriple, Prod.fst_add, Prod.snd_add, stretchBilin_add_left, stretchBilin_add_right]
    ring
  map_smul' c p := by
    simp only [stretchTriple, Prod.smul_fst, Prod.smul_snd, stretchBilin_smul_left, stretchBilin_smul_right,
      RingHom.id_apply, smul_eq_mul]
    ring

private def tripleRightMap (w : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ))
    (p : (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) : ((Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) →ₗ[ℂ] ℂ where
  toFun q := stretchTriple w.1 w.2 p.1 p.2 q.1 q.2
  map_add' q q' := by
    simp only [stretchTriple, Prod.fst_add, Prod.snd_add, stretchBilin_add_left, stretchBilin_add_right]
    ring
  map_smul' c q := by
    simp only [stretchTriple, Prod.smul_fst, Prod.smul_snd, stretchBilin_smul_left, stretchBilin_smul_right,
      RingHom.id_apply, smul_eq_mul]
    ring

private lemma stretchTriple_expand (B A A' : Finset ℤ) (c d e : ℤ → ℂ)
    (w : ℤ → (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ)) (p q : ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) :
    stretchTriple (∑ n ∈ B, c n • w n).1 (∑ n ∈ B, c n • w n).2 (∑ n ∈ A, d n • p n).1 (∑ n ∈ A, d n • p n).2
        (∑ n ∈ A', e n • q n).1 (∑ n ∈ A', e n • q n).2
      = ∑ n ∈ B, ∑ n₁ ∈ A, ∑ n₂ ∈ A', c n * d n₁ * e n₂
          * stretchTriple (w n).1 (w n).2 (p n₁).1 (p n₁).2 (q n₂).1 (q n₂).2 := by
  have hM := map_sum (tripleModelMap (∑ n ∈ A, d n • p n) (∑ n ∈ A', e n • q n)) (fun n => c n • w n) B
  simp only [map_smul, smul_eq_mul] at hM
  refine hM.trans (Finset.sum_congr rfl fun n _ => ?_)
  have hL := map_sum (tripleLeftMap (w n) (∑ n ∈ A', e n • q n)) (fun n => d n • p n) A
  simp only [map_smul, smul_eq_mul] at hL
  change c n * tripleLeftMap (w n) (∑ n ∈ A', e n • q n) (∑ n ∈ A, d n • p n) = _
  rw [hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n₁ _ => ?_
  have hR := map_sum (tripleRightMap (w n) (p n₁)) (fun n => e n • q n) A'
  simp only [map_smul, smul_eq_mul] at hR
  change c n * (d n₁ * tripleRightMap (w n) (p n₁) (∑ n ∈ A', e n • q n)) = _
  rw [hR, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n₂ _ => ?_
  change c n * (d n₁ * (e n₂ * stretchTriple (w n).1 (w n).2 (p n₁).1 (p n₁).2 (q n₂).1 (q n₂).2)) = _
  ring

private lemma grid_mean_triple (N : ℕ) (B A A' : Finset ℤ)
    (w : ℤ → (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ)) (p q : ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ))
    (hN : ∀ n ∈ B, ∀ n₁ ∈ A, ∀ n₂ ∈ A', (n + n₁ + -n₂).natAbs < N) :
    ∑ k ∈ Finset.range N, stretchTriple (∑ n ∈ B, gridPhase N n k • w n).1 (∑ n ∈ B, gridPhase N n k • w n).2
        (∑ n ∈ A, gridPhase N n k • p n).1 (∑ n ∈ A, gridPhase N n k • p n).2
        (∑ n ∈ A', gridPhase N (-n) k • q n).1 (∑ n ∈ A', gridPhase N (-n) k • q n).2
      = (N : ℂ) * ∑ n ∈ B, ∑ n₁ ∈ A, ∑ n₂ ∈ A', if n + n₁ = n₂ then
          stretchTriple (w n).1 (w n).2 (p n₁).1 (p n₁).2 (q n₂).1 (q n₂).2 else 0 := by
  simp only [stretchTriple_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n₁ hn₁ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n₂ hn₂ => ?_
  have hk : ∀ k, gridPhase N n k * gridPhase N n₁ k * gridPhase N (-n₂) k
      * stretchTriple (w n).1 (w n).2 (p n₁).1 (p n₁).2 (q n₂).1 (q n₂).2
      = gridPhase N (n + n₁ + -n₂) k * stretchTriple (w n).1 (w n).2 (p n₁).1 (p n₁).2 (q n₂).1 (q n₂).2 := by
    intro k
    rw [gridPhase_mul, gridPhase_mul]
  rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.sum_mul, gridPhase_sum N _ (hN n hn n₁ hn₁ n₂ hn₂)]
  by_cases h : n + n₁ = n₂
  · simp [h]
  · have h0 : n + n₁ + -n₂ ≠ 0 := by omega
    simp [h0, h]

private lemma grid_mean_crossCharge (N : ℕ) (A : Finset ℤ) (e : ℤ → ℤ)
    (p : ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) (σc γc ℓ : ℝ)
    (he : ∀ n ∈ A, ∀ n' ∈ A, (e n - e n').natAbs < N ∧ (e n = e n' → n = n')) :
    ∑ k ∈ Finset.range N, crossCharge σc γc ℓ (∑ n ∈ A, gridPhase N (e n) k • p n).1
        (∑ n ∈ A, gridPhase N (e n) k • p n).2
      = N * ∑ n ∈ A, crossCharge σc γc ℓ (p n).1 (p n).2 := by
  have h1 : ∀ k, (∑ n ∈ A, gridPhase N (e n) k • p n).1 = fun i => ∑ n ∈ A, gridPhase N (e n) k * (p n).1 i := by
    intro k
    funext i
    simp [Prod.fst_sum, Finset.sum_apply]
  have h2 : ∀ k, (∑ n ∈ A, gridPhase N (e n) k • p n).2
      = fun ij => ∑ n ∈ A, gridPhase N (e n) k * (p n).2 ij := by
    intro k
    funext ij
    simp [Prod.snd_sum, Finset.sum_apply]
  have h3 : ∀ k, curlOfGrad (∑ n ∈ A, gridPhase N (e n) k • p n).2
      = fun i => ∑ n ∈ A, gridPhase N (e n) k * curlOfGrad (p n).2 i := by
    intro k
    funext i
    rw [Prod.snd_sum]
    simp only [Prod.smul_snd]
    exact curlOfGrad_sum A _ _ i
  have hc := grid_mean_sq N A e (fun n => curlOfGrad (p n).2) he
  have hg := grid_mean_sq N A e (fun n => (p n).2) he
  have ha := grid_mean_sq N A e (fun n => (p n).1) he
  simp only [crossCharge, h3]
  simp only [h2, h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, hc, hg, ha]
  ring

private lemma twice_mul_le (x y c : ℝ) (hc : 0 < c) : 2 * x * y ≤ c * x ^ 2 + c⁻¹ * y ^ 2 := by
  have e : c * x ^ 2 + c⁻¹ * y ^ 2 - 2 * x * y = c⁻¹ * (c * x - y) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ c⁻¹ * (c * x - y) ^ 2 := by positivity
  linarith

private lemma weighted_pair_bound (s t ℓ β p1 p2 p3 q1 q2 q3 : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hℓ : 0 < ℓ)
    (hβ : 0 < β) :
    2 * (s * p1 * q1 + t * (p2 * q3 + q2 * p3)) ≤
      β * (s * p1 ^ 2 + t * (ℓ * p3 ^ 2 + p2 ^ 2 / ℓ)) + β⁻¹ * (s * q1 ^ 2 + t * (ℓ * q3 ^ 2 + q2 ^ 2 / ℓ)) := by
  have y1 := mul_le_mul_of_nonneg_left (twice_mul_le p1 q1 β hβ) hs
  have y2 := mul_le_mul_of_nonneg_left (twice_mul_le p2 q3 (β / ℓ) (by positivity)) ht
  have y3 := mul_le_mul_of_nonneg_left (twice_mul_le p3 q2 (β * ℓ) (by positivity)) ht
  have e : β * (s * p1 ^ 2 + t * (ℓ * p3 ^ 2 + p2 ^ 2 / ℓ)) + β⁻¹ * (s * q1 ^ 2 + t * (ℓ * q3 ^ 2 + q2 ^ 2 / ℓ))
      = s * (β * p1 ^ 2 + β⁻¹ * q1 ^ 2) + t * (β / ℓ * p2 ^ 2 + (β / ℓ)⁻¹ * q3 ^ 2)
        + t * (β * ℓ * p3 ^ 2 + (β * ℓ)⁻¹ * q2 ^ 2) := by
    field_simp
    ring
  rw [e]
  nlinarith

private lemma crossCharge_star (σc γc ℓ : ℝ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) :
    crossCharge σc γc ℓ (star a) (star g) = crossCharge σc γc ℓ a g := by
  unfold crossCharge
  rw [curlOfGrad_star, cnormSq_star, cnormSq_star, cnormSq_star]

private lemma mean_bound_combine (N : ℕ) (hN : 0 < N) (T : ℂ) (st : ℕ → ℂ) (cu cy : ℕ → ℝ) (β X Y : ℝ)
    (hexp : ∑ k ∈ Finset.range N, st k = N * T) (hpt : ∀ k, 2 * ‖st k‖ ≤ β * cu k + β⁻¹ * cy k)
    (hU : ∑ k ∈ Finset.range N, cu k = N * X) (hY : ∑ k ∈ Finset.range N, cy k = N * Y) :
    2 * ‖T‖ ≤ β * X + β⁻¹ * Y := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) * (2 * ‖T‖) = 2 * ‖∑ k ∈ Finset.range N, st k‖ := by
    rw [hexp, norm_mul, Complex.norm_natCast]
    ring
  have h2 : 2 * ‖∑ k ∈ Finset.range N, st k‖ ≤ ∑ k ∈ Finset.range N, 2 * ‖st k‖ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
  have h3 : ∑ k ∈ Finset.range N, 2 * ‖st k‖ ≤ ∑ k ∈ Finset.range N, (β * cu k + β⁻¹ * cy k) :=
    Finset.sum_le_sum fun k _ => hpt k
  have h4 : ∑ k ∈ Finset.range N, (β * cu k + β⁻¹ * cy k) = N * (β * X + β⁻¹ * Y) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hU, hY]
    ring
  exact le_of_mul_le_mul_left (by linarith) hNpos

theorem crossWaveBound (hB : StretchTripleBoundHolds) : CrossWaveBoundHolds := by
  intro m A A' B x x' wg wh σc γc ℓ βc hm hσ hγ hℓ hβ hS hG
  set S : ℕ := ∑ n ∈ B, n.natAbs + ∑ n ∈ A, n.natAbs + ∑ n ∈ A', n.natAbs with hSdef
  set N : ℕ := 2 * S + 1 with hNdef
  have hN0 : N ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have bB : ∀ n ∈ B, n.natAbs ≤ ∑ n ∈ B, n.natAbs := fun n hn =>
    Finset.single_le_sum (f := fun n : ℤ => n.natAbs) (fun _ _ => Nat.zero_le _) hn
  have bA : ∀ n ∈ A, n.natAbs ≤ ∑ n ∈ A, n.natAbs := fun n hn =>
    Finset.single_le_sum (f := fun n : ℤ => n.natAbs) (fun _ _ => Nat.zero_le _) hn
  have bA' : ∀ n ∈ A', n.natAbs ≤ ∑ n ∈ A', n.natAbs := fun n hn =>
    Finset.single_le_sum (f := fun n : ℤ => n.natAbs) (fun _ _ => Nat.zero_le _) hn
  have hfreq : ∀ n ∈ B, ∀ n₁ ∈ A, ∀ n₂ ∈ A', (n + n₁ + -n₂).natAbs < N := by
    intro n hn n₁ hn₁ n₂ hn₂
    have := bB n hn
    have := bA n₁ hn₁
    have := bA' n₂ hn₂
    omega
  have hexp := grid_mean_triple N B A A' (fun n => (wg n, wh n)) x (fun n => star (x' n)) hfreq
  have hU := grid_mean_crossCharge N A (fun n => n) x σc γc ℓ (by
    intro n hn n' hn'
    refine ⟨?_, id⟩
    have := bA n hn
    have := bA n' hn'
    omega)
  have hY := grid_mean_crossCharge N A' (fun n => -n) (fun n => star (x' n)) σc γc ℓ (by
    intro n hn n' hn'
    refine ⟨?_, fun h => by omega⟩
    have := bA' n hn
    have := bA' n' hn'
    omega)
  simp only [Prod.fst_star, Prod.snd_star, crossCharge_star] at hY
  refine mean_bound_combine N (by omega) _ _ _ _ βc _ _ hexp ?_ hU hY
  intro k
  have hW1 : ∀ ij, (∑ n ∈ B, gridPhase N n k
      • ((wg n, wh n) : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ))).1 ij
        = ∑ n ∈ B, gridPhase N n k * wg n ij := by
    intro ij
    simp [Prod.fst_sum, Finset.sum_apply]
  have hW2 : (∑ n ∈ B, gridPhase N n k
      • ((wg n, wh n) : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ))).2
        = ∑ n ∈ B, gridPhase N n k • wh n := by
    simp [Prod.snd_sum]
  have hsym : ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3,
      (((∑ n ∈ B, gridPhase N n k
        • ((wg n, wh n) : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ))).1 (i, j)
      + (∑ n ∈ B, gridPhase N n k
        • ((wg n, wh n) : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ))).1 (j, i)) / 2) * u j)
        ≤ σc ^ 2 * cnormSq u := by
    intro u
    have h := hS (2 * Real.pi * k / ((m : ℝ) * N)) u
    simp only [azimuthPhase_grid m N hm0 hN0] at h
    refine le_of_eq_of_le ?_ h
    congr 1
    funext i
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hW1, hW1, ← Finset.sum_add_distrib, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  have hcurl : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, curlGradOfSecondDeriv
      (∑ n ∈ B, gridPhase N n k
        • ((wg n, wh n) : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ))).2 (j, l) * u l)
        ≤ γc ^ 2 * cnormSq u := by
    intro u
    have h := hG (2 * Real.pi * k / ((m : ℝ) * N)) u
    simp only [azimuthPhase_grid m N hm0 hN0] at h
    rw [hW2]
    simp only [curlGradOfSecondDeriv_sum]
    exact h
  have hb := hB _ _ σc γc hσ hγ hsym hcurl (∑ n ∈ A, gridPhase N n k • x n).1 (∑ n ∈ A, gridPhase N n k • x n).2
    (∑ n ∈ A', gridPhase N (-n) k • star (x' n)).1 (∑ n ∈ A', gridPhase N (-n) k • star (x' n)).2
  have hw := weighted_pair_bound σc (3 / (2 * Real.sqrt 2) * γc) ℓ βc
    (Real.sqrt (cnormSq (curlOfGrad (∑ n ∈ A, gridPhase N n k • x n).2)))
    (Real.sqrt (cnormSq (∑ n ∈ A, gridPhase N n k • x n).1))
    (Real.sqrt (cnormSq (∑ n ∈ A, gridPhase N n k • x n).2))
    (Real.sqrt (cnormSq (curlOfGrad (∑ n ∈ A', gridPhase N (-n) k • star (x' n)).2)))
    (Real.sqrt (cnormSq (∑ n ∈ A', gridPhase N (-n) k • star (x' n)).1))
    (Real.sqrt (cnormSq (∑ n ∈ A', gridPhase N (-n) k • star (x' n)).2))
    hσ (by positivity) hℓ hβ
  simp only [Real.sq_sqrt (cnormSq_nonneg' _)] at hw
  unfold crossCharge
  linarith

end Bridge

end CertCell

end Breakdown
