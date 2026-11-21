import TorusEuler.TerminalBorelCutoff
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Prod

/-! A smooth series with prescribed normal jets along the time-zero hyperplane. -/

open Set Filter Function
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem norm_iteratedFDeriv_comp_linear_le {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (g : X →L[ℝ] Y) (hg : ‖g‖ ≤ 1) {f : Y → Z} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ k (f ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ k f (g x)‖ := by
  rw [g.iteratedFDeriv_comp_right hf x (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hg)

set_option maxHeartbeats 1200000 in
/-- A sequence of smooth compactly supported boundary data has a smooth
parameterized Borel extension, with each specified normal derivative at zero. -/
theorem exists_terminalBorelExtension (a : ℕ → E → F)
    (ha : ∀ n, ContDiff ℝ ∞ (a n)) (hSupport : ∀ n, HasCompactSupport (a n)) :
    ∃ G : ℝ × E → F, ContDiff ℝ ∞ G ∧
      ∀ n (x : E), iteratedDeriv n (fun t : ℝ => G (t, x)) 0 = a n x := by
  have hA : ∀ n k : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ {ε : ℝ}, 0 < ε → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ k (terminalBorelAtom n ε) t‖ ≤ A * ε ^ n * ε⁻¹ ^ k :=
    exists_terminalBorelAtom_fderiv_bound
  choose A hA₀ hA using hA
  have hB : ∀ n k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x : E, ‖iteratedFDeriv ℝ k (a n) x‖ ≤ B := by
    intro n k
    obtain ⟨B, hB⟩ := ((ha n).continuous_iteratedFDeriv (by simp)).bounded_above_of_compact_support
      ((hSupport n).iteratedFDeriv k)
    exact ⟨B, (norm_nonneg _).trans (hB 0), hB⟩
  choose B hB₀ hB using hB
  let c (n k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A n i * B n (k - i)
  have hc₀ (n k : ℕ) : 0 ≤ c n k :=
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA₀ n i)) (hB₀ n _)
  let M (n : ℕ) : ℝ := 1 + ∑ k ∈ Finset.range n, c n k
  have hM (n : ℕ) : 1 ≤ M n := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hc₀ n k)
  have hM₀ (n : ℕ) : 0 < M n := zero_lt_one.trans_le (hM n)
  have hcM (n k : ℕ) (hk : k < n) : c n k ≤ M n :=
    (Finset.single_le_sum (f := fun j => c n j) (fun i _ => hc₀ n i) (Finset.mem_range.mpr hk)).trans
      (le_add_of_nonneg_left zero_le_one)
  let ρ (n : ℕ) : ℝ := (1 / 2) ^ n
  have hρ (n : ℕ) : 0 < ρ n := pow_pos (by norm_num) _
  have hρ₁ (n : ℕ) : ρ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hρSum : Summable ρ := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  let ε (n : ℕ) : ℝ := ρ n / M n
  have hε (n : ℕ) : 0 < ε n := div_pos (hρ n) (hM₀ n)
  have hε₁ (n : ℕ) : ε n ≤ 1 := (div_le_one (hM₀ n)).2 ((hρ₁ n).trans (hM n))
  let v (k n : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * (A n i * ε n ^ n * (ε n)⁻¹ ^ i) * B n (k - i)
  have hTerm₀ (n k i : ℕ) :
      0 ≤ (k.choose i : ℝ) * (A n i * ε n ^ n * (ε n)⁻¹ ^ i) * B n (k - i) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (hA₀ n i)
      (pow_nonneg (hε n).le _)) (pow_nonneg (inv_nonneg.mpr (hε n).le) _))) (hB₀ n _)
  have hv₀ (k n : ℕ) : 0 ≤ v k n := Finset.sum_nonneg fun i _ => hTerm₀ n k i
  have hεPow (n i : ℕ) (hi : i < n) : ε n ^ n * (ε n)⁻¹ ^ i ≤ ε n := by
    have heq : ε n ^ n * (ε n)⁻¹ ^ i = ε n ^ (n - i) := calc
      _ = ε n ^ (n - i + i) * (ε n)⁻¹ ^ i := by rw [Nat.sub_add_cancel hi.le]
      _ = _ := by rw [pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ (hε n).ne', one_pow, mul_one]
    rw [heq]
    simpa only [pow_one] using pow_le_pow_of_le_one (hε n).le (hε₁ n) (by omega : 1 ≤ n - i)
  have hvSmall (k n : ℕ) (hk : k < n) : v k n ≤ ρ n := calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * A n i * B n (k - i)) * ε n := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans_lt hk
      calc
        _ = ((k.choose i : ℝ) * A n i * B n (k - i)) * (ε n ^ n * (ε n)⁻¹ ^ i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hεPow n i hi')
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA₀ n i)) (hB₀ n _))
    _ = c n k * ε n := by rw [Finset.sum_mul]
    _ ≤ M n * ε n := mul_le_mul_of_nonneg_right (hcM n k hk) (hε n).le
    _ = ρ n := by
      dsimp only [ε]
      field_simp [(hM₀ n).ne']
  have hv (k : ℕ) : Summable (v k) :=
    .of_norm_bounded_eventually_nat hρSum <| (eventually_ge_atTop (k + 1)).mono fun n hn => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hv₀ k n)]
      exact hvSmall k n (by omega)
  let atom (n : ℕ) (z : ℝ × E) : F := terminalBorelAtom n (ε n) z.1 • a n z.2
  have hSmooth (n : ℕ) : ContDiff ℝ ∞ (atom n) :=
    ((contDiff_terminalBorelAtom n (ε n)).comp contDiff_fst).smul ((ha n).comp contDiff_snd)
  have hDeriv (k n : ℕ) (z : ℝ × E) : ‖iteratedFDeriv ℝ k (atom n) z‖ ≤ v k n := by
    refine (norm_iteratedFDeriv_smul_le ((contDiff_terminalBorelAtom n (ε n)).comp contDiff_fst)
      ((ha n).comp contDiff_snd) z (n := k) (by simp)).trans ?_
    apply Finset.sum_le_sum
    intro i _
    have hL := (norm_iteratedFDeriv_comp_linear_le (ContinuousLinearMap.fst ℝ ℝ E)
      (ContinuousLinearMap.norm_fst_le ℝ ℝ E) (contDiff_terminalBorelAtom n (ε n)) i z).trans
      (hA n i (hε n) z.1)
    have hR := (norm_iteratedFDeriv_comp_linear_le (ContinuousLinearMap.snd ℝ ℝ E)
      (ContinuousLinearMap.norm_snd_le ℝ ℝ E) (ha n) (k - i) z).trans
      (hB n (k - i) z.2)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)) hR (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hA n i (hε n) z.1)))
  let G (z : ℝ × E) : F := ∑' n, atom n z
  refine ⟨G, contDiff_tsum hSmooth (fun k _ => hv k) (fun k n z _ => hDeriv k n z), ?_⟩
  intro k x
  let slice (n : ℕ) (t : ℝ) : F := terminalBorelAtom n (ε n) t • a n x
  have hsmooth (n : ℕ) : ContDiff ℝ ∞ (slice n) :=
    (contDiff_terminalBorelAtom n (ε n)).smul contDiff_const
  have hslice (j n : ℕ) (t : ℝ) : ‖iteratedFDeriv ℝ j (slice n) t‖ ≤ v j n := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    change ‖iteratedDeriv j (fun y => terminalBorelAtom n (ε n) y • a n x) t‖ ≤ _
    rw [iteratedDeriv_smul_const ((contDiff_terminalBorelAtom n (ε n)).contDiffAt.of_le (by simp)),
      norm_smul, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hBzero : ‖a n x‖ ≤ B n 0 := by
      simpa only [norm_iteratedFDeriv_zero] using hB n 0 x
    refine (mul_le_mul (hA n j (hε n) t) hBzero (norm_nonneg _)
      ((norm_nonneg _).trans (hA n j (hε n) t))).trans ?_
    have hSingle := Finset.single_le_sum (f := fun i =>
      (j.choose i : ℝ) * (A n i * ε n ^ n * (ε n)⁻¹ ^ i) * B n (j - i))
      (fun i _ => hTerm₀ n j i) (Finset.mem_range.mpr (Nat.lt_succ_self j))
    simpa only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self] using hSingle
  have hsum : iteratedDeriv k (fun t => ∑' n, slice n t) 0 = ∑' n, iteratedDeriv k (slice n) 0 := by
    simp only [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
    rw [iteratedFDeriv_tsum_apply hsmooth (fun j _ => hv j) (fun j n t _ => hslice j n t)
      (show (k : ℕ∞) ≤ ⊤ from le_top)]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm.toContinuousLinearEquiv.map_tsum
  change iteratedDeriv k (fun t => ∑' n, slice n t) 0 = a k x
  rw [hsum, tsum_eq_single k]
  · change iteratedDeriv k (fun t => terminalBorelAtom k (ε k) t • a k x) 0 = _
    rw [iteratedDeriv_smul_const ((contDiff_terminalBorelAtom k (ε k)).contDiffAt.of_le (by simp)),
      iteratedDeriv_terminalBorelAtom_zero k k (hε k)]
    simp
  · intro n hn
    change iteratedDeriv k (fun t => terminalBorelAtom n (ε n) t • a n x) 0 = _
    rw [iteratedDeriv_smul_const ((contDiff_terminalBorelAtom n (ε n)).contDiffAt.of_le (by simp)),
      iteratedDeriv_terminalBorelAtom_zero n k (hε n)]
    simp [Ne.symm hn]

end

end TorusEuler
