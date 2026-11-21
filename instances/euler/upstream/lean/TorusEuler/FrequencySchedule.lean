import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace TorusEuler

/-- The frequency exponent in (1.14). It is applied to positive orders in the paper. -/
def frequencyExponent (b s : ℕ) : ℕ :=
  320 * b * (s + 1)

theorem frequencyExponent_mono (b : ℕ) : Monotone (frequencyExponent b) := by
  intro s t hst
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hst 1)

/-- The maximum in (1.14) preserves admissible current orders and increases by at most one. -/
theorem frequencySchedule_order_step {B : ℕ → ℝ} {q qNext : ℕ} {freqPrev : ℝ}
    (hmax : IsGreatest {s | 1 ≤ s ∧ s ≤ q + 1 ∧ B s ≤ freqPrev} qNext)
    (hq : 1 ≤ q) (hCurrent : B q ≤ freqPrev) :
    q ≤ qNext ∧ qNext ≤ q + 1 := by
  exact ⟨hmax.2 ⟨hq, Nat.le_succ _, hCurrent⟩, hmax.1.2.1⟩

/-- The next order advances exactly when the next threshold is reached. -/
theorem frequencySchedule_order_advance_iff {B : ℕ → ℝ} {q qNext : ℕ} {freqPrev : ℝ}
    (hmax : IsGreatest {s | 1 ≤ s ∧ s ≤ q + 1 ∧ B s ≤ freqPrev} qNext) :
    qNext = q + 1 ↔ B (q + 1) ≤ freqPrev := by
  constructor
  · rintro rfl
    exact hmax.1.2.2
  · intro hThreshold
    exact le_antisymm hmax.1.2.1 (hmax.2 ⟨Nat.succ_pos _, le_rfl, hThreshold⟩)

/-- The recurrence (1.14) preserves the lower bound one and makes the frequencies nondecreasing. -/
theorem frequencySchedule_frequency_mono (b : ℕ) (q : ℕ → ℕ) (freq : ℕ → ℝ)
    (hb : 1 ≤ b) (hInit : 1 ≤ freq 0)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) :
    Monotone freq := by
  have hOne : ∀ i, 1 ≤ freq i := by
    intro i
    induction i with
    | zero => exact hInit
    | succ i hi => rw [hFreq i]; exact one_le_pow₀ hi
  apply monotone_nat_of_le_succ
  intro i
  rw [hFreq i]
  have hbPos : 0 < b := hb
  exact le_self_pow₀ (hOne i) (by unfold frequencyExponent; positivity)

/-- For positive stage indices, the previous choice and frequency monotonicity
give the admissibility needed for the order step. -/
theorem frequencySchedule_order_steps (B freq : ℕ → ℝ) (q : ℕ → ℕ)
    (hqInit : q 1 = 1) (hInit : B 1 ≤ freq 0) (hFreqMono : Monotone freq)
    (hMax : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2)))
    (i : ℕ) : q (i + 1) ≤ q (i + 2) ∧ q (i + 2) ≤ q (i + 1) + 1 := by
  apply frequencySchedule_order_step (hMax i)
  cases i with
  | zero => simp [hqInit]
  | succ i => exact (hMax i).1.1
  cases i with
  | zero => simpa [hqInit] using hInit
  | succ i => exact (hMax i).1.2.2.trans (hFreqMono (Nat.le_succ i))

/-- Appendix C's exact three-step logarithmic identity. The index `i` denotes the
paper's `j - 1`, so the three exponents are at indices `i + 1` through `i + 3`. -/
theorem frequencySchedule_three_log_steps (b : ℕ) (q : ℕ → ℕ) (freq L : ℕ → ℝ)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hL : ∀ i, L i = 4 * Real.log (freq (i + 1))) (i : ℕ) :
    L (i + 2) =
      4 * (frequencyExponent b (q (i + 1)) : ℝ) *
        (frequencyExponent b (q (i + 2)) : ℝ) *
        (frequencyExponent b (q (i + 3)) : ℝ) * Real.log (freq i) := by
  rw [hL, hFreq (i + 2), Real.log_pow, hFreq (i + 1), Real.log_pow, hFreq i, Real.log_pow]
  ring

/-- The floor (1.13), adjacent-order bounds and admissibility imply (1.15).
Here `i = j - 1` in the manuscript's notation. -/
theorem frequencySchedule_log_bound (b : ℕ) (q : ℕ → ℕ) (B freq L : ℕ → ℝ)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hL : ∀ i, L i = 4 * Real.log (freq (i + 1))) (i : ℕ)
    (hqStep : q (i + 1) ≤ q (i + 2))
    (hqNext : q (i + 3) ≤ q (i + 2) + 1)
    (hBPos : 0 < B (q (i + 2)))
    (hFloor : 4 * (frequencyExponent b (q (i + 2) + 1) : ℝ) ^ 3 ≤
      Real.log (B (q (i + 2))))
    (hAdmissible : B (q (i + 2)) ≤ freq i) :
    L (i + 2) ≤ (Real.log (freq i)) ^ 2 := by
  let K₁ : ℝ := frequencyExponent b (q (i + 1))
  let K₂ : ℝ := frequencyExponent b (q (i + 2))
  let K₃ : ℝ := frequencyExponent b (q (i + 3))
  let K : ℝ := frequencyExponent b (q (i + 2) + 1)
  have hK₂ : K₂ ≤ K := by
    dsimp only [K₂, K]
    exact_mod_cast frequencyExponent_mono b (Nat.le_succ (q (i + 2)))
  have hK₁ : K₁ ≤ K := by
    dsimp only [K₁, K]
    exact_mod_cast frequencyExponent_mono b (hqStep.trans (Nat.le_succ (q (i + 2))))
  have hK₃ : K₃ ≤ K := by
    dsimp only [K₃, K]
    exact_mod_cast frequencyExponent_mono b hqNext
  have hProduct : 4 * K₁ * K₂ * K₃ ≤ 4 * K ^ 3 := by
    calc
      4 * K₁ * K₂ * K₃ ≤ 4 * K * K * K := by gcongr
      _ = 4 * K ^ 3 := by ring
  have hLogThreshold : Real.log (B (q (i + 2))) ≤ Real.log (freq i) :=
    (Real.log_le_log_iff hBPos (hBPos.trans_le hAdmissible)).2 hAdmissible
  have hBound : 4 * K₁ * K₂ * K₃ ≤ Real.log (freq i) :=
    hProduct.trans (hFloor.trans hLogThreshold)
  have hLog : 0 ≤ Real.log (freq i) := by
    exact le_trans (by positivity : 0 ≤ 4 * K ^ 3) (hFloor.trans hLogThreshold)
  rw [frequencySchedule_three_log_steps b q freq L hFreq hL, sq]
  exact mul_le_mul_of_nonneg_right hBound hLog

/-- Equation (1.15) follows directly from the initial choice, recurrence, maxima and floor. -/
theorem frequencySchedule_log_bound_of_maxima (b : ℕ) (q : ℕ → ℕ) (B freq L : ℕ → ℝ)
    (hb : 1 ≤ b) (hqInit : q 1 = 1) (hInit : B 1 ≤ freq 0)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hL : ∀ i, L i = 4 * Real.log (freq (i + 1)))
    (hMax : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2)))
    (hBPos : ∀ s, 1 ≤ s → 0 < B s)
    (hFloor : ∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s))
    (i : ℕ) : L (i + 2) ≤ (Real.log (freq i)) ^ 2 := by
  have hBOne : 1 ≤ B 1 :=
    (Real.log_nonneg_iff (hBPos 1 le_rfl)).1 ((by positivity :
      0 ≤ 4 * (frequencyExponent b 2 : ℝ) ^ 3).trans (hFloor 1 le_rfl))
  have hFreqInit : 1 ≤ freq 0 := hBOne.trans hInit
  have hFreqMono := frequencySchedule_frequency_mono b q freq hb hFreqInit hFreq
  have hSteps := frequencySchedule_order_steps B freq q hqInit hInit hFreqMono hMax
  exact frequencySchedule_log_bound b q B freq L hFreq hL i (hSteps i).1 (hSteps (i + 1)).2
    (hBPos _ (hMax i).1.1) (hFloor _ (hMax i).1.1) (hMax i).1.2.2

end TorusEuler
