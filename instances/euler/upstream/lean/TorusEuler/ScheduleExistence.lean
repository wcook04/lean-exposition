import TorusEuler.FrequencySchedule

namespace TorusEuler

private noncomputable def nextOrder (B : ℕ → ℝ) (order : ℕ) (freq : ℝ) : ℕ :=
  if B (order + 1) ≤ freq then order + 1 else order

private theorem nextOrder_isGreatest {B : ℕ → ℝ} {order : ℕ} {freq : ℝ}
    (hOrder : 1 ≤ order) (hCurrent : B order ≤ freq) :
    IsGreatest {s | 1 ≤ s ∧ s ≤ order + 1 ∧ B s ≤ freq} (nextOrder B order freq) := by
  unfold nextOrder
  split_ifs with hAdvance
  · exact ⟨⟨Nat.succ_pos _, le_rfl, hAdvance⟩, fun _ hs => hs.2.1⟩
  · refine ⟨⟨hOrder, Nat.le_succ _, hCurrent⟩, ?_⟩
    intro s hs
    rcases hs with ⟨_, hsBound, hsThreshold⟩
    have hsNe : s ≠ order + 1 := by
      intro hsEq
      exact hAdvance (hsEq ▸ hsThreshold)
    exact Nat.le_of_lt_succ (lt_of_le_of_ne hsBound hsNe)

/-- At index `i`, the two entries are the paper's `q_(i+1)` and `λ_i`. -/
private noncomputable def scheduleState (b : ℕ) (B : ℕ → ℝ) (N : ℝ) : ℕ → ℕ × ℝ
  | 0 => (1, N)
  | i + 1 =>
    let previous := scheduleState b B N i
    (nextOrder B previous.1 previous.2, previous.2 ^ frequencyExponent b previous.1)

private theorem scheduleState_admissible (b : ℕ) (B : ℕ → ℝ) (N : ℝ)
    (hb : 1 ≤ b) (hN : 1 ≤ N) (hInit : B 1 ≤ N) (i : ℕ) :
    1 ≤ (scheduleState b B N i).1 ∧ 1 ≤ (scheduleState b B N i).2 ∧
      B (scheduleState b B N i).1 ≤ (scheduleState b B N i).2 := by
  induction i with
  | zero => exact ⟨le_rfl, hN, hInit⟩
  | succ i ih =>
    let previous := scheduleState b B N i
    have hMax := nextOrder_isGreatest ih.1 ih.2.2
    have hExponent : frequencyExponent b previous.1 ≠ 0 := by
      unfold frequencyExponent
      have hbPos : 0 < b := hb
      positivity
    have hFreq : previous.2 ≤ previous.2 ^ frequencyExponent b previous.1 :=
      le_self_pow₀ ih.2.1 hExponent
    exact ⟨hMax.1.1, ih.2.1.trans hFreq, hMax.1.2.2.trans hFreq⟩

/-- Equation (1.14) defines the one-based orders and zero-based frequencies together. -/
theorem frequencySchedule_exists (b : ℕ) (B : ℕ → ℝ) (N : ℝ)
    (hb : 1 ≤ b) (hN : 1 ≤ N) (hInit : B 1 ≤ N) :
    ∃ (q : ℕ → ℕ) (freq : ℕ → ℝ), q 1 = 1 ∧ freq 0 = N ∧
      (∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) ∧
      (∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2))) := by
  refine ⟨fun i => (scheduleState b B N i.pred).1, fun i => (scheduleState b B N i).2,
    rfl, rfl, fun _ => rfl, ?_⟩
  intro i
  have hAdmissible := scheduleState_admissible b B N hb hN hInit i
  exact nextOrder_isGreatest hAdmissible.1 hAdmissible.2.2

end TorusEuler
