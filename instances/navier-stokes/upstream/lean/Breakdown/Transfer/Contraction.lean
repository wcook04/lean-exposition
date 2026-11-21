import Breakdown.Transfer.StatementsAbstract

open scoped ENNReal NNReal
open Metric Set

noncomputable section

namespace Breakdown

namespace ContractionInternal

theorem exists_small_fixed {Z : Type} [NormedAddCommGroup Z] [CompleteSpace Z] (G : Z → Z)
    (b K : ℝ) (hb : 0 ≤ b) (hK : 0 ≤ K) (hsmall : 8 * K * b ≤ 1)
    (h1 : ∀ z, ‖G z‖ ≤ b + K * ‖z‖ ^ 2)
    (h2 : ∀ z w, ‖G z - G w‖ ≤ K * (‖z‖ + ‖w‖) * ‖z - w‖) :
    ∃ z, G z = z ∧ ‖z‖ ≤ 2 * b := by
  have hmaps : MapsTo G (closedBall 0 (2 * b)) (closedBall 0 (2 * b)) := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right] at hz ⊢
    have hz2 : ‖z‖ ^ 2 ≤ (2 * b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    calc ‖G z‖ ≤ b + K * ‖z‖ ^ 2 := h1 z
      _ ≤ b + K * (2 * b) ^ 2 := by gcongr
      _ ≤ 2 * b := by nlinarith [mul_nonneg hb (sub_nonneg.2 hsmall)]
  have hc : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict G _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    have hx : ‖(x : Z)‖ ≤ 2 * b := by
      have h := x.2
      rwa [mem_closedBall, dist_zero_right] at h
    have hy : ‖(y : Z)‖ ≤ 2 * b := by
      have h := y.2
      rwa [mem_closedBall, dist_zero_right] at h
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
    have hKb : K * (4 * b) ≤ 1 / 2 := by linarith
    calc ‖G x - G y‖ ≤ K * (‖(x : Z)‖ + ‖(y : Z)‖) * ‖(x : Z) - y‖ := h2 _ _
      _ ≤ K * (4 * b) * ‖(x : Z) - y‖ := by gcongr; linarith
      _ ≤ ((1 / 2 : ℝ≥0) : ℝ) * ‖(x : Z) - y‖ := by
        push_cast
        exact mul_le_mul_of_nonneg_right hKb (norm_nonneg _)
  obtain ⟨y, hys, hfix, -⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete
    hmaps hc (x := 0) (mem_closedBall_self (by linarith)) (edist_ne_top _ _)
  exact ⟨y, hfix, by simpa using hys⟩

end ContractionInternal

theorem contraction : ContractionStatement := by
  intro X Y _ _ _ _ _ _ A Γ Ev J N θ R hθ hθ1 hR
  have hnorm : ∀ (z : lp (fun _ : ℕ => Y) ∞) (n : ℕ), ‖z n‖ ≤ ‖z‖ :=
    fun z n => lp.norm_apply_le_norm ENNReal.top_ne_zero z n
  have hpow : ∀ n : ℕ, ‖θ ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow, Real.norm_of_nonneg hθ.le]
    exact pow_le_one₀ hθ.le hθ1
  have hpt : ∀ (ξ : X) (z : lp (fun _ : ℕ => Y) ∞) (n : ℕ),
      ‖(if n = 0 then Γ ξ else 0) + θ ^ n • N (z n) (z n)‖ ≤ ‖Γ‖ * ‖ξ‖ + ‖N‖ * ‖z‖ ^ 2 := by
    intro ξ z n
    have e1 : ‖(if n = 0 then Γ ξ else 0 : Y)‖ ≤ ‖Γ‖ * ‖ξ‖ := by
      split_ifs
      · exact Γ.le_opNorm ξ
      · simp only [norm_zero]; positivity
    have e2 : ‖θ ^ n • N (z n) (z n)‖ ≤ ‖N‖ * ‖z‖ ^ 2 := by
      rw [norm_smul]
      calc ‖θ ^ n‖ * ‖N (z n) (z n)‖ ≤ 1 * (‖N‖ * ‖z n‖ * ‖z n‖) := by
            gcongr
            exacts [hpow n, N.le_opNorm₂ _ _]
        _ ≤ ‖N‖ * ‖z‖ ^ 2 := by
            rw [one_mul, sq, ← mul_assoc]
            gcongr <;> exact hnorm z n
    exact (norm_add_le _ _).trans (add_le_add e1 e2)
  have hmem : ∀ (ξ : X) (z : lp (fun _ : ℕ => Y) ∞),
      Memℓp (fun n : ℕ => (if n = 0 then Γ ξ else 0) + θ ^ n • N (z n) (z n)) ∞ := by
    intro ξ z
    refine memℓp_infty ⟨‖Γ‖ * ‖ξ‖ + ‖N‖ * ‖z‖ ^ 2, ?_⟩
    rintro - ⟨n, rfl⟩
    exact hpt ξ z n
  obtain ⟨g, hg⟩ : ∃ g : X → lp (fun _ : ℕ => Y) ∞ → lp (fun _ : ℕ => Y) ∞,
      ∀ ξ z n, g ξ z n = (if n = 0 then Γ ξ else 0) + θ ^ n • N (z n) (z n) :=
    ⟨fun ξ z => ⟨_, hmem ξ z⟩, fun _ _ _ => rfl⟩
  have hgn : ∀ ξ z, ‖g ξ z‖ ≤ ‖Γ‖ * ‖ξ‖ + ‖N‖ * ‖z‖ ^ 2 := fun ξ z =>
    lp.norm_le_of_forall_le (by positivity) fun n => by rw [hg]; exact hpt ξ z n
  have hgd : ∀ ξ z w, ‖g ξ z - g ξ w‖ ≤ ‖N‖ * (‖z‖ + ‖w‖) * ‖z - w‖ := by
    intro ξ z w
    refine lp.norm_le_of_forall_le (by positivity) fun n => ?_
    have hd : ‖z n - w n‖ ≤ ‖z - w‖ := by
      have := hnorm (z - w) n
      rwa [lp.coeFn_sub, Pi.sub_apply] at this
    have hsplit : N (z n) (z n) - N (w n) (w n) = N (z n - w n) (z n) + N (w n) (z n - w n) := by
      simp only [map_sub, sub_apply]
      abel
    rw [lp.coeFn_sub, Pi.sub_apply, hg, hg, add_sub_add_left_eq_sub, ← smul_sub, hsplit,
      norm_smul]
    calc ‖θ ^ n‖ * ‖N (z n - w n) (z n) + N (w n) (z n - w n)‖
        ≤ 1 * (‖N‖ * ‖z n - w n‖ * ‖z n‖ + ‖N‖ * ‖w n‖ * ‖z n - w n‖) := by
          gcongr
          · exact hpow n
          · exact (norm_add_le _ _).trans (add_le_add (N.le_opNorm₂ _ _) (N.le_opNorm₂ _ _))
      _ ≤ 1 * (‖N‖ * ‖z - w‖ * ‖z‖ + ‖N‖ * ‖w‖ * ‖z - w‖) := by
          gcongr
          · exact hnorm z n
          · exact hnorm w n
      _ = ‖N‖ * (‖z‖ + ‖w‖) * ‖z - w‖ := by ring
  set K := ‖R‖ * ‖N‖ with hKdef
  set B := ‖R‖ * ‖Γ‖ with hBdef
  have hK : 0 ≤ K := by positivity
  have hB : 0 ≤ B := by positivity
  have hden : 0 < 8 * (K + 1) * (B + 1) := by positivity
  refine ⟨1 / (8 * (K + 1) * (B + 1)), by positivity, ‖R‖ * (‖Γ‖ + 2 * ‖N‖ * B), ?_⟩
  intro ξ hξ
  have hξ' : 8 * (K + 1) * (B + 1) * ‖ξ‖ ≤ 1 := by
    rw [le_div_iff₀ hden] at hξ
    linarith
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hsmall : 8 * K * (B * ‖ξ‖) ≤ 1 := by
    have : K * B ≤ (K + 1) * (B + 1) := by nlinarith
    calc 8 * K * (B * ‖ξ‖) = 8 * (K * B) * ‖ξ‖ := by ring
      _ ≤ 8 * ((K + 1) * (B + 1)) * ‖ξ‖ := by gcongr
      _ ≤ 1 := by linarith
  have hsmall2 : 2 * (B * ‖ξ‖) ≤ 1 := by
    have : 2 * B ≤ 8 * (K + 1) * (B + 1) := by nlinarith
    calc 2 * (B * ‖ξ‖) = 2 * B * ‖ξ‖ := by ring
      _ ≤ 8 * (K + 1) * (B + 1) * ‖ξ‖ := by gcongr
      _ ≤ 1 := hξ'
  have hRg : ∀ z, ‖R (g ξ z)‖ ≤ ‖R‖ * (‖Γ‖ * ‖ξ‖ + ‖N‖ * ‖z‖ ^ 2) := fun z =>
    (R.le_opNorm _).trans (by gcongr; exact hgn ξ z)
  obtain ⟨z, hz, hzn⟩ := ContractionInternal.exists_small_fixed (fun z => (R (g ξ z)).2)
    (B * ‖ξ‖) K (by positivity) hK hsmall
    (fun z => (norm_snd_le _).trans ((hRg z).trans (le_of_eq (by rw [hKdef, hBdef]; ring))))
    (fun z w => by
      rw [← Prod.snd_sub, ← map_sub]
      refine (norm_snd_le _).trans ((R.le_opNorm _).trans ?_)
      calc ‖R‖ * ‖g ξ z - g ξ w‖ ≤ ‖R‖ * (‖N‖ * (‖z‖ + ‖w‖) * ‖z - w‖) := by
            gcongr; exact hgd ξ z w
        _ = K * (‖z‖ + ‖w‖) * ‖z - w‖ := by rw [hKdef]; ring)
  refine ⟨(R (g ξ z)).1, z, ?_, ?_⟩
  · have hz1 : ‖z‖ ≤ 1 := by linarith
    have hzsq : ‖z‖ ^ 2 ≤ 2 * (B * ‖ξ‖) := by
      calc ‖z‖ ^ 2 = ‖z‖ * ‖z‖ := sq _
        _ ≤ 1 * ‖z‖ := by gcongr
        _ ≤ 2 * (B * ‖ξ‖) := by linarith
    calc ‖(R (g ξ z)).1‖ ≤ ‖R (g ξ z)‖ := norm_fst_le _
      _ ≤ ‖R‖ * (‖Γ‖ * ‖ξ‖ + ‖N‖ * ‖z‖ ^ 2) := hRg z
      _ ≤ ‖R‖ * (‖Γ‖ * ‖ξ‖ + ‖N‖ * (2 * (B * ‖ξ‖))) := by gcongr
      _ = ‖R‖ * (‖Γ‖ + 2 * ‖N‖ * B) * ‖ξ‖ := by ring
  · intro n
    have h := hR (g ξ z) n
    have hz' : (R (g ξ z)).2 = z := hz
    rw [hz', hg] at h
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [if_true, pow_zero, one_smul] at h ⊢
      rw [map_add, ← sub_sub, h]
      abel
    · simp only [if_neg hn, zero_add] at h ⊢
      exact h

end Breakdown
