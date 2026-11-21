import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.FarField

private lemma weightedBound_zero_iff {E : Type*} [SeminormedAddCommGroup E] (a : ℝ → Space → E)
    (C : ℝ) : WeightedBound a 0 C ↔ ∀ s y, ‖a s y‖ ≤ C := by
  unfold WeightedBound
  simp only [Real.rpow_zero, one_mul]

private lemma weightedBound_zero_of {E : Type*} [SeminormedAddCommGroup E] {a : ℝ → Space → E}
    {γ C : ℝ} (hγ : 0 ≤ γ) (h : WeightedBound a γ C) : ∀ s y, ‖a s y‖ ≤ C := by
  intro s y
  have h1 : (1 : ℝ) ≤ (1 + ‖y‖) ^ γ := Real.one_le_rpow (by linarith [norm_nonneg y]) hγ
  calc ‖a s y‖ = 1 * ‖a s y‖ := (one_mul _).symm
    _ ≤ (1 + ‖y‖) ^ γ * ‖a s y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ C := h s y

private lemma measurable_pairTensor {a b : ℝ → Space → Space}
    (ha : Measurable (fun p : ℝ × Space => a p.1 p.2))
    (hb : Measurable (fun p : ℝ × Space => b p.1 p.2)) :
    Measurable (fun p : ℝ × Space => pairTensor a b p.1 p.2) := by
  have hc : ∀ i : Fin 3, Measurable (fun x : Space => x i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.measurable
  refine measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun k => ?_))
  exact ((hc j).comp ha).mul ((hc k).comp hb)

private lemma boundedMeasurable_pairTensor (hTW : TensorWeight) {a b : ℝ → Space → Space}
    {A B : ℝ} (ha : Measurable (fun p : ℝ × Space => a p.1 p.2))
    (hb : Measurable (fun p : ℝ × Space => b p.1 p.2))
    (hA : ∀ s y, ‖a s y‖ ≤ A) (hB : ∀ s y, ‖b s y‖ ≤ B) :
    IsBoundedMeasurableTensor (pairTensor a b) := by
  refine ⟨measurable_pairTensor ha hb, A * B, ?_⟩
  have h := hTW a b 0 0 A B le_rfl le_rfl ((weightedBound_zero_iff a A).2 hA)
    ((weightedBound_zero_iff b B).2 hB)
  rw [add_zero] at h
  exact (weightedBound_zero_iff _ _).1 h

private lemma pairTensor_add_left (a b c : ℝ → Space → Space) :
    pairTensor (a + b) c = pairTensor a c + pairTensor b c := by
  funext s z j k
  simp [pairTensor, tensorField, add_mul]

private lemma pairTensor_add_right (a b c : ℝ → Space → Space) :
    pairTensor a (b + c) = pairTensor a b + pairTensor a c := by
  funext s z j k
  simp [pairTensor, tensorField, mul_add]

private def neumannIterate (g V : ℝ → Space → Space) : ℕ → ℝ → Space → Space
  | 0 => fun _ _ => 0
  | n + 1 => fun s y => g s y + profileOp 1 (pairTensor V (neumannIterate g V n)) s y

theorem neumannDecay_of_op :
    OpWeightedBound → OpLinear → OpMeasurable → TensorWeight → NeumannDecay := by
  intro hOp hLin hMeas hTW hK W hW hbdd htail hfix
  obtain ⟨C, hC⟩ := hbdd
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0)
  have e1 : (1 + ((0 : ℕ) : ℝ) / 2) = 1 := by norm_num
  have e2 : min (0 : ℝ) (((0 : ℕ) : ℝ) + 1) = 0 := by norm_num
  have e3 : min (3 / 4 : ℝ) (((0 : ℕ) : ℝ) + 1) = 3 / 4 := by norm_num
  obtain ⟨K0, hK0, hT0⟩ := hOp hK 0 (by norm_num) 0 le_rfl (by norm_num) (by norm_num)
  obtain ⟨K1, hK1, hT1⟩ := hOp hK 0 (by norm_num) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
  rw [e1, e2] at hT0
  rw [e1, e3] at hT1
  have hadd := (hLin hK).1 1 le_rfl
  obtain ⟨ε, hεpos, hK0ε, hK1ε⟩ : ∃ ε : ℝ, 0 < ε ∧ K0 * ε ≤ 1 / 2 ∧ K1 * ε ≤ 1 / 2 := by
    have hD : (0 : ℝ) < 2 * (K0 + K1 + 1) := by linarith
    refine ⟨1 / (2 * (K0 + K1 + 1)), by positivity, ?_, ?_⟩ <;>
      rw [mul_one_div, div_le_iff₀ hD] <;> linarith
  obtain ⟨R', hR'⟩ := htail ε hεpos
  obtain ⟨R, hR0, hRR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ s y, R ≤ ‖y‖ → ‖W s y‖ ≤ ε :=
    ⟨max R' 0, le_max_right _ _, fun s y hy => hR' s y (le_trans (le_max_left _ _) hy)⟩
  obtain ⟨W1, V, hW1m, hVm, hsplit, hVb, hW1w⟩ : ∃ W1 V : ℝ → Space → Space,
      Measurable (fun p : ℝ × Space => W1 p.1 p.2) ∧ Measurable (fun p : ℝ × Space => V p.1 p.2) ∧
      W1 + V = W ∧ (∀ s y, ‖V s y‖ ≤ ε) ∧
      WeightedBound W1 (3 / 4) ((1 + R) ^ (3 / 4 : ℝ) * C) := by
    have hm1 : Measurable (fun p : ℝ × Space => if ‖p.2‖ < R then W p.1 p.2 else 0) :=
      Measurable.ite (measurableSet_lt (measurable_norm.comp measurable_snd) measurable_const)
        hW measurable_const
    refine ⟨fun s y => if ‖y‖ < R then W s y else 0, W - fun s y => if ‖y‖ < R then W s y else 0,
      hm1, hW.sub hm1, by abel, ?_, ?_⟩
    · intro s y
      by_cases h : ‖y‖ < R
      · simp [h, hεpos.le]
      · simp only [Pi.sub_apply, h, ↓reduceIte, sub_zero]
        exact hRR s y (not_lt.1 h)
    · intro s y
      by_cases h : ‖y‖ < R
      · simp only [h, ↓reduceIte]
        exact mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)) (hC s y)
          (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
      · simp only [h, ↓reduceIte, norm_zero, mul_zero]
        exact mul_nonneg (Real.rpow_nonneg (by linarith) _) hC0
  have hVw0 : WeightedBound V 0 ε := (weightedBound_zero_iff V ε).2 hVb
  have hbW1W := boundedMeasurable_pairTensor hTW hW1m hW (weightedBound_zero_of (by norm_num) hW1w) hC
  have hbVW := boundedMeasurable_pairTensor hTW hVm hW hVb hC
  have hPT : pairTensor W W = pairTensor W1 W + pairTensor V W := by
    rw [← pairTensor_add_left, hsplit]
  obtain ⟨g, hgdef⟩ : ∃ g, g = profileOp 1 (pairTensor W1 W) := ⟨_, rfl⟩
  have hgm : Measurable (fun p : ℝ × Space => g p.1 p.2) := by
    rw [hgdef]; exact hMeas 1 _ (measurable_pairTensor hW1m hW)
  obtain ⟨G, hG0, hgw⟩ : ∃ G, 0 ≤ G ∧ WeightedBound g (3 / 4) G := by
    have hR1 : (0 : ℝ) ≤ (1 + R) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
    refine ⟨K1 * ((1 + R) ^ (3 / 4 : ℝ) * C * C),
      mul_nonneg hK1 (mul_nonneg (mul_nonneg hR1 hC0) hC0), ?_⟩
    have h := hTW W1 W (3 / 4) 0 ((1 + R) ^ (3 / 4 : ℝ) * C) C (by norm_num) le_rfl hW1w
      ((weightedBound_zero_iff W C).2 hC)
    rw [add_zero] at h
    rw [hgdef]
    exact hT1 _ _ h
  have hWeq : ∀ s y, W s y = g s y + profileOp 1 (pairTensor V W) s y := by
    intro s y
    rw [hgdef]
    calc W s y = profileOp 1 (pairTensor W W) s y := hfix s y
      _ = _ := by rw [hPT]; exact hadd _ _ hbW1W hbVW s y
  have hind : ∀ n : ℕ, Measurable (fun p : ℝ × Space => neumannIterate g V n p.1 p.2) ∧
      WeightedBound (neumannIterate g V n) (3 / 4) (2 * G) ∧
      ∀ s y, ‖W s y - neumannIterate g V n s y‖ ≤ C * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, fun s y => ?_, fun s y => ?_⟩
      · show Measurable (fun _ : ℝ × Space => (0 : Space))
        exact measurable_const
      · show (1 + ‖y‖) ^ (3 / 4 : ℝ) * ‖(0 : Space)‖ ≤ 2 * G
        rw [norm_zero, mul_zero]; linarith
      · show ‖W s y - 0‖ ≤ C * (1 / 2) ^ 0
        rw [sub_zero, pow_zero, mul_one]; exact hC s y
    | succ n ih =>
      obtain ⟨hm, hw, hd⟩ := ih
      have hmd : Measurable (fun p : ℝ × Space => (W - neumannIterate g V n) p.1 p.2) := hW.sub hm
      have hbVu := boundedMeasurable_pairTensor hTW hVm hm hVb (weightedBound_zero_of (by norm_num) hw)
      have hbVd := boundedMeasurable_pairTensor hTW hVm hmd hVb hd
      have hTsplit : pairTensor V W =
          pairTensor V (neumannIterate g V n) + pairTensor V (W - neumannIterate g V n) := by
        rw [← pairTensor_add_right]; congr 1; abel
      have hT : ∀ s y, profileOp 1 (pairTensor V W) s y =
          profileOp 1 (pairTensor V (neumannIterate g V n)) s y +
            profileOp 1 (pairTensor V (W - neumannIterate g V n)) s y := by
        intro s y; rw [hTsplit]; exact hadd _ _ hbVu hbVd s y
      refine ⟨?_, fun s y => ?_, fun s y => ?_⟩
      · show Measurable (fun p : ℝ × Space =>
          g p.1 p.2 + profileOp 1 (pairTensor V (neumannIterate g V n)) p.1 p.2)
        exact hgm.add (hMeas 1 _ (measurable_pairTensor hVm hm))
      · show (1 + ‖y‖) ^ (3 / 4 : ℝ) *
          ‖g s y + profileOp 1 (pairTensor V (neumannIterate g V n)) s y‖ ≤ 2 * G
        have hVu : WeightedBound (pairTensor V (neumannIterate g V n)) (3 / 4) (ε * (2 * G)) := by
          have h := hTW V _ 0 (3 / 4) ε (2 * G) le_rfl (by norm_num) hVw0 hw
          rwa [zero_add] at h
        have h1 := hgw s y
        have h2 := hT1 _ _ hVu s y
        have h3 : K1 * (ε * (2 * G)) ≤ G := by
          have := mul_le_mul_of_nonneg_right hK1ε (by linarith : (0 : ℝ) ≤ 2 * G)
          linarith
        have h4 : 0 ≤ (1 + ‖y‖) ^ (3 / 4 : ℝ) := by positivity
        calc _ ≤ (1 + ‖y‖) ^ (3 / 4 : ℝ) * ‖g s y‖ + (1 + ‖y‖) ^ (3 / 4 : ℝ) *
              ‖profileOp 1 (pairTensor V (neumannIterate g V n)) s y‖ := by
              rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) h4
          _ ≤ G + K1 * (ε * (2 * G)) := add_le_add h1 h2
          _ ≤ 2 * G := by linarith
      · have hkey : W s y - neumannIterate g V (n + 1) s y =
            profileOp 1 (pairTensor V (W - neumannIterate g V n)) s y := by
          show W s y - (g s y + profileOp 1 (pairTensor V (neumannIterate g V n)) s y) = _
          rw [hWeq s y, hT s y]; abel
        rw [hkey]
        have hVd0 : WeightedBound (pairTensor V (W - neumannIterate g V n)) 0
            (ε * (C * (1 / 2) ^ n)) := by
          have h := hTW V _ 0 0 ε (C * (1 / 2) ^ n) le_rfl le_rfl hVw0
            ((weightedBound_zero_iff _ _).2 hd)
          rwa [add_zero] at h
        have h5 := (weightedBound_zero_iff _ _).1 (hT0 _ _ hVd0) s y
        have h6 : 0 ≤ C * (1 / 2 : ℝ) ^ n := mul_nonneg hC0 (by positivity)
        calc _ ≤ K0 * (ε * (C * (1 / 2) ^ n)) := h5
          _ = (K0 * ε) * (C * (1 / 2) ^ n) := by ring
          _ ≤ (1 / 2) * (C * (1 / 2) ^ n) := mul_le_mul_of_nonneg_right hK0ε h6
          _ = C * (1 / 2) ^ (n + 1) := by ring
  refine ⟨2 * G, fun s y => ?_⟩
  have hlim : Tendsto (fun n : ℕ => 2 * G + (1 + ‖y‖) ^ (3 / 4 : ℝ) * (C * (1 / 2 : ℝ) ^ n)) atTop
      (𝓝 (2 * G + (1 + ‖y‖) ^ (3 / 4 : ℝ) * (C * 0))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))))
  rw [mul_zero, mul_zero, add_zero] at hlim
  refine ge_of_tendsto' hlim (fun n => ?_)
  obtain ⟨-, hu, hd⟩ := hind n
  have h4 : 0 ≤ (1 + ‖y‖) ^ (3 / 4 : ℝ) := by positivity
  have h7 : ‖W s y‖ ≤ ‖neumannIterate g V n s y‖ + ‖W s y - neumannIterate g V n s y‖ := by
    simpa using norm_add_le (neumannIterate g V n s y) (W s y - neumannIterate g V n s y)
  calc (1 + ‖y‖) ^ (3 / 4 : ℝ) * ‖W s y‖
      ≤ (1 + ‖y‖) ^ (3 / 4 : ℝ) * ‖neumannIterate g V n s y‖ +
          (1 + ‖y‖) ^ (3 / 4 : ℝ) * ‖W s y - neumannIterate g V n s y‖ := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left h7 h4
    _ ≤ 2 * G + (1 + ‖y‖) ^ (3 / 4 : ℝ) * (C * (1 / 2) ^ n) :=
        add_le_add (hu s y) (mul_le_mul_of_nonneg_left (hd s y) h4)

end Breakdown.FarField
