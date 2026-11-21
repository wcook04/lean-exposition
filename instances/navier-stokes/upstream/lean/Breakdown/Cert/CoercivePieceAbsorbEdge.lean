import Breakdown.Cert.CoerciveNodes

open scoped ENNReal

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceAbsorb

def IsGoodPoint (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : Prop :=
  Summable (fun ι => secondDerivAmp H ι σ y ^ 2) ∧ Summable (fun ι => vortGradAmp H ι σ y ^ 2) ∧
    Summable (fun ι => gradAmp G ι σ y ^ 2) ∧ Summable (fun ι => vortAmp G ι σ y ^ 2) ∧
    Summable (fun ι => velAmp v ι σ y ^ 2)

theorem absorb_le {c A B p q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : c ^ 2 ≤ 4 * A * B) :
    c * p * q ≤ A * p ^ 2 + B * q ^ 2 := by
  rcases hA.eq_or_lt with h | h
  · subst h
    have hc0 : c = 0 := by nlinarith [sq_nonneg c]
    subst hc0
    nlinarith [sq_nonneg q]
  · nlinarith [sq_nonneg (2 * A * p - c * q), mul_nonneg (sub_nonneg.2 hc) (sq_nonneg q), mul_pos h h]

theorem ind_nonneg (p : Prop) : 0 ≤ ModeWeights.ind p := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem ind_le_one (p : Prop) : ModeWeights.ind p ≤ 1 := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem summable_bdd_mul {f p : ℤ × ℤ → ℝ} {K : ℝ} (hf : ∀ ι, |f ι| ≤ K) (hp : Summable fun ι => p ι ^ 2) :
    Summable fun ι => f ι * p ι ^ 2 := by
  refine Summable.of_norm_bounded (g := fun ι => K * p ι ^ 2) (hp.mul_left K) fun ι => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (p ι))]
  exact mul_le_mul_of_nonneg_right (hf ι) (sq_nonneg _)

open Classical in
theorem abs_inward_le (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (B : ℤ × ℤ → Space → ℝ) (ι : ℤ × ℤ) (y : Space) :
    |PieceWeights.inward h T B ι y| ≤ ∑ α ∈ h.harmonics, |B α y| := by
  have hb : ∀ κ : ℤ × ℤ, |PieceWeights.backSum h T B κ y| ≤ ∑ α ∈ h.harmonics, |B α y| := by
    intro κ
    unfold PieceWeights.backSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    split_ifs <;> simp
  unfold PieceWeights.inward
  split_ifs
  · exact hb ι
  · exact hb (-ι)
  · simpa using Finset.sum_nonneg fun α _ => abs_nonneg (B α y)

open Classical in
theorem abs_outward_le (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (B : ℤ × ℤ → Space → ℝ) (ι : ℤ × ℤ) (y : Space) :
    |PieceWeights.outward h T B ι y| ≤ 2 * ∑ α ∈ h.harmonics, |B α y| := by
  have hf : ∀ κ : ℤ × ℤ, |PieceWeights.fwdSum h T B κ y| ≤ ∑ α ∈ h.harmonics, |B α y| := by
    intro κ
    unfold PieceWeights.fwdSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    split_ifs <;> simp
  have h0 : 0 ≤ ∑ α ∈ h.harmonics, |B α y| := Finset.sum_nonneg fun α _ => abs_nonneg (B α y)
  unfold PieceWeights.outward
  refine (abs_add_le _ _).trans ?_
  have e1 : |(if ι ∈ T then 0 else PieceWeights.fwdSum h T B ι y)| ≤ ∑ α ∈ h.harmonics, |B α y| := by
    split_ifs
    · simpa using h0
    · exact hf ι
  have e2 : |(if -ι ∈ T then 0 else PieceWeights.fwdSum h T B (-ι) y)| ≤ ∑ α ∈ h.harmonics, |B α y| := by
    split_ifs
    · simpa using h0
    · exact hf (-ι)
  linarith

open Classical in
theorem edge_term_le {a b c' d : Prop} {x Bv pi q1 q2 c A Bc : ℝ} (hX : 0 ≤ x) (hXB : x ≤ Bv)
    (hA : 0 ≤ A) (hB : 0 ≤ Bc) (hc : c ^ 2 ≤ 4 * A * Bc) :
    c * pi * (if a then (if b then 0 else x * q1) else if c' then (if d then 0 else x * q2) else 0)
      ≤ ModeWeights.ind (a ∨ c') * A * (if a then (if b then 0 else Bv) else if c' then (if d then 0 else Bv) else 0)
          * pi ^ 2 + Bc * ((if a ∧ ¬ b then x * q1 ^ 2 else 0) + (if ¬ a ∧ c' ∧ ¬ d then x * q2 ^ 2 else 0)) := by
  have hA2 : 0 ≤ A * pi ^ 2 := mul_nonneg hA (sq_nonneg _)
  unfold ModeWeights.ind
  by_cases ha : a
  · by_cases hb : b
    · simp [ha, hb]
    · have k := absorb_le (p := pi) (q := q1) hA hB hc
      simp only [ha, hb, if_true, if_false, true_or, not_false_eq_true, and_self, not_true_eq_false,
        false_and, add_zero, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left k hX, mul_le_mul_of_nonneg_right hXB hA2]
  · by_cases hc' : c'
    · by_cases hd : d
      · simp [ha, hc', hd]
      · have k := absorb_le (p := pi) (q := q2) hA hB hc
        simp only [ha, hc', hd, if_true, if_false, or_true, not_false_eq_true, and_self, false_and, zero_add,
          one_mul, true_and]
        nlinarith [mul_le_mul_of_nonneg_left k hX, mul_le_mul_of_nonneg_right hXB hA2]
    · simp [ha, hc']

theorem abs_mul_le_half {c p q : ℝ} : |c * (p * q)| ≤ |c| * (p ^ 2 + q ^ 2) := by
  rw [abs_mul, abs_mul]
  have h1 : |p| * |q| ≤ p ^ 2 + q ^ 2 := by
    nlinarith [sq_nonneg (|p| - |q|), sq_abs p, sq_abs q, abs_nonneg p, abs_nonneg q]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

open Classical in
theorem edge_term_abs {a b c' d : Prop} {x pi q1 q2 c : ℝ} (hX : 0 ≤ x) :
    |c * pi * (if a then (if b then 0 else x * q1) else if c' then (if d then 0 else x * q2) else 0)|
      ≤ |c| * x * (pi ^ 2 + q1 ^ 2 + q2 ^ 2) := by
  have h0 : 0 ≤ |c| * x * (pi ^ 2 + q1 ^ 2 + q2 ^ 2) :=
    mul_nonneg (mul_nonneg (abs_nonneg c) hX) (by positivity)
  have k1 : |c * pi * (x * q1)| ≤ |c| * x * (pi ^ 2 + q1 ^ 2 + q2 ^ 2) := by
    have := abs_mul_le_half (c := c) (p := pi) (q := q1)
    rw [show c * pi * (x * q1) = x * (c * (pi * q1)) by ring, abs_mul, abs_of_nonneg hX]
    nlinarith [mul_le_mul_of_nonneg_left this hX, mul_nonneg (mul_nonneg (abs_nonneg c) hX) (sq_nonneg q2)]
  have k2 : |c * pi * (x * q2)| ≤ |c| * x * (pi ^ 2 + q1 ^ 2 + q2 ^ 2) := by
    have := abs_mul_le_half (c := c) (p := pi) (q := q2)
    rw [show c * pi * (x * q2) = x * (c * (pi * q2)) by ring, abs_mul, abs_of_nonneg hX]
    nlinarith [mul_le_mul_of_nonneg_left this hX, mul_nonneg (mul_nonneg (abs_nonneg c) hX) (sq_nonneg q1)]
  split_ifs <;> simp_all

open Classical in
theorem edgeSum_eq (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X q : ℤ × ℤ → ℝ) (ι : ℤ × ℤ) :
    edgeSum h T X q ι = ∑ α ∈ h.harmonics, (if ι ∈ T then (if ι - α ∈ T then 0 else X α * q (ι - α))
      else if -ι ∈ T then (if -ι - α ∈ T then 0 else X α * q (ι + α)) else 0) := by
  unfold edgeSum
  split_ifs <;> simp

open Classical in
theorem inward_eq (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (B : ℤ × ℤ → Space → ℝ) (ι : ℤ × ℤ) (y : Space) :
    PieceWeights.inward h T B ι y = ∑ α ∈ h.harmonics, (if ι ∈ T then (if ι - α ∈ T then 0 else B α y)
      else if -ι ∈ T then (if -ι - α ∈ T then 0 else B α y) else 0) := by
  unfold PieceWeights.inward PieceWeights.backSum
  split_ifs <;> simp

theorem ite_nonneg_of {p : Prop} [Decidable p] {a : ℝ} (ha : 0 ≤ a) : 0 ≤ (if p then a else 0) := by
  split_ifs <;> simp [ha]

theorem ite_le_of {p : Prop} [Decidable p] {a : ℝ} (ha : 0 ≤ a) : (if p then a else 0) ≤ a := by
  split_ifs <;> simp [ha]

theorem summable_shift_sub {q : ℤ × ℤ → ℝ} (hq : Summable fun ι => q ι ^ 2) (α : ℤ × ℤ) :
    Summable fun ι => q (ι - α) ^ 2 :=
  hq.comp_injective (sub_left_injective (b := α))

theorem summable_shift_add {q : ℤ × ℤ → ℝ} (hq : Summable fun ι => q ι ^ 2) (α : ℤ × ℤ) :
    Summable fun ι => q (ι + α) ^ 2 :=
  hq.comp_injective (add_left_injective α)

open Classical in
theorem reindex_le (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X : ℤ × ℤ → ℝ) (B : ℤ × ℤ → Space → ℝ) (y : Space)
    (hX0 : ∀ α ∈ h.harmonics, 0 ≤ X α) (hXB : ∀ α ∈ h.harmonics, X α ≤ B α y)
    (q : ℤ × ℤ → ℝ) (hq : Summable fun ι => q ι ^ 2) {Bc : ℝ} (hB : 0 ≤ Bc) :
    (Summable fun ι => ∑ α ∈ h.harmonics, Bc * ((if ι ∈ T ∧ ¬ ι - α ∈ T then X α * q (ι - α) ^ 2 else 0)
        + (if ¬ ι ∈ T ∧ -ι ∈ T ∧ ¬ -ι - α ∈ T then X α * q (ι + α) ^ 2 else 0))) ∧
    ∑' ι, ∑ α ∈ h.harmonics, Bc * ((if ι ∈ T ∧ ¬ ι - α ∈ T then X α * q (ι - α) ^ 2 else 0)
        + (if ¬ ι ∈ T ∧ -ι ∈ T ∧ ¬ -ι - α ∈ T then X α * q (ι + α) ^ 2 else 0))
      ≤ ∑' ι, Bc * PieceWeights.outward h T B ι y * q ι ^ 2 := by
  have hq1 := summable_shift_sub hq
  have hq2 := summable_shift_add hq
  have hB0 : ∀ α ∈ h.harmonics, 0 ≤ B α y := fun α hα => (hX0 α hα).trans (hXB α hα)
  have sg1 : ∀ α ∈ h.harmonics, Summable fun ι => (if ι ∈ T ∧ ¬ ι - α ∈ T then X α * q (ι - α) ^ 2 else 0) :=
    fun α hα => Summable.of_nonneg_of_le (fun _ => ite_nonneg_of (mul_nonneg (hX0 α hα) (sq_nonneg _)))
      (fun _ => ite_le_of (mul_nonneg (hX0 α hα) (sq_nonneg _))) ((hq1 α).mul_left (X α))
  have sg2 : ∀ α ∈ h.harmonics, Summable fun ι =>
      (if ¬ ι ∈ T ∧ -ι ∈ T ∧ ¬ -ι - α ∈ T then X α * q (ι + α) ^ 2 else 0) :=
    fun α hα => Summable.of_nonneg_of_le (fun _ => ite_nonneg_of (mul_nonneg (hX0 α hα) (sq_nonneg _)))
      (fun _ => ite_le_of (mul_nonneg (hX0 α hα) (sq_nonneg _))) ((hq2 α).mul_left (X α))
  have sA : ∀ α ∈ h.harmonics, Summable fun ι => Bc * ((if ι ∈ T ∧ ¬ ι - α ∈ T then X α * q (ι - α) ^ 2 else 0)
      + (if ¬ ι ∈ T ∧ -ι ∈ T ∧ ¬ -ι - α ∈ T then X α * q (ι + α) ^ 2 else 0)) :=
    fun α hα => ((sg1 α hα).add (sg2 α hα)).mul_left Bc
  refine ⟨summable_sum sA, ?_⟩
  have sa1 : ∀ α ∈ h.harmonics, Summable fun κ => (if ¬ κ ∈ T then (if κ + α ∈ T then B α y else 0) else 0)
      * q κ ^ 2 := fun α _ => summable_bdd_mul (K := |B α y|) (fun κ => by split_ifs <;> simp) hq
  have sa2 : ∀ α ∈ h.harmonics, Summable fun κ => (if ¬ -κ ∈ T then (if -κ + α ∈ T then B α y else 0) else 0)
      * q κ ^ 2 := fun α _ => summable_bdd_mul (K := |B α y|) (fun κ => by split_ifs <;> simp) hq
  have r1 : ∀ α ∈ h.harmonics, ∑' ι, (if ι ∈ T ∧ ¬ ι - α ∈ T then X α * q (ι - α) ^ 2 else 0)
      ≤ ∑' κ, (if ¬ κ ∈ T then (if κ + α ∈ T then B α y else 0) else 0) * q κ ^ 2 := by
    intro α hα
    have e := (Equiv.addRight α).tsum_eq (fun ι => if ι ∈ T ∧ ¬ ι - α ∈ T then X α * q (ι - α) ^ 2 else 0)
    simp only [Equiv.coe_addRight, add_sub_cancel_right] at e
    rw [← e]
    refine Summable.tsum_le_tsum (fun κ => ?_) ?_ (sa1 α hα)
    · have hXB' := hXB α hα
      have hq0 := sq_nonneg (q κ)
      by_cases h1 : κ ∈ T <;> by_cases h2 : κ + α ∈ T <;>
        simp only [h1, h2, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and,
          if_true, if_false, zero_mul, le_refl] <;>
        first | exact le_rfl | exact mul_le_mul_of_nonneg_right hXB' hq0 | exact mul_nonneg (hB0 α hα) hq0
    · have := (Equiv.addRight α).summable_iff.2 (sg1 α hα)
      simpa only [Function.comp_def, Equiv.coe_addRight, add_sub_cancel_right] using this
  have r2 : ∀ α ∈ h.harmonics, ∑' ι, (if ¬ ι ∈ T ∧ -ι ∈ T ∧ ¬ -ι - α ∈ T then X α * q (ι + α) ^ 2 else 0)
      ≤ ∑' κ, (if ¬ -κ ∈ T then (if -κ + α ∈ T then B α y else 0) else 0) * q κ ^ 2 := by
    intro α hα
    have e := (Equiv.subRight α).tsum_eq
      (fun ι => if ¬ ι ∈ T ∧ -ι ∈ T ∧ ¬ -ι - α ∈ T then X α * q (ι + α) ^ 2 else 0)
    simp only [Equiv.subRight_apply, sub_add_cancel, neg_sub, sub_sub_cancel_left] at e
    rw [← e]
    refine Summable.tsum_le_tsum (fun κ => ?_) ?_ (sa2 α hα)
    · have hXB' := hXB α hα
      have hq0 := sq_nonneg (q κ)
      have hk : α - κ = -κ + α := by abel
      simp only [hk]
      by_cases h1 : κ - α ∈ T <;> by_cases h2 : -κ + α ∈ T <;> by_cases h3 : -κ ∈ T <;>
        simp only [h1, h2, h3, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and, false_and,
          if_true, if_false, zero_mul, le_refl] <;>
        first | exact le_rfl | exact mul_le_mul_of_nonneg_right hXB' hq0 | exact mul_nonneg (hB0 α hα) hq0
    · have := (Equiv.subRight α).summable_iff.2 (sg2 α hα)
      simpa only [Function.comp_def, Equiv.subRight_apply, sub_add_cancel, neg_sub, sub_sub_cancel_left] using this
  have hout : ∀ κ, Bc * PieceWeights.outward h T B κ y * q κ ^ 2 = ∑ α ∈ h.harmonics, Bc *
      ((if ¬ κ ∈ T then (if κ + α ∈ T then B α y else 0) else 0) * q κ ^ 2
        + (if ¬ -κ ∈ T then (if -κ + α ∈ T then B α y else 0) else 0) * q κ ^ 2) := by
    intro κ
    unfold PieceWeights.outward PieceWeights.fwdSum
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    by_cases h1 : κ ∈ T <;> by_cases h2 : -κ ∈ T <;> simp [h1, h2] <;> ring
  rw [Summable.tsum_finsetSum sA]
  simp_rw [hout]
  rw [Summable.tsum_finsetSum fun α hα => ((sa1 α hα).add (sa2 α hα)).mul_left Bc]
  refine Finset.sum_le_sum fun α hα => ?_
  rw [(sg1 α hα).add (sg2 α hα) |>.tsum_mul_left, ((sa1 α hα).add (sa2 α hα)).tsum_mul_left,
    (sg1 α hα).tsum_add (sg2 α hα), (sa1 α hα).tsum_add (sa2 α hα)]
  exact mul_le_mul_of_nonneg_left (add_le_add (r1 α hα) (r2 α hα)) hB

open Classical in
theorem edge_le (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X : ℤ × ℤ → ℝ) (B : ℤ × ℤ → Space → ℝ) (y : Space)
    (hX0 : ∀ α ∈ h.harmonics, 0 ≤ X α) (hXB : ∀ α ∈ h.harmonics, X α ≤ B α y)
    (p q : ℤ × ℤ → ℝ) (hp : Summable fun ι => p ι ^ 2) (hq : Summable fun ι => q ι ^ 2)
    {c A Bc : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ Bc) (hc : c ^ 2 ≤ 4 * A * Bc) :
    Summable (fun ι => c * p ι * edgeSum h T X q ι) ∧
      ∑' ι, c * p ι * edgeSum h T X q ι ≤
        ∑' ι, ModeWeights.ind (PieceWeights.inPiece T ι) * A * PieceWeights.inward h T B ι y * p ι ^ 2
          + ∑' ι, Bc * PieceWeights.outward h T B ι y * q ι ^ 2 := by
  have hq1 : ∀ α : ℤ × ℤ, Summable fun ι => q (ι - α) ^ 2 := fun α =>
    summable_shift_sub hq α
  have hq2 : ∀ α : ℤ × ℤ, Summable fun ι => q (ι + α) ^ 2 := fun α =>
    summable_shift_add hq α
  have sL : Summable fun ι => c * p ι * edgeSum h T X q ι := by
    refine Summable.of_norm_bounded
      (g := fun ι => ∑ α ∈ h.harmonics, |c| * X α * (p ι ^ 2 + q (ι - α) ^ 2 + q (ι + α) ^ 2))
      (summable_sum fun α _ => (((hp.add (hq1 α)).add (hq2 α)).mul_left (|c| * X α))) fun ι => ?_
    rw [Real.norm_eq_abs, edgeSum_eq, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α hα => edge_term_abs (hX0 α hα))
  have sR1 : Summable fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * A * PieceWeights.inward h T B ι y
      * p ι ^ 2 := by
    refine summable_bdd_mul (K := A * ∑ α ∈ h.harmonics, |B α y|) (fun ι => ?_) hp
    rw [abs_mul, abs_mul, abs_of_nonneg (ind_nonneg _), abs_of_nonneg hA]
    have k1 := mul_le_mul_of_nonneg_left (abs_inward_le h T B ι y) hA
    have k2 := ind_le_one (PieceWeights.inPiece T ι)
    have k3 := ind_nonneg (PieceWeights.inPiece T ι)
    have k4 : 0 ≤ A * |PieceWeights.inward h T B ι y| := mul_nonneg hA (abs_nonneg _)
    nlinarith
  obtain ⟨sG, hG⟩ := reindex_le h T X B y hX0 hXB q hq hB
  have hpt : ∀ ι, c * p ι * edgeSum h T X q ι ≤
      ModeWeights.ind (PieceWeights.inPiece T ι) * A * PieceWeights.inward h T B ι y * p ι ^ 2
        + ∑ α ∈ h.harmonics, Bc * ((if ι ∈ T ∧ ¬ ι - α ∈ T then X α * q (ι - α) ^ 2 else 0)
          + (if ¬ ι ∈ T ∧ -ι ∈ T ∧ ¬ -ι - α ∈ T then X α * q (ι + α) ^ 2 else 0)) := by
    intro ι
    rw [edgeSum_eq, inward_eq, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun α hα => edge_term_le (hX0 α hα) (hXB α hα) hA hB hc
  refine ⟨sL, ?_⟩
  calc ∑' ι, c * p ι * edgeSum h T X q ι
      ≤ ∑' ι, (ModeWeights.ind (PieceWeights.inPiece T ι) * A * PieceWeights.inward h T B ι y * p ι ^ 2
        + ∑ α ∈ h.harmonics, Bc * ((if ι ∈ T ∧ ¬ ι - α ∈ T then X α * q (ι - α) ^ 2 else 0)
          + (if ¬ ι ∈ T ∧ -ι ∈ T ∧ ¬ -ι - α ∈ T then X α * q (ι + α) ^ 2 else 0))) :=
        Summable.tsum_le_tsum hpt sL (sR1.add sG)
    _ ≤ _ := by
        rw [sR1.tsum_add sG]
        linarith

theorem summable_inward_term (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (B : ℤ × ℤ → Space → ℝ) (y : Space)
    (A : ℝ) (p : ℤ × ℤ → ℝ) (hp : Summable fun ι => p ι ^ 2) :
    Summable fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * A * PieceWeights.inward h T B ι y * p ι ^ 2 := by
  refine summable_bdd_mul (K := |A| * ∑ α ∈ h.harmonics, |B α y|) (fun ι => ?_) hp
  rw [abs_mul, abs_mul, abs_of_nonneg (ind_nonneg _)]
  have k1 := mul_le_mul_of_nonneg_left (abs_inward_le h T B ι y) (abs_nonneg A)
  have k2 := ind_le_one (PieceWeights.inPiece T ι)
  have k3 := ind_nonneg (PieceWeights.inPiece T ι)
  have k4 : 0 ≤ |A| * |PieceWeights.inward h T B ι y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

theorem summable_outward_term (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (B : ℤ × ℤ → Space → ℝ) (y : Space)
    (Bc : ℝ) (q : ℤ × ℤ → ℝ) (hq : Summable fun ι => q ι ^ 2) :
    Summable fun ι => Bc * PieceWeights.outward h T B ι y * q ι ^ 2 := by
  refine summable_bdd_mul (K := |Bc| * (2 * ∑ α ∈ h.harmonics, |B α y|)) (fun ι => ?_) hq
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_outward_le h T B ι y) (abs_nonneg _)

theorem summable_ind_term (T : Set (ℤ × ℤ)) (p : ℤ × ℤ → ℝ) (hp : Summable fun ι => p ι ^ 2) :
    Summable fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * p ι ^ 2 :=
  summable_bdd_mul (K := 1) (fun ι => by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _) hp

theorem pieceNorm_sq (T : Set (ℤ × ℤ)) (g : ℤ × ℤ → ℝ) (_hg : Summable fun κ => g κ ^ 2) :
    pieceNorm T g ^ 2 = ∑' κ, ModeWeights.ind (PieceWeights.inPiece T κ) * g κ ^ 2 := by
  unfold pieceNorm
  exact Real.sq_sqrt (tsum_nonneg fun κ => mul_nonneg (ind_nonneg _) (sq_nonneg _))

theorem block_le (T : Set (ℤ × ℤ)) (p q : ℤ × ℤ → ℝ) (hp : Summable fun κ => p κ ^ 2)
    (hq : Summable fun κ => q κ ^ 2) {c A Bc : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ Bc) (hc : c ^ 2 ≤ 4 * A * Bc) :
    c * pieceNorm T p * pieceNorm T q ≤
      A * ∑' κ, ModeWeights.ind (PieceWeights.inPiece T κ) * p κ ^ 2
        + Bc * ∑' κ, ModeWeights.ind (PieceWeights.inPiece T κ) * q κ ^ 2 := by
  rw [← pieceNorm_sq T p hp, ← pieceNorm_sq T q hq]
  exact absorb_le hA hB hc

end Internal.PieceAbsorb

end Coercive

end Breakdown
