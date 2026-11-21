import TorusEuler.LocalizedAmplitudeComparison
import TorusEuler.Paper.Proofs.S53.Library.Leaves

/-!
# S53 library: Lemma 5.3 chain: private helpers of the label-Lipschitz and wave-phase jet bounds

Generated copy (script `s53tools/mkcopy.py`) of the declarations phaseJetBound_scaledPhaseOnly, phaseJetBound_smul_localized, norm_label_difference_le_of_first_jet of
`TorusEuler/LocalizedAmplitudeComparison.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section


open ContinuousLinearMap Set MeasureTheory
open scoped ContDiff InnerProductSpace
open NormedSpace (normalize)

namespace TorusEuler.Paper.Lib.S53

open TorusEuler
section LocalizedDuhamel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end LocalizedDuhamel

section NearLabelContraction

variable {E : Type} [NormedAddCommGroup E]

variable [InnerProductSpace ℝ E]

end NearLabelContraction

section FixedTransverse

variable {E S : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

end FixedTransverse

open NormedSpace (normalize)
open MovingWaveVector

namespace MovingWaveVector.PhysicalAmplification

open MovingWaveVector.PhysicalAmplification
end MovingWaveVector.PhysicalAmplification

/-- Copy of the private library lemma `phaseJetBound_scaledPhaseOnly`, made public in `Paper.Lib.S53` (glue). -/
theorem phaseJetBound_scaledPhaseOnly {f : ℝ → ℝ} {n : ℕ} {h C : ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : 0 < h)
    (hderiv : ∀ j ≤ n, ∀ s, h ^ j * ‖iteratedDeriv j f s‖ ≤ C) :
    PhaseJetBound n C (fun p : Vec3 × ℝ => f (h * p.2)) := by
  let L : (Vec3 × ℝ) →L[ℝ] ℝ := h • ContinuousLinearMap.snd ℝ Vec3 ℝ
  have hL : ‖L‖ ≤ h := by
    rw [show L = h • ContinuousLinearMap.snd ℝ Vec3 ℝ from rfl, norm_smul,
      Real.norm_of_nonneg hh.le]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ Vec3 ℝ) hh.le)
  intro j hj p
  change ‖iteratedFDeriv ℝ j (f ∘ L) p‖ ≤ C
  rw [L.iteratedFDeriv_comp_right hf p (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L p)‖ * ‖L‖ ^ j := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ j f (L p))
          (fun _ => L)
    _ ≤ ‖iteratedFDeriv ℝ j f (L p)‖ * h ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL j) (norm_nonneg _)
    _ ≤ C := by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, mul_comm]; exact hderiv j hj _

/-- Copy of the private library lemma `phaseJetBound_smul_localized`, made public in `Paper.Lib.S53` (glue). -/
theorem phaseJetBound_smul_localized {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ} {g : E → F} {n : ℕ} {A B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hfB : PhaseJetBound n A f) (hgB : PhaseJetBound n B g) :
    PhaseJetBound n ((2 : ℝ) ^ n * A * B) (fun x => f x • g x) := by
  intro j hj x
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      norm_iteratedFDeriv_smul_le hf hg x (by simp)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfB i (hij.trans hj) x) (Nat.cast_nonneg _))
        (hgB (j - i) ((Nat.sub_le j i).trans hj) x) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ j * A * B := by
      have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ)^j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB

/-- Copy of the private library lemma `norm_label_difference_le_of_first_jet`, made public in `Paper.Lib.S53` (glue). -/
theorem norm_label_difference_le_of_first_jet
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Vec3 → V} {C : ℝ}
    (hf : Differentiable ℝ f) (hC : ∀ a, ‖iteratedFDeriv ℝ 1 f a‖ ≤ C) (a b : Vec3) :
    ‖f a - f b‖ ≤ C * ‖a - b‖ :=
  (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hf x) (fun x _ => by simpa only [norm_iteratedFDeriv_one] using hC x)
    (mem_univ b) (mem_univ a)

end TorusEuler.Paper.Lib.S53

namespace TorusEuler.Paper.Lib.S53.LocalizedAmplitude

open TorusEuler.LocalizedAmplitude
end TorusEuler.Paper.Lib.S53.LocalizedAmplitude

