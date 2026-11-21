import Mathlib

noncomputable section

namespace Breakdown.Spectral

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

private theorem exists_far_in_span {x : ℕ → Y} (hx : LinearIndependent ℂ x) (n : ℕ) :
    ∃ v : Y, v ∈ Submodule.span ℂ (x '' Set.Iic n) ∧ ‖v‖ ≤ 1 ∧
      ∀ w ∈ Submodule.span ℂ (x '' Set.Iio n), 1 / 2 ≤ ‖v - w‖ := by
  set V := Submodule.span ℂ (x '' Set.Iic n)
  set W := Submodule.span ℂ (x '' Set.Iio n)
  have : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ ((Set.finite_Iic n).image x)
  let F : Submodule ℂ V := W.comap V.subtype
  have hFc : IsClosed (F : Set V) := Submodule.closed_of_finiteDimensional F
  have hxV : x n ∈ V := Submodule.subset_span ⟨n, Set.mem_Iic.2 le_rfl, rfl⟩
  have hF : ∃ z : V, z ∉ F := ⟨⟨x n, hxV⟩, hx.notMem_span_image (by simp)⟩
  obtain ⟨z, -, hz1, hz⟩ := riesz_lemma_of_lt_one hFc hF (r := 1 / 2) (by norm_num)
  refine ⟨z, z.2, ?_, fun w hw => ?_⟩
  · exact le_of_eq hz1
  · have hwV : w ∈ V := Submodule.span_mono (Set.image_mono Set.Iio_subset_Iic_self) hw
    have h := hz ⟨w, hwV⟩ hw
    exact h

theorem exists_separated_of_eigen (S : Y →L[ℂ] Y) (μ : ℕ → ℂ) (hμ : Function.Injective μ)
    (hE : ∀ n, Module.End.HasEigenvalue (S : Module.End ℂ Y) (μ n)) :
    ∃ y : ℕ → Y, (∀ n, ‖y n‖ ≤ 1) ∧ ∀ m n, m < n → ‖μ n‖ / 2 ≤ ‖S (y n) - S (y m)‖ := by
  choose x hx using fun n => (hE n).exists_hasEigenvector
  have hSx : ∀ k, S (x k) = μ k • x k := fun k => (hx k).apply_eq_smul
  have hli : LinearIndependent ℂ x :=
    Module.End.eigenvectors_linearIndependent' (S : Module.End ℂ Y) μ hμ x hx
  choose y hyV hy1 hyW using exists_far_in_span hli
  refine ⟨y, hy1, fun m n hmn => ?_⟩
  have hVW : Submodule.span ℂ (x '' Set.Iic m) ≤ Submodule.span ℂ (x '' Set.Iio n) :=
    Submodule.span_mono (Set.image_mono fun k hk => lt_of_le_of_lt (Set.mem_Iic.1 hk) hmn)
  have hSV : ∀ p : ℕ, Submodule.span ℂ (x '' Set.Iic p) ≤
      (Submodule.span ℂ (x '' Set.Iic p)).comap (S : Y →ₗ[ℂ] Y) := by
    intro p
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, hSx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  have hDW : Submodule.span ℂ (x '' Set.Iic n) ≤
      (Submodule.span ℂ (x '' Set.Iio n)).comap ((S - μ n • (1 : Y →L[ℂ] Y) : Y →L[ℂ] Y) : Y →ₗ[ℂ] Y) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
    have e : (S - μ n • (1 : Y →L[ℂ] Y)) (x k) = (μ k - μ n) • x k := by
      simp [hSx, sub_smul]
    rw [e]
    rcases lt_or_eq_of_le (Set.mem_Iic.1 hk) with h | h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, h, rfl⟩)
    · subst h; simp
  set w : Y := S (y m) - (S (y n) - μ n • y n) with hw
  have hwW : w ∈ Submodule.span ℂ (x '' Set.Iio n) := by
    refine Submodule.sub_mem _ (hVW (hSV m (hyV m))) ?_
    have h := hDW (hyV n)
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe] at h
    have e : (S - μ n • (1 : Y →L[ℂ] Y)) (y n) = S (y n) - μ n • y n := by
      simp
    rwa [e] at h
  have key : S (y n) - S (y m) = μ n • y n - w := by
    rw [hw]; abel
  rw [key]
  rcases eq_or_ne (μ n) 0 with h0 | h0
  · simp [h0]
  · have e2 : μ n • y n - w = μ n • (y n - (μ n)⁻¹ • w) := by
      rw [smul_sub, smul_inv_smul₀ h0]
    rw [e2, norm_smul]
    have := hyW n _ (Submodule.smul_mem _ (μ n)⁻¹ hwW)
    nlinarith [norm_nonneg (μ n)]

theorem not_separated_of_compact (A C : Y →L[ℂ] Y) {a c : ℝ} (hA : ‖A‖ ≤ a)
    (hC : IsCompactOperator C) (hac : 2 * a < c) (y : ℕ → Y) (hy : ∀ n, ‖y n‖ ≤ 1)
    (hsep : ∀ m n, m < n → c ≤ ‖(A + C) (y n) - (A + C) (y m)‖) : False := by
  obtain ⟨K, hK, hK'⟩ := hC.image_closedBall_subset_compact 1
  obtain ⟨z, -, ψ, hψ, hψz⟩ :=
    hK.tendsto_subseq (x := fun n => C (y n)) (fun n => hK' ⟨y n, by simpa using hy n, rfl⟩)
  have hcs := hψz.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcs
  obtain ⟨N, hN⟩ := hcs (c - 2 * a) (by linarith)
  have h1 : ‖C (y (ψ (N + 1))) - C (y (ψ N))‖ < c - 2 * a := by
    simpa [dist_eq_norm] using hN (N + 1) (by omega)
  have h2 := hsep _ _ (hψ (Nat.lt_succ_self N))
  have hbd : ∀ v : Y, ‖v‖ ≤ 1 → ‖A v‖ ≤ a := by
    intro v hv
    have ha : 0 ≤ a := le_trans (norm_nonneg _) hA
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ a * 1 := mul_le_mul hA hv (norm_nonneg _) ha
      _ = a := mul_one a
  have hA2 : ‖A (y (ψ (N + 1))) - A (y (ψ N))‖ ≤ 2 * a := by
    calc _ ≤ ‖A (y (ψ (N + 1)))‖ + ‖A (y (ψ N))‖ := norm_sub_le _ _
      _ ≤ a + a := add_le_add (hbd _ (hy _)) (hbd _ (hy _))
      _ = 2 * a := by ring
  have e : (A + C) (y (ψ (N + 1))) - (A + C) (y (ψ N)) =
      (A (y (ψ (N + 1))) - A (y (ψ N))) + (C (y (ψ (N + 1))) - C (y (ψ N))) := by
    show A _ + C _ - (A _ + C _) = _
    abel
  rw [e] at h2
  have := norm_add_le (A (y (ψ (N + 1))) - A (y (ψ N))) (C (y (ψ (N + 1))) - C (y (ψ N)))
  linarith

end Breakdown.Spectral
