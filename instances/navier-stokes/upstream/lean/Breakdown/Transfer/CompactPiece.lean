import Breakdown.Transfer.StatementsLocal

open Set

noncomputable section

namespace Breakdown

namespace CompactPieceInternal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem dense_span_smul {T : ℝ} {S : Set X} (hS : Dense S) :
    Dense ((Submodule.span ℝ {f : Piece X T | ∃ (φ : C(Icc (0 : ℝ) T, ℝ)) (y : X),
      y ∈ S ∧ ∀ t, f t = φ t • y}) : Set (Piece X T)) := by
  rw [Metric.dense_iff]
  intro g ε hε
  set e := ε / 3 with he
  have he0 : 0 < e := by positivity
  let U : Icc (0 : ℝ) T → Set (Icc (0 : ℝ) T) := fun x => g ⁻¹' Metric.ball (g x) e
  have hUo : ∀ x, IsOpen (U x) := fun x => Metric.isOpen_ball.preimage g.continuous
  have hUc : (univ : Set (Icc (0 : ℝ) T)) ⊆ ⋃ x, U x := fun z _ =>
    mem_iUnion.2 ⟨z, by simp [U, Metric.mem_ball, he0]⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  let V : F → Set (Icc (0 : ℝ) T) := fun i => U i
  have hVc : (univ : Set (Icc (0 : ℝ) T)) ⊆ ⋃ i, V i := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (hF hz)
    exact mem_iUnion.2 ⟨⟨x, hx⟩, hzx⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ V (fun i => hUo i) hVc
  have hy : ∀ i : F, ∃ y ∈ S, dist (g i) y < e := fun i => hS.exists_dist_lt _ he0
  choose y hyS hyd using hy
  let a : F → Piece X T := fun i => ⟨fun z => ρ i z • y i, (ρ i).continuous.smul continuous_const⟩
  refine ⟨∑ i, a i, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hle : ‖∑ i, a i - g‖ ≤ 2 * e := by
      rw [ContinuousMap.norm_le _ (by positivity)]
      intro z
      have hsum : ∑ i, ρ i z = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact ρ.sum_eq_one (mem_univ z)
      have hexp : (∑ i, a i - g) z = ∑ i, ρ i z • (y i - g z) := by
        rw [ContinuousMap.sub_apply, ContinuousMap.sum_apply]
        change ∑ i, ρ i z • y i - g z = _
        rw [Finset.sum_congr rfl fun i _ => smul_sub (ρ i z) (y i) (g z), Finset.sum_sub_distrib,
          ← Finset.sum_smul, hsum, one_smul]
      rw [hexp]
      calc ‖∑ i, ρ i z • (y i - g z)‖ ≤ ∑ i, ‖ρ i z • (y i - g z)‖ := norm_sum_le _ _
        _ ≤ ∑ i, ρ i z * (2 * e) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg i z)]
          by_cases h0 : ρ i z = 0
          · simp [h0]
          · refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg i z)
            have hz : z ∈ V i := hρ i (subset_tsupport _ (Function.mem_support.2 h0))
            have hz' : dist (g z) (g i) < e := hz
            rw [← dist_eq_norm]
            have h2 := dist_triangle (y i) (g i) (g z)
            have h3 := dist_comm (y i) (g i)
            have h4 := dist_comm (g i) (g z)
            linarith [hyd i]
        _ = 2 * e := by rw [← Finset.sum_mul, hsum, one_mul]
    linarith
  · exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨ρ i, y i, hyS i, fun t => rfl⟩

end CompactPieceInternal

theorem compactPiece_of (h1 : CompactSimpleStatement) : CompactPieceStatement := by
  intro X _ _ _ H T hT hT1 hK f
  obtain ⟨S, hSd, hSK⟩ := hK
  let C : Submodule ℝ (Piece X T) :=
    { carrier := {f | IsCompactOperator ((pieceEnd T).comp (H.pieceBil T f))}
      add_mem' := by
        intro a b ha hb
        simp only [mem_ofPred_eq, map_add, ContinuousLinearMap.comp_add] at ha hb ⊢
        exact ha.add hb
      zero_mem' := by
        simp only [mem_ofPred_eq, map_zero, ContinuousLinearMap.comp_zero]
        exact isCompactOperator_zero
      smul_mem' := by
        intro c a ha
        simp only [mem_ofPred_eq, map_smul, ContinuousLinearMap.comp_smul] at ha ⊢
        exact ha.smul c }
  have hcont : Continuous fun g : Piece X T => (pieceEnd T).comp (H.pieceBil T g) :=
    continuous_const.clm_comp (H.pieceBil T).continuous
  have hCc : IsClosed (C : Set (Piece X T)) :=
    (isClosed_setOfPred_isCompactOperator (σ₁₂ := RingHom.id ℝ) (M₁ := Piece X T)
      (M₂ := X)).preimage hcont
  have hspan : Submodule.span ℝ {g : Piece X T | ∃ (φ : C(Icc (0 : ℝ) T, ℝ)) (y : X),
      y ∈ S ∧ ∀ t, g t = φ t • y} ≤ C := by
    rw [Submodule.span_le]
    rintro g ⟨φ, y, hy, hg⟩
    exact h1 X H T y φ g hT hT1 (hSK y hy) hg
  exact closure_minimal hspan hCc (CompactPieceInternal.dense_span_smul hSd f)

end Breakdown
