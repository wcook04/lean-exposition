import TorusEuler.Paper.Proofs.S5b.Lemma58A

/-!
# Lemma 5.8, second part: glue for the bounds (5.47), (5.48)

* `graph_norm_le_wNorm`: for a profile vanishing before `t₀`, the supremum of its graph is
  at most `‖g‖_{[0],γ}` on all of `[0,T]` when `γ ≤ 1` (`08_exact_wave.tex:125-127`: "since
  `γ ≤ 1`, the supremum of `W_osc^♮` is at most `‖W_osc‖_{[0],γ}`").
* `holder_zero`, `holder_smul`: the half-Hölder norms of `0` and of `c • f`.
* `holder_of_active`: a half-Hölder bound on `[t₀,T]` for the graph of a profile vanishing
  before `t₀` holds on `[0,T]`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile AppendixD

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The zero field has every half-Hölder norm zero. -/
theorem holder_zero (m : ℕ) :
    SpatialHolderHalf m (0 : Vec3 → E) ∧ spatialHolderHalfNorm m (0 : Vec3 → E) ≤ 0 := by
  have h := spatialHolderHalfNorm_le_of_uniformJets (g := (0 : Vec3 → E)) (m := m)
    contDiff_const le_rfl fun j _ x => by
      rw [show (0 : Vec3 → E) = fun _ => 0 from rfl, iteratedFDeriv_fun_zero]
      simp
  exact ⟨h.1, h.2.trans_eq (mul_zero _)⟩

/-- The half-Hölder norm is homogeneous: `‖c f‖_{C^{m,1/2}} = |c| ‖f‖_{C^{m,1/2}}`. -/
theorem holder_smul {m : ℕ} {f : Vec3 → E} (hf : SpatialHolderHalf m f) (c : ℝ) :
    SpatialHolderHalf m (c • f) ∧ spatialHolderHalfNorm m (c • f) = |c| * spatialHolderHalfNorm m f := by
  have hD (j : ℕ) (hj : j ≤ m) : iteratedFDeriv ℝ j (c • f) = c • iteratedFDeriv ℝ j f := by
    funext x
    exact iteratedFDeriv_const_smul_apply ((hf.1.of_le (by exact_mod_cast hj)).contDiffAt)
  have hS (j : ℕ) (hj : j ≤ m) :
      spatialSupNorm (iteratedFDeriv ℝ j (c • f)) = |c| * spatialSupNorm (iteratedFDeriv ℝ j f) := by
    rw [hD j hj]
    unfold spatialSupNorm
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    exact (Real.mul_iSup_of_nonneg (abs_nonneg c) _).symm
  have hQ (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j (c • f)) p =
        |c| * spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) p := by
    rw [hD j hj]
    simp only [spatialHolderHalfQuotient, Pi.smul_apply, ← smul_sub, norm_smul, Real.norm_eq_abs,
      mul_div_assoc]
  have hH (j : ℕ) (hj : j ≤ m) :
      spatialHolderHalfSeminorm (iteratedFDeriv ℝ j (c • f)) =
        |c| * spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) := by
    unfold spatialHolderHalfSeminorm
    simp only [hQ j hj]
    exact (Real.mul_iSup_of_nonneg (abs_nonneg c) _).symm
  refine ⟨⟨hf.1.const_smul c, fun j hj => ⟨?_, ?_⟩⟩, ?_⟩
  · obtain ⟨B, hB⟩ := (hf.2 j hj).1
    refine ⟨|c| * B, forall_mem_range.mpr fun x => ?_⟩
    rw [hD j hj, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB ⟨x, rfl⟩) (abs_nonneg c)
  · obtain ⟨B, hB⟩ := (hf.2 j hj).2
    refine ⟨|c| * B, forall_mem_range.mpr fun p => ?_⟩
    rw [hQ j hj]
    exact mul_le_mul_of_nonneg_left (hB ⟨p, rfl⟩) (abs_nonneg c)
  · unfold spatialHolderHalfNorm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [hS j hj', hH j hj', mul_add]

variable {T : ℝ} {k : Vec3}

/-- The graph of a profile vanishing before `t₀` vanishes before `t₀`. -/
theorem graphRead_eq_zero_before {Y : Velocity} {g : HierarchyTwistedProfile T k E} {t₀ : ℝ}
    (hg : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x s, g.val.val.val (t, x, s) = 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) (hpre : t < t₀) : graphRead Y g t = 0 := by
  funext x
  exact hg t ht hpre _ _

/-- **The supremum bound behind (5.47)**: for a profile vanishing before `t₀` and a
weight `0 < γ ≤ 1` on `[t₀,T]`, `|g^♮(t,x)| ≤ ‖g‖_{[0],γ}` on `[0,T]`
(`08_exact_wave.tex:125-127`). -/
theorem graph_norm_le_wNorm (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    {γ : ℝ → ℝ} (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγ1 : ∀ t ∈ Icc t₀ T, γ t ≤ 1) (ℓ h : ℝ) (Y : Velocity)
    {g : HierarchyTwistedProfile T k E}
    (hg : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x s, g.val.val.val (t, x, s) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    ‖graphRead Y g t x‖ ≤ S5.wNorm ℓ h t₀ γ 0 g := by
  have hfin := Bridge.fieldNormFinite_weighted hT ℓ h 0 ht₀ htT hγc hγ g
  have hN : 0 ≤ S5.wNorm ℓ h t₀ γ 0 g := fieldNorm_nonneg hfin
  by_cases hpre : t < t₀
  · rw [graphRead_eq_zero_before hg ht hpre]
    simpa using hN
  · have hact : t ∈ Icc t₀ T := ⟨le_of_not_gt hpre, ht.2⟩
    have h1 := norm_le_weight_mul_weightedFieldNorm (γ := Bridge.restrictWeight (Icc t₀ T) γ)
      (fun s => hγ s s.2) hfin ⟨t, hact⟩ (Y t x, ⟪k, Y t x⟫_ℝ)
    change ‖g.val.val.val (t, Y t x, ⟪k, Y t x⟫_ℝ)‖ ≤ _
    refine h1.trans ?_
    change γ t * S5.wNorm ℓ h t₀ γ 0 g ≤ _
    simpa using mul_le_mul_of_nonneg_right (hγ1 t hact) hN

/-- A half-Hölder bound for the graph of a profile vanishing before `t₀`, known on
`[t₀,T]`, holds on `[0,T]`. -/
theorem holder_of_active {Y : Velocity} {g : HierarchyTwistedProfile T k E} {t₀ : ℝ}
    (hg : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x s, g.val.val.val (t, x, s) = 0) {m : ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (hact : ∀ t ∈ Icc t₀ T, SpatialHolderHalf m (graphRead Y g t) ∧
      spatialHolderHalfNorm m (graphRead Y g t) ≤ B) :
    ∀ t ∈ Icc 0 T, SpatialHolderHalf m (graphRead Y g t) ∧
      spatialHolderHalfNorm m (graphRead Y g t) ≤ B := by
  intro t ht
  by_cases hpre : t < t₀
  · rw [graphRead_eq_zero_before hg ht hpre]
    exact ⟨(holder_zero m).1, (holder_zero m).2.trans hB⟩
  · exact hact t ⟨le_of_not_gt hpre, ht.2⟩

end

end TorusEuler.Paper.S5b
