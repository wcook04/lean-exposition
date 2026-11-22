module

public import QuarticQuery.Upper.Sampler

/-!
# A common finite workspace for a finite family of coherent samplers

Compiled as part of the `QuarticQuery` library target.

The pairwise existential workspaces in `Samples` can be replaced by one finite
workspace, one initial basis state, and one output map. A query-free basis
permutation selects the desired summand before the direct-sum circuit runs.
The logical read count is unchanged. This supplies the workspace interface
needed to instantiate the tensor preparation of equation (15).
-/

@[expose] public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper

/-- Ledger: eq-15. A finite nonempty family of coherent samplers with a common
read count has a common finite workspace, origin, and output map. The circuit
family and all workspace choices are fixed before the oracle input. The basis
permutation preparing each summand is input-independent and costs no reads.
-/
theorem quantumWorkspace_uniformize {ι J β : Type} [Fintype J] [Nonempty J]
    {c : ℕ} {L : J → BitInput ι → β → ℝ}
    (h : ∀ j, Samples c (L j)) :
    ∃ (Z : Type) (_ : Fintype Z) (o : Z) (out : Z → β)
      (F : J → BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z),
      (∀ j, IsCirc c (F j)) ∧
      ∀ j x b, lawOf (F j x (rket o)) out b = L j x b := by
  classical
  choose Zj instZj oj outj Fj hFj hLj using h
  let _ := instZj
  let Z := Σ j, Zj j
  let j₀ : J := Classical.choice inferInstance
  let o : Z := ⟨j₀, oj j₀⟩
  let out : Z → β := fun z => outj z.1 z.2
  let T : BitInput ι → Reg Z ≃ₗᵢ[ℂ] Reg Z :=
    fun x => sigmaOp fun j => Fj j x
  have hT : IsCirc c T := IsCirc.sigma hFj
  let P : J → Reg Z ≃ₗᵢ[ℂ] Reg Z :=
    fun j => regCongr (Equiv.swap o (⟨j, oj j⟩ : Z))
  have hblock : ∀ j x b,
      lawOf (T x (rket (⟨j, oj j⟩ : Z))) out b = L j x b := by
    intro j x b
    rw [lawOf_sigma, hLj, Finset.sum_eq_single j]
    · simp only [T, out]
      rw [slice_sigmaOp, slice_rket_same]
    · intro j' _ hj'
      simp only [T, out]
      rw [slice_sigmaOp, slice_rket_ne hj', map_zero]
      simp [lawOf]
    · simp
  refine ⟨Z, inferInstance, o, out, fun j x => (P j).trans (T x), ?_, ?_⟩
  · intro j
    exact ((IsCirc.gate (P j)).comp hT).cast (by omega)
  · intro j x b
    simp only [LinearIsometryEquiv.trans_apply, P, regCongr_rket,
      Equiv.swap_apply_left]
    exact hblock j x b

end QuarticQuery.Paper
