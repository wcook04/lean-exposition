import Breakdown.CertCell.CertificateStatements

open Matrix Breakdown.CellCert.Finite

noncomputable section

namespace Breakdown.CertCell.Certificate

private theorem quad_add_forms {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (M + N) x = quadValue M x + quadValue N x := by
  simp [quadValue, Matrix.add_mulVec, dotProduct_add]

private theorem quad_sub_forms {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (M - N) x = quadValue M x - quadValue N x := by
  simp [quadValue, Matrix.sub_mulVec, dotProduct_sub]

private theorem quad_finset_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (M : κ → Matrix ι ι ℝ)
    (x : ι → ℝ) : quadValue (∑ k ∈ s, M k) x = ∑ k ∈ s, quadValue (M k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadValue]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, quad_add_forms, ih]

private theorem quad_diagonal_form {ι : Type*} [Fintype ι] [DecidableEq ι] (d x : ι → ℝ) :
    quadValue (diagonal d) x = ∑ j, d j * x j ^ 2 := by
  simp only [quadValue, mulVec_diagonal, dotProduct]
  exact Finset.sum_congr rfl (fun j _ => by ring)

private theorem quad_outer_form {ι : Type*} [Fintype ι] (c x : ι → ℝ) :
    quadValue (vecMulVec c c) x = (c ⬝ᵥ x) ^ 2 := by
  simp only [quadValue, mulVec, vecMulVec, dotProduct, of_apply, sq, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem signedTreeLowerBound : SignedTreeLowerBound := by
  intro A B _ _ T hT x
  classical
  let _ := T.leafFintype
  let _ := T.nodeFintype
  let _ := T.columnFintype
  set f : T.Node → ℝ := fun μ => quadValue (T.front μ) x with hf
  set g : T.Leaf → ℝ := fun l => quadValue (T.leafForm l) x with hg
  have hsum : ∑ ν, (f ν + T.pivotGain ν x - T.columnLoss ν x) ≤ ∑ ν, quadValue (T.nodeInput ν) x :=
    Finset.sum_le_sum (fun ν _ => hT.node_bound ν x)
  have hin : ∀ ν, quadValue (T.nodeInput ν) x =
      (∑ l, if T.leafNode l = ν then g l else 0) + ∑ μ, if T.parent μ = some ν then f μ else 0 := by
    intro ν
    unfold SignedTree.nodeInput
    rw [quad_add_forms, quad_finset_sum, quad_finset_sum, Finset.sum_filter, Finset.sum_filter]
  have hleaves : ∑ ν, (∑ l, if T.leafNode l = ν then g l else 0) = ∑ l, g l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp
  have hkids : ∑ ν, (∑ μ, if T.parent μ = some ν then f μ else 0) = ∑ μ, f μ - f T.root := by
    rw [Finset.sum_comm]
    have h1 : ∀ μ ∈ (Finset.univ : Finset T.Node),
        (∑ ν, if T.parent μ = some ν then f μ else 0) = f μ - if μ = T.root then f μ else 0 := by
      intro μ _
      by_cases hne : μ = T.root
      · subst hne
        simp [hT.root_parent]
      · obtain ⟨ν0, hν0⟩ : ∃ ν0, T.parent μ = some ν0 := by
          cases h : T.parent μ with
          | none => exact absurd (hT.only_root μ h) hne
          | some ν0 => exact ⟨ν0, rfl⟩
        rw [hν0]
        simp [hne]
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
    simp
  have htot : quadValue T.totalForm x = ∑ l, g l := by
    unfold SignedTree.totalForm
    rw [quad_finset_sum]
  have hgain : ∀ ν, quadValue (diagonal (fun j => if j ∈ T.pivots ν then T.slack ν j else 0)) x
      = T.pivotGain ν x := by
    intro ν
    rw [quad_diagonal_form]
    unfold SignedTree.pivotGain
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hloss : ∑ c, quadValue (vecMulVec (T.column c) (T.column c)) x = ∑ ν, T.columnLoss ν x := by
    unfold SignedTree.columnLoss
    simp only [quad_outer_form]
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun c => {T.columnNode c})]
    · simp
    · intro c ν
      simp [eq_comm]
  have hroot : quadValue T.rootForm x = f T.root + ∑ ν, T.pivotGain ν x - ∑ ν, T.columnLoss ν x := by
    unfold SignedTree.rootForm
    rw [quad_sub_forms, quad_add_forms, quad_finset_sum, quad_finset_sum, ← hloss]
    simp only [hgain, hf]
  rw [Finset.sum_congr rfl (fun ν _ => hin ν), Finset.sum_add_distrib, hleaves, hkids,
    Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [hroot, htot]
  linarith
