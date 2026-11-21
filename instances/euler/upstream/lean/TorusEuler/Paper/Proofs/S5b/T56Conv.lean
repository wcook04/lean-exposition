import TorusEuler.Paper.Proofs.S5b.T56Exact

/-!
# Theorem 5.6, glue: independence of the level constants of the depth

The constants `hierarchyLevelConstant P K p` of the level induction depend on the depth `P` only
through the numbers of pairs at levels `≤ p`, which do not depend on `P ≥ p`. This gives the
constants `C_{n,p}` of (5.34)-(5.36) independent of `P` ("the number of products in a level and
the constants of the lower levels at higher orders enter `C_{n,p}`", TeX :635-636).
-/

namespace TorusEuler.Paper.S5b

/-- The pairs at level `p ≤ P'` do not depend on the depth `P ≥ P'` (`shift ≤ 1`). -/
theorem levelPairs_indep {P P' shift p : ℕ} (hs : shift ≤ 1) (hp : p ≤ P') (hPP : P' ≤ P) :
    hierarchyLevelPairs P shift p = hierarchyLevelPairs P' shift p := by
  ext ⟨i, j⟩
  have hprod : ∀ (s t : Finset ℕ) (x : ℕ × ℕ), x ∈ s.product t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
    fun _ _ _ => Finset.mem_product
  unfold hierarchyLevelPairs
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [hierarchyAdvectionPairs, hprod, Finset.mem_Icc,
    hierarchyAdvectionLevel]
  constructor <;> intro h <;> omega

/-- The level constants do not depend on the depth `P ≥ P'` at levels `≤ P'`. -/
theorem levelConstant_indep {P P' : ℕ} (K : ℝ) (hPP : P' ≤ P) :
    ∀ q, q ≤ P' → hierarchyLevelConstant P K q = hierarchyLevelConstant P' K q := by
  intro q
  induction q with
  | zero => intro _; rfl
  | succ q ih =>
    intro hq
    have h0 := levelPairs_indep (P := P) (shift := 0) (p := q + 1) (by norm_num) hq hPP
    have h1 := levelPairs_indep (P := P) (shift := 1) (p := q + 1) (by norm_num) hq hPP
    change hierarchyStepCap P (q + 1) K (hierarchyLevelConstant P K q) =
      hierarchyStepCap P' (q + 1) K (hierarchyLevelConstant P' K q)
    rw [ih (by omega)]
    unfold hierarchyStepCap
    rw [h0, h1]

end TorusEuler.Paper.S5b
