import TorusEuler.Paper.SBD.Statements

/-! # Proof of Lemma D.3 (lifting of zero-order inverse bounds)

Conditional proof `Paper.Proof.lemma_D_3` of `Paper.Statement.lemma_D_3`
(`cc:uf:trunc:lem:lifting`, sections/appD_finite_norms.tex:133-188 of the latest
manuscript). Lemma D.3 is a leaf of the proof spine: its TeX proof cites no
other numbered result, so the Lean proof has no hypotheses. -/

namespace TorusEuler.Paper

/-- Proof of **Lemma D.3** (`cc:uf:trunc:lem:lifting`), following
sections/appD_finite_norms.tex:164-188. The TeX proof cites no numbered
result, so this leaf has no hypotheses.

* Differentiated equation (appD:165-173): for each nondecreasing word `w` of
  weighted derivatives, `ℒ(∂^w v) = ∂^w F − ∑_ν ∑_{0<β'≤β} T_ν(∂^{β'} c_ν ∂^{β-β'} v)`;
  this is the Leibniz recursion inside the library lemma
  `paperLemmaD3_lifting` (own content of D.3), driven by the commutation
  hypotheses `hComm`, `hProd`, `hFC` of the statement.
* Zero-order estimate applied to the differentiated data (appD:174) is the
  hypothesis `hInv` (with `hLow`), and the product bound for `T_ν` is `hB`.
* Assignment of `ℓ_*^i` to the coefficient (appD:175-177): the word bound
  `appendixSlowCoefficient_word_le` (own content of D.3) turns the hypothesis
  (D.7) `hSlow`, stated on the exact-order norm `ℓ_*^m |c_ν|_m`, into the
  per-word bound that the recursion needs, using that coefficient derivatives
  commute (`hAC`) and `b_ν ≥ 0` (`hb`).
* Induction from order zero (appD:178-185) is the induction in
  `paperLemmaD3_lifting`; it produces the explicit constant
  `C_n = #W_n · (1 + 2^n ∑_{1≤i≤n} max(0, C_i))^n` (the slow bound `slow 0` is
  set to `0`, since (D.7) and the recursion only use orders `m ≥ 1`), which
  depends only on `n`, the index type of the directions, and the bounds `C_m`,
  `1 ≤ m ≤ n`, of (D.7).
* Hölder version (appD:186-187): the statement is abstract in the zero-order
  seminorms, so the half-Hölder case is the same proof with `pA`, `pE`, `pF`
  the zero-order half-Hölder norms; the product inequality in `C^{0,1/2}` is
  the hypothesis `hB` for those norms.

Equation numbers: (D.1) for the norms, (D.7) `cc:uf:trunc:eq:slow` for the
slow-coefficient hypothesis. -/
theorem Proof.lemma_D_3 : Statement.lemma_D_3 := by
  intro Idx _ _ n Cm
  let slow : ℕ → ℝ := fun m => if m = 0 then 0 else max 0 (Cm m)
  have hslow (m : ℕ) : 0 ≤ slow m := by
    dsimp only [slow]
    split_ifs
    exacts [le_rfl, le_max_left _ _]
  refine ⟨((hierarchyAdmissibleWords Idx n).card : ℝ) *
    (1 + 2 ^ n * ∑ i ∈ Finset.range (n + 1), slow i) ^ n, by
      have : 0 ≤ ∑ i ∈ Finset.range (n + 1), slow i :=
        Finset.sum_nonneg fun i _ => hslow i
      positivity, ?_⟩
  intro J A E F _ _ _ _ _ _ _ DA DE DF pA pE pF L₀ T c b Clow hComm hProd hFC hAC hb hB hLow
    hInv hSlow v f hEq
  exact paperLemmaD3_lifting DA DE DF n pA pE pF L₀ T c hComm hProd hFC b hB hLow hInv slow
    hslow
    (fun w hw1 hwn => appendixSlowCoefficient_word_le DA pA hAC c b hb hLow w
      ((hSlow _ hw1 hwn).trans (by
        dsimp only [slow]
        split_ifs with h0
        · exact absurd h0 (Nat.one_le_iff_ne_zero.mp hw1)
        · exact le_max_right _ _))) hEq

end TorusEuler.Paper
