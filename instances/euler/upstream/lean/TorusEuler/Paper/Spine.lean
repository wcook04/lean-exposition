import TorusEuler.Paper.All

/-! The proof spine of the latest manuscript.

Generated from `formalization/spine.json` by `spine_gen.py`; do not edit by hand.
Each numbered result is the conditional proof of its statement applied to the
spine nodes of exactly the results its TeX proof cites. -/

/-- Spine node for lemma 1.3 (`cc:uf:tower:lem:slow-orders`). Cites: none. -/
theorem TorusEuler.Paper.lemma_1_3 : TorusEuler.Paper.Statement.lemma_1_3 :=
  TorusEuler.Paper.Proof.lemma_1_3

/-- Spine node for  unnumbered display eq_5_59 (`cc:holder:product-growth`). Cites: none. -/
theorem TorusEuler.Paper.Text.eq_5_59 : TorusEuler.Paper.Statement.Text.eq_5_59 :=
  TorusEuler.Paper.Proof.Text.eq_5_59

/-- Spine node for proposition 8.1 (`cc:uf:terminal:agreement`). Cites: 1.3, eq_5_59. -/
theorem TorusEuler.Paper.proposition_8_1 : TorusEuler.Paper.Statement.proposition_8_1 :=
  TorusEuler.Paper.Proof.proposition_8_1_of TorusEuler.Paper.lemma_1_3 TorusEuler.Paper.Text.eq_5_59

/-- Spine node for lemma 2.2 (`cc:lem:frame`). Cites: none. -/
theorem TorusEuler.Paper.lemma_2_2 : TorusEuler.Paper.Statement.lemma_2_2 :=
  TorusEuler.Paper.Proof.lemma_2_2

/-- Spine node for lemma 2.4 (`cc:uf:exact:lem:additive`). Cites: 2.2. -/
theorem TorusEuler.Paper.lemma_2_4 : TorusEuler.Paper.Statement.lemma_2_4 :=
  TorusEuler.Paper.Proof.lemma_2_4_of TorusEuler.Paper.lemma_2_2

/-- Spine node for lemma B.1 (`cc:uf:trunc:lem:cutoff`). Cites: none. -/
theorem TorusEuler.Paper.lemma_B_1 : TorusEuler.Paper.Statement.lemma_B_1 :=
  TorusEuler.Paper.Proof.lemma_B_1

/-- Spine node for proposition 8.2 (`cc:uf:terminal:velocity-curl`). Cites: 1.3, 2.2, 2.4, B.1. -/
theorem TorusEuler.Paper.proposition_8_2 : TorusEuler.Paper.Statement.proposition_8_2 :=
  TorusEuler.Paper.Proof.proposition_8_2_of TorusEuler.Paper.lemma_1_3 TorusEuler.Paper.lemma_2_2 TorusEuler.Paper.lemma_2_4 TorusEuler.Paper.lemma_B_1

/-- Spine node for corollary 8.3 (`cc:uf:terminal:time`). Cites: none. -/
theorem TorusEuler.Paper.corollary_8_3 : TorusEuler.Paper.Statement.corollary_8_3 :=
  TorusEuler.Paper.Proof.corollary_8_3

/-- Spine node for proposition 8.4 (`cc:uf:terminal:off-origin`). Cites: 1.3. -/
theorem TorusEuler.Paper.proposition_8_4 : TorusEuler.Paper.Statement.proposition_8_4 :=
  TorusEuler.Paper.Proof.proposition_8_4_of TorusEuler.Paper.lemma_1_3

/-- Spine node for lemma 2.5 (`cc:lem:model`). Cites: none. -/
theorem TorusEuler.Paper.lemma_2_5 : TorusEuler.Paper.Statement.lemma_2_5 :=
  TorusEuler.Paper.Proof.lemma_2_5

/-- Spine node for lemma 2.6 (`cc:lem:finite-comparison`). Cites: 2.4, 2.5. -/
theorem TorusEuler.Paper.lemma_2_6 : TorusEuler.Paper.Statement.lemma_2_6 :=
  TorusEuler.Paper.Proof.lemma_2_6_of TorusEuler.Paper.lemma_2_4 TorusEuler.Paper.lemma_2_5

/-- Spine node for lemma 2.7 (`cc:lem:new-wave-couplings`). Cites: 2.4, 2.5, 2.6. -/
theorem TorusEuler.Paper.lemma_2_7 : TorusEuler.Paper.Statement.lemma_2_7 :=
  TorusEuler.Paper.Proof.lemma_2_7_of TorusEuler.Paper.lemma_2_4 TorusEuler.Paper.lemma_2_5 TorusEuler.Paper.lemma_2_6

/-- Spine node for proposition 2.8 (`cc:prop:finite-return`). Cites: 2.4, 2.5, 2.6, 2.7. -/
theorem TorusEuler.Paper.proposition_2_8 : TorusEuler.Paper.Statement.proposition_2_8 :=
  TorusEuler.Paper.Proof.proposition_2_8_of TorusEuler.Paper.lemma_2_4 TorusEuler.Paper.lemma_2_5 TorusEuler.Paper.lemma_2_6 TorusEuler.Paper.lemma_2_7

/-- Spine node for lemma 4.1 (`cc:uf:mean:hardy`). Cites: none. -/
theorem TorusEuler.Paper.lemma_4_1 : TorusEuler.Paper.Statement.lemma_4_1 :=
  TorusEuler.Paper.Proof.lemma_4_1

/-- Spine node for lemma A.2 (`cc:holder:freezing`). Cites: none. -/
theorem TorusEuler.Paper.lemma_A_2 : TorusEuler.Paper.Statement.lemma_A_2 :=
  TorusEuler.Paper.Proof.lemma_A_2

/-- Spine node for theorem A.1 (`cc:holder:linear`). Cites: A.2. -/
theorem TorusEuler.Paper.theorem_A_1 : TorusEuler.Paper.Statement.theorem_A_1 :=
  TorusEuler.Paper.Proof.theorem_A_1_of TorusEuler.Paper.lemma_A_2

/-- Spine node for theorem 4.2 (`cc:uf:mean:inverse`). Cites: 4.1, A.1, A.2. -/
theorem TorusEuler.Paper.theorem_4_2 : TorusEuler.Paper.Statement.theorem_4_2 :=
  TorusEuler.Paper.Proof.theorem_4_2_of TorusEuler.Paper.lemma_4_1 TorusEuler.Paper.theorem_A_1 TorusEuler.Paper.lemma_A_2

/-- Spine node for proposition 5.4 (`cc:uf:hier:prop:identity`). Cites: 4.2. -/
theorem TorusEuler.Paper.proposition_5_4 : TorusEuler.Paper.Statement.proposition_5_4 :=
  TorusEuler.Paper.Proof.proposition_5_4_of TorusEuler.Paper.theorem_4_2

/-- Spine node for lemma 3.1 (`cc:uf:exact:lem:profile`). Cites: none. -/
theorem TorusEuler.Paper.lemma_3_1 : TorusEuler.Paper.Statement.lemma_3_1 :=
  TorusEuler.Paper.Proof.lemma_3_1

/-- Spine node for lemma D.2 (`cc:uf:trunc:lem:coefficients`). Cites: none. -/
theorem TorusEuler.Paper.lemma_D_2 : TorusEuler.Paper.Statement.lemma_D_2 :=
  TorusEuler.Paper.Proof.lemma_D_2

/-- Spine node for proposition 5.1 (`cc:uf:trunc:prop:parent`). Cites: B.1, D.2. -/
theorem TorusEuler.Paper.proposition_5_1 : TorusEuler.Paper.Statement.proposition_5_1 :=
  TorusEuler.Paper.Proof.proposition_5_1_of TorusEuler.Paper.lemma_B_1 TorusEuler.Paper.lemma_D_2

/-- Spine node for lemma D.1 (`cc:uf:trunc:lem:fields`). Cites: none. -/
theorem TorusEuler.Paper.lemma_D_1 : TorusEuler.Paper.Statement.lemma_D_1 :=
  TorusEuler.Paper.Proof.lemma_D_1

/-- Spine node for lemma D.3 (`cc:uf:trunc:lem:lifting`). Cites: none. -/
theorem TorusEuler.Paper.lemma_D_3 : TorusEuler.Paper.Statement.lemma_D_3 :=
  TorusEuler.Paper.Proof.lemma_D_3

/-- Spine node for lemma 5.3 (`cc:uf:tower:lem:inverse`). Cites: 3.1, 5.1, D.1, D.2, D.3. -/
theorem TorusEuler.Paper.lemma_5_3 : TorusEuler.Paper.Statement.lemma_5_3 :=
  TorusEuler.Paper.Proof.lemma_5_3_of TorusEuler.Paper.lemma_3_1 TorusEuler.Paper.proposition_5_1 TorusEuler.Paper.lemma_D_1 TorusEuler.Paper.lemma_D_2 TorusEuler.Paper.lemma_D_3

/-- Spine node for lemma 5.5 (`cc:uf:hier:lem:relay`). Cites: 5.1, D.1. -/
theorem TorusEuler.Paper.lemma_5_5 : TorusEuler.Paper.Statement.lemma_5_5 :=
  TorusEuler.Paper.Proof.lemma_5_5_of TorusEuler.Paper.proposition_5_1 TorusEuler.Paper.lemma_D_1

/-- Spine node for  unnumbered display eq_D_2 (`cc:uf:trunc:eq:holder-sup`). Cites: none. -/
theorem TorusEuler.Paper.Text.eq_D_2 : TorusEuler.Paper.Statement.Text.eq_D_2 :=
  TorusEuler.Paper.Proof.Text.eq_D_2

/-- Spine node for  unnumbered display eq_5_13 (`cc:uf:mean:thresholds`). Cites: 5.1, D.2, eq_D_2. -/
theorem TorusEuler.Paper.Text.eq_5_13 : TorusEuler.Paper.Statement.Text.eq_5_13 :=
  TorusEuler.Paper.Proof.Text.eq_5_13_of TorusEuler.Paper.proposition_5_1 TorusEuler.Paper.lemma_D_2 TorusEuler.Paper.Text.eq_D_2

/-- Spine node for  unnumbered display eq_5_14 (`cc:uf:mean:holder-bound`). Cites: 4.2, 5.1, D.2, D.3, eq_5_13. -/
theorem TorusEuler.Paper.Text.eq_5_14 : TorusEuler.Paper.Statement.Text.eq_5_14 :=
  TorusEuler.Paper.Proof.Text.eq_5_14_of TorusEuler.Paper.theorem_4_2 TorusEuler.Paper.proposition_5_1 TorusEuler.Paper.lemma_D_2 TorusEuler.Paper.lemma_D_3 TorusEuler.Paper.Text.eq_5_13

/-- Spine node for proposition 5.2 (`cc:uf:mean:columns`). Cites: 5.1, D.1, eq_D_2, eq_5_14. -/
theorem TorusEuler.Paper.proposition_5_2 : TorusEuler.Paper.Statement.proposition_5_2 :=
  TorusEuler.Paper.Proof.proposition_5_2_of TorusEuler.Paper.proposition_5_1 TorusEuler.Paper.lemma_D_1 TorusEuler.Paper.Text.eq_D_2 TorusEuler.Paper.Text.eq_5_14

/-- Spine node for theorem 5.6 (`cc:uf:hier:thm:depth`). Cites: 5.1, 5.2, 5.3, 5.4, 5.5, D.1, B.1. -/
theorem TorusEuler.Paper.theorem_5_6 : TorusEuler.Paper.Statement.theorem_5_6 :=
  TorusEuler.Paper.Proof.theorem_5_6_of TorusEuler.Paper.proposition_5_1 TorusEuler.Paper.proposition_5_2 TorusEuler.Paper.lemma_5_3 TorusEuler.Paper.proposition_5_4 TorusEuler.Paper.lemma_5_5 TorusEuler.Paper.lemma_D_1 TorusEuler.Paper.lemma_B_1

/-- Spine node for lemma 5.7 (`cc:uf:hier:lem:physical`). Cites: 5.1, D.1. -/
theorem TorusEuler.Paper.lemma_5_7 : TorusEuler.Paper.Statement.lemma_5_7 :=
  TorusEuler.Paper.Proof.lemma_5_7_of TorusEuler.Paper.proposition_5_1 TorusEuler.Paper.lemma_D_1

/-- Spine node for lemma 5.8 (`cc:uf:step:lem:approximate`). Cites: 5.3, 5.4, 5.5, 5.6, 5.7. -/
theorem TorusEuler.Paper.lemma_5_8 : TorusEuler.Paper.Statement.lemma_5_8 :=
  TorusEuler.Paper.Proof.lemma_5_8_of TorusEuler.Paper.lemma_5_3 TorusEuler.Paper.proposition_5_4 TorusEuler.Paper.lemma_5_5 TorusEuler.Paper.theorem_5_6 TorusEuler.Paper.lemma_5_7

/-- Spine node for lemma 5.9 (`cc:uf:step:lem:pressure-center`). Cites: 3.1, 4.2, 5.1, 5.3, 5.6, 5.7, B.1, D.1, 5.4. -/
theorem TorusEuler.Paper.lemma_5_9 : TorusEuler.Paper.Statement.lemma_5_9 :=
  TorusEuler.Paper.Proof.lemma_5_9_of TorusEuler.Paper.lemma_3_1 TorusEuler.Paper.theorem_4_2 TorusEuler.Paper.proposition_5_1 TorusEuler.Paper.lemma_5_3 TorusEuler.Paper.theorem_5_6 TorusEuler.Paper.lemma_5_7 TorusEuler.Paper.lemma_B_1 TorusEuler.Paper.lemma_D_1 TorusEuler.Paper.proposition_5_4

/-- Spine node for lemma 5.10 (`cc:uf:step:lem:flow-bounds`). Cites: 5.1, 5.6, 5.4. -/
theorem TorusEuler.Paper.lemma_5_10 : TorusEuler.Paper.Statement.lemma_5_10 :=
  TorusEuler.Paper.Proof.lemma_5_10_of TorusEuler.Paper.proposition_5_1 TorusEuler.Paper.theorem_5_6 TorusEuler.Paper.proposition_5_4

/-- Spine node for proposition 5.11 (`cc:uf:step:thm:step`). Cites: 5.8, 5.9, B.1, eq_5_59. -/
theorem TorusEuler.Paper.proposition_5_11 : TorusEuler.Paper.Statement.proposition_5_11 :=
  TorusEuler.Paper.Proof.proposition_5_11_of TorusEuler.Paper.lemma_5_8 TorusEuler.Paper.lemma_5_9 TorusEuler.Paper.lemma_B_1 TorusEuler.Paper.Text.eq_5_59

/-- Spine node for lemma 6.1 (`cc:uf:base:lem:first`). Cites: 2.2. -/
theorem TorusEuler.Paper.lemma_6_1 : TorusEuler.Paper.Statement.lemma_6_1 :=
  TorusEuler.Paper.Proof.lemma_6_1_of TorusEuler.Paper.lemma_2_2

/-- Spine node for theorem 7.1 (`cc:uf:tower:thm:finite`). Cites: 1.3, 2.2, 2.5, 2.6, 2.7, 2.8, 5.4, 5.8, 5.9, 5.10, 5.11, 6.1, B.1. -/
theorem TorusEuler.Paper.theorem_7_1 : TorusEuler.Paper.Statement.theorem_7_1 :=
  TorusEuler.Paper.Proof.theorem_7_1_of TorusEuler.Paper.lemma_1_3 TorusEuler.Paper.lemma_2_2 TorusEuler.Paper.lemma_2_5 TorusEuler.Paper.lemma_2_6 TorusEuler.Paper.lemma_2_7 TorusEuler.Paper.proposition_2_8 TorusEuler.Paper.proposition_5_4 TorusEuler.Paper.lemma_5_8 TorusEuler.Paper.lemma_5_9 TorusEuler.Paper.lemma_5_10 TorusEuler.Paper.proposition_5_11 TorusEuler.Paper.lemma_6_1 TorusEuler.Paper.lemma_B_1

/-- Spine node for  unnumbered display section8_setting (`unlabeled`). Cites: 7.1. -/
theorem TorusEuler.Paper.Text.section8_setting : TorusEuler.Paper.Statement.Text.section8_setting :=
  TorusEuler.Paper.Proof.Text.section8_setting_of TorusEuler.Paper.theorem_7_1

/-- Spine node for theorem 1.1 (`cc:target:unforced`). Cites: 8.1, 8.2, 8.3, 8.4, section8_setting. -/
theorem TorusEuler.Paper.theorem_1_1 : TorusEuler.Paper.Statement.theorem_1_1 :=
  TorusEuler.Paper.Proof.theorem_1_1_of TorusEuler.Paper.proposition_8_1 TorusEuler.Paper.proposition_8_2 TorusEuler.Paper.corollary_8_3 TorusEuler.Paper.proposition_8_4 TorusEuler.Paper.Text.section8_setting

/-- Spine node for remark 1.2 (`unlabeled`). Cites: none. -/
theorem TorusEuler.Paper.remark_1_2 : TorusEuler.Paper.Statement.remark_1_2 :=
  TorusEuler.Paper.Proof.remark_1_2

/-- Spine node for lemma 2.1 (`cc:lem:wave`). Cites: none. -/
theorem TorusEuler.Paper.lemma_2_1 : TorusEuler.Paper.Statement.lemma_2_1 :=
  TorusEuler.Paper.Proof.lemma_2_1

/-- Spine node for lemma 2.3 (`cc:lem:strong-shear`). Cites: 2.2. -/
theorem TorusEuler.Paper.lemma_2_3 : TorusEuler.Paper.Statement.lemma_2_3 :=
  TorusEuler.Paper.Proof.lemma_2_3_of TorusEuler.Paper.lemma_2_2
