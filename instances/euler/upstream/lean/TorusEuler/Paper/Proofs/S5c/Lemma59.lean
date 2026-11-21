import TorusEuler.Paper.Proofs.S5c.Library.LeadingClaim
import TorusEuler.Paper.Proofs.S5c.Library.HigherClaim
import TorusEuler.Paper.Proofs.S5c.Library.MeanClaim
import TorusEuler.Paper.Proofs.S5c.Library.CenterBound
import TorusEuler.Paper.Proofs.S5c.Library.Assembly59

/-!
# Proof of Lemma 5.9 (package S5c)

Conditional proof `Paper.Proof.lemma_5_9_of` of the pressure Hessian bound (5.49) and the central
velocity gradient (5.50) (`cc:uf:step:lem:pressure-center`, `sections/08_exact_wave.tex:158-278`).
-/

namespace TorusEuler.Paper

noncomputable section

/-- **Proof of Lemma 5.9** following `sections/08_exact_wave.tex:158-278` (the hypotheses are the
cites of the ledger row, in ledger order: 3.1, 4.2, 5.1, 5.3, 5.6, 5.7, B.1, D.1, 5.4).

Step 1, the leading pressure `𝗉_1 = -c_𝐚P_h` (`:171-204`, (5.51)): `Lib.S5c.leadingHessianClaim`;
the first tensor `-c_𝐚F_h'κ⊗κ` uses `F_h' ≥ -Ch` and `P_h' = F_h` of `h3_1` (Lemma 3.1), and
`0 ≤ c_𝐚|κ|² ≤ 2|κ||M||𝐚|` the bound (5.19) of `h5_3` (Lemma 5.3); the other tensors are bounded through Lemma D.1 (`hD_1`: (D.3), (D.4)) with the coefficient norms
(D.6), (5.8) of `h5_1` (Proposition 5.1) and the bound (5.34) at `p = 1` of `h5_6` (Theorem 5.6)
(the TeX, `:201-203`, takes this bound `λ‖𝗉_1‖_{[2]} ≤ C𝖣^Cλ^{-5/4}` from (5.22), Lemma 5.3 (iii); the Lean
reads the same bound for the twisted profile from (5.34) at `p = 1`, which the TeX derives from (5.22),
`06c_finite_hierarchy.tex:514`; clause (iii) of `h5_3` is not used, see the notes of the package);
`𝗉_1 = 0` for `t < t₀` and off `supp g` comes from the cutoff and the envelope (`:185-186`), not
from Proposition 5.4.

Step 2, the higher oscillatory pressures (`:206-232`, (5.52)): `Lib.S5c.higherHessianClaim`; the
gradient profile `𝐝̃∑𝗉_p` is bounded in `‖·‖_{[1],γ}` by Lemma D.1 (`hD_1`: (D.3), (D.4)), from the
coefficient bounds (D.6), (5.8) of `h5_1` and (5.34) of `h5_6`; the supports and the vanishing
before `t₀` come from `h5_4`; (5.44) of `h5_7` converts the weighted norm into the Hessian bound.

Step 3, the mean pressures (`:233-255`): `Lib.S5c.meanHessianClaim`; Theorem 4.2 (`h4_2`) gives
`div W̄^♮ = 0` and the linearized Euler equation (4.12) for the sum of the mean equations (5.11),
(5.45) of `h5_7` and (5.37) of `h5_6` the size of the source and of `W̄^♮` in `C_tC^{1,1/2}`, and
Lemma B.1 (`hB_1`, Bernstein) the size of `∇U` in `C_tC^{0,1/2}`.

Step 4, the sum of the three Hessians is (5.49) (`:252-255`), `Lib.S5c.lemma59_of_claims`.

Step 5, the velocity gradient at the origin (`:257-278`): `Lib.S5c.centralReturnClaim`, (5.50), from
`F_h(0) = 0`, `F_h'(0) = 1` of `h3_1`, (5.34), (5.36), (5.37) of `h5_6`, (5.44) at `m = 1` of
`h5_7`, and the supports of `h5_4`. -/
theorem Proof.lemma_5_9_of (h3_1 : Statement.lemma_3_1) (h4_2 : Statement.theorem_4_2)
    (h5_1 : Statement.proposition_5_1) (h5_3 : Statement.lemma_5_3)
    (h5_6 : Statement.theorem_5_6) (h5_7 : Statement.lemma_5_7) (hB_1 : Statement.lemma_B_1)
    (hD_1 : Statement.lemma_D_1) (h5_4 : Statement.proposition_5_4) : Statement.lemma_5_9 :=
  Lib.S5c.lemma59_of_claims (Lib.S5c.leadingHessianClaim h3_1 h5_1 h5_3 h5_6 hD_1)
    (Lib.S5c.higherHessianClaim h5_1 h5_4 h5_6 h5_7 hD_1)
    (Lib.S5c.meanHessianClaim h4_2 h5_6 h5_7 hB_1)
    (Lib.S5c.centralReturnClaim h3_1 h5_4 h5_6 h5_7)

end

end TorusEuler.Paper
