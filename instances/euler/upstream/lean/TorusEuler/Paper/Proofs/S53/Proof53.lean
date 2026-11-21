import TorusEuler.Paper.Proofs.S53.Lemma53
import TorusEuler.Paper.Proofs.S53.Library.OdeFinal

/-!
# Proof of Lemma 5.3 (conditional)

Conditional proof `Paper.Proof.lemma_5_3_of` of `Paper.Statement.lemma_5_3` of the latest manuscript
(`cc:uf:tower:lem:inverse`, sections/06c_finite_hierarchy.tex:54-220).
-/

namespace TorusEuler.Paper

noncomputable section

/-- Proof of **Lemma 5.3** (`cc:uf:tower:lem:inverse`), following sections/06c_finite_hierarchy.tex:54-220.

* (5.19), near-origin bounds of the seed (06c:105-158): the coefficient jets (D.6) of Proposition 5.1
  (`h5_1`) give `Lib.S5a.leafBounds_of_h51` and `Lib.S5a.seedNear_of_h51`; the seed on the ball comes from
  the jets of the coframe (`Lib.S5a.exists_seedOn_of_D6`, the proof of Lemma 5.3 itself).
* The coefficients `A_⊥`, `A_⊥†`, `ℳ_⊥` satisfy (D.6), 06c:92-95: **Lemma D.2(a)** (`hD_2`, through
  `Lib.S53.mul_of_D2`) is applied in the fixed value space of `3 × 3` matrices to the products `G Q` and
  `(G Q)(M F)` of the coefficients of Proposition 5.1 (`Lib.S53.transverseCoframe_jetPower`); `A_⊥` and
  `A_⊥†` are fixed contractions of them. Representation: Lemma D.2(b) is replaced by the pullback
  representation `A_⊥† = π G Q` (`G` the inverse deformation, `Q = Id - P_κ` the projection orthogonal to
  the covector `κ`, `π` the orthogonal projection onto the transverse plane), with `A_⊥† A_⊥ = Id` and
  `A_⊥ A_⊥† = Id - P_κ` as at 06c:41-45; the jets of `P_κ` come from `h5_1`, so no inverse of `K_⊥` is formed.
  This is a deviation of the proof route (not forced by the statement): the TeX bounds `K_⊥⁻¹` (06c:89-95)
  and uses D.2(b); the Lean uses the identity `A_⊥† = π G Q` and D.2(a) only.
* The conditions (D.7) and the rescaled coefficients, 06c:173-174 and 181-184: **Lemma D.2(c)** (`hD_2`,
  through `Lib.S53.rescale_of_D2`, `Lib.S53.rescaled_coframe_jets`, `Lib.S53.rescaled_pressure_jets`)
  at the base scale `D₀` with `D₀ ^ 64 ≤ D` (`Lib.S53.Leaf2`): the rescaled jets of `A_⊥`, `A_⊥†`, the
  bound `ℓ_*|A_⊥|_m ≤ C D^{-3}` for positive orders, and the rescaled jets of the coefficients of the
  pressure operators. Deviation: the TeX takes the coefficient bound (5.8) of Proposition 5.1 for
  `κ/λ`, `λ²/|κ|²` and `P_κ` (06c:190-192, 205-206); the Lean re-derives the rescaled jets of `M`, `κ/λ`,
  `λ²/|κ|²` from the (D.6) conjunct of `h5_1` through D.2(c), and does not use the (5.8) conjunct.
* Zero-order estimate (5.23) (06c:96-128) and the ODE for the derivative words, part (i) (06c:160-184): the jets of the
  solution of `x' = A x + f` in the constant label and phase directions form the spaces on which
  **Lemma D.3** (`hD_3`, in the form `Lib.S53.jetD3`) lifts the zero-order bound from the stability
  hypothesis to all orders; the factor `Φ N q` is `Lib.S53.odeWordBound_of_D3 hD_3`.
* The phase primitive in the pressure bound (5.24), 06c:185-198 (part (ii)): **Lemma D.1** (`hD_1`, the bound (D.5)),
  through `Lib.S5a.relayWordBound_linearPrimitive_of_D1`. The product estimate (D.4), cited at
  06c:180-181, 191, 206 and 214, is the pointwise Leibniz rule (`phaseJetBound_bilinear_product` and its
  relatives), taken as glue, not from `hD_1`.
* Uniqueness (ii), 06c:185-198: `Bridge.TransverseSolution.unique`.
* Regularity of the seed (iii), 06c:199-219: `Bridge.hierarchyRegularity_of_isSeed`. Deviation: instead of
  applying (5.20) with `f = 0` to `g·a` (06c:208-210), the Lean re-runs the argument of (i) with `f = 0` for
  the enveloped seed in rescaled labels (`SeedOn.envelopedAmplitude_scaledJetBound`, with its own Gronwall
  comparison, D.3 lifting and D.2(c) rescaling), and bounds `p[A_1]` from the explicit form (3.3) through
  `norm_phasePrimitive_le` instead of (5.24). The profile of Lemma 3.1 (`h3_1`: `‖F_h‖_[n] ≤ C_n h`,
  06c:211-213) enters through `Lib.S53.waveProfile_bounds` in `exists_scaled_deriv_waveProfile_bound` and
  `exists_scaled_wavePhaseJetBounds`. -/
theorem Proof.lemma_5_3_of (h3_1 : Statement.lemma_3_1) (h5_1 : Statement.proposition_5_1)
    (hD_1 : Statement.lemma_D_1) (hD_2 : Statement.lemma_D_2) (hD_3 : Statement.lemma_D_3) :
    Statement.lemma_5_3 :=
  lemma_5_3_of_ode h3_1 h5_1 hD_1 hD_2 (Lib.S53.odeWordBound_of_D3 hD_3)

end

end TorusEuler.Paper
