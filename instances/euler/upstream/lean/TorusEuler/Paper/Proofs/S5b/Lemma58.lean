import TorusEuler.Paper.Proofs.S5b.Lemma58Core
import TorusEuler.Paper.Proofs.S5b.Lemma58OddB

/-!
# Lemma 5.8: conditional proof

`S5b.oddExpansions_of` derives the oddness of `W^♮` ("`W^♮` is odd by the symmetry of the
construction of Subsection 5.5 under `(a,s) ↦ (-a,-s)`", `sections/08_exact_wave.tex:121-123`)
from the uniqueness clause of Proposition 5.4: the reflected family `S5b.reflFamily u` is again
an expansion with the same data (`S5b.isExpansion_reflFamily`), hence equal to `u` level by
level, so `W = ϱW`, i.e. `W(t,-a,-s) = -W(t,a,s)`, and `W^♮(t,·)` is odd because `X(t,·)⁻¹` is
odd (library `inverseParentGraphRead_reflection`).

`Proof.lemma_5_8_of` is then `S5b.lemma_5_8_of_odd` with this oddness.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

open HierarchyTwistedProfile

noncomputable section

namespace S5b

/-- **Oddness of `W^♮` from the uniqueness clause of Proposition 5.4**
(`sections/08_exact_wave.tex:121-123`). For `a ≥ max(a₄, 3)`, the reflected family
`reflFamily u` (`ϱV_p, ϱC_p, ϱB_p, 𝗉_p∘reflection, q̄_p∘reflection`) is an expansion with
`R ↦ ϱR`, `S ↦ ϱS` (`isExpansion_reflFamily`); the uniqueness clause of `h5_4` gives
`V_p = ϱV_p`, `B_p = ϱB_p` (`p ≤ P`) and `C_{p+1} = ϱC_{p+1}`, hence `W = ϱW`, and `W^♮(t,·)` is
odd since `X(t,·)` is odd. -/
theorem oddExpansions_of (h5_4 : Statement.proposition_5_4) : OddExpansions := by
  obtain ⟨a₄, h4⟩ := h5_4
  refine ⟨max a₄ 3, fun a ha => ?_⟩
  intro T hT U X pU k D lam t₀ center d χ hP hL hO amp hamp P hP2 R S u hu t ht
  have ha4 : a₄ ≤ a := le_of_max_le_left ha
  have ha3 : 3 ≤ a := le_of_max_le_right ha
  have hℓ : 0 < S5.radius D a := Bridge.radius_pos hP a
  have hfit : 2 * S5.radius D a < 1 / 2 := Bridge.radius_fits hP.scale_ge_two ha3
  have hh : 0 < S5.width lam := Bridge.width_pos hP
  have hh₁ : S5.width lam ≤ 1 := Bridge.width_le_one hP
  -- the reflected family is an expansion with the same data
  have hu' := isExpansion_reflFamily hP hL hamp hℓ hfit hh hh₁ hu
  -- uniqueness clause of Proposition 5.4
  obtain ⟨-, h4r⟩ := h4 a ha4 hT d χ hP hL hO
  obtain ⟨-, huniq, -⟩ := h4r amp hamp P hP2
  obtain ⟨-, -, hlev, hC⟩ := huniq R S (vrefl R) (vrefl S) u (reflFamily u) hu hu'
  -- `W = ϱW`
  have hW : S5.expansion u P = vrefl (S5.expansion u P) := by
    unfold S5.expansion
    rw [map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.mem_Icc.mp hp
    have h1 := hlev p hp
    have h2 := hC (p + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) h1.1 h2) h1.2.1
  have hrefl : reflection (S5.expansion u P) = -S5.expansion u P := by
    nth_rewrite 2 [hW]
    rw [vrefl_apply, neg_neg]
  have hpar := parity_of_odd hrefl
  intro x
  rw [inverseParentGraphRead_reflection hT hP.flow hP.velocity_smooth hP.velocity_periodic
    hP.velocity_odd _ hpar ht x, neg_one_smul]

end S5b

/-- **Proof of Lemma 5.8** (`cc:uf:step:lem:approximate`, `sections/08_exact_wave.tex:108-144`;
statement :82-107, equations (5.43), (5.46)–(5.48), with (5.29), (5.30), (3.8)).

* `h5_4` (Proposition 5.4): `𝐝̃·W = 0` (divergence of `V`), the identity (5.29) (equation
  (5.46), TeX :108-115), `W_osc = ∑(V_i + C_{i+1})` with its support in `supp g` and its
  vanishing before `t₀` (hypothesis of Lemma 5.7 for `W_osc`, and (5.47), (5.48) before `t₀`),
  `R_P` independent of the phase outside `supp g` (hypothesis of Lemma 5.7 for `R_P`); and its
  uniqueness clause for the oddness of `W^♮` ("by the symmetry of the construction under
  `(a,s) ↦ (-a,-s)`", TeX :121-123, `S5b.oddExpansions_of`).
  The joint smoothness of `V` and `Π` asserted by Proposition 5.4 (TeX :120-121) is built into the
  representation (the levels are `HierarchyTwistedProfile` values), so `approx_smooth` needs no
  input from `h5_4`.
* `h5_6` (Theorem 5.6), whose hypothesis `𝖣^{C₆}λ^{-1/12} ≤ 1` follows from (5.43): (5.37) at
  order `0` for (5.47) (TeX :125-127) and at order `m+1` for (5.48) (`W_osc`, `W̄`, TeX
  :128-131), and (5.38) at order `2` for `R_P` (TeX :132-136).
* `h5_7` (Lemma 5.7): (5.45) weighted for `W_osc`, phase-independent on `[0,T]` for `W̄`
  (TeX :128-131), unweighted at `m = 1` for `R_P` (TeX :132-136), and weighted at `m = 1` for
  `A₁ + C[A₁]` (the activation term `R_χ̃ = χ̃'(A₁ + C[A₁])`, TeX :138-143).
* `h5_3` (Lemma 5.3): (5.22) at order `3` for `‖A₁‖_{[3],γ}` (TeX :137-138).
* `h5_5` (Lemma 5.5): (5.31) at order `2` for `‖C[A₁]‖_{[2],γ}` (TeX :137-138).

The assembly is `S5b.lemma_5_8_of_odd` (constants in its docstring). -/
theorem Proof.lemma_5_8_of (h5_3 : Statement.lemma_5_3) (h5_4 : Statement.proposition_5_4)
    (h5_5 : Statement.lemma_5_5) (h5_6 : Statement.theorem_5_6) (h5_7 : Statement.lemma_5_7) :
    Statement.lemma_5_8 :=
  S5b.lemma_5_8_of_odd h5_3 h5_4 h5_5 h5_6 h5_7 (S5b.oddExpansions_of h5_4)

end

end TorusEuler.Paper
