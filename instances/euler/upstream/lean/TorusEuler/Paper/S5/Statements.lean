import TorusEuler.Paper.S5.Vocabulary

/-!
# Statements of Section 5 of the latest manuscript

Faithful statements (`Paper.Statement.*`) of Propositions 5.1, 5.2, 5.4, 5.11,
Lemmas 5.3, 5.5, 5.7–5.10, Theorem 5.6 and of the display (5.59) in the proof of
Proposition 5.11 (`Paper.Statement.Text.eq_5_59`), in the latest numbering of
`latest-pdf/main.aux`.

Common conventions (see `TorusEuler.Paper.S5` for the vocabulary):

* The standing hypotheses of §5.1 are `S5.Parent`, `S5.Launch`, `S5.Origin`; the
  coefficient profiles `(D_aX)⁻¹`, `M`, `κ` of the parent are carried by any
  `ParentGeometry` `d` (they are determined by `U`, `X`, `k_*`).
* The envelope radius is `ℓ_* = 𝖣^{-a}` with an absolute exponent `a` fixed
  sufficiently large (`∃ a₀, ∀ a ≥ a₀`), as in `08a_parent_step.tex:105-110`;
  the absolute exponents `C` may depend on `a`, which is itself absolute.
* Constants written `C_n`, `C_{n,p}`, `C_{m,P}` in the text are functions `K`
  quantified before the parent; the step constants `b`, `Γ_P` of §5.6 are
  "sufficiently large" (`∀ b ≥ b₀, ∀ Γ ≥ Γ₀`); every conclusion is monotone in
  them and hypothesis (5.43) is antitone, so this is the text's choice.
* The seed, the expansion of §5.5 and the truncation of §5.7 are objects fixed in
  the text; they enter in predicate form (`S5.IsSeed`, `S5.IsExpansion`,
  `S5.IsTruncation`), with existence (and uniqueness) asserted in Proposition 5.4
  and Proposition 5.11.
* The divergence corrections use the latest indexing `C₁ = 0`,
  `C_{p+1} = C[V_p]` (`S5.Cd`).
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

open HierarchyTwistedProfile LocalizedAmplitude ChildFlow

noncomputable section

/-- **Proposition 5.1** (`cc:uf:trunc:prop:parent`, sections/05b_parent_coefficients.tex:16).
There is an absolute exponent `C` such that each coefficient
`c ∈ {(D_aX)^{±1}, M, κ/λ, λ²/|κ|², P_κ}` satisfies (D.6)
`|c|_m ≤ C_m 𝖣^{C(m+1)}`; every field `f` with `|f|_m ≤ C'_m A_f 𝖣^m` satisfies
(5.7) `|f∘X|_m ≤ C_m A_f 𝖣^{Cm}`; and, when `ℓ_* ≤ 𝖣^{-C}`, (5.8)
`‖c‖_{[n]} ≤ C_n 𝖣^C`, `‖f∘X‖_{[n]} ≤ C_n A_f` for every `n`.
Equations: (D.6), (5.7), (5.8); standing (5.1), (5.3).

Representation: torus fields are `ℤ³`-periodic fields on `ℝ³`; the multi-index
sum `|c|_m` is replaced by the operator norm of the `m`-th Fréchet derivative,
pointwise in `(t,a)` (equivalent up to a factor `3^m`); `‖c‖_{[n]}` is
`∑_{j≤n} ℓ^j sup_a ‖D^j c(t)‖` at each time `t ∈ [0,T]` (the supremum over `t` is
the same bound); the constants of (5.7) depend on the constants `C'_m` of its
hypothesis (`∀ C', ∃ Kf`), while those of the coefficients do not; `f` takes
values in any real normed space and is smooth in `x` at each time. -/
def Statement.proposition_5_1 : Prop :=
  ∃ C : ℕ, ∃ K : ℕ → ℝ, ∀ C' : ℕ → ℝ, ∃ Kf : ℕ → ℝ,
    ∀ {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3} {D lam t₀ : ℝ},
      0 < T → S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ →
      let F := fun (t : ℝ) (a : Vec3) => fderiv ℝ (X 0 t) a
      let G := fun (t : ℝ) (a : Vec3) => fderiv ℝ (X t 0) (X 0 t a)
      let M := S5.strainField U X
      let κn := fun (t : ℝ) (a : Vec3) => lam⁻¹ • S5.waveVector X k t a
      let ν := fun (t : ℝ) (a : Vec3) => lam ^ 2 / ‖S5.waveVector X k t a‖ ^ 2
      let Pκ := fun (t : ℝ) (a : Vec3) => (‖S5.waveVector X k t a‖ ^ 2)⁻¹ •
        InnerProductSpace.rankOne ℝ (S5.waveVector X k t a) (S5.waveVector X k t a)
      -- (D.6) for the six coefficients
      (∀ m : ℕ, ∀ t ∈ Icc 0 T, ∀ a : Vec3,
        ‖iteratedFDeriv ℝ m (F t) a‖ ≤ K m * D ^ (C * (m + 1)) ∧
        ‖iteratedFDeriv ℝ m (G t) a‖ ≤ K m * D ^ (C * (m + 1)) ∧
        ‖iteratedFDeriv ℝ m (M t) a‖ ≤ K m * D ^ (C * (m + 1)) ∧
        ‖iteratedFDeriv ℝ m (κn t) a‖ ≤ K m * D ^ (C * (m + 1)) ∧
        ‖iteratedFDeriv ℝ m (ν t) a‖ ≤ K m * D ^ (C * (m + 1)) ∧
        ‖iteratedFDeriv ℝ m (Pκ t) a‖ ≤ K m * D ^ (C * (m + 1))) ∧
      -- (5.7)
      (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → Vec3 → E) (Af : ℝ),
        0 ≤ Af → (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (f t)) →
        (∀ m : ℕ, ∀ t ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ m (f t) x‖ ≤ C' m * Af * D ^ m) →
        ∀ m : ℕ, ∀ t ∈ Icc 0 T, ∀ a,
          ‖iteratedFDeriv ℝ m (fun b => f t (X 0 t b)) a‖ ≤ Kf m * Af * D ^ (C * m)) ∧
      -- (5.8)
      (∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ (D ^ C)⁻¹ → ∀ n : ℕ, ∀ t ∈ Icc 0 T,
        (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (F t))) ≤
            K n * D ^ C ∧
        (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (G t))) ≤
            K n * D ^ C ∧
        (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (M t))) ≤
            K n * D ^ C ∧
        (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (κn t))) ≤
            K n * D ^ C ∧
        (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (ν t))) ≤
            K n * D ^ C ∧
        (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (Pκ t))) ≤
            K n * D ^ C ∧
        ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → Vec3 → E) (Af : ℝ),
          0 ≤ Af → (∀ r ∈ Icc 0 T, ContDiff ℝ ∞ (f r)) →
          (∀ m : ℕ, ∀ r ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ m (f r) x‖ ≤ C' m * Af * D ^ m) →
          (∑ j ∈ Finset.range (n + 1),
            ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (fun b => f t (X 0 t b)))) ≤ Kf n * Af)

/-- **Proposition 5.2** (`cc:uf:mean:columns`, sections/06d_mean_estimates.tex:22).
There is an absolute exponent `C` such that, for every `n ≥ 0`, every solution
`(B, q̄)` of the mean equation (5.11) with source `f̄` satisfies (5.12)
`‖B‖_{[n]} ≤ C_n 𝖣^C ‖f̄‖_{[n+1]}`.
Equations: (5.11), (5.12); standing (5.1), (5.2).

Representation: `B`, `q̄`, `f̄` are phase-independent lattice-twisted profiles on
`[0,T]`; the mean equation is `S5.MeanSolution` (operator form of
`B_t + MB + 𝐝q̄ = f̄`, with `B = D_aX z_t`, `z(0) = z(T) = 0`, `div_a z_t = 0` in
place of `𝐝·B = 0`); `‖·‖_{[n]}` is the unweighted norm (D.1) on `[0,T]`
(`S5.uNorm`), in which phase derivatives of phase-independent fields vanish;
`ℓ_* = 𝖣^{-a}` with `a ≥ a₀`. -/
def Statement.proposition_5_2 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ K : ℕ → ℝ,
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam : ℝ} (d : ParentGeometry hT U X k),
      S5.Parent T U X pU D lam →
      ∀ (f B : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ),
        S5.MeanSolution d f B q →
        ∀ n : ℕ, S5.uNorm (S5.radius D a) (S5.width lam) n B ≤
          K n * D ^ C * S5.uNorm (S5.radius D a) (S5.width lam) (n + 1) f

/-- **Lemma 5.3** (`cc:uf:tower:lem:inverse`, sections/06c_finite_hierarchy.tex:54).
For `t₀ ≤ t ≤ T` and `|a| ≤ 2ℓ_*` the seed satisfies (5.19)
`|𝐚(t,a)| ≤ 2|𝐚(t,0)|`, `(κ·M𝐚)(t,a) > 0`. There is an absolute exponent `C`
such that at every order `n`: (i) (5.20)
`‖V‖_{[n],γ} ≤ C_n 𝖣^C (γ(t₀)⁻¹‖V(t₀)‖_{[n]} + ‖f‖_{[n],γ})` for smooth `V`, `f`
satisfying (5.17) on `[t₀,T]`, `V ⊥ κ`, with `V(t₀)` and `f` vanishing at labels
outside `supp g`; (ii) (5.21) `‖V‖_{[n],γ} + λ‖𝗉‖_{[n],γ} ≤ C_n 𝖣^C ‖f‖_{[n],γ}`
for the solution of (5.15) with `V(0) = 0` and source `f` of zero phase mean
vanishing for `t < t₀` and outside `supp g`; (iii) (5.22)
`‖A₁‖_{[n],γ} + λ‖𝗉[A₁]‖_{[n],γ} ≤ C_n 𝖣^C λ^{-5/4}` on `[t₀,T]`.
Equations: (5.15), (5.17), (5.19)–(5.22); standing (5.1), (5.3)–(5.5).

Representation: `V`, `f` are lattice-twisted profiles on `[0,T]` (only their
values on `[t₀,T]` enter (i)); a smooth twisted field given only on `[t₀,T]`, as
in the text, enters (i) through any smooth twisted profile on `[0,T]` that agrees
with it on `[t₀,T]` (a Seeley extension in time, which acts pointwise in the label
and the phase and so keeps the lattice twist; for `A₁` Lemma 5.5 provides one);
(5.17) is written with
`affineWaveAmplitudeOperator M κ = -(Id - 2P_κ)M` and
`oscillatoryTransverseProjection κ = Id - P_κ`; the solution in (ii) is any
`S5.TransverseSolution` (the solution is unique); `A₁`, `𝗉[A₁]` are the fields
`S5.leading`, `S5.leadingPressure` on `[t₀,T] × ℝ³ × ℝ` and their norm is the
weighted norm (D.1) of these fields; the seed is any `S5.IsSeed`;
`ℓ_* = 𝖣^{-a}` with `a ≥ a₀`. -/
def Statement.lemma_5_3 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ K : ℕ → ℝ,
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      let ℓ := S5.radius D a
      let h := S5.width lam
      let γ := S5.weight lam center
      let M := S5.strainField U X
      let κ := S5.waveVector X k
      let Sg := S5.envelopeSupport ℓ
      -- (5.19)
      (∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
        ∀ t ∈ Icc t₀ T, ∀ x : Vec3, ‖x‖ ≤ 2 * ℓ →
          ‖amp t x‖ ≤ 2 * ‖amp t 0‖ ∧ 0 < ⟪κ t x, M t x (amp t x)⟫_ℝ) ∧
      -- (i), (5.20)
      (∀ n : ℕ, ∀ V f : HierarchyTwistedProfile T k Vec3,
        (∀ x ∉ Sg, ∀ s, V.val.val.val (t₀, x, s) = 0) →
        (∀ t ∈ Icc t₀ T, ∀ x ∉ Sg, ∀ s, f.val.val.val (t, x, s) = 0) →
        (∀ t ∈ Icc t₀ T, ∀ x s, ⟪κ t x, V.val.val.val (t, x, s)⟫_ℝ = 0) →
        (∀ t ∈ Icc t₀ T, ∀ x s, HasDerivWithinAt (fun r => V.val.val.val (r, x, s))
          (affineWaveAmplitudeOperator (M t x) (κ t x) (V.val.val.val (t, x, s)) +
            oscillatoryTransverseProjection (κ t x) (f.val.val.val (t, x, s))) (Icc t₀ T) t) →
        S5.wNorm ℓ h t₀ γ n V ≤
          K n * D ^ C * ((γ t₀)⁻¹ * S5.launchNorm ℓ h t₀ n V + S5.wNorm ℓ h t₀ γ n f)) ∧
      -- (ii), (5.21)
      (∀ n : ℕ, ∀ (f V : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ),
        (S5.ops d).average f = 0 →
        (∀ t ∈ Icc 0 T, ∀ x s, t < t₀ ∨ x ∉ Sg → f.val.val.val (t, x, s) = 0) →
        S5.TransverseSolution d f V q →
        S5.wNorm ℓ h t₀ γ n V + lam * S5.wNorm ℓ h t₀ γ n q ≤ K n * D ^ C * S5.wNorm ℓ h t₀ γ n f) ∧
      -- (iii), (5.22)
      (∀ n : ℕ, ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
        S5.fieldNorm ℓ h (Icc t₀ T) (fun t => (γ t)⁻¹) n
            (fun t x => S5.leading ℓ h amp t x.1 x.2) +
          lam * S5.fieldNorm ℓ h (Icc t₀ T) (fun t => (γ t)⁻¹) n
            (fun t x => S5.leadingPressure U X k ℓ h amp t x.1 x.2) ≤
          K n * D ^ C * lam ^ (-5 / 4 : ℝ))

/-- **Proposition 5.4** (`cc:uf:hier:prop:identity`, sections/06c_finite_hierarchy.tex:304).
For every integer `P ≥ 2` the profiles obtained from (5.11), (5.27), (5.28) are
well defined (the seed of §5.1 exists, and the profiles exist and are unique), and
`W = ∑_{p=1}^P Z_p + C_{P+1} = ∑_{p=1}^P (V_p + C_{p+1} + B_p)`,
`𝖯 = ∑_{p=1}^P (𝗉_p + q̄_p)`, `q̄₁ = 0`, satisfy `𝐝̃·W = 0` and (5.29)
`W_t + MW + (W·𝐝̃)W + 𝐝̃𝖯 + R_U∘X = R_P + R_χ̃`. The oscillatory part
`W_osc = W - ⟨W⟩ = ∑_{p=1}^P (V_p + C_{p+1})` is supported in `supp g`, and so are
the sources `f_p + f_p^S`; `V_p`, `C_p`, `𝗉_p`, `f_p + f_p^S` vanish for `t < t₀`;
with `V_{P+1} = B_{P+1} = 0`, `Y_{P+1} = Z_{P+1} = C_{P+1}`; the remainder `R_P` of
(5.30) is independent of the phase at labels outside `supp g`; the construction is
jointly smooth.
Equations: (5.11), (5.25)–(5.30), (3.7), (3.8); latest indexing `C₁ = 0`,
`C_{p+1} = C[V_p]`.

Representation: the expansion is any family satisfying the defining recursions
(`S5.IsExpansion`), with `R = R_U∘X` and `S = χ̃'A₁` (`R_χ̃ = S + C[S]`); joint
smoothness is part of the profile type; the operators `∂_t + M`, `(·)·𝐝`,
`(·)·κ∂_s`, `𝐝`, `κ∂_s`, `⟨·⟩` are those of `S5.ops d`; `𝐝̃·` is
`S5.totalDivergence d`; "supported in `supp g`" means vanishing at labels outside
`S5.envelopeSupport ℓ_*`; uniqueness is stated for all profiles that enter `W`,
`𝖯`, `R_P`; the existence of the seed of §5.1 (`S5.IsSeed`: the solution of (3.2)
with (5.4) on `[t₀,T]`, jointly smooth), from which the profiles start through
`A₁ = g𝐚F_h`, is stated as part of the assertion that they are well defined (the
text defines the seed in §5.1 and does not state its existence separately; this
conjunct is recorded as an export of Proposition 5.4 in the ledger);
`ℓ_* = 𝖣^{-a}` with `a ≥ a₀`. -/
def Statement.proposition_5_4 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a →
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      -- the seed of §5.1, which gives `V₁`, `𝗉₁`, `C₂`, exists
      (∃ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp) ∧
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      let ℓ := S5.radius D a
      let h := S5.width lam
      let A := S5.ops d
      let Sg := S5.envelopeSupport ℓ
      -- the profiles are well defined: existence
      (∃ (R S : HierarchyTwistedProfile T k Vec3)
          (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ ℓ h amp P R S u) ∧
      -- and uniqueness
      (∀ (R S R' S' : HierarchyTwistedProfile T k Vec3)
          (u u' : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ ℓ h amp P R S u → S5.IsExpansion d pU χ ℓ h amp P R' S' u' →
        R = R' ∧ S = S' ∧
          (∀ i ∈ Finset.Icc 1 P, u.V i = u'.V i ∧ u.B i = u'.B i ∧ u.p i = u'.p i ∧ u.q i = u'.q i) ∧
          ∀ i ∈ Finset.Icc 1 (P + 1), S5.Cd u i = S5.Cd u' i) ∧
      -- the identities
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ ℓ h amp P R S u →
        let cS := S5.curlCorrection d S
        let W := S5.expansion u P
        let Pr := S5.expansionPressure u P
        let RP := S5.remainder A u P
        W = (∑ i ∈ Finset.Icc 1 P, S5.Zd u i) + S5.Cd u (P + 1) ∧
        S5.totalDivergence d W = 0 ∧
        -- (5.29)
        A.material W + A.labelAdv W W + A.phaseAdv W W + A.labelGrad Pr + A.phaseGrad Pr + R =
          RP + (S + cS) ∧
        W - A.average W = ∑ i ∈ Finset.Icc 1 P, (u.V i + S5.Cd u (i + 1)) ∧
        -- supports in `supp g`
        (∀ t ∈ Icc 0 T, ∀ x ∉ Sg, ∀ s, (W - A.average W).val.val.val (t, x, s) = 0) ∧
        (∀ i ∈ Finset.Icc 2 P, ∀ t ∈ Icc 0 T, ∀ x ∉ Sg, ∀ s,
          (S5.oscSource A u cS i + S5.suppSource A u i).val.val.val (t, x, s) = 0) ∧
        -- vanishing before activation
        (∀ t ∈ Icc 0 T, t < t₀ → ∀ x s,
          (∀ i ∈ Finset.Icc 1 P,
            (u.V i).val.val.val (t, x, s) = 0 ∧ (u.p i).val.val.val (t, x, s) = 0) ∧
          (∀ i ∈ Finset.Icc 1 (P + 1), (S5.Cd u i).val.val.val (t, x, s) = 0) ∧
          ∀ i ∈ Finset.Icc 2 P, (S5.oscSource A u cS i + S5.suppSource A u i).val.val.val (t, x, s) = 0) ∧
        -- `Y_{P+1} = Z_{P+1} = C_{P+1}`
        S5.Yd u (P + 1) = S5.Cd u (P + 1) ∧ S5.Zd u (P + 1) = S5.Cd u (P + 1) ∧
        -- `R_P` is independent of the phase outside `supp g`
        ∀ t ∈ Icc 0 T, ∀ x ∉ Sg, ∀ s, RP.val.val.val (t, x, s) = RP.val.val.val (t, x, 0)

/-- **Lemma 5.5** (`cc:uf:hier:lem:relay`, sections/06c_finite_hierarchy.tex:399).
There is an absolute exponent `C` such that, for every `n ≥ 0` and every field `V`
with `⟨V⟩ = 0`, `κ·V = 0`, (5.31) `‖C[V]‖_{[n],γ} ≤ C_n 𝖣^C λ^{-1} ‖V‖_{[n+1],γ}`;
if moreover `V_t + MV + κ∂_s𝗉 = f` with `⟨f⟩ = 0`, `⟨𝗉⟩ = 0`, then (5.32)
`‖(∂_t+M)C[V] + 𝐝𝗉‖_{[n],γ} ≤ C_n 𝖣^C λ^{-1}(‖V‖_{[n+1],γ} + ‖f‖_{[n+1],γ})`.
For the leading oscillation `V = A₁` on `[t₀,T]` the source is `f = 0`: `A₁` and
`𝗉 = 𝗉[A₁]` satisfy the hypotheses of (5.32) with `f = 0` (this is (3.4)), so
`‖(∂_t+M)C[A₁] + 𝐝𝗉[A₁]‖_{[n],γ} ≤ C_n 𝖣^C λ^{-1} ‖A₁‖_{[n+1],γ}`.
Equations: (5.31), (5.32), (3.4), (3.5).

Representation: `V`, `f`, `𝗉` are lattice-twisted profiles on `[0,T]`; the
transversality, the zero phase mean of `𝗉` and the equation are required on
`[t₀,T]`, where the weighted norm is taken, while `⟨V⟩ = 0` and `⟨f⟩ = 0` are
required on all of `[0,T]` (`A.average` is the phase average on the whole slab;
in every application the fields have zero phase mean at all times, and `C[·]`
only sees `V - ⟨V⟩`). The fields `A₁ = S5.leading`, `𝗉[A₁] = S5.leadingPressure`
of a seed (any `S5.IsSeed`) live on `[t₀,T]`; they enter as smooth twisted
profiles `V`, `q` on `[0,T]` whose values on `[t₀,T]` over the label cell
`[-1/2,1/2]³` are those of `A₁`, `𝗉[A₁]` (by the lattice twist this fixes them on
`[t₀,T]`), with `⟨V⟩ = 0` on `[0,T]`. The leading clause asserts that such
profiles exist and satisfy the hypotheses of (5.31) and (5.32) with `f = 0`
(the equation is (3.4)), and states (5.32) for them, whose source term then
vanishes; `ℓ_* = 𝖣^{-a}` with `a ≥ a₀`. -/
def Statement.lemma_5_5 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ K : ℕ → ℝ,
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      let ℓ := S5.radius D a
      let h := S5.width lam
      let γ := S5.weight lam center
      let A := S5.ops d
      let κ := S5.waveVector X k
      (∀ n : ℕ, ∀ V : HierarchyTwistedProfile T k Vec3, A.average V = 0 →
        (∀ t ∈ Icc t₀ T, ∀ x s, ⟪κ t x, V.val.val.val (t, x, s)⟫_ℝ = 0) →
        -- (5.31)
        S5.wNorm ℓ h t₀ γ n (S5.curlCorrection d V) ≤
            K n * D ^ C * lam⁻¹ * S5.wNorm ℓ h t₀ γ (n + 1) V ∧
        -- (5.32)
        ∀ (f : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ),
          A.average f = 0 →
          (∀ t ∈ Icc t₀ T, ∀ x, phaseMean (fun s => q.val.val.val (t, x, s)) = 0) →
          (∀ t ∈ Icc t₀ T, ∀ x s,
            (A.material V + A.phaseGrad q).val.val.val (t, x, s) = f.val.val.val (t, x, s)) →
          S5.wNorm ℓ h t₀ γ n (A.material (S5.curlCorrection d V) + A.labelGrad q) ≤
            K n * D ^ C * lam⁻¹ * (S5.wNorm ℓ h t₀ γ (n + 1) V + S5.wNorm ℓ h t₀ γ (n + 1) f)) ∧
      -- the leading oscillation `A₁` on `[t₀,T]`, with `𝗉[A₁]`, is admissible in (5.32)
      -- with source `f = 0` (this is (3.4)), and (5.32) holds for it without a source
      (∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
        ∃ (V : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ),
          (∀ t ∈ Icc t₀ T, ∀ x ∈ centeredCell, ∀ s,
            V.val.val.val (t, x, s) = S5.leading ℓ h amp t x s ∧
              q.val.val.val (t, x, s) = S5.leadingPressure U X k ℓ h amp t x s) ∧
          A.average V = 0 ∧
          (∀ t ∈ Icc t₀ T, ∀ x s, ⟪κ t x, V.val.val.val (t, x, s)⟫_ℝ = 0) ∧
          (∀ t ∈ Icc t₀ T, ∀ x, phaseMean (fun s => q.val.val.val (t, x, s)) = 0) ∧
          (∀ t ∈ Icc t₀ T, ∀ x s, (A.material V + A.phaseGrad q).val.val.val (t, x, s) = 0) ∧
          ∀ n : ℕ, S5.wNorm ℓ h t₀ γ n (A.material (S5.curlCorrection d V) + A.labelGrad q) ≤
            K n * D ^ C * lam⁻¹ * S5.wNorm ℓ h t₀ γ (n + 1) V)

/-- **Theorem 5.6** (`cc:uf:hier:thm:depth`, sections/06c_finite_hierarchy.tex:469).
There is an absolute exponent `C` such that, if `𝖣^C λ^{-1/12} ≤ 1`, the
construction satisfies for all `n ≥ 0` and `p ≥ 2`: (5.34)
`‖V_p‖_{[n],γ} + ‖f_p + f_p^S‖_{[n],γ} + λ‖𝗉_p‖_{[n],γ} ≤ C_{n,p} 𝖣^C λ^{-5/4} λ^{-2(p-1)/3}`,
(5.35) `‖B_p‖_{[n]} + ‖f̄_p‖_{[n]} ≤ C_{n,p} 𝖣^C λ^{-5/2} λ^{-2(p-2)/3}`,
(5.36) `‖C_{p+1}‖_{[n],γ} ≤ C_{n,p} 𝖣^C λ^{-9/4} λ^{-2(p-1)/3}`; (5.34) and (5.36)
also hold for `p = 1` with `f₁ = f₁^S = 0`; and the expansion of depth `P ≥ 2`
satisfies for all `m ≥ 0` (5.37) `‖W_osc‖_{[m],γ} ≤ C_{m,P} 𝖣^C λ^{-5/4}`,
`‖∑_{p=2}^P B_p‖_{[m]} + ‖∑_{p=2}^P f̄_p‖_{[m]} ≤ C_{m,P} 𝖣^C λ^{-5/2}`, and (5.38)
`‖R_P‖_{[m]} ≤ C_{m,P} λ^{-5/4} λ^{-2P/3}`.
Equations: (5.34)–(5.38); latest indexing `C_{p+1} = C[V_p]` in (5.36).

Representation: "the construction" is any expansion of depth `P` in predicate form
(`S5.IsExpansion`), and the level bounds are stated for `p ≤ P` with constants
`C_{n,p}` independent of `P` (the levels do not depend on the depth);
`‖·‖_{[n],γ}`, `‖·‖_{[n]}` are `S5.wNorm`, `S5.uNorm`; `W_osc = W - ⟨W⟩`;
`ℓ_* = 𝖣^{-a}` with `a ≥ a₀`, and the exponent `C` depends on the absolute `a`. -/
def Statement.theorem_5_6 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ K : ℕ → ℕ → ℝ, ∃ KP : ℕ → ℕ → ℝ,
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      D ^ C * lam ^ (-1 / 12 : ℝ) ≤ 1 →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        let ℓ := S5.radius D a
        let h := S5.width lam
        let γ := S5.weight lam center
        let A := S5.ops d
        let cS := S5.curlCorrection d S
        let W := S5.expansion u P
        -- (5.34), `p = 1`
        (∀ n : ℕ, S5.wNorm ℓ h t₀ γ n (u.V 1) + lam * S5.wNorm ℓ h t₀ γ n (u.p 1) ≤
          K n 1 * D ^ C * lam ^ (-5 / 4 : ℝ)) ∧
        -- (5.34), `p ≥ 2`
        (∀ n : ℕ, ∀ p ∈ Finset.Icc 2 P,
          S5.wNorm ℓ h t₀ γ n (u.V p) +
              S5.wNorm ℓ h t₀ γ n (S5.oscSource A u cS p + S5.suppSource A u p) +
              lam * S5.wNorm ℓ h t₀ γ n (u.p p) ≤
            K n p * D ^ C * lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3)) ∧
        -- (5.35)
        (∀ n : ℕ, ∀ p ∈ Finset.Icc 2 P,
          S5.uNorm ℓ h n (u.B p) + S5.uNorm ℓ h n (S5.meanSource A u cS R p) ≤
            K n p * D ^ C * lam ^ (-5 / 2 : ℝ) * lam ^ (-2 * ((p : ℝ) - 2) / 3)) ∧
        -- (5.36), `p ≥ 1`
        (∀ n : ℕ, ∀ p ∈ Finset.Icc 1 P,
          S5.wNorm ℓ h t₀ γ n (S5.Cd u (p + 1)) ≤
            K n p * D ^ C * lam ^ (-9 / 4 : ℝ) * lam ^ (-2 * ((p : ℝ) - 1) / 3)) ∧
        -- (5.37)
        (∀ m : ℕ,
          S5.wNorm ℓ h t₀ γ m (W - A.average W) ≤ KP m P * D ^ C * lam ^ (-5 / 4 : ℝ) ∧
          S5.uNorm ℓ h m (∑ p ∈ Finset.Icc 2 P, u.B p) +
              S5.uNorm ℓ h m (∑ p ∈ Finset.Icc 2 P, S5.meanSource A u cS R p) ≤
            KP m P * D ^ C * lam ^ (-5 / 2 : ℝ)) ∧
        -- (5.38)
        ∀ m : ℕ, S5.uNorm ℓ h m (S5.remainder A u P) ≤
          KP m P * lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)

/-- **Lemma 5.7** (`cc:uf:hier:lem:physical`, sections/08_exact_wave.tex:32).
Let `g₀(t,a,s)` be smooth and independent of the phase at labels outside
`supp g`, with phase average extending periodically. There is an absolute exponent
`C` such that for every `m ≥ 0` and `t ∈ [t₀,T]`, (5.44)
`∑_{|β|=m} ‖∂_x^β g₀^♮(t)‖_∞ ≤ C_m (𝖣^C λ^{3/2})^m γ(t) ‖g₀‖_{[m],γ}` and (5.45)
`‖g₀^♮(t)‖_{C^{m,1/2}} ≤ C_m (𝖣^C λ^{3/2})^{m+1} γ(t) ‖g₀‖_{[m+1],γ}`. Both bounds
also hold on `[0,T]` with `γ` replaced by one, and for a phase-independent field
with `𝖣^C λ^{3/2}` replaced by `𝖣^C`.
Equations: (5.44), (5.45), (3.1).

Representation: `g₀` is a lattice-twisted profile (this encodes the periodic
extension across the cell faces) with values in any real normed space;
`g₀^♮(t,x) = g₀(t, X(t,·)⁻¹(x), k_*·X(t,·)⁻¹(x))` is `graphRead (fun t => X t 0) g₀`;
the multi-index sum is bounded by the sum over ordered derivative words
`∑_{i : Fin m → Fin 3} sup |∂_{i₁}⋯∂_{iₘ} g₀^♮(t)|`; `C^{m,1/2}` is
`SpatialHolderHalf m` with `spatialHolderHalfNorm m`; `ℓ_* = 𝖣^{-a}` with
`a ≥ a₀`. -/
def Statement.lemma_5_7 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ C : ℕ, ∃ K : ℕ → ℝ,
    ∀ {T : ℝ} (_hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3},
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g₀ : HierarchyTwistedProfile T k E),
      let ℓ := S5.radius D a
      let h := S5.width lam
      let γ := S5.weight lam center
      (∀ t ∈ Icc 0 T, ∀ x ∉ S5.envelopeSupport ℓ, ∀ s,
        g₀.val.val.val (t, x, s) = g₀.val.val.val (t, x, 0)) →
      let F := graphRead (fun t => X t 0) g₀
      let bound := fun (Λ₁ γt : ℝ) (N : ℕ → ℝ) (m : ℕ) (t : ℝ) =>
        (∑ i : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) (F t))) ≤
            K m * Λ₁ ^ m * γt * N m ∧
          SpatialHolderHalf m (F t) ∧
          spatialHolderHalfNorm m (F t) ≤ K m * Λ₁ ^ (m + 1) * γt * N (m + 1)
      -- (5.44), (5.45) on `[t₀,T]`
      (∀ m : ℕ, ∀ t ∈ Icc t₀ T,
        bound (D ^ C * lam ^ (3 / 2 : ℝ)) (γ t) (fun n => S5.wNorm ℓ h t₀ γ n g₀) m t) ∧
      -- on `[0,T]` with `γ` replaced by one
      (∀ m : ℕ, ∀ t ∈ Icc 0 T,
        bound (D ^ C * lam ^ (3 / 2 : ℝ)) 1 (fun n => S5.uNorm ℓ h n g₀) m t) ∧
      -- phase-independent fields
      ((∀ t ∈ Icc 0 T, ∀ x s, g₀.val.val.val (t, x, s) = g₀.val.val.val (t, x, 0)) →
        (∀ m : ℕ, ∀ t ∈ Icc t₀ T, bound (D ^ C) (γ t) (fun n => S5.wNorm ℓ h t₀ γ n g₀) m t) ∧
        ∀ m : ℕ, ∀ t ∈ Icc 0 T, bound (D ^ C) 1 (fun n => S5.uNorm ℓ h n g₀) m t)

/-- **Lemma 5.8** (`cc:uf:step:lem:approximate`, sections/08_exact_wave.tex:82).
With `V = U + W^♮`, `Π = p_U + 𝖯^♮` for the expansion of depth `P ≥ 2`,
`C_step = Γ_P 𝖣^b` and (5.43) `C_step λ^{-1/12} ≤ 1`: `V` is smooth, odd and
divergence free, `Π` is smooth, (5.46) `V_t + V·∇V + ∇Π = R_V = R_P^♮ + R_χ̃^♮`,
(5.47) `‖W_osc^♮‖_{C_tL^∞} ≤ C_{0,P} 𝖣^b λ^{-5/4}` and, for every `m ≥ 0`, (5.48)
`‖W_osc^♮‖_{C_tC^{m,1/2}} ≤ C_{m,P} 𝖣^{b(m+2)} λ^{3(m+1)/2-5/4}`,
`‖W̄^♮‖_{C_tC^{m,1/2}} ≤ C_{m,P} 𝖣^{b(m+2)} λ^{-5/2}`,
`‖R_V‖_{C_tC^{1,1/2}} ≤ C_step λ² (λ^{-2P/3} + ‖χ̃'γ‖_{∞,[t₀,T]})`.
Equations: (5.43), (5.46)–(5.48), (5.29), (5.30), (3.8).

Representation: the expansion is any `S5.IsExpansion` (`R_χ̃ = S + C[S]`);
`f^♮ = graphRead (fun t => X t 0) f`; `W̄ = ∑_{p=2}^P B_p`; time norms `C_t` are
bounds at every `t ∈ [0,T]`; `C^{m,1/2}` is `SpatialHolderHalf m` with
`spatialHolderHalfNorm m`; smoothness is joint on `[0,T] × ℝ³` with spatial
periodicity; `‖χ̃'γ‖_{∞,[t₀,T]}` is `χ.derivativeSize γ`; `b` and `Γ_P` are
sufficiently large (`∀ b ≥ b₀`, `∀ Γ ≥ Γ₀`), the constants `C_{m,P}` are fixed
before them; `ℓ_* = 𝖣^{-a}` with `a ≥ a₀`. -/
def Statement.lemma_5_8 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ b₀ : ℕ, ∃ Γ₀ : ℕ → ℝ, ∃ K : ℕ → ℕ → ℝ,
    ∀ b : ℕ, b₀ ≤ b → ∀ Γ : ℕ → ℝ, (∀ P, Γ₀ P ≤ Γ P) →
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        Γ P * D ^ b * lam ^ (-1 / 12 : ℝ) ≤ 1 →
        let γ := S5.weight lam center
        let A := S5.ops d
        let Y : Velocity := fun t => X t 0
        let W := S5.expansion u P
        let V : Velocity := U + graphRead Y W
        let Pres : Pressure := pU + graphRead Y (S5.expansionPressure u P)
        let RV : Velocity :=
          graphRead Y (S5.remainder A u P + (S + S5.curlCorrection d S))
        let Wosc := graphRead Y (W - A.average W)
        let Wbar := graphRead Y (∑ p ∈ Finset.Icc 2 P, u.B p)
        (ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
          ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t) ∧ Function.Odd (V t) ∧
            ∀ x, divergence (V t) x = 0) ∧
        (ContDiffOn ℝ ∞ (Function.uncurry Pres) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
          ∀ t ∈ Icc 0 T, SpatiallyPeriodic (Pres t)) ∧
        -- (5.46)
        (∀ t ∈ Icc 0 T, ∀ x, momentumResidual (Icc 0 T) V Pres t x = RV t x) ∧
        -- (5.47)
        (∀ t ∈ Icc 0 T, ∀ x, ‖Wosc t x‖ ≤ K 0 P * D ^ b * lam ^ (-5 / 4 : ℝ)) ∧
        -- (5.48)
        (∀ m : ℕ, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (Wosc t) ∧
          spatialHolderHalfNorm m (Wosc t) ≤
            K m P * D ^ (b * (m + 2)) * lam ^ ((3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4)) ∧
        (∀ m : ℕ, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (Wbar t) ∧
          spatialHolderHalfNorm m (Wbar t) ≤ K m P * D ^ (b * (m + 2)) * lam ^ (-5 / 2 : ℝ)) ∧
        ∀ t ∈ Icc 0 T, SpatialHolderHalf 1 (RV t) ∧
          spatialHolderHalfNorm 1 (RV t) ≤
            Γ P * D ^ b * lam ^ (2 : ℝ) * (lam ^ (-2 * (P : ℝ) / 3) + χ.derivativeSize γ)

/-- **Lemma 5.9** (`cc:uf:step:lem:pressure-center`, sections/08_exact_wave.tex:158).
On `[0,T] × 𝕋³`, (5.49) `D_x²𝖯^♮ ≤ C_step λ^{-1/4} Id`; at `x = 0`, for
`t₀ ≤ t ≤ T`, (5.50) `∇V(t,0) = ∇U(t,0) + χ̃(t) 𝐚(t,0) ⊗ κ(t,0) + E_c(t)` with
`|E_c| ≤ λ^{-1/3}`.
Equations: (5.43), (5.49), (5.50).

Representation: as in Lemma 5.8; the quadratic-form inequality is
`⟪v, D²𝖯^♮ v⟫ ≤ C_step λ^{-1/4} |v|²` with `D²` the derivative of the gradient;
`∇V(t,0)` is the derivative `fderiv ℝ (V t) 0`, `𝐚 ⊗ κ` is the rank-one map
`v ↦ (κ·v) 𝐚` (`InnerProductSpace.rankOne`), `𝐚(t,0)` is the central seed, and
`E_c` is the difference, bounded in operator norm. -/
def Statement.lemma_5_9 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ b₀ : ℕ, ∃ Γ₀ : ℕ → ℝ,
    ∀ b : ℕ, b₀ ≤ b → ∀ Γ : ℕ → ℝ, (∀ P, Γ₀ P ≤ Γ P) →
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        Γ P * D ^ b * lam ^ (-1 / 12 : ℝ) ≤ 1 →
        let Y : Velocity := fun t => X t 0
        let V : Velocity := U + graphRead Y (S5.expansion u P)
        let Pnat : Pressure := graphRead Y (S5.expansionPressure u P)
        -- (5.49)
        (∀ t ∈ Icc 0 T, ∀ x v : Vec3,
          ⟪v, fderiv ℝ (gradient (Pnat t)) x v⟫_ℝ ≤ Γ P * D ^ b * lam ^ (-1 / 4 : ℝ) * ‖v‖ ^ 2) ∧
        -- (5.50)
        ∀ t ∈ Icc t₀ T,
          ‖fderiv ℝ (V t) 0 - fderiv ℝ (U t) 0 -
              χ.value t • InnerProductSpace.rankOne ℝ (center t) (S5.waveVector X k t 0)‖ ≤
            lam ^ (-1 / 3 : ℝ)

/-- **Lemma 5.10** (`cc:uf:step:lem:flow-bounds`, sections/08_exact_wave.tex:290).
Let `v` be a smooth divergence-free field on `[0,T] × 𝕋³` with
`‖v‖_{C_tC²} ≤ λ^{-5/2}`. The flow `Y` of `V + v` from time zero satisfies (5.53)
`sup |(D_aY)^{±1}| ≤ C_step λ^{1/4}`.
Equations: (5.43), (5.53).

Representation: as in Lemma 5.8; the hypothesis on `v` is a bound on each
derivative of order `j ≤ 2` (implied by the `C²` norm bound); the flow exists
(`DeformationOn` records the flow from every initial time, its lattice
equivariance and the bounds), and every label flow `Y` of `V + v` on `[0,T]`
satisfies the bounds, with `D_aY(t,a) = fderiv ℝ (Y 0 t) a` and
`(D_aY)⁻¹` read at `x = Y(t,a)` as `fderiv ℝ (Y t 0) x`. -/
def Statement.lemma_5_10 : Prop :=
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ b₀ : ℕ, ∃ Γ₀ : ℕ → ℝ,
    ∀ b : ℕ, b₀ ≤ b → ∀ Γ : ℕ → ℝ, (∀ P, Γ₀ P ≤ Γ P) →
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        Γ P * D ^ b * lam ^ (-1 / 12 : ℝ) ≤ 1 →
        let V : Velocity := U + graphRead (fun t => X t 0) (S5.expansion u P)
        let Cflow := Γ P * D ^ b * lam ^ (1 / 4 : ℝ)
        ∀ v : Velocity, ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, SpatiallyPeriodic (v t)) →
          (∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0) →
          (∀ t ∈ Icc 0 T, ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (v t) x‖ ≤ lam ^ (-5 / 2 : ℝ)) →
          (∃ Yf : ℝ → Velocity, DeformationOn (V + v) Yf T Cflow) ∧
          ∀ Yf : ℝ → Velocity, IsLabelFlowOn (V + v) Yf (Icc 0 T) →
            ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (Yf 0 t) x‖ ≤ Cflow ∧ ‖fderiv ℝ (Yf t 0) x‖ ≤ Cflow

/-- **Proposition 5.11** (`cc:uf:step:thm:step`, sections/08_exact_wave.tex:379).
Let `Λ ≥ 1` and put (5.55) `u = S_Λ V`, `v_Λ = u - V`,
`ε_Λ = Λ^{2-P}(1 + ‖V‖_{C_tC^{P,1/2}})²`; let `p` be the zero-mean function with
`Δp = -tr((∇u)²)` and `R_u = u_t + u·∇u + ∇p`. Then `u` is smooth, odd,
divergence free and supported on frequencies at most `2Λ`; `R_u` is odd,
divergence free and supported on frequencies at most `4Λ`; (5.56)
`‖v_Λ‖_{C_tC^{2,1/2}} ≤ C_{2,P} ε_Λ`,
`‖R_u‖_{C_tC^{1,1/2}} + ‖D²(p-Π)‖_{C_tC^{0,1/2}} ≤ C‖R_V‖_{C_tC^{1,1/2}} + C_{2,P} ε_Λ`;
and (5.57) `D²(p - p_U) ≤ (C_step λ^{-1/4} + C‖R_V‖_{C_tC^{1,1/2}} + C_{2,P} ε_Λ) Id`
on `[0,T] × 𝕋³`.
Equations: (5.43), (5.55)–(5.57).

Representation: as in Lemma 5.8; the cutoff symbol `ψ` of Appendix B is any
`S5.CutoffSymbol` and the constants depend on it; `u` and `p` are any fields with
`S5.IsTruncation` (they exist, and the definitions determine them); `C_tC^{m,1/2}`
norms on the left are bounds at every time with `SpatialHolderHalf` (for the sum
in (5.56) at every pair of times, i.e. the sum of the two time suprema), and on the
right are `slabSpatialHolderHalfNorm` (the time supremum); "supported on
frequencies at most `Λ`" is `RealTorusFourierBand Λ` of the torus field;
`D²(p - Π)` is `fderiv ℝ (gradient (p t - Π t))`. -/
def Statement.proposition_5_11 : Prop :=
  ∀ ψ : Vec3 → ℝ, S5.CutoffSymbol ψ →
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ b₀ : ℕ, ∃ Γ₀ : ℕ → ℝ, ∃ (C : ℝ) (K : ℕ → ℝ),
    ∀ b : ℕ, b₀ ≤ b → ∀ Γ : ℕ → ℝ, (∀ P, Γ₀ P ≤ Γ P) →
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (w : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S w →
        Γ P * D ^ b * lam ^ (-1 / 12 : ℝ) ≤ 1 →
        ∀ Λ : ℝ, 1 ≤ Λ →
        let Y : Velocity := fun t => X t 0
        let V : Velocity := U + graphRead Y (S5.expansion w P)
        let Pres : Pressure := pU + graphRead Y (S5.expansionPressure w P)
        let RV : Velocity := graphRead Y (S5.remainder (S5.ops d) w P + (S + S5.curlCorrection d S))
        let ε := Λ ^ ((2 : ℤ) - P) * (1 + slabSpatialHolderHalfNorm T P V) ^ 2
        let e := C * slabSpatialHolderHalfNorm T 1 RV + K P * ε
        (∃ (u : Velocity) (p : Pressure), S5.IsTruncation T ψ Λ V u p) ∧
        ∀ (u : Velocity) (p : Pressure), S5.IsTruncation T ψ Λ V u p →
          let Ru := momentumResidual (Icc 0 T) u p
          -- `u` smooth, odd, divergence free, frequencies at most `2Λ`
          (ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
            ∀ t ∈ Icc 0 T, Function.Odd (u t) ∧ (∀ x, divergence (u t) x = 0) ∧
              ∃ c : C(UnitAddTorus (Fin 3), Vec3),
                (∀ x, c (toUnitTorus x) = u t x) ∧ RealTorusFourierBand (2 * Λ) c) ∧
          -- `R_u` odd, divergence free, frequencies at most `4Λ`
          (∀ t ∈ Icc 0 T, Function.Odd (Ru t) ∧ (∀ x, divergence (Ru t) x = 0) ∧
            ∃ c : C(UnitAddTorus (Fin 3), Vec3),
              (∀ x, c (toUnitTorus x) = Ru t x) ∧ RealTorusFourierBand (4 * Λ) c) ∧
          -- (5.56)
          (∀ t ∈ Icc 0 T, SpatialHolderHalf 2 (u t - V t) ∧
            spatialHolderHalfNorm 2 (u t - V t) ≤ K P * ε) ∧
          (∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, SpatialHolderHalf 1 (Ru t) ∧
            SpatialHolderHalf 0 (fderiv ℝ (gradient (p t' - Pres t'))) ∧
            spatialHolderHalfNorm 1 (Ru t) +
                spatialHolderHalfNorm 0 (fderiv ℝ (gradient (p t' - Pres t'))) ≤ e) ∧
          -- (5.57)
          ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
            ⟪v, fderiv ℝ (gradient (p t - pU t)) x v⟫_ℝ ≤
              (Γ P * D ^ b * lam ^ (-1 / 4 : ℝ) + e) * ‖v‖ ^ 2

/-- **Display (5.59)** (`cc:holder:product-growth`, sections/08_exact_wave.tex:426, in the
proof of Proposition 5.11). For every integer `m ≥ 0`,
`‖fg‖_{C^{m,1/2}} ≤ C_m ‖f‖_{C^{m,1/2}} ‖g‖_{C^{m,1/2}}`.
Equation: (5.59).

Representation: the product `fg` is any continuous bilinear product
`B : E →L F →L G` of fields `f : ℝ³ → E`, `g : ℝ³ → F` (scalar, vector and tensor
products), and the constant is `C_m ‖B‖`; `C^{m,1/2}` is `SpatialHolderHalf m`
with `spatialHolderHalfNorm m` (on periodic fields it is the norm on `𝕋³`). -/
def Statement.Text.eq_5_59 : Prop :=
  ∀ m : ℕ, ∃ Cm : ℝ, 0 ≤ Cm ∧
    ∀ {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
      (B : E →L[ℝ] F →L[ℝ] G) (f : Vec3 → E) (g : Vec3 → F),
      SpatialHolderHalf m f → SpatialHolderHalf m g →
        SpatialHolderHalf m (fun x => B (f x) (g x)) ∧
          spatialHolderHalfNorm m (fun x => B (f x) (g x)) ≤
            Cm * ‖B‖ * spatialHolderHalfNorm m f * spatialHolderHalfNorm m g

end

end TorusEuler.Paper
