import TorusEuler.Paper.S5.Statements

/-! # Instances of the Section 5 statements at fixed constants (package S678a)

Mechanical copies of the bodies of `Statement.proposition_5_4`, `lemma_5_8`, `lemma_5_9`,
`lemma_5_10` and `proposition_5_11` after the existential constants
(`S5/Statements.lean:211-625`), so that the step lemmas of row 7.1 can take "the statement at the
chosen constants" as one hypothesis `Body.. a b Γ ..`. The `split..` theorems are the definitional
unfoldings of the statements (no content). Row 7.1 (sections/08b_induction.tex:376-461) applies
them to the data of step `j`. -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler HierarchyTwistedProfile LocalizedAmplitude ChildFlow

noncomputable section

/-- Body of `Statement.proposition_5_4` after the constants (generated copy). -/
def Body54 (a : ℕ) : Prop :=
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

/-- The statement of Proposition 5.4 read as the family `Body54 a` (unfolding, no content). -/
theorem split54 (h : Statement.proposition_5_4) : ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → Body54 a := h

/-- Body of `Statement.lemma_5_8` after the constants (generated copy). -/
def Body58 (a b : ℕ) (Γ : ℕ → ℝ) (K : ℕ → ℕ → ℝ) : Prop :=
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

/-- The statement of Lemma 5.8 read as the family of `Body58` (unfolding, no content). -/
theorem split58 (h : Statement.lemma_5_8) : ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ b₀ : ℕ, ∃ Γ₀ : ℕ → ℝ, ∃ K : ℕ → ℕ → ℝ,
    ∀ b : ℕ, b₀ ≤ b → ∀ Γ : ℕ → ℝ, (∀ P, Γ₀ P ≤ Γ P) → Body58 a b Γ K := h

/-- Body of `Statement.lemma_5_9` after the constants (generated copy). -/
def Body59 (a b : ℕ) (Γ : ℕ → ℝ) : Prop :=
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

/-- The statement of Lemma 5.9 read as the family of `Body59` (unfolding the definition, no content). -/
theorem split59 (h : Statement.lemma_5_9) : ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ b₀ : ℕ, ∃ Γ₀ : ℕ → ℝ,
    ∀ b : ℕ, b₀ ≤ b → ∀ Γ : ℕ → ℝ, (∀ P, Γ₀ P ≤ Γ P) → Body59 a b Γ := h

/-- Body of `Statement.lemma_5_10` after the constants (generated copy). -/
def Body510 (a b : ℕ) (Γ : ℕ → ℝ) : Prop :=
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

/-- The statement of Lemma 5.10 read as the family of `Body510` (unfolding, no content). -/
theorem split510 (h : Statement.lemma_5_10) : ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ b₀ : ℕ, ∃ Γ₀ : ℕ → ℝ,
    ∀ b : ℕ, b₀ ≤ b → ∀ Γ : ℕ → ℝ, (∀ P, Γ₀ P ≤ Γ P) → Body510 a b Γ := h

/-- Body of `Statement.proposition_5_11` after the constants (generated copy). -/
def Body511 (ψ : Vec3 → ℝ) (a b : ℕ) (Γ : ℕ → ℝ) (C : ℝ) (K : ℕ → ℝ) : Prop :=
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

/-- The statement of Proposition 5.11 read as the family of `Body511` (unfolding, no content). -/
theorem split511 (h : Statement.proposition_5_11) : ∀ ψ : Vec3 → ℝ, S5.CutoffSymbol ψ →
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ b₀ : ℕ, ∃ Γ₀ : ℕ → ℝ, ∃ (C : ℝ) (K : ℕ → ℝ),
    ∀ b : ℕ, b₀ ≤ b → ∀ Γ : ℕ → ℝ, (∀ P, Γ₀ P ≤ Γ P) → Body511 ψ a b Γ C K := h


end

end TorusEuler.Paper.Lib.S678a
