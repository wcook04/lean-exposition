import TorusEuler.Paper.Proofs.S678a.Library.ChildBounds
import TorusEuler.TruncatedParentAdmissibility
import TorusEuler.TruncatedParentPoissonPressure
import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.S5Bridge.Norms
import TorusEuler.Paper.Proofs.S5Bridge.Children
import TorusEuler.Paper.Proofs.S5Bridge.Operators
import TorusEuler.Paper.Proofs.S5Bridge.Leading
import TorusEuler.Paper.Proofs.S5Bridge.Library.Wrap
import TorusEuler.PaperPhysicalCutoff

/-! # Per-step input of the cutoff child (package S678a), part 1

Own glue of row 7.1 (items 4-6 of the proof, sections/08b_induction.tex:376-381, :415-421, :463-470):

* `isTruncation_of_cutoffChild`: the cutoff child is a truncation in the sense of Section 5.7
  (`S5.IsTruncation`), so Proposition 5.11 (`h5_11`) applies to it (copy of
  `Bridge.isTruncation_of_stage` for `CutoffChild`).
* `tails_of_lemma_B_1`: the tail bounds `hTails`, `hTailTwo` of the cutoff child from (B.2) of the
  real block of Lemma B.1 (`hB_1`).
* `scheduled_bounds_of_5_11`: the bounds of Proposition 5.11, (5.56)-(5.57) at slab
  suprema, turned into the per-time bounds `C next^(-7/2) + next^(-5)` of `scheduled_T2_T3'`, with
  the size bounds (5.47) of Lemma 5.8 and the truncation-error budget; the C^2 bound of (5.56) and (5.57) give `hTwo`, `hPress57`. -/

open Set
open scoped ContDiff InnerProductSpace

local notation "Labels" => UnitAddTorus (Fin 3)

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler

noncomputable section

/-- The cutoff child is a truncation in the sense of Section 5.7: copy of
`Bridge.isTruncation_of_stage` (S5Bridge/Children.lean:44) for `CutoffChild`. -/
theorem isTruncation_of_cutoffChild {T Λ : ℝ} {ψ : Vec3 → ℝ} {V : Velocity}
    (s : CutoffChild T Λ ψ V) : S5.IsTruncation T ψ Λ V s.velocity s.pressure where
  cutoff := fun t ht c hc x => by
    have hceq : c = s.approximateTorus t :=
      Bridge.torusField_eq_of_lift fun y => (hc y).trans (s.approximate_rep t ht y).symm
    rw [hceq]
    exact s.cutoff t (toUnitTorus x)
  pressure_smooth := fun t ht => contDiff_slice' s.smooth_pressure ht
  pressure_periodic := s.periodic_pressure
  pressure_mean_zero := s.mean_zero_pressure
  poisson := s.poisson

/-- The half-Hölder norm of a field and of its negative agree, and membership transfers. -/
theorem spatialHolderHalf_neg {m : ℕ} {f : Vec3 → Vec3} (hf : SpatialHolderHalf m f) :
    SpatialHolderHalf m (fun x => -f x) ∧
      spatialHolderHalfNorm m (fun x => -f x) = spatialHolderHalfNorm m f := by
  have hit (j : ℕ) : iteratedFDeriv ℝ j (fun x => -f x) = fun x => -iteratedFDeriv ℝ j f x := by
    funext x
    exact iteratedFDeriv_neg_apply (i := j) (f := f) (x := x)
  have hsup (j : ℕ) : spatialSupNorm (iteratedFDeriv ℝ j (fun x => -f x)) =
      spatialSupNorm (iteratedFDeriv ℝ j f) := by
    rw [hit]
    simp only [spatialSupNorm, norm_neg]
  have hquot (j : ℕ) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j (fun x => -f x)) p =
        spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) p := by
    rw [hit]
    simp only [spatialHolderHalfQuotient, ← neg_sub', norm_neg]
  have hsem (j : ℕ) : spatialHolderHalfSeminorm (iteratedFDeriv ℝ j (fun x => -f x)) =
      spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) := by
    simp only [spatialHolderHalfSeminorm, hquot]
  refine ⟨⟨hf.1.neg, fun j hj => ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := hf.2 j hj
    refine ⟨?_, ?_⟩
    · rw [hit]
      simpa only [norm_neg] using h1
    · have : spatialHolderHalfQuotient (iteratedFDeriv ℝ j (fun x => -f x)) =
          spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) := funext (hquot j)
      rw [this]
      exact h2
  · unfold spatialHolderHalfNorm
    exact Finset.sum_congr rfl fun j _ => by rw [hsup, hsem]

/-- The half-Hölder norm is nonnegative (copy of `spatialHolderHalfNorm_nonneg`,
S5b/Lemma58C4.lean:27, a generic fact). -/
theorem holderNorm_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ)
    (f : Vec3 → E) : 0 ≤ spatialHolderHalfNorm m f :=
  Finset.sum_nonneg fun _ _ => add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))

/-- **The tail bounds of the cutoff child** (Lemma B.1, (B.2), real block, sections/appB_cutoff.tex;
used at sections/08b_induction.tex:450): for a fixed symbol there are constants `Ct M ≥ 0` such that
the child `s.velocity = S_Λ V` of a field `V t` of class `C^{M,1/2}` satisfies, for `m ≤ M`,
`‖s.velocity t - V t‖_{C^{m,1/2}} ≤ Ct M Λ^{m-M} ‖V t‖_{C^{M,1/2}}`. Uses `hB1`. -/
theorem tails_of_lemma_B_1 (hB1 : Statement.lemma_B_1) {ψ : Vec3 → ℝ} (hψ : S5.CutoffSymbol ψ) :
    ∃ Ct : ℕ → ℝ, (∀ M, 0 ≤ Ct M) ∧ ∀ {T Λ : ℝ}, 0 < Λ → ∀ {V : Velocity}
      (s : CutoffChild T Λ ψ V) (M : ℕ), (∀ t ∈ Icc 0 T, SpatialHolderHalf M (V t)) →
      ∀ m ≤ M, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (s.velocity t - V t) ∧
        spatialHolderHalfNorm m (s.velocity t - V t) ≤
          Ct M * Λ ^ ((m : ℤ) - M) * spatialHolderHalfNorm M (V t) := by
  obtain ⟨Cop, Cb, Ct, _, _, hCt, h⟩ := hB1 ψ (Bridge.cutoffSymbol_appendixB hψ)
  refine ⟨Ct, hCt, fun {T Λ} hΛ {V} s M hV m hm t ht => ?_⟩
  obtain ⟨_, hreal, _⟩ := h Λ hΛ
  obtain ⟨_, _, _, _, _, _, _, _, hB2⟩ := hreal
  have hg : SpatialHolderHalf M (fun x => s.approximateTorus t (toUnitTorus x)) := by
    have : (fun x => s.approximateTorus t (toUnitTorus x)) = V t :=
      funext (s.approximate_rep t ht)
    rw [this]
    exact hV t ht
  obtain ⟨h1, h2⟩ := hB2 M m hm (s.approximateTorus t) hg
  have hfun : (fun x => s.approximateTorus t (toUnitTorus x) -
        realVectorFourierCutoff ψ Λ (s.approximateTorus t) (toUnitTorus x)) =
      fun x => V t x - s.velocity t x := by
    funext x
    rw [s.approximate_rep t ht x]
    exact congrArg (fun w => V t x - w) (s.cutoff t (toUnitTorus x)).symm
  have hneg : s.velocity t - V t = fun x => -(V t x - s.velocity t x) := by
    funext x
    simp
  rw [hfun] at h1 h2
  obtain ⟨h3, h4⟩ := spatialHolderHalf_neg h1
  rw [hneg]
  refine ⟨h3, ?_⟩
  rw [h4]
  have hV' : (fun x => s.approximateTorus t (toUnitTorus x)) = V t := funext (s.approximate_rep t ht)
  rwa [hV'] at h2

/-- The second-order tail `hTailTwo` of the cutoff child: `‖s.velocity t - V t‖_{C^{2,1/2}} ≤
Ct P · truncErr` (the case `m = 2`, `M = P ≥ 2` of `tails_of_lemma_B_1`, with `‖V‖ ≤ (1+‖V‖)²`). -/
theorem tailTwo_of_tails {Ct Λ : ℝ} {T : ℝ} {ψ : Vec3 → ℝ} {V : Velocity} (hCt : 0 ≤ Ct)
    (hΛ : 0 < Λ) (s : CutoffChild T Λ ψ V) {P : ℕ} (hP : 2 ≤ P)
    (hTails : ∀ m ≤ P, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (s.velocity t - V t) ∧
      spatialHolderHalfNorm m (s.velocity t - V t) ≤
        Ct * Λ ^ ((m : ℤ) - P) * spatialHolderHalfNorm P (V t)) :
    ∀ t ∈ Icc 0 T, spatialHolderHalfNorm 2 (s.velocity t - V t) ≤ Ct * truncErr Λ V P t := by
  intro t ht
  refine ((hTails 2 hP t ht).2).trans ?_
  unfold truncErr
  have hN := holderNorm_nonneg P (V t)
  have hz : 0 ≤ Λ ^ ((2 : ℤ) - P) := zpow_nonneg hΛ.le _
  have hle : spatialHolderHalfNorm P (V t) ≤ (1 + spatialHolderHalfNorm P (V t)) ^ 2 := by
    nlinarith
  calc Ct * Λ ^ (((2 : ℕ) : ℤ) - P) * spatialHolderHalfNorm P (V t)
      = Ct * (Λ ^ ((2 : ℤ) - P) * spatialHolderHalfNorm P (V t)) := by push_cast; ring
    _ ≤ Ct * (Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P (V t)) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hz) hCt

/-- **The residual and pressure bounds of the cutoff child at the scheduled size** (item 4 of the proof,
sections/08b_induction.tex:415-421 (item 5) and :463-470 (item 6), from the e-clause (the last conjunct of the (5.56) block) of Proposition 5.11, applied through `hE`, the C^2 bound of (5.56) (clause 3, `hC3`) and the pressure increment (5.57) (clause 5, `h57`) being read directly, and
the size bounds (5.47) of Lemma 5.8 (`hRV`) and the velocity size `hVsize`): with
`e = C ‖R_V‖_{C_tC^{1,1/2}} + K_P ε_Λ` of Proposition 5.11, `ε_Λ = Λ^{2-P}(1 + ‖V‖_{C_tC^{P,1/2}})²`,
`K_P ≤ μ`, `‖R_V‖ ≤ next^{-7/2}` and the truncation-error budget,
`e ≤ C next^{-7/2} + next^{-5}`. Gives the shapes `hRes`, `hTwo` (`‖u - V‖_{C^{2,1/2}} ≤ next^{-5}`) and `hPress57` ((5.57) at the scheduled size, with `G = Γ D^b λ^{-1/4}`) of `scheduled_T2_T3'` and `exists_inductiveEulerChild_of_physicalCutoff'`. -/
theorem scheduled_bounds_of_5_11 {T : ℝ} (hT : 0 < T) {ψ : Vec3 → ℝ} {V RV : Velocity}
    {Pres pU : Pressure} {μ KP Cc G : ℝ} {b q qNext : ℕ}
    (s : CutoffChild T ((μ ^ frequencyExponent b q) ^ 5) ψ V)
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hKP : KP ≤ μ) (hCc : 0 ≤ Cc)
    (hRV : ∀ t ∈ Icc 0 T, spatialHolderHalfNorm 1 (RV t) ≤
      ((μ ^ frequencyExponent b q) ^ frequencyExponent b qNext) ^ (-7 / 2 : ℝ))
    (hVsize : ∀ t ∈ Icc 0 T, SpatialHolderHalf (6 * frequencyExponent b qNext) (V t) ∧
      1 + spatialHolderHalfNorm (6 * frequencyExponent b qNext) (V t) ≤
        3 * (μ ^ frequencyExponent b q) ^ (2 * (6 * frequencyExponent b qNext + 1)))
    (hE : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, SpatialHolderHalf 1 (s.residual t) ∧
      SpatialHolderHalf 0 (fderiv ℝ (gradient (s.pressure t' - Pres t'))) ∧
      spatialHolderHalfNorm 1 (s.residual t) +
          spatialHolderHalfNorm 0 (fderiv ℝ (gradient (s.pressure t' - Pres t'))) ≤
        Cc * slabSpatialHolderHalfNorm T 1 RV +
          KP * (((μ ^ frequencyExponent b q) ^ 5) ^ ((2 : ℤ) - (6 * frequencyExponent b qNext : ℕ)) *
            (1 + slabSpatialHolderHalfNorm T (6 * frequencyExponent b qNext) V) ^ 2))
    (hC3 : ∀ t ∈ Icc 0 T, SpatialHolderHalf 2 (s.velocity t - V t) ∧
      spatialHolderHalfNorm 2 (s.velocity t - V t) ≤
        KP * (((μ ^ frequencyExponent b q) ^ 5) ^ ((2 : ℤ) - (6 * frequencyExponent b qNext : ℕ)) *
          (1 + slabSpatialHolderHalfNorm T (6 * frequencyExponent b qNext) V) ^ 2))
    (h57 : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (s.pressure t - pU t)) x v⟫_ℝ ≤
        (G + (Cc * slabSpatialHolderHalfNorm T 1 RV +
          KP * (((μ ^ frequencyExponent b q) ^ 5) ^ ((2 : ℤ) - (6 * frequencyExponent b qNext : ℕ)) *
            (1 + slabSpatialHolderHalfNorm T (6 * frequencyExponent b qNext) V) ^ 2))) * ‖v‖ ^ 2) :
    let next := ((μ ^ frequencyExponent b q) ^ frequencyExponent b qNext)
    (∀ t ∈ Icc 0 T, SpatialHolderHalf 1 (s.residual t) ∧ spatialHolderHalfNorm 1 (s.residual t) ≤
        Cc * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ)) ∧
      (∀ t ∈ Icc 0 T, spatialHolderHalfNorm 0
        (fderiv ℝ (gradient (fun x => s.pressure t x - Pres t x))) ≤
          Cc * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ)) ∧
      (∀ t ∈ Icc 0 T, SpatialHolderHalf 2 (s.velocity t - V t) ∧
        spatialHolderHalfNorm 2 (s.velocity t - V t) ≤ next ^ (-5 : ℝ)) ∧
      ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
        ⟪v, fderiv ℝ (gradient (s.pressure t - pU t)) x v⟫_ℝ ≤
          (G + (Cc * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ))) * ‖v‖ ^ 2 := by
  intro next
  have : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  set Pd := 6 * frequencyExponent b qNext with hPd
  have hRVslab : slabSpatialHolderHalfNorm T 1 RV ≤ next ^ (-7 / 2 : ℝ) :=
    ciSup_le fun t => hRV t t.2
  have hVslab0 : 0 ≤ slabSpatialHolderHalfNorm T Pd V :=
    Real.iSup_nonneg fun t => holderNorm_nonneg _ _
  have hVslab : 1 + slabSpatialHolderHalfNorm T Pd V ≤
      3 * (μ ^ frequencyExponent b q) ^ (2 * (Pd + 1)) := by
    have : slabSpatialHolderHalfNorm T Pd V ≤
        3 * (μ ^ frequencyExponent b q) ^ (2 * (Pd + 1)) - 1 :=
      ciSup_le fun t => by linarith [(hVsize t t.2).2]
    linarith
  have hBudget := frequencySchedule_truncation_error_budget (q := q) (qNext := qNext) hμ hb
    hVslab0 hVslab
  dsimp only at hBudget
  have hε : 0 ≤ ((μ ^ frequencyExponent b q) ^ 5) ^ ((2 : ℤ) - (Pd : ℕ)) *
      (1 + slabSpatialHolderHalfNorm T Pd V) ^ 2 := by
    have : (0 : ℝ) < (μ ^ frequencyExponent b q) ^ 5 := by
      have : 0 < μ := by linarith
      positivity
    positivity
  have hKε : KP * (((μ ^ frequencyExponent b q) ^ 5) ^ ((2 : ℤ) - (Pd : ℕ)) *
      (1 + slabSpatialHolderHalfNorm T Pd V) ^ 2) ≤ next ^ (-5 : ℝ) :=
    (mul_le_mul_of_nonneg_right hKP hε).trans hBudget
  have hBound (t t' : ℝ) (ht : t ∈ Icc 0 T) (ht' : t' ∈ Icc 0 T) :
      spatialHolderHalfNorm 1 (s.residual t) +
          spatialHolderHalfNorm 0 (fderiv ℝ (gradient (s.pressure t' - Pres t'))) ≤
        Cc * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ) :=
    ((hE t ht t' ht').2.2).trans (add_le_add (mul_le_mul_of_nonneg_left hRVslab hCc) hKε)
  have hee : Cc * slabSpatialHolderHalfNorm T 1 RV +
      KP * (((μ ^ frequencyExponent b q) ^ 5) ^ ((2 : ℤ) - (Pd : ℕ)) *
        (1 + slabSpatialHolderHalfNorm T Pd V) ^ 2) ≤ Cc * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left hRVslab hCc) hKε
  refine ⟨fun t ht => ⟨(hE t ht t ht).1, ?_⟩, fun t ht => ?_, fun t ht => ⟨(hC3 t ht).1,
    (hC3 t ht).2.trans hKε⟩, fun t ht x v => (h57 t ht x v).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hee]) (sq_nonneg _))⟩
  · linarith [hBound t t ht ht, holderNorm_nonneg 0 (fderiv ℝ (gradient (s.pressure t - Pres t)))]
  · have := hBound t t ht ht
    have h0 := holderNorm_nonneg 1 (s.residual t)
    change spatialHolderHalfNorm 0 (fderiv ℝ (gradient (s.pressure t - Pres t))) ≤ _
    linarith

section Average

open HierarchyTwistedProfile

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

/-- **The phase average of the expansion is the mean part** (sections/06c_finite_hierarchy.tex:222-302,
(5.11), (5.15), the definition of `W̄` in Lemma 5.8): for an expansion `u` of depth `P` whose first
velocity level has zero average (`hV1`, `⟨χ̃A₁⟩ = 0`, `F_h` has zero mean),
`⟨W⟩ = ∑_{p=2}^P B_p`; hence `W - ⟨W⟩` is the oscillation `W_osc` and `⟨W⟩^♮ = W̄^♮` of Lemma 5.8.
Uses: `C_{p+1} = C[V_p]` has zero average, `V_p` (`p ≥ 2`) has zero average (transverse solution),
`B_p` is phase independent (mean solution), `B_1 = 0`. -/
theorem average_expansion (d : ParentGeometry hT U X k) {pU : Pressure} {t₀ : ℝ}
    {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} {amp : ℝ → Vec3 → Vec3} {P : ℕ}
    {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) (hV1 : (S5.ops d).average (u.V 1) = 0) :
    (S5.ops d).average (S5.expansion u P) = ∑ p ∈ Finset.Icc 2 P, u.B p := by
  unfold S5.expansion
  rw [map_sum]
  have hterm : ∀ p ∈ Finset.Icc 1 P, (S5.ops d).average (u.V p + S5.Cd u (p + 1) + u.B p) =
      u.B p := by
    intro p hp
    have hC : (S5.ops d).average (S5.Cd u (p + 1)) = 0 := by
      rw [hu.correction p hp]
      exact Bridge.ops_average_curlCorrection d _
    have hV : (S5.ops d).average (u.V p) = 0 := by
      by_cases hp1 : p = 1
      · subst hp1
        exact hV1
      · exact (hu.transverse p (Finset.mem_Icc.mpr ⟨by
          have := (Finset.mem_Icc.mp hp).1; omega, (Finset.mem_Icc.mp hp).2⟩)).mean_zero
    have hB : (S5.ops d).average (u.B p) = u.B p := by
      by_cases hp1 : p = 1
      · subst hp1
        rw [hu.first_mean.1, map_zero]
      · exact (hu.mean p (Finset.mem_Icc.mpr ⟨by
          have := (Finset.mem_Icc.mp hp).1; omega, (Finset.mem_Icc.mp hp).2⟩)).1.phase_independent
    rw [map_add, map_add, hC, hV, hB, zero_add, zero_add]
  rw [Finset.sum_congr rfl hterm]
  symm
  refine Finset.sum_subset (fun p hp => ?_) (fun p hp hp' => ?_)
  · have := Finset.mem_Icc.mp hp
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  · have h1 : p = 1 := by
      have := Finset.mem_Icc.mp hp
      have : ¬ (2 ≤ p ∧ p ≤ P) := fun h => hp' (Finset.mem_Icc.mpr h)
      omega
    subst h1
    exact hu.first_mean.1

/-- The first velocity level `V₁ = χ̃A₁` has zero phase average (`F_h` has zero mean;
sections/06c_finite_hierarchy.tex:222-240, (3.7)): `V₁` agrees with `leadingVelocityProfile` on the
label cell, and the latter has zero average (`Bridge.leadingVelocityProfile_average`). -/
theorem average_firstLevel {lam : ℝ} (d : ParentGeometry hT U X k) {pU : Pressure} {t₀ : ℝ}
    {center : ℝ → Vec3} {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} {amp : ℝ → Vec3 → Vec3} {P : ℕ}
    {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hL : S5.Launch T X k lam t₀) (hamp : S5.IsSeed U X k t₀ T center amp)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) : (S5.ops d).average (u.V 1) = 0 := by
  have hV : u.V 1 = Bridge.leadingVelocityProfile hL hamp hℓ hfit hh hh₁ χ.value χ.smooth
      χ.zero_before :=
    Lib.S5Bridge.eq_of_centeredCell fun t ht a ha s => by
      rw [hu.leading_velocity t ht a ha s,
        Bridge.leadingVelocityProfile_cell_eval hL hamp hℓ hfit hh hh₁ χ.value χ.smooth
          χ.zero_before ht ha s]
  rw [hV]
  exact Bridge.leadingVelocityProfile_average d hL hamp hℓ hfit hh hh₁ χ.value χ.smooth
    χ.zero_before

end Average

end

end TorusEuler.Paper.Lib.S678a
