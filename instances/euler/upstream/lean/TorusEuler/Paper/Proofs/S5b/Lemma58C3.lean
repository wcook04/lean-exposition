import TorusEuler.Paper.Proofs.S5b.Lemma58C2

/-!
# Lemma 5.8, third part (continued): the norm of the twisted extension of `A₁`

`extLeading_wNorm_le`: on `[t₀,T]` the weighted norm (D.1) of the twisted profile
`V₀ = extLeading …` is at most the weighted norm (D.1) of the raw field `A₁ = g𝐚F_h` on
`[t₀,T] × ℝ³ × ℝ` (which is the norm bounded by (5.22) of Lemma 5.3), and the raw field has
bounded jets. Every mixed jet of `V₀` at `(t,a,s)` is, after a twisted lattice translation into
the cell, either a jet of `A₁` (near labels in the open ball of radius `1/2 - δ`, where
`V₀ = A₁`), or zero (near labels whose lattice translates all stay at distance `≥ 2ℓ_*`); and
conversely every jet of `A₁` is a jet of `V₀` or zero. This is glue: the identification of the
lattice-periodic profile with the field of the text on the cell.
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile LocalizedAmplitude Lib.S5Bridge AppendixD

noncomputable section

section Words

variable {ι U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Words of functions that agree near a point agree near that point. -/
theorem word_eventuallyEq {D : ι → U → U} {f g : U → E} {x : U} (h : f =ᶠ[𝓝 x] g)
    (w : List ι) : phaseOperatorWord D w f =ᶠ[𝓝 x] phaseOperatorWord D w g := by
  induction w with
  | nil => exact h
  | cons i w ih =>
    filter_upwards [ih.eventuallyEq_nhds] with y hy
    change fderiv ℝ (phaseOperatorWord D w f) y (D i y) = fderiv ℝ (phaseOperatorWord D w g) y (D i y)
    rw [hy.fderiv_eq]

/-- Words in constant directions commute with translations. -/
theorem word_comp_add (d : ι → U) {f : U → E} (c : U) (w : List ι) :
    phaseOperatorWord (fun i (_ : U) => d i) w (fun y => f (y + c)) =
      fun y => phaseOperatorWord (fun i (_ : U) => d i) w f (y + c) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext y
    change fderiv ℝ (phaseOperatorWord (fun i (_ : U) => d i) w (fun y => f (y + c))) y (d i) =
      fderiv ℝ (phaseOperatorWord (fun i (_ : U) => d i) w f) (y + c) (d i)
    rw [ih, fderiv_comp_add_right]

end Words

variable {T : ℝ} {k : Vec3}

/-- The mixed directions of (D.1) are constant. -/
theorem mixedDirection_const (ℓ h : ℝ) :
    hierarchyMixedDirection ℓ h = fun i (_ : Vec3 × ℝ) => hierarchyMixedDirection ℓ h i 0 := rfl

/-- A label in the closed cell is at least as close to the origin as any of its lattice
translates. -/
theorem norm_le_norm_sub_latticeVector {a : Vec3} (ha : a ∈ centeredCell) (m : Fin 3 → ℤ) :
    ‖a‖ ≤ ‖a - latticeVector m‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have hai := ha i
  have hm : (a - latticeVector m) i = a i - (m i : ℝ) := by
    simp [latticeVector]
  rw [hm, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  rcases le_or_gt (m i) 0 with hle | hgt
  · rcases lt_or_eq_of_le hle with hlt | heq
    · have : (m i : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      nlinarith [hai.1, hai.2]
    · rw [heq]; simp
  · have : (1 : ℝ) ≤ m i := by exact_mod_cast hgt
    nlinarith [hai.1, hai.2]

variable {U : Velocity} {X : ℝ → Velocity} {t₀ : ℝ} {center : ℝ → Vec3} {lam : ℝ}

/-- **Jets of the twisted extension versus jets of `A₁`** at a time `t ∈ [t₀,T]`, for the
fields scaled by a constant `c` (the weight `γ(t)⁻¹`): every jet of one is a jet of the other
or zero. -/
theorem extLeading_jets (hL : S5.Launch T X k lam t₀) {ℓ h : ℝ} (hℓ : 0 < ℓ)
    (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) {amp ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)))
    (hEq : ∀ t ∈ Icc t₀ T, ∀ a, ampE t a = amp t a) {t : ℝ} (ht : t ∈ Icc t₀ T) (c : ℝ)
    (ℓ' h' : ℝ) (w : List (Fin 4)) (x : Vec3 × ℝ) :
    let V := fun y : Vec3 × ℝ => c • (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val (t, y)
    let A := fun y : Vec3 × ℝ => c • S5.leading ℓ h amp t y.1 y.2
    let D := hierarchyMixedDirection ℓ' h'
    (phaseOperatorWord D w V x = 0 ∨ ∃ y, phaseOperatorWord D w V x = phaseOperatorWord D w A y) ∧
      (phaseOperatorWord D w A x = 0 ∨ ∃ y, phaseOperatorWord D w A x = phaseOperatorWord D w V y) := by
  intro V A D
  have ht' : t ∈ Icc 0 T := Bridge.Launch.active_subset hL ht
  set δ : ℝ := (1 / 2 - 2 * ℓ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  -- (F1) `V = A` on the cell
  have hF1 (y : Vec3 × ℝ) (hy : y.1 ∈ centeredCell) : V y = A y := by
    change c • (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val (t, y.1, y.2) = _
    rw [extLeading_active_eval k hℓ hfit hh hh₁ hE hEq hL.start_nonneg ht, wrapped_eq_on_cell k hy y.2
      hfit (fun b hb q => by simp only [rawLeading, radialEnvelope_eq_zero hℓ hb, zero_smul]),
      rawLeading_eq_leading]
  -- labels of norm `< 1/2` lie in the cell
  have hcell (b : Vec3) (hb : ‖b‖ < 1 / 2) : b ∈ centeredCell := fun i => by
    have := PiLp.norm_apply_le b i
    rw [Real.norm_eq_abs] at this
    exact ⟨by linarith [neg_abs_le (b i)], by linarith [le_abs_self (b i)]⟩
  -- near a label of norm `< 1/2 - δ`, `V = A`
  have hnear (y : Vec3 × ℝ) (hy : ‖y.1‖ < 1 / 2 - δ) : V =ᶠ[𝓝 y] A := by
    have hopen : IsOpen {z : Vec3 × ℝ | ‖z.1‖ < 1 / 2} :=
      isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
    filter_upwards [hopen.mem_nhds (show ‖y.1‖ < 1 / 2 by linarith)] with z hz
    exact hF1 z (hcell z.1 hz)
  have hDconst : D = fun i (_ : Vec3 × ℝ) => hierarchyMixedDirection ℓ' h' i 0 := rfl
  refine ⟨?_, ?_⟩
  · -- jets of `V`: translate into the cell
    obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell x.1
    let cc : Vec3 × ℝ := (latticeVector n, ⟪k, latticeVector n⟫_ℝ)
    let x' : Vec3 × ℝ := (x.1 - latticeVector n, x.2 - ⟪k, latticeVector n⟫_ℝ)
    have hx : x = x' + cc := by
      change x = (x.1 - latticeVector n + latticeVector n, x.2 - ⟪k, latticeVector n⟫_ℝ +
        ⟪k, latticeVector n⟫_ℝ)
      simp
    have hVtrans : (fun y => V (y + cc)) = V := by
      funext y
      change c • (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val
        (t, y.1 + latticeVector n, y.2 + ⟪k, latticeVector n⟫_ℝ) = _
      rw [HierarchyTwistedProfile.twistedSlice]
    have hword : phaseOperatorWord D w V x = phaseOperatorWord D w V x' := by
      rw [hx, hDconst]
      have h := congrFun (word_comp_add (fun i => hierarchyMixedDirection ℓ' h' i 0) (f := V) cc w) x'
      rw [hVtrans] at h
      exact h.symm
    rw [hword]
    by_cases hsmall : ‖x'.1‖ < 1 / 2 - δ
    · exact Or.inr ⟨x', ((word_eventuallyEq (hnear x' hsmall) w).eq_of_nhds)⟩
    · left
      have hzero : V =ᶠ[𝓝 x'] fun _ => 0 := by
        have hball : Metric.ball x'.1 (δ / 2) ∈ 𝓝 x'.1 := Metric.ball_mem_nhds _ (by linarith)
        filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hball] with z hz
        have hz' : ‖z.1 - x'.1‖ < δ / 2 := by simpa [dist_eq_norm] using hz
        have hsep (m : Fin 3 → ℤ) : 2 * ℓ ≤ ‖z.1 - latticeVector m‖ := by
          have h1 := norm_le_norm_sub_latticeVector hn m
          have h2 : ‖x'.1 - latticeVector m‖ ≤ ‖z.1 - latticeVector m‖ + ‖z.1 - x'.1‖ := by
            calc ‖x'.1 - latticeVector m‖ = ‖(z.1 - latticeVector m) - (z.1 - x'.1)‖ := by
                  congr 1; abel
              _ ≤ _ := norm_sub_le _ _
          have h3 : 1 / 2 - δ ≤ ‖x'.1‖ := le_of_not_gt hsmall
          change 1 / 2 - δ ≤ ‖x.1 - latticeVector n‖ at h3
          change ‖x.1 - latticeVector n‖ ≤ ‖x.1 - latticeVector n - latticeVector m‖ at h1
          change ‖x.1 - latticeVector n - latticeVector m‖ ≤ _ + _ at h2
          rw [hδ] at h3 hz'
          linarith
        change c • (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val (t, z.1, z.2) = 0
        have h0 := phaseTwistedPeriodizeCentered_radialEnvelope_eq_zero_of_separation (k := k)
          (f := fun u x q => waveProfile h q • ampE u x) hℓ hsep t z.2
        rw [extLeading_eval k hℓ hfit hh hh₁ hE ht',
          show phaseTwistedPeriodizeCentered k (rawLeading ℓ h ampE) t z.1 z.2 = 0 from h0, smul_zero]
      rw [(word_eventuallyEq hzero w).eq_of_nhds,
        show (fun _ : Vec3 × ℝ => (0 : Vec3)) = 0 from rfl, word_zero]
      rfl
  · -- jets of `A`
    by_cases hsmall : ‖x.1‖ < 1 / 2 - δ
    · exact Or.inr ⟨x, ((word_eventuallyEq (hnear x hsmall) w).eq_of_nhds).symm⟩
    · left
      have hzero : A =ᶠ[𝓝 x] fun _ => 0 := by
        have hball : Metric.ball x.1 δ ∈ 𝓝 x.1 := Metric.ball_mem_nhds _ hδ0
        filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hball] with z hz
        have hz' : ‖z.1 - x.1‖ < δ := by simpa [dist_eq_norm] using hz
        have h3 : 1 / 2 - δ ≤ ‖x.1‖ := le_of_not_gt hsmall
        have h4 : ‖x.1‖ ≤ ‖z.1‖ + ‖z.1 - x.1‖ := by
          calc ‖x.1‖ = ‖z.1 - (z.1 - x.1)‖ := by congr 1; abel
            _ ≤ _ := norm_sub_le _ _
        have hfar : 2 * ℓ ≤ ‖z.1‖ := by rw [hδ] at h3 hz'; linarith
        change c • S5.leading ℓ h amp t z.1 z.2 = 0
        simp only [S5.leading, radialEnvelope_eq_zero hℓ hfar, zero_mul, zero_smul, smul_zero]
      rw [(word_eventuallyEq hzero w).eq_of_nhds,
        show (fun _ : Vec3 × ℝ => (0 : Vec3)) = 0 from rfl, word_zero]
      rfl

/-- **The norm comparison**: on `[t₀,T]`, `‖V₀‖_{[n],γ} ≤ ‖A₁‖_{[n],γ}` (the latter the norm
(D.1) of the raw field `S5.leading` on `[t₀,T] × ℝ³ × ℝ`), and the raw field has bounded jets
(so its norm is a genuine finite norm). -/
theorem extLeading_wNorm_le (hT : 0 < T) (hL : S5.Launch T X k lam t₀) {ℓ h : ℝ} (hℓ : 0 < ℓ)
    (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) {amp ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)))
    (hEq : ∀ t ∈ Icc t₀ T, ∀ a, ampE t a = amp t a) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t) (n : ℕ) :
    S5.wNorm ℓ h t₀ γ n (extLeading (T := T) k hℓ hfit hh hh₁ hE) ≤
      S5.fieldNorm ℓ h (Icc t₀ T) (fun t => (γ t)⁻¹) n (fun t x => S5.leading ℓ h amp t x.1 x.2) := by
  let FV : Icc t₀ T → Vec3 × ℝ → Vec3 := fun t x =>
    (γ t)⁻¹ • (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val ((t : ℝ), x)
  let FA : Icc t₀ T → Vec3 × ℝ → Vec3 := fun t x => (γ t)⁻¹ • S5.leading ℓ h amp t x.1 x.2
  have hfin := Bridge.fieldNormFinite_weighted hT ℓ h n hL.start_nonneg hL.start_lt.le hγc hγ
    (extLeading (T := T) k hℓ hfit hh hh₁ hE)
  have hsubV (w : List (Fin 4)) : hierarchyJetValues False (hierarchyMixedDirection ℓ h) w FV ⊆
      hierarchyJetValues False (hierarchyMixedDirection ℓ h) w FA := by
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
    · exact Or.inl rfl
    · rcases (extLeading_jets hL hℓ hfit hh hh₁ hE hEq t.2 (γ t)⁻¹ ℓ h w x).1 with h0 | ⟨y, hy⟩
      · left
        change ‖phaseOperatorWord _ w (FV t) x‖ = 0
        exact (congrArg norm h0).trans norm_zero
      · exact Or.inr (Or.inl ⟨t, y, (congrArg norm hy).symm⟩)
    · exact hH.elim
  have hsubA (w : List (Fin 4)) : hierarchyJetValues False (hierarchyMixedDirection ℓ h) w FA ⊆
      hierarchyJetValues False (hierarchyMixedDirection ℓ h) w FV := by
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
    · exact Or.inl rfl
    · rcases (extLeading_jets hL hℓ hfit hh hh₁ hE hEq t.2 (γ t)⁻¹ ℓ h w x).2 with h0 | ⟨y, hy⟩
      · left
        change ‖phaseOperatorWord _ w (FA t) x‖ = 0
        exact (congrArg norm h0).trans norm_zero
      · exact Or.inr (Or.inl ⟨t, y, (congrArg norm hy).symm⟩)
    · exact hH.elim
  change hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n FV ≤
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n FA
  refine Finset.sum_le_sum fun w hw => csSup_le_csSup ((hfin.2 w hw).mono (hsubA w))
    ⟨0, Or.inl rfl⟩ (hsubV w)

end

end TorusEuler.Paper.S5b
