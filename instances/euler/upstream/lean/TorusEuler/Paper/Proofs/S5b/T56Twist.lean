import TorusEuler.Paper.Proofs.S5b.T56Terms
import TorusEuler.Paper.Proofs.S5b.Lemma58C3

/-!
# Theorem 5.6, glue: twisted profiles versus raw fields

A lattice-twisted profile whose values on the label cell are those of a raw field `F` that
vanishes at labels of norm `≥ 2ℓ_*` has, at every time, the same jets (up to zero) as `F`
(a generalization of `extLeading_jets` of `Lemma58C3`, for any value space). Hence its weighted
norm (D.1) on `[t₀,T]` is at most the norm of the raw field, as used implicitly in the text for
the norms of `A₁`, `𝗉[A₁]` (TeX :570-571, :514-518). A time multiplier of modulus at most one does
not increase the norm (`fieldNorm_smul_time_le`, `wNorm_smul_time_le`).
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 4000000 in
/-- **Jets of a twisted profile versus jets of a raw field** at one time: every jet of one is a
jet of the other or zero. -/
theorem twisted_jets (V₀ : HierarchyTwistedProfile T k E) {t : ℝ} {F : Vec3 × ℝ → E} {ℓ : ℝ}
    (_hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    (hcell : ∀ y : Vec3 × ℝ, y.1 ∈ centeredCell → V₀.val.val.val (t, y.1, y.2) = F y)
    (hzero : ∀ y : Vec3 × ℝ, 2 * ℓ ≤ ‖y.1‖ → F y = 0) (c : ℝ)
    (ℓ' h' : ℝ) (w : List (Fin 4)) (x : Vec3 × ℝ) :
    let V := fun y : Vec3 × ℝ => c • V₀.val.val.val (t, y.1, y.2)
    let A := fun y : Vec3 × ℝ => c • F y
    let D := hierarchyMixedDirection ℓ' h'
    (phaseOperatorWord D w V x = 0 ∨ ∃ y, phaseOperatorWord D w V x = phaseOperatorWord D w A y) ∧
      (phaseOperatorWord D w A x = 0 ∨ ∃ y, phaseOperatorWord D w A x = phaseOperatorWord D w V y) := by
  intro V A D
  set δ : ℝ := (1 / 2 - 2 * ℓ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hF1 (y : Vec3 × ℝ) (hy : y.1 ∈ centeredCell) : V y = A y := by
    change c • V₀.val.val.val (t, y.1, y.2) = c • F y
    rw [hcell y hy]
  have hcellb (b : Vec3) (hb : ‖b‖ < 1 / 2) : b ∈ centeredCell := fun i => by
    have := PiLp.norm_apply_le b i
    rw [Real.norm_eq_abs] at this
    exact ⟨by linarith [neg_abs_le (b i)], by linarith [le_abs_self (b i)]⟩
  have hnear (y : Vec3 × ℝ) (hy : ‖y.1‖ < 1 / 2 - δ) : V =ᶠ[𝓝 y] A := by
    have hopen : IsOpen {z : Vec3 × ℝ | ‖z.1‖ < 1 / 2} :=
      isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
    filter_upwards [hopen.mem_nhds (show ‖y.1‖ < 1 / 2 by linarith)] with z hz
    exact hF1 z (hcellb z.1 hz)
  have hDconst : D = fun i (_ : Vec3 × ℝ) => hierarchyMixedDirection ℓ' h' i 0 := rfl
  have hVtw (n : Fin 3 → ℤ) : (fun y => V (y + (latticeVector n, ⟪k, latticeVector n⟫_ℝ))) = V := by
    funext y
    change c • V₀.val.val.val (t, y.1 + latticeVector n, y.2 + ⟪k, latticeVector n⟫_ℝ) = _
    rw [HierarchyTwistedProfile.twistedSlice]
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell x.1
    let cc : Vec3 × ℝ := (latticeVector n, ⟪k, latticeVector n⟫_ℝ)
    let x' : Vec3 × ℝ := (x.1 - latticeVector n, x.2 - ⟪k, latticeVector n⟫_ℝ)
    have hx : x = x' + cc := by
      change x = (x.1 - latticeVector n + latticeVector n, x.2 - ⟪k, latticeVector n⟫_ℝ +
        ⟪k, latticeVector n⟫_ℝ)
      simp
    have hVtrans : (fun y => V (y + cc)) = V := hVtw n
    have hword : phaseOperatorWord D w V x = phaseOperatorWord D w V x' := by
      rw [hx, hDconst]
      have h := congrFun (word_comp_add (fun i => hierarchyMixedDirection ℓ' h' i 0) (f := V) cc w) x'
      rw [hVtrans] at h
      exact h.symm
    rw [hword]
    by_cases hsmall : ‖x'.1‖ < 1 / 2 - δ
    · exact Or.inr ⟨x', ((word_eventuallyEq (hnear x' hsmall) w).eq_of_nhds)⟩
    · left
      have hzero' : V =ᶠ[𝓝 x'] fun _ => 0 := by
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
        obtain ⟨n', hn'⟩ := exists_sub_latticeVector_mem_centeredCell z.1
        have hV : V z = V (z.1 - latticeVector n', z.2 - ⟪k, latticeVector n'⟫_ℝ) := by
          have h := HierarchyTwistedProfile.twistedSlice V₀ t (z.1 - latticeVector n')
            (z.2 - ⟪k, latticeVector n'⟫_ℝ) n'
          simp only [sub_add_cancel] at h
          change c • V₀.val.val.val (t, z.1, z.2) = c • V₀.val.val.val (t, z.1 - latticeVector n',
            z.2 - ⟪k, latticeVector n'⟫_ℝ)
          rw [h]
        rw [hV, hF1 (z.1 - latticeVector n', z.2 - ⟪k, latticeVector n'⟫_ℝ) hn']
        change c • F (z.1 - latticeVector n', z.2 - ⟪k, latticeVector n'⟫_ℝ) = 0
        rw [hzero (z.1 - latticeVector n', z.2 - ⟪k, latticeVector n'⟫_ℝ) (hsep n'), smul_zero]
      rw [(word_eventuallyEq hzero' w).eq_of_nhds,
        show (fun _ : Vec3 × ℝ => (0 : E)) = 0 from rfl, word_zero]
      rfl
  · by_cases hsmall : ‖x.1‖ < 1 / 2 - δ
    · exact Or.inr ⟨x, ((word_eventuallyEq (hnear x hsmall) w).eq_of_nhds).symm⟩
    · left
      have hzero' : A =ᶠ[𝓝 x] fun _ => 0 := by
        have hball : Metric.ball x.1 δ ∈ 𝓝 x.1 := Metric.ball_mem_nhds _ hδ0
        filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hball] with z hz
        have hz' : ‖z.1 - x.1‖ < δ := by simpa [dist_eq_norm] using hz
        have h3 : 1 / 2 - δ ≤ ‖x.1‖ := le_of_not_gt hsmall
        have h4 : ‖x.1‖ ≤ ‖z.1‖ + ‖z.1 - x.1‖ := by
          calc ‖x.1‖ = ‖z.1 - (z.1 - x.1)‖ := by congr 1; abel
            _ ≤ _ := norm_sub_le _ _
        have hfar : 2 * ℓ ≤ ‖z.1‖ := by rw [hδ] at h3 hz'; linarith
        change c • F z = 0
        rw [hzero z hfar, smul_zero]
      rw [(word_eventuallyEq hzero' w).eq_of_nhds,
        show (fun _ : Vec3 × ℝ => (0 : E)) = 0 from rfl, word_zero]
      rfl

variable {U : Velocity} {X : ℝ → Velocity} {t₀ : ℝ}

set_option maxHeartbeats 4000000 in
/-- **Norm of a twisted profile versus the raw field**: on `[t₀,T]`, `‖V₀‖_{[n],γ} ≤ ‖F‖_{[n],γ}`
(the latter the norm (D.1) of the raw field on `[t₀,T] × ℝ³ × ℝ`). -/
theorem twisted_wNorm_le (hT : 0 < T) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {ℓ h : ℝ} (hℓ : 0 < ℓ)
    (hfit : 2 * ℓ < 1 / 2) (V₀ : HierarchyTwistedProfile T k E) {F : ℝ → Vec3 → ℝ → E}
    (hcell : ∀ t ∈ Icc t₀ T, ∀ x ∈ centeredCell, ∀ s, V₀.val.val.val (t, x, s) = F t x s)
    (hzero : ∀ t ∈ Icc t₀ T, ∀ x s, 2 * ℓ ≤ ‖x‖ → F t x s = 0) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t) (n : ℕ) :
    S5.wNorm ℓ h t₀ γ n V₀ ≤
      S5.fieldNorm ℓ h (Icc t₀ T) (fun t => (γ t)⁻¹) n (fun t x => F t x.1 x.2) := by
  let FV : Icc t₀ T → Vec3 × ℝ → E := fun t x => (γ t)⁻¹ • V₀.val.val.val ((t : ℝ), x)
  let FA : Icc t₀ T → Vec3 × ℝ → E := fun t x => (γ t)⁻¹ • F t x.1 x.2
  have hfin := Bridge.fieldNormFinite_weighted hT ℓ h n ht₀ htT hγc hγ V₀
  have hj (t : Icc t₀ T) (c : ℝ) (w : List (Fin 4)) (x : Vec3 × ℝ) :=
    twisted_jets (k := k) V₀ (t := (t : ℝ)) (F := fun y => F t y.1 y.2) hℓ hfit
      (fun y hy => hcell t t.2 y.1 hy y.2) (fun y hy => hzero t t.2 y.1 y.2 hy) c ℓ h w x
  have hsubV (w : List (Fin 4)) : hierarchyJetValues False (hierarchyMixedDirection ℓ h) w FV ⊆
      hierarchyJetValues False (hierarchyMixedDirection ℓ h) w FA := by
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
    · exact Or.inl rfl
    · rcases (hj t (γ t)⁻¹ w x).1 with h0 | ⟨y, hy⟩
      · left
        exact (congrArg norm h0).trans norm_zero
      · exact Or.inr (Or.inl ⟨t, y, (congrArg norm hy).symm⟩)
    · exact hH.elim
  have hsubA (w : List (Fin 4)) : hierarchyJetValues False (hierarchyMixedDirection ℓ h) w FA ⊆
      hierarchyJetValues False (hierarchyMixedDirection ℓ h) w FV := by
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
    · exact Or.inl rfl
    · rcases (hj t (γ t)⁻¹ w x).2 with h0 | ⟨y, hy⟩
      · left
        exact (congrArg norm h0).trans norm_zero
      · exact Or.inr (Or.inl ⟨t, y, (congrArg norm hy).symm⟩)
    · exact hH.elim
  change hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n FV ≤
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n FA
  refine Finset.sum_le_sum fun w hw => csSup_le_csSup ((hfin.2 w hw).mono (hsubA w))
    ⟨0, Or.inl rfl⟩ (hsubV w)

/-- A time multiplier of modulus at most one does not increase the norm (D.1) of a field whose
jets are bounded. -/
theorem fieldNorm_smul_time_le {ℓ h : ℝ} {A : Set ℝ} {τ c : ℝ → ℝ} (hc : ∀ t ∈ A, |c t| ≤ 1)
    (n : ℕ) {f : ℝ → Vec3 × ℝ → E}
    (hfin : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
        (fun (t : A) x => τ t • f t x))) :
    S5.fieldNorm ℓ h A τ n (fun t x => c t • f t x) ≤ S5.fieldNorm ℓ h A τ n f := by
  unfold S5.fieldNorm
  refine wordNorm_le_of_values hfin fun w _ t x => ⟨t, x, ?_⟩
  have : (fun y => τ t • (c t • f t y)) = fun y => c t • (τ t • f t y) := by
    funext y; rw [smul_comm]
  change ‖phaseOperatorWord _ w (fun y => τ t • (c t • f t y)) x‖ ≤
    ‖phaseOperatorWord _ w (fun y => τ t • f t y) x‖
  rw [this, word_smul_const, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hc t t.2)

end

end TorusEuler.Paper.S5b
