import TorusEuler.Paper.Proofs.S678a.Library.LocalStep
import TorusEuler.HierarchyPhysicalInitialSlice
import TorusEuler.PhysicalWaveEnvelopeSupport
import TorusEuler.Paper.Proofs.S678a.Library.StepBundle

/-! # The oscillation of a step vanishes through activation and is localized (package S678a)

Items 4-5 of the proof of Theorem 7.1 (sections/08b_induction.tex:376-461): the oscillation
`O_j = (W - ⟨W⟩)^♮` vanishes on `[0,t_j]` (the clause `vanishing before activation` of
Proposition 5.4, closed at `t_j` by continuity or by `V_p(0) = 0`) and is supported within
`λ_{j-1}^{-1}` of the lattice (the support clause of Proposition 5.4 and the radius
`ℓ_* = 𝖣^{-a}` of the envelope, `a ≥ 3`). -/

open Set Filter UnitAddTorus
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler HierarchyTwistedProfile

noncomputable section

/-- A smooth profile that vanishes before `t₀ > 0` vanishes at `t₀`. -/
theorem profile_zero_at_activation {T t₀ : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchySmoothProfile T E) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (h : ∀ t ∈ Icc 0 T, t < t₀ → ∀ a s, f.val (t, a, s) = 0) (a : Vec3) (s : ℝ) :
    f.val (t₀, a, s) = 0 := by
  have hc : ContinuousOn (fun t : ℝ => f.val (t, a, s)) (Icc 0 T) :=
    (HierarchySmoothProfile.smooth f).continuousOn.comp
      (by fun_prop : Continuous fun t : ℝ => ((t, a, s) : HierarchyProfilePoint)).continuousOn
      (fun t ht => ⟨ht, mem_univ _⟩)
  have hcl : t₀ ∈ closure (Ico 0 t₀) := by
    rw [closure_Ico ht₀.ne]
    exact ⟨ht₀.le, le_rfl⟩
  have hne : (𝓝[Ico 0 t₀] t₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have h1 : ContinuousWithinAt (fun t : ℝ => f.val (t, a, s)) (Ico 0 t₀) t₀ :=
    (hc t₀ ⟨ht₀.le, ht₀T⟩).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc_right ht₀T))
  have h2 : (fun t : ℝ => f.val (t, a, s)) =ᶠ[𝓝[Ico 0 t₀] t₀] fun _ => (0 : E) :=
    eventually_nhdsWithin_of_forall fun t ht => h t ⟨ht.1, ht.2.le.trans ht₀T⟩ ht.2 a s
  exact tendsto_nhds_unique_of_eventuallyEq h1 tendsto_const_nhds h2

/-- The completion of a profile with vanishing time slice has vanishing time slice. -/
theorem complete_eq_zero_on_time_slice {T t : ℝ} {k : Vec3} (hT : 0 < T)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)) (κ : HierarchyTwistedProfile T k Vec3)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ r ∈ Icc 0 T, ∀ a, κ.val.val.val (r, a, 0) ≠ 0) (V : HierarchyTwistedProfile T k Vec3)
    (ht : t ∈ Icc 0 T) (hV : ∀ a s, V.val.val.val (t, a, s) = 0) (a : Vec3) (s : ℝ) :
    (HierarchyTwistedProfile.complete hT G κ hκPhase hκ V).val.val.val (t, a, s) = 0 := by
  have hV0 : ∀ a s, (V.val.val - HierarchySmoothProfile.profilePhaseAverage hT V.val.val).val
      (t, a, s) = 0 := by
    intro a s
    have hs : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    show V.val.val.val (t, a, s) - (HierarchySmoothProfile.profilePhaseAverage hT V.val.val).val
      (t, a, s) = 0
    rw [HierarchySmoothProfile.profilePhaseAverage_apply hT _ hs]
    simp [hV a]
  exact HierarchySmoothProfile.profileCompletion_eq_zero_on_time_slice hT G.val.val
    κ.val.val (V.val.val - HierarchySmoothProfile.profilePhaseAverage hT V.val.val) hκ ht hV0 a s

/-- Evaluation of a finite sum of twisted profiles. -/
theorem twisted_sum_apply {T : ℝ} {k : Vec3} {ι : Type*} (s : Finset ι)
    (f : ι → HierarchyTwistedProfile T k Vec3) (z : HierarchyProfilePoint) :
    (∑ i ∈ s, f i).val.val.val z = ∑ i ∈ s, (f i).val.val.val z := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

/-- **The oscillation vanishes through activation** (Proposition 5.4, vanishing before `t₀`,
and `V_p(0) = 0`, `χ̃(t₀) = 0`): the profile `W - ⟨W⟩ = ∑_{p ≤ P} (V_p + C_{p+1})` vanishes at
every time of `[0, t₀]`, at every label and phase. -/
theorem osc_profile_vanishes {T t₀ ℓ h : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity}
    {k : Vec3} {pU : Pressure} {amp : ℝ → Vec3 → Vec3} {P : ℕ}
    {d : ParentGeometry hT U X k} {χ : PaperWaveCutoff t₀ T}
    {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (ht₀ : 0 ≤ t₀) (ht₀T : t₀ ≤ T) (hχ : χ.value t₀ = 0)
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u)
    (hsum : S5.expansion u P - (S5.ops d).average (S5.expansion u P) =
      ∑ i ∈ Finset.Icc 1 P, (u.V i + S5.Cd u (i + 1)))
    (hVb : ∀ i ∈ Finset.Icc 1 P, ∀ t ∈ Icc 0 T, t < t₀ → ∀ x s, (u.V i).val.val.val (t, x, s) = 0) :
    ∀ t ∈ Icc 0 t₀, ∀ a s, (S5.expansion u P - (S5.ops d).average (S5.expansion u P)).val.val.val
      (t, a, s) = 0 := by
  -- the velocity levels vanish at `t₀`
  have hV0 : ∀ i ∈ Finset.Icc 1 P, ∀ a s, (u.V i).val.val.val (t₀, a, s) = 0 := by
    intro i hi a s
    rcases ht₀.lt_or_eq with hpos | hzero
    · exact profile_zero_at_activation (u.V i).val.val hpos ht₀T (hVb i hi) a s
    · subst hzero
      by_cases h1 : i = 1
      · subst h1
        obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
        have hcell := hu.leading_velocity 0 ⟨le_rfl, hT.le⟩ (a - latticeVector n) hn
          (s - ⟪k, latticeVector n⟫_ℝ)
        have hper := twistedSlice (u.V 1) 0 (a - latticeVector n) (s - ⟪k, latticeVector n⟫_ℝ) n
        rw [sub_add_cancel, sub_add_cancel] at hper
        rw [hper, hcell, hχ, zero_smul]
      · have hi2 : i ∈ Finset.Icc 2 P := by
          simp only [Finset.mem_Icc] at hi ⊢
          omega
        exact (hu.transverse i hi2).initial a s
  intro t ht a s
  rw [hsum, twisted_sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hVz : ∀ a s, (u.V i).val.val.val (t, a, s) = 0 := by
    intro a s
    rcases ht.2.lt_or_eq with hlt | heq
    · exact hVb i hi t ⟨ht.1, ht.2.trans ht₀T⟩ hlt a s
    · rw [heq]; exact hV0 i hi a s
  have hC : (S5.Cd u (i + 1)).val.val.val (t, a, s) = 0 := by
    have hcorr := hu.correction i hi
    rw [hcorr]
    exact complete_eq_zero_on_time_slice hT _ _ _ _ _ ⟨ht.1, ht.2.trans ht₀T⟩ hVz a s
  show (u.V i).val.val.val (t, a, s) + (S5.Cd u (i + 1)).val.val.val (t, a, s) = 0
  rw [hVz a s, hC, add_zero]

/-- **The oscillation is localized** (support clause of Proposition 5.4 and `ℓ_* = 𝖣^{-a}`,
`a ≥ 3`): where the oscillation `graphRead Y f` of a profile `f` that vanishes at labels outside
the envelope support is nonzero, the point is within `λ_{j-1}^{-1}` of a lattice point. -/
theorem osc_support {P : InductiveEulerParameters} {n : ℕ} {activationOld activation : ℝ}
    (parent : InductiveEulerStage P n activationOld) {k : Vec3}
    (hT : 0 < P.slab (n + 1) activation) (hSlab : P.slab (n + 1) activation ≤ P.slab n activationOld)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hμ : 2 ≤ P.frequency n) (hell : ℓ ≤ ((P.frequency n ^ 9) ^ 3)⁻¹)
    (f : HierarchyTwistedProfile (P.slab (n + 1) activation) k Vec3)
    (hf : ∀ t ∈ Icc 0 (P.slab (n + 1) activation), ∀ x ∉ tsupport (periodizeCentered (radialEnvelope ℓ)),
      ∀ s, f.val.val.val (t, x, s) = 0) :
    ∀ t ∈ Icc 0 (P.slab (n + 1) activation), ∀ x, graphRead (fun r => parent.flow r 0) f t x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency n)⁻¹ := by
  intro t ht x hx
  have hsub : Icc 0 (P.slab (n + 1) activation) ⊆ Icc 0 (P.slab n activationOld) :=
    Icc_subset_Icc_right hSlab
  have hX : IsLabelFlowOn parent.velocity parent.flow (Icc 0 (P.slab (n + 1) activation)) :=
    parent.deformation.flow.mono hsub
  have hμD : P.frequency n ≤ P.frequency n ^ 9 :=
    le_self_pow₀ (one_le_two.trans hμ) (by norm_num)
  have hmem : parent.flow t 0 x ∈ tsupport (periodizeCentered (radialEnvelope ℓ)) := by
    by_contra h
    exact hx (hf t ht _ h _)
  exact hX.exists_lattice_dist_le_inv_of_inverse_mem_periodicEnvelope_tsupport hT hℓ
    ((parent.smooth_velocity.mono (prod_mono_left hsub)).of_le (by simp))
    (fun s _ => parent.periodic_velocity s) (fun s hs => parent.odd_velocity s (hsub hs)) ht hμ hμD
    hell (fun a => ((parent.deformation.bounds t (hsub ht)).2.1 a).2.trans hμD) hmem

end

end TorusEuler.Paper.Lib.S678a
