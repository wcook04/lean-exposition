import TorusEuler.TerminalHierarchyLinearTime
import TorusEuler.HierarchyTwistedSelectedRelay

/-! The normalized primitive terms in the mixed-time completion and relay. -/

open Set Finset
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}
  {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A phase-independent coefficient preserves a zero phase mean. -/
theorem PhaseMeanZero.clm_apply (f : HierarchyTwistedProfile T k E)
    (hf : PhaseMeanZero f) (c : HierarchyTwistedProfile T k (E →L[ℝ] F))
    (hc : HierarchyPeriodicProfile.PhaseIndependent c.val.val) :
    PhaseMeanZero (applyField c f) := by
  intro t ht a
  let L := c.val.val.val (t, a, 0)
  have he : (fun s => (applyField c f).val.val.val (t, a, s)) =
      fun s => L (f.val.val.val (t, a, s)) := by
    funext s
    rw [applyField_eval c f ⟨ht, mem_univ _⟩, hc (t, a, 0) ⟨ht, mem_univ _⟩ s]
  rw [he, phaseMean, L.intervalIntegral_comp_comm, ← phaseMean, hf t ht a, map_zero]
  have hcont : Continuous (fun s => f.val.val.val (t, a, s)) := by
    refine continuousOn_univ.mp ((HierarchySmoothProfile.smooth f.val.val).continuousOn.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn ?_)
    exact fun _ _ => ⟨ht, mem_univ _⟩
  exact hcont.intervalIntegrable _ _

/-- One normalized potential or pressure primitive, after applying its
phase-independent coefficient. -/
def relayPhasePrimitive (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (hf : PhaseMeanZero f) (c : HierarchyTwistedProfile T k (E →L[ℝ] F))
    (hc : HierarchyPeriodicProfile.PhaseIndependent c.val.val) : HierarchyTwistedProfile T k F :=
  phasePrimitiveProfile hT (applyField c f) (hf.clm_apply f c hc)

theorem relayPhasePrimitive_apply (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (hf : PhaseMeanZero f) (c : HierarchyTwistedProfile T k (E →L[ℝ] F))
    (hc : HierarchyPeriodicProfile.PhaseIndependent c.val.val)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (relayPhasePrimitive hT f hf c hc).val.val.val (t, a, s) =
      phasePrimitive (fun σ => c.val.val.val (t,a,0) (f.val.val.val (t,a,σ))) s := by
  rw [relayPhasePrimitive, phasePrimitiveProfile_apply hT _ _ ht]
  apply congrArg (fun g => phasePrimitive g s)
  funext σ
  rw [applyField_eval c f ⟨ht, mem_univ _⟩, hc (t,a,0) ⟨ht, mem_univ _⟩ σ]

/-- A primitive followed by one of the label derivatives and one coframe row. -/
def relayPrimitiveTerm (hT : 0 < T) (ell h : ℝ) (i : Fin 3)
    (f : HierarchyTwistedProfile T k E) (hf : PhaseMeanZero f)
    (c : HierarchyTwistedProfile T k (E →L[ℝ] F))
    (hc : HierarchyPeriodicProfile.PhaseIndependent c.val.val)
    (row : HierarchyTwistedProfile T k (F →L[ℝ] G)) : HierarchyTwistedProfile T k G :=
  applyField row (scaledProfileDerivative hT ell h i.castSucc (relayPhasePrimitive hT f hf c hc))

theorem relayPrimitiveTerm_apply (hT : 0 < T) (ell h : ℝ) (i : Fin 3)
    (f : HierarchyTwistedProfile T k E) (hf : PhaseMeanZero f)
    (c : HierarchyTwistedProfile T k (E →L[ℝ] F))
    (hc : HierarchyPeriodicProfile.PhaseIndependent c.val.val)
    (row : HierarchyTwistedProfile T k (F →L[ℝ] G))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (relayPrimitiveTerm hT ell h i f hf c hc row).val.val.val (t, x) =
      row.val.val.val (t, x) (phaseDirectionalDerivative (hierarchyMixedDirection ell h i.castSucc)
        (fun y => phasePrimitive (fun σ => c.val.val.val (t,y.1,0) (f.val.val.val (t,y.1,σ))) y.2) x) := by
  unfold relayPrimitiveTerm
  rw [applyField_eval row _ ⟨ht, mem_univ _⟩, scaledProfileDerivative_apply hT ell h i.castSucc _ ht]
  rw [show (fun y : Vec3 × ℝ => (relayPhasePrimitive hT f hf c hc).val.val.val (t, y)) =
    fun y => phasePrimitive (fun σ => c.val.val.val (t,y.1,0) (f.val.val.val (t,y.1,σ))) y.2
    from funext fun y => relayPhasePrimitive_apply hT f hf c hc ht y.1 y.2]

/-- The factorial time norm of a normalized relay term has the same one
label derivative cost and two linear coefficient factors as the spatial bound. -/
theorem timeJetSeminorm_relayPrimitiveTerm_le (hT : 0 < T) (q : ℕ) (ell h : ℝ) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C)
    (i : Fin 3) (f : HierarchyTwistedProfile T k E) (hf : PhaseMeanZero f)
    (c : HierarchyTwistedProfile T k (E →L[ℝ] F))
    (hc : HierarchyPeriodicProfile.PhaseIndependent c.val.val)
    (row : HierarchyTwistedProfile T k (F →L[ℝ] G)) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ)
        (relayPrimitiveTerm hT ell h i f hf c hc row) ≤
      (2 * (terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ G (E := F)).flip n) *
        (terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ F (E := E)).flip (n + 1))) *
        (timeJetSeminorm hT q (unweightedSeminorm False ell h n hT) row *
          timeJetSeminorm hT q (unweightedSeminorm False ell h (n + 1) hT) c) *
        timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n + 1) hT hA τ hτ) f := by
  let prim := relayPhasePrimitive hT f hf c hc
  let coeff := terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ F (E := E)).flip (n + 1)
  let rowCost := terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ G (E := F)).flip n
  let Urow := timeJetSeminorm hT q (unweightedSeminorm False ell h n hT) row
  let Uco := timeJetSeminorm hT q (unweightedSeminorm False ell h (n + 1) hT) c
  let Vf := timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n + 1) hT hA τ hτ) f
  have hD := timeJetSeminorm_scaledProfileDerivative_le False hT q ell h i.castSucc n prim hA τ hτ
  have hPrim := timeJetSeminorm_phasePrimitiveProfile_le hT q (applyField c f) (hf.clm_apply f c hc)
    hA τ hτ ell h (n + 1)
  have hV := timeJetSeminorm_applyField_weighted_le hT q False ell h (n + 1) hA τ hτ c f
  calc
    _ ≤ rowCost * (Urow * timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ)
        (scaledProfileDerivative hT ell h i.castSucc prim)) :=
      timeJetSeminorm_applyField_weighted_le hT q False ell h n hA τ hτ row _
    _ ≤ rowCost * (Urow * (2 * (coeff * (Uco * Vf)))) := by
      have hr : 0 ≤ rowCost := by unfold rowCost terminalHierarchyProductCost; positivity
      have hs : 0 ≤ Urow := apply_nonneg _ _
      apply mul_le_mul_of_nonneg_left _ hr
      apply mul_le_mul_of_nonneg_left _ hs
      exact hD.trans (hPrim.trans (mul_le_mul_of_nonneg_left hV (by norm_num)))
    _ = _ := by dsimp only [coeff, rowCost, Urow, Uco, Vf]; ring

end

end TorusEuler.HierarchyTwistedProfile
