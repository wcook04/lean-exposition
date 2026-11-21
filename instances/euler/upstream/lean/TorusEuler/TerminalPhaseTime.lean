import TorusEuler.TerminalProfileTimeDerivatives
import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchyConcreteCompletion
import TorusEuler.HierarchyLinearRelayBounds
import TorusEuler.FirstWaveHierarchyInput
import TorusEuler.TruncatedParentAdmissibility

/-! Phase normalization and primitive estimates for time jets on the closed slab. -/

open Set MeasureTheory
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "I" => Icc (0 : ℝ) T
local notation "Profile" => HierarchyTwistedProfile T k E

/-- The phase derivative, with time and label held fixed. -/
abbrev phaseDerivative (hT : 0 < T) : Profile →ₗ[ℝ] Profile :=
  directionDerivative hT (0, 0, 1)

theorem phaseDerivative_apply (hT : 0 < T) (f : Profile)
    (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) :
    (phaseDerivative hT f).val.val.val (t,a,s) =
      deriv (fun r => f.val.val.val (t,a,r)) s := by
  rw [phaseDerivative, directionDerivative_apply hT _ _ ⟨ht, mem_univ _⟩]
  exact eval_phaseDerivative f ⟨ht, mem_univ _⟩

theorem hasDerivAt_phaseDerivative (hT : 0 < T) (f : Profile)
    (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) :
    HasDerivAt (fun r => f.val.val.val (t,a,r))
      ((phaseDerivative hT f).val.val.val (t,a,s)) s := by
  rw [phaseDerivative_apply hT f t ht a s]
  have hs : ContDiff ℝ ∞ (fun r => f.val.val.val (t,a,r)) :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val ht).comp
      (contDiff_const.prodMk contDiff_id)
  exact (hs.differentiable (by simp) s).hasDerivAt

variable [CompleteSpace E]

/-- The normalized phase average commutes with a genuine time derivative
also at the two endpoints. -/
theorem hasDerivWithinAt_phaseMean (hT : 0 < T) (f : Profile)
    (t : ℝ) (ht : t ∈ I) (a : Vec3) :
    HasDerivWithinAt (fun u => phaseMean (fun s => f.val.val.val (u,a,s)))
      (phaseMean (fun s => (timeDerivative hT f).val.val.val (t,a,s))) I t := by
  let F (u s : ℝ) := f.val.val.val (u,a,s)
  let D (u s : ℝ) := (timeDerivative hT f).val.val.val (u,a,s)
  have hcont (g : Profile) : ContinuousOn (fun p : ℝ × ℝ => g.val.val.val (p.1,a,p.2))
      (I ×ˢ (Icc (0 : ℝ) 1)) :=
    (HierarchySmoothProfile.smooth g.val.val).continuousOn.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hd (u : ℝ) (hu : u ∈ I) (s : ℝ) (_ : s ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun r => F r s) (D u s) I u := by
    rw [show D u s = derivWithin (fun r => F r s) I u from timeDerivative_apply hT f hu (a,s)]
    have hslice : ContDiffOn ℝ ∞ (fun r => F r s) I :=
      (HierarchySmoothProfile.smooth f.val.val).comp
        (contDiff_id.prodMk contDiff_const).contDiffOn (fun r hr => ⟨hr, mem_univ (a,s)⟩)
    exact (hslice.differentiableOn (by simp) u hu).hasDerivWithinAt
  have h := hasDerivWithinAt_integral_prod_Icc (F := F) (D := D) isCompact_Icc ht
    (hcont f) (hcont (timeDerivative hT f)) hd
  simpa only [phaseMean, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    F, D] using h

/-- Normalization is preserved by every time jet of a smooth twisted profile. -/
theorem phaseMean_timeJet_eq_zero (hT : 0 < T) (f : Profile)
    (hmean : ∀ t ∈ I, ∀ a, phaseMean (fun s => f.val.val.val (t,a,s)) = 0)
    (i : ℕ) (t : ℝ) (ht : t ∈ I) (a : Vec3) :
    phaseMean (fun s => (timeJet hT i f).val.val.val (t,a,s)) = 0 := by
  induction i generalizing t with
  | zero => simpa only [timeJet_zero] using hmean t ht a
  | succ i ih =>
    rw [timeJet_succ]
    let g := timeJet hT i f
    have hd := hasDerivWithinAt_phaseMean hT g t ht a
    have hz : HasDerivWithinAt (fun u => phaseMean (fun s => g.val.val.val (u,a,s)))
        0 I t :=
      (hasDerivWithinAt_const t I (0 : E)).congr (fun u hu => ih u hu) (ih t ht)
    exact (hd.derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
      (hz.derivWithin (uniqueDiffOn_Icc hT t ht))

/-- A mean-zero profile is controlled by its phase derivative with the unit
period primitive constant, including all label and phase words at the same
positive time weight. -/
theorem amplitudeSeminorm_le_phaseDerivative (hT : 0 < T) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T))
    (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < γ t) (ℓ h : ℝ) (n : ℕ) (f : Profile)
    (hmean : ∀ t ∈ I, ∀ a, phaseMean (fun s => f.val.val.val (t,a,s)) = 0) :
    amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hγ₀ f ≤
      2 * amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hγ₀ (phaseDerivative hT f) := by
  let A := Icc t₀ T
  have hA : A ⊆ I := Icc_subset_Icc_left ht₀
  let w (t : ℝ) := (γ t)⁻¹
  let u := weightedSlices A w f
  let du := weightedSlices A w (phaseDerivative hT f)
  have hderiv (t : A) (a : Vec3) (s : ℝ) :
      HasDerivAt (fun z => u t (a,z)) (du t (a,s)) s :=
    (hasDerivAt_phaseDerivative hT f t (hA t.property) a s).const_smul (w t)
  have hper (t : A) (a : Vec3) : Function.Periodic (fun z => u t (a,z)) 1 :=
    fun z => congrArg (fun x : E => w t • x) (HierarchyPeriodicProfile.phasePeriodic f.val t a z)
  have hduper (t : A) (a : Vec3) : Function.Periodic (fun z => du t (a,z)) 1 :=
    fun z => congrArg (fun x : E => w t • x)
      (HierarchyPeriodicProfile.phasePeriodic (phaseDerivative hT f).val t a z)
  have hdu (t : A) := weightedSlices_smooth hA w (phaseDerivative hT f) t
  have hdc (t : A) (a : Vec3) : Continuous (fun z => du t (a,z)) :=
    (hdu t).continuous.comp (continuous_const.prodMk continuous_id)
  have hzero (t : A) (a : Vec3) : phaseMean (fun z => du t (a,z)) = 0 :=
    phaseMean_deriv (hderiv t a) (hdc t a) (hper t a)
  have hbase (t : A) (a : Vec3) : phaseMean (fun z => u t (a,z)) = 0 := by
    change phaseMean (fun z => w t • f.val.val.val (t,a,z)) = 0
    rw [phaseMean_const_smul, hmean t (hA t.property) a, smul_zero]
  have hEq : (fun (t : A) (p : Vec3 × ℝ) => phasePrimitive (fun s => du t (p.1,s)) p.2) = u := by
    funext t p
    rw [phasePrimitive_deriv (hderiv t p.1) (hdc t p.1), phaseOscillation, hbase, sub_zero]
  obtain ⟨B, hB⟩ := inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hγ₀
  have hbound := hierarchyFiniteWordNorm_phasePrimitive_le
    (fun i => hierarchyMixedDirection ℓ h i 0) n hdu hduper hzero
    (fun w _ => hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w (phaseDerivative hT f)
      hA (fun t => (γ t)⁻¹) hB)
  rw [amplitudeSeminorm_apply, amplitudeSeminorm_apply]
  rw [hEq] at hbound
  exact hbound.2

end

end TorusEuler.HierarchyTwistedProfile
