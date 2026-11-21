import TorusEuler.TerminalProfileTimeDerivatives
import TorusEuler.WaveCompletionRelay
import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchyLinearRelayBounds
import TorusEuler.TerminalPhaseTime

/-! Time differentiation of fixed-phase integrals in the selected hierarchy. -/

open Set Filter
open scoped ContDiff Interval InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem profile_phase_time_continuous (f : HierarchyTwistedProfile T k E) (a : Vec3) :
    ContinuousOn (Function.uncurry (fun r s => f.val.val.val (r, a, s))) (Icc 0 T ×ˢ univ) :=
  (HierarchySmoothProfile.smooth f.val.val).continuousOn.comp
    ((continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn)
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

private theorem profile_phase_time_hasDerivWithinAt (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (a : Vec3) {t : ℝ} (ht : t ∈ Icc 0 T) (s : ℝ) :
    HasDerivWithinAt (fun u => f.val.val.val (u, a, s))
      ((timeDerivative hT f).val.val.val (t, a, s)) (Icc 0 T) t := by
  rw [timeDerivative_apply hT _ ht (a, s)]
  exact (((HierarchySmoothProfile.smooth f.val.val).comp
    (contDiff_id.prodMk (contDiff_const.prodMk contDiff_const)).contDiffOn
    (fun _ hu => ⟨hu, mem_univ _⟩)).differentiableOn (by simp) t ht).hasDerivWithinAt

variable [CompleteSpace E]

/-- Time jets pass under integration on a fixed compact phase interval,
including at the endpoints of the time slab. -/
theorem iteratedDerivWithin_phaseInterval_time (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (c d : ℝ) :
    iteratedDerivWithin i (fun r => ∫ s in c..d, f.val.val.val (r, a, s)) (Icc 0 T) t =
      ∫ s in c..d, (timeJet hT i f).val.val.val (t, a, s) := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
    rw [iteratedDerivWithin_succ, timeJet_succ]
    let g := timeJet hT i f
    rw [derivWithin_congr (fun r hr => ih hr) (ih ht)]
    exact (hasDerivWithinAt_phaseInterval ht (profile_phase_time_continuous g a)
      (profile_phase_time_continuous (timeDerivative hT g) a)
      (fun r hr s => profile_phase_time_hasDerivWithinAt hT g a hr s) c d).derivWithin
      (uniqueDiffOn_Icc hT _ ht)

/-- Time jets pass through the normalized phase primitive and its
zero-mean subtraction. -/
theorem iteratedDerivWithin_phasePrimitive_time (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    iteratedDerivWithin i (fun r => phasePrimitive (fun σ => f.val.val.val (r, a, σ)) s) (Icc 0 T) t =
      phasePrimitive (fun σ => (timeJet hT i f).val.val.val (t, a, σ)) s := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
    rw [iteratedDerivWithin_succ, timeJet_succ]
    let g := timeJet hT i f
    rw [derivWithin_congr (fun r hr => ih hr) (ih ht)]
    exact (hasDerivWithinAt_phasePrimitive_time ht (profile_phase_time_continuous g a)
      (profile_phase_time_continuous (timeDerivative hT g) a)
      (fun r hr σ => profile_phase_time_hasDerivWithinAt hT g a hr σ) s).derivWithin
      (uniqueDiffOn_Icc hT _ ht)

/-- The exact phase average in the mean force commutes with time jets. -/
theorem timeJet_profilePhaseAverage (hT : 0 < T) (i : ℕ) (f : HierarchyTwistedProfile T k Vec3) :
    timeJet hT i (profilePhaseAverage hT f) = profilePhaseAverage hT (timeJet hT i f) := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, s⟩ hz
  have ht : t ∈ Icc 0 T := hz.1
  rw [timeJet_apply hT i _ ht]
  have hRight : (profilePhaseAverage hT (timeJet hT i f)).val.val.val (t, a, s) =
      phaseMean (fun σ => (timeJet hT i f).val.val.val (t, a, σ)) :=
    HierarchySmoothProfile.profilePhaseAverage_apply hT _ hz
  rw [hRight]
  have hAvg : EqOn (fun r => (profilePhaseAverage hT f).val.val.val (r, a, s))
      (fun r => ∫ σ in (0 : ℝ)..1, f.val.val.val (r, a, σ)) (Icc 0 T) := by
    intro r hr
    exact HierarchySmoothProfile.profilePhaseAverage_apply hT _ ⟨hr, mem_univ _⟩
  rw [iteratedDerivWithin_congr hAvg ht]
  exact iteratedDerivWithin_phaseInterval_time hT f i ht a 0 1

omit [CompleteSpace E] in
/-- A profile that vanishes on the inactive time interval has vanishing
closed-slab jets there, including when the slab starts at the inactive endpoint. -/
theorem timeJet_zero_of_inactive (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    {t₀ : ℝ} (hi : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, f.val.val.val (t, x) = 0)
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (ht₀ : t < t₀) (x : Vec3 × ℝ) :
    (timeJet hT i f).val.val.val (t, x) = 0 := by
  induction i generalizing t with
  | zero => exact hi t ht ht₀ x
  | succ i ih =>
    rw [timeJet_succ, timeDerivative_apply hT _ ht]
    have he : (fun r => (timeJet hT i f).val.val.val (r, x)) =ᶠ[nhdsWithin t (Icc 0 T)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht₀)] with r hr hr₀
      exact ih hr hr₀
    rw [he.derivWithin_eq (ih ht ht₀)]
    simp

/-- The phase integrals of the profile vanish at each time and label. -/
def PhaseMeanZero (f : HierarchyTwistedProfile T k E) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ a : Vec3, phaseMean (fun s => f.val.val.val (t, a, s)) = 0

theorem PhaseMeanZero.timeJet {f : HierarchyTwistedProfile T k E}
    (hf : PhaseMeanZero f) (hT : 0 < T) (i : ℕ) :
    PhaseMeanZero (timeJet hT i f) := by
  exact phaseMean_timeJet_eq_zero hT f hf i

private theorem primitive_phaseTranslate {f : ℝ → E} (hf : Continuous f)
    (hper : Function.Periodic f 1) (hzero : phaseMean f = 0) (b : ℝ) :
    phasePrimitive (fun s => f (s + b)) = fun s => phasePrimitive f (s + b) := by
  have hd (s : ℝ) : HasDerivAt (fun r => phasePrimitive f (r + b)) (f (s + b)) s :=
    ((hasDerivAt_phasePrimitive hf (s + b)).scomp s ((hasDerivAt_id s).add_const b)).congr_deriv
      (by simp)
  have h := phasePrimitive_deriv hd (hf.comp (continuous_id.add continuous_const))
  have hm : phaseMean (fun s => phasePrimitive f (s + b)) = 0 := by
    unfold phaseMean
    rw [intervalIntegral.integral_comp_add_right]
    calc
      _ = ∫ s in (0 : ℝ)..1, phasePrimitive f s := by
        simpa only [zero_add, add_comm b (1 : ℝ)] using
          (periodic_phasePrimitive hf hper hzero).intervalIntegral_add_eq b 0
      _ = 0 := phaseMean_phasePrimitive hf
  rw [h]
  funext s
  exact sub_eq_self.mpr hm

omit [CompleteSpace E] in
private theorem phasePrimitive_profile_smooth (hT : 0 < T) (f : HierarchyTwistedProfile T k E) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      phasePrimitive (fun s => f.val.val.val (x.1, x.2.1, s)) x.2.2) (hierarchyProfileSlab T) := by
  let S := Icc (0 : ℝ) T ×ˢ (univ : Set Vec3)
  let F (x : ℝ × Vec3) (s : ℝ) := f.val.val.val (x.1, x.2, s)
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (S ×ˢ (univ : Set ℝ)) :=
    (HierarchySmoothProfile.smooth f.val.val).comp
      (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk contDiffOn_snd))
      (fun _ hz => ⟨hz.1.1, mem_univ _⟩)
  have hP := contDiffOn_phasePrimitive ((convex_Icc (0 : ℝ) T).prod (convex_univ (𝕜 := ℝ)))
    ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) hF
  exact hP.comp ((contDiffOn_fst.prodMk contDiffOn_snd.fst).prodMk contDiffOn_snd.snd)
    (fun _ hz => ⟨⟨hz.1, mem_univ _⟩, mem_univ _⟩)

/-- A normalized primitive of a centered profile preserves its period
and the exact lattice twist. -/
def phasePrimitiveProfile (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (hf : PhaseMeanZero f) : HierarchyTwistedProfile T k E := by
  let F (x : HierarchyProfilePoint) := phasePrimitive (fun s => f.val.val.val (x.1, x.2.1, s)) x.2.2
  let G := HierarchySmoothProfile.ofSmooth F (phasePrimitive_profile_smooth hT f)
  have he {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) : G.val (t, a, s) = F (t, a, s) :=
    HierarchySmoothProfile.ofSmooth_apply _ ⟨ht, mem_univ _⟩
  have hphase {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) : Continuous (fun s => f.val.val.val (t, a, s)) :=
    continuousOn_univ.mp ((profile_phase_time_continuous f a).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨ht, mem_univ _⟩))
  let H := HierarchyPeriodicProfile.ofPeriodicSlices G fun t ht a s => by
    change G.val (t, a, s + 1) = G.val (t, a, s)
    rw [he ht, he ht]
    exact periodic_phasePrimitive (hphase ht a) (HierarchyPeriodicProfile.phasePeriodic f.val t a)
      (hf t ht a) s
  refine ofTwistedSlices H (fun t ht a s m => ?_)
  let d := latticeVector m
  let b := ⟪k, d⟫_ℝ
  change G.val (t, a + d, s + b) = G.val (t, a, s)
  rw [he ht, he ht]
  change phasePrimitive (fun σ => f.val.val.val (t, a + d, σ)) (s + b) =
    phasePrimitive (fun σ => f.val.val.val (t, a, σ)) s
  rw [← congrFun (primitive_phaseTranslate (hphase ht (a + d))
    (HierarchyPeriodicProfile.phasePeriodic f.val t (a + d)) (hf t ht (a + d)) b) s]
  apply congrArg (fun g => phasePrimitive g s)
  funext σ
  exact twistedSlice f t a σ m

theorem phasePrimitiveProfile_apply (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (hf : PhaseMeanZero f) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (phasePrimitiveProfile hT f hf).val.val.val (t, a, s) =
      phasePrimitive (fun σ => f.val.val.val (t, a, σ)) s :=
  HierarchySmoothProfile.ofSmooth_apply (phasePrimitive_profile_smooth hT f) ⟨ht, mem_univ _⟩

/-- The bundled phase primitive commutes with every closed-slab time jet. -/
theorem timeJet_phasePrimitiveProfile (hT : 0 < T) (i : ℕ) (f : HierarchyTwistedProfile T k E)
    (hf : PhaseMeanZero f) :
    timeJet hT i (phasePrimitiveProfile hT f hf) =
      phasePrimitiveProfile hT (timeJet hT i f) (hf.timeJet hT i) := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, s⟩ hz
  rw [timeJet_apply hT i _ hz.1, phasePrimitiveProfile_apply hT _ _ hz.1]
  have he : EqOn (fun r => (phasePrimitiveProfile hT f hf).val.val.val (r, a, s))
      (fun r => phasePrimitive (fun σ => f.val.val.val (r, a, σ)) s) (Icc 0 T) :=
    fun r hr => phasePrimitiveProfile_apply hT f hf hr a s
  rw [iteratedDerivWithin_congr he hz.1]
  exact iteratedDerivWithin_phasePrimitive_time hT f i hz.1 a s

theorem boundedWeightSeminorm_phasePrimitiveProfile_le (hT : 0 < T)
    (f : HierarchyTwistedProfile T k E) (hf : PhaseMeanZero f)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {B : ℝ}
    (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B) (ell h : ℝ) (n : ℕ) :
    boundedWeightSeminorm False ell h n hT hA τ hτ (phasePrimitiveProfile hT f hf) ≤
      2 * boundedWeightSeminorm False ell h n hT hA τ hτ f := by
  let F := weightedSlices A τ f
  have hper (t : A) (a : Vec3) : Function.Periodic (fun s => F t (a, s)) 1 := by
    intro s
    exact congrArg (fun v : E => τ t • v) (HierarchyPeriodicProfile.phasePeriodic f.val t a s)
  have hmean (t : A) (a : Vec3) : phaseMean (fun s => F t (a, s)) = 0 := by
    change phaseMean (fun s => τ t • f.val.val.val (t, a, s)) = 0
    rw [phaseMean_const_smul, hf t (hA t.property) a, smul_zero]
  have hN := (hierarchyFiniteWordNorm_phasePrimitive_le
    (fun i => hierarchyMixedDirection ell h i 0) n (weightedSlices_smooth hA τ f) hper hmean
    (fun w _ => hierarchyTwistedMixedWord_bddAbove_weighted hT ell h False w f hA τ hτ)).2
  have he : weightedSlices A τ (phasePrimitiveProfile hT f hf) = fun t (x : Vec3 × ℝ) =>
      phasePrimitive (fun s => F t (x.1, s)) x.2 := by
    funext t x
    change τ t • (phasePrimitiveProfile hT f hf).val.val.val (t, x) =
      phasePrimitive (fun s => τ t • f.val.val.val (t, x.1, s)) x.2
    rw [phasePrimitiveProfile_apply hT f hf (hA t.property)]
    simp only [phasePrimitive, phaseOscillation, phaseMean, intervalIntegral.integral_smul, smul_sub]
  rw [boundedWeightSeminorm_apply, boundedWeightSeminorm_apply, he]
  exact hN

end

end TorusEuler.HierarchyTwistedProfile
