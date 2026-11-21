import TorusEuler.HierarchyConcreteCompletion
import TorusEuler.HierarchyConcreteMean
import TorusEuler.HierarchyTwistedProfiles

/-! The concrete curl completion preserves the lattice twist and the
joint reflection of admissible transverse profiles. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace Interval

namespace TorusEuler

private theorem wavePotential_translate_phase (κ : Vec3) {V : ℝ → Vec3}
    (hV : Continuous V) (hper : Function.Periodic V 1) (hmean : phaseMean V = 0) (b : ℝ) :
    wavePotential κ (fun s => V (s + b)) = fun s => wavePotential κ V (s + b) := by
  let I (s : ℝ) := (-(‖κ‖ ^ 2)⁻¹) • cross3 κ (V (s + b))
  have hI : Continuous I := by
    change Continuous (fun s => (-(‖κ‖ ^ 2)⁻¹) • cross3Left κ (V (s + b)))
    exact ((cross3Left κ).continuous.comp (hV.comp (continuous_id.add continuous_const))).const_smul
      (-(‖κ‖ ^ 2)⁻¹ : ℝ)
  have hD (s : ℝ) : HasDerivAt (fun r => wavePotential κ V (r + b)) (I s) s :=
    ((hasDerivAt_wavePotential κ hV (s + b)).scomp s ((hasDerivAt_id s).add_const b))
      |>.congr_deriv (by simp [I])
  have hQm : phaseMean (fun s => wavePotential κ V (s + b)) = 0 := by
    calc
      _ = phaseMean (wavePotential κ V) := by
        unfold phaseMean
        rw [intervalIntegral.integral_comp_add_right]
        simpa only [zero_add, add_comm (1 : ℝ) b] using
          (periodic_wavePotential κ hV hper hmean).intervalIntegral_add_eq b 0
      _ = 0 := phaseMean_wavePotential κ hV
  change phasePrimitive I = _
  rw [phasePrimitive_deriv hD hI]
  funext s
  exact sub_eq_self.mpr hQm

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

private theorem phaseMean_centered_twisted (hT : 0 < T) (V : HierarchyTwistedProfile T k Vec3)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    phaseMean (fun r => (V - profilePhaseAverage hT V).val.val.val (t, a, r)) = 0 := by
  let V₀ := V - profilePhaseAverage hT V
  have hid := congrArg Subtype.val
    (HierarchyPeriodicProfile.profilePhaseAverage_idempotent hT V.val)
  change HierarchySmoothProfile.profilePhaseAverage hT
    (HierarchySmoothProfile.profilePhaseAverage hT V.val.val) =
      HierarchySmoothProfile.profilePhaseAverage hT V.val.val at hid
  have hz : HierarchySmoothProfile.profilePhaseAverage hT V₀.val.val = 0 := by
    change HierarchySmoothProfile.profilePhaseAverage hT
      (V.val.val - HierarchySmoothProfile.profilePhaseAverage hT V.val.val) = 0
    rw [map_sub, hid, sub_self]
  have hpt : (t, a, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  change phaseMean (fun r => V₀.val.val.val (t, a, r)) = 0
  rw [← HierarchySmoothProfile.profilePhaseAverage_apply hT V₀.val.val hpt, hz]
  rfl

/-- The periodic completion preserves the lattice twist of the profile. -/
theorem twistedPeriodic_complete (hT : 0 < T)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)) (κ V : HierarchyTwistedProfile T k Vec3)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0) (n : Fin 3 → ℤ) :
    Function.Periodic (HierarchyPeriodicProfile.complete hT G.val κ.val hκ V.val).val.val
      (hierarchyLatticeShift k n) := by
  let V₀ := V - profilePhaseAverage hT V
  let Q := HierarchySmoothProfile.profileWavePotential hT κ.val.val hκ V₀.val.val
  let C := HierarchySmoothProfile.profileSlowCurl hT G.val.val Q
  change Function.Periodic C.val (hierarchyLatticeShift k n)
  intro x
  by_cases hx : x ∈ hierarchyProfileSlab T
  · rcases x with ⟨t, a, s⟩
    have ht : t ∈ Icc 0 T := hx.1
    let d := latticeVector n
    let c := ⟪k, d⟫_ℝ
    have hQtw (a : Vec3) (s : ℝ) : Q.val (t, a + d, s + c) = Q.val (t, a, s) := by
      have hpt : (t, a + d, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
      have hκtw : κ.val.val.val (t, a + d, 0) = κ.val.val.val (t, a, 0) := by
        rw [← hκPhase _ hpt c]
        simpa only [zero_add] using twistedSlice κ t a 0 n
      let w := fun r => V₀.val.val.val (t, a + d, r)
      have hW : Continuous w :=
        (HierarchySmoothProfile.contDiff_labelPhase_slice V₀.val.val ht).continuous.comp
          (continuous_const.prodMk continuous_id)
      have hTranslate := congrFun
        (wavePotential_translate_phase (κ.val.val.val (t, a + d, 0)) hW
          (HierarchyPeriodicProfile.phasePeriodic V₀.val t (a + d))
          (phaseMean_centered_twisted hT V ht (a + d)) c) s
      change (HierarchySmoothProfile.profileWavePotential hT κ.val.val hκ V₀.val.val).val
        (t, a + d, s + c) = _
      rw [HierarchySmoothProfile.profileWavePotential_apply hT κ.val.val hκ V₀.val.val ht,
        show Q.val (t, a, s) = _ from
          HierarchySmoothProfile.profileWavePotential_apply hT κ.val.val hκ V₀.val.val ht a s,
        ← hTranslate, hκtw]
      exact congrArg (fun f => wavePotential (κ.val.val.val (t, a, 0)) f s)
        (funext fun r => twistedSlice V₀ t a r n)
    have hD : fderiv ℝ (fun b => Q.val (t, b, s + c)) (a + d) =
        fderiv ℝ (fun b => Q.val (t, b, s)) a := by
      rw [← fderiv_comp_add_right d]
      exact congrArg (fun f : Vec3 → Vec3 => fderiv ℝ f a) (funext fun b => hQtw b s)
    rw [add_hierarchyLatticeShift]
    change (HierarchySmoothProfile.profileSlowCurl hT G.val.val Q).val (t, a + d, s + c) =
      (HierarchySmoothProfile.profileSlowCurl hT G.val.val Q).val (t, a, s)
    rw [HierarchySmoothProfile.profileSlowCurl_apply hT G.val.val Q ht,
      HierarchySmoothProfile.profileSlowCurl_apply hT G.val.val Q ht,
      hD, twistedSlice G t a s n]
  · rw [HierarchySmoothProfile.eq_zero_outside C
      (fun h => hx (add_hierarchyLatticeShift_mem_slab.mp h)),
      HierarchySmoothProfile.eq_zero_outside C hx]

end HierarchyTwistedProfile

end TorusEuler

namespace TorusEuler

noncomputable section

private theorem phaseMean_wavePotential_reflect (κ : Vec3) {V : ℝ → Vec3} (hV : Continuous V)
    (hper : Function.Periodic V 1) (hmean : phaseMean V = 0) :
    phaseMean (fun s => wavePotential κ V (-s)) = 0 := by
  have hp := periodic_wavePotential κ hV hper hmean
  calc
    phaseMean (fun s => wavePotential κ V (-s)) = phaseMean (wavePotential κ V) := by
      unfold phaseMean
      rw [intervalIntegral.integral_comp_neg, neg_zero]
      simpa only [neg_add_cancel, zero_add] using hp.intervalIntegral_add_eq (-1) 0
    _ = 0 := phaseMean_wavePotential κ hV

/-- The normalized potential of the reversed, negated velocity is the
reversed potential of the original velocity. -/
theorem wavePotential_neg_reflected (κ : Vec3) {V : ℝ → Vec3} (hV : Continuous V)
    (hper : Function.Periodic V 1) (hmean : phaseMean V = 0) :
    wavePotential κ (fun s => -V (-s)) = fun s => wavePotential κ V (-s) := by
  let D (s : ℝ) := (-(‖κ‖ ^ 2)⁻¹) • cross3 κ (-V (-s))
  have hD : Continuous D := by
    change Continuous (fun s => (-(‖κ‖ ^ 2)⁻¹) • cross3Left κ (-V (-s)))
    exact ((cross3Left κ).continuous.comp (hV.comp continuous_neg).neg).const_smul (-(‖κ‖ ^ 2)⁻¹)
  have hder (s : ℝ) : HasDerivAt (fun r => wavePotential κ V (-r)) (D s) s := by
    refine ((hasDerivAt_wavePotential κ hV (-s)).scomp s (hasDerivAt_neg' s)).congr_deriv ?_
    simp only [D, ← cross3Left_apply, map_neg, neg_one_smul, smul_neg]
  change phasePrimitive D = _
  rw [phasePrimitive_deriv hder hD]
  funext s
  exact sub_eq_self.mpr (phaseMean_wavePotential_reflect κ hV hper hmean)

namespace HierarchySmoothProfile

variable {T : ℝ}

local notation "VP" => HierarchySmoothProfile T Vec3
local notation "VPmap" => HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)

private theorem localReflectionParity_of_onSlab (sign : ℝ) (f : VP)
    (hf : ∀ x ∈ hierarchyProfileSlab T,
      f.val (hierarchyProfileReflection x) = sign • f.val x) :
    HierarchyProfileReflectionParity sign f.val := by
  intro x
  by_cases hx : x ∈ hierarchyProfileSlab T
  · exact hf x hx
  · rw [eq_zero_outside f (fun h => hx (hierarchyProfileReflection_mem_slab.mp h)),
      eq_zero_outside f hx, smul_zero]

/-- The phase primitive reverses the joint reflection sign of the odd input. -/
theorem profileWavePotential_reflectionEven (hT : 0 < T) (κ V : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0)
    (hκeven : HierarchyProfileReflectionParity 1 κ.val)
    (hVodd : HierarchyProfileReflectionParity (-1) V.val)
    (hper : ∀ t ∈ Icc 0 T, ∀ a, Function.Periodic (fun s => V.val (t, a, s)) 1)
    (hmean : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun s => V.val (t, a, s)) = 0) :
    HierarchyProfileReflectionParity 1 (profileWavePotential hT κ hκ V).val := by
  apply localReflectionParity_of_onSlab
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  have hk : κ.val (t, -a, 0) = κ.val (t, a, 0) := by
    simpa only [hierarchyProfileReflection_apply, neg_zero, one_smul] using hκeven (t, a, 0)
  have hV : (fun r => V.val (t, -a, r)) = fun r => -V.val (t, a, -r) := by
    funext r
    simpa only [hierarchyProfileReflection_apply, neg_neg, neg_one_smul] using hVodd (t, a, -r)
  have hVc : Continuous (fun r => V.val (t, a, r)) :=
    (contDiff_labelPhase_slice V ht).continuous.comp (continuous_const.prodMk continuous_id)
  simp only [hierarchyProfileReflection_apply, profileWavePotential_apply hT κ hκ V ht, one_smul]
  rw [hk, hV, wavePotential_neg_reflected _ hVc (hper t ht a) (hmean t ht a)]
  simp only [neg_neg]

/-- A label derivative reverses the joint reflection sign of the even potential. -/
theorem profileSlowCurl_reflectionOdd (hT : 0 < T) (G : VPmap) (Q : VP)
    (hGeven : HierarchyProfileReflectionParity 1 G.val)
    (hQeven : HierarchyProfileReflectionParity 1 Q.val) :
    HierarchyProfileReflectionParity (-1) (profileSlowCurl hT G Q).val := by
  apply localReflectionParity_of_onSlab
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  have hG : G.val (t, -a, -s) = G.val (t, a, s) := by
    simpa only [hierarchyProfileReflection_apply, one_smul] using hGeven (t, a, s)
  have hQ : fderiv ℝ (fun b => Q.val (t, b, -s)) (-a) =
      -fderiv ℝ (fun b => Q.val (t, b, s)) a := by
    apply ContinuousLinearMap.ext
    intro v
    rw [neg_apply, ← profileLabelDerivative Q ht (-a) v (-s),
      ← profileLabelDerivative Q ht a v s]
    simpa only [hierarchyProfileReflection_apply, neg_one_smul] using
      (fderivWithin_hierarchyProfileReflection_of_reversed hT Q hQeven hx
        (d := (0, v, 0)) (by simp))
  simp only [hierarchyProfileReflection_apply, profileSlowCurl_apply hT G Q ht]
  rw [hG, hQ, neg_comp]
  change curlOfDerivativeCLM (-_) = (-1 : ℝ) • curlOfDerivativeCLM _
  rw [map_neg, neg_one_smul]

/-- The actual divergence correction is odd under joint label-phase
reflection when the coframe and covector are even and the input is odd. -/
theorem profileCompletion_reflectionOdd (hT : 0 < T) (G : VPmap) (κ V : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0)
    (hGeven : HierarchyProfileReflectionParity 1 G.val)
    (hκeven : HierarchyProfileReflectionParity 1 κ.val)
    (hVodd : HierarchyProfileReflectionParity (-1) V.val)
    (hper : ∀ t ∈ Icc 0 T, ∀ a, Function.Periodic (fun s => V.val (t, a, s)) 1)
    (hmean : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun s => V.val (t, a, s)) = 0) :
    HierarchyProfileReflectionParity (-1) (profileCompletion hT G κ hκ V).val :=
  profileSlowCurl_reflectionOdd hT G _ hGeven
    (profileWavePotential_reflectionEven hT κ V hκ hκeven hVodd hper hmean)

end HierarchySmoothProfile

namespace HierarchyPeriodicProfile

/-- The periodic completion on admissible zero-mean odd input preserves oddness. -/
theorem complete_reflectionOdd_of_phaseMean_zero {T : ℝ} (hT : 0 < T)
    (G : HierarchyPeriodicProfile T (Vec3 →L[ℝ] Vec3)) (κ V : HierarchyPeriodicProfile T Vec3)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val (t, a, 0) ≠ 0)
    (hGeven : HierarchyProfileReflectionParity 1 G.val.val)
    (hκeven : HierarchyProfileReflectionParity 1 κ.val.val)
    (hVodd : HierarchyProfileReflectionParity (-1) V.val.val)
    (hVmean : profilePhaseAverage hT V = 0) :
    HierarchyProfileReflectionParity (-1) (complete hT G κ hκ V).val.val := by
  rw [complete_val_of_phaseMean_zero hT G κ hκ V hVmean]
  apply HierarchySmoothProfile.profileCompletion_reflectionOdd hT G.val κ.val V.val hκ
    hGeven hκeven hVodd (fun t _ a => phasePeriodic V t a)
  intro t ht a
  have hx : (t, a, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hzero := congrArg (fun f : HierarchyPeriodicProfile T Vec3 => f.val.val (t, a, 0)) hVmean
  change (HierarchySmoothProfile.profilePhaseAverage hT V.val).val (t, a, 0) = 0 at hzero
  rwa [HierarchySmoothProfile.profilePhaseAverage_apply hT V.val hx] at hzero

end HierarchyPeriodicProfile

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "VPmap" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

/-- The same periodic curl completion, restricted to the lattice-compatible
profiles of the finite hierarchy. -/
def complete (hT : 0 < T) (G : VPmap) (κ : VP)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0) (V : VP) : VP :=
  ⟨HierarchyPeriodicProfile.complete hT G.val κ.val hκ V.val,
    fun n => twistedPeriodic_complete hT G κ V hκPhase hκ n⟩

@[simp] theorem complete_val (hT : 0 < T) (G : VPmap) (κ : VP)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0) (V : VP) :
    (complete hT G κ hκPhase hκ V).val =
      HierarchyPeriodicProfile.complete hT G.val κ.val hκ V.val := rfl

theorem complete_val_val_of_phaseMean_zero (hT : 0 < T) (G : VPmap) (κ : VP)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0) (V : VP)
    (hVmean : profilePhaseAverage hT V = 0) :
    (complete hT G κ hκPhase hκ V).val.val =
      HierarchySmoothProfile.profileCompletion hT G.val.val κ.val.val hκ V.val.val :=
  HierarchyPeriodicProfile.complete_val_of_phaseMean_zero hT G.val κ.val hκ V.val
    (congrArg Subtype.val hVmean)

/-- The lattice-compatible correction has zero phase average.
This supplies the completion law of the finite solver. -/
theorem average_complete (hT : 0 < T) (G M : VPmap) (κ : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0) (V : VP) :
    (twistedHierarchyOperators hT G M κ).average (complete hT G κ hκPhase hκ V) = 0 :=
  Subtype.ext (HierarchyPeriodicProfile.average_complete hT G.val M.val κ.val hGPhase hκ V.val)

/-- The completed transverse profile retains joint oddness under the
even coframe and covector of an odd parent. -/
theorem complete_reflectionOdd_of_phaseMean_zero (hT : 0 < T) (G : VPmap) (κ : VP)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0) (V : VP)
    (hGeven : HierarchyProfileReflectionParity 1 G.val.val.val)
    (hκeven : HierarchyProfileReflectionParity 1 κ.val.val.val)
    (hVodd : HierarchyProfileReflectionParity (-1) V.val.val.val)
    (hVmean : profilePhaseAverage hT V = 0) :
    HierarchyProfileReflectionParity (-1) (complete hT G κ hκPhase hκ V).val.val.val :=
  HierarchyPeriodicProfile.complete_reflectionOdd_of_phaseMean_zero hT G.val κ.val V.val
    hκ hGeven hκeven hVodd (congrArg Subtype.val hVmean)

end HierarchyTwistedProfile

end

end TorusEuler
