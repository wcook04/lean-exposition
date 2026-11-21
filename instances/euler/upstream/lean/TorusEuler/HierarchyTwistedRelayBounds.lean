import TorusEuler.HierarchyTwistedSourceCancellation
import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchyLinearRelayBounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The weighted linear relay on the actual closed slab of twisted profiles. -/

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Interval Topology

namespace TorusEuler

/-- The closed-slab time derivative of the relay label jet is the label jet
of the potential-time profile. -/
theorem hasDerivWithinAt_relayLabelJet_of_smoothProfile
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (Q : HierarchySmoothProfile T Vec3) {Qt : Vec3 × ℝ → Vec3}
    (hQt : ∀ y, HasDerivWithinAt (fun r => Q.val (r, y)) (Qt y) (Icc 0 T) t)
    (x : Vec3 × ℝ) :
    HasDerivWithinAt (fun r => hierarchyRelayLabelJet (fun y => Q.val (r, y)) x)
      (hierarchyRelayLabelJet Qt x) (Icc 0 T) t := by
  let D := hierarchyProfileSlab T
  let dQ := fderivWithin ℝ Q.val D
  let d₂Q := fderivWithin ℝ dQ D (t, x)
  let eₜ : HierarchyProfilePoint := (1, 0)
  let space := inr ℝ ℝ (Vec3 × ℝ)
  let label := space.comp (inl ℝ Vec3 ℝ)
  let timePart := ContinuousLinearMap.apply ℝ Vec3 eₜ
  let labelPart := (compL ℝ Vec3 HierarchyProfilePoint Vec3).flip label
  have hI := uniqueDiffOn_Icc hT
  have hD := uniqueDiffOn_hierarchyProfileSlab hT
  have hpoint : (t, x) ∈ D := ⟨ht, mem_univ _⟩
  have hAccum : (t, x) ∈ closure (interior D) := by
    rw [show D = Icc 0 T ×ˢ (univ : Set (Vec3 × ℝ)) from rfl, interior_prod_eq, closure_prod_eq,
      interior_univ, closure_univ, closure_interior_Icc hT.ne]
    exact hpoint
  have hQ : ContDiffOn ℝ 2 Q.val D := (HierarchySmoothProfile.smooth Q).of_le (by simp)
  have hSym : ∀ v w, d₂Q v w = d₂Q w v :=
    (hQ _ hpoint).isSymmSndFDerivWithinAt (by rw [minSmoothness_of_isRCLikeNormedField])
      hD hAccum hpoint
  have hDQ (r : ℝ) (hr : r ∈ Icc 0 T) (y : Vec3 × ℝ) :
      HasFDerivWithinAt Q.val (dQ (r, y)) D (r, y) :=
    (hQ.differentiableOn (by norm_num) _ ⟨hr, mem_univ y⟩).hasFDerivWithinAt
  have hD₂Q : HasFDerivWithinAt dQ d₂Q D (t, x) :=
    ((hQ.fderivWithin hD (m := 1) (by norm_num)).differentiableOn
      (by norm_num) _ hpoint).hasFDerivWithinAt
  have hlabel (r : ℝ) (hr : r ∈ Icc 0 T) :
      hierarchyRelayLabelJet (fun y => Q.val (r, y)) x = labelPart (dQ (r, x)) := by
    have hs := (hDQ r hr x).comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) r x)
      (Eventually.of_forall fun y => ⟨hr, mem_univ y⟩)
    change (fderiv ℝ (Q.val ∘ Prod.mk r) x).comp (inl ℝ Vec3 ℝ) = labelPart (dQ (r, x))
    rw [hs.fderiv]
    rfl
  have hMaps (y : Vec3 × ℝ) : MapsTo (fun r : ℝ => (r, y)) (Icc 0 T) D :=
    fun _ hr => ⟨hr, mem_univ y⟩
  have htime (y : Vec3 × ℝ) : Qt y = timePart (dQ (t, y)) := by
    have hv := (hDQ t ht y).comp_hasDerivWithinAt t
      ((hasDerivWithinAt_id t (Icc 0 T)).prodMk (hasDerivWithinAt_const t (Icc 0 T) y))
      (hMaps y)
    exact ((hQt y).derivWithin (hI t ht)).symm.trans (hv.derivWithin (hI t ht))
  have hD₂space := hD₂Q.comp_hasFDerivAt x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
    (Eventually.of_forall fun y => ⟨ht, mem_univ y⟩)
  have hQt' : HasFDerivAt Qt (timePart.comp (d₂Q.comp space)) x :=
    (timePart.hasFDerivAt.comp x hD₂space).congr_of_eventuallyEq
      (Eventually.of_forall htime)
  have hD₂time := hD₂Q.comp_hasDerivWithinAt t
    ((hasDerivWithinAt_id t (Icc 0 T)).prodMk (hasDerivWithinAt_const t (Icc 0 T) x))
    (hMaps x)
  have hJet : HasDerivWithinAt
      (fun r => hierarchyRelayLabelJet (fun y => Q.val (r, y)) x)
      (labelPart (d₂Q eₜ)) (Icc 0 T) t :=
    (labelPart.hasFDerivAt.comp_hasDerivWithinAt t hD₂time).congr_of_mem hlabel ht
  refine hJet.congr_deriv ?_
  rw [hierarchyRelayLabelJet, hQt'.fderiv]
  exact ContinuousLinearMap.ext fun v => hSym eₜ (0, v, 0)


private theorem relayPrimitive_const_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℝ) (f : ℝ → E) (s : ℝ) :
    phasePrimitive (fun σ => r • f σ) s = r • phasePrimitive f s := by
  simp only [phasePrimitive, phaseOscillation, intervalIntegral.integral_smul,
    phaseMean_const_smul, smul_sub]

/-- A scalar constant on the label and phase variables passes through the
potential of the relay. -/
theorem relayPotentialProfile_const_smul (r : ℝ) (k : Vec3 → Vec3)
    (V : Vec3 × ℝ → Vec3) :
    relayPotentialProfile k (fun x => r • V x) = fun x => r • relayPotentialProfile k V x := by
  funext x
  change phasePrimitive (fun s => hierarchyRelayPotentialCoefficient (k x.1)
    (r • V (x.1, s))) x.2 =
    r • phasePrimitive (fun s => hierarchyRelayPotentialCoefficient (k x.1) (V (x.1, s))) x.2
  simp only [map_smul, relayPrimitive_const_smul]

/-- The potential-time source depends linearly on the simultaneous
normalization of the velocity and forcing. -/
theorem relayPotentialTimeProfile_const_smul (r : ℝ)
    (M : Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3 → Vec3) (V F : Vec3 × ℝ → Vec3) :
    relayPotentialTimeProfile M k (fun x => r • V x) (fun x => r • F x) =
      fun x => r • relayPotentialTimeProfile M k V F x := by
  funext x
  simp only [relayPotentialTimeProfile, wavePotentialTimeSource_eq_coefficients,
    map_smul, ← smul_add, relayPrimitive_const_smul]

/-- The normalized pressure is linear in the simultaneous normalization
of the velocity and forcing. -/
theorem relayPhasePressureProfile_const_smul (r : ℝ)
    (M : Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3 → Vec3) (V F : Vec3 × ℝ → Vec3) :
    relayPhasePressureProfile M k (fun x => r • V x) (fun x => r • F x) =
      fun x => r • relayPhasePressureProfile M k V F x := by
  funext x
  simp only [relayPhasePressureProfile, oscillatoryPhasePressure, oscillatoryPressureSlope_eq_coefficients,
    map_smul, ← smul_add, relayPrimitive_const_smul]

/-- At each time the weight can multiply the two input slices before the
normalized relay is formed. No derivative differentiates the time weight. -/
theorem hierarchyLinearRelayAt_input_const_smul (r : ℝ)
    (G : Vec3 →L[ℝ] Vec3) (M : Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3 → Vec3)
    (V F : Vec3 × ℝ → Vec3) (x : Vec3 × ℝ) :
    hierarchyLinearRelayAt G (M x.1)
      (relayPotentialProfile k (fun y => r • V y))
      (relayPotentialTimeProfile M k (fun y => r • V y) (fun y => r • F y))
      (relayPhasePressureProfile M k (fun y => r • V y) (fun y => r • F y)) x =
    r • hierarchyLinearRelayAt G (M x.1) (relayPotentialProfile k V)
      (relayPotentialTimeProfile M k V F) (relayPhasePressureProfile M k V F) x := by
  rw [relayPotentialProfile_const_smul, relayPotentialTimeProfile_const_smul,
    relayPhasePressureProfile_const_smul]
  change hierarchyLinearRelayAt G (M x.1) (r • relayPotentialProfile k V)
      (r • relayPotentialTimeProfile M k V F) (r • relayPhasePressureProfile M k V F) x = _
  rw [hierarchyLinearRelayAt_eq_coordinate_sum one_ne_zero 1,
    hierarchyLinearRelayAt_eq_coordinate_sum one_ne_zero 1, Finset.smul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp only [phaseDirectionalDerivative, fderiv_const_smul_field, Pi.smul_apply, _root_.smul_apply,
    map_smul, smul_add]


private theorem relayPrimitive_add_continuous {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) (s : ℝ) :
    phasePrimitive (fun a => f a + g a) s = phasePrimitive f s + phasePrimitive g s := by
  have heq : (fun a => ∫ b in (0 : ℝ)..a, f b + g b) =
      fun a => (∫ b in (0 : ℝ)..a, f b) + (∫ b in (0 : ℝ)..a, g b) := by
    funext a
    exact intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
  unfold phasePrimitive phaseOscillation
  rw [heq, phaseMean_add
    (intervalIntegral.continuous_primitive hf.intervalIntegrable 0)
    (intervalIntegral.continuous_primitive hg.intervalIntegrable 0)]
  abel_nf
  ac_rfl

private theorem relayPotentialTimeProfile_add_forcing
    (M : Vec3 → Vec3 →L[ℝ] Vec3) (κ : Vec3 → Vec3) {V F : Vec3 × ℝ → Vec3}
    (hV : Continuous V) (hF : Continuous F) :
    relayPotentialTimeProfile M κ V F =
      fun x => relayPotentialTimeProfile M κ V (fun _ => 0) x + relayPotentialProfile κ F x := by
  funext x
  have hVc : Continuous (fun s => V (x.1, s)) :=
    hV.comp (continuous_const.prodMk continuous_id)
  have hFc : Continuous (fun s => F (x.1, s)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  change phasePrimitive (fun s => wavePotentialTimeSource (M x.1) (κ x.1)
    (V (x.1, s)) (F (x.1, s))) x.2 =
      phasePrimitive (fun s => wavePotentialTimeSource (M x.1) (κ x.1)
        (V (x.1, s)) 0) x.2 +
      phasePrimitive (fun s => hierarchyRelayPotentialCoefficient (κ x.1) (F (x.1, s))) x.2
  simp only [wavePotentialTimeSource_eq_coefficients, map_zero, add_zero]
  exact relayPrimitive_add_continuous
    ((hierarchyRelayTimeAmplitudeCoefficient (M x.1) (κ x.1)).continuous.comp hVc)
    ((hierarchyRelayPotentialCoefficient (κ x.1)).continuous.comp hFc) x.2

private theorem relayPhasePressureProfile_of_transverse_force
    (M : Vec3 → Vec3 →L[ℝ] Vec3) (κ : Vec3 → Vec3) (V F : Vec3 × ℝ → Vec3)
    (hperp : ∀ x, ⟪κ x.1, F x⟫_ℝ = 0) :
    relayPhasePressureProfile M κ V F = relayPhasePressureProfile M κ V (fun _ => 0) := by
  funext x
  unfold relayPhasePressureProfile oscillatoryPhasePressure
  congr 1
  funext s
  simp only [oscillatoryPressureSlope_eq_coefficients, hierarchyRelayPressureSourceCoefficient,
    smul_apply, innerSL_apply_apply, hperp (x.1, s), smul_zero, map_zero, add_zero]

/-- Removing the smooth force potential from the potential-time profile
gives differentiability of the homogeneous potential-time profile. -/
theorem differentiableAt_relayPotentialTimeProfile_zero
    (M : Vec3 → Vec3 →L[ℝ] Vec3) (κ : Vec3 → Vec3)
    {V F : Vec3 × ℝ → Vec3} (hV : Continuous V) (hF : Continuous F)
    (x : Vec3 × ℝ)
    (hQt : DifferentiableAt ℝ (relayPotentialTimeProfile M κ V F) x)
    (hQF : DifferentiableAt ℝ (relayPotentialProfile κ F) x) :
    DifferentiableAt ℝ (relayPotentialTimeProfile M κ V (fun _ => 0)) x := by
  have hEq : (fun y => relayPotentialTimeProfile M κ V F y - relayPotentialProfile κ F y) =
      relayPotentialTimeProfile M κ V (fun _ => 0) := by
    rw [relayPotentialTimeProfile_add_forcing M κ hV hF]
    funext y
    exact add_sub_cancel_right _ _
  rw [← hEq]
  exact hQt.sub hQF

/-- In the linear relay a transverse forcing contributes just its own slow
curl completion. Subtracting that completion leaves the homogeneous relay. -/
theorem hierarchyLinearRelayAt_sub_transverse_force_completion
    (G : Vec3 →L[ℝ] Vec3) (M : Vec3 → Vec3 →L[ℝ] Vec3) (κ : Vec3 → Vec3)
    {V F : Vec3 × ℝ → Vec3} (hV : Continuous V) (hF : Continuous F)
    (hperp : ∀ x, ⟪κ x.1, F x⟫_ℝ = 0)
    (x : Vec3 × ℝ)
    (hQt : DifferentiableAt ℝ (relayPotentialTimeProfile M κ V (fun _ => 0)) x)
    (hQF : DifferentiableAt ℝ (relayPotentialProfile κ F) x) :
    hierarchyLinearRelayAt G (M x.1) (relayPotentialProfile κ V)
      (relayPotentialTimeProfile M κ V F) (relayPhasePressureProfile M κ V F) x -
        curlOfDerivative ((hierarchyRelayLabelJet (relayPotentialProfile κ F) x).comp G) =
      hierarchyLinearRelayAt G (M x.1) (relayPotentialProfile κ V)
        (relayPotentialTimeProfile M κ V (fun _ => 0))
        (relayPhasePressureProfile M κ V (fun _ => 0)) x := by
  rw [relayPotentialTimeProfile_add_forcing M κ hV hF,
    relayPhasePressureProfile_of_transverse_force M κ V F hperp]
  unfold hierarchyLinearRelayAt hierarchyRelayLabelJet
  rw [fderiv_fun_add hQt hQF]
  simp only [add_comp, curlOfDerivative_add]
  abel


end TorusEuler

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

private theorem continuousOn_relayCross3 {X : Type*} [TopologicalSpace X] {S : Set X}
    {u v : X → Vec3} (hu : ContinuousOn u S) (hv : ContinuousOn v S) :
    ContinuousOn (fun x => cross3 (u x) (v x)) S := by
  unfold cross3
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
    (continuousOn_pi.mpr ?_)
  have hu' (i : Fin 3) : ContinuousOn (fun t => (u t).ofLp i) S :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp_continuousOn hu
  have hv' (i : Fin 3) : ContinuousOn (fun t => (v t).ofLp i) S :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp_continuousOn hv
  intro i
  fin_cases i
  · exact ((hu' 1).mul (hv' 2)).sub ((hu' 2).mul (hv' 1))
  · exact ((hu' 2).mul (hv' 0)).sub ((hu' 0).mul (hv' 2))
  · exact ((hu' 0).mul (hv' 1)).sub ((hu' 1).mul (hv' 0))

private theorem contOn_relay_time_phase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchyTwistedProfile T k E) (a : Vec3) :
    ContinuousOn (fun z : ℝ × ℝ => f.val.val.val (z.1, a, z.2)) (Icc 0 T ×ˢ univ) :=
  (HierarchySmoothProfile.smooth f.val.val).continuousOn.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

private theorem continuousOn_relay_time_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : HierarchyTwistedProfile T k E) (a : Vec3) :
    ContinuousOn (fun z : ℝ × ℝ => f.val.val.val (z.1, a, 0)) (Icc 0 T ×ˢ univ) :=
  (HierarchySmoothProfile.smooth f.val.val).continuousOn.comp
    (continuous_fst.prodMk continuous_const).continuousOn
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

/-- Differentiating the actual normalized potential in time removes the phase
pressure from the integrand, since that term is parallel to the covector. -/
theorem profileWavePotential_time_of_transverse_on (hT : 0 < T) (M : MP) (κ V F : VP) (p : SP)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hVdot : ∀ t ∈ Icc t₀ T, ∀ a s, HasDerivWithinAt
      (fun r => V.val.val.val (r, a, s))
      (F.val.val.val (t, a, s) - M.val.val.val (t, a, 0) (V.val.val.val (t, a, s)) -
        deriv (fun r => p.val.val.val (t, a, r)) s • κ.val.val.val (t, a, 0)) (Icc t₀ T) t)
    {t : ℝ} (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt
      (fun r => (HierarchySmoothProfile.profileWavePotential hT κ.val.val hκ V.val.val).val (r, a, s))
      (relayPotentialTimeProfile (fun b => M.val.val.val (t, b, 0))
        (fun b => κ.val.val.val (t, b, 0)) (fun x => V.val.val.val (t, x))
        (fun x => F.val.val.val (t, x)) (a, s)) (Icc t₀ T) t := by
  let K (r : ℝ) := κ.val.val.val (r, a, 0)
  let Str (r : ℝ) := M.val.val.val (r, a, 0)
  let W (r s : ℝ) := V.val.val.val (r, a, s)
  let f (r s : ℝ) := F.val.val.val (r, a, s)
  let q (r σ : ℝ) := deriv (fun r' => p.val.val.val (r, a, r')) σ
  let I := Icc t₀ T ×ˢ (univ : Set ℝ)
  have hI : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hK : ContinuousOn (fun z : ℝ × ℝ => K z.1) I := (continuousOn_relay_time_zero κ a).mono (prod_mono hI le_rfl)
  have hM : ContinuousOn (fun z : ℝ × ℝ => Str z.1) I := (continuousOn_relay_time_zero M a).mono (prod_mono hI le_rfl)
  have hV : ContinuousOn (fun z : ℝ × ℝ => W z.1 z.2) I := (contOn_relay_time_phase V a).mono (prod_mono hI le_rfl)
  have hF : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) I := (contOn_relay_time_phase F a).mono (prod_mono hI le_rfl)
  have hkn : ∀ z ∈ I, ‖K z.1‖ ^ 2 ≠ 0 :=
    fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκ z.1 (hI hz.1) a))
  have hInv : ContinuousOn (fun z : ℝ × ℝ => (‖K z.1‖ ^ 2)⁻¹) I :=
    (hK.norm.pow 2).inv₀ hkn
  have hCross := continuousOn_relayCross3 hK hV
  have hA := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).continuous.comp_continuousOn hM
  have hSource : ContinuousOn (fun z : ℝ × ℝ =>
      wavePotentialTimeSource (Str z.1) (K z.1) (W z.1 z.2) (f z.1 z.2)) I := by
    have hin : ContinuousOn (fun z : ℝ × ℝ => ⟪K z.1, Str z.1 (K z.1)⟫_ℝ) I :=
      hK.inner (hM.clm_apply hK)
    unfold wavePotentialTimeSource
    exact (hInv.smul (((continuousOn_relayCross3 (hA.clm_apply hK) hV).add
      (continuousOn_relayCross3 hK (hM.clm_apply hV))).sub (continuousOn_relayCross3 hK hF))).sub
      (((continuousOn_const.mul hin).div ((hK.norm.pow 2).pow 2)
        (fun z hz => pow_ne_zero 2 (hkn z hz))).smul hCross)
  have htime := hasDerivWithinAt_wavePotential_time (κ := K) (V := W) (f := f) (q := q) (M := Str)
    ht (fun u hu => hκ u (hI hu) a) (fun u hu => (hκdot u (hI hu) a).mono hI) (fun u hu σ => hVdot u hu a σ)
    (hInv.neg.smul hCross) hSource s
  exact htime.congr_of_mem (fun u hu =>
    HierarchySmoothProfile.profileWavePotential_apply hT κ.val.val hκ V.val.val (hI hu) a s) ht

theorem profileWavePotential_time_of_transverse (hT : 0 < T) (M : MP) (κ V F : VP) (p : SP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hVdot : ∀ t ∈ Icc 0 T, ∀ a s, HasDerivWithinAt
      (fun r => V.val.val.val (r, a, s))
      (F.val.val.val (t, a, s) - M.val.val.val (t, a, 0) (V.val.val.val (t, a, s)) -
        deriv (fun r => p.val.val.val (t, a, r)) s • κ.val.val.val (t, a, 0)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt
      (fun r => (HierarchySmoothProfile.profileWavePotential hT κ.val.val hκ V.val.val).val (r, a, s))
      (relayPotentialTimeProfile (fun b => M.val.val.val (t, b, 0))
        (fun b => κ.val.val.val (t, b, 0)) (fun x => V.val.val.val (t, x))
        (fun x => F.val.val.val (t, x)) (a, s)) (Icc 0 T) t :=
  profileWavePotential_time_of_transverse_on hT M κ V F p le_rfl hκ hκdot hVdot ht a s

private theorem relayLabelJet_eq_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec3 × ℝ → E} {a : Vec3} {s : ℝ} (hf : DifferentiableAt ℝ f (a, s)) :
    hierarchyRelayLabelJet f (a, s) = fderiv ℝ (fun b => f (b, s)) a := by
  rw [hierarchyRelayLabelJet, (hasFDerivAt_profile_partials hf).fderiv]
  ext v
  simp

/-- The fixed-time formula for the four slow relay terms, with the actual
transported covector and the genuine phase profiles. -/
def waveRelayAt (G M : MP) (κ V F : VP) (t : ℝ) (x : Vec3 × ℝ) : Vec3 :=
  let K (a : Vec3) := κ.val.val.val (t, a, 0)
  let Str (a : Vec3) := M.val.val.val (t, a, 0)
  let v (y : Vec3 × ℝ) := V.val.val.val (t, y)
  let f (y : Vec3 × ℝ) := F.val.val.val (t, y)
  hierarchyLinearRelayAt (G.val.val.val (t, x.1, 0)) (Str x.1)
    (relayPotentialProfile K v) (relayPotentialTimeProfile Str K v f)
    (relayPhasePressureProfile Str K v f) x

set_option maxHeartbeats 1000000 in
/-- The actual material derivative of the periodic curl completion plus the
label pressure gradient equals the four terms of the slow relay. -/
theorem material_complete_add_labelGrad_apply_relay_on (hT : 0 < T)
    (G M : MP) (κ V F : VP) (p : SP)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hstart : t₀ < T)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hMPhase : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hVmean : profilePhaseAverage hT V = 0)
    (hGdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun r => G.val.val.val (r, a, 0))
        (-((G.val.val.val (t, a, 0)).comp (M.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hVdot : ∀ t ∈ Icc t₀ T, ∀ a s, HasDerivWithinAt
      (fun r => V.val.val.val (r, a, s))
      (F.val.val.val (t, a, s) - M.val.val.val (t, a, 0) (V.val.val.val (t, a, s)) -
        deriv (fun r => p.val.val.val (t, a, r)) s • κ.val.val.val (t, a, 0)) (Icc t₀ T) t)
    (hp : ∀ t ∈ Icc t₀ T, ∀ a s,
      p.val.val.val (t, a, s) = oscillatoryPhasePressure
        (M.val.val.val (t, a, 0)) (κ.val.val.val (t, a, 0))
        (fun r => F.val.val.val (t, a, r)) (fun r => V.val.val.val (t, a, r)) s)
    {t : ℝ} (hta : t ∈ Icc t₀ T) (x : Vec3 × ℝ) :
    let ops := twistedHierarchyOperators hT G M κ
    (ops.material (complete hT G κ hκPhase hκ V) + ops.labelGrad p).val.val.val (t, x) =
      waveRelayAt G M κ V F t x := by
  have hIactive : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have ht := hIactive hta
  let ops := twistedHierarchyOperators hT G M κ
  let Q := HierarchySmoothProfile.profileWavePotential hT κ.val.val hκ V.val.val
  let C := complete hT G κ hκPhase hκ V
  let D (r : ℝ) := G.val.val.val (r, x.1, 0)
  let Str (r : ℝ) (a : Vec3) := M.val.val.val (r, a, 0)
  let K (r : ℝ) (a : Vec3) := κ.val.val.val (r, a, 0)
  let v (r : ℝ) (y : Vec3 × ℝ) := V.val.val.val (r, y)
  let f (r : ℝ) (y : Vec3 × ℝ) := F.val.val.val (r, y)
  let Qt := relayPotentialTimeProfile (Str t) (K t) (v t) (f t)
  let P := relayPhasePressureProfile (Str t) (K t) (v t) (f t)
  have hx : (t, x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hQ (r : ℝ) (hr : r ∈ Icc 0 T) :
      (fun y => Q.val (r, y)) = relayPotentialProfile (K r) (v r) := by
    funext y
    exact HierarchySmoothProfile.profileWavePotential_apply hT κ.val.val hκ V.val.val hr y.1 y.2
  have hP : (fun y => p.val.val.val (t, y)) = P := funext fun y => hp t hta y.1 y.2
  have hC (r : ℝ) (hr : r ∈ Icc 0 T) :
      C.val.val.val (r, x) =
        curlOfDerivative ((hierarchyRelayLabelJet (fun y => Q.val (r, y)) x).comp (D r)) := by
    change (complete hT G κ hκPhase hκ V).val.val.val (r, x) = _
    rw [complete_val_val_of_phaseMean_zero hT G κ hκPhase hκ V hVmean]
    change (HierarchySmoothProfile.profileSlowCurl hT G.val.val Q).val (r, x.1, x.2) = _
    rw [HierarchySmoothProfile.profileSlowCurl_apply hT G.val.val Q hr,
      hGPhase (r, x.1, 0) ⟨hr, mem_univ _⟩ x.2,
      relayLabelJet_eq_slice ((HierarchySmoothProfile.contDiff_labelPhase_slice Q hr).differentiable
        (by simp) x)]
  have hTQt (y : Vec3 × ℝ) : HasDerivWithinAt (fun r => Q.val (r, y)) (Qt y) (Icc 0 T) t := by
    have hActive := profileWavePotential_time_of_transverse_on hT M κ V F p ht₀ hκ hκdot hVdot hta y.1 y.2
    have hFull := HierarchySmoothProfile.hasDerivWithinAt_profileTime Q ht y.1 y.2
    have hUnique := uniqueDiffOn_Icc hstart t hta
    exact hFull.congr_deriv (((hFull.mono hIactive).derivWithin hUnique).symm.trans
      (hActive.derivWithin hUnique))
  have hJ := hasDerivWithinAt_relayLabelJet_of_smoothProfile hT ht Q hTQt x
  have hCurlTime := hasDerivWithinAt_pulledBackCurl hJ (hGdot t ht x.1)
  have hI := uniqueDiffOn_Icc hT t ht
  have hct :
      fderivWithin ℝ C.val.val.val (hierarchyProfileSlab T) (t, x) (1, 0, 0) =
        derivWithin (fun r =>
          curlOfDerivative ((hierarchyRelayLabelJet (fun y => Q.val (r, y)) x).comp (D r))) (Icc 0 T) t := by
    exact ((HierarchySmoothProfile.hasDerivWithinAt_profileTime C.val.val ht x.1 x.2).derivWithin hI).symm.trans
      ((hCurlTime.congr_of_mem hC ht).derivWithin hI |>.trans (hCurlTime.derivWithin hI).symm)
  have hpJet : fderiv ℝ (fun b => p.val.val.val (t, b, x.2)) x.1 =
      hierarchyRelayLabelJet P x := by
    rw [← hP, relayLabelJet_eq_slice
      ((HierarchySmoothProfile.contDiff_labelPhase_slice p.val.val ht).differentiable (by simp) x)]
  change ((HierarchySmoothProfile.hierarchyConcreteOperators hT G.val.val M.val.val
    κ.val.val).material C.val.val).val (t, x) +
      (HierarchySmoothProfile.labelGradient hT G.val.val p.val.val).val (t, x) = _
  rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT _ _ _ _ hx,
    HierarchySmoothProfile.labelGradient_eq_adjoint_gradient hT _ _ ht x.1 x.2,
    hMPhase (t, x.1, 0) ⟨ht, mem_univ _⟩ x.2,
    hGPhase (t, x.1, 0) ⟨ht, mem_univ _⟩ x.2,
    hct, hC t ht, gradient, hpJet]
  change _ = hierarchyLinearRelayAt (D t) (Str t x.1) (relayPotentialProfile (K t) (v t)) Qt P x
  rw [← hQ t ht]
  exact derivWithin_waveCompletion_add_pressure hI hJ (hGdot t ht x.1)

theorem material_complete_add_labelGrad_apply_relay (hT : 0 < T)
    (G M : MP) (κ V F : VP) (p : SP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hMPhase : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hVmean : profilePhaseAverage hT V = 0)
    (hGdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun r => G.val.val.val (r, a, 0))
        (-((G.val.val.val (t, a, 0)).comp (M.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hVdot : ∀ t ∈ Icc 0 T, ∀ a s, HasDerivWithinAt
      (fun r => V.val.val.val (r, a, s))
      (F.val.val.val (t, a, s) - M.val.val.val (t, a, 0) (V.val.val.val (t, a, s)) -
        deriv (fun r => p.val.val.val (t, a, r)) s • κ.val.val.val (t, a, 0)) (Icc 0 T) t)
    (hp : ∀ t ∈ Icc 0 T, ∀ a s,
      p.val.val.val (t, a, s) = oscillatoryPhasePressure
        (M.val.val.val (t, a, 0)) (κ.val.val.val (t, a, 0))
        (fun r => F.val.val.val (t, a, r)) (fun r => V.val.val.val (t, a, r)) s)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    let ops := twistedHierarchyOperators hT G M κ
    (ops.material (complete hT G κ hκPhase hκ V) + ops.labelGrad p).val.val.val (t, x) =
      waveRelayAt G M κ V F t x :=
  material_complete_add_labelGrad_apply_relay_on hT G M κ V F p le_rfl hT hGPhase hMPhase hκPhase
    hκ hVmean hGdot hκdot hVdot hp ht x

/-- The twisted momentum identity gives the scalar-time transverse ODE on
each fixed label and phase, including at both endpoints of the slab. -/
theorem velocity_equation_of_twisted_momentum_at (hT : 0 < T) (G M : MP)
    (κ V F : VP) (p : SP)
    (hM : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκ : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ)
    (hmomentum : let ops := twistedHierarchyOperators hT G M κ
      (ops.material V + ops.phaseGrad p).val.val.val (t, a, s) = F.val.val.val (t, a, s)) :
    HasDerivWithinAt (fun r => V.val.val.val (r, a, s))
      (F.val.val.val (t, a, s) - M.val.val.val (t, a, 0) (V.val.val.val (t, a, s)) -
        deriv (fun r => p.val.val.val (t, a, r)) s • κ.val.val.val (t, a, 0)) (Icc 0 T) t := by
  let ops := HierarchySmoothProfile.hierarchyConcreteOperators hT G.val.val M.val.val κ.val.val
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hm := hmomentum
  change (ops.material V.val.val).val (t, a, s) +
    (HierarchySmoothProfile.phaseGradient hT κ.val.val p.val.val).val (t, a, s) =
    F.val.val.val (t, a, s) at hm
  rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT _ _ _ _ hx,
    HierarchySmoothProfile.phaseGradient_apply hT _ _ hx,
    hM (t, a, 0) ⟨ht, mem_univ _⟩ s, hκ (t, a, 0) ⟨ht, mem_univ _⟩ s,
    ← (HierarchySmoothProfile.hasDerivAt_profilePhase p.val.val ht a s).deriv] at hm
  apply (HierarchySmoothProfile.hasDerivWithinAt_profileTime V.val.val ht a s).congr_deriv
  rw [← hm]
  abel

theorem velocity_equation_of_twisted_momentum (hT : 0 < T) (G M : MP)
    (κ V F : VP) (p : SP)
    (hM : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκ : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hmomentum : let ops := twistedHierarchyOperators hT G M κ
      ops.material V + ops.phaseGrad p = F)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt (fun r => V.val.val.val (r, a, s))
      (F.val.val.val (t, a, s) - M.val.val.val (t, a, 0) (V.val.val.val (t, a, s)) -
        deriv (fun r => p.val.val.val (t, a, r)) s • κ.val.val.val (t, a, 0)) (Icc 0 T) t :=
  velocity_equation_of_twisted_momentum_at hT G M κ V F p hM hκ ht a s
    (congrArg (fun v : VP => v.val.val.val (t, a, s)) hmomentum)

/-- The normalized phase pressure is forced by transversality and the
twisted momentum equation. This includes the switched leading wave. -/
theorem phasePressure_value_of_twisted_momentum_on (hT : 0 < T) (G M : MP)
    (κ V F : VP) (p : SP)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hstart : t₀ < T)
    (hM : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (htrans : ∀ t ∈ Icc t₀ T, ∀ a s, ⟪κ.val.val.val (t, a, 0), V.val.val.val (t, a, s)⟫_ℝ = 0)
    (hpMean : ∀ t ∈ Icc t₀ T, ∀ a, phaseMean (fun r => p.val.val.val (t, a, r)) = 0)
    (hmomentum : let ops := twistedHierarchyOperators hT G M κ
      ∀ t ∈ Icc t₀ T, ∀ a s, (ops.material V + ops.phaseGrad p).val.val.val (t, a, s) =
        F.val.val.val (t, a, s))
    {t : ℝ} (hta : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    p.val.val.val (t, a, s) =
      oscillatoryPhasePressure (M.val.val.val (t, a, 0)) (κ.val.val.val (t, a, 0))
        (fun r => F.val.val.val (t, a, r)) (fun r => V.val.val.val (t, a, r)) s := by
  have hIactive : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have ht := hIactive hta
  let K := κ.val.val.val (t, a, 0)
  let Str := M.val.val.val (t, a, 0)
  let p₀ (r : ℝ) := p.val.val.val (t, a, r)
  let v (r : ℝ) := V.val.val.val (t, a, r)
  let f (r : ℝ) := F.val.val.val (t, a, r)
  let D (r : ℝ) := oscillatoryPressureSlope Str K (f r) (v r)
  have hD (r : ℝ) : deriv p₀ r = D r := by
    have hv := velocity_equation_of_twisted_momentum_at hT G M κ V F p hM hκPhase ht a r
      (hmomentum t hta a r)
    have hvκ := ((hκdot t ht a).inner ℝ hv).mono hIactive
    have hz : HasDerivWithinAt
        (fun u => ⟪κ.val.val.val (u, a, 0), V.val.val.val (u, a, r)⟫_ℝ) 0 (Icc t₀ T) t :=
      (hasDerivWithinAt_const t (Icc t₀ T) (0 : ℝ)).congr_of_mem
        (fun u hu => htrans u hu a r) hta
    have hh := (hvκ.derivWithin (uniqueDiffOn_Icc hstart t hta)).symm.trans
      (hz.derivWithin (uniqueDiffOn_Icc hstart t hta))
    change ⟪K, f r - Str (v r) - deriv p₀ r • K⟫_ℝ + ⟪-(Str.adjoint K), v r⟫_ℝ = 0 at hh
    rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_neg_left,
      ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq] at hh
    change deriv p₀ r = (⟪K, f r⟫_ℝ - 2 * ⟪K, Str (v r)⟫_ℝ) / ‖K‖ ^ 2
    apply (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκ t ht a)))).2
    linarith
  have hpSmooth : ContDiff ℝ ∞ p₀ :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice p.val.val ht).comp
      (contDiff_const.prodMk contDiff_id)
  have hCont : Continuous D := by
    rw [← funext hD]
    exact hpSmooth.continuous_deriv (by simp)
  have hDer (r : ℝ) : HasDerivAt p₀ (D r) r :=
    (hpSmooth.differentiable (by simp) r).hasDerivAt.congr_deriv (hD r)
  change p₀ s = phasePrimitive D s
  rw [phasePrimitive_deriv hDer hCont, phaseOscillation, hpMean t hta a, sub_zero]

theorem phasePressure_value_of_twisted_momentum (hT : 0 < T) (G M : MP)
    (κ V F : VP) (p : SP)
    (hM : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (htrans : ∀ t ∈ Icc 0 T, ∀ a s, ⟪κ.val.val.val (t, a, 0), V.val.val.val (t, a, s)⟫_ℝ = 0)
    (hpMean : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun r => p.val.val.val (t, a, r)) = 0)
    (hmomentum : let ops := twistedHierarchyOperators hT G M κ
      ops.material V + ops.phaseGrad p = F)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    p.val.val.val (t, a, s) =
      oscillatoryPhasePressure (M.val.val.val (t, a, 0)) (κ.val.val.val (t, a, 0))
        (fun r => F.val.val.val (t, a, r)) (fun r => V.val.val.val (t, a, r)) s :=
  phasePressure_value_of_twisted_momentum_on hT G M κ V F p le_rfl hT hM hκPhase hκ hκdot htrans hpMean
    (fun t _ a s => congrArg (fun v : VP => v.val.val.val (t, a, s)) hmomentum) ht a s

/-- The actual centered completion evaluates to the pulled-back curl of
its normalized potential. -/
theorem complete_apply_relayPotential (hT : 0 < T) (G : MP) (κ V : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hVmean : profilePhaseAverage hT V = 0) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (complete hT G κ hκPhase hκ V).val.val.val (t, x) =
      curlOfDerivative ((hierarchyRelayLabelJet
        (relayPotentialProfile (fun b => κ.val.val.val (t, b, 0))
          (fun y => V.val.val.val (t, y))) x).comp (G.val.val.val (t, x.1, 0))) := by
  let Q := HierarchySmoothProfile.profileWavePotential hT κ.val.val hκ V.val.val
  have hQ : (fun y => Q.val (t, y)) =
      relayPotentialProfile (fun b => κ.val.val.val (t, b, 0)) (fun y => V.val.val.val (t, y)) :=
    funext fun y => HierarchySmoothProfile.profileWavePotential_apply hT κ.val.val hκ V.val.val ht y.1 y.2
  rw [complete_val_val_of_phaseMean_zero hT G κ hκPhase hκ V hVmean]
  change (HierarchySmoothProfile.profileSlowCurl hT G.val.val Q).val (t, x.1, x.2) = _
  rw [HierarchySmoothProfile.profileSlowCurl_apply hT G.val.val Q ht, ← hQ,
    hGPhase (t, x.1, 0) ⟨ht, mem_univ _⟩ x.2,
    relayLabelJet_eq_slice ((HierarchySmoothProfile.contDiff_labelPhase_slice Q ht).differentiable (by simp) x)]

/-- The actual relay evaluation is determined by the selected momentum
equation and its normalized phase pressure. -/
theorem material_complete_add_labelGrad_apply_relay_of_momentum_on (hT : 0 < T)
    (G M : MP) (κ V F : VP) (p : SP)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hstart : t₀ < T)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hMPhase : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hVmean : profilePhaseAverage hT V = 0)
    (hGdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun r => G.val.val.val (r, a, 0))
        (-((G.val.val.val (t, a, 0)).comp (M.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (htrans : ∀ t ∈ Icc t₀ T, ∀ a s, ⟪κ.val.val.val (t, a, 0), V.val.val.val (t, a, s)⟫_ℝ = 0)
    (hpMean : ∀ t ∈ Icc t₀ T, ∀ a, phaseMean (fun r => p.val.val.val (t, a, r)) = 0)
    (hmomentum : let ops := twistedHierarchyOperators hT G M κ
      ∀ t ∈ Icc t₀ T, ∀ a s, (ops.material V + ops.phaseGrad p).val.val.val (t, a, s) =
        F.val.val.val (t, a, s))
    {t : ℝ} (ht : t ∈ Icc t₀ T) (x : Vec3 × ℝ) :
    let ops := twistedHierarchyOperators hT G M κ
    (ops.material (complete hT G κ hκPhase hκ V) + ops.labelGrad p).val.val.val (t, x) =
      waveRelayAt G M κ V F t x := by
  have hIactive : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  exact material_complete_add_labelGrad_apply_relay_on hT G M κ V F p ht₀ hstart hGPhase hMPhase hκPhase
    hκ hVmean hGdot hκdot
    (fun t hu a s => (velocity_equation_of_twisted_momentum_at hT G M κ V F p hMPhase hκPhase
      (hIactive hu) a s (hmomentum t hu a s)).mono hIactive)
    (fun _ hu => phasePressure_value_of_twisted_momentum_on hT G M κ V F p ht₀ hstart
      hMPhase hκPhase hκ hκdot htrans hpMean hmomentum hu) ht x

theorem material_complete_add_labelGrad_apply_relay_of_momentum (hT : 0 < T)
    (G M : MP) (κ V F : VP) (p : SP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hMPhase : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hVmean : profilePhaseAverage hT V = 0)
    (hGdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun r => G.val.val.val (r, a, 0))
        (-((G.val.val.val (t, a, 0)).comp (M.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (htrans : ∀ t ∈ Icc 0 T, ∀ a s, ⟪κ.val.val.val (t, a, 0), V.val.val.val (t, a, s)⟫_ℝ = 0)
    (hpMean : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun r => p.val.val.val (t, a, r)) = 0)
    (hmomentum : let ops := twistedHierarchyOperators hT G M κ
      ops.material V + ops.phaseGrad p = F)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    let ops := twistedHierarchyOperators hT G M κ
    (ops.material (complete hT G κ hκPhase hκ V) + ops.labelGrad p).val.val.val (t, x) =
      waveRelayAt G M κ V F t x :=
  material_complete_add_labelGrad_apply_relay_of_momentum_on hT G M κ V F p le_rfl hT hGPhase hMPhase
    hκPhase hκ hVmean hGdot hκdot htrans hpMean
    (fun t _ a s => congrArg (fun v : VP => v.val.val.val (t, a, s)) hmomentum) ht x

/-- Subtracting the completion of the transverse switch force leaves the
homogeneous relay of the switched leading velocity. -/
theorem material_complete_add_labelGrad_sub_switch_apply_relay (hT : 0 < T)
    (G M : MP) (κ V F : VP) (p : SP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hMPhase : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hVmean : profilePhaseAverage hT V = 0)
    (hFmean : profilePhaseAverage hT F = 0)
    (hGdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun r => G.val.val.val (r, a, 0))
        (-((G.val.val.val (t, a, 0)).comp (M.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hVtrans : ∀ t ∈ Icc 0 T, ∀ a s, ⟪κ.val.val.val (t, a, 0), V.val.val.val (t, a, s)⟫_ℝ = 0)
    (hFtrans : ∀ t ∈ Icc 0 T, ∀ a s, ⟪κ.val.val.val (t, a, 0), F.val.val.val (t, a, s)⟫_ℝ = 0)
    (hpMean : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun r => p.val.val.val (t, a, r)) = 0)
    (hmomentum : let ops := twistedHierarchyOperators hT G M κ
      ops.material V + ops.phaseGrad p = F)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    let ops := twistedHierarchyOperators hT G M κ
    (ops.material (complete hT G κ hκPhase hκ V) + ops.labelGrad p -
      complete hT G κ hκPhase hκ F).val.val.val (t, x) =
        waveRelayAt G M κ V 0 t x := by
  let ops := twistedHierarchyOperators hT G M κ
  let Str (a : Vec3) := M.val.val.val (t, a, 0)
  let K (a : Vec3) := κ.val.val.val (t, a, 0)
  let v (y : Vec3 × ℝ) := V.val.val.val (t, y)
  let f (y : Vec3 × ℝ) := F.val.val.val (t, y)
  let Q := HierarchySmoothProfile.profileWavePotential hT κ.val.val hκ V.val.val
  let QF := HierarchySmoothProfile.profileWavePotential hT κ.val.val hκ F.val.val
  let D := HierarchySmoothProfile.derivativeAlong hT
    (HierarchySmoothProfile.constant (1, 0, 0)) Q
  have hcontV := (HierarchySmoothProfile.contDiff_labelPhase_slice V.val.val ht).continuous
  have hcontF := (HierarchySmoothProfile.contDiff_labelPhase_slice F.val.val ht).continuous
  have hQtF : DifferentiableAt ℝ (relayPotentialTimeProfile Str K v f) x := by
    have heq : (fun y => D.val (t, y)) = relayPotentialTimeProfile Str K v f := by
      funext y
      have hy : (t, y) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
      have hqt := profileWavePotential_time_of_transverse hT M κ V F p hκ hκdot
        (fun _ hu => velocity_equation_of_twisted_momentum hT G M κ V F p hMPhase hκPhase
          hmomentum hu) ht y.1 y.2
      have hQd := HierarchySmoothProfile.hasDerivWithinAt_profileTime Q ht y.1 y.2
      dsimp only [D]
      rw [HierarchySmoothProfile.derivativeAlong_apply hT _ _ hy,
        HierarchySmoothProfile.constant_apply _ hy]
      exact (hQd.derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
        (hqt.derivWithin (uniqueDiffOn_Icc hT t ht))
    rw [← heq]
    exact (HierarchySmoothProfile.contDiff_labelPhase_slice D ht).differentiable (by simp) x
  have hQF : DifferentiableAt ℝ (relayPotentialProfile K f) x := by
    have heq : (fun y => QF.val (t, y)) = relayPotentialProfile K f :=
      funext fun y => HierarchySmoothProfile.profileWavePotential_apply hT κ.val.val hκ F.val.val ht y.1 y.2
    rw [← heq]
    exact (HierarchySmoothProfile.contDiff_labelPhase_slice QF ht).differentiable (by simp) x
  have hQt₀ : DifferentiableAt ℝ (relayPotentialTimeProfile Str K v (fun _ => 0)) x := by
    have heq : relayPotentialTimeProfile Str K v (fun _ => 0) =
        fun y => relayPotentialTimeProfile Str K v f y - relayPotentialProfile K f y := by
      funext y
      have hadd : relayPotentialTimeProfile Str K v f =
          fun z => relayPotentialTimeProfile Str K v (fun _ => 0) z + relayPotentialProfile K f z :=
        relayPotentialTimeProfile_add_forcing Str K hcontV hcontF
      exact (eq_sub_iff_add_eq).2 (congrFun hadd y).symm
    rw [heq]
    exact hQtF.sub hQF
  have hR := material_complete_add_labelGrad_apply_relay_of_momentum hT G M κ V F p
    hGPhase hMPhase hκPhase hκ hVmean hGdot hκdot hVtrans hpMean hmomentum ht x
  have hC := complete_apply_relayPotential hT G κ F hGPhase hκPhase hκ hFmean ht x
  change (ops.material (complete hT G κ hκPhase hκ V) + ops.labelGrad p).val.val.val (t, x) -
    (complete hT G κ hκPhase hκ F).val.val.val (t, x) = _
  rw [hR, hC]
  exact hierarchyLinearRelayAt_sub_transverse_force_completion
    (G.val.val.val (t, x.1, 0)) Str K hcontV hcontF (fun y => hFtrans t ht y.1 y.2) x hQt₀ hQF

/-- A pointwise representation of an actual twisted source as the raw relay
also represents its weighted slices using the weighted input slices. -/
theorem weightedSlices_eq_hierarchyLinearRelayAt_of_eval
    {T : ℝ} {k : Vec3} {A : Set ℝ} (τ : ℝ → ℝ)
    (G M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3) (κ : ℝ → Vec3 → Vec3)
    (V F R : HierarchyTwistedProfile T k Vec3)
    (hR : ∀ t ∈ A, ∀ x : Vec3 × ℝ,
      R.val.val.val (t, x) =
        hierarchyLinearRelayAt (G t x.1) (M t x.1)
          (relayPotentialProfile (κ t) (fun y => V.val.val.val (t, y)))
          (relayPotentialTimeProfile (M t) (κ t) (fun y => V.val.val.val (t, y))
            (fun y => F.val.val.val (t, y)))
          (relayPhasePressureProfile (M t) (κ t) (fun y => V.val.val.val (t, y))
            (fun y => F.val.val.val (t, y))) x) :
    weightedSlices A τ R = fun (t : A) x =>
      hierarchyLinearRelayAt (G t x.1) (M t x.1)
        (relayPotentialProfile (κ t) (weightedSlices A τ V t))
        (relayPotentialTimeProfile (M t) (κ t) (weightedSlices A τ V t) (weightedSlices A τ F t))
        (relayPhasePressureProfile (M t) (κ t) (weightedSlices A τ V t) (weightedSlices A τ F t)) x := by
  funext t x
  change τ t • R.val.val.val (t, x) = _
  rw [hR t t.property x]
  exact (hierarchyLinearRelayAt_input_const_smul (τ t) (G t x.1) (M t) (κ t)
    (fun y => V.val.val.val (t, y)) (fun y => F.val.val.val (t, y)) x).symm


/-- The parent coefficient budgets for the normalized potential, pressure,
and the three coframe contractions in the linear relay. -/
structure WaveRelayCoefficientBudget {X : Type*} (ℓ h : ℝ) (n : ℕ) (K : ℝ)
    (G M : X → Vec3 → Vec3 →L[ℝ] Vec3) (κnorm : X → Vec3 → Vec3) : Prop where
  potential : HierarchyRelayCoefficientJets ℓ h (n + 1) K
    (fun t a => hierarchyRelayPotentialCoefficient (κnorm t a))
  potentialTime : HierarchyRelayCoefficientJets ℓ h (n + 1) K
    (fun t a => hierarchyRelayTimeAmplitudeCoefficient (M t a) (κnorm t a))
  pressureAmplitude : HierarchyRelayCoefficientJets ℓ h (n + 1) K
    (fun t a => hierarchyRelayPressureAmplitudeCoefficient (M t a) (κnorm t a))
  pressureSource : HierarchyRelayCoefficientJets ℓ h (n + 1) K
    (fun t a => hierarchyRelayPressureSourceCoefficient (κnorm t a))
  curl : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
    (fun t a => hierarchyRelayCurlRow ℓ (G t a) i)
  material : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
    (fun t a => hierarchyRelayMaterialRow ℓ (G t a) (M t a) i)
  gradient : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
    (fun t a => hierarchyRelayPressureRow ℓ (G t a) i)

/-- The explicit order constant in the normalized linear relay estimate. -/
def waveRelayOrderConstant (n : ℕ) : ℝ :=
  18 * (hierarchyAdmissibleWords (Fin 4) n).card *
    (hierarchyAdmissibleWords (Fin 4) (n + 1)).card * (2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)

set_option maxHeartbeats 1000000 in
/-- An actual source represented by the canonical linear relay has the
inverse-frequency bound in the measured twisted seminorm. A time weight
is passed to both input slices before their label-phase differentiation. -/
theorem boundedWeightSeminorm_waveRelay_le_of_eval (hT : 0 < T)
    (G M : MP) (κ V F R : VP) (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ)
    {freq K : ℝ} (hfreq : 0 < freq) {S : Set ℝ} (hS : S ⊆ Icc 0 T)
    (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ S, ‖τ t‖ ≤ C)
    (hV : (twistedHierarchyOperators hT G M κ).average V = 0)
    (hF : (twistedHierarchyOperators hT G M κ).average F = 0)
    (hEval : ∀ t ∈ S, ∀ x : Vec3 × ℝ, R.val.val.val (t, x) = waveRelayAt G M κ V F t x)
    (hCoeff : WaveRelayCoefficientBudget ℓ h n K
      (fun (t : S) a => G.val.val.val (t, a, 0)) (fun (t : S) a => M.val.val.val (t, a, 0))
      (fun (t : S) a => freq⁻¹ • κ.val.val.val (t, a, 0))) :
    boundedWeightSeminorm False ℓ h n hT hS τ hτ R ≤
      waveRelayOrderConstant n * K ^ 2 * freq⁻¹ *
        (boundedWeightSeminorm False ℓ h (n + 1) hT hS τ hτ V +
          boundedWeightSeminorm False ℓ h (n + 1) hT hS τ hτ F) := by
  let G₀ (t : ℝ) (a : Vec3) := G.val.val.val (t, a, 0)
  let M₀ (t : ℝ) (a : Vec3) := M.val.val.val (t, a, 0)
  let κ₀ (t : ℝ) (a : Vec3) := κ.val.val.val (t, a, 0)
  let k₀ (t : S) (a : Vec3) := freq⁻¹ • κ₀ t a
  let v := weightedSlices S τ V
  let f := weightedSlices S τ F
  have hPeriod (W : VP) (t : S) (a : Vec3) :
      Function.Periodic (fun s => weightedSlices S τ W t (a, s)) 1 := by
    intro s
    change τ t • W.val.val.val (t, a, s + 1) = τ t • W.val.val.val (t, a, s)
    exact congrArg (fun u : Vec3 => τ t • u) (HierarchyPeriodicProfile.phasePeriodic W.val t a s)
  have hMean (W : VP) (hW : (twistedHierarchyOperators hT G M κ).average W = 0)
      (t : S) (a : Vec3) : phaseMean (fun s => weightedSlices S τ W t (a, s)) = 0 := by
    have h := congrArg (fun z : VP => z.val.val.val (t, a, 0)) hW
    change ((twistedHierarchyOperators hT G M κ).average W).val.val.val (t, a, 0) = 0 at h
    rw [average_apply_phaseMean hT G M κ W (hS t.property) a 0] at h
    change phaseMean (fun s => τ t • W.val.val.val (t, a, s)) = 0
    rw [phaseMean_const_smul, h, smul_zero]
  have hWord (W : VP) := hierarchyRelayWordBound_of_finiteNorm (ℓ := ℓ) (h := h) (n := n + 1)
    (f := weightedSlices S τ W) (fun w _ =>
      hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w W hS τ hτ)
  have hb := hierarchyFiniteWordNorm_waveLinearRelay_le n hℓ hfreq
    (G := fun (t : S) a => G₀ t a) (M := fun (t : S) a => M₀ t a) (k := k₀) (V := v) (f := f)
    (weightedSlices_smooth hS τ V) (weightedSlices_smooth hS τ F)
    (hPeriod V) (hPeriod F) (hMean V hV) (hMean F hF) (hWord V) (hWord F)
    hCoeff.potential hCoeff.potentialTime hCoeff.pressureAmplitude hCoeff.pressureSource
    hCoeff.curl hCoeff.material hCoeff.gradient
  dsimp only at hb
  have hScale (t : S) : (fun a => freq • k₀ t a) = κ₀ t := by
    funext a
    change freq • (freq⁻¹ • κ₀ t a) = κ₀ t a
    rw [smul_smul, mul_inv_cancel₀ hfreq.ne', one_smul]
  simp_rw [hScale] at hb
  have hW := weightedSlices_eq_hierarchyLinearRelayAt_of_eval τ G₀ M₀ κ₀ V F R hEval
  rw [boundedWeightSeminorm_apply, hW]
  exact hb


/-- A scalar time weight may be applied to the velocity slices before
taking their normalized potential and slow curl. -/
theorem weightedSlices_complete_eq_relayPotential (hT : 0 < T) (G : MP) (κ V : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hVmean : profilePhaseAverage hT V = 0)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) :
    weightedSlices A τ (complete hT G κ hκPhase hκ V) = fun (t : A) x =>
      curlOfDerivative ((hierarchyRelayLabelJet
        (relayPotentialProfile (fun a => κ.val.val.val (t, a, 0)) (weightedSlices A τ V t)) x).comp
        (G.val.val.val (t, x.1, 0))) := by
  funext t x
  change τ t • (complete hT G κ hκPhase hκ V).val.val.val (t, x) = _
  rw [complete_apply_relayPotential hT G κ V hGPhase hκPhase hκ hVmean (hA t.property)]
  let P := relayPotentialProfile (fun a => κ.val.val.val (t, a, 0))
    (fun y => V.val.val.val (t, y))
  have hWeighted : relayPotentialProfile (fun a => κ.val.val.val (t, a, 0))
        (weightedSlices A τ V t) = τ t • P :=
    relayPotentialProfile_const_smul (τ t) _ _
  rw [hWeighted]
  simp only [hierarchyRelayLabelJet, fderiv_const_smul_field, Pi.smul_apply, smul_comp,
    curlOfDerivative_smul]
  rfl

set_option maxHeartbeats 1000000 in
/-- The actual completion costs one mixed order and gains one inverse
frequency in the Appendix D weighted seminorm. -/
theorem boundedWeightSeminorm_complete_le (hT : 0 < T) (G : MP) (κ V : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hVmean : profilePhaseAverage hT V = 0)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {freq K : ℝ} (hfreq : 0 < freq)
    (hG : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun (t : A) a => hierarchyRelayCurlRow ℓ (G.val.val.val (t, a, 0)) i))
    (hκNorm : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun (t : A) a => hierarchyRelayPotentialCoefficient (freq⁻¹ • κ.val.val.val (t, a, 0)))) :
    boundedWeightSeminorm False ℓ h n hT hA τ hτ (complete hT G κ hκPhase hκ V) ≤
      (6 * (hierarchyAdmissibleWords (Fin 4) n).card *
        (hierarchyAdmissibleWords (Fin 4) (n + 1)).card * (2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)) *
        K ^ 2 * freq⁻¹ * boundedWeightSeminorm False ℓ h (n + 1) hT hA τ hτ V := by
  let W := weightedSlices A τ V
  let coframe (t : A) (x : Vec3 × ℝ) := G.val.val.val (t, x.1, 0)
  let covector (t : A) (a : Vec3) := freq⁻¹ • κ.val.val.val (t, a, 0)
  have hWp (t : A) (a : Vec3) : Function.Periodic (fun s => W t (a, s)) 1 := by
    intro s
    change τ t • V.val.val.val (t, a, s + 1) = τ t • V.val.val.val (t, a, s)
    exact congrArg (fun v : Vec3 => τ t • v) (HierarchyPeriodicProfile.phasePeriodic V.val t a s)
  have hWzero (t : A) (a : Vec3) : phaseMean (fun s => W t (a, s)) = 0 := by
    have ht := hA t.property
    have hx : ((t : ℝ), a, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    have hmean := congrArg (fun f : VP => f.val.val.val (t, a, 0)) hVmean
    change (HierarchySmoothProfile.profilePhaseAverage hT V.val.val).val (t, a, 0) = 0 at hmean
    rw [HierarchySmoothProfile.profilePhaseAverage_apply hT V.val.val hx] at hmean
    change phaseMean (fun s => τ t • V.val.val.val (t, a, s)) = 0
    rw [phaseMean_const_smul, hmean, smul_zero]
  have hWN := hierarchyRelayWordBound_of_finiteNorm
    (f := W) (ℓ := ℓ) (h := h) (n := n + 1) fun w _ =>
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w V hA τ hτ
  have hb := hierarchyFiniteWordNorm_waveCompletion_le (G := coframe) (k := covector)
    n hℓ hfreq (weightedSlices_smooth hA τ V) hWp hWzero hWN
    (fun i => (hG i).1) (fun i => (hG i).2) hκNorm.1 hκNorm.2
  have hκ' (t : A) (a : Vec3) : freq • covector t a = κ.val.val.val (t, a, 0) := by
    simp [covector, smul_smul, hfreq.ne']
  have hEq : weightedSlices A τ (complete hT G κ hκPhase hκ V) = fun (t : A) x =>
      curlOfDerivative ((hierarchyRelayLabelJet (fun y =>
        wavePotential (freq • covector t y.1) (fun s => W t (y.1, s)) y.2) x).comp
          (coframe t x)) := by
    rw [weightedSlices_complete_eq_relayPotential hT G κ V hGPhase hκPhase hκ hVmean hA τ]
    funext t x
    simp only [hκ', W, coframe]
    rfl
  simp only [boundedWeightSeminorm_apply] at *
  rw [hEq]
  refine hb.trans_eq ?_
  ring


end

end TorusEuler.HierarchyTwistedProfile
