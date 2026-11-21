import TorusEuler.HierarchySourceBounds
import TorusEuler.ParentCoframeEstimates
import TorusEuler.PhaseProfileEstimates
import TorusEuler.WaveCompletionBounds
import TorusEuler.OscillatoryHierarchySolve
import TorusEuler.TerminalIntegrals
import TorusEuler.LabelFlowGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The inverse-frequency factor, curl commutator, and finite-order
estimates in the linear relay of (5.31)–(5.33). -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace Interval

namespace TorusEuler

noncomputable section

private theorem relay_cross3_smul_left (r : ℝ) (a b : Vec3) :
    cross3 (r • a) b = r • cross3 a b := by
  apply WithLp.ofLp_injective
  simp [cross3, map_smul, LinearMap.smul_apply]

private theorem relay_inv_normsq_smul (a : Vec3) (r : ℝ) :
    (‖r • a‖ ^ 2)⁻¹ = r⁻¹ ^ 2 * (‖a‖ ^ 2)⁻¹ := by
  simpa only [inv_inv, div_eq_mul_inv] using inv_sq_norm_inv_smul r⁻¹ a

private theorem relay_phasePrimitive_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (f : ℝ → E) (s : ℝ) :
    phasePrimitive (fun σ => r • f σ) s = r • phasePrimitive f s := by
  simp only [phasePrimitive, phaseOscillation, intervalIntegral.integral_smul,
    phaseMean_const_smul, smul_sub]

/-- The curl potential gains exactly one inverse factor of the positive
frequency when its covector is replaced by the normalized covector. -/
theorem wavePotential_frequency_scale {freq : ℝ} (hf : 0 < freq)
    (k : Vec3) (V : ℝ → Vec3) (s : ℝ) :
    wavePotential (freq • k) V s = freq⁻¹ • wavePotential k V s := by
  unfold wavePotential
  rw [← relay_phasePrimitive_smul]
  congr 1
  funext σ
  rw [relay_inv_normsq_smul, relay_cross3_smul_left, smul_smul, smul_smul]
  congr 1
  field_simp [hf.ne']

/-- The time integrand of the potential has the same exact frequency
homogeneity. No derivative of the normalized strain or forcing enters. -/
theorem wavePotentialTimeSource_frequency_scale {freq : ℝ} (hf : 0 < freq)
    (M : Vec3 →L[ℝ] Vec3) (k v f : Vec3) :
    wavePotentialTimeSource M (freq • k) v f =
      freq⁻¹ • wavePotentialTimeSource M k v f := by
  have h₁ (q : ℝ) : freq⁻¹ ^ 2 * q * freq = freq⁻¹ * q := by
    field_simp [hf.ne']
  have h₂ (q y : ℝ) :
      2 * (freq * (freq * y)) * (freq⁻¹ ^ 2 * q) ^ 2 * freq =
        freq⁻¹ * (2 * y * q ^ 2) := by
    field_simp [hf.ne']
  unfold wavePotentialTimeSource
  simp_rw [div_eq_mul_inv]
  rw [← inv_pow (‖freq • k‖ ^ 2), ← inv_pow (‖k‖ ^ 2)]
  simp only [relay_inv_normsq_smul, map_smul, relay_cross3_smul_left,
    real_inner_smul_left, real_inner_smul_right, ← smul_add, ← smul_sub, smul_smul, h₁, h₂]
  module

/-- The mean-zero pressure from the transverse equation has the same
inverse-frequency factor. -/
theorem oscillatoryPhasePressure_frequency_scale {freq : ℝ} (hf : 0 < freq)
    (M : Vec3 →L[ℝ] Vec3) (k : Vec3) (f V : ℝ → Vec3) (s : ℝ) :
    oscillatoryPhasePressure M (freq • k) f V s =
      freq⁻¹ • oscillatoryPhasePressure M k f V s := by
  unfold oscillatoryPhasePressure
  rw [← relay_phasePrimitive_smul]
  congr 1
  funext σ
  simp only [oscillatoryPressureSlope, real_inner_smul_left, div_eq_mul_inv,
    relay_inv_normsq_smul, smul_eq_mul]
  field_simp [hf.ne']

/-- Time differentiation of the potential preserves the inverse factor.
This is an equality of the actual phase primitives in (5.33). -/
theorem phasePrimitive_wavePotentialTimeSource_frequency_scale {freq : ℝ} (hf : 0 < freq)
    (M : Vec3 →L[ℝ] Vec3) (k : Vec3) (V f : ℝ → Vec3) (s : ℝ) :
    phasePrimitive (fun σ => wavePotentialTimeSource M (freq • k) (V σ) (f σ)) s =
      freq⁻¹ • phasePrimitive (fun σ => wavePotentialTimeSource M k (V σ) (f σ)) s := by
  simpa only [wavePotentialTimeSource_frequency_scale hf] using
    relay_phasePrimitive_smul freq⁻¹ (fun σ => wavePotentialTimeSource M k (V σ) (f σ)) s

private theorem relay_sum_coordinateDirection (a : Vec3) :
    (∑ i : Fin 3, a i • coordinateDirection i) = a := by
  ext j
  let eval := (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
  change eval (∑ i, a i • coordinateDirection i) = a j
  rw [map_sum]
  simp [eval, coordinateDirection, EuclideanSpace.single, PiLp.single_apply]

theorem pulledBackCurl_eq_coordinate_sum (J G : Vec3 →L[ℝ] Vec3) :
    curlOfDerivative (J.comp G) =
      ∑ i : Fin 3, cross3 (G.adjoint (coordinateDirection i)) (J (coordinateDirection i)) := by
  have hsum : J.comp G = ∑ i : Fin 3, InnerProductSpace.rankOne ℝ
      (J (coordinateDirection i)) (G.adjoint (coordinateDirection i)) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply,
      InnerProductSpace.rankOne_apply, ContinuousLinearMap.adjoint_inner_left]
    have hr (i : Fin 3) : ⟪coordinateDirection i, G v⟫_ℝ = (G v) i := by
      simp [coordinateDirection, EuclideanSpace.inner_single_left]
    simp only [hr, ← map_smul, ← map_sum, relay_sum_coordinateDirection]
  change curlOfDerivativeCLM (J.comp G) = _
  rw [hsum, map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    coordinateCurl_rankOne (J (coordinateDirection i)) (G.adjoint (coordinateDirection i))

private theorem relay_curlOfDerivativeCLM_apply (D : Vec3 →L[ℝ] Vec3) :
    curlOfDerivativeCLM D = curlOfDerivative D := rfl

/-- The inverse coframe of a forward deformation satisfying the variational
equation solves the reverse equation by differentiation of the inverse. -/
theorem hasDerivWithinAt_inverseCoframe {I : Set ℝ} {t : ℝ}
    {F : ℝ → Vec3 ≃L[ℝ] Vec3} {M : Vec3 →L[ℝ] Vec3}
    (hF : HasDerivWithinAt (fun r => (F r : Vec3 →L[ℝ] Vec3))
      (M.comp (F t : Vec3 →L[ℝ] Vec3)) I t) :
    HasDerivWithinAt (fun r => (F r).symm.toContinuousLinearMap)
      (-((F t).symm.toContinuousLinearMap.comp M)) I t := by
  have hInverse := (hasFDerivAt_ringInverse (𝕜 := ℝ) (F t).toUnit).comp_hasDerivWithinAt t hF
  have hinv_eq : (fun r => (F r).symm.toContinuousLinearMap) =
      Ring.inverse ∘ (fun r => (F r : Vec3 →L[ℝ] Vec3)) := by
    funext r
    exact (Ring.inverse_unit (F r).toUnit).symm
  rw [← hinv_eq] at hInverse
  let G := (F t).symm.toContinuousLinearMap
  refine hInverse.congr_deriv ?_
  simp only [neg_apply, mulLeftRight_apply, ContinuousLinearMap.mul_def]
  change -(G.comp (M.comp (F t : Vec3 →L[ℝ] Vec3))).comp G = -(G.comp M)
  apply ContinuousLinearMap.ext
  intro v
  simp [G]

/-- The inverse label derivative along the actual parent trajectory is
differentiable within the whole closed slab and solves the reverse equation. -/
theorem IsLabelFlowOn.hasDerivWithinAt_inverseLabelCoframe
    {U : Velocity} {X : ℝ → Velocity} {l r s t : ℝ}
    (hX : IsLabelFlowOn U X (Icc l r))
    (hlr : l < r) (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u)) (hs : s ∈ Icc l r)
    (ht : t ∈ Icc l r) (a : Vec3) :
    HasDerivWithinAt (fun u => fderiv ℝ (X u s) (X s u a))
      (-((fderiv ℝ (X t s) (X s t a)).comp (fderiv ℝ (U t) (X s t a)))) (Icc l r) t := by
  classical
  let F (u : ℝ) := fderiv ℝ (X s u) a
  let G (u : ℝ) := fderiv ℝ (X u s) (X s u a)
  let E (u : ℝ) : Vec3 ≃L[ℝ] Vec3 :=
    if hu : u ∈ Icc l r then
      ContinuousLinearEquiv.equivOfInverse' (F u) (G u)
        (hX.labelDerivative_inverse hlr hU hper hs hu a).2
        (hX.labelDerivative_inverse hlr hU hper hs hu a).1
    else ContinuousLinearEquiv.refl ℝ Vec3
  have hEF (u : ℝ) (hu : u ∈ Icc l r) : (E u).toContinuousLinearMap = F u := by
    simp only [E, dite_eq_left hu]
    rfl
  have hEG (u : ℝ) (hu : u ∈ Icc l r) : (E u).symm.toContinuousLinearMap = G u := by
    simp only [E, dite_eq_left hu]
    rfl
  have hE : HasDerivWithinAt (fun u => (E u).toContinuousLinearMap)
      ((fderiv ℝ (U t) (X s t a)).comp (E t).toContinuousLinearMap) (Icc l r) t := by
    rw [hEF t ht]
    exact ((hX.labelDerivative_evolves hlr hU hper hs a).2 t ht).congr_of_mem hEF ht
  have hInv := hasDerivWithinAt_inverseCoframe hE
  rw [hEG t ht] at hInv
  exact hInv.congr_of_mem (fun u hu => (hEG u hu).symm) ht

/-- Time differentiation of the pulled-back curl. The supplied derivative of
the label jet is the label derivative of the time derivative whenever these
mixed derivatives commute. -/
theorem hasDerivWithinAt_pulledBackCurl {I : Set ℝ} {t : ℝ}
    {J G : ℝ → Vec3 →L[ℝ] Vec3} {Jt M : Vec3 →L[ℝ] Vec3}
    (hJ : HasDerivWithinAt J Jt I t)
    (hG : HasDerivWithinAt G (-((G t).comp M)) I t) :
    HasDerivWithinAt (fun r => curlOfDerivative ((J r).comp (G r)))
      (curlOfDerivative (Jt.comp (G t)) -
        curlOfDerivative (((J t).comp (G t)).comp M)) I t := by
  have hcomp : HasDerivWithinAt (fun r => (J r).comp (G r))
      (Jt.comp (G t) - ((J t).comp (G t)).comp M) I t := by
    refine (hJ.clm_comp hG).congr_deriv ?_
    ext v
    simp [sub_eq_add_neg]
  simpa only [Function.comp_def, map_sub, relay_curlOfDerivativeCLM_apply] using
    curlOfDerivativeCLM.hasFDerivAt.comp_hasDerivWithinAt t hcomp

/-- The curl portion of the material relay in (5.32), before adding the label
pressure gradient. The middle term is precisely the curl commutator. -/
theorem pulledBackCurl_material_eq {I : Set ℝ} {t : ℝ}
    {J G : ℝ → Vec3 →L[ℝ] Vec3} {Jt M : Vec3 →L[ℝ] Vec3}
    (hI : UniqueDiffWithinAt ℝ I t) (hJ : HasDerivWithinAt J Jt I t)
    (hG : HasDerivWithinAt G (-((G t).comp M)) I t) :
    derivWithin (fun u => curlOfDerivative ((J u).comp (G u))) I t +
      M (curlOfDerivative ((J t).comp (G t))) =
    curlOfDerivative (Jt.comp (G t)) - curlOfDerivative (((J t).comp (G t)).comp M) +
      M (curlOfDerivative ((J t).comp (G t))) := by
  rw [(hasDerivWithinAt_pulledBackCurl hJ hG).derivWithin hI]


section PrimitiveWordNorm

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem phaseMean_add_phase {f : ℝ → E} (hper : Function.Periodic f 1) (b : ℝ) :
    phaseMean (fun s => f (b + s)) = phaseMean f := by
  unfold phaseMean
  simp_rw [add_comm b]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ) b] using hper.intervalIntegral_add_eq b 0

private theorem phasePrimitive_add_phase {f : ℝ → E} (hf : Continuous f)
    (hper : Function.Periodic f 1) (hzero : phaseMean f = 0) (b : ℝ) :
    phasePrimitive (fun s => f (b + s)) = fun s => phasePrimitive f (b + s) := by
  have hderiv (s : ℝ) : HasDerivAt (fun u => phasePrimitive f (b + u)) (f (b + s)) s :=
    (hasDerivAt_phasePrimitive hf (b + s)).scomp s ((hasDerivAt_id s).const_add b)
      |>.congr_deriv (by simp)
  have h := phasePrimitive_deriv hderiv (hf.comp (continuous_const.add continuous_id))
  have hmean : phaseMean (fun s => phasePrimitive f (b + s)) = 0 :=
    (phaseMean_add_phase (periodic_phasePrimitive hf hper hzero) b).trans
      (phaseMean_phasePrimitive hf)
  rw [h]
  funext s
  exact sub_eq_self.mpr hmean

-- This is the same anchored integrand used by PhaseProfileEstimates.
private theorem contDiff_phasePrimitive_word {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (Function.uncurry (fun a => phasePrimitive (f a))) := by
  let g (a : P) (s : ℝ) := ∫ σ in (0 : ℝ)..s, f a σ
  have hrescale : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ => f p.1.1 (p.1.2 * p.2)) :=
    hf.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))
  have h := contDiff_snd.smul
    (contDiff_and_iteratedFDeriv_phaseInterval (f := fun (p : P × ℝ) σ => f p.1 (p.2 * σ))
      hrescale 0 1).1
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    convert h using 1
    funext p
    symm
    change p.2 • (∫ σ in (0 : ℝ)..1, f p.1 (p.2 * σ)) = ∫ σ in (0 : ℝ)..p.2, f p.1 σ
    simpa only [mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (f p.1) p.2
  exact hg.sub ((contDiff_and_iteratedFDeriv_phaseInterval hg 0 1).1.comp contDiff_fst)

variable {ι U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]

omit [CompleteSpace E] in
theorem phaseOperatorWord_constant_eq_iteratedFDeriv (d : ι → U)
    {f : U → E} (hf : ContDiff ℝ ∞ f) (w : List ι) (x : U) :
    phaseOperatorWord (fun i _ => d i) w f x =
      iteratedFDeriv ℝ w.length f x (fun i => d (w.get i)) := by
  induction w generalizing x with
  | nil => simp [phaseOperatorWord]
  | cons i w ih =>
    have hw : phaseOperatorWord (fun j _ => d j) w f =
        fun y => iteratedFDeriv ℝ w.length f y (fun j => d (w.get j)) :=
      funext ih
    change fderiv ℝ (phaseOperatorWord (fun j _ => d j) w f) x (d i) =
      iteratedFDeriv ℝ (w.length + 1) f x (fun j => d ((i :: w).get j))
    rw [hw]
    have hd := hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top w.length) x
    rw [hd.iteratedFDeriv_succ_apply_left']
    rfl

variable {T : Type*} [Fintype ι] [LinearOrder ι]

/-- The zero-mean periodic primitive doubles the finite supremum norm at most.
The derivative word, including every label and phase weight, is unchanged. -/
theorem hierarchyFiniteWordNorm_phasePrimitive_le (d : ι → P × ℝ) (n : ℕ)
    {f : T → P × ℝ → E} (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hper : ∀ t a, Function.Periodic (fun s => f t (a, s)) 1)
    (hzero : ∀ t a, phaseMean (fun s => f t (a, s)) = 0)
    (hb : ∀ w ∈ hierarchyAdmissibleWords ι n,
      BddAbove (hierarchyJetValues False (fun i _ => d i) w f)) :
    let F (t : T) (p : P × ℝ) := phasePrimitive (fun s => f t (p.1, s)) p.2
    (∀ w ∈ hierarchyAdmissibleWords ι n,
      BddAbove (hierarchyJetValues False (fun i _ => d i) w F)) ∧
    hierarchyFiniteWordNorm False (fun i _ => d i) n F ≤
      2 * hierarchyFiniteWordNorm False (fun i _ => d i) n f := by
  let F (t : T) (p : P × ℝ) := phasePrimitive (fun s => f t (p.1, s)) p.2
  change (∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove
    (hierarchyJetValues False (fun i _ => d i) w F)) ∧ _
  let D := fun i (_ : P × ℝ) => d i
  let M (w : List ι) := sSup (hierarchyJetValues False D w f)
  have hF (t : T) : ContDiff ℝ ∞ (F t) :=
    contDiff_phasePrimitive_word (f := fun a s => f t (a,s)) (hf t)
  have hM (w : List ι) (hw : w ∈ hierarchyAdmissibleWords ι n) : 0 ≤ M w :=
    le_csSup (hb w hw) (Or.inl rfl)
  have hbound (w : List ι) (hw : w ∈ hierarchyAdmissibleWords ι n)
      (t : T) (p : P × ℝ) : ‖phaseOperatorWord D w (F t) p‖ ≤ 2 * M w := by
    let g (z : P × ℝ) (σ : ℝ) := f t (z.1, z.2 + σ)
    have hg : ContDiff ℝ ∞ (Function.uncurry g) :=
      (hf t).comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.add contDiff_snd))
    have hgper (z : P × ℝ) : Function.Periodic (g z) 1 := by
      intro σ
      simpa only [g, add_assoc] using hper t z.1 (z.2 + σ)
    have hgzero (z : P × ℝ) : phaseMean (g z) = 0 :=
      (phaseMean_add_phase (hper t z.1) z.2).trans (hzero t z.1)
    have hshift : (fun z => phasePrimitive (g z) 0) = F t := by
      funext z
      have hfc : Continuous (fun s => f t (z.1, s)) :=
        (hf t).continuous.comp (continuous_const.prodMk continuous_id)
      simpa only [g, F, add_zero] using
        congrFun (phasePrimitive_add_phase hfc (hper t z.1) (hzero t z.1) z.2) 0
    let v : Fin w.length → P × ℝ := fun i => d (w.get i)
    have hsource (σ : ℝ) : ‖(1 : ℝ) • mixedPhaseJet g w.length 0 p σ v‖ ≤ M w := by
      simp only [one_smul, mixedPhaseJet, iteratedDeriv_zero]
      have heq : (fun z => g z σ) = (fun z => f t (z + (0, σ))) := by
        funext z
        rcases z with ⟨a, s⟩
        simp only [g, Prod.mk_add_mk, add_zero]
      rw [heq, iteratedFDeriv_comp_add_right]
      rw [← phaseOperatorWord_constant_eq_iteratedFDeriv d (hf t)]
      exact le_csSup (hb w hw) (Or.inr (Or.inl ⟨t, p + (0, σ), rfl⟩))
    have h := ((norm_apply_mixedPhaseJet_phaseOps_le hg hgper w.length 0 p 0 1 v hsource).2.2) hgzero
    simp only [one_smul, mixedPhaseJet, iteratedDeriv_zero, hshift] at h
    rw [phaseOperatorWord_constant_eq_iteratedFDeriv d (hF t)]
    exact h
  have hvalues (w : List ι) (hw : w ∈ hierarchyAdmissibleWords ι n) :
      2 * M w ∈ upperBounds (hierarchyJetValues False D w F) := by
    rintro r (rfl | ⟨t, p, rfl⟩ | ⟨hf', _⟩)
    · exact mul_nonneg (by norm_num) (hM w hw)
    · exact hbound w hw t p
    · exact hf'.elim
  refine ⟨fun w hw => ⟨2 * M w, hvalues w hw⟩, ?_⟩
  change (∑ w ∈ hierarchyAdmissibleWords ι n, sSup (hierarchyJetValues False D w F)) ≤
    2 * ∑ w ∈ hierarchyAdmissibleWords ι n, M w
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun w hw => csSup_le ⟨0, Or.inl rfl⟩ (hvalues w hw)

end PrimitiveWordNorm


section FiniteOrder

variable {T E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A uniform bound for the individual weighted derivatives in the
finite sup norm. The order counts labels and phase together. -/
def HierarchyRelayWordBound (ℓ h : ℝ) (n : ℕ) (B : ℝ)
    (f : T → Vec3 × ℝ → E) : Prop :=
  0 ≤ B ∧ ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n, ∀ t x,
    ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (f t) x‖ ≤ B

/-- A normalized label-jet bound gives the same mixed-word bound for the
phase-independent lift of the coefficient. -/
theorem hierarchyRelayWordBound_of_phaseIndependent {ℓ h : ℝ} {n : ℕ} {B : ℝ}
    {c : T → Vec3 → E} (hℓ : 0 ≤ ℓ) (hB : 0 ≤ B)
    (hc : ∀ t, ContDiff ℝ ∞ (c t))
    (hjets : ∀ t j, j ≤ n → ∀ a, ℓ ^ j * ‖iteratedFDeriv ℝ j (c t) a‖ ≤ B) :
    HierarchyRelayWordBound ℓ h n B (fun t x => c t x.1) := by
  let d (i : Fin 4) : Vec3 × ℝ := hierarchyMixedDirection ℓ h i 0
  have hd (i : Fin 4) : ‖(d i).1‖ ≤ ℓ := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hz : (d (Fin.last 3)).1 = 0 := by
        simp only [d, hierarchyMixedDirection, Fin.lastCases_last, phaseCoordinateDirection,
          Prod.smul_fst, smul_zero]
      show ‖(d (Fin.last 3)).1‖ ≤ ℓ
      simpa only [hz, norm_zero] using hℓ
    · simp [d, hierarchyMixedDirection, phaseCoordinateDirection, coordinateDirection,
        norm_smul, abs_of_nonneg hℓ]
  refine ⟨hB, fun w hw t x => ?_⟩
  have hlen := (mem_hierarchyAdmissibleWords.mp hw).1
  let L := fst ℝ Vec3 ℝ
  change ‖phaseOperatorWord (fun i _ => d i) w (c t ∘ L) x‖ ≤ B
  rw [phaseOperatorWord_constant_eq_iteratedFDeriv d ((hc t).comp L.contDiff)]
  rw [L.iteratedFDeriv_comp_right (hc t) x (by simp)]
  change ‖iteratedFDeriv ℝ w.length (c t) x.1 (fun i => (d (w.get i)).1)‖ ≤ B
  calc
    _ ≤ ‖iteratedFDeriv ℝ w.length (c t) x.1‖ * ℓ ^ w.length := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ w.length (c t) x.1).le_opNorm_mul_prod_of_le
          (b := fun _ => ℓ) (fun i => hd (w.get i))
    _ ≤ B := by simpa only [mul_comm] using hjets t w.length hlen x.1

theorem HierarchyRelayWordBound.finiteNorm_le {ℓ h : ℝ} {n : ℕ} {B : ℝ}
    {f : T → Vec3 × ℝ → E} (hf : HierarchyRelayWordBound ℓ h n B f) :
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n f ≤
      (hierarchyAdmissibleWords (Fin 4) n).card * B := by
  have hword (w : List (Fin 4)) (hw : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      B ∈ upperBounds (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w f) := by
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hFalse, _⟩)
    · exact hf.1
    · exact hf.2 w hw t x
    · exact hFalse.elim
  calc
    _ ≤ ∑ _w ∈ hierarchyAdmissibleWords (Fin 4) n, B := by
      exact Finset.sum_le_sum fun w hw => csSup_le ⟨0, Or.inl rfl⟩ (hword w hw)
    _ = _ := by simp

theorem hierarchyRelayWordBound_of_finiteNorm {ℓ h : ℝ} {n : ℕ}
    {f : T → Vec3 × ℝ → E}
    (hfb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w f)) :
    HierarchyRelayWordBound ℓ h n
      (hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n f) f := by
  have hz (w) (hw : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      0 ≤ sSup (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w f) :=
    le_csSup (hfb w hw) (Or.inl rfl)
  refine ⟨Finset.sum_nonneg hz, fun w hw t x => ?_⟩
  exact (le_csSup (hfb w hw) (Or.inr (Or.inl ⟨t, x, rfl⟩))).trans (Finset.single_le_sum hz hw)

private theorem relayWordBound_bdd {ℓ h : ℝ} {n : ℕ} {B : ℝ} {f : T → Vec3 × ℝ → E}
    (hf : HierarchyRelayWordBound ℓ h n B f) :
    ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w f) := by
  intro w hw
  refine ⟨B, ?_⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hFalse, _⟩)
  · exact hf.1
  · exact hf.2 w hw t x
  · exact hFalse.elim

private theorem relayWordBound_mono {ℓ h : ℝ} {n m : ℕ} {B C : ℝ}
    {f : T → Vec3 × ℝ → E} (hf : HierarchyRelayWordBound ℓ h n B f)
    (hm : m ≤ n) (hB : B ≤ C) : HierarchyRelayWordBound ℓ h m C f := by
  refine ⟨hf.1.trans hB, fun w hw t x => ?_⟩
  obtain ⟨hw₁, hw₂⟩ := mem_hierarchyAdmissibleWords.mp hw
  exact (hf.2 w (mem_hierarchyAdmissibleWords.mpr ⟨hw₁.trans hm, hw₂⟩) t x).trans hB

private theorem relayWordBound_phasePrimitive [CompleteSpace E]
    {ℓ h : ℝ} {n : ℕ} {B : ℝ} {f : T → Vec3 × ℝ → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hper : ∀ t a, Function.Periodic (fun s => f t (a,s)) 1)
    (hzero : ∀ t a, phaseMean (fun s => f t (a,s)) = 0)
    (hB : HierarchyRelayWordBound ℓ h n B f) :
    HierarchyRelayWordBound ℓ h n (2 * ((hierarchyAdmissibleWords (Fin 4) n).card * B))
      (fun t x => phasePrimitive (fun s => f t (x.1,s)) x.2) := by
  obtain ⟨hb, hle⟩ := hierarchyFiniteWordNorm_phasePrimitive_le
    (fun i => hierarchyMixedDirection ℓ h i 0) n hf hper hzero (relayWordBound_bdd hB)
  exact relayWordBound_mono (hierarchyRelayWordBound_of_finiteNorm hb) le_rfl
    (hle.trans (mul_le_mul_of_nonneg_left hB.finiteNorm_le (by norm_num)))

private theorem relayWordBound_bilinear {ℓ h : ℝ} {n : ℕ} {A C : ℝ}
    {f : T → Vec3 × ℝ → E} {g : T → Vec3 × ℝ → F} (B : E →L[ℝ] F →L[ℝ] G)
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hfA : HierarchyRelayWordBound ℓ h n A f)
    (hgC : HierarchyRelayWordBound ℓ h n C g) :
    HierarchyRelayWordBound ℓ h n ((2 : ℝ) ^ n * ‖B‖ * A * C)
      (fun t x => B (f t x) (g t x)) := by
  have hA := hfA.1
  have hC := hgC.1
  refine ⟨by positivity, fun w hw t x => ?_⟩
  obtain ⟨hw₁, hw₂⟩ := mem_hierarchyAdmissibleWords.mp hw
  have hsub (v : List (Fin 4)) (hv : List.Sublist v w) :
      v ∈ hierarchyAdmissibleWords (Fin 4) n :=
    mem_hierarchyAdmissibleWords.mpr ⟨hv.length_le.trans hw₁, hw₂.sublist hv⟩
  refine ((phaseOperatorWord_bilinear_bounds B (fun _ => contDiff_const) (hf t) (hg t)
    w hA (fun v hv => hfA.2 v (hsub v hv) t) (fun v hv => hgC.2 v (hsub v hv) t)).1 x).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hw₁)
      (norm_nonneg B)) hA) hC

/-- Applying a bounded coefficient to a bounded profile costs the product
of their word bounds with the finite Leibniz factor. -/
theorem HierarchyRelayWordBound.clm_apply {ℓ h : ℝ} {n : ℕ} {A C : ℝ}
    {f : T → Vec3 × ℝ → E →L[ℝ] F} {g : T → Vec3 × ℝ → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hfA : HierarchyRelayWordBound ℓ h n A f)
    (hgC : HierarchyRelayWordBound ℓ h n C g) :
    HierarchyRelayWordBound ℓ h n ((2 : ℝ) ^ n * A * C)
      (fun t x => f t x (g t x)) := by
  let B : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ F)
  have hB : ‖B‖ ≤ 1 := by
    simp only [B, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  apply relayWordBound_mono (relayWordBound_bilinear B hf hg hfA hgC) le_rfl
  calc
    _ ≤ (2 : ℝ) ^ n * 1 * A * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB (by positivity)) hfA.1) hgC.1
    _ = _ := by rw [mul_one]

private theorem phaseOperatorWord_append_relay (ℓ h : ℝ) (w v : List (Fin 4))
    (f : Vec3 × ℝ → E) :
    phaseOperatorWord (hierarchyMixedDirection ℓ h) (w ++ v) f =
      phaseOperatorWord (hierarchyMixedDirection ℓ h) w
        (phaseOperatorWord (hierarchyMixedDirection ℓ h) v f) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, phaseOperatorWord, ih]

private theorem relayWordBound_partial {ℓ h : ℝ} {n : ℕ} {A : ℝ}
    {f : T → Vec3 × ℝ → E} (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hA : HierarchyRelayWordBound ℓ h (n + 1) A f) (i : Fin 4) :
    HierarchyRelayWordBound ℓ h n A
      (fun t => phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i) (f t)) := by
  refine ⟨hA.1, fun w hw t x => ?_⟩
  let v := (w ++ [i]).mergeSort
  have hv : v.Perm (w ++ [i]) := List.mergeSort_perm _ _
  have hvm : v ∈ hierarchyAdmissibleWords (Fin 4) (n + 1) := by
    apply mem_hierarchyAdmissibleWords.mpr
    exact ⟨by simpa only [hv.length_eq, List.length_append, List.length_singleton] using
      Nat.succ_le_succ (mem_hierarchyAdmissibleWords.mp hw).1, List.pairwise_mergeSort' _ _⟩
  have heq := phaseOperatorWord_constantDirections_perm (fun j => hierarchyMixedDirection ℓ h j 0)
    (hf t) hv
  change phaseOperatorWord (hierarchyMixedDirection ℓ h) v (f t) =
    phaseOperatorWord (hierarchyMixedDirection ℓ h) (w ++ [i]) (f t) at heq
  rw [phaseOperatorWord_append_relay] at heq
  change phaseOperatorWord (hierarchyMixedDirection ℓ h) v (f t) =
    phaseOperatorWord (hierarchyMixedDirection ℓ h) w
      (phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i) (f t)) at heq
  rw [← heq]
  exact hA.2 v hvm t x

private theorem relayWordBound_const_smul {ℓ h : ℝ} {n : ℕ} {B : ℝ}
    {f : T → Vec3 × ℝ → E} (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hB : HierarchyRelayWordBound ℓ h n B f) (c : ℝ) :
    HierarchyRelayWordBound ℓ h n (‖c‖ * B) (fun t x => c • f t x) := by
  refine ⟨mul_nonneg (norm_nonneg _) hB.1, fun w hw t x => ?_⟩
  change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun x => c • f t x) x‖ ≤ _
  rw [phaseOperatorWord_const_smul (D := hierarchyMixedDirection ℓ h)
    (fun _ => contDiff_const) (hf t), norm_smul]
  exact mul_le_mul_of_nonneg_left (hB.2 w hw t x) (norm_nonneg _)

private theorem relay_phaseOperatorWord_sum {ι : Type*} {ℓ h : ℝ}
    (s : Finset ι) (f : ι → Vec3 × ℝ → E)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (w : List (Fin 4)) (x : Vec3 × ℝ) :
    phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, phaseOperatorWord (hierarchyMixedDirection ℓ h) w (f i) x := by
  induction w generalizing x with
  | nil => rfl
  | cons j w ih =>
    change fderiv ℝ (phaseOperatorWord (hierarchyMixedDirection ℓ h) w
      (fun y => ∑ i ∈ s, f i y)) x (hierarchyMixedDirection ℓ h j x) = _
    rw [funext ih, fderiv_fun_sum]
    · simp only [_root_.sum_apply, phaseOperatorWord, phaseDirectionalDerivative]
    · exact fun i hi => (contDiff_phaseOperatorWord (fun _ => contDiff_const) (hf i hi)
        w).differentiable (by simp) x

private theorem relayWordBound_sum {ι : Type*} {ℓ h : ℝ} {n : ℕ}
    (s : Finset ι) {B : ι → ℝ} {f : ι → T → Vec3 × ℝ → E}
    (hf : ∀ i ∈ s, ∀ t, ContDiff ℝ ∞ (f i t))
    (hB : ∀ i ∈ s, HierarchyRelayWordBound ℓ h n (B i) (f i)) :
    HierarchyRelayWordBound ℓ h n (∑ i ∈ s, B i) (fun t x => ∑ i ∈ s, f i t x) := by
  refine ⟨Finset.sum_nonneg (fun i hi => (hB i hi).1), fun w hw t x => ?_⟩
  rw [relay_phaseOperatorWord_sum s (fun i => f i t) (fun i hi => hf i hi t)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => (hB i hi).2 w hw t x)

private theorem relayWordBound_add {ℓ h : ℝ} {n : ℕ} {A B : ℝ}
    {f g : T → Vec3 × ℝ → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hA : HierarchyRelayWordBound ℓ h n A f) (hB : HierarchyRelayWordBound ℓ h n B g) :
    HierarchyRelayWordBound ℓ h n (A + B) (fun t x => f t x + g t x) := by
  let F (i : Fin 2) : T → Vec3 × ℝ → E := Fin.cases f (fun _ => g) i
  let C (i : Fin 2) : ℝ := Fin.cases A (fun _ => B) i
  have hF (i : Fin 2) (t : T) : ContDiff ℝ ∞ (F i t) := by
    fin_cases i
    · exact hf t
    · exact hg t
  have hC (i : Fin 2) : HierarchyRelayWordBound ℓ h n (C i) (F i) := by
    fin_cases i
    · exact hA
    · exact hB
  simpa only [Fin.sum_univ_two, show F 0 = f from rfl, show F 1 = g from rfl,
    show C 0 = A from rfl, show C 1 = B from rfl] using
    relayWordBound_sum (Finset.univ : Finset (Fin 2)) (fun i _ => hF i) (fun i _ => hC i)

/-- A coframe or curl coordinate multiplies a label derivative by a
coefficient that includes the reciprocal label radius. This estimate
costs exactly one derivative on the differentiated profile. -/
theorem hierarchyRelayWordBound_labelTerm {ℓ h : ℝ} {n : ℕ} {A C : ℝ}
    {a : T → Vec3 × ℝ → E →L[ℝ] F} {g : T → Vec3 × ℝ → E}
    (ha : ∀ t, ContDiff ℝ ∞ (a t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (haA : HierarchyRelayWordBound ℓ h n A a)
    (hgC : HierarchyRelayWordBound ℓ h (n + 1) C g) (i : Fin 3) :
    HierarchyRelayWordBound ℓ h n ((2 : ℝ) ^ n * A * C)
      (fun t x => a t x
        (phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i.castSucc) (g t) x)) :=
  HierarchyRelayWordBound.clm_apply ha
    (fun t => ((hg t).fderiv_right (by simp)).clm_apply contDiff_const)
    haA (relayWordBound_partial hg hgC i.castSucc)

/-- The coefficient of one weighted derivative of the pulled-back curl. -/
def hierarchyRelayCurlRow (ℓ : ℝ) (G : Vec3 →L[ℝ] Vec3) (i : Fin 3) : Vec3 →L[ℝ] Vec3 :=
  ℓ⁻¹ • cross3Left (G.adjoint (coordinateDirection i))

def hierarchyRelayLabelJet {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Vec3 × ℝ → Y) (x : Vec3 × ℝ) : Vec3 →L[ℝ] Y :=
  (fderiv ℝ f x).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)

theorem pulledBackCurl_eq_weightedCoordinateSum {ℓ : ℝ} (hℓ : ℓ ≠ 0) (h : ℝ)
    (G : Vec3 →L[ℝ] Vec3) (f : Vec3 × ℝ → Vec3) (x : Vec3 × ℝ) :
    curlOfDerivative ((hierarchyRelayLabelJet f x).comp G) =
      ∑ i : Fin 3, hierarchyRelayCurlRow ℓ G i
        (phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i.castSucc) f x) := by
  rw [pulledBackCurl_eq_coordinate_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hierarchyRelayCurlRow, hierarchyRelayLabelJet, _root_.smul_apply,
    phaseDirectionalDerivative, hierarchyMixedDirection, Fin.lastCases_castSucc,
    phaseCoordinateDirection, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    map_smul, smul_smul, mul_inv_cancel₀ hℓ, one_smul, cross3Left_apply]

/-- A pulled-back curl costs one weighted label derivative and one
coframe coefficient. The inverse frequency commutes with all spatial
and phase derivatives. -/
theorem hierarchyFiniteWordNorm_pulledBackCurl_le {ℓ h freq A B : ℝ} (n : ℕ)
    (hℓ : ℓ ≠ 0) (hfreq : 0 < freq) {G : T → Vec3 × ℝ → Vec3 →L[ℝ] Vec3}
    {Q : T → Vec3 × ℝ → Vec3}
    (hQ : ∀ t, ContDiff ℝ ∞ (Q t))
    (hG : ∀ i t, ContDiff ℝ ∞ (fun x => hierarchyRelayCurlRow ℓ (G t x) i))
    (hGN : ∀ i, HierarchyRelayWordBound ℓ h n A
      (fun t x => hierarchyRelayCurlRow ℓ (G t x) i))
    (hQN : HierarchyRelayWordBound ℓ h (n + 1) B Q) :
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun t x => freq⁻¹ • curlOfDerivative ((hierarchyRelayLabelJet (Q t) x).comp (G t x))) ≤
      (hierarchyAdmissibleWords (Fin 4) n).card * (3 * (2 : ℝ) ^ n * A * B * freq⁻¹) := by
  let C (i : Fin 3) (t : T) (x : Vec3 × ℝ) :=
    hierarchyRelayCurlRow ℓ (G t x) i
      (phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i.castSucc) (Q t) x)
  have hC (i) (t) : ContDiff ℝ ∞ (C i t) :=
    (hG i t).clm_apply (((hQ t).fderiv_right (by simp)).clm_apply contDiff_const)
  have hbC (i) : HierarchyRelayWordBound ℓ h n ((2 : ℝ) ^ n * A * B) (C i) :=
    hierarchyRelayWordBound_labelTerm (hG i) hQ (hGN i) hQN i
  have hS (t : T) : ContDiff ℝ ∞ (fun x => ∑ i, C i t x) := by
    simpa only [Finset.sum_apply] using
      (ContDiff.sum (s := Finset.univ) (fun i _ => hC i t))
  have hsum := relayWordBound_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => hC i) (fun i _ => hbC i)
  have hbound := (relayWordBound_const_smul hS hsum freq⁻¹).finiteNorm_le
  simp_rw [pulledBackCurl_eq_weightedCoordinateSum hℓ h]
  simpa [C, Real.norm_eq_abs, abs_of_pos hfreq, mul_assoc, mul_comm, mul_left_comm]
    using hbound

/-- The coefficient of the potential after normalizing the covector by
the central frequency. -/
def hierarchyRelayPotentialCoefficient (k : Vec3) : Vec3 →L[ℝ] Vec3 :=
  (-(‖k‖ ^ 2)⁻¹) • cross3Left k

def hierarchyRelayTimeAmplitudeCoefficient (M : Vec3 →L[ℝ] Vec3) (k : Vec3) :
    Vec3 →L[ℝ] Vec3 :=
  (‖k‖ ^ 2)⁻¹ • (cross3Left (M.adjoint k) + (cross3Left k).comp M) -
    (2 * ⟪k, M k⟫_ℝ / (‖k‖ ^ 2) ^ 2) • cross3Left k

def hierarchyRelayPressureAmplitudeCoefficient (M : Vec3 →L[ℝ] Vec3) (k : Vec3) :
    Vec3 →L[ℝ] ℝ :=
  (-2 * (‖k‖ ^ 2)⁻¹) • (innerSL ℝ k).comp M

def hierarchyRelayPressureSourceCoefficient (k : Vec3) : Vec3 →L[ℝ] ℝ :=
  (‖k‖ ^ 2)⁻¹ • innerSL ℝ k

theorem wavePotentialTimeSource_eq_coefficients (M : Vec3 →L[ℝ] Vec3) (k v f : Vec3) :
    wavePotentialTimeSource M k v f =
      hierarchyRelayTimeAmplitudeCoefficient M k v + hierarchyRelayPotentialCoefficient k f := by
  simp only [hierarchyRelayTimeAmplitudeCoefficient, hierarchyRelayPotentialCoefficient,
    wavePotentialTimeSource, comp_apply, sub_apply, add_apply, _root_.smul_apply,
    cross3Left_apply, smul_sub, neg_smul]
  abel

theorem oscillatoryPressureSlope_eq_coefficients (M : Vec3 →L[ℝ] Vec3) (k f v : Vec3) :
    oscillatoryPressureSlope M k f v =
      hierarchyRelayPressureAmplitudeCoefficient M k v + hierarchyRelayPressureSourceCoefficient k f := by
  simp only [oscillatoryPressureSlope, hierarchyRelayPressureAmplitudeCoefficient,
    hierarchyRelayPressureSourceCoefficient, comp_apply, _root_.smul_apply, innerSL_apply_apply,
    smul_eq_mul, div_eq_mul_inv]
  ring

/-- The normalized integrand is linear in two phase profiles. Its
phase primitive costs no additional word length and requires no time
regularity of the coefficients or inputs. -/
theorem hierarchyRelayWordBound_linearPrimitive [CompleteSpace E]
    {ℓ h A B V₀ F₀ : ℝ} {n : ℕ}
    {a b : T → Vec3 → Vec3 →L[ℝ] E} {V f : T → Vec3 × ℝ → Vec3}
    (ha : ∀ t, ContDiff ℝ ∞ (fun x : Vec3 × ℝ => a t x.1))
    (hb : ∀ t, ContDiff ℝ ∞ (fun x : Vec3 × ℝ => b t x.1))
    (hV : ∀ t, ContDiff ℝ ∞ (V t)) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hVp : ∀ t x, Function.Periodic (fun s => V t (x,s)) 1)
    (hfp : ∀ t x, Function.Periodic (fun s => f t (x,s)) 1)
    (hVz : ∀ t x, phaseMean (fun s => V t (x,s)) = 0)
    (hfz : ∀ t x, phaseMean (fun s => f t (x,s)) = 0)
    (haN : HierarchyRelayWordBound ℓ h n A (fun t x => a t x.1))
    (hbN : HierarchyRelayWordBound ℓ h n B (fun t x => b t x.1))
    (hVN : HierarchyRelayWordBound ℓ h n V₀ V) (hfN : HierarchyRelayWordBound ℓ h n F₀ f) :
    let P (t : T) (x : Vec3 × ℝ) :=
      phasePrimitive (fun s => a t x.1 (V t (x.1,s)) + b t x.1 (f t (x.1,s))) x.2
    (∀ t, ContDiff ℝ ∞ (P t)) ∧
      HierarchyRelayWordBound ℓ h n
        (2 * ((hierarchyAdmissibleWords (Fin 4) n).card *
          ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B * F₀))) P := by
  let I (t : T) (x : Vec3 × ℝ) := a t x.1 (V t x) + b t x.1 (f t x)
  have hv (t) : ContDiff ℝ ∞ (fun x : Vec3 × ℝ => a t x.1 (V t x)) := (ha t).clm_apply (hV t)
  have hf' (t) : ContDiff ℝ ∞ (fun x : Vec3 × ℝ => b t x.1 (f t x)) := (hb t).clm_apply (hf t)
  have hI (t) : ContDiff ℝ ∞ (I t) := (hv t).add (hf' t)
  have hIp (t x) : Function.Periodic (fun s => I t (x,s)) 1 :=
    fun s => by simp only [I, hVp t x s, hfp t x s]
  have hIz (t x) : phaseMean (fun s => I t (x,s)) = 0 := by
    have hvC : Continuous (fun s => V t (x,s)) :=
      (hV t).continuous.comp (continuous_const.prodMk continuous_id)
    have hfC : Continuous (fun s => f t (x,s)) :=
      (hf t).continuous.comp (continuous_const.prodMk continuous_id)
    have hva : Continuous (fun s => a t x (V t (x,s))) := (a t x).continuous.comp hvC
    have hfb : Continuous (fun s => b t x (f t (x,s))) := (b t x).continuous.comp hfC
    have hvzero : phaseMean (fun s => a t x (V t (x,s))) = 0 := by
      rw [phaseMean, (a t x).intervalIntegral_comp_comm (hvC.intervalIntegrable 0 1),
        ← phaseMean, hVz, map_zero]
    have hfzero : phaseMean (fun s => b t x (f t (x,s))) = 0 := by
      rw [phaseMean, (b t x).intervalIntegral_comp_comm (hfC.intervalIntegrable 0 1),
        ← phaseMean, hfz, map_zero]
    simp only [I, phaseMean_add hva hfb, hvzero, hfzero, add_zero]
  exact ⟨fun t => contDiff_phasePrimitive_word (f := fun x s => I t (x,s)) (hI t),
    relayWordBound_phasePrimitive hI hIp hIz
      (relayWordBound_add hv hf' (HierarchyRelayWordBound.clm_apply ha hV haN hVN)
        (HierarchyRelayWordBound.clm_apply hb hf hbN hfN))⟩

/-- The finite bound for the actual divergence correction (5.31).
The amplitude can already include the reciprocal time weight. The
coefficient budgets are those of the normalized covector map and the
inverse-radius rows of the inverse label derivative. -/
theorem hierarchyFiniteWordNorm_waveCompletion_le {ℓ h freq A B V₀ : ℝ} (n : ℕ)
    (hℓ : ℓ ≠ 0) (hfreq : 0 < freq) {G : T → Vec3 × ℝ → Vec3 →L[ℝ] Vec3}
    {k : T → Vec3 → Vec3} {V : T → Vec3 × ℝ → Vec3}
    (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hVp : ∀ t a, Function.Periodic (fun s => V t (a,s)) 1)
    (hVzero : ∀ t a, phaseMean (fun s => V t (a,s)) = 0)
    (hVN : HierarchyRelayWordBound ℓ h (n + 1) V₀ V)
    (hG : ∀ i t, ContDiff ℝ ∞ (fun x => hierarchyRelayCurlRow ℓ (G t x) i))
    (hGN : ∀ i, HierarchyRelayWordBound ℓ h n A
      (fun t x => hierarchyRelayCurlRow ℓ (G t x) i))
    (hK : ∀ t, ContDiff ℝ ∞ (fun x : Vec3 × ℝ => hierarchyRelayPotentialCoefficient (k t x.1)))
    (hKN : HierarchyRelayWordBound ℓ h (n + 1) B
      (fun t x => hierarchyRelayPotentialCoefficient (k t x.1))) :
    let Q (t : T) (x : Vec3 × ℝ) := wavePotential (freq • k t x.1) (fun s => V t (x.1,s)) x.2
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun t x => curlOfDerivative ((hierarchyRelayLabelJet (Q t) x).comp (G t x))) ≤
      (hierarchyAdmissibleWords (Fin 4) n).card * (3 * (2 : ℝ) ^ n * A *
        (2 * ((hierarchyAdmissibleWords (Fin 4) (n + 1)).card *
          ((2 : ℝ) ^ (n + 1) * B * V₀))) * freq⁻¹) := by
  let I := fun (t : T) (x : Vec3 × ℝ) => hierarchyRelayPotentialCoefficient (k t x.1) (V t x)
  let P := fun (t : T) (x : Vec3 × ℝ) => phasePrimitive (fun s => I t (x.1,s)) x.2
  have hI (t) : ContDiff ℝ ∞ (I t) := (hK t).clm_apply (hV t)
  have hIp (t a) : Function.Periodic (fun s => I t (a,s)) 1 :=
    fun s => congrArg (hierarchyRelayPotentialCoefficient (k t a)) (hVp t a s)
  have hIz (t a) : phaseMean (fun s => I t (a,s)) = 0 := by
    let L := hierarchyRelayPotentialCoefficient (k t a)
    have hVc : Continuous (fun s => V t (a,s)) :=
      (hV t).continuous.comp (continuous_const.prodMk continuous_id)
    change phaseMean (fun s => L (V t (a,s))) = 0
    rw [phaseMean, L.intervalIntegral_comp_comm (hVc.intervalIntegrable 0 1),
      ← phaseMean, hVzero, map_zero]
  have hP (t) : ContDiff ℝ ∞ (P t) :=
    contDiff_phasePrimitive_word (f := fun a s => I t (a,s)) (hI t)
  have hPN := relayWordBound_phasePrimitive hI hIp hIz (HierarchyRelayWordBound.clm_apply hK hV hKN hVN)
  have hb := hierarchyFiniteWordNorm_pulledBackCurl_le n hℓ hfreq hP hG hGN hPN
  have heq (t : T) :
      (fun x : Vec3 × ℝ => wavePotential (freq • k t x.1) (fun s => V t (x.1,s)) x.2) =
        fun x => freq⁻¹ • P t x := by
    funext x
    exact wavePotential_frequency_scale hfreq (k t x.1) (fun s => V t (x.1,s)) x.2
  dsimp only
  have hcurl (t : T) (x : Vec3 × ℝ) :
      curlOfDerivative ((hierarchyRelayLabelJet (fun y =>
        wavePotential (freq • k t y.1) (fun s => V t (y.1,s)) y.2) x).comp (G t x)) =
      freq⁻¹ • curlOfDerivative ((hierarchyRelayLabelJet (P t) x).comp (G t x)) := by
    rw [heq]
    simp only [hierarchyRelayLabelJet, fderiv_fun_const_smul ((hP t).differentiable (by simp) x),
      smul_comp, curlOfDerivative_smul]
  simp_rw [hcurl]
  exact hb

def hierarchyRelayPressureRow (ℓ : ℝ) (G : Vec3 →L[ℝ] Vec3) (i : Fin 3) : ℝ →L[ℝ] Vec3 :=
  ℓ⁻¹ • toSpanSingleton ℝ (G.adjoint (coordinateDirection i))

def hierarchyRelayMaterialRow (ℓ : ℝ) (G M : Vec3 →L[ℝ] Vec3)
    (i : Fin 3) : Vec3 →L[ℝ] Vec3 :=
  M.comp (hierarchyRelayCurlRow ℓ G i) - hierarchyRelayCurlRow ℓ (G.comp M) i

theorem pulledBackGradient_eq_weightedCoordinateSum {ℓ : ℝ} (hℓ : ℓ ≠ 0) (h : ℝ)
    (G : Vec3 →L[ℝ] Vec3) (p : Vec3 × ℝ → ℝ) (x : Vec3 × ℝ) :
    G.adjoint ((InnerProductSpace.toDual ℝ Vec3).symm (hierarchyRelayLabelJet p x)) =
      ∑ i : Fin 3, hierarchyRelayPressureRow ℓ G i
        (phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i.castSucc) p x) := by
  let J := hierarchyRelayLabelJet p x
  let a := (InnerProductSpace.toDual ℝ Vec3).symm J
  have hJ : innerSL ℝ a = J := (InnerProductSpace.toDual ℝ Vec3).apply_symm_apply J
  have ha (i : Fin 3) : a i = J (coordinateDirection i) := by
    have hi := congrArg (fun k : Vec3 →L[ℝ] ℝ => k (coordinateDirection i)) hJ
    simpa [coordinateDirection, EuclideanSpace.inner_single_right] using hi
  change G.adjoint a = _
  conv_lhs => rw [← relay_sum_coordinateDirection a, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul, ha, J, hierarchyRelayPressureRow, hierarchyRelayLabelJet,
    _root_.smul_apply, phaseDirectionalDerivative, hierarchyMixedDirection, Fin.lastCases_castSucc,
    phaseCoordinateDirection, comp_apply, inl_apply, toSpanSingleton_apply, smul_smul,
    smul_eq_mul]
  congr 1
  field_simp [hℓ]

/-- The exact four slow terms after commuting the time derivative
through the pulled-back curl. `Qt` is the potential-time profile
computed from (5.33), and `p` is the oscillatory phase pressure. -/
def hierarchyLinearRelayAt (G M : Vec3 →L[ℝ] Vec3)
    (Q Qt : Vec3 × ℝ → Vec3) (p : Vec3 × ℝ → ℝ) (x : Vec3 × ℝ) : Vec3 :=
  curlOfDerivative ((hierarchyRelayLabelJet Qt x).comp G) -
    curlOfDerivative (((hierarchyRelayLabelJet Q x).comp G).comp M) +
    M (curlOfDerivative ((hierarchyRelayLabelJet Q x).comp G)) +
    G.adjoint ((InnerProductSpace.toDual ℝ Vec3).symm (hierarchyRelayLabelJet p x))

theorem hierarchyLinearRelayAt_eq_coordinate_sum {ℓ : ℝ} (hℓ : ℓ ≠ 0) (h : ℝ)
    (G M : Vec3 →L[ℝ] Vec3) (Q Qt : Vec3 × ℝ → Vec3) (p : Vec3 × ℝ → ℝ)
    (x : Vec3 × ℝ) :
    hierarchyLinearRelayAt G M Q Qt p x =
      ∑ i : Fin 3, (hierarchyRelayCurlRow ℓ G i
        (phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i.castSucc) Qt x) +
        hierarchyRelayMaterialRow ℓ G M i
          (phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i.castSucc) Q x) +
        hierarchyRelayPressureRow ℓ G i
          (phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i.castSucc) p x)) := by
  unfold hierarchyLinearRelayAt
  rw [comp_assoc, pulledBackCurl_eq_weightedCoordinateSum hℓ h,
    pulledBackCurl_eq_weightedCoordinateSum hℓ h, pulledBackCurl_eq_weightedCoordinateSum hℓ h,
    pulledBackGradient_eq_weightedCoordinateSum hℓ h, map_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hierarchyRelayMaterialRow, sub_apply, comp_apply]
  abel

/-- Simultaneously multiplying the three input profiles by a scalar
multiplies the entire relay, including the commutator, by that scalar. -/
theorem hierarchyLinearRelayAt_smul (r : ℝ)
    (G M : Vec3 →L[ℝ] Vec3)
    {Q Qt : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ} {x : Vec3 × ℝ}
    (hQ : DifferentiableAt ℝ Q x) (hQt : DifferentiableAt ℝ Qt x)
    (hp : DifferentiableAt ℝ p x) :
    hierarchyLinearRelayAt G M (fun y => r • Q y) (fun y => r • Qt y) (fun y => r • p y) x =
      r • hierarchyLinearRelayAt G M Q Qt p x := by
  rw [hierarchyLinearRelayAt_eq_coordinate_sum one_ne_zero 1,
    hierarchyLinearRelayAt_eq_coordinate_sum one_ne_zero 1, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [phaseDirectionalDerivative, fderiv_fun_const_smul hQ, fderiv_fun_const_smul hQt,
    fderiv_fun_const_smul hp, _root_.smul_apply, map_smul, smul_add]

/-- The actual primitive fields in the relay with the frequency
removed from the covector. Each depends only on the indicated
fixed-time coefficient and profile data. -/
def relayPotentialProfile (k : Vec3 → Vec3) (V : Vec3 × ℝ → Vec3)
    (x : Vec3 × ℝ) : Vec3 :=
  wavePotential (k x.1) (fun s => V (x.1,s)) x.2

def relayPotentialTimeProfile (M : Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3 → Vec3)
    (V f : Vec3 × ℝ → Vec3) (x : Vec3 × ℝ) : Vec3 :=
  phasePrimitive (fun s => wavePotentialTimeSource (M x.1) (k x.1) (V (x.1,s)) (f (x.1,s))) x.2

def relayPhasePressureProfile (M : Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3 → Vec3)
    (V f : Vec3 × ℝ → Vec3) (x : Vec3 × ℝ) : ℝ :=
  oscillatoryPhasePressure (M x.1) (k x.1) (fun s => f (x.1,s)) (fun s => V (x.1,s)) x.2

theorem hierarchyLinearRelayAt_frequency_scale {freq : ℝ} (hf : 0 < freq)
    (G : Vec3 →L[ℝ] Vec3) (M : Vec3 → Vec3 →L[ℝ] Vec3)
    (k : Vec3 → Vec3) (V f : Vec3 × ℝ → Vec3) (x : Vec3 × ℝ)
    (hQ : DifferentiableAt ℝ (relayPotentialProfile k V) x)
    (hQt : DifferentiableAt ℝ (relayPotentialTimeProfile M k V f) x)
    (hp : DifferentiableAt ℝ (relayPhasePressureProfile M k V f) x) :
    hierarchyLinearRelayAt G (M x.1) (relayPotentialProfile (fun a => freq • k a) V)
      (relayPotentialTimeProfile M (fun a => freq • k a) V f)
      (relayPhasePressureProfile M (fun a => freq • k a) V f) x =
    freq⁻¹ • hierarchyLinearRelayAt G (M x.1) (relayPotentialProfile k V)
      (relayPotentialTimeProfile M k V f) (relayPhasePressureProfile M k V f) x := by
  have h₁ : relayPotentialProfile (fun a => freq • k a) V =
      fun y => freq⁻¹ • relayPotentialProfile k V y := by
    funext y
    exact wavePotential_frequency_scale hf (k y.1) (fun s => V (y.1,s)) y.2
  have h₂ : relayPotentialTimeProfile M (fun a => freq • k a) V f =
      fun y => freq⁻¹ • relayPotentialTimeProfile M k V f y := by
    funext y
    exact phasePrimitive_wavePotentialTimeSource_frequency_scale hf (M y.1) (k y.1)
      (fun s => V (y.1,s)) (fun s => f (y.1,s)) y.2
  have h₃ : relayPhasePressureProfile M (fun a => freq • k a) V f =
      fun y => freq⁻¹ • relayPhasePressureProfile M k V f y := by
    funext y
    exact oscillatoryPhasePressure_frequency_scale hf (M y.1) (k y.1)
      (fun s => f (y.1,s)) (fun s => V (y.1,s)) y.2
  rw [h₁, h₂, h₃, hierarchyLinearRelayAt_smul _ _ _ hQ hQt hp]

theorem hasDerivAt_labelJet_of_jointSmooth {E U : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup U] [NormedSpace ℝ U]
    {Q : ℝ × U → E} (hQ : ContDiff ℝ ∞ Q) (t : ℝ) (a : U) :
    HasDerivAt (fun r => fderiv ℝ (fun b => Q (r,b)) a)
      (fderiv ℝ (fun b => fderiv ℝ Q (t,b) (1,0)) a) t := by
  let I := inr ℝ ℝ U
  have hj (r : ℝ) : fderiv ℝ (fun b => Q (r,b)) a =
      (fderiv ℝ Q (r,a)).comp I := by
    have hI : HasFDerivAt (fun b : U => (r,b)) I a :=
      (hasFDerivAt_const r a).prodMk (hasFDerivAt_id a)
    exact (((hQ.differentiable (by simp) (r,a)).hasFDerivAt).comp a hI).fderiv
  have hSmooth : ContDiff ℝ ∞ (fderiv ℝ Q) := hQ.fderiv_right (by simp)
  have hD := (hSmooth.differentiable (by simp) (t,a)).hasFDerivAt
  have ht : HasDerivAt (fun r : ℝ => (r,a)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t a)
  have hL : HasFDerivAt (fun b : U => (t,b)) I a :=
    (hasFDerivAt_const t a).prodMk (hasFDerivAt_id a)
  have hT := hD.comp_hasDerivAt t ht
  have hA := hD.comp a hL
  let L := (compL ℝ U (ℝ × U) E).flip I
  let K := ContinuousLinearMap.apply ℝ E ((1 : ℝ), (0 : U))
  have hT' := L.hasFDerivAt.comp_hasDerivAt t hT
  have hA' := K.hasFDerivAt.comp a hA
  change HasDerivAt (fun r => (fderiv ℝ Q (r,a)).comp I)
    ((fderiv ℝ (fderiv ℝ Q) (t,a) (1,0)).comp I) t at hT'
  change HasFDerivAt (fun b => fderiv ℝ Q (t,b) (1,0))
    (K.comp ((fderiv ℝ (fderiv ℝ Q) (t,a)).comp I)) a at hA'
  simp_rw [hj]
  rw [hA'.fderiv]
  refine hT'.congr_deriv ?_
  ext v
  exact (hQ.contDiffAt.isSymmSndFDerivAt (by simp)) (1,0) (0,v)

/-- The potential-time formula also differentiates the label jet if
the potential has a jointly smooth extension across the time slab. -/
theorem hasDerivWithinAt_relayLabelJet_of_jointSmooth
    {I : Set ℝ} {t : ℝ} {Q : ℝ → Vec3 × ℝ → Vec3} {Qt : Vec3 × ℝ → Vec3}
    (hI : UniqueDiffWithinAt ℝ I t)
    (hQ : ContDiff ℝ ∞ (Function.uncurry Q))
    (hQt : ∀ x, HasDerivWithinAt (fun r => Q r x) (Qt x) I t) (x : Vec3 × ℝ) :
    HasDerivWithinAt (fun r => hierarchyRelayLabelJet (Q r) x)
      (hierarchyRelayLabelJet Qt x) I t := by
  have heq : (fun y => fderiv ℝ (Function.uncurry Q) (t,y) (1,0)) = Qt := by
    funext y
    have h := ((hQ.differentiable (by simp) (t,y)).hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    exact (h.hasDerivWithinAt.derivWithin hI).symm.trans ((hQt y).derivWithin hI)
  have hj := hasDerivAt_labelJet_of_jointSmooth hQ t x
  change HasDerivAt (fun r => fderiv ℝ (Q r) x)
    (fderiv ℝ (fun y => fderiv ℝ (Function.uncurry Q) (t,y) (1,0)) x) t at hj
  rw [heq] at hj
  let L := (compL ℝ Vec3 (Vec3 × ℝ) Vec3).flip (inl ℝ Vec3 ℝ)
  exact (L.hasFDerivAt.comp_hasDerivAt t hj).hasDerivWithinAt

/-- If the potential's time derivative commutes with its label jet,
the actual time derivative of the divergence correction is the
curl and commutator appearing in the relay formula. -/
theorem derivWithin_waveCompletion_add_pressure {I : Set ℝ} {t : ℝ} {x : Vec3 × ℝ}
    {Q : ℝ → Vec3 × ℝ → Vec3} {Qt : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ}
    {G : ℝ → Vec3 →L[ℝ] Vec3} {M : Vec3 →L[ℝ] Vec3}
    (hI : UniqueDiffWithinAt ℝ I t)
    (hJet : HasDerivWithinAt (fun r => hierarchyRelayLabelJet (Q r) x)
      (hierarchyRelayLabelJet Qt x) I t)
    (hG : HasDerivWithinAt G (-((G t).comp M)) I t) :
    derivWithin (fun r => curlOfDerivative ((hierarchyRelayLabelJet (Q r) x).comp (G r))) I t +
        M (curlOfDerivative ((hierarchyRelayLabelJet (Q t) x).comp (G t))) +
        (G t).adjoint ((InnerProductSpace.toDual ℝ Vec3).symm (hierarchyRelayLabelJet p x)) =
      hierarchyLinearRelayAt (G t) M (Q t) Qt p x := by
  rw [pulledBackCurl_material_eq hI hJet hG]
  rfl

/-- An all-order bound for the normalized linear relay assembled from
the actual curl, its commutator, and the inverse-coframe gradient.
Each row has its own coefficient budget and every primitive profile is
used at order `n + 1`. The single inverse frequency is common to them. -/
theorem hierarchyFiniteWordNorm_linearRelay_le
    {ℓ h freq A B C Q₀ Qt₀ p₀ : ℝ} (n : ℕ) (hℓ : ℓ ≠ 0) (hf : 0 < freq)
    {G M : T → Vec3 × ℝ → Vec3 →L[ℝ] Vec3}
    {Q Qt : T → Vec3 × ℝ → Vec3} {p : T → Vec3 × ℝ → ℝ}
    (hQ : ∀ t, ContDiff ℝ ∞ (Q t)) (hQt : ∀ t, ContDiff ℝ ∞ (Qt t))
    (hp : ∀ t, ContDiff ℝ ∞ (p t))
    (hQN : HierarchyRelayWordBound ℓ h (n + 1) Q₀ Q)
    (hQtN : HierarchyRelayWordBound ℓ h (n + 1) Qt₀ Qt)
    (hpN : HierarchyRelayWordBound ℓ h (n + 1) p₀ p)
    (hG : ∀ i t, ContDiff ℝ ∞ (fun x => hierarchyRelayCurlRow ℓ (G t x) i))
    (hMG : ∀ i t, ContDiff ℝ ∞ (fun x => hierarchyRelayMaterialRow ℓ (G t x) (M t x) i))
    (hP : ∀ i t, ContDiff ℝ ∞ (fun x => hierarchyRelayPressureRow ℓ (G t x) i))
    (hGN : ∀ i, HierarchyRelayWordBound ℓ h n A
      (fun t x => hierarchyRelayCurlRow ℓ (G t x) i))
    (hMGN : ∀ i, HierarchyRelayWordBound ℓ h n B
      (fun t x => hierarchyRelayMaterialRow ℓ (G t x) (M t x) i))
    (hPN : ∀ i, HierarchyRelayWordBound ℓ h n C
      (fun t x => hierarchyRelayPressureRow ℓ (G t x) i)) :
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun t x => freq⁻¹ • hierarchyLinearRelayAt (G t x) (M t x) (Q t) (Qt t) (p t) x) ≤
      (hierarchyAdmissibleWords (Fin 4) n).card *
        (freq⁻¹ * (3 * ((2 : ℝ) ^ n * A * Qt₀ + (2 : ℝ) ^ n * B * Q₀ + (2 : ℝ) ^ n * C * p₀))) := by
  let d (i : Fin 3) := hierarchyMixedDirection ℓ h i.castSucc
  let f₁ (i : Fin 3) (t : T) (x : Vec3 × ℝ) :=
    hierarchyRelayCurlRow ℓ (G t x) i (phaseDirectionalDerivative (d i) (Qt t) x)
  let f₂ (i : Fin 3) (t : T) (x : Vec3 × ℝ) :=
    hierarchyRelayMaterialRow ℓ (G t x) (M t x) i (phaseDirectionalDerivative (d i) (Q t) x)
  let f₃ (i : Fin 3) (t : T) (x : Vec3 × ℝ) :=
    hierarchyRelayPressureRow ℓ (G t x) i (phaseDirectionalDerivative (d i) (p t) x)
  have h₁ (i) (t) : ContDiff ℝ ∞ (f₁ i t) :=
    (hG i t).clm_apply (((hQt t).fderiv_right (by simp)).clm_apply contDiff_const)
  have h₂ (i) (t) : ContDiff ℝ ∞ (f₂ i t) :=
    (hMG i t).clm_apply (((hQ t).fderiv_right (by simp)).clm_apply contDiff_const)
  have h₃ (i) (t) : ContDiff ℝ ∞ (f₃ i t) :=
    (hP i t).clm_apply (((hp t).fderiv_right (by simp)).clm_apply contDiff_const)
  have b₁ (i) : HierarchyRelayWordBound ℓ h n ((2 : ℝ) ^ n * A * Qt₀) (f₁ i) :=
    hierarchyRelayWordBound_labelTerm (hG i) hQt (hGN i) hQtN i
  have b₂ (i) : HierarchyRelayWordBound ℓ h n ((2 : ℝ) ^ n * B * Q₀) (f₂ i) :=
    hierarchyRelayWordBound_labelTerm (hMG i) hQ (hMGN i) hQN i
  have b₃ (i) : HierarchyRelayWordBound ℓ h n ((2 : ℝ) ^ n * C * p₀) (f₃ i) :=
    hierarchyRelayWordBound_labelTerm (hP i) hp (hPN i) hpN i
  have hs (i : Fin 3) (t : T) : ContDiff ℝ ∞ (fun x => f₁ i t x + f₂ i t x + f₃ i t x) :=
    ((h₁ i t).add (h₂ i t)).add (h₃ i t)
  have hsum (t : T) : ContDiff ℝ ∞ (fun x => ∑ i, (f₁ i t x + f₂ i t x + f₃ i t x)) := by
    simpa only [Finset.sum_apply] using (ContDiff.sum (s := Finset.univ) (fun i _ => hs i t))
  have hb := relayWordBound_sum (Finset.univ : Finset (Fin 3)) (fun i _ => hs i)
    (fun i _ => relayWordBound_add (fun t => (h₁ i t).add (h₂ i t)) (h₃ i)
      (relayWordBound_add (h₁ i) (h₂ i) (b₁ i) (b₂ i)) (b₃ i))
  have hbound := (relayWordBound_const_smul hsum hb freq⁻¹).finiteNorm_le
  simp_rw [hierarchyLinearRelayAt_eq_coordinate_sum hℓ h]
  simpa [d, f₁, f₂, f₃, Real.norm_eq_abs, abs_of_pos hf, mul_add] using hbound

/-- A finite smooth coefficient budget shared by the normalized
potential and pressure operators and the inverse-radius coframe rows. -/
def HierarchyRelayCoefficientJets (ℓ h : ℝ) (n : ℕ) (K : ℝ)
    (c : T → Vec3 → E) : Prop :=
  (∀ t, ContDiff ℝ ∞ (fun x : Vec3 × ℝ => c t x.1)) ∧
    HierarchyRelayWordBound ℓ h n K (fun t x => c t x.1)

/-- The slope in the parent coefficient jet estimate disappears from
the finite budget under the envelope-radius condition. The power
remaining in `A` is independent of the derivative order. -/
theorem HierarchyRelayCoefficientJets.of_parent_power_bound
    {ℓ h D A : ℝ} {n q : ℕ} {c : T → Vec3 → E} {C : ℕ → ℝ}
    (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hA : 0 ≤ A) (hscale : ℓ * D ^ q ≤ 1)
    (hc : ∀ t, ContDiff ℝ ∞ (c t)) (hC : ∀ j ≤ n, 0 ≤ C j)
    (hjets : ∀ t j, j ≤ n → ∀ a,
      ‖iteratedFDeriv ℝ j (c t) a‖ ≤ C j * A * D ^ (q * j)) :
    HierarchyRelayCoefficientJets ℓ h n ((∑ j ∈ Finset.range (n + 1), C j) * A) c := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), C j :=
    Finset.sum_nonneg fun j hj => hC j (by have hj := Finset.mem_range.mp hj; omega)
  refine ⟨fun t => (hc t).comp contDiff_fst,
    hierarchyRelayWordBound_of_phaseIndependent hℓ (mul_nonneg hsum hA) hc ?_⟩
  intro t j hj a
  have hCn : C j ≤ ∑ i ∈ Finset.range (n + 1), C i :=
    Finset.single_le_sum (fun i hi => hC i (by have hi := Finset.mem_range.mp hi; omega))
      (Finset.mem_range.mpr (by omega))
  calc
    _ ≤ ℓ ^ j * (C j * A * D ^ (q * j)) :=
      mul_le_mul_of_nonneg_left (hjets t j hj a) (pow_nonneg hℓ _)
    _ = (ℓ * D ^ q) ^ j * (C j * A) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ C j * A :=
      mul_le_of_le_one_left (mul_nonneg (hC j hj) hA)
        (pow_le_one₀ (mul_nonneg hℓ (pow_nonneg hD _)) hscale)
    _ ≤ _ := mul_le_mul_of_nonneg_right hCn hA

private theorem relayWordBound_zero (ℓ h : ℝ) (n : ℕ) :
    HierarchyRelayWordBound ℓ h n 0 (fun (_ : T) (_ : Vec3 × ℝ) => (0 : E)) := by
  have hz (w : List (Fin 4)) :
      phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun _ => (0 : E)) = fun _ => 0 := by
    induction w with
    | nil => rfl
    | cons i w ih =>
      rw [phaseOperatorWord, ih]
      funext x
      simp [phaseDirectionalDerivative]
  refine ⟨le_rfl, fun w _ t x => ?_⟩
  simp only [hz, norm_zero, le_refl]

set_option maxHeartbeats 1200000 in
/-- Weighted bound for the actual four terms of the linear relay. The
input profiles may already be divided by the time weight, which is
constant in the label and phase differentiated here. Every profile
is read through order `n + 1`, and the covector normalization provides
one inverse frequency. The coefficient budget is for the concrete
operators displayed in (5.31)–(5.33). -/
theorem hierarchyFiniteWordNorm_waveLinearRelay_le
    {ℓ h freq K V₀ F₀ : ℝ} (n : ℕ) (hℓ : ℓ ≠ 0) (hfreq : 0 < freq)
    {G M : T → Vec3 → Vec3 →L[ℝ] Vec3} {k : T → Vec3 → Vec3}
    {V f : T → Vec3 × ℝ → Vec3}
    (hV : ∀ t, ContDiff ℝ ∞ (V t)) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hVp : ∀ t a, Function.Periodic (fun s => V t (a,s)) 1)
    (hfp : ∀ t a, Function.Periodic (fun s => f t (a,s)) 1)
    (hVz : ∀ t a, phaseMean (fun s => V t (a,s)) = 0)
    (hfz : ∀ t a, phaseMean (fun s => f t (a,s)) = 0)
    (hVN : HierarchyRelayWordBound ℓ h (n + 1) V₀ V)
    (hfN : HierarchyRelayWordBound ℓ h (n + 1) F₀ f)
    (hKq : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun t a => hierarchyRelayPotentialCoefficient (k t a)))
    (hKqt : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun t a => hierarchyRelayTimeAmplitudeCoefficient (M t a) (k t a)))
    (hKpv : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun t a => hierarchyRelayPressureAmplitudeCoefficient (M t a) (k t a)))
    (hKpf : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun t a => hierarchyRelayPressureSourceCoefficient (k t a)))
    (hG : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun t a => hierarchyRelayCurlRow ℓ (G t a) i))
    (hMG : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun t a => hierarchyRelayMaterialRow ℓ (G t a) (M t a) i))
    (hP : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun t a => hierarchyRelayPressureRow ℓ (G t a) i)) :
    let κ (t : T) (a : Vec3) := freq • k t a
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun t x => hierarchyLinearRelayAt (G t x.1) (M t x.1)
        (relayPotentialProfile (κ t) (V t)) (relayPotentialTimeProfile (M t) (κ t) (V t) (f t))
        (relayPhasePressureProfile (M t) (κ t) (V t) (f t)) x) ≤
      (18 * (hierarchyAdmissibleWords (Fin 4) n).card *
        (hierarchyAdmissibleWords (Fin 4) (n + 1)).card * (2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)) *
          K ^ 2 * freq⁻¹ * (V₀ + F₀) := by
  let B := 2 * ((hierarchyAdmissibleWords (Fin 4) (n + 1)).card *
      ((2 : ℝ) ^ (n + 1) * K * V₀ + (2 : ℝ) ^ (n + 1) * K * F₀))
  have hK : 0 ≤ K := hKq.2.1
  have hf₀ : 0 ≤ F₀ := hfN.1
  obtain ⟨hsq, hbq⟩ := hierarchyRelayWordBound_linearPrimitive
    (a := fun t a => hierarchyRelayPotentialCoefficient (k t a))
    (b := fun t a => hierarchyRelayPotentialCoefficient (k t a))
    (f := fun _ _ => 0) hKq.1 hKq.1 hV
    (fun _ => contDiff_const) hVp (fun _ _ _ => rfl) hVz
    (fun _ _ => phaseMean_const 0) hKq.2 hKq.2 hVN
    (relayWordBound_zero (T := T) (E := Vec3) ℓ h (n + 1))
  simp only [map_zero, add_zero, mul_zero] at hsq hbq
  have hsq' (t) : ContDiff ℝ ∞ (relayPotentialProfile (k t) (V t)) := hsq t
  have hbq' : HierarchyRelayWordBound ℓ h (n + 1) B
      (fun t => relayPotentialProfile (k t) (V t)) := by
    have he : (fun t x => phasePrimitive (fun s =>
        hierarchyRelayPotentialCoefficient (k t x.1) (V t (x.1,s))) x.2) =
        fun t => relayPotentialProfile (k t) (V t) := rfl
    rw [← he]
    refine relayWordBound_mono hbq le_rfl ?_
    dsimp only [B]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (Nat.cast_nonneg _)) (by norm_num)
  obtain ⟨hsqt, hbqt⟩ := hierarchyRelayWordBound_linearPrimitive
    (a := fun t a => hierarchyRelayTimeAmplitudeCoefficient (M t a) (k t a))
    (b := fun t a => hierarchyRelayPotentialCoefficient (k t a))
    hKqt.1 hKq.1 hV hf hVp hfp hVz hfz hKqt.2 hKq.2 hVN hfN
  obtain ⟨hsp, hbp⟩ := hierarchyRelayWordBound_linearPrimitive
    (a := fun t a => hierarchyRelayPressureAmplitudeCoefficient (M t a) (k t a))
    (b := fun t a => hierarchyRelayPressureSourceCoefficient (k t a))
    hKpv.1 hKpf.1 hV hf hVp hfp hVz hfz hKpv.2 hKpf.2 hVN hfN
  have hqe (t : T) : relayPotentialTimeProfile (M t) (k t) (V t) (f t) =
      fun x => phasePrimitive (fun s =>
        hierarchyRelayTimeAmplitudeCoefficient (M t x.1) (k t x.1) (V t (x.1,s)) +
        hierarchyRelayPotentialCoefficient (k t x.1) (f t (x.1,s))) x.2 := by
    funext x
    simp only [relayPotentialTimeProfile, wavePotentialTimeSource_eq_coefficients]
  have hpe (t : T) : relayPhasePressureProfile (M t) (k t) (V t) (f t) =
      fun x => phasePrimitive (fun s =>
        hierarchyRelayPressureAmplitudeCoefficient (M t x.1) (k t x.1) (V t (x.1,s)) +
        hierarchyRelayPressureSourceCoefficient (k t x.1) (f t (x.1,s))) x.2 := by
    funext x
    simp only [relayPhasePressureProfile, oscillatoryPhasePressure,
      oscillatoryPressureSlope_eq_coefficients]
  have hrs (t) : ContDiff ℝ ∞ (relayPotentialTimeProfile (M t) (k t) (V t) (f t)) := by
    rw [hqe]
    exact hsqt t
  have hrsN : HierarchyRelayWordBound ℓ h (n + 1) B
      (fun t => relayPotentialTimeProfile (M t) (k t) (V t) (f t)) := by
    simp_rw [hqe]
    exact hbqt
  have hps (t) : ContDiff ℝ ∞ (relayPhasePressureProfile (M t) (k t) (V t) (f t)) := by
    rw [hpe]
    exact hsp t
  have hpsN : HierarchyRelayWordBound ℓ h (n + 1) B
      (fun t => relayPhasePressureProfile (M t) (k t) (V t) (f t)) := by
    simp_rw [hpe]
    exact hbp
  have hb := hierarchyFiniteWordNorm_linearRelay_le (A := K) (B := K) (C := K)
    (G := fun t x => G t x.1) (M := fun t x => M t x.1)
    n hℓ hfreq hsq' hrs hps hbq' hrsN hpsN
    (fun i => (hG i).1) (fun i => (hMG i).1) (fun i => (hP i).1)
    (fun i => (hG i).2) (fun i => (hMG i).2) (fun i => (hP i).2)
  have heq (t : T) (x : Vec3 × ℝ) :
      hierarchyLinearRelayAt (G t x.1) (M t x.1)
        (relayPotentialProfile (fun a => freq • k t a) (V t))
        (relayPotentialTimeProfile (M t) (fun a => freq • k t a) (V t) (f t))
        (relayPhasePressureProfile (M t) (fun a => freq • k t a) (V t) (f t)) x =
      freq⁻¹ • hierarchyLinearRelayAt (G t x.1) (M t x.1) (relayPotentialProfile (k t) (V t))
        (relayPotentialTimeProfile (M t) (k t) (V t) (f t))
        (relayPhasePressureProfile (M t) (k t) (V t) (f t)) x :=
    hierarchyLinearRelayAt_frequency_scale hfreq _ _ _ _ _ _
      ((hsq' t).differentiable (by simp) x) ((hrs t).differentiable (by simp) x)
      ((hps t).differentiable (by simp) x)
  dsimp only
  simp_rw [heq]
  refine hb.trans_eq ?_
  dsimp only [B]
  ring

end FiniteOrder

end

end TorusEuler
