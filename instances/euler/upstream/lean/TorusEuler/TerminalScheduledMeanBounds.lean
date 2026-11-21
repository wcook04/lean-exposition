import TorusEuler.TerminalMeanGain
import TorusEuler.TerminalMeanGainCosts
import TorusEuler.TerminalMeanFlowCoefficientBounds
import TorusEuler.TerminalScheduledParentCoefficients
import TorusEuler.TerminalScheduleCosts

/-! The mean row of the mixed recurrence on the exact scheduled parent. -/

open Set Finset
open scoped ContDiff

namespace TorusEuler.ScheduledEulerConstruction

open HierarchyTwistedProfile

noncomputable section

local notation "Mat" => (Vec3 →L[ℝ] Vec3)
local notation "Leray" => endpointStrongSpatialLeray

private def terminalMeanWordConstant (C : ℕ → ℝ) (m : ℕ) : ℝ :=
  6 * ∑ j ∈ Finset.range (m + 1), (C j + C (j + 1))

private theorem terminalMeanWordConstant_nonneg {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (m : ℕ) :
    0 ≤ terminalMeanWordConstant C m :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => add_nonneg (hC j) (hC (j+1)))

private theorem terminalMeanWordConstant_dominates {C C' : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hCC : ∀ j, C' j ≤ C j) {n m : ℕ} (hm : m ≤ n) :
    6 * (C' m + C' (m+1)) ≤ terminalMeanWordConstant C n := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (add_le_add (hCC m) (hCC (m+1))).trans
    (Finset.single_le_sum (f := fun j => C j + C (j+1))
      (fun j _ => add_nonneg (hC j) (hC (j+1))) (Finset.mem_range.mpr (by omega)))

private theorem mixedCoefficientWordCap {T ℓ D : ℝ} (hT : 0 < T) (hℓ : 0 < ℓ)
    (hD : 1 ≤ D) (scale e n q : ℕ) {C C' : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hC' : ∀ j, 0 ≤ C' j) (hCC' : ∀ j, C' j ≤ C j)
    (hScale : ℓ * D ^ scale ≤ 1) {f : ℝ → Vec3 → Mat}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hRaw : TerminalMixedJetBound 0 T q scale D (D ^ e) C' f)
    (jet : EndpointSlabHalfHolderJets T coordinateDirection (Function.uncurry f))
    (i : ℕ) (hi : i ≤ q) (w : List (Fin 3)) (hw : w.length ≤ n) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ℓ ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤
      terminalMeanWordConstant C n * D ^ (e + scale) := by
  have hD₀ := zero_le_one.trans hD
  have hA : 0 ≤ D ^ e := pow_nonneg hD₀ _
  refine (jet.mul_norm_terminalTimeJet_le_rawJets hT hℓ hD hA hf scale i C' hC' hScale
    (hRaw i hi) w t ht).trans ?_
  rw [pow_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (terminalMeanWordConstant_dominates hC hCC' hw) hA) (pow_nonneg hD₀ _)

private theorem meanSource_scheduledWordCap {T ℓ h D : ℝ} {k : Vec3} {hT : 0 < T}
    {G M : HierarchyTwistedProfile T k Mat} {κ force : HierarchyTwistedProfile T k Vec3}
    (hT₁ : T ≤ 1) (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (hD : 1 ≤ D) (hTime : T⁻¹ ≤ D)
    (a : ℕ) (hRadius : ℓ⁻¹ ≤ D ^ a)
    (hForce : (twistedHierarchyOperators hT G M κ).average force = force) (q m : ℕ)
    (jet : EndpointSlabHalfHolderJets T coordinateDirection
      (fun z => force.val.val.val (z.1,z.2,0)))
    (i : ℕ) (hi : i ≤ q) (w : List (Fin 3)) (hw : w.length ≤ m) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ℓ ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤
      (4 * (q.factorial : ℝ) * D ^ (q + a)) *
        timeJetSeminorm hT q (unweightedSeminorm False ℓ h (m+1) hT) force := by
  let Z := timeJetSeminorm hT q (unweightedSeminorm False ℓ h (m+1) hT) force
  let F (t : ℝ) (x : Vec3) := force.val.val.val (t,x,0)
  let L := hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (m + 1)
    (fun r : Icc 0 T => slabTimeJet 0 T i F r)
  obtain ⟨hF, hPer, _⟩ := meanSource_properties hT G M κ force hForce
  have hcap := jet.mul_norm_terminalTimeJet_le_labelNorm hT hℓ hℓ₁ hF hPer m i w hw t ht
  have hL : L ≤ (q.factorial : ℝ) * T⁻¹ ^ q * Z :=
    meanSource_timeJet_labelNorm_le (S := force) hT₁ (ℓ := ℓ) (h := h) (m+1) hForce i hi
  have hD₀ := zero_le_one.trans hD
  have hTime' : T⁻¹ ^ q ≤ D ^ q := pow_le_pow_left₀ (inv_nonneg.mpr hT.le) hTime _
  have hZ : 0 ≤ Z := apply_nonneg _ _
  have hSqrt₀ := Real.sqrt_nonneg ℓ
  have hSqrt : ℓ ≤ Real.sqrt ℓ := by
    calc
      ℓ = Real.sqrt ℓ * Real.sqrt ℓ := (Real.mul_self_sqrt hℓ.le).symm
      _ ≤ 1 * Real.sqrt ℓ := mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr hℓ₁) hSqrt₀
      _ = _ := one_mul _
  have hSqrtInv : (Real.sqrt ℓ)⁻¹ ≤ D ^ a := (inv_anti₀ hℓ hSqrt).trans hRadius
  change _ ≤ (4 * (q.factorial : ℝ) * D ^ (q + a)) * Z
  calc
    _ ≤ 4 * L / Real.sqrt ℓ := hcap
    _ ≤ (4 * ((q.factorial : ℝ) * D ^ q * Z)) * (D ^ a) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul _ hSqrtInv (inv_nonneg.mpr hSqrt₀) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hL.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hTime' (Nat.cast_nonneg _)) hZ)
    _ = _ := by rw [pow_add]; ring

set_option maxHeartbeats 6500000 in
/-- The exact mean solver of the scheduled approximation gains one time
derivative. The radius threshold is uniform in the time order, and the
remaining constants depend on the fixed derivative orders. -/
theorem exists_scheduledMeanTimeBounds :
    ∃ a₀ : ℕ, 16 ≤ a₀ ∧ ∀ (q E : ℕ) (C : ℕ → ℝ), (∀ m, 0 ≤ C m) →
      ∃ (r₀ : ℕ) (K : ℕ → ℝ), (∀ m, 0 ≤ K m) ∧
        ∀ {P : InductiveEulerParameters} (c : TorusEuler.ScheduledEulerConstruction P) (n : ℕ),
          a₀ ≤ c.radiusExponent → Real.exp 1 ≤ P.frequency 0 → 2 ≤ P.frequency (n+1) →
          c.ScheduledParentCoefficientTimeBounds n q E C →
          let d := (c.selectedStep n).selected
          let D := P.frequency (n+1) ^ (9 : ℕ)
          ∀ (m : ℕ) (force : HierarchyTwistedProfile (c.construction.slab (n+2)) d.carrier Vec3)
            (hForce : d.approximation.operators.average force = force),
            timeJetSeminorm d.time_pos (q+1) (unweightedSeminorm False d.radius d.width m d.time_pos)
              (d.approximation.solvers.solveMean force hForce).val.B ≤
            (K m * D ^ (r₀ + c.radiusExponent)) *
              timeJetSeminorm d.time_pos q (unweightedSeminorm False d.radius d.width (m+1) d.time_pos) force := by
  obtain ⟨R, hR, hOld⟩ := InductiveEulerStage.exists_velocity_jet_bounds
  obtain ⟨p, s₀, H, hs₀, hH, hInverse⟩ := exists_terminalMeanParentInverseCaps R hR
  refine ⟨max 16 s₀, le_max_left _ _, ?_⟩
  intro q E C hC
  let Q := q+1
  obtain ⟨CK, CO, _, hCK, hCO, _, hCoefficients⟩ := exists_terminalMeanCoefficientCost C hC Q
  let Adj := terminalRealAdjoint
  let CA (j : ℕ) : ℝ := ‖Adj‖ * C j
  let Total (j : ℕ) : ℝ := C j + CA j + CK j + CO j
  have hCA (j : ℕ) : 0 ≤ CA j := mul_nonneg (norm_nonneg Adj) (hC j)
  have hTotal (j : ℕ) : 0 ≤ Total j := add_nonneg (add_nonneg (add_nonneg (hC j) (hCA j)) (hCK j)) (hCO j)
  have hCF (j : ℕ) : C j ≤ Total j := by dsimp only [Total]; linarith only [hCA j, hCK j, hCO j]
  have hCAF (j : ℕ) : CA j ≤ Total j := by dsimp only [Total]; linarith only [hC j, hCK j, hCO j]
  have hCKF (j : ℕ) : CK j ≤ Total j := by dsimp only [Total]; linarith only [hC j, hCA j, hCO j]
  have hCOF (j : ℕ) : CO j ≤ Total j := by dsimp only [Total]; linarith only [hC j, hCA j, hCK j]
  let cCoef (m : ℕ) := terminalMeanWordConstant Total m
  let eCoef := 3 * E + 16
  let Hsum (m : ℕ) : ℝ := ∑ j ∈ Finset.range (m + 1), H j
  let Kword (m : ℕ) : ℝ := 2 * (1 + ‖Leray‖) * Hsum m
  have hHs (m : ℕ) : 0 ≤ Hsum m := Finset.sum_nonneg fun j _ => hH j
  have hKw (m : ℕ) : 0 ≤ Kword m := mul_nonneg (by positivity) (hHs m)
  let I₀ (m : ℕ) : ℝ := (1 + (2 : ℝ) ^ m * Kword m) ^ m
  let A₀ (m : ℕ) : ℝ := max (I₀ m) (I₀ m * ‖Leray‖)
  let B₀ (m : ℕ) : ℝ := (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ Q + (2 : ℝ) ^ Q) * cCoef m
  let csrc : ℝ := 4 * (q.factorial : ℝ)
  let G₀ (m : ℕ) : ℝ := (2 : ℝ) ^ (m + 1 + q) * cCoef m * csrc
  let C₀ (m : ℕ) : ℝ := (2 : ℝ) ^ (m + 1 + Q) * cCoef m
  let factor (m : ℕ) : ℝ := ((Q : ℝ) + 1) * ((hierarchyAdmissibleWords (Fin 3) m).card : ℝ)
  let K (m : ℕ) : ℝ := factor m * (C₀ m * ((1 + A₀ m * (1 + B₀ m)) ^ (Q + 1) * G₀ m))
  let r₀ := (p + eCoef) * (Q + 1) + 2 * eCoef + q
  have hCoef (m : ℕ) : 0 ≤ cCoef m := terminalMeanWordConstant_nonneg hTotal m
  have hI₀ (m : ℕ) : 0 ≤ I₀ m := pow_nonneg (add_nonneg zero_le_one (mul_nonneg (by positivity) (hKw m))) _
  have hA₀ (m : ℕ) : 0 ≤ A₀ m := (hI₀ m).trans (le_max_left _ _)
  have hB₀ (m : ℕ) : 0 ≤ B₀ m := mul_nonneg (by positivity) (hCoef m)
  have hG₀ (m : ℕ) : 0 ≤ G₀ m := mul_nonneg (mul_nonneg (by positivity) (hCoef m)) (by dsimp only [csrc]; positivity)
  have hC₀ (m : ℕ) : 0 ≤ C₀ m := mul_nonneg (by positivity) (hCoef m)
  have hFactor (m : ℕ) : 0 ≤ factor m := by dsimp only [factor]; positivity
  have hK (m : ℕ) : 0 ≤ K m := mul_nonneg (hFactor m) (mul_nonneg (hC₀ m)
    (mul_nonneg (pow_nonneg (add_nonneg zero_le_one (mul_nonneg (hA₀ m)
      (add_nonneg zero_le_one (hB₀ m)))) _) (hG₀ m)))
  refine ⟨r₀, K, hK, ?_⟩
  intro P c n ha₀ hInitial hμ₂ hb d D m force hForce
  let tip := c.construction.tip n
  let T := c.construction.slab (n+2)
  let μ := P.frequency (n+1)
  let ell := d.radius
  let h := d.width
  let geom := d.parent.geometry
  let md := geom.mean
  let ht := d.time_pos
  let hT₁ := d.time_le_one
  let r := solveMean ht hT₁ geom.inverse geom.strain geom.covector md force hForce
  let ff (t : ℝ) (x : Vec3) := force.val.val.val (t,x,0)
  let F (t : ℝ) (x : Vec3) := md.deformation (t, toUnitTorus x)
  let M (t : ℝ) (x : Vec3) := md.strain (t, toUnitTorus x)
  have hμ : 1 ≤ μ := one_le_two.trans hμ₂
  have hD₂ : 2 ≤ D := d.parent_scale_ge_two
  have hD : 1 ≤ D := one_le_two.trans hD₂
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hEll : 0 < ell := d.regularity.envelope_pos
  have hEll₁ : ell ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hD)
  have ha : s₀ ≤ c.radiusExponent := (le_max_right _ _).trans ha₀
  have hRadius : ell * D ^ (16 : ℕ) ≤ 1 :=
    d.radius_mul_parent_power ((le_max_left _ _).trans ha₀)
  have hTime : T⁻¹ ≤ D := by
    calc
      _ ≤ μ ^ (1 / 8 : ℝ) := P.terminal_slab_inv_le hInitial (n+1) tip.next_activation_nonnegative
      _ ≤ μ ^ (9 : ℝ) := Real.rpow_le_rpow_of_exponent_le hμ (by norm_num)
      _ = D := Real.rpow_natCast _ _
  have hOldF (t : ℝ) (h_t : t ∈ Icc 0 T) (x : Vec3) :
      ‖fderiv ℝ (tip.parent.flow 0 t) x‖ ≤ D :=
    (d.parent.raw_coframe_norm_le_frequency_nine hμ₂ h_t x).1
  have hOldG (t : ℝ) (h_t : t ∈ Icc 0 T) (x : Vec3) :
      ‖fderiv ℝ (tip.parent.flow t 0) (tip.parent.flow 0 t x)‖ ≤ D :=
    (d.parent.raw_coframe_norm_le_frequency_nine hμ₂ h_t x).2
  have hFEq (t : ℝ) (h_t : t ∈ Icc 0 T) (x : Vec3) :
      F t x = fderiv ℝ (tip.parent.flow 0 t) x := geom.deformation_value t h_t x
  have hMEq (t : ℝ) (h_t : t ∈ Icc 0 T) (x : Vec3) :
      M t x = fderiv ℝ (tip.parent.velocity t) (tip.parent.flow 0 t x) :=
    (md.strain_value (t,x,0) ⟨h_t, mem_univ _⟩).symm.trans
      (geom.strain_value (t,x,0) ⟨h_t, mem_univ _⟩)
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    md.deformation_smooth
  have hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    md.strain_smooth
  let recovery := r.recovery.weakenInverseBound (zero_lt_one.trans_le md.inverse_bound_ge_one)
    (d.parent.inverse_bound.le.trans d.parent_frequency_le_scale) md.strain_bound_nonneg
  obtain ⟨⟨inv⟩, hPosWords⟩ := hInverse ht hT₁ hD₂ md.strain_bound_nonneg
    d.parent.strain_bound.le d.parent.deformationOn.flow d.parent.smooth_velocity
    (fun t _ => tip.parent.periodic_velocity t) hOldF hOldG
    (fun j i hi hij t h_t x => hOld tip.parent hμ j i hi hij t (d.parent.subset h_t) x)
    md.deformation md.strain ff r.rawVelocity hF hM hFEq hMEq recovery
  let Kcurve := recovery.jets.kinetic.curve
  let Ocurve := recovery.jets.vorticity.curve
  have hSmall : D ^ p * D ^ (9 : ℕ) * Real.sqrt ell ≤ 1 :=
    meanScalarRadius_absorbs_inverse hD (le_rfl : D ^ p ≤ D ^ p) (hs₀.trans ha)
  have hHle (w : List (Fin 3)) (hw : w.length ≤ m) : H w.length ≤ Hsum m :=
    Finset.single_le_sum (f := H) (fun j _ => hH j) (Finset.mem_range.mpr (by omega))
  have hK0 (w : List (Fin 3)) (hw₁ : 1 ≤ w.length) (hw : w.length ≤ m) (t : ℝ)
      (h_t : t ∈ Icc 0 T) :
      D ^ p * (ell ^ w.length * (2 * ‖Leray‖ * ‖Kcurve w t‖)) ≤ Kword m := by
    have hPoint : ‖Kcurve w t‖ ≤ endpointClosedTimeNorm T (Kcurve w) :=
      norm_le_endpointClosedTimeNorm (recovery.jets.kinetic.smooth w).continuousOn h_t
    have hRaw := hPosWords c.radiusExponent ha w hw₁
    have hStep : D ^ p * (ell ^ w.length * ‖Kcurve w t‖) ≤ Hsum m := by
      calc
        _ ≤ D ^ p * (ell ^ w.length * (endpointClosedTimeNorm T (Kcurve w) +
            endpointClosedTimeNorm T (Ocurve w))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hPoint.trans (le_add_of_nonneg_right (endpointClosedTimeNorm_nonneg ht.le _)))
            (pow_nonneg hEll.le _)) (pow_nonneg hD₀ _)
        _ ≤ D ^ p * (H w.length * D ^ 9 * Real.sqrt ell) :=
          mul_le_mul_of_nonneg_left hRaw (pow_nonneg hD₀ _)
        _ = (D ^ p * D ^ 9 * Real.sqrt ell) * H w.length := by ring
        _ ≤ H w.length := mul_le_of_le_one_left (hH _) hSmall
        _ ≤ Hsum m := hHle w hw
    calc
      _ = (2 * ‖Leray‖) * (D ^ p * (ell ^ w.length * ‖Kcurve w t‖)) := by ring
      _ ≤ (2 * ‖Leray‖) * Hsum m := mul_le_mul_of_nonneg_left hStep (by positivity)
      _ ≤ Kword m := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) zero_le_two) (hHs m)
  have hBaseK (w : List (Fin 3)) (hw₁ : 1 ≤ w.length) (hw : w.length ≤ m) :
      D ^ p * (ell ^ w.length * endpointPhysicalCoefficientWordNorm T Kcurve Ocurve w) ≤ Kword m := by
    have h₁ := endpointPhysicalCoefficientWordNorm_threshold ht.le hT₁ hEll.le (pow_nonneg hD₀ p)
      (hH w.length) Kcurve Ocurve w (hPosWords c.radiusExponent ha w hw₁) hSmall
    refine h₁.trans ((mul_le_mul_of_nonneg_left (hHle w hw) zero_le_two).trans ?_)
    dsimp only [Kword]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hHs m)
      (le_add_of_nonneg_right (norm_nonneg Leray))) zero_le_two
  have hFraw := hb.forward.congr (fun t h_t x => (hFEq t h_t x).symm)
  have hMraw := hb.gradient.congr (fun t h_t x => (hMEq t h_t x).symm)
  have hDE : 0 ≤ D ^ E := pow_nonneg hD₀ _
  have hEamp : D ^ E ≤ D ^ (3 * E) := pow_le_pow_right₀ hD (by omega)
  obtain ⟨hKraw, hOraw, _⟩ := hCoefficients ht hD₀ hDE hF hM hFraw hMraw
  have hE2 : D ^ E * D ^ E ≤ D ^ (3 * E) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hD (by omega)
  have hE3 : D ^ E * (D ^ E * D ^ E) = D ^ (3 * E) := by
    rw [← pow_add, ← pow_add, show E + (E + E) = 3 * E by omega]
  let FK (t : ℝ) (x : Vec3) := kineticForm (F t x)
  let FO (t : ℝ) (x : Vec3) := vorticityForm (F t x) (M t x)
  let Fadj (t : ℝ) (x : Vec3) := (F t x).adjoint
  have hAdjF : ContDiffOn ℝ ∞ (Function.uncurry Fadj) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    Adj.contDiff.comp_contDiffOn hF
  have hAdjM : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (M z.1 z.2).adjoint)
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    Adj.contDiff.comp_contDiffOn hM
  have hFK : ContDiffOn ℝ ∞ (Function.uncurry FK) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hAdjF.clm_comp hF
  have hFO : ContDiffOn ℝ ∞ (Function.uncurry FO) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hAdjF.clm_comp ((hAdjM.sub hM).clm_comp hF)
  have hRawK : TerminalMixedJetBound 0 T Q 16 D (D ^ (3 * E)) CK FK :=
    hKraw.mono_amplitude hD₀ hCK hE2
  have hRawO : TerminalMixedJetBound 0 T Q 16 D (D ^ (3 * E)) CO FO :=
    hOraw.mono_amplitude hD₀ hCO hE3.le
  have hRawF : TerminalMixedJetBound 0 T Q 16 D (D ^ (3 * E)) C F :=
    hFraw.mono_amplitude hD₀ hC hEamp
  have hRawAdj : TerminalMixedJetBound 0 T Q 16 D (D ^ (3 * E)) CA Fadj :=
    (hFraw.apply_clm ht hF Adj).mono_amplitude hD₀ hCA hEamp
  let χ := cCoef m * D ^ eCoef
  let Z := timeJetSeminorm ht q (unweightedSeminorm False ell h (m+1) ht) force
  let χsrc := csrc * D ^ (q + c.radiusExponent)
  have hχ : 0 ≤ χ := mul_nonneg (hCoef m) (pow_nonneg hD₀ _)
  have hχsrc : 0 ≤ χsrc := mul_nonneg (by dsimp only [csrc]; positivity) (pow_nonneg hD₀ _)
  have hZ : 0 ≤ Z := apply_nonneg _ _
  have hTimeK (i : ℕ) (hi : i ≤ Q) (w : List (Fin 3)) (hw : w.length ≤ m)
      (t : ℝ) (h_t : t ∈ Icc 0 T) :
      ell ^ w.length * ‖terminalTimeJet T i (Kcurve w) t‖ ≤ χ ∧
        ell ^ w.length * ‖terminalTimeJet T i (Ocurve w) t‖ ≤ χ :=
    ⟨mixedCoefficientWordCap ht hEll hD 16 (3*E) m Q hTotal hCK hCKF hRadius hFK
        hRawK recovery.jets.kinetic i hi w hw h_t,
      mixedCoefficientWordCap ht hEll hD 16 (3*E) m Q hTotal hCO hCOF hRadius hFO
        hRawO recovery.jets.vorticity i hi w hw h_t⟩
  have hTimeF (jet : EndpointSlabHalfHolderJets T coordinateDirection (Function.uncurry F))
      (i : ℕ) (hi : i ≤ Q) (w : List (Fin 3)) (hw : w.length ≤ m)
      (t : ℝ) (h_t : t ∈ Icc 0 T) :
      ell ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤ χ :=
    mixedCoefficientWordCap ht hEll hD 16 (3*E) m Q hTotal hC hCF hRadius hF hRawF jet i hi w hw h_t
  have hTimeAdj (jet : EndpointSlabHalfHolderJets T coordinateDirection (Function.uncurry Fadj))
      (i : ℕ) (hi : i ≤ Q-1) (w : List (Fin 3)) (hw : w.length ≤ m)
      (t : ℝ) (h_t : t ∈ Icc 0 T) :
      ell ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤ χ :=
    mixedCoefficientWordCap ht hEll hD 16 (3*E) m Q hTotal hCA hCAF hRadius hAdjF hRawAdj jet i
      (hi.trans (Nat.sub_le Q 1)) w hw h_t
  have hTimeForce (jet : EndpointSlabHalfHolderJets T coordinateDirection (Function.uncurry ff))
      (i : ℕ) (hi : i ≤ Q-1) (w : List (Fin 3)) (hw : w.length ≤ m)
      (t : ℝ) (h_t : t ∈ Icc 0 T) :
      ell ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤ χsrc * Z := by
    exact meanSource_scheduledWordCap hT₁ hEll hEll₁ hD hTime c.radiusExponent d.radius_inv.le
      hForce q m jet i (by simpa only [Q, Nat.add_sub_cancel] using hi) w hw h_t
  have hGain := selectedMean_timeJetSeminorm_le_of_holderCaps (ℓ := ell) (h := h)
    r hT₁ hD hEll hForce m Q p recovery inv hχ hχsrc (hKw m) hZ hK0 hBaseK hTimeK hTimeF hTimeAdj hTimeForce
  let K₀ := D ^ p * I₀ m
  let A := max K₀ (K₀ * ‖Leray‖)
  let B := (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ Q + (2 : ℝ) ^ Q) * χ
  let G := (2 : ℝ) ^ (m + 1 + (Q - 1)) * χ * (χsrc * Z)
  let Cext := (2 : ℝ) ^ (m + 1 + Q) * χ
  have hA : 0 ≤ A := (mul_nonneg (pow_nonneg hD₀ _) (hI₀ m)).trans (le_max_left _ _)
  have hB : 0 ≤ B := mul_nonneg (by positivity) hχ
  have hG : 0 ≤ G := mul_nonneg (mul_nonneg (by positivity) hχ) (mul_nonneg hχsrc hZ)
  have hAS : A ≤ A₀ m * D ^ p := by
    apply max_le
    · dsimp only [K₀]
      rw [mul_comm (D ^ p)]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hD₀ _)
    · calc
      K₀ * ‖Leray‖ = (I₀ m * ‖Leray‖) * D ^ p := by dsimp only [K₀]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hD₀ _)
  have hBS : B ≤ B₀ m * D ^ eCoef := by
    dsimp only [B, B₀, χ]
    exact le_of_eq (by ring)
  have hGS : G ≤ G₀ m * D ^ (eCoef + (q + c.radiusExponent)) * Z := by
    dsimp only [G, G₀, Q, χ, χsrc]
    rw [Nat.add_sub_cancel, pow_add D eCoef]
    exact le_of_eq (by ring)
  have hCS : Cext ≤ C₀ m * D ^ eCoef := by dsimp only [Cext, C₀, χ]; rw [mul_assoc]
  have hpGain := terminalMeanGainPolynomial_le (q := Q) hD hA hB hG hZ
    (hA₀ m) (hB₀ m) (hG₀ m) (hC₀ m) hAS hBS hGS hCS
  change timeJetSeminorm ht Q (unweightedSeminorm False ell h m ht) r.output.B ≤
    (K m * D ^ (r₀ + c.radiusExponent)) * Z
  change timeJetSeminorm ht Q (unweightedSeminorm False ell h m ht) r.output.B ≤
    factor m * (Cext * ((1 + A * (1 + B)) ^ (Q + 1) * G)) at hGain
  refine hGain.trans ((mul_le_mul_of_nonneg_left hpGain (hFactor m)).trans_eq ?_)
  have he : (p + eCoef) * (Q + 1) + 2 * eCoef + (q + c.radiusExponent) =
      r₀ + c.radiusExponent := by dsimp only [r₀]; omega
  rw [he]
  dsimp only [K]
  ring

end

end TorusEuler.ScheduledEulerConstruction
