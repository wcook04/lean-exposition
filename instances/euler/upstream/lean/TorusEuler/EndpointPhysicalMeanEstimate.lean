import TorusEuler.EndpointPhysicalMeanSolve
import TorusEuler.EndpointPhysicalJetEstimates
import TorusEuler.EndpointPhysicalInverseCaps

/-! Quantitative estimates for the same label velocity and physical mean
returned by the closed-slab forced endpoint solve. -/

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "Coefficient" => (Vec3 →L[ℝ] Vec3)
local notation "TimeSlab(" T ")" => Icc (0 : ℝ) T
local notation "LiftSlab(" T ")" => Set.prod (TimeSlab(T)) (univ : Set Vec3)
local notation "Path(" T ")" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) T))
local notation "MixedFixed(" T ")" => freezingFixedSpace (endpointStrongMixedLeray T)

local instance quantitativeMeanSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance quantitativeMeanSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

private theorem contDiff_endpointMeanSlice {T : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × Vec3 → E} (hf : ContDiffOn ℝ ∞ f LiftSlab(T))
    {t : ℝ} (ht : t ∈ TimeSlab(T)) : ContDiff ℝ ∞ (fun x => f (t, x)) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- Increasing the inverse deformation bound weakens both coercivity
constants while preserving the recovered fields and all their spatial jets. -/
def EndpointPhysicalMeanRecovery.weakenInverseBound {T D₀ D L : ℝ}
    {hT : 0 < T} {F M : ℝ × A → Coefficient} {force v : Velocity}
    (rec : EndpointPhysicalMeanRecovery hT D₀ L F M force v)
    (hD₀ : 0 < D₀) (hD : D₀ ≤ D) (hL : 0 ≤ L) :
    EndpointPhysicalMeanRecovery hT D L F M force v := by
  have hp : 0 < D := hD₀.trans_le hD
  have hsq : D₀ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hD₀.le hD 2
  refine ⟨rec.curve, rec.jets, rec.lift_eq, rec.words, rec.projected_integrated, ?_, ?_⟩
  · intro t ht a z
    have hi : (D ^ 2)⁻¹ ≤ (D₀ ^ 2)⁻¹ :=
      (inv_le_inv₀ (pow_pos hp 2) (pow_pos hD₀ 2)).mpr hsq
    exact (mul_le_mul_of_nonneg_right hi (sq_nonneg ‖z‖)).trans
      (rec.kinetic_coercive t ht a z)
  · intro a w hw
    have hb : 2 * D₀ ^ 2 * (1 + L) ^ 2 ≤ 2 * D ^ 2 * (1 + L) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq zero_le_two) (sq_nonneg _)
    have hi : 1 / (2 * D ^ 2 * (1 + L) ^ 2) ≤ 1 / (2 * D₀ ^ 2 * (1 + L) ^ 2) := by
      rw [one_div, one_div]
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hb
    exact (mul_le_mul_of_nonneg_right hi (sq_nonneg ‖w‖)).trans (rec.mixed_coercive a w hw)

/-- Each actual source word is the negative primitive of the corresponding
word of the adjoint-deformation force. -/
theorem exists_endpointPhysicalPulledForceWords {T D L : ℝ} (hT : 0 < T)
    (F M : ℝ × A → Coefficient) (force v : Velocity)
    (rec : EndpointPhysicalMeanRecovery hT D L F M force v)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (force t)) :
    ∃ pull : List (Fin 3) → ℝ → C½,
      (∀ q, ContinuousOn (pull q) TimeSlab(T)) ∧
      (∀ q, EqOn (rec.jets.source.curve q) (fun t => -endpointPrimitive (pull q) t) TimeSlab(T)) ∧
      ∀ q t, t ∈ TimeSlab(T) → ∀ x,
        HalfHolder.eval (toUnitTorus x) (pull q t) =
          spatialDerivativeWord q (fun y => (F (t, toUnitTorus y)).adjoint (force t y)) x := by
  let f (z : ℝ × Vec3) := (F (z.1, toUnitTorus z.2)).adjoint (force z.1 z.2)
  let Adj : Coefficient ≃ₗᵢ[ℝ] Coefficient := ContinuousLinearMap.adjoint
  have hAdj : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (F (z.1, toUnitTorus z.2)).adjoint) LiftSlab(T) :=
    Adj.contDiff.comp_contDiffOn hF
  have hf : ContDiffOn ℝ ∞ f LiftSlab(T) := hAdj.clm_apply hforce
  have hfp (t : ℝ) (ht : t ∈ TimeSlab(T)) : SpatiallyPeriodic (fun x => f (t, x)) := by
    intro n x
    dsimp only [f]
    rw [(toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩, hper t ht n x]
  obtain ⟨P⟩ := exists_endpointSlabHalfHolderJets hT coordinateDirection f hf hfp
  let src := rec.jets.source.curve
  have hZero : EqOn (src []) (fun t => -endpointPrimitive (P.curve []) t) TimeSlab(T) :=
    endpointSourceCurve_eq_negPrimitive_of_lift (src []) (P.curve []) (fun t x => f (t, x))
      (P.smooth []).continuousOn (fun t ht x => P.eval_lift [] t ht x)
      (fun t ht x => rec.jets.source.eval_lift [] t ht x)
  refine ⟨P.curve, (fun q => (P.smooth q).continuousOn), ?_, ?_⟩
  · intro q
    exact endpointSourceWords_eq_negPrimitive hT src P.curve coordinateDirection q.length
      (fun r _ => (rec.jets.source.smooth r).differentiableOn (by simp))
      (fun r _ => (P.smooth r).continuousOn)
      (fun i r _ => rec.jets.source.spatialDerivative i r)
      (fun i r _ => P.spatialDerivative i r) hZero q le_rfl
  · intro q t ht x
    exact (P.eval_lift q t ht x).trans (endpointSlabSpatialWord_eq_spatialDerivativeWord hT hf q t ht x)

set_option maxHeartbeats 3200000 in
/-- A common recovery cap and the weighted coefficient and source bounds
control the actual physical mean selected by the recovered jet family. -/
theorem norm_endpointPhysicalRecoveredMean_le {T D L ℓ μ LK CK As Am Cap Cost Csrc : ℝ}
    (hT : 0 < T) (hℓ : 0 ≤ ℓ) (N : ℕ) (F M : ℝ × A → Coefficient)
    (force v B : Velocity) (rec : EndpointPhysicalMeanRecovery hT D L F M force v)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T))
    (hB : ∀ t ∈ TimeSlab(T), ∀ x, B t x = F (t, toUnitTorus x) (v t x))
    (hFbdd : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N,
      BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) q
        (fun (t : TimeSlab(T)) x => F (t.val, toUnitTorus x))))
    (hμ : 0 < μ) (hLK : 0 ≤ LK)
    (hLip : ∀ t ∈ TimeSlab(T), ∀ a b,
      ‖HalfHolder.eval a (rec.jets.kinetic.curve [] t) -
        HalfHolder.eval b (rec.jets.kinetic.curve [] t)‖ ≤ LK * dist a b)
    (hPos : ∀ t ∈ TimeSlab(T), ∀ a z,
      μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (rec.jets.kinetic.curve [] t) z, z⟫_ℝ)
    (hSup : ∀ t ∈ TimeSlab(T), ‖(rec.jets.kinetic.curve [] t).val.1‖ ≤ CK)
    (eS : ℝ → S ≃L[ℝ] S)
    (heS : ∀ t ∈ TimeSlab(T), ∀ z : S,
      eS t z = endpointStrongSpatialProjection ((rec.jets.kinetic.curve [] t).coefficientMul z.val))
    (hAs : ∀ t ∈ TimeSlab(T), ‖((eS t).symm : S →L[ℝ] S)‖ ≤ As)
    (eM : MixedFixed(T) ≃L[ℝ] MixedFixed(T))
    (heM : (eM : MixedFixed(T) →L[ℝ] MixedFixed(T)) = freezingCompression (endpointStrongMixedLeray T)
      (endpointMixedPathCoefficient hT.le (rec.jets.kineticMixed []) (rec.jets.vorticityMixed [])).coefficientMul
        (endpointStrongMixedLeray_idempotent hT))
    (hAm : ‖(eM.symm : MixedFixed(T) →L[ℝ] MixedFixed(T))‖ ≤ Am)
    (hCap : endpointPhysicalInverseBudget hT.le (rec.jets.kineticMixed []) (rec.jets.vorticityMixed []) As Am ≤ Cap)
    (hCost : 0 ≤ Cost) (hCsrc : 0 ≤ Csrc)
    (hCoefficient : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N, 1 ≤ q.length →
      Cap * (ℓ ^ q.length *
        endpointPhysicalCoefficientWordNorm T rec.jets.kinetic.curve rec.jets.vorticity.curve q) ≤ Cost)
    (hSource : ∀ q ∈ hierarchyAdmissibleWords (Fin 3) N,
      ℓ ^ q.length * endpointClosedTimeNorm T (rec.jets.source.curve q) ≤ Csrc) :
    let k : ℝ := (hierarchyAdmissibleWords (Fin 3) N).card
    let Fval := fun (t : TimeSlab(T)) x => F (t.val, toUnitTorus x)
    hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) N (fun t : TimeSlab(T) => B t) ≤
      k * (2 : ℝ) ^ N * (2 * hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) N Fval *
        (k * (Cap * Csrc * (1 + (2 : ℝ) ^ N * Cost) ^ N))) := by
  obtain ⟨w⟩ := rec.words N
  let K := rec.jets.kinetic.curve
  let Ω := rec.jets.vorticity.curve
  let src := rec.jets.source.curve
  let g := w.curve
  have hK (q : List (Fin 3)) : ContinuousOn (K q) TimeSlab(T) := (rec.jets.kinetic.smooth q).continuousOn
  have hΩ (q : List (Fin 3)) : ContinuousOn (Ω q) TimeSlab(T) := (rec.jets.vorticity.smooth q).continuousOn
  have hs (q : List (Fin 3)) : ContinuousOn (src q) TimeSlab(T) := (rec.jets.source.smooth q).continuousOn
  have hg (q : List (Fin 3)) (hq : q.length ≤ N) : ContinuousOn (g q) TimeSlab(T) :=
    (w.smooth q hq).continuousOn
  have hAs₀ : 0 ≤ As := (norm_nonneg ((eS 0).symm : S →L[ℝ] S)).trans (hAs 0 ⟨le_rfl, hT.le⟩)
  have hAm₀ : 0 ≤ Am := (norm_nonneg (eM.symm : MixedFixed(T) →L[ℝ] MixedFixed(T))).trans hAm
  have hCap₀ := (endpointPhysicalInverseBudget_nonneg hT.le (rec.jets.kineticMixed [])
    (rec.jets.vorticityMixed []) hAs₀ hAm₀).trans hCap
  have hRec := endpointPhysicalJetNormRecurrence hT rec.jets.kineticMixed rec.jets.vorticityMixed w.mixed
    rec.jets.sourceMixed K Ω src g (fun q _ => hK q) (fun q _ => hΩ q) (fun q _ => hs q) hg
    (fun q _ => ae_of_all _ (rec.jets.source_action q)) w.represents
    (fun q _ => ae_of_all _ (rec.jets.kinetic_action q))
    (fun q _ => ae_of_all _ (rec.jets.vorticity_action q))
    w.fixed w.projected_equation hμ hLK hLip hPos hSup eS heS hAs eM heM hAm
  have hRecCap (q : List (Fin 3)) (hq : q.length ≤ N) : endpointClosedTimeNorm T (g q) ≤ Cap *
      (endpointClosedTimeNorm T (src q) + ((endpointMixedCorrectionPairs q).map fun p =>
        endpointPhysicalCoefficientWordNorm T K Ω p.1 * endpointClosedTimeNorm T (g p.2)).sum) := by
    apply (hRec q hq).trans
    apply mul_le_mul_of_nonneg_right hCap
    apply add_nonneg (endpointClosedTimeNorm_nonneg hT.le _)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    have hCoeff : 0 ≤ endpointPhysicalCoefficientWordNorm T K Ω p.1 := by
      unfold endpointPhysicalCoefficientWordNorm
      exact mul_nonneg zero_le_two (add_nonneg (endpointClosedTimeNorm_nonneg hT.le _)
        (mul_nonneg hT.le (endpointClosedTimeNorm_nonneg hT.le _)))
    exact mul_nonneg hCoeff (endpointClosedTimeNorm_nonneg hT.le _)
  have h0 (q : List (Fin 3)) (hq : q.length ≤ N) (hord : q.Pairwise (· ≤ ·)) :
      q ∈ hierarchyAdmissibleWords (Fin 3) N := mem_hierarchyAdmissibleWords.mpr ⟨hq, hord⟩
  have hV := endpointWeightedPhysicalMeanEstimate_sorted hT.le hℓ hCap₀ hCsrc hCost K Ω src g
    (fun q hq hs => hSource q (h0 q hq hs))
    (fun q hpos hq hs => hCoefficient q (h0 q hq hs) hpos)
    (fun q hq _ => hRecCap q hq)
  have hcSlice (t : ℝ) (ht : t ∈ TimeSlab(T)) :
      ContDiff ℝ ∞ (fun x => F (t, toUnitTorus x)) := contDiff_endpointMeanSlice hF ht
  have hvSlice (t : ℝ) (ht : t ∈ TimeSlab(T)) : ContDiff ℝ ∞ (v t) :=
    contDiff_endpointMeanSlice hv ht
  have hEval (q : List (Fin 3)) (hq : q.length ≤ N) (t : ℝ) (ht : t ∈ TimeSlab(T)) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (g q t).val = spatialDerivativeWord q (v t) x := by
    apply eval_lift_recoveredSpatialWord (hvSlice t ht) (fun r => (g r t).val) ?_ ?_ q hq x
    · intro y
      change HalfHolder.eval (toUnitTorus y) (w.curve [] t).val = v t y
      calc
        _ = HalfHolder.eval (toUnitTorus y) (rec.curve t).val :=
          congrArg (fun u : S => HalfHolder.eval (toUnitTorus y) u.val) (w.base_eq ht)
        _ = v t y := congrArg (fun f : Velocity => f t y) rec.lift_eq.symm
    · intro i r hr
      exact w.spatial_derivative r hr i t ht
  have hWord (q : List (Fin 3)) (hq : q ∈ hierarchyAdmissibleWords (Fin 3) N) :
      ℓ ^ q.length * endpointClosedTimeNorm T (g q) ≤
        Cap * Csrc * (1 + (2 : ℝ) ^ N * Cost) ^ N := by
    obtain ⟨hqn, hqs⟩ := mem_hierarchyAdmissibleWords.mp hq
    have hBase : 1 ≤ 1 + (2 : ℝ) ^ N * Cost :=
      le_add_of_nonneg_right (mul_nonneg (pow_nonneg zero_le_two N) hCost)
    exact (hV q hqn hqs).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hBase hqn) (mul_nonneg hCap₀ hCsrc))
  have hBEq : (fun t : TimeSlab(T) => B t) = fun (t : TimeSlab(T)) x => F (t.val, toUnitTorus x) (v t x) :=
    funext fun t => funext (hB t t.property)
  rw [hBEq]
  exact hierarchyFiniteWordNorm_physicalMeanVelocity_le hT.le hℓ N
    (fun t x => F (t, toUnitTorus x)) v g hcSlice hvSlice hFbdd hg hEval hWord

/-- The two coefficient costs and the source cost in the finite mean estimate
fit one fixed polynomial power of the deformation scale. -/
theorem meanScalarBudget_le_power {D Ainv C K Fnorm Bnorm : ℝ} {a b s : ℕ}
    (hD : 1 ≤ D) (hA : 0 ≤ Ainv) (hK : 0 ≤ K) (hF : 0 ≤ Fnorm)
    (hAinv : Ainv ≤ C * D ^ a)
    (hBudget : Bnorm ≤ K * Ainv * (D ^ b / Real.sqrt ((D ^ s)⁻¹)) ^ 2 *
      (Fnorm / Real.sqrt ((D ^ s)⁻¹))) :
    Bnorm ≤ (K * C) * D ^ (a + 2 * b + 2 * s) * Fnorm := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hDs : 1 ≤ D ^ s := one_le_pow₀ hD
  have hCoefficient : (D ^ b / Real.sqrt ((D ^ s)⁻¹)) ^ 2 = (D ^ b) ^ 2 * D ^ s := by
    rw [div_pow, Real.sq_sqrt (inv_nonneg.mpr (pow_nonneg hD₀ _)), div_inv_eq_mul]
  have hSource : Fnorm / Real.sqrt ((D ^ s)⁻¹) ≤ Fnorm * D ^ s := by
    rw [div_eq_mul_inv, Real.sqrt_inv, inv_inv]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr hDs)) hF
  have hCoef₀ : 0 ≤ (D ^ b) ^ 2 * D ^ s := mul_nonneg (sq_nonneg _) (pow_nonneg hD₀ _)
  calc
    _ ≤ _ := hBudget
    _ = K * Ainv * ((D ^ b) ^ 2 * D ^ s) * (Fnorm / Real.sqrt ((D ^ s)⁻¹)) := by
      rw [hCoefficient]
    _ ≤ K * Ainv * ((D ^ b) ^ 2 * D ^ s) * (Fnorm * D ^ s) :=
      mul_le_mul_of_nonneg_left hSource (mul_nonneg (mul_nonneg hK hA) hCoef₀)
    _ ≤ K * (C * D ^ a) * ((D ^ b) ^ 2 * D ^ s) * (Fnorm * D ^ s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAinv hK) hCoef₀) (mul_nonneg hF (pow_nonneg hD₀ _))
    _ = _ := by
      rw [show a + 2 * b + 2 * s = a + b * 2 + s + s by omega, pow_add, pow_add, pow_add, pow_mul]
      ring

/-- A sufficiently small label radius absorbs the inverse estimate and the
ninth degree coefficient cost. -/
theorem meanScalarRadius_absorbs_inverse {D Ainv : ℝ} {a s : ℕ}
    (hD : 1 ≤ D) (hAinv : Ainv ≤ D ^ a) (hs : 2 * (a + 9) ≤ s) :
    Ainv * D ^ 9 * Real.sqrt ((D ^ s)⁻¹) ≤ 1 := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hDs : 0 < D ^ s := pow_pos (zero_lt_one.trans_le hD) _
  have hPower : (D ^ (a + 9)) ^ 2 ≤ D ^ s := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hD (by omega)
  suffices hz : D ^ (a + 9) * Real.sqrt ((D ^ s)⁻¹) ≤ 1 by
    rw [pow_add] at hz
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAinv (pow_nonneg hD₀ _))
      (Real.sqrt_nonneg _)).trans hz
  apply (sq_le_sq₀ (mul_nonneg (pow_nonneg hD₀ _) (Real.sqrt_nonneg _)) zero_le_one).1
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hDs.le), one_pow]
  exact (mul_le_mul_of_nonneg_right hPower (inv_nonneg.mpr hDs.le)).trans_eq
    (mul_inv_cancel₀ hDs.ne')

/-- The force jet values are bounded in both the supremum and half-Hölder
measurements at every finite label word. -/
theorem bddAbove_endpointLabelWord_of_smooth_periodic {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T ℓ : ℝ}
    (hT : 0 < T) (hℓ : 0 ≤ ℓ) {f : ℝ → Vec3 → E} (hf : ContDiffOn ℝ ∞ (Function.uncurry f)
      (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (f t))
    (q : List (Fin 3)) :
    let u := fun (t : Icc (0 : ℝ) T) => f t
    BddAbove (hierarchyJetValues False (hierarchyLabelDirection ℓ) q u) ∧
      BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) q u) := by
  intro u
  obtain ⟨C, hC⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT hf hper q.length
  obtain ⟨I, hI⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT hf hper (q.length+1)
  have htime : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hC₀ := (norm_nonneg _).trans (hC 0 htime 0)
  have hI₀ := (norm_nonneg _).trans (hI 0 htime 0)
  have hslice (t : Icc (0 : ℝ) T) : ContDiff ℝ ∞ (u t) :=
    hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨t.property, mem_univ x⟩)
  have hB := (hierarchyJetValues_true_label_bddAbove_csSup_le_of_iteratedFDeriv hℓ hC₀ hI₀
    hslice q (fun t => hC t t.property) (fun t => hI t t.property)).1
  refine ⟨hB.mono ?_, hB⟩
  intro r hr
  rcases hr with h | h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact h.elim

/-- The order-dependent factor in the physical mean estimate. Its scalar
arguments depend only on the uniform parent coefficient budgets. -/
def endpointPhysicalMeanWordConstant (C H : ℕ → ℝ) (N : ℕ) : ℝ :=
  let k : ℝ := (hierarchyAdmissibleWords (Fin 3) N).card
  let j := k * (2 : ℝ) ^ N
  let R := (1 + (2 : ℝ) ^ N * (2 * ∑ r ∈ Finset.range (N + 1), H r)) ^ N
  j * (2 * C N) * (k * R) * (Real.sqrt 2 * j * (8 * C N))

theorem endpointPhysicalMeanWordConstant_nonneg (C H : ℕ → ℝ)
    (hC : ∀ n, 0 ≤ C n) (hH : ∀ n, 0 ≤ H n) (N : ℕ) :
    0 ≤ endpointPhysicalMeanWordConstant C H N := by
  unfold endpointPhysicalMeanWordConstant
  have hsum : 0 ≤ ∑ r ∈ Finset.range (N + 1), H r := Finset.sum_nonneg (fun r _ => hH r)
  have hCN := hC N
  positivity

private theorem physicalMeanWordScalar_rearrange (j k r c R d f : ℝ) :
    j * (2 * (c * d) * (k * (R * (Real.sqrt 2 * (j * (2 * (c * d) * (4 * f)))) * r))) =
      (j * (2 * c) * (k * r) * (Real.sqrt 2 * j * (8 * c))) * R * d ^ 2 * f := by ring

set_option maxHeartbeats 4000000 in
/-- Absolute powers in the inverse and radius give the finite-order estimate
for the same recovered physical mean. The Hölder source costs one extra
spatial word in the supremum norm. -/
theorem norm_endpointPhysicalRecoveredMean_le_of_power_caps {T D L μ LK CK As Am : ℝ}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hD : 1 ≤ D) (p s N : ℕ) (hs : 2 * (p + 9) ≤ s)
    (C H : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (hH : ∀ n, 0 ≤ H n)
    (F M : ℝ × A → Coefficient) (force v B : Velocity) (rec : EndpointPhysicalMeanRecovery hT D L F M force v)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T))
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (hforcePer : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (force t))
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T))
    (hB : ∀ t ∈ TimeSlab(T), ∀ x, B t x = F (t, toUnitTorus x) (v t x))
    (hμ : 0 < μ) (hLK : 0 ≤ LK)
    (hLip : ∀ t ∈ TimeSlab(T), ∀ a b,
      ‖HalfHolder.eval a (rec.jets.kinetic.curve [] t) -
        HalfHolder.eval b (rec.jets.kinetic.curve [] t)‖ ≤ LK * dist a b)
    (hPos : ∀ t ∈ TimeSlab(T), ∀ a z,
      μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (rec.jets.kinetic.curve [] t) z, z⟫_ℝ)
    (hSup : ∀ t ∈ TimeSlab(T), ‖(rec.jets.kinetic.curve [] t).val.1‖ ≤ CK)
    (eS : ℝ → S ≃L[ℝ] S)
    (heS : ∀ t ∈ TimeSlab(T), ∀ z : S,
      eS t z = endpointStrongSpatialProjection ((rec.jets.kinetic.curve [] t).coefficientMul z.val))
    (hAs : ∀ t ∈ TimeSlab(T), ‖((eS t).symm : S →L[ℝ] S)‖ ≤ As)
    (eM : MixedFixed(T) ≃L[ℝ] MixedFixed(T))
    (heM : (eM : MixedFixed(T) →L[ℝ] MixedFixed(T)) = freezingCompression (endpointStrongMixedLeray T)
      (endpointMixedPathCoefficient hT.le (rec.jets.kineticMixed []) (rec.jets.vorticityMixed [])).coefficientMul
        (endpointStrongMixedLeray_idempotent hT))
    (hAm : ‖(eM.symm : MixedFixed(T) →L[ℝ] MixedFixed(T))‖ ≤ Am)
    (hCap : endpointPhysicalInverseBudget hT.le (rec.jets.kineticMixed []) (rec.jets.vorticityMixed []) As Am ≤ D ^ p) :
    let ℓ := (D ^ s)⁻¹
    let dir := hierarchyLabelDirection ℓ
    let Fv := fun (t : TimeSlab(T)) x => F (t.val, toUnitTorus x)
    let Fad := fun (t : TimeSlab(T)) x => (Fv t x).adjoint
    (∀ q ∈ hierarchyAdmissibleWords (Fin 3) N,
      BddAbove (hierarchyJetValues True dir q Fv) ∧ BddAbove (hierarchyJetValues True dir q Fad)) →
    hierarchyFiniteWordNorm True dir N Fv ≤ C N * D / Real.sqrt ℓ →
    hierarchyFiniteWordNorm True dir N Fad ≤ C N * D / Real.sqrt ℓ →
    (∀ q ∈ hierarchyAdmissibleWords (Fin 3) N, 1 ≤ q.length →
      ℓ ^ q.length * (endpointClosedTimeNorm T (rec.jets.kinetic.curve q) +
        endpointClosedTimeNorm T (rec.jets.vorticity.curve q)) ≤ H q.length * D ^ 9 * Real.sqrt ℓ) →
    hierarchyFiniteWordNorm False dir N (fun t : TimeSlab(T) => B t) ≤
      endpointPhysicalMeanWordConstant C H N * D ^ (p + 2 + 2 * s) *
        hierarchyFiniteWordNorm False dir (N + 1) (fun t : TimeSlab(T) => force t) := by
  intro ℓ dir Fv Fad hCoB hFv hFad hCoefficient
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hDpos _)
  have hℓ₁ : ℓ ≤ 1 := (inv_le_one₀ (pow_pos hDpos _)).mpr (one_le_pow₀ hD)
  let W : ℝ := (hierarchyAdmissibleWords (Fin 3) N).card
  let J := W * (2 : ℝ) ^ N
  let Ainv := D ^ p
  let Z := ∑ r ∈ Finset.range (N + 1), H r
  let R := (1 + (2 : ℝ) ^ N * (2 * Z)) ^ N
  let fN := hierarchyFiniteWordNorm False dir (N + 1) (fun t : TimeSlab(T) => force t)
  let d := D / Real.sqrt ℓ
  let f := fN / Real.sqrt ℓ
  let csrc := Real.sqrt 2 * (J * (2 * (C N * d) * (4 * f)))
  have hW : 0 ≤ W := Nat.cast_nonneg _
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hA : 0 ≤ Ainv := pow_nonneg hDpos.le _
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun q _ => hH q)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hd : 0 ≤ d := div_nonneg hDpos.le (Real.sqrt_nonneg _)
  have hc : 0 ≤ C N := hC N
  have hbForce (q : List (Fin 3)) := bddAbove_endpointLabelWord_of_smooth_periodic hT hℓ.le hforce hforcePer q
  have hf₀ : 0 ≤ fN := Finset.sum_nonneg (fun q _ => le_csSup (hbForce q).1 (Or.inl rfl))
  have hfn : 0 ≤ f := div_nonneg hf₀ (Real.sqrt_nonneg _)
  have hcs : 0 ≤ csrc := by dsimp only [csrc]; positivity
  have hForceN : hierarchyFiniteWordNorm True dir N (fun t : TimeSlab(T) => force t) ≤ 4 * f := by
    have h := hierarchyFiniteWordNorm_holder_le (f := fun t : TimeSlab(T) => force t) ℓ hℓ hℓ₁ N
      (fun (t : TimeSlab(T)) => contDiff_endpointMeanSlice hforce t.property)
      (fun q _ => (hbForce q).1)
    simpa only [f, fN, dir, mul_div_assoc] using h
  have hForceN₀ : 0 ≤ hierarchyFiniteWordNorm True dir N (fun t : TimeSlab(T) => force t) :=
    Finset.sum_nonneg (fun q _ => le_csSup (hbForce q).2 (Or.inl rfl))
  obtain ⟨pull, hPull, hPullEq, hLift⟩ := exists_endpointPhysicalPulledForceWords hT F M force v rec hF hforce hforcePer
  let Adj : Coefficient ≃ₗᵢ[ℝ] Coefficient := ContinuousLinearMap.adjoint
  have hAdj (t : ℝ) (ht : t ∈ TimeSlab(T)) :
      ContDiff ℝ ∞ (fun x => (F (t, toUnitTorus x)).adjoint) :=
    Adj.contDiff.comp (contDiff_endpointMeanSlice hF ht)
  have hFad' : hierarchyFiniteWordNorm True dir N Fad ≤ C N * d := by
    simpa only [d, mul_div_assoc] using hFad
  have hSource (q : List (Fin 3)) (hq : q ∈ hierarchyAdmissibleWords (Fin 3) N) :
      ℓ ^ q.length * endpointClosedTimeNorm T (rec.jets.source.curve q) ≤ csrc := by
    have hz := weighted_endpointIntegratedForce_le hT hℓ N
      (fun t x => (F (t, toUnitTorus x)).adjoint) force rec.jets.source.curve pull hAdj
      (fun t ht => contDiff_endpointMeanSlice hforce ht)
      (fun r hr => (hCoB r hr).2) (fun r _ => (hbForce r).2)
      (fun r _ => hPull r) (fun r _ => hPullEq r) (fun r _ => hLift r) q hq
    refine hz.trans ?_
    change T * Real.sqrt 2 * (J * (2 * hierarchyFiniteWordNorm True dir N Fad *
      hierarchyFiniteWordNorm True dir N (fun t : TimeSlab(T) => force t))) ≤ csrc
    have hProd := mul_le_mul (mul_le_mul_of_nonneg_left hFad' zero_le_two) hForceN
      hForceN₀ (by positivity : 0 ≤ 2 * (C N * d))
    calc
      _ ≤ (1 * Real.sqrt 2) * (J * (2 * (C N * d) * (4 * f))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hT₁ (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_left hProd hJ)
          (mul_nonneg hJ (mul_nonneg (mul_nonneg zero_le_two
            (Finset.sum_nonneg fun r hr => le_csSup (hCoB r hr).2 (Or.inl rfl))) hForceN₀))
          (by positivity)
      _ = _ := by simp only [one_mul, csrc]
  have hSmall : Ainv * D ^ 9 * Real.sqrt ℓ ≤ 1 :=
    meanScalarRadius_absorbs_inverse hD (a := p) (s := s) (le_rfl : Ainv ≤ D ^ p) hs
  have hCof (q : List (Fin 3)) (hq : q ∈ hierarchyAdmissibleWords (Fin 3) N) (hp : 1 ≤ q.length) :
      Ainv * (ℓ ^ q.length *
        endpointPhysicalCoefficientWordNorm T rec.jets.kinetic.curve rec.jets.vorticity.curve q) ≤ 2 * Z := by
    have hN := (mem_hierarchyAdmissibleWords.mp hq).1
    have hHz : H q.length ≤ Z :=
      Finset.single_le_sum (f := H) (fun r _ => hH r) (Finset.mem_range.mpr (by omega))
    exact (endpointPhysicalCoefficientWordNorm_threshold hT.le hT₁ hℓ.le hA (hH q.length)
      rec.jets.kinetic.curve rec.jets.vorticity.curve q (hCoefficient q hq hp) hSmall).trans
        (mul_le_mul_of_nonneg_left hHz zero_le_two)
  have hB0 := norm_endpointPhysicalRecoveredMean_le hT hℓ.le N F M force v B rec hF hv hB
    (fun q hq => (hCoB q hq).1) hμ hLK hLip hPos hSup eS heS hAs eM heM hAm hCap
    (mul_nonneg zero_le_two hZ) hcs hCof hSource
  let FN := hierarchyFiniteWordNorm True dir N Fv
  have hFN : 0 ≤ FN := Finset.sum_nonneg (fun q hq => le_csSup (hCoB q hq).1 (Or.inl rfl))
  have hv' : FN ≤ C N * d := by simpa only [d, mul_div_assoc] using hFv
  have hOuter :
      hierarchyFiniteWordNorm False dir N (fun t : TimeSlab(T) => B t) ≤
        endpointPhysicalMeanWordConstant C H N * Ainv * d ^ 2 * f := by
    change hierarchyFiniteWordNorm False dir N (fun t : TimeSlab(T) => B t) ≤ _ at hB0
    calc
      _ ≤ J * (2 * FN * (W * (Ainv * csrc * R))) := hB0
      _ ≤ J * (2 * (C N * d) * (W * (Ainv * csrc * R))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hv' zero_le_two)
          (mul_nonneg hW (mul_nonneg (mul_nonneg hA hcs) hR))) hJ
      _ = _ := by
        dsimp only [csrc, endpointPhysicalMeanWordConstant]
        exact physicalMeanWordScalar_rearrange J W R (C N) Ainv d f
  have hFinal := meanScalarBudget_le_power (a := p) (b := 1) (s := s) hD hA
    (endpointPhysicalMeanWordConstant_nonneg C H hC hH N) hf₀
    (C := 1) (by simp only [one_mul]; exact le_rfl : Ainv ≤ 1 * D ^ p)
    (by simpa only [pow_one, d, ℓ, f] using hOuter)
  simpa only [mul_one, Nat.mul_one, fN, dir] using hFinal


set_option maxHeartbeats 1000000 in
theorem EndpointSlabHalfHolderJets.mul_closedTimeNorm_le_liftCap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T ℓ : ℝ}
    (hT : 0 < T) (hℓ : 0 < ℓ) {f : ℝ × Vec3 → E}
    (jet : EndpointSlabHalfHolderJets T coordinateDirection f)
    (hf : ContDiffOn ℝ ∞ f (Icc 0 T ×ˢ (univ : Set Vec3)))
    (q : List (Fin 3))
    (hB : BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) q
      (fun (t : Icc (0 : ℝ) T) x => f (t,x)))) :
    ℓ ^ q.length * endpointClosedTimeNorm T (jet.curve q) ≤ Real.sqrt 2 *
      sSup (hierarchyJetValues True (hierarchyLabelDirection ℓ) q
        (fun (t : Icc (0 : ℝ) T) x => f (t,x))) := by
  let F (t : ℝ) (x : Vec3) := f (t,x)
  have hs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (F t) :=
    hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht,mem_univ x⟩)
  have hLift (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (jet.curve q t) = spatialDerivativeWord q (F t) x :=
    (jet.eval_lift q t ht x).trans (endpointSlabSpatialWord_eq_spatialDerivativeWord hT hf q t ht x)
  exact mul_endpointClosedTimeNorm_le_of_hierarchyLabelWord (f := F) hT.le hℓ q
    (jet.curve q) hs hB hLift


set_option maxHeartbeats 6500000 in
/-- The actual parent deformation and strain give one radius threshold and one
polynomial power for all recovered physical mean coefficients. The finite-order
constants are uniform over the time slab, the parent and the hierarchy depth. -/
theorem exists_endpointPhysicalRecoveredMean_parentBound (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ (p s₀ : ℕ) (C : ℕ → ℝ), (∀ n, 0 ≤ C n) ∧
      ∀ {T D L : ℝ} {U : Velocity} {X : ℝ → Velocity},
      ∀ (hT : 0 < T), T ≤ 1 → 2 ≤ D → 0 ≤ L → L ≤ D →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T) →
      (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t)) →
      (∀ t ∈ TimeSlab(T), ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ TimeSlab(T), ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ TimeSlab(T), ∀ x,
        ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
      ∀ (F M : ℝ × A → Coefficient) (force v B : Velocity),
      ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T) →
      ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => M (z.1, toUnitTorus z.2)) LiftSlab(T) →
      (∀ t ∈ TimeSlab(T), ∀ x, F (t, toUnitTorus x) = fderiv ℝ (X 0 t) x) →
      (∀ t ∈ TimeSlab(T), ∀ x, M (t, toUnitTorus x) = fderiv ℝ (U t) (X 0 t x)) →
      ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T) →
      (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (force t)) →
      ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T) →
      (∀ t ∈ TimeSlab(T), ∀ x, B t x = F (t, toUnitTorus x) (v t x)) →
      EndpointPhysicalMeanRecovery hT D L F M force v →
      ∀ s : ℕ, s₀ ≤ s → ∀ n : ℕ,
        let ℓ := (D ^ s)⁻¹
        hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n (fun t : TimeSlab(T) => B t) ≤
          C n * D ^ (p + 2 + 2 * s) *
            hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (n + 1)
              (fun t : TimeSlab(T) => force t) := by
  obtain ⟨J, hJ, hRaw⟩ := exists_parentMeanCoefficientJetBounds R hR
  obtain ⟨C, H, hC, hH, hWeighted⟩ := exists_parentMeanWeightedCoefficientBounds R hR
  let C₀ := 13 + J 0 + J 0 + 4 * J 1 + 4 * J 1
  have hC₀ : 1 ≤ C₀ := by dsimp only [C₀]; linarith only [hJ 0, hJ 1]
  obtain ⟨CI, _, hInverse⟩ := exists_endpointPhysicalInverseCaps 9 hC₀
  obtain ⟨p, hp⟩ := exists_endpointPower_absorb_prefactor CI (291 * 9)
  let H' (n : ℕ) := Real.sqrt 2 * H n
  have hH' (n : ℕ) : 0 ≤ H' n := mul_nonneg (Real.sqrt_nonneg 2) (hH n)
  refine ⟨p, 2 * (p + 9), endpointPhysicalMeanWordConstant C H',
    endpointPhysicalMeanWordConstant_nonneg C H' hC hH', ?_⟩
  intro T D L U X hT hT₁ hD hL hLD hX hU hUper hF₀ hG₀ hUjets
    F M force v B hF hM hFEq hMEq hforce hforcePer hv hB rec s hs n
  let ℓ := (D ^ s)⁻¹
  let dir := hierarchyLabelDirection ℓ
  have hD₁ : 1 ≤ D := (by norm_num : (1 : ℝ) ≤ 2).trans hD
  have hDpos : 0 < D := zero_lt_one.trans_le hD₁
  have hℓ : 0 < ℓ := inv_pos.mpr (pow_pos hDpos _)
  have hScale : ℓ * D ^ 6 ≤ 1 := by
    dsimp only [ℓ]
    rw [inv_mul_eq_div]
    exact (div_le_one (pow_pos hDpos _)).mpr (pow_le_pow_right₀ hD₁ (by omega))
  let K := rec.jets.kinetic.curve
  let Ω := rec.jets.vorticity.curve
  let k (t : ℝ) (x : Vec3) := kineticForm (F (t, toUnitTorus x))
  let o (t : ℝ) (x : Vec3) := vorticityForm (F (t, toUnitTorus x)) (M (t, toUnitTorus x))
  let Adj : Coefficient ≃ₗᵢ[ℝ] Coefficient := ContinuousLinearMap.adjoint
  have hFa : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (F (z.1, toUnitTorus z.2)).adjoint) LiftSlab(T) :=
    Adj.contDiff.comp_contDiffOn hF
  have hMa : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (M (z.1, toUnitTorus z.2)).adjoint) LiftSlab(T) :=
    Adj.contDiff.comp_contDiffOn hM
  have hkC : ContDiffOn ℝ ∞ (Function.uncurry k) LiftSlab(T) := hFa.clm_comp hF
  have hoC : ContDiffOn ℝ ∞ (Function.uncurry o) LiftSlab(T) :=
    hFa.clm_comp ((hMa.sub hM).clm_comp hF)
  have hraw (t : ℝ) (ht : t ∈ TimeSlab(T)) (m : ℕ) (x : Vec3) :
      ‖iteratedFDeriv ℝ m (k t) x‖ ≤ J m * D ^ (5 * m + 2) ∧
        ‖iteratedFDeriv ℝ m (o t) x‖ ≤ J m * D ^ (6 * m + 3) := by
    have h := hRaw hT hT₁ hD₁ hX hU hUper hF₀ hG₀ hUjets t ht
    have hKO := (h.2.2.2.2 m x).2.2
    simpa only [k, o, hFEq t ht, hMEq t ht] using hKO
  have hd₀ : 0 ≤ D := hDpos.le
  obtain ⟨hKB, hKL⟩ := endpointHalfHolderCaps_of_lift_gradient
    (mul_nonneg (hJ 0) (pow_nonneg hd₀ 2)) (mul_nonneg (hJ 1) (pow_nonneg hd₀ 7)) (K []) k
    (fun t ht x => rec.jets.kinetic.eval_lift [] t ht x)
    (fun t ht => (contDiff_endpointMeanSlice hkC ht).differentiable (by simp))
    (fun t ht x => by simpa only [norm_iteratedFDeriv_zero] using (hraw t ht 0 x).1)
    (fun t ht x => by simpa only [norm_iteratedFDeriv_one] using (hraw t ht 1 x).1)
  obtain ⟨hΩB, hΩL⟩ := endpointHalfHolderCaps_of_lift_gradient
    (mul_nonneg (hJ 0) (pow_nonneg hd₀ 3)) (mul_nonneg (hJ 1) (pow_nonneg hd₀ 9)) (Ω []) o
    (fun t ht x => rec.jets.vorticity.eval_lift [] t ht x)
    (fun t ht => (contDiff_endpointMeanSlice hoC ht).differentiable (by simp))
    (fun t ht x => by simpa only [norm_iteratedFDeriv_zero] using (hraw t ht 0 x).2)
    (fun t ht x => by simpa only [norm_iteratedFDeriv_one] using (hraw t ht 1 x).2)
  let μ := (D ^ 2)⁻¹
  let μmix := 1 / (2 * D ^ 2 * (1 + L) ^ 2)
  let LK := 2 * (J 1 * D ^ 7)
  let LΩ := 2 * (J 1 * D ^ 9)
  let CK := J 0 * D ^ 2 + LK
  let CΩ := J 0 * D ^ 3 + LΩ
  have hμ : 0 < μ := inv_pos.mpr (pow_pos hDpos 2)
  have hμmix : 0 < μmix := by dsimp only [μmix]; positivity
  have hLK : 0 ≤ LK := mul_nonneg zero_le_two (mul_nonneg (hJ 1) (pow_nonneg hd₀ 7))
  have hLΩ : 0 ≤ LΩ := mul_nonneg zero_le_two (mul_nonneg (hJ 1) (pow_nonneg hd₀ 9))
  have hCK : 0 ≤ CK := add_nonneg (mul_nonneg (hJ 0) (pow_nonneg hd₀ 2)) hLK
  have hCΩ : 0 ≤ CΩ := add_nonneg (mul_nonneg (hJ 0) (pow_nonneg hd₀ 3)) hLΩ
  have hCommon : 4 + μ⁻¹ + μmix⁻¹ + CK + CΩ + LK + LΩ ≤ C₀ * D ^ 9 := by
    simpa only [μ, μmix, CK, CΩ, LK, LΩ, C₀, mul_assoc] using
      endpointInverseCommonScale_le_power_nine hD₁ hL hLD (hJ 0) (hJ 0) (hJ 1) (hJ 1)
  obtain ⟨eS, eM, As, Am, heS, hAs, heM, hAm, hCap⟩ :=
    hInverse (D := D) (μ := μ) (μmix := μmix) (CK := CK) (CΩ := CΩ) (LK := LK) (LΩ := LΩ)
      hT hT₁ hD₁ (rec.jets.kineticMixed []) (rec.jets.vorticityMixed []) (K []) (Ω [])
      (rec.jets.kinetic.smooth []).continuousOn (rec.jets.vorticity.smooth []).continuousOn
      (rec.jets.kinetic_action []) (rec.jets.vorticity_action [])
      hCK hCΩ hLK hLΩ hKB hΩB hKL hΩL hμ hμmix rec.kinetic_coercive rec.mixed_coercive hCommon
  let coframe (t : TimeSlab(T)) (x : Vec3) := F (t.val, toUnitTorus x)
  let adj (t : TimeSlab(T)) (x : Vec3) := (coframe t x).adjoint
  have hWeight := hWeighted hT hT₁ hD₁ hℓ hScale hX hU hUper hF₀ hG₀ hUjets
  have hFM : coframe = fun (t : TimeSlab(T)) x => fderiv ℝ (X 0 t.val) x :=
    funext fun t => funext (hFEq t t.property)
  have hAM : adj = fun (t : TimeSlab(T)) x => (fderiv ℝ (X 0 t.val) x).adjoint := by
    funext t x
    exact congrArg (fun Z : Coefficient => Z.adjoint) (hFEq t t.property x)
  have hKM : (fun t : TimeSlab(T) => k t) =
      fun (t : TimeSlab(T)) x => kineticForm (fderiv ℝ (X 0 t.val) x) := by
    funext t x
    dsimp only [k]
    rw [hFEq t t.property]
  have hOM : (fun t : TimeSlab(T) => o t) =
      fun (t : TimeSlab(T)) x => vorticityForm (fderiv ℝ (X 0 t.val) x) (fderiv ℝ (U t.val) (X 0 t.val x)) := by
    funext t x
    dsimp only [o]
    rw [hFEq t t.property, hMEq t t.property]
  have hFbdd (q : List (Fin 3)) :
      BddAbove (hierarchyJetValues True dir q coframe) := by
    rw [hFM]
    exact (hWeight.1 q).1
  have hAbdd (q : List (Fin 3)) :
      BddAbove (hierarchyJetValues True dir q adj) := by
    rw [hAM]
    exact (hWeight.1 q).2.1
  have hFword : hierarchyFiniteWordNorm True dir n coframe ≤ C n * D / Real.sqrt ℓ := by
    rw [hFM]
    exact (hWeight.2.1 n).1
  have hAword : hierarchyFiniteWordNorm True dir n adj ≤ C n * D / Real.sqrt ℓ := by
    rw [hAM]
    exact (hWeight.2.1 n).2
  have hCoeff (q : List (Fin 3)) (hq : 1 ≤ q.length) :
      ℓ ^ q.length * (endpointClosedTimeNorm T (K q) + endpointClosedTimeNorm T (Ω q)) ≤
        H' q.length * D ^ 9 * Real.sqrt ℓ := by
    have hkB : BddAbove (hierarchyJetValues True dir q (fun t : TimeSlab(T) => k t)) := by
      rw [hKM]
      exact (hWeight.1 q).2.2.1
    have hoB : BddAbove (hierarchyJetValues True dir q (fun t : TimeSlab(T) => o t)) := by
      rw [hOM]
      exact (hWeight.1 q).2.2.2
    have hkW := rec.jets.kinetic.mul_closedTimeNorm_le_liftCap hT hℓ hkC q hkB
    have hoW := rec.jets.vorticity.mul_closedTimeNorm_le_liftCap hT hℓ hoC q hoB
    have hKO : sSup (hierarchyJetValues True dir q (fun t : TimeSlab(T) => k t)) +
        sSup (hierarchyJetValues True dir q (fun t : TimeSlab(T) => o t)) ≤
        H q.length * D ^ 9 * Real.sqrt ℓ := by
      rw [hKM, hOM]
      exact (hWeight.2.2 q) (by omega)
    rw [mul_add]
    calc
      _ ≤ Real.sqrt 2 *
          (sSup (hierarchyJetValues True dir q (fun t : TimeSlab(T) => k t)) +
            sSup (hierarchyJetValues True dir q (fun t : TimeSlab(T) => o t))) := by
        rw [mul_add]
        exact add_le_add hkW hoW
      _ ≤ Real.sqrt 2 * (H q.length * D ^ 9 * Real.sqrt ℓ) :=
        mul_le_mul_of_nonneg_left hKO (Real.sqrt_nonneg _)
      _ = _ := by dsimp only [H']; ac_rfl
  exact norm_endpointPhysicalRecoveredMean_le_of_power_caps hT hT₁ hD₁ p s n hs C H' hC hH'
    F M force v B rec hF hforce hforcePer hv hB hμ hLK hKL rec.kinetic_coercive
    (fun t ht => (norm_fst_le (K [] t).val).trans (hKB t ht)) eS heS hAs eM heM hAm
    (hCap.trans (hp D hD)) (fun q _ => ⟨hFbdd q, hAbdd q⟩) hFword hAword
    (fun q _ hq => hCoeff q hq)

set_option maxHeartbeats 2500000 in
/-- The forced mean solver returns one smooth physical mean and its normalized
pressure together with the uniform all-orders estimate for that same mean. -/
theorem exists_endpointPhysicalForcedMean_withUniformEstimate (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ (p s₀ : ℕ) (C : ℕ → ℝ), (∀ n, 0 ≤ C n) ∧
      ∀ {T D L : ℝ} {U : Velocity} {X : ℝ → Velocity},
      0 < T → T ≤ 1 → 2 ≤ D → 0 ≤ L → L ≤ D →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T) →
      (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t)) →
      (∀ t ∈ TimeSlab(T), ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ TimeSlab(T), ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ TimeSlab(T), ∀ x,
        ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
      ∀ (F G M Mt : ℝ × A → Coefficient) (force : Velocity),
      ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T) →
      ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => M (z.1, toUnitTorus z.2)) LiftSlab(T) →
      (∀ t ∈ TimeSlab(T), ∀ x, F (t, toUnitTorus x) = fderiv ℝ (X 0 t) x) →
      (∀ t ∈ TimeSlab(T), ∀ x, M (t, toUnitTorus x) = fderiv ℝ (U t) (X 0 t x)) →
      ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T) →
      (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (force t)) →
      (∀ (a : A) t, t ∈ TimeSlab(T) →
        HasDerivWithinAt (fun r => F (r, a)) ((M (t, a)).comp (F (t, a))) TimeSlab(T) t) →
      (∀ (a : A) t, t ∈ TimeSlab(T) →
        HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) TimeSlab(T) t) →
      (∀ a, ContinuousOn (fun r => Mt (r, a)) TimeSlab(T)) →
      (∀ (a : A) t, t ∈ TimeSlab(T) → (G (t, a)).comp (F (t, a)) = ContinuousLinearMap.id ℝ Vec3) →
      (∀ (a : A) t, t ∈ TimeSlab(T) → (F (t, a)).comp (G (t, a)) = ContinuousLinearMap.id ℝ Vec3) →
      (∀ (a : A) t, t ∈ TimeSlab(T) → ‖G (t, a)‖ ≤ D) →
      (∀ (a : A) t, t ∈ TimeSlab(T) → ‖M (t, a)‖ ≤ L) →
      (∀ (a : A) t, t ∈ TimeSlab(T) → ∀ x : Vec3,
        ⟪endpointHessian (M (t, a)) (Mt (t, a)) x, x⟫_ℝ ≤ ‖x‖ ^ 2) →
      ∃ (v Z B : Velocity) (q : Pressure),
      ContDiffOn ℝ ∞ (Function.uncurry v) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry Z) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry B) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry q) LiftSlab(T) ∧
      (∀ t ∈ TimeSlab(T), SpatiallyPeriodic (v t) ∧ SpatiallyPeriodic (Z t) ∧
        SpatiallyPeriodic (B t) ∧ SpatiallyPeriodic (q t) ∧ (∫ x in centeredCell, q t x) = 0) ∧
      Z 0 = 0 ∧ Z T = 0 ∧
      (∀ t ∈ TimeSlab(T), ∀ x, B t x = F (t, toUnitTorus x) (v t x) ∧
        HasDerivWithinAt (fun r => Z r x) (v t x) TimeSlab(T) t ∧
        divergence (v t) x = 0 ∧
        derivWithin (fun r => B r x) TimeSlab(T) t + M (t, toUnitTorus x) (B t x) +
          (G (t, toUnitTorus x)).adjoint (gradient (q t) x) = force t x) ∧
      (∀ s : ℕ, s₀ ≤ s → ∀ n : ℕ,
        let ℓ := (D ^ s)⁻¹
        hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n (fun t : TimeSlab(T) => B t) ≤
          C n * D ^ (p + 2 + 2 * s) *
            hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (n + 1)
              (fun t : TimeSlab(T) => force t)) := by
  obtain ⟨p, s₀, C, hC, hEstimate⟩ := exists_endpointPhysicalRecoveredMean_parentBound R hR
  refine ⟨p, s₀, C, hC, ?_⟩
  intro T D L U X hT hT₁ hD hL hLD hX hU hUper hF₀ hG₀ hUjets F G M Mt force hFc hMc hFEq hMEq
    hforce hforcePer hF hM hMt hGF hFG hGbound hMbound hupper
  have hD₁ : 1 ≤ D := (by norm_num : (1 : ℝ) ≤ 2).trans hD
  obtain ⟨v, Z, B, q, hv, hZ, hB, hq, hPerMean, hStart, hFinish, hMom, ⟨rec⟩⟩ :=
    exists_endpointPhysicalForcedMean_withRecovery hT hT₁ hD₁ hL F G M Mt force hFc hMc hforce
      hforcePer hF hM hMt hGF hFG hGbound hMbound hupper
  exact ⟨v, Z, B, q, hv, hZ, hB, hq, hPerMean, hStart, hFinish, hMom,
    hEstimate hT hT₁ hD hL hLD hX hU hUper hF₀ hG₀ hUjets
      F M force v B hFc hMc hFEq hMEq hforce hforcePer hv (fun t ht x => (hMom t ht x).1) rec⟩

end

end TorusEuler
