import TorusEuler.Paper.Proofs.S678a.Library.CutoffChild
import TorusEuler.TruncatedChildInductiveStage

/-! # Scheduled bounds of the cutoff child (package S678a)

Own glue of row 7.1 (items 4-6 of the proof, sections/08b_induction.tex:376-381, :415-421, :463-470).

Copies of the library lemmas on `TruncatedChildStage` (TruncatedChildStage.lean:671-812) for the
structure `CutoffChild` and with the residual and pressure bounds of the cutoff
(`CutoffBounds.residual`, `.pressure`, which are content of Proposition 5.11) taken as the
hypotheses `hRes`, `hPress57` (the pressure increment (5.57), replacing the bound on `D²(p - Π)` and the Hessian of `Π`) in their final shape `C·next^(-7/2) + next^(-5)`. The bound `hErr`
and the tail bounds come from Lemma B.1 (B.2) and the size bound (5.47). Also the copy of
`InductiveEulerStage.ofTruncatedChildStage` (TruncatedChildInductiveStage.lean:16). -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

local notation "Labels" => UnitAddTorus (Fin 3)

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler

noncomputable section

/-- The slice form of the truncation error in (5.56) (`TruncatedChildStage.truncationError`). -/
def truncErr (Λ : ℝ) (V : Velocity) (P : ℕ) (t : ℝ) : ℝ :=
  Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P (V t)) ^ 2

/-- A function jointly smooth on a closed slab is smooth in the space variable at every fixed time of the slab. -/
theorem contDiff_slice' {T t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- The Hessian is additive: `D²p = D²(p - q) + D²q` for smooth `p, q` (the splitting of the child
pressure `p = (p - p_U) + p_U` used with (5.57) of Proposition 5.11). -/
theorem hessian_split {p q : Vec3 → ℝ} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) (x : Vec3) :
    fderiv ℝ (gradient p) x = fderiv ℝ (gradient (p - q)) x + fderiv ℝ (gradient q) x := by
  have hsm (f : Vec3 → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (gradient f) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (m := ∞) (by simp))
  have hd : ContDiff ℝ ∞ (p - q) := hp.sub hq
  have hpq : p = fun y => (p - q) y + q y := by funext y; simp
  have hgrad : gradient (fun y => (p - q) y + q y) =
      fun y => gradient (p - q) y + gradient q y := by
    funext y
    unfold gradient
    rw [fderiv_fun_add (hd.differentiable (by simp)).differentiableAt
      (hq.differentiable (by simp)).differentiableAt, map_add]
  conv_lhs => rw [hpq, hgrad]
  exact fderiv_fun_add ((hsm _ hd).differentiable (by simp)).differentiableAt
    ((hsm _ hq).differentiable (by simp)).differentiableAt

/-- Copy of `TruncatedChildStage.truncationError_le_next` (TruncatedChildStage.lean:671); the
child stage is not needed. -/
theorem truncErr_le_next {μ K : ℝ} {b q qNext : ℕ} {V : Velocity}
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hK : K ≤ μ) (t : ℝ)
    (hV : SpatialHolderHalf (6 * frequencyExponent b qNext) (V t))
    (hSize : 1 + spatialHolderHalfNorm (6 * frequencyExponent b qNext) (V t) ≤
      3 * (μ ^ frequencyExponent b q) ^ (2 * (6 * frequencyExponent b qNext + 1))) :
    K * truncErr ((μ ^ frequencyExponent b q) ^ 5) V (6 * frequencyExponent b qNext) t ≤
      ((μ ^ frequencyExponent b q) ^ frequencyExponent b qNext) ^ (-5 : ℝ) := by
  have hN : 0 ≤ spatialHolderHalfNorm (6 * frequencyExponent b qNext) (V t) :=
    (norm_nonneg _).trans (norm_iteratedFDeriv_le_spatialHolderHalfNorm hV (Nat.zero_le _) 0)
  have hε : 0 ≤ truncErr ((μ ^ frequencyExponent b q) ^ 5) V (6 * frequencyExponent b qNext) t := by
    unfold truncErr
    positivity
  exact (mul_le_mul_of_nonneg_right hK hε).trans
    (frequencySchedule_truncation_error_budget hμ hb hN hSize)

/-- Copy of `TruncatedChildStage.scheduled_increment` (TruncatedChildStage.lean:724) with the tail
bounds of (B.2) as the hypothesis `hTails`. -/
theorem scheduled_increment' {T : ℝ} {ψ : Vec3 → ℝ} {V : Velocity} {μ Cmean K : ℝ}
    {b q qNext P : ℕ}
    (s : CutoffChild T ((μ ^ frequencyExponent b q) ^ 5) ψ V)
    (hTails : ∀ m ≤ P, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (s.velocity t - V t) ∧
      spatialHolderHalfNorm m (s.velocity t - V t) ≤
        K * ((μ ^ frequencyExponent b q) ^ 5) ^ ((m : ℤ) - P) * spatialHolderHalfNorm P (V t))
    {parent osc mean : Velocity} (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hOrder : q ≤ qNext)
    (hDepth : q ≤ P) (hCmean : Cmean ≤ μ) (hK : 0 ≤ K)
    (hV : ∀ t ∈ Icc 0 T, SpatialHolderHalf P (V t))
    (hSplit : ∀ t ∈ Icc 0 T, V t = parent t + osc t + mean t)
    (hMean : ∀ m ≤ q, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (mean t) ∧
      spatialHolderHalfNorm m (mean t) ≤ Cmean * (μ ^ 9) ^ (b * (m + 2)) *
        (μ ^ frequencyExponent b q) ^ (-5 / 2 : ℝ))
    (hErr : ∀ t ∈ Icc 0 T, K * truncErr ((μ ^ frequencyExponent b q) ^ 5) V P t ≤
      ((μ ^ frequencyExponent b q) ^ frequencyExponent b qNext) ^ (-5 : ℝ)) :
    ∀ m ≤ q, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (s.velocity t - parent t - osc t) ∧
      spatialHolderHalfNorm m (s.velocity t - parent t - osc t) ≤ (μ ^ frequencyExponent b q)⁻¹ := by
  intro m hm t ht
  let tail := s.velocity t - V t
  have hTail := hTails m (hm.trans hDepth) t ht
  have hSize : 0 ≤ spatialHolderHalfNorm P (V t) := (norm_nonneg _).trans
    (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hV t ht) (Nat.zero_le _) 0)
  have hFreq : 1 ≤ μ ^ frequencyExponent b q := one_le_pow₀ (by linarith)
  have hTailRate := induction_child_cutoffTail_budget (μ := K) hFreq hK hSize le_rfl
    hTail.2 (hErr t ht)
  exact frequencySchedule_child_velocity_increment hμ hb hm hOrder hCmean
    (show s.velocity t = V t + tail by dsimp [tail]; abel) (hSplit t ht)
    (hMean m hm t ht).1 hTail.1 (hMean m hm t ht).2 hTailRate

/-- Copy of `TruncatedChildStage.scheduled_T2_T3` (TruncatedChildStage.lean:752): T2 and T3 for the
cutoff child and its Poisson pressure. The residual and the pressure Hessian of the cutoff are
bounded by `hRes`, `hPress57` (the bounds of Proposition 5.11 at the scheduled size), instead of
`CutoffBounds.residual`, `.pressure` with the bounds on `R_V` and `truncationError`. -/
theorem scheduled_T2_T3' {T : ℝ} {ψ : Vec3 → ℝ} {V : Velocity}
    {freq : ℕ → ℝ} {Cstep C Sparent : ℝ} {b q qNext j : ℕ}
    (s : CutoffChild T (((freq j) ^ frequencyExponent b q) ^ 5) ψ V)
    {parent osc : Velocity} {parentPressure : Pressure} {Y : ℝ → Velocity}
    (hμ : 2 ≤ freq j) (hb : 1 ≤ b) (hC : 0 ≤ C) (hS : T ≤ Sparent)
    (hCstep : Cstep ≤ ((freq j) ^ frequencyExponent b q) ^ (1 / 32 : ℝ))
    (hlarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ ((freq j) ^ frequencyExponent b q) ^ frequencyExponent b qNext)
    (hFlow : ChildFlow.DeformationOn s.velocity Y T
      (Cstep * ((freq j) ^ frequencyExponent b q) ^ (1 / 4 : ℝ)))
    (hParent : ∀ t ∈ Icc 0 T, ∀ x, ‖parent t x‖ ≤ freq j)
    (hOsc : ∀ t ∈ Icc 0 T, ∀ x,
      ‖osc t x‖ ≤ Cstep * ((freq j) ^ frequencyExponent b q) ^ (-5 / 4 : ℝ))
    (hInc : ∀ t ∈ Icc 0 T, SpatialHolderHalf 0 (s.velocity t - parent t - osc t) ∧
      spatialHolderHalfNorm 0 (s.velocity t - parent t - osc t) ≤ ((freq j) ^ frequencyExponent b q)⁻¹)
    (hRes : let next := ((freq j) ^ frequencyExponent b q) ^ frequencyExponent b qNext
      ∀ t ∈ Icc 0 T, SpatialHolderHalf 1 (s.residual t) ∧ spatialHolderHalfNorm 1 (s.residual t) ≤
        C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ))
    (hParentSmooth : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (parentPressure t))
    (hParentPressure : ∀ t ∈ Icc 0 Sparent, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (parentPressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range j, (freq i)⁻¹) * ‖v‖ ^ 2)
    (hPress57 : let next := ((freq j) ^ frequencyExponent b q) ^ frequencyExponent b qNext
      ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
        ⟪v, fderiv ℝ (gradient (s.pressure t - parentPressure t)) x v⟫_ℝ ≤
          (Cstep * ((freq j) ^ frequencyExponent b q) ^ (-1 / 4 : ℝ) +
            (C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ))) * ‖v‖ ^ 2) :
    let childFrequency := (freq j) ^ frequencyExponent b q
    let next := childFrequency ^ frequencyExponent b qNext
    (∀ t ∈ Icc 0 T, ‖s.torusVelocity t‖ ≤ childFrequency) ∧
      ChildFlow.DeformationOn s.velocity Y T childFrequency ∧
      (∀ t ∈ Icc 0 T, ∀ x, ‖s.residual t x‖ ≤ next ^ (-3 : ℝ)) ∧
      ∀ t ∈ Icc 0 T, ∀ x v : Vec3, ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range (j + 1), (freq i)⁻¹) * ‖v‖ ^ 2 := by
  let childFrequency := (freq j) ^ frequencyExponent b q
  let next := childFrequency ^ frequencyExponent b qNext
  have hchildFrequency : 1 ≤ childFrequency := one_le_pow₀ (by linarith)
  have hRpoint (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      ‖s.residual t x‖ ≤ C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ) := by
    have h := norm_iteratedFDeriv_le_spatialHolderHalfNorm (hRes t ht).1 (Nat.zero_le 1) x
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (hRes t ht).2
  obtain ⟨hU, hY, hR⟩ := frequencySchedule_child_T2 (qNext := qNext) hμ hb hC hCstep
    hlarge hFlow hParent hOsc hInc hRpoint
  refine ⟨fun t ht => (ContinuousMap.norm_le _ (zero_le_one.trans hchildFrequency)).mpr fun z => ?_,
    hY, hR, ?_⟩
  · obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    exact hU t ht x
  · refine frequencySchedule_child_T3 (qNext := qNext) hμ hb hC hS hCstep hlarge hParentPressure ?_
    dsimp only
    intro t ht x v
    have hdec := hessian_split (contDiff_slice' s.smooth_pressure ht) (hParentSmooth t ht) x
    have hin : ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ =
        ⟪v, fderiv ℝ (gradient (s.pressure t - parentPressure t)) x v⟫_ℝ +
          ⟪v, fderiv ℝ (gradient (parentPressure t)) x v⟫_ℝ := by
      rw [hdec, add_apply, inner_add_right]
    have h57 := hPress57 t ht x v
    linarith only [hin, h57]

/-- Copy of `InductiveEulerStage.ofTruncatedChildStage` (TruncatedChildInductiveStage.lean:16)
for `CutoffChild`: the cutoff child with the two scheduled bounds is the next stage. -/
def InductiveEulerStage.ofCutoffChild {P : InductiveEulerParameters} {n : ℕ} {activation T Λ : ℝ}
    {ψ : Vec3 → ℝ} {V : Velocity} {Y : ℝ → Velocity}
    (s : CutoffChild T Λ ψ V)
    (hSlab : T = P.slab n activation) (hRadius : Λ = P.frequency n ^ 5)
    (hU : ∀ t ∈ Icc 0 T, ‖s.torusVelocity t‖ ≤ P.frequency n)
    (hFlow : ChildFlow.DeformationOn s.velocity Y T (P.frequency n))
    (hR : ∀ t ∈ Icc 0 T, ∀ x, ‖s.residual t x‖ ≤ P.frequency (n + 1) ^ (-3 : ℝ))
    (hP : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range n, (P.frequency i)⁻¹) * ‖v‖ ^ 2) :
    InductiveEulerStage P n activation := by
  subst T
  subst Λ
  refine {
    torusVelocity := s.torusVelocity
    pressure := s.pressure
    flow := Y
    smooth_velocity := s.smooth_velocity
    odd_velocity := s.odd_velocity
    divergence_free := s.divergence_free
    velocity_band := s.velocity_band
    velocity_bound := hU
    smooth_pressure := s.smooth_pressure
    periodic_pressure := s.periodic_pressure
    mean_zero_pressure := s.mean_zero_pressure
    poisson := s.poisson
    projected_eq := s.projected_eq
    residual_bound := ?_
    deformation := hFlow
    pressure_hessian := hP }
  intro t ht x
  have hpow : P.frequency (n + 1) ^ (-3 : ℝ) = ((P.frequency (n + 1))⁻¹)^3 := by
    calc
      _ = P.frequency (n + 1) ^ (-(3 : ℕ) : ℤ) := Real.rpow_neg_natCast _ 3
      _ = _ := by rw [zpow_neg, zpow_natCast, inv_pow]
  exact (hR t ht x).trans_eq hpow

/-- The velocity of the stage built from a cutoff child is the velocity of the child. -/
theorem InductiveEulerStage.ofCutoffChild_velocity {P : InductiveEulerParameters} {n : ℕ}
    {activation T Λ : ℝ} {ψ : Vec3 → ℝ} {V : Velocity} {Y : ℝ → Velocity}
    (s : CutoffChild T Λ ψ V)
    (hSlab : T = P.slab n activation) (hRadius : Λ = P.frequency n ^ 5)
    (hU : ∀ t ∈ Icc 0 T, ‖s.torusVelocity t‖ ≤ P.frequency n)
    (hFlow : ChildFlow.DeformationOn s.velocity Y T (P.frequency n))
    (hR : ∀ t ∈ Icc 0 T, ∀ x, ‖s.residual t x‖ ≤ P.frequency (n + 1) ^ (-3 : ℝ))
    (hP : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range n, (P.frequency i)⁻¹) * ‖v‖ ^ 2) :
    (InductiveEulerStage.ofCutoffChild s hSlab hRadius hU hFlow hR hP).velocity = s.velocity := by
  subst T
  subst Λ
  rfl

/-- The pressure of the stage built from a cutoff child is the pressure of the child. -/
theorem InductiveEulerStage.ofCutoffChild_pressure {P : InductiveEulerParameters} {n : ℕ}
    {activation T Λ : ℝ} {ψ : Vec3 → ℝ} {V : Velocity} {Y : ℝ → Velocity}
    (s : CutoffChild T Λ ψ V)
    (hSlab : T = P.slab n activation) (hRadius : Λ = P.frequency n ^ 5)
    (hU : ∀ t ∈ Icc 0 T, ‖s.torusVelocity t‖ ≤ P.frequency n)
    (hFlow : ChildFlow.DeformationOn s.velocity Y T (P.frequency n))
    (hR : ∀ t ∈ Icc 0 T, ∀ x, ‖s.residual t x‖ ≤ P.frequency (n + 1) ^ (-3 : ℝ))
    (hP : ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (s.pressure t)) x v⟫_ℝ ≤
        (∑ i ∈ Finset.range n, (P.frequency i)⁻¹) * ‖v‖ ^ 2) :
    (InductiveEulerStage.ofCutoffChild s hSlab hRadius hU hFlow hR hP).pressure = s.pressure := by
  subst T
  subst Λ
  rfl

end

end TorusEuler.Paper.Lib.S678a
