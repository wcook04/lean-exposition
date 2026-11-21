import TorusEuler.HierarchyParentGeometry
import TorusEuler.InductiveStageConstruction
import TorusEuler.TruncatedChildStage

/-! The inductive parent on the endpoint slab of its next wave. -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.InductiveEulerStage

noncomputable section

variable {P : InductiveEulerParameters} {n : ℕ} {activation T : ℝ}
local notation "Time(" T ")" => Icc (0 : ℝ) T
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)
local notation "Labels" => UnitAddTorus (Fin 3)

/-- The same inductive stage on the smaller endpoint slab, with its actual
parent coefficients and pulled-back residual. -/
structure OnSlab (s : InductiveEulerStage P n activation) (hT : 0 < T) (k : Vec3) where
  subset : Time(T) ⊆ Icc 0 (P.slab n activation)
  geometry : HierarchyTwistedProfile.ParentGeometry hT s.velocity s.flow k
  inverse_bound : geometry.mean.inverse_bound = P.frequency n
  strain_bound : geometry.mean.strain_bound = P.frequency n ^ 9
  momentum_same : ∀ t ∈ Time(T), momentumResidual Time(T) s.velocity s.pressure t = s.residual t
  projected_same : ∀ t ∈ Time(T), closedSlabLerayMomentum 0 T s.velocity t = s.residual t
  residualTorus : ℝ → C(Labels, Vec3)
  residualTorus_value : ∀ t ∈ Time(T), ∀ x, residualTorus t (toUnitTorus x) = s.residual t x
  residualTorus_band : ∀ t ∈ Time(T), RealTorusFourierBand (4 * P.frequency n ^ 5) (residualTorus t)
  residualTorus_bound : ∀ t ∈ Time(T), ‖residualTorus t‖ ≤ P.frequency (n + 1) ^ (-3 : ℝ)
  residual_derivative : ∀ t ∈ Time(T), ∀ x, ‖fderiv ℝ (s.residual t) x‖ ≤ 1 / 2
  residualProfile : HierarchyTwistedProfile T k Vec3
  residualProfile_mean :
    (HierarchyTwistedProfile.twistedHierarchyOperators hT geometry.inverse geometry.strain geometry.covector).average
      residualProfile = residualProfile
  residualProfile_value : ∀ x ∈ hierarchyProfileSlab T,
    residualProfile.val.val.val x = s.residual x.1 (s.flow 0 x.1 x.2.1)
  residualProfile_odd : HierarchyProfileReflectionParity (-1) residualProfile.val.val.val

namespace OnSlab

variable {s : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}

theorem deformationOn (d : s.OnSlab hT k) :
    ChildFlow.DeformationOn s.velocity s.flow T (P.frequency n) :=
  ⟨s.deformation.flow.mono d.subset,
    fun r hr t ht => s.deformation.lattice r (d.subset hr) t (d.subset ht),
    fun t ht => s.deformation.bounds t (d.subset ht)⟩

theorem smooth_velocity (d : s.OnSlab hT k) :
    ContDiffOn ℝ ∞ (Function.uncurry s.velocity) Slab(T) :=
  s.smooth_velocity.mono (prod_mono_left d.subset)

theorem smooth_pressure (d : s.OnSlab hT k) :
    ContDiffOn ℝ ∞ (Function.uncurry s.pressure) Slab(T) :=
  s.smooth_pressure.mono (prod_mono_left d.subset)

theorem smooth_residual (d : s.OnSlab hT k) : ContDiffOn ℝ ∞ (Function.uncurry s.residual) Slab(T) := by
  exact (contDiffOn_closedSlab_momentumResidual hT d.smooth_velocity d.smooth_pressure).congr
    fun x hx => (congrFun (d.momentum_same x.1 hx.1) x.2).symm

end OnSlab

private theorem stage_frequency_lower (P : InductiveEulerParameters) (h₀ : 4 ≤ P.frequency 0) :
    (∀ j, P.frequency 0 ≤ P.frequency j) ∧
    (∀ j, 2 * P.frequency j ≤ P.frequency (j + 1)) ∧
    ∀ j, P.frequency j ^ 2 ≤ P.frequency (j + 1) := by
  have hexp (j : ℕ) : 2 ≤ frequencyExponent P.exponentParameter (P.order (j + 1)) := by
    unfold frequencyExponent
    calc
      2 ≤ 320 * 1 * 1 := by decide
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left 320 P.exponentParameter_ge) (by omega)
  have hnext {j : ℕ} (hj : 4 ≤ P.frequency j) : P.frequency j ^ 2 ≤ P.frequency (j + 1) := by
    rw [P.frequency_step]
    exact pow_le_pow_right₀ (by linarith) (hexp j)
  have hdouble {j : ℕ} (hj : 4 ≤ P.frequency j) : 2 * P.frequency j ≤ P.frequency j ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ P.frequency j by linarith) (show 0 ≤ P.frequency j - 2 by linarith)]
  have hle (j : ℕ) : P.frequency 0 ≤ P.frequency j := by
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      have hj := h₀.trans ih
      have hbase : P.frequency j ≤ 2 * P.frequency j := by linarith
      exact ih.trans (hbase.trans ((hdouble hj).trans (hnext hj)))
  exact ⟨hle, fun j => (hdouble (h₀.trans (hle j))).trans (hnext (h₀.trans (hle j))),
    fun j => hnext (h₀.trans (hle j))⟩

private theorem scheduled_residual_derivative_budget {f g K : ℝ}
    (hf : 1 ≤ f) (hK : 0 ≤ K) (hfreq : 2 * K ≤ f) (hg : f ^ 2 ≤ g) :
    K * f ^ 5 * g ^ (-3 : ℝ) ≤ 1 / 2 := by
  have hfpos : 0 < f := zero_lt_one.trans_le hf
  have hgpos : 0 < g := (sq_pos_of_pos hfpos).trans_le hg
  have hpow : f ^ 6 ≤ g ^ 3 := by
    rw [show (f ^ (6 : ℕ)) = (f ^ (2 : ℕ)) ^ (3 : ℕ) by ring]
    exact pow_le_pow_left₀ (sq_nonneg f) hg _
  rw [Real.rpow_neg hgpos.le, Real.rpow_ofNat]
  calc
    _ ≤ K * f ^ 5 * (f ^ (6 : ℕ))⁻¹ :=
      mul_le_mul_of_nonneg_left ((inv_le_inv₀ (pow_pos hgpos 3) (pow_pos hfpos 6)).mpr hpow)
        (mul_nonneg hK (pow_nonneg hfpos.le 5))
    _ = K / f := by field_simp [ne_of_gt hfpos]
    _ ≤ 1 / 2 := (div_le_iff₀ hfpos).mpr (by linarith)

set_option maxHeartbeats 3200000 in
/-- The actual T1–T3 data on the parent slab give the coframe, coercivity,
and mean residual on the next endpoint slab. -/
theorem exists_onSlab_threshold :
    ∃ N : ℝ, 4 ≤ N ∧
      ∀ (P : InductiveEulerParameters), N ≤ P.frequency 0 →
        ∀ {n : ℕ} {activation T : ℝ}, (s : InductiveEulerStage P n activation) →
          ∀ (hT : 0 < T), T ≤ P.slab n activation → ∀ {k : Vec3}, k ≠ 0 →
          Nonempty (s.OnSlab hT k) := by
  obtain ⟨N₀,K,hN₀,hK,hBounds⟩ := exists_parent_projectedMomentum_bounds
  let N := max 4 (max N₀ (2 * K))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro P hN n activation T s hT hTold k hk
  let old := P.slab n activation
  let f := P.frequency n
  let next := P.frequency (n + 1)
  have hold : 0 < old := hT.trans_le hTold
  have hbase : 4 ≤ P.frequency 0 := (le_max_left _ _).trans hN
  obtain ⟨hfreq,hgrow,hsq⟩ := stage_frequency_lower P hbase
  have hNf : N₀ ≤ f := ((le_max_left N₀ (2 * K)).trans (le_max_right _ _)).trans (hN.trans (hfreq n))
  have hKf : 2 * K ≤ f := ((le_max_right N₀ (2 * K)).trans (le_max_right _ _)).trans (hN.trans (hfreq n))
  have hf : 1 ≤ f := (by norm_num : (1 : ℝ) ≤ 4).trans (hbase.trans (hfreq n))
  have hnext : 1 ≤ next := (by norm_num : (1 : ℝ) ≤ 4).trans (hbase.trans (hfreq (n + 1)))
  have hsub : Time(T) ⊆ Icc 0 old := Icc_subset_Icc_right hTold
  have hu : ContDiffOn ℝ ∞ (Function.uncurry s.velocity) Slab(T) :=
    s.smooth_velocity.mono (prod_mono_left hsub)
  have hp : ContDiffOn ℝ ∞ (Function.uncurry s.pressure) Slab(T) :=
    s.smooth_pressure.mono (prod_mono_left hsub)
  have hper (t : ℝ) (_ : t ∈ Time(T)) : SpatiallyPeriodic (s.velocity t) := s.periodic_velocity t
  have hX : IsLabelFlowOn s.velocity s.flow Time(T) := s.deformation.flow.mono hsub
  have hRrestrict (t : ℝ) (ht : t ∈ Time(T)) : momentumResidual Time(T) s.velocity s.pressure t = s.residual t :=
    momentumResidual_restrict_Icc hT le_rfl hTold (s.smooth_velocity.of_le (by simp)) ht
  have hProj (t : ℝ) (ht : t ∈ Time(T)) : closedSlabLerayMomentum 0 T s.velocity t = s.residual t :=
    (closedSlabLerayMomentum_restrict_Icc hT le_rfl hTold (s.smooth_velocity.of_le (by simp)) ht).trans
      (s.projected_eq t (hsub ht)).symm
  obtain ⟨A,Rtor,hA,hRtor,hRnorm,hEvolution,hBand,hGrad⟩ :=
    hBounds hold hNf hnext s.torusVelocity s.residual s.smooth_velocity
      (fun t ht => ⟨s.velocity_bound t ht, s.velocity_band t ht⟩) s.divergence_free
      (fun t ht => (s.projected_eq t ht).symm) s.residual_bound
  have hRjet (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖fderiv ℝ (s.residual t) x‖ ≤ 1 / 2 :=
    (hGrad t (hsub ht) x).2.2.trans (scheduled_residual_derivative_budget hf hK hKf (hsq n))
  have hRjet' (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      ‖fderiv ℝ (momentumResidual Time(T) s.velocity s.pressure t) x‖ ≤ 1 / 2 := by
    rw [hRrestrict t ht]
    exact hRjet t ht x
  have hpGrad (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : DifferentiableAt ℝ (gradient (s.pressure t)) x := by
    have hSlice : ContDiff ℝ ∞ (s.pressure t) := contDiffOn_univ.mp
      (hp.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun a _ => ⟨ht, mem_univ a⟩)
    have hsp : ContDiff ℝ ∞ (fderiv ℝ (s.pressure t)) := hSlice.fderiv_right (m := ∞) (by simp)
    exact ((InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp hsp).differentiable (by simp) x
  have hUpper (t : ℝ) (ht : t ∈ Time(T)) (x w : Vec3) :
      ⟪(fderiv ℝ (gradient (s.pressure t)) x -
        fderiv ℝ (momentumResidual Time(T) s.velocity s.pressure t) x) w, w⟫_ℝ ≤ ‖w‖ ^ 2 :=
    inductionPressure_eulerianCoercivity hbase hgrow (fun v => by
      rw [real_inner_comm]
      exact s.pressure_hessian t (hsub ht) x v) (hRjet' t ht x) w
  obtain ⟨d, hdG, hdM⟩ := HierarchyTwistedProfile.exists_parentGeometry_withBounds hT hX hk hu hper hpGrad
    hf (pow_nonneg (zero_le_one.trans hf) _) (fun t ht a => ((s.deformation.bounds t (hsub ht)).2.2 (s.flow 0 t a)).2)
    (fun t ht x => (hGrad t (hsub ht) x).1) hUpper
  have hsR : ContDiffOn ℝ ∞ (Function.uncurry (momentumResidual Time(T) s.velocity s.pressure)) Slab(T) :=
    contDiffOn_closedSlab_momentumResidual hT hu hp
  have hpR (t : ℝ) (ht : t ∈ Time(T)) : SpatiallyPeriodic (momentumResidual Time(T) s.velocity s.pressure t) := by
    intro m x
    rw [hRrestrict t ht, ← hRtor t (hsub ht) (x + latticeVector m), ← hRtor t (hsub ht) x,
      (toUnitTorus_eq_iff _ _).mpr ⟨m, rfl⟩]
  have hoR (t : ℝ) (ht : t ∈ Time(T)) : Function.Odd (momentumResidual Time(T) s.velocity s.pressure t) := by
    rw [hRrestrict t ht]
    exact odd_closedSlab_momentumResidual_of_projectedData (hsub ht) s.torusVelocity s.pressure
      (s.velocity_band t (hsub ht)) s.odd_velocity (A t) (hA t (hsub ht))
      (fun x => by
        have e := hEvolution t (hsub ht) x
        rw [hRtor t (hsub ht) x] at e
        exact e) hold
  obtain ⟨R,hRmean,hRval,hRparity⟩ :=
    HierarchyTwistedProfile.exists_pulledBackParentResidual hT hX hu hper hsR hpR d
  exact ⟨⟨hsub,d,hdG,hdM,hRrestrict,hProj,Rtor,fun t ht => hRtor t (hsub ht),
    fun t ht => (hBand t (hsub ht)).1, fun t ht => hRnorm t (hsub ht),hRjet,R,hRmean,
    fun x hx => (hRval x hx).trans (congrFun (hRrestrict x.1 hx.1) _),
    hRparity (fun t ht => s.odd_velocity t (hsub ht)) hoR⟩⟩

end

end TorusEuler.InductiveEulerStage
