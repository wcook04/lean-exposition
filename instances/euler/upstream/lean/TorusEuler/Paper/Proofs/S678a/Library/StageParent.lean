import TorusEuler.Paper.Proofs.S678a.Library.ParentBridge

/-! # The parent `S5.Parent` of a stage (package S678a)

An `InductiveEulerStage` of the construction, restricted to a
slab `[0,T] ⊆ [0,S]`, satisfies `S5.Parent` with `𝖣 = λ_n^9` and frequency `λ_{n+1}` (the standing
hypotheses of Section 5.1, sections/08a_parent_step.tex:9-33 and sections/08b_induction.tex:269-282).
Copy of the argument of `InductiveEulerStage.exists_onSlab_threshold`
(InductiveParentGeometry.lean:107) with the projected-momentum bounds taken from `hB_1`
(`projectedMomentum_bounds_of_hB1`). -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

noncomputable section

local notation "Time(" T ")" => Icc (0 : ℝ) T
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

/-- Frequencies of a parameter record with `4 ≤ μ_0` are nondecreasing, at least double at each step and at least squared at each step. -/
theorem stage_frequency_lower (P : InductiveEulerParameters) (h₀ : 4 ≤ P.frequency 0) :
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

/-- Elementary inequality `K f^5 g^(-3) ≤ 1/2` for `1 ≤ f`, `2K ≤ f` and `f^2 ≤ g`. -/
theorem scheduled_residual_derivative_budget {f g K : ℝ}
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

/-- A torus field supported on frequencies at most `D` is supported on frequencies at most `D'` for `D ≤ D'`. -/
theorem band_mono {D D' : ℝ} {g : C(UnitAddTorus (Fin 3), Vec3)} (h : D ≤ D')
    (hb : RealTorusFourierBand D g) : RealTorusFourierBand D' g :=
  fun k hk => hb k (lt_of_le_of_lt h hk)

set_option maxHeartbeats 3200000 in
/-- **The parent of a stage.** For `N ≤ λ_0` large, a stage `s` of index `n`, restricted to
`[0,T] ⊆ [0,S_n]` with `T ≤ 1`, satisfies the standing hypotheses `S5.Parent` of Section 5
with `𝖣 = λ_n^9` and frequency `λ_{n+1}`: the velocity bands `2λ_n^5 ≤ 2𝖣`, the bounds (5.1), the
residual band `4λ_n^5 ≤ 4𝖣` and size (5.6) from the Leray identity (7.5) and (T1), and the
coercivity (5.2) from (T3) and the Bernstein bound for `∇R` (`hB_1`). Uses `hB_1`
through `projectedMomentum_bounds_of_hB1`. -/
theorem stage_parent (hB_1 : Statement.lemma_B_1) :
    ∃ N : ℝ, 4 ≤ N ∧
      ∀ (P : InductiveEulerParameters), N ≤ P.frequency 0 →
        ∀ {n : ℕ} {activation T : ℝ} (s : InductiveEulerStage P n activation),
          0 < T → T ≤ P.slab n activation → T ≤ 1 →
          S5.Parent T s.velocity s.flow s.pressure (P.frequency n ^ 9) (P.frequency (n + 1)) := by
  obtain ⟨N₀, K, hN₀, hK, hBounds⟩ := projectedMomentum_bounds_of_hB1 hB_1
  let N := max 4 (max N₀ (2 * K))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro P hN n activation T s hT hTold hT1
  let old := P.slab n activation
  let f := P.frequency n
  let next := P.frequency (n + 1)
  have hold : 0 < old := hT.trans_le hTold
  have hbase : 4 ≤ P.frequency 0 := (le_max_left _ _).trans hN
  obtain ⟨hfreq, hgrow, hsq⟩ := stage_frequency_lower P hbase
  have hNf : N₀ ≤ f := ((le_max_left N₀ (2 * K)).trans (le_max_right _ _)).trans (hN.trans (hfreq n))
  have hKf : 2 * K ≤ f := ((le_max_right N₀ (2 * K)).trans (le_max_right _ _)).trans (hN.trans (hfreq n))
  have hf4 : 4 ≤ f := hbase.trans (hfreq n)
  have hf : 1 ≤ f := (by norm_num : (1 : ℝ) ≤ 4).trans hf4
  have hnext : 1 ≤ next := (by norm_num : (1 : ℝ) ≤ 4).trans (hbase.trans (hfreq (n + 1)))
  have hsub : Time(T) ⊆ Icc 0 old := Icc_subset_Icc_right hTold
  have hu : ContDiffOn ℝ ∞ (Function.uncurry s.velocity) Slab(T) :=
    s.smooth_velocity.mono (prod_mono_left hsub)
  have hp : ContDiffOn ℝ ∞ (Function.uncurry s.pressure) Slab(T) :=
    s.smooth_pressure.mono (prod_mono_left hsub)
  have hper (t : ℝ) (_ : t ∈ Time(T)) : SpatiallyPeriodic (s.velocity t) := s.periodic_velocity t
  have hX : IsLabelFlowOn s.velocity s.flow Time(T) := s.deformation.flow.mono hsub
  have hRrestrict (t : ℝ) (ht : t ∈ Time(T)) :
      momentumResidual Time(T) s.velocity s.pressure t = s.residual t :=
    momentumResidual_restrict_Icc hT le_rfl hTold (s.smooth_velocity.of_le (by simp)) ht
  have hsRfull : ContDiffOn ℝ ∞ (Function.uncurry s.residual) (Icc 0 old ×ˢ (univ : Set Vec3)) :=
    contDiffOn_closedSlab_momentumResidual hold s.smooth_velocity s.smooth_pressure
  have hRs (t : ℝ) (ht : t ∈ Icc 0 old) : ContDiff ℝ ∞ (s.residual t) :=
    contDiffOn_univ.mp (hsRfull.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun a _ => ⟨ht, mem_univ a⟩))
  obtain ⟨A, Rtor, hA, hRtor, hRnorm, hEvolution, hBand, hGrad⟩ :=
    hBounds hold hNf hnext s.torusVelocity s.residual hRs s.smooth_velocity
      (fun t ht => ⟨s.velocity_bound t ht, s.velocity_band t ht⟩) s.divergence_free
      (fun t ht => (s.projected_eq t ht).symm) s.residual_bound
  have hRjet (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖fderiv ℝ (s.residual t) x‖ ≤ 1 / 2 :=
    (hGrad t (hsub ht) x).2.2.trans (scheduled_residual_derivative_budget hf hK hKf (hsq n))
  have hRjet' (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      ‖fderiv ℝ (momentumResidual Time(T) s.velocity s.pressure t) x‖ ≤ 1 / 2 := by
    rw [hRrestrict t ht]
    exact hRjet t ht x
  have hUpper (t : ℝ) (ht : t ∈ Time(T)) (x w : Vec3) :
      ⟪(fderiv ℝ (gradient (s.pressure t)) x -
        fderiv ℝ (momentumResidual Time(T) s.velocity s.pressure t) x) w, w⟫_ℝ ≤ ‖w‖ ^ 2 :=
    inductionPressure_eulerianCoercivity hbase hgrow (fun v => by
      rw [real_inner_comm]
      exact s.pressure_hessian t (hsub ht) x v) (hRjet' t ht x) w
  have hoR (t : ℝ) (ht : t ∈ Time(T)) :
      Function.Odd (momentumResidual Time(T) s.velocity s.pressure t) := by
    rw [hRrestrict t ht]
    exact odd_closedSlab_momentumResidual_of_projectedData (hsub ht) s.torusVelocity s.pressure
      (s.velocity_band t (hsub ht)) s.odd_velocity (A t) (hA t (hsub ht))
      (fun x => by
        have e := hEvolution t (hsub ht) x
        rw [hRtor t (hsub ht) x] at e
        exact e) hold
  have h2f : f ≤ f ^ 9 := le_self_pow₀ hf (by norm_num)
  have hfD : f ^ 5 ≤ f ^ 9 := pow_le_pow_right₀ hf (by norm_num)
  refine
    { time_le_one := hT1
      scale_ge_two := by linarith
      frequency_ge_one := hnext
      flow := hX
      velocity_smooth := hu
      velocity_periodic := hper
      velocity_odd := fun t ht => s.odd_velocity t (hsub ht)
      divergence_free := fun t ht => s.divergence_free t (hsub ht)
      velocity_band := ⟨s.torusVelocity, fun t ht =>
        ⟨fun x => rfl, band_mono (by linarith) (s.velocity_band t (hsub ht))⟩⟩
      gradient_le := fun t ht x => (hGrad t (hsub ht) x).1
      deformation_le := fun t ht a =>
        (((s.deformation.bounds t (hsub ht)).2.1 a).2).trans h2f
      inverse_deformation_le := fun t ht a =>
        (((s.deformation.bounds t (hsub ht)).2.2 (s.flow 0 t a)).2).trans h2f
      pressure_smooth := hp
      pressure_periodic := fun t ht => s.periodic_pressure t (hsub ht)
      residual_odd := hoR
      residual_band := ⟨Rtor, fun t ht =>
        ⟨fun x => (hRtor t (hsub ht) x).trans (congrFun (hRrestrict t ht) x).symm,
          band_mono (by linarith) (hBand t (hsub ht)).1,
          (hRnorm t (hsub ht)).trans
            (Real.rpow_le_rpow_of_exponent_le hnext (by norm_num))⟩⟩
      coercive := fun t ht x w => hUpper t ht x w }

end

end TorusEuler.Paper.Lib.S678a
