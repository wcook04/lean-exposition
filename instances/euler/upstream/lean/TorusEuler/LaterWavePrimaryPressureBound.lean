import TorusEuler.HierarchyPhysicalPressureBounds
import TorusEuler.InductiveLaterStageAssembly
import TorusEuler.ParentSeedJetBudgets

/-! The leading pressure Hessian for the actual selected later wave. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.InductiveEulerTip.SelectedLaterInput

noncomputable section

open HierarchyTwistedProfile LocalizedAmplitude

private theorem laterPrimaryPressure_constant_le {D b ℓ B₀ P₀ : ℝ} (a : ℕ)
    (hD : 1 ≤ D) (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (hB₀ : 0 ≤ B₀) (hP₀ : 0 ≤ P₀) :
    let B := (ℓ * D ^ 8) * (b * D)
    let Q := 2 * (4 * (P₀ * D ^ 7) * (B₀ * D ^ 13)) * (max 1 (D ^ a * B)) ^ 2
    let Cb := ℓ * b
    let Cq := 2 * (4 * P₀ * B₀) * Cb ^ 2
    (2 * B ^ 3 + (3 * B ^ 4 + B ^ 2) * Q) ≤
      (2 * Cb ^ 3 + (3 * Cb ^ 4 + Cb ^ 2) * Cq) * D ^ (2 * a + 74) := by
  dsimp only
  let Cb := ℓ * b
  let Cq := 2 * (4 * P₀ * B₀) * Cb ^ 2
  have hCb : 1 ≤ Cb := one_le_mul_of_one_le_of_one_le hℓ hb
  have hCb₀ : 0 ≤ Cb := zero_le_one.trans hCb
  have hCq : 0 ≤ Cq := by dsimp only [Cq]; positivity
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hB : (ℓ * D ^ 8) * (b * D) = Cb * D ^ 9 := by dsimp only [Cb]; ring
  have hJ : 1 ≤ D ^ a * (Cb * D ^ 9) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD)
      (one_le_mul_of_one_le_of_one_le hCb (one_le_pow₀ hD))
  rw [hB, max_eq_right hJ]
  let E := 2 * a + 38
  have hQ : 2 * (4 * (P₀ * D ^ 7) * (B₀ * D ^ 13)) * (D ^ a * (Cb * D ^ 9)) ^ 2 =
      Cq * D ^ E := by
    rw [mul_pow, mul_pow, ← pow_mul D a 2, ← pow_mul D 9 2]
    dsimp only [Cq, E]
    rw [pow_add D (2 * a), Nat.mul_comm 2 a]
    ring
  rw [hQ]
  have hE : E + 36 = 2 * a + 74 := rfl
  have hHead : 2 * Cb ^ 3 * D ^ 27 ≤ 2 * Cb ^ 3 * D ^ (E + 36) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (by positivity)
  have hGeom : 3 * Cb ^ 4 * D ^ 36 + Cb ^ 2 * D ^ 18 ≤
      (3 * Cb ^ 4 + Cb ^ 2) * D ^ 36 := by
    rw [add_mul]
    have hPow : D ^ 18 ≤ D ^ 36 := pow_le_pow_right₀ hD (by decide : (18 : ℕ) ≤ 36)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hPow (sq_nonneg Cb))
  calc
    _ = 2 * Cb ^ 3 * D ^ 27 + (3 * Cb ^ 4 * D ^ 36 + Cb ^ 2 * D ^ 18) * (Cq * D ^ E) := by ring
    _ ≤ 2 * Cb ^ 3 * D ^ (E + 36) +
        ((3 * Cb ^ 4 + Cb ^ 2) * D ^ 36) * (Cq * D ^ E) :=
      add_le_add hHead (mul_le_mul_of_nonneg_right hGeom (by positivity))
    _ = (2 * Cb ^ 3 + (3 * Cb ^ 4 + Cb ^ 2) * Cq) * D ^ (E + 36) := by
      rw [pow_add D E 36]
      ring
    _ = _ := by rw [hE]

set_option maxHeartbeats 2500000 in
/-- The leading pressure Hessian of Lemma 5.9 for any physical
parent geometry with Bernstein-scale velocity jets. -/
theorem _root_.TorusEuler.exists_parent_leading_pressure_hessian_bound
    (W : ℕ → ℝ) (hW : ∀ j, 0 ≤ W j) :
    ∃ (A : ℕ) (C : ℝ), 30 ≤ A ∧ 0 ≤ C ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ell Cseed freq rate : ℝ}
        {a : ℕ} {k : Vec3} {center : ℝ → Vec3},
        0 < T → T ≤ 1 → 2 ≤ D → 1 ≤ freq → A ≤ a → ell⁻¹ = D ^ a →
        ‖labelWaveVector X 0 0 k t₀‖ = freq → ‖k‖ ≤ D * freq →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X 0 t) x‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X t 0) (X 0 t x)‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (U t) x‖ ≤ W n * D ^ j) →
        (∀ t ∈ Icc t₀ T, ‖center t‖ ≤ freq ^ (-3 / 4 : ℝ)) →
        let M (t : ℝ) (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
        let κ (t : ℝ) (x : Vec3) := labelWaveVector X 0 x k t
        CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D →
        ∀ (seed : SeedOn M κ center t₀ T ell D Cseed)
          (reg : seed.HierarchyRegularity rate (freq ^ (-1 / 2 : ℝ))),
        ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
          ⟪v, fderiv ℝ (gradient (graphRead (fun u => X u 0) (seed.twistedPressure reg k) t)) x v⟫_ℝ ≤
            (C * D ^ (2 * a + 74) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  obtain ⟨A, hA, hSeed⟩ := exists_parent_seed_leadingAndSlowJetBounds W hW
  obtain ⟨_, Cseed, Cpressure, _, hCseed, hCpressure, hSlow⟩ := hSeed 2
  obtain ⟨Gjet, hGjet, hParent⟩ := exists_parent_coefficientJetBounds W hW
  let b := 1 + W 1
  let l := 1 + Gjet 1
  let Cb := l * b
  let Cq := 2 * (4 * Cpressure * Cseed) * Cb ^ 2
  let C := 2 * Cb ^ 3 + (3 * Cb ^ 4 + Cb ^ 2) * Cq
  have hb : 1 ≤ b := le_add_of_nonneg_right (hW 1)
  have hl : 1 ≤ l := le_add_of_nonneg_right (hGjet 1)
  have hCs : 0 ≤ Cseed := zero_le_one.trans hCseed
  have hCp : 0 ≤ Cpressure := zero_le_one.trans hCpressure
  refine ⟨A, C, hA, by dsimp only [C, Cq, Cb]; positivity, ?_⟩
  intro U X T t₀ D ell Cinput freq rate a k center hT hTime hD₂ hfreq ha hRadius
    hLaunch hCarrier hX hU hper hF hG hVel hCap M κ hCenter seed reg t ht x v
  let B := b * D
  let L := l * D ^ 8
  have hD : 1 ≤ D := one_le_two.trans hD₂
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hb hD
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hl (one_le_pow₀ hD)
  have hDB : D ≤ B := le_mul_of_one_le_left hD₀ hb
  have hM (y : Vec3) : ‖fderiv ℝ (U t) y‖ ≤ B := by
    have hj := hVel 1 1 le_rfl le_rfl t ht y
    rw [norm_iteratedFDeriv_one, pow_one] at hj
    exact hj.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hD₀)
  have hG₁ (y : Vec3) : ‖fderiv ℝ (fun z => fderiv ℝ (X t 0) (X 0 t z)) y‖ ≤ L := by
    have hj := (hParent hT hTime hD hX hU hper hF hG hVel k
      (zero_lt_one.trans_le hfreq) ⟨reg.nonneg_start, reg.start_lt_end.le⟩ hLaunch 1 t ht y).2.1
    rw [norm_iteratedFDeriv_one] at hj
    exact hj.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity))
  have hCar : ‖k‖ ≤ B * freq := hCarrier.trans
    (mul_le_mul_of_nonneg_right hDB (zero_le_one.trans hfreq))
  have hEll : ell ≤ (D ^ A)⁻¹ := by
    rw [← inv_inv ell, hRadius]
    exact inv_anti₀ (pow_pos (zero_lt_one.trans_le hD) _) (pow_le_pow_right₀ hD ha)
  have hRows (ha : t₀ ≤ t) := hSlow (k := k) reg.nonneg_start reg.start_lt_end hTime hD₂
    reg.envelope_pos hEll hfreq hLaunch hX hU hper hF hG hVel hCenter seed
    (χ := (1 : ℝ)) (by norm_num) t ⟨ha, ht.2⟩
  have hAmp (ha : t₀ ≤ t) :
      PhaseJetBound 2 ((Cseed * D ^ 13) * ‖center t‖)
        (fun y => radialEnvelope ell (ell • y) • seed.amplitude t (ell • y)) :=
    (hRows ha).2.1
  have hP (ha : t₀ ≤ t) :
      let F (y : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M t (ell • y))
        (freq⁻¹ • κ t (ell • y))
      ContDiff ℝ ∞ F ∧ PhaseJetBound 2 (Cpressure * D ^ 7) F := (hRows ha).2.2
  have hbud := SeedOn.primaryPressureBudget_of_parent_seedJets (seed := seed) reg
    hX hU hper ht hfreq hB hL (by positivity : 0 ≤ Cseed * D ^ 13)
    (by positivity : 0 ≤ Cpressure * D ^ 7) rfl (fun ha => hCap t ⟨ha, ht.2⟩)
    hCar hM (fun y => (hG t ht y).trans hDB) hG₁ hAmp hP
  have hBound := SeedOn.twistedPressure_parentGraph_hessian_upper (seed := seed) reg
    hX hU hper ht hbud x v
  have hConstant :
      2 * (L * B) ^ 3 + (3 * (L * B) ^ 4 + (L * B) ^ 2) *
        (2 * (4 * (Cpressure * D ^ 7) * (Cseed * D ^ 13)) * (max 1 (ell⁻¹ * (L * B))) ^ 2) ≤
      C * D ^ (2 * a + 74) := by
    rw [hRadius]
    exact laterPrimaryPressure_constant_le a hD hb hl hCs hCp
  exact hBound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hConstant (by positivity)) (sq_nonneg _))

/-- The actual selected leading pressure has the same uniform one-sided
bound on the scheduled later slabs. -/
theorem exists_leading_pressure_hessian_bound :
    ∃ (A : ℕ) (C : ℝ), 30 ≤ A ∧ 0 ≤ C ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {tip : InductiveEulerTip P n}
        {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a), A ≤ a →
        ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation), ∀ x v : Vec3,
        ⟪v, fderiv ℝ (gradient (d.approximation.leadingPressure t)) x v⟫_ℝ ≤
          (C * (P.frequency (n + 1) ^ 9) ^ (2 * a + 74) * P.frequency (n + 2) ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  obtain ⟨W, hW, hVelocity⟩ := InductiveEulerStage.exists_velocity_jet_bounds
  obtain ⟨A, C, hA, hC, hBound⟩ := exists_parent_leading_pressure_hessian_bound W hW
  refine ⟨A, C, hA, hC, ?_⟩
  intro P n tip Cenv a d ha t ht x v
  let D := P.frequency (n + 1) ^ (9 : ℕ)
  let T := P.slab (n + 2) tip.nextActivation
  let U := tip.parent.velocity
  let X := tip.parent.flow
  have hParentOne : 1 ≤ P.frequency (n + 1) := one_le_two.trans d.parent_frequency_ge_two
  have hF (u : ℝ) (hu : u ∈ Icc 0 T) (y : Vec3) : ‖fderiv ℝ (X 0 u) y‖ ≤ D :=
    ((d.parent.deformationOn.bounds u hu).2.1 y).2.trans d.parent_frequency_le_scale
  have hG (u : ℝ) (hu : u ∈ Icc 0 T) (y : Vec3) : ‖fderiv ℝ (X u 0) (X 0 u y)‖ ≤ D :=
    ((d.parent.deformationOn.bounds u hu).2.2 (X 0 u y)).2.trans d.parent_frequency_le_scale
  have hVel (m j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) (u : ℝ) (hu : u ∈ Icc 0 T) (y : Vec3) :
      ‖iteratedFDeriv ℝ j (U u) y‖ ≤ W m * D ^ j :=
    hVelocity tip.parent hParentOne m j hj hm u (d.parent.subset hu) y
  have hCap (u : ℝ) (hu : u ∈ Icc tip.nextActivation T) :
      ‖d.selection.crossing.amplitude u‖ ≤ P.frequency (n + 2) ^ (-3 / 4 : ℝ) := by
    simpa only [neg_div] using d.center_amplitude_le_peak u hu
  change ⟪v, fderiv ℝ (gradient (graphRead (fun u => X u 0) (d.seed.twistedPressure d.regularity d.carrier) t)) x v⟫_ℝ ≤ _
  exact hBound d.time_pos d.time_le_one d.parent_scale_ge_two d.child_frequency_ge_one
    ha d.radius_inv d.label_launch_covector_norm d.carrier_bound d.parent.deformationOn.flow
    d.parent.smooth_velocity (fun u _ => tip.parent.periodic_velocity u)
    hF hG hVel hCap d.centerWaveOn_labels d.seed d.regularity t ht x v

end
end TorusEuler.InductiveEulerTip.SelectedLaterInput
