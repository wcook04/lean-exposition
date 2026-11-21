import TorusEuler.HierarchyStageCoefficientCaps
import TorusEuler.HierarchyPhysicalVelocityBounds

/-! Pullback jets for the actual corrected velocity and the cutoff tail. -/

open ContinuousLinearMap MeasureTheory Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

/-- The absolute exponent for both flow jet bounds. -/
def profileFlowJetPower (lossPower : ℕ) : ℕ := 6 * lossPower + 8

/-- The fixed-order cost of multiplying by the coframe and taking scaled jets. -/
def profileFlowCoframeCost (C : ℕ → ℝ) (m : ℕ) : ℝ :=
  (4 : ℝ) ^ m * hierarchyQuadraticConstant (Fin 4) m *
    InductiveEulerStage.stageCoefficientOrderConstant C m

/-- The fixed cost of the uncut oscillatory pullback. -/
def profileFlowOscillationCost (C : ℕ → ℝ) (depth : ℕ) (levelConstant : ℝ) : ℝ :=
  profileFlowCoframeCost C 2 * (2 * ((Finset.Icc 1 depth).card : ℝ) * levelConstant)

/-- The fixed cost of the uncut mean pullback. -/
def profileFlowMeanCost (C : ℕ → ℝ) (depth : ℕ) (levelConstant : ℝ) : ℝ :=
  profileFlowCoframeCost C 1 * (((Finset.Icc 1 depth).card : ℝ) * levelConstant)

/-- The common coefficient for the two uncut profiles and the cutoff tail. -/
def profileFlowJetConstant (C : ℕ → ℝ) (depth : ℕ) (levelConstant : ℝ) : ℝ :=
  profileFlowOscillationCost C depth levelConstant +
    profileFlowMeanCost C depth levelConstant + (1 + C 1)

private theorem profileFlowCoframeCost_nonneg (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (m : ℕ) :
    0 ≤ profileFlowCoframeCost C m := by
  have hQ : 0 ≤ hierarchyQuadraticConstant (Fin 4) m := by unfold hierarchyQuadraticConstant; positivity
  have hJ := InductiveEulerStage.stageCoefficientOrderConstant_nonneg C hC m
  unfold profileFlowCoframeCost
  positivity

/-- The finite flow prefactor is positive for a nonnegative level budget. -/
theorem one_le_profileFlowJetConstant (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (depth : ℕ)
    {levelConstant : ℝ} (hLevelC : 0 ≤ levelConstant) :
    1 ≤ profileFlowJetConstant C depth levelConstant := by
  have hOsc := profileFlowCoframeCost_nonneg C hC 2
  have hMean := profileFlowCoframeCost_nonneg C hC 1
  have h₁ := hC 1
  unfold profileFlowJetConstant profileFlowOscillationCost profileFlowMeanCost
  exact (le_add_of_nonneg_right h₁).trans
    (le_add_of_nonneg_left (add_nonneg (mul_nonneg hOsc (by positivity)) (mul_nonneg hMean (by positivity))))

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

local notation "I" => Icc (0 : ℝ) T
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

private theorem inverseCoframe_mul_unweighted_le (hT : 0 < T) (ℓ h : ℝ) (m : ℕ)
    (G : MP) (f : VP) :
    unweightedSeminorm False ℓ h m hT (applyField G f) ≤
      hierarchyQuadraticConstant (Fin 4) m * unweightedSeminorm False ℓ h m hT G *
        unweightedSeminorm False ℓ h m hT f := by
  let B : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 →L[ℝ] Vec3 := (ContinuousLinearMap.apply ℝ Vec3).flip
  have hB : ‖B‖ ≤ 1 := by
    simp only [B, opNorm_flip, ContinuousLinearMap.apply]
    refine opNorm_le_bound _ zero_le_one fun u => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  let UG := unweightedSeminorm False ℓ h m hT G
  let Uf := unweightedSeminorm False ℓ h m hT f
  calc
    _ ≤ (hierarchyAdmissibleWords (Fin 4) m).card * (2 : ℝ) ^ m * (2 * ‖B‖ * UG * Uf) :=
      boundedWeightSeminorm_bilinear_le B False ℓ h m hT (Subset.rfl : I ⊆ I)
        (fun _ => 1) (fun _ => 1) (fun _ => 1) (Cf := 1) (Cg := 1) (Cfg := 1)
        (by simp) (by simp) (by simp) (by simp) G f (applyField G f) (by
          intro t ht x
          have hx : (t,x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ x⟩
          rw [applyField_val, HierarchyPeriodicProfile.applyField_val,
            HierarchySmoothProfile.applyField_eval _ _ hx]
          rfl)
    _ ≤ _ := by
      have hUG : 0 ≤ UG := apply_nonneg _ _
      have hUf : 0 ≤ Uf := apply_nonneg _ _
      calc
        _ ≤ (hierarchyAdmissibleWords (Fin 4) m).card * (2 : ℝ) ^ m * (2 * 1 * UG * Uf) := by gcongr
        _ = _ := by dsimp only [UG, Uf, hierarchyQuadraticConstant]; ring

/-- The actual inverse parent coframe has the finite label norm given
by its raw derivative bounds and the small envelope radius. -/
theorem inverseCoframe_unweighted_le_of_parent
    {U : Velocity} {X : ℝ → Velocity} {hT : 0 < T} (d : ParentGeometry hT U X k)
    {D ℓ h : ℝ} {C : ℕ → ℝ} (hℓ : 0 ≤ ℓ) (hD : 1 ≤ D)
    (hscale : ℓ * D ^ (7 : ℕ) ≤ 1) (hC : ∀ j, 0 ≤ C j) (m : ℕ)
    (hSmooth : ∀ t ∈ I, ContDiff ℝ ∞ (fun x => fderiv ℝ (X t 0) (X 0 t x)))
    (hJets : ∀ j, ∀ t ∈ I, ∀ x : Vec3,
      ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (X t 0) (X 0 t y)) x‖ ≤ C j * D ^ (7 * j + 1)) :
    unweightedSeminorm False ℓ h m hT d.inverse ≤
      InductiveEulerStage.stageCoefficientOrderConstant C m * D := by
  let G (t : I) (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
  have hRaw (t : I) (j : ℕ) (_hj : j ≤ m) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (G t) x‖ ≤ C j * D * D ^ (7 * j) := by
    refine (hJets j t t.property x).trans_eq ?_
    rw [pow_add, pow_one]
    ring
  have hCoef := HierarchyRelayCoefficientJets.of_parent_power_bound (h := h) (q := 7)
    hℓ (zero_le_one.trans hD) (zero_le_one.trans hD) hscale
    (fun (t : I) => hSmooth t t.property) (fun j _ => hC j) hRaw
  refine (unweightedSeminorm_le_of_labelCoefficientJets hT ℓ h m d.inverse G
    (fun t x => d.inverse_value (t,x) ⟨t.property, mem_univ x⟩) hCoef).trans_eq ?_
  unfold InductiveEulerStage.stageCoefficientOrderConstant
  ring

end HierarchyTwistedProfile

namespace HierarchyTwistedProfile.PhysicalApproximationData

section PhaseSplit

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "VP" => HierarchyTwistedProfile T k Vec3

set_option maxHeartbeats 1800000 in
private theorem phaseMean_phaseOscillation_pullback_zero (b : PhysicalApproximationData d p P)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    let pv := b.profiles.velocity P
    let g := fun r => ChildFlow.pullbackField X b.profileVelocity 0 t (a,r)
    phaseMean g = (applyField d.inverse (b.operators.average pv)).val.val.val (t,a,s) ∧
      phaseOscillation g s =
        (applyField d.inverse (pv - b.operators.average pv)).val.val.val (t,a,s) := by
  intro pv g
  let G := fderiv ℝ (X t 0) (X 0 t a)
  have hx (r : ℝ) : (t,a,r) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hG (r : ℝ) : d.inverse.val.val.val (t,a,r) = G := d.inverse_value _ (hx r)
  have hApp (q : VP) (r : ℝ) :
      (applyField d.inverse q).val.val.val (t,a,r) = G (q.val.val.val (t,a,r)) := by
    rw [applyField_val, HierarchyPeriodicProfile.applyField_val,
      HierarchySmoothProfile.applyField_eval _ _ (hx r), hG r]
  have hAvg (r : ℝ) : (b.operators.average pv).val.val.val (t,a,r) =
      phaseMean (b.profileVelocity t a) := by
    change (HierarchySmoothProfile.profilePhaseAverage hT pv.val.val).val (t,a,r) = _
    exact HierarchySmoothProfile.profilePhaseAverage_apply hT pv.val.val (hx r)
  have hPull : g = fun r => G (b.profileVelocity t a r) := by
    funext r
    change G (b.profileVelocity t a r + 0) = _
    rw [add_zero]
  have hC : Continuous (b.profileVelocity t a) := by
    change Continuous (Function.uncurry (b.profileVelocity t) ∘ fun r : ℝ => (a,r))
    exact (b.profileVelocity_smooth t ht).continuous.comp (continuous_const.prodMk continuous_id)
  have hMeanG : phaseMean g = G (phaseMean (b.profileVelocity t a)) := by
    rw [hPull]
    simpa only [phaseMean, Function.comp_apply] using G.intervalIntegral_comp_comm (hC.intervalIntegrable 0 1)
  refine ⟨hMeanG.trans ((hApp (b.operators.average pv) s).trans
    (congrArg G (hAvg s))).symm, ?_⟩
  have hv : pv.val.val.val (t,a,s) = b.profileVelocity t a s := rfl
  have hSub : (pv - b.operators.average pv).val.val.val (t,a,s) =
      b.profileVelocity t a s - phaseMean (b.profileVelocity t a) := by
    change pv.val.val.val (t,a,s) - (b.operators.average pv).val.val.val (t,a,s) = _
    rw [hv, hAvg s]
  change g s - phaseMean g = _
  exact (congrArg₂ (· - ·) (congrFun hPull s) hMeanG).trans
    ((G.map_sub _ _).symm.trans
      ((congrArg G hSub.symm).trans (hApp (pv - b.operators.average pv) s).symm))

set_option maxHeartbeats 800000 in
private theorem phaseMean_phaseOscillation_pullback_zero_fun (b : PhysicalApproximationData d p P)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let pv := b.profiles.velocity P
    (fun (a : Vec3) (_ : ℝ) => phaseMean (fun r => ChildFlow.pullbackField X b.profileVelocity 0 t (a,r))) =
      (fun (a : Vec3) (s : ℝ) => (applyField d.inverse (b.operators.average pv)).val.val.val (t,a,s)) ∧
    (fun (a : Vec3) (s : ℝ) => phaseOscillation (fun r => ChildFlow.pullbackField X b.profileVelocity 0 t (a,r)) s) =
      (fun (a : Vec3) (s : ℝ) => (applyField d.inverse (pv - b.operators.average pv)).val.val.val (t,a,s)) := by
  intro pv
  exact ⟨funext fun a => funext fun s => (b.phaseMean_phaseOscillation_pullback_zero ht a s).1,
    funext fun a => funext fun s => (b.phaseMean_phaseOscillation_pullback_zero ht a s).2⟩

end PhaseSplit

variable {T : ℝ} {k : Vec3} {hT : 0 < T}
  {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ} {parent : InductiveEulerStage P n activation}

local notation "I" => Icc (0 : ℝ) T
local notation "VP" => HierarchyTwistedProfile T k Vec3


private theorem coframeApplied_scaledJets {U : Velocity} {X : ℝ → Velocity}
    {d : ParentGeometry hT U X k} {D ℓ h freq : ℝ}
    {C : ℕ → ℝ} (m : ℕ)
    (hG : unweightedSeminorm False ℓ h m hT d.inverse ≤
      InductiveEulerStage.stageCoefficientOrderConstant C m * D)
    (hD : 1 ≤ D) (hf : 0 < freq) (hC : ∀ j, 0 ≤ C j) (f : VP)
    {A α : ℝ} {q : ℕ} (hA : 0 ≤ A)
    (hN : unweightedSeminorm False ℓ h m hT f ≤ A * D ^ q * freq ^ α)
    {t : ℝ} (ht : t ∈ I) :
    PhaseJetBound m (profileFlowCoframeCost C m * A * D ^ (q + 1) * freq ^ α)
      (scaledPhaseProfile ℓ h (slice (applyField d.inverse f) t)) := by
  have hq : 0 ≤ hierarchyQuadraticConstant (Fin 4) m := by unfold hierarchyQuadraticConstant; positivity
  have hJ := InductiveEulerStage.stageCoefficientOrderConstant_nonneg C hC m
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hA₀ : 0 ≤ A * D ^ q * freq ^ α := by positivity
  have hj := scaledPhaseProfile_jetBound_unweighted hT ℓ h m (applyField d.inverse f) ht
  intro j hjm x
  refine (hj j hjm x).trans ?_
  calc
    _ ≤ (4 : ℝ) ^ m * (hierarchyQuadraticConstant (Fin 4) m *
        unweightedSeminorm False ℓ h m hT d.inverse * unweightedSeminorm False ℓ h m hT f) :=
      mul_le_mul_of_nonneg_left (inverseCoframe_mul_unweighted_le hT ℓ h m d.inverse f) (by positivity)
    _ ≤ (4 : ℝ) ^ m * (hierarchyQuadraticConstant (Fin 4) m *
        (InductiveEulerStage.stageCoefficientOrderConstant C m * D) * (A * D ^ q * freq ^ α)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left hG hq) hN (apply_nonneg _ _) (by positivity)) (by positivity)
    _ = _ := by rw [pow_succ]; dsimp only [profileFlowCoframeCost]; ring

private theorem centeredProfileZero_of_inactive {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
    {d : ParentGeometry hT U X k} {depth : ℕ}
    (b : PhysicalApproximationData d p depth) (hDepth : 1 ≤ depth)
    {t₀ : ℝ} {S : Set Vec3} (hS : IsClosed S) (hInactive : b.leading.Inactive t₀ S) :
    ∀ t ∈ I, t < t₀ → ∀ x : Vec3 × ℝ,
      (b.profiles.velocity depth - b.operators.average (b.profiles.velocity depth)).val.val.val (t,x) = 0 := by
  obtain ⟨hSupport, _, _⟩ := physicalConstruct_support_and_tail_on_inactive hT b.time_le_one hS
    d.inverse d.strain d.covector d.mean d.oscillation
    hDepth b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output
    hInactive.velocity hInactive.pressure hInactive.completionSwitch
  have heq : b.profiles.velocity depth - b.operators.average (b.profiles.velocity depth) =
      ∑ i ∈ Finset.Icc 1 depth, (b.profiles.V i + b.profiles.C i) :=
    b.solvers.construct_velocity_sub_average depth b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output
  intro t ht ht₀ x
  rw [heq]
  let ev : VP →ₗ[ℝ] Vec3 := ⟨⟨fun f => f.val.val.val (t,x), fun _ _ => rfl⟩, fun _ _ => rfl⟩
  change ev (∑ i ∈ Finset.Icc 1 depth, (b.profiles.V i + b.profiles.C i)) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hx : (t,x) ∈ hierarchyInactiveRegion T t₀ S := ⟨⟨ht, mem_univ x⟩, Or.inl ht₀⟩
  change (b.profiles.V i).val.val.val (t,x) + (b.profiles.C i).val.val.val (t,x) = 0
  have hv : (b.profiles.V i).val.val.val (t,x) = 0 := (hSupport i).1 hx
  have hc : (b.profiles.C i).val.val.val (t,x) = 0 := (hSupport i).2.1 hx
  rw [hv, hc, add_zero]

set_option maxHeartbeats 2200000 in
/-- The finite measured levels give the uncut oscillatory and mean
pullbacks. These bounds apply before any choice of Eulerian perturbation. -/
theorem uncutPullbackProfileJetBounds_of_actualLevels
    {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
    {d : ParentGeometry hT U X k} {depth lossPower : ℕ} {D ℓ h freq : ℝ} {C : ℕ → ℝ}
    (hCoefficient : ∀ m, unweightedSeminorm False ℓ h m hT d.inverse ≤
      InductiveEulerStage.stageCoefficientOrderConstant C m * D)
    (hD : 1 ≤ D) (hC : ∀ j, 0 ≤ C j) (hf : 1 ≤ freq)
    (b : PhysicalApproximationData d p depth) (hDepth : 1 ≤ depth)
    {levelConstant : ℝ} (hLevelC : 0 ≤ levelConstant)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {S : Set Vec3} (hS : IsClosed S)
    (hInactive : b.leading.Inactive t₀ S)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγmax : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hLevels : ∀ m ≤ 2, ∀ j ∈ Finset.Icc 1 depth, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles depth b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ℓ h hT ht₀ htT γ hγ hpos) freq (D ^ lossPower) levelConstant m j) :
    let Aosc := profileFlowOscillationCost C depth levelConstant
    let Amean := profileFlowMeanCost C depth levelConstant
    0 ≤ Aosc ∧ 0 ≤ Amean ∧
    (∀ t ∈ I, PhaseJetBound 2 (Aosc * D ^ (2 * lossPower + 1) * freq ^ (-5 / 4 : ℝ))
      (scaledPhaseProfile ℓ h (fun x => phaseOscillation
        (fun r => ChildFlow.pullbackField X b.profileVelocity 0 t (x, r))))) ∧
    ∀ t ∈ I, PhaseJetBound 1 (Amean * D ^ (6 * lossPower + 1) * freq ^ (-5 / 2 : ℝ))
      (scaledPhaseProfile ℓ h (fun x _ => phaseMean
        (fun r => ChildFlow.pullbackField X b.profileVelocity 0 t (x, r)))) := by
  intro Aosc Amean
  let count := ((Finset.Icc 1 depth).card : ℝ)
  let F := b.profiles.velocity depth
  let Fmean := b.operators.average F
  let Fosc := F - Fmean
  let N (m : ℕ) : Seminorm ℝ VP := unweightedSeminorm False ℓ h m hT
  have hfpos : 0 < freq := zero_lt_one.trans_le hf
  have hLoss : 1 ≤ D ^ lossPower := one_le_pow₀ hD
  have hcount : 0 ≤ count := Nat.cast_nonneg _
  have hAosc : 0 ≤ Aosc := mul_nonneg (profileFlowCoframeCost_nonneg C hC 2) (by positivity)
  have hAmean : 0 ≤ Amean := mul_nonneg (profileFlowCoframeCost_nonneg C hC 1) (mul_nonneg hcount hLevelC)
  have hOscNorm : N 2 Fosc ≤ (2 * count * levelConstant) * D ^ (2 * lossPower) * freq ^ (-5 / 4 : ℝ) := by
    have hm := (b.velocityProfileSums_of_actualLevels hDepth 2 hf hLoss hLevelC ht₀ htT γ hγ hpos
      (hLevels 2 le_rfl)).1
    refine ((unweightedSeminorm_le_amplitudeSeminorm_of_inactive False ℓ h 2 hT ht₀ htT γ hγ hpos
      hγmax Fosc (centeredProfileZero_of_inactive b hDepth hS hInactive)).trans hm).trans_eq ?_
    rw [← pow_mul, Nat.mul_comm lossPower 2]
  have hMeanNorm : N 1 Fmean ≤ (count * levelConstant) * D ^ (6 * lossPower) * freq ^ (-5 / 2 : ℝ) := by
    refine ((b.velocityProfileSums_of_actualLevels hDepth 1 hf hLoss hLevelC ht₀ htT γ hγ hpos
      (hLevels 1 (by decide))).2.2).trans_eq ?_
    rw [← pow_mul, Nat.mul_comm lossPower 6]
  refine ⟨hAosc, hAmean, ?_, ?_⟩
  · intro t ht
    rw [(b.phaseMean_phaseOscillation_pullback_zero_fun ht).2]
    exact coframeApplied_scaledJets 2 (hCoefficient 2) hD hfpos hC Fosc
      (by positivity : 0 ≤ 2 * count * levelConstant) hOscNorm ht
  · intro t ht
    rw [(b.phaseMean_phaseOscillation_pullback_zero_fun ht).1]
    exact coframeApplied_scaledJets 1 (hCoefficient 1) hD hfpos hC Fmean
      (mul_nonneg hcount hLevelC) hMeanNorm ht

set_option maxHeartbeats 3500000 in
/-- Two oscillatory orders and one mean order, measured on the very same
selected hierarchy, give the exact jet fields needed by the cutoff flow. -/
theorem pulledBackProfileJetBounds_of_actualLevels
    {d : parent.OnSlab hT k} {depth a lossPower : ℕ} {D ℓ h freq next : ℝ} {C : ℕ → ℝ}
    (cap : InductiveEulerStage.StageCoefficientCaps d a D ℓ h freq C)
    (hD : 1 ≤ D) (hC : ∀ j, 0 ≤ C j) (hf : 1 ≤ freq) (hNext : freq ≤ next)
    (b : PhysicalApproximationData d.geometry parent.pressure depth)
    (props : PhysicalApproximationProperties b) (hDepth : 2 ≤ depth)
    {Λ : ℝ} {ψ : Vec3 → ℝ} (cutoff : TruncatedChildStage T Λ ψ b.velocity b.residual)
    {cutoffC cutoffK levelConstant : ℝ}
    (hCutoff : cutoff.CutoffBounds (b.potential props) depth cutoffC cutoffK)
    (hTail : ∀ t ∈ I, cutoffK * cutoff.truncationError depth t ≤ next ^ (-5 : ℝ))
    (hLevelC : 0 ≤ levelConstant)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {S : Set Vec3} (hS : IsClosed S)
    (hInactive : b.leading.Inactive t₀ S)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγmax : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hLevels : ∀ m ≤ 2, ∀ j ∈ Finset.Icc 1 depth, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles depth b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ℓ h hT ht₀ htT γ hγ hpos) freq (D ^ lossPower) levelConstant m j) :
    let B := profileFlowJetConstant C depth levelConstant
    0 ≤ B ∧ cutoff.PulledBackProfileJetBounds parent.flow b.profileVelocity
      freq ℓ h B D (profileFlowJetPower lossPower) := by
  let power := profileFlowJetPower lossPower
  let Aosc := profileFlowOscillationCost C depth levelConstant
  let Amean := profileFlowMeanCost C depth levelConstant
  let B := profileFlowJetConstant C depth levelConstant
  let F := b.profiles.velocity depth
  have hfpos : 0 < freq := zero_lt_one.trans_le hf
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hDepth₁ : 1 ≤ depth := by omega
  have hCoefficient (m : ℕ) := inverseCoframe_unweighted_le_of_parent (h := h)
    d.geometry cap.label_pos.le hD cap.label_scale hC m cap.coframeSmooth cap.rawCoframe
  obtain ⟨hAosc, hAmean, hoscs, hmeans⟩ := uncutPullbackProfileJetBounds_of_actualLevels
    hCoefficient hD hC hf b hDepth₁ hLevelC ht₀ htT hS hInactive γ hγ hpos hγmax hLevels
  have hB : 0 ≤ B := add_nonneg (add_nonneg hAosc hAmean) (add_nonneg zero_le_one (hC 1))
  have hOscPow : 2 * lossPower + 1 ≤ power := by dsimp [power, profileFlowJetPower]; omega
  have hMeanPow : 6 * lossPower + 1 ≤ power := by dsimp [power, profileFlowJetPower]; omega
  have hTailPow : 8 ≤ power := by dsimp [power, profileFlowJetPower]; omega
  have hAoscB : Aosc ≤ B :=
    (le_add_of_nonneg_right hAmean).trans (le_add_of_nonneg_right (add_nonneg zero_le_one (hC 1)))
  have hOsc (t : ℝ) (ht : t ∈ I) : PhaseJetBound 2 (B * D ^ power * freq ^ (-5 / 4 : ℝ))
      (scaledPhaseProfile ℓ h (fun x => phaseOscillation
        (fun r => ChildFlow.pullbackField parent.flow b.profileVelocity 0 t (x,r)))) := by
    intro j hj x
    exact (hoscs t ht j hj x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hAoscB (pow_le_pow_right₀ hD hOscPow) (pow_nonneg hD₀ _) hB) (by positivity))
  have hMean (t : ℝ) (ht : t ∈ I) : PhaseJetBound 1 (Amean * D ^ power * freq ^ (-5 / 2 : ℝ))
      (scaledPhaseProfile ℓ h (fun x _ => phaseMean
        (fun r => ChildFlow.pullbackField parent.flow b.profileVelocity 0 t (x,r)))) := by
    intro j hj x
    exact (hmeans t ht j hj x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hMeanPow) hAmean) (by positivity))
  have hε : next ^ (-5 : ℝ) ≤ freq ^ (-5 / 2 : ℝ) := by
    calc
      _ ≤ freq ^ (-5 : ℝ) := by
        rw [show (-5 : ℝ) = -(5 : ℝ) by ring, Real.rpow_neg (hfpos.le.trans hNext), Real.rpow_neg hfpos.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hfpos _) (Real.rpow_le_rpow hfpos.le hNext (by norm_num))
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hf (by norm_num)
  have hBudget : Amean * D ^ power * freq ^ (-5 / 2 : ℝ) +
      max D (D * D + C 1 * D ^ (8 : ℕ)) * next ^ (-5 : ℝ) ≤ B * D ^ power * freq ^ (-5 / 2 : ℝ) := by
    have hc₁ : 0 ≤ 1 + C 1 := add_nonneg zero_le_one (hC 1)
    have hTailCoef : max D (D * D + C 1 * D ^ (8 : ℕ)) ≤ (1 + C 1) * D ^ power :=
      (cap.cutoffTailCoframeBudget hD (hC 1)).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hD hTailPow) hc₁)
    calc
      _ ≤ Amean * D ^ power * freq ^ (-5 / 2 : ℝ) + (1 + C 1) * D ^ power * freq ^ (-5 / 2 : ℝ) :=
        add_le_add le_rfl (mul_le_mul hTailCoef hε (Real.rpow_nonneg (hfpos.le.trans hNext) _)
          (mul_nonneg hc₁ (pow_nonneg hD₀ _)))
      _ = (Amean + (1 + C 1)) * D ^ power * freq ^ (-5 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (add_le_add (le_add_of_nonneg_left hAosc) le_rfl) (pow_nonneg hD₀ _)) (by positivity)
  have hW : ContDiffOn ℝ ∞ (Function.uncurry fun t => Function.uncurry (b.profileVelocity t))
      (Icc 0 T ×ˢ (univ : Set ChildFlow.PhaseState)) :=
    HierarchySmoothProfile.smooth F.val.val
  exact ⟨hB, TruncatedChildStage.PulledBackProfileJetBounds.of_uncut cutoff hCutoff hDepth hT
    d.deformationOn.flow d.smooth_velocity (fun t _ => parent.periodic_velocity t)
    props.velocity_smooth hW (by rw [abs_of_pos cap.label_pos]; exact cap.label_le_one)
    cap.deformation cap.coframeDerivative hTail hOsc hMean hBudget⟩

end HierarchyTwistedProfile.PhysicalApproximationData

end

end TorusEuler
