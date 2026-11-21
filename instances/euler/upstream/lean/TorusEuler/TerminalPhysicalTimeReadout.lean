import TorusEuler.TerminalMaterialGraphBounds
import TorusEuler.TerminalTimeJetNorms
import TorusEuler.TerminalHierarchyPhaseTime
import TorusEuler.HierarchyPhysicalVelocityBounds

/-! Mixed-time graph readout for the actual mean, oscillation, and residual
of a selected physical approximation. -/

open Set Filter
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
  {hT : 0 < T} {g : ParentGeometry hT U X k} {depth : ℕ}

local notation "I" => Icc (0 : ℝ) T
local notation "Slab" => Set.prod I (univ : Set Vec3)
local notation "InvFlow" => (fun r => X r 0)
local notation "Jet(" i "," f ")" => slabTimeJet 0 T i f

namespace PhysicalApproximationData

variable (b : PhysicalApproximationData g p depth)

local notation "ProfileMean" => b.operators.average (b.profiles.velocity depth)
local notation "ProfileOscillation" => b.profiles.velocity depth - ProfileMean
local notation "ProfileRemainder" => b.operators.remainder b.profiles depth
local notation "ProfileSwitch" => b.leading.leadingSwitch + b.leading.completionSwitch

/-- The exact selected oscillatory profile vanishes before activation in all
label and phase variables. -/
theorem terminal_oscillationProfile_zero_before (hDepth : 1 ≤ depth)
    {t₀ : ℝ} {S : Set Vec3} (hS : IsClosed S) (hInactive : b.leading.Inactive t₀ S)
    {t : ℝ} (ht : t ∈ I) (ht₀ : t < t₀) (x : Vec3 × ℝ) :
    (ProfileOscillation).val.val.val (t,x) = 0 := by
  obtain ⟨hSupport, _, _⟩ := physicalConstruct_support_and_tail_on_inactive hT b.time_le_one hS
    g.inverse g.strain g.covector g.mean g.oscillation hDepth
    b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output
    hInactive.velocity hInactive.pressure hInactive.completionSwitch
  have heq : ProfileOscillation = ∑ i ∈ Finset.Icc 1 depth, (b.profiles.V i + b.profiles.C i) :=
    b.solvers.construct_velocity_sub_average depth b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output
  rw [heq]
  let ev : HierarchyTwistedProfile T k Vec3 →ₗ[ℝ] Vec3 :=
    ⟨⟨fun f => f.val.val.val (t,x), fun _ _ => rfl⟩, fun _ _ => rfl⟩
  change ev (∑ i ∈ Finset.Icc 1 depth, (b.profiles.V i + b.profiles.C i)) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hx : (t,x) ∈ hierarchyInactiveRegion T t₀ S := ⟨⟨ht, mem_univ _⟩, Or.inl ht₀⟩
  change (b.profiles.V i).val.val.val (t,x) + (b.profiles.C i).val.val.val (t,x) = 0
  have hv : (b.profiles.V i).val.val.val (t,x) = 0 := (hSupport i).1 hx
  have hc : (b.profiles.C i).val.val.val (t,x) = 0 := (hSupport i).2.1 hx
  rw [hv, hc, zero_add]

/-- Time jets preserve vanishing outside any closed time set. -/
theorem timeJet_zero_outside_closed (f : HierarchyTwistedProfile T k Vec3) {S : Set ℝ}
    (hS : IsClosed S) (hZero : ∀ r ∈ I, r ∉ S → ∀ x : Vec3 × ℝ, f.val.val.val (r,x) = 0)
    (i : ℕ) {t : ℝ} (ht : t ∈ I) (hnot : t ∉ S) (x : Vec3 × ℝ) :
    (timeJet hT i f).val.val.val (t,x) = 0 := by
  rw [timeJet_apply hT i f ht]
  have hEq : (fun r => f.val.val.val (r,x)) =ᶠ[nhdsWithin t I] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (hS.isOpen_compl.mem_nhds hnot)] with r hr hS'
    exact hZero r hr hS' x
  rw [hEq.iteratedDerivWithin_eq (hZero t ht hnot x)]
  simp

/-- The Eulerian velocity time jet splits into the actual parent time jet
and the two graph corrections. -/
theorem terminal_slabTimeJet_velocity_eq
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) Slab)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (i : ℕ) {t : ℝ} (ht : t ∈ I) :
    Jet(i,b.velocity) t = Jet(i,U) t + Jet(i,b.oscillation) t + Jet(i,b.meanCorrection) t := by
  have hA := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hOsc : ContDiffOn ℝ ∞ (Function.uncurry b.oscillation) Slab :=
    HierarchySmoothProfile.contDiffOn_graphRead (A := InvFlow) k (ProfileOscillation).val.val hA
  have hMean : ContDiffOn ℝ ∞ (Function.uncurry b.meanCorrection) Slab :=
    HierarchySmoothProfile.contDiffOn_graphRead (A := InvFlow) k (ProfileMean).val.val hA
  funext x
  have heq : EqOn (fun r => b.velocity r x)
      (((fun r => U r x) + fun r => b.oscillation r x) + fun r => b.meanCorrection r x) I := by
    intro r _
    exact congrFun (congrFun b.velocity_eq_parent_add_oscillation_add_mean r) x
  change iteratedDerivWithin i (fun r => b.velocity r x) I t = _
  rw [iteratedDerivWithin_congr heq ht]
  have hSum : ContDiffWithinAt ℝ i ((fun r => U r x) + fun r => b.oscillation r x) I t :=
    ((terminal_contDiffOn_timeSlice hU x).add (terminal_contDiffOn_timeSlice hOsc x)).of_le (by simp) t ht
  rw [iteratedDerivWithin_add ht (uniqueDiffOn_Icc hT) hSum
    ((terminal_contDiffOn_timeSlice hMean x).of_le (by simp) t ht),
    iteratedDerivWithin_add ht (uniqueDiffOn_Icc hT)
      ((terminal_contDiffOn_timeSlice hU x).of_le (by simp) t ht)
      ((terminal_contDiffOn_timeSlice hOsc x).of_le (by simp) t ht)]
  rfl

/-- The residual time jet splits into the exact tail and both switch forces. -/
theorem terminal_slabTimeJet_residual_eq
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) Slab)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (i : ℕ) {t : ℝ} (ht : t ∈ I) :
    Jet(i,b.residual) t =
      Jet(i,graphRead InvFlow ProfileRemainder) t + Jet(i,graphRead InvFlow ProfileSwitch) t := by
  let tail := graphRead InvFlow ProfileRemainder
  let switch := graphRead InvFlow ProfileSwitch
  have hA := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hTail : ContDiffOn ℝ ∞ (Function.uncurry tail) Slab :=
    HierarchySmoothProfile.contDiffOn_graphRead (A := InvFlow) k (ProfileRemainder).val.val hA
  have hSwitch : ContDiffOn ℝ ∞ (Function.uncurry switch) Slab :=
    HierarchySmoothProfile.contDiffOn_graphRead (A := InvFlow) k (ProfileSwitch).val.val hA
  funext x
  have hEq : EqOn (fun r => b.residual r x) ((fun r => tail r x) + fun r => switch r x) I :=
    fun r _ => congrFun (b.residual_eq_graph_tail_add_switch r) x
  change iteratedDerivWithin i (fun r => b.residual r x) I t = _
  rw [iteratedDerivWithin_congr hEq ht, iteratedDerivWithin_add ht (uniqueDiffOn_Icc hT)
    ((terminal_contDiffOn_timeSlice hTail x).of_le (by simp) t ht)
    ((terminal_contDiffOn_timeSlice hSwitch x).of_le (by simp) t ht)]
  rfl

/-- Geometric spatial bounds on all material time jets of a fixed graph. -/
abbrev GeometricGraphJet (hT : 0 < T) (A : Velocity) (f : HierarchyTwistedProfile T k Vec3)
    (N q : ℕ) (C B : ℝ) : Prop :=
  ∀ j ≤ q, ∀ m, j + m ≤ N → ∀ t ∈ I, ∀ x : Vec3,
    ‖iteratedFDeriv ℝ m (graphRead A (timeJet hT j f) t) x‖ ≤ C * B ^ m

set_option maxHeartbeats 1800000 in
/-- Read the differentiated velocity, mean, and residual of the same exact
physical approximation. The phase-independent graph uses its own smaller
spatial rate, while the oscillatory graphs share the carrier rate. -/
theorem physicalTimeReadout_of_graphJets
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) Slab)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    {N q : ℕ} {Bmean Bwave D Cmean Cosc Ctail Cswitch : ℝ}
    (hBM : 1 ≤ Bmean) (hBW : Bmean ≤ Bwave) (hD : 0 ≤ D)
    (hCM : 0 ≤ Cmean) (hCO : 0 ≤ Cosc) (hCT : 0 ≤ Ctail) (hCS : 0 ≤ Cswitch)
    (hParent : ∀ i ≤ q, ∀ m ≤ N, ∀ t ∈ I, ∀ x,
      ‖iteratedFDeriv ℝ m (Jet(i,U) t) x‖ ≤ D * Bmean ^ m)
    (hMean : GeometricGraphJet hT InvFlow ProfileMean N q Cmean Bmean)
    (hOsc : GeometricGraphJet hT InvFlow ProfileOscillation N q Cosc Bwave)
    (hTail : GeometricGraphJet hT InvFlow ProfileRemainder N q Ctail Bwave)
    (hSwitch : GeometricGraphJet hT InvFlow ProfileSwitch N q Cswitch Bwave)
    {i m : ℕ} (hi : i ≤ q) {t : ℝ} (ht : t ∈ I) :
    let K := (1 + (2 : ℝ) ^ (N+q) * D) ^ i
    (i + m + 1 ≤ N →
      (SpatialHolderHalf m (Jet(i,b.meanCorrection) t) ∧
        spatialHolderHalfNorm m (Jet(i,b.meanCorrection) t) ≤
          (3 * (m+1) : ℝ) * (K * Cmean * Bmean ^ (m+1+i))) ∧
      (SpatialHolderHalf m (Jet(i,b.velocity) t) ∧
        spatialHolderHalfNorm m (Jet(i,b.velocity) t) ≤
          (3 * (m+1) : ℝ) * (K * (D + Cosc + Cmean) * Bwave ^ (m+1+i)))) ∧
    (i + 2 ≤ N → SpatialHolderHalf 1 (Jet(i,b.residual) t) ∧
      spatialHolderHalfNorm 1 (Jet(i,b.residual) t) ≤
        6 * (K * (Ctail + Cswitch) * Bwave ^ (2+i))) := by
  let K := (1 + (2 : ℝ) ^ (N+q) * D) ^ i
  have hK : 1 ≤ K := one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hBW₁ : 1 ≤ Bwave := hBM.trans hBW
  have hBM₀ : 0 ≤ Bmean := zero_le_one.trans hBM
  have hM (m : ℕ) (hm : i + m + 1 ≤ N) :=
    eulerianTimeJet_graphRead_holderHalf_le hT hX hU hper ProfileMean hBM hCM hD
      (fun l hl => hParent l hl.le) hMean hi hm ht
  have hParentWave (j : ℕ) (hj : j ≤ q) (n : ℕ) (hn : n ≤ N) (s : ℝ) (hs : s ∈ I) (x : Vec3) :
      ‖iteratedFDeriv ℝ n (Jet(j,U) s) x‖ ≤ D * Bwave ^ n :=
    (hParent j hj n hn s hs x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBM₀ hBW _) hD)
  constructor
  · intro hm
    have hMeanJet := hM m hm
    refine ⟨hMeanJet, ?_⟩
    have hOscJet := eulerianTimeJet_graphRead_holderHalf_le hT hX hU hper ProfileOscillation hBW₁
      hCO hD (fun l hl => hParentWave l hl.le) hOsc hi hm ht
    have hUjet := spatialHolderHalfNorm_le_of_uniformJets (m := m)
      (slabTimeJet_slice_smooth hT hU i ht) (show 0 ≤ D * Bwave ^ (m+1+i) by positivity)
      (fun r hr x => (hParentWave i hi r (by omega) t ht x).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hBW₁ (by omega)) hD))
    rw [b.terminal_slabTimeJet_velocity_eq hX hU hper i ht]
    have hUO := spatialHolderHalf_add_exact hUjet.1 hOscJet.1
    have hV := spatialHolderHalf_add_exact hUO.1 hMeanJet.1
    refine ⟨hV.1, hV.2.trans ?_⟩
    have hMeanWave : (3 * (m+1) : ℝ) * (K * Cmean * Bmean ^ (m+1+i)) ≤
        (3 * (m+1) : ℝ) * (K * Cmean * Bwave ^ (m+1+i)) := by gcongr
    have hUWave : (3 * (m+1) : ℝ) * (D * Bwave ^ (m+1+i)) ≤
        (3 * (m+1) : ℝ) * (K * D * Bwave ^ (m+1+i)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hD hK)
        (by positivity)) (by positivity)
    exact (add_le_add (hUO.2.trans (add_le_add (hUjet.2.trans hUWave) hOscJet.2))
      (hMeanJet.2.trans hMeanWave)).trans_eq (by ring)
  · intro hm
    have hTailJet := eulerianTimeJet_graphRead_holderHalf_le hT hX hU hper ProfileRemainder hBW₁
      hCT hD (fun l hl => hParentWave l hl.le) hTail hi (m := 1) (by omega) ht
    have hSwitchJet := eulerianTimeJet_graphRead_holderHalf_le hT hX hU hper ProfileSwitch hBW₁
      hCS hD (fun l hl => hParentWave l hl.le) hSwitch hi (m := 1) (by omega) ht
    rw [b.terminal_slabTimeJet_residual_eq hX hU hper i ht]
    have hsum := spatialHolderHalf_add_exact hTailJet.1 hSwitchJet.1
    exact ⟨hsum.1, hsum.2.trans ((add_le_add hTailJet.2 hSwitchJet.2).trans_eq (by ring))⟩

/-- The maximum extraction cost from the factorial-weighted time seminorm. -/
def terminalTimeExtraction (T : ℝ) (q : ℕ) : ℝ := (q.factorial : ℝ) * T⁻¹ ^ q

private theorem extract_terminalTimeJetSeminorm (hT : 0 < T) (hT₁ : T ≤ 1)
    {f : HierarchyTwistedProfile T k Vec3} (S : Seminorm ℝ (HierarchyTwistedProfile T k Vec3))
    {q i : ℕ} (hi : i ≤ q) {M : ℝ} (hM : timeJetSeminorm hT q S f ≤ M) :
    S (timeJet hT i f) ≤ terminalTimeExtraction T q * M := by
  have hInv : 1 ≤ T⁻¹ := (one_le_inv₀ hT).2 hT₁
  have hFac : (i.factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.monotone_factorial hi
  have hFactor : (i.factorial : ℝ) * T⁻¹ ^ i ≤ terminalTimeExtraction T q :=
    mul_le_mul hFac (pow_le_pow_right₀ hInv hi) (by positivity) (Nat.cast_nonneg _)
  exact (norm_timeJet_le hT hi S f).trans (mul_le_mul hFactor hM (apply_nonneg _ _) (by
    unfold terminalTimeExtraction
    positivity))

set_option maxHeartbeats 1700000 in
/-- A weighted material bound on a supported profile loses only the
maximum amplitude on that support. Outside the support every time jet is zero. -/
theorem geometricGraphJet_of_weightedSeminorms_closedSupport
    (hT : 0 < T) (f : HierarchyTwistedProfile T k Vec3)
    {t₀ ℓ h D freq L M α Cγ : ℝ} {N q a : ℕ} {S : Set ℝ}
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hSupp : IsClosed S) (hActive : S ⊆ Icc t₀ T)
    (hZero : ∀ t ∈ I, t ∉ S → ∀ x : Vec3 × ℝ, f.val.val.val (t,x) = 0)
    (hγCap : ∀ t ∈ S, γ t ≤ Cγ) (hCγ : 0 ≤ Cγ)
    (hℓ : 0 < ℓ) (hh : 0 < h) (hD : 1 ≤ D) (hf : 1 ≤ freq)
    (hL : 1 ≤ L) (hM : 0 ≤ M) (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1/2 : ℝ))
    (hCarrier : ‖k‖ ≤ D * freq)
    {A : Velocity} {B : ℝ → Vec3 → Vec3 →L[ℝ] Vec3}
    (hA : ∀ t ∈ I, ContDiff ℝ ∞ (A t))
    (hB : ∀ t ∈ I, ∀ x, B t (A t x) = fderiv ℝ (A t) x)
    (hBreg : ∀ t ∈ I, ContDiff ℝ ∞ (B t))
    (hCoeff : ∀ t ∈ I, ∀ m ≤ N, ∀ x, ℓ ^ m * ‖iteratedFDeriv ℝ m (B t) x‖ ≤ L * D)
    (hNorm : ∀ i ≤ q, ∀ m ≤ N, amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hpos
      (timeJet hT i f) ≤ M * freq ^ α)
    (hWave : D ^ (max a 1 + 1) * freq ^ (3/2 : ℝ) ≤ freq ^ 2) :
    GeometricGraphJet hT A f N q (materialGraphFactor (2*L) N * M * (Cγ * freq ^ α)) (freq ^ 2) := by
  intro j hj m hjm t ht x
  have hScale0 : 0 ≤ D ^ (max a 1 + 1) * freq ^ (3/2 : ℝ) := by positivity
  have hL₀ := zero_le_one.trans hL
  have hD₀ := zero_le_one.trans hD
  have hf₀ := zero_le_one.trans hf
  have hfα := Real.rpow_nonneg hf₀ α
  by_cases htS : t ∈ S
  · have hγ₀ := (hpos t (hActive htS)).le
    have hjets := norm_iteratedFDeriv_materialGraphRead_weighted_le hT ht₀ htT γ hγ hpos f
      (p := 0) (hActive htS) hℓ hh hD hf hL hM hLabel hWidth hCarrier
      (hA t ht) (hB t ht) (hBreg t ht) (hCoeff t ht)
      (fun i hi n hn => by simpa only [pow_zero, mul_one] using hNorm i hi n hn)
      hj m (by omega) x
    simp only [pow_zero, mul_one] at hjets
    refine hjets.trans ?_
    change (materialGraphFactor (2*L) N * M * (γ t * freq ^ α)) * _ ≤ _
    exact mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hγCap t htS) hfα)
      (by unfold materialGraphFactor; positivity)) (pow_le_pow_left₀ hScale0 hWave _)
      (pow_nonneg hScale0 _) (by unfold materialGraphFactor; positivity)
  · have hEq : graphRead A (timeJet hT j f) t = 0 := by
      funext y
      exact timeJet_zero_outside_closed f hSupp hZero j ht htS _
    rw [hEq]
    change ‖iteratedFDeriv ℝ m (fun _ : Vec3 => (0 : Vec3)) x‖ ≤ _
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    unfold materialGraphFactor
    positivity

set_option maxHeartbeats 2700000 in
/-- The actual factorial time norms of the selected finite hierarchy give
the four geometric graph bounds needed by the mixed-time readout. -/
theorem geometricGraphJets_of_physicalTimeNorms
    (hDepth : 1 ≤ depth)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) Slab)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    {t₀ ℓ h D freq L M O R W α Γ : ℝ} {N q a : ℕ}
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγone : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    {env : Set Vec3} (hClosed : IsClosed env) (hInactive : b.leading.Inactive t₀ env)
    {switchSlab : Set ℝ} (hSwitchClosed : IsClosed switchSlab) (hSwitchActive : switchSlab ⊆ Icc t₀ T)
    (hSwitchZero : ∀ t ∈ I, t ∉ switchSlab → ∀ x : Vec3 × ℝ, (ProfileSwitch).val.val.val (t,x) = 0)
    (hΓ : 0 ≤ Γ) (hΓcap : ∀ t ∈ switchSlab, γ t ≤ Γ)
    (hℓ : 0 < ℓ) (hh : 0 < h) (hD : 1 ≤ D) (hf : 1 ≤ freq) (hL : 1 ≤ L)
    (hM : 0 ≤ M) (hO : 0 ≤ O) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1/2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hCoeff : ∀ t ∈ I, ∀ m ≤ N, ∀ x, ℓ ^ m *
      ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ (X t 0) (X 0 t y)) x‖ ≤ L * D)
    (hMean : timeJetSeminorm hT q (unweightedSeminorm False ℓ h N hT) ProfileMean ≤
      M * freq ^ (-5/2 : ℝ))
    (hOsc : timeJetSeminorm hT q (amplitudeSeminorm False ℓ h N hT ht₀ htT γ hγ hpos)
      ProfileOscillation ≤ O * freq ^ (-5/4 : ℝ))
    (hTail : timeJetSeminorm hT q (unweightedSeminorm False ℓ h N hT) ProfileRemainder ≤ R * freq ^ α)
    (hSwitch : timeJetSeminorm hT q (amplitudeSeminorm False ℓ h N hT ht₀ htT γ hγ hpos) ProfileSwitch ≤
      W * freq ^ (-5/4 : ℝ))
    (hWave : D ^ (max a 1 + 1) * freq ^ (3/2 : ℝ) ≤ freq ^ 2) :
    let ext := terminalTimeExtraction T q
    GeometricGraphJet hT InvFlow ProfileMean N q
        (materialGraphFactor L N * (ext * M) * freq ^ (-5/2 : ℝ)) (D ^ (a+1)) ∧
      GeometricGraphJet hT InvFlow ProfileOscillation N q
        (materialGraphFactor (2*L) N * (ext * O) * freq ^ (-5/4 : ℝ)) (freq ^ 2) ∧
      GeometricGraphJet hT InvFlow ProfileRemainder N q
        (materialGraphFactor (2*L) N * (ext * R) * freq ^ α) (freq ^ 2) ∧
      GeometricGraphJet hT InvFlow ProfileSwitch N q
        (materialGraphFactor (2*L) N * (ext * W) * (Γ * freq ^ (-5/4 : ℝ))) (freq ^ 2) := by
  let ext := terminalTimeExtraction T q
  have hExt : 0 ≤ ext := by dsimp [ext, terminalTimeExtraction]; positivity
  let B (t : ℝ) (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
  have hGeom (t : ℝ) (ht : t ∈ I) : ContDiff ℝ ∞ (InvFlow t) ∧
      (∀ x, B t (InvFlow t x) = fderiv ℝ (InvFlow t) x) ∧ ContDiff ℝ ∞ (B t) :=
    graphCoframe_geometry hT hX hU hper ht
  have hUnweighted (f : HierarchyTwistedProfile T k Vec3) {C β : ℝ}
      (hNorm : timeJetSeminorm hT q (unweightedSeminorm False ℓ h N hT) f ≤ C * freq ^ β) :
      ∀ j ≤ q, ∀ m ≤ N, unweightedSeminorm False ℓ h m hT (timeJet hT j f) ≤
        (ext*C) * freq ^ β := by
    intro j hj m hm
    refine (unweightedSeminorm_mono_order False ℓ h hm hT _).trans ?_
    simpa only [mul_assoc] using extract_terminalTimeJetSeminorm hT b.time_le_one
      (unweightedSeminorm False ℓ h N hT) hj hNorm
  have hWeighted (f : HierarchyTwistedProfile T k Vec3) {C β : ℝ}
      (hNorm : timeJetSeminorm hT q (amplitudeSeminorm False ℓ h N hT ht₀ htT γ hγ hpos) f ≤ C * freq ^ β) :
      ∀ j ≤ q, ∀ m ≤ N, amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hpos (timeJet hT j f) ≤
        (ext*C) * freq ^ β := by
    intro j hj m hm
    refine (amplitudeSeminorm_mono_order False ℓ h hm hT ht₀ htT γ hγ hpos _).trans ?_
    simpa only [mul_assoc] using extract_terminalTimeJetSeminorm hT b.time_le_one
      (amplitudeSeminorm False ℓ h N hT ht₀ htT γ hγ hpos) hj hNorm
  have hOscZero (t : ℝ) (ht : t ∈ I) (hNot : t ∉ Icc t₀ T) (x : Vec3 × ℝ) :
      (ProfileOscillation).val.val.val (t,x) = 0 :=
    b.terminal_oscillationProfile_zero_before hDepth hClosed hInactive ht
      (lt_of_not_ge fun h => hNot ⟨h,ht.2⟩) x
  have hOscRate := geometricGraphJet_of_weightedSeminorms_closedSupport (q := q) (N := N)
    hT ProfileOscillation ht₀ htT γ hγ hpos isClosed_Icc Subset.rfl hOscZero hγone zero_le_one
    hℓ hh hD hf hL (mul_nonneg hExt hO) hLabel hWidth hCarrier
    (fun t ht => (hGeom t ht).1) (fun t ht => (hGeom t ht).2.1) (fun t ht => (hGeom t ht).2.2)
    hCoeff (hWeighted _ hOsc) hWave
  have hTailCor : ContinuousOn (fun _ : ℝ => (1 : ℝ)) I := continuousOn_const
  have hTailPos : ∀ t ∈ I, (0 : ℝ) < 1 := fun _ _ => zero_lt_one
  have hTailWeight (j : ℕ) (hj : j ≤ q) (m : ℕ) (hm : m ≤ N) :
      amplitudeSeminorm False ℓ h m hT le_rfl hT.le (fun _ => 1) hTailCor hTailPos
        (timeJet hT j ProfileRemainder) ≤ (ext*R) * freq ^ α := by
    simpa only [amplitudeSeminorm_apply, unweightedSeminorm, boundedWeightSeminorm_apply, inv_one] using
      hUnweighted _ hTail j hj m hm
  have hTailRate := geometricGraphJet_of_weightedSeminorms_closedSupport (q := q) (N := N)
    hT ProfileRemainder le_rfl hT.le (fun _ => 1) hTailCor hTailPos isClosed_Icc Subset.rfl
    (fun _ ht hNot _ => (hNot ht).elim) (fun _ _ => le_rfl) zero_le_one
    hℓ hh hD hf hL (mul_nonneg hExt hR) hLabel hWidth hCarrier
    (fun t ht => (hGeom t ht).1) (fun t ht => (hGeom t ht).2.1) (fun t ht => (hGeom t ht).2.2)
    hCoeff hTailWeight hWave
  have hSwitchRate := geometricGraphJet_of_weightedSeminorms_closedSupport (q := q) (N := N)
    hT ProfileSwitch ht₀ htT γ hγ hpos hSwitchClosed hSwitchActive hSwitchZero hΓcap hΓ
    hℓ hh hD hf hL (mul_nonneg hExt hW) hLabel hWidth hCarrier
    (fun t ht => (hGeom t ht).1) (fun t ht => (hGeom t ht).2.1) (fun t ht => (hGeom t ht).2.2)
    hCoeff (hWeighted _ hSwitch) hWave
  have hMeanRate : GeometricGraphJet hT InvFlow ProfileMean N q
      (materialGraphFactor L N * (ext*M) * freq ^ (-5/2 : ℝ)) (D ^ (a+1)) := by
    intro j hj m hm t ht x
    have hPhase := (average_is_mean hT g.inverse g.strain g.covector (b.profiles.velocity depth)).1
    simpa only [pow_zero, mul_one, materialGraphFactor] using norm_iteratedFDeriv_materialGraphRead_mean_le hT
      ProfileMean hPhase (a := a) (p := 0) ht hℓ hD (zero_lt_one.trans_le hf) hL
      (mul_nonneg hExt hM) hLabel (hGeom t ht).1 (hGeom t ht).2.1 (hGeom t ht).2.2 (hCoeff t ht)
      (fun i hi n hn => by simpa only [pow_zero, mul_one] using hUnweighted _ hMean i hi n hn)
      hj m (by omega) x
  exact ⟨hMeanRate, by simpa only [one_mul] using hOscRate, by simpa only [one_mul] using hTailRate, hSwitchRate⟩

end PhysicalApproximationData

/-- The prescribed depth turns the profile tail's rate into the fourth
inverse power of the following frequency. -/
theorem terminalDepthTail_rpow {freq next : ℝ} (hf : 0 < freq) {depth exponent : ℕ}
    (hDepth : depth = 6 * exponent) (hNext : next = freq ^ exponent) :
    freq ^ hierarchyOscExponent (depth + 1) =
      freq ^ (-5/4 : ℝ) * next ^ (-4 : ℝ) := by
  rw [hDepth, hNext, hierarchyOscExponent, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    Nat.cast_mul, Nat.cast_ofNat, ← Real.rpow_natCast_mul hf.le]
  rw [← Real.rpow_add hf]
  congr 1
  ring

/-- A half-power of frequency absorbs the label part of one oscillatory
spatial derivative. -/
theorem terminalWaveSpatialRate_le {D freq : ℝ} {a : ℕ} (hf : 0 < freq)
    (hLabel : D ^ (max a 1 + 1) ≤ freq ^ (1/2 : ℝ)) :
    D ^ (max a 1 + 1) * freq ^ (3/2 : ℝ) ≤ freq ^ (2 : ℕ) := by
  refine (mul_le_mul_of_nonneg_right hLabel (Real.rpow_nonneg hf.le _)).trans_eq ?_
  rw [← Real.rpow_add hf, show (1/2 : ℝ) + 3/2 = (2 : ℕ) by norm_num, Real.rpow_natCast]

/-- The Eulerian time differentiation factor carries a fixed old-parent
power when the parent velocity jets have a fixed polynomial bound. -/
theorem terminalGraphTimeFactor_le_of_parent {μ C D : ℝ} {N q i A : ℕ}
    (hμ : 1 ≤ μ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hi : i ≤ q) (hBound : D ≤ C * μ ^ A) :
    (1 + (2 : ℝ) ^ (N+q) * D) ^ i ≤
      (1 + (2 : ℝ) ^ (N+q) * C) ^ q * μ ^ (A*q) := by
  have hOne : 1 ≤ (1 + (2 : ℝ) ^ (N+q) * C) * μ ^ A :=
    one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (by positivity)) (one_le_pow₀ hμ)
  have hBase : 1 + (2 : ℝ) ^ (N+q) * D ≤ (1 + (2 : ℝ) ^ (N+q) * C) * μ ^ A := by
    calc
      _ ≤ μ ^ A + (2 : ℝ) ^ (N+q) * (C * μ ^ A) :=
        add_le_add (one_le_pow₀ hμ) (mul_le_mul_of_nonneg_left hBound (by positivity))
      _ = _ := by ring
  calc
    _ ≤ ((1 + (2 : ℝ) ^ (N+q) * C) * μ ^ A) ^ i :=
      pow_le_pow_left₀ (by positivity) hBase _
    _ ≤ ((1 + (2 : ℝ) ^ (N+q) * C) * μ ^ A) ^ q := pow_le_pow_right₀ hOne hi
    _ = _ := by rw [mul_pow, ← pow_mul]

end

end TorusEuler.HierarchyTwistedProfile
