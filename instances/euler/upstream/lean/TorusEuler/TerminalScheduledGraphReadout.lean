import TorusEuler.TerminalScheduledGraphScalars
import TorusEuler.TerminalGraphAbsorption
import TorusEuler.TerminalScheduledParentJets
import TorusEuler.InductiveTerminalSwitchTime

/-! The actual later graphs with their single old-parent polynomial loss. -/

open Set Filter
open scoped ContDiff Topology

namespace TorusEuler.ScheduledEulerConstruction

open HierarchyTwistedProfile
open HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

set_option quotPrecheck false

variable {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (n : ℕ)

local notation "Tip" => c.construction.tip n
local notation "Input" => (c.selectedStep n).selected
local notation "Approx" => (c.selectedStep n).selected.approximation
local notation "Schild" => c.construction.slab (n+2)
local notation "μ" => P.frequency (n+1)
local notation "freq" => P.frequency (n+2)
local notation "next" => P.frequency (n+3)
local notation "depth" => P.stepDepth (n+1)
local notation "a" => c.radiusExponent
local notation "D" => μ ^ (9 : ℕ)
local notation "ell" => (c.selectedStep n).selected.radius
local notation "width" => (c.selectedStep n).selected.width
local notation "t₀" => (c.construction.tip n).nextActivation
local notation "I" => Icc (0 : ℝ) Schild
local notation "MeanProfile" => ((Approx).operators.average ((Approx).profiles.velocity depth))
local notation "OscProfile" => ((Approx).profiles.velocity depth - MeanProfile)
local notation "TailProfile" => ((Approx).operators.remainder (Approx).profiles depth)
local notation "SwitchProfile" => ((Approx).leading.leadingSwitch + (Approx).leading.completionSwitch)
local notation "gamma" => (Input).centerWeight

/-- A common Bernstein constant through the readout reserve. -/
def terminalGraphParentCost (C : ℕ → ℝ) (N : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (N+1), C j

theorem terminalGraphParentCost_ge_one (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) (N : ℕ) :
    1 ≤ terminalGraphParentCost C N :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hC j)

theorem le_terminalGraphParentCost (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) {m N : ℕ} (hm : m ≤ N) :
    C m ≤ terminalGraphParentCost C N := by
  have h := Finset.single_le_sum (f := C) (fun j _ => hC j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  exact h.trans (le_add_of_nonneg_left zero_le_one)

/-- The weighted mixed norms of the exact selected finite hierarchy and
of the two switch sources in the residual. Each coefficient carries the
same old-parent power. -/
def SelectedProfileGraphTimeBounds (q E : ℕ) (M O R W : ℝ) : Prop :=
  let N := depth + q + 1
  let hT := (Input).time_pos
  let h₀ := (Tip).next_activation_nonnegative
  let h₁ := (Input).launch_time_mem.2
  let U := timeJetSeminorm hT q (unweightedSeminorm False ell width N hT)
  let V := timeJetSeminorm hT q (amplitudeSeminorm False ell width N hT h₀ h₁
    gamma (Input).centerWeight_continuous (Input).centerWeight_pos)
  U MeanProfile ≤ (M * μ ^ E) * freq ^ (-5/2 : ℝ) ∧
    V OscProfile ≤ (O * μ ^ E) * freq ^ (-5/4 : ℝ) ∧
    U TailProfile ≤ (R * μ ^ E) * freq ^ hierarchyOscExponent (depth+1) ∧
    V SwitchProfile ≤ (W * μ ^ E) * freq ^ (-5/4 : ℝ)

set_option maxHeartbeats 1500000 in
/-- A uniform fixed-order coframe constant applies to every exact selected
stage on the common schedule. -/
theorem exists_scheduledGraphCoframeBounds :
    ∃ L : ℕ → ℝ, (∀ N, 1 ≤ L N) ∧
      ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P),
        7 ≤ c.radiusExponent → ∀ n N, let d := (c.selectedStep n).selected
        ∀ t ∈ Icc 0 (c.construction.slab (n+2)), ∀ j ≤ N, ∀ x,
          d.radius ^ j * ‖iteratedFDeriv ℝ j (fun y =>
            fderiv ℝ ((c.construction.tip n).parent.flow t 0)
              ((c.construction.tip n).parent.flow 0 t y)) x‖ ≤ L N * (P.frequency (n+1) ^ (9 : ℕ)) := by
  obtain ⟨C,hC,hCaps⟩ := InductiveEulerStage.exists_stageCoefficientCaps
  refine ⟨InductiveEulerStage.stageCoframeOrderConstant C,
    InductiveEulerStage.stageCoframeOrderConstant_ge_one C hC, ?_⟩
  intro P c ha n N d
  have hμ : 1 ≤ P.frequency (n+1) := one_le_two.trans d.parent_frequency_ge_two
  have hf : 0 < P.frequency (n+2) := zero_lt_one.trans_le d.child_frequency_ge_one
  exact (hCaps d.parent d.time_le_one hμ hf d.launch_time_mem d.label_launch_covector_norm
    c.radiusExponent ha).scaledCoframe N

set_option maxHeartbeats 3200000 in
/-- The actual factorial hierarchy and parent jet bounds on one selected
stage imply the two polynomial graph rows; the full scalar cost is read
from just one entry in the fixed-order schedule. -/
theorem polynomialTimeBounds_of_selectedProfileGraphTimeBounds
    {q B E : ℕ} {M O R W L : ℝ} {Kparent : ℕ → ℝ}
    (hBase : Real.exp 1 ≤ P.frequency 0)
    (hL : 1 ≤ L) (hKparent : ∀ m, 0 ≤ Kparent m)
    (hM : 0 ≤ M) (hO : 0 ≤ O) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hOldWave : D ^ (max a 1 + 1) ≤ freq ^ (1/2 : ℝ))
    (hCost : terminalGraphReadoutCost q (depth+q+1) L (terminalGraphParentCost Kparent (depth+q+1))
      M O R W ≤ μ)
    (hCoframe : ∀ t ∈ I, ∀ m ≤ depth+q+1, ∀ x, ell ^ m *
      ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ ((Tip).parent.flow t 0)
        ((Tip).parent.flow 0 t y)) x‖ ≤ L * D)
    (hParent : TerminalMixedJetBound 0 Schild q 5 μ (μ^B) Kparent (Tip).parent.velocity)
    (hEnvelope : ∀ t ∈ Icc t₀ (t₀ + 1 / (Input).window.physical.rate),
      gamma t ≤ Real.exp 3 * next ^ (-4 : ℝ))
    (hNorm : c.SelectedProfileGraphTimeBounds n q E M O R W) :
    c.PolynomialApproximationTimeBounds q (terminalGraphReadoutPower q B E) n ∧
      ∀ m ≤ depth, c.PolynomialMeanTimeBound q m
        (terminalGraphReadoutPower q B E + 9*(a+1)*(m+1+q)) n := by
  let d := Input
  let b := Approx
  let N := depth+q+1
  let Cparent := terminalGraphParentCost Kparent N
  let S := Icc t₀ (min Schild (t₀ + 1 / d.window.physical.rate))
  let Γ := Real.exp 3 * next ^ (-4 : ℝ)
  have hFrame : Schild = P.slab (n+2) t₀ := rfl
  have hμ : 1 ≤ μ := one_le_two.trans d.parent_frequency_ge_two
  have hμ₀ : 0 ≤ μ := zero_le_one.trans hμ
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hf : 1 ≤ freq := d.child_frequency_ge_one
  have hf₀ : 0 < freq := zero_lt_one.trans_le hf
  have hNext : next = freq ^ frequencyExponent P.exponentParameter (P.order (n+3)) :=
    P.frequency_step (n+2)
  have hn₀ : 0 ≤ next := hNext ▸ pow_nonneg hf₀.le _
  have hΓ : 0 ≤ Γ := mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hn₀ _)
  have hT : 0 < Schild := d.time_pos
  have hInv : Schild⁻¹ ≤ μ := by
    refine (P.terminal_slab_inv_le hBase (n+1) (Tip).next_activation_nonnegative).trans ?_
    nth_rw 2 [← Real.rpow_one μ]
    exact Real.rpow_le_rpow_of_exponent_le hμ (by norm_num)
  have hBoundS : S ⊆ Icc t₀ Schild := Icc_subset_Icc_right (min_le_left _ _)
  have hGammaS (t : ℝ) (ht : t ∈ S) : gamma t ≤ Γ :=
    hEnvelope t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  have hZeroS (t : ℝ) (ht : t ∈ I) (hNot : t ∉ S) (x : Vec3 × ℝ) :
      (SwitchProfile).val.val.val (t,x) = 0 := by
    exact d.activationSwitch_eq_zero_outside ht
      (fun h => hNot ⟨h.1, le_min ht.2 h.2⟩) x.1 x.2
  have hWave := terminalWaveSpatialRate_le hf₀ hOldWave
  have hBmean : 1 ≤ D ^ (a+1) := one_le_pow₀ hD
  have hBwave : D ^ (a+1) ≤ freq ^ (2 : ℕ) := by
    calc
      _ ≤ D ^ (max a 1 +1) := pow_le_pow_right₀ hD (Nat.succ_le_succ (le_max_left _ _))
      _ ≤ freq ^ (1/2 : ℝ) := hOldWave
      _ ≤ _ := by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hf (by norm_num)
  have hcP : 0 ≤ Cparent := zero_le_one.trans (terminalGraphParentCost_ge_one Kparent hKparent N)
  have hParents (i : ℕ) (hi : i ≤ q) (m : ℕ) (hm : m ≤ N) (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      ‖iteratedFDeriv ℝ m (slabTimeJet 0 Schild i (Tip).parent.velocity t) x‖ ≤
        (Cparent * μ^B) * (D^(a+1))^m := by
    refine (hParent i hi m t ht x).trans ?_
    refine mul_le_mul (mul_le_mul_of_nonneg_right (le_terminalGraphParentCost Kparent hKparent hm) (by positivity))
      ?_ (by positivity) (by positivity)
    rw [← pow_mul D, ← pow_mul μ]
    apply pow_le_pow_right₀ hμ
    have h₁ : 5 ≤ 9*(a+1) := by
      have : 9 ≤ 9*(a+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right m h₁
  let Ψ := terminalGraphReadoutPower q B E
  have hCost' : terminalGraphReadoutCost q N L Cparent M O R W ≤ μ := hCost
  have hExp : depth = 6 * frequencyExponent P.exponentParameter (P.order (n+3)) := rfl
  have hDepth : 2 ≤ depth := d.depth_ge_two
  obtain ⟨hMean,hOsc,hTail,hSwitch⟩ := hNorm
  obtain ⟨hm,ho,hr,hs⟩ := b.geometricGraphJets_of_physicalTimeNorms
    ((by decide : 1 ≤ 2).trans d.depth_ge_two)
    d.parent.deformationOn.flow d.parent.smooth_velocity (fun t _ => (Tip).parent.periodic_velocity t)
    (Tip).next_activation_nonnegative d.launch_time_mem.2 gamma d.centerWeight_continuous d.centerWeight_pos
    d.centerWeight_le_one (isClosed_tsupport _) d.leading_inactive
    (show IsClosed S from isClosed_Icc) hBoundS hZeroS hΓ hGammaS
    d.regularity.envelope_pos (Real.rpow_pos_of_pos hf₀ _) hD hf hL
    (by positivity) (by positivity) (by positivity) (by positivity) d.radius_inv.le rfl d.carrier_bound
    hCoframe hMean hOsc hTail hSwitch hWave
  have hRead (i : ℕ) (hi : i ≤ q) (m : ℕ) (t : ℝ) (ht : t ∈ I) :=
    b.physicalTimeReadout_of_graphJets d.parent.deformationOn.flow d.parent.smooth_velocity
      (fun t _ => (Tip).parent.periodic_velocity t) hBmean hBwave (by positivity)
      (by unfold materialGraphFactor terminalTimeExtraction; positivity)
      (by unfold materialGraphFactor terminalTimeExtraction; positivity)
      (by unfold materialGraphFactor terminalTimeExtraction; positivity)
      (by unfold materialGraphFactor terminalTimeExtraction; positivity)
      hParents hm ho hr hs (i := i) (m := m) hi ht
  have hCarrierRate (i : ℕ) (hi : i ≤ q) (m : ℕ) :
      (freq ^ (2 : ℕ)) ^ (m+1+i) ≤ freq ^ (2 * ((m : ℝ)+1)+2*q) := by
    rw [← pow_mul, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hf
    push_cast
    have : (i : ℝ) ≤ q := by exact_mod_cast hi
    linarith
  have hResidualRate (i : ℕ) (hi : i ≤ q) :
      (freq ^ (2 : ℕ)) ^ (2+i) ≤ freq ^ (2 * ((q : ℝ)+2)) := by
    rw [← pow_mul, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hf
    push_cast
    have : (i : ℝ) ≤ q := by exact_mod_cast hi
    linarith
  have hScalars (i : ℕ) (hi : i ≤ q) (m : ℕ) (hm : m ≤ N) :=
    terminalGraphReadoutScalars_le (T := Schild) (parentPower := B) (profilePower := E)
      hμ hT hInv hf hL hcP hM hO hR hW hCost' hi hm hExp hNext
  constructor
  · intro i hi t ht
    constructor
    · intro m hmi
      have hOrder : i + m + 1 ≤ N := by dsimp only [N]; omega
      have hV := ((hRead i hi m t ht).1 hOrder).2.2
      have hS := (hScalars i hi m (by dsimp only [N]; omega)).2.1
      refine hV.trans ((by
        calc
          _ = _ := by dsimp only [N]; rw [hFrame]; ring
          _ ≤ (μ ^ Ψ) * (freq ^ (2 : ℕ)) ^ (m+1+i) :=
            mul_le_mul_of_nonneg_right hS (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left (hCarrierRate i hi m) (by positivity)))
    · have hOrder : i + 2 ≤ N := by
        dsimp only [N]
        omega
      have hR := ((hRead i hi 0 t ht).2 hOrder).2
      have hS := (hScalars i hi 0 (Nat.zero_le N)).2.2
      refine hR.trans ((by
        calc
          _ = _ := by dsimp only [N,Γ]; rw [hFrame]; ring
          _ ≤ (μ ^ Ψ * next ^ (-4 : ℝ)) * (freq ^ (2 : ℕ)) ^ (2+i) :=
            mul_le_mul_of_nonneg_right hS (by positivity)
          _ ≤ (μ ^ Ψ * next ^ (-4 : ℝ)) * freq ^ (2 * ((q : ℝ)+2)) :=
            mul_le_mul_of_nonneg_left (hResidualRate i hi) (by positivity)
          _ = _ := by ring))
  · intro m hmi t ht
    have hOrder : q + m + 1 ≤ N := by dsimp only [N]; omega
    have hMread := ((hRead q le_rfl m t ht).1 hOrder).1
    have hS := (hScalars q le_rfl m (by dsimp only [N]; omega)).1
    refine ⟨hMread.1, hMread.2.trans ?_⟩
    calc
      _ = _ := by dsimp only [N]; rw [hFrame]; ring
      _ ≤ (μ ^ Ψ * freq ^ (-5/2 : ℝ)) * (D^(a+1))^(m+1+q) :=
        mul_le_mul_of_nonneg_right hS (by positivity)
      _ = _ := by
        simp only [← pow_mul, Nat.mul_assoc]
        rw [mul_right_comm, ← pow_add]
        simp only [Ψ, neg_div]

end

end TorusEuler.ScheduledEulerConstruction
