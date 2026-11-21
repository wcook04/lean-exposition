import TorusEuler.TerminalTimeJetNorms
import TorusEuler.TerminalTimeLeibniz
import TorusEuler.TerminalPhaseTime
import TorusEuler.TerminalTransverseCoefficients

/-! The same selected transverse solve obeys the time-differentiated bounds. -/

open Set Finset
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

section WeightedProducts

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "Profile[" E "]" => HierarchyTwistedProfile T k E

/-- The spatial cost of applying a label matrix to a weighted profile. -/
def terminalApplyFieldCost (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) : ℝ :=
  (hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n *
    (2 * ‖(ContinuousLinearMap.apply ℝ F : E →L[ℝ] (E →L[ℝ] F) →L[ℝ] F).flip‖)

theorem terminalApplyFieldCost_nonneg (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) : 0 ≤ terminalApplyFieldCost E F n := by
  unfold terminalApplyFieldCost
  positivity

variable (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
  {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T)) (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < γ t)
  (ℓ h : ℝ) (n : ℕ)

local notation "N[" e "]" => unweightedSeminorm (E := e) (k := k) False ℓ h n hT
local notation "W[" e "]" => amplitudeSeminorm (E := e) (k := k) False ℓ h n hT ht₀ htT γ hγ hγ₀

theorem terminalWeighted_applyField_le (A : Profile[E →L[ℝ] F]) (f : Profile[E]) :
    W[F] (applyField A f) ≤ terminalApplyFieldCost E F n * (N[E →L[ℝ] F] A * W[E] f) := by
  have hI : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  obtain ⟨B, hB⟩ := inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hγ₀
  let W₀ := boundedWeightSeminorm (E := (E →L[ℝ] F)) (k := k) False ℓ h n hT hI
      (fun _ => 1) (B := 1) (by simp)
  have h₀ : W₀ A ≤ N[E →L[ℝ] F] A := by
    exact boundedWeightSeminorm_mono_time False ℓ h n hT hI
      (Subset.rfl : Icc (0 : ℝ) T ⊆ Icc 0 T) (fun _ => 1) (C := 1) (by simp) A
  let ev : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F := (ContinuousLinearMap.apply ℝ F).flip
  have hN := boundedWeightSeminorm_bilinear_le ev False ℓ h n hT hI
    (fun _ => 1) (fun t => (γ t)⁻¹) (fun t => (γ t)⁻¹)
    (by simp : ∀ t ∈ Icc t₀ T, ‖(1 : ℝ)‖ ≤ 1) hB hB (by simp) A f (applyField A f)
    (fun t ht p => applyField_eval A f ⟨hI ht, mem_univ _⟩)
  have hW : W[F] (applyField A f) ≤ terminalApplyFieldCost E F n * (W₀ A * W[E] f) := by
    refine hN.trans_eq ?_
    change (hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n *
      (2 * ‖ev‖ * W₀ A * W[E] f) = _
    unfold terminalApplyFieldCost
    dsimp only [ev]
    ring
  exact hW.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h₀ (apply_nonneg W[E] f))
    (terminalApplyFieldCost_nonneg E F n))

/-- Factorial weighting preserves the spatial product coefficient at every
time order. The coefficient norm is unweighted and the operand norm retains
its active-slab reciprocal amplitude. -/
theorem terminalWeighted_timeJet_applyField_le (q : ℕ) (A : Profile[E →L[ℝ] F]) (f : Profile[E]) :
    timeJetSeminorm hT q W[F] (applyField A f) ≤
      terminalApplyFieldCost E F n *
        (timeJetSeminorm hT q N[E →L[ℝ] F] A * timeJetSeminorm hT q W[E] f) := by
  exact timeJetSeminorm_applyField_le hT q N[E →L[ℝ] F] W[E] W[F]
    (terminalApplyFieldCost_nonneg E F n)
    (terminalWeighted_applyField_le hT ht₀ htT hγ hγ₀ ℓ h n) A f

end WeightedProducts

section TimeBootstrap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem terminalTimeJetWeight_succ_le (hT : 0 < T) (i : ℕ) :
    terminalTimeJetWeight T (i + 1) ≤ T * terminalTimeJetWeight T i := by
  have h : terminalTimeJetWeight T (i + 1) * (i + 1 : ℝ) = T * terminalTimeJetWeight T i := by
    have hf : (i.factorial : ℝ) ≠ 0 := by positivity
    have hi : (i + 1 : ℝ) ≠ 0 := by positivity
    rw [terminalTimeJetWeight, terminalTimeJetWeight, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
  rw [← h]
  exact le_mul_of_one_le_right (terminalTimeJetWeight_pos hT _).le
    (le_add_of_nonneg_left (Nat.cast_nonneg i))

/-- The next time order costs one differentiated profile, with no spatial
derivative loss and one factor of the slab duration. -/
theorem timeJetSeminorm_succ_le (hT : 0 < T) (q : ℕ)
    (N : Seminorm ℝ (HierarchyTwistedProfile T k E)) (f : HierarchyTwistedProfile T k E) :
    timeJetSeminorm hT (q + 1) N f ≤ N f + T * timeJetSeminorm hT q N (timeDerivative hT f) := by
  rw [timeJetSeminorm_apply, Finset.sum_range_succ']
  simp only [terminalTimeJetWeight, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, timeJet_zero, one_mul]
  rw [add_comm, timeJetSeminorm_apply, mul_sum]
  refine add_le_add le_rfl (sum_le_sum fun i _ => ?_)
  rw [timeJet_succ', ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (terminalTimeJetWeight_succ_le hT i) (apply_nonneg N _)

end TimeBootstrap

section ProjectedEquation

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "SP" => HierarchyTwistedProfile T k ℝ

theorem TransverseResult.projected_profile {hT : 0 < T} {G M : MP} {κ F : VP}
    (r : TransverseResult hT G M κ F) {d : TransverseCoefficients M κ} {freq : ℝ}
    (c : TransverseTimeCoefficients d freq) :
    timeDerivative hT r.output.V = applyField c.velocity r.output.V + applyField c.source F := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t,a,s⟩ hts
  rw [timeDerivative_apply hT _ hts.1]
  simp only [Submodule.coe_add, Pi.add_apply, applyField_eval _ _ hts]
  exact (r.velocity_projectedEquation c t hts.1 a s).derivWithin (uniqueDiffOn_Icc hT t hts.1)

theorem TransverseResult.pressure_normalized_profile {hT : 0 < T} {G M : MP} {κ F : VP}
    (r : TransverseResult hT G M κ F) {d : TransverseCoefficients M κ} {freq : ℝ}
    (hf : 0 < freq) (c : TransverseTimeCoefficients d freq) :
    phaseDerivative hT (freq • r.output.p) =
      applyField c.pressureVelocity r.output.V + applyField c.pressureSource F := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t,a,s⟩ hts
  rw [phaseDerivative_apply hT _ t hts.1 a s]
  simp only [Submodule.coe_add, Pi.add_apply, applyField_eval _ _ hts]
  exact (r.pressure_normalized_slope hf c t hts.1 a s).deriv

variable (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
  {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T)) (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < γ t)
  (ℓ h : ℝ) (n q : ℕ)

local notation "Wv" => amplitudeSeminorm (E := Vec3) (k := k) False ℓ h n hT ht₀ htT γ hγ hγ₀
local notation "Wp" => amplitudeSeminorm (E := ℝ) (k := k) False ℓ h n hT ht₀ htT γ hγ hγ₀
local notation "N[" e "]" => unweightedSeminorm (E := e) (k := k) False ℓ h n hT
local notation "JV[" i "]" => (timeJetSeminorm hT i Wv)
local notation "JP[" i "]" => (timeJetSeminorm hT i Wp)

/-- The differentiated projected equation costs the amplitude of the
undifferentiated field and the source. The same argument applies to the
uncut leading wave by taking the source to be zero. -/
theorem terminalProjectedVelocity_timeJet_le (V F : VP) (A B : MP) {C : ℝ} (hC : 0 ≤ C)
    (hA : timeJetSeminorm hT q N[Vec3 →L[ℝ] Vec3] A ≤ C)
    (hB : timeJetSeminorm hT q N[Vec3 →L[ℝ] Vec3] B ≤ C)
    (heq : timeDerivative hT V = applyField A V + applyField B F) :
    JV[q] V ≤ (1 + T * terminalApplyFieldCost Vec3 Vec3 n * C) ^ q * (Wv V + JV[q] F) := by
  let K := terminalApplyFieldCost Vec3 Vec3 n
  let d := T * K * C
  let a := Wv V + JV[q] F
  have hK := terminalApplyFieldCost_nonneg Vec3 Vec3 n
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg hT.le hK) hC
  have ha : 0 ≤ a := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have h : ∀ i ≤ q, JV[i] V + JV[q] F ≤ (1 + d) ^ i * a := by
    intro i
    induction i with
    | zero => intro _; rw [timeJetSeminorm_zero, pow_zero, one_mul]
    | succ i ih =>
      intro hi
      have hj : i ≤ q := Nat.le_of_succ_le hi
      have hA' := (timeJetSeminorm_mono hT hj _ A).trans hA
      have hB' := (timeJetSeminorm_mono hT hj _ B).trans hB
      have hv := (terminalWeighted_timeJet_applyField_le hT ht₀ htT hγ hγ₀ ℓ h n i A V).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA' (apply_nonneg _ _)) hK)
      have hf := (terminalWeighted_timeJet_applyField_le hT ht₀ htT hγ hγ₀ ℓ h n i B F).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul hB' (timeJetSeminorm_mono hT hj Wv F)
          (apply_nonneg _ _) hC) hK)
      have hder : JV[i] (timeDerivative hT V) ≤ K * C * (JV[i] V + JV[q] F) := by
        rw [heq]
        exact ((map_add_le_add (JV[i]) _ _).trans (add_le_add hv hf)).trans_eq (by ring)
      calc
        _ ≤ (Wv V + T * JV[i] (timeDerivative hT V)) + JV[q] F :=
          add_le_add (timeJetSeminorm_succ_le hT i Wv V) le_rfl
        _ ≤ (Wv V + T * (K * C * (JV[i] V + JV[q] F))) + JV[q] F := by gcongr
        _ = a + d * (JV[i] V + JV[q] F) := by dsimp only [a, d]; ring
        _ ≤ (1 + d) ^ i * a + d * ((1 + d) ^ i * a) :=
          add_le_add (le_mul_of_one_le_left ha (one_le_pow₀ (by linarith))) (mul_le_mul_of_nonneg_left (ih hj) hd)
        _ = _ := by rw [pow_succ]; ring
  exact (le_add_of_nonneg_right (apply_nonneg (JV[q]) F)).trans (h q le_rfl)

section

local notation "scalarCost" => terminalApplyFieldCost Vec3 ℝ n
local notation "vectorCost" => terminalApplyFieldCost Vec3 Vec3 n

/-- The fixed-order cost multiplying the differentiated source. -/
def transverseTimeCost (T : ℝ) (n q : ℕ) (C₀ C : ℝ) : ℝ :=
  (1 + 2 * terminalApplyFieldCost Vec3 ℝ n * C) *
    ((1 + T * terminalApplyFieldCost Vec3 Vec3 n * C) ^ q * (C₀ + 1)) +
  2 * terminalApplyFieldCost Vec3 ℝ n * C

theorem transverseTimeCost_nonneg {T C₀ C : ℝ} (n q : ℕ)
    (hT : 0 ≤ T) (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) :
    0 ≤ transverseTimeCost T n q C₀ C := by
  have hp := terminalApplyFieldCost_nonneg Vec3 ℝ n
  have hv := terminalApplyFieldCost_nonneg Vec3 Vec3 n
  unfold transverseTimeCost
  positivity

/-- The concrete transverse inverse at every time order. Only the same
order of the force is needed. The undifferentiated inverse supplies the
base bound and the two normalized pressure coefficients preserve the
inverse factor of the new carrier. -/
theorem TransverseResult.timeJet_bound {G M : MP} {κ F : VP} (r : TransverseResult hT G M κ F)
    {d : TransverseCoefficients M κ} {freq C₀ C : ℝ} (hf : 0 < freq)
    (c : TransverseTimeCoefficients d freq) (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C)
    (hBase : Wv r.output.V ≤ C₀ * Wv F)
    (hA : timeJetSeminorm hT q N[Vec3 →L[ℝ] Vec3] c.velocity ≤ C)
    (hB : timeJetSeminorm hT q N[Vec3 →L[ℝ] Vec3] c.source ≤ C)
    (hP : timeJetSeminorm hT q N[Vec3 →L[ℝ] ℝ] c.pressureVelocity ≤ C)
    (hQ : timeJetSeminorm hT q N[Vec3 →L[ℝ] ℝ] c.pressureSource ≤ C) :
    JV[q] r.output.V + freq * JP[q] r.output.p ≤
      transverseTimeCost T n q C₀ C * JV[q] F := by
  let V := r.output.V
  let p : SP := freq • r.output.p
  let Λ := (1 + T * vectorCost * C) ^ q * (C₀ + 1)
  have hK := terminalApplyFieldCost_nonneg Vec3 ℝ n
  have hγs (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) :
      phaseMean (fun s => p.val.val.val (t,a,s)) = 0 := by
    change phaseMean (fun s => freq • r.output.p.val.val.val (t,a,s)) = _
    rw [phaseMean_const_smul, r.pressure_mean t ht a, smul_zero]
  have hv : JV[q] V ≤ Λ * JV[q] F := by
    refine (terminalProjectedVelocity_timeJet_le hT ht₀ htT hγ hγ₀ ℓ h n q V F c.velocity c.source hC
      hA hB (r.projected_profile c)).trans ?_
    have hZero : Wv F ≤ JV[q] F := by
      simpa only [timeJetSeminorm_zero] using timeJetSeminorm_mono hT (Nat.zero_le q) Wv F
    have hV₀ := hBase.trans (mul_le_mul_of_nonneg_left hZero hC₀)
    have hvCost : 0 ≤ vectorCost := terminalApplyFieldCost_nonneg Vec3 Vec3 n
    calc
      _ ≤ (1 + T * vectorCost * C) ^ q * (C₀ * JV[q] F + JV[q] F) :=
        mul_le_mul_of_nonneg_left (add_le_add hV₀ le_rfl) (by positivity)
      _ = _ := by dsimp only [Λ]; ring
  have hpSlope : JP[q] p ≤ 2 * JP[q] (phaseDerivative hT p) := by
    refine timeJetSeminorm_le_of_jetwise_le hT q Wp Wp (phaseDerivative hT p) p 2 ?_
    intro i _
    rw [timeJet_directionDerivative]
    exact amplitudeSeminorm_le_phaseDerivative hT ht₀ htT hγ hγ₀ ℓ h n (timeJet hT i p)
      (fun t ht a => phaseMean_timeJet_eq_zero hT p hγs i t ht a)
  have hpEval := (terminalWeighted_timeJet_applyField_le hT ht₀ htT hγ hγ₀ ℓ h n q
      c.pressureVelocity V).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP (apply_nonneg _ _)) hK)
  have hqEval := (terminalWeighted_timeJet_applyField_le hT ht₀ htT hγ hγ₀ ℓ h n q
      c.pressureSource F).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ (apply_nonneg _ _)) hK)
  have hp : JP[q] p ≤ 2 * (scalarCost * (C * JV[q] V) + scalarCost * (C * JV[q] F)) := by
    rw [r.pressure_normalized_profile hf c] at hpSlope
    exact hpSlope.trans (mul_le_mul_of_nonneg_left
      ((map_add_le_add (JP[q]) _ _).trans (add_le_add hpEval hqEval)) zero_le_two)
  have hpScale : JP[q] p = freq * JP[q] r.output.p := by
    dsimp only [p]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hf]
  rw [← hpScale]
  calc
    _ ≤ JV[q] V + 2 * (scalarCost * (C * JV[q] V) + scalarCost * (C * JV[q] F)) :=
      add_le_add le_rfl hp
    _ ≤ Λ * JV[q] F + 2 * (scalarCost * (C * (Λ * JV[q] F)) + scalarCost * (C * JV[q] F)) := by gcongr
    _ = _ := by unfold transverseTimeCost; dsimp only [Λ]; ring

end
end ProjectedEquation

end

end TorusEuler.HierarchyTwistedProfile
