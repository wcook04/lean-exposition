import TorusEuler.HierarchyPhysicalSolvers
import TorusEuler.HierarchyPhaseIndependentNorm
import TorusEuler.TerminalTimeGraphBounds
import TorusEuler.TerminalTimeJetNorms
import TorusEuler.TerminalTimeJet

/-! The actual selected hierarchy mean inherits the raw mean time estimates. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

/-- Taking the parity part of a velocity commutes with all within-slab time derivatives. -/
theorem slabTimeJet_endpointTimeParityPart {T : ℝ} (hT : 0 < T) {f : Velocity}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (σ : ℝ) (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    slabTimeJet 0 T q (endpointTimeParityPart σ f) t x =
      endpointTimeParityPart σ (slabTimeJet 0 T q f) t x := by
  induction q generalizing t with
  | zero =>
      rw [slabTimeJet_zero (E := Vec3) 0 T f]
      simp only [slabTimeJet, iteratedDerivWithin_zero]
  | succ n ih =>
      rw [slabTimeJet_succ]
      have hDer := derivWithin_congr
        (fun r hr => ih hr) (ih ht)
      rw [hDer, derivWithin_endpointTimeParityPart hT (slabTimeJet_smooth hT hf n) ht,
        endpointTimeParityPart]
      exact congrArg (fun g => endpointParityPart σ g x)
        (funext fun y => (slabTimeJet_succ 0 T n f t y).symm)

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3} {G M : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)}
  {κ S : HierarchyTwistedProfile T k Vec3} {hT : 0 < T} {d : MeanCoefficients G M}

local notation "I" => Icc (0 : ℝ) T

theorem rawMean_timeJet_labelNorm_le (r : MeanResult hT G M κ S d)
    {ℓ h : ℝ} (hℓ : 0 ≤ ℓ) (n q : ℕ) :
    unweightedSeminorm False ℓ h n hT (timeJet hT q r.output.B) ≤
      hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
        (fun (t : I) => slabTimeJet 0 T q r.rawMean t) := by
  have hAvg : HierarchyPeriodicProfile.profilePhaseAverage hT r.output.B.val = r.output.B.val :=
    congrArg Subtype.val r.output.average_B
  have hPhase :=
    HierarchyPeriodicProfile.phaseIndependent_of_profilePhaseAverage_eq_self hT r.output.B.val hAvg
  rw [unweightedSeminorm_false_eq_labelWordNorm_of_phaseIndependent hT ℓ h n _
    (timeJet_phaseIndependent hT r.output.B hPhase q)]
  rcases r.meanSelection with hRaw | hOdd
  · have hEq : (fun (t : I) a => (timeJet hT q r.output.B).val.val.val (t,a,0)) =
        (fun (t : I) => slabTimeJet 0 T q r.rawMean t) := by
      funext t a
      rw [timeJet_apply hT q r.output.B t.property]
      exact iteratedDerivWithin_congr (fun s hs => hRaw s hs a) t.property
    rw [hEq]
  · have hEq : (fun (t : I) a => (timeJet hT q r.output.B).val.val.val (t,a,0)) =
        (fun (t : I) => endpointTimeParityPart (-1) (slabTimeJet 0 T q r.rawMean) t) := by
      funext t a
      rw [timeJet_apply hT q r.output.B t.property,
        ← slabTimeJet_endpointTimeParityPart hT r.rawMean_smooth (-1) q t.property a]
      exact iteratedDerivWithin_congr (fun s hs => hOdd s hs a) t.property
    rw [hEq]
    exact hierarchyFiniteLabelNorm_endpointParityPart_le
      (f := fun (t : I) => slabTimeJet 0 T q r.rawMean t)
      (fun t => slabTimeJet_slice_smooth hT r.rawMean_smooth q t.property)
      False ℓ n (sign := -1) (by norm_num)
      (fun w _ => (bddAbove_endpointLabelWord_of_smooth_periodic hT hℓ
        (slabTimeJet_smooth hT r.rawMean_smooth q)
        (fun _ ht => slabTimeJet_periodic r.rawMean_periodic q ht) w).1)

/-- A common bound on the raw mean time slices gives the factorial norm of
the very same mean selected by the hierarchy. -/
theorem selectedMean_timeJetSeminorm_le_of_raw (r : MeanResult hT G M κ S d)
    (hT₁ : T ≤ 1) {ℓ h C : ℝ} (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C) (n q : ℕ)
    (hRaw : ∀ i ≤ q, hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
      (fun (t : I) => slabTimeJet 0 T i r.rawMean t) ≤ C) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) r.output.B ≤ ((q : ℝ) + 1) * C := by
  rw [timeJetSeminorm_apply]
  calc
    _ ≤ ∑ i ∈ Finset.range (q + 1), C := by
      apply Finset.sum_le_sum
      intro i hi
      have hw : terminalTimeJetWeight T i ≤ 1 := by
        apply (div_le_one (Nat.cast_pos.mpr (Nat.factorial_pos i))).mpr
        exact (pow_le_one₀ hT.le hT₁).trans (by exact_mod_cast Nat.factorial_pos i)
      exact (mul_le_mul_of_nonneg_left
        ((rawMean_timeJet_labelNorm_le r hℓ (h := h) n i).trans (hRaw i
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))) (terminalTimeJetWeight_pos hT i).le).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw hC)
    _ = _ := by simp [nsmul_eq_mul]

/-- Extract any fixed source derivative from the factorial mixed norm with
one constant at the prescribed time order. -/
theorem meanSource_timeJet_labelNorm_le {q : ℕ} (hT₁ : T ≤ 1) {ℓ h : ℝ} (n : ℕ)
    (hS : (twistedHierarchyOperators hT G M κ).average S = S)
    (i : ℕ) (hi : i ≤ q) :
    hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
      (fun (t : I) => slabTimeJet 0 T i (fun r a => S.val.val.val (r,a,0)) t) ≤
      (q.factorial : ℝ) * T⁻¹ ^ q * timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) S := by
  have hAvg : HierarchyPeriodicProfile.profilePhaseAverage hT S.val = S.val := congrArg Subtype.val hS
  have hPhase := HierarchyPeriodicProfile.phaseIndependent_of_profilePhaseAverage_eq_self hT S.val hAvg
  have hEq : (fun (t : I) a => (timeJet hT i S).val.val.val (t,a,0)) =
      (fun (t : I) => slabTimeJet 0 T i (fun r a => S.val.val.val (r,a,0)) t) := by
    funext t a
    exact timeJet_apply hT i S t.property (a,0)
  rw [← hEq, ← unweightedSeminorm_false_eq_labelWordNorm_of_phaseIndependent hT ℓ h n _
    (timeJet_phaseIndependent hT S hPhase i)]
  refine (norm_timeJet_le hT hi _ S).trans ?_
  have hF : (i.factorial : ℝ) ≤ q.factorial := by
    exact_mod_cast Nat.monotone_factorial hi
  have hI : T⁻¹ ^ i ≤ T⁻¹ ^ q := pow_le_pow_right₀ ((one_le_inv₀ hT).mpr hT₁) hi
  exact mul_le_mul_of_nonneg_right (mul_le_mul hF hI (by positivity) (Nat.cast_nonneg _))
    (apply_nonneg _ _)

end HierarchyTwistedProfile
end
end TorusEuler
