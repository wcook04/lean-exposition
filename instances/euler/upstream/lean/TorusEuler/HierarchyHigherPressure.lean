import TorusEuler.HierarchyTwistedSolves
import TorusEuler.HierarchyConcreteCompletion
import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchyPhysicalSolvers
import TorusEuler.HierarchySupportPropagation
import TorusEuler.PhysicalHierarchyProfileBounds
import TorusEuler.WavePressureCenter

/-!
The higher oscillatory pressure estimate (5.52) in frozen Lemma 5.9.
The proof uses the transverse pressure slope before taking a physical derivative.
-/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "LP" => Vec3 × ℝ
local notation "Op" => Vec3 →L[ℝ] Vec3

/-- The longitudinal projection used in the transverse pressure equation. -/
def hierarchyLongitudinalProjection (κ : Vec3) : Op :=
  (‖κ‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ κ κ

theorem contDiff_hierarchyLongitudinalProjection {κ : Vec3 → Vec3}
    (hκ : ContDiff ℝ ∞ κ) (hnz : ∀ a, κ a ≠ 0) :
    ContDiff ℝ ∞ (fun a => hierarchyLongitudinalProjection (κ a)) := by
  have hi := (hκ.norm_sq ℝ).inv (fun a => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hnz a)))
  exact hi.smul (((innerSL ℝ (E := Vec3)).contDiff.comp hκ).smulRight hκ)

private def hierarchyPressureLabelRestriction : (LP →L[ℝ] ℝ) →L[ℝ] Vec3 :=
  (InnerProductSpace.toDual ℝ Vec3).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((compL ℝ Vec3 LP ℝ).flip (inl ℝ Vec3 ℝ))

private theorem hierarchyPressureLabelRestriction_apply (D : LP →L[ℝ] ℝ) :
    hierarchyPressureLabelRestriction D = (InnerProductSpace.toDual ℝ Vec3).symm
      (D.comp (inl ℝ Vec3 ℝ)) := rfl

private theorem norm_hierarchyPressureLabelRestriction_le :
    ‖hierarchyPressureLabelRestriction‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun D => ?_
  rw [hierarchyPressureLabelRestriction_apply, LinearIsometryEquiv.norm_map, one_mul]
  exact (D.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg D) (norm_inl_le_one ℝ Vec3 ℝ))

/-- The gradient in the labels with the phase coordinate held fixed. -/
def hierarchyPressureLabelGradient (p : Vec3 → ℝ → ℝ) (a : Vec3) (s : ℝ) : Vec3 :=
  hierarchyPressureLabelRestriction (fderiv ℝ (Function.uncurry p) (a,s))

/-- The gradient profile before evaluating it on the physical phase graph.
The fast phase derivative is represented by the actual longitudinal
projection of the force minus twice the strain correction. -/
def hierarchyHigherPressureGradient (G M : Vec3 → Op) (κ : Vec3 → Vec3)
    (p : Vec3 → ℝ → ℝ) (force V : Vec3 → ℝ → Vec3) (a : Vec3) (s : ℝ) : Vec3 :=
  (G a).adjoint (hierarchyPressureLabelGradient p a s) +
    hierarchyLongitudinalProjection (κ a) (force a s - (2 : ℝ) • M a (V a s))

private theorem fderiv_eq_label_coprod_pressureSlope {p : Vec3 → ℝ → ℝ}
    {a : Vec3} {s b : ℝ} (hp : DifferentiableAt ℝ (Function.uncurry p) (a,s))
    (hs : HasDerivAt (p a) b s) :
    fderiv ℝ (Function.uncurry p) (a,s) =
      ((fderiv ℝ (Function.uncurry p) (a,s)).comp (inl ℝ Vec3 ℝ)).coprod
        (toSpanSingleton ℝ b) := by
  let D := fderiv ℝ (Function.uncurry p) (a,s)
  have hline := (hasDerivAt_const (c := a) s).prodMk (hasDerivAt_id s)
  have hD : D (0, 1) = b := (hp.hasFDerivAt.comp_hasDerivAt s hline).unique hs
  apply ContinuousLinearMap.ext
  intro z
  change D z = D (z.1, 0) + z.2 * b
  have hpair : z = (z.1, 0) + z.2 • ((0 : Vec3), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hpair]
  simp only [map_add, map_smul, hD, smul_eq_mul]

/-- The exact first physical derivative with the costly phase derivative
already eliminated by the transverse equation. -/
theorem gradient_transportedHigherPressure_eq {A : Velocity} {k : Vec3} {t : ℝ}
    {G M : Vec3 → Op} {κ : Vec3 → Vec3} {p : Vec3 → ℝ → ℝ}
    {force V : Vec3 → ℝ → Vec3} (hA : Differentiable ℝ (A t))
    (hG : ∀ x, G (A t x) = fderiv ℝ (A t) x)
    (hκ : ∀ a, κ a = (G a).adjoint k)
    (hp : Differentiable ℝ (Function.uncurry p))
    (hs : ∀ a s, HasDerivAt (p a) (oscillatoryPressureSlope (M a) (κ a) (force a s) (V a s)) s) :
    gradient (transportedProfile A k (fun _ => p) t) =
      transportedProfile A k (fun _ => hierarchyHigherPressureGradient G M κ p force V) t := by
  apply gradient_eq
  intro x
  let a := A t x
  let s := ⟪k, a⟫_ℝ
  have hpd := (hp (a,s)).hasFDerivAt
  rw [fderiv_eq_label_coprod_pressureSlope (hp (a,s)) (hs a s)] at hpd
  rw [hκ a, hG x] at hpd
  have h := hasGradientAt_transportedOscillatoryPressure (p := fun _ => p)
    (hA x).hasFDerivAt hpd
  simpa only [transportedProfile, hierarchyHigherPressureGradient, hierarchyPressureLabelGradient,
    hierarchyPressureLabelRestriction_apply, hκ a, hG x, a, s, hierarchyLongitudinalProjection, smul_apply]
    using h

private theorem phaseJetBound_pressure_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : LP → E} {A B : ℝ} {n : ℕ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hF : PhaseJetBound n A f) (hG : PhaseJetBound n B g) :
    PhaseJetBound n (A + B) (fun z => f z + g z) := by
  intro j hj x
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hF j hj x) (hG j hj x))

private theorem phaseJetBound_pressure_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : LP → E} {A B : ℝ} {n : ℕ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hF : PhaseJetBound n A f) (hG : PhaseJetBound n B g) :
    PhaseJetBound n (A + B) (fun z => f z - g z) := by
  intro j hj x
  rw [fun_iteratedFDeriv_sub_apply (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hF j hj x) (hG j hj x))

private theorem phaseJetBound_pressure_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : LP → E} {A : ℝ} {n : ℕ} (hf : ContDiff ℝ ∞ f) (hF : PhaseJetBound n A f)
    (c : ℝ) : PhaseJetBound n (‖c‖ * A) (fun z => c • f z) := by
  intro j hj x
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by simp)).contDiffAt, norm_smul]
  exact mul_le_mul_of_nonneg_left (hF j hj x) (norm_nonneg c)

private theorem phaseJetBound_pressure_clmApply {L : LP → Op} {f : LP → Vec3}
    {A B : ℝ} {n : ℕ} (hL : ContDiff ℝ ∞ L) (hf : ContDiff ℝ ∞ f)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hLn : PhaseJetBound n A L) (hfn : PhaseJetBound n B f) :
    PhaseJetBound n ((2 : ℝ) ^ n * A * B) (fun x => L x (f x)) := by
  intro j hj x
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i L x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖ :=
      norm_iteratedFDeriv_clm_apply hL hf x (by simp)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hLn i (hij.trans hj) x) (Nat.cast_nonneg _))
        (hfn (j - i) ((Nat.sub_le j i).trans hj) x) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ j * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]
    _ ≤ (2 : ℝ) ^ n * A * B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB

private theorem scaledPressureLabelGradient_eq {ell h : ℝ} (hell : ell ≠ 0)
    {p : Vec3 → ℝ → ℝ} (hp : Differentiable ℝ (Function.uncurry p)) :
    scaledPhaseProfile ell h (hierarchyPressureLabelGradient p) =
      fun z => ell⁻¹ • hierarchyPressureLabelRestriction
        (fderiv ℝ (scaledPhaseProfile ell h p) z) := by
  funext z
  let S := labelPhaseScale ell h
  let D := fderiv ℝ (Function.uncurry p) (S z)
  change hierarchyPressureLabelRestriction D =
    ell⁻¹ • hierarchyPressureLabelRestriction (fderiv ℝ (Function.uncurry p ∘ S) z)
  have hD : fderiv ℝ (Function.uncurry p ∘ S) z = D.comp S :=
    ((hp (S z)).hasFDerivAt.comp z S.hasFDerivAt).fderiv
  have hcomp : (D.comp S).comp (inl ℝ Vec3 ℝ) = ell • D.comp (inl ℝ Vec3 ℝ) := by
    ext v
    change D (S (v, 0)) = ell * D (v, 0)
    rw [show S (v, 0) = ell • (v, (0 : ℝ)) by simp [S, labelPhaseScale_apply], map_smul,
      smul_eq_mul]
  rw [hD, hierarchyPressureLabelRestriction_apply, hierarchyPressureLabelRestriction_apply,
    hcomp, map_smul, smul_smul, inv_mul_cancel₀ hell, one_smul]

/-- One label derivative of the pressure consumes a label radius factor, with
no inverse power of the phase width. -/
theorem scaledPressureLabelGradient_jetBound {ell h B : ℝ} (hell : 0 < ell)
    {p : Vec3 → ℝ → ℝ} (hp : ContDiff ℝ ∞ (Function.uncurry p))
    (hpN : PhaseJetBound 2 B (scaledPhaseProfile ell h p)) :
    PhaseJetBound 1 (ell⁻¹ * B) (scaledPhaseProfile ell h (hierarchyPressureLabelGradient p)) := by
  have hscaled : ContDiff ℝ ∞ (scaledPhaseProfile ell h p) :=
    hp.comp (labelPhaseScale ell h).contDiff
  have hD := hscaled.fderiv_right (m := ∞) (by simp)
  have hreg := hierarchyPressureLabelRestriction.contDiff.comp hD
  have hjet : PhaseJetBound 1 B (hierarchyPressureLabelRestriction ∘
      fderiv ℝ (scaledPhaseProfile ell h p)) := by
    intro j hj x
    refine (hierarchyPressureLabelRestriction.norm_iteratedFDeriv_comp_left hD.contDiffAt
      (by simp)).trans ?_
    rw [norm_iteratedFDeriv_fderiv]
    exact (mul_le_of_le_one_left (norm_nonneg _) norm_hierarchyPressureLabelRestriction_le).trans
      (hpN (j + 1) (Nat.succ_le_succ hj) x)
  rw [scaledPressureLabelGradient_eq hell.ne' (hp.differentiable (by simp))]
  simpa only [Function.comp_apply, Real.norm_of_nonneg (inv_nonneg.mpr hell.le)] using
    phaseJetBound_pressure_smul hreg hjet ell⁻¹

/-- Weighted first jets of the exact higher pressure gradient. The label part
uses a second pressure jet, and the projected phase part uses only first jets
of the actual transverse force and velocity. -/
theorem scaledHigherPressureGradient_jetBound {ell h CG CM CP Bp Bf Bv : ℝ}
    {G M : Vec3 → Op} {κ : Vec3 → Vec3} {p : Vec3 → ℝ → ℝ} {f V : Vec3 → ℝ → Vec3}
    (hell : 0 < ell) (hCG : 0 ≤ CG) (hCM : 0 ≤ CM) (hCP : 0 ≤ CP)
    (hBp : 0 ≤ Bp) (hBf : 0 ≤ Bf) (hBv : 0 ≤ Bv)
    (hG : ContDiff ℝ ∞ (fun a => (G a).adjoint)) (hM : ContDiff ℝ ∞ M)
    (hP : ContDiff ℝ ∞ (fun a => hierarchyLongitudinalProjection (κ a)))
    (hp : ContDiff ℝ ∞ (Function.uncurry p)) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hGN : PhaseJetBound 1 CG (scaledPhaseCoefficient ell (fun a => (G a).adjoint)))
    (hMN : PhaseJetBound 1 CM (scaledPhaseCoefficient ell M))
    (hPN : PhaseJetBound 1 CP (scaledPhaseCoefficient ell (fun a => hierarchyLongitudinalProjection (κ a))))
    (hpN : PhaseJetBound 2 Bp (scaledPhaseProfile ell h p))
    (hfN : PhaseJetBound 1 Bf (scaledPhaseProfile ell h f))
    (hVN : PhaseJetBound 1 Bv (scaledPhaseProfile ell h V)) :
    PhaseJetBound 1 (2 * CG * (ell⁻¹ * Bp) + 2 * CP * (Bf + 2 * (2 * CM * Bv)))
      (scaledPhaseProfile ell h (hierarchyHigherPressureGradient G M κ p f V)) := by
  let gs := scaledPhaseCoefficient ell (fun a => (G a).adjoint)
  let ms := scaledPhaseCoefficient ell M
  let ps := scaledPhaseCoefficient ell (fun a => hierarchyLongitudinalProjection (κ a))
  let hp' := scaledPhaseProfile ell h (hierarchyPressureLabelGradient p)
  let fs := scaledPhaseProfile ell h f
  let vs := scaledPhaseProfile ell h V
  have hgs : ContDiff ℝ ∞ gs := contDiff_scaledPhaseCoefficient hG ell
  have hms : ContDiff ℝ ∞ ms := contDiff_scaledPhaseCoefficient hM ell
  have hps : ContDiff ℝ ∞ ps := contDiff_scaledPhaseCoefficient hP ell
  have hfs : ContDiff ℝ ∞ fs := hf.comp (labelPhaseScale ell h).contDiff
  have hvs : ContDiff ℝ ∞ vs := hV.comp (labelPhaseScale ell h).contDiff
  have hp's : ContDiff ℝ ∞ hp' := by
    dsimp only [hp']
    rw [scaledPressureLabelGradient_eq hell.ne' (hp.differentiable (by simp))]
    have hs : ContDiff ℝ ∞ (scaledPhaseProfile ell h p) := hp.comp (labelPhaseScale ell h).contDiff
    exact (hierarchyPressureLabelRestriction.contDiff.comp (hs.fderiv_right (by simp))).const_smul _
  have hp'jet := scaledPressureLabelGradient_jetBound hell hp hpN
  have hl := phaseJetBound_pressure_clmApply hgs hp's hCG (by positivity) hGN hp'jet
  have hMV := phaseJetBound_pressure_clmApply hms hvs hCM hBv hMN hVN
  have hMVs := hms.clm_apply hvs
  have h2 := phaseJetBound_pressure_smul hMVs hMV (2 : ℝ)
  have hq := phaseJetBound_pressure_sub hfs (hMVs.const_smul _) hfN h2
  have hr := phaseJetBound_pressure_clmApply hps (hfs.sub (hMVs.const_smul (2 : ℝ)))
    hCP (by norm_num; positivity) hPN hq
  have H := phaseJetBound_pressure_add (hgs.clm_apply hp's)
    (hps.clm_apply (hfs.sub (hMVs.const_smul (2 : ℝ)))) hl hr
  change PhaseJetBound 1 _
    (fun z => gs z (hp' z) + ps z (fs z - 2 • ms z (vs z)))
  simpa only [pow_one, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using H

/-- After the phase slope has been used, the remaining physical derivative
costs at most the usual single factor `freq^(3/2)`. -/
theorem higherPressureGraphCost_le {freq ell h C A B : ℝ} {k : Vec3}
    (hfreq : 1 ≤ freq) (hell : 0 < ell) (hC : 0 ≤ C)
    (hw : h = freq ^ (-1 / 2 : ℝ)) (hellInv : ell⁻¹ ≤ A) (hk : ‖k‖ ≤ B * freq) :
    6 * ((ell⁻¹ + h⁻¹ * ‖k‖) * C) ≤ (6 * ((A + B) * C)) * freq ^ (3 / 2 : ℝ) := by
  have hf₀ : 0 < freq := zero_lt_one.trans_le hfreq
  have hA : 0 ≤ A := (inv_nonneg.mpr hell.le).trans hellInv
  have hlarge : 1 ≤ freq ^ (3 / 2 : ℝ) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hfreq (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hinv : h⁻¹ = freq ^ (1 / 2 : ℝ) := by
    rw [hw, show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hf₀.le, inv_inv]
  calc
    _ ≤ 6 * ((A + freq ^ (1 / 2 : ℝ) * (B * freq)) * C) := by
      rw [hinv]
      gcongr
    _ = 6 * ((A + B * freq ^ (3 / 2 : ℝ)) * C) := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hf₀, Real.rpow_one]
      ring
    _ ≤ 6 * ((A * freq ^ (3 / 2 : ℝ) + B * freq ^ (3 / 2 : ℝ)) * C) := by
      gcongr
      exact le_mul_of_one_le_right hA hlarge
    _ = _ := by ring

/-- The pressure gradient budget uses the velocity and source at the requested
order and the slow label derivative uses pressure one order higher. The level
bounds already include one power of frequency multiplying the pressure. -/
theorem higherPressureGradientBudget_sum_le {P : ℕ} {freq C L cF cV cQ cSlow : ℝ}
    (hfreq : 1 ≤ freq) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hcF : 0 ≤ cF) (hcV : 0 ≤ cV) (hcSlow : 0 ≤ cSlow)
    (hslow : cQ ≤ cSlow * freq) (F V q g : ℕ → ℝ)
    (hq : ∀ p ∈ Finset.Icc 2 P, 0 ≤ q p)
    (hF : ∀ p ∈ Finset.Icc 2 P, F p ≤ C * freq ^ hierarchyOscExponent p)
    (hV : ∀ p ∈ Finset.Icc 2 P, V p ≤ C * L * freq ^ hierarchyOscExponent p)
    (hQ : ∀ p ∈ Finset.Icc 2 P, freq * q p ≤ C * L * freq ^ hierarchyOscExponent p)
    (hg : ∀ p ∈ Finset.Icc 2 P, g p ≤ cF * F p + cV * V p + cQ * q p) :
    (∑ p ∈ Finset.Icc 2 P, g p) ≤ (Finset.Icc 2 P).card *
      (C * (cF + (cV + cSlow) * L) * freq ^ (-23 / 12 : ℝ)) := by
  have hlevel (p : ℕ) (hp : p ∈ Finset.Icc 2 P) :
      g p ≤ C * (cF + (cV + cSlow) * L) * freq ^ (-23 / 12 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hfreq
      (hierarchyOscExponent_antitone (Finset.mem_Icc.mp hp).1)
    have hslow' : cQ * q p ≤ cSlow * (C * L * freq ^ hierarchyOscExponent p) := calc
      _ ≤ (cSlow * freq) * q p := mul_le_mul_of_nonneg_right hslow (hq p hp)
      _ = cSlow * (freq * q p) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hQ p hp) hcSlow
    calc
      _ ≤ cF * F p + cV * V p + cQ * q p := hg p hp
      _ ≤ cF * (C * freq ^ hierarchyOscExponent p) +
          cV * (C * L * freq ^ hierarchyOscExponent p) +
          cSlow * (C * L * freq ^ hierarchyOscExponent p) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hF p hp) hcF)
          (mul_le_mul_of_nonneg_left (hV p hp) hcV)) hslow'
      _ = C * (cF + (cV + cSlow) * L) * freq ^ hierarchyOscExponent p := by ring
      _ ≤ _ := by
        rw [show hierarchyOscExponent 2 = (-23 / 12 : ℝ) by norm_num [hierarchyOscExponent]] at hpow
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
  calc
    _ ≤ ∑ _p ∈ Finset.Icc 2 P, (C * (cF + (cV + cSlow) * L) * freq ^ (-23 / 12 : ℝ)) :=
      Finset.sum_le_sum hlevel
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Combining the pressure jet estimate and the graph derivative costs a
fixed parent power, independent of the depth or derivative-order constants. -/
theorem higherPressure_prefactor_le_parentPower {P a b c : ℕ}
    {D Cjet Kwave Aell loss C B L C₀ : ℝ}
    (hD : 1 ≤ D) (hCjet₀ : 0 ≤ Cjet) (hKwave₀ : 0 ≤ Kwave) (hAell₀ : 0 ≤ Aell)
    (hloss₀ : 0 ≤ loss) (hC₀ : 0 ≤ C)
    (hCjet : Cjet ≤ B * D ^ 24) (hKwave : Kwave ≤ D ^ c)
    (hAell : Aell ≤ D ^ a) (hloss : loss ≤ L * D ^ b) (hC : C ≤ C₀) :
    6 * ((Aell + Kwave) * Cjet) * ((Finset.Icc 2 P).card *
      (C * (8 * Cjet + (32 * Cjet ^ 2 + 32 * Cjet * Aell) * loss))) ≤
    (12 * (Finset.Icc 2 P).card * C₀ * B ^ 2 * (8 + 32 * (B + 1) * L)) *
      D ^ (max a c + 48 + (max 24 a + b)) := by
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hB : 0 ≤ B := nonneg_of_mul_nonneg_left (hCjet₀.trans hCjet) (pow_pos hD₀ _)
  have hL : 0 ≤ L := nonneg_of_mul_nonneg_left (hloss₀.trans hloss) (pow_pos hD₀ _)
  have hC₀' : 0 ≤ C₀ := hC₀.trans hC
  have hpair : Aell + Kwave ≤ 2 * D ^ max a c := by
    rw [two_mul]
    exact add_le_add (hAell.trans (pow_le_pow_right₀ hD (le_max_left _ _)))
      (hKwave.trans (pow_le_pow_right₀ hD (le_max_right _ _)))
  have hjet : Cjet ^ 2 ≤ B ^ 2 * D ^ 48 := by
    simpa only [mul_pow, ← pow_mul, show (24 : ℕ) * 2 = 48 by decide] using
      pow_le_pow_left₀ hCjet₀ hCjet 2
  have hsum : Cjet + Aell ≤ (B + 1) * D ^ max 24 a := by
    rw [add_mul, one_mul]
    exact add_le_add (hCjet.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD (le_max_left _ _)) hB))
      (hAell.trans (pow_le_pow_right₀ hD (le_max_right _ _)))
  have he : 1 ≤ D ^ (max 24 a + b) := one_le_pow₀ hD
  have hinner : 8 + 32 * (Cjet + Aell) * loss ≤
      (8 + 32 * (B + 1) * L) * D ^ (max 24 a + b) := calc
    _ ≤ 8 + 32 * ((B + 1) * D ^ max 24 a) * (L * D ^ b) := by gcongr
    _ = 8 + (32 * (B + 1) * L) * D ^ (max 24 a + b) := by rw [pow_add]; ring
    _ ≤ _ := by
      rw [add_mul]
      have h8 : (8 : ℝ) ≤ 8 * D ^ (max 24 a + b) :=
        le_mul_of_one_le_right (by norm_num) he
      exact add_le_add h8 le_rfl
  calc
    _ = 6 * (Finset.Icc 2 P).card * C * (Aell + Kwave) * Cjet ^ 2 *
        (8 + 32 * (Cjet + Aell) * loss) := by ring
    _ ≤ 6 * (Finset.Icc 2 P).card * C₀ * (2 * D ^ max a c) *
        (B ^ 2 * D ^ 48) * ((8 + 32 * (B + 1) * L) * D ^ (max 24 a + b)) := by
      gcongr
    _ = _ := by
      rw [pow_add D (max a c + 48) (max 24 a + b), pow_add D (max a c) 48]
      ring


section Jets

variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The total corrected gradient uses the sum of the individual jet budgets. -/
theorem phaseJetBound_sum_of_level_bounds {n P : ℕ} {f : ℕ → U → E} {M : ℕ → ℝ}
    (hf : ∀ p ∈ Finset.Icc 2 P, ContDiff ℝ n (f p))
    (hM : ∀ p ∈ Finset.Icc 2 P, PhaseJetBound n (M p) (f p)) :
    PhaseJetBound n (∑ p ∈ Finset.Icc 2 P, M p) (fun x => ∑ p ∈ Finset.Icc 2 P, f p x) := by
  intro j hj x
  rw [iteratedFDeriv_fun_sum_apply (fun p hp => ((hf p hp).of_le (by exact_mod_cast hj)).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp => hM p hp j hj x))

end Jets


namespace HierarchyTwistedProfile

variable {T : ℝ} {k₀ : Vec3}

/-- Read the exact gradient profile of a selected twisted pressure. Its
phase contribution uses the actual source of that transverse selection. -/
theorem TransverseResult.gradient_transportedPressure_eq {hT : 0 < T}
    {G M : HierarchyTwistedProfile T k₀ Op} {κ F : HierarchyTwistedProfile T k₀ Vec3}
    (r : TransverseResult hT G M κ F) {A : Velocity} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hA : Differentiable ℝ (A t))
    (hG : ∀ x, G.val.val.val (t,A t x,0) = fderiv ℝ (A t) x)
    (hκ : ∀ a, κ.val.val.val (t,a,0) = (G.val.val.val (t,a,0)).adjoint k₀) :
    let p (a : Vec3) (s : ℝ) := r.output.p.val.val.val (t,a,s)
    let f (a : Vec3) (s : ℝ) := F.val.val.val (t,a,s)
    let v (a : Vec3) (s : ℝ) := r.output.V.val.val.val (t,a,s)
    gradient (transportedProfile A k₀ (fun _ => p) t) =
      transportedProfile A k₀ (fun _ => hierarchyHigherPressureGradient
        (fun a => G.val.val.val (t,a,0)) (fun a => M.val.val.val (t,a,0))
        (fun a => κ.val.val.val (t,a,0)) p f v) t := by
  exact gradient_transportedHigherPressure_eq hA hG hκ
    ((HierarchySmoothProfile.contDiff_labelPhase_slice r.output.p.val.val ht).differentiable
      (by simp)) (r.pressure_slope t ht)

end HierarchyTwistedProfile

private theorem contDiff_hierarchyHigherPressureGradient
    {G M : Vec3 → Op} {κ : Vec3 → Vec3} {p : Vec3 → ℝ → ℝ} {f V : Vec3 → ℝ → Vec3}
    (hG : ContDiff ℝ ∞ (fun a => (G a).adjoint)) (hM : ContDiff ℝ ∞ M)
    (hP : ContDiff ℝ ∞ (fun a => hierarchyLongitudinalProjection (κ a)))
    (hp : ContDiff ℝ ∞ (Function.uncurry p)) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) :
    ContDiff ℝ ∞ (Function.uncurry (hierarchyHigherPressureGradient G M κ p f V)) := by
  have hgrad := hierarchyPressureLabelRestriction.contDiff.comp (hp.fderiv_right (m := ∞) (by simp))
  exact ((hG.comp contDiff_fst).clm_apply hgrad).add
    ((hP.comp contDiff_fst).clm_apply (hf.sub (((hM.comp contDiff_fst).clm_apply hV).const_smul _)))

private theorem gradient_higherPressureFinsetSum {ι : Type*} {s : Finset ι} {p : ι → Vec3 → ℝ}
    (hp : ∀ i ∈ s, Differentiable ℝ (p i)) (x : Vec3) :
    gradient (fun y => ∑ i ∈ s, p i y) x = ∑ i ∈ s, gradient (p i) x := by
  unfold gradient
  rw [fderiv_fun_sum (fun i hi => hp i hi x), map_sum]

namespace HierarchyTwistedProfile

variable {T : ℝ} {k₀ : Vec3}

/-- At an active time the exact amplitude-weighted finite norm of a twisted
profile gives its scaled spatial jets. The amplitude is at most one. -/
theorem scaledTwistedProfile_jetBound_of_amplitudeSeminorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ell h t₀ t : ℝ} {n : ℕ}
    (hT : 0 < T) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ r ∈ Icc t₀ T, 0 < γ r)
    (ht : t ∈ Icc t₀ T) (hγ₁ : γ t ≤ 1) (f : HierarchyTwistedProfile T k₀ E) :
    PhaseJetBound n ((4 : ℝ) ^ n * amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hpos f)
      (scaledPhaseProfile ell h (fun a s => f.val.val.val (t,a,s))) := by
  let F (r : Icc t₀ T) (a : Vec3) (s : ℝ) := f.val.val.val (r,a,s)
  let τ (r : Icc t₀ T) : ℝ := γ r
  have hbdd (w) (_ : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ell h) w
        (fun r => (τ r)⁻¹ • Function.uncurry (F r))) :=
    hierarchyTwistedMixedWord_bddAbove_weighted hT ell h False w f
      (Icc_subset_Icc_left ht₀) (fun r => (γ r)⁻¹)
      (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hphase := scaledPhaseProfile_jetBound_of_actual_weightedWordNorm (f := F) (gamma := τ)
    hbdd ⟨t, ht⟩ (hpos t ht)
    (HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val (Icc_subset_Icc_left ht₀ ht))
  intro j hj x
  refine (hphase j hj x).trans ?_
  change γ t * ((4 : ℝ) ^ n * amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hpos f) ≤ _
  exact mul_le_of_le_one_left (by positivity) hγ₁

local notation "VP" => HierarchyTwistedProfile T k₀ Vec3
local notation "SP" => HierarchyTwistedProfile T k₀ ℝ
local notation "MP" => HierarchyTwistedProfile T k₀ Op
local notation "Slice[" f "," t "]" => (fun a s => (Subtype.val (Subtype.val (Subtype.val f))) (t,a,s))
local notation "Label[" f "," t "]" => (fun a => (Subtype.val (Subtype.val (Subtype.val f))) (t,a,0))

set_option maxHeartbeats 1600000 in
/-- The exact higher oscillatory pressure of the finite hierarchy satisfies
(5.52) on the active interval. The per-level inputs are the measured hierarchy
bounds at orders one and two, and one order of weighted parent coefficient jets. -/
theorem norm_higherPressureSum_hessian_of_actualLevels
    {hT : 0 < T} {G M : MP} {κ : VP}
    (solvers : FiniteHierarchySolvers (twistedHierarchyOperators hT G M κ))
    (hSelected : ∀ f hf, ∃ r : TransverseResult hT G M κ f,
      r.output = (solvers.solveTransverse f hf).val)
    (P : ℕ) (completionSwitch parentResidual : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    {freq ell h t₀ t C loss Cjet Aell Kwave : ℝ} {A : Velocity}
    (hfreq : 1 ≤ freq) (hell : 0 < ell) (hhw : h = freq ^ (-1 / 2 : ℝ))
    (hellInv : ell⁻¹ ≤ Aell) (hk : ‖k₀‖ ≤ Kwave * freq)
    (hC : 0 ≤ C) (hLoss : 0 ≤ loss) (hCjet : 0 ≤ Cjet)
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ r ∈ Icc t₀ T, 0 < γ r)
    (ht : t ∈ Icc t₀ T) (hγ₁ : γ t ≤ 1)
    (hA : ContDiff ℝ ∞ (A t))
    (hG : ∀ x, Label[G,t] (A t x) = fderiv ℝ (A t) x)
    (hκ : ∀ a, Label[κ,t] a = (Label[G,t] a).adjoint k₀)
    (hκ₀ : ∀ a, Label[κ,t] a ≠ 0)
    (hGjet : ∀ j ≤ 1, ∀ a, ell ^ j * ‖iteratedFDeriv ℝ j Label[G,t] a‖ ≤ Cjet)
    (hGadjJet : ∀ j ≤ 1, ∀ a,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun b => (Label[G,t] b).adjoint) a‖ ≤ Cjet)
    (hMjet : ∀ j ≤ 1, ∀ a, ell ^ j * ‖iteratedFDeriv ℝ j Label[M,t] a‖ ≤ Cjet)
    (hProjectionJet : ∀ j ≤ 1, ∀ a,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun b => hierarchyLongitudinalProjection (Label[κ,t] b)) a‖ ≤ Cjet) :
    let ops := twistedHierarchyOperators hT G M κ
    let u := solvers.construct P completionSwitch parentResidual hR leading
    let S := actualMeasuredLevels ops u P completionSwitch parentResidual freq
      (zero_le_one.trans hfreq) ell h hT ht₀ htT γ hγ hpos
    (∀ p ∈ Finset.Icc 2 P, HierarchyLevelBound S freq loss C 1 p) →
    (∀ p ∈ Finset.Icc 2 P, HierarchyLevelBound S freq loss C 2 p) →
    ∀ x, ‖fderiv ℝ (gradient (fun y => ∑ p ∈ Finset.Icc 2 P,
      transportedProfile A k₀ (fun _ => Slice[u.p p,t]) t y)) x‖ ≤
      (6 * ((Aell + Kwave) * Cjet)) *
        ((Finset.Icc 2 P).card * (C * (8 * Cjet + (32 * Cjet ^ 2 + 32 * Cjet * Aell) * loss))) *
        freq ^ (-5 / 12 : ℝ) := by
  intro ops u S hlevels1 hlevels2 x
  let s := Finset.Icc 2 P
  have ht' : t ∈ Icc 0 T := Icc_subset_Icc_left ht₀ ht
  have hf₀ : 0 < freq := zero_lt_one.trans_le hfreq
  have hh : 0 < h := hhw.symm ▸ Real.rpow_pos_of_pos hf₀ _
  have hAe : 0 ≤ Aell := (inv_nonneg.mpr hell.le).trans hellInv
  let f (p : ℕ) : VP :=
    let H := ops.sourceBeforeMean u P completionSwitch p
    (-(H - ops.average H)) - hierarchyAdvectionAtLevel P 1 p (ops.meanPhaseProduct u)
  let Grad (p : ℕ) := hierarchyHigherPressureGradient Label[G,t] Label[M,t] Label[κ,t]
    Slice[u.p p,t] Slice[f p,t] Slice[u.V p,t]
  let W (n : ℕ) : Seminorm ℝ VP := amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hpos
  let Q (n : ℕ) : Seminorm ℝ SP := amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hpos
  let B (p : ℕ) := 8 * Cjet * W 1 (f p) + 32 * Cjet ^ 2 * W 1 (u.V p) +
    (32 * Cjet * ell⁻¹) * Q 2 (u.p p)
  let K := s.card * (C * (8 * Cjet + (32 * Cjet ^ 2 + 32 * Cjet * Aell) * loss))
  have hGs : ContDiff ℝ ∞ Label[G,t] :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice G.val.val ht').comp
      (contDiff_id.prodMk contDiff_const)
  have hMs : ContDiff ℝ ∞ Label[M,t] :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice M.val.val ht').comp
      (contDiff_id.prodMk contDiff_const)
  have hκs : ContDiff ℝ ∞ Label[κ,t] :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice κ.val.val ht').comp
      (contDiff_id.prodMk contDiff_const)
  have hProjection := contDiff_hierarchyLongitudinalProjection hκs hκ₀
  have hGadj : ContDiff ℝ ∞ (fun a => (Label[G,t] a).adjoint) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).contDiff.comp hGs
  have hpressure (p : ℕ) : ContDiff ℝ ∞ (Function.uncurry Slice[u.p p,t]) :=
    HierarchySmoothProfile.contDiff_labelPhase_slice (u.p p).val.val ht'
  have hforce (p : ℕ) : ContDiff ℝ ∞ (Function.uncurry Slice[f p,t]) :=
    HierarchySmoothProfile.contDiff_labelPhase_slice (f p).val.val ht'
  have hvelocity (p : ℕ) : ContDiff ℝ ∞ (Function.uncurry Slice[u.V p,t]) :=
    HierarchySmoothProfile.contDiff_labelPhase_slice (u.V p).val.val ht'
  have hGrad (p : ℕ) : ContDiff ℝ ∞ (Function.uncurry (Grad p)) :=
    contDiff_hierarchyHigherPressureGradient hGadj hMs hProjection (hpressure p) (hforce p) (hvelocity p)
  have hgrad (p : ℕ) (hp : p ∈ s) :
      gradient (transportedProfile A k₀ (fun _ => Slice[u.p p,t]) t) =
        transportedProfile A k₀ (fun _ => Grad p) t := by
    obtain ⟨hf, hv, hq⟩ := solvers.construct_transverse_selected hp completionSwitch parentResidual hR leading
    obtain ⟨r, hr⟩ := hSelected (f p) hf
    change u.V p = (solvers.solveTransverse (f p) hf).val.V at hv
    change u.p p = (solvers.solveTransverse (f p) hf).val.p at hq
    rw [← hr] at hv hq
    simpa only [Grad, hv, hq] using r.gradient_transportedPressure_eq ht' (hA.differentiable (by simp)) hG hκ
  have hBg (p : ℕ) : PhaseJetBound 1 (B p) (scaledPhaseProfile ell h (Grad p)) := by
    have hp := scaledTwistedProfile_jetBound_of_amplitudeSeminorm (n := 2) (ell := ell) (h := h)
      hT ht₀ htT γ hγ hpos ht hγ₁ (u.p p)
    have hf := scaledTwistedProfile_jetBound_of_amplitudeSeminorm (n := 1) (ell := ell) (h := h)
      hT ht₀ htT γ hγ hpos ht hγ₁ (f p)
    have hv := scaledTwistedProfile_jetBound_of_amplitudeSeminorm (n := 1) (ell := ell) (h := h)
      hT ht₀ htT γ hγ hpos ht hγ₁ (u.V p)
    have hB := scaledHigherPressureGradient_jetBound (CG := Cjet) (CM := Cjet) (CP := Cjet)
      hell hCjet hCjet hCjet (by positivity) (by positivity) (by positivity)
      hGadj hMs hProjection (hpressure p) (hforce p) (hvelocity p)
      (scaledPhaseCoefficient_jetBound hGadj hell.le hGadjJet)
      (scaledPhaseCoefficient_jetBound hMs hell.le hMjet)
      (scaledPhaseCoefficient_jetBound hProjection hell.le hProjectionJet) hp hf hv
    convert hB using 1
    dsimp [B, W, Q]
    ring
  have hsum : (∑ p ∈ s, B p) ≤ K * freq ^ (-23 / 12 : ℝ) := by
    have he : 32 * Cjet * ell⁻¹ ≤ (32 * Cjet * Aell) * freq :=
      (mul_le_mul_of_nonneg_left hellInv (by positivity)).trans
        (le_mul_of_one_le_right (by positivity) hfreq)
    have hF (p : ℕ) (hp : p ∈ s) : W 1 (f p) = S.oscSource 1 p := by
      have he : p ≠ 1 := by have hp' := (Finset.mem_Icc.mp hp).1; omega
      simp [S, actualMeasuredLevels, HierarchyMeasuredLevels.ofProfiles, he, f, W]
    have hV (p : ℕ) (hp : p ∈ s) : W 1 (u.V p) ≤ C * loss * freq ^ hierarchyOscExponent p :=
      (le_add_of_nonneg_right (mul_nonneg hf₀.le (apply_nonneg (Q 1) (u.p p)))).trans
        (hlevels1 p hp).osc
    have hQ (p : ℕ) (hp : p ∈ s) : freq * Q 2 (u.p p) ≤ C * loss * freq ^ hierarchyOscExponent p :=
      (le_add_of_nonneg_left (apply_nonneg (W 2) (u.V p))).trans (hlevels2 p hp).osc
    have H := higherPressureGradientBudget_sum_le hfreq hC hLoss
      (show 0 ≤ 8 * Cjet by positivity) (show 0 ≤ 32 * Cjet ^ 2 by positivity)
      (show 0 ≤ 32 * Cjet * Aell by positivity) he
      (fun p => W 1 (f p)) (fun p => W 1 (u.V p)) (fun p => Q 2 (u.p p)) B
      (fun p _ => apply_nonneg (Q 2) (u.p p))
      (fun p hp => (hF p hp).trans_le (hlevels1 p hp).oscSource) hV hQ (fun p _ => le_rfl)
    simpa only [K, mul_assoc] using H
  let gradSum (r : ℝ) (a : Vec3) (z : ℝ) := ∑ p ∈ s, Grad p a z
  have hgradSum : ContDiff ℝ ∞ (Function.uncurry (gradSum t)) := by
    change ContDiff ℝ ∞ (fun z : LP => ∑ p ∈ s, Function.uncurry (Grad p) z)
    simpa only [Finset.sum_apply] using (ContDiff.sum (s := s) (fun p _ => hGrad p))
  have hgradjet : PhaseJetBound 1 (∑ p ∈ s, B p) (scaledPhaseProfile ell h (gradSum t)) := by
    apply phaseJetBound_sum_of_level_bounds
    · intro p hp
      exact (((hGrad p).comp (labelPhaseScale ell h).contDiff).of_le (by simp))
    · intro p hp
      exact hBg p
  have hgradient : gradient (fun y => ∑ p ∈ s, transportedProfile A k₀ (fun _ => Slice[u.p p,t]) t y) =
      transportedProfile A k₀ gradSum t := by
    funext y
    have hdiff (p : ℕ) (_ : p ∈ s) : Differentiable ℝ
        (transportedProfile A k₀ (fun _ => Slice[u.p p,t]) t) :=
      ((hpressure p).comp (hA.prodMk ((innerSL ℝ k₀).contDiff.comp hA))).differentiable (by simp)
    rw [gradient_higherPressureFinsetSum hdiff]
    exact Finset.sum_congr rfl (fun p hp => congrFun (hgrad p hp) y)
  have hbudget : 0 ≤ ∑ p ∈ s, B p := by
    apply Finset.sum_nonneg
    intro p hp
    dsimp only [B]
    positivity
  exact norm_higherOscillatory_hessian_le_at_hierarchy_scale hf₀ hell hh hCjet hbudget hA hG hGs
    hgradSum hGjet hgradjet hgradient
    (higherPressureGraphCost_le hfreq hell hCjet hhw hellInv hk) hsum x

/-- The concrete solver retains precisely the velocity and pressure of its
selected transverse result. -/
theorem physicalSolvers_selectsTransverseResult {hT : 0 < T} (hT₁ : T ≤ 1)
    {G M : MP} {κ : VP} (mean : MeanCoefficients G M) (osc : TransverseCoefficients M κ)
    (f : VP) (hf : (twistedHierarchyOperators hT G M κ).average f = 0) :
    ∃ r : TransverseResult hT G M κ f,
      r.output = ((physicalSolvers hT hT₁ G M κ mean osc).solveTransverse f hf).val :=
  ⟨solveTransverse hT G M κ osc f hf, rfl⟩

/-- The time-slab version of the higher pressure bound uses the exact
inactive-set pressure conclusion of the support propagation theorem. -/
theorem norm_higherPressureSum_hessian_le_on_slab_of_support
    {t₀ bound : ℝ} {S : Set Vec3} {P : ℕ} {A : Velocity} (p : ℕ → SP)
    (hb : 0 ≤ bound)
    (hSupport : ∀ i ∈ Finset.Icc 2 P, EqOn (p i).val.val.val 0 (hierarchyInactiveRegion T t₀ S))
    (hActive : ∀ t ∈ Icc t₀ T, ∀ x,
      ‖fderiv ℝ (gradient (fun y => ∑ i ∈ Finset.Icc 2 P,
        transportedProfile A k₀ (fun _ => Slice[p i,t]) t y)) x‖ ≤ bound) :
    ∀ t ∈ Icc 0 T, ∀ x,
      ‖fderiv ℝ (gradient (fun y => ∑ i ∈ Finset.Icc 2 P,
        transportedProfile A k₀ (fun _ => Slice[p i,t]) t y)) x‖ ≤ bound := by
  intro t ht x
  by_cases hlt : t < t₀
  · have hz : (fun y => ∑ i ∈ Finset.Icc 2 P,
        transportedProfile A k₀ (fun _ => Slice[p i,t]) t y) = 0 := by
      funext y
      apply Finset.sum_eq_zero
      intro i hi
      exact hSupport i hi ⟨⟨ht, mem_univ _⟩, Or.inl hlt⟩
    rw [hz]
    have hg : gradient (0 : Vec3 → ℝ) = 0 := gradient_fun_const' (0 : ℝ)
    rw [hg, fderiv_zero, Pi.zero_apply, norm_zero]
    exact hb
  · exact hActive t ⟨le_of_not_gt hlt, ht.2⟩ x

end HierarchyTwistedProfile

end

end TorusEuler
