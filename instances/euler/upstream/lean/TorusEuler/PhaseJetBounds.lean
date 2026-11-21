import TorusEuler.TransportedPhase
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Sum

open ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler

section DirectionalJets

variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coordinate derivative, with a direction field allowed to vary with the base point. -/
noncomputable def phaseDirectionalDerivative (D : U → U) (f : U → E) : U → E :=
  fun x => fderiv ℝ f x (D x)

/-- The first letter of an ordered word is the outermost derivative. -/
noncomputable def phaseOperatorWord {ι : Type*} (D : ι → U → U) :
    List ι → (U → E) → U → E
  | [], f => f
  | i :: w, f => phaseDirectionalDerivative (D i) (phaseOperatorWord D w f)

theorem contDiff_phaseOperatorWord {ι : Type*} {D : ι → U → U} {f : U → E}
    (hD : ∀ i, ContDiff ℝ ∞ (D i)) (hf : ContDiff ℝ ∞ f) (w : List ι) :
    ContDiff ℝ ∞ (phaseOperatorWord D w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact (ih.fderiv_right (by simp)).clm_apply (hD i)

/-- A uniform bound for all Fréchet derivative norms up to the indicated order. -/
def PhaseJetBound (n : ℕ) (C : ℝ) (f : U → E) : Prop :=
  ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C

theorem PhaseJetBound.mono_order {n m : ℕ} {C : ℝ} {f : U → E}
    (h : PhaseJetBound n C f) (hm : m ≤ n) : PhaseJetBound m C f :=
  fun j hj x => h j (hj.trans hm) x

/-- The weighted Leibniz estimate for one operation. The bound on the profile may
include a time weight, since all derivatives here are taken at fixed time. -/
theorem phaseDirectionalDerivative_jetBound {n : ℕ} {C M : ℝ} {D : U → U} {f : U → E}
    (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hcoeff : PhaseJetBound n C D) (hprofile : PhaseJetBound (n + 1) M f) :
    PhaseJetBound n ((2 : ℝ) ^ n * C * M) (phaseDirectionalDerivative D f) := by
  intro j hj x
  have hbinomial : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  calc
    ‖iteratedFDeriv ℝ j (phaseDirectionalDerivative D f) x‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fderiv ℝ f) x‖ * ‖iteratedFDeriv ℝ (j - i) D x‖ :=
      norm_iteratedFDeriv_clm_apply (hf.fderiv_right (by simp)) hD x (by simp)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * M * C := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [norm_iteratedFDeriv_fderiv]
      have hp := hprofile (i + 1) (Nat.succ_le_succ (hij.trans hj)) x
      have hd := hcoeff (j - i) ((Nat.sub_le j i).trans hj) x
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)) hd (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hM)
    _ = (2 : ℝ) ^ j * C * M := by rw [← Finset.sum_mul, ← Finset.sum_mul, hbinomial]; ring
    _ ≤ (2 : ℝ) ^ n * C * M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hC) hM

/-- The iterated Leibniz bound for a word, with the coefficient and profile jet
bounds specified through the working order. -/
theorem phaseOperatorWord_jetBound {ι : Type*} {D : ι → U → U} {f : U → E}
    {N n : ℕ} {C M : ℝ} (w : List ι) (hn : n + w.length ≤ N)
    (hD : ∀ i, ContDiff ℝ ∞ (D i)) (hf : ContDiff ℝ ∞ f)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hcoeff : ∀ i, PhaseJetBound N C (D i))
    (hprofile : PhaseJetBound N M f) :
    PhaseJetBound n (((2 : ℝ) ^ N * C) ^ w.length * M) (phaseOperatorWord D w f) := by
  induction w generalizing n with
  | nil => simpa [phaseOperatorWord] using hprofile.mono_order (by simpa using hn)
  | cons i w ih =>
    have htail : n + 1 + w.length ≤ N := by simpa [Nat.add_assoc, Nat.add_comm 1] using hn
    have hsub : n ≤ N := (Nat.le_add_right _ _).trans hn
    have hderiv := phaseDirectionalDerivative_jetBound (hD i) (contDiff_phaseOperatorWord hD hf w)
      hC (by positivity) ((hcoeff i).mono_order hsub) (ih htail)
    intro j hj x
    refine (hderiv j hj x).trans ?_
    change (2 : ℝ)^n * C * (((2 : ℝ)^N * C)^w.length * M) ≤
      ((2 : ℝ)^N * C)^(w.length + 1) * M
    rw [pow_succ', mul_assoc ((2 : ℝ)^N * C)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hsub) hC) (by positivity)

end DirectionalJets

section Evaluation

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Eulerian coordinate directions in the lift. -/
noncomputable def coordinateDirection (i : Fin 3) : Vec3 := EuclideanSpace.single i 1

/-- The usual ordered coordinate partials of a field on the lift. -/
noncomputable def spatialDerivativeWord : List (Fin 3) → (Vec3 → E) → Vec3 → E :=
  phaseOperatorWord (fun i _ => coordinateDirection i)

/-- The chain rule iterated along a coordinate word, for a graph with a supplied
direction field over each of its Eulerian coordinate derivatives. -/
theorem spatialDerivativeWord_comp {D : Fin 3 → P → P} {G : Vec3 → P} {f : P → E}
    (hG : Differentiable ℝ G) (hD : ∀ i, ContDiff ℝ ∞ (D i)) (hf : ContDiff ℝ ∞ f)
    (hgraph : ∀ i x, fderiv ℝ G x (coordinateDirection i) = D i (G x)) (w : List (Fin 3)) :
    spatialDerivativeWord w (f ∘ G) = phaseOperatorWord D w f ∘ G := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    change fderiv ℝ (spatialDerivativeWord w (f ∘ G)) x (coordinateDirection i) =
      fderiv ℝ (phaseOperatorWord D w f) (G x) (D i (G x))
    rw [ih]
    have hd := (contDiff_phaseOperatorWord hD hf w).differentiable (by simp) (G x)
    rw [(hd.hasFDerivAt.comp x (hG x).hasFDerivAt).fderiv, comp_apply, hgraph]

/-- A spatial derivative word agrees with evaluating the actual Fréchet derivative
in the corresponding ordered coordinate directions. -/
theorem spatialDerivativeWord_eq_iteratedFDeriv {f : Vec3 → E}
    (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) (x : Vec3) :
    spatialDerivativeWord w f x =
      iteratedFDeriv ℝ w.length f x (fun i => coordinateDirection (w.get i)) := by
  induction w generalizing x with
  | nil => simp [spatialDerivativeWord, phaseOperatorWord]
  | cons i w ih =>
    have hw : spatialDerivativeWord w f =
        fun y => iteratedFDeriv ℝ w.length f y (fun j => coordinateDirection (w.get j)) :=
      funext ih
    change fderiv ℝ (spatialDerivativeWord w f) x (coordinateDirection i) =
      iteratedFDeriv ℝ (w.length + 1) f x (fun j => coordinateDirection ((i :: w).get j))
    rw [hw]
    have hd := hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top w.length) x
    rw [hd.iteratedFDeriv_succ_apply_left']
    rfl

end Evaluation

section ScaledProfiles

variable {E : Type*}

/-- Scaling the label by the envelope radius and the phase by the profile width
makes the weighted coordinate derivatives into the ordinary derivatives of a rescaled profile. -/
noncomputable def labelPhaseScale (ℓ h : ℝ) : (Vec3 × ℝ) →L[ℝ] (Vec3 × ℝ) :=
  (ℓ • fst ℝ Vec3 ℝ).prod (h • snd ℝ Vec3 ℝ)

theorem labelPhaseScale_apply (ℓ h : ℝ) (p : Vec3 × ℝ) :
    labelPhaseScale ℓ h p = (ℓ • p.1, h * p.2) := rfl

private theorem labelPhaseScale_left_inv {ℓ h : ℝ} (hℓ : ℓ ≠ 0) (hh : h ≠ 0)
    (p : Vec3 × ℝ) :
    labelPhaseScale ℓ h (labelPhaseScale ℓ⁻¹ h⁻¹ p) = p := by
  simp only [labelPhaseScale_apply, smul_smul, ← mul_assoc, mul_inv_cancel₀ hℓ, mul_inv_cancel₀ hh,
    one_smul, one_mul]

/-- The label-phase displacement, expressed in the scaled coordinates. -/
noncomputable def labelPhaseSlope (ℓ h : ℝ) (k : Vec3) : Vec3 →L[ℝ] (Vec3 × ℝ) :=
  (labelPhaseScale ℓ⁻¹ h⁻¹).comp ((ContinuousLinearMap.id ℝ Vec3).prod (innerSL ℝ k))

theorem labelPhaseSlope_apply (ℓ h : ℝ) (k v : Vec3) :
    labelPhaseSlope ℓ h k v = (ℓ⁻¹ • v, h⁻¹ * ⟪k, v⟫_ℝ) := rfl

/-- The actual phase graph at fixed time, expressed in the scaled coordinates. -/
noncomputable def scaledPhaseGraph (A : Velocity) (k : Vec3) (ℓ h t : ℝ) : Vec3 → Vec3 × ℝ :=
  labelPhaseSlope ℓ h k ∘ A t

/-- The label-phase profile in the coordinates with unit envelope and phase scales. -/
noncomputable def scaledPhaseProfile (ℓ h : ℝ) (f : Vec3 → ℝ → E) : Vec3 × ℝ → E :=
  Function.uncurry f ∘ labelPhaseScale ℓ h

theorem scaledPhaseProfile_comp_graph {A : Velocity} {k : Vec3} {ℓ h t : ℝ}
    (hℓ : ℓ ≠ 0) (hh : h ≠ 0) (f : ℝ → Vec3 → ℝ → E) :
    scaledPhaseProfile ℓ h (f t) ∘ scaledPhaseGraph A k ℓ h t = transportedProfile A k f t := by
  funext x
  have hscale := labelPhaseScale_left_inv hℓ hh (A t x, ⟪k, A t x⟫_ℝ)
  exact congrArg (Function.uncurry (f t)) hscale

/-- The inverse-label derivative in scaled label coordinates. -/
noncomputable def scaledPhaseCoefficient (ℓ : ℝ) (B : Vec3 → Vec3 →L[ℝ] Vec3) :
    (Vec3 × ℝ) → (Vec3 →L[ℝ] Vec3) :=
  fun p => B (ℓ • p.1)

/-- The lifted phase derivative direction obtained from the inverse-label derivative.
Before rescaling this direction is `(B eᵢ, ⟪k, B eᵢ⟫)`. -/
noncomputable def scaledPhaseDirection (ℓ h : ℝ) (k : Vec3) (B : Vec3 → Vec3 →L[ℝ] Vec3)
    (i : Fin 3) : (Vec3 × ℝ) → (Vec3 × ℝ) :=
  fun p => labelPhaseSlope ℓ h k (scaledPhaseCoefficient ℓ B p (coordinateDirection i))

theorem contDiff_scaledPhaseCoefficient {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (hB : ContDiff ℝ ∞ B) (ℓ : ℝ) : ContDiff ℝ ∞ (scaledPhaseCoefficient ℓ B) := by
  exact hB.comp (contDiff_fst.const_smul ℓ)

theorem contDiff_scaledPhaseDirection {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (hB : ContDiff ℝ ∞ B) (ℓ h : ℝ) (k : Vec3) (i : Fin 3) :
    ContDiff ℝ ∞ (scaledPhaseDirection ℓ h k B i) :=
  (labelPhaseSlope ℓ h k).contDiff.comp
    ((contDiff_scaledPhaseCoefficient hB ℓ).clm_apply (contDiff_const (c := coordinateDirection i)))

private theorem fderiv_scaledPhaseGraph_apply {A : Velocity} {k x : Vec3} {ℓ h t : ℝ}
    {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (hℓ : ℓ ≠ 0) (hA : DifferentiableAt ℝ (A t) x)
    (hB : B (A t x) = fderiv ℝ (A t) x) (i : Fin 3) :
    fderiv ℝ (scaledPhaseGraph A k ℓ h t) x (coordinateDirection i) =
      scaledPhaseDirection ℓ h k B i (scaledPhaseGraph A k ℓ h t x) := by
  let L := labelPhaseSlope ℓ h k
  let e := coordinateDirection i
  have hderiv := (L.hasFDerivAt.comp x hA.hasFDerivAt).fderiv
  have hlabel : ℓ • (L (A t x)).1 = A t x := by
    rw [show L (A t x) = (ℓ⁻¹ • A t x, h⁻¹ * ⟪k, A t x⟫_ℝ) from labelPhaseSlope_apply ..]
    simp only [smul_smul, mul_inv_cancel₀ hℓ, one_smul]
  change fderiv ℝ (L ∘ A t) x e = L (B (ℓ • (L (A t x)).1) e)
  rw [hderiv, comp_apply, hlabel, hB]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordered spatial derivatives of the actual transported profile are the ordered
pulled-back phase derivatives evaluated on the transported graph. -/
theorem spatialDerivativeWord_transportedProfile {A : Velocity} {k : Vec3} {t ℓ h : ℝ}
    {B : Vec3 → Vec3 →L[ℝ] Vec3} {f : ℝ → Vec3 → ℝ → E}
    (hℓ : ℓ ≠ 0) (hh : h ≠ 0) (hA : Differentiable ℝ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) (w : List (Fin 3)) :
    spatialDerivativeWord w (transportedProfile A k f t) =
      phaseOperatorWord (scaledPhaseDirection ℓ h k B) w (scaledPhaseProfile ℓ h (f t)) ∘
        scaledPhaseGraph A k ℓ h t := by
  rw [← scaledPhaseProfile_comp_graph hℓ hh f (A := A) (k := k) (t := t)]
  exact spatialDerivativeWord_comp
    ((labelPhaseSlope ℓ h k).differentiable.comp hA)
    (contDiff_scaledPhaseDirection hBreg ℓ h k)
    (hf.comp (labelPhaseScale ℓ h).contDiff)
    (fun i x => fderiv_scaledPhaseGraph_apply hℓ (hA x) (hB x) i) w

/-- The two contributions to the spatial cost are the reciprocal envelope radius
and the wave vector divided by the phase width. -/
theorem norm_labelPhaseSlope_le (ℓ h : ℝ) (k : Vec3) (hℓ : 0 ≤ ℓ) (hh : 0 ≤ h) :
    ‖labelPhaseSlope ℓ h k‖ ≤ ℓ⁻¹ + h⁻¹ * ‖k‖ := by
  have hnℓ := inv_nonneg.mpr hℓ
  have hnh := inv_nonneg.mpr hh
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [labelPhaseSlope_apply, Prod.norm_def, max_le_iff]
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnℓ]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hnh (norm_nonneg k)))
      (norm_nonneg v)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnh]
    calc
      h⁻¹ * |⟪k, v⟫_ℝ| ≤ h⁻¹ * (‖k‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm k v) hnh
      _ ≤ (ℓ⁻¹ + h⁻¹ * ‖k‖) * ‖v‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hnℓ) (norm_nonneg v)

/-- A weighted label jet bound for the inverse differential implies a bound for its
jet in the scaled label-phase coordinates. -/
theorem scaledPhaseCoefficient_jetBound {B : Vec3 → Vec3 →L[ℝ] Vec3} {ℓ C : ℝ} {n : ℕ}
    (hB : ContDiff ℝ ∞ B) (hℓ : 0 ≤ ℓ)
    (hcoeff : ∀ j ≤ n, ∀ a, ℓ ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ C) :
    PhaseJetBound n C (scaledPhaseCoefficient ℓ B) := by
  intro j hj p
  let S := ℓ • fst ℝ Vec3 ℝ
  have hS : ‖S‖ ≤ ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hℓ]
    exact mul_le_of_le_one_right hℓ (ContinuousLinearMap.norm_fst_le ..)
  change ‖iteratedFDeriv ℝ j (B ∘ S) p‖ ≤ C
  rw [S.iteratedFDeriv_comp_right hB p (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j B (S p)‖ * ‖S‖ ^ j := by
      simpa using (iteratedFDeriv ℝ j B (S p)).norm_compContinuousLinearMap_le (fun _ => S)
    _ ≤ ‖iteratedFDeriv ℝ j B (S p)‖ * ℓ ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hS j) (norm_nonneg _)
    _ ≤ C := by rw [mul_comm]; exact hcoeff j hj (S p)

theorem scaledPhaseDirection_jetBound {B : Vec3 → Vec3 →L[ℝ] Vec3} {ℓ h C : ℝ} {n : ℕ}
    (hB : ContDiff ℝ ∞ B) (hℓ : 0 ≤ ℓ) (hh : 0 ≤ h)
    (hcoeff : PhaseJetBound n C (scaledPhaseCoefficient ℓ B)) (k : Vec3) (i : Fin 3) :
    PhaseJetBound n ((ℓ⁻¹ + h⁻¹ * ‖k‖) * C) (scaledPhaseDirection ℓ h k B i) := by
  intro j hj p
  let L := labelPhaseSlope ℓ h k
  let e := coordinateDirection i
  have he : ‖e‖ = 1 := by simp [e, coordinateDirection, EuclideanSpace.single]
  let u : Vec3 × ℝ → Vec3 := fun q => scaledPhaseCoefficient ℓ B q e
  have hc := contDiff_scaledPhaseCoefficient hB ℓ
  have hu : ContDiff ℝ ∞ u := hc.clm_apply contDiff_const
  have hbound : ‖iteratedFDeriv ℝ j u p‖ ≤ C := by
    have h := norm_iteratedFDeriv_clm_apply_const (c := e) hc.contDiffAt (by simp : (j : WithTop ℕ∞) ≤ ∞)
      (x := p)
    rw [he, one_mul] at h
    exact h.trans (hcoeff j hj p)
  change ‖iteratedFDeriv ℝ j (L ∘ u) p‖ ≤ _
  exact (L.norm_iteratedFDeriv_comp_left hu.contDiffAt (by simp)).trans
    (mul_le_mul (norm_labelPhaseSlope_le ℓ h k hℓ hh) hbound (norm_nonneg _) (by positivity))

/-- The physical derivative bound for every ordered spatial word, with explicit label
coefficient input and a profile jet bound carrying a time weight. -/
theorem norm_spatialDerivativeWord_transportedProfile_le {A : Velocity} {k : Vec3}
    {t ℓ h C γ M : ℝ} {B : Vec3 → Vec3 →L[ℝ] Vec3} {f : ℝ → Vec3 → ℝ → E}
    (hℓ : 0 < ℓ) (hh : 0 < h) (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hM : 0 ≤ M)
    (hA : Differentiable ℝ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) (w : List (Fin 3))
    (hcoeff : ∀ j ≤ w.length, ∀ a, ℓ ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ C)
    (hprofile : PhaseJetBound w.length (γ * M) (scaledPhaseProfile ℓ h (f t))) (x : Vec3) :
    ‖spatialDerivativeWord w (transportedProfile A k f t) x‖ ≤
      ((2 : ℝ) ^ w.length * ((ℓ⁻¹ + h⁻¹ * ‖k‖) * C)) ^ w.length * (γ * M) := by
  rw [spatialDerivativeWord_transportedProfile hℓ.ne' hh.ne' hA hB hBreg hf, Function.comp_apply]
  have hstep (i : Fin 3) := scaledPhaseDirection_jetBound hBreg hℓ.le hh.le
    (scaledPhaseCoefficient_jetBound hBreg hℓ.le hcoeff) k i
  have hj := phaseOperatorWord_jetBound (n := 0) w (by simp)
    (contDiff_scaledPhaseDirection hBreg ℓ h k) (hf.comp (labelPhaseScale ℓ h).contDiff)
    (by positivity) (mul_nonneg hγ hM) hstep hprofile
  simpa only [norm_iteratedFDeriv_zero, scaledPhaseProfile] using hj 0 le_rfl (scaledPhaseGraph A k ℓ h t x)

section CoordinateBounds

private theorem norm_multilinear_le_of_coordinate_bounds {ι α P : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (basis : α → P) (coord : P → α → ℝ)
    (hexp : ∀ p, (∑ i, coord p i • basis i) = p)
    (hcoord : ∀ p i, |coord p i| ≤ ‖p‖)
    (D : ContinuousMultilinearMap ℝ (fun _ : ι => P) E) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ i : ι → α, ‖D (fun j => basis (i j))‖ ≤ C) :
    ‖D‖ ≤ (Fintype.card α : ℝ) ^ (Fintype.card ι) * C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro p
  have hsum := D.toMultilinearMap.map_sum (fun j i => coord (p j) i • basis i)
  have hsub : (fun j => ∑ i, coord (p j) i • basis i) = p := funext fun j => hexp (p j)
  rw [hsub] at hsum
  change D p = ∑ r : ι → α, D (fun j => coord (p j) (r j) • basis (r j)) at hsum
  rw [hsum]
  calc
    ‖∑ r : ι → α, D (fun j => coord (p j) (r j) • basis (r j))‖ ≤
        ∑ r : ι → α, ‖D (fun j => coord (p j) (r j) • basis (r j))‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ι → α, C * ∏ j, ‖p j‖ := by
      refine Finset.sum_le_sum fun r _ => ?_
      rw [show D (fun j => coord (p j) (r j) • basis (r j)) =
          (∏ j, coord (p j) (r j)) • D (fun j => basis (r j)) from
        D.toMultilinearMap.map_smul_univ _ _, norm_smul, Real.norm_eq_abs, Finset.abs_prod]
      rw [mul_comm]
      exact mul_le_mul (hD r) (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun _ _ => hcoord _ _))
        (by positivity) hC
    _ = (Fintype.card α : ℝ) ^ (Fintype.card ι) * C * ∏ j, ‖p j‖ := by
      simp [mul_assoc]

private theorem sum_coordinateDirection (a : Vec3) :
    (∑ i, (a i) • coordinateDirection i) = a := by
  apply PiLp.ext
  intro j
  let eval := (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
  change eval (∑ i, a i • coordinateDirection i) = a j
  rw [map_sum]
  simp [eval, coordinateDirection, EuclideanSpace.single, PiLp.single_apply]

/-- The label coordinate directions and the separate phase direction. -/
noncomputable def phaseCoordinateDirection : Fin 3 ⊕ Unit → Vec3 × ℝ
  | .inl i => (coordinateDirection i, 0)
  | .inr _ => (0, 1)

private def phaseCoordinateValue (p : Vec3 × ℝ) : Fin 3 ⊕ Unit → ℝ
  | .inl i => p.1 i
  | .inr _ => p.2

private theorem sum_phaseCoordinateDirection (p : Vec3 × ℝ) :
    (∑ i, phaseCoordinateValue p i • phaseCoordinateDirection i) = p := by
  rw [Fintype.sum_sum_type]
  apply Prod.ext
  · change (fst ℝ Vec3 ℝ)
      ((∑ i : Fin 3, phaseCoordinateValue p (.inl i) • phaseCoordinateDirection (.inl i)) +
        ∑ i : Unit, phaseCoordinateValue p (.inr i) • phaseCoordinateDirection (.inr i)) = _
    rw [map_add, map_sum, map_sum]
    simp [phaseCoordinateDirection, phaseCoordinateValue, sum_coordinateDirection]
  · change (snd ℝ Vec3 ℝ)
      ((∑ i : Fin 3, phaseCoordinateValue p (.inl i) • phaseCoordinateDirection (.inl i)) +
        ∑ i : Unit, phaseCoordinateValue p (.inr i) • phaseCoordinateDirection (.inr i)) = _
    rw [map_add, map_sum, map_sum]
    simp [phaseCoordinateDirection, phaseCoordinateValue]

private theorem abs_phaseCoordinateValue_le (p : Vec3 × ℝ) (i : Fin 3 ⊕ Unit) :
    |phaseCoordinateValue p i| ≤ ‖p‖ := by
  cases i with
  | inl j => exact (PiLp.norm_apply_le p.1 j).trans (norm_fst_le p)
  | inr j => exact norm_snd_le p

/-- Each label letter contributes the envelope scale and each phase letter the
profile width. Their product is the weight of a mixed derivative word. -/
def phaseCoordinateWeight (ℓ h : ℝ) : Fin 3 ⊕ Unit → ℝ
  | .inl _ => ℓ
  | .inr _ => h

theorem labelPhaseScale_phaseCoordinateDirection (ℓ h : ℝ) (i : Fin 3 ⊕ Unit) :
    labelPhaseScale ℓ h (phaseCoordinateDirection i) =
      phaseCoordinateWeight ℓ h i • phaseCoordinateDirection i := by
  cases i <;> simp [labelPhaseScale_apply, phaseCoordinateDirection, phaseCoordinateWeight,
    Prod.smul_mk, smul_eq_mul]

/-- Scaling a mixed derivative multiplies it by one envelope radius per label
letter and one phase width per phase letter. -/
theorem iteratedFDeriv_scaledPhaseProfile_apply_coordinate {f : Vec3 → ℝ → E} {j : ℕ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (ℓ h : ℝ)
    (p : Vec3 × ℝ) (i : Fin j → Fin 3 ⊕ Unit) :
    iteratedFDeriv ℝ j (scaledPhaseProfile ℓ h f) p (fun r => phaseCoordinateDirection (i r)) =
      (∏ r, phaseCoordinateWeight ℓ h (i r)) •
        iteratedFDeriv ℝ j (Function.uncurry f) (labelPhaseScale ℓ h p)
          (fun r => phaseCoordinateDirection (i r)) := by
  unfold scaledPhaseProfile
  rw [(labelPhaseScale ℓ h).iteratedFDeriv_comp_right hf p (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    labelPhaseScale_phaseCoordinateDirection]
  exact (iteratedFDeriv ℝ j (Function.uncurry f) (labelPhaseScale ℓ h p)).toMultilinearMap.map_smul_univ _ _

/-- The coordinate bounds on weighted mixed derivatives imply the rescaled
Fréchet jet bound with a dimension factor depending only on the order. -/
theorem scaledPhaseProfile_jetBound_of_coordinateBounds {f : Vec3 → ℝ → E} {n : ℕ} {M : ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hM : 0 ≤ M) (ℓ h : ℝ)
    (hcoord : ∀ j ≤ n, ∀ (p : Vec3 × ℝ) (i : Fin j → Fin 3 ⊕ Unit),
      ‖(∏ r, phaseCoordinateWeight ℓ h (i r)) •
        iteratedFDeriv ℝ j (Function.uncurry f) p (fun r => phaseCoordinateDirection (i r))‖ ≤ M) :
    PhaseJetBound n ((4 : ℝ) ^ n * M) (scaledPhaseProfile ℓ h f) := by
  intro j hj p
  have hbasis (i : Fin j → Fin 3 ⊕ Unit) :
      ‖iteratedFDeriv ℝ j (scaledPhaseProfile ℓ h f) p (fun r => phaseCoordinateDirection (i r))‖ ≤ M := by
    rw [iteratedFDeriv_scaledPhaseProfile_apply_coordinate hf]
    exact hcoord j hj _ i
  have hbound := norm_multilinear_le_of_coordinate_bounds phaseCoordinateDirection phaseCoordinateValue
    sum_phaseCoordinateDirection abs_phaseCoordinateValue_le
    (iteratedFDeriv ℝ j (scaledPhaseProfile ℓ h f) p) hM hbasis
  have hsmall : ‖iteratedFDeriv ℝ j (scaledPhaseProfile ℓ h f) p‖ ≤ (4 : ℝ) ^ j * M := by
    simpa [Fintype.card_sum] using hbound
  exact hsmall.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hM)

/-- In operator norm, the actual Eulerian jet has the same frequency power.
The additional factor (3^m) compares the coordinate components with the
multilinear operator norm. -/
theorem norm_iteratedFDeriv_transportedProfile_le {A : Velocity} {k : Vec3}
    {t ℓ h C γ M : ℝ} {B : Vec3 → Vec3 →L[ℝ] Vec3} {f : ℝ → Vec3 → ℝ → E}
    (hℓ : 0 < ℓ) (hh : 0 < h) (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hM : 0 ≤ M)
    (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) (m : ℕ)
    (hcoeff : ∀ j ≤ m, ∀ a, ℓ ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ C)
    (hprofile : PhaseJetBound m (γ * M) (scaledPhaseProfile ℓ h (f t))) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (transportedProfile A k f t) x‖ ≤
      (3 : ℝ) ^ m * (((2 : ℝ) ^ m * ((ℓ⁻¹ + h⁻¹ * ‖k‖) * C)) ^ m * (γ * M)) := by
  let g := transportedProfile A k f t
  let bound := ((2 : ℝ) ^ m * ((ℓ⁻¹ + h⁻¹ * ‖k‖) * C)) ^ m * (γ * M)
  have hcomp := hf.comp (hA.prodMk ((innerSL ℝ k).contDiff.comp hA))
  have hg : ContDiff ℝ ∞ g := hcomp
  have hdir (i : Fin m → Fin 3) :
      ‖iteratedFDeriv ℝ m g x (fun j => coordinateDirection (i j))‖ ≤ bound := by
    have hword := norm_spatialDerivativeWord_transportedProfile_le (A := A) (k := k)
      hℓ hh hC hγ hM (hA.differentiable (by simp)) hB hBreg hf (List.ofFn i)
      (by simpa only [List.length_ofFn] using hcoeff)
      (by simpa only [List.length_ofFn] using hprofile) x
    rw [spatialDerivativeWord_eq_iteratedFDeriv hg] at hword
    simp only [List.get_ofFn] at hword
    have hcast {n : ℕ} (hn : n = m) :
        iteratedFDeriv ℝ n g x (fun j => coordinateDirection (i (Fin.cast hn j))) =
          iteratedFDeriv ℝ m g x (fun j => coordinateDirection (i j)) := by subst n; rfl
    rw [hcast (List.length_ofFn (f := i))] at hword
    simpa only [List.length_ofFn] using hword
  have hb : 0 ≤ bound := by dsimp [bound]; positivity
  have hnorm := norm_multilinear_le_of_coordinate_bounds coordinateDirection
    (fun a : Vec3 => fun i => a i) sum_coordinateDirection
    (fun a i => PiLp.norm_apply_le a i) (iteratedFDeriv ℝ m g x) hb hdir
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using hnorm

end CoordinateBounds

end ScaledProfiles

section Holder

variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The half-Hölder difference bound from two adjacent uniform jet bounds.
The square root records the geometric-mean estimate of Appendix D. -/
theorem norm_iteratedFDeriv_sub_le_sqrt {f : U → E} {m : ℕ} {M L : ℝ}
    (hf : ContDiff ℝ ∞ f) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hval : ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ M)
    (hderiv : ∀ x, ‖iteratedFDeriv ℝ (m + 1) f x‖ ≤ L) (x y : U) :
    ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤
      Real.sqrt (2 * M * L) * Real.sqrt ‖x - y‖ := by
  let g := iteratedFDeriv ℝ m f
  have hd := hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top m)
  have hdiff : ‖g x - g y‖ ≤ L * ‖x - y‖ :=
    (convex_univ : Convex ℝ (Set.univ : Set U)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hd z) (fun z _ => by rw [norm_fderiv_iteratedFDeriv]; exact hderiv z)
      (Set.mem_univ y) (Set.mem_univ x)
  have hsum : ‖g x - g y‖ ≤ 2 * M := by
    rw [two_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hval x) (hval y))
  have hsq : ‖g x - g y‖ ^ 2 ≤ 2 * M * (L * ‖x - y‖) := by
    rw [sq]
    exact mul_le_mul hsum hdiff (norm_nonneg _) (by positivity)
  have hbound := Real.le_sqrt_of_sq_le hsq
  rwa [← mul_assoc, Real.sqrt_mul (by positivity)] at hbound

end Holder

end TorusEuler
