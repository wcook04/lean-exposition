import Breakdown.Cert.CoercivePassageCommon
import Breakdown.Cert.CoerciveField
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoercivePieceAbsorbMeasure

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassageModes

open ModeRotation

theorem axialRot_sub (φ : ℝ) (a b : Space) : axialRot φ (a - b) = axialRot φ a - axialRot φ b := by
  ext i
  fin_cases i <;> simp [axialRot, unitVector] <;> ring

theorem integrable_exp_mul {f : ℝ × ℝ → ℝ} (hf : Integrable f boxMeasure) (ι : ℤ × ℤ) :
    Integrable (fun p : ℝ × ℝ => expFactor ι p.1 p.2 * ((f p : ℝ) : ℂ)) boxMeasure := by
  refine hf.norm.mono' (((continuous_expFactor ι).aestronglyMeasurable).mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1)) (Eventually.of_forall fun p => ?_)
  simp only [norm_mul, norm_expFactor, one_mul, Complex.norm_real, le_refl]

theorem integrable_secondDerivComponent {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => H (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (k : Fin 3 × Fin 3 × Fin 3) :
    Integrable (fun p : ℝ × ℝ => axialRot (-p.2) (H (z.1 + p.1) (axialRot p.2 z.2)
      (axialRot p.2 (unitVector k.2.1)) (axialRot p.2 (unitVector k.2.2))) k.1) boxMeasure := by
  refine hz.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
  · have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot (-q.1) (q.2 (axialRot q.1 (unitVector k.2.1)) (axialRot q.1 (unitVector k.2.2))) k.1) := by
      unfold axialRot
      fun_prop
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.2, H (z.1 + p.1) (axialRot p.2 z.2))) boxMeasure :=
      continuous_snd.aestronglyMeasurable.prodMk hz.1
    have h2 := hc.comp_aestronglyMeasurable hm
    exact h2
  · refine (PiLp.norm_apply_le _ k.1).trans ?_
    rw [norm_axialRot axialRotationHolds_proof]
    refine ((H (z.1 + p.1) (axialRot p.2 z.2)).le_opNorm₂ _ _).trans ?_
    simp [norm_axialRot axialRotationHolds_proof, unitVector]

theorem modeVel_sub_of {X Y : ℝ → Space → Space} {z : ℝ × Space}
    (hX : Integrable (fun p : ℝ × ℝ => X (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (hY : Integrable (fun p : ℝ × ℝ => Y (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) (ι : ℤ × ℤ) :
    modeVel ι (fun σ y => X σ y - Y σ y) z.1 z.2 = modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2 := by
  funext i
  have h1 := integrable_exp_mul (integrable_velComponent axialRotationHolds_proof hX i) ι
  have h2 := integrable_exp_mul (integrable_velComponent axialRotationHolds_proof hY i) ι
  beta_reduce at h1 h2
  have e1 := iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (X (z.1 + τ) (axialRot φ z.2)) i : ℝ) : ℂ)) h1
  have e2 := iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (Y (z.1 + τ) (axialRot φ z.2)) i : ℝ) : ℂ)) h2
  have e3 := iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (X (z.1 + τ) (axialRot φ z.2)) i : ℝ) : ℂ)
    - expFactor ι τ φ * ((axialRot (-φ) (Y (z.1 + τ) (axialRot φ z.2)) i : ℝ) : ℂ)) (h1.sub h2)
  beta_reduce at e1 e2 e3
  simp only [modeVel, modeAverage_eq, Pi.sub_apply, axialRot_sub, PiLp.sub_apply, Complex.ofReal_sub, mul_sub]
  rw [e1, e2, e3, integral_sub h1 h2]
  ring

theorem modeGrad_sub_of {G₁ G₂ : ℝ → Space → (Space →L[ℝ] Space)} {z : ℝ × Space}
    (hX : Integrable (fun p : ℝ × ℝ => G₁ (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (hY : Integrable (fun p : ℝ × ℝ => G₂ (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) (ι : ℤ × ℤ) :
    modeGrad ι (fun σ y => G₁ σ y - G₂ σ y) z.1 z.2 = modeGrad ι G₁ z.1 z.2 - modeGrad ι G₂ z.1 z.2 := by
  funext ij
  have h1 := integrable_exp_mul (integrable_gradComponent axialRotationHolds_proof hX ij) ι
  have h2 := integrable_exp_mul (integrable_gradComponent axialRotationHolds_proof hY ij) ι
  beta_reduce at h1 h2
  have e1 := iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (G₁ (z.1 + τ) (axialRot φ z.2)
    (axialRot φ (unitVector ij.2))) ij.1 : ℝ) : ℂ)) h1
  have e2 := iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (G₂ (z.1 + τ) (axialRot φ z.2)
    (axialRot φ (unitVector ij.2))) ij.1 : ℝ) : ℂ)) h2
  have e3 := iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (G₁ (z.1 + τ) (axialRot φ z.2)
    (axialRot φ (unitVector ij.2))) ij.1 : ℝ) : ℂ) - expFactor ι τ φ * ((axialRot (-φ) (G₂ (z.1 + τ)
    (axialRot φ z.2) (axialRot φ (unitVector ij.2))) ij.1 : ℝ) : ℂ)) (h1.sub h2)
  beta_reduce at e1 e2 e3
  simp only [modeGrad, modeAverage_eq, Pi.sub_apply, ContinuousLinearMap.sub_apply, axialRot_sub,
    PiLp.sub_apply, Complex.ofReal_sub, mul_sub]
  rw [e1, e2, e3, integral_sub h1 h2]
  ring

theorem modeSecondDeriv_sub_of {H₁ H₂ : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {z : ℝ × Space}
    (hX : Integrable (fun p : ℝ × ℝ => H₁ (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (hY : Integrable (fun p : ℝ × ℝ => H₂ (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) (ι : ℤ × ℤ) :
    modeSecondDeriv ι (fun σ y => H₁ σ y - H₂ σ y) z.1 z.2 = modeSecondDeriv ι H₁ z.1 z.2 - modeSecondDeriv ι H₂ z.1 z.2 := by
  funext k
  have h1 := integrable_exp_mul (integrable_secondDerivComponent hX k) ι
  have h2 := integrable_exp_mul (integrable_secondDerivComponent hY k) ι
  beta_reduce at h1 h2
  have e1 := iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (H₁ (z.1 + τ) (axialRot φ z.2)
    (axialRot φ (unitVector k.2.1)) (axialRot φ (unitVector k.2.2))) k.1 : ℝ) : ℂ)) h1
  have e2 := iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (H₂ (z.1 + τ) (axialRot φ z.2)
    (axialRot φ (unitVector k.2.1)) (axialRot φ (unitVector k.2.2))) k.1 : ℝ) : ℂ)) h2
  have e3 := iter_eq_prod (fun τ φ => expFactor ι τ φ * ((axialRot (-φ) (H₁ (z.1 + τ) (axialRot φ z.2)
    (axialRot φ (unitVector k.2.1)) (axialRot φ (unitVector k.2.2))) k.1 : ℝ) : ℂ)
    - expFactor ι τ φ * ((axialRot (-φ) (H₂ (z.1 + τ) (axialRot φ z.2)
    (axialRot φ (unitVector k.2.1)) (axialRot φ (unitVector k.2.2))) k.1 : ℝ) : ℂ)) (h1.sub h2)
  beta_reduce at e1 e2 e3
  simp only [modeSecondDeriv, modeAverage_eq, Pi.sub_apply, ContinuousLinearMap.sub_apply, axialRot_sub,
    PiLp.sub_apply, Complex.ofReal_sub, mul_sub]
  rw [e1, e2, e3, integral_sub h1 h2]
  ring

def weightedDiff (X Y : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space := (1 + ‖y‖)⁻¹ • (X σ y - Y σ y)

theorem modeVel_weightedDiff (X Y : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (weightedDiff X Y) σ y =
      fun i => (((1 + ‖y‖)⁻¹ : ℝ) : ℂ) * modeVel ι (fun σ y => X σ y - Y σ y) σ y i := by
  funext i
  unfold modeVel
  rw [← Field.modeAverage_const_mul]
  congr 1
  funext τ φ b
  simp only [weightedDiff, Field.axialRot_smul, norm_axialRot axialRotationHolds_proof, PiLp.smul_apply,
    smul_eq_mul]

theorem cnormSq_const_mul {β : Type*} [Fintype β] (c : ℂ) (x : β → ℂ) :
    cnormSq (fun b => c * x b) = ‖c‖ ^ 2 * cnormSq x := by
  simp only [cnormSq, norm_mul, mul_pow, Finset.mul_sum]

theorem tendsto_of_cnormSq {β : Type*} [Fintype β] {a : ℕ → β → ℂ} {a₀ : β → ℂ}
    (h : Tendsto (fun n => cnormSq (a n - a₀)) atTop (𝓝 0)) : Tendsto a atTop (𝓝 a₀) := by
  rw [tendsto_pi_nhds]
  intro b
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun n => Real.sqrt (cnormSq (a n - a₀))) atTop (𝓝 0) := by
    simpa using h.sqrt
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hs
  rw [← Real.sqrt_sq (norm_nonneg (a n b - a₀ b))]
  apply Real.sqrt_le_sqrt
  have := Finset.single_le_sum (f := fun b => ‖(a n - a₀) b‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ b)
  simpa [cnormSq] using this

def restOfAmps {C : Type} (m : ModeWeights C) (w : Space → ℝ) (W : ℝ → Space → Space) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) (a b c d e : ℤ × ℤ → ℝ) : ℝ :=
  baseDensity m.convD m.convZ (m.classOf ι) m.c w y (d ι) (e ι) (b ι) (c ι) (a ι)
    + (-((m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y) * e ι * c ι)
      - m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|) * c ι ^ 2
      - m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * a ι * c ι
      - m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖ * b ι * c ι
      - m.eps ι y * c ι * ∑ α ∈ m.waves,
        (velAmp W α σ y * e (ι - α) + gradAmp (gradField W) α σ y * c (ι - α)
          + vortGradAmp (secondDerivField W) α σ y * a (ι - α)
          + vortAmp (gradField W) α σ y * b (ι - α)))
    + (-((m.mu ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.muGrad ι y) * b ι * a ι)
      - m.mu ι y * |m.rate (m.classOf ι) y| * a ι ^ 2
      - m.mu ι y * a ι * ∑ α ∈ m.waves, velAmp W α σ y * b (ι - α)
      - ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0)
        * ((‖fderiv ℝ (meanField W) y‖ ^ 2 * a ι ^ 2
            + (∑ α ∈ m.waves, gradAmp (gradField W) α σ y * a (ι - α)) ^ 2) / m.eta (m.classOf ι)
          + (1 / 2) * m.eta (m.classOf ι) * m.mu ι y ^ 2 * a ι ^ 2))

theorem modeRest_eq {C : Type} (m : ModeWeights C) (w : Space → ℝ) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeRest m w W v G H ι σ y = restOfAmps m w W ι σ y (fun κ => velAmp v κ σ y) (fun κ => gradAmp G κ σ y)
      (fun κ => vortAmp G κ σ y) (fun κ => secondDerivAmp H κ σ y) (fun κ => vortGradAmp H κ σ y) := rfl

theorem continuous_restOfAmps {C : Type} (m : ModeWeights C) (w : Space → ℝ) (W : ℝ → Space → Space)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    Continuous (fun t : (ℤ × ℤ → ℝ) × (ℤ × ℤ → ℝ) × (ℤ × ℤ → ℝ) × (ℤ × ℤ → ℝ) × (ℤ × ℤ → ℝ) =>
      restOfAmps m w W ι σ y t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) := by
  unfold restOfAmps baseDensity
  fun_prop

def stretchOf (W : ℝ → Space → Space) (σ : ℝ) (y : Space) (p : Space × (Space →L[ℝ] Space)) : ℝ :=
  stretchForm W (fun _ _ => p.1) (fun _ _ => p.2) σ y

theorem stretchForm_eq_of (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    stretchForm W v G σ y = stretchOf W σ y (v σ y, G σ y) := by
  unfold stretchOf stretchForm
  rfl

theorem continuous_stretchForm (W : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    Continuous (stretchOf W σ y) := by
  unfold stretchOf stretchForm curlVec
  fun_prop

theorem limits_of_modes {C : Type} (m : ModeWeights C) (P : ℝ) (w : Space → ℝ) (W : ℝ → Space → Space)
    {U : ℕ → ℝ → Space → Space} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {σ : ℝ} {y : Space}
    (hV : ∀ κ, Tendsto (fun n => modeVel κ (U n) σ y) atTop (𝓝 (modeVel κ v σ y)))
    (hG : ∀ κ, Tendsto (fun n => modeGrad κ (gradField (U n)) σ y) atTop (𝓝 (modeGrad κ G σ y)))
    (hH : ∀ κ, Tendsto (fun n => modeSecondDeriv κ (secondDerivField (U n)) σ y) atTop (𝓝 (modeSecondDeriv κ H σ y)))
    (hu0 : Tendsto (fun n => U n σ y) atTop (𝓝 (v σ y)))
    (hg0 : Tendsto (fun n => gradField (U n) σ y) atTop (𝓝 (G σ y))) :
    (∀ ι, Tendsto (fun n => modePos m P (U n) (gradField (U n)) ι σ y) atTop
        (𝓝 (modePos m P v G ι σ y))) ∧
      (∀ ι, Tendsto (fun n => modeRest m w W (U n) (gradField (U n)) (secondDerivField (U n)) ι σ y)
        atTop (𝓝 (modeRest m w W v G H ι σ y))) ∧
      Tendsto (fun n => stretchForm W (U n) (gradField (U n)) σ y) atTop
        (𝓝 (stretchForm W v G σ y)) := by
  have hc1 : Continuous (fun x : Fin 3 → ℂ => Real.sqrt (cnormSq x)) :=
    Real.continuous_sqrt.comp FieldModes.continuous_cnormSq
  have hc2 : Continuous (fun x : Fin 3 × Fin 3 → ℂ => Real.sqrt (cnormSq x)) :=
    Real.continuous_sqrt.comp FieldModes.continuous_cnormSq
  have hc3 : Continuous (fun x : Fin 3 × Fin 3 × Fin 3 → ℂ => Real.sqrt (cnormSq x)) :=
    Real.continuous_sqrt.comp FieldModes.continuous_cnormSq
  have hcurl : Continuous (fun x : Fin 3 × Fin 3 → ℂ => curlOfGrad x) :=
    continuous_pi fun i => by
      simp only [curlOfGrad]
      fun_prop
  have hcurlH : Continuous (fun x : Fin 3 × Fin 3 × Fin 3 → ℂ => curlGradOfSecondDeriv x) :=
    continuous_pi fun i => by
      simp only [curlGradOfSecondDeriv]
      fun_prop
  have hva : ∀ κ, Tendsto (fun n => velAmp (U n) κ σ y) atTop (𝓝 (velAmp v κ σ y)) := fun κ =>
    (hc1.tendsto _).comp (hV κ)
  have hga : ∀ κ, Tendsto (fun n => gradAmp (gradField (U n)) κ σ y) atTop (𝓝 (gradAmp G κ σ y)) := fun κ =>
    (hc2.tendsto _).comp (hG κ)
  have hta : ∀ κ, Tendsto (fun n => vortAmp (gradField (U n)) κ σ y) atTop (𝓝 (vortAmp G κ σ y)) := fun κ =>
    ((Real.continuous_sqrt.comp FieldModes.continuous_cnormSq).comp hcurl |>.tendsto _).comp (hG κ)
  have hha : ∀ κ, Tendsto (fun n => secondDerivAmp (secondDerivField (U n)) κ σ y) atTop (𝓝 (secondDerivAmp H κ σ y)) := fun κ =>
    (hc3.tendsto _).comp (hH κ)
  have hwa : ∀ κ, Tendsto (fun n => vortGradAmp (secondDerivField (U n)) κ σ y) atTop (𝓝 (vortGradAmp H κ σ y)) :=
    fun κ => ((Real.continuous_sqrt.comp FieldModes.continuous_cnormSq).comp hcurlH |>.tendsto _).comp (hH κ)
  refine ⟨fun ι => ?_, fun ι => ?_, ?_⟩
  · unfold modePos modeEpsPos modeMuPos
    exact (((hta ι).pow 2).const_mul _).add (((hva ι).pow 2).const_mul _)
  · simp only [modeRest_eq]
    have ht := (tendsto_pi_nhds.2 hva).prodMk_nhds ((tendsto_pi_nhds.2 hga).prodMk_nhds
      ((tendsto_pi_nhds.2 hta).prodMk_nhds ((tendsto_pi_nhds.2 hha).prodMk_nhds (tendsto_pi_nhds.2 hwa))))
    have h := ((continuous_restOfAmps m w W ι σ y).tendsto _).comp ht
    exact h
  · have e : ∀ n, stretchForm W (U n) (gradField (U n)) σ y = stretchOf W σ y (U n σ y, gradField (U n) σ y) :=
      fun n => stretchForm_eq_of W (U n) (gradField (U n)) σ y
    have h := ((continuous_stretchForm W σ y).tendsto (v σ y, G σ y)).comp (hu0.prodMk_nhds hg0)
    rw [← stretchForm_eq_of W v G σ y] at h
    exact h.congr fun n => (e n).symm

def modeDiff (u : ℕ → ℝ → Space → Space) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (j : ℕ) (κ : ℤ × ℤ) (n : ℕ) (σ : ℝ) (y : Space) :
    ℝ≥0∞ :=
  if j = 0 then ENNReal.ofReal (cnormSq (modeVel κ (weightedDiff (u n) v) σ y))
  else if j = 1 then ENNReal.ofReal (cnormSq (modeGrad κ (fun σ y => gradField (u n) σ y - G σ y) σ y))
  else ENNReal.ofReal (cnormSq (modeSecondDeriv κ (fun σ y => secondDerivField (u n) σ y - H σ y) σ y))

def modeIndex : ℕ ≃ ℤ × ℤ := (Denumerable.eqv (ℤ × ℤ)).symm

def diffModes (u : ℕ → ℝ → Space → Space) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (k n : ℕ) (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  modeDiff u v G H k.unpair.1 (modeIndex k.unpair.2) n σ y

theorem diffModes_pair (u : ℕ → ℝ → Space → Space) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (j : ℕ) (κ : ℤ × ℤ) (n : ℕ) (σ : ℝ) (y : Space) :
    diffModes u v G H (Nat.pair j (modeIndex.symm κ)) n σ y = modeDiff u v G H j κ n σ y := by
  simp only [diffModes, Nat.unpair_pair, Equiv.apply_symm_apply]

section Measure

variable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space}

theorem weightedDiff_measurable {X Y : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => weightedDiff X Y z.1 z.2) volume := by
  have hc : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖)⁻¹) :=
    (continuous_const.add continuous_snd.norm).inv₀ fun z => (add_pos_of_pos_of_nonneg one_pos (norm_nonneg z.2)).ne'
  exact hc.aestronglyMeasurable.smul (hX.sub hY)

theorem modeDiff_aemeasurable (hSP : SmoothPerturbationIsPerturbationHolds)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) (j : ℕ) (κ : ℤ × ℤ) (n : ℕ) :
    AEMeasurable (fun z : ℝ × Space => modeDiff u v G H j κ n z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hp := hSP P (u n) (hu.1 n)
  unfold modeDiff
  by_cases h0 : j = 0
  · simp only [if_pos h0]
    exact PieceAbsorb.aemeasurable_ofReal_cnormSq (FieldModes.aemeasurable_modeVel
      (weightedDiff_measurable hp.measurable_velocity hv.measurable_velocity) κ)
  · by_cases h1 : j = 1
    · simp only [if_neg h0, if_pos h1]
      exact PieceAbsorb.aemeasurable_ofReal_cnormSq (FieldModes.aemeasurable_modeGrad
        (hp.measurable_gradient.sub hv.measurable_gradient) κ)
    · simp only [if_neg h0, if_neg h1]
      exact PieceAbsorb.aemeasurable_ofReal_cnormSq (PieceAbsorb.aemeasurable_modeSecondDeriv
        (hp.measurable_secondDeriv.sub hv.measurable_secondDeriv) κ)

theorem vel_diff_tendsto (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) (κ : ℤ × ℤ) :
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (cnormSq (modeVel κ (weightedDiff (u n) v) σ y))) atTop (𝓝 0) := by
  have hpt : ∀ n σ y, ‖weightedDiff (u n) v σ y‖ ^ 2 = ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := by
    intro n σ y
    have h0 : 0 < 1 + ‖y‖ := by positivity
    rw [weightedDiff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h0, mul_pow, inv_pow, div_eq_inv_mul]
  have hT : Tendsto (fun n => periodLIntegral (fun σ y => ‖weightedDiff (u n) v σ y‖ ^ 2)) atTop (𝓝 0) := by
    simp only [hpt]
    exact hu.2.2.2.1
  have hfin := (tendsto_order.1 hT).2 ⊤ ENNReal.zero_lt_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hfin] with n hn
  have hp := hSP P (u n) (hu.1 n)
  have hper : IsTimePeriodic (weightedDiff (u n) v) := fun σ y => by
    simp only [weightedDiff, hp.periodic_velocity σ y, hv.periodic_velocity σ y]
  rw [hPars.1 (weightedDiff (u n) v) (weightedDiff_measurable hp.measurable_velocity hv.measurable_velocity)
    hper hn]
  exact ENNReal.le_tsum (f := fun κ' : ℤ × ℤ => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
    ENNReal.ofReal (cnormSq (modeVel κ' (weightedDiff (u n) v) σ y))) κ

theorem grad_diff_tendsto (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) (κ : ℤ × ℤ) :
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (cnormSq (modeGrad κ (fun σ y => gradField (u n) σ y - G σ y) σ y))) atTop (𝓝 0) := by
  have hT := hu.2.1
  have hfin := (tendsto_order.1 hT).2 ⊤ ENNReal.zero_lt_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hfin] with n hn
  have hp := hSP P (u n) (hu.1 n)
  have hper : IsTimePeriodic (fun σ y => gradField (u n) σ y - G σ y) := fun σ y => by
    simp only [hp.periodic_gradient σ y, hv.periodic_gradient σ y]
  rw [hPars.2.1 (fun σ y => gradField (u n) σ y - G σ y) (hp.measurable_gradient.sub hv.measurable_gradient)
    hper hn]
  exact ENNReal.le_tsum (f := fun κ' : ℤ × ℤ => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
    ENNReal.ofReal (cnormSq (modeGrad κ' (fun σ y => gradField (u n) σ y - G σ y) σ y))) κ

theorem secondDeriv_diff_tendsto (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) (κ : ℤ × ℤ) :
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal (cnormSq (modeSecondDeriv κ (fun σ y => secondDerivField (u n) σ y - H σ y) σ y))) atTop (𝓝 0) := by
  have hT := hu.2.2.1
  have hfin := (tendsto_order.1 hT).2 ⊤ ENNReal.zero_lt_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hfin] with n hn
  have hp := hSP P (u n) (hu.1 n)
  have hper : IsTimePeriodic (fun σ y => secondDerivField (u n) σ y - H σ y) := fun σ y => by
    simp only [hp.periodic_secondDeriv σ y, hv.periodic_secondDeriv σ y]
  rw [hPars.2.2.1 (fun σ y => secondDerivField (u n) σ y - H σ y) (hp.measurable_secondDeriv.sub hv.measurable_secondDeriv)
    hper hn]
  exact ENNReal.le_tsum (f := fun κ' : ℤ × ℤ => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
    ENNReal.ofReal (cnormSq (modeSecondDeriv κ' (fun σ y => secondDerivField (u n) σ y - H σ y) σ y))) κ

theorem modeDiff_tendsto (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) (j : ℕ) (κ : ℤ × ℤ) :
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, modeDiff u v G H j κ n σ y) atTop (𝓝 0) := by
  unfold modeDiff
  by_cases h0 : j = 0
  · simp only [if_pos h0]
    exact vel_diff_tendsto hPars hSP hv hu κ
  · by_cases h1 : j = 1
    · simp only [if_neg h0, if_pos h1]
      exact grad_diff_tendsto hPars hSP hv hu κ
    · simp only [if_neg h0, if_neg h1]
      exact secondDeriv_diff_tendsto hPars hSP hv hu κ

theorem modeDiff_zero (u : ℕ → ℝ → Space → Space) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (κ : ℤ × ℤ) (n : ℕ) (σ : ℝ) (y : Space) :
    modeDiff u v G H 0 κ n σ y = ENNReal.ofReal (cnormSq (modeVel κ (weightedDiff (u n) v) σ y)) := by
  rw [modeDiff, if_pos rfl]

theorem modeDiff_one (u : ℕ → ℝ → Space → Space) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (κ : ℤ × ℤ) (n : ℕ) (σ : ℝ) (y : Space) :
    modeDiff u v G H 1 κ n σ y =
      ENNReal.ofReal (cnormSq (modeGrad κ (fun σ y => gradField (u n) σ y - G σ y) σ y)) := by
  rw [modeDiff, if_neg one_ne_zero, if_pos rfl]

theorem modeDiff_two (u : ℕ → ℝ → Space → Space) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (κ : ℤ × ℤ) (n : ℕ) (σ : ℝ) (y : Space) :
    modeDiff u v G H 2 κ n σ y =
      ENNReal.ofReal (cnormSq (modeSecondDeriv κ (fun σ y => secondDerivField (u n) σ y - H σ y) σ y)) := by
  rw [modeDiff, if_neg (by norm_num), if_neg (by norm_num)]

theorem ae_modes_sub (hSP : SmoothPerturbationIsPerturbationHolds)
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    ∀ᵐ z : ℝ × Space, ∀ n, ∀ κ : ℤ × ℤ,
      modeVel κ (fun σ y => u n σ y - v σ y) z.1 z.2 = modeVel κ (u n) z.1 z.2 - modeVel κ v z.1 z.2 ∧
      modeGrad κ (fun σ y => gradField (u n) σ y - G σ y) z.1 z.2 =
        modeGrad κ (gradField (u n)) z.1 z.2 - modeGrad κ G z.1 z.2 ∧
      modeSecondDeriv κ (fun σ y => secondDerivField (u n) σ y - H σ y) z.1 z.2 =
        modeSecondDeriv κ (secondDerivField (u n)) z.1 z.2 - modeSecondDeriv κ H z.1 z.2 := by
  obtain ⟨lv, lG, lH⟩ := perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have hl := fun n => perturbationLocalIntegrabilityHolds_proof ∅ P (u n) (gradField (u n)) (secondDerivField (u n))
    (transportPart P (u n)) (hSP P (u n) (hu.1 n))
  have hn := ae_all_iff.2 fun n => (ae_integrable_orbit axialRotationHolds_proof (hl n).1).and
    ((ae_integrable_orbit axialRotationHolds_proof (hl n).2.1).and
      (ae_integrable_orbit axialRotationHolds_proof (hl n).2.2))
  filter_upwards [hn, ae_integrable_orbit axialRotationHolds_proof lv, ae_integrable_orbit axialRotationHolds_proof lG,
    ae_integrable_orbit axialRotationHolds_proof lH] with z hz h1 h2 h3 n κ
  exact ⟨modeVel_sub_of (hz n).1 h1 κ, modeGrad_sub_of (hz n).2.1 h2 κ, modeSecondDeriv_sub_of (hz n).2.2 h3 κ⟩

end Measure

theorem modes_converge_ae {C : Type} (m : ModeWeights C) (P : ℝ) (w : Space → ℝ) (W : ℝ → Space → Space)
    (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
      (∀ ι, Tendsto (fun n => modePos m P (u (φ n)) (gradField (u (φ n))) ι σ y) atTop
          (𝓝 (modePos m P v G ι σ y))) ∧
        (∀ ι, Tendsto (fun n => modeRest m w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y)
          atTop (𝓝 (modeRest m w W v G H ι σ y))) ∧
        Tendsto (fun n => stretchForm W (u (φ n)) (gradField (u (φ n))) σ y) atTop
          (𝓝 (stretchForm W v G σ y)) := by
  obtain ⟨φ, hφ, hae⟩ := PassageCommon.ae_subseq_fields hSP hv hu (E := diffModes u v G H)
    (fun k n => modeDiff_aemeasurable hSP hv hu k.unpair.1 (modeIndex k.unpair.2) n)
    (fun k => modeDiff_tendsto hPars hSP hv hu k.unpair.1 (modeIndex k.unpair.2))
  have hlin := ae_modes_sub hSP hv hu
  have hlin2 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) 1)
    (Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space)) hlin)
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae, hlin2] with σ h1 h2
  filter_upwards [h1, h2] with y hy hl
  obtain ⟨hk, hu0, hg0, -⟩ := hy
  refine limits_of_modes m P w W (U := fun n => u (φ n)) (fun κ => ?_) (fun κ => ?_) (fun κ => ?_) hu0 hg0
  · have hk0 := hk (Nat.pair 0 (modeIndex.symm κ))
    simp only [diffModes_pair, modeDiff_zero] at hk0
    have hc := PassageCommon.tendsto_zero_of_ofReal (fun n => FieldModes.cnormSq_nonneg _) hk0
    refine tendsto_of_cnormSq ?_
    have e : ∀ n, cnormSq (modeVel κ (u (φ n)) σ y - modeVel κ v σ y) =
        (1 + ‖y‖) ^ 2 * cnormSq (modeVel κ (weightedDiff (u (φ n)) v) σ y) := fun n => by
      have h0 : 0 < 1 + ‖y‖ := by positivity
      rw [← (hl (φ n) κ).1, modeVel_weightedDiff, cnormSq_const_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_inv, abs_of_pos h0, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 h0.ne'), one_mul]
    have h := hc.const_mul ((1 + ‖y‖) ^ 2)
    rw [mul_zero] at h
    exact h.congr fun n => (e n).symm
  · have hk1 := hk (Nat.pair 1 (modeIndex.symm κ))
    simp only [diffModes_pair, modeDiff_one] at hk1
    have hc := PassageCommon.tendsto_zero_of_ofReal (fun n => FieldModes.cnormSq_nonneg _) hk1
    refine tendsto_of_cnormSq ?_
    exact hc.congr fun n => by rw [(hl (φ n) κ).2.1]
  · have hk2 := hk (Nat.pair 2 (modeIndex.symm κ))
    simp only [diffModes_pair, modeDiff_two] at hk2
    have hc := PassageCommon.tendsto_zero_of_ofReal (fun n => FieldModes.cnormSq_nonneg _) hk2
    refine tendsto_of_cnormSq ?_
    exact hc.congr fun n => by rw [(hl (φ n) κ).2.2]

end Internal.DensityPassageModes

end Coercive

end Breakdown
