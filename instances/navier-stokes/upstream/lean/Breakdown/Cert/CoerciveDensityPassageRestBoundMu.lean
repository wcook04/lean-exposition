import Breakdown.Cert.CoerciveDensityPassageRestBound
import Breakdown.Cert.CoerciveSmoothMuDecay

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassageRestBound

theorem mu_coeff_bounds {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : ℤ × ℤ) (σ : ℝ) (y : Space),
      |(m.mu ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.muGrad ι y) * (1 + ‖y‖)| ≤ M ∧
      |m.mu ι y * |m.rate (m.classOf ι) y| * (1 + ‖y‖) ^ 2| ≤ M ∧
      (∀ α, |m.mu ι y * (1 + ‖y‖) * velAmp W α σ y| ≤ M) ∧
      |ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) * ‖fderiv ℝ (meanField W) y‖ ^ 2 * (1 + ‖y‖) ^ 2
        / m.eta (m.classOf ι)| ≤ M ∧
      (∀ α β, |ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) / m.eta (m.classOf ι)
        * (gradAmp (gradField W) α σ y * (1 + ‖y‖)) * (gradAmp (gradField W) β σ y * (1 + ‖y‖))| ≤ M) ∧
      |ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) * (1 / 2) * m.eta (m.classOf ι) * m.mu ι y ^ 2
        * (1 + ‖y‖) ^ 2| ≤ M := by
  obtain ⟨D, hD⟩ := hWdec
  have hWn : ∀ σ y, ‖W σ y‖ ≤ D / (1 + ‖y‖) := fun σ y => by
    have h := hD σ y 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero, zero_add, pow_one] at h
  have hD1 : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 := fun σ y => by
    have h := hD σ y 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at h
  have hD0 : 0 ≤ D := by
    have h := hWn 0 0
    rw [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  obtain ⟨B1, hB1⟩ := hm.muW_decay
  obtain ⟨Br, hBr⟩ := hm.rate_bounded
  have := hm.finite_classes
  have : Nonempty C := ⟨m.classOf 0⟩
  choose Kc hKc using hm.muW_increment
  obtain ⟨c1, hc1⟩ := Finite.exists_max (fun c => (Kc c : ℝ))
  obtain ⟨c2, hc2⟩ := Finite.exists_max m.eta
  have hB10 : 0 ≤ B1 := (abs_nonneg _).trans (hB1 (m.classOf 0) 0).1
  have hBr0 : 0 ≤ Br := (abs_nonneg _).trans (hBr (m.classOf 0) 0)
  have hKL0 : 0 ≤ (Kc c1 : ℝ) := NNReal.coe_nonneg _
  have hemin := hm.etaMin_pos
  have hηM0 : 0 ≤ m.eta c2 := (hm.eta_pos c2).le
  set Cr : ℝ := 3 * D + 1 + 2 * Br with hCr
  have hCr0 : 0 ≤ Cr := by positivity
  refine ⟨(Cr * (4 * B1) + ((Kc c1 : ℝ) + B1)) + Br * (4 * B1) + 2 * D * (4 * B1) + 144 * D ^ 2 / m.etaMin
    + 9 * D ^ 2 / m.etaMin + (1 / 2) * m.eta c2 * (16 * B1 ^ 2), by positivity, fun ι σ y => ?_⟩
  set u : ℝ := 1 + ‖y‖ with hu
  have hu0 : 0 < u := by positivity
  have hu1 : 1 ≤ u := by simp [hu]
  set c := m.classOf ι with hc
  have hmu0 : 0 ≤ m.mu ι y := abs_nonneg _
  have hmu : m.mu ι y * u ^ 2 ≤ 4 * B1 := by
    obtain ⟨h1, h2, -⟩ := hB1 c y
    have ht : 2 * ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith only [sq_nonneg (‖y‖ - 1)]
    have e : m.mu ι y * u ^ 2 = m.mu ι y + m.mu ι y * (2 * ‖y‖) + ‖y‖ ^ 2 * m.mu ι y := by rw [hu]; ring
    have h3 : m.mu ι y * (2 * ‖y‖) ≤ m.mu ι y * (1 + ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left ht hmu0
    have e2 : |m.muW c y| * u ^ 2 = |m.muW c y| + |m.muW c y| * (2 * ‖y‖) + ‖y‖ ^ 2 * |m.muW c y| := e
    have h32 : |m.muW c y| * (2 * ‖y‖) ≤ |m.muW c y| * (1 + ‖y‖ ^ 2) := h3
    show |m.muW c y| * u ^ 2 ≤ 4 * B1
    nlinarith only [e2, h32, h1, h2]
  have hmu4 : m.mu ι y ≤ 4 * B1 := le_trans (le_mul_of_one_le_right hmu0 (one_le_pow₀ hu1)) hmu
  have hmuu : m.mu ι y * u ≤ 4 * B1 := by
    have huu : u ≤ u ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left huu hmu0
    linarith
  have hmug0 : 0 ≤ m.muGrad ι y := norm_nonneg _
  have hmug : m.muGrad ι y * u ≤ (Kc c1 : ℝ) + B1 := by
    obtain ⟨-, -, h3⟩ := hB1 c y
    have hk : m.muGrad ι y ≤ Kc c1 := (norm_fderiv_le_of_lipschitz ℝ (hKc c)).trans (hc1 c)
    have h3' : ‖y‖ * m.muGrad ι y ≤ B1 := h3
    rw [hu]
    nlinarith only [h3', hk]
  have hmf : ‖meanField W y‖ ≤ 3 * D := by
    refine (Internal.MuSmooth.Decay.meanField_norm_le W hWn y).trans ?_
    have : D / u ≤ D := div_le_self hD0 hu1
    linarith
  have hrv : ‖relativeVelocity W (m.rate c) y‖ ≤ Cr * u := by
    unfold relativeVelocity
    have hr := hBr c y
    have h1 : ‖-(y 1) • unitVector 0 + y 0 • unitVector 1‖ ≤ 2 * ‖y‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Internal.MuSmooth.Decay.unit_norm, Internal.MuSmooth.Decay.unit_norm, mul_one,
        mul_one, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
      linarith [Internal.MuSmooth.Decay.coord_abs_le y 0, Internal.MuSmooth.Decay.coord_abs_le y 1]
    have h2 : ‖m.rate c y • (-(y 1) • unitVector 0 + y 0 • unitVector 1)‖ ≤ Br * (2 * ‖y‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hr h1 (norm_nonneg _) hBr0
    have h3 : ‖(1 / 2 : ℝ) • y‖ = (1 / 2) * ‖y‖ := by rw [norm_smul]; norm_num
    have h4 := norm_sub_le (meanField W y + (1 / 2 : ℝ) • y) (m.rate c y • (-(y 1) • unitVector 0 + y 0 • unitVector 1))
    have h5 := norm_add_le (meanField W y) ((1 / 2 : ℝ) • y)
    have hy : ‖y‖ ≤ u := by rw [hu]; linarith
    rw [hCr]
    nlinarith only [h4, h5, h3, h2, hmf, hy, hu1, mul_le_mul_of_nonneg_left hu1 hD0, mul_le_mul_of_nonneg_left hy hBr0, norm_nonneg y]
  have hvW : ∀ α, velAmp W α σ y ≤ 2 * D / u := fun α => by
    have h := Internal.MuSmooth.Decay.cnormSq_modeVel_le W α σ y (M := D / u) (fun τ φ => by
      have := hWn (σ + τ) (axialRot φ y); rwa [Internal.MuSmooth.Decay.rot_norm] at this)
    unfold velAmp
    rw [Real.sqrt_le_left (by positivity)]
    refine h.trans ?_
    rw [div_pow, div_pow]
    have hu2 : 0 < u ^ 2 := by positivity
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hu2]
    nlinarith only [sq_nonneg D]
  have hgW : ∀ α, gradAmp (gradField W) α σ y ≤ 3 * D / u ^ 2 := fun α => by
    have h := Internal.MuSmooth.Decay.cnormSq_modeGrad_le (gradField W) α σ y (M := D / u ^ 2) (fun τ φ => by
      have := hD1 (σ + τ) (axialRot φ y); rwa [Internal.MuSmooth.Decay.rot_norm] at this)
    unfold gradAmp
    rw [Real.sqrt_le_left (by positivity)]
    refine h.trans (le_of_eq ?_)
    ring
  have hmfd := Internal.MuSmooth.Decay.meanField_fderiv_le hW hD1 hD0 y
  have hind0 : 0 ≤ ModeWeights.ind (∃ x, m.muW c x ≠ 0) := by
    unfold ModeWeights.ind; split_ifs <;> norm_num
  have hind1 := Internal.MuSmooth.Decay.ind_le_one (∃ x, m.muW c x ≠ 0)
  have hη := hm.eta_pos c
  have hηmin := hm.etaMin_le c
  have hηmax := hc2 c
  have hrate := hBr c y
  have hrate0 := abs_nonneg (m.rate c y)
  have b1 : (m.mu ι y * ‖relativeVelocity W (m.rate c) y‖ + m.muGrad ι y) * u ≤ Cr * (4 * B1) + ((Kc c1 : ℝ) + B1) := by
    have h1 : m.mu ι y * ‖relativeVelocity W (m.rate c) y‖ * u ≤ Cr * (4 * B1) := by
      have := mul_le_mul_of_nonneg_left hrv hmu0
      nlinarith only [mul_le_mul_of_nonneg_right this hu0.le, mul_le_mul_of_nonneg_left hmu hCr0]
    nlinarith only [h1, hmug]
  have b2 : m.mu ι y * |m.rate c y| * u ^ 2 ≤ Br * (4 * B1) := by
    have e : m.mu ι y * |m.rate c y| * u ^ 2 = |m.rate c y| * (m.mu ι y * u ^ 2) := by ring
    rw [e]
    nlinarith only [mul_le_mul_of_nonneg_right hrate (mul_nonneg hmu0 (sq_nonneg u)), mul_le_mul_of_nonneg_left hmu hBr0]
  have b3 : ∀ α, m.mu ι y * u * velAmp W α σ y ≤ 2 * D * (4 * B1) := fun α => by
    have h1 : velAmp W α σ y * u ≤ 2 * D := by
      have := mul_le_mul_of_nonneg_right (hvW α) hu0.le
      rwa [div_mul_cancel₀ _ hu0.ne'] at this
    have e : m.mu ι y * u * velAmp W α σ y = m.mu ι y * (velAmp W α σ y * u) := by ring
    rw [e]
    nlinarith only [mul_le_mul_of_nonneg_left h1 hmu0, mul_le_mul_of_nonneg_right hmu4 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD0)]
  have b4 : ModeWeights.ind (∃ x, m.muW c x ≠ 0) * ‖fderiv ℝ (meanField W) y‖ ^ 2 * u ^ 2 / m.eta c
      ≤ 144 * D ^ 2 / m.etaMin := by
    have hf : ‖fderiv ℝ (meanField W) y‖ * u ^ 2 ≤ 12 * D := by
      have := mul_le_mul_of_nonneg_right hmfd (by positivity : (0 : ℝ) ≤ u ^ 2)
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    have hf0 := norm_nonneg (fderiv ℝ (meanField W) y)
    have hsq : ‖fderiv ℝ (meanField W) y‖ ^ 2 * u ^ 2 ≤ 144 * D ^ 2 := by
      have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
      have h2 : (‖fderiv ℝ (meanField W) y‖ * u ^ 2) ^ 2 ≤ (12 * D) ^ 2 := pow_le_pow_left₀ (by positivity) hf 2
      nlinarith only [h2, hu2, sq_nonneg (‖fderiv ℝ (meanField W) y‖ * u), hf0]
    rw [div_le_div_iff₀ hη hemin]
    have h3 : ModeWeights.ind (∃ x, m.muW c x ≠ 0) * ‖fderiv ℝ (meanField W) y‖ ^ 2 * u ^ 2 ≤ 144 * D ^ 2 := by
      nlinarith only [hsq, hind0, hind1, mul_nonneg (sq_nonneg ‖fderiv ℝ (meanField W) y‖) (sq_nonneg u)]
    nlinarith only [h3, hηmin, hemin, mul_nonneg (mul_nonneg hind0 (sq_nonneg ‖fderiv ℝ (meanField W) y‖)) (sq_nonneg u), sq_nonneg D]
  have hgu : ∀ α, gradAmp (gradField W) α σ y * u ≤ 3 * D := fun α => by
    have := mul_le_mul_of_nonneg_right (hgW α) (by positivity : (0 : ℝ) ≤ u ^ 2)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    have h0 : 0 ≤ gradAmp (gradField W) α σ y := Real.sqrt_nonneg _
    have huu : u ≤ u ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left huu h0
    linarith
  have b5 : ∀ α β, ModeWeights.ind (∃ x, m.muW c x ≠ 0) / m.eta c
      * (gradAmp (gradField W) α σ y * u) * (gradAmp (gradField W) β σ y * u) ≤ 9 * D ^ 2 / m.etaMin := fun α β => by
    have ha0 : 0 ≤ gradAmp (gradField W) α σ y * u := mul_nonneg (Real.sqrt_nonneg _) hu0.le
    have hb0 : 0 ≤ gradAmp (gradField W) β σ y * u := mul_nonneg (Real.sqrt_nonneg _) hu0.le
    have hp : (gradAmp (gradField W) α σ y * u) * (gradAmp (gradField W) β σ y * u) ≤ 9 * D ^ 2 := by
      nlinarith only [mul_le_mul (hgu α) (hgu β) hb0 (by positivity : (0 : ℝ) ≤ 3 * D)]
    have hq : ModeWeights.ind (∃ x, m.muW c x ≠ 0) / m.eta c ≤ 1 / m.etaMin := by
      rw [div_le_div_iff₀ hη hemin]
      nlinarith only [hind1, hind0, hηmin, hemin]
    have hq0 : 0 ≤ ModeWeights.ind (∃ x, m.muW c x ≠ 0) / m.eta c := div_nonneg hind0 hη.le
    calc ModeWeights.ind (∃ x, m.muW c x ≠ 0) / m.eta c
          * (gradAmp (gradField W) α σ y * u) * (gradAmp (gradField W) β σ y * u)
        = ModeWeights.ind (∃ x, m.muW c x ≠ 0) / m.eta c
          * ((gradAmp (gradField W) α σ y * u) * (gradAmp (gradField W) β σ y * u)) := by ring
      _ ≤ 1 / m.etaMin * (9 * D ^ 2) := mul_le_mul hq hp (mul_nonneg ha0 hb0) (by positivity)
      _ = 9 * D ^ 2 / m.etaMin := by ring
  have b6 : ModeWeights.ind (∃ x, m.muW c x ≠ 0) * (1 / 2) * m.eta c * m.mu ι y ^ 2 * u ^ 2
      ≤ (1 / 2) * m.eta c2 * (16 * B1 ^ 2) := by
    have hmu2 : m.mu ι y ^ 2 * u ^ 2 ≤ 16 * B1 ^ 2 := by
      have h := pow_le_pow_left₀ (mul_nonneg hmu0 hu0.le) hmuu 2
      nlinarith only [h]
    have e : ModeWeights.ind (∃ x, m.muW c x ≠ 0) * (1 / 2) * m.eta c * m.mu ι y ^ 2 * u ^ 2
        = (1 / 2) * (ModeWeights.ind (∃ x, m.muW c x ≠ 0) * m.eta c) * (m.mu ι y ^ 2 * u ^ 2) := by ring
    rw [e]
    have hie : ModeWeights.ind (∃ x, m.muW c x ≠ 0) * m.eta c ≤ m.eta c2 := by nlinarith only [hind1, hind0, hη, hηmax]
    have hie0 : 0 ≤ ModeWeights.ind (∃ x, m.muW c x ≠ 0) * m.eta c := mul_nonneg hind0 hη.le
    nlinarith only [mul_le_mul hie hmu2 (by positivity) hηM0]
  have n1 : 0 ≤ (m.mu ι y * ‖relativeVelocity W (m.rate c) y‖ + m.muGrad ι y) * u := by positivity
  have n2 : 0 ≤ m.mu ι y * |m.rate c y| * u ^ 2 := by positivity
  have n4 : 0 ≤ ModeWeights.ind (∃ x, m.muW c x ≠ 0) * ‖fderiv ℝ (meanField W) y‖ ^ 2 * u ^ 2 / m.eta c := by
    have := hη.le; positivity
  have n6 : 0 ≤ ModeWeights.ind (∃ x, m.muW c x ≠ 0) * (1 / 2) * m.eta c * m.mu ι y ^ 2 * u ^ 2 := by
    have := hη.le; positivity
  have P1 : 0 ≤ 144 * D ^ 2 / m.etaMin := by positivity
  have P2 : 0 ≤ 9 * D ^ 2 / m.etaMin := by positivity
  have P3 : 0 ≤ (1 / 2) * m.eta c2 * (16 * B1 ^ 2) := by positivity
  have P4 : 0 ≤ 2 * D * (4 * B1) := by positivity
  have P5 : 0 ≤ Br * (4 * B1) := by positivity
  have P6 : 0 ≤ Cr * (4 * B1) + ((Kc c1 : ℝ) + B1) := by positivity
  refine ⟨?_, ?_, fun α => ?_, ?_, fun α β => ?_, ?_⟩
  · rw [abs_of_nonneg n1]; linarith
  · rw [abs_of_nonneg n2]; linarith
  · have hv0 : 0 ≤ velAmp W α σ y := Real.sqrt_nonneg _
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hmu0 hu0.le) hv0)]; linarith [b3 α]
  · rw [abs_of_nonneg n4]; linarith
  · have ga : 0 ≤ gradAmp (gradField W) α σ y := Real.sqrt_nonneg _
    have gb : 0 ≤ gradAmp (gradField W) β σ y := Real.sqrt_nonneg _
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (div_nonneg hind0 hη.le) (mul_nonneg ga hu0.le))
      (mul_nonneg gb hu0.le))]
    linarith [b5 α β]
  · rw [abs_of_nonneg n6]; linarith

private theorem restBound_congr {R₁ R₂ : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsRestBound R₁ v G H) (e : R₁ = R₂) :
    IsRestBound R₂ v G H := e ▸ h

theorem muRest_bound {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hWs : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G _ ι σ y => modeMuRest m W v G ι σ y) v G H := by
  obtain ⟨M, hM0, hM⟩ := mu_coeff_bounds hA hWs hWdec
  have h1 := isRestBound_prod isAmp_grad isAmp_vel
    (fun ι _ y => (m.mu ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.muGrad ι y) * (1 + ‖y‖))
    hM0 (fun ι σ y => (hM ι σ y).1) (0, 0) (0, 0) v G H
  have h2 := isRestBound_prod isAmp_vel isAmp_vel
    (fun ι _ y => m.mu ι y * |m.rate (m.classOf ι) y| * (1 + ‖y‖) ^ 2)
    hM0 (fun ι σ y => (hM ι σ y).2.1) (0, 0) (0, 0) v G H
  have h3 := isRestBound_finsetSum m.waves (fun α _ => isRestBound_prod isAmp_vel isAmp_grad
    (fun ι σ y => m.mu ι y * (1 + ‖y‖) * velAmp W α σ y)
    hM0 (fun ι σ y => (hM ι σ y).2.2.1 α) (0, 0) α v G H)
  have h4 := isRestBound_prod isAmp_vel isAmp_vel
    (fun ι _ y => ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) * ‖fderiv ℝ (meanField W) y‖ ^ 2
      * (1 + ‖y‖) ^ 2 / m.eta (m.classOf ι))
    hM0 (fun ι σ y => (hM ι σ y).2.2.2.1) (0, 0) (0, 0) v G H
  have h5 := isRestBound_finsetSum m.waves (fun α _ => isRestBound_finsetSum m.waves (fun β _ =>
    isRestBound_prod isAmp_vel isAmp_vel
    (fun ι σ y => ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) / m.eta (m.classOf ι)
      * (gradAmp (gradField W) α σ y * (1 + ‖y‖)) * (gradAmp (gradField W) β σ y * (1 + ‖y‖)))
    hM0 (fun ι σ y => (hM ι σ y).2.2.2.2.1 α β) α β v G H))
  have h6 := isRestBound_prod isAmp_vel isAmp_vel
    (fun ι _ y => ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) * (1 / 2) * m.eta (m.classOf ι)
      * m.mu ι y ^ 2 * (1 + ‖y‖) ^ 2)
    hM0 (fun ι σ y => (hM ι σ y).2.2.2.2.2) (0, 0) (0, 0) v G H
  refine restBound_congr ((((h1.neg).add h2.neg).add h3.neg).add ((h4.add h5).add h6).neg) ?_
  funext v G H ι σ y
  simp only [Prod.mk_zero_zero, sub_zero]
  have hr : (1 + ‖y‖) ≠ 0 := by positivity
  have hη : m.eta (m.classOf ι) ≠ 0 := (hA.eta_pos _).ne'
  have k1 : (m.mu ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.muGrad ι y) * (1 + ‖y‖)
      * (gradAmp G ι σ y * (velAmp v ι σ y / (1 + ‖y‖)))
      = (m.mu ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.muGrad ι y) * gradAmp G ι σ y
        * velAmp v ι σ y := by
    field_simp
  have k2 : m.mu ι y * |m.rate (m.classOf ι) y| * (1 + ‖y‖) ^ 2
      * (velAmp v ι σ y / (1 + ‖y‖) * (velAmp v ι σ y / (1 + ‖y‖)))
      = m.mu ι y * |m.rate (m.classOf ι) y| * velAmp v ι σ y ^ 2 := by
    field_simp
  have k3 : ∑ α ∈ m.waves, m.mu ι y * (1 + ‖y‖) * velAmp W α σ y
      * (velAmp v ι σ y / (1 + ‖y‖) * gradAmp G (ι - α) σ y)
      = m.mu ι y * velAmp v ι σ y * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp G (ι - α) σ y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    field_simp
  have k4 : ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) * ‖fderiv ℝ (meanField W) y‖ ^ 2
      * (1 + ‖y‖) ^ 2 / m.eta (m.classOf ι) * (velAmp v ι σ y / (1 + ‖y‖) * (velAmp v ι σ y / (1 + ‖y‖)))
      = ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) * (‖fderiv ℝ (meanField W) y‖ ^ 2
        * velAmp v ι σ y ^ 2 / m.eta (m.classOf ι)) := by
    field_simp
  have k5 : ∑ α ∈ m.waves, ∑ β ∈ m.waves, ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) / m.eta (m.classOf ι)
      * (gradAmp (gradField W) α σ y * (1 + ‖y‖)) * (gradAmp (gradField W) β σ y * (1 + ‖y‖))
      * (velAmp v (ι - α) σ y / (1 + ‖y‖) * (velAmp v (ι - β) σ y / (1 + ‖y‖)))
      = ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0)
        * ((∑ α ∈ m.waves, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / m.eta (m.classOf ι)) := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    field_simp
  have k6 : ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) * (1 / 2) * m.eta (m.classOf ι)
      * m.mu ι y ^ 2 * (1 + ‖y‖) ^ 2 * (velAmp v ι σ y / (1 + ‖y‖) * (velAmp v ι σ y / (1 + ‖y‖)))
      = ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) * ((1 / 2) * m.eta (m.classOf ι) * m.mu ι y ^ 2
        * velAmp v ι σ y ^ 2) := by
    field_simp
  unfold modeMuRest
  linear_combination -(k1 + k2 + k3 + k4 + k5 + k6)

end Internal.DensityPassageRestBound

end Coercive

end Breakdown
