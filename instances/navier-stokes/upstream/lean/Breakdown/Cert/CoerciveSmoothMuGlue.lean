import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.MuSmooth

def pairTerm {C : Type} (m : ModeWeights C) (v Q : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  (Complex.I * (m.muW (m.classOf ι) y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι Q σ y)).re

def pairMode {C : Type} (m : ModeWeights C) (v Q : ℝ → Space → Space) (ι : ℤ × ℤ) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pairTerm m v Q ι σ y

def dopDensity {C : Type} (m : ModeWeights C) (P : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  m.mu ι y * |m.dop P ι y| * cnormSq (modeVel ι v σ y)

def dopMode {C : Type} (m : ModeWeights C) (P : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) : ℝ≥0∞ :=
  ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (dopDensity m P v ι σ y)

def restMode {C : Type} (m : ModeWeights C) (W v : ℝ → Space → Space) (ι : ℤ × ℤ) : ℝ≥0∞ :=
  ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-modeMuRest m W v (gradField v) ι σ y)

theorem cnorm_nonneg {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nonpos_combo {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    -a - b - c - d * e ≤ 0 := by
  nlinarith [mul_nonneg hd he]

theorem ind_nonneg (p : Prop) : 0 ≤ ModeWeights.ind p := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem rest_nonpos {C : Type} (m : ModeWeights C) (hη : ∀ c, 0 < m.eta c) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeMuRest m W v G ι σ y ≤ 0 := by
  unfold modeMuRest
  have h1 : 0 ≤ m.mu ι y := abs_nonneg _
  have h2 : 0 ≤ m.muGrad ι y := norm_nonneg _
  have h3 : 0 ≤ gradAmp G ι σ y := Real.sqrt_nonneg _
  have h4 : 0 ≤ velAmp v ι σ y := Real.sqrt_nonneg _
  have h5 : 0 ≤ ∑ α ∈ m.waves, velAmp W α σ y * gradAmp G (ι - α) σ y :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h6 := ind_nonneg (∃ x, m.muW (m.classOf ι) x ≠ 0)
  have h7 := hη (m.classOf ι)
  have h8 : 0 ≤ ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ := norm_nonneg _
  have h9 : 0 ≤ |m.rate (m.classOf ι) y| := abs_nonneg _
  exact nonpos_combo (mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg h1 h8) h2) h3) h4)
    (mul_nonneg (mul_nonneg h1 h9) (sq_nonneg _)) (mul_nonneg (mul_nonneg h1 h4) h5) h6
    (add_nonneg (div_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) h7.le)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h7.le) (sq_nonneg _)) (sq_nonneg _)))

theorem pos_eq {C : Type} (m : ModeWeights C) (P : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : modeMuPos m P v ι σ y = (1 - m.cμ) * dopDensity m P v ι σ y := by
  unfold modeMuPos dopDensity velAmp
  rw [Real.sq_sqrt (cnorm_nonneg _)]
  ring

theorem dopDensity_nonneg {C : Type} (m : ModeWeights C) (P : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) : 0 ≤ dopDensity m P v ι σ y := by
  unfold dopDensity
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (cnorm_nonneg _)

theorem swap_sum (f : ℝ → Space → ℤ × ℤ → ℝ≥0∞) (hf : ∀ ι, Measurable (fun p : ℝ × Space => f p.1 p.2 ι)) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, f σ y ι = ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y ι := by
  have h1 : ∀ σ, ∫⁻ y, ∑' ι, f σ y ι = ∑' ι, ∫⁻ y, f σ y ι := fun σ =>
    lintegral_tsum fun ι => ((hf ι).comp measurable_prodMk_left).aemeasurable
  simp_rw [h1]
  exact lintegral_tsum fun ι => ((hf ι).lintegral_prod_right' (ν := volume)).aemeasurable

theorem toReal_le_of {d r : ℝ≥0∞} {t : ℝ} (hr : r ≠ ⊤) (h : d + ENNReal.ofReal (-t) ≤ ENNReal.ofReal t + r) :
    d ≠ ⊤ ∧ d.toReal ≤ t + r.toReal := by
  have hd : d ≠ ⊤ := by
    intro hd
    rw [hd, top_add] at h
    exact (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hr⟩) (top_le_iff.1 h)
  refine ⟨hd, ?_⟩
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hr⟩) h
  rw [ENNReal.toReal_add hd ENNReal.ofReal_ne_top, ENNReal.toReal_add ENNReal.ofReal_ne_top hr,
    ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at h2
  rcases le_total 0 t with ht | ht
  · rw [max_eq_right (by linarith : -t ≤ 0), max_eq_left ht] at h2
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ -t), max_eq_right ht] at h2
    linarith

theorem ennreal_bound {a s X : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (h : a - s ≤ X) :
    ENNReal.ofReal a + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + ENNReal.ofReal s := by
  rcases le_total 0 X with hX | hX
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -X ≤ 0), add_zero, ← ENNReal.ofReal_add hX hs]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [← ENNReal.ofReal_add ha (by linarith : 0 ≤ -X), ENNReal.ofReal_of_nonpos hX, zero_add]
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem split_of_modes {C : Type} (m : ModeWeights C) (P : ℝ) (W v Q : ℝ → Space → Space)
    (hcμ : m.cμ < 1) (hη : ∀ c, 0 < m.eta c)
    (hmeasR : ∀ ι, Measurable (fun p : ℝ × Space => ENNReal.ofReal (-modeMuRest m W v (gradField v) ι p.1 p.2)))
    (hmeasD : ∀ ι, Measurable (fun p : ℝ × Space => ENNReal.ofReal (dopDensity m P v ι p.1 p.2)))
    (hrest : ∑' ι, restMode m W v ι < ⊤)
    (hsum : Summable (fun ι => pairMode m v Q ι))
    (hmode : ∀ ι, dopMode m P v ι + ENNReal.ofReal (-pairMode m v Q ι)
      ≤ ENNReal.ofReal (pairMode m v Q ι) + restMode m W v ι) :
    IsSplitLowerBound (muPairing (fun ι y => m.muW (m.classOf ι) y) v Q - m.cμ * (m.frequencySeminormSq P v).toReal)
      (fun σ y ι => modeMuPos m P v ι σ y)
      (fun σ y ι => modeMuRest m W v (gradField v) ι σ y) (fun _ _ => 0) (fun _ _ => 0) := by
  have hR : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (-modeMuRest m W v (gradField v) ι σ y)
      = ∑' ι, restMode m W v ι := swap_sum _ hmeasR
  have hRtop : ∑' ι, restMode m W v ι ≠ ⊤ := hrest.ne
  have hRi : ∀ ι, restMode m W v ι ≠ ⊤ := fun ι =>
    ne_top_of_le_ne_top hRtop (ENNReal.le_tsum ι)
  have hD : ∀ ι, dopMode m P v ι ≠ ⊤ ∧
      (dopMode m P v ι).toReal ≤ pairMode m v Q ι + (restMode m W v ι).toReal := fun ι =>
    toReal_le_of (hRi ι) (hmode ι)
  have hsR : Summable (fun ι => (restMode m W v ι).toReal) := ENNReal.summable_toReal hRtop
  have hsD : Summable (fun ι => (dopMode m P v ι).toReal) :=
    Summable.of_nonneg_of_le (fun ι => ENNReal.toReal_nonneg) (fun ι => (hD ι).2) (hsum.add hsR)
  have hDeq : ∑' ι, dopMode m P v ι = ENNReal.ofReal (∑' ι, (dopMode m P v ι).toReal) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun ι => ENNReal.toReal_nonneg) hsD]
    exact tsum_congr fun ι => (ENNReal.ofReal_toReal (hD ι).1).symm
  have hReq : ∑' ι, restMode m W v ι = ENNReal.ofReal (∑' ι, (restMode m W v ι).toReal) := by
    rw [← ENNReal.tsum_toReal_eq hRi, ENNReal.ofReal_toReal hRtop]
  have hfreq : m.frequencySeminormSq P v = ∑' ι, dopMode m P v ι := rfl
  have hpair : muPairing (fun ι y => m.muW (m.classOf ι) y) v Q = ∑' ι, pairMode m v Q ι := rfl
  have hineq : ∑' ι, (dopMode m P v ι).toReal
      ≤ ∑' ι, pairMode m v Q ι + ∑' ι, (restMode m W v ι).toReal := by
    exact hasSum_le (fun ι => (hD ι).2) hsD.hasSum (hsum.hasSum.add hsR.hasSum)
  have hPos : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (modeMuPos m P v ι σ y)
      = ENNReal.ofReal (1 - m.cμ) * ∑' ι, dopMode m P v ι := by
    have hpt : ∀ σ y ι, ENNReal.ofReal (modeMuPos m P v ι σ y)
        = ENNReal.ofReal (1 - m.cμ) * ENNReal.ofReal (dopDensity m P v ι σ y) := fun σ y ι => by
      rw [pos_eq, ENNReal.ofReal_mul (by linarith)]
    simp_rw [hpt]
    rw [swap_sum _ (fun ι => ((hmeasD ι).const_mul _)), ← ENNReal.tsum_mul_left]
    refine tsum_congr fun ι => ?_
    unfold dopMode
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun σ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hRestZero : ∀ σ y, ∑' ι, ENNReal.ofReal (modeMuRest m W v (gradField v) ι σ y) = 0 := fun σ y => by
    simp [ENNReal.ofReal_eq_zero.2 (rest_nonpos m hη W v (gradField v) _ σ y)]
  refine ⟨?_, ?_⟩
  · simp only [neg_zero, ENNReal.ofReal_zero, add_zero]
    rw [hR]
    exact hrest
  · simp only [neg_zero, ENNReal.ofReal_zero, add_zero, hRestZero]
    rw [hPos, hR, hDeq, hReq, ← ENNReal.ofReal_mul (by linarith), hfreq, hDeq,
      ENNReal.toReal_ofReal (tsum_nonneg fun ι => ENNReal.toReal_nonneg), hpair]
    refine ennreal_bound (mul_nonneg (by linarith) (tsum_nonneg fun ι => ENNReal.toReal_nonneg))
      (tsum_nonneg fun ι => ENNReal.toReal_nonneg) ?_
    have h0 : 0 ≤ ∑' ι, (dopMode m P v ι).toReal := tsum_nonneg fun ι => ENNReal.toReal_nonneg
    have hc0 : 0 < m.cμ * 0 + 1 := by linarith
    nlinarith

def innerPart (P : ℝ) (W v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  transportPart P v σ y - secondDerivTrace (secondDerivField v σ y) + fderiv ℝ (v σ) y (W σ y)

def transportLoss {C : Type} (m : ModeWeights C) (W v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  (m.mu ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.muGrad ι y)
      * gradAmp (gradField v) ι σ y * velAmp v ι σ y
    + m.mu ι y * |m.rate (m.classOf ι) y| * velAmp v ι σ y ^ 2
    + m.mu ι y * velAmp v ι σ y * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y

def pressureLoss {C : Type} (m : ModeWeights C) (W v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0)
    * ((‖fderiv ℝ (meanField W) y‖ ^ 2 * velAmp v ι σ y ^ 2
        + (∑ α ∈ m.waves, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2) / m.eta (m.classOf ι)
      + (1 / 2) * m.eta (m.classOf ι) * m.mu ι y ^ 2 * velAmp v ι σ y ^ 2)

theorem neg_rest_eq {C : Type} (m : ModeWeights C) (W v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) :
    -modeMuRest m W v (gradField v) ι σ y = transportLoss m W v ι σ y + pressureLoss m W v ι σ y := by
  unfold modeMuRest transportLoss pressureLoss
  ring

theorem transportLoss_nonneg {C : Type} (m : ModeWeights C) (W v : ℝ → Space → Space) (ι : ℤ × ℤ)
    (σ : ℝ) (y : Space) : 0 ≤ transportLoss m W v ι σ y := by
  unfold transportLoss
  have h1 : 0 ≤ m.mu ι y := abs_nonneg _
  have h2 : 0 ≤ m.muGrad ι y := norm_nonneg _
  have h3 : 0 ≤ gradAmp (gradField v) ι σ y := Real.sqrt_nonneg _
  have h4 : 0 ≤ velAmp v ι σ y := Real.sqrt_nonneg _
  have h5 : 0 ≤ ∑ α ∈ m.waves, velAmp W α σ y * gradAmp (gradField v) (ι - α) σ y :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h8 : 0 ≤ ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ := norm_nonneg _
  have h9 : 0 ≤ |m.rate (m.classOf ι) y| := abs_nonneg _
  exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg h1 h8) h2) h3) h4)
    (mul_nonneg (mul_nonneg h1 h9) (sq_nonneg _))) (mul_nonneg (mul_nonneg h1 h4) h5)

theorem pressureLoss_nonneg {C : Type} (m : ModeWeights C) (hη : ∀ c, 0 < m.eta c) (W v : ℝ → Space → Space)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : 0 ≤ pressureLoss m W v ι σ y := by
  unfold pressureLoss
  have h7 := hη (m.classOf ι)
  exact mul_nonneg (ind_nonneg _)
    (add_nonneg (div_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) h7.le)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h7.le) (sq_nonneg _)) (sq_nonneg _)))

end Internal.MuSmooth

end Coercive

end Breakdown
