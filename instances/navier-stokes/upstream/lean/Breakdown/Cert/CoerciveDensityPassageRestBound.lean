import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoerciveSmoothDensityBase

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassageRestBound

def ampTotal (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∑' ι : ℤ × ℤ, ENNReal.ofReal (cnormSq (modeSecondDeriv ι H σ y) + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    + cnormSq (modeGrad ι G σ y) + cnormSq (curlOfGrad (modeGrad ι G σ y))
    + cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2)

def diffTotal (u : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
    (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∑' ι : ℤ × ℤ, ENNReal.ofReal (cnormSq (modeSecondDeriv ι Hu σ y - modeSecondDeriv ι H σ y)
    + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι Hu σ y) - curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    + cnormSq (modeGrad ι Gu σ y - modeGrad ι G σ y)
    + cnormSq (curlOfGrad (modeGrad ι Gu σ y) - curlOfGrad (modeGrad ι G σ y))
    + cnormSq (modeVel ι u σ y - modeVel ι v σ y) / (1 + ‖y‖) ^ 2)

def IsRestBound (R : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    (∀ σ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (|R v G H ι σ y|) ≤ ENNReal.ofReal K * ampTotal v G H σ y) ∧
    ∀ t : ℝ, 0 < t → ∀ (u : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
      (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) σ y,
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (|R u Gu Hu ι σ y - R v G H ι σ y|)
        ≤ ENNReal.ofReal (K * (1 + 1 / t)) * diffTotal u Gu Hu v G H σ y
          + ENNReal.ofReal (K * t) * ampTotal v G H σ y

theorem IsRestBound.add {R₁ R₂ : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h₁ : IsRestBound R₁ v G H) (h₂ : IsRestBound R₂ v G H) :
    IsRestBound (fun v G H ι σ y => R₁ v G H ι σ y + R₂ v G H ι σ y) v G H := by
  obtain ⟨K₁, hK₁, a₁, b₁⟩ := h₁
  obtain ⟨K₂, hK₂, a₂, b₂⟩ := h₂
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun σ y => ?_, fun t ht u Gu Hu σ y => ?_⟩
  · calc ∑' ι : ℤ × ℤ, ENNReal.ofReal (|R₁ v G H ι σ y + R₂ v G H ι σ y|)
        ≤ ∑' ι : ℤ × ℤ, (ENNReal.ofReal (|R₁ v G H ι σ y|) + ENNReal.ofReal (|R₂ v G H ι σ y|)) :=
          ENNReal.tsum_le_tsum fun ι => by
            rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = (∑' ι : ℤ × ℤ, ENNReal.ofReal (|R₁ v G H ι σ y|)) + ∑' ι : ℤ × ℤ, ENNReal.ofReal (|R₂ v G H ι σ y|) :=
          ENNReal.tsum_add
      _ ≤ ENNReal.ofReal K₁ * ampTotal v G H σ y + ENNReal.ofReal K₂ * ampTotal v G H σ y :=
          add_le_add (a₁ σ y) (a₂ σ y)
      _ = ENNReal.ofReal (K₁ + K₂) * ampTotal v G H σ y := by
          rw [ENNReal.ofReal_add hK₁ hK₂, add_mul]
  · have e1 : 0 ≤ K₁ * (1 + 1 / t) := mul_nonneg hK₁ (by positivity)
    have e2 : 0 ≤ K₂ * (1 + 1 / t) := mul_nonneg hK₂ (by positivity)
    have e3 : 0 ≤ K₁ * t := mul_nonneg hK₁ ht.le
    have e4 : 0 ≤ K₂ * t := mul_nonneg hK₂ ht.le
    calc ∑' ι : ℤ × ℤ, ENNReal.ofReal (|(R₁ u Gu Hu ι σ y + R₂ u Gu Hu ι σ y)
          - (R₁ v G H ι σ y + R₂ v G H ι σ y)|)
        ≤ ∑' ι : ℤ × ℤ, (ENNReal.ofReal (|R₁ u Gu Hu ι σ y - R₁ v G H ι σ y|)
          + ENNReal.ofReal (|R₂ u Gu Hu ι σ y - R₂ v G H ι σ y|)) :=
          ENNReal.tsum_le_tsum fun ι => by
            rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
            refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (abs_add_le _ _))
            ring_nf
      _ = (∑' ι : ℤ × ℤ, ENNReal.ofReal (|R₁ u Gu Hu ι σ y - R₁ v G H ι σ y|))
          + ∑' ι : ℤ × ℤ, ENNReal.ofReal (|R₂ u Gu Hu ι σ y - R₂ v G H ι σ y|) := ENNReal.tsum_add
      _ ≤ (ENNReal.ofReal (K₁ * (1 + 1 / t)) * diffTotal u Gu Hu v G H σ y
            + ENNReal.ofReal (K₁ * t) * ampTotal v G H σ y)
          + (ENNReal.ofReal (K₂ * (1 + 1 / t)) * diffTotal u Gu Hu v G H σ y
            + ENNReal.ofReal (K₂ * t) * ampTotal v G H σ y) :=
          add_le_add (b₁ t ht u Gu Hu σ y) (b₂ t ht u Gu Hu σ y)
      _ = ENNReal.ofReal ((K₁ + K₂) * (1 + 1 / t)) * diffTotal u Gu Hu v G H σ y
          + ENNReal.ofReal ((K₁ + K₂) * t) * ampTotal v G H σ y := by
          rw [add_mul, add_mul, ENNReal.ofReal_add e1 e2, ENNReal.ofReal_add e3 e4, add_mul, add_mul]
          ring

theorem sqrt_cnormSq_sub_le {β : Type*} [Fintype β] (x z : β → ℂ) :
    |Real.sqrt (cnormSq x) - Real.sqrt (cnormSq z)| ≤ Real.sqrt (cnormSq (x - z)) := by
  have key : ∀ a : β → ℂ, Real.sqrt (cnormSq a) = ‖(WithLp.toLp 2 a : EuclideanSpace ℂ β)‖ := fun a => by
    rw [EuclideanSpace.norm_eq]
    rfl
  rw [key, key, key, WithLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _

theorem prod_diff_le {a b a' b' d e t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hd : |a' - a| ≤ d) (he : |b' - b| ≤ e) (ht : 0 < t) :
    |a' * b' - a * b| ≤ (1 + 1 / t) * (d ^ 2 + e ^ 2) + t * (a ^ 2 + b ^ 2) := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hbb : b' ≤ b + e := by linarith [le_abs_self (b' - b)]
  have s1 : |a' * b' - a * b| ≤ d * b' + a * e := by
    have eq : a' * b' - a * b = (a' - a) * b' + a * (b' - b) := by ring
    rw [eq]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hb']
      exact mul_le_mul_of_nonneg_right hd hb'
    · rw [abs_mul, abs_of_nonneg ha]
      exact mul_le_mul_of_nonneg_left he ha
  have s2 : d * b' ≤ d * b + d * e := by nlinarith
  have h1 : d * b ≤ d ^ 2 / t + t * b ^ 2 := by
    have : d * b * t ≤ d ^ 2 + t * b ^ 2 * t := by nlinarith [sq_nonneg (d - t * b)]
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    linarith
  have h2 : a * e ≤ e ^ 2 / t + t * a ^ 2 := by
    have : a * e * t ≤ e ^ 2 + t * a ^ 2 * t := by nlinarith [sq_nonneg (e - t * a)]
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    linarith
  have h3 : d * e ≤ d ^ 2 + e ^ 2 := by nlinarith [sq_nonneg (d - e)]
  have e5 : (1 + 1 / t) * (d ^ 2 + e ^ 2) = d ^ 2 + e ^ 2 + (d ^ 2 / t + e ^ 2 / t) := by ring
  have h4 : 0 ≤ d ^ 2 / t := by positivity
  have h5 : 0 ≤ e ^ 2 / t := by positivity
  rw [e5]
  nlinarith

theorem sq_term_le {c M a a' d t : ℝ} (hc : |c| ≤ M) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hd : |a' - a| ≤ d)
    (ht : 0 < t) :
    |c * a' ^ 2 - c * a ^ 2| ≤ (2 * M) * (1 + 1 / t) * d ^ 2 + (2 * M) * t * a ^ 2 := by
  have h := prod_diff_le (b := a) (b' := a') ha ha ha' hd hd ht
  have hM : 0 ≤ M := (abs_nonneg _).trans hc
  have eq : c * a' ^ 2 - c * a ^ 2 = c * (a' * a' - a * a) := by ring
  rw [eq, abs_mul]
  calc |c| * |a' * a' - a * a| ≤ M * ((1 + 1 / t) * (d ^ 2 + d ^ 2) + t * (a ^ 2 + a ^ 2)) :=
        mul_le_mul hc h (abs_nonneg _) hM
    _ = (2 * M) * (1 + 1 / t) * d ^ 2 + (2 * M) * t * a ^ 2 := by ring

theorem sq_term_abs_le {c M a : ℝ} (hc : |c| ≤ M) : |c * a ^ 2| ≤ M * a ^ 2 := by
  rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg a)

theorem sqrt_cnormSq_sq {β : Type*} [Fintype β] (x : β → ℂ) : Real.sqrt (cnormSq x) ^ 2 = cnormSq x :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem ennreal_step {r D A K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (h : |r| ≤ K₁ * D + K₂ * A) :
    ENNReal.ofReal (|r|) ≤ ENNReal.ofReal K₁ * ENNReal.ofReal D + ENNReal.ofReal K₂ * ENNReal.ofReal A := by
  rw [← ENNReal.ofReal_mul hK₁, ← ENNReal.ofReal_mul hK₂,
    ← ENNReal.ofReal_add (mul_nonneg hK₁ hD) (mul_nonneg hK₂ hA)]
  exact ENNReal.ofReal_le_ofReal h

theorem tsum_step {f D A : ℤ × ℤ → ℝ≥0∞} {a b : ℝ≥0∞} (h : ∀ ι, f ι ≤ a * D ι + b * A ι) :
    ∑' ι, f ι ≤ a * ∑' ι, D ι + b * ∑' ι, A ι := by
  calc ∑' ι, f ι ≤ ∑' ι, (a * D ι + b * A ι) := ENNReal.tsum_le_tsum h
    _ = a * ∑' ι, D ι + b * ∑' ι, A ι := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

theorem amp_sub_le {β : Type*} [Fintype β] (x z : β → ℂ) :
    |Real.sqrt (cnormSq x) - Real.sqrt (cnormSq z)| ≤ Real.sqrt (cnormSq (x - z)) :=
  sqrt_cnormSq_sub_le x z

theorem amp_sub_div_le {β : Type*} [Fintype β] (x z : β → ℂ) {r : ℝ} (hr : 0 < r) :
    |Real.sqrt (cnormSq x) / r - Real.sqrt (cnormSq z) / r| ≤ Real.sqrt (cnormSq (x - z)) / r := by
  rw [← sub_div, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (sqrt_cnormSq_sub_le x z) hr.le

theorem five_split (c1 c2 c3 c4 c5 X1 X2 X3 X4 X5 Y1 Y2 Y3 Y4 Y5 : ℝ) :
    c1 * X1 ^ 2 + c2 * X2 ^ 2 + c3 * X3 ^ 2 + c4 * X4 ^ 2 - c5 * X5 ^ 2
      - (c1 * Y1 ^ 2 + c2 * Y2 ^ 2 + c3 * Y3 ^ 2 + c4 * Y4 ^ 2 - c5 * Y5 ^ 2)
      = (c1 * X1 ^ 2 - c1 * Y1 ^ 2) + (c2 * X2 ^ 2 - c2 * Y2 ^ 2) + (c3 * X3 ^ 2 - c3 * Y3 ^ 2)
        + (c4 * X4 ^ 2 - c4 * Y4 ^ 2) - (c5 * X5 ^ 2 - c5 * Y5 ^ 2) := by ring

theorem base_coeff_bounds {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {w₀ epsSup epsGradSup ratio : ℝ} (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hwB : ∃ B, ∀ y, w y ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : ℤ × ℤ) (y : Space),
      |m.convD (m.classOf ι) y - m.c| ≤ M ∧ |1 - m.convD (m.classOf ι) y| ≤ M ∧
      |1 / 4 - m.convZ (m.classOf ι) y| ≤ M ∧
      |m.convZ (m.classOf ι) y - ModeWeights.secondDerivNorm (m.convD (m.classOf ι)) y - m.c * w y| ≤ M ∧
      |ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * (1 + ‖y‖) ^ 2| ≤ M := by
  obtain ⟨BD, hBD⟩ := hA.convD_decay
  obtain ⟨BZ, hBZ⟩ := hA.convZ_decay
  obtain ⟨HD, hHD⟩ := SmoothDensity.BaseBound.secondDerivD_bound hA
  obtain ⟨Bw, hBw⟩ := hwB
  refine ⟨1 + |BD| + |BZ| + |HD| + |Bw|, by positivity, fun ι y => ?_⟩
  set cl := m.classOf ι
  have hc0 := hA.c_pos
  have hc1 := hA.c_lt_one
  have hd0 := hA.convD_nonneg cl y
  have hdB : m.convD cl y ≤ |BD| := by
    have := hBD cl y 0 (by norm_num)
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_abs_self _))
  have hz : |m.convZ cl y| ≤ |BZ| := by
    have := hBZ cl y 0 (by norm_num)
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hhz : (1 + ‖y‖) ^ 2 * ModeWeights.secondDerivNorm (m.convZ cl) y ≤ |BZ| :=
    (hBZ cl y 2 le_rfl).trans (le_abs_self _)
  have hhz0 : 0 ≤ ModeWeights.secondDerivNorm (m.convZ cl) y := norm_nonneg _
  have hhd0 : 0 ≤ ModeWeights.secondDerivNorm (m.convD cl) y := norm_nonneg _
  have hhd : ModeWeights.secondDerivNorm (m.convD cl) y ≤ |HD| := (hHD cl y).trans (le_abs_self _)
  have hw0 : 0 ≤ w y := hA.weight_pos.le.trans (hA.weight_lower y)
  have hwb : w y ≤ |Bw| := (hBw y).trans (le_abs_self _)
  have hcw : 0 ≤ m.c * w y := mul_nonneg hc0.le hw0
  have hcw' : m.c * w y ≤ |Bw| := by nlinarith
  have a1 := abs_nonneg BD
  have a2 := abs_nonneg BZ
  have a3 := abs_nonneg HD
  have a4 := abs_nonneg Bw
  have hz' := abs_le.1 hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_of_nonneg (by positivity), mul_comm]; linarith

theorem base_bound {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {w₀ epsSup epsGradSup ratio : ℝ} (hA : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hwB : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y))
      v G H := by
  obtain ⟨M, hM0, hM⟩ := base_coeff_bounds hA hwB
  refine ⟨2 * M, by positivity, fun σ y => ?_, fun t ht u Gu Hu σ y => ?_⟩
  · unfold ampTotal
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ι => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := hM ι y
    have hy : 0 < 1 + ‖y‖ := by positivity
    have ex : ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * velAmp v ι σ y ^ 2
        = (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * (1 + ‖y‖) ^ 2) * (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 := by
      field_simp
    have hv2 : (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 = cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 := by
      rw [div_pow, velAmp, sqrt_cnormSq_sq]
    unfold modeVals baseDensity
    dsimp only
    rw [ex]
    have t1 := sq_term_abs_le (a := secondDerivAmp H ι σ y) c1
    have t2 := sq_term_abs_le (a := vortGradAmp H ι σ y) c2
    have t3 := sq_term_abs_le (a := vortAmp G ι σ y) c3
    have t4 := sq_term_abs_le (a := gradAmp G ι σ y) c4
    have t5 := sq_term_abs_le (a := velAmp v ι σ y / (1 + ‖y‖)) c5
    rw [secondDerivAmp, sqrt_cnormSq_sq] at t1
    rw [vortGradAmp, sqrt_cnormSq_sq] at t2
    rw [vortAmp, sqrt_cnormSq_sq] at t3
    rw [gradAmp, sqrt_cnormSq_sq] at t4
    rw [hv2] at t5
    rw [secondDerivAmp, vortGradAmp, vortAmp, gradAmp, sqrt_cnormSq_sq, sqrt_cnormSq_sq, sqrt_cnormSq_sq,
      sqrt_cnormSq_sq, hv2]
    have p1 := Internal.FieldModes.cnormSq_nonneg (modeSecondDeriv ι H σ y)
    have p2 := Internal.FieldModes.cnormSq_nonneg (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    have p3 := Internal.FieldModes.cnormSq_nonneg (modeGrad ι G σ y)
    have p4 := Internal.FieldModes.cnormSq_nonneg (curlOfGrad (modeGrad ι G σ y))
    have p5 : 0 ≤ cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 :=
      div_nonneg (Internal.FieldModes.cnormSq_nonneg _) (by positivity)
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) t5) |>.trans ?_
    nlinarith
  · unfold ampTotal diffTotal
    refine tsum_step fun ι => ?_
    obtain ⟨c1, c2, c3, c4, c5⟩ := hM ι y
    have hy : 0 < 1 + ‖y‖ := by positivity
    have exu : ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * velAmp u ι σ y ^ 2
        = (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * (1 + ‖y‖) ^ 2) * (velAmp u ι σ y / (1 + ‖y‖)) ^ 2 := by
      field_simp
    have exv : ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * velAmp v ι σ y ^ 2
        = (ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y * (1 + ‖y‖) ^ 2) * (velAmp v ι σ y / (1 + ‖y‖)) ^ 2 := by
      field_simp
    unfold modeVals baseDensity
    dsimp only
    rw [exu, exv]
    have q0 : 0 < t := ht
    have t1 := sq_term_le (a := secondDerivAmp H ι σ y) (a' := secondDerivAmp Hu ι σ y) c1 (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (amp_sub_le _ _) q0
    have t2 := sq_term_le (a := vortGradAmp H ι σ y) (a' := vortGradAmp Hu ι σ y) c2 (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (amp_sub_le _ _) q0
    have t3 := sq_term_le (a := vortAmp G ι σ y) (a' := vortAmp Gu ι σ y) c3 (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (amp_sub_le _ _) q0
    have t4 := sq_term_le (a := gradAmp G ι σ y) (a' := gradAmp Gu ι σ y) c4 (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (amp_sub_le _ _) q0
    have t5 := sq_term_le (a := velAmp v ι σ y / (1 + ‖y‖)) (a' := velAmp u ι σ y / (1 + ‖y‖)) c5
      (div_nonneg (Real.sqrt_nonneg _) hy.le) (div_nonneg (Real.sqrt_nonneg _) hy.le) (amp_sub_div_le _ _ hy) q0
    have p1 := Internal.FieldModes.cnormSq_nonneg (modeSecondDeriv ι H σ y)
    have p2 := Internal.FieldModes.cnormSq_nonneg (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    have p3 := Internal.FieldModes.cnormSq_nonneg (modeGrad ι G σ y)
    have p4 := Internal.FieldModes.cnormSq_nonneg (curlOfGrad (modeGrad ι G σ y))
    have p5 : 0 ≤ cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 :=
      div_nonneg (Internal.FieldModes.cnormSq_nonneg _) (by positivity)
    have d1 := Internal.FieldModes.cnormSq_nonneg (modeSecondDeriv ι Hu σ y - modeSecondDeriv ι H σ y)
    have d2 := Internal.FieldModes.cnormSq_nonneg (curlGradOfSecondDeriv (modeSecondDeriv ι Hu σ y) - curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    have d3 := Internal.FieldModes.cnormSq_nonneg (modeGrad ι Gu σ y - modeGrad ι G σ y)
    have d4 := Internal.FieldModes.cnormSq_nonneg (curlOfGrad (modeGrad ι Gu σ y) - curlOfGrad (modeGrad ι G σ y))
    have d5 : 0 ≤ cnormSq (modeVel ι u σ y - modeVel ι v σ y) / (1 + ‖y‖) ^ 2 :=
      div_nonneg (Internal.FieldModes.cnormSq_nonneg _) (by positivity)
    refine ennreal_step (by positivity) (by positivity) (by linarith) (by linarith) ?_
    rw [five_split]
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) t5) |>.trans (le_of_eq ?_)
    simp only [secondDerivAmp, vortGradAmp, vortAmp, gradAmp, velAmp, div_pow, sqrt_cnormSq_sq]
    ring

def ampSqAt (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (modeSecondDeriv ι H σ y) + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    + cnormSq (modeGrad ι G σ y) + cnormSq (curlOfGrad (modeGrad ι G σ y))
    + cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2

def diffSqAt (u : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
    (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (modeSecondDeriv ι Hu σ y - modeSecondDeriv ι H σ y)
    + cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι Hu σ y) - curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    + cnormSq (modeGrad ι Gu σ y - modeGrad ι G σ y)
    + cnormSq (curlOfGrad (modeGrad ι Gu σ y) - curlOfGrad (modeGrad ι G σ y))
    + cnormSq (modeVel ι u σ y - modeVel ι v σ y) / (1 + ‖y‖) ^ 2

theorem ampTotal_eq (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    ampTotal v G H σ y = ∑' ι, ENNReal.ofReal (ampSqAt v G H ι σ y) := rfl

theorem diffTotal_eq (u : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
    (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (σ : ℝ) (y : Space) :
    diffTotal u Gu Hu v G H σ y = ∑' ι, ENNReal.ofReal (diffSqAt u Gu Hu v G H ι σ y) := rfl

def IsAmp (A : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ) : Prop :=
  ∀ v G H ι σ y, 0 ≤ A v G H ι σ y ∧ A v G H ι σ y ^ 2 ≤ ampSqAt v G H ι σ y ∧
    ∀ u Gu Hu, (A u Gu Hu ι σ y - A v G H ι σ y) ^ 2 ≤ diffSqAt u Gu Hu v G H ι σ y

theorem amp_sq_sub_le {β : Type*} [Fintype β] (x' x : β → ℂ) :
    (Real.sqrt (cnormSq x') - Real.sqrt (cnormSq x)) ^ 2 ≤ cnormSq (x' - x) := by
  rw [← sq_abs, ← sqrt_cnormSq_sq (x' - x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (sqrt_cnormSq_sub_le x' x) 2

theorem ampSqAt_parts (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    0 ≤ cnormSq (modeSecondDeriv ι H σ y) ∧ 0 ≤ cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y)) ∧
      0 ≤ cnormSq (modeGrad ι G σ y) ∧ 0 ≤ cnormSq (curlOfGrad (modeGrad ι G σ y)) ∧
      0 ≤ cnormSq (modeVel ι v σ y) / (1 + ‖y‖) ^ 2 :=
  ⟨Internal.FieldModes.cnormSq_nonneg _, Internal.FieldModes.cnormSq_nonneg _,
    Internal.FieldModes.cnormSq_nonneg _, Internal.FieldModes.cnormSq_nonneg _,
    div_nonneg (Internal.FieldModes.cnormSq_nonneg _) (by positivity)⟩

theorem diffSqAt_parts (u : ℝ → Space → Space) (Gu : ℝ → Space → (Space →L[ℝ] Space))
    (Hu : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    0 ≤ cnormSq (modeSecondDeriv ι Hu σ y - modeSecondDeriv ι H σ y) ∧
      0 ≤ cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι Hu σ y) - curlGradOfSecondDeriv (modeSecondDeriv ι H σ y)) ∧
      0 ≤ cnormSq (modeGrad ι Gu σ y - modeGrad ι G σ y) ∧
      0 ≤ cnormSq (curlOfGrad (modeGrad ι Gu σ y) - curlOfGrad (modeGrad ι G σ y)) ∧
      0 ≤ cnormSq (modeVel ι u σ y - modeVel ι v σ y) / (1 + ‖y‖) ^ 2 :=
  ⟨Internal.FieldModes.cnormSq_nonneg _, Internal.FieldModes.cnormSq_nonneg _,
    Internal.FieldModes.cnormSq_nonneg _, Internal.FieldModes.cnormSq_nonneg _,
    div_nonneg (Internal.FieldModes.cnormSq_nonneg _) (by positivity)⟩

theorem isAmp_secondDeriv : IsAmp (fun _ _ H ι σ y => secondDerivAmp H ι σ y) := fun v G H ι σ y => by
  obtain ⟨a1, a2, a3, a4, a5⟩ := ampSqAt_parts v G H ι σ y
  refine ⟨Real.sqrt_nonneg _, ?_, fun u Gu Hu => ?_⟩
  · simp only [secondDerivAmp, sqrt_cnormSq_sq, ampSqAt]; linarith
  · obtain ⟨d1, d2, d3, d4, d5⟩ := diffSqAt_parts u Gu Hu v G H ι σ y
    have := amp_sq_sub_le (modeSecondDeriv ι Hu σ y) (modeSecondDeriv ι H σ y)
    simp only [secondDerivAmp, diffSqAt]; linarith

theorem isAmp_vortGrad : IsAmp (fun _ _ H ι σ y => vortGradAmp H ι σ y) := fun v G H ι σ y => by
  obtain ⟨a1, a2, a3, a4, a5⟩ := ampSqAt_parts v G H ι σ y
  refine ⟨Real.sqrt_nonneg _, ?_, fun u Gu Hu => ?_⟩
  · simp only [vortGradAmp, sqrt_cnormSq_sq, ampSqAt]; linarith
  · obtain ⟨d1, d2, d3, d4, d5⟩ := diffSqAt_parts u Gu Hu v G H ι σ y
    have := amp_sq_sub_le (curlGradOfSecondDeriv (modeSecondDeriv ι Hu σ y)) (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y))
    simp only [vortGradAmp, diffSqAt]; linarith

theorem isAmp_grad : IsAmp (fun _ G _ ι σ y => gradAmp G ι σ y) := fun v G H ι σ y => by
  obtain ⟨a1, a2, a3, a4, a5⟩ := ampSqAt_parts v G H ι σ y
  refine ⟨Real.sqrt_nonneg _, ?_, fun u Gu Hu => ?_⟩
  · simp only [gradAmp, sqrt_cnormSq_sq, ampSqAt]; linarith
  · obtain ⟨d1, d2, d3, d4, d5⟩ := diffSqAt_parts u Gu Hu v G H ι σ y
    have := amp_sq_sub_le (modeGrad ι Gu σ y) (modeGrad ι G σ y)
    simp only [gradAmp, diffSqAt]; linarith

theorem isAmp_vort : IsAmp (fun _ G _ ι σ y => vortAmp G ι σ y) := fun v G H ι σ y => by
  obtain ⟨a1, a2, a3, a4, a5⟩ := ampSqAt_parts v G H ι σ y
  refine ⟨Real.sqrt_nonneg _, ?_, fun u Gu Hu => ?_⟩
  · simp only [vortAmp, sqrt_cnormSq_sq, ampSqAt]; linarith
  · obtain ⟨d1, d2, d3, d4, d5⟩ := diffSqAt_parts u Gu Hu v G H ι σ y
    have := amp_sq_sub_le (curlOfGrad (modeGrad ι Gu σ y)) (curlOfGrad (modeGrad ι G σ y))
    simp only [vortAmp, diffSqAt]; linarith

theorem isAmp_vel : IsAmp (fun v _ _ ι σ y => velAmp v ι σ y / (1 + ‖y‖)) := fun v G H ι σ y => by
  obtain ⟨a1, a2, a3, a4, a5⟩ := ampSqAt_parts v G H ι σ y
  have hy : 0 < 1 + ‖y‖ := by positivity
  refine ⟨div_nonneg (Real.sqrt_nonneg _) hy.le, ?_, fun u Gu Hu => ?_⟩
  · simp only [velAmp, div_pow, sqrt_cnormSq_sq, ampSqAt]; linarith
  · obtain ⟨d1, d2, d3, d4, d5⟩ := diffSqAt_parts u Gu Hu v G H ι σ y
    have h := amp_sq_sub_le (modeVel ι u σ y) (modeVel ι v σ y)
    have h2 : (velAmp u ι σ y / (1 + ‖y‖) - velAmp v ι σ y / (1 + ‖y‖)) ^ 2
        ≤ cnormSq (modeVel ι u σ y - modeVel ι v σ y) / (1 + ‖y‖) ^ 2 := by
      rw [← sub_div, div_pow]
      exact div_le_div_of_nonneg_right h (by positivity)
    simp only [diffSqAt]; linarith

theorem tsum_shift_two (f : ℤ × ℤ → ℝ≥0∞) (s s' : ℤ × ℤ) (a : ℝ≥0∞) :
    ∑' ι, a * (f (ι - s) + f (ι - s')) = (2 * a) * ∑' ι, f ι := by
  have h1 : ∑' ι, f (ι - s) = ∑' ι, f ι := (Equiv.subRight s).tsum_eq f
  have h2 : ∑' ι, f (ι - s') = ∑' ι, f ι := (Equiv.subRight s').tsum_eq f
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, h1, h2]
  ring

theorem isRestBound_prod {A B : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    (hA : IsAmp A) (hB : IsAmp B) (c : ℤ × ℤ → ℝ → Space → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ ι σ y, |c ι σ y| ≤ M) (s s' : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => c ι σ y * (A v G H (ι - s) σ y * B v G H (ι - s') σ y)) v G H := by
  refine ⟨2 * M, by positivity, fun σ y => ?_, fun t ht u Gu Hu σ y => ?_⟩
  · rw [ampTotal_eq, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← tsum_shift_two _ s s']
    refine ENNReal.tsum_le_tsum fun ι => ?_
    obtain ⟨a0, a1, -⟩ := hA v G H (ι - s) σ y
    obtain ⟨b0, b1, -⟩ := hB v G H (ι - s') σ y
    have q1 := (ampSqAt_parts v G H (ι - s) σ y)
    have q2 := (ampSqAt_parts v G H (ι - s') σ y)
    have n1 : 0 ≤ ampSqAt v G H (ι - s) σ y := (sq_nonneg _).trans a1
    have n2 : 0 ≤ ampSqAt v G H (ι - s') σ y := (sq_nonneg _).trans b1
    rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_mul hM]
    refine ENNReal.ofReal_le_ofReal ?_
    dsimp only
    rw [abs_mul, abs_of_nonneg (mul_nonneg a0 b0)]
    have hab : A v G H (ι - s) σ y * B v G H (ι - s') σ y ≤ ampSqAt v G H (ι - s) σ y + ampSqAt v G H (ι - s') σ y := by
      nlinarith [sq_nonneg (A v G H (ι - s) σ y - B v G H (ι - s') σ y)]
    exact mul_le_mul (hc ι σ y) hab (mul_nonneg a0 b0) hM
  · rw [ampTotal_eq, diffTotal_eq]
    have e1 : ENNReal.ofReal (2 * M * (1 + 1 / t)) = 2 * ENNReal.ofReal (M * (1 + 1 / t)) := by
      rw [mul_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have e2 : ENNReal.ofReal (2 * M * t) = 2 * ENNReal.ofReal (M * t) := by
      rw [mul_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [e1, e2, ← tsum_shift_two _ s s', ← tsum_shift_two _ s s', ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun ι => ?_
    obtain ⟨a0, a1, a2⟩ := hA v G H (ι - s) σ y
    obtain ⟨b0, b1, b2⟩ := hB v G H (ι - s') σ y
    obtain ⟨a0', -, -⟩ := hA u Gu Hu (ι - s) σ y
    obtain ⟨b0', -, -⟩ := hB u Gu Hu (ι - s') σ y
    have da := a2 u Gu Hu
    have db := b2 u Gu Hu
    have m1 : 0 ≤ diffSqAt u Gu Hu v G H (ι - s) σ y := (sq_nonneg _).trans da
    have m2 : 0 ≤ diffSqAt u Gu Hu v G H (ι - s') σ y := (sq_nonneg _).trans db
    have n1 : 0 ≤ ampSqAt v G H (ι - s) σ y := (sq_nonneg _).trans a1
    have n2 : 0 ≤ ampSqAt v G H (ι - s') σ y := (sq_nonneg _).trans b1
    have ht' : 0 ≤ 1 + 1 / t := by positivity
    rw [← ENNReal.ofReal_add m1 m2, ← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    dsimp only
    have hda : |A u Gu Hu (ι - s) σ y - A v G H (ι - s) σ y| ≤ Real.sqrt (diffSqAt u Gu Hu v G H (ι - s) σ y) :=
      Real.abs_le_sqrt da
    have hdb : |B u Gu Hu (ι - s') σ y - B v G H (ι - s') σ y| ≤ Real.sqrt (diffSqAt u Gu Hu v G H (ι - s') σ y) :=
      Real.abs_le_sqrt db
    have hp := prod_diff_le a0 b0 b0' hda hdb ht
    rw [Real.sq_sqrt m1, Real.sq_sqrt m2] at hp
    have hq : |A u Gu Hu (ι - s) σ y * B u Gu Hu (ι - s') σ y - A v G H (ι - s) σ y * B v G H (ι - s') σ y|
        ≤ (1 + 1 / t) * (diffSqAt u Gu Hu v G H (ι - s) σ y + diffSqAt u Gu Hu v G H (ι - s') σ y)
          + t * (ampSqAt v G H (ι - s) σ y + ampSqAt v G H (ι - s') σ y) := by
      refine hp.trans ?_
      nlinarith
    rw [← mul_sub, abs_mul]
    calc |c ι σ y| * |A u Gu Hu (ι - s) σ y * B u Gu Hu (ι - s') σ y - A v G H (ι - s) σ y * B v G H (ι - s') σ y|
        ≤ M * ((1 + 1 / t) * (diffSqAt u Gu Hu v G H (ι - s) σ y + diffSqAt u Gu Hu v G H (ι - s') σ y)
          + t * (ampSqAt v G H (ι - s) σ y + ampSqAt v G H (ι - s') σ y)) :=
          mul_le_mul (hc ι σ y) hq (abs_nonneg _) hM
      _ = M * (1 + 1 / t) * (diffSqAt u Gu Hu v G H (ι - s) σ y + diffSqAt u Gu Hu v G H (ι - s') σ y)
          + M * t * (ampSqAt v G H (ι - s) σ y + ampSqAt v G H (ι - s') σ y) := by ring

theorem restBound_of_zero (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun _ _ _ _ _ _ => 0) v G H :=
  ⟨0, le_rfl, fun σ y => by simp, fun t ht u Gu Hu σ y => by simp⟩

theorem IsRestBound.neg {R : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsRestBound R v G H) :
    IsRestBound (fun v G H ι σ y => -R v G H ι σ y) v G H := by
  obtain ⟨K, hK, a, b⟩ := h
  refine ⟨K, hK, fun σ y => ?_, fun t ht u Gu Hu σ y => ?_⟩
  · simpa only [abs_neg] using a σ y
  · have e : ∀ ι, |-R u Gu Hu ι σ y - -R v G H ι σ y| = |R u Gu Hu ι σ y - R v G H ι σ y| := fun ι => by
      rw [← abs_neg]; ring_nf
    simp only [e]
    exact b t ht u Gu Hu σ y

theorem isRestBound_finsetSum {κ : Type*} (S : Finset κ)
    {R : κ → (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
      (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : ∀ α ∈ S, IsRestBound (R α) v G H) :
    IsRestBound (fun v G H ι σ y => ∑ α ∈ S, R α v G H ι σ y) v G H := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using restBound_of_zero v G H
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := ih fun α hα => h α (Finset.mem_insert_of_mem hα)
    have := h1.add h2
    simpa only [Finset.sum_insert ha] using this

end Internal.DensityPassageRestBound

end Coercive

end Breakdown
