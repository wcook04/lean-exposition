import Breakdown.CertCell.PatchModeWeak
import Breakdown.CertCell.PatchRoughTest

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.PatchTraceBound

theorem box_finite (ρ R : ℝ) : IsFiniteMeasure (volume.restrict (Icc ρ R ×ˢ Icc (-R) R)) :=
  isFiniteMeasure_restrict.2 (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne

theorem integrableOn_of_memLp {f : ℝ × ℝ → ℂ} {ρ R : ℝ} (h : MemLp f 2 (volume.restrict (Icc ρ R ×ˢ Icc (-R) R))) :
    IntegrableOn f (Icc ρ R ×ˢ Icc (-R) R) := by
  have := box_finite ρ R
  exact h.integrable (by norm_num)

theorem integrableOn_radial {f : ℝ × ℝ → ℂ} {ρ R : ℝ} (h : IntegrableOn f (Icc ρ R ×ˢ Icc (-R) R)) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * f p) (Icc ρ R ×ˢ Icc (-R) R) := by
  refine h.bdd_mul (c := |ρ| + |R|) (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable ?_
  refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 (Eventually.of_forall fun p hp => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases le_total 0 p.1 with h0 | h0
  · rw [abs_of_nonneg h0]; linarith [hp.1.2, le_abs_self R, abs_nonneg ρ]
  · rw [abs_of_nonpos h0]; linarith [hp.1.1, neg_abs_le ρ, abs_nonneg R]

theorem divergence_rough {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (η : ℤ × ℤ)
    {Ψ : ℝ × ℝ → ℂ} {K : NNReal} (hΨ : LipschitzWith K Ψ) (hc : HasCompactSupport Ψ)
    (hpos : ∀ p ∈ tsupport Ψ, 0 < p.1) :
    (∫ p, fderiv ℝ Ψ p (1, 0) * ((p.1 : ℂ) * planeVel η v 0 p.1 p.2)) +
      (∫ p, fderiv ℝ Ψ p (0, 1) * ((p.1 : ℂ) * planeVel η v 2 p.1 p.2)) +
      ∫ p, Ψ p * (-((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2) = 0 := by
  refine weak_identity_rough (fun ρ R hρ => integrableOn_radial (integrableOn_of_memLp (planeVel_memLp hv η 0 hρ)))
    (fun ρ R hρ => integrableOn_radial (integrableOn_of_memLp (planeVel_memLp hv η 2 hρ)))
    (fun ρ R hρ => (integrableOn_of_memLp (planeVel_memLp hv η 1 hρ)).const_mul _) ?_ hΨ hc hpos
  intro ψ hψ hcs hps
  have h := planeVel_divergence_weak hv η ψ hψ hcs hps
  have e1 : ∫ p : ℝ × ℝ, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * ((p.1 : ℂ) * planeVel η v 0 p.1 p.2) =
      ∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * planeVel η v 0 p.1 p.2 := by
    congr 1; funext p; push_cast; ring
  have e2 : ∫ p : ℝ × ℝ, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * ((p.1 : ℂ) * planeVel η v 2 p.1 p.2) =
      ∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * planeVel η v 2 p.1 p.2 := by
    congr 1; funext p; push_cast; ring
  have e3 : ∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * (-((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2) =
      -((η.2 : ℂ) * Complex.I) * ∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * planeVel η v 1 p.1 p.2 := by
    rw [← integral_const_mul]; congr 1; funext p; ring
  rw [e1, e2, e3]
  linear_combination h

theorem radial_rough {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (η : ℤ × ℤ)
    {Ψ : ℝ × ℝ → ℂ} {K : NNReal} (hΨ : LipschitzWith K Ψ) (hc : HasCompactSupport Ψ)
    (hpos : ∀ p ∈ tsupport Ψ, 0 < p.1) :
    (∫ p, fderiv ℝ Ψ p (1, 0) * ((p.1 : ℂ) * planeVel η v 0 p.1 p.2)) +
      (∫ p, fderiv ℝ Ψ p (0, 1) * (0 : ℂ)) +
      ∫ p, Ψ p * (-((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2 - (p.1 : ℂ) * planeVelHeight η G 2 p.1 p.2) = 0 := by
  have iU0 := fun ρ R (hρ : (0 : ℝ) < ρ) => integrableOn_radial (integrableOn_of_memLp (planeVel_memLp hv η 0 (R := R) hρ))
  have iU1 := fun ρ R (hρ : (0 : ℝ) < ρ) => (integrableOn_of_memLp (planeVel_memLp hv η 1 (R := R) hρ)).const_mul
    (-((η.2 : ℂ) * Complex.I))
  have iH := fun ρ R (hρ : (0 : ℝ) < ρ) => integrableOn_radial (integrableOn_of_memLp (planeHeight_memLp hv η (R := R) hρ))
  refine weak_identity_rough iU0 (fun ρ R _ => integrableOn_zero)
    (fun ρ R hρ => (iU1 ρ R hρ).sub (iH ρ R hρ)) ?_ hΨ hc hpos
  intro ψ hψ hcs hps
  have hD := planeVel_divergence_weak hv η ψ hψ hcs hps
  have hZ := planeVel_height_weak hv η ψ hψ hcs hps
  obtain ⟨ρ, R, hρ, hS⟩ := Internal.PatchRoughTest.exists_strip hcs hps
  obtain ⟨M, hM⟩ := hψ.continuous.bounded_above_of_compact_support hcs
  have z1 : ∀ p, p ∉ Internal.PatchRoughTest.strip ρ R → ((ψ p : ℝ) : ℂ) = 0 := fun p hp => by
    simp [Internal.PatchRoughTest.zero_off hS p hp]
  have i1 : Integrable fun p : ℝ × ℝ => ((ψ p : ℝ) : ℂ) * planeVel η v 1 p.1 p.2 :=
    Internal.PatchRoughTest.integrable_bdd_mul (M := M)
      (Complex.continuous_ofReal.comp hψ.continuous).aestronglyMeasurable
      (fun p => by rw [Complex.norm_real]; exact hM p) z1
      (integrableOn_of_memLp (planeVel_memLp hv η 1 hρ))
  have i2 : Integrable fun p : ℝ × ℝ => ((ψ p : ℝ) : ℂ) * ((p.1 : ℂ) * planeVelHeight η G 2 p.1 p.2) :=
    Internal.PatchRoughTest.integrable_bdd_mul (M := M)
      (Complex.continuous_ofReal.comp hψ.continuous).aestronglyMeasurable
      (fun p => by rw [Complex.norm_real]; exact hM p) z1
      (integrableOn_radial (integrableOn_of_memLp (planeHeight_memLp hv η hρ)))
  have e1 : ∫ p : ℝ × ℝ, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * ((p.1 : ℂ) * planeVel η v 0 p.1 p.2) =
      ∫ p : ℝ × ℝ, ((p.1 * fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * planeVel η v 0 p.1 p.2 := by
    congr 1; funext p; push_cast; ring
  have e3 : ∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * (-((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2 -
      (p.1 : ℂ) * planeVelHeight η G 2 p.1 p.2) =
      -((η.2 : ℂ) * Complex.I) * (∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * planeVel η v 1 p.1 p.2) -
        ∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * planeVelHeight η G 2 p.1 p.2 := by
    rw [← integral_const_mul]
    have e4 : ∫ p : ℝ × ℝ, ((p.1 * ψ p : ℝ) : ℂ) * planeVelHeight η G 2 p.1 p.2 =
        ∫ p : ℝ × ℝ, ((ψ p : ℝ) : ℂ) * ((p.1 : ℂ) * planeVelHeight η G 2 p.1 p.2) := by
      congr 1; funext p; push_cast; ring
    rw [e4, ← integral_sub (i1.const_mul _) i2]
    congr 1; funext p; ring
  simp only [Pi.sub_apply]
  rw [e1, e3]
  simp only [mul_zero, integral_zero, add_zero]
  linear_combination hD - hZ

def clampTo (a b x : ℝ) : ℝ := max a (min x b)

theorem clampTo_slope (a b : ℝ) : LipschitzWith 1 (clampTo a b) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, clampTo]
  rw [max_comm a, max_comm a]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

theorem clampTo_of_mem {a b x : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : clampTo a b x = x := by
  simp [clampTo, min_eq_left h2, max_eq_right h1]

theorem clampTo_of_le {a b x : ℝ} (hab : a ≤ b) (h : x ≤ a) : clampTo a b x = a := by
  simp only [clampTo, min_eq_left (h.trans hab)]
  exact max_eq_left h

theorem clampTo_of_ge {a b x : ℝ} (hab : a ≤ b) (h : b ≤ x) : clampTo a b x = b := by
  simp [clampTo, min_eq_right h, max_eq_right hab]

theorem clampTo_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : a ≤ clampTo a b x ∧ clampTo a b x ≤ b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem slope_mul {f g : ℝ × ℝ → ℂ} {Kf Kg : NNReal} {Mf Mg : ℝ} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hMf : ∀ x, ‖f x‖ ≤ Mf) (hMg : ∀ x, ‖g x‖ ≤ Mg) :
    ∃ K : NNReal, LipschitzWith K (fun x => f x * g x) := by
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  refine ⟨⟨Mf * Kg + Mg * Kf, by positivity⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [dist_eq_norm]
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 := hf.dist_le_mul x y
  have h2 := hg.dist_le_mul x y
  simp only [dist_eq_norm] at h1 h2
  calc ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖ ≤ Mf * (Kg * ‖x - y‖) + Mg * (Kf * ‖x - y‖) :=
        add_le_add (mul_le_mul (hMf x) h2 (norm_nonneg _) hMf0) (mul_le_mul (hMg y) h1 (norm_nonneg _) hMg0)
    _ = (Mf * Kg + Mg * Kf) * ‖x - y‖ := by ring

def edgeValue (φ : ℝ × ℝ → ℂ) (ρ₁ ρ₂ r : ℝ) : ℂ := φ (clampTo ρ₁ ρ₂ r, 0)

def heightWeight (h z : ℝ) : ℝ := 1 - clampTo 0 h z / h

def coreTest (φ : ℝ × ℝ → ℂ) (ρ₁ ρ₂ h : ℝ) (p : ℝ × ℝ) : ℂ :=
  φ (clampTo ρ₁ ρ₂ p.1, clampTo 0 h p.2) - edgeValue φ ρ₁ ρ₂ p.1 * (heightWeight h p.2 : ℂ)

def rampWeight (h : ℝ) (n : ℕ) (z : ℝ) : ℝ := min (heightWeight h z) (max 0 (1 + ((n : ℝ) + 1) * z))

def rampTest (φ : ℝ × ℝ → ℂ) (ρ₁ ρ₂ h : ℝ) (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  edgeValue φ ρ₁ ρ₂ p.1 * (rampWeight h n p.2 : ℂ)

theorem edgeValue_slope {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ) (ρ₁ ρ₂ : ℝ) :
    LipschitzWith K (edgeValue φ ρ₁ ρ₂) := by
  have h1 : LipschitzWith 1 (fun r : ℝ => (clampTo ρ₁ ρ₂ r, (0 : ℝ))) := by
    simpa using (clampTo_slope ρ₁ ρ₂).prodMk (LipschitzWith.const (0 : ℝ))
  have h2 := hφ.comp h1
  rw [mul_one] at h2
  exact h2

theorem edgeValue_side {φ : ℝ × ℝ → ℂ} {ρ₁ ρ₂ : ℝ} (hρ : ρ₁ ≤ ρ₂) (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0)
    (r : ℝ) (hr : r ∉ Icc ρ₁ ρ₂) : edgeValue φ ρ₁ ρ₂ r = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hr
  rcases hr with hr | hr
  · rw [edgeValue, clampTo_of_le hρ hr.le]; exact (hside 0).1
  · rw [edgeValue, clampTo_of_ge hρ hr.le]; exact (hside 0).2

theorem edgeValue_bound {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ) {ρ₁ ρ₂ : ℝ} (hρ : ρ₁ ≤ ρ₂)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) (r : ℝ) : ‖edgeValue φ ρ₁ ρ₂ r‖ ≤ K * (ρ₂ - ρ₁) := by
  have h := hφ.dist_le_mul (clampTo ρ₁ ρ₂ r, 0) (ρ₁, 0)
  rw [dist_eq_norm, (hside 0).1, sub_zero, Prod.dist_eq, Real.dist_eq, dist_self, max_eq_left (abs_nonneg _)] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ K.2)
  have hm := clampTo_mem hρ r
  rw [abs_of_nonneg (by linarith [hm.1])]
  linarith [hm.2]

theorem hw_mem {h : ℝ} (hh : 0 < h) (z : ℝ) : 0 ≤ heightWeight h z ∧ heightWeight h z ≤ 1 := by
  have hm := clampTo_mem hh.le z
  unfold heightWeight
  constructor
  · rw [sub_nonneg, div_le_one hh]; exact hm.2
  · have : 0 ≤ clampTo 0 h z / h := div_nonneg hm.1 hh.le
    linarith

theorem hw_slope {h : ℝ} (hh : 0 < h) : LipschitzWith (Real.toNNReal (1 / h)) (heightWeight h) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  have h1 := (clampTo_slope 0 h).dist_le_mul z w
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h1 ⊢
  rw [Real.coe_toNNReal _ (by positivity), heightWeight, heightWeight,
    show 1 - clampTo 0 h z / h - (1 - clampTo 0 h w / h) = -((clampTo 0 h z - clampTo 0 h w) / h) by ring,
    abs_neg, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  calc |clampTo 0 h z - clampTo 0 h w| ≤ |z - w| := h1
    _ = 1 / h * |z - w| * h := by field_simp

theorem hw_of_nonpos {h : ℝ} (hh : 0 < h) {z : ℝ} (hz : z ≤ 0) : heightWeight h z = 1 := by
  simp [heightWeight, clampTo_of_le hh.le hz]

theorem hw_of_ge {h : ℝ} (hh : 0 < h) {z : ℝ} (hz : h ≤ z) : heightWeight h z = 0 := by
  simp [heightWeight, clampTo_of_ge hh.le hz, div_self hh.ne']

theorem hw_of_mem {h : ℝ} {z : ℝ} (h1 : 0 ≤ z) (h2 : z ≤ h) : heightWeight h z = 1 - z / h := by
  simp [heightWeight, clampTo_of_mem h1 h2]

theorem core_slope {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ) {ρ₁ ρ₂ h : ℝ} (hρ : ρ₁ ≤ ρ₂) (hh : 0 < h)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) : ∃ K' : NNReal, LipschitzWith K' (coreTest φ ρ₁ ρ₂ h) := by
  have h1 : LipschitzWith K (fun p : ℝ × ℝ => φ (clampTo ρ₁ ρ₂ p.1, clampTo 0 h p.2)) := by
    have hm : LipschitzWith 1 (fun p : ℝ × ℝ => (clampTo ρ₁ ρ₂ p.1, clampTo 0 h p.2)) := by
      simpa using ((clampTo_slope ρ₁ ρ₂).comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))).prodMk
        ((clampTo_slope 0 h).comp (LipschitzWith.prod_snd (α := ℝ) (β := ℝ)))
    have := hφ.comp hm
    rw [mul_one] at this
    exact this
  have hf : LipschitzWith K (fun p : ℝ × ℝ => edgeValue φ ρ₁ ρ₂ p.1) := by
    have := (edgeValue_slope hφ ρ₁ ρ₂).comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
    rw [mul_one] at this
    exact this
  have hg : LipschitzWith (Real.toNNReal (1 / h)) (fun p : ℝ × ℝ => ((heightWeight h p.2 : ℝ) : ℂ)) := by
    have := (Complex.isometry_ofReal.lipschitz.comp (hw_slope hh)).comp (LipschitzWith.prod_snd (α := ℝ) (β := ℝ))
    simp only [one_mul, mul_one] at this
    exact this
  obtain ⟨K₂, hK₂⟩ := slope_mul hf hg (fun p => edgeValue_bound hφ hρ hside p.1) (Mg := 1) (fun p => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hw_mem hh _).1]; exact (hw_mem hh _).2)
  exact ⟨K + K₂, h1.sub hK₂⟩

theorem core_zero {φ : ℝ × ℝ → ℂ} {ρ₁ ρ₂ h : ℝ} (hρ : ρ₁ ≤ ρ₂) (hh : 0 < h)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) (htop : ∀ r, φ (r, h) = 0) (p : ℝ × ℝ)
    (hp : p ∉ patch ρ₁ ρ₂ h) : coreTest φ ρ₁ ρ₂ h p = 0 := by
  simp only [patch, mem_prod, mem_Icc, not_and_or, not_le] at hp
  unfold coreTest
  rcases hp with (hp | hp) | (hp | hp)
  · rw [edgeValue_side hρ hside p.1 (fun h' => absurd h'.1 (not_le.2 hp)), clampTo_of_le hρ hp.le,
      (hside _).1, zero_mul, sub_zero]
  · rw [edgeValue_side hρ hside p.1 (fun h' => absurd h'.2 (not_le.2 hp)), clampTo_of_ge hρ hp.le,
      (hside _).2, zero_mul, sub_zero]
  · rw [clampTo_of_le hh.le hp.le, hw_of_nonpos hh hp.le, edgeValue]
    simp
  · rw [clampTo_of_ge hh.le hp.le, hw_of_ge hh hp.le, htop]
    simp

theorem ramp_mem {h : ℝ} (hh : 0 < h) (n : ℕ) (z : ℝ) : 0 ≤ rampWeight h n z ∧ rampWeight h n z ≤ 1 :=
  ⟨le_min (hw_mem hh z).1 (le_max_left _ _), (min_le_left _ _).trans (hw_mem hh z).2⟩

theorem ramp_slope {h : ℝ} (hh : 0 < h) (n : ℕ) : ∃ K : NNReal, LipschitzWith K (rampWeight h n) := by
  have h2 : LipschitzWith (Real.toNNReal ((n : ℝ) + 1)) (fun z : ℝ => 1 + ((n : ℝ) + 1) * z) := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq,
      show 1 + ((n : ℝ) + 1) * z - (1 + ((n : ℝ) + 1) * w) = ((n : ℝ) + 1) * (z - w) by ring, abs_mul,
      abs_of_pos (by positivity)]
  exact ⟨_, (hw_slope hh).min ((LipschitzWith.const (α := ℝ) (0 : ℝ)).max h2)⟩

theorem ramp_of_nonneg {h : ℝ} (hh : 0 < h) (n : ℕ) {z : ℝ} (hz : 0 ≤ z) : rampWeight h n z = heightWeight h z := by
  refine min_eq_left ((hw_mem hh z).2.trans ?_)
  refine le_max_of_le_right ?_
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem ramp_of_neg {h : ℝ} (n : ℕ) {z : ℝ} (hz : 1 + ((n : ℝ) + 1) * z ≤ 0) (hh : 0 < h) :
    rampWeight h n z = 0 := by
  rw [rampWeight, max_eq_left hz]
  exact min_eq_right (hw_mem hh z).1

theorem ramp_of_ge {h : ℝ} (hh : 0 < h) (n : ℕ) {z : ℝ} (hz : h ≤ z) : rampWeight h n z = 0 := by
  rw [rampWeight, hw_of_ge hh hz]
  exact min_eq_left (le_max_left _ _)

theorem rampTest_slope {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ) {ρ₁ ρ₂ h : ℝ} (hρ : ρ₁ ≤ ρ₂) (hh : 0 < h)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) (n : ℕ) : ∃ K' : NNReal, LipschitzWith K' (rampTest φ ρ₁ ρ₂ h n) := by
  have hf : LipschitzWith K (fun p : ℝ × ℝ => edgeValue φ ρ₁ ρ₂ p.1) := by
    have := (edgeValue_slope hφ ρ₁ ρ₂).comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
    rw [mul_one] at this
    exact this
  obtain ⟨Kr, hKr⟩ := ramp_slope hh n
  have hg : LipschitzWith Kr (fun p : ℝ × ℝ => ((rampWeight h n p.2 : ℝ) : ℂ)) := by
    have := (Complex.isometry_ofReal.lipschitz.comp hKr).comp (LipschitzWith.prod_snd (α := ℝ) (β := ℝ))
    simp only [one_mul, mul_one] at this
    exact this
  exact slope_mul hf hg (fun p => edgeValue_bound hφ hρ hside p.1) (Mg := 1) (fun p => by
    rw [Complex.norm_real, Real.norm_of_nonneg (ramp_mem hh n _).1]; exact (ramp_mem hh n _).2)

theorem rampTest_zero {φ : ℝ × ℝ → ℂ} {ρ₁ ρ₂ h : ℝ} (hρ : ρ₁ ≤ ρ₂) (hh : 0 < h)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) (n : ℕ) (p : ℝ × ℝ)
    (hp : p ∉ Icc ρ₁ ρ₂ ×ˢ Icc (-1) h) : rampTest φ ρ₁ ρ₂ h n p = 0 := by
  simp only [mem_prod, not_and_or] at hp
  unfold rampTest
  rcases hp with hp | hp
  · rw [edgeValue_side hρ hside p.1 hp, zero_mul]
  · rw [mem_Icc, not_and_or, not_le, not_le] at hp
    rcases hp with hp | hp
    · rw [ramp_of_neg n (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hh]; simp
    · rw [ramp_of_ge hh n hp.le]; simp

theorem fderiv_split {F : ℝ → ℂ} {c : ℝ → ℝ} {p : ℝ × ℝ} (hF : DifferentiableAt ℝ F p.1)
    (hc : DifferentiableAt ℝ c p.2) :
    fderiv ℝ (fun q : ℝ × ℝ => F q.1 * (c q.2 : ℂ)) p (1, 0) = deriv F p.1 * (c p.2 : ℂ) ∧
    fderiv ℝ (fun q : ℝ × ℝ => F q.1 * (c q.2 : ℂ)) p (0, 1) = F p.1 * ((deriv c p.2 : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => F q.1) ((fderiv ℝ F p.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    hF.hasFDerivAt.comp p (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => (c q.2 : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ c p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (hc.hasFDerivAt.comp p hasFDerivAt_snd)
  have h3 := HasFDerivAt.fderiv (f := fun q : ℝ × ℝ => F q.1 * (c q.2 : ℂ)) (h1.mul h2)
  constructor
  · rw [h3]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_zero, smul_eq_mul, mul_zero, zero_add]
    rw [mul_comm]
    rfl
  · rw [h3]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_zero, smul_eq_mul, mul_zero, add_zero]
    rfl

theorem ae_fst_ne (c : ℝ) : ∀ᵐ p : ℝ × ℝ, p.1 ≠ c := by
  have h : ∀ᵐ x : ℝ, x ≠ c := by
    rw [ae_iff]
    simp
  exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae h

theorem ae_snd_ne (c : ℝ) : ∀ᵐ p : ℝ × ℝ, p.2 ≠ c := by
  have h : ∀ᵐ x : ℝ, x ≠ c := by
    rw [ae_iff]
    simp
  exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae h

theorem ae_fst_of {P : ℝ → Prop} (h : ∀ᵐ x : ℝ, P x) : ∀ᵐ p : ℝ × ℝ, P p.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae h

theorem ae_snd_of {P : ℝ → Prop} (h : ∀ᵐ x : ℝ, P x) : ∀ᵐ p : ℝ × ℝ, P p.2 :=
  (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae h

theorem edge_deriv_zero {φ : ℝ × ℝ → ℂ} {ρ₁ ρ₂ : ℝ} (hρ : ρ₁ ≤ ρ₂) (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0)
    {r : ℝ} (hr : r < ρ₁ ∨ ρ₂ < r) : deriv (edgeValue φ ρ₁ ρ₂) r = 0 := by
  have hev : edgeValue φ ρ₁ ρ₂ =ᶠ[𝓝 r] fun _ => (0 : ℂ) := by
    rcases hr with hr | hr
    · filter_upwards [Iio_mem_nhds hr] with s hs
      exact edgeValue_side hρ hside s (fun h' => absurd h'.1 (not_le.2 hs))
    · filter_upwards [Ioi_mem_nhds hr] with s hs
      exact edgeValue_side hρ hside s (fun h' => absurd h'.2 (not_le.2 hs))
  rw [hev.deriv_eq, deriv_const]

theorem core_fderiv_in {φ : ℝ × ℝ → ℂ} {ρ₁ ρ₂ h : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Ioo ρ₁ ρ₂ ×ˢ Ioo 0 h) (hφd : DifferentiableAt ℝ φ p)
    (hed : DifferentiableAt ℝ (edgeValue φ ρ₁ ρ₂) p.1) (u : ℝ × ℝ) :
    fderiv ℝ (coreTest φ ρ₁ ρ₂ h) p u = fderiv ℝ φ p u -
      fderiv ℝ (fun q : ℝ × ℝ => edgeValue φ ρ₁ ρ₂ q.1 * (((1 - q.2 / h : ℝ)) : ℂ)) p u := by
  have hev : coreTest φ ρ₁ ρ₂ h =ᶠ[𝓝 p] fun q => φ q - edgeValue φ ρ₁ ρ₂ q.1 * (((1 - q.2 / h : ℝ)) : ℂ) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp] with q hq
    obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hq
    simp only [coreTest]
    rw [clampTo_of_mem a1.le a2.le, clampTo_of_mem b1.le b2.le, hw_of_mem b1.le b2.le]
  have hc : DifferentiableAt ℝ (fun z : ℝ => 1 - z / h) p.2 := by fun_prop
  have hprod : DifferentiableAt ℝ (fun q : ℝ × ℝ => edgeValue φ ρ₁ ρ₂ q.1 * (((1 - q.2 / h : ℝ)) : ℂ)) p := by
    have h1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => edgeValue φ ρ₁ ρ₂ q.1) p := hed.comp p differentiableAt_fst
    have h2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => (((1 - q.2 / h : ℝ)) : ℂ)) p :=
      Complex.ofRealCLM.differentiableAt.comp p (hc.comp p differentiableAt_snd)
    exact h1.mul h2
  rw [hev.fderiv_eq, fderiv_fun_sub hφd hprod]
  rfl

theorem core_fderiv_out {φ : ℝ × ℝ → ℂ} {ρ₁ ρ₂ h : ℝ} (hρ : ρ₁ ≤ ρ₂) (hh : 0 < h)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) (htop : ∀ r, φ (r, h) = 0) {p : ℝ × ℝ}
    (hp : p ∉ patch ρ₁ ρ₂ h) : fderiv ℝ (coreTest φ ρ₁ ρ₂ h) p = 0 := by
  have hcl : IsClosed (patch ρ₁ ρ₂ h) := isClosed_Icc.prod isClosed_Icc
  have hev : coreTest φ ρ₁ ρ₂ h =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
    filter_upwards [hcl.isOpen_compl.mem_nhds hp] with q hq
    exact core_zero hρ hh hside htop q hq
  rw [hev.fderiv_eq]
  simp

theorem norm_integral_sq_le {S : Set (ℝ × ℝ)} {j : ℝ × ℝ → ℂ} {X Y : ℝ × ℝ → ℝ}
    (hX : IntegrableOn X S) (hY : IntegrableOn Y S) (hX0 : ∀ᵐ p ∂(volume.restrict S), 0 ≤ X p)
    (hY0 : ∀ᵐ p ∂(volume.restrict S), 0 ≤ Y p) (hj : ∀ᵐ p ∂(volume.restrict S), ‖j p‖ ≤ Real.sqrt (X p) * Real.sqrt (Y p)) :
    ‖∫ p in S, j p‖ ^ 2 ≤ (∫ p in S, X p) * ∫ p in S, Y p := by
  have hsX : MemLp (fun p => Real.sqrt (X p)) (ENNReal.ofReal 2) (volume.restrict S) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq_norm (Real.continuous_sqrt.comp_aestronglyMeasurable hX.1)).2 ?_
    exact hX.congr (hX0.mono fun p hp => by simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp])
  have hsY : MemLp (fun p => Real.sqrt (Y p)) (ENNReal.ofReal 2) (volume.restrict S) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq_norm (Real.continuous_sqrt.comp_aestronglyMeasurable hY.1)).2 ?_
    exact hY.congr (hY0.mono fun p hp => by simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp])
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun p => Real.sqrt_nonneg (X p)) (Eventually.of_forall fun p => Real.sqrt_nonneg (Y p))
    hsX hsY
  have e1 : ∫ p in S, Real.sqrt (X p) ^ (2 : ℝ) = ∫ p in S, X p :=
    integral_congr_ae (hX0.mono fun p hp => by simp only [Real.rpow_two, Real.sq_sqrt hp])
  have e2 : ∫ p in S, Real.sqrt (Y p) ^ (2 : ℝ) = ∫ p in S, Y p :=
    integral_congr_ae (hY0.mono fun p hp => by simp only [Real.rpow_two, Real.sq_sqrt hp])
  rw [e1, e2] at hH
  have hIX : 0 ≤ ∫ p in S, X p := integral_nonneg_of_ae hX0
  have hIY : 0 ≤ ∫ p in S, Y p := integral_nonneg_of_ae hY0
  have hprod : Integrable (fun p => Real.sqrt (X p) * Real.sqrt (Y p)) (volume.restrict S) := by
    refine ((hX.add hY).div_const 2).mono' ((Real.continuous_sqrt.comp_aestronglyMeasurable hX.1).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hY.1)) ((hX0.and hY0).mono fun p hp => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), Pi.add_apply]
    nlinarith [Real.sq_sqrt hp.1, Real.sq_sqrt hp.2, sq_nonneg (Real.sqrt (X p) - Real.sqrt (Y p))]
  have h1 : ‖∫ p in S, j p‖ ≤ ∫ p in S, Real.sqrt (X p) * Real.sqrt (Y p) :=
    (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg (Eventually.of_forall fun p => norm_nonneg _)
      hprod hj)
  have h2 := h1.trans hH
  have h3 : (0 : ℝ) ≤ ‖∫ p in S, j p‖ := norm_nonneg _
  calc ‖∫ p in S, j p‖ ^ 2 ≤ ((∫ p in S, X p) ^ (1 / (2 : ℝ)) * (∫ p in S, Y p) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ h3 h2 2
    _ = (∫ p in S, X p) * ∫ p in S, Y p := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hIX, Real.sq_sqrt hIY]

theorem sum_three_mul_le (a0 a1 a2 u0 u1 u2 : ℂ) : ‖a0 * u0 + a1 * u1 + a2 * u2‖ ≤
    Real.sqrt (‖a0‖ ^ 2 + ‖a1‖ ^ 2 + ‖a2‖ ^ 2) * Real.sqrt (‖u0‖ ^ 2 + ‖u1‖ ^ 2 + ‖u2‖ ^ 2) := by
  have h1 : ‖a0 * u0 + a1 * u1 + a2 * u2‖ ≤ ‖a0‖ * ‖u0‖ + ‖a1‖ * ‖u1‖ + ‖a2‖ * ‖u2‖ := by
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (le_of_eq (by rw [norm_mul, norm_mul]))) (le_of_eq (norm_mul _ _))
  refine h1.trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (‖a0‖ * ‖u1‖ - ‖a1‖ * ‖u0‖), sq_nonneg (‖a0‖ * ‖u2‖ - ‖a2‖ * ‖u0‖),
    sq_nonneg (‖a1‖ * ‖u2‖ - ‖a2‖ * ‖u1‖), norm_nonneg a0, norm_nonneg a1, norm_nonneg a2,
    norm_nonneg u0, norm_nonneg u1, norm_nonneg u2]

theorem deriv_height_line (h z : ℝ) : deriv (fun z : ℝ => 1 - z / h) z = -(1 / h) := by
  have : HasDerivAt (fun z : ℝ => 1 - z / h) (-(1 / h)) z := by
    simpa using ((hasDerivAt_id z).div_const h).const_sub 1
  exact this.deriv

theorem integral_eq_set_of_ae {F G : ℝ × ℝ → ℂ} {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (h : ∀ᵐ p, F p = S.indicator G p) : ∫ p, F p = ∫ p in S, G p := by
  rw [← integral_indicator hS]
  exact integral_congr_ae h

theorem core_identity {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (η : ℤ × ℤ) {ρ₁ ρ₂ h : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂) (hh : 0 < h) {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) (htop : ∀ r, φ (r, h) = 0) :
    (∫ p in patch ρ₁ ρ₂ h, (fderiv ℝ φ p (1, 0) - deriv (edgeValue φ ρ₁ ρ₂) p.1 * ((1 - p.2 / h : ℝ) : ℂ)) *
        ((p.1 : ℂ) * planeVel η v 0 p.1 p.2)) +
      (∫ p in patch ρ₁ ρ₂ h, (fderiv ℝ φ p (0, 1) - edgeValue φ ρ₁ ρ₂ p.1 * ((-(1 / h) : ℝ) : ℂ)) *
        ((p.1 : ℂ) * planeVel η v 2 p.1 p.2)) +
      ∫ p in patch ρ₁ ρ₂ h, (φ p - edgeValue φ ρ₁ ρ₂ p.1 * ((1 - p.2 / h : ℝ) : ℂ)) *
        (-((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2) = 0 := by
  obtain ⟨K', hK'⟩ := core_slope hφ hρ.le hh hside
  have hS : MeasurableSet (patch ρ₁ ρ₂ h) := measurableSet_Icc.prod measurableSet_Icc
  have hcl : IsClosed (patch ρ₁ ρ₂ h) := isClosed_Icc.prod isClosed_Icc
  have hsupp : tsupport (coreTest φ ρ₁ ρ₂ h) ⊆ patch ρ₁ ρ₂ h :=
    closure_minimal (fun p hp => by_contra fun h' => hp (core_zero hρ.le hh hside htop p h')) hcl
  have hD := divergence_rough hv η hK'
    (HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) fun p hp => core_zero hρ.le hh hside htop p hp)
    (fun p hp => lt_of_lt_of_le hρ₁ (hsupp hp).1.1)
  have hE := edgeValue_slope hφ ρ₁ ρ₂
  have good : ∀ᵐ p : ℝ × ℝ, p.1 ≠ ρ₁ ∧ p.1 ≠ ρ₂ ∧ p.2 ≠ 0 ∧ p.2 ≠ h ∧ DifferentiableAt ℝ φ p ∧
      DifferentiableAt ℝ (edgeValue φ ρ₁ ρ₂) p.1 := by
    filter_upwards [ae_fst_ne ρ₁, ae_fst_ne ρ₂, ae_snd_ne 0, ae_snd_ne h, hφ.ae_differentiableAt,
      ae_fst_of hE.ae_differentiableAt] with p h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hint : ∀ p : ℝ × ℝ, p.1 ≠ ρ₁ → p.1 ≠ ρ₂ → p.2 ≠ 0 → p.2 ≠ h → p ∈ patch ρ₁ ρ₂ h →
      p ∈ Ioo ρ₁ ρ₂ ×ˢ Ioo 0 h := fun p h1 h2 h3 h4 hp =>
    ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm h1), lt_of_le_of_ne hp.1.2 h2⟩,
      lt_of_le_of_ne hp.2.1 (Ne.symm h3), lt_of_le_of_ne hp.2.2 h4⟩
  have hline : ∀ z : ℝ, DifferentiableAt ℝ (fun z : ℝ => 1 - z / h) z := fun z => by fun_prop
  have I1 : ∫ p, fderiv ℝ (coreTest φ ρ₁ ρ₂ h) p (1, 0) * ((p.1 : ℂ) * planeVel η v 0 p.1 p.2) =
      ∫ p in patch ρ₁ ρ₂ h, (fderiv ℝ φ p (1, 0) - deriv (edgeValue φ ρ₁ ρ₂) p.1 * ((1 - p.2 / h : ℝ) : ℂ)) *
        ((p.1 : ℂ) * planeVel η v 0 p.1 p.2) := by
    refine integral_eq_set_of_ae hS (good.mono fun p ⟨h1, h2, h3, h4, h5, h6⟩ => ?_)
    by_cases hp : p ∈ patch ρ₁ ρ₂ h
    · rw [indicator_of_mem hp, core_fderiv_in (hint p h1 h2 h3 h4 hp) h5 h6,
        (fderiv_split (c := fun z : ℝ => 1 - z / h) h6 (hline p.2)).1]
    · rw [indicator_of_notMem hp, core_fderiv_out hρ.le hh hside htop hp]
      simp
  have I2 : ∫ p, fderiv ℝ (coreTest φ ρ₁ ρ₂ h) p (0, 1) * ((p.1 : ℂ) * planeVel η v 2 p.1 p.2) =
      ∫ p in patch ρ₁ ρ₂ h, (fderiv ℝ φ p (0, 1) - edgeValue φ ρ₁ ρ₂ p.1 * ((-(1 / h) : ℝ) : ℂ)) *
        ((p.1 : ℂ) * planeVel η v 2 p.1 p.2) := by
    refine integral_eq_set_of_ae hS (good.mono fun p ⟨h1, h2, h3, h4, h5, h6⟩ => ?_)
    by_cases hp : p ∈ patch ρ₁ ρ₂ h
    · rw [indicator_of_mem hp, core_fderiv_in (hint p h1 h2 h3 h4 hp) h5 h6,
        (fderiv_split (c := fun z : ℝ => 1 - z / h) h6 (hline p.2)).2, deriv_height_line]
    · rw [indicator_of_notMem hp, core_fderiv_out hρ.le hh hside htop hp]
      simp
  have I3 : ∫ p, coreTest φ ρ₁ ρ₂ h p * (-((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2) =
      ∫ p in patch ρ₁ ρ₂ h, (φ p - edgeValue φ ρ₁ ρ₂ p.1 * ((1 - p.2 / h : ℝ) : ℂ)) *
        (-((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2) := by
    refine integral_eq_set_of_ae hS (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ patch ρ₁ ρ₂ h
    · rw [indicator_of_mem hp]
      obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hp
      simp only [coreTest]
      rw [clampTo_of_mem a1 a2, clampTo_of_mem b1 b2, hw_of_mem b1 b2]
    · rw [indicator_of_notMem hp, core_zero hρ.le hh hside htop p hp, zero_mul]
  rw [← I1, ← I2, ← I3]
  exact hD

theorem ramp_identity {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (η : ℤ × ℤ) {ρ₁ ρ₂ h : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂) (hh : 0 < h) {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) :
    (∫ p in patch ρ₁ ρ₂ h, deriv (edgeValue φ ρ₁ ρ₂) p.1 * ((1 - p.2 / h : ℝ) : ℂ) *
        ((p.1 : ℂ) * planeVel η v 0 p.1 p.2)) +
      ∫ p in patch ρ₁ ρ₂ h, edgeValue φ ρ₁ ρ₂ p.1 * ((1 - p.2 / h : ℝ) : ℂ) *
        (-((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2 - (p.1 : ℂ) * planeVelHeight η G 2 p.1 p.2) = 0 := by
  set E := edgeValue φ ρ₁ ρ₂ with hEdef
  set A : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * planeVel η v 0 p.1 p.2 with hAdef
  set Cf : ℝ × ℝ → ℂ := fun p => -((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2 -
    (p.1 : ℂ) * planeVelHeight η G 2 p.1 p.2 with hCdef
  set B : Set (ℝ × ℝ) := Icc ρ₁ ρ₂ ×ˢ Icc (-1) h with hBdef
  set S : Set (ℝ × ℝ) := patch ρ₁ ρ₂ h with hSdef
  have hBm : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hSm : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hSB : S ⊆ B := fun p hp => ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩
  set R1 := ρ₂ + h + 1 with hR1
  have hBbox : B ⊆ Icc ρ₁ R1 ×ˢ Icc (-R1) R1 := fun p hp =>
    ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have iA : IntegrableOn A B :=
    (integrableOn_radial (integrableOn_of_memLp (planeVel_memLp hv η 0 (R := R1) hρ₁))).mono_set hBbox
  have iC : IntegrableOn Cf B :=
    IntegrableOn.mono_set (((integrableOn_of_memLp (planeVel_memLp hv η 1 (R := R1) hρ₁)).const_mul
      (-((η.2 : ℂ) * Complex.I))).sub
      (integrableOn_radial (integrableOn_of_memLp (planeHeight_memLp hv η (R := R1) hρ₁)))) hBbox
  have hE := edgeValue_slope hφ ρ₁ ρ₂
  have hE'b : ∀ r, ‖deriv E r‖ ≤ K := fun r => norm_deriv_le_of_lipschitz hE
  have hEb : ∀ r, ‖E r‖ ≤ K * (ρ₂ - ρ₁) := edgeValue_bound hφ hρ.le hside
  have hE'm : Measurable (deriv E) := measurable_deriv E
  have hEc : Continuous E := hE.continuous
  have hEz : ∀ r, r ∉ Icc ρ₁ ρ₂ → E r = 0 := edgeValue_side hρ.le hside
  have hE'z : ∀ r, r ∉ Icc ρ₁ ρ₂ → deriv E r = 0 := fun r hr => by
    rw [mem_Icc, not_and_or, not_le, not_le] at hr
    exact edge_deriv_zero hρ.le hside hr
  set gn : ℕ → ℝ × ℝ → ℂ := fun n p => deriv E p.1 * (rampWeight h n p.2 : ℂ) * A p +
    E p.1 * (rampWeight h n p.2 : ℂ) * Cf p with hgn
  set ginf : ℝ × ℝ → ℂ := S.indicator (fun p => deriv E p.1 * ((1 - p.2 / h : ℝ) : ℂ) * A p +
    E p.1 * ((1 - p.2 / h : ℝ) : ℂ) * Cf p) with hginf
  have hrb : ∀ n z, ‖((rampWeight h n z : ℝ) : ℂ)‖ ≤ 1 := fun n z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (ramp_mem hh n z).1]; exact (ramp_mem hh n z).2
  have hrc : ∀ n, Continuous (rampWeight h n) := fun n => (ramp_slope hh n).choose_spec.continuous
  have igB1 : ∀ n, IntegrableOn (fun p => deriv E p.1 * (rampWeight h n p.2 : ℂ) * A p) B := by
    intro n
    · refine iA.bdd_mul (c := K * 1) ?_ (Eventually.of_forall fun p => ?_)
      · exact ((hE'm.comp measurable_fst).aestronglyMeasurable.mul
          (Complex.continuous_ofReal.comp ((hrc n).comp continuous_snd)).aestronglyMeasurable)
      · rw [norm_mul]; exact mul_le_mul (hE'b _) (hrb n _) (norm_nonneg _) K.2
  have igB2 : ∀ n, IntegrableOn (fun p => E p.1 * (rampWeight h n p.2 : ℂ) * Cf p) B := by
    intro n
    · refine iC.bdd_mul (c := K * (ρ₂ - ρ₁) * 1) ?_ (Eventually.of_forall fun p => ?_)
      · exact ((hEc.comp continuous_fst).mul (Complex.continuous_ofReal.comp
          ((hrc n).comp continuous_snd))).aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_mul (hEb _) (hrb n _) (norm_nonneg _) (by nlinarith [K.2, hρ])
  have igB : ∀ n, IntegrableOn (gn n) B := fun n => (igB1 n).add (igB2 n)
  have hGn : ∀ n, ∫ p in B, gn n p = 0 := by
    intro n
    obtain ⟨Kn, hKn⟩ := rampTest_slope hφ hρ.le hh hside n
    have hcl : IsClosed B := isClosed_Icc.prod isClosed_Icc
    have hsupp : tsupport (rampTest φ ρ₁ ρ₂ h n) ⊆ B :=
      closure_minimal (fun p hp => by_contra fun h' => hp (rampTest_zero hρ.le hh hside n p h')) hcl
    have hR := radial_rough hv η hKn
      (HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) fun p hp => rampTest_zero hρ.le hh hside n p hp)
      (fun p hp => lt_of_lt_of_le hρ₁ (hsupp hp).1.1)
    have hR2 : (∫ p, fderiv ℝ (rampTest φ ρ₁ ρ₂ h n) p (1, 0) * A p) +
        (∫ p, fderiv ℝ (rampTest φ ρ₁ ρ₂ h n) p (0, 1) * (0 : ℂ)) + ∫ p, rampTest φ ρ₁ ρ₂ h n p * Cf p = 0 := hR
    simp only [mul_zero, integral_zero, add_zero] at hR2
    have hdiff : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ E p.1 ∧ DifferentiableAt ℝ (rampWeight h n) p.2 := by
      filter_upwards [ae_fst_of hE.ae_differentiableAt,
        ae_snd_of (ramp_slope hh n).choose_spec.ae_differentiableAt] with p h1 h2
      exact ⟨h1, h2⟩
    have zoff : ∀ p, p ∉ B → ∀ (X : ℝ × ℝ → ℂ), deriv E p.1 * (rampWeight h n p.2 : ℂ) * X p = 0 ∧
        E p.1 * (rampWeight h n p.2 : ℂ) * X p = 0 := by
      intro p hp X
      simp only [hBdef, mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · rw [hE'z _ hp, hEz _ hp]; simp
      · rw [mem_Icc, not_and_or, not_le, not_le] at hp
        rcases hp with hp | hp
        · rw [ramp_of_neg n (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hh]; simp
        · rw [ramp_of_ge hh n hp.le]; simp
    have J1 : ∫ p, fderiv ℝ (rampTest φ ρ₁ ρ₂ h n) p (1, 0) * A p =
        ∫ p in B, deriv E p.1 * (rampWeight h n p.2 : ℂ) * A p := by
      refine integral_eq_set_of_ae hBm (hdiff.mono fun p ⟨h1, h2⟩ => ?_)
      have hd : fderiv ℝ (rampTest φ ρ₁ ρ₂ h n) p (1, 0) = deriv E p.1 * (rampWeight h n p.2 : ℂ) :=
        (fderiv_split (F := E) (c := rampWeight h n) h1 h2).1
      rw [hd]
      by_cases hp : p ∈ B
      · rw [indicator_of_mem hp]
      · rw [indicator_of_notMem hp]
        exact (zoff p hp A).1
    have J3 : ∫ p, rampTest φ ρ₁ ρ₂ h n p * Cf p = ∫ p in B, E p.1 * (rampWeight h n p.2 : ℂ) * Cf p := by
      refine integral_eq_set_of_ae hBm (Eventually.of_forall fun p => ?_)
      by_cases hp : p ∈ B
      · rw [indicator_of_mem hp]; rfl
      · rw [indicator_of_notMem hp]
        exact (zoff p hp Cf).2
    rw [J1, J3] at hR2
    rw [← hR2, ← integral_add (igB1 n) (igB2 n)]
  have hlim : Tendsto (fun n => ∫ p in B, gn n p) atTop (𝓝 (∫ p in B, ginf p)) := by
    refine tendsto_integral_of_dominated_convergence (fun p => K * ‖A p‖ + K * (ρ₂ - ρ₁) * ‖Cf p‖)
      (fun n => (igB n).1) ((iA.norm.const_mul _).add (iC.norm.const_mul _)) (fun n => Eventually.of_forall fun p => ?_) ?_
    · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_mul]
        calc ‖deriv E p.1‖ * ‖((rampWeight h n p.2 : ℝ) : ℂ)‖ * ‖A p‖ ≤ K * 1 * ‖A p‖ := by
              gcongr
              · exact hE'b _
              · exact hrb n _
          _ = K * ‖A p‖ := by ring
      · rw [norm_mul, norm_mul]
        calc ‖E p.1‖ * ‖((rampWeight h n p.2 : ℝ) : ℂ)‖ * ‖Cf p‖ ≤ K * (ρ₂ - ρ₁) * 1 * ‖Cf p‖ := by
              gcongr
              · exact hEb _
              · exact hrb n _
          _ = K * (ρ₂ - ρ₁) * ‖Cf p‖ := by ring
    · refine ae_restrict_of_ae ((ae_snd_ne 0).mono fun p hp0 => ?_)
      by_cases hz : 0 < p.2
      · have hr : ∀ n, rampWeight h n p.2 = heightWeight h p.2 := fun n => ramp_of_nonneg hh n hz.le
        by_cases hpS : p ∈ S
        · have hw := hw_of_mem (h := h) hpS.2.1 hpS.2.2
          have e : ∀ n, gn n p = ginf p := by
            intro n
            simp only [hgn, hginf, indicator_of_mem hpS, hr, hw]
          simp only [e]
          exact tendsto_const_nhds
        · have e : ∀ n, gn n p = 0 := by
            intro n
            simp only [hSdef, patch, mem_prod, not_and_or] at hpS
            rcases hpS with hp1 | hp2
            · simp only [hgn, hE'z _ hp1, hEz _ hp1]; simp
            · have hgt : h < p.2 := by
                rw [mem_Icc, not_and_or, not_le, not_le] at hp2
                rcases hp2 with hp2 | hp2
                · exact absurd hz (not_lt.2 hp2.le)
                · exact hp2
              simp only [hgn, hr, hw_of_ge hh hgt.le]; simp
          simp only [e, hginf, indicator_of_notMem hpS]
          exact tendsto_const_nhds
      · have hneg : p.2 < 0 := lt_of_le_of_ne (not_lt.1 hz) hp0
        have hpS : p ∉ S := fun h' => absurd h'.2.1 (not_le.2 hneg)
        rw [hginf, indicator_of_notMem hpS]
        refine tendsto_const_nhds.congr' ?_
        rw [EventuallyEq, eventually_atTop]
        refine ⟨⌈-1 / p.2⌉₊, fun n hn => ?_⟩
        have hn' : -1 / p.2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
        have h1 : 1 + ((n : ℝ) + 1) * p.2 ≤ 0 := by
          have := (div_le_iff_of_neg' hneg).1 hn'
          nlinarith
        simp only [hgn, ramp_of_neg n h1 hh]
        simp
  have hzero : ∫ p in B, ginf p = 0 := tendsto_nhds_unique hlim (by simp only [hGn]; exact tendsto_const_nhds)
  rw [hginf, setIntegral_indicator hSm, inter_eq_right.2 hSB] at hzero
  have iS1 : IntegrableOn (fun p => deriv E p.1 * ((1 - p.2 / h : ℝ) : ℂ) * A p) S := by
    refine (iA.mono_set hSB).bdd_mul (c := K * 1) ?_ ?_
    · exact ((hE'm.comp measurable_fst).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun p : ℝ × ℝ => 1 - p.2 / h)).aestronglyMeasurable)
    · refine (ae_restrict_iff' hSm).2 (Eventually.of_forall fun p hp => ?_)
      rw [norm_mul, Complex.norm_real, ← hw_of_mem hp.2.1 hp.2.2, Real.norm_of_nonneg (hw_mem hh _).1]
      exact mul_le_mul (hE'b _) (hw_mem hh _).2 (hw_mem hh _).1 K.2
  have iS2 : IntegrableOn (fun p => E p.1 * ((1 - p.2 / h : ℝ) : ℂ) * Cf p) S := by
    refine (iC.mono_set hSB).bdd_mul (c := K * (ρ₂ - ρ₁) * 1) ?_ ?_
    · exact ((hEc.comp continuous_fst).mul
        (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun p : ℝ × ℝ => 1 - p.2 / h))).aestronglyMeasurable
    · refine (ae_restrict_iff' hSm).2 (Eventually.of_forall fun p hp => ?_)
      rw [norm_mul, Complex.norm_real, ← hw_of_mem hp.2.1 hp.2.2, Real.norm_of_nonneg (hw_mem hh _).1]
      exact mul_le_mul (hEb _) (hw_mem hh _).2 (hw_mem hh _).1 (by nlinarith [K.2, hρ])
  rw [← integral_add iS1 iS2]
  exact hzero

theorem trace_identity (hP : PlaneDataFlipHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hflip : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (ξ : ℤ × ℤ) {ρ₁ ρ₂ h : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂) (hh : 0 < h) {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) :
    patchTrace ξ v G ρ₁ ρ₂ h φ = ∫ p in patch ρ₁ ρ₂ h,
      (planeVelHeight (flipLabel ξ) G 2 p.1 p.2 * ((1 - p.2 / h : ℝ) : ℂ) - planeVel (flipLabel ξ) v 2 p.1 p.2 / (h : ℂ)) *
        edgeValue φ ρ₁ ρ₂ p.1 * (p.1 : ℂ) := by
  set η := flipLabel ξ with hη
  set k : ℝ × ℝ → ℂ := fun p => planeVelHeight η G 2 p.1 p.2 * ((1 - p.2 / h : ℝ) : ℂ) -
    planeVel η v 2 p.1 p.2 / (h : ℂ) with hk
  have hT := hP Γ P v G H g hv hflip ξ 2
  rw [ae_restrict_iff' measurableSet_Ioi] at hT
  have hfs : (frameSign 2 : ℂ) = -1 := by simp [frameSign]
  have step1 : patchTrace ξ v G ρ₁ ρ₂ h φ = ∫ r in ρ₁..ρ₂,
      (∫ z in (0 : ℝ)..h, k (r, z)) * edgeValue φ ρ₁ ρ₂ r * (r : ℂ) := by
    unfold patchTrace
    refine intervalIntegral.integral_congr_ae (hT.mono fun r hr hmem => ?_)
    rw [uIoc_of_le hρ.le] at hmem
    have hr0 : 0 < r := lt_trans hρ₁ hmem.1
    have e1 := (hr hr0 h hh).1
    rw [hfs] at e1
    have e2 : upperTrace (planeVel ξ v 2 r) (planeVelHeight ξ G 2 r) h = ∫ z in (0 : ℝ)..h, k (r, z) := by
      have : upperTrace (planeVel ξ v 2 r) (planeVelHeight ξ G 2 r) h =
          -upperTrace (planeVel η v 2 r) (planeVelHeight η G 2 r) h := by
        rw [e1]; ring
      rw [this, upperTrace, neg_neg]
    rw [e2, edgeValue, clampTo_of_mem hmem.1.le hmem.2]
  have hS : MeasurableSet (patch ρ₁ ρ₂ h) := measurableSet_Icc.prod measurableSet_Icc
  set R1 := ρ₂ + h + 1 with hR1
  have hSbox : patch ρ₁ ρ₂ h ⊆ Icc ρ₁ R1 ×ˢ Icc (-R1) R1 := fun p hp =>
    ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have iH : IntegrableOn (fun p : ℝ × ℝ => planeVelHeight η G 2 p.1 p.2) (patch ρ₁ ρ₂ h) :=
    (integrableOn_of_memLp (planeHeight_memLp hv η (R := R1) hρ₁)).mono_set hSbox
  have iU : IntegrableOn (fun p : ℝ × ℝ => planeVel η v 2 p.1 p.2) (patch ρ₁ ρ₂ h) :=
    (integrableOn_of_memLp (planeVel_memLp hv η 2 (R := R1) hρ₁)).mono_set hSbox
  have hEb := edgeValue_bound hφ hρ.le hside
  have hEc : Continuous (edgeValue φ ρ₁ ρ₂) := (edgeValue_slope hφ ρ₁ ρ₂).continuous
  have ik : IntegrableOn k (patch ρ₁ ρ₂ h) := by
    refine Integrable.sub ?_ (iU.div_const _)
    refine iH.mul_bdd (c := 1) (Complex.continuous_ofReal.comp (by fun_prop :
      Continuous fun p : ℝ × ℝ => 1 - p.2 / h)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_)
    rw [Complex.norm_real, ← hw_of_mem hp.2.1 hp.2.2, Real.norm_of_nonneg (hw_mem hh _).1]
    exact (hw_mem hh _).2
  have ikE : IntegrableOn (fun p : ℝ × ℝ => k p * edgeValue φ ρ₁ ρ₂ p.1 * (p.1 : ℂ)) (patch ρ₁ ρ₂ h) := by
    have h1 : IntegrableOn (fun p : ℝ × ℝ => k p * edgeValue φ ρ₁ ρ₂ p.1) (patch ρ₁ ρ₂ h) :=
      ik.mul_bdd (c := K * (ρ₂ - ρ₁)) (hEc.comp continuous_fst).aestronglyMeasurable
        (Eventually.of_forall fun p => hEb p.1)
    refine h1.mul_bdd (c := ρ₂) (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_)
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hp.1.1])]
    exact hp.1.2
  rw [step1, intervalIntegral.integral_of_le hρ.le, ← integral_Icc_eq_integral_Ioc]
  have e3 : ∀ r : ℝ, (∫ z in (0 : ℝ)..h, k (r, z)) * edgeValue φ ρ₁ ρ₂ r * (r : ℂ) =
      ∫ z in Icc (0 : ℝ) h, k (r, z) * edgeValue φ ρ₁ ρ₂ r * (r : ℂ) := by
    intro r
    rw [intervalIntegral.integral_of_le hh.le, ← integral_Icc_eq_integral_Ioc, integral_mul_const,
      integral_mul_const]
  simp_rw [e3]
  rw [patch, Measure.volume_eq_prod, setIntegral_prod _ ikE]

theorem bdd_on {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {f X : ℝ × ℝ → ℂ} {M : ℝ} (hX : IntegrableOn X S)
    (hf : AEStronglyMeasurable f (volume.restrict S)) (hb : ∀ p ∈ S, ‖f p‖ ≤ M) :
    IntegrableOn (fun p => f p * X p) S :=
  hX.bdd_mul hf ((ae_restrict_iff' hS).2 (Eventually.of_forall hb))

theorem phi_bound {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ) {ρ₁ ρ₂ h : ℝ}
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) {p : ℝ × ℝ} (hp : p ∈ patch ρ₁ ρ₂ h) :
    ‖φ p‖ ≤ K * (ρ₂ - ρ₁) := by
  have h1 := hφ.dist_le_mul p (ρ₁, p.2)
  rw [dist_eq_norm, (hside p.2).1, sub_zero, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
    max_eq_left (abs_nonneg _), abs_of_nonneg (by linarith [hp.1.1])] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (by linarith [hp.1.2]) K.2)

theorem fderiv_bound {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ) (p u : ℝ × ℝ) (hu : ‖u‖ ≤ 1) :
    ‖fderiv ℝ φ p u‖ ≤ K :=
  ((fderiv ℝ φ p).le_opNorm u).trans (by
    calc ‖fderiv ℝ φ p‖ * ‖u‖ ≤ K * 1 := mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hφ) hu (norm_nonneg _) K.2
      _ = K := mul_one _)

theorem norm_unit_r : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]

theorem norm_unit_z : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]

theorem main_identity (hP : PlaneDataFlipHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g)
    (hflip : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (ξ : ℤ × ℤ) {ρ₁ ρ₂ h : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂) (hh : 0 < h) {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) (htop : ∀ r, φ (r, h) = 0) :
    patchTrace ξ v G ρ₁ ρ₂ h φ = ∫ p in patch ρ₁ ρ₂ h,
      (fderiv ℝ φ p (1, 0) * ((p.1 : ℂ) * planeVel (flipLabel ξ) v 0 p.1 p.2) +
        fderiv ℝ φ p (0, 1) * ((p.1 : ℂ) * planeVel (flipLabel ξ) v 2 p.1 p.2) +
        φ p * (-(((flipLabel ξ).2 : ℂ) * Complex.I) * planeVel (flipLabel ξ) v 1 p.1 p.2)) := by
  have hE1 := core_identity hv (flipLabel ξ) hρ₁ hρ hh hφ hside htop
  have hE2 := ramp_identity hv (flipLabel ξ) hρ₁ hρ hh hφ hside
  have hE3 := trace_identity hP hv hflip ξ hρ₁ hρ hh hφ hside
  set η := flipLabel ξ with hη
  set S := patch ρ₁ ρ₂ h with hSdef
  set E := edgeValue φ ρ₁ ρ₂ with hEdef
  set c : ℂ := -((η.2 : ℂ) * Complex.I) with hc
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  set R1 := ρ₂ + h + 1 with hR1
  have hSbox : S ⊆ Icc ρ₁ R1 ×ˢ Icc (-R1) R1 := fun p hp =>
    ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have iU : ∀ a, IntegrableOn (fun p : ℝ × ℝ => planeVel η v a p.1 p.2) S := fun a =>
    (integrableOn_of_memLp (planeVel_memLp hv η a (R := R1) hρ₁)).mono_set hSbox
  have irU : ∀ a, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * planeVel η v a p.1 p.2) S := fun a =>
    (integrableOn_radial (integrableOn_of_memLp (planeVel_memLp hv η a (R := R1) hρ₁))).mono_set hSbox
  have iH : IntegrableOn (fun p : ℝ × ℝ => planeVelHeight η G 2 p.1 p.2) S :=
    (integrableOn_of_memLp (planeHeight_memLp hv η (R := R1) hρ₁)).mono_set hSbox
  have irH : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * planeVelHeight η G 2 p.1 p.2) S :=
    (integrableOn_radial (integrableOn_of_memLp (planeHeight_memLp hv η (R := R1) hρ₁))).mono_set hSbox
  have hEl := edgeValue_slope hφ ρ₁ ρ₂
  have hEb := edgeValue_bound hφ hρ.le hside
  have hE'b : ∀ r, ‖deriv E r‖ ≤ K := fun r => norm_deriv_le_of_lipschitz hEl
  have hE'm : AEStronglyMeasurable (fun p : ℝ × ℝ => deriv E p.1) (volume.restrict S) :=
    ((measurable_deriv E).comp measurable_fst).aestronglyMeasurable
  have hEm : AEStronglyMeasurable (fun p : ℝ × ℝ => E p.1) (volume.restrict S) :=
    (hEl.continuous.comp continuous_fst).aestronglyMeasurable
  have hlm : AEStronglyMeasurable (fun p : ℝ × ℝ => (((1 - p.2 / h : ℝ)) : ℂ)) (volume.restrict S) :=
    (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun p : ℝ × ℝ => 1 - p.2 / h)).aestronglyMeasurable
  have hlb : ∀ p ∈ S, ‖(((1 - p.2 / h : ℝ)) : ℂ)‖ ≤ 1 := fun p hp => by
    rw [Complex.norm_real, ← hw_of_mem hp.2.1 hp.2.2, Real.norm_of_nonneg (hw_mem hh _).1]
    exact (hw_mem hh _).2
  have hdm : ∀ u : ℝ × ℝ, AEStronglyMeasurable (fun p => fderiv ℝ φ p u) (volume.restrict S) := fun u =>
    (measurable_fderiv_apply_const ℝ φ u).aestronglyMeasurable
  have hφm : AEStronglyMeasurable φ (volume.restrict S) := hφ.continuous.aestronglyMeasurable
  have hrm : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 : ℂ)) (volume.restrict S) :=
    (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable
  have hrb : ∀ p ∈ S, ‖(p.1 : ℂ)‖ ≤ ρ₂ := fun p hp => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hp.1.1])]; exact hp.1.2
  have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have i1 : IntegrableOn (fun p => (fderiv ℝ φ p (1, 0) - deriv E p.1 * (((1 - p.2 / h : ℝ)) : ℂ)) *
      ((p.1 : ℂ) * planeVel η v 0 p.1 p.2)) S :=
    bdd_on hS (irU 0) ((hdm _).sub (hE'm.mul hlm)) (M := K + K * 1) fun p hp =>
      (norm_sub_le _ _).trans (add_le_add (fderiv_bound hφ p _ norm_unit_r)
        (by rw [norm_mul]; exact mul_le_mul (hE'b _) (hlb p hp) (norm_nonneg _) K.2))
  have i2 : IntegrableOn (fun p => (fderiv ℝ φ p (0, 1) - E p.1 * ((-(1 / h) : ℝ) : ℂ)) *
      ((p.1 : ℂ) * planeVel η v 2 p.1 p.2)) S :=
    bdd_on hS (irU 2) ((hdm _).sub (hEm.mul aestronglyMeasurable_const))
      (M := K + K * (ρ₂ - ρ₁) * ‖((-(1 / h) : ℝ) : ℂ)‖) fun p hp =>
      (norm_sub_le _ _).trans (add_le_add (fderiv_bound hφ p _ norm_unit_z)
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hEb _) (norm_nonneg _)))
  have i3 : IntegrableOn (fun p => (φ p - E p.1 * (((1 - p.2 / h : ℝ)) : ℂ)) *
      (c * planeVel η v 1 p.1 p.2)) S :=
    bdd_on hS ((iU 1).const_mul c) (hφm.sub (hEm.mul hlm)) (M := K * (ρ₂ - ρ₁) + K * (ρ₂ - ρ₁) * 1)
      fun p hp => (norm_sub_le _ _).trans (add_le_add (phi_bound hφ hside hp)
        (by rw [norm_mul]; exact mul_le_mul (hEb _) (hlb p hp) (norm_nonneg _) (by nlinarith [K.2, hρ])))
  have j1 : IntegrableOn (fun p => deriv E p.1 * (((1 - p.2 / h : ℝ)) : ℂ) *
      ((p.1 : ℂ) * planeVel η v 0 p.1 p.2)) S :=
    bdd_on hS (irU 0) (hE'm.mul hlm) (M := K * 1) fun p hp => by
      rw [norm_mul]; exact mul_le_mul (hE'b _) (hlb p hp) (norm_nonneg _) K.2
  have j2 : IntegrableOn (fun p => E p.1 * (((1 - p.2 / h : ℝ)) : ℂ) *
      (c * planeVel η v 1 p.1 p.2 - (p.1 : ℂ) * planeVelHeight η G 2 p.1 p.2)) S :=
    bdd_on hS (((iU 1).const_mul c).sub irH) (hEm.mul hlm) (M := K * (ρ₂ - ρ₁) * 1) fun p hp => by
      rw [norm_mul]; exact mul_le_mul (hEb _) (hlb p hp) (norm_nonneg _) (by nlinarith [K.2, hρ])
  have it0 : IntegrableOn (fun p => planeVelHeight η G 2 p.1 p.2 * (((1 - p.2 / h : ℝ)) : ℂ) -
      planeVel η v 2 p.1 p.2 / (h : ℂ)) S := by
    refine Integrable.sub ?_ ((iU 2).div_const _)
    have := bdd_on hS iH hlm (M := 1) hlb
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only
    ring
  have it : IntegrableOn (fun p => (planeVelHeight η G 2 p.1 p.2 * (((1 - p.2 / h : ℝ)) : ℂ) -
      planeVel η v 2 p.1 p.2 / (h : ℂ)) * E p.1 * (p.1 : ℂ)) S := by
    have := bdd_on hS it0 (hEm.mul hrm) (M := K * (ρ₂ - ρ₁) * ρ₂) fun p hp => by
      rw [Pi.mul_apply, norm_mul]; exact mul_le_mul (hEb _) (hrb p hp) (norm_nonneg _) (by nlinarith [K.2, hρ])
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  rw [hE3]
  have hsum : ∫ p in S, (fderiv ℝ φ p (1, 0) * ((p.1 : ℂ) * planeVel η v 0 p.1 p.2) +
        fderiv ℝ φ p (0, 1) * ((p.1 : ℂ) * planeVel η v 2 p.1 p.2) +
        φ p * (c * planeVel η v 1 p.1 p.2)) =
      ∫ p in S, ((fderiv ℝ φ p (1, 0) - deriv E p.1 * (((1 - p.2 / h : ℝ)) : ℂ)) *
          ((p.1 : ℂ) * planeVel η v 0 p.1 p.2) +
        (fderiv ℝ φ p (0, 1) - E p.1 * ((-(1 / h) : ℝ) : ℂ)) * ((p.1 : ℂ) * planeVel η v 2 p.1 p.2) +
        (φ p - E p.1 * (((1 - p.2 / h : ℝ)) : ℂ)) * (c * planeVel η v 1 p.1 p.2) +
        deriv E p.1 * (((1 - p.2 / h : ℝ)) : ℂ) * ((p.1 : ℂ) * planeVel η v 0 p.1 p.2) +
        E p.1 * (((1 - p.2 / h : ℝ)) : ℂ) *
          (c * planeVel η v 1 p.1 p.2 - (p.1 : ℂ) * planeVelHeight η G 2 p.1 p.2) +
        (planeVelHeight η G 2 p.1 p.2 * (((1 - p.2 / h : ℝ)) : ℂ) - planeVel η v 2 p.1 p.2 / (h : ℂ)) *
          E p.1 * (p.1 : ℂ)) := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    push_cast
    field_simp
    ring
  have e5 := integral_add ((((i1.add i2).add i3).add j1).add j2) it
  have e4 := integral_add (((i1.add i2).add i3).add j1) j2
  have e3 := integral_add ((i1.add i2).add i3) j1
  have e2 := integral_add (i1.add i2) i3
  have e1 := integral_add i1 i2
  simp only [Pi.add_apply] at e5 e4 e3 e2
  rw [hsum, e5, e4, e3, e2, e1]
  linear_combination (-1 : ℂ) * hE1 - hE2

theorem sq_norm_real_mul (r : ℝ) (z : ℂ) : ‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem sq_norm_phase (k : ℤ) (z : ℂ) : ‖-((k : ℂ) * Complex.I) * z‖ ^ 2 = (k : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, mul_one, mul_pow, Complex.norm_intCast, sq_abs]

theorem gradSq_bound {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ) {ρ₁ ρ₂ h : ℝ} (hρ₁ : 0 < ρ₁)
    (hside : ∀ z, φ (ρ₁, z) = 0 ∧ φ (ρ₂, z) = 0) (k : ℤ) {p : ℝ × ℝ} (hp : p ∈ patch ρ₁ ρ₂ h) :
    0 ≤ patchGradSq k φ p ∧ patchGradSq k φ p ≤ K ^ 2 + K ^ 2 + (k : ℝ) ^ 2 * (K * (ρ₂ - ρ₁)) ^ 2 / ρ₁ ^ 2 := by
  have hr : ρ₁ ≤ p.1 := hp.1.1
  have hr0 : 0 < p.1 := lt_of_lt_of_le hρ₁ hr
  have hφb := phi_bound hφ hside hp
  have h1 := fderiv_bound hφ p _ norm_unit_r
  have h2 := fderiv_bound hφ p _ norm_unit_z
  have hK0 : (0 : ℝ) ≤ K := K.2
  unfold patchGradSq
  constructor
  · positivity
  · have e1 : ‖fderiv ℝ φ p (1, 0)‖ ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e2 : ‖fderiv ℝ φ p (0, 1)‖ ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have e3 : (k : ℝ) ^ 2 * ‖φ p‖ ^ 2 / p.1 ^ 2 ≤ (k : ℝ) ^ 2 * (K * (ρ₂ - ρ₁)) ^ 2 / ρ₁ ^ 2 := by
      gcongr
    linarith

end Internal.PatchTraceBound

open Internal.PatchTraceBound in
theorem patchTraceBound (hP : PlaneDataFlipHolds) (hD : ModeHeightDerivHolds) (hM : TraceMatchHolds) :
    PatchTraceBoundHolds := by
  intro Γ P v G H g hv hflip ξ ρ₁ ρ₂ h b φ K hρ₁ hρ hh hbm hb0 hb1 hφ hside htop
  obtain ⟨b₀, hb₀, hbb₀⟩ := hb0
  obtain ⟨b₁, hbb₁⟩ := hb1
  rw [main_identity hP hv hflip ξ hρ₁ hρ hh hφ hside htop]
  set η := flipLabel ξ with hη
  set S := patch ρ₁ ρ₂ h with hSdef
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hSf : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.2 (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  set R1 := ρ₂ + h + 1 with hR1
  have hSbox : S ⊆ Icc ρ₁ R1 ×ˢ Icc (-R1) R1 := fun p hp =>
    ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hcn : ∀ p : ℝ × ℝ, cnormSq (modeVel η v 0 (planePoint p)) =
      ‖planeVel η v 0 p.1 p.2‖ ^ 2 + ‖planeVel η v 1 p.1 p.2‖ ^ 2 + ‖planeVel η v 2 p.1 p.2‖ ^ 2 := by
    intro p
    simp only [cnormSq, Fin.sum_univ_three]
    rfl
  have isq : ∀ a, IntegrableOn (fun p : ℝ × ℝ => ‖planeVel η v a p.1 p.2‖ ^ 2) S := fun a =>
    IntegrableOn.mono_set ((memLp_two_iff_integrable_sq_norm (planeVel_memLp hv η a (R := R1) hρ₁).1).1
      (planeVel_memLp hv η a (R := R1) hρ₁)) hSbox
  have hb0' : ∀ p, 0 < b p := fun p => lt_of_lt_of_le hb₀ (hbb₀ p)
  have hbm' : AEStronglyMeasurable b (volume.restrict S) := hbm.aestronglyMeasurable
  refine norm_integral_sq_le ?_ ?_ ?_ ?_ ?_
  · have h1 : IntegrableOn (fun p : ℝ × ℝ => cnormSq (modeVel η v 0 (planePoint p))) S := by
      simp only [hcn]
      exact ((isq 0).add (isq 1)).add (isq 2)
    have h2 : IntegrableOn (fun p : ℝ × ℝ => b p * cnormSq (modeVel η v 0 (planePoint p))) S :=
      h1.bdd_mul (c := b₁) hbm' (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (hb0' p).le]; exact hbb₁ p)
    exact h2.mul_bdd (c := ρ₂) measurable_fst.aestronglyMeasurable
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => by
        rw [Real.norm_of_nonneg (by linarith [hp.1.1])]; exact hp.1.2))
  · have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => patchGradSq ξ.2 φ p / b p * p.1) (volume.restrict S) := by
      have m1 : Measurable (fun p : ℝ × ℝ => ‖fderiv ℝ φ p (1, 0)‖ ^ 2) :=
        (measurable_fderiv_apply_const ℝ φ (1, 0)).norm.pow_const 2
      have m2 : Measurable (fun p : ℝ × ℝ => ‖fderiv ℝ φ p (0, 1)‖ ^ 2) :=
        (measurable_fderiv_apply_const ℝ φ (0, 1)).norm.pow_const 2
      have m3 : Measurable (fun p : ℝ × ℝ => ((ξ.2 : ℤ) : ℝ) ^ 2 * ‖φ p‖ ^ 2 / p.1 ^ 2) :=
        (measurable_const.mul (hφ.continuous.measurable.norm.pow_const 2)).div (measurable_fst.pow_const 2)
      exact ((((m1.add m2).add m3).div hbm).mul measurable_fst).aestronglyMeasurable
    refine Integrable.mono' (integrable_const ((K ^ 2 + K ^ 2 + ((ξ.2 : ℤ) : ℝ) ^ 2 * (K * (ρ₂ - ρ₁)) ^ 2 / ρ₁ ^ 2)
      / b₀ * ρ₂)) hm ((ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_))
    have hg := gradSq_bound hφ hρ₁ hside ξ.2 hp
    have hr : 0 ≤ p.1 := by linarith [hp.1.1]
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg hg.1 (hb0' p).le) hr)]
    have hq : patchGradSq ξ.2 φ p / b p ≤ (K ^ 2 + K ^ 2 + ((ξ.2 : ℤ) : ℝ) ^ 2 * (K * (ρ₂ - ρ₁)) ^ 2 / ρ₁ ^ 2) / b₀ :=
      div_le_div₀ (le_trans hg.1 hg.2) hg.2 hb₀ (hbb₀ p)
    exact mul_le_mul hq hp.1.2 hr (le_trans (div_nonneg hg.1 (hb0' p).le) hq)
  · refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_)
    have hr : 0 ≤ p.1 := by linarith [hp.1.1]
    exact mul_nonneg (mul_nonneg (hb0' p).le (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hr
  · refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_)
    have hr : 0 ≤ p.1 := by linarith [hp.1.1]
    exact mul_nonneg (div_nonneg (gradSq_bound hφ hρ₁ hside ξ.2 hp).1 (hb0' p).le) hr
  · refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_)
    have hr0 : 0 < p.1 := lt_of_lt_of_le hρ₁ hp.1.1
    have hbp := hb0' p
    have e : fderiv ℝ φ p (1, 0) * ((p.1 : ℂ) * planeVel η v 0 p.1 p.2) +
        fderiv ℝ φ p (0, 1) * ((p.1 : ℂ) * planeVel η v 2 p.1 p.2) +
        φ p * (-((η.2 : ℂ) * Complex.I) * planeVel η v 1 p.1 p.2) =
        ((p.1 : ℂ) * fderiv ℝ φ p (1, 0)) * planeVel η v 0 p.1 p.2 +
        (-((η.2 : ℂ) * Complex.I) * φ p) * planeVel η v 1 p.1 p.2 +
        ((p.1 : ℂ) * fderiv ℝ φ p (0, 1)) * planeVel η v 2 p.1 p.2 := by ring
    rw [e]
    refine (sum_three_mul_le _ _ _ _ _ _).trans (le_of_eq ?_)
    rw [sq_norm_real_mul, sq_norm_real_mul, sq_norm_phase, hcn]
    have hη2 : ((η.2 : ℤ) : ℝ) ^ 2 = ((ξ.2 : ℤ) : ℝ) ^ 2 := by
      simp [hη, flipLabel]
    rw [hη2, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    unfold patchGradSq
    field_simp
    ring

end Bridge

end CertCell

end Breakdown
