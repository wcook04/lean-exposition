import Breakdown.CertCell.RowProfileDefs

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

namespace Internal.RowParts

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

def monoR (K : CellBox) (i : ℕ) (r : ℝ) : ℝ := K.refR r ^ i

def monoZ (K : CellBox) (j : ℕ) (z : ℝ) : ℝ := K.refZ z ^ j

theorem monoR_contDiff (K : CellBox) (i : ℕ) : ContDiff ℝ 1 (monoR K i) := by
  unfold monoR CellBox.refR
  fun_prop

theorem monoZ_contDiff (K : CellBox) (j : ℕ) : ContDiff ℝ 1 (monoZ K j) := by
  unfold monoZ CellBox.refZ
  fun_prop

theorem eval_expand (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) :
    P.eval K p = ∑ i, ∑ j, P.coef i j * ((monoR K i p.1 * monoZ K j p.2 : ℝ) : ℂ) := by
  unfold CellPoly.eval monoR monoZ
  push_cast
  simp only [mul_assoc]

theorem conj_eval (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) :
    (starRingEnd ℂ) (P.eval K p)
      = ∑ i, ∑ j, (starRingEnd ℂ) (P.coef i j) * ((monoR K i p.1 * monoZ K j p.2 : ℝ) : ℂ) := by
  rw [eval_expand]
  simp only [map_sum, map_mul, Complex.conj_ofReal]

theorem eval_hasDerivAt_r (K : CellBox) (P : CellPoly) (r z : ℝ) :
    HasDerivAt (fun r' => P.eval K (r', z))
      (∑ i, ∑ j, P.coef i j * ((deriv (monoR K i) r * monoZ K j z : ℝ) : ℂ)) r := by
  have e : (fun r' => P.eval K (r', z)) = fun r' => ∑ i, ∑ j, P.coef i j * ((monoR K i r' * monoZ K j z : ℝ) : ℂ) :=
    funext fun r' => eval_expand K P (r', z)
  rw [e]
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  have h1 : HasDerivAt (monoR K i) (deriv (monoR K i) r) r :=
    ((monoR_contDiff K i).differentiable one_ne_zero r).hasDerivAt
  exact ((h1.mul_const (monoZ K j z)).ofReal_comp).const_mul (P.coef i j)

theorem eval_hasDerivAt_z (K : CellBox) (P : CellPoly) (r z : ℝ) :
    HasDerivAt (fun z' => P.eval K (r, z'))
      (∑ i, ∑ j, P.coef i j * ((monoR K i r * deriv (monoZ K j) z : ℝ) : ℂ)) z := by
  have e : (fun z' => P.eval K (r, z')) = fun z' => ∑ i, ∑ j, P.coef i j * ((monoR K i r * monoZ K j z' : ℝ) : ℂ) :=
    funext fun z' => eval_expand K P (r, z')
  rw [e]
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  have h1 : HasDerivAt (monoZ K j) (deriv (monoZ K j) z) z :=
    ((monoZ_contDiff K j).differentiable one_ne_zero z).hasDerivAt
  exact ((h1.const_mul (monoR K i r)).ofReal_comp).const_mul (P.coef i j)

theorem radialDeriv_eval (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) :
    CellBox.radialDeriv (fun p => P.eval K p) p
      = ∑ i, ∑ j, P.coef i j * ((deriv (monoR K i) p.1 * monoZ K j p.2 : ℝ) : ℂ) :=
  (eval_hasDerivAt_r K P p.1 p.2).deriv

theorem heightDeriv_eval (K : CellBox) (P : CellPoly) (p : ℝ × ℝ) :
    CellBox.heightDeriv (fun p => P.eval K p) p
      = ∑ i, ∑ j, P.coef i j * ((monoR K i p.1 * deriv (monoZ K j) p.2 : ℝ) : ℂ) :=
  (eval_hasDerivAt_z K P p.1 p.2).deriv


def radialCut (K : CellBox) (i : ℕ) (r : ℝ) : ℝ :=
  r * monoR K i r - K.r₂ * monoR K i K.r₂ * ((r - K.r₁) / (K.r₂ - K.r₁))
    - K.r₁ * monoR K i K.r₁ * ((r - K.r₂) / (K.r₁ - K.r₂))

def heightCut (K : CellBox) (j : ℕ) (z : ℝ) : ℝ :=
  monoZ K j z - monoZ K j K.z₂ * ((z - K.z₁) / (K.z₂ - K.z₁))
    - monoZ K j K.z₁ * ((z - K.z₂) / (K.z₁ - K.z₂))

theorem radialCut_hasDerivAt (K : CellBox) (i : ℕ) (r : ℝ) :
    HasDerivAt (radialCut K i) (monoR K i r + r * deriv (monoR K i) r
      - K.r₂ * monoR K i K.r₂ / (K.r₂ - K.r₁) - K.r₁ * monoR K i K.r₁ / (K.r₁ - K.r₂)) r := by
  have h1 : HasDerivAt (monoR K i) (deriv (monoR K i) r) r :=
    ((monoR_contDiff K i).differentiable one_ne_zero r).hasDerivAt
  have h2 := (hasDerivAt_id' r).mul h1
  have h3 := (((hasDerivAt_id' r).sub_const K.r₁).div_const (K.r₂ - K.r₁)).const_mul (K.r₂ * monoR K i K.r₂)
  have h4 := (((hasDerivAt_id' r).sub_const K.r₂).div_const (K.r₁ - K.r₂)).const_mul (K.r₁ * monoR K i K.r₁)
  have h5 := (h2.sub h3).sub h4
  unfold radialCut
  exact h5.congr_deriv (by ring)

theorem heightCut_hasDerivAt (K : CellBox) (j : ℕ) (z : ℝ) :
    HasDerivAt (heightCut K j) (deriv (monoZ K j) z
      - monoZ K j K.z₂ / (K.z₂ - K.z₁) - monoZ K j K.z₁ / (K.z₁ - K.z₂)) z := by
  have h1 : HasDerivAt (monoZ K j) (deriv (monoZ K j) z) z :=
    ((monoZ_contDiff K j).differentiable one_ne_zero z).hasDerivAt
  have h3 := (((hasDerivAt_id' z).sub_const K.z₁).div_const (K.z₂ - K.z₁)).const_mul (monoZ K j K.z₂)
  have h4 := (((hasDerivAt_id' z).sub_const K.z₂).div_const (K.z₁ - K.z₂)).const_mul (monoZ K j K.z₁)
  have h5 := (h1.sub h3).sub h4
  unfold heightCut
  exact h5.congr_deriv (by ring)

theorem radialCut_contDiff (K : CellBox) (i : ℕ) : ContDiff ℝ 1 (radialCut K i) := by
  unfold radialCut
  have := monoR_contDiff K i
  fun_prop

theorem heightCut_contDiff (K : CellBox) (j : ℕ) : ContDiff ℝ 1 (heightCut K j) := by
  unfold heightCut
  have := monoZ_contDiff K j
  fun_prop

theorem radialCut_left (K : CellBox) (h : K.r₁ < K.r₂) (i : ℕ) : radialCut K i K.r₁ = 0 := by
  have : K.r₁ - K.r₂ ≠ 0 := sub_ne_zero.2 h.ne
  unfold radialCut
  rw [sub_self, zero_div, mul_zero, sub_zero, div_self this, mul_one, sub_self]

theorem radialCut_right (K : CellBox) (h : K.r₁ < K.r₂) (i : ℕ) : radialCut K i K.r₂ = 0 := by
  have : K.r₂ - K.r₁ ≠ 0 := sub_ne_zero.2 h.ne'
  unfold radialCut
  rw [div_self this, mul_one, sub_self, sub_self, zero_div, mul_zero, sub_zero]

theorem heightCut_left (K : CellBox) (h : K.z₁ < K.z₂) (j : ℕ) : heightCut K j K.z₁ = 0 := by
  have : K.z₁ - K.z₂ ≠ 0 := sub_ne_zero.2 h.ne
  unfold heightCut
  rw [sub_self, zero_div, mul_zero, sub_zero, div_self this, mul_one, sub_self]

theorem heightCut_right (K : CellBox) (h : K.z₁ < K.z₂) (j : ℕ) : heightCut K j K.z₂ = 0 := by
  have : K.z₂ - K.z₁ ≠ 0 := sub_ne_zero.2 h.ne'
  unfold heightCut
  rw [div_self this, mul_one, sub_self, sub_self, zero_div, mul_zero, sub_zero]

theorem radial_algebra (K : CellBox) (P : CellPoly) (S T : ℂ) (p : ℝ × ℝ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (P.coef i j) * (T * ((radialCut K i p.1 * monoZ K j p.2 : ℝ) : ℂ)
        + S * ((deriv (radialCut K i) p.1 * monoZ K j p.2 : ℝ) : ℂ))
      = (p.1 : ℂ) * T * (starRingEnd ℂ) (P.eval K p)
        + S * ((starRingEnd ℂ) (P.eval K p) + (p.1 : ℂ) * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => P.eval K q) p))
        - (K.r₂ : ℂ) * ((((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) * S + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * T)
            * (starRingEnd ℂ) (P.eval K (K.r₂, p.2))
        - (K.r₁ : ℂ) * ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * S + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * T)
            * (starRingEnd ℂ) (P.eval K (K.r₁, p.2)) := by
  simp only [(radialCut_hasDerivAt K _ p.1).deriv, conj_eval, radialDeriv_eval, map_sum, map_mul, Complex.conj_ofReal]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold radialCut
  push_cast
  ring

theorem height_algebra (K : CellBox) (P : CellPoly) (S T : ℂ) (p : ℝ × ℝ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (P.coef i j) * ((p.1 : ℂ) * (T * ((monoR K i p.1 * heightCut K j p.2 : ℝ) : ℂ)
        + S * ((monoR K i p.1 * deriv (heightCut K j) p.2 : ℝ) : ℂ)))
      = (p.1 : ℂ) * T * (starRingEnd ℂ) (P.eval K p)
        + (p.1 : ℂ) * S * (starRingEnd ℂ) (CellBox.heightDeriv (fun q => P.eval K q) p)
        - (p.1 : ℂ) * ((((1 / (K.z₂ - K.z₁) : ℝ)) : ℂ) * S + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * T)
            * (starRingEnd ℂ) (P.eval K (p.1, K.z₂))
        - (p.1 : ℂ) * ((((1 / (K.z₁ - K.z₂) : ℝ)) : ℂ) * S + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * T)
            * (starRingEnd ℂ) (P.eval K (p.1, K.z₁)) := by
  simp only [(heightCut_hasDerivAt K _ p.2).deriv, conj_eval, heightDeriv_eval, map_sum, map_mul, Complex.conj_ofReal]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold heightCut
  push_cast
  ring

theorem continuous_eval (K : CellBox) (P : CellPoly) : Continuous (fun p : ℝ × ℝ => P.eval K p) := by
  unfold CellPoly.eval CellBox.refR CellBox.refZ
  fun_prop

theorem continuous_radialDeriv_eval (K : CellBox) (P : CellPoly) :
    Continuous (fun p : ℝ × ℝ => CellBox.radialDeriv (fun q => P.eval K q) p) := by
  simp only [radialDeriv_eval]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
  exact (((monoR_contDiff K i).continuous_deriv le_rfl).comp continuous_fst).mul
    ((monoZ_contDiff K j).continuous.comp continuous_snd)

theorem continuous_heightDeriv_eval (K : CellBox) (P : CellPoly) :
    Continuous (fun p : ℝ × ℝ => CellBox.heightDeriv (fun q => P.eval K q) p) := by
  simp only [heightDeriv_eval]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
  exact ((monoR_contDiff K i).continuous.comp continuous_fst).mul
    (((monoZ_contDiff K j).continuous_deriv le_rfl).comp continuous_snd)

theorem cont_conj_eval_side (K : CellBox) (P : CellPoly) (c : ℝ) :
    Continuous (fun p : ℝ × ℝ => (starRingEnd ℂ) (P.eval K (c, p.2))) :=
  Complex.continuous_conj.comp ((continuous_eval K P).comp (continuous_const.prodMk continuous_snd))

theorem cont_conj_eval_level (K : CellBox) (P : CellPoly) (c : ℝ) :
    Continuous (fun p : ℝ × ℝ => (starRingEnd ℂ) (P.eval K (p.1, c))) :=
  Complex.continuous_conj.comp ((continuous_eval K P).comp (continuous_fst.prodMk continuous_const))

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem rect_measurable (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem int_mul_cont {K : CellBox} {f h : ℝ × ℝ → ℂ} (hf : IntegrableOn f K.rect) (hh : Continuous h) :
    IntegrableOn (fun p => h p * f p) K.rect :=
  IntegrableOn.continuousOn_mul hh.continuousOn hf (rect_compact K)

theorem slice_ae_z {f : ℝ × ℝ → ℂ} {a b c d : ℝ} (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∀ᵐ z ∂(volume.restrict (Icc c d)), IntegrableOn (fun r => f (r, z)) (Icc a b) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact hf.prod_left_ae

theorem slice_ae_r {f : ℝ × ℝ → ℂ} {a b c d : ℝ} (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∀ᵐ r ∂(volume.restrict (Icc a b)), IntegrableOn (fun z => f (r, z)) (Icc c d) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact hf.prod_right_ae

theorem iterated_z {f : ℝ × ℝ → ℂ} {a b c d : ℝ} (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∫ p in Icc a b ×ˢ Icc c d, f p = ∫ z in Icc c d, ∫ r in Icc a b, f (r, z) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_symm f hf

theorem iterated_r {f : ℝ × ℝ → ℂ} {a b c d : ℝ} (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∫ p in Icc a b ×ˢ Icc c d, f p = ∫ r in Icc a b, ∫ z in Icc c d, f (r, z) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod f hf

theorem radial_boundary (K : CellBox) (φ : Fin 3 → CellPoly) (F dF : Fin 3 → ℝ × ℝ → ℂ) (c o σ : ℝ)
    (hmin : min c o = K.r₁) (hmax : max c o = K.r₂) (hσ : (σ : ℂ) * edgeSign c o = 1)
    (hint : ∀ a, IntegrableOn (fun p => (c : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * F a p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF a p)) K.rect) :
    IntegrableOn (fun p => ∑ a : Fin 3, (c : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * F a p
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF a p) * (starRingEnd ℂ) ((φ a).eval K (c, p.2))) K.rect ∧
    (σ : ℂ) * ∫ z in Icc K.z₁ K.z₂, (c : ℂ) * cdot3 (fun a => radialStripTrace c o (F a) (dF a) z)
        (testValue K φ (c, z))
      = ∫ p in K.rect, ∑ a : Fin 3, (c : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * F a p
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF a p) * (starRingEnd ℂ) ((φ a).eval K (c, p.2)) := by
  set X : Fin 3 → ℝ × ℝ → ℂ := fun a p => (c : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * F a p
    + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF a p) * (starRingEnd ℂ) ((φ a).eval K (c, p.2)) with hX
  have hXi : ∀ a, IntegrableOn (X a) K.rect := by
    intro a
    have h := int_mul_cont (hint a) (cont_conj_eval_side K (φ a) c)
    refine h.congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [hX]
    ring
  have hS : IntegrableOn (fun p => ∑ a : Fin 3, X a p) K.rect := by
    simp only [Fin.sum_univ_three]
    exact ((hXi 0).add (hXi 1)).add (hXi 2)
  have hsl : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)), ∀ a, IntegrableOn (fun r => X a (r, z)) (Icc K.r₁ K.r₂) :=
    ae_all_iff.2 fun a => slice_ae_z (hXi a)
  refine ⟨hS, ?_⟩
  rw [CellBox.rect] at hS ⊢
  rw [iterated_z hS, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hsl] with z hz
  rw [integral_finsetSum _ fun a _ => hz a]
  simp only [cdot3, testValue, radialStripTrace, hmin, hmax, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [hX]
  rw [integral_mul_const, integral_const_mul]
  linear_combination (((c : ℂ) * (starRingEnd ℂ) ((φ a).eval K (c, z))) * ∫ r in Icc K.r₁ K.r₂,
    ((((1 / (c - o) : ℝ)) : ℂ) * F a (r, z) + (((r - o) / (c - o) : ℝ) : ℂ) * dF a (r, z))) * hσ

theorem height_boundary (K : CellBox) (φ : Fin 3 → CellPoly) (F dF : Fin 3 → ℝ × ℝ → ℂ) (c o σ : ℝ)
    (hmin : min c o = K.z₁) (hmax : max c o = K.z₂) (hσ : (σ : ℂ) * edgeSign c o = 1)
    (hint : ∀ a, IntegrableOn (fun p => (p.1 : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * F a p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF a p)) K.rect) :
    IntegrableOn (fun p => ∑ a : Fin 3, (p.1 : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * F a p
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF a p) * (starRingEnd ℂ) ((φ a).eval K (p.1, c))) K.rect ∧
    (σ : ℂ) * ∫ r in Icc K.r₁ K.r₂, (r : ℂ) * cdot3 (fun a => heightStripTrace c o (F a) (dF a) r)
        (testValue K φ (r, c))
      = ∫ p in K.rect, ∑ a : Fin 3, (p.1 : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * F a p
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF a p) * (starRingEnd ℂ) ((φ a).eval K (p.1, c)) := by
  set X : Fin 3 → ℝ × ℝ → ℂ := fun a p => (p.1 : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * F a p
    + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF a p) * (starRingEnd ℂ) ((φ a).eval K (p.1, c)) with hX
  have hXi : ∀ a, IntegrableOn (X a) K.rect := by
    intro a
    have h := int_mul_cont (hint a) (cont_conj_eval_level K (φ a) c)
    refine h.congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [hX]
    ring
  have hS : IntegrableOn (fun p => ∑ a : Fin 3, X a p) K.rect := by
    simp only [Fin.sum_univ_three]
    exact ((hXi 0).add (hXi 1)).add (hXi 2)
  have hsl : ∀ᵐ r ∂(volume.restrict (Icc K.r₁ K.r₂)), ∀ a, IntegrableOn (fun z => X a (r, z)) (Icc K.z₁ K.z₂) :=
    ae_all_iff.2 fun a => slice_ae_r (hXi a)
  refine ⟨hS, ?_⟩
  rw [CellBox.rect] at hS ⊢
  rw [iterated_r hS, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hsl] with r hr
  rw [integral_finsetSum _ fun a _ => hr a]
  simp only [cdot3, testValue, heightStripTrace, hmin, hmax, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [hX]
  rw [integral_mul_const, integral_const_mul]
  linear_combination (((r : ℂ) * (starRingEnd ℂ) ((φ a).eval K (r, c))) * ∫ z in Icc K.z₁ K.z₂,
    ((((1 / (c - o) : ℝ)) : ℂ) * F a (r, z) + (((z - o) / (c - o) : ℝ) : ℂ) * dF a (r, z))) * hσ

theorem turn_adjoint (k : ℝ) (x y : Fin 3 → ℂ) :
    ∑ a : Fin 3, (turnVector k x a * (starRingEnd ℂ) (y a) + x a * (starRingEnd ℂ) (turnVector k y a)) = 0 := by
  simp [Fin.sum_univ_three, turnVector, map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem integrable_zero_sum {ι : Type*} (S : Finset ι) {K : CellBox} (f : ι → ℝ × ℝ → ℂ)
    (h : ∀ i, IntegrableOn (f i) K.rect ∧ ∫ p in K.rect, f i p = 0) :
    IntegrableOn (fun p => ∑ i ∈ S, f i p) K.rect ∧ ∫ p in K.rect, ∑ i ∈ S, f i p = 0 := by
  refine ⟨integrable_finsetSum S fun i _ => (h i).1, ?_⟩
  rw [integral_finsetSum S fun i _ => (h i).1]
  exact Finset.sum_eq_zero fun i _ => (h i).2

theorem integrable_zero_smul {K : CellBox} (w : ℂ) {f : ℝ × ℝ → ℂ}
    (h : IntegrableOn f K.rect ∧ ∫ p in K.rect, f p = 0) :
    IntegrableOn (fun p => w * f p) K.rect ∧ ∫ p in K.rect, w * f p = 0 := by
  refine ⟨h.1.const_mul w, ?_⟩
  rw [integral_const_mul, h.2, mul_zero]

theorem radial_hint {K : CellBox} {S T : ℝ × ℝ → ℂ} (hS : IntegrableOn S K.rect)
    (hT : IntegrableOn (fun p => (p.1 : ℂ) * T p) K.rect) (hT' : K.r₁ ≠ 0 → IntegrableOn T K.rect) (c o : ℝ)
    (hcase : c = 0 ∨ K.r₁ ≠ 0 ∨ o = 0) :
    IntegrableOn (fun p => (c : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * S p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * T p))
      K.rect := by
  rcases hcase with h | h | h
  · have e : (fun p : ℝ × ℝ => (c : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * S p
        + (((p.1 - o) / (c - o) : ℝ) : ℂ) * T p)) = fun _ => 0 := by
      funext p
      simp [h]
    rw [e]
    exact integrableOn_zero
  · have hc : Continuous (fun p : ℝ × ℝ => ((((p.1 - o) / (c - o) : ℝ)) : ℂ)) := by fun_prop
    exact ((hS.const_mul _).add (int_mul_cont (hT' h) hc)).const_mul _
  · refine IntegrableOn.congr_fun (((hS.const_mul (((1 / (c - o) : ℝ)) : ℂ)).add
      (hT.const_mul (((1 / (c - o) : ℝ)) : ℂ))).const_mul (c : ℂ)) (fun p _ => ?_) (rect_measurable K)
    simp only [h, sub_zero, Pi.add_apply]
    push_cast
    ring

theorem height_hint {K : CellBox} {S T : ℝ × ℝ → ℂ} (hS : IntegrableOn S K.rect)
    (hT : IntegrableOn (fun p => (p.1 : ℂ) * T p) K.rect) (c o : ℝ) :
    IntegrableOn (fun p => (p.1 : ℂ) * ((((1 / (c - o) : ℝ)) : ℂ) * S p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * T p))
      K.rect := by
  have hc1 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * (((1 / (c - o) : ℝ)) : ℂ)) := by fun_prop
  have hc2 : Continuous (fun p : ℝ × ℝ => ((((p.2 - o) / (c - o) : ℝ)) : ℂ)) := by fun_prop
  refine IntegrableOn.congr_fun ((int_mul_cont hS hc1).add (int_mul_cont hT hc2)) (fun p _ => ?_)
    (rect_measurable K)
  simp only [Pi.add_apply]
  ring

theorem ae_first_ne_zero_rect (K : CellBox) : ∀ᵐ p ∂(volume.restrict K.rect), p.1 ≠ 0 := by
  have hnull : volume ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = 0 := by
    rw [show ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) by
      ext p; simp, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  refine ae_restrict_of_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with p hp
  simpa using hp

theorem row_parts_identity (K : CellBox) (hK : IsCellBox K) (k : ℝ) (s : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (t : Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (R : RowProfile)
    (hgrad : ∀ p, R.grad p = fun a b => s a b p) (hlap : ∀ p, R.lap p = fun a => ∑ c : Fin 3, t a c c p)
    (hrad : ∀ e z, R.radialSide e z
      = fun a => radialStripTrace (sideRadius K e) (otherRadius K e) (s a 0) (t a 0 0) z)
    (hht : ∀ e r, R.heightSide e r
      = fun a => heightStripTrace (sideHeight K e) (otherHeight K e) (s a 2) (t a 2 2) r)
    (hsI : ∀ a b, IntegrableOn (s a b) K.rect)
    (htI : ∀ a b c, IntegrableOn (fun p => (p.1 : ℂ) * t a b c p) K.rect)
    (hR : ∀ a (χ τ : ℝ → ℝ), ContDiff ℝ 1 χ → χ K.r₁ = 0 → χ K.r₂ = 0 → Continuous τ →
      IntegrableOn (fun p => t a 0 0 p * ((χ p.1 * τ p.2 : ℝ) : ℂ)
        + s a 0 p * ((deriv χ p.1 * τ p.2 : ℝ) : ℂ)) K.rect ∧
      ∫ p in K.rect, (t a 0 0 p * ((χ p.1 * τ p.2 : ℝ) : ℂ) + s a 0 p * ((deriv χ p.1 * τ p.2 : ℝ) : ℂ)) = 0)
    (hZ : ∀ a (A χ : ℝ → ℝ), ContDiff ℝ 1 A → ContDiff ℝ 1 χ → χ K.z₁ = 0 → χ K.z₂ = 0 →
      IntegrableOn (fun p => (p.1 : ℂ) * (t a 2 2 p * ((A p.1 * χ p.2 : ℝ) : ℂ)
        + s a 2 p * ((A p.1 * deriv χ p.2 : ℝ) : ℂ))) K.rect ∧
      ∫ p in K.rect, (p.1 : ℂ) * (t a 2 2 p * ((A p.1 * χ p.2 : ℝ) : ℂ)
        + s a 2 p * ((A p.1 * deriv χ p.2 : ℝ) : ℂ)) = 0)
    (hA : ∀ a, ∀ᵐ p ∂(volume.restrict K.rect),
      (p.1 : ℂ) * t a 1 1 p = turnVector k (fun b => s b 1 p) a + s a 0 p)
    (φ : Fin 3 → CellPoly) :
    rowPairing K R.lap φ = rowBoundaryGrad K R φ
      - ∫ p in K.rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b) := by
  have h12 : K.r₁ < K.r₂ := hK.r_order.2
  have hz12 : K.z₁ < K.z₂ := hK.z_order.2
  have hKm := rect_measurable K
  have htI' : K.r₁ ≠ 0 → ∀ a b c, IntegrableOn (t a b c) K.rect := by
    intro h0 a b c
    have hpos : ∀ p ∈ K.rect, ((p.1 : ℂ)) ≠ 0 := fun p hp =>
      Complex.ofReal_ne_zero.2 (ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)) hp.1.1))
    have hc : ContinuousOn (fun p : ℝ × ℝ => ((p.1 : ℂ))⁻¹) K.rect :=
      (Complex.continuous_ofReal.comp continuous_fst).continuousOn.inv₀ hpos
    refine IntegrableOn.congr_fun (IntegrableOn.continuousOn_mul hc (htI a b c) (rect_compact K))
      (fun p hp => ?_) hKm
    rw [← mul_assoc, inv_mul_cancel₀ (hpos p hp), one_mul]
  obtain ⟨iR0, eR0⟩ := radial_boundary K φ (fun a => s a 0) (fun a => t a 0 0) K.r₁ K.r₂ (-1)
    (min_eq_left h12.le) (max_eq_right h12.le) (by simp [edgeSign, not_lt.2 h12.le])
    (fun a => radial_hint (hsI a 0) (htI a 0 0) (fun h => htI' h a 0 0) K.r₁ K.r₂
      (or_iff_not_imp_left.2 fun h => Or.inl h))
  obtain ⟨iR1, eR1⟩ := radial_boundary K φ (fun a => s a 0) (fun a => t a 0 0) K.r₂ K.r₁ 1
    (min_eq_right h12.le) (max_eq_left h12.le) (by simp [edgeSign, h12])
    (fun a => radial_hint (hsI a 0) (htI a 0 0) (fun h => htI' h a 0 0) K.r₂ K.r₁
      (Or.inr (ne_or_eq K.r₁ 0)))
  obtain ⟨iH0, eH0⟩ := height_boundary K φ (fun a => s a 2) (fun a => t a 2 2) K.z₁ K.z₂ (-1)
    (min_eq_left hz12.le) (max_eq_right hz12.le) (by simp [edgeSign, not_lt.2 hz12.le])
    (fun a => height_hint (hsI a 2) (htI a 2 2) K.z₁ K.z₂)
  obtain ⟨iH1, eH1⟩ := height_boundary K φ (fun a => s a 2) (fun a => t a 2 2) K.z₂ K.z₁ 1
    (min_eq_right hz12.le) (max_eq_left hz12.le) (by simp [edgeSign, hz12])
    (fun a => height_hint (hsI a 2) (htI a 2 2) K.z₂ K.z₁)
  have hB : rowBoundaryGrad K R φ
      = ((-1 : ℝ) : ℂ) * (∫ z in Icc K.z₁ K.z₂, (K.r₁ : ℂ) * cdot3
          (fun a => radialStripTrace K.r₁ K.r₂ ((fun a => s a 0) a) ((fun a => t a 0 0) a) z)
          (testValue K φ (K.r₁, z)))
        + ((-1 : ℝ) : ℂ) * (∫ r in Icc K.r₁ K.r₂, (r : ℂ) * cdot3
          (fun a => heightStripTrace K.z₁ K.z₂ ((fun a => s a 2) a) ((fun a => t a 2 2) a) r)
          (testValue K φ (r, K.z₁)))
        + ((1 : ℝ) : ℂ) * (∫ z in Icc K.z₁ K.z₂, (K.r₂ : ℂ) * cdot3
          (fun a => radialStripTrace K.r₂ K.r₁ ((fun a => s a 0) a) ((fun a => t a 0 0) a) z)
          (testValue K φ (K.r₂, z)))
        + ((1 : ℝ) : ℂ) * (∫ r in Icc K.r₁ K.r₂, (r : ℂ) * cdot3
          (fun a => heightStripTrace K.z₂ K.z₁ ((fun a => s a 2) a) ((fun a => t a 2 2) a) r)
          (testValue K φ (r, K.z₂))) := by
    have a0 : sideRadius K 0 = K.r₁ := if_pos rfl
    have a1 : sideRadius K 1 = K.r₂ := if_neg (by decide)
    have b0 : otherRadius K 0 = K.r₂ := if_pos rfl
    have b1 : otherRadius K 1 = K.r₁ := if_neg (by decide)
    have c0 : sideHeight K 0 = K.z₁ := if_pos rfl
    have c1 : sideHeight K 1 = K.z₂ := if_neg (by decide)
    have d0 : otherHeight K 0 = K.z₂ := if_pos rfl
    have d1 : otherHeight K 1 = K.z₁ := if_neg (by decide)
    have g0 : sideSign 0 = -1 := if_pos rfl
    have g1 : sideSign 1 = 1 := if_neg (by decide)
    simp only [rowBoundaryGrad, Fin.sum_univ_two, hrad, hht]
    rw [a0, a1, b0, b1, c0, c1, d0, d1, g0, g1]
    push_cast
    ring
  beta_reduce at hB eR0 eR1 eH0 eH1 iR0 iR1 iH0 iH1
  obtain ⟨RB0, hRB0⟩ : ∃ f : ℝ × ℝ → ℂ, f = fun p => ∑ a : Fin 3, (K.r₁ : ℂ) * ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ)
      * s a 0 p + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * t a 0 0 p)
        * (starRingEnd ℂ) ((φ a).eval K (K.r₁, p.2)) := ⟨_, rfl⟩
  obtain ⟨RB1, hRB1⟩ : ∃ f : ℝ × ℝ → ℂ, f = fun p => ∑ a : Fin 3, (K.r₂ : ℂ) * ((((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ)
      * s a 0 p + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * t a 0 0 p)
        * (starRingEnd ℂ) ((φ a).eval K (K.r₂, p.2)) := ⟨_, rfl⟩
  obtain ⟨HB0, hHB0⟩ : ∃ f : ℝ × ℝ → ℂ, f = fun p => ∑ a : Fin 3, (p.1 : ℂ) * ((((1 / (K.z₁ - K.z₂) : ℝ)) : ℂ)
      * s a 2 p + (((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) : ℂ) * t a 2 2 p)
        * (starRingEnd ℂ) ((φ a).eval K (p.1, K.z₁)) := ⟨_, rfl⟩
  obtain ⟨HB1, hHB1⟩ : ∃ f : ℝ × ℝ → ℂ, f = fun p => ∑ a : Fin 3, (p.1 : ℂ) * ((((1 / (K.z₂ - K.z₁) : ℝ)) : ℂ)
      * s a 2 p + (((p.2 - K.z₁) / (K.z₂ - K.z₁) : ℝ) : ℂ) * t a 2 2 p)
        * (starRingEnd ℂ) ((φ a).eval K (p.1, K.z₂)) := ⟨_, rfl⟩
  rw [← hRB0] at iR0 eR0
  rw [← hRB1] at iR1 eR1
  rw [← hHB0] at iH0 eH0
  rw [← hHB1] at iH1 eH1
  obtain ⟨Rb, hRb⟩ : ∃ f : Fin 3 → ℝ × ℝ → ℂ, f = fun a p => ∑ i, ∑ j, (starRingEnd ℂ) ((φ a).coef i j) *
      (t a 0 0 p * ((radialCut K i p.1 * monoZ K j p.2 : ℝ) : ℂ)
        + s a 0 p * ((deriv (radialCut K i) p.1 * monoZ K j p.2 : ℝ) : ℂ)) := ⟨_, rfl⟩
  obtain ⟨Hb, hHb⟩ : ∃ f : Fin 3 → ℝ × ℝ → ℂ, f = fun a p => ∑ i, ∑ j, (starRingEnd ℂ) ((φ a).coef i j) *
      ((p.1 : ℂ) * (t a 2 2 p * ((monoR K i p.1 * heightCut K j p.2 : ℝ) : ℂ)
        + s a 2 p * ((monoR K i p.1 * deriv (heightCut K j) p.2 : ℝ) : ℂ))) := ⟨_, rfl⟩
  have hRbz : ∀ a, IntegrableOn (Rb a) K.rect ∧ ∫ p in K.rect, Rb a p = 0 := by
    intro a
    rw [hRb]
    beta_reduce
    exact integrable_zero_sum _ _ fun i => integrable_zero_sum _ _ fun j => integrable_zero_smul _
      (hR a (radialCut K i) (monoZ K j) (radialCut_contDiff K i) (radialCut_left K h12 i)
        (radialCut_right K h12 i) (monoZ_contDiff K j).continuous)
  have hHbz : ∀ a, IntegrableOn (Hb a) K.rect ∧ ∫ p in K.rect, Hb a p = 0 := by
    intro a
    rw [hHb]
    beta_reduce
    exact integrable_zero_sum _ _ fun i => integrable_zero_sum _ _ fun j => integrable_zero_smul _
      (hZ a (monoR K i) (heightCut K j) (monoR_contDiff K i) (heightCut_contDiff K j) (heightCut_left K hz12 j)
        (heightCut_right K hz12 j))
  have hRH : IntegrableOn (fun p => ∑ a : Fin 3, (Rb a p + Hb a p)) K.rect ∧
      ∫ p in K.rect, ∑ a : Fin 3, (Rb a p + Hb a p) = 0 :=
    integrable_zero_sum _ _ fun a => ⟨(hRbz a).1.add (hHbz a).1, by
      rw [integral_add (hRbz a).1 (hHbz a).1, (hRbz a).2, (hHbz a).2, add_zero]⟩
  obtain ⟨Dg, hDg⟩ : ∃ f : ℝ × ℝ → ℂ, f = fun p => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
      R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b) := ⟨_, rfl⟩
  have hpt : ∀ᵐ p ∂(volume.restrict K.rect), (p.1 : ℂ) * cdot3 (R.lap p) (testValue K φ p) =
      (RB0 p + HB0 p + RB1 p + HB1 p + ∑ a : Fin 3, (Rb a p + Hb a p)) - Dg p := by
    filter_upwards [hA 0, hA 1, hA 2, ae_first_ne_zero_rect K] with p h0 h1 h2 hp
    have hpc : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp
    have ra := fun a => radial_algebra K (φ a) (s a 0 p) (t a 0 0 p) p
    have ha := fun a => height_algebra K (φ a) (s a 2 p) (t a 2 2 p) p
    have hang : ∀ a, (p.1 : ℂ) * (starRingEnd ℂ) (turnVector k (testValue K φ p) a / (p.1 : ℂ))
        = (starRingEnd ℂ) (turnVector k (testValue K φ p) a) := by
      intro a
      rw [map_div₀, Complex.conj_ofReal]
      field_simp
    have adj := turn_adjoint k (fun b => s b 1 p) (testValue K φ p)
    have tv : ∀ a, testValue K φ p a = (φ a).eval K p := fun a => rfl
    have tg0 : ∀ a, testGrad K k φ p a 0 = CellBox.radialDeriv (fun q => (φ a).eval K q) p := fun a => by
      simp [testGrad]
    have tg1 : ∀ a, testGrad K k φ p a 1 = turnVector k (testValue K φ p) a / (p.1 : ℂ) := fun a => by
      simp [testGrad]
    have tg2 : ∀ a, testGrad K k φ p a 2 = CellBox.heightDeriv (fun q => (φ a).eval K q) p := fun a => by
      simp [testGrad]
    simp only [Fin.sum_univ_three, tv] at adj
    rw [hRB0, hRB1, hHB0, hHB1, hRb, hHb, hDg]
    simp only [cdot3, hlap, hgrad, Fin.sum_univ_three, tv, tg0, tg1, tg2]
    linear_combination (-1 : ℂ) * (ra 0 + ra 1 + ra 2) - (ha 0 + ha 1 + ha 2)
      + (starRingEnd ℂ) ((φ 0).eval K p) * h0 + (starRingEnd ℂ) ((φ 1).eval K p) * h1
      + (starRingEnd ℂ) ((φ 2).eval K p) * h2
      + s 0 1 p * hang 0 + s 1 1 p * hang 1 + s 2 1 p * hang 2 + adj
  have hAi : IntegrableOn (fun p => (p.1 : ℂ) * cdot3 (R.lap p) (testValue K φ p)) K.rect := by
    have hc : ∀ a, Continuous (fun p : ℝ × ℝ => (starRingEnd ℂ) ((φ a).eval K p)) := fun a =>
      Complex.continuous_conj.comp (continuous_eval K (φ a))
    refine IntegrableOn.congr_fun (integrable_finsetSum Finset.univ fun a _ =>
      integrable_finsetSum Finset.univ fun c _ => int_mul_cont (htI a c c) (hc a)) (fun p _ => ?_) hKm
    simp only [cdot3, hlap, testValue, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  have hW : IntegrableOn (fun p => (RB0 p + HB0 p + RB1 p + HB1 p + ∑ a : Fin 3, (Rb a p + Hb a p))
      - (p.1 : ℂ) * cdot3 (R.lap p) (testValue K φ p)) K.rect :=
    ((((iR0.add iH0).add iR1).add iH1).add hRH.1).sub hAi
  have hDi : IntegrableOn Dg K.rect := by
    refine Integrable.congr hW ?_
    filter_upwards [hpt] with p hp
    rw [hp]
    ring
  have hmain := integral_congr_ae hpt
  have i1 : IntegrableOn (fun p => RB0 p + HB0 p) K.rect := iR0.add iH0
  have i2 : IntegrableOn (fun p => RB0 p + HB0 p + RB1 p) K.rect := i1.add iR1
  have i3 : IntegrableOn (fun p => RB0 p + HB0 p + RB1 p + HB1 p) K.rect := i2.add iH1
  have i4 : IntegrableOn (fun p => RB0 p + HB0 p + RB1 p + HB1 p + ∑ a : Fin 3, (Rb a p + Hb a p)) K.rect :=
    i3.add hRH.1
  rw [integral_sub i4 hDi, integral_add i3 hRH.1, integral_add i2 iH1, integral_add i1 iR1,
    integral_add iR0 iH0, hRH.2] at hmain
  rw [rowPairing, hmain, hB, ← hDg]
  linear_combination (-1 : ℂ) * (eR0 + eH0 + eR1 + eH1)

end Internal.RowParts

end CellCalculus

end CertCell

end Breakdown
