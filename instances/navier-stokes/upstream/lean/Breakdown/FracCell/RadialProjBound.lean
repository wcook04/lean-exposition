import Breakdown.FracCell.VelocityTailSt
import Breakdown.FracCell.ResolvedEnergyCore

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace RadialProjBoundInternal

variable (K : CellBox)

def pl {d : ℕ} (c : Fin (d + 1) → ℂ) (r : ℝ) : ℂ := ∑ j, c j * (r : ℂ) ^ (j : ℕ)

def pairingMat (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun t j =>
  ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * (r : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))

def rhs (d : ℕ) (f : ℝ → ℂ) : Fin (d + 1) → ℂ := fun t =>
  ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * f r * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))

def sol (d : ℕ) (f : ℝ → ℂ) : Fin (d + 1) → ℂ := Matrix.mulVec (pairingMat K d)⁻¹ (rhs K d f)

theorem w_nonneg {r : ℝ} (hr : r ∈ Set.Icc K.r₁ K.r₂) : 0 ≤ K.lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs
  · linarith [hr.1]
  · exact zero_le_one

theorem w_pos {r : ℝ} (hr : r ∈ Set.Ioo K.r₁ K.r₂) : 0 < K.lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs
  · linarith [hr.1]
  · exact zero_lt_one

theorem pl_cont {d : ℕ} (c : Fin (d + 1) → ℂ) : Continuous (pl c) := by
  unfold pl
  fun_prop

theorem wc_cont : Continuous (fun r : ℝ => (K.lineWeight r : ℂ)) :=
  Complex.continuous_ofReal.comp (ResolvedEnergyInternal.lw_cont K)

theorem pow_cont (t : ℕ) : Continuous (fun r : ℝ => (r : ℂ) ^ t) :=
  Complex.continuous_ofReal.pow t

theorem pow_conj_cont (t : ℕ) : Continuous (fun r : ℝ => (starRingEnd ℂ) ((r : ℂ) ^ t)) :=
  Complex.continuous_conj.comp (Complex.continuous_ofReal.pow t)

theorem sq_int_cont {g : ℝ → ℂ} (hg : Continuous g) :
    IntegrableOn (fun r => K.lineWeight r * ‖g r‖ ^ 2) (Set.Icc K.r₁ K.r₂) :=
  ((ResolvedEnergyInternal.lw_cont K).mul (hg.norm.pow 2)).integrableOn_Icc

theorem cross_int {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc K.r₁ K.r₂)))
    (hfi : IntegrableOn (fun r => K.lineWeight r * ‖f r‖ ^ 2) (Set.Icc K.r₁ K.r₂)) (hg : Continuous g) :
    IntegrableOn (fun r => (K.lineWeight r : ℂ) * f r * (starRingEnd ℂ) (g r)) (Set.Icc K.r₁ K.r₂) := by
  have hgi := sq_int_cont K hg
  refine Integrable.mono' (hfi.add hgi) ?_ ?_
  · exact ((wc_cont K).aestronglyMeasurable.mul hf).mul (Complex.continuous_conj.comp hg).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ (fun r hr => ?_))
    have h0 := w_nonneg K hr
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, Complex.norm_conj, Pi.add_apply]
    nlinarith [mul_nonneg h0 (sq_nonneg (‖f r‖ - ‖g r‖)), norm_nonneg (f r), norm_nonneg (g r),
      mul_nonneg h0 (add_nonneg (sq_nonneg ‖f r‖) (sq_nonneg ‖g r‖))]

theorem sub_int {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc K.r₁ K.r₂)))
    (hfi : IntegrableOn (fun r => K.lineWeight r * ‖f r‖ ^ 2) (Set.Icc K.r₁ K.r₂)) (hg : Continuous g) :
    IntegrableOn (fun r => K.lineWeight r * ‖f r - g r‖ ^ 2) (Set.Icc K.r₁ K.r₂) := by
  have hgi := sq_int_cont K hg
  refine Integrable.mono' ((hfi.const_mul 2).add (hgi.const_mul 2)) ?_ ?_
  · exact (ResolvedEnergyInternal.lw_cont K).aestronglyMeasurable.mul ((hf.sub hg.aestronglyMeasurable).norm.pow 2)
  · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ (fun r hr => ?_))
    have h0 := w_nonneg K hr
    have h1 : ‖f r - g r‖ ≤ ‖f r‖ + ‖g r‖ := norm_sub_le _ _
    have h2 : ‖f r - g r‖ ^ 2 ≤ 2 * ‖f r‖ ^ 2 + 2 * ‖g r‖ ^ 2 := by
      nlinarith [norm_nonneg (f r - g r), norm_nonneg (f r), norm_nonneg (g r), sq_nonneg (‖f r‖ - ‖g r‖)]
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0, abs_pow, abs_norm, Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]

theorem pl_pair {d : ℕ} (e : Fin (d + 1) → ℂ) (t : Fin (d + 1)) :
    ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * pl e r * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))
      = Matrix.mulVec (pairingMat K d) e t := by
  have hc : ∀ j : Fin (d + 1), IntegrableOn (fun r : ℝ => (K.lineWeight r : ℂ) * (r : ℂ) ^ (j : ℕ)
      * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))) (Set.Icc K.r₁ K.r₂) := fun j =>
    (((wc_cont K).mul (pow_cont _)).mul (pow_conj_cont (t : ℕ))).integrableOn_Icc
  have e1 : (fun r : ℝ => (K.lineWeight r : ℂ) * pl e r * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)))
      = fun r => ∑ j, e j * ((K.lineWeight r : ℂ) * (r : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))) := by
    funext r
    unfold pl
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, integral_finsetSum _ (fun j _ => (hc j).const_mul (e j))]
  simp only [integral_const_mul, Matrix.mulVec, dotProduct, pairingMat]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem expand {d : ℕ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc K.r₁ K.r₂)))
    (hfi : IntegrableOn (fun r => K.lineWeight r * ‖f r‖ ^ 2) (Set.Icc K.r₁ K.r₂))
    (c : Fin (d + 1) → ℂ) (t : Fin (d + 1)) :
    ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * (f r - pl c r) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))
      = rhs K d f t - Matrix.mulVec (pairingMat K d) c t := by
  rw [← pl_pair K c t, rhs]
  have h1 := cross_int K hf hfi (pow_cont (t : ℕ))
  have h2 : IntegrableOn (fun r : ℝ => (K.lineWeight r : ℂ) * pl c r * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)))
      (Set.Icc K.r₁ K.r₂) :=
    (((wc_cont K).mul (pl_cont c)).mul (pow_conj_cont (t : ℕ))).integrableOn_Icc
  rw [← integral_sub h1 h2]
  congr 1
  funext r
  ring

theorem conj_pl {d : ℕ} (e : Fin (d + 1) → ℂ) (r : ℝ) :
    (starRingEnd ℂ) (pl e r) = ∑ t, (starRingEnd ℂ) (e t) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) := by
  unfold pl
  simp only [map_sum, map_mul]

theorem cross_zero {d : ℕ} {u : ℝ → ℂ}
    (hu : AEStronglyMeasurable u (volume.restrict (Set.Icc K.r₁ K.r₂)))
    (hui : IntegrableOn (fun r => K.lineWeight r * ‖u r‖ ^ 2) (Set.Icc K.r₁ K.r₂))
    (h0 : ∀ t : Fin (d + 1),
      ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * u r * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0)
    (e : Fin (d + 1) → ℂ) :
    ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * u r * (starRingEnd ℂ) (pl e r) = 0 := by
  have e1 : (fun r : ℝ => (K.lineWeight r : ℂ) * u r * (starRingEnd ℂ) (pl e r))
      = fun r => ∑ t, (starRingEnd ℂ) (e t) * ((K.lineWeight r : ℂ) * u r * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))) := by
    funext r
    rw [conj_pl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, integral_finsetSum _ (fun (t : Fin (d + 1)) _ =>
    (cross_int K hu hui (pow_cont (t : ℕ))).const_mul _)]
  simp only [integral_const_mul, h0, mul_zero, Finset.sum_const_zero]

theorem pl_sub {d : ℕ} (c c' : Fin (d + 1) → ℂ) (r : ℝ) : pl c r - pl c' r = pl (c - c') r := by
  unfold pl
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring

theorem min1 {d : ℕ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc K.r₁ K.r₂)))
    (hfi : IntegrableOn (fun r => K.lineWeight r * ‖f r‖ ^ 2) (Set.Icc K.r₁ K.r₂))
    {c : Fin (d + 1) → ℂ} (hc : Matrix.mulVec (pairingMat K d) c = rhs K d f) (c' : Fin (d + 1) → ℂ) :
    ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖f r - pl c r‖ ^ 2
      ≤ ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖f r - pl c' r‖ ^ 2 := by
  have hu : AEStronglyMeasurable (fun r => f r - pl c r) (volume.restrict (Set.Icc K.r₁ K.r₂)) :=
    hf.sub (pl_cont c).aestronglyMeasurable
  have hui := sub_int K hf hfi (pl_cont c)
  have h0 : ∀ t : Fin (d + 1), ∫ r in Set.Icc K.r₁ K.r₂,
      (K.lineWeight r : ℂ) * (f r - pl c r) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0 := by
    intro t
    rw [expand K hf hfi c t, hc, sub_self]
  have hz := cross_zero K hu hui h0 (c - c')
  have hvi := sq_int_cont K (pl_cont (c - c'))
  have hci := cross_int K hu hui (pl_cont (c - c'))
  have e : ∀ r, K.lineWeight r * ‖f r - pl c' r‖ ^ 2 = K.lineWeight r * ‖f r - pl c r‖ ^ 2
      + K.lineWeight r * ‖pl (c - c') r‖ ^ 2
      + 2 * RCLike.re ((K.lineWeight r : ℂ) * (f r - pl c r) * (starRingEnd ℂ) (pl (c - c') r)) := by
    intro r
    have h := Complex.normSq_add (f r - pl c r) (pl (c - c') r)
    rw [← pl_sub, sub_add_sub_cancel] at h
    rw [← pl_sub, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, h, mul_assoc, RCLike.re_to_complex,
      Complex.re_ofReal_mul]
    ring
  have hre : ∫ r in Set.Icc K.r₁ K.r₂,
      RCLike.re ((K.lineWeight r : ℂ) * (f r - pl c r) * (starRingEnd ℂ) (pl (c - c') r)) = 0 := by
    rw [integral_re hci, hz]
    simp
  have hA : IntegrableOn (fun r => K.lineWeight r * ‖f r - pl c r‖ ^ 2 + K.lineWeight r * ‖pl (c - c') r‖ ^ 2)
      (Set.Icc K.r₁ K.r₂) := hui.add hvi
  have hB : IntegrableOn (fun r => 2 * RCLike.re ((K.lineWeight r : ℂ) * (f r - pl c r)
      * (starRingEnd ℂ) (pl (c - c') r))) (Set.Icc K.r₁ K.r₂) := hci.re.const_mul 2
  simp only [e]
  rw [integral_add hA hB, integral_add hui hvi, integral_const_mul, hre]
  have hv0 : 0 ≤ ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖pl (c - c') r‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Icc (fun r hr => mul_nonneg (w_nonneg K hr) (sq_nonneg _))
  linarith

theorem pl_eq_zero_of (hK : IsCellBox K) {d : ℕ} {e : Fin (d + 1) → ℂ}
    (h : ∀ r ∈ Set.Ioo K.r₁ K.r₂, pl e r = 0) : e = 0 := by
  let P : Polynomial ℂ := ∑ j : Fin (d + 1), Polynomial.C (e j) * Polynomial.X ^ (j : ℕ)
  have hev : ∀ r : ℝ, P.eval (r : ℂ) = pl e r := by
    intro r
    simp [P, Polynomial.eval_finsetSum, pl]
  have hP : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    refine Set.Infinite.mono ?_ ((Set.Ioo_infinite hK.r_order.2).image Complex.ofReal_injective.injOn)
    rintro x ⟨r, hr, rfl⟩
    show P.eval (r : ℂ) = 0
    rw [hev, h r hr]
  funext t
  have hc : P.coeff (t : ℕ) = e t := by
    simp [P, Fin.val_inj]
  rw [← hc, hP]
  simp

theorem pairingMat_zero (hK : IsCellBox K) {d : ℕ} {e : Fin (d + 1) → ℂ} (h : Matrix.mulVec (pairingMat K d) e = 0) :
    e = 0 := by
  have hint : ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * pl e r * (starRingEnd ℂ) (pl e r) = 0 := by
    refine cross_zero K (pl_cont e).aestronglyMeasurable (sq_int_cont K (pl_cont e)) ?_ e
    intro t
    rw [pl_pair, h]
    rfl
  have hreal : ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖pl e r‖ ^ 2 = 0 := by
    have e1 : (fun r : ℝ => (K.lineWeight r : ℂ) * pl e r * (starRingEnd ℂ) (pl e r))
        = fun r => ((K.lineWeight r * ‖pl e r‖ ^ 2 : ℝ) : ℂ) := by
      funext r
      rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [e1, integral_complex_ofReal] at hint
    exact_mod_cast hint
  refine pl_eq_zero_of K hK (fun r₀ hr₀ => ?_)
  by_contra hne
  have hcont : Continuous (fun r => K.lineWeight r * ‖pl e r‖ ^ 2) :=
    (ResolvedEnergyInternal.lw_cont K).mul ((pl_cont e).norm.pow 2)
  have hpos : 0 < ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖pl e r‖ ^ 2 := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ (sq_int_cont K (pl_cont e))]
    · have hsub : Function.support (fun r => K.lineWeight r * ‖pl e r‖ ^ 2) ∩ Set.Ioo K.r₁ K.r₂
          ⊆ Function.support (fun r => K.lineWeight r * ‖pl e r‖ ^ 2) ∩ Set.Icc K.r₁ K.r₂ :=
        Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      refine IsOpen.measure_pos volume (hcont.isOpen_support.inter isOpen_Ioo) ⟨r₀, ?_, hr₀⟩
      have hw := w_pos K hr₀
      have hn : 0 < ‖pl e r₀‖ := norm_pos_iff.2 hne
      exact (mul_pos hw (pow_pos hn 2)).ne'
    · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ (fun r hr => ?_))
      exact mul_nonneg (w_nonneg K hr) (sq_nonneg _)
  linarith

theorem pairingMat_inj (hK : IsCellBox K) (d : ℕ) : Function.Injective (Matrix.mulVec (pairingMat K d)) := by
  intro a b hab
  have h : Matrix.mulVec (pairingMat K d) (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
  exact sub_eq_zero.mp (pairingMat_zero K hK h)

theorem pairingMat_sol (hK : IsCellBox K) (d : ℕ) (f : ℝ → ℂ) :
    Matrix.mulVec (pairingMat K d) (sol K d f) = rhs K d f := by
  have hu : IsUnit (pairingMat K d) := Matrix.mulVec_injective_iff_isUnit.mp (pairingMat_inj K hK d)
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  unfold sol
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

theorem projR_eq (hK : IsCellBox K) (d : ℕ) (s : ℝ × ℝ → ℂ) (z : ℝ)
    (hf : AEStronglyMeasurable (fun r => s (r, z)) (volume.restrict (Set.Icc K.r₁ K.r₂)))
    (hfi : IntegrableOn (fun r => K.lineWeight r * ‖s (r, z)‖ ^ 2) (Set.Icc K.r₁ K.r₂)) (r : ℝ) :
    K.projR d s (r, z) = pl (sol K d (fun r => s (r, z))) r := by
  have key : ∀ c : Fin (d + 1) → ℂ, (∀ t : Fin (d + 1), ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) *
      (s (r, z) - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0)
      ↔ Matrix.mulVec (pairingMat K d) c = rhs K d (fun r => s (r, z)) := by
    intro c
    have hx := expand K hf hfi c
    simp only [pl] at hx
    simp only [hx, sub_eq_zero]
    constructor
    · intro h
      funext t
      exact (h t).symm
    · intro h t
      rw [h]
  unfold CellBox.projR
  dsimp only
  split_ifs with hex
  · have h1 := (key _).1 hex.choose_spec
    have h2 : hex.choose = sol K d (fun r => s (r, z)) := pairingMat_inj K hK d (h1.trans (pairingMat_sol K hK d _).symm)
    rw [h2]
    rfl
  · exact absurd ⟨_, (key _).2 (pairingMat_sol K hK d _)⟩ hex

end RadialProjBoundInternal

open RadialProjBoundInternal in
theorem radialProjBound : RadialProjBoundStatement := by
  intro K hK Q _ s hsm hsi
  have hrect : volume.restrict K.rect
      = (volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rfl
  have hsm' : AEStronglyMeasurable s
      ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := hrect ▸ hsm
  have hsi' : Integrable (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖s p‖ ^ 2)
      ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    have h : Integrable (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖s p‖ ^ 2) (volume.restrict K.rect) := hsi
    rwa [hrect] at h
  have hgood : ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)),
      AEStronglyMeasurable (fun r => s (r, z)) (volume.restrict (Set.Icc K.r₁ K.r₂)) ∧
      IntegrableOn (fun r => K.lineWeight r * ‖s (r, z)‖ ^ 2) (Set.Icc K.r₁ K.r₂) := by
    filter_upwards [hsm'.prodMk_right, hsi'.prod_left_ae] with z h1 h2
    exact ⟨h1, h2⟩
  have hb : ∀ t : Fin (Q - 2 + 1), AEStronglyMeasurable (fun z => rhs K (Q - 2) (fun r => s (r, z)) t)
      (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    intro t
    have h : AEStronglyMeasurable (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * s p
        * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ)))
        ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) :=
      (((wc_cont K).comp continuous_fst).aestronglyMeasurable.mul hsm').mul
        ((pow_conj_cont (t : ℕ)).comp continuous_fst).aestronglyMeasurable
    exact h.prod_swap.integral_prod_right'
  have hc : ∀ j : Fin (Q - 2 + 1), AEStronglyMeasurable (fun z => sol K (Q - 2) (fun r => s (r, z)) j)
      (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
    intro j
    have e : (fun z => sol K (Q - 2) (fun r => s (r, z)) j)
        = fun z => ∑ t, (pairingMat K (Q - 2))⁻¹ j t * rhs K (Q - 2) (fun r => s (r, z)) t := by
      funext z
      rfl
    rw [e]
    exact Finset.aestronglyMeasurable_fun_sum _ fun t _ => (hb t).const_mul _
  have hg : AEStronglyMeasurable (fun p : ℝ × ℝ => K.lineWeight p.1
      * ‖s p - pl (sol K (Q - 2) (fun r => s (r, p.2))) p.1‖ ^ 2)
      ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    have hp : AEStronglyMeasurable (fun p : ℝ × ℝ => pl (sol K (Q - 2) (fun r => s (r, p.2))) p.1)
        ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
      unfold pl
      exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        (hc j).comp_snd.mul ((Complex.continuous_ofReal.comp continuous_fst).pow _).aestronglyMeasurable
    exact ((ResolvedEnergyInternal.lw_cont K).comp continuous_fst).aestronglyMeasurable.mul
      ((hsm'.sub hp).norm.pow 2)
  have hJ : AEStronglyMeasurable (fun z => ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r
      * ‖s (r, z) - pl (sol K (Q - 2) (fun r => s (r, z))) r‖ ^ 2) (volume.restrict (Set.Icc K.z₁ K.z₂)) :=
    hg.prod_swap.integral_prod_right'
  have heq : (fun z => ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r
      * ‖s (r, z) - pl (sol K (Q - 2) (fun r => s (r, z))) r‖ ^ 2)
      =ᵐ[volume.restrict (Set.Icc K.z₁ K.z₂)]
      (fun z => ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖s (r, z) - K.projR (Q - 2) s (r, z)‖ ^ 2) := by
    filter_upwards [hgood] with z hz
    congr 1
    funext r
    rw [projR_eq K hK (Q - 2) s z hz.1 hz.2 r]
  have hmeas := hJ.congr heq
  have hbound : Integrable (fun z => ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖s (r, z)‖ ^ 2)
      (volume.restrict (Set.Icc K.z₁ K.z₂)) := hsi'.integral_prod_right
  have hle0 : ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)),
      ‖∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖s (r, z) - K.projR (Q - 2) s (r, z)‖ ^ 2‖
        ≤ ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖s (r, z)‖ ^ 2 := by
    filter_upwards [hgood] with z hz
    have hnn : 0 ≤ ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖s (r, z) - K.projR (Q - 2) s (r, z)‖ ^ 2 :=
      setIntegral_nonneg measurableSet_Icc (fun r hr => mul_nonneg (w_nonneg K hr) (sq_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hm := min1 K hz.1 hz.2 (pairingMat_sol K hK (Q - 2) (fun r => s (r, z))) 0
    have h0 : ∀ r, pl (0 : Fin (Q - 2 + 1) → ℂ) r = 0 := fun r => by simp [pl]
    simp only [h0, sub_zero] at hm
    simp only [projR_eq K hK (Q - 2) s z hz.1 hz.2]
    exact hm
  refine ⟨Integrable.mono' hbound hmeas hle0, ?_⟩
  obtain ⟨cc, hcc⟩ := ResolvedEnergyInternal.proj_mem K (Q - 2) Q s
  have hP' : ∀ r z, K.proj (Q - 2) Q s (r, z) = pl (fun j => ∑ l, cc j l * (z : ℂ) ^ (l : ℕ)) r := by
    intro r z
    rw [hcc]
    unfold pl
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hm : ∀ p ∈ K.rect, 0 ≤ K.lineWeightFn p := fun p hp => w_nonneg K hp.1
  have hmm : AEStronglyMeasurable K.lineWeightFn (volume.restrict K.rect) :=
    ((ResolvedEnergyInternal.lw_cont K).comp continuous_fst).aestronglyMeasurable
  have hmc : ContinuousOn K.lineWeightFn K.rect :=
    ((ResolvedEnergyInternal.lw_cont K).comp continuous_fst).continuousOn
  have hPQ := ResolvedEnergyInternal.cont_integrable K hmc
    (ResolvedEnergyInternal.poly_cont (ResolvedEnergyInternal.proj_mem K Q Q s))
  have hPd := ResolvedEnergyInternal.cont_integrable K hmc
    (ResolvedEnergyInternal.poly_cont (ResolvedEnergyInternal.proj_mem K (Q - 2) Q s))
  have o1 := ResolvedEnergyInternal.orth_split K hm hmm hsm hPQ.1 hsi hPQ.2
    (ResolvedEnergyInternal.proj_orth K Q Q s)
  have o2 := ResolvedEnergyInternal.orth_split K hm hmm hsm hPd.1 hsi hPd.2
    (ResolvedEnergyInternal.proj_orth K (Q - 2) Q s)
  have hdi := ResolvedEnergyInternal.sub_sq_integrable K hm hmm hsm hPd.1 hsi hPd.2
  have hdi' : Integrable (fun p : ℝ × ℝ => K.lineWeightFn p * ‖s p - K.proj (Q - 2) Q s p‖ ^ 2)
      ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    have h : Integrable (fun p : ℝ × ℝ => K.lineWeightFn p * ‖s p - K.proj (Q - 2) Q s p‖ ^ 2)
        (volume.restrict K.rect) := hdi
    rwa [hrect] at h
  have hfull : K.normSqOn K.lineWeightFn (fun p => s p - K.proj (Q - 2) Q s p)
      = ∫ z in Set.Icc K.z₁ K.z₂, ∫ r in Set.Icc K.r₁ K.r₂,
          K.lineWeight r * ‖s (r, z) - K.proj (Q - 2) Q s (r, z)‖ ^ 2 := by
    unfold CellBox.normSqOn
    rw [hrect, integral_prod_symm _ hdi']
    rfl
  have hmono : ∫ z in Set.Icc K.z₁ K.z₂, ∫ r in Set.Icc K.r₁ K.r₂,
        K.lineWeight r * ‖s (r, z) - K.projR (Q - 2) s (r, z)‖ ^ 2
      ≤ ∫ z in Set.Icc K.z₁ K.z₂, ∫ r in Set.Icc K.r₁ K.r₂,
        K.lineWeight r * ‖s (r, z) - K.proj (Q - 2) Q s (r, z)‖ ^ 2 := by
    refine integral_mono_ae (Integrable.mono' hbound hmeas hle0) hdi'.integral_prod_right ?_
    filter_upwards [hgood] with z hz
    simp only [projR_eq K hK (Q - 2) s z hz.1 hz.2, hP']
    exact min1 K hz.1 hz.2 (pairingMat_sol K hK (Q - 2) (fun r => s (r, z))) _
  unfold CellBox.tailNormSq
  linarith

end CellAnalysis

end CellCert

end Breakdown
