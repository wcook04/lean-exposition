import Breakdown.CertCell.AssemblyRowParts

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open Coupling CellCert.CellAnalysis CellCert.CellFormula CellCalculus

theorem two_re_mul_conj_sub_le (f u : ℂ) : 2 * (f * (starRingEnd ℂ) u).re - ‖u‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := Complex.normSq_nonneg (f - u)
  rw [Complex.normSq_sub] at h
  rw [Complex.sq_norm, Complex.sq_norm]
  linarith

theorem integrable_weight_mul_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {w : X → ℝ}
    {a b : X → ℂ} (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hwm : AEStronglyMeasurable w μ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hai : Integrable (fun x => w x * ‖a x‖ ^ 2) μ) (hbi : Integrable (fun x => w x * ‖b x‖ ^ 2) μ) :
    Integrable (fun x => (w x : ℂ) * (a x * (starRingEnd ℂ) (b x))) μ := by
  refine Integrable.mono' ((hai.add hbi).div_const 2) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hwm).mul
      (ha.mul (Complex.continuous_conj.comp_aestronglyMeasurable hb))
  · filter_upwards [hw] with x hx
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hx]
    have h1 : 0 ≤ (‖a x‖ - ‖b x‖) ^ 2 := sq_nonneg _
    have h2 : w x * (‖a x‖ * ‖b x‖) ≤ w x * ((‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hx
    simp only [Pi.add_apply]
    linarith


theorem sum_fiber_ite {n κ : Type*} [Fintype n] [DecidableEq κ] (L : n → κ) (T : Finset κ) (hL : ∀ i, L i ∈ T)
    (F : κ → n → ℂ) : ∑ ℓ ∈ T, ∑ i, (if L i = ℓ then F ℓ i else 0) = ∑ i, F (L i) i := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_ite_eq T (L i) (fun ℓ => F ℓ i), if_pos (hL i)]

theorem quadForm_inv_le_of_tests {X : Type*} [MeasurableSpace X] {μ : Measure X} {n κ : Type*} [Fintype n]
    [DecidableEq n] [DecidableEq κ] {m : ℕ} (L : n → κ) (T : Finset κ) (hL : ∀ i, L i ∈ T)
    (w : X → ℝ) (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hwm : AEStronglyMeasurable w μ)
    (φ : n → X → Fin m → ℂ) (f : κ → X → Fin m → ℂ)
    (hφ : ∀ i c, AEStronglyMeasurable (fun x => φ i x c) μ) (hf : ∀ ℓ ∈ T, ∀ c, AEStronglyMeasurable (fun x => f ℓ x c) μ)
    (hφi : ∀ i c, Integrable (fun x => w x * ‖φ i x c‖ ^ 2) μ)
    (hfi : ∀ ℓ ∈ T, ∀ c, Integrable (fun x => w x * ‖f ℓ x c‖ ^ 2) μ)
    (G : Matrix n n ℂ)
    (hG : ∀ i i', G i i' = if L i = L i' then
      ∫ x, (w x : ℂ) * ∑ c, φ i' x c * (starRingEnd ℂ) (φ i x c) ∂μ else 0)
    (hpos : G.PosDef) (t : n → ℂ)
    (ht : ∀ i, t i = ∫ x, (w x : ℂ) * ∑ c, f (L i) x c * (starRingEnd ℂ) (φ i x c) ∂μ) :
    quadForm G⁻¹ t ≤ ∑ ℓ ∈ T, ∫ x, w x * ∑ c, ‖f ℓ x c‖ ^ 2 ∂μ := by
  classical
  set c : n → ℂ := G⁻¹ *ᵥ t with hc
  have hunit : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hpos.isUnit
  have hGc : G *ᵥ c = t := by
    rw [hc, mulVec_mulVec, mul_nonsing_inv G hunit, one_mulVec]
  have hherm : Gᴴ = G := hpos.isHermitian
  have hq1 : quadForm G⁻¹ t = (star c ⬝ᵥ (G *ᵥ c)).re := by
    unfold quadForm
    rw [← hc]
    congr 1
    conv_lhs => rw [← hGc]
    rw [star_mulVec, hherm, ← dotProduct_mulVec]
  have hq2 : quadForm G⁻¹ t = 2 * (star c ⬝ᵥ t).re - (star c ⬝ᵥ (G *ᵥ c)).re := by
    rw [hq1, hGc]; ring
  set u : κ → X → Fin m → ℂ := fun ℓ x a => ∑ i, if L i = ℓ then c i * φ i x a else 0 with hu
  have hintA : ∀ i a, Integrable (fun x => (w x : ℂ) * (f (L i) x a * (starRingEnd ℂ) (φ i x a))) μ :=
    fun i a => integrable_weight_mul_conj hw hwm (hf _ (hL i) a) (hφ i a) (hfi _ (hL i) a) (hφi i a)
  have hintB : ∀ i i' a, Integrable (fun x => (w x : ℂ) * (φ i' x a * (starRingEnd ℂ) (φ i x a))) μ :=
    fun i i' a => integrable_weight_mul_conj hw hwm (hφ i' a) (hφ i a) (hφi i' a) (hφi i a)
  have I1 : star c ⬝ᵥ t = ∫ x, ∑ i, ∑ a, (starRingEnd ℂ) (c i) *
      ((w x : ℂ) * (f (L i) x a * (starRingEnd ℂ) (φ i x a))) ∂μ := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => (hintA i a).const_mul _))]
    unfold dotProduct
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun a _ => (hintA i a).const_mul _), ht i, Pi.star_apply, RCLike.star_def,
      ← integral_const_mul]
    rw [← integral_finsetSum _ (fun a _ => (hintA i a).const_mul _)]
    congr 1
    funext x
    rw [Finset.mul_sum, Finset.mul_sum]
  have I2 : star c ⬝ᵥ (G *ᵥ c) = ∫ x, ∑ i, ∑ i', ∑ a, (if L i = L i' then (starRingEnd ℂ) (c i) * c i' else 0) *
      ((w x : ℂ) * (φ i' x a * (starRingEnd ℂ) (φ i x a))) ∂μ := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun i' _ =>
      integrable_finsetSum _ (fun a _ => (hintB i i' a).const_mul _)))]
    unfold dotProduct mulVec dotProduct
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun i' _ => integrable_finsetSum _ (fun a _ => (hintB i i' a).const_mul _)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    show (star c) i * (G i i' * c i') = _
    rw [integral_finsetSum _ (fun a _ => (hintB i i' a).const_mul _), hG i i']
    by_cases h : L i = L i'
    · simp only [h, if_true, Pi.star_apply, RCLike.star_def]
      rw [show ∀ A : ℂ, (starRingEnd ℂ) (c i) * (A * c i') = ((starRingEnd ℂ) (c i) * c i') * A from
        fun A => by ring]
      rw [← integral_const_mul, ← integral_finsetSum _ (fun a _ => (hintB i i' a).const_mul _)]
      congr 1
      funext x
      rw [Finset.mul_sum, Finset.mul_sum]
    · simp [h]
  have P1 : ∀ x, (∑ i, ∑ a, (starRingEnd ℂ) (c i) * ((w x : ℂ) * (f (L i) x a * (starRingEnd ℂ) (φ i x a))))
      = ∑ ℓ ∈ T, (w x : ℂ) * ∑ a, f ℓ x a * (starRingEnd ℂ) (u ℓ x a) := by
    intro x
    rw [← sum_fiber_ite L T hL (fun ℓ i => ∑ a, (starRingEnd ℂ) (c i) * ((w x : ℂ) * (f ℓ x a * (starRingEnd ℂ) (φ i x a))))]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    simp only [hu, map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : L i = ℓ
    · simp only [h, if_true, map_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      ring
    · simp [h]
  have P2 : ∀ x, (∑ i, ∑ i', ∑ a, (if L i = L i' then (starRingEnd ℂ) (c i) * c i' else 0) *
      ((w x : ℂ) * (φ i' x a * (starRingEnd ℂ) (φ i x a))))
      = ∑ ℓ ∈ T, (w x : ℂ) * ∑ a, u ℓ x a * (starRingEnd ℂ) (u ℓ x a) := by
    intro x
    rw [← sum_fiber_ite L T hL (fun ℓ i => ∑ i', ∑ a, (if ℓ = L i' then (starRingEnd ℂ) (c i) * c i' else 0) *
      ((w x : ℂ) * (φ i' x a * (starRingEnd ℂ) (φ i x a))))]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    let F : n → n → Fin m → ℂ := fun i i' a => if L i = ℓ ∧ L i' = ℓ then
      (w x : ℂ) * (c i' * φ i' x a * ((starRingEnd ℂ) (c i) * (starRingEnd ℂ) (φ i x a))) else 0
    calc _ = ∑ i, ∑ i', ∑ a, F i i' a := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases h : L i = ℓ
          · rw [if_pos h]
            refine Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun a _ => ?_))
            by_cases h' : L i' = ℓ
            · have h'' : ℓ = L i' := h'.symm
              simp only [F]
              rw [if_pos (show L i = ℓ ∧ L i' = ℓ from ⟨h, h'⟩)]
              try rw [if_pos h'']
              ring
            · have h'' : ¬ ℓ = L i' := fun e => h' e.symm
              simp only [F, h', and_false, if_false, h'', zero_mul]
          · simp only [F, h, false_and, if_false, Finset.sum_const_zero]
      _ = ∑ a, ∑ i', ∑ i, F i i' a := by
          rw [Finset.sum_comm]
          conv_lhs => enter [2, i']; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          simp only [hu, map_sum]
          rw [Finset.sum_mul_sum]
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun i _ => ?_))
          by_cases h : L i = ℓ <;> by_cases h' : L i' = ℓ <;> simp [F, h, h']
  have hg1 : Integrable (fun x => ∑ ℓ ∈ T, (w x : ℂ) * ∑ a, f ℓ x a * (starRingEnd ℂ) (u ℓ x a)) μ := by
    refine (integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun a _ => (hintA i a).const_mul ((starRingEnd ℂ) (c i))))).congr ?_
    exact Filter.Eventually.of_forall P1
  have hg2 : Integrable (fun x => ∑ ℓ ∈ T, (w x : ℂ) * ∑ a, u ℓ x a * (starRingEnd ℂ) (u ℓ x a)) μ := by
    refine (integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun i' _ =>
      integrable_finsetSum Finset.univ (fun a _ => (hintB i i' a).const_mul
        (if L i = L i' then (starRingEnd ℂ) (c i) * c i' else 0))))).congr ?_
    exact Filter.Eventually.of_forall P2
  have hR : ∀ ℓ ∈ T, Integrable (fun x => w x * ∑ a, ‖f ℓ x a‖ ^ 2) μ := by
    intro ℓ hℓ
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun a _ => hfi ℓ hℓ a)
  have E1 : (star c ⬝ᵥ t).re = ∫ x, (∑ ℓ ∈ T, (w x : ℂ) * ∑ a, f ℓ x a * (starRingEnd ℂ) (u ℓ x a)).re ∂μ := by
    rw [I1, integral_congr_ae (Filter.Eventually.of_forall P1)]
    exact (integral_re hg1).symm
  have E2 : (star c ⬝ᵥ (G *ᵥ c)).re = ∫ x, (∑ ℓ ∈ T, (w x : ℂ) * ∑ a, u ℓ x a * (starRingEnd ℂ) (u ℓ x a)).re ∂μ := by
    rw [I2, integral_congr_ae (Filter.Eventually.of_forall P2)]
    exact (integral_re hg2).symm
  have h1r : Integrable (fun x => 2 * (∑ ℓ ∈ T, (w x : ℂ) * ∑ a, f ℓ x a * (starRingEnd ℂ) (u ℓ x a)).re) μ :=
    hg1.re.const_mul 2
  have h2r : Integrable (fun x => (∑ ℓ ∈ T, (w x : ℂ) * ∑ a, u ℓ x a * (starRingEnd ℂ) (u ℓ x a)).re) μ := hg2.re
  rw [hq2, E1, E2, ← integral_const_mul, ← integral_sub h1r h2r, ← integral_finsetSum _ hR]
  refine integral_mono_ae (h1r.sub h2r) (integrable_finsetSum _ hR) ?_
  filter_upwards [hw] with x hx
  simp only [Complex.re_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun ℓ _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun a _ => ?_)
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.mul_conj, Complex.ofReal_re, ← Complex.sq_norm]
  have h := mul_le_mul_of_nonneg_left (two_re_mul_conj_sub_le (f ℓ x a) (u ℓ x a)) hx
  linarith


theorem cellPoly_eval_continuous (K : CellBox) (P : CellPoly) : Continuous (fun p : ℝ × ℝ => P.eval K p) := by
  unfold CellPoly.eval CellBox.refR CellBox.refZ
  fun_prop

theorem rect_isCompact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem rect_first_nonneg {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ p.1 :=
  le_trans hK.r_order.1 hp.1.1

theorem integrableOn_rect_of_continuous {K : CellBox} {g : ℝ × ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn g K.rect :=
  hg.continuousOn.integrableOn_compact (rect_isCompact K)

theorem rect_measurableSet (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem ae_rect_first_nonneg {K : CellBox} (hK : IsCellBox K) : ∀ᵐ p ∂(volume.restrict K.rect), 0 ≤ p.1 :=
  ae_restrict_of_forall_mem (rect_measurableSet K) (fun _ hp => rect_first_nonneg hK hp)

section Rows

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem rowTestValue_continuous {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (i : Fin B.rowCount) (a : Fin 3) :
    Continuous (fun p => rowTestValue D K B i p a) :=
  cellPoly_eval_continuous _ _

theorem inverseWeightedSq_rows_le (A : AssemblyEntry D R) (hC : RowConditions D R A) (K : Fin D.mesh.count)
    (f : ℤ × ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (hfm : ∀ ℓ ∈ D.mesh.tested K, ∀ a, AEStronglyMeasurable (fun p => f ℓ p a) (volume.restrict (D.mesh.box K).rect))
    (hfi : ∀ ℓ ∈ D.mesh.tested K, ∀ a, IntegrableOn (fun p => p.1 * ‖f ℓ p a‖ ^ 2) (D.mesh.box K).rect)
    (t : Fin (A.blocks K).rowCount → ℂ)
    (ht : ∀ i, t i = ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
      ∑ a, f ((A.blocks K).rowLabel i) p a * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p a)) :
    inverseWeightedSq (rowGram D K (A.blocks K)) t
      ≤ ∑ ℓ ∈ D.mesh.tested K, ∫ p in (D.mesh.box K).rect, p.1 * ∑ a, ‖f ℓ p a‖ ^ 2 := by
  classical
  have hK : IsCellBox (D.mesh.box K) := hC.mesh_valid.box_valid K
  unfold inverseWeightedSq
  refine quadForm_inv_le_of_tests (A.blocks K).rowLabel (D.mesh.tested K) (hC.label_tested K) (fun p : ℝ × ℝ => p.1)
    (ae_rect_first_nonneg hK) continuous_fst.aestronglyMeasurable
    (fun i p a => rowTestValue D K (A.blocks K) i p a) f
    (fun i a => (rowTestValue_continuous D K (A.blocks K) i a).aestronglyMeasurable) hfm
    (fun i a => integrableOn_rect_of_continuous
      (continuous_fst.mul ((rowTestValue_continuous D K (A.blocks K) i a).norm.pow 2)))
    hfi _ ?_ (hC.gram_pos K) t ht
  intro i i'
  unfold rowGram
  split_ifs with h
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [rowTestValue, rowTestPoly, testAt, h]
  · rfl

theorem norm_sub_sq_le_two (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  have h2 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem curlComp_eq (s : Fin 3 → Fin 3 → ℂ) :
    curlComp s 0 = s 2 1 - s 1 2 ∧ curlComp s 1 = s 0 2 - s 2 0 ∧ curlComp s 2 = s 1 0 - s 0 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [curlComp, Fin.sum_univ_three, CellCert.permSign] <;> ring

theorem curlSq_le_sumSq (s : Fin 3 → Fin 3 → ℂ) : curlSq s ≤ 2 * sumSq s := by
  obtain ⟨h0, h1, h2⟩ := curlComp_eq s
  unfold curlSq sumSq
  simp only [Fin.sum_univ_three]
  rw [h0, h1, h2]
  nlinarith [norm_sub_sq_le_two (s 2 1) (s 1 2), norm_sub_sq_le_two (s 0 2) (s 2 0),
    norm_sub_sq_le_two (s 1 0) (s 0 1), sq_nonneg ‖s 0 0‖, sq_nonneg ‖s 1 1‖, sq_nonneg ‖s 2 2‖]

theorem sum_pairVec_sq (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    ∑ j, ‖pairVec s w j‖ ^ 2 = sumSq s + vecSq w := by
  simp [Fin.sum_univ_succ, pairVec, sumSq, vecSq]
  ring

theorem velAt_eq_bandProfile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (a : Fin 3) (p : ℝ × ℝ) : velAt D.azimuthOrder ι v a p = bandProfile D ι v G p ⟨9 + a.val, by omega⟩ := by
  unfold bandProfile pairVec
  rw [dif_neg (by show ¬ (9 + a.val < 9); omega)]
  unfold velArray
  congr 1
  ext
  simp only
  omega

theorem gradAt_eq_bandProfile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (a b : Fin 3) (p : ℝ × ℝ) :
    gradAt D.azimuthOrder ι G a b p = bandProfile D ι v G p ⟨3 * a.val + b.val, by omega⟩ := by
  unfold bandProfile pairVec
  rw [dif_pos (by show 3 * a.val + b.val < 9; omega)]
  unfold gradArray
  congr 1
  · ext; simp only; omega
  · ext; simp only; omega

theorem profile_facts (hTF : TrueFieldRegular D) {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} {κ : Fin k → ℝ} {F Pg : ℝ → Space → Space}
    (ht : IsCellTuple D K q v G H g κ F Pg) (ι : ℤ × ℤ) :
    (∀ a, AEStronglyMeasurable (fun p => velAt D.azimuthOrder ι v a p) (volume.restrict (D.mesh.box K).rect)) ∧
    (∀ a b, AEStronglyMeasurable (fun p => gradAt D.azimuthOrder ι G a b p) (volume.restrict (D.mesh.box K).rect)) ∧
    IntegrableOn (fun p => p.1 * (sumSq (gradArray D.azimuthOrder ι G p) + vecSq (velArray D.azimuthOrder ι v p)))
      (D.mesh.box K).rect := by
  obtain ⟨hm, hi⟩ := (hTF.1 K q v G H g κ F Pg ht).1 ι
  refine ⟨fun a => ?_, fun a b => ?_, ?_⟩
  · simp only [velAt_eq_bandProfile D ι v G]
    exact hm _
  · simp only [gradAt_eq_bandProfile D ι v G]
    exact hm _
  · refine hi.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [bandProfile, sum_pairVec_sq]

theorem integrableOn_of_le_weighted {K : CellBox} (hK : IsCellBox K) {X Y : ℝ × ℝ → ℝ} {c : ℝ}
    (hY : IntegrableOn (fun p => p.1 * Y p) K.rect) (hX : AEStronglyMeasurable X (volume.restrict K.rect))
    (hle : ∀ p, 0 ≤ X p ∧ X p ≤ c * Y p) : IntegrableOn (fun p => p.1 * X p) K.rect := by
  refine Integrable.mono' (hY.const_mul c) (continuous_fst.aestronglyMeasurable.mul hX) ?_
  filter_upwards [ae_rect_first_nonneg hK] with p hp
  rw [Real.norm_of_nonneg (mul_nonneg hp (hle p).1)]
  have := mul_le_mul_of_nonneg_left (hle p).2 hp
  linarith

theorem profile_integrable (hTF : TrueFieldRegular D) {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K))
    {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} {κ : Fin k → ℝ} {F Pg : ℝ → Space → Space}
    (ht : IsCellTuple D K q v G H g κ F Pg) (ι : ℤ × ℤ) :
    IntegrableOn (fun p => p.1 * modeVelSq D ι v p) (D.mesh.box K).rect ∧
    IntegrableOn (fun p => p.1 * modeCurlSq D ι G p) (D.mesh.box K).rect ∧
    ∀ a, IntegrableOn (fun p => p.1 * ‖velAt D.azimuthOrder ι v a p‖ ^ 2) (D.mesh.box K).rect := by
  obtain ⟨hv, hg, hi⟩ := profile_facts D hTF ht ι
  have hvs : ∀ p, 0 ≤ vecSq (velArray D.azimuthOrder ι v p) := fun p => by unfold vecSq; positivity
  have hss : ∀ p, 0 ≤ sumSq (gradArray D.azimuthOrder ι G p) := fun p => by unfold sumSq; positivity
  refine ⟨?_, ?_, fun a => ?_⟩
  · refine integrableOn_of_le_weighted (c := 1) hK hi (by unfold modeVelSq; fun_prop) (fun p => ⟨?_, ?_⟩)
    · unfold modeVelSq; positivity
    · have : modeVelSq D ι v p = vecSq (velArray D.azimuthOrder ι v p) := rfl
      rw [this]; linarith [hss p]
  · have hc : ∀ i, AEStronglyMeasurable (fun p => curlComp (gradArray D.azimuthOrder ι G p) i)
        (volume.restrict (D.mesh.box K).rect) := by
      intro i
      unfold curlComp gradArray
      fun_prop
    refine integrableOn_of_le_weighted (c := 2) hK hi (by unfold modeCurlSq; fun_prop) (fun p => ⟨?_, ?_⟩)
    · unfold modeCurlSq; positivity
    · have h1 : modeCurlSq D ι G p = curlSq (gradArray D.azimuthOrder ι G p) := rfl
      rw [h1]; linarith [curlSq_le_sumSq (gradArray D.azimuthOrder ι G p), hvs p]
  · refine integrableOn_of_le_weighted (c := 1) hK hi ((hv a).norm.pow 2) (fun p => ⟨by positivity, ?_⟩)
    have : ‖velAt D.azimuthOrder ι v a p‖ ^ 2 ≤ vecSq (velArray D.azimuthOrder ι v p) := by
      unfold vecSq
      exact Finset.single_le_sum (f := fun b => ‖velArray D.azimuthOrder ι v p b‖ ^ 2)
        (fun b _ => by positivity) (Finset.mem_univ a)
    linarith [hss p]

theorem sumSq_integrable (hTF : TrueFieldRegular D) {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K))
    {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} {κ : Fin k → ℝ} {F Pg : ℝ → Space → Space}
    (ht : IsCellTuple D K q v G H g κ F Pg) (ι : ℤ × ℤ) :
    IntegrableOn (fun p => p.1 * sumSq (gradArray D.azimuthOrder ι G p)) (D.mesh.box K).rect := by
  obtain ⟨_, hg, hi⟩ := profile_facts D hTF ht ι
  refine integrableOn_of_le_weighted (c := 1) hK hi (by unfold sumSq gradArray; fun_prop)
    (fun p => ⟨by unfold sumSq; positivity, ?_⟩)
  have : 0 ≤ vecSq (velArray D.azimuthOrder ι v p) := by unfold vecSq; positivity
  linarith

theorem weighted_integral_nonneg {K : CellBox} (hK : IsCellBox K) {X : ℝ × ℝ → ℝ} (hX : ∀ p, 0 ≤ X p) :
    0 ≤ ∫ p in K.rect, p.1 * X p := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_rect_first_nonneg hK] with p hp
  exact mul_nonneg hp (hX p)

theorem weighted_three_le {K : CellBox} (hK : IsCellBox K) {X Y Z : ℝ × ℝ → ℝ}
    (hXi : IntegrableOn (fun p => p.1 * X p) K.rect) (hYi : IntegrableOn (fun p => p.1 * Y p) K.rect)
    (hZi : IntegrableOn (fun p => p.1 * Z p) K.rect)
    (hX : ∀ p, 0 ≤ X p) (hY : ∀ p, 0 ≤ Y p) (hZ : ∀ p, 0 ≤ Z p) {a c a' b' c' : ℝ}
    (ha : a ≤ a') (hb : 0 ≤ b') (hc : c ≤ c') :
    a * (∫ p in K.rect, p.1 * X p) + c * (∫ p in K.rect, p.1 * Z p)
      ≤ ∫ p in K.rect, p.1 * (a' * X p + b' * Y p + c' * Z p) := by
  have e : (fun p : ℝ × ℝ => p.1 * (a' * X p + b' * Y p + c' * Z p))
      = fun p => a' * (p.1 * X p) + b' * (p.1 * Y p) + c' * (p.1 * Z p) := by
    funext p; ring
  have i1 : IntegrableOn (fun p : ℝ × ℝ => a' * (p.1 * X p) + b' * (p.1 * Y p)) K.rect :=
    (hXi.const_mul a').add (hYi.const_mul b')
  rw [e, integral_add (f := fun p : ℝ × ℝ => a' * (p.1 * X p) + b' * (p.1 * Y p))
    (g := fun p : ℝ × ℝ => c' * (p.1 * Z p)) i1 (hZi.const_mul c'),
    integral_add (f := fun p : ℝ × ℝ => a' * (p.1 * X p)) (g := fun p : ℝ × ℝ => b' * (p.1 * Y p))
      (hXi.const_mul a') (hYi.const_mul b'), integral_const_mul, integral_const_mul, integral_const_mul]
  have h1 := weighted_integral_nonneg hK hX
  have h2 := weighted_integral_nonneg hK hY
  have h3 := weighted_integral_nonneg hK hZ
  nlinarith [mul_le_mul_of_nonneg_right ha h1, mul_le_mul_of_nonneg_right hc h3, mul_nonneg hb h2]

theorem weighted_two_eq {K : CellBox} {X Z : ℝ × ℝ → ℝ}
    (hXi : IntegrableOn (fun p => p.1 * X p) K.rect) (hZi : IntegrableOn (fun p => p.1 * Z p) K.rect) (c e1 e2 : ℝ) :
    c * ∫ p in K.rect, p.1 * (e1 * X p + e2 * Z p)
      = (c * e1) * (∫ p in K.rect, p.1 * X p) + (c * e2) * (∫ p in K.rect, p.1 * Z p) := by
  have e : (fun p : ℝ × ℝ => p.1 * (e1 * X p + e2 * Z p)) = fun p => e1 * (p.1 * X p) + e2 * (p.1 * Z p) := by
    funext p; ring
  rw [e, integral_add (f := fun p : ℝ × ℝ => e1 * (p.1 * X p)) (g := fun p : ℝ × ℝ => e2 * (p.1 * Z p))
    (hXi.const_mul e1) (hZi.const_mul e2), integral_const_mul, integral_const_mul]
  ring

theorem weighted_two_le {K : CellBox} (hK : IsCellBox K) {X Z : ℝ × ℝ → ℝ}
    (hXi : IntegrableOn (fun p => p.1 * X p) K.rect) (hZi : IntegrableOn (fun p => p.1 * Z p) K.rect)
    (hX : ∀ p, 0 ≤ X p) (hZ : ∀ p, 0 ≤ Z p) {a c a' c' : ℝ} (ha : a ≤ a') (hc : c ≤ c') :
    a * (∫ p in K.rect, p.1 * X p) + c * (∫ p in K.rect, p.1 * Z p)
      ≤ ∫ p in K.rect, p.1 * (a' * X p + c' * Z p) := by
  have h := weighted_two_eq hXi hZi 1 a' c'
  rw [one_mul, one_mul, one_mul] at h
  rw [h]
  have h1 := weighted_integral_nonneg hK hX
  have h3 := weighted_integral_nonneg hK hZ
  nlinarith [mul_le_mul_of_nonneg_right ha h1, mul_le_mul_of_nonneg_right hc h3]

end Rows

end Internal

end Assembly

end CertCell

end Breakdown
