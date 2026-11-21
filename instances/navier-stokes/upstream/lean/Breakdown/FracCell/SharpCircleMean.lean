import Breakdown.FracCell.SharpCircleBound
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.RelTrace
import Breakdown.FracCell.FormulaYLinear

open MeasureTheory

noncomputable section

namespace Breakdown.FracInternal.SharpCircleMean

open Breakdown.CellCert Breakdown.CellCert.CellAnalysis SteadyCert Assembly
open Breakdown.CellCert.CellFormula.Internal.RelTrace
open Breakdown.CellCert.CellEnergy.Internal.CircleWeak
open Breakdown.CellCert.CellFormula.FormulaYLinearInternal

theorem couple_identity (G : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (htr : ∑ a : Fin 3, G a a = 0) :
    ∑ i : Fin 3, ∑ l : Fin 3, couplingMap G v i l * (starRingEnd ℂ) (couplingMap G v i l)
      = 2 * ∑ j : Fin 3, matVec G v j * (starRingEnd ℂ) (matVec G v j)
        + (1 / 4 : ℂ) * ∑ i : Fin 3, ∑ l : Fin 3, matVec G (fun q => bracketMat v i q) l
            * (starRingEnd ℂ) (matVec G (fun q => bracketMat v i q) l)
        + (1 / 2 : ℂ) * (∑ l : Fin 3, v l * matVec G (fun j => (starRingEnd ℂ) (matVec G v j)) l
          + (starRingEnd ℂ) (∑ l : Fin 3, v l * matVec G (fun j => (starRingEnd ℂ) (matVec G v j)) l)) := by
  have h22 : G 2 2 = -G 0 0 - G 1 1 := by
    rw [Fin.sum_univ_three] at htr; linear_combination htr
  simp only [couplingMap, bracketMat, matVec, Fin.sum_univ_three, map_add, map_mul, map_neg,
    map_div₀, map_one, map_ofNat, Complex.conj_ofReal]
  simp [CellCert.permSign]
  rw [h22]
  simp only [map_sub, map_neg]
  ring

theorem norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem vecSq_eq (v : Fin 3 → ℂ) : vecSq v = (∑ a : Fin 3, v a * (starRingEnd ℂ) (v a)).re := by
  unfold vecSq
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ => norm_sq_eq (v a)

theorem sumSq_eq (s : Fin 3 → Fin 3 → ℂ) :
    sumSq s = (∑ a : Fin 3, ∑ b : Fin 3, s a b * (starRingEnd ℂ) (s a b)).re := by
  unfold sumSq
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun b _ => norm_sq_eq _

theorem real_identity (G : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (htr : ∑ a : Fin 3, G a a = 0) :
    sumSq (couplingMap G v) = 2 * vecSq (matVec G v)
      + (1 / 4) * ∑ i : Fin 3, vecSq (matVec G (fun q => bracketMat v i q))
      + (∑ l : Fin 3, v l * matVec G (fun j => (starRingEnd ℂ) (matVec G v j)) l).re := by
  rw [sumSq_eq, couple_identity G v htr, vecSq_eq]
  simp only [vecSq_eq, Complex.add_re, Complex.re_sum]
  simp only [Complex.mul_re, Complex.re_sum, Complex.im_sum, Complex.add_re, Complex.add_im, Complex.conj_re,
    Complex.conj_im]
  norm_num
  ring

theorem bracket_sq (v : Fin 3 → ℂ) : ∑ i : Fin 3, vecSq (fun q => bracketMat v i q) = 2 * vecSq v := by
  simp only [vecSq, bracketMat, Fin.sum_univ_three]
  simp [CellCert.permSign]
  ring

theorem op_sqrt {G : Fin 3 → Fin 3 → ℂ} {g : ℝ} (hg : 0 ≤ g) (hG : OpBound G g) (u : Fin 3 → ℂ) :
    Real.sqrt (vecSq (matVec G u)) ≤ g * Real.sqrt (vecSq u) := by
  rw [← Real.sqrt_sq hg, ← Real.sqrt_mul (sq_nonneg g)]
  exact Real.sqrt_le_sqrt (hG u)

theorem vecInner_le (u w : Fin 3 → ℂ) : ‖∑ l : Fin 3, u l * w l‖ ≤ Real.sqrt (vecSq u) * Real.sqrt (vecSq w) := by
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun l => ‖u l‖) (fun l => ‖w l‖)
  simpa [vecSq] using h

theorem vecSq_nonneg (v : Fin 3 → ℂ) : 0 ≤ vecSq v := by unfold vecSq; positivity

theorem sumSq_nonneg (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ sumSq s := by unfold sumSq; positivity

theorem vecSq_conj (w : Fin 3 → ℂ) : vecSq (fun j => (starRingEnd ℂ) (w j)) = vecSq w := by
  simp [vecSq]

theorem coupling_sq_le {G : Fin 3 → Fin 3 → ℂ} {g : ℝ} (hg : 0 ≤ g) (hG : OpBound G g)
    (htr : ∑ a : Fin 3, G a a = 0) (v : Fin 3 → ℂ) :
    sumSq (couplingMap G v) ≤ 7 / 2 * g ^ 2 * vecSq v := by
  rw [real_identity G v htr]
  have h1 := hG v
  have h2 : ∑ i : Fin 3, vecSq (matVec G (fun q => bracketMat v i q)) ≤ g ^ 2 * (2 * vecSq v) := by
    rw [← bracket_sq, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hG _
  have h3 : (∑ l : Fin 3, v l * matVec G (fun j => (starRingEnd ℂ) (matVec G v j)) l).re ≤ g ^ 2 * vecSq v := by
    refine (Complex.re_le_norm _).trans ((vecInner_le _ _).trans ?_)
    have ha := op_sqrt hg hG (fun j => (starRingEnd ℂ) (matVec G v j))
    rw [vecSq_conj] at ha
    have hb := op_sqrt hg hG v
    have hv := Real.sq_sqrt (vecSq_nonneg v)
    have s0 := Real.sqrt_nonneg (vecSq v)
    have s1 := Real.sqrt_nonneg (vecSq (matVec G v))
    calc Real.sqrt (vecSq v) * Real.sqrt (vecSq (matVec G fun j => (starRingEnd ℂ) (matVec G v j)))
        ≤ Real.sqrt (vecSq v) * (g * Real.sqrt (vecSq (matVec G v))) := mul_le_mul_of_nonneg_left ha s0
      _ ≤ Real.sqrt (vecSq v) * (g * (g * Real.sqrt (vecSq v))) := by
          gcongr
      _ = g ^ 2 * Real.sqrt (vecSq v) ^ 2 := by ring
      _ = g ^ 2 * vecSq v := by rw [hv]
  nlinarith

theorem pairing_le (s t : Fin 3 → Fin 3 → ℂ) :
    ‖entryPairing s t‖ ≤ Real.sqrt (sumSq s) * Real.sqrt (sumSq t) := by
  unfold entryPairing
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => norm_sum_le _ _).trans ?_
  simp only [norm_mul, RCLike.norm_conj]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun x : Fin 3 × Fin 3 => ‖s x.1 x.2‖)
    (fun x => ‖t x.1 x.2‖)
  simp only [Fintype.sum_prod_type] at h
  simpa [sumSq] using h

theorem pairing_swap (s t : Fin 3 → Fin 3 → ℂ) :
    entryPairing s t = (starRingEnd ℂ) (entryPairing t s) := by
  unfold entryPairing
  simp [map_sum, mul_comm]

theorem coupling_norm_le {G : Fin 3 → Fin 3 → ℂ} {g : ℝ} (hg : 0 ≤ g) (hG : OpBound G g)
    (htr : ∑ a : Fin 3, G a a = 0) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    ‖entryPairing (couplingMap G v) s‖
      ≤ Exterior.traceFreeConst * g * Real.sqrt (sumSq s) * Real.sqrt (vecSq v) := by
  have h1 := pairing_le (couplingMap G v) s
  have h2 : Real.sqrt (sumSq (couplingMap G v)) ≤ Exterior.traceFreeConst * g * Real.sqrt (vecSq v) := by
    refine (Real.sqrt_le_sqrt (coupling_sq_le hg hG htr v)).trans (le_of_eq ?_)
    unfold Exterior.traceFreeConst
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hg]
  have h3 := Real.sqrt_nonneg (sumSq s)
  calc ‖entryPairing (couplingMap G v) s‖ ≤ Real.sqrt (sumSq (couplingMap G v)) * Real.sqrt (sumSq s) := h1
    _ ≤ (Exterior.traceFreeConst * g * Real.sqrt (vecSq v)) * Real.sqrt (sumSq s) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = Exterior.traceFreeConst * g * Real.sqrt (sumSq s) * Real.sqrt (vecSq v) := by ring

theorem ent_eq (M : Space →L[ℝ] Space) (i j : Fin 3) : ent M i j = entry M i j := by
  simp [ent, entry, unitVector, EuclideanSpace.inner_single_right]

theorem diag_int (M : ℝ → (Space →L[ℝ] Space))
    (hint : ∀ i j : Fin 3, IntervalIntegrable (fun θ => ent (M θ) i j) volume 0 (2 * Real.pi)) (a : Fin 3) :
    IntervalIntegrable (fun θ => frameMat θ (M θ) a a) volume 0 (2 * Real.pi) := by
  simp_rw [frameMat_diag]
  have hc : Continuous fun θ : ℝ => Real.cos θ ^ 2 := by fun_prop
  have hs : Continuous fun θ : ℝ => Real.sin θ ^ 2 := by fun_prop
  have hcs : Continuous fun θ : ℝ => Real.cos θ * Real.sin θ := by fun_prop
  have hcs' : Continuous fun θ : ℝ => -(Real.cos θ * Real.sin θ) := by fun_prop
  have h01 := (hint 0 1).add (hint 1 0)
  fin_cases a
  · simp only [diagExp, Fin.zero_eta, Matrix.cons_val_zero]
    exact (((hint 0 0).continuousOn_mul hc.continuousOn).add (h01.continuousOn_mul hcs.continuousOn)).add
      ((hint 1 1).continuousOn_mul hs.continuousOn)
  · simp only [diagExp, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact (((hint 0 0).continuousOn_mul hs.continuousOn).add (h01.continuousOn_mul hcs'.continuousOn)).add
      ((hint 1 1).continuousOn_mul hc.continuousOn)
  · simp only [diagExp]
    simpa using hint 2 2

theorem zero_trace (m : ℕ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ)
    (hint : ∀ i j : Fin 3, IntervalIntegrable (fun θ => ent (G (cylPoint r θ z)) i j) volume 0 (2 * Real.pi))
    (htr : ∀ θ : ℝ, ∑ i : Fin 3, entry (G (cylPoint r θ z)) i i = 0) :
    ∑ a : Fin 3, modeMat m 0 G r z a a = 0 := by
  have hexp : ∀ θ : ℝ, Complex.exp (-((azimuth m 0 * θ : ℝ) : ℂ) * Complex.I) = 1 := by
    intro θ; simp [azimuth]
  have hmode : ∀ a : Fin 3, modeMat m 0 G r z a a = (1 / (2 * Real.pi) : ℂ) *
      ((∫ θ in (0 : ℝ)..(2 * Real.pi), frameMat θ (G (cylPoint r θ z)) a a : ℝ) : ℂ) := by
    intro a
    unfold modeMat
    simp only [hexp, one_mul]
    rw [intervalIntegral.integral_ofReal]
  have hsum := intervalIntegral.integral_finsetSum (μ := volume) (a := 0) (b := 2 * Real.pi)
    (s := Finset.univ) (f := fun a θ => frameMat θ (G (cylPoint r θ z)) a a)
    (fun a _ => diag_int (fun θ => G (cylPoint r θ z)) hint a)
  have hz : ∀ θ : ℝ, ∑ a : Fin 3, frameMat θ (G (cylPoint r θ z)) a a = 0 := by
    intro θ
    simp only [frameMat_diag]
    rw [diag_sum]
    simpa [ent_eq] using htr θ
  simp only [hmode]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, ← hsum]
  simp [hz]

theorem open_ae (K : CellBox) :
    ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := by
  have h : (Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ : Set (ℝ × ℝ)) =ᵐ[volume] K.rect := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  rw [← Measure.restrict_congr_set h]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)

theorem trace_ae {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c) {K : CellBox}
    {S : CellScalars} {B : CellBases} {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k}
    (hd : IsCellData α c K S B Cl R) :
    ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 → p ∈ K.rect →
      ∑ a : Fin 3, modeMat c.order 0 c.modelCurlGrad p.1 p.2 a a = 0 := by
  have hK := hd.box
  have hsub : K.solid ⊆ c.cellRegion := hd.solid_in_region
  have hfin : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hsub).measure_lt_top
  obtain ⟨C, hC⟩ := hc.model_bounded
  have hGm := hc.model_measurable.2.2.2
  have hloc : ∀ i j : Fin 3,
      LocallyIntegrable (K.solid.indicator (fun y => ent (c.modelCurlGrad y) i j)) volume := by
    intro i j
    refine Integrable.locallyIntegrable ?_
    have hc0 : IntegrableOn (fun _ : Space => C) K.solid := by
      refine (integrableOn_const_iff ?_).2 (Or.inr hfin)
      simp
    refine Integrable.mono' (hc0.integrable_indicator (solid_meas K))
      (((continuous_ent i j).comp_aestronglyMeasurable hGm).indicator (solid_meas K)) (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ K.solid
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Real.norm_eq_abs]
      refine (abs_ent_le _ i j).trans (((c.modelCurlGrad y).le_opNorm _).trans ?_)
      have hu : ‖unitVector j‖ = 1 := by simp [unitVector]
      rw [hu, mul_one]
      exact (hC y (hsub hy)).2.2.2
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, norm_zero]
  have hall : ∀ᵐ q : ℝ × ℝ ∂volume, ∀ i j : Fin 3, 0 < q.1 → IntervalIntegrable
      (fun θ => K.solid.indicator (fun y => ent (c.modelCurlGrad y) i j) (cylPoint q.1 θ q.2))
      volume 0 (2 * Real.pi) := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    exact sections (hloc i j)
  filter_upwards [ae_restrict_of_ae hall] with p hp hp1 hpK
  have hint : ∀ i j : Fin 3, IntervalIntegrable (fun θ => ent (c.modelCurlGrad (cylPoint p.1 θ p.2)) i j)
      volume 0 (2 * Real.pi) := by
    intro i j
    have e : (fun θ => K.solid.indicator (fun y => ent (c.modelCurlGrad y) i j) (cylPoint p.1 θ p.2))
        = fun θ => ent (c.modelCurlGrad (cylPoint p.1 θ p.2)) i j := by
      funext θ
      exact Set.indicator_of_mem (cyl_solid K hK hpK θ) _
    rw [← e]
    exact hp i j hp1
  exact zero_trace c.order c.modelCurlGrad p.1 p.2 hint (fun θ => hd.curlGrad_traceFree p hpK hp1.ne' θ)

theorem wave_eq {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)
    (n : ℤ) (p : ℝ × ℝ) :
    SharpCircleBoundParts.couplingWave c K S x n n p
      = ((entryPairing (couplingMap (modeMat c.order 0 c.modelCurlGrad p.1 p.2)
          (SharpParts.sharpVel c K S x n p)) (SharpParts.sharpGrad c K S x n p)).re : ℂ) := by
  unfold SharpCircleBoundParts.couplingWave CellScalars.curlGradMode
  rw [sub_self, pairing_swap (SharpParts.sharpGrad c K S x n p), ← mul_add, Complex.add_conj]
  push_cast
  ring

theorem meanLoss_summable' {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)
    (p : ℝ × ℝ) (hg : 0 ≤ S.meanGradBound p)
    (hq : Summable (fun n : ℤ => sumSq (SharpParts.sharpGrad c K S x n p)))
    (hv : Summable (fun n : ℤ => vecSq (SharpParts.sharpVel c K S x n p))) :
    Summable (fun n : ℤ => SharpCircleBoundParts.meanLoss c K S x n p) := by
  have hT : 0 ≤ Exterior.traceFreeConst := by unfold Exterior.traceFreeConst; positivity
  have hTg : 0 ≤ Exterior.traceFreeConst * S.meanGradBound p := mul_nonneg hT hg
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) ((hq.add hv).mul_left
    (Exterior.traceFreeConst * S.meanGradBound p))
  · unfold SharpCircleBoundParts.meanLoss
    exact mul_nonneg (mul_nonneg hTg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · unfold SharpCircleBoundParts.meanLoss
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hTg
    have ha := Real.sq_sqrt (sumSq_nonneg (SharpParts.sharpGrad c K S x n p))
    have hb := Real.sq_sqrt (vecSq_nonneg (SharpParts.sharpVel c K S x n p))
    nlinarith [sq_nonneg (Real.sqrt (sumSq (SharpParts.sharpGrad c K S x n p))
      - Real.sqrt (vecSq (SharpParts.sharpVel c K S x n p)))]

end Breakdown.FracInternal.SharpCircleMean

namespace Breakdown.CellCert.CellAnalysis

open Breakdown.FracInternal.SharpCircleMean SharpCircleBoundParts

theorem sharpCircleMean_holds : SharpCircleMeanStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  have hK := hd.box
  filter_upwards [open_ae K, trace_ae hc hd] with p hp htp hq hv
  have hp1 : 0 < p.1 := lt_of_le_of_lt hK.r_order.1 hp.1.1
  have hpK : p ∈ K.rect := ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hG := hd.mean_le p hp hp1.ne'
  have htr := htp hp1 hpK
  have hg := (hd.scalars.grad_bounds_nonneg p).1
  have key : ∀ n : ℤ, ‖couplingWave c K S x n n p‖ ≤ meanLoss c K S x n p := by
    intro n
    rw [wave_eq, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (coupling_norm_le hg hG htr _ _)
  refine ⟨Summable.of_norm_bounded (meanLoss_summable' c K S x p hg hq hv) key, fun n => ?_⟩
  exact neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans (key n))

end Breakdown.CellCert.CellAnalysis
