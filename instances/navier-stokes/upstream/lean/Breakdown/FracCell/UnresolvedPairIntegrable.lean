import Breakdown.FracCell.UnresolvedRowClassSt
import Breakdown.FracCell.ModeGradSquare
import Breakdown.FracCell.ModeVelSquare
import Breakdown.FracCell.CellDensityModesSolid

open MeasureTheory Set

noncomputable section

namespace Breakdown.FracInternal.UnresolvedPairIntegrable


open SteadyCert CellCert CellCert.CellAnalysis Assembly
open CellCert.CellAnalysis.LowEntry.Internal CellCert.CellAnalysis.ModeGradSquare.Internal

def WeightedSq (K : CellBox) (f : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f (volume.restrict K.rect) ∧
    IntegrableOn (fun p => K.lineWeight p.1 * ‖f p‖ ^ 2) K.rect

def BoundedOn (K : CellBox) (h : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable h (volume.restrict K.rect) ∧ ∃ C : ℝ, ∀ p ∈ K.rect, ‖h p‖ ≤ C

theorem lw_nonneg {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ K.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs
  · exact le_trans hK.r_order.1 hp.1.1
  · exact zero_le_one

theorem lw_meas (K : CellBox) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => K.lineWeight p.1) (volume.restrict K.rect) :=
  ((lineWeight_cont K).comp continuous_fst).aestronglyMeasurable

theorem ws_add {K : CellBox} (hK : IsCellBox K) {f g : ℝ × ℝ → ℂ} (hf : WeightedSq K f) (hg : WeightedSq K g) :
    WeightedSq K (fun p => f p + g p) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  refine ((hf.2.add hg.2).const_mul 2).mono' ((lw_meas K).mul ((hf.1.add hg.1).norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
  have hw := lw_nonneg hK hp
  have h1 := norm_add_le (f p) (g p)
  have h2 : ‖f p + g p‖ ^ 2 ≤ 2 * ‖f p‖ ^ 2 + 2 * ‖g p‖ ^ 2 := by
    nlinarith [norm_nonneg (f p + g p), sq_nonneg (‖f p‖ - ‖g p‖), norm_nonneg (f p), norm_nonneg (g p)]
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

theorem ws_sub {K : CellBox} (hK : IsCellBox K) {f g : ℝ × ℝ → ℂ} (hf : WeightedSq K f) (hg : WeightedSq K g) :
    WeightedSq K (fun p => f p - g p) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  refine ((hf.2.add hg.2).const_mul 2).mono' ((lw_meas K).mul ((hf.1.sub hg.1).norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
  have hw := lw_nonneg hK hp
  have h1 := norm_sub_le (f p) (g p)
  have h2 : ‖f p - g p‖ ^ 2 ≤ 2 * ‖f p‖ ^ 2 + 2 * ‖g p‖ ^ 2 := by
    nlinarith [norm_nonneg (f p - g p), sq_nonneg (‖f p‖ - ‖g p‖), norm_nonneg (f p), norm_nonneg (g p)]
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

theorem ws_zero (K : CellBox) : WeightedSq K (fun _ => 0) := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  simp

theorem ws_sum {K : CellBox} (hK : IsCellBox K) {ι : Type*} (s : Finset ι) {f : ι → ℝ × ℝ → ℂ}
    (hf : ∀ i ∈ s, WeightedSq K (f i)) : WeightedSq K (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ws_zero K
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact ws_add hK (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem ws_bdd_mul {K : CellBox} (hK : IsCellBox K) {h f : ℝ × ℝ → ℂ} (hh : BoundedOn K h) (hf : WeightedSq K f) :
    WeightedSq K (fun p => h p * f p) := by
  obtain ⟨hm, C, hC⟩ := hh
  refine ⟨hm.mul hf.1, ?_⟩
  refine (hf.2.const_mul (C ^ 2)).mono' ((lw_meas K).mul ((hm.mul hf.1).norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
  have hw := lw_nonneg hK hp
  have h1 : ‖h p‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC p hp) 2
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _)), norm_mul, mul_pow]
  have h3 : 0 ≤ K.lineWeight p.1 * ‖f p‖ ^ 2 := mul_nonneg hw (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right h1 h3]

theorem ws_mul_bdd {K : CellBox} (hK : IsCellBox K) {h f : ℝ × ℝ → ℂ} (hf : WeightedSq K f) (hh : BoundedOn K h) :
    WeightedSq K (fun p => f p * h p) := by
  simpa only [mul_comm] using ws_bdd_mul hK hh hf

theorem bdd_const (K : CellBox) (z : ℂ) : BoundedOn K (fun _ => z) :=
  ⟨aestronglyMeasurable_const, ‖z‖, fun _ _ => le_rfl⟩

theorem ws_const_mul {K : CellBox} (hK : IsCellBox K) (z : ℂ) {f : ℝ × ℝ → ℂ} (hf : WeightedSq K f) :
    WeightedSq K (fun p => z * f p) :=
  ws_bdd_mul hK (bdd_const K z) hf

theorem bdd_conj {K : CellBox} {h : ℝ × ℝ → ℂ} (hh : BoundedOn K h) :
    BoundedOn K (fun p => (starRingEnd ℂ) (h p)) := by
  obtain ⟨hm, C, hC⟩ := hh
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hm, C, fun p hp => ?_⟩
  rw [Complex.norm_conj]
  exact hC p hp

theorem ws_conj {K : CellBox} {f : ℝ × ℝ → ℂ} (hf : WeightedSq K f) :
    WeightedSq K (fun p => (starRingEnd ℂ) (f p)) := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hf.1, ?_⟩
  simpa only [Complex.norm_conj] using hf.2

theorem pair_int {K : CellBox} (hK : IsCellBox K) {f g : ℝ × ℝ → ℂ} (hf : WeightedSq K f) (hg : WeightedSq K g) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * (f p * (starRingEnd ℂ) (g p))) K.rect := by
  have hm : AEStronglyMeasurable (fun p => (K.lineWeight p.1 : ℂ) * (f p * (starRingEnd ℂ) (g p)))
      (volume.restrict K.rect) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (lw_meas K)).mul
      (hf.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hg.1))
  refine (hf.2.add hg.2).mono' hm ?_
  filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
  have hw := lw_nonneg hK hp
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hw]
  simp only [Pi.add_apply]
  have h1 : ‖f p‖ * ‖g p‖ ≤ ‖f p‖ ^ 2 + ‖g p‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f p‖ - ‖g p‖), norm_nonneg (f p), norm_nonneg (g p)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hw]



def lift (X : Space → Space) : Space → (Space →L[ℝ] Space) := fun y => (innerSL ℝ axialUnit).smulRight (X y)

theorem frame_lift (θ : ℝ) (u : Space) (a : Fin 3) :
    frameMat θ ((innerSL ℝ axialUnit).smulRight u) a 2 = frameVec θ u a := by
  have h : (innerSL ℝ axialUnit) axialUnit = 1 := by
    simp [axialUnit]
  fin_cases a <;> simp [frameMat, frameVec, ContinuousLinearMap.smulRight_apply, h]

theorem modeVec_lift (m : ℕ) (n : ℤ) (X : Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    modeVec m n X p.1 p.2 a = gradMode m n (lift X) a 2 p := by
  unfold gradMode modeMat modeVec lift
  simp only [frame_lift]

theorem lift_meas {X : Space → Space} (hX : AEStronglyMeasurable X volume) :
    AEStronglyMeasurable (lift X) volume := by
  have hc : Continuous (fun u : Space => (innerSL ℝ axialUnit).smulRight u) :=
    (ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ axialUnit)).continuous
  exact hc.comp_aestronglyMeasurable hX

theorem lift_sq {X : Space → Space} (hX : MemLp X 2 volume) : Integrable (fun y => entrySq (lift X y)) := by
  have h := (memLp_two_iff_integrable_sq_norm hX.1).1 hX
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [entrySq, lift, Fin.sum_univ_three, unitVector, axialUnit, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.inner_single_left]

theorem ws_mode {K : CellBox} (hK : IsCellBox K) (m : ℕ) (n : ℤ) {X : Space → Space} (hX : MemLp X 2 volume)
    (a : Fin 3) : WeightedSq K (fun p => modeVec m n X p.1 p.2 a) := by
  have e : (fun p : ℝ × ℝ => modeVec m n X p.1 p.2 a) = gradMode m n (lift X) a 2 :=
    funext fun p => modeVec_lift m n X a p
  rw [e]
  exact ⟨gm_meas K hK m n (lift_meas hX.1) a 2, gm_sq K hK m n (lift_meas hX.1) (lift_sq hX) a 2⟩

theorem mode_norm_le (m : ℕ) (n : ℤ) (X : Space → Space) (r z C : ℝ) (hC : ∀ θ, ‖X (cylPoint r θ z)‖ ≤ C)
    (a : Fin 3) : ‖modeVec m n X r z a‖ ≤ C := by
  unfold modeVec
  have hp := Real.pi_pos
  have hb : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi), ‖Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameVec θ (X (cylPoint r θ z)) a : ℂ)‖ ≤ C := by
    intro θ _
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact (ModeVelSquareInternal.frameVec_abs θ _ a).trans (hC θ)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [norm_mul]
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn, sub_zero, abs_of_pos (by positivity)] at *
  calc 1 / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameVec θ (X (cylPoint r θ z)) a : ℂ)‖ ≤ 1 / (2 * Real.pi) * (C * (2 * Real.pi)) := by gcongr
    _ = C := by field_simp

theorem bdd_mode {K : CellBox} (hK : IsCellBox K) (m : ℕ) (n : ℤ) {X : Space → Space}
    (hX : AEStronglyMeasurable X volume) (C : ℝ) (hC : ∀ p ∈ K.rect, ∀ θ, ‖X (cylPoint p.1 θ p.2)‖ ≤ C)
    (a : Fin 3) : BoundedOn K (fun p => modeVec m n X p.1 p.2 a) := by
  have e : (fun p : ℝ × ℝ => modeVec m n X p.1 p.2 a) = gradMode m n (lift X) a 2 :=
    funext fun p => modeVec_lift m n X a p
  refine ⟨e ▸ gm_meas K hK m n (lift_meas hX) a 2, C, fun p hp => mode_norm_le m n X p.1 p.2 C (hC p hp) a⟩

theorem cyl_mem_solid {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid := by
  have hr : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  have hz : 0 ≤ p.2 := le_trans hK.z_order.1 hp.2.1
  simp only [CellBox.solid, Set.mem_ofPred_eq, FracInternal.CellDensityModesSolid.cyl_radius hr,
    FracInternal.CellDensityModesSolid.cyl_height, abs_of_nonneg hz]
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩

theorem bdd_rHat {K : CellBox} (hK : IsCellBox K) :
    BoundedOn K (fun p => ((CellScalars.rHat K p : ℝ) : ℂ)) := by
  refine ⟨(Complex.measurable_ofReal.comp (measurable_fst.div
    ((lineWeight_cont K).measurable.comp measurable_fst))).aestronglyMeasurable, 1 + K.r₂, fun p hp => ?_⟩
  have hr : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs
  · rcases eq_or_lt_of_le hr with h | h
    · rw [← h]; simp; linarith [hK.r_order.2]
    · rw [div_self h.ne']; simp; linarith [hK.r_order.2]
  · rw [div_one, abs_of_nonneg hr]; linarith [hp.1.2]

theorem ws_cross_bdd {K : CellBox} (hK : IsCellBox K) {u w : ℝ × ℝ → Fin 3 → ℂ}
    (hu : ∀ j, BoundedOn K (fun p => u p j)) (hw : ∀ j, WeightedSq K (fun p => w p j)) (i : Fin 3) :
    WeightedSq K (fun p => crossC (u p) (w p) i) := by
  fin_cases i
  · exact ws_sub hK (ws_bdd_mul hK (hu 1) (hw 2)) (ws_bdd_mul hK (hu 2) (hw 1))
  · exact ws_sub hK (ws_bdd_mul hK (hu 2) (hw 0)) (ws_bdd_mul hK (hu 0) (hw 2))
  · exact ws_sub hK (ws_bdd_mul hK (hu 0) (hw 1)) (ws_bdd_mul hK (hu 1) (hw 0))

theorem ws_cross_ws {K : CellBox} (hK : IsCellBox K) {u w : ℝ × ℝ → Fin 3 → ℂ}
    (hw : ∀ j, WeightedSq K (fun p => w p j)) (hu : ∀ j, BoundedOn K (fun p => u p j)) (i : Fin 3) :
    WeightedSq K (fun p => crossC (w p) (u p) i) := by
  fin_cases i
  · exact ws_sub hK (ws_mul_bdd hK (hw 1) (hu 2)) (ws_mul_bdd hK (hw 2) (hu 1))
  · exact ws_sub hK (ws_mul_bdd hK (hw 2) (hu 0)) (ws_mul_bdd hK (hw 0) (hu 2))
  · exact ws_sub hK (ws_mul_bdd hK (hw 0) (hu 1)) (ws_mul_bdd hK (hw 1) (hu 0))

theorem ws_curlAdj {K : CellBox} (hK : IsCellBox K) {u : ℝ × ℝ → Fin 3 → ℂ}
    (hu : ∀ j, WeightedSq K (fun p => u p j)) (l j : Fin 3) :
    WeightedSq K (fun p => curlAdj (u p) l j) := by
  unfold curlAdj
  exact ws_sum hK _ fun i _ => ws_const_mul hK _ (hu i)


end Breakdown.FracInternal.UnresolvedPairIntegrable

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly
open CellAnalysis.ModeGradSquare.Internal Breakdown.FracInternal.UnresolvedPairIntegrable

theorem unresolvedPairIntegrable_holds : UnresolvedPairIntegrableStatement := by
  intro α _ _ k N c hc K S B Cl slots R hR _ x hx a _ n _
  have hK : IsCellBox K := hR.box
  obtain ⟨C, hC⟩ := hc.model_bounded
  have hin : ∀ p ∈ K.rect, ∀ θ, cylPoint p.1 θ p.2 ∈ c.cellRegion :=
    fun p hp θ => hR.solid_in_region (cyl_mem_solid hK hp θ)
  have hV : ∀ (k' : ℤ) (j : Fin 3),
      BoundedOn K (fun p => (starRingEnd ℂ) (modeVec c.order k' c.modelVelocity p.1 p.2 j)) :=
    fun k' j => bdd_conj (bdd_mode hK c.order k' hc.model_measurable.1 C
      (fun p hp θ => (hC _ (hin p hp θ)).1) j)
  have hW : ∀ (k' : ℤ) (j : Fin 3),
      BoundedOn K (fun p => (starRingEnd ℂ) (modeVec c.order k' c.modelCurl p.1 p.2 j)) :=
    fun k' j => bdd_conj (bdd_mode hK c.order k' hc.model_measurable.2.1 C
      (fun p hp θ => (hC _ (hin p hp θ)).2.1) j)
  have hrow : ∀ (m : ℤ) (j : Fin 3), WeightedSq K (fun p => CellScalars.rowMode c a m p j) :=
    fun m j => ws_mode hK c.order m (hc.base.row_two a) j
  have hS : ∀ i j : Fin 3, WeightedSq K (fun p => CellScalars.rowCouplingStrain c K R a n p i j) := by
    intro i j
    unfold CellScalars.rowCouplingStrain
    exact ws_bdd_mul hK (bdd_rHat hK) (ws_sum hK _ fun m _ => ws_curlAdj hK (fun l =>
      ws_cross_bdd hK (u := fun p => conjVec3 (modeVec c.order (m - n) c.modelVelocity p.1 p.2))
        (w := fun p => CellScalars.rowMode c a m p) (hV (m - n)) (hrow m) l) i j)
  have hT : ∀ i : Fin 3, WeightedSq K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) := by
    intro i
    unfold CellScalars.rowCouplingVelocity
    exact ws_bdd_mul hK (bdd_rHat hK) (ws_sum hK _ fun m _ =>
      ws_cross_ws hK (u := fun p => conjVec3 (modeVec c.order (m - n) c.modelCurl p.1 p.2))
        (w := fun p => CellScalars.rowMode c a m p) (hrow m) (hW (m - n)) i)
  have hG : ∀ i j : Fin 3, WeightedSq K (gradMode c.order n x.2.1 i j) := fun i j =>
    ⟨gm_meas K hK c.order n hx.1.measurable_gradient i j,
      gm_sq K hK c.order n hx.1.measurable_gradient hx.1.gradient_two i j⟩
  have hv : ∀ i : Fin 3, WeightedSq K (fun p => modeVec c.order n x.1 p.1 p.2 i) := fun i =>
    modeVelSquare K hK c.order x.1 x.2.1 x.2.2.1 hx.1 n i
  have e : CellScalars.unresolvedPairAt c K R x a n = fun p =>
      (∑ i : Fin 3, ∑ j : Fin 3, (K.lineWeight p.1 : ℂ) *
        (gradMode c.order n x.2.1 i j p * (starRingEnd ℂ) (CellScalars.rowCouplingStrain c K R a n p i j)))
      + ∑ i : Fin 3, (K.lineWeight p.1 : ℂ) *
        (modeVec c.order n x.1 p.1 p.2 i * (starRingEnd ℂ) (CellScalars.rowCouplingVelocity c K R a n p i)) := by
    funext p
    simp only [CellScalars.unresolvedPairAt, entryPairing, CellScalars.vecPair, mul_add, Finset.mul_sum]
  rw [e]
  exact Integrable.add
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => pair_int hK (hG i j) (hS i j))
    (integrable_finsetSum _ fun i _ => pair_int hK (hv i) (hT i))

end Breakdown.CellCert.CellAnalysis
