import Breakdown.Cert.ReadingEnergy

open scoped ENNReal Topology NNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.HeldMetric

open Internal.ReadingEnergy Internal.SliceFields

def weightedMeasure (w : Space → ℝ) : Measure Space :=
  volume.withDensity (fun y => ((w y).toNNReal : ℝ≥0∞))

theorem weightedMeasure_le {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) :
    weightedMeasure w ≤ ENNReal.ofReal C • volume := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [weightedMeasure, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul,
    ← setLIntegral_const]
  exact setLIntegral_mono measurable_const fun y _ => ENNReal.ofReal_le_ofReal (hC y)

theorem memLp_weightedMeasure {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) (g : L2R) :
    MemLp (g : Space → Space) 2 (weightedMeasure w) :=
  (Lp.memLp g).of_measure_le_smul ENNReal.ofReal_ne_top (weightedMeasure_le hC)

theorem ae_weightedMeasure {w : Space → ℝ} {P : Space → Prop} (h : ∀ᵐ y, P y) :
    ∀ᵐ y ∂(weightedMeasure w), P y :=
  (withDensity_absolutelyContinuous _ _).ae_le h

def weightedEmbed {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) :
    L2R →ₗ[ℝ] Lp Space 2 (weightedMeasure w) where
  toFun g := (memLp_weightedMeasure hC g).toLp g
  map_add' g h := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (ae_weightedMeasure (Lp.coeFn_add g h))
  map_smul' a g := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_weightedMeasure (Lp.coeFn_smul a g))

theorem weightedEmbed_norm_le {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) (g : L2R) :
    ‖weightedEmbed hC g‖ ≤ (ENNReal.ofReal C ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖g‖ := by
  change ‖(memLp_weightedMeasure hC g).toLp g‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (Lp.eLpNorm_ne_top g)) ?_
  calc eLpNorm (g : Space → Space) 2 (weightedMeasure w)
      ≤ eLpNorm (g : Space → Space) 2 (ENNReal.ofReal C • volume) :=
        eLpNorm_mono_measure _ (weightedMeasure_le hC)
    _ = _ := by rw [eLpNorm_smul_measure_of_ne_top (by simp)]; rfl

def weightedEmbedL {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) :
    L2R →L[ℝ] Lp Space 2 (weightedMeasure w) :=
  (weightedEmbed hC).mkContinuous _ (weightedEmbed_norm_le hC)

theorem weightedEmbedL_norm_sq {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwm : Measurable w) {C : ℝ}
    (hC : ∀ y, w y ≤ C) (g : L2R) :
    ‖weightedEmbedL hC g‖ ^ 2 = ∫ y, w y * ‖(g : Space → Space) y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have e : (weightedEmbedL hC g : Space → Space) =ᵐ[weightedMeasure w] (g : Space → Space) :=
    MemLp.coeFn_toLp (memLp_weightedMeasure hC g)
  rw [integral_congr_ae (g := fun y => ‖(g : Space → Space) y‖ ^ 2)
    (e.mono fun y hy => by simp only [hy, real_inner_self_eq_norm_sq])]
  rw [weightedMeasure, integral_withDensity_eq_integral_smul (hwm.real_toNNReal)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hw0 y), smul_eq_mul]

theorem integrable_weight_mul_sq {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (g : L2R) :
    Integrable (fun y => w y * ‖(g : Space → Space) y‖ ^ 2) :=
  (integrable_norm_sq_L2R g).bdd_mul (c := C) hwm.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 y)]
      exact hC y)

theorem sliceWeightedGrad_eq_sum {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (h : Freq.X) :
    sliceWeightedGrad w h = ∑ j : Fin 3, ‖weightedEmbedL hC (partialX j h)‖ ^ 2 := by
  unfold sliceWeightedGrad
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => integrable_weight_mul_sq hwm hC hw0 _]
  exact Finset.sum_congr rfl fun j _ => (weightedEmbedL_norm_sq hw0 hwm hC _).symm

def weightedColumn {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) (j : Fin 3) :
    XBar →L[ℝ] Lp Space 2 (weightedMeasure w) :=
  (weightedEmbedL hC).comp ((partialX j).comp gradPart)

theorem slice_ae_eq {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (u : XX) :
    (fun t => sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t))) =ᵐ[volume]
      fun t => ∑ j : Fin 3, ‖(weightedColumn hC j).compLpL 2 volume u t‖ ^ 2 := by
  filter_upwards [ae_all_iff.2 fun j =>
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure TimeCircle))
      (weightedColumn hC j) u] with t ht
  exact (sliceWeightedGrad_eq_sum hwm hC hw0 _).trans
    (Finset.sum_congr rfl fun j _ => congrArg (fun z => ‖z‖ ^ 2) (ht j).symm)

theorem integrable_slice {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (u : XX) :
    Integrable (fun t => sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t))) volume :=
  (integrable_finsetSum _ fun j _ =>
    (Lp.memLp ((weightedColumn hC j).compLpL 2 volume u)).integrable_norm_pow two_ne_zero).congr
      (slice_ae_eq hwm hC hw0 u).symm

theorem integral_slice_eq {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (u : XX) :
    ∫ t, sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t)) =
      ∑ j : Fin 3, ‖(weightedColumn hC j).compLpL 2 volume u‖ ^ 2 :=
  (integral_congr_ae (slice_ae_eq hwm hC hw0 u)).trans
    ((integral_finsetSum _ fun j _ =>
      (Lp.memLp ((weightedColumn hC j).compLpL 2 volume u)).integrable_norm_pow two_ne_zero).trans
      (Finset.sum_congr rfl fun _ _ => (norm_sq_eq_integral _).symm))

def weightedNorm {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) (u : XX) : ℝ :=
  Real.sqrt (∑ j : Fin 3, ‖(weightedColumn hC j).compLpL 2 volume u‖ ^ 2)

theorem sizeZ_eq_sum {k : ℕ} {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (u : XX) (κ : Fin k → ℝ) :
    sizeZ w u κ = Real.sqrt (‖secondCLM u‖ ^ 2 +
      ∑ j : Fin 3, ‖(weightedColumn hC j).compLpL 2 volume u‖ ^ 2 + ∑ i, κ i ^ 2) :=
  congrArg (fun s => Real.sqrt (‖secondCLM u‖ ^ 2 + s + ∑ i, κ i ^ 2)) (integral_slice_eq hwm hC hw0 u)

theorem sizeZ_eq_three {k : ℕ} {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (u : XX) (κ : Fin k → ℝ) :
    sizeZ w u κ = Real.sqrt (‖secondCLM u‖ ^ 2 + weightedNorm hC u ^ 2 + vecNorm κ ^ 2) := by
  have e1 : weightedNorm hC u ^ 2 = ∑ j : Fin 3, ‖(weightedColumn hC j).compLpL 2 volume u‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have e2 : vecNorm κ ^ 2 = ∑ i, κ i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  refine (sizeZ_eq_sum hwm hC hw0 u κ).trans (congrArg Real.sqrt ?_)
  linarith

theorem continuous_sizeZ {k : ℕ} {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) : Continuous fun x : XX × (Fin k → ℝ) => sizeZ w x.1 x.2 := by
  refine Continuous.congr ?_ fun x => (sizeZ_eq_sum hwm hC hw0 x.1 x.2).symm
  fun_prop

theorem sqrt_sum_sq_le {ι : Type*} [Fintype ι] (f g h : ι → ℝ) (hh : ∀ i, |h i| ≤ |f i| + |g i|) :
    Real.sqrt (∑ i, h i ^ 2) ≤ Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  have e : ∀ a : ι → ℝ, ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι)‖ = Real.sqrt (∑ i, a i ^ 2) :=
    fun a => by
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]
  have e' : ∀ a : ι → ℝ, Real.sqrt (∑ i, a i ^ 2) = Real.sqrt (∑ i, |a i| ^ 2) :=
    fun a => by simp only [sq_abs]
  have key : Real.sqrt (∑ i, h i ^ 2) ≤ ‖(WithLp.toLp 2 (fun i => |f i| + |g i|) : EuclideanSpace ℝ ι)‖ := by
    rw [e]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    rw [← sq_abs (h i)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hh i) 2
  have tri := norm_add_le (WithLp.toLp 2 (fun i => |f i|) : EuclideanSpace ℝ ι)
    (WithLp.toLp 2 (fun i => |g i|))
  rw [← WithLp.toLp_add] at tri
  rw [e' f, e' g, ← e (fun i => |f i|), ← e (fun i => |g i|)]
  exact key.trans tri

theorem sqrt_three_le {a b c a₁ b₁ c₁ a₂ b₂ c₂ : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha10 : 0 ≤ a₁) (hb10 : 0 ≤ b₁) (hc10 : 0 ≤ c₁) (ha20 : 0 ≤ a₂) (hb20 : 0 ≤ b₂) (hc20 : 0 ≤ c₂)
    (ha : a ≤ a₁ + a₂) (hb : b ≤ b₁ + b₂) (hc : c ≤ c₁ + c₂) :
    Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) ≤
      Real.sqrt (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) + Real.sqrt (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) := by
  have ha' : |a| ≤ |a₁| + |a₂| := by
    rw [abs_of_nonneg ha0, abs_of_nonneg ha10, abs_of_nonneg ha20]; exact ha
  have hb' : |b| ≤ |b₁| + |b₂| := by
    rw [abs_of_nonneg hb0, abs_of_nonneg hb10, abs_of_nonneg hb20]; exact hb
  have hc' : |c| ≤ |c₁| + |c₂| := by
    rw [abs_of_nonneg hc0, abs_of_nonneg hc10, abs_of_nonneg hc20]; exact hc
  have h := sqrt_sum_sq_le ![a₁, b₁, c₁] ![a₂, b₂, c₂] ![a, b, c] (fun i => by
    fin_cases i
    exacts [ha', hb', hc'])
  simpa [Fin.sum_univ_three, add_assoc] using h

theorem weightedNorm_add_le {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) (u v : XX) :
    weightedNorm hC (u + v) ≤ weightedNorm hC u + weightedNorm hC v :=
  sqrt_sum_sq_le _ _ _ fun j => by
    simp only [abs_norm, map_add]
    exact norm_add_le _ _

theorem vecNorm_add_le {k : ℕ} (κ μ : Fin k → ℝ) : vecNorm (κ + μ) ≤ vecNorm κ + vecNorm μ :=
  sqrt_sum_sq_le _ _ _ fun _ => abs_add_le _ _

theorem sizeZ_add_le {k : ℕ} {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (u v : XX) (κ μ : Fin k → ℝ) :
    sizeZ w (u + v) (κ + μ) ≤ sizeZ w u κ + sizeZ w v μ := by
  have hp : ‖secondCLM (u + v)‖ ≤ ‖secondCLM u‖ + ‖secondCLM v‖ :=
    (congrArg norm (map_add secondCLM u v)).trans_le (norm_add_le _ _)
  have key := sqrt_three_le (norm_nonneg (secondCLM (u + v))) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (norm_nonneg (secondCLM u)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (norm_nonneg (secondCLM v)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hp (weightedNorm_add_le hC u v) (vecNorm_add_le κ μ)
  exact (sizeZ_eq_three hwm hC hw0 (u + v) (κ + μ)).trans_le (key.trans_eq
    (congrArg₂ (· + ·) (sizeZ_eq_three hwm hC hw0 u κ).symm (sizeZ_eq_three hwm hC hw0 v μ).symm))

theorem sliceWeightedGrad_ge {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) (x : Freq.X) :
    w₀ * ‖x‖ ^ 2 ≤ sliceWeightedGrad w x := by
  have e : w₀ * ‖x‖ ^ 2 = ∫ y, w₀ * ∑ j : Fin 3, ‖(partialX j x : Space → Space) y‖ ^ 2 :=
    (congrArg (w₀ * ·) (integral_sum_partialX x).symm).trans (integral_const_mul _ _).symm
  refine e.trans_le (integral_mono ((integrable_sum_partialX x).const_mul w₀)
    (integrable_weighted hw (integrable_sum_partialX x)) fun y => ?_)
  exact mul_le_mul_of_nonneg_right (hw.2.2.1 y) (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem integral_gradSq_const_mul (w₀ : ℝ) (u : XX) :
    ∫ t, w₀ * ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2 = w₀ * ‖gradCLM u‖ ^ 2 :=
  (integral_const_mul w₀ _).trans (congrArg (w₀ * ·) (norm_sq_gradCLM u).symm)

theorem integral_slice_ge {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) {C : ℝ}
    (hC : ∀ y, w y ≤ C) (u : XX) :
    ∫ t, w₀ * ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2 ≤
      ∫ t, sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t)) :=
  integral_mono ((integrable_gradSq u).const_mul w₀)
    (integrable_slice hw.2.1 hC (fun y => hw.1.le.trans (hw.2.2.1 y)) u)
    fun t => sliceWeightedGrad_ge hw (gradPart ((u : TimeCircle → XBar) t))

theorem energyW_ge {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) {C : ℝ}
    (hC : ∀ y, w y ≤ C) (u : XX) :
    ‖secondCLM u‖ ^ 2 + w₀ * ‖gradCLM u‖ ^ 2 ≤ energyW w u :=
  add_le_add le_rfl ((integral_gradSq_const_mul w₀ u).symm.trans_le (integral_slice_ge hw hC u))

theorem norm_sq_xx (u : XX) : ‖u‖ ^ 2 = ‖gradCLM u‖ ^ 2 + ‖secondCLM u‖ ^ 2 := by
  have h1 := norm_sq_eq_integral (E := XBar) u
  have h2 := norm_sq_gradCLM u
  have h3 := norm_sq_secondCLM u
  have h4 := integral_add (integrable_gradSq u) (integrable_secondSq u)
  have h5 : ∫ t, ‖(u : TimeCircle → XBar) t‖ ^ 2 = ∫ t, (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2 +
      ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2) :=
    integral_congr_ae (Eventually.of_forall fun t =>
      WithLp.prod_norm_sq_eq_of_L2 ((u : TimeCircle → XBar) t : WithLp 2 (Freq.X × Freq.X)))
  linarith

theorem norm_le_vecNorm {k : ℕ} (κ : Fin k → ℝ) : ‖κ‖ ≤ vecNorm κ :=
  (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => by
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun j => κ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))

theorem sizeZ_lower {k : ℕ} {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) {C : ℝ}
    (hC : ∀ y, w y ≤ C) (u : XX) (κ : Fin k → ℝ) : Real.sqrt (min 1 w₀) * ‖(u, κ)‖ ≤ sizeZ w u κ := by
  have hw₀ : 0 < w₀ := hw.1
  have hm : 0 ≤ min 1 w₀ := le_min zero_le_one hw₀.le
  have hE := energyW_ge hw hC u
  have hN := norm_sq_xx u
  have hs : vecNorm κ ^ 2 = ∑ i, κ i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hK := norm_le_vecNorm κ
  have hc1 : Real.sqrt (min 1 w₀) ≤ 1 := (Real.sqrt_le_sqrt (min_le_left 1 w₀)).trans_eq Real.sqrt_one
  have hc0 : 0 ≤ Real.sqrt (min 1 w₀) := Real.sqrt_nonneg _
  have hc2 : Real.sqrt (min 1 w₀) ^ 2 = min 1 w₀ := Real.sq_sqrt hm
  have hg := sq_nonneg ‖gradCLM u‖
  have hsec := sq_nonneg ‖secondCLM u‖
  have h1 : min 1 w₀ * ‖gradCLM u‖ ^ 2 ≤ w₀ * ‖gradCLM u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hg
  have h2 : min 1 w₀ * ‖secondCLM u‖ ^ 2 ≤ ‖secondCLM u‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hsec).trans_eq (one_mul _)
  have hsumk : 0 ≤ ∑ i, κ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hE0 : 0 ≤ energyW w u := (add_nonneg hsec (mul_nonneg hw₀.le hg)).trans hE
  have hT : 0 ≤ energyW w u + ∑ i, κ i ^ 2 := add_nonneg hE0 hsumk
  have hA : Real.sqrt (min 1 w₀) * ‖u‖ ≤ Real.sqrt (energyW w u + ∑ i, κ i ^ 2) := by
    refine (Real.le_sqrt (mul_nonneg hc0 (norm_nonneg _)) hT).2 ?_
    calc (Real.sqrt (min 1 w₀) * ‖u‖) ^ 2 = Real.sqrt (min 1 w₀) ^ 2 * ‖u‖ ^ 2 := mul_pow _ _ _
      _ = min 1 w₀ * ‖u‖ ^ 2 := congrArg (· * ‖u‖ ^ 2) hc2
      _ = min 1 w₀ * ‖gradCLM u‖ ^ 2 + min 1 w₀ * ‖secondCLM u‖ ^ 2 :=
          (congrArg (min 1 w₀ * ·) hN).trans (mul_add _ _ _)
      _ ≤ w₀ * ‖gradCLM u‖ ^ 2 + ‖secondCLM u‖ ^ 2 := add_le_add h1 h2
      _ = ‖secondCLM u‖ ^ 2 + w₀ * ‖gradCLM u‖ ^ 2 := add_comm _ _
      _ ≤ energyW w u := hE
      _ ≤ energyW w u + ∑ i, κ i ^ 2 := le_add_of_nonneg_right hsumk
  have hV : vecNorm κ ≤ Real.sqrt (energyW w u + ∑ i, κ i ^ 2) :=
    (Real.le_sqrt (Real.sqrt_nonneg _) hT).2 (hs.trans_le (le_add_of_nonneg_left hE0))
  have hB : Real.sqrt (min 1 w₀) * ‖κ‖ ≤ Real.sqrt (energyW w u + ∑ i, κ i ^ 2) :=
    ((mul_le_mul_of_nonneg_right hc1 (norm_nonneg κ)).trans_eq (one_mul _)).trans (hK.trans hV)
  exact (mul_le_mul_of_nonneg_left (le_of_eq (Prod.norm_def (u, κ))) hc0).trans
    ((mul_max_of_nonneg _ _ hc0).trans_le (max_le hA hB))

theorem isClosed_invariant (Γ : Set Symmetry) : IsClosed (invariantHH Γ : Set HH) := by
  unfold invariantHH
  simp only [Submodule.coe_iInf]
  exact isClosed_iInter fun γ => isClosed_iInter fun _ => ContinuousLinearMap.isClosed_ker _

theorem isClosed_eLpNorm_top_le {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (C : ℝ≥0∞) :
    IsClosed {g : Lp F 2 μ | eLpNorm g ⊤ μ ≤ C} := by
  refine IsSeqClosed.isClosed fun g g₀ hg hlim => ?_
  have h1 : Tendsto (fun n => eLpNorm (⇑(g n) - ⇑g₀) 2 μ) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' g g₀).1 hlim
  have h2 : TendstoInMeasure μ (fun n => ⇑(g n)) atTop ⇑g₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun n => Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _) h1
  obtain ⟨ns, -, hns⟩ := h2.exists_seq_tendsto_ae
  have h3 := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ⊤)
    (fun i => Lp.aestronglyMeasurable (g (ns i))) (⇑g₀) hns
  change eLpNorm (⇑g₀) ⊤ μ ≤ C
  exact h3.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun i => hg (ns i)))

theorem supGrad_eq_eLpNorm (v : XX) : supGrad v = eLpNorm (gradCLM v) ⊤ volume :=
  (eLpNorm_congr_ae (ContinuousLinearMap.coeFn_compLpL gradPart v)).symm

theorem isClosed_supGrad_le (C : ℝ≥0∞) : IsClosed {v : XX | supGrad v ≤ C} := by
  have e : {v : XX | supGrad v ≤ C} = gradCLM ⁻¹' {g : HH | eLpNorm g ⊤ volume ≤ C} :=
    Set.ext fun v => Iff.of_eq (congrArg (· ≤ C) (supGrad_eq_eLpNorm v))
  exact (congrArg IsClosed e).mpr ((isClosed_eLpNorm_top_le C).preimage gradCLM.continuous)

theorem supGrad_add_le (u v : XX) : supGrad (u + v) ≤ supGrad u + supGrad v :=
  calc supGrad (u + v) = eLpNorm (⇑(gradCLM u + gradCLM v)) ⊤ volume :=
        (supGrad_eq_eLpNorm (u + v)).trans
          (congrArg (fun g : HH => eLpNorm (⇑g) ⊤ volume) (map_add gradCLM u v))
    _ = eLpNorm (⇑(gradCLM u) + ⇑(gradCLM v)) ⊤ volume := eLpNorm_congr_ae (Lp.coeFn_add _ _)
    _ ≤ eLpNorm (gradCLM u) ⊤ volume + eLpNorm (gradCLM v) ⊤ volume :=
        eLpNorm_add_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) le_top
    _ = supGrad u + supGrad v :=
        congrArg₂ (· + ·) (supGrad_eq_eLpNorm u).symm (supGrad_eq_eLpNorm v).symm

theorem supGrad_sub_le (u v : XX) : supGrad (u - v) ≤ supGrad u + supGrad v :=
  calc supGrad (u - v) = eLpNorm (⇑(gradCLM u - gradCLM v)) ⊤ volume :=
        (supGrad_eq_eLpNorm (u - v)).trans
          (congrArg (fun g : HH => eLpNorm (⇑g) ⊤ volume) (map_sub gradCLM u v))
    _ = eLpNorm (⇑(gradCLM u) - ⇑(gradCLM v)) ⊤ volume := eLpNorm_congr_ae (Lp.coeFn_sub _ _)
    _ ≤ eLpNorm (gradCLM u) ⊤ volume + eLpNorm (gradCLM v) ⊤ volume :=
        eLpNorm_sub_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) le_top
    _ = supGrad u + supGrad v :=
        congrArg₂ (· + ·) (supGrad_eq_eLpNorm u).symm (supGrad_eq_eLpNorm v).symm

theorem supGrad_sub_ne_top {S : ℝ} {u v : XX} (hu : supGrad u ≤ ENNReal.ofReal S)
    (hv : supGrad v ≤ ENNReal.ofReal S) : supGrad (u - v) ≠ ⊤ :=
  ((supGrad_sub_le u v).trans_lt (ENNReal.add_lt_top.2
    ⟨hu.trans_lt ENNReal.ofReal_lt_top, hv.trans_lt ENNReal.ofReal_lt_top⟩)).ne

theorem sup_part_le {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (b : ℕ → XX) (b₀ : XX)
    (hb : Tendsto b atTop (𝓝 b₀)) (hfin : ∀ n, supGrad (b n) ≠ ⊤)
    (hev : ∀ᶠ n in atTop, c * (supGrad (b n)).toReal ≤ ε) : c * (supGrad b₀).toReal ≤ ε := by
  rcases hc.eq_or_lt with h0 | hpos
  · exact (mul_eq_zero_of_left h0.symm _).trans_le hε
  · have hM : 0 ≤ ε / c := div_nonneg hε hpos.le
    have hev' : ∀ᶠ n in atTop, supGrad (b n) ≤ ENNReal.ofReal (ε / c) :=
      hev.mono fun n hn => (ENNReal.le_ofReal_iff_toReal_le (hfin n) hM).2
        ((le_div_iff₀ hpos).2 ((mul_comm _ _).trans_le hn))
    have hmem : supGrad b₀ ≤ ENNReal.ofReal (ε / c) :=
      (isClosed_supGrad_le _).mem_of_tendsto hb hev'
    exact (mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hM hmem) hpos.le).trans_eq
      (mul_div_cancel₀ ε hpos.ne')

theorem admissible {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) :
    IsAdmissibleWeight d.weightFn d.weight :=
  ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩

end Internal.HeldMetric

open Internal.HeldMetric in
theorem heldMetricHolds_of (_h1 : GraphClosedHolds) (_h2 : ReadingEnergyHolds) : HeldMetricHolds := by
  intro k d hd
  have hw := admissible hd
  have hwm : Measurable d.weightFn := hd.weightFn_measurable
  have hC : ∀ y, d.weightFn y ≤ d.weightMax := hd.weightFn_upper
  have hw0 : ∀ y, 0 ≤ d.weightFn y := fun y => hd.weight_pos.le.trans (hd.weightFn_lower y)
  have hS := continuous_sizeZ (k := k) hwm hC hw0
  have hc0 : 0 ≤ 2 * d.sizeBound / d.supBound :=
    div_nonneg (mul_nonneg zero_le_two hd.sizeBound_nonneg) hd.supBound_pos.le
  refine ⟨?_, ⟨Real.sqrt (min 1 d.weight), Real.sqrt_pos.2 (lt_min one_pos hd.weight_pos),
    fun x _ y _ => (sizeZ_lower hw hC (x.1 - y.1) (x.2 - y.2)).trans (le_max_left _ _)⟩, ?_, ?_⟩
  · have c1 : IsClosed {x : XX × (Fin k → ℝ) | gradCLM x.1 ∈ invariantHH d.symmetries} :=
      (isClosed_invariant d.symmetries).preimage (gradCLM.continuous.comp continuous_fst)
    have c2 : IsClosed {x : XX × (Fin k → ℝ) | sizeZ d.weightFn x.1 x.2 ≤ 2 * d.sizeBound} :=
      isClosed_le hS continuous_const
    have c3 : IsClosed {x : XX × (Fin k → ℝ) | supGrad x.1 ≤ ENNReal.ofReal d.supBound} :=
      (isClosed_supGrad_le _).preimage continuous_fst
    exact c1.inter (c2.inter c3)
  · intro x hx y hy z hz
    have e1 : x.1 - z.1 = (x.1 - y.1) + (y.1 - z.1) := (sub_add_sub_cancel x.1 y.1 z.1).symm
    have e2 : x.2 - z.2 = (x.2 - y.2) + (y.2 - z.2) := (sub_add_sub_cancel x.2 y.2 z.2).symm
    have hsz : sizeZ d.weightFn (x.1 - z.1) (x.2 - z.2) ≤
        sizeZ d.weightFn (x.1 - y.1) (x.2 - y.2) + sizeZ d.weightFn (y.1 - z.1) (y.2 - z.2) :=
      (congrArg₂ (sizeZ d.weightFn) e1 e2).trans_le (sizeZ_add_le hwm hC hw0 _ _ _ _)
    have hxy := supGrad_sub_ne_top hx.2.2 hy.2.2
    have hyz := supGrad_sub_ne_top hy.2.2 hz.2.2
    have hsup : (supGrad (x.1 - z.1)).toReal ≤
        (supGrad (x.1 - y.1)).toReal + (supGrad (y.1 - z.1)).toReal :=
      (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hxy, hyz⟩)
        ((congrArg supGrad e1).trans_le (supGrad_add_le _ _))).trans_eq
        (ENNReal.toReal_add hxy hyz)
    refine max_le ?_ ?_
    · exact hsz.trans (add_le_add (le_max_left _ _) (le_max_left _ _))
    · calc 2 * d.sizeBound / d.supBound * (supGrad (x.1 - z.1)).toReal
          ≤ 2 * d.sizeBound / d.supBound * ((supGrad (x.1 - y.1)).toReal +
            (supGrad (y.1 - z.1)).toReal) := mul_le_mul_of_nonneg_left hsup hc0
        _ = 2 * d.sizeBound / d.supBound * (supGrad (x.1 - y.1)).toReal +
            2 * d.sizeBound / d.supBound * (supGrad (y.1 - z.1)).toReal := mul_add _ _ _
        _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)
  · intro x hx y hy u hu hlim ε hev
    have hT : Tendsto (fun n => x - u n) atTop (𝓝 (x - y)) := tendsto_const_nhds.sub hlim
    have hε : 0 ≤ ε := by
      obtain ⟨n, hn⟩ := hev.exists
      exact (Real.sqrt_nonneg _).trans ((le_max_left _ _).trans hn)
    refine max_le ?_ ?_
    · exact le_of_tendsto ((hS.tendsto (x - y)).comp hT)
        (hev.mono fun n hn => (le_max_left _ _).trans hn)
    · exact sup_part_le hc0 hε (fun n => x.1 - (u n).1) (x.1 - y.1)
        (tendsto_const_nhds.sub ((continuous_fst.tendsto y).comp hlim))
        (fun n => supGrad_sub_ne_top hx.2.2 (hu n).2.2)
        (hev.mono fun n hn => (le_max_right _ _).trans hn)

end Breakdown.Cert
