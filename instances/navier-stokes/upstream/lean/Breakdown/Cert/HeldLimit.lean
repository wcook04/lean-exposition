import Breakdown.Cert.Nodes
import Breakdown.Cert.HeldLimitReadings
import Breakdown.Cert.WeakCompact
import Breakdown.Cert.HeldLimitProducts

open scoped ENNReal Topology NNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.HeldLimit

theorem tendsto_inner_clm_apply {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : ℕ → E →L[ℝ] F) (T₀ : E →L[ℝ] F) (x : ℕ → E) (x₀ : E) (B : ℝ)
    (hT : Tendsto T atTop (𝓝 T₀)) (hx : ∀ n, ‖x n‖ ≤ B)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (x n) y) atTop (𝓝 (inner ℝ x₀ y))) (z : F) :
    Tendsto (fun n => inner ℝ (T n (x n)) z) atTop (𝓝 (inner ℝ (T₀ x₀) z)) := by
  have h1 : Tendsto (fun n => inner ℝ (T₀ (x n)) z) atTop (𝓝 (inner ℝ (T₀ x₀) z)) := by
    have := hw (ContinuousLinearMap.adjoint T₀ z)
    simpa only [ContinuousLinearMap.adjoint_inner_right] using this
  have h2 : Tendsto (fun n => inner ℝ ((T n - T₀) (x n)) z) atTop (𝓝 0) := by
    have hn : Tendsto (fun n => ‖T n - T₀‖ * B * ‖z‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => ‖T n - T₀‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hT
      simpa using (h0.mul_const B).mul_const ‖z‖
    refine squeeze_zero_norm (fun n => ?_) hn
    calc ‖inner ℝ ((T n - T₀) (x n)) z‖ ≤ ‖(T n - T₀) (x n)‖ * ‖z‖ := norm_inner_le_norm _ _
      _ ≤ ‖T n - T₀‖ * ‖x n‖ * ‖z‖ := by gcongr; exact (T n - T₀).le_opNorm _
      _ ≤ ‖T n - T₀‖ * B * ‖z‖ := by gcongr; exact hx n
  have h3 := h2.add h1
  rw [zero_add] at h3
  refine h3.congr (fun n => ?_)
  rw [show (T n - T₀) (x n) = T n (x n) - T₀ (x n) from rfl, inner_sub_left, sub_add_cancel]

theorem inner_sum_eq_zero_of_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) (a b c r e : ℕ → E) (a₀ b₀ c₀ r₀ e₀ : E)
    (ha : Tendsto (fun n => inner ℝ (a n) z) atTop (𝓝 (inner ℝ a₀ z)))
    (hb : Tendsto (fun n => inner ℝ (b n) z) atTop (𝓝 (inner ℝ b₀ z)))
    (hc : Tendsto (fun n => inner ℝ (c n) z) atTop (𝓝 (inner ℝ c₀ z)))
    (hr : Tendsto (fun n => inner ℝ (r n) z) atTop (𝓝 (inner ℝ r₀ z)))
    (he : Tendsto (fun n => inner ℝ (e n) z) atTop (𝓝 (inner ℝ e₀ z)))
    (h0 : ∀ n, a n + b n + c n + r n + e n = 0) :
    inner ℝ (a₀ + b₀ + c₀ + r₀ + e₀) z = 0 := by
  have hs := (((ha.add hb).add hc).add hr).add he
  have hz : ∀ n, inner ℝ (a n) z + inner ℝ (b n) z + inner ℝ (c n) z + inner ℝ (r n) z
      + inner ℝ (e n) z = 0 := fun n => by
    simp only [← inner_add_left, h0 n, inner_zero_left]
  have h := tendsto_nhds_unique tendsto_const_nhds (hs.congr hz)
  simp only [inner_add_left]
  exact h.symm

theorem tendsto_clm_of_weak {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {k : ℕ} (L : E →L[ℝ] (Fin k → ℝ)) (x : ℕ → E) (x₀ : E)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (x n) y) atTop (𝓝 (inner ℝ x₀ y))) :
    Tendsto (fun n => L (x n)) atTop (𝓝 (L x₀)) := by
  rw [tendsto_pi_nhds]
  intro i
  set ℓ : StrongDual ℝ E := (ContinuousLinearMap.proj i).comp L
  set y : E := (InnerProductSpace.toDual ℝ E).symm ℓ
  have hy : ∀ a, L a i = inner ℝ a y := fun a => by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl
  simp only [hy]
  exact hw y

theorem isClosed_invariantHH (Γ : Set Symmetry) : IsClosed (invariantHH Γ : Set HH) := by
  unfold invariantHH
  simp only [Submodule.coe_iInf]
  exact isClosed_iInter fun γ => isClosed_iInter fun _ => ContinuousLinearMap.isClosed_ker _

theorem weighted_integral_nonneg {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) :
    0 ≤ ∫ t, sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t)) := by
  apply integral_nonneg
  intro t
  apply integral_nonneg
  intro y
  exact mul_nonneg (hw y) (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem energyW_nonneg {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) : 0 ≤ energyW w u := by
  have h := weighted_integral_nonneg hw u
  have h' := sq_nonneg ‖secondCLM u‖
  unfold energyW
  linarith

theorem secondCLM_sq_le {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) :
    ‖secondCLM u‖ ^ 2 ≤ energyW w u := by
  have h := weighted_integral_nonneg hw u
  unfold energyW
  linarith

theorem sqrt_energyW_le_sizeZ {k : ℕ} (w : Space → ℝ) (u : XX) (κ : Fin k → ℝ) :
    Real.sqrt (energyW w u) ≤ sizeZ w u κ :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _))

theorem vecNorm_le_sizeZ {k : ℕ} {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) (κ : Fin k → ℝ) :
    vecNorm κ ≤ sizeZ w u κ :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_left (energyW_nonneg hw u))

theorem abs_le_vecNorm {k : ℕ} (κ : Fin k → ℝ) (i : Fin k) : |κ i| ≤ vecNorm κ := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (f := fun j => κ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))

theorem norm_le_vecNorm {k : ℕ} (κ : Fin k → ℝ) : ‖κ‖ ≤ vecNorm κ :=
  (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact abs_le_vecNorm κ i

theorem norm_le_of_add_eq_zero {E : Type*} [NormedAddCommGroup E] {f c a r e : E}
    (h : f + c + a + r + e = 0) : ‖f‖ ≤ ‖c‖ + ‖a‖ + ‖r‖ + ‖e‖ := by
  have he : f = -(c + a + r + e) := by
    rw [eq_neg_iff_add_eq_zero, ← h]
    abel
  rw [he, norm_neg]
  linarith [norm_add_le (c + a + r) e, norm_add_le (c + a) r, norm_add_le c a]

theorem l2_norm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ∫ a, ‖u a‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun a => real_inner_self_eq_norm_sq _)

theorem l2_integrable_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : Lp E 2 μ) :
    Integrable (fun a => ‖u a‖ ^ 2) μ :=
  (L2.integrable_inner (𝕜 := ℝ) u u).congr (Eventually.of_forall fun _ => real_inner_self_eq_norm_sq _)

theorem norm_sq_compLpL_add {α : Type*} [MeasurableSpace α] {μ : Measure α} {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hAB : ∀ x, ‖x‖ ^ 2 = ‖A x‖ ^ 2 + ‖B x‖ ^ 2) (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ‖A.compLpL 2 μ u‖ ^ 2 + ‖B.compLpL 2 μ u‖ ^ 2 := by
  rw [l2_norm_sq_eq_integral, l2_norm_sq_eq_integral, l2_norm_sq_eq_integral,
    ← integral_add (l2_integrable_norm_sq _) (l2_integrable_norm_sq _)]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL A u, ContinuousLinearMap.coeFn_compLpL B u]
    with a ha hb
  rw [ha, hb]
  exact hAB _

theorem norm_compLpL_le_top {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (u : Lp E 2 μ) (h : eLpNorm (fun a => A (u a)) ⊤ μ < ⊤) :
    ‖A.compLpL 2 μ u‖ ≤ (eLpNorm (fun a => A (u a)) ⊤ μ).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousLinearMap.coeFn_compLpL A u)]
  exact ENNReal.toReal_mono h.ne (eLpNorm_le_eLpNorm_of_exponent_le le_top
    (A.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)))

theorem norm_sq_xbar (q : XBar) : ‖q‖ ^ 2 = ‖gradPart q‖ ^ 2 + ‖secondPart q‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (q : WithLp 2 (Freq.X × Freq.X))

theorem norm_sq_eq (u : XX) : ‖u‖ ^ 2 = ‖gradCLM u‖ ^ 2 + ‖secondCLM u‖ ^ 2 :=
  norm_sq_compLpL_add gradPart secondPart norm_sq_xbar u

theorem gradCLM_norm_le (u : XX) (h : supGrad u < ⊤) : ‖gradCLM u‖ ≤ (supGrad u).toReal := by
  have : IsProbabilityMeasure (volume : Measure TimeCircle) :=
    ⟨by rw [AddCircle.measure_univ]; simp⟩
  exact norm_compLpL_le_top gradPart u h

theorem le_add_of_sq_eq {x a b : ℝ} (_hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 = a ^ 2 + b ^ 2) : x ≤ a + b := by
  nlinarith [mul_nonneg ha hb]

theorem norm_le_add (u : XX) : ‖u‖ ≤ ‖gradCLM u‖ + ‖secondCLM u‖ :=
  le_add_of_sq_eq (norm_nonneg u) (norm_nonneg _) (norm_nonneg _) (norm_sq_eq u)

theorem exists_bound_of_tendsto {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : ℕ → E →L[ℝ] F) (T₀ : E →L[ℝ] F)
    (hT : Tendsto T atTop (𝓝 T₀)) : ∃ C, 0 ≤ C ∧ ∀ n x, ‖T n x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC⟩ := hT.norm.bddAbove_range
  exact ⟨max C 0, le_max_right _ _, fun n x =>
    (T n).le_of_opNorm_le ((hC ⟨n, rfl⟩).trans (le_max_left _ _)) x⟩

theorem convex_topBall {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (C : ℝ≥0∞) : Convex ℝ {g : Lp F 2 μ | eLpNorm g ⊤ μ ≤ C} := by
  intro g hg h hh a b ha hb hab
  have hg' : eLpNorm g ⊤ μ ≤ C := hg
  have hh' : eLpNorm h ⊤ μ ≤ C := hh
  change eLpNorm (⇑(a • g + b • h)) ⊤ μ ≤ C
  rw [eLpNorm_congr_ae (Lp.coeFn_add _ _)]
  refine (eLpNorm_add_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) le_top).trans ?_
  rw [eLpNorm_congr_ae (Lp.coeFn_smul a g), eLpNorm_congr_ae (Lp.coeFn_smul b h),
    eLpNorm_const_smul, eLpNorm_const_smul]
  calc ‖a‖ₑ * eLpNorm g ⊤ μ + ‖b‖ₑ * eLpNorm h ⊤ μ ≤ ‖a‖ₑ * C + ‖b‖ₑ * C := by gcongr
    _ = (‖a‖ₑ + ‖b‖ₑ) * C := by ring
    _ = C := by
      rw [Real.enorm_of_nonneg ha, Real.enorm_of_nonneg hb, ← ENNReal.ofReal_add ha hb, hab,
        ENNReal.ofReal_one, one_mul]

theorem isClosed_topBall {α F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (C : ℝ≥0∞) : IsClosed {g : Lp F 2 μ | eLpNorm g ⊤ μ ≤ C} := by
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

theorem topBall_of_weak {α F E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (L : E →L[ℝ] Lp F 2 μ) (C : ℝ≥0∞) (u : ℕ → E) (u₀ : E)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y)))
    (hu : ∀ n, eLpNorm (L (u n)) ⊤ μ ≤ C) : eLpNorm (L u₀) ⊤ μ ≤ C :=
  mem_of_weak_limit (L ⁻¹' {g : Lp F 2 μ | eLpNorm g ⊤ μ ≤ C})
    ((convex_topBall C).linear_preimage L.toLinearMap) ((isClosed_topBall C).preimage L.continuous)
    u hu u₀ hw

theorem supGrad_eq (v : XX) : supGrad v = eLpNorm (gradCLM v) ⊤ volume :=
  (eLpNorm_congr_ae (ContinuousLinearMap.coeFn_compLpL gradPart v)).symm

theorem supGrad_le_of_weak (S : ℝ) (u : ℕ → XX) (u₀ : XX)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y)))
    (hS : ∀ n, supGrad (u n) ≤ ENNReal.ofReal S) : supGrad u₀ ≤ ENNReal.ofReal S := by
  rw [supGrad_eq]
  exact topBall_of_weak gradCLM _ u u₀ hw fun n => by
    rw [← supGrad_eq]
    exact hS n

def weightedVolume (w : Space → ℝ) : Measure Space :=
  volume.withDensity (fun y => ((w y).toNNReal : ℝ≥0∞))

theorem weightedVolume_le {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) :
    weightedVolume w ≤ ENNReal.ofReal C • volume := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [weightedVolume, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul,
    ← setLIntegral_const]
  exact setLIntegral_mono measurable_const fun y _ => ENNReal.ofReal_le_ofReal (hC y)

theorem memLp_weighted {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) (g : L2R) :
    MemLp (g : Space → Space) 2 (weightedVolume w) :=
  (Lp.memLp g).of_measure_le_smul ENNReal.ofReal_ne_top (weightedVolume_le hC)

theorem ae_weighted {w : Space → ℝ} {P : Space → Prop} (h : ∀ᵐ y, P y) :
    ∀ᵐ y ∂(weightedVolume w), P y :=
  (withDensity_absolutelyContinuous _ _).ae_le h

def weightedLin {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) :
    L2R →ₗ[ℝ] Lp Space 2 (weightedVolume w) where
  toFun g := (memLp_weighted hC g).toLp g
  map_add' g h := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (ae_weighted (Lp.coeFn_add g h))
  map_smul' a g := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_weighted (Lp.coeFn_smul a g))

theorem weightedLin_norm_le {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) (g : L2R) :
    ‖weightedLin hC g‖ ≤ (ENNReal.ofReal C ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖g‖ := by
  change ‖(memLp_weighted hC g).toLp g‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (Lp.eLpNorm_ne_top g)) ?_
  calc eLpNorm (g : Space → Space) 2 (weightedVolume w)
      ≤ eLpNorm (g : Space → Space) 2 (ENNReal.ofReal C • volume) :=
        eLpNorm_mono_measure _ (weightedVolume_le hC)
    _ = _ := by rw [eLpNorm_smul_measure_of_ne_top (by simp)]; rfl

def weightedCLM {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) :
    L2R →L[ℝ] Lp Space 2 (weightedVolume w) :=
  (weightedLin hC).mkContinuous _ (weightedLin_norm_le hC)

theorem weightedCLM_norm_sq {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwm : Measurable w) {C : ℝ}
    (hC : ∀ y, w y ≤ C) (g : L2R) :
    ‖weightedCLM hC g‖ ^ 2 = ∫ y, w y * ‖(g : Space → Space) y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have e : (weightedCLM hC g : Space → Space) =ᵐ[weightedVolume w] (g : Space → Space) :=
    MemLp.coeFn_toLp (memLp_weighted hC g)
  rw [integral_congr_ae (g := fun y => ‖(g : Space → Space) y‖ ^ 2)
    (e.mono fun y hy => by simp only [hy, real_inner_self_eq_norm_sq])]
  rw [weightedVolume, integral_withDensity_eq_integral_smul (hwm.real_toNNReal)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hw0 y), smul_eq_mul]

theorem convexOn_norm_sq_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ConvexOn ℝ Set.univ (fun x => ‖L x‖ ^ 2) := by
  have h1 : ConvexOn ℝ Set.univ (fun x => ‖L x‖) :=
    (convexOn_norm convex_univ).comp_linearMap L.toLinearMap
  exact h1.pow (fun x _ => norm_nonneg _) 2

theorem quadratic_le_of_weak {E F₀ F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L₀ : E →L[ℝ] F₀) (L : Fin 3 → E →L[ℝ] F) (u : ℕ → E) (u₀ : E)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y))) (c : ℝ)
    (hc : ∀ n, ‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 ≤ c) :
    ‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 ≤ c := by
  have hQ : ConvexOn ℝ Set.univ
      (fun x => ‖L₀ x‖ ^ 2 + (‖L 0 x‖ ^ 2 + ‖L 1 x‖ ^ 2 + ‖L 2 x‖ ^ 2)) :=
    (convexOn_norm_sq_comp L₀).add
      (((convexOn_norm_sq_comp (L 0)).add (convexOn_norm_sq_comp (L 1))).add
        (convexOn_norm_sq_comp (L 2)))
  have hK := hQ.convex_le c
  have hcl : IsClosed {x ∈ (Set.univ : Set E) |
      ‖L₀ x‖ ^ 2 + (‖L 0 x‖ ^ 2 + ‖L 1 x‖ ^ 2 + ‖L 2 x‖ ^ 2) ≤ c} := by
    simp only [Set.mem_univ, true_and]
    exact isClosed_le (by fun_prop) continuous_const
  have hm := mem_of_weak_limit _ hK hcl u (fun n => ⟨Set.mem_univ _, by
    have := hc n
    simpa only [Fin.sum_univ_three] using this⟩) u₀ hw
  have := hm.2
  simpa only [Fin.sum_univ_three] using this

theorem integrable_weighted {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (g : L2R) :
    Integrable (fun y => w y * ‖(g : Space → Space) y‖ ^ 2) :=
  (l2_integrable_norm_sq g).bdd_mul hwm.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 y)]
      exact hC y)

theorem sliceWeightedGrad_eq {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (h : Freq.X) :
    sliceWeightedGrad w h = ∑ j : Fin 3, ‖weightedCLM hC (partialX j h)‖ ^ 2 := by
  unfold sliceWeightedGrad
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => integrable_weighted hwm hC hw0 _]
  exact Finset.sum_congr rfl fun j _ => (weightedCLM_norm_sq hw0 hwm hC _).symm

def weightedGradPart {w : Space → ℝ} {C : ℝ} (hC : ∀ y, w y ≤ C) (j : Fin 3) :
    XBar →L[ℝ] Lp Space 2 (weightedVolume w) :=
  (weightedCLM hC).comp ((partialX j).comp gradPart)

theorem weighted_slice_eq {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (q : XBar) :
    sliceWeightedGrad w (gradPart q) = ∑ j : Fin 3, ‖weightedGradPart hC j q‖ ^ 2 :=
  sliceWeightedGrad_eq hwm hC hw0 _

theorem integral_sum_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : Fin 3 → E →L[ℝ] F) (u : Lp E 2 μ) :
    ∫ t, ∑ j : Fin 3, ‖A j (u t)‖ ^ 2 ∂μ = ∑ j : Fin 3, ‖(A j).compLpL 2 μ u‖ ^ 2 := by
  have hi : ∀ j, (fun t => ‖A j (u t)‖ ^ 2) =ᵐ[μ] (fun t => ‖(A j).compLpL 2 μ u t‖ ^ 2) :=
    fun j => (ContinuousLinearMap.coeFn_compLpL (A j) u).mono fun t ht => by dsimp only; rw [ht]
  rw [integral_finsetSum _ fun j _ => (l2_integrable_norm_sq _).congr (hi j).symm]
  exact Finset.sum_congr rfl fun j _ => by
    rw [l2_norm_sq_eq_integral]
    exact integral_congr_ae (hi j)

theorem weighted_integral_eq {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (u : XX) :
    ∫ t, sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t)) =
      ∑ j : Fin 3, ‖(weightedGradPart hC j).compLpL 2 volume u‖ ^ 2 := by
  calc ∫ t, sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t))
      = ∫ t, ∑ j : Fin 3, ‖weightedGradPart hC j ((u : TimeCircle → XBar) t)‖ ^ 2 :=
        integral_congr_ae (Eventually.of_forall fun t => weighted_slice_eq hwm hC hw0 _)
    _ = _ := integral_sum_norm_sq (weightedGradPart hC) u

theorem energyW_eq {w : Space → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ y, w y ≤ C)
    (hw0 : ∀ y, 0 ≤ w y) (v : XX) : energyW w v = ‖secondCLM v‖ ^ 2 +
      ∑ j : Fin 3, ‖(weightedGradPart hC j).compLpL 2 volume v‖ ^ 2 :=
  congrArg (fun x => ‖secondCLM v‖ ^ 2 + x) (weighted_integral_eq hwm hC hw0 v)

theorem sqrt_le_of_weak {E F₀ F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} (L₀ : E →L[ℝ] F₀) (L : Fin 3 → E →L[ℝ] F) (u : ℕ → E) (u₀ : E)
    (hu : ∀ y, Tendsto (fun n => inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y)))
    (κ : ℕ → Fin k → ℝ) (κ₀ : Fin k → ℝ) (hκ : Tendsto κ atTop (𝓝 κ₀)) (B : ℝ)
    (hB : ∀ n, Real.sqrt (‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2) ≤ B) :
    Real.sqrt (‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 + ∑ i, κ₀ i ^ 2) ≤ B := by
  have hB0 : 0 ≤ B := (Real.sqrt_nonneg _).trans (hB 0)
  have hsq : ∀ n, ‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2 ≤ B ^ 2 := fun n => by
    have h1 : 0 ≤ ‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2 := by positivity
    calc ‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2
        = Real.sqrt (‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2) ^ 2 :=
          (Real.sq_sqrt h1).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hB n) 2
  have hκs : Tendsto (fun n => ∑ i, κ n i ^ 2) atTop (𝓝 (∑ i, κ₀ i ^ 2)) :=
    tendsto_finsetSum _ fun i _ => ((continuous_apply i).tendsto κ₀ |>.comp hκ).pow 2
  have hlim : ‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 ≤ B ^ 2 - ∑ i, κ₀ i ^ 2 := by
    by_contra hcon
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 - (B ^ 2 - ∑ i, κ₀ i ^ 2)) / 2 :=
      ⟨_, rfl⟩
    have hεpos : 0 < ε := by rw [hε]; linarith [not_le.1 hcon]
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hκs.eventually (Ioi_mem_nhds
      (show ∑ i, κ₀ i ^ 2 - ε < ∑ i, κ₀ i ^ 2 by linarith)))
    have hc : ∀ n, ‖L₀ (u (n + N))‖ ^ 2 + ∑ j, ‖L j (u (n + N))‖ ^ 2 ≤
        B ^ 2 - ∑ i, κ₀ i ^ 2 + ε := fun n => by
      have h1 := hsq (n + N)
      have h2 : ∑ i, κ₀ i ^ 2 - ε < ∑ i, κ (n + N) i ^ 2 := hN (n + N) (Nat.le_add_left N n)
      linarith
    have h := quadratic_le_of_weak L₀ L (fun n => u (n + N)) u₀
      (fun y => (hu y).comp (tendsto_add_atTop_nat N)) _ hc
    linarith [not_le.1 hcon]
  calc Real.sqrt (‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 + ∑ i, κ₀ i ^ 2) ≤ Real.sqrt (B ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
    _ = B := Real.sqrt_sq hB0

theorem sizeZ_le_of_weak {k : ℕ} {w : Space → ℝ} {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀)
    (u : ℕ → XX) (u₀ : XX) (κ : ℕ → Fin k → ℝ) (κ₀ : Fin k → ℝ)
    (hu : ∀ y, Tendsto (fun n => inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y)))
    (hκ : Tendsto κ atTop (𝓝 κ₀)) (B : ℝ) (hB : ∀ n, sizeZ w (u n) (κ n) ≤ B) :
    sizeZ w u₀ κ₀ ≤ B := by
  obtain ⟨hw₀, hwm, hlow, C, hC⟩ := hw
  have hw0 : ∀ y, 0 ≤ w y := fun y => hw₀.le.trans (hlow y)
  have hE := energyW_eq hwm hC hw0
  have hB' : ∀ n, Real.sqrt (‖secondCLM (u n)‖ ^ 2 +
      ∑ j : Fin 3, ‖(weightedGradPart hC j).compLpL 2 volume (u n)‖ ^ 2 + ∑ i, κ n i ^ 2) ≤ B :=
    fun n => by
      rw [← hE]
      exact hB n
  have h := sqrt_le_of_weak secondCLM (fun j => (weightedGradPart hC j).compLpL 2 volume)
    u u₀ hu κ κ₀ hκ B hB'
  rw [← hE] at h
  exact h

theorem isReadingOf_readingOf (h12 : ReadingExistsHolds) (u : XX) :
    IsReadingOf u (readingOf u).1 (readingOf u).2.1 (readingOf u).2.2 := by
  have h : ∃ r : VelField × GradField × SecondField, IsReadingOf u r.1 r.2.1 r.2.2 := by
    obtain ⟨v, G, H, hr, -⟩ := h12 u
    exact ⟨(v, G, H), hr⟩
  unfold readingOf
  rw [dif_pos h]
  exact h.choose_spec

theorem periodBallLIntegral_mono {R : ℝ} {f g : ℝ → Space → ℝ} (h : ∀ σ y, f σ y ≤ g σ y) :
    periodBallLIntegral R f ≤ periodBallLIntegral R g := by
  unfold periodBallLIntegral
  exact lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (h σ y)

theorem sq_component_le (x : Space) (j : Fin 3) : ‖x j‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x j) 2

theorem column_integral_tendsto (v : ℕ → VelField) (G : ℕ → GradField) (v₀ : VelField)
    (G₀ : GradField)
    (hv : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => v n z.1 z.2) volume)
    (hG : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => G n z.1 z.2) volume)
    (hv₀ : AEStronglyMeasurable (fun z : ℝ × Space => v₀ z.1 z.2) volume)
    (hG₀ : AEStronglyMeasurable (fun z : ℝ × Space => G₀ z.1 z.2) volume)
    (hpv : ∀ n, IsTimePeriodic (v n)) (hpG : ∀ n, IsTimePeriodic (G n))
    (hpv₀ : IsTimePeriodic v₀) (hpG₀ : IsTimePeriodic G₀)
    (hloc : IsLocalReadingLimit v G v₀ G₀)
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestField φ) (j : Fin 3) :
    (∀ᶠ n in atTop, Integrable (fun z : ℝ × Space =>
      (v n z.1 z.2) j * inner ℝ (gradColumn (G n) j z.1 z.2) (φ z.1 z.2))) ∧
    Integrable (fun z : ℝ × Space => (v₀ z.1 z.2) j * inner ℝ (gradColumn G₀ j z.1 z.2) (φ z.1 z.2)) ∧
    Tendsto (fun n => ∫ z : ℝ × Space,
      (v n z.1 z.2) j * inner ℝ (gradColumn (G n) j z.1 z.2) (φ z.1 z.2)) atTop
      (𝓝 (∫ z : ℝ × Space, (v₀ z.1 z.2) j * inner ℝ (gradColumn G₀ j z.1 z.2) (φ z.1 z.2))) :=
  scalar_product_integral_tendsto (fun n σ y => (v n σ y) j) (fun n => gradColumn (G n) j)
    (fun σ y => (v₀ σ y) j) (gradColumn G₀ j)
    (fun n => (EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable (hv n))
    (fun n => (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable (hG n))
    ((EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable hv₀)
    ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hG₀)
    (fun n σ y => by simp only [hpv n σ y]) (fun n σ y => by simp only [gradColumn, hpG n σ y])
    (fun σ y => by simp only [hpv₀ σ y]) (fun σ y => by simp only [gradColumn, hpG₀ σ y])
    (fun R hR => lt_of_le_of_lt (periodBallLIntegral_mono fun σ y => sq_component_le _ j)
      (hloc R hR).1)
    (fun R hR => (hloc R hR).2.1 j)
    (fun R hR => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hloc R hR).2.2.1
      (fun _ => zero_le) (fun n => periodBallLIntegral_mono fun σ y => by
        have := sq_component_le (v n σ y - v₀ σ y) j
        simpa only [PiLp.sub_apply] using this))
    (fun R hR => (hloc R hR).2.2.2 j) φ hφ

theorem apply_eq_sum (A : Space →L[ℝ] Space) (x : Space) :
    A x = ∑ j : Fin 3, x j • A (unitVector j) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    unitVector]

theorem inner_apply_eq_sum (A : Space →L[ℝ] Space) (x w : Space) :
    inner ℝ (A x) w = ∑ j : Fin 3, x j * inner ℝ (A (unitVector j)) w := by
  rw [apply_eq_sum A x, sum_inner]
  exact Finset.sum_congr rfl fun j _ => real_inner_smul_left _ _ _

theorem tendsto_integral_apply (v : ℕ → VelField) (G : ℕ → GradField) (v₀ : VelField)
    (G₀ : GradField)
    (hv : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => v n z.1 z.2) volume)
    (hG : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => G n z.1 z.2) volume)
    (hv₀ : AEStronglyMeasurable (fun z : ℝ × Space => v₀ z.1 z.2) volume)
    (hG₀ : AEStronglyMeasurable (fun z : ℝ × Space => G₀ z.1 z.2) volume)
    (hpv : ∀ n, IsTimePeriodic (v n)) (hpG : ∀ n, IsTimePeriodic (G n))
    (hpv₀ : IsTimePeriodic v₀) (hpG₀ : IsTimePeriodic G₀)
    (hloc : IsLocalReadingLimit v G v₀ G₀)
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestField φ) :
    Tendsto (fun n => ∫ z : ℝ × Space, inner ℝ (G n z.1 z.2 (v n z.1 z.2)) (φ z.1 z.2)) atTop
      (𝓝 (∫ z : ℝ × Space, inner ℝ (G₀ z.1 z.2 (v₀ z.1 z.2)) (φ z.1 z.2))) := by
  have hc := fun j => column_integral_tendsto v G v₀ G₀ hv hG hv₀ hG₀ hpv hpG hpv₀ hpG₀ hloc φ hφ j
  have hall : ∀ᶠ n in atTop, ∀ j : Fin 3, Integrable (fun z : ℝ × Space =>
      (v n z.1 z.2) j * inner ℝ (gradColumn (G n) j z.1 z.2) (φ z.1 z.2)) :=
    eventually_all.2 fun j => (hc j).1
  have e : (fun n => ∑ j : Fin 3, ∫ z : ℝ × Space,
      (v n z.1 z.2) j * inner ℝ (gradColumn (G n) j z.1 z.2) (φ z.1 z.2)) =ᶠ[atTop]
      fun n => ∫ z : ℝ × Space, inner ℝ (G n z.1 z.2 (v n z.1 z.2)) (φ z.1 z.2) := by
    filter_upwards [hall] with n hn
    rw [← integral_finsetSum _ fun j _ => hn j]
    exact (integral_congr_ae (Eventually.of_forall fun z => inner_apply_eq_sum _ _ _)).symm
  have e₀ : ∫ z : ℝ × Space, inner ℝ (G₀ z.1 z.2 (v₀ z.1 z.2)) (φ z.1 z.2) =
      ∑ j : Fin 3, ∫ z : ℝ × Space,
        (v₀ z.1 z.2) j * inner ℝ (gradColumn G₀ j z.1 z.2) (φ z.1 z.2) := by
    rw [← integral_finsetSum _ fun j _ => (hc j).2.1]
    exact integral_congr_ae (Eventually.of_forall fun z => inner_apply_eq_sum _ _ _)
  rw [e₀]
  exact (tendsto_finsetSum _ fun j _ => (hc j).2.2).congr' e

theorem tendsto_inner_productH_of_local (h5 : ProductPairingHolds) (h12 : ReadingExistsHolds)
    (P : ℕ → ℝ) (P₀ : ℝ) (f : ℕ → HH) (f₀ : HH) (ψ : ℕ → ℕ)
    (hSn : ∀ n, supGrad (freeInv (P (ψ n)) (f (ψ n))) < ⊤) (hS₀ : supGrad (freeInv P₀ f₀) < ⊤)
    (hloc : IsLocalReadingLimit (fun n => (readingOf (freeInv (P (ψ n)) (f (ψ n)))).1)
      (fun n => (readingOf (freeInv (P (ψ n)) (f (ψ n)))).2.1) (readingOf (freeInv P₀ f₀)).1
      (readingOf (freeInv P₀ f₀)).2.1)
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestField φ) :
    Tendsto (fun n => inner ℝ (productH (freeInv (P (ψ n)) (f (ψ n)))
        (freeInv (P (ψ n)) (f (ψ n)))) (testInHH φ)) atTop
      (𝓝 (inner ℝ (productH (freeInv P₀ f₀) (freeInv P₀ f₀)) (testInHH φ))) := by
  have e : ∀ n, inner ℝ (productH (freeInv (P (ψ n)) (f (ψ n))) (freeInv (P (ψ n)) (f (ψ n))))
      (testInHH φ) = ∫ z : ℝ × Space,
        inner ℝ ((readingOf (freeInv (P (ψ n)) (f (ψ n)))).2.1 z.1 z.2
          ((readingOf (freeInv (P (ψ n)) (f (ψ n)))).1 z.1 z.2)) (φ z.1 z.2) :=
    fun n => h5 _ _ (hSn n) φ hφ
  have e₀ : inner ℝ (productH (freeInv P₀ f₀) (freeInv P₀ f₀)) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ ((readingOf (freeInv P₀ f₀)).2.1 z.1 z.2
        ((readingOf (freeInv P₀ f₀)).1 z.1 z.2)) (φ z.1 z.2) := h5 _ _ hS₀ φ hφ
  have r := fun n => isReadingOf_readingOf h12 (freeInv (P (ψ n)) (f (ψ n)))
  have r₀ := isReadingOf_readingOf h12 (freeInv P₀ f₀)
  have key : Tendsto (fun n => inner ℝ (productH (freeInv (P (ψ n)) (f (ψ n)))
      (freeInv (P (ψ n)) (f (ψ n)))) (testInHH φ)) atTop
      (𝓝 (∫ z : ℝ × Space, inner ℝ ((readingOf (freeInv P₀ f₀)).2.1 z.1 z.2
        ((readingOf (freeInv P₀ f₀)).1 z.1 z.2)) (φ z.1 z.2))) := by
    refine Tendsto.congr (fun n => (e n).symm) ?_
    exact tendsto_integral_apply (fun n => (readingOf (freeInv (P (ψ n)) (f (ψ n)))).1)
      (fun n => (readingOf (freeInv (P (ψ n)) (f (ψ n)))).2.1) (readingOf (freeInv P₀ f₀)).1
      (readingOf (freeInv P₀ f₀)).2.1 (fun n => (r n).measurable_velocity)
      (fun n => (r n).measurable_gradient) r₀.measurable_velocity r₀.measurable_gradient
      (fun n => (r n).periodic_velocity) (fun n => (r n).periodic_gradient)
      r₀.periodic_velocity r₀.periodic_gradient hloc φ hφ
  exact (congrArg (fun x : ℝ => Tendsto (fun n => inner ℝ (productH (freeInv (P (ψ n)) (f (ψ n)))
    (freeInv (P (ψ n)) (f (ψ n)))) (testInHH φ)) atTop (𝓝 x)) e₀).mpr key

theorem tendsto_inner_productH (h1 : PeriodContinuityHolds) (h2 : LocalCompactnessHolds)
    (h5 : ProductPairingHolds) (h9 : FreeInvHolds) (h12 : ReadingExistsHolds) (a b S : ℝ)
    (ha : 0 < a) (P : ℕ → ℝ) (P₀ : ℝ) (f : ℕ → HH) (f₀ : HH) (hP : ∀ n, P n ∈ Set.Icc a b)
    (hP₀ : Tendsto P atTop (𝓝 P₀)) (C : ℝ) (hC : ∀ n, ‖f n‖ ≤ C)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (f n) y) atTop (𝓝 (inner ℝ f₀ y)))
    (hS : ∀ n, supGrad (freeInv (P n) (f n)) ≤ ENNReal.ofReal S) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ φ, IsSpaceTimeTestField φ →
      Tendsto (fun n => inner ℝ (productH (freeInv (P (ψ n)) (f (ψ n)))
          (freeInv (P (ψ n)) (f (ψ n)))) (testInHH φ)) atTop
        (𝓝 (inner ℝ (productH (freeInv P₀ f₀) (freeInv P₀ f₀)) (testInHH φ))) := by
  have hP₀a : P₀ ∈ Set.Icc a b :=
    isClosed_Icc.mem_of_tendsto hP₀ (Eventually.of_forall hP)
  have hwu : ∀ y, Tendsto (fun n => inner ℝ (freeInv (P n) (f n)) y) atTop
      (𝓝 (inner ℝ (freeInv P₀ f₀) y)) :=
    h1 P P₀ f f₀ (ha.trans_le hP₀a.1) (fun n => ha.trans_le (hP n).1) hP₀ ⟨C, hC⟩ hw
  have hS₀ : supGrad (freeInv P₀ f₀) < ⊤ :=
    lt_of_le_of_lt (supGrad_le_of_weak S _ _ hwu hS) ENNReal.ofReal_lt_top
  exact (reading_tendsto_local h1 h2 h9 h12 a b ha P P₀ f f₀ hP hP₀ C hC hw).imp fun ψ h =>
    ⟨h.1, tendsto_inner_productH_of_local h5 h12 P P₀ f f₀ ψ
      (fun n => lt_of_le_of_lt (hS (ψ n)) ENNReal.ofReal_lt_top) hS₀ h.2⟩

end Internal.HeldLimit

open Internal.HeldLimit in
theorem heldLimitHolds_of (h1 : PeriodContinuityHolds) (h2 : LocalCompactnessHolds)
    (h3 : ConvectionContinuityHolds) (h4 : DataContinuityHolds) (h5 : ProductPairingHolds)
    (h6 : ProductBoundHolds) (h7 : HeldMetricHolds) (h8 : InvarianceHolds) (h9 : FreeInvHolds)
    (h10 : ConvectionHolds) (h11 : DataHolds) (h12 : ReadingExistsHolds) (h13 : TestDenseHolds) :
    HeldLimitHolds := by
  intro k d hd p q hp hq hpq f κ hsol
  have hwpos : ∀ y, 0 ≤ d.weightFn y := fun y => hd.weight_pos.le.trans (hd.weightFn_lower y)
  have hadm : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hS0 := hd.supBound_pos.le
  have hB0 := hd.sizeBound_nonneg
  have hsupfin : ∀ n, supGrad (freeInv (d.period (p n)) (f n)) < ⊤ :=
    fun n => lt_of_le_of_lt (hsol n).sup ENNReal.ofReal_lt_top
  have hsupR : ∀ n, (supGrad (freeInv (d.period (p n)) (f n))).toReal ≤ d.supBound :=
    fun n => ENNReal.toReal_le_of_le_ofReal hS0 (hsol n).sup
  have hE : ∀ n, Real.sqrt (energyW d.weightFn (freeInv (d.period (p n)) (f n))) ≤
      2 * d.sizeBound :=
    fun n => (sqrt_energyW_le_sizeZ _ _ (κ n)).trans (hsol n).size
  have hsec : ∀ n, ‖secondCLM (freeInv (d.period (p n)) (f n))‖ ≤ 2 * d.sizeBound := by
    intro n
    calc ‖secondCLM (freeInv (d.period (p n)) (f n))‖
        = Real.sqrt (‖secondCLM (freeInv (d.period (p n)) (f n))‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (energyW d.weightFn (freeInv (d.period (p n)) (f n))) :=
          Real.sqrt_le_sqrt (secondCLM_sq_le hwpos _)
      _ ≤ _ := hE n
  have hgr : ∀ n, ‖gradCLM (freeInv (d.period (p n)) (f n))‖ ≤ d.supBound :=
    fun n => (gradCLM_norm_le _ (hsupfin n)).trans (hsupR n)
  have hub : ∀ n, ‖freeInv (d.period (p n)) (f n)‖ ≤ d.supBound + 2 * d.sizeBound :=
    fun n => (norm_le_add _).trans (add_le_add (hgr n) (hsec n))
  have hvκ : ∀ n, vecNorm (κ n) ≤ 2 * d.sizeBound :=
    fun n => (vecNorm_le_sizeZ hwpos _ _).trans (hsol n).size
  have hpw : Tendsto p atTop (𝓝[d.box] q) :=
    tendsto_nhdsWithin_iff.2 ⟨hpq, Eventually.of_forall hp⟩
  have hconvT : Tendsto (fun n => convection d (p n)) atTop (𝓝 (convection d q)) :=
    ((h3 d hd) q hq).tendsto.comp hpw
  obtain ⟨Cc, hCc0, hCc⟩ := exists_bound_of_tendsto _ _ hconvT
  have hag : 0 ≤ supBoundFactor d.weight := by
    unfold supBoundFactor
    positivity
  have hfb : ∀ n, ‖f n‖ ≤ Cc * (d.supBound + 2 * d.sizeBound) + d.actuatorBound * (2 * d.sizeBound)
      + supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound + d.defectMax := by
    intro n
    have hD := h11 d hd (p n) (hp n)
    have e1 : ‖convection d (p n) (freeInv (d.period (p n)) (f n))‖ ≤
        Cc * (d.supBound + 2 * d.sizeBound) :=
      (hCc n _).trans (mul_le_mul_of_nonneg_left (hub n) hCc0)
    have e2 : ‖actuatorH d (κ n)‖ ≤ d.actuatorBound * (2 * d.sizeBound) :=
      (hD.2.2.2.1 (κ n)).trans (mul_le_mul_of_nonneg_left (hvκ n) hd.actuatorBound_nonneg)
    have e3 : ‖productH (freeInv (d.period (p n)) (f n)) (freeInv (d.period (p n)) (f n))‖ ≤
        supBoundFactor d.weight * (2 * d.sizeBound) * d.supBound :=
      ((h6 _ _ hadm _ _ (hsupfin n)).2.2).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hE n) hag)
        (hsupR n) ENNReal.toReal_nonneg (mul_nonneg hag (by linarith)))
    have e4 : ‖defectH d (p n)‖ ≤ d.defectMax := hD.2.1.trans (hd.defect_le _ (hp n))
    exact (norm_le_of_add_eq_zero (hsol n).equation).trans
      (add_le_add (add_le_add (add_le_add e1 e2) e3) e4)
  obtain ⟨s1, f₀, hs1, -, hw1⟩ := exists_weakly_convergent_subseq f _ hfb
  obtain ⟨κ₀, -, s2, hs2, hκ2⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := 2 * d.sizeBound))
    (x := fun n => κ (s1 n))
    (fun n => mem_closedBall_zero_iff.2 ((norm_le_vecNorm _).trans (hvκ (s1 n))))
  obtain ⟨pm, hpm, hmin⟩ := (show IsCompact d.box from isCompact_Icc).exists_isMinOn ⟨q, hq⟩
    hd.period_continuous
  have hpa : ∀ n, d.period (p n) ∈ Set.Icc (d.period pm) d.periodMax :=
    fun n => ⟨isMinOn_iff.1 hmin _ (hp n), hd.period_le _ (hp n)⟩
  have hPt : Tendsto (fun n => d.period (p n)) atTop (𝓝 (d.period q)) :=
    (hd.period_continuous q hq).tendsto.comp hpw
  obtain ⟨s3, hs3, hprod⟩ := tendsto_inner_productH h1 h2 h5 h9 h12 (d.period pm) d.periodMax
    d.supBound (hd.period_pos pm hpm) (fun n => d.period (p (s1 (s2 n)))) (d.period q)
    (fun n => f (s1 (s2 n))) f₀ (fun n => hpa _) (hPt.comp (hs1.comp hs2).tendsto_atTop) _
    (fun n => hfb _) (fun y => (hw1 y).comp hs2.tendsto_atTop) (fun n => (hsol _).sup)
  have hs : StrictMono (fun n => s1 (s2 (s3 n))) := hs1.comp (hs2.comp hs3)
  have hwf : ∀ y, Tendsto (fun n => inner ℝ (f (s1 (s2 (s3 n)))) y) atTop (𝓝 (inner ℝ f₀ y)) :=
    fun y => ((hw1 y).comp hs2.tendsto_atTop).comp hs3.tendsto_atTop
  have hκ : Tendsto (fun n => κ (s1 (s2 (s3 n)))) atTop (𝓝 κ₀) := hκ2.comp hs3.tendsto_atTop
  have hps : Tendsto (fun n => p (s1 (s2 (s3 n)))) atTop (𝓝[d.box] q) :=
    hpw.comp hs.tendsto_atTop
  have hwu : ∀ y, Tendsto (fun n => inner ℝ (freeInv (d.period (p (s1 (s2 (s3 n)))))
      (f (s1 (s2 (s3 n))))) y) atTop (𝓝 (inner ℝ (freeInv (d.period q) f₀) y)) :=
    h1 (fun n => d.period (p (s1 (s2 (s3 n))))) (d.period q) (fun n => f (s1 (s2 (s3 n)))) f₀
      (hd.period_pos q hq) (fun n => hd.period_pos _ (hp _)) (hPt.comp hs.tendsto_atTop)
      ⟨_, fun n => hfb _⟩ hwf
  refine ⟨fun n => s1 (s2 (s3 n)), hs, f₀, κ₀, ⟨?_, ?_, ?_, ?_, ?_⟩, hκ⟩
  · exact mem_of_weak_limit (invariantHH d.symmetries : Set HH) (Submodule.convex _)
      (isClosed_invariantHH _) (fun n => f (s1 (s2 (s3 n)))) (fun n => (hsol _).invariant) f₀ hwf
  · apply h13
    intro g hg
    have hA := hwf (testInHH g)
    have hB := tendsto_inner_clm_apply (fun n => convection d (p (s1 (s2 (s3 n)))))
      (convection d q) _ _ _ (hconvT.comp hs.tendsto_atTop) (fun n => hub _) hwu (testInHH g)
    have hC : Tendsto (fun n => inner ℝ (actuatorH d (κ (s1 (s2 (s3 n))))) (testInHH g)) atTop
        (𝓝 (inner ℝ (actuatorH d κ₀) (testInHH g))) :=
      (((actuatorH d).continuous.tendsto κ₀).comp hκ).inner tendsto_const_nhds
    have hDf : Tendsto (fun n => inner ℝ (defectH d (p (s1 (s2 (s3 n))))) (testInHH g)) atTop
        (𝓝 (inner ℝ (defectH d q) (testInHH g))) :=
      (((h4 d hd).2 g hg) q hq).tendsto.comp hps
    exact inner_sum_eq_zero_of_tendsto (testInHH g) (fun n => f (s1 (s2 (s3 n))))
      (fun n => convection d (p (s1 (s2 (s3 n))))
        (freeInv (d.period (p (s1 (s2 (s3 n))))) (f (s1 (s2 (s3 n))))))
      (fun n => actuatorH d (κ (s1 (s2 (s3 n)))))
      (fun n => productH (freeInv (d.period (p (s1 (s2 (s3 n))))) (f (s1 (s2 (s3 n)))))
        (freeInv (d.period (p (s1 (s2 (s3 n))))) (f (s1 (s2 (s3 n))))))
      (fun n => defectH d (p (s1 (s2 (s3 n))))) _ _ _ _ _ hA hB hC (hprod g hg) hDf
      (fun n => (hsol _).equation)
  · have ha := tendsto_clm_of_weak (pinMap d) _ _ hwu
    have hb : Tendsto (fun n => targetGap d (p (s1 (s2 (s3 n))))) atTop (𝓝 (targetGap d q)) :=
      ((h4 d hd).1 q hq).tendsto.comp hps
    exact tendsto_nhds_unique ha (hb.congr fun n => (hsol _).pins.symm)
  · exact sizeZ_le_of_weak hadm _ _ _ _ hwu hκ _ (fun n => (hsol _).size)
  · exact supGrad_le_of_weak _ _ _ hwu (fun n => (hsol _).sup)

end Breakdown.Cert
