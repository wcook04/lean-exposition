import Breakdown.Cert.Nodes
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.DenseEnergyCurveBand

open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown.Cert

open Freq


theorem exists_dense_energyCurve (h0 : PropagatorBoundHolds) (h1 : GradInvHolds)
    (h2 : GraphClosedHolds) {P : ℝ} (hP : 0 < P) :
    ∃ D : Submodule ℝ HH, Dense (D : Set HH) ∧ ∀ f ∈ D, ∃ (k : HH) (c : ℝ → Freq.X),
      Continuous c ∧ (∀ σ, c (σ + 1) = c σ) ∧
      (∀ᵐ σ : ℝ, c σ = (gradInv P f : TimeCircle → HBar) (σ : TimeCircle)) ∧
      (∀ᵐ t : TimeCircle, IsHalfSspOf ((gradInv P f : TimeCircle → HBar) t)
        ((k : TimeCircle → HBar) t)) ∧
      ∀ a b : ℝ, a ≤ b → (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
        ∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
            ((k : TimeCircle → HBar) (σ : TimeCircle))
          - ‖(k : TimeCircle → HBar) (σ : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2) := by
  exact exists_dense_energyCurve_band h0 h1 h2 hP

namespace Internal.FreeInv

theorem second_eq_of_halfSsp (x k k' : Freq.X) (h : Freq.IsHalfSspOf x k)
    (h' : Freq.IsHalfSspOf x k') : k = k' := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [h, h'] with ξ h1 h2
  rw [h1, h2]

theorem gradPart_injective (h2 : GraphClosedHolds) : Function.Injective gradPart := by
  intro q q' hqq
  have h' : IsHalfSspOf (gradPart q) (secondPart q') := by
    rw [hqq]
    exact h2 q'
  have hk : secondPart q = secondPart q' := second_eq_of_halfSsp (gradPart q) _ _ (h2 q) h'
  exact Subtype.ext ((WithLp.ext_iff 2).2 (Prod.ext hqq hk))

theorem gradCLM_ae (u : XX) :
    ∀ᵐ t ∂(volume : Measure TimeCircle), (gradCLM u : TimeCircle → HBar) t = gradPart (u t) :=
  ContinuousLinearMap.coeFn_compLpL gradPart u

theorem secondCLM_ae (u : XX) :
    ∀ᵐ t ∂(volume : Measure TimeCircle), (secondCLM u : TimeCircle → HBar) t = secondPart (u t) :=
  ContinuousLinearMap.coeFn_compLpL secondPart u

theorem gradCLM_injective (h2 : GraphClosedHolds) : Function.Injective gradCLM := by
  intro u u' huu
  apply Lp.ext
  filter_upwards [gradCLM_ae u, gradCLM_ae u'] with t ht ht'
  apply gradPart_injective h2
  have he := congrArg (fun w : HH => (w : TimeCircle → HBar) t) huu
  exact ht.symm.trans (he.trans ht')

theorem norm_xbar_le (q : XBar) : ‖q‖ ≤ ‖gradPart q‖ + ‖secondPart q‖ := by
  have hsq : ‖q‖ ^ 2 = ‖gradPart q‖ ^ 2 + ‖secondPart q‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 (q : WithLp 2 (Freq.X × Freq.X))
  have h0 : 0 ≤ ‖gradPart q‖ := norm_nonneg _
  have h0' : 0 ≤ ‖secondPart q‖ := norm_nonneg _
  nlinarith [norm_nonneg q]


theorem norm_le_compLpL_add {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L₁ : E →L[ℝ] F) (L₂ : E →L[ℝ] G) (hL : ∀ x, ‖x‖ ≤ ‖L₁ x‖ + ‖L₂ x‖)
    (u : Lp (α := TimeCircle) E 2) :
    ‖u‖ ≤ ‖L₁.compLpL 2 volume u‖ + ‖L₂.compLpL 2 volume u‖ := by
  have hle : ∀ᵐ t ∂(volume : Measure TimeCircle),
      ‖(u : TimeCircle → E) t‖ ≤ ‖(fun t => ‖(L₁.compLpL 2 volume u : TimeCircle → F) t‖) t
        + (fun t => ‖(L₂.compLpL 2 volume u : TimeCircle → G) t‖) t‖ := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL L₁ u,
      ContinuousLinearMap.coeFn_compLpL L₂ u] with t ht hst
    rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), ht, hst]
    exact hL _
  have h1 := eLpNorm_mono_ae (p := 2) hle
  have h2 := eLpNorm_add_le (p := 2) (μ := (volume : Measure TimeCircle))
    (Lp.aestronglyMeasurable (L₁.compLpL 2 volume u)).norm
    (Lp.aestronglyMeasurable (L₂.compLpL 2 volume u)).norm (by norm_num)
  rw [eLpNorm_norm, eLpNorm_norm] at h2
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_add (Lp.eLpNorm_ne_top _)
    (Lp.eLpNorm_ne_top _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨Lp.eLpNorm_ne_top _, Lp.eLpNorm_ne_top _⟩)
    (h1.trans h2)

theorem norm_XX_le (u : XX) : ‖u‖ ≤ ‖gradCLM u‖ + ‖secondCLM u‖ :=
  norm_le_compLpL_add gradPart secondPart norm_xbar_le u

theorem bound_of_le_inner {a b c : ℝ} (hc : 0 ≤ c) (x : ℝ)
    (hx : x ≤ c * a) (h : a ^ 2 + (1 / 4 : ℝ) * b ^ 2 ≤ x) :
    a ^ 2 + (1 / 4 : ℝ) * b ^ 2 ≤ c ^ 2 ∧ a ≤ c ∧ b ≤ 2 * c := by
  have hac : a ≤ c := by nlinarith
  have hfin : a ^ 2 + (1 / 4 : ℝ) * b ^ 2 ≤ c ^ 2 := by nlinarith
  refine ⟨hfin, hac, ?_⟩
  nlinarith


theorem exists_extension {V W Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : W →L[ℝ] Y) (s : W →L[ℝ] V) (A : V →L[ℝ] Y) (hg : Function.Injective g)
    (hn : ∀ w, ‖w‖ ≤ ‖g w‖ + ‖s w‖) (D : Submodule ℝ V) (hD : Dense (D : Set V))
    (hDu : ∀ f ∈ D, ∃ w : W, g w = A f ∧
      ‖s w‖ ^ 2 + (1 / 4 : ℝ) * ‖g w‖ ^ 2 ≤ inner ℝ f (s w)) :
    ∃ T : V →L[ℝ] W, (∀ f, g (T f) = A f) ∧ ∀ f : V,
      ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  choose U hU hUb using hDu
  have hbd : ∀ f (hf : f ∈ D), ‖s (U f hf)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (U f hf)‖ ^ 2
      ≤ ‖f‖ ^ 2 ∧ ‖s (U f hf)‖ ≤ ‖f‖ ∧ ‖g (U f hf)‖ ≤ 2 * ‖f‖ := fun f hf =>
    bound_of_le_inner (norm_nonneg _) _ (real_inner_le_norm _ _) (hUb f hf)
  have hUeq : ∀ (f : D) (w : W), g w = A f → U f f.2 = w := fun f w hw =>
    hg ((hU f f.2).trans hw.symm)
  let Φ : D →ₗ[ℝ] W :=
    { toFun := fun f => U f f.2
      map_add' := fun f f' => hUeq (f + f') (U f f.2 + U f' f'.2) (by
        rw [map_add, hU, hU, Submodule.coe_add, map_add])
      map_smul' := fun c f => hUeq (c • f) (c • U f f.2) (by
        rw [map_smul, hU, Submodule.coe_smul, map_smul]) }
  have hΦ : ∀ f : D, ‖Φ f‖ ≤ 3 * ‖f‖ := fun f => by
    have h := hbd f f.2
    have := hn (U f f.2)
    show ‖U f f.2‖ ≤ 3 * ‖(f : V)‖
    linarith [h.2.1, h.2.2]
  let Φc : D →L[ℝ] W := Φ.mkContinuous 3 hΦ
  have hdense : DenseRange D.subtypeL := hD.denseRange_val
  have hind : IsUniformInducing D.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  let T : V →L[ℝ] W := Φc.extend D.subtypeL
  have hT : ∀ f : D, T f = U f f.2 := fun f =>
    ContinuousLinearMap.extend_eq Φc hdense hind f
  have hspec : ∀ f, g (T f) = A f := by
    have heq : (fun f => g (T f)) = fun f => A f := by
      refine hdense.equalizer (g.continuous.comp T.continuous) A.continuous ?_
      funext f
      show g (T f) = A f
      rw [hT]
      exact hU f f.2
    exact fun f => congrFun heq f
  refine ⟨T, hspec, ?_⟩
  have hcl : IsClosed {f : V | ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2} := by
    apply isClosed_le
    · fun_prop
    · fun_prop
  have hsub : (D : Set V) ⊆ {f : V | ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2} :=
    fun f hf => by
      show ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2
      have e : T f = U f hf := hT ⟨f, hf⟩
      rw [e]
      exact (hbd f hf).1
  intro f
  exact (hcl.closure_subset_iff.2 hsub) (hD.closure_eq ▸ Set.mem_univ f)

theorem exists_freeInvSpec_bound (h2 : GraphClosedHolds) {P : ℝ} (D : Submodule ℝ HH)
    (hD : Dense (D : Set HH)) (hDu : ∀ f ∈ D, ∃ u : XX, gradCLM u = gradInv P f ∧
      ‖secondCLM u‖ ^ 2 + (1 / 4 : ℝ) * ‖gradCLM u‖ ^ 2 ≤ inner ℝ f (secondCLM u)) :
    ∃ T : HH →L[ℝ] XX, FreeInvSpec P T ∧ ∀ f : HH,
      ‖secondCLM (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖gradCLM (T f)‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  exists_extension gradCLM secondCLM (gradInv P) (gradCLM_injective h2) norm_XX_le D hD hDu

theorem norm_toLp_le {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖WithLp.toLp 2 (a, b)‖ ≤ ‖a‖ + ‖b‖ := by
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (a, b))
  have h0 : 0 ≤ ‖a‖ := norm_nonneg _
  have h0' : 0 ≤ ‖b‖ := norm_nonneg _
  have h1 : ‖(WithLp.toLp 2 (a, b)).fst‖ = ‖a‖ := rfl
  have h2 : ‖(WithLp.toLp 2 (a, b)).snd‖ = ‖b‖ := rfl
  rw [h1, h2] at hsq
  nlinarith [norm_nonneg (WithLp.toLp 2 (a, b))]


theorem exists_pair_lift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ (WithLp 2 (E × E))) [K.HasOrthogonalProjection]
    (v k : TimeCircle → E) (hv : MemLp v 2 volume) (hk : MemLp k 2 volume)
    (hvk : ∀ᵐ t ∂(volume : Measure TimeCircle), WithLp.toLp 2 (v t, k t) ∈ K) :
    ∃ w : TimeCircle → K, MemLp w 2 volume ∧
      ∀ᵐ t ∂(volume : Measure TimeCircle), ((w t : K) : WithLp 2 (E × E)) = WithLp.toLp 2 (v t, k t) := by
  refine ⟨fun t => K.orthogonalProjectionOnto (WithLp.toLp 2 (v t, k t)), ?_, ?_⟩
  · have hmeas : AEStronglyMeasurable (fun t => K.orthogonalProjectionOnto (WithLp.toLp 2 (v t, k t))) volume :=
      (K.orthogonalProjectionOnto.continuous.comp
        (WithLp.prod_continuous_toLp 2 E E)).comp_aestronglyMeasurable
        (hv.aestronglyMeasurable.prodMk hk.aestronglyMeasurable)
    refine (hv.norm.add hk.norm).of_le hmeas (Filter.Eventually.of_forall fun t => ?_)
    rw [Pi.add_apply, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    refine (Submodule.norm_coe _).symm.le.trans ?_
    refine (K.norm_orthogonalProjectionOnto_apply_le _).trans ?_
    exact norm_toLp_le _ _
  · filter_upwards [hvk] with t ht
    exact congrArg Subtype.val (K.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, ht⟩)

theorem norm_sq_Lp_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : Lp (α := TimeCircle) E 2) : ‖k‖ ^ 2 = ∫ t, ‖(k : TimeCircle → E) t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext t
  exact real_inner_self_eq_norm_sq _

theorem period_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f k v : Lp (α := TimeCircle) E 2) (c : ℝ → E) (r : ℝ) (hc1 : c 1 = c 0)
    (hcv : ∀ᵐ σ : ℝ, c σ = (v : TimeCircle → E) (σ : TimeCircle))
    (hid : r * (‖c 1‖ ^ 2 - ‖c 0‖ ^ 2) =
      ∫ σ in (0 : ℝ)..1, (inner ℝ ((f : TimeCircle → E) (σ : TimeCircle))
          ((k : TimeCircle → E) (σ : TimeCircle))
        - ‖(k : TimeCircle → E) (σ : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2)) :
    inner ℝ f k = ‖k‖ ^ 2 + (1 / 4 : ℝ) * ‖v‖ ^ 2 := by
  have h0 : ∫ σ in (0 : ℝ)..1, (inner ℝ ((f : TimeCircle → E) (σ : TimeCircle))
          ((k : TimeCircle → E) (σ : TimeCircle))
        - ‖(k : TimeCircle → E) (σ : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2) = 0 := by
    rw [← hid, hc1, sub_self, mul_zero]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at h0
  have hcongr : ∫ σ in Set.Icc (0 : ℝ) 1, (inner ℝ ((f : TimeCircle → E) (σ : TimeCircle))
          ((k : TimeCircle → E) (σ : TimeCircle))
        - ‖(k : TimeCircle → E) (σ : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2) =
      ∫ σ in Set.Icc (0 : ℝ) 1, (fun t : TimeCircle => inner ℝ ((f : TimeCircle → E) t)
          ((k : TimeCircle → E) t) - ‖(k : TimeCircle → E) t‖ ^ 2
          - (1 / 4 : ℝ) * ‖(v : TimeCircle → E) t‖ ^ 2) (σ : TimeCircle) := by
    refine integral_congr_ae (ae_restrict_of_ae (hcv.mono fun σ h => ?_))
    simp only
    rw [h]
  have hH : ∫ t : TimeCircle, (inner ℝ ((f : TimeCircle → E) t) ((k : TimeCircle → E) t)
      - ‖(k : TimeCircle → E) t‖ ^ 2 - (1 / 4 : ℝ) * ‖(v : TimeCircle → E) t‖ ^ 2) = 0 :=
    (integral_Icc_coe _).symm.trans (hcongr.symm.trans h0)
  have hi1 : Integrable (fun t => inner ℝ ((f : TimeCircle → E) t) ((k : TimeCircle → E) t))
      volume := L2.integrable_inner f k
  have hi2 : Integrable (fun t => ‖(k : TimeCircle → E) t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable k)).1 (Lp.memLp k)
  have hi3 : Integrable (fun t => ‖(v : TimeCircle → E) t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).1 (Lp.memLp v)
  have hi12 : Integrable (fun t => inner ℝ ((f : TimeCircle → E) t) ((k : TimeCircle → E) t)
      - ‖(k : TimeCircle → E) t‖ ^ 2) volume := hi1.sub hi2
  have hi3' : Integrable (fun t => (1 / 4 : ℝ) * ‖(v : TimeCircle → E) t‖ ^ 2) volume :=
    hi3.const_mul _
  rw [integral_sub hi12 hi3', integral_sub hi1 hi2, integral_const_mul] at hH
  rw [L2.inner_def, norm_sq_Lp_eq k, norm_sq_Lp_eq v]
  linarith

theorem exists_xx_of_halfSsp (v k : HH)
    (hvk : ∀ᵐ t ∂(volume : Measure TimeCircle),
      IsHalfSspOf ((v : TimeCircle → HBar) t) ((k : TimeCircle → HBar) t)) :
    ∃ u : XX, gradCLM u = v ∧ secondCLM u = k :=
  (exists_pair_lift halfOrderGraph (v : TimeCircle → HBar)
    (k : TimeCircle → HBar) (Lp.memLp v) (Lp.memLp k) (hvk.mono fun t ht =>
      Submodule.le_topologicalClosure _ (Submodule.subset_span ht))).elim fun w hw =>
  ⟨hw.1.toLp w, Lp.ext (by
    filter_upwards [gradCLM_ae (hw.1.toLp w), hw.1.coeFn_toLp, hw.2] with t h1 h2 h3
    exact h1.trans ((congrArg gradPart h2).trans (congrArg WithLp.fst h3))),
   Lp.ext (by
    filter_upwards [secondCLM_ae (hw.1.toLp w), hw.1.coeFn_toLp, hw.2] with t h1 h2 h3
    exact h1.trans ((congrArg secondPart h2).trans (congrArg WithLp.snd h3)))⟩

theorem le_inner_of_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f s g k v : V) (hs : s = k) (hg : g = v)
    (h : inner ℝ f k = ‖k‖ ^ 2 + (1 / 4 : ℝ) * ‖v‖ ^ 2) :
    ‖s‖ ^ 2 + (1 / 4 : ℝ) * ‖g‖ ^ 2 ≤ inner ℝ f s := by
  subst hs
  subst hg
  exact h.symm.le

theorem second_of_curve {P : ℝ} (f : HH)
    (hxx : ∀ k : HH, (∀ᵐ t ∂(volume : Measure TimeCircle),
      IsHalfSspOf ((gradInv P f : TimeCircle → HBar) t) ((k : TimeCircle → HBar) t)) →
      ∃ u : XX, gradCLM u = gradInv P f ∧ secondCLM u = k)
    (hc : ∃ (k : HH) (c : ℝ → Freq.X),
      Continuous c ∧ (∀ σ, c (σ + 1) = c σ) ∧
      (∀ᵐ σ : ℝ, c σ = (gradInv P f : TimeCircle → HBar) (σ : TimeCircle)) ∧
      (∀ᵐ t : TimeCircle, IsHalfSspOf ((gradInv P f : TimeCircle → HBar) t)
        ((k : TimeCircle → HBar) t)) ∧
      ∀ a b : ℝ, a ≤ b → (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
        ∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
            ((k : TimeCircle → HBar) (σ : TimeCircle))
          - ‖(k : TimeCircle → HBar) (σ : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2)) :
    ∃ u : XX, gradCLM u = gradInv P f ∧
      ‖secondCLM u‖ ^ 2 + (1 / 4 : ℝ) * ‖gradCLM u‖ ^ 2 ≤ inner ℝ f (secondCLM u) :=
  hc.elim fun k hk => hk.elim fun c hc' => (hxx k hc'.2.2.2.1).elim fun u hu =>
    ⟨u, hu.1, le_inner_of_eq f (secondCLM u) (gradCLM u) k (gradInv P f) hu.2 hu.1
      (period_identity f k (gradInv P f) c (1 / (2 * P))
        ((congrArg c (zero_add (1 : ℝ)).symm).trans (hc'.2.1 0)) hc'.2.2.1
        (hc'.2.2.2.2 0 1 zero_le_one))⟩

theorem exists_dense_second (h0 : PropagatorBoundHolds) (h1 : GradInvHolds)
    (h2 : GraphClosedHolds) {P : ℝ} (hP : 0 < P) :
    ∃ D : Submodule ℝ HH, Dense (D : Set HH) ∧ ∀ f ∈ D, ∃ u : XX, gradCLM u = gradInv P f ∧
      ‖secondCLM u‖ ^ 2 + (1 / 4 : ℝ) * ‖gradCLM u‖ ^ 2 ≤ inner ℝ f (secondCLM u) :=
  (exists_dense_energyCurve h0 h1 h2 hP).elim fun D hD =>
    ⟨D, hD.1, fun f hf => second_of_curve f (exists_xx_of_halfSsp (gradInv P f)) (hD.2 f hf)⟩

open scoped Classical in
theorem spec_of_dite {α : Type*} [Zero α] {p : α → Prop} (h : ∃ a, p a) :
    p (if h : ∃ a, p a then h.choose else 0) := by
  rw [dif_pos h]
  exact h.choose_spec

theorem bound_transfer {V W Y : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedSpace ℝ V]
    (g : W →L[ℝ] Y) (s : W →L[ℝ] V) (A : V →L[ℝ] Y) (hg : Function.Injective g)
    (S T : V →L[ℝ] W) (hS : ∀ f, g (S f) = A f) (hT : ∀ f, g (T f) = A f)
    (hb : ∀ f : V, ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2) (f : V) :
    ‖s (S f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (S f)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have e : S f = T f := hg ((hS f).trans (hT f).symm)
  rw [e]
  exact hb f

theorem exists_freeInv_bound (h0 : PropagatorBoundHolds) (h1 : GradInvHolds)
    (h2 : GraphClosedHolds) {P : ℝ} (hP : 0 < P) :
    ∃ T : HH →L[ℝ] XX, FreeInvSpec P T ∧ ∀ f : HH,
      ‖secondCLM (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖gradCLM (T f)‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  (exists_dense_second h0 h1 h2 hP).elim fun D hD => exists_freeInvSpec_bound h2 D hD.1 hD.2

theorem freeInv_of_bound (h2 : GraphClosedHolds) (P : ℝ)
    (hT : ∃ T : HH →L[ℝ] XX, FreeInvSpec P T ∧ ∀ f : HH,
      ‖secondCLM (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖gradCLM (T f)‖ ^ 2 ≤ ‖f‖ ^ 2) :
    (∃ T, FreeInvSpec P T) ∧ ∀ f : HH,
      ‖secondCLM (freeInv P f)‖ ^ 2 + (1 / 4 : ℝ) * ‖gradCLM (freeInv P f)‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  hT.elim fun T hT' => ⟨⟨T, hT'.1⟩, bound_transfer gradCLM secondCLM (gradInv P)
    (gradCLM_injective h2) (freeInv P) T (spec_of_dite ⟨T, hT'.1⟩) hT'.1 hT'.2⟩

end Internal.FreeInv

open Internal.FreeInv

theorem freeInvHolds_of (h0 : PropagatorBoundHolds) (h1 : GradInvHolds) (h2 : GraphClosedHolds) :
    FreeInvHolds := fun P hP => freeInv_of_bound h2 P (exists_freeInv_bound h0 h1 h2 hP)

end Breakdown.Cert
