import Breakdown.Cert.Nodes
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.SupBoundHalfSsp
import Breakdown.Cert.SliceFields
import Breakdown.Cert.HalfOrderGraphMem

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.LocalCompactness

theorem reading_spec (hr : ReadingExistsHolds) (u : XX) :
    IsReadingOf u (readingOf u).1 (readingOf u).2.1 (readingOf u).2.2 := by
  obtain ⟨v, G, H, h, -⟩ := hr u
  have hx : ∃ r : VelField × GradField × SecondField, IsReadingOf u r.1 r.2.1 r.2.2 :=
    ⟨(v, G, H), h⟩
  unfold readingOf
  rw [dif_pos hx]
  exact hx.choose_spec

theorem norm_sq_eq_integral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (W : Lp E 2 μ) :
    ‖W‖ ^ 2 = ∫ t, ‖(W : α → E) t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  ext t
  exact real_inner_self_eq_norm_sq _

theorem lintegral_norm_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (W : Lp E 2 μ) :
    ∫⁻ t, ENNReal.ofReal (‖(W : α → E) t‖ ^ 2) ∂μ = ENNReal.ofReal (‖W‖ ^ 2) := by
  rw [norm_sq_eq_integral W, ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp W).integrable_norm_pow two_ne_zero)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]

theorem gradCLM_ae (u : XX) : (gradCLM u : TimeCircle → HBar) =ᵐ[volume]
    fun t => gradPart ((u : TimeCircle → XBar) t) := by
  unfold gradCLM
  exact ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) gradPart u

theorem secondCLM_ae (u : XX) : (secondCLM u : TimeCircle → HBar) =ᵐ[volume]
    fun t => secondPart ((u : TimeCircle → XBar) t) := by
  unfold secondCLM
  exact ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) secondPart u

theorem norm_sq_xx (u : XX) : ‖u‖ ^ 2 = ‖gradCLM u‖ ^ 2 + ‖secondCLM u‖ ^ 2 := by
  have eg : (fun t => ‖(gradCLM u : TimeCircle → HBar) t‖ ^ 2) =ᵐ[volume]
      fun t => ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2 :=
    (gradCLM_ae u).mono fun t ht => congrArg (fun x : HBar => ‖x‖ ^ 2) ht
  have es : (fun t => ‖(secondCLM u : TimeCircle → HBar) t‖ ^ 2) =ᵐ[volume]
      fun t => ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2 :=
    (secondCLM_ae u).mono fun t ht => congrArg (fun x : HBar => ‖x‖ ^ 2) ht
  have ig : Integrable (fun t => ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2) volume :=
    ((Lp.memLp (gradCLM u)).integrable_norm_pow two_ne_zero).congr eg
  have is : Integrable (fun t => ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2) volume :=
    ((Lp.memLp (secondCLM u)).integrable_norm_pow two_ne_zero).congr es
  have e0 : ‖u‖ ^ 2 = ∫ t, ‖(u : TimeCircle → XBar) t‖ ^ 2 := norm_sq_eq_integral u
  have e1 : ‖gradCLM u‖ ^ 2 = ∫ t, ‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2 :=
    (norm_sq_eq_integral (gradCLM u)).trans (integral_congr_ae eg)
  have e2 : ‖secondCLM u‖ ^ 2 = ∫ t, ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2 :=
    (norm_sq_eq_integral (secondCLM u)).trans (integral_congr_ae es)
  have e3 : ∫ t, ‖(u : TimeCircle → XBar) t‖ ^ 2 = ∫ t, (‖gradPart ((u : TimeCircle → XBar) t)‖ ^ 2
      + ‖secondPart ((u : TimeCircle → XBar) t)‖ ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => norm_xbar_sq _)
  exact e0.trans (e3.trans ((integral_add ig is).trans (congrArg₂ (· + ·) e1.symm e2.symm)))

theorem real_bounds' {A B U F : ℝ} (hb : B ^ 2 + (1 / 4 : ℝ) * A ^ 2 ≤ F ^ 2)
    (e : U ^ 2 = A ^ 2 + B ^ 2) (h2 : 0 ≤ F) :
    A ≤ 2 * F ∧ B ≤ F ∧ U ^ 2 ≤ 5 * F ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (A - 2 * F)]
  · nlinarith [sq_nonneg (B - F)]
  · nlinarith

theorem real_le_of_sq {A B U : ℝ} (e : U ^ 2 = A ^ 2 + B ^ 2) (h2 : 0 ≤ U) :
    A ≤ U ∧ B ≤ U := by
  constructor
  · nlinarith [sq_nonneg (A - U)]
  · nlinarith [sq_nonneg (B - U)]

theorem norm_le_of_free (h4 : FreeInvHolds) {P : ℝ} (hP : 0 < P) (f : HH) :
    ‖gradCLM (freeInv P f)‖ ≤ 2 * ‖f‖ ∧ ‖secondCLM (freeInv P f)‖ ≤ ‖f‖ ∧
      ‖freeInv P f‖ ^ 2 ≤ 5 * ‖f‖ ^ 2 := by
  exact real_bounds' ((h4 P hP).2 f) (norm_sq_xx (freeInv P f))
    (norm_nonneg f)

theorem norm_le_of_xbar (q : XBar) : ‖gradPart q‖ ≤ ‖q‖ ∧ ‖secondPart q‖ ≤ ‖q‖ := by
  exact real_le_of_sq (norm_xbar_sq q) (norm_nonneg _)

theorem ball_velocity_le (r : ℝ) (w : Space → Space) (q : XBar)
    (hw : w =ᵐ[volume] (velocity (gradPart q) : Space → Space)) :
    ∫⁻ y in Metric.closedBall (0 : Space) r, ENNReal.ofReal (‖w y‖ ^ 2) ≤
      ENNReal.ofReal (‖q‖ ^ 2) * volume (Metric.closedBall (0 : Space) r) := by
  have hs := sq_le_of_halfSsp (gradPart q) (secondPart q) (halfSsp_of_xbar q)
  obtain ⟨h1, h2⟩ := norm_le_of_xbar q
  have hpi : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  calc ∫⁻ y in Metric.closedBall (0 : Space) r, ENNReal.ofReal (‖w y‖ ^ 2)
      ≤ ∫⁻ _ in Metric.closedBall (0 : Space) r, ENNReal.ofReal (‖q‖ ^ 2) := by
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hw, hs] with y hy hy'
        rw [hy]
        refine ENNReal.ofReal_le_ofReal (hy'.trans ?_)
        calc 1 / (2 * Real.pi) * ‖gradPart q‖ * ‖secondPart q‖ ≤ 1 * ‖q‖ * ‖q‖ := by
              gcongr
          _ = ‖q‖ ^ 2 := by ring
    _ = ENNReal.ofReal (‖q‖ ^ 2) * volume (Metric.closedBall (0 : Space) r) :=
        setLIntegral_const _ _

theorem column_ae (w : Space → Space) (G : Space → (Space →L[ℝ] Space)) (q : XBar)
    (hw : w =ᵐ[volume] (velocity (gradPart q) : Space → Space)) (hG : IsWeakGradient w G)
    (j : Fin 3) :
    (fun y => G y (unitVector j)) =ᵐ[volume] (partialX j (gradPart q) : Space → Space) := by
  obtain ⟨G₀, H₀, hG₀, -, -, -, hcol, -⟩ := slice_fields _ _ (halfSsp_of_xbar q)
  have loc : ∀ K : Space → (Space →L[ℝ] Space), LocallyIntegrable K volume →
      LocallyIntegrable (fun y => K y (unitVector j)) volume := fun K hK x =>
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).integrableAtFilter_comp (hK x)
  have h : (fun y => G y (unitVector j)) =ᵐ[volume] fun y => G₀ y (unitVector j) := by
    refine ae_eq_of_integral_contDiff_smul_eq (loc G hG.2.1) (loc G₀ hG₀.2.1) fun φ hφ hs => ?_
    show ∫ y, φ y • G y (unitVector j) = ∫ y, φ y • G₀ y (unitVector j)
    rw [hG.2.2 φ ⟨hφ, hs⟩ j, hG₀.2.2 φ ⟨hφ, hs⟩ j]
    congr 1
    exact integral_congr_ae (hw.mono fun y hy => by simp only [hy])
  exact h.trans (hcol j)

theorem ball_l2_le (r : ℝ) (w : Space → Space) (F : L2R) (hw : w =ᵐ[volume] (F : Space → Space)) :
    ∫⁻ y in Metric.closedBall (0 : Space) r, ENNReal.ofReal (‖w y‖ ^ 2) ≤ ENNReal.ofReal (‖F‖ ^ 2) := by
  calc ∫⁻ y in Metric.closedBall (0 : Space) r, ENNReal.ofReal (‖w y‖ ^ 2)
      ≤ ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 2) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, ENNReal.ofReal (‖(F : Space → Space) y‖ ^ 2) :=
        lintegral_congr_ae (hw.mono fun y hy => by simp only [hy])
    _ = ENNReal.ofReal (‖F‖ ^ 2) := lintegral_norm_sq F

theorem norm_partialX_le (j : Fin 3) (q : XBar) : ‖partialX j (gradPart q)‖ ^ 2 ≤ ‖q‖ ^ 2 := by
  have e := Internal.SliceFields.sum_norm_partialX_sq (gradPart q)
  have h1 : ‖partialX j (gradPart q)‖ ^ 2 ≤ ∑ i : Fin 3, ‖partialX i (gradPart q)‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖partialX i (gradPart q)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  obtain ⟨h2, -⟩ := norm_le_of_xbar q
  have h3 : ‖gradPart q‖ ^ 2 ≤ ‖q‖ ^ 2 := by gcongr
  linarith


theorem ofReal_toReal_ball (r : ℝ) (hB : volume (Metric.closedBall (0 : Space) r) ≠ ⊤) :
    ENNReal.ofReal (volume (Metric.closedBall (0 : Space) r)).toReal =
      volume (Metric.closedBall (0 : Space) r) :=
  ENNReal.ofReal_toReal hB

theorem ofReal_mul_volume (a : ℝ) (ha : 0 ≤ a) (r : ℝ)
    (hB : volume (Metric.closedBall (0 : Space) r) ≠ ⊤) :
    ENNReal.ofReal a * volume (Metric.closedBall (0 : Space) r) =
      ENNReal.ofReal (a * (volume (Metric.closedBall (0 : Space) r)).toReal) := by
  rw [ENNReal.ofReal_mul ha, ofReal_toReal_ball r hB]

theorem period_velocity_le (r : ℝ) (w : ℝ → Space → Space) (W : XX)
    (hw : ∀ᵐ σ : ℝ, w σ =ᵐ[volume]
      (velocity (gradPart ((W : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space)) :
    periodBallLIntegral r (fun σ y => ‖w σ y‖ ^ 2) ≤
      ENNReal.ofReal (‖W‖ ^ 2 * (volume (Metric.closedBall (0 : Space) r)).toReal) := by
  have hm : AEMeasurable (fun t : TimeCircle => ENNReal.ofReal (‖(W : TimeCircle → XBar) t‖ ^ 2)) volume :=
    ((Lp.aestronglyMeasurable W).norm.pow 2).aemeasurable.ennreal_ofReal
  have hB : volume (Metric.closedBall (0 : Space) r) ≠ ⊤ := measure_closedBall_lt_top.ne
  refine le_trans ?_ (ofReal_mul_volume _ (sq_nonneg _) r hB).le
  unfold periodBallLIntegral
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) r, ENNReal.ofReal (‖w σ y‖ ^ 2)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (‖(W : TimeCircle → XBar) (σ : TimeCircle)‖ ^ 2) *
          volume (Metric.closedBall (0 : Space) r) :=
        lintegral_mono_ae (ae_restrict_of_ae (hw.mono fun σ hσ => ball_velocity_le r (w σ) _ hσ))
    _ = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (‖(W : TimeCircle → XBar) (σ : TimeCircle)‖ ^ 2)) *
          volume (Metric.closedBall (0 : Space) r) := lintegral_mul_const' _ _ hB
    _ = ENNReal.ofReal (‖W‖ ^ 2) * volume (Metric.closedBall (0 : Space) r) :=
        congrArg (· * volume (Metric.closedBall (0 : Space) r))
          ((lintegral_Icc_coe (fun t => ENNReal.ofReal (‖(W : TimeCircle → XBar) t‖ ^ 2)) hm).trans
            (lintegral_norm_sq W))

theorem period_column_le (r : ℝ) (j : Fin 3) (w : ℝ → Space → Space) (W : XX)
    (hw : ∀ᵐ σ : ℝ, w σ =ᵐ[volume]
      (partialX j (gradPart ((W : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space)) :
    periodBallLIntegral r (fun σ y => ‖w σ y‖ ^ 2) ≤ ENNReal.ofReal (‖W‖ ^ 2) := by
  have hm : AEMeasurable (fun t : TimeCircle => ENNReal.ofReal (‖(W : TimeCircle → XBar) t‖ ^ 2)) volume :=
    ((Lp.aestronglyMeasurable W).norm.pow 2).aemeasurable.ennreal_ofReal
  unfold periodBallLIntegral
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) r, ENNReal.ofReal (‖w σ y‖ ^ 2)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (‖(W : TimeCircle → XBar) (σ : TimeCircle)‖ ^ 2) :=
        lintegral_mono_ae (ae_restrict_of_ae (hw.mono fun σ hσ =>
          (ball_l2_le r (w σ) _ hσ).trans (ENNReal.ofReal_le_ofReal (norm_partialX_le j _))))
    _ = ENNReal.ofReal (‖W‖ ^ 2) :=
        (lintegral_Icc_coe (fun t => ENNReal.ofReal (‖(W : TimeCircle → XBar) t‖ ^ 2)) hm).trans
          (lintegral_norm_sq W)

theorem sub_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] (L : Freq.X →L[ℝ] Lp (α := Space) Space p) (w w' : ℝ → Space → Space)
    (u u' : XX)
    (h : ∀ᵐ σ : ℝ, w σ =ᵐ[volume]
      (L (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space))
    (h' : ∀ᵐ σ : ℝ, w' σ =ᵐ[volume]
      (L (gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space)) :
    ∀ᵐ σ : ℝ, (fun y => w σ y - w' σ y) =ᵐ[volume]
      (L (gradPart (((u - u' : XX) : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) := by
  have hs : ∀ᵐ σ : ℝ, ((u - u' : XX) : TimeCircle → XBar) (σ : TimeCircle) =
      (u : TimeCircle → XBar) σ - (u' : TimeCircle → XBar) σ :=
    (ae_coe_iff (fun t => ((u - u' : XX) : TimeCircle → XBar) t =
      (u : TimeCircle → XBar) t - (u' : TimeCircle → XBar) t)).1 (Lp.coeFn_sub u u')
  filter_upwards [h, h', hs] with σ a b c
  rw [c, map_sub, map_sub]
  exact (a.sub b).trans (Lp.coeFn_sub _ _).symm

theorem reading_column_ae {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hR : IsReadingOf u v G H) (j : Fin 3) :
    ∀ᵐ σ : ℝ, gradColumn G j σ =ᵐ[volume]
      (partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) := by
  filter_upwards [hR.velocity_eq, hR.weak_gradient] with σ h1 h2
  exact column_ae (v σ) (G σ) _ h1 h2 j

theorem fin_velocity (h5 : ReadingExistsHolds) (u u' : XX) (r : ℝ) :
    periodBallLIntegral r (fun σ y => ‖(readingOf u).1 σ y - (readingOf u').1 σ y‖ ^ 2) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (period_velocity_le r (fun σ y => (readingOf u).1 σ y - (readingOf u').1 σ y) (u - u')
      (sub_ae velocity _ _ u u' (reading_spec h5 u).velocity_eq (reading_spec h5 u').velocity_eq))

theorem fin_column (h5 : ReadingExistsHolds) (u u' : XX) (r : ℝ) (j : Fin 3) :
    periodBallLIntegral r (fun σ y => ‖gradColumn (readingOf u).2.1 j σ y
      - gradColumn (readingOf u').2.1 j σ y‖ ^ 2) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (period_column_le r j (fun σ y => gradColumn (readingOf u).2.1 j σ y
      - gradColumn (readingOf u').2.1 j σ y) (u - u')
      (sub_ae (partialX j) _ _ u u' (reading_column_ae (reading_spec h5 u) j)
        (reading_column_ae (reading_spec h5 u') j)))

theorem periodBallNorm_mono {r s : ℝ} (hrs : r ≤ s) (F : ℝ → Space → Space)
    (hF : periodBallLIntegral s (fun σ y => ‖F σ y‖ ^ 2) ≠ ⊤) :
    periodBallNorm r F ≤ periodBallNorm s F := by
  unfold periodBallNorm
  refine Real.sqrt_le_sqrt (ENNReal.toReal_mono hF ?_)
  unfold periodBallLIntegral
  exact lintegral_mono fun σ => lintegral_mono_set (Metric.closedBall_subset_closedBall hrs)

theorem real_mul_bound {U F C V : ℝ} (hu : U ^ 2 ≤ 5 * F ^ 2) (hf : F ^ 2 ≤ C ^ 2) (hV : 0 ≤ V) :
    U ^ 2 * V ≤ 5 * C ^ 2 * (V + 1) := by
  have h0 : 0 ≤ U ^ 2 := sq_nonneg U
  nlinarith [sq_nonneg C]

theorem real_bound {U F C V : ℝ} (hu : U ^ 2 ≤ 5 * F ^ 2) (hf : F ^ 2 ≤ C ^ 2) (hV : 0 ≤ V) :
    U ^ 2 ≤ 5 * C ^ 2 * (V + 1) := by
  nlinarith [sq_nonneg C]

def FundamentalAt (F : ℕ → ℝ → Space → Space) (R : ℝ) (ψ : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, periodBallNorm R (fun σ y => F (ψ m) σ y - F (ψ n) σ y) < ε

theorem fundamentalAt_sub {F : ℕ → ℝ → Space → Space} {R : ℝ} {ψ ψ' : ℕ → ℕ} (θ : ℕ → ℕ) (k : ℕ)
    (hθ : ∀ n, n ≤ θ n) (he : ∀ n ≥ k, ψ' n = ψ (θ n)) (h : FundamentalAt F R ψ) : FundamentalAt F R ψ' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨max N k, fun m hm n hn => ?_⟩
  rw [he m (le_of_max_le_right hm), he n (le_of_max_le_right hn)]
  exact hN _ ((le_of_max_le_left hm).trans (hθ m)) _ ((le_of_max_le_left hn).trans (hθ n))

theorem fundamentalAt_comp {F : ℕ → ℝ → Space → Space} {R : ℝ} {ψ θ : ℕ → ℕ} (hθ : StrictMono θ)
    (h : FundamentalAt F R ψ) : FundamentalAt F R (ψ ∘ θ) :=
  fundamentalAt_sub θ 0 hθ.id_le (fun _ _ => rfl) h

def diagSeq (φ : ℕ → (ℕ → ℕ) → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | k + 1 => diagSeq φ k ∘ φ k (diagSeq φ k)

theorem exists_diagonal (Q : ℕ → (ℕ → ℕ) → Prop)
    (hstep : ∀ k (ψ : ℕ → ℕ), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Q k (ψ ∘ φ))
    (hsub : ∀ k (ψ ψ' θ : ℕ → ℕ) (j : ℕ), (∀ n, n ≤ θ n) → (∀ n ≥ j, ψ' n = ψ (θ n)) →
      Q k ψ → Q k ψ') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, Q k φ := by
  choose φ hφm hφQ using hstep
  have hsucc : ∀ k, diagSeq φ (k + 1) = diagSeq φ k ∘ φ k (diagSeq φ k) := fun k => rfl
  have hmono : ∀ k, StrictMono (diagSeq φ k) := by
    intro k
    induction k with
    | zero => exact strictMono_id
    | succ k ih => rw [hsucc]; exact ih.comp (hφm _ _)
  have hext : ∀ k m, ∃ θ : ℕ → ℕ, StrictMono θ ∧ diagSeq φ (k + m) = diagSeq φ k ∘ θ := by
    intro k m
    induction m with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ m ih =>
      obtain ⟨θ, hθ, he⟩ := ih
      refine ⟨θ ∘ φ (k + m) (diagSeq φ (k + m)), hθ.comp (hφm _ _), ?_⟩
      show diagSeq φ (k + m + 1) = _
      rw [hsucc]
      funext n
      exact congrFun he (φ (k + m) (diagSeq φ (k + m)) n)
  refine ⟨fun n => diagSeq φ n n, strictMono_nat_of_lt_succ fun n => ?_, fun k => ?_⟩
  · show diagSeq φ n n < diagSeq φ (n + 1) (n + 1)
    rw [hsucc]
    exact hmono n (lt_of_lt_of_le (Nat.lt_succ_self n) ((hφm n _).id_le _))
  · choose θ hθ he using hext (k + 1)
    refine hsub k (diagSeq φ (k + 1)) _ (fun n => θ (n - (k + 1)) n) (k + 1)
      (fun n => (hθ _).id_le n) (fun n hn => ?_) (hφQ k (diagSeq φ k))
    have e := congrFun (he (n - (k + 1))) n
    rw [Nat.add_sub_cancel' hn] at e
    exact e

theorem criterion_apply (h3 : TranslationCriterionHolds) (F : ℕ → ℝ → Space → Space)
    {R K A B : ℝ} (rt : ℝ → ℝ) (hR : 0 < R) (hrt : Tendsto rt (𝓝[>] 0) (𝓝 0)) (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hm : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => F n z.1 z.2) volume)
    (hp : ∀ n, IsTimePeriodic (F n))
    (hb : ∀ n, periodBallLIntegral (R + 1) (fun σ y => ‖F n σ y‖ ^ 2) ≤ ENNReal.ofReal K)
    (ht : ∀ n, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      periodBallNorm R (fun σ y => F n (σ + δ) y - F n σ y) ≤ |rt δ| * A)
    (hs : ∀ n (h : Space), periodBallNorm R (fun σ y => F n σ (y + h) - F n σ y) ≤ ‖h‖ * B)
    (ψ : ℕ → ℕ) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ FundamentalAt F R (ψ ∘ φ) := by
  have e1 : Tendsto (fun δ => |rt δ|) (𝓝[>] 0) (𝓝 0) := by
    have e := (continuous_abs.tendsto (0 : ℝ)).comp hrt
    rw [abs_zero] at e
    exact e
  have e2 : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hρ : Tendsto (fun δ => |rt δ| * A + δ * B) (𝓝[>] 0) (𝓝 0) := by
    simpa using (e1.mul_const A).add (e2.mul_const B)
  obtain ⟨φ, hφ, hc⟩ := h3 (fun n => F (ψ n)) R K (fun δ => |rt δ| * A + δ * B) hR hρ
    (fun n => hm _) (fun n => hp _) (fun n => hb _)
    (fun n δ hδ => (ht _ δ hδ).trans (le_add_of_nonneg_right (mul_nonneg hδ.1.le hB)))
    (fun n h _ _ => (hs _ h).trans (le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) hA)))
  exact ⟨φ, hφ, hc⟩

theorem step_velocity (h1 : TimeModulusHolds) (h2 : SpaceModulusHolds)
    (h3 : TranslationCriterionHolds) (h4 : FreeInvHolds) (h5 : ReadingExistsHolds) {a b : ℝ}
    (ha : 0 < a) {P : ℕ → ℝ} {f : ℕ → HH} (hP : ∀ n, P n ∈ Set.Icc a b) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) {R : ℝ} (hR : 0 < R) (ψ : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      FundamentalAt (fun n => (readingOf (freeInv (P n) (f n))).1) R (ψ ∘ φ) := by
  refine (h1 a b R ha hR).elim fun rt hr => ?_
  have hrt := hr.1
  have hmod := hr.2
  have hPpos : ∀ n, 0 < P n := fun n => ha.trans_le (hP n).1
  have hV : 0 ≤ (volume (Metric.closedBall (0 : Space) (R + 1))).toReal := ENNReal.toReal_nonneg
  have hm : ∀ n, AEStronglyMeasurable
      (fun z : ℝ × Space => (readingOf (freeInv (P n) (f n))).1 z.1 z.2) volume :=
    fun n => (reading_spec h5 (freeInv (P n) (f n))).measurable_velocity
  have hp : ∀ n, IsTimePeriodic (readingOf (freeInv (P n) (f n))).1 :=
    fun n => (reading_spec h5 (freeInv (P n) (f n))).periodic_velocity
  have hb : ∀ n, periodBallLIntegral (R + 1)
      (fun σ y => ‖(readingOf (freeInv (P n) (f n))).1 σ y‖ ^ 2) ≤
      ENNReal.ofReal (5 * C ^ 2 * ((volume (Metric.closedBall (0 : Space) (R + 1))).toReal + 1)) := by
    intro n
    refine (period_velocity_le (R + 1) _ _
      (reading_spec h5 (freeInv (P n) (f n))).velocity_eq).trans (ENNReal.ofReal_le_ofReal ?_)
    have hu := (norm_le_of_free h4 (hPpos n) (f n)).2.2
    have hfc : ‖f n‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hf n) 2
    exact real_mul_bound hu hfc hV
  have ht : ∀ n, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, periodBallNorm R
      (fun σ y => (readingOf (freeInv (P n) (f n))).1 (σ + δ) y
        - (readingOf (freeInv (P n) (f n))).1 σ y) ≤ |rt δ| * C := fun n δ hδ =>
    (hmod (P n) (hP n) (f n) δ hδ).1.trans
      ((mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hf n) (abs_nonneg _)))
  have hs : ∀ n (h : Space), periodBallNorm R
      (fun σ y => (readingOf (freeInv (P n) (f n))).1 σ (y + h)
        - (readingOf (freeInv (P n) (f n))).1 σ y) ≤ ‖h‖ * (2 * C) := fun n h =>
    (h2 R hR (freeInv (P n) (f n)) h).1.trans (mul_le_mul_of_nonneg_left
      ((norm_le_of_free h4 (hPpos n) (f n)).1.trans (by linarith [hf n])) (norm_nonneg h))
  exact criterion_apply h3 _ rt hR hrt hC (by positivity) hm hp hb ht hs ψ

theorem step_column (h1 : TimeModulusHolds) (h2 : SpaceModulusHolds)
    (h3 : TranslationCriterionHolds) (h4 : FreeInvHolds) (h5 : ReadingExistsHolds) {a b : ℝ}
    (ha : 0 < a) {P : ℕ → ℝ} {f : ℕ → HH} (hP : ∀ n, P n ∈ Set.Icc a b) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) {R : ℝ} (hR : 0 < R) (j : Fin 3) (ψ : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      FundamentalAt (fun n => gradColumn (readingOf (freeInv (P n) (f n))).2.1 j) R (ψ ∘ φ) := by
  refine (h1 a b R ha hR).elim fun rt hr => ?_
  have hrt := hr.1
  have hmod := hr.2
  have hPpos : ∀ n, 0 < P n := fun n => ha.trans_le (hP n).1
  have hV : 0 ≤ (volume (Metric.closedBall (0 : Space) (R + 1))).toReal := ENNReal.toReal_nonneg
  have hm : ∀ n, AEStronglyMeasurable
      (fun z : ℝ × Space => gradColumn (readingOf (freeInv (P n) (f n))).2.1 j z.1 z.2) volume :=
    fun n => (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable
      (reading_spec h5 (freeInv (P n) (f n))).measurable_gradient
  have hp : ∀ n, IsTimePeriodic (gradColumn (readingOf (freeInv (P n) (f n))).2.1 j) :=
    fun n σ y => congrArg (fun L : Space →L[ℝ] Space => L (unitVector j))
      ((reading_spec h5 (freeInv (P n) (f n))).periodic_gradient σ y)
  have hb : ∀ n, periodBallLIntegral (R + 1)
      (fun σ y => ‖gradColumn (readingOf (freeInv (P n) (f n))).2.1 j σ y‖ ^ 2) ≤
      ENNReal.ofReal (5 * C ^ 2 * ((volume (Metric.closedBall (0 : Space) (R + 1))).toReal + 1)) := by
    intro n
    refine (period_column_le (R + 1) j _ _
      (reading_column_ae (reading_spec h5 (freeInv (P n) (f n))) j)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hu := (norm_le_of_free h4 (hPpos n) (f n)).2.2
    have hfc : ‖f n‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hf n) 2
    exact real_bound hu hfc hV
  have ht : ∀ n, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, periodBallNorm R
      (fun σ y => gradColumn (readingOf (freeInv (P n) (f n))).2.1 j (σ + δ) y
        - gradColumn (readingOf (freeInv (P n) (f n))).2.1 j σ y) ≤ |rt δ| * C := fun n δ hδ =>
    ((hmod (P n) (hP n) (f n) δ hδ).2 j).trans
      ((mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hf n) (abs_nonneg _)))
  have hs : ∀ n (h : Space), periodBallNorm R
      (fun σ y => gradColumn (readingOf (freeInv (P n) (f n))).2.1 j σ (y + h)
        - gradColumn (readingOf (freeInv (P n) (f n))).2.1 j σ y) ≤ ‖h‖ * (2 * C) := fun n h =>
    ((h2 R hR (freeInv (P n) (f n)) h).2 j).trans (mul_le_mul_of_nonneg_left
      ((norm_le_of_free h4 (hPpos n) (f n)).2.1.trans (by linarith [hf n])) (norm_nonneg h))
  exact criterion_apply h3 _ rt hR hrt hC (by positivity) hm hp hb ht hs ψ

end Internal.LocalCompactness

open Internal.LocalCompactness in
theorem localCompactnessHolds_of (h1 : TimeModulusHolds) (h2 : SpaceModulusHolds)
    (h3 : TranslationCriterionHolds) (h4 : FreeInvHolds) (h5 : ReadingExistsHolds) :
    LocalCompactnessHolds := by
  intro a b ha P f hP hCex
  refine hCex.elim fun C hC => ?_
  have hC₀ : 0 ≤ max C 0 := le_max_right _ _
  have hf : ∀ n, ‖f n‖ ≤ max C 0 := fun n => (hC n).trans (le_max_left _ _)
  have hstep : ∀ (k : ℕ) (ψ : ℕ → ℕ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (FundamentalAt (fun n => (readingOf (freeInv (P n) (f n))).1) ((k : ℝ) + 1) (ψ ∘ φ) ∧
        ∀ j, FundamentalAt (fun n => gradColumn (readingOf (freeInv (P n) (f n))).2.1 j)
          ((k : ℝ) + 1) (ψ ∘ φ)) := by
    intro k ψ
    have hR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    refine (step_velocity h1 h2 h3 h4 h5 ha hP hC₀ hf hR ψ).elim fun φ₁ hφ₁ => ?_
    refine (step_column h1 h2 h3 h4 h5 ha hP hC₀ hf hR 0 (ψ ∘ φ₁)).elim fun φ₂ hφ₂ => ?_
    refine (step_column h1 h2 h3 h4 h5 ha hP hC₀ hf hR 1 (ψ ∘ φ₁ ∘ φ₂)).elim fun φ₃ hφ₃ => ?_
    refine (step_column h1 h2 h3 h4 h5 ha hP hC₀ hf hR 2 (ψ ∘ φ₁ ∘ φ₂ ∘ φ₃)).elim
      fun φ₄ hφ₄ => ?_
    refine ⟨φ₁ ∘ φ₂ ∘ φ₃ ∘ φ₄, hφ₁.1.comp (hφ₂.1.comp (hφ₃.1.comp hφ₄.1)),
      fundamentalAt_comp (ψ := ψ ∘ φ₁) (hφ₂.1.comp (hφ₃.1.comp hφ₄.1)) hφ₁.2, fun j => ?_⟩
    fin_cases j
    · exact fundamentalAt_comp (ψ := ψ ∘ φ₁ ∘ φ₂) (hφ₃.1.comp hφ₄.1) hφ₂.2
    · exact fundamentalAt_comp (ψ := ψ ∘ φ₁ ∘ φ₂ ∘ φ₃) hφ₄.1 hφ₃.2
    · exact hφ₄.2
  have hdiag : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ,
      (FundamentalAt (fun n => (readingOf (freeInv (P n) (f n))).1) ((k : ℝ) + 1) φ ∧
        ∀ j, FundamentalAt (fun n => gradColumn (readingOf (freeInv (P n) (f n))).2.1 j)
          ((k : ℝ) + 1) φ) :=
    exists_diagonal (fun k ψ =>
      FundamentalAt (fun n => (readingOf (freeInv (P n) (f n))).1) ((k : ℝ) + 1) ψ ∧
        ∀ j, FundamentalAt (fun n => gradColumn (readingOf (freeInv (P n) (f n))).2.1 j)
          ((k : ℝ) + 1) ψ) hstep
      fun k ψ ψ' θ j hθ he h =>
        ⟨fundamentalAt_sub θ j hθ he h.1, fun i => fundamentalAt_sub θ j hθ he (h.2 i)⟩
  refine hdiag.elim fun φ hφ => ?_
  refine ⟨φ, hφ.1, fun R _ ε hε => ?_⟩
  refine (exists_nat_ge R).elim fun k hk => ?_
  have hRk : R ≤ (k : ℝ) + 1 := by linarith
  have hQ := hφ.2 k
  refine (hQ.1 ε hε).elim fun N₀ hN₀ => ?_
  refine (hQ.2 0 ε hε).elim fun N₁ hN₁ => ?_
  refine (hQ.2 1 ε hε).elim fun N₂ hN₂ => ?_
  refine (hQ.2 2 ε hε).elim fun N₃ hN₃ => ?_
  refine ⟨max (max N₀ N₁) (max N₂ N₃), fun m hm n hn => ?_⟩
  have hm0 : N₀ ≤ m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hm1 : N₁ ≤ m := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hm2 : N₂ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm3 : N₃ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hn0 : N₀ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : N₁ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn3 : N₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  refine ⟨(periodBallNorm_mono hRk _ (fin_velocity h5 (freeInv (P (φ m)) (f (φ m)))
    (freeInv (P (φ n)) (f (φ n))) ((k : ℝ) + 1))).trans_lt (hN₀ m hm0 n hn0), fun j => ?_⟩
  have hcol : ∀ i : Fin 3, periodBallNorm ((k : ℝ) + 1) (fun σ y =>
      gradColumn (readingOf (freeInv (P (φ m)) (f (φ m)))).2.1 i σ y
        - gradColumn (readingOf (freeInv (P (φ n)) (f (φ n)))).2.1 i σ y) < ε →
      periodBallNorm R (fun σ y =>
      gradColumn (readingOf (freeInv (P (φ m)) (f (φ m)))).2.1 i σ y
        - gradColumn (readingOf (freeInv (P (φ n)) (f (φ n)))).2.1 i σ y) < ε := fun i hi =>
    (periodBallNorm_mono hRk _ (fin_column h5 (freeInv (P (φ m)) (f (φ m)))
      (freeInv (P (φ n)) (f (φ n))) ((k : ℝ) + 1) i)).trans_lt hi
  fin_cases j
  · exact hcol 0 (hN₁ m hm1 n hn1)
  · exact hcol 1 (hN₂ m hm2 n hn2)
  · exact hcol 2 (hN₃ m hm3 n hn3)

end Breakdown.Cert
