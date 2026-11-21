import Breakdown.Torus.SeqDefs

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace SeqOps.Internal

section Seq

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem norm_apply_le {Y W : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (A : ℕ → Y →L[ℝ] W) {C : ℝ}
    (hA : ∀ n, ‖A n‖ ≤ C) (g : lp (fun _ : ℕ => Y) ∞) (n : ℕ) : ‖A n (g n)‖ ≤ C * ‖g‖ :=
  ((A n).le_opNorm _).trans (mul_le_mul (hA n) (lp.norm_apply_le_norm ENNReal.top_ne_zero g n)
    (norm_nonneg _) ((norm_nonneg _).trans (hA n)))

def opFun (A : ℕ → E →L[ℝ] X) {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C) (g : lp (fun _ : ℕ => E) ∞) :
    lp (fun _ : ℕ => X) ∞ :=
  ⟨fun n => A n (g n), memℓp_infty ⟨C * ‖g‖, by
    rintro _ ⟨n, rfl⟩
    exact norm_apply_le A hA g n⟩⟩

theorem opFun_apply (A : ℕ → E →L[ℝ] X) {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C)
    (g : lp (fun _ : ℕ => E) ∞) (n : ℕ) : opFun A hA g n = A n (g n) := rfl

def opCLM (A : ℕ → E →L[ℝ] X) {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C) (hC : 0 ≤ C) :
    lp (fun _ : ℕ => E) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞ :=
  LinearMap.mkContinuous
    { toFun := opFun A hA
      map_add' := fun g h => lp.ext <| funext fun n => by
        simp only [lp.coeFn_add, Pi.add_apply, opFun_apply, map_add]
      map_smul' := fun c g => lp.ext <| funext fun n => by
        simp only [lp.coeFn_smul, Pi.smul_apply, opFun_apply, map_smul, RingHom.id_apply] }
    C (fun g => lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg _))
      (fun n => norm_apply_le A hA g n))

theorem shift_le (B : ℕ → X →L[ℝ] X) {C : ℝ} (hB : ∀ n, ‖B n‖ ≤ C) (hC : 0 ≤ C)
    (g : lp (fun _ : ℕ => X) ∞) (n : ℕ) :
    ‖(if n = 0 then 0 else B (n - 1) (g (n - 1)))‖ ≤ C * ‖g‖ := by
  split_ifs
  · rw [norm_zero]
    exact mul_nonneg hC (norm_nonneg _)
  · exact norm_apply_le B hB g (n - 1)

def shiftFun (B : ℕ → X →L[ℝ] X) {C : ℝ} (hB : ∀ n, ‖B n‖ ≤ C) (hC : 0 ≤ C)
    (g : lp (fun _ : ℕ => X) ∞) : lp (fun _ : ℕ => X) ∞ :=
  ⟨fun n => if n = 0 then 0 else B (n - 1) (g (n - 1)), memℓp_infty ⟨C * ‖g‖, by
    rintro _ ⟨n, rfl⟩
    exact shift_le B hB hC g n⟩⟩

theorem shiftFun_apply (B : ℕ → X →L[ℝ] X) {C : ℝ} (hB : ∀ n, ‖B n‖ ≤ C) (hC : 0 ≤ C)
    (g : lp (fun _ : ℕ => X) ∞) (n : ℕ) :
    shiftFun B hB hC g n = if n = 0 then 0 else B (n - 1) (g (n - 1)) := rfl

def shiftCLM (B : ℕ → X →L[ℝ] X) {C : ℝ} (hB : ∀ n, ‖B n‖ ≤ C) (hC : 0 ≤ C) :
    lp (fun _ : ℕ => X) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞ :=
  LinearMap.mkContinuous
    { toFun := shiftFun B hB hC
      map_add' := fun g h => lp.ext <| funext fun n => by
        simp only [lp.coeFn_add, Pi.add_apply, shiftFun_apply, map_add]
        split_ifs <;> simp
      map_smul' := fun c g => lp.ext <| funext fun n => by
        simp only [lp.coeFn_smul, Pi.smul_apply, shiftFun_apply, map_smul, RingHom.id_apply]
        split_ifs <;> simp }
    C (fun g => lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg _))
      (fun n => shift_le B hB hC g n))

theorem seed_le (A₀ : E →L[ℝ] X) (e : E) (n : ℕ) :
    ‖(if n = 0 then A₀ e else 0)‖ ≤ ‖A₀ e‖ := by
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

def seedFun (A₀ : E →L[ℝ] X) (e : E) : lp (fun _ : ℕ => X) ∞ :=
  ⟨fun n => if n = 0 then A₀ e else 0, memℓp_infty ⟨‖A₀ e‖, by
    rintro _ ⟨n, rfl⟩
    exact seed_le A₀ e n⟩⟩

theorem seedFun_apply (A₀ : E →L[ℝ] X) (e : E) (n : ℕ) :
    seedFun A₀ e n = if n = 0 then A₀ e else 0 := rfl

def seedCLM (A₀ : E →L[ℝ] X) : E →L[ℝ] lp (fun _ : ℕ => X) ∞ :=
  LinearMap.mkContinuous
    { toFun := seedFun A₀
      map_add' := fun e f => lp.ext <| funext fun n => by
        simp only [lp.coeFn_add, Pi.add_apply, seedFun_apply, map_add]
        split_ifs <;> simp
      map_smul' := fun c e => lp.ext <| funext fun n => by
        simp only [lp.coeFn_smul, Pi.smul_apply, seedFun_apply, map_smul, RingHom.id_apply]
        split_ifs <;> simp }
    ‖A₀‖ (fun e => lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => (seed_le A₀ e n).trans (A₀.le_opNorm e)))

end Seq

section Conv

variable {Y Z X : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem extend_add {T : ℝ} (f g : Piece Y T) (s : ℝ) :
    extendPiece (f + g) s = extendPiece f s + extendPiece g s := by
  unfold extendPiece
  split_ifs with h
  · rfl
  · simp

theorem extend_smul {T : ℝ} (c : ℝ) (f : Piece Y T) (s : ℝ) :
    extendPiece (c • f) s = c • extendPiece f s := by
  unfold extendPiece
  split_ifs with h
  · rfl
  · simp

theorem extend_continuous {T : ℝ} (f : Piece Y T) : Continuous (extendPiece f) := by
  unfold extendPiece
  split_ifs with h
  · exact f.continuous.comp continuous_projIcc
  · exact continuous_const

theorem norm_extend_le {T : ℝ} (f : Piece Y T) (s : ℝ) : ‖extendPiece f s‖ ≤ ‖f‖ := by
  unfold extendPiece
  split_ifs with h
  · exact ContinuousMap.norm_coe_le_norm f _
  · simp

theorem tendsto_apply (Λ : ℝ → Z →L[ℝ] X) (hΛc : ∀ ζ, ContinuousOn (fun τ => Λ τ ζ) (Ioi 0))
    {α : Type} {l : Filter α} {τ : α → ℝ} {z : α → Z} {τ₀ : ℝ} {z₀ : Z} {B : ℝ}
    (h₀ : 0 < τ₀) (hτ : Tendsto τ l (𝓝 τ₀)) (hz : Tendsto z l (𝓝 z₀))
    (hB : ∀ᶠ x in l, ‖Λ (τ x)‖ ≤ B) :
    Tendsto (fun x => Λ (τ x) (z x)) l (𝓝 (Λ τ₀ z₀)) := by
  have h1 : Tendsto (fun x => Λ (τ x) z₀) l (𝓝 (Λ τ₀ z₀)) :=
    ((hΛc z₀).continuousAt (Ioi_mem_nhds h₀)).tendsto.comp hτ
  have hbd : ∀ᶠ x in l, ‖Λ (τ x) (z x) - Λ (τ x) z₀‖ ≤ B * ‖z x - z₀‖ := by
    filter_upwards [hB] with x hx
    rw [← map_sub]
    exact ((Λ (τ x)).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hlim : Tendsto (fun x => B * ‖z x - z₀‖) l (𝓝 0) := by
    have hz' : Tendsto (fun x => ‖z x - z₀‖) l (𝓝 0) := by
      simpa using (hz.sub_const z₀).norm
    simpa using hz'.const_mul B
  simpa using (squeeze_zero_norm' hbd hlim).add h1

def convKernel (Λ : ℝ → Z →L[ℝ] X) {L : ℝ} (w : C(Icc (0 : ℝ) L, ℝ)) (ζ : Piece Z L)
    (s r : ℝ) : X :=
  extendPiece w (s - r) • Λ r (extendPiece ζ (s - r))

variable (Λ : ℝ → Z →L[ℝ] X) {L C : ℝ} (w : C(Icc (0 : ℝ) L, ℝ))

theorem convKernel_continuousOn (hC : 0 ≤ C)
    (hΛ : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)))
    (hΛc : ∀ ζ, ContinuousOn (fun τ => Λ τ ζ) (Ioi 0)) (ζ : Piece Z L) (s : ℝ) :
    ContinuousOn (convKernel Λ w ζ s) (Ioc 0 1) := by
  intro r₀ hr₀
  have hw : Continuous (fun r : ℝ => extendPiece w (s - r)) :=
    (extend_continuous w).comp (continuous_const.sub continuous_id)
  have hz : Continuous (fun r : ℝ => extendPiece ζ (s - r)) :=
    (extend_continuous ζ).comp (continuous_const.sub continuous_id)
  have hB : ∀ᶠ r in 𝓝[Ioc 0 1] r₀, ‖Λ r‖ ≤ C * (r₀ / 2) ^ (-(3 / 4 : ℝ)) := by
    have h2 : ∀ᶠ r in 𝓝[Ioc 0 1] r₀, r₀ / 2 < r :=
      nhdsWithin_le_nhds (lt_mem_nhds (by linarith [hr₀.1]))
    filter_upwards [h2, self_mem_nhdsWithin] with r hr hr'
    refine (hΛ r hr'.1 hr'.2).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hr₀.1]) hr.le (by norm_num)
  exact Tendsto.smul ((hw.tendsto r₀).mono_left nhdsWithin_le_nhds)
    (tendsto_apply Λ hΛc (τ := fun r => r) hr₀.1 (tendsto_id.mono_left nhdsWithin_le_nhds)
      ((hz.tendsto r₀).mono_left nhdsWithin_le_nhds) hB)

theorem convKernel_continuous_left (ζ : Piece Z L) (r : ℝ) :
    Continuous (fun s => convKernel Λ w ζ s r) := by
  have hw : Continuous (fun s : ℝ => extendPiece w (s - r)) :=
    (extend_continuous w).comp (continuous_id.sub continuous_const)
  have hz : Continuous (fun s : ℝ => extendPiece ζ (s - r)) :=
    (extend_continuous ζ).comp (continuous_id.sub continuous_const)
  exact hw.smul ((Λ r).continuous.comp hz)

theorem norm_convKernel_le (hC : 0 ≤ C)
    (hΛ : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ))) (ζ : Piece Z L) (s r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖convKernel Λ w ζ s r‖ ≤ ‖w‖ * C * ‖ζ‖ * r ^ (-(3 / 4 : ℝ)) := by
  unfold convKernel
  rw [norm_smul]
  calc ‖extendPiece w (s - r)‖ * ‖Λ r (extendPiece ζ (s - r))‖
      ≤ ‖w‖ * (C * r ^ (-(3 / 4 : ℝ)) * ‖ζ‖) :=
        mul_le_mul (norm_extend_le w _) (((Λ r).le_opNorm _).trans
          (mul_le_mul (hΛ r hr hr1) (norm_extend_le ζ _) (norm_nonneg _)
            (mul_nonneg hC (Real.rpow_nonneg hr.le _)))) (norm_nonneg _) (norm_nonneg _)
    _ = ‖w‖ * C * ‖ζ‖ * r ^ (-(3 / 4 : ℝ)) := by ring

theorem bound_integrableOn (K : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun r : ℝ => K * r ^ (-(3 / 4 : ℝ))) (Ioc 0 c) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K)

theorem convKernel_integrable (hC : 0 ≤ C)
    (hΛ : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)))
    (hΛc : ∀ ζ, ContinuousOn (fun τ => Λ τ ζ) (Ioi 0)) (ζ : Piece Z L) (s : ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) : IntervalIntegrable (convKernel Λ w ζ s) volume 0 c := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc]
  refine Integrable.mono' (bound_integrableOn (‖w‖ * C * ‖ζ‖) hc)
    (((convKernel_continuousOn Λ w hC hΛ hΛc ζ s).mono (Ioc_subset_Ioc_right hc1)).aestronglyMeasurable
      measurableSet_Ioc) ?_
  exact (ae_restrict_mem measurableSet_Ioc).mono fun r hr =>
    norm_convKernel_le Λ w hC hΛ ζ s r hr.1 (hr.2.trans hc1)

theorem integral_rpow_three_quarters (c : ℝ) :
    ∫ r in (0 : ℝ)..c, r ^ (-(3 / 4 : ℝ)) = 4 * c ^ (1 / 4 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  have e : (-(3 / 4 : ℝ)) + 1 = 1 / 4 := by norm_num
  rw [e, Real.zero_rpow (by norm_num)]
  ring

def convFun (ζ : Piece Z L) (s : ℝ) : X := ∫ r in (0 : ℝ)..s, convKernel Λ w ζ s r

theorem convFun_eq (ζ : Piece Z L) (s : ℝ) :
    ∫ σ in (0 : ℝ)..s, (extendPiece w σ) • Λ (s - σ) (extendPiece ζ σ) = convFun Λ w ζ s := by
  calc ∫ σ in (0 : ℝ)..s, (extendPiece w σ) • Λ (s - σ) (extendPiece ζ σ)
      = ∫ σ in (0 : ℝ)..s, convKernel Λ w ζ s (s - σ) := by
        simp only [convKernel, sub_sub_cancel]
    _ = ∫ r in s - s..s - 0, convKernel Λ w ζ s r :=
        intervalIntegral.integral_comp_sub_left (convKernel Λ w ζ s) s
    _ = convFun Λ w ζ s := by rw [sub_self, sub_zero]; rfl

theorem norm_convFun_le (hL1 : L ≤ 1) (hC : 0 ≤ C)
    (hΛ : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ))) (ζ : Piece Z L) (s : ℝ)
    (hs : s ∈ Icc 0 L) : ‖convFun Λ w ζ s‖ ≤ 4 * C * L ^ (1 / 4 : ℝ) * ‖w‖ * ‖ζ‖ := by
  have hK : 0 ≤ ‖w‖ * C * ‖ζ‖ := mul_nonneg (mul_nonneg (norm_nonneg _) hC) (norm_nonneg _)
  have hr : s ^ (1 / 4 : ℝ) ≤ L ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hs.1 hs.2 (by norm_num)
  calc ‖convFun Λ w ζ s‖ ≤ ∫ r in (0 : ℝ)..s, ‖w‖ * C * ‖ζ‖ * r ^ (-(3 / 4 : ℝ)) :=
        intervalIntegral.norm_integral_le_of_norm_le hs.1
          (Eventually.of_forall fun r hr =>
            norm_convKernel_le Λ w hC hΛ ζ s r hr.1 (hr.2.trans (hs.2.trans hL1)))
          ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
    _ = ‖w‖ * C * ‖ζ‖ * (4 * s ^ (1 / 4 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow_three_quarters]
    _ ≤ ‖w‖ * C * ‖ζ‖ * (4 * L ^ (1 / 4 : ℝ)) := by gcongr
    _ = 4 * C * L ^ (1 / 4 : ℝ) * ‖w‖ * ‖ζ‖ := by ring

theorem convFun_continuousOn (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hC : 0 ≤ C)
    (hΛ : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)))
    (hΛc : ∀ ζ, ContinuousOn (fun τ => Λ τ ζ) (Ioi 0)) (ζ : Piece Z L) :
    ContinuousOn (convFun Λ w ζ) (Icc 0 L) := by
  have hrep : ∀ s ∈ Icc 0 L, convFun Λ w ζ s =
      ∫ r in Ioc 0 L, (Iic s).indicator (convKernel Λ w ζ s) r := by
    intro s hs
    rw [convFun, intervalIntegral.integral_of_le hs.1, setIntegral_indicator measurableSet_Iic,
      Ioc_inter_Iic, inf_eq_right.2 hs.2]
  have hcont : Continuous (fun s =>
      ∫ r in Ioc 0 L, (Iic s).indicator (convKernel Λ w ζ s) r) := by
    rw [continuous_iff_continuousAt]
    intro s₀
    refine tendsto_integral_filter_of_dominated_convergence
      (fun r => ‖w‖ * C * ‖ζ‖ * r ^ (-(3 / 4 : ℝ))) ?_ ?_ (bound_integrableOn _ hL0) ?_
    · exact Eventually.of_forall fun s =>
        (((convKernel_continuousOn Λ w hC hΛ hΛc ζ s).mono
          (Ioc_subset_Ioc_right hL1)).aestronglyMeasurable measurableSet_Ioc).indicator
          measurableSet_Iic
    · exact Eventually.of_forall fun s => (ae_restrict_mem measurableSet_Ioc).mono fun r hr =>
        (norm_indicator_le_norm_self _ _).trans
          (norm_convKernel_le Λ w hC hΛ ζ s r hr.1 (hr.2.trans hL1))
    · have hne : ∀ᵐ r ∂(volume.restrict (Ioc 0 L)), r ≠ s₀ := by
        refine ae_restrict_of_ae ?_
        rw [ae_iff]
        simp
      filter_upwards [hne] with r hne
      have hk := (convKernel_continuous_left Λ w ζ r).tendsto s₀
      rcases lt_or_gt_of_ne hne with h | h
      · rw [indicator_of_mem (mem_Iic.2 h.le)]
        refine hk.congr' ?_
        filter_upwards [lt_mem_nhds h] with s hs
        exact (indicator_of_mem (mem_Iic.2 hs.le) _).symm
      · rw [indicator_of_notMem (by simpa using h)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [gt_mem_nhds h] with s hs
        exact (indicator_of_notMem (by simpa using hs) _).symm
  exact hcont.continuousOn.congr hrep

theorem convFun_add (hL1 : L ≤ 1) (hC : 0 ≤ C)
    (hΛ : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)))
    (hΛc : ∀ ζ, ContinuousOn (fun τ => Λ τ ζ) (Ioi 0)) (ζ ζ' : Piece Z L) (s : ℝ)
    (hs : s ∈ Icc 0 L) : convFun Λ w (ζ + ζ') s = convFun Λ w ζ s + convFun Λ w ζ' s := by
  have e : convKernel Λ w (ζ + ζ') s = fun r => convKernel Λ w ζ s r + convKernel Λ w ζ' s r := by
    funext r
    simp only [convKernel, extend_add, map_add, smul_add]
  rw [convFun, e]
  exact intervalIntegral.integral_add
    (convKernel_integrable Λ w hC hΛ hΛc ζ s hs.1 (hs.2.trans hL1))
    (convKernel_integrable Λ w hC hΛ hΛc ζ' s hs.1 (hs.2.trans hL1))

theorem convFun_smul (c : ℝ) (ζ : Piece Z L) (s : ℝ) :
    convFun Λ w (c • ζ) s = c • convFun Λ w ζ s := by
  have e : convKernel Λ w (c • ζ) s = fun r => c • convKernel Λ w ζ s r := by
    funext r
    simp only [convKernel, extend_smul, map_smul]
    rw [smul_comm]
  rw [convFun, e]
  exact intervalIntegral.integral_smul _ _

def convPiece (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hC : 0 ≤ C)
    (hΛ : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)))
    (hΛc : ∀ ζ, ContinuousOn (fun τ => Λ τ ζ) (Ioi 0)) (ζ : Piece Z L) : Piece X L :=
  ⟨fun s => convFun Λ w ζ s, (convFun_continuousOn Λ w hL0 hL1 hC hΛ hΛc ζ).domRestrict⟩

def convCLM (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hC : 0 ≤ C)
    (hΛ : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)))
    (hΛc : ∀ ζ, ContinuousOn (fun τ => Λ τ ζ) (Ioi 0)) : Piece Z L →L[ℝ] Piece X L :=
  LinearMap.mkContinuous
    { toFun := convPiece Λ w hL0 hL1 hC hΛ hΛc
      map_add' := fun ζ ζ' => by
        ext s
        exact convFun_add Λ w hL1 hC hΛ hΛc ζ ζ' s s.2
      map_smul' := fun c ζ => by
        ext s
        exact convFun_smul Λ w c ζ s }
    (4 * C * L ^ (1 / 4 : ℝ) * ‖w‖) (fun ζ => by
      have h0 : 0 ≤ 4 * C * L ^ (1 / 4 : ℝ) * ‖w‖ :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg hL0 _))
          (norm_nonneg _)
      refine (ContinuousMap.norm_le _ (mul_nonneg h0 (norm_nonneg _))).2 fun s => ?_
      exact norm_convFun_le Λ w hL1 hC hΛ ζ s s.2)

end Conv

end SeqOps.Internal

open SeqOps.Internal

theorem seqOpSpec : SeqOpSpec := by
  intro E X _ _ _ _ _ _ A C hA hC
  have hex : ∃ T : lp (fun _ : ℕ => E) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞, ∀ g n, T g n = A n (g n) :=
    ⟨opCLM A hA hC, fun _ _ => rfl⟩
  have h1 : ∀ g n, seqOp A g n = A n (g n) := by
    intro g n
    unfold seqOp
    rw [dif_pos hex]
    exact hex.choose_spec g n
  refine ⟨h1, ?_, fun B hB => ?_, fun A₀ => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ hC fun g => ?_
    refine lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg _)) fun n => ?_
    rw [h1]
    exact norm_apply_le A hA g n
  · have hexB : ∃ T : lp (fun _ : ℕ => X) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞,
        ∀ g n, T g n = if n = 0 then 0 else B (n - 1) (g (n - 1)) :=
      ⟨shiftCLM B hB hC, fun _ _ => rfl⟩
    have h2 : ∀ g n, seqShift B g n = if n = 0 then 0 else B (n - 1) (g (n - 1)) := by
      intro g n
      unfold seqShift
      rw [dif_pos hexB]
      exact hexB.choose_spec g n
    refine ⟨h2, ContinuousLinearMap.opNorm_le_bound _ hC fun g => ?_⟩
    refine lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg _)) fun n => ?_
    rw [h2]
    exact shift_le B hB hC g n
  · have hexS : ∃ T : E →L[ℝ] lp (fun _ : ℕ => X) ∞, ∀ e n, T e n = if n = 0 then A₀ e else 0 :=
      ⟨seedCLM A₀, fun _ _ => rfl⟩
    have h3 : ∀ e n, seqSeed A₀ e n = if n = 0 then A₀ e else 0 := by
      intro e n
      unfold seqSeed
      rw [dif_pos hexS]
      exact hexS.choose_spec e n
    refine ⟨h3, ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun e => ?_⟩
    refine lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun n => ?_
    rw [h3]
    exact (seed_le A₀ e n).trans (A₀.le_opNorm e)

theorem pieceCompSpec : PieceCompSpec := by
  intro E X _ _ _ _ _ _ L A hL
  have hex : ∃ T : Piece E L →L[ℝ] Piece X L, ∀ f s, T f s = A (f s) :=
    ⟨ContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) L) A, fun _ _ => rfl⟩
  have h1 : ∀ f s, pieceComp L A f s = A (f s) := by
    intro f s
    unfold pieceComp
    rw [dif_pos hex]
    exact hex.choose_spec f s
  refine ⟨h1, ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_⟩
  refine (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 fun s => ?_
  rw [h1]
  exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm s) (norm_nonneg _))

theorem pieceConvSpec : PieceConvSpec := by
  intro Z X _ _ _ _ _ _ L Λ w C hL hL1 hC hΛ hΛc
  have hex : ∃ T : Piece Z L →L[ℝ] Piece X L, ∀ ζ (s : Icc (0 : ℝ) L),
      T ζ s = ∫ σ in (0 : ℝ)..s, (extendPiece w σ) • Λ (s - σ) (extendPiece ζ σ) :=
    ⟨convCLM Λ w hL.le hL1 hC hΛ hΛc, fun ζ s => (convFun_eq Λ w ζ s).symm⟩
  have h1 : ∀ ζ (s : Icc (0 : ℝ) L),
      pieceConv L Λ w ζ s = ∫ σ in (0 : ℝ)..s, (extendPiece w σ) • Λ (s - σ) (extendPiece ζ σ) := by
    intro ζ s
    unfold pieceConv
    rw [dif_pos hex]
    exact hex.choose_spec ζ s
  have h0 : 0 ≤ 4 * C * L ^ (1 / 4 : ℝ) * ‖w‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg hL.le _))
      (norm_nonneg _)
  refine ⟨h1, ContinuousLinearMap.opNorm_le_bound _ h0 fun ζ => ?_⟩
  refine (ContinuousMap.norm_le _ (mul_nonneg h0 (norm_nonneg _))).2 fun s => ?_
  rw [h1, convFun_eq]
  exact norm_convFun_le Λ w hL1 hC hΛ ζ s s.2

end Breakdown.Periodic
