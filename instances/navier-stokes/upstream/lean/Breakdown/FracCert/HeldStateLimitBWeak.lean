import Breakdown.FracCert.Defs
import Breakdown.Cert.WeakCompact
import Breakdown.FracCert.HeldUnique
import Breakdown.FracCert.LinearStateClosed

open scoped ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace WeakFieldLimit

theorem pair_eq {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫ y, inner ℝ (f y) (g y) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem pair_integrable {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem exists_weak_subseq (f : ℕ → Space → Space) (B : ℝ) (hf : ∀ n, MemLp (f n) 2 volume)
    (hb : ∀ n, l2Norm (f n) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : Space → Space, MemLp f₀ 2 volume ∧ l2Norm f₀ ≤ B ∧
      ∀ g : Space → Space, MemLp g 2 volume →
        Tendsto (fun n => ∫ y, inner ℝ (f (φ n) y) (g y)) atTop (𝓝 (∫ y, inner ℝ (f₀ y) (g y))) := by
  have hb' : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B := fun n => by
    rw [← HeldUniqueInternal.l2Norm_eq (hf n)]
    exact hb n
  obtain ⟨φ, x, hφ, hx, hw⟩ := exists_weakly_convergent_subseq (fun n => (hf n).toLp (f n)) B hb'
  have hxm : MemLp (x : Space → Space) 2 volume := Lp.memLp x
  refine ⟨φ, hφ, x, hxm, ?_, ?_⟩
  · rw [HeldUniqueInternal.l2Norm_eq hxm, Lp.toLp_coeFn]
    exact hx
  · intro g hg
    have e1 : ∀ n, ∫ y, inner ℝ (f (φ n) y) (g y) = inner ℝ ((hf (φ n)).toLp (f (φ n))) (hg.toLp g) :=
      fun n => pair_eq (hf (φ n)) hg
    have e2 : ∫ y, inner ℝ ((x : Space → Space) y) (g y) = inner ℝ x (hg.toLp g) := by
      rw [pair_eq hxm hg, Lp.toLp_coeFn]
    simp only [e1, e2]
    exact hw (hg.toLp g)

theorem weighted_lsc {f : ℕ → Space → Space} {f₀ : Space → Space} (hf : ∀ n, MemLp (f n) 2 volume)
    (hf₀ : MemLp f₀ 2 volume) {w : Space → ℝ} {wmax : ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hwm : ∀ y, w y ≤ wmax)
    (hconv : ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (f n y) (g y)) atTop (𝓝 (∫ y, inner ℝ (f₀ y) (g y)))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ y, w y * ‖f₀ y‖ ^ 2 ≤ (∫ y, w y * ‖f n y‖ ^ 2) + ε := by
  intro ε hε
  have hwg : MemLp (fun y => w y • f₀ y) 2 volume := by
    refine MemLp.of_le_mul (c := max wmax 0) hf₀ (hw.aestronglyMeasurable.smul hf₀.1) (ae_of_all _ fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hw0 y)]
    exact mul_le_mul_of_nonneg_right ((hwm y).trans (le_max_left _ _)) (norm_nonneg _)
  have hsq : ∀ {h : Space → Space}, MemLp h 2 volume → Integrable (fun y => w y * ‖h y‖ ^ 2) := by
    intro h hh
    have hi : Integrable (fun y => ‖h y‖ ^ 2) := hh.integrable_norm_pow (by norm_num)
    refine (hi.const_mul (max wmax 0)).mono' (hw.aestronglyMeasurable.mul hi.aestronglyMeasurable)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hw0 y) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right ((hwm y).trans (le_max_left _ _)) (sq_nonneg _)
  have hlim := hconv _ hwg
  have e0 : ∫ y, inner ℝ (f₀ y) (w y • f₀ y) = ∫ y, w y * ‖f₀ y‖ ^ 2 := by
    congr 1
    funext y
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  rw [e0] at hlim
  have hev := (tendsto_order.1 hlim).1 ((∫ y, w y * ‖f₀ y‖ ^ 2) - ε / 2) (by linarith)
  filter_upwards [hev] with n hn
  have hpt : ∀ y, inner ℝ (f n y) (w y • f₀ y) ≤ (w y * ‖f n y‖ ^ 2 + w y * ‖f₀ y‖ ^ 2) / 2 := by
    intro y
    rw [inner_smul_right]
    have h1 : inner ℝ (f n y) (f₀ y) ≤ ‖f n y‖ * ‖f₀ y‖ := real_inner_le_norm _ _
    have h2 : ‖f n y‖ * ‖f₀ y‖ ≤ (‖f n y‖ ^ 2 + ‖f₀ y‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖f n y‖ - ‖f₀ y‖)]
    have := mul_le_mul_of_nonneg_left (h1.trans h2) (hw0 y)
    linarith
  have hint : ∫ y, inner ℝ (f n y) (w y • f₀ y) ≤
      ((∫ y, w y * ‖f n y‖ ^ 2) + ∫ y, w y * ‖f₀ y‖ ^ 2) / 2 := by
    rw [← integral_add (hsq (hf n)) (hsq hf₀), ← integral_div]
    exact integral_mono (pair_integrable (hf n) hwg)
      (((hsq (hf n)).add (hsq hf₀)).div_const 2) hpt
  linarith


def colOp (c : Fin 3 → Space → Space) (y : Space) : Space →L[ℝ] Space :=
  ∑ i : Fin 3, ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ (unitVector i)) (c i y)

theorem colOp_apply (c : Fin 3 → Space → Space) (y : Space) (j : Fin 3) :
    colOp c y (unitVector j) = c j y := by
  simp [colOp, unitVector, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, ite_smul]

theorem colOp_meas {c : Fin 3 → Space → Space} (hc : ∀ i, AEStronglyMeasurable (c i) volume) :
    AEStronglyMeasurable (colOp c) volume := by
  have e : colOp c = fun y => ∑ i : Fin 3,
      ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ (unitVector i)) (c i y) := rfl
  rw [e]
  refine (Finset.aestronglyMeasurable_sum Finset.univ fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ Space Space (innerSL ℝ (unitVector i))).continuous.comp_aestronglyMeasurable (hc i)).congr
    (ae_of_all _ fun y => ?_)
  simp [Finset.sum_apply]

theorem exists_weak_operator_subseq (G : ℕ → Space → (Space →L[ℝ] Space)) (K : ℝ)
    (hm : ∀ n, AEStronglyMeasurable (G n) volume) (hi : ∀ n, Integrable (fun y => entrySq (G n y)))
    (hb : ∀ n, ∫ y, entrySq (G n y) ≤ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G₀ : Space → (Space →L[ℝ] Space), AEStronglyMeasurable G₀ volume ∧
      (∀ i, MemLp (fun y => G₀ y (unitVector i)) 2 volume) ∧
      ∀ i : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
        Tendsto (fun n => ∫ y, inner ℝ (G (φ n) y (unitVector i)) (g y)) atTop
          (𝓝 (∫ y, inner ℝ (G₀ y (unitVector i)) (g y))) := by
  have hcol : ∀ n i, MemLp (fun y => G n y (unitVector i)) 2 volume := fun n i =>
    LinearStateClosedInternal.col_memLp (hm n) (hi n) i
  have hcb : ∀ n i, l2Norm (fun y => G n y (unitVector i)) ≤ Real.sqrt K := by
    intro n i
    unfold l2Norm
    refine Real.sqrt_le_sqrt ((integral_mono ((hcol n i).integrable_norm_pow (by norm_num)) (hi n)
      fun y => LinearStateClosedInternal.entry_le _ i).trans (hb n))
  obtain ⟨φ₀, hφ₀, c₀, hc₀, -, hw₀⟩ := exists_weak_subseq (fun n y => G n y (unitVector 0)) _
    (fun n => hcol n 0) (fun n => hcb n 0)
  obtain ⟨φ₁, hφ₁, c₁, hc₁, -, hw₁⟩ := exists_weak_subseq (fun n y => G (φ₀ n) y (unitVector 1)) _
    (fun n => hcol (φ₀ n) 1) (fun n => hcb (φ₀ n) 1)
  obtain ⟨φ₂, hφ₂, c₂, hc₂, -, hw₂⟩ := exists_weak_subseq (fun n y => G (φ₀ (φ₁ n)) y (unitVector 2)) _
    (fun n => hcol (φ₀ (φ₁ n)) 2) (fun n => hcb (φ₀ (φ₁ n)) 2)
  let c : Fin 3 → Space → Space := ![c₀, c₁, c₂]
  have hcm : ∀ i, MemLp (c i) 2 volume := by
    intro i
    fin_cases i
    · exact hc₀
    · exact hc₁
    · exact hc₂
  refine ⟨fun n => φ₀ (φ₁ (φ₂ n)), hφ₀.comp (hφ₁.comp hφ₂), colOp c, colOp_meas fun i => (hcm i).1, ?_, ?_⟩
  · intro i
    simp only [colOp_apply]
    exact hcm i
  · intro i g hg
    simp only [colOp_apply]
    fin_cases i
    · exact ((hw₀ g hg).comp hφ₁.tendsto_atTop).comp hφ₂.tendsto_atTop
    · exact (hw₁ g hg).comp hφ₂.tendsto_atTop
    · exact hw₂ g hg

theorem entryInner_tendsto {G : ℕ → Space → (Space →L[ℝ] Space)} {G₀ : Space → (Space →L[ℝ] Space)}
    (hG : ∀ n i, MemLp (fun y => G n y (unitVector i)) 2 volume)
    (hG₀ : ∀ i, MemLp (fun y => G₀ y (unitVector i)) 2 volume)
    (hw : ∀ i : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (G n y (unitVector i)) (g y)) atTop
        (𝓝 (∫ y, inner ℝ (G₀ y (unitVector i)) (g y))))
    (E : Space → (Space →L[ℝ] Space)) (hE : AEStronglyMeasurable E volume)
    (hEi : Integrable (fun y => entrySq (E y))) :
    Tendsto (fun n => ∫ y, entryInner (G n y) (E y)) atTop (𝓝 (∫ y, entryInner (G₀ y) (E y))) := by
  have hEc : ∀ i, MemLp (fun y => E y (unitVector i)) 2 volume := fun i =>
    LinearStateClosedInternal.col_memLp hE hEi i
  have e : ∀ F : Space → (Space →L[ℝ] Space), (∀ i, MemLp (fun y => F y (unitVector i)) 2 volume) →
      ∫ y, entryInner (F y) (E y) = ∑ i : Fin 3, ∫ y, inner ℝ (F y (unitVector i)) (E y (unitVector i)) := by
    intro F hF
    unfold entryInner
    exact integral_finset_sum _ fun i _ => pair_integrable (hF i) (hEc i)
  simp only [e _ (hG _), e _ hG₀]
  exact tendsto_finset_sum _ fun i _ => hw i _ (hEc i)

theorem weighted_entry_lsc {G : ℕ → Space → (Space →L[ℝ] Space)} {G₀ : Space → (Space →L[ℝ] Space)}
    (hG : ∀ n i, MemLp (fun y => G n y (unitVector i)) 2 volume)
    (hG₀ : ∀ i, MemLp (fun y => G₀ y (unitVector i)) 2 volume)
    (hw : ∀ i : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (G n y (unitVector i)) (g y)) atTop
        (𝓝 (∫ y, inner ℝ (G₀ y (unitVector i)) (g y))))
    {w : Space → ℝ} {wmax : ℝ} (hwm : Measurable w) (hw0 : ∀ y, 0 ≤ w y) (hwu : ∀ y, w y ≤ wmax) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∫ y, w y * entrySq (G₀ y) ≤ (∫ y, w y * entrySq (G n y)) + ε := by
  intro ε hε
  have hsq : ∀ {h : Space → Space}, MemLp h 2 volume → Integrable (fun y => w y * ‖h y‖ ^ 2) := by
    intro h hh
    have hi : Integrable (fun y => ‖h y‖ ^ 2) := hh.integrable_norm_pow (by norm_num)
    refine (hi.const_mul (max wmax 0)).mono' (hwm.aestronglyMeasurable.mul hi.aestronglyMeasurable)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hw0 y) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right ((hwu y).trans (le_max_left _ _)) (sq_nonneg _)
  have e : ∀ F : Space → (Space →L[ℝ] Space), (∀ i, MemLp (fun y => F y (unitVector i)) 2 volume) →
      ∫ y, w y * entrySq (F y) = ∑ i : Fin 3, ∫ y, w y * ‖F y (unitVector i)‖ ^ 2 := by
    intro F hF
    unfold entrySq
    simp only [Finset.mul_sum]
    exact integral_finset_sum _ fun i _ => hsq (hF i)
  have hev : ∀ i : Fin 3, ∀ᶠ n in atTop, ∫ y, w y * ‖G₀ y (unitVector i)‖ ^ 2 ≤
      (∫ y, w y * ‖G n y (unitVector i)‖ ^ 2) + ε / 3 := fun i =>
    weighted_lsc (fun n => hG n i) (hG₀ i) hwm hw0 hwu (hw i) (ε / 3) (by linarith)
  filter_upwards [Filter.eventually_all.2 hev] with n hn
  rw [e _ hG₀, e _ (hG n)]
  have := Finset.sum_le_sum (s := Finset.univ) fun i _ => hn i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

theorem exists_weak_subseq_family : ∀ (m : ℕ) (f : Fin m → ℕ → Space → Space) (B : ℝ),
    (∀ j n, MemLp (f j n) 2 volume) → (∀ j n, l2Norm (f j n) ≤ B) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : Fin m → Space → Space, (∀ j, MemLp (f₀ j) 2 volume) ∧
      ∀ j, ∀ g : Space → Space, MemLp g 2 volume →
        Tendsto (fun n => ∫ y, inner ℝ (f j (φ n) y) (g y)) atTop (𝓝 (∫ y, inner ℝ (f₀ j y) (g y)))
  | 0, f, B, _, _ => ⟨id, strictMono_id, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩
  | m + 1, f, B, hf, hb => by
    obtain ⟨φ₁, hφ₁, f₁, hf₁, hw₁⟩ :=
      exists_weak_subseq_family m (fun j => f j.castSucc) B (fun j n => hf _ n) (fun j n => hb _ n)
    obtain ⟨φ₂, hφ₂, c, hc, -, hw₂⟩ := exists_weak_subseq (fun n => f (Fin.last m) (φ₁ n)) B
      (fun n => hf _ _) (fun n => hb _ _)
    refine ⟨fun n => φ₁ (φ₂ n), hφ₁.comp hφ₂, Fin.snoc f₁ c, ?_, ?_⟩
    · intro j
      cases j using Fin.lastCases with
      | last => simpa using hc
      | cast j => simpa using hf₁ j
    · intro j g hg
      cases j using Fin.lastCases with
      | last => simpa using hw₂ g hg
      | cast j =>
        simp only [Fin.snoc_castSucc]
        exact (hw₁ j g hg).comp hφ₂.tendsto_atTop

end WeakFieldLimit

end SteadyCert

end Breakdown
