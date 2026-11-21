import Breakdown.Frac.StTorusStep
import Breakdown.Transfer.StatementsLocal
import Breakdown.Torus.Glue

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace FracGlue.Internal

open Glue.Internal

def FracMildAt (α : ℝ) (u : ℝ → V) (a t : ℝ) : Prop :=
  IntervalIntegrable (fun s => fracTorusKernel α (t - s) (u s) (u s)) volume a t ∧
    u t = fracTorusHeat α (t - a) (u a) + ∫ s in a..t, fracTorusKernel α (t - s) (u s) (u s)

theorem unitFrame_K (α : ℝ) (hα : 1 < α) :
    (fracStepFrame α hα 1 one_pos le_rfl).K = fracTorusKernel α := by
  funext τ
  show (1 : ℝ) ^ (3 / (4 * α)) • fracTorusKernel α (1 * τ) = fracTorusKernel α τ
  rw [Real.one_rpow, one_smul, one_mul]

theorem unitFrame_G (α : ℝ) (hα : 1 < α) :
    (fracStepFrame α hα 1 one_pos le_rfl).G = fracTorusHeat α := by
  funext τ
  show fracTorusHeat α (1 * τ) = fracTorusHeat α τ
  rw [one_mul]

theorem unitFrame_mildAt_iff (α : ℝ) (hα : 1 < α) (u : ℝ → V) (a t : ℝ) :
    (fracStepFrame α hα 1 one_pos le_rfl).VarConst u a t ↔ FracMildAt α u a t := by
  unfold HeatBilinear.VarConst FracMildAt
  rw [unitFrame_K, unitFrame_G]

theorem fracMildAt_congr {α : ℝ} {u v : ℝ → V} {a t : ℝ} (hat : a ≤ t) (h : EqOn u v (Icc a t))
    (hu : FracMildAt α u a t) : FracMildAt α v a t := by
  have hE : EqOn (fun s => fracTorusKernel α (t - s) (u s) (u s))
      (fun s => fracTorusKernel α (t - s) (v s) (v s)) (uIcc a t) := by
    intro s hs
    rw [uIcc_of_le hat] at hs
    simp only [h hs]
  refine ⟨hu.1.congr (hE.mono uIoc_subset_uIcc), ?_⟩
  rw [← h ⟨hat, le_rfl⟩, ← h ⟨le_rfl, hat⟩, ← intervalIntegral.integral_congr hE]
  exact hu.2

theorem glue_at (α : ℝ) {T lam : ℝ} (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1)
    (u : ℕ → Piece V (1 - lam))
    (hlink : ∀ n, extendPiece (u (n + 1)) 0 = lam ^ dilExponent α • pieceEnd (1 - lam) (u n))
    (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (1 - lam)) :
    fracGluePieces α T lam u (stepStart T lam n + stepScale T lam n * s) =
      (stepScale T lam n) ^ (-dilExponent α) • extendPiece (u n) s := by
  have hμ := stepScale_pos hT hl n
  have hd : T - (stepStart T lam n + stepScale T lam n * s) = T * lam ^ n * (1 - s) := by
    simp only [stepStart, stepScale]
    ring
  rcases eq_or_lt_of_le hs.2 with h | h
  · subst h
    have hN : stepNumber T lam (stepStart T lam n + stepScale T lam n * (1 - lam)) = n + 1 := by
      have e : T * lam ^ n * (1 - (1 - lam)) = T * lam ^ (n + 1) := by ring
      apply stepNumber_eq hT hl hl1
      · rw [hd, e, pow_succ lam (n + 1), ← mul_assoc]
        exact mul_lt_of_lt_one_right (mul_pos hT (pow_pos hl _)) hl1
      · rw [hd, e]
    simp only [fracGluePieces, hN]
    rw [← start_succ, sub_self, zero_div, hlink n, extendPiece_right (by linarith) (u n),
      smul_smul, scale_succ]
    congr 1
    rw [Real.mul_rpow hμ.le hl.le, mul_assoc, ← Real.rpow_add hl, neg_add_cancel,
      Real.rpow_zero, mul_one]
  · have hN : stepNumber T lam (stepStart T lam n + stepScale T lam n * s) = n := by
      apply stepNumber_eq hT hl hl1
      · rw [hd, pow_succ, ← mul_assoc]
        exact mul_lt_mul_of_pos_left (by linarith) (mul_pos hT (pow_pos hl _))
      · rw [hd]
        have := mul_pos hT (pow_pos hl n)
        nlinarith [hs.1]
    simp only [fracGluePieces, hN, add_sub_cancel_left, mul_div_cancel_left₀ _ hμ.ne']

theorem piece_mildIdentity (α : ℝ) (hα : 1 < α) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    {L t₀ t : ℝ} {a : ℝ → V} (ha : (fracStepFrame α hα μ hμ hμ1).IsMildOnIcc a 0 L)
    (ht : t ∈ Icc t₀ (t₀ + μ * L)) :
    FracMildAt α (fun r => μ ^ (-dilExponent α) • a ((r - t₀) / μ)) t₀ t := by
  obtain ⟨s, hsdef⟩ : ∃ s, s = (t - t₀) / μ := ⟨_, rfl⟩
  have hs : s ∈ Icc 0 L := by
    rw [hsdef]
    exact ⟨div_nonneg (by linarith [ht.1]) hμ.le, by rw [div_le_iff₀ hμ]; linarith [ht.2]⟩
  obtain ⟨hint, heq⟩ := ha.2 s hs
  have hK' : ∀ τ, (fracStepFrame α hα μ hμ hμ1).K τ =
      μ ^ (3 / (4 * α)) • fracTorusKernel α (μ * τ) := fun τ => rfl
  have hG' : ∀ τ, (fracStepFrame α hα μ hμ hμ1).G τ = fracTorusHeat α (μ * τ) := fun τ => rfl
  simp only [hK', hG', smul_apply, sub_zero] at hint heq
  have hpos : 0 < μ ^ (3 / (4 * α)) := Real.rpow_pos_of_pos hμ _
  have hg : IntervalIntegrable (fun σ => fracTorusKernel α (μ * (s - σ)) (a σ) (a σ)) volume 0 s := by
    have h2 := hint.smul (μ ^ (3 / (4 * α)))⁻¹
    have e : (fun σ => fracTorusKernel α (μ * (s - σ)) (a σ) (a σ)) =
        (μ ^ (3 / (4 * α)))⁻¹ • fun σ =>
          μ ^ (3 / (4 * α)) • fracTorusKernel α (μ * (s - σ)) (a σ) (a σ) := by
      funext σ
      simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [e]
    exact h2
  have key : ∀ r, t - r = μ * (s - (r - t₀) / μ) := fun r => by
    rw [hsdef, mul_sub, mul_div_cancel₀ _ hμ.ne', mul_div_cancel₀ _ hμ.ne']
    ring
  have hc : ∀ r, fracTorusKernel α (t - r) (μ ^ (-dilExponent α) • a ((r - t₀) / μ))
      (μ ^ (-dilExponent α) • a ((r - t₀) / μ)) =
      (μ ^ (-dilExponent α) * μ ^ (-dilExponent α)) •
        fracTorusKernel α (μ * (s - (r - t₀) / μ)) (a ((r - t₀) / μ)) (a ((r - t₀) / μ)) :=
    fun r => by
      simp only [key r, map_smul, smul_apply, smul_smul]
  have hts : μ * s + t₀ = t := by
    rw [hsdef, mul_div_cancel₀ _ hμ.ne']
    ring
  have hcomp : IntervalIntegrable
      (fun r => fracTorusKernel α (μ * (s - (r - t₀) / μ)) (a ((r - t₀) / μ)) (a ((r - t₀) / μ)))
      volume t₀ t := by
    have h1 := (hg.comp_mul_left (c := μ⁻¹)).comp_sub_right t₀
    have e1 : (0 : ℝ) / μ⁻¹ + t₀ = t₀ := by simp
    have e2 : s / μ⁻¹ + t₀ = t := by rw [div_inv_eq_mul, mul_comm]; exact hts
    rw [e1, e2] at h1
    simpa only [div_eq_inv_mul] using h1
  refine ⟨?_, ?_⟩
  · simp only [hc]
    exact (hcomp.smul (μ ^ (-dilExponent α) * μ ^ (-dilExponent α))).congr fun r _ => rfl
  · have hsub := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := s)
      (fun r => fracTorusKernel α (μ * (s - (r - t₀) / μ)) (a ((r - t₀) / μ))
        (a ((r - t₀) / μ))) μ t₀
    have e3 : μ * 0 + t₀ = t₀ := by ring
    rw [e3, hts] at hsub
    beta_reduce at hsub
    have e5 : ∀ x, (μ * x + t₀ - t₀) / μ = x := fun x => by
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hμ.ne']
    simp only [e5] at hsub
    have hts' : t - t₀ = μ * s := by rw [← hts]; ring
    have hI : ∫ r in t₀..t, fracTorusKernel α (t - r) (μ ^ (-dilExponent α) • a ((r - t₀) / μ))
        (μ ^ (-dilExponent α) • a ((r - t₀) / μ)) =
        ((μ ^ (-dilExponent α) * μ ^ (-dilExponent α)) * μ) •
          ∫ σ in (0 : ℝ)..s, fracTorusKernel α (μ * (s - σ)) (a σ) (a σ) := by
      simp only [hc, intervalIntegral.integral_smul]
      rw [← hsub, smul_smul]
    have hA : a s = fracTorusHeat α (μ * s) (a 0) +
        μ ^ (3 / (4 * α)) • ∫ σ in (0 : ℝ)..s, fracTorusKernel α (μ * (s - σ)) (a σ) (a σ) := by
      rw [heq, intervalIntegral.integral_smul]
    have hscal : μ ^ (-dilExponent α) * μ ^ (3 / (4 * α)) =
        μ ^ (-dilExponent α) * μ ^ (-dilExponent α) * μ := by
      rw [← Real.rpow_add hμ, ← Real.rpow_add hμ, ← Real.rpow_add_one hμ.ne']
      congr 1
      unfold dilExponent
      ring
    show μ ^ (-dilExponent α) • a ((t - t₀) / μ) =
      fracTorusHeat α (t - t₀) (μ ^ (-dilExponent α) • a ((t₀ - t₀) / μ)) +
        ∫ r in t₀..t, fracTorusKernel α (t - r) (μ ^ (-dilExponent α) • a ((r - t₀) / μ))
          (μ ^ (-dilExponent α) • a ((r - t₀) / μ))
    have hX : a ((t - t₀) / μ) = a s := by rw [hsdef]
    have hH : fracTorusHeat α (t - t₀) (μ ^ (-dilExponent α) • a ((t₀ - t₀) / μ)) =
        μ ^ (-dilExponent α) • fracTorusHeat α (μ * s) (a 0) := by
      rw [sub_self, zero_div, hts', ContinuousLinearMap.map_smul]
    have hfin : ∀ x y : V, μ ^ (-dilExponent α) • (x + μ ^ (3 / (4 * α)) • y) =
        μ ^ (-dilExponent α) • x + (μ ^ (-dilExponent α) * μ ^ (-dilExponent α) * μ) • y := by
      intro x y
      rw [smul_add, smul_smul, hscal]
    rw [hI, hX, hH, hA]
    exact hfin _ _

theorem glue_upto (α : ℝ) (hα : 1 < α) (hC : ConcatStatement) {T lam : ℝ} (hT : 0 < T)
    (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam < 1) (u : ℕ → Piece V (1 - lam))
    (hm : ∀ n, (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1.le n)).IsMildOnIcc (extendPiece (u n)) 0 (1 - lam))
    (hlink : ∀ n, extendPiece (u (n + 1)) 0 = lam ^ dilExponent α • pieceEnd (1 - lam) (u n))
    (n : ℕ) :
    ContinuousOn (fracGluePieces α T lam u) (Icc 0 (stepStart T lam n)) ∧
      ∀ t ∈ Icc 0 (stepStart T lam n), FracMildAt α (fracGluePieces α T lam u) 0 t := by
  induction n with
  | zero =>
    have h0 : stepStart T lam 0 = 0 := by simp [stepStart, stepScale]
    rw [h0, Icc_self]
    refine ⟨continuousOn_singleton _ _, ?_⟩
    rintro t rfl
    refine ⟨IntervalIntegrable.refl, ?_⟩
    rw [sub_self, intervalIntegral.integral_same, (fracTorusHeatAlgebra α).2.1, add_zero,
      ContinuousLinearMap.id_apply]
  | succ n ih =>
    obtain ⟨hc, hd⟩ := ih
    have hμ := stepScale_pos hT hl n
    have hμ1 := stepScale_le_one hT1 hl hl1.le n
    have h0 : 0 ≤ stepStart T lam n :=
      sub_nonneg.2 (mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1.le))
    have hsucc := start_succ T lam n
    have hmono : stepStart T lam n ≤ stepStart T lam (n + 1) := by
      rw [hsucc]
      have := mul_pos hμ (sub_pos.2 hl1)
      linarith
    have hEq : EqOn (fracGluePieces α T lam u)
        (fun r => stepScale T lam n ^ (-dilExponent α) •
          extendPiece (u n) ((r - stepStart T lam n) / stepScale T lam n))
        (Icc (stepStart T lam n) (stepStart T lam (n + 1))) := by
      intro r hr
      rw [hsucc] at hr
      have hs : (r - stepStart T lam n) / stepScale T lam n ∈ Icc 0 (1 - lam) :=
        ⟨div_nonneg (by linarith [hr.1]) hμ.le, by rw [div_le_iff₀ hμ]; linarith [hr.2]⟩
      have e := glue_at α hT hl hl1 u hlink n _ hs
      rw [affine_cancel hμ.ne'] at e
      exact e
    have hvc : Continuous (fun r => stepScale T lam n ^ (-dilExponent α) •
        extendPiece (u n) ((r - stepStart T lam n) / stepScale T lam n)) :=
      (((extendPiece_cont (u n)).comp ((continuous_sub_right (stepStart T lam n)).div_const
        (stepScale T lam n))).const_smul (stepScale T lam n ^ (-dilExponent α))).congr fun r => rfl
    have hcn : ContinuousOn (fracGluePieces α T lam u)
        (Icc (stepStart T lam n) (stepStart T lam (n + 1))) :=
      hvc.continuousOn.congr hEq
    have hc' : ContinuousOn (fracGluePieces α T lam u) (Icc 0 (stepStart T lam (n + 1))) := by
      rw [← Icc_union_Icc_eq_Icc h0 hmono]
      exact hc.union_of_isClosed hcn isClosed_Icc isClosed_Icc
    refine ⟨hc', fun t ht => ?_⟩
    rcases le_or_gt t (stepStart T lam n) with htn | htn
    · exact hd t ⟨ht.1, htn⟩
    · have htI : t ∈ Icc (stepStart T lam n) (stepStart T lam n + stepScale T lam n * (1 - lam)) :=
        ⟨htn.le, by rw [← hsucc]; exact ht.2⟩
      have hp := piece_mildIdentity α hα hμ hμ1 (hm n) htI
      have hg := fracMildAt_congr htn.le (fun r hr => (hEq ⟨hr.1, hr.2.trans ht.2⟩).symm) hp
      have hH := hC V (fracStepFrame α hα 1 one_pos le_rfl) (fracGluePieces α T lam u) 0
        (stepStart T lam n) t h0 htn.le (hc'.mono (Icc_subset_Icc le_rfl ht.2))
        ((unitFrame_mildAt_iff α hα _ _ _).2 (hd _ ⟨h0, le_rfl⟩))
        ((unitFrame_mildAt_iff α hα _ _ _).2 hg)
      exact (unitFrame_mildAt_iff α hα _ _ _).1 hH

end FracGlue.Internal

open FracGlue.Internal in
theorem fracGlueMild_of (α : ℝ) (hα : 1 < α) (h1 : RestrictStatement) (h2 : ConcatStatement)
    (h3 : ShiftStatement) : FracGlueMild α hα := by
  intro T lam hT hT1 hl hl1 u hm hlink
  have cover : ∀ t ∈ Ico (0 : ℝ) T, ∃ n, t < stepStart T lam n := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (sub_pos.2 ht.2) hT) hl1
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hT, mul_comm] at hn
    simp only [stepStart, stepScale]
    linarith
  refine ⟨⟨?_, ?_⟩, fun n s hs => glue_at α hT hl hl1 u hlink n s hs⟩
  · intro t ht
    obtain ⟨n, hn⟩ := cover t ht
    have hc := (glue_upto α hα h2 hT hT1 hl hl1 u hm hlink n).1
    refine (hc t ⟨ht.1, hn.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio _, isOpen_Iio, hn, fun y hy => ⟨hy.2.1, hy.1.le⟩⟩
  · intro t ht
    obtain ⟨n, hn⟩ := cover t ht
    exact (glue_upto α hα h2 hT hT1 hl hl1 u hm hlink n).2 t ⟨ht.1, hn.le⟩

end Breakdown.Periodic
