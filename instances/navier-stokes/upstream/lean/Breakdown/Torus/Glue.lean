import Breakdown.Torus.StatementsSteps
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace Glue.Internal

def TorusVarConst (u : ℝ → V) (a t : ℝ) : Prop :=
  IntervalIntegrable (fun s => kernel (t - s) (u s) (u s)) volume a t ∧
    u t = heat (t - a) (u a) + ∫ s in a..t, kernel (t - s) (u s) (u s)

theorem unitFrame_K (hK : KernelSharpBound) : (stepFrame hK 1 one_pos le_rfl).K = kernel := by
  funext τ
  show (1 : ℝ) ^ (3 / 4 : ℝ) • kernel (1 * τ) = kernel τ
  rw [Real.one_rpow, one_smul, one_mul]

theorem unitFrame_G (hK : KernelSharpBound) : (stepFrame hK 1 one_pos le_rfl).G = heat := by
  funext τ
  show heat (1 * τ) = heat τ
  rw [one_mul]

theorem unitFrame_varConst_iff (hK : KernelSharpBound) (u : ℝ → V) (a t : ℝ) :
    (stepFrame hK 1 one_pos le_rfl).VarConst u a t ↔ TorusVarConst u a t := by
  unfold HeatBilinear.VarConst TorusVarConst
  rw [unitFrame_K, unitFrame_G]

theorem torusVarConst_congr {u v : ℝ → V} {a t : ℝ} (hat : a ≤ t) (h : EqOn u v (Icc a t))
    (hu : TorusVarConst u a t) : TorusVarConst v a t := by
  have hE : EqOn (fun s => kernel (t - s) (u s) (u s)) (fun s => kernel (t - s) (v s) (v s))
      (uIcc a t) := by
    intro s hs
    rw [uIcc_of_le hat] at hs
    simp only [h hs]
  refine ⟨hu.1.congr (hE.mono uIoc_subset_uIcc), ?_⟩
  rw [← h ⟨hat, le_rfl⟩, ← h ⟨le_rfl, hat⟩, ← intervalIntegral.integral_congr hE]
  exact hu.2

theorem extendPiece_cont {L : ℝ} (f : Piece V L) : Continuous (extendPiece f) := by
  rcases le_or_gt 0 L with h | h
  · exact (f.continuous.Icc_extend' (h := h)).congr fun t => by simp [extendPiece, h]
  · exact (continuous_const (y := (0 : V))).congr fun t => by simp [extendPiece, not_le.2 h]

theorem extendPiece_right {L : ℝ} (hL : 0 ≤ L) (f : Piece V L) :
    extendPiece f L = pieceEnd L f := by
  simp [extendPiece, pieceEnd, hL, IccExtend_right]

theorem affine_cancel {μ : ℝ} (hμ : μ ≠ 0) (x y : ℝ) : x + μ * ((y - x) / μ) = y := by
  rw [mul_div_cancel₀ _ hμ]
  ring

theorem stepNumber_eq {T lam t : ℝ} {n : ℕ} (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1)
    (h1 : T * lam ^ (n + 1) < T - t) (h2 : T - t ≤ T * lam ^ n) : stepNumber T lam t = n := by
  have hlog : Real.log lam < 0 := Real.log_neg hl hl1
  have hq0 : 0 < (T - t) / T := div_pos ((mul_pos hT (pow_pos hl _)).trans h1) hT
  have e1 : lam ^ (n + 1) < (T - t) / T := by
    rw [lt_div_iff₀ hT, mul_comm]
    exact h1
  have e2 : (T - t) / T ≤ lam ^ n := by
    rw [div_le_iff₀ hT, mul_comm]
    exact h2
  have hq1 : Real.log ((T - t) / T) ≤ 0 :=
    Real.log_nonpos hq0.le (e2.trans (pow_le_one₀ hl.le hl1.le))
  unfold stepNumber
  rw [Nat.floor_eq_iff (div_nonneg_of_nonpos hq1 hlog.le), le_div_iff_of_neg hlog,
    div_lt_iff_of_neg hlog]
  refine ⟨?_, ?_⟩
  · rw [← Real.log_pow]
    exact Real.log_le_log hq0 e2
  · have h3 := Real.log_lt_log (pow_pos hl _) e1
    rw [Real.log_pow] at h3
    push_cast at h3
    exact h3

theorem scale_succ (T lam : ℝ) (n : ℕ) : stepScale T lam (n + 1) = stepScale T lam n * lam := by
  simp only [stepScale, pow_succ, mul_assoc]

theorem start_succ (T lam : ℝ) (n : ℕ) :
    stepStart T lam (n + 1) = stepStart T lam n + stepScale T lam n * (1 - lam) := by
  simp only [stepStart]
  rw [scale_succ]
  ring

theorem glue_at {T lam : ℝ} (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1)
    (u : ℕ → Piece V (1 - lam))
    (hlink : ∀ n, extendPiece (u (n + 1)) 0 = lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (u n))
    (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (1 - lam)) :
    gluePieces T lam u (stepStart T lam n + stepScale T lam n * s) =
      (stepScale T lam n) ^ (-(1 / 4 : ℝ)) • extendPiece (u n) s := by
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
    simp only [gluePieces, hN]
    rw [← start_succ, sub_self, zero_div, hlink n, extendPiece_right (by linarith) (u n),
      smul_smul, scale_succ]
    congr 1
    rw [Real.mul_rpow hμ.le hl.le, mul_assoc, ← Real.rpow_add hl]
    norm_num
  · have hN : stepNumber T lam (stepStart T lam n + stepScale T lam n * s) = n := by
      apply stepNumber_eq hT hl hl1
      · rw [hd, pow_succ, ← mul_assoc]
        exact mul_lt_mul_of_pos_left (by linarith) (mul_pos hT (pow_pos hl _))
      · rw [hd]
        have := mul_pos hT (pow_pos hl n)
        nlinarith [hs.1]
    simp only [gluePieces, hN, add_sub_cancel_left, mul_div_cancel_left₀ _ hμ.ne']

theorem piece_varConst (hK : KernelSharpBound) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    {L t₀ t : ℝ} {a : ℝ → V} (ha : (stepFrame hK μ hμ hμ1).IsMildOnIcc a 0 L)
    (ht : t ∈ Icc t₀ (t₀ + μ * L)) :
    TorusVarConst (fun r => μ ^ (-(1 / 4 : ℝ)) • a ((r - t₀) / μ)) t₀ t := by
  obtain ⟨s, hsdef⟩ : ∃ s, s = (t - t₀) / μ := ⟨_, rfl⟩
  have hs : s ∈ Icc 0 L := by
    rw [hsdef]
    exact ⟨div_nonneg (by linarith [ht.1]) hμ.le, by rw [div_le_iff₀ hμ]; linarith [ht.2]⟩
  obtain ⟨hint, heq⟩ := ha.2 s hs
  have hK' : ∀ τ, (stepFrame hK μ hμ hμ1).K τ = μ ^ (3 / 4 : ℝ) • kernel (μ * τ) := fun τ => rfl
  have hG' : ∀ τ, (stepFrame hK μ hμ hμ1).G τ = heat (μ * τ) := fun τ => rfl
  simp only [hK', hG', ContinuousLinearMap.smul_apply, sub_zero] at hint heq
  have hpos : 0 < μ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hμ _
  have hg : IntervalIntegrable (fun σ => kernel (μ * (s - σ)) (a σ) (a σ)) volume 0 s := by
    have h2 := hint.smul (μ ^ (3 / 4 : ℝ))⁻¹
    have e : (fun σ => kernel (μ * (s - σ)) (a σ) (a σ)) =
        (μ ^ (3 / 4 : ℝ))⁻¹ • fun σ => μ ^ (3 / 4 : ℝ) • kernel (μ * (s - σ)) (a σ) (a σ) := by
      funext σ
      simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [e]
    exact h2
  have key : ∀ r, t - r = μ * (s - (r - t₀) / μ) := fun r => by
    rw [hsdef, mul_sub, mul_div_cancel₀ _ hμ.ne', mul_div_cancel₀ _ hμ.ne']
    ring
  have hc : ∀ r, kernel (t - r) (μ ^ (-(1 / 4 : ℝ)) • a ((r - t₀) / μ))
      (μ ^ (-(1 / 4 : ℝ)) • a ((r - t₀) / μ)) =
      (μ ^ (-(1 / 4 : ℝ)) * μ ^ (-(1 / 4 : ℝ))) •
        kernel (μ * (s - (r - t₀) / μ)) (a ((r - t₀) / μ)) (a ((r - t₀) / μ)) := fun r => by
    simp only [key r, map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  have hts : μ * s + t₀ = t := by
    rw [hsdef, mul_div_cancel₀ _ hμ.ne']
    ring
  have hcomp : IntervalIntegrable
      (fun r => kernel (μ * (s - (r - t₀) / μ)) (a ((r - t₀) / μ)) (a ((r - t₀) / μ)))
      volume t₀ t := by
    have h1 := (hg.comp_mul_left (c := μ⁻¹)).comp_sub_right t₀
    have e1 : (0 : ℝ) / μ⁻¹ + t₀ = t₀ := by simp
    have e2 : s / μ⁻¹ + t₀ = t := by rw [div_inv_eq_mul, mul_comm]; exact hts
    rw [e1, e2] at h1
    simpa only [div_eq_inv_mul] using h1
  refine ⟨?_, ?_⟩
  · simp only [hc]
    exact (hcomp.smul (μ ^ (-(1 / 4 : ℝ)) * μ ^ (-(1 / 4 : ℝ)))).congr fun r _ => rfl
  · have hsub := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := s)
      (fun r => kernel (μ * (s - (r - t₀) / μ)) (a ((r - t₀) / μ)) (a ((r - t₀) / μ))) μ t₀
    have e3 : μ * 0 + t₀ = t₀ := by ring
    rw [e3, hts] at hsub
    beta_reduce at hsub
    have e5 : ∀ x, (μ * x + t₀ - t₀) / μ = x := fun x => by
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hμ.ne']
    simp only [e5] at hsub
    have hts' : t - t₀ = μ * s := by rw [← hts]; ring
    have hI : ∫ r in t₀..t, kernel (t - r) (μ ^ (-(1 / 4 : ℝ)) • a ((r - t₀) / μ))
        (μ ^ (-(1 / 4 : ℝ)) • a ((r - t₀) / μ)) =
        ((μ ^ (-(1 / 4 : ℝ)) * μ ^ (-(1 / 4 : ℝ))) * μ) •
          ∫ σ in (0 : ℝ)..s, kernel (μ * (s - σ)) (a σ) (a σ) := by
      simp only [hc, intervalIntegral.integral_smul]
      rw [← hsub, smul_smul]
    have hA : a s = heat (μ * s) (a 0) +
        μ ^ (3 / 4 : ℝ) • ∫ σ in (0 : ℝ)..s, kernel (μ * (s - σ)) (a σ) (a σ) := by
      rw [heq, intervalIntegral.integral_smul]
    have hscal : μ ^ (-(1 / 4 : ℝ)) * μ ^ (3 / 4 : ℝ) =
        μ ^ (-(1 / 4 : ℝ)) * μ ^ (-(1 / 4 : ℝ)) * μ := by
      rw [← Real.rpow_add hμ, ← Real.rpow_add hμ, ← Real.rpow_add_one hμ.ne']
      norm_num
    show μ ^ (-(1 / 4 : ℝ)) • a ((t - t₀) / μ) =
      heat (t - t₀) (μ ^ (-(1 / 4 : ℝ)) • a ((t₀ - t₀) / μ)) +
        ∫ r in t₀..t, kernel (t - r) (μ ^ (-(1 / 4 : ℝ)) • a ((r - t₀) / μ))
          (μ ^ (-(1 / 4 : ℝ)) • a ((r - t₀) / μ))
    have hX : a ((t - t₀) / μ) = a s := by rw [hsdef]
    have hH : heat (t - t₀) (μ ^ (-(1 / 4 : ℝ)) • a ((t₀ - t₀) / μ)) =
        μ ^ (-(1 / 4 : ℝ)) • heat (μ * s) (a 0) := by
      rw [sub_self, zero_div, hts', ContinuousLinearMap.map_smul]
    have hfin : ∀ x y : V, μ ^ (-(1 / 4 : ℝ)) • (x + μ ^ (3 / 4 : ℝ) • y) =
        μ ^ (-(1 / 4 : ℝ)) • x + (μ ^ (-(1 / 4 : ℝ)) * μ ^ (-(1 / 4 : ℝ)) * μ) • y := by
      intro x y
      rw [smul_add, smul_smul, hscal]
    rw [hI, hX, hH, hA]
    exact hfin _ _

theorem glue_upto (hK : KernelSharpBound) (hC : ConcatStatement) {T lam : ℝ} (hT : 0 < T)
    (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam < 1) (u : ℕ → Piece V (1 - lam))
    (hm : ∀ n, (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1.le n)).IsMildOnIcc (extendPiece (u n)) 0 (1 - lam))
    (hlink : ∀ n, extendPiece (u (n + 1)) 0 = lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (u n))
    (n : ℕ) :
    ContinuousOn (gluePieces T lam u) (Icc 0 (stepStart T lam n)) ∧
      ∀ t ∈ Icc 0 (stepStart T lam n), TorusVarConst (gluePieces T lam u) 0 t := by
  induction n with
  | zero =>
    have h0 : stepStart T lam 0 = 0 := by simp [stepStart, stepScale]
    rw [h0, Icc_self]
    refine ⟨continuousOn_singleton _ _, ?_⟩
    rintro t rfl
    refine ⟨IntervalIntegrable.refl, ?_⟩
    rw [sub_self, intervalIntegral.integral_same, heat_zero, add_zero, ContinuousLinearMap.id_apply]
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
    have hEq : EqOn (gluePieces T lam u)
        (fun r => stepScale T lam n ^ (-(1 / 4 : ℝ)) •
          extendPiece (u n) ((r - stepStart T lam n) / stepScale T lam n))
        (Icc (stepStart T lam n) (stepStart T lam (n + 1))) := by
      intro r hr
      rw [hsucc] at hr
      have hs : (r - stepStart T lam n) / stepScale T lam n ∈ Icc 0 (1 - lam) :=
        ⟨div_nonneg (by linarith [hr.1]) hμ.le, by rw [div_le_iff₀ hμ]; linarith [hr.2]⟩
      have e := glue_at hT hl hl1 u hlink n _ hs
      rw [affine_cancel hμ.ne'] at e
      exact e
    have hvc : Continuous (fun r => stepScale T lam n ^ (-(1 / 4 : ℝ)) •
        extendPiece (u n) ((r - stepStart T lam n) / stepScale T lam n)) :=
      (((extendPiece_cont (u n)).comp ((continuous_sub_right (stepStart T lam n)).div_const
        (stepScale T lam n))).const_smul (stepScale T lam n ^ (-(1 / 4 : ℝ)))).congr fun r => rfl
    have hcn : ContinuousOn (gluePieces T lam u) (Icc (stepStart T lam n) (stepStart T lam (n + 1))) :=
      hvc.continuousOn.congr hEq
    have hc' : ContinuousOn (gluePieces T lam u) (Icc 0 (stepStart T lam (n + 1))) := by
      rw [← Icc_union_Icc_eq_Icc h0 hmono]
      exact hc.union_of_isClosed hcn isClosed_Icc isClosed_Icc
    refine ⟨hc', fun t ht => ?_⟩
    rcases le_or_gt t (stepStart T lam n) with htn | htn
    · exact hd t ⟨ht.1, htn⟩
    · have htI : t ∈ Icc (stepStart T lam n) (stepStart T lam n + stepScale T lam n * (1 - lam)) :=
        ⟨htn.le, by rw [← hsucc]; exact ht.2⟩
      have hp := piece_varConst hK hμ hμ1 (hm n) htI
      have hg := torusVarConst_congr htn.le (fun r hr => (hEq ⟨hr.1, hr.2.trans ht.2⟩).symm) hp
      have hH := hC V (stepFrame hK 1 one_pos le_rfl) (gluePieces T lam u) 0 (stepStart T lam n) t
        h0 htn.le (hc'.mono (Icc_subset_Icc le_rfl ht.2))
        ((unitFrame_varConst_iff hK _ _ _).2 (hd _ ⟨h0, le_rfl⟩))
        ((unitFrame_varConst_iff hK _ _ _).2 hg)
      exact (unitFrame_varConst_iff hK _ _ _).1 hH

end Glue.Internal

open Glue.Internal in
theorem glueMild (hR : RestrictStatement) (hC : ConcatStatement) (hS : ShiftStatement)
    (hD : VarConstIntegralStatement) : GlueMild := by
  intro hK T lam hT hT1 hl hl1 u hm hlink
  have cover : ∀ t ∈ Ico (0 : ℝ) T, ∃ n, t < stepStart T lam n := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (sub_pos.2 ht.2) hT) hl1
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hT, mul_comm] at hn
    simp only [stepStart, stepScale]
    linarith
  refine ⟨⟨?_, ?_⟩, fun n s hs => glue_at hT hl hl1 u hlink n s hs⟩
  · intro t ht
    obtain ⟨n, hn⟩ := cover t ht
    have hc := (glue_upto hK hC hT hT1 hl hl1 u hm hlink n).1
    refine (hc t ⟨ht.1, hn.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio _, isOpen_Iio, hn, fun y hy => ⟨hy.2.1, hy.1.le⟩⟩
  · intro t ht
    obtain ⟨n, hn⟩ := cover t ht
    exact (glue_upto hK hC hT hT1 hl hl1 u hm hlink n).2 t ⟨ht.1, hn.le⟩

end Breakdown.Periodic
