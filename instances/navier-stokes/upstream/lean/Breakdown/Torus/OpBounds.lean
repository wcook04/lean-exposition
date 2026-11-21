import Breakdown.Torus.StatementsInverse
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace OpBounds.Internal

section Seq

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem norm_le_of_seqOp_spec (A : ℕ → E →L[ℝ] X)
    (T : lp (fun _ : ℕ => E) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞) (hT : ∀ g n, T g n = A n (g n))
    (n : ℕ) : ‖A n‖ ≤ ‖T‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  have h1 : ‖T (lp.single (E := fun _ : ℕ => E) ∞ n y) n‖ ≤ ‖T (lp.single (E := fun _ : ℕ => E) ∞ n y)‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero _ n
  have h2 : ‖lp.single (E := fun _ : ℕ => E) ∞ n y‖ ≤ ‖y‖ := by
    refine lp.norm_le_of_forall_le (norm_nonneg y) fun i => ?_
    rw [lp.single_apply]
    by_cases h : i = n
    · subst h
      simp
    · simp [h]
  rw [hT, lp.single_apply, Pi.single_eq_same] at h1
  calc ‖A n y‖ ≤ ‖T (lp.single (E := fun _ : ℕ => E) ∞ n y)‖ := h1
    _ ≤ ‖T‖ * ‖lp.single (E := fun _ : ℕ => E) ∞ n y‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ‖y‖ := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

theorem seqOp_eq_zero (A : ℕ → E →L[ℝ] X) (h : ¬∃ C, ∀ n, ‖A n‖ ≤ C) : seqOp A = 0 := by
  unfold seqOp
  rw [dif_neg]
  rintro ⟨T, hT⟩
  exact h ⟨‖T‖, norm_le_of_seqOp_spec A T hT⟩

theorem norm_seqOp_sub_le (hS : SeqOpSpec) (A B : ℕ → E →L[ℝ] X) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n, ‖A n - B n‖ ≤ C) : ‖seqOp A - seqOp B‖ ≤ C := by
  by_cases hA : ∃ D, ∀ n, ‖A n‖ ≤ D
  · obtain ⟨D, hD⟩ := hA
    have hD0 : 0 ≤ |D| + C := by positivity
    have hAb : ∀ n, ‖A n‖ ≤ |D| + C := fun n => (hD n).trans (by linarith [le_abs_self D])
    have hBb : ∀ n, ‖B n‖ ≤ |D| + C := fun n => by
      calc ‖B n‖ = ‖A n - (A n - B n)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖A n‖ + ‖A n - B n‖ := norm_sub_le _ _
        _ ≤ |D| + C := by linarith [hD n, h n, le_abs_self D]
    have sA := (hS E X A (|D| + C) hAb hD0).1
    have sB := (hS E X B (|D| + C) hBb hD0).1
    have sAB := hS E X (fun n => A n - B n) C h hC
    have e : seqOp A - seqOp B = seqOp (fun n => A n - B n) := by
      refine ContinuousLinearMap.ext fun g => lp.ext (funext fun n => ?_)
      rw [_root_.sub_apply, lp.coeFn_sub, Pi.sub_apply, sA, sB, sAB.1,
        _root_.sub_apply]
    rw [e]
    exact sAB.2.1
  · have hB : ¬∃ D, ∀ n, ‖B n‖ ≤ D := by
      rintro ⟨D, hD⟩
      refine hA ⟨D + C, fun n => ?_⟩
      calc ‖A n‖ = ‖(A n - B n) + B n‖ := by rw [sub_add_cancel]
        _ ≤ ‖A n - B n‖ + ‖B n‖ := norm_add_le _ _
        _ ≤ D + C := by linarith [h n, hD n]
    rw [seqOp_eq_zero A hA, seqOp_eq_zero B hB, sub_self, norm_zero]
    exact hC

end Seq

section Heat

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem ck_nonneg (H : HeatBilinear Y) : 0 ≤ H.CK := by
  have h := H.K_bound 1 one_pos le_rfl
  rw [Real.one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

theorem norm_pieceFree_le (H : HeatBilinear Y) (T : ℝ) : ‖H.pieceFree T‖ ≤ 1 := by
  unfold HeatBilinear.pieceFree
  split_ifs with h
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg x)).2 fun t => ?_
    rw [h.choose_spec x t]
    simpa using (H.G t).le_of_opNorm_le (H.G_norm t t.2.1) x
  · simp

theorem norm_pieceEnd_le (T : ℝ) : ‖(pieceEnd T : Piece Y T →L[ℝ] Y)‖ ≤ 1 := by
  unfold pieceEnd
  split_ifs with h
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul]
    exact ContinuousMap.norm_coe_le_norm f _
  · simp

theorem norm_bil_sub_le (hP : PieceOperatorStatement) (H : HeatBilinear Y) (L M : ℝ) (hL : 0 < L)
    (hL1 : L ≤ 1) (f g : Piece Y L) (h : ‖f - g‖ ≤ M) :
    ‖(2 : ℝ) • H.pieceBil L g - (2 : ℝ) • H.pieceBil L f‖ ≤ 8 * H.CK * L ^ (1 / 4 : ℝ) * M := by
  have hb := (hP Y H L hL).2.1 hL1
  rw [← smul_sub, ← map_sub, norm_smul, Real.norm_two]
  have e : ‖g - f‖ ≤ M := by rwa [norm_sub_rev]
  calc 2 * ‖H.pieceBil L (g - f)‖ ≤ 2 * (‖H.pieceBil L‖ * ‖g - f‖) := by
        gcongr
        exact (H.pieceBil L).le_opNorm _
    _ ≤ 2 * (4 * H.CK * L ^ (1 / 4 : ℝ) * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hb e (norm_nonneg _) ((norm_nonneg _).trans hb))
          (by norm_num)
    _ = 8 * H.CK * L ^ (1 / 4 : ℝ) * M := by ring

theorem norm_seqBil_sub_le (hS : SeqOpSpec) (hP : PieceOperatorStatement) (H : ℕ → HeatBilinear Y)
    (CK L M : ℝ) (hCK : ∀ n, (H n).CK = CK) (hL : 0 < L) (hL1 : L ≤ 1) (f g : ℕ → Piece Y L)
    (h : ∀ n, ‖f n - g n‖ ≤ M) :
    ‖seqOp (fun n => (2 : ℝ) • (H n).pieceBil L (g n)) -
        seqOp (fun n => (2 : ℝ) • (H n).pieceBil L (f n))‖ ≤ 8 * CK * L ^ (1 / 4 : ℝ) * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (h 0)
  have hCK0 : 0 ≤ CK := hCK 0 ▸ ck_nonneg (H 0)
  refine norm_seqOp_sub_le hS _ _ _ (by positivity) fun n => ?_
  have := norm_bil_sub_le hP (H n) L M hL hL1 (f n) (g n) (h n)
  rwa [hCK n] at this

end Heat

theorem norm_comp_snd_le {E Y Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (D : Y →L[ℝ] Z) : ‖D.comp (ContinuousLinearMap.snd ℝ E Y)‖ ≤ ‖D‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have b := ContinuousLinearMap.norm_snd_le ℝ E Y
  calc ‖D‖ * ‖ContinuousLinearMap.snd ℝ E Y‖ ≤ ‖D‖ * 1 := mul_le_mul_of_nonneg_left b (norm_nonneg _)
    _ = ‖D‖ := mul_one _

theorem r3Op_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : MildFramework Freq.X)
    (P : ℝ) (k : ℕ) (θ : ℝ) (J : E →L[ℝ] Freq.X)
    (f g : ℕ → Piece Freq.X (MildFramework.stepLength P k)) :
    r3Op F P k θ J f - r3Op F P k θ J g =
      (seqOp (fun n => (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (g n)) -
        seqOp (fun n => (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (f n))).comp
        (ContinuousLinearMap.snd ℝ _ _) := by
  simp only [r3Op, ContinuousLinearMap.sub_comp]
  abel

theorem norm_chain_sub_le {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (hS : SeqOpSpec)
    (hP : PieceOperatorStatement) (H : ℕ → HeatBilinear Y) (CK L M : ℝ) (hCK : ∀ n, (H n).CK = CK)
    (hL : 0 < L) (hL1 : L ≤ 1) (S : (lp (fun _ : ℕ => Piece Y L) ∞) →L[ℝ] (lp (fun _ : ℕ => Piece Y L) ∞))
    (G : E →L[ℝ] (lp (fun _ : ℕ => Piece Y L) ∞)) (f g : ℕ → Piece Y L) (h : ∀ n, ‖f n - g n‖ ≤ M) :
    ‖((ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - S.comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) -
        G.comp (ContinuousLinearMap.fst ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) -
        (seqOp fun n => (2 : ℝ) • (H n).pieceBil L (f n)).comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞))) -
      ((ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - S.comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) -
        G.comp (ContinuousLinearMap.fst ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) -
        (seqOp fun n => (2 : ℝ) • (H n).pieceBil L (g n)).comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)))‖ ≤
      8 * CK * L ^ (1 / 4 : ℝ) * M := by
  have e : ((ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - S.comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) -
        G.comp (ContinuousLinearMap.fst ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) -
        (seqOp fun n => (2 : ℝ) • (H n).pieceBil L (f n)).comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞))) -
      ((ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) - S.comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) -
        G.comp (ContinuousLinearMap.fst ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) -
        (seqOp fun n => (2 : ℝ) • (H n).pieceBil L (g n)).comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞))) =
      (seqOp (fun n => (2 : ℝ) • (H n).pieceBil L (g n)) -
        seqOp (fun n => (2 : ℝ) • (H n).pieceBil L (f n))).comp (ContinuousLinearMap.snd ℝ E (lp (fun _ : ℕ => Piece Y L) ∞)) := by
    rw [ContinuousLinearMap.sub_comp]
    abel
  rw [e]
  exact (norm_comp_snd_le _).trans (norm_seqBil_sub_le hS hP H CK L M hCK hL hL1 f g h)

end OpBounds.Internal

set_option maxHeartbeats 2000000 in
open OpBounds.Internal in
theorem opDiffBounds (hS : SeqOpSpec) (hP : PieceOperatorStatement) : OpDiffBounds := by
  constructor
  · intro F P k θ M E _ _ J f g hL hL1 h
    rw [r3Op_sub]
    refine (norm_comp_snd_le _).trans ?_
    exact norm_seqBil_sub_le (Y := Freq.X) hS hP (fun _ => F.toHeatBilinear) F.CK
      (MildFramework.stepLength P k) M (fun _ => rfl) hL hL1 f g h
  · intro hK T lam θ M hT hT1 hl hl1 E _ _ Jt f g hlam h
    have hck : ∀ n, (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1 n)).CK = hK.choose := fun _ => rfl
    have hL : 0 < 1 - lam := by linarith
    have hL1 : 1 - lam ≤ 1 := by linarith
    unfold torusOp
    exact norm_chain_sub_le hS hP _ hK.choose (1 - lam) M hck hL hL1 _ _ f g h


namespace OpBounds.Internal

section Conv

variable {Z Y : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem extendPiece_eq {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {L : ℝ} (hL : 0 ≤ L)
    (f : Piece W L) (σ : ℝ) : extendPiece f σ = f (projIcc 0 L hL σ) := by
  rw [extendPiece, dif_pos hL]
  rfl

def combKernel {m : ℕ} (Λ : Fin m → ℝ → Z →L[ℝ] Y) (τ : ℝ) : (Fin m → Z) →L[ℝ] Y :=
  ∑ l, (Λ l τ).comp (ContinuousLinearMap.proj l)

theorem combKernel_apply {m : ℕ} (Λ : Fin m → ℝ → Z →L[ℝ] Y) (τ : ℝ) (y : Fin m → Z) :
    combKernel Λ τ y = ∑ l, Λ l τ (y l) := by
  simp [combKernel]

theorem norm_combKernel_le {m : ℕ} (Λ : Fin m → ℝ → Z →L[ℝ] Y) (τ : ℝ) :
    ‖combKernel Λ τ‖ ≤ ∑ l, ‖Λ l τ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun l _ => norm_nonneg _)
    fun y => ?_
  rw [combKernel_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  exact ((Λ l τ).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm y l) (norm_nonneg _))

theorem sum_pieceConv_apply (hV : PieceConvSpec) {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1) {m : ℕ}
    (Λ : Fin m → ℝ → Z →L[ℝ] Y) (w : Fin m → C(Icc (0 : ℝ) L, ℝ)) (C : Fin m → ℝ)
    (hC : ∀ l, 0 ≤ C l) (hb : ∀ l τ, 0 < τ → τ ≤ 1 → ‖Λ l τ‖ ≤ C l * τ ^ (-(3 / 4 : ℝ)))
    (hc : ∀ l ζ, ContinuousOn (fun τ => Λ l τ ζ) (Ioi 0)) (ζ : Piece Z L) (s : Icc (0 : ℝ) L) :
    (∑ l, pieceConv L (Λ l) (w l)) ζ s =
      ∫ σ in (0 : ℝ)..s, ∑ l, extendPiece (w l) σ • Λ l (s - σ) (extendPiece ζ σ) := by
  classical
  have hb' : ∀ τ, 0 < τ → τ ≤ 1 → ‖combKernel Λ τ‖ ≤ (∑ l, C l) * τ ^ (-(3 / 4 : ℝ)) := by
    intro τ h0 h1
    rw [Finset.sum_mul]
    exact (norm_combKernel_le Λ τ).trans (Finset.sum_le_sum fun l _ => hb l τ h0 h1)
  have hc' : ∀ y, ContinuousOn (fun τ => combKernel Λ τ y) (Ioi 0) := by
    intro y
    simp only [combKernel_apply]
    exact continuousOn_finsetSum _ fun l _ => hc l (y l)
  have hPc := (hV (Fin m → Z) Y L (combKernel Λ) 1 (∑ l, C l) hL hL1
    (Finset.sum_nonneg fun l _ => hC l) hb' hc').1
  let ι : Fin m → Piece (Fin m → Z) L := fun l =>
    ⟨fun t => Pi.single l (w l t • ζ t), (continuous_single l).comp ((w l).continuous.smul ζ.continuous)⟩
  have hι : ∀ l, pieceConv L (Λ l) (w l) ζ s = pieceConv L (combKernel Λ) 1 (ι l) s := by
    intro l
    rw [(hV Z Y L (Λ l) (w l) (C l) hL hL1 (hC l) (hb l) (hc l)).1, hPc]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [extendPiece_eq hL.le, combKernel_apply, ι, ContinuousMap.coe_mk,
      ContinuousMap.one_apply, one_smul]
    rw [Finset.sum_eq_single l]
    · rw [Pi.single_eq_same, map_smul]
    · intro l' _ hl'
      rw [Pi.single_eq_of_ne hl', map_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h
  rw [_root_.sum_apply, ContinuousMap.sum_apply]
  simp_rw [hι]
  rw [← ContinuousMap.sum_apply, ← map_sum, hPc]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only [extendPiece_eq hL.le, combKernel_apply, ι, ContinuousMap.one_apply, one_smul,
    ContinuousMap.sum_apply, ContinuousMap.coe_mk, Finset.sum_apply, Pi.single_apply,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, map_smul]

theorem norm_sum_pieceConv_le (hV : PieceConvSpec) {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1) {m : ℕ}
    (Λ : Fin m → ℝ → Z →L[ℝ] Y) (w : Fin m → C(Icc (0 : ℝ) L, ℝ)) (C : Fin m → ℝ)
    (hC : ∀ l, 0 ≤ C l) (hb : ∀ l τ, 0 < τ → τ ≤ 1 → ‖Λ l τ‖ ≤ C l * τ ^ (-(3 / 4 : ℝ)))
    (hc : ∀ l ζ, ContinuousOn (fun τ => Λ l τ ζ) (Ioi 0)) (B : ℝ) (hB : 0 ≤ B)
    (hcomb : ∀ (σ : Icc (0 : ℝ) L) (τ : ℝ), 0 < τ → τ ≤ 1 → ∀ z,
      ‖∑ l, w l σ • Λ l τ z‖ ≤ B * τ ^ (-(3 / 4 : ℝ)) * ‖z‖) :
    ‖∑ l, pieceConv L (Λ l) (w l)‖ ≤ 4 * B := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ζ => ?_
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun s => ?_
  rw [sum_pieceConv_apply hV hL hL1 Λ w C hC hb hc ζ s]
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2.trans hL1
  have hint : IntervalIntegrable (fun σ => B * ‖ζ‖ * ((s : ℝ) - σ) ^ (-(3 / 4 : ℝ))) volume 0 s := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := (s : ℝ)) (b := 0)
      (r := -(3 / 4 : ℝ)) (by norm_num)).comp_sub_left (s : ℝ)
    simp only [sub_self, sub_zero] at this
    exact this.const_mul _
  have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ (s : ℝ) := by
    simp [ae_iff, measure_singleton]
  have hae : ∀ᵐ σ ∂volume, σ ∈ Ioc (0 : ℝ) s →
      ‖∑ l, extendPiece (w l) σ • Λ l (s - σ) (extendPiece ζ σ)‖ ≤
        B * ‖ζ‖ * ((s : ℝ) - σ) ^ (-(3 / 4 : ℝ)) := by
    filter_upwards [hne] with σ hσ hmem
    have hlt : σ < s := lt_of_le_of_ne hmem.2 hσ
    have hσL : σ ∈ Icc (0 : ℝ) L := ⟨hmem.1.le, hmem.2.trans s.2.2⟩
    simp only [extendPiece_eq hL.le, projIcc_of_mem hL.le hσL]
    have h1 := hcomb ⟨σ, hσL⟩ (s - σ) (by linarith) (by linarith [hmem.1]) (ζ ⟨σ, hσL⟩)
    have h2 : 0 ≤ B * ((s : ℝ) - σ) ^ (-(3 / 4 : ℝ)) :=
      mul_nonneg hB (Real.rpow_nonneg (by linarith) _)
    calc _ ≤ B * ((s : ℝ) - σ) ^ (-(3 / 4 : ℝ)) * ‖ζ ⟨σ, hσL⟩‖ := h1
      _ ≤ B * ((s : ℝ) - σ) ^ (-(3 / 4 : ℝ)) * ‖ζ‖ :=
          mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm ζ _) h2
      _ = _ := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le hs0 hae hint).trans ?_
  have hsub := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (s : ℝ)
    (a := 0) (b := s)
  simp only [sub_self, sub_zero] at hsub
  rw [intervalIntegral.integral_const_mul, hsub, integral_rpow (Or.inl (by norm_num)),
    show (-(3 / 4 : ℝ) + 1) = 1 / 4 by norm_num, Real.zero_rpow (by norm_num)]
  have : (s : ℝ) ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hs0 hs1 (by norm_num)
  have h3 : 0 ≤ B * ‖ζ‖ := mul_nonneg hB (norm_nonneg ζ)
  calc B * ‖ζ‖ * (((s : ℝ) ^ (1 / 4 : ℝ) - 0) / (1 / 4)) = 4 * (B * ‖ζ‖) * (s : ℝ) ^ (1 / 4 : ℝ) := by
        ring
    _ ≤ 4 * (B * ‖ζ‖) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 4 * B * ‖ζ‖ := by ring

end Conv

section Fields

theorem isTestField_zero : IsTestField (0 : Space → Space) := by
  refine ⟨contDiff_const, HasCompactSupport.zero, fun y => ?_⟩
  simp [divergenceAt]

theorem isTestField_add {f g : Space → Space} (hf : IsTestField f) (hg : IsTestField g) :
    IsTestField (f + g) := by
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, fun y => ?_⟩
  have hfy := hf.2.2 y
  have hgy := hg.2.2 y
  unfold divergenceAt at hfy hgy ⊢
  have e : fderiv ℝ (f + g) y = fderiv ℝ f y + fderiv ℝ g y :=
    fderiv_add (hf.1.differentiable (by simp) y) (hg.1.differentiable (by simp) y)
  rw [e]
  simp only [_root_.add_apply, PiLp.add_apply, Finset.sum_add_distrib, hfy, hgy,
    add_zero]

theorem isTestField_smul (c : ℝ) {f : Space → Space} (hf : IsTestField f) :
    IsTestField (c • f) := by
  refine ⟨hf.1.const_smul c, hf.2.1.smul_left (f := fun _ => c), fun y => ?_⟩
  have hfy := hf.2.2 y
  unfold divergenceAt at hfy ⊢
  have e : fderiv ℝ (c • f) y = c • fderiv ℝ f y :=
    fderiv_const_smul (hf.1.differentiable (by simp) y) c
  rw [e]
  simp only [_root_.smul_apply, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hfy,
    mul_zero]

theorem isTestField_sum {m : ℕ} (c : Fin m → ℝ) (φ : Fin m → Space → Space)
    (h : ∀ l, IsTestField (φ l)) (s : Finset (Fin m)) : IsTestField (∑ l ∈ s, c l • φ l) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using isTestField_zero
  · intro l s hl ih
    rw [Finset.sum_insert hl]
    exact isTestField_add (isTestField_smul _ (h l)) ih

theorem isDecayField_of_test {φ : Space → Space} (h : IsTestField φ) : IsDecayField φ := by
  refine ⟨h.1, h.2.2, ?_⟩
  have h0 : Continuous φ := h.1.continuous
  have h1 : Continuous (fderiv ℝ φ) := h.1.continuous_fderiv (by simp)
  have hc : Continuous fun y => (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖) := by fun_prop
  have hk : HasCompactSupport fun y => (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖) :=
    (h.2.1.norm.add (h.2.1.fderiv ℝ).norm).mul_left
  obtain ⟨K, hK⟩ := hc.bounded_above_of_compact_support hk
  refine ⟨K, fun y => ?_⟩
  have hy : (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖) ≤ K := (Real.le_norm_self _).trans (hK y)
  have a := norm_nonneg (φ y)
  have b := norm_nonneg (fderiv ℝ φ y)
  have r := norm_nonneg y
  have hp : 0 < 1 + ‖y‖ := by positivity
  constructor
  · rw [le_div_iff₀ hp]
    nlinarith [mul_nonneg a r, mul_nonneg (mul_nonneg a r) r, mul_nonneg b (sq_nonneg (1 + ‖y‖))]
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg a (sq_nonneg (1 + ‖y‖))]

theorem embedX_sum (hE : Freq.EmbedLinear) {m : ℕ} (c : Fin m → ℝ) (φ : Fin m → Space → Space)
    (h : ∀ l, IsTestField (φ l)) (s : Finset (Fin m)) :
    Freq.embedX (∑ l ∈ s, c l • φ l) = ∑ l ∈ s, c l • Freq.embedX (φ l) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have e := hE.2.1 0 0 (isDecayField_of_test isTestField_zero)
      (isDecayField_of_test isTestField_zero)
    simpa using e
  · intro l s hl ih
    rw [Finset.sum_insert hl, Finset.sum_insert hl,
      hE.1 _ _ (isDecayField_of_test (isTestField_smul _ (h l)))
        (isDecayField_of_test (isTestField_sum c φ h s)),
      hE.2.2 _ _ (isDecayField_of_test (h l)), ih]

def advInt (φ : Space → Space) (b : ℝ) (ζ : ShellData) : Space → Space :=
  (Metric.closedBall (0 : Space) b).indicator
    (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y +
      (ζ.2 : Space → Space) y j • Freq.partialField φ j y))

theorem advectShell_eq (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData) :
    advectShell φ hφ b ζ = Freq.toLpOrZero 2 (advInt φ b ζ) := rfl

theorem memLp_advInt {φ : Space → Space} (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData) :
    MemLp (advInt φ b ζ) 2 volume := by
  unfold advInt
  rw [memLp_indicator_iff_restrict measurableSet_closedBall]
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) b)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hc : Continuous φ := hφ.1.continuous
  have hd : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by simp)
  refine memLp_finsetSum _ fun j _ => MemLp.add ?_ ?_
  · have h1 : MemLp (fun y => φ y j) ⊤ volume :=
      Continuous.memLp_top_of_hasCompactSupport (by fun_prop)
        (hφ.2.1.comp_left (g := fun v : Space => v j) (by simp)) volume
    exact ((Lp.memLp (ζ.1 j)).smul h1).restrict _
  · have h6 : MemLp (fun y => (ζ.2 : Space → Space) y j) 6 volume :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' (Lp.memLp ζ.2)
    have hp : MemLp (Freq.partialField φ j) ⊤ volume :=
      Continuous.memLp_top_of_hasCompactSupport (hd.clm_apply continuous_const)
        ((hφ.2.1.fderiv ℝ).comp_left (g := fun T : Space →L[ℝ] Space => T (unitVector j)) (by simp))
        volume
    exact ((MemLp.smul (r := 6) hp h6).restrict _).mono_exponent (by norm_num)

theorem advInt_add {f g : Space → Space} (hf : IsTestField f) (hg : IsTestField g) (b : ℝ)
    (ζ : ShellData) : advInt (f + g) b ζ = advInt f b ζ + advInt g b ζ := by
  funext y
  have e : ∀ j, Freq.partialField (f + g) j y = Freq.partialField f j y + Freq.partialField g j y := by
    intro j
    have d : fderiv ℝ (f + g) y = fderiv ℝ f y + fderiv ℝ g y :=
      fderiv_add (hf.1.differentiable (by simp) y) (hg.1.differentiable (by simp) y)
    simp only [Freq.partialField, d, _root_.add_apply]
  simp only [advInt, Pi.add_apply]
  by_cases hy : y ∈ Metric.closedBall (0 : Space) b
  · simp only [indicator_of_mem hy, e, PiLp.add_apply, add_smul, smul_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    abel
  · simp only [indicator_of_notMem hy, add_zero]

theorem advInt_smul (c : ℝ) {f : Space → Space} (hf : IsTestField f) (b : ℝ) (ζ : ShellData) :
    advInt (c • f) b ζ = c • advInt f b ζ := by
  funext y
  have e : ∀ j, Freq.partialField (c • f) j y = c • Freq.partialField f j y := by
    intro j
    have d : fderiv ℝ (c • f) y = c • fderiv ℝ f y :=
      fderiv_const_smul (hf.1.differentiable (by simp) y) c
    simp only [Freq.partialField, d, _root_.smul_apply]
  simp only [advInt, Pi.smul_apply]
  by_cases hy : y ∈ Metric.closedBall (0 : Space) b
  · simp only [indicator_of_mem hy, e, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_add, PiLp.smul_apply, smul_eq_mul, mul_smul, smul_comm ((ζ.2 : Space → Space) y j) c]
  · simp only [indicator_of_notMem hy, smul_zero]

theorem toLpOrZero_add {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Freq.toLpOrZero 2 (f + g) = Freq.toLpOrZero 2 f + Freq.toLpOrZero 2 g := by
  unfold Freq.toLpOrZero
  rw [dif_pos (hf.add hg), dif_pos hf, dif_pos hg]
  exact MemLp.toLp_add hf hg

theorem toLpOrZero_smul (c : ℝ) {f : Space → Space} (hf : MemLp f 2 volume) :
    Freq.toLpOrZero 2 (c • f) = c • Freq.toLpOrZero 2 f := by
  unfold Freq.toLpOrZero
  rw [dif_pos (hf.const_smul c), dif_pos hf]
  exact MemLp.toLp_const_smul c hf

theorem advectShell_sum {m : ℕ} (c : Fin m → ℝ) (φ : Fin m → Space → Space)
    (h : ∀ l, IsTestField (φ l)) (b : ℝ) (ζ : ShellData) (s : Finset (Fin m)) :
    advectShell (∑ l ∈ s, c l • φ l) (isTestField_sum c φ h s) b ζ =
      ∑ l ∈ s, c l • advectShell (φ l) (h l) b ζ := by
  classical
  rw [advectShell_eq]
  simp only [advectShell_eq]
  refine Finset.induction_on s ?_ ?_
  · have e0 := advInt_smul 0 isTestField_zero b ζ
    rw [zero_smul, zero_smul] at e0
    have e1 := toLpOrZero_smul 0 (MemLp.zero : MemLp (0 : Space → Space) 2 volume)
    rw [zero_smul, zero_smul] at e1
    simp only [Finset.sum_empty, e0, e1]
  · intro l s hl ih
    rw [Finset.sum_insert hl, Finset.sum_insert hl,
      advInt_add (isTestField_smul _ (h l)) (isTestField_sum c φ h s), advInt_smul _ (h l),
      toLpOrZero_add ((memLp_advInt (h l) b ζ).const_smul _) (memLp_advInt (isTestField_sum c φ h s) b ζ),
      toLpOrZero_smul _ (memLp_advInt (h l) b ζ), ih]

theorem lambdaR3_sum {m : ℕ} (c : Fin m → ℝ) (φ : Fin m → Space → Space)
    (h : ∀ l, IsTestField (φ l)) (b τ : ℝ) (ζ : ShellData) :
    ∑ l, c l • lambdaR3 (φ l) (h l) b τ ζ =
      lambdaR3 (∑ l, c l • φ l) (isTestField_sum c φ h Finset.univ) b τ ζ := by
  simp only [lambdaR3, _root_.neg_apply, ContinuousLinearMap.comp_apply]
  rw [advectShell_sum c φ h b ζ Finset.univ]
  simp only [map_sum, map_smul, smul_neg, Finset.sum_neg_distrib]

theorem lambdaTorus_sum {m : ℕ} (c : Fin m → ℝ) (φ : Fin m → Space → Space)
    (h : ∀ l, IsTestField (φ l)) (b μ τ : ℝ) (ζ : ShellData) :
    ∑ l, c l • lambdaTorus (φ l) (h l) b μ τ ζ =
      lambdaTorus (∑ l, c l • φ l) (isTestField_sum c φ h Finset.univ) b μ τ ζ := by
  simp only [lambdaTorus, _root_.neg_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [advectShell_sum c φ h b ζ Finset.univ]
  simp only [map_sum, map_smul, smul_neg, Finset.sum_neg_distrib, Finset.smul_sum]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun l _ => ?_)
  rw [smul_comm]

end Fields

end OpBounds.Internal


namespace OpBounds.Internal

theorem norm_dil_le (F : MildFramework Freq.X) {μ : ℝ} (hμ : 0 < μ) : ‖F.D μ‖ ≤ μ ^ (1 / 4 : ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg hμ.le _) fun u => (F.D_norm μ hμ u).le

set_option maxHeartbeats 2000000 in
theorem norm_r3Shift_entry (F : MildFramework Freq.X) (P : ℝ) (k : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ‖θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)‖ ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ := by
  have h1 : ‖F.stepFree P k‖ ≤ 1 := norm_pieceFree_le F.toHeatBilinear _
  have h2 : ‖F.stepEnd P k‖ ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) := by
    show ‖(F.D (Real.exp (-(P / k)))).comp (pieceEnd (MildFramework.stepLength P k))‖ ≤ _
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) * 1 :=
          mul_le_mul (norm_dil_le F (Real.exp_pos _)) (norm_pieceEnd_le _) (norm_nonneg _)
            (Real.rpow_nonneg (Real.exp_pos _).le _)
      _ = _ := mul_one _
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hθ.le, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hθ.le)
  calc _ ≤ ‖F.stepFree P k‖ * ‖F.stepEnd P k‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * Real.exp (-(P / k)) ^ (1 / 4 : ℝ) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem norm_torusShift_entry (H : HeatBilinear V) (L c : ℝ) (hc : 0 ≤ c) :
    ‖c • (H.pieceFree L).comp (pieceEnd L)‖ ≤ c := by
  rw [norm_smul, Real.norm_of_nonneg hc]
  calc c * ‖(H.pieceFree L).comp (pieceEnd L)‖ ≤ c * (‖H.pieceFree L‖ * ‖(pieceEnd L : Piece V L →L[ℝ] V)‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hc
    _ ≤ c * (1 * 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul (norm_pieceFree_le H L) (norm_pieceEnd_le L) (norm_nonneg _) zero_le_one) hc
    _ = c := by ring

theorem isShellScale_step {T lam b : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (hb : 0 < b) (hsb : Real.sqrt T * b ≤ 1 / 8) (n : ℕ) : IsShellScale (stepScale T lam n) b := by
  refine ⟨stepScale_pos hT hl n, stepScale_le_one hT1 hl hl1 n, hb, ?_⟩
  show Real.sqrt (T * lam ^ n) * b ≤ 1 / 8
  have h : T * lam ^ n ≤ T := mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1)
  exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) hb.le).trans hsb

end OpBounds.Internal

set_option maxHeartbeats 4000000 in
open OpBounds.Internal in
theorem operatorNormBounds (hS : SeqOpSpec) (hC : PieceCompSpec) (hV : PieceConvSpec)
    (hRL : R3LambdaBound) (hTL : TorusLambdaBound) (hRR : RestrictR3Bound) (hE : Freq.EmbedLinear)
    (hH : ∀ x : Freq.L2R, ContinuousOn (fun τ => Freq.heatDivFree τ x) (Ioi 0))
    (hF : ∀ (μ : ℝ) (x : Freq.L2R), 0 < μ → ContinuousOn (fun τ => sourceOp μ τ x) (Ioi 0)) :
    OperatorNormBounds := by
  obtain ⟨C1, hC1, hb1⟩ := hRL
  obtain ⟨C2, hC2, hb2⟩ := hTL
  obtain ⟨C3, hC3, hb3⟩ := hRR
  have hC4 := restrictTorusFun_bound.choose_spec.1
  set C4 := restrictTorusFun_bound.choose
  have hK : 0 ≤ max (max (4 * C1) (4 * C2)) (max C3 C4) :=
    le_max_of_le_right (le_max_of_le_left hC3)
  refine ⟨max (max (4 * C1) (4 * C2)) (max C3 C4), hK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L b M A hL hL1 hM
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hn : ∀ n, ‖∑ l, pieceConv L (fun τ => lambdaR3 (A.field n l) (A.isTest n l) b τ)
        (A.weight n l)‖ ≤ 4 * (C1 * M) := by
      intro n
      refine norm_sum_pieceConv_le hV hL hL1 (fun l τ => lambdaR3 (A.field n l) (A.isTest n l) b τ)
        (A.weight n) (fun l => C1 * ‖Freq.embedX (A.field n l)‖)
        (fun l => mul_nonneg hC1 (norm_nonneg _)) ?_ ?_ (C1 * M) (mul_nonneg hC1 hM0) ?_
      · intro l τ h0 h1
        refine ContinuousLinearMap.opNorm_le_bound _
          (mul_nonneg (mul_nonneg hC1 (norm_nonneg _)) (Real.rpow_nonneg h0.le _)) fun z => ?_
        exact (hb1 _ _ b τ h0 z).trans (le_of_eq (by ring))
      · intro l z
        simp only [lambdaR3, _root_.neg_apply, ContinuousLinearMap.comp_apply]
        exact (hH _).neg
      · intro σ τ h0 h1 z
        show ‖∑ l, A.weight n l σ • lambdaR3 (A.field n l) (A.isTest n l) b τ z‖ ≤ _
        rw [lambdaR3_sum (fun l => A.weight n l σ) (A.field n) (A.isTest n) b τ z]
        refine (hb1 _ _ b τ h0 z).trans ?_
        rw [embedX_sum hE (fun l => A.weight n l σ) (A.field n) (A.isTest n) Finset.univ]
        have hr : ‖∑ l, A.weight n l σ • Freq.embedX (A.field n l)‖ ≤ M :=
          (ContinuousMap.norm_coe_le_norm (A.r3Piece n) σ).trans (hM n)
        have hp : 0 ≤ C1 * τ ^ (-(3 / 4 : ℝ)) := mul_nonneg hC1 (Real.rpow_nonneg h0.le _)
        calc C1 * τ ^ (-(3 / 4 : ℝ)) * ‖∑ l, A.weight n l σ • Freq.embedX (A.field n l)‖ * ‖z‖ ≤
            C1 * τ ^ (-(3 / 4 : ℝ)) * M * ‖z‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hp) (norm_nonneg _)
          _ = C1 * M * τ ^ (-(3 / 4 : ℝ)) * ‖z‖ := by ring
    show ‖seqOp _‖ ≤ _
    refine ((hS _ _ _ (4 * (C1 * M)) hn (by positivity)).2.1).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) hM0
  · intro b T lam M A hT hT1 hl hl1 hb hsb hM
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hL : 0 < 1 - lam := by linarith
    have hL1 : 1 - lam ≤ 1 := by linarith
    have hμ := isShellScale_step hT hT1 hl hl1.le hb hsb
    have hμτ : ∀ n τ, 0 < τ → τ ≤ 1 → stepScale T lam n * τ ≤ 1 := fun n τ h0 h1 =>
      mul_le_one₀ (stepScale_le_one hT1 hl hl1.le n) h0.le h1
    have hn : ∀ n, ‖∑ l, pieceConv (1 - lam)
        (fun τ => lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
        (A.weight n l)‖ ≤ 4 * (C2 * M) := by
      intro n
      refine norm_sum_pieceConv_le hV hL hL1
        (fun l τ => lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
        (A.weight n) (fun l => C2 * ‖Freq.embedX (A.field n l)‖)
        (fun l => mul_nonneg hC2 (norm_nonneg _)) ?_ ?_ (C2 * M) (mul_nonneg hC2 hM0) ?_
      · intro l τ h0 h1
        refine ContinuousLinearMap.opNorm_le_bound _
          (mul_nonneg (mul_nonneg hC2 (norm_nonneg _)) (Real.rpow_nonneg h0.le _)) fun z => ?_
        exact (hb2 _ _ b _ τ (hμ n) h0 (hμτ n τ h0 h1) z).trans (le_of_eq (by ring))
      · intro l z
        simp only [lambdaTorus, _root_.neg_apply, _root_.smul_apply,
          ContinuousLinearMap.comp_apply]
        exact ((hF _ _ (stepScale_pos hT hl n)).const_smul
          ((stepScale T lam n) ^ (-(1 / 4 : ℝ)))).neg
      · intro σ τ h0 h1 z
        show ‖∑ l, A.weight n l σ • lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ z‖ ≤ _
        rw [lambdaTorus_sum (fun l => A.weight n l σ) (A.field n) (A.isTest n) b _ τ z]
        refine (hb2 _ _ b _ τ (hμ n) h0 (hμτ n τ h0 h1) z).trans ?_
        rw [embedX_sum hE (fun l => A.weight n l σ) (A.field n) (A.isTest n) Finset.univ]
        have hr : ‖∑ l, A.weight n l σ • Freq.embedX (A.field n l)‖ ≤ M :=
          (ContinuousMap.norm_coe_le_norm (A.r3Piece n) σ).trans (hM n)
        have hp : 0 ≤ C2 * τ ^ (-(3 / 4 : ℝ)) := mul_nonneg hC2 (Real.rpow_nonneg h0.le _)
        calc C2 * τ ^ (-(3 / 4 : ℝ)) * ‖∑ l, A.weight n l σ • Freq.embedX (A.field n l)‖ * ‖z‖ ≤
            C2 * τ ^ (-(3 / 4 : ℝ)) * M * ‖z‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hp) (norm_nonneg _)
          _ = C2 * M * τ ^ (-(3 / 4 : ℝ)) * ‖z‖ := by ring
    show ‖seqOp _‖ ≤ _
    refine ((hS _ _ _ (4 * (C2 * M)) hn (by positivity)).2.1).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) hM0
  · intro L b hL
    show ‖seqOp _‖ ≤ _
    refine ((hS _ _ _ C3 (fun _ => (hC _ _ L _ hL.le).2.trans (hb3 b)) hC3).2.1).trans ?_
    exact le_max_of_le_right (le_max_left _ _)
  · intro b T lam hT hT1 hl hl1 hb hsb
    have hR : ∀ n, ‖restrictTorus (stepScale T lam n) b‖ ≤ C4 := fun n =>
      LinearMap.mkContinuous_norm_le _ hC4 _
    show ‖seqOp _‖ ≤ _
    refine ((hS _ _ _ C4 (fun n => (hC _ _ (1 - lam) _ (by linarith)).2.trans (hR n)) hC4).2.1).trans ?_
    exact le_max_of_le_right (le_max_right _ _)
  · intro F P k θ hP hk hθ
    have h0 : 0 ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ :=
      div_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _) hθ.le
    unfold r3Shift
    exact ((hS _ _ (fun _ => (0 : Piece Freq.X (MildFramework.stepLength P k) →L[ℝ]
      Piece Freq.X (MildFramework.stepLength P k))) _ (fun _ => by rw [norm_zero]; exact h0) h0).2.2.1 _
      (fun _ => norm_r3Shift_entry F P k hθ)).2
  · intro hK T lam θ hT hT1 hl hl1 hθ
    have h0 : 0 ≤ lam ^ (1 / 4 : ℝ) / θ := div_nonneg (Real.rpow_nonneg hl.le _) hθ.le
    unfold torusShift
    exact ((hS _ _ (fun _ => (0 : Piece V (1 - lam) →L[ℝ] Piece V (1 - lam))) _
      (fun _ => by rw [norm_zero]; exact h0) h0).2.2.1 _
      (fun n => norm_torusShift_entry _ (1 - lam) _ h0)).2

end Breakdown.Periodic
