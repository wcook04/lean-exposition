import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace PieceOperatorInternal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem extendPiece_add {T : ℝ} (f g : Piece X T) (s : ℝ) :
    extendPiece (f + g) s = extendPiece f s + extendPiece g s := by
  unfold extendPiece
  split_ifs with h
  · rfl
  · simp

theorem extendPiece_smul {T : ℝ} (c : ℝ) (f : Piece X T) (s : ℝ) :
    extendPiece (c • f) s = c • extendPiece f s := by
  unfold extendPiece
  split_ifs with h
  · rfl
  · simp

theorem extendPiece_continuous {T : ℝ} (f : Piece X T) : Continuous (extendPiece f) := by
  unfold extendPiece
  split_ifs with h
  · exact f.continuous.comp continuous_projIcc
  · exact continuous_const

theorem norm_extendPiece_le {T : ℝ} (f : Piece X T) (s : ℝ) : ‖extendPiece f s‖ ≤ ‖f‖ := by
  unfold extendPiece
  split_ifs with h
  · exact ContinuousMap.norm_coe_le_norm f _
  · simp

theorem CK_nonneg (H : HeatBilinear X) : 0 ≤ H.CK := by
  have h := H.K_bound 1 one_pos le_rfl
  rw [Real.one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

theorem norm_K_far (H : HeatBilinear X) (τ : ℝ) (hτ : 1 ≤ τ) (u v : X) :
    ‖H.K τ u v‖ ≤ H.CK * ‖u‖ * ‖v‖ := by
  have hs := H.K_shift (τ - 1) 1 (by linarith) one_pos u v
  rw [sub_add_cancel] at hs
  rw [← hs]
  have h1 := H.K_bound 1 one_pos le_rfl
  rw [Real.one_rpow, mul_one] at h1
  calc ‖H.G (τ - 1) (H.K 1 u v)‖ ≤ 1 * ‖H.K 1 u v‖ :=
        (H.G (τ - 1)).le_of_opNorm_le (H.G_norm _ (by linarith)) _
    _ ≤ 1 * (‖H.K 1‖ * ‖u‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((H.K 1).le_opNorm₂ u v) zero_le_one
    _ ≤ H.CK * ‖u‖ * ‖v‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
          (norm_nonneg _)

theorem varConst_piece (h1 : VarConstIntegralStatement) (H : HeatBilinear X) {T : ℝ} (f g : Piece X T)
    (a b : ℝ) (hab : a ≤ b) :
    (∀ t ∈ Icc a b, IntervalIntegrable
      (fun s => H.K (t - s) (extendPiece f s) (extendPiece g s)) volume a t) ∧
    (∀ t ∈ Icc a b, t - a ≤ 1 →
      ‖∫ s in a..t, H.K (t - s) (extendPiece f s) (extendPiece g s)‖ ≤
        4 * H.CK * (t - a) ^ (1 / 4 : ℝ) * ‖f‖ * ‖g‖) ∧
    ContinuousOn (fun t => ∫ s in a..t, H.K (t - s) (extendPiece f s) (extendPiece g s))
      (Icc a b) :=
  h1 X H (extendPiece f) (extendPiece g) a b ‖f‖ ‖g‖ hab
    (extendPiece_continuous f).continuousOn (extendPiece_continuous g).continuousOn
    (fun s _ => norm_extendPiece_le f s) (fun s _ => norm_extendPiece_le g s)

theorem norm_integral_le (h1 : VarConstIntegralStatement) (H : HeatBilinear X) {T : ℝ}
    (hT : 0 ≤ T) (f g : Piece X T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖∫ s in (0 : ℝ)..t, H.K (t - s) (extendPiece f s) (extendPiece g s)‖ ≤
      (4 + T) * H.CK * ‖f‖ * ‖g‖ := by
  have hc := CK_nonneg H
  have hCfg : 0 ≤ H.CK * ‖f‖ * ‖g‖ :=
    mul_nonneg (mul_nonneg hc (norm_nonneg _)) (norm_nonneg _)
  have hD := varConst_piece h1 H f g 0 T hT
  rcases le_or_gt t 1 with h | h
  · have hb := hD.2.1 t ht (by simpa using h)
    rw [sub_zero] at hb
    have hr : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.1 h (by norm_num)
    have e1 : 4 * H.CK * t ^ (1 / 4 : ℝ) * ‖f‖ * ‖g‖ =
        (4 * t ^ (1 / 4 : ℝ)) * (H.CK * ‖f‖ * ‖g‖) := by ring
    have e2 : (4 + T) * H.CK * ‖f‖ * ‖g‖ = (4 + T) * (H.CK * ‖f‖ * ‖g‖) := by ring
    rw [e2]
    rw [e1] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hCfg)
  · have ht0 : 0 ≤ t := ht.1
    have hint := hD.1 t ht
    have hint1 : IntervalIntegrable
        (fun s => H.K (t - s) (extendPiece f s) (extendPiece g s)) volume 0 (t - 1) :=
      hint.mono_set (uIcc_subset_uIcc left_mem_uIcc
        (by rw [uIcc_of_le ht0]; constructor <;> linarith))
    have hD2 := varConst_piece h1 H f g (t - 1) t (by linarith)
    have htm : t ∈ Icc (t - 1) t := ⟨by linarith, le_rfl⟩
    have hint2 := hD2.1 t htm
    have hb2 := hD2.2.1 t htm (by linarith)
    rw [show t - (t - 1) = 1 by ring, Real.one_rpow, mul_one] at hb2
    have hb1 : ‖∫ s in (0 : ℝ)..(t - 1), H.K (t - s) (extendPiece f s) (extendPiece g s)‖ ≤
        H.CK * ‖f‖ * ‖g‖ * |t - 1 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le (by linarith)] at hs
      calc _ ≤ H.CK * ‖extendPiece f s‖ * ‖extendPiece g s‖ :=
            norm_K_far H _ (by linarith [hs.2]) _ _
        _ ≤ H.CK * ‖f‖ * ‖g‖ :=
            mul_le_mul (mul_le_mul_of_nonneg_left (norm_extendPiece_le f s) hc)
              (norm_extendPiece_le g s) (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))
    rw [sub_zero, abs_of_nonneg (by linarith)] at hb1
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    calc _ ≤ ‖∫ s in (0 : ℝ)..(t - 1), H.K (t - s) (extendPiece f s) (extendPiece g s)‖ +
          ‖∫ s in (t - 1)..t, H.K (t - s) (extendPiece f s) (extendPiece g s)‖ := norm_add_le _ _
      _ ≤ H.CK * ‖f‖ * ‖g‖ * (t - 1) + 4 * H.CK * ‖f‖ * ‖g‖ := add_le_add hb1 hb2
      _ ≤ (4 + T) * H.CK * ‖f‖ * ‖g‖ := by
          nlinarith [mul_nonneg hCfg (sub_nonneg.2 ht.2)]

def integralPiece (h1 : VarConstIntegralStatement) (H : HeatBilinear X) {T : ℝ} (hT : 0 ≤ T)
    (f g : Piece X T) : Piece X T :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), H.K (t - s) (extendPiece f s) (extendPiece g s),
    (varConst_piece h1 H f g 0 T hT).2.2.domRestrict⟩

theorem integrable_piece (h1 : VarConstIntegralStatement) (H : HeatBilinear X) {T : ℝ}
    (hT : 0 ≤ T) (f g : Piece X T) (t : Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => H.K (t - s) (extendPiece f s) (extendPiece g s)) volume 0 t :=
  (varConst_piece h1 H f g 0 T hT).1 t t.2

theorem integralPiece_add_left (h1 : VarConstIntegralStatement) (H : HeatBilinear X) {T : ℝ}
    (hT : 0 ≤ T) (f f' g : Piece X T) :
    integralPiece h1 H hT (f + f') g = integralPiece h1 H hT f g + integralPiece h1 H hT f' g := by
  ext t
  simp only [integralPiece, ContinuousMap.coe_mk, ContinuousMap.add_apply, extendPiece_add,
    map_add, add_apply]
  exact intervalIntegral.integral_add (integrable_piece h1 H hT f g t)
    (integrable_piece h1 H hT f' g t)

theorem integralPiece_add_right (h1 : VarConstIntegralStatement) (H : HeatBilinear X) {T : ℝ}
    (hT : 0 ≤ T) (f g g' : Piece X T) :
    integralPiece h1 H hT f (g + g') = integralPiece h1 H hT f g + integralPiece h1 H hT f g' := by
  ext t
  simp only [integralPiece, ContinuousMap.coe_mk, ContinuousMap.add_apply, extendPiece_add,
    map_add]
  exact intervalIntegral.integral_add (integrable_piece h1 H hT f g t)
    (integrable_piece h1 H hT f g' t)

theorem integralPiece_smul_left (h1 : VarConstIntegralStatement) (H : HeatBilinear X) {T : ℝ}
    (hT : 0 ≤ T) (c : ℝ) (f g : Piece X T) :
    integralPiece h1 H hT (c • f) g = c • integralPiece h1 H hT f g := by
  ext t
  simp only [integralPiece, ContinuousMap.coe_mk, ContinuousMap.smul_apply, extendPiece_smul,
    map_smul, smul_apply]
  exact intervalIntegral.integral_smul _ _

theorem integralPiece_smul_right (h1 : VarConstIntegralStatement) (H : HeatBilinear X) {T : ℝ}
    (hT : 0 ≤ T) (c : ℝ) (f g : Piece X T) :
    integralPiece h1 H hT f (c • g) = c • integralPiece h1 H hT f g := by
  ext t
  simp only [integralPiece, ContinuousMap.coe_mk, ContinuousMap.smul_apply, extendPiece_smul,
    map_smul]
  exact intervalIntegral.integral_smul _ _

def integralBil (h1 : VarConstIntegralStatement) (H : HeatBilinear X) {T : ℝ} (hT : 0 ≤ T) :
    Piece X T →L[ℝ] Piece X T →L[ℝ] Piece X T :=
  (LinearMap.mk₂ ℝ (integralPiece h1 H hT) (integralPiece_add_left h1 H hT)
    (integralPiece_smul_left h1 H hT) (integralPiece_add_right h1 H hT)
    (integralPiece_smul_right h1 H hT)).mkContinuous₂ ((4 + T) * H.CK) (fun f g => by
      show ‖integralPiece h1 H hT f g‖ ≤ _
      rw [ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (mul_nonneg (by linarith)
        (CK_nonneg H)) (norm_nonneg _)) (norm_nonneg _))]
      intro t
      exact norm_integral_le h1 H hT f g t t.2)

def freePiece (H : HeatBilinear X) (T : ℝ) (x : X) : Piece X T :=
  ⟨fun t => H.G t x, ((H.G_cont x).mono (fun _ ht => ht.1)).domRestrict⟩

def freeLin (H : HeatBilinear X) (T : ℝ) : X →ₗ[ℝ] Piece X T where
  toFun := freePiece H T
  map_add' x y := by
    ext t
    exact map_add (H.G t) x y
  map_smul' c x := by
    ext t
    exact map_smul (H.G t) c x

theorem norm_G_apply_le (H : HeatBilinear X) (t : ℝ) (ht : 0 ≤ t) (x : X) : ‖H.G t x‖ ≤ ‖x‖ := by
  have h := (H.G t).le_of_opNorm_le (H.G_norm t ht) x
  rwa [one_mul] at h

def freeCLM (H : HeatBilinear X) (T : ℝ) : X →L[ℝ] Piece X T :=
  (freeLin H T).mkContinuous 1 (fun x => by
    rw [one_mul]
    show ‖freePiece H T x‖ ≤ ‖x‖
    rw [ContinuousMap.norm_le _ (norm_nonneg x)]
    intro t
    exact norm_G_apply_le H t t.2.1 x)

end PieceOperatorInternal

theorem pieceOperator_of (h1 : VarConstIntegralStatement) : PieceOperatorStatement := by
  intro X _ _ _ H T hT
  have hT0 : 0 ≤ T := hT.le
  have hex : ∃ B : Piece X T →L[ℝ] Piece X T →L[ℝ] Piece X T, ∀ f g (t : Icc (0 : ℝ) T),
      B f g t = ∫ s in (0 : ℝ)..t, H.K (t - s) (extendPiece f s) (extendPiece g s) :=
    ⟨PieceOperatorInternal.integralBil h1 H hT0, fun _ _ _ => rfl⟩
  have hB : ∀ (f g : Piece X T) (t : Icc (0 : ℝ) T),
      H.pieceBil T f g t = ∫ s in (0 : ℝ)..t, H.K (t - s) (extendPiece f s) (extendPiece g s) := by
    intro f g t
    unfold HeatBilinear.pieceBil
    rw [dif_pos hex]
    exact hex.choose_spec f g t
  have hexF : ∃ L : X →L[ℝ] Piece X T, ∀ x (t : Icc (0 : ℝ) T), L x t = H.G t x :=
    ⟨PieceOperatorInternal.freeCLM H T, fun _ _ => rfl⟩
  have hF : ∀ (x : X) (t : Icc (0 : ℝ) T), H.pieceFree T x t = H.G t x := by
    intro x t
    unfold HeatBilinear.pieceFree
    rw [dif_pos hexF]
    exact hexF.choose_spec x t
  refine ⟨hB, fun hT1 => ?_, hF, ?_⟩
  · have hc := PieceOperatorInternal.CK_nonneg H
    have h4c : 0 ≤ 4 * H.CK := mul_nonneg (by norm_num) hc
    have h0 : 0 ≤ 4 * H.CK * T ^ (1 / 4 : ℝ) := mul_nonneg h4c (Real.rpow_nonneg hT0 _)
    refine ContinuousLinearMap.opNorm_le_bound₂ _ h0 (fun f g => ?_)
    rw [ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg h0 (norm_nonneg _)) (norm_nonneg _))]
    intro t
    rw [hB]
    have hb := (PieceOperatorInternal.varConst_piece h1 H f g 0 T hT0).2.1 t t.2
      (by simpa using t.2.2.trans hT1)
    rw [sub_zero] at hb
    have hr := Real.rpow_le_rpow t.2.1 t.2.2 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr h4c) (norm_nonneg f)) (norm_nonneg g))
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg x)]
    intro t
    rw [hF]
    exact PieceOperatorInternal.norm_G_apply_le H t t.2.1 x

end Breakdown
