import Breakdown.Torus.StatementsSteps
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace SeqPerturbation.Internal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem extend_eq {T : ℝ} (hT : 0 ≤ T) (f : Piece X T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    extendPiece f t = f ⟨t, ht⟩ := by
  unfold extendPiece
  rw [dif_pos hT, Set.IccExtend_of_mem hT f ht]

theorem extend_continuous {T : ℝ} (hT : 0 ≤ T) (f : Piece X T) : Continuous (extendPiece f) := by
  have h : extendPiece f = Set.IccExtend hT f := by
    funext t
    unfold extendPiece
    rw [dif_pos hT]
  rw [h]
  exact f.continuous.Icc_extend'

theorem extend_add_smul {T : ℝ} (hT : 0 ≤ T) (f g : Piece X T) (a s : ℝ) :
    extendPiece (f + a • g) s = extendPiece f s + a • extendPiece g s := by
  unfold extendPiece
  rw [dif_pos hT, dif_pos hT, dif_pos hT]
  simp only [Set.IccExtend_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply]

theorem mild_of_eq (hP : PieceOperatorStatement) (hD : VarConstIntegralStatement)
    (H : HeatBilinear X) {T : ℝ} (hT : 0 < T) (u : Piece X T) (x : X)
    (hu : u = H.pieceFree T x + H.pieceBil T u u) :
    extendPiece u 0 = x ∧ H.IsMildOnIcc (extendPiece u) 0 T := by
  obtain ⟨hB, -, hF, -⟩ := hP X H T hT
  have hT0 : 0 ≤ T := hT.le
  have hval : ∀ t (ht : t ∈ Icc (0 : ℝ) T), extendPiece u t = H.G t x +
      ∫ s in (0 : ℝ)..t, H.K (t - s) (extendPiece u s) (extendPiece u s) := by
    intro t ht
    rw [extend_eq hT0 u ht]
    conv_lhs => rw [hu]
    rw [ContinuousMap.add_apply, hF, hB]
  have h0 : extendPiece u 0 = x := by
    rw [hval 0 ⟨le_rfl, hT0⟩]
    simp [H.G_zero]
  have cu : ContinuousOn (extendPiece u) (Icc 0 T) := (extend_continuous hT0 u).continuousOn
  have bu : ∀ s ∈ Icc (0 : ℝ) T, ‖extendPiece u s‖ ≤ ‖u‖ := fun s hs => by
    rw [extend_eq hT0 u hs]
    exact u.norm_coe_le_norm _
  have hi := (hD X H _ _ 0 T _ _ hT0 cu cu bu bu).1
  refine ⟨h0, cu, fun t ht => ⟨hi t ht, ?_⟩⟩
  rw [sub_zero, h0]
  exact hval t ht

theorem bil_symm (hP : PieceOperatorStatement) (H : HeatBilinear X) {T : ℝ} (hT : 0 < T)
    (f g : Piece X T) : H.pieceBil T f g = H.pieceBil T g f := by
  obtain ⟨hB, -, -, -⟩ := hP X H T hT
  ext t
  rw [hB, hB]
  exact intervalIntegral.integral_congr fun s _ => H.K_symm _ _ _

theorem piece_identity {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : Z →L[ℝ] P) (B : P →L[ℝ] P →L[ℝ] P)
    (hB : ∀ f g, B f g = B g f) (t : ℝ) (ht : t ≠ 0) (b w r I D : P) (b0 y : Z)
    (hb : b = F b0 + B b b + r)
    (hw : w - (2 : ℝ) • B b w - I = t • B w w - t⁻¹ • r + D)
    (hy : t • I + t • D = F y) :
    b + t • w = F (b0 + y) + B (b + t • w) (b + t • w) := by
  have hw' : w = (2 : ℝ) • B b w + I + (t • B w w - t⁻¹ • r + D) := by
    rw [← hw]
    abel
  have hr : t • t⁻¹ • r = r := by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
  have e1 : t • w = (2 * t) • B b w + t • I + t • D + (t * t) • B w w - r := by
    calc t • w = t • ((2 : ℝ) • B b w + I + (t • B w w - t⁻¹ • r + D)) := congrArg (t • ·) hw'
      _ = (2 * t) • B b w + t • I + t • D + (t * t) • B w w - r := by
        rw [smul_add, smul_add, smul_add, smul_sub, hr]
        module
  rw [map_add F b0 y, ← hy]
  simp only [map_add, map_smul, add_apply, smul_apply]
  rw [hB w b]
  conv_lhs => rw [hb, e1]
  module

def seqNonlin (H : ℕ → HeatBilinear X) (L θ : ℝ) (res : ℕ → Piece X L) (ξ : X)
    (z : ℕ → Piece X L) (n : ℕ) : Piece X L :=
  θ ^ n • (H n).pieceBil L (z n) (z n) - (θ ^ n)⁻¹ • res n +
    if n = 0 then (H 0).pieceFree L ξ else 0

theorem seqNonlin_sub (H : ℕ → HeatBilinear X) (L θ : ℝ) (res : ℕ → Piece X L) (ξ : X)
    (z z' : ℕ → Piece X L) (n : ℕ) :
    seqNonlin H L θ res ξ z n - seqNonlin H L θ res ξ z' n =
      θ ^ n • (H n).pieceBil L (z n) (z n) - θ ^ n • (H n).pieceBil L (z' n) (z' n) := by
  unfold seqNonlin
  abel

theorem quad_le {A q x s : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) (hqA : 8 * q * A ≤ 1) (hs0 : 0 ≤ s)
    (hs : s ≤ 2 * A) (hx : x ≤ A + q * s ^ 2) : x ≤ 2 * A := by
  have h2 : s ^ 2 ≤ (2 * A) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  nlinarith [mul_le_mul_of_nonneg_left h2 hq, mul_le_mul_of_nonneg_left hqA hA]

theorem exists_fixed {Y : Type*} [NormedAddCommGroup Y] [CompleteSpace Y] (Φ : Y → Y) (A q : ℝ)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hqA : 8 * q * A ≤ 1)
    (hb : ∀ z, ‖Φ z‖ ≤ A + q * ‖z‖ ^ 2)
    (hl : ∀ z z', ‖Φ z - Φ z'‖ ≤ q * (‖z‖ + ‖z'‖) * ‖z - z'‖) :
    ∃ z, Φ z = z ∧ ‖z‖ ≤ 2 * A := by
  have hmaps : ∀ z ∈ Metric.closedBall (0 : Y) (2 * A), Φ z ∈ Metric.closedBall (0 : Y) (2 * A) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    exact quad_le hA hq hqA (norm_nonneg _) hz (hb z)
  have : CompleteSpace (Metric.closedBall (0 : Y) (2 * A)) :=
    (Metric.isClosed_closedBall).completeSpace_coe
  have : Nonempty (Metric.closedBall (0 : Y) (2 * A)) :=
    ⟨⟨0, by rw [Metric.mem_closedBall, dist_self]; linarith⟩⟩
  let Ψ : Metric.closedBall (0 : Y) (2 * A) → Metric.closedBall (0 : Y) (2 * A) :=
    fun z => ⟨Φ z, hmaps z z.2⟩
  have hc : ContractingWith (1 / 2 : NNReal) Ψ := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun z z' => ?_⟩
    show dist (Φ z) (Φ z') ≤ ((1 / 2 : NNReal) : ℝ) * dist (z : Y) z'
    have hz := z.2
    have hz' := z'.2
    rw [Metric.mem_closedBall, dist_zero_right] at hz hz'
    rw [dist_eq_norm, dist_eq_norm]
    have h1 : q * (‖(z : Y)‖ + ‖(z' : Y)‖) ≤ 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hz hz') hq]
    calc ‖Φ z - Φ z'‖ ≤ q * (‖(z : Y)‖ + ‖(z' : Y)‖) * ‖(z : Y) - z'‖ := hl _ _
      _ ≤ 1 / 2 * ‖(z : Y) - z'‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ((1 / 2 : NNReal) : ℝ) * ‖(z : Y) - z'‖ := by norm_num
  have hfix : Ψ (ContractingWith.fixedPoint Ψ hc) = ContractingWith.fixedPoint Ψ hc :=
    hc.fixedPoint_isFixedPt
  refine ⟨(ContractingWith.fixedPoint Ψ hc).1, congrArg Subtype.val hfix, ?_⟩
  have h := (ContractingWith.fixedPoint Ψ hc).2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

end SeqPerturbation.Internal

open SeqPerturbation.Internal in
theorem seqPerturbation (hP : PieceOperatorStatement) (hD : VarConstIntegralStatement) :
    SeqPerturbation := by
  intro X E _ _ _ _ _ _ H L θ c CK M ρ ub res J R ξ hL hL1 hθ hθ1 hCK hHCK hub hlink heq hres hR
    hsmall
  have hL0 : 0 ≤ L := hL.le
  have hLq : 0 ≤ L ^ (1 / 4 : ℝ) := rpow_nonneg hL0 _
  have hη0 : 0 ≤ 4 * CK * L ^ (1 / 4 : ℝ) := mul_nonneg (mul_nonneg (by norm_num) hCK) hLq
  have hBn : ∀ n, ‖(H n).pieceBil L‖ ≤ 4 * CK * L ^ (1 / 4 : ℝ) := fun n =>
    ((hP X (H n) L hL).2.1 hL1).trans
      (mul_le_mul_of_nonneg_right (by linarith [hHCK n]) hLq)
  have hF1 : ∀ n, ‖(H n).pieceFree L‖ ≤ 1 := fun n => (hP X (H n) L hL).2.2.2
  have hρ : 0 ≤ ρ := by
    have h := hres 0
    rw [pow_zero, one_mul] at h
    exact (norm_nonneg _).trans h
  have hθn : ∀ n : ℕ, 0 < θ ^ n := fun n => pow_pos hθ n
  have hθn1 : ∀ n : ℕ, θ ^ n ≤ 1 := fun n => pow_le_one₀ hθ.le hθ1.le
  have hzn : ∀ (z : lp (fun _ : ℕ => Piece X L) ∞) n, ‖z n‖ ≤ ‖z‖ := fun z n =>
    lp.norm_apply_le_norm ENNReal.top_ne_zero z n
  have hgb : ∀ (z : lp (fun _ : ℕ => Piece X L) ∞) n,
      ‖seqNonlin H L θ res ξ z n‖ ≤ 4 * CK * L ^ (1 / 4 : ℝ) * ‖z‖ ^ 2 + (ρ + ‖ξ‖) := by
    intro z n
    have q1 : ‖θ ^ n • (H n).pieceBil L (z n) (z n)‖ ≤ 4 * CK * L ^ (1 / 4 : ℝ) * ‖z‖ ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg (hθn n).le]
      have h1 := ((H n).pieceBil L).le_opNorm₂ (z n) (z n)
      have h2 := hzn z n
      have h3 : ‖(H n).pieceBil L‖ * ‖z n‖ * ‖z n‖ ≤ 4 * CK * L ^ (1 / 4 : ℝ) * ‖z‖ * ‖z‖ :=
        mul_le_mul (mul_le_mul (hBn n) h2 (norm_nonneg _) hη0) h2 (norm_nonneg _)
          (mul_nonneg hη0 (norm_nonneg _))
      have h4 := mul_le_of_le_one_left (norm_nonneg ((H n).pieceBil L (z n) (z n))) (hθn1 n)
      nlinarith
    have q2 : ‖(θ ^ n)⁻¹ • res n‖ ≤ ρ := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (hθn n).le]
      calc (θ ^ n)⁻¹ * ‖res n‖ ≤ (θ ^ n)⁻¹ * (θ ^ n * ρ) :=
            mul_le_mul_of_nonneg_left (hres n) (inv_nonneg.2 (hθn n).le)
        _ = ρ := inv_mul_cancel_left₀ (hθn n).ne' ρ
    have q3 : ‖(if n = 0 then (H 0).pieceFree L ξ else 0 : Piece X L)‖ ≤ ‖ξ‖ := by
      split_ifs
      · exact (((H 0).pieceFree L).le_opNorm ξ).trans
          (mul_le_of_le_one_left (norm_nonneg _) (hF1 0))
      · rw [norm_zero]
        exact norm_nonneg _
    unfold seqNonlin
    have q4 := norm_add_le (θ ^ n • (H n).pieceBil L (z n) (z n) - (θ ^ n)⁻¹ • res n)
      (if n = 0 then (H 0).pieceFree L ξ else 0 : Piece X L)
    have q5 := norm_sub_le (θ ^ n • (H n).pieceBil L (z n) (z n)) ((θ ^ n)⁻¹ • res n)
    linarith
  have hgd : ∀ (z z' : lp (fun _ : ℕ => Piece X L) ∞) n,
      ‖seqNonlin H L θ res ξ z n - seqNonlin H L θ res ξ z' n‖ ≤
        4 * CK * L ^ (1 / 4 : ℝ) * (‖z‖ + ‖z'‖) * ‖z - z'‖ := by
    intro z z' n
    rw [seqNonlin_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (hθn n).le]
    have hd : ‖z n - z' n‖ ≤ ‖z - z'‖ := by
      have h := hzn (z - z') n
      rwa [lp.coeFn_sub, Pi.sub_apply] at h
    have key : (H n).pieceBil L (z n) (z n) - (H n).pieceBil L (z' n) (z' n) =
        (H n).pieceBil L (z n) (z n - z' n) + (H n).pieceBil L (z n - z' n) (z' n) := by
      rw [map_sub, map_sub, sub_apply]
      abel
    rw [key]
    have h1 := ((H n).pieceBil L).le_opNorm₂ (z n) (z n - z' n)
    have h2 := ((H n).pieceBil L).le_opNorm₂ (z n - z' n) (z' n)
    have t1 : ‖(H n).pieceBil L‖ * ‖z n‖ * ‖z n - z' n‖ ≤
        4 * CK * L ^ (1 / 4 : ℝ) * ‖z‖ * ‖z - z'‖ :=
      mul_le_mul (mul_le_mul (hBn n) (hzn z n) (norm_nonneg _) hη0) hd (norm_nonneg _)
        (mul_nonneg hη0 (norm_nonneg _))
    have t2 : ‖(H n).pieceBil L‖ * ‖z n - z' n‖ * ‖z' n‖ ≤
        4 * CK * L ^ (1 / 4 : ℝ) * ‖z - z'‖ * ‖z'‖ :=
      mul_le_mul (mul_le_mul (hBn n) hd (norm_nonneg _) hη0) (hzn z' n) (norm_nonneg _)
        (mul_nonneg hη0 (norm_nonneg _))
    have h3 := norm_add_le ((H n).pieceBil L (z n) (z n - z' n))
      ((H n).pieceBil L (z n - z' n) (z' n))
    have h4 := mul_le_of_le_one_left (norm_nonneg ((H n).pieceBil L (z n) (z n - z' n) +
      (H n).pieceBil L (z n - z' n) (z' n))) (hθn1 n)
    nlinarith
  have hmem : ∀ z : lp (fun _ : ℕ => Piece X L) ∞, Memℓp (seqNonlin H L θ res ξ z) ∞ :=
    fun z => memℓp_infty ⟨4 * CK * L ^ (1 / 4 : ℝ) * ‖z‖ ^ 2 + (ρ + ‖ξ‖), by
      rintro _ ⟨n, rfl⟩
      exact hgb z n⟩
  let g : lp (fun _ : ℕ => Piece X L) ∞ → lp (fun _ : ℕ => Piece X L) ∞ :=
    fun z => ⟨seqNonlin H L θ res ξ z, hmem z⟩
  have ha0 : 0 ≤ ρ + ‖ξ‖ := add_nonneg hρ (norm_nonneg _)
  have hgn : ∀ z, ‖g z‖ ≤ 4 * CK * L ^ (1 / 4 : ℝ) * ‖z‖ ^ 2 + (ρ + ‖ξ‖) := fun z =>
    lp.norm_le_of_forall_le (add_nonneg (mul_nonneg hη0 (sq_nonneg _)) ha0) (fun n => hgb z n)
  have hgl : ∀ z z', ‖g z - g z'‖ ≤ 4 * CK * L ^ (1 / 4 : ℝ) * (‖z‖ + ‖z'‖) * ‖z - z'‖ :=
    fun z z' => lp.norm_le_of_forall_le
      (mul_nonneg (mul_nonneg hη0 (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _))
      (fun n => by
        rw [lp.coeFn_sub, Pi.sub_apply]
        exact hgd z z' n)
  have hRn0 : 0 ≤ ‖R‖ := norm_nonneg _
  have hRg : ∀ z, ‖R (g z)‖ ≤ ‖R‖ * (ρ + ‖ξ‖) + ‖R‖ * (4 * CK * L ^ (1 / 4 : ℝ)) * ‖z‖ ^ 2 :=
    fun z => by
      have h := mul_le_mul_of_nonneg_left (hgn z) hRn0
      nlinarith [R.le_opNorm (g z)]
  have hA : 0 ≤ ‖R‖ * (ρ + ‖ξ‖) := mul_nonneg hRn0 ha0
  have hq : 0 ≤ ‖R‖ * (4 * CK * L ^ (1 / 4 : ℝ)) := mul_nonneg hRn0 hη0
  have hX : 0 ≤ ‖R‖ ^ 2 * CK * L ^ (1 / 4 : ℝ) * (ρ + ‖ξ‖) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hCK) hLq) ha0
  have hqA : 8 * (‖R‖ * (4 * CK * L ^ (1 / 4 : ℝ))) * (‖R‖ * (ρ + ‖ξ‖)) ≤ 1 := by
    nlinarith
  obtain ⟨z, hz, hzb⟩ := exists_fixed (fun z => (R (g z)).2) _ _ hA hq hqA
    (fun z => (norm_snd_le _).trans (hRg z))
    (fun z z' => by
      show ‖(R (g z)).2 - (R (g z')).2‖ ≤ _
      rw [← Prod.snd_sub, ← map_sub]
      have h := mul_le_mul_of_nonneg_left (hgl z z') hRn0
      nlinarith [norm_snd_le (R (g z - g z')), R.le_opNorm (g z - g z')])
  have hz2 : (R (g z)).2 = z := hz
  have hzeq : ∀ n, z n - (2 : ℝ) • (H n).pieceBil L (ub n) (z n) -
      (if n = 0 then (H 0).pieceFree L (J (R (g z)).1)
        else (c / θ) • (H n).pieceFree L (pieceEnd L (z (n - 1)))) =
        seqNonlin H L θ res ξ z n := by
    intro n
    have h := hR (g z) n
    rw [hz2] at h
    exact h
  have h0 : ub 0 + θ ^ 0 • z 0 = (H 0).pieceFree L (extendPiece (ub 0) 0 + (J (R (g z)).1 + ξ)) +
      (H 0).pieceBil L (ub 0 + θ ^ 0 • z 0) (ub 0 + θ ^ 0 • z 0) := by
    refine piece_identity _ _ (bil_symm hP (H 0) hL) _ (hθn 0).ne' (ub 0) (z 0) (res 0)
      ((H 0).pieceFree L (J (R (g z)).1)) ((H 0).pieceFree L ξ) _ _ (heq 0) ?_ ?_
    · have h := hzeq 0
      rw [if_pos rfl] at h
      rw [h]
      unfold seqNonlin
      rw [if_pos rfl]
    · rw [pow_zero, one_smul, one_smul, map_add]
  have hs : ∀ k : ℕ, ub (k + 1) + θ ^ (k + 1) • z (k + 1) =
      (H (k + 1)).pieceFree L (extendPiece (ub (k + 1)) 0 + c • pieceEnd L (θ ^ k • z k)) +
      (H (k + 1)).pieceBil L (ub (k + 1) + θ ^ (k + 1) • z (k + 1))
        (ub (k + 1) + θ ^ (k + 1) • z (k + 1)) := by
    intro k
    refine piece_identity _ _ (bil_symm hP (H (k + 1)) hL) _ (hθn (k + 1)).ne' (ub (k + 1))
      (z (k + 1)) (res (k + 1)) ((c / θ) • (H (k + 1)).pieceFree L (pieceEnd L (z k))) 0 _ _
      (heq (k + 1)) ?_ ?_
    · have h := hzeq (k + 1)
      rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel] at h
      rw [h]
      unfold seqNonlin
      rw [if_neg (Nat.succ_ne_zero k), add_zero]
    · rw [smul_zero, add_zero, map_smul, map_smul, map_smul, smul_smul, smul_smul]
      congr 1
      rw [pow_succ]
      field_simp
  have hm0 := mild_of_eq hP hD (H 0) hL _ _ h0
  have hms : ∀ k, _ := fun k => mild_of_eq hP hD (H (k + 1)) hL _ _ (hs k)
  refine ⟨(R (g z)).1, fun n => z n, fun n => (hzn z n).trans (by linarith),
    (norm_fst_le _).trans (by
      have := quad_le hA hq hqA (norm_nonneg _) hzb (hRg z)
      linarith), ?_, ?_, ?_⟩
  · intro n
    rcases n with _ | k
    · exact hm0.2
    · exact (hms k).2
  · have h := hm0.1
    rw [extend_add_smul hL0, pow_zero, one_smul] at h
    have h' := add_left_cancel h
    rw [h', add_comm]
  · intro n
    rw [(hms n).1, hlink n, ← smul_add, ← map_add]
