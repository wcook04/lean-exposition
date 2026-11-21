import Breakdown.Torus.CompareStatements
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace CompareChain.Internal

theorem shiftChain_self {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : ℕ → X →L[ℝ] X) (m : ℕ) : shiftChain B m m = ContinuousLinearMap.id ℝ X := by
  cases m with
  | zero => simp [shiftChain]
  | succ n => simp [shiftChain]

theorem shiftChain_succ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : ℕ → X →L[ℝ] X) {m n : ℕ} (h : m ≤ n) :
    shiftChain B m (n + 1) = (B n).comp (shiftChain B m n) := by
  simp only [shiftChain]
  rw [if_neg (by omega)]

theorem pieceEnd_apply {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ} (hL : 0 ≤ L)
    (z : Piece X L) : pieceEnd L z = z ⟨L, hL, le_rfl⟩ := by
  unfold pieceEnd
  rw [dif_pos hL]
  rfl

theorem r3Step_apply (F : MildFramework Freq.X) (hP : PieceOperatorStatement) (P : ℝ) (k : ℕ)
    (θ : ℝ) (hL : 0 < MildFramework.stepLength P k) (n : ℕ)
    (z : Piece Freq.X (MildFramework.stepLength P k)) (s : Icc (0 : ℝ) (MildFramework.stepLength P k)) :
    r3Step F P k θ n z s =
      θ⁻¹ • F.G s (F.D (Real.exp (-(P / k))) (pieceEnd (MildFramework.stepLength P k) z)) := by
  have h := (hP Freq.X F.toHeatBilinear _ hL).2.2.1
  show θ⁻¹ • (F.stepFree P k (F.stepEnd P k z)) s = _
  exact congrArg (θ⁻¹ • ·) (h _ s)

theorem chain_apply {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {L : ℝ} (hL : 0 ≤ L)
    (B : ℕ → Piece Y L →L[ℝ] Piece Y L) (c : ℝ) (A : ℕ → ℝ → Y →L[ℝ] Y)
    (hB : ∀ n (z : Piece Y L) (s : Icc (0 : ℝ) L), B n z s = c • A n s (pieceEnd L z))
    (m : ℕ) (Ψ : ℕ → ℝ → Y →L[ℝ] Y) (h0 : ∀ s : Icc (0 : ℝ) L, A m s = Ψ 0 s)
    (hs : ∀ (j : ℕ) (s : Icc (0 : ℝ) L), (A (m + j + 1) s).comp (Ψ j L) = Ψ (j + 1) s)
    (y : Piece Y L) : ∀ (j : ℕ) (s : Icc (0 : ℝ) L),
      shiftChain B m (m + j + 1) y s = c ^ (j + 1) • Ψ j s (pieceEnd L y) := by
  intro j
  induction j with
  | zero =>
    intro s
    rw [Nat.add_zero, shiftChain_succ _ le_rfl, shiftChain_self, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, hB, h0, zero_add, pow_one]
  | succ j ih =>
    intro s
    rw [show m + (j + 1) + 1 = (m + j + 1) + 1 by omega, shiftChain_succ _ (by omega),
      ContinuousLinearMap.comp_apply, hB, pieceEnd_apply hL, ih, map_smul, smul_smul, ← pow_succ',
      ← hs j s]
    rfl

theorem r3Chain (F : MildFramework Freq.X) (hP : PieceOperatorStatement) (P : ℝ) (k : ℕ) (θ : ℝ)
    (hPk : 0 < P) (hk : 0 < k) (y : Piece Freq.X (MildFramework.stepLength P k)) (m j : ℕ)
    (s : Icc (0 : ℝ) (MildFramework.stepLength P k)) :
      shiftChain (r3Step F P k θ) m (m + j + 1) y s =
        (θ⁻¹) ^ (j + 1) • F.D (Real.exp (-(P / k)) ^ (j + 1))
          (F.G (Real.exp (-(P / k)) ^ (j + 1) * s + Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (j + 1))
            (pieceEnd (MildFramework.stepLength P k) y)) := by
  have hl0 : 0 < Real.exp (-(P / k)) := Real.exp_pos _
  have hl1 : Real.exp (-(P / k)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (div_pos hPk (Nat.cast_pos.mpr hk)))
  have hL : 0 < MildFramework.stepLength P k := by
    show 0 < 1 - Real.exp (-(P / k))
    linarith
  have h0 : ∀ t : Icc (0 : ℝ) (MildFramework.stepLength P k),
      (F.G t).comp (F.D (Real.exp (-(P / k)))) = (F.D (Real.exp (-(P / k)) ^ (0 + 1))).comp
        (F.G (Real.exp (-(P / k)) ^ (0 + 1) * t + Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (0 + 1))) := by
    intro t
    have e : Real.exp (-(P / k)) ^ (0 + 1) * t + Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (0 + 1) =
        Real.exp (-(P / k)) * t := by ring
    have e2 : Real.exp (-(P / k)) ^ (0 + 1) = Real.exp (-(P / k)) := pow_one _
    calc (F.G t).comp (F.D (Real.exp (-(P / k))))
        = (F.D (Real.exp (-(P / k)))).comp (F.G (Real.exp (-(P / k)) * t)) :=
          (F.D_G _ _ hl0 t.2.1).symm
      _ = (F.D (Real.exp (-(P / k)) ^ (0 + 1))).comp
          (F.G (Real.exp (-(P / k)) ^ (0 + 1) * t + Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (0 + 1))) :=
          congrArg₂ (fun a b => (F.D a).comp (F.G b)) e2.symm e.symm
  have hs : ∀ (i : ℕ) (t : Icc (0 : ℝ) (MildFramework.stepLength P k)),
      ((F.G t).comp (F.D (Real.exp (-(P / k))))).comp ((F.D (Real.exp (-(P / k)) ^ (i + 1))).comp
        (F.G (Real.exp (-(P / k)) ^ (i + 1) * MildFramework.stepLength P k + Real.exp (-(P / k)) -
          Real.exp (-(P / k)) ^ (i + 1)))) =
      (F.D (Real.exp (-(P / k)) ^ (i + 1 + 1))).comp (F.G (Real.exp (-(P / k)) ^ (i + 1 + 1) * t +
          Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1 + 1))) := by
    intro i t
    have ht : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have hpos : 0 < Real.exp (-(P / k)) ^ (i + 1) := pow_pos hl0 _
    have hpos2 : 0 < Real.exp (-(P / k)) ^ (i + 1 + 1) := pow_pos hl0 _
    have hle : Real.exp (-(P / k)) ^ (i + 1 + 1) ≤ Real.exp (-(P / k)) := by
      calc Real.exp (-(P / k)) ^ (i + 1 + 1) = Real.exp (-(P / k)) ^ (i + 1) * Real.exp (-(P / k)) :=
            pow_succ _ _
        _ ≤ 1 * Real.exp (-(P / k)) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hl0.le hl1.le) hl0.le
        _ = Real.exp (-(P / k)) := one_mul _
    have ea : Real.exp (-(P / k)) ^ (i + 1) * MildFramework.stepLength P k + Real.exp (-(P / k)) -
        Real.exp (-(P / k)) ^ (i + 1) = Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1 + 1) := by
      show Real.exp (-(P / k)) ^ (i + 1) * (1 - Real.exp (-(P / k))) + Real.exp (-(P / k)) -
        Real.exp (-(P / k)) ^ (i + 1) = Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1 + 1)
      ring
    have eb : Real.exp (-(P / k)) ^ (i + 1 + 1) * t +
        (Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1 + 1)) =
        Real.exp (-(P / k)) ^ (i + 1 + 1) * t + Real.exp (-(P / k)) -
        Real.exp (-(P / k)) ^ (i + 1 + 1) := by ring
    have ec : Real.exp (-(P / k)) * Real.exp (-(P / k)) ^ (i + 1) = Real.exp (-(P / k)) ^ (i + 1 + 1) :=
      (pow_succ' _ _).symm
    have hc : 0 ≤ Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1 + 1) := by linarith
    have hDm : (F.D (Real.exp (-(P / k)))).comp (F.D (Real.exp (-(P / k)) ^ (i + 1))) =
        F.D (Real.exp (-(P / k)) ^ (i + 1 + 1)) :=
      (F.D_mul _ _ hl0 hpos).symm.trans (congrArg F.D ec)
    apply ContinuousLinearMap.ext
    intro x
    calc F.G t (F.D (Real.exp (-(P / k))) (F.D (Real.exp (-(P / k)) ^ (i + 1))
          (F.G (Real.exp (-(P / k)) ^ (i + 1) * MildFramework.stepLength P k + Real.exp (-(P / k)) -
            Real.exp (-(P / k)) ^ (i + 1)) x)))
        = F.G t (F.D (Real.exp (-(P / k)) ^ (i + 1 + 1))
          (F.G (Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1 + 1)) x)) :=
          congrArg₂ (fun (M : Freq.X →L[ℝ] Freq.X) (a : ℝ) => F.G t (M (F.G a x))) hDm ea
      _ = F.D (Real.exp (-(P / k)) ^ (i + 1 + 1)) (F.G (Real.exp (-(P / k)) ^ (i + 1 + 1) * t)
          (F.G (Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1 + 1)) x)) :=
          (DFunLike.congr_fun (F.D_G _ _ hpos2 ht) _).symm
      _ = F.D (Real.exp (-(P / k)) ^ (i + 1 + 1)) (F.G (Real.exp (-(P / k)) ^ (i + 1 + 1) * t +
          (Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1 + 1))) x) :=
          congrArg (F.D (Real.exp (-(P / k)) ^ (i + 1 + 1)))
            (DFunLike.congr_fun (F.G_add _ _ (mul_nonneg hpos2.le ht) hc) x).symm
      _ = F.D (Real.exp (-(P / k)) ^ (i + 1 + 1)) (F.G (Real.exp (-(P / k)) ^ (i + 1 + 1) * t +
          Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1 + 1)) x) :=
          congrArg (fun a => F.D (Real.exp (-(P / k)) ^ (i + 1 + 1)) (F.G a x)) eb
  exact chain_apply hL.le (r3Step F P k θ) θ⁻¹
    (fun _ t => (F.G t).comp (F.D (Real.exp (-(P / k)))))
    (fun n z t => r3Step_apply F hP P k θ hL n z t) m
    (fun i t => (F.D (Real.exp (-(P / k)) ^ (i + 1))).comp
      (F.G (Real.exp (-(P / k)) ^ (i + 1) * t + Real.exp (-(P / k)) - Real.exp (-(P / k)) ^ (i + 1))))
    h0 hs y j s

theorem torusStep_apply (hK : KernelSharpBound) (hP : PieceOperatorStatement) (T lam θ : ℝ)
    (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (hL : 0 < 1 - lam) (n : ℕ)
    (z : Piece V (1 - lam)) (s : Icc (0 : ℝ) (1 - lam)) :
    torusStep hK T lam θ hT hT1 hl hl1 n z s =
      (lam ^ (1 / 4 : ℝ) / θ) • heat (stepScale T lam (n + 1) * s) (pieceEnd (1 - lam) z) := by
  have h := (hP V (stepFrame hK (stepScale T lam (n + 1)) (stepScale_pos hT hl (n + 1))
    (stepScale_le_one hT1 hl hl1 (n + 1))) _ hL).2.2.1
  show (lam ^ (1 / 4 : ℝ) / θ) • ((stepFrame hK (stepScale T lam (n + 1)) (stepScale_pos hT hl (n + 1))
    (stepScale_le_one hT1 hl hl1 (n + 1))).pieceFree (1 - lam) (pieceEnd (1 - lam) z)) s = _
  exact congrArg ((lam ^ (1 / 4 : ℝ) / θ) • ·) (h _ s)

theorem torusChain (hK : KernelSharpBound) (hP : PieceOperatorStatement) (T lam θ : ℝ)
    (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (hlt : lam < 1)
    (y : Piece V (1 - lam)) (m j : ℕ) (s : Icc (0 : ℝ) (1 - lam)) :
      shiftChain (torusStep hK T lam θ hT hT1 hl hl1) m (m + j + 1) y s =
        (lam ^ (1 / 4 : ℝ) / θ) ^ (j + 1) •
          heat (stepScale T lam m * (lam ^ (j + 1) * s + lam - lam ^ (j + 1))) (pieceEnd (1 - lam) y) := by
  have hL : 0 < 1 - lam := by linarith
  have hm : 0 < stepScale T lam m := stepScale_pos hT hl m
  have key := chain_apply hL.le (torusStep hK T lam θ hT hT1 hl hl1) (lam ^ (1 / 4 : ℝ) / θ)
    (fun n t => heat (stepScale T lam (n + 1) * t))
    (fun n z t => torusStep_apply hK hP T lam θ hT hT1 hl hl1 hL n z t) m
    (fun i t => heat (stepScale T lam m * (lam ^ (i + 1) * t + lam - lam ^ (i + 1))))
    (fun t => by
      show heat (stepScale T lam (m + 1) * t) =
        heat (stepScale T lam m * (lam ^ (0 + 1) * t + lam - lam ^ (0 + 1)))
      congr 1
      simp only [stepScale]
      ring)
    (fun i t => by
      have ht : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have hle : lam ^ (i + 1 + 1) ≤ lam := by
        calc lam ^ (i + 1 + 1) = lam ^ (i + 1) * lam := pow_succ _ _
          _ ≤ 1 * lam := mul_le_mul_of_nonneg_right (pow_le_one₀ hl.le hl1) hl.le
          _ = lam := one_mul _
      have ea : stepScale T lam m * (lam ^ (i + 1) * (1 - lam) + lam - lam ^ (i + 1)) =
          stepScale T lam m * (lam - lam ^ (i + 1 + 1)) := by ring
      have eb : stepScale T lam m * (lam ^ (i + 1 + 1) * t + lam - lam ^ (i + 1 + 1)) =
          stepScale T lam (m + i + 1 + 1) * t + stepScale T lam m * (lam - lam ^ (i + 1 + 1)) := by
        simp only [stepScale]
        ring
      show (heat (stepScale T lam (m + i + 1 + 1) * t)).comp
          (heat (stepScale T lam m * (lam ^ (i + 1) * (1 - lam) + lam - lam ^ (i + 1)))) =
        heat (stepScale T lam m * (lam ^ (i + 1 + 1) * t + lam - lam ^ (i + 1 + 1)))
      rw [ea, eb, heat_add _ _ (mul_nonneg (stepScale_pos hT hl _).le ht)
        (mul_nonneg hm.le (by linarith))])
    y j s
  exact key

end CompareChain.Internal

theorem r3ChainFormula (hP : PieceOperatorStatement) : R3ChainFormula := by
  intro F hG hD P k θ hPk hk y m j s
  rw [← hG, ← hD]
  exact CompareChain.Internal.r3Chain F hP P k θ hPk hk y m j s

theorem torusChainFormula (hP : PieceOperatorStatement) : TorusChainFormula := by
  intro hK T lam θ hT hT1 hl hl1 hlt y m j s
  exact CompareChain.Internal.torusChain hK hP T lam θ hT hT1 hl hl1 hlt y m j s

end Breakdown.Periodic
