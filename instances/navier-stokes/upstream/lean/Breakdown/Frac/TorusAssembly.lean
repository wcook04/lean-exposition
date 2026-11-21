import Breakdown.Frac.StTorusReduce
import Breakdown.Frac.StTorusStepApprox
import Breakdown.Frac.StTorusInverse
import Breakdown.Frac.StProfile
import Breakdown.Frac.ScaledStatements
import Breakdown.Torus.Assembly
import Breakdown.Torus.TestLift
import Breakdown.Torus.StatementsSeqOps

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracTorusAssembly.Internal

theorem norm_fracTorusSeed_le (hS : SeqOpSpec) (α : ℝ) (hα : 1 < α) (T lam : ℝ) (hT : 0 < T) (hT1 : T ≤ 1)
    (hl : 0 < lam) (hl1 : lam ≤ 1) (hl1' : lam < 1) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Jt : E →L[ℝ] V) : ‖fracTorusSeed α hα T lam hT hT1 hl hl1 Jt‖ ≤ ‖Jt‖ := by
  unfold fracTorusSeed
  have h0 := (hS E (Piece V (1 - lam)) (fun _ => 0) 0 (by simp) le_rfl).2.2.2
    (((fracStepFrame α hα (stepScale T lam 0) (stepScale_pos hT hl 0)
      (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam)).comp Jt)
  refine h0.2.trans ?_
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hF := (pieceOperator V (fracStepFrame α hα (stepScale T lam 0) (stepScale_pos hT hl 0)
      (stepScale_le_one hT1 hl hl1 0)) (1 - lam) (by linarith)).2.2.2
  calc _ ≤ 1 * ‖Jt‖ := mul_le_mul_of_nonneg_right hF (norm_nonneg _)
    _ = ‖Jt‖ := one_mul _

set_option maxHeartbeats 2000000 in
theorem frac_torus_seq_equation (hS : SeqOpSpec) (α : ℝ) (hα : 1 < α) (T lam θ : ℝ) (hT : 0 < T)
    (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (hl1' : lam < 1) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Jt : E →L[ℝ] V) (f : ℕ → Piece V (1 - lam)) (Mf : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ Mf) (R : TorusSeq (1 - lam) →L[ℝ] E × TorusSeq (1 - lam))
    (hR : (fracTorusOp α hα T lam θ hT hT1 hl hl1 Jt f).comp R = ContinuousLinearMap.id ℝ _) :
    ∀ g n, (R g).2 n - (2 : ℝ) • (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam) (f n) ((R g).2 n) -
      (if n = 0 then (fracStepFrame α hα (stepScale T lam 0) (stepScale_pos hT hl 0)
          (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam) (Jt (R g).1)
        else (lam ^ dilExponent α / θ) • (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
          (stepScale_le_one hT1 hl hl1 n)).pieceFree (1 - lam) (pieceEnd (1 - lam) ((R g).2 (n - 1)))) = g n := by
  intro g n
  have hL : 0 < 1 - lam := by linarith
  have hKc : 0 < fracStepCK α hα := (fracStepCK_spec α hα).1
  have hbil : ∀ m, ‖(2 : ℝ) • (fracStepFrame α hα (stepScale T lam m) (stepScale_pos hT hl m)
      (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam) (f m)‖ ≤
      ‖(2 : ℝ)‖ * (4 * fracStepCK α hα * (1 - lam) ^ (1 / 4 : ℝ) * |Mf|) := by
    intro m
    have hb : ‖(fracStepFrame α hα (stepScale T lam m) (stepScale_pos hT hl m)
        (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam)‖ ≤ 4 * fracStepCK α hα * (1 - lam) ^ (1 / 4 : ℝ) :=
      (pieceOperator V (fracStepFrame α hα (stepScale T lam m) (stepScale_pos hT hl m)
        (stepScale_le_one hT1 hl hl1 m)) (1 - lam) hL).2.1 (by linarith)
    have h2 := ContinuousLinearMap.le_opNorm ((fracStepFrame α hα (stepScale T lam m) (stepScale_pos hT hl m)
        (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam)) (f m)
    have h3 : ‖(fracStepFrame α hα (stepScale T lam m) (stepScale_pos hT hl m)
        (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam) (f m)‖ ≤
        4 * fracStepCK α hα * (1 - lam) ^ (1 / 4 : ℝ) * |Mf| :=
      h2.trans (mul_le_mul hb ((hf m).trans (le_abs_self _)) (norm_nonneg _) (by positivity))
    exact (norm_smul_le (2 : ℝ) _).trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
  have hA := hS E (Piece V (1 - lam)) (fun _ => 0) 0 (by simp) le_rfl
  have hB := hS (Piece V (1 - lam)) (Piece V (1 - lam)) _ _ hbil (by positivity)
  have hC := hS (Piece V (1 - lam)) (Piece V (1 - lam)) (fun _ => 0)
    (‖lam ^ dilExponent α / θ‖ * (1 * ‖pieceEnd (X := V) (1 - lam)‖)) (fun _ => by simp; positivity)
    (by positivity)
  have hsh := hC.2.2.1 (fun m => (lam ^ dilExponent α / θ) •
    ((fracStepFrame α hα (stepScale T lam (m + 1)) (stepScale_pos hT hl (m + 1))
      (stepScale_le_one hT1 hl hl1 (m + 1))).pieceFree (1 - lam)).comp (pieceEnd (1 - lam))) (fun m => by
        refine (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        exact (pieceOperator V (fracStepFrame α hα (stepScale T lam (m + 1)) (stepScale_pos hT hl (m + 1))
          (stepScale_le_one hT1 hl hl1 (m + 1))) (1 - lam) hL).2.2.2)
  have key : ∀ x : E × TorusSeq (1 - lam), (fracTorusOp α hα T lam θ hT hT1 hl hl1 Jt f x) n =
      x.2 n - (fracTorusShift α hα T lam θ hT hT1 hl hl1 x.2) n -
        (fracTorusSeed α hα T lam hT hT1 hl hl1 Jt x.1) n -
        (seqOp fun m => (2 : ℝ) • (fracStepFrame α hα (stepScale T lam m) (stepScale_pos hT hl m)
          (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam) (f m)) x.2 n := fun x => rfl
  have e1 : (fracTorusShift α hα T lam θ hT hT1 hl hl1 (R g).2) n = if n = 0 then 0 else
      ((lam ^ dilExponent α / θ) • ((fracStepFrame α hα (stepScale T lam (n - 1 + 1))
        (stepScale_pos hT hl (n - 1 + 1)) (stepScale_le_one hT1 hl hl1 (n - 1 + 1))).pieceFree
          (1 - lam)).comp (pieceEnd (1 - lam)))
        ((R g).2 (n - 1)) := hsh.1 (R g).2 n
  have e2 : (fracTorusSeed α hα T lam hT hT1 hl hl1 Jt (R g).1) n = if n = 0 then
      ((fracStepFrame α hα (stepScale T lam 0) (stepScale_pos hT hl 0)
        (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam)).comp Jt (R g).1 else 0 :=
    (hA.2.2.2 _).1 (R g).1 n
  have e3 := hB.1 (R g).2 n
  have h : (fracTorusOp α hα T lam θ hT hT1 hl hl1 Jt f (R g)) n = g n := by
    have h0 := DFunLike.congr_fun hR g
    exact congrArg (fun y : TorusSeq (1 - lam) => y n) h0
  have h' : (R g).2 n - (fracTorusShift α hα T lam θ hT hT1 hl hl1 (R g).2) n -
      (fracTorusSeed α hα T lam hT hT1 hl hl1 Jt (R g).1) n -
      (seqOp fun m => (2 : ℝ) • (fracStepFrame α hα (stepScale T lam m) (stepScale_pos hT hl m)
        (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam) (f m)) (R g).2 n = g n :=
    (key (R g)).symm.trans h
  rcases n with _ | m
  · simp only [e1, e2, e3, ↓reduceIte, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, sub_zero] at h'
    simp only [↓reduceIte]
    refine Eq.trans ?_ h'
    abel
  · simp only [e1, e2, e3, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, sub_zero] at h'
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    refine Eq.trans ?_ h'
    abel

theorem rpow_small (p y : ℝ) (hp : 0 < p) (hy : 0 < y) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ T : ℝ, 0 ≤ T → T ≤ t₀ → T ^ p ≤ y :=
  ⟨y ^ (1 / p), Real.rpow_pos_of_pos hy _, fun T hT hTt => by
    calc T ^ p ≤ (y ^ (1 / p)) ^ p := Real.rpow_le_rpow hT hTt hp.le
      _ = y := by rw [← Real.rpow_mul hy.le, one_div_mul_cancel hp.ne', Real.rpow_one]⟩

theorem divergenceAt_const_smul {f : Space → Space} (hf : Differentiable ℝ f) (c : ℝ) (x : Space) :
    divergenceAt (c • f) x = c * divergenceAt f x := by
  unfold divergenceAt
  rw [fderiv_const_smul (hf x) c, Finset.mul_sum]
  simp

theorem dilExponent_pos {α : ℝ} (hα : 1 < α) : 0 < dilExponent α := by
  unfold dilExponent
  have h : 3 / (4 * α) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

end FracTorusAssembly.Internal

set_option maxHeartbeats 4000000 in
open Assembly.Internal FracTorusAssembly.Internal in
theorem fracTorusBlowup_of_parts (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4)
    (hFw : Freq.FracFrameworkSpec α ∧ Freq.FracCommutes α) (hOrb : FracProfileOrbit) (hUV : UnitViscosity)
    (hIff : ProfileExistsIff) (hOrbNorm : ScaledOrbitNormStatement) (hOrbBd : ScaledOrbitBoundStatement)
    (hPiece : ScaledProfilePieceStatement) (hTestDense : Freq.TestDense) (hTestSpec : Freq.TestSpanSpec)
    (hBase : FracBaseInverse α) (hR3 : FracR3ChainEq α) (hTor : FracTorusChainEq α hα)
    (hDiff : FracOpDiffBounds α hα) (hNorm : FracOperatorNormBounds α hα) (hLift : TestLiftExists)
    (hTLift : TorusLiftExists) (hComp : FracComparisonSmall α hα) (hLinks : FracApproxLinks α)
    (hRes : FracApproxResidualSmall α hα) (hClose : FracApproxClose α) (hSizes : FracApproxSizes α)
    (hDatum : FracDatumClose α) (hAdd : ToVAdd) (hApprox : FracApproximantExists α)
    (hTS : TransplantSmooth) (hSeq : SeqPerturbation) (hGlue : FracGlueMild α hα)
    (hUnb : FracGlueUnbounded α) (hRI : RightInversePerturb) (hSI : ShellInverseTransfer)
    (hSeqOps : SeqOpSpec) (hP : RotatingFractionalProfileExists α) : FracTorusBlowup α := by
  obtain ⟨U₁, Q₁, a, ν, hprof₁⟩ := (hIff α).1 hP
  obtain ⟨U, Pp, hIL⟩ : ∃ (U : Space → Space) (Pp : Space → ℝ), IsRotatingProfile α a 1 U Pp :=
    ⟨_, _, hUV α hα hα2 a ν U₁ Q₁ hprof₁⟩
  obtain ⟨F, hGX, hKX, hDX⟩ := hFw.1
  have hκ : 0 < dilExponent α := dilExponent_pos hα
  obtain ⟨P', hP0⟩ : ∃ x : ℝ, 0 < x := ⟨1, one_pos⟩
  have horb0 := hOrb α hα hα2 a U Pp hIL F hGX hKX hDX P' hP0
  have hcomm := hFw.2 F hGX hKX hDX (axialRotation (-(a * P')))
  obtain ⟨c, hc, hcw⟩ := hOrbNorm Freq.X (dilExponent α) hκ F _ hcomm _ P' horb0
  obtain ⟨Mw, hMw⟩ := hOrbBd Freq.X (dilExponent α) hκ F _ _ P' horb0
  have hKc : 0 < fracStepCK α hα := (fracStepCK_spec α hα).1
  have hCK : 0 ≤ F.CK := by
    have h3 : 0 ≤ F.CK * (1 : ℝ) ^ (-(3 / 4 : ℝ)) := (norm_nonneg _).trans (F.K_bound 1 one_pos le_rfl)
    rwa [Real.one_rpow, mul_one] at h3
  obtain ⟨k, θ, Vs, J, R0, hk, hL12, hθ, hθ', hθ1, hfd, hJ, hR0⟩ :=
    hBase F _ hcomm _ P' horb0 Freq.testSpan hTestDense (1 / 2) (by norm_num)
  have := hfd
  have : CompleteSpace Vs := FiniteDimensional.complete ℝ Vs
  have hlam0 : 0 < (Real.exp (-(P' / k))) := Real.exp_pos _
  have hlam1 : (Real.exp (-(P' / k))) < 1 :=
    (Real.exp_lt_exp.2 (neg_neg_of_pos (div_pos hP0 (Nat.cast_pos.2 hk)))).trans_eq Real.exp_zero
  have hL0 : 0 < 1 - (Real.exp (-(P' / k))) := by linarith
  have hL1 : 1 - (Real.exp (-(P' / k))) ≤ 1 := by linarith
  have hLq : (1 - (Real.exp (-(P' / k)))) ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hL0.le hL1 (by norm_num)
  have hLq0 : 0 ≤ (1 - (Real.exp (-(P' / k)))) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hL0.le _
  have hθ0 : 0 < θ := lt_of_le_of_lt (Real.rpow_nonneg hlam0.le _) hθ
  obtain ⟨qq, hqq⟩ : ∃ x : ℝ, x = (Real.exp (-(P' / k))) ^ dilExponent α / θ := ⟨_, rfl⟩
  have hq0 : 0 ≤ qq := hqq ▸ div_nonneg (Real.rpow_nonneg hlam0.le _) hθ0.le
  have hq1 : qq < 1 := hqq ▸ (div_lt_one hθ0).2 hθ
  have hiq : 0 ≤ (1 - qq)⁻¹ := inv_nonneg.2 (by linarith)
  obtain ⟨bJ, hbJ, ⟨ψ₁⟩⟩ := hLift Vs (J.comp Vs.subtypeL) (fun e => hJ _)
  obtain ⟨Ts, Ms, hTs, hsz⟩ := hSizes a U Pp (Real.exp (-(P' / k))) c hIL hlam0 hlam1 hc (fun s => hcw s)
  obtain ⟨Kres, hKres0, hKres⟩ := hRes a U Pp (Real.exp (-(P' / k))) θ hlam0 hlam1 hIL hθ'
  obtain ⟨T₁, hT₁, CJ, hCJ0, hCJ⟩ := uniform_of_basis (E := Vs) (Y := V)
    (fun T e => (simScale α T ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α T) (ψ₁.field e))) (fun e => by
      obtain ⟨Td, hTd, hd⟩ := hDatum a U Pp (Real.exp (-(P' / k))) bJ 1 (ψ₁.field e) hIL hlam0 hlam1 (ψ₁.isTest e)
        (ψ₁.support e) hbJ one_pos
      refine ⟨min Td Ts, lt_min hTd hTs,
        ‖Freq.embedX (ψ₁.field e) - Freq.embedX (rotatingSlice a U 0)‖ + 1 + Ms, fun T hT hT' => ?_⟩
      have h1 := hd T hT (lt_of_lt_of_le hT' (min_le_left _ _))
      have h2 := (norm_extendPiece_le (fracApproxPiece α a U T (Real.exp (-(P' / k))) 0) 0).trans
        ((hsz T hT (lt_of_lt_of_le hT' (min_le_right _ _)) 0).1)
      have h3 := norm_sub_norm_le ((simScale α T ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α T) (ψ₁.field e)))
        (extendPiece (fracApproxPiece α a U T (Real.exp (-(P' / k))) 0) 0)
      linarith)
  obtain ⟨Cn, hCn0, hNB1, hNB2, hNR1, hNR2, hShift1, hShift2⟩ := hNorm
  obtain ⟨M0, hM0⟩ : ∃ x : ℝ, x = Real.exp (dilExponent α * (P' / k)) * Mw := ⟨_, rfl⟩
  have hM00 : 0 ≤ M0 := hM0 ▸ mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hMw 0))
  have hprof : ∀ n, ‖F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P' k n‖ ≤ M0 := fun n =>
    hM0 ▸ (hPiece Freq.X (dilExponent α) hκ F _ hcomm _ P' horb0 k hk n).2.2.2.2 Mw hMw
  obtain ⟨Cstb, hCstb⟩ : ∃ x : ℝ, x = 1 + (2 * ‖R0‖) * (Cn * (M0 + 1)) * (1 + Cn) := ⟨_, rfl⟩
  have hCstb0 : 0 ≤ Cstb := hCstb ▸ add_nonneg zero_le_one (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two
    (R0.opNorm_nonneg)) (mul_nonneg hCn0 (add_nonneg hM00 zero_le_one))) (add_nonneg zero_le_one hCn0))
  obtain ⟨C3, hC3⟩ : ∃ x : ℝ, x = (1 - qq)⁻¹ * (1 + (Cn * (M0 + 1) + CJ + 1) * 2 * Cstb * Cn * (1 - qq)⁻¹) :=
    ⟨_, rfl⟩
  have hA0 : 0 ≤ Cn * (M0 + 1) + CJ + 1 :=
    add_nonneg (add_nonneg (mul_nonneg hCn0 (add_nonneg hM00 zero_le_one)) hCJ0) zero_le_one
  have hC30 : 0 ≤ C3 := hC3 ▸ mul_nonneg hiq (add_nonneg zero_le_one
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA0 zero_le_two) hCstb0) hCn0) hiq))
  obtain ⟨ε, hε0, hε1, hεs⟩ := exists_small (8 * F.CK * ‖R0‖ + 16 * fracStepCK α hα * C3) (1 / 2) (by norm_num)
  have hε16 : 0 ≤ ε * (16 * fracStepCK α hα * C3) :=
    mul_nonneg hε0.le (mul_nonneg (mul_nonneg (by norm_num) hKc.le) hC30)
  obtain ⟨bA, hbA, A₀, hA₀⟩ := hApprox F (axialRotation (-(a * P'))) a U Pp P' hcomm horb0 hIL k hk ε hε0
  have hb : 0 < max bJ bA := lt_max_of_lt_left hbJ
  obtain ⟨A, hA⟩ : ∃ A : Approximant (MildFramework.stepLength P' k) (max bJ bA),
      ∀ n, ‖A.r3Piece n - F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P' k n‖ ≤ ε :=
    ⟨enlargeApprox A₀ (le_max_right bJ bA), hA₀⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : TestLift Vs (J.comp Vs.subtypeL) (max bJ bA), ψ.field = ψ₁.field :=
    ⟨enlargeLift ψ₁ (le_max_left bJ bA), rfl⟩
  have hAM : ∀ n, ‖A.r3Piece n‖ ≤ M0 + 1 := fun n => by
    have h1 := norm_sub_norm_le (A.r3Piece n) (F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P' k n)
    linarith only [h1, hA n, hprof n, hε1]
  have hd1 := hDiff.1 F P' k θ ε Vs (J.comp Vs.subtypeL) A.r3Piece
    (F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P' k) hL0 hL1 hA
  obtain ⟨Rf, hRf, hRfn⟩ := hRI (Vs × R3Seq (1 - (Real.exp (-(P' / k))))) (R3Seq (1 - (Real.exp (-(P' / k)))))
    (fracR3Op F P' k θ (J.comp Vs.subtypeL) (F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P' k))
    (fracR3Op F P' k θ (J.comp Vs.subtypeL) A.r3Piece) R0 ‖R0‖ hR0 le_rfl (by
      have h1 := mul_le_mul_of_nonneg_right hd1 (R0.opNorm_nonneg)
      have h2 : 8 * F.CK * (1 - (Real.exp (-(P' / k)))) ^ (1 / 4 : ℝ) * ε * ‖R0‖ ≤ ε * (8 * F.CK * ‖R0‖) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg hCK hε0.le) (R0.opNorm_nonneg)) (sub_nonneg.2 hLq)
        nlinarith only [this]
      linarith only [h1, h2, hεs, hε16])
  have hch := hR3 F hKX P' k θ (max bJ bA) Vs (J.comp Vs.subtypeL) A hL0 hL1
  have hRf' : (chainOp (fracR3Shift F P' k θ) (fracR3Seed F P' k (J.comp Vs.subtypeL)) (fracR3Lambda α A)
      (r3Restrict _ (max bJ bA))).comp Rf = ContinuousLinearMap.id ℝ _ :=
    (congrArg (fun X => ContinuousLinearMap.comp X Rf) hch).trans hRf
  have hBn := hNB1 (1 - (Real.exp (-(P' / k)))) (max bJ bA) (M0 + 1) A hL0 hL1 hAM
  have hRrn := hNR1 (1 - (Real.exp (-(P' / k)))) (max bJ bA) hL0
  obtain ⟨Cst, hCst⟩ : ∃ x : ℝ, x = 1 + 2 * ‖R0‖ * ‖fracR3Lambda α A‖ * (1 + ‖r3Restrict (1 - (Real.exp (-(P' / k)))) (max bJ bA)‖) :=
    ⟨_, rfl⟩
  have hCst1 : 1 ≤ Cst := hCst ▸ le_add_of_nonneg_right (by positivity)
  have hCstle : Cst ≤ Cstb := by
    rw [hCst, hCstb]
    exact mono3 (mul_nonneg zero_le_two (R0.opNorm_nonneg)) (norm_nonneg _) hBn (by positivity)
      (by linarith only [hRrn])
  obtain ⟨δ, hδ⟩ : ∃ x : ℝ, x = 1 / (4 * Cst) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδ ▸ by positivity
  have hδc : 4 * δ * (1 + 2 * ‖R0‖ * ‖fracR3Lambda α A‖ * (1 + ‖r3Restrict (1 - (Real.exp (-(P' / k)))) (max bJ bA)‖)) ≤ 1 := by
    rw [← hCst, hδ]; apply le_of_eq; field_simp
  obtain ⟨T₀c, hT₀c, hcmp⟩ := hComp F hKX hGX hDX P' k θ (max bJ bA) Vs (J.comp Vs.subtypeL) ψ A hlam0
    hlam1.le hP0 hk hL12 hθ hθ1 hb δ hδ0
  obtain ⟨ϱ, hϱ0, -, hϱs⟩ := exists_small (512 * C3 ^ 2 * fracStepCK α hα) (1 / 2) (by norm_num)
  obtain ⟨η, hη0, -, hηs⟩ := exists_small (256 * C3 ^ 2 * fracStepCK α hα * Kres) (1 / 2) (by norm_num)
  obtain ⟨x0, hx0, hdx⟩ := hTestDense.exists_dist_lt (Freq.embedX (rotatingSlice a U 0)) hϱ0
  obtain ⟨ψ₀, hψ₀, hψ₀e⟩ := hTestSpec x0 hx0
  have hclose0 : ‖Freq.embedX ψ₀ - Freq.embedX (rotatingSlice a U 0)‖ ≤ ϱ := by
    rw [hψ₀e, ← dist_eq_norm, dist_comm]; exact hdx.le
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hψ₀.2.1.isCompact.isBounded
  have hb₀ : 0 < max r 1 := lt_max_of_lt_right one_pos
  have hsupp0 : tsupport ψ₀ ⊆ Metric.closedBall 0 (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨Td, hTd, hdat⟩ := hDatum a U Pp (Real.exp (-(P' / k))) (max r 1) ϱ ψ₀ hIL hlam0 hlam1 hψ₀ hsupp0 hb₀ hϱ0
  obtain ⟨Tcl, hTcl, hcl⟩ := hClose F hDX a U Pp P' k (max bJ bA) ε ε A hIL hP0 hk hb hε0 hA
  have hB' : 0 < max (max bJ bA) (max r 1) := lt_max_of_lt_left hb
  have hα0 : 0 < α := by linarith
  obtain ⟨tη, htη, hηT⟩ := rpow_small (1 / (4 * α)) η (by positivity) hη0
  obtain ⟨tb, htb, hbT⟩ := rpow_small (1 / α) ((1 / (8 * max (max bJ bA) (max r 1))) ^ 2) (by positivity)
    (by positivity)
  obtain ⟨m, hm⟩ : ∃ x : ℝ, x = min (min (min T₀c Tcl) (min Ts Td)) (min (min T₁ 1) (min tη tb)) := ⟨_, rfl⟩
  have hm0 : 0 < m := hm ▸ lt_min (lt_min (lt_min hT₀c hTcl) (lt_min hTs hTd))
    (lt_min (lt_min hT₁ one_pos) (lt_min htη htb))
  have hT : 0 < m / 2 := half_pos hm0
  have hTm : m / 2 < m := half_lt_self hm0
  have hm1 : m ≤ min (min T₀c Tcl) (min Ts Td) := hm ▸ min_le_left _ _
  have hm2 : m ≤ min (min T₁ 1) (min tη tb) := hm ▸ min_le_right _ _
  have hTc : m / 2 < T₀c := lt_of_lt_of_le hTm (hm1.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hTl : m / 2 < Tcl := lt_of_lt_of_le hTm (hm1.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hTs' : m / 2 < Ts := lt_of_lt_of_le hTm (hm1.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hTd' : m / 2 < Td := lt_of_lt_of_le hTm (hm1.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hT1' : m / 2 < T₁ := lt_of_lt_of_le hTm (hm2.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hT1 : m / 2 ≤ 1 := (lt_of_lt_of_le hTm (hm2.trans ((min_le_left _ _).trans (min_le_right _ _)))).le
  have hT4 : (m / 2) ^ (1 / (4 * α)) ≤ η :=
    hηT _ hT.le (lt_of_lt_of_le hTm (hm2.trans ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hTb : simScale α (m / 2) ≤ (1 / (8 * max (max bJ bA) (max r 1))) ^ 2 :=
    hbT _ hT.le (lt_of_lt_of_le hTm (hm2.trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hsim0 : 0 < simScale α (m / 2) := Real.rpow_pos_of_pos hT _
  have hsim1 : simScale α (m / 2) ≤ 1 := Real.rpow_le_one hT.le hT1 (by positivity)
  have hsq : Real.sqrt (simScale α (m / 2)) * max (max bJ bA) (max r 1) ≤ 1 / 8 := by
    have h1 : Real.sqrt (simScale α (m / 2)) ≤ 1 / (8 * max (max bJ bA) (max r 1)) := by
      rw [show 1 / (8 * max (max bJ bA) (max r 1)) = Real.sqrt ((1 / (8 * max (max bJ bA) (max r 1))) ^ 2)
        from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hTb
    calc Real.sqrt (simScale α (m / 2)) * max (max bJ bA) (max r 1)
        ≤ 1 / (8 * max (max bJ bA) (max r 1)) * max (max bJ bA) (max r 1) :=
          mul_le_mul_of_nonneg_right h1 hB'.le
      _ = 1 / 8 := by field_simp
  have hsqb : Real.sqrt (simScale α (m / 2)) * max bJ bA ≤ 1 / 8 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg _)) hsq
  have hsqb0 : Real.sqrt (simScale α (m / 2)) * max r 1 ≤ 1 / 8 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)) hsq
  obtain ⟨Jt, hJt⟩ := hTLift Vs (J.comp Vs.subtypeL) (max bJ bA) ψ (simScale α (m / 2)) hb hsim0 hsim1 hsqb
  have hJtn : ‖Jt‖ ≤ CJ := hCJ (m / 2) hT hT1' Jt (fun e => by rw [hJt e, hψ])
  have hGt := (norm_fracTorusSeed_le hSeqOps α hα (m / 2) (Real.exp (-(P' / k))) hT hT1 hlam0 hlam1.le hlam1 Jt).trans hJtn
  obtain ⟨c1, c2⟩ := hcmp (m / 2) hT hT1 hTc Jt hJt
  have hS1 : ‖fracR3Shift F P' k θ‖ ≤ qq := hqq ▸ hShift1 F P' k θ hP0 hk hθ0
  have hS2 : ‖fracTorusShift α hα (m / 2) (Real.exp (-(P' / k))) θ hT hT1 hlam0 hlam1.le‖ ≤ qq :=
    hqq ▸ hShift2 (m / 2) (Real.exp (-(P' / k))) θ hT hT1 hlam0 hlam1.le hθ0
  obtain ⟨R', hR', hR'n⟩ := hSI Vs (R3Seq (1 - (Real.exp (-(P' / k))))) (TorusSeq (1 - (Real.exp (-(P' / k))))) (ShellSeq (1 - (Real.exp (-(P' / k)))))
    (fracR3Shift F P' k θ) (fracR3Seed F P' k (J.comp Vs.subtypeL)) (fracR3Lambda α A) (r3Restrict _ (max bJ bA))
    (fracTorusShift α hα (m / 2) (Real.exp (-(P' / k))) θ hT hT1 hlam0 hlam1.le)
    (fracTorusSeed α hα (m / 2) (Real.exp (-(P' / k))) hT hT1 hlam0 hlam1.le Jt)
    (fracTorusLambda α A (m / 2) (Real.exp (-(P' / k)))) (fracTorusRestrict α _ (max bJ bA) (m / 2) (Real.exp (-(P' / k)))) Rf qq (2 * ‖R0‖) δ
    hq0 hq1 hS1 hS2 hRf' hRfn c1 c2 hδc
  have hBt := hNB2 (max bJ bA) (m / 2) (Real.exp (-(P' / k))) (M0 + 1) A hT hT1 hlam0 hlam1 hb hsqb hAM
  have hRt := hNR2 (max bJ bA) (m / 2) (Real.exp (-(P' / k))) hT hT1 hlam0 hlam1 hb hsqb
  have hR'C3 : ‖R'‖ ≤ C3 := by
    have hBG : ‖fracTorusLambda α A (m / 2) (Real.exp (-(P' / k)))‖ +
        ‖fracTorusSeed α hα (m / 2) (Real.exp (-(P' / k))) hT hT1 hlam0 hlam1.le Jt‖ + 1 ≤ Cn * (M0 + 1) + CJ + 1 := by
      linarith only [hBt, hGt]
    have hBG0 : 0 ≤ ‖fracTorusLambda α A (m / 2) (Real.exp (-(P' / k)))‖ +
        ‖fracTorusSeed α hα (m / 2) (Real.exp (-(P' / k))) hT hT1 hlam0 hlam1.le Jt‖ + 1 := by positivity
    have hB3 := bound_mono hiq hBG0 hBG (by linarith only [hCst1]) hCstle (norm_nonneg _) hRt
    subst hCst hC3
    exact hR'n.trans hB3
  have hch2 := hTor (m / 2) (Real.exp (-(P' / k))) θ (max bJ bA) hT hT1 hlam0 hlam1.le Vs Jt A hlam1 hb hsqb
  have hR'' := (congrArg (fun X => ContinuousLinearMap.comp X R') hch2).symm.trans hR'
  have hd2 := hDiff.2 (m / 2) (Real.exp (-(P' / k))) θ (ε + ε) hT hT1 hlam0 hlam1.le Vs Jt (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))))
    (fun n => A.torusPiece (simScale α (stepScale (m / 2) (Real.exp (-(P' / k))) n)) n) hlam1 (fun n => hcl (m / 2) hT hTl n)
  obtain ⟨R2, hR2, hR2n⟩ := hRI (Vs × TorusSeq (1 - (Real.exp (-(P' / k))))) (TorusSeq (1 - (Real.exp (-(P' / k)))))
    (fracTorusOp α hα (m / 2) (Real.exp (-(P' / k))) θ hT hT1 hlam0 hlam1.le Jt
      (fun n => A.torusPiece (simScale α (stepScale (m / 2) (Real.exp (-(P' / k))) n)) n))
    (fracTorusOp α hα (m / 2) (Real.exp (-(P' / k))) θ hT hT1 hlam0 hlam1.le Jt (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))))) R' C3 hR''
    hR'C3 (by
      have h1 := mul_le_mul_of_nonneg_right hd2 hC30
      have h2 : 8 * fracStepCK α hα * (1 - (Real.exp (-(P' / k)))) ^ (1 / 4 : ℝ) * (ε + ε) * C3 ≤
          ε * (16 * fracStepCK α hα * C3) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg hKc.le hε0.le) hC30) (sub_nonneg.2 hLq)
        nlinarith only [this]
      have h3 : 0 ≤ ε * (8 * F.CK * ‖R0‖) :=
        mul_nonneg hε0.le (mul_nonneg (mul_nonneg (by norm_num) hCK) R0.opNorm_nonneg)
      linarith only [h1, h2, hεs, h3])
  have heq := frac_torus_seq_equation hSeqOps α hα (m / 2) (Real.exp (-(P' / k))) θ hT hT1 hlam0 hlam1.le hlam1 Jt
    (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k)))) Ms (fun n => (hsz (m / 2) hT hTs' n).1) R2 hR2
  obtain ⟨ξ, hξ⟩ : ∃ x : V, x = (simScale α (m / 2) ^ (1 / 4 : ℝ)) •
      toV (transplantField (simScale α (m / 2)) ψ₀) - extendPiece (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))) 0) 0 :=
    ⟨_, rfl⟩
  have hξn : ‖ξ‖ ≤ ϱ + ϱ := by
    subst hξ; exact (hdat (m / 2) hT hTd').trans (by linarith only [hclose0])
  have hR2sq : ‖R2‖ ^ 2 ≤ (2 * C3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR2n 2
  have hsmall : 64 * ‖R2‖ ^ 2 * fracStepCK α hα * (1 - (Real.exp (-(P' / k)))) ^ (1 / 4 : ℝ) *
      (Kres * (m / 2) ^ (1 / (4 * α)) + ‖ξ‖) ≤ 1 := by
    have a2 : Kres * (m / 2) ^ (1 / (4 * α)) + ‖ξ‖ ≤ Kres * η + (ϱ + ϱ) :=
      add_le_add (mul_le_mul_of_nonneg_left hT4 hKres0) hξn
    have a3 : 0 ≤ Kres * (m / 2) ^ (1 / (4 * α)) + ‖ξ‖ :=
      add_nonneg (mul_nonneg hKres0 (Real.rpow_nonneg hT.le _)) (norm_nonneg _)
    have a4 : 64 * ‖R2‖ ^ 2 * fracStepCK α hα ≤ 64 * (2 * C3) ^ 2 * fracStepCK α hα :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR2sq (by norm_num)) hKc.le
    have a5 : 0 ≤ 64 * (2 * C3) ^ 2 * fracStepCK α hα := mul_nonneg (by positivity) hKc.le
    calc 64 * ‖R2‖ ^ 2 * fracStepCK α hα * (1 - (Real.exp (-(P' / k)))) ^ (1 / 4 : ℝ) *
          (Kres * (m / 2) ^ (1 / (4 * α)) + ‖ξ‖)
        ≤ 64 * (2 * C3) ^ 2 * fracStepCK α hα * 1 * (Kres * η + (ϱ + ϱ)) :=
          mul_le_mul (mul_le_mul a4 hLq hLq0 a5) a2 a3 (by simpa using a5)
      _ = η * (256 * C3 ^ 2 * fracStepCK α hα * Kres) + ϱ * (512 * C3 ^ 2 * fracStepCK α hα) := by ring
      _ ≤ 1 := by linarith only [hηs, hϱs]
  obtain ⟨e, z, hz, -, hmild, hz0, hlk⟩ := hSeq V Vs
    (fun n => (fracStepFrame α hα (stepScale (m / 2) (Real.exp (-(P' / k))) n) (stepScale_pos hT hlam0 n)
      (stepScale_le_one hT1 hlam0 hlam1.le n))) (1 - (Real.exp (-(P' / k)))) θ ((Real.exp (-(P' / k))) ^ dilExponent α)
    (fracStepCK α hα) Ms (Kres * (m / 2) ^ (1 / (4 * α))) (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))))
    (fun n => fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))) n -
      (fracStepFrame α hα (stepScale (m / 2) (Real.exp (-(P' / k))) n) (stepScale_pos hT hlam0 n)
        (stepScale_le_one hT1 hlam0 hlam1.le n)).pieceFree (1 - (Real.exp (-(P' / k))))
          (extendPiece (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))) n) 0) -
      (fracStepFrame α hα (stepScale (m / 2) (Real.exp (-(P' / k))) n) (stepScale_pos hT hlam0 n)
        (stepScale_le_one hT1 hlam0 hlam1.le n)).pieceBil (1 - (Real.exp (-(P' / k))))
          (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))) n) (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))) n))
    Jt R2 ξ hL0 hL1 hθ0 hθ1 hKc.le (fun n => le_rfl) (fun n => (hsz (m / 2) hT hTs' n).1)
    (fun n => (hLinks a U Pp (m / 2) (Real.exp (-(P' / k))) hIL hT hT1 hlam0 hlam1 n).2) (fun n => by abel)
    (fun n => hKres (m / 2) hT hT1 n) heq hsmall
  have hgl := hGlue (m / 2) (Real.exp (-(P' / k))) hT hT1 hlam0 hlam1
    (fun n => fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))) n + θ ^ n • z n) hmild hlk
  have hunb := hUnb (m / 2) (Real.exp (-(P' / k))) θ (c / 2) _ (fun n => fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))) n + θ ^ n • z n)
    (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k)))) z hT hlam0 hlam1 hθ0 hθ1 (half_pos hc)
    (fun n s => (hsz (m / 2) hT hTs' n).2 s) hz (fun n => rfl)
  have hts0 := hTS ψ₀ (simScale α (m / 2)) (max r 1) hψ₀.1 hψ₀.2.2 ⟨hsim0, hsim1, hb₀, hsqb0⟩ hsupp0
  have htse := hTS (ψ.field e) (simScale α (m / 2)) (max bJ bA) (ψ.isTest e).1 (ψ.isTest e).2.2
    ⟨hsim0, hsim1, hb, hsqb⟩ (ψ.support e)
  have hsum := hAdd _ _ hts0.1 htse.1 hts0.2.1 htse.2.1 hts0.2.2.1 htse.2.2.1
  obtain ⟨cT, hcT⟩ : ∃ x : ℝ, x = (m / 2) ^ (-dilExponent α) * simScale α (m / 2) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  refine ⟨cT • (transplantField (simScale α (m / 2)) ψ₀ + transplantField (simScale α (m / 2)) (ψ.field e)),
    (hts0.1.add htse.1).const_smul cT,
    fun i x => by simp only [Pi.smul_apply, Pi.add_apply, hts0.2.1 i x, htse.2.1 i x], fun x => ?_, m / 2, hT,
    fracGluePieces α (m / 2) (Real.exp (-(P' / k))) (fun n => fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))) n + θ ^ n • z n), ?_, hgl.1, hunb⟩
  · rw [divergenceAt_const_smul (f := transplantField (simScale α (m / 2)) ψ₀ +
        transplantField (simScale α (m / 2)) (ψ.field e)) ((hts0.1.add htse.1).differentiable (by simp)),
      divergenceAt_add (hts0.1.differentiable (by simp)) (htse.1.differentiable (by simp)),
      hts0.2.2.1 x, htse.2.2.1 x, add_zero, mul_zero]
  · have h0 := hgl.2 0 0 ⟨le_rfl, hL0.le⟩
    have hs0 : stepStart (m / 2) (Real.exp (-(P' / k))) 0 + stepScale (m / 2) (Real.exp (-(P' / k))) 0 * 0 = 0 := by simp [stepStart, stepScale]
    have hsc : stepScale (m / 2) (Real.exp (-(P' / k))) 0 = m / 2 := by simp [stepScale]
    rw [hs0, hsc] at h0
    rw [Internal.TestLift.toV_smul, hsum]
    refine h0.trans ?_
    beta_reduce
    have hx : extendPiece (fracApproxPiece α a U (m / 2) (Real.exp (-(P' / k))) 0 + θ ^ 0 • z 0) 0 =
        (simScale α (m / 2) ^ (1 / 4 : ℝ)) • (toV (transplantField (simScale α (m / 2)) ψ₀) +
          toV (transplantField (simScale α (m / 2)) (ψ.field e))) := by
      simp only [extendPiece_add, hz0, hξ, hJt e, pow_zero, one_smul, smul_add]
      abel
    rw [hx, smul_smul, hcT]

end Breakdown.Periodic
