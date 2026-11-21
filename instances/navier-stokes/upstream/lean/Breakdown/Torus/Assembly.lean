import Breakdown.Torus.StatementsApproxSteps
import Breakdown.Torus.StatementsSteps
import Breakdown.Torus.Reduction
import Breakdown.Profile.StatementsEmbed
import Breakdown.Transfer.Exports

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def IsFreqTrRealization (Rlz : Realization Freq.X) : Prop :=
  Rlz.F.K = Freq.bilinX ∧ Rlz.F.G = Freq.heatX ∧ Rlz.F.D = Freq.dilX ∧ Rlz.rot = Freq.rotX ∧
    Rlz.embed = Freq.embedX ∧ Rlz.test = Freq.testSpan

namespace Assembly.Internal

theorem extendPiece_add {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ}
    (f g : Piece X L) (t : ℝ) : extendPiece (f + g) t = extendPiece f t + extendPiece g t := by
  unfold extendPiece
  split_ifs with h
  · simp [Set.IccExtend_apply]
  · simp

theorem norm_extendPiece_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ}
    (f : Piece X L) (t : ℝ) : ‖extendPiece f t‖ ≤ ‖f‖ := by
  unfold extendPiece
  split_ifs with h
  · rw [Set.IccExtend_apply]
    exact ContinuousMap.norm_coe_le_norm f _
  · simp

theorem exists_small (K δ : ℝ) (hδ : 0 < δ) : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * K ≤ δ := by
  refine ⟨min 1 (δ / (|K| + 1)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  have h1 : min 1 (δ / (|K| + 1)) ≤ δ / (|K| + 1) := min_le_right _ _
  have h0 : 0 ≤ min 1 (δ / (|K| + 1)) := le_of_lt (lt_min one_pos (by positivity))
  calc min 1 (δ / (|K| + 1)) * K ≤ min 1 (δ / (|K| + 1)) * |K| :=
        mul_le_mul_of_nonneg_left (le_abs_self K) h0
    _ ≤ δ / (|K| + 1) * |K| := mul_le_mul_of_nonneg_right h1 (abs_nonneg K)
    _ ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg K]

theorem uniform_of_basis {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : ℝ → E → Y)
    (h : ∀ e, ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ B : ℝ, ∀ T, 0 < T → T < T₀ → ‖g T e‖ ≤ B) :
    ∃ T₁ : ℝ, 0 < T₁ ∧ ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ T, 0 < T → T < T₁ → ∀ Jt : E →L[ℝ] Y,
      (∀ e, Jt e = g T e) → ‖Jt‖ ≤ CJ := by
  classical
  let v := Module.finBasis ℝ E
  obtain ⟨C, hC, hv⟩ := v.exists_opNorm_le (F := Y)
  choose T₀ hT₀ B hB using fun i => h (v i)
  let s : Finset ℝ := insert 1 (Finset.univ.image T₀)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs, ?_, C * ∑ i, |B i|, by positivity, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hT₀ i
  · intro T hT hT1 Jt hJ
    refine hv (by positivity) fun i => ?_
    rw [hJ]
    have hi : s.min' hs ≤ T₀ i := Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
    calc ‖g T (v i)‖ ≤ B i := hB i T hT (lt_of_lt_of_le hT1 hi)
      _ ≤ |B i| := le_abs_self _
      _ ≤ ∑ j, |B j| := Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

theorem divergenceAt_add {f g : Space → Space} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (x : Space) : divergenceAt (f + g) x = divergenceAt f x + divergenceAt g x := by
  unfold divergenceAt
  rw [fderiv_add (hf x) (hg x), ← Finset.sum_add_distrib]
  simp

def enlargeApprox {L b b' : ℝ} (A : Approximant L b) (h : b ≤ b') : Approximant L b' :=
  { A with support := fun n l => (A.support n l).trans (Metric.closedBall_subset_closedBall h) }

def enlargeLift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {J : E →L[ℝ] Freq.X} {b b' : ℝ}
    (ψ : TestLift E J b) (h : b ≤ b') : TestLift E J b' :=
  { ψ with support := fun e => (ψ.support e).trans (Metric.closedBall_subset_closedBall h) }

theorem norm_torusSeed_le (hS : SeqOpSpec) (hK : KernelSharpBound) (T lam : ℝ) (hT : 0 < T) (hT1 : T ≤ 1)
    (hl : 0 < lam) (hl1 : lam ≤ 1) (hl1' : lam < 1) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Jt : E →L[ℝ] V) : ‖torusSeed hK T lam hT hT1 hl hl1 Jt‖ ≤ ‖Jt‖ := by
  unfold torusSeed
  have h0 := (hS E (Piece V (1 - lam)) (fun _ => 0) 0 (by simp) le_rfl).2.2.2
    (((stepFrame hK (stepScale T lam 0) (stepScale_pos hT hl 0)
      (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam)).comp Jt)
  refine h0.2.trans ?_
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hF := (pieceOperator V (stepFrame hK (stepScale T lam 0) (stepScale_pos hT hl 0)
      (stepScale_le_one hT1 hl hl1 0)) (1 - lam) (by linarith)).2.2.2
  calc _ ≤ 1 * ‖Jt‖ := mul_le_mul_of_nonneg_right hF (norm_nonneg _)
    _ = ‖Jt‖ := one_mul _


theorem torus_seq_equation (hS : SeqOpSpec) (hK : KernelSharpBound) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1)
    (hl : 0 < lam) (hl1 : lam ≤ 1) (hl1' : lam < 1) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Jt : E →L[ℝ] V) (f : ℕ → Piece V (1 - lam)) (Mf : ℝ) (hf : ∀ n, ‖f n‖ ≤ Mf)
    (R : TorusSeq (1 - lam) →L[ℝ] E × TorusSeq (1 - lam))
    (hR : (torusOp hK T lam θ hT hT1 hl hl1 Jt f).comp R = ContinuousLinearMap.id ℝ _) :
    ∀ g n, (R g).2 n - (2 : ℝ) • (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam) (f n) ((R g).2 n) -
      (if n = 0 then (stepFrame hK (stepScale T lam 0) (stepScale_pos hT hl 0)
          (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam) (Jt (R g).1)
        else (lam ^ (1 / 4 : ℝ) / θ) • (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
          (stepScale_le_one hT1 hl hl1 n)).pieceFree (1 - lam) (pieceEnd (1 - lam) ((R g).2 (n - 1)))) = g n := by
  intro g n
  have hL : 0 < 1 - lam := by linarith
  have hKc : 0 < hK.choose := hK.choose_spec.1
  have hbil : ∀ m, ‖(2 : ℝ) • (stepFrame hK (stepScale T lam m) (stepScale_pos hT hl m)
      (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam) (f m)‖ ≤
      ‖(2 : ℝ)‖ * (4 * hK.choose * (1 - lam) ^ (1 / 4 : ℝ) * |Mf|) := by
    intro m
    have hb : ‖(stepFrame hK (stepScale T lam m) (stepScale_pos hT hl m)
        (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam)‖ ≤ 4 * hK.choose * (1 - lam) ^ (1 / 4 : ℝ) :=
      (pieceOperator V (stepFrame hK (stepScale T lam m) (stepScale_pos hT hl m)
        (stepScale_le_one hT1 hl hl1 m)) (1 - lam) hL).2.1 (by linarith)
    have h2 := ContinuousLinearMap.le_opNorm ((stepFrame hK (stepScale T lam m) (stepScale_pos hT hl m)
        (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam)) (f m)
    have h3 : ‖(stepFrame hK (stepScale T lam m) (stepScale_pos hT hl m)
        (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam) (f m)‖ ≤
        4 * hK.choose * (1 - lam) ^ (1 / 4 : ℝ) * |Mf| :=
      h2.trans (mul_le_mul hb ((hf m).trans (le_abs_self _)) (norm_nonneg _) (by positivity))
    exact (norm_smul_le (2 : ℝ) _).trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
  have hA := hS E (Piece V (1 - lam)) (fun _ => 0) 0 (by simp) le_rfl
  have hB := hS (Piece V (1 - lam)) (Piece V (1 - lam)) _ _ hbil (by positivity)
  have hC := hS (Piece V (1 - lam)) (Piece V (1 - lam)) (fun _ => 0)
    (‖lam ^ (1 / 4 : ℝ) / θ‖ * (1 * ‖pieceEnd (X := V) (1 - lam)‖)) (fun _ => by simp; positivity)
    (by positivity)
  have hsh := hC.2.2.1 (fun m => (lam ^ (1 / 4 : ℝ) / θ) •
    ((stepFrame hK (stepScale T lam (m + 1)) (stepScale_pos hT hl (m + 1))
      (stepScale_le_one hT1 hl hl1 (m + 1))).pieceFree (1 - lam)).comp (pieceEnd (1 - lam))) (fun m => by
        refine (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        exact (pieceOperator V (stepFrame hK (stepScale T lam (m + 1)) (stepScale_pos hT hl (m + 1))
          (stepScale_le_one hT1 hl hl1 (m + 1))) (1 - lam) hL).2.2.2)
  have key : ∀ x : E × TorusSeq (1 - lam), (torusOp hK T lam θ hT hT1 hl hl1 Jt f x) n =
      x.2 n - (torusShift hK T lam θ hT hT1 hl hl1 x.2) n - (torusSeed hK T lam hT hT1 hl hl1 Jt x.1) n -
        (seqOp fun m => (2 : ℝ) • (stepFrame hK (stepScale T lam m) (stepScale_pos hT hl m) (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam) (f m)) x.2 n := fun x => rfl
  have e1 : (torusShift hK T lam θ hT hT1 hl hl1 (R g).2) n = if n = 0 then 0 else
      ((lam ^ (1 / 4 : ℝ) / θ) • ((stepFrame hK (stepScale T lam (n - 1 + 1)) (stepScale_pos hT hl (n - 1 + 1)) (stepScale_le_one hT1 hl hl1 (n - 1 + 1))).pieceFree (1 - lam)).comp (pieceEnd (1 - lam)))
        ((R g).2 (n - 1)) := hsh.1 (R g).2 n
  have e2 : (torusSeed hK T lam hT hT1 hl hl1 Jt (R g).1) n = if n = 0 then
      ((stepFrame hK (stepScale T lam 0) (stepScale_pos hT hl 0) (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam)).comp Jt (R g).1 else 0 := (hA.2.2.2 _).1 (R g).1 n
  have e3 := hB.1 (R g).2 n
  have h : (torusOp hK T lam θ hT hT1 hl hl1 Jt f (R g)) n = g n := by
    have h0 := DFunLike.congr_fun hR g
    exact congrArg (fun y : TorusSeq (1 - lam) => y n) h0
  have h' : (R g).2 n - (torusShift hK T lam θ hT hT1 hl hl1 (R g).2) n - (torusSeed hK T lam hT hT1 hl hl1 Jt (R g).1) n - (seqOp fun m => (2 : ℝ) • (stepFrame hK (stepScale T lam m) (stepScale_pos hT hl m) (stepScale_le_one hT1 hl hl1 m)).pieceBil (1 - lam) (f m)) (R g).2 n = g n := (key (R g)).symm.trans h
  rcases n with _ | m
  · simp only [e1, e2, e3, ↓reduceIte, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      sub_zero] at h'
    simp only [↓reduceIte]
    refine Eq.trans ?_ h'
    abel
  · simp only [e1, e2, e3, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, sub_zero] at h'
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    refine Eq.trans ?_ h'
    abel


theorem bound_mono {q a A c Cc d D : ℝ} (hq : 0 ≤ q) (ha0 : 0 ≤ a) (ha : a ≤ A) (hc0 : 0 ≤ c) (hc : c ≤ Cc)
    (hd0 : 0 ≤ d) (hd : d ≤ D) : q * (1 + a * 2 * c * d * q) ≤ q * (1 + A * 2 * Cc * D * q) := by
  refine mul_le_mul_of_nonneg_left ?_ hq
  have h1 : a * c ≤ A * Cc := mul_le_mul ha hc hc0 (ha0.trans ha)
  have h2 : a * c * d ≤ A * Cc * D := mul_le_mul h1 hd hd0 ((mul_nonneg ha0 hc0).trans h1)
  have h3 : a * 2 * c * d * q ≤ A * 2 * Cc * D * q := by
    calc a * 2 * c * d * q = (a * c * d) * (2 * q) := by ring
      _ ≤ (A * Cc * D) * (2 * q) := mul_le_mul_of_nonneg_right h2 (mul_nonneg zero_le_two hq)
      _ = A * 2 * Cc * D * q := by ring
  linarith

theorem mono3 {a x X y Y : ℝ} (ha : 0 ≤ a) (hx0 : 0 ≤ x) (hx : x ≤ X) (hy0 : 0 ≤ y) (hy : y ≤ Y) :
    1 + a * x * y ≤ 1 + a * X * Y := by
  have h1 : x * y ≤ X * Y := mul_le_mul hx hy hy0 (hx0.trans hx)
  have h2 := mul_le_mul_of_nonneg_left h1 ha
  linarith [show a * x * y = a * (x * y) by ring, show a * X * Y = a * (X * Y) by ring]

end Assembly.Internal

set_option maxHeartbeats 4000000 in
open Assembly.Internal in
theorem torusBlowup_of_parts (Rlz : Realization Freq.X) (hRz : IsFreqTrRealization Rlz)
    (hEmb : EmbeddedProfileOrbit) (hOrbNorm : OrbitNormStatement) (hOrbBd : OrbitBoundStatement)
    (hPiece : ProfilePieceStatement) (hTestDense : Freq.TestDense) (hTestSpec : Freq.TestSpanSpec)
    (hBase : BaseInverse) (hR3 : R3ChainEq) (hTor : TorusChainEq) (hDiff : OpDiffBounds)
    (hNorm : OperatorNormBounds) (hLift : TestLiftExists) (hTLift : TorusLiftExists)
    (hComp : ComparisonSmall) (hLinks : ApproxLinks) (hRes : ApproxResidualSmall) (hClose : ApproxClose)
    (hSizes : ApproxSizes) (hDatum : DatumClose) (hAdd : ToVAdd) (hApprox : ApproximantExists)
    (hTS : TransplantSmooth) (hSeq : SeqPerturbation) (hGlue : GlueMild) (hUnb : GlueUnbounded)
    (hRI : RightInversePerturb) (hSI : ShellInverseTransfer) (hSeqOps : SeqOpSpec)
    (hP : PeriodicSimilarityProfileExists) : TorusBlowup := by
  obtain ⟨hKX, hGX, hDX, hrot, hemb, -⟩ := hRz
  obtain ⟨W, q, P, R, C, hP0, hWs, hqs, hres, hdiv, hper, hnz, hdec, hdecq⟩ := hP
  have hIL : IsSimilarityProfile W q C := ⟨hWs, hqs, hres, hdiv, hdec, hdecq⟩
  have horb0 := hEmb Freq.X Rlz W q P R C hP0 hIL hper hnz
  rw [hrot, hemb] at horb0
  have hcomm := Rlz.rot_commutes R
  rw [hrot] at hcomm
  obtain ⟨c, hc, hcw⟩ := hOrbNorm Freq.X Rlz.F (Freq.rotX R) hcomm _ P horb0
  obtain ⟨Mw, hMw⟩ := hOrbBd Freq.X Rlz.F (Freq.rotX R) _ P horb0
  have hK := kernelSharpBound_holds
  have hKc : 0 < hK.choose := hK.choose_spec.1
  have hCK : 0 ≤ Rlz.F.CK := by
    have h3 : 0 ≤ Rlz.F.CK * (1 : ℝ) ^ (-(3 / 4 : ℝ)) := (norm_nonneg _).trans (Rlz.F.K_bound 1 one_pos le_rfl)
    rwa [Real.one_rpow, mul_one] at h3
  obtain ⟨k, θ, Vs, J, R0, hk, hL12, hθ, hθ1, hfd, hJ, hR0⟩ :=
    hBase Rlz.F (Freq.rotX R) hcomm _ P horb0 Freq.testSpan hTestDense (1 / 2) (by norm_num)
  have := hfd
  have : CompleteSpace Vs := FiniteDimensional.complete ℝ Vs
  have hlam0 : 0 < (Real.exp (-(P / k))) := Real.exp_pos _
  have hlam1 : (Real.exp (-(P / k))) < 1 := (Real.exp_lt_exp.2 (neg_neg_of_pos (div_pos hP0 (Nat.cast_pos.2 hk)))).trans_eq Real.exp_zero
  have hL0 : 0 < 1 - (Real.exp (-(P / k))) := by linarith
  have hL1 : 1 - (Real.exp (-(P / k))) ≤ 1 := by linarith
  have hLq : (1 - (Real.exp (-(P / k)))) ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hL0.le hL1 (by norm_num)
  have hLq0 : 0 ≤ (1 - (Real.exp (-(P / k)))) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hL0.le _
  have hθ0 : 0 < θ := lt_of_le_of_lt (Real.rpow_nonneg hlam0.le _) hθ
  obtain ⟨qq, hqq⟩ : ∃ x : ℝ, x = (Real.exp (-(P / k))) ^ (1 / 4 : ℝ) / θ := ⟨_, rfl⟩
  have hq0 : 0 ≤ qq := hqq ▸ div_nonneg (Real.rpow_nonneg hlam0.le _) hθ0.le
  have hq1 : qq < 1 := hqq ▸ (div_lt_one hθ0).2 hθ
  have hiq : 0 ≤ (1 - qq)⁻¹ := inv_nonneg.2 (by linarith)
  obtain ⟨bJ, hbJ, ⟨ψ₁⟩⟩ := hLift Vs (J.comp Vs.subtypeL) (fun e => hJ _)
  obtain ⟨Ts, Ms, hTs, hsz⟩ := hSizes W q C (Real.exp (-(P / k))) c hIL hlam0 hlam1 hc (fun s => hcw s)
  obtain ⟨Kres, hKres0, hKres⟩ := hRes hK W q C (Real.exp (-(P / k))) θ hlam0 hlam1 hIL hθ
  obtain ⟨T₁, hT₁, CJ, hCJ0, hCJ⟩ := uniform_of_basis (E := Vs) (Y := V)
    (fun T e => (T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ₁.field e))) (fun e => by
      obtain ⟨Td, hTd, hd⟩ := hDatum W q C (Real.exp (-(P / k))) bJ 1 (ψ₁.field e) hIL hlam0 hlam1 (ψ₁.isTest e)
        (ψ₁.support e) hbJ one_pos
      refine ⟨min Td Ts, lt_min hTd hTs, ‖Freq.embedX (ψ₁.field e) - Freq.embedX (W 0)‖ + 1 + Ms,
        fun T hT hT' => ?_⟩
      have h1 := hd T hT (lt_of_lt_of_le hT' (min_le_left _ _))
      have h2 := (norm_extendPiece_le (approxPiece W T (Real.exp (-(P / k))) 0) 0).trans
        ((hsz T hT (lt_of_lt_of_le hT' (min_le_right _ _)) 0).1)
      have h3 := norm_sub_norm_le ((T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ₁.field e)))
        (extendPiece (approxPiece W T (Real.exp (-(P / k))) 0) 0)
      linarith)
  obtain ⟨Cn, hCn0, hNB1, hNB2, hNR1, hNR2, hShift1, hShift2⟩ := hNorm
  obtain ⟨M0, hM0⟩ : ∃ x : ℝ, x = Real.exp (P / k / 4) * Mw := ⟨_, rfl⟩
  have hM00 : 0 ≤ M0 := hM0 ▸ mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hMw 0))
  have hprof : ∀ n, ‖Rlz.F.profilePiece (fun s => Freq.embedX (W s)) P k n‖ ≤ M0 := fun n =>
    hM0 ▸ (hPiece Freq.X Rlz.F (Freq.rotX R) hcomm _ P horb0 k hk n).2.2.2.2 Mw hMw
  obtain ⟨Cstb, hCstb⟩ : ∃ x : ℝ, x = 1 + (2 * ‖R0‖) * (Cn * (M0 + 1)) * (1 + Cn) := ⟨_, rfl⟩
  have hCstb0 : 0 ≤ Cstb := hCstb ▸ add_nonneg zero_le_one (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two
    (R0.opNorm_nonneg)) (mul_nonneg hCn0 (add_nonneg hM00 zero_le_one))) (add_nonneg zero_le_one hCn0))
  obtain ⟨C3, hC3⟩ : ∃ x : ℝ, x = (1 - qq)⁻¹ * (1 + (Cn * (M0 + 1) + CJ + 1) * 2 * Cstb * Cn * (1 - qq)⁻¹) :=
    ⟨_, rfl⟩
  have hA0 : 0 ≤ Cn * (M0 + 1) + CJ + 1 :=
    add_nonneg (add_nonneg (mul_nonneg hCn0 (add_nonneg hM00 zero_le_one)) hCJ0) zero_le_one
  have hC30 : 0 ≤ C3 := hC3 ▸ mul_nonneg hiq (add_nonneg zero_le_one
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA0 zero_le_two) hCstb0) hCn0) hiq))
  obtain ⟨ε, hε0, hε1, hεs⟩ := exists_small (8 * Rlz.F.CK * ‖R0‖ + 16 * hK.choose * C3) (1 / 2) (by norm_num)
  have hε16 : 0 ≤ ε * (16 * hK.choose * C3) := mul_nonneg hε0.le (mul_nonneg (mul_nonneg (by norm_num) hKc.le) hC30)
  obtain ⟨bA, hbA, A₀, hA₀⟩ := hApprox Rlz.F R W q C P hcomm horb0 hIL k hk ε hε0
  have hb : 0 < max bJ bA := lt_max_of_lt_left hbJ
  obtain ⟨A, hA⟩ : ∃ A : Approximant (MildFramework.stepLength P k) (max bJ bA),
      ∀ n, ‖A.r3Piece n - Rlz.F.profilePiece (fun s => Freq.embedX (W s)) P k n‖ ≤ ε :=
    ⟨enlargeApprox A₀ (le_max_right bJ bA), hA₀⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : TestLift Vs (J.comp Vs.subtypeL) (max bJ bA), ψ.field = ψ₁.field :=
    ⟨enlargeLift ψ₁ (le_max_left bJ bA), rfl⟩
  have hAM : ∀ n, ‖A.r3Piece n‖ ≤ M0 + 1 := fun n => by
    have h1 := norm_sub_norm_le (A.r3Piece n) (Rlz.F.profilePiece (fun s => Freq.embedX (W s)) P k n)
    linarith only [h1, hA n, hprof n, hε1]
  have hd1 := hDiff.1 Rlz.F P k θ ε Vs (J.comp Vs.subtypeL) A.r3Piece
    (Rlz.F.profilePiece (fun s => Freq.embedX (W s)) P k) hL0 hL1 hA
  obtain ⟨Rf, hRf, hRfn⟩ := hRI (Vs × R3Seq (1 - (Real.exp (-(P / k))))) (R3Seq (1 - (Real.exp (-(P / k)))))
    (r3Op Rlz.F P k θ (J.comp Vs.subtypeL) (Rlz.F.profilePiece (fun s => Freq.embedX (W s)) P k))
    (r3Op Rlz.F P k θ (J.comp Vs.subtypeL) A.r3Piece) R0 ‖R0‖ hR0 le_rfl (by
      have h1 := mul_le_mul_of_nonneg_right hd1 (R0.opNorm_nonneg)
      have h2 : 8 * Rlz.F.CK * (1 - (Real.exp (-(P / k)))) ^ (1 / 4 : ℝ) * ε * ‖R0‖ ≤ ε * (8 * Rlz.F.CK * ‖R0‖) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg hCK hε0.le) (R0.opNorm_nonneg)) (sub_nonneg.2 hLq)
        nlinarith only [this]
      linarith only [h1, h2, hεs, hε16])
  have hch := hR3 Rlz.F hKX P k θ (max bJ bA) Vs (J.comp Vs.subtypeL) A hL0 hL1
  have hRf' : (chainOp (r3Shift Rlz.F P k θ) (r3Seed Rlz.F P k (J.comp Vs.subtypeL)) (r3Lambda A)
      (r3Restrict _ (max bJ bA))).comp Rf = ContinuousLinearMap.id ℝ _ :=
    (congrArg (fun X => ContinuousLinearMap.comp X Rf) hch).trans hRf
  have hBn := hNB1 (1 - (Real.exp (-(P / k)))) (max bJ bA) (M0 + 1) A hL0 hL1 hAM
  have hRrn := hNR1 (1 - (Real.exp (-(P / k)))) (max bJ bA) hL0
  obtain ⟨Cst, hCst⟩ : ∃ x : ℝ, x = 1 + 2 * ‖R0‖ * ‖r3Lambda A‖ * (1 + ‖r3Restrict (1 - (Real.exp (-(P / k)))) (max bJ bA)‖) :=
    ⟨_, rfl⟩
  have hCst1 : 1 ≤ Cst := hCst ▸ le_add_of_nonneg_right (by positivity)
  have hCstle : Cst ≤ Cstb := by
    rw [hCst, hCstb]
    exact mono3 (mul_nonneg zero_le_two (R0.opNorm_nonneg)) (norm_nonneg _) hBn (by positivity)
      (by linarith only [hRrn])
  obtain ⟨δ, hδ⟩ : ∃ x : ℝ, x = 1 / (4 * Cst) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδ ▸ by positivity
  have hδc : 4 * δ * (1 + 2 * ‖R0‖ * ‖r3Lambda A‖ * (1 + ‖r3Restrict (1 - (Real.exp (-(P / k)))) (max bJ bA)‖)) ≤ 1 := by
    rw [← hCst, hδ]; apply le_of_eq; field_simp
  obtain ⟨T₀c, hT₀c, hcmp⟩ := hComp hK Rlz.F hKX hGX hDX P k θ (max bJ bA) Vs (J.comp Vs.subtypeL) ψ A hlam0
    hlam1.le hP0 hk hL12 hθ hθ1 hb δ hδ0
  obtain ⟨ϱ, hϱ0, -, hϱs⟩ := exists_small (512 * C3 ^ 2 * hK.choose) (1 / 2) (by norm_num)
  obtain ⟨η, hη0, -, hηs⟩ := exists_small (256 * C3 ^ 2 * hK.choose * Kres) (1 / 2) (by norm_num)
  obtain ⟨x0, hx0, hdx⟩ := hTestDense.exists_dist_lt (Freq.embedX (W 0)) hϱ0
  obtain ⟨ψ₀, hψ₀, hψ₀e⟩ := hTestSpec x0 hx0
  have hclose0 : ‖Freq.embedX ψ₀ - Freq.embedX (W 0)‖ ≤ ϱ := by
    rw [hψ₀e, ← dist_eq_norm, dist_comm]; exact hdx.le
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hψ₀.2.1.isCompact.isBounded
  have hb₀ : 0 < max r 1 := lt_max_of_lt_right one_pos
  have hsupp0 : tsupport ψ₀ ⊆ Metric.closedBall 0 (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨Td, hTd, hdat⟩ := hDatum W q C (Real.exp (-(P / k))) (max r 1) ϱ ψ₀ hIL hlam0 hlam1 hψ₀ hsupp0 hb₀ hϱ0
  obtain ⟨Tcl, hTcl, hcl⟩ := hClose Rlz.F hDX W q C P k (max bJ bA) ε ε A hIL hP0 hk hb hε0 hA
  have hB' : 0 < max (max bJ bA) (max r 1) := lt_max_of_lt_left hb
  obtain ⟨m, hm⟩ : ∃ x : ℝ, x = min (min (min T₀c Tcl) (min Ts Td))
      (min (min T₁ 1) (min (η ^ 4) ((1 / (8 * max (max bJ bA) (max r 1))) ^ 2))) := ⟨_, rfl⟩
  have hm0 : 0 < m := hm ▸ lt_min (lt_min (lt_min hT₀c hTcl) (lt_min hTs hTd))
    (lt_min (lt_min hT₁ one_pos) (lt_min (by positivity) (by positivity)))
  have hT : 0 < m / 2 := half_pos hm0
  have hTm : m / 2 < m := half_lt_self hm0
  have hm1 : m ≤ min (min T₀c Tcl) (min Ts Td) := hm ▸ min_le_left _ _
  have hm2 : m ≤ min (min T₁ 1) (min (η ^ 4) ((1 / (8 * max (max bJ bA) (max r 1))) ^ 2)) :=
    hm ▸ min_le_right _ _
  have hTc : m / 2 < T₀c := lt_of_lt_of_le hTm (hm1.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hTl : m / 2 < Tcl := lt_of_lt_of_le hTm (hm1.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hTs' : m / 2 < Ts := lt_of_lt_of_le hTm (hm1.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hTd' : m / 2 < Td := lt_of_lt_of_le hTm (hm1.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hT1' : m / 2 < T₁ := lt_of_lt_of_le hTm (hm2.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hT1 : m / 2 ≤ 1 := (lt_of_lt_of_le hTm (hm2.trans ((min_le_left _ _).trans (min_le_right _ _)))).le
  have hTη : m / 2 ≤ η ^ 4 := (lt_of_lt_of_le hTm (hm2.trans ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hTb : m / 2 ≤ (1 / (8 * max (max bJ bA) (max r 1))) ^ 2 :=
    (lt_of_lt_of_le hTm (hm2.trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hsq : Real.sqrt (m / 2) * max (max bJ bA) (max r 1) ≤ 1 / 8 := by
    have h1 : Real.sqrt (m / 2) ≤ 1 / (8 * max (max bJ bA) (max r 1)) := by
      rw [show 1 / (8 * max (max bJ bA) (max r 1)) = Real.sqrt ((1 / (8 * max (max bJ bA) (max r 1))) ^ 2)
        from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hTb
    calc Real.sqrt (m / 2) * max (max bJ bA) (max r 1)
        ≤ 1 / (8 * max (max bJ bA) (max r 1)) * max (max bJ bA) (max r 1) :=
          mul_le_mul_of_nonneg_right h1 hB'.le
      _ = 1 / 8 := by field_simp
  have hsqb : Real.sqrt (m / 2) * max bJ bA ≤ 1 / 8 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg _)) hsq
  have hsqb0 : Real.sqrt (m / 2) * max r 1 ≤ 1 / 8 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)) hsq
  have hT4 : (m / 2) ^ (1 / 4 : ℝ) ≤ η := by
    calc (m / 2) ^ (1 / 4 : ℝ) ≤ (η ^ 4) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hT.le hTη (by norm_num)
      _ = η := by rw [← Real.rpow_natCast, ← Real.rpow_mul hη0.le]; norm_num
  obtain ⟨Jt, hJt⟩ := hTLift Vs (J.comp Vs.subtypeL) (max bJ bA) ψ (m / 2) hb hT hT1 hsqb
  have hJtn : ‖Jt‖ ≤ CJ := hCJ (m / 2) hT hT1' Jt (fun e => by rw [hJt e, hψ])
  have hGt := (norm_torusSeed_le hSeqOps hK (m / 2) (Real.exp (-(P / k))) hT hT1 hlam0 hlam1.le hlam1 Jt).trans hJtn
  obtain ⟨c1, c2⟩ := hcmp (m / 2) hT hT1 hTc Jt hJt
  have hS1 : ‖r3Shift Rlz.F P k θ‖ ≤ qq := hqq ▸ hShift1 Rlz.F P k θ hP0 hk hθ0
  have hS2 : ‖torusShift hK (m / 2) (Real.exp (-(P / k))) θ hT hT1 hlam0 hlam1.le‖ ≤ qq :=
    hqq ▸ hShift2 hK (m / 2) (Real.exp (-(P / k))) θ hT hT1 hlam0 hlam1.le hθ0
  obtain ⟨R', hR', hR'n⟩ := hSI Vs (R3Seq (1 - (Real.exp (-(P / k))))) (TorusSeq (1 - (Real.exp (-(P / k))))) (ShellSeq (1 - (Real.exp (-(P / k)))))
    (r3Shift Rlz.F P k θ) (r3Seed Rlz.F P k (J.comp Vs.subtypeL)) (r3Lambda A) (r3Restrict _ (max bJ bA))
    (torusShift hK (m / 2) (Real.exp (-(P / k))) θ hT hT1 hlam0 hlam1.le) (torusSeed hK (m / 2) (Real.exp (-(P / k))) hT hT1 hlam0 hlam1.le Jt)
    (torusLambda A (m / 2) (Real.exp (-(P / k)))) (torusRestrict _ (max bJ bA) (m / 2) (Real.exp (-(P / k)))) Rf qq (2 * ‖R0‖) δ hq0 hq1 hS1 hS2
    hRf' hRfn c1 c2 hδc
  have hBt := hNB2 (max bJ bA) (m / 2) (Real.exp (-(P / k))) (M0 + 1) A hT hT1 hlam0 hlam1 hb hsqb hAM
  have hRt := hNR2 (max bJ bA) (m / 2) (Real.exp (-(P / k))) hT hT1 hlam0 hlam1 hb hsqb
  have hR'C3 : ‖R'‖ ≤ C3 := by
    have hBG : ‖torusLambda A (m / 2) (Real.exp (-(P / k)))‖ + ‖torusSeed hK (m / 2) (Real.exp (-(P / k))) hT hT1 hlam0 hlam1.le Jt‖ + 1 ≤ Cn * (M0 + 1) + CJ + 1 := by linarith only [hBt, hGt]
    have hBG0 : 0 ≤ ‖torusLambda A (m / 2) (Real.exp (-(P / k)))‖ + ‖torusSeed hK (m / 2) (Real.exp (-(P / k))) hT hT1 hlam0 hlam1.le Jt‖ + 1 := by positivity
    have hB3 := bound_mono hiq hBG0 hBG (by linarith only [hCst1]) hCstle (norm_nonneg _) hRt
    subst hCst hC3
    exact hR'n.trans hB3
  have hch2 := hTor hK (m / 2) (Real.exp (-(P / k))) θ (max bJ bA) hT hT1 hlam0 hlam1.le Vs Jt A hlam1 hb hsqb
  have hR'' := (congrArg (fun X => ContinuousLinearMap.comp X R') hch2).symm.trans hR'
  have hd2 := hDiff.2 hK (m / 2) (Real.exp (-(P / k))) θ (ε + ε) hT hT1 hlam0 hlam1.le Vs Jt (approxPiece W (m / 2) (Real.exp (-(P / k))))
    (fun n => A.torusPiece (stepScale (m / 2) (Real.exp (-(P / k))) n) n) hlam1 (fun n => hcl (m / 2) hT hTl n)
  obtain ⟨R2, hR2, hR2n⟩ := hRI (Vs × TorusSeq (1 - (Real.exp (-(P / k))))) (TorusSeq (1 - (Real.exp (-(P / k)))))
    (torusOp hK (m / 2) (Real.exp (-(P / k))) θ hT hT1 hlam0 hlam1.le Jt (fun n => A.torusPiece (stepScale (m / 2) (Real.exp (-(P / k))) n) n))
    (torusOp hK (m / 2) (Real.exp (-(P / k))) θ hT hT1 hlam0 hlam1.le Jt (approxPiece W (m / 2) (Real.exp (-(P / k))))) R' C3 hR'' hR'C3 (by
      have h1 := mul_le_mul_of_nonneg_right hd2 hC30
      have h2 : 8 * hK.choose * (1 - (Real.exp (-(P / k)))) ^ (1 / 4 : ℝ) * (ε + ε) * C3 ≤ ε * (16 * hK.choose * C3) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg hKc.le hε0.le) hC30) (sub_nonneg.2 hLq)
        nlinarith only [this]
      have h3 : 0 ≤ ε * (8 * Rlz.F.CK * ‖R0‖) :=
        mul_nonneg hε0.le (mul_nonneg (mul_nonneg (by norm_num) hCK) R0.opNorm_nonneg)
      linarith only [h1, h2, hεs, h3])
  have heq := torus_seq_equation hSeqOps hK (m / 2) (Real.exp (-(P / k))) θ hT hT1 hlam0 hlam1.le hlam1 Jt
    (approxPiece W (m / 2) (Real.exp (-(P / k)))) Ms (fun n => (hsz (m / 2) hT hTs' n).1) R2 hR2
  obtain ⟨ξ, hξ⟩ : ∃ x : V, x = ((m / 2) ^ (1 / 4 : ℝ)) • toV (transplantField (m / 2) ψ₀) -
      extendPiece (approxPiece W (m / 2) (Real.exp (-(P / k))) 0) 0 := ⟨_, rfl⟩
  have hξn : ‖ξ‖ ≤ ϱ + ϱ := by
    subst hξ; exact (hdat (m / 2) hT hTd').trans (by linarith only [hclose0])
  have hR2sq : ‖R2‖ ^ 2 ≤ (2 * C3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR2n 2
  have hsmall : 64 * ‖R2‖ ^ 2 * hK.choose * (1 - (Real.exp (-(P / k)))) ^ (1 / 4 : ℝ) *
      (Kres * (m / 2) ^ (1 / 4 : ℝ) + ‖ξ‖) ≤ 1 := by
    have a2 : Kres * (m / 2) ^ (1 / 4 : ℝ) + ‖ξ‖ ≤ Kres * η + (ϱ + ϱ) :=
      add_le_add (mul_le_mul_of_nonneg_left hT4 hKres0) hξn
    have a3 : 0 ≤ Kres * (m / 2) ^ (1 / 4 : ℝ) + ‖ξ‖ :=
      add_nonneg (mul_nonneg hKres0 (Real.rpow_nonneg hT.le _)) (norm_nonneg _)
    have a4 : 64 * ‖R2‖ ^ 2 * hK.choose ≤ 64 * (2 * C3) ^ 2 * hK.choose :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR2sq (by norm_num)) hKc.le
    have a5 : 0 ≤ 64 * (2 * C3) ^ 2 * hK.choose := mul_nonneg (by positivity) hKc.le
    calc 64 * ‖R2‖ ^ 2 * hK.choose * (1 - (Real.exp (-(P / k)))) ^ (1 / 4 : ℝ) * (Kres * (m / 2) ^ (1 / 4 : ℝ) + ‖ξ‖)
        ≤ 64 * (2 * C3) ^ 2 * hK.choose * 1 * (Kres * η + (ϱ + ϱ)) :=
          mul_le_mul (mul_le_mul a4 hLq hLq0 a5) a2 a3 (by simpa using a5)
      _ = η * (256 * C3 ^ 2 * hK.choose * Kres) + ϱ * (512 * C3 ^ 2 * hK.choose) := by ring
      _ ≤ 1 := by linarith only [hηs, hϱs]
  obtain ⟨e, z, hz, -, hmild, hz0, hlk⟩ := hSeq V Vs (fun n => (stepFrame hK (stepScale (m / 2) (Real.exp (-(P / k))) n) (stepScale_pos hT hlam0 n) (stepScale_le_one hT1 hlam0 hlam1.le n))) (1 - (Real.exp (-(P / k)))) θ ((Real.exp (-(P / k))) ^ (1 / 4 : ℝ))
    hK.choose Ms (Kres * (m / 2) ^ (1 / 4 : ℝ)) (approxPiece W (m / 2) (Real.exp (-(P / k))))
    (fun n => approxPiece W (m / 2) (Real.exp (-(P / k))) n - (stepFrame hK (stepScale (m / 2) (Real.exp (-(P / k))) n) (stepScale_pos hT hlam0 n) (stepScale_le_one hT1 hlam0 hlam1.le n)).pieceFree (1 - (Real.exp (-(P / k))))
      (extendPiece (approxPiece W (m / 2) (Real.exp (-(P / k))) n) 0) -
      (stepFrame hK (stepScale (m / 2) (Real.exp (-(P / k))) n) (stepScale_pos hT hlam0 n) (stepScale_le_one hT1 hlam0 hlam1.le n)).pieceBil (1 - (Real.exp (-(P / k)))) (approxPiece W (m / 2) (Real.exp (-(P / k))) n) (approxPiece W (m / 2) (Real.exp (-(P / k))) n))
    Jt R2 ξ hL0 hL1 hθ0 hθ1 hKc.le (fun n => le_rfl) (fun n => (hsz (m / 2) hT hTs' n).1)
    (fun n => (hLinks W q C (m / 2) (Real.exp (-(P / k))) hIL hT hT1 hlam0 hlam1 n).2) (fun n => by abel)
    (fun n => hKres (m / 2) hT hT1 n) heq hsmall
  have hgl := hGlue hK (m / 2) (Real.exp (-(P / k))) hT hT1 hlam0 hlam1
    (fun n => approxPiece W (m / 2) (Real.exp (-(P / k))) n + θ ^ n • z n) hmild hlk
  have hunb := hUnb (m / 2) (Real.exp (-(P / k))) θ (c / 2) _ (fun n => approxPiece W (m / 2) (Real.exp (-(P / k))) n + θ ^ n • z n)
    (approxPiece W (m / 2) (Real.exp (-(P / k)))) z hT hlam0 hlam1 hθ0 hθ1 (half_pos hc)
    (fun n s => (hsz (m / 2) hT hTs' n).2 s) hz (fun n => rfl)
  have hts0 := hTS ψ₀ (m / 2) (max r 1) hψ₀.1 hψ₀.2.2 ⟨hT, hT1, hb₀, hsqb0⟩ hsupp0
  have htse := hTS (ψ.field e) (m / 2) (max bJ bA) (ψ.isTest e).1 (ψ.isTest e).2.2 ⟨hT, hT1, hb, hsqb⟩
    (ψ.support e)
  have hsum := hAdd _ _ hts0.1 htse.1 hts0.2.1 htse.2.1 hts0.2.2.1 htse.2.2.1
  refine ⟨transplantField (m / 2) ψ₀ + transplantField (m / 2) (ψ.field e), hts0.1.add htse.1,
    fun i x => by simp only [Pi.add_apply, hts0.2.1 i x, htse.2.1 i x], fun x => ?_, m / 2, hT,
    gluePieces (m / 2) (Real.exp (-(P / k))) (fun n => approxPiece W (m / 2) (Real.exp (-(P / k))) n + θ ^ n • z n), ?_, hgl.1, hunb⟩
  · rw [divergenceAt_add (hts0.1.differentiable (by simp)) (htse.1.differentiable (by simp)),
      hts0.2.2.1 x, htse.2.2.1 x, add_zero]
  · have h0 := hgl.2 0 0 ⟨le_rfl, hL0.le⟩
    have hs0 : stepStart (m / 2) (Real.exp (-(P / k))) 0 + stepScale (m / 2) (Real.exp (-(P / k))) 0 * 0 = 0 := by simp [stepStart, stepScale]
    have hsc : stepScale (m / 2) (Real.exp (-(P / k))) 0 = m / 2 := by simp [stepScale]
    rw [hs0, hsc] at h0
    refine h0.trans ?_
    rw [hsum]
    beta_reduce
    have hx : extendPiece (approxPiece W (m / 2) (Real.exp (-(P / k))) 0 + θ ^ 0 • z 0) 0 =
        ((m / 2) ^ (1 / 4 : ℝ)) • (toV (transplantField (m / 2) ψ₀) + toV (transplantField (m / 2) (ψ.field e))) := by
      simp only [extendPiece_add, hz0, hξ, hJt e, pow_zero, one_smul, smul_add]
      abel
    rw [hx, smul_smul, ← Real.rpow_add hT, neg_add_cancel, Real.rpow_zero, one_smul]

end Breakdown.Periodic
