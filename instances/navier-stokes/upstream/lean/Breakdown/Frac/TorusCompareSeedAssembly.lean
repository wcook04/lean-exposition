import Breakdown.Frac.StTorusStepCompare
import Breakdown.Frac.TorusHeat
import Breakdown.Torus.CompareSeedAssembly
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracCompareSeedAssembly.Internal

open CompareSeedAssembly.Internal

theorem scaleField_eq {α c : ℝ} (hc : 0 < c) (f : Space → Space) :
    scaleField α c f = (c ^ (1 - 1 / α)) • dilateField (simScale α c) f := by
  funext y
  have hs : Real.sqrt (c ^ (1 / α)) = c ^ (1 / (2 * α)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc.le]
    congr 1
    ring
  simp only [scaleField, dilateField, simScale, Pi.smul_apply, smul_smul, hs]
  congr 1
  rw [← Real.rpow_add hc]
  congr 1
  ring

theorem simScale_mul {α a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    simScale α (a * c) = simScale α a * simScale α c := by
  unfold simScale
  exact Real.mul_rpow ha hc

theorem simScale_pos {α a : ℝ} (ha : 0 < a) : 0 < simScale α a := Real.rpow_pos_of_pos ha _

theorem dil_pow_eq {α lam θ : ℝ} (hl : 0 < lam) (n : ℕ) :
    (lam ^ dilExponent α / θ) ^ n = (θ⁻¹) ^ n * (lam ^ n) ^ dilExponent α := by
  rw [div_pow, ← rpow_pow_comm hl.le, inv_pow]
  ring

theorem dil_split {α x : ℝ} (hx : 0 < x) :
    x ^ dilExponent α = x ^ (1 - 1 / α) * simScale α x ^ (1 / 4 : ℝ) := by
  unfold simScale
  rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  unfold dilExponent
  congr 1
  ring

set_option maxHeartbeats 1600000 in
theorem slot_le_of_freeHeat {α : ℝ} (hα : 1 < α) (hTD : TransplantDilate) (hED : Freq.FracEmbedDilate α)
    {φ : Space → Space} {b lam θ T η s : ℝ} {n : ℕ} (hφ : IsTestField φ)
    (hφ' : IsTestField (dilateField (simScale α (lam ^ n)) φ)) (hl : 0 < lam) (hl1 : lam ≤ 1) (hθ : 0 < θ) (hT : 0 < T)
    (key : ‖restrictTorus (simScale α (T * lam ^ n)) b ((simScale α (T * lam ^ n)) ^ (1 / 4 : ℝ) •
        fracTorusHeat α ((T * lam ^ n) * (s + (lam ^ n)⁻¹ - 1))
          (toV (transplantField (simScale α (T * lam ^ n)) (dilateField (simScale α (lam ^ n)) φ)))) -
      restrictR3 b (Freq.fracHeatX α (s + (lam ^ n)⁻¹ - 1)
        (Freq.embedX (dilateField (simScale α (lam ^ n)) φ)))‖ ≤ η * θ ^ n) :
    ‖restrictTorus (simScale α (stepScale T lam n)) b ((lam ^ dilExponent α / θ) ^ n •
          fracTorusHeat α (T * (lam ^ n * s + 1 - lam ^ n))
            ((simScale α T ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α T) φ))) -
        restrictR3 b ((θ⁻¹) ^ n • Freq.fracHeatX α (s + (lam ^ n)⁻¹ - 1)
          (Freq.fracDilX α (lam ^ n) (Freq.embedX φ)))‖ ≤ η := by
  have hln : 0 < lam ^ n := pow_pos hl n
  have hln1 : lam ^ n ≤ 1 := pow_le_one₀ hl.le hl1
  have hα0 : 0 < α := lt_trans one_pos hα
  have hsT := simScale_pos (α := α) hT
  have hsx := simScale_pos (α := α) hln
  have e1 : transplantField (simScale α T) φ =
      transplantField (simScale α (T * lam ^ n)) (dilateField (simScale α (lam ^ n)) φ) := by
    rw [simScale_mul hT.le hln.le]
    exact hTD _ _ φ hsT hsx
  have hdφ := Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hφ
  have hdφ' := Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hφ'
  have e3 : Freq.fracDilX α (lam ^ n) (Freq.embedX φ) =
      ((lam ^ n) ^ (1 - 1 / α)) • Freq.embedX (dilateField (simScale α (lam ^ n)) φ) := by
    rw [hED _ φ hln hdφ, scaleField_eq hln]
    exact Freq.embedNormLinear_holds.2.2.2 _ _ hdφ'
  have hx : lam ^ n * (lam ^ n)⁻¹ = 1 := mul_inv_cancel₀ hln.ne'
  have e4 : T * (lam ^ n * s + 1 - lam ^ n) = (T * lam ^ n) * (s + (lam ^ n)⁻¹ - 1) := by
    linear_combination (-T) * hx
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (θ⁻¹) ^ n * (lam ^ n) ^ (1 - 1 / α) := ⟨_, rfl⟩
  have hcoef : (lam ^ dilExponent α / θ) ^ n * simScale α T ^ (1 / 4 : ℝ) =
      K * simScale α (T * lam ^ n) ^ (1 / 4 : ℝ) := by
    rw [dil_pow_eq hl, dil_split hln, simScale_mul hT.le hln.le,
      Real.mul_rpow hsT.le hsx.le, hK]
    ring
  have hst : stepScale T lam n = T * lam ^ n := rfl
  have ht : (lam ^ dilExponent α / θ) ^ n • fracTorusHeat α (T * (lam ^ n * s + 1 - lam ^ n))
      ((simScale α T ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α T) φ)) =
      K • ((simScale α (T * lam ^ n) ^ (1 / 4 : ℝ)) •
        fracTorusHeat α ((T * lam ^ n) * (s + (lam ^ n)⁻¹ - 1))
          (toV (transplantField (simScale α (T * lam ^ n)) (dilateField (simScale α (lam ^ n)) φ)))) := by
    rw [map_smul, smul_smul, smul_smul, hcoef, e1, e4]
  have hr : (θ⁻¹) ^ n • Freq.fracHeatX α (s + (lam ^ n)⁻¹ - 1) (Freq.fracDilX α (lam ^ n) (Freq.embedX φ)) =
      K • Freq.fracHeatX α (s + (lam ^ n)⁻¹ - 1) (Freq.embedX (dilateField (simScale α (lam ^ n)) φ)) := by
    rw [e3, map_smul, smul_smul, hK]
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hmain : restrictTorus (simScale α (stepScale T lam n)) b ((lam ^ dilExponent α / θ) ^ n •
          fracTorusHeat α (T * (lam ^ n * s + 1 - lam ^ n))
            ((simScale α T ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α T) φ))) -
        restrictR3 b ((θ⁻¹) ^ n • Freq.fracHeatX α (s + (lam ^ n)⁻¹ - 1)
          (Freq.fracDilX α (lam ^ n) (Freq.embedX φ))) =
      K • (restrictTorus (simScale α (T * lam ^ n)) b ((simScale α (T * lam ^ n) ^ (1 / 4 : ℝ)) • fracTorusHeat α ((T * lam ^ n) * (s + (lam ^ n)⁻¹ - 1)) (toV (transplantField (simScale α (T * lam ^ n)) (dilateField (simScale α (lam ^ n)) φ)))) - restrictR3 b (Freq.fracHeatX α (s + (lam ^ n)⁻¹ - 1) (Freq.embedX (dilateField (simScale α (lam ^ n)) φ)))) := by
    have h1 := congrArg₂ (fun x y => restrictTorus (simScale α (stepScale T lam n)) b x - restrictR3 b y) ht hr
    refine h1.trans ?_
    simp only [hst]
    rw [(restrictTorus _ b).map_smul, (restrictR3 b).map_smul, smul_sub]
  rw [hmain, norm_smul]
  rw [Real.norm_of_nonneg hK0]
  have hxk : (lam ^ n) ^ (1 - 1 / α) ≤ 1 := by
    refine Real.rpow_le_one hln.le hln1 ?_
    rw [sub_nonneg, div_le_one hα0]
    exact hα.le
  refine (mul_le_mul_of_nonneg_left key hK0).trans ?_
  have hθn : (θ⁻¹) ^ n * θ ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hθ.ne', one_pow]
  have hη : 0 ≤ η := by
    have := (norm_nonneg _).trans key
    exact nonneg_of_mul_nonneg_left this (pow_pos hθ n)
  calc K * (η * θ ^ n) = (lam ^ n) ^ (1 - 1 / α) * η * ((θ⁻¹) ^ n * θ ^ n) := by rw [hK]; ring
    _ = (lam ^ n) ^ (1 - 1 / α) * η := by rw [hθn, mul_one]
    _ ≤ 1 * η := mul_le_mul_of_nonneg_right hxk hη
    _ = η := one_mul η

theorem torus_slot (hS : SeqOpSpec) (hC : PieceCompSpec) (α L b T lam : ℝ) (hL : 0 ≤ L)
    (g : TorusSeq L) (n : ℕ) (s : Icc (0 : ℝ) L) :
    fracTorusRestrict α L b T lam g n s = restrictTorus (simScale α (stepScale T lam n)) b (g n s) := by
  have hCt0 := restrictTorusFun_bound.choose_spec.1
  have hA : ∀ m, ‖pieceComp L (restrictTorus (simScale α (stepScale T lam m)) b)‖ ≤
      restrictTorusFun_bound.choose :=
    fun m => ((hC V ShellData L _ hL).2).trans (by unfold restrictTorus; exact LinearMap.mkContinuous_norm_le _ hCt0 _)
  unfold fracTorusRestrict
  rw [(hS _ _ _ _ hA hCt0).1 g n]
  exact (hC _ _ _ _ hL).1 _ _

theorem slot_le_geometric {α : ℝ} (hH : Freq.FracHeatSemigroup α) (hD : Freq.FracDilationAlgebra α)
    {Ct Cr M lam θ T b s : ℝ} {n : ℕ} {x : Freq.X} {z : V} (hCt0 : 0 ≤ Ct) (hCr0 : 0 ≤ Cr)
    (hnT : ∀ μ c : ℝ, ‖restrictTorus μ c‖ ≤ Ct) (hCr : ∀ c, ‖restrictR3 c‖ ≤ Cr) (hz : ‖z‖ ≤ M)
    (hl : 0 < lam) (hl1 : lam < 1) (hθ : 0 < θ) (hs0 : 0 ≤ s) :
    ‖restrictTorus (simScale α (stepScale T lam n)) b ((lam ^ dilExponent α / θ) ^ n •
          fracTorusHeat α (T * (lam ^ n * s + 1 - lam ^ n)) z) -
        restrictR3 b ((θ⁻¹) ^ n • Freq.fracHeatX α (s + (lam ^ n)⁻¹ - 1) (Freq.fracDilX α (lam ^ n) x))‖ ≤
      (Ct * M + Cr * ‖x‖) * (lam ^ dilExponent α / θ) ^ n := by
  have hq0 : 0 ≤ lam ^ dilExponent α / θ := div_nonneg (rpow_nonneg hl.le _) hθ.le
  have hln : 0 < lam ^ n := pow_pos hl n
  have hln1 : lam ^ n ≤ 1 := pow_le_one₀ hl.le hl1.le
  have hinv : 1 ≤ (lam ^ n)⁻¹ := (one_le_inv₀ hln).mpr hln1
  have hτ0 : 0 ≤ s + (lam ^ n)⁻¹ - 1 := by linarith
  have hqn : (θ⁻¹) ^ n * (lam ^ n) ^ dilExponent α = (lam ^ dilExponent α / θ) ^ n := (dil_pow_eq hl n).symm
  have ht : ‖restrictTorus (simScale α (stepScale T lam n)) b ((lam ^ dilExponent α / θ) ^ n •
      fracTorusHeat α (T * (lam ^ n * s + 1 - lam ^ n)) z)‖ ≤
      Ct * ((lam ^ dilExponent α / θ) ^ n * M) := by
    refine ((restrictTorus _ b).le_opNorm _).trans (mul_le_mul (hnT _ _) ?_ (norm_nonneg _) hCt0)
    rw [norm_smul, norm_pow, Real.norm_of_nonneg hq0]
    refine mul_le_mul_of_nonneg_left (((fracTorusHeat α _).le_of_opNorm_le
      ((fracTorusHeatAlgebra α).2.2.2.1 _) _).trans ?_) (pow_nonneg hq0 n)
    rw [one_mul]
    exact hz
  have hr : ‖restrictR3 b ((θ⁻¹) ^ n • Freq.fracHeatX α (s + (lam ^ n)⁻¹ - 1) (Freq.fracDilX α (lam ^ n) x))‖ ≤
      Cr * ((lam ^ dilExponent α / θ) ^ n * ‖x‖) := by
    refine ((restrictR3 b).le_of_opNorm_le (hCr b) _).trans (mul_le_mul_of_nonneg_left ?_ hCr0)
    rw [norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg hθ.le, ← hqn, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine ((Freq.fracHeatX α _).le_of_opNorm_le (hH.2.2.1 _ hτ0) _).trans ?_
    rw [one_mul]
    exact (hD.1 _ hln _).le
  refine (norm_sub_le _ _).trans ((add_le_add ht hr).trans (le_of_eq ?_))
  ring

theorem simScale_small {α T y : ℝ} (hα : 1 < α) (hT : 0 < T) (hy : 0 < y) (hTy : T < y ^ α) :
    simScale α T < y := by
  have hα0 : 0 < α := lt_trans one_pos hα
  have h := Real.rpow_lt_rpow hT.le hTy (one_div_pos.mpr hα0)
  unfold simScale
  rw [one_div, Real.rpow_rpow_inv hy.le hα0.ne'] at h
  rwa [one_div]

theorem simScale_le_one {α T : ℝ} (hα : 1 < α) (hT : 0 < T) (hT1 : T ≤ 1) : simScale α T ≤ 1 :=
  Real.rpow_le_one hT.le hT1 (one_div_pos.mpr (lt_trans one_pos hα)).le

theorem slot_bound {α : ℝ} (hα : 1 < α) (hTD : TransplantDilate) (hDT : DilateTest)
    (hFH : FracFreeHeatComparison α) (hED : Freq.FracEmbedDilate α) (hTN : TransplantNorm)
    (hRR : RestrictR3Bound) (hH : Freq.FracHeatSemigroup α) (hD : Freq.FracDilationAlgebra α)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : E →L[ℝ] Freq.X} {b : ℝ} (ψ : TestLift E J b) (hb : 0 < b) {lam θ : ℝ} (hl : 0 < lam)
    (hl1 : lam < 1) (hq : lam ^ dilExponent α < θ) (e : E) {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T < T₀ → ∀ Jt : E →L[ℝ] V,
      Jt e = (simScale α T ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α T) (ψ.field e)) →
      ∀ (n : ℕ) (s : ℝ), 0 ≤ s → s ≤ 1 - lam →
      ‖restrictTorus (simScale α (stepScale T lam n)) b ((lam ^ dilExponent α / θ) ^ n •
          fracTorusHeat α (T * (lam ^ n * s + 1 - lam ^ n)) (Jt e)) -
        restrictR3 b ((θ⁻¹) ^ n • Freq.fracHeatX α (s + (lam ^ n)⁻¹ - 1)
          (Freq.fracDilX α (lam ^ n) (J e)))‖ ≤ η := by
  choose Cr hCr0 hCr using hRR
  have hCt0 : 0 ≤ restrictTorusFun_bound.choose := restrictTorusFun_bound.choose_spec.1
  have hnT : ∀ μ c : ℝ, ‖restrictTorus μ c‖ ≤ restrictTorusFun_bound.choose := fun μ c => by
    unfold restrictTorus
    exact LinearMap.mkContinuous_norm_le _ hCt0 _
  have hθ : 0 < θ := lt_of_le_of_lt (rpow_nonneg hl.le _) hq
  have hq0 : 0 ≤ lam ^ dilExponent α / θ := div_nonneg (rpow_nonneg hl.le _) hθ.le
  have hq1 : lam ^ dilExponent α / θ < 1 := (div_lt_one hθ).mpr hq
  have hfT : IsTestField (ψ.field e) := ψ.isTest e
  choose M hM0 hM using transplant_bound hTN ψ e
  have hK0 : 0 ≤ restrictTorusFun_bound.choose * M + Cr * ‖J e‖ :=
    add_nonneg (mul_nonneg hCt0 hM0) (mul_nonneg hCr0 (norm_nonneg _))
  choose N hN using exists_pow_lt_of_lt_one
    (div_pos hη (by linarith : (0 : ℝ) < restrictTorusFun_bound.choose * M + Cr * ‖J e‖ + 1)) hq1
  have hμ : ∀ n : ℕ, ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∀ τ ∈ Icc (0 : ℝ) (lam ^ n)⁻¹,
      ‖restrictTorus (simScale α μ) b ((simScale α μ ^ (1 / 4 : ℝ)) • fracTorusHeat α (μ * τ)
          (toV (transplantField (simScale α μ) (dilateField (simScale α (lam ^ n)) (ψ.field e))))) -
        restrictR3 b (Freq.fracHeatX α τ
          (Freq.embedX (dilateField (simScale α (lam ^ n)) (ψ.field e))))‖ ≤ η * θ ^ n :=
    fun n => hFH _ (hDT _ _ (simScale_pos (pow_pos hl n)) hfT) b (lam ^ n) (η * θ ^ n) hb (pow_pos hl n)
      (by positivity)
  choose μ₀ hμ₀ hμb using hμ
  have hS : 0 ≤ ∑ n ∈ Finset.range N, 1 / μ₀ n :=
    Finset.sum_nonneg fun n _ => (one_div_pos.mpr (hμ₀ n)).le
  have hy : (0 : ℝ) < 1 / (64 * b ^ 2) := by positivity
  refine ⟨min (1 / (1 + ∑ n ∈ Finset.range N, 1 / μ₀ n)) ((1 / (64 * b ^ 2)) ^ α),
    lt_min (div_pos one_pos (by linarith)) (Real.rpow_pos_of_pos hy _), ?_⟩
  intro T hT hT1 hTT Jt hJt n s hs0 hs1
  rw [hJt]
  have hTa := lt_of_lt_of_le hTT (min_le_left _ _)
  have hTb := lt_of_lt_of_le hTT (min_le_right _ _)
  by_cases hn : n < N
  · have hln : 0 < lam ^ n := pow_pos hl n
    have hln1 : lam ^ n ≤ 1 := pow_le_one₀ hl.le hl1.le
    have hinv : 1 ≤ (lam ^ n)⁻¹ := (one_le_inv₀ hln).mpr hln1
    have hμn : T * lam ^ n < μ₀ n := by
      have h1 : T * lam ^ n ≤ T := mul_le_of_le_one_right hT.le hln1
      have h2 := inv_sum_le (Finset.range N) μ₀ hμ₀ n (Finset.mem_range.mpr hn)
      linarith
    have hτ : s + (lam ^ n)⁻¹ - 1 ∈ Icc (0 : ℝ) (lam ^ n)⁻¹ := ⟨by linarith, by linarith⟩
    rw [← ψ.embed e]
    exact slot_le_of_freeHeat hα hTD hED hfT (hDT _ _ (simScale_pos hln) hfT) hl hl1.le hθ hT
      (hμb n (T * lam ^ n) (mul_pos hT hln) hμn _ hτ)
  · have hsT := simScale_pos (α := α) hT
    have hsc : IsShellScale (simScale α T) b :=
      ⟨hsT, simScale_le_one hα hT hT1, hb, sqrt_mul_le hsT hb (simScale_small hα hT hy hTb)⟩
    exact (slot_le_geometric hH hD hCt0 hCr0 hnT hCr (hM _ hsc) hl hl1 hθ hs0).trans
      (geometric_tail_le hK0 hη hq0 hq1 (not_lt.mp hn) hN)

end FracCompareSeedAssembly.Internal

open FracCompareSeedAssembly.Internal CompareSeedAssembly.Internal in
theorem fracSeedComparison (α : ℝ) (hα : 1 < α) (hR : FracR3SeedEntry α) (hT : FracTorusSeedEntry α hα)
    (hTD : TransplantDilate) (hDT : DilateTest) (hFH : FracFreeHeatComparison α)
    (hED : Freq.FracEmbedDilate α) (hTN : TransplantNorm) (hRR : RestrictR3Bound) (hS : SeqOpSpec)
    (hC : PieceCompSpec) (_hO : FracOperatorNormBounds α hα) (hH : Freq.FracHeatSemigroup α)
    (hD : Freq.FracDilationAlgebra α) : FracSeedComparison α hα := by
  intro F hFK hFG hFD P k θ b E _ _ _ J ψ hl hl1 hP hk hL hq hθ1 hb δ hδ
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hlt : Real.exp (-(P / k)) < 1 := Real.exp_lt_one_iff.mpr (by have := div_pos hP hk'; linarith)
  have hL0 : 0 ≤ 1 - Real.exp (-(P / k)) := by linarith
  choose η hη hred using basis_reduce (E := E) δ hδ
  have hex := fun i => slot_bound hα hTD hDT hFH hED hTN hRR hH hD ψ hb hl hlt hq
    (Module.finBasis ℝ E i) hη
  choose T₀ hT₀ hT₀b using hex
  have hSum : 0 ≤ ∑ i, 1 / T₀ i := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hT₀ i)).le
  refine ⟨1 / (1 + ∑ i, 1 / T₀ i), div_pos one_pos (by linarith), ?_⟩
  intro T hT0 hT1 hTT Jt hJt
  apply hred
  intro i
  have hTi : T < T₀ i := lt_of_lt_of_le hTT (inv_sum_le Finset.univ T₀ hT₀ i (Finset.mem_univ i))
  refine lp.norm_le_of_forall_le hη.le fun n => ?_
  refine (ContinuousMap.norm_le _ hη.le).2 fun s => ?_
  simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.comp_apply, lp.coeFn_sub,
    ContinuousMap.sub_apply]
  refine (congrArg (‖·‖) (congrArg₂ (· - ·) (torus_slot hS hC _ _ _ _ _ hL0 _ n s)
    (r3_slot hRR hS hC _ _ hL0 _ n s))).trans_le ?_
  refine (congrArg (‖·‖) (congrArg₂ (fun x y => restrictTorus _ b x - restrictR3 b y)
    (hT T _ θ hT0 hT1 hl hl1 E Jt hlt hq hθ1 (Module.finBasis ℝ E i) n s)
    (hR F hFG hFD P k θ E J hP hk hq hθ1 (Module.finBasis ℝ E i) n s))).trans_le ?_
  exact hT₀b i T hT0 hT1 hTi Jt (hJt _) n s s.2.1 s.2.2

end Breakdown.Periodic
