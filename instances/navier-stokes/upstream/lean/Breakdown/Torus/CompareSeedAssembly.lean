import Breakdown.Torus.CompareStatements
import Breakdown.FreqTr.EmbedNegSsp

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace CompareSeedAssembly.Internal

theorem inv_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 < f i) (i : ι) (hi : i ∈ s) :
    1 / (1 + ∑ j ∈ s, 1 / f j) ≤ f i := by
  have h1 : 1 / f i ≤ ∑ j ∈ s, 1 / f j :=
    Finset.single_le_sum (f := fun j => 1 / f j) (fun j _ => (one_div_pos.mpr (hf j)).le) hi
  have h2 : 0 < 1 / f i := one_div_pos.mpr (hf i)
  calc 1 / (1 + ∑ j ∈ s, 1 / f j) ≤ 1 / (1 / f i) := one_div_le_one_div_of_le h2 (by linarith)
    _ = f i := one_div_one_div _

theorem basis_reduce {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (δ : ℝ) (hδ : 0 < δ) : ∃ η : ℝ, 0 < η ∧ ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (D : E →L[ℝ] Y), (∀ i, ‖D (Module.finBasis ℝ E i)‖ ≤ η) → ‖D‖ ≤ δ := by
  set bs := Module.finBasis ℝ E
  set Kc := ∑ i, ‖LinearMap.toContinuousLinearMap (bs.coord i)‖
  have hKc0 : 0 ≤ Kc := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨δ / (Kc + 1), div_pos hδ (by linarith), fun Y _ _ D hD => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hδ.le fun e => ?_
  have he : D e = ∑ i, bs.repr e i • D (bs i) := by
    conv_lhs => rw [← bs.sum_repr e]
    rw [map_sum]
    simp only [map_smul]
  have hc : ∀ i, ‖bs.repr e i‖ ≤ ‖LinearMap.toContinuousLinearMap (bs.coord i)‖ * ‖e‖ := fun i => by
    have := (LinearMap.toContinuousLinearMap (bs.coord i)).le_opNorm e
    simpa [Module.Basis.coord_apply] using this
  have hK : Kc * (δ / (Kc + 1)) ≤ δ := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  rw [he]
  calc ‖∑ i, bs.repr e i • D (bs i)‖ ≤ ∑ i, ‖bs.repr e i‖ * (δ / (Kc + 1)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hD i) (norm_nonneg _)
    _ ≤ ∑ i, ‖LinearMap.toContinuousLinearMap (bs.coord i)‖ * ‖e‖ * (δ / (Kc + 1)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (by positivity)
    _ = ‖e‖ * (Kc * (δ / (Kc + 1))) := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
    _ ≤ ‖e‖ * δ := mul_le_mul_of_nonneg_left hK (norm_nonneg e)
    _ = δ * ‖e‖ := mul_comm _ _

theorem torus_slot (hS : SeqOpSpec) (hC : PieceCompSpec) (L b T lam : ℝ) (hL : 0 ≤ L)
    (g : TorusSeq L) (n : ℕ) (s : Icc (0 : ℝ) L) :
    torusRestrict L b T lam g n s = restrictTorus (stepScale T lam n) b (g n s) := by
  have hCt0 := restrictTorusFun_bound.choose_spec.1
  have hA : ∀ m, ‖pieceComp L (restrictTorus (stepScale T lam m) b)‖ ≤ restrictTorusFun_bound.choose :=
    fun m => ((hC V ShellData L _ hL).2).trans (by unfold restrictTorus; exact LinearMap.mkContinuous_norm_le _ hCt0 _)
  unfold torusRestrict
  rw [(hS _ _ _ _ hA hCt0).1 g n]
  exact (hC _ _ _ _ hL).1 _ _

theorem r3_slot (hRR : RestrictR3Bound) (hS : SeqOpSpec) (hC : PieceCompSpec) (L b : ℝ) (hL : 0 ≤ L)
    (g : R3Seq L) (n : ℕ) (s : Icc (0 : ℝ) L) :
    r3Restrict L b g n s = restrictR3 b (g n s) := by
  choose Cr hCr0 hCr using hRR
  have hA : ∀ m : ℕ, ‖pieceComp L (restrictR3 b)‖ ≤ Cr := fun _ => ((hC _ _ L _ hL).2).trans (hCr b)
  unfold r3Restrict
  rw [(hS _ _ _ _ hA hCr0).1 g n]
  exact (hC _ _ _ _ hL).1 _ _

theorem transplant_bound (hTN : TransplantNorm) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : E →L[ℝ] Freq.X} {b : ℝ} (ψ : TestLift E J b) (e : E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, IsShellScale T b →
      ‖(T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ.field e))‖ ≤ M := by
  have hfT : IsTestField (ψ.field e) := ψ.isTest e
  refine ⟨Real.sqrt ((∫ y, ∑ i : Fin 3, ‖fderiv ℝ (ψ.field e) y (unitVector i)‖ ^ 2) +
    ∫ y, ‖ψ.field e y‖ ^ 2), Real.sqrt_nonneg _, fun T hsc => ?_⟩
  have h := hTN (ψ.field e) T b hfT.1 hfT.2.2 hsc (ψ.support e)
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  rw [h]
  have : T * ∫ y, ‖ψ.field e y‖ ^ 2 ≤ ∫ y, ‖ψ.field e y‖ ^ 2 :=
    mul_le_of_le_one_left (integral_nonneg fun _ => by positivity) hsc.2.1
  linarith

theorem sqrt_mul_le {T b : ℝ} (hT : 0 < T) (hb : 0 < b) (hTb : T < 1 / (64 * b ^ 2)) :
    Real.sqrt T * b ≤ 1 / 8 := by
  have h64 : T * (64 * b ^ 2) < 1 := (lt_div_iff₀ (by positivity)).mp hTb
  nlinarith [Real.sq_sqrt hT.le, Real.sqrt_nonneg T, mul_nonneg (Real.sqrt_nonneg T) hb.le]

theorem slot_le_of_freeHeat (hTD : TransplantDilate) (hED : Freq.EmbedDilate) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {J : E →L[ℝ] Freq.X} {b : ℝ} (ψ : TestLift E J b) (e : E) {lam θ T η s : ℝ} {n : ℕ}
    (hl : 0 < lam) (hθ : 0 < θ) (hT : 0 < T)
    (key : ‖restrictTorus (T * lam ^ n) b ((T * lam ^ n) ^ (1 / 4 : ℝ) • heat ((T * lam ^ n) * (s + (lam ^ n)⁻¹ - 1))
        (toV (transplantField (T * lam ^ n) (dilateField (lam ^ n) (ψ.field e))))) -
      restrictR3 b (Freq.heatX (s + (lam ^ n)⁻¹ - 1) (Freq.embedX (dilateField (lam ^ n) (ψ.field e))))‖ ≤ η * θ ^ n) :
    ‖restrictTorus (stepScale T lam n) b ((lam ^ (1 / 4 : ℝ) / θ) ^ n •
          heat (T * (lam ^ n * s + 1 - lam ^ n)) ((T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ.field e)))) -
        restrictR3 b ((θ⁻¹) ^ n • Freq.heatX (s + (lam ^ n)⁻¹ - 1) (Freq.dilX (lam ^ n) (J e)))‖ ≤ η := by
  have hln : 0 < lam ^ n := pow_pos hl n
  have hfT : IsTestField (ψ.field e) := ψ.isTest e
  have e1 : transplantField T (ψ.field e) = transplantField (T * lam ^ n) (dilateField (lam ^ n) (ψ.field e)) :=
    hTD T (lam ^ n) (ψ.field e) hT hln
  have e3 : Freq.dilX (lam ^ n) (J e) = Freq.embedX (dilateField (lam ^ n) (ψ.field e)) := by
    rw [← ψ.embed e]
    exact hED _ _ hln (Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hfT)
  have hx : lam ^ n * (lam ^ n)⁻¹ = 1 := mul_inv_cancel₀ hln.ne'
  have e4 : T * (lam ^ n * s + 1 - lam ^ n) = (T * lam ^ n) * (s + (lam ^ n)⁻¹ - 1) := by
    linear_combination (-T) * hx
  have hqn : (θ⁻¹) ^ n * (lam ^ n) ^ (1 / 4 : ℝ) = (lam ^ (1 / 4 : ℝ) / θ) ^ n := by
    rw [div_pow, ← rpow_pow_comm hl.le, inv_pow]
    ring
  have e5 : (lam ^ (1 / 4 : ℝ) / θ) ^ n * T ^ (1 / 4 : ℝ) = (θ⁻¹) ^ n * (T * lam ^ n) ^ (1 / 4 : ℝ) := by
    rw [mul_rpow hT.le hln.le, ← hqn]
    ring
  have hst : stepScale T lam n = T * lam ^ n := rfl
  simp only [ContinuousLinearMap.map_smul] at key
  simp only [hst, e1, e3, e4, ContinuousLinearMap.map_smul, smul_smul]
  simp only [e5, mul_smul]
  simp only [← smul_sub, norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg hθ.le]
  refine (mul_le_mul_of_nonneg_left key (by positivity)).trans (le_of_eq ?_)
  have := hθ.ne'
  rw [inv_pow]
  field_simp

theorem slot_le_geometric (hH : Freq.HeatSemigroup) (hD : Freq.DilationAlgebra) {Ct Cr M lam θ T b s : ℝ} {n : ℕ}
    {x : Freq.X} {z : V} (hCt0 : 0 ≤ Ct) (hCr0 : 0 ≤ Cr) (hnT : ∀ μ c : ℝ, ‖restrictTorus μ c‖ ≤ Ct)
    (hCr : ∀ c, ‖restrictR3 c‖ ≤ Cr) (hz : ‖z‖ ≤ M) (hl : 0 < lam) (hl1 : lam < 1) (hθ : 0 < θ) (hs0 : 0 ≤ s) :
    ‖restrictTorus (stepScale T lam n) b ((lam ^ (1 / 4 : ℝ) / θ) ^ n • heat (T * (lam ^ n * s + 1 - lam ^ n)) z) -
        restrictR3 b ((θ⁻¹) ^ n • Freq.heatX (s + (lam ^ n)⁻¹ - 1) (Freq.dilX (lam ^ n) x))‖ ≤
      (Ct * M + Cr * ‖x‖) * (lam ^ (1 / 4 : ℝ) / θ) ^ n := by
  have hq0 : 0 ≤ lam ^ (1 / 4 : ℝ) / θ := div_nonneg (rpow_nonneg hl.le _) hθ.le
  have hln : 0 < lam ^ n := pow_pos hl n
  have hln1 : lam ^ n ≤ 1 := pow_le_one₀ hl.le hl1.le
  have hinv : 1 ≤ (lam ^ n)⁻¹ := (one_le_inv₀ hln).mpr hln1
  have hτ0 : 0 ≤ s + (lam ^ n)⁻¹ - 1 := by linarith
  have hqn : (θ⁻¹) ^ n * (lam ^ n) ^ (1 / 4 : ℝ) = (lam ^ (1 / 4 : ℝ) / θ) ^ n := by
    rw [div_pow, ← rpow_pow_comm hl.le, inv_pow]
    ring
  have ht : ‖restrictTorus (stepScale T lam n) b ((lam ^ (1 / 4 : ℝ) / θ) ^ n • heat (T * (lam ^ n * s + 1 - lam ^ n)) z)‖ ≤
      Ct * ((lam ^ (1 / 4 : ℝ) / θ) ^ n * M) := by
    refine ((restrictTorus _ b).le_opNorm _).trans (mul_le_mul (hnT _ _) ?_ (norm_nonneg _) hCt0)
    rw [norm_smul, norm_pow, Real.norm_of_nonneg hq0]
    refine mul_le_mul_of_nonneg_left (((heat _).le_of_opNorm_le (norm_heat_le _) _).trans ?_) (pow_nonneg hq0 n)
    rw [one_mul]
    exact hz
  have hr : ‖restrictR3 b ((θ⁻¹) ^ n • Freq.heatX (s + (lam ^ n)⁻¹ - 1) (Freq.dilX (lam ^ n) x))‖ ≤
      Cr * ((lam ^ (1 / 4 : ℝ) / θ) ^ n * ‖x‖) := by
    refine ((restrictR3 b).le_of_opNorm_le (hCr b) _).trans (mul_le_mul_of_nonneg_left ?_ hCr0)
    rw [norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg hθ.le, ← hqn, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine ((Freq.heatX _).le_of_opNorm_le (hH.2.2.1 _ hτ0) _).trans ?_
    rw [one_mul]
    exact (hD.1 _ hln _).le
  refine (norm_sub_le _ _).trans ((add_le_add ht hr).trans (le_of_eq ?_))
  ring

theorem geometric_tail_le {K q η : ℝ} {n N : ℕ} (hK0 : 0 ≤ K) (hη : 0 < η) (hq0 : 0 ≤ q) (hq1 : q < 1) (hn : N ≤ n)
    (hN : q ^ N < η / (K + 1)) : K * q ^ n ≤ η := by
  have hqN : q ^ n ≤ q ^ N := pow_le_pow_of_le_one hq0 hq1.le hn
  calc K * q ^ n ≤ K * (η / (K + 1)) := mul_le_mul_of_nonneg_left (hqN.trans hN.le) hK0
    _ ≤ (K + 1) * (η / (K + 1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = η := by field_simp

theorem slot_bound (hTD : TransplantDilate) (hDT : DilateTest) (hFH : FreeHeatComparison)
    (hED : Freq.EmbedDilate) (hTN : TransplantNorm) (hRR : RestrictR3Bound) (hH : Freq.HeatSemigroup)
    (hD : Freq.DilationAlgebra) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : E →L[ℝ] Freq.X} {b : ℝ} (ψ : TestLift E J b) (hb : 0 < b) {lam θ : ℝ} (hl : 0 < lam)
    (hl1 : lam < 1) (hq : lam ^ (1 / 4 : ℝ) < θ) (e : E) {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T < T₀ → ∀ Jt : E →L[ℝ] V,
      Jt e = (T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ.field e)) → ∀ (n : ℕ) (s : ℝ), 0 ≤ s → s ≤ 1 - lam →
      ‖restrictTorus (stepScale T lam n) b ((lam ^ (1 / 4 : ℝ) / θ) ^ n •
          heat (T * (lam ^ n * s + 1 - lam ^ n)) (Jt e)) -
        restrictR3 b ((θ⁻¹) ^ n • Freq.heatX (s + (lam ^ n)⁻¹ - 1) (Freq.dilX (lam ^ n) (J e)))‖ ≤ η := by
  choose Cr hCr0 hCr using hRR
  have hCt0 : 0 ≤ restrictTorusFun_bound.choose := restrictTorusFun_bound.choose_spec.1
  have hnT : ∀ μ c : ℝ, ‖restrictTorus μ c‖ ≤ restrictTorusFun_bound.choose := fun μ c => by
    unfold restrictTorus
    exact LinearMap.mkContinuous_norm_le _ hCt0 _
  have hθ : 0 < θ := lt_of_le_of_lt (rpow_nonneg hl.le _) hq
  have hq0 : 0 ≤ lam ^ (1 / 4 : ℝ) / θ := div_nonneg (rpow_nonneg hl.le _) hθ.le
  have hq1 : lam ^ (1 / 4 : ℝ) / θ < 1 := (div_lt_one hθ).mpr hq
  have hfT : IsTestField (ψ.field e) := ψ.isTest e
  choose M hM0 hM using transplant_bound hTN ψ e
  have hK0 : 0 ≤ restrictTorusFun_bound.choose * M + Cr * ‖J e‖ :=
    add_nonneg (mul_nonneg hCt0 hM0) (mul_nonneg hCr0 (norm_nonneg _))
  choose N hN using exists_pow_lt_of_lt_one
    (div_pos hη (by linarith : (0 : ℝ) < restrictTorusFun_bound.choose * M + Cr * ‖J e‖ + 1)) hq1
  have hμ : ∀ n : ℕ, ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∀ τ ∈ Icc (0 : ℝ) (lam ^ n)⁻¹,
      ‖restrictTorus μ b ((μ ^ (1 / 4 : ℝ)) • heat (μ * τ) (toV (transplantField μ (dilateField (lam ^ n) (ψ.field e))))) -
        restrictR3 b (Freq.heatX τ (Freq.embedX (dilateField (lam ^ n) (ψ.field e))))‖ ≤ η * θ ^ n :=
    fun n => hFH _ (hDT _ _ (pow_pos hl n) hfT) b (lam ^ n) (η * θ ^ n) hb (pow_pos hl n) (by positivity)
  choose μ₀ hμ₀ hμb using hμ
  have hS : 0 ≤ ∑ n ∈ Finset.range N, 1 / μ₀ n :=
    Finset.sum_nonneg fun n _ => (one_div_pos.mpr (hμ₀ n)).le
  refine ⟨min (1 / (1 + ∑ n ∈ Finset.range N, 1 / μ₀ n)) (1 / (64 * b ^ 2)),
    lt_min (div_pos one_pos (by linarith)) (by positivity), ?_⟩
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
    exact slot_le_of_freeHeat hTD hED ψ e hl hθ hT (hμb n (T * lam ^ n) (mul_pos hT hln) hμn _ hτ)
  · have hsc : IsShellScale T b := ⟨hT, hT1, hb, sqrt_mul_le hT hb hTb⟩
    exact (slot_le_geometric hH hD hCt0 hCr0 hnT hCr (hM T hsc) hl hl1 hθ hs0).trans
      (geometric_tail_le hK0 hη hq0 hq1 (not_lt.mp hn) hN)

end CompareSeedAssembly.Internal

open CompareSeedAssembly.Internal in
theorem seedComparison (hR : R3SeedEntry) (hT : TorusSeedEntry) (hTD : TransplantDilate)
    (hDT : DilateTest) (hFH : FreeHeatComparison) (hED : Freq.EmbedDilate) (hTN : TransplantNorm)
    (hRR : RestrictR3Bound) (hS : SeqOpSpec) (hC : PieceCompSpec) (hH : Freq.HeatSemigroup)
    (hD : Freq.DilationAlgebra) : SeedComparison := by
  intro hK F hFK hFG hFD P k θ b E _ _ _ J ψ hl hl1 hP hk hL hq hθ1 hb δ hδ
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hlt : Real.exp (-(P / k)) < 1 := Real.exp_lt_one_iff.mpr (by have := div_pos hP hk'; linarith)
  have hL0 : 0 ≤ 1 - Real.exp (-(P / k)) := by linarith
  choose η hη hred using basis_reduce (E := E) δ hδ
  have hex := fun i => slot_bound hTD hDT hFH hED hTN hRR hH hD ψ hb hl hlt hq
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
  refine (congrArg (‖·‖) (congrArg₂ (· - ·) (torus_slot hS hC _ _ _ _ hL0 _ n s)
    (r3_slot hRR hS hC _ _ hL0 _ n s))).trans_le ?_
  refine (congrArg (‖·‖) (congrArg₂ (fun x y => restrictTorus _ b x - restrictR3 b y)
    (hT hK T _ θ hT0 hT1 hl hl1 E Jt hlt hq hθ1 (Module.finBasis ℝ E i) n s)
    (hR F hFG hFD P k θ E J hP hk hq hθ1 (Module.finBasis ℝ E i) n s))).trans_le ?_
  exact hT₀b i T hT0 hT1 hTi Jt (hJt _) n s s.2.1 s.2.2

end Breakdown.Periodic
