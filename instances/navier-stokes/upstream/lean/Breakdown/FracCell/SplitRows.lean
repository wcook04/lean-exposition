import Breakdown.FracCell.StClauses
import Breakdown.FracCert.SplitFormBounds
import Breakdown.FracCell.SplitRowsTail

open scoped ContDiff ENNReal
open MeasureTheory Real Set

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

namespace Internal.SplitRows

theorem tail_le {s c x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hc : 0 < c) (hcx : c ≤ x) :
    ENNReal.ofReal (x ^ s - c ^ s) ≤ ∫⁻ l in Ioi c, ENNReal.ofReal (s * l ^ (s - 1) * ratioFn l x) := by
  have hx := hc.trans_le hcx
  have h := Internal.SplitRowsTail.tail_real hs0 hs1 hc hcx
  have hcb : c ≤ x * x / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  rw [intervalIntegral.integral_of_le hcb] at h
  have hI : IntegrableOn (fun l => s * l ^ (s - 1) * (x / (l + x))) (Ioc c (x * x / c)) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    intro l hl
    have hl0 : 0 < l := hc.trans_le hl.1
    exact ((continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hl0.ne'))).mul
      (continuousAt_const.div (continuousAt_id.add continuousAt_const)
        (by show l + x ≠ 0; linarith))).continuousWithinAt
  calc ENNReal.ofReal (x ^ s - c ^ s)
      ≤ ENNReal.ofReal (∫ l in Ioc c (x * x / c), s * l ^ (s - 1) * (x / (l + x))) := ENNReal.ofReal_le_ofReal h
    _ = ∫⁻ l in Ioc c (x * x / c), ENNReal.ofReal (s * l ^ (s - 1) * ratioFn l x) := by
        rw [ofReal_integral_eq_lintegral_ofReal hI]
        · rfl
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
          have hl0 : 0 < l := hc.trans hl.1
          exact mul_nonneg (mul_nonneg hs0.le (Real.rpow_nonneg hl0.le _)) (div_nonneg hx.le (by linarith))
    _ ≤ _ := lintegral_mono_set Ioc_subset_Ioi_self

theorem ratio_step {g g0 r r0 : ℝ} (hg0 : 0 ≤ g0) (hg : g0 ≤ g) (hr0 : 0 < r0) (hr : r0 ≤ r) :
    g ^ 2 / (g + r) ≤ g0 ^ 2 / (g0 + r0) + (g - g0) := by
  have h1 : g ^ 2 / (g + r) ≤ g ^ 2 / (g + r0) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  have n1 : g + r0 ≠ 0 := by linarith
  have n2 : g0 + r0 ≠ 0 := by linarith
  have e1 : g ^ 2 / (g + r0) = g - r0 + r0 ^ 2 / (g + r0) := by
    field_simp
    ring
  have e2 : g0 ^ 2 / (g0 + r0) = g0 - r0 + r0 ^ 2 / (g0 + r0) := by
    field_simp
    ring
  have h2 : r0 ^ 2 / (g + r0) ≤ r0 ^ 2 / (g0 + r0) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  linarith

theorem ratioFn_mono {l x y : ℝ} (hl : 0 < l) (hx : 0 ≤ x) (hxy : x ≤ y) : ratioFn l x ≤ ratioFn l y := by
  unfold ratioFn
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem ratioFn_nonneg {l x : ℝ} (hl : 0 < l) (hx : 0 ≤ x) : 0 ≤ ratioFn l x := by
  unfold ratioFn
  exact div_nonneg hx (by linarith)

theorem ratioFn_le_one {l x : ℝ} (hl : 0 < l) (hx : 0 ≤ x) : ratioFn l x ≤ 1 := by
  unfold ratioFn
  rw [div_le_one (by linarith)]
  linarith

variable {α : ℝ} {k N : ℕ} {c : FracCellData k N}

theorem splitVisc_pos (hc : IsFracCell α c) : 0 < c.splitVisc :=
  hc.base.coercivity_pos.trans hc.base.coercivity_lt

theorem cutoff_pos (hc : IsFracCell α c) : 0 < c.cutoff :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (splitVisc_pos hc) _) hc.cutoff_ge

theorem levelSum_mono (hc : IsFracCell α c) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    c.levelSum x ≤ c.levelSum y := by
  unfold FracCellData.levelSum
  gcongr with i
  · exact hc.levelCoef_nonneg i
  · exact ratioFn_mono (hc.levelRate_pos i) hx hxy

theorem levelSum_nonneg (hc : IsFracCell α c) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ c.levelSum x := by
  unfold FracCellData.levelSum
  exact add_nonneg hc.baseCoef_nonneg (Finset.sum_nonneg fun i _ =>
    mul_nonneg (hc.levelCoef_nonneg i) (ratioFn_nonneg (hc.levelRate_pos i) hx))

theorem symbol_le (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFracCell α c) {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (c.ratioSymbol α x) ≤ ENNReal.ofReal (c.levelSum x) +
      ∫⁻ l in Ioi c.cutoff, ENNReal.ofReal ((α - 1) * l ^ ((α - 1) - 1) * ratioFn l x) := by
  rcases le_or_gt x c.cutoff with h | h
  · exact (ENNReal.ofReal_le_ofReal (hc.symbol_fit x hx h)).trans le_self_add
  have hs : 0 < α - 1 := by linarith
  have hν := splitVisc_pos hc
  have hC := cutoff_pos hc
  have hνC : c.splitVisc ≤ c.cutoff ^ (α - 1) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hν.le _) hc.cutoff_ge hs.le
    rwa [← Real.rpow_mul hν.le, one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one] at this
  have hmono : c.cutoff ^ (α - 1) ≤ x ^ (α - 1) := Real.rpow_le_rpow hC.le h.le hs.le
  have hρ := hc.base.reduced_pos
  have hw := hc.base.weightMin_pos
  have hr : c.reducedCoercivity ≤ c.reducedCoercivity * (1 + c.weightMin / x) := by
    have : 0 ≤ c.weightMin / x := div_nonneg hw.le hx.le
    nlinarith
  have step := ratio_step (g := c.gapSymbol α x) (g0 := c.gapSymbol α c.cutoff)
    (by unfold FracCellData.gapSymbol; linarith) (by unfold FracCellData.gapSymbol; linarith) hρ hr
  have hend := hc.symbol_end
  have hlev := levelSum_mono hc hC.le h.le
  have hreal : c.ratioSymbol α x ≤ c.levelSum x + (x ^ (α - 1) - c.cutoff ^ (α - 1)) := by
    unfold FracCellData.ratioSymbol FracCellData.fullSymbol
    have e : c.gapSymbol α x - c.gapSymbol α c.cutoff = x ^ (α - 1) - c.cutoff ^ (α - 1) := by
      unfold FracCellData.gapSymbol; ring
    linarith
  calc ENNReal.ofReal (c.ratioSymbol α x)
      ≤ ENNReal.ofReal (c.levelSum x + (x ^ (α - 1) - c.cutoff ^ (α - 1))) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (c.levelSum x) + ENNReal.ofReal (x ^ (α - 1) - c.cutoff ^ (α - 1)) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := by
        gcongr
        exact tail_le hs (by linarith) hC h.le


theorem amgm_pt {g I A B F t : ℝ} (hI : |I| ≤ A * B) (hF : 0 < F) (ht : 0 < t) :
    g * I ≤ (t * (F * A ^ 2) + (g ^ 2 / F * B ^ 2) / t) / 2 := by
  have hq : (g ^ 2 / F * B ^ 2) / t * (t * F) = g ^ 2 * B ^ 2 := by
    field_simp
  have key : 2 * |g| * A * B * (t * F) ≤ (t * (F * A ^ 2) + (g ^ 2 / F * B ^ 2) / t) * (t * F) := by
    rw [add_mul, hq]
    nlinarith [sq_nonneg (t * F * A - |g| * B), sq_abs g]
  have k2 := le_of_mul_le_mul_right key (by positivity)
  have k3 : g * I ≤ |g| * (A * B) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hI (abs_nonneg _))
  linarith

theorem freqPow_pow (α : ℝ) (ξ : Space) : freqPow (2 * α - 2) ξ = freqPow 2 ξ ^ (α - 1) := by
  unfold freqPow
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem freqPow_nonneg (ξ : Space) : 0 ≤ freqPow 2 ξ := by
  unfold freqPow
  positivity

theorem freqPow_pos {ξ : Space} (hξ : ξ ≠ 0) : 0 < freqPow 2 ξ := by
  unfold freqPow
  have := norm_pos_iff.2 hξ
  positivity

theorem measurable_freqPow : Measurable fun ξ : Space => freqPow 2 ξ := by
  unfold freqPow
  fun_prop

theorem full_pos (hc : IsFracCell α c) {ξ : Space} (hξ : ξ ≠ 0) : 0 < c.fullSymbol α (freqPow 2 ξ) := by
  have hκ : 0 < 2 * π * ‖ξ‖ := by have := norm_pos_iff.2 hξ; positivity
  have hb := hc.base.formScale_bound _ hκ
  have e1 : freqPow 2 ξ = (2 * π * ‖ξ‖) ^ 2 := by
    unfold freqPow
    exact Real.rpow_two _
  have e2 : freqPow 2 ξ ^ (α - 1) = (2 * π * ‖ξ‖) ^ (2 * (α - 1)) := by
    rw [← freqPow_pow]
    unfold freqPow
    congr 1
    ring
  unfold FracCellData.fullSymbol FracCellData.gapSymbol
  rw [e2, e1]
  by_contra hn
  have hn := not_lt.mp hn
  nlinarith [sq_nonneg c.formScale]

theorem ratio_nonneg (hc : IsFracCell α c) {ξ : Space} (hξ : ξ ≠ 0) : 0 ≤ c.ratioSymbol α (freqPow 2 ξ) := by
  unfold FracCellData.ratioSymbol
  exact div_nonneg (sq_nonneg _) (full_pos hc hξ).le

theorem ae_ne_zero' : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
  have := (Set.countable_singleton (0 : Space)).ae_notMem volume
  filter_upwards [this] with ξ hξ
  simpa using hξ

open Internal.SplitFormBounds in
theorem pair_split (h2 : WeakPowerSymbolStatement) (hα1 : 1 < α) (hα2 : α < 5 / 4)
    (d : FracCertData k N) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    (hs : IsSecondOrderField m v G H) (hP : IsWeakFractionalPower α v P)
    {φ : Space → Space} (hφ : MemLp φ 2 volume) :
    Integrable (fun ξ => (freqPow 2 ξ ^ (α - 1) - d.splitVisc) *
      inner ℝ ((secondSymbol H : Space → Freq.CSpace) ξ) ((fieldSymbol φ : Space → Freq.CSpace) ξ)) ∧
    l2Pair (d.splitField P H) φ = ∫ ξ, (freqPow 2 ξ ^ (α - 1) - d.splitVisc) *
      inner ℝ ((secondSymbol H : Space → Freq.CSpace) ξ) ((fieldSymbol φ : Space → Freq.CSpace) ξ) := by
  have hsym := h2 α hα1 (by linarith) m v G H P hs hP
  have hw := memLp_trace hs
  have Ihf : Integrable (fun ξ => inner ℝ ((secondSymbol H : Space → Freq.CSpace) ξ)
      ((fieldSymbol φ : Space → Freq.CSpace) ξ)) :=
    L2.integrable_inner (𝕜 := ℝ) (secondSymbol H) (fieldSymbol φ)
  have IPf : Integrable (fun ξ => inner ℝ ((fieldSymbol P : Space → Freq.CSpace) ξ)
      ((fieldSymbol φ : Space → Freq.CSpace) ξ)) :=
    L2.integrable_inner (𝕜 := ℝ) (fieldSymbol P) (fieldSymbol φ)
  have hpt : (fun ξ => inner ℝ ((fieldSymbol P : Space → Freq.CSpace) ξ) ((fieldSymbol φ : Space → Freq.CSpace) ξ))
      =ᵐ[volume] fun ξ => freqPow 2 ξ ^ (α - 1) *
        inner ℝ ((secondSymbol H : Space → Freq.CSpace) ξ) ((fieldSymbol φ : Space → Freq.CSpace) ξ) := by
    filter_upwards [hsym] with ξ hξ
    rw [hξ, real_inner_smul_left, freqPow_pow]
  have I1 := IPf.congr hpt
  have Itot := I1.sub (Ihf.const_mul d.splitVisc)
  refine ⟨Itot.congr (Filter.Eventually.of_forall fun ξ => by simp only [Pi.sub_apply]; ring), ?_⟩
  have eP : l2Pair P φ = ∫ ξ, freqPow 2 ξ ^ (α - 1) *
      inner ℝ ((secondSymbol H : Space → Freq.CSpace) ξ) ((fieldSymbol φ : Space → Freq.CSpace) ξ) := by
    rw [pair_symbol hP.1 hφ]
    exact integral_congr_ae hpt
  have eN : l2Pair (negSecondTrace H) φ = ∫ ξ, inner ℝ ((secondSymbol H : Space → Freq.CSpace) ξ)
      ((fieldSymbol φ : Space → Freq.CSpace) ξ) := pair_symbol hw hφ
  have eS : l2Pair (d.splitField P H) φ = l2Pair P φ - d.splitVisc * l2Pair (negSecondTrace H) φ := by
    unfold l2Pair
    rw [← integral_const_mul, ← integral_sub (integrable_pair hP.1 hφ) ((integrable_pair hw hφ).const_mul _)]
    congr 1
    ext y
    simp only [FracCertData.splitField, negSecondTrace, inner_add_left, inner_neg_left, real_inner_smul_left]
    ring
  rw [eS, eP, eN, ← integral_const_mul, ← integral_sub I1 (Ihf.const_mul _)]
  congr 1
  ext ξ
  ring

open Internal.SplitFormBounds in
theorem pair_sum {F : Space → Space} (hF : MemLp F 2 volume) (e : Fin N → Space → Space)
    (he : ∀ b, MemLp (e b) 2 volume) (x : Fin N → ℝ) :
    l2Pair F (fun y => ∑ b, x b • e b y) = ∑ b, x b * l2Pair F (e b) := by
  unfold l2Pair
  simp only [inner_sum, real_inner_smul_right]
  rw [integral_finsetSum _ (fun b _ => (integrable_pair hF (he b)).const_mul (x b))]
  simp only [integral_const_mul]

theorem memLp_rows (hc : IsFracCell α c) (x : Fin N → ℝ) :
    MemLp (fun y => ∑ b, x b • c.row b y) 2 volume :=
  memLp_finsetSum _ fun b _ => (hc.base.row_two b).const_smul (x b)

open Internal.SplitFormBounds in
theorem norm_rows (hc : IsFracCell α c) (x : Fin N → ℝ) :
    ∫ ξ, ‖(fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace) ξ‖ ^ 2 = ∑ b, x b ^ 2 := by
  have hφ := memLp_rows hc x
  have e1 := pair_symbol hφ hφ
  simp only [real_inner_self_eq_norm_sq] at e1
  rw [← e1, pair_sum hφ _ (fun b => hc.base.row_two b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e2 : l2Pair (fun y => ∑ b, x b • c.row b y) (c.row b) = l2Pair (c.row b) (fun y => ∑ b, x b • c.row b y) := by
    unfold l2Pair
    simp only [real_inner_comm]
  rw [e2, pair_sum (hc.base.row_two b) _ (fun b => hc.base.row_two b)]
  simp only [hc.base.row_orthonormal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem smoothingForm_nonneg (lam : ℝ) (hlam : 0 < lam) (φ : Space → Space) : 0 ≤ smoothingForm lam φ := by
  unfold smoothingForm
  apply Real.sInf_nonneg
  rintro r ⟨ψ, Dψ, -, -, -, -, rfl⟩
  exact add_nonneg (integral_nonneg fun y => sq_nonneg _)
    (mul_nonneg (by positivity) (integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _))

theorem level_pt (hSL : SmoothingLowerStatement) (hc : IsFracCell α c) (x : Fin N → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Integrable (fun ξ => ratioFn lam (freqPow 2 ξ) *
      ‖(fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace) ξ‖ ^ 2) ∧
    ∫ ξ, ratioFn lam (freqPow 2 ξ) * ‖(fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace) ξ‖ ^ 2
      ≤ ∑ b, c.spectralBound (c.blockIndex b) lam * x b ^ 2 := by
  have hφ := memLp_rows hc x
  set f := (fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace)
  have In : Integrable (fun ξ => ‖f ξ‖ ^ 2) := (Lp.memLp _).integrable_norm_pow two_ne_zero
  have hm : Measurable fun ξ : Space => ratioFn lam (freqPow 2 ξ) :=
    measurable_freqPow.div (measurable_const.add measurable_freqPow)
  refine ⟨In.mono' (hm.aestronglyMeasurable.mul
      ((Lp.stronglyMeasurable _).aestronglyMeasurable.norm.pow 2)) (Filter.Eventually.of_forall fun ξ => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ratioFn_nonneg hlam (freqPow_nonneg ξ)) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (ratioFn_le_one hlam (freqPow_nonneg ξ))
  · exact (hSL lam hlam _ hφ).trans (hc.spectral_bound lam hlam x)

theorem tail_lint (hSL : SmoothingLowerStatement) (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFracCell α c)
    (x : Fin N → ℝ) (hK : 0 ≤ c.tailConst) :
    ∫⁻ ξ, (∫⁻ l in Ioi c.cutoff, ENNReal.ofReal ((α - 1) * l ^ ((α - 1) - 1) * ratioFn l (freqPow 2 ξ))) *
        ENNReal.ofReal (‖(fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace) ξ‖ ^ 2)
      ≤ ENNReal.ofReal ((∑ b, x b ^ 2) *
        ((α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1)))) := by
  set f := (fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace)
  have hs : 0 < α - 1 := by linarith
  have hC := cutoff_pos hc
  have hgm : Measurable fun ξ => ‖f ξ‖ ^ 2 := (Lp.stronglyMeasurable _).measurable.norm.pow_const 2
  have m1 : Measurable fun p : Space × ℝ => freqPow 2 p.1 := measurable_freqPow.comp measurable_fst
  have m2 : Measurable fun p : Space × ℝ => ‖f p.1‖ ^ 2 := hgm.comp measurable_fst
  have hW : Measurable (Function.uncurry fun (ξ : Space) (l : ℝ) =>
      ENNReal.ofReal ((α - 1) * l ^ ((α - 1) - 1) * ratioFn l (freqPow 2 ξ)) * ENNReal.ofReal (‖f ξ‖ ^ 2)) := by
    unfold ratioFn Function.uncurry
    fun_prop
  have hSx : 0 ≤ ∑ b, x b ^ 2 := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hA : 0 ≤ (α - 1) * c.tailConst * (∑ b, x b ^ 2) := by positivity
  calc _ = ∫⁻ ξ, ∫⁻ l in Ioi c.cutoff, ENNReal.ofReal ((α - 1) * l ^ ((α - 1) - 1) * ratioFn l (freqPow 2 ξ)) *
          ENNReal.ofReal (‖f ξ‖ ^ 2) := by
        refine lintegral_congr fun ξ => ?_
        rw [lintegral_mul_const]
        unfold ratioFn
        fun_prop
    _ = ∫⁻ l in Ioi c.cutoff, ∫⁻ ξ, ENNReal.ofReal ((α - 1) * l ^ ((α - 1) - 1) * ratioFn l (freqPow 2 ξ)) *
          ENNReal.ofReal (‖f ξ‖ ^ 2) := lintegral_lintegral_swap hW.aemeasurable
    _ ≤ ∫⁻ l in Ioi c.cutoff, ENNReal.ofReal ((α - 1) * c.tailConst * (∑ b, x b ^ 2) * l ^ ((α - 1) - 3 / 2)) := by
        refine setLIntegral_mono (by fun_prop) fun l hl => ?_
        have hl0 : 0 < l := hC.trans hl
        have hw0 : 0 ≤ (α - 1) * l ^ ((α - 1) - 1) := mul_nonneg hs.le (Real.rpow_nonneg hl0.le _)
        obtain ⟨Il, hle⟩ := level_pt hSL hc x hl0
        have e1 : ∫⁻ ξ, ENNReal.ofReal ((α - 1) * l ^ ((α - 1) - 1) * ratioFn l (freqPow 2 ξ)) *
            ENNReal.ofReal (‖f ξ‖ ^ 2) = ENNReal.ofReal (∫ ξ, (α - 1) * l ^ ((α - 1) - 1) *
              (ratioFn l (freqPow 2 ξ) * ‖f ξ‖ ^ 2)) := by
          rw [ofReal_integral_eq_lintegral_ofReal (Il.const_mul _) (Filter.Eventually.of_forall fun ξ =>
            mul_nonneg hw0 (mul_nonneg (ratioFn_nonneg hl0 (freqPow_nonneg ξ)) (sq_nonneg _)))]
          refine lintegral_congr fun ξ => ?_
          rw [← ENNReal.ofReal_mul (mul_nonneg hw0 (ratioFn_nonneg hl0 (freqPow_nonneg ξ)))]
          congr 1
          ring
        rw [e1]
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul]
        have h3 : ∑ b, c.spectralBound (c.blockIndex b) l * x b ^ 2 ≤
            c.tailConst * l ^ (-(1 / 2 : ℝ)) * ∑ b, x b ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun b _ =>
            mul_le_mul_of_nonneg_right (hc.spectral_tail b l hl.le) (sq_nonneg _)
        have h4 : l ^ ((α - 1) - 1) * l ^ (-(1 / 2 : ℝ)) = l ^ ((α - 1) - 3 / 2) := by
          rw [← Real.rpow_add hl0]
          congr 1
          ring
        calc (α - 1) * l ^ ((α - 1) - 1) * ∫ ξ, ratioFn l (freqPow 2 ξ) * ‖f ξ‖ ^ 2
            ≤ (α - 1) * l ^ ((α - 1) - 1) * (c.tailConst * l ^ (-(1 / 2 : ℝ)) * ∑ b, x b ^ 2) :=
              mul_le_mul_of_nonneg_left (hle.trans h3) hw0
          _ = (α - 1) * c.tailConst * (∑ b, x b ^ 2) * (l ^ ((α - 1) - 1) * l ^ (-(1 / 2 : ℝ))) := by ring
          _ = _ := by rw [h4]
    _ = ENNReal.ofReal ((∑ b, x b ^ 2) *
        ((α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1)))) := by
        have hI : IntegrableOn (fun l : ℝ => (α - 1) * c.tailConst * (∑ b, x b ^ 2) * l ^ ((α - 1) - 3 / 2))
            (Ioi c.cutoff) := (integrableOn_Ioi_rpow_of_lt (by linarith) hC).const_mul _
        rw [← ofReal_integral_eq_lintegral_ofReal hI (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
          exact mul_nonneg hA (Real.rpow_nonneg (hC.trans hl).le _))]
        congr 1
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hC]
        have e : (α - 1) - 3 / 2 + 1 = (α - 1) - 1 / 2 := by ring
        rw [e]
        rw [neg_div, ← div_neg, neg_sub]
        ring

theorem level_int (hSL : SmoothingLowerStatement) (hc : IsFracCell α c) (x : Fin N → ℝ) :
    Integrable (fun ξ => c.levelSum (freqPow 2 ξ) *
      ‖(fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace) ξ‖ ^ 2) ∧
    ∫ ξ, c.levelSum (freqPow 2 ξ) * ‖(fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace) ξ‖ ^ 2
      ≤ ∑ b, x b ^ 2 * (c.baseCoef + ∑ i, c.levelCoef i * c.spectralBound (c.blockIndex b) (c.levelRate i)) := by
  set f := (fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace)
  have In : Integrable (fun ξ => ‖f ξ‖ ^ 2) := (Lp.memLp _).integrable_norm_pow two_ne_zero
  have Ii : ∀ i, Integrable (fun ξ => c.levelCoef i * (ratioFn (c.levelRate i) (freqPow 2 ξ) * ‖f ξ‖ ^ 2)) :=
    fun i => (level_pt hSL hc x (hc.levelRate_pos i)).1.const_mul _
  have ept : (fun ξ => c.levelSum (freqPow 2 ξ) * ‖f ξ‖ ^ 2) = fun ξ => c.baseCoef * ‖f ξ‖ ^ 2 +
      ∑ i, c.levelCoef i * (ratioFn (c.levelRate i) (freqPow 2 ξ) * ‖f ξ‖ ^ 2) := by
    ext ξ
    simp only [FracCellData.levelSum, add_mul, Finset.sum_mul, mul_assoc]
  have Isum : Integrable (fun ξ => ∑ i, c.levelCoef i * (ratioFn (c.levelRate i) (freqPow 2 ξ) * ‖f ξ‖ ^ 2)) :=
    integrable_finsetSum _ fun i _ => Ii i
  rw [ept]
  refine ⟨(In.const_mul _).add Isum, ?_⟩
  rw [integral_add (In.const_mul _) Isum, integral_finsetSum _ fun i _ => Ii i, integral_const_mul]
  simp only [integral_const_mul]
  rw [norm_rows hc x]
  have eR : ∑ b, x b ^ 2 * (c.baseCoef + ∑ i, c.levelCoef i * c.spectralBound (c.blockIndex b) (c.levelRate i)) =
      c.baseCoef * ∑ b, x b ^ 2 + ∑ i, c.levelCoef i * ∑ b, c.spectralBound (c.blockIndex b) (c.levelRate i) * x b ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun b _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring
  rw [eR]
  gcongr with i
  · exact hc.levelCoef_nonneg i
  · exact (level_pt hSL hc x (hc.levelRate_pos i)).2

theorem ratio_int (hSL : SmoothingLowerStatement) (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFracCell α c)
    (x : Fin N → ℝ) (hK : 0 ≤ c.tailConst) :
    Integrable (fun ξ => c.ratioSymbol α (freqPow 2 ξ) *
      ‖(fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace) ξ‖ ^ 2) ∧
    ∫ ξ, c.ratioSymbol α (freqPow 2 ξ) * ‖(fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace) ξ‖ ^ 2
      ≤ ∑ b, x b ^ 2 * (c.baseCoef + ∑ i, c.levelCoef i * c.spectralBound (c.blockIndex b) (c.levelRate i)
        + (α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1))) := by
  obtain ⟨IL, hL⟩ := level_int hSL hc x
  have hT := tail_lint hSL hα1 hα2 hc x hK
  set f := (fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace)
  have hgm : Measurable fun ξ => ‖f ξ‖ ^ 2 := (Lp.stronglyMeasurable _).measurable.norm.pow_const 2
  have hmf := measurable_freqPow
  have hmR : Measurable fun ξ => c.ratioSymbol α (freqPow 2 ξ) * ‖f ξ‖ ^ 2 := by
    unfold FracCellData.ratioSymbol FracCellData.fullSymbol FracCellData.gapSymbol
    fun_prop
  have hmL : Measurable fun ξ => c.levelSum (freqPow 2 ξ) * ‖f ξ‖ ^ 2 := by
    unfold FracCellData.levelSum ratioFn
    fun_prop
  have hnn : 0 ≤ᵐ[volume] fun ξ => c.ratioSymbol α (freqPow 2 ξ) * ‖f ξ‖ ^ 2 := by
    filter_upwards [ae_ne_zero'] with ξ hξ
    exact mul_nonneg (ratio_nonneg hc hξ) (sq_nonneg _)
  have hs : 0 < α - 1 := by linarith
  have hB0 : 0 ≤ (∑ b, x b ^ 2) * ((α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1))) := by
    have : 0 < 1 / 2 - (α - 1) := by linarith
    have := cutoff_pos hc
    have : 0 ≤ ∑ b, x b ^ 2 := Finset.sum_nonneg fun b _ => sq_nonneg _
    positivity
  have hA0 : 0 ≤ ∫ ξ, c.levelSum (freqPow 2 ξ) * ‖f ξ‖ ^ 2 :=
    integral_nonneg fun ξ => mul_nonneg (levelSum_nonneg hc (freqPow_nonneg ξ)) (sq_nonneg _)
  have hlint : ∫⁻ ξ, ENNReal.ofReal (c.ratioSymbol α (freqPow 2 ξ) * ‖f ξ‖ ^ 2) ≤
      ENNReal.ofReal (∫ ξ, c.levelSum (freqPow 2 ξ) * ‖f ξ‖ ^ 2) +
      ENNReal.ofReal ((∑ b, x b ^ 2) * ((α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1)))) := by
    calc ∫⁻ ξ, ENNReal.ofReal (c.ratioSymbol α (freqPow 2 ξ) * ‖f ξ‖ ^ 2)
        ≤ ∫⁻ ξ, (ENNReal.ofReal (c.levelSum (freqPow 2 ξ) * ‖f ξ‖ ^ 2) +
          (∫⁻ l in Ioi c.cutoff, ENNReal.ofReal ((α - 1) * l ^ ((α - 1) - 1) * ratioFn l (freqPow 2 ξ))) *
            ENNReal.ofReal (‖f ξ‖ ^ 2)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_ne_zero'] with ξ hξ
          rw [ENNReal.ofReal_mul (ratio_nonneg hc hξ),
            ENNReal.ofReal_mul (levelSum_nonneg hc (freqPow_nonneg ξ)), ← add_mul]
          exact mul_le_mul_left (symbol_le hα1 hα2 hc (freqPow_pos hξ)) _
      _ = (∫⁻ ξ, ENNReal.ofReal (c.levelSum (freqPow 2 ξ) * ‖f ξ‖ ^ 2)) +
          ∫⁻ ξ, (∫⁻ l in Ioi c.cutoff, ENNReal.ofReal ((α - 1) * l ^ ((α - 1) - 1) * ratioFn l (freqPow 2 ξ))) *
            ENNReal.ofReal (‖f ξ‖ ^ 2) := lintegral_add_left hmL.ennreal_ofReal _
      _ ≤ _ := by
          rw [← ofReal_integral_eq_lintegral_ofReal IL (Filter.Eventually.of_forall fun ξ =>
            mul_nonneg (levelSum_nonneg hc (freqPow_nonneg ξ)) (sq_nonneg _))]
          exact add_le_add le_rfl hT
  have hfin : ∫⁻ ξ, ENNReal.ofReal (c.ratioSymbol α (freqPow 2 ξ) * ‖f ξ‖ ^ 2) < ⊤ :=
    lt_of_le_of_lt hlint (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  refine ⟨⟨hmR.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmR.aestronglyMeasurable]
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hlint
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hA0,
    ENNReal.toReal_ofReal hB0] at h1
  refine h1.trans ?_
  have e : ∑ b, x b ^ 2 * (c.baseCoef + ∑ i, c.levelCoef i * c.spectralBound (c.blockIndex b) (c.levelRate i)
        + (α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1))) =
      ∑ b, x b ^ 2 * (c.baseCoef + ∑ i, c.levelCoef i * c.spectralBound (c.blockIndex b) (c.levelRate i)) +
      (∑ b, x b ^ 2) * ((α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1))) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  linarith

theorem final_real {R E B : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → 2 * R ^ 2 ≤ t * E ^ 2 + B ^ 2 * R ^ 2 / t) : R ≤ B * E := by
  by_contra hlt
  have hlt := not_le.mp hlt
  have hRp : 0 < R := lt_of_le_of_lt (mul_nonneg hB hE) hlt
  rcases hE.eq_or_lt with hE0 | hEp
  · have h1 := h (B ^ 2 + 1) (by positivity)
    rw [← hE0] at h1
    have h2 : B ^ 2 * R ^ 2 / (B ^ 2 + 1) ≤ R ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg R]
    nlinarith
  · rcases hB.eq_or_lt with hB0 | hBp
    · have h1 := h (R ^ 2 / E ^ 2) (by positivity)
      rw [← hB0] at h1
      have e : R ^ 2 / E ^ 2 * E ^ 2 = R ^ 2 := div_mul_cancel₀ _ (by positivity)
      have e2 : (0 : ℝ) ^ 2 * R ^ 2 / (R ^ 2 / E ^ 2) = 0 := by simp
      rw [e, e2] at h1
      nlinarith
    · have h1 := h (B * R / E) (by positivity)
      have e1 : B * R / E * E ^ 2 = B * R * E := by field_simp
      have e2 : B ^ 2 * R ^ 2 / (B * R / E) = B * R * E := by field_simp
      rw [e1, e2] at h1
      nlinarith

open Internal.SplitFormBounds in
theorem energy_eq (h1 : SecondSymbolEnergyStatement) (h3 : WeakPowerSymbolStatement) (hα1 : 1 < α)
    (hα2 : α < 5 / 4) (hc : IsFracCell α c) {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    (hs : IsSecondOrderField c.order v G H) (hP : IsWeakFractionalPower α v P) :
    0 ≤ c.toFracCertData.splitEnergy P G H ∧
    Integrable (fun ξ => c.fullSymbol α (freqPow 2 ξ) * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) ∧
    c.toFracCertData.splitEnergy P G H ^ 2 =
      ∫ ξ, c.fullSymbol α (freqPow 2 ξ) * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 := by
  obtain ⟨Iy, eG, -, eX⟩ := h1 c.order v G H hs
  have hw := memLp_trace hs
  obtain ⟨Ig, eg⟩ := pair_split h3 hα1 hα2 c.toFracCertData hs hP hw
  have hsq : ∀ ξ, inner ℝ ((secondSymbol H : Space → Freq.CSpace) ξ)
      ((fieldSymbol (negSecondTrace H) : Space → Freq.CSpace) ξ) = ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 :=
    fun ξ => real_inner_self_eq_norm_sq _
  simp only [hsq] at Ig eg
  have In : Integrable (fun ξ => ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) :=
    (Lp.memLp (secondSymbol H)).integrable_norm_pow two_ne_zero
  have ept : (fun ξ => c.fullSymbol α (freqPow 2 ξ) * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) =
      fun ξ => (freqPow 2 ξ ^ (α - 1) - c.splitVisc) * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 +
        (c.reducedCoercivity * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 +
          c.reducedCoercivity * c.weightMin * (‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ)) := by
    ext ξ
    unfold FracCellData.fullSymbol FracCellData.gapSymbol
    ring
  have Itot : Integrable (fun ξ => c.fullSymbol α (freqPow 2 ξ) * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) := by
    rw [ept]
    exact Ig.add ((In.const_mul c.reducedCoercivity).add (Iy.const_mul (c.reducedCoercivity * c.weightMin)))
  have hE : ∫ ξ, c.fullSymbol α (freqPow 2 ξ) * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 =
      l2Pair (c.toFracCertData.splitField P H) (negSecondTrace H) +
        c.reducedCoercivity * ((∫ y, ‖secondTrace (H y)‖ ^ 2) + c.weightMin * ∫ y, entrySq (G y)) := by
    have I2 : Integrable (fun ξ => c.reducedCoercivity * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 +
        c.reducedCoercivity * c.weightMin * (‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ)) :=
      (In.const_mul _).add (Iy.const_mul _)
    rw [ept, integral_add Ig I2, integral_add (In.const_mul _) (Iy.const_mul _), integral_const_mul,
      integral_const_mul, eg, eX, eG]
    ring
  have h0 : 0 ≤ ∫ ξ, c.fullSymbol α (freqPow 2 ξ) * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_ne_zero'] with ξ hξ
    exact mul_nonneg (full_pos hc hξ).le (sq_nonneg _)
  refine ⟨Real.sqrt_nonneg _, Itot, ?_⟩
  unfold FracCertData.splitEnergy
  rw [← hE, Real.sq_sqrt h0]

theorem tailConst_nonneg (hc : IsFracCell α c) (b0 : Fin N) : 0 ≤ c.tailConst := by
  have hC := cutoff_pos hc
  have h0 := (smoothingForm_nonneg c.cutoff hC _).trans (hc.spectral_bound c.cutoff hC (Pi.single b0 1))
  rw [Finset.sum_eq_single b0 (fun b _ hb => by simp [hb]) (by simp)] at h0
  simp only [Pi.single_eq_same, one_pow, mul_one] at h0
  have h1 := hc.spectral_tail b0 c.cutoff le_rfl
  have hp : 0 < c.cutoff ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hC _
  by_contra hn
  have hn := not_le.mp hn
  nlinarith

theorem splitRows_main (hSL : SmoothingLowerStatement) (h1 : SecondSymbolEnergyStatement)
    (h3 : WeakPowerSymbolStatement) (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFracCell α c)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {P : Space → Space} (hs : IsSecondOrderField c.order v G H) (hP : IsWeakFractionalPower α v P) :
    rowSize c.row c.rowWeight (c.toFracCertData.splitField P H) ≤
      c.splitBound * c.toFracCertData.splitEnergy P G H := by
  obtain ⟨hE0, IE, hEsq⟩ := energy_eq h1 h3 hα1 hα2 hc hs hP
  set F := c.toFracCertData.splitField P H with hFdef
  set E := c.toFracCertData.splitEnergy P G H
  set y : Fin N → ℝ := fun a => l2Pair F (c.row a) with hy
  have hR0 : 0 ≤ rowSize c.row c.rowWeight F := Real.sqrt_nonneg _
  have hRsq : rowSize c.row c.rowWeight F ^ 2 = ∑ a, c.rowWeight a * y a ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun a _ => mul_nonneg (hc.base.rowWeight_pos a).le (sq_nonneg _))
  set R := rowSize c.row c.rowWeight F
  have hB := hc.base.splitBound_nonneg
  rcases hR0.eq_or_lt with hR | hR
  · rw [← hR]
    exact mul_nonneg hB hE0
  have hN : Nonempty (Fin N) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : R ^ 2 = 0 := by rw [hRsq]; exact Finset.sum_of_isEmpty _
    nlinarith
  obtain ⟨b0⟩ := hN
  have hK := tailConst_nonneg hc b0
  have hw := Internal.SplitFormBounds.memLp_trace hs
  have hT : MemLp (fun y => c.splitVisc • secondTrace (H y)) 2 volume :=
    (hw.const_smul (-c.splitVisc)).ae_eq (Filter.Eventually.of_forall fun y => by
      simp [negSecondTrace, smul_neg, neg_smul])
  have hF : MemLp F 2 volume := hP.1.add hT
  set x : Fin N → ℝ := fun a => c.rowWeight a * y a with hx
  have hφ := memLp_rows hc x
  obtain ⟨Iφ, eφ⟩ := pair_split h3 hα1 hα2 c.toFracCertData hs hP hφ
  obtain ⟨Ir, hr⟩ := ratio_int hSL hα1 hα2 hc x hK
  have hpair : l2Pair F (fun y => ∑ b, x b • c.row b y) = R ^ 2 := by
    rw [pair_sum hF _ (fun b => hc.base.row_two b), hRsq]
    exact Finset.sum_congr rfl fun b _ => by simp only [hx, hy]; ring
  have hrb : ∫ ξ, c.ratioSymbol α (freqPow 2 ξ) *
      ‖(fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace) ξ‖ ^ 2 ≤ c.splitBound ^ 2 * R ^ 2 := by
    refine hr.trans ?_
    rw [hRsq, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have hb := hc.splitBound_ge b
    have hτ := (hc.base.rowWeight_pos b).le
    have e : x b ^ 2 * (c.baseCoef + ∑ i, c.levelCoef i * c.spectralBound (c.blockIndex b) (c.levelRate i)
        + (α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1))) =
        (c.rowWeight b * y b ^ 2) * (c.rowWeight b * (c.baseCoef + ∑ i, c.levelCoef i *
          c.spectralBound (c.blockIndex b) (c.levelRate i)
        + (α - 1) * c.tailConst * c.cutoff ^ ((α - 1) - 1 / 2) / (1 / 2 - (α - 1)))) := by
      simp only [hx]
      ring
    rw [e]
    calc _ ≤ (c.rowWeight b * y b ^ 2) * c.splitBound ^ 2 :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg hτ (sq_nonneg _))
      _ = _ := by ring
  refine final_real hE0 hB fun t ht => ?_
  set f := (fieldSymbol (fun y => ∑ b, x b • c.row b y) : Space → Freq.CSpace)
  set h := (secondSymbol H : Space → Freq.CSpace)
  have Irhs : Integrable (fun ξ => (t * (c.fullSymbol α (freqPow 2 ξ) * ‖h ξ‖ ^ 2) +
      (c.ratioSymbol α (freqPow 2 ξ) * ‖f ξ‖ ^ 2) / t) / 2) :=
    ((IE.const_mul t).add (Ir.div_const t)).div_const 2
  have hint := integral_mono_ae Iφ Irhs (by
    filter_upwards [ae_ne_zero'] with ξ hξ
    unfold FracCellData.ratioSymbol
    exact amgm_pt (g := c.gapSymbol α (freqPow 2 ξ)) ((abs_real_inner_le_norm _ _))
      (full_pos hc hξ) ht)
  rw [← eφ, hpair, integral_div, integral_add (IE.const_mul t) (Ir.div_const t), integral_const_mul,
    integral_div, ← hEsq] at hint
  have h4 : (∫ ξ, c.ratioSymbol α (freqPow 2 ξ) * ‖f ξ‖ ^ 2) / t ≤ c.splitBound ^ 2 * R ^ 2 / t :=
    div_le_div_of_nonneg_right hrb ht.le
  linarith

end Internal.SplitRows

open Internal.SplitRows in
theorem splitRows_of (h1 : SmoothingLowerStatement) (h2 : SteadyCert.SecondSymbolEnergyStatement)
    (h3 : SteadyCert.WeakPowerSymbolStatement) : SplitRowsStatement :=
  fun _ hα1 hα2 _ _ _ hc _ _ _ hs _ hP => splitRows_main h1 h2 h3 hα1 hα2 hc hs hP


end CellCert

end Breakdown
