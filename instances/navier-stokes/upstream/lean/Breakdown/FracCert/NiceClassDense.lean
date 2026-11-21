import Breakdown.FracCert.StFreeNice
import Breakdown.Frac.NNiceField
import Breakdown.FreqTr.NiceDense
import Breakdown.FreqTr.BilinRotate
import Breakdown.FreqTr.Realization
import Breakdown.Cert.CoerciveTestDensityProof
import Breakdown.Cert.Invariance
import Breakdown.Cert.ProjectionSpec

open scoped ContDiff ENNReal FourierTransform SchwartzMap
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

private theorem integral_inner_eq (R : Freq.L2R) {b : Space → Space} (hb : MemLp b 2 volume) :
    ∫ y, inner ℝ (R y) (b y) = inner ℝ R (Freq.toLpOrZero 2 b) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Freq.Internal.H1Consistency.toLpOrZero_ae hb] with y hy
  rw [hy]

open Freq Cert Cert.Internal.ProjectionSpec in
private theorem transform_mem_sig (F : Space → Space) (hF : IsSolenoidalL2 F) :
    Freq.freqTrR (Freq.complexify (Freq.toLpOrZero 2 F)) ∈ Freq.Sig := by
  set T : L2R := toLpOrZero 2 F with hTdef
  set f : L2C := freqTrR (complexify T) with hfdef
  set x : HBar := solProj T with hxdef
  have hxf : (x : L2C) = f - fieldOp id longitudinal f := solProj_coe T
  set R : L2R := T - toPhys (x : L2C) with hRdef
  have hRhat : freqTrR (complexify R) = fieldOp id longitudinal f := by
    rw [hRdef, map_sub, map_sub, freqTrR_complexify_toPhys x.2, hxf, ← hfdef]
    abel
  have hzero : ∀ᵐ y ∂volume, (R : Space → Space) y = 0 := by
    refine Coercive.Internal.TestDensityProof.slice_zero (Lp.memLp R) (fun c hc hcs => ?_) (fun w hw => ?_)
    · have hg := Coercive.Internal.TestDensityProof.gradient_memLp hc hcs
      set C : L2C := freqTrR (complexify (toLpOrZero 2 (gradientAt c))) with hCdef
      have hCP : fieldOp id longitudinal C = C := by
        have h0 := congrArg (fun z : HBar => (z : L2C)) (Cert.Internal.Invariance.solField_gradientAt
          (hc.of_le (by simp)) hg)
        simp only [solField, solProj_coe, ZeroMemClass.coe_zero] at h0
        exact (sub_eq_zero.1 h0).symm
      rw [integral_inner_eq R hg, ← inner_transform, hRhat, ← hCdef, inner_fieldOp_longitudinal, hCP,
        hfdef, inner_transform, hTdef, ← integral_inner_eq _ hg]
      have e : ∫ y, inner ℝ ((toLpOrZero 2 F : L2R) y) (gradientAt c y) = ∫ y, inner ℝ (F y) (gradientAt c y) := by
        apply integral_congr_ae
        filter_upwards [Freq.Internal.H1Consistency.toLpOrZero_ae hF.1] with y hy
        rw [hy]
      rw [e]
      exact hF.2 c ⟨hc, hcs⟩
    · have hw2 : MemLp w 2 volume := Freq.Internal.BilinTestFormula.test_memLp hw 2
      have hmem := Freq.Internal.H1Consistency.hat_mem_sig fieldOpRealized_holds
        (Freq.freqTrConjSym fieldOpRealized_holds) (Cert.Internal.TestDense.isH1Field_of_test hw)
      rw [integral_inner_eq R hw2, ← inner_transform, hRhat, inner_fieldOp_longitudinal,
        fieldOp_longitudinal_of_mem hmem, inner_zero_right]
  have hR0 : R = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hzero] with y h1
    rw [h1]
    rfl
  rw [Freq.Internal.H1Consistency.mem_sig_iff]
  refine ⟨Freq.freqTrConjSym fieldOpRealized_holds T, ?_⟩
  rw [← hRhat, hR0, map_zero, map_zero]

open Freq Freq.Internal.NiceDense in
private theorem symbol_close (f : Space → CSpace) (hf2 : MemLp f 2 volume)
    (hsym : ∀ᵐ ξ ∂volume, conjVec (f (-ξ)) = f ξ) (hdiv : ∀ᵐ ξ ∂volume, longitudinal ξ (f ξ) = 0)
    (δ : ℝ) (hδ : 0 < δ) : ∃ m, IsNiceSymbol m ∧ eLpNorm (m - f) 2 volume < ENNReal.ofReal δ := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨n, hn⟩ := (tail_small hf2 hδ2).exists
  have hmeas : MeasurableSet (outerSet n) := by
    unfold outerSet
    exact (measurableSet_lt measurable_norm measurable_const).union
      (measurableSet_lt measurable_const measurable_norm)
  set r : ℝ := 1 / ((n : ℝ) + 1) with hrdef
  set R : ℝ := (n : ℝ) + 1 with hRdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : 0 < r := by positivity
  have hrR : r ≤ R := by
    have : r ≤ 1 := by rw [hrdef, div_le_one (by positivity)]; linarith
    linarith
  set f₁ : Space → CSpace := (outerSet n)ᶜ.indicator f with hf₁def
  have hf₁supp : ∀ ξ, ‖ξ‖ < r ∨ R < ‖ξ‖ → f₁ ξ = 0 := by
    intro ξ hξ
    apply Set.indicator_of_notMem
    exact fun hc => hc hξ
  have hf₁2 : MemLp f₁ 2 volume := hf2.indicator hmeas.compl
  have hff₁ : f = f₁ + (outerSet n).indicator f := (Set.indicator_compl_add_self _ _).symm
  obtain ⟨m₀, hm₀, hm₀0, hm₀R, hm₀err⟩ := smooth_annulus hf₁2 hr hrR hf₁supp hδ2
  obtain ⟨hnice, -⟩ := nice_symField_projField hm₀ (half_pos hr) hm₀0 hm₀R
  set m : Space → CSpace := symField (projField m₀) with hmdef
  have hf₁sym : ∀ᵐ ξ ∂volume, conjVec (f₁ (-ξ)) = f₁ ξ := by
    filter_upwards [hsym] with ξ h
    by_cases hξ : ξ ∈ outerSet n
    · have h' : -ξ ∈ outerSet n := by simpa [outerSet] using hξ
      simp [hf₁def, hξ, h']
    · have h' : -ξ ∉ outerSet n := by simpa [outerSet] using hξ
      simp [hf₁def, hξ, h', h]
  have hf₁proj : ∀ᵐ ξ ∂volume, longitudinal ξ (f₁ ξ) = 0 := by
    filter_upwards [hdiv] with ξ h
    by_cases hξ : ξ ∈ outerSet n
    · simp [hf₁def, hξ]
    · simp [hf₁def, hξ, h]
  have hpm : AEStronglyMeasurable (projField m₀) volume :=
    (contDiff_projField hm₀ (half_pos hr) hm₀0).continuous.aestronglyMeasurable
  have herr1 : eLpNorm (m - f₁) 2 volume < ENNReal.ofReal (δ / 2) := by
    calc eLpNorm (m - f₁) 2 volume ≤ eLpNorm (projField m₀ - f₁) 2 volume :=
          eLpNorm_symField_sub_le hpm hf₁2.aestronglyMeasurable hf₁sym
      _ ≤ eLpNorm (m₀ - f₁) 2 volume := by
          apply eLpNorm_mono_ae
          filter_upwards [hf₁proj] with ξ h
          have e : (projField m₀ - f₁) ξ = (m₀ ξ - f₁ ξ) - longitudinal ξ (m₀ ξ - f₁ ξ) := by
            simp only [Pi.sub_apply, projField, map_sub, h]
            abel
          rw [e]
          exact norm_proj_le ξ _
      _ < ENNReal.ofReal (δ / 2) := hm₀err
  have hmc : AEStronglyMeasurable m volume := hnice.1.continuous.aestronglyMeasurable
  refine ⟨m, hnice, ?_⟩
  have e : m - f = (m - f₁) - (outerSet n).indicator f := by
    funext ξ
    have := congrFun hff₁ ξ
    simp only [Pi.add_apply] at this
    simp only [Pi.sub_apply]
    rw [this]
    abel
  rw [e]
  calc eLpNorm ((m - f₁) - (outerSet n).indicator f) 2 volume
      ≤ eLpNorm (m - f₁) 2 volume + eLpNorm ((outerSet n).indicator f) 2 volume :=
        eLpNorm_sub_le (hmc.sub hf₁2.aestronglyMeasurable)
          (hf2.aestronglyMeasurable.indicator hmeas) (by norm_num)
    _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := ENNReal.add_lt_add herr1 hn
    _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add hδ2.le hδ2.le, add_halves]

open Freq in
private theorem norm_complexify_eq (v : L2R) : ‖complexify v‖ = ‖v‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec v] with x hx
  change ‖(complexify v : Space → CSpace) x‖ = _
  rw [complexify, hx]
  exact Freq.Internal.BilinCompact.norm_complexifyVec _

private theorem integral_sq_eq (u : Lp (α := Space) Space 2) (g : Space → Space)
    (h : (u : Space → Space) =ᵐ[volume] g) : ∫ y, ‖g y‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [← hy, real_inner_self_eq_norm_sq]

open Freq Breakdown.FracInternal.NiceField in
private theorem transform_field {m : Space → CSpace} (hm : IsNiceSymbol m) :
    freqTrR (complexify ((fieldS hm).toLp 2)) = (symbolS hm).toLp 2 := by
  rw [Freq.Internal.FreqTrConjSym.complexify_toLp, Freq.Internal.FreqTrConjSym.freqTrR_toLp]
  congr 1
  ext x
  rw [SchwartzMap.fourier_coe]
  have e : ⇑(SchwartzMap.postcompCLM (𝕜 := ℝ) complexifyVec (fieldS hm)) =
      fun x => complexifyVec (fieldS hm x) := by
    funext y
    rw [SchwartzMap.postcompCLM_apply]
  rw [e, transform_fieldS hm, symbolS_coe]

open Freq Breakdown.FracInternal.NiceField in
private theorem dense_of_mem_sig (F : Space → Space) (hF : MemLp F 2 volume)
    (hS : Freq.freqTrR (Freq.complexify (Freq.toLpOrZero 2 F)) ∈ Freq.Sig) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Space → Freq.CSpace, Freq.IsNiceSymbol s ∧ ∫ y, ‖F y - Freq.niceField s y‖ ^ 2 < ε := by
  set f0 : L2C := freqTrR (complexify (toLpOrZero 2 F)) with hf0
  obtain ⟨hsym, hdiv⟩ := Freq.Internal.NiceDense.sig_ae fieldOpRealized_holds ⟨f0, hS⟩
  obtain ⟨m, hm, herr⟩ := symbol_close (f0 : Space → CSpace) (Lp.memLp _) hsym hdiv (Real.sqrt ε)
    (Real.sqrt_pos.2 hε)
  refine ⟨m, hm, ?_⟩
  have hT : toLpOrZero 2 F = hF.toLp F := by rw [toLpOrZero, dif_pos hF]
  set N : L2R := (fieldS hm).toLp 2 volume with hN
  have hae : ((hF.toLp F - N : L2R) : Space → Space) =ᵐ[volume] fun y => F y - niceField m y := by
    filter_upwards [Lp.coeFn_sub (hF.toLp F) N, hF.coeFn_toLp, (fieldS hm).coeFn_toLp 2 volume]
      with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, hN, h3, fieldS_coe]
  rw [integral_sq_eq _ _ hae]
  have hnorm : ‖hF.toLp F - N‖ = ‖f0 - (symbolS hm).toLp 2 volume‖ := by
    rw [hf0, hT, ← transform_field hm, ← map_sub, ← map_sub, ← norm_complexify_eq]
    exact (Freq.freqTrL2.norm_map _).symm
  have hlt : ‖f0 - (symbolS hm).toLp 2 volume‖ < Real.sqrt ε := by
    rw [Lp.norm_def]
    have hae2 : ((f0 - (symbolS hm).toLp 2 volume : L2C) : Space → CSpace) =ᵐ[volume] -(m - (f0 : Space → CSpace)) := by
      filter_upwards [Lp.coeFn_sub f0 ((symbolS hm).toLp 2 volume), (symbolS hm).coeFn_toLp 2 volume] with y h1 h2
      rw [h1, Pi.sub_apply, h2, symbolS_coe]
      simp
    rw [eLpNorm_congr_ae hae2, eLpNorm_neg]
    exact ENNReal.toReal_lt_of_lt_ofReal herr
  rw [hnorm]
  exact (Real.lt_sqrt (norm_nonneg _)).1 hlt

private def turnFun (θ : ℝ) (y : Space) : Space :=
  EuclideanSpace.single 0 (Real.cos θ * y 0 - Real.sin θ * y 1) +
    EuclideanSpace.single 1 (Real.sin θ * y 0 + Real.cos θ * y 1) +
    EuclideanSpace.single 2 (y 2)

private theorem turnFun_apply (θ : ℝ) (y : Space) :
    turnFun θ y 0 = Real.cos θ * y 0 - Real.sin θ * y 1 ∧
    turnFun θ y 1 = Real.sin θ * y 0 + Real.cos θ * y 1 ∧ turnFun θ y 2 = y 2 := by
  simp [turnFun]

private theorem mirror_apply (y : Space) : mirror y 0 = y 0 ∧ mirror y 1 = y 1 ∧ mirror y 2 = -(y 2) := by
  simp [mirror]

private theorem space_ext {y z : Space} (h0 : y 0 = z 0) (h1 : y 1 = z 1) (h2 : y 2 = z 2) : y = z := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem turnFun_comp (a b : ℝ) (y : Space) : turnFun a (turnFun b y) = turnFun (a + b) y := by
  obtain ⟨h0, h1, h2⟩ := turnFun_apply b y
  obtain ⟨k0, k1, k2⟩ := turnFun_apply a (turnFun b y)
  obtain ⟨l0, l1, l2⟩ := turnFun_apply (a + b) y
  apply space_ext
  · rw [k0, l0, h0, h1, Real.cos_add, Real.sin_add]; ring
  · rw [k1, l1, h0, h1, Real.cos_add, Real.sin_add]; ring
  · rw [k2, l2, h2]

private theorem turnFun_zero (y : Space) : turnFun 0 y = y := by
  obtain ⟨h0, h1, h2⟩ := turnFun_apply 0 y
  apply space_ext
  · rw [h0]; simp
  · rw [h1]; simp
  · rw [h2]

private theorem turnFun_period (θ : ℝ) (j : ℕ) (y : Space) : turnFun (θ + 2 * π * j) y = turnFun θ y := by
  obtain ⟨h0, h1, h2⟩ := turnFun_apply (θ + 2 * π * j) y
  obtain ⟨l0, l1, l2⟩ := turnFun_apply θ y
  have hc : Real.cos (θ + 2 * π * j) = Real.cos θ := by
    rw [show 2 * π * (j : ℝ) = (j : ℕ) * (2 * π) by ring, Real.cos_add_nat_mul_two_pi]
  have hs : Real.sin (θ + 2 * π * j) = Real.sin θ := by
    rw [show 2 * π * (j : ℝ) = (j : ℕ) * (2 * π) by ring, Real.sin_add_nat_mul_two_pi]
  apply space_ext
  · rw [h0, l0, hc, hs]
  · rw [h1, l1, hc, hs]
  · rw [h2, l2]

private theorem norm_turnFun (θ : ℝ) (y : Space) : ‖turnFun θ y‖ = ‖y‖ := by
  obtain ⟨h0, h1, h2⟩ := turnFun_apply θ y
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_three, h0, h1, h2]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq θ

private theorem norm_mirror (y : Space) : ‖mirror y‖ = ‖y‖ := by
  obtain ⟨h0, h1, h2⟩ := mirror_apply y
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_three, h0, h1, h2]
  simp only [Real.norm_eq_abs, sq_abs, neg_sq]

private theorem turnFun_add (θ : ℝ) (y z : Space) : turnFun θ (y + z) = turnFun θ y + turnFun θ z := by
  obtain ⟨h0, h1, h2⟩ := turnFun_apply θ y
  obtain ⟨k0, k1, k2⟩ := turnFun_apply θ z
  obtain ⟨l0, l1, l2⟩ := turnFun_apply θ (y + z)
  apply space_ext
  · rw [PiLp.add_apply, l0, h0, k0, PiLp.add_apply, PiLp.add_apply]; ring
  · rw [PiLp.add_apply, l1, h1, k1, PiLp.add_apply, PiLp.add_apply]; ring
  · rw [PiLp.add_apply, l2, h2, k2, PiLp.add_apply]

private theorem turnFun_smul (θ c : ℝ) (y : Space) : turnFun θ (c • y) = c • turnFun θ y := by
  obtain ⟨h0, h1, h2⟩ := turnFun_apply θ y
  obtain ⟨l0, l1, l2⟩ := turnFun_apply θ (c • y)
  apply space_ext
  · rw [PiLp.smul_apply, l0, h0, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]; ring
  · rw [PiLp.smul_apply, l1, h1, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]; ring
  · rw [PiLp.smul_apply, l2, h2, PiLp.smul_apply]

private theorem mirror_add (y z : Space) : mirror (y + z) = mirror y + mirror z := by
  obtain ⟨h0, h1, h2⟩ := mirror_apply y
  obtain ⟨k0, k1, k2⟩ := mirror_apply z
  obtain ⟨l0, l1, l2⟩ := mirror_apply (y + z)
  apply space_ext
  · rw [PiLp.add_apply, l0, h0, k0, PiLp.add_apply]
  · rw [PiLp.add_apply, l1, h1, k1, PiLp.add_apply]
  · rw [PiLp.add_apply, l2, h2, k2, PiLp.add_apply]; ring

private theorem mirror_smul (c : ℝ) (y : Space) : mirror (c • y) = c • mirror y := by
  obtain ⟨h0, h1, h2⟩ := mirror_apply y
  obtain ⟨l0, l1, l2⟩ := mirror_apply (c • y)
  apply space_ext
  · rw [PiLp.smul_apply, l0, h0, PiLp.smul_apply]
  · rw [PiLp.smul_apply, l1, h1, PiLp.smul_apply]
  · rw [PiLp.smul_apply, l2, h2, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]; ring

private theorem mirror_mirror (y : Space) : mirror (mirror y) = y := by
  obtain ⟨h0, h1, h2⟩ := mirror_apply y
  obtain ⟨l0, l1, l2⟩ := mirror_apply (mirror y)
  apply space_ext
  · rw [l0, h0]
  · rw [l1, h1]
  · rw [l2, h2, neg_neg]

private theorem mirror_turnFun (θ : ℝ) (y : Space) : mirror (turnFun θ y) = turnFun θ (mirror y) := by
  obtain ⟨h0, h1, h2⟩ := turnFun_apply θ y
  obtain ⟨k0, k1, k2⟩ := mirror_apply (turnFun θ y)
  obtain ⟨l0, l1, l2⟩ := turnFun_apply θ (mirror y)
  obtain ⟨m0, m1, m2⟩ := mirror_apply y
  apply space_ext
  · rw [k0, l0, h0, m0, m1]
  · rw [k1, l1, h1, m0, m1]
  · rw [k2, l2, h2, m2]

private def turnIso (θ : ℝ) : Space ≃ₗᵢ[ℝ] Space :=
  { toFun := turnFun θ
    invFun := turnFun (-θ)
    map_add' := turnFun_add θ
    map_smul' := turnFun_smul θ
    left_inv := fun y => by
      show turnFun (-θ) (turnFun θ y) = y
      rw [turnFun_comp, neg_add_cancel, turnFun_zero]
    right_inv := fun y => by
      show turnFun θ (turnFun (-θ) y) = y
      rw [turnFun_comp, add_neg_cancel, turnFun_zero]
    norm_map' := norm_turnFun θ }

private theorem turnIso_apply (θ : ℝ) (y : Space) : turnIso θ y = turnFun θ y := rfl

private def mirrorIso : Space ≃ₗᵢ[ℝ] Space :=
  { toFun := mirror
    invFun := mirror
    map_add' := mirror_add
    map_smul' := mirror_smul
    left_inv := mirror_mirror
    right_inv := mirror_mirror
    norm_map' := norm_mirror }

private theorem mirrorIso_apply (y : Space) : mirrorIso y = mirror y := rfl

private def angle (n : ℕ) (k : Fin (n + 1)) : ℝ := 2 * π * (k : ℕ) / ((n : ℝ) + 1)

private def elem (n : ℕ) (i : Fin (n + 1) × Bool) : Space ≃ₗᵢ[ℝ] Space :=
  if i.2 then mirrorIso.trans (turnIso (angle n i.1)) else turnIso (angle n i.1)

private theorem elem_apply (n : ℕ) (i : Fin (n + 1) × Bool) (y : Space) :
    elem n i y = turnFun (angle n i.1) (if i.2 then mirror y else y) := by
  unfold elem
  split_ifs <;> rfl

private theorem angle_succ (n : ℕ) (k : Fin (n + 1)) (y : Space) :
    turnFun (angle n (k + 1)) y = turnFun (2 * π / ((n : ℝ) + 1)) (turnFun (angle n k) y) := by
  rw [turnFun_comp]
  have hv : ((k + 1 : Fin (n + 1)) : ℕ) = ((k : ℕ) + 1) % (n + 1) := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have hd := Nat.mod_add_div ((k : ℕ) + 1) (n + 1)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have e : 2 * π / ((n : ℝ) + 1) + angle n k =
      angle n (k + 1) + 2 * π * ((((k : ℕ) + 1) / (n + 1) : ℕ) : ℝ) := by
    unfold angle
    rw [hv]
    have hd' : ((((k : ℕ) + 1) % (n + 1) : ℕ) : ℝ) + ((n : ℝ) + 1) * ((((k : ℕ) + 1) / (n + 1) : ℕ) : ℝ) =
        (k : ℕ) + 1 := by exact_mod_cast hd
    field_simp
    linear_combination (-1 : ℝ) * hd'
  rw [e, turnFun_period]

private theorem elem_turn (n : ℕ) (i : Fin (n + 1) × Bool) (y : Space) :
    elem n (i.1 + 1, i.2) y = turnFun (2 * π / ((n : ℝ) + 1)) (elem n i y) := by
  rw [elem_apply, elem_apply, angle_succ]

private theorem elem_mirror (n : ℕ) (i : Fin (n + 1) × Bool) (y : Space) :
    elem n (i.1, !i.2) y = mirror (elem n i y) := by
  rw [elem_apply, elem_apply, mirror_turnFun]
  cases i.2 <;> simp [mirror_mirror]

private theorem symm_of_comp {L K : Space ≃ₗᵢ[ℝ] Space} {T : Space → Space} (h : ∀ y, L y = T (K y))
    (y : Space) : L.symm (T y) = K.symm y := by
  rw [LinearIsometryEquiv.symm_apply_eq, h, LinearIsometryEquiv.apply_symm_apply]

open Freq Freq.Internal.Rotation in
private theorem realVec_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : realVec (rotC R z) = R (realVec z) := by
  ext i
  rw [apply_eq_sum]
  simp only [realVec, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    rotC_apply, Complex.re_sum, Complex.re_ofReal_mul]

open Freq Freq.Internal.Rotation in
private theorem div_rotC (R : Space ≃ₗᵢ[ℝ] Space) (ξ : Space) (z : CSpace) :
    ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * rotC R z i = ∑ j : Fin 3, (((R.symm ξ) j : ℝ) : ℂ) * z j := by
  simp only [rotC_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [apply_eq_sum R.symm ξ j]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [symm_unit]
  ring

private def avgSym (n : ℕ) (s : Space → Freq.CSpace) (ξ : Space) : Freq.CSpace :=
  (1 / (2 * ((n : ℝ) + 1)) : ℝ) • ∑ i : Fin (n + 1) × Bool, Freq.rotC (elem n i) (s ((elem n i).symm ξ))

open Freq Freq.Internal.Rotation in
private theorem avgSym_nice (n : ℕ) {s : Space → CSpace} (hs : IsNiceSymbol s) : IsNiceSymbol (avgSym n s) := by
  obtain ⟨hc, hcs, ⟨r, hr, h0⟩, hh, hd⟩ := hs
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  have hout : ∀ ξ : Space, R < ‖ξ‖ → s ξ = 0 := by
    intro ξ hξ
    by_contra hne
    have := hR (subset_tsupport _ hne)
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  refine ⟨?_, ?_, ⟨r, hr, fun ξ hξ => ?_⟩, fun ξ => ?_, fun ξ => ?_⟩
  · unfold avgSym
    refine ContDiff.const_smul _ (ContDiff.sum fun i _ => ?_)
    exact (rotC (elem n i)).contDiff.comp (hc.comp (elem n i).symm.contDiff)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) (fun ξ hξ => ?_)
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hξ
    unfold avgSym
    rw [Finset.sum_eq_zero, smul_zero]
    intro i _
    rw [hout _ (by rwa [LinearIsometryEquiv.norm_map]), map_zero]
  · unfold avgSym
    rw [Finset.sum_eq_zero, smul_zero]
    intro i _
    rw [h0 _ (by rwa [LinearIsometryEquiv.norm_map]), map_zero]
  · unfold avgSym
    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_neg, hh, conjVec_rotC]
  · unfold avgSym
    have e : ∀ i : Fin 3, ((ξ i : ℝ) : ℂ) * ((1 / (2 * ((n : ℝ) + 1)) : ℝ) •
        ∑ j : Fin (n + 1) × Bool, rotC (elem n j) (s ((elem n j).symm ξ))) i =
        (((1 / (2 * ((n : ℝ) + 1)) : ℝ) : ℂ) * ∑ j : Fin (n + 1) × Bool,
          ((ξ i : ℝ) : ℂ) * rotC (elem n j) (s ((elem n j).symm ξ)) i) := by
      intro i
      rw [PiLp.smul_apply, Complex.real_smul, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    rw [div_rotC]
    exact hd _

open Freq Freq.Internal.BilinRotate Breakdown.FracInternal.NiceField in
private theorem niceField_avgSym (n : ℕ) {s : Space → CSpace} (hs : IsNiceSymbol s) (x : Space) :
    niceField (avgSym n s) x = (1 / (2 * ((n : ℝ) + 1)) : ℝ) •
      ∑ i : Fin (n + 1) × Bool, elem n i (niceField s ((elem n i).symm x)) := by
  set S := symbolS hs with hSdef
  have hfun : avgSym n s = fun ξ => (1 / (2 * ((n : ℝ) + 1)) : ℝ) •
      ∑ i : Fin (n + 1) × Bool, rotRapid (elem n i) S ξ := by
    funext ξ
    unfold avgSym
    refine congrArg _ (Finset.sum_congr rfl (fun i _ => ?_))
    rw [rotRapid_apply, hSdef, symbolS_coe]
  have hint : ∀ i, Integrable (fun v : Space => 𝐞 (inner ℝ v x) • rotRapid (elem n i) S v) volume := by
    intro i
    refine (rotRapid (elem n i) S).integrable.mono ?_ (ae_of_all _ fun v => ?_)
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        (rotRapid (elem n i) S).continuous).aestronglyMeasurable
    · simp [Circle.smul_def, norm_smul, Circle.norm_coe]
  have hF : 𝓕⁻ (avgSym n s) x = (1 / (2 * ((n : ℝ) + 1)) : ℝ) •
      ∑ i : Fin (n + 1) × Bool, rotC (elem n i) ((𝓕⁻ s) ((elem n i).symm x)) := by
    rw [hfun, Real.fourierInv_eq]
    have e : ∀ v : Space, 𝐞 (inner ℝ v x) • ((1 / (2 * ((n : ℝ) + 1)) : ℝ) •
        ∑ i : Fin (n + 1) × Bool, rotRapid (elem n i) S v) =
        (1 / (2 * ((n : ℝ) + 1)) : ℝ) • ∑ i : Fin (n + 1) × Bool, 𝐞 (inner ℝ v x) • rotRapid (elem n i) S v := by
      intro v
      simp only [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Circle.smul_def, Circle.smul_def, smul_comm]
    simp_rw [e]
    rw [integral_smul, integral_finsetSum _ (fun i _ => hint i)]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : (𝓕⁻ (rotRapid (elem n i) S)) x = (rotRapid (elem n i) (𝓕⁻ S)) x := by
      rw [freqTrInv_rotRapid]
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, rotRapid_apply, SchwartzMap.fourierInv_coe,
      hSdef, symbolS_coe] at h1
    exact h1
  show realVec (𝓕⁻ (avgSym n s) x) = _
  rw [hF, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [realVec_rotC]
  rfl

private def shiftEquiv (n : ℕ) : (Fin (n + 1) × Bool) ≃ (Fin (n + 1) × Bool) :=
  Equiv.prodCongr (Equiv.addRight 1) (Equiv.refl Bool)

private def boolFlip : Bool ≃ Bool :=
  ⟨fun b => !b, fun b => !b, fun b => Bool.not_not b, fun b => Bool.not_not b⟩

private def flipEquiv (n : ℕ) : (Fin (n + 1) × Bool) ≃ (Fin (n + 1) × Bool) :=
  Equiv.prodCongr (Equiv.refl _) boolFlip

open Freq in
private theorem avg_turn (n : ℕ) {s : Space → CSpace} (hs : IsNiceSymbol s) (y : Space) :
    niceField (avgSym n s) (turnFun (2 * π / ((n : ℝ) + 1)) y) =
      turnFun (2 * π / ((n : ℝ) + 1)) (niceField (avgSym n s) y) := by
  rw [niceField_avgSym n hs, niceField_avgSym n hs]
  change _ = turnIso (2 * π / ((n : ℝ) + 1)) _
  rw [map_smul, map_sum]
  congr 1
  refine (Fintype.sum_equiv (shiftEquiv n) _ _ (fun i => ?_)).symm
  have hc : ∀ z, elem n (shiftEquiv n i) z = turnFun (2 * π / ((n : ℝ) + 1)) (elem n i z) :=
    fun z => elem_turn n i z
  rw [symm_of_comp hc, hc, turnIso_apply]

open Freq in
private theorem avg_mirror (n : ℕ) {s : Space → CSpace} (hs : IsNiceSymbol s) (y : Space) :
    niceField (avgSym n s) (mirror y) = mirror (niceField (avgSym n s) y) := by
  rw [niceField_avgSym n hs, niceField_avgSym n hs]
  change _ = mirrorIso _
  rw [map_smul, map_sum]
  congr 1
  refine (Fintype.sum_equiv (flipEquiv n) _ _ (fun i => ?_)).symm
  have hc : ∀ z, elem n (flipEquiv n i) z = mirror (elem n i z) := fun z => elem_mirror n i z
  rw [symm_of_comp hc, hc, mirrorIso_apply]

private theorem equiv_comp {F : Space → Space} {A : Space → Space} (B : Space ≃ₗᵢ[ℝ] Space)
    (hA : ∀ᵐ y ∂volume, F (A y) = A (F y)) (hB : ∀ᵐ y ∂volume, F (B y) = B (F y)) :
    ∀ᵐ y ∂volume, F (A (B y)) = A (B (F y)) := by
  have h2 := B.measurePreserving.quasiMeasurePreserving.tendsto_ae.eventually hA
  filter_upwards [hB, h2] with y h1 h2
  rw [h2, h1]

private theorem equiv_turn_pow {F : Space → Space} (θ : ℝ)
    (hT : ∀ᵐ y ∂volume, F (turnFun θ y) = turnFun θ (F y)) (j : ℕ) :
    ∀ᵐ y ∂volume, F (turnFun (j * θ) y) = turnFun (j * θ) (F y) := by
  induction j with
  | zero => exact Filter.Eventually.of_forall fun y => by simp [turnFun_zero]
  | succ j ih =>
    have h := equiv_comp (turnIso (j * θ)) hT ih
    filter_upwards [h] with y hy
    simp only [turnIso_apply, turnFun_comp] at hy
    have e : θ + j * θ = ((j + 1 : ℕ) : ℝ) * θ := by push_cast; ring
    rw [e] at hy
    exact hy

private theorem equiv_elem {F : Space → Space} (n : ℕ)
    (hT : ∀ᵐ y ∂volume, F (turnFun (2 * π / ((n : ℝ) + 1)) y) = turnFun (2 * π / ((n : ℝ) + 1)) (F y))
    (hM : ∀ᵐ y ∂volume, F (mirror y) = mirror (F y)) (i : Fin (n + 1) × Bool) :
    ∀ᵐ y ∂volume, F (elem n i y) = elem n i (F y) := by
  have hk := equiv_turn_pow _ hT (i.1 : ℕ)
  have ha : ((i.1 : ℕ) : ℝ) * (2 * π / ((n : ℝ) + 1)) = angle n i.1 := by
    unfold angle; ring
  rw [ha] at hk
  obtain ⟨k, e⟩ := i
  cases e
  · filter_upwards [hk] with y hy
    simpa [elem_apply] using hy
  · have h := equiv_comp mirrorIso hk hM
    filter_upwards [h] with y hy
    simpa [elem_apply, mirrorIso_apply] using hy

open Freq Breakdown.FracInternal.NiceField in
private theorem avg_le (n : ℕ) {s : Space → CSpace} (hs : IsNiceSymbol s) (F : Space → Space)
    (hF : MemLp F 2 volume) (heq : ∀ i, ∀ᵐ y ∂volume, F (elem n i y) = elem n i (F y)) :
    ∫ y, ‖F y - niceField (avgSym n s) y‖ ^ 2 ≤ ∫ y, ‖F y - niceField s y‖ ^ 2 := by
  set c : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcard : c * (Fintype.card (Fin (n + 1) × Bool) : ℝ) = 1 := by
    rw [hc, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast
    field_simp
  have hnf : ∀ {t : Space → CSpace}, IsNiceSymbol t → MemLp (niceField t) 2 volume := by
    intro t ht
    have h := (fieldS ht).memLp 2 (μ := volume)
    rwa [fieldS_coe] at h
  set D : Space → Space := fun y => F y - niceField s y with hD
  have hDm : MemLp D 2 volume := hF.sub (hnf hs)
  have hback : ∀ i, ∀ᵐ x ∂volume, F x = elem n i (F ((elem n i).symm x)) := by
    intro i
    have h := (elem n i).symm.measurePreserving.quasiMeasurePreserving.tendsto_ae.eventually (heq i)
    filter_upwards [h] with x hx
    rw [LinearIsometryEquiv.apply_symm_apply] at hx
    exact hx
  have hpt : ∀ᵐ x ∂volume, ‖F x - niceField (avgSym n s) x‖ ^ 2 ≤
      c * ∑ i : Fin (n + 1) × Bool, ‖D ((elem n i).symm x)‖ ^ 2 := by
    filter_upwards [ae_all_iff.2 hback] with x hx
    have hFx : F x = c • ∑ i : Fin (n + 1) × Bool, elem n i (F ((elem n i).symm x)) := by
      rw [← Finset.sum_congr rfl (fun i _ => hx i), Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hcard, one_smul]
    have e : F x - niceField (avgSym n s) x =
        c • ∑ i : Fin (n + 1) × Bool, elem n i (D ((elem n i).symm x)) := by
      rw [niceField_avgSym n hs]
      conv_lhs => rw [hFx]
      rw [← smul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hD, map_sub]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, mul_pow]
    have h1 : ‖∑ i : Fin (n + 1) × Bool, elem n i (D ((elem n i).symm x))‖ ≤
        ∑ i : Fin (n + 1) × Bool, ‖D ((elem n i).symm x)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact LinearIsometryEquiv.norm_map _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (n + 1) × Bool)))
      (f := fun i => ‖D ((elem n i).symm x)‖)
    rw [Finset.card_univ] at h2
    have h3 : ‖∑ i : Fin (n + 1) × Bool, elem n i (D ((elem n i).symm x))‖ ^ 2 ≤
        (Fintype.card (Fin (n + 1) × Bool) : ℝ) * ∑ i : Fin (n + 1) × Bool, ‖D ((elem n i).symm x)‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    calc c ^ 2 * ‖∑ i : Fin (n + 1) × Bool, elem n i (D ((elem n i).symm x))‖ ^ 2
        ≤ c ^ 2 * ((Fintype.card (Fin (n + 1) × Bool) : ℝ) *
          ∑ i : Fin (n + 1) × Bool, ‖D ((elem n i).symm x)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = c * ∑ i : Fin (n + 1) × Bool, ‖D ((elem n i).symm x)‖ ^ 2 := by
          rw [← mul_assoc, sq, mul_assoc c c, hcard, mul_one]
  have hterm : ∀ i : Fin (n + 1) × Bool, Integrable (fun x => ‖D ((elem n i).symm x)‖ ^ 2) volume := by
    intro i
    have h := hDm.comp_measurePreserving (elem n i).symm.measurePreserving
    exact (memLp_two_iff_integrable_sq_norm h.1).1 h
  have hL : MemLp (fun y => F y - niceField (avgSym n s) y) 2 volume := hF.sub (hnf (avgSym_nice n hs))
  calc ∫ y, ‖F y - niceField (avgSym n s) y‖ ^ 2
      ≤ ∫ x, c * ∑ i : Fin (n + 1) × Bool, ‖D ((elem n i).symm x)‖ ^ 2 :=
        integral_mono_ae ((memLp_two_iff_integrable_sq_norm hL.1).1 hL)
          ((integrable_finsetSum _ (fun i _ => hterm i)).const_mul c) hpt
    _ = ∫ y, ‖F y - niceField s y‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ (fun i _ => hterm i)]
        have hi : ∀ i : Fin (n + 1) × Bool, ∫ x, ‖D ((elem n i).symm x)‖ ^ 2 = ∫ y, ‖D y‖ ^ 2 :=
          fun i => (elem n i).symm.measurePreserving.integral_comp
            (elem n i).symm.toHomeomorph.measurableEmbedding (fun y => ‖D y‖ ^ 2)
        rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← mul_assoc, hcard, one_mul]

private theorem turnStep_eq (m : ℕ) (y : Space) : turnStep m y = turnFun (2 * π / m) y := rfl

private theorem turnFun_full (y : Space) : turnFun (2 * π / ((0 : ℕ) + 1 : ℝ)) y = y := by
  have h := turnFun_period 0 1 y
  rw [turnFun_zero] at h
  simpa using h

open Freq in
private theorem classAverage (m : ℕ) (s : Space → Freq.CSpace) (hs : Freq.IsNiceSymbol s) :
    ∃ s' : Space → Freq.CSpace, Freq.IsNiceSymbol s' ∧ IsClassField m (Freq.niceField s') ∧
      ∀ F : Space → Space, MemLp F 2 volume → IsClassField m F →
        ∫ y, ‖F y - Freq.niceField s' y‖ ^ 2 ≤ ∫ y, ‖F y - Freq.niceField s y‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    have h0 : ∀ y, turnStep 0 y = y := fun y => by
      rw [turnStep_eq, Nat.cast_zero, div_zero, turnFun_zero]
    refine ⟨avgSym 0 s, avgSym_nice 0 hs, ⟨Filter.Eventually.of_forall fun y => by rw [h0, h0],
      Filter.Eventually.of_forall fun y => avg_mirror 0 hs y⟩, fun F hF hcl => ?_⟩
    refine avg_le 0 hs F hF (equiv_elem 0 (Filter.Eventually.of_forall fun y => ?_) hcl.2)
    rw [turnFun_full, turnFun_full]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h
    have hstep : ∀ y, turnStep (0 + n + 1) y = turnFun (2 * π / ((n : ℝ) + 1)) y := fun y => by
      rw [turnStep_eq]
      congr 2
      push_cast
      ring
    refine ⟨avgSym n s, avgSym_nice n hs, ⟨Filter.Eventually.of_forall fun y => by
      rw [hstep, hstep, avg_turn n hs], Filter.Eventually.of_forall fun y => avg_mirror n hs y⟩,
      fun F hF hcl => ?_⟩
    refine avg_le n hs F hF (equiv_elem n ?_ hcl.2)
    filter_upwards [hcl.1] with y hy
    rwa [hstep, hstep] at hy

theorem niceClassDense : NiceClassDenseStatement := by
  intro m F hF hcl ε hε
  obtain ⟨s, hs, hlt⟩ := dense_of_mem_sig F hF.1 (transform_mem_sig F hF) ε hε
  obtain ⟨s', hs', hcl', hle⟩ := classAverage m s hs
  exact ⟨s', hs', hcl', lt_of_le_of_lt (hle F hF.1 hcl) hlt⟩

end SteadyCert

end Breakdown
