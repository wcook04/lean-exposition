import Breakdown.FracCert.StHeldParts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace SecondTraceSolenoidalInternal

def dirDeriv (j : Fin 3) (f : Space → ℝ) : Space → ℝ := fun y => fderiv ℝ f y (unitVector j)

def diagSum (f : Space → ℝ) : Space → ℝ := fun y => ∑ j : Fin 3, dirDeriv j (dirDeriv j f) y

theorem contDiff_dirDeriv {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (dirDeriv j f) :=
  (contDiff_infty_iff_fderiv.1 hf).2.clm_apply contDiff_const

theorem test_dirDeriv {f : Space → ℝ} (hf : IsTestScalar f) (j : Fin 3) : IsTestScalar (dirDeriv j f) :=
  ⟨contDiff_dirDeriv hf.1 j, hf.2.fderiv_apply (𝕜 := ℝ) (unitVector j)⟩

theorem differentiable_of_smooth {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

theorem dirDeriv_dirDeriv {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) (y : Space) :
    dirDeriv i (dirDeriv j f) y = fderiv ℝ (fderiv ℝ f) y (unitVector i) (unitVector j) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((contDiff_infty_iff_fderiv.1 hf).2.differentiable (by simp)) y
  show fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) y (unitVector i) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem dirDeriv_comm {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) :
    dirDeriv i (dirDeriv j f) = dirDeriv j (dirDeriv i f) := by
  funext y
  rw [dirDeriv_dirDeriv hf, dirDeriv_dirDeriv hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top) _ _

theorem diagSum_eq (f : Space → ℝ) :
    diagSum f = fun y => dirDeriv 0 (dirDeriv 0 f) y + dirDeriv 1 (dirDeriv 1 f) y +
      dirDeriv 2 (dirDeriv 2 f) y := by
  funext y
  simp [diagSum, Fin.sum_univ_three]

theorem test_diagSum {f : Space → ℝ} (hf : IsTestScalar f) : IsTestScalar (diagSum f) := by
  have h0 := test_dirDeriv (test_dirDeriv hf 0) 0
  have h1 := test_dirDeriv (test_dirDeriv hf 1) 1
  have h2 := test_dirDeriv (test_dirDeriv hf 2) 2
  rw [diagSum_eq]
  exact ⟨(h0.1.add h1.1).add h2.1, (h0.2.add h1.2).add h2.2⟩

theorem diagSum_dirDeriv {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    diagSum (dirDeriv i f) = dirDeriv i (diagSum f) := by
  have hd : ∀ j, Differentiable ℝ (dirDeriv j (dirDeriv j f)) := fun j =>
    differentiable_of_smooth (contDiff_dirDeriv (contDiff_dirDeriv hf j) j)
  have hc : ∀ j, dirDeriv j (dirDeriv j (dirDeriv i f)) = dirDeriv i (dirDeriv j (dirDeriv j f)) := by
    intro j
    rw [dirDeriv_comm hf j i, dirDeriv_comm (contDiff_dirDeriv hf j) j i]
  funext y
  have hsum : HasFDerivAt (diagSum f) (fderiv ℝ (dirDeriv 0 (dirDeriv 0 f)) y +
      fderiv ℝ (dirDeriv 1 (dirDeriv 1 f)) y + fderiv ℝ (dirDeriv 2 (dirDeriv 2 f)) y) y := by
    rw [diagSum_eq]
    exact (((hd 0) y).hasFDerivAt.add ((hd 1) y).hasFDerivAt).add ((hd 2) y).hasFDerivAt
  show ∑ j : Fin 3, dirDeriv j (dirDeriv j (dirDeriv i f)) y = fderiv ℝ (diagSum f) y (unitVector i)
  rw [hsum.fderiv, Fin.sum_univ_three, hc 0, hc 1, hc 2]
  simp only [ContinuousLinearMap.add_apply]
  rfl

theorem integrable_test_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    {p : ℝ≥0∞} (hf : MemLp f p volume) (hp : 1 ≤ p) {ψ : Space → ℝ} (hψ : IsTestScalar ψ) :
    Integrable (fun y => ψ y • f y) volume :=
  (hf.locallyIntegrable hp).integrable_smul_left_of_hasCompactSupport hψ.1.continuous hψ.2

theorem memLp_column {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (h2 : Integrable fun y => entrySq (G y)) (i : Fin 3) :
    MemLp (fun y => G y (unitVector i)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector i)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hG
  refine (memLp_two_iff_integrable_sq_norm hm).2 (h2.mono' (hm.norm.pow 2) ?_)
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact Finset.single_le_sum (f := fun k => ‖G y (unitVector k)‖ ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ i)

theorem memLp_entry {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume)
    (h2 : Integrable fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)
    (j : Fin 3) : MemLp (fun y => H y (unitVector j) (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector j)) volume :=
    ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous).comp_aestronglyMeasurable hH
  refine (memLp_two_iff_integrable_sq_norm hm).2 (h2.mono' (hm.norm.pow 2) ?_)
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact (Finset.single_le_sum (f := fun k => ‖H y (unitVector j) (unitVector k)‖ ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ k : Fin 3, ‖H y (unitVector i) (unitVector k)‖ ^ 2)
      (fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ j))

variable {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
  {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}

theorem memLp_trace (h : IsSecondOrderField m v G H) :
    MemLp (fun y => secondTrace (H y)) 2 volume := by
  have := memLp_finset_sum (Finset.univ : Finset (Fin 3))
    (f := fun j y => H y (unitVector j) (unitVector j))
    (fun j _ => memLp_entry h.measurable_second h.second_two j)
  exact this

theorem weak_diag (h : IsSecondOrderField m v G H) {ψ : Space → ℝ} (hψ : IsTestScalar ψ) :
    ∫ y, ψ y • secondTrace (H y) = ∫ y, diagSum ψ y • v y := by
  have e1 : ∀ j, ∫ y, ψ y • H y (unitVector j) (unitVector j) =
      ∫ y, dirDeriv j (dirDeriv j ψ) y • v y := by
    intro j
    have a := h.weak_second ψ hψ j j
    have b := h.weak_gradient (dirDeriv j ψ) (test_dirDeriv hψ j) j
    simp only [dirDeriv] at b ⊢
    rw [b, a, neg_neg]
  have hH : ∀ j, Integrable (fun y => ψ y • H y (unitVector j) (unitVector j)) := fun j =>
    integrable_test_smul (memLp_entry h.measurable_second h.second_two j) one_le_two hψ
  have hv : ∀ j, Integrable (fun y => dirDeriv j (dirDeriv j ψ) y • v y) := fun j =>
    integrable_test_smul h.velocity_six (by norm_num) (test_dirDeriv (test_dirDeriv hψ j) j)
  calc ∫ y, ψ y • secondTrace (H y) = ∑ j : Fin 3, ∫ y, ψ y • H y (unitVector j) (unitVector j) := by
        rw [← integral_finset_sum _ (fun j _ => hH j)]
        simp only [secondTrace, Finset.smul_sum]
    _ = ∑ j : Fin 3, ∫ y, dirDeriv j (dirDeriv j ψ) y • v y := Finset.sum_congr rfl fun j _ => e1 j
    _ = ∫ y, diagSum ψ y • v y := by
        rw [← integral_finset_sum _ (fun j _ => hv j)]
        simp only [diagSum, Finset.sum_smul]

theorem solenoidal (h : IsSecondOrderField m v G H) {φ : Space → ℝ} (hφ : IsTestScalar φ) :
    ∫ y, inner ℝ (negSecondTrace H y) (gradientAt φ y) = 0 := by
  have hS := memLp_trace h
  have hint : ∀ i, Integrable (fun y => dirDeriv i φ y • secondTrace (H y)) := fun i =>
    integrable_test_smul hS one_le_two (test_dirDeriv hφ i)
  have hGi : ∀ i, Integrable (fun y => diagSum φ y • G y (unitVector i)) := fun i =>
    integrable_test_smul (memLp_column h.measurable_gradient h.gradient_two i) one_le_two (test_diagSum hφ)
  have step : ∀ i, inner ℝ (unitVector i) (∫ y, dirDeriv i φ y • secondTrace (H y)) =
      -∫ y, diagSum φ y * inner ℝ (G y (unitVector i)) (unitVector i) := by
    intro i
    rw [weak_diag h (test_dirDeriv hφ i), diagSum_dirDeriv hφ.1 i]
    have hw := h.weak_gradient (diagSum φ) (test_diagSum hφ) i
    change inner ℝ (unitVector i) (∫ y, fderiv ℝ (diagSum φ) y (unitVector i) • v y) = _
    rw [hw, inner_neg_right, ← integral_inner (hGi i)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [real_inner_smul_right, real_inner_comm]
  have pt : ∀ y, inner ℝ (negSecondTrace H y) (gradientAt φ y) =
      -∑ i : Fin 3, inner ℝ (unitVector i) (dirDeriv i φ y • secondTrace (H y)) := by
    intro y
    rw [negSecondTrace, inner_neg_left, gradientAt, inner_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]
    rfl
  have hprod : ∀ i, Integrable (fun y => diagSum φ y * inner ℝ (G y (unitVector i)) (unitVector i)) :=
    fun i => ((hGi i).inner_const (unitVector i)).congr
      (Filter.Eventually.of_forall fun y => real_inner_smul_left _ _ _)
  have hz : (fun y => ∑ i : Fin 3, diagSum φ y * inner ℝ (G y (unitVector i)) (unitVector i))
      =ᵐ[volume] fun _ => (0 : ℝ) := by
    filter_upwards [h.divergence] with y hy
    rw [← Finset.mul_sum, hy, mul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall pt), integral_neg,
    integral_finset_sum _ (fun i _ => (hint i).const_inner _)]
  rw [Finset.sum_congr rfl fun i _ => (integral_inner (hint i) (unitVector i)).trans (step i)]
  rw [Finset.sum_neg_distrib, neg_neg, ← integral_finset_sum _ (fun i _ => hprod i),
    integral_congr_ae hz, integral_zero]

theorem trace_iso_aux (A : Space ≃ₗᵢ[ℝ] Space) (B : Space →L[ℝ] Space →L[ℝ] ℝ) :
    ∑ j : Fin 3, B (A (unitVector j)) (A (unitVector j)) =
      ∑ k : Fin 3, ∑ l : Fin 3, inner ℝ (unitVector k) (unitVector l) * B (unitVector k) (unitVector l) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hbj : ∀ j, b j = unitVector j := fun j => by
    simp only [b, EuclideanSpace.basisFun_apply]
    rfl
  have expand : ∀ x : Space, B x x = ∑ k : Fin 3, ∑ l : Fin 3,
      (inner ℝ (unitVector k) x * inner ℝ (unitVector l) x) * B (unitVector k) (unitVector l) := by
    intro x
    have hx := b.sum_repr' x
    simp only [hbj] at hx
    conv_lhs => rw [← hx]
    simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have orth : ∀ k l, ∑ j : Fin 3, inner ℝ (unitVector k) (A (unitVector j)) *
      inner ℝ (unitVector l) (A (unitVector j)) = inner ℝ (unitVector k) (unitVector l) := by
    intro k l
    have hs := (b.map A).sum_inner_mul_inner (unitVector k) (unitVector l)
    simp only [OrthonormalBasis.map_apply, hbj] at hs
    rw [← hs]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm (A (unitVector j)) (unitVector l)]
  rw [Finset.sum_congr rfl fun j _ => expand (A (unitVector j))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_mul, orth]

theorem trace_iso (A : Space ≃ₗᵢ[ℝ] Space) (B : Space →L[ℝ] Space →L[ℝ] ℝ) :
    ∑ j : Fin 3, B (A (unitVector j)) (A (unitVector j)) = ∑ j : Fin 3, B (unitVector j) (unitVector j) := by
  rw [trace_iso_aux A B, ← trace_iso_aux (LinearIsometryEquiv.refl ℝ Space) B]
  rfl

theorem fderiv_comp_iso (A : Space ≃ₗᵢ[ℝ] Space) (g : Space → ℝ) (y w : Space) :
    fderiv ℝ (fun x => g (A x)) y w = fderiv ℝ g (A y) (A w) := by
  have h1 := A.toContinuousLinearEquiv.comp_right_fderiv (f := g) (x := y)
  exact congrArg (fun L => L w) h1

theorem diagSum_comp_iso (A : Space ≃ₗᵢ[ℝ] Space) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (y : Space) :
    diagSum (fun x => f (A x)) y = diagSum f (A y) := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.1 hf).2.differentiable (by simp)
  have e : ∀ j, dirDeriv j (dirDeriv j (fun x => f (A x))) y =
      fderiv ℝ (fderiv ℝ f) (A y) (A (unitVector j)) (A (unitVector j)) := by
    intro j
    have h1 : dirDeriv j (fun x => f (A x)) = fun x => (fun z => fderiv ℝ f z (A (unitVector j))) (A x) := by
      funext x
      exact fderiv_comp_iso A f x _
    rw [h1]
    change fderiv ℝ (fun x => (fun z => fderiv ℝ f z (A (unitVector j))) (A x)) y (unitVector j) = _
    rw [fderiv_comp_iso A (fun z => fderiv ℝ f z (A (unitVector j))) y (unitVector j)]
    rw [fderiv_clm_apply (hd _) (differentiableAt_const _)]
    simp
  show ∑ j : Fin 3, dirDeriv j (dirDeriv j (fun x => f (A x))) y =
    ∑ j : Fin 3, dirDeriv j (dirDeriv j f) (A y)
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_congr rfl fun j _ => dirDeriv_dirDeriv hf j j (A y)]
  exact trace_iso A (fderiv ℝ (fderiv ℝ f) (A y))

theorem integral_comp_iso {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Space ≃ₗᵢ[ℝ] Space)
    (g : Space → E) : ∫ y, g (A y) = ∫ z, g z :=
  A.measurePreserving.integral_comp A.toHomeomorph.measurableEmbedding g

theorem integral_iso_smul (A : Space ≃ₗᵢ[ℝ] Space) (c : Space → ℝ) (F : Space → Space) :
    ∫ y, c y • A (F y) = A (∫ y, c y • F y) := by
  have := A.toLinearIsometry.integral_comp_comm (μ := volume) (fun y => c y • F y)
  simp only [LinearIsometryEquiv.coe_toLinearIsometry, map_smul] at this
  exact this

theorem trace_equivariant (h : IsSecondOrderField m v G H) (A : Space ≃ₗᵢ[ℝ] Space)
    (hv : ∀ᵐ y ∂volume, v (A y) = A (v y)) :
    ∀ᵐ y ∂volume, negSecondTrace H (A y) = A (negSecondTrace H y) := by
  have hS := memLp_trace h
  have hT : MemLp (fun y => A.symm (secondTrace (H (A y)))) 2 volume := by
    have h1 : MemLp (fun y => secondTrace (H (A y))) 2 volume :=
      hS.comp_measurePreserving A.measurePreserving
    exact ContinuousLinearMap.comp_memLp' A.symm.toContinuousLinearEquiv.toContinuousLinearMap h1
  have key : ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y, ψ y • A.symm (secondTrace (H (A y))) = ∫ y, ψ y • secondTrace (H y) := by
    intro ψ hψ1 hψ2
    have hψ : IsTestScalar ψ := ⟨hψ1, hψ2⟩
    have hψA : IsTestScalar (fun z => ψ (A.symm z)) :=
      ⟨hψ1.comp A.symm.contDiff, hψ2.comp_homeomorph A.symm.toHomeomorph⟩
    have c2 : ∫ y, ψ y • secondTrace (H (A y)) = ∫ z, ψ (A.symm z) • secondTrace (H z) := by
      rw [← integral_comp_iso A (fun z => ψ (A.symm z) • secondTrace (H z))]
      simp
    have c4 : ∫ z, diagSum ψ (A.symm z) • v z = ∫ y, diagSum ψ y • v (A y) := by
      rw [← integral_comp_iso A (fun z => diagSum ψ (A.symm z) • v z)]
      simp
    have c5 : ∫ y, diagSum ψ y • v (A y) = ∫ y, diagSum ψ y • A (v y) :=
      integral_congr_ae (hv.mono fun y hy => by simp only [hy])
    rw [integral_iso_smul A.symm ψ, c2, weak_diag h hψA]
    have c3 : ∫ z, diagSum (fun z => ψ (A.symm z)) z • v z = ∫ z, diagSum ψ (A.symm z) • v z := by
      congr 1
      funext z
      rw [diagSum_comp_iso A.symm hψ1 z]
    rw [c3, c4, c5, integral_iso_smul A (diagSum ψ), ← weak_diag h hψ]
    simp
  have hTS := ae_eq_of_integral_contDiff_smul_eq (hT.locallyIntegrable one_le_two)
    (hS.locallyIntegrable one_le_two) key
  filter_upwards [hTS] with y hy
  simp only [negSecondTrace, map_neg]
  rw [← hy, LinearIsometryEquiv.apply_symm_apply]

theorem turnStep_add (m : ℕ) (a b : Space) : turnStep m (a + b) = turnStep m a + turnStep m b := by
  ext i
  fin_cases i <;> simp [turnStep, EuclideanSpace.single_apply] <;> ring

theorem turnStep_smul (m : ℕ) (c : ℝ) (a : Space) : turnStep m (c • a) = c • turnStep m a := by
  ext i
  fin_cases i <;> simp [turnStep, EuclideanSpace.single_apply] <;> ring

theorem turnStep_norm (m : ℕ) (y : Space) : ‖turnStep m y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, turnStep, EuclideanSpace.single_apply, Real.norm_eq_abs, sq_abs]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq (2 * Real.pi / m)

theorem mirror_add (a b : Space) : mirror (a + b) = mirror a + mirror b := by
  ext i
  fin_cases i <;> simp [mirror, EuclideanSpace.single_apply] <;> ring

theorem mirror_smul (c : ℝ) (a : Space) : mirror (c • a) = c • mirror a := by
  ext i
  fin_cases i <;> simp [mirror, EuclideanSpace.single_apply]

theorem mirror_norm (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, mirror, EuclideanSpace.single_apply, Real.norm_eq_abs, sq_abs]

def turnIso (m : ℕ) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := turnStep m, map_add' := turnStep_add m, map_smul' := turnStep_smul m,
      norm_map' := turnStep_norm m } rfl

def mirrorIso : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := mirror, map_add' := mirror_add, map_smul' := mirror_smul, norm_map' := mirror_norm } rfl

theorem turnIso_coe (m : ℕ) : ⇑(turnIso m) = turnStep m := by
  unfold turnIso
  rw [LinearIsometry.coe_toLinearIsometryEquiv]
  rfl

theorem mirrorIso_coe : ⇑mirrorIso = mirror := by
  unfold mirrorIso
  rw [LinearIsometry.coe_toLinearIsometryEquiv]
  rfl

end SecondTraceSolenoidalInternal

open SecondTraceSolenoidalInternal in
theorem secondTraceSolenoidal : SecondTraceSolenoidalStatement := by
  intro m v G H h
  refine ⟨⟨(memLp_trace h).neg, fun φ hφ => solenoidal h hφ⟩, ?_, ?_⟩
  · have h1 := trace_equivariant h (turnIso m) (by rw [turnIso_coe]; exact h.symmetric.1)
    rw [turnIso_coe] at h1
    exact h1
  · have h1 := trace_equivariant h mirrorIso (by rw [mirrorIso_coe]; exact h.symmetric.2)
    rw [mirrorIso_coe] at h1
    exact h1

end SteadyCert

end Breakdown
