import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

private def outerProductMap : Space →L[ℝ] Space →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (a b : Space) (j k : Fin 3) => a j * b k)
      (fun a a' b => by ext j k; simp; ring)
      (fun c a b => by ext j k; simp; ring)
      (fun a b b' => by ext j k; simp; ring)
      (fun c a b => by ext j k; simp; ring))
    1 (fun a b => by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      show ‖a j * b k‖ ≤ 1 * ‖a‖ * ‖b‖
      rw [norm_mul, one_mul]
      exact mul_le_mul (PiLp.norm_apply_le a j) (PiLp.norm_apply_le b k) (norm_nonneg _)
        (norm_nonneg _))

private lemma outerProductMap_norm_le : ‖outerProductMap‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

private lemma norm_iteratedFDeriv_outer_le {f : Space → Space} {C : ℝ} (hf : ContDiff ℝ 2 f)
    (hC : ∀ j ≤ 2, ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ C) (n : ℕ) (hn : n ≤ 2) (z : Space) :
    ‖iteratedFDeriv ℝ n (fun z => outerProductMap (f z) (f z)) z‖ ≤ 4 * (C * C) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by norm_num) z)
  refine (outerProductMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hf z
    (by exact_mod_cast hn) outerProductMap_norm_le).trans ?_
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (C * C) :=
        Finset.sum_le_sum fun i hi => by
          have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [← mul_assoc]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hC i (by omega) z) (Nat.cast_nonneg _))
            (hC (n - i) (by omega) z) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC0)
    _ = 2 ^ n * (C * C) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
    _ ≤ 4 * (C * C) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC0 hC0)
        calc (2 : ℝ) ^ n ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hn
          _ = 4 := by norm_num

private lemma hasFDerivAt_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {z : Space} (h : DifferentiableAt ℝ (fderiv ℝ f) z) (v : Space) :
    HasFDerivAt (fun x => fderiv ℝ f x v) ((fderiv ℝ (fderiv ℝ f) z).flip v) z := by
  simpa using h.hasFDerivAt.clm_apply (hasFDerivAt_const v z)

theorem derivRepresentation_of_op (hPD : ProfileOpDeriv) : DerivRepresentation := by
  intro hK W q P R hW
  have hS := hW.toIsSmoothOrbitField
  obtain ⟨C, hC⟩ := hS.deriv_bound
  have hj : ContDiff ℝ 3 (fun p : ℝ × Space => W p.1 p.2) :=
    contDiff_infty.1 hS.smooth_field 3
  have hWs : ∀ s, ContDiff ℝ 3 (W s) := fun s =>
    hj.comp ((contDiff_const (c := s)).prodMk contDiff_id)
  have hCW : ∀ s, ∀ j ≤ 2, ∀ z, ‖iteratedFDeriv ℝ j (W s) z‖ ≤ C := fun s j hjle z =>
    hC j (by omega) s z
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → Space → Fin 3 → Fin 3 → ℝ,
      F = fun s z => outerProductMap (W s z) (W s z) := ⟨_, rfl⟩
  have hFeq : pairTensor W W = F := by
    rw [hFdef]
    rfl
  rw [hFeq]
  have hFs : ∀ s, ContDiff ℝ 3 (F s) := fun s => by
    rw [hFdef]
    exact (outerProductMap.contDiff.comp (hWs s)).clm_apply (hWs s)
  have hFj : ContDiff ℝ 3 (fun p : ℝ × Space => F p.1 p.2) := by
    rw [hFdef]
    exact (outerProductMap.contDiff.comp hj).clm_apply hj
  have hFb : ∀ n ≤ 2, ∀ s z, ‖iteratedFDeriv ℝ n (F s) z‖ ≤ 4 * (C * C) := fun n hn s z => by
    rw [hFdef]
    exact norm_iteratedFDeriv_outer_le ((hWs s).of_le (by norm_num)) (hCW s) n hn z
  have hrep : ∀ s, W s = profileOp 1 F s := fun s => funext fun y => by
    rw [← hFeq]
    exact (hW.integral_eq s y).trans (profileBilin_eq_profileOp W W s y)
  have hF1 : ContDiff ℝ 1 (fun p : ℝ × Space => F p.1 p.2) := hFj.of_le (by norm_num)
  have hF0 : ∀ s z, ‖F s z‖ ≤ 4 * (C * C) := fun s z => by
    simpa [norm_iteratedFDeriv_zero] using hFb 0 (by norm_num) s z
  have hFd : ∀ s z, ‖fderiv ℝ (F s) z‖ ≤ 4 * (C * C) := fun s z => by
    rw [← norm_iteratedFDeriv_one]
    exact hFb 1 (by norm_num) s z
  have first : ∀ s y v,
      fderiv ℝ (W s) y v = profileOp (3 / 2) (directionalTensor F v) s y := by
    intro s y v
    rw [hrep s, (hPD hK 1 le_rfl F (4 * (C * C)) hF1 hF0 hFd s y).2 v]
    norm_num
  refine fun s y v => ⟨first s y v, fun w => ?_⟩
  have hG1 : ContDiff ℝ 1 (fun p : ℝ × Space => directionalTensor F v p.1 p.2) := by
    have h := ContDiff.fderiv (f := fun (p : ℝ × Space) (z : Space) => F p.1 z) (g := Prod.snd)
      (n := 1) (m := 3) (hFj.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
      (by norm_num)
    exact h.clm_apply contDiff_const
  have hGb : ∀ s z, ‖directionalTensor F v s z‖ ≤ 4 * (C * C) * ‖v‖ := fun s z =>
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hFd s z) (norm_nonneg v))
  have hGd : ∀ s z, ‖fderiv ℝ (directionalTensor F v s) z‖ ≤ 4 * (C * C) * ‖v‖ := fun s z => by
    have hdiff : DifferentiableAt ℝ (fderiv ℝ (F s)) z :=
      ((hFs s).fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num) z
    have hd := hasFDerivAt_fderiv_apply hdiff v
    rw [show directionalTensor F v s = fun z => fderiv ℝ (F s) z v from rfl, hd.fderiv]
    calc _ ≤ ‖(fderiv ℝ (fderiv ℝ (F s)) z).flip‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 2 (F s) z‖ * ‖v‖ := by
          rw [ContinuousLinearMap.opNorm_flip, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hFb 2 le_rfl s z) (norm_nonneg v)
  have hWd : DifferentiableAt ℝ (fderiv ℝ (W s)) y :=
    ((hWs s).fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num) y
  have hfun : (fun x => fderiv ℝ (W s) x v) = profileOp (3 / 2) (directionalTensor F v) s :=
    funext fun x => first s x v
  have hswap : fderiv ℝ (fderiv ℝ (W s)) y w v = fderiv ℝ (fun x => fderiv ℝ (W s) x v) y w := by
    rw [(hasFDerivAt_fderiv_apply hWd v).fderiv, ContinuousLinearMap.flip_apply]
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hswap, hfun, (hPD hK (3 / 2) (by norm_num) (directionalTensor F v) (4 * (C * C) * ‖v‖)
    hG1 hGb hGd s y).2 w]
  norm_num

end Breakdown.FarField
