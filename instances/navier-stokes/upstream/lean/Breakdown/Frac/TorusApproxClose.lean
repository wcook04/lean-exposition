import Breakdown.Frac.TorusApproxCloseAux
import Breakdown.Torus.ApproxClose
import Breakdown.Frac.RExports
import Breakdown.Frac.PSlice
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TorusApproxClose.Internal

open ApproxClose.Internal

theorem coord_le (v w : Space) (j : Fin 3) : |v j - w j| ≤ dist v w := by
  rw [dist_eq_norm]
  have := PiLp.norm_apply_le (v - w) j
  rwa [Real.norm_eq_abs, PiLp.sub_apply] at this

theorem freq_coord (k : Lattice) (i : Fin 3) : freq k i = k i := by
  simp [freq, unitVector, Pi.single_apply]

theorem center_coord (i : Fin 3) : center i = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

theorem wrap_eq (x : Space) : wrap x = x + freq (fun i => -round (x i - center i)) := by
  simp [wrap, freq, sub_eq_add_neg, Finset.sum_neg_distrib, neg_smul]

theorem periodize_wrap {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : ∀ v, centralRadius / 2 ≤ dist v center → f v = 0) (x : Space) :
    latticePeriodize f x = f (wrap x) := by
  unfold latticePeriodize
  rw [wrap_eq]
  refine tsum_eq_single (fun i => -round (x i - center i)) fun j hj => ?_
  by_contra h
  apply hj
  funext i
  have hd : dist (x + freq j) center < 1 / 8 := by
    by_contra h'
    exact h (hf _ (by rw [centralRadius]; linarith))
  have a1 := (coord_le _ _ i).trans hd.le
  rw [PiLp.add_apply, freq_coord, center_coord] at a1
  have a3 := abs_sub_round (x i - 1 / 2)
  rw [abs_le] at a1 a3
  have key : |((j i + round (x i - 1 / 2) : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith [a1.1, a1.2, a3.1, a3.2]
  have h' : |j i + round (x i - 1 / 2)| < 1 := by exact_mod_cast key
  have := abs_lt.mp h'
  rw [center_coord]
  omega

theorem fderiv_scale_apply {f : Space → Space} (hf : Differentiable ℝ f) (p q : ℝ) (y v : Space) :
    fderiv ℝ (fun y => p • f (q • y)) y v = (p * q) • fderiv ℝ f (q • y) v := by
  have h1 : HasFDerivAt (fun y : Space => q • y) (q • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id (𝕜 := ℝ) y).const_smul q
  have h2 : HasFDerivAt (fun y => p • f (q • y))
      (p • ((fderiv ℝ f (q • y)).comp (q • ContinuousLinearMap.id ℝ Space))) y :=
    ((hf _).hasFDerivAt.comp y h1).const_smul p
  rw [h2.fderiv]
  simp [smul_smul]

theorem gradEnergy_scale {f : Space → Space} (hf : Differentiable ℝ f) (p : ℝ) {q : ℝ} (hq : 0 < q) :
    gradEnergy (fun y => p • f (q • y)) = p ^ 2 * q⁻¹ * gradEnergy f := by
  unfold gradEnergy
  have e : ∀ y, ∑ i : Fin 3, ‖fderiv ℝ (fun y => p • f (q • y)) y (unitVector i)‖ ^ 2 =
      (p * q) ^ 2 * ∑ i : Fin 3, ‖fderiv ℝ f (q • y) (unitVector i)‖ ^ 2 := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_scale_apply hf, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume
    (fun y => ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2) q (hR := hq.le),
    finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

theorem mass_scale (f : Space → Space) (p : ℝ) {q : ℝ} (hq : 0 < q) :
    ∫ y, ‖p • f (q • y)‖ ^ 2 = p ^ 2 * (q ^ 3)⁻¹ * ∫ y, ‖f y‖ ^ 2 := by
  have e : ∀ y, ‖p • f (q • y)‖ ^ 2 = p ^ 2 * ‖f (q • y)‖ ^ 2 := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume (fun y => ‖f y‖ ^ 2) q
    (hR := hq.le), finrank_euclideanSpace_fin, smul_eq_mul]
  ring

theorem sqrt_simScale {α μ : ℝ} (hμ : 0 < μ) : Real.sqrt (simScale α μ) = μ ^ (1 / (2 * α)) := by
  rw [Real.sqrt_eq_rpow, simScale, ← Real.rpow_mul hμ.le]
  congr 1
  ring

theorem amp_eq {α μ : ℝ} (hα : 0 < α) (hμ : 0 < μ) :
    simScale α μ ^ (1 / 4 : ℝ) * ((Real.sqrt (simScale α μ))⁻¹ * μ ^ (1 - 1 / (2 * α))) =
      μ ^ dilExponent α := by
  rw [sqrt_simScale hμ, simScale, ← Real.rpow_mul hμ.le, ← Real.rpow_neg hμ.le, ← Real.rpow_add hμ,
    ← Real.rpow_add hμ, dilExponent]
  congr 1
  field_simp
  ring

theorem mass_exp {α m ℓ : ℝ} (hα : 0 < α) (hm : 0 < m) (hℓ : 0 < ℓ) :
    simScale α (m * ℓ) * ((m ^ (1 - 1 / (2 * α))) ^ 2 * ((m ^ (1 / (2 * α))) ^ 3)⁻¹ *
      ℓ ^ (-((5 - 4 * α) / (2 * α)))) = (m * ℓ) ^ ((4 * α - 3) / (2 * α)) := by
  simp only [simScale, Real.mul_rpow hm.le hℓ.le, Real.rpow_def_of_pos hm, Real.rpow_def_of_pos hℓ,
    ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  field_simp
  push_cast
  ring

theorem fdil_split {α : ℝ} (hDA : Freq.FracDilationAlgebra α) {c c₀ : ℝ} (hc : 0 < c) (x x₀ : Freq.X) :
    ‖Freq.fracDilX α c x - Freq.fracDilX α c₀ x₀‖ ≤
      c ^ dilExponent α * ‖x - x₀‖ + ‖Freq.fracDilX α c x₀ - Freq.fracDilX α c₀ x₀‖ := by
  have hsplit : Freq.fracDilX α c x - Freq.fracDilX α c₀ x₀ =
      Freq.fracDilX α c (x - x₀) + (Freq.fracDilX α c x₀ - Freq.fracDilX α c₀ x₀) := by
    rw [map_sub]
    abel
  rw [hsplit, ← hDA.1 c hc]
  exact norm_add_le _ _

theorem fprofileContinuous {α : ℝ} (hDA : Freq.FracDilationAlgebra α) (hDC : Freq.FracDilationContinuous α)
    {W : ℝ → Space → Space} (hx : Continuous (fun σ => Freq.embedX (W σ))) (s₀ L : ℝ) (hL : L < 1) :
    Continuous (fun t : Icc (0 : ℝ) L =>
      Freq.fracDilX α (1 - (t : ℝ))⁻¹ (Freq.embedX (W (s₀ - Real.log (1 - (t : ℝ)))))) := by
  have ha_pos : ∀ t : Icc (0 : ℝ) L, 0 < 1 - (t : ℝ) := fun t => by linarith [t.2.2]
  have hac : Continuous (fun t : Icc (0 : ℝ) L => (1 - (t : ℝ))⁻¹) :=
    (continuous_const.sub continuous_subtype_val).inv₀ (fun t => (ha_pos t).ne')
  have hxc : Continuous (fun t : Icc (0 : ℝ) L => Freq.embedX (W (s₀ - Real.log (1 - (t : ℝ))))) :=
    hx.comp (continuous_const.sub ((continuous_const.sub continuous_subtype_val).log
      (fun t => (ha_pos t).ne')))
  rw [continuous_iff_continuousAt]
  intro t₀
  have ha₀ : 0 < (1 - (t₀ : ℝ))⁻¹ := inv_pos.mpr (ha_pos t₀)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun t : Icc (0 : ℝ) L => ((1 - (t : ℝ))⁻¹) ^ dilExponent α *
      ‖Freq.embedX (W (s₀ - Real.log (1 - (t : ℝ)))) - Freq.embedX (W (s₀ - Real.log (1 - (t₀ : ℝ))))‖ +
      ‖Freq.fracDilX α (1 - (t : ℝ))⁻¹ (Freq.embedX (W (s₀ - Real.log (1 - (t₀ : ℝ))))) -
        Freq.fracDilX α (1 - (t₀ : ℝ))⁻¹ (Freq.embedX (W (s₀ - Real.log (1 - (t₀ : ℝ)))))‖)
    (fun t => norm_nonneg _) (fun t => fdil_split hDA (inv_pos.mpr (ha_pos t)) _ _) ?_
  have h1 := (hac.tendsto t₀).rpow_const (p := dilExponent α) (Or.inl ha₀.ne')
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp (hxc.tendsto t₀)
  have h3 := tendsto_iff_norm_sub_tendsto_zero.mp
    (((hDC (Freq.embedX (W (s₀ - Real.log (1 - (t₀ : ℝ)))))).continuousAt
      (Ioi_mem_nhds ha₀)).tendsto.comp (hac.tendsto t₀))
  have h4 := (h1.mul h2).add h3
  rw [mul_zero, add_zero] at h4
  exact h4

end TorusApproxClose.Internal

open TorusApproxClose.Internal ApproxClose.Internal in
set_option maxHeartbeats 4000000 in
theorem fracApproxClose (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (hTN : TransplantNorm)
    (hTS : TransplantSmooth) (hA : FracApproxFieldProperties α) (hL : FracApproxLinks α)
    (hED : Freq.FracEmbedDilate α) (hDA : Freq.FracDilationAlgebra α)
    (hDC : Freq.FracDilationContinuous α) (hSC : RotatingSliceContinuous)
    (hSD : FracSelfSimilarDecay α) (hCC : FracCutoffClose α) : FracApproxClose α := by
  intro F hF a U P P' k b ε δ A hU hP hk hb hδ hAε
  have hα0 : 0 < α := by linarith
  obtain ⟨hEN, hEL⟩ := Freq.embedNormLinear_holds
  have hSlice : ∀ s, IsDecayField (rotatingSlice a U s) := fun s =>
    (rotatingSliceDecay α hα hα2 a U P hU s).1
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hl : 0 < Real.exp (-(P' / k)) := Real.exp_pos _
  have hl1 : Real.exp (-(P' / k)) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos hP hk'))
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hAε 0)
  obtain ⟨Cb, hCb⟩ := A.bound
  obtain ⟨K, hK0, hK⟩ := l2_le_grad Freq.gradSixDecay (b := b)
  set M2 : ℝ := (A.terms : ℝ) * (|Cb| * (Real.sqrt K * |Cb|)) with hM2
  have hM2n : 0 ≤ M2 := by positivity
  obtain ⟨hgc, Km, hKm⟩ := hCC a U P hU
  set Λ : ℝ := ((Real.exp (-(P' / k)))⁻¹ ^ (1 - 1 / (2 * α))) ^ 2 with hΛ
  have hΛ0 : 0 < Λ := by positivity
  obtain ⟨ℓ₀, hℓ₀, hgc'⟩ := hgc (δ ^ 2 / 16 / Λ) (by positivity)
  set g : ℝ := (4 * α - 3) / (2 * α) with hg
  have hg0 : 0 < g := by rw [hg]; apply div_pos <;> linarith
  set X : ℝ := min ((1 / (8 * b)) ^ 2) (δ ^ 2 / (16 * (M2 ^ 2 + 1))) with hX
  have hX0 : 0 < X := lt_min (by positivity) (by positivity)
  set Y : ℝ := (δ ^ 2 / 16 / (|Km| + 1)) ^ g⁻¹ with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos (by positivity) _
  have hXa : 0 < X ^ α := Real.rpow_pos_of_pos hX0 _
  refine ⟨min (min ℓ₀ 1) (min (X ^ α) Y), lt_min (lt_min hℓ₀ one_pos) (lt_min hXa hY0), ?_⟩
  intro T hT hT₀ n
  have hTa : T < ℓ₀ := hT₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hT1 : T ≤ 1 := (hT₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hTX : T < X ^ α := hT₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hTY : T < Y := hT₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = Real.exp (-(P' / k)) := ⟨_, rfl⟩
  have hl' : 0 < lam := hlam ▸ hl
  have hl1' : lam < 1 := hlam ▸ hl1
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = stepScale T (Real.exp (-(P' / k))) n := ⟨_, rfl⟩
  have hμ : 0 < μ := hμdef ▸ stepScale_pos hT hl n
  have hμT : μ ≤ T := by
    rw [hμdef, stepScale]
    exact mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1.le)
  have hμ1 : μ ≤ 1 := hμT.trans hT1
  obtain ⟨μ', hμ'def⟩ : ∃ μ', μ' = simScale α μ := ⟨_, rfl⟩
  have hμ' : 0 < μ' := hμ'def ▸ Real.rpow_pos_of_pos hμ _
  have hμ'1 : μ' ≤ 1 := hμ'def ▸ Real.rpow_le_one hμ.le hμ1 (by positivity)
  have hμ'X : μ' < X := by
    have h1 : μ ^ α⁻¹ < (X ^ α) ^ α⁻¹ := Real.rpow_lt_rpow hμ.le (hμT.trans_lt hTX) (by positivity)
    rw [Real.rpow_rpow_inv hX0.le hα0.ne'] at h1
    rw [hμ'def, simScale, one_div]
    exact h1
  rw [← hμdef, ← hμ'def]
  refine (ContinuousMap.norm_le _ (add_nonneg hε hδ.le)).mpr fun s => ?_
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 - lam := hlam ▸ s.2.2
  have h1s : 0 < 1 - (s : ℝ) := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = stepStart T (Real.exp (-(P' / k))) n + μ * s := ⟨_, rfl⟩
  have hTt : T - t = μ * (1 - s) := by
    rw [ht, stepStart, ← hμdef]
    ring
  have htT : t < T := by nlinarith
  have ht0 : 0 ≤ t := by
    have : t = T - μ + μ * s := by rw [ht, stepStart, ← hμdef]
    nlinarith
  have hℓ : 0 < T - t := by linarith
  have hlo : lam * μ ≤ T - t := by rw [hTt]; nlinarith
  have hhi : T - t ≤ μ := by rw [hTt]; nlinarith
  obtain ⟨r, hrdef⟩ : ∃ r, r = Real.sqrt μ' := ⟨_, rfl⟩
  have hr : 0 < r := hrdef ▸ Real.sqrt_pos.mpr hμ'
  have hrμ : r = μ ^ (1 / (2 * α)) := by rw [hrdef, hμ'def, sqrt_simScale hμ]
  have hsqb : r < 1 / (8 * b) := by
    rw [hrdef]
    exact (Real.sqrt_lt' (by positivity)).mpr (hμ'X.trans_le (min_le_left _ _))
  obtain ⟨B, hB⟩ : ∃ B, B = max b (1 / (8 * r)) := ⟨_, rfl⟩
  have hsh : IsShellScale μ' B := by
    refine ⟨hμ', hμ'1, hB ▸ lt_max_of_lt_left hb, ?_⟩
    rw [← hrdef, hB, mul_max_of_nonneg _ _ hr.le]
    have e8 : r * (1 / (8 * r)) = 1 / 8 := by
      field_simp
    refine max_le ?_ e8.le
    rw [lt_div_iff₀ (by positivity)] at hsqb
    have h8 : r * (8 * b) = 8 * (r * b) := by ring
    linarith
  set f : Space → Space := fracApproxField α a U T t with hfdef
  have hAU := hA a U P hU T hT
  have hf : ContDiff ℝ ∞ f := by
    have hc : ContDiffOn ℝ ∞ ((fun z : ℝ × Space => fracApproxField α a U T z.1 z.2) ∘
        (fun x : Space => (t, x))) univ :=
      hAU.1.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x _ => ⟨htT, mem_univ x⟩)
    exact contDiffOn_univ.mp hc
  have hfz : ∀ v, centralRadius / 2 ≤ dist v center → f v = 0 := fun v hv => ((hAU.2.2 t htT v).2.1 hv).1
  have hfd : ∀ x, divergenceAt f x = 0 := fun x => (hAU.2.2 t htT x).1
  set ca : ℝ := μ ^ (1 - 1 / (2 * α)) with hca
  have hca0 : 0 < ca := Real.rpow_pos_of_pos hμ _
  set G : Space → Space := fun y => ca • f (center + r • y) with hGdef
  have hGc : ContDiff ℝ ∞ G :=
    (hf.comp (contDiff_const.add (contDiff_id.const_smul r))).const_smul ca
  have hGs : ∀ y, 1 / (8 * r) < ‖y‖ → G y = 0 := by
    intro y hy
    have hd : centralRadius / 2 ≤ dist (center + r • y) center := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, centralRadius]
      rw [div_lt_iff₀ (by positivity)] at hy
      nlinarith
    simp only [hGdef, hfz _ hd, smul_zero]
  have hGd : ∀ y, divergenceAt G y = 0 := by
    intro y
    have e : G = (ca / r) • (fun y => r • f (center + r • y)) := by
      funext y
      simp only [hGdef, Pi.smul_apply, smul_smul]
      congr 1
      field_simp
    rw [e, ToVLinear.Internal.divergenceAt_smul, divergence_affine (hf.differentiable (by simp)), hfd,
      mul_zero, mul_zero]
  have hG : IsDecayField G := decay_of_ball hGc hGd hGs
  have hGB : ∀ y, B < ‖y‖ → G y = 0 := fun y hy =>
    hGs y (lt_of_le_of_lt (hB ▸ le_max_right _ _) hy)
  have hφ : ∀ l, IsDecayField (A.field n l) := fun l =>
    decay_of_ball (A.isTest n l).1 (A.isTest n l).2.2 (field_vanish A n l)
  have hφB : ∀ l y, B < ‖y‖ → A.field n l y = 0 := fun l y hy =>
    field_vanish A n l y (lt_of_le_of_lt (hB ▸ le_max_left _ _) hy)
  obtain ⟨hTG1, hTG2, hTG3, _⟩ := hTS G μ' B hGc hGd hsh (tsupport_sub_ball hGB)
  set kc : ℝ := r⁻¹ * ca with hkc
  have hkc0 : 0 < kc := by positivity
  have htrans : transplantField μ' G = kc • latticePeriodize f := by
    funext x
    rw [Pi.smul_apply, periodize_wrap hfz x]
    simp only [transplantField, simCoord, hGdef, Pi.smul_apply, smul_smul, ← hrdef]
    rw [mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  have hper : latticePeriodize f = kc⁻¹ • transplantField μ' G := by
    rw [htrans, smul_smul, inv_mul_cancel₀ hkc0.ne', one_smul]
  have hamp : μ ^ dilExponent α * kc⁻¹ = μ' ^ (1 / 4 : ℝ) := by
    have e := amp_eq (α := α) hα0 hμ
    rw [← hμ'def, ← hrdef] at e
    rw [← e, hkc, ← hca]
    field_simp
  have hpiece : fracApproxPiece α a U T (Real.exp (-(P' / k))) n s = μ' ^ (1 / 4 : ℝ) • toV (transplantField μ' G) := by
    rw [(hL a U P T _ hU hT hT1 hl hl1 n).1 s, ← hμdef, ← ht, ← hfdef, hper,
      toV_smul _ hTG1 hTG2 hTG3, smul_smul, hamp]
  set m : ℝ := (1 - (s : ℝ))⁻¹ with hmdef
  have hm0 : 0 < m := inv_pos.mpr h1s
  have hmℓ : μ = m * (T - t) := by
    rw [hTt, hmdef]
    field_simp
  have hm1 : 1 ≤ m := by
    rw [hmdef]
    exact one_le_inv₀ h1s |>.mpr (by linarith)
  have hmlam : m ≤ lam⁻¹ := by
    rw [hmdef]
    exact inv_anti₀ hl' (by linarith)
  set W : Space → Space := rotatingSlice a U (similarityTime T t) with hWdef
  set Pf : Space → Space := scaleField α m W with hPfdef
  have hPf : IsDecayField Pf := Freq.decayFieldScale α hα0 m W hm0 (hSlice _)
  have hcont := fprofileContinuous hDA hDC (hSC α hα hα2 a U P hU) (n * (P' / k))
    (MildFramework.stepLength P' k) (by show 1 - Real.exp (-(P' / k)) < 1; linarith)
  have hc' : Continuous (fun t : Icc (0 : ℝ) (MildFramework.stepLength P' k) =>
      F.selfSimilar (fun s => Freq.embedX (rotatingSlice a U s)) (n * (P' / k)) t) := by
    simp only [ScaledMildFramework.selfSimilar, hF]
    exact hcont
  have hsim : similarityTime T t = n * (P' / k) - Real.log (1 - s) := by
    unfold similarityTime
    rw [hTt]
    have : μ * (1 - s) / T = lam ^ n * (1 - s) := by
      rw [hμdef, stepScale, hlam]
      field_simp
    rw [this, Real.log_mul (pow_ne_zero _ hl'.ne') h1s.ne', Real.log_pow, hlam, Real.log_exp]
    ring
  have hpp : (F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P' k n) s = Freq.embedX Pf := by
    unfold ScaledMildFramework.profilePiece toPiece
    rw [dif_pos hc']
    show F.selfSimilar (fun s => Freq.embedX (rotatingSlice a U s)) (n * (P' / k)) s = _
    simp only [ScaledMildFramework.selfSimilar, hF]
    rw [hED _ _ (inv_pos.mpr h1s) (hSlice _), hPfdef, hWdef, hsim]
  have hε' : ‖Freq.embedX Pf - ∑ l, A.weight n l s • Freq.embedX (A.field n l)‖ ≤ ε :=
    r3_bound A _ n s (hAε n) hpp
  set H : Space → Space := fracCutAt α a U T t (T - t) with hHdef
  have hGH : G = fun y => m ^ (1 - 1 / (2 * α)) • H (m ^ (1 / (2 * α)) • y) := by
    funext y
    simp only [hGdef, hHdef, fracCutAt, smul_smul, hca, hrμ, hmℓ]
    rw [Real.mul_rpow hm0.le hℓ.le, Real.mul_rpow hm0.le hℓ.le, mul_comm ((T - t) ^ (1 / (2 * α)))]
  have hGP : G - Pf = fun y => m ^ (1 - 1 / (2 * α)) • (H - W) (m ^ (1 / (2 * α)) • y) := by
    funext y
    simp only [hGH, hPfdef, scaleField, Pi.sub_apply, smul_sub]
  have hHc : ContDiff ℝ ∞ H := by
    rw [hHdef]
    unfold fracCutAt
    exact (hf.comp (contDiff_const.add (contDiff_id.const_smul _))).const_smul _
  have hHW : Differentiable ℝ (H - W) := (hHc.sub (hSlice _).1).differentiable (by simp)
  have hb0 : 0 < m ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hm0 _
  have hgrad : gradEnergy (G - Pf) ≤ δ ^ 2 / 16 := by
    rw [hGP, gradEnergy_scale hHW _ hb0, gradEnergy_sub_comm]
    have hE := hgc' T t hT hT1 ht0 htT (hhi.trans_lt (hμT.trans_lt hTa))
    have hE0 : 0 ≤ gradEnergy (W - H) := integral_nonneg fun _ =>
      Finset.sum_nonneg fun _ _ => by positivity
    have hp : (m ^ (1 - 1 / (2 * α))) ^ 2 ≤ Λ := by
      rw [hΛ, ← hlam]
      have h2 : 0 ≤ 1 - 1 / (2 * α) := by
        rw [sub_nonneg, div_le_one (by positivity)]
        linarith
      exact pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow hm0.le hmlam h2) 2
    have hq : (m ^ (1 / (2 * α)))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hm1 (by positivity))
    calc (m ^ (1 - 1 / (2 * α))) ^ 2 * (m ^ (1 / (2 * α)))⁻¹ * gradEnergy (W - H)
        ≤ Λ * 1 * (δ ^ 2 / 16 / Λ) := by
          apply mul_le_mul (mul_le_mul hp hq (by positivity) hΛ0.le) hE hE0 (by positivity)
      _ = δ ^ 2 / 16 := by field_simp
  have hmass : μ' * ∫ y, ‖G y‖ ^ 2 ≤ δ ^ 2 / 16 := by
    have e1 : ∫ y, ‖G y‖ ^ 2 = (m ^ (1 - 1 / (2 * α))) ^ 2 * ((m ^ (1 / (2 * α))) ^ 3)⁻¹ *
        ∫ y, ‖H y‖ ^ 2 := by
      rw [hGH]
      exact mass_scale H _ hb0
    have hHm := hKm T t hT hT1 ht0 htT
    have hz : 0 < (T - t) ^ (-((5 - 4 * α) / (2 * α))) := Real.rpow_pos_of_pos hℓ _
    have hHm' : ∫ y, ‖H y‖ ^ 2 ≤ |Km| * (T - t) ^ (-((5 - 4 * α) / (2 * α))) :=
      hHm.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz.le)
    have hid := mass_exp hα0 hm0 hℓ
    rw [← hmℓ, ← hμ'def] at hid
    have hcoef : 0 ≤ (m ^ (1 - 1 / (2 * α))) ^ 2 * ((m ^ (1 / (2 * α))) ^ 3)⁻¹ := by positivity
    have hμg : μ ^ g < δ ^ 2 / 16 / (|Km| + 1) := by
      have h1 := Real.rpow_lt_rpow hμ.le (hμT.trans_lt hTY) hg0
      rwa [hY, Real.rpow_inv_rpow (by positivity) hg0.ne'] at h1
    have hμg0 : 0 ≤ μ ^ g := (Real.rpow_pos_of_pos hμ _).le
    calc μ' * ∫ y, ‖G y‖ ^ 2
        ≤ μ' * ((m ^ (1 - 1 / (2 * α))) ^ 2 * ((m ^ (1 / (2 * α))) ^ 3)⁻¹ *
            (|Km| * (T - t) ^ (-((5 - 4 * α) / (2 * α))))) := by
          rw [e1]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHm' hcoef) hμ'.le
      _ = |Km| * μ ^ g := by
          rw [← hid]
          ring
      _ ≤ (|Km| + 1) * μ ^ g := mul_le_mul_of_nonneg_right (by linarith) hμg0
      _ ≤ δ ^ 2 / 16 := by
          rw [lt_div_iff₀ (by positivity)] at hμg
          nlinarith
  have hM2' : Real.sqrt (∫ y, ‖(∑ l, A.weight n l s • A.field n l) y‖ ^ 2) ≤ M2 := by
    refine (l2_sum_le Finset.univ (fun l => A.weight n l s)
      (fun l => memLp_of_ball (A.isTest n l).1.continuous (field_vanish A n l))).2.trans ?_
    have hterm : ∀ l : Fin A.terms, |A.weight n l s| * Real.sqrt (∫ y, ‖A.field n l y‖ ^ 2) ≤
        |Cb| * (Real.sqrt K * |Cb|) := by
      intro l
      have hw : |A.weight n l s| ≤ |Cb| := by
        rw [← Real.norm_eq_abs]
        exact (ContinuousMap.norm_coe_le_norm _ _).trans ((hCb n l).2.trans (le_abs_self _))
      have hint : ∫ y, ‖A.field n l y‖ ^ 2 ≤ K * Cb ^ 2 := by
        refine (hK _ (A.isTest n l) (A.support n l)).trans ?_
        rw [← hEN _ (hφ l)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hCb n l).1 2) hK0
      have hsq : Real.sqrt (∫ y, ‖A.field n l y‖ ^ 2) ≤ Real.sqrt K * |Cb| := by
        rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hK0]
        exact Real.sqrt_le_sqrt hint
      exact mul_le_mul hw hsq (Real.sqrt_nonneg _) (abs_nonneg _)
    refine (Finset.sum_le_sum fun l _ => hterm l).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbd := pieceBound hTN hEN hEL (fun l => A.weight n l s) hsh hG hGB hφ hφB hPf hε' hgrad hmass hM2'
  rw [torus_diff A μ' _ n s hpiece, toV_transplant_sub hTS (fun l => A.weight n l s) hsh hG hGB hφ hφB]
  have hsη : Real.sqrt (δ ^ 2 / 16) = δ / 4 := by
    rw [show δ ^ 2 / 16 = (δ / 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsη] at hbd
  have hμm : μ' * (16 * (M2 ^ 2 + 1)) < δ ^ 2 :=
    (lt_div_iff₀ (by positivity)).mp (hμ'X.trans_le (min_le_right _ _))
  have hfin : ‖μ' ^ (1 / 4 : ℝ) • toV (transplantField μ' (G - ∑ l, A.weight n l s • A.field n l))‖ ^ 2
      ≤ (ε + δ) ^ 2 := by
    nlinarith [mul_nonneg hε hδ.le, mul_nonneg hμ'.le (sq_nonneg M2)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (add_nonneg hε hδ.le) two_ne_zero).mp hfin

end Breakdown.Periodic
