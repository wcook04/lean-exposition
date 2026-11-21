import Breakdown.FracCell.VelocityTailSt

open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.OneVarTailInternal

lemma ac_congr {f g : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (h : ∀ x ∈ uIcc a b, f x = g x) : AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hs => ?_⟩
  have e : ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)
      = ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    obtain ⟨h1, h2⟩ := hE.1 i hi
    rw [h _ h1, h _ h2]
  rw [e]
  exact H E hE hs

lemma ac_ofReal {u : ℝ → ℝ} {a b : ℝ} (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun y => (u y : ℂ)) a b := by
  have hd : ∀ x y : ℝ, dist (x : ℂ) (y : ℂ) = dist x y := by
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
  unfold AbsolutelyContinuousOnInterval at hu ⊢
  simpa only [hd] using hu

lemma ac_primitive {k : ℝ → ℂ} {a b c : ℝ} (hk : IntervalIntegrable k volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun y => ∫ t in c..y, k t) a b := by
  have hkre : IntervalIntegrable (fun t => (k t).re) volume a b := ⟨hk.1.re, hk.2.re⟩
  have hkim : IntervalIntegrable (fun t => (k t).im) volume a b := ⟨hk.1.im, hk.2.im⟩
  have hre := ac_ofReal (hkre.absolutelyContinuousOnInterval_intervalIntegral hc)
  have him := ac_ofReal (hkim.absolutelyContinuousOnInterval_intervalIntegral hc)
  have hsum := hre.add (him.const_smul Complex.I)
  refine ac_congr hsum (fun y hy => ?_)
  have hky : IntervalIntegrable k volume c y :=
    hk.mono_set (uIcc_subset_uIcc hc hy)
  have e1 : ∫ t in c..y, (k t).re = (∫ t in c..y, k t).re := intervalIntegral.intervalIntegral_re hky
  have e2 : ∫ t in c..y, (k t).im = (∫ t in c..y, k t).im := intervalIntegral.intervalIntegral_im hky
  simp only [Pi.add_apply, smul_eq_mul]
  rw [e1, e2]
  apply Complex.ext <;> simp

lemma ibp_seg {x b : ℝ} (hxb : x ≤ b) {h k Φ Φ' : ℝ → ℂ}
    (hrep : ∀ y ∈ Icc x b, h y = h x + ∫ t in x..y, k t)
    (hk : IntervalIntegrable k volume x b)
    (hΦ : ∀ t, HasDerivAt Φ (Φ' t) t) (hΦc : ContDiff ℝ 1 Φ) (hΦ'c : Continuous Φ') :
    ∫ t in x..b, k t * Φ t = h b * Φ b - h x * Φ x - ∫ t in x..b, h t * Φ' t := by
  set H : ℝ → ℂ := fun y => h x + ∫ t in x..y, k t with hH
  have hxmem : x ∈ uIcc x b := left_mem_uIcc
  have hHac : AbsolutelyContinuousOnInterval H x b := by
    have := (ac_primitive hk hxmem)
    have c : AbsolutelyContinuousOnInterval (fun _ : ℝ => h x) x b :=
      (LipschitzWith.const (h x)).lipschitzOnWith.absolutelyContinuousOnInterval
    exact c.add this
  have hHc : ContinuousOn H (uIcc x b) := hHac.continuousOn
  have hΦac : AbsolutelyContinuousOnInterval Φ x b := (hΦc.contDiffOn).absolutelyContinuousOnInterval
  have hF : IntervalIntegrable (fun t => k t * Φ t + H t * Φ' t) volume x b := by
    refine IntervalIntegrable.add ?_ ?_
    · exact hk.mul_continuousOn hΦc.continuous.continuousOn
    · exact (hHc.mul hΦ'c.continuousOn).intervalIntegrable
  have hGac : AbsolutelyContinuousOnInterval
      (fun y => H y * Φ y - ∫ t in x..y, (k t * Φ t + H t * Φ' t)) x b :=
    (hHac.smul hΦac).sub (ac_primitive hF hxmem)
  have hder : ∀ᵐ y, y ∈ uIcc x b → HasDerivAt
      (fun y => H y * Φ y - ∫ t in x..y, (k t * Φ t + H t * Φ' t)) 0 y := by
    filter_upwards [hk.ae_hasDerivAt_integral, hF.ae_hasDerivAt_integral] with y h1 h2 hy
    have d1 : HasDerivAt H (k y) y := (h1 hy x hxmem).const_add (h x)
    have d2 := h2 hy x hxmem
    have := (d1.mul (hΦ y)).sub d2
    exact this.congr_deriv (by simp)
  obtain ⟨C, hC⟩ := hGac.const_of_ae_hasDerivAt_zero hder
  have gx := hC x hxmem
  have gb := hC b right_mem_uIcc
  have hHx : H x = h x := by simp [hH]
  have hHb : H b = h b := by rw [hrep b ⟨hxb, le_rfl⟩]
  have hint : ∫ t in x..b, h t * Φ' t = ∫ t in x..b, H t * Φ' t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hxb] at ht
    simp only [hH]
    rw [hrep t ht]
  have i1 : IntervalIntegrable (fun t => k t * Φ t) volume x b :=
    hk.mul_continuousOn hΦc.continuous.continuousOn
  have i2 : IntervalIntegrable (fun t => H t * Φ' t) volume x b :=
    (hHc.mul hΦ'c.continuousOn).intervalIntegrable
  have hsplit : ∫ t in x..b, (k t * Φ t + H t * Φ' t)
      = (∫ t in x..b, k t * Φ t) + ∫ t in x..b, H t * Φ' t :=
    intervalIntegral.integral_add i1 i2
  simp only [intervalIntegral.integral_same, sub_zero] at gx
  rw [hHx] at gx
  rw [hsplit] at gb
  rw [hint, ← hHb]
  linear_combination gx - gb

end Breakdown.CellCert.CellAnalysis.OneVarTailInternal

namespace Breakdown.CellCert.CellAnalysis.OneVarTailInternal

open Breakdown.CellCert.CellAnalysis

lemma conj_pow_real (r : ℝ) (t : ℕ) : (starRingEnd ℂ) ((r : ℂ) ^ t) = (r : ℂ) ^ t := by
  rw [map_pow, Complex.conj_ofReal]

lemma lineProj_poly (ρ : ℝ → ℝ) (a b : ℝ) (n : ℕ) (f : ℝ → ℂ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ x : ℝ, lineProj ρ a b n f x = P.eval (x : ℂ) := by
  unfold lineProj
  split_ifs with hc
  · refine ⟨∑ j : Fin (n + 1), Polynomial.C (hc.choose j) * Polynomial.X ^ (j : ℕ), ?_, fun x => ?_⟩
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      rw [Polynomial.natDegree_X_pow]
      have := j.isLt
      omega
    · simp [Polynomial.eval_finsetSum]
  · exact ⟨0, by simp, fun x => by simp⟩

lemma lineProj_orth (ρ : ℝ → ℝ) (a b : ℝ) (n : ℕ) (f : ℝ → ℂ)
    (hex : ∃ c : Fin (n + 1) → ℂ, ∀ t : Fin (n + 1),
      ∫ r in Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) *
        (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0) (t : Fin (n + 1)) :
    ∫ r in Icc a b, (ρ r : ℂ) * (f r - lineProj ρ a b n f r) * (r : ℂ) ^ (t : ℕ) = 0 := by
  have e : ∀ r : ℝ, lineProj ρ a b n f r = ∑ j, hex.choose j * (r : ℂ) ^ (j : ℕ) := by
    intro r
    unfold lineProj
    rw [dif_pos hex]
  have := hex.choose_spec t
  simp only [conj_pow_real] at this
  simp only [e]
  exact this

lemma orth_poly {ρ : ℝ → ℝ} {a b : ℝ} {n : ℕ} {u : ℝ → ℂ}
    (horth : ∀ t : Fin (n + 1), ∫ r in Icc a b, (ρ r : ℂ) * u r * (r : ℂ) ^ (t : ℕ) = 0)
    (hint : IntegrableOn (fun r => (ρ r : ℂ) * u r) (Icc a b))
    (P : Polynomial ℂ) (hP : P.natDegree ≤ n) :
    ∫ r in Icc a b, (ρ r : ℂ) * u r * P.eval (r : ℂ) = 0 := by
  have hsum : ∀ r : ℝ, P.eval (r : ℂ) = ∑ t : Fin (n + 1), P.coeff t * (r : ℂ) ^ (t : ℕ) := by
    intro r
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
    exact (Fin.sum_univ_eq_sum_range (fun t => P.coeff t * (r : ℂ) ^ t) (n + 1)).symm
  simp_rw [hsum, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero (fun t _ => ?_)
    have e : (fun r : ℝ => (ρ r : ℂ) * u r * (P.coeff t * (r : ℂ) ^ (t : ℕ)))
        = fun r => P.coeff t * ((ρ r : ℂ) * u r * (r : ℂ) ^ (t : ℕ)) := by
      funext r
      ring
    rw [e, integral_const_mul, horth t, mul_zero]
  · intro t _
    exact hint.mul_continuousOn (by fun_prop) isCompact_Icc

lemma coeff_sum_fin {n : ℕ} (c : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).coeff i = c i := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Fin.ext h.symm)
  · simp

lemma pairing_exists {ρ : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hρc : Continuous ρ)
    (hρ0 : ∀ r ∈ Icc a b, 0 ≤ ρ r) (hρpos : ∀ r ∈ Ioc a b, 0 < ρ r) (n : ℕ) {f : ℝ → ℂ}
    (hf : IntegrableOn (fun r => (ρ r : ℂ) * f r) (Icc a b)) :
    ∃ c : Fin (n + 1) → ℂ, ∀ t : Fin (n + 1),
      ∫ r in Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) *
        (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0 := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun t j => ∫ r in Icc a b, (ρ r : ℂ) * (r : ℂ) ^ (j : ℕ) * (r : ℂ) ^ (t : ℕ)
  let v : Fin (n + 1) → ℂ := fun t => ∫ r in Icc a b, (ρ r : ℂ) * f r * (r : ℂ) ^ (t : ℕ)
  have hMv : ∀ c : Fin (n + 1) → ℂ, ∀ t, (M.mulVec c) t
      = ∫ r in Icc a b, (ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (r : ℂ) ^ (t : ℕ) := by
    intro c t
    simp only [Matrix.mulVec, dotProduct, M]
    have e : ∀ r : ℝ, (ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (r : ℂ) ^ (t : ℕ)
        = ∑ j : Fin (n + 1), ((ρ r : ℂ) * (r : ℂ) ^ (j : ℕ) * (r : ℂ) ^ (t : ℕ)) * c j := by
      intro r
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    simp_rw [e]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun j _ => (integral_mul_const _ _).symm)
    · intro j _
      exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hc' : ∀ t : Fin (n + 1), ∫ r in Icc a b, (ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ))
        * (r : ℂ) ^ (t : ℕ) = 0 := by
      intro t
      rw [← hMv]
      have := congrFun hc t
      simpa using this
    set p : ℝ → ℂ := fun r => ∑ j, c j * (r : ℂ) ^ (j : ℕ) with hp
    let Q : Polynomial ℂ := ∑ j : Fin (n + 1), Polynomial.C ((starRingEnd ℂ) (c j)) * Polynomial.X ^ (j : ℕ)
    have hQ : Q.natDegree ≤ n := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      rw [Polynomial.natDegree_X_pow]
      have := j.isLt
      omega
    have hQe : ∀ r : ℝ, Q.eval (r : ℂ) = (starRingEnd ℂ) (p r) := by
      intro r
      simp [Q, hp, Polynomial.eval_finsetSum, map_sum, Complex.conj_ofReal]
    have hpint : IntegrableOn (fun r => (ρ r : ℂ) * p r) (Icc a b) :=
      (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
    have h0 := orth_poly hc' hpint Q hQ
    rw [show (fun r : ℝ => (ρ r : ℂ) * p r * Q.eval (r : ℂ))
      = fun r => (ρ r : ℂ) * p r * (starRingEnd ℂ) (p r) from funext fun r => by rw [hQe]] at h0
    have hre : ∀ r : ℝ, (ρ r : ℂ) * p r * (starRingEnd ℂ) (p r) = ((ρ r * ‖p r‖ ^ 2 : ℝ) : ℂ) := by
      intro r
      rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [show (fun r : ℝ => (ρ r : ℂ) * p r * (starRingEnd ℂ) (p r))
      = fun r => ((ρ r * ‖p r‖ ^ 2 : ℝ) : ℂ) from funext hre, integral_complex_ofReal,
      Complex.ofReal_eq_zero] at h0
    have hcont : Continuous (fun r => ρ r * ‖p r‖ ^ 2) := by fun_prop
    have hz : (fun r => ρ r * ‖p r‖ ^ 2) =ᵐ[volume.restrict (Icc a b)] 0 := by
      rw [← integral_eq_zero_iff_of_nonneg_ae]
      · exact h0
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact mul_nonneg (hρ0 r hr) (by positivity)
      · exact hcont.continuousOn.integrableOn_compact isCompact_Icc
    have hna : ∀ᵐ r ∂(volume.restrict (Icc a b)), r ≠ a := by
      refine ae_restrict_of_ae ?_
      have : volume ({a} : Set ℝ) = 0 := measure_singleton a
      rw [ae_iff]
      simpa using this
    have hpz : ∀ᵐ r ∂(volume.restrict (Icc a b)), p r = 0 := by
      filter_upwards [hz, hna, ae_restrict_mem measurableSet_Icc] with r h1 h2 h3
      have hpos : 0 < ρ r := hρpos r ⟨lt_of_le_of_ne h3.1 (Ne.symm h2), h3.2⟩
      have : ρ r * ‖p r‖ ^ 2 = 0 := h1
      have : ‖p r‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hpos.ne'
        · exact h
      simpa using this
    have hinf : Set.Infinite {r : ℝ | p r = 0} := by
      intro hfin
      have hnull : volume {r : ℝ | p r = 0} = 0 := hfin.measure_zero _
      have hnot : ∀ᵐ r ∂(volume.restrict (Icc a b)), r ∉ {r : ℝ | p r = 0} :=
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull)
      have hfalse : ∀ᵐ r ∂(volume.restrict (Icc a b)), False := by
        filter_upwards [hpz, hnot] with r h1 h2
        exact h2 h1
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero,
        Real.volume_Icc] at hfalse
      simp at hfalse
      linarith
    let P : Polynomial ℂ := ∑ j : Fin (n + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)
    have hPe : ∀ r : ℝ, P.eval (r : ℂ) = p r := by
      intro r
      simp [P, hp, Polynomial.eval_finsetSum]
    have hP0 : P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      have : ((fun r : ℝ => (r : ℂ)) '' {r : ℝ | p r = 0}).Infinite :=
        hinf.image Complex.ofReal_injective.injOn
      refine this.mono ?_
      rintro _ ⟨r, hr, rfl⟩
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def]
      rw [hPe]
      exact hr
    funext i
    have := coeff_sum_fin c i
    rw [show (∑ j : Fin (n + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)) = P from rfl, hP0] at this
    simpa using this.symm
  have hsurj : Function.Surjective M.mulVecLin := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨c, hcv⟩ := hsurj v
  refine ⟨c, fun t => ?_⟩
  have ht := congrFun hcv t
  simp only [Matrix.mulVecLin_apply] at ht
  rw [hMv] at ht
  simp only [conj_pow_real]
  have i1 : IntegrableOn (fun r => (ρ r : ℂ) * f r * (r : ℂ) ^ (t : ℕ)) (Icc a b) :=
    hf.mul_continuousOn (by fun_prop) isCompact_Icc
  have i2 : IntegrableOn (fun r => (ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (r : ℂ) ^ (t : ℕ))
      (Icc a b) := (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
  have e : (fun r : ℝ => (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (r : ℂ) ^ (t : ℕ))
      = fun r => (ρ r : ℂ) * f r * (r : ℂ) ^ (t : ℕ)
        - (ρ r : ℂ) * (∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (r : ℂ) ^ (t : ℕ) := by
    funext r
    ring
  rw [e, integral_sub i1 i2, ht]
  simp [v]

end Breakdown.CellCert.CellAnalysis.OneVarTailInternal

namespace Breakdown.CellCert.CellAnalysis.OneVarTailInternal

open Breakdown.CellCert.CellAnalysis

lemma pc (P : Polynomial ℂ) : Continuous fun r : ℝ => P.eval (r : ℂ) :=
  P.continuous.comp Complex.continuous_ofReal

lemma pd (P : Polynomial ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => P.eval (r : ℂ)) (P.derivative.eval (t : ℂ)) t :=
  (P.hasDerivAt (t : ℂ)).comp_ofReal

lemma cd (P : Polynomial ℂ) : ContDiff ℝ 1 (fun r : ℝ => P.eval (r : ℂ)) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (pd P t).differentiableAt, ?_⟩
  have : deriv (fun r : ℝ => P.eval (r : ℂ)) = fun t : ℝ => P.derivative.eval (t : ℂ) :=
    funext fun t => (pd P t).deriv
  rw [this]
  exact pc _

lemma wt_int {ρ : ℝ → ℝ} {a b : ℝ} (hρc : Continuous ρ) (hρ0 : ∀ r ∈ Icc a b, 0 ≤ ρ r)
    {v : ℝ → ℂ} (hv : AEStronglyMeasurable v (volume.restrict (Icc a b)))
    (hi : IntegrableOn (fun r => ρ r * ‖v r‖ ^ 2) (Icc a b)) :
    IntegrableOn (fun r => (ρ r : ℂ) * v r) (Icc a b) := by
  have hρi : IntegrableOn ρ (Icc a b) := hρc.continuousOn.integrableOn_compact isCompact_Icc
  refine Integrable.mono' (hρi.add hi) ?_ ?_
  · exact (Complex.continuous_ofReal.comp hρc).aestronglyMeasurable.mul hv
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ0 r hr)]
    have h0 := hρ0 r hr
    have h1 : ‖v r‖ ≤ 1 + ‖v r‖ ^ 2 := by nlinarith [norm_nonneg (v r)]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h1 h0]

lemma sq_int {ρ : ℝ → ℝ} {a b : ℝ} (hρc : Continuous ρ) (hρ0 : ∀ r ∈ Icc a b, 0 ≤ ρ r)
    {v : ℝ → ℂ} (hv : AEStronglyMeasurable v (volume.restrict (Icc a b)))
    (hi : IntegrableOn (fun r => ρ r * ‖v r‖ ^ 2) (Icc a b)) (s : ℝ → ℂ) (hs : Continuous s) :
    IntegrableOn (fun r => ρ r * ‖v r - s r‖ ^ 2) (Icc a b) := by
  have hs2 : IntegrableOn (fun r => ρ r * ‖s r‖ ^ 2) (Icc a b) :=
    (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
  refine Integrable.mono' ((hi.const_mul 2).add (hs2.const_mul 2)) ?_ ?_
  · exact hρc.aestronglyMeasurable.mul ((hv.sub hs.aestronglyMeasurable).norm.pow 2)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have h0 := hρ0 r hr
    have ht : ‖v r - s r‖ ≤ ‖v r‖ + ‖s r‖ := norm_sub_le _ _
    have h3 : ‖v r - s r‖ ^ 2 ≤ (‖v r‖ + ‖s r‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    have h2 : ‖v r - s r‖ ^ 2 ≤ 2 * ‖v r‖ ^ 2 + 2 * ‖s r‖ ^ 2 := by
      nlinarith [sq_nonneg (‖v r‖ - ‖s r‖)]
    rw [Real.norm_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]

lemma w_int {ρ W : ℝ → ℝ} {a b : ℝ} (hρc : Continuous ρ) (hWc : Continuous W)
    (hρ0 : ∀ r ∈ Icc a b, 0 ≤ ρ r) (hW01 : ∀ r ∈ Icc a b, 0 ≤ W r ∧ W r ≤ 1)
    {v : ℝ → ℂ} (hv : AEStronglyMeasurable v (volume.restrict (Icc a b)))
    (hi : IntegrableOn (fun r => ρ r * ‖v r‖ ^ 2) (Icc a b)) :
    IntegrableOn (fun r => ρ r * W r * ‖v r‖ ^ 2) (Icc a b) := by
  refine Integrable.mono' hi ((hρc.aestronglyMeasurable.mul hWc.aestronglyMeasurable).mul
    (hv.norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  obtain ⟨h0, h1⟩ := hW01 r hr
  have h2 := hρ0 r hr
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg h2 h0) (sq_nonneg _))]
  have : ρ r * W r ≤ ρ r := by nlinarith
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

lemma ibp_lim {a b : ℝ} (hab : a < b) {h k Φ Φ' : ℝ → ℂ}
    (hrep : ∀ x ∈ Ioc a b, ∀ y ∈ Icc x b, h y = h x + ∫ t in x..y, k t)
    (hk : ∀ x ∈ Ioc a b, IntervalIntegrable k volume x b)
    (hΦ : ∀ t, HasDerivAt Φ (Φ' t) t) (hΦc : ContDiff ℝ 1 Φ) (hΦ'c : Continuous Φ')
    (hΦb : Φ b = 0)
    (hkΦ : IntegrableOn (fun t => k t * Φ t) (Icc a b))
    (hhΦ : IntegrableOn (fun t => h t * Φ' t) (Icc a b))
    (hlim : Tendsto (fun x => h x * Φ x) (𝓝[>] a) (𝓝 0)) :
    ∫ t in Icc a b, k t * Φ t = - ∫ t in Icc a b, h t * Φ' t := by
  have hseg : ∀ x ∈ Ioo a b, h x * Φ x
      = -(∫ t in x..b, k t * Φ t) - ∫ t in x..b, h t * Φ' t := by
    intro x hx
    have := ibp_seg hx.2.le (hrep x ⟨hx.1, hx.2.le⟩) (hk x ⟨hx.1, hx.2.le⟩) hΦ hΦc hΦ'c
    rw [this, hΦb]
    ring
  have c1 : ContinuousOn (fun x => ∫ t in x..b, k t * Φ t) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval_left (by rw [uIcc_of_le hab.le]; exact hkΦ)
  have c2 : ContinuousOn (fun x => ∫ t in x..b, h t * Φ' t) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval_left (by rw [uIcc_of_le hab.le]; exact hhΦ)
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have hmem : uIcc a b ∈ 𝓝[>] a := by
    rw [uIcc_of_le hab.le]
    exact mem_of_superset (Ioo_mem_nhdsGT hab) Ioo_subset_Icc_self
  have t1 := ((c1 a ha).mono_of_mem_nhdsWithin hmem).tendsto
  have t2 := ((c2 a ha).mono_of_mem_nhdsWithin hmem).tendsto
  have t3 : Tendsto (fun x => h x * Φ x) (𝓝[>] a)
      (𝓝 (-(∫ t in a..b, k t * Φ t) - ∫ t in a..b, h t * Φ' t)) := by
    refine (t1.neg.sub t2).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact (hseg x hx).symm
  have heq := tendsto_nhds_unique t3 hlim
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le] at heq
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  linear_combination -heq

end Breakdown.CellCert.CellAnalysis.OneVarTailInternal

namespace Breakdown.CellCert.CellAnalysis.OneVarTailInternal

open Breakdown.CellCert.CellAnalysis

theorem hbase {a b : ℝ} {ρ : ℝ → ℝ} (hab : a < b) (hρc : Continuous ρ)
    (hρ0 : ∀ r ∈ Icc a b, 0 ≤ ρ r) (hρpos : ∀ r ∈ Ioc a b, 0 < ρ r)
    (hρmono : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → ρ x ≤ ρ y)
    {d : ℕ} (hd : 2 ≤ d)
    (hdual : ∀ E : Polynomial ℂ, E.natDegree ≤ d - 2 → ∃ Φp Pp : Polynomial ℂ, Pp.natDegree ≤ d - 1 ∧
      (∀ r : ℝ, Φp.eval (r : ℂ) = (ρ r : ℂ) * ((1 - ((2 * r - a - b) / (b - a)) ^ 2 : ℝ) : ℂ) * E.eval (r : ℂ)) ∧
      (∀ r : ℝ, Φp.derivative.eval (r : ℂ) = (ρ r : ℂ) * Pp.eval (r : ℂ)))
    {f g : ℝ → ℂ}
    (hrep : ∀ x ∈ Set.Ioc a b, ∀ y ∈ Set.Ioc a b, f y = f x + ∫ t in x..y, g t)
    (hfc : ContinuousOn f (Set.Ioc a b))
    (hgm : AEStronglyMeasurable g (volume.restrict (Set.Icc a b)))
    (hgi : IntegrableOn (fun r => ρ r * ‖g r‖ ^ 2) (Set.Icc a b))
    (hfi : IntegrableOn (fun r => ρ r * ‖f r‖ ^ 2) (Set.Icc a b)) :
    IntegrableOn (fun r => ρ r * (1 - ((2 * r - a - b) / (b - a)) ^ 2) *
          ‖deriv (fun x => f x - lineProj ρ a b (d - 1) f x) r‖ ^ 2) (Set.Icc a b) ∧
      ∫ r in Set.Icc a b, ρ r * (1 - ((2 * r - a - b) / (b - a)) ^ 2) *
          ‖deriv (fun x => f x - lineProj ρ a b (d - 1) f x) r‖ ^ 2
        ≤ ∫ r in Set.Icc a b, ρ r * ‖g r - lineProj ρ a b (d - 2) g r‖ ^ 2 := by
  have hba : 0 < b - a := by linarith
  have hne : b - a ≠ 0 := hba.ne'
  set W : ℝ → ℝ := fun r => 1 - ((2 * r - a - b) / (b - a)) ^ 2 with hWdef
  have hWc : Continuous W := by fun_prop
  have hW01 : ∀ r ∈ Icc a b, 0 ≤ W r ∧ W r ≤ 1 := by
    intro r hr
    have hsq : ((2 * r - a - b) / (b - a)) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_one (by positivity)]
      nlinarith [hr.1, hr.2]
    exact ⟨by simp only [hWdef]; linarith, by simp only [hWdef]; nlinarith [sq_nonneg ((2 * r - a - b) / (b - a))]⟩
  have hWb : W b = 0 := by
    simp only [hWdef]
    rw [show 2 * b - a - b = b - a by ring, div_self hne]
    norm_num
  have hWa : W a = 0 := by
    simp only [hWdef]
    rw [show 2 * a - a - b = -(b - a) by ring, neg_div, div_self hne]
    norm_num
  have hIcc : volume.restrict (Icc a b) = volume.restrict (Ioc a b) :=
    (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm
  have hIoo : volume.restrict (Icc a b) = volume.restrict (Ioo a b) :=
    (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm
  have hfm : AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
    rw [hIcc]
    exact hfc.aestronglyMeasurable measurableSet_Ioc
  have hρg := wt_int hρc hρ0 hgm hgi
  have hρf := wt_int hρc hρ0 hfm hfi
  have hex := pairing_exists hab hρc hρ0 hρpos (d - 1) hρf
  have horth := lineProj_orth ρ a b (d - 1) f hex
  obtain ⟨P, hPdeg, hPe⟩ := lineProj_poly ρ a b (d - 1) f
  obtain ⟨S, hSdeg, hSe⟩ := lineProj_poly ρ a b (d - 2) g
  set q := Polynomial.derivative P with hq
  set h : ℝ → ℂ := fun r => f r - P.eval (r : ℂ) with hh
  set k : ℝ → ℂ := fun r => g r - q.eval (r : ℂ) with hk
  have horth' : ∀ t : Fin (d - 1 + 1),
      ∫ r in Icc a b, (ρ r : ℂ) * h r * (r : ℂ) ^ (t : ℕ) = 0 := by
    intro t
    have := horth t
    simp only [hPe] at this
    exact this
  have hρh : IntegrableOn (fun r => (ρ r : ℂ) * h r) (Icc a b) := by
    have : IntegrableOn (fun r => (ρ r : ℂ) * P.eval (r : ℂ)) (Icc a b) :=
      ((Complex.continuous_ofReal.comp hρc).mul (pc P)).continuousOn.integrableOn_compact isCompact_Icc
    exact (hρf.sub this).congr_fun (fun r _ => by simp only [hh, Pi.sub_apply]; ring) measurableSet_Icc
  have hρk : IntegrableOn (fun r => (ρ r : ℂ) * k r) (Icc a b) := by
    have : IntegrableOn (fun r => (ρ r : ℂ) * q.eval (r : ℂ)) (Icc a b) :=
      ((Complex.continuous_ofReal.comp hρc).mul (pc q)).continuousOn.integrableOn_compact isCompact_Icc
    exact (hρg.sub this).congr_fun (fun r _ => by simp only [hk, Pi.sub_apply]; ring) measurableSet_Icc
  have hgloc : ∀ x ∈ Ioc a b, IntervalIntegrable g volume x b := by
    intro x hx
    have hsub : Icc x b ⊆ Icc a b := Icc_subset_Icc hx.1.le le_rfl
    have hpx := hρpos x hx
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx.2]
    refine Integrable.mono' ((hρg.mono_set hsub).norm.const_mul (ρ x)⁻¹)
      (hgm.mono_measure (Measure.restrict_mono hsub le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hxr : ρ x ≤ ρ r := hρmono x ⟨hx.1.le, hx.2⟩ r (hsub hr) hr.1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ0 r (hsub hr)), inv_mul_eq_div,
      le_div_iff₀ hpx]
    nlinarith [norm_nonneg (g r)]
  have hkloc : ∀ x ∈ Ioc a b, IntervalIntegrable k volume x b :=
    fun x hx => (hgloc x hx).sub ((pc q).intervalIntegrable _ _)
  have hrep_h : ∀ x ∈ Ioc a b, ∀ y ∈ Icc x b, h y = h x + ∫ t in x..y, k t := by
    intro x hx y hy
    have hyI : y ∈ Ioc a b := ⟨lt_of_lt_of_le hx.1 hy.1, hy.2⟩
    have hgxy : IntervalIntegrable g volume x y := by
      refine (hgloc x hx).mono_set ?_
      rw [uIcc_of_le hy.1, uIcc_of_le hx.2]
      exact Icc_subset_Icc le_rfl hy.2
    have hq_int : ∫ t in x..y, q.eval (t : ℂ) = P.eval (y : ℂ) - P.eval (x : ℂ) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => pd P t) ((pc q).intervalIntegrable _ _)
    simp only [hh, hk]
    rw [intervalIntegral.integral_sub hgxy ((pc q).intervalIntegrable _ _), hq_int, hrep x hx y hyI]
    ring
  have hderiv : ∀ᵐ r ∂(volume.restrict (Icc a b)),
      deriv (fun x => f x - lineProj ρ a b (d - 1) f x) r = k r := by
    have hall : ∀ᵐ y, ∀ n : ℕ, y ∈ uIcc (a + (b - a) / (n + 2)) b →
        ∀ c ∈ uIcc (a + (b - a) / (n + 2)) b,
          HasDerivAt (fun y => ∫ t in c..y, g t) (g y) y := by
      rw [ae_all_iff]
      intro n
      have hn2 : (0 : ℝ) < n + 2 := by positivity
      have hxn : a + (b - a) / (n + 2) ∈ Ioc a b := by
        constructor
        · have : 0 < (b - a) / (n + 2) := by positivity
          linarith
        · have : (b - a) / (n + 2) ≤ b - a := by
            rw [div_le_iff₀ hn2]
            nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          linarith
      exact (hgloc _ hxn).ae_hasDerivAt_integral
    rw [hIoo]
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioo] with y hy hyI
    have hya : 0 < y - a := by linarith [hyI.1]
    obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / (y - a))
    have hn2 : (0 : ℝ) < n + 2 := by positivity
    have hlt : (b - a) / (n + 2) < y - a := by
      rw [div_lt_iff₀ hn2]
      rw [div_lt_iff₀ hya] at hn
      nlinarith
    have hpos : 0 < (b - a) / (n + 2) := by positivity
    have hxI : a + (b - a) / (n + 2) ∈ Ioc a b := ⟨by linarith, by linarith [hyI.2]⟩
    have hxy : a + (b - a) / (n + 2) < y := by linarith
    have hyu : y ∈ uIcc (a + (b - a) / (n + 2)) b := by
      rw [uIcc_of_le hxI.2]
      exact ⟨hxy.le, hyI.2.le⟩
    have hD := hy n hyu _ left_mem_uIcc
    have hfD : HasDerivAt f (g y) y := by
      have := hD.const_add (f (a + (b - a) / (n + 2)))
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hxy hyI.2] with z hz
      exact hrep _ hxI z ⟨lt_trans hxI.1 hz.1, hz.2.le⟩
    have hPD : HasDerivAt (fun x : ℝ => lineProj ρ a b (d - 1) f x) (q.eval (y : ℂ)) y :=
      (pd P y).congr_of_eventuallyEq (Eventually.of_forall (fun z => hPe z))
    exact (hfD.sub hPD).deriv
  have hkm : AEStronglyMeasurable k (volume.restrict (Icc a b)) :=
    hgm.sub (pc q).aestronglyMeasurable
  have hρk2 : IntegrableOn (fun r => ρ r * ‖k r‖ ^ 2) (Icc a b) :=
    sq_int hρc hρ0 hgm hgi (fun r => q.eval (r : ℂ)) (pc q)
  have hwk2 : IntegrableOn (fun r => ρ r * W r * ‖k r‖ ^ 2) (Icc a b) :=
    w_int hρc hWc hρ0 hW01 hkm hρk2
  have hLHS : (fun r => ρ r * W r * ‖deriv (fun x => f x - lineProj ρ a b (d - 1) f x) r‖ ^ 2)
      =ᵐ[volume.restrict (Icc a b)] fun r => ρ r * W r * ‖k r‖ ^ 2 := by
    filter_upwards [hderiv] with r hr
    rw [hr]
  have horthk : ∀ E : Polynomial ℂ, E.natDegree ≤ d - 2 →
      ∫ r in Icc a b, k r * ((ρ r : ℂ) * (W r : ℂ) * E.eval (r : ℂ)) = 0 := by
    intro E hE
    obtain ⟨Φp, Pp, hPp, hΦe0, hΦd⟩ := hdual E hE
    have hΦe : ∀ r : ℝ, Φp.eval (r : ℂ) = (ρ r : ℂ) * (W r : ℂ) * E.eval (r : ℂ) := hΦe0
    obtain ⟨Bρ, hBρ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hρc.continuousOn
    obtain ⟨BP, hBP⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) (pc P).continuousOn
    set G0 := ∫ r in Icc a b, ‖(ρ r : ℂ) * g r‖ with hG0
    have hbound : ∀ x ∈ Ioo a b, ‖(ρ x : ℂ) * h x‖ ≤ Bρ * ‖f b‖ + G0 + Bρ * BP := by
      intro x hx
      have hxI : x ∈ Ioc a b := ⟨hx.1, hx.2.le⟩
      have hxc : x ∈ Icc a b := Ioo_subset_Icc_self hx
      have hfx : f x = f b - ∫ t in x..b, g t := by
        rw [hrep x hxI b ⟨hab, le_rfl⟩]
        ring
      have hρx : ‖(ρ x : ℂ)‖ ≤ Bρ := by
        rw [Complex.norm_real]
        exact hBρ x hxc
      have hBρ0 : 0 ≤ Bρ := le_trans (norm_nonneg _) hρx
      have hPx := hBP x hxc
      have hsub : Icc x b ⊆ Icc a b := Icc_subset_Icc hx.1.le le_rfl
      have hint_bd : ‖(ρ x : ℂ) * ∫ t in x..b, g t‖ ≤ G0 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ0 x hxc)]
        calc ρ x * ‖∫ t in x..b, g t‖ ≤ ρ x * ∫ t in x..b, ‖g t‖ :=
              mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hx.2.le)
                (hρ0 x hxc)
          _ = ∫ t in x..b, ρ x * ‖g t‖ := (intervalIntegral.integral_const_mul _ _).symm
          _ ≤ ∫ t in x..b, ‖(ρ t : ℂ) * g t‖ := by
              apply intervalIntegral.integral_mono_on hx.2.le
              · exact ((hgloc x hxI).norm).const_mul _
              · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx.2.le).mpr
                  ((hρg.mono_set hsub).norm)
              · intro t ht
                rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ0 t (hsub ht))]
                exact mul_le_mul_of_nonneg_right (hρmono x hxc t (hsub ht) ht.1) (norm_nonneg _)
          _ = ∫ t in Ioc x b, ‖(ρ t : ℂ) * g t‖ := intervalIntegral.integral_of_le hx.2.le
          _ ≤ G0 := setIntegral_mono_set hρg.norm
              (Eventually.of_forall (fun t => norm_nonneg _))
              (Ioc_subset_Icc_self.trans hsub).eventuallyLE
      rw [show (ρ x : ℂ) * h x = (ρ x : ℂ) * f b - (ρ x : ℂ) * (∫ t in x..b, g t)
          - (ρ x : ℂ) * P.eval (x : ℂ) by simp only [hh]; rw [hfx]; ring]
      refine (norm_sub_le_of_le (norm_sub_le _ _) le_rfl).trans ?_
      rw [norm_mul (ρ x : ℂ) (f b), norm_mul (ρ x : ℂ) (P.eval (x : ℂ))]
      have e1 := mul_le_mul_of_nonneg_right hρx (norm_nonneg (f b))
      have e3 := mul_le_mul hρx hPx (norm_nonneg _) hBρ0
      linarith
    have hWE : Tendsto (fun x : ℝ => (W x : ℂ) * E.eval (x : ℂ)) (𝓝[>] a) (𝓝 0) := by
      have hc : Continuous (fun x : ℝ => (W x : ℂ) * E.eval (x : ℂ)) :=
        (Complex.continuous_ofReal.comp hWc).mul (pc E)
      have h0 : (fun x : ℝ => (W x : ℂ) * E.eval (x : ℂ)) a = 0 := by simp [hWa]
      rw [← h0]
      exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun x => h x * Φp.eval (x : ℂ)) (𝓝[>] a) (𝓝 0) := by
      have hT : Tendsto (fun x : ℝ => (Bρ * ‖f b‖ + G0 + Bρ * BP) * ‖(W x : ℂ) * E.eval (x : ℂ)‖)
          (𝓝[>] a) (𝓝 0) := by
        have := (hWE.norm).const_mul (Bρ * ‖f b‖ + G0 + Bρ * BP)
        simpa using this
      refine squeeze_zero_norm' ?_ hT
      filter_upwards [Ioo_mem_nhdsGT hab] with x hx
      rw [show h x * Φp.eval (x : ℂ) = ((ρ x : ℂ) * h x) * ((W x : ℂ) * E.eval (x : ℂ)) by
        rw [hΦe]; ring, norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _)
    have hkΦ : IntegrableOn (fun t => k t * Φp.eval (t : ℂ)) (Icc a b) := by
      have := hρk.mul_continuousOn ((Complex.continuous_ofReal.comp hWc).mul (pc E)).continuousOn
        isCompact_Icc
      exact this.congr_fun (fun r _ => by
        simp only [Pi.mul_apply, Function.comp_apply, hΦe]; ring) measurableSet_Icc
    have hhΦ : IntegrableOn (fun t => h t * Φp.derivative.eval (t : ℂ)) (Icc a b) := by
      have := hρh.mul_continuousOn (pc Pp).continuousOn isCompact_Icc
      exact this.congr_fun (fun r _ => by simp only [hΦd]; ring) measurableSet_Icc
    have hΦb : Φp.eval (b : ℂ) = 0 := by
      rw [hΦe, hWb]
      simp
    have key := ibp_lim hab hrep_h hkloc (pd Φp) (cd Φp) (pc _) hΦb hkΦ hhΦ hlim
    have e1 : (fun r => k r * ((ρ r : ℂ) * (W r : ℂ) * E.eval (r : ℂ)))
        = fun r => k r * Φp.eval (r : ℂ) := funext fun r => by rw [hΦe]
    rw [e1, key]
    have e2 : (fun r => h r * Φp.derivative.eval (r : ℂ))
        = fun r => (ρ r : ℂ) * h r * Pp.eval (r : ℂ) := funext fun r => by rw [hΦd]; ring
    rw [e2, orth_poly horth' hρh Pp (by omega), neg_zero]
  set e := q - S with he
  have hedeg : e.natDegree ≤ d - 2 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ hSdeg)
    exact (Polynomial.natDegree_derivative_le P).trans (by omega)
  set E := e.map (starRingEnd ℂ) with hE
  have hEdeg : E.natDegree ≤ d - 2 := Polynomial.natDegree_map_le.trans hedeg
  have hEe : ∀ r : ℝ, E.eval (r : ℂ) = (starRingEnd ℂ) (e.eval (r : ℂ)) := by
    intro r
    rw [hE, Polynomial.eval_map]
    conv_lhs => rw [← Complex.conj_ofReal r]
    exact Polynomial.eval₂_hom _ _
  have hvk : ∀ r : ℝ, g r - S.eval (r : ℂ) = k r + e.eval (r : ℂ) := by
    intro r
    simp only [hk, he, Polynomial.eval_sub]
    ring
  have hpt : ∀ r : ℝ, ρ r * W r * ‖g r - S.eval (r : ℂ)‖ ^ 2
      = ρ r * W r * ‖k r‖ ^ 2 + ρ r * W r * ‖e.eval (r : ℂ)‖ ^ 2
        + 2 * (k r * ((ρ r : ℂ) * (W r : ℂ) * E.eval (r : ℂ))).re := by
    intro r
    rw [hvk, hEe, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    have : k r * ((ρ r : ℂ) * (W r : ℂ) * (starRingEnd ℂ) (e.eval (r : ℂ)))
        = ((ρ r * W r : ℝ) : ℂ) * (k r * (starRingEnd ℂ) (e.eval (r : ℂ))) := by
      push_cast
      ring
    rw [this, Complex.re_ofReal_mul]
    ring
  have hI2 : IntegrableOn (fun r => ρ r * W r * ‖e.eval (r : ℂ)‖ ^ 2) (Icc a b) :=
    ((hρc.mul hWc).mul ((pc e).norm.pow 2)).continuousOn.integrableOn_compact isCompact_Icc
  have hI3c : IntegrableOn (fun r => k r * ((ρ r : ℂ) * (W r : ℂ) * E.eval (r : ℂ))) (Icc a b) :=
    (hρk.mul_continuousOn ((Complex.continuous_ofReal.comp hWc).mul (pc E)).continuousOn
      isCompact_Icc).congr_fun (fun r _ => by
        simp only [Pi.mul_apply, Function.comp_apply]; ring) measurableSet_Icc
  have hI3 : IntegrableOn (fun r => 2 * (k r * ((ρ r : ℂ) * (W r : ℂ) * E.eval (r : ℂ))).re)
      (Icc a b) := hI3c.re.const_mul 2
  have hre0 : ∫ r in Icc a b, 2 * (k r * ((ρ r : ℂ) * (W r : ℂ) * E.eval (r : ℂ))).re = 0 := by
    rw [integral_const_mul]
    have := integral_re hI3c
    simp only [RCLike.re_to_complex] at this
    rw [this, horthk E hEdeg]
    simp
  have hsum : ∫ r in Icc a b, ρ r * W r * ‖g r - S.eval (r : ℂ)‖ ^ 2
      = (∫ r in Icc a b, ρ r * W r * ‖k r‖ ^ 2) + (∫ r in Icc a b, ρ r * W r * ‖e.eval (r : ℂ)‖ ^ 2)
        + ∫ r in Icc a b, 2 * (k r * ((ρ r : ℂ) * (W r : ℂ) * E.eval (r : ℂ))).re := by
    simp_rw [hpt]
    have hI12 : IntegrableOn (fun r => ρ r * W r * ‖k r‖ ^ 2 + ρ r * W r * ‖e.eval (r : ℂ)‖ ^ 2)
        (Icc a b) := hwk2.add hI2
    rw [integral_add hI12 hI3, integral_add hwk2 hI2]
  have hnn : 0 ≤ ∫ r in Icc a b, ρ r * W r * ‖e.eval (r : ℂ)‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Icc
      (fun r hr => mul_nonneg (mul_nonneg (hρ0 r hr) (hW01 r hr).1) (sq_nonneg _))
  have hgS := sq_int hρc hρ0 hgm hgi (fun r => S.eval (r : ℂ)) (pc S)
  have hmono : ∫ r in Icc a b, ρ r * W r * ‖g r - S.eval (r : ℂ)‖ ^ 2
      ≤ ∫ r in Icc a b, ρ r * ‖g r - S.eval (r : ℂ)‖ ^ 2 := by
    refine setIntegral_mono_on (w_int hρc hWc hρ0 hW01 (hgm.sub (pc S).aestronglyMeasurable) hgS)
      hgS measurableSet_Icc (fun r hr => ?_)
    obtain ⟨h0, h1⟩ := hW01 r hr
    have h2 := hρ0 r hr
    have : ρ r * W r ≤ ρ r := by nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  refine ⟨hwk2.congr hLHS.symm, ?_⟩
  rw [integral_congr_ae hLHS]
  have hR : (fun r => ρ r * ‖g r - lineProj ρ a b (d - 2) g r‖ ^ 2)
      = fun r => ρ r * ‖g r - S.eval (r : ℂ)‖ ^ 2 := funext fun r => by rw [hSe]
  rw [hR]
  linarith [hsum, hnn, hmono, hre0]

end Breakdown.CellCert.CellAnalysis.OneVarTailInternal

namespace Breakdown.CellCert.CellAnalysis.OneVarTailInternal

open Breakdown.CellCert.CellAnalysis Polynomial

lemma dual_one {a b : ℝ} (hab : a < b) {d : ℕ} (hd : 2 ≤ d) :
    ∀ E : Polynomial ℂ, E.natDegree ≤ d - 2 → ∃ Φp Pp : Polynomial ℂ, Pp.natDegree ≤ d - 1 ∧
      (∀ r : ℝ, Φp.eval (r : ℂ) = (((fun _ => (1 : ℝ)) r : ℝ) : ℂ) *
        ((1 - ((2 * r - a - b) / (b - a)) ^ 2 : ℝ) : ℂ) * E.eval (r : ℂ)) ∧
      (∀ r : ℝ, Φp.derivative.eval (r : ℂ) = (((fun _ => (1 : ℝ)) r : ℝ) : ℂ) * Pp.eval (r : ℂ)) := by
  intro E hE
  have hne : b - a ≠ 0 := by linarith
  let Wp : Polynomial ℂ := 1 - (C ((2 / (b - a) : ℝ) : ℂ) * X - C (((a + b) / (b - a) : ℝ) : ℂ)) ^ 2
  have hWdeg : Wp.natDegree ≤ 2 := by
    simp only [Wp]
    compute_degree
  have hWe : ∀ r : ℝ, Wp.eval (r : ℂ) = ((1 - ((2 * r - a - b) / (b - a)) ^ 2 : ℝ) : ℂ) := by
    intro r
    have key : (2 / (b - a)) * r - (a + b) / (b - a) = (2 * r - a - b) / (b - a) := by
      field_simp
      ring
    simp only [Wp, eval_sub, eval_one, eval_pow, eval_mul, eval_C, eval_X]
    rw [← key]
    push_cast
    ring
  refine ⟨Wp * E, derivative (Wp * E), ?_, fun r => ?_, fun r => ?_⟩
  · refine (natDegree_derivative_le _).trans ?_
    have := natDegree_mul_le (p := Wp) (q := E)
    omega
  · rw [eval_mul, hWe]
    push_cast
    ring
  · simp

lemma dual_id {b : ℝ} (hb : 0 < b) {d : ℕ} (hd : 2 ≤ d) :
    ∀ E : Polynomial ℂ, E.natDegree ≤ d - 2 → ∃ Φp Pp : Polynomial ℂ, Pp.natDegree ≤ d - 1 ∧
      (∀ r : ℝ, Φp.eval (r : ℂ) = ((id r : ℝ) : ℂ) *
        ((1 - ((2 * r - 0 - b) / (b - 0)) ^ 2 : ℝ) : ℂ) * E.eval (r : ℂ)) ∧
      (∀ r : ℝ, Φp.derivative.eval (r : ℂ) = ((id r : ℝ) : ℂ) * Pp.eval (r : ℂ)) := by
  intro E hE
  have hne : b ≠ 0 := hb.ne'
  let U : Polynomial ℂ := (C ((4 / b : ℝ) : ℂ) - C ((4 / b ^ 2 : ℝ) : ℂ) * X) * E
  have hUdeg : U.natDegree ≤ d - 1 := by
    have h1 : (C ((4 / b : ℝ) : ℂ) - C ((4 / b ^ 2 : ℝ) : ℂ) * X).natDegree ≤ 1 := by
      compute_degree
    have := natDegree_mul_le (p := C ((4 / b : ℝ) : ℂ) - C ((4 / b ^ 2 : ℝ) : ℂ) * X) (q := E)
    simp only [U]
    omega
  refine ⟨X ^ 2 * U, C 2 * U + X * derivative U, ?_, fun r => ?_, fun r => ?_⟩
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans hUdeg
    · refine natDegree_mul_le.trans ?_
      have h1 := natDegree_X_le (R := ℂ)
      have h2 := natDegree_derivative_le U
      omega
  · have key : (1 - ((2 * r - 0 - b) / (b - 0)) ^ 2 : ℝ) = r * (4 / b - 4 / b ^ 2 * r) := by
      field_simp
      ring
    rw [key]
    simp only [U, eval_mul, eval_pow, eval_X, eval_sub, eval_C, id]
    push_cast
    ring
  · simp only [derivative_mul, derivative_X_pow, eval_add, eval_mul, eval_pow, eval_X, eval_C, id]
    push_cast
    ring

theorem main_statement : OneVarTailGoodStatement := by
  intro a b ρ ha hab hρ d hd f g hrep hfc hgm hgi hfi
  rcases hρ with rfl | ⟨rfl, rfl⟩
  · exact hbase hab continuous_const (fun _ _ => zero_le_one) (fun _ _ => one_pos)
      (fun _ _ _ _ _ => le_rfl) hd (dual_one hab hd) hrep hfc hgm hgi hfi
  · exact hbase hab continuous_id (fun r hr => hr.1) (fun r hr => hr.1)
      (fun _ _ _ _ hxy => hxy) hd (dual_id hab hd) hrep hfc hgm hgi hfi

end Breakdown.CellCert.CellAnalysis.OneVarTailInternal

namespace Breakdown.CellCert.CellAnalysis

theorem oneVarTailGood : OneVarTailGoodStatement :=
  OneVarTailInternal.main_statement

end Breakdown.CellCert.CellAnalysis
