import Breakdown.Cert.CoerciveSmoothPiecePairingSplitWeight

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPairingClass

open ModeL2Internal (IsSquareField)

abbrev periodProductMeasure : Measure (ℝ × Space) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)

theorem memLp_of_real {h : ℝ → Space → ℝ}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => h z.1 z.2) periodProductMeasure)
    (h2 : periodLIntegral (fun σ y => h σ y ^ 2) < ⊤) :
    MemLp (fun z : ℝ × Space => h z.1 z.2) 2 periodProductMeasure := by
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine ⟨(hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [lintegral_prod _ ((hm.aemeasurable.pow_const 2).ennreal_ofReal)]
  exact h2

theorem lt_top_of_memLp_real {h : ℝ → Space → ℝ}
    (hh : MemLp (fun z : ℝ × Space => h z.1 z.2) 2 periodProductMeasure) :
    periodLIntegral (fun σ y => h σ y ^ 2) < ⊤ := by
  have hi := (memLp_two_iff_integrable_sq_norm hh.1).1 hh
  simp only [Real.norm_eq_abs, sq_abs] at hi
  unfold periodLIntegral
  rw [← lintegral_prod _ hi.1.aemeasurable.ennreal_ofReal]
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)).1 hi.2

theorem memLp_of_continuous_real {h : ℝ → Space → ℝ} (hc : Continuous (fun z : ℝ × Space => h z.1 z.2))
    (h2 : periodLIntegral (fun σ y => h σ y ^ 2) < ⊤) :
    MemLp (fun z : ℝ × Space => h z.1 z.2) 2 periodProductMeasure :=
  memLp_of_real hc.aestronglyMeasurable h2

theorem memLp_of_bound {h g : ℝ → Space → ℝ} (hc : Continuous (fun z : ℝ × Space => h z.1 z.2))
    (hg : MemLp (fun z : ℝ × Space => g z.1 z.2) 2 periodProductMeasure)
    (hb : ∀ σ y, |h σ y| ≤ g σ y) : MemLp (fun z : ℝ × Space => h z.1 z.2) 2 periodProductMeasure :=
  hg.of_le hc.aestronglyMeasurable (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hb z.1 z.2).trans (le_abs_self _))

theorem norm_iter_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space → F) (y : Space) :
    ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fun x => fderiv ℝ f x) y‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := y) (n := 1)
  rw [norm_iteratedFDeriv_one] at h
  exact h.symm

theorem norm_iter_three (f : Space → Space) (y : Space) :
    ‖iteratedFDeriv ℝ 3 f y‖ = ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ f x') x) y‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := y) (n := 2)
  rw [norm_iter_two] at h
  exact h.symm

theorem slice_contDiff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {V : ℝ → Space → G}
    (hV : ContDiff ℝ ∞ (fun z : ℝ × Space => V z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (V z.1) z.2) :=
  PairingSplitInternal.contDiff_slice hV (by exact_mod_cast le_rfl)

theorem time_contDiff {V : ℝ → Space → Space} (hV : ContDiff ℝ ∞ (fun z : ℝ × Space => V z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => deriv (fun s => V s z.2) z.1) := by
  have dt : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun s => V s z.2) z.1) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (s : ℝ) => V s z.2) (g := fun z => z.1)
      (hV.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst (by exact_mod_cast le_rfl)
  exact dt.clm_apply contDiff_const

theorem transport_contDiff (P : ℝ) {v : ℝ → Space → Space}
    (hV : ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => transportPart P v z.1 z.2) := by
  unfold transportPart
  exact (((time_contDiff hV).const_smul (1 / P)).add (hV.const_smul (1 / 2 : ℝ))).add
    (((slice_contDiff hV).clm_apply contDiff_snd).const_smul (1 / 2 : ℝ))

theorem slice_of_joint {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {n : WithTop ℕ∞}
    {V : ℝ → Space → G} (hV : ContDiff ℝ n (fun z : ℝ × Space => V z.1 z.2)) (σ : ℝ) :
    ContDiff ℝ n (V σ) :=
  hV.comp (contDiff_const.prodMk contDiff_id)

theorem smoothRight_eq (P : ℝ) (W v : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    smoothRight P W v σ y = transportPart P v σ y - secondDerivTrace (secondDerivField v σ y)
      + fderiv ℝ (v σ) y (W σ y) + fderiv ℝ (W σ) y (v σ y) := rfl

theorem secondDerivTrace_contDiff {v : ℝ → Space → Space} (hV : ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => secondDerivTrace (secondDerivField v z.1 z.2)) := by
  have d2 := slice_contDiff (V := fun s x => fderiv ℝ (v s) x) (slice_contDiff hV)
  unfold secondDerivTrace secondDerivField
  exact ContDiff.sum fun j _ => (d2.clm_apply contDiff_const).clm_apply contDiff_const

theorem smoothRight_contDiff' {P : ℝ} {W v : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ 1 (fun z : ℝ × Space => smoothRight P W v z.1 z.2) := by
  have hV := hv.smooth
  have d1 := slice_contDiff hV
  have dW : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    PairingSplitInternal.contDiff_slice (V := W) hW (by norm_num)
  have hW1 : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2) := hW.of_le (by norm_num)
  have c1 : ContDiff ℝ 1 (fun z : ℝ × Space => transportPart P v z.1 z.2) :=
    (transport_contDiff P hV).of_le (by norm_cast)
  have c4 : ContDiff ℝ 1 (fun z : ℝ × Space => secondDerivTrace (secondDerivField v z.1 z.2)) :=
    (secondDerivTrace_contDiff hV).of_le (by norm_cast)
  have c5 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2 (W z.1 z.2)) :=
    (d1.of_le (by norm_cast)).clm_apply hW1
  have c6 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
    dW.clm_apply (hV.of_le (by norm_cast))
  exact ((c1.sub c4).add c5).add c6

theorem smoothRight_periodic' {P : ℝ} {W v : ℝ → Space → Space} (hWp : IsTimePeriodic W)
    (hv : IsSmoothPerturbation P v) : IsTimePeriodic (smoothRight P W v) := by
  have hvp := hv.periodic
  intro σ y
  have ev : v (σ + 1) = v σ := funext fun x => hvp σ x
  have eW : W (σ + 1) = W σ := funext fun x => hWp σ x
  have ed : deriv (fun s => v s y) (σ + 1) = deriv (fun s => v s y) σ := by
    have key := deriv_comp_add_const (f := fun s => v s y) (a := (1 : ℝ)) (x := σ)
    have e : (fun x => v (x + 1) y) = fun s => v s y := funext fun s => hvp s y
    simp only [e] at key
    exact key.symm
  unfold smoothRight secondDerivField
  rw [ed, ev, eW]

theorem norm_secondDerivTrace_le (H : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondDerivTrace H‖ ≤ 3 * ‖H‖ := by
  unfold secondDerivTrace
  calc ‖∑ j : Fin 3, H (unitVector j) (unitVector j)‖ ≤ ∑ j : Fin 3, ‖H (unitVector j) (unitVector j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖H‖ := Finset.sum_le_sum fun j _ => by
        have h1 := (H (unitVector j)).le_opNorm (unitVector j)
        have h2 := H.le_opNorm (unitVector j)
        have hu : ‖unitVector j‖ = 1 := by simp [unitVector]
        rw [hu, mul_one] at h1 h2
        exact h1.trans h2
    _ = 3 * ‖H‖ := by simp

def traceCLM : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] Space :=
  ∑ j : Fin 3, (ContinuousLinearMap.apply ℝ Space (unitVector j)).comp
    (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j))

theorem traceCLM_apply (H : Space →L[ℝ] Space →L[ℝ] Space) : traceCLM H = secondDerivTrace H := by
  simp [traceCLM, secondDerivTrace]

theorem norm_fderiv_trace_le {g : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {y : Space}
    (hg : DifferentiableAt ℝ g y) :
    ‖fderiv ℝ (fun x => secondDerivTrace (g x)) y‖ ≤ 3 * ‖fderiv ℝ g y‖ := by
  have e : (fun x => secondDerivTrace (g x)) = fun x => traceCLM (g x) := funext fun x => (traceCLM_apply _).symm
  have hd : HasFDerivAt (fun x => traceCLM (g x)) (traceCLM.comp (fderiv ℝ g y)) y :=
    traceCLM.hasFDerivAt.comp y hg.hasFDerivAt
  rw [e, hd.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hT : ‖traceCLM‖ ≤ 3 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun H => by
      rw [traceCLM_apply]; exact norm_secondDerivTrace_le H
  exact mul_le_mul_of_nonneg_right hT (norm_nonneg _)

theorem norm_fderiv_apply_le {f : Space → (Space →L[ℝ] Space)} {g : Space → Space} {N : ℕ∞ω}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) (hN : (1 : ℕ∞ω) ≤ N) (y : Space) :
    ‖fderiv ℝ (fun x => f x (g x)) y‖ ≤ ‖f y‖ * ‖fderiv ℝ g y‖ + ‖fderiv ℝ f y‖ * ‖g y‖ := by
  have h := norm_iteratedFDeriv_clm_apply (n := 1) hf hg y hN
  simpa [Finset.sum_range_succ, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one] using h

theorem decay_nonneg {W : ℝ → Space → Space} {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) : 0 ≤ D := by
  have h := hD 0 0 0 (by norm_num)
  have e : D / (1 + ‖(0 : Space)‖) ^ (0 + 1) = D := by simp
  rw [e] at h
  exact (norm_nonneg _).trans h

theorem div_pow_le_div {D a r : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a) (hr : 0 ≤ r) {k : ℕ} (hk : 1 ≤ k) :
    D / (1 + r) ^ k * a ≤ D * (a / (1 + r)) := by
  have h1 : 1 + r ≤ (1 + r) ^ k := le_self_pow₀ (by linarith) (by omega)
  have h0 : 0 < 1 + r := by linarith
  rw [div_mul_eq_mul_div, mul_div_assoc']
  exact div_le_div_of_nonneg_left (mul_nonneg hD ha) h0 h1

theorem div_pow_le {D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) (k : ℕ) : D / (1 + r) ^ k ≤ D :=
  div_le_self hD (one_le_pow₀ (by linarith))

theorem weighted_continuous {v : ℝ → Space → Space} (hc : Continuous (fun z : ℝ × Space => v z.1 z.2)) :
    Continuous (fun z : ℝ × Space => ‖v z.1 z.2‖ / (1 + ‖z.2‖)) :=
  hc.norm.div (continuous_const.add continuous_snd.norm) fun z => by positivity

theorem memLp_weighted {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    MemLp (fun z : ℝ × Space => ‖v z.1 z.2‖ / (1 + ‖z.2‖)) 2 periodProductMeasure := by
  refine memLp_of_continuous_real (h := fun σ y => ‖v σ y‖ / (1 + ‖y‖))
    (weighted_continuous hv.smooth.continuous) ?_
  have e : (fun σ y => (‖v σ y‖ / (1 + ‖y‖)) ^ 2) = fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 :=
    funext fun σ => funext fun y => div_pow _ _ 2
  rw [e]
  exact hv.weighted_finite

theorem memLp_deriv_one {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    MemLp (fun z : ℝ × Space => ‖fderiv ℝ (v z.1) z.2‖) 2 periodProductMeasure := by
  refine memLp_of_continuous_real (h := fun σ y => ‖fderiv ℝ (v σ) y‖)
    (slice_contDiff hv.smooth).continuous.norm ?_
  have e : (fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2) = fun σ y => ‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2 :=
    funext fun σ => funext fun y => by rw [norm_iteratedFDeriv_one]
  rw [e]
  exact hv.derivatives_finite 1 le_rfl

theorem memLp_deriv_two {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    MemLp (fun z : ℝ × Space => ‖fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2‖) 2 periodProductMeasure := by
  refine memLp_of_continuous_real (h := fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖)
    (slice_contDiff (V := fun s x => fderiv ℝ (v s) x) (slice_contDiff hv.smooth)).continuous.norm ?_
  have e : (fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2)
      = fun σ y => ‖iteratedFDeriv ℝ 2 (v σ) y‖ ^ 2 :=
    funext fun σ => funext fun y => by rw [norm_iter_two]
  rw [e]
  exact hv.derivatives_finite 2 (by norm_num)

theorem memLp_deriv_three {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    MemLp (fun z : ℝ × Space =>
      ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v z.1) x') x) z.2‖) 2 periodProductMeasure := by
  refine memLp_of_continuous_real
    (h := fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖)
    (slice_contDiff (V := fun s x => fderiv ℝ (fun x' => fderiv ℝ (v s) x') x)
      (slice_contDiff (V := fun s x => fderiv ℝ (v s) x) (slice_contDiff hv.smooth))).continuous.norm ?_
  have e : (fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖ ^ 2)
      = fun σ y => ‖iteratedFDeriv ℝ 3 (v σ) y‖ ^ 2 :=
    funext fun σ => funext fun y => by rw [norm_iter_three]
  rw [e]
  exact hv.derivatives_finite 3 (by norm_num)

theorem memLp_transport {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    MemLp (fun z : ℝ × Space => ‖transportPart P v z.1 z.2‖) 2 periodProductMeasure := by
  refine memLp_of_continuous_real (h := fun σ y => ‖transportPart P v σ y‖)
    (transport_contDiff P hv.smooth).continuous.norm ?_
  have e : (fun σ y => ‖transportPart P v σ y‖ ^ 2) = fun σ y => ‖iteratedFDeriv ℝ 0 (transportPart P v σ) y‖ ^ 2 :=
    funext fun σ => funext fun y => by rw [norm_iteratedFDeriv_zero]
  rw [e]
  exact hv.transport_finite 0

theorem memLp_transport_deriv {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    MemLp (fun z : ℝ × Space => ‖fderiv ℝ (transportPart P v z.1) z.2‖) 2 periodProductMeasure := by
  refine memLp_of_continuous_real (h := fun σ y => ‖fderiv ℝ (transportPart P v σ) y‖)
    (slice_contDiff (transport_contDiff P hv.smooth)).continuous.norm ?_
  have e : (fun σ y => ‖fderiv ℝ (transportPart P v σ) y‖ ^ 2)
      = fun σ y => ‖iteratedFDeriv ℝ 1 (transportPart P v σ) y‖ ^ 2 :=
    funext fun σ => funext fun y => by rw [norm_iteratedFDeriv_one]
  rw [e]
  exact hv.transport_finite 1

theorem smoothRight_norm_le (P : ℝ) {W v : ℝ → Space → Space} {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) (σ : ℝ) (y : Space) :
    ‖smoothRight P W v σ y‖ ≤ ‖transportPart P v σ y‖ + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖
      + D * ‖fderiv ℝ (v σ) y‖ + D * (‖v σ y‖ / (1 + ‖y‖)) := by
  have hD0 := decay_nonneg hD
  have hr := norm_nonneg y
  have h0 : ‖W σ y‖ ≤ D := by
    have h := hD σ y 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (div_pow_le hD0 hr _)
  have h1 : ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 := by
    have h := hD σ y 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at h
  have eH : ‖secondDerivTrace (secondDerivField v σ y)‖ ≤ 3 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ :=
    norm_secondDerivTrace_le _
  have eA : ‖fderiv ℝ (v σ) y (W σ y)‖ ≤ D * ‖fderiv ℝ (v σ) y‖ :=
    ((fderiv ℝ (v σ) y).le_opNorm _).trans (by
      rw [mul_comm D]; exact mul_le_mul_of_nonneg_left h0 (norm_nonneg _))
  have eB : ‖fderiv ℝ (W σ) y (v σ y)‖ ≤ D * (‖v σ y‖ / (1 + ‖y‖)) :=
    ((fderiv ℝ (W σ) y).le_opNorm _).trans ((mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
      (div_pow_le_div hD0 (norm_nonneg _) hr (by norm_num)))
  rw [smoothRight_eq]
  calc ‖transportPart P v σ y - secondDerivTrace (secondDerivField v σ y) + fderiv ℝ (v σ) y (W σ y)
        + fderiv ℝ (W σ) y (v σ y)‖
      ≤ ‖transportPart P v σ y‖ + ‖secondDerivTrace (secondDerivField v σ y)‖ + ‖fderiv ℝ (v σ) y (W σ y)‖
        + ‖fderiv ℝ (W σ) y (v σ y)‖ := by
        exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

theorem smoothRight_square' {P : ℝ} {W v : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWd : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) : IsSquareField (smoothRight P W v) := by
  obtain ⟨D, hD⟩ := hWd
  have hc := (smoothRight_contDiff' hW hv).continuous
  refine ⟨hc.aestronglyMeasurable, smoothRight_periodic' hWp hv, ?_⟩
  have hg := (((memLp_transport hv).add ((memLp_deriv_two hv).const_mul 3)).add
    ((memLp_deriv_one hv).const_mul D)).add ((memLp_weighted hv).const_mul D)
  have hm := memLp_of_bound (h := fun σ y => ‖smoothRight P W v σ y‖)
    (g := fun σ y => ‖transportPart P v σ y‖ + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖
      + D * ‖fderiv ℝ (v σ) y‖ + D * (‖v σ y‖ / (1 + ‖y‖))) hc.norm hg
    (fun σ y => by rw [abs_norm]; exact smoothRight_norm_le P hD σ y)
  exact lt_top_of_memLp_real hm

theorem smoothRight_fderiv_norm_le (P : ℝ) {W v : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) (σ : ℝ) (y : Space) :
    ‖fderiv ℝ (smoothRight P W v σ) y‖ ≤ ‖fderiv ℝ (transportPart P v σ) y‖
      + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖
      + (D * ‖fderiv ℝ (v σ) y‖ + D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖)
      + (D * ‖fderiv ℝ (v σ) y‖ + D * (‖v σ y‖ / (1 + ‖y‖))) := by
  have hD0 := decay_nonneg hD
  have hr := norm_nonneg y
  have hvs : ContDiff ℝ ∞ (v σ) := slice_of_joint hv.smooth σ
  have hWs : ContDiff ℝ 2 (W σ) := slice_of_joint hW σ
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := hvs.fderiv_right (by exact_mod_cast le_rfl)
  have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (v σ))) := hD1.fderiv_right (by exact_mod_cast le_rfl)
  have hWD : ContDiff ℝ 1 (fderiv ℝ (W σ)) := hWs.fderiv_right (by norm_num)
  have hT : ContDiff ℝ ∞ (transportPart P v σ) := slice_of_joint (transport_contDiff P hv.smooth) σ
  have dT : DifferentiableAt ℝ (transportPart P v σ) y := (hT.differentiable (by simp)) y
  have dH : DifferentiableAt ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y := by
    have e : (fun x => secondDerivTrace (secondDerivField v σ x)) = fun x => traceCLM (fderiv ℝ (fderiv ℝ (v σ)) x) :=
      funext fun x => (traceCLM_apply _).symm
    rw [e]
    exact traceCLM.differentiableAt.comp y ((hD2.differentiable (by simp)) y)
  have dA : DifferentiableAt ℝ (fun x => fderiv ℝ (v σ) x (W σ x)) y :=
    ((hD1.differentiable (by simp)) y).clm_apply ((hWs.differentiable (by norm_num)) y)
  have dB : DifferentiableAt ℝ (fun x => fderiv ℝ (W σ) x (v σ x)) y :=
    ((hWD.differentiable (by norm_num)) y).clm_apply ((hvs.differentiable (by simp)) y)
  have w0 : ‖W σ y‖ ≤ D := by
    have h := hD σ y 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (div_pow_le hD0 hr _)
  have w1 : ‖fderiv ℝ (W σ) y‖ ≤ D := by
    have h := hD σ y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (div_pow_le hD0 hr _)
  have w2 : ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ ≤ D / (1 + ‖y‖) ^ 3 := by
    have h := hD σ y 2 (by norm_num)
    rwa [norm_iter_two] at h
  have eH : ‖fderiv ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y‖
      ≤ 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖ :=
    norm_fderiv_trace_le (g := fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x)
      ((hD2.differentiable (by simp)) y)
  have eA : ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x (W σ x)) y‖
      ≤ D * ‖fderiv ℝ (v σ) y‖ + D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ := by
    have h := norm_fderiv_apply_le (N := 2) (hD1.of_le (by norm_cast)) hWs (by norm_num) y
    have a1 : ‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ ≤ D * ‖fderiv ℝ (v σ) y‖ := by
      rw [mul_comm D]; exact mul_le_mul_of_nonneg_left w1 (norm_nonneg _)
    have a2 : ‖fderiv ℝ (fderiv ℝ (v σ)) y‖ * ‖W σ y‖ ≤ D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ := by
      rw [mul_comm D]; exact mul_le_mul_of_nonneg_left w0 (norm_nonneg _)
    exact h.trans (add_le_add a1 a2)
  have eB : ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x (v σ x)) y‖
      ≤ D * ‖fderiv ℝ (v σ) y‖ + D * (‖v σ y‖ / (1 + ‖y‖)) := by
    have h := norm_fderiv_apply_le (N := 1) hWD (hvs.of_le (by norm_cast)) le_rfl y
    have a1 : ‖fderiv ℝ (W σ) y‖ * ‖fderiv ℝ (v σ) y‖ ≤ D * ‖fderiv ℝ (v σ) y‖ :=
      mul_le_mul_of_nonneg_right w1 (norm_nonneg _)
    have a2 : ‖fderiv ℝ (fderiv ℝ (W σ)) y‖ * ‖v σ y‖ ≤ D * (‖v σ y‖ / (1 + ‖y‖)) :=
      (mul_le_mul_of_nonneg_right w2 (norm_nonneg _)).trans
        (div_pow_le_div hD0 (norm_nonneg _) hr (by norm_num))
    exact h.trans (add_le_add a1 a2)
  have e : smoothRight P W v σ = fun x => transportPart P v σ x - secondDerivTrace (secondDerivField v σ x)
      + fderiv ℝ (v σ) x (W σ x) + fderiv ℝ (W σ) x (v σ x) := rfl
  have dTH : DifferentiableAt ℝ (fun x => transportPart P v σ x - secondDerivTrace (secondDerivField v σ x)) y :=
    dT.sub dH
  have dTHA : DifferentiableAt ℝ (fun x => transportPart P v σ x - secondDerivTrace (secondDerivField v σ x)
      + fderiv ℝ (v σ) x (W σ x)) y := dTH.add dA
  rw [e, fderiv_fun_add dTHA dB, fderiv_fun_add dTH dA, fderiv_fun_sub dT dH]
  calc ‖fderiv ℝ (transportPart P v σ) y - fderiv ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y
        + fderiv ℝ (fun x => fderiv ℝ (v σ) x (W σ x)) y + fderiv ℝ (fun x => fderiv ℝ (W σ) x (v σ x)) y‖
      ≤ ‖fderiv ℝ (transportPart P v σ) y‖ + ‖fderiv ℝ (fun x => secondDerivTrace (secondDerivField v σ x)) y‖
        + ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x (W σ x)) y‖
        + ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x (v σ x)) y‖ := by
        exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

theorem smoothRight_fderiv_sq {P : ℝ} {W v : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (_hWp : IsTimePeriodic W)
    (hWd : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) :
    periodLIntegral (fun σ y => matSq (fderiv ℝ (smoothRight P W v σ) y)) < ⊤ := by
  obtain ⟨D, hD⟩ := hWd
  have hc : Continuous (fun z : ℝ × Space => ‖fderiv ℝ (smoothRight P W v z.1) z.2‖) :=
    (PairingSplitInternal.contDiff_slice (V := smoothRight P W v) (n := 0)
      (smoothRight_contDiff' hW hv) (by norm_num)).continuous.norm
  have hg := (((memLp_transport_deriv hv).add ((memLp_deriv_three hv).const_mul 3)).add
    (((memLp_deriv_one hv).const_mul D).add ((memLp_deriv_two hv).const_mul D))).add
    (((memLp_deriv_one hv).const_mul D).add ((memLp_weighted hv).const_mul D))
  have hm := memLp_of_bound (h := fun σ y => ‖fderiv ℝ (smoothRight P W v σ) y‖)
    (g := fun σ y => ‖fderiv ℝ (transportPart P v σ) y‖
      + 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖
      + (D * ‖fderiv ℝ (v σ) y‖ + D * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖)
      + (D * ‖fderiv ℝ (v σ) y‖ + D * (‖v σ y‖ / (1 + ‖y‖)))) hc hg
    (fun σ y => by rw [abs_norm]; exact smoothRight_fderiv_norm_le P hW hD hv σ y)
  exact SmoothWeightSplit.periodLIntegral_lt_top_of_le (by norm_num : (0 : ℝ) ≤ 3)
    (fun σ y => SmoothWeightSplit.matSq_le_three_sq _) (lt_top_of_memLp_real hm)


theorem divergence_negSsp {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hdiv : ∀ x, divergenceAt f x = 0)
    (y : Space) : divergenceAt (fun x => -secondDerivTrace (fderiv ℝ (fun x' => fderiv ℝ f x') x)) y = 0 := by
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_rfl)
  have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hD1.fderiv_right (by exact_mod_cast le_rfl)
  have dD1 : Differentiable ℝ (fderiv ℝ f) := hD1.differentiable (by simp)
  have dD2 : Differentiable ℝ (fderiv ℝ (fderiv ℝ f)) := hD2.differentiable (by simp)
  have s12 : ∀ a b c : Space, fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a b c
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y b a c := by
    intro a b c
    have hs := ((contDiff_infty.1 hD1 2).contDiffAt (x := y)).isSymmSndFDerivAt (by simp)
    rw [hs a b]
  have s23 : ∀ a b c : Space, fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a b c
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a c b := by
    intro a b c
    have e : (fun x => fderiv ℝ (fderiv ℝ f) x b c) = fun x => fderiv ℝ (fderiv ℝ f) x c b :=
      funext fun x => ((contDiff_infty.1 hf 2).contDiffAt (x := x)).isSymmSndFDerivAt (by simp) b c
    have l1 := PairingSplitInternal.fderiv_apply_const (dD2.clm_apply (differentiable_const b) y) c a
    have l2 := PairingSplitInternal.fderiv_apply_const (dD2 y) b a
    have l3 := PairingSplitInternal.fderiv_apply_const (dD2.clm_apply (differentiable_const c) y) b a
    have l4 := PairingSplitInternal.fderiv_apply_const (dD2 y) c a
    rw [e] at l1
    rw [l1, l2] at l3
    rw [l3, l4] at *
  have hA : ∀ j : Fin 3, ∀ y', ∑ i : Fin 3,
      (fderiv ℝ (fderiv ℝ f) y' (unitVector j) (unitVector i)) i = 0 :=
    fun j y' => PairingSplitInternal.trace_deriv_zero dD1 (fun x => hdiv x) y' (unitVector j)
  have hB : ∀ j : Fin 3, ∑ i : Fin 3,
      (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y (unitVector j) (unitVector j) (unitVector i)) i = 0 := by
    intro j
    have h := PairingSplitInternal.trace_deriv_zero (g := fun y' => fderiv ℝ (fderiv ℝ f) y' (unitVector j))
      (dD2.clm_apply (differentiable_const _)) (hA j) y (unitVector j)
    rwa [PairingSplitInternal.fderiv_apply_const (dD2 y)] at h
  have hdu : ∀ i : Fin 3, fderiv ℝ (fun x => -secondDerivTrace (fderiv ℝ (fun x' => fderiv ℝ f x') x)) y (unitVector i)
      = -∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y (unitVector i) (unitVector j) (unitVector j) := by
    intro i
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin 3)), DifferentiableAt ℝ
        (fun y => fderiv ℝ (fderiv ℝ f) y (unitVector j) (unitVector j)) y :=
      fun j _ => ((dD2 y).clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
    have e : (fun x => -secondDerivTrace (fderiv ℝ (fun x' => fderiv ℝ f x') x))
        = fun y => -∑ j : Fin 3, fderiv ℝ (fderiv ℝ f) y (unitVector j) (unitVector j) := rfl
    rw [e, fderiv_fun_neg, neg_apply, fderiv_fun_sum hj, sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PairingSplitInternal.fderiv_apply_const (c := fun y => fderiv ℝ (fderiv ℝ f) y (unitVector j))
      ((dD2 y).clm_apply (differentiableAt_const _)), PairingSplitInternal.fderiv_apply_const (dD2 y)]
  have hc : ∀ (a : Fin 3 → Space) (i : Fin 3), (-(∑ j, a j)) i = -∑ j, a j i := by
    intro a i
    rw [← PairingSplitInternal.proj_apply, map_neg, map_sum]
    rfl
  unfold divergenceAt
  simp only [hdu, hc]
  rw [Finset.sum_neg_distrib, Finset.sum_comm, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← hB j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s12 (unitVector i), s23 (unitVector j) (unitVector i)]

theorem integrable_of_far {h : Space → ℝ} (hc : Continuous h) {R : ℝ} (hR : ∀ y, R < ‖y‖ → h y = 0) :
    Integrable h :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall 0 R) fun y hy =>
    hR y (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy))

theorem inner_gradientAt (a : Space) (p : Space → ℝ) (y : Space) :
    inner ℝ a (gradientAt p y) = ∑ i : Fin 3, a i * fderiv ℝ p y (unitVector i) := by
  unfold gradientAt
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, unitVector, EuclideanSpace.inner_single_right]
  simp only [one_mul, RCLike.conj_to_real]
  ring

theorem slice_negSsp_orthogonal {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hdiv : ∀ x, divergenceAt f x = 0)
    {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) {R : ℝ} (hR : ∀ y, R < ‖y‖ → p y = 0) :
    ∫ y, inner ℝ (-secondDerivTrace (fderiv ℝ (fun x' => fderiv ℝ f x') y)) (gradientAt p y) = 0 := by
  set L : Space → Space := fun x => -secondDerivTrace (fderiv ℝ (fun x' => fderiv ℝ f x') x) with hLdef
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_rfl)
  have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hD1.fderiv_right (by exact_mod_cast le_rfl)
  have hL : ContDiff ℝ ∞ L := by
    have e : L = fun x => -traceCLM (fderiv ℝ (fderiv ℝ f) x) := funext fun x => by
      rw [hLdef, traceCLM_apply]
    rw [e]
    exact (traceCLM.contDiff.comp hD2).neg
  have hLi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun x => L x i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hL
  have dL : Differentiable ℝ L := hL.differentiable (by simp)
  have dLi : ∀ i : Fin 3, Differentiable ℝ (fun x => L x i) := fun i => (hLi i).differentiable (by simp)
  have dp : Differentiable ℝ p := hp.differentiable (by simp)
  have cDp : Continuous (fun x => fderiv ℝ p x) := hp.continuous_fderiv (by simp)
  have cDLi : ∀ i : Fin 3, Continuous (fun x => fderiv ℝ (fun x' => L x' i) x) := fun i =>
    (hLi i).continuous_fderiv (by simp)
  have hpR : ∀ y, R < ‖y‖ → fderiv ℝ p y = 0 := fun y hy => PairingSplitInternal.fderiv_eq_zero_far hR hy
  have I1 : ∀ i : Fin 3, Integrable (fun x => L x i * fderiv ℝ p x (unitVector i)) := fun i =>
    integrable_of_far (((hLi i).continuous).mul (cDp.clm_apply continuous_const)) fun y hy => by
      rw [hpR y hy]; simp
  have I2 : ∀ i : Fin 3, Integrable (fun x => fderiv ℝ (fun x' => L x' i) x (unitVector i) * p x) := fun i =>
    integrable_of_far (((cDLi i).clm_apply continuous_const).mul hp.continuous) fun y hy => by
      rw [hR y hy]; simp
  have I3 : ∀ i : Fin 3, Integrable (fun x => L x i * p x) := fun i =>
    integrable_of_far ((hLi i).continuous.mul hp.continuous) fun y hy => by rw [hR y hy]; simp
  have step : ∀ i : Fin 3, ∫ x, L x i * fderiv ℝ p x (unitVector i)
      = -∫ x, fderiv ℝ (fun x' => L x' i) x (unitVector i) * p x := fun i =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (I2 i) (I1 i) (I3 i) (fun x _ => dLi i x)
      (fun x _ => dp x)
  have hdivL : ∀ x, ∑ i : Fin 3, fderiv ℝ (fun x' => L x' i) x (unitVector i) = 0 := fun x => by
    have h := divergence_negSsp hf hdiv x
    unfold divergenceAt at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact PairingSplitInternal.fderiv_component (dL x) i (unitVector i)
  calc ∫ y, inner ℝ (L y) (gradientAt p y) = ∫ y, ∑ i : Fin 3, L y i * fderiv ℝ p y (unitVector i) := by
        congr 1; funext y; exact inner_gradientAt _ _ _
    _ = ∑ i : Fin 3, ∫ y, L y i * fderiv ℝ p y (unitVector i) :=
        integral_finsetSum _ fun i _ => I1 i
    _ = ∑ i : Fin 3, -∫ y, fderiv ℝ (fun x' => L x' i) y (unitVector i) * p y :=
        Finset.sum_congr rfl fun i _ => step i
    _ = -∫ y, ∑ i : Fin 3, fderiv ℝ (fun x' => L x' i) y (unitVector i) * p y := by
        rw [Finset.sum_neg_distrib, integral_finsetSum _ fun i _ => I2 i]
    _ = 0 := by
        have e : (fun y => ∑ i : Fin 3, fderiv ℝ (fun x' => L x' i) y (unitVector i) * p y) = fun _ => 0 :=
          funext fun y => by rw [← Finset.sum_mul, hdivL y, zero_mul]
        rw [e]; simp

theorem negSsp_contDiff {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ 1 (fun z : ℝ × Space => -secondDerivTrace (secondDerivField v z.1 z.2)) :=
  ((secondDerivTrace_contDiff hv.smooth).neg).of_le (by norm_cast)

theorem sq_iter_two_finite {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    periodLIntegral (fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2) < ⊤ := by
  have e : (fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2)
      = fun σ y => ‖iteratedFDeriv ℝ 2 (v σ) y‖ ^ 2 :=
    funext fun σ => funext fun y => by rw [norm_iter_two]
  rw [e]
  exact hv.derivatives_finite 2 (by norm_num)

theorem sq_iter_three_finite {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    periodLIntegral (fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖ ^ 2) < ⊤ := by
  have e : (fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖ ^ 2)
      = fun σ y => ‖iteratedFDeriv ℝ 3 (v σ) y‖ ^ 2 :=
    funext fun σ => funext fun y => by rw [norm_iter_three]
  rw [e]
  exact hv.derivatives_finite 3 (by norm_num)

theorem negSsp_fderiv_sq {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => -secondDerivTrace (secondDerivField v σ x)) y)) < ⊤ := by
  refine SmoothWeightSplit.periodLIntegral_lt_top_of_le (by norm_num : (0 : ℝ) ≤ 27) (fun σ y => ?_)
    (sq_iter_three_finite hv)
  have hvs : ContDiff ℝ ∞ (v σ) := slice_of_joint hv.smooth σ
  have hD1 : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := hvs.fderiv_right (by exact_mod_cast le_rfl)
  have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (v σ))) := hD1.fderiv_right (by exact_mod_cast le_rfl)
  have h1 := SmoothWeightSplit.matSq_le_three_sq (fderiv ℝ (fun x => -secondDerivTrace (secondDerivField v σ x)) y)
  have h2 : ‖fderiv ℝ (fun x => -secondDerivTrace (secondDerivField v σ x)) y‖
      ≤ 3 * ‖fderiv ℝ (fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x) y‖ := by
    rw [fderiv_fun_neg, norm_neg]
    exact norm_fderiv_trace_le (g := fun x => fderiv ℝ (fun x' => fderiv ℝ (v σ) x') x)
      ((hD2.differentiable (by simp)) y)
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith

theorem negSsp_solenoidal_self {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    IsSolenoidalPartOf (fun σ y => -secondDerivTrace (secondDerivField v σ y)) (fun σ y => -secondDerivTrace (secondDerivField v σ y)) := by
  refine ⟨(negSsp_contDiff hv).continuous.aestronglyMeasurable, fun σ y => ?_, ?_, fun q hq => ?_,
    fun _ _ => rfl⟩
  · have ev : v (σ + 1) = v σ := funext fun x => hv.periodic σ x
    simp only [secondDerivField, ev]
  · refine SmoothWeightSplit.periodLIntegral_lt_top_of_le (by norm_num : (0 : ℝ) ≤ 9) (fun σ y => ?_)
      (sq_iter_two_finite hv)
    have h2 : ‖-secondDerivTrace (secondDerivField v σ y)‖ ≤ 3 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ := by
      rw [norm_neg]; exact norm_secondDerivTrace_le _
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith
  · obtain ⟨hqs, -, R, hR⟩ := hq
    have e : ∀ σ, ∫ y, inner ℝ (-secondDerivTrace (secondDerivField v σ y)) (gradientAt (q σ) y) = 0 := fun σ =>
      slice_negSsp_orthogonal (slice_of_joint hv.smooth σ) (fun x => hv.divergence_free σ x)
        (slice_of_joint hqs σ) (fun y hy => hR σ y hy)
    simp only [e, integral_zero]

end Internal.SmoothPairingClass

end Coercive

end Breakdown
