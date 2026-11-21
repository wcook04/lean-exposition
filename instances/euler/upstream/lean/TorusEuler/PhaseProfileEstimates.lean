import TorusEuler.PhaseCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Mixed parameter and phase estimates for Appendix D, equation (D.5). -/

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace TorusEuler

section ParameterIntegration

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiff_parameter_jet {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
    ContDiff ℝ ∞ (fun p : P × ℝ => iteratedFDeriv ℝ k (fun x => f x p.2) p.1) := by
  let ι := ContinuousLinearMap.inl ℝ P ℝ
  let C := ContinuousMultilinearMap.compContinuousLinearMapL (F := E)
    (fun _ : Fin k => ι)
  have h : (fun p : P × ℝ => iteratedFDeriv ℝ k (fun x => f x p.2) p.1) =
      fun p => C (iteratedFDeriv ℝ k (Function.uncurry f) p) := by
    funext p
    rcases p with ⟨x, s⟩
    have hslice : (fun y => f y s) =
        (fun z : P × ℝ => Function.uncurry f (z + (0, s))) ∘ ι := by
      funext y
      simp [ι, Function.uncurry]
    have hshift : ContDiff ℝ ∞ (fun z : P × ℝ => Function.uncurry f (z + (0, s))) :=
      hf.comp (contDiff_id.add contDiff_const)
    rw [hslice, ι.iteratedFDeriv_comp_right hshift x (by simp), iteratedFDeriv_comp_add_right]
    simp [C, ι]
  rw [h]
  exact C.contDiff.comp (hf.iteratedFDeriv_right (by simp))

variable [ProperSpace P]

private theorem hasFDerivAt_phaseInterval {f : P → ℝ → E} {df : P → ℝ → P →L[ℝ] E}
    (hf : Continuous (Function.uncurry f)) (hdf : Continuous (Function.uncurry df))
    (hderiv : ∀ x s, HasFDerivAt (fun y => f y s) (df x s) x)
    (a b : ℝ) (x : P) :
    HasFDerivAt (fun y => ∫ s in a..b, f y s) (∫ s in a..b, df x s) x := by
  have hcont (y : P) : Continuous (f y) := hf.comp (continuous_const.prodMk continuous_id)
  have hdcont : Continuous (df x) := hdf.comp (continuous_const.prodMk continuous_id)
  have hcompact : IsCompact (Metric.closedBall x 1 ×ˢ Set.uIcc a b) :=
    (isCompact_closedBall x 1).prod isCompact_uIcc
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hdf.norm.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => M)
    (Metric.ball_mem_nhds x zero_lt_one) (Eventually.of_forall fun y => (hcont y).aestronglyMeasurable)
    ((hcont x).intervalIntegrable a b) hdcont.aestronglyMeasurable
    (Eventually.of_forall fun s hs y hy => ?_) intervalIntegrable_const
    (Eventually.of_forall fun s _ y _ => hderiv y s)
  have hp : (y, s) ∈ Metric.closedBall x 1 ×ˢ Set.uIcc a b :=
    ⟨Metric.ball_subset_closedBall hy, uIoc_subset_uIcc hs⟩
  exact hM (mem_image_of_mem (fun p : P × ℝ => ‖df p.1 p.2‖) hp)

variable [CompleteSpace E]

/-- A jointly smooth integrand on a fixed compact phase interval has a smooth
parameter integral, with every parameter derivative obtained inside the integral. -/
theorem contDiff_and_iteratedFDeriv_phaseInterval {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ s in a..b, f x s) ∧
    ∀ k (x : P), iteratedFDeriv ℝ k (fun y => ∫ s in a..b, f y s) x =
      ∫ s in a..b, iteratedFDeriv ℝ k (fun y => f y s) x := by
  let D (k : ℕ) (x : P) (s : ℝ) := iteratedFDeriv ℝ k (fun y => f y s) x
  let J (x : P) : FormalMultilinearSeries ℝ P E := fun k => ∫ s in a..b, D k x s
  have hD (k : ℕ) : ContDiff ℝ ∞ (Function.uncurry (D k)) := contDiff_parameter_jet hf k
  have hjoint (k : ℕ) (x : P) :
      HasFDerivAt (fun y => J y k) ((J x (k + 1)).curryLeft) x := by
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) E
    have hC : Continuous (Function.uncurry (fun y s => C (D (k + 1) y s))) :=
      C.continuous.comp (hD (k + 1)).continuous
    have hderiv (y : P) (s : ℝ) : HasFDerivAt (fun z => D k z s) (C (D (k + 1) y s)) y := by
      have hDs : ContDiff ℝ ∞ (fun z => D k z s) :=
        (hD k).comp (contDiff_id.prodMk contDiff_const)
      have h := (hDs.differentiable (by simp) y).hasFDerivAt
      rwa [show fderiv ℝ (fun z => D k z s) y = C (D (k + 1) y s) from
        congrFun fderiv_iteratedFDeriv y] at h
    have h := hasFDerivAt_phaseInterval (hD k).continuous hC hderiv a b x
    have hcomm := LinearIsometry.intervalIntegral_comp_comm (𝕜 := ℝ) (μ := volume)
      (a := a) (b := b) (E := P [×(k + 1)]→L[ℝ] E) (F := P →L[ℝ] (P [×k]→L[ℝ] E))
      C.toLinearIsometry (fun s => D (k + 1) x s)
    change (∫ s in a..b, C (D (k + 1) x s)) = C (∫ s in a..b, D (k + 1) x s) at hcomm
    rw [hcomm] at h
    exact h
  have hzero (x : P) : (J x 0).curry0 = ∫ s in a..b, f x s := by
    let C := continuousMultilinearCurryFin0 ℝ P E
    change C (∫ s in a..b, D 0 x s) = _
    have hcomm := LinearIsometry.intervalIntegral_comp_comm (𝕜 := ℝ) (μ := volume)
      (a := a) (b := b) (E := P [×0]→L[ℝ] E) (F := E) C.toLinearIsometry (fun s => D 0 x s)
    change (∫ s in a..b, C (D 0 x s)) = C (∫ s in a..b, D 0 x s) at hcomm
    rw [← hcomm]
    simp [C, D, iteratedFDeriv_zero_apply]
  have hJ : HasFTaylorSeriesUpToOn ∞ (fun x => ∫ s in a..b, f x s) J univ :=
    ⟨fun x _ => hzero x, fun k _ x _ => (hjoint k x).hasFDerivWithinAt,
      fun k _ => (continuous_iff_continuousAt.2 fun x => (hjoint k x).continuousAt).continuousOn⟩
  refine ⟨contDiffOn_univ.mp hJ.contDiffOn, fun k x => ?_⟩
  rw [← iteratedFDerivWithin_univ]
  exact (hJ.eq_iteratedFDerivWithin_of_uniqueDiffOn (by simp) uniqueDiffOn_univ (mem_univ x)).symm

private theorem contDiff_phaseAnchoredPrimitive {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun p : P × ℝ => ∫ σ in (0 : ℝ)..p.2, f p.1 σ) := by
  have hrescale : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ => f p.1.1 (p.1.2 * p.2)) :=
    hf.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))
  have h := contDiff_snd.smul
    (contDiff_and_iteratedFDeriv_phaseInterval (f := fun (p : P × ℝ) σ => f p.1 (p.2 * σ))
      hrescale 0 1).1
  have heq : (fun p : P × ℝ => ∫ σ in (0 : ℝ)..p.2, f p.1 σ) =
      fun p => p.2 • ∫ σ in (0 : ℝ)..1, f p.1 (p.2 * σ) := by
    funext p
    symm
    simpa only [mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (f p.1) p.2
  rw [heq]
  exact h

/-- Parameter derivatives commute with the phase average. -/
theorem iteratedFDeriv_phaseMean {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) (x : P) :
    iteratedFDeriv ℝ k (fun y => phaseMean (f y)) x =
      phaseMean (fun s => iteratedFDeriv ℝ k (fun y => f y s) x) :=
  (contDiff_and_iteratedFDeriv_phaseInterval hf 0 1).2 k x

/-- Parameter derivatives commute with subtraction of the phase average. -/
theorem iteratedFDeriv_phaseOscillation {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) (x : P) (s : ℝ) :
    iteratedFDeriv ℝ k (fun y => phaseOscillation (f y) s) x =
      phaseOscillation (fun σ => iteratedFDeriv ℝ k (fun y => f y σ) x) s := by
  have hs : ContDiff ℝ ∞ (fun y => f y s) := hf.comp (contDiff_id.prodMk contDiff_const)
  have hm : ContDiff ℝ ∞ (fun y => phaseMean (f y)) :=
    (contDiff_and_iteratedFDeriv_phaseInterval hf 0 1).1
  unfold phaseOscillation
  change iteratedFDeriv ℝ k ((fun y => f y s) - (fun y => phaseMean (f y))) x = _
  rw [iteratedFDeriv_sub_apply (hs.contDiffAt.of_le (by simp))
    (hm.contDiffAt.of_le (by simp)), iteratedFDeriv_phaseMean hf]

/-- Parameter derivatives commute with the phase primitive, including its
normalization by subtraction of the phase mean. -/
theorem iteratedFDeriv_phasePrimitive {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) (x : P) (s : ℝ) :
    iteratedFDeriv ℝ k (fun y => phasePrimitive (f y) s) x =
      phasePrimitive (fun σ => iteratedFDeriv ℝ k (fun y => f y σ) x) s := by
  let g (y : P) (σ : ℝ) := ∫ z in (0 : ℝ)..σ, f y z
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := contDiff_phaseAnchoredPrimitive hf
  change iteratedFDeriv ℝ k (fun y => phaseOscillation (g y) s) x = _
  rw [iteratedFDeriv_phaseOscillation hg]
  congr 1
  funext σ
  exact (contDiff_and_iteratedFDeriv_phaseInterval hf 0 σ).2 k x

end ParameterIntegration

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every phase derivative of a periodic profile has the same period. -/
theorem periodic_iteratedDeriv_phase {f : ℝ → E} {τ : ℝ}
    (hper : Function.Periodic f τ) (j : ℕ) :
    Function.Periodic (iteratedDeriv j f) τ := by
  have hshift : (fun s => f (s + τ)) = f := funext hper
  intro s
  have h := congrFun (iteratedDeriv_comp_add_const j f τ) s
  rw [hshift] at h
  exact h.symm

variable [CompleteSpace E]

theorem phaseMean_iteratedDeriv_succ {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) (j : ℕ) :
    phaseMean (iteratedDeriv (j + 1) f) = 0 := by
  apply phaseMean_deriv
    (f := iteratedDeriv j f) (hper := periodic_iteratedDeriv_phase hper j)
  · intro s
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv j (mod_cast ENat.natCast_lt_top j) s).hasDerivAt
  · exact hf.continuous_iteratedDeriv (j + 1) (by simp)

/-- Viewing the phase average as a constant phase field, it commutes with all phase derivatives. -/
theorem iteratedDeriv_phaseMean_const {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) (j : ℕ) (s : ℝ) :
    iteratedDeriv j (fun _ : ℝ => phaseMean f) s = phaseMean (iteratedDeriv j f) := by
  cases j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j =>
    rw [phaseMean_iteratedDeriv_succ hf hper j]
    simp only [iteratedDeriv_const, Nat.succ_ne_zero, ite_false]

/-- Removing the phase average commutes with all phase derivatives. -/
theorem iteratedDeriv_phaseOscillation_eq {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) (j : ℕ) :
    iteratedDeriv j (phaseOscillation f) = phaseOscillation (iteratedDeriv j f) := by
  cases j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j =>
    have hd : deriv (phaseOscillation f) = deriv f := by
      funext s
      exact ((hf.differentiable (by simp) s).hasDerivAt.sub_const _).deriv
    rw [iteratedDeriv_succ', hd, ← iteratedDeriv_succ']
    funext s
    rw [phaseOscillation, phaseMean_iteratedDeriv_succ hf hper j, sub_zero]

/-- The normalized periodic primitive commutes with every phase derivative on mean-zero profiles. -/
theorem iteratedDeriv_phasePrimitive_eq {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) (hmean : phaseMean f = 0) (j : ℕ) :
    iteratedDeriv j (phasePrimitive f) = phasePrimitive (iteratedDeriv j f) := by
  cases j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j =>
    have hder : deriv (phasePrimitive f) = f :=
      funext fun s => (hasDerivAt_phasePrimitive hf.continuous s).deriv
    have hjder (s : ℝ) : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f s) s := by
      rw [iteratedDeriv_succ]
      exact (hf.differentiable_iteratedDeriv j (mod_cast ENat.natCast_lt_top j) s).hasDerivAt
    have hjmean : phaseMean (iteratedDeriv j f) = 0 := by
      cases j with
      | zero => simpa only [iteratedDeriv_zero] using hmean
      | succ k => exact phaseMean_iteratedDeriv_succ hf hper k
    rw [iteratedDeriv_succ', hder, phasePrimitive_deriv hjder
      (hf.continuous_iteratedDeriv (j + 1) (by simp))]
    funext s
    rw [phaseOscillation, hjmean, sub_zero]

end

section MixedJets

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [ProperSpace P] [CompleteSpace E] in
private theorem contDiff_phaseDerivative {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun p : P × ℝ => deriv (f p.1) p.2) := by
  have h (p : P × ℝ) : deriv (f p.1) p.2 = fderiv ℝ (Function.uncurry f) p (0, 1) := by
    have hd := (hf.differentiable (by simp) p).hasFDerivAt.comp p.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
    exact hd.hasDerivAt.deriv
  rw [funext h]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

omit [ProperSpace P] [CompleteSpace E] in
private theorem contDiff_iteratedPhaseDerivative {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : P × ℝ => iteratedDeriv j (f p.1) p.2) := by
  induction j with
  | zero =>
    have h : Function.uncurry f = (fun p : P × ℝ => f p.1 p.2) := by
      funext p
      rcases p with ⟨x, s⟩
      rfl
    simpa only [iteratedDeriv_zero, h] using hf
  | succ j hj =>
    simpa only [iteratedDeriv_succ] using
      contDiff_phaseDerivative (f := fun x => iteratedDeriv j (f x)) hj

/-- Taking the phase derivative first and the parameter derivative second.
The parameter is the label in (D.1), with time held fixed. -/
noncomputable def mixedPhaseJet (f : P → ℝ → E) (k j : ℕ) (x : P) (s : ℝ) :
    P [×k]→L[ℝ] E :=
  iteratedFDeriv ℝ k (fun y => iteratedDeriv j (f y) s) x

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem phaseMean_map (L : E →L[ℝ] F) {g : ℝ → E} (hg : Continuous g) :
    phaseMean (L ∘ g) = L (phaseMean g) :=
  L.intervalIntegral_comp_comm (hg.intervalIntegrable 0 1)

private theorem phaseOscillation_map (L : E →L[ℝ] F) {g : ℝ → E} (hg : Continuous g) (s : ℝ) :
    phaseOscillation (L ∘ g) s = L (phaseOscillation g s) := by
  rw [phaseOscillation, phaseOscillation, L.map_sub, phaseMean_map L hg]
  rfl

private theorem phasePrimitive_map (L : E →L[ℝ] F) {g : ℝ → E} (hg : Continuous g) (s : ℝ) :
    phasePrimitive (L ∘ g) s = L (phasePrimitive g s) := by
  have h : (fun r => ∫ σ in (0 : ℝ)..r, L (g σ)) =
      L ∘ (fun r => ∫ σ in (0 : ℝ)..r, g σ) := by
    funext r
    exact L.intervalIntegral_comp_comm (hg.intervalIntegrable 0 r)
  simpa only [phasePrimitive, Function.comp_def, h] using
    phaseOscillation_map L (intervalIntegral.differentiable_integral_of_continuous hg).continuous s

/-- The constants in (D.5) apply to any fixed linear evaluation of a mixed
jet, including a weighted directional or coordinate derivative. The primitive
estimate requires zero phase mean at every label. -/
theorem norm_map_mixedPhaseJet_phaseOps_le {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hper : ∀ y, Function.Periodic (f y) 1)
    (k j : ℕ) (x : P) (s : ℝ) (L : (P [×k]→L[ℝ] E) →L[ℝ] F) {M : ℝ}
    (hM : ∀ σ, ‖L (mixedPhaseJet f k j x σ)‖ ≤ M) :
    ‖L (mixedPhaseJet (fun y _ => phaseMean (f y)) k j x s)‖ ≤ M ∧
    ‖L (mixedPhaseJet (fun y => phaseOscillation (f y)) k j x s)‖ ≤ 2 * M ∧
    ((∀ y, phaseMean (f y) = 0) →
      ‖L (mixedPhaseJet (fun y => phasePrimitive (f y)) k j x s)‖ ≤ 2 * M) := by
  let Dj (y : P) := iteratedDeriv j (f y)
  let J := fun σ => mixedPhaseJet f k j x σ
  have hDj : ContDiff ℝ ∞ (Function.uncurry Dj) := contDiff_iteratedPhaseDerivative hf j
  have hfS (y : P) : ContDiff ℝ ∞ (f y) := hf.comp (contDiff_const.prodMk contDiff_id)
  have hJcont : Continuous J :=
    (contDiff_parameter_jet hDj k).continuous.comp (continuous_const.prodMk continuous_id)
  have hJper : Function.Periodic J 1 := by
    intro σ
    have hshift : (fun y => Dj y (σ + 1)) = (fun y => Dj y σ) :=
      funext fun y => periodic_iteratedDeriv_phase (hper y) j σ
    exact congrArg (fun g : P → E => iteratedFDeriv ℝ k g x) hshift
  have hmean : mixedPhaseJet (fun y _ => phaseMean (f y)) k j x s = phaseMean J := by
    unfold mixedPhaseJet
    simp_rw [iteratedDeriv_phaseMean_const (hfS _) (hper _)]
    exact iteratedFDeriv_phaseMean hDj k x
  have hosc : mixedPhaseJet (fun y => phaseOscillation (f y)) k j x s = phaseOscillation J s := by
    unfold mixedPhaseJet
    simp_rw [iteratedDeriv_phaseOscillation_eq (hfS _) (hper _)]
    exact iteratedFDeriv_phaseOscillation hDj k x s
  refine ⟨?_, ?_, fun hzero => ?_⟩
  · rw [hmean, ← phaseMean_map L hJcont]
    exact norm_phaseMean_le (fun σ _ => hM σ)
  · rw [hosc, ← phaseOscillation_map L hJcont]
    exact norm_phaseOscillation_le hM s
  · have hprim : mixedPhaseJet (fun y => phasePrimitive (f y)) k j x s = phasePrimitive J s := by
      unfold mixedPhaseJet
      simp_rw [iteratedDeriv_phasePrimitive_eq (hfS _) (hper _) (hzero _)]
      exact iteratedFDeriv_phasePrimitive hDj k x s
    have hDjZero : (fun y => phaseMean (Dj y)) = (fun _ => (0 : E)) := by
      funext y
      cases j with
      | zero => simpa only [Dj, iteratedDeriv_zero] using hzero y
      | succ n => exact phaseMean_iteratedDeriv_succ (hfS y) (hper y) n
    have hJzero : phaseMean J = 0 := by
      change phaseMean (fun σ => iteratedFDeriv ℝ k (fun y => Dj y σ) x) = 0
      rw [← iteratedFDeriv_phaseMean hDj k x, hDjZero, iteratedFDeriv_fun_zero, Pi.zero_apply]
    have hLJzero : phaseMean (L ∘ J) = 0 := by
      rw [phaseMean_map L hJcont, hJzero, map_zero]
    rw [hprim, ← phasePrimitive_map L hJcont]
    exact norm_phasePrimitive_le (L.continuous.comp hJcont) (fun σ => congrArg L (hJper σ))
      hLJzero (fun σ _ => hM σ) s

/-- Each weighted coordinate term of the finite norm in (D.1) obeys the
phase-operator estimates (D.5). Use fixed label basis directions for `v`.
The weight can include the factor `1 / γ t` since time is held fixed. -/
theorem norm_apply_mixedPhaseJet_phaseOps_le {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (hper : ∀ y, Function.Periodic (f y) 1)
    (k j : ℕ) (x : P) (s w : ℝ) (v : Fin k → P) {M : ℝ}
    (hM : ∀ σ, ‖w • (mixedPhaseJet f k j x σ) v‖ ≤ M) :
    ‖w • (mixedPhaseJet (fun y _ => phaseMean (f y)) k j x s) v‖ ≤ M ∧
    ‖w • (mixedPhaseJet (fun y => phaseOscillation (f y)) k j x s) v‖ ≤ 2 * M ∧
    ((∀ y, phaseMean (f y) = 0) →
      ‖w • (mixedPhaseJet (fun y => phasePrimitive (f y)) k j x s) v‖ ≤ 2 * M) :=
  norm_map_mixedPhaseJet_phaseOps_le hf hper k j x s
    (w • ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P) E v) hM

end MixedJets

end TorusEuler
