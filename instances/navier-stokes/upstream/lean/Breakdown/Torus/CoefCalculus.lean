import Breakdown.Torus.StatementsCoeff

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace CoefCalculus.Internal

theorem toLp_insertNth_one (i : Fin 3) (y : Fin 2 → ℝ) :
    WithLp.toLp 2 (Fin.insertNth i (1 : ℝ) y) =
      WithLp.toLp 2 (Fin.insertNth i (0 : ℝ) y) + unitVector i := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨m, rfl⟩
  · simp [unitVector]
  · simp [unitVector, Fin.succAbove_ne]

theorem cell_eq_preimage : cell = (WithLp.ofLp : Space → Fin 3 → ℝ) ⁻¹' Icc 0 1 := by
  ext x
  simp [cell, Pi.le_def, forall_and]

theorem integral_cell_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (i : Fin 3) (F : Space → E) (F' : Space → Space →L[ℝ] E)
    (hF : ∀ x, HasFDerivAt F (F' x) x) (hc : Continuous fun x => F' x (unitVector i))
    (hp : ∀ x, F (x + unitVector i) = F x) :
    ∫ x in cell, F' x (unitVector i) = 0 := by
  set L : (Fin 3 → ℝ) →L[ℝ] Space :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap with hL
  have hSspp : ∀ y, L y = WithLp.toLp 2 y := fun y => rfl
  set G : (Fin 3 → ℝ) → E := fun y => F (WithLp.toLp 2 y) with hG
  set G' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] E := fun y => (F' (WithLp.toLp 2 y)).comp L with hG'
  have hGd : ∀ y, HasFDerivAt G (G' y) y := by
    intro y
    have := (hF (L y)).comp y L.hasFDerivAt
    exact this
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun y => (hGd y).continuousAt
  let f : Fin 3 → (Fin 3 → ℝ) → E := fun j => if j = i then G else fun _ => 0
  let f' : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] E := fun j y => if j = i then G' y else 0
  have hsum : ∀ y, ∑ j, f' j y (Pi.single j 1) = F' (WithLp.toLp 2 y) (unitVector i) := by
    intro y
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [f', hj]) (by simp)]
    simp only [f', G', if_true, ContinuousLinearMap.comp_apply, hSspp]
    rfl
  have key := integral_divergence_of_hasFDerivAt_off_countable' (0 : Fin 3 → ℝ) 1
    (fun j => by simp) f f' ∅ countable_empty
    (fun j => by
      by_cases h : j = i
      · simp only [f, h, if_true]; exact hGc.continuousOn
      · simp only [f, h, if_false]; exact continuousOn_const)
    (fun y _ j => by
      by_cases h : j = i
      · simp only [f, f', h, if_true]; exact hGd y
      · simp only [f, f', h, if_false]; exact hasFDerivAt_const _ _)
    (by
      simp_rw [hsum]
      exact ((hc.comp (PiLp.continuous_toLp 2 _)).continuousOn).integrableOn_compact isCompact_Icc)
  have hrhs : ∀ j, ((∫ x in Icc ((0 : Fin 3 → ℝ) ∘ j.succAbove) ((1 : Fin 3 → ℝ) ∘ j.succAbove),
      f j (Fin.insertNth j ((1 : Fin 3 → ℝ) j) x)) -
      ∫ x in Icc ((0 : Fin 3 → ℝ) ∘ j.succAbove) ((1 : Fin 3 → ℝ) ∘ j.succAbove),
      f j (Fin.insertNth j ((0 : Fin 3 → ℝ) j) x)) = 0 := by
    intro j
    by_cases h : j = i
    · subst h
      simp only [f, if_true, G, Pi.one_apply, Pi.zero_apply, toLp_insertNth_one, hp, sub_self]
    · simp [f, h]
  simp_rw [hsum, hrhs, Finset.sum_const_zero] at key
  rw [cell_eq_preimage]
  have hpre := (PiLp.volume_preserving_ofLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
    (fun y => F' (WithLp.toLp 2 y) (unitVector i)) (Icc 0 1)
  simpa using hpre.trans key

theorem isCompact_cell : IsCompact cell := by
  rw [cell_eq_preimage]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph.isCompact_preimage.2
    isCompact_Icc

theorem freq_apply (k : Lattice) (j : Fin 3) : freq k j = k j := by
  simp [freq, unitVector, WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]

theorem inner_freq_unitVector (k : Lattice) (i : Fin 3) :
    inner ℝ (freq k) (unitVector i) = k i := by
  simp [unitVector, EuclideanSpace.inner_single_right, freq_apply]

def charL (k : Lattice) : Space →L[ℝ] ℂ :=
  (-(2 * π * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ (freq k)))

theorem character_eq (k : Lattice) : character k = fun x => Complex.exp (charL k x) := by
  funext x
  simp [character, charL]

theorem hasFDerivAt_character (k : Lattice) (x : Space) :
    HasFDerivAt (character k) (character k x • charL k) x := by
  rw [character_eq]
  exact (charL k).hasFDerivAt.cexp

theorem continuous_character (k : Lattice) : Continuous (character k) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_character k x).continuousAt

theorem charL_unitVector (k : Lattice) (i : Fin 3) :
    charL k (unitVector i) = -(2 * π * Complex.I * (k i : ℂ)) := by
  simp [charL, inner_freq_unitVector]

theorem character_add_unitVector (k : Lattice) (i : Fin 3) (x : Space) :
    character k (x + unitVector i) = character k x := by
  rw [character, character, inner_add_right, inner_freq_unitVector]
  have : -(2 * π * Complex.I * (((inner ℝ (freq k) x + (k i : ℝ) : ℝ)) : ℂ)) =
      -(2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)) +
        ((-k i : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem integral_character_smul_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (i : Fin 3) (k : Lattice) (h : Space → E) (h' : Space → Space →L[ℝ] E)
    (hd : ∀ x, HasFDerivAt h (h' x) x) (hc : Continuous fun x => h' x (unitVector i))
    (hp : ∀ x, h (x + unitVector i) = h x) :
    ∫ x in cell, character k x • h' x (unitVector i) =
      (2 * π * Complex.I * (k i : ℂ)) • ∫ x in cell, character k x • h x := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hD : ∀ x, HasFDerivAt (fun y => character k y • h y)
      (character k x • h' x + (character k x • charL k).smulRight (h x)) x :=
    fun x => (hasFDerivAt_character k x).smul (hd x)
  have heval : ∀ x, (character k x • h' x + (character k x • charL k).smulRight (h x))
      (unitVector i) = character k x • h' x (unitVector i) +
        (-(2 * π * Complex.I * (k i : ℂ))) • (character k x • h x) := by
    intro x
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, charL_unitVector, smul_eq_mul, smul_smul]
    rw [mul_comm (character k x)]
  have ha : IntegrableOn (fun x => character k x • h' x (unitVector i)) cell :=
    ((continuous_character k).smul hc).continuousOn.integrableOn_compact isCompact_cell
  have hb : IntegrableOn (fun x => (-(2 * π * Complex.I * (k i : ℂ))) • (character k x • h x))
      cell :=
    (continuous_const.smul ((continuous_character k).smul hhc)).continuousOn.integrableOn_compact
      isCompact_cell
  have hc1 : Continuous fun x => character k x • h' x (unitVector i) :=
    (continuous_character k).smul hc
  have hc2 : Continuous fun x => (-(2 * π * Complex.I * (k i : ℂ))) • (character k x • h x) :=
    continuous_const.smul ((continuous_character k).smul hhc)
  have hc3 : Continuous fun x =>
      (character k x • h' x + (character k x • charL k).smulRight (h x)) (unitVector i) := by
    simp_rw [heval]
    exact hc1.add hc2
  have h0 := integral_cell_eq_zero i _ _ hD hc3
    (fun x => by simp only [character_add_unitVector, hp])
  simp_rw [heval] at h0
  rw [integral_add ha hb, integral_smul] at h0
  rw [eq_neg_of_add_eq_zero_left h0, neg_smul, neg_neg]

def complexifyL : Space →L[ℝ] Coef :=
  LinearMap.toContinuousLinearMap
    { toFun := complexify
      map_add' := fun x y => by ext j; simp [complexify]
      map_smul' := fun r x => by ext j; simp [complexify] }

theorem complexifyL_apply (x : Space) : complexifyL x = complexify x := rfl

theorem freqTrCoef_sum (φ : Fin 3 → Space → Space) (hφ : ∀ j, Continuous (φ j)) (k : Lattice) :
    freqTrCoef (fun x => ∑ j, φ j x) k = ∑ j, freqTrCoef (φ j) k := by
  unfold freqTrCoef
  have : ∀ x, character k x • complexify (∑ j, φ j x) =
      ∑ j, character k x • complexify (φ j x) := by
    intro x
    rw [← complexifyL_apply, map_sum, Finset.smul_sum]
    rfl
  simp_rw [this]
  exact integral_finsetSum _ fun j _ =>
    ((continuous_character k).smul (complexifyL.continuous.comp (hφ j))).continuousOn.integrableOn_compact
      isCompact_cell

end CoefCalculus.Internal

open CoefCalculus.Internal

theorem coefDeriv : CoefDeriv := by
  intro f hf hp i k
  have hfd := hf.differentiable one_ne_zero
  have hfc := hf.continuous_fderiv one_ne_zero
  exact integral_character_smul_deriv i k (fun x => complexify (f x))
    (fun x => complexifyL.comp (fderiv ℝ f x))
    (fun x => complexifyL.hasFDerivAt.comp x (hfd x).hasFDerivAt)
    (complexifyL.continuous.comp (hfc.clm_apply continuous_const)) (fun x => by simp only [hp i x])

theorem coefSumSecondPartials : CoefSumSecondPartials := by
  intro f hf hp k
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg : ∀ j, ContDiff ℝ 1 (fun y => fderiv ℝ f y (unitVector j)) :=
    fun j => h1.clm_apply contDiff_const
  have hgp : ∀ j, IsPeriodic (fun y => fderiv ℝ f y (unitVector j)) := by
    intro j i x
    have : (fun y => f (y + unitVector i)) = f := funext (hp i)
    simp only
    rw [← fderiv_comp_add_right (unitVector i), this]
  have hssp : sumSecondPartialsAt f =
      fun x => ∑ j, fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector j) := by
    funext x
    unfold sumSecondPartialsAt
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedFDeriv_two_apply,
      fderiv_clm_apply ((h1.differentiable one_ne_zero) x) (differentiableAt_const _)]
    simp
  have hcont : ∀ j, Continuous fun x =>
      fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector j) :=
    fun j => ((hg j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [hssp, freqTrCoef_sum _ hcont]
  simp_rw [coefDeriv _ (hg _) (hgp _), coefDeriv f (hf.of_le (by norm_num)) hp, smul_smul]
  rw [← Finset.sum_smul, ← Complex.coe_smul]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [freq_apply]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem coefGradient : CoefGradient := by
  intro g hg hp k
  have hgd := hg.differentiable one_ne_zero
  have hgc := hg.continuous_fderiv one_ne_zero
  have hscal : ∀ j, ∫ x in cell, character k x * ((fderiv ℝ g x (unitVector j) : ℝ) : ℂ) =
      2 * π * Complex.I * (k j : ℂ) * scalarCoef g k := by
    intro j
    have := integral_character_smul_deriv j k (fun x => ((g x : ℝ) : ℂ))
      (fun x => Complex.ofRealCLM.comp (fderiv ℝ g x))
      (fun x => Complex.ofRealCLM.hasFDerivAt.comp x (hgd x).hasFDerivAt)
      (Complex.continuous_ofReal.comp (hgc.clm_apply continuous_const)) (fun x => by simp only [hp j x])
    simpa [scalarCoef] using this
  have hcx : ∀ x, character k x • complexify (gradientAt g x) =
      ∑ j, (character k x * ((fderiv ℝ g x (unitVector j) : ℝ) : ℂ)) • complexify (unitVector j) := by
    intro x
    rw [gradientAt, ← complexifyL_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, ← Complex.coe_smul, smul_smul, complexifyL_apply]
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun x =>
      (character k x * ((fderiv ℝ g x (unitVector j) : ℝ) : ℂ)) • complexify (unitVector j))
      (volume.restrict cell) := fun j _ =>
    (((continuous_character k).mul (Complex.continuous_ofReal.comp
      (hgc.clm_apply continuous_const))).smul continuous_const).continuousOn.integrableOn_compact
        isCompact_cell
  unfold freqTrCoef
  simp_rw [hcx]
  rw [integral_finsetSum _ hint]
  simp_rw [integral_smul_const, hscal]
  ext m
  simp [complexify, unitVector, latVec, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

end Breakdown.Periodic
