import Breakdown.FracCell.MeshFarPoly

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly MeshFarPolyInternal

namespace MeshFarCoefEnergyInternal

theorem rect_finite (K : CellBox) : IsFiniteMeasure (volume.restrict K.rect) :=
  isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

def basisFn (B : CellBases) (k : ℕ × ℕ) (p : ℝ × ℝ) : ℂ := ((B.radialPoly k.1 p.1 * B.heightPoly k.2 p.2 : ℝ) : ℂ)

theorem basisFn_continuous (B : CellBases) (k : ℕ × ℕ) : Continuous (basisFn B k) := by
  have h1 := radialPoly_continuous B k.1
  have h2 := heightPoly_continuous B k.2
  unfold basisFn
  fun_prop

theorem basis_orth (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (k k' : ℕ × ℕ) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * basisFn B k p * basisFn B k' p = if k = k' then 1 else 0 := by
  have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * basisFn B k p * basisFn B k' p =
      ((K.lineWeight p.1 * B.radialPoly k.1 p.1 * B.radialPoly k'.1 p.1 : ℝ) : ℂ)
        * ((B.heightPoly k.2 p.2 * B.heightPoly k'.2 p.2 : ℝ) : ℂ) := by
    intro p
    unfold basisFn
    push_cast
    ring
  simp_rw [e]
  have hprod : ∫ p in K.rect, ((K.lineWeight p.1 * B.radialPoly k.1 p.1 * B.radialPoly k'.1 p.1 : ℝ) : ℂ)
        * ((B.heightPoly k.2 p.2 * B.heightPoly k'.2 p.2 : ℝ) : ℂ)
      = (∫ r in Set.Icc K.r₁ K.r₂, ((K.lineWeight r * B.radialPoly k.1 r * B.radialPoly k'.1 r : ℝ) : ℂ))
        * ∫ z in Set.Icc K.z₁ K.z₂, ((B.heightPoly k.2 z * B.heightPoly k'.2 z : ℝ) : ℂ) := by
    unfold CellBox.rect
    rw [Measure.volume_eq_prod]
    exact setIntegral_prod_mul (fun r => ((K.lineWeight r * B.radialPoly k.1 r * B.radialPoly k'.1 r : ℝ) : ℂ))
      (fun z => ((B.heightPoly k.2 z * B.heightPoly k'.2 z : ℝ) : ℂ)) _ _
  rw [hprod, integral_complex_ofReal, integral_complex_ofReal, hB.radial_orthonormal, hB.height_orthonormal]
  obtain ⟨j, l⟩ := k
  obtain ⟨j', l'⟩ := k'
  by_cases hj : j = j' <;> by_cases hl : l = l' <;> simp [hj, hl]

theorem coefEnergy_le (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Y : ℝ × ℝ → ℂ)
    (hY : AEStronglyMeasurable Y (volume.restrict K.rect)) (C : ℝ) (hC : ∀ p ∈ K.rect, ‖Y p‖ ≤ C)
    (u : Finset (ℕ × ℕ)) :
    ∑ k ∈ u, ‖B.coef K Y k.1 k.2‖ ^ 2 ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖Y p‖ ^ 2 := by
  have := rect_finite K
  have hae : ∀ᵐ p ∂(volume.restrict K.rect), p ∈ K.rect := ae_restrict_mem (rect_meas K)
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hw := lineWeight_continuous K
  have hWc : Continuous (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ)) := by fun_prop
  have hbc := basisFn_continuous B
  have bm : ∀ (g : ℝ × ℝ → ℂ), Continuous g → ∀ (f : ℝ × ℝ → ℂ), AEStronglyMeasurable f (volume.restrict K.rect) →
      (∃ D, ∀ p ∈ K.rect, ‖f p‖ ≤ D) → Integrable (fun p => f p * g p) (volume.restrict K.rect) := by
    intro g hg f hf hfb
    obtain ⟨D, hD⟩ := hfb
    obtain ⟨E, hE⟩ := hcomp.exists_bound_of_continuousOn hg.continuousOn
    refine Integrable.of_bound (hf.mul hg.aestronglyMeasurable) (D * E) ?_
    filter_upwards [hae] with p hp
    rw [norm_mul]
    exact mul_le_mul (hD p hp) (hE p hp) (norm_nonneg _) ((norm_nonneg _).trans (hD p hp))
  have hcont : ∀ g : ℝ × ℝ → ℂ, Continuous g → Integrable g (volume.restrict K.rect) :=
    fun g hg => ContinuousOn.integrableOn_compact hcomp hg.continuousOn
  have hYc : AEStronglyMeasurable (fun p => conj (Y p)) (volume.restrict K.rect) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hY
  have hYcb : ∃ D, ∀ p ∈ K.rect, ‖conj (Y p)‖ ≤ D := ⟨C, fun p hp => by rw [Complex.norm_conj]; exact hC p hp⟩
  have hYYb : ∃ D, ∀ p ∈ K.rect, ‖Y p * conj (Y p)‖ ≤ D := ⟨C * C, fun p hp => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC p hp) (hC p hp) (norm_nonneg _) ((norm_nonneg _).trans (hC p hp))⟩
  set c : ℕ × ℕ → ℂ := fun k => B.coef K Y k.1 k.2 with hcdef
  have hck : ∀ k, ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Y p * basisFn B k p = c k := fun k => rfl
  set S : ℝ × ℝ → ℂ := fun p => ∑ k ∈ u, c k * basisFn B k p with hSdef
  have hS : Continuous S := continuous_finsetSum _ (fun k _ => continuous_const.mul (hbc k))
  have hconjφ : ∀ k p, conj (basisFn B k p) = basisFn B k p := fun k p => by
    unfold basisFn
    exact Complex.conj_ofReal _
  have hconjS : ∀ p, conj (S p) = ∑ k ∈ u, conj (c k) * basisFn B k p := by
    intro p
    simp only [hSdef, map_sum, map_mul, hconjφ]
  have hexp : ∀ p, (K.lineWeight p.1 : ℂ) * (Y p - S p) * conj (Y p - S p)
      = (K.lineWeight p.1 : ℂ) * Y p * conj (Y p) - (K.lineWeight p.1 : ℂ) * Y p * conj (S p)
        - (K.lineWeight p.1 : ℂ) * S p * conj (Y p) + (K.lineWeight p.1 : ℂ) * S p * conj (S p) := by
    intro p
    rw [map_sub]
    ring
  have iA : Integrable (fun p => (K.lineWeight p.1 : ℂ) * Y p * conj (Y p)) (volume.restrict K.rect) :=
    (bm _ hWc (fun p => Y p * conj (Y p)) (hY.mul hYc) hYYb).congr
      (Filter.Eventually.of_forall (fun p => by ring))
  have iBk : ∀ k, Integrable (fun p => (K.lineWeight p.1 : ℂ) * Y p * basisFn B k p) (volume.restrict K.rect) :=
    fun k => (bm _ (hWc.mul (hbc k)) Y hY ⟨C, hC⟩).congr (Filter.Eventually.of_forall (fun p => by
      simp only [Pi.mul_apply]
      ring))
  have eB1 : ∀ p, (K.lineWeight p.1 : ℂ) * Y p * conj (S p)
      = ∑ k ∈ u, conj (c k) * ((K.lineWeight p.1 : ℂ) * Y p * basisFn B k p) := by
    intro p
    rw [hconjS p, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have iB1 : Integrable (fun p => (K.lineWeight p.1 : ℂ) * Y p * conj (S p)) (volume.restrict K.rect) := by
    simp_rw [eB1]
    exact integrable_finsetSum _ (fun k _ => (iBk k).const_mul _)
  have vB1 : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Y p * conj (S p) = ∑ k ∈ u, conj (c k) * c k := by
    simp_rw [eB1]
    rw [integral_finsetSum _ (fun k _ => (iBk k).const_mul _)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul, hck]
  have eB2 : (fun p => (K.lineWeight p.1 : ℂ) * S p * conj (Y p))
      = fun p => conj ((K.lineWeight p.1 : ℂ) * Y p * conj (S p)) := by
    funext p
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have iB2 : Integrable (fun p => (K.lineWeight p.1 : ℂ) * S p * conj (Y p)) (volume.restrict K.rect) :=
    (bm _ (hWc.mul hS) (fun p => conj (Y p)) hYc hYcb).congr (Filter.Eventually.of_forall (fun p => by
      simp only [Pi.mul_apply]
      ring))
  have vB2 : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * S p * conj (Y p) = ∑ k ∈ u, c k * conj (c k) := by
    rw [eB2, integral_conj, vB1, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_mul, Complex.conj_conj]
  have eD : ∀ p, (K.lineWeight p.1 : ℂ) * S p * conj (S p)
      = ∑ k ∈ u, ∑ k' ∈ u, (c k * conj (c k')) * ((K.lineWeight p.1 : ℂ) * basisFn B k p * basisFn B k' p) := by
    intro p
    rw [hconjS p, mul_assoc, hSdef, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k' _ => by ring)
  have iDk : ∀ k k', Integrable (fun p => (c k * conj (c k')) * ((K.lineWeight p.1 : ℂ) * basisFn B k p * basisFn B k' p))
      (volume.restrict K.rect) := fun k k' => hcont _ (continuous_const.mul ((hWc.mul (hbc k)).mul (hbc k')))
  have iD : Integrable (fun p => (K.lineWeight p.1 : ℂ) * S p * conj (S p)) (volume.restrict K.rect) :=
    hcont _ ((hWc.mul hS).mul (Complex.continuous_conj.comp hS))
  have vD : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * S p * conj (S p) = ∑ k ∈ u, c k * conj (c k) := by
    simp_rw [eD]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun k' _ => iDk k k'))]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [integral_finsetSum _ (fun k' _ => iDk k k')]
    simp_rw [integral_const_mul, basis_orth K B hB]
    simp [hk]
  have vA : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Y p * conj (Y p)
      = ((∫ p in K.rect, K.lineWeight p.1 * ‖Y p‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have vL : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (Y p - S p) * conj (Y p - S p)
      = ((∫ p in K.rect, K.lineWeight p.1 * ‖Y p - S p‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hR : 0 ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖Y p - S p‖ ^ 2 := by
    refine setIntegral_nonneg (rect_meas K) (fun p hp => mul_nonneg ?_ (sq_nonneg _))
    unfold CellBox.lineWeight
    split_ifs
    · exact hp.1.1.trans' (by linarith)
    · exact zero_le_one
  have htot : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (Y p - S p) * conj (Y p - S p)
      = (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Y p * conj (Y p))
        - (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Y p * conj (S p))
        - (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * S p * conj (Y p))
        + ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * S p * conj (S p) := by
    simp_rw [hexp]
    have h3 : Integrable (fun p => (K.lineWeight p.1 : ℂ) * Y p * conj (Y p) - (K.lineWeight p.1 : ℂ) * Y p * conj (S p)
        - (K.lineWeight p.1 : ℂ) * S p * conj (Y p)) (volume.restrict K.rect) := (iA.sub iB1).sub iB2
    have h2 : Integrable (fun p => (K.lineWeight p.1 : ℂ) * Y p * conj (Y p) - (K.lineWeight p.1 : ℂ) * Y p * conj (S p))
        (volume.restrict K.rect) := iA.sub iB1
    rw [integral_add h3 iD, integral_sub h2 iB2, integral_sub iA iB1]
  rw [vL, vA, vB1, vB2, vD] at htot
  have hnc : ∀ k, conj (c k) * c k = ((‖c k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hnc] at htot
  have hre := congrArg Complex.re htot
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.re_sum] at hre
  have hsum : ∑ k ∈ u, ‖B.coef K Y k.1 k.2‖ ^ 2 = ∑ k ∈ u, ‖c k‖ ^ 2 := rfl
  rw [hsum]
  linarith

theorem inputFn_continuous (m : ℕ) (B : CellBases) {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O)
    (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (i : I) (c : Fin (T.dim i)) :
    Continuous (fun q : (ℝ × ℝ) × ℝ => T.inputFn m B w i c q.1 q.2) := by
  unfold TailFamily.inputFn
  have h1 := radialPoly_continuous B
  have h2 := heightPoly_continuous B
  fun_prop

theorem inputFn_bound (K : CellBox) (m : ℕ) (B : CellBases) {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O)
    (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (i : I) (c : Fin (T.dim i)) :
    ∃ E, ∀ p ∈ K.rect, ∀ θ : ℝ, ‖T.inputFn m B w i c p θ‖ ≤ E := by
  have h1 := radialPoly_continuous B
  have h2 := heightPoly_continuous B
  have hc : Continuous (fun p : ℝ × ℝ => (∑ n' ∈ T.inModes, ∑ j ∈ Finset.range (T.inputDeg i + 1),
      ∑ l ∈ Finset.range (T.inputDeg i + 1), ‖w i n' j l c‖ * |B.radialPoly j p.1 * B.heightPoly l p.2| : ℝ)) := by
    fun_prop
  obtain ⟨E, hE⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨E, fun p hp θ => le_trans ?_ ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hE p hp))⟩
  unfold TailFamily.inputFn
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n' _ => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun l _ => ?_))
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem outputMode_regular (K : CellBox) (m : ℕ) (B : CellBases) {I O : Type} [Fintype I] [Fintype O]
    (T : TailFamily I O) (hT : IsTailRegular K T) (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (o : O) (n : ℤ) :
    AEStronglyMeasurable (T.outputMode m B w o n) (volume.restrict K.rect) ∧
      ∃ C, ∀ p ∈ K.rect, ‖T.outputMode m B w o n p‖ ≤ C := by
  set G : (ℝ × ℝ) × ℝ → ℂ := fun q => Complex.exp (-(azimuth m n * q.2 : ℝ) * Complex.I) *
      (∑ i, ∑ c : Fin (T.dim i), T.mult i o c q.1 q.2 * T.inputFn m B w i c q.1 q.2) with hG
  have hOut : ∀ p, T.outputMode m B w o n p = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), G (p, θ) :=
    fun p => rfl
  constructor
  · have hGm : AEStronglyMeasurable G ((volume.restrict K.rect).prod volume) := by
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (by fun_prop : Continuous (fun q : (ℝ × ℝ) × ℝ =>
          Complex.exp (-(azimuth m n * q.2 : ℝ) * Complex.I))).aestronglyMeasurable
      · refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => Finset.aestronglyMeasurable_fun_sum _ (fun c _ => ?_))
        exact (hT.mult_measurable i o c).mul (inputFn_continuous m B T w i c).aestronglyMeasurable
    have hGr : AEStronglyMeasurable G ((volume.restrict K.rect).prod (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
      have e : (volume.restrict K.rect).prod (volume.restrict (Set.Ioc 0 (2 * Real.pi)))
          = ((volume.restrict K.rect).prod volume).restrict (Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi)) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [e]
      exact hGm.restrict
    have hI := hGr.integral_prod_right'
    have e2 : T.outputMode m B w o n = fun p => (1 / (2 * Real.pi) : ℂ) *
        ∫ θ, G (p, θ) ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
      funext p
      rw [hOut p, intervalIntegral.integral_of_le (by positivity)]
    rw [e2]
    exact hI.const_mul _
  · choose Cm hCm using hT.mult_bounded
    have hE : ∀ i (c : Fin (T.dim i)), ∃ E, ∀ p ∈ K.rect, ∀ θ : ℝ, ‖T.inputFn m B w i c p θ‖ ≤ E :=
      fun i c => inputFn_bound K m B T w i c
    choose E hE using hE
    refine ⟨‖(1 / (2 * Real.pi) : ℂ)‖ * ((∑ i, ∑ c : Fin (T.dim i), Cm i o c * E i c) * |2 * Real.pi - 0|),
      fun p hp => ?_⟩
    rw [hOut p, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => ?_)
    rw [hG]
    dsimp only
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
    rw [norm_mul]
    exact mul_le_mul (hCm i o c p hp θ) (hE i c p hp θ) (norm_nonneg _) ((norm_nonneg _).trans (hCm i o c p hp θ))

end MeshFarCoefEnergyInternal

open MeshFarCoefEnergyInternal in
theorem farSummable_holds : FarSummableStatement := by
  intro K B hK hB m D I O _ _ T hT w o n
  obtain ⟨hm, C, hC⟩ := outputMode_regular K m B T hT w o n
  refine summable_of_sum_le (c := ∫ p in K.rect, K.lineWeight p.1 * ‖T.outputMode m B w o n p‖ ^ 2)
    (fun jl => ?_) (fun u => ?_)
  · dsimp only
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  · refine le_trans (Finset.sum_le_sum (fun jl _ => ?_)) (coefEnergy_le K B hB _ hm C hC u)
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _

end CellAnalysis

end CellCert

end Breakdown
