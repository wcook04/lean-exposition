import Breakdown.CertCell.LocalFieldDefs2

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy

namespace Internal

theorem radialRowValue {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (u : D → ℂ) (hs : ∀ n a b j l, u (I.strainSlot n a b j l) = B.coef K (F n a b) j l)
    (n : modes) (C : Fin 3 → Fin 3 → ℂ) (hint : ∀ a b, IntegrableOn (F n a b) K.rect) (j l : Fin (Q + 1)) :
    rowApply (lowRow I n C j l) u = B.coef K (modeSum C (F n)) j l := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have h1 : rowApply (lowRow I n C j l) u = ∑ a : Fin 3, ∑ b : Fin 3, C a b * u (I.strainSlot n a b j l) := by
    unfold rowApply lowRow
    calc ∑ d, (∑ a : Fin 3, ∑ b : Fin 3, C a b * (if d = I.strainSlot n a b j l then 1 else 0)) * u d
        = ∑ d, ∑ a : Fin 3, ∑ b : Fin 3, C a b * ((if d = I.strainSlot n a b j l then 1 else 0) * u d) := by
          simp only [Finset.sum_mul, mul_assoc]
      _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ d, C a b * ((if d = I.strainSlot n a b j l then 1 else 0) * u d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ a : Fin 3, ∑ b : Fin 3, C a b * u (I.strainSlot n a b j l) := by
          simp [ite_mul, Finset.sum_ite_eq']
  rw [h1]
  simp only [hs]
  unfold CellBases.coef modeSum
  simp only [Finset.mul_sum, Finset.sum_mul]
  have hi : ∀ a b : Fin 3, IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * (C a b * F n a b p) *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
    intro a b
    have hc : ContinuousOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * C a b *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
      apply Continuous.continuousOn
      exact ((Complex.continuous_ofReal.comp ((RadialProjInternal.lineWeight_cont K).comp continuous_fst)).mul
        continuous_const).mul (Complex.continuous_ofReal.comp
          ((((RadialProjInternal.radialPoly_diff B j).continuous).comp continuous_fst).mul
            ((RadialProjInternal.heightPoly_cont B l).comp continuous_snd)))
    refine ((hint a b).continuousOn_mul hc hcomp).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    ring
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hi a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

theorem radialFieldParts (K : CellBox) (F dF : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (hT : ∀ a b, RadialTracePair K (F a b) (dF a b)) (C : Fin 3 → Fin 3 → ℂ) (hr : K.r₁ ≠ 0)
    (ψ t : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (ht : Continuous t) (h1 : ψ K.r₁ = 0) (h2 : ψ K.r₂ = 0) :
    ∫ p in K.rect, modeSum C dF p * ((ψ p.1 * t p.2 : ℝ) : ℂ) =
      -∫ p in K.rect, modeSum C F p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hc1 : ContinuousOn (fun p : ℝ × ℝ => ((ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp ((hψ.continuous.comp continuous_fst).mul (ht.comp continuous_snd))).continuousOn
  have hc2 : ContinuousOn (fun p : ℝ × ℝ => ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp (((hψ.continuous_deriv le_rfl).comp continuous_fst).mul
      (ht.comp continuous_snd))).continuousOn
  have i1 : ∀ a b, IntegrableOn (fun p => dF a b p * ((ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    fun a b => ((hT a b).2.2.1 hr).mul_continuousOn hc1 hcomp
  have i2 : ∀ a b, IntegrableOn (fun p => F a b p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    fun a b => ((hT a b).1).mul_continuousOn hc2 hcomp
  have hab : ∀ a b, ∫ p in K.rect, dF a b p * ((ψ p.1 * t p.2 : ℝ) : ℂ) =
      -∫ p in K.rect, F a b p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ) := by
    intro a b
    have h := (hT a b).2.2.2 ψ t hψ ht (Or.inl hr)
    rw [h1, h2, Complex.ofReal_zero, zero_mul, zero_mul, sub_zero, integral_add (i1 a b) (i2 a b)] at h
    exact eq_neg_of_add_eq_zero_left h
  have j1 : ∀ a b, IntegrableOn (fun p => C a b * dF a b p * ((ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    fun a b => by unfold IntegrableOn; simp only [mul_assoc]; exact (i1 a b).const_mul (C a b)
  have j2 : ∀ a b, IntegrableOn (fun p => C a b * F a b p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    fun a b => by unfold IntegrableOn; simp only [mul_assoc]; exact (i2 a b).const_mul (C a b)
  unfold modeSum
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => j1 a b,
    integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => j2 a b, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => j1 a b, integral_finsetSum _ fun b _ => j2 a b, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hab a b, mul_neg]

theorem radialLowPair {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (I : LowIndex D modes Q q)
    (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ)
    (hs : ∀ n a b j l, u (I.strainSlot n a b j l) = B.coef K (F n a b) j l)
    (n : modes) (C : Fin 3 → Fin 3 → ℂ) (hint : ∀ a b, IntegrableOn (F n a b) K.rect) (hr : K.r₁ ≠ 0)
    (φ : ℝ × ℝ → ℝ) (hpoly : (fun p => (φ p : ℂ)) ∈ polyFn Q Q) :
    rowApply (lowPairRow K B I n C φ) u = ∫ p in K.rect, modeSum C (F n) p * (φ p : ℂ) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hlw : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, hr]
  have hF : IntegrableOn (modeSum C (F n)) K.rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul (C a b)
  obtain ⟨e, he⟩ := HeightProj.span_mem B.radialCoef B.heightCoef (fun j => (hB.radial_leading j).ne')
    (fun j => (hB.height_leading j).ne') hpoly
  have hbc : ∀ j l : ℕ, Continuous (basisFn B j l) := fun j l =>
    ((RadialProjInternal.radialPoly_diff B j).continuous.comp continuous_fst).mul
      ((RadialProjInternal.heightPoly_cont B l).comp continuous_snd)
  have hor : ∀ j j', ∫ r in Set.Icc K.r₁ K.r₂, (fun _ : ℝ => (1 : ℝ)) r * HeightProj.triPoly B.radialCoef j r *
      HeightProj.triPoly B.radialCoef j' r = if j = j' then 1 else 0 := by
    intro j j'
    have := hB.radial_orthonormal j j'
    simp only [hlw] at this
    exact this
  have hort : ∀ j l j' l' : ℕ, ∫ p in K.rect, ((basisFn B j l p : ℝ) : ℂ) * ((basisFn B j' l' p : ℝ) : ℂ) =
      if j = j' ∧ l = l' then 1 else 0 := by
    intro j l j' l'
    have := HeightProj.ortho2 B.radialCoef B.heightCoef K.r₁ K.r₂ K.z₁ K.z₂ (fun _ => 1) hor
      hB.height_orthonormal j l j' l'
    simp only [Complex.ofReal_one, one_mul] at this
    exact this
  have hexp : ∀ p, (φ p : ℂ) = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((basisFn B j l p : ℝ) : ℂ) :=
    fun p => he p
  have hbb : ∀ (j l : ℕ) (j' l' : ℕ), IntegrableOn
      (fun p => ((basisFn B j l p : ℝ) : ℂ) * ((basisFn B j' l' p : ℝ) : ℂ)) K.rect := fun j l j' l' =>
    ((Complex.continuous_ofReal.comp (hbc j l)).mul
      (Complex.continuous_ofReal.comp (hbc j' l'))).continuousOn.integrableOn_compact hcomp
  have hco : ∀ j l : Fin (Q + 1), ((rectIntegral K (fun p => basisFn B j l p * φ p) : ℝ) : ℂ) = e j l := by
    intro j l
    unfold rectIntegral
    rw [← integral_complex_ofReal]
    have h1 : ∀ p, (((basisFn B j l p * φ p) : ℝ) : ℂ) = ∑ j' : Fin (Q + 1), ∑ l' : Fin (Q + 1),
        e j' l' * (((basisFn B j l p : ℝ) : ℂ) * ((basisFn B j' l' p : ℝ) : ℂ)) := by
      intro p
      rw [Complex.ofReal_mul, hexp p, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l' _ => ?_
      ring
    simp_rw [h1]
    rw [integral_finsetSum _ fun (j' : Fin (Q + 1)) _ => integrable_finsetSum _
      fun (l' : Fin (Q + 1)) _ => (hbb j l j' l').const_mul (e j' l')]
    have h2 : ∀ j' : Fin (Q + 1), ∫ p in K.rect, ∑ l' : Fin (Q + 1),
        e j' l' * (((basisFn B j l p : ℝ) : ℂ) * ((basisFn B j' l' p : ℝ) : ℂ)) =
        ∑ l' : Fin (Q + 1), e j' l' * (if (j : ℕ) = j' ∧ (l : ℕ) = l' then 1 else 0) := by
      intro j'
      rw [integral_finsetSum _ fun (l' : Fin (Q + 1)) _ => (hbb j l j' l').const_mul (e j' l')]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [integral_const_mul, hort]
    simp_rw [h2]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single l]
      · simp
      · intro l' _ hl'
        rw [if_neg]; · simp
        rintro ⟨-, h⟩; exact hl' (Fin.ext h.symm)
      · simp
    · intro j' _ hj'
      refine Finset.sum_eq_zero fun l' _ => ?_
      rw [if_neg]; · simp
      rintro ⟨h, -⟩; exact hj' (Fin.ext h.symm)
    · simp
  have hFb : ∀ j l : ℕ, IntegrableOn (fun p => modeSum C (F n) p * ((basisFn B j l p : ℝ) : ℂ)) K.rect :=
    fun j l => hF.mul_continuousOn ((Complex.continuous_ofReal.comp (hbc j l)).continuousOn) hcomp
  have hcoef : ∀ j l : ℕ, B.coef K (modeSum C (F n)) j l =
      ∫ p in K.rect, modeSum C (F n) p * ((basisFn B j l p : ℝ) : ℂ) := by
    intro j l
    unfold CellBases.coef
    congr 1
    funext p
    rw [hlw]
    simp [basisFn]
  have hrow : rowApply (lowPairRow K B I n C φ) u = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
      ((rectIntegral K (fun p => basisFn B j l p * φ p) : ℝ) : ℂ) * rowApply (lowRow I n C j l) u := by
    unfold rowApply lowPairRow
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  rw [hrow]
  simp_rw [hco, radialRowValue K B I F u hs n C hint, hcoef]
  simp_rw [hexp, Finset.mul_sum]
  have hFe : ∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => modeSum C (F n) p * (e j l * ((basisFn B j l p : ℝ) : ℂ))) K.rect := fun j l => by
    unfold IntegrableOn
    exact ((hFb j l).const_mul (e j l)).congr (Filter.Eventually.of_forall fun p => by ring)
  rw [integral_finsetSum _ fun (j : Fin (Q + 1)) _ => integrable_finsetSum _ fun (l : Fin (Q + 1)) _ => hFe j l]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun (l : Fin (Q + 1)) _ => hFe j l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

end Internal

theorem localRadialProjPiece {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (m : ℕ)
    (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ)
    (hB : IsCellBases K B) (hD : IsModeData m K B I F T u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) :
    quadFormValue (radialProjForm K B I n C) u =
      K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
        (CellBox.radialDeriv (K.proj Q Q (modeSum C (F n)))) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hint : ∀ a b, IntegrableOn (F n a b) K.rect := fun a b => (hD.radial_trace n a b).1
  have hF : IntegrableOn (modeSum C (F n)) K.rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul (C a b)
  have hFt : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * modeSum C (F n) p) K.rect := by
    intro t s ht hs
    refine hF.continuousOn_mul (Continuous.continuousOn ?_) hcomp
    exact Complex.continuous_ofReal.comp ((((RadialProjInternal.lineWeight_cont K).comp continuous_fst).mul
      (ht.comp continuous_fst)).mul (hs.comp continuous_snd))
  rw [HeightProj.proj_eq_basis K B hB Q _ hFt]
  set w : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) with hw
  set P : Fin (Q + 1) × Fin (Q + 1) → ℝ × ℝ → ℝ := fun jl => radialSlope (basisFn B jl.1 jl.2) with hP
  have hform : radialProjForm K B I n C =
      formOfRows (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowRow I n C jl.1 jl.2)
        ((K.innerRadius : ℂ) • testInnerMatrix K w P) := by
    unfold radialProjForm
    congr 1
    ext jl jl'
    simp only [Matrix.smul_apply, smul_eq_mul, testInnerMatrix, Complex.ofReal_mul, hw, hP]
  have hwc : Continuous w := ((RadialProjInternal.lineWeight_cont K).comp continuous_fst).mul
    (continuous_const.sub (((RadialProjInternal.refR_cont K).comp continuous_fst).pow 2))
  have hint2 : ∀ i i', IntegrableOn (fun p => w p * P i p * P i' p) K.rect := fun i i' =>
    ((hwc.mul (RadialProjInternal.slope_cont B i.1 i.2)).mul
      (RadialProjInternal.slope_cont B i'.1 i'.2)).continuousOn.integrableOn_compact hcomp
  rw [hform, RadialForm.value_formOfRows, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.re_ofReal_mul, RadialForm.pairing_value K w P hint2]
  congr 1
  unfold CellBox.normSqOn
  congr 1
  funext p
  congr 2
  rw [RadialProjInternal.deriv_basis_sum, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Internal.radialRowValue K B I F u hD.strain n C hint]

theorem localRadialInnerPiece {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (m : ℕ)
    (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ)
    (hK : IsCellBox K) (hB : IsCellBases K B) (hq : 1 ≤ q) (hqQ : q + 1 ≤ Q) (hD : IsModeData m K B I F T u)
    (n : modes) (C : Fin 3 → Fin 3 → ℂ) (hr : K.r₁ ≠ 0) :
    quadFormValue (radialInnerForm K B I n C) u =
      K.testSupremum (fun p => (p.1 - K.r₁) * (1 - K.refR p.1 ^ 2)) (polyFn (Q - 2) Q)
        (modeSum C (fun a b => T n a b 0)) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 2 := ⟨Q - 2, by omega⟩
  have hint : ∀ a b, IntegrableOn (F n a b) K.rect := fun a b => (hD.radial_trace n a b).1
  have hdF : IntegrableOn (modeSum C (fun a b => T n a b 0)) K.rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      ((hD.radial_trace n a b).2.2.1 hr).const_mul (C a b)
  have hw : (fun p : ℝ × ℝ => (p.1 - K.r₁) * (1 - K.refR p.1 ^ 2)) = radialInnerWeight K := rfl
  have hg : ∀ i : Fin (Q' + 2 - 2 + 1) × Fin (Q' + 2 + 1), IntegrableOn (fun p => ((radialInnerWeight K p : ℝ) : ℂ) *
      modeSum C (fun a b => T n a b 0) p * ((monomial i.1 i.2 p : ℝ) : ℂ)) K.rect := by
    intro i
    have hc : ContinuousOn (fun p : ℝ × ℝ => ((radialInnerWeight K p : ℝ) : ℂ) *
        ((monomial i.1 i.2 p : ℝ) : ℂ)) K.rect :=
      ((Complex.continuous_ofReal.comp (RadialInner.weight_cont K)).mul (Complex.continuous_ofReal.comp
        ((continuous_fst.pow _).mul (continuous_snd.pow _)))).continuousOn
    refine (hdF.continuousOn_mul hc hcomp).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    ring
  rw [hw, HeightParts.testSup_polyFn K hK (radialInnerWeight K) (RadialInner.weight_cont K)
    (RadialInner.weight_nonneg K hK) (RadialInner.weight_pos K hK) (Q' + 2 - 2) (Q' + 2) _
    (fun jl : Fin (Q' + 2 - 2 + 1) × Fin (Q' + 2 + 1) => lowPairRow K B I n C
      (fun p => -radialSlope (fun p' => radialInnerWeight K p' * monomial jl.1 jl.2 p') p)) u hg]
  · rfl
  · intro i
    obtain ⟨ψ, hψ, h1, h2, hslope, hwm, hpoly, _⟩ :=
      RadialInner.inner_test K hK (Q := Q' + 2) i.1 i.2 (by have := i.1.2; omega) (by have := i.2.2; omega)
    have hφ : (fun p => -radialSlope (fun p' => radialInnerWeight K p' * monomial i.1 i.2 p') p) =
        fun p : ℝ × ℝ => -(deriv ψ p.1 * p.2 ^ (i.2 : ℕ)) := funext fun p => by rw [hslope]
    rw [hφ, Internal.radialLowPair K B hB I F u hD.strain n C hint hr
      (fun p : ℝ × ℝ => -(deriv ψ p.1 * p.2 ^ (i.2 : ℕ))) hpoly]
    have e1 : ∫ p in K.rect, ((radialInnerWeight K p : ℝ) : ℂ) * modeSum C (fun a b => T n a b 0) p *
        ((monomial i.1 i.2 p : ℝ) : ℂ) =
        ∫ p in K.rect, modeSum C (fun a b => T n a b 0) p *
          ((ψ p.1 * (fun z : ℝ => z ^ (i.2 : ℕ)) p.2 : ℝ) : ℂ) := by
      congr 1
      funext p
      rw [show ψ p.1 * (fun z : ℝ => z ^ (i.2 : ℕ)) p.2 = radialInnerWeight K p * monomial i.1 i.2 p from
        (hwm p).symm]
      push_cast
      ring
    rw [e1, Internal.radialFieldParts K (F n) (fun a b => T n a b 0) (hD.radial_trace n) C hr ψ
      (fun z : ℝ => z ^ (i.2 : ℕ)) hψ (continuous_pow _) h1 h2, ← integral_neg]
    congr 1
    funext p
    push_cast
    ring

open Classical in
theorem localRadialLowPieces {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (m : ℕ)
    (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : D → ℂ)
    (hK : IsCellBox K) (hB : IsCellBases K B) (hq : 1 ≤ q) (hqQ : q + 1 ≤ Q) (hD : IsModeData m K B I F T u)
    (n : modes) (C : Fin 3 → Fin 3 → ℂ) :
    quadFormValue (radialProjForm K B I n C + (if K.r₁ = 0 then 0 else radialInnerForm K B I n C)) u =
      K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
          (CellBox.radialDeriv (K.proj Q Q (modeSum C (F n))))
        + (if K.r₁ = 0 then 0 else
          K.testSupremum (fun p => (p.1 - K.r₁) * (1 - K.refR p.1 ^ 2)) (polyFn (Q - 2) Q)
            (modeSum C (fun a b => T n a b 0))) := by
  rw [RadialForm.value_add, localRadialProjPiece m K B I F T u hB hD n C]
  by_cases h : K.r₁ = 0
  · simp only [h, if_true, RadialForm.value_zero]
  · simp only [h, if_false, localRadialInnerPiece m K B I F T u hK hB hq hqQ hD n C h]

end LocalField

end CertCell

end Breakdown
