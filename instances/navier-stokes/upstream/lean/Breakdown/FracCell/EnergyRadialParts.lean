import Breakdown.FracCell.EnergyRadialProj
import Breakdown.FracCell.EnergyHeightParts

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

def RadialTraceStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H → ∀ (n : ℤ) (a b : Fin 3),
      IntegrableOn (gradMode m n G a b) K.rect ∧
      IntegrableOn (fun p => (p.1 : ℂ) * radialGradMode m n H a b p) K.rect ∧
      (K.r₁ ≠ 0 → IntegrableOn (radialGradMode m n H a b) K.rect) ∧
      ∀ (ψ t : ℝ → ℝ), ContDiff ℝ 1 ψ → Continuous t → (K.r₁ ≠ 0 ∨ ψ 0 = 0) →
        ∫ p in K.rect, (radialGradMode m n H a b p * ((ψ p.1 * t p.2 : ℝ) : ℂ)
            + gradMode m n G a b p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) =
          ((ψ K.r₂ : ℝ) : ℂ) * radialFaceMoment K (gradMode m n G a b) (radialGradMode m n H a b) 1 t
            - ((ψ K.r₁ : ℝ) : ℂ) * radialFaceMoment K (gradMode m n G a b) (radialGradMode m n H a b) 0 t

namespace RadialInner

theorem field_parts (hT : RadialTraceStatement) (K : CellBox) (hK : IsCellBox K) (m : ℕ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hf : IsSecondOrderField m v G H) (n : ℤ) (C : Fin 3 → Fin 3 → ℂ) (hr : K.r₁ ≠ 0)
    (ψ t : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (ht : Continuous t) (h1 : ψ K.r₁ = 0) (h2 : ψ K.r₂ = 0) :
    ∫ p in K.rect, radialField m n H C p * ((ψ p.1 * t p.2 : ℝ) : ℂ) =
      -∫ p in K.rect, strainField m n G C p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hc1 : ContinuousOn (fun p : ℝ × ℝ => ((ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp ((hψ.continuous.comp continuous_fst).mul (ht.comp continuous_snd))).continuousOn
  have hc2 : ContinuousOn (fun p : ℝ × ℝ => ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp (((hψ.continuous_deriv le_rfl).comp continuous_fst).mul
      (ht.comp continuous_snd))).continuousOn
  have i1 : ∀ a b, IntegrableOn (fun p => radialGradMode m n H a b p * ((ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    fun a b => (((hT K hK m v G H hf n a b).2.2.1 hr)).mul_continuousOn hc1 hcomp
  have i2 : ∀ a b, IntegrableOn (fun p => gradMode m n G a b p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    fun a b => ((hT K hK m v G H hf n a b).1).mul_continuousOn hc2 hcomp
  have hab : ∀ a b, ∫ p in K.rect, radialGradMode m n H a b p * ((ψ p.1 * t p.2 : ℝ) : ℂ) =
      -∫ p in K.rect, gradMode m n G a b p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ) := by
    intro a b
    have h := (hT K hK m v G H hf n a b).2.2.2 ψ t hψ ht (Or.inl hr)
    rw [h1, h2, Complex.ofReal_zero, zero_mul, zero_mul, sub_zero, integral_add (i1 a b) (i2 a b)] at h
    exact eq_neg_of_add_eq_zero_left h
  have j1 : ∀ a b, IntegrableOn (fun p => C a b * radialGradMode m n H a b p * ((ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    fun a b => by unfold IntegrableOn; simp only [mul_assoc]; exact (i1 a b).const_mul (C a b)
  have j2 : ∀ a b, IntegrableOn (fun p => C a b * gradMode m n G a b p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    fun a b => by unfold IntegrableOn; simp only [mul_assoc]; exact (i2 a b).const_mul (C a b)
  unfold radialField strainField
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => j1 a b,
    integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => j2 a b, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => j1 a b, integral_finsetSum _ fun b _ => j2 a b, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hab a b, mul_neg]

theorem low_pair (hT : RadialTraceStatement) (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ}
    (c : FracCellData k N) (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ)
    (hE : EnergySetting α c K B S I v G H u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) (hr : K.r₁ ≠ 0)
    (φ : ℝ × ℝ → ℝ) (_hφ : Continuous φ) (hpoly : (fun p => (φ p : ℂ)) ∈ polyFn Q Q) :
    rowApply (lowPairRow K B I n C φ) u = ∫ p in K.rect, strainField c.order n G C p * (φ p : ℂ) := by
  have hK := hE.box
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hlw : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, hr]
  have hint : ∀ a b, IntegrableOn (gradMode c.order n G a b) K.rect := fun a b =>
    (hT K hK c.order v G H hE.field n a b).1
  have hF : IntegrableOn (strainField c.order n G C) K.rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul (C a b)
  obtain ⟨e, he⟩ := HeightProj.span_mem B.radialCoef B.heightCoef (fun j => (hE.bases.radial_leading j).ne')
    (fun j => (hE.bases.height_leading j).ne') hpoly
  have hbc : ∀ j l : ℕ, Continuous (basisFn B j l) := fun j l =>
    ((RadialProjInternal.radialPoly_diff B j).continuous.comp continuous_fst).mul
      ((RadialProjInternal.heightPoly_cont B l).comp continuous_snd)
  have hor : ∀ j j', ∫ r in Set.Icc K.r₁ K.r₂, (fun _ : ℝ => (1 : ℝ)) r * HeightProj.triPoly B.radialCoef j r *
      HeightProj.triPoly B.radialCoef j' r = if j = j' then 1 else 0 := by
    intro j j'
    have := hE.bases.radial_orthonormal j j'
    simp only [hlw] at this
    exact this
  have hort : ∀ j l j' l' : ℕ, ∫ p in K.rect, ((basisFn B j l p : ℝ) : ℂ) * ((basisFn B j' l' p : ℝ) : ℂ) =
      if j = j' ∧ l = l' then 1 else 0 := by
    intro j l j' l'
    have := HeightProj.ortho2 B.radialCoef B.heightCoef K.r₁ K.r₂ K.z₁ K.z₂ (fun _ => 1) hor
      hE.bases.height_orthonormal j l j' l'
    simp only [Complex.ofReal_one, one_mul] at this
    exact this
  have hexp : ∀ p, (φ p : ℂ) = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((basisFn B j l p : ℝ) : ℂ) :=
    fun p => he p
  have hbb : ∀ (j l : ℕ) (j' l' : ℕ), IntegrableOn
      (fun p => ((basisFn B j l p : ℝ) : ℂ) * ((basisFn B j' l' p : ℝ) : ℂ)) K.rect := fun j l j' l' =>
    ((Complex.continuous_ofReal.comp (hbc j l)).mul (Complex.continuous_ofReal.comp (hbc j' l'))).continuousOn.integrableOn_compact hcomp
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
  have hFb : ∀ j l : ℕ, IntegrableOn (fun p => strainField c.order n G C p * ((basisFn B j l p : ℝ) : ℂ)) K.rect :=
    fun j l => hF.mul_continuousOn ((Complex.continuous_ofReal.comp (hbc j l)).continuousOn) hcomp
  have hcoef : ∀ j l : ℕ, B.coef K (strainField c.order n G C) j l =
      ∫ p in K.rect, strainField c.order n G C p * ((basisFn B j l p : ℝ) : ℂ) := by
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
  simp_rw [hco, RadialProjInternal.row_value K B I c.order v G H u hE.represents n C hint, hcoef]
  simp_rw [hexp, Finset.mul_sum]
  have hFe : ∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => strainField c.order n G C p * (e j l * ((basisFn B j l p : ℝ) : ℂ))) K.rect := fun j l => by
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

theorem inner_test (K : CellBox) (hK : IsCellBox K) {Q : ℕ} (j l : ℕ) (hj : j + 2 ≤ Q) (hl : l ≤ Q) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ ∧ ψ K.r₁ = 0 ∧ ψ K.r₂ = 0 ∧
      (∀ p : ℝ × ℝ, radialSlope (fun p' => radialInnerWeight K p' * monomial j l p') p = deriv ψ p.1 * p.2 ^ l) ∧
      (∀ p : ℝ × ℝ, radialInnerWeight K p * monomial j l p = ψ p.1 * p.2 ^ l) ∧
      (fun p : ℝ × ℝ => (((-(deriv ψ p.1 * p.2 ^ l)) : ℝ) : ℂ)) ∈ polyFn Q Q ∧ Continuous (deriv ψ) := by
  open Polynomial in
  have hne : K.r₂ - K.r₁ ≠ 0 := by linarith [hK.r_order.2]
  set P : ℝ[X] := (X - C K.r₁) * (1 - ((C 2 * X - C (K.r₁ + K.r₂)) * C (1 / (K.r₂ - K.r₁))) ^ 2) * X ^ j with hP
  have hev : ∀ r, P.eval r = (r - K.r₁) * (1 - K.refR r ^ 2) * r ^ j := by
    intro r
    simp only [hP, eval_mul, eval_sub, eval_X, eval_C, eval_one, eval_pow]
    unfold CellBox.refR
    ring
  have hψ : (fun r => P.eval r) = fun r => (r - K.r₁) * (1 - K.refR r ^ 2) * r ^ j := funext hev
  have hder : ∀ r, deriv (fun r => P.eval r) r = P.derivative.eval r := fun r => P.deriv
  have hdeg : P.natDegree ≤ j + 3 := by
    rw [hP]
    compute_degree
    omega
  have hdeg' : P.derivative.natDegree < Q + 1 := by
    have := Polynomial.natDegree_derivative_le P
    omega
  have hdc : Continuous (deriv (fun r => P.eval r)) := by
    have : deriv (fun r => P.eval r) = fun r => P.derivative.eval r := funext hder
    rw [this]
    exact P.derivative.continuous
  refine ⟨fun r => P.eval r, contDiff_one_iff_deriv.mpr ⟨P.differentiable, hdc⟩, ?_, ?_, ?_, ?_, ?_, hdc⟩
  · show P.eval K.r₁ = 0
    rw [hev]; ring
  · show P.eval K.r₂ = 0
    rw [hev]
    have : K.refR K.r₂ = 1 := by unfold CellBox.refR; field_simp; ring
    rw [this]; ring
  · intro p
    rw [hder]
    have hf : (fun r : ℝ => radialInnerWeight K (r, p.2) * monomial j l (r, p.2)) =
        fun r => P.eval r * p.2 ^ l := by
      funext r
      rw [hev]
      simp only [radialInnerWeight, monomial]
      ring
    show deriv (fun r : ℝ => radialInnerWeight K (r, p.2) * monomial j l (r, p.2)) p.1 = _
    rw [hf, deriv_mul_const (P.differentiable p.1), hder]
  · intro p
    show _ = P.eval p.1 * p.2 ^ l
    rw [hev]
    simp only [radialInnerWeight, monomial]
    ring
  · refine ⟨fun k l' => if (l' : ℕ) = l then -((P.derivative.coeff k : ℝ) : ℂ) else 0, fun p => ?_⟩
    simp only [hder]
    rw [Polynomial.eval_eq_sum_range' hdeg', Finset.sum_range]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single ⟨l, by omega⟩]
    · simp
    · intro l' _ hl'
      rw [if_neg]
      · simp
      · intro h; exact hl' (Fin.ext h)
    · simp

theorem one_sub_refR_sq (K : CellBox) (hK : IsCellBox K) (r : ℝ) :
    1 - K.refR r ^ 2 = 4 * (K.r₂ - r) * (r - K.r₁) / (K.r₂ - K.r₁) ^ 2 := by
  have hne : K.r₂ - K.r₁ ≠ 0 := by linarith [hK.r_order.2]
  unfold CellBox.refR
  field_simp
  ring

theorem weight_cont (K : CellBox) : Continuous (radialInnerWeight K) := by
  unfold radialInnerWeight
  exact (continuous_fst.sub continuous_const).mul
    (continuous_const.sub (((RadialProjInternal.refR_cont K).comp continuous_fst).pow 2))

theorem weight_nonneg (K : CellBox) (hK : IsCellBox K) (p : ℝ × ℝ) (hp : p ∈ K.rect) :
    0 ≤ radialInnerWeight K p := by
  unfold radialInnerWeight
  rw [one_sub_refR_sq K hK]
  have h1 : K.r₁ ≤ p.1 := hp.1.1
  have h2 : p.1 ≤ K.r₂ := hp.1.2
  have : 0 ≤ 4 * (K.r₂ - p.1) * (p.1 - K.r₁) / (K.r₂ - K.r₁) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) (sq_nonneg _)
  exact mul_nonneg (by linarith) this

theorem weight_pos (K : CellBox) (hK : IsCellBox K) (p : ℝ × ℝ)
    (hp : p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) : 0 < radialInnerWeight K p := by
  unfold radialInnerWeight
  rw [one_sub_refR_sq K hK]
  have h1 : K.r₁ < p.1 := hp.1.1
  have h2 : p.1 < K.r₂ := hp.1.2
  have hne : 0 < (K.r₂ - K.r₁) ^ 2 := by have := hK.r_order.2; positivity
  have : 0 < 4 * (K.r₂ - p.1) * (p.1 - K.r₁) / (K.r₂ - K.r₁) ^ 2 :=
    div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) hne
  exact mul_pos (by linarith) this

end RadialInner

namespace RadialOuter

theorem ptw (x w : ℝ) (z y : ℂ) : ((x * w ^ 2 : ℝ) : ℂ) * (z / (w : ℂ)) * y = (x : ℂ) * z * ((w : ℂ) * y) := by
  by_cases h : w = 0
  · simp [h]
  · have hw : (w : ℂ) ≠ 0 := by exact_mod_cast h
    push_cast
    field_simp

theorem outer_sup (K : CellBox) (hK : IsCellBox K) {D : Type} [Fintype D] [DecidableEq D] (Q q : ℕ) (hQ : 1 ≤ Q)
    (g : ℝ × ℝ → ℂ) (rows : Fin Q × Fin (q + 1) → D → ℂ) (u : D → ℂ)
    (hg : ∀ i : Fin Q × Fin (q + 1),
      IntegrableOn (fun p => (p.1 : ℂ) * g p * ((radialOuterTest K i.1 i.2 p : ℝ) : ℂ)) K.rect)
    (hrow : ∀ i : Fin Q × Fin (q + 1),
      rowApply (rows i) u = ∫ p in K.rect, (p.1 : ℂ) * g p * ((radialOuterTest K i.1 i.2 p : ℝ) : ℂ)) :
    K.testSupremum (fun p => p.1) (scaledPolyFn K.lineWeightFn (Q - 1) q) g =
      quadFormValue (testSupForm rows
        (testInnerMatrix K (fun p => p.1) (fun jl : Fin Q × Fin (q + 1) => radialOuterTest K jl.1 jl.2))) u := by
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  set m' : ℝ × ℝ → ℝ := fun p => p.1 * K.lineWeight p.1 ^ 2 with hm'
  set g' : ℝ × ℝ → ℂ := fun p => g p / (K.lineWeight p.1 : ℂ) with hg'
  have hlw := RadialProjInternal.lineWeight_cont K
  have hlw0 : ∀ r, 0 ≤ r → 0 ≤ K.lineWeight r := fun r hr => by
    unfold CellBox.lineWeight; split_ifs <;> linarith
  have hlwp : ∀ r, 0 < r → 0 < K.lineWeight r := fun r hr => by
    unfold CellBox.lineWeight; split_ifs <;> linarith
  have hnorm : ∀ (P₀ : ℝ × ℝ → ℂ), K.normSqOn (fun p => p.1) (fun p => (K.lineWeightFn p : ℂ) * P₀ p) =
      K.normSqOn m' P₀ := by
    intro P₀
    unfold CellBox.normSqOn
    congr 1
    funext p
    simp only [hm', CellBox.lineWeightFn, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hpair : ∀ (P₀ : ℝ × ℝ → ℂ), K.pairOn (fun p => p.1) g (fun p => (K.lineWeightFn p : ℂ) * P₀ p) =
      K.pairOn m' g' P₀ := by
    intro P₀
    unfold CellBox.pairOn
    congr 1
    funext p
    simp only [hm', hg', CellBox.lineWeightFn, map_mul, Complex.conj_ofReal]
    exact (ptw _ _ _ _).symm
  have hset : K.testSupremum (fun p => p.1) (scaledPolyFn K.lineWeightFn (Q' + 1 - 1) q) g =
      K.testSupremum m' (polyFn (Q' + 1 - 1) q) g' := by
    unfold CellBox.testSupremum
    congr 1
    ext t
    constructor
    · rintro ⟨P, ⟨P₀, hP₀, hP⟩, hpos, rfl⟩
      have hPe : P = fun p => (K.lineWeightFn p : ℂ) * P₀ p := funext hP
      subst hPe
      exact ⟨P₀, hP₀, by rw [← hnorm]; exact hpos, by rw [hnorm, hpair]⟩
    · rintro ⟨P₀, hP₀, hpos, rfl⟩
      exact ⟨fun p => (K.lineWeightFn p : ℂ) * P₀ p, ⟨P₀, hP₀, fun p => rfl⟩, by rw [hnorm]; exact hpos,
        by rw [hnorm, hpair]⟩
  have hmc : Continuous m' := continuous_fst.mul ((hlw.comp continuous_fst).pow 2)
  have hm0 : ∀ p ∈ K.rect, 0 ≤ m' p := by
    intro p hp
    have : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    exact mul_nonneg this (sq_nonneg _)
  have hmpos : ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, 0 < m' p := by
    intro p hp
    have : 0 < p.1 := lt_of_le_of_lt hK.r_order.1 hp.1.1
    exact mul_pos this (pow_pos (hlwp _ this) 2)
  have hpt : ∀ (i : Fin (Q' + 1) × Fin (q + 1)) (p : ℝ × ℝ), ((m' p : ℝ) : ℂ) * g' p * ((monomial i.1 i.2 p : ℝ) : ℂ) =
      (p.1 : ℂ) * g p * ((radialOuterTest K i.1 i.2 p : ℝ) : ℂ) := by
    intro i p
    simp only [hm', hg', radialOuterTest]
    rw [ptw]
    push_cast
    ring
  rw [hset, HeightParts.testSup_polyFn K hK m' hmc hm0 hmpos (Q' + 1 - 1) q g' rows u
    (fun i => (hg i).congr_fun (fun p _ => (hpt i p).symm) (measurableSet_Icc.prod measurableSet_Icc))
    (fun i => by rw [hrow i]; congr 1; funext p; exact (hpt i p).symm)]
  congr 2
  ext i i'
  simp only [testInnerMatrix, rectIntegral, hm', radialOuterTest]
  congr 2
  funext p
  ring

theorem rowApply_add {D : Type} [Fintype D] (f g : D → ℂ) (u : D → ℂ) :
    rowApply (fun d => f d + g d) u = rowApply f u + rowApply g u := by
  unfold rowApply; simp only [add_mul, Finset.sum_add_distrib]

theorem rowApply_sum {D ι : Type} [Fintype D] [Fintype ι] (f : ι → D → ℂ) (u : D → ℂ) :
    rowApply (fun d => ∑ i, f i d) u = ∑ i, rowApply (f i) u := by
  unfold rowApply; simp only [Finset.sum_mul]; rw [Finset.sum_comm]

theorem rowApply_mul {D : Type} [Fintype D] (c : ℂ) (f : D → ℂ) (u : D → ℂ) :
    rowApply (fun d => c * f d) u = c * rowApply f u := by
  unfold rowApply; simp only [Finset.mul_sum, mul_assoc]

theorem face_expand (hT : RadialTraceStatement) (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ}
    (c : FracCellData k N) (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ)
    (hE : EnergySetting α c K B S I v G H u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) (e : Fin 2)
    (he : e = 0 → K.r₁ ≠ 0) (l : Fin (q + 1)) :
    ∑ l' : Fin (q + 1), ((heightMoment K B l l' : ℝ) : ℂ) * rowApply (radialFaceComp I n C e l') u =
      ∑ a : Fin 3, ∑ b : Fin 3, C a b *
        radialFaceMoment K (gradMode c.order n G a b) (radialGradMode c.order n H a b) e (fun z => z ^ (l : ℕ)) := by
  have hK := hE.box
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hdeg := hE.scalars.degrees
  obtain ⟨co, hco⟩ := HeightProj.pow_span B.heightCoef (fun j => (hE.bases.height_leading j).ne') q l
    (by have := l.2; omega)
  have hmom : ∀ l' : Fin (q + 1), heightMoment K B l l' = co l' := by
    intro l'
    unfold heightMoment
    have e1 : ∀ z, z ^ (l : ℕ) * B.heightPoly l' z =
        ∑ l'' : Fin (q + 1), co l'' * (B.heightPoly l'' z * B.heightPoly l' z) := by
      intro z
      rw [hco z, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l'' _ => ?_
      show co l'' * HeightProj.triPoly B.heightCoef l'' z * B.heightPoly l' z = _
      unfold HeightProj.triPoly CellBases.heightPoly
      ring
    simp_rw [e1]
    have hi : ∀ l'' : Fin (q + 1), IntegrableOn (fun z => co l'' * (B.heightPoly l'' z * B.heightPoly l' z))
        (Set.Icc K.z₁ K.z₂) := fun l'' =>
      (continuous_const.mul ((RadialProjInternal.heightPoly_cont B l'').mul
        (RadialProjInternal.heightPoly_cont B l'))).continuousOn.integrableOn_compact isCompact_Icc
    rw [integral_finsetSum _ fun l'' _ => hi l'']
    simp_rw [integral_const_mul, hE.bases.height_orthonormal]
    rw [Finset.sum_eq_single l']
    · simp
    · intro l'' _ hl''
      rw [if_neg]; · simp
      intro h; exact hl'' (Fin.ext h)
    · simp
  have hface : ∀ (a b : Fin 3) (t : ℝ → ℝ), Continuous t →
      ∀ (f : Fin (q + 1) → ℝ) (h : Fin (q + 1) → ℝ → ℝ), (∀ i, Continuous (h i)) → (∀ z, t z = ∑ i, f i * h i z) →
      radialFaceMoment K (gradMode c.order n G a b) (radialGradMode c.order n H a b) e t =
        ∑ i, (f i : ℂ) * radialFaceMoment K (gradMode c.order n G a b) (radialGradMode c.order n H a b) e (h i) := by
    intro a b t _ f h hh ht
    have hT' := hT K hK c.order v G H hE.field n a b
    have hstrip : ∀ (c' o : ℝ), (c' = K.r₂ ∧ o = K.r₁) ∨ (c' = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) →
        radialStripMoment c' o K.z₁ K.z₂ (gradMode c.order n G a b) (radialGradMode c.order n H a b) t =
          ∑ i, (f i : ℂ) * radialStripMoment c' o K.z₁ K.z₂ (gradMode c.order n G a b)
            (radialGradMode c.order n H a b) (h i) := by
      intro c' o hco'
      have hrect : Set.Icc (min c' o) (max c' o) ×ˢ Set.Icc K.z₁ K.z₂ = K.rect := by
        rcases hco' with ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩
        · rw [min_eq_right hK.r_order.2.le, max_eq_left hK.r_order.2.le]; rfl
        · rw [min_eq_left hK.r_order.2.le, max_eq_right hK.r_order.2.le]; rfl
      have hX : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c' - o) : ℝ)) : ℂ) * gradMode c.order n G a b p +
          (((p.1 - o) / (c' - o) : ℝ) : ℂ) * radialGradMode c.order n H a b p) K.rect := by
        refine (hT'.1.const_mul _).add ?_
        rcases hco' with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hr⟩
        · by_cases hr : K.r₁ = 0
          · have hc : ContinuousOn (fun p : ℝ × ℝ => (((1 / (K.r₂ - K.r₁)) : ℝ) : ℂ)) K.rect := continuousOn_const
            refine (hT'.2.1.continuousOn_mul hc hcomp).congr_fun (fun p _ => ?_)
              (measurableSet_Icc.prod measurableSet_Icc)
            simp only [hr, sub_zero]
            push_cast
            ring
          · refine ((hT'.2.2.1 hr).continuousOn_mul (Continuous.continuousOn ?_) hcomp)
            exact Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _)
        · refine ((hT'.2.2.1 hr).continuousOn_mul (Continuous.continuousOn ?_) hcomp)
          exact Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _)
      unfold radialStripMoment
      rw [hrect]
      have hXi : ∀ i, IntegrableOn (fun p : ℝ × ℝ => (f i : ℂ) * (((((1 / (c' - o) : ℝ)) : ℂ) *
          gradMode c.order n G a b p + (((p.1 - o) / (c' - o) : ℝ) : ℂ) * radialGradMode c.order n H a b p) *
            ((h i p.2 : ℝ) : ℂ))) K.rect := fun i =>
        (hX.mul_continuousOn ((Complex.continuous_ofReal.comp ((hh i).comp continuous_snd)).continuousOn) hcomp).const_mul _
      have e2 : ∀ p : ℝ × ℝ, ((((1 / (c' - o) : ℝ)) : ℂ) * gradMode c.order n G a b p +
          (((p.1 - o) / (c' - o) : ℝ) : ℂ) * radialGradMode c.order n H a b p) * ((t p.2 : ℝ) : ℂ) =
          ∑ i, (f i : ℂ) * (((((1 / (c' - o) : ℝ)) : ℂ) * gradMode c.order n G a b p +
          (((p.1 - o) / (c' - o) : ℝ) : ℂ) * radialGradMode c.order n H a b p) * ((h i p.2 : ℝ) : ℂ)) := by
        intro p
        rw [ht p.2]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      simp_rw [e2]
      rw [integral_finsetSum _ fun i _ => hXi i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul]
      ring
    unfold radialFaceMoment
    split_ifs with h1
    · exact hstrip _ _ (Or.inl ⟨rfl, rfl⟩)
    · have : e = 0 := by
        rcases Fin.exists_fin_two.mp ⟨e, rfl⟩ with h0 | h0 <;> [exact h0; exact absurd h0 h1]
      exact hstrip _ _ (Or.inr ⟨rfl, rfl, he this⟩)
  have hrowC : ∀ l' : Fin (q + 1), rowApply (radialFaceComp I n C e l') u = ∑ a : Fin 3, ∑ b : Fin 3, C a b *
      radialFaceMoment K (gradMode c.order n G a b) (radialGradMode c.order n H a b) e (B.heightPoly l') := by
    intro l'
    unfold radialFaceComp
    rw [rowApply_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [rowApply_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [rowApply_mul, hE.represents.radial_face n e a b l' he]
  simp_rw [hrowC, hmom, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hface a b (fun z => z ^ (l : ℕ)) (continuous_pow _) co (fun i => B.heightPoly i)
    (fun i => RadialProjInternal.heightPoly_cont B i) (fun z => hco z), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem low_pair_weighted (hT : RadialTraceStatement) (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ}
    (c : FracCellData k N) (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ)
    (hE : EnergySetting α c K B S I v G H u) (n : modes) (C : Fin 3 → Fin 3 → ℂ)
    (φ₀ : ℝ × ℝ → ℝ) (_hφ : Continuous φ₀) (hpoly : (fun p => (φ₀ p : ℂ)) ∈ polyFn Q Q) :
    rowApply (lowPairRow K B I n C (fun p => K.lineWeight p.1 * φ₀ p)) u =
      ∫ p in K.rect, strainField c.order n G C p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) := by
  have hK := hE.box
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hlc := RadialProjInternal.lineWeight_cont K
  have hint : ∀ a b, IntegrableOn (gradMode c.order n G a b) K.rect := fun a b =>
    (hT K hK c.order v G H hE.field n a b).1
  have hF : IntegrableOn (strainField c.order n G C) K.rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul (C a b)
  obtain ⟨e, he⟩ := HeightProj.span_mem B.radialCoef B.heightCoef (fun j => (hE.bases.radial_leading j).ne')
    (fun j => (hE.bases.height_leading j).ne') hpoly
  have hbc : ∀ j l : ℕ, Continuous (basisFn B j l) := fun j l =>
    ((RadialProjInternal.radialPoly_diff B j).continuous.comp continuous_fst).mul
      ((RadialProjInternal.heightPoly_cont B l).comp continuous_snd)
  have hort : ∀ j l j' l' : ℕ, ∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) * ((basisFn B j l p : ℝ) : ℂ) *
      ((basisFn B j' l' p : ℝ) : ℂ) = if j = j' ∧ l = l' then 1 else 0 := fun j l j' l' =>
    HeightProj.ortho2 B.radialCoef B.heightCoef K.r₁ K.r₂ K.z₁ K.z₂ K.lineWeight hE.bases.radial_orthonormal
      hE.bases.height_orthonormal j l j' l'
  have hexp : ∀ p, (φ₀ p : ℂ) = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((basisFn B j l p : ℝ) : ℂ) :=
    fun p => he p
  have hbb : ∀ (j l : ℕ) (j' l' : ℕ), IntegrableOn
      (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * ((basisFn B j l p : ℝ) : ℂ) * ((basisFn B j' l' p : ℝ) : ℂ))
        K.rect := fun j l j' l' =>
    (((Complex.continuous_ofReal.comp (hlc.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (hbc j l))).mul
        (Complex.continuous_ofReal.comp (hbc j' l'))).continuousOn.integrableOn_compact hcomp
  have hco : ∀ j l : Fin (Q + 1),
      ((rectIntegral K (fun p => basisFn B j l p * (K.lineWeight p.1 * φ₀ p)) : ℝ) : ℂ) = e j l := by
    intro j l
    unfold rectIntegral
    rw [← integral_complex_ofReal]
    have h1 : ∀ p, (((basisFn B j l p * (K.lineWeight p.1 * φ₀ p)) : ℝ) : ℂ) = ∑ j' : Fin (Q + 1),
        ∑ l' : Fin (Q + 1), e j' l' * (((K.lineWeight p.1 : ℝ) : ℂ) * ((basisFn B j l p : ℝ) : ℂ) *
          ((basisFn B j' l' p : ℝ) : ℂ)) := by
      intro p
      rw [Complex.ofReal_mul, Complex.ofReal_mul, hexp p, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l' _ => ?_
      ring
    simp_rw [h1]
    rw [integral_finsetSum _ fun (j' : Fin (Q + 1)) _ => integrable_finsetSum _
      fun (l' : Fin (Q + 1)) _ => (hbb j l j' l').const_mul (e j' l')]
    have h2 : ∀ j' : Fin (Q + 1), ∫ p in K.rect, ∑ l' : Fin (Q + 1),
        e j' l' * (((K.lineWeight p.1 : ℝ) : ℂ) * ((basisFn B j l p : ℝ) : ℂ) * ((basisFn B j' l' p : ℝ) : ℂ)) =
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
  have hFb : ∀ j l : ℕ, IntegrableOn (fun p => strainField c.order n G C p *
      (((K.lineWeight p.1 : ℝ) : ℂ) * ((basisFn B j l p : ℝ) : ℂ))) K.rect :=
    fun j l => hF.mul_continuousOn (((Complex.continuous_ofReal.comp (hlc.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (hbc j l))).continuousOn) hcomp
  have hcoef : ∀ j l : ℕ, B.coef K (strainField c.order n G C) j l =
      ∫ p in K.rect, strainField c.order n G C p * (((K.lineWeight p.1 : ℝ) : ℂ) * ((basisFn B j l p : ℝ) : ℂ)) := by
    intro j l
    unfold CellBases.coef
    congr 1
    funext p
    simp only [basisFn]
    ring
  have hrow : rowApply (lowPairRow K B I n C (fun p => K.lineWeight p.1 * φ₀ p)) u =
      ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
      ((rectIntegral K (fun p => basisFn B j l p * (K.lineWeight p.1 * φ₀ p)) : ℝ) : ℂ) *
        rowApply (lowRow I n C j l) u := by
    unfold rowApply lowPairRow
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  rw [hrow]
  simp_rw [hco, RadialProjInternal.row_value K B I c.order v G H u hE.represents n C hint, hcoef]
  have hFe : ∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => strainField c.order n G C p * (((K.lineWeight p.1 : ℝ) : ℂ) *
        (e j l * ((basisFn B j l p : ℝ) : ℂ)))) K.rect := fun j l => by
    unfold IntegrableOn
    exact ((hFb j l).const_mul (e j l)).congr (Filter.Eventually.of_forall fun p => by ring)
  have e3 : ∀ p, strainField c.order n G C p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) =
      ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), strainField c.order n G C p * (((K.lineWeight p.1 : ℝ) : ℂ) *
        (e j l * ((basisFn B j l p : ℝ) : ℂ))) := by
    intro p
    rw [Complex.ofReal_mul, hexp p, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [e3]
  rw [integral_finsetSum _ fun (j : Fin (Q + 1)) _ => integrable_finsetSum _ fun (l : Fin (Q + 1)) _ => hFe j l]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun (l : Fin (Q + 1)) _ => hFe j l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

theorem poly_mem {Q : ℕ} (R : Polynomial ℝ) (hR : R.natDegree < Q + 1) (l : ℕ) (hl : l ≤ Q) :
    (fun p : ℝ × ℝ => (((-(R.eval p.1 * p.2 ^ l)) : ℝ) : ℂ)) ∈ polyFn Q Q := by
  refine ⟨fun k l' => if (l' : ℕ) = l then -((R.coeff k : ℝ) : ℂ) else 0, fun p => ?_⟩
  show ((-(R.eval p.1 * p.2 ^ l) : ℝ) : ℂ) = _
  rw [Polynomial.eval_eq_sum_range' hR, Finset.sum_range]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single ⟨l, by omega⟩]
  · simp
  · intro l' _ hl'
    rw [if_neg]
    · simp
    · intro h; exact hl' (Fin.ext h)
  · simp

theorem outer_test (K : CellBox) (hK : IsCellBox K) {Q : ℕ} (j l : ℕ) (hj : j + 1 ≤ Q) (hl : l ≤ Q) :
    ∃ (ψ : ℝ → ℝ) (φ₀ : ℝ × ℝ → ℝ), ContDiff ℝ 1 ψ ∧ ψ 0 = 0 ∧
      ψ K.r₂ = K.r₂ * K.lineWeight K.r₂ * K.r₂ ^ j ∧ ψ K.r₁ = -(K.r₁ * K.lineWeight K.r₁ * K.r₁ ^ j) ∧
      (∀ p : ℝ × ℝ, p.1 * K.refR p.1 * radialOuterTest K j l p = ψ p.1 * p.2 ^ l) ∧
      (∀ p : ℝ × ℝ, -radialSlope (fun p' => p'.1 * K.refR p'.1 * radialOuterTest K j l p') p =
        K.lineWeight p.1 * φ₀ p) ∧
      (∀ p : ℝ × ℝ, K.lineWeight p.1 * φ₀ p = -(deriv ψ p.1 * p.2 ^ l)) ∧
      Continuous φ₀ ∧ (fun p => (φ₀ p : ℂ)) ∈ polyFn Q Q := by
  open Polynomial in
  have hne : K.r₂ - K.r₁ ≠ 0 := by linarith [hK.r_order.2]
  have href1 : K.refR K.r₁ = -1 := by unfold CellBox.refR; field_simp; ring
  have href2 : K.refR K.r₂ = 1 := by unfold CellBox.refR; field_simp; ring
  set RP : ℝ[X] := (C 2 * X - C (K.r₁ + K.r₂)) * C (1 / (K.r₂ - K.r₁)) with hRP
  have hRPe : ∀ r, RP.eval r = K.refR r := by
    intro r
    simp only [hRP, eval_mul, eval_sub, eval_X, eval_C]
    unfold CellBox.refR
    ring
  have hRPd : RP.natDegree ≤ 1 := by rw [hRP]; compute_degree
  by_cases h0 : K.r₁ = 0
  · have hlw : ∀ r, K.lineWeight r = r := fun r => by simp [CellBox.lineWeight, h0]
    set P : ℝ[X] := X ^ 2 * (RP * X ^ j) with hP
    have hev : ∀ r, P.eval r = r * K.refR r * K.lineWeight r * r ^ j := by
      intro r; rw [hlw]; simp only [hP, eval_mul, eval_pow, eval_X, hRPe]; ring
    have hder : ∀ r, deriv (fun r => P.eval r) r = P.derivative.eval r := fun r => P.deriv
    have hc0 : P.derivative.coeff 0 = 0 := by
      rw [coeff_derivative, hP, coeff_X_pow_mul']
      simp
    have hdiv : ∀ r, r * P.derivative.divX.eval r = P.derivative.eval r := by
      intro r
      have := X_mul_divX_add P.derivative
      rw [hc0, map_zero, add_zero] at this
      conv_rhs => rw [← this]
      simp
    have hdeg : P.natDegree ≤ j + 3 := by
      rw [hP]
      calc (X ^ 2 * (RP * X ^ j)).natDegree ≤ (X ^ 2 : ℝ[X]).natDegree + (RP * X ^ j).natDegree := natDegree_mul_le
        _ ≤ 2 + (1 + j) := add_le_add (natDegree_X_pow_le 2)
            (natDegree_mul_le.trans (add_le_add hRPd (natDegree_X_pow_le j)))
        _ ≤ j + 3 := by omega
    have hdeg' : P.derivative.divX.natDegree < Q + 1 := by
      rw [natDegree_divX_eq_natDegree_tsub_one]
      have := natDegree_derivative_le P
      omega
    have hdc : Continuous (deriv (fun r => P.eval r)) := by
      have : deriv (fun r => P.eval r) = fun r => P.derivative.eval r := funext hder
      rw [this]; exact P.derivative.continuous
    refine ⟨fun r => P.eval r, fun p => -(P.derivative.divX.eval p.1 * p.2 ^ l),
      contDiff_one_iff_deriv.mpr ⟨P.differentiable, hdc⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, poly_mem _ hdeg' l hl⟩
    · show P.eval 0 = 0
      simp [hP]
    · show P.eval K.r₂ = _
      rw [hev, href2]; ring
    · show P.eval K.r₁ = _
      rw [hev, href1]; ring
    · intro p
      show _ = P.eval p.1 * p.2 ^ l
      rw [hev]
      simp only [radialOuterTest, monomial]
      ring
    · intro p
      have hf : (fun r : ℝ => r * K.refR r * radialOuterTest K j l (r, p.2)) = fun r => P.eval r * p.2 ^ l := by
        funext r
        rw [hev]
        simp only [radialOuterTest, monomial]
        ring
      show -deriv (fun r : ℝ => r * K.refR r * radialOuterTest K j l (r, p.2)) p.1 = _
      rw [hf, deriv_mul_const (P.differentiable p.1), hder, hlw, ← hdiv]
      ring
    · intro p
      show K.lineWeight p.1 * -(P.derivative.divX.eval p.1 * p.2 ^ l) = -(deriv (fun r => P.eval r) p.1 * p.2 ^ l)
      rw [hlw, hder, ← hdiv]
      ring
    · exact ((P.derivative.divX.continuous.comp continuous_fst).mul (continuous_snd.pow _)).neg
  · have hlw : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h0]
    set P : ℝ[X] := X * (RP * X ^ j) with hP
    have hev : ∀ r, P.eval r = r * K.refR r * K.lineWeight r * r ^ j := by
      intro r; rw [hlw]; simp only [hP, eval_mul, eval_pow, eval_X, hRPe]; ring
    have hder : ∀ r, deriv (fun r => P.eval r) r = P.derivative.eval r := fun r => P.deriv
    have hdeg : P.natDegree ≤ j + 2 := by
      rw [hP]
      calc (X * (RP * X ^ j)).natDegree ≤ (X : ℝ[X]).natDegree + (RP * X ^ j).natDegree := natDegree_mul_le
        _ ≤ 1 + (1 + j) := add_le_add natDegree_X_le
            (natDegree_mul_le.trans (add_le_add hRPd (natDegree_X_pow_le j)))
        _ ≤ j + 2 := by omega
    have hdeg' : P.derivative.natDegree < Q + 1 := by
      have := natDegree_derivative_le P
      omega
    have hdc : Continuous (deriv (fun r => P.eval r)) := by
      have : deriv (fun r => P.eval r) = fun r => P.derivative.eval r := funext hder
      rw [this]; exact P.derivative.continuous
    refine ⟨fun r => P.eval r, fun p => -(P.derivative.eval p.1 * p.2 ^ l),
      contDiff_one_iff_deriv.mpr ⟨P.differentiable, hdc⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, poly_mem _ hdeg' l hl⟩
    · show P.eval 0 = 0
      simp [hP]
    · show P.eval K.r₂ = _
      rw [hev, href2]; ring
    · show P.eval K.r₁ = _
      rw [hev, href1]; ring
    · intro p
      show _ = P.eval p.1 * p.2 ^ l
      rw [hev]
      simp only [radialOuterTest, monomial]
      ring
    · intro p
      have hf : (fun r : ℝ => r * K.refR r * radialOuterTest K j l (r, p.2)) = fun r => P.eval r * p.2 ^ l := by
        funext r
        rw [hev]
        simp only [radialOuterTest, monomial]
        ring
      show -deriv (fun r : ℝ => r * K.refR r * radialOuterTest K j l (r, p.2)) p.1 = _
      rw [hf, deriv_mul_const (P.differentiable p.1), hlw, hder]
      ring
    · intro p
      show K.lineWeight p.1 * -(P.derivative.eval p.1 * p.2 ^ l) = -(deriv (fun r => P.eval r) p.1 * p.2 ^ l)
      rw [hlw, hder]
      ring
    · exact ((P.derivative.continuous.comp continuous_fst).mul (continuous_snd.pow _)).neg

theorem outer_row (hT : RadialTraceStatement) (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ}
    (c : FracCellData k N) (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ)
    (hE : EnergySetting α c K B S I v G H u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) (j : Fin Q) (l : Fin (q + 1)) :
    rowApply (radialOuterRow K B I n C j l) u =
      ∫ p in K.rect, (p.1 : ℂ) * ((K.refR p.1 : ℂ) * radialField c.order n H C p) *
        ((radialOuterTest K j l p : ℝ) : ℂ) := by
  have hK := hE.box
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hdeg := hE.scalars.degrees
  rw [← hE.degHigh_eq, ← hE.degLow_eq] at hdeg
  obtain ⟨ψ, φ₀, hψ, hψ0, hψ2, hψ1, hpt, hsl, hφψ, hφc, hpoly⟩ :=
    outer_test K hK (Q := Q) j l (by have := j.2; omega) (by have := l.2; omega)
  have hrow : rowApply (radialOuterRow K B I n C j l) u =
      ((K.r₂ * K.lineWeight K.r₂ * K.r₂ ^ (j : ℕ) : ℝ) : ℂ) *
          ∑ l' : Fin (q + 1), ((heightMoment K B l l' : ℝ) : ℂ) * rowApply (radialFaceComp I n C 1 l') u
        + ((K.r₁ * K.lineWeight K.r₁ * K.r₁ ^ (j : ℕ) : ℝ) : ℂ) *
          ∑ l' : Fin (q + 1), ((heightMoment K B l l' : ℝ) : ℂ) * rowApply (radialFaceComp I n C 0 l') u
        + ∫ p in K.rect, strainField c.order n G C p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) := by
    unfold radialOuterRow
    rw [rowApply_add, rowApply_sum]
    simp only [rowApply_mul, rowApply_add]
    have hlp : (fun p => -radialSlope (fun p' => p'.1 * K.refR p'.1 * radialOuterTest K j l p') p) =
        fun p => K.lineWeight p.1 * φ₀ p := funext hsl
    rw [hlp, low_pair_weighted hT α c K B S I v G H u hE n C φ₀ hφc hpoly]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    · refine Finset.sum_congr rfl fun l' _ => ?_; ring
    · refine Finset.sum_congr rfl fun l' _ => ?_; ring
  have hface0 : ((K.r₁ * K.lineWeight K.r₁ * K.r₁ ^ (j : ℕ) : ℝ) : ℂ) *
        ∑ l' : Fin (q + 1), ((heightMoment K B l l' : ℝ) : ℂ) * rowApply (radialFaceComp I n C 0 l') u =
      ((K.r₁ * K.lineWeight K.r₁ * K.r₁ ^ (j : ℕ) : ℝ) : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, C a b *
        radialFaceMoment K (gradMode c.order n G a b) (radialGradMode c.order n H a b) 0 (fun z => z ^ (l : ℕ)) := by
    by_cases hr0 : K.r₁ = 0
    · simp [hr0]
    · rw [face_expand hT α c K B S I v G H u hE n C 0 (fun _ => hr0) l]
  rw [hrow, hface0, face_expand hT α c K B S I v G H u hE n C 1 (fun h => absurd h (by decide)) l]
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hc1 : ContinuousOn (fun p : ℝ × ℝ => ((K.refR p.1 * radialOuterTest K j l p : ℝ) : ℂ)) K.rect := by
    apply Continuous.continuousOn
    refine Complex.continuous_ofReal.comp (((RadialProjInternal.refR_cont K).comp continuous_fst).mul ?_)
    unfold radialOuterTest monomial
    exact ((RadialProjInternal.lineWeight_cont K).comp continuous_fst).mul
      ((continuous_fst.pow _).mul (continuous_snd.pow _))
  have hc2 : ContinuousOn (fun p : ℝ × ℝ => ((deriv ψ p.1 * p.2 ^ (l : ℕ) : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp ((hdc.comp continuous_fst).mul (continuous_snd.pow _))).continuousOn
  have hptc : ∀ p : ℝ × ℝ, ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ) =
      (p.1 : ℂ) * ((K.refR p.1 * radialOuterTest K j l p : ℝ) : ℂ) := by
    intro p
    show ((ψ p.1 * p.2 ^ (l : ℕ) : ℝ) : ℂ) = _
    rw [← hpt p]
    push_cast
    ring
  have i1 : ∀ a b, IntegrableOn (fun p => radialGradMode c.order n H a b p *
      ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ)) K.rect := by
    intro a b
    refine (((hT K hK c.order v G H hE.field n a b).2.1).mul_continuousOn hc1 hcomp).congr_fun (fun p _ => ?_)
      (measurableSet_Icc.prod measurableSet_Icc)
    simp only []
    rw [hptc p]
    ring
  have i2 : ∀ a b, IntegrableOn (fun p => gradMode c.order n G a b p *
      ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ)) K.rect := fun a b =>
    ((hT K hK c.order v G H hE.field n a b).1).mul_continuousOn hc2 hcomp
  have key : ∀ a b, ∫ p in K.rect, radialGradMode c.order n H a b p *
      ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ) =
      ((ψ K.r₂ : ℝ) : ℂ) * radialFaceMoment K (gradMode c.order n G a b) (radialGradMode c.order n H a b) 1
          (fun z => z ^ (l : ℕ))
        - ((ψ K.r₁ : ℝ) : ℂ) * radialFaceMoment K (gradMode c.order n G a b) (radialGradMode c.order n H a b) 0
          (fun z => z ^ (l : ℕ))
        - ∫ p in K.rect, gradMode c.order n G a b p * ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ) := by
    intro a b
    have h := (hT K hK c.order v G H hE.field n a b).2.2.2 ψ (fun z => z ^ (l : ℕ)) hψ (continuous_pow _)
      (Or.inr hψ0)
    rw [integral_add (i1 a b) (i2 a b)] at h
    rw [← h]
    ring
  have j1 : ∀ a b, IntegrableOn (fun p => C a b * (radialGradMode c.order n H a b p *
      ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ))) K.rect := fun a b => (i1 a b).const_mul _
  have j2 : ∀ a b, IntegrableOn (fun p => C a b * (gradMode c.order n G a b p *
      ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ))) K.rect := fun a b => (i2 a b).const_mul _
  have hR : ∫ p in K.rect, (p.1 : ℂ) * ((K.refR p.1 : ℂ) * radialField c.order n H C p) *
      ((radialOuterTest K j l p : ℝ) : ℂ) = ∑ a : Fin 3, ∑ b : Fin 3, C a b * ∫ p in K.rect,
        radialGradMode c.order n H a b p * ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ) := by
    have e1 : ∀ p : ℝ × ℝ, (p.1 : ℂ) * ((K.refR p.1 : ℂ) * radialField c.order n H C p) *
        ((radialOuterTest K j l p : ℝ) : ℂ) = ∑ a : Fin 3, ∑ b : Fin 3, C a b *
          (radialGradMode c.order n H a b p * ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ)) := by
      intro p
      rw [hptc p]
      unfold radialField
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      push_cast
      ring
    simp_rw [e1]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => j1 a b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => j1 a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
  have hL : ∫ p in K.rect, strainField c.order n G C p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) =
      -∑ a : Fin 3, ∑ b : Fin 3, C a b * ∫ p in K.rect,
        gradMode c.order n G a b p * ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ) := by
    have e2 : ∀ p : ℝ × ℝ, strainField c.order n G C p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) =
        -∑ a : Fin 3, ∑ b : Fin 3, C a b *
          (gradMode c.order n G a b p * ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ)) := by
      intro p
      rw [hφψ p]
      unfold strainField
      simp only [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      push_cast
      ring
    simp_rw [e2]
    rw [integral_neg, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => j2 a b]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => j2 a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
  rw [hR, hL]
  simp_rw [key]
  rw [hψ2, hψ1]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

end RadialOuter

namespace RadialPieces

theorem proj_piece (hT : RadialTraceStatement) (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ}
    (c : FracCellData k N) (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ)
    (hE : EnergySetting α c K B S I v G H u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) :
    quadFormValue (radialProjForm K B I n C) u =
      K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
        (CellBox.radialDeriv (K.proj Q Q (strainField c.order n G C))) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hint : ∀ a b, IntegrableOn (gradMode c.order n G a b) K.rect := fun a b =>
    (hT K hE.box c.order v G H hE.field n a b).1
  have hF : IntegrableOn (strainField c.order n G C) K.rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul (C a b)
  have hFt : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * strainField c.order n G C p) K.rect := by
    intro t s ht hs
    refine hF.continuousOn_mul (Continuous.continuousOn ?_) hcomp
    exact Complex.continuous_ofReal.comp ((((RadialProjInternal.lineWeight_cont K).comp continuous_fst).mul
      (ht.comp continuous_fst)).mul (hs.comp continuous_snd))
  rw [HeightProj.proj_eq_basis K B hE.bases Q _ hFt]
  set m : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) with hm
  set P : Fin (Q + 1) × Fin (Q + 1) → ℝ × ℝ → ℝ := fun jl => radialSlope (basisFn B jl.1 jl.2) with hP
  have hform : radialProjForm K B I n C =
      formOfRows (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowRow I n C jl.1 jl.2)
        ((K.innerRadius : ℂ) • testInnerMatrix K m P) := by
    unfold radialProjForm
    congr 1
    ext jl jl'
    simp only [Matrix.smul_apply, smul_eq_mul, testInnerMatrix, Complex.ofReal_mul, hm, hP]
  have hmc : Continuous m := ((RadialProjInternal.lineWeight_cont K).comp continuous_fst).mul
    (continuous_const.sub (((RadialProjInternal.refR_cont K).comp continuous_fst).pow 2))
  have hint2 : ∀ i i', IntegrableOn (fun p => m p * P i p * P i' p) K.rect := fun i i' =>
    ((hmc.mul (RadialProjInternal.slope_cont B i.1 i.2)).mul
      (RadialProjInternal.slope_cont B i'.1 i'.2)).continuousOn.integrableOn_compact hcomp
  rw [hform, RadialForm.value_formOfRows, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.re_ofReal_mul, RadialForm.pairing_value K m P hint2]
  congr 1
  unfold CellBox.normSqOn
  congr 1
  funext p
  congr 2
  rw [RadialProjInternal.deriv_basis_sum, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [RadialProjInternal.row_value K B I c.order v G H u hE.represents n C hint]

theorem inner_piece (hT : RadialTraceStatement) (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ}
    (c : FracCellData k N) (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ)
    (hE : EnergySetting α c K B S I v G H u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) (hr : K.r₁ ≠ 0) :
    quadFormValue (radialInnerForm K B I n C) u =
      K.testSupremum (fun p => (p.1 - K.r₁) * (1 - K.refR p.1 ^ 2)) (polyFn (Q - 2) Q) (radialField c.order n H C) := by
  have hK := hE.box
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 2 := ⟨Q - 2, by
    have := hE.scalars.degrees; rw [hE.degHigh_eq]; omega⟩
  have hdF : IntegrableOn (radialField c.order n H C) K.rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      ((hT K hK c.order v G H hE.field n a b).2.2.1 hr).const_mul (C a b)
  have hw : (fun p : ℝ × ℝ => (p.1 - K.r₁) * (1 - K.refR p.1 ^ 2)) = radialInnerWeight K := rfl
  have hg : ∀ i : Fin (Q' + 2 - 2 + 1) × Fin (Q' + 2 + 1), IntegrableOn (fun p => ((radialInnerWeight K p : ℝ) : ℂ) *
      radialField c.order n H C p * ((monomial i.1 i.2 p : ℝ) : ℂ)) K.rect := by
    intro i
    have hc : ContinuousOn (fun p : ℝ × ℝ => ((radialInnerWeight K p : ℝ) : ℂ) * ((monomial i.1 i.2 p : ℝ) : ℂ)) K.rect :=
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
    obtain ⟨ψ, hψ, h1, h2, hslope, hwm, hpoly, hdc⟩ :=
      RadialInner.inner_test K hK (Q := Q' + 2) i.1 i.2 (by have := i.1.2; omega) (by have := i.2.2; omega)
    have hφ : (fun p => -radialSlope (fun p' => radialInnerWeight K p' * monomial i.1 i.2 p') p) =
        fun p : ℝ × ℝ => -(deriv ψ p.1 * p.2 ^ (i.2 : ℕ)) := funext fun p => by rw [hslope]
    rw [hφ, RadialInner.low_pair hT α c K B S I v G H u hE n C hr
      (fun p : ℝ × ℝ => -(deriv ψ p.1 * p.2 ^ (i.2 : ℕ)))
      (((hdc.comp continuous_fst).mul (continuous_snd.pow _)).neg) hpoly]
    have e1 : ∫ p in K.rect, ((radialInnerWeight K p : ℝ) : ℂ) * radialField c.order n H C p *
        ((monomial i.1 i.2 p : ℝ) : ℂ) =
        ∫ p in K.rect, radialField c.order n H C p * ((ψ p.1 * (fun z : ℝ => z ^ (i.2 : ℕ)) p.2 : ℝ) : ℂ) := by
      congr 1
      funext p
      rw [show ψ p.1 * (fun z : ℝ => z ^ (i.2 : ℕ)) p.2 = radialInnerWeight K p * monomial i.1 i.2 p from (hwm p).symm]
      push_cast
      ring
    rw [e1, RadialInner.field_parts hT K hK c.order v G H hE.field n C hr ψ (fun z : ℝ => z ^ (i.2 : ℕ)) hψ
      (continuous_pow _) h1 h2, ← integral_neg]
    congr 1
    funext p
    push_cast
    ring

theorem outer_piece (hT : RadialTraceStatement) (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ}
    (c : FracCellData k N) (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ)
    (hE : EnergySetting α c K B S I v G H u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) :
    quadFormValue (radialOuterForm K B I n C) u =
      K.testSupremum (fun p => p.1) (scaledPolyFn K.lineWeightFn (Q - 1) q)
        (fun p => (K.refR p.1 : ℂ) * radialField c.order n H C p) := by
  have hK := hE.box
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hQ : 1 ≤ Q := by have := hE.scalars.degrees; rw [hE.degHigh_eq]; omega
  have hrf : IntegrableOn (fun p => (p.1 : ℂ) * radialField c.order n H C p) K.rect := by
    have : (fun p : ℝ × ℝ => (p.1 : ℂ) * radialField c.order n H C p) =
        fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * ((p.1 : ℂ) * radialGradMode c.order n H a b p) := by
      funext p
      unfold radialField
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      ((hT K hK c.order v G H hE.field n a b).2.1).const_mul (C a b)
  refine (RadialOuter.outer_sup K hK Q q hQ _ _ u (fun i => ?_)
    (fun i => RadialOuter.outer_row hT α c K B S I v G H u hE n C i.1 i.2)).symm
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((K.refR p.1 : ℝ) : ℂ) * ((radialOuterTest K i.1 i.2 p : ℝ) : ℂ)) K.rect := by
    apply Continuous.continuousOn
    refine (Complex.continuous_ofReal.comp ((RadialProjInternal.refR_cont K).comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp ?_)
    unfold radialOuterTest monomial
    exact ((RadialProjInternal.lineWeight_cont K).comp continuous_fst).mul
      ((continuous_fst.pow _).mul (continuous_snd.pow _))
  refine (hrf.continuousOn_mul hc hcomp).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  ring

end RadialPieces

end Breakdown.CellCert.CellEnergy
