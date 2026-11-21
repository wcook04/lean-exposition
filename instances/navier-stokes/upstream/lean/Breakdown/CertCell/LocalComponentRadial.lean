import Breakdown.CertCell.LocalRadialPieces

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy

namespace Internal

section Outer

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} {m : ℕ}
  {K : CellBox} {B : CellBases} {I : LowIndex D modes Q q} {F : modes → Fin 3 → Fin 3 → ℝ × ℝ → ℂ}
  {T : modes → Fin 3 → Fin 3 → Fin 3 → ℝ × ℝ → ℂ} {u : D → ℂ}

theorem radialOuterFaceExpand (hK : IsCellBox K) (hB : IsCellBases K B) (hM : IsModeData m K B I F T u)
    (n : modes) (C : Fin 3 → Fin 3 → ℂ) (e : Fin 2) (he : e = 0 → K.r₁ ≠ 0) (l : Fin (q + 1)) :
    ∑ l' : Fin (q + 1), ((heightMoment K B l l' : ℝ) : ℂ) * rowApply (radialFaceComp I n C e l') u =
      ∑ a : Fin 3, ∑ b : Fin 3, C a b * radialFaceMoment K (F n a b) (T n a b 0) e (fun z => z ^ (l : ℕ)) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨co, hco⟩ := HeightProj.pow_span B.heightCoef (fun j => (hB.height_leading j).ne') q l
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
    simp_rw [integral_const_mul, hB.height_orthonormal]
    rw [Finset.sum_eq_single l']
    · simp
    · intro l'' _ hl''
      rw [if_neg]; · simp
      intro h; exact hl'' (Fin.ext h)
    · simp
  have hface : ∀ (a b : Fin 3) (t : ℝ → ℝ), Continuous t →
      ∀ (f : Fin (q + 1) → ℝ) (h : Fin (q + 1) → ℝ → ℝ), (∀ i, Continuous (h i)) → (∀ z, t z = ∑ i, f i * h i z) →
      radialFaceMoment K (F n a b) (T n a b 0) e t =
        ∑ i, (f i : ℂ) * radialFaceMoment K (F n a b) (T n a b 0) e (h i) := by
    intro a b t _ f h hh ht
    have hT' := hM.radial_trace n a b
    have hstrip : ∀ (c' o : ℝ), (c' = K.r₂ ∧ o = K.r₁) ∨ (c' = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) →
        radialStripMoment c' o K.z₁ K.z₂ (F n a b) (T n a b 0) t =
          ∑ i, (f i : ℂ) * radialStripMoment c' o K.z₁ K.z₂ (F n a b) (T n a b 0) (h i) := by
      intro c' o hco'
      have hrect : Set.Icc (min c' o) (max c' o) ×ˢ Set.Icc K.z₁ K.z₂ = K.rect := by
        rcases hco' with ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩
        · rw [min_eq_right hK.r_order.2.le, max_eq_left hK.r_order.2.le]; rfl
        · rw [min_eq_left hK.r_order.2.le, max_eq_right hK.r_order.2.le]; rfl
      have hX : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c' - o) : ℝ)) : ℂ) * F n a b p +
          (((p.1 - o) / (c' - o) : ℝ) : ℂ) * T n a b 0 p) K.rect := by
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
          F n a b p + (((p.1 - o) / (c' - o) : ℝ) : ℂ) * T n a b 0 p) * ((h i p.2 : ℝ) : ℂ))) K.rect := fun i =>
        (hX.mul_continuousOn ((Complex.continuous_ofReal.comp ((hh i).comp continuous_snd)).continuousOn)
          hcomp).const_mul _
      have e2 : ∀ p : ℝ × ℝ, ((((1 / (c' - o) : ℝ)) : ℂ) * F n a b p +
          (((p.1 - o) / (c' - o) : ℝ) : ℂ) * T n a b 0 p) * ((t p.2 : ℝ) : ℂ) =
          ∑ i, (f i : ℂ) * (((((1 / (c' - o) : ℝ)) : ℂ) * F n a b p +
          (((p.1 - o) / (c' - o) : ℝ) : ℂ) * T n a b 0 p) * ((h i p.2 : ℝ) : ℂ)) := by
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
      radialFaceMoment K (F n a b) (T n a b 0) e (B.heightPoly l') := by
    intro l'
    unfold radialFaceComp
    rw [RadialOuter.rowApply_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [RadialOuter.rowApply_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [RadialOuter.rowApply_mul, hM.radial_face n e a b l' he]
  simp_rw [hrowC, hmom, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hface a b (fun z => z ^ (l : ℕ)) (continuous_pow _) co (fun i => B.heightPoly i)
    (fun i => RadialProjInternal.heightPoly_cont B i) (fun z => hco z), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem radialOuterLowPair (hB : IsCellBases K B) (hM : IsModeData m K B I F T u) (n : modes)
    (C : Fin 3 → Fin 3 → ℂ) (φ₀ : ℝ × ℝ → ℝ) (hpoly : (fun p => (φ₀ p : ℂ)) ∈ polyFn Q Q) :
    rowApply (lowPairRow K B I n C (fun p => K.lineWeight p.1 * φ₀ p)) u =
      ∫ p in K.rect, modeSum C (F n) p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hlc := RadialProjInternal.lineWeight_cont K
  have hint : ∀ a b, IntegrableOn (F n a b) K.rect := fun a b => (hM.radial_trace n a b).1
  have hF : IntegrableOn (modeSum C (F n)) K.rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul (C a b)
  obtain ⟨e, he⟩ := HeightProj.span_mem B.radialCoef B.heightCoef (fun j => (hB.radial_leading j).ne')
    (fun j => (hB.height_leading j).ne') hpoly
  have hbc : ∀ j l : ℕ, Continuous (basisFn B j l) := fun j l =>
    ((RadialProjInternal.radialPoly_diff B j).continuous.comp continuous_fst).mul
      ((RadialProjInternal.heightPoly_cont B l).comp continuous_snd)
  have hort : ∀ j l j' l' : ℕ, ∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) * ((basisFn B j l p : ℝ) : ℂ) *
      ((basisFn B j' l' p : ℝ) : ℂ) = if j = j' ∧ l = l' then 1 else 0 := fun j l j' l' =>
    HeightProj.ortho2 B.radialCoef B.heightCoef K.r₁ K.r₂ K.z₁ K.z₂ K.lineWeight hB.radial_orthonormal
      hB.height_orthonormal j l j' l'
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
  have hFb : ∀ j l : ℕ, IntegrableOn (fun p => modeSum C (F n) p *
      (((K.lineWeight p.1 : ℝ) : ℂ) * ((basisFn B j l p : ℝ) : ℂ))) K.rect :=
    fun j l => hF.mul_continuousOn (((Complex.continuous_ofReal.comp (hlc.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (hbc j l))).continuousOn) hcomp
  have hcoef : ∀ j l : ℕ, B.coef K (modeSum C (F n)) j l =
      ∫ p in K.rect, modeSum C (F n) p * (((K.lineWeight p.1 : ℝ) : ℂ) * ((basisFn B j l p : ℝ) : ℂ)) := by
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
  simp_rw [hco, radialRowValue K B I F u hM.strain n C hint, hcoef]
  have hFe : ∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => modeSum C (F n) p * (((K.lineWeight p.1 : ℝ) : ℂ) *
        (e j l * ((basisFn B j l p : ℝ) : ℂ)))) K.rect := fun j l => by
    unfold IntegrableOn
    exact ((hFb j l).const_mul (e j l)).congr (Filter.Eventually.of_forall fun p => by ring)
  have e3 : ∀ p, modeSum C (F n) p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) =
      ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), modeSum C (F n) p * (((K.lineWeight p.1 : ℝ) : ℂ) *
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

theorem radialOuterRowValue (hK : IsCellBox K) (hB : IsCellBases K B) (hqQ : q + 1 ≤ Q)
    (hM : IsModeData m K B I F T u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) (j : Fin Q) (l : Fin (q + 1)) :
    rowApply (radialOuterRow K B I n C j l) u =
      ∫ p in K.rect, (p.1 : ℂ) * ((K.refR p.1 : ℂ) * modeSum C (fun a b => T n a b 0) p) *
        ((radialOuterTest K j l p : ℝ) : ℂ) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨ψ, φ₀, hψ, hψ0, hψ2, hψ1, hpt, hsl, hφψ, -, hpoly⟩ :=
    RadialOuter.outer_test K hK (Q := Q) j l (by have := j.2; omega) (by have := l.2; omega)
  have hrow : rowApply (radialOuterRow K B I n C j l) u =
      ((K.r₂ * K.lineWeight K.r₂ * K.r₂ ^ (j : ℕ) : ℝ) : ℂ) *
          ∑ l' : Fin (q + 1), ((heightMoment K B l l' : ℝ) : ℂ) * rowApply (radialFaceComp I n C 1 l') u
        + ((K.r₁ * K.lineWeight K.r₁ * K.r₁ ^ (j : ℕ) : ℝ) : ℂ) *
          ∑ l' : Fin (q + 1), ((heightMoment K B l l' : ℝ) : ℂ) * rowApply (radialFaceComp I n C 0 l') u
        + ∫ p in K.rect, modeSum C (F n) p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) := by
    unfold radialOuterRow
    rw [RadialOuter.rowApply_add, RadialOuter.rowApply_sum]
    simp only [RadialOuter.rowApply_mul, RadialOuter.rowApply_add]
    have hlp : (fun p => -radialSlope (fun p' => p'.1 * K.refR p'.1 * radialOuterTest K j l p') p) =
        fun p => K.lineWeight p.1 * φ₀ p := funext hsl
    rw [hlp, radialOuterLowPair hB hM n C φ₀ hpoly]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    · refine Finset.sum_congr rfl fun l' _ => ?_; ring
    · refine Finset.sum_congr rfl fun l' _ => ?_; ring
  have hface0 : ((K.r₁ * K.lineWeight K.r₁ * K.r₁ ^ (j : ℕ) : ℝ) : ℂ) *
        ∑ l' : Fin (q + 1), ((heightMoment K B l l' : ℝ) : ℂ) * rowApply (radialFaceComp I n C 0 l') u =
      ((K.r₁ * K.lineWeight K.r₁ * K.r₁ ^ (j : ℕ) : ℝ) : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, C a b *
        radialFaceMoment K (F n a b) (T n a b 0) 0 (fun z => z ^ (l : ℕ)) := by
    by_cases hr0 : K.r₁ = 0
    · simp [hr0]
    · rw [radialOuterFaceExpand hK hB hM n C 0 (fun _ => hr0) l]
  rw [hrow, hface0, radialOuterFaceExpand hK hB hM n C 1 (fun h => absurd h (by decide)) l]
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
  have i1 : ∀ a b, IntegrableOn (fun p => T n a b 0 p *
      ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ)) K.rect := by
    intro a b
    refine (((hM.radial_trace n a b).2.1).mul_continuousOn hc1 hcomp).congr_fun (fun p _ => ?_)
      (measurableSet_Icc.prod measurableSet_Icc)
    simp only []
    rw [hptc p]
    ring
  have i2 : ∀ a b, IntegrableOn (fun p => F n a b p *
      ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ)) K.rect := fun a b =>
    ((hM.radial_trace n a b).1).mul_continuousOn hc2 hcomp
  have key : ∀ a b, ∫ p in K.rect, T n a b 0 p * ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ) =
      ((ψ K.r₂ : ℝ) : ℂ) * radialFaceMoment K (F n a b) (T n a b 0) 1 (fun z => z ^ (l : ℕ))
        - ((ψ K.r₁ : ℝ) : ℂ) * radialFaceMoment K (F n a b) (T n a b 0) 0 (fun z => z ^ (l : ℕ))
        - ∫ p in K.rect, F n a b p * ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ) := by
    intro a b
    have h := (hM.radial_trace n a b).2.2.2 ψ (fun z => z ^ (l : ℕ)) hψ (continuous_pow _) (Or.inr hψ0)
    rw [integral_add (i1 a b) (i2 a b)] at h
    rw [← h]
    ring
  have j1 : ∀ a b, IntegrableOn (fun p => C a b * (T n a b 0 p *
      ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ))) K.rect := fun a b => (i1 a b).const_mul _
  have j2 : ∀ a b, IntegrableOn (fun p => C a b * (F n a b p *
      ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ))) K.rect := fun a b => (i2 a b).const_mul _
  have hR : ∫ p in K.rect, (p.1 : ℂ) * ((K.refR p.1 : ℂ) * modeSum C (fun a b => T n a b 0) p) *
      ((radialOuterTest K j l p : ℝ) : ℂ) = ∑ a : Fin 3, ∑ b : Fin 3, C a b * ∫ p in K.rect,
        T n a b 0 p * ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ) := by
    have e1 : ∀ p : ℝ × ℝ, (p.1 : ℂ) * ((K.refR p.1 : ℂ) * modeSum C (fun a b => T n a b 0) p) *
        ((radialOuterTest K j l p : ℝ) : ℂ) = ∑ a : Fin 3, ∑ b : Fin 3, C a b *
          (T n a b 0 p * ((ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ)) := by
      intro p
      rw [hptc p]
      unfold modeSum
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
  have hL : ∫ p in K.rect, modeSum C (F n) p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) =
      -∑ a : Fin 3, ∑ b : Fin 3, C a b * ∫ p in K.rect,
        F n a b p * ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ) := by
    have e2 : ∀ p : ℝ × ℝ, modeSum C (F n) p * ((K.lineWeight p.1 * φ₀ p : ℝ) : ℂ) =
        -∑ a : Fin 3, ∑ b : Fin 3, C a b *
          (F n a b p * ((deriv ψ p.1 * (fun z : ℝ => z ^ (l : ℕ)) p.2 : ℝ) : ℂ)) := by
      intro p
      rw [hφψ p]
      unfold modeSum
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

theorem radialOuterValue (hK : IsCellBox K) (hB : IsCellBases K B) (hq : 1 ≤ q) (hqQ : q + 1 ≤ Q)
    (hM : IsModeData m K B I F T u) (n : modes) (C : Fin 3 → Fin 3 → ℂ) :
    quadFormValue (radialOuterForm K B I n C) u =
      K.testSupremum (fun p => p.1) (scaledPolyFn K.lineWeightFn (Q - 1) q)
        (fun p => (K.refR p.1 : ℂ) * modeSum C (fun a b => T n a b 0) p) := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hQ : 1 ≤ Q := by omega
  have hrf : IntegrableOn (fun p => (p.1 : ℂ) * modeSum C (fun a b => T n a b 0) p) K.rect := by
    have : (fun p : ℝ × ℝ => (p.1 : ℂ) * modeSum C (fun a b => T n a b 0) p) =
        fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * ((p.1 : ℂ) * T n a b 0 p) := by
      funext p
      unfold modeSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      ((hM.radial_trace n a b).2.1).const_mul (C a b)
  refine (RadialOuter.outer_sup K hK Q q hQ _ _ u (fun i => ?_)
    (fun i => radialOuterRowValue hK hB hqQ hM n C i.1 i.2)).symm
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((K.refR p.1 : ℝ) : ℂ) * ((radialOuterTest K i.1 i.2 p : ℝ) : ℂ))
      K.rect := by
    apply Continuous.continuousOn
    refine (Complex.continuous_ofReal.comp ((RadialProjInternal.refR_cont K).comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp ?_)
    unfold radialOuterTest monomial
    exact ((RadialProjInternal.lineWeight_cont K).comp continuous_fst).mul
      ((continuous_fst.pow _).mul (continuous_snd.pow _))
  refine (hrf.continuousOn_mul hc hcomp).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  ring

end Outer

end Internal

open Classical in
theorem localComponentRadial : LocalComponentRadialStatement := by
  intro D _ _ modes Q q m K B I F T u hK hB hq hqQ hM n C
  rw [RadialForm.value_add, localRadialLowPieces m K B I F T u hK hB hq hqQ hM n C,
    Internal.radialOuterValue hK hB hq hqQ hM n C]
  unfold CellBox.radialEnergy
  rfl

end LocalField

end CertCell

end Breakdown
