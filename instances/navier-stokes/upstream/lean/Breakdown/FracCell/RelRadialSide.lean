import Breakdown.FracCell.StCoordsProof
import Breakdown.FracCell.ModeRadialWeak

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

namespace RadialSide.Internal

def polySpan (B : CellBases) (M : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ (Set.range (fun j : Fin M => B.radialPoly j))

theorem lineWeight_continuous (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs <;> fun_prop

theorem radialPoly_continuous (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  exact continuous_finsetSum _ (fun i _ => by fun_prop)

theorem heightPoly_continuous (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly
  exact continuous_finsetSum _ (fun i _ => by fun_prop)

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem pow_mem (K : CellBox) (B : CellBases) (hB : IsCellBases K B) :
    ∀ i M, i < M → (fun r : ℝ => r ^ i) ∈ polySpan B M := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro M hiM
  have hP : B.radialPoly i ∈ polySpan B M := Submodule.subset_span ⟨⟨i, hiM⟩, rfl⟩
  have hlow : (∑ k ∈ Finset.range i, B.radialCoef i k • fun r : ℝ => r ^ k) ∈ polySpan B M :=
    Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ (ih k (Finset.mem_range.1 hk) M
      (by have := Finset.mem_range.1 hk; omega)))
  have hdec : B.radialPoly i = B.radialCoef i i • (fun r : ℝ => r ^ i) +
      ∑ k ∈ Finset.range i, B.radialCoef i k • fun r : ℝ => r ^ k := by
    funext r
    simp only [CellBases.radialPoly, Finset.sum_range_succ, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hlead : B.radialCoef i i • (fun r : ℝ => r ^ i) ∈ polySpan B M := by
    have := Submodule.sub_mem _ hP hlow
    rwa [hdec, add_sub_cancel_right] at this
  have hc : B.radialCoef i i ≠ 0 := (hB.radial_leading i).ne'
  have := Submodule.smul_mem _ (B.radialCoef i i)⁻¹ hlead
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem expand (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (M : ℕ) (f g : ℝ → ℝ)
    (hf : f ∈ polySpan B M) (hg : ∀ r, g r = K.lineWeight r * f r) (r : ℝ) :
    ∑ j ∈ Finset.range M, (∫ s in Set.Icc K.r₁ K.r₂, g s * B.radialPoly j s) * B.radialPoly j r = f r := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hf
  have hfa : ∀ s, f s = ∑ j : Fin M, a j * B.radialPoly j s := by
    intro s
    rw [← ha]
    simp [Finset.sum_apply]
  have hco : ∀ k : Fin M, ∫ s in Set.Icc K.r₁ K.r₂, g s * B.radialPoly k s = a k := by
    intro k
    have h1 : (fun s => g s * B.radialPoly k s) =
        fun s => ∑ j : Fin M, a j * (K.lineWeight s * B.radialPoly j s * B.radialPoly k s) := by
      funext s
      rw [hg, hfa, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1, integral_finsetSum]
    · simp_rw [integral_const_mul, hB.radial_orthonormal]
      simp [Fin.val_inj]
    · intro j _
      have h1 := lineWeight_continuous K
      have h2 := radialPoly_continuous B j
      have h3 := radialPoly_continuous B k
      have hi : IntegrableOn (fun s => K.lineWeight s * B.radialPoly j s * B.radialPoly k s)
          (Set.Icc K.r₁ K.r₂) := Continuous.integrableOn_Icc (by fun_prop)
      exact hi.const_mul (a j)
  rw [Finset.sum_range (fun j => (∫ s in Set.Icc K.r₁ K.r₂, g s * B.radialPoly j s) * B.radialPoly j r)]
  simp_rw [hco]
  rw [hfa]


theorem intPair (K : CellBox) (F dF : ℝ × ℝ → ℂ) (hF : IntegrableOn F K.rect)
    (hdF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * dF p) K.rect) (u s f t : ℝ → ℝ)
    (hu : Continuous u) (hf : Continuous f) (ht : Continuous t) (hs : ∀ r, s r = K.lineWeight r * f r) :
    IntegrableOn (fun p : ℝ × ℝ => (((u p.1 : ℝ) : ℂ) * F p + ((s p.1 : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ))
      K.rect := by
  have h1 := hF.mul_continuousOn (g' := fun p : ℝ × ℝ => ((u p.1 : ℝ) : ℂ) * ((t p.2 : ℝ) : ℂ))
    (Continuous.continuousOn (by fun_prop)) (rect_compact K)
  have h2 := hdF.mul_continuousOn (g' := fun p : ℝ × ℝ => ((f p.1 : ℝ) : ℂ) * ((t p.2 : ℝ) : ℂ))
    (Continuous.continuousOn (by fun_prop)) (rect_compact K)
  have e : (fun p : ℝ × ℝ => (((u p.1 : ℝ) : ℂ) * F p + ((s p.1 : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ)) =
      fun x => F x * (((u x.1 : ℝ) : ℂ) * ((t x.2 : ℝ) : ℂ)) +
        ((K.lineWeight x.1 : ℝ) : ℂ) * dF x * (((f x.1 : ℝ) : ℂ) * ((t x.2 : ℝ) : ℂ)) := by
    funext p
    rw [hs]
    push_cast
    ring
  rw [e]
  exact h1.add h2

theorem coefSum (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (M : ℕ) (f g : ℝ → ℝ)
    (hf : f ∈ polySpan B M) (hg : ∀ r, g r = K.lineWeight r * f r) (Φ : ℝ × ℝ → ℂ)
    (hΦ : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Φ p) K.rect) (l : ℕ) :
    ∑ j ∈ Finset.range M, (((∫ r in Set.Icc K.r₁ K.r₂, g r * B.radialPoly j r : ℝ)) : ℂ) * B.coef K Φ j l =
      ∫ p in K.rect, ((g p.1 : ℝ) : ℂ) * Φ p * ((B.heightPoly l p.2 : ℝ) : ℂ) := by
  unfold CellBases.coef
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · congr 1
    funext p
    have e := expand K B hB M f g hf hg p.1
    calc ∑ j ∈ Finset.range M, (((∫ r in Set.Icc K.r₁ K.r₂, g r * B.radialPoly j r : ℝ)) : ℂ) *
          (((K.lineWeight p.1 : ℝ) : ℂ) * Φ p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = ((K.lineWeight p.1 : ℝ) : ℂ) * Φ p * ((((∑ j ∈ Finset.range M,
            (∫ r in Set.Icc K.r₁ K.r₂, g r * B.radialPoly j r) * B.radialPoly j p.1) * B.heightPoly l p.2 : ℝ)) : ℂ) := by
          rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          push_cast
          ring
      _ = ((g p.1 : ℝ) : ℂ) * Φ p * ((B.heightPoly l p.2 : ℝ) : ℂ) := by
          rw [e, hg p.1]
          push_cast
          ring
  · intro j _
    have hc : Continuous (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
      have := radialPoly_continuous B j
      have := heightPoly_continuous B l
      fun_prop
    have := hΦ.mul_continuousOn hc.continuousOn (rect_compact K)
    exact this.const_mul _

theorem key (K : CellBox) (hK : IsCellBox K) (B : CellBases) (hB : IsCellBases K B) (F dF : ℝ × ℝ → ℂ)
    (hF : IntegrableOn F K.rect) (hdF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * dF p) K.rect)
    (hbase : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 → ∀ t : ℝ → ℝ, Continuous t →
      ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * F p + ((ψ p.1 : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ) = 0)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ 1 β) (M₁ M₂ : ℕ) (f₁ f₂ : ℝ → ℝ) (hf₁ : f₁ ∈ polySpan B M₁)
    (hf₂ : f₂ ∈ polySpan B M₂) (hc₂ : Continuous f₂)
    (e₁ : ∀ r, deriv β r = K.lineWeight r * f₁ r) (e₂ : ∀ r, β r = K.lineWeight r * f₂ r) (l : ℕ) :
    ((β K.r₂ : ℝ) : ℂ) * radialStripMoment K.r₂ K.r₁ K.z₁ K.z₂ F dF (B.heightPoly l)
      - ((β K.r₁ : ℝ) : ℂ) * radialStripMoment K.r₁ K.r₂ K.z₁ K.z₂ F dF (B.heightPoly l)
      - ∑ j ∈ Finset.range M₁, (((∫ r in Set.Icc K.r₁ K.r₂, deriv β r * B.radialPoly j r : ℝ)) : ℂ) *
          B.coef K F j l
      - ∑ j ∈ Finset.range M₂, (((∫ r in Set.Icc K.r₁ K.r₂, β r * B.radialPoly j r : ℝ)) : ℂ) * B.coef K dF j l
      = 0 := by
  have hlt : K.r₁ < K.r₂ := hK.r_order.2
  have hne : K.r₂ - K.r₁ ≠ 0 := sub_ne_zero.2 hlt.ne'
  have hne' : K.r₁ - K.r₂ ≠ 0 := sub_ne_zero.2 hlt.ne
  have hw : Continuous K.lineWeight := lineWeight_continuous K
  have ht : Continuous (B.heightPoly l) := heightPoly_continuous B l
  have hβc : Continuous β := hβ.continuous
  have hdβc : Continuous (deriv β) := hβ.continuous_deriv le_rfl
  have hwF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect := by
    have := hF.mul_continuousOn (g' := fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ))
      (Continuous.continuousOn (by fun_prop)) (rect_compact K)
    have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p) =
        fun p => F p * ((K.lineWeight p.1 : ℝ) : ℂ) := by
      funext p
      ring
    rw [e]
    exact this
  rw [coefSum K B hB M₁ f₁ (deriv β) hf₁ e₁ F hwF l, coefSum K B hB M₂ f₂ β hf₂ e₂ dF hdF l]
  have hs1 : edgeSign K.r₂ K.r₁ = 1 := by simp [edgeSign, hlt]
  have hs0 : edgeSign K.r₁ K.r₂ = -1 := by simp [edgeSign, not_lt.2 hlt.le]
  have hset1 : Set.Icc (min K.r₂ K.r₁) (max K.r₂ K.r₁) ×ˢ Set.Icc K.z₁ K.z₂ = K.rect := by
    rw [min_eq_right hlt.le, max_eq_left hlt.le]
    rfl
  have hset0 : Set.Icc (min K.r₁ K.r₂) (max K.r₁ K.r₂) ×ˢ Set.Icc K.z₁ K.z₂ = K.rect := by
    rw [min_eq_left hlt.le, max_eq_right hlt.le]
    rfl
  unfold radialStripMoment
  rw [hs1, hs0, hset1, hset0]
  set ψ : ℝ → ℝ := fun r => β K.r₂ * ((r - K.r₁) / (K.r₂ - K.r₁)) + β K.r₁ * ((r - K.r₂) / (K.r₁ - K.r₂)) - β r
    with hψ
  have hψd : ∀ r, deriv ψ r = β K.r₂ * (1 / (K.r₂ - K.r₁)) + β K.r₁ * (1 / (K.r₁ - K.r₂)) - deriv β r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => (r - K.r₁) / (K.r₂ - K.r₁)) (1 / (K.r₂ - K.r₁)) r :=
      ((hasDerivAt_id' r).sub_const K.r₁).div_const _
    have h0 : HasDerivAt (fun r : ℝ => (r - K.r₂) / (K.r₁ - K.r₂)) (1 / (K.r₁ - K.r₂)) r :=
      ((hasDerivAt_id' r).sub_const K.r₂).div_const _
    have hb : HasDerivAt β (deriv β r) r := ((hβ.differentiable (by norm_num)) r).hasDerivAt
    exact (((h1.const_mul (β K.r₂)).add (h0.const_mul (β K.r₁))).sub hb).deriv
  have hψc : ContDiff ℝ 1 ψ := by
    rw [hψ]
    fun_prop
  have hψ1 : ψ K.r₁ = 0 := by
    simp only [hψ]
    rw [sub_self, zero_div, div_self hne']
    ring
  have hψ2 : ψ K.r₂ = 0 := by
    simp only [hψ]
    rw [sub_self, zero_div, div_self hne]
    ring
  have hC := hbase ψ hψc hψ1 hψ2 (B.heightPoly l) ht
  have hA := (intPair K F dF hF hdF (fun _ => 1 / (K.r₂ - K.r₁)) (fun r => (r - K.r₁) / (K.r₂ - K.r₁))
    (fun r => if K.r₁ = 0 then 1 / (K.r₂ - K.r₁) else (r - K.r₁) / (K.r₂ - K.r₁))
    (B.heightPoly l) continuous_const (by split_ifs <;> fun_prop) ht (fun r => by
      by_cases h0 : K.r₁ = 0
      · simp only [CellBox.lineWeight, h0, if_true]
        ring
      · simp [CellBox.lineWeight, h0])).const_mul ((β K.r₂ : ℝ) : ℂ)
  have hβ0 : K.r₁ = 0 → β K.r₁ = 0 := fun h0 => by
    rw [e₂, CellBox.lineWeight, if_pos h0, h0, zero_mul]
  have hB0 : IntegrableOn (fun p : ℝ × ℝ => ((β K.r₁ : ℝ) : ℂ) *
      (((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * F p + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * dF p) *
        ((B.heightPoly l p.2 : ℝ) : ℂ))) K.rect := by
    by_cases h0 : K.r₁ = 0
    · simp only [hβ0 h0, Complex.ofReal_zero, zero_mul]
      exact integrableOn_zero
    · exact (intPair K F dF hF hdF (fun _ => 1 / (K.r₁ - K.r₂)) (fun r => (r - K.r₂) / (K.r₁ - K.r₂))
        (fun r => (r - K.r₂) / (K.r₁ - K.r₂)) (B.heightPoly l) continuous_const (by fun_prop) ht
        (fun r => by simp [CellBox.lineWeight, h0])).const_mul _
  have hCi : IntegrableOn (fun p : ℝ × ℝ => ((deriv β p.1 : ℝ) : ℂ) * F p * ((B.heightPoly l p.2 : ℝ) : ℂ))
      K.rect := by
    have := intPair K F dF hF hdF (deriv β) (fun _ => 0) (fun _ => 0) (B.heightPoly l) hdβc continuous_const ht
      (fun r => by simp)
    have e : (fun p : ℝ × ℝ => ((deriv β p.1 : ℝ) : ℂ) * F p * ((B.heightPoly l p.2 : ℝ) : ℂ)) =
        fun p : ℝ × ℝ => (((deriv β p.1 : ℝ) : ℂ) * F p + (((fun _ => (0 : ℝ)) p.1 : ℝ) : ℂ) * dF p) *
          ((B.heightPoly l p.2 : ℝ) : ℂ) := by
      funext p
      simp
    rw [e]
    exact this
  have hDi : IntegrableOn (fun p : ℝ × ℝ => ((β p.1 : ℝ) : ℂ) * dF p * ((B.heightPoly l p.2 : ℝ) : ℂ))
      K.rect := by
    have := intPair K F dF hF hdF (fun _ => 0) β f₂ (B.heightPoly l) continuous_const hc₂ ht e₂
    have e : (fun p : ℝ × ℝ => ((β p.1 : ℝ) : ℂ) * dF p * ((B.heightPoly l p.2 : ℝ) : ℂ)) =
        fun p : ℝ × ℝ => ((((fun _ => (0 : ℝ)) p.1 : ℝ) : ℂ) * F p + ((β p.1 : ℝ) : ℂ) * dF p) *
          ((B.heightPoly l p.2 : ℝ) : ℂ) := by
      funext p
      simp
    rw [e]
    exact this
  refine Eq.trans ?_ hC
  rw [one_mul, neg_one_mul, mul_neg, sub_neg_eq_add, ← integral_const_mul, ← integral_const_mul,
    ← integral_add hA hB0]
  have hAB := hA.add hB0
  simp only [Pi.add_def] at hAB
  have hABC := hAB.sub hCi
  simp only [Pi.sub_def] at hABC
  rw [← integral_sub hAB hCi, ← integral_sub hABC hDi]
  congr 1
  funext p
  rw [hψd p.1]
  simp only [hψ]
  push_cast
  ring

theorem pair_sub {ι : Type*} [Fintype ι] (f g T : ι → ℂ) :
    ∑ d, (f - g) d * T d = ∑ d, f d * T d - ∑ d, g d * T d := by
  simp [sub_mul, Finset.sum_sub_distrib]

theorem pair_smul {ι : Type*} [Fintype ι] (c : ℂ) (f T : ι → ℂ) :
    ∑ d, (c • f) d * T d = c * ∑ d, f d * T d := by
  simp [Finset.mul_sum, mul_assoc]

theorem pair_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → ℂ) (T : ι → ℂ) :
    ∑ d, (∑ j ∈ s, f j) d * T d = ∑ j ∈ s, ∑ d, f j d * T d := by
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem pair_unit (L : CellLayout) (d₀ : L.Datum) (T : L.Datum → ℂ) : ∑ d, L.unitAt d₀ d * T d = T d₀ := by
  simp [CellLayout.unitAt, Pi.single_apply]

theorem pair_extra (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : L.modes) (e : Fin 4) (a : Fin 3) (d : ℕ)
    (hd : d < L.degCoef + 1) :
    ∑ u, L.extraAt n e a d u * L.trueData x u = L.extraValue n x e a d := by
  simp only [CellLayout.extraAt, dif_pos hd]
  exact pair_unit L _ _

theorem pair_velocity (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : L.modes) (a : Fin 3) (j l : ℕ)
    (hj : j ∈ Finset.range L.degCoef) (hl : l < L.degCoef) :
    ∑ u, L.velocityAt n a j l u * L.trueData x u = L.bases.coef L.box (L.velMode n x a) j l := by
  simp only [CellLayout.velocityAt, dif_pos (And.intro (Finset.mem_range.1 hj) hl)]
  exact pair_unit L _ _

theorem pair_strain (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : L.modes) (a b : Fin 3) (j l : ℕ)
    (hj : j ∈ Finset.range (L.degCoef + 1)) (hl : l < L.degCoef + 1) :
    ∑ u, L.strainAt n a b j l u * L.trueData x u = L.bases.coef L.box (L.gradModeOf n x a b) j l := by
  simp only [CellLayout.strainAt, dif_pos (And.intro (Finset.mem_range.1 hj) hl)]
  exact pair_unit L _ _

theorem extra_one (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : ℤ) (a : Fin 3) (d : ℕ) :
    L.extraValue n x 1 a d = radialStripMoment L.box.r₂ L.box.r₁ L.box.z₁ L.box.z₂ (L.velMode n x a)
      (L.gradModeOf n x a 0) (L.bases.heightPoly d) := by
  simp [CellLayout.extraValue, CellLayout.sideTest]

theorem extra_zero (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : ℤ) (a : Fin 3) (d : ℕ) :
    L.extraValue n x 0 a d = radialStripMoment L.box.r₁ L.box.r₂ L.box.z₁ L.box.z₂ (L.velMode n x a)
      (L.gradModeOf n x a 0) (L.bases.heightPoly d) := by
  simp [CellLayout.extraValue, CellLayout.sideTest]

end RadialSide.Internal

open RadialSide.Internal

theorem relRadialSide_of (h : ModeRadialWeakStatement) : RelRadialSideStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, a, l, i⟩ := ρ
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl]
  split_ifs with hax
  · simp
  · have hK : IsCellBox L.box := hL.box_eq ▸ hL.box_valid
    have hB : IsCellBases L.box L.bases := by
      rw [hL.box_eq, hL.bases_eq]
      exact hL.bases_valid
    have hx1 : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by
      rw [hL.order_eq]
      exact hx.1
    obtain ⟨hF, hdF, hbase⟩ := h L.box hK L.order x.1 x.2.1 x.2.2.1 hx1 n a
    have hl := l.isLt
    have hil := i.isLt
    simp only [pair_sub, pair_smul, pair_sum]
    rw [pair_extra L x n 1 a l (by omega), pair_extra L x n 0 a l (by omega), extra_one, extra_zero]
    have hv : ∀ (cf : ℕ → ℂ), ∑ j ∈ Finset.range L.degCoef, cf j * ∑ u, L.velocityAt n a j l u * L.trueData x u =
        ∑ j ∈ Finset.range L.degCoef, cf j * L.bases.coef L.box (L.velMode n x a) j l :=
      fun cf => Finset.sum_congr rfl (fun j hj => by rw [pair_velocity L x n a j l hj hl])
    have hs : ∀ (cf : ℕ → ℂ), ∑ j ∈ Finset.range (L.degCoef + 1),
        cf j * ∑ u, L.strainAt n a 0 j l u * L.trueData x u =
        ∑ j ∈ Finset.range (L.degCoef + 1), cf j * L.bases.coef L.box (L.gradModeOf n x a 0) j l :=
      fun cf => Finset.sum_congr rfl (fun j hj => by rw [pair_strain L x n a 0 j l hj (by omega)])
    rw [hv, hs]
    simp only [CellLayout.radialInt]
    by_cases h0 : L.box.r₁ = 0
    · have hi : (i : ℕ) < L.degCoef := by
        have : (i : ℕ) ≠ L.degCoef := fun hh => hax ⟨h0, hh⟩
        omega
      have hβ : L.radialBeta i = fun r => r ^ ((i : ℕ) + 2) := by
        funext r
        simp [CellLayout.radialBeta, h0]
      have hw : ∀ r, L.box.lineWeight r = r := fun r => by simp [CellBox.lineWeight, h0]
      have hm1 : (fun r : ℝ => ((i : ℝ) + 2) * r ^ (i : ℕ)) ∈ polySpan L.bases L.degCoef := by
        have := Submodule.smul_mem (polySpan L.bases L.degCoef) ((i : ℝ) + 2)
          (pow_mem L.box L.bases hB i L.degCoef hi)
        convert this using 1
        funext r
        simp [smul_eq_mul]
      exact key L.box hK L.bases hB (L.velMode n x a) (L.gradModeOf n x a 0) hF hdF hbase
        (L.radialBeta i) (by rw [hβ]; fun_prop) L.degCoef (L.degCoef + 1)
        (fun r => ((i : ℝ) + 2) * r ^ (i : ℕ)) (fun r => r ^ ((i : ℕ) + 1))
        hm1 (pow_mem L.box L.bases hB _ _ (by omega)) (by fun_prop)
        (fun r => by
          rw [hβ, hw, (hasDerivAt_pow ((i : ℕ) + 2) r).deriv, show (i : ℕ) + 2 - 1 = (i : ℕ) + 1 by omega]
          push_cast
          ring)
        (fun r => by
          rw [hβ, hw]
          ring) l
    · have hβ : L.radialBeta i = fun r => r ^ (i : ℕ) := by
        funext r
        simp [CellLayout.radialBeta, h0]
      have hw : ∀ r, L.box.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h0]
      have hm1 : (fun r : ℝ => (i : ℝ) * r ^ ((i : ℕ) - 1)) ∈ polySpan L.bases L.degCoef := by
        have := Submodule.smul_mem (polySpan L.bases L.degCoef) (i : ℝ)
          (pow_mem L.box L.bases hB ((i : ℕ) - 1) L.degCoef (by omega))
        convert this using 1
        funext r
        simp [smul_eq_mul]
      exact key L.box hK L.bases hB (L.velMode n x a) (L.gradModeOf n x a 0) hF hdF hbase
        (L.radialBeta i) (by rw [hβ]; fun_prop) L.degCoef (L.degCoef + 1)
        (fun r => (i : ℝ) * r ^ ((i : ℕ) - 1)) (fun r => r ^ (i : ℕ))
        hm1 (pow_mem L.box L.bases hB _ _ (by omega)) (by fun_prop)
        (fun r => by
          rw [hβ, hw, (hasDerivAt_pow (i : ℕ) r).deriv]
          ring)
        (fun r => by
          rw [hβ, hw]
          ring) l


end Breakdown.CellCert.CellFormula
