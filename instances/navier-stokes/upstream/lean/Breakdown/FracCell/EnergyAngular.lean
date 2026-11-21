import Breakdown.FracCell.StEnergyProof
import Breakdown.FracCell.StAngularMode

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

private lemma formOfRows_eq {D ι : Type} [Fintype D] [DecidableEq D] [Fintype ι] (rows : ι → D → ℂ)
    (M : Matrix ι ι ℂ) : formOfRows rows M = (Matrix.of rows)ᴴ * M * Matrix.of rows := by
  ext d d'
  simp only [formOfRows, mul_apply, conjTranspose_apply, of_apply, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]

private lemma quad_formOfRows {D ι : Type} [Fintype D] [DecidableEq D] [Fintype ι] (rows : ι → D → ℂ)
    (M : Matrix ι ι ℂ) (u : D → ℂ) :
    quadFormValue (formOfRows rows M) u =
      (star (fun i => rowApply (rows i) u) ⬝ᵥ (M *ᵥ fun i => rowApply (rows i) u)).re := by
  have hx : (fun i => rowApply (rows i) u) = Matrix.of rows *ᵥ u := by
    ext i; simp [rowApply, mulVec, dotProduct]
  unfold quadFormValue
  rw [formOfRows_eq, hx, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

private lemma conj_swap {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (a b : ι → ℂ) :
    star (star a ⬝ᵥ (G *ᵥ b)) = star b ⬝ᵥ (G *ᵥ a) := by
  rw [star_dotProduct, star_star, star_mulVec, hG.eq, ← dotProduct_mulVec, dotProduct_comm]

private lemma conj_re {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (a : ι → ℂ) :
    ((star a ⬝ᵥ (G *ᵥ a)).re : ℂ) = star a ⬝ᵥ (G *ᵥ a) := by
  have h := conj_swap hG a a
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp; linarith

private lemma pd_re_pos {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) {a : ι → ℂ} (ha : a ≠ 0) :
    0 < (star a ⬝ᵥ (G *ᵥ a)).re := by
  have := hG.dotProduct_mulVec_pos ha
  exact (Complex.pos_iff.mp this).1

private lemma sesq_bound {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) (c z : ι → ℂ) :
    ‖star c ⬝ᵥ (G *ᵥ z)‖ ^ 2 ≤ (star c ⬝ᵥ (G *ᵥ c)).re * (star z ⬝ᵥ (G *ᵥ z)).re := by
  by_cases hz : z = 0
  · subst hz; simp
  have hs := pd_re_pos hG hz
  set s := (star z ⬝ᵥ (G *ᵥ z)).re with hs_def
  set β := star c ⬝ᵥ (G *ᵥ z) with hβ
  set l : ℂ := (starRingEnd ℂ) β / (s : ℂ) with hl
  have hpsd : 0 ≤ (star (c - l • z) ⬝ᵥ (G *ᵥ (c - l • z))).re := by
    by_cases h0 : c - l • z = 0
    · rw [h0]; simp
    · exact (pd_re_pos hG h0).le
  have hzc : star z ⬝ᵥ (G *ᵥ c) = (starRingEnd ℂ) β := by
    rw [hβ, ← Complex.star_def, conj_swap hG.isHermitian]
  have hzz : star z ⬝ᵥ (G *ᵥ z) = (s : ℂ) := (conj_re hG.isHermitian z).symm
  have hexp : star (c - l • z) ⬝ᵥ (G *ᵥ (c - l • z)) =
      star c ⬝ᵥ (G *ᵥ c) - l * β - (starRingEnd ℂ) l * (starRingEnd ℂ) β
        + (starRingEnd ℂ) l * l * (s : ℂ) := by
    rw [mulVec_sub, mulVec_smul, star_sub, star_smul, dotProduct_sub, sub_dotProduct, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul, hzc, hzz, ← hβ]
    simp only [smul_eq_mul, Complex.star_def]
    ring
  rw [hexp] at hpsd
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have key : l * β = ((‖β‖ ^ 2 / s : ℝ) : ℂ) := by
    rw [hl, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have key2 : (starRingEnd ℂ) l * (starRingEnd ℂ) β = ((‖β‖ ^ 2 / s : ℝ) : ℂ) := by
    rw [← map_mul, key, Complex.conj_ofReal]
  have key3 : (starRingEnd ℂ) l * l * (s : ℂ) = ((‖β‖ ^ 2 / s : ℝ) : ℂ) := by
    rw [mul_comm ((starRingEnd ℂ) l) l, mul_assoc, hl]
    rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    field_simp
    rw [mul_comm _ β, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; field_simp
  rw [key, key2, key3] at hpsd
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hpsd
  have : ‖β‖ ^ 2 / s ≤ (star c ⬝ᵥ (G *ᵥ c)).re := by linarith
  rw [div_le_iff₀ hs] at this
  linarith

private lemma sup_identity {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) (x : ι → ℂ) :
    sSup {t : ℝ | ∃ c : ι → ℂ, 0 < (star c ⬝ᵥ (G *ᵥ c)).re ∧
      t = ‖star c ⬝ᵥ x‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re} = (star x ⬝ᵥ (G⁻¹ *ᵥ x)).re := by
  have hU : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  set z := G⁻¹ *ᵥ x with hz
  have hGz : G *ᵥ z = x := by rw [hz, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hR : star x ⬝ᵥ (G⁻¹ *ᵥ x) = star z ⬝ᵥ (G *ᵥ z) := by
    rw [← hz]
    conv_lhs => rw [← hGz]
    rw [star_mulVec, hG.isHermitian.eq, ← dotProduct_mulVec]
  rw [hR]
  have hub : ∀ t ∈ {t : ℝ | ∃ c : ι → ℂ, 0 < (star c ⬝ᵥ (G *ᵥ c)).re ∧
      t = ‖star c ⬝ᵥ x‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re}, t ≤ (star z ⬝ᵥ (G *ᵥ z)).re := by
    rintro t ⟨c, hc, rfl⟩
    rw [div_le_iff₀ hc, ← hGz, mul_comm]
    exact sesq_bound hG c z
  by_cases h0 : z = 0
  · have hz0 : (star z ⬝ᵥ (G *ᵥ z)).re = 0 := by rw [h0]; simp
    rw [hz0]
    apply le_antisymm
    · exact Real.sSup_nonpos (fun t ht => hz0 ▸ hub t ht)
    · apply Real.sSup_nonneg
      rintro t ⟨c, hc, rfl⟩
      positivity
  · have hpos := pd_re_pos hG h0
    apply IsGreatest.csSup_eq
    refine ⟨⟨z, hpos, ?_⟩, hub⟩
    rw [← hGz, ← conj_re hG.isHermitian z, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp only [Complex.ofReal_re]
    field_simp


private lemma quad_add {D : Type} [Fintype D] (X Y : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (X + Y) u = quadFormValue X u + quadFormValue Y u := by
  unfold quadFormValue
  rw [add_mulVec, dotProduct_add, Complex.add_re]

private lemma supremum_eq_of (K : CellBox) (μ : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ → ℂ)) (F : ℝ × ℝ → ℂ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (hG : G.PosDef) (x : ι → ℂ)
    (h1 : ∀ P ∈ V, ∃ c : ι → ℂ, ((K.normSqOn μ P : ℝ) : ℂ) = star c ⬝ᵥ (G *ᵥ c) ∧
      K.pairOn μ F P = star c ⬝ᵥ x)
    (h2 : ∀ c : ι → ℂ, ∃ P ∈ V, ((K.normSqOn μ P : ℝ) : ℂ) = star c ⬝ᵥ (G *ᵥ c) ∧
      K.pairOn μ F P = star c ⬝ᵥ x) :
    K.testSupremum μ V F = (star x ⬝ᵥ (G⁻¹ *ᵥ x)).re := by
  rw [← sup_identity hG x]
  unfold CellBox.testSupremum
  congr 1
  ext t
  constructor
  · rintro ⟨P, hP, hpos, rfl⟩
    obtain ⟨c, hn, hp⟩ := h1 P hP
    have hre : K.normSqOn μ P = (star c ⬝ᵥ (G *ᵥ c)).re := by rw [← hn, Complex.ofReal_re]
    exact ⟨c, hre ▸ hpos, by rw [hp, hre]⟩
  · rintro ⟨c, hpos, rfl⟩
    obtain ⟨P, hP, hn, hp⟩ := h2 c
    have hre : K.normSqOn μ P = (star c ⬝ᵥ (G *ᵥ c)).re := by rw [← hn, Complex.ofReal_re]
    exact ⟨P, hP, hre ▸ hpos, by rw [hp, hre]⟩

private lemma param_eq (K : CellBox) (μ : ℝ × ℝ → ℝ) (F : ℝ × ℝ → ℂ) {ι : Type} [Fintype ι]
    (Ps : ι → ℝ × ℝ → ℝ)
    (hF : ∀ i, IntegrableOn (fun p => (μ p : ℂ) * F p * (Ps i p : ℂ)) K.rect)
    (hP : ∀ i i', IntegrableOn (fun p => μ p * Ps i p * Ps i' p) K.rect) (c : ι → ℂ) :
    ((K.normSqOn μ (fun p => ∑ i, c i * (Ps i p : ℂ)) : ℝ) : ℂ) = star c ⬝ᵥ (testInnerMatrix K μ Ps *ᵥ c) ∧
    K.pairOn μ F (fun p => ∑ i, c i * (Ps i p : ℂ)) =
      star c ⬝ᵥ (fun i => ∫ p in K.rect, (μ p : ℂ) * F p * (Ps i p : ℂ)) := by
  constructor
  · unfold CellBox.normSqOn testInnerMatrix rectIntegral
    rw [← integral_complex_ofReal]
    have hpt : ∀ p : ℝ × ℝ, (((μ p * ‖∑ i, c i * (Ps i p : ℂ)‖ ^ 2 : ℝ)) : ℂ) =
        ∑ i, ∑ i', (starRingEnd ℂ) (c i) * (((μ p * Ps i p * Ps i' p : ℝ)) : ℂ) * c i' := by
      intro p
      rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, map_sum,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      simp only [map_mul, Complex.conj_ofReal]
      push_cast; ring
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum _ (fun i' _ => ?_)]
      · refine Finset.sum_congr rfl (fun i' _ => ?_)
        rw [integral_mul_const, integral_const_mul, integral_complex_ofReal]; ring
      · exact (((hP i i').ofReal).const_mul _).mul_const _
    · refine integrable_finsetSum _ (fun i' _ => ?_)
      exact (((hP i i').ofReal).const_mul _).mul_const _
  · unfold CellBox.pairOn
    have hpt : ∀ p : ℝ × ℝ, (μ p : ℂ) * F p * (starRingEnd ℂ) (∑ i, c i * (Ps i p : ℂ)) =
        ∑ i, (starRingEnd ℂ) (c i) * ((μ p : ℂ) * F p * (Ps i p : ℂ)) := by
      intro p
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [map_mul, Complex.conj_ofReal]; ring
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun i _ => (hF i).const_mul _)]
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul]


private lemma poly_cont (B : CellBases) (j l : ℕ) : Continuous (fun p : ℝ × ℝ => basisFn B j l p) := by
  unfold basisFn CellBases.radialPoly CellBases.heightPoly
  fun_prop

private lemma rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

private lemma rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

private lemma coef_strain (K : CellBox) (B : CellBases) (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space))
    (C' : Fin 3 → Fin 3 → ℂ)
    (hint : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p) K.rect) (j l : ℕ) :
    B.coef K (strainField m n G C') j l = ∑ a, ∑ b, C' a b * B.coef K (gradMode m n G a b) j l := by
  have hI : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := fun a b =>
    (hint a b).mul_continuousOn (Complex.continuous_ofReal.comp (poly_cont B j l)).continuousOn (rect_compact K)
  unfold CellBases.coef strainField
  have hpt : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * (∑ a, ∑ b, C' a b * gradMode m n G a b p) *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) = ∑ a, ∑ b, C' a b * ((K.lineWeight p.1 : ℂ) *
        gradMode m n G a b p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
    intro p
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hI a b).const_mul _))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [integral_finsetSum _ (fun b _ => (hI a b).const_mul _)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [integral_const_mul]

private lemma lowRow_apply {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (n : modes) (C' : Fin 3 → Fin 3 → ℂ) (j l : Fin (Q + 1)) (u : D → ℂ) :
    rowApply (lowRow I n C' j l) u = ∑ a, ∑ b, C' a b * u (I.strainSlot n a b j l) := by
  simp only [rowApply, lowRow, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [mul_assoc]

private lemma lowPair_apply {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (n : modes) (C' : Fin 3 → Fin 3 → ℂ)
    (φ : ℝ × ℝ → ℝ) (u : D → ℂ) :
    rowApply (lowPairRow K B I n C' φ) u = ∑ jl : Fin (Q + 1) × Fin (Q + 1),
      ((rectIntegral K (fun p => basisFn B jl.1 jl.2 p * φ p) : ℝ) : ℂ) * rowApply (lowRow I n C' jl.1 jl.2) u := by
  simp only [rowApply, lowPairRow, Finset.sum_mul, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring

private lemma orth2 (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (j l j' l' : ℕ) :
    ∫ p in K.rect, K.lineWeight p.1 * basisFn B j' l' p * basisFn B j l p =
      if j' = j ∧ l' = l then 1 else 0 := by
  have : ∫ p in K.rect, K.lineWeight p.1 * basisFn B j' l' p * basisFn B j l p =
      ∫ p in K.rect, (K.lineWeight p.1 * B.radialPoly j' p.1 * B.radialPoly j p.1) *
        (B.heightPoly l' p.2 * B.heightPoly l p.2) := by
    congr 1; funext p; unfold basisFn; ring
  rw [this]
  unfold CellBox.rect
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_mul (fun r => K.lineWeight r * B.radialPoly j' r * B.radialPoly j r)
      (fun z => B.heightPoly l' z * B.heightPoly l z), hB.radial_orthonormal, hB.height_orthonormal]
  by_cases h1 : j' = j <;> by_cases h2 : l' = l <;> simp [h1, h2]

private lemma expand (K : CellBox) (B : CellBases) (hK : IsCellBox K) (hB : IsCellBases K B) (Q : ℕ)
    (g : ℝ × ℝ → ℂ) (hg : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * g p) K.rect) (ψ : ℝ × ℝ → ℝ)
    (hψ : ψ ∈ Submodule.span ℝ (Set.range (fun jl : Fin (Q + 1) × Fin (Q + 1) => basisFn B jl.1 jl.2))) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * g p * (ψ p : ℂ) =
      ∑ jl : Fin (Q + 1) × Fin (Q + 1),
        ((∫ p in K.rect, K.lineWeight p.1 * ψ p * basisFn B jl.1 jl.2 p : ℝ) : ℂ) * B.coef K g jl.1 jl.2 := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hψ
  have hwc : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1) := by
    unfold CellBox.lineWeight; split_ifs <;> fun_prop
  have hb : ∀ jl : Fin (Q + 1) × Fin (Q + 1), IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * g p *
      ((basisFn B jl.1 jl.2 p : ℝ) : ℂ)) K.rect := fun jl =>
    hg.mul_continuousOn (Complex.continuous_ofReal.comp (poly_cont B _ _)).continuousOn (rect_compact K)
  have hpt : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * g p *
      (((∑ jl, d jl • fun p => basisFn B jl.1 jl.2 p) p : ℝ) : ℂ) =
      ∑ jl : Fin (Q + 1) × Fin (Q + 1), (d jl : ℂ) * ((K.lineWeight p.1 : ℂ) * g p * ((basisFn B jl.1 jl.2 p : ℝ) : ℂ)) := by
    intro p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun jl _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun jl _ => (hb jl).const_mul _)]
  refine Finset.sum_congr rfl fun jl _ => ?_
  rw [integral_const_mul]
  have hpt2 : ∀ p : ℝ × ℝ, K.lineWeight p.1 * (∑ jl', d jl' • fun p => basisFn B jl'.1 jl'.2 p) p *
      basisFn B jl.1 jl.2 p = ∑ jl' : Fin (Q + 1) × Fin (Q + 1),
        d jl' * (K.lineWeight p.1 * basisFn B jl'.1 jl'.2 p * basisFn B jl.1 jl.2 p) := by
    intro p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun jl' _ => by ring
  simp_rw [hpt2]
  rw [integral_finsetSum _ (fun jl' _ => ?_)]
  · have : ∀ jl' : Fin (Q + 1) × Fin (Q + 1), ((jl'.1 : ℕ) = jl.1 ∧ (jl'.2 : ℕ) = jl.2) ↔ jl' = jl := by
      intro jl'
      rw [Fin.val_inj, Fin.val_inj, Prod.ext_iff]
    simp only [integral_const_mul, orth2 K B hB, this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  · exact ((ContinuousOn.integrableOn_compact (rect_compact K)
      ((hwc.mul (poly_cont B _ _)).mul (poly_cont B _ _)).continuousOn)).const_mul _

private lemma pow_span (P : ℕ → ℝ → ℝ) (a : ℕ → ℕ → ℝ)
    (hP : ∀ j r, P j r = ∑ i ∈ Finset.range (j + 1), a j i * r ^ i) (ha : ∀ j, a j j ≠ 0) (Q : ℕ) :
    ∀ i, i ≤ Q → (fun r : ℝ => r ^ i) ∈ Submodule.span ℝ (Set.range (fun j : Fin (Q + 1) => P j)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hPi : (P i) ∈ Submodule.span ℝ (Set.range (fun j : Fin (Q + 1) => P j)) :=
      Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩
    have heq : (fun r : ℝ => r ^ i) =
        (a i i)⁻¹ • (P i - ∑ t ∈ Finset.range i, a i t • (fun r : ℝ => r ^ t)) := by
      funext r
      simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, hP, Finset.sum_range_succ]
      rw [add_sub_cancel_left, inv_mul_cancel_left₀ (ha i)]
    rw [heq]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ hPi (Submodule.sum_mem _ fun t ht =>
      Submodule.smul_mem _ _ (ih t (Finset.mem_range.mp ht) ?_)))
    have := Finset.mem_range.mp ht
    omega

private lemma mono_span (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q i k : ℕ) (hi : i ≤ Q)
    (hk : k ≤ Q) :
    monomial i k ∈ Submodule.span ℝ (Set.range (fun jl : Fin (Q + 1) × Fin (Q + 1) => basisFn B jl.1 jl.2)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
    (pow_span (fun j r => B.radialPoly j r) B.radialCoef (fun j r => rfl) (fun j => (hB.radial_leading j).ne') Q i hi)
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
    (pow_span (fun j r => B.heightPoly j r) B.heightCoef (fun j r => rfl) (fun j => (hB.height_leading j).ne') Q k hk)
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨fun jl => c jl.1 * d jl.2, ?_⟩
  funext p
  have h1 := congrFun hc p.1
  have h2 := congrFun hd p.2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  rw [Fintype.sum_prod_type]
  simp only [monomial, basisFn]
  rw [← h1, ← h2, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring


private lemma poly1_zero {d : ℕ} (s : Fin d → ℂ) {a b : ℝ} (hab : a < b)
    (h : ∀ r ∈ Set.Ioo a b, ∑ j, s j * (r : ℂ) ^ (j : ℕ) = 0) : s = 0 := by
  classical
  set P : Polynomial ℂ := ∑ j : Fin d, Polynomial.C (s j) * Polynomial.X ^ (j : ℕ) with hP
  have hev : ∀ r : ℝ, P.eval (r : ℂ) = ∑ j, s j * (r : ℂ) ^ (j : ℕ) := by
    intro r
    rw [hP, Polynomial.eval_finsetSum]
    simp
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ ((Set.Ioo_infinite hab).image
      (fun x _ y _ hxy => Complex.ofReal_injective hxy))
    rintro _ ⟨r, hr, rfl⟩
    show P.IsRoot (r : ℂ)
    rw [Polynomial.IsRoot, hev]
    exact h r hr
  funext j
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff (j : ℕ)) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single j (fun j' _ hj' => if_neg (fun h => hj' (Fin.ext h.symm)))
    (fun h => absurd (Finset.mem_univ j) h)] at hc
  simpa using hc

private lemma poly2_zero {d1 d2 : ℕ} (c : Fin d1 × Fin d2 → ℂ) {a b e f : ℝ} (hab : a < b) (hef : e < f)
    (h : ∀ r ∈ Set.Ioo a b, ∀ z ∈ Set.Ioo e f, ∑ i, c i * (r : ℂ) ^ (i.1 : ℕ) * (z : ℂ) ^ (i.2 : ℕ) = 0) :
    c = 0 := by
  have h1 : ∀ z ∈ Set.Ioo e f, ∀ j, ∑ l, c (j, l) * (z : ℂ) ^ (l : ℕ) = 0 := by
    intro z hz
    have := poly1_zero (fun j => ∑ l, c (j, l) * (z : ℂ) ^ (l : ℕ)) hab (fun r hr => by
      rw [← h r hr z hz, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => by ring)
    exact fun j => congrFun this j
  funext i
  have := poly1_zero (fun l => c (i.1, l)) hef (fun z hz => h1 z hz i.1)
  exact congrFun this i.2

private lemma pairing_pd (K : CellBox) (hK : IsCellBox K) (μ : ℝ × ℝ → ℝ) (hμc : ContinuousOn μ K.rect)
    (hμ0 : ∀ p ∈ K.rect, 0 ≤ μ p) (hμU : ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, 0 < μ p)
    (d1 d2 : ℕ) :
    (testInnerMatrix K μ (fun jl : Fin d1 × Fin d2 => angularTest jl.1 jl.2)).PosDef := by
  classical
  set Ps := fun jl : Fin d1 × Fin d2 => angularTest jl.1 jl.2 with hPs
  have hPc : ∀ i, Continuous (Ps i) := fun i => by
    show Continuous (angularTest i.1 i.2)
    unfold angularTest monomial
    fun_prop
  have hint : ∀ i i', IntegrableOn (fun p => μ p * Ps i p * Ps i' p) K.rect := fun i i' =>
    ContinuousOn.integrableOn_compact (rect_compact K) ((hμc.mul (hPc i).continuousOn).mul (hPc i').continuousOn)
  rw [posDef_iff_dotProduct_mulVec]
  constructor
  · ext i i'
    simp only [conjTranspose_apply, testInnerMatrix, RCLike.star_def, Complex.conj_ofReal, rectIntegral]
    congr 2
    funext p
    ring
  · intro x hx
    have h0F : ∀ i, IntegrableOn (fun p => (μ p : ℂ) * (fun _ => (0 : ℂ)) p * (Ps i p : ℂ)) K.rect := by
      intro i; simp
    rw [← (param_eq K μ (fun _ => 0) Ps h0F hint x).1, Complex.zero_lt_real]
    set P := fun p : ℝ × ℝ => ∑ i, x i * (Ps i p : ℂ) with hP
    have hPcont : Continuous P := by
      simp only [hP]; exact continuous_finsetSum _ fun i _ => continuous_const.mul
        (Complex.continuous_ofReal.comp (hPc i))
    have hfc : ContinuousOn (fun p => μ p * ‖P p‖ ^ 2) K.rect :=
      hμc.mul (hPcont.norm.pow 2).continuousOn
    have hnn : 0 ≤ᵐ[volume.restrict K.rect] fun p => μ p * ‖P p‖ ^ 2 := by
      refine (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
      exact mul_nonneg (hμ0 p hp) (by positivity)
    have hI : Integrable (fun p => μ p * ‖P p‖ ^ 2) (volume.restrict K.rect) :=
      hfc.integrableOn_compact (rect_compact K)
    unfold CellBox.normSqOn
    rcases (integral_nonneg_of_ae hnn).lt_or_eq with hlt | heq
    · exact hlt
    exfalso
    have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hI).1 heq.symm
    have hUr : Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ ⊆ K.rect :=
      Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
    have hzU := ae_restrict_of_ae_restrict_of_subset hUr hz
    have hEq := Measure.eqOn_open_of_ae_eq hzU (isOpen_Ioo.prod isOpen_Ioo) (hfc.mono hUr) continuousOn_const
    apply hx
    refine poly2_zero x hK.r_order.2 hK.z_order.2 (fun r hr z hz' => ?_)
    have hpU : (r, z) ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := ⟨hr, hz'⟩
    have h1 := hEq hpU
    simp only [Pi.zero_apply] at h1
    have hPz : P (r, z) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h (hμU _ hpU).ne'
      · exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (hK.r_order.1.trans_lt hr.1).ne'
    have : P (r, z) = (r : ℂ) * ∑ i, x i * (r : ℂ) ^ (i.1 : ℕ) * (z : ℂ) ^ (i.2 : ℕ) := by
      simp only [hP, hPs, angularTest, monomial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [this] at hPz
    exact (mul_eq_zero.1 hPz).resolve_left hr0

private lemma pairing_axis_pd (K : CellBox) (hK : IsCellBox K) (h0 : K.r₁ = 0) (Q : ℕ) :
    (testInnerMatrix K (fun p => p.1) (fun jl : Fin (Q + 1) × Fin (Q + 1) => angularTest jl.1 jl.2)).PosDef :=
  pairing_pd K hK _ continuous_fst.continuousOn (fun p hp => h0 ▸ hp.1.1) (fun p hp => h0 ▸ hp.1.1) _ _

private lemma pairing_off_pd (K : CellBox) (hK : IsCellBox K) (h0 : K.r₁ ≠ 0) (Q : ℕ) :
    (testInnerMatrix K (angularOffWeight K) (fun jl : Fin Q × Fin (Q + 1) => angularTest jl.1 jl.2)).PosDef := by
  have hr1 : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
  have hr2 : 0 < K.r₂ := hr1.trans hK.r_order.2
  refine pairing_pd K hK _ ?_ ?_ ?_ _ _
  · unfold angularOffWeight
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro p hp
    exact mul_ne_zero (hr1.trans_le hp.1.1).ne' hr2.ne'
  · intro p hp
    unfold angularOffWeight
    exact div_nonneg (by linarith [hp.1.2]) (mul_nonneg (hr1.trans_le hp.1.1).le hr2.le)
  · intro p hp
    unfold angularOffWeight
    exact div_pos (by linarith [hp.1.2]) (mul_pos (hr1.trans hp.1.1) hr2)


private lemma poly_mem {d : ℕ} (P : ℝ × ℝ → ℂ) :
    P ∈ polyFn d d ↔ ∃ c : Fin (d + 1) × Fin (d + 1) → ℂ,
      P = fun p => ∑ k, c k * ((monomial k.1 k.2 p : ℝ) : ℂ) := by
  constructor
  · rintro ⟨c', hc'⟩
    refine ⟨fun k => c' k.1 k.2, ?_⟩
    funext p
    rw [hc' p, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [monomial]; push_cast; ring
  · rintro ⟨c, rfl⟩
    refine ⟨fun j l => c (j, l), fun p => ?_⟩
    dsimp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [monomial]; push_cast; ring

private lemma basis_in_mono (B : CellBases) (Q : ℕ) (i : Fin (Q + 1) × Fin (Q + 1)) :
    basisFn B i.1 i.2 ∈ Submodule.span ℝ (Set.range (fun k : Fin (Q + 1) × Fin (Q + 1) => monomial k.1 k.2)) := by
  have heq : basisFn B i.1 i.2 = ∑ a ∈ Finset.range (i.1 + 1), ∑ b ∈ Finset.range (i.2 + 1),
      (B.radialCoef i.1 a * B.heightCoef i.2 b) • monomial a b := by
    funext p
    simp only [basisFn, CellBases.radialPoly, CellBases.heightPoly, Finset.sum_mul_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, monomial]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [heq]
  refine Submodule.sum_mem _ fun a ha => Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ ?_
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  exact Submodule.subset_span ⟨(⟨a, by omega⟩, ⟨b, by omega⟩), rfl⟩

private lemma proj_norm (K : CellBox) (B : CellBases) (hK : IsCellBox K) (hB : IsCellBases K B)
    (h0 : K.r₁ ≠ 0) (Q : ℕ) (F : ℝ × ℝ → ℂ) (hF : IntegrableOn F K.rect) :
    K.normSqOn (fun _ => 1) (K.proj Q Q F) = ∑ jl : Fin (Q + 1) × Fin (Q + 1), ‖B.coef K F jl.1 jl.2‖ ^ 2 := by
  classical
  have hw : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h0]
  set b := fun i : Fin (Q + 1) × Fin (Q + 1) => basisFn B i.1 i.2 with hb
  have hbc : ∀ i, Continuous (b i) := fun i => poly_cont B _ _
  have hmc : ∀ k : Fin (Q + 1) × Fin (Q + 1), Continuous (monomial k.1 k.2) := fun k => by
    unfold monomial; fun_prop
  set c := fun i : Fin (Q + 1) × Fin (Q + 1) => B.coef K F i.1 i.2 with hc
  set Ps := fun p => ∑ i, c i * ((b i p : ℝ) : ℂ) with hPs
  have hPsc : Continuous Ps := continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Complex.continuous_ofReal.comp (hbc i))
  have hwF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect := by simpa [hw] using hF
  have hmem : Ps ∈ polyFn Q Q := by
    have he : ∀ i, ∃ e : Fin (Q + 1) × Fin (Q + 1) → ℝ, ∑ k, e k • monomial k.1 k.2 = b i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun ℝ).1 (basis_in_mono B Q i)
    choose e he using he
    refine (poly_mem Ps).2 ⟨fun k => ∑ i, c i * (e i k : ℂ), ?_⟩
    funext p
    simp only [hPs]
    have : ∀ i, ((b i p : ℝ) : ℂ) = ∑ k, (e i k : ℂ) * ((monomial k.1 k.2 p : ℝ) : ℂ) := by
      intro i
      rw [← he i]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      push_cast; rfl
    simp only [this, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  have hpairlin : ∀ (P₁ P₂ T : ℝ × ℝ → ℂ), IntegrableOn (fun p => P₁ p * (starRingEnd ℂ) (T p)) K.rect →
      IntegrableOn (fun p => P₂ p * (starRingEnd ℂ) (T p)) K.rect →
      K.pairOn (fun _ => 1) (fun p => P₁ p - P₂ p) T =
        (∫ p in K.rect, P₁ p * (starRingEnd ℂ) (T p)) - ∫ p in K.rect, P₂ p * (starRingEnd ℂ) (T p) := by
    intro P₁ P₂ T h1 h2
    unfold CellBox.pairOn
    rw [← integral_sub h1 h2]
    congr 1; funext p; push_cast; ring
  have hFT : ∀ T : ℝ × ℝ → ℂ, Continuous T → IntegrableOn (fun p => F p * (starRingEnd ℂ) (T p)) K.rect :=
    fun T hT => hF.mul_continuousOn (Complex.continuous_conj.comp hT).continuousOn (rect_compact K)
  have hCT : ∀ P T : ℝ × ℝ → ℂ, Continuous P → Continuous T →
      IntegrableOn (fun p => P p * (starRingEnd ℂ) (T p)) K.rect :=
    fun P T hP hT => (hP.mul (Complex.continuous_conj.comp hT)).continuousOn.integrableOn_compact (rect_compact K)
  have hpoly_cont : ∀ T ∈ polyFn Q Q, Continuous T := by
    intro T hT
    obtain ⟨t, rfl⟩ := (poly_mem T).1 hT
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (Complex.continuous_ofReal.comp (hmc k))
  have horth : ∀ T ∈ polyFn Q Q, K.pairOn (fun _ => 1) (fun p => F p - Ps p) T = 0 := by
    intro T hT
    have hTc := hpoly_cont T hT
    rw [hpairlin F Ps T (hFT T hTc) (hCT Ps T hPsc hTc), sub_eq_zero]
    obtain ⟨t, rfl⟩ := (poly_mem T).1 hT
    have hpt : ∀ (P : ℝ × ℝ → ℂ) (p : ℝ × ℝ), P p * (starRingEnd ℂ) (∑ k, t k * ((monomial k.1 k.2 p : ℝ) : ℂ)) =
        ∑ k, (starRingEnd ℂ) (t k) * (P p * ((monomial k.1 k.2 p : ℝ) : ℂ)) := by
      intro P p
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_mul, Complex.conj_ofReal]; ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun k _ => ?_, integral_finsetSum _ fun k _ => ?_]
    rotate_left
    · exact ((hPsc.mul (Complex.continuous_ofReal.comp (hmc k))).continuousOn.integrableOn_compact
        (rect_compact K)).const_mul _
    · exact (hF.mul_continuousOn (Complex.continuous_ofReal.comp (hmc k)).continuousOn (rect_compact K)).const_mul _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_const_mul]
    congr 1
    have hE := expand K B hK hB Q F hwF (monomial k.1 k.2) (mono_span K B hB Q k.1 k.2
      (Nat.lt_succ_iff.mp k.1.2) (Nat.lt_succ_iff.mp k.2.2))
    simp only [hw, Complex.ofReal_one, one_mul] at hE
    rw [hE]
    simp only [hPs, Finset.sum_mul]
    rw [integral_finsetSum _ fun i _ => ?_]
    rotate_left
    · exact ((continuous_const.mul (Complex.continuous_ofReal.comp (hbc i))).mul
        (Complex.continuous_ofReal.comp (hmc k))).continuousOn.integrableOn_compact (rect_compact K)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    simp only [mul_assoc]
    rw [integral_const_mul, ← integral_complex_ofReal]
    congr 2
    funext p
    push_cast; simp only [hb]; ring
  have hex : ∃ P ∈ polyFn Q Q, ∀ T ∈ polyFn Q Q, K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0 := by
    refine ⟨Ps, hmem, fun T hT => ?_⟩
    have : K.lineWeightFn = fun _ => 1 := funext fun p => hw p.1
    rw [this]; exact horth T hT
  unfold CellBox.proj
  rw [dif_pos hex]
  obtain ⟨hP0mem, hP0orth⟩ := hex.choose_spec
  set P0 := hex.choose
  have hlw : K.lineWeightFn = fun _ => 1 := funext fun p => hw p.1
  rw [hlw] at hP0orth
  have hP0c := hpoly_cont P0 hP0mem
  have hDmem : (fun p => P0 p - Ps p) ∈ polyFn Q Q := by
    obtain ⟨c0, hc0⟩ := (poly_mem P0).1 hP0mem
    obtain ⟨c1, hc1⟩ := (poly_mem Ps).1 hmem
    refine (poly_mem _).2 ⟨c0 - c1, ?_⟩
    funext p
    rw [hc0, hc1]
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  set D := fun p => P0 p - Ps p with hD
  have hDc : Continuous D := hP0c.sub hPsc
  have hDD : ∫ p in K.rect, D p * (starRingEnd ℂ) (D p) = 0 := by
    have h1 := horth D hDmem
    have h2 := hP0orth D hDmem
    rw [hpairlin F Ps D (hFT D hDc) (hCT Ps D hPsc hDc)] at h1
    rw [hpairlin F P0 D (hFT D hDc) (hCT P0 D hP0c hDc)] at h2
    have : ∫ p in K.rect, D p * (starRingEnd ℂ) (D p) =
        (∫ p in K.rect, P0 p * (starRingEnd ℂ) (D p)) - ∫ p in K.rect, Ps p * (starRingEnd ℂ) (D p) := by
      rw [← integral_sub (hCT P0 D hP0c hDc) (hCT Ps D hPsc hDc)]
      congr 1; funext p; simp only [hD]; ring
    rw [this]
    linear_combination h1 - h2
  have hnn : 0 ≤ᵐ[volume.restrict K.rect] fun p => ‖D p‖ ^ 2 :=
    Filter.Eventually.of_forall fun p => by positivity
  have hI : Integrable (fun p => ‖D p‖ ^ 2) (volume.restrict K.rect) :=
    (hDc.norm.pow 2).continuousOn.integrableOn_compact (rect_compact K)
  have hzero : ∫ p in K.rect, ‖D p‖ ^ 2 = 0 := by
    have : ((∫ p in K.rect, ‖D p‖ ^ 2 : ℝ) : ℂ) = ∫ p in K.rect, D p * (starRingEnd ℂ) (D p) := by
      rw [← integral_complex_ofReal]
      congr 1; funext p
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast this.trans hDD
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hI).1 hzero
  have hstep : K.normSqOn (fun _ => 1) P0 = K.normSqOn (fun _ => 1) Ps := by
    unfold CellBox.normSqOn
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    have : D p = 0 := by simpa using hp
    have : P0 p = Ps p := sub_eq_zero.1 this
    rw [this]
  rw [hstep]
  have hint : ∀ i i', IntegrableOn (fun p => (fun _ => (1 : ℝ)) p * b i p * b i' p) K.rect := fun i i' =>
    ((continuous_const.mul (hbc i)).mul (hbc i')).continuousOn.integrableOn_compact (rect_compact K)
  have h0F : ∀ i, IntegrableOn (fun p => (((fun _ => (1 : ℝ)) p : ℝ) : ℂ) * (fun _ => (0 : ℂ)) p * (b i p : ℂ)) K.rect := by
    intro i; simp
  have hN := (param_eq K (fun _ => 1) (fun _ => 0) b h0F hint c).1
  have hG : testInnerMatrix K (fun _ => 1) b = 1 := by
    ext i i'
    have hval : ∫ p in K.rect, (1 : ℝ) * b i p * b i' p =
        if (i.1 : ℕ) = i'.1 ∧ (i.2 : ℕ) = i'.2 then 1 else 0 := by
      rw [← orth2 K B hB i'.1 i'.2 i.1 i.2]
      congr 1; funext p; rw [hw]
    simp only [testInnerMatrix, rectIntegral, one_apply, hval]
    have hii : ((i.1 : ℕ) = i'.1 ∧ (i.2 : ℕ) = i'.2) ↔ i = i' := by
      rw [Fin.val_inj, Fin.val_inj, Prod.ext_iff]
    simp only [hii]
    split_ifs <;> simp
  rw [hG, one_mulVec] at hN
  apply Complex.ofReal_injective
  rw [hN]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']

private lemma axis_pt (r : ℝ) (x : ℂ) (m : ℝ) : (r : ℂ) * x * (m : ℂ) = (r : ℂ) * (x / r) * ((r * m : ℝ) : ℂ) := by
  by_cases hr : r = 0
  · simp [hr]
  · have : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    push_cast
    field_simp

private lemma sum_swap4 (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    ∑ a, ∑ b, ∑ a', ∑ b', f a b a' b' = ∑ a', ∑ b', ∑ a, ∑ b, f a b a' b' := by
  simp only [Fin.sum_univ_three]; ring

private lemma scaled_mem {d d' : ℕ} {ι : Type} [Fintype ι] (e : ι ≃ Fin (d + 1) × Fin (d' + 1)) (P : ℝ × ℝ → ℂ) :
    P ∈ scaledPolyFn (fun p => p.1) d d' ↔
      ∃ c : ι → ℂ, P = fun p => ∑ i, c i * ((angularTest (e i).1 (e i).2 p : ℝ) : ℂ) := by
  constructor
  · rintro ⟨P₀, ⟨c', hc'⟩, hP⟩
    refine ⟨fun i => c' (e i).1 (e i).2, ?_⟩
    funext p
    rw [hP p, hc' p, ← e.symm.sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [Equiv.apply_symm_apply, angularTest, monomial]
    push_cast; ring
  · rintro ⟨c, rfl⟩
    refine ⟨fun p => ∑ i, c i * ((monomial (e i).1 (e i).2 p : ℝ) : ℂ), ⟨fun j l => c (e.symm (j, l)), fun p => ?_⟩,
      fun p => ?_⟩
    · dsimp only
      rw [← e.symm.sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
      simp only [Equiv.apply_symm_apply, monomial]
      push_cast; ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [angularTest]
      push_cast; ring

private lemma supremum_case (K : CellBox) (μ : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ → ℂ)) (F : ℝ × ℝ → ℂ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (Ps : ι → ℝ × ℝ → ℝ)
    (hV : ∀ P, P ∈ V ↔ ∃ c : ι → ℂ, P = fun p => ∑ i, c i * ((Ps i p : ℝ) : ℂ))
    (hG : (testInnerMatrix K μ Ps).PosDef)
    (hF : ∀ i, IntegrableOn (fun p => (μ p : ℂ) * F p * (Ps i p : ℂ)) K.rect)
    (hP : ∀ i i', IntegrableOn (fun p => μ p * Ps i p * Ps i' p) K.rect) (x : ι → ℂ)
    (hx : ∀ i, ∫ p in K.rect, (μ p : ℂ) * F p * (Ps i p : ℂ) = x i) :
    K.testSupremum μ V F = (star x ⬝ᵥ ((testInnerMatrix K μ Ps)⁻¹ *ᵥ x)).re := by
  have hxe : (fun i => ∫ p in K.rect, (μ p : ℂ) * F p * (Ps i p : ℂ)) = x := funext hx
  apply supremum_eq_of K μ V F _ hG x
  · intro P hPV
    obtain ⟨c, rfl⟩ := (hV P).1 hPV
    exact ⟨c, (param_eq K μ F Ps hF hP c).1, hxe ▸ (param_eq K μ F Ps hF hP c).2⟩
  · intro c
    exact ⟨_, (hV _).2 ⟨c, rfl⟩, (param_eq K μ F Ps hF hP c).1, hxe ▸ (param_eq K μ F Ps hF hP c).2⟩

theorem componentAngular_of (hF : AngularFrameStatement) (hM : ModeIntegrableStatement) :
    ComponentAngularStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u hset n C
  have hK := hset.box
  have hB := hset.bases
  have hR := hset.represents
  set A := angularArray (azimuth c.order n) C with hA
  set g := strainField c.order (n : ℤ) G A with hg
  set F := angularField c.order (n : ℤ) H C with hFdef
  have hint : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode c.order (n : ℤ) G a b p) K.rect :=
    fun a b => (hM c.order v G H hset.field K hK (n : ℤ) a).2 b
  have hgint : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * g p) K.rect := by
    have : (fun p => (K.lineWeight p.1 : ℂ) * g p) =
        fun p => ∑ a, ∑ b, A a b * ((K.lineWeight p.1 : ℂ) * gradMode c.order n G a b p) := by
      funext p
      simp only [hg, strainField, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _
  have hae : ∀ᵐ p ∂(volume.restrict K.rect), F p = g p := by
    have h9 : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a b, angularGradMode c.order n H a b p =
        ∑ a', ∑ b', angularComb (azimuth c.order n) a b a' b' * gradMode c.order n G a' b' p := by
      rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro b
      exact hF α c K B S I v G H u hset n a b
    filter_upwards [h9] with p hp
    simp only [hFdef, hg, angularField, strainField, hp, hA, angularArray, Finset.mul_sum, Finset.sum_mul]
    rw [sum_swap4 (fun a b a' b' => C a b * (angularComb (azimuth c.order n) a b a' b' * gradMode c.order n G a' b' p))]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hrow : ∀ j l : Fin (Q + 1), rowApply (lowRow I n A j l) u = B.coef K g j l := by
    intro j l
    rw [lowRow_apply, hg, coef_strain K B c.order n G A hint]
    simp only [hR.strain]
  have hpair : ∀ φ : ℝ × ℝ → ℝ, rowApply (lowPairRow K B I n A φ) u = ∑ jl : Fin (Q + 1) × Fin (Q + 1),
      ((rectIntegral K (fun p => basisFn B jl.1 jl.2 p * φ p) : ℝ) : ℂ) * B.coef K g jl.1 jl.2 := by
    intro φ
    rw [lowPair_apply]
    simp only [hrow]
  have hcont : ∀ (f : ℝ × ℝ → ℝ), Continuous f → IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * g p * (f p : ℂ)) K.rect :=
    fun f hf => hgint.mul_continuousOn (Complex.continuous_ofReal.comp hf).continuousOn (rect_compact K)
  by_cases h0 : K.r₁ = 0
  · have hw : ∀ r, K.lineWeight r = r := fun r => by simp [CellBox.lineWeight, h0]
    rw [if_pos h0]
    unfold CellBox.angularEnergy
    rw [if_pos h0]
    unfold angularAxisForm testSupForm
    rw [quad_formOfRows]
    symm
    refine supremum_case K (fun p => p.1) _ _ (fun jl : Fin (Q + 1) × Fin (Q + 1) => angularTest jl.1 jl.2)
      (fun P => scaled_mem (Equiv.refl _) P) (pairing_axis_pd K hK h0 Q) ?_ ?_ _ ?_
    · intro i
      refine (hcont _ (by unfold monomial; fun_prop : Continuous (monomial i.1 i.2))).congr ?_
      refine (ae_restrict_iff' (rect_meas K)).2 ?_
      filter_upwards [(ae_restrict_iff' (rect_meas K)).1 hae] with p hp hpr
      rw [hp hpr, hw]
      exact axis_pt _ _ _
    · intro i i'
      exact (by unfold angularTest monomial; fun_prop : Continuous fun p : ℝ × ℝ =>
        p.1 * angularTest i.1 i.2 p * angularTest i'.1 i'.2 p).continuousOn.integrableOn_compact (rect_compact K)
    · intro i
      rw [hpair]
      have h1 : ∫ p in K.rect, ((p.1 : ℝ) : ℂ) * (F p / (p.1 : ℂ)) * ((angularTest i.1 i.2 p : ℝ) : ℂ) =
          ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * g p * ((monomial i.1 i.2 p : ℝ) : ℂ) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with p hp
        rw [hp, hw]
        exact (axis_pt _ _ _).symm
      rw [h1, expand K B hK hB Q g hgint _ (mono_span K B hB Q i.1 i.2 (Nat.lt_succ_iff.mp i.1.2)
        (Nat.lt_succ_iff.mp i.2.2))]
      refine Finset.sum_congr rfl fun jl _ => ?_
      congr 2
      unfold rectIntegral
      congr 1
      funext p
      rw [hw]
      unfold angularTest
      ring
  · have hw : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h0]
    rw [if_neg h0]
    unfold CellBox.angularEnergy
    rw [if_neg h0]
    unfold angularOffForm
    rw [quad_add]
    have hr1 : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
    have hr2 : 0 < K.r₂ := hr1.trans hK.r_order.2
    have hpos : ∀ p ∈ K.rect, 0 < p.1 := fun p hp => hr1.trans_le hp.1.1
    have hFint : IntegrableOn F K.rect := by
      have : IntegrableOn g K.rect := by simpa [hw] using hgint
      exact this.congr (by filter_upwards [hae] with p hp; exact hp.symm)
    have hcoef : ∀ j l, B.coef K F j l = B.coef K g j l := by
      intro j l
      unfold CellBases.coef
      exact integral_congr_ae (by filter_upwards [hae] with p hp; rw [hp])
    congr 1
    · erw [quad_formOfRows]
      rw [proj_norm K B hK hB h0 Q F hFint]
      simp only [hrow, hcoef]
      simp only [mulVec, dotProduct, Pi.star_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, RCLike.star_def]
      rw [Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun jl _ => ?_
      rw [show (starRingEnd ℂ) (B.coef K g jl.1 jl.2) * (((K.r₂⁻¹ : ℝ) : ℂ) * B.coef K g jl.1 jl.2) =
          ((K.r₂⁻¹ * ‖B.coef K g jl.1 jl.2‖ ^ 2 : ℝ) : ℂ) by
        rw [mul_left_comm, Complex.conj_mul']; push_cast; ring, Complex.ofReal_re]
    · have hQ : 1 ≤ Q := by
        have h1 := hset.scalars.degrees
        have h2 := hset.degHigh_eq
        omega
      obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      unfold testSupForm
      rw [quad_formOfRows]
      symm
      have hco : ∀ i : Fin (Q' + 1) × Fin (Q' + 1 + 1),
          ContinuousOn (fun p : ℝ × ℝ => angularOffWeight K p * angularTest i.1 i.2 p) K.rect := by
        intro i
        unfold angularOffWeight angularTest monomial
        refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)
        intro p hp
        exact mul_ne_zero (hpos p hp).ne' hr2.ne'
      have hψ : ∀ i : Fin (Q' + 1) × Fin (Q' + 1 + 1), ∀ p ∈ K.rect, angularOffWeight K p * angularTest i.1 i.2 p =
          (monomial i.1 i.2 - K.r₂⁻¹ • monomial (i.1 + 1) i.2) p := by
        intro i p hp
        have := (hpos p hp).ne'
        simp only [angularOffWeight, angularTest, monomial, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      refine supremum_case K (angularOffWeight K) _ F (fun jl : Fin (Q' + 1) × Fin (Q' + 1 + 1) => angularTest jl.1 jl.2)
        (fun P => scaled_mem (Equiv.refl _) P) (pairing_off_pd K hK h0 (Q' + 1)) ?_ ?_ _ ?_
      · intro i
        have := hFint.mul_continuousOn (Complex.continuous_ofReal.comp_continuousOn (hco i)) (rect_compact K)
        refine this.congr (Filter.Eventually.of_forall fun p => ?_)
        simp only [Function.comp_apply]
        push_cast; ring
      · intro i i'
        have hcw : ContinuousOn (angularOffWeight K) K.rect := by
          unfold angularOffWeight
          refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
          intro p hp
          exact mul_ne_zero (hpos p hp).ne' hr2.ne'
        refine ContinuousOn.integrableOn_compact (rect_compact K) ?_
        refine (hcw.mul ?_).mul ?_
        · exact (by unfold angularTest monomial; fun_prop : Continuous (angularTest i.1 i.2)).continuousOn
        · exact (by unfold angularTest monomial; fun_prop : Continuous (angularTest i'.1 i'.2)).continuousOn
      · intro i
        rw [hpair]
        have hmem : (monomial i.1 i.2 - K.r₂⁻¹ • monomial (i.1 + 1) i.2) ∈ Submodule.span ℝ
            (Set.range (fun jl : Fin (Q' + 1 + 1) × Fin (Q' + 1 + 1) => basisFn B jl.1 jl.2)) :=
          Submodule.sub_mem _ (mono_span K B hB _ _ _ (by omega) (by omega))
            (Submodule.smul_mem _ _ (mono_span K B hB _ _ _ (by omega) (by omega)))
        have h1 : ∫ p in K.rect, ((angularOffWeight K p : ℝ) : ℂ) * F p * ((angularTest i.1 i.2 p : ℝ) : ℂ) =
            ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * g p *
              (((monomial i.1 i.2 - K.r₂⁻¹ • monomial (i.1 + 1) i.2) p : ℝ) : ℂ) := by
          refine integral_congr_ae ?_
          filter_upwards [hae, ae_restrict_mem (rect_meas K)] with p hp hpr
          rw [hp, hw, ← hψ i p hpr]
          push_cast; ring
        rw [h1, expand K B hK hB (Q' + 1) g hgint _ hmem]
        refine Finset.sum_congr rfl fun jl _ => ?_
        congr 2
        unfold rectIntegral
        refine setIntegral_congr_fun (rect_meas K) fun p hp => ?_
        rw [hw, ← hψ i p hp]
        ring

end Breakdown.CellCert.CellEnergy
