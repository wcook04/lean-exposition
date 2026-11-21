import Breakdown.CertCell.LocalComponentAngularAlgebra

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown.CertCell.LocalField.Internal.AngularValue

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy

theorem poly_cont (B : CellBases) (j l : ℕ) : Continuous (fun p : ℝ × ℝ => basisFn B j l p) := by
  unfold basisFn CellBases.radialPoly CellBases.heightPoly
  fun_prop

theorem coef_modeSum (K : CellBox) (B : CellBases) (C' : Fin 3 → Fin 3 → ℂ) (X : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (hint : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X a b p) K.rect) (j l : ℕ) :
    B.coef K (modeSum C' X) j l = ∑ a, ∑ b, C' a b * B.coef K (X a b) j l := by
  have hI : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X a b p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := fun a b =>
    (hint a b).mul_continuousOn (Complex.continuous_ofReal.comp (poly_cont B j l)).continuousOn (rect_compact K)
  unfold CellBases.coef modeSum
  have hpt : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * (∑ a, ∑ b, C' a b * X a b p) *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) = ∑ a, ∑ b, C' a b * ((K.lineWeight p.1 : ℂ) *
        X a b p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
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

theorem lowRow_apply {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (n : modes) (C' : Fin 3 → Fin 3 → ℂ) (j l : Fin (Q + 1)) (u : D → ℂ) :
    rowApply (lowRow I n C' j l) u = ∑ a, ∑ b, C' a b * u (I.strainSlot n a b j l) := by
  simp only [rowApply, lowRow, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [mul_assoc]

theorem lowPair_apply {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
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

theorem orth2 (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (j l j' l' : ℕ) :
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

theorem expand (K : CellBox) (B : CellBases) (hK : IsCellBox K) (hB : IsCellBases K B) (Q : ℕ)
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

theorem pow_span (P : ℕ → ℝ → ℝ) (a : ℕ → ℕ → ℝ)
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

theorem mono_span (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q i k : ℕ) (hi : i ≤ Q)
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


theorem poly_mem {d : ℕ} (P : ℝ × ℝ → ℂ) :
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

theorem basis_in_mono (B : CellBases) (Q : ℕ) (i : Fin (Q + 1) × Fin (Q + 1)) :
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

theorem proj_norm (K : CellBox) (B : CellBases) (hK : IsCellBox K) (hB : IsCellBases K B)
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

end Breakdown.CertCell.LocalField.Internal.AngularValue
