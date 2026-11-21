import Breakdown.CertCell.LocalFieldDefs2

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown.CertCell.LocalField.Internal.AngularValue

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy

theorem formOfRows_eq {D ι : Type} [Fintype D] [DecidableEq D] [Fintype ι] (rows : ι → D → ℂ)
    (M : Matrix ι ι ℂ) : formOfRows rows M = (Matrix.of rows)ᴴ * M * Matrix.of rows := by
  ext d d'
  simp only [formOfRows, mul_apply, conjTranspose_apply, of_apply, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]

theorem quad_formOfRows {D ι : Type} [Fintype D] [DecidableEq D] [Fintype ι] (rows : ι → D → ℂ)
    (M : Matrix ι ι ℂ) (u : D → ℂ) :
    quadFormValue (formOfRows rows M) u =
      (star (fun i => rowApply (rows i) u) ⬝ᵥ (M *ᵥ fun i => rowApply (rows i) u)).re := by
  have hx : (fun i => rowApply (rows i) u) = Matrix.of rows *ᵥ u := by
    ext i; simp [rowApply, mulVec, dotProduct]
  unfold quadFormValue
  rw [formOfRows_eq, hx, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

theorem conj_swap {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (a b : ι → ℂ) :
    star (star a ⬝ᵥ (G *ᵥ b)) = star b ⬝ᵥ (G *ᵥ a) := by
  rw [star_dotProduct, star_star, star_mulVec, hG.eq, ← dotProduct_mulVec, dotProduct_comm]

theorem conj_re {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (a : ι → ℂ) :
    ((star a ⬝ᵥ (G *ᵥ a)).re : ℂ) = star a ⬝ᵥ (G *ᵥ a) := by
  have h := conj_swap hG a a
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp; linarith

theorem pd_re_pos {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) {a : ι → ℂ} (ha : a ≠ 0) :
    0 < (star a ⬝ᵥ (G *ᵥ a)).re := by
  have := hG.dotProduct_mulVec_pos ha
  exact (Complex.pos_iff.mp this).1

theorem sesq_bound {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) (c z : ι → ℂ) :
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

theorem sup_identity {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) (x : ι → ℂ) :
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


theorem quad_add {D : Type} [Fintype D] (X Y : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (X + Y) u = quadFormValue X u + quadFormValue Y u := by
  unfold quadFormValue
  rw [add_mulVec, dotProduct_add, Complex.add_re]

theorem supremum_eq_of (K : CellBox) (μ : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ → ℂ)) (F : ℝ × ℝ → ℂ) {ι : Type}
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

theorem param_eq (K : CellBox) (μ : ℝ × ℝ → ℝ) (F : ℝ × ℝ → ℂ) {ι : Type} [Fintype ι]
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


theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem poly1_zero {d : ℕ} (s : Fin d → ℂ) {a b : ℝ} (hab : a < b)
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

theorem poly2_zero {d1 d2 : ℕ} (c : Fin d1 × Fin d2 → ℂ) {a b e f : ℝ} (hab : a < b) (hef : e < f)
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

theorem pairMatrix_pd (K : CellBox) (hK : IsCellBox K) (μ : ℝ × ℝ → ℝ) (hμc : ContinuousOn μ K.rect)
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

theorem pairMatrix_axis_pd (K : CellBox) (hK : IsCellBox K) (h0 : K.r₁ = 0) (Q : ℕ) :
    (testInnerMatrix K (fun p => p.1) (fun jl : Fin (Q + 1) × Fin (Q + 1) => angularTest jl.1 jl.2)).PosDef :=
  pairMatrix_pd K hK _ continuous_fst.continuousOn (fun p hp => h0 ▸ hp.1.1) (fun p hp => h0 ▸ hp.1.1) _ _

theorem pairMatrix_off_pd (K : CellBox) (hK : IsCellBox K) (h0 : K.r₁ ≠ 0) (Q : ℕ) :
    (testInnerMatrix K (angularOffWeight K) (fun jl : Fin Q × Fin (Q + 1) => angularTest jl.1 jl.2)).PosDef := by
  have hr1 : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
  have hr2 : 0 < K.r₂ := hr1.trans hK.r_order.2
  refine pairMatrix_pd K hK _ ?_ ?_ ?_ _ _
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


theorem axis_pt (r : ℝ) (x : ℂ) (m : ℝ) : (r : ℂ) * x * (m : ℂ) = (r : ℂ) * (x / r) * ((r * m : ℝ) : ℂ) := by
  by_cases hr : r = 0
  · simp [hr]
  · have : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    push_cast
    field_simp

theorem sum_swap4 (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    ∑ a, ∑ b, ∑ a', ∑ b', f a b a' b' = ∑ a', ∑ b', ∑ a, ∑ b, f a b a' b' := by
  simp only [Fin.sum_univ_three]; ring

theorem scaled_mem {d d' : ℕ} {ι : Type} [Fintype ι] (e : ι ≃ Fin (d + 1) × Fin (d' + 1)) (P : ℝ × ℝ → ℂ) :
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

theorem supremum_case (K : CellBox) (μ : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ → ℂ)) (F : ℝ × ℝ → ℂ) {ι : Type}
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

end Breakdown.CertCell.LocalField.Internal.AngularValue
