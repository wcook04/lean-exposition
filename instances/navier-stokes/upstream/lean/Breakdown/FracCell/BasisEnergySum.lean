import Breakdown.FracCell.SharpRowIdentity

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

namespace BasisSeriesInternal

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem rect_compactSpace (K : CellBox) : CompactSpace K.rect :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)

theorem lw_cont (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem lw_nonneg (K : CellBox) (p : ℝ × ℝ) (hp : p ∈ K.rect) : 0 ≤ K.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs with h
  · have := hp.1.1
    linarith
  · exact zero_le_one

theorem lw_le (K : CellBox) (p : ℝ × ℝ) (hp : p ∈ K.rect) : K.lineWeight p.1 ≤ max K.r₂ 1 := by
  unfold CellBox.lineWeight
  split_ifs with h
  · exact le_trans hp.1.2 (le_max_left _ _)
  · exact le_max_right _ _

def rho (K : CellBox) : Measure K.rect := Measure.comap Subtype.val volume

def wt (K : CellBox) (x : K.rect) : NNReal := Real.toNNReal (K.lineWeight x.1.1)

def nu (K : CellBox) : Measure K.rect := (rho K).withDensity (fun x => (wt K x : ENNReal))

theorem emb (K : CellBox) : MeasurableEmbedding (Subtype.val : K.rect → ℝ × ℝ) :=
  MeasurableEmbedding.subtype_coe (rect_meas K)

theorem map_rho (K : CellBox) : (rho K).map Subtype.val = volume.restrict K.rect :=
  map_comap_subtype_coe (rect_meas K) _

theorem wt_meas (K : CellBox) : Measurable (wt K) :=
  measurable_real_toNNReal.comp ((lw_cont K).measurable.comp (measurable_fst.comp measurable_subtype_coe))

theorem wt_coe (K : CellBox) (x : K.rect) : ((wt K x : NNReal) : ℝ) = K.lineWeight x.1.1 :=
  Real.coe_toNNReal _ (lw_nonneg K x.1 x.2)

theorem rho_finite (K : CellBox) : IsFiniteMeasure (rho K) := by
  constructor
  have h : rho K Set.univ = (volume.restrict K.rect) Set.univ := by
    rw [← map_rho K, Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
    rfl
  rw [h, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top

theorem nu_finite (K : CellBox) : IsFiniteMeasure (nu K) := by
  have := rho_finite K
  constructor
  unfold nu
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ x, (wt K x : ENNReal) ∂(rho K) ≤ ∫⁻ _, (Real.toNNReal (max K.r₂ 1) : ENNReal) ∂(rho K) := by
        apply lintegral_mono
        intro x
        exact ENNReal.coe_le_coe.mpr (Real.toNNReal_le_toNNReal (lw_le K x.1 x.2))
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)

attribute [local instance] rect_compactSpace nu_finite

theorem integral_nu (K : CellBox) (g : ℝ × ℝ → ℂ) :
    ∫ x, g x.1 ∂(nu K) = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * g p := by
  unfold nu
  rw [integral_withDensity_eq_integral_smul (wt_meas K), ← map_rho K, (emb K).integral_map]
  congr 1
  funext x
  rw [NNReal.smul_def, Complex.real_smul, wt_coe]

theorem integrable_nu_iff (K : CellBox) (g : ℝ × ℝ → ℝ) :
    Integrable (fun x : K.rect => g x.1) (nu K) ↔ IntegrableOn (fun p => K.lineWeight p.1 * g p) K.rect := by
  unfold nu
  rw [integrable_withDensity_iff_integrable_smul (wt_meas K), IntegrableOn, ← map_rho K,
    (emb K).integrable_map_iff]
  have e : (fun x : K.rect => wt K x • g x.1) = (fun p : ℝ × ℝ => K.lineWeight p.1 * g p) ∘ Subtype.val := by
    funext x
    simp only [Function.comp, NNReal.smul_def, smul_eq_mul, wt_coe]
  rw [e]

theorem memLp_of (K : CellBox) (F : ℝ × ℝ → ℂ) (hF : IsWeightedSquare K F) :
    MemLp (fun x : K.rect => F x.1) 2 (nu K) := by
  have hm : AEStronglyMeasurable (fun x : K.rect => F x.1) (nu K) := by
    have h1 : AEStronglyMeasurable (fun x : K.rect => F x.1) (rho K) := by
      have := hF.1
      rw [← map_rho K, (emb K).aestronglyMeasurable_map_iff] at this
      exact this
    exact h1.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [memLp_two_iff_integrable_sq_norm hm]
  exact (integrable_nu_iff K (fun p => ‖F p‖ ^ 2)).mpr hF.2

theorem inner_C (a b : ℂ) : inner ℂ a b = conj a * b := by
  rw [RCLike.inner_apply]
  ring

theorem inner_ae (K : CellBox) (u v : Lp ℂ 2 (nu K)) (f g : K.rect → ℂ) (hu : u =ᵐ[nu K] f)
    (hv : v =ᵐ[nu K] g) : inner ℂ u v = ∫ x, conj (f x) * g x ∂(nu K) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x h1 h2
  rw [h1, h2, inner_C]

def bv (B : CellBases) (jl : ℕ × ℕ) (p : ℝ × ℝ) : ℂ := ((B.radialPoly jl.1 p.1 * B.heightPoly jl.2 p.2 : ℝ) : ℂ)

theorem radial_cont (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_pow i))

theorem height_cont (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_pow i))

def eC (K : CellBox) (B : CellBases) (jl : ℕ × ℕ) : C(K.rect, ℂ) :=
  ⟨fun x => bv B jl x.1, Complex.continuous_ofReal.comp
    (((radial_cont B jl.1).comp (continuous_fst.comp continuous_subtype_val)).mul
      ((height_cont B jl.2).comp (continuous_snd.comp continuous_subtype_val)))⟩

def eL (K : CellBox) (B : CellBases) (jl : ℕ × ℕ) : Lp ℂ 2 (nu K) :=
  ContinuousMap.toLp (E := ℂ) 2 (nu K) ℂ (eC K B jl)

theorem eL_ae (K : CellBox) (B : CellBases) (jl : ℕ × ℕ) : eL K B jl =ᵐ[nu K] fun x => bv B jl x.1 :=
  ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := nu K) (𝕜 := ℂ) (eC K B jl)

theorem orth (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (a b : ℕ × ℕ) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (conj (bv B a p) * bv B b p) = if a = b then 1 else 0 := by
  have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * (conj (bv B a p) * bv B b p) =
      (((K.lineWeight p.1 * B.radialPoly a.1 p.1 * B.radialPoly b.1 p.1) *
        (B.heightPoly a.2 p.2 * B.heightPoly b.2 p.2) : ℝ) : ℂ) := by
    intro p
    unfold bv
    rw [Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [e]
  rw [integral_complex_ofReal]
  unfold CellBox.rect
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun r => K.lineWeight r * B.radialPoly a.1 r * B.radialPoly b.1 r)
    (fun z => B.heightPoly a.2 z * B.heightPoly b.2 z), hB.radial_orthonormal, hB.height_orthonormal]
  obtain ⟨j, l⟩ := a
  obtain ⟨j', l'⟩ := b
  by_cases h1 : j = j' <;> by_cases h2 : l = l' <;> simp [h1, h2]

theorem orth_eL (K : CellBox) (B : CellBases) (hB : IsCellBases K B) : Orthonormal ℂ (eL K B) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [inner_ae K _ _ _ _ (eL_ae K B a) (eL_ae K B b), integral_nu K (fun p => conj (bv B a p) * bv B b p)]
  exact orth K B hB a b


def mono (K : CellBox) (ab : ℕ × ℕ) : C(K.rect, ℂ) :=
  ⟨fun x => (x.1.1 : ℂ) ^ ab.1 * (x.1.2 : ℂ) ^ ab.2,
    ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_subtype_val)).pow _).mul
      ((Complex.continuous_ofReal.comp (continuous_snd.comp continuous_subtype_val)).pow _)⟩

def M (K : CellBox) : Submodule ℂ C(K.rect, ℂ) := Submodule.span ℂ (Set.range (mono K))

theorem mono_mul (K : CellBox) (a b : ℕ × ℕ) : mono K a * mono K b = mono K (a.1 + b.1, a.2 + b.2) := by
  ext x
  simp only [mono, ContinuousMap.mul_apply, ContinuousMap.coe_mk, pow_add]
  ring

theorem mul_mem_M (K : CellBox) {f g : C(K.rect, ℂ)} (hf : f ∈ M K) (hg : g ∈ M K) : f * g ∈ M K := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [mono_mul]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add y z _ _ h1 h2 =>
      rw [mul_add]
      exact add_mem h1 h2
    | smul c y _ h =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c h
  | zero => simp
  | add x y _ _ h1 h2 =>
    rw [add_mul]
    exact add_mem h1 h2
  | smul c x _ h =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c h

theorem one_mem_M (K : CellBox) : (1 : C(K.rect, ℂ)) ∈ M K := by
  have e : (1 : C(K.rect, ℂ)) = mono K (0, 0) := by
    ext x
    simp [mono]
  rw [e]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem star_mono (K : CellBox) (a : ℕ × ℕ) : star (mono K a) = mono K a := by
  ext x
  simp [mono]

theorem star_mem_M (K : CellBox) {f : C(K.rect, ℂ)} (hf : f ∈ M K) : star f ∈ M K := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [star_mono]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ h1 h2 =>
    rw [star_add]
    exact add_mem h1 h2
  | smul c x _ h =>
    rw [star_smul]
    exact Submodule.smul_mem _ _ h

def A (K : CellBox) : StarSubalgebra ℂ C(K.rect, ℂ) where
  carrier := M K
  mul_mem' := fun hf hg => mul_mem_M K hf hg
  one_mem' := one_mem_M K
  add_mem' := fun hf hg => add_mem hf hg
  zero_mem' := zero_mem _
  algebraMap_mem' := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (one_mem_M K)
  star_mem' := fun hf => star_mem_M K hf

theorem A_sep (K : CellBox) : (A K).SeparatesPoints := by
  intro x y hxy
  have hne : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  by_cases h1 : x.1.1 = y.1.1
  · have h2 : x.1.2 ≠ y.1.2 := fun h2 => hne (Prod.ext h1 h2)
    refine ⟨mono K (0, 1), ⟨mono K (0, 1), Submodule.subset_span ⟨_, rfl⟩, rfl⟩, ?_⟩
    simpa [mono] using h2
  · refine ⟨mono K (1, 0), ⟨mono K (1, 0), Submodule.subset_span ⟨_, rfl⟩, rfl⟩, ?_⟩
    simpa [mono] using h1

theorem pow_mem_span (c : ℕ → ℕ → ℝ) (hc : ∀ j, 0 < c j j) (a : ℕ) :
    (fun r : ℝ => r ^ a) ∈ Submodule.span ℝ (Set.range (fun j (r : ℝ) => ∑ i ∈ Finset.range (j + 1), c j i * r ^ i)) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    have e : (fun r : ℝ => r ^ a) = (c a a)⁻¹ • ((fun r : ℝ => ∑ i ∈ Finset.range (a + 1), c a i * r ^ i) -
        ∑ i ∈ Finset.range a, c a i • (fun r : ℝ => r ^ i)) := by
      funext r
      have := (hc a).ne'
      simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_range_succ]
      field_simp
      ring
    rw [e]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨a, rfl⟩
    · exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (ih i (Finset.mem_range.mp hi)))

theorem pow_expand (c : ℕ → ℕ → ℝ) (hc : ∀ j, 0 < c j j) (a : ℕ) :
    ∃ s : Finset ℕ, ∃ d : ℕ → ℝ, ∀ r : ℝ, r ^ a = ∑ j ∈ s, d j * ∑ i ∈ Finset.range (j + 1), c j i * r ^ i := by
  obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (pow_mem_span c hc a)
  refine ⟨d.support, d, fun r => ?_⟩
  have := congrFun hd r
  rw [← this, Finsupp.sum, Finset.sum_apply]
  rfl

theorem mono_mem_V (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (ab : ℕ × ℕ) :
    mono K ab ∈ Submodule.span ℂ (Set.range (eC K B)) := by
  obtain ⟨s, d, hd⟩ := pow_expand B.radialCoef hB.radial_leading ab.1
  obtain ⟨t, e, he⟩ := pow_expand B.heightCoef hB.height_leading ab.2
  have h : mono K ab = ∑ j ∈ s, ∑ l ∈ t, ((d j * e l : ℝ) : ℂ) • eC K B (j, l) := by
    ext x
    simp only [mono, eC, bv, ContinuousMap.coe_mk, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, hd x.1.1, he x.1.2]
    push_cast
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    unfold CellBases.radialPoly CellBases.heightPoly
    push_cast
    ring
  rw [h]
  exact Submodule.sum_mem _ (fun j _ => Submodule.sum_mem _ (fun l _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, l), rfl⟩)))

theorem M_le_V (K : CellBox) (B : CellBases) (hB : IsCellBases K B) :
    M K ≤ Submodule.span ℂ (Set.range (eC K B)) := by
  unfold M
  rw [Submodule.span_le]
  rintro _ ⟨ab, rfl⟩
  exact mono_mem_V K B hB ab

theorem span_dense (K : CellBox) (B : CellBases) (hB : IsCellBases K B) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (eL K B))).topologicalClosure := by
  set T := ContinuousMap.toLp (E := ℂ) 2 (nu K) ℂ
  set VL := Submodule.span ℂ (Set.range (eL K B))
  have hA : (A K).topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ (A_sep K)
  have hmap : Submodule.map (T : C(K.rect, ℂ) →ₗ[ℂ] Lp ℂ 2 (nu K)) (Submodule.span ℂ (Set.range (eC K B))) ≤ VL := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨jl, rfl⟩, rfl⟩
    exact ⟨jl, rfl⟩
  have hM : ∀ f ∈ M K, T f ∈ VL := fun f hf => hmap ⟨f, M_le_V K B hB hf, rfl⟩
  have hcl : Set.range T ⊆ (VL.topologicalClosure : Set (Lp ℂ 2 (nu K))) := by
    rintro _ ⟨f, rfl⟩
    have hf : f ∈ closure (A K : Set C(K.rect, ℂ)) := by
      have h0 : f ∈ (A K).topologicalClosure := by
        rw [hA]
        trivial
      rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at h0
      exact h0
    have h2 := image_closure_subset_closure_image T.continuous ⟨f, hf, rfl⟩
    rw [Submodule.topologicalClosure_coe]
    refine closure_mono ?_ h2
    rintro _ ⟨g, hg, rfl⟩
    exact hM g hg
  intro u _
  have hd := ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (nu K) ℂ (by norm_num)
  exact closure_minimal hcl VL.isClosed_topologicalClosure (hd u)

theorem inner_e_F (K : CellBox) (B : CellBases) (F : ℝ × ℝ → ℂ) (hF : MemLp (fun x : K.rect => F x.1) 2 (nu K))
    (jl : ℕ × ℕ) : inner ℂ (eL K B jl) (hF.toLp _) = B.coef K F jl.1 jl.2 := by
  rw [inner_ae K _ _ _ _ (eL_ae K B jl) hF.coeFn_toLp, integral_nu K (fun p => conj (bv B jl p) * F p)]
  unfold CellBases.coef
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [bv, Complex.conj_ofReal]
  ring

theorem inner_W_e (K : CellBox) (B : CellBases) (W : ℝ × ℝ → ℂ) (hW : MemLp (fun x : K.rect => W x.1) 2 (nu K))
    (jl : ℕ × ℕ) : inner ℂ (hW.toLp _) (eL K B jl) = conj (B.coef K W jl.1 jl.2) := by
  rw [inner_ae K _ _ _ _ hW.coeFn_toLp (eL_ae K B jl), integral_nu K (fun p => conj (W p) * bv B jl p)]
  unfold CellBases.coef
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [bv, map_mul, Complex.conj_ofReal]
  ring

end BasisSeriesInternal

open BasisSeriesInternal in
theorem basisEnergySum_holds : BasisEnergySumStatement := by
  intro K B _ hB ι _ F W hF hW
  have hFm := fun i => memLp_of K (F i) (hF i)
  have hWm := fun i => memLp_of K (W i) (hW i)
  have hterm : ∀ i, HasSum (fun jl : ℕ × ℕ => B.coef K (F i) jl.1 jl.2 * conj (B.coef K (W i) jl.1 jl.2))
      (∫ x, conj (W i x.1) * F i x.1 ∂(nu K)) := by
    intro i
    have h := (HilbertBasis.mk (orth_eL K B hB) (span_dense K B hB)).hasSum_inner_mul_inner
      ((hWm i).toLp _) ((hFm i).toLp _)
    simp only [HilbertBasis.coe_mk] at h
    rw [inner_ae K _ _ _ _ (hWm i).coeFn_toLp (hFm i).coeFn_toLp] at h
    have e : (fun jl : ℕ × ℕ => inner ℂ ((hWm i).toLp _) (eL K B jl) * inner ℂ (eL K B jl) ((hFm i).toLp _)) =
        fun jl : ℕ × ℕ => B.coef K (F i) jl.1 jl.2 * conj (B.coef K (W i) jl.1 jl.2) := by
      funext jl
      rw [inner_W_e, inner_e_F, mul_comm]
    rw [e] at h
    exact h
  have hint : ∀ i, Integrable (fun x : K.rect => conj (W i x.1) * F i x.1) (nu K) := by
    intro i
    refine (L2.integrable_inner (𝕜 := ℂ) ((hWm i).toLp _) ((hFm i).toLp _)).congr ?_
    filter_upwards [(hWm i).coeFn_toLp, (hFm i).coeFn_toLp] with x h1 h2
    rw [h1, h2, inner_C]
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => hterm i)
  convert hs using 1
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  have h3 := integral_nu K (fun p => ∑ i, conj (W i p) * F i p)
  rw [h3]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [mul_comm (conj _)]

end CellAnalysis

end CellCert

end Breakdown
