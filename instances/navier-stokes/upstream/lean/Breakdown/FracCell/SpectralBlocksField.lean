import Breakdown.FracCell.SpectralBlocksFamily

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def blockInner (sd : SpectralData) (β : ℕ) (lam : ℝ) : ℝ :=
  if (sd.block β).onAxis then
    sd.axisUpper (sd.block β).degree (lam * ((sd.block β).outerRadius - (sd.block β).innerRadius) ^ 2)
      + sd.intervalUpper (sd.block β).degree
          (lam * ((sd.block β).upperHeight - (sd.block β).lowerHeight) ^ 2 / 4)
  else
    (sd.block β).outerRadius / (sd.block β).innerRadius
      * (sd.intervalUpper (sd.block β).degree
            (lam * ((sd.block β).outerRadius - (sd.block β).innerRadius) ^ 2 / 4)
        + sd.intervalUpper (sd.block β).degree
            (lam * ((sd.block β).upperHeight - (sd.block β).lowerHeight) ^ 2 / 4)
        + ratioFn lam (((sd.block β).mode + 1 : ℝ) ^ 2 / (sd.block β).innerRadius ^ 2))

def FieldWitnessStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (sd : SpectralData), IsSpectralData c sd →
    ∀ lam : ℝ, 0 < lam → ∀ a : Fin N, ∀ φ : Space → Space, IsBlockField (sd.block (c.blockIndex a)) φ →
      MemLp φ 2 volume →
      ∃ (ψ : Space → Space) (Dψ : Space → (Space →L[ℝ] Space)),
        MemLp ψ 2 volume ∧ AEStronglyMeasurable Dψ volume ∧ Integrable (fun y => entrySq (Dψ y)) ∧
        IsWeakGradientOf ψ Dψ ∧ ModeGradient (sd.block (c.blockIndex a)) Dψ ∧
        ModeField (sd.block (c.blockIndex a)) (fun y => φ y - ψ y) ∧
        (∫ y, ‖φ y - ψ y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (Dψ y)
          ≤ blockInner sd (c.blockIndex a) lam * ∫ y, ‖φ y‖ ^ 2

namespace Internal.SpectralBlocksField

theorem blockSpectral_eq (sd : SpectralData) (β : ℕ) (lam : ℝ) :
    sd.blockSpectral β lam = min 1 (blockInner sd β lam) := by
  unfold SpectralData.blockSpectral blockInner
  split_ifs <;> rfl

theorem twoVar_comb {ι : Type*} (s : Finset ι) (w : ι → ℝ) (A : ι → ℝ[X][X]) (r z : ℝ) :
    twoVarEval (∑ b ∈ s, C (C (w b)) * A b) r z = ∑ b ∈ s, w b * twoVarEval (A b) r z := by
  simp [twoVarEval, Polynomial.map_sum, Polynomial.eval_finsetSum]

theorem twoVar_zero (r z : ℝ) : twoVarEval 0 r z = 0 := by
  simp [twoVarEval]

theorem twoVar_continuous (P : ℝ[X][X]) : Continuous (Function.uncurry (twoVarEval P)) := by
  have h : Function.uncurry (twoVarEval P) = fun q : ℝ × ℝ =>
      ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).eval q.2 * q.1 ^ i := by
    funext q
    simp only [Function.uncurry, twoVarEval, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    rfl
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((P.coeff i).continuous.comp continuous_snd).mul (continuous_fst.pow i)


theorem comb_blockField {N : ℕ} (g : CellBlock) (w : Fin N → ℝ) (F : Fin N → Space → Space)
    (hF : ∀ b, w b ≠ 0 → IsBlockField g (F b)) : IsBlockField g (fun y => ∑ b, w b • F b y) := by
  classical
  have hex : ∀ b, ∃ A : Fin 2 → Fin 3 → Fin 2 → ℝ[X][X],
      (∀ s c t, (A s c t).natDegree ≤ g.degree ∧ ∀ j, ((A s c t).coeff j).natDegree ≤ g.degree) ∧
      (g.onAxis = true → ∀ s t, X ∣ A s 0 t ∧ X ∣ A s 1 t) ∧
      (∀ᵐ y ∂volume, w b ≠ 0 → F b y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
        (fun v => ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord v)
          * twoVarEval (A s c t) (radialCoord v) (v 2)) • frameVector c v) y) := by
    intro b
    by_cases hb : w b = 0
    · exact ⟨fun _ _ _ => 0, fun _ _ _ => by simp, fun _ _ _ => by simp,
        Filter.Eventually.of_forall fun _ h => absurd hb h⟩
    · obtain ⟨A, h1, h2, h3⟩ := hF b hb
      exact ⟨A, h1, h2, h3.mono fun _ hy _ => hy⟩
  choose A hA1 hA2 hA3 using hex
  refine ⟨fun s c t => ∑ b, C (C (w b)) * A b s c t, fun s c t => ⟨?_, fun j => ?_⟩, ?_, ?_⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun b _ => (natDegree_C_mul_le _ _).trans (hA1 b s c t).1
  · rw [finsetSum_coeff]
    refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    rw [coeff_C_mul]
    exact (natDegree_C_mul_le _ _).trans ((hA1 b s c t).2 j)
  · intro hax s t
    exact ⟨Finset.dvd_sum fun b _ => dvd_mul_of_dvd_right (hA2 b hax s t).1 _,
      Finset.dvd_sum fun b _ => dvd_mul_of_dvd_right (hA2 b hax s t).2 _⟩
  · filter_upwards [ae_all_iff.2 hA3] with y hy
    have e1 : ∑ b, w b • F b y = ∑ b, w b • ∑ s : Fin 2, Set.indicator (cellSolid g s)
        (fun v => ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord v)
          * twoVarEval (A b s c t) (radialCoord v) (v 2)) • frameVector c v) y := by
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : w b = 0
      · simp [hb]
      · rw [hy b hb]
    simp only [] at e1 ⊢
    rw [e1]
    simp only [twoVar_comb, Set.indicator_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun b _ => by ring
    · simp

theorem radial_continuous : Continuous radialCoord := by
  unfold radialCoord
  fun_prop

theorem angle_measurable : Measurable angleCoord := by
  unfold angleCoord
  have h : Continuous fun y : Space => (⟨y 0, y 1⟩ : ℂ) :=
    Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop : Continuous fun y : Space => (y 0, y 1))
  exact Complex.measurable_arg.comp h.measurable

theorem single_continuous (i : Fin 3) : Continuous fun a : ℝ => (EuclideanSpace.single i a : Space) := by
  exact (Isometry.of_dist_eq fun a b => PiLp.dist_single_same 2 (fun _ : Fin 3 => ℝ) i a b).continuous

theorem frame_measurable (c : Fin 3) : Measurable (frameVector c) := by
  fin_cases c
  · exact (((single_continuous 0).measurable.comp (Real.measurable_cos.comp angle_measurable)).add
      ((single_continuous 1).measurable.comp (Real.measurable_sin.comp angle_measurable)))
  · exact (((single_continuous 0).measurable.comp ((Real.measurable_sin.comp angle_measurable).neg)).add
      ((single_continuous 1).measurable.comp (Real.measurable_cos.comp angle_measurable)))
  · exact measurable_const

theorem solid_measurable (g : CellBlock) (s : Fin 2) : MeasurableSet (cellSolid g s) := by
  have hr : Measurable radialCoord := radial_continuous.measurable
  have hz : Measurable fun y : Space => if s = 0 then y 2 else -y 2 := by
    split_ifs
    · exact (by fun_prop : Continuous fun y : Space => y 2).measurable
    · exact (by fun_prop : Continuous fun y : Space => -y 2).measurable
  unfold cellSolid
  simp only [Set.ofPred_and]
  exact (measurableSet_le measurable_const hr).inter ((measurableSet_le hr measurable_const).inter
    ((measurableSet_le measurable_const hz).inter (measurableSet_le hz measurable_const)))

theorem trig_measurable (t : Fin 2) : Measurable (trigMode t) := by
  unfold trigMode
  split_ifs
  · exact Real.measurable_cos
  · exact Real.measurable_sin

theorem blockField_measurable {g : CellBlock} {φ : Space → Space} (h : IsBlockField g φ) :
    AEStronglyMeasurable φ volume := by
  obtain ⟨A, -, -, hA⟩ := h
  have hS : Measurable fun y => ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
        * twoVarEval (A s c t) (radialCoord w) (w 2)) • frameVector c w) y := by
    refine Finset.measurable_fun_sum _ fun s _ => ?_
    refine Measurable.indicator ?_ (solid_measurable g s)
    refine Finset.measurable_fun_sum _ fun c _ => ?_
    have hX : Measurable fun v : Space => ∑ t : Fin 2, trigMode t (g.mode * angleCoord v)
        * twoVarEval (A s c t) (radialCoord v) (v 2) := by
      refine Finset.measurable_fun_sum _ fun t _ => ?_
      exact ((trig_measurable t).comp (measurable_const.mul angle_measurable)).mul
        ((twoVar_continuous (A s c t)).measurable.comp
          (radial_continuous.measurable.prodMk (by fun_prop : Continuous fun y : Space => y 2).measurable))
    exact hX.smul (frame_measurable c)
  exact hS.aestronglyMeasurable.congr (hA.mono fun y hy => hy.symm)

theorem pair_integrable {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem row_memLp {g : CellBlock} {φ : Space → Space} (h : IsBlockField g φ) (hn : l2Pair φ φ = 1) :
    MemLp φ 2 volume := by
  have hm : AEStronglyMeasurable φ volume := blockField_measurable h
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have e : l2Pair φ φ = ∫ y, ‖φ y‖ ^ 2 := by
    unfold l2Pair
    simp_rw [real_inner_self_eq_norm_sq]
  refine Integrable.of_integral_ne_zero ?_
  rw [← e, hn]
  norm_num

theorem comb_norm {N : ℕ} (R : Fin N → Space → Space) (hR : ∀ b, MemLp (R b) 2 volume)
    (ho : ∀ a b, l2Pair (R a) (R b) = if a = b then 1 else 0) (w : Fin N → ℝ) :
    ∫ y, ‖∑ b, w b • R b y‖ ^ 2 = ∑ b, w b ^ 2 := by
  have h : ∀ y, ‖∑ b, w b • R b y‖ ^ 2 = ∑ a, ∑ b, w a * w b * inner ℝ (R a y) (R b y) := by
    intro y
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp_rw [h]
  have hi : ∀ a b, Integrable (fun y => w a * w b * inner ℝ (R a y) (R b y)) volume :=
    fun a b => (pair_integrable (hR a) (hR b)).const_mul _
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hi a b]
  simp_rw [integral_const_mul]
  have hp : ∀ b, ∫ y, inner ℝ (R a y) (R b y) = if a = b then 1 else 0 := fun b => ho a b
  simp_rw [hp]
  simp [sq]

theorem blockField_mode {g : CellBlock} {φ : Space → Space} (h : IsBlockField g φ) :
    ∃ φ₀ : Space → Space, φ =ᵐ[volume] φ₀ ∧ ModeField g φ₀ := by
  obtain ⟨A, -, -, hA⟩ := h
  exact ⟨_, hA, fun s c t r z => twoVarEval (A s c t) r z, fun s c t => (twoVar_continuous (A s c t)).measurable,
    fun y => rfl⟩

theorem shift_witness {g : CellBlock} {φ φ₀ : Space → Space} (hL : MemLp φ 2 volume) (he : φ =ᵐ[volume] φ₀)
    (hm : ModeField g φ₀) :
    MemLp (fun y => φ y - φ₀ y) 2 volume ∧ IsWeakGradientOf (fun y => φ y - φ₀ y) (fun _ => 0) ∧
      ModeField g (fun y => φ y - (φ y - φ₀ y)) ∧ MemLp (fun y => φ y - (φ y - φ₀ y)) 2 volume ∧
      ∫ y, ‖φ y - (φ y - φ₀ y)‖ ^ 2 = ∫ y, ‖φ y‖ ^ 2 := by
  have hz : (0 : Space → Space) =ᵐ[volume] fun y => φ y - φ₀ y := he.mono fun y hy => by simp [hy]
  have h1 : MemLp (fun y => φ y - φ₀ y) 2 volume := MemLp.zero.ae_eq hz
  refine ⟨h1, fun T _ j => ?_, ?_, hL.sub h1, ?_⟩
  · have e : (fun y => fderiv ℝ T y (unitVector j) • (φ y - φ₀ y)) =ᵐ[volume] fun _ => (0 : Space) :=
      he.mono fun y hy => by simp [hy]
    rw [integral_congr_ae e]
    simp
  · obtain ⟨f, hf, hF⟩ := hm
    exact ⟨f, hf, fun y => (sub_sub_cancel (φ y) (φ₀ y)).trans (hF y)⟩
  · simp only [sub_sub_cancel]
    exact integral_congr_ae (he.mono fun y hy => by simp [hy])

theorem zero_modeGradient (g : CellBlock) : ModeGradient g (fun _ => 0) :=
  ⟨fun _ _ _ _ _ _ => 0, fun _ _ _ _ => measurable_const, fun y => by simp⟩

end Internal.SpectralBlocksField

open Internal.SpectralBlocksField in
theorem blockWitness_of_field (hFW : FieldWitnessStatement) : BlockWitnessStatement := by
  intro k N c sd hsd lam hlam x a
  classical
  have hrowL : ∀ b, MemLp (c.row b) 2 volume := fun b =>
    row_memLp (hsd.rows_in_blocks b) (by rw [hsd.rows_orthonormal b b, if_pos rfl])
  have hblk : IsBlockField (sd.block (c.blockIndex a))
      (fun y => ∑ b, (if c.blockIndex b = c.blockIndex a then x b else 0) • c.row b y) := by
    refine comb_blockField _ _ _ fun b hb => ?_
    have hb' : c.blockIndex b = c.blockIndex a := by
      by_contra hne
      exact hb (if_neg hne)
    rw [← hb']
    exact hsd.rows_in_blocks b
  have hφL : MemLp (fun y => ∑ b, (if c.blockIndex b = c.blockIndex a then x b else 0) • c.row b y) 2 volume :=
    memLp_finsetSum _ fun b _ => (hrowL b).const_smul (if c.blockIndex b = c.blockIndex a then x b else 0)
  have hnorm : ∫ y, ‖∑ b, (if c.blockIndex b = c.blockIndex a then x b else 0) • c.row b y‖ ^ 2
      = ∑ b, (if c.blockIndex b = c.blockIndex a then x b ^ 2 else 0) := by
    rw [comb_norm _ hrowL hsd.rows_orthonormal]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  simp only [blockSpectral_eq]
  by_cases hE : blockInner sd (c.blockIndex a) lam ≤ 1
  · obtain ⟨ψ, Dψ, h1, h2, h3, h4, h5, h6, h7⟩ := hFW c sd hsd lam hlam a _ hblk hφL
    refine ⟨ψ, Dψ, h1, h2, h3, h4, h5, h6, hφL.sub h1, ?_⟩
    rw [min_eq_right hE, ← hnorm]
    exact h7
  · obtain ⟨φ₀, he, hmode⟩ := blockField_mode hblk
    obtain ⟨s1, s2, s3, s4, s5⟩ := shift_witness hφL he hmode
    refine ⟨_, fun _ => 0, s1, aestronglyMeasurable_const, ?_, s2, zero_modeGradient _, s3, s4, ?_⟩
    · simp [entrySq]
    · rw [min_eq_left (le_of_lt (not_le.mp hE)), ← hnorm, s5]
      simp [entrySq]

end Spectral

end CellCert

end Breakdown
