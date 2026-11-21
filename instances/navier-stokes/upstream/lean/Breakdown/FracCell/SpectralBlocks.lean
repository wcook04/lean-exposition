import Breakdown.FracCell.SpectralBlocksPiece

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.SpectralBlocks

def Adm (ψ : Space → Space) (Dψ : Space → (Space →L[ℝ] Space)) : Prop :=
  MemLp ψ 2 volume ∧ AEStronglyMeasurable Dψ volume ∧
    (∀ j : Fin 3, MemLp (fun y => Dψ y (unitVector j)) 2 volume) ∧ IsWeakGradientOf ψ Dψ

theorem comp_memLp {Dψ : Space → (Space →L[ℝ] Space)} (hD : AEStronglyMeasurable Dψ volume)
    (hE : Integrable (fun y => entrySq (Dψ y))) (j : Fin 3) :
    MemLp (fun y => Dψ y (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => Dψ y (unitVector j)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hD
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine hE.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ ‖Dψ y (unitVector j)‖ ^ 2 := by positivity
  rw [Real.norm_of_nonneg h0]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖Dψ y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ j)

theorem entrySq_integrable {Dψ : Space → (Space →L[ℝ] Space)}
    (h : ∀ j : Fin 3, MemLp (fun y => Dψ y (unitVector j)) 2 volume) :
    Integrable (fun y => entrySq (Dψ y)) := by
  unfold entrySq
  exact integrable_finsetSum _ fun j _ => (memLp_two_iff_integrable_sq_norm (h j).1).1 (h j)

theorem inner_integrable {u v : Space → Space} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Integrable fun y => inner ℝ (u y) (v y) := by
  have huv := hu.add hv
  have h := (memLp_two_iff_integrable_sq_norm huv.1).1 huv
  have h1 := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have h2 := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  have e : (fun y => inner ℝ (u y) (v y)) =
      fun y => (‖(u + v) y‖ ^ 2 - ‖u y‖ ^ 2 - ‖v y‖ ^ 2) / 2 := by
    funext y
    simp only [Pi.add_apply]
    rw [norm_add_sq_real]
    ring
  rw [e]
  exact ((h.sub h1).sub h2).div_const 2

theorem weak_add {f₁ f₂ : Space → Space} {g₁ g₂ : Space → (Space →L[ℝ] Space)}
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume)
    (hg₁ : ∀ j : Fin 3, MemLp (fun y => g₁ y (unitVector j)) 2 volume)
    (hg₂ : ∀ j : Fin 3, MemLp (fun y => g₂ y (unitVector j)) 2 volume)
    (h₁ : IsWeakGradientOf f₁ g₁) (h₂ : IsWeakGradientOf f₂ g₂) :
    IsWeakGradientOf (fun y => f₁ y + f₂ y) (fun y => g₁ y + g₂ y) := by
  intro φ hφ j
  have hφc : Continuous φ := hφ.1.continuous
  have hφd : Continuous fun y => fderiv ℝ φ y (unitVector j) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφs : HasCompactSupport fun y => fderiv ℝ φ y (unitVector j) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)
  have hA : ∀ f : Space → Space, MemLp f 2 volume →
      Integrable fun y => fderiv ℝ φ y (unitVector j) • f y :=
    fun f hf => (hf.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφd hφs
  have hB : ∀ f : Space → Space, MemLp f 2 volume → Integrable fun y => φ y • f y :=
    fun f hf => (hf.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφc hφ.2
  simp only [ContinuousLinearMap.add_apply, smul_add]
  rw [integral_add (hA _ hf₁) (hA _ hf₂), integral_add (hB _ (hg₁ j)) (hB _ (hg₂ j)), h₁ φ hφ j,
    h₂ φ hφ j, neg_add]

theorem adm_zero : Adm (fun _ => 0) (fun _ => 0) := by
  refine ⟨MemLp.zero', aestronglyMeasurable_const, fun j => ?_, fun φ _ j => ?_⟩
  · simpa using (MemLp.zero' : MemLp (fun _ : Space => (0 : Space)) 2 volume)
  · simp

theorem adm_add {f₁ f₂ : Space → Space} {g₁ g₂ : Space → (Space →L[ℝ] Space)}
    (h₁ : Adm f₁ g₁) (h₂ : Adm f₂ g₂) : Adm (fun y => f₁ y + f₂ y) (fun y => g₁ y + g₂ y) :=
  ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun j => (h₁.2.2.1 j).add (h₂.2.2.1 j),
    weak_add h₁.1 h₂.1 h₁.2.2.1 h₂.2.2.1 h₁.2.2.2 h₂.2.2.2⟩

theorem adm_sum (ψ : ℕ → Space → Space) (Dψ : ℕ → Space → (Space →L[ℝ] Space)) :
    ∀ B : Finset ℕ, (∀ β ∈ B, Adm (ψ β) (Dψ β)) →
      Adm (fun y => ∑ β ∈ B, ψ β y) (fun y => ∑ β ∈ B, Dψ β y) := by
  intro B
  induction B using Finset.induction_on with
  | empty => intro _; simp only [Finset.sum_empty]; exact adm_zero
  | @insert a s ha ih =>
    intro h
    simp only [Finset.sum_insert ha]
    exact adm_add (h a (Finset.mem_insert_self a s)) (ih fun β hβ => h β (Finset.mem_insert_of_mem hβ))

theorem diag_integral (B : Finset ℕ) (w : ℕ → ℕ → Space → ℝ)
    (hi : ∀ β ∈ B, ∀ β' ∈ B, Integrable (w β β'))
    (ho : ∀ β ∈ B, ∀ β' ∈ B, β ≠ β' → ∫ y, w β β' y = 0) :
    ∫ y, ∑ β ∈ B, ∑ β' ∈ B, w β β' y = ∑ β ∈ B, ∫ y, w β β y := by
  rw [integral_finsetSum _ (fun β hβ => integrable_finsetSum _ fun β' hβ' => hi β hβ β' hβ')]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [integral_finsetSum _ fun β' hβ' => hi β hβ β' hβ', Finset.sum_eq_single β]
  · intro b hb hne
    exact ho β hβ b hb (Ne.symm hne)
  · intro h
    exact absurd hβ h

theorem normSq_sum (B : Finset ℕ) (u : ℕ → Space) :
    ‖∑ β ∈ B, u β‖ ^ 2 = ∑ β ∈ B, ∑ β' ∈ B, inner ℝ (u β) (u β') := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum]

theorem sq_sum (B : Finset ℕ) (u : ℕ → Space → Space) (hu : ∀ β ∈ B, MemLp (u β) 2 volume)
    (ho : ∀ β ∈ B, ∀ β' ∈ B, β ≠ β' → ∫ y, inner ℝ (u β y) (u β' y) = 0) :
    ∫ y, ‖∑ β ∈ B, u β y‖ ^ 2 = ∑ β ∈ B, ∫ y, ‖u β y‖ ^ 2 := by
  simp only [normSq_sum]
  rw [diag_integral B (fun β β' y => inner ℝ (u β y) (u β' y))
    (fun β hβ β' hβ' => inner_integrable (hu β hβ) (hu β' hβ')) ho]
  simp only [real_inner_self_eq_norm_sq]

theorem entrySq_sum (B : Finset ℕ) (D : ℕ → Space →L[ℝ] Space) :
    entrySq (∑ β ∈ B, D β) = ∑ β ∈ B, ∑ β' ∈ B, entryInner (D β) (D β') := by
  unfold entrySq entryInner
  simp only [ContinuousLinearMap.sum_apply, normSq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_comm]

theorem entryInner_self (D : Space →L[ℝ] Space) : entryInner D D = entrySq D := by
  unfold entrySq entryInner
  simp only [real_inner_self_eq_norm_sq]

theorem grad_sum (B : Finset ℕ) (D : ℕ → Space → (Space →L[ℝ] Space))
    (hD : ∀ β ∈ B, ∀ j : Fin 3, MemLp (fun y => D β y (unitVector j)) 2 volume)
    (ho : ∀ β ∈ B, ∀ β' ∈ B, β ≠ β' → ∫ y, entryInner (D β y) (D β' y) = 0) :
    ∫ y, entrySq (∑ β ∈ B, D β y) = ∑ β ∈ B, ∫ y, entrySq (D β y) := by
  simp only [entrySq_sum]
  rw [diag_integral B (fun β β' y => entryInner (D β y) (D β' y)) (fun β hβ β' hβ' => ?_) ho]
  · simp only [entryInner_self]
  · unfold entryInner
    exact integrable_finsetSum _ fun j _ => inner_integrable (hD β hβ j) (hD β' hβ' j)

theorem form_le {lam : ℝ} (hlam : 0 < lam) {φ ψ : Space → Space} {Dψ : Space → (Space →L[ℝ] Space)}
    (h : Adm ψ Dψ) :
    smoothingForm lam φ ≤ (∫ y, ‖φ y - ψ y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (Dψ y) := by
  unfold smoothingForm
  refine csInf_le ⟨0, ?_⟩ ⟨ψ, Dψ, h.1, h.2.1, entrySq_integrable h.2.2.1, h.2.2.2, rfl⟩
  rintro r ⟨ψ', Dψ', -, -, -, -, rfl⟩
  exact add_nonneg (integral_nonneg fun y => sq_nonneg _)
    (mul_nonneg (by positivity) (integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _))


theorem single_cont (i : Fin 3) : Continuous fun a : ℝ => (EuclideanSpace.single i a : Space) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
  by_cases h : j = i
  · subst h
    simp only [Pi.single_eq_same]
    exact continuous_id
  · simp only [Pi.single_eq_of_ne h]
    exact continuous_const

theorem coord_cont (i : Fin 3) : Continuous fun y : Space => y i := by fun_prop

theorem radial_cont : Continuous radialCoord := by
  unfold radialCoord
  fun_prop

theorem angle_meas : Measurable angleCoord :=
  Complex.measurable_arg.comp
    (Complex.equivRealProdCLM.symm.continuous.comp ((coord_cont 0).prodMk (coord_cont 1))).measurable

theorem twoVar_cont (P : Polynomial (Polynomial ℝ)) : Continuous fun p : ℝ × ℝ => twoVarEval P p.1 p.2 := by
  have e : ∀ r z : ℝ, twoVarEval P r z =
      ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j).eval z * r ^ j := by
    intro r z
    rw [twoVarEval, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    simp
  simp only [e]
  exact continuous_finsetSum _ fun j _ =>
    ((P.coeff j).continuous.comp continuous_snd).mul (continuous_fst.pow j)

theorem solid_meas (g : CellBlock) (s : Fin 2) : MeasurableSet (cellSolid g s) := by
  have hz : Continuous fun y : Space => if s = 0 then y 2 else -y 2 := by
    split_ifs
    · exact coord_cont 2
    · exact (coord_cont 2).neg
  exact ((isClosed_le continuous_const radial_cont).inter ((isClosed_le radial_cont continuous_const).inter
    ((isClosed_le continuous_const hz).inter (isClosed_le hz continuous_const)))).measurableSet

theorem trig_meas (t : Fin 2) (m : ℝ) : Measurable fun w : Space => trigMode t (m * angleCoord w) := by
  unfold trigMode
  split_ifs
  · exact Real.measurable_cos.comp (measurable_const.mul angle_meas)
  · exact Real.measurable_sin.comp (measurable_const.mul angle_meas)

theorem frame_meas : ∀ c : Fin 3, Measurable (frameVector c)
  | 0 => ((single_cont 0).measurable.comp (Real.measurable_cos.comp angle_meas)).add
      ((single_cont 1).measurable.comp (Real.measurable_sin.comp angle_meas))
  | 1 => ((single_cont 0).measurable.comp (Real.measurable_sin.comp angle_meas).neg).add
      ((single_cont 1).measurable.comp (Real.measurable_cos.comp angle_meas))
  | 2 => measurable_const

theorem blockField_meas {g : CellBlock} {F : Space → Space} (h : IsBlockField g F) : AEStronglyMeasurable F volume := by
  obtain ⟨A, -, -, hF⟩ := h
  have hS : Measurable fun y => ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
        * twoVarEval (A s c t) (radialCoord w) (w 2)) • frameVector c w) y := by
    refine Finset.measurable_sum _ fun s _ => Measurable.indicator ?_ (solid_meas g s)
    refine Finset.measurable_sum _ fun c _ => ?_
    refine Measurable.smul (f := fun w => ∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
      * twoVarEval (A s c t) (radialCoord w) (w 2)) (g := frameVector c) ?_ (frame_meas c)
    refine Finset.measurable_sum _ fun t _ => Measurable.mul (trig_meas t _) ?_
    exact (twoVar_cont (A s c t)).measurable.comp (radial_cont.measurable.prodMk (coord_cont 2).measurable)
  exact hS.aestronglyMeasurable.congr (hF.mono fun y hy => hy.symm)

variable {k N : ℕ} {c : FracCellData k N} {sd : SpectralData}

theorem row_memLp (hsd : IsSpectralData c sd) (a : Fin N) : MemLp (c.row a) 2 volume := by
  have hm := blockField_meas (hsd.rows_in_blocks a)
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have h1 := hsd.rows_orthonormal a a
  simp only [if_true, l2Pair] at h1
  have hi : Integrable fun y => inner ℝ (c.row a y) (c.row a y) := by
    by_contra hn
    rw [integral_undef hn] at h1
    norm_num at h1
  simpa only [real_inner_self_eq_norm_sq] using hi

theorem part_memLp (hsd : IsSpectralData c sd) (x : Fin N → ℝ) (β : ℕ) :
    MemLp (blockPart c x β) 2 volume := by
  unfold blockPart
  exact memLp_finsetSum _ fun b _ => (row_memLp hsd b).const_smul (x b)

theorem pairingMat (hsd : IsSpectralData c sd) (x : Fin N → ℝ) (S T : Finset (Fin N)) :
    ∫ y, inner ℝ (∑ a ∈ S, x a • c.row a y) (∑ b ∈ T, x b • c.row b y)
      = ∑ a ∈ S, ∑ b ∈ T, x a * x b * (if a = b then 1 else 0) := by
  have e : ∀ y, inner ℝ (∑ a ∈ S, x a • c.row a y) (∑ b ∈ T, x b • c.row b y)
      = ∑ a ∈ S, ∑ b ∈ T, x a * x b * inner ℝ (c.row a y) (c.row b y) := by
    intro y
    rw [sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp only [e]
  have hi : ∀ a b, Integrable fun y => x a * x b * inner ℝ (c.row a y) (c.row b y) :=
    fun a b => (inner_integrable (row_memLp hsd a) (row_memLp hsd b)).const_mul _
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hi a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ fun b _ => hi a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, ← hsd.rows_orthonormal a b, l2Pair]

theorem part_orth (hsd : IsSpectralData c sd) (x : Fin N → ℝ) {β β' : ℕ} (h : β ≠ β') :
    ∫ y, inner ℝ (blockPart c x β y) (blockPart c x β' y) = 0 := by
  unfold blockPart
  rw [pairingMat hsd]
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  have hab : a ≠ b := by
    rintro rfl
    exact h ((Finset.mem_filter.1 ha).2.symm.trans (Finset.mem_filter.1 hb).2)
  simp [hab]

theorem part_norm (hsd : IsSpectralData c sd) (x : Fin N → ℝ) (β : ℕ) :
    ∫ y, ‖blockPart c x β y‖ ^ 2 = ∑ b ∈ Finset.univ.filter (fun b => c.blockIndex b = β), x b ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq]
  unfold blockPart
  rw [pairingMat hsd]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos ha]
  ring

theorem piece_of_approx (h6 : BlockApproxStatement) : BlockPieceStatement := by
  intro k N c sd hsd lam hlam x
  classical
  obtain ⟨ψ, Dψ, hadm, horth, hbd⟩ := h6 c sd hsd lam hlam x
  set B : Finset ℕ := Finset.univ.image c.blockIndex with hB
  let P : ℕ → Prop := fun β => β ∈ B ∧ blockInnerValue sd β lam < 1
  let ψ' : ℕ → Space → Space := fun β => if P β then ψ β else fun _ => 0
  let D' : ℕ → Space → (Space →L[ℝ] Space) := fun β => if P β then Dψ β else fun _ => 0
  have eψ : ∀ β, P β → ψ' β = ψ β := fun β hp => if_pos hp
  have eψ0 : ∀ β, ¬P β → ψ' β = fun _ => 0 := fun β hp => if_neg hp
  have eD : ∀ β, P β → D' β = Dψ β := fun β hp => if_pos hp
  have eD0 : ∀ β, ¬P β → D' β = fun _ => 0 := fun β hp => if_neg hp
  have hadm' : ∀ β, MemLp (ψ' β) 2 volume ∧ AEStronglyMeasurable (D' β) volume ∧
      Integrable (fun y => entrySq (D' β y)) ∧ IsWeakGradientOf (ψ' β) (D' β) := by
    intro β
    by_cases hp : P β
    · rw [eψ β hp, eD β hp]
      exact hadm β
    · rw [eψ0 β hp, eD0 β hp]
      refine ⟨MemLp.zero', aestronglyMeasurable_const, ?_, fun φ _ j => by simp⟩
      simp [entrySq]
  have o1 : ∀ β β', β ≠ β' → ∫ y, inner ℝ (blockPart c x β y) (ψ' β' y) = 0 := by
    intro β β' h
    by_cases hp : P β'
    · rw [eψ β' hp]
      exact (horth β β' h).1
    · rw [eψ0 β' hp]
      simp
  have o2 : ∀ β β', β ≠ β' → ∫ y, inner ℝ (ψ' β y) (ψ' β' y) = 0 := by
    intro β β' h
    by_cases hp : P β
    · by_cases hq : P β'
      · rw [eψ β hp, eψ β' hq]
        exact (horth β β' h).2.1
      · rw [eψ0 β' hq]
        simp
    · rw [eψ0 β hp]
      simp
  have o3 : ∀ β β', β ≠ β' → ∫ y, entryInner (D' β y) (D' β' y) = 0 := by
    intro β β' h
    by_cases hp : P β
    · by_cases hq : P β'
      · rw [eD β hp, eD β' hq]
        exact (horth β β' h).2.2
      · rw [eD0 β' hq]
        simp [entryInner]
    · rw [eD0 β hp]
      simp [entryInner]
  refine ⟨ψ', D', fun β => ⟨(hadm' β).1, (hadm' β).2.1, (hadm' β).2.2.1, (hadm' β).2.2.2,
    (part_memLp hsd x β).sub (hadm' β).1⟩, fun β β' h => ⟨?_, o3 β β' h⟩, fun β => ?_⟩
  · have I1 := inner_integrable (part_memLp hsd x β) (part_memLp hsd x β')
    have I2 := inner_integrable (part_memLp hsd x β) (hadm' β').1
    have I3 := inner_integrable (hadm' β).1 (part_memLp hsd x β')
    have I4 := inner_integrable (hadm' β).1 (hadm' β').1
    have ec : (fun y => inner ℝ (ψ' β y) (blockPart c x β' y)) =
        fun y => inner ℝ (blockPart c x β' y) (ψ' β y) := funext fun y => real_inner_comm _ _
    simp only [inner_sub_left, inner_sub_right]
    rw [integral_sub, integral_sub I1 I3, integral_sub I2 I4, ec,
      part_orth hsd x h, o1 β β' h, o1 β' β (Ne.symm h), o2 β β' h]
    · ring
    · exact I1.sub I3
    · exact I2.sub I4
  · rw [blockSpectral_eq_min_inner, ← part_norm hsd x β]
    by_cases hp : P β
    · rw [eψ β hp, eD β hp, min_eq_right hp.2.le]
      exact hbd β hp.1 hp.2
    · rw [eψ0 β hp, eD0 β hp]
      have ez : (fun y : Space => entrySq ((fun _ : Space => (0 : Space →L[ℝ] Space)) y)) = fun _ => 0 := by
        funext y
        simp [entrySq]
      simp only [sub_zero]
      rw [ez, integral_zero, mul_zero, add_zero]
      by_cases hβ : β ∈ B
      · have hn : ¬ blockInnerValue sd β lam < 1 := fun h => hp ⟨hβ, h⟩
        rw [min_eq_left (not_lt.1 hn), one_mul]
      · have hz : ∀ y, blockPart c x β y = 0 := by
          intro y
          unfold blockPart
          refine Finset.sum_eq_zero fun b hb => ?_
          exact absurd ((Finset.mem_filter.1 hb).2 ▸ Finset.mem_image_of_mem c.blockIndex (Finset.mem_univ b)) hβ
        simp [hz]

end Internal.SpectralBlocks

open Internal.SpectralBlocks

theorem blockBound_of (h1 : IntervalIdentityStatement) (h2 : IntervalMinimalStatement)
    (h3 : IntervalMonotoneStatement) (h4 : IntervalClosedStatement) (h5 : AxisClosedStatement)
    (h6 : BlockApproxStatement) : BlockBoundStatement := by
  intro k N c sd hsd lam hlam x
  obtain ⟨ψ, Dψ, hadm, horth, hbd⟩ := piece_of_approx h6 c sd hsd lam hlam x
  set B : Finset ℕ := Finset.univ.image c.blockIndex with hB
  have hmaps : ∀ b ∈ (Finset.univ : Finset (Fin N)), c.blockIndex b ∈ B :=
    fun b _ => Finset.mem_image_of_mem _ (Finset.mem_univ b)
  have hA : ∀ β ∈ B, Adm (ψ β) (Dψ β) := fun β _ =>
    ⟨(hadm β).1, (hadm β).2.1, comp_memLp (hadm β).2.1 (hadm β).2.2.1, (hadm β).2.2.2.1⟩
  have hle := form_le (φ := fun y => ∑ b, x b • c.row b y) hlam (adm_sum ψ Dψ B hA)
  have ephi : ∀ y, (∑ b, x b • c.row b y) - ∑ β ∈ B, ψ β y = ∑ β ∈ B, (blockPart c x β y - ψ β y) := by
    intro y
    rw [Finset.sum_sub_distrib]
    congr 1
    unfold blockPart
    exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  simp only [ephi] at hle
  rw [sq_sum B (fun β y => blockPart c x β y - ψ β y) (fun β _ => (hadm β).2.2.2.2)
      (fun β _ β' _ hne => (horth β β' hne).1),
    grad_sum B Dψ (fun β hβ => (hA β hβ).2.2.1) (fun β _ β' _ hne => (horth β β' hne).2),
    Finset.mul_sum, ← Finset.sum_add_distrib] at hle
  refine hle.trans ((Finset.sum_le_sum fun β _ => hbd β).trans (le_of_eq ?_))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [(Finset.mem_filter.1 hb).2]

end Spectral

end CellCert

end Breakdown
