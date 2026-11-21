import Breakdown.FracCell.CellSystemDefs

open scoped ContDiff

namespace Breakdown.CellCert.GivenFields

@[fun_prop] theorem ofReal_cd {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (fun b => (f b : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

@[fun_prop] theorem ofReal_cd' : ContDiff ℝ 2 (fun b : ℝ => (b : ℂ)) :=
  Complex.ofRealCLM.contDiff

private theorem reduced_contDiff (P : ChartParams) (F : FieldData) (n : ℤ) (t x : ℝ) (i : Fin 3) :
    ContDiff ℝ 2 (fun b : ℝ => reducedField P F n b t x i) := by
  by_cases hn : n = 0
  · subst hn
    simp only [reducedField, if_true, twistedScale, radialScale]
    fin_cases i <;> simp <;> fun_prop
  · simp only [reducedField, hn, if_false, twistedScale, radialScale]
    fin_cases i <;> simp <;> fun_prop

private theorem fieldOf_contDiff (P : ChartParams) (F : FieldData) (y : Space) :
    ContDiff ℝ 2 (fun b : ℝ => fieldOf P F b y) := by
  have hr := reduced_contDiff P F
  unfold fieldOf ofComponents modePhase
  have hc : ∀ i : Fin 3, ContDiff ℝ 2 (fun b : ℝ => ((decayFactor P y : ℂ) * ∑ n ∈ F.modes,
      Complex.exp (Complex.I * (((n * P.m : ℤ) : ℝ) * angleOf y + n * b * logPhase P y : ℝ)) *
      (reducedField P F n b (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P F n b (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P F n b (chartT P y) (heightRatio y) 2 * azimVecQ y i)).re) := by
    intro i
    let g : ℝ → ℂ := fun b => (decayFactor P y : ℂ) * ∑ n ∈ F.modes,
      Complex.exp (Complex.I * (((n * P.m : ℤ) : ℝ) * angleOf y + n * b * logPhase P y : ℝ)) *
      (reducedField P F n b (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P F n b (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P F n b (chartT P y) (heightRatio y) 2 * azimVecQ y i)
    change ContDiff ℝ 2 (fun b => Complex.reCLM (g b))
    refine Complex.reCLM.contDiff.comp (?_ : ContDiff ℝ 2 g)
    refine contDiff_const.mul ?_
    refine ContDiff.sum (fun n _ => ?_)
    refine ContDiff.mul ?_ ?_
    · refine Complex.contDiff_exp.comp ?_
      refine contDiff_const.mul ?_
      refine Complex.ofRealCLM.contDiff.comp ?_
      exact contDiff_const.add ((contDiff_const.mul contDiff_id).mul contDiff_const)
    · have h0 := hr n (chartT P y) (heightRatio y) 0
      have h1 := hr n (chartT P y) (heightRatio y) 1
      have h2 := hr n (chartT P y) (heightRatio y) 2
      exact ((h0.mul contDiff_const).add (h1.mul contDiff_const)).add (h2.mul contDiff_const)
  have hs : ∀ (j : Fin 3) (r : ℝ), (EuclideanSpace.single j r : Space) = r • EuclideanSpace.single j 1 := by
    intro j r
    ext i
    rw [PiLp.smul_apply, PiLp.single_apply, PiLp.single_apply]
    split_ifs <;> simp
  have hs' : ∀ j : Fin 3, ContDiff ℝ 2 (fun r : ℝ => (EuclideanSpace.single j r : Space)) := by
    intro j
    have e : (fun r : ℝ => (EuclideanSpace.single j r : Space)) = fun r => r • EuclideanSpace.single j 1 := funext (hs j)
    rw [e]
    fun_prop
  exact (((hs' 0).comp (hc 0)).add ((hs' 1).comp (hc 1))).add ((hs' 2).comp (hc 2))

private theorem phaseCurv_genuine (P : ChartParams) (F : FieldData) (β : ℝ) (y : Space) :
    HasDerivAt (Breakdown.CellCert.CellSystem.phaseDerivField P F · y)
      (Breakdown.CellCert.CellSystem.phaseCurvField P F β y) β := by
  have h := fieldOf_contDiff P F y
  have h1 : ContDiff ℝ 1 (deriv (fun b : ℝ => fieldOf P F b y)) := by
    have h' : ContDiff ℝ (1 + 1) (fun b : ℝ => fieldOf P F b y) := by rw [one_add_one_eq_two]; exact h
    exact ((contDiff_succ_iff_deriv (n := 1)).1 h').2.2
  have hd : Differentiable ℝ (deriv (fun b : ℝ => fieldOf P F b y)) := h1.differentiable (by norm_num)
  exact (hd β).hasDerivAt

end Breakdown.CellCert.GivenFields

namespace Breakdown.CellCert.CellSystem

private theorem expansion_end {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    (hg : ContDiff ℝ 2 g) (s δ C : ℝ)
    (hC : ∀ t, |t - s| ≤ |δ| → ‖deriv (deriv g) t‖ ≤ C) :
    ‖g (s + δ) - δ • deriv g (s + δ) - g s‖ ≤ δ ^ 2 / 2 * C := by
  have hg' : ContDiff ℝ (1 + 1) g := by rw [one_add_one_eq_two]; exact hg
  have h1 : ContDiff ℝ 1 (deriv g) := ((contDiff_succ_iff_deriv (n := 1)).1 hg').2.2
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd : Differentiable ℝ (deriv g) := h1.differentiable (by norm_num)
  set F : ℝ → E := fun u => g (s + u * δ) - (u * δ) • deriv g (s + u * δ) - g s with hF
  set F' : ℝ → E := fun u => -((u * δ ^ 2) • deriv (deriv g) (s + u * δ)) with hF'
  have hder : ∀ u, HasDerivAt F (F' u) u := by
    intro u
    have ha : HasDerivAt (fun u : ℝ => s + u * δ) δ u := by
      simpa using ((hasDerivAt_id u).mul_const δ).const_add s
    have hg1 : HasDerivAt (fun u => g (s + u * δ)) (δ • deriv g (s + u * δ)) u :=
      (hgd (s + u * δ)).hasDerivAt.scomp u ha
    have hg2 : HasDerivAt ((deriv g) ∘ (fun u : ℝ => s + u * δ)) (δ • deriv (deriv g) (s + u * δ)) u :=
      HasDerivAt.scomp u (hd (s + u * δ)).hasDerivAt ha
    have hm : HasDerivAt (fun u : ℝ => u * δ) δ u := by simpa using (hasDerivAt_id u).mul_const δ
    have hp := hm.smul hg2
    have := (hg1.sub hp).sub_const (g s)
    refine this.congr_deriv ?_
    show _ = -((u * δ ^ 2) • deriv (deriv g) (s + u * δ))
    simp only [Function.comp_apply]
    module
  have hcont : Continuous F := by
    refine Continuous.sub (Continuous.sub ?_ ?_) continuous_const
    · exact hgd.continuous.comp (by fun_prop)
    · exact (continuous_id.mul continuous_const).smul (hd.continuous.comp (by fun_prop))
  have hB : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖F u‖ ≤ δ ^ 2 * C * u ^ 2 / 2 := by
    intro u hu
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := F) (f' := F')
      (B := fun u => δ ^ 2 * C * u ^ 2 / 2) (B' := fun u => δ ^ 2 * C * u)
      hcont.continuousOn (fun x _ => (hder x).hasDerivWithinAt) ?_
      (fun x => ?_) (fun x hx => ?_) hu
    · simp [hF]
    · have := ((hasDerivAt_pow 2 x).const_mul (δ ^ 2 * C)).div_const 2
      refine this.congr_deriv ?_
      first | (norm_num; done) | (norm_num; ring)
    · have hx0 : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := hx.2.le
      have hb : ‖deriv (deriv g) (s + x * δ)‖ ≤ C := by
        apply hC
        rw [show s + x * δ - s = x * δ by ring, abs_mul, abs_of_nonneg hx0]
        nlinarith [abs_nonneg δ]
      simp only [hF', norm_neg, norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : 0 ≤ x * δ ^ 2)]
      calc x * δ ^ 2 * ‖deriv (deriv g) (s + x * δ)‖ ≤ x * δ ^ 2 * C :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = δ ^ 2 * C * x := by ring
  have := hB 1 ⟨zero_le_one, le_rfl⟩
  simpa [hF] using this.trans (le_of_eq (by ring))

end Breakdown.CellCert.CellSystem

open scoped ContDiff

namespace Breakdown.CellCert.CellSystem

open GivenFields

private theorem phase_split {k : ℕ} (D : ProfileData k) (step : Fin k → ℝ)
    (hstep : ∀ i, step i = -(2 * D.power * (D.chart.m : ℝ) * D.rateSlope i)) (p : Fin k → ℝ) :
    D.phase p = D.phase 0 + ∑ i, step i * p i := by
  simp only [ProfileData.phase, ProfileData.rate, hstep, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rw [mul_add, Finset.mul_sum, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => by ring)

private theorem sum_one {k : ℕ} (μ : Fin k → ℕ) (h : ∑ i, μ i = 1) : ∃ i, μ = Pi.single i 1 := by
  have : ∃ i, μ i ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at h
  obtain ⟨i, hi⟩ := this
  refine ⟨i, funext fun j => ?_⟩
  have hle : μ i ≤ 1 := h ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hi1 : μ i = 1 := by omega
  by_cases hj : j = i
  · subst hj; simp [hi1]
  · have hsum := Finset.add_sum_erase Finset.univ μ (Finset.mem_univ i)
    rw [h, hi1] at hsum
    have h0 : ∑ x ∈ Finset.univ.erase i, μ x = 0 := by omega
    have := (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
    simp [this, Pi.single_apply, hj]

private theorem centreSup {k : ℕ} (D : ProfileData k) (step rad ampS : Fin k → ℝ) (higherS : (Fin k → ℕ) → ℝ)
    (curvS range : ℝ)
    (hstep : ∀ i, step i = -(2 * D.power * (D.chart.m : ℝ) * D.rateSlope i))
    (hwidth : splitWidth rad step ≤ range)
    (hzero : (0 : Fin k → ℕ) ∈ D.index)
    (hamp_index : ∀ i, Pi.single i 1 ∈ D.index)
    (amp_sup : ∀ i, ∀ β, |β - D.phase 0| ≤ range → ∀ y, ‖ampField D step i β y‖ ≤ ampS i)
    (higher_sup : ∀ μ ∈ D.index, 2 ≤ ∑ i, μ i → ∀ β, |β - D.phase 0| ≤ range →
      ∀ y, ‖fieldOf D.chart (D.part μ) β y‖ ≤ higherS μ)
    (curv_sup : ∀ β, |β - D.phase 0| ≤ range → ∀ y, ‖phaseCurvField D.chart (D.part 0) β y‖ ≤ curvS) :
    ∀ p ∈ SteadyCert.box rad, ∀ y, ‖D.profile p y - D.profile 0 y‖ ≤
      ∑ i, rad i * ampS i + ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), (∏ i, rad i ^ μ i) * higherS μ
        + splitWidth rad step ^ 2 / 2 * curvS := by
  intro p hp y
  have hrad : ∀ i, |p i| ≤ rad i := hp
  have hrad0 : ∀ i, 0 ≤ rad i := fun i => (abs_nonneg _).trans (hrad i)
  set W : (Fin k → ℕ) → ℝ → Space := fun μ β => fieldOf D.chart (D.part μ) β y with hW
  set δ : ℝ := ∑ i, step i * p i with hδdef
  have hphase : D.phase p = D.phase 0 + δ := phase_split D step hstep p
  have hsw0 : 0 ≤ splitWidth rad step :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hrad0 i))
  have hδ : |δ| ≤ splitWidth rad step := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hrad i) (abs_nonneg _)
  have hrange : |D.phase p - D.phase 0| ≤ range := by
    rw [hphase, add_sub_cancel_left]; exact hδ.trans hwidth
  have hmono0 : ∀ μ : Fin k → ℕ, μ ≠ 0 → ProfileData.monomialOf (0 : Fin k → ℝ) μ = 0 := by
    intro μ hμ
    obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
      by_contra hc; push_neg at hc; exact hμ (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [zero_pow hj])
  have hp0 : D.profile 0 y = W 0 (D.phase 0) := by
    unfold ProfileData.profile
    rw [Finset.sum_eq_single (0 : Fin k → ℕ)]
    · simp [ProfileData.monomialOf, hW]
    · intro μ _ hμ; rw [hmono0 μ hμ, zero_smul]
    · intro h; exact absurd hzero h
  have hlow : D.index.filter (fun μ => ¬ 2 ≤ ∑ i, μ i) =
      insert (0 : Fin k → ℕ) (Finset.univ.image (fun i : Fin k => (Pi.single i 1 : Fin k → ℕ))) := by
    ext μ
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_le]
    constructor
    · rintro ⟨_, hlt⟩
      rcases Nat.lt_succ_iff.1 (Nat.lt_succ_iff.2 (Nat.lt_succ_iff.1 hlt)) |> Nat.le_one_iff_eq_zero_or_eq_one.1 with h0 | h1
      · left; funext j; exact (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_univ j)
      · right; obtain ⟨i, hi⟩ := sum_one μ h1; exact ⟨i, hi.symm⟩
    · rintro (h | ⟨i, rfl⟩)
      · subst h; exact ⟨hzero, by simp⟩
      · exact ⟨hamp_index i, by simp [Finset.sum_pi_single']⟩
  have hnot : (0 : Fin k → ℕ) ∉ Finset.univ.image (fun i : Fin k => (Pi.single i 1 : Fin k → ℕ)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i h
    have := congrFun h i
    simp at this
  have hinj : Set.InjOn (fun i : Fin k => (Pi.single i 1 : Fin k → ℕ)) (Finset.univ : Finset (Fin k)) := by
    intro i _ j _ h
    by_contra hij
    have := congrFun h i
    simp [Pi.single_apply, hij] at this
  have hmono1 : ∀ i, ProfileData.monomialOf p (Pi.single i 1) = p i := by
    intro i
    unfold ProfileData.monomialOf
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  have hpp : D.profile p y = W 0 (D.phase p) + ∑ i, p i • W (Pi.single i 1) (D.phase p)
      + ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), ProfileData.monomialOf p μ • W μ (D.phase p) := by
    unfold ProfileData.profile
    rw [← Finset.sum_filter_add_sum_filter_not D.index (fun μ => 2 ≤ ∑ i, μ i), add_comm, hlow,
      Finset.sum_insert hnot, Finset.sum_image hinj]
    simp only [hmono1]
    have : ProfileData.monomialOf p (0 : Fin k → ℕ) = 1 := by simp [ProfileData.monomialOf]
    rw [this, one_smul]
  set T1 : Space := ∑ i, p i • ampField D step i (D.phase p) y with hT1def
  set T2 : Space := ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), ProfileData.monomialOf p μ • W μ (D.phase p) with hT2def
  set T3 : Space := W 0 (D.phase 0 + δ) - δ • phaseDerivField D.chart (D.part 0) (D.phase 0 + δ) y - W 0 (D.phase 0) with hT3def
  have hT1 : T1 = ∑ i, p i • W (Pi.single i 1) (D.phase p) + δ • phaseDerivField D.chart (D.part 0) (D.phase p) y := by
    rw [hT1def]
    simp only [ampField, smul_add, Finset.sum_add_distrib, hW]
    congr 1
    rw [hδdef, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul, mul_comm]
  have hsplit : D.profile p y - D.profile 0 y = T1 + T2 + T3 := by
    rw [hpp, hp0, hT1, hT3def, ← hphase]
    abel
  have h1 : ‖T1‖ ≤ ∑ i, rad i * ampS i := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hrad i) (amp_sup i _ hrange y) (norm_nonneg _) (hrad0 i)
  have h2 : ‖T2‖ ≤ ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), (∏ i, rad i ^ μ i) * higherS μ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun μ hμ => ?_))
    rw [Finset.mem_filter] at hμ
    rw [norm_smul, Real.norm_eq_abs]
    have hm : |ProfileData.monomialOf p μ| ≤ ∏ i, rad i ^ μ i := by
      unfold ProfileData.monomialOf
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hrad i) _)
    exact mul_le_mul hm (higher_sup μ hμ.1 hμ.2 _ hrange y) (norm_nonneg _)
      (Finset.prod_nonneg (fun i _ => pow_nonneg (hrad0 i) _))
  have hcurv0 : 0 ≤ curvS :=
    (norm_nonneg _).trans (curv_sup (D.phase 0) (by simpa using hsw0.trans hwidth) y)
  have h3 : ‖T3‖ ≤ splitWidth rad step ^ 2 / 2 * curvS := by
    have ht := expansion_end (fun b => fieldOf D.chart (D.part 0) b y)
      (GivenFields.fieldOf_contDiff _ _ y) (D.phase 0) δ curvS
      (fun t ht => curv_sup t ((ht.trans hδ).trans hwidth) y)
    refine ht.trans ?_
    have hsq : δ ^ 2 ≤ splitWidth rad step ^ 2 := sq_le_sq' (abs_le.1 hδ).1 (abs_le.1 hδ).2
    nlinarith
  rw [hsplit]
  calc ‖T1 + T2 + T3‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ := norm_add₃_le
    _ ≤ _ := by linarith

end Breakdown.CellCert.CellSystem

namespace Breakdown.CellCert.CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula

theorem centreSupSplit_of {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X) :
    ∀ p ∈ box c.radius, ∀ y, ‖c.profile p y - c.centre y‖ ≤ X.centreSup p := by
  intro p hp y
  have hprof : c.profile = D.profile := h.given.profile_instance.profile_eq
  have hcen : c.centre = D.profile 0 := h.given.centre_instance.centre_eq
  rw [h.losses.centreSup_eq p, hprof, hcen]
  exact centreSup D X.splitStep c.radius X.ampSup X.higherSup X.curvSup X.splitRange
    h.losses.split_step h.losses.split_width h.given.profile.index_zero h.losses.amp_index
    h.losses.amp_sup h.losses.higher_sup h.losses.curv_sup p hp y

end Breakdown.CellCert.CellSystem
