import Breakdown.CertCell.AssemblyTreeStateHead

open Matrix MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace TreeStateInternal

open CellCalculus CellCert.CellFormula CellCert.Finite

theorem quadValue_add_left {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (M + N) x = quadValue M x + quadValue N x := by
  simp [quadValue, add_mulVec, dotProduct_add]

theorem quadValue_neg_left {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (-M) x = -quadValue M x := by
  simp [quadValue, neg_mulVec, dotProduct_neg]

theorem quadValue_sum_left {ι κ : Type*} [Fintype ι] (s : Finset κ) (M : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (∑ l ∈ s, M l) x = ∑ l ∈ s, quadValue (M l) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadValue]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, quadValue_add_left, ih]

theorem quadValue_nsmul_left {ι : Type*} [Fintype ι] (n : ℕ) (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (n • M) x = n * quadValue M x := by
  induction n with
  | zero => simp [quadValue]
  | succ n ih =>
    rw [succ_nsmul, quadValue_add_left, ih]
    push_cast
    ring

theorem quadFormValue_add_left {ι : Type} [Fintype ι] (M N : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadFormValue (M + N) x = quadFormValue M x + quadFormValue N x := by
  simp [quadFormValue, add_mulVec, dotProduct_add]

theorem quadFormValue_sum_left {ι κ : Type} [Fintype ι] (s : Finset κ) (M : κ → Matrix ι ι ℂ) (x : ι → ℂ) :
    quadFormValue (∑ l ∈ s, M l) x = ∑ l ∈ s, quadFormValue (M l) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadFormValue]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, quadFormValue_add_left, ih]

theorem quadValue_realLeafForm_eq {n A : Type} [Fintype n] [Fintype A] (P : Matrix n A ℂ) (Ψ : Matrix n n ℂ)
    (y : A → ℝ) : quadValue (realLeafForm P Ψ) y = quadFormValue Ψ (P *ᵥ fun a => (y a : ℂ)) := by
  have hstar : star (fun a => (y a : ℂ)) = fun a => (y a : ℂ) := by
    funext a
    simp
  have h1 : star (P *ᵥ fun a => (y a : ℂ)) ⬝ᵥ (Ψ *ᵥ (P *ᵥ fun a => (y a : ℂ)))
      = (fun a => (y a : ℂ)) ⬝ᵥ ((P.conjTranspose * Ψ * P) *ᵥ fun a => (y a : ℂ)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hstar]
  unfold quadFormValue
  rw [h1]
  simp [quadValue, realLeafForm, dotProduct, mulVec, Complex.re_sum]

theorem quadFormValue_add_null {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (s g : ι → ℂ)
    (h1 : M *ᵥ g = 0) (h2 : Mᴴ *ᵥ g = 0) : quadFormValue M (s + g) = quadFormValue M s := by
  have h3 : star g ᵥ* M = 0 := by
    have h := congrArg star h2
    rw [Matrix.star_mulVec, conjTranspose_conjTranspose] at h
    simpa using h
  unfold quadFormValue
  rw [star_add, mulVec_add, h1, add_zero, add_dotProduct, Matrix.dotProduct_mulVec (star g), h3,
    zero_dotProduct, add_zero]

theorem quadFormValue_eq_of_null_coords {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (u u' : ι → ℂ)
    (h : ∀ i, u i = u' i ∨ ∀ j, M i j = 0 ∧ M j i = 0) : quadFormValue M u = quadFormValue M u' := by
  unfold quadFormValue
  congr 1
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases h i with hi | hi
  · rcases h j with hj | hj
    · rw [hi, hj]
    · rw [(hj i).2]
      simp
  · rw [(hi j).1]
    simp

section Tree

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem sum_pieceForm_eq {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (K : Fin D.mesh.count) :
    (haveI := T.partFintype K; ∑ j, ∑ j', T.pieceForm K j j') = R.cellForm K := by
  letI := T.partFintype K
  funext a b
  classical
  simp only [Matrix.sum_apply, TreeEntry.pieceForm]
  rw [Finset.sum_eq_single (T.partOf K a)]
  · rw [Finset.sum_eq_single (T.partOf K b)]
    · simp
    · intro j' _ hj'
      simp [Ne.symm hj']
    · simp
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro j' _
    simp [Ne.symm hj]
  · simp

theorem quadValue_totalForm_eq {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (T : TreeEntry D R)
    (front : T.Node → Matrix (T.Slaved ⊕ T.Free) (T.Slaved ⊕ T.Free) ℝ) (y : T.Slaved ⊕ T.Free → ℝ) :
    (haveI := T.slavedFintype; haveI := T.freeFintype;
      quadValue (T.tree front).totalForm y
        = quadValue T.globalLeaf y + ∑ K, quadFormValue (R.cellForm K) (T.embed K *ᵥ fun a => (y a : ℂ))
          + 2 * ∑ j, quadFormValue (R.creditPatch j).credit (T.creditEmbed j *ᵥ fun a => (y a : ℂ))) := by
  letI := T.slavedFintype
  letI := T.freeFintype
  letI := T.nullPairFintype
  letI := T.partFintype
  unfold Certificate.SignedTree.totalForm
  rw [quadValue_sum_left]
  change ∑ l : T.Leaf, quadValue (T.leafForm l) y = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_sigma]
  have hnull : ∑ pb : T.NullPair × Bool, quadValue (T.leafForm (Sum.inl (Sum.inr pb))) y = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro p _
    rw [Fintype.sum_bool]
    simp only [TreeEntry.leafForm, quadValue_neg_left]
    ring
  rw [hnull, add_zero]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro K _
    rw [← sum_pieceForm_eq T K, Fintype.sum_prod_type]
    simp only [TreeEntry.leafForm, quadValue_realLeafForm_eq]
    rw [quadFormValue_sum_left]
    apply Finset.sum_congr rfl
    intro j _
    rw [quadFormValue_sum_left]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [TreeEntry.leafForm]
    rw [quadValue_nsmul_left, quadValue_realLeafForm_eq]
    norm_num

end Tree


section Rows

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}
  {T : TreeEntry D R}

theorem unusedRow_of_unused {e : ℝ} (W : RowEntry D R T) (hT : TreeRowConditions D R e T W) (K : Fin D.mesh.count)
    (d : CellVar D.mesh K (R.layouts K)) (hu : (W.reason K d).IsUnused) : W.UnusedRow K d := by
  have hj := hT.justified K d
  unfold RowEntry.Accounted at hj
  generalize W.reason K d = w at hj hu
  cases w
  all_goals first | exact hj | exact False.elim hu

theorem rowEmbed_apply_cell (W : RowEntry D R T) (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (f : T.Slaved → ℝ) (g : T.Free → ℝ) :
    (haveI := T.slavedFintype; haveI := T.freeFintype;
      (W.rowEmbed K *ᵥ fun a => ((Sum.elim f g a : ℝ) : ℂ)) (Sum.inl (Sum.inl d))) = W.rowValue K d f := by
  letI := T.slavedFintype
  letI := T.freeFintype
  classical
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, RowEntry.rowEmbed, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, add_zero, RowEntry.rowValue, RowEntry.rowVec, ite_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

open Classical in
theorem rowEmbed_apply_port (W : RowEntry D R T) (K : Fin D.mesh.count) (j : Fin (R.portCount K))
    (f : T.Slaved → ℝ) (g : T.Free → ℝ) :
    (haveI := T.slavedFintype; haveI := T.freeFintype;
      (W.rowEmbed K *ᵥ fun a => ((Sum.elim f g a : ℝ) : ℂ)) (Sum.inl (Sum.inr j)))
      = (haveI := T.freeFintype; ∑ b : T.Free, ((if b = W.portRe (R.portKey K j) then 1 else 0)
        + (if W.portIm (R.portKey K j) = some b then (if W.portConj (R.portKey K j) then -Complex.I else Complex.I)
          else 0)) * ((g b : ℝ) : ℂ)) := by
  letI := T.slavedFintype
  letI := T.freeFintype
  classical
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, RowEntry.rowEmbed, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, zero_add]

theorem rowEmbed_apply_kappa (W : RowEntry D R T) (K : Fin D.mesh.count) (i : Fin k)
    (f : T.Slaved → ℝ) (g : T.Free → ℝ) :
    (haveI := T.slavedFintype; haveI := T.freeFintype;
      (W.rowEmbed K *ᵥ fun a => ((Sum.elim f g a : ℝ) : ℂ)) (Sum.inr (Sum.inl i))) = ((f (W.kappa i) : ℝ) : ℂ) := by
  letI := T.slavedFintype
  letI := T.freeFintype
  classical
  simp [mulVec, dotProduct, Fintype.sum_sum_type, RowEntry.rowEmbed]

theorem rowEmbed_apply_zeta (W : RowEntry D R T) (K : Fin D.mesh.count) (i : Fin k)
    (f : T.Slaved → ℝ) (g : T.Free → ℝ) :
    (haveI := T.slavedFintype; haveI := T.freeFintype;
      (W.rowEmbed K *ᵥ fun a => ((Sum.elim f g a : ℝ) : ℂ)) (Sum.inr (Sum.inr i))) = ((g (W.zeta i) : ℝ) : ℂ) := by
  letI := T.slavedFintype
  letI := T.freeFintype
  classical
  simp [mulVec, dotProduct, Fintype.sum_sum_type, RowEntry.rowEmbed]

end Rows

section Geometry

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}

theorem presSegments_off_axis (hC : CellCalculusConditions D R) (K : Fin D.mesh.count) (ι : ℤ × ℤ)
    (hι : ι ∈ D.mesh.resolved K) (s : Fin ((R.layouts K).layout ι).presCount)
    (hr : (((R.layouts K).layout ι).presSegment s).radial = true) :
    0 < min (((R.layouts K).layout ι).presSegment s).level (((R.layouts K).layout ι).presSegment s).other ∨
      (((R.layouts K).layout ι).presSegment s).other = 0 := by
  obtain ⟨c, S, -, -, hLay⟩ := (hC.layouts_valid K).layout_valid ι hι
  have hbox := hLay.box_valid
  rw [← hLay.box_eq] at hbox
  obtain ⟨hseg, hne⟩ := hC.pressure_placed K ι hι
  have hl := hne s hr
  have ho := (hseg.2.2.2.2.1 s hr).2.2
  have h0 := hbox.r_order.1
  have h1 := hbox.r_order.2
  rcases hseg.1 s with ⟨_, hlev⟩ | ⟨hnr, _⟩
  · rcases hlev with hlev | hlev
    · left
      rw [hlev] at hl
      rw [ho, hlev]
      have : 0 < ((R.layouts K).layout ι).box.r₁ := lt_of_le_of_ne h0 (Ne.symm hl)
      exact lt_min (by linarith) (by linarith)
    · rcases eq_or_lt_of_le h0 with hz | hpos
      · right
        rw [ho, hlev, ← hz]
        ring
      · left
        rw [ho, hlev]
        exact lt_min (by linarith) (by linarith)
  · exact absurd hr hnr

end Geometry

section Main

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem headUnit_sum_cell {D : CellLayerData k C nE nM} {R : CellCalculusEntry D} (K : Fin D.mesh.count)
    (γ : ℤ × ℤ → ℂ) (d : CellVar D.mesh K (R.layouts K)) :
    ∑ ι ∈ D.mesh.resolved K, γ ι * headUnit D R K ι (Sum.inl (Sum.inl d))
      = γ d.1.1 * presUnitMoment ((R.layouts K).layout d.1.1) d.2 := by
  have h : ∀ ι, headUnit D R K ι (Sum.inl (Sum.inl d))
      = if d.1.1 = ι then presUnitMoment ((R.layouts K).layout d.1.1) d.2 else 0 := fun ι => rfl
  simp only [h, mul_ite, mul_zero, Finset.sum_ite_eq, d.1.2, if_true]

end Main

end TreeStateInternal

open TreeStateInternal CellCalculus CellCert.CellFormula CellCert.Finite in
theorem treeState_holds : TreeStateHolds := by
  intro k C nE nM D R e T W hC hG hT hM hFlip hPr hIB q hq front
  letI := T.slavedFintype
  letI := T.freeFintype
  classical
  obtain ⟨h0v, h0G, h0H, h0g, h0κ, h0F⟩ := hT.base_zero q hq
  refine ⟨BaseStateInternal.value_of_zero D (T.basePoint q) h0v h0G h0H h0κ h0F, ?_⟩
  unfold Certificate.IsState
  refine ⟨BaseStateInternal.trueData_of_zero T (T.basePoint q) h0v h0G h0H h0g h0κ h0F, fun x u => ?_⟩
  rw [hT.freeMap_zero, Matrix.zero_mulVec, add_zero]
  have hPg : IsPeriodicPressure (chosenPressure D x) := hPr q hq x
  have hκ : ∀ i, T.trueData x (W.kappa i) = x.κ i := by
    intro i
    simp only [TreeEntry.trueData, TreeEntry.fieldData, (hT.kappa_eval i).1, (hT.kappa_eval i).2]
  have hγex : ∀ (K : Fin D.mesh.count) (ι : ℤ × ℤ), ∃ γ : ℂ, ι ∈ D.mesh.resolved K → ∀ d,
      headHarmonic ((R.layouts K).layout ι) (labelTime ι) x.v x.G x.H (chosenPressure D x) d
        = harmonicData ((R.layouts K).layout ι) (labelTime ι) x.v x.G x.H (chosenPressure D x) d
          + γ * presUnitMoment ((R.layouts K).layout ι) d := by
    intro K ι
    by_cases hι : ι ∈ D.mesh.resolved K
    · obtain ⟨γ, hγ⟩ := HeadShiftInternal.headHarmonic_eq_shift _ (presSegments_off_axis hC K ι hι)
        (labelTime ι) x.v x.G x.H (chosenPressure D x) (hPg.harmonic_gradient _).1 (hPg.harmonic_gradient _).2
      exact ⟨γ, fun _ => hγ⟩
    · exact ⟨0, fun h => absurd h hι⟩
  choose γ hγ using hγex
  have hrow : ∀ (K : Fin D.mesh.count) (i : CellVars D R K), (∀ d, i = Sum.inl (Sum.inl d) → ¬ (W.reason K d).IsUnused) →
      (W.rowEmbed K *ᵥ fun a => ((Sum.elim (T.trueData x) u a : ℝ) : ℂ)) i
        = cellState D.mesh K (R.layouts K) x.v x.G x.H (chosenPressure D x) x.κ (fun i => u (W.zeta i))
            (fun j => ∑ b : T.Free, ((if b = W.portRe (R.portKey K j) then 1 else 0)
              + (if W.portIm (R.portKey K j) = some b then
                  (if W.portConj (R.portKey K j) then -Complex.I else Complex.I) else 0)) * ((u b : ℝ) : ℂ)) i
          + (∑ c, T.fieldGauge c x.v x.G x.H (chosenPressure D x) * T.gaugeDir K c i
            + ∑ ι ∈ D.mesh.resolved K, γ K ι * headUnit D R K ι i) := by
    intro K i hi
    rcases i with ((d | j) | (i | i))
    · rw [rowEmbed_apply_cell, hM q hq x K d (hi d rfl), headUnit_sum_cell]
      simp only [TreeEntry.shiftedState, TreeEntry.fieldShifted, TreeEntry.fieldHead, Sum.elim_inl, cellState,
        modeData]
      rw [hγ K d.1.1 d.1.2 d.2]
      ring
    · rw [rowEmbed_apply_port]
      simp [cellState, TreeEntry.gaugeDir, headUnit]
    · rw [rowEmbed_apply_kappa]
      simp [cellState, TreeEntry.gaugeDir, headUnit, hκ]
    · rw [rowEmbed_apply_zeta]
      simp [cellState, TreeEntry.gaugeDir, headUnit]
  have hkey : ∀ K : Fin D.mesh.count,
      quadFormValue (R.cellForm K) (T.embed K *ᵥ fun a => ((Sum.elim (T.trueData x) u a : ℝ) : ℂ))
        = quadFormValue (R.cellForm K)
            (cellState D.mesh K (R.layouts K) x.v x.G x.H (chosenPressure D x) x.κ (fun i => u (W.zeta i))
              (fun j => ∑ b : T.Free, ((if b = W.portRe (R.portKey K j) then 1 else 0)
                + (if W.portIm (R.portKey K j) = some b then
                    (if W.portConj (R.portKey K j) then -Complex.I else Complex.I) else 0)) * ((u b : ℝ) : ℂ))) := by
    intro K
    rw [hT.embed_eq K]
    rw [quadFormValue_eq_of_null_coords _ _
      (cellState D.mesh K (R.layouts K) x.v x.G x.H (chosenPressure D x) x.κ (fun i => u (W.zeta i))
        (fun j => ∑ b : T.Free, ((if b = W.portRe (R.portKey K j) then 1 else 0)
          + (if W.portIm (R.portKey K j) = some b then
              (if W.portConj (R.portKey K j) then -Complex.I else Complex.I) else 0)) * ((u b : ℝ) : ℂ))
        + (∑ c, T.fieldGauge c x.v x.G x.H (chosenPressure D x) • T.gaugeDir K c
          + ∑ ι ∈ D.mesh.resolved K, γ K ι • headUnit D R K ι))]
    · apply quadFormValue_add_null
      · rw [mulVec_add, mulVec_sum, mulVec_sum]
        rw [Finset.sum_eq_zero (fun c _ => by rw [mulVec_smul, (hG.kernel K c).1, smul_zero]), zero_add]
        refine Finset.sum_eq_zero fun ι hι => ?_
        have hk : R.cellForm K *ᵥ headUnit D R K ι = 0 := (hT.head_kernel K ⟨ι, hι⟩).1
        rw [mulVec_smul, hk, smul_zero]
      · rw [mulVec_add, mulVec_sum, mulVec_sum]
        rw [Finset.sum_eq_zero (fun c _ => by rw [mulVec_smul, (hG.kernel K c).2, smul_zero]), zero_add]
        refine Finset.sum_eq_zero fun ι hι => ?_
        have hk : (R.cellForm K)ᴴ *ᵥ headUnit D R K ι = 0 := (hT.head_kernel K ⟨ι, hι⟩).2
        rw [mulVec_smul, hk, smul_zero]
    · intro i
      by_cases hi : ∃ d, i = Sum.inl (Sum.inl d) ∧ (W.reason K d).IsUnused
      · right
        obtain ⟨d, rfl, hu⟩ := hi
        exact (unusedRow_of_unused W hT K d hu).2.1
      · left
        rw [hrow K i (fun d hd hu => hi ⟨d, hd, hu⟩)]
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hcred : ∀ j : Fin R.creditCount,
      quadFormValue (R.creditPatch j).credit (T.creditEmbed j *ᵥ fun a => ((Sum.elim (T.trueData x) u a : ℝ) : ℂ))
        = Coupling.quadForm (R.creditPatch j).credit
            (CreditEval.creditData D R j x.v x.G x.H (chosenPressure D x) x.κ (fun i => u (W.zeta i))
              (fun n => ∑ b : T.Free, ((if b = W.portRe n then 1 else 0)
                + (if W.portIm n = some b then (if W.portConj n then -Complex.I else Complex.I) else 0))
                  * ((u b : ℝ) : ℂ))) := by
    intro j
    show quadFormValue _ _ = quadFormValue _ _
    congr 1
    funext d
    have h1 : (T.creditEmbed j *ᵥ fun a => ((Sum.elim (T.trueData x) u a : ℝ) : ℂ)) d
        = (T.embed (R.creditOwner j d) *ᵥ fun a => ((Sum.elim (T.trueData x) u a : ℝ) : ℂ))
            (Sum.inl (Sum.inl (R.creditCoord j d))) := rfl
    rw [h1, hT.embed_eq]
    rw [hrow _ _ (fun d' hd' hu => by
      have hdd : R.creditCoord j d = d' := Sum.inl.inj (Sum.inl.inj hd')
      subst hdd
      exact (unusedRow_of_unused W hT _ _ hu).2.2 j d rfl)]
    rw [Finset.sum_eq_zero (fun c _ => by rw [hG.credit j d c, mul_zero]),
      Finset.sum_eq_zero (fun ι _ => by rw [hT.head_credit j d ι, mul_zero]), add_zero, add_zero]
    rfl
  have hglob : Sum.elim (T.trueData x) u ⬝ᵥ (T.globalLeaf *ᵥ Sum.elim (T.trueData x) u)
      ≤ globalForm D e x.κ (fun i => u (W.zeta i)) := by
    have h := hT.global_eq (Sum.elim (T.trueData x) u)
    have hk : (fun i => Sum.elim (T.trueData x) u (Sum.inl (W.kappa i))) = x.κ := funext hκ
    rw [hk] at h
    exact h
  have hstrong : IsStrongRightSide D.given D.cert.actuator x.κ x.v x.G x.H x.g (flipAverage x.F)
      (chosenPressure D x) := by
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [chosenPressure]
    abel
  have hbound := hIB q hq x (fun i => u (W.zeta i))
    (fun n => ∑ b : T.Free, ((if b = W.portRe n then 1 else 0)
      + (if W.portIm n = some b then (if W.portConj n then -Complex.I else Complex.I) else 0)) * ((u b : ℝ) : ℂ))
    (chosenPressure D x) hPg (hFlip q hq x) hstrong
  rw [quadValue_totalForm_eq T front (Sum.elim (T.trueData x) u)]
  rw [Finset.sum_congr rfl (fun K _ => hkey K), Finset.sum_congr rfl (fun j _ => hcred j)]
  unfold initialStateValue at hbound
  unfold quadValue
  linarith


end Assembly

end CertCell

end Breakdown
