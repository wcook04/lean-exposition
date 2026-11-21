import Breakdown.CertCell.RowsMatchDerived

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}
  {T : TreeEntry D R}

def velVal (L : CellLayout) (h : L.Datum → ℂ) (n : L.modes) (s : Fin L.segCount) (a : Fin 3) (i : ℕ) : ℂ :=
  if hi : i < L.degSide + 2 then h (CellDatum.sideVelocity n s a ⟨i, hi⟩) else 0

def cornerVal (L : CellLayout) (h : L.Datum → ℂ) (n : L.modes) (c : Option (Fin L.cornerCount)) (a : Fin 3) : ℂ :=
  match c with
  | none => 0
  | some c => h (CellDatum.cornerVelocity n c a)

def EndOK (L : CellLayout) (s : Fin L.segCount) (c₀ : Option (Fin L.cornerCount)) : Prop :=
  match c₀ with
  | some c => L.segEnd s 0 = some c ∧ L.corner c = streamEnds (L.segment s) 0
  | none => (L.segment s).radial = false ∧ (L.segment s).lo = 0

def NormalSegmentIdentity (L : CellLayout) (h : L.Datum → ℂ) : Prop :=
  ∀ (n : L.modes) (s : Fin L.segCount) (deg : Fin (L.degSide + 1)) (c₀ : Option (Fin L.cornerCount))
    (c₁ : Fin L.cornerCount) (pcoef : ℕ → ℝ) (pdeg : ℕ),
    L.segEnd s 1 = some c₁ → L.corner c₁ = streamEnds (L.segment s) 1 →
    EndOK L s c₀ →
    ((L.segment s).radial = true → (L.segment s).level ≠ 0 →
      (∀ u : ℝ, ∑ j ∈ Finset.range ((deg : ℕ) + 1), ((j : ℝ) * (L.segment s).testCoef deg j) * u ^ (j - 1)
        = ∑ i ∈ Finset.range (pdeg + 1), pcoef i * (L.segment s).test i u) →
      h (CellDatum.sideGradient n s 0 deg)
        = -((1 / (L.segment s).level : ℝ) : ℂ) *
            (velVal L h n s 0 deg + ((azimuth L.order n : ℂ) * Complex.I) * velVal L h n s 1 deg)
          - (((L.segment s).test deg (L.segment s).hi : ℝ) : ℂ) * cornerVal L h n (some c₁) 2
          + (((L.segment s).test deg (L.segment s).lo : ℝ) : ℂ) * cornerVal L h n c₀ 2
          + ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) * velVal L h n s 2 i) ∧
    ((L.segment s).radial = false →
      (∀ u : ℝ, u * ∑ j ∈ Finset.range ((deg : ℕ) + 1), ((j : ℝ) * (L.segment s).testCoef deg j) * u ^ (j - 1)
        = ∑ i ∈ Finset.range (pdeg + 1), pcoef i * (L.segment s).test i u) →
      h (CellDatum.sideGradient n s 2 deg)
        = -((((L.segment s).hi * (L.segment s).test deg (L.segment s).hi : ℝ) : ℂ) * cornerVal L h n (some c₁) 0)
          + (((L.segment s).lo * (L.segment s).test deg (L.segment s).lo : ℝ) : ℂ) * cornerVal L h n c₀ 0
          + ∑ i ∈ Finset.range (pdeg + 1), ((pcoef i : ℝ) : ℂ) * velVal L h n s 0 i
          - ((azimuth L.order n : ℂ) * Complex.I) * velVal L h n s 1 deg)

def NormalSegmentHolds : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (modes : Finset ℤ) (L : CellLayout), IsHarmonicLayout m K B modes L →
    ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (Pg : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → IsPeriodicPressure Pg → ∀ ν : ℤ,
        NormalSegmentIdentity L (harmonicData L ν v G H Pg)

namespace RowEntry

variable (W : RowEntry D R T)

def valOf (f : T.Slaved → ℝ) : (T.Slaved → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ a, v a * (f a : ℂ)
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_assoc]

theorem rowValue_eq_valOf (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (f : T.Slaved → ℝ) :
    W.rowValue K d f = valOf f (W.rowVec K d) := W.rowValue_eq_sum K d f

theorem valOf_velRow (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (n : ((R.layouts K).layout ι.1).modes)
    (s : Fin ((R.layouts K).layout ι.1).segCount) (a : Fin 3) (i : ℕ) (f : T.Slaved → ℝ) :
    valOf f (W.velRow K ι n s a i) = velVal ((R.layouts K).layout ι.1) (fun e => W.rowValue K ⟨ι, e⟩ f) n s a i := by
  unfold velRow velVal
  split_ifs with hi
  · exact (W.rowValue_eq_valOf K _ f).symm
  · exact map_zero _

theorem valOf_cornerRow (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (n : ((R.layouts K).layout ι.1).modes)
    (c : Option (Fin ((R.layouts K).layout ι.1).cornerCount)) (a : Fin 3) (f : T.Slaved → ℝ) :
    valOf f (W.cornerRow K ι n c a) = cornerVal ((R.layouts K).layout ι.1) (fun e => W.rowValue K ⟨ι, e⟩ f) n c a := by
  cases c with
  | none => exact map_zero _
  | some c => exact (W.rowValue_eq_valOf K _ f).symm

theorem velVal_congr (L : CellLayout) (h₁ h₂ : L.Datum → ℂ) (n : L.modes) (s : Fin L.segCount) (a : Fin 3) (i : ℕ)
    (hh : ∀ hi : i < L.degSide + 2, h₁ (CellDatum.sideVelocity n s a ⟨i, hi⟩) = h₂ (CellDatum.sideVelocity n s a ⟨i, hi⟩)) :
    velVal L h₁ n s a i = velVal L h₂ n s a i := by
  unfold velVal
  split_ifs with hi
  · exact hh hi
  · rfl

theorem fieldShifted_of_not_pres (K : Fin D.mesh.count) (ι : D.mesh.resolved K)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    (e : ((R.layouts K).layout ι.1).Datum) (hp : isPressureDatum ((R.layouts K).layout ι.1) e = false) :
    T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl ⟨ι, e⟩))
      = harmonicData ((R.layouts K).layout ι.1) (labelTime ι.1) v G H Pg e := by
  have hg : ∀ c, T.gaugeDir K c (Sum.inl (Sum.inl ⟨ι, e⟩)) = 0 := fun c => gaugeDir_of_not_pres T K c ⟨ι, e⟩ hp
  simp only [TreeEntry.fieldShifted, TreeEntry.fieldHead, Sum.elim_inl, hg, mul_zero,
    Finset.sum_const_zero, add_zero]
  exact headHarmonic_of_not_pres _ _ _ _ _ _ e hp

theorem normal_end_ok (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (n : ((R.layouts K).layout d.1.1).modes) (s : Fin ((R.layouts K).layout d.1.1).segCount)
    (c₀ : Option (Fin ((R.layouts K).layout d.1.1).cornerCount))
    (h : match c₀ with
      | some c => ((R.layouts K).layout d.1.1).segEnd s 0 = some c ∧
          ((R.layouts K).layout d.1.1).corner c = streamEnds (((R.layouts K).layout d.1.1).segment s) 0 ∧
          W.cornerReady K d n c
      | none => (((R.layouts K).layout d.1.1).segment s).radial = false ∧
          (((R.layouts K).layout d.1.1).segment s).lo = 0) :
    EndOK ((R.layouts K).layout d.1.1) s c₀ := by
  cases c₀ with
  | none => exact h
  | some c => exact ⟨h.1, h.2.1⟩

theorem normal_corner_val (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K))
    (n : ((R.layouts K).layout d.1.1).modes) (s : Fin ((R.layouts K).layout d.1.1).segCount)
    (c₀ : Option (Fin ((R.layouts K).layout d.1.1).cornerCount)) (g h' : ((R.layouts K).layout d.1.1).Datum → ℂ)
    (h : match c₀ with
      | some c => ((R.layouts K).layout d.1.1).segEnd s 0 = some c ∧
          ((R.layouts K).layout d.1.1).corner c = streamEnds (((R.layouts K).layout d.1.1).segment s) 0 ∧
          W.cornerReady K d n c
      | none => (((R.layouts K).layout d.1.1).segment s).radial = false ∧
          (((R.layouts K).layout d.1.1).segment s).lo = 0)
    (HC : ∀ c a, W.cornerReady K d n c → g (CellDatum.cornerVelocity n c a) = h' (CellDatum.cornerVelocity n c a))
    (a : Fin 3) : cornerVal ((R.layouts K).layout d.1.1) g n c₀ a = cornerVal ((R.layouts K).layout d.1.1) h' n c₀ a := by
  cases c₀ with
  | none => rfl
  | some c => exact HC c a h.2.2

theorem normal_row_fields (K : Fin D.mesh.count) (d : CellVar D.mesh K (R.layouts K)) (pcoef : ℕ → ℝ) (pdeg : ℕ)
    (hw : W.NormalRow K d pcoef pdeg) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ : Fin k → ℝ)
    (hseg : NormalSegmentIdentity ((R.layouts K).layout d.1.1)
      (harmonicData ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg))
    (hlow : ∀ e : ((R.layouts K).layout d.1.1).Datum, W.rank K ⟨d.1, e⟩ < W.rank K d →
      ¬ (W.reason K ⟨d.1, e⟩).IsUnused →
      W.rowValue K ⟨d.1, e⟩ (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl ⟨d.1, e⟩))) :
    W.rowValue K d (T.fieldData v G H Pg κ) = T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) := by
  obtain ⟨n, s, deg, c₀, c₁, hend1, hc1, hready1, hc0, hvel, hcase⟩ := hw
  have HV : ∀ (a : Fin 3) (i : ℕ), W.velReady K d n s a i →
      velVal ((R.layouts K).layout d.1.1) (fun e => W.rowValue K ⟨d.1, e⟩ (T.fieldData v G H Pg κ)) n s a i = velVal ((R.layouts K).layout d.1.1) (harmonicData ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg) n s a i := by
    intro a i hr
    obtain ⟨h', hrank, hun⟩ := hr
    apply velVal_congr
    intro hi
    rw [hlow _ hrank hun]
    exact fieldShifted_of_not_pres K d.1 v G H Pg κ _ rfl
  have HC : ∀ (c : Fin ((R.layouts K).layout d.1.1).cornerCount) (a : Fin 3), W.cornerReady K d n c →
      W.rowValue K ⟨d.1, CellDatum.cornerVelocity n c a⟩ (T.fieldData v G H Pg κ) = (harmonicData ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg) (CellDatum.cornerVelocity n c a) := by
    intro c a hr
    obtain ⟨hrank, hun⟩ := hr a
    rw [hlow _ hrank hun]
    exact fieldShifted_of_not_pres K d.1 v G H Pg κ _ rfl
  have hc0' := W.normal_end_ok K d n s c₀ hc0
  have HC0 := W.normal_corner_val K d n s c₀ (fun e => W.rowValue K ⟨d.1, e⟩ (T.fieldData v G H Pg κ))
    (harmonicData ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg) hc0 HC
  have hdpres : ∀ e : ((R.layouts K).layout d.1.1).Datum, (e = CellDatum.sideGradient n s 0 deg ∨ e = CellDatum.sideGradient n s 2 deg) →
      isPressureDatum ((R.layouts K).layout d.1.1) e = false := by
    rintro e (rfl | rfl) <;> rfl
  rcases hcase with ⟨hrad, hd, hlev, hpoly, hvec⟩ | ⟨hrad, hd, hpoly, hvec⟩
  · have hid := (hseg n s deg c₀ c₁ pcoef pdeg hend1 hc1 hc0').1 hrad hlev hpoly
    rw [W.rowValue_eq_valOf, hvec]
    simp only [map_add, map_sub, map_neg, map_smul, map_sum, smul_eq_mul, W.valOf_velRow, W.valOf_cornerRow,
      ← W.rowValue_eq_valOf]
    rw [HV 0 deg (hvel 0).1, HV 1 deg (hvel 1).1, HC c₁ 2 hready1, HC0 2]
    rw [Finset.sum_congr rfl (fun i hi => by rw [HV 2 i ((hvel 2).2 i hi)])]
    rw [show T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) = (harmonicData ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg) d.2 from
      fieldShifted_of_not_pres K d.1 v G H Pg κ d.2 (hdpres d.2 (Or.inl hd))]
    rw [hd, hid]
    simp only [cornerVal]
    ring
  · have hid := (hseg n s deg c₀ c₁ pcoef pdeg hend1 hc1 hc0').2 hrad hpoly
    rw [W.rowValue_eq_valOf, hvec]
    simp only [map_add, map_sub, map_neg, map_smul, map_sum, smul_eq_mul, W.valOf_velRow, W.valOf_cornerRow,
      ← W.rowValue_eq_valOf]
    rw [HV 1 deg (hvel 1).1, HC c₁ 0 hready1, HC0 0]
    rw [Finset.sum_congr rfl (fun i hi => by rw [HV 0 i ((hvel 0).2 i hi)])]
    rw [show T.fieldShifted K v G H Pg κ (Sum.inl (Sum.inl d)) = (harmonicData ((R.layouts K).layout d.1.1) (labelTime d.1.1) v G H Pg) d.2 from
      fieldShifted_of_not_pres K d.1 v G H Pg κ d.2 (hdpres d.2 (Or.inr hd))]
    rw [hd, hid]
    simp only [cornerVal]

end RowEntry

end Assembly

end CertCell

end Breakdown
