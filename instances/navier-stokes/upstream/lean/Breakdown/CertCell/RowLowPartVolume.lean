import Breakdown.CertCell.RowLowPartBoundary

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.CellCalculus.RowLow.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

theorem conj_frameWeight (p : ℝ × ℝ) (b : Fin 3) : (starRingEnd ℂ) (frameWeight p b) = frameWeight p b := by
  unfold frameWeight
  split_ifs <;> simp

theorem strain_row_eq (K : CellBox) (B : CellBases) (k : ℝ) (φ : Fin 3 → CellPoly) (a b : Fin 3) (j l : ℕ)
    (p : ℝ × ℝ) :
    (p.1 : ℂ) * basisValue B j l p * ((starRingEnd ℂ) (testGrad K k φ p a b)
      + (1 / 2 : ℂ) * frameWeight p b * (starRingEnd ℂ) ((φ a).eval K p))
      = (starRingEnd ℂ) ((p.1 : ℂ) * gTot K k φ p a b * basisValue B j l p) := by
  unfold gTot
  simp only [map_mul, map_add, conj_basisValue, Complex.conj_ofReal, conj_frameWeight, map_div₀, map_one,
    map_ofNat]
  ring

theorem sum_fin_range2 {N : ℕ} (f : ℕ → ℕ → ℂ) :
    ∑ j : Fin N, ∑ l : Fin N, f j l = ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, f j l := by
  rw [Fin.sum_univ_eq_sum_range (fun j => ∑ l : Fin N, f j l)]
  exact Finset.sum_congr rfl (fun j _ => Fin.sum_univ_eq_sum_range (f j) N)

theorem cell_block (hexp : CellBasisExpansionStatement) {K : CellBox} {B : CellBases} (hK : IsCellBox K)
    (hB : IsCellBases K B) {N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly N N h) {Gc Gs : ℝ × ℝ → ℂ}
    (ic : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Gc p) K.rect)
    (is : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Gs p) K.rect) (row : ℕ → ℕ → ℂ)
    (hrow : ∀ j l, row j l = (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * h x * basisValue B j l x)) :
    ∑ j : Fin N, ∑ l : Fin N, row j l * (B.coef K Gc j l + Complex.I * B.coef K Gs j l)
      = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (Gc p + Complex.I * Gs p) * (starRingEnd ℂ) (h p) := by
  rw [sum_fin_range2 (fun j l => row j l * (B.coef K Gc j l + Complex.I * B.coef K Gs j l))]
  have e : ∀ j ∈ Finset.range N, ∑ l ∈ Finset.range N, row j l * (B.coef K Gc j l + Complex.I * B.coef K Gs j l)
      = (∑ l ∈ Finset.range N, B.coef K Gc j l *
          (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * h x * basisValue B j l x))
        + Complex.I * ∑ l ∈ Finset.range N, B.coef K Gs j l *
          (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * h x * basisValue B j l x) := by
    intro j _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hrow]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, cell_expand_pairing hexp hK hB hh ic,
    cell_expand_pairing hexp hK hB hh is]
  have hc : ContinuousOn (fun p => (starRingEnd ℂ) (h p)) K.rect :=
    (Complex.continuous_conj.comp (bi_contDiff hh).continuous).continuousOn
  rw [← integral_const_mul, ← integral_add (ic.mul_continuousOn hc (rect_compact K))
    ((is.mul_continuousOn hc (rect_compact K)).const_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only
  ring

theorem volume_point (K : CellBox) (k freq : ℝ) (φ : Fin 3 → CellPoly) (grad : Fin 3 → Fin 3 → ℂ) (vel : Fin 3 → ℂ)
    (p : ℝ × ℝ) :
    (p.1 : ℂ) * ((∑ a : Fin 3, ∑ b : Fin 3, grad a b * (starRingEnd ℂ) (testGrad K k φ p a b))
      + cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * vel a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * grad a 0 + (p.2 : ℂ) * grad a 2)) (testValue K φ p))
      = (∑ a : Fin 3, ∑ b : Fin 3, grad a b * (starRingEnd ℂ) ((p.1 : ℂ) * gTot K k φ p a b))
        + ((freq : ℂ) * Complex.I + 1 / 2) * ∑ a : Fin 3, vel a * (starRingEnd ℂ) ((p.1 : ℂ) * (φ a).eval K p) := by
  unfold gTot cdot3 testValue
  simp only [Fin.sum_univ_three, frameWeight, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [map_mul, map_add, Complex.conj_ofReal, map_div₀, map_one, map_ofNat, map_zero]
  ring

theorem sum_modes (L : CellLayout) {n0 : ℤ} (hmodes : L.modes = {n0}) {β : Type*} [Fintype β]
    (f : L.modes × β → ℂ) :
    ∑ i, f i = ∑ x : β, f (⟨n0, by rw [hmodes]; exact Finset.mem_singleton_self n0⟩, x) := by
  rw [Fintype.sum_prod_type]
  refine Fintype.sum_eq_single _ (fun n hn => ?_)
  exfalso
  apply hn
  have h2 : (n : ℤ) ∈ ({n0} : Finset ℤ) := hmodes ▸ n.2
  exact Subtype.ext (Finset.mem_singleton.1 h2)

section Data

variable (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)

theorem data_lowStrain (i : L.modes × Fin 3 × Fin 3 × Fin (L.degCoef + 1) × Fin (L.degCoef + 1)) :
    harmonicData L ν v G H Pg (Sum.inl i) =
      L.bases.coef L.box (gradMode L.order i.1 (harmonicCos ν G) i.2.1 i.2.2.1) i.2.2.2.1 i.2.2.2.2
        + Complex.I * L.bases.coef L.box (gradMode L.order i.1 (harmonicSin ν G) i.2.1 i.2.2.1) i.2.2.2.1 i.2.2.2.2 :=
  rfl

theorem data_lowVelocity (i : L.modes × Fin 3 × Fin L.degCoef × Fin L.degCoef) :
    harmonicData L ν v G H Pg (Sum.inr (Sum.inl i)) =
      L.bases.coef L.box (fun p => modeVec L.order i.1 (harmonicCos ν v) p.1 p.2 i.2.1) i.2.2.1 i.2.2.2
        + Complex.I * L.bases.coef L.box (fun p => modeVec L.order i.1 (harmonicSin ν v) p.1 p.2 i.2.1) i.2.2.1 i.2.2.2 :=
  rfl

theorem data_sidePressure (i : L.modes × Fin L.presCount × Fin L.degSide) :
    harmonicData L ν v G H Pg (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) =
      (L.presSegment i.2.1).moment true (L.pressMode i.1 (cosTuple ν v G H Pg))
          (L.pressureGradMode i.1 (cosTuple ν v G H Pg) 0) (L.pressureGradMode i.1 (cosTuple ν v G H Pg) 2) i.2.2
        + Complex.I * (L.presSegment i.2.1).moment true (L.pressMode i.1 (sinTuple ν v G H Pg))
          (L.pressureGradMode i.1 (sinTuple ν v G H Pg) 0) (L.pressureGradMode i.1 (sinTuple ν v G H Pg) 2) i.2.2 :=
  rfl

theorem pressMode_cos (n : ℤ) : L.pressMode n (cosTuple ν v G H Pg) = fun p => presMode L.order n
    (fun y => potentialOf (harmonicCos ν Pg) y - (L.gaugeValue (cosTuple ν v G H Pg) / L.gaugeUnit).re) p.1 p.2 :=
  rfl

theorem pressMode_sin (n : ℤ) : L.pressMode n (sinTuple ν v G H Pg) = fun p => presMode L.order n
    (fun y => potentialOf (harmonicSin ν Pg) y - (L.gaugeValue (sinTuple ν v G H Pg) / L.gaugeUnit).re) p.1 p.2 :=
  rfl

theorem pgm_cos (n : ℤ) (a : Fin 3) : L.pressureGradMode n (cosTuple ν v G H Pg) a =
    fun p => modeVec L.order n (harmonicCos ν Pg) p.1 p.2 a := rfl

theorem pgm_sin (n : ℤ) (a : Fin 3) : L.pressureGradMode n (sinTuple ν v G H Pg) a =
    fun p => modeVec L.order n (harmonicSin ν Pg) p.1 p.2 a := rfl

end Data

section Blocks

variable {k' N' : ℕ} {c0 : FracCellData k' N'} {K : CellBox} {S0 : CellScalars} {B : CellBases} {L : CellLayout}

theorem strain_block_data (hexpC : CellBasisExpansionStatement) (h1 : HarmonicLiftStatement)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (Pg : ℝ → Space → Space) (hv : IsPeriodicSecondOrder v G H)
    {m : ℕ} (hLc : IsCellLayout c0 K S0 B L) (hord : L.order = m) (ι : ℤ × ℤ) (hmodes : L.modes = {ι.1})
    (k : ℝ) (φ : Fin 3 → CellPoly) (hs : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (hsP : ∀ a b, IsBivariatePoly (L.degCoef + 1) (L.degCoef + 1) (hs a b))
    (hsE : ∀ a b, ∀ p ∈ K.rect, (p.1 : ℂ) * gTot K k φ p a b = (K.lineWeight p.1 : ℂ) * hs a b p) :
    ∑ i : L.modes × Fin 3 × Fin 3 × Fin (L.degCoef + 1) × Fin (L.degCoef + 1),
        ownStrainRow L k φ i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 * harmonicData L (labelTime ι) v G H Pg (Sum.inl i)
      = ∑ a : Fin 3, ∑ b : Fin 3, ∫ p in K.rect,
          (K.lineWeight p.1 : ℂ) * gradAt m ι G a b p * (starRingEnd ℂ) (hs a b p) := by
  have hK := hLc.box_valid
  have hB := hLc.bases_valid
  refine (sum_modes L hmodes _).trans ?_
  simp only [Fintype.sum_prod_type, data_lowStrain, hLc.box_eq, hLc.bases_eq, hord]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  obtain ⟨hc, hsn, -⟩ := h1 m v G H hv (labelTime ι)
  have hrow : ∀ j l : ℕ, ownStrainRow L k φ a b j l =
      (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * hs a b x * basisValue B j l x) := by
    intro j l
    unfold ownStrainRow
    rw [hLc.box_eq, hLc.bases_eq, ← integral_conj]
    refine setIntegral_congr_fun (rect_meas K) (fun p hp => ?_)
    rw [strain_row_eq, hsE a b p hp]
  rw [cell_block hexpC hK hB (hsP a b) ((localModeIntegrable m _ _ _ hc K hK ι.1 a).2 b)
    ((localModeIntegrable m _ _ _ hsn K hK ι.1 a).2 b) (fun j l => ownStrainRow L k φ a b j l) hrow]
  refine integral_congr_ae ?_
  filter_upwards [lift_rect h1 hv m ι hK] with p hp
  rw [hp.2.1 a b]

theorem vel_block_data (hexpC : CellBasisExpansionStatement) (h1 : HarmonicLiftStatement)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (Pg : ℝ → Space → Space) (hv : IsPeriodicSecondOrder v G H)
    {m : ℕ} (hLc : IsCellLayout c0 K S0 B L) (hord : L.order = m) (ι : ℤ × ℤ) (hmodes : L.modes = {ι.1})
    (freq : ℝ) (φ : Fin 3 → CellPoly) (hw : Fin 3 → ℝ × ℝ → ℂ)
    (hwP : ∀ a, IsBivariatePoly L.degCoef L.degCoef (hw a))
    (hwE : ∀ a, ∀ p : ℝ × ℝ, (p.1 : ℂ) * (φ a).eval K p = (K.lineWeight p.1 : ℂ) * hw a p) :
    ∑ i : L.modes × Fin 3 × Fin L.degCoef × Fin L.degCoef,
        ownVelocityRow L freq φ i.2.1 i.2.2.1 i.2.2.2 * harmonicData L (labelTime ι) v G H Pg (Sum.inr (Sum.inl i))
      = ((freq : ℂ) * Complex.I + 1 / 2) * ∑ a : Fin 3, ∫ p in K.rect,
          (K.lineWeight p.1 : ℂ) * velAt m ι v a p * (starRingEnd ℂ) (hw a p) := by
  have hK := hLc.box_valid
  have hB := hLc.bases_valid
  refine (sum_modes L hmodes _).trans ?_
  simp only [Fintype.sum_prod_type, data_lowVelocity, hLc.box_eq, hLc.bases_eq, hord]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  obtain ⟨hc, hsn, -⟩ := h1 m v G H hv (labelTime ι)
  have hrow : ∀ j l : ℕ, (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * hw a x * basisValue B j l x) =
      (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * hw a x * basisValue B j l x) := fun _ _ => rfl
  have hcb := cell_block hexpC hK hB (hwP a) ((localModeIntegrable m _ _ _ hc K hK ι.1 a).1)
    ((localModeIntegrable m _ _ _ hsn K hK ι.1 a).1) _ hrow
  have hvr : ∀ j l : ℕ, ownVelocityRow L freq φ a j l = ((freq : ℂ) * Complex.I + 1 / 2) *
      (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * hw a x * basisValue B j l x) := by
    intro j l
    unfold ownVelocityRow
    rw [hLc.box_eq, hLc.bases_eq, ← integral_conj]
    congr 1
    refine setIntegral_congr_fun (rect_meas K) (fun p _ => ?_)
    have := hwE a p
    have hc2 := congrArg (starRingEnd ℂ) this
    simp only [map_mul, Complex.conj_ofReal] at hc2
    simp only [map_mul, conj_basisValue, Complex.conj_ofReal]
    linear_combination basisValue B j l p * hc2
  simp only [hvr]
  have e : ∀ j : Fin L.degCoef, ∀ l : Fin L.degCoef, ((freq : ℂ) * Complex.I + 1 / 2) *
      (starRingEnd ℂ) (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * hw a x * basisValue B j l x) *
        (B.coef K (fun p => modeVec m ι.1 (harmonicCos (labelTime ι) v) p.1 p.2 a) j l
          + Complex.I * B.coef K (fun p => modeVec m ι.1 (harmonicSin (labelTime ι) v) p.1 p.2 a) j l)
      = ((freq : ℂ) * Complex.I + 1 / 2) * ((starRingEnd ℂ)
          (∫ x in K.rect, (K.lineWeight x.1 : ℂ) * hw a x * basisValue B j l x) *
        (B.coef K (fun p => modeVec m ι.1 (harmonicCos (labelTime ι) v) p.1 p.2 a) j l
          + Complex.I * B.coef K (fun p => modeVec m ι.1 (harmonicSin (labelTime ι) v) p.1 p.2 a) j l)) :=
    fun j l => by ring
  simp only [e, ← Finset.mul_sum]
  rw [hcb]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [lift_rect h1 hv m ι hK] with p hp
  rw [hp.1 a]

theorem volume_data (h1 : HarmonicLiftStatement) {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (Pg : ℝ → Space → Space) (hv : IsPeriodicSecondOrder v G H)
    (m : ℕ) (ι : ℤ × ℤ) (hK : IsCellBox K) (k freq : ℝ) (φ : Fin 3 → CellPoly) {M M' : ℕ}
    (hs : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (hsP : ∀ a b, IsBivariatePoly M M (hs a b))
    (hsE : ∀ a b, ∀ p ∈ K.rect, (p.1 : ℂ) * gTot K k φ p a b = (K.lineWeight p.1 : ℂ) * hs a b p)
    (hw : Fin 3 → ℝ × ℝ → ℂ) (hwP : ∀ a, IsBivariatePoly M' M' (hw a))
    (hwE : ∀ a, ∀ p : ℝ × ℝ, (p.1 : ℂ) * (φ a).eval K p = (K.lineWeight p.1 : ℂ) * hw a p) :
    rowVolume K k freq (labelRowProfile K m ι v G H Pg) φ
      = (∑ a : Fin 3, ∑ b : Fin 3, ∫ p in K.rect,
          (K.lineWeight p.1 : ℂ) * gradAt m ι G a b p * (starRingEnd ℂ) (hs a b p))
        + ((freq : ℂ) * Complex.I + 1 / 2) * ∑ a : Fin 3, ∫ p in K.rect,
          (K.lineWeight p.1 : ℂ) * velAt m ι v a p * (starRingEnd ℂ) (hw a p) := by
  unfold rowVolume
  have hpt : ∀ p ∈ K.rect, (p.1 : ℂ) *
      ((∑ a : Fin 3, ∑ b : Fin 3, (labelRowProfile K m ι v G H Pg).grad p a b *
          (starRingEnd ℂ) (testGrad K k φ p a b))
        + cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * (labelRowProfile K m ι v G H Pg).vel p a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * (labelRowProfile K m ι v G H Pg).grad p a 0
            + (p.2 : ℂ) * (labelRowProfile K m ι v G H Pg).grad p a 2)) (testValue K φ p))
      = (∑ a : Fin 3, ∑ b : Fin 3, (K.lineWeight p.1 : ℂ) * gradAt m ι G a b p * (starRingEnd ℂ) (hs a b p))
        + ((freq : ℂ) * Complex.I + 1 / 2) * ∑ a : Fin 3,
          (K.lineWeight p.1 : ℂ) * velAt m ι v a p * (starRingEnd ℂ) (hw a p) := by
    intro p hp
    rw [volume_point]
    congr 1
    · refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [hsE a b p hp]
      simp only [map_mul, Complex.conj_ofReal, labelRowProfile, gradArray]
      ring
    · congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hwE a p]
      simp only [map_mul, Complex.conj_ofReal, labelRowProfile, velArray]
      ring
  rw [setIntegral_congr_fun (rect_meas K) hpt]
  have ig : ∀ a b, IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradAt m ι G a b p *
      (starRingEnd ℂ) (hs a b p)) K.rect := fun a b =>
    (lw_gradAt_int h1 hv m ι hK a b).mul_continuousOn
      (Complex.continuous_conj.comp (bi_contDiff (hsP a b)).continuous).continuousOn (rect_compact K)
  have iv : ∀ a, IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * velAt m ι v a p *
      (starRingEnd ℂ) (hw a p)) K.rect := fun a =>
    (lw_velAt_int h1 hv m ι hK a).mul_continuousOn
      (Complex.continuous_conj.comp (bi_contDiff (hwP a)).continuous).continuousOn (rect_compact K)
  rw [integral_add (integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => ig a b)))
      ((integrable_finsetSum _ (fun a _ => iv a)).const_mul _),
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => ig a b)), integral_const_mul,
    integral_finsetSum _ (fun a _ => iv a)]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => integral_finsetSum _ (fun b _ => ig a b))

end Blocks

end Breakdown.CertCell.CellCalculus.RowLow.Internal
