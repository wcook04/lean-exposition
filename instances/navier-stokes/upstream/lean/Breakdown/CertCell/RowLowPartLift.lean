import Breakdown.CertCell.RowLowPartStrip
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.CellCalculus.RowLow.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

theorem datum_sum (L : CellLayout) (f : L.Datum → ℂ) :
    ∑ d, f d = (∑ i, f (Sum.inl i)) + (∑ i, f (Sum.inr (Sum.inl i))) + (∑ i, f (Sum.inr (Sum.inr (Sum.inl i))))
      + (∑ i, f (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
      + (∑ i, f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
      + (∑ i, f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))))
      + (∑ i, f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))))
      + (∑ i, f (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))))))) := by
  simp only [CellLayout.Datum, CellDatum, Fintype.sum_sum_type]
  ring

theorem own_sum (L : CellLayout) (k freq : ℝ) (φ : Fin 3 → CellPoly) (u : L.Datum → ℂ) :
    ∑ d, ownRowVector L k freq φ d * u d =
      (∑ i : L.modes × Fin 3 × Fin 3 × Fin (L.degCoef + 1) × Fin (L.degCoef + 1),
          ownStrainRow L k φ i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 * u (Sum.inl i))
      + (∑ i : L.modes × Fin 3 × Fin L.degCoef × Fin L.degCoef,
          ownVelocityRow L freq φ i.2.1 i.2.2.1 i.2.2.2 * u (Sum.inr (Sum.inl i)))
      + (∑ i : L.modes × Fin L.segCount × Fin 3 × Fin (L.degSide + 1),
          sideGradRow L φ i.2.1 i.2.2.1 i.2.2.2 * u (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
      + (∑ i : L.modes × Fin L.presCount × Fin L.degSide,
          sidePresRow L φ i.2.1 i.2.2 * u (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))) := by
  rw [datum_sum]
  simp only [ownRowVector, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]

theorem rect_sub_strip {K : CellBox} (hK : IsCellBox K) : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc K.z₁ K.z₂ := by
  rintro p ⟨⟨h1, h2⟩, h3⟩
  exact ⟨⟨hK.r_order.1.trans h1, h2⟩, h3⟩

theorem rect_sub_square {K : CellBox} (hK : IsCellBox K) : K.rect ⊆ Icc 0 (max K.r₂ K.z₂) ×ˢ Icc (-(max K.r₂ K.z₂)) (max K.r₂ K.z₂) := by
  rintro p ⟨⟨h1, h2⟩, h3, h4⟩
  refine ⟨⟨hK.r_order.1.trans h1, h2.trans (le_max_left _ _)⟩, ?_, h4.trans (le_max_right _ _)⟩
  have := hK.z_order.1
  have : 0 ≤ max K.r₂ K.z₂ := (hK.z_order.1.trans hK.z_order.2.le).trans (le_max_right _ _)
  linarith

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem third_weighted_int {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hL : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ)
    (a b c : Fin 3) {K : CellBox} (hK : IsCellBox K) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b c p) K.rect := by
  have h := Breakdown.FracInternal.MeshDataAffineModes.weighted_strip
    (Breakdown.FracInternal.MeshDataAffineModes.second_locInt hL.measurable_second hL.second_two)
    (Breakdown.FracInternal.MeshDataAffineModes.thirdKernel m n a b c)
    (Breakdown.FracInternal.MeshDataAffineModes.thirdKernel_cont m n a b c)
    (Breakdown.FracInternal.MeshDataAffineModes.thirdKernel_bound m n a b c)
    (Breakdown.FracInternal.MeshDataAffineModes.thirdKernel_per m n a b c) (max K.r₂ K.z₂)
  exact (h.mono_set (rect_sub_square hK)).congr_fun
    (fun p _ => by rw [Breakdown.FracInternal.MeshDataAffineModes.modeThird_k]) (rect_meas K)

theorem grad_int {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hL : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ)
    (a b : Fin 3) {K : CellBox} (hK : IsCellBox K) : IntegrableOn (gradMode m n G a b) K.rect :=
  ((localModeStripIntegrable m v G H hL n K.r₂ K.z₁ K.z₂).2 a b).mono_set (rect_sub_strip hK)

theorem vel_int {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hL : IsLocalSecondOrderField v G H) (m : ℕ) (n : ℤ)
    (a : Fin 3) {K : CellBox} (hK : IsCellBox K) :
    IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect :=
  ((localModeStripIntegrable m v G H hL n K.r₂ K.z₁ K.z₂).1 a).mono_set (rect_sub_strip hK)

theorem harmonicMode_label (ι : ℤ × ℤ) : harmonicMode (labelTime ι) ι.1 = ι := by
  unfold harmonicMode labelTime
  ext
  · rfl
  · simp only
    have : ι.1 + (2 * ι.2 - ι.1) = 2 * ι.2 := by ring
    rw [this]
    omega

theorem even_label (ι : ℤ × ℤ) : Even (ι.1 + labelTime ι) := by
  unfold labelTime
  exact ⟨ι.2, by ring⟩

theorem ae_rect_pos {K : CellBox} (hK : IsCellBox K) : ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 := by
  filter_upwards [ae_restrict_of_ae Breakdown.FracInternal.MeshDataAffineModes.ae_off_axis,
    ae_restrict_mem (rect_meas K)] with p h0 hp
  exact lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm h0)

theorem lift_rect (h1 : HarmonicLiftStatement) {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsPeriodicSecondOrder v G H) (m : ℕ) (ι : ℤ × ℤ)
    {K : CellBox} (hK : IsCellBox K) :
    ∀ᵐ p ∂(volume.restrict K.rect),
      (∀ a, velAt m ι v a p = modeVec m ι.1 (harmonicCos (labelTime ι) v) p.1 p.2 a
          + Complex.I * modeVec m ι.1 (harmonicSin (labelTime ι) v) p.1 p.2 a) ∧
      (∀ a b, gradAt m ι G a b p = gradMode m ι.1 (harmonicCos (labelTime ι) G) a b p
          + Complex.I * gradMode m ι.1 (harmonicSin (labelTime ι) G) a b p) ∧
      (∀ a b c, slopeAt m ι H a b c p = modeThird m ι.1 (harmonicCos (labelTime ι) H) a b c p
          + Complex.I * modeThird m ι.1 (harmonicSin (labelTime ι) H) a b c p) := by
  have h := (h1 m v G H hv (labelTime ι)).2.2 ι.1 (even_label ι)
  rw [harmonicMode_label] at h
  filter_upwards [ae_restrict_of_ae h, ae_rect_pos hK] with p hp h0
  exact hp h0

theorem pres_lift_rect (h2 : HarmonicPressureLiftStatement) {Pg : ℝ → Space → Space} (hp : IsPeriodicPressure Pg)
    (m : ℕ) (ι : ℤ × ℤ) {K : CellBox} (hK : IsCellBox K) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ a, velAt m ι Pg a p
      = modeVec m ι.1 (harmonicCos (labelTime ι) Pg) p.1 p.2 a
          + Complex.I * modeVec m ι.1 (harmonicSin (labelTime ι) Pg) p.1 p.2 a := by
  have h := h2 m Pg hp (labelTime ι) ι.1 (even_label ι)
  rw [harmonicMode_label] at h
  filter_upwards [ae_restrict_of_ae h, ae_rect_pos hK] with p hp h0
  exact hp h0

section Lift

variable (h1 : HarmonicLiftStatement) {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsPeriodicSecondOrder v G H) (m : ℕ) (ι : ℤ × ℤ)
    {K : CellBox} (hK : IsCellBox K)

include h1 hv hK

theorem gradAt_int (a b : Fin 3) : IntegrableOn (gradAt m ι G a b) K.rect := by
  obtain ⟨hc, hs, -⟩ := h1 m v G H hv (labelTime ι)
  refine ((grad_int hc m ι.1 a b hK).add ((grad_int hs m ι.1 a b hK).const_mul Complex.I)).congr ?_
  filter_upwards [lift_rect h1 hv m ι hK] with p hp
  exact (hp.2.1 a b).symm

theorem velAt_int (a : Fin 3) : IntegrableOn (fun p => velAt m ι v a p) K.rect := by
  obtain ⟨hc, hs, -⟩ := h1 m v G H hv (labelTime ι)
  refine ((vel_int hc m ι.1 a hK).add ((vel_int hs m ι.1 a hK).const_mul Complex.I)).congr ?_
  filter_upwards [lift_rect h1 hv m ι hK] with p hp
  exact (hp.1 a).symm

theorem slopeAt_w_int (a b c : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * slopeAt m ι H a b c p) K.rect := by
  obtain ⟨hc, hs, -⟩ := h1 m v G H hv (labelTime ι)
  refine ((third_weighted_int hc m ι.1 a b c hK).add
    ((third_weighted_int hs m ι.1 a b c hK).const_mul Complex.I)).congr ?_
  filter_upwards [lift_rect h1 hv m ι hK] with p hp
  rw [hp.2.2 a b c, Pi.add_apply]
  ring

theorem lw_gradAt_int (a b : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradAt m ι G a b p) K.rect := by
  obtain ⟨hc, hs, -⟩ := h1 m v G H hv (labelTime ι)
  refine (((localModeIntegrable m _ _ _ hc K hK ι.1 a).2 b).add
    (((localModeIntegrable m _ _ _ hs K hK ι.1 a).2 b).const_mul Complex.I)).congr ?_
  filter_upwards [lift_rect h1 hv m ι hK] with p hp
  rw [hp.2.1 a b, Pi.add_apply]
  ring

theorem lw_velAt_int (a : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * velAt m ι v a p) K.rect := by
  obtain ⟨hc, hs, -⟩ := h1 m v G H hv (labelTime ι)
  refine (((localModeIntegrable m _ _ _ hc K hK ι.1 a).1).add
    (((localModeIntegrable m _ _ _ hs K hK ι.1 a).1).const_mul Complex.I)).congr ?_
  filter_upwards [lift_rect h1 hv m ι hK] with p hp
  rw [hp.1 a, Pi.add_apply]
  ring

end Lift

section Pressure

variable (h2 : HarmonicPressureLiftStatement) {Pg : ℝ → Space → Space} (hp : IsPeriodicPressure Pg) (m : ℕ)
    (ι : ℤ × ℤ) {K : CellBox} (hK : IsCellBox K)

theorem pres_int_of (Q : Space → Space) (hQ : IsGradientField Q) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => presMode m n (potentialOf Q) p.1 p.2) K.rect := by
  have h := (MeshDataAffineModes.gradient_modes_integrable m Q hQ n 0 K.r₁ K.r₂ K.z₁ K.z₂).1
  simp only [sub_zero] at h
  exact h

include hp in
theorem labelPressure_int : IntegrableOn (labelPressure m ι Pg) K.rect :=
  (pres_int_of m (harmonicCos (labelTime ι) Pg) (hp.harmonic_gradient _).1 ι.1).add
    ((pres_int_of m (harmonicSin (labelTime ι) Pg) (hp.harmonic_gradient _).2 ι.1).const_mul Complex.I)

include h2 hp hK in
theorem presVel_w_int (a : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * velAt m ι Pg a p) K.rect := by
  have hc := (MeshDataAffineModes.gradient_modes_integrable m _ (hp.harmonic_gradient (labelTime ι)).1 ι.1 0
    K.r₁ K.r₂ K.z₁ K.z₂).2 a
  have hs := (MeshDataAffineModes.gradient_modes_integrable m _ (hp.harmonic_gradient (labelTime ι)).2 ι.1 0
    K.r₁ K.r₂ K.z₁ K.z₂).2 a
  refine (hc.add (hs.const_mul Complex.I)).congr ?_
  filter_upwards [pres_lift_rect h2 hp m ι hK] with p hq
  rw [hq a, Pi.add_apply]
  ring

theorem presMode_shift (Q : Space → Space) (hQ : IsGradientField Q) (n : ℤ) (e : ℝ) :
    ∀ᵐ p : ℝ × ℝ, presMode m n (fun y => potentialOf Q y - e) p.1 p.2
      = presMode m n (potentialOf Q) p.1 p.2 - (e : ℂ) * presMode m n (fun _ => 1) 0 0 := by
  have hQQ : (1 : ℝ) • Q + (0 : ℝ) • Q = Q := by simp
  have hC : potentialOf ((1 : ℝ) • Q + (0 : ℝ) • Q) =ᵐ[volume]
      fun y => (1 : ℝ) * potentialOf Q y + (0 : ℝ) * potentialOf Q y + 0 := by
    rw [hQQ]
    exact Filter.Eventually.of_forall (fun y => by simp)
  have h := MeshDataAffineModes.gradient_modes_affine m Q Q hQ hQ 1 0 0 0 0 e hC n
  rw [hQQ] at h
  filter_upwards [h] with p hp
  rw [hp.1]
  simp only [sub_zero]
  have : presMode m n (fun _ => (1 : ℝ)) p.1 p.2 = presMode m n (fun _ => 1) 0 0 := rfl
  rw [this]
  push_cast
  ring

end Pressure

theorem presMode_one (m : ℕ) (n : ℤ) (h : (n : ℝ) * m ≠ 0) : presMode m n (fun _ => 1) 0 0 = 0 := by
  unfold presMode azimuth
  have hw : ((n : ℂ) * (m : ℂ)) ≠ 0 := by exact_mod_cast h
  have hc : (-((n : ℂ) * (m : ℂ)) * Complex.I) ≠ 0 := mul_ne_zero (neg_ne_zero.2 hw) Complex.I_ne_zero
  have e1 : (fun θ : ℝ => Complex.exp (-(((n : ℝ) * m * θ : ℝ) : ℂ) * Complex.I) * (((1 : ℝ)) : ℂ)) =
      fun θ : ℝ => Complex.exp ((-((n : ℂ) * (m : ℂ)) * Complex.I) * (θ : ℂ)) := by
    funext θ
    push_cast
    ring_nf
  rw [e1, integral_exp_mul_complex hc]
  have e2 : (-((n : ℂ) * (m : ℂ)) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) =
      ((-(n * (m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e2, Complex.exp_int_mul_two_pi_mul_I]
  simp

end Breakdown.CertCell.CellCalculus.RowLow.Internal
