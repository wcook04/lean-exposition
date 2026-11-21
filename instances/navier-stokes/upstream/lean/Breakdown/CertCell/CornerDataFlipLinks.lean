import Breakdown.CertCell.PlaneDataFlipLinks
import Breakdown.CertCell.ModeHeightDerivative

open scoped ContDiff
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.CertCell.Bridge

namespace Internal.CornerDataFlip

open CellCert.CellAnalysis.LowEntry.Internal (cylArg)
open TailBand.Internal.FlipDecay (ae_orbit_of_ae cylArg_eq)
open Internal.ModeFlip (modeVel_flip_of modeGrad_flip_of modeSecondDeriv_flip_of)
open Internal.PlaneDataFlip (ae_field_flip flipPoint_planePoint)
open Internal.HeightOrbit (waveAvg_integrableOn plane_weak radialL_cont axialL_cont axialL)
open Internal.HeightModes (frameCoord frameCoord_smooth vel_rep gradz_rep gradr_rep secondDerivrz_rep col_loc
  flip_loc grad_weak_op mixed_partial deriv_test scale_id)

theorem ae_plane_flip {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g)
    (hflip : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (ξ : ℤ × ℤ) :
    ∀ᵐ p : ℝ × ℝ,
      modeVel (flipLabel ξ) v 0 (planePoint p)
          = (fun a => (frameSign a : ℂ) * modeVel ξ v 0 (planePoint (p.1, -p.2)) a) ∧
      modeGrad (flipLabel ξ) G 0 (planePoint p)
          = (fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint (p.1, -p.2)) ab) ∧
      modeSecondDeriv (flipLabel ξ) H 0 (planePoint p)
          = (fun abc => ((frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2 : ℝ) : ℂ)
            * modeSecondDeriv ξ H 0 (planePoint (p.1, -p.2)) abc) := by
  have horb := ae_orbit_of_ae (ae_field_flip hp hflip)
  have hpt : ∀ᵐ p : ℝ × ℝ,
      modeVel (flipLabel ξ) v 0 (flipPoint (planePoint p))
          = (fun a => (frameSign a : ℂ) * modeVel ξ v 0 (planePoint p) a) ∧
      modeGrad (flipLabel ξ) G 0 (flipPoint (planePoint p))
          = (fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) ab) ∧
      modeSecondDeriv (flipLabel ξ) H 0 (flipPoint (planePoint p))
          = (fun abc => ((frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2 : ℝ) : ℂ)
            * modeSecondDeriv ξ H 0 (planePoint p) abc) := by
    filter_upwards [horb] with p hq
    have hq2 : ∀ᵐ q ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
        v q.1 (flipPoint (cylArg (p, q.2))) = flipPoint (v q.1 (cylArg (p, q.2)))
        ∧ (∀ u, G q.1 (flipPoint (cylArg (p, q.2))) u = flipPoint (G q.1 (cylArg (p, q.2)) (flipPoint u)))
        ∧ ∀ u u', H q.1 (flipPoint (cylArg (p, q.2))) u u'
          = flipPoint (H q.1 (cylArg (p, q.2)) (flipPoint u) (flipPoint u')) := by
      rw [← Measure.volume_eq_prod]
      exact hq
    have ho : ∀ᵐ τ : ℝ, ∀ᵐ φ : ℝ, v (0 + τ) (flipPoint (axialRot φ (planePoint p)))
          = flipPoint (v (0 + τ) (axialRot φ (planePoint p)))
        ∧ (∀ u, G (0 + τ) (flipPoint (axialRot φ (planePoint p))) u
          = flipPoint (G (0 + τ) (axialRot φ (planePoint p)) (flipPoint u)))
        ∧ ∀ u u', H (0 + τ) (flipPoint (axialRot φ (planePoint p))) u u'
          = flipPoint (H (0 + τ) (axialRot φ (planePoint p)) (flipPoint u) (flipPoint u')) := by
      filter_upwards [Measure.ae_ae_of_ae_prod hq2] with τ hτ
      filter_upwards [hτ] with φ hφ
      simpa only [zero_add, cylArg_eq] using hφ
    exact ⟨modeVel_flip_of ξ (ho.mono fun _ h => h.mono fun _ h => h.1),
      modeGrad_flip_of ξ (ho.mono fun _ h => h.mono fun _ h => h.2.1),
      modeSecondDeriv_flip_of ξ (ho.mono fun _ h => h.mono fun _ h => h.2.2)⟩
  have hneg : MeasurePreserving (fun p : ℝ × ℝ => (p.1, -p.2)) volume volume := by
    have e : (fun p : ℝ × ℝ => (p.1, -p.2)) = Prod.map (id : ℝ → ℝ) (fun z : ℝ => -z) := rfl
    rw [e, Measure.volume_eq_prod]
    exact (MeasurePreserving.id _).prod (Measure.measurePreserving_neg _)
  filter_upwards [hneg.quasiMeasurePreserving.ae hpt] with p hp'
  simp only [flipPoint_planePoint, neg_neg, Prod.mk.eta] at hp'
  exact hp'

theorem cornerMoment_congr {cr orr cz oz : ℝ} {F Fr Fz Frz F' Fr' Fz' Frz' : ℝ × ℝ → ℂ}
    (h : ∀ᵐ p : ℝ × ℝ, F p = F' p ∧ Fr p = Fr' p ∧ Fz p = Fz' p ∧ Frz p = Frz' p) :
    CellCert.CellFormula.cornerMoment cr orr cz oz F Fr Fz Frz
      = CellCert.CellFormula.cornerMoment cr orr cz oz F' Fr' Fz' Frz' := by
  unfold CellCert.CellFormula.cornerMoment
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae h] with p hp
  rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

theorem plane_weak_data {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g) (ξ : ℤ × ℤ) (a : Fin 3) :
    (∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeVel ξ v 0 (planePoint p) a) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) ∧
      IntegrableOn (fun p => modeGrad ξ G 0 (planePoint p) (a, 0)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) ∧
      IntegrableOn (fun p => modeGrad ξ G 0 (planePoint p) (a, 2)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) ∧
      IntegrableOn (fun p => modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁)) ∧
    ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVel ξ v 0 (planePoint p) a =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 0)) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVel ξ v 0 (planePoint p) a =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 2)) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 0) =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2)) := by
  obtain ⟨lv, lG, lH⟩ := Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hp
  have hslice : ∀ᵐ τ, AEStronglyMeasurable (H τ) volume := hp.measurable_secondDeriv.prodMk_left
  have w1 : ∀ᵐ τ, LocallyIntegrable (v τ) volume ∧
      (∀ j : Fin 3, LocallyIntegrable (fun y => G τ y (unitVector j)) volume) ∧
      ∀ φ : Space → ℝ, SteadyCert.IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) • v τ y = -∫ y, φ y • G τ y (unitVector j) := by
    filter_upwards [hp.weak_gradient] with τ hτ
    refine ⟨hτ.1, fun j => col_loc hτ.2.1 j, fun φ hφ j => ?_⟩
    rw [hτ.2.2 φ hφ j, neg_neg]
  have w2 : ∀ᵐ τ, LocallyIntegrable (G τ) volume ∧
      (∀ j : Fin 3, LocallyIntegrable (fun y => H τ y (unitVector j)) volume) ∧
      ∀ φ : Space → ℝ, SteadyCert.IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) • G τ y = -∫ y, φ y • H τ y (unitVector j) := by
    filter_upwards [hp.weak_gradient, hp.weak_secondDeriv, hslice] with τ h1 h2 h3
    have hHl : LocallyIntegrable (H τ) volume := flip_loc h3 fun i => (h2 i).2.1
    exact ⟨h1.2.1, fun j => col_loc hHl j, fun φ hφ j => grad_weak_op h1.2.1 hHl h2 φ hφ j⟩
  have L1 := frameCoord_smooth a
  have L2 : ContDiff ℝ ∞ (axialL (frameCoord a)) := L1.clm_comp contDiff_const
  have Q1 : ∀ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ p ∈ tsupport χ, 0 < p.1) →
      (∫ p, ((fderiv ℝ χ p (1, 0) : ℝ) : ℂ) * modeVel ξ v 0 (planePoint p) a =
        -∫ p, ((χ p : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 0)) ∧
      (∫ p, ((fderiv ℝ χ p (0, 1) : ℝ) : ℂ) * modeVel ξ v 0 (planePoint p) a =
        -∫ p, ((χ p : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 2)) := by
    intro χ hχ hc hpos
    have h := plane_weak v G lv lG w1 (frameCoord a) L1 ξ.1 ξ.2 χ hχ hc hpos
    simp only [vel_rep, gradr_rep, gradz_rep]
    exact ⟨scale_id _ h.1, scale_id _ h.2⟩
  refine ⟨fun a₁ b₁ c₁ d₁ h0 => ⟨?_, ?_, ?_, ?_⟩, fun ψ hψ hc hpos => ⟨(Q1 ψ hψ hc hpos).1,
    (Q1 ψ hψ hc hpos).2, ?_⟩⟩
  · simp only [vel_rep]
    exact (waveAvg_integrableOn v lv _ L1.continuous _ _ h0).const_mul _
  · simp only [gradr_rep]
    exact (waveAvg_integrableOn G lG _ (radialL_cont L1.continuous) _ _ h0).const_mul _
  · simp only [gradz_rep]
    exact (waveAvg_integrableOn G lG _ (axialL_cont L1.continuous) _ _ h0).const_mul _
  · simp only [secondDerivrz_rep]
    exact (waveAvg_integrableOn H lH _ (radialL_cont L2.continuous) _ _ h0).const_mul _
  · have C : ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 2) =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2) := by
      have h := plane_weak G H lG lH w2 (axialL (frameCoord a)) L2 ξ.1 ξ.2 ψ hψ hc hpos
      simp only [gradz_rep, secondDerivrz_rep]
      exact scale_id _ h.1
    obtain ⟨z1, z2, z3⟩ := deriv_test hψ hc hpos (0, 1)
    obtain ⟨r1, r2, r3⟩ := deriv_test hψ hc hpos (1, 0)
    have A := (Q1 _ z1 z2 z3).1
    have B := (Q1 _ r1 r2 r3).2
    have e : (fun p => ((fderiv ℝ (fun q => fderiv ℝ ψ q (0, 1)) p (1, 0) : ℝ) : ℂ)
          * modeVel ξ v 0 (planePoint p) a) =
        fun p => ((fderiv ℝ (fun q => fderiv ℝ ψ q (1, 0)) p (0, 1) : ℝ) : ℂ)
          * modeVel ξ v 0 (planePoint p) a :=
      funext fun p => by rw [mixed_partial hψ]
    calc ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 0)
        = -∫ p, ((fderiv ℝ (fun q => fderiv ℝ ψ q (0, 1)) p (1, 0) : ℝ) : ℂ)
            * modeVel ξ v 0 (planePoint p) a := by rw [A, neg_neg]
      _ = -∫ p, ((fderiv ℝ (fun q => fderiv ℝ ψ q (1, 0)) p (0, 1) : ℝ) : ℂ)
            * modeVel ξ v 0 (planePoint p) a := by rw [e]
      _ = ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 2) := by
          rw [B, neg_neg]
      _ = _ := C

theorem integral_mul_comm_real (A : ℝ × ℝ → ℂ) (χ : ℝ × ℝ → ℝ) (R : Set (ℝ × ℝ)) :
    ∫ p in R, A p * ((χ p : ℝ) : ℂ) = ∫ p in R, ((χ p : ℝ) : ℂ) * A p :=
  integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)

theorem weak_on_rectangle {A B : ℝ × ℝ → ℂ} {ψ χ : ℝ × ℝ → ℝ} {R : Set (ℝ × ℝ)}
    (hψ : ∀ p, p ∉ R → ψ p = 0) (hχ : ∀ p, p ∉ R → χ p = 0)
    (h : ∫ p, ((χ p : ℝ) : ℂ) * A p = -∫ p, ((ψ p : ℝ) : ℂ) * B p) :
    ∫ p in R, A p * ((χ p : ℝ) : ℂ) = -∫ p in R, B p * ((ψ p : ℝ) : ℂ) := by
  rw [integral_mul_comm_real, integral_mul_comm_real,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by rw [hχ p hp]; simp,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by rw [hψ p hp]; simp]
  exact h

theorem plane_derivs_on {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g) (ξ : ℤ × ℤ) (a : Fin 3)
    {lo hi c d : ℝ} (hlo : 0 < lo) :
    HasWeakPlaneDerivsOn (fun p => planeVel ξ v a p.1 p.2) (planeVelRadial ξ G a)
      (fun p => planeVelHeight ξ G a p.1 p.2) (planeVelMixed ξ H a) (Icc lo hi ×ˢ Icc c d) := by
  obtain ⟨hI, hW⟩ := plane_weak_data hp ξ a
  obtain ⟨i1, i2, i3, i4⟩ := hI lo hi c d hlo
  refine ⟨i1, i2, i3, i4, fun ψ hψ hc hsub => ?_⟩
  have hout : ∀ p, p ∉ Icc lo hi ×ˢ Icc c d → p ∉ tsupport ψ := fun p hp ht =>
    hp (interior_subset (hsub ht))
  have hpos : ∀ p ∈ tsupport ψ, 0 < p.1 := fun p ht =>
    lt_of_lt_of_le hlo (interior_subset (hsub ht)).1.1
  have z0 : ∀ p, p ∉ Icc lo hi ×ˢ Icc c d → ψ p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (hout p hp)
  have zd : ∀ u : ℝ × ℝ, ∀ p, p ∉ Icc lo hi ×ˢ Icc c d → fderiv ℝ ψ p u = 0 := fun u p hp => by
    rw [fderiv_of_notMem_tsupport ℝ (hout p hp)]
    rfl
  obtain ⟨e1, e2, e3⟩ := hW ψ hψ hc hpos
  exact ⟨weak_on_rectangle z0 (zd (1, 0)) e1, weak_on_rectangle z0 (zd (0, 1)) e2,
    weak_on_rectangle z0 (zd (0, 1)) e3⟩

theorem trace_heights (hT : TraceHeightHolds) {f fz : ℝ → ℂ} {h h' : ℝ} (hh : 0 < h) (hh' : 0 < h')
    (hw : ∀ k : ℝ, 0 < k → HasWeakDerivOn f fz (-k) k) :
    upperTrace f fz h = upperTrace f fz h' := by
  have hk : 0 < max h h' := lt_max_of_lt_left hh
  have w := hw (2 * max h h') (by positivity)
  rw [hT f fz h (max h h') hh (le_max_left _ _) w, hT f fz h' (max h h') hh' (le_max_right _ _) w]

end Internal.CornerDataFlip

open Internal.CornerDataFlip in
theorem cornerDataFlip (hX : ModeFlipHolds) (hR : ModeShiftRotateHolds) (hR' : ModeShiftRotateTensorHolds)
    (hF : CornerFlipHolds) (hM : CornerMatchHolds) (hC : CornerTraceHolds) (hT : TraceHeightHolds)
    (hD : ModeHeightDerivHolds) (hE : HessianEnergyIdentityHolds) (hF' : TraceFlipHolds) (hM' : TraceMatchHolds) :
    CornerDataFlipHolds := by
  intro Γ P v G H g hp hflip ξ a cr orr h h' hcr hor hne hh hh'
  have hmin : 0 < min cr orr := lt_min hcr hor
  have hmax : 0 < max cr orr := lt_max_of_lt_left hcr
  have hs0 : frameSign (0 : Fin 3) = 1 := by simp [frameSign]
  have hs2 : frameSign (2 : Fin 3) = -1 := by simp [frameSign]
  have step1 : CellCert.CellFormula.cornerMoment cr orr 0 h (fun p => planeVel (flipLabel ξ) v a p.1 p.2)
        (planeVelRadial (flipLabel ξ) G a) (fun p => planeVelHeight (flipLabel ξ) G a p.1 p.2)
        (planeVelMixed (flipLabel ξ) H a)
      = CellCert.CellFormula.cornerMoment cr orr 0 h
        (fun p => (frameSign a : ℂ) * planeVel ξ v a p.1 (-p.2))
        (fun p => (frameSign a : ℂ) * planeVelRadial ξ G a (p.1, -p.2))
        (fun p => -((frameSign a : ℂ) * planeVelHeight ξ G a p.1 (-p.2)))
        (fun p => -((frameSign a : ℂ) * planeVelMixed ξ H a (p.1, -p.2))) := by
    refine cornerMoment_congr ?_
    filter_upwards [ae_plane_flip hp hflip ξ] with p hq
    obtain ⟨q1, q2, q3⟩ := hq
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [planeVel, Prod.mk.eta]
      rw [q1]
    · simp only [planeVelRadial]
      rw [q2]
      simp only [hs0]
      push_cast
      ring
    · simp only [planeVelHeight, Prod.mk.eta]
      rw [q2]
      simp only [hs2]
      push_cast
      ring
    · simp only [planeVelMixed]
      rw [q3]
      simp only [hs0, hs2]
      push_cast
      ring
  have step2 := hF (fun p => planeVel ξ v a p.1 p.2) (planeVelRadial ξ G a)
    (fun p => planeVelHeight ξ G a p.1 p.2) (planeVelMixed ξ H a) cr orr h (frameSign a : ℂ)
  have step3 := hM (fun p => planeVel ξ v a p.1 p.2) (planeVelRadial ξ G a)
    (fun p => planeVelHeight ξ G a p.1 p.2) (planeVelMixed ξ H a) cr orr h (min cr orr / 2) (2 * max cr orr)
    hne hh (half_lt_self hmin) (by linarith) (plane_derivs_on hp ξ a (half_pos hmin))
  obtain ⟨hI, -⟩ := plane_weak_data hp ξ a
  have hIc : ∀ k : ℝ, IntegrableOn (fun p => planeVel ξ v a p.1 p.2) (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k) ∧
      IntegrableOn (planeVelRadial ξ G a) (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k) ∧
      IntegrableOn (fun p => planeVelHeight ξ G a p.1 p.2) (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k) ∧
      IntegrableOn (planeVelMixed ξ H a) (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k) := fun k =>
    hI (min cr orr) (max cr orr) 0 k hmin
  have t1 := hC (fun p => planeVel ξ v a p.1 p.2) (planeVelRadial ξ G a)
    (fun p => planeVelHeight ξ G a p.1 p.2) (planeVelMixed ξ H a) cr orr h hne hh
    (hIc h).1 (hIc h).2.1 (hIc h).2.2.1 (hIc h).2.2.2
  have t2 := hC (fun p => planeVel ξ v a p.1 p.2) (planeVelRadial ξ G a)
    (fun p => planeVelHeight ξ G a p.1 p.2) (planeVelMixed ξ H a) cr orr h' hne hh'
    (hIc h').1 (hIc h').2.1 (hIc h').2.2.1 (hIc h').2.2.2
  have hlines : ∀ᵐ r ∂(volume.restrict (Icc (min cr orr) (max cr orr))),
      upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h
          = upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h' ∧
      upperTrace (fun z => modeGrad ξ G 0 (planePoint (r, z)) (a, 0))
          (fun z => modeSecondDeriv ξ H 0 (planePoint (r, z)) (a, 0, 2)) h
        = upperTrace (fun z => modeGrad ξ G 0 (planePoint (r, z)) (a, 0))
          (fun z => modeSecondDeriv ξ H 0 (planePoint (r, z)) (a, 0, 2)) h' := by
    have hsub : Icc (min cr orr) (max cr orr) ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le hmin hr.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hD Γ P v G H g hp ξ a)] with r hr
    exact ⟨trace_heights hT hh hh' fun k hk => (hr k hk).1,
      trace_heights hT hh hh' fun k hk => (hr k hk).2.2⟩
  have step4 : CellCert.CellFormula.cornerMoment cr orr 0 h (fun p => planeVel ξ v a p.1 p.2)
        (planeVelRadial ξ G a) (fun p => planeVelHeight ξ G a p.1 p.2) (planeVelMixed ξ H a)
      = CellCert.CellFormula.cornerMoment cr orr 0 h' (fun p => planeVel ξ v a p.1 p.2)
        (planeVelRadial ξ G a) (fun p => planeVelHeight ξ G a p.1 p.2) (planeVelMixed ξ H a) := by
    rw [t1, t2]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hlines] with r hr
    show (((1 / (cr - orr) : ℝ)) : ℂ) * upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h
        + (((r - orr) / (cr - orr) : ℝ) : ℂ) * upperTrace (fun z => modeGrad ξ G 0 (planePoint (r, z)) (a, 0))
          (fun z => modeSecondDeriv ξ H 0 (planePoint (r, z)) (a, 0, 2)) h
      = (((1 / (cr - orr) : ℝ)) : ℂ) * upperTrace (planeVel ξ v a r) (planeVelHeight ξ G a r) h'
        + (((r - orr) / (cr - orr) : ℝ) : ℂ) * upperTrace (fun z => modeGrad ξ G 0 (planePoint (r, z)) (a, 0))
          (fun z => modeSecondDeriv ξ H 0 (planePoint (r, z)) (a, 0, 2)) h'
    rw [hr.1, hr.2]
  rw [step1]
  refine step2.trans ?_
  rw [← step3, step4]

end Breakdown.CertCell.Bridge
