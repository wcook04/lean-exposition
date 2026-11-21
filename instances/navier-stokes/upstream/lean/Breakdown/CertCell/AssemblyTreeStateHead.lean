import Breakdown.CertCell.AssemblyTreeStateZero

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace HeadShiftInternal

open CellCalculus CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellCoordinates

theorem test_continuous (S : FaceSegment) (d : ℕ) : Continuous (S.test d) := by
  unfold FaceSegment.test
  fun_prop

theorem presMode_one_const (m : ℕ) (n : ℤ) :
    (fun p : ℝ × ℝ => presMode m n (fun _ => (1 : ℝ)) p.1 p.2) = fun _ => presMode m n (fun _ => (1 : ℝ)) 0 0 :=
  rfl

theorem radial_add (c o lo hi : ℝ) (F G dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) (K : ℂ) (ht : Continuous t)
    (hG : Continuous G)
    (hint : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      * ((t p.2 : ℝ) : ℂ)) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi)) :
    radialStripMoment c o lo hi (fun p => F p + K * G p) dF t
      = radialStripMoment c o lo hi F dF t + K * radialStripMoment c o lo hi G (fun _ => 0) t := by
  have hB : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * G p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * 0)
      * ((t p.2 : ℝ) : ℂ)) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
    exact (by fun_prop : Continuous _).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  unfold radialStripMoment
  have h := integral_add hint (hB.const_mul K)
  rw [integral_const_mul] at h
  simp only [mul_zero, add_zero] at h ⊢
  calc _ = edgeSign c o * ((∫ p in Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi,
        ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((t p.2 : ℝ) : ℂ))
        + K * ∫ p in Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi,
          (((1 / (c - o) : ℝ)) : ℂ) * G p * ((t p.2 : ℝ) : ℂ)) := by
        congr 1
        rw [← h]
        congr 1
        funext p
        ring
    _ = _ := by ring

theorem height_add (c o lo hi : ℝ) (wt : ℝ → ℝ) (F G dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) (K : ℂ) (ht : Continuous t)
    (hwt : Continuous wt) (hG : Continuous G)
    (hint : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p)
      * ((wt p.1 * t p.1 : ℝ) : ℂ)) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o))) :
    heightStripMoment c o lo hi wt (fun p => F p + K * G p) dF t
      = heightStripMoment c o lo hi wt F dF t + K * heightStripMoment c o lo hi wt G (fun _ => 0) t := by
  have hB : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * G p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * 0)
      * ((wt p.1 * t p.1 : ℝ) : ℂ)) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) := by
    exact (by fun_prop : Continuous _).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  unfold heightStripMoment
  have h := integral_add hint (hB.const_mul K)
  rw [integral_const_mul] at h
  simp only [mul_zero, add_zero] at h ⊢
  calc _ = edgeSign c o * ((∫ p in Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o),
        ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((wt p.1 * t p.1 : ℝ) : ℂ))
        + K * ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o),
          (((1 / (c - o) : ℝ)) : ℂ) * G p * ((wt p.1 * t p.1 : ℝ) : ℂ)) := by
        congr 1
        rw [← h]
        congr 1
        funext p
        ring
    _ = _ := by ring


theorem presMode_shift (m : ℕ) (n : ℤ) (Q : Space → Space) (hQ : SteadyCert.IsGradientField Q) (e a : ℝ) :
    (fun p : ℝ × ℝ => presMode m n (fun y => potentialOf Q y - a) p.1 p.2) =ᵐ[volume]
      fun p => presMode m n (fun y => potentialOf Q y - e) p.1 p.2
        + (((e - a : ℝ)) : ℂ) * presMode m n (fun _ => (1 : ℝ)) p.1 p.2 := by
  have hQQ : (1 : ℝ) • Q + (0 : ℝ) • Q = Q := by simp
  have hC : potentialOf ((1 : ℝ) • Q + (0 : ℝ) • Q) =ᵐ[volume]
      fun y => 1 * potentialOf Q y + 0 * potentialOf Q y + 0 := by
    rw [hQQ]
    exact Filter.Eventually.of_forall fun y => by ring
  have hA := MeshDataAffineModes.gradient_modes_affine m Q Q hQ hQ 1 0 0 e e a hC n
  filter_upwards [hA] with p hp
  have h1 := hp.1
  rw [hQQ] at h1
  rw [h1]
  push_cast
  ring

theorem presMoment_shift (S : FaceSegment)
    (hS : S.radial = true → 0 < min S.level S.other ∨ S.other = 0) (m : ℕ) (n : ℤ) (Q : Space → Space)
    (hQ : SteadyCert.IsGradientField Q) (e a : ℝ) (d : ℕ) :
    S.moment true (fun p => presMode m n (fun y => potentialOf Q y - a) p.1 p.2)
        (fun p => modeVec m n Q p.1 p.2 0) (fun p => modeVec m n Q p.1 p.2 2) d
      = S.moment true (fun p => presMode m n (fun y => potentialOf Q y - e) p.1 p.2)
          (fun p => modeVec m n Q p.1 p.2 0) (fun p => modeVec m n Q p.1 p.2 2) d
        + (((e - a : ℝ)) : ℂ) * S.moment true (fun p => presMode m n (fun _ => (1 : ℝ)) p.1 p.2)
          (fun _ => 0) (fun _ => 0) d := by
  rw [BaseStateInternal.moment_congr_ae _ _ _ _ (presMode_shift m n Q hQ e a)]
  have hG : Continuous (fun p : ℝ × ℝ => presMode m n (fun _ => (1 : ℝ)) p.1 p.2) := by
    rw [presMode_one_const]
    exact continuous_const
  have hI := fun r₁ r₂ z₁ z₂ => MeshDataAffineModes.gradient_modes_integrable m Q hQ n e r₁ r₂ z₁ z₂
  have ht := test_continuous S d
  unfold FaceSegment.moment
  by_cases hr : S.radial = true
  · rw [if_pos hr, if_pos hr, if_pos hr]
    refine radial_add _ _ _ _ _ _ _ (S.test d) _ ht hG ?_
    have hF := (hI (min S.level S.other) (max S.level S.other) S.lo S.hi).1
    have hV := (hI (min S.level S.other) (max S.level S.other) S.lo S.hi).2 0
    have hK : IsCompact (Set.Icc (min S.level S.other) (max S.level S.other) ×ˢ Set.Icc S.lo S.hi) :=
      isCompact_Icc.prod isCompact_Icc
    have hM : MeasurableSet (Set.Icc (min S.level S.other) (max S.level S.other) ×ˢ Set.Icc S.lo S.hi) :=
      measurableSet_Icc.prod measurableSet_Icc
    simp only [add_mul]
    refine IntegrableOn.add ?_ ?_
    · refine (hF.mul_continuousOn (g' := fun p : ℝ × ℝ =>
        (((1 / (S.level - S.other) : ℝ)) : ℂ) * ((S.test d p.2 : ℝ) : ℂ)) (by fun_prop) hK).congr_fun
        (fun p _ => by ring) hM
    · rcases hS hr with hpos | h0
      · have hne : ∀ p ∈ Set.Icc (min S.level S.other) (max S.level S.other) ×ˢ Set.Icc S.lo S.hi, p.1 ≠ 0 :=
          fun p hp => (lt_of_lt_of_le hpos (Set.mem_Icc.mp (Set.mem_prod.mp hp).1).1).ne'
        refine (hV.mul_continuousOn (g' := fun p : ℝ × ℝ =>
          ((((p.1 - S.other) / (S.level - S.other) / p.1 : ℝ)) : ℂ) * ((S.test d p.2 : ℝ) : ℂ)) ?_ hK).congr_fun
          ?_ hM
        · refine ContinuousOn.mul ?_ (by fun_prop : Continuous fun p : ℝ × ℝ => ((S.test d p.2 : ℝ) : ℂ)).continuousOn
          refine Complex.continuous_ofReal.comp_continuousOn ?_
          exact ContinuousOn.div (by fun_prop) (by fun_prop) hne
        · intro p hp
          have hp1 : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hne p hp)
          push_cast
          field_simp
      · refine (hV.mul_continuousOn (g' := fun p : ℝ × ℝ =>
          (((1 / S.level : ℝ)) : ℂ) * ((S.test d p.2 : ℝ) : ℂ)) (by fun_prop) hK).congr_fun ?_ hM
        intro p _
        rw [h0]
        push_cast
        ring
  · rw [if_neg hr, if_neg hr, if_neg hr]
    have hw : (fun r : ℝ => if true = true then r else (1 : ℝ)) = fun r => r := funext fun r => if_pos rfl
    rw [hw]
    refine height_add _ _ _ _ (fun r => r) _ _ _ (S.test d) _ ht continuous_id hG ?_
    have hF := (hI S.lo S.hi (min S.level S.other) (max S.level S.other)).1
    have hV := (hI S.lo S.hi (min S.level S.other) (max S.level S.other)).2 2
    have hK : IsCompact (Set.Icc S.lo S.hi ×ˢ Set.Icc (min S.level S.other) (max S.level S.other)) :=
      isCompact_Icc.prod isCompact_Icc
    have hM : MeasurableSet (Set.Icc S.lo S.hi ×ˢ Set.Icc (min S.level S.other) (max S.level S.other)) :=
      measurableSet_Icc.prod measurableSet_Icc
    simp only [add_mul]
    refine IntegrableOn.add ?_ ?_
    · refine (hF.mul_continuousOn (g' := fun p : ℝ × ℝ =>
        (((1 / (S.level - S.other) : ℝ)) : ℂ) * ((p.1 * S.test d p.1 : ℝ) : ℂ)) (by fun_prop) hK).congr_fun
        (fun p _ => by ring) hM
    · refine (hV.mul_continuousOn (g' := fun p : ℝ × ℝ =>
        ((((p.2 - S.other) / (S.level - S.other) : ℝ)) : ℂ) * ((S.test d p.1 : ℝ) : ℂ)) (by fun_prop) hK).congr_fun
        ?_ hM
      intro p _
      push_cast
      ring


theorem headData_eq_shift (L : CellLayout)
    (hL : ∀ s, (L.presSegment s).radial = true →
      0 < min (L.presSegment s).level (L.presSegment s).other ∨ (L.presSegment s).other = 0)
    (x : Assembly.FieldTuple 0) (hx : SteadyCert.IsGradientField x.2.2.2.2) (d : L.Datum) :
    headData L x d = L.trueData x d
      + ((((L.gaugeValue x / L.gaugeUnit).re - ⨍ z in Metric.ball (0 : Space) 1, potentialOf x.2.2.2.2 z : ℝ)) : ℂ)
        * presUnitMoment L d := by
  rcases d with d | d | d | d | d | d | d | d
  · show L.trueData x _ = L.trueData x _ + _ * 0
    rw [mul_zero, add_zero]
  · show L.trueData x _ = L.trueData x _ + _ * 0
    rw [mul_zero, add_zero]
  · show L.trueData x _ = L.trueData x _ + _ * 0
    rw [mul_zero, add_zero]
  · show L.trueData x _ = L.trueData x _ + _ * 0
    rw [mul_zero, add_zero]
  · simp only [headData, presUnitMoment, CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    unfold headPressure headPotential CellLayout.pressMode CellLayout.pressureOf CellLayout.pressureGradMode
    exact presMoment_shift _ (hL _) _ _ _ hx _ _ _
  · show L.trueData x _ = L.trueData x _ + _ * 0
    rw [mul_zero, add_zero]
  · show L.trueData x _ = L.trueData x _ + _ * 0
    rw [mul_zero, add_zero]
  · show L.trueData x _ = L.trueData x _ + _ * 0
    rw [mul_zero, add_zero]

theorem headHarmonic_eq_shift (L : CellLayout)
    (hL : ∀ s, (L.presSegment s).radial = true →
      0 < min (L.presSegment s).level (L.presSegment s).other ∨ (L.presSegment s).other = 0)
    (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (hc : SteadyCert.IsGradientField (harmonicCos ν Pg)) (hs : SteadyCert.IsGradientField (harmonicSin ν Pg)) :
    ∃ γ : ℂ, ∀ d, headHarmonic L ν v G H Pg d = harmonicData L ν v G H Pg d + γ * presUnitMoment L d := by
  refine ⟨((((L.gaugeValue (cosTuple ν v G H Pg) / L.gaugeUnit).re
      - ⨍ z in Metric.ball (0 : Space) 1, potentialOf (cosTuple ν v G H Pg).2.2.2.2 z : ℝ)) : ℂ)
    + Complex.I * ((((L.gaugeValue (sinTuple ν v G H Pg) / L.gaugeUnit).re
      - ⨍ z in Metric.ball (0 : Space) 1, potentialOf (sinTuple ν v G H Pg).2.2.2.2 z : ℝ)) : ℂ), fun d => ?_⟩
  simp only [headHarmonic, harmonicData]
  rw [headData_eq_shift L hL (cosTuple ν v G H Pg) hc d, headData_eq_shift L hL (sinTuple ν v G H Pg) hs d]
  ring

end HeadShiftInternal

end Assembly

end CertCell

end Breakdown
