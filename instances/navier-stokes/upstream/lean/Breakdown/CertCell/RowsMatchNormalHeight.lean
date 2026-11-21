import Breakdown.CertCell.RowsMatchNormalTurn

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.SegmentNormal

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula LocalField
  LocalField.Internal.FaceTraceFree SegmentLine

namespace Internal

theorem height_trace_split (K : CellBox) {c o lo hi : ℝ} (hR : Icc lo hi ×ˢ Icc (min c o) (max c o) = K.rect)
    {F₀ F₁ F₂ D₀ D₁ D₂ : ℝ × ℝ → ℂ} (wt t : ℝ → ℝ)
    (hF : ∀ᵐ p ∂(volume.restrict K.rect), F₀ p + F₁ p + F₂ p = 0)
    (hD : ∀ᵐ p ∂(volume.restrict K.rect), D₀ p + D₁ p + D₂ p = 0)
    (i₁ : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F₁ p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D₁ p) * ((wt p.1 * t p.1 : ℝ) : ℂ)) K.rect)
    (i₂ : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F₂ p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D₂ p) * ((wt p.1 * t p.1 : ℝ) : ℂ)) K.rect) :
    heightStripMoment c o lo hi wt F₀ D₀ t =
      -heightStripMoment c o lo hi wt F₁ D₁ t - heightStripMoment c o lo hi wt F₂ D₂ t := by
  unfold heightStripMoment
  rw [hR]
  have hae : ∀ᵐ p ∂(volume.restrict K.rect),
      ((((1 / (c - o) : ℝ)) : ℂ) * F₀ p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D₀ p) * ((wt p.1 * t p.1 : ℝ) : ℂ)
        = -(((((1 / (c - o) : ℝ)) : ℂ) * F₁ p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D₁ p)
            * ((wt p.1 * t p.1 : ℝ) : ℂ))
          - ((((1 / (c - o) : ℝ)) : ℂ) * F₂ p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D₂ p)
            * ((wt p.1 * t p.1 : ℝ) : ℂ) := by
    filter_upwards [hF, hD] with p h1 h2
    linear_combination ((((1 / (c - o) : ℝ)) : ℂ) * ((wt p.1 * t p.1 : ℝ) : ℂ)) * h1
      + ((((p.2 - o) / (c - o) : ℝ) : ℂ) * ((wt p.1 * t p.1 : ℝ) : ℂ)) * h2
  have n₁ : IntegrableOn (fun p => -(((((1 / (c - o) : ℝ)) : ℂ) * F₁ p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * D₁ p) * ((wt p.1 * t p.1 : ℝ) : ℂ))) K.rect := i₁.neg
  rw [integral_congr_ae hae, integral_sub n₁ i₂, integral_neg]
  ring

theorem height_identity {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hf : IsLocalSecondOrderField v G H) (n : ℤ)
    {c o lo hi : ℝ} (hc : 0 ≤ c) (ho : 0 ≤ o) (hco : c ≠ o) (hlh : lo < hi) (hlo : 0 ≤ lo)
    {t : ℝ → ℝ} (ht : ContDiff ℝ ∞ t) :
    heightStripMoment c o lo hi (fun r => r) (gradMode m n G 2 2) (modeThird m n H 2 2 2) t =
      -(((hi * t hi : ℝ) : ℂ) * cornerMoment hi lo c o (fun p => modeVec m n v p.1 p.2 0) (gradMode m n G 0 0)
          (gradMode m n G 0 2) (modeThird m n H 0 0 2))
        + ((lo * t lo : ℝ) : ℂ) * cornerMoment lo hi c o (fun p => modeVec m n v p.1 p.2 0) (gradMode m n G 0 0)
          (gradMode m n G 0 2) (modeThird m n H 0 0 2)
        + heightStripMoment c o lo hi (fun _ => 1) (fun p => modeVec m n v p.1 p.2 0) (gradMode m n G 0 2)
          (fun u => u * deriv t u)
        - ((azimuth m n : ℂ) * Complex.I) *
          heightStripMoment c o lo hi (fun _ => 1) (fun p => modeVec m n v p.1 p.2 1) (gradMode m n G 1 2) t := by
  obtain ⟨K, hKdef⟩ : ∃ K : CellBox, K = ⟨lo, hi, min c o, max c o⟩ := ⟨_, rfl⟩
  have hr1 : K.r₁ = lo := by rw [hKdef]
  have hr2 : K.r₂ = hi := by rw [hKdef]
  have hz1 : K.z₁ = min c o := by rw [hKdef]
  have hz2 : K.z₂ = max c o := by rw [hKdef]
  have hK : IsCellBox K := ⟨⟨hr1 ▸ hlo, hr1 ▸ hr2 ▸ hlh⟩, ⟨hz1 ▸ le_min hc ho, hz1 ▸ hz2 ▸ min_lt_max.2 hco⟩⟩
  have hR : Icc lo hi ×ˢ Icc (min c o) (max c o) = K.rect := by rw [hKdef]; rfl
  have hw : Continuous (fun p : ℝ × ℝ => (((p.2 - o) / (c - o) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)
  have htc : Continuous (fun p : ℝ × ℝ => ((t p.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (ht.continuous.comp continuous_fst)
  have hG : ∀ a b : Fin 3, IntegrableOn (gradMode m n G a b) K.rect := fun a b => grad_rect_int K hK (m := m) hf n a b
  have hV : ∀ a : Fin 3, IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect := fun a =>
    ((localModeStripIntegrable m v G H hf n hi (min c o) (max c o)).1 a).mono_set (by
      rw [← hR]
      exact prod_mono (Icc_subset_Icc_left hlo) subset_rfl)
  have iJ : ∀ a : Fin 3, IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * gradMode m n G a a p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a a 2 p) * (((fun r => r) p.1 * t p.1 : ℝ) : ℂ)) K.rect := by
    intro a
    have c1 : Continuous (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * ((p.1 * t p.1 : ℝ) : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp (continuous_fst.mul (ht.continuous.comp continuous_fst)))
    have h1 := (hG a a).mul_continuousOn c1.continuousOn (rect_compact K)
    have h2 := offset_int K (third_weighted_int K hK (m := m) hf n a a 2) (o := 0) (fun _ => rfl)
      (fun p => (((p.2 - o) / (c - o) : ℝ) : ℂ) * ((t p.1 : ℝ) : ℂ)) (hw.mul htc)
    refine (h1.add h2).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [Pi.add_apply]
    push_cast
    ring
  have hsplit := height_trace_split K hR (fun r => r) t
    (F₀ := gradMode m n G 2 2) (F₁ := gradMode m n G 0 0) (F₂ := gradMode m n G 1 1)
    (D₀ := modeThird m n H 2 2 2) (D₁ := modeThird m n H 0 0 2) (D₂ := modeThird m n H 1 1 2)
    (by filter_upwards [grad_trace_zero K hK (m := m) hf n] with p hp
        simp only [Fin.sum_univ_three] at hp
        linear_combination hp)
    (by filter_upwards [third_trace_zero K hK (m := m) hf n 2] with p hp
        simp only [Fin.sum_univ_three] at hp
        linear_combination hp)
    (iJ 0) (iJ 1)
  have hang : heightStripMoment c o lo hi (fun r => r) (gradMode m n G 1 1) (modeThird m n H 1 1 2) t =
      heightStripMoment c o lo hi (fun _ => 1) (fun p => modeVec m n v p.1 p.2 0) (gradMode m n G 0 2) t
        + ((azimuth m n : ℂ) * Complex.I) *
          heightStripMoment c o lo hi (fun _ => 1) (fun p => modeVec m n v p.1 p.2 1) (gradMode m n G 1 2) t := by
    unfold heightStripMoment
    rw [hR]
    have j : ∀ a : Fin 3, IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * modeVec m n v p.1 p.2 a
        + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G a 2 p) * (((fun _ => (1 : ℝ)) p.1 * t p.1 : ℝ) : ℂ))
        K.rect := by
      intro a
      have h1 := IntegrableOn.mul_continuousOn ((hV a).const_mul ((1 / (c - o) : ℝ) : ℂ)) htc.continuousOn
        (rect_compact K)
      have h2 := ((hG a 2).continuousOn_mul hw.continuousOn (rect_compact K)).mul_continuousOn htc.continuousOn
        (rect_compact K)
      refine (h1.add h2).congr_fun (fun p _ => ?_) (rect_measurable K)
      simp only [Pi.add_apply]
      push_cast
      ring
    have hae : ∀ᵐ p ∂(volume.restrict K.rect),
        ((((1 / (c - o) : ℝ)) : ℂ) * gradMode m n G 1 1 p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 1 1 2 p)
          * (((fun r => r) p.1 * t p.1 : ℝ) : ℂ) =
        ((((1 / (c - o) : ℝ)) : ℂ) * modeVec m n v p.1 p.2 0 + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p)
          * (((fun _ => (1 : ℝ)) p.1 * t p.1 : ℝ) : ℂ)
        + ((azimuth m n : ℂ) * Complex.I) * (((((1 / (c - o) : ℝ)) : ℂ) * modeVec m n v p.1 p.2 1
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 1 2 p) * (((fun _ => (1 : ℝ)) p.1 * t p.1 : ℝ) : ℂ)) := by
      filter_upwards [ae_pos_on K hK (localAngularMode m v G H hf n),
        ae_pos_on K hK (localAngularHeightMode m v G H hf n)] with p h1 h2
      simp only [Complex.ofReal_mul, Complex.ofReal_one, one_mul]
      linear_combination ((((1 / (c - o) : ℝ)) : ℂ) * ((t p.1 : ℝ) : ℂ)) * h1.2.1
        + ((((p.2 - o) / (c - o) : ℝ) : ℂ) * ((t p.1 : ℝ) : ℂ)) * h2.2.1
    rw [integral_congr_ae hae, integral_add (j 0) ((j 1).const_mul _), integral_const_mul]
    ring
  have intT : ∀ g : ℝ → ℝ, Continuous g → (0 < lo ∨ ∃ g₀ : ℝ → ℝ, Continuous g₀ ∧ ∀ u, g u = (u - lo) * g₀ u) →
      IntegrableOn (fun p : ℝ × ℝ => (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p * ((g p.1 : ℝ) : ℂ))
        K.rect := by
    intro g hg hq
    have hgc : Continuous (fun p : ℝ × ℝ => ((g p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hg.comp continuous_fst)
    rcases hq with hq | ⟨g₀, hg₀, hfac⟩
    · have hT : IntegrableOn (modeThird m n H 0 0 2) K.rect :=
        (third_weighted_int K hK (m := m) hf n 0 0 2).congr_fun (fun p _ => by
          simp [CellBox.lineWeight, hr1, hq.ne']) (rect_measurable K)
      exact (hT.continuousOn_mul hw.continuousOn (rect_compact K)).mul_continuousOn hgc.continuousOn
        (rect_compact K)
    · have h2 := offset_int K (third_weighted_int K hK (m := m) hf n 0 0 2) (o := lo) (fun h => hr1 ▸ h)
        (fun p => (((p.2 - o) / (c - o) : ℝ) : ℂ) * ((g₀ p.1 : ℝ) : ℂ))
        (hw.mul (Complex.continuous_ofReal.comp (hg₀.comp continuous_fst)))
      refine h2.congr_fun (fun p _ => ?_) (rect_measurable K)
      simp only
      rw [hfac p.1]
      push_cast
      ring
  have hB : ∀ g : ℝ → ℝ, Continuous g → (0 < lo ∨ ∃ g₀ : ℝ → ℝ, Continuous g₀ ∧ ∀ u, g u = (u - lo) * g₀ u) →
      IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 0 0 p
        + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p) * ((g p.1 : ℝ) : ℂ)) K.rect := by
    intro g hg hq
    have hgc : Continuous (fun p : ℝ × ℝ => ((g p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hg.comp continuous_fst)
    have p1 := IntegrableOn.mul_continuousOn ((hG 0 0).const_mul ((1 / (c - o) : ℝ) : ℂ)) hgc.continuousOn
      (rect_compact K)
    refine (p1.add (intT g hg hq)).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [Pi.add_apply]
    ring
  have hA : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p) K.rect :=
    ((hV 0).const_mul _).add ((hG 0 2).continuousOn_mul hw.continuousOn (rect_compact K))
  have iA : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn (fun p : ℝ × ℝ =>
      (((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0 + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p)
        * ((f p.1 : ℝ) : ℂ)) K.rect := fun f hf' =>
    hA.mul_continuousOn (Complex.continuous_ofReal.comp (hf'.comp continuous_fst)).continuousOn (rect_compact K)
  have hI : ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → h lo = 0 → h hi = 0 →
      (0 < lo ∨ ∃ h₀ : ℝ → ℝ, Continuous h₀ ∧ ∀ u, h u = (u - lo) * h₀ u) →
      lineForm Prod.fst K.rect (fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p)
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 0 0 p
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p) (deriv h) h = 0 := by
    intro h hh h0 h1 hq
    have hd : Continuous (deriv h) := hh.continuous_deriv (by simp)
    have hh1 : ContDiff ℝ 1 h := hh.of_le (by simp)
    have hdc : Continuous (fun p : ℝ × ℝ => ((deriv h p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hd.comp continuous_fst)
    have hhc : Continuous (fun p : ℝ × ℝ => ((h p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hh.continuous.comp continuous_fst)
    have W1 := (localModeRadialWeak K hK m v G H hf n 0).2.2 h hh1 (hr1 ▸ h0) (hr2 ▸ h1)
      (fun _ => 1 / (c - o)) continuous_const
    have W2 := localRadialMixedWeak K hK m v G H hf n 0 h hh1 (hr1 ▸ h0) (hr2 ▸ h1)
      (fun z => (z - o) / (c - o)) ((continuous_id.sub continuous_const).div_const _)
    have k1 : IntegrableOn (fun p : ℝ × ℝ => (((deriv h p.1 : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
        + ((h p.1 : ℝ) : ℂ) * gradMode m n G 0 0 p) * (((fun _ => 1 / (c - o)) p.2 : ℝ) : ℂ)) K.rect := by
      have a1 := (hV 0).continuousOn_mul hdc.continuousOn (rect_compact K)
      have a2 := (hG 0 0).continuousOn_mul hhc.continuousOn (rect_compact K)
      exact (a1.add a2).mul_continuousOn continuous_const.continuousOn (rect_compact K)
    have k2 : IntegrableOn (fun p : ℝ × ℝ => (((deriv h p.1 : ℝ) : ℂ) * gradMode m n G 0 2 p
        + ((h p.1 : ℝ) : ℂ) * modeThird m n H 0 0 2 p) * (((fun z => (z - o) / (c - o)) p.2 : ℝ) : ℂ)) K.rect := by
      have a1 := ((hG 0 2).continuousOn_mul hdc.continuousOn (rect_compact K)).mul_continuousOn hw.continuousOn
        (rect_compact K)
      have a2 := intT h hh.continuous hq
      refine (a1.add a2).congr_fun (fun p _ => ?_) (rect_measurable K)
      simp only [Pi.add_apply]
      ring
    unfold lineForm
    have e : (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p) * ((deriv h p.1 : ℝ) : ℂ)
        + (((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 0 0 p
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p) * ((h p.1 : ℝ) : ℂ)) =
        fun p => (((deriv h p.1 : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
          + ((h p.1 : ℝ) : ℂ) * gradMode m n G 0 0 p) * (((fun _ => 1 / (c - o)) p.2 : ℝ) : ℂ)
        + (((deriv h p.1 : ℝ) : ℂ) * gradMode m n G 0 2 p
          + ((h p.1 : ℝ) : ℂ) * modeThird m n H 0 0 2 p) * (((fun z => (z - o) / (c - o)) p.2 : ℝ) : ℂ) := by
      funext p
      ring
    rw [e, integral_add k1 k2, W1, W2, add_zero]
  have htd : ∀ u, HasDerivAt t (deriv t u) u := fun u => (ht.differentiable (by simp) u).hasDerivAt
  have hdt : Continuous (deriv t) := ht.continuous_deriv (by simp)
  have hQ : 0 < lo ∨ ∃ t₀ : ℝ → ℝ, Continuous t₀ ∧ ∀ u, u * t u = (u - lo) * t₀ u := by
    rcases eq_or_lt_of_le hlo with h | h
    · exact Or.inr ⟨t, ht.continuous, fun u => by rw [← h]; ring⟩
    · exact Or.inl h
  have BP := lineForm_byParts (π := Prod.fst) (s := K.rect)
    (A := fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p)
    (B := fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 0 0 p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p)
    continuous_fst (rect_compact K) hA hlh (0 < lo) hB hI (t := fun u => u * t u) (contDiff_id.mul ht) hQ
  rw [show deriv (fun u => u * t u) = fun u => t u + u * deriv t u from funext fun u =>
    (((hasDerivAt_id' u).mul (htd u)).congr_deriv (by ring)).deriv] at BP
  have hcomb := lineForm_comb (π := Prod.fst) (s := K.rect)
    (A := fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p)
    (B := fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 0 0 p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p)
    (f := fun u => t u + u * deriv t u) (g := fun u => u * t u)
    t (fun _ => 0) (fun u => u * deriv t u) (fun _ => 0) (fun _ => 0) (fun u => u * t u) 1 1
    (fun u => by ring) (fun u => by ring)
    (by simpa using iA _ ht.continuous) (by simpa using iA _ (continuous_id.mul hdt))
    (by simpa using hB _ (continuous_id.mul ht.continuous) hQ)
  have e00 : heightStripMoment c o lo hi (fun r => r) (gradMode m n G 0 0) (modeThird m n H 0 0 2) t =
      edgeSign c o * lineForm Prod.fst K.rect
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p)
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 0 0 p
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p) (fun _ => 0) (fun u => u * t u) := by
    unfold heightStripMoment lineForm
    rw [hR]
    congr 1
    refine setIntegral_congr_fun (rect_measurable K) (fun p _ => ?_)
    simp only
    push_cast
    ring
  have ev : ∀ s : ℝ → ℝ, heightStripMoment c o lo hi (fun _ => 1) (fun p => modeVec m n v p.1 p.2 0)
      (gradMode m n G 0 2) s =
      edgeSign c o * lineForm Prod.fst K.rect
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p)
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 0 0 p
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p) s (fun _ => 0) := by
    intro s
    unfold heightStripMoment lineForm
    rw [hR]
    congr 1
    refine setIntegral_congr_fun (rect_measurable K) (fun p _ => ?_)
    simp only
    push_cast
    ring
  have eC1 : cornerMoment hi lo c o (fun p => modeVec m n v p.1 p.2 0) (gradMode m n G 0 0)
      (gradMode m n G 0 2) (modeThird m n H 0 0 2) =
      edgeSign c o * lineForm Prod.fst K.rect
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p)
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 0 0 p
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p)
        (fun _ => 1 / (hi - lo)) (fun u => (u - lo) / (hi - lo)) := by
    unfold cornerMoment lineForm
    rw [edgeSign_of_lt hlh, min_eq_right hlh.le, max_eq_left hlh.le, hR, one_mul]
    congr 1
    refine setIntegral_congr_fun (rect_measurable K) (fun p _ => ?_)
    simp only
    push_cast
    ring
  have eC0 : cornerMoment lo hi c o (fun p => modeVec m n v p.1 p.2 0) (gradMode m n G 0 0)
      (gradMode m n G 0 2) (modeThird m n H 0 0 2) =
      -(edgeSign c o * lineForm Prod.fst K.rect
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 0
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 0 2 p)
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 0 0 p
          + (((p.2 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 0 0 2 p)
        (fun _ => 1 / (lo - hi)) (fun u => (u - hi) / (lo - hi))) := by
    unfold cornerMoment lineForm
    rw [edgeSign_of_gt hlh, min_eq_left hlh.le, max_eq_right hlh.le, hR, neg_one_mul, neg_mul]
    congr 2
    refine setIntegral_congr_fun (rect_measurable K) (fun p _ => ?_)
    simp only
    push_cast
    ring
  rw [hsplit, hang, e00, ev t, ev (fun u => u * deriv t u), eC1, eC0]
  push_cast at BP hcomb ⊢
  linear_combination (edgeSign c o) * hcomb - (edgeSign c o) * BP

end Internal

end Breakdown.CertCell.SegmentNormal
