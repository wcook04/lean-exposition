import Breakdown.Cert.CoerciveDensityPassageModes

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PiecePassageModes

open DensityPassageModes

theorem tendsto_ite_zero {p : Prop} [Decidable p] {f : ℕ → ℝ} {a : ℝ} (hf : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun n => if p then 0 else f n) atTop (𝓝 (if p then 0 else a)) := by
  by_cases hp : p
  · simp only [if_pos hp]
    exact tendsto_const_nhds
  · simp only [if_neg hp]
    exact hf

open Classical in
theorem tendsto_edgeSum (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X : ℤ × ℤ → ℝ) {g : ℕ → ℤ × ℤ → ℝ}
    {g₀ : ℤ × ℤ → ℝ} (hg : ∀ κ, Tendsto (fun n => g n κ) atTop (𝓝 (g₀ κ))) (ι : ℤ × ℤ) :
    Tendsto (fun n => edgeSum h T X (g n) ι) atTop (𝓝 (edgeSum h T X g₀ ι)) := by
  unfold edgeSum
  by_cases h1 : ι ∈ T
  · simp only [if_pos h1]
    exact tendsto_finsetSum _ fun β _ => tendsto_ite_zero ((hg _).const_mul _)
  · by_cases h2 : -ι ∈ T
    · simp only [if_neg h1, if_pos h2]
      exact tendsto_finsetSum _ fun β _ => tendsto_ite_zero ((hg _).const_mul _)
    · simp only [if_neg h1, if_neg h2]
      exact tendsto_const_nhds

theorem piece_limits_of_modes {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space)
    {U : ℕ → ℝ → Space → Space} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {σ : ℝ} {y : Space}
    (hV : ∀ κ, Tendsto (fun n => modeVel κ (U n) σ y) atTop (𝓝 (modeVel κ v σ y)))
    (hG : ∀ κ, Tendsto (fun n => modeGrad κ (gradField (U n)) σ y) atTop (𝓝 (modeGrad κ G σ y)))
    (hH : ∀ κ, Tendsto (fun n => modeSecondDeriv κ (secondDerivField (U n)) σ y) atTop (𝓝 (modeSecondDeriv κ H σ y)))
    (hu0 : Tendsto (fun n => U n σ y) atTop (𝓝 (v σ y)))
    (hg0 : Tendsto (fun n => gradField (U n) σ y) atTop (𝓝 (G σ y))) :
    (∀ ι, Tendsto (fun n => piecePos m P (U n) (gradField (U n)) ι σ y) atTop
        (𝓝 (piecePos m P v G ι σ y))) ∧
      (∀ ι, Tendsto (fun n => pieceRest m h w W (U n) (gradField (U n)) (secondDerivField (U n)) ι σ y)
        atTop (𝓝 (pieceRest m h w W v G H ι σ y))) ∧
      Tendsto (fun n => stretchForm W (U n) (gradField (U n)) σ y) atTop
        (𝓝 (stretchForm W v G σ y)) := by
  have hc1 : Continuous (fun x : Fin 3 → ℂ => Real.sqrt (cnormSq x)) :=
    Real.continuous_sqrt.comp FieldModes.continuous_cnormSq
  have hc2 : Continuous (fun x : Fin 3 × Fin 3 → ℂ => Real.sqrt (cnormSq x)) :=
    Real.continuous_sqrt.comp FieldModes.continuous_cnormSq
  have hc3 : Continuous (fun x : Fin 3 × Fin 3 × Fin 3 → ℂ => Real.sqrt (cnormSq x)) :=
    Real.continuous_sqrt.comp FieldModes.continuous_cnormSq
  have hcurl : Continuous (fun x : Fin 3 × Fin 3 → ℂ => curlOfGrad x) :=
    continuous_pi fun i => by
      simp only [curlOfGrad]
      fun_prop
  have hcurlH : Continuous (fun x : Fin 3 × Fin 3 × Fin 3 → ℂ => curlGradOfSecondDeriv x) :=
    continuous_pi fun i => by
      simp only [curlGradOfSecondDeriv]
      fun_prop
  have hva : ∀ κ, Tendsto (fun n => velAmp (U n) κ σ y) atTop (𝓝 (velAmp v κ σ y)) := fun κ =>
    (hc1.tendsto _).comp (hV κ)
  have hga : ∀ κ, Tendsto (fun n => gradAmp (gradField (U n)) κ σ y) atTop (𝓝 (gradAmp G κ σ y)) :=
    fun κ => (hc2.tendsto _).comp (hG κ)
  have hta : ∀ κ, Tendsto (fun n => vortAmp (gradField (U n)) κ σ y) atTop (𝓝 (vortAmp G κ σ y)) :=
    fun κ => ((Real.continuous_sqrt.comp FieldModes.continuous_cnormSq).comp hcurl |>.tendsto _).comp (hG κ)
  have hha : ∀ κ, Tendsto (fun n => secondDerivAmp (secondDerivField (U n)) κ σ y) atTop (𝓝 (secondDerivAmp H κ σ y)) :=
    fun κ => (hc3.tendsto _).comp (hH κ)
  have hwa : ∀ κ, Tendsto (fun n => vortGradAmp (secondDerivField (U n)) κ σ y) atTop (𝓝 (vortGradAmp H κ σ y)) :=
    fun κ => ((Real.continuous_sqrt.comp FieldModes.continuous_cnormSq).comp hcurlH |>.tendsto _).comp (hH κ)
  refine ⟨fun ι => ?_, fun ι => ?_, ?_⟩
  · unfold piecePos pieceEpsPos pieceMuPos
    exact (tendsto_finsetSum _ fun β _ => ((hta ι).pow 2).const_mul _).add
      (tendsto_finsetSum _ fun β _ => ((hva ι).pow 2).const_mul _)
  · unfold pieceRest modeVals pieceEpsRestMode pieceMuRestMode
    have hb : Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ =>
        baseDensity m.convD m.convZ (m.classOf ι) m.c w y p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
      unfold baseDensity
      fun_prop
    refine ((((hb.tendsto _).comp ((hha ι).prodMk_nhds ((hwa ι).prodMk_nhds ((hga ι).prodMk_nhds
      ((hta ι).prodMk_nhds (hva ι))))))).add (tendsto_finsetSum _ fun β _ => ?_)).add
      (tendsto_finsetSum _ fun β _ => ?_)
    · exact (((hta ι).const_mul _).mul ((((tendsto_edgeSum h _ _ hwa ι).add (tendsto_edgeSum h _ _ hta ι)).add
        (tendsto_edgeSum h _ _ hva ι)).add (tendsto_edgeSum h _ _ hga ι))).neg
    · exact (((hva ι).const_mul _).mul (tendsto_edgeSum h _ _ hga ι)).neg.sub
        (((((tendsto_finsetSum _ fun α _ => (hva _).const_mul _).pow 2).div_const _).add
          (((hva ι).pow 2).const_mul _)).const_mul _)
  · have e : ∀ n, stretchForm W (U n) (gradField (U n)) σ y = stretchOf W σ y (U n σ y, gradField (U n) σ y) :=
      fun n => stretchForm_eq_of W (U n) (gradField (U n)) σ y
    have hs := ((continuous_stretchForm W σ y).tendsto (v σ y, G σ y)).comp (hu0.prodMk_nhds hg0)
    rw [← stretchForm_eq_of W v G σ y] at hs
    exact hs.congr fun n => (e n).symm

theorem ae_subseq_modes (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
      (∀ κ, Tendsto (fun n => modeVel κ (u (φ n)) σ y) atTop (𝓝 (modeVel κ v σ y))) ∧
      (∀ κ, Tendsto (fun n => modeGrad κ (gradField (u (φ n))) σ y) atTop (𝓝 (modeGrad κ G σ y))) ∧
      (∀ κ, Tendsto (fun n => modeSecondDeriv κ (secondDerivField (u (φ n))) σ y) atTop (𝓝 (modeSecondDeriv κ H σ y))) ∧
      Tendsto (fun n => u (φ n) σ y) atTop (𝓝 (v σ y)) ∧
      Tendsto (fun n => gradField (u (φ n)) σ y) atTop (𝓝 (G σ y)) := by
  obtain ⟨φ, hφ, hae⟩ := PassageCommon.ae_subseq_fields hSP hv hu (E := diffModes u v G H)
    (fun k n => modeDiff_aemeasurable hSP hv hu k.unpair.1 (modeIndex k.unpair.2) n)
    (fun k => modeDiff_tendsto hPars hSP hv hu k.unpair.1 (modeIndex k.unpair.2))
  have hlin := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) 1)
    (Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space))
      (ae_modes_sub hSP hv hu))
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae, hlin] with σ h1 h2
  filter_upwards [h1, h2] with y hy hl
  obtain ⟨hk, hu0, hg0, -⟩ := hy
  refine ⟨fun κ => ?_, fun κ => ?_, fun κ => ?_, hu0, hg0⟩
  · have hk0 := hk (Nat.pair 0 (modeIndex.symm κ))
    simp only [diffModes_pair, modeDiff_zero] at hk0
    have hc := PassageCommon.tendsto_zero_of_ofReal (fun n => FieldModes.cnormSq_nonneg _) hk0
    refine tendsto_of_cnormSq ?_
    have e : ∀ n, cnormSq (modeVel κ (u (φ n)) σ y - modeVel κ v σ y) =
        (1 + ‖y‖) ^ 2 * cnormSq (modeVel κ (weightedDiff (u (φ n)) v) σ y) := fun n => by
      have h0 : 0 < 1 + ‖y‖ := by positivity
      rw [← (hl (φ n) κ).1, modeVel_weightedDiff, cnormSq_const_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_inv, abs_of_pos h0, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 h0.ne'), one_mul]
    have ht := hc.const_mul ((1 + ‖y‖) ^ 2)
    rw [mul_zero] at ht
    exact ht.congr fun n => (e n).symm
  · have hk1 := hk (Nat.pair 1 (modeIndex.symm κ))
    simp only [diffModes_pair, modeDiff_one] at hk1
    have hc := PassageCommon.tendsto_zero_of_ofReal (fun n => FieldModes.cnormSq_nonneg _) hk1
    refine tendsto_of_cnormSq ?_
    exact hc.congr fun n => by rw [(hl (φ n) κ).2.1]
  · have hk2 := hk (Nat.pair 2 (modeIndex.symm κ))
    simp only [diffModes_pair, modeDiff_two] at hk2
    have hc := PassageCommon.tendsto_zero_of_ofReal (fun n => FieldModes.cnormSq_nonneg _) hk2
    refine tendsto_of_cnormSq ?_
    exact hc.congr fun n => by rw [(hl (φ n) κ).2.2]

theorem tendsto_of_absorb_bound {e D : ℕ → ℝ → Space → ℝ≥0∞} {A : ℝ → Space → ℝ≥0∞} {K : ℝ}
    (hD : ∀ n, AEMeasurable (fun z : ℝ × Space => D n z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
    (hA : AEMeasurable (fun z : ℝ × Space => A z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
    (hfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A σ y) < ⊤)
    (hlim : Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, D n σ y) atTop (𝓝 0))
    (hb : ∀ t : ℝ, 0 < t → ∀ n σ y,
      e n σ y ≤ ENNReal.ofReal (K * (1 + 1 / t)) * D n σ y + ENNReal.ofReal (K * t) * A σ y) :
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, e n σ y) atTop (𝓝 0) := by
  have hint : ∀ t : ℝ, 0 < t → ∀ n, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, e n σ y) ≤
      ENNReal.ofReal (K * (1 + 1 / t)) * (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, D n σ y)
        + ENNReal.ofReal (K * t) * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A σ y := by
    intro t ht n
    have hmd := (hD n).const_mul (ENNReal.ofReal (K * (1 + 1 / t)))
    have hma := hA.const_mul (ENNReal.ofReal (K * t))
    calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, e n σ y)
        ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            (ENNReal.ofReal (K * (1 + 1 / t)) * D n σ y + ENNReal.ofReal (K * t) * A σ y) :=
          lintegral_mono fun σ => lintegral_mono fun y => hb t ht n σ y
      _ = ∫⁻ z, (ENNReal.ofReal (K * (1 + 1 / t)) * D n z.1 z.2 + ENNReal.ofReal (K * t) * A z.1 z.2)
            ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
          (lintegral_prod _ (hmd.add hma)).symm
      _ = ENNReal.ofReal (K * (1 + 1 / t)) * (∫⁻ z, D n z.1 z.2 ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
            + ENNReal.ofReal (K * t) * ∫⁻ z, A z.1 z.2 ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
          rw [lintegral_add_left' hmd, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := by rw [lintegral_prod _ (hD n), lintegral_prod _ hA]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (K * t)) (𝓝[>] 0) (𝓝 0) := by
    have hct : Continuous (fun t : ℝ => ENNReal.ofReal (K * t)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
    have h0 := (hct.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h0
  have hc := ENNReal.Tendsto.mul_const h1 (Or.inr hfin.ne)
  rw [zero_mul] at hc
  obtain ⟨t, htJ, ht⟩ := ((hc.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne'))).and
    self_mem_nhdsWithin).exists
  have hI := ENNReal.Tendsto.const_mul hlim (Or.inr (ENNReal.ofReal_ne_top (r := K * (1 + 1 / t))))
  rw [mul_zero] at hI
  filter_upwards [hI.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne'))] with n hn
  calc _ ≤ _ := hint t ht n
    _ ≤ ε / 2 + ε / 2 := add_le_add hn.le htJ.le
    _ = ε := ENNReal.add_halves ε

end Internal.PiecePassageModes

end Coercive

end Breakdown
