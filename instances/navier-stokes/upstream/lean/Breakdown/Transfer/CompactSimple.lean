import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown

namespace CompactSimpleInternal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem extendPiece_eq {T : ℝ} (hT : 0 ≤ T) (f : Piece X T) (s : ℝ) :
    extendPiece f s = f (projIcc 0 T hT s) := by
  simp only [extendPiece, dif_pos hT]
  rfl

theorem norm_extendPiece_le {T : ℝ} (f : Piece X T) (s : ℝ) : ‖extendPiece f s‖ ≤ ‖f‖ := by
  by_cases hT : 0 ≤ T
  · rw [extendPiece_eq hT]
    exact f.norm_coe_le_norm _
  · simp only [extendPiece, dif_neg hT, norm_zero]
    exact norm_nonneg _

theorem continuous_extendPiece {T : ℝ} (f : Piece X T) : Continuous (extendPiece f) := by
  by_cases hT : 0 ≤ T
  · have h : extendPiece f = fun s => f (projIcc 0 T hT s) := funext (extendPiece_eq hT f)
    rw [h]
    exact f.continuous.comp continuous_projIcc
  · have h : extendPiece f = fun _ => (0 : X) := funext fun s => by
      simp only [extendPiece, dif_neg hT]
    rw [h]
    exact continuous_const

theorem continuousOn_G_apply [CompleteSpace X] (H : HeatBilinear X) :
    ContinuousOn (fun p : ℝ × X => H.G p.1 p.2) (Ici 0 ×ˢ univ) := by
  intro p hp
  have h1 : ContinuousWithinAt (fun q : ℝ × X => H.G q.1 p.2) (Ici 0 ×ˢ univ) p :=
    ((H.G_cont p.2).comp continuousOn_fst (fun q hq => hq.1)) p hp
  have h2 : Tendsto (fun q : ℝ × X => H.G q.1 (q.2 - p.2)) (𝓝[Ici 0 ×ˢ univ] p) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun q : ℝ × X => ‖q.2 - p.2‖)
    · filter_upwards [self_mem_nhdsWithin] with q hq
      calc ‖H.G q.1 (q.2 - p.2)‖ ≤ ‖H.G q.1‖ * ‖q.2 - p.2‖ := (H.G q.1).le_opNorm _
        _ ≤ 1 * ‖q.2 - p.2‖ := by
          gcongr
          exact H.G_norm _ hq.1
        _ = ‖q.2 - p.2‖ := one_mul _
    · have h3 : Tendsto (fun q : ℝ × X => ‖q.2 - p.2‖) (𝓝 p) (𝓝 ‖p.2 - p.2‖) :=
        ((continuous_snd.sub continuous_const).norm).tendsto p
      rw [sub_self, norm_zero] at h3
      exact h3.mono_left nhdsWithin_le_nhds
  have h4 := h1.tendsto.add h2
  rw [add_zero] at h4
  refine h4.congr (fun q => ?_)
  rw [map_sub]
  abel

end CompactSimpleInternal

open CompactSimpleInternal in
theorem compactSimple_of (h1 : VarConstIntegralStatement) (h2 : PieceOperatorStatement) :
    CompactSimpleStatement := by
  intro X _ _ _ H T y φ f hT hT1 hK hf
  have hT0 : 0 ≤ T := hT.le
  have hfe : ∀ s, extendPiece f s = φ (projIcc 0 T hT0 s) • y := fun s => by
    rw [extendPiece_eq hT0, hf]
  have hOp : ∀ v : Piece X T, ((pieceEnd T).comp (H.pieceBil T f)) v =
      ∫ s in (0 : ℝ)..T, H.K (T - s) (extendPiece f s) (extendPiece v s) := by
    intro v
    have h := (h2 X H T hT).1 f v ⟨T, hT0, le_rfl⟩
    simp only [ContinuousLinearMap.comp_apply, pieceEnd, dif_pos hT0,
      ContinuousMap.evalCLM_apply]
    exact h
  have hlimc : ContinuousAt (fun ε : ℝ => 4 * H.CK * ε ^ (1 / 4 : ℝ) * ‖f‖ * 1) 0 :=
    ((continuousAt_const.mul (Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num)))).mul
      continuousAt_const).mul continuousAt_const
  have h00 : 4 * H.CK * (0 : ℝ) ^ (1 / 4 : ℝ) * ‖f‖ * 1 = 0 := by
    rw [Real.zero_rpow (by norm_num)]
    ring
  have hlim : Tendsto (fun ε : ℝ => 4 * H.CK * ε ^ (1 / 4 : ℝ) * ‖f‖ * 1) (𝓝[>] 0) (𝓝 0) := by
    have h := hlimc.tendsto
    simp only [h00] at h
    exact h.mono_left nhdsWithin_le_nhds
  have htb : TotallyBounded (((pieceEnd T).comp (H.pieceBil T f)) '' closedBall 0 1) := by
    refine Metric.totallyBounded_iff.2 (fun δ hδ => ?_)
    obtain ⟨ε, hεδ, hε⟩ :=
      ((hlim.eventually (gt_mem_nhds (half_pos hδ))).and (Ioo_mem_nhdsGT hT)).exists
    have hKc : IsCompact (closure (H.K ε y '' closedBall 0 ‖φ‖)) :=
      IsCompactOperator.isCompact_closure_image_closedBall (f := (H.K ε y : X →ₗ[ℝ] X))
        (hK ε hε.1) ‖φ‖
    have hZ : IsCompact ((fun p : ℝ × X => H.G p.1 p.2) ''
        (Icc 0 T ×ˢ closure (H.K ε y '' closedBall 0 ‖φ‖))) :=
      (isCompact_Icc.prod hKc).image_of_continuousOn
        ((continuousOn_G_apply H).mono (prod_mono Icc_subset_Ici_self (subset_univ _)))
    have hC : IsCompact ((fun x : X => (T - ε) • x) '' closure (convexHull ℝ
        ((fun p : ℝ × X => H.G p.1 p.2) '' (Icc 0 T ×ˢ closure (H.K ε y '' closedBall 0 ‖φ‖))))) :=
      ((hZ.totallyBounded.convexHull.closure).isCompact_of_isClosed isClosed_closure).image
        (continuous_const_smul (T - ε))
    obtain ⟨t, htf, hcov⟩ := Metric.totallyBounded_iff.1 hC.totallyBounded (δ / 2) (half_pos hδ)
    refine ⟨t, htf, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hv1 : ‖v‖ ≤ 1 := by simpa using hv
    have hbf : ∀ s ∈ Icc (0 : ℝ) T, ‖extendPiece f s‖ ≤ ‖f‖ := fun s _ => norm_extendPiece_le f s
    have hbv : ∀ s ∈ Icc (0 : ℝ) T, ‖extendPiece v s‖ ≤ 1 :=
      fun s _ => (norm_extendPiece_le v s).trans hv1
    have hint := ((h1 X H (extendPiece f) (extendPiece v) 0 T ‖f‖ 1 hT0
      (continuous_extendPiece f).continuousOn (continuous_extendPiece v).continuousOn
      hbf hbv).1 T ⟨hT0, le_rfl⟩)
    have hmid : T - ε ∈ uIcc (0 : ℝ) T := mem_uIcc_of_le (by linarith [hε.2]) (by linarith [hε.1])
    have hA : IntervalIntegrable (fun s => H.K (T - s) (extendPiece f s) (extendPiece v s))
        volume 0 (T - ε) := hint.mono_set (uIcc_subset_uIcc left_mem_uIcc hmid)
    have hB : IntervalIntegrable (fun s => H.K (T - s) (extendPiece f s) (extendPiece v s))
        volume (T - ε) T := hint.mono_set (uIcc_subset_uIcc hmid right_mem_uIcc)
    have hsplit : ((pieceEnd T).comp (H.pieceBil T f)) v =
        (∫ s in (0 : ℝ)..(T - ε), H.K (T - s) (extendPiece f s) (extendPiece v s)) +
          ∫ s in (T - ε)..T, H.K (T - s) (extendPiece f s) (extendPiece v s) := by
      rw [hOp, intervalIntegral.integral_add_adjacent_intervals hA hB]
    have htail : ‖∫ s in (T - ε)..T, H.K (T - s) (extendPiece f s) (extendPiece v s)‖ < δ / 2 := by
      have h := (h1 X H (extendPiece f) (extendPiece v) (T - ε) T ‖f‖ 1 (by linarith [hε.1])
        (continuous_extendPiece f).continuousOn (continuous_extendPiece v).continuousOn
        (fun s _ => norm_extendPiece_le f s)
        (fun s _ => (norm_extendPiece_le v s).trans hv1)).2.1 T ⟨by linarith [hε.1], le_rfl⟩
        (by linarith [hε.1, hε.2])
      rw [sub_sub_cancel] at h
      exact h.trans_lt hεδ
    have hmem : ∀ s ∈ Ioc (0 : ℝ) (T - ε), H.K (T - s) (extendPiece f s) (extendPiece v s) ∈
        (fun p : ℝ × X => H.G p.1 p.2) '' (Icc 0 T ×ˢ closure (H.K ε y '' closedBall 0 ‖φ‖)) := by
      intro s hs
      refine ⟨(T - ε - s, H.K ε y (φ (projIcc 0 T hT0 s) • extendPiece v s)),
        ⟨⟨by linarith [hs.2], by linarith [hs.1, hε.1]⟩, subset_closure ⟨_, ?_, rfl⟩⟩, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul]
        calc ‖φ (projIcc 0 T hT0 s)‖ * ‖extendPiece v s‖ ≤ ‖φ‖ * 1 :=
              mul_le_mul (φ.norm_coe_le_norm _) ((norm_extendPiece_le v s).trans hv1)
                (norm_nonneg _) (norm_nonneg _)
          _ = ‖φ‖ := mul_one _
      · show H.G (T - ε - s) (H.K ε y (φ (projIcc 0 T hT0 s) • extendPiece v s)) = _
        rw [H.K_shift (T - ε - s) ε (by linarith [hs.2]) hε.1, hfe s,
          show T - ε - s + ε = T - s by ring]
        simp only [map_smul, smul_apply]
    have hpos : 0 < T - ε := by linarith [hε.2]
    have havg := (convex_convexHull ℝ ((fun p : ℝ × X => H.G p.1 p.2) ''
        (Icc 0 T ×ˢ closure (H.K ε y '' closedBall 0 ‖φ‖)))).set_average_mem_closure
      (μ := volume) (t := Ioc 0 (T - ε))
      (f := fun s => H.K (T - s) (extendPiece f s) (extendPiece v s))
      (by rw [Real.volume_Ioc]; simpa using hpos) (by simp [Real.volume_Ioc])
      ((ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall fun s hs => subset_convexHull ℝ _ (hmem s hs))) hA.1
    have hI1 : (∫ s in (0 : ℝ)..(T - ε), H.K (T - s) (extendPiece f s) (extendPiece v s)) ∈
        (fun x : X => (T - ε) • x) '' closure (convexHull ℝ
          ((fun p : ℝ × X => H.G p.1 p.2) ''
            (Icc 0 T ×ˢ closure (H.K ε y '' closedBall 0 ‖φ‖)))) := by
      refine ⟨_, havg, ?_⟩
      show (T - ε) • _ = _
      rw [setAverage_eq, Real.volume_real_Ioc_of_le hpos.le, sub_zero,
        smul_inv_smul₀ hpos.ne', intervalIntegral.integral_of_le hpos.le]
    obtain ⟨c, hc, hdc⟩ : ∃ c ∈ t, (∫ s in (0 : ℝ)..(T - ε),
        H.K (T - s) (extendPiece f s) (extendPiece v s)) ∈ ball c (δ / 2) := by
      simpa only [mem_iUnion, exists_prop] using hcov hI1
    refine mem_iUnion₂.2 ⟨c, hc, ?_⟩
    rw [mem_ball, hsplit, dist_eq_norm]
    rw [mem_ball, dist_eq_norm] at hdc
    calc ‖(∫ s in (0 : ℝ)..(T - ε), H.K (T - s) (extendPiece f s) (extendPiece v s)) +
          (∫ s in (T - ε)..T, H.K (T - s) (extendPiece f s) (extendPiece v s)) - c‖
        = ‖((∫ s in (0 : ℝ)..(T - ε), H.K (T - s) (extendPiece f s) (extendPiece v s)) - c) +
          ∫ s in (T - ε)..T, H.K (T - s) (extendPiece f s) (extendPiece v s)‖ := by
          congr 1
          abel
      _ ≤ _ := norm_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add hdc htail
      _ = δ := add_halves δ
  refine ⟨closure (((pieceEnd T).comp (H.pieceBil T f)) '' closedBall 0 1),
    htb.closure.isCompact_of_isClosed isClosed_closure, ?_⟩
  exact Filter.mem_of_superset (closedBall_mem_nhds 0 one_pos)
    (fun v hv => subset_closure (mem_image_of_mem _ hv))

end Breakdown
