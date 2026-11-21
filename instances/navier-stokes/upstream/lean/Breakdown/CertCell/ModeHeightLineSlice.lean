import Breakdown.CertCell.BridgeStatements

open scoped ContDiff Topology
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.CertCell.Bridge

namespace Internal.HeightLine

abbrev seg (N : ℕ) : Set ℝ := Icc (-(N : ℝ)) N

theorem seg_le (N : ℕ) : -(N : ℝ) ≤ N := neg_le_self (Nat.cast_nonneg N)

def lineTests (N : ℕ) : Set (ℝ → ℝ) := {η | ContDiff ℝ ∞ η ∧ tsupport η ⊆ seg N}

def lineData (N : ℕ) (η : lineTests N) : C(seg N, ℝ) × C(seg N, ℝ) :=
  (⟨fun z => η.1 z, η.2.1.continuous.comp continuous_subtype_val⟩,
    ⟨fun z => deriv η.1 z, (η.2.1.continuous_deriv (by simp)).comp continuous_subtype_val⟩)

def linePair (f fz : ℝ → ℂ) (N : ℕ) (x : C(seg N, ℝ) × C(seg N, ℝ)) : ℂ :=
  ∫ z in seg N, ((x.2 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * f z
    + ((x.1 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * fz z

theorem lift_cont (N : ℕ) (u : C(seg N, ℝ)) :
    Continuous (fun z => ((u (projIcc _ _ (seg_le N) z) : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (u.continuous.comp continuous_projIcc)

theorem linePair_cont (f fz : ℝ → ℂ) (N : ℕ) (hf : IntegrableOn f (seg N)) (hfz : IntegrableOn fz (seg N)) :
    Continuous (linePair f fz N) := by
  have hi : ∀ (u : C(seg N, ℝ)) (w : ℝ → ℂ), IntegrableOn w (seg N) →
      IntegrableOn (fun z => ((u (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * w z) (seg N) :=
    fun u w hw => hw.continuousOn_mul (lift_cont N u).continuousOn isCompact_Icc
  set I : ℝ := (∫ z in seg N, ‖f z‖) + ∫ z in seg N, ‖fz z‖ with hI
  have hI0 : 0 ≤ I := add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  have key : ∀ x y : C(seg N, ℝ) × C(seg N, ℝ), ‖linePair f fz N y - linePair f fz N x‖ ≤ dist y x * I := by
    intro x y
    have iy : IntegrableOn (fun z => ((y.2 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * f z
        + ((y.1 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * fz z) (seg N) := (hi _ _ hf).add (hi _ _ hfz)
    have ix : IntegrableOn (fun z => ((x.2 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * f z
        + ((x.1 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * fz z) (seg N) := (hi _ _ hf).add (hi _ _ hfz)
    unfold linePair
    rw [← integral_sub iy ix, hI, mul_add,
      ← integral_const_mul, ← integral_const_mul, ← integral_add (hf.norm.const_mul _) (hfz.norm.const_mul _)]
    refine norm_integral_le_of_norm_le ((hf.norm.const_mul _).add (hfz.norm.const_mul _)) (Eventually.of_forall fun z => ?_)
    have d2 : |y.2 (projIcc _ _ (seg_le N) z) - x.2 (projIcc _ _ (seg_le N) z)| ≤ dist y x :=
      ((ContinuousMap.dist_apply_le_dist _).trans (le_max_right _ _)).trans_eq' (Real.dist_eq _ _).symm
    have d1 : |y.1 (projIcc _ _ (seg_le N) z) - x.1 (projIcc _ _ (seg_le N) z)| ≤ dist y x :=
      ((ContinuousMap.dist_apply_le_dist _).trans (le_max_left _ _)).trans_eq' (Real.dist_eq _ _).symm
    have e : ((y.2 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * f z + ((y.1 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * fz z
        - (((x.2 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * f z + ((x.1 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ) * fz z)
        = (((y.2 (projIcc _ _ (seg_le N) z) - x.2 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ)) * f z
          + (((y.1 (projIcc _ _ (seg_le N) z) - x.1 (projIcc _ _ (seg_le N) z) : ℝ) : ℂ)) * fz z := by
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right d2 (norm_nonneg _)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right d1 (norm_nonneg _)
  refine Metric.continuous_iff.2 fun x ε hε => ⟨ε / (I + 1), by positivity, fun y hy => ?_⟩
  rw [dist_eq_norm]
  refine (key x y).trans_lt ?_
  calc dist y x * I ≤ dist y x * (I + 1) := mul_le_mul_of_nonneg_left (by linarith) dist_nonneg
    _ < ε / (I + 1) * (I + 1) := mul_lt_mul_of_pos_right hy (by linarith)
    _ = ε := div_mul_cancel₀ _ (by linarith)

theorem rect_restrict (A B : Set ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (A ×ˢ B) = (volume.restrict A).prod (volume.restrict B) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

theorem compact_in_Ioi {k : Set ℝ} (hk : IsCompact k) (hs : k ⊆ Ioi 0) : ∃ a b : ℝ, 0 < a ∧ k ⊆ Icc a b := by
  rcases k.eq_empty_or_nonempty with h | h
  · exact ⟨1, 1, one_pos, h ▸ empty_subset _⟩
  obtain ⟨x, hx, hmin⟩ := hk.exists_isMinOn h continuousOn_id
  obtain ⟨b, hb⟩ := hk.bddAbove
  exact ⟨x, b, hs hx, fun y hy => ⟨hmin hy, hb hy⟩⟩


theorem fderiv_prod_test {g η : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hη : ContDiff ℝ ∞ η) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => g q.1 * η q.2) p (0, 1) = g p.1 * deriv η p.2 := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => g q.1) ((fderiv ℝ g p.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    ((hg.differentiable (by simp)) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => η q.2) ((fderiv ℝ η p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((hη.differentiable (by simp)) p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have h3 : HasFDerivAt (fun q : ℝ × ℝ => g q.1 * η q.2) _ p := h1.mul h2
  rw [h3.fderiv]
  show g p.1 * fderiv ℝ η p.2 1 + η p.2 * fderiv ℝ g p.1 0 = _
  rw [map_zero, mul_zero, add_zero]
  rfl

theorem zero_off_seg {N : ℕ} {η : ℝ → ℝ} (hηt : tsupport η ⊆ seg N) {z : ℝ} (hz : z ∉ seg N) :
    η z = 0 ∧ deriv η z = 0 :=
  ⟨by by_contra h; exact hz (hηt (subset_tsupport _ h)), deriv_of_notMem_tsupport fun h => hz (hηt h)⟩

theorem ae_line_zero (F Fz : ℝ × ℝ → ℂ)
    (hF : ∀ a b c d : ℝ, 0 < a → IntegrableOn F (Icc a b ×ˢ Icc c d))
    (hFz : ∀ a b c d : ℝ, 0 < a → IntegrableOn Fz (Icc a b ×ˢ Icc c d))
    (hid : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, ((ψ p : ℝ) : ℂ) * Fz p)
    (N : ℕ) (η : lineTests N) :
    ∀ᵐ r, 0 < r → linePair (fun z => F (r, z)) (fun z => Fz (r, z)) N (lineData N η) = 0 := by
  obtain ⟨η, hηs, hηt⟩ := η
  set Q : ℝ × ℝ → ℂ := fun p => ((deriv η p.2 : ℝ) : ℂ) * F p + ((η p.2 : ℝ) : ℂ) * Fz p with hQ
  have cd : Continuous (deriv η) := hηs.continuous_deriv (by simp)
  have hQi : ∀ a b : ℝ, 0 < a → IntegrableOn Q (Icc a b ×ˢ seg N) := by
    intro a b ha
    have hc : IsCompact (Icc a b ×ˢ seg N) := isCompact_Icc.prod isCompact_Icc
    exact ((hF a b _ _ ha).continuousOn_mul
      ((Complex.continuous_ofReal.comp (cd.comp continuous_snd)).continuousOn) hc).add
      ((hFz a b _ _ ha).continuousOn_mul
        ((Complex.continuous_ofReal.comp (hηs.continuous.comp continuous_snd)).continuousOn) hc)
  have hL : ∀ r, linePair (fun z => F (r, z)) (fun z => Fz (r, z)) N (lineData N ⟨η, hηs, hηt⟩) =
      ∫ z in seg N, Q (r, z) := by
    intro r
    refine setIntegral_congr_fun measurableSet_Icc fun z hz => ?_
    simp only [lineData, ContinuousMap.coe_mk, projIcc_of_mem _ hz, hQ]
  simp only [hL]
  have hloc : LocallyIntegrableOn (fun r => ∫ z in seg N, Q (r, z)) (Ioi 0) := by
    refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun k hk hkc => ?_
    obtain ⟨a, b, ha, hab⟩ := compact_in_Ioi hkc hk
    have h := hQi a b ha
    rw [IntegrableOn, rect_restrict] at h
    exact (show IntegrableOn (fun r => ∫ z in seg N, Q (r, z)) (Icc a b) volume from h.integral_prod_left).mono_set hab
  refine isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs => ?_
  obtain ⟨a, b, ha, hab⟩ := compact_in_Ioi hgc.isCompact hgs
  have hgz : ∀ r, r ∉ Icc a b → g r = 0 := fun r hr => by
    by_contra h; exact hr (hab (subset_tsupport _ h))
  set ψ : ℝ × ℝ → ℝ := fun q => g q.1 * η q.2 with hψdef
  have hψ : ContDiff ℝ ∞ ψ := (hg.comp contDiff_fst).mul (hηs.comp contDiff_snd)
  have hηc : IsCompact (tsupport η) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hηt
  have hsupp : tsupport ψ ⊆ tsupport g ×ˢ tsupport η := by
    refine closure_minimal (fun q hq => ?_) ((isClosed_tsupport _).prod (isClosed_tsupport _))
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hq), subset_tsupport _ (right_ne_zero_of_mul hq)⟩
  have hcs : HasCompactSupport ψ := (hgc.isCompact.prod hηc).of_isClosed_subset (isClosed_tsupport _) hsupp
  have hpos : ∀ p ∈ tsupport ψ, 0 < p.1 := fun p hp => hgs (hsupp hp).1
  have hrect : IsCompact (Icc a b ×ˢ seg N) := isCompact_Icc.prod isCompact_Icc
  have hout : ∀ p : ℝ × ℝ, p ∉ Icc a b ×ˢ seg N → g p.1 = 0 ∨ (η p.2 = 0 ∧ deriv η p.2 = 0) := by
    intro p hp
    by_cases h1 : p.1 ∈ Icc a b
    · exact Or.inr (zero_off_seg hηt fun h2 => hp ⟨h1, h2⟩)
    · exact Or.inl (hgz _ h1)
  have cg : Continuous (fun p : ℝ × ℝ => ((g p.1 : ℝ) : ℂ)) := Complex.continuous_ofReal.comp (hg.continuous.comp continuous_fst)
  have hint : IntegrableOn (fun p => ((g p.1 : ℝ) : ℂ) * Q p) (Icc a b ×ˢ seg N) :=
    (hQi a b ha).continuousOn_mul cg.continuousOn hrect
  have e1 : (fun p => ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p) = fun p => ((g p.1 * deriv η p.2 : ℝ) : ℂ) * F p :=
    funext fun p => by rw [hψdef, fderiv_prod_test hg hηs p]
  have i1 : Integrable (fun p => ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p) := by
    rw [e1]
    refine ((hF a b _ _ ha).continuousOn_mul (Complex.continuous_ofReal.comp
      ((hg.continuous.comp continuous_fst).mul (cd.comp continuous_snd))).continuousOn hrect).integrable_of_forall_notMem_eq_zero
      fun p hp => ?_
    rcases hout p hp with h | h <;> simp [h]
  have i2 : Integrable (fun p => ((ψ p : ℝ) : ℂ) * Fz p) := by
    refine ((hFz a b _ _ ha).continuousOn_mul (Complex.continuous_ofReal.comp hψ.continuous).continuousOn
      hrect).integrable_of_forall_notMem_eq_zero fun p hp => ?_
    rcases hout p hp with h | h <;> simp [hψdef, h]
  calc ∫ r, g r • ∫ z in seg N, Q (r, z)
      = ∫ r in Icc a b, g r • ∫ z in seg N, Q (r, z) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by rw [hgz r hr, zero_smul]).symm
    _ = ∫ r in Icc a b, ∫ z in seg N, ((g r : ℝ) : ℂ) * Q (r, z) :=
        setIntegral_congr_fun measurableSet_Icc fun r _ => by rw [Complex.real_smul, integral_const_mul]
    _ = ∫ p in Icc a b ×ˢ seg N, ((g p.1 : ℝ) : ℂ) * Q p := (setIntegral_prod _ hint).symm
    _ = ∫ p, ((g p.1 : ℝ) : ℂ) * Q p := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
        rcases hout p hp with h | h <;> simp [hQ, h]
    _ = ∫ p, (((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p + ((ψ p : ℝ) : ℂ) * Fz p) := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [hQ, hψdef, fderiv_prod_test hg hηs p]
        push_cast
        ring
    _ = 0 := by rw [integral_add i1 i2, hid ψ hψ hcs hpos, neg_add_cancel]

theorem ae_line_integrable (F : ℝ × ℝ → ℂ) (hF : ∀ a b c d : ℝ, 0 < a → IntegrableOn F (Icc a b ×ˢ Icc c d)) :
    ∀ᵐ r, ∀ k N : ℕ, r ∈ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) → IntegrableOn (fun z => F (r, z)) (seg N) := by
  rw [ae_all_iff]; intro k
  rw [ae_all_iff]; intro N
  have h := hF (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) (-(N : ℝ)) N (by positivity)
  rw [IntegrableOn, rect_restrict] at h
  exact (ae_restrict_iff' measurableSet_Icc).1 h.prod_right_ae

theorem slice_weak (F Fz : ℝ × ℝ → ℂ)
    (hF : ∀ a b c d : ℝ, 0 < a → IntegrableOn F (Icc a b ×ˢ Icc c d))
    (hFz : ∀ a b c d : ℝ, 0 < a → IntegrableOn Fz (Icc a b ×ˢ Icc c d))
    (hid : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, ((ψ p : ℝ) : ℂ) * Fz p) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ h : ℝ, 0 < h →
      HasWeakDerivOn (fun z => F (r, z)) (fun z => Fz (r, z)) (-h) h := by
  have hsep : ∀ N : ℕ, ∃ t ⊆ range (lineData N), t.Countable ∧ range (lineData N) ⊆ closure t :=
    fun N => (TopologicalSpace.IsSeparable.of_separableSpace _).exists_countable_dense_subset
  choose t hts htc hdense using hsep
  have hpre : ∀ N, ∀ x ∈ t N, ∃ η : lineTests N, lineData N η = x := fun N x hx => hts N hx
  choose η hη using hpre
  have hzero : ∀ᵐ r, ∀ N : ℕ, ∀ x : t N, 0 < r →
      linePair (fun z => F (r, z)) (fun z => Fz (r, z)) N x = 0 := by
    rw [ae_all_iff]; intro N
    have := (htc N).to_subtype
    rw [ae_all_iff]; intro x
    filter_upwards [ae_line_zero F Fz hF hFz hid N (η N x.1 x.2)] with r hr h0
    rw [← hη N x.1 x.2]
    exact hr h0
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hzero, ae_line_integrable F hF, ae_line_integrable Fz hFz] with r hr hi hiz r0 h h0
  have r0' : (0 : ℝ) < r := r0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r ∈ Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (max r (1 / r))
    refine ⟨k, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      have := (le_max_right r (1 / r)).trans hk.le
      rw [div_le_iff₀ r0'] at this
      nlinarith
    · linarith [le_max_left r (1 / r)]
  obtain ⟨N, hN⟩ := exists_nat_ge h
  have hsub : Ioo (-h) h ⊆ seg N := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  refine ⟨(hi k N hk).mono_set hsub, (hiz k N hk).mono_set hsub, fun ψ hψ hc hs => ?_⟩
  have hψN : ψ ∈ lineTests N := ⟨hψ, hs.trans hsub⟩
  have hP : linePair (fun z => F (r, z)) (fun z => Fz (r, z)) N (lineData N ⟨ψ, hψN⟩) = 0 := by
    have hcl : closure (t N) ⊆ {x | linePair (fun z => F (r, z)) (fun z => Fz (r, z)) N x = 0} :=
      closure_minimal (fun x hx => hr N ⟨x, hx⟩ r0)
        (isClosed_eq (linePair_cont _ _ N (hi k N hk) (hiz k N hk)) continuous_const)
    exact hcl (hdense N (mem_range_self _))
  have hoff : ∀ z, z ∉ Ioo (-h) h → ψ z = 0 ∧ deriv ψ z = 0 := fun z hz =>
    ⟨by by_contra h'; exact hz (hs (subset_tsupport _ h')), deriv_of_notMem_tsupport fun h' => hz (hs h')⟩
  have hoff' : ∀ z, z ∉ seg N → ψ z = 0 ∧ deriv ψ z = 0 := fun z hz => hoff z fun h' => hz (hsub h')
  have cd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have i1 : IntegrableOn (fun z => ((deriv ψ z : ℝ) : ℂ) * F (r, z)) (seg N) :=
    (hi k N hk).continuousOn_mul (Complex.continuous_ofReal.comp cd).continuousOn isCompact_Icc
  have i2 : IntegrableOn (fun z => ((ψ z : ℝ) : ℂ) * Fz (r, z)) (seg N) :=
    (hiz k N hk).continuousOn_mul (Complex.continuous_ofReal.comp hψ.continuous).continuousOn isCompact_Icc
  have hP' : (∫ z in seg N, ((deriv ψ z : ℝ) : ℂ) * F (r, z)) + ∫ z in seg N, ((ψ z : ℝ) : ℂ) * Fz (r, z) = 0 := by
    rw [← integral_add i1 i2, ← hP]
    refine setIntegral_congr_fun measurableSet_Icc fun z hz => ?_
    simp only [lineData, ContinuousMap.coe_mk, projIcc_of_mem _ hz]
  have eA : ∫ z in Ioo (-h) h, F (r, z) * ((deriv ψ z : ℝ) : ℂ) = ∫ z in seg N, ((deriv ψ z : ℝ) : ℂ) * F (r, z) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [(hoff z hz).2],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [(hoff' z hz).2]]
    exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  have eB : ∫ z in Ioo (-h) h, Fz (r, z) * ((ψ z : ℝ) : ℂ) = ∫ z in seg N, ((ψ z : ℝ) : ℂ) * Fz (r, z) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [(hoff z hz).1],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by simp [(hoff' z hz).1]]
    exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [eA, eB]
  exact eq_neg_of_add_eq_zero_left hP'

end Internal.HeightLine

end Breakdown.CertCell.Bridge
