import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.CertCell.ModeHeightDerivative

open scoped ContDiff Topology
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.CertCell.SideTrace

namespace Internal.RadialModes

open Bridge Bridge.Internal.HeightLine Bridge.Internal.HeightOrbit Bridge.Internal.HeightModes

def rayTests (u w : ℝ) : Set (ℝ → ℝ) := {η | ContDiff ℝ ∞ η ∧ tsupport η ⊆ Icc u w}

def rayData (u w : ℝ) (η : rayTests u w) : C(Icc u w, ℝ) × C(Icc u w, ℝ) :=
  (⟨fun r => η.1 r, η.2.1.continuous.comp continuous_subtype_val⟩,
    ⟨fun r => deriv η.1 r, (η.2.1.continuous_deriv (by simp)).comp continuous_subtype_val⟩)

def rayPair (f fr : ℝ → ℂ) {u w : ℝ} (huw : u ≤ w) (x : C(Icc u w, ℝ) × C(Icc u w, ℝ)) : ℂ :=
  ∫ r in Icc u w, (((x.2 (projIcc u w huw r) : ℝ) : ℂ) * f r + ((x.1 (projIcc u w huw r) : ℝ) : ℂ) * fr r)

theorem ray_lift_cont {u w : ℝ} (huw : u ≤ w) (y : C(Icc u w, ℝ)) :
    Continuous (fun r => ((y (projIcc u w huw r) : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (y.continuous.comp continuous_projIcc)

theorem rayPair_cont (f fr : ℝ → ℂ) {u w : ℝ} (huw : u ≤ w) (hf : IntegrableOn f (Icc u w))
    (hfr : IntegrableOn fr (Icc u w)) : Continuous (rayPair f fr huw) := by
  have hi : ∀ (y : C(Icc u w, ℝ)) (h : ℝ → ℂ), IntegrableOn h (Icc u w) →
      IntegrableOn (fun r => ((y (projIcc u w huw r) : ℝ) : ℂ) * h r) (Icc u w) :=
    fun y h hh => hh.continuousOn_mul (ray_lift_cont huw y).continuousOn isCompact_Icc
  set I : ℝ := (∫ r in Icc u w, ‖f r‖) + ∫ r in Icc u w, ‖fr r‖ with hI
  have hI0 : 0 ≤ I :=
    add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  have key : ∀ x y : C(Icc u w, ℝ) × C(Icc u w, ℝ),
      ‖rayPair f fr huw y - rayPair f fr huw x‖ ≤ dist y x * I := by
    intro x y
    have iy : IntegrableOn (fun r => ((y.2 (projIcc u w huw r) : ℝ) : ℂ) * f r
        + ((y.1 (projIcc u w huw r) : ℝ) : ℂ) * fr r) (Icc u w) := (hi y.2 f hf).add (hi y.1 fr hfr)
    have ix : IntegrableOn (fun r => ((x.2 (projIcc u w huw r) : ℝ) : ℂ) * f r
        + ((x.1 (projIcc u w huw r) : ℝ) : ℂ) * fr r) (Icc u w) := (hi x.2 f hf).add (hi x.1 fr hfr)
    unfold rayPair
    rw [← integral_sub iy ix, hI, mul_add, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hf.norm.const_mul _) (hfr.norm.const_mul _)]
    refine norm_integral_le_of_norm_le ((hf.norm.const_mul _).add (hfr.norm.const_mul _))
      (Eventually.of_forall fun r => ?_)
    have d2 : |y.2 (projIcc u w huw r) - x.2 (projIcc u w huw r)| ≤ dist y x :=
      ((ContinuousMap.dist_apply_le_dist _).trans (le_max_right _ _)).trans_eq' (Real.dist_eq _ _).symm
    have d1 : |y.1 (projIcc u w huw r) - x.1 (projIcc u w huw r)| ≤ dist y x :=
      ((ContinuousMap.dist_apply_le_dist _).trans (le_max_left _ _)).trans_eq' (Real.dist_eq _ _).symm
    have e : ((y.2 (projIcc u w huw r) : ℝ) : ℂ) * f r + ((y.1 (projIcc u w huw r) : ℝ) : ℂ) * fr r
        - (((x.2 (projIcc u w huw r) : ℝ) : ℂ) * f r + ((x.1 (projIcc u w huw r) : ℝ) : ℂ) * fr r)
        = (((y.2 (projIcc u w huw r) - x.2 (projIcc u w huw r) : ℝ) : ℂ)) * f r
          + (((y.1 (projIcc u w huw r) - x.1 (projIcc u w huw r) : ℝ) : ℂ)) * fr r := by
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

theorem ray_deriv_test {η g : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hg : ContDiff ℝ ∞ g) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => η q.1 * g q.2) p (1, 0) = g p.2 * deriv η p.1 := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => η q.1) ((fderiv ℝ η p.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    ((hη.differentiable (by simp)) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => g q.2) ((fderiv ℝ g p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((hg.differentiable (by simp)) p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have h3 : HasFDerivAt (fun q : ℝ × ℝ => η q.1 * g q.2) _ p := h1.mul h2
  rw [h3.fderiv]
  show η p.1 * fderiv ℝ g p.2 0 + g p.2 * fderiv ℝ η p.1 1 = _
  rw [map_zero, mul_zero, zero_add]
  rfl

theorem ae_ray_zero (F Fr : ℝ × ℝ → ℂ)
    (hF : ∀ a b c d : ℝ, 0 < a → IntegrableOn F (Icc a b ×ˢ Icc c d))
    (hFr : ∀ a b c d : ℝ, 0 < a → IntegrableOn Fr (Icc a b ×ˢ Icc c d))
    (hid : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, ((ψ p : ℝ) : ℂ) * Fr p)
    {u w : ℝ} (hu : 0 < u) (huw : u ≤ w) (η : rayTests u w) :
    ∀ᵐ z, rayPair (fun r => F (r, z)) (fun r => Fr (r, z)) huw (rayData u w η) = 0 := by
  obtain ⟨η, hηs, hηt⟩ := η
  set Q : ℝ × ℝ → ℂ := fun p => ((deriv η p.1 : ℝ) : ℂ) * F p + ((η p.1 : ℝ) : ℂ) * Fr p with hQ
  have cd : Continuous (deriv η) := hηs.continuous_deriv (by simp)
  have hQi : ∀ c d : ℝ, IntegrableOn Q (Icc u w ×ˢ Icc c d) := by
    intro c d
    have hc : IsCompact (Icc u w ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
    exact ((hF u w c d hu).continuousOn_mul
      ((Complex.continuous_ofReal.comp (cd.comp continuous_fst)).continuousOn) hc).add
      ((hFr u w c d hu).continuousOn_mul
        ((Complex.continuous_ofReal.comp (hηs.continuous.comp continuous_fst)).continuousOn) hc)
  have hL : ∀ z, rayPair (fun r => F (r, z)) (fun r => Fr (r, z)) huw (rayData u w ⟨η, hηs, hηt⟩) =
      ∫ r in Icc u w, Q (r, z) := by
    intro z
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [rayData, ContinuousMap.coe_mk, projIcc_of_mem _ hr, hQ]
  simp only [hL]
  have hloc : LocallyIntegrable (fun z => ∫ r in Icc u w, Q (r, z)) volume := by
    refine locallyIntegrable_iff.2 fun k hk => ?_
    obtain ⟨c, hc⟩ := hk.bddBelow
    obtain ⟨d, hd⟩ := hk.bddAbove
    have h := hQi c d
    rw [IntegrableOn, rect_restrict] at h
    exact (show IntegrableOn (fun z => ∫ r in Icc u w, Q (r, z)) (Icc c d) volume from
      h.integral_prod_right).mono_set fun y hy => ⟨hc hy, hd hy⟩
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc => ?_
  obtain ⟨c, hc⟩ := hgc.isCompact.bddBelow
  obtain ⟨d, hd⟩ := hgc.isCompact.bddAbove
  have hgz : ∀ z, z ∉ Icc c d → g z = 0 := fun z hz => by
    by_contra h
    exact hz ⟨hc (subset_tsupport _ h), hd (subset_tsupport _ h)⟩
  set ψ : ℝ × ℝ → ℝ := fun q => η q.1 * g q.2 with hψdef
  have hψ : ContDiff ℝ ∞ ψ := (hηs.comp contDiff_fst).mul (hg.comp contDiff_snd)
  have hηc : IsCompact (tsupport η) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hηt
  have hsupp : tsupport ψ ⊆ tsupport η ×ˢ tsupport g := by
    refine closure_minimal (fun q hq => ?_) ((isClosed_tsupport _).prod (isClosed_tsupport _))
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hq), subset_tsupport _ (right_ne_zero_of_mul hq)⟩
  have hcs : HasCompactSupport ψ :=
    (hηc.prod hgc.isCompact).of_isClosed_subset (isClosed_tsupport _) hsupp
  have hpos : ∀ p ∈ tsupport ψ, 0 < p.1 := fun p hp => lt_of_lt_of_le hu (hηt (hsupp hp).1).1
  have hrect : IsCompact (Icc u w ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hout : ∀ p : ℝ × ℝ, p ∉ Icc u w ×ˢ Icc c d → g p.2 = 0 ∨ (η p.1 = 0 ∧ deriv η p.1 = 0) := by
    intro p hp
    by_cases h2 : p.2 ∈ Icc c d
    · refine Or.inr ⟨?_, ?_⟩
      · by_contra h
        exact hp ⟨hηt (subset_tsupport _ h), h2⟩
      · exact deriv_of_notMem_tsupport fun h => hp ⟨hηt h, h2⟩
    · exact Or.inl (hgz _ h2)
  have cg : Continuous (fun p : ℝ × ℝ => ((g p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hg.continuous.comp continuous_snd)
  have hint : IntegrableOn (fun p => ((g p.2 : ℝ) : ℂ) * Q p) (Icc u w ×ˢ Icc c d) :=
    (hQi c d).continuousOn_mul cg.continuousOn hrect
  have hint' := hint
  rw [IntegrableOn, rect_restrict] at hint'
  have e1 : (fun p => ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p) =
      fun p => ((g p.2 * deriv η p.1 : ℝ) : ℂ) * F p :=
    funext fun p => by rw [hψdef, ray_deriv_test hηs hg p]
  have i1 : Integrable (fun p => ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p) := by
    rw [e1]
    refine ((hF u w c d hu).continuousOn_mul (Complex.continuous_ofReal.comp
      ((hg.continuous.comp continuous_snd).mul (cd.comp continuous_fst))).continuousOn
      hrect).integrable_of_forall_notMem_eq_zero fun p hp => ?_
    rcases hout p hp with h | h <;> simp [h]
  have i2 : Integrable (fun p => ((ψ p : ℝ) : ℂ) * Fr p) := by
    refine ((hFr u w c d hu).continuousOn_mul (Complex.continuous_ofReal.comp hψ.continuous).continuousOn
      hrect).integrable_of_forall_notMem_eq_zero fun p hp => ?_
    rcases hout p hp with h | h <;> simp [hψdef, h]
  calc ∫ z, g z • ∫ r in Icc u w, Q (r, z)
      = ∫ z in Icc c d, g z • ∫ r in Icc u w, Q (r, z) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by rw [hgz z hz, zero_smul]).symm
    _ = ∫ z in Icc c d, ∫ r in Icc u w, ((g z : ℝ) : ℂ) * Q (r, z) :=
        setIntegral_congr_fun measurableSet_Icc fun z _ => by rw [Complex.real_smul, integral_const_mul]
    _ = ∫ p in Icc u w ×ˢ Icc c d, ((g p.2 : ℝ) : ℂ) * Q p := by
        rw [rect_restrict]
        exact (integral_prod_symm _ hint').symm
    _ = ∫ p, ((g p.2 : ℝ) : ℂ) * Q p := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
        rcases hout p hp with h | h <;> simp [hQ, h]
    _ = ∫ p, (((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p + ((ψ p : ℝ) : ℂ) * Fr p) := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [hQ, hψdef, ray_deriv_test hηs hg p]
        push_cast
        ring
    _ = 0 := by rw [integral_add i1 i2, hid ψ hψ hcs hpos, neg_add_cancel]

def lowEnd (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

def highEnd (N : ℕ) : ℝ := (N : ℝ) + 1

theorem lowEnd_pos (N : ℕ) : 0 < lowEnd N := by
  unfold lowEnd
  positivity

theorem band_le (N : ℕ) : lowEnd N ≤ highEnd N := by
  unfold lowEnd highEnd
  have h : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  exact ((div_le_one (by linarith)).2 h).trans h

theorem ae_ray_integrable (F : ℝ × ℝ → ℂ) (hF : ∀ a b c d : ℝ, 0 < a → IntegrableOn F (Icc a b ×ˢ Icc c d)) :
    ∀ᵐ z, ∀ k N : ℕ, z ∈ Icc (-(k : ℝ)) k → IntegrableOn (fun r => F (r, z)) (Icc (lowEnd N) (highEnd N)) := by
  rw [ae_all_iff]; intro k
  rw [ae_all_iff]; intro N
  have h := hF (lowEnd N) (highEnd N) (-(k : ℝ)) k (lowEnd_pos N)
  rw [IntegrableOn, rect_restrict] at h
  exact (ae_restrict_iff' measurableSet_Icc).1 h.prod_left_ae

theorem ray_slice_weak (F Fr : ℝ × ℝ → ℂ)
    (hF : ∀ a b c d : ℝ, 0 < a → IntegrableOn F (Icc a b ×ˢ Icc c d))
    (hFr : ∀ a b c d : ℝ, 0 < a → IntegrableOn Fr (Icc a b ×ˢ Icc c d))
    (hid : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, ((ψ p : ℝ) : ℂ) * Fr p) :
    ∀ᵐ z, ∀ lo hi : ℝ, 0 < lo → lo < hi →
      HasWeakDerivOn (fun r => F (r, z)) (fun r => Fr (r, z)) lo hi := by
  have hsep : ∀ N : ℕ, ∃ t ⊆ range (rayData (lowEnd N) (highEnd N)), t.Countable ∧
      range (rayData (lowEnd N) (highEnd N)) ⊆ closure t :=
    fun N => (TopologicalSpace.IsSeparable.of_separableSpace _).exists_countable_dense_subset
  choose t hts htc hdense using hsep
  have hpre : ∀ N, ∀ x ∈ t N, ∃ η : rayTests (lowEnd N) (highEnd N), rayData _ _ η = x :=
    fun N x hx => hts N hx
  choose η hη using hpre
  have hzero : ∀ᵐ z, ∀ N : ℕ, ∀ x : t N,
      rayPair (fun r => F (r, z)) (fun r => Fr (r, z)) (band_le N) x = 0 := by
    rw [ae_all_iff]; intro N
    have := (htc N).to_subtype
    rw [ae_all_iff]; intro x
    filter_upwards [ae_ray_zero F Fr hF hFr hid (lowEnd_pos N) (band_le N) (η N x.1 x.2)] with z hz
    rw [← hη N x.1 x.2]
    exact hz
  filter_upwards [hzero, ae_ray_integrable F hF, ae_ray_integrable Fr hFr] with z hz ihF ihFr lo hi hlo hlh
  obtain ⟨k, hk⟩ : ∃ k : ℕ, z ∈ Icc (-(k : ℝ)) k := by
    obtain ⟨k, hk⟩ := exists_nat_ge |z|
    exact ⟨k, abs_le.1 hk⟩
  obtain ⟨N, hN⟩ := exists_nat_ge (max hi (1 / lo))
  have hsub : Ioo lo hi ⊆ Icc (lowEnd N) (highEnd N) := by
    intro r hr
    have h1 : 1 / lo ≤ N := (le_max_right _ _).trans hN
    have h2 : hi ≤ N := (le_max_left _ _).trans hN
    refine ⟨?_, ?_⟩
    · have hle : lowEnd N ≤ lo := by
        unfold lowEnd
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hlo] at h1
        nlinarith
      linarith [hr.1]
    · unfold highEnd
      linarith [hr.2]
  refine ⟨(ihF k N hk).mono_set hsub, (ihFr k N hk).mono_set hsub, fun ψ hψ hc hs => ?_⟩
  have hψN : ψ ∈ rayTests (lowEnd N) (highEnd N) := ⟨hψ, hs.trans hsub⟩
  have hP : rayPair (fun r => F (r, z)) (fun r => Fr (r, z)) (band_le N) (rayData _ _ ⟨ψ, hψN⟩) = 0 := by
    have hcl : closure (t N) ⊆ {x | rayPair (fun r => F (r, z)) (fun r => Fr (r, z)) (band_le N) x = 0} :=
      closure_minimal (fun x hx => hz N ⟨x, hx⟩)
        (isClosed_eq (rayPair_cont _ _ (band_le N) (ihF k N hk) (ihFr k N hk)) continuous_const)
    exact hcl (hdense N (mem_range_self _))
  have hoff : ∀ r, r ∉ Ioo lo hi → ψ r = 0 ∧ deriv ψ r = 0 := fun r hr =>
    ⟨by by_contra h'; exact hr (hs (subset_tsupport _ h')), deriv_of_notMem_tsupport fun h' => hr (hs h')⟩
  have hoff' : ∀ r, r ∉ Icc (lowEnd N) (highEnd N) → ψ r = 0 ∧ deriv ψ r = 0 :=
    fun r hr => hoff r fun h' => hr (hsub h')
  have cd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have i1 : IntegrableOn (fun r => ((deriv ψ r : ℝ) : ℂ) * F (r, z)) (Icc (lowEnd N) (highEnd N)) :=
    (ihF k N hk).continuousOn_mul (Complex.continuous_ofReal.comp cd).continuousOn isCompact_Icc
  have i2 : IntegrableOn (fun r => ((ψ r : ℝ) : ℂ) * Fr (r, z)) (Icc (lowEnd N) (highEnd N)) :=
    (ihFr k N hk).continuousOn_mul (Complex.continuous_ofReal.comp hψ.continuous).continuousOn isCompact_Icc
  have hP' : (∫ r in Icc (lowEnd N) (highEnd N), ((deriv ψ r : ℝ) : ℂ) * F (r, z))
      + ∫ r in Icc (lowEnd N) (highEnd N), ((ψ r : ℝ) : ℂ) * Fr (r, z) = 0 := by
    rw [← integral_add i1 i2, ← hP]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [rayData, ContinuousMap.coe_mk, projIcc_of_mem _ hr]
  have eA : ∫ r in Ioo lo hi, F (r, z) * ((deriv ψ r : ℝ) : ℂ)
      = ∫ r in Icc (lowEnd N) (highEnd N), ((deriv ψ r : ℝ) : ℂ) * F (r, z) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by simp [(hoff r hr).2],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by simp [(hoff' r hr).2]]
    exact integral_congr_ae (Eventually.of_forall fun r => mul_comm _ _)
  have eB : ∫ r in Ioo lo hi, Fr (r, z) * ((ψ r : ℝ) : ℂ)
      = ∫ r in Icc (lowEnd N) (highEnd N), ((ψ r : ℝ) : ℂ) * Fr (r, z) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by simp [(hoff r hr).1],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by simp [(hoff' r hr).1]]
    exact integral_congr_ae (Eventually.of_forall fun r => mul_comm _ _)
  rw [eA, eB]
  exact eq_neg_of_add_eq_zero_left hP'

def planeCol : Fin 3 → Space := ![unitVector 0, unitVector 1, 0]

def turnCol : Fin 3 → Space := ![unitVector 1, -unitVector 0, 0]

def axisCol : Fin 3 → Space := ![0, 0, unitVector 2]

def dirAt (b : Fin 3) (q : ℝ × ℝ) : Space := q.1 • planeCol b + q.2 • turnCol b + axisCol b

theorem dirAt_smooth (b : Fin 3) : ContDiff ℝ ∞ (dirAt b) :=
  ((contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)).add contDiff_const

theorem dirAt_rot (b : Fin 3) (θ : ℝ) : axialRot θ (unitVector b) = dirAt b (Real.cos θ, Real.sin θ) := by
  ext i
  fin_cases b <;> fin_cases i <;> simp [axialRot, dirAt, planeCol, turnCol, axisCol, unitVector]

theorem dirAt_zero (q : ℝ × ℝ) : dirAt 0 q = unitAt q := by
  ext i
  fin_cases i <;> simp [dirAt, planeCol, turnCol, axisCol, unitAt, unitVector]

def columnMap (b : Fin 3) (L : ℝ × ℝ → (Space →L[ℝ] ℝ)) (q : ℝ × ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (L q).comp (ContinuousLinearMap.apply ℝ Space (dirAt b q))

theorem columnMap_smooth (b : Fin 3) {L : ℝ × ℝ → (Space →L[ℝ] ℝ)} (hL : ContDiff ℝ ∞ L) :
    ContDiff ℝ ∞ (columnMap b L) :=
  hL.clm_comp ((ContinuousLinearMap.apply ℝ Space :
    Space →L[ℝ] (Space →L[ℝ] Space) →L[ℝ] Space).contDiff.comp (dirAt_smooth b))

theorem grad_col_rep (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    modeGrad ξ G 0 (planePoint p) (a, b) =
      (1 / (2 * Real.pi) : ℂ) * waveAvg G (columnMap b (frameCoord a)) ξ.1 ξ.2 p :=
  mode_eq ξ _ (a, b) G (columnMap b (frameCoord a)) p fun τ θ => by
    simp only [zero_add, axialRot_planePoint, dirAt_rot, columnMap, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, frameCoord_apply]

theorem second_col_rep (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b : Fin 3)
    (p : ℝ × ℝ) :
    modeSecondDeriv ξ H 0 (planePoint p) (a, 0, b) =
      (1 / (2 * Real.pi) : ℂ) * waveAvg H (radialL (columnMap b (frameCoord a))) ξ.1 ξ.2 p :=
  mode_eq ξ _ (a, 0, b) H (radialL (columnMap b (frameCoord a))) p fun τ θ => by
    simp only [zero_add, axialRot_planePoint, dirAt_zero, dirAt_rot, radialL, columnMap,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, frameCoord_apply]

end Internal.RadialModes

open Bridge Bridge.Internal.HeightOrbit Bridge.Internal.HeightModes Internal.RadialModes in
theorem modeRadialDeriv (hE : Bridge.HessianEnergyIdentityHolds) : ModeRadialDerivHolds := by
  intro Γ P v G H g hp ξ a b
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
  have L1s := frameCoord_smooth a
  have Lbs := columnMap_smooth b L1s
  have L1c := L1s.continuous
  have Lbc := Lbs.continuous
  set c : ℂ := (1 / (2 * Real.pi) : ℂ)
  have iU : ∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeVel ξ v 0 (planePoint p) a) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) := fun _ _ _ _ h0 => by
    simp only [vel_rep]
    exact (waveAvg_integrableOn v lv _ L1c _ _ h0).const_mul c
  have iUr : ∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeGrad ξ G 0 (planePoint p) (a, 0)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) :=
    fun _ _ _ _ h0 => by
      simp only [gradr_rep]
      exact (waveAvg_integrableOn G lG _ (radialL_cont L1c) _ _ h0).const_mul c
  have iGb : ∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeGrad ξ G 0 (planePoint p) (a, b)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) :=
    fun _ _ _ _ h0 => by
      simp only [grad_col_rep]
      exact (waveAvg_integrableOn G lG _ Lbc _ _ h0).const_mul c
  have iWb : ∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeSecondDeriv ξ H 0 (planePoint p) (a, 0, b)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) :=
    fun _ _ _ _ h0 => by
      simp only [second_col_rep]
      exact (waveAvg_integrableOn H lH _ (radialL_cont Lbc) _ _ h0).const_mul c
  have P1 : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVel ξ v 0 (planePoint p) a =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 0) := by
    intro ψ hψ hc hpos
    have h := plane_weak v G lv lG w1 (frameCoord a) L1s ξ.1 ξ.2 ψ hψ hc hpos
    simp only [vel_rep, gradr_rep]
    exact scale_id c h.1
  have P2 : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, b) =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeSecondDeriv ξ H 0 (planePoint p) (a, 0, b) := by
    intro ψ hψ hc hpos
    have h := plane_weak G H lG lH w2 (columnMap b (frameCoord a)) Lbs ξ.1 ξ.2 ψ hψ hc hpos
    simp only [grad_col_rep, second_col_rep]
    exact scale_id c h.1
  have S1 := ray_slice_weak _ _ iU iUr P1
  have S2 := ray_slice_weak _ _ iGb iWb P2
  filter_upwards [S1, S2] with z h1 h2 lo hi hlo hlh
  exact ⟨h1 lo hi hlo hlh, h2 lo hi hlo hlh⟩

end Breakdown.CertCell.SideTrace
