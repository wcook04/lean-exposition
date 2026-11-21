import TorusEuler.TerminalTimeJetNorms

/-! Time Leibniz formulas for the actual hierarchy on the closed slab. -/

open ContinuousLinearMap Finset Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem map_eval (L : E →L[ℝ] F) (f : HierarchyTwistedProfile T k E)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (map L f).val.val.val x = L (f.val.val.val x) := by
  rw [map_val, HierarchyPeriodicProfile.map_val, HierarchySmoothProfile.map_apply _ _ hx]

theorem applyField_eval (A : HierarchyTwistedProfile T k (E →L[ℝ] F))
    (f : HierarchyTwistedProfile T k E)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (applyField A f).val.val.val x = A.val.val.val x (f.val.val.val x) := by
  rw [applyField_val, HierarchyPeriodicProfile.applyField_val, HierarchySmoothProfile.applyField_eval _ _ hx]

theorem directionDerivative_map (hT : 0 < T) (v : HierarchyProfilePoint)
    (L : E →L[ℝ] F) (f : HierarchyTwistedProfile T k E) :
    directionDerivative hT v (map L f) = map L (directionDerivative hT v f) := by
  apply HierarchyTwistedProfile.ext
  intro x hx
  let S := hierarchyProfileSlab T
  have hf := ((HierarchySmoothProfile.smooth f.val.val).differentiableOn (by simp) x hx).hasFDerivWithinAt
  rw [directionDerivative_apply hT v _ hx, map_eval _ _ hx, directionDerivative_apply hT v f hx,
    fderivWithin_congr' (show EqOn (map L f).val.val.val (fun y => L (f.val.val.val y)) S
      from fun _ hy => map_eval L f hy) hx]
  exact congrArg (fun D : HierarchyProfilePoint →L[ℝ] F => D v)
    ((L.hasFDerivAt.comp_hasFDerivWithinAt x hf).fderivWithin (uniqueDiffOn_hierarchyProfileSlab hT x hx))

theorem timeJet_map (hT : 0 < T) (i : ℕ)
    (L : E →L[ℝ] F) (f : HierarchyTwistedProfile T k E) :
    timeJet hT i (map L f) = map L (timeJet hT i f) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [timeJet_succ, timeJet_succ, ih, directionDerivative_map hT (1, 0, 0)]

theorem directionDerivative_applyField (hT : 0 < T) (v : HierarchyProfilePoint)
    (A : HierarchyTwistedProfile T k (E →L[ℝ] F)) (f : HierarchyTwistedProfile T k E) :
    directionDerivative hT v (applyField A f) =
      applyField (directionDerivative hT v A) f + applyField A (directionDerivative hT v f) := by
  apply HierarchyTwistedProfile.ext
  intro x hx
  let S := hierarchyProfileSlab T
  have hA := ((HierarchySmoothProfile.smooth A.val.val).differentiableOn (by simp) x hx).hasFDerivWithinAt
  have hf := ((HierarchySmoothProfile.smooth f.val.val).differentiableOn (by simp) x hx).hasFDerivWithinAt
  rw [directionDerivative_apply hT v _ hx,
    fderivWithin_congr' (show EqOn (applyField A f).val.val.val
      (fun y => A.val.val.val y (f.val.val.val y)) S from fun _ hy => applyField_eval A f hy) hx,
    (hA.clm_apply hf).fderivWithin (uniqueDiffOn_hierarchyProfileSlab hT x hx)]
  change _ = (applyField (directionDerivative hT v A) f).val.val.val x +
    (applyField A (directionDerivative hT v f)).val.val.val x
  simp only [add_apply, ContinuousLinearMap.comp_apply, flip_apply, applyField_eval _ _ hx,
    directionDerivative_apply _ _ _ hx, add_comm]

theorem timeDerivative_applyField (hT : 0 < T)
    (A : HierarchyTwistedProfile T k (E →L[ℝ] F)) (f : HierarchyTwistedProfile T k E) :
    timeDerivative hT (applyField A f) =
      applyField (timeDerivative hT A) f + applyField A (timeDerivative hT f) :=
  directionDerivative_applyField hT (1, 0, 0) A f

/-- The exact binomial Leibniz expansion for time-dependent coefficients. -/
theorem timeJet_applyField (hT : 0 < T) (n : ℕ)
    (A : HierarchyTwistedProfile T k (E →L[ℝ] F)) (f : HierarchyTwistedProfile T k E) :
    timeJet hT n (applyField A f) = ∑ i ∈ range (n + 1),
      n.choose i • applyField (timeJet hT i A) (timeJet hT (n - i) f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [timeJet_succ, ih, map_sum,
      sum_choose_succ_nsmul (fun i j => applyField (timeJet hT i A) (timeJet hT j f)) n]
    simp only [map_nsmul, timeDerivative_applyField, nsmul_add, sum_add_distrib, ← timeJet_succ]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hn : n - i + 1 = n + 1 - i := by
      have := mem_range.mp hi
      omega
    rw [hn]

/-- Apply a fixed continuous bilinear map to two slab profiles. -/
def pointwiseBilinear (B : E →L[ℝ] F →L[ℝ] G) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k F →ₗ[ℝ]
      HierarchyTwistedProfile T k G :=
  applyField.comp (map B)

theorem pointwiseBilinear_eval (B : E →L[ℝ] F →L[ℝ] G)
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (pointwiseBilinear B f g).val.val.val x = B (f.val.val.val x) (g.val.val.val x) := by
  rw [pointwiseBilinear, LinearMap.comp_apply, applyField_eval _ _ hx, map_eval _ _ hx]

theorem timeJet_pointwiseBilinear (hT : 0 < T) (n : ℕ) (B : E →L[ℝ] F →L[ℝ] G)
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F) :
    timeJet hT n (pointwiseBilinear B f g) = ∑ i ∈ range (n + 1),
      n.choose i • pointwiseBilinear B (timeJet hT i f) (timeJet hT (n - i) g) := by
  simp only [pointwiseBilinear, LinearMap.comp_apply, timeJet_applyField, timeJet_map]

theorem terminalSeminorm_sum_le {M ι : Type*} [AddCommGroup M] [Module ℝ M]
    (N : Seminorm ℝ M) (s : Finset ι) (f : ι → M) :
    N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact (map_add_le_add N _ _).trans (add_le_add le_rfl ih)

/-- A Leibniz expansion and the corresponding spatial norm bound give the
same bound in the factorial time norm. -/
theorem timeJetSeminorm_bilinear_le_of_identity
    (hT : 0 < T) (q : ℕ)
    (NE : Seminorm ℝ (HierarchyTwistedProfile T k E))
    (NF : Seminorm ℝ (HierarchyTwistedProfile T k F))
    (NG : Seminorm ℝ (HierarchyTwistedProfile T k G))
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F)
    (v : HierarchyTwistedProfile T k G)
    (B : HierarchyTwistedProfile T k E → HierarchyTwistedProfile T k F →
      HierarchyTwistedProfile T k G)
    {C : ℝ} (hC : 0 ≤ C)
    (hJet : ∀ n ≤ q, timeJet hT n v = ∑ i ∈ range (n + 1),
      n.choose i • B (timeJet hT i f) (timeJet hT (n - i) g))
    (hBound : ∀ n ≤ q, ∀ i ≤ n,
      NG (B (timeJet hT i f) (timeJet hT (n - i) g)) ≤
        C * (NE (timeJet hT i f) * NF (timeJet hT (n - i) g))) :
    timeJetSeminorm hT q NG v ≤ C * (timeJetSeminorm hT q NE f * timeJetSeminorm hT q NF g) := by
  refine timeJetSeminorm_bilinear_le_of_jetwise_le hT q NE NF NG f g _ hC fun n hn => ?_
  rw [hJet n hn]
  refine (terminalSeminorm_sum_le NG _ _).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [← Nat.cast_smul_eq_nsmul ℝ, map_smul_eq_mul, Real.norm_of_nonneg (Nat.cast_nonneg _), mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hBound n hn i (Nat.lt_succ_iff.mp (mem_range.mp hi))) (Nat.cast_nonneg _)

/-- Every fixed spatial bilinear estimate lifts to the factorial time norm
with the original cost. -/
theorem timeJetSeminorm_pointwiseBilinear_le
    (hT : 0 < T) (q : ℕ) (B : E →L[ℝ] F →L[ℝ] G)
    (NE : Seminorm ℝ (HierarchyTwistedProfile T k E))
    (NF : Seminorm ℝ (HierarchyTwistedProfile T k F))
    (NG : Seminorm ℝ (HierarchyTwistedProfile T k G))
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (u : HierarchyTwistedProfile T k E) (v : HierarchyTwistedProfile T k F),
      NG (pointwiseBilinear B u v) ≤ C * (NE u * NF v))
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F) :
    timeJetSeminorm hT q NG (pointwiseBilinear B f g) ≤
      C * (timeJetSeminorm hT q NE f * timeJetSeminorm hT q NF g) :=
  timeJetSeminorm_bilinear_le_of_identity hT q NE NF NG f g _ (fun u v => pointwiseBilinear B u v) hC
    (fun n _ => timeJet_pointwiseBilinear hT n B f g) (fun _ _ _ _ => h _ _)

/-- The time Leibniz bound for a profile of continuous linear maps applied
to a profile. -/
theorem timeJetSeminorm_applyField_le (hT : 0 < T) (q : ℕ)
    (NA : Seminorm ℝ (HierarchyTwistedProfile T k (E →L[ℝ] F)))
    (NE : Seminorm ℝ (HierarchyTwistedProfile T k E))
    (NF : Seminorm ℝ (HierarchyTwistedProfile T k F))
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (A : HierarchyTwistedProfile T k (E →L[ℝ] F)) (f : HierarchyTwistedProfile T k E),
      NF (applyField A f) ≤ C * (NA A * NE f))
    (A : HierarchyTwistedProfile T k (E →L[ℝ] F)) (f : HierarchyTwistedProfile T k E) :
    timeJetSeminorm hT q NF (applyField A f) ≤
      C * (timeJetSeminorm hT q NA A * timeJetSeminorm hT q NE f) :=
  timeJetSeminorm_bilinear_le_of_identity hT q NA NE NF A f _ (fun u v => applyField u v) hC
    (fun n _ => timeJet_applyField hT n A f) (fun _ _ _ _ => h _ _)

/-- The actual Appendix D coefficient bounds, with time multipliers applied
after differentiation, hold with the original spatial cost. -/
theorem timeJetSeminorm_boundedWeight_bilinear_le
    (B : E →L[ℝ] F →L[ℝ] G) (holder : Prop) (ℓ h : ℝ) (n q : ℕ)
    (hT : 0 < T) {S : Set ℝ} (hS : S ⊆ Icc 0 T)
    (τf τg τfg : ℝ → ℝ) {Cf Cg Cfg : ℝ}
    (hf : ∀ t ∈ S, ‖τf t‖ ≤ Cf) (hg : ∀ t ∈ S, ‖τg t‖ ≤ Cg)
    (hfg : ∀ t ∈ S, ‖τfg t‖ ≤ Cfg)
    (hWeight : ∀ t ∈ S, τfg t = τf t * τg t)
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F) :
    let Nf := boundedWeightSeminorm holder ℓ h n hT hS τf hf
    let Ng := boundedWeightSeminorm holder ℓ h n hT hS τg hg
    let Nfg := boundedWeightSeminorm holder ℓ h n hT hS τfg hfg
    timeJetSeminorm hT q Nfg (pointwiseBilinear B f g) ≤
      ((hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n * (2 * ‖B‖)) *
        (timeJetSeminorm hT q Nf f * timeJetSeminorm hT q Ng g) := by
  intro Nf Ng Nfg
  refine timeJetSeminorm_pointwiseBilinear_le hT q B Nf Ng Nfg (by positivity) ?_ f g
  intro u v
  have hBounds := boundedWeightSeminorm_bilinear_le B holder ℓ h n hT hS τf τg τfg
    hf hg hfg hWeight u v (pointwiseBilinear B u v)
    (fun t ht x => pointwiseBilinear_eval B u v ⟨hS ht, mem_univ x⟩)
  simpa only [Nf, Ng, Nfg, mul_assoc] using hBounds

end

end TorusEuler.HierarchyTwistedProfile
