import TorusEuler.LocalizedSeedRegularity
import TorusEuler.OscillatoryDerivativeEstimates
import TorusEuler.TransverseCoframeRegularity
import TorusEuler.ParentCoframeEstimates

/-! Weighted derivatives of the homogeneous seed in the fixed transverse plane. -/

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

section HomogeneousJets

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
private theorem opNorm_le_bound_on_unit_vectors {m : ℕ}
    (F : P [×m]→L[ℝ] E) {B : ℝ} (hB : 0 ≤ B)
    (hunit : ∀ v : Fin m → P, (∀ i, ‖v i‖ ≤ 1) → ‖F v‖ ≤ B) : ‖F‖ ≤ B := by
  refine ContinuousMultilinearMap.opNorm_le_bound hB fun v => ?_
  by_cases hz : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [F.map_coord_zero i hi, norm_zero]
    exact mul_nonneg hB (Finset.prod_nonneg fun j _ => norm_nonneg (v j))
  · let u (i : Fin m) := ‖v i‖⁻¹ • v i
    have hn (i : Fin m) : 0 < ‖v i‖ := norm_pos_iff.mpr fun hi => hz ⟨i, hi⟩
    have hunit' (i : Fin m) : ‖u i‖ = 1 := by
      rw [show u i = ‖v i‖⁻¹ • v i from rfl, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (hn i).le), inv_mul_cancel₀ (hn i).ne']
    have heq : v = fun i => ‖v i‖ • u i := by
      funext i
      rw [show u i = ‖v i‖⁻¹ • v i from rfl, smul_smul, mul_inv_cancel₀ (hn i).ne', one_smul]
    calc
      ‖F v‖ = ‖(∏ i, ‖v i‖) • F u‖ := by
        congr 1
        exact (congrArg F heq).trans (F.map_smul_univ (fun i => ‖v i‖) u)
      _ = (∏ i, ‖v i‖) * ‖F u‖ := by
        rw [norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => norm_nonneg (v j))]
      _ ≤ B * ∏ i, ‖v i‖ := by
        rw [mul_comm B]
        exact mul_le_mul_of_nonneg_left (hunit u fun i => (hunit' i).le)
          (Finset.prod_nonneg fun j _ => norm_nonneg (v j))

omit [FiniteDimensional ℝ P] in
/-- A time slice of a jointly smooth closed-slab family is spatially smooth. -/
theorem contDiff_slice_on_closedSlab {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : ℝ → P → F} {l r t : ℝ}
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc l r ×ˢ (univ : Set P)))
    (ht : t ∈ Icc l r) : ContDiff ℝ ∞ (u t) :=
  contDiffOn_univ.mp (hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun p _ => ⟨ht, mem_univ p⟩))

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
private theorem iteratedFDeriv_apply_fin_cast {m n : ℕ} (h : m = n)
    (f : P → E) (x : P) (v : Fin n → P) :
    iteratedFDeriv ℝ m f x (fun i => v (Fin.cast h i)) =
      iteratedFDeriv ℝ n f x v := by
  subst n
  rfl

set_option maxHeartbeats 900000 in
/-- The weighted homogeneous ODE estimate holds in the full Fréchet operator
norm, by applying the word recurrence to arbitrary unit directions. -/
theorem weighted_homogeneous_jetBounds_Icc (N : ℕ)
    {A : ℝ → P → E →L[ℝ] E} {y : ℝ → P → E} {g dg : ℝ → ℝ}
    {S : Set P} {l r K C B : ℝ} (hlr : l < r)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc l r ×ˢ (univ : Set P)))
    (hy : ContDiffOn ℝ ∞ (Function.uncurry y) (Icc l r ×ˢ (univ : Set P)))
    (hyt : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (fun u => y u p) (A t p (y t p)) (Icc l r) t)
    (hpos : ∀ t ∈ Icc l r, 0 < g t)
    (hg : ∀ t ∈ Icc l r, HasDerivWithinAt g (dg t) (Icc l r) t)
    (hdg : ContinuousOn dg (Icc l r))
    (hStable : ∀ p ∈ S, ∀ z : ℝ → E,
      (∀ t ∈ Icc l r, HasDerivWithinAt z (A t p (z t)) (Icc l r) t) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖z v‖ / g v ≤ K * (‖z u‖ / g u))
    (hinit : ∀ m ≤ N, ∀ p ∈ S, ‖iteratedFDeriv ℝ m (y l) p‖ / g l ≤ B)
    (hcoeff : ∀ m ≤ N, 0 < m → ∀ p ∈ S, ∀ t ∈ Icc l r, ‖iteratedFDeriv ℝ m (A t) p‖ ≤ C) :
    ∀ m ≤ N, ∀ p ∈ S, ∀ t ∈ Icc l r,
      ‖iteratedFDeriv ℝ m (y t) p‖ ≤
        linearODEWordFactor (K * (r - l) * C) N * (K * B) * g t := by
  let d (v : {v : P // ‖v‖ ≤ 1}) := v.val
  have hl : l ∈ Icc l r := left_mem_Icc.mpr hlr.le
  have hword {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : P → F} (hf : ContDiff ℝ ∞ f) (w : List {v : P // ‖v‖ ≤ 1}) (p : P) :
      ‖phaseOperatorWord (fun i _ => d i) w f p‖ ≤ ‖iteratedFDeriv ℝ w.length f p‖ := by
    rw [phaseOperatorWord_eq_jet d hf]
    refine ((iteratedFDeriv ℝ w.length f p).le_opNorm _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one
      (fun i _ => norm_nonneg (d (w.get i))) (fun i _ => (w.get i).property))
  have h := linearODE_wordBounds_Icc d N (A := A) (f := fun _ _ => 0) (x := y) (S := S)
    (H := 0) hlr hK hC hB le_rfl hA contDiffOn_const hy
    (fun p t ht => by simpa only [add_zero] using hyt p t ht) hpos hg hdg hStable
    (fun w hw p hp => (div_le_div_of_nonneg_right (hword (contDiff_slice_on_closedSlab hy hl) w p)
      (hpos l hl).le).trans (hinit w.length hw p hp)) ?_ ?_
  · intro m hm p hp t ht
    let L := linearODEWordFactor (K * (r - l) * C) N * (K * B)
    have hL : 0 ≤ L := mul_nonneg
      (linearODEWordFactor_nonneg (by positivity) N) (mul_nonneg hK hB)
    refine opNorm_le_bound_on_unit_vectors _ (mul_nonneg hL (hpos t ht).le) fun v hv => ?_
    let w := List.ofFn (fun i => (⟨v i, hv i⟩ : {v : P // ‖v‖ ≤ 1}))
    have hw : w.length ≤ N := by simpa only [w, List.length_ofFn] using hm
    have hwt := h w hw p hp t ht
    have hval : phaseOperatorWord (fun i _ => d i) w (y t) p =
        iteratedFDeriv ℝ m (y t) p v := by
      rw [phaseOperatorWord_eq_jet d (contDiff_slice_on_closedSlab hy ht)]
      simp only [w, List.get_ofFn, d]
      exact iteratedFDeriv_apply_fin_cast _ _ _ _
    rw [hval] at hwt
    apply (div_le_iff₀ (hpos t ht)).mp
    simpa only [mul_zero, add_zero] using hwt
  · intro w _ p _ t _
    simp [phaseOperatorWord_eq_jet d (contDiff_const (c := (0 : E)))]
  · intro w hw hne p hp t ht
    exact (hword (contDiff_slice_on_closedSlab hA ht) w p).trans
      (hcoeff w.length hw (List.length_pos_iff.mpr hne) p hp t ht)

end HomogeneousJets

/-- The weighted center estimate applies on every subinterval. A solution on
the subinterval is extended by the original linear evolution and uniqueness. -/
theorem weighted_stability_restrict_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} {g : ℝ → ℝ} {l r K a : ℝ}
    (hA : ContinuousOn A (Icc l r)) (ha : a ∈ Icc l r)
    (hStable : ∀ z : ℝ → E,
      (∀ t ∈ Icc l r, HasDerivWithinAt z (A t (z t)) (Icc l r) t) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖z v‖ / g v ≤ K * (‖z u‖ / g u))
    (z : ℝ → E)
    (hz : ∀ t ∈ Icc a r, HasDerivWithinAt z (A t (z t)) (Icc a r) t)
    {u v : ℝ} (hu : u ∈ Icc a r) (hv : v ∈ Icc u r) :
    ‖z v‖ / g v ≤ K * (‖z u‖ / g u) := by
  have hsub : Icc a r ⊆ Icc l r := Icc_subset_Icc_left ha.1
  obtain ⟨Z, hZ₀, hZ⟩ := linearODE_exists_Icc_of_mem ha hA (z a)
  have hEq : EqOn Z z (Icc a r) :=
    linearODE_unique_of_mem ordConnected_Icc (left_mem_Icc.mpr ha.2) (hA.mono hsub)
      (fun t ht => (hZ t (hsub ht)).mono hsub) hz hZ₀
  have hv' : v ∈ Icc a r := ⟨hu.1.trans hv.1, hv.2⟩
  rw [← hEq hu, ← hEq hv']
  exact hStable Z hZ u (hsub hu) v hv

/-- A uniform coefficient comparison with the center gives stability at a
label for every pair of ordered times on the slab. -/
theorem weighted_near_label_stability_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A A₁ : ℝ → E →L[ℝ] E} {g dg : ℝ → ℝ} {l r K : ℝ}
    (hK : 0 < K) (hT : r - l ≤ 1)
    (hA : ContinuousOn A (Icc l r)) (hA₁ : ContinuousOn A₁ (Icc l r))
    (hchange : ∀ t ∈ Icc l r, ‖A₁ t - A t‖ ≤ K⁻¹)
    (hpos : ∀ t ∈ Icc l r, 0 < g t)
    (hg : ∀ t ∈ Icc l r, HasDerivWithinAt g (dg t) (Icc l r) t)
    (hdg : ContinuousOn dg (Icc l r))
    (hStable : ∀ z : ℝ → E,
      (∀ t ∈ Icc l r, HasDerivWithinAt z (A t (z t)) (Icc l r) t) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖z v‖ / g v ≤ K * (‖z u‖ / g u))
    (x : ℝ → E)
    (hx : ∀ t ∈ Icc l r, HasDerivWithinAt x (A₁ t (x t)) (Icc l r) t)
    {u v : ℝ} (hu : u ∈ Icc l r) (hv : v ∈ Icc u r) :
    ‖x v‖ / g v ≤ (Real.exp 1 * K) * (‖x u‖ / g u) := by
  have hsub : Icc u r ⊆ Icc l r := Icc_subset_Icc_left hu.1
  exact (weighted_near_label_forward (x := x) hK (by linarith [hu.1]) (hA.mono hsub)
    (hA₁.mono hsub) (fun t ht => hchange t (hsub ht)) (fun t ht => hpos t (hsub ht))
    (fun t ht => (hg t (hsub ht)).mono hsub) (hdg.mono hsub)
    (fun z hz _ hs _ hvs => weighted_stability_restrict_Icc hA hu hStable z hz hs hvs)
    (fun t ht => (hx t (hsub ht)).mono hsub) hv)

namespace LocalizedAmplitude

local notation "Coeff" => Vec3 →L[ℝ] Vec3

/-- The actual selected seed, expressed in the fixed launch plane, solves
the homogeneous fixed-coordinate equation. Its initial value is the reader
applied to the center seed, since the reader already projects. -/
theorem SeedOn.fixedCoframeAmplitude_equation
    {F G M : ℝ → Vec3 → Coeff} {k : Vec3} {center : ℝ → Vec3}
    {l r ℓ D C : ℝ} (w : SeedOn M (fun t a => (G t a).adjoint k) center l r ℓ D C)
    (hlr : l ≤ r)
    (hκ : ∀ a t, t ∈ Icc l r → (G t a).adjoint k ≠ 0)
    (hF : ∀ a t, t ∈ Icc l r →
      HasDerivWithinAt (fun u => F u a) ((M t a).comp (F t a)) (Icc l r) t)
    (hG : ∀ a, ContinuousOn (fun t => G t a) (Icc l r))
    (hM : ∀ a, ContinuousOn (fun t => M t a) (Icc l r))
    (hInv : ∀ a t, t ∈ Icc l r →
      (G t a).comp (F t a) = .id ℝ Vec3 ∧ (F t a).comp (G t a) = .id ℝ Vec3) :
    let J (t : ℝ) (a : Vec3) := coframeLift k (F t a)
    let R (t : ℝ) (a : Vec3) := coframePullback k (G t a)
    let A (t : ℝ) (a : Vec3) := fixedTransverseGenerator (M t a) (J t a) (R t a)
    let y (t : ℝ) (a : Vec3) := R t a (w.amplitude t a)
    (∀ a, y l a = R l a (center l)) ∧
    ∀ a t, t ∈ Icc l r → J t a (y t a) = w.amplitude t a ∧
      HasDerivWithinAt (fun u => y u a) (A t a (y t a)) (Icc l r) t := by
  dsimp only
  let I := Icc l r
  let J (t : ℝ) (a : Vec3) := coframeLift k (F t a)
  let R (t : ℝ) (a : Vec3) := coframePullback k (G t a)
  let κ (t : ℝ) (a : Vec3) := (G t a).adjoint k
  let A (t : ℝ) (a : Vec3) := fixedTransverseGenerator (M t a) (J t a) (R t a)
  let y (t : ℝ) (a : Vec3) := R t a (w.amplitude t a)
  have hl : l ∈ I := left_mem_Icc.mpr hlr
  have hId (a : Vec3) (t : ℝ) (ht : t ∈ I) :
      (R t a).comp (J t a) = .id ℝ (transversePlane k) ∧
      (J t a).comp (R t a) = oscillatoryTransverseProjection (κ t a) :=
    coframe_identities k (hInv a t ht).1 (hInv a t ht).2
  have hInit (a : Vec3) : y l a = R l a (center l) := by
    change R l a (w.amplitude l a) = _
    rw [w.activation]
    exact fixedTransverse_read_projection (hId a l hl).1 (hId a l hl).2 _
  refine ⟨hInit, fun a t ht => ?_⟩
  have hJ (u : ℝ) (hu : u ∈ I) :
      HasDerivWithinAt (fun v => J v a) ((M u a).comp (J u a)) I u :=
    coframeLift_hasDerivWithinAt k (F := fun v => F v a) (M := fun v => M v a) (hF a u hu)
  have hR : ContinuousOn (fun u => R u a) I :=
    coframePullback_continuousOn k (hG a) (fun u hu => hκ a u hu)
  have hAc : ContinuousOn (fun u => A u a) I :=
    continuousOn_fixedTransverseGenerator (hM a) (HasDerivWithinAt.continuousOn hJ) hR
  obtain ⟨z, hz₀, hz⟩ := linearODE_exists_Icc_of_mem hl hAc (R l a (center l))
  have hLift (u : ℝ) (hu : u ∈ I) :
      HasDerivWithinAt (fun v => J v a (z v))
        (affineWaveAmplitudeOperator (M u a) (κ u a) (J u a (z u))) I u :=
    hasDerivWithinAt_fixedTransverse_lift (hId a u hu).2 (hJ u hu) (hz u hu)
  have hκc : ContinuousOn (fun u => κ u a) I :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).continuous.comp_continuousOn
      (hG a)).clm_apply continuousOn_const
  have hPhys : ContinuousOn (fun u => affineWaveAmplitudeOperator (M u a) (κ u a)) I :=
    continuousOn_affineWaveAmplitudeOperator (hM a) hκc (fun u hu => hκ a u hu)
  have heq : EqOn (fun u => J u a (z u)) (fun u => w.amplitude u a) I := by
    apply linearODE_unique_of_mem ordConnected_Icc hl hPhys hLift (w.equation a)
    rw [hz₀, ← comp_apply, (hId a l hl).2, w.activation]
  have hread (u : ℝ) (hu : u ∈ I) : y u a = z u := by
    dsimp only [y]
    have hVal : J u a (z u) = w.amplitude u a := heq hu
    rw [← hVal, ← comp_apply, (hId a u hu).1, id_apply]
  change J t a (y t a) = w.amplitude t a ∧
    HasDerivWithinAt (fun u => y u a) (A t a (y t a)) I t
  refine ⟨by rw [hread t ht]; exact heq ht, ?_⟩
  rw [hread t ht]
  exact (hz t ht).congr_of_mem hread ht

end LocalizedAmplitude

theorem phaseJetBound_bilinear_product
    {P E F H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : E →L[ℝ] F →L[ℝ] H) (hL : ‖L‖ ≤ 1)
    {f : P → E} {g : P → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : PhaseJetBound N A f) (hG : PhaseJetBound N B g) :
    PhaseJetBound N ((2 : ℝ) ^ N * (A * B)) (fun a => L (f a) (g a)) := by
  intro m hm a
  have h := norm_iteratedFDeriv_bilinear_scaled_le (D := 1) (p := 0) (q := 0) (r := 0)
    L hL (hf.of_le (by simp)) (hg.of_le (by simp)) a
    (fun j hj => by simpa only [one_pow, mul_one] using hF j (hj.trans hm) a)
    (fun j hj => by simpa only [one_pow, mul_one] using hG j (hj.trans hm) a)
  simp only [one_pow, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hm) (mul_nonneg hA hB))


private theorem phaseJetBound_clm_application
    {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : P → E →L[ℝ] F} {g : P → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : PhaseJetBound N A f) (hG : PhaseJetBound N B g) :
    PhaseJetBound N ((2 : ℝ) ^ N * (A * B)) (fun a => f a (g a)) := by
  let L : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F := (ContinuousLinearMap.apply ℝ F).flip
  have hL : ‖L‖ ≤ 1 := by
    simp only [L, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  exact phaseJetBound_bilinear_product L hL hf hg hA hB hF hG

namespace LocalizedAmplitude

local notation "Coeff" => Vec3 →L[ℝ] Vec3

set_option maxHeartbeats 1300000 in
/-- Localized homogeneous seed estimates in normalized spatial coordinates.
The ODE estimate is used only on the support of the envelope. Initial data
are the projected center amplitude, including every derivative of the envelope. -/
theorem SeedOn.envelopedAmplitude_scaledJetBound
    {F G M : ℝ → Vec3 → Coeff} {k : Vec3} {center : ℝ → Vec3} {dg : ℝ → ℝ}
    {l r ℓ D C K CA CJ CR CE : ℝ} (w : SeedOn M (fun t a => (G t a).adjoint k) center l r ℓ D C)
    (N : ℕ) (hlr : l < r) (hT : r - l ≤ 1) (hℓ : 0 < ℓ)
    (hK : 0 < K) (hCA : 0 ≤ CA) (hCJ : 0 ≤ CJ) (hCR : 0 ≤ CR) (hCE : 0 ≤ CE)
    (hκ : ∀ a t, t ∈ Icc l r → (G t a).adjoint k ≠ 0)
    (hF : ∀ a t, t ∈ Icc l r →
      HasDerivWithinAt (fun u => F u a) ((M t a).comp (F t a)) (Icc l r) t)
    (hInv : ∀ a t, t ∈ Icc l r →
      (G t a).comp (F t a) = .id ℝ Vec3 ∧ (F t a).comp (G t a) = .id ℝ Vec3)
    (hFs : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc l r ×ˢ (univ : Set Vec3)))
    (hGs : ContDiffOn ℝ ∞ (Function.uncurry G) (Icc l r ×ˢ (univ : Set Vec3)))
    (hMs : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc l r ×ˢ (univ : Set Vec3)))
    (hws : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc l r ×ˢ (univ : Set Vec3)))
    (hCpos : ∀ t ∈ Icc l r, 0 < ‖center t‖)
    (hCder : ∀ t ∈ Icc l r, HasDerivWithinAt (fun u => ‖center u‖) (dg t) (Icc l r) t)
    (hdg : ContinuousOn dg (Icc l r)) :
    let J (t : ℝ) (a : Vec3) := coframeLift k (F t (ℓ • a))
    let R (t : ℝ) (a : Vec3) := coframePullback k (G t (ℓ • a))
    let A (t : ℝ) (a : Vec3) := fixedTransverseGenerator (M t (ℓ • a)) (J t a) (R t a)
    let S : Set Vec3 := {a | ‖a‖ ≤ 2}
    let e (a : Vec3) := radialEnvelope ℓ (ℓ • a)
    (∀ t ∈ Icc l r, PhaseJetBound N CJ (J t)) →
    PhaseJetBound N CR (R l) →
    PhaseJetBound N CE e →
    (∀ m ≤ N, 0 < m → ∀ a ∈ S, ∀ t ∈ Icc l r, ‖iteratedFDeriv ℝ m (A t) a‖ ≤ CA) →
    (∀ a ∈ S, ∀ t ∈ Icc l r, ‖A t a - A t 0‖ ≤ K⁻¹) →
    (∀ y : ℝ → transversePlane k,
      (∀ t ∈ Icc l r, HasDerivWithinAt y (A t 0 (y t)) (Icc l r) t) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / ‖center v‖ ≤ K * (‖y u‖ / ‖center u‖)) →
    ∀ t ∈ Icc l r, PhaseJetBound N
      ((2 : ℝ) ^ N * (CJ * (linearODEWordFactor ((Real.exp 1 * K) * (r - l) * CA) N *
        ((Real.exp 1 * K) * ((2 : ℝ) ^ N * (CE * CR))))) * ‖center t‖)
      (fun a => e a • w.amplitude t (ℓ • a)) := by
  intro J R A S e hJjet hRjet hejet hAjet hNear hStable
  let I := Icc l r
  let f (t : ℝ) (a : Vec3) := e a • R t a (w.amplitude t (ℓ • a))
  let scale (p : ℝ × Vec3) := (p.1, ℓ • p.2)
  let B := (2 : ℝ) ^ N * (CE * CR)
  let K' := Real.exp 1 * K
  let L := linearODEWordFactor (K' * (r - l) * CA) N * (K' * B)
  have hl : l ∈ I := left_mem_Icc.mpr hlr.le
  have hScale : ContDiff ℝ ∞ scale := contDiff_fst.prodMk (contDiff_snd.const_smul ℓ)
  have hmaps : MapsTo scale (I ×ˢ (univ : Set Vec3)) (I ×ˢ (univ : Set Vec3)) :=
    fun p hp => ⟨hp.1, mem_univ _⟩
  have hEs : ContDiff ℝ ∞ e :=
    (contDiff_radialEnvelope hℓ).comp (contDiff_id.const_smul ℓ)
  have hJs : ContDiffOn ℝ ∞ (Function.uncurry J) (I ×ˢ (univ : Set Vec3)) :=
    contDiffOn_coframeLift k (hFs.comp hScale.contDiffOn hmaps)
  have hRs : ContDiffOn ℝ ∞ (Function.uncurry R) (I ×ˢ (univ : Set Vec3)) :=
    contDiffOn_coframePullback k (hGs.comp hScale.contDiffOn hmaps)
      (fun p hp => hκ (ℓ • p.2) p.1 hp.1)
  have hAs : ContDiffOn ℝ ∞ (Function.uncurry A) (I ×ˢ (univ : Set Vec3)) :=
    (contDiffOn_const (c := (-2 : ℝ))).smul
      (hRs.clm_comp ((hMs.comp hScale.contDiffOn hmaps).clm_comp hJs))
  have hws' : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 => w.amplitude p.1 (ℓ • p.2))
      (I ×ˢ (univ : Set Vec3)) := hws.comp hScale.contDiffOn hmaps
  have hfs : ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ (univ : Set Vec3)) :=
    ((hEs.comp contDiff_snd).contDiffOn).smul (hRs.clm_apply hws')
  have htime {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℝ → Vec3 → E}
      (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (I ×ˢ (univ : Set Vec3))) (a : Vec3) :
      ContinuousOn (fun t => u t a) I :=
    hu.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht => ⟨ht, mem_univ a⟩)
  obtain ⟨hInit, hEq⟩ := w.fixedCoframeAmplitude_equation hlr.le hκ hF
    (htime hGs) (htime hMs) hInv
  have hFt (a : Vec3) (t : ℝ) (ht : t ∈ I) :
      HasDerivWithinAt (fun u => f u a) (A t a (f t a)) I t := by
    have h := ((hEq (ℓ • a) t ht).2).const_smul (e a)
    rw [map_smul]
    exact h
  have hInit' : f l = fun a => e a • R l a (center l) := by
    funext a
    exact congrArg (e a • ·) (hInit (ℓ • a))
  have hRsl := contDiff_slice_on_closedSlab hRs hl
  have hInitR : PhaseJetBound N (‖center l‖ * CR) (fun a => R l a (center l)) := by
    intro m hm a
    exact (norm_iteratedFDeriv_clm_apply_const (c := center l) hRsl.contDiffAt (by simp) (x := a)).trans
      (mul_le_mul_of_nonneg_left (hRjet m hm a) (norm_nonneg _))
  have hB : 0 ≤ B := mul_nonneg (by positivity) (mul_nonneg hCE hCR)
  have hK' : 0 ≤ K' := mul_nonneg (Real.exp_nonneg _) hK.le
  have hL : 0 ≤ L :=
    mul_nonneg (linearODEWordFactor_nonneg (by positivity) N) (mul_nonneg hK' hB)
  have hInitJet : PhaseJetBound N (B * ‖center l‖) (f l) := by
    have h := phaseJetBound_bilinear_product (lsmul ℝ ℝ) opNorm_lsmul_le hEs
      (hRsl.clm_apply contDiff_const) hCE (mul_nonneg (norm_nonneg _) hCR) hejet hInitR
    rw [hInit', show B * ‖center l‖ = (2 : ℝ) ^ N * (CE * (‖center l‖ * CR)) by dsimp only [B]; ring]
    exact h
  have hStable' (a : Vec3) (ha : a ∈ S) (y : ℝ → transversePlane k) (hy : ∀ t ∈ I,
      HasDerivWithinAt y (A t a (y t)) I t) (u : ℝ) (hu : u ∈ I) (v : ℝ) (hv : v ∈ Icc u r) :
      ‖y v‖ / ‖center v‖ ≤ K' * (‖y u‖ / ‖center u‖) :=
    weighted_near_label_stability_Icc hK hT (htime hAs 0) (htime hAs a)
      (hNear a ha) hCpos hCder hdg hStable y hy hu hv
  have hjet := weighted_homogeneous_jetBounds_Icc N hlr hK' hCA hB hAs hfs hFt
    hCpos hCder hdg hStable'
    (fun m hm a _ => (div_le_iff₀ (hCpos l hl)).2 (hInitJet m hm a)) hAjet
  intro t ht
  have hfjet : PhaseJetBound N (L * ‖center t‖) (f t) := by
    intro m hm a
    by_cases ha : a ∈ S
    · exact hjet m hm a ha t ht
    · have hS : IsClosed S := isClosed_le continuous_norm continuous_const
      have heq : f t =ᶠ[𝓝 a] (0 : Vec3 → transversePlane k) := by
        filter_upwards [hS.isOpen_compl.mem_nhds ha] with b hb
        have hb' : 2 ≤ ‖b‖ := le_of_not_ge hb
        have hz : e b = 0 := radialEnvelope_eq_zero hℓ (by
          rw [norm_smul, Real.norm_of_nonneg hℓ.le, mul_comm 2 ℓ]
          exact mul_le_mul_of_nonneg_left hb' hℓ.le)
        simp [f, hz]
      rw [(heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
      simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg hL (norm_nonneg _)
  have hOut (a : Vec3) : J t a (f t a) = e a • w.amplitude t (ℓ • a) := by
    change J t a (e a • R t a (w.amplitude t (ℓ • a))) = _
    rw [map_smul, (hEq (ℓ • a) t ht).1]
  have hJet := phaseJetBound_clm_application (contDiff_slice_on_closedSlab hJs ht)
    (contDiff_slice_on_closedSlab hfs ht) hCJ (mul_nonneg hL (norm_nonneg _))
    (hJjet t ht) hfjet
  have hv : (fun a => J t a (f t a)) = fun a => e a • w.amplitude t (ℓ • a) := funext hOut
  rw [hv] at hJet
  intro m hm a
  refine (hJet m hm a).trans_eq ?_
  dsimp only [L, K', B]
  ring

end LocalizedAmplitude

section Radius

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Scaling the label multiplies the Fréchet jet by one radius factor for
each derivative. -/
theorem norm_iteratedFDeriv_scaledLabel_le {f : E → F} (hf : ContDiff ℝ ∞ f)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (n : ℕ) (a : E) :
    ‖iteratedFDeriv ℝ n (fun y => f (ℓ • y)) a‖ ≤
      ℓ ^ n * ‖iteratedFDeriv ℝ n f (ℓ • a)‖ := by
  let L : E →L[ℝ] E := ℓ • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ ℓ := by
    rw [show L = ℓ • ContinuousLinearMap.id ℝ E from rfl, norm_smul, Real.norm_of_nonneg hℓ]
    exact mul_le_of_le_one_right hℓ ContinuousLinearMap.norm_id_le
  change ‖iteratedFDeriv ℝ n (f ∘ L) a‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf a (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (L a)‖ * ‖L‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n f (L a)).norm_compContinuousLinearMap_le (fun _ => L)
    _ ≤ _ := by
      rw [mul_comm (ℓ ^ n)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL n) (norm_nonneg _)

/-- Under the radius restriction, coefficient jets have a uniform scaled
bound. Every positive-order jet retains one factor of the radius. -/
theorem norm_iteratedFDeriv_scaledLabel_power_le {f : E → F} (hf : ContDiff ℝ ∞ f)
    {D ℓ C : ℝ} {p q : ℕ} (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ)
    (hscale : ℓ * D ^ p ≤ 1) (hC : 0 ≤ C) (n : ℕ) (a : E)
    (hjet : ‖iteratedFDeriv ℝ n f (ℓ • a)‖ ≤ C * D ^ (p * n + q)) :
    ‖iteratedFDeriv ℝ n (fun y => f (ℓ • y)) a‖ ≤ C * D ^ q ∧
    (0 < n → ‖iteratedFDeriv ℝ n (fun y => f (ℓ • y)) a‖ ≤ C * ℓ * D ^ (p + q)) := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hbase : 0 ≤ ℓ * D ^ p := mul_nonneg hℓ (pow_nonneg hD₀ _)
  have hA : 0 ≤ C * D ^ q := mul_nonneg hC (pow_nonneg hD₀ _)
  have h : ‖iteratedFDeriv ℝ n (fun y => f (ℓ • y)) a‖ ≤ (ℓ * D ^ p) ^ n * (C * D ^ q) := by
    calc
      _ ≤ ℓ ^ n * (C * D ^ (p * n + q)) :=
        (norm_iteratedFDeriv_scaledLabel_le hf hℓ n a).trans
          (mul_le_mul_of_nonneg_left hjet (pow_nonneg hℓ _))
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
  refine ⟨h.trans (mul_le_of_le_one_left hA (pow_le_one₀ hbase hscale)), fun hn => h.trans ?_⟩
  calc
    _ ≤ (ℓ * D ^ p) * (C * D ^ q) :=
      mul_le_mul_of_nonneg_right (by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
        rw [pow_succ]
        exact mul_le_of_le_one_left hbase (pow_le_one₀ hbase hscale)) hA
    _ = _ := by rw [pow_add]; ring

private theorem phaseJetBound_const_smul {f : E → F} (hf : ContDiff ℝ ∞ f)
    {B c : ℝ} {n : ℕ} (hjet : PhaseJetBound n B f) :
    PhaseJetBound n (‖c‖ * B) (fun x => c • f x) := by
  intro j hj a
  change ‖iteratedFDeriv ℝ j (c • f) a‖ ≤ ‖c‖ * B
  rw [iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by simp)), norm_smul]
  exact mul_le_mul_of_nonneg_left (hjet j hj a) (norm_nonneg _)

private theorem phaseJetBound_comp_contraction {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (L : P →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    {B : ℝ} {n : ℕ} (hjet : PhaseJetBound n B f) :
    PhaseJetBound n B (f ∘ L) := by
  intro j hj a
  rw [L.iteratedFDeriv_comp_right hf a (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L a)‖ * ‖L‖ ^ j := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ j f (L a)).norm_compContinuousLinearMap_le (fun _ => L)
    _ ≤ _ := (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)).trans
      (hjet j hj (L a))

theorem phaseJetBound_comp_left_contraction {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P → E} (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {B : ℝ} {n : ℕ} (hjet : PhaseJetBound n B f) :
    PhaseJetBound n B (L ∘ f) := by
  intro j hj a
  exact (L.norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (hjet j hj a))

end Radius

namespace LocalizedAmplitude

local notation "End3" => Vec3 →L[ℝ] Vec3

section Regularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed transverse coframe and its evolution operator are jointly
smooth whenever the input coefficients are smooth and the covector stays nonzero. -/
theorem contDiff_transverseCoframeFields (k : Vec3) {F G M : E → End3} {N : ℕ∞ω}
    (hF : ContDiff ℝ N F) (hG : ContDiff ℝ N G) (hM : ContDiff ℝ N M)
    (hκ : ∀ b, (G b).adjoint k ≠ 0) :
    let J (b : E) := coframeLift k (F b)
    let R (b : E) := coframePullback k (G b)
    let A (b : E) := fixedTransverseGenerator (M b) (J b) (R b)
    ContDiff ℝ N J ∧ ContDiff ℝ N R ∧ ContDiff ℝ N A := by
  let J (b : E) := coframeLift k (F b)
  let R (b : E) := coframePullback k (G b)
  have hJ : ContDiff ℝ N J :=
    contDiffOn_univ.mp (contDiffOn_coframeLift k hF.contDiffOn)
  have hR : ContDiff ℝ N R :=
    contDiffOn_univ.mp (contDiffOn_coframePullback k hG.contDiffOn fun b _ => hκ b)
  exact ⟨hJ, hR, (hR.clm_comp (hM.clm_comp hJ)).const_smul (-2 : ℝ)⟩

private theorem contDiff_coframeLongitudinal (k : Vec3) {G : E → End3} {N : ℕ∞ω}
    (hG : ContDiff ℝ N G) (hκ : ∀ b, (G b).adjoint k ≠ 0) :
    ContDiff ℝ N (fun b =>
      (‖(G b).adjoint k‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ ((G b).adjoint k) ((G b).adjoint k)) := by
  let κ (b : E) := (G b).adjoint k
  let adj : End3 ≃ₗᵢ[ℝ] End3 := ContinuousLinearMap.adjoint
  have hκc : ContDiff ℝ N κ := (adj.contDiff.comp hG).clm_apply contDiff_const
  let L : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
  have hInner : ContDiff ℝ N (fun b => L (κ b)) := L.contDiff.comp hκc
  have hRank : ContDiff ℝ N (fun b => InnerProductSpace.rankOne ℝ (κ b) (κ b)) :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Vec3) (F := Vec3)).contDiff.comp
      (hInner.prodMk hκc)
  exact ((hκc.norm_sq ℝ).inv fun b => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκ b))).smul hRank

end Regularity

private theorem norm_iteratedFDeriv_clm_comp_scaled_through_le
    {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : P → F →L[ℝ] G} {g : P → E →L[ℝ] F}
    {n p q r : ℕ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (x : P)
    {D C₁ C₂ : ℝ} (hD : 0 ≤ D) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C₁ * D ^ (p * i + q))
    (h₂ : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ C₂ * D ^ (p * i + r)) :
    ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun b => (f b).comp (g b)) x‖ ≤
      (2 : ℝ) ^ n * (C₁ * C₂) * D ^ (p * i + q + r) := by
  intro i hi
  have h := norm_iteratedFDeriv_bilinear_scaled_le (compL ℝ E F G) (norm_compL_le ℝ E F G)
    (hf.of_le (by exact_mod_cast hi)) (hg.of_le (by exact_mod_cast hi)) x
    (fun j hj => h₁ j (hj.trans hi)) (fun j hj => h₂ j (hj.trans hi))
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) (mul_nonneg hC₁ hC₂))
    (pow_nonneg hD _))

set_option maxHeartbeats 1200000 in
/-- The physical coframe fields and the fixed transverse generator inherit
a common slope in derivative order from the parent coefficient jets. -/
theorem norm_iteratedFDeriv_transverseCoframeFields_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : Vec3)
    {F G M : E → End3} {n : ℕ}
    (hF : ContDiff ℝ n F) (hG : ContDiff ℝ n G) (hM : ContDiff ℝ n M)
    (hκ : ∀ b, (G b).adjoint k ≠ 0) (a : E) {D C : ℝ} (hD : 1 ≤ D) (hC : 0 ≤ C)
    (hFj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i F a‖ ≤ C * D ^ (5 * i + 1))
    (hGj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i G a‖ ≤ C * D ^ (7 * i + 1))
    (hMj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i M a‖ ≤ C * D ^ (6 * i + 1))
    (hPj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun b =>
      (‖(G b).adjoint k‖ ^ 2)⁻¹ •
        InnerProductSpace.rankOne ℝ ((G b).adjoint k) ((G b).adjoint k)) a‖ ≤
      C * D ^ (16 * i + 8)) :
    let J (b : E) := coframeLift k (F b)
    let R (b : E) := coframePullback k (G b)
    let A (b : E) := fixedTransverseGenerator (M b) (J b) (R b)
    let B : ℝ := 2 ^ n
    let C_R := B * (C * (1 + C))
    let C_MJ := B * (C * C)
    ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i J a‖ ≤ C * D ^ (16 * i + 1) ∧
      ‖iteratedFDeriv ℝ i R a‖ ≤ C_R * D ^ (16 * i + 9) ∧
      ‖iteratedFDeriv ℝ i A a‖ ≤ (2 * (B * (C_R * C_MJ))) * D ^ (16 * i + 11) := by
  let J (b : E) := coframeLift k (F b)
  let R (b : E) := coframePullback k (G b)
  let A (b : E) := fixedTransverseGenerator (M b) (J b) (R b)
  let P (b : E) : End3 := (‖(G b).adjoint k‖ ^ 2)⁻¹ •
    InnerProductSpace.rankOne ℝ ((G b).adjoint k) ((G b).adjoint k)
  let Q (b : E) := oscillatoryTransverseProjection ((G b).adjoint k)
  let B : ℝ := 2 ^ n
  let C_R := B * (C * (1 + C))
  let C_MJ := B * (C * C)
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hB₀ : 0 ≤ B := by dsimp [B]; positivity
  have hCR : 0 ≤ C_R := mul_nonneg hB₀ (mul_nonneg hC (by positivity))
  have hCMJ : 0 ≤ C_MJ := mul_nonneg hB₀ (mul_nonneg hC hC)
  obtain ⟨hJ, hR, _⟩ := contDiff_transverseCoframeFields k hF hG hM hκ
  have hP : ContDiff ℝ n P := contDiff_coframeLongitudinal k hG hκ
  have hQ : ContDiff ℝ n Q :=
    (contDiff_const (c := ContinuousLinearMap.id ℝ Vec3)).sub hP
  have hF16 (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i F a‖ ≤ C * D ^ (16 * i + 1) :=
    (hFj i hi).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hC)
  have hG16 (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i G a‖ ≤ C * D ^ (16 * i + 1) :=
    (hGj i hi).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hC)
  have hM16 (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i M a‖ ≤ C * D ^ (16 * i + 1) :=
    (hMj i hi).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hC)
  have hJj (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i J a‖ ≤ C * D ^ (16 * i + 1) := by
    let L := (compL ℝ (transversePlane k) Vec3 Vec3).flip (transversePlane k).subtypeL
    have hL : ‖L‖ ≤ 1 := by
      refine opNorm_le_bound _ zero_le_one fun S => ?_
      change ‖coframeLift k S‖ ≤ 1 * ‖S‖
      rw [one_mul]
      exact norm_coframeLift_le k S
    have hf : ContDiffAt ℝ i F a := (hF.of_le (by exact_mod_cast hi)).contDiffAt
    have hb := L.norm_iteratedFDeriv_comp_left hf le_rfl
    exact (hb.trans (mul_le_of_le_one_left (norm_nonneg _) hL)).trans (hF16 i hi)
  have hId (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun _ : E => ContinuousLinearMap.id ℝ Vec3) a‖ ≤ 1 := by
    cases i with
    | zero => simpa only [norm_iteratedFDeriv_zero] using (norm_id_le (𝕜 := ℝ) (E := Vec3))
    | succ i =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero i), Pi.zero_apply, norm_zero]
      exact zero_le_one
  have hQj (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i Q a‖ ≤ (1 + C) * D ^ (16 * i + 8) := by
    change ‖iteratedFDeriv ℝ i (fun b => ContinuousLinearMap.id ℝ Vec3 - P b) a‖ ≤ _
    have hsub := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (x := a)
      (contDiffAt_const (c := ContinuousLinearMap.id ℝ Vec3))
      (hP.of_le (by exact_mod_cast hi)).contDiffAt
    change iteratedFDeriv ℝ i (fun b => ContinuousLinearMap.id ℝ Vec3 - P b) a = _ at hsub
    rw [hsub]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i (fun _ : E => ContinuousLinearMap.id ℝ Vec3) a‖ +
          ‖iteratedFDeriv ℝ i P a‖ := norm_sub_le _ _
      _ ≤ D ^ (16 * i + 8) + C * D ^ (16 * i + 8) :=
        add_le_add ((hId i).trans (one_le_pow₀ hD)) (hPj i hi)
      _ = _ := by ring
  let GQ (b : E) := (G b).comp (Q b)
  have hGQ : ContDiff ℝ n GQ := hG.clm_comp hQ
  have hGQj (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i GQ a‖ ≤ C_R * D ^ (16 * i + 9) :=
    norm_iteratedFDeriv_clm_comp_scaled_through_le hG hQ a hD₀ hC
      (by positivity : 0 ≤ 1 + C) hG16 hQj i hi
  have hRj (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i R a‖ ≤ C_R * D ^ (16 * i + 9) := by
    let K := (transversePlane k).orthogonalProjectionOnto
    let L := compL ℝ Vec3 Vec3 (transversePlane k) K
    have hL : ‖L‖ ≤ 1 := by
      refine opNorm_le_bound _ zero_le_one fun S => ?_
      change ‖K.comp S‖ ≤ 1 * ‖S‖
      exact (K.opNorm_comp_le S).trans
        (mul_le_mul_of_nonneg_right (transversePlane k).orthogonalProjectionOnto_norm_le (norm_nonneg _))
    have hgq : ContDiffAt ℝ i GQ a := (hGQ.of_le (by exact_mod_cast hi)).contDiffAt
    have hb := L.norm_iteratedFDeriv_comp_left hgq le_rfl
    exact (hb.trans (mul_le_of_le_one_left (norm_nonneg _) hL)).trans (hGQj i hi)
  let MJ (b : E) := (M b).comp (J b)
  have hMJ : ContDiff ℝ n MJ := hM.clm_comp hJ
  have hMJj (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i MJ a‖ ≤ C_MJ * D ^ (16 * i + 2) :=
    norm_iteratedFDeriv_clm_comp_scaled_through_le hM hJ a hD₀ hC hC hM16 hJj i hi
  change ∀ i ≤ n,
    ‖iteratedFDeriv ℝ i J a‖ ≤ C * D ^ (16 * i + 1) ∧
    ‖iteratedFDeriv ℝ i R a‖ ≤ C_R * D ^ (16 * i + 9) ∧
    ‖iteratedFDeriv ℝ i A a‖ ≤ (2 * (B * (C_R * C_MJ))) * D ^ (16 * i + 11)
  intro i hi
  refine ⟨hJj i hi, hRj i hi, ?_⟩
  change ‖iteratedFDeriv ℝ i (fun b => (-2 : ℝ) • (R b).comp (MJ b)) a‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((hR.clm_comp hMJ).of_le (by exact_mod_cast hi)).contDiffAt]
  calc
    _ ≤ 2 * ‖iteratedFDeriv ℝ i (fun b => (R b).comp (MJ b)) a‖ := by
      rw [neg_smul, two_smul, norm_neg, two_mul]
      exact norm_add_le _ _
    _ ≤ 2 * (B * (C_R * C_MJ) * D ^ (16 * i + 11)) :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_clm_comp_scaled_through_le hR hMJ a hD₀ hCR hCMJ hRj hMJj i hi) (by norm_num)
    _ = _ := by ring

set_option maxHeartbeats 1500000 in
/-- The fixed-plane lift, pullback, and generator of the actual parent flow
have a common derivative-order slope in the parent scale. The constants
depend only on the parent velocity-jet constants and the order. -/
theorem exists_parent_transverseCoframeJetBounds (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (U t) x‖ ≤ W n * D ^ j) →
        ∀ (k : Vec3) {Λ t₀ : ℝ}, 0 < Λ → t₀ ∈ Icc 0 T →
          ‖labelWaveVector X 0 0 k t₀‖ = Λ → ∀ n : ℕ, ∀ t ∈ Icc 0 T,
          let F := fderiv ℝ (X 0 t)
          let G (b : Vec3) := fderiv ℝ (X t 0) (X 0 t b)
          let M (b : Vec3) := fderiv ℝ (U t) (X 0 t b)
          let J (b : Vec3) := coframeLift k (F b)
          let R (b : Vec3) := coframePullback k (G b)
          let A (b : Vec3) := fixedTransverseGenerator (M b) (J b) (R b)
          ContDiff ℝ ∞ J ∧ ContDiff ℝ ∞ R ∧ ContDiff ℝ ∞ A ∧
          ∀ a : Vec3, ∀ i ≤ n,
            ‖iteratedFDeriv ℝ i J a‖ ≤ C n * D ^ (16 * i + 1) ∧
            ‖iteratedFDeriv ℝ i R a‖ ≤ C n * D ^ (16 * i + 9) ∧
            ‖iteratedFDeriv ℝ i A a‖ ≤ C n * D ^ (16 * i + 11) := by
  obtain ⟨K, hK, hParent⟩ := exists_parent_coefficientJetBounds W hW
  let Q (n : ℕ) := 1 + ∑ j ∈ Finset.range (n + 1), K j
  let B (n : ℕ) : ℝ := 2 ^ n
  let CR (n : ℕ) := B n * (Q n * (1 + Q n))
  let CMJ (n : ℕ) := B n * (Q n * Q n)
  let CA (n : ℕ) := 2 * (B n * (CR n * CMJ n))
  let C (n : ℕ) := Q n + CR n + CA n
  have hQ (n : ℕ) : 0 ≤ Q n :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun j _ => hK j)
  have hB (n : ℕ) : 0 ≤ B n := by dsimp only [B]; positivity
  have hCR (n : ℕ) : 0 ≤ CR n := mul_nonneg (hB n)
    (mul_nonneg (hQ n) (add_nonneg zero_le_one (hQ n)))
  have hCMJ (n : ℕ) : 0 ≤ CMJ n := mul_nonneg (hB n) (mul_nonneg (hQ n) (hQ n))
  have hCA (n : ℕ) : 0 ≤ CA n :=
    mul_nonneg (by norm_num) (mul_nonneg (hB n) (mul_nonneg (hCR n) (hCMJ n)))
  have hCoe (n : ℕ) : 0 ≤ C n ∧ Q n ≤ C n ∧ CR n ≤ C n ∧ CA n ≤ C n := by
    dsimp only [C]
    have hq := hQ n
    have hr := hCR n
    have ha := hCA n
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hKQ {i n : ℕ} (hi : i ≤ n) : K i ≤ Q n := by
    have hm : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun j _ => hK j) hm).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, fun n => (hCoe n).1, ?_⟩
  intro U X T D hT hT₁ hD hX hU hper hF hG hUJet k Λ t₀ hΛ ht₀ hcenter n t ht
  dsimp only
  let F := fderiv ℝ (X 0 t)
  let G (b : Vec3) := fderiv ℝ (X t 0) (X 0 t b)
  let M (b : Vec3) := fderiv ℝ (U t) (X 0 t b)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hFlow (j : ℕ) : ContDiff ℝ j (X 0 t) := (hX.labelJets_evolve j hT hU hper).1 t ht
  have hFlowSmooth : ContDiff ℝ ∞ (X 0 t) := contDiff_infty.mpr hFlow
  have hFs : ContDiff ℝ ∞ F := (contDiff_infty_iff_fderiv.mp hFlowSmooth).2
  have hGs : ContDiff ℝ ∞ G := contDiff_infty.mpr fun j =>
    hX.contDiff_inverseLabelDerivative hT hU₂ hper h₀ ht (hFlow (j + 1))
  have hUtime : ContDiff ℝ ∞ (U t) :=
    contDiffOn_univ.mp (hU.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun b _ => ⟨ht, mem_univ b⟩))
  have hMs : ContDiff ℝ ∞ M := (contDiff_infty_iff_fderiv.mp hUtime).2.comp hFlowSmooth
  have hκ (b : Vec3) : (G b).adjoint k ≠ 0 := by
    have hlower := (hX.norm_normalizedLabelWaveVector_bounds hT hU₂ hper ht₀ ht b k hD hΛ hcenter
      (hF t₀ ht₀ 0) (hG t₀ ht₀ 0) (hF t ht b) (hG t ht b)).2.1
    have hne := (normalizedWaveNorm_ne_zero_and_inv_sq_le (zero_lt_one.trans_le hD) hlower).1
    change labelWaveVector X 0 b k t ≠ 0
    intro hzero
    exact hne (by rw [hzero, smul_zero])
  obtain ⟨hJs, hRs, hAs⟩ := contDiff_transverseCoframeFields k hFs hGs hMs hκ
  refine ⟨hJs, hRs, hAs, fun a => ?_⟩
  have hJets (j : ℕ) := hParent hT hT₁ hD hX hU hper hF hG hUJet k hΛ ht₀ hcenter j t ht a
  have hExpand (j : ℕ) (hj : j ≤ n) (e : ℕ) : K j * D ^ e ≤ Q n * D ^ e :=
    mul_le_mul_of_nonneg_right (hKQ hj) (pow_nonneg hD₀ _)
  have hz := norm_iteratedFDeriv_transverseCoframeFields_le k
    (hFs.of_le (by simp) : ContDiff ℝ n F)
    (hGs.of_le (by simp) : ContDiff ℝ n G)
    (hMs.of_le (by simp) : ContDiff ℝ n M) hκ a hD (hQ n)
    (fun j hj => (hJets j).1.trans (hExpand j hj _))
    (fun j hj => (hJets j).2.1.trans (hExpand j hj _))
    (fun j hj => (hJets j).2.2.2.1.trans (hExpand j hj _))
    (fun j hj => (hJets j).2.2.2.2.2.2.trans (hExpand j hj _))
  intro i hi
  obtain ⟨hJb, hRb, hAb⟩ := hz i hi
  obtain ⟨_, hCQ, hCR', hCA'⟩ := hCoe n
  exact ⟨hJb.trans (mul_le_mul_of_nonneg_right hCQ (pow_nonneg hD₀ _)),
    hRb.trans (mul_le_mul_of_nonneg_right hCR' (pow_nonneg hD₀ _)),
    hAb.trans (mul_le_mul_of_nonneg_right hCA' (pow_nonneg hD₀ _))⟩

end LocalizedAmplitude

/-- The scaled envelope is the unit envelope evaluated at the rescaled label. -/
theorem radialEnvelope_eq_unit_scaled {ell : ℝ} (hell : 0 < ell) :
    radialEnvelope ell = fun a => radialEnvelope 1 (ell⁻¹ • a) := by
  funext a
  simp only [radialEnvelope, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hell.le),
    div_eq_inv_mul, inv_one, one_mul]

/-- At each order the envelope costs precisely the inverse power of its radius. -/
theorem exists_norm_iteratedFDeriv_radialEnvelope_le (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : ℝ, 0 < ell → ∀ x : Vec3,
      ‖iteratedFDeriv ℝ m (radialEnvelope ell) x‖ ≤ C * ell⁻¹ ^ m := by
  have hSmooth := contDiff_radialEnvelope (ℓ := 1) (by norm_num)
  let jet := fun x : Vec3 => ‖iteratedFDeriv ℝ m (radialEnvelope 1) x‖
  let ball := Metric.closedBall (0 : Vec3) 2
  have hCont : Continuous jet := (hSmooth.continuous_iteratedFDeriv (by simp)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vec3) 2).bddAbove_image hCont.continuousOn
  let C' := max 1 C
  have hC' : 0 < C' := zero_lt_one.trans_le (le_max_left _ _)
  have hUnit (x : Vec3) : jet x ≤ C' := by
    by_cases hx : x ∈ ball
    · exact (hC (mem_image_of_mem jet hx)).trans (le_max_right _ _)
    · have hz : iteratedFDeriv ℝ m (radialEnvelope 1) x = 0 := by
        apply Function.notMem_support.mp
        intro hx'
        have hx'' := tsupport_radialEnvelope_subset (show 0 < (1 : ℝ) by norm_num)
          (support_iteratedFDeriv_subset m hx')
        change ‖x‖ ≤ 2 * (1 : ℝ) at hx''
        apply hx
        simpa only [ball, Metric.mem_closedBall, dist_zero_right, mul_one] using hx''
      simpa only [jet, hz, norm_zero] using hC'.le
  refine ⟨C', hC', fun ell hell x => ?_⟩
  rw [radialEnvelope_eq_unit_scaled hell,
    iteratedFDeriv_comp_const_smul ell⁻¹ (hSmooth.of_le (by simp)), norm_smul,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hell.le) _), mul_comm C']
  exact mul_le_mul_of_nonneg_left (hUnit _) (pow_nonneg (inv_nonneg.mpr hell.le) _)

/-- Weighting by the envelope radius makes every spatial envelope jet uniformly bounded. -/
theorem exists_weighted_iteratedFDeriv_radialEnvelope_le (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : ℝ, 0 < ell → ∀ x : Vec3,
      ell ^ m * ‖iteratedFDeriv ℝ m (radialEnvelope ell) x‖ ≤ C := by
  obtain ⟨C, hC, hj⟩ := exists_norm_iteratedFDeriv_radialEnvelope_le m
  refine ⟨C, hC, fun ell hell x => ?_⟩
  have hpow : ell ^ m * ell⁻¹ ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hell.ne', one_pow]
  calc
    _ ≤ ell ^ m * (C * ell⁻¹ ^ m) := mul_le_mul_of_nonneg_left (hj ell hell x) (pow_nonneg hell.le _)
    _ = C * (ell ^ m * ell⁻¹ ^ m) := by ring
    _ = C := by rw [hpow, mul_one]


/-- A fixed number of radius-normalized envelope derivatives has a bound
that depends on the derivative order alone. -/
theorem exists_phaseJetBound_scaledRadialEnvelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ℓ : ℝ}, 0 < ℓ →
      PhaseJetBound N C (fun a : Vec3 => radialEnvelope ℓ (ℓ • a)) := by
  choose c hc hjet using exists_weighted_iteratedFDeriv_radialEnvelope_le
  let C := 1 + ∑ m ∈ Finset.range (N + 1), c m
  have hs : 0 ≤ ∑ m ∈ Finset.range (N + 1), c m :=
    Finset.sum_nonneg fun m _ => (hc m).le
  refine ⟨C, by dsimp only [C]; linarith, fun {ℓ} hℓ m hm a => ?_⟩
  refine (norm_iteratedFDeriv_scaledLabel_le (contDiff_radialEnvelope hℓ) hℓ.le m a).trans
    ((hjet m ℓ hℓ (ℓ • a)).trans ?_)
  have hsum := Finset.single_le_sum (f := c) (fun m _ => (hc m).le)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  dsimp only [C]
  linarith

/-- The first-order envelope threshold bounds every smaller radius power. -/
theorem radius_power_small {D ℓ C : ℝ} (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ)
    (hC : 1 ≤ C) (hr : 2 * C * ℓ * D ^ 30 ≤ 1) {p : ℕ} (hp : p ≤ 30) :
    ℓ * D ^ p ≤ 1 := by
  calc
    ℓ * D ^ p ≤ ℓ * D ^ 30 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hp) hℓ
    _ ≤ (2 * C) * (ℓ * D ^ 30) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    _ ≤ 1 := by rw [← mul_assoc]; exact hr

/-- On labels in the scaled envelope, the coframe generator differs from
its centered value by at most the reciprocal center propagator bound. -/
theorem norm_scaledLabel_generator_sub_center_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Vec3 → E} (hA : ContDiff ℝ ∞ A) {D ℓ C : ℝ}
    (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) (hC : 1 ≤ C)
    (hr : 2 * C * ℓ * D ^ 30 ≤ 1)
    (hgrad : ∀ a, ‖iteratedFDeriv ℝ 1 A a‖ ≤ C * D ^ 27)
    {a : Vec3} (ha : ‖a‖ ≤ 2) : ‖A (ℓ • a) - A 0‖ ≤ (D ^ 3)⁻¹ := by
  have hGrad (b : Vec3) : ‖fderiv ℝ A b‖ ≤ C * D ^ 27 := by
    simpa only [norm_iteratedFDeriv_one] using hgrad b
  have hLip := (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
    (fun b _ => (hA.differentiable (by simp)) b) (fun b _ => hGrad b)
    (mem_univ (0 : Vec3)) (mem_univ (ℓ • a))
  have hD₃ : 0 < D ^ 3 := by positivity
  calc
    _ ≤ C * D ^ 27 * (ℓ * ‖a‖) := by
      simpa only [sub_zero, norm_smul, Real.norm_of_nonneg hℓ] using hLip
    _ ≤ C * D ^ 27 * (ℓ * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha hℓ) (by positivity)
    _ ≤ _ := by
      rw [← one_div]
      apply (le_div_iff₀ hD₃).mpr
      calc
        _ = 2 * C * ℓ * D ^ 30 := by ring
        _ ≤ 1 := hr

namespace LocalizedAmplitude

local notation "Coeff" => Vec3 →L[ℝ] Vec3

set_option maxHeartbeats 1650000 in
/-- The physical enveloped seed has polynomial cost (D^{13}) at every
fixed order. The restriction on the label radius uses only the first
derivative of the generator. -/
theorem exists_seedOn_envelopedAmplitude_scaledJetBound_polynomial
    (N : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {F G M : ℝ → Vec3 → Coeff} {k : Vec3} {center : ℝ → Vec3} {dg : ℝ → ℝ}
        {l r ℓ D Cseed C₁ : ℝ} (w : SeedOn M (fun t a => (G t a).adjoint k) center l r ℓ D Cseed),
      l < r → r - l ≤ 1 → 0 < ℓ → 1 ≤ D → 1 ≤ C₁ → 2 * C₁ * ℓ * D ^ 30 ≤ 1 →
      (∀ a t, t ∈ Icc l r → (G t a).adjoint k ≠ 0) →
      (∀ a t, t ∈ Icc l r →
        HasDerivWithinAt (fun u => F u a) ((M t a).comp (F t a)) (Icc l r) t) →
      (∀ a t, t ∈ Icc l r →
        (G t a).comp (F t a) = .id ℝ Vec3 ∧ (F t a).comp (G t a) = .id ℝ Vec3) →
      ContDiffOn ℝ ∞ (Function.uncurry F) (Icc l r ×ˢ (univ : Set Vec3)) →
      ContDiffOn ℝ ∞ (Function.uncurry G) (Icc l r ×ˢ (univ : Set Vec3)) →
      ContDiffOn ℝ ∞ (Function.uncurry M) (Icc l r ×ˢ (univ : Set Vec3)) →
      ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc l r ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc l r, 0 < ‖center t‖) →
      (∀ t ∈ Icc l r, HasDerivWithinAt (fun u => ‖center u‖) (dg t) (Icc l r) t) →
      ContinuousOn dg (Icc l r) →
      let J (t : ℝ) (a : Vec3) := coframeLift k (F t a)
      let R (t : ℝ) (a : Vec3) := coframePullback k (G t a)
      let A (t : ℝ) (a : Vec3) := fixedTransverseGenerator (M t a) (J t a) (R t a)
      (∀ t ∈ Icc l r, ∀ a, ‖iteratedFDeriv ℝ 1 (A t) a‖ ≤ C₁ * D ^ 27) →
      (∀ t ∈ Icc l r, ∀ m ≤ N, ∀ a,
        ‖iteratedFDeriv ℝ m (J t) a‖ ≤ C * D ^ (16 * m + 1) ∧
        ‖iteratedFDeriv ℝ m (R t) a‖ ≤ C * D ^ (16 * m + 9) ∧
        ‖iteratedFDeriv ℝ m (A t) a‖ ≤ C * D ^ (16 * m + 11)) →
      (∀ y : ℝ → transversePlane k,
        (∀ t ∈ Icc l r, HasDerivWithinAt y (A t 0 (y t)) (Icc l r) t) →
        ∀ u ∈ Icc l r, ∀ v ∈ Icc u r,
          ‖y v‖ / ‖center v‖ ≤ D ^ 3 * (‖y u‖ / ‖center u‖)) →
      ∀ t ∈ Icc l r, PhaseJetBound N (B * D ^ 13 * ‖center t‖)
        (fun a => radialEnvelope ℓ (ℓ • a) • w.amplitude t (ℓ • a)) := by
  obtain ⟨CE, hCE, hEjet⟩ := exists_phaseJetBound_scaledRadialEnvelope N
  let e := Real.exp 1
  let Q := linearODEWordFactor (e * C) N
  let B₀ := (2 : ℝ) ^ N * (C * (Q * (e * ((2 : ℝ) ^ N * (CE * C)))))
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hCE₀ : 0 ≤ CE := zero_le_one.trans hCE
  have he : 0 ≤ e := Real.exp_nonneg _
  have hQ : 0 ≤ Q := linearODEWordFactor_nonneg (mul_nonneg he hC₀) _
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨1 + B₀, by linarith, ?_⟩
  intro F G M k center dg l r ℓ D Cseed C₁ w hlr hT hℓ hD hC₁ hrad
    hκ hF hInv hFs hGs hMs hws hpos hg hdg J R A hgrad hjet hstable t ht
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hs : ℓ * D ^ 16 ≤ 1 := radius_power_small hD hℓ.le hC₁ hrad (by decide)
  have h30 := radius_power_small hD hℓ.le hC₁ hrad (p := 30) (by decide)
  have hJRA (u : ℝ) (hu : u ∈ Icc l r) :
      ContDiff ℝ ∞ (J u) ∧ ContDiff ℝ ∞ (R u) ∧ ContDiff ℝ ∞ (A u) :=
    contDiff_transverseCoframeFields k (contDiff_slice_on_closedSlab hFs hu)
      (contDiff_slice_on_closedSlab hGs hu) (contDiff_slice_on_closedSlab hMs hu) fun a => hκ a u hu
  have hj (u : ℝ) (hu : u ∈ Icc l r) :
      PhaseJetBound N (C * D) (fun a => J u (ℓ • a)) := by
    intro m hm a
    have h := (norm_iteratedFDeriv_scaledLabel_power_le (hJRA u hu).1 hD hℓ.le hs hC₀ m a
      (hjet u hu m hm (ℓ • a)).1).1
    simpa only [pow_one] using h
  have hr : PhaseJetBound N (C * D ^ 9) (fun a => R l (ℓ • a)) := by
    have hl : l ∈ Icc l r := left_mem_Icc.mpr hlr.le
    intro m hm a
    exact (norm_iteratedFDeriv_scaledLabel_power_le (hJRA l hl).2.1 hD hℓ.le hs hC₀ m a
      (hjet l hl m hm (ℓ • a)).2.1).1
  have ha (m : ℕ) (hm : m ≤ N) (hm₀ : 0 < m) (a : Vec3) (u : ℝ) (hu : u ∈ Icc l r) :
      ‖iteratedFDeriv ℝ m (fun b => A u (ℓ • b)) a‖ ≤ C * ℓ * D ^ 27 :=
    (norm_iteratedFDeriv_scaledLabel_power_le (hJRA u hu).2.2 hD hℓ.le hs hC₀ m a
      (hjet u hu m hm (ℓ • a)).2.2).2 hm₀
  have hn (a : Vec3) (ha : ‖a‖ ≤ 2) (u : ℝ) (hu : u ∈ Icc l r) :
      ‖A u (ℓ • a) - A u 0‖ ≤ (D ^ 3)⁻¹ :=
    norm_scaledLabel_generator_sub_center_le (hJRA u hu).2.2 hD hℓ.le hC₁ hrad (hgrad u hu) ha
  have hscaledStable :
      ∀ y : ℝ → transversePlane k,
        (∀ t ∈ Icc l r, HasDerivWithinAt y (A t (ℓ • 0) (y t)) (Icc l r) t) →
        ∀ u ∈ Icc l r, ∀ v ∈ Icc u r,
          ‖y v‖ / ‖center v‖ ≤ D ^ 3 * (‖y u‖ / ‖center u‖) := by
    simpa only [smul_zero] using hstable
  have h := w.envelopedAmplitude_scaledJetBound N hlr hT hℓ
    (K := D ^ 3) (CA := C * ℓ * D ^ 27) (CJ := C * D) (CR := C * D ^ 9) (CE := CE)
    (by positivity) (by positivity) (by positivity) (by positivity) hCE₀
    hκ hF hInv hFs hGs hMs hws hpos hg hdg hj hr (hEjet hℓ)
    (fun m hm hm₀ a _ u hu => ha m hm hm₀ a u hu)
    (fun a hs u hu => by simpa only [smul_zero] using hn a hs u hu) hscaledStable t ht
  let q := (e * D ^ 3) * (r - l) * (C * ℓ * D ^ 27)
  have hq₀ : 0 ≤ q := by
    exact mul_nonneg (mul_nonneg (mul_nonneg he (pow_nonneg hD₀.le _)) (sub_nonneg.mpr hlr.le))
      (by positivity)
  have hq : q ≤ e * C := by
    calc
      q = (e * C) * ((r - l) * (ℓ * D ^ 30)) := by dsimp only [q]; ring
      _ ≤ e * C := mul_le_of_le_one_right (mul_nonneg he hC₀)
        (mul_le_one₀ hT (by positivity) h30)
  have hQ' := linearODEWordFactor_mono hq₀ hq N
  intro m hm a
  refine (h m hm a).trans ?_
  change (2 : ℝ) ^ N * (C * D *
    (linearODEWordFactor q N * ((e * D ^ 3) * ((2 : ℝ) ^ N * (CE * (C * D ^ 9)))))) *
      ‖center t‖ ≤ _
  calc
    _ ≤ (2 : ℝ) ^ N * (C * D *
        (Q * ((e * D ^ 3) * ((2 : ℝ) ^ N * (CE * (C * D ^ 9)))))) *
        ‖center t‖ := by gcongr
    _ = B₀ * D ^ 13 * ‖center t‖ := by dsimp only [B₀]; ring
    _ ≤ _ := by gcongr; linarith

end LocalizedAmplitude

section Pressure

/-- The frequency-normalized pressure amplitude operator is the product of
the normalized covector, the strain and the reciprocal squared covector norm. -/
theorem phaseJetBound_normalizedPressureAmplitudeCoefficient
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {M : P → Vec3 →L[ℝ] Vec3} {κ : P → Vec3} {freq BK BM BQ : ℝ} {N : ℕ}
    (hf : 0 < freq) (hM : ContDiff ℝ ∞ M) (hκ : ContDiff ℝ ∞ κ) (hκ₀ : ∀ x, κ x ≠ 0)
    (hBK : 0 ≤ BK) (hBM : 0 ≤ BM) (hBQ : 0 ≤ BQ)
    (hKjet : PhaseJetBound N BK (fun a => freq⁻¹ • κ a))
    (hMjet : PhaseJetBound N BM M)
    (hQjet : PhaseJetBound N BQ (fun a => freq ^ 2 / ‖κ a‖ ^ 2)) :
    let Pcoef (a : P) := hierarchyRelayPressureAmplitudeCoefficient (M a) (freq⁻¹ • κ a)
    ContDiff ℝ ∞ Pcoef ∧
      PhaseJetBound N (2 * ((2 : ℝ) ^ N * (BQ * ((2 : ℝ) ^ N * (BK * BM))))) Pcoef := by
  intro Pcoef
  let K (a : P) := freq⁻¹ • κ a
  let Q (a : P) := freq ^ 2 / ‖κ a‖ ^ 2
  let I : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
  let L := compL ℝ Vec3 Vec3 ℝ
  let H (a : P) := (I (K a)).comp (M a)
  have hKs : ContDiff ℝ ∞ K := hκ.const_smul _
  have hQs : ContDiff ℝ ∞ Q := contDiff_const.div (hκ.norm_sq ℝ)
    (fun a => pow_ne_zero _ (norm_ne_zero_iff.mpr (hκ₀ a)))
  have hIs : ContDiff ℝ ∞ (I ∘ K) := I.contDiff.comp hKs
  have hIjet : PhaseJetBound N BK (I ∘ K) :=
    phaseJetBound_comp_left_contraction hKs I (norm_innerSL_le ℝ) hKjet
  have hHs : ContDiff ℝ ∞ H := hIs.clm_comp hM
  have hHjet : PhaseJetBound N ((2 : ℝ) ^ N * (BK * BM)) H :=
    phaseJetBound_bilinear_product L (norm_compL_le ℝ Vec3 Vec3 ℝ)
      hIs hM hBK hBM hIjet hMjet
  have hP : Pcoef = fun a => (-2 : ℝ) • (Q a • H a) := by
    funext a
    have hRecip : (‖K a‖ ^ 2)⁻¹ = Q a := by
      dsimp only [K, Q]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hf.le), mul_pow, mul_inv_rev,
        inv_pow, inv_inv, div_eq_mul_inv, mul_comm]
    change (-2 * (‖K a‖ ^ 2)⁻¹) • H a = _
    rw [hRecip, smul_smul]
  rw [hP]
  have hQH : ContDiff ℝ ∞ (fun a => Q a • H a) := hQs.smul hHs
  refine ⟨hQH.const_smul _, ?_⟩
  have hjet := phaseJetBound_bilinear_product (lsmul ℝ ℝ) opNorm_lsmul_le hQs hHs hBQ
    (mul_nonneg (by positivity) (mul_nonneg hBK hBM)) hQjet hHjet
  have htwo : ‖(-2 : ℝ)‖ = 2 := by norm_num
  simpa only [htwo] using phaseJetBound_const_smul (c := (-2 : ℝ)) hQH hjet

theorem normalizedPressureAmplitudeCoefficient_apply_leading
    {freq : ℝ} (hf : 0 < freq) (M : Vec3 →L[ℝ] Vec3) (κ a : Vec3) (c : ℝ) :
    hierarchyRelayPressureAmplitudeCoefficient M (freq⁻¹ • κ) (c • a) =
      freq * -wavePressureCoefficient c κ a M := by
  have hRecip : (‖freq⁻¹ • κ‖ ^ 2)⁻¹ = freq ^ 2 / ‖κ‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hf.le), mul_pow, mul_inv_rev,
      inv_pow, inv_inv, div_eq_mul_inv, mul_comm]
  simp only [hierarchyRelayPressureAmplitudeCoefficient, hRecip, wavePressureCoefficient,
    comp_apply, _root_.smul_apply, innerSL_apply_apply, map_smul, smul_eq_mul, div_eq_mul_inv]
  have hInv : freq ^ 2 * freq⁻¹ = freq := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hf.ne', mul_one]
  calc
    _ = (freq ^ 2 * freq⁻¹) * (-(2 * c * ⟪κ, M a⟫_ℝ) * (‖κ‖ ^ 2)⁻¹) := by ring
    _ = _ := by rw [hInv]; ring

set_option maxHeartbeats 950000 in
/-- The initial velocity and frequency-scaled pressure in (5.25) follow from
the scaled envelope-amplitude and pressure operator jets on a time slice. -/
theorem exists_leading_scaledJetBounds_of_slowJets (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {freq ℓ χ B P₀ g : ℝ} {a κ : Vec3 → Vec3}
      {M : Vec3 → Vec3 →L[ℝ] Vec3}, 1 ≤ freq → 0 ≤ B → 0 ≤ P₀ → 0 ≤ g →
      let h := freq ^ (-1 / 2 : ℝ)
      let γ := freq ^ (3 / 4 : ℝ) * g
      let A (x : Vec3) := (χ * radialEnvelope ℓ (ℓ • x)) • a (ℓ • x)
      let Pcoef (x : Vec3) :=
        hierarchyRelayPressureAmplitudeCoefficient (M (ℓ • x)) (freq⁻¹ • κ (ℓ • x))
      ContDiff ℝ ∞ A → ContDiff ℝ ∞ Pcoef →
      PhaseJetBound N (B * g) A → PhaseJetBound N P₀ Pcoef →
      PhaseJetBound N (γ * (C * B * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile ℓ h (fun x s => ((χ * radialEnvelope ℓ x) * waveProfile h s) • a x)) ∧
      PhaseJetBound N (γ * (C * ((2 : ℝ) ^ N * (P₀ * B)) * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile ℓ h (fun x s =>
          freq * oscillatoryPhasePressure (M x) (κ x) (fun _ => 0)
            (fun q => ((χ * radialEnvelope ℓ x) * waveProfile h q) • a x) s)) := by
  obtain ⟨C, hC, h⟩ := exists_switchedLeadingProfile_scaledJetBounds N
  refine ⟨C, hC, ?_⟩
  intro freq ℓ χ B P₀ g a κ M hf hB hP₀ hg hwidth γ A Pcoef hA hP hAjet hPjet
  let Q := (2 : ℝ) ^ N * (P₀ * B)
  have hQ : 0 ≤ Q := mul_nonneg (by positivity) (mul_nonneg hP₀ hB)
  have hf₀ : 0 < freq := zero_lt_one.trans_le hf
  have hγ : 0 ≤ γ := mul_nonneg (Real.rpow_nonneg hf₀.le _) hg
  have hγeq : γ * freq ^ (-3 / 4 : ℝ) = g := by
    dsimp only [γ]
    rw [show (-3 / 4 : ℝ) = -(3 / 4) by norm_num, Real.rpow_neg hf₀.le]
    rw [mul_right_comm, mul_inv_cancel₀ (Real.rpow_pos_of_pos hf₀ _).ne', one_mul]
  let fst := ContinuousLinearMap.fst ℝ Vec3 ℝ
  have hAs := hA.comp fst.contDiff
  have hAjet' := phaseJetBound_comp_contraction hA fst (ContinuousLinearMap.norm_fst_le ..) hAjet
  have hPAs : ContDiff ℝ ∞ (fun x => Pcoef x (A x)) := hP.clm_apply hA
  have hPA := phaseJetBound_clm_application hP hA hP₀ (mul_nonneg hB hg) hPjet hAjet
  have hPjet' := phaseJetBound_comp_contraction hPAs fst (ContinuousLinearMap.norm_fst_le ..) hPA
  have hPdef : (fun x => Pcoef x (A x)) ∘ fst = fun p : Vec3 × ℝ =>
      freq * -wavePressureCoefficient (χ * radialEnvelope ℓ (ℓ • p.1))
        (κ (ℓ • p.1)) (a (ℓ • p.1)) (M (ℓ • p.1)) := by
    funext p
    exact normalizedPressureAmplitudeCoefficient_apply_leading hf₀ _ _ _ _
  have hPAs' := hPAs.comp fst.contDiff
  rw [hPdef] at hPAs' hPjet'
  have hAformat : B * γ * freq ^ (-3 / 4 : ℝ) = B * g := by rw [mul_assoc, hγeq]
  have hPformat : Q * γ * freq ^ (-3 / 4 : ℝ) = (2 : ℝ) ^ N * (P₀ * (B * g)) := by
    rw [mul_assoc, hγeq]
    dsimp only [Q]
    ring
  rw [← hAformat] at hAjet'
  rw [← hPformat] at hPjet'
  exact h hf hγ hB hQ hAs hPAs' hAjet' hPjet'


/-- The carrier-normalized pressure operator costs a fixed power (D^7)
through every fixed order of radius-normalized label derivatives. -/
theorem phaseJetBound_normalizedPressureAmplitudeCoefficient_polynomial
    (N : ℕ) {M : Vec3 → Vec3 →L[ℝ] Vec3} {κ : Vec3 → Vec3}
    {freq ℓ D C : ℝ} (hf : 0 < freq) (hℓ : 0 < ℓ) (hD : 1 ≤ D)
    (hR : ℓ * D ^ 16 ≤ 1) (hC : 0 ≤ C)
    (hM : ContDiff ℝ ∞ M) (hκ : ContDiff ℝ ∞ κ) (hκ₀ : ∀ a, κ a ≠ 0)
    (hjet : ∀ m ≤ N, ∀ a,
      ‖iteratedFDeriv ℝ m M a‖ ≤ C * D ^ (6 * m + 1) ∧
      ‖iteratedFDeriv ℝ m (fun b => freq⁻¹ • κ b) a‖ ≤ C * D ^ (7 * m + 2) ∧
      ‖iteratedFDeriv ℝ m (fun b => freq ^ 2 / ‖κ b‖ ^ 2) a‖ ≤ C * D ^ (16 * m + 4)) :
    let Pcoef (a : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M (ℓ • a)) (freq⁻¹ • κ (ℓ • a))
    ContDiff ℝ ∞ Pcoef ∧ PhaseJetBound N ((2 * (2 : ℝ) ^ (2 * N) * C ^ 3) * D ^ 7) Pcoef := by
  intro Pcoef
  have hRle (p : ℕ) (hp : p ≤ 16) : ℓ * D ^ p ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hp) hℓ.le).trans hR
  have hKs : ContDiff ℝ ∞ (fun a => freq⁻¹ • κ a) := hκ.const_smul _
  have hQs : ContDiff ℝ ∞ (fun a => freq ^ 2 / ‖κ a‖ ^ 2) :=
    contDiff_const.div (hκ.norm_sq ℝ) fun a => pow_ne_zero _ (norm_ne_zero_iff.mpr (hκ₀ a))
  have hKj : PhaseJetBound N (C * D ^ 2) (fun a => freq⁻¹ • κ (ℓ • a)) :=
    fun m hm a => (norm_iteratedFDeriv_scaledLabel_power_le hKs hD hℓ.le (hRle 7 (by decide))
      hC m a (hjet m hm (ℓ • a)).2.1).1
  have hMj : PhaseJetBound N (C * D) (fun a => M (ℓ • a)) := by
    intro m hm a
    simpa only [pow_one] using (norm_iteratedFDeriv_scaledLabel_power_le hM hD hℓ.le
      (hRle 6 (by decide)) hC m a (hjet m hm (ℓ • a)).1).1
  have hQj : PhaseJetBound N (C * D ^ 4) (fun a => freq ^ 2 / ‖κ (ℓ • a)‖ ^ 2) :=
    fun m hm a => (norm_iteratedFDeriv_scaledLabel_power_le hQs hD hℓ.le hR
      hC m a (hjet m hm (ℓ • a)).2.2).1
  have hScale : ContDiff ℝ ∞ (fun a : Vec3 => ℓ • a) := contDiff_id.const_smul _
  have h := phaseJetBound_normalizedPressureAmplitudeCoefficient hf (hM.comp hScale)
    (hκ.comp hScale) (fun a => hκ₀ (ℓ • a)) (by positivity) (by positivity) (by positivity) hKj hMj hQj
  refine ⟨h.1, fun m hm a => (h.2 m hm a).trans_eq ?_⟩
  rw [Nat.mul_comm 2 N, pow_mul, pow_two ((2 : ℝ) ^ N)]
  ring

/-- A switch of magnitude at most one leaves the common polynomial budget
for the initial velocity and frequency-normalized pressure unchanged. -/
theorem exists_leading_scaledJetBounds_polynomial (N : ℕ)
    {B P : ℝ} (hB : 1 ≤ B) (hP : 1 ≤ P) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {freq ℓ χ D g : ℝ} {a κ : Vec3 → Vec3}
      {M : Vec3 → Vec3 →L[ℝ] Vec3}, 1 ≤ freq → 1 ≤ D → |χ| ≤ 1 → 0 ≤ g →
      let h := freq ^ (-1 / 2 : ℝ)
      let γ := freq ^ (3 / 4 : ℝ) * g
      let A (x : Vec3) := radialEnvelope ℓ (ℓ • x) • a (ℓ • x)
      let Pcoef (x : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M (ℓ • x)) (freq⁻¹ • κ (ℓ • x))
      ContDiff ℝ ∞ A → ContDiff ℝ ∞ Pcoef →
      PhaseJetBound N (B * D ^ 13 * g) A → PhaseJetBound N (P * D ^ 7) Pcoef →
      PhaseJetBound N (γ * (C * D ^ 20 * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile ℓ h (fun x s => ((χ * radialEnvelope ℓ x) * waveProfile h s) • a x)) ∧
      PhaseJetBound N (γ * (C * D ^ 20 * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile ℓ h (fun x s =>
          freq * oscillatoryPhasePressure (M x) (κ x) (fun _ => 0)
            (fun q => ((χ * radialEnvelope ℓ x) * waveProfile h q) • a x) s)) := by
  obtain ⟨Cw, hCw, h⟩ := exists_leading_scaledJetBounds_of_slowJets N
  let C := 1 + Cw * B + Cw * ((2 : ℝ) ^ N * (P * B))
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hP₀ : 0 ≤ P := zero_le_one.trans hP
  have hCw₀ : 0 ≤ Cw := zero_le_one.trans hCw
  have hpos : 0 ≤ Cw * B ∧ 0 ≤ Cw * ((2 : ℝ) ^ N * (P * B)) := ⟨by positivity, by positivity⟩
  refine ⟨C, by dsimp only [C]; linarith [hpos.1, hpos.2], ?_⟩
  intro freq ℓ χ D g a κ M hf hD hχ hg hwidth γ A Pcoef hA hPcoef hAj hPj
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hAs := hA.const_smul χ
  have hAsj : PhaseJetBound N (B * D ^ 13 * g)
      (fun x => (χ * radialEnvelope ℓ (ℓ • x)) • a (ℓ • x)) := by
    intro m hm x
    have hh := phaseJetBound_const_smul (c := χ) hA hAj m hm x
    have heq : (fun x => (χ * radialEnvelope ℓ (ℓ • x)) • a (ℓ • x)) = χ • A := by
      funext x
      simp only [A, Pi.smul_apply, smul_smul]
    rw [heq]
    exact hh.trans (mul_le_of_le_one_left (by positivity) (by rwa [Real.norm_eq_abs]))
  have hAs' : ContDiff ℝ ∞ (fun x => (χ * radialEnvelope ℓ (ℓ • x)) • a (ℓ • x)) := by
    simpa only [A, smul_smul] using hAs
  obtain ⟨hv, hp⟩ := h hf (by positivity : 0 ≤ B * D ^ 13)
    (by positivity : 0 ≤ P * D ^ 7) hg hAs' hPcoef hAsj hPj
  have hvC : Cw * B ≤ C := by dsimp only [C]; linarith [hpos.2]
  have hpC : Cw * ((2 : ℝ) ^ N * (P * B)) ≤ C := by dsimp only [C]; linarith [hpos.1]
  constructor
  · intro m hm x
    refine (hv m hm x).trans ?_
    have hvD := pow_le_pow_right₀ hD (show 13 ≤ (20 : ℕ) by decide)
    rw [← mul_assoc Cw]
    gcongr
  · intro m hm x
    refine (hp m hm x).trans ?_
    have heq : Cw * ((2 : ℝ) ^ N * (P * D ^ 7 * (B * D ^ 13))) =
        (Cw * ((2 : ℝ) ^ N * (P * B))) * D ^ 20 := by ring
    rw [heq]
    gcongr

end Pressure

end

end TorusEuler
