import TorusEuler.SeedDerivativeBudgets
import TorusEuler.Paper.Proofs.S53.Library.Leaf51
import TorusEuler.Paper.Proofs.S53.Library.Leaves
import TorusEuler.Paper.Proofs.S53.Library.D2Bridge
import TorusEuler.Paper.Proofs.S53.Library.D2Coframe
import TorusEuler.Paper.Proofs.S53.Library.CopyLAC
import TorusEuler.Paper.Proofs.S53.Library.CopyLACaux
import TorusEuler.Paper.Proofs.S53.Library.CopyODEaux
import TorusEuler.Paper.Proofs.S53.Library.CopyODE

/-!
# S53 library: Lemma 5.3 chain: seed derivative budgets

Generated copy (script `s53tools/mkcopy.py`) of the declarations phaseJetBound_normalizedPressureAmplitudeCoefficient_polynomial, phaseJetBound_normalizedPressureAmplitudeCoefficient, phaseJetBound_bilinear_product, exists_leading_scaledJetBounds_polynomial, exists_leading_scaledJetBounds_of_slowJets, phaseJetBound_clm_application, exists_seedOn_envelopedAmplitude_scaledJetBound_polynomial, SeedOn.envelopedAmplitude_scaledJetBound, weighted_homogeneous_jetBounds_Icc, exists_parent_transverseCoframeJetBounds, norm_iteratedFDeriv_transverseCoframeFields_le, norm_iteratedFDeriv_clm_comp_scaled_through_le, opNorm_le_bound_on_unit_vectors, iteratedFDeriv_apply_fin_cast, phaseJetBound_const_smul, phaseJetBound_comp_contraction, contDiff_coframeLongitudinal of
`TorusEuler/SeedDerivativeBudgets.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section

variable [TorusEuler.Paper.Lib.S53.Leaves]

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S53

open TorusEuler
noncomputable section

section HomogeneousJets

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [TorusEuler.Paper.Lib.S53.Leaves] in
omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
/-- Copy of the library lemma `TorusEuler.opNorm_le_bound_on_unit_vectors` (glue), placed in `Paper.Lib.S53`. -/
theorem opNorm_le_bound_on_unit_vectors {m : ℕ}
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

omit [TorusEuler.Paper.Lib.S53.Leaves] in
omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
/-- Copy of the library lemma `TorusEuler.iteratedFDeriv_apply_fin_cast` (glue), placed in `Paper.Lib.S53`. -/
theorem iteratedFDeriv_apply_fin_cast {m n : ℕ} (h : m = n)
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
    simpa only [mul_zero, add_zero, linearODEWordFactor] using hwt
  · intro w _ p _ t _
    simp [phaseOperatorWord_eq_jet d (contDiff_const (c := (0 : E)))]
  · intro w hw hne p hp t ht
    exact (hword (contDiff_slice_on_closedSlab hA ht) w p).trans
      (hcoeff w.length hw (List.length_pos_iff.mpr hne) p hp t ht)

end HomogeneousJets

namespace LocalizedAmplitude

open LocalizedAmplitude
local notation "Coeff" => Vec3 →L[ℝ] Vec3

end LocalizedAmplitude

omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- Copy of the library lemma `TorusEuler.phaseJetBound_bilinear_product` (glue), placed in `Paper.Lib.S53`. -/
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
  have hfm : ContDiff ℝ m f := hf.of_le (by simp)
  have hgm : ContDiff ℝ m g := hg.of_le (by simp)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
      ‖iteratedFDeriv ℝ i f a‖ * ‖iteratedFDeriv ℝ (m - i) g a‖ ≤ A * B := by
    have hin : i ≤ m := by simpa using Finset.mem_range.mp hi
    exact mul_le_mul (hF i (hin.trans hm) a) (hG (m - i) ((Nat.sub_le _ _).trans hm) a)
      (norm_nonneg _) hA
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f a‖ * ‖iteratedFDeriv ℝ (m - i) g a‖ :=
      L.norm_iteratedFDeriv_le_of_bilinear_of_le_one hfm hgm a le_rfl hL
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (A * B) := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hterm i hi) (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ m * (A * B) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose m
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hm) (mul_nonneg hA hB)

omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- Copy of the library lemma `TorusEuler.phaseJetBound_clm_application` (glue), placed in `Paper.Lib.S53`. -/
theorem phaseJetBound_clm_application
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

open LocalizedAmplitude
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

omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- Copy of the library lemma `TorusEuler.phaseJetBound_const_smul` (glue), placed in `Paper.Lib.S53`. -/
theorem phaseJetBound_const_smul {f : E → F} (hf : ContDiff ℝ ∞ f)
    {B c : ℝ} {n : ℕ} (hjet : PhaseJetBound n B f) :
    PhaseJetBound n (‖c‖ * B) (fun x => c • f x) := by
  intro j hj a
  change ‖iteratedFDeriv ℝ j (c • f) a‖ ≤ ‖c‖ * B
  rw [iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by simp)), norm_smul]
  exact mul_le_mul_of_nonneg_left (hjet j hj a) (norm_nonneg _)

omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- Copy of the library lemma `TorusEuler.phaseJetBound_comp_contraction` (glue), placed in `Paper.Lib.S53`. -/
theorem phaseJetBound_comp_contraction {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
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

end Radius

namespace LocalizedAmplitude

open LocalizedAmplitude
local notation "End3" => Vec3 →L[ℝ] Vec3

section Regularity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- Copy of the library lemma `TorusEuler.contDiff_coframeLongitudinal` (glue), placed in `Paper.Lib.S53`. -/
theorem contDiff_coframeLongitudinal (k : Vec3) {G : E → End3} {N : ℕ∞ω}
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

set_option maxHeartbeats 1500000 in
/-- The coframe coefficients of the actual parent flow satisfy the power bound (D.6), by Lemma D.2(a)
(`transverseCoframe_jetPower`), as used in the proof of Lemma 5.3 (06c_finite_hierarchy.tex:92-95).
The leaf jets hold at the base scale `D₀`; the geometric bounds on the flow hold at the scale `D`. The
fields are `F = D_a X`, `G Q` with `Q` the projection orthogonal to `G^T k`, and `-2 (G Q)(M F)`; the
lift `J`, the pullback `R` and the generator `A` are fixed contractions of them
(`J = F ι`, `R = π (G Q)`, `A = π (-2 (G Q)(M F)) ι` with the inclusion `ι` and the orthogonal
projection `π` of the transverse plane). -/
theorem exists_parent_transverseCoframeJetPower (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) :
    ∃ C₁ C₂ : ℕ → ℝ, (∀ n, 0 ≤ C₁ n) ∧ (∀ n, 0 ≤ C₂ n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D D₀ : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D → 1 ≤ D₀ →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        ∀ (k : Vec3) {Λ t₀ : ℝ}, 0 < Λ → t₀ ∈ Icc 0 T →
          ‖labelWaveVector X 0 0 k t₀‖ = Λ → Lib.S5a.LeafBounds W U X T D₀ k Λ →
          ∀ t ∈ Icc 0 T,
          let F := fderiv ℝ (X 0 t)
          let G (b : Vec3) := fderiv ℝ (X t 0) (X 0 t b)
          let M (b : Vec3) := fderiv ℝ (U t) (X 0 t b)
          let J (b : Vec3) := coframeLift k (F b)
          let R (b : Vec3) := coframePullback k (G b)
          let A (b : Vec3) := fixedTransverseGenerator (M b) (J b) (R b)
          ContDiff ℝ ∞ J ∧ ContDiff ℝ ∞ R ∧ ContDiff ℝ ∞ A ∧
          JetPower W D₀ 16 F ∧
          JetPower C₁ D₀ 32
            (fun b => (G b).comp (oscillatoryTransverseProjection ((G b).adjoint k))) ∧
          JetPower C₂ D₀ 64 (fun b => (-2 : ℝ) •
            ((G b).comp (oscillatoryTransverseProjection ((G b).adjoint k))).comp
              ((M b).comp (F b))) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hcoframe⟩ := transverseCoframe_jetPower W hW
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro U X T D D₀ hT hT₁ hD hD₀ hX hU hper hF hG k Λ t₀ hΛ ht₀ hcenter hLeaf t ht
  dsimp only
  let F := fderiv ℝ (X 0 t)
  let G (b : Vec3) := fderiv ℝ (X t 0) (X 0 t b)
  let M (b : Vec3) := fderiv ℝ (U t) (X 0 t b)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
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
  have hPs := contDiff_coframeLongitudinal k hGs hκ
  have hpow (e m : ℕ) (hm : e ≤ 16 * (m + 1)) : D₀ ^ e ≤ D₀ ^ (16 * (m + 1)) :=
    pow_le_pow_right₀ hD₀ hm
  have hnn (m : ℕ) : 0 ≤ W m := hW m
  have hJets (m : ℕ) (x : Vec3) := hLeaf m t ht x
  have hF16 : JetPower W D₀ 16 F := ⟨hFs, fun m x => ((hJets m x).1.trans
    (mul_le_mul_of_nonneg_left (hpow _ m (by omega)) (hnn m)))⟩
  have hG16 : JetPower W D₀ 16 G := ⟨hGs, fun m x => ((hJets m x).2.1.trans
    (mul_le_mul_of_nonneg_left (hpow _ m (by omega)) (hnn m)))⟩
  have hM16 : JetPower W D₀ 16 M := ⟨hMs, fun m x => ((hJets m x).2.2.2.1.trans
    (mul_le_mul_of_nonneg_left (hpow _ m (by omega)) (hnn m)))⟩
  have hP16 : JetPower W D₀ 16 (fun b => (‖(G b).adjoint k‖ ^ 2)⁻¹ •
      InnerProductSpace.rankOne ℝ ((G b).adjoint k) ((G b).adjoint k)) :=
    ⟨hPs, fun m x => ((hJets m x).2.2.2.2.2.2.trans
      (mul_le_mul_of_nonneg_left (hpow _ m (by omega)) (hnn m)))⟩
  exact ⟨hJs, hRs, hAs, hF16, hcoframe k hD₀ hF16 hG16 hM16 hP16⟩

end LocalizedAmplitude

namespace LocalizedAmplitude

open LocalizedAmplitude
local notation "Coeff" => Vec3 →L[ℝ] Vec3

set_option maxHeartbeats 1650000 in
/-- The physical enveloped seed has polynomial cost (D^{13}) at every
fixed order. The restriction on the label radius uses only the first
derivative of the generator. -/
theorem exists_seedOn_envelopedAmplitude_scaledJetBound_polynomial
    (N : ℕ) (Kf Kg Ka : ℕ → ℝ) (hKf : ∀ m, 0 ≤ Kf m) (hKg : ∀ m, 0 ≤ Kg m) (hKa : ∀ m, 0 ≤ Ka m) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {F G M : ℝ → Vec3 → Coeff} {k : Vec3} {center : ℝ → Vec3} {dg : ℝ → ℝ}
        {l r ℓ D D₀ Cseed C₁ : ℝ} (w : SeedOn M (fun t a => (G t a).adjoint k) center l r ℓ D Cseed),
      l < r → r - l ≤ 1 → 0 < ℓ → 1 ≤ D → 1 ≤ D₀ → D₀ ^ d2Scale ≤ D → 1 ≤ C₁ →
      2 * C₁ * ℓ * D ^ 30 ≤ 1 →
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
      (∀ t ∈ Icc l r, JetPower Kf D₀ 16 (F t)) →
      (∀ t ∈ Icc l r, JetPower Kg D₀ 32
        (fun a => (G t a).comp (oscillatoryTransverseProjection ((G t a).adjoint k)))) →
      (∀ t ∈ Icc l r, JetPower Ka D₀ 64 (fun a => (-2 : ℝ) •
        ((G t a).comp (oscillatoryTransverseProjection ((G t a).adjoint k))).comp
          ((M t a).comp (F t a)))) →
      (∀ y : ℝ → transversePlane k,
        (∀ t ∈ Icc l r, HasDerivWithinAt y (A t 0 (y t)) (Icc l r) t) →
        ∀ u ∈ Icc l r, ∀ v ∈ Icc u r,
          ‖y v‖ / ‖center v‖ ≤ D ^ 3 * (‖y u‖ / ‖center u‖)) →
      ∀ t ∈ Icc l r, PhaseJetBound N (B * D ^ 13 * ‖center t‖)
        (fun a => radialEnvelope ℓ (ℓ • a) • w.amplitude t (ℓ • a)) := by
  obtain ⟨CE, hCE, hEjet⟩ := exists_phaseJetBound_scaledRadialEnvelope N
  obtain ⟨RF, hRF, hRFb⟩ := rescale_of_D2 (X := Vec3 →L[ℝ] Vec3) Kf hKf 16
  obtain ⟨RG, hRG, hRGb⟩ := rescale_of_D2 (X := Vec3 →L[ℝ] Vec3) Kg hKg 32
  obtain ⟨RA, hRA, hRAb⟩ := rescale_of_D2 (X := Vec3 →L[ℝ] Vec3) Ka hKa 64
  let C : ℝ := 1 + ∑ m ∈ Finset.range (N + 1), (RF m + RG m + RA m)
  have hsum : 0 ≤ ∑ m ∈ Finset.range (N + 1), (RF m + RG m + RA m) :=
    Finset.sum_nonneg fun m _ => add_nonneg (add_nonneg (hRF m) (hRG m)) (hRA m)
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hRC (m : ℕ) (hm : m ≤ N) : RF m ≤ C ∧ RG m ≤ C ∧ RA m ≤ C := by
    have h1 := Finset.single_le_sum (f := fun m => RF m + RG m + RA m)
      (fun m _ => add_nonneg (add_nonneg (hRF m) (hRG m)) (hRA m))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    have := hRF m
    have := hRG m
    have := hRA m
    dsimp only [C] at *
    refine ⟨by linarith, by linarith, by linarith⟩
  let e := Real.exp 1
  let Q := linearODEWordFactor (e * C) N
  let B₀ := (2 : ℝ) ^ N * (C * (Q * (e * ((2 : ℝ) ^ N * (CE * C)))))
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hCE₀ : 0 ≤ CE := zero_le_one.trans hCE
  have he : 0 ≤ e := Real.exp_nonneg _
  have hQ : 0 ≤ Q := linearODEWordFactor_nonneg (mul_nonneg he hC₀) _
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨1 + B₀, by linarith, ?_⟩
  intro F G M k center dg l r ℓ D D₀ Cseed C₁ w hlr hT hℓ hD hDb hpow hC₁ hrad
    hκ hF hInv hFs hGs hMs hws hpos hg hdg J R A hgrad hFj hGQj hAtj hstable t ht
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hs : ℓ * D ^ 16 ≤ 1 := radius_power_small hD hℓ.le hC₁ hrad (by decide)
  have h30 := radius_power_small hD hℓ.le hC₁ hrad (p := 30) (by decide)
  have hJRA (u : ℝ) (hu : u ∈ Icc l r) :
      ContDiff ℝ ∞ (J u) ∧ ContDiff ℝ ∞ (R u) ∧ ContDiff ℝ ∞ (A u) :=
    contDiff_transverseCoframeFields k (contDiff_slice_on_closedSlab hFs hu)
      (contDiff_slice_on_closedSlab hGs hu) (contDiff_slice_on_closedSlab hMs hu) fun a => hκ a u hu
  have hpow64 : D₀ ^ 64 ≤ D := hpow
  have hsD (a : ℕ) (ha : a ≤ 64) : ℓ * D₀ ^ a ≤ 1 := by
    calc ℓ * D₀ ^ a ≤ ℓ * D₀ ^ 64 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hDb ha) hℓ.le
      _ ≤ ℓ * D := mul_le_mul_of_nonneg_left hpow64 hℓ.le
      _ ≤ ℓ * D ^ 30 := mul_le_mul_of_nonneg_left (le_self_pow₀ hD (by norm_num)) hℓ.le
      _ ≤ 1 := h30
  have hDpow (a e : ℕ) (hae : a ≤ 64) (he : 1 ≤ e) : D₀ ^ a ≤ D ^ e :=
    (pow_le_pow_right₀ hDb hae).trans (hpow64.trans (le_self_pow₀ hD (by omega)))
  have hscaleS : ContDiff ℝ ∞ (fun a : Vec3 => ℓ • a) := contDiff_id.const_smul _
  have hj (u : ℝ) (hu : u ∈ Icc l r) :
      PhaseJetBound N (C * D) (fun a => J u (ℓ • a)) := by
    intro m hm a
    have hg : ContDiff ℝ ∞ (fun y => F u (ℓ • y)) := (hFj u hu).1.comp hscaleS
    refine (norm_iteratedFDeriv_coframeLift_le k hg m a).trans ?_
    refine ((hRFb hDb hℓ (hsD 16 (by norm_num)) (hFj u hu) m a).1).trans ?_
    rw [← pow_one D]
    exact mul_le_mul (hRC m hm).1 (hDpow 16 1 (by norm_num) le_rfl) (pow_nonneg (by linarith) _)
      (by linarith [(hRC m hm).1, hRF m])
  have hr : PhaseJetBound N (C * D ^ 9) (fun a => R l (ℓ • a)) := by
    have hl : l ∈ Icc l r := left_mem_Icc.mpr hlr.le
    intro m hm a
    have hg : ContDiff ℝ ∞ (fun y => (G l (ℓ • y)).comp
        (oscillatoryTransverseProjection ((G l (ℓ • y)).adjoint k))) :=
      (hGQj l hl).1.comp hscaleS
    refine (norm_iteratedFDeriv_projLeft_le k hg m a).trans ?_
    refine ((hRGb hDb hℓ (hsD 32 (by norm_num)) (hGQj l hl) m a).1).trans ?_
    exact mul_le_mul (hRC m hm).2.1 (hDpow 32 9 (by norm_num) (by norm_num)) (pow_nonneg (by linarith) _)
      (by linarith [(hRC m hm).1, hRF m])
  have ha (m : ℕ) (hm : m ≤ N) (hm₀ : 0 < m) (a : Vec3) (u : ℝ) (hu : u ∈ Icc l r) :
      ‖iteratedFDeriv ℝ m (fun b => A u (ℓ • b)) a‖ ≤ C * ℓ * D ^ 27 := by
    have hg : ContDiff ℝ ∞ (fun y => (-2 : ℝ) •
        ((G u (ℓ • y)).comp (oscillatoryTransverseProjection ((G u (ℓ • y)).adjoint k))).comp
          ((M u (ℓ • y)).comp (F u (ℓ • y)))) := (hAtj u hu).1.comp hscaleS
    have hAeq : (fun b => A u (ℓ • b)) = fun b => (transversePlane k).orthogonalProjectionOnto.comp
        (coframeLift k ((-2 : ℝ) • ((G u (ℓ • b)).comp
          (oscillatoryTransverseProjection ((G u (ℓ • b)).adjoint k))).comp
            ((M u (ℓ • b)).comp (F u (ℓ • b))))) := by
      funext b
      exact fixedTransverseGenerator_eq k _ _ _
    rw [hAeq]
    refine (norm_iteratedFDeriv_projLeft'_le k (contDiff_coframeLift' k hg) m a).trans ?_
    refine (norm_iteratedFDeriv_coframeLift_le k hg m a).trans ?_
    refine ((hRAb hDb hℓ (hsD 64 le_rfl) (hAtj u hu) m a).2 hm₀).trans ?_
    have h2 : D₀ ^ (2 * 64) ≤ D ^ 27 := by
      rw [pow_mul']
      exact (pow_le_pow_left₀ (pow_nonneg (by linarith) _) hpow64 2).trans
        (pow_le_pow_right₀ hD (by norm_num))
    have hRAC : 0 ≤ C := by linarith [(hRC m hm).2.2, hRA m]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hRC m hm).2.2 hℓ.le) h2
      (pow_nonneg (by linarith) _) (mul_nonneg hRAC hℓ.le)
  have hn (a : Vec3) (ha : ‖a‖ ≤ 2) (u : ℝ) (hu : u ∈ Icc l r) :
      ‖A u (ℓ • a) - A u 0‖ ≤ (D ^ 3)⁻¹ :=
    norm_scaledLabel_generator_sub_center_le (hJRA u hu).2.2 hD hℓ.le hC₁ hrad (hgrad u hu) ha
  have hscaledStable :
      ∀ y : ℝ → transversePlane k,
        (∀ t ∈ Icc l r, HasDerivWithinAt y (A t (ℓ • 0) (y t)) (Icc l r) t) →
        ∀ u ∈ Icc l r, ∀ v ∈ Icc u r,
          ‖y v‖ / ‖center v‖ ≤ D ^ 3 * (‖y u‖ / ‖center u‖) := by
    simpa only [smul_zero] using hstable
  have h := SeedOn.envelopedAmplitude_scaledJetBound w N hlr hT hℓ
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

omit [TorusEuler.Paper.Lib.S53.Leaves] in
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

set_option maxHeartbeats 950000 in
/-- The initial velocity and frequency-scaled pressure in (5.22) follow from
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


/-- The carrier-normalized pressure operator costs a fixed power (D^7) through every fixed order of
radius-normalized label derivatives. The rescaled jets of the coefficients `M`, `κ/λ` and `λ²/|κ|²`
are bounded by Lemma D.2(c) (`rescale_of_D2`) at the base scale `D₀ ≤ D^{1/64}`. -/
theorem phaseJetBound_normalizedPressureAmplitudeCoefficient_polynomial
    (N : ℕ) (W : ℕ → ℝ) (hW : ∀ m, 0 ≤ W m) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧
      ∀ {M : Vec3 → Vec3 →L[ℝ] Vec3} {κ : Vec3 → Vec3} {freq ℓ D D₀ : ℝ},
        0 < freq → 0 < ℓ → 1 ≤ D → 1 ≤ D₀ → D₀ ^ d2Scale ≤ D → ℓ * D ^ 16 ≤ 1 →
        ContDiff ℝ ∞ κ → (∀ a, κ a ≠ 0) →
        JetPower W D₀ 16 M → JetPower W D₀ 16 (fun b => freq⁻¹ • κ b) →
        JetPower W D₀ 16 (fun b => freq ^ 2 / ‖κ b‖ ^ 2) →
        let Pcoef (a : Vec3) :=
          hierarchyRelayPressureAmplitudeCoefficient (M (ℓ • a)) (freq⁻¹ • κ (ℓ • a))
        ContDiff ℝ ∞ Pcoef ∧ PhaseJetBound N (Cp * D ^ 7) Pcoef := by
  obtain ⟨RM, hRM, hRMb⟩ := rescale_of_D2 (X := Vec3 →L[ℝ] Vec3) W hW 16
  obtain ⟨RK, hRK, hRKb⟩ := rescale_of_D2 (X := Vec3) W hW 16
  obtain ⟨RQ, hRQ, hRQb⟩ := rescale_of_D2 (X := ℝ) W hW 16
  let C : ℝ := 1 + ∑ m ∈ Finset.range (N + 1), (RM m + RK m + RQ m)
  have hsum : 0 ≤ ∑ m ∈ Finset.range (N + 1), (RM m + RK m + RQ m) :=
    Finset.sum_nonneg fun m _ => add_nonneg (add_nonneg (hRM m) (hRK m)) (hRQ m)
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hRC (m : ℕ) (hm : m ≤ N) : RM m ≤ C ∧ RK m ≤ C ∧ RQ m ≤ C := by
    have h1 := Finset.single_le_sum (f := fun m => RM m + RK m + RQ m)
      (fun m _ => add_nonneg (add_nonneg (hRM m) (hRK m)) (hRQ m))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    have := hRM m
    have := hRK m
    have := hRQ m
    dsimp only [C] at *
    refine ⟨by linarith, by linarith, by linarith⟩
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  refine ⟨2 * (2 : ℝ) ^ (2 * N) * C ^ 3, by positivity, ?_⟩
  intro M κ freq ℓ D D₀ hf hℓ hD hDb hpow hR hκ hκ₀ hMj hKj hQj Pcoef
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hpow64 : D₀ ^ 64 ≤ D := hpow
  have hs16 : ℓ * D₀ ^ 16 ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hDb (by norm_num : 16 ≤ 64)).trans
      (hpow64.trans (le_self_pow₀ hD (by norm_num)))) hℓ.le).trans hR
  have hDpow (e : ℕ) (he : 1 ≤ e) : D₀ ^ 16 ≤ D ^ e :=
    (pow_le_pow_right₀ hDb (by norm_num : 16 ≤ 64)).trans (hpow64.trans (le_self_pow₀ hD (by omega)))
  have hKj' : PhaseJetBound N (C * D ^ 2) (fun a => freq⁻¹ • κ (ℓ • a)) := fun m hm a =>
    ((hRKb hDb hℓ hs16 hKj m a).1).trans (mul_le_mul (hRC m hm).2.1 (hDpow 2 (by norm_num))
      (pow_nonneg (by linarith) _) hC₀)
  have hMj' : PhaseJetBound N (C * D) (fun a => M (ℓ • a)) := by
    intro m hm a
    have h := ((hRMb hDb hℓ hs16 hMj m a).1).trans (mul_le_mul (hRC m hm).1 (hDpow 1 le_rfl)
      (pow_nonneg (by linarith) _) hC₀)
    simpa only [pow_one] using h
  have hQj' : PhaseJetBound N (C * D ^ 4) (fun a => freq ^ 2 / ‖κ (ℓ • a)‖ ^ 2) := fun m hm a =>
    ((hRQb hDb hℓ hs16 hQj m a).1).trans (mul_le_mul (hRC m hm).2.2 (hDpow 4 (by norm_num))
      (pow_nonneg (by linarith) _) hC₀)
  have hScale : ContDiff ℝ ∞ (fun a : Vec3 => ℓ • a) := contDiff_id.const_smul _
  have h := phaseJetBound_normalizedPressureAmplitudeCoefficient hf (hMj.1.comp hScale)
    (hκ.comp hScale) (fun a => hκ₀ (ℓ • a)) (by positivity) (by positivity) (by positivity)
    hKj' hMj' hQj'
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

end TorusEuler.Paper.Lib.S53

