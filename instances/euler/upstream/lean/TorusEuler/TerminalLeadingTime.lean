import TorusEuler.SeedDerivativeBudgets
import TorusEuler.LaterWaveDerivativeBudgets
import TorusEuler.InductiveLaterStageAssembly
import TorusEuler.TerminalCoefficientTimeBase
import TorusEuler.TerminalTimeGraphCalculus
import TorusEuler.TerminalTimeJetNorms
import TorusEuler.TerminalPhaseTime

/-! Fixed-label, fixed-phase time bounds for the later leading wave. -/

open Set Filter
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {X E F G : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Differentiate in time while keeping the scaled label and phase fixed. -/
abbrev activeTimeJet (a b : ℝ) (i : ℕ) (f : ℝ → X → E) (t : ℝ) (x : X) : E :=
  iteratedDerivWithin i (fun u => f u x) (Icc a b) t

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
@[simp] theorem activeTimeJet_zero (a b : ℝ) (f : ℝ → X → E) : activeTimeJet a b 0 f = f := by
  funext t x
  exact congrFun iteratedDerivWithin_zero t

private theorem activeTimeJet_timeSlice {a b : ℝ} {f : ℝ → X → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set X))) (x : X) :
    ContDiffOn ℝ ∞ (fun t => f t x) (Icc a b) :=
  hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ ht => ⟨ht, mem_univ x⟩)

private theorem activeTimeJet_smooth {a b : ℝ} (hab : a < b) {f : ℝ → X → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set X))) (i : ℕ) :
    ContDiffOn ℝ ∞ (Function.uncurry (activeTimeJet a b i f)) (Icc a b ×ˢ (univ : Set X)) := by
  induction i with
  | zero => simpa only [activeTimeJet_zero] using hf
  | succ i ih =>
    let S : Set (ℝ × X) := Icc a b ×ˢ univ
    let L : ((ℝ × X) →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E (1, 0)
    let f' := Function.uncurry (activeTimeJet a b i f)
    have hd : ContDiffOn ℝ ∞ (fderivWithin ℝ f' S) S :=
      ih.fderivWithin ((uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ) (by simp)
    refine (L.contDiff.comp_contDiffOn hd).congr ?_
    rintro ⟨t, x⟩ ⟨ht, _⟩
    have hx : (t, x) ∈ S := ⟨ht, mem_univ x⟩
    have hd' := (ih.differentiableOn (by simp) (t, x) hx).hasFDerivWithinAt
    have hs := hd'.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).hasFDerivWithinAt
      (fun r hr => show (r, x) ∈ S from ⟨hr, mem_univ x⟩)
    have hs' : HasDerivWithinAt (fun r => activeTimeJet a b i f r x)
        (fderivWithin ℝ f' S (t, x) (1, 0)) (Icc a b) t := by
      simpa only [Function.comp_def, Function.uncurry_apply_pair,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using hs.hasDerivWithinAt
    change iteratedDerivWithin (i + 1) (fun u => f u x) (Icc a b) t =
      fderivWithin ℝ f' S (t,x) (1,0)
    rw [iteratedDerivWithin_succ]
    exact hs'.derivWithin (uniqueDiffOn_Icc hab t ht)

private theorem activeTimeJet_sliceSmooth {a b : ℝ} (hab : a < b) {f : ℝ → X → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set X))) (i : ℕ)
    {t : ℝ} (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (activeTimeJet a b i f t) :=
  contDiffOn_univ.mp <| (activeTimeJet_smooth hab hf i).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨ht, mem_univ x⟩)

private theorem activeTimeJet_eq_of_subset {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hsub : Icc c d ⊆ Icc a b) {f : ℝ → X → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set X))) (i : ℕ)
    {t : ℝ} (ht : t ∈ Icc c d) (x : X) :
    activeTimeJet c d i f t x = activeTimeJet a b i f t x := by
  induction i generalizing t with
  | zero => rw [activeTimeJet_zero, activeTimeJet_zero]
  | succ i ih =>
    simp only [iteratedDerivWithin_succ, activeTimeJet]
    refine (derivWithin_congr (fun r hr => ih hr) (ih ht)).trans ?_
    have h := (activeTimeJet_timeSlice (activeTimeJet_smooth hab hf i) x).differentiableOn
      (by simp) t (hsub ht)
    exact (h.hasDerivWithinAt.mono hsub).derivWithin (uniqueDiffOn_Icc hcd t ht)

/-- Binomial time Leibniz and the radius-scaled spatial product bound. The
constants can depend on the time slice, so a weight on one input survives
untouched after differentiation. -/
theorem activeTimeJet_bilinear_phaseJetBound (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) {f : ℝ → X → E} {g : ℝ → X → F}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set X)))
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc a b ×ˢ (univ : Set X)))
    (i n : ℕ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hF : ∀ j ≤ i, PhaseJetBound n A (activeTimeJet a b j f t))
    (hG : ∀ j ≤ i, PhaseJetBound n C (activeTimeJet a b j g t)) :
    PhaseJetBound n ((2 : ℝ) ^ i * ((2 : ℝ) ^ n * (A * C)))
      (activeTimeJet a b i (fun u x => B (f u x) (g u x)) t) := by
  intro m hm x
  let term (j : ℕ) (y : X) := B (activeTimeJet a b j f t y) (activeTimeJet a b (i - j) g t y)
  have hEq : activeTimeJet a b i (fun u x => B (f u x) (g u x)) t =
      fun y => ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) • term j y := by
    funext y
    simp only [term, Nat.cast_smul_eq_nsmul]
    exact iteratedDerivWithin_bilinear B (uniqueDiffOn_Icc hab) ht
      (activeTimeJet_timeSlice hf y) (activeTimeJet_timeSlice hg y) i
  have hreg (j : ℕ) : ContDiff ℝ ∞ (term j) :=
    (B.contDiff.comp (activeTimeJet_sliceSmooth hab hf j ht)).clm_apply
      (activeTimeJet_sliceSmooth hab hg (i-j) ht)
  have hnorm (j : ℕ) (hj : j ∈ Finset.range (i + 1)) :
      ‖iteratedFDeriv ℝ m (term j) x‖ ≤ (2 : ℝ) ^ n * (A * C) :=
    phaseJetBound_bilinear_product B hB (activeTimeJet_sliceSmooth hab hf j ht)
      (activeTimeJet_sliceSmooth hab hg (i-j) ht) hA hC
      (hF j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) (hG (i-j) (Nat.sub_le _ _)) m hm x
  rw [hEq, iteratedFDeriv_fun_sum_apply fun j _ =>
    ((hreg j).const_smul _).contDiffAt.of_le (by simp)]
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1),
        ‖iteratedFDeriv ℝ m (fun y => (i.choose j : ℝ) • term j y) x‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ((2 : ℝ) ^ n * (A * C)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [iteratedFDeriv_const_smul_apply' ((hreg j).contDiffAt.of_le (by simp)),
        norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hnorm j hj) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose i

private theorem norm_applyField_bilinear_le :
    ‖(ContinuousLinearMap.apply ℝ E : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] E).flip‖ ≤ (1 : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
  rw [one_mul]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (fun x => A.le_opNorm x)

/-- A homogeneous amplitude equation gives all prescribed time jets
from its zeroth time bounds and the coefficient jets. -/
theorem activeTimeJet_homogeneous_phaseJetBound {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    {f : ℝ → X → E} {A : ℝ → X → E →L[ℝ] E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set X)))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc a b ×ˢ (univ : Set X)))
    (hODE : ∀ u ∈ Icc a b, ∀ x, HasDerivWithinAt (fun r => f r x) (A u x (f u x)) (Icc a b) u)
    (q n : ℕ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAc : ∀ j ≤ q, PhaseJetBound n B (activeTimeJet a b j A t))
    (hfc : PhaseJetBound n C (f t)) :
    ∀ i ≤ q, PhaseJetBound n (C * (1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * B) ^ i)
      (activeTimeJet a b i f t) := by
  let growth := 1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * B
  have hGrowth : 1 ≤ growth := by dsimp only [growth]; linarith only [show 0 ≤ (2 : ℝ) ^ q * (2 : ℝ) ^ n * B by positivity]
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    cases i with
    | zero => simpa only [activeTimeJet_zero, pow_zero, mul_one] using hfc
    | succ i =>
      have hEq : activeTimeJet a b (i + 1) f t =
          activeTimeJet a b i (fun u x => A u x (f u x)) t := by
        funext x
        rw [activeTimeJet, iteratedDerivWithin_succ']
        exact iteratedDerivWithin_congr (fun u hu => (hODE u hu x).derivWithin
          (uniqueDiffOn_Icc hab u hu)) ht
      rw [hEq]
      have hprod := activeTimeJet_bilinear_phaseJetBound (ContinuousLinearMap.apply ℝ E).flip
        norm_applyField_bilinear_le hab ht hA hf i n hB (show 0 ≤ C * growth ^ i by positivity)
        (fun j hj => hAc j (hj.trans (Nat.le_of_succ_le hi))) ?_
      · intro m hm x
        refine (hprod m hm x).trans ?_
        change (2 : ℝ) ^ i * ((2 : ℝ) ^ n * (B * (C * growth ^ i))) ≤ C * growth ^ (i+1)
        rw [pow_succ]
        calc
          _ = (C * growth ^ i) * ((2 : ℝ) ^ i * (2 : ℝ) ^ n * B) := by ring
          _ ≤ (C * growth ^ i) * ((2 : ℝ) ^ q * (2 : ℝ) ^ n * B) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (pow_le_pow_right₀ (by norm_num) (Nat.le_of_succ_le hi)) (by positivity)) hB)
              (by positivity)
          _ ≤ (C * growth ^ i) * growth :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
          _ = _ := mul_assoc _ _ _
      · intro j hj m hm x
        exact (ih j (Nat.lt_succ_iff.mpr hj) (hj.trans (Nat.le_of_succ_le hi)) m hm x).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hGrowth hj) hC)

end

namespace HierarchyTwistedProfile

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T t₀ ell h : ℝ} {k : Vec3}

/-- Transfer fixed-label active-slab time jets through the exact wrapping
on the centered cell, then sum with the factorial time weights. -/
theorem timeJetSeminorm_le_of_activeCellJets (hT : 0 < T) (ht₀ : 0 ≤ t₀) (htT : t₀ < T)
    (hell : ell ≠ 0) (hh : h ≠ 0) (f : HierarchyTwistedProfile T k E)
    (raw : ℝ → Vec3 → ℝ → E)
    (hRaw : ContDiffOn ℝ ∞ (fun z : HierarchyProfilePoint => raw z.1 z.2.1 z.2.2)
      (Icc t₀ T ×ˢ (univ : Set (Vec3 × ℝ))))
    (hCell : ∀ t ∈ Icc t₀ T, ∀ a ∈ centeredCell, ∀ s,
      f.val.val.val (t, a, s) = raw t a s)
    (n q : ℕ) {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T))
    (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t) {B : ℝ} (hB : 0 ≤ B)
    (hJets : ∀ i ≤ q, ∀ t ∈ Icc t₀ T,
      PhaseJetBound n (γ t * B) (activeTimeJet t₀ T i (fun u => scaledPhaseProfile ell h (raw u)) t)) :
    timeJetSeminorm hT q (amplitudeSeminorm False ell h n hT ht₀ htT.le γ hγ hpos) f ≤
      (∑ i ∈ Finset.range (q + 1), terminalTimeJetWeight T i) *
        ((hierarchyAdmissibleWords (Fin 4) n).card : ℝ) * B := by
  let F (t : ℝ) (x : Vec3 × ℝ) := f.val.val.val (t, x)
  let R (t : ℝ) (x : Vec3 × ℝ) := raw t x.1 x.2
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set (Vec3 × ℝ))) :=
    HierarchySmoothProfile.smooth f.val.val
  have hsmall : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hC (i : ℕ) (hi : i ≤ q) :
      amplitudeSeminorm False ell h n hT ht₀ htT.le γ hγ hpos (timeJet hT i f) ≤
        ((hierarchyAdmissibleWords (Fin 4) n).card : ℝ) * B := by
    apply amplitudeSeminorm_le_of_scaledJetBound hT ht₀ htT.le hγ hpos hell hh hB
    intro t ht
    let g (a : Vec3) (s : ℝ) := activeTimeJet t₀ T i R t (a,s)
    have hreg : ContDiff ℝ ∞ (Function.uncurry g) := activeTimeJet_sliceSmooth htT hRaw i ht
    have heq (a : Vec3) (ha : a ∈ centeredCell) (s : ℝ) :
        (timeJet hT i f).val.val.val (t, a, s) = g a s := by
      rw [timeJet_apply hT i f (hsmall ht) (a,s)]
      change activeTimeJet 0 T i F t (a,s) = activeTimeJet t₀ T i R t (a,s)
      rw [← activeTimeJet_eq_of_subset hT htT hsmall hF i ht (a,s)]
      exact iteratedDerivWithin_congr (fun u hu => hCell u hu a ha s) ht
    exact phaseJetBound_of_centeredCell (hsmall ht) hell hh hreg heq (hJets i hi t ht)
  rw [timeJetSeminorm_apply, mul_assoc, Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
    (hC i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) (terminalTimeJetWeight_pos hT i).le

end HierarchyTwistedProfile

section Leading

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem activeTimeJet_phaseProduct {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    {f : ℝ → Vec3 → E} (hf : ContDiffOn ℝ ∞ (Function.uncurry f)
      (Icc a b ×ˢ (univ : Set Vec3))) {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i n : ℕ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfJ : PhaseJetBound n A (activeTimeJet a b i f t)) (hφJ : PhaseJetBound n C φ) :
    PhaseJetBound n ((2 : ℝ) ^ n * (C * A))
      (activeTimeJet a b i (fun u p => φ p • f u p.1) t) := by
  let L : Vec3 × ℝ →L[ℝ] Vec3 := ContinuousLinearMap.fst ℝ Vec3 ℝ
  have hEq : activeTimeJet a b i (fun u p => φ p • f u p.1) t =
      fun p => φ p • activeTimeJet a b i f t (L p) := by
    funext p
    exact iteratedDerivWithin_fun_const_smul_field (φ p) (fun u => f u p.1)
  have hReg := activeTimeJet_sliceSmooth hab hf i ht
  have hLift : PhaseJetBound n A (activeTimeJet a b i f t ∘ L) := by
    intro j hj p
    rw [L.iteratedFDeriv_comp_right hReg p (by simp)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (activeTimeJet a b i f t) (L p)‖ * ‖L‖ ^ j := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (iteratedFDeriv ℝ j (activeTimeJet a b i f t) (L p)).norm_compContinuousLinearMap_le
            (fun _ => L)
      _ ≤ _ := (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ..))).trans (hfJ j hj (L p))
  rw [hEq]
  exact phaseJetBound_bilinear_product (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    ContinuousLinearMap.opNorm_lsmul_le hφ (hReg.comp L.contDiff) hC hA hφJ hLift

private theorem phaseJetBound_constant_of_norm_le {A : ℝ} {c : E} (hc : ‖c‖ ≤ A) (n : ℕ) :
    PhaseJetBound n A (fun _ : Vec3 => c) := by
  intro m _ x
  cases m with
  | zero => simpa using hc
  | succ m =>
    rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m)]
    simpa using (norm_nonneg c).trans hc

end Leading

namespace LocalizedAmplitude.SeedOn

noncomputable section

variable {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
  {center : ℝ → Vec3} {t₀ T ell D C r h : ℝ}

/-- The actual radius-scaled slow amplitude. Its time equation has the
same generator as the physical amplitude because the envelope is fixed. -/
def scaledEnvelopedAmplitude (w : SeedOn M κ center t₀ T ell D C) (t : ℝ) (x : Vec3) : Vec3 :=
  radialEnvelope ell (ell • x) • w.amplitude t (ell • x)

private theorem scaledEnvelopedAmplitude_smooth {w : SeedOn M κ center t₀ T ell D C}
    (d : w.HierarchyRegularity r h) :
    ContDiffOn ℝ ∞ (Function.uncurry w.scaledEnvelopedAmplitude)
      (Icc t₀ T ×ˢ (univ : Set Vec3)) := by
  let F (z : ℝ × Vec3) := (z.1, ell • z.2)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk (contDiff_snd.const_smul ell)
  have hMaps : MapsTo F (Icc t₀ T ×ˢ (univ : Set Vec3)) (Icc t₀ T ×ˢ (univ : Set Vec3)) :=
    fun z hz => ⟨hz.1, mem_univ (ell • z.2)⟩
  have hA := d.amplitude_smooth.comp hF.contDiffOn hMaps
  exact ((contDiff_radialEnvelope d.envelope_pos).comp (contDiff_snd.const_smul ell)).contDiffOn.smul hA

private theorem scaledEnvelopedAmplitude_ode (w : SeedOn M κ center t₀ T ell D C)
    {t : ℝ} (ht : t ∈ Icc t₀ T) (x : Vec3) :
    HasDerivWithinAt (fun u => w.scaledEnvelopedAmplitude u x)
      (affineWaveAmplitudeOperator (M t (ell • x)) (κ t (ell • x)) (w.scaledEnvelopedAmplitude t x))
      (Icc t₀ T) t := by
  have hs := (w.equation (ell • x) t ht).const_smul (radialEnvelope ell (ell • x))
  change HasDerivWithinAt (fun u => radialEnvelope ell (ell • x) • w.amplitude u (ell • x)) _ _ _ at hs
  change HasDerivWithinAt (fun u => radialEnvelope ell (ell • x) • w.amplitude u (ell • x)) _ _ _
  rw [scaledEnvelopedAmplitude, map_smul]
  exact hs

/-- The weighted radius and phase jets of the exact unwrapped leading
velocity and carrier-normalized pressure, with any smooth time multiplier.
Taking the multiplier to be the switch or its derivative recovers the
later leading wave and its activation source. -/
theorem exists_activeScaledLeading_timeJetBounds (n : ℕ) :
    ∃ Eφ : ℝ, 1 ≤ Eφ ∧
    ∀ {t₀ T ell D C r freq : ℝ} {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
      {center : ℝ → Vec3} {w : SeedOn M κ center t₀ T ell D C}
      (_hf : 1 ≤ freq) (_d : w.HierarchyRegularity r (freq ^ (-1 / 2 : ℝ)))
      (q : ℕ) {t : ℝ} (_ht : t ∈ Icc t₀ T) {χ : ℝ → ℝ} (_hχ : ContDiff ℝ ∞ χ)
      {Bamp Bgen Bpre Bχ : ℝ} (_hAmp : 0 ≤ Bamp) (_hGen : 0 ≤ Bgen) (_hPre : 0 ≤ Bpre)
      (_hBχ : 0 ≤ Bχ),
      let gen (u : ℝ) (x : Vec3) := affineWaveAmplitudeOperator (M u (ell • x)) (κ u (ell • x))
      let pre (u : ℝ) (x : Vec3) :=
        hierarchyRelayPressureAmplitudeCoefficient (M u (ell • x)) (freq⁻¹ • κ u (ell • x))
      let hh := freq ^ (-1 / 2 : ℝ)
      let γ := freq ^ (3 / 4 : ℝ) * ‖center t‖
      let V := Eφ * (2 : ℝ) ^ (q + 2*n) * Bχ * Bamp * (1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * Bgen) ^ q
      let P := (2 : ℝ) ^ (q+n) * Bpre * V
      ContDiffOn ℝ ∞ (Function.uncurry gen) (Icc t₀ T ×ˢ (univ : Set Vec3)) →
      ContDiffOn ℝ ∞ (Function.uncurry pre) (Icc t₀ T ×ˢ (univ : Set Vec3)) →
      (∀ i ≤ q, PhaseJetBound n Bgen (activeTimeJet t₀ T i gen t)) →
      (∀ i ≤ q, PhaseJetBound n Bpre (activeTimeJet t₀ T i pre t)) →
      (∀ i ≤ q, ‖iteratedDeriv i χ t‖ ≤ Bχ) →
      PhaseJetBound n (‖center t‖ * Bamp) (w.scaledEnvelopedAmplitude t) →
      ∀ i ≤ q, PhaseJetBound n (γ * (V * freq ^ (-5 / 4 : ℝ)))
        (activeTimeJet t₀ T i (fun u =>
          scaledPhaseProfile ell hh (fun a s => χ u • w.leading hh u a s)) t) ∧
      PhaseJetBound n (γ * (P * freq ^ (-5 / 4 : ℝ)))
        (activeTimeJet t₀ T i (fun u =>
          scaledPhaseProfile ell hh (fun a s => freq * (χ u * w.leadingPressure hh u a s))) t) := by
  obtain ⟨Eφ, hEφ, hPhase⟩ := exists_scaled_wavePhaseJetBounds n
  refine ⟨Eφ, hEφ, ?_⟩
  intro t₀ T ell D C r freq M κ center w hf d q t ht χ hχ Bamp Bgen Bpre Bχ hAmp hGen hPre hBχ
    gen pre hh γ V P hGens hPres hGensJ hPresJ hχJ hAmpJ i hi
  let A := w.scaledEnvelopedAmplitude
  let Amp := ‖center t‖ * Bamp * (1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * Bgen) ^ q
  let switched (u : ℝ) (x : Vec3) := χ u • A u x
  let press (u : ℝ) (x : Vec3) := pre u x (switched u x)
  let Vlabel := (2 : ℝ) ^ q * ((2 : ℝ) ^ n * (Bχ * Amp))
  let Plabel := (2 : ℝ) ^ q * ((2 : ℝ) ^ n * (Bpre * Vlabel))
  let I := Icc t₀ T
  let J := I ×ˢ (univ : Set Vec3)
  have hAreg : ContDiffOn ℝ ∞ (Function.uncurry A) J := scaledEnvelopedAmplitude_smooth d
  have hχreg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => χ z.1) J := (hχ.comp contDiff_fst).contDiffOn
  have hVreg : ContDiffOn ℝ ∞ (Function.uncurry switched) J := hχreg.smul hAreg
  have hPreg : ContDiffOn ℝ ∞ (Function.uncurry press) J := hPres.clm_apply hVreg
  have hAmp₀ : 0 ≤ Amp := by dsimp only [Amp]; positivity
  have hVlabel : 0 ≤ Vlabel := by dsimp only [Vlabel]; positivity
  have hPlabel : 0 ≤ Plabel := by dsimp only [Plabel]; positivity
  have hF : ∀ j ≤ q, PhaseJetBound n Amp (activeTimeJet t₀ T j A t) := by
    intro j hj m hm x
    have base := activeTimeJet_homogeneous_phaseJetBound d.start_lt_end ht hAreg hGens
      (fun _ hu x => scaledEnvelopedAmplitude_ode w hu x) q n hGen (mul_nonneg (norm_nonneg _) hAmp)
      hGensJ hAmpJ j hj m hm x
    refine base.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ?_ hj) (by positivity))
    exact le_add_of_nonneg_right (by positivity)
  have hS : ∀ j ≤ q, PhaseJetBound n Bχ (activeTimeJet t₀ T j (fun u (_ : Vec3) => χ u) t) := by
    intro j hj
    have heq : activeTimeJet t₀ T j (fun u (_ : Vec3) => χ u) t =
        fun _ => iteratedDeriv j χ t := by
      funext _x
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc d.start_lt_end)
        (hχ.contDiffAt.of_le (by simp)) ht
    rw [heq]
    exact phaseJetBound_constant_of_norm_le (hχJ j hj) n
  have hVJ (j : ℕ) (hj : j ≤ q) : PhaseJetBound n Vlabel (activeTimeJet t₀ T j switched t) := by
    intro m hm x
    have h := activeTimeJet_bilinear_phaseJetBound (ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] Vec3 →L[ℝ] Vec3) ContinuousLinearMap.opNorm_lsmul_le d.start_lt_end ht
      hχreg hAreg j n hBχ hAmp₀ (fun p hp => hS p (hp.trans hj)) (fun p hp => hF p (hp.trans hj))
    exact (h m hm x).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hj) (by positivity))
  have hPJ : PhaseJetBound n Plabel (activeTimeJet t₀ T i press t) := by
    intro m hm x
    have h := activeTimeJet_bilinear_phaseJetBound
      (ContinuousLinearMap.apply ℝ ℝ : Vec3 →L[ℝ] (Vec3 →L[ℝ] ℝ) →L[ℝ] ℝ).flip
      (by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
        rw [one_mul]
        exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) (fun x => L.le_opNorm x))
      d.start_lt_end ht hPres hVreg i n hPre hVlabel
      (fun j hj => hPresJ j (hj.trans hi)) (fun j hj => hVJ j (hj.trans hi))
    exact (h m hm x).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hi) (by positivity))
  obtain ⟨hW, hQ⟩ := hPhase hh d.phase_pos d.phase_le_one
  let wave (p : Vec3 × ℝ) := waveProfile hh (hh * p.2)
  let primitive (p : Vec3 × ℝ) := wavePressurePrimitive hh (hh * p.2)
  have hWreg : ContDiff ℝ ∞ wave := (contDiff_waveProfile d.phase_pos d.phase_le_one).comp
    (contDiff_const.mul contDiff_snd)
  have hQreg : ContDiff ℝ ∞ primitive := (contDiff_wavePressurePrimitive d.phase_pos d.phase_le_one).comp
    (contDiff_const.mul contDiff_snd)
  have heV : (fun u => scaledPhaseProfile ell hh (fun a s => χ u • w.leading hh u a s)) =
      (fun u p => wave p • switched u p.1) := by
    funext u p
    simp only [scaledPhaseProfile, Function.comp_def, labelPhaseScale_apply, Function.uncurry_apply_pair,
      SeedOn.leading, scaledEnvelopedAmplitude, switched, A, wave, smul_smul]
    congr 1
    ring
  have heP : (fun u => scaledPhaseProfile ell hh (fun a s => freq * (χ u * w.leadingPressure hh u a s))) =
      (fun u p => primitive p • press u p.1) := by
    funext u p
    simp only [scaledPhaseProfile, Function.comp_def, labelPhaseScale_apply, Function.uncurry_apply_pair,
      SeedOn.leadingPressure, scaledEnvelopedAmplitude, press, pre, switched, A, primitive,
      map_smul, smul_eq_mul]
    have hcoef := normalizedPressureAmplitudeCoefficient_apply_leading (zero_lt_one.trans_le hf)
      (M u (ell • p.1)) (κ u (ell • p.1)) (w.amplitude u (ell • p.1)) 1
    rw [one_smul] at hcoef
    rw [hcoef]
    simp only [wavePressureCoefficient, mul_one, div_eq_mul_inv]
    ring
  have hGain : hh * ‖center t‖ = γ * freq ^ (-5 / 4 : ℝ) := by
    have h := (profileWidth_and_seedScale hf).2
    dsimp only [γ]
    calc
      _ = (freq ^ (-3 / 4 : ℝ) * hh) * (freq ^ (3 / 4 : ℝ) * ‖center t‖) := by
        have hprod : freq ^ (-3 / 4 : ℝ) * freq ^ (3 / 4 : ℝ) = 1 := by
          rw [← Real.rpow_add (zero_lt_one.trans_le hf)]
          norm_num
        calc
          _ = (freq ^ (-3 / 4 : ℝ) * freq ^ (3 / 4 : ℝ)) * (hh * ‖center t‖) := by rw [hprod, one_mul]
          _ = _ := by ring
      _ = _ := by rw [h]; ring
  have hEV : (2 : ℝ) ^ n * ((Eφ * hh) * Vlabel) = γ * (V * freq ^ (-5 / 4 : ℝ)) := by
    dsimp only [Vlabel, Amp, V]
    rw [pow_add, pow_mul]
    calc
      _ = (hh * ‖center t‖) * (Eφ * (2 : ℝ) ^ q * ((2 : ℝ) ^ 2) ^ n * Bχ * Bamp *
          (1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * Bgen) ^ q) := by rw [← pow_mul, Nat.mul_comm, pow_mul]; ring
      _ = _ := by rw [hGain]; ring
  have hEP : (2 : ℝ) ^ n * ((Eφ * hh) * Plabel) = γ * (P * freq ^ (-5 / 4 : ℝ)) := by
    dsimp only [Plabel, P]
    rw [pow_add]
    calc
      _ = ((2 : ℝ) ^ n * ((Eφ * hh) * Vlabel)) * ((2 : ℝ) ^ q * (2 : ℝ) ^ n * Bpre) := by ring
      _ = _ := by rw [hEV]; ring
  rw [heV, heP, ← hEV, ← hEP]
  exact ⟨activeTimeJet_phaseProduct d.start_lt_end ht hVreg hWreg i n hVlabel
      (mul_nonneg (zero_le_one.trans hEφ) d.phase_pos.le) (hVJ i hi) hW,
    activeTimeJet_phaseProduct d.start_lt_end ht hPreg hQreg i n hPlabel
      (mul_nonneg (zero_le_one.trans hEφ) d.phase_pos.le) hPJ hQ⟩

open HierarchyTwistedProfile

/-- The weighted time bounds for the three selected leading profiles are
the radius-scaled active-cell bounds of their exact raw time derivatives. -/
theorem twistedLeading_timeJetSeminorm_bounds {w : SeedOn M κ center t₀ T ell D C}
    (d : w.HierarchyRegularity r h) (k : Vec3) (q n : ℕ) {freq : ℝ} (hf : 0 ≤ freq)
    {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    {BV BP BS : ℝ} (hBV : 0 ≤ BV) (hBP : 0 ≤ BP) (hBS : 0 ≤ BS)
    (hV : ∀ i ≤ q, ∀ t ∈ Icc t₀ T, PhaseJetBound n (γ t * BV)
      (activeTimeJet t₀ T i (fun u => scaledPhaseProfile ell h (w.switchedLeading r h u)) t))
    (hP : ∀ i ≤ q, ∀ t ∈ Icc t₀ T, PhaseJetBound n (γ t * BP)
      (activeTimeJet t₀ T i (fun u =>
        scaledPhaseProfile ell h (fun a s => freq * w.switchedPressure r h u a s)) t))
    (hS : ∀ i ≤ q, ∀ t ∈ Icc t₀ T, PhaseJetBound n (γ t * BS)
      (activeTimeJet t₀ T i (fun u => scaledPhaseProfile ell h (w.leadingSwitchProfile r h u)) t)) :
    let V := timeJetSeminorm d.end_pos q (amplitudeSeminorm False ell h n d.end_pos
      d.nonneg_start d.start_lt_end.le γ hγ hpos) (w.twistedLeading d k)
    let P := timeJetSeminorm d.end_pos q (amplitudeSeminorm False ell h n d.end_pos
      d.nonneg_start d.start_lt_end.le γ hγ hpos) (w.twistedPressure d k)
    let S := timeJetSeminorm d.end_pos q (amplitudeSeminorm False ell h n d.end_pos
      d.nonneg_start d.start_lt_end.le γ hγ hpos) (w.twistedLeadingSwitch d k)
    let C := (∑ i ∈ Finset.range (q + 1), terminalTimeJetWeight T i) *
      ((hierarchyAdmissibleWords (Fin 4) n).card : ℝ)
    V ≤ C * BV ∧ freq * P ≤ C * BP ∧ S ≤ C * BS := by
  intro V P S C
  let I := Icc t₀ T
  let J := I ×ˢ (univ : Set (Vec3 × ℝ))
  have hsub : J ⊆ Iic T ×ˢ (univ : Set (Vec3 × ℝ)) :=
    prod_mono (fun _ ht => ht.2) subset_rfl
  have hVreg := (w.contDiffOn_switchedLeading d.start_lt_end d.rate_nonneg d.envelope_pos
    d.phase_pos d.phase_le_one d.amplitude_smooth).mono hsub
  have hPreg := (w.contDiffOn_switchedPressure d.start_lt_end d.rate_nonneg d.envelope_pos
    d.phase_pos d.phase_le_one d.strain_smooth d.covector_smooth d.covector_nonzero d.amplitude_smooth).mono hsub
  have hSwitch : ContDiff ℝ ∞ (deriv (waveSwitch t₀ r)) := by
    apply ContDiff.deriv'
    simpa using contDiff_waveSwitch t₀ r
  have hSreg : ContDiffOn ℝ ∞ (fun z : HierarchyProfilePoint =>
      w.leadingSwitchProfile r h z.1 z.2.1 z.2.2) J :=
    (hSwitch.comp contDiff_fst).contDiffOn.smul
      (w.contDiffOn_leading d.envelope_pos d.phase_pos d.phase_le_one d.amplitude_smooth)
  have hCellV (t : ℝ) (ht : t ∈ I) (a : Vec3) (ha : a ∈ centeredCell) (s : ℝ) :
      (w.twistedLeading d k).val.val.val (t,a,s) = w.switchedLeading r h t a s :=
    w.twistedLeading_cell_eval d k ⟨d.nonneg_start.trans ht.1, ht.2⟩ ha s
  have hCellP (t : ℝ) (ht : t ∈ I) (a : Vec3) (ha : a ∈ centeredCell) (s : ℝ) :
      (freq • w.twistedPressure d k).val.val.val (t,a,s) = freq * w.switchedPressure r h t a s := by
    change freq * (w.twistedPressure d k).val.val.val (t,a,s) = _
    rw [w.twistedPressure_cell_eval d k ⟨d.nonneg_start.trans ht.1, ht.2⟩ ha s]
  have hCellS (t : ℝ) (ht : t ∈ I) (a : Vec3) (ha : a ∈ centeredCell) (s : ℝ) :
      (w.twistedLeadingSwitch d k).val.val.val (t,a,s) = w.leadingSwitchProfile r h t a s :=
    w.twistedLeadingSwitch_cell_eval d k ⟨d.nonneg_start.trans ht.1, ht.2⟩ ha s
  have hVP := timeJetSeminorm_le_of_activeCellJets d.end_pos d.nonneg_start d.start_lt_end
    d.envelope_pos.ne' d.phase_pos.ne' (w.twistedLeading d k) (w.switchedLeading r h)
    hVreg hCellV n q hγ hpos hBV hV
  have hPP := timeJetSeminorm_le_of_activeCellJets d.end_pos d.nonneg_start d.start_lt_end
    d.envelope_pos.ne' d.phase_pos.ne' (freq • w.twistedPressure d k)
    (fun t a s => freq * w.switchedPressure r h t a s) (contDiffOn_const.mul hPreg)
    hCellP n q hγ hpos hBP hP
  have hSP := timeJetSeminorm_le_of_activeCellJets d.end_pos d.nonneg_start d.start_lt_end
    d.envelope_pos.ne' d.phase_pos.ne' (w.twistedLeadingSwitch d k) (w.leadingSwitchProfile r h)
    hSreg hCellS n q hγ hpos hBS hS
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hf] at hPP
  exact ⟨hVP, hPP, hSP⟩

end

end LocalizedAmplitude.SeedOn

namespace TerminalMixedJetBound

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed spatial slope of a mixed jet estimate is absorbed by the
localized radius, with the time-order prefactor unchanged. -/
theorem scaledActiveTimeJet_phaseJetBound {T t₀ : ℝ} {q p e : ℕ} {D ell : ℝ}
    {C : ℕ → ℝ} {f : ℝ → Vec3 → E}
    (hT : 0 < T) (ht₀ : 0 ≤ t₀) (htT : t₀ < T) (hD : 1 ≤ D) (hEll : 0 ≤ ell)
    (hscale : ell * D ^ p ≤ 1) (hC : ∀ n, 0 ≤ C n)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (H : TerminalMixedJetBound 0 T q p D (D ^ e) C f) (n : ℕ)
    {i : ℕ} (hi : i ≤ q) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    PhaseJetBound n ((∑ m ∈ Finset.range (n + 1), C m) * D ^ e)
      (activeTimeJet t₀ T i (fun t y => f t (ell • y)) t) := by
  have hs : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hderiv : activeTimeJet t₀ T i (fun u y => f u (ell • y)) t =
      fun y => slabTimeJet 0 T i f t (ell • y) :=
    funext fun y => activeTimeJet_eq_of_subset hT htT hs hf i ht (ell • y)
  intro m hm x
  rw [hderiv]
  have hjet : ‖iteratedFDeriv ℝ m (slabTimeJet 0 T i f t) (ell • x)‖ ≤
      C m * D ^ (p * m + e) := by
    simpa only [pow_add, mul_assoc, mul_comm (D ^ e)] using H i hi m t (hs ht) (ell • x)
  refine ((norm_iteratedFDeriv_scaledLabel_power_le
    (slabTimeJet_slice_smooth hT hf i (hs ht)) hD hEll hscale (hC m) m x hjet).1).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := C) (fun j _ => hC j)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hm))) (pow_nonneg (zero_le_one.trans hD) _)

end TerminalMixedJetBound

namespace InductiveEulerTip.SelectedLaterInput

open LocalizedAmplitude

/-- The actual future wave has the required zeroth-time weight after
rescaling the envelope label. The radius threshold works at all orders. -/
theorem exists_scaledEnvelopedAmplitudeCost :
    ∃ (A : ℕ) (cost : ℕ → ℝ), 30 ≤ A ∧ (∀ m, 1 ≤ cost m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {tip : InductiveEulerTip P n}
        {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a), A ≤ a → ∀ m : ℕ,
        ∀ t ∈ Icc tip.nextActivation (P.slab (n + 2) tip.nextActivation),
          PhaseJetBound m (‖d.selection.crossing.amplitude t‖ *
            (cost m * (P.frequency (n + 1) ^ (9 : ℕ)) ^ (13 : ℕ))) (d.seed.scaledEnvelopedAmplitude t) := by
  obtain ⟨W, hW, hJets⟩ := InductiveEulerStage.exists_velocity_jet_bounds
  obtain ⟨A, hA, hSeedAll⟩ := exists_parent_seed_leadingAndSlowJetBounds W hW
  choose K cost L hK hCost hL hSeed using hSeedAll
  refine ⟨A, cost, hA, hCost, ?_⟩
  intro P n tip Cenv a d ha m t ht
  let T := P.slab (n + 2) tip.nextActivation
  let D := P.frequency (n + 1) ^ (9 : ℕ)
  have hParentOne : 1 ≤ P.frequency (n + 1) := one_le_two.trans d.parent_frequency_ge_two
  have hF (u : ℝ) (hu : u ∈ Icc 0 T) (x : Vec3) : ‖fderiv ℝ (tip.parent.flow 0 u) x‖ ≤ D :=
    ((d.parent.deformationOn.bounds u hu).2.1 x).2.trans d.parent_frequency_le_scale
  have hG (u : ℝ) (hu : u ∈ Icc 0 T) (x : Vec3) :
      ‖fderiv ℝ (tip.parent.flow u 0) (tip.parent.flow 0 u x)‖ ≤ D :=
    ((d.parent.deformationOn.bounds u hu).2.2 (tip.parent.flow 0 u x)).2.trans d.parent_frequency_le_scale
  have h := hSeed m tip.next_activation_nonnegative d.regularity.start_lt_end d.time_le_one
    d.parent_scale_ge_two d.regularity.envelope_pos (d.radius_le_inverse_power ha)
    d.child_frequency_ge_one d.label_launch_covector_norm d.parent.deformationOn.flow
    d.parent.smooth_velocity (fun u _ => tip.parent.periodic_velocity u) hF hG
    (fun q j hj hq u hu x => hJets tip.parent hParentOne q j hj hq u (d.parent.subset hu) x)
    d.centerWaveOn_labels d.seed (χ := 1) (by norm_num) t ht
  change PhaseJetBound m (‖d.selection.crossing.amplitude t‖ * (cost m * D ^ (13 : ℕ)))
    (fun x => radialEnvelope d.radius (d.radius • x) • d.seed.amplitude t (d.radius • x))
  simpa only [mul_comm ‖d.selection.crossing.amplitude t‖] using h.2.1

open HierarchyTwistedProfile

private theorem deriv_waveSwitch_zero_off_ramp {t₀ r t : ℝ} (hr : 0 < r)
    (ht : t ∉ Icc t₀ (t₀ + 1 / r)) : deriv (waveSwitch t₀ r) t = 0 := by
  by_cases hlt : t < t₀
  · refine ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_).deriv
    filter_upwards [Iio_mem_nhds hlt] with u hu
    exact waveSwitch_eq_zero_of_le hr.le hu.le
  · have hgt : t₀ + 1 / r < t := lt_of_not_ge fun hu => ht ⟨le_of_not_gt hlt, hu⟩
    refine ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq ?_).deriv
    filter_upwards [Ioi_mem_nhds hgt] with u hu
    exact waveSwitch_eq_one_of_activation hr hu.le

variable {P : InductiveEulerParameters} {j : ℕ} {tip : InductiveEulerTip P j}
  {Cenv : ℝ} {a : ℕ}

/-- The activation ramp on the actual closed stage. -/
def activationRamp (d : tip.SelectedLaterInput Cenv a) : Set ℝ :=
  Icc tip.nextActivation (min (P.slab (j + 2) tip.nextActivation)
    (tip.nextActivation + 1 / d.window.physical.rate))

theorem activationRamp_isClosed (d : tip.SelectedLaterInput Cenv a) : IsClosed d.activationRamp :=
  isClosed_Icc

theorem activationRamp_subset_active (d : tip.SelectedLaterInput Cenv a) :
    d.activationRamp ⊆ Icc tip.nextActivation (P.slab (j + 2) tip.nextActivation) :=
  fun _ ht => ⟨ht.1, ht.2.trans (min_le_left _ _)⟩

/-- Both exact activation sources vanish off the same time ramp. The
completion retains the scalar switch derivative. -/
theorem activationSwitch_zero_off_ramp (d : tip.SelectedLaterInput Cenv a)
    {t : ℝ} (ht : t ∈ Icc 0 (P.slab (j + 2) tip.nextActivation)) (hOff : t ∉ d.activationRamp)
    (x : Vec3 × ℝ) :
    (d.approximation.leading.leadingSwitch + d.approximation.leading.completionSwitch).val.val.val
      (t, x) = 0 := by
  obtain ⟨y, s⟩ := x
  have hR : t ∉ Icc tip.nextActivation (tip.nextActivation + 1 / d.window.physical.rate) := by
    intro hr
    exact hOff ⟨hr.1, le_min ht.2 hr.2⟩
  have hz := deriv_waveSwitch_zero_off_ramp d.window.physical.rate_pos hR
  change (d.seed.twistedLeadingSwitch d.regularity d.carrier).val.val.val (t,y,s) +
    (d.seed.twistedCompletionSwitch d.regularity d.parent.geometry.inverse d.parent.geometry.covector
      d.parent.geometry.oscillation.covector_independent
      d.parent.geometry.oscillation.covector_ne_zero).val.val.val (t,y,s) = 0
  rw [d.seed.twistedLeadingSwitch_eval d.regularity d.carrier ht,
    d.seed.twistedCompletionSwitch_eval d.regularity d.parent.geometry.inverse d.parent.geometry.covector
      d.parent.geometry.oscillation.covector_independent
      d.parent.geometry.oscillation.covector_ne_zero d.parent.geometry.covector_value ht]
  simp only [phaseTwistedPeriodizeCentered, SeedOn.leadingSwitchProfile, hz, zero_smul, zero_add]

/-- The leading pressure stays phase normalized at every time order. -/
theorem leadingPressure_timeJet_phaseMean_zero (d : tip.SelectedLaterInput Cenv a) (i : ℕ)
    (t : ℝ) (ht : t ∈ Icc 0 (P.slab (j + 2) tip.nextActivation)) (x : Vec3) :
    phaseMean (fun s => (timeJet d.time_pos i d.leading.output.p).val.val.val (t,x,s)) = 0 := by
  exact phaseMean_timeJet_eq_zero d.time_pos d.leading.output.p
    (fun u hu y => d.seed.twistedPressure_phaseMean_zero d.regularity d.carrier hu y) i t ht x

end InductiveEulerTip.SelectedLaterInput

end TorusEuler
