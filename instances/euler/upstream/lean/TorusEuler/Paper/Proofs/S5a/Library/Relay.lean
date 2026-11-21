import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.SBD.Statements

/-!
# S5a library: the relay estimates of Lemma 5.5 with the primitive bound of Lemma D.1

Copies of the library estimates that prove (5.31) and (5.32)
(`TorusEuler/HierarchyLinearRelayBounds.lean`, `TorusEuler/HierarchyTwistedRelayBounds.lean`),
in which the one use of the content lemma `hierarchyFiniteWordNorm_phasePrimitive_le` of
Lemma D.1 (the primitive estimate of (D.5)) is replaced by the hypothesis
`hD : Statement.lemma_D_1` (`relayWordBound_phasePrimitive_of_D1`). The copied lemmas
`boundedWeightSeminorm_complete_le`, `boundedWeightSeminorm_waveRelay_le_of_eval` are the
content of row 5.5 itself; the other copies are private glue. Each copy records its
original; except for the threaded hypothesis `hD` and the positivity of the weights `ℓ`, `h`
that Lemma D.1 requires, statements and proofs are unchanged.

| original | copy |
|---|---|
| `contDiff_phasePrimitive_word` (private, `HierarchyLinearRelayBounds.lean:231`) | `contDiff_phasePrimitive_word` |
| `relayWordBound_bdd` (private, :408) | `relayWordBound_bdd` |
| `relayWordBound_mono` (private, :419) | `relayWordBound_mono` |
| `relayWordBound_phasePrimitive` (private, :426) | `relayWordBound_phasePrimitive_of_D1` (uses (D.5) of `hD`) |
| `relayWordBound_bilinear` (private, :439) | `relayWordBound_bilinear` |
| `relayWordBound_const_smul` (private, :514) | `relayWordBound_const_smul` |
| `relay_phaseOperatorWord_sum` (private, :524) | `relay_phaseOperatorWord_sum` |
| `relayWordBound_sum` (private, :539) | `relayWordBound_sum` |
| `relayWordBound_add` (private, :548) | `relayWordBound_add` |
| `relayWordBound_zero` (private, :1047) | `relayWordBound_zero` |
| `hierarchyRelayWordBound_linearPrimitive` (:670) | `relayWordBound_linearPrimitive_of_D1` |
| `hierarchyFiniteWordNorm_waveCompletion_le` (:718) | `waveCompletion_le_of_D1` |
| `hierarchyFiniteWordNorm_waveLinearRelay_le` (:1067) | `waveLinearRelay_le_of_D1` |
| `boundedWeightSeminorm_waveRelay_le_of_eval` (`HierarchyTwistedRelayBounds.lean:788`, 5.5 content) | `boundedWeightSeminorm_waveRelay_le_of_eval_of_D1` |
| `boundedWeightSeminorm_complete_le` (`HierarchyTwistedRelayBounds.lean:868`, 5.5 content) | `boundedWeightSeminorm_complete_le_of_D1` |
-/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile

section PrimitiveWord

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Copy of the private `contDiff_phasePrimitive_word`
(`TorusEuler/HierarchyLinearRelayBounds.lean:231`): the phase primitive of a jointly smooth
family is jointly smooth. Same proof. -/
theorem contDiff_phasePrimitive_word {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (Function.uncurry (fun a => phasePrimitive (f a))) := by
  let g (a : P) (s : ℝ) := ∫ σ in (0 : ℝ)..s, f a σ
  have hrescale : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ => f p.1.1 (p.1.2 * p.2)) :=
    hf.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))
  have h := contDiff_snd.smul
    (contDiff_and_iteratedFDeriv_phaseInterval (f := fun (p : P × ℝ) σ => f p.1 (p.2 * σ))
      hrescale 0 1).1
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    convert h using 1
    funext p
    symm
    change p.2 • (∫ σ in (0 : ℝ)..1, f p.1 (p.2 * σ)) = ∫ σ in (0 : ℝ)..p.2, f p.1 σ
    simpa only [mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (f p.1) p.2
  exact hg.sub ((contDiff_and_iteratedFDeriv_phaseInterval hg 0 1).1.comp contDiff_fst)

end PrimitiveWord

section WordBounds

variable {T : Type} {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Copy of the private `relayWordBound_bdd` (`HierarchyLinearRelayBounds.lean:408`). -/
theorem relayWordBound_bdd {ℓ h : ℝ} {n : ℕ} {B : ℝ} {f : T → Vec3 × ℝ → E}
    (hf : HierarchyRelayWordBound ℓ h n B f) :
    ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w f) := by
  intro w hw
  refine ⟨B, ?_⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hFalse, _⟩)
  · exact hf.1
  · exact hf.2 w hw t x
  · exact hFalse.elim

/-- Copy of the private `relayWordBound_mono` (`HierarchyLinearRelayBounds.lean:419`). -/
theorem relayWordBound_mono {ℓ h : ℝ} {n m : ℕ} {B C : ℝ}
    {f : T → Vec3 × ℝ → E} (hf : HierarchyRelayWordBound ℓ h n B f)
    (hm : m ≤ n) (hB : B ≤ C) : HierarchyRelayWordBound ℓ h m C f := by
  refine ⟨hf.1.trans hB, fun w hw t x => ?_⟩
  obtain ⟨hw₁, hw₂⟩ := mem_hierarchyAdmissibleWords.mp hw
  exact (hf.2 w (mem_hierarchyAdmissibleWords.mpr ⟨hw₁.trans hm, hw₂⟩) t x).trans hB

/-- The weight `γ ≡ 1` does not change a field. -/
theorem weighted_one (f : T → Vec3 × ℝ → E) : AppendixD.weighted (fun _ => (1 : ℝ)) f = f := by
  funext t x
  simp [AppendixD.weighted]

/-- **The primitive estimate (D.5) of Lemma D.1** on word bounds. Replaces the private
`relayWordBound_phasePrimitive` (`HierarchyLinearRelayBounds.lean:426`), whose proof calls the
content lemma `hierarchyFiniteWordNorm_phasePrimitive_le` of Lemma D.1: here the bound
`‖∂_s^{-1} f‖_{[n]} ≤ 2 ‖f‖_{[n]}` and the finiteness of the left side are the (D.5) clause of
`hD`, with `γ ≡ 1`. -/
theorem relayWordBound_phasePrimitive_of_D1 (hD : Statement.lemma_D_1) [CompleteSpace E]
    {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {n : ℕ} {B : ℝ} {f : T → Vec3 × ℝ → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hper : ∀ t a, Function.Periodic (fun s => f t (a,s)) 1)
    (hzero : ∀ t a, phaseMean (fun s => f t (a,s)) = 0)
    (hB : HierarchyRelayWordBound ℓ h n B f) :
    HierarchyRelayWordBound ℓ h n (2 * ((hierarchyAdmissibleWords (Fin 4) n).card * B))
      (fun t x => phasePrimitive (fun s => f t (x.1,s)) x.2) := by
  have hfin : AppendixD.FieldNormFinite ℓ h n (AppendixD.weighted (fun _ => (1 : ℝ)) f) := by
    rw [weighted_one]
    exact ⟨hf, relayWordBound_bdd hB⟩
  obtain ⟨_, _, _, _, hprim⟩ :=
    (hD T ℓ h hℓ hh (fun _ => 1) (fun _ => one_pos) n).2.2.1 E f hfin hper
  obtain ⟨hbP, hle⟩ := hprim hzero
  rw [weighted_one] at hbP
  unfold AppendixD.weightedFieldNorm at hle
  rw [weighted_one, weighted_one] at hle
  exact relayWordBound_mono (hierarchyRelayWordBound_of_finiteNorm hbP.2) le_rfl
    (hle.trans (mul_le_mul_of_nonneg_left hB.finiteNorm_le (by norm_num)))

/-- Copy of the private `relayWordBound_bilinear` (`HierarchyLinearRelayBounds.lean:439`). -/
theorem relayWordBound_bilinear {ℓ h : ℝ} {n : ℕ} {A C : ℝ}
    {f : T → Vec3 × ℝ → E} {g : T → Vec3 × ℝ → F} (B : E →L[ℝ] F →L[ℝ] G)
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hfA : HierarchyRelayWordBound ℓ h n A f)
    (hgC : HierarchyRelayWordBound ℓ h n C g) :
    HierarchyRelayWordBound ℓ h n ((2 : ℝ) ^ n * ‖B‖ * A * C)
      (fun t x => B (f t x) (g t x)) := by
  have hA := hfA.1
  have hC := hgC.1
  refine ⟨by positivity, fun w hw t x => ?_⟩
  obtain ⟨hw₁, hw₂⟩ := mem_hierarchyAdmissibleWords.mp hw
  have hsub (v : List (Fin 4)) (hv : List.Sublist v w) :
      v ∈ hierarchyAdmissibleWords (Fin 4) n :=
    mem_hierarchyAdmissibleWords.mpr ⟨hv.length_le.trans hw₁, hw₂.sublist hv⟩
  refine ((phaseOperatorWord_bilinear_bounds B (fun _ => contDiff_const) (hf t) (hg t)
    w hA (fun v hv => hfA.2 v (hsub v hv) t) (fun v hv => hgC.2 v (hsub v hv) t)).1 x).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hw₁)
      (norm_nonneg B)) hA) hC

/-- Copy of the private `relayWordBound_const_smul` (`HierarchyLinearRelayBounds.lean:514`). -/
theorem relayWordBound_const_smul {ℓ h : ℝ} {n : ℕ} {B : ℝ}
    {f : T → Vec3 × ℝ → E} (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hB : HierarchyRelayWordBound ℓ h n B f) (c : ℝ) :
    HierarchyRelayWordBound ℓ h n (‖c‖ * B) (fun t x => c • f t x) := by
  refine ⟨mul_nonneg (norm_nonneg _) hB.1, fun w hw t x => ?_⟩
  change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun x => c • f t x) x‖ ≤ _
  rw [phaseOperatorWord_const_smul (D := hierarchyMixedDirection ℓ h)
    (fun _ => contDiff_const) (hf t), norm_smul]
  exact mul_le_mul_of_nonneg_left (hB.2 w hw t x) (norm_nonneg _)

/-- Copy of the private `relay_phaseOperatorWord_sum` (`HierarchyLinearRelayBounds.lean:524`). -/
theorem relay_phaseOperatorWord_sum {ι : Type*} {ℓ h : ℝ}
    (s : Finset ι) (f : ι → Vec3 × ℝ → E)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (w : List (Fin 4)) (x : Vec3 × ℝ) :
    phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, phaseOperatorWord (hierarchyMixedDirection ℓ h) w (f i) x := by
  induction w generalizing x with
  | nil => rfl
  | cons j w ih =>
    change fderiv ℝ (phaseOperatorWord (hierarchyMixedDirection ℓ h) w
      (fun y => ∑ i ∈ s, f i y)) x (hierarchyMixedDirection ℓ h j x) = _
    rw [funext ih, fderiv_fun_sum]
    · simp only [_root_.sum_apply, phaseOperatorWord, phaseDirectionalDerivative]
    · exact fun i hi => (contDiff_phaseOperatorWord (fun _ => contDiff_const) (hf i hi)
        w).differentiable (by simp) x

/-- Copy of the private `relayWordBound_sum` (`HierarchyLinearRelayBounds.lean:539`). -/
theorem relayWordBound_sum {ι : Type*} {ℓ h : ℝ} {n : ℕ}
    (s : Finset ι) {B : ι → ℝ} {f : ι → T → Vec3 × ℝ → E}
    (hf : ∀ i ∈ s, ∀ t, ContDiff ℝ ∞ (f i t))
    (hB : ∀ i ∈ s, HierarchyRelayWordBound ℓ h n (B i) (f i)) :
    HierarchyRelayWordBound ℓ h n (∑ i ∈ s, B i) (fun t x => ∑ i ∈ s, f i t x) := by
  refine ⟨Finset.sum_nonneg (fun i hi => (hB i hi).1), fun w hw t x => ?_⟩
  rw [relay_phaseOperatorWord_sum s (fun i => f i t) (fun i hi => hf i hi t)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => (hB i hi).2 w hw t x)

/-- Copy of the private `relayWordBound_add` (`HierarchyLinearRelayBounds.lean:548`). -/
theorem relayWordBound_add {ℓ h : ℝ} {n : ℕ} {A B : ℝ}
    {f g : T → Vec3 × ℝ → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hA : HierarchyRelayWordBound ℓ h n A f) (hB : HierarchyRelayWordBound ℓ h n B g) :
    HierarchyRelayWordBound ℓ h n (A + B) (fun t x => f t x + g t x) := by
  let F (i : Fin 2) : T → Vec3 × ℝ → E := Fin.cases f (fun _ => g) i
  let C (i : Fin 2) : ℝ := Fin.cases A (fun _ => B) i
  have hF (i : Fin 2) (t : T) : ContDiff ℝ ∞ (F i t) := by
    fin_cases i
    · exact hf t
    · exact hg t
  have hC (i : Fin 2) : HierarchyRelayWordBound ℓ h n (C i) (F i) := by
    fin_cases i
    · exact hA
    · exact hB
  simpa only [Fin.sum_univ_two, show F 0 = f from rfl, show F 1 = g from rfl,
    show C 0 = A from rfl, show C 1 = B from rfl] using
    relayWordBound_sum (Finset.univ : Finset (Fin 2)) (fun i _ => hF i) (fun i _ => hC i)

/-- Copy of the private `relayWordBound_zero` (`HierarchyLinearRelayBounds.lean:1047`). -/
theorem relayWordBound_zero (ℓ h : ℝ) (n : ℕ) :
    HierarchyRelayWordBound ℓ h n 0 (fun (_ : T) (_ : Vec3 × ℝ) => (0 : E)) := by
  have hz (w : List (Fin 4)) :
      phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun _ => (0 : E)) = fun _ => 0 := by
    induction w with
    | nil => rfl
    | cons i w ih =>
      rw [phaseOperatorWord, ih]
      funext x
      simp [phaseDirectionalDerivative]
  refine ⟨le_rfl, fun w _ t x => ?_⟩
  simp only [hz, norm_zero, le_refl]

/-- Copy of `hierarchyRelayWordBound_linearPrimitive` (`HierarchyLinearRelayBounds.lean:670`),
with the primitive estimate (D.5) taken from `hD` (`relayWordBound_phasePrimitive_of_D1`). -/
theorem relayWordBound_linearPrimitive_of_D1 (hD : Statement.lemma_D_1) [CompleteSpace E]
    {ℓ h A B V₀ F₀ : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) {n : ℕ}
    {a b : T → Vec3 → Vec3 →L[ℝ] E} {V f : T → Vec3 × ℝ → Vec3}
    (ha : ∀ t, ContDiff ℝ ∞ (fun x : Vec3 × ℝ => a t x.1))
    (hb : ∀ t, ContDiff ℝ ∞ (fun x : Vec3 × ℝ => b t x.1))
    (hV : ∀ t, ContDiff ℝ ∞ (V t)) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hVp : ∀ t x, Function.Periodic (fun s => V t (x,s)) 1)
    (hfp : ∀ t x, Function.Periodic (fun s => f t (x,s)) 1)
    (hVz : ∀ t x, phaseMean (fun s => V t (x,s)) = 0)
    (hfz : ∀ t x, phaseMean (fun s => f t (x,s)) = 0)
    (haN : HierarchyRelayWordBound ℓ h n A (fun t x => a t x.1))
    (hbN : HierarchyRelayWordBound ℓ h n B (fun t x => b t x.1))
    (hVN : HierarchyRelayWordBound ℓ h n V₀ V) (hfN : HierarchyRelayWordBound ℓ h n F₀ f) :
    let P (t : T) (x : Vec3 × ℝ) :=
      phasePrimitive (fun s => a t x.1 (V t (x.1,s)) + b t x.1 (f t (x.1,s))) x.2
    (∀ t, ContDiff ℝ ∞ (P t)) ∧
      HierarchyRelayWordBound ℓ h n
        (2 * ((hierarchyAdmissibleWords (Fin 4) n).card *
          ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B * F₀))) P := by
  let I (t : T) (x : Vec3 × ℝ) := a t x.1 (V t x) + b t x.1 (f t x)
  have hv (t) : ContDiff ℝ ∞ (fun x : Vec3 × ℝ => a t x.1 (V t x)) := (ha t).clm_apply (hV t)
  have hf' (t) : ContDiff ℝ ∞ (fun x : Vec3 × ℝ => b t x.1 (f t x)) := (hb t).clm_apply (hf t)
  have hI (t) : ContDiff ℝ ∞ (I t) := (hv t).add (hf' t)
  have hIp (t x) : Function.Periodic (fun s => I t (x,s)) 1 :=
    fun s => by simp only [I, hVp t x s, hfp t x s]
  have hIz (t x) : phaseMean (fun s => I t (x,s)) = 0 := by
    have hvC : Continuous (fun s => V t (x,s)) :=
      (hV t).continuous.comp (continuous_const.prodMk continuous_id)
    have hfC : Continuous (fun s => f t (x,s)) :=
      (hf t).continuous.comp (continuous_const.prodMk continuous_id)
    have hva : Continuous (fun s => a t x (V t (x,s))) := (a t x).continuous.comp hvC
    have hfb : Continuous (fun s => b t x (f t (x,s))) := (b t x).continuous.comp hfC
    have hvzero : phaseMean (fun s => a t x (V t (x,s))) = 0 := by
      rw [phaseMean, (a t x).intervalIntegral_comp_comm (hvC.intervalIntegrable 0 1),
        ← phaseMean, hVz, map_zero]
    have hfzero : phaseMean (fun s => b t x (f t (x,s))) = 0 := by
      rw [phaseMean, (b t x).intervalIntegral_comp_comm (hfC.intervalIntegrable 0 1),
        ← phaseMean, hfz, map_zero]
    simp only [I, phaseMean_add hva hfb, hvzero, hfzero, add_zero]
  exact ⟨fun t => contDiff_phasePrimitive_word (f := fun x s => I t (x,s)) (hI t),
    relayWordBound_phasePrimitive_of_D1 hD hℓ hh hI hIp hIz
      (relayWordBound_add hv hf' (HierarchyRelayWordBound.clm_apply ha hV haN hVN)
        (HierarchyRelayWordBound.clm_apply hb hf hbN hfN))⟩

/-- Copy of `hierarchyFiniteWordNorm_waveCompletion_le` (`HierarchyLinearRelayBounds.lean:718`),
the finite bound for the divergence correction (5.31), with the primitive estimate (D.5)
taken from `hD`. -/
theorem waveCompletion_le_of_D1 (hD : Statement.lemma_D_1) {ℓ h freq A B V₀ : ℝ} (n : ℕ)
    (hℓ' : 0 < ℓ) (hh : 0 < h) (hfreq : 0 < freq) {G : T → Vec3 × ℝ → Vec3 →L[ℝ] Vec3}
    {k : T → Vec3 → Vec3} {V : T → Vec3 × ℝ → Vec3}
    (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hVp : ∀ t a, Function.Periodic (fun s => V t (a,s)) 1)
    (hVzero : ∀ t a, phaseMean (fun s => V t (a,s)) = 0)
    (hVN : HierarchyRelayWordBound ℓ h (n + 1) V₀ V)
    (hG : ∀ i t, ContDiff ℝ ∞ (fun x => hierarchyRelayCurlRow ℓ (G t x) i))
    (hGN : ∀ i, HierarchyRelayWordBound ℓ h n A
      (fun t x => hierarchyRelayCurlRow ℓ (G t x) i))
    (hK : ∀ t, ContDiff ℝ ∞ (fun x : Vec3 × ℝ => hierarchyRelayPotentialCoefficient (k t x.1)))
    (hKN : HierarchyRelayWordBound ℓ h (n + 1) B
      (fun t x => hierarchyRelayPotentialCoefficient (k t x.1))) :
    let Q (t : T) (x : Vec3 × ℝ) := wavePotential (freq • k t x.1) (fun s => V t (x.1,s)) x.2
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun t x => curlOfDerivative ((hierarchyRelayLabelJet (Q t) x).comp (G t x))) ≤
      (hierarchyAdmissibleWords (Fin 4) n).card * (3 * (2 : ℝ) ^ n * A *
        (2 * ((hierarchyAdmissibleWords (Fin 4) (n + 1)).card *
          ((2 : ℝ) ^ (n + 1) * B * V₀))) * freq⁻¹) := by
  have hℓ : ℓ ≠ 0 := hℓ'.ne'
  let I := fun (t : T) (x : Vec3 × ℝ) => hierarchyRelayPotentialCoefficient (k t x.1) (V t x)
  let P := fun (t : T) (x : Vec3 × ℝ) => phasePrimitive (fun s => I t (x.1,s)) x.2
  have hI (t) : ContDiff ℝ ∞ (I t) := (hK t).clm_apply (hV t)
  have hIp (t a) : Function.Periodic (fun s => I t (a,s)) 1 :=
    fun s => congrArg (hierarchyRelayPotentialCoefficient (k t a)) (hVp t a s)
  have hIz (t a) : phaseMean (fun s => I t (a,s)) = 0 := by
    let L := hierarchyRelayPotentialCoefficient (k t a)
    have hVc : Continuous (fun s => V t (a,s)) :=
      (hV t).continuous.comp (continuous_const.prodMk continuous_id)
    change phaseMean (fun s => L (V t (a,s))) = 0
    rw [phaseMean, L.intervalIntegral_comp_comm (hVc.intervalIntegrable 0 1),
      ← phaseMean, hVzero, map_zero]
  have hP (t) : ContDiff ℝ ∞ (P t) :=
    contDiff_phasePrimitive_word (f := fun a s => I t (a,s)) (hI t)
  have hPN := relayWordBound_phasePrimitive_of_D1 hD hℓ' hh hI hIp hIz
    (HierarchyRelayWordBound.clm_apply hK hV hKN hVN)
  have hb := hierarchyFiniteWordNorm_pulledBackCurl_le n hℓ hfreq hP hG hGN hPN
  have heq (t : T) :
      (fun x : Vec3 × ℝ => wavePotential (freq • k t x.1) (fun s => V t (x.1,s)) x.2) =
        fun x => freq⁻¹ • P t x := by
    funext x
    exact wavePotential_frequency_scale hfreq (k t x.1) (fun s => V t (x.1,s)) x.2
  dsimp only
  have hcurl (t : T) (x : Vec3 × ℝ) :
      curlOfDerivative ((hierarchyRelayLabelJet (fun y =>
        wavePotential (freq • k t y.1) (fun s => V t (y.1,s)) y.2) x).comp (G t x)) =
      freq⁻¹ • curlOfDerivative ((hierarchyRelayLabelJet (P t) x).comp (G t x)) := by
    rw [heq]
    simp only [hierarchyRelayLabelJet, fderiv_fun_const_smul ((hP t).differentiable (by simp) x),
      smul_comp, curlOfDerivative_smul]
  simp_rw [hcurl]
  exact hb

set_option maxHeartbeats 1200000 in
/-- Copy of `hierarchyFiniteWordNorm_waveLinearRelay_le` (`HierarchyLinearRelayBounds.lean:1067`),
the weighted bound for the four terms of the linear relay (5.32)–(5.33), with the primitive
estimate (D.5) taken from `hD`. -/
theorem waveLinearRelay_le_of_D1 (hD : Statement.lemma_D_1)
    {ℓ h freq K V₀ F₀ : ℝ} (n : ℕ) (hℓ' : 0 < ℓ) (hh : 0 < h) (hfreq : 0 < freq)
    {G M : T → Vec3 → Vec3 →L[ℝ] Vec3} {k : T → Vec3 → Vec3}
    {V f : T → Vec3 × ℝ → Vec3}
    (hV : ∀ t, ContDiff ℝ ∞ (V t)) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hVp : ∀ t a, Function.Periodic (fun s => V t (a,s)) 1)
    (hfp : ∀ t a, Function.Periodic (fun s => f t (a,s)) 1)
    (hVz : ∀ t a, phaseMean (fun s => V t (a,s)) = 0)
    (hfz : ∀ t a, phaseMean (fun s => f t (a,s)) = 0)
    (hVN : HierarchyRelayWordBound ℓ h (n + 1) V₀ V)
    (hfN : HierarchyRelayWordBound ℓ h (n + 1) F₀ f)
    (hKq : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun t a => hierarchyRelayPotentialCoefficient (k t a)))
    (hKqt : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun t a => hierarchyRelayTimeAmplitudeCoefficient (M t a) (k t a)))
    (hKpv : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun t a => hierarchyRelayPressureAmplitudeCoefficient (M t a) (k t a)))
    (hKpf : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun t a => hierarchyRelayPressureSourceCoefficient (k t a)))
    (hG : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun t a => hierarchyRelayCurlRow ℓ (G t a) i))
    (hMG : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun t a => hierarchyRelayMaterialRow ℓ (G t a) (M t a) i))
    (hP : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun t a => hierarchyRelayPressureRow ℓ (G t a) i)) :
    let κ (t : T) (a : Vec3) := freq • k t a
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun t x => hierarchyLinearRelayAt (G t x.1) (M t x.1)
        (relayPotentialProfile (κ t) (V t)) (relayPotentialTimeProfile (M t) (κ t) (V t) (f t))
        (relayPhasePressureProfile (M t) (κ t) (V t) (f t)) x) ≤
      (18 * (hierarchyAdmissibleWords (Fin 4) n).card *
        (hierarchyAdmissibleWords (Fin 4) (n + 1)).card * (2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)) *
          K ^ 2 * freq⁻¹ * (V₀ + F₀) := by
  have hℓ : ℓ ≠ 0 := hℓ'.ne'
  let B := 2 * ((hierarchyAdmissibleWords (Fin 4) (n + 1)).card *
      ((2 : ℝ) ^ (n + 1) * K * V₀ + (2 : ℝ) ^ (n + 1) * K * F₀))
  have hK : 0 ≤ K := hKq.2.1
  have hf₀ : 0 ≤ F₀ := hfN.1
  obtain ⟨hsq, hbq⟩ := relayWordBound_linearPrimitive_of_D1 hD hℓ' hh
    (a := fun t a => hierarchyRelayPotentialCoefficient (k t a))
    (b := fun t a => hierarchyRelayPotentialCoefficient (k t a))
    (f := fun _ _ => 0) hKq.1 hKq.1 hV
    (fun _ => contDiff_const) hVp (fun _ _ _ => rfl) hVz
    (fun _ _ => phaseMean_const 0) hKq.2 hKq.2 hVN
    (relayWordBound_zero (T := T) (E := Vec3) ℓ h (n + 1))
  simp only [map_zero, add_zero, mul_zero] at hsq hbq
  have hsq' (t) : ContDiff ℝ ∞ (relayPotentialProfile (k t) (V t)) := hsq t
  have hbq' : HierarchyRelayWordBound ℓ h (n + 1) B
      (fun t => relayPotentialProfile (k t) (V t)) := by
    have he : (fun t x => phasePrimitive (fun s =>
        hierarchyRelayPotentialCoefficient (k t x.1) (V t (x.1,s))) x.2) =
        fun t => relayPotentialProfile (k t) (V t) := rfl
    rw [← he]
    refine relayWordBound_mono hbq le_rfl ?_
    dsimp only [B]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (Nat.cast_nonneg _)) (by norm_num)
  obtain ⟨hsqt, hbqt⟩ := relayWordBound_linearPrimitive_of_D1 hD hℓ' hh
    (a := fun t a => hierarchyRelayTimeAmplitudeCoefficient (M t a) (k t a))
    (b := fun t a => hierarchyRelayPotentialCoefficient (k t a))
    hKqt.1 hKq.1 hV hf hVp hfp hVz hfz hKqt.2 hKq.2 hVN hfN
  obtain ⟨hsp, hbp⟩ := relayWordBound_linearPrimitive_of_D1 hD hℓ' hh
    (a := fun t a => hierarchyRelayPressureAmplitudeCoefficient (M t a) (k t a))
    (b := fun t a => hierarchyRelayPressureSourceCoefficient (k t a))
    hKpv.1 hKpf.1 hV hf hVp hfp hVz hfz hKpv.2 hKpf.2 hVN hfN
  have hqe (t : T) : relayPotentialTimeProfile (M t) (k t) (V t) (f t) =
      fun x => phasePrimitive (fun s =>
        hierarchyRelayTimeAmplitudeCoefficient (M t x.1) (k t x.1) (V t (x.1,s)) +
        hierarchyRelayPotentialCoefficient (k t x.1) (f t (x.1,s))) x.2 := by
    funext x
    simp only [relayPotentialTimeProfile, wavePotentialTimeSource_eq_coefficients]
  have hpe (t : T) : relayPhasePressureProfile (M t) (k t) (V t) (f t) =
      fun x => phasePrimitive (fun s =>
        hierarchyRelayPressureAmplitudeCoefficient (M t x.1) (k t x.1) (V t (x.1,s)) +
        hierarchyRelayPressureSourceCoefficient (k t x.1) (f t (x.1,s))) x.2 := by
    funext x
    simp only [relayPhasePressureProfile, oscillatoryPhasePressure,
      oscillatoryPressureSlope_eq_coefficients]
  have hrs (t) : ContDiff ℝ ∞ (relayPotentialTimeProfile (M t) (k t) (V t) (f t)) := by
    rw [hqe]
    exact hsqt t
  have hrsN : HierarchyRelayWordBound ℓ h (n + 1) B
      (fun t => relayPotentialTimeProfile (M t) (k t) (V t) (f t)) := by
    simp_rw [hqe]
    exact hbqt
  have hps (t) : ContDiff ℝ ∞ (relayPhasePressureProfile (M t) (k t) (V t) (f t)) := by
    rw [hpe]
    exact hsp t
  have hpsN : HierarchyRelayWordBound ℓ h (n + 1) B
      (fun t => relayPhasePressureProfile (M t) (k t) (V t) (f t)) := by
    simp_rw [hpe]
    exact hbp
  have hb := hierarchyFiniteWordNorm_linearRelay_le (A := K) (B := K) (C := K)
    (G := fun t x => G t x.1) (M := fun t x => M t x.1)
    n hℓ hfreq hsq' hrs hps hbq' hrsN hpsN
    (fun i => (hG i).1) (fun i => (hMG i).1) (fun i => (hP i).1)
    (fun i => (hG i).2) (fun i => (hMG i).2) (fun i => (hP i).2)
  have heq (t : T) (x : Vec3 × ℝ) :
      hierarchyLinearRelayAt (G t x.1) (M t x.1)
        (relayPotentialProfile (fun a => freq • k t a) (V t))
        (relayPotentialTimeProfile (M t) (fun a => freq • k t a) (V t) (f t))
        (relayPhasePressureProfile (M t) (fun a => freq • k t a) (V t) (f t)) x =
      freq⁻¹ • hierarchyLinearRelayAt (G t x.1) (M t x.1) (relayPotentialProfile (k t) (V t))
        (relayPotentialTimeProfile (M t) (k t) (V t) (f t))
        (relayPhasePressureProfile (M t) (k t) (V t) (f t)) x :=
    hierarchyLinearRelayAt_frequency_scale hfreq _ _ _ _ _ _
      ((hsq' t).differentiable (by simp) x) ((hrs t).differentiable (by simp) x)
      ((hps t).differentiable (by simp) x)
  dsimp only
  simp_rw [heq]
  refine hb.trans_eq ?_
  dsimp only [B]
  ring

end WordBounds

section Twisted

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

set_option maxHeartbeats 1000000 in
/-- Copy of `boundedWeightSeminorm_waveRelay_le_of_eval`
(`TorusEuler/HierarchyTwistedRelayBounds.lean:788`, content of row 5.5): the relay source
(5.32)–(5.33) has the inverse-frequency bound in the weighted seminorm. The primitive
estimate (D.5) is taken from `hD` (through `waveLinearRelay_le_of_D1`). -/
theorem boundedWeightSeminorm_waveRelay_le_of_eval_of_D1 (hD : Statement.lemma_D_1)
    (hT : 0 < T) (G M : MP) (κ V F R : VP) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (n : ℕ)
    {freq K : ℝ} (hfreq : 0 < freq) {S : Set ℝ} (hS : S ⊆ Icc 0 T)
    (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ S, ‖τ t‖ ≤ C)
    (hV : (twistedHierarchyOperators hT G M κ).average V = 0)
    (hF : (twistedHierarchyOperators hT G M κ).average F = 0)
    (hEval : ∀ t ∈ S, ∀ x : Vec3 × ℝ, R.val.val.val (t, x) = waveRelayAt G M κ V F t x)
    (hCoeff : WaveRelayCoefficientBudget ℓ h n K
      (fun (t : S) a => G.val.val.val (t, a, 0)) (fun (t : S) a => M.val.val.val (t, a, 0))
      (fun (t : S) a => freq⁻¹ • κ.val.val.val (t, a, 0))) :
    boundedWeightSeminorm False ℓ h n hT hS τ hτ R ≤
      waveRelayOrderConstant n * K ^ 2 * freq⁻¹ *
        (boundedWeightSeminorm False ℓ h (n + 1) hT hS τ hτ V +
          boundedWeightSeminorm False ℓ h (n + 1) hT hS τ hτ F) := by
  let G₀ (t : ℝ) (a : Vec3) := G.val.val.val (t, a, 0)
  let M₀ (t : ℝ) (a : Vec3) := M.val.val.val (t, a, 0)
  let κ₀ (t : ℝ) (a : Vec3) := κ.val.val.val (t, a, 0)
  let k₀ (t : S) (a : Vec3) := freq⁻¹ • κ₀ t a
  let v := weightedSlices S τ V
  let f := weightedSlices S τ F
  have hPeriod (W : VP) (t : S) (a : Vec3) :
      Function.Periodic (fun s => weightedSlices S τ W t (a, s)) 1 := by
    intro s
    change τ t • W.val.val.val (t, a, s + 1) = τ t • W.val.val.val (t, a, s)
    exact congrArg (fun u : Vec3 => τ t • u) (HierarchyPeriodicProfile.phasePeriodic W.val t a s)
  have hMean (W : VP) (hW : (twistedHierarchyOperators hT G M κ).average W = 0)
      (t : S) (a : Vec3) : phaseMean (fun s => weightedSlices S τ W t (a, s)) = 0 := by
    have h := congrArg (fun z : VP => z.val.val.val (t, a, 0)) hW
    change ((twistedHierarchyOperators hT G M κ).average W).val.val.val (t, a, 0) = 0 at h
    rw [average_apply_phaseMean hT G M κ W (hS t.property) a 0] at h
    change phaseMean (fun s => τ t • W.val.val.val (t, a, s)) = 0
    rw [phaseMean_const_smul, h, smul_zero]
  have hWord (W : VP) := hierarchyRelayWordBound_of_finiteNorm (ℓ := ℓ) (h := h) (n := n + 1)
    (f := weightedSlices S τ W) (fun w _ =>
      hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w W hS τ hτ)
  have hb := waveLinearRelay_le_of_D1 hD n hℓ hh hfreq
    (G := fun (t : S) a => G₀ t a) (M := fun (t : S) a => M₀ t a) (k := k₀) (V := v) (f := f)
    (weightedSlices_smooth hS τ V) (weightedSlices_smooth hS τ F)
    (hPeriod V) (hPeriod F) (hMean V hV) (hMean F hF) (hWord V) (hWord F)
    hCoeff.potential hCoeff.potentialTime hCoeff.pressureAmplitude hCoeff.pressureSource
    hCoeff.curl hCoeff.material hCoeff.gradient
  dsimp only at hb
  have hScale (t : S) : (fun a => freq • k₀ t a) = κ₀ t := by
    funext a
    change freq • (freq⁻¹ • κ₀ t a) = κ₀ t a
    rw [smul_smul, mul_inv_cancel₀ hfreq.ne', one_smul]
  simp_rw [hScale] at hb
  have hW := weightedSlices_eq_hierarchyLinearRelayAt_of_eval τ G₀ M₀ κ₀ V F R hEval
  rw [boundedWeightSeminorm_apply, hW]
  exact hb

set_option maxHeartbeats 1000000 in
/-- Copy of `boundedWeightSeminorm_complete_le`
(`TorusEuler/HierarchyTwistedRelayBounds.lean:868`, content of row 5.5): the divergence
correction (5.31) costs one mixed order and gains one inverse frequency in the weighted
seminorm. The primitive estimate (D.5) is taken from `hD` (through `waveCompletion_le_of_D1`). -/
theorem boundedWeightSeminorm_complete_le_of_D1 (hD : Statement.lemma_D_1)
    (hT : 0 < T) (G : MP) (κ V : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hVmean : profilePhaseAverage hT V = 0)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C)
    (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (n : ℕ) {freq K : ℝ} (hfreq : 0 < freq)
    (hG : ∀ i, HierarchyRelayCoefficientJets ℓ h n K
      (fun (t : A) a => hierarchyRelayCurlRow ℓ (G.val.val.val (t, a, 0)) i))
    (hκNorm : HierarchyRelayCoefficientJets ℓ h (n + 1) K
      (fun (t : A) a => hierarchyRelayPotentialCoefficient (freq⁻¹ • κ.val.val.val (t, a, 0)))) :
    boundedWeightSeminorm False ℓ h n hT hA τ hτ (complete hT G κ hκPhase hκ V) ≤
      (6 * (hierarchyAdmissibleWords (Fin 4) n).card *
        (hierarchyAdmissibleWords (Fin 4) (n + 1)).card * (2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)) *
        K ^ 2 * freq⁻¹ * boundedWeightSeminorm False ℓ h (n + 1) hT hA τ hτ V := by
  let W := weightedSlices A τ V
  let coframe (t : A) (x : Vec3 × ℝ) := G.val.val.val (t, x.1, 0)
  let covector (t : A) (a : Vec3) := freq⁻¹ • κ.val.val.val (t, a, 0)
  have hWp (t : A) (a : Vec3) : Function.Periodic (fun s => W t (a, s)) 1 := by
    intro s
    change τ t • V.val.val.val (t, a, s + 1) = τ t • V.val.val.val (t, a, s)
    exact congrArg (fun v : Vec3 => τ t • v) (HierarchyPeriodicProfile.phasePeriodic V.val t a s)
  have hWzero (t : A) (a : Vec3) : phaseMean (fun s => W t (a, s)) = 0 := by
    have ht := hA t.property
    have hx : ((t : ℝ), a, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    have hmean := congrArg (fun f : VP => f.val.val.val (t, a, 0)) hVmean
    change (HierarchySmoothProfile.profilePhaseAverage hT V.val.val).val (t, a, 0) = 0 at hmean
    rw [HierarchySmoothProfile.profilePhaseAverage_apply hT V.val.val hx] at hmean
    change phaseMean (fun s => τ t • V.val.val.val (t, a, s)) = 0
    rw [phaseMean_const_smul, hmean, smul_zero]
  have hWN := hierarchyRelayWordBound_of_finiteNorm
    (f := W) (ℓ := ℓ) (h := h) (n := n + 1) fun w _ =>
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w V hA τ hτ
  have hb := waveCompletion_le_of_D1 hD (G := coframe) (k := covector)
    n hℓ hh hfreq (weightedSlices_smooth hA τ V) hWp hWzero hWN
    (fun i => (hG i).1) (fun i => (hG i).2) hκNorm.1 hκNorm.2
  have hκ' (t : A) (a : Vec3) : freq • covector t a = κ.val.val.val (t, a, 0) := by
    simp [covector, smul_smul, hfreq.ne']
  have hEq : weightedSlices A τ (complete hT G κ hκPhase hκ V) = fun (t : A) x =>
      curlOfDerivative ((hierarchyRelayLabelJet (fun y =>
        wavePotential (freq • covector t y.1) (fun s => W t (y.1, s)) y.2) x).comp
          (coframe t x)) := by
    rw [weightedSlices_complete_eq_relayPotential hT G κ V hGPhase hκPhase hκ hVmean hA τ]
    funext t x
    simp only [hκ', W, coframe]
    rfl
  simp only [boundedWeightSeminorm_apply] at *
  rw [hEq]
  refine hb.trans_eq ?_
  ring

end Twisted

end

end TorusEuler.Paper.Lib.S5a
