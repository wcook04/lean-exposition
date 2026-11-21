import TorusEuler.TerminalLeadingTime

/-! Scheduled leading and activation time estimates for the selected later wave. -/

open Set Filter
open scoped ContDiff

namespace TorusEuler.InductiveEulerTip.SelectedLaterInput

open LocalizedAmplitude

noncomputable section

open HierarchyTwistedProfile

/-- The degree in the old parent scale is independent of the label/phase
order and of the expansion depth. -/
def leadingTimeParentPower (q e : ℕ) : ℕ := e * (q + 1) + q + 14

set_option maxHeartbeats 1500000 in
/-- One fixed-order cost bounds the actual three leading rows of the
scheduled expansion. The coefficient cap and scalar switch bounds use the
same selected parent and later wave. -/
theorem exists_leadingTimeJetBudget (p : ℕ) :
    ∃ A : ℕ, p ≤ A ∧ ∀ (q e : ℕ) (Ccoeff Cswitch : ℕ → ℝ),
      (∀ m, 0 ≤ Ccoeff m) → (∀ m, 0 ≤ Cswitch m) →
      ∃ cost : ℕ → ℝ, (∀ m, 0 ≤ cost m) ∧
      ∀ {P : InductiveEulerParameters} {j : ℕ} {tip : InductiveEulerTip P j}
        {Cenv : ℝ} {a : ℕ} (d : tip.SelectedLaterInput Cenv a), A ≤ a →
        let t₀ := tip.nextActivation
        let T := P.slab (j + 2) t₀
        let μ := P.frequency (j + 1)
        let D := μ ^ (9 : ℕ)
        let freq := P.frequency (j + 2)
        let r := d.window.physical.rate
        let M (t : ℝ) (x : Vec3) := fderiv ℝ (tip.parent.velocity t) (tip.parent.flow 0 t x)
        let κ (t : ℝ) (x : Vec3) := labelWaveVector tip.parent.flow 0 x d.carrier t
        let gen (t : ℝ) (x : Vec3) := affineWaveAmplitudeOperator (M t x) (κ t x)
        let pre (t : ℝ) (x : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M t x) (freq⁻¹ • κ t x)
        ContDiffOn ℝ ∞ (Function.uncurry gen) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        ContDiffOn ℝ ∞ (Function.uncurry pre) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        TerminalMixedJetBound 0 T q p D (D ^ e) Ccoeff gen →
        TerminalMixedJetBound 0 T q p D (D ^ e) Ccoeff pre →
        (∀ i ≤ q + 1, ∀ t, |iteratedDeriv i (waveSwitch t₀ r) t| ≤ Cswitch i * μ ^ i) →
        ∀ n : ℕ,
          let wV : Seminorm ℝ (HierarchyTwistedProfile T d.carrier Vec3) :=
            amplitudeSeminorm False d.radius d.width n d.time_pos
            tip.next_activation_nonnegative d.regularity.start_lt_end.le
            d.centerWeight d.centerWeight_continuous d.centerWeight_pos
          let V := timeJetSeminorm d.time_pos q wV d.leading.output.V
          let S := timeJetSeminorm d.time_pos q wV d.leading.leadingSwitch
          let wP : Seminorm ℝ (HierarchyTwistedProfile T d.carrier ℝ) :=
            amplitudeSeminorm False d.radius d.width n d.time_pos
            tip.next_activation_nonnegative d.regularity.start_lt_end.le
            d.centerWeight d.centerWeight_continuous d.centerWeight_pos
          let press := timeJetSeminorm d.time_pos q wP d.leading.output.p
          let R := cost n * D ^ leadingTimeParentPower q e * freq ^ (-5 / 4 : ℝ)
          V + freq * press ≤ R ∧ S ≤ R := by
  obtain ⟨A₀, Cseed, _, hCseed, hSeed⟩ := exists_scaledEnvelopedAmplitudeCost
  refine ⟨max p A₀, le_max_left _ _, ?_⟩
  intro q e Ccoeff Cswitch hCcoeff hCswitch
  choose Eφ hEφ hJets using LocalizedAmplitude.SeedOn.exists_activeScaledLeading_timeJetBounds
  let G (n : ℕ) : ℝ := ∑ m ∈ Finset.range (n + 1), Ccoeff m
  let H : ℝ := ∑ m ∈ Finset.range (q + 2), Cswitch m
  let V (n : ℕ) := Eφ n * (2 : ℝ) ^ (q + 2*n) * H * Cseed n *
    (1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * G n) ^ q
  let L (n : ℕ) := (2 : ℝ) ^ (q+n) * G n * V n
  let fixed (n : ℕ) := ((q + 1 : ℕ) : ℝ) * ((hierarchyAdmissibleWords (Fin 4) n).card : ℝ)
  let cost (n : ℕ) := fixed n * (V n + L n)
  have hG (n : ℕ) : 0 ≤ G n := Finset.sum_nonneg (fun m _ => hCcoeff m)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun m _ => hCswitch m)
  have hV (n : ℕ) : 0 ≤ V n := by
    have hφ := zero_le_one.trans (hEφ n)
    have hSeedN := zero_le_one.trans (hCseed n)
    have hGN := hG n
    dsimp only [V]
    positivity
  have hL (n : ℕ) : 0 ≤ L n := by
    dsimp only [L]
    exact mul_nonneg (mul_nonneg (by positivity) (hG n)) (hV n)
  refine ⟨cost, ?_, ?_⟩
  · intro n
    exact mul_nonneg (by dsimp only [fixed]; positivity) (add_nonneg (hV n) (hL n))
  intro P j tip Cenv a d ha t₀ T μ D freq r M κ gen pre hg hp hGen hPre hSwitch n wV VJ SJ wP PJ R
  have ht₀ : 0 ≤ t₀ := tip.next_activation_nonnegative
  have htT : t₀ < T := d.regularity.start_lt_end
  have hT : 0 < T := d.time_pos
  have hD : 1 ≤ D := one_le_two.trans d.parent_scale_ge_two
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hf : 1 ≤ freq := d.child_frequency_ge_one
  have hf₀ : 0 ≤ freq := zero_le_one.trans hf
  have hDμ : μ ≤ D := d.parent_frequency_le_scale
  have hμ : 1 ≤ μ := one_le_two.trans d.parent_frequency_ge_two
  let J := Icc t₀ T ×ˢ (univ : Set Vec3)
  let sc (x : ℝ × Vec3) := (x.1, d.radius • x.2)
  have hsc : ContDiff ℝ ∞ sc := contDiff_fst.prodMk (contDiff_snd.const_smul d.radius)
  have hmaps : MapsTo sc J (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    fun x hx => ⟨⟨ht₀.trans hx.1.1, hx.1.2⟩, mem_univ _⟩
  have hScale : d.radius * D ^ p ≤ 1 := d.radius_mul_parent_power ((le_max_left p A₀).trans ha)
  let Bgen := G n * D ^ e
  let Bamp := Cseed n * D ^ (13 : ℕ)
  let Bχ := H * D ^ (q+1)
  have hBgen : 0 ≤ Bgen := mul_nonneg (hG n) (pow_nonneg hD₀ _)
  have hBamp : 0 ≤ Bamp := mul_nonneg (zero_le_one.trans (hCseed n)) (pow_nonneg hD₀ _)
  have hBχ : 0 ≤ Bχ := mul_nonneg hH (pow_nonneg hD₀ _)
  have hχJ (i : ℕ) (hi : i ≤ q + 1) (t : ℝ) : ‖iteratedDeriv i (waveSwitch t₀ r) t‖ ≤ Bχ := by
    rw [Real.norm_eq_abs]
    refine (hSwitch i hi t).trans ?_
    have hHi : Cswitch i ≤ H := Finset.single_le_sum (f := Cswitch) (fun m _ => hCswitch m)
      (Finset.mem_range.mpr (by omega))
    have hpow : μ ^ i ≤ D ^ (q+1) := (pow_le_pow_left₀ (zero_le_one.trans hμ) hDμ i).trans
      (pow_le_pow_right₀ hD hi)
    exact mul_le_mul hHi hpow (pow_nonneg (zero_le_one.trans hμ) _) hH
  have hχs : ContDiff ℝ ∞ (deriv (waveSwitch t₀ r)) := by
    apply ContDiff.deriv'
    simpa using contDiff_waveSwitch t₀ r
  have hχsJ (i : ℕ) (hi : i ≤ q) (t : ℝ) : ‖iteratedDeriv i (deriv (waveSwitch t₀ r)) t‖ ≤ Bχ := by
    rw [← iteratedDeriv_succ']
    exact hχJ (i+1) (Nat.succ_le_succ hi) t
  have hA (t : ℝ) (ht : t ∈ Icc t₀ T) : PhaseJetBound n (‖d.selection.crossing.amplitude t‖ * Bamp)
      (d.seed.scaledEnvelopedAmplitude t) := hSeed d ((le_max_right p A₀).trans ha) n t ht
  let bV := Eφ n * (2 : ℝ) ^ (q + 2*n) * Bχ * Bamp *
    (1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * Bgen) ^ q
  let bP := (2 : ℝ) ^ (q+n) * Bgen * bV
  have hscOn : ContDiffOn ℝ ∞ sc J := hsc.contDiffOn
  have hgR : ContDiffOn ℝ ∞ (Function.uncurry (fun t x => gen t (d.radius • x))) J := by
    have hComp : ContDiffOn ℝ ∞ ((Function.uncurry gen) ∘ sc) J := hg.comp hscOn hmaps
    change ContDiffOn ℝ ∞ ((Function.uncurry gen) ∘ sc) J
    exact hComp
  have hpR : ContDiffOn ℝ ∞ (Function.uncurry (fun t x => pre t (d.radius • x))) J := by
    have hComp : ContDiffOn ℝ ∞ ((Function.uncurry pre) ∘ sc) J := hp.comp hscOn hmaps
    change ContDiffOn ℝ ∞ ((Function.uncurry pre) ∘ sc) J
    exact hComp
  have hGenJ (t : ℝ) (ht : t ∈ Icc t₀ T) (i : ℕ) (hi : i ≤ q) :
      PhaseJetBound n Bgen (activeTimeJet t₀ T i (fun u x => gen u (d.radius • x)) t) :=
    TerminalMixedJetBound.scaledActiveTimeJet_phaseJetBound
      (q := q) (p := p) (e := e) (D := D) (ell := d.radius) (C := Ccoeff) (f := gen)
      hT ht₀ htT hD d.regularity.envelope_pos.le
      hScale hCcoeff hg hGen n hi ht
  have hPreJ (t : ℝ) (ht : t ∈ Icc t₀ T) (i : ℕ) (hi : i ≤ q) :
      PhaseJetBound n Bgen (activeTimeJet t₀ T i (fun u x => pre u (d.radius • x)) t) :=
    TerminalMixedJetBound.scaledActiveTimeJet_phaseJetBound
      (q := q) (p := p) (e := e) (D := D) (ell := d.radius) (C := Ccoeff) (f := pre)
      hT ht₀ htT hD d.regularity.envelope_pos.le
      hScale hCcoeff hp hPre n hi ht
  have hMid (t : ℝ) (ht : t ∈ Icc t₀ T) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
      (hχq : ∀ i ≤ q, ‖iteratedDeriv i χ t‖ ≤ Bχ) (i : ℕ) (hi : i ≤ q) :
      PhaseJetBound n (d.centerWeight t * (bV * freq ^ (-5 / 4 : ℝ)))
        (activeTimeJet t₀ T i (fun u =>
          scaledPhaseProfile d.radius d.width (fun x s => χ u • d.seed.leading d.width u x s)) t) ∧
      PhaseJetBound n (d.centerWeight t * (bP * freq ^ (-5 / 4 : ℝ)))
        (activeTimeJet t₀ T i (fun u => scaledPhaseProfile d.radius d.width
          (fun x s => freq * (χ u * d.seed.leadingPressure d.width u x s))) t) :=
    hJets n (t₀ := t₀) (T := T) (ell := d.radius) (D := D) (r := r) (freq := freq)
      (M := M) (κ := κ) (center := d.selection.crossing.amplitude) (w := d.seed)
      (Bamp := Bamp) (Bgen := Bgen) (Bpre := Bgen) (Bχ := Bχ)
      hf d.regularity q ht hχ hBamp hBgen hBgen hBχ hgR hpR (hGenJ t ht) (hPreJ t ht)
      hχq (hA t ht) i hi
  have hBV : 0 ≤ bV := by
    have hφ := zero_le_one.trans (hEφ n)
    dsimp only [bV]
    positivity
  have hBP : 0 ≤ bP := by dsimp only [bP]; positivity
  have HJ := LocalizedAmplitude.SeedOn.twistedLeading_timeJetSeminorm_bounds d.regularity d.carrier q n hf₀
    d.centerWeight_continuous d.centerWeight_pos
    (mul_nonneg hBV (Real.rpow_nonneg hf₀ _))
    (mul_nonneg hBP (Real.rpow_nonneg hf₀ _))
    (mul_nonneg hBV (Real.rpow_nonneg hf₀ _))
    (fun i hi t ht => (hMid t ht (contDiff_waveSwitch t₀ r)
      (fun k hk => hχJ k (hk.trans (Nat.le_succ q)) t) i hi).1)
    (fun i hi t ht => (hMid t ht (contDiff_waveSwitch t₀ r)
      (fun k hk => hχJ k (hk.trans (Nat.le_succ q)) t) i hi).2)
    (fun i hi t ht => (hMid t ht hχs (fun k hk => hχsJ k hk t) i hi).1)
  have hGrowth : 1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * Bgen ≤
      (1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * G n) * D ^ e := by
    rw [add_mul, one_mul]
    exact add_le_add (one_le_pow₀ hD) (le_of_eq (by dsimp only [Bgen]; ring))
  have hV' : bV ≤ V n * D ^ (e*q + q + 14) := by
    dsimp only [bV, Bχ, Bamp]
    calc
      _ ≤ Eφ n * (2 : ℝ) ^ (q + 2*n) * (H * D ^ (q+1)) * (Cseed n * D ^ (13 : ℕ)) *
          ((1 + (2 : ℝ) ^ q * (2 : ℝ) ^ n * G n) * D ^ e)^q :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hGrowth q)
          (by
            have hφ := zero_le_one.trans (hEφ n)
            have hSeedN := zero_le_one.trans (hCseed n)
            positivity)
      _ = _ := by
        dsimp only [V]
        rw [mul_pow, ← pow_mul]
        have hpow : D ^ (e*q+q+14) = D ^ (e*q) * D ^ (q+1) * D ^ (13 : ℕ) := by
          rw [show e*q+q+14 = (e*q+(q+1))+13 by omega, pow_add, pow_add]
        rw [hpow]
        ring
  have hVcap : bV ≤ V n * D ^ leadingTimeParentPower q e :=
    hV'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD (by unfold leadingTimeParentPower; rw [Nat.mul_succ]; omega)) (hV n))
  have hPcap : bP ≤ L n * D ^ leadingTimeParentPower q e := by
    dsimp only [bP, Bgen]
    calc
      _ ≤ (2 : ℝ) ^ (q+n) * (G n * D ^ e) * (V n * D ^ (e*q+q+14)) :=
        mul_le_mul_of_nonneg_left hV' (by have hGN := hG n; positivity)
      _ = _ := by
        dsimp only [L]
        have hpow : D ^ leadingTimeParentPower q e = D ^ e * D ^ (e*q+q+14) := by
          rw [← pow_add]
          congr 1
          unfold leadingTimeParentPower
          rw [Nat.mul_succ]
          omega
        rw [hpow]
        ring
  have hWeight (i : ℕ) : terminalTimeJetWeight T i ≤ 1 := by
    unfold terminalTimeJetWeight
    have hFact : (1 : ℝ) ≤ i.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos i)
    exact (div_le_one (by positivity)).2 ((pow_le_one₀ hT.le d.time_le_one).trans hFact)
  have hCount :
      (∑ i ∈ Finset.range (q+1), terminalTimeJetWeight T i) *
          ((hierarchyAdmissibleWords (Fin 4) n).card : ℝ) ≤ fixed n := by
    dsimp only [fixed]
    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
    calc
      _ ≤ ∑ _i ∈ Finset.range (q+1), (1 : ℝ) := Finset.sum_le_sum fun i _ => hWeight i
      _ = _ := by simp
  have hfPow := Real.rpow_nonneg hf₀ (-5/4 : ℝ)
  have h1 := HJ.1.trans
    (mul_le_mul hCount (mul_le_mul_of_nonneg_right hVcap hfPow)
      (mul_nonneg hBV hfPow) (by dsimp only [fixed]; positivity))
  have h2 := HJ.2.1.trans
    (mul_le_mul hCount (mul_le_mul_of_nonneg_right hPcap hfPow)
      (mul_nonneg hBP hfPow) (by dsimp only [fixed]; positivity))
  have h3 := HJ.2.2.trans
    (mul_le_mul hCount (mul_le_mul_of_nonneg_right hVcap hfPow)
      (mul_nonneg hBV hfPow) (by dsimp only [fixed]; positivity))
  refine ⟨(add_le_add h1 h2).trans_eq ?_, h3.trans ?_⟩
  · dsimp only [R, cost]; ring
  · dsimp only [R, cost]
    calc
      _ ≤ fixed n * (((V n + L n) * D ^ leadingTimeParentPower q e) * freq ^ (-5 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hL n)) (pow_nonneg hD₀ _)) hfPow)
          (by dsimp only [fixed]; positivity)
      _ = _ := by ring

end

end TorusEuler.InductiveEulerTip.SelectedLaterInput
