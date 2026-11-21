import TorusEuler.Paper.Proofs.S5b.T56Exact
import TorusEuler.Paper.Proofs.S5b.T56Coef
import TorusEuler.Paper.Proofs.S5b.T56Resid

/-!
# Theorem 5.6: the measured recurrence of an expansion

The induction of the proof of Theorem 5.6 (`sections/06c_finite_hierarchy.tex:521-637`) in the
bookkeeping of the library's `HierarchyNormRecurrence`: every ingredient of the TeX proof enters
through its estimate.

* the advection bounds (5.39) (`hD_1`, Lemma D.1, with the coefficient norms of Proposition 5.1
  `h5_1`: `T56Coef`) give the product terms of the sources (`T56Terms`);
* the mean equation (5.11) is solved with (5.12) of Proposition 5.2 (`h5_2`);
* the transverse equation (5.15) is solved with (5.21) of Lemma 5.3 (`h5_3`), and the seed `A₁`,
  `𝗉[A₁]` is bounded by (5.22) (`h5_3`);
* the completion is bounded by (5.31) and the relay `(∂_t+M)C[V] + 𝐝𝗉` by (5.32) of Lemma 5.5
  (`h5_5`), for `p = 2` through the leading clause of Lemma 5.5;
* the pulled-back parent residual by (5.6) and the composition clause (5.7) of Proposition 5.1
  (`h5_1`) with Bernstein's inequality (B.1) (`hB_1`) (`T56Resid`);
* Proposition 5.4 (`h5_4`) gives the vanishing of the levels before `t₀`, the supports,
  and `Y_{P+1} = Z_{P+1} = C_{P+1}` for the remainder (5.38).
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile

noncomputable section

/-- The norm setting of Section 5. -/
theorem normSetting_of {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
    {D lam t₀ : ℝ} {center : ℝ → Vec3} (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) (hO : S5.Origin T U X k D lam t₀ center) (a : ℕ) :
    NormSetting T (S5.radius D a) (S5.width lam) t₀ (S5.weight lam center) :=
  ⟨Bridge.Launch.end_pos hL, Bridge.radius_pos hP a, Bridge.width_pos hP, hL.start_nonneg,
    hL.start_lt.le, Bridge.Origin.weight_continuousOn hO, Bridge.Origin.weight_pos hP hO,
    Bridge.Origin.weight_le_one hO⟩

/-- The measured levels of the profiles `u` in the norms `Un`, `Wn`. -/
def measuredOf {T : ℝ} {k : Vec3} {ℓ h t₀ : ℝ} {γ : ℝ → ℝ} (st : NormSetting T ℓ h t₀ γ)
    (A : HierarchyOperators (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ))
    (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ))
    (P : ℕ) (cS R : HierarchyTwistedProfile T k Vec3) (lam : ℝ) (hf : 0 ≤ lam) :
    HierarchyMeasuredLevels :=
  HierarchyMeasuredLevels.ofProfiles A u P cS R lam hf
    (fun j => Un (k := k) st j) (fun j => Wn (k := k) st j) (fun j => Wn (E := ℝ) (k := k) st j)
    (fun j => apply_nonneg (Un (k := k) st j)) (fun j => apply_nonneg (Wn (k := k) st j))
    (fun j => apply_nonneg (Wn (E := ℝ) (k := k) st j))


section Master

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3} {D lam t₀ : ℝ}
  {center : ℝ → Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- The indices of the pairs entering the sources are levels of the expansion. -/
theorem pairs_mem {P shift p : ℕ} (hs : shift ≤ 1) (hp : p ∈ Finset.Icc 2 P) {ij : ℕ × ℕ}
    (hij : ij ∈ hierarchyLevelPairs P shift p) :
    ij.1 ∈ Finset.Icc 1 P ∧ ij.2 ∈ Finset.Icc 1 P := by
  obtain ⟨h1, h2, h3⟩ := levelPairs_spec hij
  obtain ⟨h4, h5⟩ := levelPairs_le hs hij
  have := Finset.mem_Icc.mp hp
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

set_option maxHeartbeats 16000000 in
/-- **The measured recurrence of an expansion** (the induction of the proof of Theorem 5.6,
`06c_finite_hierarchy.tex:521-637`, in the bookkeeping of `HierarchyNormRecurrence`): with
`ℓ_* = 𝖣^{-a}`, `L = 𝖣^c` and constants `K_H` independent of the parent and of the depth, the
measured levels `s'` (level-one oscillation: the norms of the unswitched leading pair `A₁`,
`𝗉[A₁]`) satisfy the recurrence through the order `H`. -/
theorem master_recurrence (hD_1 : Statement.lemma_D_1) (h5_1 : Statement.proposition_5_1)
    (h5_2 : Statement.proposition_5_2) (h5_3 : Statement.lemma_5_3)
    (h5_4 : Statement.proposition_5_4) (h5_5 : Statement.lemma_5_5)
    (hB_1 : Statement.lemma_B_1) :
    ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ (c : ℕ) (K : ℕ → ℝ) (KP : ℕ → ℕ → ℝ), (∀ H, 1 ≤ K H) ∧
      ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
        {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k)
        (χ : PaperWaveCutoff t₀ T) (hP : S5.Parent T U X pU D lam)
        (hL : S5.Launch T X k lam t₀) (hO : S5.Origin T U X k D lam t₀ center)
        {amp : ℝ → Vec3 → Vec3} (_hamp : S5.IsSeed U X k t₀ T center amp) {P : ℕ} (_hP2 : 2 ≤ P)
        {R S : HierarchyTwistedProfile T k Vec3}
        {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
        (_hu : S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u),
        ∃ (osc₁ : ℕ → ℝ) (h₁ : ∀ n, 0 ≤ osc₁ n),
          (∀ n, Wn (k := k) (normSetting_of hP hL hO a) n (u.V 1) +
              lam * Wn (E := ℝ) (k := k) (normSetting_of hP hL hO a) n (u.p 1) ≤ osc₁ n) ∧
          (∀ H, HierarchyNormRecurrence
            (measuredLevels' (measuredOf (normSetting_of hP hL hO a) (S5.ops d) u P
              (S5.curlCorrection d S) R lam (zero_le_one.trans hP.frequency_ge_one)) osc₁ h₁)
            lam (D ^ c) (K H) P H) ∧
          ((D ^ c) ^ 6 * lam ^ (-1 / 12 : ℝ) ≤ 1 → ∀ m : ℕ,
            S5.uNorm (S5.radius D a) (S5.width lam) m (S5.remainder (S5.ops d) u P) ≤
              KP m P * lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)) := by
  obtain ⟨Cc, Kc, hKc0, hcoef⟩ := coefBounds_of_h5_1 h5_1
  obtain ⟨Cr, Kr, hres⟩ := residual_uNorm h5_1 hB_1
  obtain ⟨a₂, h2⟩ := h5_2
  obtain ⟨a₃, h3⟩ := h5_3
  obtain ⟨a₄, h4⟩ := h5_4
  obtain ⟨a₅, h5⟩ := h5_5
  refine ⟨max (max (max a₂ a₃) (max a₄ a₅)) (max (max Cc Cr) 3), fun a ha => ?_⟩
  simp only [max_le_iff] at ha
  obtain ⟨⟨⟨ha2, ha3⟩, ha4, ha5⟩, ⟨haCc, haCr⟩, haa⟩ := ha
  obtain ⟨C₂, K₂, h2'⟩ := h2 a ha2
  obtain ⟨C₃, K₃, h3'⟩ := h3 a ha3
  obtain ⟨C₅, K₅, h5'⟩ := h5 a ha5
  let ψ : ℕ → ℝ := fun n => 6 * productConst n ^ 2 * Kc n + max (K₂ n) 0 + max (K₃ n) 0 +
    max (K₅ n) 0 + max (Kr n) 0
  have hψ0 : ∀ n, 0 ≤ ψ n := fun n => by
    have := productConst_nonneg n
    have := hKc0 n
    have := le_max_right (K₂ n) 0
    have := le_max_right (K₃ n) 0
    have := le_max_right (K₅ n) 0
    have := le_max_right (Kr n) 0
    dsimp only [ψ]
    positivity
  let K : ℕ → ℝ := fun H => 1 + ∑ n ∈ Finset.range (H + 1), ψ n
  have hK1 : ∀ H, 1 ≤ K H := fun H =>
    le_add_of_nonneg_right (Finset.sum_nonneg fun n _ => hψ0 n)
  have hKψ : ∀ H n, n ≤ H → ψ n ≤ K H := fun H n hn =>
    (Finset.single_le_sum (f := ψ) (fun n _ => hψ0 n) (Finset.mem_range.mpr (by omega))).trans
      (le_add_of_nonneg_left zero_le_one)
  let F₁ : ℕ → Finset (ℕ × ℕ) := fun P =>
    (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter (fun ij => P + 1 ≤ ij.1 + ij.2)
  let F₂ : ℕ → Finset (ℕ × ℕ) := fun P =>
    (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter (fun ij => P + 2 ≤ ij.1 + ij.2)
  let AP : ℕ → ℕ → ℝ := fun m P => hierarchyLevelConstant P (K (m + 1 + 3 * P)) P
  let KPfun : ℕ → ℕ → ℝ := fun m P =>
    2 * K (m + 1 + 3 * P) * AP m P ^ 2 * (1 + ((F₁ P).card : ℝ) + 2 * ((F₂ P).card : ℝ)) +
      2 * (P : ℝ) * AP m P
  refine ⟨Cc + a + C₂ + C₃ + C₅ + 1, K, KPfun, hK1, ?_⟩
  intro T hT U X pU k D lam t₀ center d χ hP hL hO amp hamp P hP2 R S u hu
  -- standing facts
  set ℓ := S5.radius D a with hℓdef
  set h := S5.width lam with hhdef
  set γ := S5.weight lam center with hγdef
  have hD : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hℓ : 0 < ℓ := Bridge.radius_pos hP a
  have hfit : 2 * ℓ < 1 / 2 := Bridge.radius_fits hP.scale_ge_two haa
  have hh : 0 < h := Bridge.width_pos hP
  have hh₁ : h ≤ 1 := Bridge.width_le_one hP
  have hγpos := Bridge.Origin.weight_pos hP hO
  have hγc := Bridge.Origin.weight_continuousOn hO
  have hγ1 := Bridge.Origin.weight_le_one hO
  have st : NormSetting T ℓ h t₀ γ := normSetting_of hP hL hO a
  have hℓCc : ℓ ≤ (D ^ Cc)⁻¹ := inv_anti₀ (pow_pos hD0 _) (pow_le_pow_right₀ hD haCc)
  have hℓCr : ℓ ≤ (D ^ Cr)⁻¹ := inv_anti₀ (pow_pos hD0 _) (pow_le_pow_right₀ hD haCr)
  have hactive : Icc t₀ T ⊆ Icc 0 T := Bridge.Launch.active_subset hL
  -- the coefficient norms
  have hc : CoefBounds T ℓ h X k (fun n => Kc n * D ^ Cc) (fun n => Kc n * D ^ Cc * lam) :=
    hcoef hT hP hL hℓ hℓCc
  -- the constants `K L`
  set c := Cc + a + C₂ + C₃ + C₅ + 1 with hcdef
  set L := D ^ c with hLdef
  have hL1 : 1 ≤ L := one_le_pow₀ hD
  have hLpow (e : ℕ) (he : e ≤ c) : D ^ e ≤ L := pow_le_pow_right₀ hD he
  have hf : 0 ≤ lam := hlam0.le
  have hKL0 (H : ℕ) : 0 ≤ K H * L := mul_nonneg (zero_le_one.trans (hK1 H)) (zero_le_one.trans hL1)
  have hlam32 : 1 ≤ lam ^ (3 / 2 : ℝ) := Real.one_le_rpow hlam (by norm_num)
  have hlam32' : 0 ≤ lam ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlam0.le _
  -- the coefficients of the products
  have hlab (H n : ℕ) (hn : n ≤ H) : 2 * labelConst ℓ (fun n => Kc n * D ^ Cc) n ≤ K H * L := by
    have hl1 : labelConst ℓ (fun n => Kc n * D ^ Cc) n =
        3 * productConst n ^ 2 * Kc n * (D ^ Cc * D ^ a) := by
      unfold labelConst
      rw [hℓdef, S5.radius, inv_inv]
      ring
    have h1 : D ^ Cc * D ^ a ≤ L := by
      rw [← pow_add]; exact hLpow _ (by omega)
    have h2 := hKψ H n hn
    have h3 : 6 * productConst n ^ 2 * Kc n ≤ ψ n := by
      have := le_max_right (K₂ n) 0
      have := le_max_right (K₃ n) 0
      have := le_max_right (K₅ n) 0
      have := le_max_right (Kr n) 0
      dsimp only [ψ]
      linarith
    have h4 : 0 ≤ 3 * productConst n ^ 2 * Kc n := by
      have := productConst_nonneg n; have := hKc0 n; positivity
    rw [hl1]
    calc 2 * (3 * productConst n ^ 2 * Kc n * (D ^ Cc * D ^ a))
        = (6 * productConst n ^ 2 * Kc n) * (D ^ Cc * D ^ a) := by ring
      _ ≤ ψ n * L := mul_le_mul h3 h1 (by positivity) (hψ0 n)
      _ ≤ K H * L := mul_le_mul_of_nonneg_right h2 (zero_le_one.trans hL1)
  have hphase (H n : ℕ) (hn : n ≤ H) :
      2 * phaseConst h (fun n => Kc n * D ^ Cc * lam) n ≤ K H * L * lam ^ (3 / 2 : ℝ) := by
    have hp1 : phaseConst h (fun n => Kc n * D ^ Cc * lam) n =
        productConst n ^ 2 * Kc n * D ^ Cc * lam ^ (3 / 2 : ℝ) := by
      unfold phaseConst
      rw [hhdef, width_inv hlam0, rpow_three_halves hlam0]
      ring
    have h1 : D ^ Cc ≤ L := hLpow _ (by omega)
    have h2 := hKψ H n hn
    have h3 : 2 * productConst n ^ 2 * Kc n ≤ ψ n := by
      have := le_max_right (K₂ n) 0
      have := le_max_right (K₃ n) 0
      have := le_max_right (K₅ n) 0
      have := le_max_right (Kr n) 0
      have := productConst_nonneg n; have := hKc0 n
      dsimp only [ψ]
      nlinarith [sq_nonneg (productConst n), mul_nonneg (sq_nonneg (productConst n)) (hKc0 n)]
    rw [hp1]
    calc 2 * (productConst n ^ 2 * Kc n * D ^ Cc * lam ^ (3 / 2 : ℝ))
        = (2 * productConst n ^ 2 * Kc n * D ^ Cc) * lam ^ (3 / 2 : ℝ) := by ring
      _ ≤ (ψ n * L) * lam ^ (3 / 2 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hlam32'
        have : 0 ≤ 2 * productConst n ^ 2 * Kc n := by
          have := productConst_nonneg n; have := hKc0 n; positivity
        calc 2 * productConst n ^ 2 * Kc n * D ^ Cc ≤ ψ n * D ^ Cc :=
              mul_le_mul_of_nonneg_right h3 (pow_nonneg hD0.le _)
          _ ≤ ψ n * L := mul_le_mul_of_nonneg_left h1 (hψ0 n)
      _ ≤ K H * L * lam ^ (3 / 2 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hlam32'
        exact mul_le_mul_of_nonneg_right h2 (zero_le_one.trans hL1)

  -- Proposition 5.4: vanishing and supports
  obtain ⟨-, h4r⟩ := h4 a ha4 hT d χ hP hL hO
  obtain ⟨-, -, h4id⟩ := h4r amp hamp P hP2
  obtain ⟨-, -, -, -, -, hsuppF, hvan, hYP, hZP, -⟩ := h4id R S u hu
  set A := S5.ops d with hAdef
  set cS := S5.curlCorrection d S with hcSdef
  have hP1 : 1 ≤ P := by omega
  have vanV : ∀ i ∈ Finset.Icc 1 P, VanishBefore t₀ (u.V i) := fun i hi t ht hpre x s =>
    ((hvan t ht hpre x s).1 i hi).1
  have vanY : ∀ i ∈ Finset.Icc 1 P, VanishBefore t₀ (u.Y i) := fun i hi t ht hpre x s => by
    have hi' := Finset.mem_Icc.mp hi
    have h1 := ((hvan t ht hpre x s).1 i hi).1
    have h2 := (hvan t ht hpre x s).2.1 i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
    change (u.V i + u.C (i - 1)).val.val.val (t, x, s) = 0
    have h2' : (u.C (i - 1)).val.val.val (t, x, s) = 0 := h2
    rw [eval_add, h1, h2', add_zero]
  have vanC : ∀ i ∈ Finset.Icc 1 P, VanishBefore t₀ (u.C (i - 1)) := fun i hi t ht hpre x s => by
    have hi' := Finset.mem_Icc.mp hi
    exact (hvan t ht hpre x s).2.1 i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
  -- the levels of the expansion
  have hC0 : u.C 0 = 0 := hu.first_correction
  have hCcorr : ∀ i ∈ Finset.Icc 1 P, u.C i = S5.curlCorrection d (u.V i) := fun i hi =>
    hu.correction i hi
  have hcS : A.average cS = 0 := Bridge.ops_average_curlCorrection d S
  have hVavg1 : A.average (u.V 1) = 0 := average_first hL hamp hℓ hfit hh hh₁ hu
  have hmem2 (i : ℕ) (hi : i ∈ Finset.Icc 1 P) (hne : ¬ i = 1) : i ∈ Finset.Icc 2 P :=
    Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hi).1; omega, (Finset.mem_Icc.mp hi).2⟩
  have hVall : ∀ i ∈ Finset.Icc 1 P, A.average (u.V i) = 0 := fun i hi => by
    by_cases h1 : i = 1
    · subst h1; exact hVavg1
    · exact (hu.transverse i (hmem2 i hi h1)).mean_zero
  have hTr : ∀ i ∈ Finset.Icc 1 P, ∀ t ∈ Icc 0 T, ∀ a s,
      ⟪S5.waveVector X k t a, (u.V i).val.val.val (t, a, s)⟫_ℝ = 0 := fun i hi => by
    by_cases h1 : i = 1
    · subst h1; exact V1_transverse d hL hamp hℓ hfit hh hh₁ hu
    · exact (hu.transverse i (hmem2 i hi h1)).transverse
  have hPm : ∀ i ∈ Finset.Icc 1 P, ∀ t ∈ Icc 0 T, ∀ a,
      phaseMean (fun r => (u.p i).val.val.val (t, a, r)) = 0 := fun i hi => by
    by_cases h1 : i = 1
    · subst h1; exact p1_phaseMean hP d hL hamp hℓ hfit hh hh₁ hu
    · exact (hu.transverse i (hmem2 i hi h1)).pressure_mean_zero
  have hBall : ∀ i ∈ Finset.Icc 1 P, A.average (u.B i) = u.B i := fun i hi => by
    by_cases h1 : i = 1
    · subst h1; rw [hu.first_mean.1, map_zero]
    · exact (hu.mean i (hmem2 i hi h1)).1.phase_independent
  have hexact := average_sourceBeforeMean_eq hP d cS hcS hC0 hCcorr hVall hBall hTr hPm
  -- the level-one pair of Lemma 5.5
  obtain ⟨V, q, hVq, hVavg, -, -, -, hrel⟩ := (h5' hT d hP hL hO).2 amp hamp
  have hVcell : ∀ t ∈ Icc t₀ T, ∀ x ∈ centeredCell, ∀ s,
      V.val.val.val (t, x, s) = S5.leading ℓ h amp t x s := fun t ht x hx s => (hVq t ht x hx s).1
  have hqcell : ∀ t ∈ Icc t₀ T, ∀ x ∈ centeredCell, ∀ s,
      q.val.val.val (t, x, s) = S5.leadingPressure U X k ℓ h amp t x s :=
    fun t ht x hx s => (hVq t ht x hx s).2
  have hSavg : A.average S = 0 := activation_average d hℓ hfit hh hh₁ hu
  let osc₁ : ℕ → ℝ := fun n => Wn (k := k) st n V + lam * Wn (E := ℝ) (k := k) st n q
  have h₁ : ∀ n, 0 ≤ osc₁ n := fun n =>
    add_nonneg (apply_nonneg _ _) (mul_nonneg hlam0.le (apply_nonneg _ _))
  have hcabs : ∀ t ∈ Icc t₀ T, |χ.value t| ≤ 1 := fun t ht => χ.abs_le_one (hactive ht)
  have hV1le : ∀ n, Wn (k := k) st n (u.V 1) ≤ Wn (k := k) st n V := fun n =>
    wNorm_smul_time_le hT hL.start_nonneg hL.start_lt.le hγc hγpos hcabs
      (fun t ht x s => V1_eq_smul d hu V hVcell t (hactive ht) x s) n
  have hp1le : ∀ n, Wn (E := ℝ) (k := k) st n (u.p 1) ≤ Wn (E := ℝ) (k := k) st n q := fun n =>
    wNorm_smul_time_le hT hL.start_nonneg hL.start_lt.le hγc hγpos hcabs
      (fun t ht x s => by
        rw [p1_eq_smul d hu q hqcell t (hactive ht) x s, smul_eq_mul]) n
  have hle : ∀ n, Wn (k := k) st n (u.V 1) + lam * Wn (E := ℝ) (k := k) st n (u.p 1) ≤ osc₁ n :=
    fun n => add_le_add (hV1le n) (mul_le_mul_of_nonneg_left (hp1le n) hlam0.le)
  -- the norms of the leading pair, (5.22)
  have hlead0 : ∀ t ∈ Icc t₀ T, ∀ x s, 2 * ℓ ≤ ‖x‖ → S5.leading ℓ h amp t x s = 0 :=
    fun t ht x s hx => by
      simp only [S5.leading, radialEnvelope_eq_zero hℓ hx, zero_mul, zero_smul]
  have hlead1 : ∀ t ∈ Icc t₀ T, ∀ x s, 2 * ℓ ≤ ‖x‖ →
      S5.leadingPressure U X k ℓ h amp t x s = 0 := fun t ht x s hx => by
    unfold S5.leadingPressure wavePressureCoefficient
    simp [radialEnvelope_eq_zero hℓ hx]
  have hseedn : ∀ n, osc₁ n ≤ K₃ n * D ^ C₃ * lam ^ (-5 / 4 : ℝ) := fun n => by
    have hVn := twisted_wNorm_le (h := h) hT hL.start_nonneg hL.start_lt.le hℓ hfit V hVcell hlead0 hγc
      hγpos n
    have hqn := twisted_wNorm_le (h := h) hT hL.start_nonneg hL.start_lt.le hℓ hfit q hqcell hlead1 hγc
      hγpos n
    exact (add_le_add hVn (mul_le_mul_of_nonneg_left hqn hlam0.le)).trans
      ((h3' hT d hP hL hO).2.2.2 n amp hamp)

  -- the coefficient bounds
  have hψge : ∀ n, max (K₂ n) 0 ≤ ψ n ∧ max (K₃ n) 0 ≤ ψ n ∧ max (K₅ n) 0 ≤ ψ n ∧
      max (Kr n) 0 ≤ ψ n := fun n => by
    have := productConst_nonneg n; have := hKc0 n
    have := le_max_right (K₂ n) 0; have := le_max_right (K₃ n) 0
    have := le_max_right (K₅ n) 0; have := le_max_right (Kr n) 0
    have : 0 ≤ 6 * productConst n ^ 2 * Kc n := by positivity
    dsimp only [ψ]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hK₂ : ∀ H n, n ≤ H → K₂ n * D ^ C₂ ≤ K H * L := fun H n hn =>
    mul_le_mul ((le_max_left _ _).trans ((hψge n).1.trans (hKψ H n hn))) (hLpow C₂ (by omega))
      (pow_nonneg hD0.le _) (zero_le_one.trans (hK1 H))
  have hK₃ : ∀ H n, n ≤ H → K₃ n * D ^ C₃ ≤ K H * L := fun H n hn =>
    mul_le_mul ((le_max_left _ _).trans ((hψge n).2.1.trans (hKψ H n hn))) (hLpow C₃ (by omega))
      (pow_nonneg hD0.le _) (zero_le_one.trans (hK1 H))
  have hK₅ : ∀ H n, n ≤ H → K₅ n * D ^ C₅ ≤ K H * L := fun H n hn =>
    mul_le_mul ((le_max_left _ _).trans ((hψge n).2.2.1.trans (hKψ H n hn))) (hLpow C₅ (by omega))
      (pow_nonneg hD0.le _) (zero_le_one.trans (hK1 H))
  have hKr : ∀ H n, n ≤ H → Kr n ≤ K H := fun H n hn =>
    (le_max_left _ _).trans ((hψge n).2.2.2.trans (hKψ H n hn))
  -- relay at level two (the leading clause of Lemma 5.5)
  have hrel2 : ∀ n, Wn (k := k) st n (A.relayAtLevel u cS 2) ≤
      K₅ n * D ^ C₅ * lam⁻¹ * Wn (k := k) st (n + 1) V := fun n => by
    have h1 : Wn (k := k) st n (A.relayAtLevel u cS 2) ≤
        Wn (k := k) st n (A.material (S5.curlCorrection d V) + A.labelGrad q) :=
      wNorm_smul_time_le hT hL.start_nonneg hL.start_lt.le hγc hγpos hcabs
        (fun t ht x s => relay_two_eq d hu V q hVcell hqcell hVavg hVavg1 hSavg hP1 t
          (hactive ht) x s) n
    exact h1.trans (hrel n)
  have hVle : ∀ n, Wn (k := k) st n V ≤ osc₁ n := fun n =>
    le_add_of_nonneg_right (mul_nonneg hlam0.le (apply_nonneg _ _))
  set s := measuredOf st A u P cS R lam hf with hsdef
  have hsosc : ∀ n p, s.osc n p = Wn (k := k) st n (u.V p) +
      lam * Wn (E := ℝ) (k := k) st n (u.p p) := fun _ _ => rfl
  have hsmean : ∀ n p, s.mean n p = Un (k := k) st n (u.B p) := fun _ _ => rfl
  have hscompl : ∀ n p, s.completion n p = Wn (k := k) st n (u.C p) := fun _ _ => rfl
  have hsY : ∀ n p, s.Y n p = Wn (k := k) st n (u.Y p) := fun _ _ => rfl
  have hsZ : ∀ n p, s.Z n p = Wn (k := k) st n (u.Y p) + Un (k := k) st n (u.B p) :=
    fun _ _ => rfl
  have hp1ne : ∀ p ∈ Finset.Icc 2 P, p ≠ 1 := fun p hp => by
    have := (Finset.mem_Icc.mp hp).1; omega
  have hsOscSrc : ∀ n, ∀ p ∈ Finset.Icc 2 P, s.oscSource n p =
      Wn (k := k) st n (S5.oscSource A u cS p + S5.suppSource A u p) := fun n p hp => by
    have hpP := (Finset.mem_Icc.mp hp).2
    change (if p = 1 then 0 else Wn (k := k) st n (-(A.sourceBeforeMean u P cS p -
      A.average (A.sourceBeforeMean u P cS p)) - hierarchyAdvectionAtLevel P 1 p
        (A.meanPhaseProduct u))) = _
    simp only [hp1ne p hp, ↓reduceIte]
    rw [Bridge.oscSource_add_suppSource_eq A u cS hpP]
  have hsMeanSrc : ∀ n, ∀ p ∈ Finset.Icc 2 P, s.meanSource n p =
      Un (k := k) st n (S5.meanSource A u cS R p) := fun n p hp => by
    have hpP := (Finset.mem_Icc.mp hp).2
    change (if p = 1 then 0 else Un (k := k) st n (-A.average (A.sourceBeforeMean u P cS p) -
      (if p = 2 then R else 0))) = _
    simp only [hp1ne p hp, ↓reduceIte]
    rw [Bridge.meanSource_eq A u cS R hpP]
  have hsOscSrc1 : ∀ n, s.oscSource n 1 = 0 := fun n => by
    simp [hsdef, measuredOf, HierarchyMeasuredLevels.ofProfiles]
  have hs'1 : ∀ n, (measuredLevels' s osc₁ h₁).osc n 1 = osc₁ n := fun n => by
    simp [measuredLevels']
  have hs'ne : ∀ n, ∀ p ∈ Finset.Icc 2 P, (measuredLevels' s osc₁ h₁).osc n p = s.osc n p :=
    fun n p hp => measuredLevels'_osc_of_ne s osc₁ h₁ (hp1ne p hp) n
  -- 

  have hlc' (H n : ℕ) (hn : n ≤ H) : labelConst ℓ (fun n => Kc n * D ^ Cc) n ≤ K H * L := by
    have := labelConst_nonneg hc hℓ n
    have := hlab H n hn
    linarith
  have hpc' (H n : ℕ) (hn : n ≤ H) :
      phaseConst h (fun n => Kc n * D ^ Cc * lam) n ≤ K H * L * lam ^ (3 / 2 : ℝ) := by
    have := phaseConst_nonneg hc hh n
    have := hphase H n hn
    linarith
  have hrelayAll : ∀ H n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 (P + 1),
      Wn (k := k) st n (A.relayAtLevel u cS p) ≤ K H * L * (lam ^ (-1 : ℝ) *
        ((measuredLevels' s osc₁ h₁).osc (n + 1) (p - 1) + s.oscSource (n + 1) (p - 1))) :=
    fun H n hn p hp => by
    rw [Real.rpow_neg_one]
    have hp' := Finset.mem_Icc.mp hp
    by_cases h2 : p = 2
    · subst h2
      rw [show (2 : ℕ) - 1 = 1 from rfl, hs'1, hsOscSrc1, add_zero]
      refine (hrel2 n).trans ?_
      calc K₅ n * D ^ C₅ * lam⁻¹ * Wn (k := k) st (n + 1) V
          ≤ (K H * L * lam⁻¹) * osc₁ (n + 1) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (hK₅ H n (by omega))
              (inv_nonneg.mpr hlam0.le)) (hVle _) (apply_nonneg _ _) ?_
            exact mul_nonneg (hKL0 H) (inv_nonneg.mpr hlam0.le)
        _ = _ := by ring
    · have hp1 : p - 1 ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hp1' : p - 1 ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hts := hu.transverse (p - 1) hp1
      have hrelayEq : A.relayAtLevel u cS p =
          A.material (S5.curlCorrection d (u.V (p - 1))) + A.labelGrad (u.p (p - 1)) := by
        unfold HierarchyOperators.relayAtLevel
        simp only [h2, ↓reduceIte, sub_zero]
        rw [hCcorr (p - 1) hp1']
      rw [hrelayEq]
      have h532 := (((h5' hT d hP hL hO).1 n (u.V (p - 1)) (hVall _ hp1')
        (fun t ht x s => hTr _ hp1' t (hactive ht) x s)).2
        (S5.oscSource A u cS (p - 1) + S5.suppSource A u (p - 1)) (u.p (p - 1))
        (transverse_average_source d hts) (fun t ht x => hPm _ hp1' t (hactive ht) x)
        (fun t ht x s => by rw [hts.momentum]))
      have hosc : Wn (k := k) st (n + 1) (u.V (p - 1)) ≤
          (measuredLevels' s osc₁ h₁).osc (n + 1) (p - 1) := by
        rw [hs'ne _ _ hp1, hsosc]
        exact le_add_of_nonneg_right (mul_nonneg hlam0.le (apply_nonneg _ _))
      have hsrc : Wn (k := k) st (n + 1) (S5.oscSource A u cS (p - 1) + S5.suppSource A u (p - 1)) =
          s.oscSource (n + 1) (p - 1) := (hsOscSrc _ _ hp1).symm
      refine h532.trans ?_
      rw [← hsrc] at *
      calc K₅ n * D ^ C₅ * lam⁻¹ * (Wn (k := k) st (n + 1) (u.V (p - 1)) +
            Wn (k := k) st (n + 1) (S5.oscSource A u cS (p - 1) + S5.suppSource A u (p - 1)))
          ≤ (K H * L * lam⁻¹) * ((measuredLevels' s osc₁ h₁).osc (n + 1) (p - 1) +
            Wn (k := k) st (n + 1) (S5.oscSource A u cS (p - 1) + S5.suppSource A u (p - 1))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (hK₅ H n (by omega))
              (inv_nonneg.mpr hlam0.le)) (add_le_add hosc le_rfl)
              (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) ?_
            exact mul_nonneg (hKL0 H) (inv_nonneg.mpr hlam0.le)
        _ = _ := by ring
  have hrec : ∀ H, HierarchyNormRecurrence (measuredLevels' s osc₁ h₁) lam L (K H) P H := fun H => by
    have hlc : ∀ n, n ≤ H → labelConst ℓ (fun n => Kc n * D ^ Cc) n ≤ K H * L := fun n hn => hlc' H n hn
    have hpc : ∀ n, n ≤ H → phaseConst h (fun n => Kc n * D ^ Cc * lam) n ≤ K H * L * lam ^ (3 / 2 : ℝ) := fun n hn => hpc' H n hn
    have hseedH : ∀ n ≤ H, osc₁ n ≤ K H * L * lam ^ hierarchyOscExponent 1 := fun n hn => by
      have he : hierarchyOscExponent 1 = -5 / 4 := by norm_num [hierarchyOscExponent]
      rw [he]
      exact (hseedn n).trans (mul_le_mul_of_nonneg_right (hK₃ H n hn) (Real.rpow_nonneg hlam0.le _))
    -- the mean source: (5.39)
    have hYY : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
        Un (k := k) st n (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2))) ≤
          K H * L * (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2) := fun n hn p hp ij hij => by
      obtain ⟨hi1, hi2⟩ := pairs_mem (shift := 0) (by norm_num) hp hij
      rw [hsY, hsY]
      exact (term_YY hD_1 st d hc n (vanY _ hi1) (vanY _ hi2)).trans
        (mul_le_mul_of_nonneg_right (hlc n (by omega))
          (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
    have hdivY : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
        Un (k := k) st n (A.average (slowLabelDivergenceProduct hT d.inverse (u.V ij.1) (u.Y ij.2))) ≤
          K H * L * (s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2) := fun n hn p hp ij hij => by
      obtain ⟨hi1, hi2⟩ := pairs_mem (shift := 0) (by norm_num) hp hij
      rw [hsY, hsosc]
      refine (term_divY hD_1 st d hc n (vanV _ hi1) (vanY _ hi2)).trans
        (mul_le_mul (hlc n (by omega)) (mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ _))
          (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (hKL0 H))
      exact le_add_of_nonneg_right (mul_nonneg hlam0.le (apply_nonneg _ _))
    have hBB : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
        Un (k := k) st n (A.labelAdv (u.B ij.1) (u.B ij.2)) ≤
          K H * L * (s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2) := fun n hn p hp ij hij => by
      rw [hsmean, hsmean]
      exact (term_BB hD_1 st d hc n (u.B ij.1) (u.B ij.2)).trans
        (mul_le_mul_of_nonneg_right (hlc n (by omega))
          (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
    have hresH : ∀ n, n + 1 ≤ H → Un (k := k) st n R ≤
        K H * lam ^ hierarchyMeanExponent 2 := fun n hn => by
      have he : hierarchyMeanExponent 2 = -5 / 2 := by norm_num [hierarchyMeanExponent]
      rw [he]
      exact (hres hT hP hL hℓ hℓCr R hu.residual n).trans
        (mul_le_mul_of_nonneg_right (hKr H n (by omega)) (Real.rpow_nonneg hlam0.le _))
    -- the mean solve: (5.12)
    have hmeanSolve : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P,
        s.mean n p ≤ K H * L * s.meanSource (n + 1) p := fun n hn p hp => by
      rw [hsmean, hsMeanSrc _ p hp]
      exact (h2' hT d hP (S5.meanSource A u cS R p) (u.B p) (u.q p) (hu.mean p hp).1 n).trans
        (mul_le_mul_of_nonneg_right (hK₂ H n (by omega)) (apply_nonneg (Un (k := k) st (n + 1)) _))
    -- the transverse solve: (5.21)
    have hoscSolve : ∀ n ≤ H, ∀ p ∈ Finset.Icc 2 P, s.osc n p ≤ K H * L * s.oscSource n p :=
      fun n hn p hp => by
      rw [hsosc, hsOscSrc _ p hp]
      have hts := hu.transverse p hp
      refine ((h3' hT d hP hL hO).2.2.1 n _ (u.V p) (u.p p) (transverse_average_source d hts)
        (fun t ht x s hx => ?_) hts).trans
        (mul_le_mul_of_nonneg_right (hK₃ H n hn) (apply_nonneg (Wn (k := k) st n) _))
      rcases hx with hpre | hoff
      · exact ((hvan t ht hpre x s).2.2 p hp)
      · exact hsuppF p hp t ht x hoff s
    -- the completion: (5.31)
    have hcomplete : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 1 P,
        Wn (k := k) st n (u.C p) ≤ K H * L * lam ^ (-1 : ℝ) *
          (measuredLevels' s osc₁ h₁).osc (n + 1) p := fun n hn p hp => by
      rw [Real.rpow_neg_one, hCcorr p hp]
      have h531 := ((h5' hT d hP hL hO).1 n (u.V p) (hVall p hp) (fun t ht x s => hTr p hp t
        (hactive ht) x s)).1
      have hVp : Wn (k := k) st (n + 1) (u.V p) ≤ (measuredLevels' s osc₁ h₁).osc (n + 1) p := by
        by_cases h1 : p = 1
        · subst h1; rw [hs'1]; exact (hV1le _).trans (hVle _)
        · rw [hs'ne _ p (hmem2 p hp h1), hsosc]
          exact le_add_of_nonneg_right (mul_nonneg hlam0.le (apply_nonneg _ _))
      refine h531.trans ?_
      calc K₅ n * D ^ C₅ * lam⁻¹ * Wn (k := k) st (n + 1) (u.V p)
          ≤ K H * L * lam⁻¹ * (measuredLevels' s osc₁ h₁).osc (n + 1) p := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (hK₅ H n (by omega))
              (inv_nonneg.mpr hlam0.le)) hVp (apply_nonneg _ _) ?_
            exact mul_nonneg (hKL0 H) (inv_nonneg.mpr hlam0.le)
        _ = _ := by ring
    have hV1H : ∀ n ≤ H, Wn (k := k) st n (u.V 1) ≤ osc₁ n := fun n _ =>
      (hV1le n).trans (hVle n)

    have hrelayMean : ∀ p ∈ Finset.Icc 2 P, A.average (A.relayAtLevel u cS p) = 0 := fun p hp => by
      have hp' := Finset.mem_Icc.mp hp
      have hp1 : p - 1 ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact average_relayAtLevel_eq_zero hT d.inverse d.strain d.covector
        d.mean.inverse_independent (PhysicalApproximationData.parentStrain_phaseIndependent (d := d)) u cS p
        (expansion_average_C d hu (Finset.mem_Icc.mp hp1).2) (hPm (p - 1) hp1) hcS
    -- the relay: (5.32) and the leading clause of Lemma 5.5
    have hrelay : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, Wn (k := k) st n (A.relayAtLevel u cS p) ≤ K H * L * (lam ^ (-1 : ℝ) * ((measuredLevels' s osc₁ h₁).osc (n + 1) (p - 1) + s.oscSource (n + 1) (p - 1))) := fun n hn p hp => hrelayAll H n hn p (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp).1, by have := (Finset.mem_Icc.mp hp).2; omega⟩)
    -- the centered slow and fast products
    have hslow : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 0 p,
        Wn (k := k) st n (A.labelProduct u ij - A.average (A.labelProduct u ij)) ≤
          K H * L * (s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2) := fun n hn p hp ij hij => by
      obtain ⟨hi1, hi2⟩ := pairs_mem (shift := 0) (by norm_num) hp hij
      rw [hsZ, hsZ]
      have hb := term_slow hD_1 st d hc n (Y := u.Y ij.1) (Y' := u.Y ij.2) (hBall _ hi1) (hBall _ hi2)
      exact hb.trans (mul_le_mul_of_nonneg_right (hlab H n (by omega))
        (mul_nonneg (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
          (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))))
    have hfast : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 1 p,
        Wn (k := k) st n (A.completionPhaseProduct u ij - A.average (A.completionPhaseProduct u ij)) ≤
          (K H * L * lam ^ (3 / 2 : ℝ)) * (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2) :=
      fun n hn p hp ij hij => by
      rw [hscompl, hsY]
      exact (term_fastC hD_1 st d hc n (u.C (ij.1 - 1)) (u.Y ij.2)).trans
        (mul_le_mul_of_nonneg_right (hphase H n (by omega))
          (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
    have hmeanPhase : ∀ n, n + 1 ≤ H → ∀ p ∈ Finset.Icc 2 P, ∀ ij ∈ hierarchyLevelPairs P 1 p,
        Wn (k := k) st n (A.meanPhaseProduct u ij) ≤
          (K H * L * lam ^ (3 / 2 : ℝ)) * (s.mean n ij.1 * s.Y (n + 1) ij.2) :=
      fun n hn p hp ij hij => by
      rw [hsmean, hsY]
      exact (term_fastB hD_1 st d hc n (u.B ij.1) (u.Y ij.2)).trans
        (mul_le_mul_of_nonneg_right (hpc n (by omega))
          (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
    exact normRecurrence' A u cS R hf (fun n => Un (k := k) st n) (fun n => Wn (k := k) st n)
      (fun n => Wn (E := ℝ) (k := k) st n)
      (fun i j => slowLabelDivergenceProduct hT d.inverse (u.V i) (u.Y j)) osc₁ h₁ (hKL0 H) hle
      hseedH hu.first_mean.1 hC0 hexact hYY hdivY hBB hresH hmeanSolve hrelayMean hrelay hslow
      hfast hmeanPhase hoscSolve hcomplete hV1H
  -- the remainder (5.38)
  refine ⟨osc₁, h₁, hle, hrec, fun hL6 m => ?_⟩
  have hL6' : L ^ 6 ≤ lam ^ (1 / 12 : ℝ) := by
    calc L ^ 6 = (L ^ 6 * lam ^ (-1 / 12 : ℝ)) * lam ^ (1 / 12 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hlam0]; norm_num
      _ ≤ 1 * lam ^ (1 / 12 : ℝ) := mul_le_mul_of_nonneg_right hL6 (Real.rpow_nonneg hlam0.le _)
      _ = _ := one_mul _
  have habs : ∀ (mL : ℕ), mL ≤ 6 → ∀ x : ℝ, x + 1 / 12 ≤ -5 / 4 - 2 * (P : ℝ) / 3 →
      L ^ mL * lam ^ x ≤ lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3) := fun mL hm x hx => by
    have h1 : L ^ mL ≤ lam ^ (1 / 12 : ℝ) := (pow_le_pow_right₀ hL1 hm).trans hL6'
    calc L ^ mL * lam ^ x ≤ lam ^ (1 / 12 : ℝ) * lam ^ x :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hlam0.le _)
      _ = lam ^ (1 / 12 + x) := (Real.rpow_add hlam0 _ _).symm
      _ ≤ lam ^ (-5 / 4 - 2 * (P : ℝ) / 3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlam (by linarith)
      _ = _ := by rw [← Real.rpow_add hlam0]; congr 1; ring
  have hlevP : ∀ m, ∀ n ≤ m + 1, ∀ p ∈ Finset.Icc 1 P,
      HierarchyLevelBound (measuredLevels' s osc₁ h₁) lam L (AP m P) n p := fun m n hn p hp =>
    hierarchy_level_bounds_through_depth (hrec (m + 1 + 3 * P)) hlam hL1 (hK1 _) hL6 n hn p hp
  have hlv := hlevP m
  have hKH0 : 0 ≤ K (m + 1 + 3 * P) := zero_le_one.trans (hK1 _)
  have hAm1 : 1 ≤ AP m P := hierarchyLevelConstant_one_le hKH0 P
  have hAm0 : 0 ≤ AP m P := zero_le_one.trans hAm1
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hn1 : m + 1 ≤ m + 1 := le_rfl
  have hn0 : m ≤ m + 1 := Nat.le_succ m
  have hPI : P ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hP1I : P + 1 ∈ Finset.Icc 1 (P + 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hTg0 : 0 ≤ lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3) :=
    mul_nonneg (Real.rpow_nonneg hlam0.le _) (Real.rpow_nonneg hlam0.le _)
  have vanCd : ∀ i ∈ Finset.Icc 1 (P + 1), VanishBefore t₀ (S5.Cd u i) :=
    fun i hi t ht hpre x s => (hvan t ht hpre x s).2.1 i hi
  have hcoefnn : 0 ≤ AP m P * L ^ 2 := mul_nonneg hAm0 (pow_nonneg hL0 _)
  -- the corrections
  have hCdb : ∀ n ≤ m + 1, ∀ i ∈ Finset.Icc 1 (P + 1), Un (k := k) st n (S5.Cd u i) ≤
      AP m P * L ^ 2 * lam ^ hierarchyCompletionExponent (i - 1) := fun n hn i hi => by
    by_cases h1 : i = 1
    · subst h1
      have : S5.Cd u 1 = 0 := hu.first_correction
      rw [this, map_zero]
      exact mul_nonneg hcoefnn (Real.rpow_nonneg hlam0.le _)
    · have hi1 : i - 1 ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr
        ⟨by have := (Finset.mem_Icc.mp hi).1; omega, by have := (Finset.mem_Icc.mp hi).2; omega⟩
      exact (U_le_W st n (vanCd i hi)).trans ((hlv n hn (i - 1) hi1).completion)
  have hexpC : hierarchyCompletionExponent P ≤ hierarchyOscExponent (P + 1) := by
    unfold hierarchyCompletionExponent hierarchyOscExponent; push_cast; linarith
  -- `Y` and `Z` up to level `P + 1`
  have hYb : ∀ j ∈ Finset.Icc 1 (P + 1), Un (k := k) st (m + 1) (S5.Yd u j) ≤
      AP m P * L ^ 2 * lam ^ hierarchyOscExponent j := fun j hj => by
    by_cases hjP : j ≤ P
    · have hj' : j ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, hjP⟩
      exact (U_le_W st (m + 1) (vanY j hj')).trans ((hlv (m + 1) hn1 j hj').Y)
    · have hjP1 : j = P + 1 := by have := (Finset.mem_Icc.mp hj).2; omega
      subst hjP1
      rw [hYP]
      refine (hCdb (m + 1) hn1 (P + 1) hP1I).trans (mul_le_mul_of_nonneg_left ?_ hcoefnn)
      simpa using Real.rpow_le_rpow_of_exponent_le hlam hexpC
  have hZb : ∀ i ∈ Finset.Icc 1 (P + 1), Un (k := k) st (m + 1) (S5.Zd u i) ≤
      AP m P * L ^ 2 * lam ^ hierarchyOscExponent i := fun i hi => by
    by_cases hiP : i ≤ P
    · have hi' : i ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, hiP⟩
      have h1 : Un (k := k) st (m + 1) (S5.Zd u i) ≤
          Un (k := k) st (m + 1) (u.Y i) + Un (k := k) st (m + 1) (u.B i) :=
        map_add_le_add (Un (k := k) st (m + 1)) _ _
      exact h1.trans (le_trans (add_le_add (U_le_W st (m + 1) (vanY i hi')) le_rfl)
        (hlv (m + 1) hn1 i hi').Z)
    · have hjP1 : i = P + 1 := by have := (Finset.mem_Icc.mp hi).2; omega
      subst hjP1
      rw [hZP]
      refine (hCdb (m + 1) hn1 (P + 1) hP1I).trans (mul_le_mul_of_nonneg_left ?_ hcoefnn)
      simpa using Real.rpow_le_rpow_of_exponent_le hlam hexpC
  have hBb : ∀ i ∈ Finset.Icc 1 (P + 1), Un (k := k) st m (u.B i) ≤
      AP m P * lam ^ hierarchyInductiveMeanExponent i := fun i hi => by
    by_cases h2 : 2 ≤ i ∧ i ≤ P
    · exact (hlv m hn0 i (Finset.mem_Icc.mpr ⟨by omega, h2.2⟩)).mean
    · have h0 : u.B i = 0 := by
        by_cases h1 : i = 1
        · subst h1; exact hu.first_mean.1
        · have : i = P + 1 := by have := (Finset.mem_Icc.mp hi); omega
          subst this; exact hu.top.2
      rw [h0, map_zero]
      exact mul_nonneg hAm0 (Real.rpow_nonneg hlam0.le _)
  have hVzero : ∀ i ∈ Finset.Icc 1 (P + 1), ∀ Y, A.phaseAdv (u.V i) Y = 0 := fun i hi Y => by
    by_cases hiP : i ≤ P
    · exact Bridge.ops_phaseAdv_of_transverse d
        (hTr i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, hiP⟩)) Y
    · have : i = P + 1 := by have := (Finset.mem_Icc.mp hi); omega
      subst this
      rw [hu.top.1, map_zero, LinearMap.zero_apply]
  -- the relay at level `P + 1`
  have hT1 : Un (k := k) st m (A.material (S5.Cd u (P + 1)) + A.labelGrad (u.p P)) ≤
      (2 * K (m + 1 + 3 * P) * AP m P ^ 2) * (lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)) := by
    have hvanR : VanishBefore t₀ (A.material (S5.Cd u (P + 1)) + A.labelGrad (u.p P)) :=
      fun t ht hpre x s => relay_vanish_before d
        (fun r hr hpre' x s => (hvan r hr hpre' x s).2.1 (P + 1) hP1I)
        (fun r hr hpre' x s => ((hvan r hr hpre' x s).1 P hPI).2) ht hpre x s
    refine (U_le_W st m hvanR).trans ?_
    have hrel := hrelayAll (m + 1 + 3 * P) m (by omega) (P + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    have hrelEq : A.relayAtLevel u cS (P + 1) =
        A.material (S5.Cd u (P + 1)) + A.labelGrad (u.p P) := by
      unfold HierarchyOperators.relayAtLevel
      have hne : ¬ (P + 1 = 2) := by omega
      simp only [hne, ↓reduceIte, sub_zero]
      rfl
    rw [hrelEq] at hrel
    simp only [Nat.add_sub_cancel] at hrel
    refine hrel.trans ?_
    have ho := (hlv (m + 1) hn1 P hPI).osc
    rw [hs'ne _ P (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)] at ho
    have hf' := (hlv (m + 1) hn1 P hPI).oscSource
    change s.oscSource (m + 1) P ≤ _ at hf'
    set E := lam ^ hierarchyOscExponent P with hE
    have hE0 : 0 ≤ E := Real.rpow_nonneg hlam0.le _
    have hsum : (measuredLevels' s osc₁ h₁).osc (m + 1) P + s.oscSource (m + 1) P ≤
        2 * AP m P * L * E := by
      rw [hs'ne _ P (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]
      have := mul_nonneg hAm0 hE0
      nlinarith [mul_le_mul_of_nonneg_left hL1 this]
    have hlamE : lam ^ (-1 : ℝ) * E = lam ^ (-1 + hierarchyOscExponent P) := by
      rw [Real.rpow_add hlam0]
    have habs2 := habs 2 (by norm_num) (-1 + hierarchyOscExponent P) (by
      unfold hierarchyOscExponent; linarith)
    calc K (m + 1 + 3 * P) * L * (lam ^ (-1 : ℝ) * ((measuredLevels' s osc₁ h₁).osc (m + 1) P +
          s.oscSource (m + 1) P))
        ≤ K (m + 1 + 3 * P) * L * (lam ^ (-1 : ℝ) * (2 * AP m P * L * E)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum
            (Real.rpow_nonneg hlam0.le _)) (mul_nonneg hKH0 hL0)
      _ = (2 * K (m + 1 + 3 * P) * AP m P) * (L ^ 2 * lam ^ (-1 + hierarchyOscExponent P)) := by
          rw [← hlamE]; ring
      _ ≤ (2 * K (m + 1 + 3 * P) * AP m P) * (lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left habs2 (by positivity)
      _ ≤ (2 * K (m + 1 + 3 * P) * AP m P ^ 2) * (lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)) := by
          refine mul_le_mul_of_nonneg_right ?_ hTg0
          have : 0 ≤ 2 * K (m + 1 + 3 * P) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hAm1 (mul_nonneg this hAm0)]
  -- the label tail
  have hT2 : ∀ ij ∈ F₁ P, Un (k := k) st m (A.labelAdv (S5.Zd u ij.1) (S5.Zd u ij.2)) ≤
      (K (m + 1 + 3 * P) * AP m P ^ 2) * (lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)) :=
    fun ij hij => by
    obtain ⟨hmem, hge⟩ := Finset.mem_filter.mp hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hmem
    have hge' : (P : ℝ) + 1 ≤ (ij.1 : ℝ) + ij.2 := by exact_mod_cast hge
    have hx := habs 5 (by norm_num) (hierarchyOscExponent ij.1 + hierarchyOscExponent ij.2) (by
      unfold hierarchyOscExponent; linarith)
    refine (term_BB hD_1 st d hc m (S5.Zd u ij.1) (S5.Zd u ij.2)).trans ?_
    refine le_trans (mul_le_mul (hlc' (m + 1 + 3 * P) m (by omega))
      (mul_le_mul (hZb _ hi) (hZb _ hj) (apply_nonneg (Un (k := k) st (m + 1)) _)
        (mul_nonneg hcoefnn (Real.rpow_nonneg hlam0.le _)))
      (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (hKL0 _)) ?_
    rw [Real.rpow_add hlam0] at hx
    calc K (m + 1 + 3 * P) * L * (AP m P * L ^ 2 * lam ^ hierarchyOscExponent ij.1 *
          (AP m P * L ^ 2 * lam ^ hierarchyOscExponent ij.2))
        = (K (m + 1 + 3 * P) * AP m P ^ 2) * (L ^ 5 * (lam ^ hierarchyOscExponent ij.1 *
          lam ^ hierarchyOscExponent ij.2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
  -- the phase tail
  have hT3 : ∀ ij ∈ F₂ P, Un (k := k) st m (A.phaseAdv (S5.Zd u ij.1) (S5.Yd u ij.2)) ≤
      (2 * K (m + 1 + 3 * P) * AP m P ^ 2) * (lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)) :=
    fun ij hij => by
    obtain ⟨hmem, hge⟩ := Finset.mem_filter.mp hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hmem
    have hi1 : 1 ≤ ij.1 := (Finset.mem_Icc.mp hi).1
    have hge' : (P : ℝ) + 2 ≤ (ij.1 : ℝ) + ij.2 := by exact_mod_cast hge
    have hsplit : A.phaseAdv (S5.Zd u ij.1) (S5.Yd u ij.2) =
        A.phaseAdv (S5.Cd u ij.1) (S5.Yd u ij.2) + A.phaseAdv (u.B ij.1) (S5.Yd u ij.2) := by
      have hV0 : A.phaseAdv (u.V ij.1) (S5.Yd u ij.2) = 0 := hVzero ij.1 hi _
      change A.phaseAdv (u.V ij.1 + S5.Cd u ij.1 + u.B ij.1) _ = _
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hV0, zero_add]
    rw [hsplit]
    refine (map_add_le_add (Un (k := k) st m) _ _).trans ?_
    have hKL := hKL0 (m + 1 + 3 * P)
    have hcast : ((ij.1 - 1 : ℕ) : ℝ) = (ij.1 : ℝ) - 1 := by rw [Nat.cast_sub hi1]; simp
    -- the completion part
    have hC1 : Un (k := k) st m (A.phaseAdv (S5.Cd u ij.1) (S5.Yd u ij.2)) ≤
        (K (m + 1 + 3 * P) * AP m P ^ 2) * (lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)) := by
      have hx := habs 5 (by norm_num)
        (3 / 2 + hierarchyCompletionExponent (ij.1 - 1) + hierarchyOscExponent ij.2) (by
          unfold hierarchyCompletionExponent hierarchyOscExponent; rw [hcast]; linarith)
      rw [Real.rpow_add hlam0, Real.rpow_add hlam0] at hx
      refine (term_fastU hD_1 st d hc m _ _).trans ?_
      refine le_trans (mul_le_mul (hpc' (m + 1 + 3 * P) m (by omega))
        (mul_le_mul (hCdb m hn0 _ hi) (hYb _ hj) (apply_nonneg (Un (k := k) st (m + 1)) _)
        (mul_nonneg hcoefnn (Real.rpow_nonneg hlam0.le _)))
        (mul_nonneg (apply_nonneg (Un (k := k) st m) _) (apply_nonneg (Un (k := k) st (m + 1)) _)) (mul_nonneg hKL hlam32')) ?_
      calc K (m + 1 + 3 * P) * L * lam ^ (3 / 2 : ℝ) *
            (AP m P * L ^ 2 * lam ^ hierarchyCompletionExponent (ij.1 - 1) *
              (AP m P * L ^ 2 * lam ^ hierarchyOscExponent ij.2))
          = (K (m + 1 + 3 * P) * AP m P ^ 2) * (L ^ 5 * (lam ^ (3 / 2 : ℝ) *
            lam ^ hierarchyCompletionExponent (ij.1 - 1) * lam ^ hierarchyOscExponent ij.2)) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
    -- the mean part
    have hB1 : Un (k := k) st m (A.phaseAdv (u.B ij.1) (S5.Yd u ij.2)) ≤
        (K (m + 1 + 3 * P) * AP m P ^ 2) * (lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)) := by
      have hx := habs 3 (by norm_num)
        (3 / 2 + hierarchyInductiveMeanExponent ij.1 + hierarchyOscExponent ij.2) (by
          unfold hierarchyInductiveMeanExponent hierarchyOscExponent; linarith)
      rw [Real.rpow_add hlam0, Real.rpow_add hlam0] at hx
      refine (term_fastU hD_1 st d hc m _ _).trans ?_
      refine le_trans (mul_le_mul (hpc' (m + 1 + 3 * P) m (by omega))
        (mul_le_mul (hBb _ hi) (hYb _ hj) (apply_nonneg (Un (k := k) st (m + 1)) _)
        (mul_nonneg hAm0 (Real.rpow_nonneg hlam0.le _)))
        (mul_nonneg (apply_nonneg (Un (k := k) st m) _) (apply_nonneg (Un (k := k) st (m + 1)) _)) (mul_nonneg hKL hlam32')) ?_
      calc K (m + 1 + 3 * P) * L * lam ^ (3 / 2 : ℝ) *
            (AP m P * lam ^ hierarchyInductiveMeanExponent ij.1 *
              (AP m P * L ^ 2 * lam ^ hierarchyOscExponent ij.2))
          = (K (m + 1 + 3 * P) * AP m P ^ 2) * (L ^ 3 * (lam ^ (3 / 2 : ℝ) *
            lam ^ hierarchyInductiveMeanExponent ij.1 * lam ^ hierarchyOscExponent ij.2)) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
    linarith
  -- assemble
  have hsum1 := seminorm_finset_le (Un (k := k) st m) (F₁ P)
    (fun ij => A.labelAdv (S5.Zd u ij.1) (S5.Zd u ij.2))
    (fun _ => (K (m + 1 + 3 * P) * AP m P ^ 2) * (lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)))
    hT2
  have hsum2 := seminorm_finset_le (Un (k := k) st m) (F₂ P)
    (fun ij => A.phaseAdv (S5.Zd u ij.1) (S5.Yd u ij.2))
    (fun _ => (2 * K (m + 1 + 3 * P) * AP m P ^ 2) * (lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)))
    hT3
  rw [Finset.sum_const, nsmul_eq_mul] at hsum1 hsum2
  unfold S5.remainder
  refine (map_add_le_add (Un (k := k) st m) _ _).trans ?_
  refine add_le_add ((map_add_le_add (Un (k := k) st m) _ _).trans (add_le_add hT1 hsum1)) hsum2 |>.trans ?_
  show _ ≤ (2 * K (m + 1 + 3 * P) * AP m P ^ 2 * (1 + ((F₁ P).card : ℝ) + 2 * ((F₂ P).card : ℝ)) +
      2 * (P : ℝ) * AP m P) * lam ^ (-5 / 4 : ℝ) * lam ^ (-2 * (P : ℝ) / 3)
  have hc1 : (0 : ℝ) ≤ (F₁ P).card := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ (F₂ P).card := Nat.cast_nonneg _
  have hq : 0 ≤ K (m + 1 + 3 * P) * AP m P ^ 2 := by positivity
  have hq2 : 0 ≤ 2 * (P : ℝ) * AP m P := by positivity
  nlinarith [mul_nonneg hq hTg0, mul_nonneg hq2 hTg0, mul_nonneg (mul_nonneg hq hc1) hTg0,
    mul_nonneg (mul_nonneg hq hc2) hTg0]

end Master

end

end TorusEuler.Paper.S5b
