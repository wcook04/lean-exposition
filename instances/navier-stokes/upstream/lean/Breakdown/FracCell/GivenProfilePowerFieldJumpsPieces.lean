import Breakdown.FracCell.GivenProfileDefs

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ProfilePowerJumpsPieces

open CellCert.GivenFields SteadyCert

def modeTerm (P : ChartParams) (D : FieldData) (β : ℝ) (n : ℤ) (y : Space) : Space :=
  ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
    (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
      reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
      reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)

theorem cellIndex_eventuallyEq (l : List ℝ) {u : ℝ} (hu : u ∉ (l.drop 1).dropLast) :
    ∀ᶠ v in nhds u, cellIndex l v = cellIndex l u := by
  have hall : ∀ᶠ v in nhds u, ∀ b ∈ ((l.drop 1).dropLast).toFinset,
      (decide (b ≤ v) = decide (b ≤ u)) := by
    rw [Filter.eventually_all_finset]
    intro b hb
    have hbu : b ≠ u := fun h => hu (h ▸ List.mem_toFinset.mp hb)
    rcases lt_or_gt_of_ne hbu with h | h
    · filter_upwards [lt_mem_nhds h] with v hv
      simp [h.le, hv.le]
    · filter_upwards [gt_mem_nhds h] with v hv
      simp [not_le.mpr h, not_le.mpr hv]
  filter_upwards [hall] with v hv
  unfold cellIndex
  congr 1
  exact List.filter_congr (fun b hb => hv b (List.mem_toFinset.mpr hb))

theorem evalHalf_eventuallyEq (S : Spline) {t x : ℝ}
    (ht : t ∉ (S.mesh.tBreaks.drop 1).dropLast) (hx : x ∉ (S.mesh.xBreaks.drop 1).dropLast) :
    ∀ᶠ p : ℝ × ℝ in nhds (t, x), S.evalHalf p.1 p.2 =
      MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)]
        (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks x)) := by
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod (cellIndex_eventuallyEq S.mesh.tBreaks ht)
    (cellIndex_eventuallyEq S.mesh.xBreaks hx)] with p hp
  unfold Spline.evalHalf
  rw [hp.1, hp.2]

theorem chartT_ne_of_radius {P : ChartParams} (hP : IsChartParams P) {z : Space} (hz : z ≠ 0)
    {b : ℝ} (hb : ‖z‖ ≠ P.L0 * b / (1 - b)) : chartT P z ≠ b := by
  intro h
  apply hb
  have hs : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hL := hP.L0_pos
  have hden : 0 < ‖z‖ + P.L0 := by linarith
  rw [← h, chartT]
  have h1 : 1 - ‖z‖ / (‖z‖ + P.L0) = P.L0 / (‖z‖ + P.L0) := by
    field_simp
    ring
  rw [h1]
  field_simp

theorem interior_bounds {l : List ℝ} (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0)
    (h1 : l.getLast? = some 1) {b : ℝ} (hb : b ∈ (l.drop 1).dropLast) : 0 < b ∧ b < 1 := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, l = a :: rest := by
    cases l with
    | nil => simp at h0
    | cons a rest => exact ⟨a, rest, rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at h0
  subst h0
  simp only [List.drop_one, List.tail_cons] at hb
  have hbr : b ∈ rest := List.mem_of_mem_dropLast hb
  rw [List.pairwise_cons] at hs
  refine ⟨hs.1 b hbr, ?_⟩
  have hne : rest ≠ [] := List.ne_nil_of_mem hbr
  have hlast : rest.getLast hne = 1 := by
    rw [List.getLast?_eq_some_getLast (by simp), List.getLast_cons hne] at h1
    exact Option.some.inj h1
  have hsplit := List.dropLast_append_getLast hne
  have hp := hs.2
  rw [← hsplit, List.pairwise_append] at hp
  have := hp.2.2 b hb (rest.getLast hne) (by simp)
  rwa [hlast] at this

theorem eval_eventuallyEq (S : Spline) (odd : Bool) {t x : ℝ} (hx0 : x ≠ 0)
    (ht : t ∉ (S.mesh.tBreaks.drop 1).dropLast) (hx : |x| ∉ (S.mesh.xBreaks.drop 1).dropLast) :
    ∀ᶠ p : ℝ × ℝ in nhds (t, x), S.eval odd p.1 p.2 =
      (if odd && decide (x < 0) then -1 else 1) *
        MvPolynomial.eval ![(p.1 : ℂ), ((if x < 0 then -p.2 else p.2 : ℝ) : ℂ)]
          (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|)) := by
  have htend : Filter.Tendsto (fun p : ℝ × ℝ => (p.1, |p.2|)) (nhds (t, x)) (nhds (t, |x|)) := by
    have hc : Continuous (fun p : ℝ × ℝ => (p.1, |p.2|)) :=
      continuous_fst.prodMk (continuous_abs.comp continuous_snd)
    simpa using hc.tendsto (t, x)
  have hE := htend.eventually (evalHalf_eventuallyEq S ht hx)
  have hsgn : ∀ᶠ p : ℝ × ℝ in nhds (t, x), (p.2 < 0 ↔ x < 0) ∧
      |p.2| = (if x < 0 then -p.2 else p.2) := by
    have hsnd : Filter.Tendsto (fun p : ℝ × ℝ => p.2) (nhds (t, x)) (nhds x) :=
      continuous_snd.tendsto (t, x)
    rcases lt_or_gt_of_ne hx0 with h | h
    · filter_upwards [hsnd.eventually (gt_mem_nhds h)] with p hp
      simp [h, hp, abs_of_neg hp]
    · filter_upwards [hsnd.eventually (lt_mem_nhds h)] with p hp
      simp [not_lt.mpr h.le, not_lt.mpr hp.le, abs_of_pos hp]
  filter_upwards [hE, hsgn] with p hp hs
  unfold Spline.eval
  rw [hp, hs.2]
  simp only [hs.1]

theorem heightRatio_abs_ne {z : Space} (hz : z ≠ 0) {b : ℝ} (h1 : z 2 ≠ b * ‖z‖)
    (h2 : z 2 ≠ -b * ‖z‖) : |heightRatio z| ≠ b := by
  have hs : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  intro h
  unfold heightRatio at h
  rcases abs_eq_abs.mp (h.trans (abs_of_nonneg (h ▸ abs_nonneg _)).symm) with h' | h'
  · exact h1 (by rw [← h']; field_simp)
  · exact h2 (by rw [← neg_neg b, ← h']; field_simp)

theorem heightRatio_ne_of_cone {z : Space} (hz : z ≠ 0) {c : ℝ} (h : z 2 ≠ c * ‖z‖) :
    heightRatio z ≠ c := by
  have hs : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  intro h'
  unfold heightRatio at h'
  exact h (by rw [← h']; field_simp)

theorem modePhase_zero (P : ChartParams) (β : ℝ) (y : Space) : modePhase P 0 β y = 1 := by
  simp [modePhase]

theorem modePhase_eq {P : ChartParams} {n : ℤ} {β : ℝ} {y : Space}
    (hw : (⟨y 0, y 1⟩ : ℂ) ≠ 0) :
    modePhase P n β y = ((⟨y 0, y 1⟩ : ℂ) / (‖(⟨y 0, y 1⟩ : ℂ)‖ : ℂ)) ^ (n * (P.m : ℤ)) *
      Complex.exp (Complex.I * ((n * β * logPhase P y : ℝ) : ℂ)) := by
  have hn : (‖(⟨y 0, y 1⟩ : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have he : Complex.exp (Complex.arg (⟨y 0, y 1⟩ : ℂ) * Complex.I) =
      (⟨y 0, y 1⟩ : ℂ) / (‖(⟨y 0, y 1⟩ : ℂ)‖ : ℂ) := by
    rw [eq_div_iff hn, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I _
  unfold modePhase angleOf
  have hsplit : Complex.I * ((((n * (P.m : ℤ) : ℤ) : ℝ) * Complex.arg (⟨y 0, y 1⟩ : ℂ) +
      n * β * logPhase P y : ℝ) : ℂ) = ((n * (P.m : ℤ) : ℤ) : ℂ) *
        (Complex.arg (⟨y 0, y 1⟩ : ℂ) * Complex.I) + Complex.I * ((n * β * logPhase P y : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul, he]

def splinesOf (D : FieldData) (n : ℤ) : List Spline :=
  [(D.amp n).radialAmp, (D.amp n).polarAmp, (D.amp n).streamAmp, (D.amp n).swirlAmp]

def breakRadii (P : ChartParams) (D : FieldData) : Finset ℝ :=
  D.modes.biUnion (fun n => ((splinesOf D n).flatMap (fun S => S.mesh.tBreaks)).toFinset.image
    (fun b => P.L0 * b / (1 - b)))

def breakCones (D : FieldData) : Finset ℝ :=
  insert 0 (D.modes.biUnion (fun n =>
    (((splinesOf D n).flatMap (fun S => S.mesh.xBreaks)).toFinset.filter (fun b => |b| < 1)).biUnion
      (fun b => {b, -b})))

theorem breakCones_abs_lt (D : FieldData) : ∀ c ∈ breakCones D, |c| < 1 := by
  intro c hc
  simp only [breakCones, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | ⟨n, _, b, ⟨_, hb⟩, rfl | rfl⟩
  · simp
  · exact hb
  · rwa [abs_neg]

theorem good_point {P : ChartParams} (hP : IsChartParams P) {D : FieldData} {n : ℤ}
    (hn : n ∈ D.modes) {S : Spline} (hS : S ∈ splinesOf D n) {z : Space} (hz : z ≠ 0)
    (hR : ∀ R ∈ breakRadii P D, ‖z‖ ≠ R) (hc : ∀ c ∈ breakCones D, z 2 ≠ c * ‖z‖) :
    chartT P z ∉ (S.mesh.tBreaks.drop 1).dropLast ∧ heightRatio z ≠ 0 ∧
      (IsTensorMesh S.mesh → |heightRatio z| ∉ (S.mesh.xBreaks.drop 1).dropLast) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hmem
    have hb : chartT P z ∈ S.mesh.tBreaks := List.mem_of_mem_drop (List.mem_of_mem_dropLast hmem)
    refine chartT_ne_of_radius hP hz (hR _ ?_) rfl
    simp only [breakRadii, Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset, List.mem_flatMap]
    exact ⟨n, hn, chartT P z, ⟨S, hS, hb⟩, rfl⟩
  · exact heightRatio_ne_of_cone hz (by simpa using hc 0 (Finset.mem_insert_self _ _))
  · intro hM hmem
    have hb : |heightRatio z| ∈ S.mesh.xBreaks := List.mem_of_mem_drop (List.mem_of_mem_dropLast hmem)
    have hbd := interior_bounds hM.x_sorted hM.x_first hM.x_last hmem
    have hlt : |(|heightRatio z|)| < 1 := by rw [abs_abs]; exact hbd.2
    have hin : ∀ c ∈ ({|heightRatio z|, -|heightRatio z|} : Finset ℝ), c ∈ breakCones D := by
      intro c hc'
      simp only [breakCones, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter,
        List.mem_toFinset, List.mem_flatMap]
      exact Or.inr ⟨n, hn, |heightRatio z|, ⟨⟨S, hS, hb⟩, hlt⟩, by simpa using hc'⟩
    exact heightRatio_abs_ne hz (hc _ (hin _ (by simp)))
      (hc _ (hin _ (by simp))) rfl

def SymbolW (U : Set Space) (wt : ℝ → ℝ) (f : Space → ℂ) : Prop :=
  ContDiffOn ℝ 3 f U ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ j ≤ 3,
    ‖iteratedFDeriv ℝ j f y‖ ≤ C * wt ‖y‖ * ‖y‖⁻¹ ^ j

theorem SymbolW.mul {U : Set Space} (hU : IsOpen U) {w₁ w₂ : ℝ → ℝ} (hw₁ : ∀ s, 0 ≤ w₁ s)
    (hw₂ : ∀ s, 0 ≤ w₂ s) {f g : Space → ℂ} (hf : SymbolW U w₁ f) (hg : SymbolW U w₂ g) :
    SymbolW U (fun s => w₁ s * w₂ s) (fun y => f y * g y) := by
  obtain ⟨hf1, C1, hC1, hf2⟩ := hf
  obtain ⟨hg1, C2, hC2, hg2⟩ := hg
  refine ⟨hf1.mul hg1, 8 * C1 * C2, by positivity, ?_⟩
  intro y hy j hj
  have hL := norm_iteratedFDerivWithin_mul_le hf1 hg1 hU.uniqueDiffOn hy (n := j)
    (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen _ hU hy] at hL
  have hr : 0 ≤ ‖y‖⁻¹ := by positivity
  have h1 := hw₁ ‖y‖
  have h2 := hw₂ ‖y‖
  calc ‖iteratedFDeriv ℝ j (fun y => f y * g y) y‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f U y‖ *
          ‖iteratedFDerivWithin ℝ (j - i) g U y‖ := hL
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (C1 * w₁ ‖y‖ * ‖y‖⁻¹ ^ i) *
          (C2 * w₂ ‖y‖ * ‖y‖⁻¹ ^ (j - i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [iteratedFDerivWithin_of_isOpen _ hU hy, iteratedFDerivWithin_of_isOpen _ hU hy]
        gcongr
        · exact hf2 y hy i (hij.trans hj)
        · exact hg2 y hy (j - i) ((Nat.sub_le j i).trans hj)
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (C1 * C2 * (w₁ ‖y‖ * w₂ ‖y‖) * ‖y‖⁻¹ ^ j) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hp : ‖y‖⁻¹ ^ j = ‖y‖⁻¹ ^ i * ‖y‖⁻¹ ^ (j - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hij]
        rw [hp]
        ring
    _ = (2 : ℝ) ^ j * (C1 * C2 * (w₁ ‖y‖ * w₂ ‖y‖) * ‖y‖⁻¹ ^ j) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ (2 : ℝ) ^ 3 * (C1 * C2 * (w₁ ‖y‖ * w₂ ‖y‖) * ‖y‖⁻¹ ^ j) := by
        gcongr
        norm_num
    _ = 8 * C1 * C2 * (w₁ ‖y‖ * w₂ ‖y‖) * ‖y‖⁻¹ ^ j := by ring

theorem SymbolW.third_le {U : Set Space} {wt : ℝ → ℝ} {f : Space → ℂ} (hf : SymbolW U wt f)
    {c : ℝ} (hc : 0 ≤ c) (hwt : ∀ s, 0 < s → wt s ≤ c * s ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ U, y ≠ 0 → ‖iteratedFDeriv ℝ 3 f y‖ ≤ K * ‖y‖⁻¹ := by
  obtain ⟨_, C, hC, hb⟩ := hf
  refine ⟨C * c, by positivity, fun y hy hy0 => (hb y hy 3 le_rfl).trans ?_⟩
  have hs : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  calc C * wt ‖y‖ * ‖y‖⁻¹ ^ 3 ≤ C * (c * ‖y‖ ^ 2) * ‖y‖⁻¹ ^ 3 := by
        gcongr
        exact hwt _ hs
    _ = C * c * ‖y‖⁻¹ := by field_simp

private def compMap (i : Fin 3) : ℂ →L[ℝ] Space :=
  Complex.reCLM.smulRight (EuclideanSpace.single i (1 : ℝ))

private lemma compMap_norm_le (i : Fin 3) : ‖compMap i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun c => ?_)
  simp only [compMap, ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, norm_smul,
    PiLp.norm_single, norm_one, mul_one, one_mul, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm c

private lemma ofComponents_re_eq (g : Fin 3 → Space → ℂ) :
    (fun y => ofComponents (fun i => (g i y).re)) = fun y => ∑ i : Fin 3, compMap i (g i y) := by
  funext y
  ext j
  rw [WithLp.ofLp_sum, Finset.sum_apply, Fin.sum_univ_three]
  fin_cases j <;> simp [ofComponents, compMap]

theorem components_third {g : Fin 3 → Space → ℂ} {z : Space} {K : ℝ}
    (hc : ∀ i, ContDiffAt ℝ 3 (g i) z) (hb : ∀ i, ‖iteratedFDeriv ℝ 3 (g i) z‖ ≤ K) :
    ContDiffAt ℝ 3 (fun y => ofComponents (fun i => (g i y).re)) z ∧
      ‖iteratedFDeriv ℝ 3 (fun y => ofComponents (fun i => (g i y).re)) z‖ ≤ 3 * K := by
  rw [ofComponents_re_eq]
  have hci : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      ContDiffAt ℝ 3 (fun y => compMap i (g i y)) z :=
    fun i _ => (compMap i).contDiff.contDiffAt.comp z (hc i)
  refine ⟨ContDiffAt.sum hci, ?_⟩
  rw [iteratedFDeriv_fun_sum_apply hci]
  calc ‖∑ i : Fin 3, iteratedFDeriv ℝ 3 (fun y => compMap i (g i y)) z‖
      ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ 3 (fun y => compMap i (g i y)) z‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, K := by
        apply Finset.sum_le_sum
        intro i _
        have h1 := (compMap i).norm_iteratedFDeriv_comp_left (hc i) (n := 3) le_rfl
        have hK : 0 ≤ ‖iteratedFDeriv ℝ 3 (g i) z‖ := norm_nonneg _
        calc ‖iteratedFDeriv ℝ 3 (fun y => compMap i (g i y)) z‖
            ≤ ‖compMap i‖ * ‖iteratedFDeriv ℝ 3 (g i) z‖ := h1
          _ ≤ 1 * ‖iteratedFDeriv ℝ 3 (g i) z‖ := by gcongr; exact compMap_norm_le i
          _ ≤ K := by rw [one_mul]; exact hb i
    _ = 3 * K := by simp

private lemma iteratedFDeriv_scale_eq {f : Space → ℂ} (hh : ∀ y : Space, ∀ c : ℝ, 0 < c → f (c • y) = f y)
    {c : ℝ} (hc : 0 < c) (y : Space) (j : ℕ) :
    iteratedFDeriv ℝ j f y = c ^ j • iteratedFDeriv ℝ j f (c • y) := by
  let g : Space ≃L[ℝ] Space := ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id ℝ Space)
    (c⁻¹ • ContinuousLinearMap.id ℝ Space)
    (fun v => by simp [smul_smul, hc.ne'])
    (fun v => by simp [smul_smul, hc.ne'])
  have hfg : f ∘ g = f := by
    funext v
    simp [g, hh v c hc]
  have h1 := g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (g y)) j
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ, hfg] at h1
  rw [h1]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply]
  have hg : ∀ w, g w = c • w := fun w => by simp [g]
  simp only [ContinuousLinearEquiv.coe_coe, hg]
  have hm := (iteratedFDeriv ℝ j f (c • y)).map_smul_univ (fun _ => c) v
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hm
  exact hm

theorem homogeneous_zero_bound {f : Space → ℂ} (hf : ContDiffOn ℝ 3 f {y | y ≠ 0})
    (hh : ∀ y : Space, ∀ c : ℝ, 0 < c → f (c • y) = f y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ≠ 0 → ∀ j ≤ 3, ‖iteratedFDeriv ℝ j f y‖ ≤ C * ‖y‖⁻¹ ^ j := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have hcont : ContinuousOn (fun y => ∑ j ∈ Finset.range 4, ‖iteratedFDeriv ℝ j f y‖)
      {y : Space | y ≠ 0} := by
    apply continuousOn_finsetSum
    intro j hj
    have hj3 : j ≤ 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hc := hf.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj3) hU.uniqueDiffOn
    exact (hc.congr (fun y hy => (iteratedFDerivWithin_of_isOpen j hU hy).symm)).norm
  have hsub : Metric.sphere (0 : Space) 1 ⊆ {y : Space | y ≠ 0} := by
    intro y hy
    show y ≠ 0
    exact ne_zero_of_mem_unit_sphere ⟨y, hy⟩
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Space) 1).exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y hy j hj
  have hs : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set u : Space := ‖y‖⁻¹ • y with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
  have hyu : ‖y‖ • u = y := by rw [hu, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hscale := iteratedFDeriv_scale_eq hh hs u j
  rw [hyu] at hscale
  have hbu : ‖iteratedFDeriv ℝ j f u‖ ≤ max C 0 := by
    have h1 := hC u (by simpa using hun)
    have h2 : ‖iteratedFDeriv ℝ j f u‖ ≤ ∑ i ∈ Finset.range 4, ‖iteratedFDeriv ℝ i f u‖ :=
      Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f u‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (by omega))
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h1
    exact (h2.trans h1).trans (le_max_left _ _)
  have heq : ‖iteratedFDeriv ℝ j f u‖ = ‖y‖ ^ j * ‖iteratedFDeriv ℝ j f y‖ := by
    rw [hscale, norm_smul, norm_pow, norm_norm]
  have hpos : 0 < ‖y‖ ^ j := pow_pos hs j
  rw [inv_pow]
  rw [le_mul_inv_iff₀ hpos, mul_comm, ← heq]
  exact hbu

theorem SymbolW.mono {U V : Set Space} {wt : ℝ → ℝ} {f : Space → ℂ} (hf : SymbolW U wt f)
    (hVU : V ⊆ U) : SymbolW V wt f := by
  obtain ⟨h1, C, hC, h2⟩ := hf
  exact ⟨h1.mono hVU, C, hC, fun y hy j hj => h2 y (hVU hy) j hj⟩

theorem SymbolW.add {U : Set Space} (hU : IsOpen U) {wt : ℝ → ℝ} {f g : Space → ℂ}
    (hf : SymbolW U wt f) (hg : SymbolW U wt g) : SymbolW U wt (fun y => f y + g y) := by
  obtain ⟨hf1, C1, hC1, hf2⟩ := hf
  obtain ⟨hg1, C2, hC2, hg2⟩ := hg
  refine ⟨hf1.add hg1, C1 + C2, by positivity, fun y hy j hj => ?_⟩
  have hfa : ContDiffAt ℝ j f y :=
    (hf1.contDiffAt (hU.mem_nhds hy)).of_le (by exact_mod_cast hj)
  have hga : ContDiffAt ℝ j g y :=
    (hg1.contDiffAt (hU.mem_nhds hy)).of_le (by exact_mod_cast hj)
  rw [fun_iteratedFDeriv_add_apply hfa hga]
  calc ‖iteratedFDeriv ℝ j f y + iteratedFDeriv ℝ j g y‖
      ≤ ‖iteratedFDeriv ℝ j f y‖ + ‖iteratedFDeriv ℝ j g y‖ := norm_add_le _ _
    _ ≤ C1 * wt ‖y‖ * ‖y‖⁻¹ ^ j + C2 * wt ‖y‖ * ‖y‖⁻¹ ^ j :=
        add_le_add (hf2 y hy j hj) (hg2 y hy j hj)
    _ = (C1 + C2) * wt ‖y‖ * ‖y‖⁻¹ ^ j := by ring

theorem SymbolW.weight_le {U : Set Space} {wt wt' : ℝ → ℝ} {f : Space → ℂ} (hf : SymbolW U wt f)
    {c : ℝ} (hc : 0 ≤ c) (hle : ∀ y ∈ U, wt ‖y‖ ≤ c * wt' ‖y‖) : SymbolW U wt' f := by
  obtain ⟨h1, C, hC, h2⟩ := hf
  refine ⟨h1, C * c, by positivity, fun y hy j hj => (h2 y hy j hj).trans ?_⟩
  have hr : 0 ≤ ‖y‖⁻¹ ^ j := by positivity
  calc C * wt ‖y‖ * ‖y‖⁻¹ ^ j ≤ C * (c * wt' ‖y‖) * ‖y‖⁻¹ ^ j := by
        gcongr
        exact hle y hy
    _ = C * c * wt' ‖y‖ * ‖y‖⁻¹ ^ j := by ring

theorem SymbolW.const (U : Set Space) (a : ℂ) : SymbolW U (fun _ => 1) (fun _ => a) := by
  refine ⟨contDiffOn_const, ‖a‖, norm_nonneg _, fun y _ j _ => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hj)]
    simp only [Pi.zero_apply, norm_zero]
    positivity

theorem SymbolW.of_homogeneous {U : Set Space} (hU0 : U ⊆ {y | y ≠ 0}) {f : Space → ℂ}
    (hf : ContDiffOn ℝ 3 f {y | y ≠ 0}) (hh : ∀ y : Space, ∀ c : ℝ, 0 < c → f (c • y) = f y) :
    SymbolW U (fun _ => 1) f := by
  obtain ⟨C, hC, hb⟩ := homogeneous_zero_bound hf hh
  refine ⟨hf.mono hU0, C, hC, fun y hy j hj => ?_⟩
  rw [mul_one]
  exact hb y (hU0 hy) j hj

private lemma scale_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℂ) {c : ℝ}
    (hc : 0 < c) (u : E) (j : ℕ) :
    iteratedFDeriv ℝ j (fun v => F (c • v)) u = c ^ j • iteratedFDeriv ℝ j F (c • u) := by
  let g : E ≃L[ℝ] E := ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id ℝ E)
    (c⁻¹ • ContinuousLinearMap.id ℝ E)
    (fun v => by simp [smul_smul, hc.ne'])
    (fun v => by simp [smul_smul, hc.ne'])
  have hg : ∀ w, g w = c • w := fun w => by simp [g]
  have hfg : (fun v => F (c • v)) = F ∘ g := by
    funext v
    simp [hg]
  have h1 := g.iteratedFDerivWithin_comp_right F uniqueDiffOn_univ (Set.mem_univ (g u)) j
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h1
  rw [hfg, h1, hg]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply]
  simp only [ContinuousLinearEquiv.coe_coe, hg]
  have hm := (iteratedFDeriv ℝ j F (c • u)).map_smul_univ (fun _ => c) v
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hm
  exact hm

private lemma norm_derivs_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ u : Space, ‖u‖ = 1 → ∀ i, 1 ≤ i → i ≤ 3 →
    ‖iteratedFDerivWithin ℝ i (fun v : Space => ‖v‖) {v | v ≠ 0} u‖ ≤ B ^ i := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have hN : ContDiffOn ℝ 3 (fun v : Space => ‖v‖) {v | v ≠ 0} :=
    fun v hv => (contDiffAt_norm ℝ hv).contDiffWithinAt
  have hcont : ContinuousOn (fun y => ∑ j ∈ Finset.range 4,
      ‖iteratedFDerivWithin ℝ j (fun v : Space => ‖v‖) {v | v ≠ 0} y‖) {y : Space | y ≠ 0} := by
    apply continuousOn_finsetSum
    intro j hj
    have hj3 : j ≤ 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (hN.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj3)
      hU.uniqueDiffOn).norm
  have hsub : Metric.sphere (0 : Space) 1 ⊆ {y : Space | y ≠ 0} := by
    intro y hy
    show y ≠ 0
    exact ne_zero_of_mem_unit_sphere ⟨y, hy⟩
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Space) 1).exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max C 1, le_max_right _ _, fun u hu i hi1 hi3 => ?_⟩
  have h1 := hC u (by simpa using hu)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h1
  have h2 : ‖iteratedFDerivWithin ℝ i (fun v : Space => ‖v‖) {v | v ≠ 0} u‖ ≤
      ∑ j ∈ Finset.range 4, ‖iteratedFDerivWithin ℝ j (fun v : Space => ‖v‖) {v | v ≠ 0} u‖ :=
    Finset.single_le_sum (f := fun j => ‖iteratedFDerivWithin ℝ j (fun v : Space => ‖v‖)
      {v | v ≠ 0} u‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  calc _ ≤ max C 1 := (h2.trans h1).trans (le_max_left _ _)
    _ = max C 1 ^ 1 := (pow_one _).symm
    _ ≤ max C 1 ^ i := pow_le_pow_right₀ (le_max_right _ _) hi1

theorem SymbolW.of_radial {h : ℝ → ℂ} {wt : ℝ → ℝ} (hwt : ∀ s, 0 ≤ wt s) (hh : ContDiffOn ℝ 3 h (Set.Ioi 0))
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ i ≤ 3,
      ‖iteratedFDeriv ℝ i h s‖ ≤ C * wt s * s⁻¹ ^ i) :
    SymbolW {y : Space | y ≠ 0} wt (fun y => h ‖y‖) := by
  obtain ⟨C, hC0, hC⟩ := hb
  obtain ⟨B, hB1, hB⟩ := norm_derivs_bound
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have hmaps : Set.MapsTo (fun v : Space => ‖v‖) {v | v ≠ 0} (Set.Ioi 0) :=
    fun v hv => norm_pos_iff.mpr hv
  have hN : ContDiffOn ℝ 3 (fun v : Space => ‖v‖) {v | v ≠ 0} :=
    fun v hv => (contDiffAt_norm ℝ hv).contDiffWithinAt
  refine ⟨hh.comp hN hmaps, 6 * C * B ^ 3, by positivity, fun y hy j hj => ?_⟩
  have hy0 : y ≠ 0 := hy
  have hs : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  set s := ‖y‖ with hsdef
  set u : Space := s⁻¹ • y with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
  have hyu : s • u = y := by rw [hu, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hun
    exact zero_ne_one hun
  let hsc : ℝ → ℂ := fun r => h (s • r)
  have hsc_cd : ContDiffOn ℝ 3 hsc (Set.Ioi 0) := by
    refine hh.comp (contDiff_const_smul s).contDiffOn (fun r hr => ?_)
    simp only [Set.mem_Ioi, smul_eq_mul] at hr ⊢
    positivity
  have hcomp : (fun v => (fun y => h ‖y‖) (s • v)) = hsc ∘ (fun v : Space => ‖v‖) := by
    funext v
    simp [hsc, norm_smul, abs_of_pos hs]
  have hCb : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i hsc (Set.Ioi 0) ‖u‖‖ ≤
      C * wt s := by
    intro i hi
    rw [hun, iteratedFDerivWithin_of_isOpen i isOpen_Ioi (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)]
    have h1' : iteratedFDeriv ℝ i hsc 1 = s ^ i • iteratedFDeriv ℝ i h s := by
      show iteratedFDeriv ℝ i (fun r => h (s • r)) 1 = _
      rw [scale_comp h hs (1 : ℝ) i, smul_eq_mul, mul_one]
    rw [h1', norm_smul, norm_pow, Real.norm_of_nonneg hs.le]
    have h2 := hC s hs i (hi.trans hj)
    have hsi : 0 < s ^ i := pow_pos hs i
    calc s ^ i * ‖iteratedFDeriv ℝ i h s‖ ≤ s ^ i * (C * wt s * s⁻¹ ^ i) := by gcongr
      _ = C * wt s * (s ^ i * s⁻¹ ^ i) := by ring
      _ = C * wt s := by rw [← mul_pow, mul_inv_cancel₀ hs.ne', one_pow, mul_one]
  have hFdB := norm_iteratedFDerivWithin_comp_le hsc_cd hN (n := j) (by exact_mod_cast hj)
    (uniqueDiffOn_Ioi 0) hU.uniqueDiffOn hmaps hu0 hCb (fun i hi1 hi3 => hB u hun i hi1 (hi3.trans hj))
  rw [← hcomp, iteratedFDerivWithin_of_isOpen j hU hu0] at hFdB
  have hsc2 := scale_comp (fun y => h ‖y‖) hs u j
  rw [hyu] at hsc2
  rw [hsc2, norm_smul, norm_pow, Real.norm_of_nonneg hs.le] at hFdB
  have hsj : 0 < s ^ j := pow_pos hs j
  have hfact : (j.factorial : ℝ) ≤ 6 := by
    interval_cases j <;> norm_num [Nat.factorial]
  have hBj : B ^ j ≤ B ^ 3 := pow_le_pow_right₀ hB1 hj
  have hw : 0 ≤ C * wt s := mul_nonneg hC0 (hwt s)
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hsj, mul_comm]
  calc s ^ j * ‖iteratedFDeriv ℝ j (fun y => h ‖y‖) y‖
      ≤ (j.factorial : ℝ) * (C * wt s) * B ^ j := hFdB
    _ ≤ 6 * (C * wt s) * B ^ 3 := by gcongr
    _ = 6 * C * B ^ 3 * wt s := by ring

theorem SymbolW.of_homogeneous_real {U : Set Space} (hU0 : U ⊆ {y | y ≠ 0}) {r : Space → ℝ}
    (hr : ContDiffOn ℝ 3 r {y | y ≠ 0}) (hh : ∀ y : Space, ∀ c : ℝ, 0 < c → r (c • y) = r y) :
    SymbolW U (fun _ => 1) (fun y => (r y : ℂ)) :=
  SymbolW.of_homogeneous hU0 (Complex.ofRealCLM.contDiff.comp_contDiffOn hr)
    (fun y c hc => by simp only [hh y c hc])

private lemma coord_div_norm_contDiffOn (i : Fin 3) :
    ContDiffOn ℝ 3 (fun y : Space => y i / ‖y‖) {y | y ≠ 0} := by
  intro y hy
  have hy0 : y ≠ 0 := hy
  have h1 : ContDiffAt ℝ 3 (fun y : Space => y i) y :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt
  exact (h1.div (contDiffAt_norm ℝ hy0) (norm_ne_zero_iff.mpr hy0)).contDiffWithinAt

private lemma coord_div_norm_smul (i : Fin 3) (y : Space) {c : ℝ} (hc : 0 < c) :
    (c • y) i / ‖c • y‖ = y i / ‖y‖ := by
  rw [PiLp.smul_apply, norm_smul, Real.norm_of_nonneg hc.le, smul_eq_mul,
    mul_div_mul_left _ _ hc.ne']

theorem heightRatio_contDiffOn : ContDiffOn ℝ 3 heightRatio {y | y ≠ 0} :=
  coord_div_norm_contDiffOn 2

theorem heightRatio_smul (y : Space) {c : ℝ} (hc : 0 < c) : heightRatio (c • y) = heightRatio y :=
  coord_div_norm_smul 2 y hc

theorem radialVec_contDiffOn (i : Fin 3) : ContDiffOn ℝ 3 (fun y => radialVec y i) {y | y ≠ 0} :=
  coord_div_norm_contDiffOn i

theorem radialVec_smul (i : Fin 3) (y : Space) {c : ℝ} (hc : 0 < c) :
    radialVec (c • y) i = radialVec y i :=
  coord_div_norm_smul i y hc

theorem azimVecQ_contDiffOn (i : Fin 3) : ContDiffOn ℝ 3 (fun y => azimVecQ y i) {y | y ≠ 0} := by
  fin_cases i
  · simpa [azimVecQ, neg_div] using (coord_div_norm_contDiffOn 1).neg
  · simpa [azimVecQ] using coord_div_norm_contDiffOn 0
  · simpa [azimVecQ] using (contDiffOn_const : ContDiffOn ℝ 3 (fun _ : Space => (0 : ℝ)) _)

theorem azimVecQ_smul (i : Fin 3) (y : Space) {c : ℝ} (hc : 0 < c) :
    azimVecQ (c • y) i = azimVecQ y i := by
  fin_cases i
  · simp only [azimVecQ, Fin.zero_eta, Matrix.cons_val_zero, neg_div]
    rw [coord_div_norm_smul 1 y hc]
  · simp only [azimVecQ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact coord_div_norm_smul 0 y hc
  · simp [azimVecQ]

theorem polarVecQ_contDiffOn (i : Fin 3) : ContDiffOn ℝ 3 (fun y => polarVecQ y i) {y | y ≠ 0} := by
  have hq : ContDiffOn ℝ 3 (fun y => qOf y) {y | y ≠ 0} := by
    simpa [qOf] using contDiffOn_const.sub (heightRatio_contDiffOn.pow 2)
  fin_cases i
  · simpa [polarVecQ, mul_div_assoc] using heightRatio_contDiffOn.mul (coord_div_norm_contDiffOn 0)
  · simpa [polarVecQ, mul_div_assoc] using heightRatio_contDiffOn.mul (coord_div_norm_contDiffOn 1)
  · simpa [polarVecQ] using hq.neg

theorem polarVecQ_smul (i : Fin 3) (y : Space) {c : ℝ} (hc : 0 < c) :
    polarVecQ (c • y) i = polarVecQ y i := by
  have hh := heightRatio_smul y hc
  fin_cases i
  · simp only [polarVecQ, Fin.zero_eta, Matrix.cons_val_zero]
    rw [mul_div_assoc, mul_div_assoc, hh, coord_div_norm_smul 0 y hc]
  · simp only [polarVecQ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [mul_div_assoc, mul_div_assoc, hh, coord_div_norm_smul 1 y hc]
  · simp [polarVecQ, qOf, hh]

theorem SymbolW.comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set Space}
    (hU : IsOpen U) {φ : Space → E} (hφ : ContDiffOn ℝ 3 φ U) {c : ℝ}
    (hφb : ∀ y ∈ U, ∀ i, 1 ≤ i → i ≤ 3 → ‖iteratedFDeriv ℝ i φ y‖ ≤ c * ‖y‖⁻¹ ^ i)
    {K : Set E} (hK : IsCompact K) (hφK : ∀ y ∈ U, φ y ∈ K) {F : E → ℂ} (hF : ContDiff ℝ 3 F) :
    SymbolW U (fun _ => 1) (fun y => F (φ y)) := by
  have hcont : Continuous (fun v => ∑ i ∈ Finset.range 4, ‖iteratedFDeriv ℝ i F v‖) := by
    refine continuous_finsetSum _ (fun i hi => ?_)
    have hi3 : i ≤ 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact (hF.continuous_iteratedFDeriv (by exact_mod_cast hi3)).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  set c' := max c 1 with hc'
  have hc'1 : 1 ≤ c' := le_max_right _ _
  refine ⟨hF.comp_contDiffOn hφ, 6 * max C 0 * c' ^ 3, by positivity, fun y hy j hj => ?_⟩
  have hCb : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i F Set.univ (φ y)‖ ≤ max C 0 := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    have h1 := hC (φ y) (hφK y hy)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h1
    have h2 : ‖iteratedFDeriv ℝ i F (φ y)‖ ≤ ∑ k ∈ Finset.range 4, ‖iteratedFDeriv ℝ k F (φ y)‖ :=
      Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k F (φ y)‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (by omega))
    exact (h2.trans h1).trans (le_max_left _ _)
  have hr : 0 ≤ ‖y‖⁻¹ := by positivity
  have hDb : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDerivWithin ℝ i φ U y‖ ≤ (c' * ‖y‖⁻¹) ^ i := by
    intro i hi1 hij
    rw [iteratedFDerivWithin_of_isOpen i hU hy]
    calc ‖iteratedFDeriv ℝ i φ y‖ ≤ c * ‖y‖⁻¹ ^ i := hφb y hy i hi1 (hij.trans hj)
      _ ≤ c' ^ i * ‖y‖⁻¹ ^ i := by
          gcongr
          calc c ≤ c' := le_max_left _ _
            _ = c' ^ 1 := (pow_one _).symm
            _ ≤ c' ^ i := pow_le_pow_right₀ hc'1 hi1
      _ = (c' * ‖y‖⁻¹) ^ i := (mul_pow _ _ _).symm
  have hFdB := norm_iteratedFDerivWithin_comp_le (hF.contDiffOn (s := Set.univ)) hφ (n := j)
    (by exact_mod_cast hj) uniqueDiffOn_univ hU.uniqueDiffOn (fun _ _ => Set.mem_univ _) hy hCb hDb
  rw [iteratedFDerivWithin_of_isOpen j hU hy] at hFdB
  have hfact : (j.factorial : ℝ) ≤ 6 := by
    interval_cases j <;> norm_num [Nat.factorial]
  have hcj : c' ^ j ≤ c' ^ 3 := pow_le_pow_right₀ hc'1 hj
  calc ‖iteratedFDeriv ℝ j (fun y => F (φ y)) y‖ ≤ (j.factorial : ℝ) * max C 0 * (c' * ‖y‖⁻¹) ^ j :=
        hFdB
    _ = (j.factorial : ℝ) * max C 0 * c' ^ j * ‖y‖⁻¹ ^ j := by rw [mul_pow]; ring
    _ ≤ 6 * max C 0 * c' ^ 3 * ‖y‖⁻¹ ^ j := by gcongr
    _ = 6 * max C 0 * c' ^ 3 * (fun _ => (1 : ℝ)) ‖y‖ * ‖y‖⁻¹ ^ j := by simp

private lemma ofReal_iteratedFDeriv_le {g : ℝ → ℝ} {s : ℝ} {i : ℕ} (hg : ContDiffAt ℝ i g s) :
    ‖iteratedFDeriv ℝ i (fun r => (g r : ℂ)) s‖ ≤ ‖iteratedDeriv i g s‖ := by
  have h1 := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hg (n := i) le_rfl
  have h2 : ‖iteratedFDeriv ℝ i g s‖ = ‖iteratedDeriv i g s‖ :=
    norm_iteratedFDeriv_eq_norm_iteratedDeriv
  rw [Complex.ofRealCLM_norm, one_mul, h2] at h1
  exact h1

theorem chartS_symbol {P : ChartParams} (hP : IsChartParams P) :
    SymbolW {y : Space | y ≠ 0} (fun _ => 1) (fun y => (chartS P y : ℂ)) := by
  have hL := hP.L0_pos
  let g : ℝ → ℝ := fun s => P.L0 * (1 * s + P.L0)⁻¹
  have hfun : (fun y : Space => (chartS P y : ℂ)) = fun y => ((g ‖y‖ : ℝ) : ℂ) := by
    funext y
    have hpos : 0 < ‖y‖ + P.L0 := by positivity
    congr 1
    simp only [chartS, chartT, g, one_mul]
    field_simp
    ring
  rw [hfun]
  have hgcd : ∀ s : ℝ, 0 < s → ContDiffAt ℝ 3 g s := by
    intro s hs
    have hne : 1 * s + P.L0 ≠ 0 := by positivity
    exact contDiffAt_const.mul (((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).inv hne)
  refine SymbolW.of_radial (h := fun r => ((g r : ℝ) : ℂ)) (fun _ => zero_le_one) ?_ ⟨6, by norm_num, ?_⟩
  · intro s hs
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp s (hgcd s hs)).contDiffWithinAt
  · intro s hs i hi
    refine (ofReal_iteratedFDeriv_le ((hgcd s hs).of_le (by exact_mod_cast hi))).trans ?_
    have hid : iteratedDeriv i g s =
        P.L0 * ((-1) ^ i * (i.factorial : ℝ) * 1 ^ i * (1 * s + P.L0) ^ (-1 - i : ℤ)) := by
      simp only [g]
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
    have hpos : 0 < s + P.L0 := by linarith
    rw [hid, one_pow, one_mul, mul_one]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_of_nonneg hL.le, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ i.factorial),
      Real.norm_of_nonneg (zpow_nonneg hpos.le _)]
    have hz : (s + P.L0) ^ (-1 - i : ℤ) = (s + P.L0)⁻¹ * ((s + P.L0)⁻¹) ^ i := by
      rw [show (-1 - i : ℤ) = -((1 + i : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        pow_add, pow_one, mul_inv, inv_pow]
    rw [hz]
    have hfact : (i.factorial : ℝ) ≤ 6 := by
      interval_cases i <;> norm_num [Nat.factorial]
    have h1 : P.L0 * (s + P.L0)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hpos]
      linarith
    have h2 : (s + P.L0)⁻¹ ^ i ≤ s⁻¹ ^ i := by
      gcongr
      linarith
    calc P.L0 * ((i.factorial : ℝ) * ((s + P.L0)⁻¹ * (s + P.L0)⁻¹ ^ i))
        = (P.L0 * (s + P.L0)⁻¹) * (i.factorial : ℝ) * (s + P.L0)⁻¹ ^ i := by ring
      _ ≤ 1 * 6 * s⁻¹ ^ i := by gcongr
      _ = 6 * (fun _ => (1 : ℝ)) s * s⁻¹ ^ i := by simp

theorem norm_symbol : SymbolW {y : Space | y ≠ 0} (fun s => |s|) (fun y => ((‖y‖ : ℝ) : ℂ)) := by
  have hcd : ∀ s : ℝ, ContDiffAt ℝ 3 (fun r : ℝ => r) s := fun s => contDiffAt_id
  refine SymbolW.of_radial (h := fun r => ((r : ℝ) : ℂ)) (wt := fun s => |s|) (fun s => abs_nonneg s) ?_ ⟨1, zero_le_one, ?_⟩
  · intro s hs
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp s (hcd s)).contDiffWithinAt
  · intro s hs i hi
    refine (ofReal_iteratedFDeriv_le ((hcd s).of_le (by exact_mod_cast hi))).trans ?_
    rw [iteratedDeriv_eq_iterate]
    interval_cases i
    · simp [abs_of_pos hs]
    · simp [deriv_id'', hs.ne', abs_of_pos hs]
    · simp [deriv_id'']
      positivity
    · simp [deriv_id'']
      positivity

theorem chartT_symbol {P : ChartParams} (hP : IsChartParams P) :
    SymbolW {y : Space | y ≠ 0} (fun s => |s|) (fun y => (chartT P y : ℂ)) := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have hL := hP.L0_pos
  have h1 := SymbolW.mul hU (fun _ => zero_le_one) (fun _ => zero_le_one) (chartS_symbol hP)
    (SymbolW.const {y : Space | y ≠ 0} ((P.L0⁻¹ : ℝ) : ℂ))
  have h2 := SymbolW.mul hU (fun s => abs_nonneg s) (fun _ => by norm_num) norm_symbol h1
  have hfun : (fun y : Space => (chartT P y : ℂ)) =
      fun y => ((‖y‖ : ℝ) : ℂ) * ((chartS P y : ℂ) * ((P.L0⁻¹ : ℝ) : ℂ)) := by
    funext y
    have hpos : 0 < ‖y‖ + P.L0 := by positivity
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    simp only [chartS, chartT]
    field_simp
    ring
  rw [hfun]
  exact h2.weight_le zero_le_one (fun y _ => by simp)

theorem mvpoly_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : MvPolynomial (Fin 2) ℂ) {u v : E → ℂ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) :
    ContDiff ℝ 3 (fun p => MvPolynomial.eval ![u p, v p] Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ 3 (fun _ : E => a))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p n hp =>
    fin_cases n
    · simpa using hp.mul hu
    · simpa using hp.mul hv

private lemma real_deriv_bound {r : Space → ℝ} {U : Set Space} (hU : IsOpen U)
    (hr : SymbolW U (fun _ => 1) (fun y => (r y : ℂ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ i ≤ 3, ‖iteratedFDeriv ℝ i r y‖ ≤ C * ‖y‖⁻¹ ^ i := by
  obtain ⟨h1, C, hC, h2⟩ := hr
  refine ⟨C, hC, fun y hy i hi => ?_⟩
  have hcd : ContDiffAt ℝ 3 (fun y => (r y : ℂ)) y := h1.contDiffAt (hU.mem_nhds hy)
  have hrd : ContDiffAt ℝ 3 r y := by
    have := Complex.reCLM.contDiff.contDiffAt.comp y hcd
    simpa [Function.comp_def] using this
  have heq := Complex.ofRealLI.norm_iteratedFDeriv_comp_left hrd (i := i) (by exact_mod_cast hi)
  have hb := h2 y hy i hi
  simp only [mul_one] at hb
  calc ‖iteratedFDeriv ℝ i r y‖ = ‖iteratedFDeriv ℝ i (⇑Complex.ofRealLI ∘ r) y‖ := heq.symm
    _ ≤ C * ‖y‖⁻¹ ^ i := hb

theorem chartS_contDiffOn {P : ChartParams} (hP : IsChartParams P) :
    ContDiffOn ℝ 3 (chartS P) {y | y ≠ 0} := by
  intro y hy
  have hy0 : y ≠ 0 := hy
  have hN : ContDiffAt ℝ 3 (fun v : Space => ‖v‖) y := contDiffAt_norm ℝ hy0
  have hne : ‖y‖ + P.L0 ≠ 0 := by have := hP.L0_pos; positivity
  exact (contDiffAt_const.sub (hN.div (hN.add contDiffAt_const) hne)).contDiffWithinAt

theorem piece_symbol {P : ChartParams} (hP : IsChartParams P) (Q : MvPolynomial (Fin 2) ℂ) (σ : ℝ) :
    SymbolW {y : Space | y ≠ 0} (fun _ => 1)
      (fun y => MvPolynomial.eval ![(chartT P y : ℂ), ((σ * heightRatio y : ℝ) : ℂ)] Q) := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have hL := hP.L0_pos
  obtain ⟨C1, hC1, hb1⟩ := real_deriv_bound hU (chartS_symbol hP)
  obtain ⟨C2, hC2, hb2⟩ := real_deriv_bound hU
    (SymbolW.of_homogeneous_real (subset_refl _) heightRatio_contDiffOn
      (fun y c hc => heightRatio_smul y hc))
  let φ : Space → ℝ × ℝ := fun y => (chartS P y, heightRatio y)
  let F : ℝ × ℝ → ℂ := fun p => MvPolynomial.eval ![((1 - p.1 : ℝ) : ℂ), ((σ * p.2 : ℝ) : ℂ)] Q
  have hfun : (fun y => MvPolynomial.eval ![(chartT P y : ℂ), ((σ * heightRatio y : ℝ) : ℂ)] Q) =
      fun y => F (φ y) := by
    funext y
    simp only [F, φ, chartS, sub_sub_cancel]
  rw [hfun]
  have hS := chartS_contDiffOn hP
  have hH := heightRatio_contDiffOn
  have hφ : ContDiffOn ℝ 3 φ {y | y ≠ 0} := hS.prodMk hH
  have hF : ContDiff ℝ 3 F := by
    apply mvpoly_contDiff
    · exact Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_fst)
    · exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd)
  refine SymbolW.comp hU hφ (c := C1 + C2) ?_ ((isCompact_Icc).prod (isCompact_Icc))
    (K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ?_ hF
  · intro y hy i hi1 hi3
    have hSa : ContDiffAt ℝ 3 (chartS P) y := hS.contDiffAt (hU.mem_nhds hy)
    have hHa : ContDiffAt ℝ 3 heightRatio y := hH.contDiffAt (hU.mem_nhds hy)
    rw [iteratedFDeriv_prodMk hSa hHa (by exact_mod_cast hi3), ContinuousMultilinearMap.opNorm_prod]
    have e1 := hb1 y hy i hi3
    have e2 := hb2 y hy i hi3
    calc ‖(iteratedFDeriv ℝ i (chartS P) y, iteratedFDeriv ℝ i heightRatio y)‖
        ≤ ‖iteratedFDeriv ℝ i (chartS P) y‖ + ‖iteratedFDeriv ℝ i heightRatio y‖ := by
          rw [Prod.norm_def]
          exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
      _ ≤ C1 * ‖y‖⁻¹ ^ i + C2 * ‖y‖⁻¹ ^ i := add_le_add e1 e2
      _ = (C1 + C2) * ‖y‖⁻¹ ^ i := by ring
  · intro y hy
    have hy0 : y ≠ 0 := hy
    have hs : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hpos : 0 < ‖y‖ + P.L0 := by positivity
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [φ, chartS, chartT, sub_nonneg]
      rw [div_le_one hpos]
      linarith
    · simp only [φ, chartS, chartT]
      have : 0 ≤ ‖y‖ / (‖y‖ + P.L0) := by positivity
      linarith
    · have h2 : |y 2| ≤ ‖y‖ := by
        simpa using PiLp.norm_apply_le y 2
      simp only [φ, heightRatio]
      rw [le_div_iff₀ hs]
      linarith [abs_le.mp h2]
    · have h2 : |y 2| ≤ ‖y‖ := by
        simpa using PiLp.norm_apply_le y 2
      simp only [φ, heightRatio]
      rw [div_le_one hs]
      linarith [abs_le.mp h2]

private lemma hom_zero_eq {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ} (hd : 1 ≤ d) {f : E → F}
    (hh : ∀ c : ℝ, 0 < c → ∀ x, f (c • x) = c ^ d • f x) : f 0 = 0 := by
  have h := hh 2 (by norm_num) 0
  rw [smul_zero] at h
  have h2 : (1 : ℝ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  have h3 : ((2 : ℝ) ^ d - 1) • f 0 = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_eq_zero.mp h3).resolve_left (by linarith)

private lemma hom_bound {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ} (hd : 1 ≤ d) {f : E → F}
    (hf : ContinuousOn f {x | x ≠ 0}) (hh : ∀ c : ℝ, 0 < c → ∀ x, f (c • x) = c ^ d • f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ d := by
  have hsub : Metric.sphere (0 : E) 1 ⊆ {x : E | x ≠ 0} := by
    intro y hy
    show y ≠ 0
    intro h0
    rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hy
    exact zero_ne_one hy
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hom_zero_eq hd hh, norm_zero]
    positivity
  have hs : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : E := ‖x‖⁻¹ • x with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
  have hxu : ‖x‖ • u = x := by rw [hu, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hb : ‖f u‖ ≤ max C 0 := (hC u (by simp [hun])).trans (le_max_left _ _)
  rw [← hxu, hh _ hs, norm_smul, norm_pow, norm_norm, hxu, mul_comm]
  gcongr

theorem hom_contDiffAt_zero {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (m : ℕ) :
    ∀ (d : ℕ) (f : E → F), m < d → ContDiffOn ℝ m f {x | x ≠ 0} →
      (∀ c : ℝ, 0 < c → ∀ x, f (c • x) = c ^ d • f x) → ContDiffAt ℝ m f 0 := by
  induction m generalizing F with
  | zero =>
    intro d f hd hf hh
    rw [Nat.cast_zero, contDiffAt_zero]
    refine ⟨Set.univ, Filter.univ_mem, fun x _ => ?_⟩
    apply ContinuousAt.continuousWithinAt
    rcases eq_or_ne x 0 with rfl | hx
    · obtain ⟨C, hC0, hC⟩ := hom_bound (by omega) hf.continuousOn hh
      have h0 := hom_zero_eq (by omega) hh
      show Filter.Tendsto f (nhds 0) (nhds (f 0))
      rw [h0]
      apply squeeze_zero_norm hC
      have hc : Continuous (fun x : E => C * ‖x‖ ^ d) := continuous_const.mul (continuous_norm.pow d)
      have := hc.tendsto 0
      simpa [zero_pow (by omega : d ≠ 0)] using this
    · have hf0 : ContinuousOn f {x : E | x ≠ 0} := hf.continuousOn
      exact hf0.continuousAt (isOpen_ne.mem_nhds hx)
  | succ m ih =>
    intro d f hd hf hh
    have hU : IsOpen {x : E | x ≠ 0} := isOpen_ne
    obtain ⟨C, hC0, hC⟩ := hom_bound (by omega) hf.continuousOn hh
    have h0 := hom_zero_eq (by omega) hh
    have hdiff : ∀ x : E, x ≠ 0 → DifferentiableAt ℝ f x := fun x hx =>
      ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    have hD0 : HasFDerivAt f (0 : E →L[ℝ] F) 0 := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      simp only [zero_add, h0, sub_zero, ContinuousLinearMap.zero_apply]
      have hO : f =O[nhds 0] (fun x : E => ‖x‖ ^ d) := by
        refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall (fun x => ?_))
        rw [norm_pow, norm_norm]
        exact hC x
      exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by omega))
    have hfd0 : fderiv ℝ f 0 = 0 := hD0.fderiv
    rw [Nat.cast_succ, contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fderiv ℝ f, ⟨Set.univ, Filter.univ_mem, fun x _ => ?_⟩, ?_⟩
    · rcases eq_or_ne x 0 with rfl | hx
      · rw [hfd0]
        exact hD0
      · exact (hdiff x hx).hasFDerivAt
    · refine ih (d - 1) (fderiv ℝ f) (by omega) (hf.fderiv_of_isOpen hU (by push_cast; exact le_rfl)) ?_
      intro c hc x
      rcases eq_or_ne x 0 with rfl | hx
      · rw [smul_zero, hfd0, smul_zero]
      have hcx : c • x ≠ 0 := smul_ne_zero hc.ne' hx
      have hfun : (fun y => f (c • y)) = fun y => c ^ d • f y := funext (hh c hc)
      have hL : HasFDerivAt (fun y : E => c • y) (c • ContinuousLinearMap.id ℝ E) x :=
        (hasFDerivAt_id x).const_smul c
      have h1 : HasFDerivAt (fun y => f (c • y)) ((fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ E)) x :=
        (hdiff _ hcx).hasFDerivAt.comp x hL
      have h2 : HasFDerivAt (fun y => c ^ d • f y) (c ^ d • fderiv ℝ f x) x :=
        (hdiff x hx).hasFDerivAt.const_smul (c ^ d)
      rw [hfun] at h1
      have heq := h1.unique h2
      ext v
      have hv := congrArg (fun L : E →L[ℝ] F => L v) heq
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, map_smul] at hv
      have hd1 : c ^ d = c * c ^ (d - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hd1, mul_smul] at hv
      have := smul_right_injective F hc.ne' hv
      simpa using this

private def axisCore (k : ℤ) (w : ℂ) : ℂ :=
  ((‖w‖ ^ 4 : ℝ) : ℂ) * Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ))

private lemma axisCore_hom (k : ℤ) : ∀ c : ℝ, 0 < c → ∀ w, axisCore k (c • w) = c ^ 4 • axisCore k w := by
  intro c hc w
  simp only [axisCore, Complex.real_smul]
  rw [Complex.arg_real_mul w hc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
  push_cast
  ring

private lemma exp_arg_zpow (k : ℤ) {w : ℂ} (hw : w ≠ 0) :
    Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ)) = (w * ((‖w‖ : ℝ) : ℂ)⁻¹) ^ k := by
  have hn : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have he : Complex.exp (Complex.arg w * Complex.I) = w * ((‖w‖ : ℝ) : ℂ)⁻¹ := by
    rw [← div_eq_mul_inv, eq_div_iff hn, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I w
  rw [← he, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

private lemma unit_zpow_contDiffAt (k : ℤ) {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ 3 (fun v : ℂ => (v * ((‖v‖ : ℝ) : ℂ)⁻¹) ^ k) w := by
  have hn : ContDiffAt ℝ 3 (fun v : ℂ => ((‖v‖ : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (contDiffAt_norm ℝ hw)
  have hn0 : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have hu : ContDiffAt ℝ 3 (fun v : ℂ => v * ((‖v‖ : ℝ) : ℂ)⁻¹) w :=
    contDiffAt_id.mul (hn.inv hn0)
  have hu0 : w * ((‖w‖ : ℝ) : ℂ)⁻¹ ≠ 0 := mul_ne_zero hw (inv_ne_zero hn0)
  rcases k with n | n
  · simpa using hu.pow n
  · simp only [zpow_negSucc]
    exact (hu.pow (n + 1)).inv (pow_ne_zero _ hu0)

private lemma axisCore_contDiffOn (k : ℤ) : ContDiffOn ℝ 3 (axisCore k) {w | w ≠ 0} := by
  intro w hw
  have hw0 : w ≠ 0 := hw
  have heq : (fun v : ℂ => ((‖v‖ ^ 4 : ℝ) : ℂ) * (v * ((‖v‖ : ℝ) : ℂ)⁻¹) ^ k) =ᶠ[nhds w]
      axisCore k := by
    filter_upwards [isOpen_ne.mem_nhds hw0] with v hv
    simp only [axisCore]
    rw [exp_arg_zpow k hv]
  have hc : ContDiffAt ℝ 3 (fun v : ℂ => ((‖v‖ ^ 4 : ℝ) : ℂ) * (v * ((‖v‖ : ℝ) : ℂ)⁻¹) ^ k) w :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp w ((contDiffAt_norm ℝ hw0).pow 4)).mul
      (unit_zpow_contDiffAt k hw0)
  exact (hc.congr_of_eventuallyEq heq.symm).contDiffWithinAt

private lemma axisCore_contDiffAt (k : ℤ) (w : ℂ) : ContDiffAt ℝ 3 (axisCore k) w := by
  rcases eq_or_ne w 0 with rfl | hw
  · have h := hom_contDiffAt_zero (E := ℂ) (F := ℂ) 3 4 (axisCore k) (by norm_num)
      (by simpa using axisCore_contDiffOn k) (axisCore_hom k)
    simpa using h
  · exact (axisCore_contDiffOn k).contDiffAt (isOpen_ne.mem_nhds hw)

private def planeMap : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 3)) +
    Complex.I • Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 3))

private lemma planeMap_apply (y : Space) : planeMap y = (⟨y 0, y 1⟩ : ℂ) := by
  apply Complex.ext <;> simp [planeMap]

private lemma norm_sq_space (y : Space) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem axis_symbol (k : ℤ) :
    SymbolW {y : Space | y ≠ 0} (fun _ => 1)
      (fun y => ((qOf y ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (((k : ℝ) * angleOf y : ℝ) : ℂ))) := by
  refine SymbolW.of_homogeneous (subset_refl _) ?_ ?_
  · intro y hy
    have hy0 : y ≠ 0 := hy
    have heq : (fun v : Space => axisCore k (planeMap v) * (((‖v‖ ^ 4)⁻¹ : ℝ) : ℂ)) =ᶠ[nhds y]
        (fun y => ((qOf y ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((k : ℝ) * angleOf y : ℝ) : ℂ))) := by
      filter_upwards [isOpen_ne.mem_nhds hy0] with v hv
      have hv0 : v ≠ 0 := hv
      have hs : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have hp2 : ‖planeMap v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
        rw [planeMap_apply, Complex.sq_norm, Complex.normSq_mk]
        ring
      have hs2 := norm_sq_space v
      have hq : qOf v ^ 2 = ‖planeMap v‖ ^ 4 * (‖v‖ ^ 4)⁻¹ := by
        have e4 : ‖planeMap v‖ ^ 4 = (‖planeMap v‖ ^ 2) ^ 2 := by ring
        rw [e4, hp2]
        simp only [qOf, heightRatio]
        field_simp
        rw [hs2]
        ring
      simp only [axisCore]
      rw [hq, planeMap_apply]
      simp only [angleOf]
      push_cast
      ring
    have hc : ContDiffAt ℝ 3 (fun v : Space => axisCore k (planeMap v) * (((‖v‖ ^ 4)⁻¹ : ℝ) : ℂ)) y := by
      have h1 : ContDiffAt ℝ 3 (fun v : Space => axisCore k (planeMap v)) y :=
        (axisCore_contDiffAt k (planeMap y)).comp y planeMap.contDiff.contDiffAt
      have h2 : ContDiffAt ℝ 3 (fun v : Space => (‖v‖ ^ 4)⁻¹) y :=
        ((contDiffAt_norm ℝ hy0).pow 4).inv (by positivity)
      exact h1.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y h2)
    exact (hc.congr_of_eventuallyEq heq.symm).contDiffWithinAt
  · intro y c hc
    have hq : qOf (c • y) = qOf y := by simp only [qOf, heightRatio_smul y hc]
    have ha : angleOf (c • y) = angleOf y := by
      simp only [angleOf]
      have : (⟨(c • y) 0, (c • y) 1⟩ : ℂ) = (c : ℂ) * ⟨y 0, y 1⟩ := by
        apply Complex.ext <;> simp
      rw [this, Complex.arg_real_mul _ hc]
    rw [hq, ha]

private lemma phase_deriv_bound (a : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, ∀ i ≤ 3,
    ‖iteratedFDeriv ℝ i (fun v : ℝ => Complex.exp (Complex.I * ((a * v : ℝ) : ℂ))) u‖ ≤ M := by
  set G : ℝ → ℂ := fun v => Complex.exp (Complex.I * ((a * v : ℝ) : ℂ)) with hG
  have hGc : ContDiff ℝ 3 G := by
    have h1 : ContDiff ℝ 3 (fun v : ℝ => Complex.I * ((a * v : ℝ) : ℂ)) :=
      contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))
    exact Complex.contDiff_exp.comp h1
  refine ⟨∑ i ∈ Finset.range 4, ‖iteratedFDeriv ℝ i G 0‖,
    Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun u i hi => ?_⟩
  let L : ℂ →L[ℝ] ℂ := G u • ContinuousLinearMap.id ℝ ℂ
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
    have hGu : ‖G u‖ = 1 := by
      simp only [hG]
      rw [Complex.norm_exp]
      simp
    simp [L, hGu]
  have hshift : G = fun v => L (G (v + -u)) := by
    funext v
    simp only [L, hG, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcd : ContDiffAt ℝ i (fun v => G (v + -u)) u :=
    ((hGc.comp (contDiff_id.add contDiff_const)).contDiffAt).of_le (by exact_mod_cast hi)
  calc ‖iteratedFDeriv ℝ i G u‖ = ‖iteratedFDeriv ℝ i (fun v => L (G (v + -u))) u‖ := by
        rw [← hshift]
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ i (fun v => G (v + -u)) u‖ :=
        L.norm_iteratedFDeriv_comp_left hcd le_rfl
    _ ≤ 1 * ‖iteratedFDeriv ℝ i G 0‖ := by
        rw [iteratedFDeriv_comp_add_right, add_neg_cancel]
        gcongr
    _ ≤ ∑ i ∈ Finset.range 4, ‖iteratedFDeriv ℝ i G 0‖ := by
        rw [one_mul]
        exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i G 0‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))

private lemma logRad_deriv1 {rc : ℝ} (hrc : 0 < rc) :
    deriv (fun r : ℝ => (1 / 2) * Real.log (1 + r ^ 2 / rc ^ 2)) = fun r => r / (r ^ 2 + rc ^ 2) := by
  funext r
  have hq : 0 < 1 + r ^ 2 / rc ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2 / rc ^ 2) (2 * r / rc ^ 2) r :=
    (((hasDerivAt_pow 2 r).div_const (rc ^ 2)).const_add 1).congr_deriv (by norm_num)
  have h2 := (h1.log hq.ne').const_mul (1 / 2 : ℝ)
  rw [h2.deriv]
  have : 0 < rc ^ 2 := by positivity
  field_simp
  ring

private lemma logRad_deriv2 {rc : ℝ} (hrc : 0 < rc) :
    deriv (fun r : ℝ => r / (r ^ 2 + rc ^ 2)) = fun r => (rc ^ 2 - r ^ 2) / (r ^ 2 + rc ^ 2) ^ 2 := by
  funext r
  have hq : r ^ 2 + rc ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2 + rc ^ 2) (2 * r) r :=
    ((hasDerivAt_pow 2 r).add_const (rc ^ 2)).congr_deriv (by norm_num)
  have h : HasDerivAt (fun r : ℝ => r / (r ^ 2 + rc ^ 2))
      (((1 : ℝ) * (r ^ 2 + rc ^ 2) - r * (2 * r)) / (r ^ 2 + rc ^ 2) ^ 2) r := (hasDerivAt_id r).div h1 hq
  rw [h.deriv]
  field_simp
  ring

private lemma logRad_deriv3 {rc : ℝ} (hrc : 0 < rc) :
    deriv (fun r : ℝ => (rc ^ 2 - r ^ 2) / (r ^ 2 + rc ^ 2) ^ 2) =
      fun r => (2 * r ^ 3 - 6 * rc ^ 2 * r) / (r ^ 2 + rc ^ 2) ^ 3 := by
  funext r
  have hq : r ^ 2 + rc ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2 + rc ^ 2) (2 * r) r :=
    ((hasDerivAt_pow 2 r).add_const (rc ^ 2)).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun r : ℝ => (r ^ 2 + rc ^ 2) ^ 2) (2 * (r ^ 2 + rc ^ 2) * (2 * r)) r :=
    (h1.pow 2).congr_deriv (by norm_num)
  have h3 : HasDerivAt (fun r : ℝ => rc ^ 2 - r ^ 2) (-(2 * r)) r :=
    ((hasDerivAt_pow 2 r).const_sub (rc ^ 2)).congr_deriv (by norm_num)
  have h : HasDerivAt (fun r : ℝ => (rc ^ 2 - r ^ 2) / (r ^ 2 + rc ^ 2) ^ 2)
      ((-(2 * r) * (r ^ 2 + rc ^ 2) ^ 2 - (rc ^ 2 - r ^ 2) * (2 * (r ^ 2 + rc ^ 2) * (2 * r))) /
        ((r ^ 2 + rc ^ 2) ^ 2) ^ 2) r := h3.div h2 (pow_ne_zero 2 hq)
  rw [h.deriv]
  field_simp
  ring

private lemma logRad_iter {rc : ℝ} (hrc : 0 < rc) {s : ℝ} (hs : 0 < s) (i : ℕ) (hi1 : 1 ≤ i)
    (hi3 : i ≤ 3) :
    |iteratedDeriv i (fun r : ℝ => (1 / 2) * Real.log (1 + r ^ 2 / rc ^ 2)) s| ≤ 8 * s⁻¹ ^ i := by
  have hr2 : 0 < rc ^ 2 := by positivity
  have hq : 0 < s ^ 2 + rc ^ 2 := by positivity
  have hs2 : s ^ 2 ≤ s ^ 2 + rc ^ 2 := by linarith
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  interval_cases i
  · rw [iteratedDeriv_one, logRad_deriv1 hrc, abs_div, abs_of_pos hq, abs_of_pos hs,
      div_le_iff₀ hq]
    have e : s⁻¹ ^ 1 * s ^ 2 = s := by field_simp
    have h1 : s⁻¹ ^ 1 * s ^ 2 ≤ s⁻¹ ^ 1 * (s ^ 2 + rc ^ 2) := by gcongr
    nlinarith
  · rw [iteratedDeriv_succ, iteratedDeriv_one, logRad_deriv1 hrc, logRad_deriv2 hrc, abs_div,
      abs_of_pos (pow_pos hq 2), div_le_iff₀ (pow_pos hq 2)]
    have hn : |rc ^ 2 - s ^ 2| ≤ s ^ 2 + rc ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    have e : s⁻¹ ^ 2 * s ^ 2 = 1 := by field_simp
    have h1 : s⁻¹ ^ 2 * s ^ 2 ≤ s⁻¹ ^ 2 * (s ^ 2 + rc ^ 2) := by gcongr
    have h2 : (s ^ 2 + rc ^ 2) * 1 ≤ (s ^ 2 + rc ^ 2) * (s⁻¹ ^ 2 * (s ^ 2 + rc ^ 2)) :=
      mul_le_mul_of_nonneg_left (by rw [e] at h1; exact h1) hq.le
    nlinarith
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, logRad_deriv1 hrc,
      logRad_deriv2 hrc, logRad_deriv3 hrc, abs_div, abs_of_pos (pow_pos hq 3),
      div_le_iff₀ (pow_pos hq 3)]
    have hn : |2 * s ^ 3 - 6 * rc ^ 2 * s| ≤ 6 * s * (s ^ 2 + rc ^ 2) := by
      have e : 2 * s ^ 3 - 6 * rc ^ 2 * s = s * (2 * s ^ 2 - 6 * rc ^ 2) := by ring
      rw [e, abs_mul, abs_of_pos hs]
      have : |2 * s ^ 2 - 6 * rc ^ 2| ≤ 6 * (s ^ 2 + rc ^ 2) := by
        rw [abs_le]
        constructor <;> nlinarith
      nlinarith
    have e : s⁻¹ ^ 3 * (s ^ 2) ^ 2 = s := by field_simp
    have h4 : (s ^ 2) ^ 2 ≤ (s ^ 2 + rc ^ 2) ^ 2 := by gcongr
    have h1 : s⁻¹ ^ 3 * (s ^ 2) ^ 2 ≤ s⁻¹ ^ 3 * (s ^ 2 + rc ^ 2) ^ 2 := by gcongr
    have h2 : (s ^ 2 + rc ^ 2) * s ≤ (s ^ 2 + rc ^ 2) * (s⁻¹ ^ 3 * (s ^ 2 + rc ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (by rw [e] at h1; exact h1) hq.le
    have h3 : 6 * s * (s ^ 2 + rc ^ 2) ≤ 8 * ((s ^ 2 + rc ^ 2) * s) := by nlinarith
    calc |2 * s ^ 3 - 6 * rc ^ 2 * s| ≤ 6 * s * (s ^ 2 + rc ^ 2) := hn
      _ ≤ 8 * ((s ^ 2 + rc ^ 2) * s) := h3
      _ ≤ 8 * ((s ^ 2 + rc ^ 2) * (s⁻¹ ^ 3 * (s ^ 2 + rc ^ 2) ^ 2)) := by gcongr
      _ = 8 * s⁻¹ ^ 3 * (s ^ 2 + rc ^ 2) ^ 3 := by ring

theorem logPhase_symbol {P : ChartParams} (hP : IsChartParams P) (a : ℝ) :
    SymbolW {y : Space | y ≠ 0} (fun _ => 1)
      (fun y => Complex.exp (Complex.I * ((a * logPhase P y : ℝ) : ℂ))) := by
  have hrc := hP.rc_pos
  obtain ⟨M, hM0, hM⟩ := phase_deriv_bound a
  let ℓ : ℝ → ℝ := fun r => (1 / 2) * Real.log (1 + r ^ 2 / P.rc ^ 2)
  let G : ℝ → ℂ := fun v => Complex.exp (Complex.I * ((a * v : ℝ) : ℂ))
  have hfun : (fun y : Space => Complex.exp (Complex.I * ((a * logPhase P y : ℝ) : ℂ))) =
      fun y => (G ∘ ℓ) ‖y‖ := rfl
  rw [hfun]
  have hℓ : ContDiff ℝ 3 ℓ :=
    contDiff_const.mul ((contDiff_const.add ((contDiff_id.pow 2).div_const _)).log
      (fun r => by positivity))
  have hG : ContDiff ℝ 3 G := by
    have h1 : ContDiff ℝ 3 (fun v : ℝ => Complex.I * ((a * v : ℝ) : ℂ)) :=
      contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))
    exact Complex.contDiff_exp.comp h1
  refine SymbolW.of_radial (h := G ∘ ℓ) (fun _ => zero_le_one) (hG.comp hℓ).contDiffOn
    ⟨6 * M * 8 ^ 3, by positivity, fun s hs i hi => ?_⟩
  have hsi : 0 ≤ s⁻¹ := by positivity
  have hFdB := norm_iteratedFDerivWithin_comp_le (hG.contDiffOn (s := Set.univ))
    (hℓ.contDiffOn (s := Set.univ)) (n := i) (by exact_mod_cast hi) uniqueDiffOn_univ uniqueDiffOn_univ
    (Set.mapsTo_univ _ _) (Set.mem_univ s) (C := M) (D := 8 * s⁻¹)
    (fun k hk => by
      rw [iteratedFDerivWithin_univ]
      exact hM (ℓ s) k (hk.trans hi))
    (fun k hk1 hk => by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      refine (logRad_iter hrc hs k hk1 (hk.trans hi)).trans ?_
      rw [mul_pow]
      gcongr
      calc (8 : ℝ) = 8 ^ 1 := (pow_one _).symm
        _ ≤ 8 ^ k := pow_le_pow_right₀ (by norm_num) hk1)
  rw [iteratedFDerivWithin_univ] at hFdB
  have hfact : (i.factorial : ℝ) ≤ 6 := by
    interval_cases i <;> norm_num [Nat.factorial]
  have h8 : (8 : ℝ) ^ i ≤ 8 ^ 3 := pow_le_pow_right₀ (by norm_num) hi
  calc ‖iteratedFDeriv ℝ i (G ∘ ℓ) s‖ ≤ (i.factorial : ℝ) * M * (8 * s⁻¹) ^ i := hFdB
    _ = (i.factorial : ℝ) * M * 8 ^ i * s⁻¹ ^ i := by rw [mul_pow]; ring
    _ ≤ 6 * M * 8 ^ 3 * s⁻¹ ^ i := by gcongr
    _ = 6 * M * 8 ^ 3 * (fun _ => (1 : ℝ)) s * s⁻¹ ^ i := by simp

private lemma shiftedPow_iteratedDeriv (L b s : ℝ) (i : ℕ) :
    iteratedDeriv i (fun r => L ^ b * (r + L) ^ (-b)) s =
      L ^ b * ((descPochhammer ℝ i).eval (-b) * (s + L) ^ (-b - i)) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const i (fun r : ℝ => r ^ (-b)) L]
  simp only []
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

private lemma fallingProduct_small {b : ℝ} (hb0 : 0 ≤ b) (hb2 : b ≤ 2) {i : ℕ} (hi : i ≤ 3) :
    |(descPochhammer ℝ i).eval (-b)| ≤ 24 := by
  interval_cases i
  · simp
  · simp only [descPochhammer_one, Polynomial.eval_X, abs_neg]
    rw [abs_of_nonneg hb0]
    linarith
  · have he : (descPochhammer ℝ 2).eval (-b) = b * (b + 1) := by
      simp only [descPochhammer_succ_right, descPochhammer_zero, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_natCast, Polynomial.eval_one]
      push_cast
      ring
    rw [he, abs_of_nonneg (by positivity)]
    nlinarith
  · have he : (descPochhammer ℝ 3).eval (-b) = -(b * (b + 1) * (b + 2)) := by
      simp only [descPochhammer_succ_right, descPochhammer_zero, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_natCast, Polynomial.eval_one]
      push_cast
      ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
    have h1 : b * (b + 1) ≤ 6 := by nlinarith
    have h2 : 0 ≤ b * (b + 1) := by positivity
    nlinarith

private lemma shiftedPow_le {L b s : ℝ} (hL : 0 < L) (hs : 0 < s) (hb0 : 0 ≤ b) (i : ℕ) :
    L ^ b * (s + L) ^ (-b - i) ≤ ((s + L) ^ i)⁻¹ := by
  have hpos : 0 < s + L := by linarith
  rw [Real.rpow_sub hpos, Real.rpow_natCast, Real.rpow_neg hpos.le, div_eq_mul_inv, ← mul_assoc]
  have h1 : L ^ b * ((s + L) ^ b)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hpos b)]
    exact Real.rpow_le_rpow hL.le (by linarith) hb0
  have h2 : 0 ≤ ((s + L) ^ i)⁻¹ := by positivity
  calc L ^ b * ((s + L) ^ b)⁻¹ * ((s + L) ^ i)⁻¹ ≤ 1 * ((s + L) ^ i)⁻¹ := by gcongr
    _ = ((s + L) ^ i)⁻¹ := one_mul _

private lemma chartS_eq {P : ChartParams} (hP : IsChartParams P) (y : Space) :
    chartS P y = P.L0 / (‖y‖ + P.L0) := by
  have hL := hP.L0_pos
  have : 0 < ‖y‖ + P.L0 := by positivity
  simp only [chartS, chartT]
  field_simp
  ring

private lemma chartS_rpow {P : ChartParams} (hP : IsChartParams P) (y : Space) (b : ℝ) :
    chartS P y ^ b = P.L0 ^ b * (‖y‖ + P.L0) ^ (-b) := by
  have hL := hP.L0_pos
  have hpos : 0 < ‖y‖ + P.L0 := by positivity
  rw [chartS_eq hP, Real.div_rpow hL.le hpos.le, Real.rpow_neg hpos.le, div_eq_mul_inv]

private lemma shiftedPow_contDiffAt {L b s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    ContDiffAt ℝ 3 (fun r : ℝ => L ^ b * (r + L) ^ (-b)) s := by
  have h1 : ContDiffAt ℝ 3 (fun r : ℝ => r + L) s := contDiffAt_id.add contDiffAt_const
  exact contDiffAt_const.mul (h1.rpow_const_of_ne (by linarith))

theorem decay_symbol {P : ChartParams} (hP : IsChartParams P) :
    SymbolW {y : Space | y ≠ 0} (fun _ => 1) (fun y => (decayFactor P y : ℂ)) := by
  have hL := hP.L0_pos
  have he := hP.eps_pos
  have he2 := hP.eps_lt
  have hb0 : 0 ≤ 2 * P.eps := by linarith
  have hb2 : 2 * P.eps ≤ 2 := by linarith
  let g : ℝ → ℝ := fun r => P.L0 ^ (2 * P.eps) * (r + P.L0) ^ (-(2 * P.eps))
  have hfun : (fun y : Space => (decayFactor P y : ℂ)) = fun y => ((g ‖y‖ : ℝ) : ℂ) := by
    funext y
    simp only [decayFactor, g, chartS_rpow hP]
  rw [hfun]
  refine SymbolW.of_radial (h := fun r => ((g r : ℝ) : ℂ)) (fun _ => zero_le_one) ?_ ⟨24, by norm_num, ?_⟩
  · intro s hs
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp s
      (shiftedPow_contDiffAt (b := 2 * P.eps) hL hs)).contDiffWithinAt
  · intro s hs i hi
    refine (ofReal_iteratedFDeriv_le ((shiftedPow_contDiffAt (b := 2 * P.eps) hL hs).of_le
      (by exact_mod_cast hi))).trans ?_
    rw [shiftedPow_iteratedDeriv, Real.norm_eq_abs]
    have hpos : 0 < s + P.L0 := by linarith
    have hp := fallingProduct_small hb0 hb2 hi
    have hw := shiftedPow_le hL hs hb0 i
    have hw0 : 0 ≤ P.L0 ^ (2 * P.eps) * (s + P.L0) ^ (-(2 * P.eps) - i) := by positivity
    have hsi : ((s + P.L0) ^ i)⁻¹ ≤ s⁻¹ ^ i := by
      rw [← inv_pow]
      gcongr
      linarith
    calc |P.L0 ^ (2 * P.eps) * ((descPochhammer ℝ i).eval (-(2 * P.eps)) *
          (s + P.L0) ^ (-(2 * P.eps) - i))|
        = |(descPochhammer ℝ i).eval (-(2 * P.eps))| *
            (P.L0 ^ (2 * P.eps) * (s + P.L0) ^ (-(2 * P.eps) - i)) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hL.le _),
            abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
          ring
      _ ≤ 24 * s⁻¹ ^ i := by
          gcongr
          exact hw.trans hsi
      _ = 24 * (fun _ => (1 : ℝ)) s * s⁻¹ ^ i := by simp

theorem coreRatio_symbol {P : ChartParams} (hP : IsChartParams P) :
    SymbolW {y : Space | y ≠ 0} (fun _ => 1) (fun y => (coreRatioT P (chartT P y) : ℂ)) := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have hL := hP.L0_pos
  have hrc := hP.rc_pos
  obtain ⟨C1, hC1, hb1⟩ := real_deriv_bound hU (chartS_symbol hP)
  let F : ℝ → ℂ := fun u => ((coreRatioT P (1 - u) : ℝ) : ℂ)
  have hfun : (fun y => (coreRatioT P (chartT P y) : ℂ)) = fun y => F (chartS P y) := by
    funext y
    simp only [F, chartS, sub_sub_cancel]
  rw [hfun]
  have hden : ∀ u : ℝ, P.L0 ^ 2 * (1 - u) ^ 2 + P.rc ^ 2 * (1 - (1 - u)) ^ 2 ≠ 0 := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · simp only [sub_zero, one_pow, mul_one, sub_self]
      positivity
    · have h1 : 0 < P.rc ^ 2 * (1 - (1 - u)) ^ 2 := by
        have : 1 - (1 - u) ≠ 0 := by simpa using hu
        positivity
      have h2 : 0 ≤ P.L0 ^ 2 * (1 - u) ^ 2 := by positivity
      linarith
  have hc : ContDiff ℝ 3 (fun u : ℝ => P.L0 ^ 2 * (1 - u) ^ 2 /
      (P.L0 ^ 2 * (1 - u) ^ 2 + P.rc ^ 2 * (1 - (1 - u)) ^ 2)) := by
    apply ContDiff.div
    · exact contDiff_const.mul ((contDiff_const.sub contDiff_id).pow 2)
    · exact (contDiff_const.mul ((contDiff_const.sub contDiff_id).pow 2)).add
        (contDiff_const.mul ((contDiff_const.sub (contDiff_const.sub contDiff_id)).pow 2))
    · exact hden
  have hF : ContDiff ℝ 3 F := Complex.ofRealCLM.contDiff.comp hc
  refine SymbolW.comp hU (chartS_contDiffOn hP) (c := C1) (fun y hy i _ hi3 => hb1 y hy i hi3)
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)) ?_ hF
  intro y hy
  have hy0 : y ≠ 0 := hy
  have hs : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hpos : 0 < ‖y‖ + P.L0 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [chartS, chartT, sub_nonneg]
    rw [div_le_one hpos]
    linarith
  · simp only [chartS, chartT]
    have : 0 ≤ ‖y‖ / (‖y‖ + P.L0) := by positivity
    linarith

def vecOf (c : Fin 3) (y : Space) (i : Fin 3) : ℝ :=
  ![radialVec y i, polarVecQ y i, azimVecQ y i] c

theorem vecOf_symbol (c i : Fin 3) :
    SymbolW {y : Space | y ≠ 0} (fun _ => 1) (fun y => ((vecOf c y i : ℝ) : ℂ)) := by
  refine SymbolW.of_homogeneous_real (subset_refl _) ?_ ?_
  · fin_cases c
    · simpa [vecOf] using radialVec_contDiffOn i
    · simpa [vecOf] using polarVecQ_contDiffOn i
    · simpa [vecOf] using azimVecQ_contDiffOn i
  · intro y a ha
    fin_cases c
    · simpa [vecOf] using radialVec_smul i y ha
    · simpa [vecOf] using polarVecQ_smul i y ha
    · simpa [vecOf] using azimVecQ_smul i y ha

def waveModel (P : ChartParams) (k : ℤ) (a : ℝ) (Q1 Q2 : MvPolynomial (Fin 2) ℂ) (c i : Fin 3)
    (y : Space) : ℂ :=
  (decayFactor P y : ℂ) *
    ((((qOf y ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (((k : ℝ) * angleOf y : ℝ) : ℂ))) *
      (Complex.exp (Complex.I * ((a * logPhase P y : ℝ) : ℂ)) *
        (((chartT P y : ℂ) * (chartT P y : ℂ)) *
          ((MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q1 +
            (coreRatioT P (chartT P y) : ℂ) *
              MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q2) *
            ((vecOf c y i : ℝ) : ℂ)))))

theorem waveModel_symbol {P : ChartParams} (hP : IsChartParams P) (k : ℤ) (a : ℝ)
    (Q1 Q2 : MvPolynomial (Fin 2) ℂ) (c i : Fin 3) :
    SymbolW {y : Space | y ≠ 0} (fun s => 1 * (1 * (1 * ((|s| * |s|) * (1 * 1)))))
      (waveModel P k a Q1 Q2 c i) := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have h1 : ∀ s : ℝ, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) s := fun _ => zero_le_one
  have ha : ∀ s : ℝ, (0 : ℝ) ≤ |s| := fun s => abs_nonneg s
  have hpoly : SymbolW {y : Space | y ≠ 0} (fun _ => 1)
      (fun y => MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q1 +
        (coreRatioT P (chartT P y) : ℂ) *
          MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q2) := by
    refine SymbolW.add hU (piece_symbol hP Q1 1) ?_
    exact (SymbolW.mul hU h1 h1 (coreRatio_symbol hP) (piece_symbol hP Q2 1)).weight_le zero_le_one
      (fun y _ => by simp)
  have hpv := SymbolW.mul hU h1 h1 hpoly (vecOf_symbol c i)
  have htt := SymbolW.mul hU ha ha (chartT_symbol hP) (chartT_symbol hP)
  have h4 := SymbolW.mul hU (fun s => mul_nonneg (ha s) (ha s)) (fun s => by positivity) htt hpv
  have h5 := SymbolW.mul hU h1 (fun s => by positivity) (logPhase_symbol hP a) h4
  have h6 := SymbolW.mul hU h1 (fun s => by positivity) (axis_symbol k) h5
  exact SymbolW.mul hU h1 (fun s => by positivity) (decay_symbol hP) h6

theorem waveModel_third {P : ChartParams} (hP : IsChartParams P) (k : ℤ) (a : ℝ)
    (Q1 Q2 : MvPolynomial (Fin 2) ℂ) (c i : Fin 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Space, y ≠ 0 → ContDiffAt ℝ 3 (waveModel P k a Q1 Q2 c i) y ∧
      ‖iteratedFDeriv ℝ 3 (waveModel P k a Q1 Q2 c i) y‖ ≤ K * ‖y‖⁻¹ := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have hs := waveModel_symbol hP k a Q1 Q2 c i
  obtain ⟨K, hK, hb⟩ := hs.third_le zero_le_one (fun s hs0 => by
    rw [abs_of_pos hs0]
    nlinarith)
  exact ⟨K, hK, fun y hy => ⟨hs.1.contDiffAt (hU.mem_nhds hy), hb y hy hy⟩⟩

theorem modePhase_split (P : ChartParams) (n : ℤ) (β : ℝ) (y : Space) :
    modePhase P n β y = Complex.exp (Complex.I * ((((n * (P.m : ℤ) : ℤ) : ℝ) * angleOf y : ℝ) : ℂ)) *
      Complex.exp (Complex.I * (((n * β) * logPhase P y : ℝ) : ℂ)) := by
  unfold modePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mvpoly_hasDerivAt_fst (Q : MvPolynomial (Fin 2) ℂ) (t x : ℝ) :
    HasDerivAt (fun t' : ℝ => MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] Q)
      (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 Q)) t := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    have key : HasDerivAt (fun t' : ℝ => MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] p +
        MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] q)
        (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 p) +
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 q)) t := hp.add hq
    simpa only [map_add] using key
  | mul_X p n hp =>
    fin_cases n
    · have h1 : HasDerivAt (fun t' : ℝ => (t' : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have key : HasDerivAt (fun t' : ℝ => MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] p * (t' : ℂ))
          (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 p) * (t : ℂ) +
            MvPolynomial.eval ![(t : ℂ), (x : ℂ)] p * 1) t := hp.mul h1
      have hf : (fun t' : ℝ => MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] (p * MvPolynomial.X ⟨0, by decide⟩)) =
          fun t' : ℝ => MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] p * (t' : ℂ) := by
        funext t'
        simp
      have hv : MvPolynomial.eval ![(t : ℂ), (x : ℂ)]
          (MvPolynomial.pderiv 0 (p * MvPolynomial.X ⟨0, by decide⟩)) =
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 p) * (t : ℂ) +
            MvPolynomial.eval ![(t : ℂ), (x : ℂ)] p * 1 := by
        simp [Derivation.leibniz, Fin.zero_eta]
        ring
      rw [hf, hv]
      exact key
    · have key : HasDerivAt (fun t' : ℝ => MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] p * (x : ℂ))
          (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 p) * (x : ℂ)) t :=
        hp.mul_const (x : ℂ)
      have hf : (fun t' : ℝ => MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] (p * MvPolynomial.X ⟨1, by decide⟩)) =
          fun t' : ℝ => MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] p * (x : ℂ) := by
        funext t'
        simp
      have hv : MvPolynomial.eval ![(t : ℂ), (x : ℂ)]
          (MvPolynomial.pderiv 0 (p * MvPolynomial.X ⟨1, by decide⟩)) =
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 p) * (x : ℂ) := by
        simp [Derivation.leibniz, Fin.mk_one, MvPolynomial.pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
        ring
      rw [hf, hv]
      exact key

theorem mvpoly_hasDerivAt_snd (Q : MvPolynomial (Fin 2) ℂ) (t x : ℝ) :
    HasDerivAt (fun x' : ℝ => MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] Q)
      (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 Q)) x := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const x a
  | add p q hp hq =>
    have key : HasDerivAt (fun x' : ℝ => MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] p +
        MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] q)
        (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 p) +
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 q)) x := hp.add hq
    simpa only [map_add] using key
  | mul_X p n hp =>
    fin_cases n
    · have key : HasDerivAt (fun x' : ℝ => MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] p * (t : ℂ))
          (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 p) * (t : ℂ)) x :=
        hp.mul_const (t : ℂ)
      have hf : (fun x' : ℝ => MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] (p * MvPolynomial.X ⟨0, by decide⟩)) =
          fun x' : ℝ => MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] p * (t : ℂ) := by
        funext x'
        simp
      have hv : MvPolynomial.eval ![(t : ℂ), (x : ℂ)]
          (MvPolynomial.pderiv 1 (p * MvPolynomial.X ⟨0, by decide⟩)) =
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 p) * (t : ℂ) := by
        simp [Derivation.leibniz, Fin.zero_eta, MvPolynomial.pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
        ring
      rw [hf, hv]
      exact key
    · have h1 : HasDerivAt (fun x' : ℝ => (x' : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
      have key : HasDerivAt (fun x' : ℝ => MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] p * (x' : ℂ))
          (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 p) * (x : ℂ) +
            MvPolynomial.eval ![(t : ℂ), (x : ℂ)] p * 1) x := hp.mul h1
      have hf : (fun x' : ℝ => MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] (p * MvPolynomial.X ⟨1, by decide⟩)) =
          fun x' : ℝ => MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] p * (x' : ℂ) := by
        funext x'
        simp
      have hv : MvPolynomial.eval ![(t : ℂ), (x : ℂ)]
          (MvPolynomial.pderiv 1 (p * MvPolynomial.X ⟨1, by decide⟩)) =
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 p) * (x : ℂ) +
            MvPolynomial.eval ![(t : ℂ), (x : ℂ)] p * 1 := by
        simp [Derivation.leibniz, Fin.mk_one]
        ring
      rw [hf, hv]
      exact key
theorem slice_deriv_fst {F G : ℝ → ℝ → ℂ} {t x : ℝ}
    (h : ∀ᶠ p : ℝ × ℝ in nhds (t, x), F p.1 p.2 = G p.1 p.2) :
    ∀ᶠ p : ℝ × ℝ in nhds (t, x), deriv (fun t' => F t' p.2) p.1 = deriv (fun t' => G t' p.2) p.1 := by
  filter_upwards [h.eventually_nhds] with p hp
  have hc : Filter.Tendsto (fun t' : ℝ => (t', p.2)) (nhds p.1) (nhds p) := by
    have := ((continuous_id.prodMk continuous_const : Continuous (fun t' : ℝ => (t', p.2)))).tendsto p.1
    simpa using this
  have he : (fun t' => F t' p.2) =ᶠ[nhds p.1] (fun t' => G t' p.2) := hc.eventually hp
  exact he.deriv_eq

theorem slice_deriv_snd {F G : ℝ → ℝ → ℂ} {t x : ℝ}
    (h : ∀ᶠ p : ℝ × ℝ in nhds (t, x), F p.1 p.2 = G p.1 p.2) :
    ∀ᶠ p : ℝ × ℝ in nhds (t, x), deriv (fun x' => F p.1 x') p.2 = deriv (fun x' => G p.1 x') p.2 := by
  filter_upwards [h.eventually_nhds] with p hp
  have hc : Filter.Tendsto (fun x' : ℝ => (p.1, x')) (nhds p.2) (nhds p) := by
    have := ((continuous_const.prodMk continuous_id : Continuous (fun x' : ℝ => (p.1, x')))).tendsto p.2
    simpa using this
  have he : (fun x' => F p.1 x') =ᶠ[nhds p.2] (fun x' => G p.1 x') := hc.eventually hp
  exact he.deriv_eq

private def flipPoly (σ : ℂ) (R : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.bind₁ (fun k : Fin 2 => if k = 0 then MvPolynomial.X 0 else MvPolynomial.C σ * MvPolynomial.X 1) R

private lemma eval_flipPoly (σ : ℂ) (R : MvPolynomial (Fin 2) ℂ) (t x : ℂ) :
    MvPolynomial.eval ![t, x] (flipPoly σ R) = MvPolynomial.eval ![t, σ * x] R := by
  induction R using MvPolynomial.induction_on with
  | C a => simp [flipPoly]
  | add p q hp hq => simp only [flipPoly, map_add] at *; rw [hp, hq]
  | mul_X p i hp =>
    simp only [flipPoly, map_mul] at *
    rw [hp]
    fin_cases i <;> simp

private def locPoly (S : Spline) (odd b : Bool) (i j : ℕ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C (if odd && b then -1 else 1) * flipPoly (if b then -1 else 1) (S.piece i j)

private lemma cellIndex_le (l : List ℝ) (u : ℝ) : cellIndex l u < l.length + 1 := by
  unfold cellIndex
  have h1 := List.length_filter_le (fun b => decide (b ≤ u)) ((l.drop 1).dropLast)
  simp only [List.length_dropLast, List.length_drop] at h1
  omega

private lemma spline_local (S : Spline) (odd : Bool) {t x : ℝ} (hx0 : x ≠ 0)
    (ht : t ∉ (S.mesh.tBreaks.drop 1).dropLast) (hx : |x| ∉ (S.mesh.xBreaks.drop 1).dropLast) :
    ∀ᶠ p : ℝ × ℝ in nhds (t, x), S.eval odd p.1 p.2 =
      MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)]
        (locPoly S odd (decide (x < 0)) (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|)) := by
  filter_upwards [eval_eventuallyEq S odd hx0 ht hx] with p hp
  rw [hp, locPoly, map_mul, MvPolynomial.eval_C, eval_flipPoly]
  by_cases h : x < 0 <;> simp [h]


private def radPart (D : FieldData) (n : ℤ) (L a : ℕ) (t x : ℝ) : ℂ :=
  weightPoly (L + 2) 1 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ (a + 2) * (D.amp n).radialAmp.eval false t x

private def polPart (D : FieldData) (n : ℤ) (L a : ℕ) (t x : ℝ) : ℂ :=
  weightPoly (L + 2) 1 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ (a + 2) * (D.amp n).polarAmp.eval true t x

private lemma reduced_wave_eq {P : ChartParams} {D : FieldData} {n : ℤ} (hn0 : n ≠ 0) (β : ℝ) {L a : ℕ}
    (hL : D.lowOrder n = L + 2) (ha : D.axisOrder n = a + 2) (hH : D.highOrder = 1) (t x : ℝ) :
    reducedField P D n β t x = ![radPart D n L a t x, polPart D n L a t x,
      (Complex.I / ((n * P.m : ℤ) : ℂ)) * (twistedScale P n β (radPart D n L a) t x + 2 * radPart D n L a t x -
        heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * polPart D n L a t' x') t x)] := by
  simp only [reducedField, if_neg hn0, hL, ha, hH]
  rfl

private lemma weight_hasDerivAt (L : ℕ) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => weightPoly (L + 2) 1 t')
      (((L + 2 : ℕ) : ℂ) * (t : ℂ) ^ (L + 1) * (1 - (t : ℂ)) - (t : ℂ) ^ (L + 2)) t := by
  have h := ((hasDerivAt_pow (L + 2) t).mul ((hasDerivAt_id' t).const_sub 1)).ofReal_comp
  convert h using 1
  · funext y
    simp [weightPoly]
  · push_cast
    ring

private lemma axis_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ)) (-(2 * (x : ℂ))) x := by
  have h := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
  convert h using 1
  push_cast
  ring

private def waveQ1 (P : ChartParams) (n : ℤ) (L a : ℕ) (A B : MvPolynomial (Fin 2) ℂ) :
    Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ L * (1 - MvPolynomial.X 0) * (1 - MvPolynomial.X 1 ^ 2) ^ a * A,
    MvPolynomial.X 0 ^ L * (1 - MvPolynomial.X 0) * (1 - MvPolynomial.X 1 ^ 2) ^ a * B,
    MvPolynomial.C (Complex.I / ((n * P.m : ℤ) : ℂ)) *
      (MvPolynomial.X 0 ^ L * (1 - MvPolynomial.X 0) *
          (MvPolynomial.C (((L + 2 : ℕ) : ℂ)) * (1 - MvPolynomial.X 0) - MvPolynomial.X 0) *
          (1 - MvPolynomial.X 1 ^ 2) ^ a * A +
        MvPolynomial.X 0 ^ (L + 1) * (1 - MvPolynomial.X 0) ^ 2 * (1 - MvPolynomial.X 1 ^ 2) ^ a *
          MvPolynomial.pderiv 0 A +
        (MvPolynomial.C 2 - MvPolynomial.C (((2 * P.eps : ℝ)) : ℂ) * MvPolynomial.X 0) *
          MvPolynomial.X 0 ^ L * (1 - MvPolynomial.X 0) * (1 - MvPolynomial.X 1 ^ 2) ^ a * A -
        MvPolynomial.X 0 ^ L * (1 - MvPolynomial.X 0) *
          (MvPolynomial.C (((a + 3 : ℕ) : ℂ)) * (1 - MvPolynomial.X 1 ^ 2) ^ a *
              (-(MvPolynomial.C 2 * MvPolynomial.X 1)) * B +
            (1 - MvPolynomial.X 1 ^ 2) ^ (a + 1) * MvPolynomial.pderiv 1 B))]

private def waveQ2 (P : ChartParams) (n : ℤ) (β : ℝ) (L a : ℕ) (A : MvPolynomial (Fin 2) ℂ) :
    Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![0, 0, MvPolynomial.C (Complex.I / ((n * P.m : ℤ) : ℂ)) * MvPolynomial.C (Complex.I * (((n : ℝ) * β : ℝ) : ℂ)) *
    MvPolynomial.X 0 ^ L * (1 - MvPolynomial.X 0) * (1 - MvPolynomial.X 1 ^ 2) ^ a * A]

private lemma wave_local {P : ChartParams} {D : FieldData} {n : ℤ} (hn0 : n ≠ 0) (β : ℝ) {L a : ℕ}
    (hL : D.lowOrder n = L + 2) (ha : D.axisOrder n = a + 2) (hH : D.highOrder = 1)
    {A B : MvPolynomial (Fin 2) ℂ} {t0 x0 : ℝ}
    (hA : ∀ᶠ p : ℝ × ℝ in nhds (t0, x0),
      (D.amp n).radialAmp.eval false p.1 p.2 = MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] A)
    (hB : ∀ᶠ p : ℝ × ℝ in nhds (t0, x0),
      (D.amp n).polarAmp.eval true p.1 p.2 = MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] B)
    (c : Fin 3) :
    (fun p : ℝ × ℝ => reducedField P D n β p.1 p.2 c) =ᶠ[nhds (t0, x0)] fun p =>
      ((p.1 : ℂ) * (p.1 : ℂ)) * ((((1 - p.2 ^ 2) ^ 2 : ℝ) : ℂ) *
        (MvPolynomial.eval ![(p.1 : ℂ), ((1 * p.2 : ℝ) : ℂ)] (waveQ1 P n L a A B c) +
          (coreRatioT P p.1 : ℂ) * MvPolynomial.eval ![(p.1 : ℂ), ((1 * p.2 : ℝ) : ℂ)] (waveQ2 P n β L a A c))) := by
  have hAeq : ∀ᶠ p : ℝ × ℝ in nhds (t0, x0), radPart D n L a p.1 p.2 =
      weightPoly (L + 2) 1 p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (a + 2) *
        MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] A := by
    filter_upwards [hA] with p hp
    rw [radPart, hp]
  have hBeq : ∀ᶠ p : ℝ × ℝ in nhds (t0, x0), ((1 - p.2 ^ 2 : ℝ) : ℂ) * polPart D n L a p.1 p.2 =
      ((1 - p.2 ^ 2 : ℝ) : ℂ) * (weightPoly (L + 2) 1 p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (a + 2) *
        MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] B) := by
    filter_upwards [hB] with p hp
    rw [polPart, hp]
  have hd1 := slice_deriv_fst (F := radPart D n L a)
    (G := fun t x => weightPoly (L + 2) 1 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ (a + 2) *
        MvPolynomial.eval ![(t : ℂ), (x : ℂ)] A) hAeq
  have hd2 := slice_deriv_snd (F := fun t x => ((1 - x ^ 2 : ℝ) : ℂ) * polPart D n L a t x)
    (G := fun t x => ((1 - x ^ 2 : ℝ) : ℂ) * (weightPoly (L + 2) 1 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ (a + 2) *
        MvPolynomial.eval ![(t : ℂ), (x : ℂ)] B)) hBeq
  fin_cases c
  · filter_upwards [hA] with p hp
    rw [reduced_wave_eq hn0 β hL ha hH]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, radPart, hp, waveQ1, waveQ2, weightPoly]
    simp only [map_mul, map_sub, map_pow, map_one, map_zero, MvPolynomial.eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    push_cast
    ring
  · filter_upwards [hB] with p hp
    rw [reduced_wave_eq hn0 β hL ha hH]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, polPart, hp, waveQ1, waveQ2,
      weightPoly]
    simp only [map_mul, map_sub, map_pow, map_one, map_zero, MvPolynomial.eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    push_cast
    ring
  · filter_upwards [hA, hd1, hd2] with p hp h1 h2
    have e1 : deriv (fun t' => radPart D n L a t' p.2) p.1 =
        (((L + 2 : ℕ) : ℂ) * (p.1 : ℂ) ^ (L + 1) * (1 - (p.1 : ℂ)) - (p.1 : ℂ) ^ (L + 2)) *
            ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (a + 2) * MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] A +
          weightPoly (L + 2) 1 p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (a + 2) *
            MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] (MvPolynomial.pderiv 0 A) := by
      rw [h1]
      exact (((weight_hasDerivAt L p.1).mul_const (((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (a + 2))).mul
        (mvpoly_hasDerivAt_fst A p.1 p.2)).deriv
    have e2 : deriv (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * polPart D n L a p.1 x') p.2 =
        -(2 * (p.2 : ℂ)) * (weightPoly (L + 2) 1 p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (a + 2) *
            MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] B) +
          ((1 - p.2 ^ 2 : ℝ) : ℂ) * ((0 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (a + 2) + weightPoly (L + 2) 1 p.1 *
              (((a + 2 : ℕ) : ℂ) * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (a + 2 - 1) * (-(2 * (p.2 : ℂ))))) *
              MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] B +
            weightPoly (L + 2) 1 p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ (a + 2) *
              MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] (MvPolynomial.pderiv 1 B)) := by
      rw [h2]
      exact ((axis_hasDerivAt p.2).mul ((((hasDerivAt_const p.2 (weightPoly (L + 2) 1 p.1)).mul
        ((axis_hasDerivAt p.2).fun_pow (a + 2))).mul (mvpoly_hasDerivAt_snd B p.1 p.2)))).deriv
    rw [reduced_wave_eq hn0 β hL ha hH]
    simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      twistedScale, radialScale, heightDeriv, e1, e2]
    simp only [radPart, hp, waveQ1, waveQ2, weightPoly, Nat.add_sub_cancel]
    simp only [map_mul, map_sub, map_add, map_neg, map_pow, map_one, map_zero, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    push_cast
    ring

private lemma pair_tendsto {P : ChartParams} (hP : IsChartParams P) {z : Space} (hz : z ≠ 0) :
    Filter.Tendsto (fun y => (chartT P y, heightRatio y)) (nhds z) (nhds (chartT P z, heightRatio z)) := by
  have hL := hP.L0_pos
  have h1 : ContinuousAt (chartT P) z := by
    unfold chartT
    exact continuous_norm.continuousAt.div (continuous_norm.add continuous_const).continuousAt
      (by positivity)
  have h2 : ContinuousAt heightRatio z :=
    heightRatio_contDiffOn.continuousOn.continuousAt (isOpen_ne.mem_nhds hz)
  exact (h1.prodMk h2).tendsto

private lemma cellIndex_lt_count {l : List ℝ} (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) (u : ℝ) :
    cellIndex l u < cellCount l := by
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at h0
  · simp at h0 h1
    linarith
  · unfold cellIndex cellCount
    have h := List.length_filter_le (fun b => decide (b ≤ u)) (((a :: b :: rest).drop 1).dropLast)
    simp only [List.length_dropLast, List.length_drop, List.length_cons] at h ⊢
    omega

private lemma first_split (p : MvPolynomial (Fin 2) ℂ) :
    ∃ R : MvPolynomial (Fin 2) ℂ, p = atFirst 0 p + MvPolynomial.X 0 * R := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp [atFirst]⟩
  | add p q hp hq =>
    obtain ⟨R1, h1⟩ := hp
    obtain ⟨R2, h2⟩ := hq
    refine ⟨R1 + R2, ?_⟩
    have hm : atFirst 0 (p + q) = atFirst 0 p + atFirst 0 q := map_add _ _ _
    rw [hm]
    linear_combination h1 + h2
  | mul_X p i hp =>
    obtain ⟨R, h⟩ := hp
    fin_cases i
    · refine ⟨p, ?_⟩
      have hm : atFirst 0 (p * MvPolynomial.X 0) = 0 := by simp [atFirst]
      show p * MvPolynomial.X 0 = atFirst 0 (p * MvPolynomial.X 0) + MvPolynomial.X 0 * p
      rw [hm]
      ring
    · refine ⟨R * MvPolynomial.X 1, ?_⟩
      have hm : atFirst 0 (p * MvPolynomial.X 1) = atFirst 0 p * MvPolynomial.X 1 := by simp [atFirst]
      show p * MvPolynomial.X 1 = atFirst 0 (p * MvPolynomial.X 1) + MvPolynomial.X 0 * (R * MvPolynomial.X 1)
      rw [hm]
      linear_combination MvPolynomial.X 1 * h

private lemma weight_one_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t' : ℝ => weightPoly 1 1 t') (1 - 2 * (t : ℂ)) t := by
  have h := ((hasDerivAt_id' t).mul ((hasDerivAt_id' t).const_sub 1)).ofReal_comp
  convert h using 1
  · funext y
    simp [weightPoly]
  · push_cast
    ring

private lemma reduced_mean_eq {P : ChartParams} {D : FieldData} (β : ℝ) (hH : D.highOrder = 1) (t x : ℝ) :
    reducedField P D 0 β t x =
      ![-(weightPoly 1 1 t * heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) *
          (D.amp 0).streamAmp.eval true t' x') t x),
        -(twistedScale P 0 β (fun t' x' => weightPoly 1 1 t' * (D.amp 0).streamAmp.eval true t' x') t x +
          2 * (weightPoly 1 1 t * (D.amp 0).streamAmp.eval true t x)),
        weightPoly 1 1 t * (D.amp 0).swirlAmp.eval false t x] := by
  simp only [reducedField, ↓reduceIte, hH]

private def meanQ (P : ChartParams) (A B : MvPolynomial (Fin 2) ℂ) : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![-(MvPolynomial.X 0 * (1 - MvPolynomial.X 0) * (-(MvPolynomial.C 2 * MvPolynomial.X 1) * A +
      (1 - MvPolynomial.X 1 ^ 2) * MvPolynomial.pderiv 1 A)),
    -(MvPolynomial.X 0 * (1 - MvPolynomial.X 0) * ((1 - MvPolynomial.C 2 * MvPolynomial.X 0) * A +
        MvPolynomial.X 0 * (1 - MvPolynomial.X 0) * MvPolynomial.pderiv 0 A) -
      MvPolynomial.C (((2 * P.eps : ℝ)) : ℂ) * MvPolynomial.X 0 * (MvPolynomial.X 0 * (1 - MvPolynomial.X 0) * A) +
      MvPolynomial.C 2 * (MvPolynomial.X 0 * (1 - MvPolynomial.X 0) * A)),
    MvPolynomial.X 0 * (1 - MvPolynomial.X 0) * B]

private lemma mean_local {P : ChartParams} {D : FieldData} (β : ℝ) (hH : D.highOrder = 1)
    {A B : MvPolynomial (Fin 2) ℂ} {t0 x0 : ℝ}
    (hA : ∀ᶠ p : ℝ × ℝ in nhds (t0, x0),
      (D.amp 0).streamAmp.eval true p.1 p.2 = MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] A)
    (hB : ∀ᶠ p : ℝ × ℝ in nhds (t0, x0),
      (D.amp 0).swirlAmp.eval false p.1 p.2 = MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] B)
    (c : Fin 3) :
    (fun p : ℝ × ℝ => reducedField P D 0 β p.1 p.2 c) =ᶠ[nhds (t0, x0)] fun p =>
      MvPolynomial.eval ![(p.1 : ℂ), ((1 * p.2 : ℝ) : ℂ)] (meanQ P A B c) := by
  have hd1 := slice_deriv_fst (F := fun t x => weightPoly 1 1 t * (D.amp 0).streamAmp.eval true t x)
    (G := fun t x => weightPoly 1 1 t * MvPolynomial.eval ![(t : ℂ), (x : ℂ)] A)
    (by filter_upwards [hA] with p hp; rw [hp])
  have hd2 := slice_deriv_snd (F := fun t x => ((1 - x ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t x)
    (G := fun t x => ((1 - x ^ 2 : ℝ) : ℂ) * MvPolynomial.eval ![(t : ℂ), (x : ℂ)] A)
    (by filter_upwards [hA] with p hp; rw [hp])
  fin_cases c
  · filter_upwards [hA, hd2] with p hp h2
    have e2 : deriv (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true p.1 x') p.2 =
        -(2 * (p.2 : ℂ)) * MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] A +
          ((1 - p.2 ^ 2 : ℝ) : ℂ) * MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] (MvPolynomial.pderiv 1 A) := by
      rw [h2]
      exact ((axis_hasDerivAt p.2).mul (mvpoly_hasDerivAt_snd A p.1 p.2)).deriv
    rw [reduced_mean_eq β hH]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, heightDeriv, e2, meanQ, weightPoly]
    simp only [map_mul, map_sub, map_add, map_neg, map_pow, map_one, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    push_cast
    ring
  · filter_upwards [hA, hd1] with p hp h1
    have e1 : deriv (fun t' => weightPoly 1 1 t' * (D.amp 0).streamAmp.eval true t' p.2) p.1 =
        (1 - 2 * (p.1 : ℂ)) * MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] A +
          weightPoly 1 1 p.1 * MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] (MvPolynomial.pderiv 0 A) := by
      rw [h1]
      exact ((weight_one_hasDerivAt p.1).mul (mvpoly_hasDerivAt_fst A p.1 p.2)).deriv
    rw [reduced_mean_eq β hH]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, twistedScale, radialScale]
    rw [e1]
    simp only [hp, meanQ, weightPoly]
    simp only [map_mul, map_sub, map_add, map_neg, map_pow, map_one, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    push_cast
    ring
  · filter_upwards [hB] with p hp
    rw [reduced_mean_eq β hH]
    simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hp,
      meanQ, weightPoly]
    simp only [map_mul, map_sub, map_one, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    push_cast
    ring

private lemma exists_break_le (l : List ℝ) (u : ℝ) (h : cellIndex l u ≠ 0) :
    ∃ b ∈ (l.drop 1).dropLast, b ≤ u := by
  unfold cellIndex at h
  obtain ⟨b, hb⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero h)
  rw [List.mem_filter] at hb
  exact ⟨b, hb.1, by simpa using hb.2⟩

private lemma locPoly_odd_split (S : Spline) (b : Bool) (i j : ℕ) (g : ℂ) (R : MvPolynomial (Fin 2) ℂ)
    (h : S.piece i j = MvPolynomial.C g * MvPolynomial.X 1 + MvPolynomial.X 0 * R) :
    locPoly S true b i j = MvPolynomial.C g * MvPolynomial.X 1 +
      MvPolynomial.X 0 * (MvPolynomial.C (if b then -1 else 1) * flipPoly (if b then -1 else 1) R) := by
  unfold locPoly flipPoly
  rw [h]
  cases b <;> simp <;> ring

private lemma locPoly_even_split (S : Spline) (b : Bool) (i j : ℕ) (g : ℂ) (R : MvPolynomial (Fin 2) ℂ)
    (h : S.piece i j = MvPolynomial.C g + MvPolynomial.X 0 * R) :
    locPoly S false b i j = MvPolynomial.C g + MvPolynomial.X 0 * flipPoly (if b then -1 else 1) R := by
  unfold locPoly flipPoly
  rw [h]
  cases b <;> simp

private def meanGuardX (g w : ℝ) (c : Fin 3) (x : ℝ) : ℝ :=
  ![-(g * (1 - 3 * x ^ 2)), -(3 * g * x), w] c

private def meanQA (P : ChartParams) (g w : ℂ) (Ra Rb : MvPolynomial (Fin 2) ℂ) :
    Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.C g * (1 - MvPolynomial.C 3 * MvPolynomial.X 1 ^ 2) -
      (1 - MvPolynomial.X 0) * (-(MvPolynomial.C 2 * MvPolynomial.X 1) * Ra +
        (1 - MvPolynomial.X 1 ^ 2) * MvPolynomial.pderiv 1 Ra),
    -((MvPolynomial.C (-3) + MvPolynomial.C 2 * MvPolynomial.X 0) * MvPolynomial.C g * MvPolynomial.X 1 +
      (1 - MvPolynomial.X 0) * (1 - MvPolynomial.C 2 * MvPolynomial.X 0) * Ra +
      (1 - MvPolynomial.X 0) ^ 2 * (Ra + MvPolynomial.X 0 * MvPolynomial.pderiv 0 Ra) -
      MvPolynomial.C (((2 * P.eps : ℝ)) : ℂ) * (1 - MvPolynomial.X 0) *
        (MvPolynomial.C g * MvPolynomial.X 1 + MvPolynomial.X 0 * Ra) -
      MvPolynomial.C 2 * MvPolynomial.C g * MvPolynomial.X 1 + MvPolynomial.C 2 * (1 - MvPolynomial.X 0) * Ra),
    (1 - MvPolynomial.X 0) * Rb - MvPolynomial.C w]

private lemma meanQ_split (P : ChartParams) {g w : ℝ} {A B Ra Rb : MvPolynomial (Fin 2) ℂ}
    (hA : A = MvPolynomial.C (g : ℂ) * MvPolynomial.X 1 + MvPolynomial.X 0 * Ra)
    (hB : B = MvPolynomial.C (w : ℂ) + MvPolynomial.X 0 * Rb) (c : Fin 3) (t x : ℝ) :
    MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (meanQ P A B c) =
      (t : ℂ) * (meanGuardX g w c x : ℂ) +
        (t : ℂ) * (t : ℂ) * MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (meanQA P g w Ra Rb c) := by
  subst hA hB
  fin_cases c <;>
    simp [meanQ, meanQA, meanGuardX, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply] <;>
    push_cast <;> ring

theorem wave_freeze {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) {n : ℤ} (hn : n ∈ D.modes) (hn0 : n ≠ 0) :
    ∃ Qs : Finset (MvPolynomial (Fin 2) ℂ), ∀ z : Space, z ≠ 0 →
      (∀ R ∈ breakRadii P D, ‖z‖ ≠ R) → (∀ c ∈ breakCones D, z 2 ≠ c * ‖z‖) →
        ∀ c : Fin 3, ∃ Q1 ∈ Qs, ∃ Q2 ∈ Qs,
          (fun y => reducedField P D n β (chartT P y) (heightRatio y) c) =ᶠ[nhds z]
            fun y => ((chartT P y : ℂ) * (chartT P y : ℂ)) * (((qOf y ^ 2 : ℝ) : ℂ) *
              (MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q1 +
                (coreRatioT P (chartT P y) : ℂ) *
                  MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q2)) := by
  obtain ⟨L, hL⟩ : ∃ L, D.lowOrder n = L + 2 :=
    ⟨D.lowOrder n - 2, by have := hD.lowOrder_ge n hn hn0; omega⟩
  obtain ⟨a, ha⟩ : ∃ a, D.axisOrder n = a + 2 :=
    ⟨D.axisOrder n - 2, by have := hD.axisOrder_ge n hn hn0; omega⟩
  have hH := hD.highOrder_eq
  set SR := (D.amp n).radialAmp with hSR
  set SP := (D.amp n).polarAmp with hSP
  have hMR := (hD.waveRadial n hn hn0).mesh
  have hMP := (hD.wavePolar n hn hn0).mesh
  let idx : Finset (Bool × ℕ × ℕ × ℕ × ℕ × Fin 3) := Finset.univ ×ˢ Finset.range (SR.mesh.tBreaks.length + 1) ×ˢ
    Finset.range (SR.mesh.xBreaks.length + 1) ×ˢ Finset.range (SP.mesh.tBreaks.length + 1) ×ˢ
    Finset.range (SP.mesh.xBreaks.length + 1) ×ˢ Finset.univ
  let f1 : Bool × ℕ × ℕ × ℕ × ℕ × Fin 3 → MvPolynomial (Fin 2) ℂ := fun q =>
    waveQ1 P n L a (locPoly SR false q.1 q.2.1 q.2.2.1) (locPoly SP true q.1 q.2.2.2.1 q.2.2.2.2.1) q.2.2.2.2.2
  let f2 : Bool × ℕ × ℕ × ℕ × ℕ × Fin 3 → MvPolynomial (Fin 2) ℂ := fun q =>
    waveQ2 P n β L a (locPoly SR false q.1 q.2.1 q.2.2.1) q.2.2.2.2.2
  refine ⟨idx.image f1 ∪ idx.image f2, ?_⟩
  intro z hz hR hc c
  obtain ⟨htR, hx0, hxR⟩ := good_point hP hn (S := SR) (by simp [splinesOf, SR]) hz hR hc
  obtain ⟨htP, -, hxP⟩ := good_point hP hn (S := SP) (by simp [splinesOf, SP]) hz hR hc
  have hA := spline_local SR false hx0 htR (hxR hMR)
  have hB := spline_local SP true hx0 htP (hxP hMP)
  have hloc := wave_local (P := P) hn0 β hL ha hH hA hB c
  have hq : (decide (heightRatio z < 0), cellIndex SR.mesh.tBreaks (chartT P z),
      cellIndex SR.mesh.xBreaks |heightRatio z|, cellIndex SP.mesh.tBreaks (chartT P z),
      cellIndex SP.mesh.xBreaks |heightRatio z|, c) ∈ idx := by
    simp only [idx, Finset.mem_product, Finset.mem_univ, Finset.mem_range, cellIndex_le, and_self]
  refine ⟨_, Finset.mem_union_left _ (Finset.mem_image_of_mem f1 hq), _,
    Finset.mem_union_right _ (Finset.mem_image_of_mem f2 hq), ?_⟩
  filter_upwards [(pair_tendsto hP hz).eventually hloc] with y hy
  exact hy

theorem waveTerm_third_bound {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) {n : ℤ} (hn : n ∈ D.modes) (hn0 : n ≠ 0) :
    ∃ (K : ℝ) (Rs cs : Finset ℝ), 0 ≤ K ∧ (∀ c ∈ cs, |c| < 1) ∧
      ∀ z : Space, z ≠ 0 → (∀ R ∈ Rs, ‖z‖ ≠ R) → (∀ c ∈ cs, z 2 ≠ c * ‖z‖) →
        ContDiffAt ℝ 3 (modeTerm P D β n) z ∧
        ‖iteratedFDeriv ℝ 3 (modeTerm P D β n) z‖ ≤ K * ‖z‖⁻¹ := by
  obtain ⟨Qs, hQ⟩ := wave_freeze hP hD β hn hn0
  have hK := fun q : MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ × Fin 3 × Fin 3 =>
    waveModel_third hP (n * (P.m : ℤ)) (n * β) q.1 q.2.1 q.2.2.1 q.2.2.2
  choose K hK0 hKb using hK
  set S := Qs ×ˢ Qs ×ˢ (Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3)) with hS
  have hKS : ∀ q ∈ S, K q ≤ ∑ q ∈ S, K q := fun q hq =>
    Finset.single_le_sum (f := K) (fun q _ => hK0 q) hq
  have hsum0 : 0 ≤ ∑ q ∈ S, K q := Finset.sum_nonneg (fun q _ => hK0 q)
  refine ⟨3 * (3 * ∑ q ∈ S, K q), breakRadii P D, breakCones D, by positivity,
    breakCones_abs_lt D, ?_⟩
  intro z hz hR hc
  have hQz := hQ z hz hR hc
  choose Q1 hQ1 Q2 hQ2 hEq using hQz
  let G : Fin 3 → Space → ℂ := fun i y => (decayFactor P y : ℂ) * (modePhase P n β y *
    (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
      reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
      reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))
  have hmt : modeTerm P D β n = fun y => ofComponents (fun i => (G i y).re) := rfl
  have hloc : ∀ i : Fin 3, G i =ᶠ[nhds z]
      fun y => ∑ c : Fin 3, waveModel P (n * (P.m : ℤ)) (n * β) (Q1 c) (Q2 c) c i y := by
    intro i
    filter_upwards [hEq 0, hEq 1, hEq 2] with y h0 h1 h2
    simp only [G, waveModel, Fin.sum_univ_three, vecOf, modePhase_split, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [h0, h1, h2]
    ring
  have hmem : ∀ c i : Fin 3, (Q1 c, Q2 c, c, i) ∈ S := by
    intro c i
    simp only [hS, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hQ1 c, hQ2 c⟩
  have hcd : ∀ c i : Fin 3,
      ContDiffAt ℝ 3 (waveModel P (n * (P.m : ℤ)) (n * β) (Q1 c) (Q2 c) c i) z :=
    fun c i => (hKb (Q1 c, Q2 c, c, i) z hz).1
  have hcomp : ∀ i : Fin 3, ContDiffAt ℝ 3 (G i) z ∧
      ‖iteratedFDeriv ℝ 3 (G i) z‖ ≤ 3 * ∑ q ∈ S, K q * ‖z‖⁻¹ := by
    intro i
    have hsumcd : ContDiffAt ℝ 3
        (fun y => ∑ c : Fin 3, waveModel P (n * (P.m : ℤ)) (n * β) (Q1 c) (Q2 c) c i y) z :=
      ContDiffAt.sum (fun c _ => hcd c i)
    refine ⟨hsumcd.congr_of_eventuallyEq (hloc i), ?_⟩
    rw [((hloc i).iteratedFDeriv ℝ 3).eq_of_nhds,
      iteratedFDeriv_fun_sum_apply (fun c _ => hcd c i)]
    have hz0 : 0 ≤ ‖z‖⁻¹ := by positivity
    calc ‖∑ c : Fin 3, iteratedFDeriv ℝ 3 (waveModel P (n * (P.m : ℤ)) (n * β) (Q1 c) (Q2 c) c i) z‖
        ≤ ∑ c : Fin 3, ‖iteratedFDeriv ℝ 3 (waveModel P (n * (P.m : ℤ)) (n * β) (Q1 c) (Q2 c) c i) z‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _c : Fin 3, (∑ q ∈ S, K q) * ‖z‖⁻¹ := by
          apply Finset.sum_le_sum
          intro c _
          refine ((hKb (Q1 c, Q2 c, c, i) z hz).2).trans ?_
          gcongr
          exact hKS _ (hmem c i)
      _ = 3 * ∑ q ∈ S, K q * ‖z‖⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_mul]
          simp
  rw [hmt]
  obtain ⟨h1, h2⟩ := components_third (g := G) (fun i => (hcomp i).1) (fun i => (hcomp i).2)
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [← Finset.sum_mul]
  ring

def meanLin (D : FieldData) (i : Fin 3) : Space →L[ℝ] ℝ :=
  ![(-D.guardStream) • EuclideanSpace.proj (0 : Fin 3) + (-D.guardSwirl) • EuclideanSpace.proj (1 : Fin 3),
    D.guardSwirl • EuclideanSpace.proj (0 : Fin 3) + (-D.guardStream) • EuclideanSpace.proj (1 : Fin 3),
    (2 * D.guardStream) • EuclideanSpace.proj (2 : Fin 3)] i

def meanGuard (D : FieldData) (c : Fin 3) (y : Space) : ℝ :=
  ![-(D.guardStream * (1 - 3 * heightRatio y ^ 2)), -(3 * D.guardStream * heightRatio y), D.guardSwirl] c

theorem meanGuard_sum {P : ChartParams} (hP : IsChartParams P) (D : FieldData) {y : Space} (hy : y ≠ 0)
    (i : Fin 3) :
    chartT P y * ∑ c : Fin 3, meanGuard D c y * vecOf c y i = meanLin D i y / (‖y‖ + P.L0) := by
  have hs : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hL := hP.L0_pos
  have hpos : 0 < ‖y‖ + P.L0 := by positivity
  fin_cases i <;>
    simp [meanGuard, meanLin, vecOf, Fin.sum_univ_three, chartT, radialVec, polarVecQ, azimVecQ, qOf,
      heightRatio] <;>
    field_simp <;>
    ring

theorem decayS_symbol {P : ChartParams} (hP : IsChartParams P) :
    SymbolW {y : Space | y ≠ 0} (fun s => |s|)
      (fun y => ((decayFactor P y * chartS P y - 1 : ℝ) : ℂ)) := by
  have hL := hP.L0_pos
  have he := hP.eps_pos
  have he2 := hP.eps_lt
  set b := 2 * P.eps + 1 with hbdef
  have hb0 : 0 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hb2 : b ≤ 2 := by linarith
  let g : ℝ → ℝ := fun r => P.L0 ^ b * (r + P.L0) ^ (-b)
  have hfun : (fun y : Space => ((decayFactor P y * chartS P y - 1 : ℝ) : ℂ)) =
      fun y => ((g ‖y‖ : ℝ) : ℂ) + (-1 : ℂ) := by
    funext y
    have hpos : 0 < chartS P y := by
      rw [chartS_eq hP]
      positivity
    have h1 : decayFactor P y * chartS P y = chartS P y ^ b := by
      simp only [decayFactor, hbdef]
      rw [Real.rpow_add_one hpos.ne']
    rw [h1, chartS_rpow hP]
    simp only [g]
    push_cast
    ring
  rw [hfun]
  have hcd : ∀ s : ℝ, 0 < s → ContDiffAt ℝ 3 (fun r : ℝ => ((g r : ℝ) : ℂ)) s := fun s hs =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp s (shiftedPow_contDiffAt (b := b) hL hs)
  refine SymbolW.of_radial (h := fun r => ((g r : ℝ) : ℂ) + (-1 : ℂ)) (wt := fun s => |s|)
    (fun s => abs_nonneg s) ?_ ⟨26 * P.L0⁻¹, by positivity, ?_⟩
  · intro s hs
    exact ((hcd s hs).add contDiffAt_const).contDiffWithinAt
  · intro s hs i hi
    have hpos : 0 < s + P.L0 := by linarith
    rw [abs_of_pos hs]
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [norm_iteratedFDeriv_zero]
      have hgs : g s = (P.L0 / (s + P.L0)) ^ b := by
        simp only [g]
        rw [Real.div_rpow hL.le hpos.le, Real.rpow_neg hpos.le, div_eq_mul_inv]
      have hle1 : g s ≤ 1 := by
        rw [hgs]
        exact Real.rpow_le_one (by positivity) ((div_le_one hpos).mpr (by linarith)) hb0
      have hx : (-1 : ℝ) ≤ -(s / (s + P.L0)) := by
        rw [neg_le_neg_iff, div_le_one hpos]
        linarith
      have hbern := one_add_mul_self_le_rpow_one_add hx hb1
      have h1x : 1 + -(s / (s + P.L0)) = P.L0 / (s + P.L0) := by
        field_simp
        ring
      rw [h1x, ← hgs] at hbern
      have hq : s / (s + P.L0) ≤ s / P.L0 := by
        apply div_le_div_of_nonneg_left hs.le hL
        linarith
      have heq : ((g s : ℝ) : ℂ) + -1 = ((g s - 1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      have h2 : b * (s / P.L0) ≤ 2 * (s / P.L0) := by
        apply mul_le_mul_of_nonneg_right hb2
        positivity
      have h3 : 2 * (s / P.L0) ≤ 26 * P.L0⁻¹ * s * s⁻¹ ^ 0 := by
        rw [pow_zero, mul_one, div_eq_mul_inv]
        have : 0 ≤ P.L0⁻¹ * s := by positivity
        nlinarith
      nlinarith
    · rw [fun_iteratedFDeriv_add_apply ((hcd s hs).of_le (by exact_mod_cast hi)) contDiffAt_const,
        iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hi1), Pi.zero_apply, add_zero]
      refine (ofReal_iteratedFDeriv_le ((shiftedPow_contDiffAt (b := b) hL hs).of_le
        (by exact_mod_cast hi))).trans ?_
      rw [shiftedPow_iteratedDeriv, Real.norm_eq_abs]
      have hp := fallingProduct_small hb0 hb2 hi
      have hw := shiftedPow_le hL hs hb0 i
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hsi : ((s + P.L0) ^ (k + 1))⁻¹ ≤ P.L0⁻¹ * s * s⁻¹ ^ (k + 1) := by
        have e1 : ((s + P.L0) ^ (k + 1))⁻¹ = ((s + P.L0) ^ k)⁻¹ * (s + P.L0)⁻¹ := by
          rw [pow_succ, mul_inv]
        have e2 : P.L0⁻¹ * s * s⁻¹ ^ (k + 1) = s⁻¹ ^ k * P.L0⁻¹ := by
          rw [pow_succ]
          field_simp
        rw [e1, e2]
        have f1 : ((s + P.L0) ^ k)⁻¹ ≤ s⁻¹ ^ k := by
          rw [← inv_pow]
          gcongr
          linarith
        have f2 : (s + P.L0)⁻¹ ≤ P.L0⁻¹ := by
          gcongr
          linarith
        gcongr
      have hw0 : 0 ≤ P.L0 ^ b * (s + P.L0) ^ (-b - ((k + 1 : ℕ) : ℝ)) := by positivity
      calc |P.L0 ^ b * ((descPochhammer ℝ (k + 1)).eval (-b) * (s + P.L0) ^ (-b - ((k + 1 : ℕ) : ℝ)))|
          = |(descPochhammer ℝ (k + 1)).eval (-b)| *
              (P.L0 ^ b * (s + P.L0) ^ (-b - ((k + 1 : ℕ) : ℝ))) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hL.le _),
              abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
            ring
        _ ≤ 24 * (P.L0⁻¹ * s * s⁻¹ ^ (k + 1)) :=
            mul_le_mul hp (hw.trans hsi) hw0 (by norm_num)
        _ ≤ 26 * P.L0⁻¹ * s * s⁻¹ ^ (k + 1) := by
            have : 0 ≤ P.L0⁻¹ * s * s⁻¹ ^ (k + 1) := by positivity
            nlinarith

theorem meanLin_symbol (D : FieldData) (i : Fin 3) (a : ℝ) :
    SymbolW {y : Space | y ≠ 0} (fun s => |s| * 1) (fun y => ((meanLin D i y * a : ℝ) : ℂ)) := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have hh : SymbolW {y : Space | y ≠ 0} (fun _ => 1) (fun y => ((meanLin D i y * a / ‖y‖ : ℝ) : ℂ)) := by
    refine SymbolW.of_homogeneous_real (subset_refl _) ?_ ?_
    · intro y hy
      have hy0 : y ≠ 0 := hy
      have h1 : ContDiffAt ℝ 3 (fun y : Space => meanLin D i y * a) y :=
        ((meanLin D i).contDiff.mul contDiff_const).contDiffAt
      exact (h1.div (contDiffAt_norm ℝ hy0) (norm_ne_zero_iff.mpr hy0)).contDiffWithinAt
    · intro y c hc
      rw [map_smul, norm_smul, Real.norm_of_nonneg hc.le, smul_eq_mul]
      field_simp
  have hm := SymbolW.mul hU (fun s => abs_nonneg s) (fun _ => zero_le_one) norm_symbol hh
  refine ⟨?_, ?_⟩
  · intro y hy
    have hy0 : y ≠ 0 := hy
    exact (Complex.ofRealCLM.contDiff.comp ((meanLin D i).contDiff.mul contDiff_const)).contDiffWithinAt
  · obtain ⟨_, C, hC, hb⟩ := hm
    refine ⟨C, hC, fun y hy j hj => ?_⟩
    have hy0 : y ≠ 0 := hy
    have heq : (fun y : Space => ((meanLin D i y * a : ℝ) : ℂ)) =ᶠ[nhds y]
        fun y => ((‖y‖ : ℝ) : ℂ) * ((meanLin D i y * a / ‖y‖ : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hy] with v hv
      have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
    exact hb y hy j hj

theorem linear_third_zero (L : Space →L[ℝ] ℝ) (a : ℝ) (z : Space) :
    iteratedFDeriv ℝ 3 (fun y => ((L y * a : ℝ) : ℂ)) z = 0 := by
  let e : Space →L[ℝ] ℂ := Complex.ofRealCLM.comp (a • L)
  have hfe : (fun y => ((L y * a : ℝ) : ℂ)) = ⇑e := by
    funext y
    simp [e, mul_comm]
  rw [hfe]
  have hf : fderiv ℝ (⇑e) = fun _ => e := funext (fun x => e.fderiv)
  have h : ‖iteratedFDeriv ℝ 3 (⇑e) z‖ = 0 := by
    have h3 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := ⇑e) (x := z) (n := 2)
    rw [hf, iteratedFDeriv_const_of_ne (by norm_num)] at h3
    simpa using h3.symm
  exact norm_eq_zero.mp h

theorem mean_freeze {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) (h0 : (0 : ℤ) ∈ D.modes) :
    ∃ (Qs : Finset (MvPolynomial (Fin 2) ℂ)) (b₀ : ℝ), 0 < b₀ ∧ ∀ z : Space, z ≠ 0 →
      (∀ R ∈ breakRadii P D, ‖z‖ ≠ R) → (∀ c ∈ breakCones D, z 2 ≠ c * ‖z‖) →
        (∀ c : Fin 3, ∃ Q ∈ Qs,
          (fun y => reducedField P D 0 β (chartT P y) (heightRatio y) c) =ᶠ[nhds z]
            fun y => (chartT P y : ℂ) * (meanGuard D c y : ℂ) +
              (chartT P y : ℂ) * (chartT P y : ℂ) *
                MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q) ∨
        (b₀ ≤ chartT P z ∧ ∀ c : Fin 3, ∃ Q ∈ Qs,
          (fun y => reducedField P D 0 β (chartT P y) (heightRatio y) c) =ᶠ[nhds z]
            fun y => MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q) := by
  have hH := hD.highOrder_eq
  set SS := (D.amp 0).streamAmp with hSS
  set SW := (D.amp 0).swirlAmp with hSW
  have hMS := (hD.meanStream h0).1.mesh
  have hMW := (hD.meanSwirl h0).1.mesh
  choose Rof hRof using first_split
  let raS : Bool → ℕ → MvPolynomial (Fin 2) ℂ := fun b j =>
    MvPolynomial.C (if b then -1 else 1) * flipPoly (if b then -1 else 1) (Rof (SS.piece 0 j))
  let rbW : Bool → ℕ → MvPolynomial (Fin 2) ℂ := fun b j => flipPoly (if b then -1 else 1) (Rof (SW.piece 0 j))
  let idx : Finset (Bool × ℕ × ℕ × ℕ × ℕ × Fin 3) := Finset.univ ×ˢ Finset.range (SS.mesh.tBreaks.length + 1) ×ˢ
    Finset.range (SS.mesh.xBreaks.length + 1) ×ˢ Finset.range (SW.mesh.tBreaks.length + 1) ×ˢ
    Finset.range (SW.mesh.xBreaks.length + 1) ×ˢ Finset.univ
  let fB : Bool × ℕ × ℕ × ℕ × ℕ × Fin 3 → MvPolynomial (Fin 2) ℂ := fun q =>
    meanQ P (locPoly SS true q.1 q.2.1 q.2.2.1) (locPoly SW false q.1 q.2.2.2.1 q.2.2.2.2.1) q.2.2.2.2.2
  let fA : Bool × ℕ × ℕ × ℕ × ℕ × Fin 3 → MvPolynomial (Fin 2) ℂ := fun q =>
    meanQA P D.guardStream D.guardSwirl (raS q.1 q.2.2.1) (rbW q.1 q.2.2.2.2.1) q.2.2.2.2.2
  let Is : Finset ℝ := ((SS.mesh.tBreaks.drop 1).dropLast ++ (SW.mesh.tBreaks.drop 1).dropLast).toFinset
  have hne : (insert 1 Is).Nonempty := Finset.insert_nonempty _ _
  refine ⟨idx.image fB ∪ idx.image fA, (insert 1 Is).min' hne, ?_, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact one_pos
    · rcases List.mem_append.mp (List.mem_toFinset.mp hy) with hy | hy
      · exact (interior_bounds hMS.t_sorted hMS.t_first hMS.t_last hy).1
      · exact (interior_bounds hMW.t_sorted hMW.t_first hMW.t_last hy).1
  intro z hz hR hc
  obtain ⟨htS, hx0, hxS⟩ := good_point hP h0 (S := SS) (by simp [splinesOf, SS]) hz hR hc
  obtain ⟨htW, -, hxW⟩ := good_point hP h0 (S := SW) (by simp [splinesOf, SW]) hz hR hc
  have hA := spline_local SS true hx0 htS (hxS hMS)
  have hB := spline_local SW false hx0 htW (hxW hMW)
  have hloc := fun c => mean_local (P := P) β hH hA hB c
  have hq : ∀ c, (decide (heightRatio z < 0), cellIndex SS.mesh.tBreaks (chartT P z),
      cellIndex SS.mesh.xBreaks |heightRatio z|, cellIndex SW.mesh.tBreaks (chartT P z),
      cellIndex SW.mesh.xBreaks |heightRatio z|, c) ∈ idx := by
    intro c
    simp only [idx, Finset.mem_product, Finset.mem_univ, Finset.mem_range, cellIndex_le, and_self]
  by_cases hcell : cellIndex SS.mesh.tBreaks (chartT P z) = 0 ∧ cellIndex SW.mesh.tBreaks (chartT P z) = 0
  · left
    intro c
    refine ⟨_, Finset.mem_union_right _ (Finset.mem_image_of_mem fA (hq c)), ?_⟩
    have hjS := cellIndex_lt_count hMS.x_first hMS.x_last |heightRatio z|
    have hjW := cellIndex_lt_count hMW.x_first hMW.x_last |heightRatio z|
    have hgS := (hD.guard_stream h0) _ hjS
    have hgW := (hD.guard_swirl h0) _ hjW
    have hpS := hRof (SS.piece 0 (cellIndex SS.mesh.xBreaks |heightRatio z|))
    have hpW := hRof (SW.piece 0 (cellIndex SW.mesh.xBreaks |heightRatio z|))
    rw [hgS] at hpS
    rw [hgW] at hpW
    have hAs := locPoly_odd_split SS (decide (heightRatio z < 0)) 0 _ _ _ hpS
    have hBs := locPoly_even_split SW (decide (heightRatio z < 0)) 0 _ _ _ hpW
    rw [hcell.1] at hA
    filter_upwards [(pair_tendsto hP hz).eventually (hloc c)] with y hy
    simp only [hcell.1, hcell.2] at hy
    rw [hy, meanQ_split P hAs hBs c]
    simp only [one_mul]
    rfl
  · right
    have hlt : (insert 1 Is).min' hne ≤ chartT P z := by
      rcases not_and_or.mp hcell with h | h
      · obtain ⟨b, hb, hbz⟩ := exists_break_le _ _ h
        exact (Finset.min'_le _ b (Finset.mem_insert_of_mem
          (List.mem_toFinset.mpr (List.mem_append_left _ hb)))).trans hbz
      · obtain ⟨b, hb, hbz⟩ := exists_break_le _ _ h
        exact (Finset.min'_le _ b (Finset.mem_insert_of_mem
          (List.mem_toFinset.mpr (List.mem_append_right _ hb)))).trans hbz
    refine ⟨hlt, fun c => ⟨_, Finset.mem_union_left _ (Finset.mem_image_of_mem fB (hq c)), ?_⟩⟩
    filter_upwards [(pair_tendsto hP hz).eventually (hloc c)] with y hy
    exact hy

def meanNear (P : ChartParams) (Q : MvPolynomial (Fin 2) ℂ) (c i : Fin 3) (y : Space) : ℂ :=
  (decayFactor P y : ℂ) * (((chartT P y : ℂ) * (chartT P y : ℂ)) *
    (MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q * ((vecOf c y i : ℝ) : ℂ)))

def meanFar (P : ChartParams) (Q : MvPolynomial (Fin 2) ℂ) (c i : Fin 3) (y : Space) : ℂ :=
  (decayFactor P y : ℂ) *
    (MvPolynomial.eval ![(chartT P y : ℂ), ((1 * heightRatio y : ℝ) : ℂ)] Q * ((vecOf c y i : ℝ) : ℂ))

def meanRest (P : ChartParams) (D : FieldData) (i : Fin 3) (y : Space) : ℂ :=
  ((meanLin D i y * P.L0⁻¹ : ℝ) : ℂ) * ((decayFactor P y * chartS P y - 1 : ℝ) : ℂ)

theorem meanNear_third {P : ChartParams} (hP : IsChartParams P) (Q : MvPolynomial (Fin 2) ℂ)
    (c i : Fin 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Space, y ≠ 0 → ContDiffAt ℝ 3 (meanNear P Q c i) y ∧
      ‖iteratedFDeriv ℝ 3 (meanNear P Q c i) y‖ ≤ K * ‖y‖⁻¹ := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have h1 : ∀ s : ℝ, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) s := fun _ => zero_le_one
  have ha : ∀ s : ℝ, (0 : ℝ) ≤ |s| := fun s => abs_nonneg s
  have hpv := SymbolW.mul hU h1 h1 (piece_symbol hP Q 1) (vecOf_symbol c i)
  have htt := SymbolW.mul hU ha ha (chartT_symbol hP) (chartT_symbol hP)
  have h4 := SymbolW.mul hU (fun s => mul_nonneg (ha s) (ha s)) (fun s => by positivity) htt hpv
  have hs : SymbolW {y : Space | y ≠ 0} _ (meanNear P Q c i) :=
    SymbolW.mul hU h1 (fun s => by positivity) (decay_symbol hP) h4
  obtain ⟨K, hK, hb⟩ := hs.third_le zero_le_one (fun s hs0 => by
    rw [abs_of_pos hs0]
    nlinarith)
  exact ⟨K, hK, fun y hy => ⟨hs.1.contDiffAt (hU.mem_nhds hy), hb y hy hy⟩⟩

theorem meanRest_third {P : ChartParams} (hP : IsChartParams P) (D : FieldData) (i : Fin 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Space, y ≠ 0 → ContDiffAt ℝ 3 (meanRest P D i) y ∧
      ‖iteratedFDeriv ℝ 3 (meanRest P D i) y‖ ≤ K * ‖y‖⁻¹ := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have hs : SymbolW {y : Space | y ≠ 0} _ (meanRest P D i) :=
    SymbolW.mul hU (fun s => by positivity) (fun s => abs_nonneg s) (meanLin_symbol D i P.L0⁻¹)
      (decayS_symbol hP)
  obtain ⟨K, hK, hb⟩ := hs.third_le zero_le_one (fun s hs0 => by
    rw [abs_of_pos hs0]
    nlinarith)
  exact ⟨K, hK, fun y hy => ⟨hs.1.contDiffAt (hU.mem_nhds hy), hb y hy hy⟩⟩

theorem meanFar_third {P : ChartParams} (hP : IsChartParams P) (Q : MvPolynomial (Fin 2) ℂ)
    (c i : Fin 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Space, y ≠ 0 → ContDiffAt ℝ 3 (meanFar P Q c i) y ∧
      ‖iteratedFDeriv ℝ 3 (meanFar P Q c i) y‖ ≤ K * ‖y‖⁻¹ ^ 3 := by
  have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  have h1 : ∀ s : ℝ, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) s := fun _ => zero_le_one
  have hpv := SymbolW.mul hU h1 h1 (piece_symbol hP Q 1) (vecOf_symbol c i)
  have hs : SymbolW {y : Space | y ≠ 0} _ (meanFar P Q c i) :=
    SymbolW.mul hU h1 (fun s => by positivity) (decay_symbol hP) hpv
  obtain ⟨hcd, C, hC, hb⟩ := hs
  refine ⟨C, hC, fun y hy => ⟨hcd.contDiffAt (hU.mem_nhds hy), ?_⟩⟩
  have := hb y hy 3 le_rfl
  simpa using this

theorem meanTerm_third_bound {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) (h0 : (0 : ℤ) ∈ D.modes) :
    ∃ (K : ℝ) (Rs cs : Finset ℝ), 0 ≤ K ∧ (∀ c ∈ cs, |c| < 1) ∧
      ∀ z : Space, z ≠ 0 → (∀ R ∈ Rs, ‖z‖ ≠ R) → (∀ c ∈ cs, z 2 ≠ c * ‖z‖) →
        ContDiffAt ℝ 3 (modeTerm P D β 0) z ∧
        ‖iteratedFDeriv ℝ 3 (modeTerm P D β 0) z‖ ≤ K * ‖z‖⁻¹ := by
  obtain ⟨Qs, b₀, hb₀, hQ⟩ := mean_freeze hP hD β h0
  have hL := hP.L0_pos
  have hN := fun q : MvPolynomial (Fin 2) ℂ × Fin 3 × Fin 3 => meanNear_third hP q.1 q.2.1 q.2.2
  have hF := fun q : MvPolynomial (Fin 2) ℂ × Fin 3 × Fin 3 => meanFar_third hP q.1 q.2.1 q.2.2
  have hE := fun i : Fin 3 => meanRest_third hP D i
  choose KN hKN0 hKNb using hN
  choose KF hKF0 hKFb using hF
  choose KE hKE0 hKEb using hE
  set S := Qs ×ˢ (Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3)) with hS
  have hKN : ∀ q ∈ S, KN q ≤ ∑ q ∈ S, KN q := fun q hq =>
    Finset.single_le_sum (f := KN) (fun q _ => hKN0 q) hq
  have hKF : ∀ q ∈ S, KF q ≤ ∑ q ∈ S, KF q := fun q hq =>
    Finset.single_le_sum (f := KF) (fun q _ => hKF0 q) hq
  have hKE : ∀ i, KE i ≤ ∑ i : Fin 3, KE i := fun i =>
    Finset.single_le_sum (f := KE) (fun i _ => hKE0 i) (Finset.mem_univ i)
  have hsN0 : 0 ≤ ∑ q ∈ S, KN q := Finset.sum_nonneg (fun q _ => hKN0 q)
  have hsF0 : 0 ≤ ∑ q ∈ S, KF q := Finset.sum_nonneg (fun q _ => hKF0 q)
  have hsE0 : 0 ≤ ∑ i : Fin 3, KE i := Finset.sum_nonneg (fun i _ => hKE0 i)
  have hLb : 0 < P.L0 * b₀ := mul_pos hL hb₀
  have hF0 : 0 ≤ (∑ q ∈ S, KF q) / (P.L0 * b₀) ^ 2 := by positivity
  set Kt := ∑ i : Fin 3, KE i + ∑ q ∈ S, KN q + (∑ q ∈ S, KF q) / (P.L0 * b₀) ^ 2 with hKt
  have hKt0 : 0 ≤ Kt := by positivity
  refine ⟨3 * (4 * Kt), breakRadii P D, breakCones D, by positivity, breakCones_abs_lt D, ?_⟩
  intro z hz hR hc
  let G : Fin 3 → Space → ℂ := fun i y => (decayFactor P y : ℂ) * (modePhase P 0 β y *
    (reducedField P D 0 β (chartT P y) (heightRatio y) 0 * radialVec y i +
      reducedField P D 0 β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
      reducedField P D 0 β (chartT P y) (heightRatio y) 2 * azimVecQ y i))
  have hmt : modeTerm P D β 0 = fun y => ofComponents (fun i => (G i y).re) := rfl
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz0 : 0 ≤ ‖z‖⁻¹ := by positivity
  have hcomp : ∀ i : Fin 3, ContDiffAt ℝ 3 (G i) z ∧
      ‖iteratedFDeriv ℝ 3 (G i) z‖ ≤ 4 * Kt * ‖z‖⁻¹ := by
    intro i
    rcases hQ z hz hR hc with hnear | ⟨hfar, hfarQ⟩
    · choose Q hQm hEq using hnear
      have hloc : G i =ᶠ[nhds z] fun y => ((meanLin D i y * P.L0⁻¹ : ℝ) : ℂ) +
          (meanRest P D i y + ∑ c : Fin 3, meanNear P (Q c) c i y) := by
        filter_upwards [hEq 0, hEq 1, hEq 2, isOpen_ne.mem_nhds hz] with y h0 h1 h2 hy
        have hy0 : y ≠ 0 := hy
        have hys : 0 < ‖y‖ := norm_pos_iff.mpr hy0
        have hkey := meanGuard_sum hP D hy0 i
        have hS' : chartS P y = P.L0 / (‖y‖ + P.L0) := by
          have : 0 < ‖y‖ + P.L0 := by positivity
          simp only [chartS, chartT]
          field_simp
          ring
        have hr : chartT P y * (meanGuard D 0 y * radialVec y i + meanGuard D 1 y * polarVecQ y i +
            meanGuard D 2 y * azimVecQ y i) = meanLin D i y * P.L0⁻¹ * chartS P y := by
          simp only [Fin.sum_univ_three, vecOf, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hkey
          rw [hkey, hS']
          have : 0 < ‖y‖ + P.L0 := by positivity
          field_simp
        have hkeyC : (chartT P y : ℂ) * ((meanGuard D 0 y : ℂ) * (radialVec y i : ℂ) +
            (meanGuard D 1 y : ℂ) * (polarVecQ y i : ℂ) + (meanGuard D 2 y : ℂ) * (azimVecQ y i : ℂ)) =
            ((meanLin D i y * P.L0⁻¹ : ℝ) : ℂ) * (chartS P y : ℂ) := by
          exact_mod_cast hr
        simp only [G, meanRest, meanNear, Fin.sum_univ_three, vecOf, modePhase_zero,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons]
        rw [h0, h1, h2]
        push_cast at hkeyC ⊢
        linear_combination (decayFactor P y : ℂ) * hkeyC
      have hcdN : ∀ c, ContDiffAt ℝ 3 (meanNear P (Q c) c i) z := fun c => (hKNb (Q c, c, i) z hz).1
      have hcdE := (hKEb i z hz).1
      have hcdL : ContDiffAt ℝ 3 (fun y => ((meanLin D i y * P.L0⁻¹ : ℝ) : ℂ)) z :=
        (Complex.ofRealCLM.contDiff.comp ((meanLin D i).contDiff.mul contDiff_const)).contDiffAt
      have hcdS : ContDiffAt ℝ 3 (fun y => ∑ c : Fin 3, meanNear P (Q c) c i y) z :=
        ContDiffAt.sum (fun c _ => hcdN c)
      have hcdR : ContDiffAt ℝ 3
          (fun y => meanRest P D i y + ∑ c : Fin 3, meanNear P (Q c) c i y) z := hcdE.add hcdS
      refine ⟨(hcdL.add hcdR).congr_of_eventuallyEq hloc, ?_⟩
      rw [(hloc.iteratedFDeriv ℝ 3).eq_of_nhds, fun_iteratedFDeriv_add_apply hcdL hcdR,
        linear_third_zero, zero_add, fun_iteratedFDeriv_add_apply hcdE hcdS,
        iteratedFDeriv_fun_sum_apply (fun c _ => hcdN c)]
      have hle : KE i + 3 * ∑ q ∈ S, KN q ≤ 4 * Kt := by
        rw [hKt]
        linarith [hKE i]
      calc _ ≤ ‖iteratedFDeriv ℝ 3 (meanRest P D i) z‖ +
            ∑ c : Fin 3, ‖iteratedFDeriv ℝ 3 (meanNear P (Q c) c i) z‖ :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
        _ ≤ KE i * ‖z‖⁻¹ + ∑ _c : Fin 3, (∑ q ∈ S, KN q) * ‖z‖⁻¹ := by
            gcongr with c
            · exact (hKEb i z hz).2
            · refine (hKNb (Q c, c, i) z hz).2.trans ?_
              gcongr
              exact hKN _ (by simp [hS, hQm c])
        _ = (KE i + 3 * ∑ q ∈ S, KN q) * ‖z‖⁻¹ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ 4 * Kt * ‖z‖⁻¹ := mul_le_mul_of_nonneg_right hle hz0
    · choose Q hQm hEq using hfarQ
      have hzb : P.L0 * b₀ ≤ ‖z‖ := by
        have hpos : 0 < ‖z‖ + P.L0 := by positivity
        have h1 : b₀ * (‖z‖ + P.L0) ≤ ‖z‖ := by
          have := hfar
          simp only [chartT] at this
          rwa [le_div_iff₀ hpos] at this
        have hb1 : b₀ ≤ 1 := by
          have : chartT P z ≤ 1 := by
            simp only [chartT]
            rw [div_le_one hpos]
            linarith
          linarith
        nlinarith
      have hloc : G i =ᶠ[nhds z] fun y => ∑ c : Fin 3, meanFar P (Q c) c i y := by
        filter_upwards [hEq 0, hEq 1, hEq 2] with y h0 h1 h2
        simp only [G, meanFar, Fin.sum_univ_three, vecOf, modePhase_zero,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons]
        rw [h0, h1, h2]
        ring
      have hcdF : ∀ c, ContDiffAt ℝ 3 (meanFar P (Q c) c i) z := fun c => (hKFb (Q c, c, i) z hz).1
      refine ⟨(ContDiffAt.sum (fun c _ => hcdF c)).congr_of_eventuallyEq hloc, ?_⟩
      rw [(hloc.iteratedFDeriv ℝ 3).eq_of_nhds, iteratedFDeriv_fun_sum_apply (fun c _ => hcdF c)]
      have hinv : ‖z‖⁻¹ ≤ (P.L0 * b₀)⁻¹ := inv_anti₀ hLb hzb
      have hw : ‖z‖⁻¹ ^ 3 ≤ ‖z‖⁻¹ / (P.L0 * b₀) ^ 2 := by
        calc ‖z‖⁻¹ ^ 3 = ‖z‖⁻¹ * ‖z‖⁻¹ ^ 2 := by ring
          _ ≤ ‖z‖⁻¹ * (P.L0 * b₀)⁻¹ ^ 2 := by gcongr
          _ = ‖z‖⁻¹ / (P.L0 * b₀) ^ 2 := by rw [inv_pow, div_eq_mul_inv]
      have hle : 3 * ((∑ q ∈ S, KF q) / (P.L0 * b₀) ^ 2) ≤ 4 * Kt := by
        rw [hKt]
        linarith
      calc _ ≤ ∑ c : Fin 3, ‖iteratedFDeriv ℝ 3 (meanFar P (Q c) c i) z‖ := norm_sum_le _ _
        _ ≤ ∑ _c : Fin 3, (∑ q ∈ S, KF q) * (‖z‖⁻¹ / (P.L0 * b₀) ^ 2) := by
            gcongr with c
            refine (hKFb (Q c, c, i) z hz).2.trans ?_
            gcongr
            exact hKF _ (by simp [hS, hQm c])
        _ = 3 * ((∑ q ∈ S, KF q) / (P.L0 * b₀) ^ 2) * ‖z‖⁻¹ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ 4 * Kt * ‖z‖⁻¹ := mul_le_mul_of_nonneg_right hle hz0
  rw [hmt]
  obtain ⟨h1, h2⟩ := components_third (g := G) (fun i => (hcomp i).1) (fun i => (hcomp i).2)
  exact ⟨h1, h2.trans (le_of_eq (by ring))⟩

private lemma ofComponents_apply (w : Fin 3 → ℝ) (j : Fin 3) : ofComponents w j = w j := by
  fin_cases j <;> simp [ofComponents]

private lemma fieldOf_eq_sum (P : ChartParams) (D : FieldData) (β : ℝ) :
    fieldOf P D β = fun y => ∑ n ∈ D.modes, modeTerm P D β n y := by
  funext y
  ext j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [fieldOf, modeTerm, ofComponents_apply]
  rw [Finset.mul_sum, Complex.re_sum]

private lemma third_of_contDiffAt {f : Space → Space} {z : Space} (h : ContDiffAt ℝ 3 f z) :
    DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) z ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ = ‖iteratedFDeriv ℝ 3 f z‖ := by
  refine ⟨?_, ?_⟩
  · have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) z := h.fderiv_right (by norm_num)
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) z := h2.fderiv_right (by norm_num)
    exact h1.differentiableAt (by norm_num)
  · rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]

theorem fieldOf_third_bound {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) :
    ∃ (K : ℝ) (Rs cs : Finset ℝ), 0 ≤ K ∧ (∀ c ∈ cs, |c| < 1) ∧
      ∀ z : Space, z ≠ 0 → (∀ R ∈ Rs, ‖z‖ ≠ R) → (∀ c ∈ cs, z 2 ≠ c * ‖z‖) →
        DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (fieldOf P D β))) z ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fieldOf P D β))) z‖ ≤ K * ‖z‖⁻¹ := by
  have key : ∀ n ∈ D.modes, ∃ (K : ℝ) (Rs cs : Finset ℝ), 0 ≤ K ∧ (∀ c ∈ cs, |c| < 1) ∧
      ∀ z : Space, z ≠ 0 → (∀ R ∈ Rs, ‖z‖ ≠ R) → (∀ c ∈ cs, z 2 ≠ c * ‖z‖) →
        ContDiffAt ℝ 3 (modeTerm P D β n) z ∧
        ‖iteratedFDeriv ℝ 3 (modeTerm P D β n) z‖ ≤ K * ‖z‖⁻¹ := by
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      exact meanTerm_third_bound hP hD β hn
    · exact waveTerm_third_bound hP hD β hn hn0
  choose! K Rs cs hK hcs hz using key
  refine ⟨∑ n ∈ D.modes, K n, D.modes.biUnion Rs, D.modes.biUnion cs,
    Finset.sum_nonneg hK, ?_, ?_⟩
  · intro c hc
    obtain ⟨n, hn, hc'⟩ := Finset.mem_biUnion.mp hc
    exact hcs n hn c hc'
  · intro z hz0 hR hc
    have hall : ∀ n ∈ D.modes, ContDiffAt ℝ 3 (modeTerm P D β n) z ∧
        ‖iteratedFDeriv ℝ 3 (modeTerm P D β n) z‖ ≤ K n * ‖z‖⁻¹ := by
      intro n hn
      exact hz n hn z hz0 (fun R hR' => hR R (Finset.mem_biUnion.mpr ⟨n, hn, hR'⟩))
        (fun c hc' => hc c (Finset.mem_biUnion.mpr ⟨n, hn, hc'⟩))
    have hcd : ContDiffAt ℝ 3 (fieldOf P D β) z := by
      rw [fieldOf_eq_sum]
      exact ContDiffAt.sum (fun n hn => (hall n hn).1)
    obtain ⟨hdiff, hnorm⟩ := third_of_contDiffAt hcd
    refine ⟨hdiff, ?_⟩
    rw [hnorm, fieldOf_eq_sum, iteratedFDeriv_fun_sum_apply (fun n hn => (hall n hn).1)]
    calc ‖∑ n ∈ D.modes, iteratedFDeriv ℝ 3 (modeTerm P D β n) z‖
        ≤ ∑ n ∈ D.modes, ‖iteratedFDeriv ℝ 3 (modeTerm P D β n) z‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ D.modes, K n * ‖z‖⁻¹ := Finset.sum_le_sum (fun n hn => (hall n hn).2)
      _ = (∑ n ∈ D.modes, K n) * ‖z‖⁻¹ := by rw [Finset.sum_mul]

end ProfilePowerJumpsPieces

end FracInternal

end Breakdown
