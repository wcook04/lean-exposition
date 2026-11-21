import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.AssemblyModelLabels
import Breakdown.CertCell.CrossWaveBound
import Breakdown.CertCell.StretchTripleBound
import Breakdown.CertCell.AssemblyCrossWaveTraceFreeProof

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem splitCharge_nonneg {σc cs cv : ℝ} (hσ : 0 ≤ σc) (hs : 0 ≤ cs) (hv : 0 ≤ cv) (a : Fin 3 → ℂ)
    (g : Fin 3 × Fin 3 → ℂ) : 0 ≤ splitCharge σc cs cv a g := by
  unfold splitCharge
  have h1 : 0 ≤ cnormSq (curlOfGrad g) := Finset.sum_nonneg (fun _ _ => by positivity)
  have h2 : 0 ≤ cnormSq g := Finset.sum_nonneg (fun _ _ => by positivity)
  have h3 : 0 ≤ cnormSq a := Finset.sum_nonneg (fun _ _ => by positivity)
  have := mul_nonneg hσ h1
  have := mul_nonneg hs h2
  have := mul_nonneg hv h3
  linarith

theorem half_sqrt_nine_halves : Real.sqrt (9 / 2) / 2 = 3 / (2 * Real.sqrt 2) := by
  have h : Real.sqrt (9 / 2) * Real.sqrt 2 = 3 := by
    rw [← Real.sqrt_mul (by norm_num), show (9 / 2 : ℝ) * 2 = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : 0 < Real.sqrt 2 := by positivity
  rw [eq_div_iff (by positivity)]
  linear_combination h

theorem crossCharge_eq_classCharge (σc γc ℓ : ℝ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) :
    Bridge.crossCharge σc γc ℓ a g = Bridge.classCharge (Real.sqrt (9 / 2)) σc γc ℓ a g := by
  unfold Bridge.crossCharge Bridge.classCharge
  rw [half_sqrt_nine_halves]

theorem classCharge_nonneg {κ σc γc ℓ : ℝ} (hκ : 0 ≤ κ) (hσ : 0 ≤ σc) (hγ : 0 ≤ γc) (hℓ : 0 < ℓ)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : 0 ≤ Bridge.classCharge κ σc γc ℓ a g := by
  have e : Bridge.classCharge κ σc γc ℓ a g = splitCharge σc (κ / 2 * γc * ℓ) (κ / 2 * γc / ℓ) a g := by
    unfold Bridge.classCharge splitCharge
    ring
  rw [e]
  exact splitCharge_nonneg hσ (by positivity) (by positivity) a g

theorem classCharge_group {V : Type} (P : PotentialData V) (i : Fin P.groupCount) (a : Fin 3 → ℂ)
    (g : Fin 3 × Fin 3 → ℂ) :
    Bridge.classCharge (P.groupKappa i) (P.groupStrain i) (P.groupGrad i) P.length a g = groupCharge P i a g := by
  unfold Bridge.classCharge groupCharge splitCharge
  ring

theorem kappa_nonneg {κ : ℝ} (hκ : κ = Real.sqrt (7 / 2) ∨ κ = Real.sqrt (9 / 2)) : 0 ≤ κ := by
  rcases hκ with rfl | rfl <;> exact Real.sqrt_nonneg _

theorem modeSecond_swap (ι : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hH : ∀ σ y u w, H σ y u w = H σ y w u) (σ : ℝ) (y : Space) (a b c : Fin 3) :
    modeSecondDeriv ι H σ y (a, b, c) = modeSecondDeriv ι H σ y (a, c, b) := by
  unfold modeSecondDeriv modeAverage
  congr 1
  refine intervalIntegral.integral_congr (fun τ _ => ?_)
  refine intervalIntegral.integral_congr (fun φ _ => ?_)
  dsimp only
  rw [hH]

theorem curlSecond_trace (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (hs : ∀ a b c, h (a, b, c) = h (a, c, b)) :
    ∑ j : Fin 3, curlGradOfSecondDeriv h (j, j) = 0 := by
  have anti : ∀ a j m : Fin 3, (alternatingSymbol j a m : ℂ) = -(alternatingSymbol a j m : ℂ) := by
    intro a j m
    unfold alternatingSymbol
    push_cast
    ring
  unfold curlGradOfSecondDeriv
  dsimp only
  have e : ∑ a : Fin 3, ∑ j : Fin 3, ∑ m : Fin 3, (alternatingSymbol a j m : ℂ) * h (m, a, j)
      = -∑ a : Fin 3, ∑ j : Fin 3, ∑ m : Fin 3, (alternatingSymbol a j m : ℂ) * h (m, a, j) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [anti x y m, hs m y x]
    ring
  linear_combination e / 2

theorem sliceWaveBound (W : Bridge.CrossWaveEntry) (hW : Bridge.IsCrossWaveEntry W) (p : ℝ × ℝ)
    (hp : p ∈ W.region) (A A' : Finset ℤ) (x x' : ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) :
    2 * ‖∑ n₁ ∈ A, ∑ n ∈ W.waveModes, if n₁ + n ∈ A' then
        Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (x n₁).1 (x n₁).2
          (star (x' (n₁ + n)).1) (star (x' (n₁ + n)).2) else 0‖
      ≤ W.balance * ∑ n₁ ∈ A, Bridge.crossCharge W.strainBound W.vorticityGradBound W.length (x n₁).1 (x n₁).2
        + W.balance⁻¹ * ∑ n₂ ∈ A', Bridge.crossCharge W.strainBound W.vorticityGradBound W.length
          (x' n₂).1 (x' n₂).2 := by
  have h := Bridge.crossWaveBound Bridge.stretchTripleBound W.azimuthOrder A A' W.waveModes x x'
    (fun n => W.strainMode n p) (fun n => W.vorticityGradMode n p) W.strainBound W.vorticityGradBound
    W.length W.balance hW.order_pos hW.strainBound_nonneg hW.vorticityGradBound_nonneg hW.length_pos
    hW.balance_pos (hW.strain_majorant p hp) (hW.vorticityGrad_majorant p hp)
  have e : (∑ n ∈ W.waveModes, ∑ n₁ ∈ A, ∑ n₂ ∈ A', if n + n₁ = n₂ then
        Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (x n₁).1 (x n₁).2
          (star (x' n₂).1) (star (x' n₂).2) else 0)
      = ∑ n₁ ∈ A, ∑ n ∈ W.waveModes, if n₁ + n ∈ A' then
        Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (x n₁).1 (x n₁).2
          (star (x' (n₁ + n)).1) (star (x' (n₁ + n)).2) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n₁ _ => Finset.sum_congr rfl (fun n _ => ?_))
    rw [Finset.sum_ite_eq, add_comm n n₁]
  rw [← e]
  exact h

theorem sliceWaveBoundClass (W : Bridge.CrossWaveEntry) (hW : Bridge.IsCrossWaveEntry W) (p : ℝ × ℝ)
    (hp : p ∈ W.region) (κ : ℝ) (hκ : κ = Real.sqrt (7 / 2) ∨ κ = Real.sqrt (9 / 2))
    (htr : κ = Real.sqrt (7 / 2) → ∀ θ, ∑ j : Fin 3, ∑ n ∈ W.waveModes,
      Bridge.azimuthPhase W.azimuthOrder n θ * curlGradOfSecondDeriv (W.vorticityGradMode n p) (j, j) = 0)
    (A A' : Finset ℤ) (x x' : ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) :
    2 * ‖∑ n₁ ∈ A, ∑ n ∈ W.waveModes, if n₁ + n ∈ A' then
        Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (x n₁).1 (x n₁).2
          (star (x' (n₁ + n)).1) (star (x' (n₁ + n)).2) else 0‖
      ≤ W.balance * ∑ n₁ ∈ A, Bridge.classCharge κ W.strainBound W.vorticityGradBound W.length (x n₁).1 (x n₁).2
        + W.balance⁻¹ * ∑ n₂ ∈ A', Bridge.classCharge κ W.strainBound W.vorticityGradBound W.length
          (x' n₂).1 (x' n₂).2 := by
  rcases hκ with rfl | rfl
  · have h := Bridge.crossWaveTraceFreeBound W.azimuthOrder A A' W.waveModes x x'
      (fun n => W.strainMode n p) (fun n => W.vorticityGradMode n p) W.strainBound W.vorticityGradBound
      W.length W.balance hW.order_pos hW.strainBound_nonneg hW.vorticityGradBound_nonneg hW.length_pos
      hW.balance_pos (hW.strain_majorant p hp) (hW.vorticityGrad_majorant p hp) (htr rfl)
    have e : (∑ n ∈ W.waveModes, ∑ n₁ ∈ A, ∑ n₂ ∈ A', if n + n₁ = n₂ then
          Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (x n₁).1 (x n₁).2
            (star (x' n₂).1) (star (x' n₂).2) else 0)
        = ∑ n₁ ∈ A, ∑ n ∈ W.waveModes, if n₁ + n ∈ A' then
          Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (x n₁).1 (x n₁).2
            (star (x' (n₁ + n)).1) (star (x' (n₁ + n)).2) else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun n₁ _ => Finset.sum_congr rfl (fun n _ => ?_))
      rw [Finset.sum_ite_eq, add_comm n n₁]
    rw [← e]
    exact h
  · simp only [← crossCharge_eq_classCharge]
    exact sliceWaveBound W hW p hp A A' x x'

theorem sum_slices {β : Type*} [AddCommMonoid β] (M : Finset (ℤ × ℤ)) (f : ℤ × ℤ → β) :
    ∑ l ∈ M.image Prod.snd, ∑ n₁ ∈ (M.filter (fun ι => ι.2 = l)).image Prod.fst, f (n₁, l) = ∑ ι ∈ M, f ι := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := M) (t := M.image Prod.snd) (g := Prod.snd)
    (fun i hi => Finset.mem_image_of_mem _ hi) f]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl (fun ι hι => ?_)
    rw [Finset.mem_filter] at hι
    rw [← hι.2]
  · intro a ha b hb hab
    rw [Finset.coe_filter] at ha hb
    exact Prod.ext hab (ha.2.trans hb.2.symm)

theorem sum_slices_le (P' : Finset (ℤ × ℤ)) (L : Finset ℤ) (s : ℤ) (g : ℤ × ℤ → ℝ) (hg : ∀ ι ∈ P', 0 ≤ g ι) :
    ∑ l ∈ L, ∑ n₂ ∈ (P'.filter (fun ι => ι.2 = l + s)).image Prod.fst, g (n₂, l + s) ≤ ∑ ι ∈ P', g ι := by
  have e : ∀ l, ∑ n₂ ∈ (P'.filter (fun ι => ι.2 = l + s)).image Prod.fst, g (n₂, l + s)
      = ∑ ι ∈ P', if ι.2 - s = l then g ι else 0 := by
    intro l
    rw [Finset.sum_image, ← Finset.sum_filter]
    · refine Finset.sum_congr (Finset.filter_congr (fun ι _ => by omega)) (fun ι hι => ?_)
      rw [Finset.mem_filter] at hι
      have : ι.2 = l + s := by omega
      rw [← this]
    · intro a ha b hb hab
      rw [Finset.coe_filter] at ha hb
      exact Prod.ext hab (ha.2.trans hb.2.symm)
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun ι hι => ?_)
  rw [Finset.sum_ite_eq]
  split_ifs
  · exact le_rfl
  · exact hg ι hι

theorem groupWaveBound (W : Bridge.CrossWaveEntry) (hW : Bridge.IsCrossWaveEntry W) (p : ℝ × ℝ)
    (hp : p ∈ W.region) (κ : ℝ) (hκ : κ = Real.sqrt (7 / 2) ∨ κ = Real.sqrt (9 / 2))
    (htr : κ = Real.sqrt (7 / 2) → ∀ θ, ∑ j : Fin 3, ∑ n ∈ W.waveModes,
      Bridge.azimuthPhase W.azimuthOrder n θ * curlGradOfSecondDeriv (W.vorticityGradMode n p) (j, j) = 0) (s : ℤ) (M P' : Finset (ℤ × ℤ)) (X Y : ℤ × ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) :
    2 * ‖∑ ι ∈ M, ∑ n ∈ W.waveModes, if (ι.1 + n, ι.2 + s) ∈ P' then
        Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (X ι).1 (X ι).2
          (star (Y (ι.1 + n, ι.2 + s)).1) (star (Y (ι.1 + n, ι.2 + s)).2) else 0‖
      ≤ W.balance * ∑ ι ∈ M, Bridge.classCharge κ W.strainBound W.vorticityGradBound W.length (X ι).1 (X ι).2
        + W.balance⁻¹ * ∑ ι ∈ P', Bridge.classCharge κ W.strainBound W.vorticityGradBound W.length
          (Y ι).1 (Y ι).2 := by
  set cc := Bridge.classCharge κ W.strainBound W.vorticityGradBound W.length with hcc
  have hcc0 : ∀ a g, 0 ≤ cc a g := fun a g =>
    classCharge_nonneg (kappa_nonneg hκ) hW.strainBound_nonneg hW.vorticityGradBound_nonneg hW.length_pos a g
  set L := M.image Prod.snd with hL
  have hA' : ∀ l m, m ∈ (P'.filter (fun ι => ι.2 = l + s)).image Prod.fst ↔ (m, l + s) ∈ P' := by
    intro l m
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨ha, ha2⟩, rfl⟩
      rw [← ha2]
      exact ha
    · intro h
      exact ⟨(m, l + s), ⟨h, rfl⟩, rfl⟩
  have hslice : ∀ l, 2 * ‖∑ n₁ ∈ (M.filter (fun ι => ι.2 = l)).image Prod.fst, ∑ n ∈ W.waveModes,
        if ((n₁, l).1 + n, (n₁, l).2 + s) ∈ P' then
        Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (X (n₁, l)).1 (X (n₁, l)).2
          (star (Y ((n₁, l).1 + n, (n₁, l).2 + s)).1) (star (Y ((n₁, l).1 + n, (n₁, l).2 + s)).2) else 0‖
      ≤ W.balance * ∑ n₁ ∈ (M.filter (fun ι => ι.2 = l)).image Prod.fst, cc (X (n₁, l)).1 (X (n₁, l)).2
        + W.balance⁻¹ * ∑ n₂ ∈ (P'.filter (fun ι => ι.2 = l + s)).image Prod.fst,
          cc (Y (n₂, l + s)).1 (Y (n₂, l + s)).2 := by
    intro l
    have h := sliceWaveBoundClass W hW p hp κ hκ htr ((M.filter (fun ι => ι.2 = l)).image Prod.fst)
      ((P'.filter (fun ι => ι.2 = l + s)).image Prod.fst) (fun n₁ => X (n₁, l)) (fun n₂ => Y (n₂, l + s))
    simp only [hA'] at h
    exact h
  rw [← sum_slices M, ← sum_slices M]
  calc 2 * ‖∑ l ∈ L, ∑ n₁ ∈ (M.filter (fun ι => ι.2 = l)).image Prod.fst, ∑ n ∈ W.waveModes,
        if ((n₁, l).1 + n, (n₁, l).2 + s) ∈ P' then
        Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (X (n₁, l)).1 (X (n₁, l)).2
          (star (Y ((n₁, l).1 + n, (n₁, l).2 + s)).1) (star (Y ((n₁, l).1 + n, (n₁, l).2 + s)).2) else 0‖
      ≤ ∑ l ∈ L, 2 * ‖∑ n₁ ∈ (M.filter (fun ι => ι.2 = l)).image Prod.fst, ∑ n ∈ W.waveModes,
        if ((n₁, l).1 + n, (n₁, l).2 + s) ∈ P' then
        Bridge.stretchTriple (W.strainMode n p) (W.vorticityGradMode n p) (X (n₁, l)).1 (X (n₁, l)).2
          (star (Y ((n₁, l).1 + n, (n₁, l).2 + s)).1) (star (Y ((n₁, l).1 + n, (n₁, l).2 + s)).2) else 0‖ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
    _ ≤ ∑ l ∈ L, (W.balance * ∑ n₁ ∈ (M.filter (fun ι => ι.2 = l)).image Prod.fst, cc (X (n₁, l)).1 (X (n₁, l)).2
        + W.balance⁻¹ * ∑ n₂ ∈ (P'.filter (fun ι => ι.2 = l + s)).image Prod.fst,
          cc (Y (n₂, l + s)).1 (Y (n₂, l + s)).2) := Finset.sum_le_sum (fun l _ => hslice l)
    _ ≤ W.balance * ∑ l ∈ L, ∑ n₁ ∈ (M.filter (fun ι => ι.2 = l)).image Prod.fst, cc (X (n₁, l)).1 (X (n₁, l)).2
        + W.balance⁻¹ * ∑ ι ∈ P', cc (Y ι).1 (Y ι).2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hW.balance_pos.le))
        exact sum_slices_le P' L s (fun ι => cc (Y ι).1 (Y ι).2) (fun ι _ => hcc0 _ _)

theorem pairWaveBound (W : Bridge.CrossWaveEntry) (hW : Bridge.IsCrossWaveEntry W) (p : ℝ × ℝ)
    (hp : p ∈ W.region) (κ : ℝ) (hκ : κ = Real.sqrt (7 / 2) ∨ κ = Real.sqrt (9 / 2))
    (htr : κ = Real.sqrt (7 / 2) → ∀ θ, ∑ j : Fin 3, ∑ n ∈ W.waveModes,
      Bridge.azimuthPhase W.azimuthOrder n θ * curlGradOfSecondDeriv (W.vorticityGradMode n p) (j, j) = 0) (n₀ : ℤ) (hn : n₀ ∈ W.waveModes) (a : ℤ) (x x' : (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) :
    2 * ‖Bridge.stretchTriple (W.strainMode n₀ p) (W.vorticityGradMode n₀ p) x.1 x.2 (star x'.1) (star x'.2)‖
      ≤ W.balance * Bridge.classCharge κ W.strainBound W.vorticityGradBound W.length x.1 x.2
        + W.balance⁻¹ * Bridge.classCharge κ W.strainBound W.vorticityGradBound W.length x'.1 x'.2 := by
  have h := sliceWaveBoundClass W hW p hp κ hκ htr {a} {a + n₀} (fun _ => x) (fun _ => x')
  simp only [Finset.sum_singleton, Finset.mem_singleton, add_right_inj] at h
  rw [Finset.sum_ite_eq' W.waveModes n₀, if_pos hn] at h
  exact h

theorem regroupCross {G : ℕ} (Rs Bd B : Finset (ℤ × ℤ)) (modes partners harm : Fin G → Finset (ℤ × ℤ))
    (f : ℤ × ℤ → ℤ × ℤ → ℂ)
    (hcover : ∀ ι ∈ Rs, ∀ β ∈ B, ι + β ∉ Rs → ι + β ∉ Bd → f ι β ≠ 0 →
      ∃ i, ι ∈ modes i ∧ ι + β ∈ partners i ∧ β ∈ harm i)
    (hsub : ∀ i, harm i ⊆ B) (hdisj : ∀ i j β, β ∈ harm i → β ∈ harm j → i = j) :
    (∑ ι ∈ Rs, ∑ β ∈ B, if ι + β ∉ Rs ∧ ι + β ∉ Bd then f ι β else 0)
      = ∑ i, ∑ ι ∈ Rs.filter (fun ι => ι ∈ modes i), ∑ β ∈ harm i,
          if ι + β ∈ (partners i).filter (fun ι' => ι' ∉ Rs ∧ ι' ∉ Bd) then f ι β else 0 := by
  have step1 : ∀ ι ∈ Rs, ∀ β ∈ B, (if ι + β ∉ Rs ∧ ι + β ∉ Bd then f ι β else 0)
      = ∑ i, if ι ∈ modes i ∧ β ∈ harm i ∧ ι + β ∈ (partners i).filter (fun ι' => ι' ∉ Rs ∧ ι' ∉ Bd)
          then f ι β else 0 := by
    intro ι hι β hβ
    by_cases hD : ι + β ∉ Rs ∧ ι + β ∉ Bd
    · by_cases hf : f ι β = 0
      · rw [if_pos hD, hf]
        symm
        exact Finset.sum_eq_zero (fun i _ => ite_self _)
      obtain ⟨i0, h1, h2, h3⟩ := hcover ι hι β hβ hD.1 hD.2 hf
      rw [if_pos hD, Finset.sum_eq_single i0]
      · rw [if_pos ⟨h1, h3, Finset.mem_filter.2 ⟨h2, hD⟩⟩]
      · intro j _ hj
        rw [if_neg]
        rintro ⟨_, hj2, _⟩
        exact hj (hdisj j i0 β hj2 h3)
      · intro h
        exact absurd (Finset.mem_univ i0) h
    · rw [if_neg hD]
      symm
      refine Finset.sum_eq_zero (fun i _ => if_neg ?_)
      rintro ⟨_, _, h⟩
      exact hD (Finset.mem_filter.1 h).2
  rw [Finset.sum_congr rfl (fun ι hι => Finset.sum_congr rfl (fun β hβ => step1 ι hι β hβ))]
  rw [Finset.sum_congr rfl (fun ι _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  by_cases hm : ι ∈ modes i
  · rw [if_pos hm]
    symm
    rw [← Finset.sum_subset (hsub i)]
    · refine Finset.sum_congr rfl (fun β hβ => ?_)
      by_cases hq : ι + β ∈ (partners i).filter (fun ι' => ι' ∉ Rs ∧ ι' ∉ Bd)
      · rw [if_pos hq, if_pos ⟨hm, hβ, hq⟩]
      · rw [if_neg hq, if_neg]
        rintro ⟨_, _, h⟩
        exact hq h
    · intro β _ hβ
      rw [if_neg]
      rintro ⟨_, h, _⟩
      exact hβ h
  · rw [if_neg hm]
    refine Finset.sum_eq_zero (fun β _ => if_neg ?_)
    rintro ⟨h, _, _⟩
    exact hm h

theorem groupWave_traceFree (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count)
    (i : Fin (P.potential K).groupCount) (hκ : (P.potential K).groupKappa i = Real.sqrt (7 / 2)) (p : ℝ × ℝ) :
    ∀ θ, ∑ j : Fin 3, ∑ n ∈ ((P.potential K).groupWave i).waveModes,
      Bridge.azimuthPhase ((P.potential K).groupWave i).azimuthOrder n θ
        * curlGradOfSecondDeriv (((P.potential K).groupWave i).vorticityGradMode n p) (j, j) = 0 := by
  obtain ⟨-, ho, -, -, -, -, -, -, -, -, htr⟩ := hP.group_wave K i
  rw [ho]
  exact htr hκ p

theorem groupModelTriple_eq (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count)
    (i : Fin (P.potential K).groupCount) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) (n : ℤ)
    (x : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (x' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K (n, (P.potential K).groupShift i) a b p)
        (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K (n, (P.potential K).groupShift i) a b p)
        x g x' g'
      = Bridge.stretchTriple (((P.potential K).groupWave i).strainMode n p)
          (((P.potential K).groupWave i).vorticityGradMode n p) x g x' g' := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, hv, -⟩ := hP.group_wave K i
  have e1 : (fun a b => D.model.strain.planeValue D.mesh.box K (n, (P.potential K).groupShift i) a b p)
      = fun a b => (((P.potential K).groupWave i).strainMode n p (a, b)
          + ((P.potential K).groupWave i).strainMode n p (b, a)) / 2 := by
    funext a b
    rw [hs n p a b, hs n p b a, hP.model_strain_symmetric K _ b a p hp]
    ring
  have e2 : (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K (n, (P.potential K).groupShift i) a b p)
      = fun a b => curlGradOfSecondDeriv (((P.potential K).groupWave i).vorticityGradMode n p) (a, b) := by
    funext a b
    rw [hv n p a b]
  rw [e1, e2]
  rfl

theorem labelFlip_neg (ι : ℤ × ℤ) : labelFlip (-ι) = -labelFlip ι := by
  refine Prod.ext ?_ ?_ <;> simp [labelFlip] <;> ring

theorem matPlaneValue_neg {count : ℕ} (F : CellMatField count) (box : Fin count → CellBox)
    (hF : F.IsConjugateClosed box) (K : Fin count) (ι : ℤ × ℤ) (a b : Fin 3) (p : ℝ × ℝ) :
    F.planeValue box K (-ι) a b p = (starRingEnd ℂ) (F.planeValue box K ι a b p) := by
  unfold CellMatField.planeValue labelValueAt
  split_ifs
  · exact hF.2 K ι a b p
  · rw [labelFlip_neg, hF.2 K (labelFlip ι) a b (p.1, -p.2), map_mul, Complex.conj_ofReal]

theorem modelTriple_off_model (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (β : ℤ × ℤ)
    (hm : -β ∉ modelLabels D K) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect)
    (x : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (y : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) :
    modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K β a b p)
      (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K β a b p) x g y h = 0 := by
  obtain ⟨-, -, hS, hG⟩ := (hP.cell_conditions.model_split K).model_conj_closed
  have hz := modelPlaneValues_eq_zero_of_not_mem D K (-β) (hP.velocity_off_labels K (-β))
    (hP.vorticity_off_labels K (-β)) (hP.strain_off_labels K (-β)) (hP.vorticity_grad_off_labels K (-β)) hm p hp
  have e1 : (fun a b => D.model.strain.planeValue D.mesh.box K β a b p) = fun _ _ => 0 := by
    funext a b
    rw [← neg_neg β, matPlaneValue_neg _ _ hS, hz.2.2.1 a b, map_zero]
  have e2 : (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K β a b p) = fun _ _ => 0 := by
    funext a b
    rw [← neg_neg β, matPlaneValue_neg _ _ hG, hz.2.2.2 a b, map_zero]
  rw [e1, e2]
  simp [modelTriple, modelBilin, curlOfGrad]

theorem groupCrossBound (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (B : Finset (ℤ × ℤ))
    (hcover : ∀ ι ∈ D.mesh.resolved K, ∀ β ∈ B, -β ∈ modelLabels D K → ι + β ∉ D.mesh.resolved K →
      ι + β ∉ D.mesh.band K → ∃ i, ι ∈ (P.potential K).groupModes i ∧ ι + β ∈ (P.potential K).groupPartners i ∧
        β ∈ (P.potential K).groupHarmonics i)
    (hsub : ∀ i, (P.potential K).groupHarmonics i ⊆ B)
    (hdisj : ∀ i j β, β ∈ (P.potential K).groupHarmonics i → β ∈ (P.potential K).groupHarmonics j → i = j)
    (X Y : ℤ × ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) :
    2 * ‖∑ ι ∈ D.mesh.resolved K, ∑ β ∈ B, if ι + β ∉ D.mesh.resolved K ∧ ι + β ∉ D.mesh.band K then
        modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K β a b p)
          (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K β a b p) (X ι).1 (X ι).2
          (star (Y (ι + β)).1) (star (Y (ι + β)).2) else 0‖
      ≤ ∑ i, ((P.potential K).groupBalance i * (∑ ι ∈ D.mesh.resolved K,
            if ι ∈ (P.potential K).groupModes i then groupCharge (P.potential K) i (X ι).1 (X ι).2 else 0)
          + ((P.potential K).groupBalance i)⁻¹ * (∑ ι' ∈ (P.potential K).groupPartners i,
            if ι' ∉ D.mesh.resolved K ∧ ι' ∉ D.mesh.band K then groupCharge (P.potential K) i (Y ι').1 (Y ι').2 else 0)) := by
  have hr := regroupCross (D.mesh.resolved K) (D.mesh.band K) B (P.potential K).groupModes
    (P.potential K).groupPartners (P.potential K).groupHarmonics
    (fun ι β => modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K β a b p)
          (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K β a b p) (X ι).1 (X ι).2
          (star (Y (ι + β)).1) (star (Y (ι + β)).2))
    (fun ι hι β hβ h1 h2 hf => hcover ι hι β hβ (by
      by_contra hm
      exact hf (modelTriple_off_model D R A P hP K β hm p hp _ _ _ _)) h1 h2) hsub hdisj
  rw [hr]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  obtain ⟨hWi, _, hreg, hsb, hvb, hbal, hlen, hharm, -, -, -⟩ := hP.group_wave K i
  have hp' : p ∈ ((P.potential K).groupWave i).region := by
    rw [hreg]
    exact hp
  have h := groupWaveBound ((P.potential K).groupWave i) hWi p hp' _ (hP.group_kappa K i)
    (fun hκ => groupWave_traceFree D R A P hP K i hκ p)
    ((P.potential K).groupShift i)
    ((D.mesh.resolved K).filter (fun ι => ι ∈ (P.potential K).groupModes i))
    ((P.potential K).groupPartners i |>.filter (fun ι' => ι' ∉ D.mesh.resolved K ∧ ι' ∉ D.mesh.band K)) X Y
  simp only [hsb, hvb, hbal, hlen, classCharge_group] at h
  have hadd : ∀ ι : ℤ × ℤ, ∀ n : ℤ, ι + (n, (P.potential K).groupShift i) = (ι.1 + n, ι.2 + (P.potential K).groupShift i) :=
    fun ι n => rfl
  have hinj : Set.InjOn (fun n : ℤ => (n, (P.potential K).groupShift i)) ((P.potential K).groupWave i).waveModes := by
    intro a _ b _ hab
    exact (Prod.mk.inj hab).1
  rw [Finset.sum_congr rfl (fun ι _ => by rw [hharm, Finset.sum_image hinj])]
  simp only [groupModelTriple_eq D R A P hP K i p hp]
  simp only [hadd]
  simp only [Finset.sum_filter] at h ⊢
  exact h

theorem partnerCostLeCharges (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (ι : ℤ × ℤ)
    (hι : ι ∉ D.mesh.resolved K) (hb : ι ∉ D.mesh.band K) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect)
    (wc wg wv : ℝ) (hc : 0 ≤ wc) (hg : 0 ≤ wg) (hv : 0 ≤ wv) :
    (∑ i, if ι ∈ (P.potential K).groupPartners i then
        (P.potential K).groupStrain i / (P.potential K).groupBalance i * wc
          + (P.potential K).groupKappa i / 2 * (P.potential K).length * (P.potential K).groupGrad i
            / (P.potential K).groupBalance i * wg
          + (P.potential K).groupKappa i / 2 * (P.potential K).groupGrad i
            / ((P.potential K).length * (P.potential K).groupBalance i) * wv else 0)
      + (if ι ∈ (A.blocks K).leakModes then
          (A.blocks K).leakCurl ι * wc + (A.blocks K).leakStrain ι * wg + (A.blocks K).leakVel ι * wv else 0)
      + creditVelDemand D R K ι p * wv
      + (if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * wg
      + (if ∃ ι₀ ∈ D.mesh.resolved K, ι₀ - ι ∈ (P.potential K).harmonicLabels then (P.potential K).epsStrain + longFactor (P.potential K) ι * (P.potential K).longStrain
          + (P.potential K).highStrain / (P.potential K).youngCurl else 0) * wc
      + (if ∃ ι₀ ∈ D.mesh.resolved K, ι₀ - ι ∈ (P.potential K).harmonicLabels then 3 / (2 * Real.sqrt 2) * (((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
          * (P.potential K).epsLength + (P.potential K).highGrad / (P.potential K).youngVel) else 0) * wg
      + (if ∃ ι₀ ∈ D.mesh.resolved K, ι₀ - ι ∈ (P.potential K).harmonicLabels then 3 / (2 * Real.sqrt 2) * (((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
          / (P.potential K).length + (P.potential K).highGrad / (P.potential K).youngStrain) else 0) * wv
      ≤ (R.entryCharges K ι).curlCharge p * wc + (R.entryCharges K ι).gradCharge p * wg
        + (R.entryCharges K ι).velCharge p * wv := by
  obtain ⟨h1, h2, h3⟩ := hP.charges_cover K ι hι hb p hp
  have k1 := mul_le_mul_of_nonneg_right h1 hc
  have k2 := mul_le_mul_of_nonneg_right h2 hg
  have k3 := mul_le_mul_of_nonneg_right h3 hv
  have e : (∑ i, if ι ∈ (P.potential K).groupPartners i then
        (P.potential K).groupStrain i / (P.potential K).groupBalance i * wc
          + (P.potential K).groupKappa i / 2 * (P.potential K).length * (P.potential K).groupGrad i
            / (P.potential K).groupBalance i * wg
          + (P.potential K).groupKappa i / 2 * (P.potential K).groupGrad i
            / ((P.potential K).length * (P.potential K).groupBalance i) * wv else 0)
      = (∑ i, if ι ∈ (P.potential K).groupPartners i then
          (P.potential K).groupStrain i / (P.potential K).groupBalance i else 0) * wc
        + (∑ i, if ι ∈ (P.potential K).groupPartners i then (P.potential K).groupKappa i / 2 * (P.potential K).length
          * (P.potential K).groupGrad i / (P.potential K).groupBalance i else 0) * wg
        + (∑ i, if ι ∈ (P.potential K).groupPartners i then (P.potential K).groupKappa i / 2 * (P.potential K).groupGrad i
          / ((P.potential K).length * (P.potential K).groupBalance i) else 0) * wv := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> ring
  rw [e]
  simp only [add_mul] at k1 k2 k3 ⊢
  split_ifs at k1 k2 k3 ⊢ <;> (try simp only [zero_mul, add_zero] at k1 k2 k3 ⊢) <;> linarith

theorem modelBilin_add_left (S Gω : Fin 3 → Fin 3 → ℂ) (a₁ a₂ : Fin 3 → ℂ) (g₁ g₂ : Fin 3 × Fin 3 → ℂ)
    (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelBilin S Gω (a₁ + a₂) (g₁ + g₂) a' g' = modelBilin S Gω a₁ g₁ a' g' + modelBilin S Gω a₂ g₂ a' g' := by
  simp only [modelBilin, curlOfGrad, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem modelBilin_add_right (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ)
    (a₁ a₂ : Fin 3 → ℂ) (g₁ g₂ : Fin 3 × Fin 3 → ℂ) :
    modelBilin S Gω a g (a₁ + a₂) (g₁ + g₂) = modelBilin S Gω a g a₁ g₁ + modelBilin S Gω a g a₂ g₂ := by
  simp only [modelBilin, curlOfGrad, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem modelBilin_smul_left (S Gω : Fin 3 → Fin 3 → ℂ) (c : ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ)
    (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelBilin S Gω (c • a) (c • g) a' g' = c * modelBilin S Gω a g a' g' := by
  simp only [modelBilin, curlOfGrad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_neg,
    mul_add]
  simp only [mul_assoc, mul_comm, mul_left_comm]

theorem modelBilin_smul_right (S Gω : Fin 3 → Fin 3 → ℂ) (c : ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ)
    (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelBilin S Gω a g (c • a') (c • g') = c * modelBilin S Gω a g a' g' := by
  simp only [modelBilin, curlOfGrad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_neg,
    mul_add]
  simp only [mul_assoc, mul_comm, mul_left_comm]

theorem modelTriple_add_left (S Gω : Fin 3 → Fin 3 → ℂ) (a₁ a₂ : Fin 3 → ℂ) (g₁ g₂ : Fin 3 × Fin 3 → ℂ)
    (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω (a₁ + a₂) (g₁ + g₂) a' g' = modelTriple S Gω a₁ g₁ a' g' + modelTriple S Gω a₂ g₂ a' g' := by
  unfold modelTriple
  rw [modelBilin_add_left, modelBilin_add_right]
  ring

theorem modelTriple_add_right (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ)
    (a₁ a₂ : Fin 3 → ℂ) (g₁ g₂ : Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω a g (a₁ + a₂) (g₁ + g₂) = modelTriple S Gω a g a₁ g₁ + modelTriple S Gω a g a₂ g₂ := by
  unfold modelTriple
  rw [modelBilin_add_left, modelBilin_add_right]
  ring

theorem modelTriple_smul_left (S Gω : Fin 3 → Fin 3 → ℂ) (c : ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ)
    (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω (c • a) (c • g) a' g' = c * modelTriple S Gω a g a' g' := by
  unfold modelTriple
  rw [modelBilin_smul_left, modelBilin_smul_right]
  ring

theorem modelTriple_smul_right (S Gω : Fin 3 → Fin 3 → ℂ) (c : ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ)
    (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω a g (c • a') (c • g') = c * modelTriple S Gω a g a' g' := by
  unfold modelTriple
  rw [modelBilin_smul_left, modelBilin_smul_right]
  ring

theorem modelTriple_sum_left {ι : Type*} (S Gω : Fin 3 → Fin 3 → ℂ) (s : Finset ι) (c : ι → ℂ)
    (a : ι → Fin 3 → ℂ) (g : ι → Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω (∑ j ∈ s, c j • a j) (∑ j ∈ s, c j • g j) a' g'
      = ∑ j ∈ s, c j * modelTriple S Gω (a j) (g j) a' g' := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := modelTriple_smul_left S Gω 0 0 0 a' g'
    simp only [zero_smul, zero_mul] at h
    simpa using h
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, modelTriple_add_left,
      modelTriple_smul_left, ih]

theorem modelTriple_sum_right {ι : Type*} (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ)
    (s : Finset ι) (c : ι → ℂ) (a' : ι → Fin 3 → ℂ) (g' : ι → Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω a g (∑ j ∈ s, c j • a' j) (∑ j ∈ s, c j • g' j)
      = ∑ j ∈ s, c j * modelTriple S Gω a g (a' j) (g' j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := modelTriple_smul_right S Gω 0 a g 0 0
    simp only [zero_smul, zero_mul] at h
    simpa using h
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, modelTriple_add_right,
      modelTriple_smul_right, ih]

theorem velOf_eq_sum (U : Fin 12 → ℂ) : velOf U = ∑ j, U j • velOf (Pi.single j 1) := by
  funext a
  simp [velOf, Finset.sum_apply, Pi.single_apply]

theorem gradOf_eq_sum (U : Fin 12 → ℂ) : gradOf U = ∑ j, U j • gradOf (Pi.single j 1) := by
  funext a
  simp [gradOf, Finset.sum_apply, Pi.single_apply]

theorem star_velOf_eq_sum (U : Fin 12 → ℂ) :
    star (velOf U) = ∑ j, (starRingEnd ℂ) (U j) • star (velOf (Pi.single j 1)) := by
  funext a
  simp [velOf, Finset.sum_apply, Pi.single_apply, apply_ite]

theorem star_gradOf_eq_sum (U : Fin 12 → ℂ) :
    star (gradOf U) = ∑ j, (starRingEnd ℂ) (U j) • star (gradOf (Pi.single j 1)) := by
  funext a
  simp [gradOf, Finset.sum_apply, Pi.single_apply, apply_ite]

theorem sesq_modelTriple (S Gω : Fin 3 → Fin 3 → ℂ) (U U' : Fin 12 → ℂ) :
    sesq12 (fun i j => modelTriple S Gω (velOf (Pi.single j 1)) (gradOf (Pi.single j 1))
        (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1)))) U U'
      = modelTriple S Gω (velOf U') (gradOf U') (star (velOf U)) (star (gradOf U)) := by
  rw [velOf_eq_sum U', gradOf_eq_sum U', star_velOf_eq_sum U, star_gradOf_eq_sum U, modelTriple_sum_left]
  simp only [modelTriple_sum_right]
  unfold sesq12
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem modelTriple_swap (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) : modelTriple S Gω a g a' g' = modelTriple S Gω a' g' a g := by
  unfold modelTriple
  ring

theorem conj_modelTriple (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) :
    (starRingEnd ℂ) (modelTriple S Gω a g a' g')
      = modelTriple (fun i j => (starRingEnd ℂ) (S i j)) (fun i j => (starRingEnd ℂ) (Gω i j)) (star a) (star g)
          (star a') (star g') := by
  simp only [modelTriple, modelBilin, curlOfGrad, map_div₀, map_add, map_neg, map_sum, map_mul, Pi.star_apply,
    Complex.conj_ofReal, map_one, map_ofNat, Complex.star_def]

theorem stretchTriple_eq_modelTriple (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ)
    (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    Bridge.stretchTriple gW hW a g a' g'
      = modelTriple (fun i j => (gW (i, j) + gW (j, i)) / 2) (fun i j => curlGradOfSecondDeriv hW (i, j)) a g a' g' := rfl

theorem labelHarmonic_neg (m : ℕ) (α : ℤ × ℤ) : labelHarmonic m (-α) = -labelHarmonic m α := by
  simp only [labelHarmonic, labelTime, labelAzimuth, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  ext
  · simp
    ring
  · simp

theorem modeAverage_neg {β : Type*} (ξ : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage (-ξ) f b = (starRingEnd ℂ) (modeAverage ξ f b) := by
  unfold modeAverage
  rw [map_mul]
  congr 1
  · have h2c : (starRingEnd ℂ) (2 : ℂ) = 2 := by simp [Complex.ext_iff]
    simp [h2c]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
  have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  simp only
  rw [intervalIntegral.integral_of_le h2, intervalIntegral.integral_of_le h2, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun φ => ?_))
  simp only
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem labelGrad_neg (m : ℕ) (α : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    modeGrad (labelHarmonic m (-α)) G 0 (planePoint p) = star (modeGrad (labelHarmonic m α) G 0 (planePoint p)) := by
  funext ij
  rw [labelHarmonic_neg, Pi.star_apply, Complex.star_def]
  exact modeAverage_neg _ _ _

theorem secondModes_neg (m : ℕ) (α : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    modeSecondDeriv (labelHarmonic m (-α)) H 0 (planePoint p) = star (modeSecondDeriv (labelHarmonic m α) H 0 (planePoint p)) := by
  funext ij
  rw [labelHarmonic_neg, Pi.star_apply, Complex.star_def]
  exact modeAverage_neg _ _ _

theorem sesq_realCoupling (m : ℕ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (α : ℤ × ℤ) (p : ℝ × ℝ) (U U' : Fin 12 → ℂ) :
    (sesq12 (fun i j => modelTriple
        (fun a b => (labelGrad m α (gradField W) p (a, b) + labelGrad m α (gradField W) p (b, a)) / 2)
        (fun a b => curlGradOfSecondDeriv (labelHess m α HW p) (a, b))
        (velOf (Pi.single j 1)) (gradOf (Pi.single j 1)) (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))))
        U U').re
      = (Bridge.stretchTriple (modeGrad (labelHarmonic m (-α)) (gradField W) 0 (planePoint p))
          (modeSecondDeriv (labelHarmonic m (-α)) HW 0 (planePoint p)) (velOf U) (gradOf U)
          (star (velOf U')) (star (gradOf U'))).re := by
  rw [sesq_modelTriple, modelTriple_swap, stretchTriple_eq_modelTriple, labelGrad_neg, secondModes_neg,
    ← Complex.conj_re (modelTriple _ _ (velOf U) _ _ _), conj_modelTriple, star_star, star_star]
  congr 2
  · funext i j
    simp only [labelGrad, Pi.star_apply, Complex.star_def, map_div₀, map_add, Complex.conj_conj, map_ofNat]
  · funext i j
    simp only [labelHess, curlGradOfSecondDeriv, Pi.star_apply, Complex.star_def, map_sum, map_mul, Complex.conj_ofReal,
      Complex.conj_conj]

theorem sesq_couplingModel (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (α : ℤ × ℤ)
    (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) (U U' : Fin 12 → ℂ) :
    (sesq12 ((P.potential K).couplingModel α p) U U').re
      = (modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K (-α) a b p)
          (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K (-α) a b p) (velOf U) (gradOf U)
          (star (velOf U')) (star (gradOf U'))).re := by
  obtain ⟨-, -, hS, hG⟩ := (hP.cell_conditions.model_split K).model_conj_closed
  rw [hP.coupling_model K α p hp U U', modelTriple_swap,
    ← Complex.conj_re (modelTriple _ _ (star (velOf U)) _ _ _), conj_modelTriple, star_star, star_star]
  simp only [← matPlaneValue_neg _ _ hS, ← matPlaneValue_neg _ _ hG]

end Internal

end Assembly

end CertCell

end Breakdown
