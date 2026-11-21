import Breakdown.FracCell.StEnergyProof

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis

namespace EnergyCrossProjInternal

def polyOf (cf : ℕ → ℕ → ℝ) (j : ℕ) (r : ℝ) : ℝ := ∑ i ∈ Finset.range (j + 1), cf j i * r ^ i

lemma pow_mem_span (cf : ℕ → ℕ → ℝ) (hlead : ∀ j, 0 < cf j j) (d : ℕ) :
    ∀ i, i ≤ d → (fun r : ℝ => r ^ i) ∈
      Submodule.span ℝ (Set.range fun j : Fin (d + 1) => polyOf cf j) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hc : cf i i ≠ 0 := (hlead i).ne'
    have heq : (fun r : ℝ => r ^ i) =
        (cf i i)⁻¹ • (polyOf cf i - ∑ t ∈ Finset.range i, cf i t • fun r : ℝ => r ^ t) := by
      funext r
      simp only [polyOf, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_range_succ]
      field_simp
      ring
    rw [heq]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩)
      (Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ ?_))
    have ht' := Finset.mem_range.1 ht
    exact ih t ht' (by omega)

lemma pow_eq_comb (cf : ℕ → ℕ → ℝ) (hlead : ∀ j, 0 < cf j j) (d i : ℕ) (hi : i ≤ d) :
    ∃ a : Fin (d + 1) → ℝ, ∀ r : ℝ, r ^ i = ∑ j : Fin (d + 1), a j * polyOf cf j r := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (pow_mem_span cf hlead d i hi)
  refine ⟨a, fun r => ?_⟩
  have := congrFun ha r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

def basisC (B : CellBases) (j l : ℕ) : ℝ × ℝ → ℂ := fun p => ((basisFn B j l p : ℝ) : ℂ)

def basisSpan (B : CellBases) (d : ℕ) : Submodule ℂ (ℝ × ℝ → ℂ) :=
  Submodule.span ℂ (Set.range fun jl : Fin (d + 1) × Fin (d + 1) => basisC B jl.1 jl.2)

lemma mono_mem (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (d i m : ℕ) (hi : i ≤ d) (hm : m ≤ d) :
    (fun p : ℝ × ℝ => (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ m) ∈ basisSpan B d := by
  obtain ⟨a, ha⟩ := pow_eq_comb B.radialCoef hB.radial_leading d i hi
  obtain ⟨b, hb⟩ := pow_eq_comb B.heightCoef hB.height_leading d m hm
  have heq : (fun p : ℝ × ℝ => (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ m) =
      ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), ((a j * b l : ℝ) : ℂ) • basisC B j l := by
    funext p
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ha p.1, hb p.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisC, basisFn, CellBases.radialPoly,
      CellBases.heightPoly, polyOf]
    push_cast
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [heq]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, l), rfl⟩)

lemma poly_mem (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (d : ℕ) (T : ℝ × ℝ → ℂ)
    (hT : T ∈ polyFn d d) : T ∈ basisSpan B d := by
  obtain ⟨c, hc⟩ := hT
  have heq : T = ∑ i : Fin (d + 1), ∑ m : Fin (d + 1),
      c i m • fun p : ℝ × ℝ => (p.1 : ℂ) ^ (i : ℕ) * (p.2 : ℂ) ^ (m : ℕ) := by
    funext p
    simp only [hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun m _ =>
    Submodule.smul_mem _ _ (mono_mem K B hB d i m (by omega) (by omega))

lemma basisC_continuous (B : CellBases) (j l : ℕ) : Continuous (basisC B j l) := by
  unfold basisC basisFn CellBases.radialPoly CellBases.heightPoly
  fun_prop

lemma lineWeight_continuous (K : CellBox) : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1) := by
  unfold CellBox.lineWeight
  split_ifs <;> fun_prop

lemma rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

lemma rect_measurable (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

lemma span_continuous (B : CellBases) (d : ℕ) (T : ℝ × ℝ → ℂ) (hT : T ∈ basisSpan B d) : Continuous T := by
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨jl, rfl⟩ := hx
    exact basisC_continuous B _ _
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.mul hx

lemma ortho (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (j l j' l' : ℕ) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * basisC B j' l' p * basisC B j l p =
      if j' = j ∧ l' = l then 1 else 0 := by
  have hreal : ∫ p in K.rect, K.lineWeight p.1 * basisFn B j' l' p * basisFn B j l p =
      (∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * B.radialPoly j' r * B.radialPoly j r) *
        ∫ z in Set.Icc K.z₁ K.z₂, B.heightPoly l' z * B.heightPoly l z := by
    rw [CellBox.rect, Measure.volume_eq_prod, ← Measure.prod_restrict, ← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [basisFn]
    ring
  have hc : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * basisC B j' l' p * basisC B j l p =
      ((∫ p in K.rect, K.lineWeight p.1 * basisFn B j' l' p * basisFn B j l p : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [basisC]
    push_cast
    ring
  rw [hc, hreal, hB.radial_orthonormal, hB.height_orthonormal]
  by_cases h1 : j' = j <;> by_cases h2 : l' = l <;> simp [h1, h2]

lemma polyFn_zero (d d' : ℕ) : (0 : ℝ × ℝ → ℂ) ∈ polyFn d d' :=
  ⟨fun _ _ => 0, fun p => by simp⟩

lemma polyFn_add {d d' : ℕ} {P T : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') (hT : T ∈ polyFn d d') :
    P + T ∈ polyFn d d' := by
  obtain ⟨c, hc⟩ := hP
  obtain ⟨e, he⟩ := hT
  exact ⟨fun j l => c j l + e j l, fun p => by
    simp only [Pi.add_apply, hc, he, add_mul, Finset.sum_add_distrib]⟩

lemma polyFn_smul {d d' : ℕ} {P : ℝ × ℝ → ℂ} (a : ℂ) (hP : P ∈ polyFn d d') : a • P ∈ polyFn d d' := by
  obtain ⟨c, hc⟩ := hP
  exact ⟨fun j l => a * c j l, fun p => by
    simp only [Pi.smul_apply, smul_eq_mul, hc, Finset.mul_sum, mul_assoc]⟩

lemma polyFn_sum {d d' : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℝ × ℝ → ℂ) (hf : ∀ i ∈ s, f i ∈ polyFn d d') :
    ∑ i ∈ s, f i ∈ polyFn d d' := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyFn_zero d d'
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact polyFn_add (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma mono_poly (d i m : ℕ) (hi : i ≤ d) (hm : m ≤ d) :
    (fun p : ℝ × ℝ => (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ m) ∈ polyFn d d := by
  refine ⟨fun a b => if (a : ℕ) = i ∧ (b : ℕ) = m then 1 else 0, fun p => ?_⟩
  rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin (d + 1)), Finset.sum_eq_single (⟨m, by omega⟩ : Fin (d + 1))]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ m := fun h => hb (Fin.ext h)
    simp [this]
  · simp
  · intro a _ ha
    have : (a : ℕ) ≠ i := fun h => ha (Fin.ext h)
    simp [this]
  · simp

lemma basisC_poly (B : CellBases) (d j l : ℕ) (hj : j ≤ d) (hl : l ≤ d) : basisC B j l ∈ polyFn d d := by
  have heq : basisC B j l = ∑ i ∈ Finset.range (j + 1), ∑ m ∈ Finset.range (l + 1),
      ((B.radialCoef j i * B.heightCoef l m : ℝ) : ℂ) • fun p : ℝ × ℝ => (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ m := by
    funext p
    simp only [basisC, basisFn, CellBases.radialPoly, CellBases.heightPoly, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    push_cast
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [heq]
  refine polyFn_sum _ _ fun i hi => polyFn_sum _ _ fun m hm => polyFn_smul _ (mono_poly d i m ?_ ?_)
  · have := Finset.mem_range.1 hi; omega
  · have := Finset.mem_range.1 hm; omega

lemma span_poly (B : CellBases) (d : ℕ) (T : ℝ × ℝ → ℂ) (hT : T ∈ basisSpan B d) : T ∈ polyFn d d := by
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨jl, rfl⟩ := hx
    exact basisC_poly B d _ _ (by omega) (by omega)
  | zero => exact polyFn_zero d d
  | add x y _ _ hx hy => exact polyFn_add hx hy
  | smul a x _ hx => exact polyFn_smul a hx

lemma poly_continuous {d d' : ℕ} (T : ℝ × ℝ → ℂ) (hT : T ∈ polyFn d d') : Continuous T := by
  obtain ⟨c, hc⟩ := hT
  have : T = fun p : ℝ × ℝ => ∑ j, ∑ l, c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) := funext hc
  rw [this]
  fun_prop

end EnergyCrossProjInternal

open EnergyCrossProjInternal in
theorem lowProj_ae_eq_coefSum (K : CellBox) (B : CellBases) (hK : IsCellBox K) (hB : IsCellBases K B)
    (F : ℝ × ℝ → ℂ) (hF : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p) K.rect) (d : ℕ) :
    K.proj d d F =ᵐ[volume.restrict K.rect]
      fun p => ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), B.coef K F j l * ((basisFn B j l p : ℝ) : ℂ) := by
  have hmeas := rect_measurable K
  have hcomp := rect_compact K
  have hw := lineWeight_continuous K
  have hwc : Continuous (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hw
  set P₀ : ℝ × ℝ → ℂ := ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), B.coef K F j l • basisC B j l with hP₀
  have hP₀apply : ∀ p, P₀ p =
      ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), B.coef K F j l * ((basisFn B j l p : ℝ) : ℂ) := by
    intro p
    simp only [hP₀, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisC]
  have hP₀span : P₀ ∈ basisSpan B d :=
    Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, l), rfl⟩)
  have hP₀cont : Continuous P₀ := span_continuous B d P₀ hP₀span
  have hint : ∀ P T : ℝ × ℝ → ℂ, Continuous P → Continuous T →
      IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * (F p - P p) * (starRingEnd ℂ) (T p)) K.rect := by
    intro P T hP hT
    have h1 : IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * (F p - P p)) K.rect := by
      have h2 : IntegrableOn (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ) * P p) K.rect :=
        (hwc.mul hP).continuousOn.integrableOn_compact hcomp
      refine (hF.sub h2).congr_fun (fun p _ => ?_) hmeas
      simp only [Pi.sub_apply]
      ring
    exact h1.mul_continuousOn (Complex.continuous_conj.comp hT).continuousOn hcomp
  have horth : ∀ T ∈ basisSpan B d, K.pairOn K.lineWeightFn (fun p => F p - P₀ p) T = 0 := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨j, l⟩, rfl⟩ := hx
      dsimp only
      have hβc := basisC_continuous B j l
      unfold CellBox.pairOn
      have hconj : ∀ p, (starRingEnd ℂ) (basisC B j l p) = basisC B j l p := fun p => by simp [basisC]
      simp only [hconj, CellBox.lineWeightFn, mul_sub, sub_mul]
      have hA : IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * F p * basisC B j l p) K.rect :=
        hF.mul_continuousOn hβc.continuousOn hcomp
      have hcB : ∀ j' l' : ℕ, Integrable (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * basisC B j' l' p * basisC B j l p)
          (volume.restrict K.rect) := fun j' l' =>
        ((hwc.mul (basisC_continuous B j' l')).mul hβc).continuousOn.integrableOn_compact hcomp
      have hC : IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * P₀ p * basisC B j l p) K.rect :=
        ((hwc.mul hP₀cont).mul hβc).continuousOn.integrableOn_compact hcomp
      rw [integral_sub hA hC]
      have h1 : ∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) * F p * basisC B j l p = B.coef K F j l := rfl
      have hexp : (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * P₀ p * basisC B j l p) = fun p =>
          ∑ j' : Fin (d + 1), ∑ l' : Fin (d + 1),
            B.coef K F j' l' * (((K.lineWeight p.1 : ℝ) : ℂ) * basisC B j' l' p * basisC B j l p) := by
        funext p
        rw [hP₀apply]
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun l' _ => ?_
        simp only [basisC]
        ring
      have hterm : ∀ j' l' : Fin (d + 1), Integrable (fun p => B.coef K F j' l' *
          (((K.lineWeight p.1 : ℝ) : ℂ) * basisC B j' l' p * basisC B j l p)) (volume.restrict K.rect) :=
        fun j' l' => (hcB j' l').const_mul _
      rw [h1, hexp, integral_finsetSum Finset.univ
        (fun j' _ => integrable_finsetSum Finset.univ (fun l' _ => hterm j' l'))]
      have hin : ∀ j' : Fin (d + 1), ∫ p in K.rect, ∑ l' : Fin (d + 1), B.coef K F j' l' *
          (((K.lineWeight p.1 : ℝ) : ℂ) * basisC B j' l' p * basisC B j l p) =
          ∑ l' : Fin (d + 1), B.coef K F j' l' * (if (j' : ℕ) = j ∧ (l' : ℕ) = l then 1 else 0) := fun j' => by
        rw [integral_finsetSum Finset.univ (fun l' _ => hterm j' l')]
        refine Finset.sum_congr rfl fun l' _ => ?_
        rw [integral_const_mul, ortho K B hB]
      simp only [hin, Fin.val_inj, mul_ite, mul_one, mul_zero, ite_and]
      simp
    | zero => simp [CellBox.pairOn]
    | add x y hxm hym hx hy =>
      have hxc := span_continuous B d x hxm
      have hyc := span_continuous B d y hym
      unfold CellBox.pairOn at hx hy ⊢
      simp only [CellBox.lineWeightFn] at hx hy ⊢
      simp only [Pi.add_apply, map_add, mul_add]
      rw [integral_add (hint P₀ x hP₀cont hxc) (hint P₀ y hP₀cont hyc), hx, hy, add_zero]
    | smul a x hxm hx =>
      unfold CellBox.pairOn at hx ⊢
      simp only [CellBox.lineWeightFn] at hx ⊢
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      have he : ∀ p : ℝ × ℝ, ((K.lineWeight p.1 : ℝ) : ℂ) * (F p - P₀ p) * ((starRingEnd ℂ) a * (starRingEnd ℂ) (x p)) =
          (starRingEnd ℂ) a * (((K.lineWeight p.1 : ℝ) : ℂ) * (F p - P₀ p) * (starRingEnd ℂ) (x p)) :=
        fun p => by ring
      simp only [he, integral_const_mul, hx, mul_zero]
  have hex : ∃ P ∈ polyFn d d, ∀ T ∈ polyFn d d, K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0 :=
    ⟨P₀, span_poly B d P₀ hP₀span, fun T hT => horth T (poly_mem K B hB d T hT)⟩
  have hproj : K.proj d d F = hex.choose := by
    unfold CellBox.proj
    rw [dif_pos hex]
  obtain ⟨hPpoly, hPorth⟩ := hex.choose_spec
  set P := hex.choose
  have hPc : Continuous P := poly_continuous P hPpoly
  set Dd : ℝ × ℝ → ℂ := P + (-1 : ℂ) • P₀ with hDd
  have hDapply : ∀ p, Dd p = P p - P₀ p := fun p => by simp only [hDd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hDpoly : Dd ∈ polyFn d d := polyFn_add hPpoly (polyFn_smul (-1) (span_poly B d P₀ hP₀span))
  have hDc : Continuous Dd := poly_continuous Dd hDpoly
  have e1 := hPorth Dd hDpoly
  have e2 := horth Dd (poly_mem K B hB d Dd hDpoly)
  unfold CellBox.pairOn at e1 e2
  simp only [CellBox.lineWeightFn] at e1 e2
  have hzero : ∫ p in K.rect, (((K.lineWeight p.1 * ‖Dd p‖ ^ 2 : ℝ)) : ℂ) = 0 := by
    have hs := integral_sub (hint P₀ Dd hP₀cont hDc) (hint P Dd hPc hDc)
    rw [e2, e1, sub_zero] at hs
    rw [← hs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have hn : (((K.lineWeight p.1 * ‖Dd p‖ ^ 2 : ℝ)) : ℂ) =
        ((K.lineWeight p.1 : ℝ) : ℂ) * (Dd p * (starRingEnd ℂ) (Dd p)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    simp only
    rw [hn, hDapply]
    ring
  have hreal : ∫ p in K.rect, K.lineWeight p.1 * ‖Dd p‖ ^ 2 = 0 := by
    rw [integral_complex_ofReal] at hzero
    exact_mod_cast hzero
  have hnn : 0 ≤ᵐ[volume.restrict K.rect] fun p => K.lineWeight p.1 * ‖Dd p‖ ^ 2 := by
    refine (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun p hp => ?_)
    have hr : 0 ≤ K.lineWeight p.1 := by
      unfold CellBox.lineWeight
      split_ifs with h0
      · exact h0 ▸ hp.1.1
      · exact zero_le_one
    exact mul_nonneg hr (sq_nonneg _)
  have hintR : Integrable (fun p => K.lineWeight p.1 * ‖Dd p‖ ^ 2) (volume.restrict K.rect) :=
    (hw.mul (hDc.norm.pow 2)).continuousOn.integrableOn_compact hcomp
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hintR).1 hreal
  have hpos : ∀ᵐ p ∂(volume.restrict K.rect), K.lineWeight p.1 ≠ 0 := by
    by_cases h0 : K.r₁ = 0
    · have hnull : volume (({(0 : ℝ)} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
        rw [Measure.volume_eq_prod, Measure.prod_prod]
        simp
      refine ae_restrict_of_ae ?_
      rw [ae_iff]
      refine measure_mono_null (fun p hp => ?_) hnull
      simp only [CellBox.lineWeight, h0, if_true, ne_eq, not_not, Set.mem_ofPred_eq] at hp
      exact ⟨hp, Set.mem_univ _⟩
    · exact Filter.Eventually.of_forall fun p => by simp [CellBox.lineWeight, h0]
  filter_upwards [hae, hpos] with p h1 h2
  simp only [Pi.zero_apply] at h1
  have h3 : ‖Dd p‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h h2
    · exact h
  have h4 : Dd p = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
    exact norm_eq_zero.1 this
  rw [hproj, ← hP₀apply]
  have := hDapply p
  rw [h4] at this
  exact (sub_eq_zero.1 this.symm)

end Breakdown.CellCert.CellEnergy
