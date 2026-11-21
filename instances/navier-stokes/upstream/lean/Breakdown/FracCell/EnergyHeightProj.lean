import Breakdown.FracCell.StEnergyProof

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellEnergy.HeightProj

open CellAnalysis

theorem sum_range_eq_fin {M : Type*} [AddCommMonoid M] (f : ℕ → M) {j Q : ℕ} (hj : j ≤ Q) :
    ∑ i ∈ Finset.range (j + 1), f i = ∑ i : Fin (Q + 1), if (i : ℕ) ≤ j then f i else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ j then f i else 0) (Q + 1), Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

def triPoly (co : ℕ → ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range (j + 1), co j k * x ^ k

theorem pow_span (co : ℕ → ℕ → ℝ) (hco : ∀ j, co j j ≠ 0) (Q : ℕ) :
    ∀ i ≤ Q, ∃ a : Fin (Q + 1) → ℝ, ∀ x : ℝ, x ^ i = ∑ j : Fin (Q + 1), a j * triPoly co j x := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    choose a ha using fun k : Fin i => ih k k.2 (by omega)
    refine ⟨fun j => (co i i)⁻¹ * ((if (j : ℕ) = i then 1 else 0) - ∑ k : Fin i, co i k * a k j), ?_⟩
    intro x
    have hP : triPoly co i x = co i i * x ^ i + ∑ k : Fin i, co i k * x ^ (k : ℕ) := by
      rw [triPoly, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range (fun k => co i k * x ^ k)]
      ring
    have h1 : ∑ j : Fin (Q + 1), (if (j : ℕ) = i then (1 : ℝ) else 0) * triPoly co j x = triPoly co i x := by
      rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin (Q + 1))]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ i := fun h => hb (Fin.ext h)
        simp [this]
      · simp
    have h2 : ∀ k : Fin i, ∑ j : Fin (Q + 1), a k j * triPoly co j x = x ^ (k : ℕ) := fun k => (ha k x).symm
    calc x ^ i = (co i i)⁻¹ * (triPoly co i x - ∑ k : Fin i, co i k * x ^ (k : ℕ)) := by
          rw [hP]; field_simp [hco i]; ring
      _ = (co i i)⁻¹ * (∑ j : Fin (Q + 1), (if (j : ℕ) = i then (1 : ℝ) else 0) * triPoly co j x
            - ∑ k : Fin i, co i k * ∑ j : Fin (Q + 1), a k j * triPoly co j x) := by
          rw [h1]; simp only [h2]
      _ = ∑ j : Fin (Q + 1), (co i i)⁻¹ * ((if (j : ℕ) = i then 1 else 0) - ∑ k : Fin i, co i k * a k j)
            * triPoly co j x := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin i)))]
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [mul_assoc, sub_mul, Finset.sum_mul]
          simp only [mul_assoc]

def polyFnG (d d' : ℕ) : Set (ℝ × ℝ → ℂ) :=
  {P | ∃ c : Fin (d + 1) → Fin (d' + 1) → ℂ, ∀ p : ℝ × ℝ,
    P p = ∑ j, ∑ l, c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ))}

def pairOnG (S : Set (ℝ × ℝ)) (m : ℝ × ℝ → ℝ) (F P : ℝ × ℝ → ℂ) : ℂ :=
  ∫ p in S, (m p : ℂ) * F p * (starRingEnd ℂ) (P p)

open Classical in
def projG (S : Set (ℝ × ℝ)) (m : ℝ × ℝ → ℝ) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  if h : ∃ P ∈ polyFnG d d', ∀ T ∈ polyFnG d d', pairOnG S m (fun p => F p - P p) T = 0
  then h.choose else 0

variable (rc hc : ℕ → ℕ → ℝ)

def bas (j l : ℕ) (p : ℝ × ℝ) : ℝ := triPoly rc j p.1 * triPoly hc l p.2

theorem triPoly_fin {Q j : ℕ} (hj : j ≤ Q) (x : ℝ) :
    triPoly rc j x = ∑ i : Fin (Q + 1), (if (i : ℕ) ≤ j then rc j i else 0) * x ^ (i : ℕ) := by
  rw [triPoly, sum_range_eq_fin _ hj]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

theorem bas_mem {Q j l : ℕ} (hj : j ≤ Q) (hl : l ≤ Q) :
    (fun p => ((bas rc hc j l p : ℝ) : ℂ)) ∈ polyFnG Q Q := by
  refine ⟨fun i k => (((if (i : ℕ) ≤ j then rc j i else 0) * (if (k : ℕ) ≤ l then hc l k else 0) : ℝ) : ℂ), ?_⟩
  intro p
  show ((bas rc hc j l p : ℝ) : ℂ) = _
  simp only [bas]
  rw [triPoly_fin rc hj, triPoly_fin hc hl, Finset.sum_mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem span_mem (hr : ∀ j, rc j j ≠ 0) (hh : ∀ j, hc j j ≠ 0) {Q : ℕ} {T : ℝ × ℝ → ℂ} (hT : T ∈ polyFnG Q Q) :
    ∃ e : Fin (Q + 1) → Fin (Q + 1) → ℂ, ∀ p, T p = ∑ j, ∑ l, e j l * ((bas rc hc j l p : ℝ) : ℂ) := by
  obtain ⟨c, hc'⟩ := hT
  choose a ha using fun i : Fin (Q + 1) => pow_span rc hr Q i (by omega)
  choose b hb using fun k : Fin (Q + 1) => pow_span hc hh Q k (by omega)
  refine ⟨fun j l => ∑ i, ∑ k, c i k * (a i j : ℂ) * (b k l : ℂ), ?_⟩
  intro p
  rw [hc' p]
  have e1 : ∀ i : Fin (Q + 1), ((p.1 : ℂ) ^ (i : ℕ)) = ∑ j, (a i j : ℂ) * (triPoly rc j p.1 : ℂ) := by
    intro i; rw [← Complex.ofReal_pow, ha i p.1]; push_cast; rfl
  have e2 : ∀ k : Fin (Q + 1), ((p.2 : ℂ) ^ (k : ℕ)) = ∑ l, (b k l : ℂ) * (triPoly hc l p.2 : ℂ) := by
    intro k; rw [← Complex.ofReal_pow, hb k p.2]; push_cast; rfl
  set X : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ :=
    fun i k j l => c i k * (a i j : ℂ) * (b k l : ℂ) * ((triPoly rc j p.1 : ℂ) * (triPoly hc l p.2 : ℂ)) with hX
  have h1 : ∀ i k, c i k * (∑ j, (a i j : ℂ) * (triPoly rc j p.1 : ℂ)) * (∑ l, (b k l : ℂ) * (triPoly hc l p.2 : ℂ))
      = ∑ j, ∑ l, X i k j l := by
    intro i k
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [hX]; ring
  have h2 : ∀ j l, (∑ i, ∑ k, c i k * (a i j : ℂ) * (b k l : ℂ)) * ((bas rc hc j l p : ℝ) : ℂ)
      = ∑ i, ∑ k, X i k j l := by
    intro j l
    simp only [bas, Complex.ofReal_mul, Finset.sum_mul, hX]
  simp only [e1, e2, h1, h2]
  calc ∑ i, ∑ k, ∑ j, ∑ l, X i k j l = ∑ i, ∑ j, ∑ l, ∑ k, X i k j l := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = ∑ j, ∑ l, ∑ i, ∑ k, X i k j l := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)

theorem sum_mem_poly {ι : Type} [Fintype ι] {d d' : ℕ} (e : ι → ℂ) (f : ι → ℝ × ℝ → ℂ)
    (hf : ∀ x, f x ∈ polyFnG d d') : (fun p => ∑ x, e x * f x p) ∈ polyFnG d d' := by
  choose c hc using hf
  refine ⟨fun j l => ∑ x, e x * c x j l, fun p => ?_⟩
  simp only [hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun x _ => ?_))
  ring

variable (rc hc : ℕ → ℕ → ℝ) (a₁ a₂ b₁ b₂ : ℝ) (lw : ℝ → ℝ)

theorem continuous_triPoly (co : ℕ → ℕ → ℝ) (j : ℕ) : Continuous (triPoly co j) := by
  unfold triPoly; fun_prop

theorem ortho2
    (hor : ∀ j j', ∫ r in Set.Icc a₁ a₂, lw r * triPoly rc j r * triPoly rc j' r = if j = j' then 1 else 0)
    (hoz : ∀ l l', ∫ z in Set.Icc b₁ b₂, triPoly hc l z * triPoly hc l' z = if l = l' then 1 else 0)
    (j l j' l' : ℕ) :
    ∫ p in Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, (lw p.1 : ℂ) * ((bas rc hc j l p : ℝ) : ℂ) * ((bas rc hc j' l' p : ℝ) : ℂ)
      = if j = j' ∧ l = l' then 1 else 0 := by
  have e : ∀ p : ℝ × ℝ, (lw p.1 : ℂ) * ((bas rc hc j l p : ℝ) : ℂ) * ((bas rc hc j' l' p : ℝ) : ℂ)
      = (((lw p.1 * triPoly rc j p.1 * triPoly rc j' p.1) * (triPoly hc l p.2 * triPoly hc l' p.2) : ℝ) : ℂ) := by
    intro p; simp only [bas]; push_cast; ring
  simp_rw [e]
  rw [integral_complex_ofReal, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_mul (f := fun r => lw r * triPoly rc j r * triPoly rc j' r)
      (g := fun z => triPoly hc l z * triPoly hc l' z), hor, hoz]
  split_ifs <;> simp_all

variable (rc hc : ℕ → ℕ → ℝ) (a₁ a₂ b₁ b₂ : ℝ) (lw : ℝ → ℝ)

def coefG (F : ℝ × ℝ → ℂ) (j l : ℕ) : ℂ :=
  ∫ p in Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, (lw p.1 : ℂ) * F p * ((bas rc hc j l p : ℝ) : ℂ)

theorem proj_eq (hr : ∀ j, rc j j ≠ 0) (hh : ∀ j, hc j j ≠ 0) (hlw : Continuous lw)
    (hor : ∀ j j', ∫ r in Set.Icc a₁ a₂, lw r * triPoly rc j r * triPoly rc j' r = if j = j' then 1 else 0)
    (hoz : ∀ l l', ∫ z in Set.Icc b₁ b₂, triPoly hc l z * triPoly hc l' z = if l = l' then 1 else 0)
    (Q : ℕ) (F : ℝ × ℝ → ℂ)
    (hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((lw p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)) :
    projG (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂) (fun p => lw p.1) Q Q F
      = fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), coefG rc hc a₁ a₂ b₁ b₂ lw F j l * ((bas rc hc j l p : ℝ) : ℂ) := by
  set S := Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂ with hS
  have hSc : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hcb : ∀ j l, Continuous (fun p : ℝ × ℝ => bas rc hc j l p) := by
    intro j l; unfold bas
    exact ((continuous_triPoly rc j).comp continuous_fst).mul ((continuous_triPoly hc l).comp continuous_snd)
  have hFb : ∀ j l, IntegrableOn (fun p => (lw p.1 : ℂ) * F p * ((bas rc hc j l p : ℝ) : ℂ)) S := by
    intro j l
    refine (hF (fun r => triPoly rc j r) (fun z => triPoly hc l z) (continuous_triPoly rc j)
      (continuous_triPoly hc l)).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [bas]; push_cast; ring
  have hbb : ∀ j l j' l', IntegrableOn
      (fun p => (lw p.1 : ℂ) * ((bas rc hc j' l' p : ℝ) : ℂ) * ((bas rc hc j l p : ℝ) : ℂ)) S := by
    intro j l j' l'
    refine ContinuousOn.integrableOn_compact hSc (Continuous.continuousOn ?_)
    have := hcb j l; have := hcb j' l'
    fun_prop
  have hinner : ∀ e : Fin (Q + 1) → Fin (Q + 1) → ℂ, ∀ j l : Fin (Q + 1),
      ∫ p in S, (lw p.1 : ℂ) * (∑ j' : Fin (Q + 1), ∑ l' : Fin (Q + 1), e j' l' * ((bas rc hc j' l' p : ℝ) : ℂ))
        * ((bas rc hc j l p : ℝ) : ℂ) = e j l := by
    intro e j l
    have h1 : ∀ p : ℝ × ℝ, (lw p.1 : ℂ) * (∑ j' : Fin (Q + 1), ∑ l' : Fin (Q + 1), e j' l' * ((bas rc hc j' l' p : ℝ) : ℂ))
        * ((bas rc hc j l p : ℝ) : ℂ) = ∑ j' : Fin (Q + 1), ∑ l' : Fin (Q + 1),
          e j' l' * ((lw p.1 : ℂ) * ((bas rc hc j' l' p : ℝ) : ℂ) * ((bas rc hc j l p : ℝ) : ℂ)) := by
      intro p; simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    simp_rw [h1]
    rw [integral_finsetSum]
    swap
    · intro j' _; exact integrable_finsetSum _ (fun l' _ => (hbb j l j' l').const_mul _)
    have h2 : ∀ j' : Fin (Q + 1), ∫ p in S, ∑ l' : Fin (Q + 1),
        e j' l' * ((lw p.1 : ℂ) * ((bas rc hc j' l' p : ℝ) : ℂ) * ((bas rc hc j l p : ℝ) : ℂ))
        = ∑ l' : Fin (Q + 1), e j' l' * (if (j' : ℕ) = j ∧ (l' : ℕ) = l then 1 else 0) := by
      intro j'
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl (fun l' _ => ?_)
        rw [integral_const_mul, ortho2 rc hc a₁ a₂ b₁ b₂ lw hor hoz]
      · intro l' _; exact (hbb j l j' l').const_mul _
    simp_rw [h2]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [Fin.val_eq_val, hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero (fun l' _ => ?_)
      simp [Fin.val_eq_val, hb]
    · simp
  have hpair : ∀ f : ℝ × ℝ → ℂ, (∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => (lw p.1 : ℂ) * f p * ((bas rc hc j l p : ℝ) : ℂ)) S) →
      ∀ e : Fin (Q + 1) → Fin (Q + 1) → ℂ,
      pairOnG S (fun p => lw p.1) f (fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((bas rc hc j l p : ℝ) : ℂ))
        = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), (starRingEnd ℂ) (e j l) *
          ∫ p in S, (lw p.1 : ℂ) * f p * ((bas rc hc j l p : ℝ) : ℂ) := by
    intro f hf e
    unfold pairOnG
    have h1 : ∀ p : ℝ × ℝ, ((lw p.1 : ℝ) : ℂ) * f p * (starRingEnd ℂ)
        (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((bas rc hc j l p : ℝ) : ℂ))
        = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), (starRingEnd ℂ) (e j l) *
          ((lw p.1 : ℂ) * f p * ((bas rc hc j l p : ℝ) : ℂ)) := by
      intro p
      simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    simp_rw [h1]
    rw [integral_finsetSum]
    swap
    · intro j _; exact integrable_finsetSum _ (fun l _ => (hf j l).const_mul _)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [integral_const_mul]
    · intro l _; exact (hf j l).const_mul _
  set P : ℝ × ℝ → ℂ := fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
    coefG rc hc a₁ a₂ b₁ b₂ lw F j l * ((bas rc hc j l p : ℝ) : ℂ) with hP
  have hPmem : P ∈ polyFnG Q Q := by
    have := sum_mem_poly (d := Q) (d' := Q) (fun x : Fin (Q + 1) × Fin (Q + 1) => coefG rc hc a₁ a₂ b₁ b₂ lw F x.1 x.2)
      (fun x p => ((bas rc hc x.1 x.2 p : ℝ) : ℂ)) (fun x => bas_mem rc hc (by omega) (by omega))
    simpa only [hP, Fintype.sum_prod_type] using this
  have hPb : ∀ j l : Fin (Q + 1), IntegrableOn (fun p => (lw p.1 : ℂ) * P p * ((bas rc hc j l p : ℝ) : ℂ)) S := by
    intro j l
    refine ContinuousOn.integrableOn_compact hSc (Continuous.continuousOn ?_)
    have := hcb j l
    have : Continuous P := by
      simp only [hP]
      refine continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun l _ => ?_))
      have := hcb j l
      fun_prop
    fun_prop
  have hsubF : ∀ g : ℝ × ℝ → ℂ, (∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => (lw p.1 : ℂ) * g p * ((bas rc hc j l p : ℝ) : ℂ)) S) → ∀ j l : Fin (Q + 1),
      ∫ p in S, (lw p.1 : ℂ) * (F p - g p) * ((bas rc hc j l p : ℝ) : ℂ)
        = coefG rc hc a₁ a₂ b₁ b₂ lw F j l - ∫ p in S, (lw p.1 : ℂ) * g p * ((bas rc hc j l p : ℝ) : ℂ) := by
    intro g hg j l
    rw [coefG, ← integral_sub (hFb j l) (hg j l)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    ring
  have hsubI : ∀ g : ℝ × ℝ → ℂ, (∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => (lw p.1 : ℂ) * g p * ((bas rc hc j l p : ℝ) : ℂ)) S) → ∀ j l : Fin (Q + 1),
      IntegrableOn (fun p => (lw p.1 : ℂ) * (F p - g p) * ((bas rc hc j l p : ℝ) : ℂ)) S := by
    intro g hg j l
    refine ((hFb j l).sub (hg j l)).congr_fun (fun p _ => by simp only [Pi.sub_apply]; ring)
      (measurableSet_Icc.prod measurableSet_Icc)
  have horth : ∀ T ∈ polyFnG Q Q, pairOnG S (fun p => lw p.1) (fun p => F p - P p) T = 0 := by
    intro T hT
    obtain ⟨e, he⟩ := span_mem rc hc hr hh hT
    have hT' : T = fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((bas rc hc j l p : ℝ) : ℂ) := funext he
    rw [hT', hpair _ (hsubI P hPb) e]
    refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun l _ => ?_))
    rw [hsubF P hPb j l, hP, hinner]
    simp
  have hex : ∃ P' ∈ polyFnG Q Q, ∀ T ∈ polyFnG Q Q, pairOnG S (fun p => lw p.1) (fun p => F p - P' p) T = 0 :=
    ⟨P, hPmem, horth⟩
  unfold projG
  rw [dif_pos hex]
  obtain ⟨hmem, hort⟩ := hex.choose_spec
  obtain ⟨e, he⟩ := span_mem rc hc hr hh hmem
  have hchoose : hex.choose = fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((bas rc hc j l p : ℝ) : ℂ) :=
    funext he
  have hcb' : ∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => (lw p.1 : ℂ) * hex.choose p * ((bas rc hc j l p : ℝ) : ℂ)) S := by
    intro j l
    rw [hchoose]
    refine ContinuousOn.integrableOn_compact hSc (Continuous.continuousOn ?_)
    have := hcb j l
    have : Continuous (fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((bas rc hc j l p : ℝ) : ℂ)) := by
      refine continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun l _ => ?_))
      have := hcb j l
      fun_prop
    fun_prop
  have hej : ∀ j l : Fin (Q + 1), e j l = coefG rc hc a₁ a₂ b₁ b₂ lw F j l := by
    intro j l
    have h0 := hort (fun p => ((bas rc hc j l p : ℝ) : ℂ)) (bas_mem rc hc (by omega) (by omega))
    have h0' : ∫ p in S, (lw p.1 : ℂ) * (F p - hex.choose p) * ((bas rc hc j l p : ℝ) : ℂ) = 0 := by
      refine Eq.trans ?_ h0
      unfold pairOnG
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp [Complex.conj_ofReal]
    rw [hsubF _ hcb' j l, hchoose, hinner] at h0'
    have h0 := h0'
    exact (sub_eq_zero.mp h0).symm
  rw [hchoose]
  funext p
  simp only [hej]
  rfl

theorem orth_gen (hr : ∀ j, rc j j ≠ 0) (hh : ∀ j, hc j j ≠ 0) (hlw : Continuous lw)
    (hor : ∀ j j', ∫ r in Set.Icc a₁ a₂, lw r * triPoly rc j r * triPoly rc j' r = if j = j' then 1 else 0)
    (hoz : ∀ l l', ∫ z in Set.Icc b₁ b₂, triPoly hc l z * triPoly hc l' z = if l = l' then 1 else 0)
    (Q : ℕ) (F : ℝ × ℝ → ℂ)
    (hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((lw p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)) :
    ∀ T ∈ polyFnG Q Q, pairOnG (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂) (fun p => lw p.1)
      (fun p => F p - ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), coefG rc hc a₁ a₂ b₁ b₂ lw F j l * ((bas rc hc j l p : ℝ) : ℂ)) T = 0 := by
  set S := Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂ with hS
  have hSc : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hcb : ∀ j l, Continuous (fun p : ℝ × ℝ => bas rc hc j l p) := by
    intro j l; unfold bas
    exact ((continuous_triPoly rc j).comp continuous_fst).mul ((continuous_triPoly hc l).comp continuous_snd)
  have hFb : ∀ j l, IntegrableOn (fun p => (lw p.1 : ℂ) * F p * ((bas rc hc j l p : ℝ) : ℂ)) S := by
    intro j l
    refine (hF (fun r => triPoly rc j r) (fun z => triPoly hc l z) (continuous_triPoly rc j)
      (continuous_triPoly hc l)).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [bas]; push_cast; ring
  have hbb : ∀ j l j' l', IntegrableOn
      (fun p => (lw p.1 : ℂ) * ((bas rc hc j' l' p : ℝ) : ℂ) * ((bas rc hc j l p : ℝ) : ℂ)) S := by
    intro j l j' l'
    refine ContinuousOn.integrableOn_compact hSc (Continuous.continuousOn ?_)
    have := hcb j l; have := hcb j' l'
    fun_prop
  have hinner : ∀ e : Fin (Q + 1) → Fin (Q + 1) → ℂ, ∀ j l : Fin (Q + 1),
      ∫ p in S, (lw p.1 : ℂ) * (∑ j' : Fin (Q + 1), ∑ l' : Fin (Q + 1), e j' l' * ((bas rc hc j' l' p : ℝ) : ℂ))
        * ((bas rc hc j l p : ℝ) : ℂ) = e j l := by
    intro e j l
    have h1 : ∀ p : ℝ × ℝ, (lw p.1 : ℂ) * (∑ j' : Fin (Q + 1), ∑ l' : Fin (Q + 1), e j' l' * ((bas rc hc j' l' p : ℝ) : ℂ))
        * ((bas rc hc j l p : ℝ) : ℂ) = ∑ j' : Fin (Q + 1), ∑ l' : Fin (Q + 1),
          e j' l' * ((lw p.1 : ℂ) * ((bas rc hc j' l' p : ℝ) : ℂ) * ((bas rc hc j l p : ℝ) : ℂ)) := by
      intro p; simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    simp_rw [h1]
    rw [integral_finsetSum]
    swap
    · intro j' _; exact integrable_finsetSum _ (fun l' _ => (hbb j l j' l').const_mul _)
    have h2 : ∀ j' : Fin (Q + 1), ∫ p in S, ∑ l' : Fin (Q + 1),
        e j' l' * ((lw p.1 : ℂ) * ((bas rc hc j' l' p : ℝ) : ℂ) * ((bas rc hc j l p : ℝ) : ℂ))
        = ∑ l' : Fin (Q + 1), e j' l' * (if (j' : ℕ) = j ∧ (l' : ℕ) = l then 1 else 0) := by
      intro j'
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl (fun l' _ => ?_)
        rw [integral_const_mul, ortho2 rc hc a₁ a₂ b₁ b₂ lw hor hoz]
      · intro l' _; exact (hbb j l j' l').const_mul _
    simp_rw [h2]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [Fin.val_eq_val, hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero (fun l' _ => ?_)
      simp [Fin.val_eq_val, hb]
    · simp
  have hpair : ∀ f : ℝ × ℝ → ℂ, (∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => (lw p.1 : ℂ) * f p * ((bas rc hc j l p : ℝ) : ℂ)) S) →
      ∀ e : Fin (Q + 1) → Fin (Q + 1) → ℂ,
      pairOnG S (fun p => lw p.1) f (fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((bas rc hc j l p : ℝ) : ℂ))
        = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), (starRingEnd ℂ) (e j l) *
          ∫ p in S, (lw p.1 : ℂ) * f p * ((bas rc hc j l p : ℝ) : ℂ) := by
    intro f hf e
    unfold pairOnG
    have h1 : ∀ p : ℝ × ℝ, ((lw p.1 : ℝ) : ℂ) * f p * (starRingEnd ℂ)
        (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((bas rc hc j l p : ℝ) : ℂ))
        = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), (starRingEnd ℂ) (e j l) *
          ((lw p.1 : ℂ) * f p * ((bas rc hc j l p : ℝ) : ℂ)) := by
      intro p
      simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    simp_rw [h1]
    rw [integral_finsetSum]
    swap
    · intro j _; exact integrable_finsetSum _ (fun l _ => (hf j l).const_mul _)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [integral_const_mul]
    · intro l _; exact (hf j l).const_mul _
  set P : ℝ × ℝ → ℂ := fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
    coefG rc hc a₁ a₂ b₁ b₂ lw F j l * ((bas rc hc j l p : ℝ) : ℂ) with hP
  have hPmem : P ∈ polyFnG Q Q := by
    have := sum_mem_poly (d := Q) (d' := Q) (fun x : Fin (Q + 1) × Fin (Q + 1) => coefG rc hc a₁ a₂ b₁ b₂ lw F x.1 x.2)
      (fun x p => ((bas rc hc x.1 x.2 p : ℝ) : ℂ)) (fun x => bas_mem rc hc (by omega) (by omega))
    simpa only [hP, Fintype.sum_prod_type] using this
  have hPb : ∀ j l : Fin (Q + 1), IntegrableOn (fun p => (lw p.1 : ℂ) * P p * ((bas rc hc j l p : ℝ) : ℂ)) S := by
    intro j l
    refine ContinuousOn.integrableOn_compact hSc (Continuous.continuousOn ?_)
    have := hcb j l
    have : Continuous P := by
      simp only [hP]
      refine continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun l _ => ?_))
      have := hcb j l
      fun_prop
    fun_prop
  have hsubF : ∀ g : ℝ × ℝ → ℂ, (∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => (lw p.1 : ℂ) * g p * ((bas rc hc j l p : ℝ) : ℂ)) S) → ∀ j l : Fin (Q + 1),
      ∫ p in S, (lw p.1 : ℂ) * (F p - g p) * ((bas rc hc j l p : ℝ) : ℂ)
        = coefG rc hc a₁ a₂ b₁ b₂ lw F j l - ∫ p in S, (lw p.1 : ℂ) * g p * ((bas rc hc j l p : ℝ) : ℂ) := by
    intro g hg j l
    rw [coefG, ← integral_sub (hFb j l) (hg j l)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    ring
  have hsubI : ∀ g : ℝ × ℝ → ℂ, (∀ j l : Fin (Q + 1), IntegrableOn
      (fun p => (lw p.1 : ℂ) * g p * ((bas rc hc j l p : ℝ) : ℂ)) S) → ∀ j l : Fin (Q + 1),
      IntegrableOn (fun p => (lw p.1 : ℂ) * (F p - g p) * ((bas rc hc j l p : ℝ) : ℂ)) S := by
    intro g hg j l
    refine ((hFb j l).sub (hg j l)).congr_fun (fun p _ => by simp only [Pi.sub_apply]; ring)
      (measurableSet_Icc.prod measurableSet_Icc)
  have horth : ∀ T ∈ polyFnG Q Q, pairOnG S (fun p => lw p.1) (fun p => F p - P p) T = 0 := by
    intro T hT
    obtain ⟨e, he⟩ := span_mem rc hc hr hh hT
    have hT' : T = fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), e j l * ((bas rc hc j l p : ℝ) : ℂ) := funext he
    rw [hT', hpair _ (hsubI P hPb) e]
    refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun l _ => ?_))
    rw [hsubF P hPb j l, hP, hinner]
    simp
  exact horth

theorem continuous_lineWeight (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem proj_eq_basis (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q : ℕ) (F : ℝ × ℝ → ℂ)
    (hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect) :
    K.proj Q Q F = fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), B.coef K F j l * ((basisFn B j l p : ℝ) : ℂ) :=
  proj_eq B.radialCoef B.heightCoef K.r₁ K.r₂ K.z₁ K.z₂ K.lineWeight (fun j => (hB.radial_leading j).ne')
    (fun j => (hB.height_leading j).ne') (continuous_lineWeight K) hB.radial_orthonormal hB.height_orthonormal Q F hF

theorem proj_orth (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q : ℕ) (F : ℝ × ℝ → ℂ)
    (hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect)
    (T : ℝ × ℝ → ℂ) (hT : T ∈ polyFn Q Q) :
    K.pairOn K.lineWeightFn
      (fun p => F p - ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), B.coef K F j l * ((basisFn B j l p : ℝ) : ℂ)) T = 0 :=
  orth_gen B.radialCoef B.heightCoef K.r₁ K.r₂ K.z₁ K.z₂ K.lineWeight (fun j => (hB.radial_leading j).ne')
    (fun j => (hB.height_leading j).ne') (continuous_lineWeight K) hB.radial_orthonormal hB.height_orthonormal Q F hF T hT

end Breakdown.CellCert.CellEnergy.HeightProj
