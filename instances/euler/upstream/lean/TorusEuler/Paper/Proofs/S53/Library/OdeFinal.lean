import TorusEuler.Paper.Proofs.S53.Library.OdeIdx

/-!
# S53 library: the weighted word recurrence of the linear ODE from Lemma D.3

`odeWordBound_of_D3` derives `OdeWordBound` (a monotone nonnegative amplification factor `Φ N q` for
all derivative words of order `≤ N` of the solution of `x' = A x + f`, TeX 06c_finite_hierarchy.tex
(5.18)-(5.23)) from `Statement.lemma_D_3`: for a word `w` the finitely many directions
`d (w_0), …, d (w_{k-1})` are the letters of `Idx = Fin k`, and the sorted word `0 … k-1` is the
admissible word that reads off `∂^w`.
-/

open Set
open scoped ContDiff


namespace TorusEuler.Paper.Lib.S53

noncomputable section

open TorusEuler

/-- Auxiliary fact `phaseOperatorWord_map` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem phaseOperatorWord_map {Idx ι P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ι → P) (σ : Idx → ι) (v : List Idx)
    (f : P → E) :
    phaseOperatorWord (fun i _ => d (σ i)) v f = phaseOperatorWord (fun j _ => d j) (v.map σ) f := by
  induction v with
  | nil => rfl
  | cons i v ih =>
    simp only [phaseOperatorWord, List.map_cons, ih]

/-- Lemma D.3 gives the weighted derivative recurrence of the linear ODE. -/
theorem odeWordBound_of_D3 (hD3 : Statement.lemma_D_3) : OdeWordBound := by
  classical
  choose Cn hCn0 hCn using fun (k j : ℕ) => odeIdx hD3 (Fin k) k (j : ℝ)
  let W : ℕ → ℝ := fun k => ((hierarchyAdmissibleWords (Fin k) k).card : ℝ)
  have hW0 : ∀ k, 0 ≤ W k := fun k => Nat.cast_nonneg _
  let Ψ : ℕ → ℕ → ℝ := fun k m => ∑ j ∈ Finset.range (m + 1), Cn k j
  have hΨ0 : ∀ k m, 0 ≤ Ψ k m := fun k m => Finset.sum_nonneg fun j _ => hCn0 k j
  have hΨm : ∀ k {m m' : ℕ}, m ≤ m' → Ψ k m ≤ Ψ k m' := fun k m m' h =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => hCn0 k j)
  let Φ : ℕ → ℝ → ℝ := fun N q => ∑ k ∈ Finset.range (N + 1), W k * Ψ k ⌈q * W k⌉₊
  refine ⟨Φ, fun {q} hq N => ?_, fun {q r} hq hqr N => ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (hW0 k) (hΨ0 k _)
  · refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hΨm k ?_) (hW0 k)
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_right hqr (hW0 k))
  intro ι P E _ _ _ _ _ _ d N A f x g dg S l r K C B H hlr hK hC hB hH hA hf hx hxt hg0 hg hdg
    hStable hinit hsource hcoeff w hw p hp u hu
  set k := w.length with hk
  let D : OdeData (Fin k) P E :=
    { d := fun i => d (w.get i), A := A, f := f, x := x, g := g, dg := dg, l := l, r := r, K := K,
      p := p, hlr := hlr, hA := hA, hf := hf, hx := hx, hxt := hxt, hg0 := hg0, hg := hg,
      hdg := hdg, hStable := hStable p hp }
  have hjet : ∀ (v : List (Fin k)) (F : P → E),
      phaseOperatorWord (fun i _ => D.d i) v F = phaseOperatorWord (fun j _ => d j) (v.map w.get) F :=
    fun v F => phaseOperatorWord_map d w.get v F
  have hjetA : ∀ (v : List (Fin k)) (F : P → E →L[ℝ] E),
      phaseOperatorWord (fun i _ => D.d i) v F = phaseOperatorWord (fun j _ => d j) (v.map w.get) F :=
    fun v F => phaseOperatorWord_map d w.get v F
  have hmapl : ∀ v : List (Fin k), (v.map w.get).length = v.length := fun v => by simp
  set q := K * (r - l) * C with hq
  set j := ⌈q * W k⌉₊ with hj
  have hspec := hCn k j D (C := C) (B := B) (H := H) hK hC
    (fun v hv => by
      rw [hjet]
      exact hinit _ ((hmapl v).trans_le (hv.trans (hw))) p hp)
    (fun v hv t ht => by
      rw [hjet]
      exact hsource _ ((hmapl v).trans_le (hv.trans (hw))) p hp t ht)
    (fun v hv hv0 t ht => by
      rw [hjetA]
      exact hcoeff _ ((hmapl v).trans_le (hv.trans (hw))) (by simpa using hv0) p hp t ht)
    (by
      calc D.K * (D.r - D.l) * C * ((hierarchyAdmissibleWords (Fin k) k).card : ℝ)
          = q * W k := rfl
        _ ≤ (j : ℝ) := Nat.le_ceil _)
  have hmem : List.finRange k ∈ hierarchyAdmissibleWords (Fin k) k :=
    mem_hierarchyAdmissibleWords.mpr ⟨by simp, List.pairwise_le_finRange k⟩
  have h1 := hspec (List.finRange k) hmem u hu
  have hword : (List.finRange k).map w.get = w := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_get w
  change ‖phaseOperatorWord (fun i _ => D.d i) (List.finRange k) (x u) p‖ / g u ≤ _ at h1
  rw [hjet, hword] at h1
  refine h1.trans ?_
  have hKB : 0 ≤ K * (B + (r - l) * H) := by
    have : 0 ≤ r - l := sub_nonneg.mpr hlr.le
    positivity
  have hterm : Cn k j * W k ≤ Φ N q := by
    have hle : Cn k j ≤ Ψ k j :=
      Finset.single_le_sum (f := fun i => Cn k i) (fun i _ => hCn0 k i)
        (Finset.mem_range.mpr (Nat.lt_succ_self j))
    have hkN : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hw)
    calc Cn k j * W k ≤ Ψ k j * W k := mul_le_mul_of_nonneg_right hle (hW0 k)
      _ = W k * Ψ k ⌈q * W k⌉₊ := by rw [mul_comm]
      _ ≤ Φ N q :=
        Finset.single_le_sum (f := fun i => W i * Ψ i ⌈q * W i⌉₊)
          (fun i _ => mul_nonneg (hW0 i) (hΨ0 i _)) hkN
  calc Cn k j * W k * D.K * (B + (D.r - D.l) * H) = (Cn k j * W k) * (K * (B + (r - l) * H)) := by
        change Cn k j * W k * K * (B + (r - l) * H) = _; ring
    _ ≤ Φ N q * (K * (B + (r - l) * H)) := mul_le_mul_of_nonneg_right hterm hKB

end

end TorusEuler.Paper.Lib.S53
