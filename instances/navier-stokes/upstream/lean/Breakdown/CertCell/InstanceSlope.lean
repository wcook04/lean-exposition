import Breakdown.CertCell.InstanceStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.GivenFields

namespace Internal.Slope

private theorem glue_slopeBound (lo hi M : ℝ) :
    ∀ (m : List ℝ), m.Pairwise (· < ·) → ∀ (g : ℕ → ℝ → ℝ),
      (∀ k ≤ m.length, ∀ u ∈ Set.Icc lo hi, ∀ v ∈ Set.Icc lo hi, |g k u - g k v| ≤ M * |u - v|) →
      (∀ k (hk : k < m.length), g k m[k] = g (k + 1) m[k]) →
      ∀ u ∈ Set.Icc lo hi, ∀ v ∈ Set.Icc lo hi,
        |g ((m.filter (fun b => decide (b ≤ u))).length) u -
          g ((m.filter (fun b => decide (b ≤ v))).length) v| ≤ M * |u - v|
  | [], _, g, hg, _ => by
    intro u hu v hv
    simpa using hg 0 le_rfl u hu v hv
  | b :: m', hm, g, hg, hj => by
    rw [List.pairwise_cons] at hm
    have ih := glue_slopeBound lo hi M m' hm.2 (fun k => g (k + 1))
      (fun k hk => hg (k + 1) (by simp; omega))
      (fun k hk => hj (k + 1) (by simp; omega))
    have hnil : ∀ z, z ≤ b → m'.filter (fun c => decide (c ≤ z)) = [] := by
      intro z hz
      rw [List.filter_eq_nil_iff]
      intro c hc
      have := hm.1 c hc
      simp only [decide_eq_true_eq, not_le]
      linarith
    have e : ∀ z, g (((b :: m').filter (fun c => decide (c ≤ z))).length) z =
        if b ≤ z then g ((m'.filter (fun c => decide (c ≤ z))).length + 1) z else g 0 z := by
      intro z
      by_cases h : b ≤ z
      · simp [h]
      · simp [h, hnil z (le_of_lt (not_le.1 h))]
    have hjb : g ((m'.filter (fun c => decide (c ≤ b))).length + 1) b = g 0 b := by
      rw [hnil b le_rfl]
      have := hj 0 (by simp)
      simpa using this.symm
    have cross : ∀ u ∈ Set.Icc lo hi, ∀ v ∈ Set.Icc lo hi, b ≤ u → v < b →
        |g ((m'.filter (fun c => decide (c ≤ u))).length + 1) u - g 0 v| ≤ M * |u - v| := by
      intro u hu v hv hbu hvb
      have hb : b ∈ Set.Icc lo hi := ⟨by linarith [hv.1], by linarith [hu.2]⟩
      have h1 := ih u hu b hb
      have h2 := hg 0 (Nat.zero_le _) b hb v hv
      rw [hjb] at h1
      calc _ ≤ |g ((m'.filter (fun c => decide (c ≤ u))).length + 1) u - g 0 b| + |g 0 b - g 0 v| :=
            abs_sub_le _ _ _
        _ ≤ M * |u - b| + M * |b - v| := add_le_add h1 h2
        _ = M * |u - v| := by
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - b), abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - v),
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - v)]
          ring
    intro u hu v hv
    rw [e u, e v]
    split_ifs with h1 h2 h2
    · exact ih u hu v hv
    · exact cross u hu v hv h1 (not_le.1 h2)
    · rw [abs_sub_comm, abs_sub_comm u]
      exact cross v hv u hu h2 (not_le.1 h1)
    · exact hg 0 (Nat.zero_le _) u hu v hv

private theorem eval_first (c : ℂ) (Q : MvPolynomial (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (atFirst c Q) = MvPolynomial.eval ![c, v 1] Q := by
  unfold atFirst
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) v _ = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ _
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 2
  funext k
  fin_cases k <;> simp

private theorem eval_second (c : ℂ) (Q : MvPolynomial (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (atSecond c Q) = MvPolynomial.eval ![v 0, c] Q := by
  unfold atSecond
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) v _ = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ _
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 2
  funext k
  fin_cases k <;> simp

private theorem poly_bound (Q : MvPolynomial (Fin 2) ℂ) : ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
    ∀ v w : Fin 2 → ℂ, (∀ i, ‖v i‖ ≤ 1) → (∀ i, ‖w i‖ ≤ 1) →
      ‖MvPolynomial.eval v Q‖ ≤ B ∧
      ‖MvPolynomial.eval v Q - MvPolynomial.eval w Q‖ ≤ K * (‖v 0 - w 0‖ + ‖v 1 - w 1‖) := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨0, ‖a‖, le_rfl, norm_nonneg _, fun v w _ _ => ⟨by simp, by simp⟩⟩
  | add p q hp hq =>
    obtain ⟨K1, B1, hK1, hB1, h1⟩ := hp
    obtain ⟨K2, B2, hK2, hB2, h2⟩ := hq
    refine ⟨K1 + K2, B1 + B2, by positivity, by positivity, fun v w hv hw => ?_⟩
    obtain ⟨a1, b1⟩ := h1 v w hv hw
    obtain ⟨a2, b2⟩ := h2 v w hv hw
    simp only [map_add]
    constructor
    · exact (norm_add_le _ _).trans (add_le_add a1 a2)
    · calc _ = ‖(MvPolynomial.eval v p - MvPolynomial.eval w p) +
            (MvPolynomial.eval v q - MvPolynomial.eval w q)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := add_le_add b1 b2
        _ = _ := by ring
  | mul_X p n hp =>
    obtain ⟨K, B, hK, hB, h⟩ := hp
    refine ⟨K + B, B, by positivity, hB, fun v w hv hw => ?_⟩
    obtain ⟨a, b⟩ := h v w hv hw
    have aw := (h w w hw hw).1
    simp only [map_mul, MvPolynomial.eval_X]
    have hd : ‖v n - w n‖ ≤ ‖v 0 - w 0‖ + ‖v 1 - w 1‖ := by
      fin_cases n
      · exact le_add_of_nonneg_right (norm_nonneg _)
      · exact le_add_of_nonneg_left (norm_nonneg _)
    have hD : 0 ≤ ‖v 0 - w 0‖ + ‖v 1 - w 1‖ := by positivity
    constructor
    · rw [norm_mul]
      calc _ ≤ B * 1 := mul_le_mul a (hv n) (norm_nonneg _) hB
        _ = B := mul_one B
    · calc ‖MvPolynomial.eval v p * v n - MvPolynomial.eval w p * w n‖
          = ‖(MvPolynomial.eval v p - MvPolynomial.eval w p) * v n + MvPolynomial.eval w p * (v n - w n)‖ := by
            ring_nf
        _ ≤ ‖MvPolynomial.eval v p - MvPolynomial.eval w p‖ * ‖v n‖ +
            ‖MvPolynomial.eval w p‖ * ‖v n - w n‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ (K * (‖v 0 - w 0‖ + ‖v 1 - w 1‖)) * 1 + B * (‖v 0 - w 0‖ + ‖v 1 - w 1‖) := by
            gcongr
            · exact hv n
        _ = (K + B) * (‖v 0 - w 0‖ + ‖v 1 - w 1‖) := by ring

private theorem vec_norm_le {t x : ℝ} (ht : |t| ≤ 1) (hx : |x| ≤ 1) :
    ∀ i, ‖(![(t : ℂ), (x : ℂ)] : Fin 2 → ℂ) i‖ ≤ 1 := by
  intro i
  fin_cases i
  · simpa [Complex.norm_real] using ht
  · simpa [Complex.norm_real] using hx

private theorem vec_dist (t x t' x' : ℝ) :
    ‖(![(t : ℂ), (x : ℂ)] : Fin 2 → ℂ) 0 - (![(t' : ℂ), (x' : ℂ)] : Fin 2 → ℂ) 0‖ +
      ‖(![(t : ℂ), (x : ℂ)] : Fin 2 → ℂ) 1 - (![(t' : ℂ), (x' : ℂ)] : Fin 2 → ℂ) 1‖ = |t - t'| + |x - x'| := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

private theorem poly_slopeBound (Q : MvPolynomial (Fin 2) ℂ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t t' x x' : ℝ,
    |t| ≤ 1 → |t'| ≤ 1 → |x| ≤ 1 → |x'| ≤ 1 →
      |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] Q).re - (MvPolynomial.eval ![(t' : ℂ), (x' : ℂ)] Q).re| ≤
        K * (|t - t'| + |x - x'|) := by
  obtain ⟨K, B, hK, _, h⟩ := poly_bound Q
  refine ⟨K, hK, fun t t' x x' ht ht' hx hx' => ?_⟩
  have hd := (h _ _ (vec_norm_le ht hx) (vec_norm_le ht' hx')).2
  rw [vec_dist] at hd
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans hd

private theorem split_first (Q : MvPolynomial (Fin 2) ℂ) :
    ∃ R, Q = atFirst 0 Q + MvPolynomial.X 0 * R := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    unfold atFirst
    rw [MvPolynomial.bind₁_C_right]
    ring
  | add p q hp hq =>
    obtain ⟨R1, h1⟩ := hp
    obtain ⟨R2, h2⟩ := hq
    refine ⟨R1 + R2, ?_⟩
    have hadd : atFirst 0 (p + q) = atFirst 0 p + atFirst 0 q := by
      unfold atFirst
      exact map_add _ _ _
    rw [hadd]
    linear_combination h1 + h2
  | mul_X p n hp =>
    obtain ⟨R1, h1⟩ := hp
    have hmul : atFirst 0 (p * MvPolynomial.X n) =
        atFirst 0 p * (if n = 0 then MvPolynomial.C 0 else MvPolynomial.X 1) := by
      unfold atFirst
      rw [map_mul, MvPolynomial.bind₁_X_right]
    rw [hmul]
    obtain rfl | rfl : n = 0 ∨ n = 1 := by fin_cases n <;> simp
    · refine ⟨p, ?_⟩
      simp
      ring
    · refine ⟨R1 * MvPolynomial.X 1, ?_⟩
      simp only [one_ne_zero, if_false]
      linear_combination (MvPolynomial.X 1) * h1

private theorem flat_slope (Q : MvPolynomial (Fin 2) ℂ) (v : ℂ) (hQ : atFirst 0 Q = MvPolynomial.C v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t x x' : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 → |x'| ≤ 1 →
      |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] Q).re - (MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] Q).re| ≤
        K * t * |x - x'| := by
  obtain ⟨R, hR⟩ := split_first Q
  rw [hQ] at hR
  obtain ⟨K, B, hK, _, h⟩ := poly_bound R
  refine ⟨K, hK, fun t x x' ht0 ht1 hx hx' => ?_⟩
  have htt : |t| ≤ 1 := abs_le.2 ⟨by linarith, ht1⟩
  have hd := (h _ _ (vec_norm_le htt hx) (vec_norm_le htt hx')).2
  rw [vec_dist, sub_self, abs_zero, zero_add] at hd
  have e : ∀ s : ℝ, MvPolynomial.eval ![(t : ℂ), (s : ℂ)] Q =
      v + (t : ℂ) * MvPolynomial.eval ![(t : ℂ), (s : ℂ)] R := by
    intro s
    conv_lhs => rw [hR]
    simp
  rw [e x, e x', ← Complex.sub_re]
  calc _ = |((t : ℂ) * (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] R -
        MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] R)).re| := by
        congr 2
        ring
    _ ≤ ‖(t : ℂ) * (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] R -
        MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] R)‖ := Complex.abs_re_le_norm _
    _ = t * ‖MvPolynomial.eval ![(t : ℂ), (x : ℂ)] R - MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] R‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    _ ≤ t * (K * |x - x'|) := mul_le_mul_of_nonneg_left hd ht0
    _ = K * t * |x - x'| := by ring

private theorem interior_pw (l : List ℝ) (hs : l.Pairwise (· < ·)) : ((l.drop 1).dropLast).Pairwise (· < ·) :=
  hs.sublist ((List.dropLast_sublist _).trans (List.drop_sublist _ _))

private theorem interior_pos (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    ∀ b ∈ (l.drop 1).dropLast, 0 < b := by
  cases l with
  | nil => simp at h0
  | cons a r =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    intro b hb
    simp only [List.drop_succ_cons, List.drop_zero] at hb
    exact (List.pairwise_cons.1 hs).1 b ((List.dropLast_sublist r).subset hb)

private theorem two_le_length (l : List ℝ) (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) :
    2 ≤ l.length := by
  match l, h0, h1 with
  | [], h0, _ => simp at h0
  | [a], h0, h1 => simp at h0 h1; linarith
  | _ :: _ :: _, _, _ => simp

private theorem interior_len (l : List ℝ) : ((l.drop 1).dropLast).length = cellCount l - 1 := by
  simp [cellCount, List.length_dropLast]

private theorem interior_get (l : List ℝ) (k : ℕ) (hk : k < ((l.drop 1).dropLast).length) :
    ((l.drop 1).dropLast)[k] = l.getD (k + 1) 0 := by
  have hk' : k + 1 < l.length := by
    simp [List.length_dropLast] at hk
    omega
  rw [List.getElem_dropLast, List.getElem_drop, List.getD_eq_getElem _ _ hk']
  congr 1
  omega

private theorem index_lt (l : List ℝ) (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) (u : ℝ) :
    cellIndex l u < cellCount l := by
  have h2 := two_le_length l h0 h1
  have := List.length_filter_le (fun b => decide (b ≤ u)) ((l.drop 1).dropLast)
  rw [interior_len] at this
  unfold cellIndex
  unfold cellCount at this ⊢
  omega

private theorem count_pos (l : List ℝ) (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) :
    1 ≤ cellCount l := by
  have h2 := two_le_length l h0 h1
  unfold cellCount
  omega

private theorem index_zero (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    cellIndex l 0 = 0 := by
  unfold cellIndex
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro b hb
  have := interior_pos l hs h0 b hb
  simp only [decide_eq_true_eq, not_le]
  exact this

private theorem list_pos_min : ∀ (r : List ℝ), (∀ b ∈ r, 0 < b) → ∃ δ, 0 < δ ∧ ∀ b ∈ r, δ ≤ b
  | [], _ => ⟨1, one_pos, fun b hb => by simp at hb⟩
  | a :: r, h => by
    obtain ⟨δ, hδ, hr⟩ := list_pos_min r (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨min a δ, lt_min (h a (by simp)) hδ, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hr b hb)

private theorem index_gap (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    ∃ δ, 0 < δ ∧ ∀ u, cellIndex l u ≠ 0 → δ ≤ u := by
  obtain ⟨δ, hδ, hr⟩ := list_pos_min _ (interior_pos l hs h0)
  refine ⟨δ, hδ, fun u hu => ?_⟩
  unfold cellIndex at hu
  obtain ⟨b, hb⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hu)
  rw [List.mem_filter, decide_eq_true_eq] at hb
  exact (hr b hb.1).trans hb.2

private theorem finite_const (n : ℕ) (P : ℕ → ℝ → Prop) (hmono : ∀ j K K', P j K → K ≤ K' → P j K')
    (h : ∀ j < n, ∃ K, P j K) : ∃ K, 0 ≤ K ∧ ∀ j < n, P j K := by
  induction n with
  | zero => exact ⟨0, le_rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨K, hK0, hK⟩ := ih (fun j hj => h j (by omega))
    obtain ⟨K', hK'⟩ := h n (by omega)
    refine ⟨max K K', le_max_of_le_left hK0, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hmono _ _ _ (hK j hj) (le_max_left _ _)
    · exact hmono _ _ _ hK' (le_max_right _ _)

private theorem t_slopeBound (S : Spline) (hS : SplineJoins 0 S) (K : ℝ)
    (hK : ∀ i < cellCount S.mesh.tBreaks, ∀ j < cellCount S.mesh.xBreaks, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece i j)).re -
          (MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] (S.piece i j)).re| ≤ K * |t - t'|) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      |(S.evalHalf t x).re - (S.evalHalf t' x).re| ≤ K * |t - t'| := by
  intro x hx t ht t' ht'
  have hm := hS.mesh
  have hj := index_lt S.mesh.xBreaks hm.x_first hm.x_last x
  have hc := count_pos S.mesh.tBreaks hm.t_first hm.t_last
  exact glue_slopeBound 0 1 K ((S.mesh.tBreaks.drop 1).dropLast) (interior_pw _ hm.t_sorted)
    (fun k u => (MvPolynomial.eval ![(u : ℂ), (x : ℂ)] (S.piece k (cellIndex S.mesh.xBreaks x))).re)
    (fun k hk u hu v hv => hK k (by rw [interior_len] at hk; omega) _ hj x hx u hu v hv)
    (fun k hk => by
      have hk2 := hk
      rw [interior_len] at hk2
      have hJ := hS.t_joins (k + 1) (by omega) (by omega) _ hj 0 le_rfl
      simp only [Nat.add_sub_cancel, tDeriv, Function.iterate_zero, id] at hJ
      have := congrArg (fun Q => (MvPolynomial.eval
        ![((S.mesh.tBreaks.getD (k + 1) 0 : ℝ) : ℂ), (x : ℂ)] Q).re) hJ
      simp only [eval_first] at this
      simp only [interior_get _ k hk]
      simpa using this) t ht t' ht'

private theorem x_slopeBound (S : Spline) (hS : SplineJoins 0 S) (t M : ℝ)
    (hM : ∀ j < cellCount S.mesh.xBreaks, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ x' ∈ Set.Icc (0 : ℝ) 1,
      |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece (cellIndex S.mesh.tBreaks t) j)).re -
        (MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] (S.piece (cellIndex S.mesh.tBreaks t) j)).re| ≤ M * |x - x'|) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ x' ∈ Set.Icc (0 : ℝ) 1,
      |(S.evalHalf t x).re - (S.evalHalf t x').re| ≤ M * |x - x'| := by
  intro x hx x' hx'
  have hm := hS.mesh
  have hi := index_lt S.mesh.tBreaks hm.t_first hm.t_last t
  have hc := count_pos S.mesh.xBreaks hm.x_first hm.x_last
  exact glue_slopeBound 0 1 M ((S.mesh.xBreaks.drop 1).dropLast) (interior_pw _ hm.x_sorted)
    (fun k u => (MvPolynomial.eval ![(t : ℂ), (u : ℂ)] (S.piece (cellIndex S.mesh.tBreaks t) k)).re)
    (fun k hk u hu v hv => hM k (by rw [interior_len] at hk; omega) u hu v hv)
    (fun k hk => by
      have hk2 := hk
      rw [interior_len] at hk2
      have hJ := hS.x_joins (k + 1) (by omega) (by omega) _ hi 0 le_rfl
      simp only [Nat.add_sub_cancel, xDeriv, Function.iterate_zero, id] at hJ
      have := congrArg (fun Q => (MvPolynomial.eval
        ![(t : ℂ), ((S.mesh.xBreaks.getD (k + 1) 0 : ℝ) : ℂ)] Q).re) hJ
      simp only [eval_second] at this
      simp only [interior_get _ k hk]
      simpa using this) x hx x' hx'

private theorem abs_unit {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : |x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hx.1], hx.2⟩

private theorem spline_t_bound (S : Spline) (hS : SplineJoins 0 S) : ∃ A, 0 ≤ A ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      |(S.evalHalf t x).re - (S.evalHalf t' x).re| ≤ A * |t - t'| := by
  have hpiece : ∀ i j, ∃ K : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece i j)).re -
        (MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] (S.piece i j)).re| ≤ K * |t - t'| := by
    intro i j
    obtain ⟨K, _, h⟩ := poly_slopeBound (S.piece i j)
    refine ⟨K, fun x hx t ht t' ht' => ?_⟩
    have := h t t' x x (abs_unit ht) (abs_unit ht') (abs_unit hx) (abs_unit hx)
    simpa using this
  obtain ⟨A, hA, hAll⟩ := finite_const (cellCount S.mesh.tBreaks)
    (fun i K => ∀ j < cellCount S.mesh.xBreaks, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ t' ∈ Set.Icc (0 : ℝ) 1, |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece i j)).re -
        (MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] (S.piece i j)).re| ≤ K * |t - t'|)
    (fun i K K' h hKK j hj x hx t ht t' ht' =>
      (h j hj x hx t ht t' ht').trans (mul_le_mul_of_nonneg_right hKK (abs_nonneg _)))
    (fun i _ => by
      obtain ⟨K, _, hK⟩ := finite_const (cellCount S.mesh.xBreaks)
        (fun j K => ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
          |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece i j)).re -
            (MvPolynomial.eval ![(t' : ℂ), (x : ℂ)] (S.piece i j)).re| ≤ K * |t - t'|)
        (fun j K K' h hKK x hx t ht t' ht' =>
          (h x hx t ht t' ht').trans (mul_le_mul_of_nonneg_right hKK (abs_nonneg _)))
        (fun j _ => hpiece i j)
      exact ⟨K, hK⟩)
  exact ⟨A, hA, t_slopeBound S hS A hAll⟩

private theorem spline_x_bound (S : Spline) (hS : SplineJoins 0 S) (v : ℂ)
    (hv : ∀ j < cellCount S.mesh.xBreaks, atFirst 0 (S.piece 0 j) = MvPolynomial.C v) : ∃ C, 0 ≤ C ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ x' ∈ Set.Icc (0 : ℝ) 1,
      |(S.evalHalf t x).re - (S.evalHalf t x').re| ≤ C * t * |x - x'| := by
  obtain ⟨K1, hK1, h1⟩ := finite_const (cellCount S.mesh.xBreaks)
    (fun j K => ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ x' ∈ Set.Icc (0 : ℝ) 1,
      |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece 0 j)).re -
        (MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] (S.piece 0 j)).re| ≤ K * t * |x - x'|)
    (fun j K K' h hKK t ht x hx x' hx' => (h t ht x hx x' hx').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKK ht.1) (abs_nonneg _)))
    (fun j hj => by
      obtain ⟨K, _, h⟩ := flat_slope _ v (hv j hj)
      exact ⟨K, fun t ht x hx x' hx' => h t x x' ht.1 ht.2 (abs_unit hx) (abs_unit hx')⟩)
  have hpiece : ∀ i j, ∃ K : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ x' ∈ Set.Icc (0 : ℝ) 1,
      |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece i j)).re -
        (MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] (S.piece i j)).re| ≤ K * |x - x'| := by
    intro i j
    obtain ⟨K, _, h⟩ := poly_slopeBound (S.piece i j)
    refine ⟨K, fun t ht x hx x' hx' => ?_⟩
    have := h t t x x' (abs_unit ht) (abs_unit ht) (abs_unit hx) (abs_unit hx')
    simpa using this
  obtain ⟨K2, hK2, h2⟩ := finite_const (cellCount S.mesh.tBreaks)
    (fun i K => ∀ j < cellCount S.mesh.xBreaks, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ x' ∈ Set.Icc (0 : ℝ) 1, |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece i j)).re -
        (MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] (S.piece i j)).re| ≤ K * |x - x'|)
    (fun i K K' h hKK j hj t ht x hx x' hx' =>
      (h j hj t ht x hx x' hx').trans (mul_le_mul_of_nonneg_right hKK (abs_nonneg _)))
    (fun i _ => by
      obtain ⟨K, _, hK⟩ := finite_const (cellCount S.mesh.xBreaks)
        (fun j K => ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ x' ∈ Set.Icc (0 : ℝ) 1,
          |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece i j)).re -
            (MvPolynomial.eval ![(t : ℂ), (x' : ℂ)] (S.piece i j)).re| ≤ K * |x - x'|)
        (fun j K K' h hKK t ht x hx x' hx' =>
          (h t ht x hx x' hx').trans (mul_le_mul_of_nonneg_right hKK (abs_nonneg _)))
        (fun j _ => hpiece i j)
      exact ⟨K, hK⟩)
  obtain ⟨δ, hδ, hgap⟩ := index_gap S.mesh.tBreaks hS.mesh.t_sorted hS.mesh.t_first
  have hq : 0 ≤ K2 / δ := div_nonneg hK2 hδ.le
  refine ⟨K1 + K2 / δ, add_nonneg hK1 hq, fun t ht => ?_⟩
  apply x_slopeBound S hS t ((K1 + K2 / δ) * t)
  intro j hj x hx x' hx'
  by_cases hi : cellIndex S.mesh.tBreaks t = 0
  · rw [hi]
    exact (h1 j hj t ht x hx x' hx').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hq) ht.1) (abs_nonneg _))
  · have hδt := hgap t hi
    have hle : K2 ≤ (K1 + K2 / δ) * t := by
      calc K2 = K2 / δ * δ := (div_mul_cancel₀ K2 hδ.ne').symm
        _ ≤ K2 / δ * t := mul_le_mul_of_nonneg_left hδt hq
        _ ≤ (K1 + K2 / δ) * t := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK1) (hδ.le.trans hδt)
    exact (h2 _ (index_lt _ hS.mesh.t_first hS.mesh.t_last t) j hj t ht x hx x' hx').trans
      (mul_le_mul_of_nonneg_right hle (abs_nonneg _))

def halfVal (S : ChartScalar) (t x : ℝ) : ℝ :=
  if 0 ≤ x then (S.upper.evalHalf t x).re else (S.lower.evalHalf t (-x)).re

private theorem plane_eq (S : ChartScalar) (hS : IsJoinedScalar 0 S) (t : ℝ) :
    S.upper.evalHalf t 0 = S.lower.evalHalf t 0 := by
  have hu := hS.upper.mesh
  have hl := hS.lower.mesh
  unfold Spline.evalHalf
  rw [index_zero _ hu.x_sorted hu.x_first, index_zero _ hl.x_sorted hl.x_first, ← hS.same_t]
  have hJ := hS.plane_joins _ (index_lt _ hu.t_first hu.t_last t) 0 le_rfl
  simp only [xDeriv, Function.iterate_zero, id, pow_zero, map_one, one_mul] at hJ
  have := congrArg (MvPolynomial.eval ![(t : ℂ), ((0 : ℝ) : ℂ)]) hJ
  simp only [eval_second] at this
  simpa using this

theorem half_t_bound (S : ChartScalar) (hS : IsJoinedScalar 0 S) : ∃ A, 0 ≤ A ∧
    ∀ x, |x| ≤ 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      |halfVal S t x - halfVal S t' x| ≤ A * |t - t'| := by
  obtain ⟨A1, hA1, h1⟩ := spline_t_bound S.upper hS.upper
  obtain ⟨A2, hA2, h2⟩ := spline_t_bound S.lower hS.lower
  refine ⟨A1 + A2, add_nonneg hA1 hA2, fun x hx t ht t' ht' => ?_⟩
  have hx' := abs_le.1 hx
  unfold halfVal
  split_ifs with h
  · exact (h1 x ⟨h, hx'.2⟩ t ht t' ht').trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA2) (abs_nonneg _))
  · exact (h2 (-x) ⟨by linarith, by linarith⟩ t ht t' ht').trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA1) (abs_nonneg _))

theorem half_x_bound (S : ChartScalar) (hS : IsJoinedScalar 0 S) (v : ℂ)
    (hvu : ∀ j < cellCount S.upper.mesh.xBreaks, atFirst 0 (S.upper.piece 0 j) = MvPolynomial.C v)
    (hvl : ∀ j < cellCount S.lower.mesh.xBreaks, atFirst 0 (S.lower.piece 0 j) = MvPolynomial.C v) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x x', |x| ≤ 1 → |x'| ≤ 1 →
      |halfVal S t x - halfVal S t x'| ≤ C * t * |x - x'| := by
  obtain ⟨C1, hC1, h1⟩ := spline_x_bound S.upper hS.upper v hvu
  obtain ⟨C2, hC2, h2⟩ := spline_x_bound S.lower hS.lower v hvl
  refine ⟨C1 + C2, add_nonneg hC1 hC2, fun t ht => ?_⟩
  have hu : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ x' ∈ Set.Icc (0 : ℝ) 1,
      |(S.upper.evalHalf t x).re - (S.upper.evalHalf t x').re| ≤ (C1 + C2) * t * |x - x'| :=
    fun x hx x' hx' => (h1 t ht x hx x' hx').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2) ht.1) (abs_nonneg _))
  have hl : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ x' ∈ Set.Icc (0 : ℝ) 1,
      |(S.lower.evalHalf t x).re - (S.lower.evalHalf t x').re| ≤ (C1 + C2) * t * |x - x'| :=
    fun x hx x' hx' => (h2 t ht x hx x' hx').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1) ht.1) (abs_nonneg _))
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hp : (S.upper.evalHalf t 0).re = (S.lower.evalHalf t 0).re := by rw [plane_eq S hS t]
  have cross : ∀ x x', 0 ≤ x → x ≤ 1 → x' < 0 → -1 ≤ x' →
      |(S.upper.evalHalf t x).re - (S.lower.evalHalf t (-x')).re| ≤ (C1 + C2) * t * |x - x'| := by
    intro x x' hx0 hx1 hx'0 hx'1
    have e1 := hu x ⟨hx0, hx1⟩ 0 h0
    have e2 := hl 0 h0 (-x') ⟨by linarith, by linarith⟩
    rw [← hp] at e2
    calc _ ≤ |(S.upper.evalHalf t x).re - (S.upper.evalHalf t 0).re| +
          |(S.upper.evalHalf t 0).re - (S.lower.evalHalf t (-x')).re| := abs_sub_le _ _ _
      _ ≤ (C1 + C2) * t * |x - 0| + (C1 + C2) * t * |0 - -x'| := add_le_add e1 e2
      _ = (C1 + C2) * t * |x - x'| := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 0), show (0 : ℝ) - -x' = x' by ring, abs_of_neg hx'0,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - x')]
        ring
  intro x x' hx hx'
  have ha := abs_le.1 hx
  have hb := abs_le.1 hx'
  unfold halfVal
  split_ifs with g1 g2 g2
  · exact hu x ⟨g1, ha.2⟩ x' ⟨g2, hb.2⟩
  · exact cross x x' g1 ha.2 (not_le.1 g2) hb.1
  · rw [abs_sub_comm, abs_sub_comm x]
    exact cross x' x g2 hb.2 (not_le.1 g1) ha.1
  · have := hl (-x) ⟨by linarith [not_le.1 g1], by linarith⟩ (-x') ⟨by linarith [not_le.1 g2], by linarith⟩
    rwa [show -x - -x' = -(x - x') by ring, abs_neg] at this

theorem half_bound (S : ChartScalar) (A C : ℝ)
    (hA : ∀ x, |x| ≤ 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      |halfVal S t x - halfVal S t' x| ≤ A * |t - t'|)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x x', |x| ≤ 1 → |x'| ≤ 1 →
      |halfVal S t x - halfVal S t x'| ≤ C * t * |x - x'|) (hA0 : 0 ≤ A) :
    ∃ B, 0 ≤ B ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, |x| ≤ 1 → |halfVal S t x| ≤ B := by
  refine ⟨A + |halfVal S 0 0|, by positivity, fun t ht x hx => ?_⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have e1 := hA x hx t ht 0 h0
  have e2 := hC 0 h0 x 0 hx (by simp)
  rw [mul_zero, zero_mul] at e2
  rw [sub_zero, abs_of_nonneg ht.1] at e1
  calc |halfVal S t x| = |(halfVal S t x - halfVal S 0 x) + (halfVal S 0 x - halfVal S 0 0) + halfVal S 0 0| := by
        congr 1
        ring
    _ ≤ |(halfVal S t x - halfVal S 0 x) + (halfVal S 0 x - halfVal S 0 0)| + |halfVal S 0 0| := abs_add_le _ _
    _ ≤ |halfVal S t x - halfVal S 0 x| + |halfVal S 0 x - halfVal S 0 0| + |halfVal S 0 0| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ A * t + 0 + |halfVal S 0 0| := by gcongr
    _ ≤ A + |halfVal S 0 0| := by nlinarith [ht.2]

private theorem sign_iff (y : Space) : 0 ≤ heightRatio y ↔ 0 ≤ y 2 := by
  unfold heightRatio
  rcases eq_or_lt_of_le (norm_nonneg y) with h | h
  · have hy : y = 0 := norm_eq_zero.1 h.symm
    subst hy
    simp
  · constructor
    · intro hh
      by_contra hneg
      have := div_neg_of_neg_of_pos (not_le.1 hneg) h
      linarith
    · intro hh
      exact div_nonneg hh h.le

private theorem coord_le (y : Space) (i : Fin 3) : |y i| ≤ ‖y‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y i

private theorem height_abs (y : Space) : |heightRatio y| ≤ 1 := by
  unfold heightRatio
  rcases eq_or_lt_of_le (norm_nonneg y) with h | h
  · rw [← h]
    simp
  · rw [abs_div, abs_norm, div_le_one h]
    exact coord_le y 2

theorem height_slope (y z : Space) : ‖z‖ * |heightRatio y - heightRatio z| ≤ 2 * ‖y - z‖ := by
  by_cases hz : z = 0
  · subst hz
    simp only [norm_zero, zero_mul]
    positivity
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  by_cases hy : y = 0
  · subst hy
    have h0 : heightRatio (0 : Space) = 0 := by simp [heightRatio]
    rw [h0]
    unfold heightRatio
    calc ‖z‖ * |0 - z 2 / ‖z‖| = |z 2| := by
          rw [zero_sub, abs_neg, abs_div, abs_norm]
          field_simp
      _ ≤ ‖z‖ := coord_le z 2
      _ ≤ 2 * ‖0 - z‖ := by
          rw [zero_sub, norm_neg]
          linarith
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h1 : |y 2 - z 2| ≤ ‖y - z‖ := by
    have := coord_le (y - z) 2
    simpa using this
  have h2 : |y 2 / ‖y‖| ≤ 1 := height_abs y
  have h3 : |‖z‖ - ‖y‖| ≤ ‖y - z‖ := by
    rw [norm_sub_rev]
    exact abs_norm_sub_norm_le z y
  have e : ‖z‖ * (y 2 / ‖y‖ - z 2 / ‖z‖) = (y 2 - z 2) + (y 2 / ‖y‖) * (‖z‖ - ‖y‖) := by
    field_simp
    ring
  unfold heightRatio
  calc ‖z‖ * |y 2 / ‖y‖ - z 2 / ‖z‖| = |‖z‖ * (y 2 / ‖y‖ - z 2 / ‖z‖)| := by
        rw [abs_mul, abs_of_pos hzn]
    _ = |(y 2 - z 2) + (y 2 / ‖y‖) * (‖z‖ - ‖y‖)| := by rw [e]
    _ ≤ |y 2 - z 2| + |y 2 / ‖y‖| * |‖z‖ - ‖y‖| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ ‖y - z‖ + 1 * ‖y - z‖ := add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) zero_le_one)
    _ = 2 * ‖y - z‖ := by ring

private theorem chart_mem (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    chartT P y ∈ Set.Icc (0 : ℝ) 1 := by
  have hd : 0 < ‖y‖ + P.L0 := add_pos_of_nonneg_of_pos (norm_nonneg y) hP.L0_pos
  unfold chartT
  exact ⟨div_nonneg (norm_nonneg _) hd.le, (div_le_one hd).2 (by linarith [hP.L0_pos])⟩

private theorem chart_le (P : ChartParams) (hP : IsChartParams P) (z : Space) :
    chartT P z ≤ ‖z‖ / P.L0 :=
  div_le_div_of_nonneg_left (norm_nonneg _) hP.L0_pos (le_add_of_nonneg_left (norm_nonneg _))

theorem chart_slopeBound (P : ChartParams) (hP : IsChartParams P) (y z : Space) :
    |chartT P y - chartT P z| ≤ ‖y - z‖ / P.L0 := by
  have hL := hP.L0_pos
  have hy : 0 < ‖y‖ + P.L0 := add_pos_of_nonneg_of_pos (norm_nonneg y) hL
  have hz : 0 < ‖z‖ + P.L0 := add_pos_of_nonneg_of_pos (norm_nonneg z) hL
  have e : chartT P y - chartT P z = P.L0 * (‖y‖ - ‖z‖) / ((‖y‖ + P.L0) * (‖z‖ + P.L0)) := by
    unfold chartT
    rw [div_sub_div _ _ hy.ne' hz.ne']
    congr 1
    ring
  rw [e, abs_div, abs_mul, abs_of_pos hL, abs_of_pos (mul_pos hy hz), div_le_div_iff₀ (mul_pos hy hz) hL]
  have h1 : |‖y‖ - ‖z‖| ≤ ‖y - z‖ := abs_norm_sub_norm_le y z
  have h2 : P.L0 * P.L0 ≤ (‖y‖ + P.L0) * (‖z‖ + P.L0) := by
    nlinarith [norm_nonneg y, norm_nonneg z]
  calc P.L0 * |‖y‖ - ‖z‖| * P.L0 = |‖y‖ - ‖z‖| * (P.L0 * P.L0) := by ring
    _ ≤ ‖y - z‖ * (P.L0 * P.L0) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ ‖y - z‖ * ((‖y‖ + P.L0) * (‖z‖ + P.L0)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

private theorem pow_slope (d : ℕ) {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |(1 - a) ^ d - (1 - b) ^ d| ≤ d * |a - b| := by
  have h := abs_pow_sub_pow_le (a := 1 - a) (b := 1 - b) (n := d)
  have hm : max |1 - a| |1 - b| ^ (d - 1) ≤ 1 := by
    apply pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
    apply max_le
    · rw [abs_of_nonneg (by linarith [ha.2])]
      linarith [ha.1]
    · rw [abs_of_nonneg (by linarith [hb.2])]
      linarith [hb.1]
  rw [show (1 - a) - (1 - b) = -(a - b) by ring, abs_neg] at h
  calc _ ≤ |a - b| * d * max |1 - a| |1 - b| ^ (d - 1) := h
    _ ≤ |a - b| * d * 1 := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = d * |a - b| := by ring

theorem eval_eq (P : ChartParams) (S : ChartScalar) :
    S.eval P = fun y => (1 - chartT P y) ^ S.decay * halfVal S (chartT P y) (heightRatio y) := by
  funext y
  unfold ChartScalar.eval halfVal
  simp only [sign_iff]

end Internal.Slope

open Internal.Slope in
theorem scalarSlopeBoundOfJoins : ScalarSlopeBoundOfJoins := by
  intro P S hP hS hF
  obtain ⟨v, hvu, hvl⟩ := hF
  obtain ⟨A, hA0, hA⟩ := half_t_bound S hS
  obtain ⟨C, hC0, hC⟩ := half_x_bound S hS v hvu hvl
  obtain ⟨B, hB0, hB⟩ := half_bound S A C hA hC hA0
  have hL := hP.L0_pos
  have hK0 : 0 ≤ ((S.decay * B + A) + 2 * C) / P.L0 := by positivity
  refine ⟨(((S.decay * B + A) + 2 * C) / P.L0).toNNReal, LipschitzWith.of_dist_le_mul fun y z => ?_⟩
  rw [Real.coe_toNNReal _ hK0, Real.dist_eq, dist_eq_norm, eval_eq]
  have ha := chart_mem P hP y
  have hb := chart_mem P hP z
  have hu := height_abs y
  have hw := height_abs z
  have e1 : (1 - chartT P y) ^ S.decay * halfVal S (chartT P y) (heightRatio y) -
      (1 - chartT P z) ^ S.decay * halfVal S (chartT P z) (heightRatio z) =
      ((1 - chartT P y) ^ S.decay - (1 - chartT P z) ^ S.decay) * halfVal S (chartT P y) (heightRatio y) +
        (1 - chartT P z) ^ S.decay * (halfVal S (chartT P y) (heightRatio y) -
          halfVal S (chartT P z) (heightRatio z)) := by ring
  have s1 := abs_add_le (((1 - chartT P y) ^ S.decay - (1 - chartT P z) ^ S.decay) *
      halfVal S (chartT P y) (heightRatio y))
    ((1 - chartT P z) ^ S.decay * (halfVal S (chartT P y) (heightRatio y) -
      halfVal S (chartT P z) (heightRatio z)))
  rw [abs_mul, abs_mul] at s1
  have s2 := mul_le_mul (pow_slope S.decay ha hb) (hB _ ha _ hu) (abs_nonneg _) (by positivity)
  have s3 : |(1 - chartT P z) ^ S.decay| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg (by linarith [hb.2]) _)]
    exact pow_le_one₀ (by linarith [hb.2]) (by linarith [hb.1])
  have s4 : |halfVal S (chartT P y) (heightRatio y) - halfVal S (chartT P z) (heightRatio z)| ≤
      A * |chartT P y - chartT P z| + C * chartT P z * |heightRatio y - heightRatio z| :=
    (abs_sub_le _ (halfVal S (chartT P z) (heightRatio y)) _).trans
      (add_le_add (hA _ hu _ ha _ hb) (hC _ hb _ _ hu hw))
  have s5 := mul_le_mul s3 s4 (abs_nonneg _) zero_le_one
  have s6 := chart_slopeBound P hP y z
  have s7 : chartT P z * |heightRatio y - heightRatio z| ≤ 2 * ‖y - z‖ / P.L0 := by
    calc chartT P z * |heightRatio y - heightRatio z| ≤ ‖z‖ / P.L0 * |heightRatio y - heightRatio z| :=
          mul_le_mul_of_nonneg_right (chart_le P hP z) (abs_nonneg _)
      _ = (‖z‖ * |heightRatio y - heightRatio z|) / P.L0 := by ring
      _ ≤ (2 * ‖y - z‖) / P.L0 := div_le_div_of_nonneg_right (height_slope y z) hL.le
  have t1 : (S.decay * |chartT P y - chartT P z|) * B ≤ S.decay * B * (‖y - z‖ / P.L0) := by
    calc (S.decay * |chartT P y - chartT P z|) * B = (S.decay * B) * |chartT P y - chartT P z| := by ring
      _ ≤ (S.decay * B) * (‖y - z‖ / P.L0) := mul_le_mul_of_nonneg_left s6 (by positivity)
  have t2 : A * |chartT P y - chartT P z| ≤ A * (‖y - z‖ / P.L0) := mul_le_mul_of_nonneg_left s6 hA0
  have t3 : C * chartT P z * |heightRatio y - heightRatio z| ≤ C * (2 * ‖y - z‖ / P.L0) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left s7 hC0
  have eK : ((S.decay * B + A) + 2 * C) / P.L0 * ‖y - z‖ =
      S.decay * B * (‖y - z‖ / P.L0) + A * (‖y - z‖ / P.L0) + C * (2 * ‖y - z‖ / P.L0) := by ring
  rw [e1, eK]
  linarith

end Instance

end CertCell

end Breakdown
