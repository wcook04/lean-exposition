import Breakdown.Transfer.StatementsAbstract

open scoped ENNReal

noncomputable section

namespace Breakdown

namespace PeriodicInverseInternal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def nseq (M : ℕ → X →L[ℝ] X) (θ : ℝ) (c : ℕ → X) (x : X) : ℕ → X
  | 0 => x
  | n + 1 => θ⁻¹ • (M n (nseq M θ c x n) + c n)

theorem nseq_zero (M : ℕ → X →L[ℝ] X) (θ : ℝ) (c : ℕ → X) (x : X) :
    nseq M θ c x 0 = x := rfl

theorem nseq_succ (M : ℕ → X →L[ℝ] X) (θ : ℝ) (c : ℕ → X) (x : X) (n : ℕ) :
    nseq M θ c x (n + 1) = θ⁻¹ • (M n (nseq M θ c x n) + c n) := rfl

theorem nseq_add (M : ℕ → X →L[ℝ] X) (θ : ℝ) (c c' : ℕ → X) (x x' : X) (n : ℕ) :
    nseq M θ (fun t => c t + c' t) (x + x') n = nseq M θ c x n + nseq M θ c' x' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nseq_succ, nseq_succ, nseq_succ, ih, map_add, ← smul_add]
    congr 1
    abel

theorem nseq_smul (M : ℕ → X →L[ℝ] X) (θ a : ℝ) (c : ℕ → X) (x : X) (n : ℕ) :
    nseq M θ (fun t => a • c t) (a • x) n = a • nseq M θ c x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nseq_succ, nseq_succ, ih, map_smul, ← smul_add, smul_comm]

theorem nseq_homog (M : ℕ → X →L[ℝ] X) (θ : ℝ) (x : X) (n : ℕ) :
    nseq M θ (fun _ => 0) x n = (θ ^ n)⁻¹ • iterProd M n x := by
  induction n with
  | zero => simp [nseq_zero, iterProd]
  | succ n ih =>
    rw [nseq_succ, ih, map_smul, add_zero, smul_smul]
    show _ = (θ ^ (n + 1))⁻¹ • M n (iterProd M n x)
    rw [pow_succ, mul_inv, mul_comm]

theorem nseq_norm_le (M : ℕ → X →L[ℝ] X) (θ : ℝ) (hθ : 0 < θ) (c : ℕ → X) (x : X)
    (Bm Bc L : ℝ) (hBc : 0 ≤ Bc) (hM : ∀ n, ‖M n‖ ≤ Bm) (hc : ∀ n, ‖c n‖ ≤ Bc)
    (hL1 : 1 ≤ L) (hLm : θ⁻¹ * Bm ≤ L) (hLi : θ⁻¹ ≤ L) (n : ℕ) :
    ‖nseq M θ c x n‖ ≤ L ^ n * (‖x‖ + n * Bc) := by
  have hθi : 0 ≤ θ⁻¹ := (inv_pos.mpr hθ).le
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  induction n with
  | zero => simp [nseq_zero]
  | succ n ih =>
    have hS : 0 ≤ ‖x‖ + n * Bc := by positivity
    rw [nseq_succ, norm_smul, Real.norm_of_nonneg hθi]
    have hstep : ‖M n (nseq M θ c x n) + c n‖ ≤ Bm * ‖nseq M θ c x n‖ + Bc :=
      calc ‖M n (nseq M θ c x n) + c n‖ ≤ ‖M n (nseq M θ c x n)‖ + ‖c n‖ := norm_add_le _ _
        _ ≤ ‖M n‖ * ‖nseq M θ c x n‖ + Bc := add_le_add ((M n).le_opNorm _) (hc n)
        _ ≤ Bm * ‖nseq M θ c x n‖ + Bc := by gcongr; exact hM n
    have hp : θ⁻¹ ≤ L ^ (n + 1) :=
      calc θ⁻¹ ≤ L := hLi
        _ = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ (n + 1) := pow_le_pow_right₀ hL1 (by omega)
    calc θ⁻¹ * ‖M n (nseq M θ c x n) + c n‖
        ≤ θ⁻¹ * (Bm * ‖nseq M θ c x n‖ + Bc) := mul_le_mul_of_nonneg_left hstep hθi
      _ = (θ⁻¹ * Bm) * ‖nseq M θ c x n‖ + θ⁻¹ * Bc := by ring
      _ ≤ L * (L ^ n * (‖x‖ + n * Bc)) + L ^ (n + 1) * Bc :=
          add_le_add (mul_le_mul hLm ih (norm_nonneg _) hL0) (mul_le_mul_of_nonneg_right hp hBc)
      _ = L ^ (n + 1) * (‖x‖ + ((n + 1 : ℕ) : ℝ) * Bc) := by push_cast; ring

theorem conj_pow (M : ℕ → X →L[ℝ] X) (σ : X ≃ₗᵢ[ℝ] X) (k : ℕ)
    (h : ∀ n x, σ (M (n + k) x) = M n (σ x)) (j n : ℕ) (x : X) :
    (σ ^ j) (M (k * j + n) x) = M n ((σ ^ j) x) := by
  induction j generalizing n x with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [show k * (j + 1) + n = (k * j + n) + k by ring, h, ih]

theorem nseq_block (M : ℕ → X →L[ℝ] X) (θ : ℝ) (c : ℕ → X) (x : X) (σ : X ≃ₗᵢ[ℝ] X) (k : ℕ)
    (h : ∀ n x, σ (M (n + k) x) = M n (σ x)) (j i : ℕ) :
    (σ ^ j) (nseq M θ c x (k * j + i)) =
      nseq M θ (fun t => (σ ^ j) (c (k * j + t))) ((σ ^ j) (nseq M θ c x (k * j))) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← Nat.add_assoc, nseq_succ, nseq_succ, map_smul, map_add, conj_pow M σ k h, ih]

theorem block_orbit (M : ℕ → X →L[ℝ] X) (θ : ℝ) (hθ : θ ≠ 0) (c : ℕ → X) (x : X)
    (σ : X ≃ₗᵢ[ℝ] X) (k : ℕ) (h : ∀ n x, σ (M (n + k) x) = M n (σ x)) (j : ℕ) :
    orbitSeq ((σ.toContinuousLinearEquiv : X →L[ℝ] X) * iterProd M k) (θ ^ k)
      (fun j => (θ ^ k) • σ (nseq M θ (fun t => (σ ^ j) (c (k * j + t))) 0 k)) x j =
      (σ ^ j) (nseq M θ c x (k * j)) := by
  induction j with
  | zero => simp [orbitSeq, nseq_zero]
  | succ j ih =>
    have e1 : k * (j + 1) = k * j + k := by ring
    simp only [orbitSeq]
    rw [ih, e1, pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply,
      nseq_block M θ c x σ k h j k]
    have hs := nseq_add M θ (fun _ => 0) (fun t => (σ ^ j) (c (k * j + t)))
      ((σ ^ j) (nseq M θ c x (k * j))) 0 k
    simp only [zero_add, add_zero] at hs
    have hk : θ ^ k ≠ 0 := pow_ne_zero k hθ
    rw [hs, nseq_homog, map_add, map_smul, smul_add, smul_smul, inv_mul_cancel₀ hk, one_smul]
    simp

end PeriodicInverseInternal

open PeriodicInverseInternal in
theorem periodicInverse_of (h1 : DiscreteDichotomyStatement) : PeriodicInverseStatement := by
  intro X Y _ _ _ _ _ _ k ρ A Γ Ev J Pu K r₁ r₂ θ Cinv hk hθ hunit hinv hper hPu hcomm hr₁ hr₁θ
    hθr₂ hdec hgrow hsurj hPuJ
  obtain ⟨U, K', hU, hUb⟩ := h1 X _ Pu K r₁ r₂ (θ ^ k) hPu hcomm hr₁ hr₁θ hθr₂ hdec hgrow hsurj
  have hσ : ∀ n x, ρ.symm (stepMap A Γ Ev (n + k) x) = stepMap A Γ Ev n (ρ.symm x) := by
    intro n x
    rw [hper n]
    simp
  have hCinv : 0 ≤ Cinv := (norm_nonneg _).trans (hinv 0)
  have hθi : 0 ≤ θ⁻¹ := (inv_pos.mpr hθ).le
  have hM : ∀ n, ‖stepMap A Γ Ev n‖ ≤ ‖Ev‖ * Cinv * ‖Γ‖ := by
    intro n
    calc ‖stepMap A Γ Ev n‖ ≤ ‖Ev‖ * ‖(Ring.inverse (1 - A n)).comp Γ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Ev‖ * (‖Ring.inverse (1 - A n)‖ * ‖Γ‖) := by
          gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Ev‖ * (Cinv * ‖Γ‖) := by gcongr; exact hinv n
      _ = ‖Ev‖ * Cinv * ‖Γ‖ := by ring
  have hBm : 0 ≤ ‖Ev‖ * Cinv * ‖Γ‖ := by positivity
  obtain ⟨L, hL1, hLm, hLi⟩ : ∃ L : ℝ, 1 ≤ L ∧ θ⁻¹ * (‖Ev‖ * Cinv * ‖Γ‖) ≤ L ∧ θ⁻¹ ≤ L :=
    ⟨1 + θ⁻¹ * (1 + ‖Ev‖ * Cinv * ‖Γ‖), by nlinarith, by nlinarith, by nlinarith⟩
  have hRinv : ∀ n w, (1 - A n) (Ring.inverse (1 - A n) w) = w := by
    intro n w
    show ((1 - A n) * Ring.inverse (1 - A n)) w = w
    rw [Ring.mul_inverse_cancel _ (hunit n)]
    rfl
  obtain ⟨cf, hcf⟩ : ∃ cf : lp (fun _ : ℕ => Y) ∞ → ℕ → X,
      ∀ g n, cf g n = Ev (Ring.inverse (1 - A n) (g n)) := ⟨_, fun _ _ => rfl⟩
  have hcfb : ∀ g n, ‖cf g n‖ ≤ ‖Ev‖ * Cinv * ‖g‖ := by
    intro g n
    rw [hcf]
    calc ‖Ev (Ring.inverse (1 - A n) (g n))‖ ≤ ‖Ev‖ * ‖Ring.inverse (1 - A n) (g n)‖ :=
          Ev.le_opNorm _
      _ ≤ ‖Ev‖ * (‖Ring.inverse (1 - A n)‖ * ‖g n‖) := by gcongr; exact (Ring.inverse (1 - A n)).le_opNorm _
      _ ≤ ‖Ev‖ * (Cinv * ‖g‖) := by
          gcongr
          · exact hinv n
          · exact lp.norm_apply_le_norm ENNReal.top_ne_zero g n
      _ = ‖Ev‖ * Cinv * ‖g‖ := by ring
  have hcfadd : ∀ g g' n, cf (g + g') n = cf g n + cf g' n := by
    intro g g' n
    rw [hcf, hcf, hcf, lp.coeFn_add, Pi.add_apply, map_add, map_add]
  have hcfsmul : ∀ (a : ℝ) g n, cf (a • g) n = a • cf g n := by
    intro a g n
    rw [hcf, hcf, lp.coeFn_smul, Pi.smul_apply, map_smul, map_smul]
  obtain ⟨ct, hct⟩ : ∃ ct : lp (fun _ : ℕ => Y) ∞ → ℕ → X, ∀ g j, ct g j = (θ ^ k) •
      ρ.symm (nseq (stepMap A Γ Ev) θ (fun t => (ρ.symm ^ j) (cf g (k * j + t))) 0 k) :=
    ⟨_, fun _ _ => rfl⟩
  have hctb : ∀ g j, ‖ct g j‖ ≤ θ ^ k * (L ^ k * (k * (‖Ev‖ * Cinv))) * ‖g‖ := by
    intro g j
    rw [hct, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (by positivity)]
    have := nseq_norm_le (stepMap A Γ Ev) θ hθ (fun t => (ρ.symm ^ j) (cf g (k * j + t))) 0
      (‖Ev‖ * Cinv * ‖Γ‖) (‖Ev‖ * Cinv * ‖g‖) L (by positivity) hM
      (fun t => by rw [LinearIsometryEquiv.norm_map]; exact hcfb g _) hL1 hLm hLi k
    rw [norm_zero, zero_add] at this
    calc θ ^ k * ‖nseq (stepMap A Γ Ev) θ (fun t => (ρ.symm ^ j) (cf g (k * j + t))) 0 k‖
        ≤ θ ^ k * (L ^ k * (k * (‖Ev‖ * Cinv * ‖g‖))) := by gcongr
      _ = θ ^ k * (L ^ k * (k * (‖Ev‖ * Cinv))) * ‖g‖ := by ring
  have hctadd : ∀ g g' j, ct (g + g') j = ct g j + ct g' j := by
    intro g g' j
    have hs := nseq_add (stepMap A Γ Ev) θ (fun t => (ρ.symm ^ j) (cf g (k * j + t)))
      (fun t => (ρ.symm ^ j) (cf g' (k * j + t))) 0 0 k
    rw [add_zero] at hs
    rw [hct, hct, hct, ← smul_add, ← map_add, ← hs]
    simp only [hcfadd, map_add]
  have hctsmul : ∀ (a : ℝ) g j, ct (a • g) j = a • ct g j := by
    intro a g j
    have hs := nseq_smul (stepMap A Γ Ev) θ a (fun t => (ρ.symm ^ j) (cf g (k * j + t))) 0 k
    rw [smul_zero] at hs
    rw [hct, hct, smul_comm a, ← map_smul ρ.symm a, ← hs]
    simp only [hcfsmul, map_smul]
  set Cct := θ ^ k * (L ^ k * (k * (‖Ev‖ * Cinv))) with hCct
  have hCct0 : 0 ≤ Cct := by positivity
  obtain ⟨ctL, hctL⟩ : ∃ T : lp (fun _ : ℕ => Y) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞,
      ∀ g j, T g j = ct g j := by
    refine ⟨LinearMap.mkContinuous
      { toFun := fun g => ⟨fun j => ct g j,
          memℓp_infty ⟨Cct * ‖g‖, by rintro _ ⟨j, rfl⟩; exact hctb g j⟩⟩
        map_add' := fun g g' => lp.ext (funext fun j => hctadd g g' j)
        map_smul' := fun a g => lp.ext (funext fun j => hctsmul a g j) } Cct
      (fun g => lp.norm_le_of_forall_le (by positivity) (fun j => hctb g j)), fun _ _ => rfl⟩

  obtain ⟨e, he⟩ : ∃ e : lp (fun _ : ℕ => Y) ∞ → X, ∀ g, e g = U (ctL g) := ⟨_, fun _ => rfl⟩
  have heb : ∀ g, ‖e g‖ ≤ ‖U‖ * ‖ctL‖ * ‖g‖ := by
    intro g
    rw [he]
    calc ‖U (ctL g)‖ ≤ ‖U‖ * ‖ctL g‖ := U.le_opNorm _
      _ ≤ ‖U‖ * (‖ctL‖ * ‖g‖) := by gcongr; exact ctL.le_opNorm g
      _ = ‖U‖ * ‖ctL‖ * ‖g‖ := by ring
  obtain ⟨y, hy⟩ : ∃ y : lp (fun _ : ℕ => Y) ∞ → ℕ → X,
      ∀ g n, y g n = nseq (stepMap A Γ Ev) θ (cf g) (J (e g)) n := ⟨_, fun _ _ => rfl⟩
  have hyadd : ∀ g g' n, y (g + g') n = y g n + y g' n := by
    intro g g' n
    rw [hy, hy, hy, ← nseq_add, he, he, he, map_add, map_add, map_add]
    congr 1
    funext t
    exact hcfadd g g' t
  have hysmul : ∀ (a : ℝ) g n, y (a • g) n = a • y g n := by
    intro a g n
    rw [hy, hy, ← nseq_smul, he, he, map_smul, map_smul, map_smul]
    congr 1
    funext t
    exact hcfsmul a g t
  set CY := max K' 0 * (‖J‖ * (‖U‖ * ‖ctL‖) + ‖ctL‖) with hCY
  have hYb : ∀ g j, ‖(ρ.symm ^ j) (y g (k * j))‖ ≤ CY * ‖g‖ := by
    intro g j
    have hor := block_orbit (stepMap A Γ Ev) θ hθ.ne' (cf g) (J (e g)) ρ.symm k hσ j
    have hfun : (fun j => (θ ^ k) • ρ.symm (nseq (stepMap A Γ Ev) θ
        (fun t => (ρ.symm ^ j) (cf g (k * j + t))) 0 k)) = fun m => ctL g m := by
      funext m
      rw [hctL, hct]
    rw [hfun] at hor
    have hP : Pu (J (e g)) = U (ctL g) := by
      rw [he]
      show (Pu * J) (U (ctL g)) = U (ctL g)
      rw [hPuJ, hU]
    have hb := hUb (ctL g) (J (e g)) hP j
    rw [hor] at hb
    rw [hy]
    have hJe : ‖J (e g)‖ ≤ ‖J‖ * (‖U‖ * ‖ctL‖) * ‖g‖ :=
      calc ‖J (e g)‖ ≤ ‖J‖ * ‖e g‖ := J.le_opNorm _
        _ ≤ ‖J‖ * (‖U‖ * ‖ctL‖ * ‖g‖) := by gcongr; exact heb g
        _ = ‖J‖ * (‖U‖ * ‖ctL‖) * ‖g‖ := by ring
    have hs : ‖J (e g)‖ + ‖ctL g‖ ≤ (‖J‖ * (‖U‖ * ‖ctL‖) + ‖ctL‖) * ‖g‖ := by
      have := ctL.le_opNorm g
      nlinarith
    have hs0 : 0 ≤ ‖J (e g)‖ + ‖ctL g‖ := by positivity
    calc _ ≤ K' * (‖J (e g)‖ + ‖ctL g‖) := hb
      _ ≤ max K' 0 * (‖J (e g)‖ + ‖ctL g‖) := mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
      _ ≤ max K' 0 * ((‖J‖ * (‖U‖ * ‖ctL‖) + ‖ctL‖) * ‖g‖) :=
          mul_le_mul_of_nonneg_left hs (le_max_right _ _)
      _ = CY * ‖g‖ := by rw [hCY]; ring
  set Cy := L ^ k * (CY + k * (‖Ev‖ * Cinv)) with hCy
  have hyb : ∀ g n, ‖y g n‖ ≤ Cy * ‖g‖ := by
    intro g n
    obtain ⟨j, i, hi, rfl⟩ : ∃ j i, i < k ∧ n = k * j + i :=
      ⟨n / k, n % k, Nat.mod_lt n hk, (Nat.div_add_mod n k).symm⟩
    rw [← LinearIsometryEquiv.norm_map (ρ.symm ^ j), hy, nseq_block _ _ _ _ _ k hσ j i, ← hy]
    have hnb := nseq_norm_le (stepMap A Γ Ev) θ hθ (fun t => (ρ.symm ^ j) (cf g (k * j + t)))
      ((ρ.symm ^ j) (y g (k * j))) (‖Ev‖ * Cinv * ‖Γ‖) (‖Ev‖ * Cinv * ‖g‖) L (by positivity) hM
      (fun t => by rw [LinearIsometryEquiv.norm_map]; exact hcfb g _) hL1 hLm hLi i
    have hLk : L ^ i ≤ L ^ k := pow_le_pow_right₀ hL1 hi.le
    have hik : (i : ℝ) ≤ k := by exact_mod_cast hi.le
    have hYj := hYb g j
    calc _ ≤ L ^ i * (‖(ρ.symm ^ j) (y g (k * j))‖ + i * (‖Ev‖ * Cinv * ‖g‖)) := hnb
      _ ≤ L ^ k * (CY * ‖g‖ + k * (‖Ev‖ * Cinv * ‖g‖)) := by gcongr
      _ = Cy * ‖g‖ := by rw [hCy]; ring

  obtain ⟨z, hz⟩ : ∃ z : lp (fun _ : ℕ => Y) ∞ → ℕ → Y,
      ∀ g n, z g n = Ring.inverse (1 - A n) (g n + Γ (y g n)) := ⟨_, fun _ _ => rfl⟩
  have hCy0 : 0 ≤ Cy := by
    have := hyb 0 0
    rw [norm_zero, mul_zero] at this
    rw [hCy]
    have hCY0 : 0 ≤ CY := by rw [hCY]; positivity
    positivity
  have hzb : ∀ g n, ‖z g n‖ ≤ Cinv * (1 + ‖Γ‖ * Cy) * ‖g‖ := by
    intro g n
    rw [hz]
    calc ‖Ring.inverse (1 - A n) (g n + Γ (y g n))‖
        ≤ ‖Ring.inverse (1 - A n)‖ * ‖g n + Γ (y g n)‖ := (Ring.inverse (1 - A n)).le_opNorm _
      _ ≤ Cinv * (‖g‖ + ‖Γ‖ * (Cy * ‖g‖)) := by
          gcongr
          · exact hinv n
          · calc ‖g n + Γ (y g n)‖ ≤ ‖g n‖ + ‖Γ (y g n)‖ := norm_add_le _ _
              _ ≤ ‖g‖ + ‖Γ‖ * (Cy * ‖g‖) := by
                  gcongr
                  · exact lp.norm_apply_le_norm ENNReal.top_ne_zero g n
                  · exact (Γ.le_opNorm _).trans (by gcongr; exact hyb g n)
      _ = Cinv * (1 + ‖Γ‖ * Cy) * ‖g‖ := by ring
  have hzadd : ∀ g g' n, z (g + g') n = z g n + z g' n := by
    intro g g' n
    rw [hz, hz, hz, ← map_add, lp.coeFn_add, Pi.add_apply, hyadd, map_add Γ]
    congr 1
    abel
  have hzsmul : ∀ (a : ℝ) g n, z (a • g) n = a • z g n := by
    intro a g n
    rw [hz, hz, ← map_smul, lp.coeFn_smul, Pi.smul_apply, hysmul, map_smul, smul_add]
  set CR := max (‖U‖ * ‖ctL‖) (Cinv * (1 + ‖Γ‖ * Cy)) with hCR
  have hz0 : 0 ≤ Cinv * (1 + ‖Γ‖ * Cy) := by positivity
  obtain ⟨R, hR1, hR2⟩ : ∃ R : lp (fun _ : ℕ => Y) ∞ →L[ℝ] X × lp (fun _ : ℕ => Y) ∞,
      (∀ g, (R g).1 = e g) ∧ ∀ g n, (R g).2 n = z g n := by
    refine ⟨LinearMap.mkContinuous
      { toFun := fun g => (e g, ⟨fun n => z g n,
          memℓp_infty ⟨Cinv * (1 + ‖Γ‖ * Cy) * ‖g‖, by rintro _ ⟨n, rfl⟩; exact hzb g n⟩⟩)
        map_add' := fun g g' => Prod.ext (by simp only [Prod.fst_add, he, map_add])
          (lp.ext (funext fun n => hzadd g g' n))
        map_smul' := fun a g => Prod.ext (by simp only [Prod.smul_fst, he, map_smul, RingHom.id_apply])
          (lp.ext (funext fun n => hzsmul a g n)) } CR
      (fun g => norm_prod_le_iff.mpr ⟨(heb g).trans (by gcongr; exact le_max_left _ _),
        lp.norm_le_of_forall_le (by positivity) (fun n => (hzb g n).trans
          (by gcongr; exact le_max_right _ _))⟩), fun _ => rfl, fun _ _ => rfl⟩
  refine ⟨R, fun g => ?_, fun g n => ?_⟩
  · rw [hR1, he]
    exact LinearMap.mem_range.mpr ⟨U (ctL g), hU _⟩
  · rw [hR1, hR2]
    have h1A : z g n - A n (z g n) = g n + Γ (y g n) := by
      rw [← hRinv n (g n + Γ (y g n)), ← hz]
      simp
    rw [h1A]
    cases n with
    | zero =>
      rw [if_pos rfl, hy, nseq_zero, add_sub_cancel_right]
    | succ m =>
      rw [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, hR2, hy, nseq_succ, ← hy, hz, hcf]
      simp only [stepMap, ContinuousLinearMap.comp_apply, map_smul, map_add]
      abel_nf

end Breakdown
