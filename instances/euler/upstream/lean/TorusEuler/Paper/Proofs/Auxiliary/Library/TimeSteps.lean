import TorusEuler.Paper.Auxiliary.Statements
import TorusEuler.TerminalStageTimeBounds
import TorusEuler.TerminalScheduledNormContinuity
import TorusEuler.TerminalScheduleCosts

/-! # From the common part of the joint proof to Lemmas 1.2 and 1.3 of the note

Shared own content of Auxiliary Lemmas 1.2 and 1.3 (decisions D15, D16 of the ledger). The joint
proof of the note (auxiliary/terminal_smoothness.tex:115-462) is an induction on the time order
`q` whose step (:121-462) is *the common part*: it bounds the fields of step `j` through time
order `q` from the bounds of step `j - 1` through order `q - 1`. In the library's vocabulary the
common part is `InductiveEulerStages.TerminalTimeStep` (TerminalStageTimeBounds.lean:55): for
every `q ψ` there is `Ψ` such that for large `n`, the time bounds `StageTimeBounds q ψ n` of stage
`n` give `StageTimeBounds (q+1) Ψ (n+1)` and `StageMixedIncrementBound (q+1) m n`.

This file proves the framing of the induction, with the two parts of the common part as hypotheses:
the base case `q = 0` (:116-121) from (T1), (T2) and the second bound of (7.4), the induction on
`q` (:118-121), the continuity clauses of (1.2) and (1.3) from the joint smoothness and
periodicity of the fields, and the relation between `Aux.TimeBounds` / `Aux.MixedIncrementBound`
and the library's `StageTimeBounds` / `StageMixedIncrementBound`. -/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler.Paper.Lib.Aux

open TorusEuler InductiveEulerStages

section

variable {P : InductiveEulerParameters} {c : InductiveEulerConstruction P}

/-- `Aux.TimeBounds` contains the library's `StageTimeBounds` (the bounds without the continuity
clauses). -/
theorem stageTimeBounds_of_timeBounds {q ψq j : ℕ} (h : Paper.Aux.TimeBounds c q ψq j) :
    c.stages.StageTimeBounds q ψq j :=
  fun i hi t ht x => (h i hi).1 t ht x



/-- The frequency of every stage is at least one. -/
theorem one_le_frequency (P : InductiveEulerParameters) (j : ℕ) : 1 ≤ P.frequency j := by
  induction j with
  | zero =>
    have hpos := P.threshold_pos 1 le_rfl
    have hlog : 0 < Real.log (P.threshold 1) :=
      lt_of_lt_of_le (by
        have hK : (0 : ℝ) < frequencyExponent P.exponentParameter (1 + 1) := by
          have := P.exponentParameter_ge
          exact Nat.cast_pos.mpr (by unfold frequencyExponent; omega)
        positivity) (P.threshold_floor 1 le_rfl)
    exact ((Real.log_pos_iff hpos.le).mp hlog).le.trans P.initial_threshold
  | succ j ih => rw [P.frequency_step]; exact one_le_pow₀ ih

/-- Joint smoothness and periodicity of the fields of step `j` on the closed slab (T1 of
Theorem 7.1 and the stage type): velocity and residual, as used for the continuity clauses of
(1.3). -/
theorem stage_smooth {C T : ℝ} (h71 : Theorem71Conclusions c C T) (j : ℕ) :
    0 < c.stages.slab j ∧
    ContDiffOn ℝ ∞ (Function.uncurry (c.stages.velocity j))
      (Icc 0 (c.stages.slab j) ×ˢ (univ : Set Vec3)) ∧
    (∀ t ∈ Icc 0 (c.stages.slab j), SpatiallyPeriodic (c.stages.velocity j t)) ∧
    ContDiffOn ℝ ∞ (Function.uncurry (c.stages.residual j))
      (Icc 0 (c.stages.slab j) ×ˢ (univ : Set Vec3)) ∧
    (∀ t ∈ Icc 0 (c.stages.slab j), SpatiallyPeriodic (c.stages.residual j t)) := by
  have hT : 0 < c.stages.slab j := by
    have := h71.lifetime
    exact this.1.trans (this.2.2 j)
  have hV := (h71.T1 j).1
  have hVper : ∀ t ∈ Icc 0 (c.stages.slab j), SpatiallyPeriodic (c.stages.velocity j t) :=
    fun t ht => ((h71.T1 j).2 t ht).1
  have hp : ContDiffOn ℝ ∞ (Function.uncurry (c.stage j).pressure)
      (Icc 0 (c.stages.slab j) ×ˢ (univ : Set Vec3)) := (c.stage j).smooth_pressure
  exact ⟨hT, hV, hVper, contDiffOn_closedSlab_momentumResidual hT hV hp,
    fun t ht => spatiallyPeriodic_closedSlab_momentumResidual ht
      (contDiff_slice_on_closedSlab hV ht) (contDiff_slice_on_closedSlab hp ht) hVper
      ((c.stage j).periodic_pressure t ht)⟩

/-- The bounds of the library with the continuity clauses of (1.3): `Aux.TimeBounds` from
`StageTimeBounds`. The continuity in the supremum norm is that of the jets of the smooth periodic
fields (`slabTimeJet_normContinuity`). -/
theorem timeBounds_of_stageTimeBounds {C T : ℝ} (h71 : Theorem71Conclusions c C T)
    {q ψq j : ℕ} (h : c.stages.StageTimeBounds q ψq j) : Paper.Aux.TimeBounds c q ψq j := by
  obtain ⟨hT, hV, hVper, hR, hRper⟩ := stage_smooth h71 j
  intro i hi
  exact ⟨fun t ht x => h i hi t ht x, (slabTimeJet_normContinuity hT hV hVper i 0).1,
    (slabTimeJet_normContinuity hT hR hRper i 0).1⟩

/-- **Lemma 1.3 applied to a parameter record** (glue; copy of `Lib.S678b.lemma13_schedule`, order
part only): `q_j → ∞` for the schedule of every `InductiveEulerParameters`, from the hypothesis
`h1_3` (Lemma 1.3 of the paper). In the joint proof this is the fact "`q_j ≥ m` for large `j`"
(terminal_smoothness.tex:69-71, :117-118). -/
theorem lemma13_order (h1_3 : Statement.lemma_1_3) (P : InductiveEulerParameters) :
    Tendsto P.order atTop atTop := by
  obtain ⟨-, ht, -⟩ := h1_3 P.exponentParameter P.threshold (P.frequency 0) P.order P.frequency
    P.exponentParameter_ge (fun s hs => ⟨P.threshold_pos s hs, P.threshold_floor s hs⟩)
    P.initial_threshold P.initial_order rfl
    (fun j hj => by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact P.frequency_step i)
    (fun j hj => by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact P.order_maximum i)
  exact ht

/-- **The induction on `q` for Lemma 1.3** (terminal_smoothness.tex:116-121 and the conclusion of
the induction step): from the time part `htime` of the common part (the step :121-407 and the
residual and velocity step :428-461), (1.3) for every `q`. The base case is the clauses
`velocity_bound` and `residual_bound` of the stage type of `c` (`stageTimeBounds_zero`, with
`ψ_0 = 1`). The induction itself does not use Lemma 1.3 of the paper; that lemma enters only in
the step (growth (1.1) at :455 and `K_{j+1} → ∞` at :459), i.e. inside `htime`. -/
theorem timeBounds_of_step {C T : ℝ} (h71 : Theorem71Conclusions c C T)
    (htime : ∀ q ψ, ∃ Ψ : ℕ, ∀ᶠ n in atTop,
      c.stages.StageTimeBounds q ψ n → c.stages.StageTimeBounds (q + 1) Ψ (n + 1)) :
    ∀ q : ℕ, ∃ ψq jq : ℕ, ∀ j : ℕ, jq ≤ j → Paper.Aux.TimeBounds c q ψq j := by
  have hfreq : ∀ n, 1 ≤ c.stages.frequency n := fun n => one_le_frequency P n
  have hTime (q : ℕ) : ∃ ψ : ℕ, ∀ᶠ n in atTop, c.stages.StageTimeBounds q ψ n := by
    induction q with
    | zero => exact ⟨1, Eventually.of_forall (c.stages.stageTimeBounds_zero hfreq)⟩
    | succ q ih =>
      obtain ⟨ψ, hψ⟩ := ih
      obtain ⟨Ψ, hΨ⟩ := htime q ψ
      have hnext : ∀ᶠ n in atTop, c.stages.StageTimeBounds (q + 1) Ψ (n + 1) :=
        (hΨ.and hψ).mono fun _ h => h.1 h.2
      obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hnext
      refine ⟨Ψ, eventually_atTop.2 ⟨n₀ + 1, ?_⟩⟩
      intro n hn
      cases n with
      | zero => omega
      | succ j => exact hn₀ j (by omega)
  intro q
  obtain ⟨ψq, hψ⟩ := hTime q
  obtain ⟨jq, hjq⟩ := eventually_atTop.1 hψ
  exact ⟨ψq, jq, fun j hj => timeBounds_of_stageTimeBounds h71 (hjq j hj)⟩

open HierarchyTwistedProfile in
/-- The mixed increment of step `j` in the library's form gives `Aux.MixedIncrementBound`: the
continuity in `C^{m,1/2}` is that of the jets of the smooth periodic field
`U_j - U_{j-1} - O_j`, with `O_j = W_osc^♮` (`Theorem71StepData.oscillation`). -/
theorem mixedIncrementBound_of_stage {C T : ℝ} {a : ℕ} {ψ : Vec3 → ℝ}
    (h71 : Theorem71Conclusions c C T) (hSteps : Theorem71Steps c a ψ) {j m q : ℕ} (hj : 1 ≤ j)
    (h : c.stages.StageMixedIncrementBound q m (j - 1)) : Paper.Aux.MixedIncrementBound c m q j := by
  obtain ⟨hT, k, center, amp, d, χ, R, S, u, hd⟩ := hSteps j hj
  let Sj := c.stages.slab j
  let X := (c.stage (j - 1)).flow
  let Wosc := S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (j + 1))) -
    (S5.ops d).average (S5.expansion u (6 * frequencyExponent P.exponentParameter (P.order (j + 1))))
  have hX := hd.parent.flow
  have hU := hd.parent.velocity_smooth
  have hUper := hd.parent.velocity_periodic
  have hY : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => X z.1 0 z.2) (Icc 0 Sj ×ˢ (univ : Set Vec3)) :=
    hX.contDiffOn_inverseLabelFlow hT hU hUper
  have hO : ContDiffOn ℝ ∞ (Function.uncurry (c.stages.oscillation j))
      (Icc 0 Sj ×ˢ (univ : Set Vec3)) := by
    refine (HierarchySmoothProfile.contDiffOn_graphRead (A := fun t => X t 0) k Wosc.val.val
      hY).congr fun z hz => ?_
    exact congrFun (hd.oscillation z.1 hz.1) z.2
  have hOper : ∀ t ∈ Icc 0 Sj, SpatiallyPeriodic (c.stages.oscillation j t) := by
    intro t ht
    rw [hd.oscillation t ht]
    exact spatiallyPeriodic_inverseParentGraphRead hT hX hU hUper Wosc ht
  let f : Velocity := fun r x =>
    c.stages.velocity j r x - c.stages.velocity (j - 1) r x - c.stages.oscillation j r x
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 Sj ×ˢ (univ : Set Vec3)) :=
    ((h71.T1 j).1.sub hU).sub hO
  have hfper : ∀ t ∈ Icc 0 Sj, SpatiallyPeriodic (f t) := by
    intro t ht n x
    simp only [f, ((h71.T1 j).2 t ht).1 n x, hUper t ht n x, hOper t ht n x]
  refine ⟨fun t ht => ?_, (slabTimeJet_normContinuity hT hf hfper q m).2⟩
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  exact h t ht

/-- **Lemma 1.2 from the common part and Lemma 1.3** (terminal_smoothness.tex:115-121 and the
induction step): for `q = 0` the second bound of (7.4), read from the clause `correction_bound` of the stage type
of `c` (the same clause as `Theorem71Conclusions.increment`), as soon as `q_j ≥ m` (`horder`, from
Lemma 1.3 of the paper, :117-118); for `q ≥ 1`, the common part at the parent bounds that Lemma 1.3 supplies
(`hAux_1_3`, here as `h13`). -/
theorem mixedIncrement_of_step {C T : ℝ} {a : ℕ} {ψ : Vec3 → ℝ}
    (h71 : Theorem71Conclusions c C T) (hSteps : Theorem71Steps c a ψ)
    (horder : Tendsto P.order atTop atTop)
    (hinc : ∀ q m ψ, ∀ᶠ n in atTop,
      c.stages.StageTimeBounds q ψ n → c.stages.StageMixedIncrementBound (q + 1) m n)
    (h13 : ∀ q : ℕ, ∃ ψq jq : ℕ, ∀ j : ℕ, jq ≤ j → Paper.Aux.TimeBounds c q ψq j) :
    ∀ m q : ℕ, ∀ᶠ j in atTop, Paper.Aux.MixedIncrementBound c m q j := by
  intro m q
  cases q with
  | zero =>
    have hO : ∀ᶠ j in atTop, m ≤ P.order j :=
      horder.eventually (eventually_ge_atTop m)
    filter_upwards [hO, eventually_ge_atTop 1] with j hm hj
    have hs := c.stages.stageMixedIncrementBound_zero (n := j - 1) (m := m)
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    exact mixedIncrementBound_of_stage h71 hSteps hj (hs hm)
  | succ q =>
    obtain ⟨ψq, jq, hjq⟩ := h13 q
    have hO := (hinc q m ψq)
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hO
    refine eventually_atTop.2 ⟨max (n₀ + 1) (jq + 1), fun j hj => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    refine mixedIncrementBound_of_stage h71 hSteps (by omega) ?_
    exact hn₀ n (by omega) (stageTimeBounds_of_timeBounds (hjq n (by omega)))

end

/-! ## The common part as one statement, and the two lemmas from it

The common part of the joint proof (:125-407) feeds two row-specific steps: Lemma 1.3's residual and
velocity step (:428-461), `CommonTime`, and Lemma 1.2's truncation difference (:409-426),
`CommonIncrement`. Each lemma takes only the part it uses. Both are still open inputs. -/

/-- The time part of the common part (Lemma 1.3's own step, :428-461, with its parents from
:125-407). Only this field is used by Lemma 1.3. -/
def CommonTime : Prop :=
  ∀ ψ : Vec3 → ℝ, S5.CutoffSymbol ψ →
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ G : ℕ → ℝ,
    ∀ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (T : ℝ),
      Paper.Aux.TimeDerivativeThreshold P.exponentParameter G P.threshold →
      P.strengthConstant = 18 * Real.exp 3 → Theorem71Conclusions c (18 * Real.exp 3) T →
      Theorem71Steps c a ψ → ∀ q ψ', ∃ Ψ : ℕ, ∀ᶠ n in atTop,
        c.stages.StageTimeBounds q ψ' n → c.stages.StageTimeBounds (q + 1) Ψ (n + 1)

/-- The increment part of the common part (Lemma 1.2's own step, truncation difference
:409-426, with its parents from :125-407). Only this field is used by Lemma 1.2. -/
def CommonIncrement : Prop :=
  ∀ ψ : Vec3 → ℝ, S5.CutoffSymbol ψ →
  ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → ∃ G : ℕ → ℝ,
    ∀ (P : InductiveEulerParameters) (c : InductiveEulerConstruction P) (T : ℝ),
      Paper.Aux.TimeDerivativeThreshold P.exponentParameter G P.threshold →
      P.strengthConstant = 18 * Real.exp 3 → Theorem71Conclusions c (18 * Real.exp 3) T →
      Theorem71Steps c a ψ → ∀ q m ψ', ∀ᶠ n in atTop,
        c.stages.StageTimeBounds q ψ' n → c.stages.StageMixedIncrementBound (q + 1) m n

/-- Lemma 1.3 from its time part. -/
theorem lemma_1_3_of_commonTime (h : CommonTime) :
    Paper.Aux.Statement.lemma_1_3 := by
  intro ψ hψ
  obtain ⟨a₀, h⟩ := h ψ hψ
  refine ⟨a₀, fun a ha => ?_⟩
  obtain ⟨G, hG⟩ := h a ha
  exact ⟨G, fun P c T hT hC h71 hS => timeBounds_of_step h71 (hG P c T hT hC h71 hS)⟩

/-- Lemma 1.2 from Lemma 1.3 (`h13`) and the increment part of the common part: the floors and the majorants of the two
combine by maxima. -/
theorem lemma_1_2_of_commonPart (h1_3 : Statement.lemma_1_3)
    (h13 : Paper.Aux.Statement.lemma_1_3) (h : CommonIncrement) :
    Paper.Aux.Statement.lemma_1_2 := by
  intro ψ hψ
  obtain ⟨a₁, h13⟩ := h13 ψ hψ
  obtain ⟨a₂, hs⟩ := h ψ hψ
  refine ⟨max a₁ a₂, fun a ha => ?_⟩
  obtain ⟨G₁, h13a⟩ := h13 a (le_of_max_le_left ha)
  obtain ⟨G₂, hsa⟩ := hs a (le_of_max_le_right ha)
  refine ⟨fun n => max (G₁ n) (G₂ n), fun P c T hG hC h71 hS => ?_⟩
  have hG₁ : Paper.Aux.TimeDerivativeThreshold P.exponentParameter G₁ P.threshold :=
    fun s hs => (le_max_left _ _).trans (hG s hs)
  have hG₂ : Paper.Aux.TimeDerivativeThreshold P.exponentParameter G₂ P.threshold :=
    fun s hs => (le_max_right _ _).trans (hG s hs)
  exact mixedIncrement_of_step h71 hS (lemma13_order h1_3 P) (hsa P c T hG₂ hC h71 hS) (h13a P c T hG₁ hC h71 hS)

end TorusEuler.Paper.Lib.Aux
