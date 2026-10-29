module

public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Semantics.Exhaustification.InnocentInclusion
public import Studies.Franke2011

/-!
# Fox and Katzir (2021): Notes on Iterated Rationality Models of Scalar Implicatures

An iterated rationality model pairs the messages with the cells of the partition they induce by
peeling: round after round, each message that identifies a cell is paired with it, and both are
set aside. A message identifies a cell when it is true there and at no other remaining cell; it
mirror-identifies the cell when it is the only remaining message true there, which is
identification with messages and cells exchanged; and it identifies the cell probabilistically
when the cell is the strict mode of the Bayesian listener's posterior. With the naive speaker, who
chooses uniformly among the messages true at her cell and is [the rational speaker of the Rational
Speech Acts model at vanishing rationality](##tendsto_speaker_naiveSpeaker), probabilistic
peeling at flat priors [reads a disjunction without a conjunctive alternative as the conjunction of
its disjuncts](##TwoDisjuncts.peel_probIdentifies_disj). The paper's case against the model as an
account of scalar implicature is that this success does not extend: with three disjuncts [peeling
stops after the disjuncts](##ThreeDisjuncts.peel_probIdentifies_disj), where the grammatical
theory's exhaustification [derives the conjunctive readings of every
disjunction](##ThreeDisjuncts.exhIEII_disj), and a prior that makes one disjunct's cell [even
slightly likelier than the other's strengthens the disjunction to that
cell](##TwoDisjuncts.probIdentifies_aOrB_of_prior).

## Implementation notes

* The cells are the assignments of truth values to logically independent alternatives, the
  classes of worlds that agree on every message.
* A criterion takes the remaining messages and cells as sets, so that the infinite scales of §3
  fit. Peeling works on finite sets and takes at most as many rounds as there are messages.
* The naive speaker chooses among the messages of the original set throughout peeling, as the
  paper's tables after a round keep the probabilities of the full table.
* Probabilistic identification compares the posterior of `RSA.listener`, equivalently the prior
  times the speaker's probability of the message. At flat priors with the naive speaker it is the
  comparison of how many messages each cell makes true, and the examples are decided that way.
* The grammatical theory's operator is `Exhaustification.exhIEII`, Bar-Lev and Fox's innocent
  exclusion and inclusion, read off the worlds where a single disjunct holds.
* Franke's iterated best response is the light system of `Studies/Franke2011.lean`, iterated from
  the literal receiver, a naive hearer, or from the literal sender, a naive speaker.

## Errata

* §4.1 says that with the alternatives *A or B*, *A* and *B* "mirror-image cell identification in
  (10) will fail as well". (10) is the probabilistic notion, which succeeds there; the
  mirror-image notion that fails is (4) (`TwoDisjuncts.peel_mirrorIdentifies_disj_eq_empty`).
* §5.2 names the third state to be peeled, three times, as ¬A ∧ B ∧ ¬C, the cell where only `B`
  holds. The state meant is ¬A ∧ B ∧ C.
* (10), unlike (2) and (4), does not require the message to be true at the cell, so every message
  identifies the last remaining cell (`probIdentifies_of_subset_singleton`). Footnote 31 says that
  adding the three-way conjunction to van Rooij's alternatives keeps *A or B or C* from
  identifying any cell; under (10) as stated it is paired with the cell where no disjunct holds,
  at which it is false (`ThreeDisjuncts.peel_probIdentifies_vanRooij_insert`).
* Footnote 33 says that in Franke's system, starting from a naive speaker or from a naive hearer,
  *A or B* among the alternatives of a three-way disjunction comes to mean that two of the three
  disjuncts hold but not all three. In the light system that holds from a naive speaker
  (`ThreeDisjuncts.franke_naiveSpeaker`); from a naive hearer the cell where all three hold keeps
  its tie with the cells where two do, and *A or B* comes to mean that at least two hold
  (`ThreeDisjuncts.franke_naiveHearer`).

## TODO

* The second repair of §5.2, on which a message may identify several cells and messages with fewer
  disjuncts take precedence, is not formalized.
* The embedded configurations that §4.2 calls analogous, free choice under a possibility modal and
  disjunctive antecedents, are not formalized here; `Studies/ChampollionAlsopGrosu2019.lean` has
  the modal model.

## References

* [fox-katzir-2021]
* [franke-2011]
* [van-rooij-2010]
* [bar-lev-fox-2020]
* [frank-goodman-2012]
-/

@[expose] public section

namespace FoxKatzir2021

open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology

/-! ### Cell identification -/

/-- A criterion of cell identification decides, given the messages and the cells not yet paired,
whether a message identifies a cell. -/
abbrev Criterion (M T : Type*) : Type _ := Set M → Set T → M → T → Prop

section Identification

variable {M T : Type*} (den : M → Set T)

/-- (2) A message identifies a cell when it is true at the cell and at no other remaining cell. -/
def Identifies : Criterion M T := fun _ Ts m t ↦ t ∈ den m ∧ ∀ t' ∈ Ts, t' ∈ den m → t' = t

/-- (4) A message mirror-identifies a cell when it is the only remaining message true at the
cell. -/
def MirrorIdentifies : Criterion M T :=
  fun Ms _ m t ↦ t ∈ den m ∧ ∀ m' ∈ Ms, t ∈ den m' → m' = m

/-- The messages true at a cell. -/
def trueMessages (t : T) : Set M := {m | t ∈ den m}

theorem mirrorIdentifies_iff {Ms : Set M} {Ts : Set T} {m : M} {t : T} :
    MirrorIdentifies den Ms Ts m t ↔ Identifies (trueMessages den) Ts Ms t m :=
  Iff.rfl

end Identification

/-! ### Peeling -/

section Peeling

variable {M T : Type*} [DecidableEq M] [DecidableEq T] (C : Criterion M T)
  [∀ (Ms : Finset M) (Ts : Finset T) m t, Decidable (C ↑Ms ↑Ts m t)]

/-- (3b) The pairs of a remaining message and a remaining cell that the message identifies. -/
def round (Ms : Finset M) (Ts : Finset T) : Finset (M × T) :=
  (Ms ×ˢ Ts).filter fun p ↦ C ↑Ms ↑Ts p.1 p.2

/-- At most `n` rounds of peeling. -/
def peelAux : ℕ → Finset M → Finset T → Finset (M × T)
  | 0, _, _ => ∅
  | n + 1, Ms, Ts =>
    if round C Ms Ts = ∅ then ∅
    else round C Ms Ts ∪
      peelAux n (Ms \ (round C Ms Ts).image Prod.fst) (Ts \ (round C Ms Ts).image Prod.snd)

/-- (3) Peeling collects the pairs each round identifies and removes their messages and cells,
until a round identifies nothing. Each round that identifies something removes a message, so
there are at most as many rounds as messages. -/
def peel (Ms : Finset M) (Ts : Finset T) : Finset (M × T) := peelAux C Ms.card Ms Ts

variable {C}

omit [DecidableEq M] [DecidableEq T] in
theorem mem_round {Ms : Finset M} {Ts : Finset T} {p : M × T} :
    p ∈ round C Ms Ts ↔ p.1 ∈ Ms ∧ p.2 ∈ Ts ∧ C ↑Ms ↑Ts p.1 p.2 := by
  simp [round, and_assoc]

theorem round_subset_peel (Ms : Finset M) (Ts : Finset T) : round C Ms Ts ⊆ peel C Ms Ts := by
  intro p hp
  obtain ⟨hm, -, -⟩ := mem_round.1 hp
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (card_ne_zero_of_mem hm)
  rw [peel, hn, peelAux]
  split_ifs with h
  · exact absurd h (ne_empty_of_mem hp)
  · exact mem_union_left _ hp

theorem peelAux_congr {C' : Criterion M T} [∀ (Ms : Finset M) (Ts : Finset T) m t,
    Decidable (C' ↑Ms ↑Ts m t)] (h : ∀ (Ms : Finset M) (Ts : Finset T) m t,
    C ↑Ms ↑Ts m t ↔ C' ↑Ms ↑Ts m t) (n : ℕ) (Ms : Finset M) (Ts : Finset T) :
    peelAux C n Ms Ts = peelAux C' n Ms Ts := by
  have hr (Ms : Finset M) (Ts : Finset T) : round C Ms Ts = round C' Ms Ts :=
    filter_congr fun p _ ↦ h Ms Ts p.1 p.2
  induction n generalizing Ms Ts with
  | zero => rfl
  | succ n ih => simp only [peelAux, hr, ih]

theorem peel_congr {C' : Criterion M T} [∀ (Ms : Finset M) (Ts : Finset T) m t,
    Decidable (C' ↑Ms ↑Ts m t)] (h : ∀ (Ms : Finset M) (Ts : Finset T) m t,
    C ↑Ms ↑Ts m t ↔ C' ↑Ms ↑Ts m t) (Ms : Finset M) (Ts : Finset T) :
    peel C Ms Ts = peel C' Ms Ts :=
  peelAux_congr h _ Ms Ts

end Peeling

/-! ### Decidability over finite sets -/

section Decidable

variable {M T : Type*} (den : M → Set T) [∀ m, DecidablePred (· ∈ den m)] [DecidableEq M]
  [DecidableEq T]

instance (Ms : Finset M) (Ts : Finset T) (m : M) (t : T) :
    Decidable (Identifies den ↑Ms ↑Ts m t) :=
  decidable_of_iff (t ∈ den m ∧ ∀ t' ∈ Ts, t' ∈ den m → t' = t) (by simp [Identifies])

instance (Ms : Finset M) (Ts : Finset T) (m : M) (t : T) :
    Decidable (MirrorIdentifies den ↑Ms ↑Ts m t) :=
  decidable_of_iff (t ∈ den m ∧ ∀ m' ∈ Ms, t ∈ den m' → m' = m) (by simp [MirrorIdentifies])

end Decidable

/-! ### Probabilistic identification and the naive speaker -/

section Probabilistic

variable {M T : Type*} [MeasurableSpace M] [Countable M] [MeasurableSingletonClass M]
  [MeasurableSpace T] [MeasurableSingletonClass T]

/-- (10) A message probabilistically identifies a cell when the listener who hears it finds the
cell likelier than every other remaining cell: the cell is the strict mode, among the remaining
cells, of the Bayesian listener `RSA.listener` with prior `μ` and speaker `S`. -/
def ProbIdentifies (μ : Measure T) (S : T → Measure M) : Criterion M T :=
  fun _ Ts m t ↦
    ∀ t' ∈ Ts, t' ≠ t → (RSA.listener μ S m).real {t'} < (RSA.listener μ S m).real {t}

omit [MeasurableSingletonClass T] in
theorem probIdentifies_of_subset_singleton {μ : Measure T} {S : T → Measure M} {Ms : Set M}
    {Ts : Set T} {t : T} (h : Ts ⊆ {t}) (m : M) : ProbIdentifies μ S Ms Ts m t :=
  fun _ ht' hne ↦ absurd (h ht') hne

-- (10)
theorem probIdentifies_iff [Fintype T] {μ : Measure T} [IsFiniteMeasure μ] {S : T → Measure M}
    [∀ t, IsFiniteMeasure (S t)] {Ms : Set M} {Ts : Set T} {m : M} {t : T} :
    ProbIdentifies μ S Ms Ts m t ↔
      ∀ t' ∈ Ts, t' ≠ t → μ.real {t'} * (S t').real {m} < μ.real {t} * (S t).real {m} := by
  simp only [ProbIdentifies, RSA.listener_real_singleton_lt_iff]

variable [DecidableEq M] (den : M → Set T) [∀ m, DecidablePred (· ∈ den m)] (Ms₀ : Finset M)

/-- (12) The naive speaker chooses uniformly among the messages of `Ms₀` true at her cell. It is
Franke's unbiased belief in the literal sender, the sender of level 0. -/
noncomputable def naiveSpeaker [Countable T] : ProbabilityTheory.Kernel T M :=
  Franke2011.unbiased fun t ↦ Ms₀.filter (t ∈ den ·)

instance [Countable T] : IsFiniteKernel (naiveSpeaker den Ms₀) :=
  inferInstanceAs (IsFiniteKernel (Franke2011.unbiased _))

omit [Countable M] in
theorem naiveSpeaker_real_singleton [Countable T] (t : T) (m : M) :
    (naiveSpeaker den Ms₀ t).real {m} =
      if m ∈ Ms₀ ∧ t ∈ den m then ((Ms₀.filter (t ∈ den ·)).card : ℝ)⁻¹ else 0 := by
  rw [naiveSpeaker, Franke2011.unbiased_real_singleton]
  simp only [mem_filter]

/-- The cardinality form of identification by the naive speaker at a flat prior: the message is
true at the cell, and every other remaining cell where it is true makes more messages true. -/
def CountIdentifies : Criterion M T := fun _ Ts m t ↦
  ∀ t' ∈ Ts, t' ≠ t → (m ∈ Ms₀ ∧ t ∈ den m) ∧
    (t' ∈ den m → (Ms₀.filter (t ∈ den ·)).card < (Ms₀.filter (t' ∈ den ·)).card)

instance [DecidableEq T] (Ms : Finset M) (Ts : Finset T) (m : M) (t : T) :
    Decidable (CountIdentifies den Ms₀ ↑Ms ↑Ts m t) :=
  decidable_of_iff (∀ t' ∈ Ts, t' ≠ t → (m ∈ Ms₀ ∧ t ∈ den m) ∧
    (t' ∈ den m → (Ms₀.filter (t ∈ den ·)).card < (Ms₀.filter (t' ∈ den ·)).card))
    (by simp [CountIdentifies])

-- footnote 20
theorem probIdentifies_uniformOn_naiveSpeaker_iff [Fintype T] [Nonempty T] {Ms : Set M}
    {Ts : Set T} {m : M} {t : T} :
    ProbIdentifies (uniformOn Set.univ) (naiveSpeaker den Ms₀) Ms Ts m t ↔
      CountIdentifies den Ms₀ Ms Ts m t := by
  simp only [ProbIdentifies, CountIdentifies]
  refine forall₂_congr fun t' _ ↦ imp_congr_right fun _ ↦ ?_
  rw [RSA.listener_real_singleton_lt_iff_of_forall_eq _ _ uniformOn_univ_singleton_eq
      uniformOn_univ_singleton_ne_zero, naiveSpeaker_real_singleton, naiveSpeaker_real_singleton]
  have hpos {s : T} (hs : m ∈ Ms₀ ∧ s ∈ den m) : (0 : ℝ) < (Ms₀.filter (s ∈ den ·)).card :=
    Nat.cast_pos.2 (card_pos.2 ⟨m, mem_filter.2 hs⟩)
  split_ifs with h' h h
  · rw [inv_lt_inv₀ (hpos h') (hpos h)]
    simp [h, h'.2]
  · exact iff_of_false (not_lt.2 (inv_nonneg.2 (hpos h').le)) fun h'' ↦ h h''.1
  · exact iff_of_true (inv_pos.2 (hpos h)) ⟨h, fun ht' ↦ absurd ⟨h.1, ht'⟩ h'⟩
  · exact iff_of_false (lt_irrefl 0) fun h'' ↦ h h''.1

end Probabilistic

/-! ### The naive speaker as a rational speaker -/

section Limit

variable {M T : Type*} [Fintype M] [Fintype T] [DecidableEq M] [DecidableEq T]
  [MeasurableSpace M] [DiscreteMeasurableSpace M] [MeasurableSpace T] [DiscreteMeasurableSpace T]
  (sem : M → Finset T) [∀ u, DecidablePred (· ∈ (sem u : Set T))]

/-- **The naive speaker is the RSA speaker at vanishing rationality.** At a flat prior and no
cost, the rational speaker of the Rational Speech Acts model weighs each true message by the
inverse size of its extension to the power of her rationality, and as the rationality goes to
zero she chooses uniformly among the true messages, as the naive speaker (12) does. -/
theorem tendsto_speaker_naiveSpeaker (t : T) (m : M) :
    Tendsto (fun α : ℝ ↦ (RSA.speaker α 0 (RSA.listener (uniformOn Set.univ)
        (RSA.truthful fun u ↦ (sem u : Set T))) Measure.dirac t).real {m}) (𝓝[>] 0)
      (𝓝 ((naiveSpeaker (fun u ↦ (sem u : Set T)) univ t).real {m})) := by
  convert RSA.tendsto_speaker_uniformOn_dirac_real_singleton_nhdsGT_zero sem t m using 2
  rw [naiveSpeaker_real_singleton]
  simp only [mem_univ, true_and, Finset.mem_coe]
  split_ifs with h <;> simp only [div_eq_inv_mul, mul_one, mul_zero]
  congr

end Limit

/-! ### Exhaustification against finitely many messages

The grammatical theory's operator `exhIEII` reads off a set of minimal worlds when the
alternatives are the denotations of finitely many messages, each condition being a statement
about finitely many messages and worlds. -/

section Exhaustification

open Exhaustification

variable {W ι : Type*} {den : ι → Set W} {D : Finset ι} {φ : Set W}

private theorem exhIEII_image_eq (S E : Finset W) (hmem : ∀ v ∈ S, v ∈ φ)
    (hle : ∀ w ∈ φ, ∃ v ∈ S, ∀ i ∈ D, v ∈ den i → w ∈ den i)
    (hanti : ∀ v ∈ S, ∀ u ∈ S, (∀ i ∈ D, u ∈ den i → v ∈ den i) → ∀ i ∈ D, v ∈ den i → u ∈ den i)
    (hE : ∀ w, w ∈ E ↔ w ∈ φ ∧ ∀ i ∈ D, (w ∈ den i ↔ ∃ v ∈ S, v ∈ den i))
    (hne : E.Nonempty) : exhIEII (den '' ↑D) φ = ↑E := by
  have hM : IsMinimalCover (den '' ↑D) φ ↑S :=
    ⟨fun v hv ↦ hmem v hv, fun w hw ↦ (hle w hw).imp fun v ⟨hv, h⟩ ↦
      ⟨hv, by simpa [leALT_iff] using h⟩,
      fun v hv u hu h ↦ by simpa [leALT_iff] using hanti v hv u hu (by simpa [leALT_iff] using h)⟩
  obtain ⟨w₀, hw₀⟩ := hne
  rw [hM.exhIEII_eq ⟨w₀, ((hE w₀).1 hw₀).1, by simpa using ((hE w₀).1 hw₀).2⟩]
  ext w
  simpa using (hE w).symm

end Exhaustification

/-! ### Two disjuncts (§§2–4, §6)

The alternatives are drawn from *A*, *B*, *A or B* and *A and B*, with `A` and `B` logically
independent, and the cells are the four assignments of truth values to `A` and `B`. -/

namespace TwoDisjuncts

/-- A cell of the partition: whether `A` holds and whether `B` holds. -/
abbrev Cell := Bool × Bool

/-- The messages *A*, *B*, *A or B* and *A and B*. -/
inductive Msg where
  | a | b | aOrB | aAndB
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Msg := ⊤

instance : DiscreteMeasurableSpace Msg := ⟨fun _ ↦ trivial⟩

/-- The cells at which each message is true. -/
def den : Msg → Set Cell
  | .a => {t | t.1}
  | .b => {t | t.2}
  | .aOrB => {t | t.1 ∨ t.2}
  | .aAndB => {t | t.1 ∧ t.2}

instance : ∀ m, DecidablePred (· ∈ den m)
  | .a => fun t ↦ inferInstanceAs (Decidable (t.1 = true))
  | .b => fun t ↦ inferInstanceAs (Decidable (t.2 = true))
  | .aOrB => fun t ↦ inferInstanceAs (Decidable (t.1 = true ∨ t.2 = true))
  | .aAndB => fun t ↦ inferInstanceAs (Decidable (t.1 = true ∧ t.2 = true))

/-- The alternatives of a disjunction without a conjunctive alternative, {*A*, *B*, *A or B*}. -/
def disj : Finset Msg := {.a, .b, .aOrB}

-- §2.2, {*A*, *B*, *A and B*}
theorem peel_identifies_conj :
    peel (Identifies den) {.a, .b, .aAndB} univ =
      {(.aAndB, (true, true)), (.a, (true, false)), (.b, (false, true))} := by
  decide

-- §3, {*A*, *B*}
theorem peel_identifies_ab_eq_empty : peel (Identifies den) {.a, .b} univ = ∅ := by
  decide

-- §3, {*A*, *B*}
theorem peel_mirrorIdentifies_ab :
    peel (MirrorIdentifies den) {.a, .b} univ = {(.a, (true, false)), (.b, (false, true))} := by
  decide

-- §4.1
theorem peel_identifies_disj_eq_empty : peel (Identifies den) disj univ = ∅ := by
  decide

-- §4.1
theorem peel_mirrorIdentifies_disj_eq_empty : peel (MirrorIdentifies den) disj univ = ∅ := by
  decide

open Classical in
/-- **The conjunctive reading of disjunction** (§4.2). With the naive speaker and flat priors,
peeling by probabilistic identification first pairs *A* with the cell where only `A` holds and
*B* with the cell where only `B` holds, and then pairs *A or B* with the cell where both hold.
Neither identification (2) nor its mirror image (4) gets started on these alternatives. -/
theorem peel_probIdentifies_disj :
    peel (ProbIdentifies (uniformOn Set.univ) (naiveSpeaker den disj)) disj univ =
      {(.a, (true, false)), (.b, (false, true)), (.aOrB, (true, true))} := by
  rw [peel_congr fun _ _ _ _ ↦ probIdentifies_uniformOn_naiveSpeaker_iff den disj]
  decide

private theorem card_filter_disj (t : Cell) :
    (disj.filter (t ∈ den ·)).card = if t = (true, true) then 3 else if t = (false, false) then 0
      else 2 := by
  revert t; decide

-- fn. 22
theorem listener_aOrB_tie :
    (RSA.listener (uniformOn Set.univ) (naiveSpeaker den disj) .aOrB).real {(true, false)} =
        (RSA.listener (uniformOn Set.univ) (naiveSpeaker den disj) .aOrB).real {(false, true)} ∧
      (RSA.listener (uniformOn Set.univ) (naiveSpeaker den disj) .aOrB).real {(true, true)} <
        (RSA.listener (uniformOn Set.univ) (naiveSpeaker den disj) .aOrB).real {(true, false)} := by
  refine ⟨congrArg ENNReal.toReal (RSA.listener_apply_singleton_congr _ _ ?_
    (uniformOn_univ_singleton_eq _ _)), ?_⟩
  · have h₁ : Msg.aOrB ∈ disj.filter ((true, false) ∈ den ·) := by decide
    have h₂ : Msg.aOrB ∈ disj.filter ((false, true) ∈ den ·) := by decide
    rw [naiveSpeaker, Franke2011.unbiased_apply_singleton, Franke2011.unbiased_apply_singleton]
    simp only [h₁, h₂, ↓reduceIte, card_filter_disj]
    norm_num
  · rw [RSA.listener_real_singleton_lt_iff_of_forall_eq _ _ uniformOn_univ_singleton_eq
      uniformOn_univ_singleton_ne_zero, naiveSpeaker_real_singleton, naiveSpeaker_real_singleton,
      card_filter_disj, card_filter_disj]
    norm_num [disj, den]

/-- **Sensitivity to priors** (§6.1, (22)). Any prior on which the cell where only `B` holds is
likelier than the cell where only `A` holds, and not too much less likely than the cell where
both hold, makes *A or B* identify the cell where only `B` holds in the first round of peeling,
so that the disjunction is strengthened to the wrong cell. The paper's case, where the other two
cells are each 0.9999 times as likely as it, is one. -/
theorem probIdentifies_aOrB_of_prior {μ : Measure Cell} [IsFiniteMeasure μ]
    (h₁ : μ.real {(true, false)} < μ.real {(false, true)})
    (h₂ : 2 * μ.real {(true, true)} < 3 * μ.real {(false, true)}) (Ms : Set Msg) :
    ProbIdentifies μ (naiveSpeaker den disj) Ms Set.univ .aOrB (false, true) := by
  have h₀ : 0 < μ.real {(false, true)} := measureReal_nonneg.trans_lt h₁
  rw [probIdentifies_iff]
  rintro ⟨_ | _, _ | _⟩ - h
  all_goals first
    | exact absurd rfl h
    | (simp only [naiveSpeaker_real_singleton, card_filter_disj]
       norm_num [disj, den]
       linarith)

open Classical in
-- (22)
theorem aOrB_onlyB_mem_peel {μ : Measure Cell} [IsFiniteMeasure μ]
    (h₁ : μ.real {(true, false)} < μ.real {(false, true)})
    (h₂ : 2 * μ.real {(true, true)} < 3 * μ.real {(false, true)}) :
    (.aOrB, (false, true)) ∈ peel (ProbIdentifies μ (naiveSpeaker den disj)) disj univ :=
  round_subset_peel _ _ (mem_round.2 ⟨by decide, mem_univ _, by
    simpa using probIdentifies_aOrB_of_prior h₁ h₂ ↑disj⟩)

-- (22)
theorem probIdentifies_a_both_of_prior {μ : Measure Cell} [IsFiniteMeasure μ]
    (h : 3 * μ.real {(true, false)} < 2 * μ.real {(true, true)}) (Ms : Set Msg) :
    ProbIdentifies μ (naiveSpeaker den disj) Ms Set.univ .a (true, true) := by
  have h₀ : 0 < μ.real {(true, true)} := by
    nlinarith [measureReal_nonneg (μ := μ) (s := {(true, false)})]
  rw [probIdentifies_iff]
  rintro ⟨_ | _, _ | _⟩ - h'
  all_goals first
    | exact absurd rfl h'
    | (simp only [naiveSpeaker_real_singleton, card_filter_disj]
       norm_num [disj, den]
       linarith)

-- §5
theorem exhIEII_disj : Exhaustification.exhIEII (den '' ↑disj) (den .aOrB) = {(true, true)} := by
  rw [exhIEII_image_eq {(true, false), (false, true)} {(true, true)} (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  simp

end TwoDisjuncts

/-! ### A finite scale (§2.2, (14), (21))

The alternatives *some*, *many* and *all* partition the context set into four cells. -/

namespace Scale

/-- The cells of the partition *some*, *many* and *all* induce. -/
inductive Cell where
  | none | someNotMany | manyNotAll | all
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Cell := ⊤

instance : DiscreteMeasurableSpace Cell := ⟨fun _ ↦ trivial⟩

instance : Nonempty Cell := ⟨.none⟩

/-- The messages *some*, *many* and *all*. -/
inductive Msg where
  | some | many | all
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Msg := ⊤

instance : DiscreteMeasurableSpace Msg := ⟨fun _ ↦ trivial⟩

/-- The cells at which each message is true. -/
def den : Msg → Set Cell
  | .some => {t | t ≠ .none}
  | .many => {t | t = .manyNotAll ∨ t = .all}
  | .all => {t | t = .all}

instance : ∀ m, DecidablePred (· ∈ den m)
  | .some => fun t ↦ inferInstanceAs (Decidable (t ≠ .none))
  | .many => fun t ↦ inferInstanceAs (Decidable (t = .manyNotAll ∨ t = .all))
  | .all => fun t ↦ inferInstanceAs (Decidable (t = .all))

-- §2.2: three rounds
theorem peel_identifies :
    peel (Identifies den) univ univ =
      {(.all, .all), (.many, .manyNotAll), (.some, .someNotMany)} := by
  decide

open Classical in
-- (14): one round
theorem round_probIdentifies :
    round (ProbIdentifies (uniformOn Set.univ) (naiveSpeaker den univ)) univ univ =
        {(.all, .all), (.many, .manyNotAll), (.some, .someNotMany)} ∧
      peel (ProbIdentifies (uniformOn Set.univ) (naiveSpeaker den univ)) univ univ =
        {(.all, .all), (.many, .manyNotAll), (.some, .someNotMany)} := by
  refine ⟨?_, ?_⟩
  · rw [show round (ProbIdentifies (uniformOn Set.univ) (naiveSpeaker den univ)) univ univ =
        round (CountIdentifies den univ) univ univ from
      filter_congr fun _ _ ↦ probIdentifies_uniformOn_naiveSpeaker_iff den univ]
    decide
  · rw [peel_congr fun _ _ _ _ ↦ probIdentifies_uniformOn_naiveSpeaker_iff den univ]
    decide

private theorem card_filter (t : Cell) :
    (univ.filter (t ∈ den ·)).card = match t with
      | .none => 0 | .someNotMany => 1 | .manyNotAll => 2 | .all => 3 := by
  revert t; decide

-- (21)
theorem probIdentifies_some_manyNotAll {μ : Measure Cell} [IsFiniteMeasure μ]
    (h₁ : 2 * μ.real {.someNotMany} < μ.real {.manyNotAll})
    (h₂ : 2 * μ.real {.all} < 3 * μ.real {.manyNotAll}) (Ms : Set Msg) :
    ProbIdentifies μ (naiveSpeaker den univ) Ms Set.univ .some .manyNotAll := by
  have h₀ : 0 < μ.real {.manyNotAll} := by
    nlinarith [measureReal_nonneg (μ := μ) (s := {Cell.someNotMany})]
  rw [probIdentifies_iff]
  rintro (_ | _ | _ | _) - h
  all_goals first
    | exact absurd rfl h
    | (simp only [naiveSpeaker_real_singleton, card_filter]
       norm_num [den]
       linarith)

end Scale

/-! ### Three disjuncts (§5)

The alternatives are drawn from the disjunctions and conjunctions of three logically independent
`A`, `B` and `C`, and the cells are the eight assignments of truth values to them. -/

namespace ThreeDisjuncts

/-- A cell of the partition: whether `A`, `B` and `C` hold. -/
abbrev Cell := Bool × Bool × Bool

/-- The messages: the disjuncts, their disjunctions and their conjunctions. -/
inductive Msg where
  | a | b | c | aOrB | aOrC | bOrC | aOrBOrC | aAndB | aAndC | bAndC | aAndBAndC
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Msg := ⊤

instance : DiscreteMeasurableSpace Msg := ⟨fun _ ↦ trivial⟩

/-- The cells at which each message is true. -/
def den : Msg → Set Cell
  | .a => {t | t.1}
  | .b => {t | t.2.1}
  | .c => {t | t.2.2}
  | .aOrB => {t | t.1 ∨ t.2.1}
  | .aOrC => {t | t.1 ∨ t.2.2}
  | .bOrC => {t | t.2.1 ∨ t.2.2}
  | .aOrBOrC => {t | t.1 ∨ t.2.1 ∨ t.2.2}
  | .aAndB => {t | t.1 ∧ t.2.1}
  | .aAndC => {t | t.1 ∧ t.2.2}
  | .bAndC => {t | t.2.1 ∧ t.2.2}
  | .aAndBAndC => {t | t.1 ∧ t.2.1 ∧ t.2.2}

instance : ∀ m, DecidablePred (· ∈ den m)
  | .a => fun t ↦ inferInstanceAs (Decidable (t.1 = true))
  | .b => fun t ↦ inferInstanceAs (Decidable (t.2.1 = true))
  | .c => fun t ↦ inferInstanceAs (Decidable (t.2.2 = true))
  | .aOrB => fun t ↦ inferInstanceAs (Decidable (t.1 = true ∨ t.2.1 = true))
  | .aOrC => fun t ↦ inferInstanceAs (Decidable (t.1 = true ∨ t.2.2 = true))
  | .bOrC => fun t ↦ inferInstanceAs (Decidable (t.2.1 = true ∨ t.2.2 = true))
  | .aOrBOrC => fun t ↦ inferInstanceAs (Decidable (t.1 = true ∨ t.2.1 = true ∨ t.2.2 = true))
  | .aAndB => fun t ↦ inferInstanceAs (Decidable (t.1 = true ∧ t.2.1 = true))
  | .aAndC => fun t ↦ inferInstanceAs (Decidable (t.1 = true ∧ t.2.2 = true))
  | .bAndC => fun t ↦ inferInstanceAs (Decidable (t.2.1 = true ∧ t.2.2 = true))
  | .aAndBAndC => fun t ↦ inferInstanceAs (Decidable (t.1 = true ∧ t.2.1 = true ∧ t.2.2 = true))

/-- The alternatives of a three-way disjunction: the disjuncts and all their disjunctions. -/
def disj : Finset Msg := {.a, .b, .c, .aOrB, .aOrC, .bOrC, .aOrBOrC}

/-- van Rooij's alternatives: the two-way disjunctions replaced by the two-way conjunctions. -/
def vanRooij : Finset Msg := {.a, .b, .c, .aAndB, .aAndC, .bAndC, .aOrBOrC}

open Classical in
/-- **Three disjuncts** (§5.1). Peeling by probabilistic identification pairs each disjunct with
the cell where it alone holds, and then stops: every remaining message is true at every remaining
cell where some disjunct holds, and the naive speaker sends it with the same probability at the
three cells where two disjuncts hold, so no disjunction is strengthened to a conjunction. -/
theorem peel_probIdentifies_disj :
    peel (ProbIdentifies (uniformOn Set.univ) (naiveSpeaker den disj)) disj univ =
      {(.a, (true, false, false)), (.b, (false, true, false)), (.c, (false, false, true))} := by
  rw [peel_congr fun _ _ _ _ ↦ probIdentifies_uniformOn_naiveSpeaker_iff den disj]
  decide

open Classical in
-- (19)
theorem peel_probIdentifies_vanRooij :
    peel (ProbIdentifies (uniformOn Set.univ) (naiveSpeaker den vanRooij)) vanRooij univ =
      {(.a, (true, false, false)), (.b, (false, true, false)), (.c, (false, false, true)),
        (.aAndB, (true, true, false)), (.aAndC, (true, false, true)),
        (.bAndC, (false, true, true)), (.aOrBOrC, (true, true, true))} := by
  rw [peel_congr fun _ _ _ _ ↦ probIdentifies_uniformOn_naiveSpeaker_iff den vanRooij]
  decide

open Classical in
-- fn. 31: with the two-way disjunctions added, *A or B or C* still identifies the cell where all
-- three hold; with the three-way conjunction added, it is paired only with the cell where none
-- holds, at which it is false, by the vacuous identification of the last remaining cell
theorem peel_probIdentifies_vanRooij_insert :
    (.aOrBOrC, (true, true, true)) ∈ peel (ProbIdentifies (uniformOn Set.univ)
        (naiveSpeaker den (vanRooij ∪ {.aOrB, .aOrC, .bOrC}))) (vanRooij ∪ {.aOrB, .aOrC, .bOrC})
        univ ∧
      (peel (ProbIdentifies (uniformOn Set.univ) (naiveSpeaker den (insert .aAndBAndC vanRooij)))
        (insert .aAndBAndC vanRooij) univ).filter (·.1 = .aOrBOrC) =
        {(.aOrBOrC, (false, false, false))} ∧ (false, false, false) ∉ den .aOrBOrC := by
  rw [peel_congr fun _ _ _ _ ↦ probIdentifies_uniformOn_naiveSpeaker_iff den _,
    peel_congr fun _ _ _ _ ↦ probIdentifies_uniformOn_naiveSpeaker_iff den _]
  decide

-- §5.2
theorem exhIEII_disj :
    Exhaustification.exhIEII (den '' ↑disj) (den .aOrBOrC) = {(true, true, true)} ∧
      Exhaustification.exhIEII (den '' ↑disj) (den .aOrB) = {(true, true, false)} := by
  refine ⟨?_, ?_⟩
  · rw [exhIEII_image_eq {(true, false, false), (false, true, false), (false, false, true)}
      {(true, true, true)} (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp
  · rw [exhIEII_image_eq {(true, false, false), (false, true, false)}
      {(true, true, false)} (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp

/-! #### Franke's iterated best response on three disjuncts (footnotes 30 and 33)

Franke's light system ([franke-2011], `Franke2011.receiverChain`, `Franke2011.senderChain`) is
iterated best response at flat priors. On the alternatives of the three-way disjunction its
outcome depends on where the iteration starts. -/

/-- The disjunctive messages, as the message type of Franke's game. -/
abbrev DMsg := {m : Msg // m ∈ disj}

/-- The cells at which each disjunctive message is true. -/
def fden (m : DMsg) : Finset Cell := univ.filter (· ∈ den m.1)

-- footnotes 30 and 33
theorem franke_naiveSpeaker :
    Franke2011.receiverStep fden (Franke2011.senderChain fden 2) ⟨.aOrBOrC, by decide⟩ =
        {(true, true, false), (true, false, true), (false, true, true)} ∧
      Franke2011.receiverStep fden (Franke2011.senderChain fden 2) ⟨.aOrB, by decide⟩ =
        {(true, true, false), (true, false, true), (false, true, true)} ∧
      Franke2011.senderChain fden 3 = Franke2011.senderChain fden 2 := by
  decide

-- footnote 30
theorem franke_naiveHearer :
    (∀ t, (⟨.aOrBOrC, by decide⟩ : DMsg) ∉
        Franke2011.senderStep fden (Franke2011.receiverChain fden 2) t) ∧
      Franke2011.receiverChain fden 2 ⟨.aOrBOrC, by decide⟩ = fden ⟨.aOrBOrC, by decide⟩ ∧
      Franke2011.receiverChain fden 2 ⟨.aOrB, by decide⟩ =
        {(true, true, false), (true, false, true), (false, true, true), (true, true, true)} ∧
      Franke2011.receiverChain fden 3 = Franke2011.receiverChain fden 2 := by
  decide

end ThreeDisjuncts

/-! ### Infinite scales (§3)

Read as *at least*, the numerals partition the context set into the cells where John has exactly
`k` children. No numeral is true at a single cell, so identification (2) never starts, while each
numeral is the only one true at its own cell once the smaller numerals are peeled, so mirror-image
identification (4) peels the numerals one by one. Under a downward-entailing operator the
messages true at a cell become the cells at which a message is true, and the two notions trade
places. -/

namespace Numerals

/-- *John has `n` children*, read as *at least `n`*, is true at the cells where he has `k ≥ n`
children. -/
def atLeast (n : ℕ) : Set ℕ := {k | n ≤ k}

-- §3
theorem not_identifies (Ms : Set ℕ) (n k : ℕ) : ¬ Identifies atLeast Ms Set.univ n k :=
  fun ⟨hk, h⟩ ↦ by
    simp only [atLeast, Set.mem_ofPred_eq] at hk h
    have := h (k + 1) trivial (by omega)
    omega

-- §3
theorem mirrorIdentifies (n : ℕ) (Ts : Set ℕ) : MirrorIdentifies atLeast {m | n ≤ m} Ts n n :=
  ⟨le_refl n, fun _ hm hmn ↦ le_antisymm hmn hm⟩

-- §3, under a downward-entailing operator
theorem identifies_trueMessages (n : ℕ) (Ts : Set ℕ) :
    Identifies (trueMessages atLeast) Ts {m | n ≤ m} n n :=
  (mirrorIdentifies_iff atLeast).1 (mirrorIdentifies n Ts)

-- §3, under a downward-entailing operator
theorem not_mirrorIdentifies_trueMessages (Ms : Set ℕ) (n k : ℕ) :
    ¬ MirrorIdentifies (trueMessages atLeast) Set.univ Ms k n :=
  fun h ↦ not_identifies Ms n k ((mirrorIdentifies_iff (trueMessages atLeast)).1 h)

end Numerals

end FoxKatzir2021
