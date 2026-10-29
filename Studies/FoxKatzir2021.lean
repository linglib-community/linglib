module

public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Semantics.Exhaustification.InnocentInclusion
public import Studies.Franke2011

/-!
# Fox and Katzir (2021): Notes on Iterated Rationality Models of Scalar Implicatures

An iterated rationality model pairs the messages with the cells of the partition they induce by
peeling: round after round, each message that identifies a cell is paired with it and both are set
aside, until a round identifies nothing. A message identifies a cell when it is true there and at
no other remaining cell; it mirror-identifies the cell when it is the only remaining message true
there, which is identification under the inverse truth relation; and it does so probabilistically
when the cell is the strict mode of the Bayesian listener's posterior. With the naive speaker, who
chooses uniformly among the messages true at her cell and is [the rational speaker of the Rational
Speech Acts model at vanishing rationality](##tendsto_speaker_naiveSpeaker), probabilistic peeling
at flat priors [reads the disjunction of two atoms as their
conjunction](##Disjunction.peel_probMirrorIdentifies_two). The paper's case against the model is
that this does not extend: with three or more atoms [peeling stops after the
atoms](##Disjunction.peel_probMirrorIdentifies_of_three_le), while the grammatical theory's
exhaustification [strengthens the disjunction of any set of atoms to the cell where exactly those
atoms hold](##Disjunction.exhIEII_or), whatever their number; and a prior that makes one
disjunct's cell [even slightly likelier than the other's strengthens the disjunction to that
cell](##Disjunction.probMirrorIdentifies_or_of_prior).

## Implementation notes

* Which messages are true at which cells is a relation `SetRel M T`. Under a downward-entailing
  operator the numerals' truth relation is the inverse of the upward one, so the two notions of
  identification trade places.
* The disjunctions take any finite set of logically independent atoms: a cell is the set of atoms
  that hold, a message the disjunction or the conjunction of a set of atoms, and an atom the
  disjunction of itself alone. Two atoms are the paper's §4 and three its §5.
* A criterion takes the remaining messages and cells as sets, so that the infinite scales of §3
  fit. Peeling iterates a round on finite sets as many times as there are messages, after which no
  round changes anything.
* The naive speaker chooses among the messages of the original set throughout peeling, as the
  paper's tables after a round keep the probabilities of the full table.
* Probabilistic identification compares the posterior of `RSA.listener`, equivalently the prior
  times the speaker's probability of the message. At flat priors with the naive speaker it is the
  comparison of how many messages each cell makes true; among the disjunctions of `n` atoms a cell
  of `k` atoms makes `2 ^ n - 2 ^ (n - k)` of them true, so it is the comparison of sizes.
* The grammatical theory's operator is `Exhaustification.exhIEII`, Bar-Lev and Fox's innocent
  exclusion and inclusion, read off the cells of a single atom.
* Franke's iterated best response is the light system of `Studies/Franke2011.lean`, iterated from
  the literal receiver, a naive hearer, or from the literal sender, a naive speaker.

## Errata

* §4.1 says that with the alternatives *A or B*, *A* and *B* "mirror-image cell identification in
  (10) will fail as well". (10) is the probabilistic notion, which succeeds there; the
  mirror-image notion that fails is (4) (`Disjunction.peel_mirrorIdentifies_disjunctions`).
* §5.2 names the third state to be peeled, three times, as ¬A ∧ B ∧ ¬C, the cell where only `B`
  holds. The state meant is ¬A ∧ B ∧ C.
* (10), unlike (2) and (4), does not require the message to be true at the cell, so every message
  identifies the last remaining cell (`probMirrorIdentifies_of_subset_singleton`). Footnote 31 says
  that adding the three-way conjunction to van Rooij's alternatives keeps *A or B or C* from
  identifying any cell; under (10) as stated it is paired with the cell where no atom holds, at
  which it is false (`Disjunction.peel_probMirrorIdentifies_vanRooij_insert`).
* Footnote 33 says that in Franke's system, starting from a naive speaker or from a naive hearer,
  *A or B* among the alternatives of a three-way disjunction comes to mean that two of the three
  disjuncts hold but not all three. In the light system that holds from a naive speaker
  (`Disjunction.franke_naiveSpeaker`); from a naive hearer the cell where all three hold keeps its
  tie with the cells where two do, and *A or B* comes to mean that at least two hold
  (`Disjunction.franke_naiveHearer`).

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
open scoped Topology SetRel

/-! ### Cell identification

Which messages are true at which cells is a relation `R : SetRel M T`. -/

/-- A criterion of cell identification decides, given the messages and the cells not yet paired,
whether a message identifies a cell. -/
abbrev Criterion (M T : Type*) : Type _ := Set M → Set T → M → T → Prop

section Identification

variable {M T : Type*} (R : SetRel M T)

/-- (2) A message identifies a cell when it is true at the cell and at no other remaining cell. -/
def Identifies : Criterion M T := fun _ Ts m t ↦ m ~[R] t ∧ ∀ t' ∈ Ts, m ~[R] t' → t' = t

/-- (4) A message mirror-identifies a cell when it is the only remaining message true at the cell:
the cell identifies the message under the inverse relation, the mirror image of (2). -/
def MirrorIdentifies : Criterion M T := fun Ms Ts m t ↦ Identifies R.inv Ts Ms t m

end Identification

/-! ### Peeling -/

section Peeling

variable {M T : Type*} [DecidableEq M] [DecidableEq T] (C : Criterion M T)
  [∀ (Ms : Finset M) (Ts : Finset T) m t, Decidable (C ↑Ms ↑Ts m t)]

/-- (3b) The pairs of a remaining message and a remaining cell that the message identifies. -/
def identified (Ms : Finset M) (Ts : Finset T) : Finset (M × T) :=
  (Ms ×ˢ Ts).filter fun p ↦ C ↑Ms ↑Ts p.1 p.2

/-- A state of peeling (3): the pairs collected, and the messages and cells not yet paired. -/
structure PeelState (M T : Type*) where
  /-- The message–cell pairs collected so far. -/
  pairs : Finset (M × T)
  /-- The messages not yet paired. -/
  messages : Finset M
  /-- The cells not yet paired. -/
  cells : Finset T

/-- (3d) A round of peeling adds the identified pairs and sets their messages and cells aside. -/
def step (s : PeelState M T) : PeelState M T where
  pairs := s.pairs ∪ identified C s.messages s.cells
  messages := s.messages \ (identified C s.messages s.cells).image Prod.fst
  cells := s.cells \ (identified C s.messages s.cells).image Prod.snd

/-- (3) Peeling the messages `Ms` and the cells `Ts`, for as many rounds as there are messages,
after which no round changes anything (`isFixedPt_step_iterate_card`). -/
def peel (Ms : Finset M) (Ts : Finset T) : Finset (M × T) :=
  ((step C)^[Ms.card] ⟨∅, Ms, Ts⟩).pairs

variable {C}

omit [DecidableEq M] [DecidableEq T] in
theorem mem_identified {Ms : Finset M} {Ts : Finset T} {p : M × T} :
    p ∈ identified C Ms Ts ↔ p.1 ∈ Ms ∧ p.2 ∈ Ts ∧ C ↑Ms ↑Ts p.1 p.2 := by
  simp [identified, and_assoc]

theorem step_eq_self_of_identified_eq_empty {s : PeelState M T}
    (h : identified C s.messages s.cells = ∅) : step C s = s := by
  simp [step, h]

theorem card_messages_step_lt {s : PeelState M T} (h : identified C s.messages s.cells ≠ ∅) :
    (step C s).messages.card < s.messages.card := by
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 h
  refine card_lt_card (sdiff_ssubset (fun m hm ↦ ?_) ⟨p.1, mem_image_of_mem _ hp⟩)
  obtain ⟨q, hq, rfl⟩ := mem_image.1 hm
  exact (mem_identified.1 hq).1

-- a round that identifies nothing ends peeling, and every other round removes a message
theorem isFixedPt_step_iterate_card (s : PeelState M T) :
    Function.IsFixedPt (step C) ((step C)^[s.messages.card] s) := by
  have key (k : ℕ) : ((step C)^[k] s).messages.card + k ≤ s.messages.card ∨
      Function.IsFixedPt (step C) ((step C)^[k] s) := by
    induction k with
    | zero => exact .inl le_rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with ih | ih
      · by_cases h : identified C ((step C)^[k] s).messages ((step C)^[k] s).cells = ∅
        · rw [step_eq_self_of_identified_eq_empty h]
          exact .inr (step_eq_self_of_identified_eq_empty h)
        · exact .inl (by have := card_messages_step_lt h; omega)
      · rw [ih.eq]
        exact .inr ih
  rcases key s.messages.card with h | h
  · refine step_eq_self_of_identified_eq_empty ?_
    have : ((step C)^[s.messages.card] s).messages = ∅ := card_eq_zero.1 (by omega)
    simp [identified, this]
  · exact h

theorem identified_subset_peel (Ms : Finset M) (Ts : Finset T) :
    identified C Ms Ts ⊆ peel C Ms Ts := by
  intro p hp
  have hpairs (k : ℕ) (s : PeelState M T) : s.pairs ⊆ ((step C)^[k] s).pairs := by
    induction k generalizing s with
    | zero => exact subset_rfl
    | succ k ih => exact subset_union_left.trans (ih (step C s))
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (card_ne_zero_of_mem (mem_identified.1 hp).1)
  rw [peel, hn, Function.iterate_succ_apply]
  exact hpairs n _ (mem_union_right _ hp)

theorem peel_congr {C' : Criterion M T} [∀ (Ms : Finset M) (Ts : Finset T) m t,
    Decidable (C' ↑Ms ↑Ts m t)] (h : ∀ (Ms : Finset M) (Ts : Finset T) m t,
    C ↑Ms ↑Ts m t ↔ C' ↑Ms ↑Ts m t) (Ms : Finset M) (Ts : Finset T) :
    peel C Ms Ts = peel C' Ms Ts := by
  have : step C = step C' := funext fun s ↦ by
    simp only [step, show identified C s.messages s.cells = identified C' s.messages s.cells from
      filter_congr fun p _ ↦ h _ _ p.1 p.2]
  rw [peel, peel, this]

end Peeling

/-! ### Decidability over finite sets -/

section Decidable

variable {M T : Type*} [DecidableEq M] [DecidableEq T] (R : SetRel M T) [DecidablePred (· ∈ R)]

instance (p : T × M) : Decidable (p ∈ R.inv) := inferInstanceAs (Decidable (p.swap ∈ R))

instance (Ms : Finset M) (Ts : Finset T) (m : M) (t : T) :
    Decidable (Identifies R ↑Ms ↑Ts m t) :=
  decidable_of_iff (m ~[R] t ∧ ∀ t' ∈ Ts, m ~[R] t' → t' = t) (by simp [Identifies])

instance (Ms : Finset M) (Ts : Finset T) (m : M) (t : T) :
    Decidable (MirrorIdentifies R ↑Ms ↑Ts m t) :=
  inferInstanceAs (Decidable (Identifies R.inv ↑Ts ↑Ms t m))

end Decidable

/-! ### Probabilistic identification and the naive speaker -/

section Probabilistic

variable {M T : Type*} [MeasurableSpace M] [Countable M] [MeasurableSingletonClass M]
  [MeasurableSpace T] [MeasurableSingletonClass T]

/-- (10) A message probabilistically mirror-identifies a cell when the listener who hears it finds
the cell likelier than every other remaining cell: the cell is the strict mode, among the
remaining cells, of the Bayesian listener `RSA.listener` with prior `μ` and speaker `S`. -/
def ProbMirrorIdentifies (μ : Measure T) (S : T → Measure M) : Criterion M T :=
  fun _ Ts m t ↦
    ∀ t' ∈ Ts, t' ≠ t → (RSA.listener μ S m).real {t'} < (RSA.listener μ S m).real {t}

omit [MeasurableSingletonClass T] in
theorem probMirrorIdentifies_of_subset_singleton {μ : Measure T} {S : T → Measure M}
    {Ms : Set M} {Ts : Set T} {t : T} (h : Ts ⊆ {t}) (m : M) :
    ProbMirrorIdentifies μ S Ms Ts m t :=
  fun _ ht' hne ↦ absurd (h ht') hne

-- (10)
theorem probMirrorIdentifies_iff [Fintype T] {μ : Measure T} [IsFiniteMeasure μ]
    {S : T → Measure M} [∀ t, IsFiniteMeasure (S t)] {Ms : Set M} {Ts : Set T} {m : M} {t : T} :
    ProbMirrorIdentifies μ S Ms Ts m t ↔
      ∀ t' ∈ Ts, t' ≠ t → μ.real {t'} * (S t').real {m} < μ.real {t} * (S t).real {m} := by
  simp only [ProbMirrorIdentifies, RSA.listener_real_singleton_lt_iff]

variable [DecidableEq M] (R : SetRel M T) [DecidablePred (· ∈ R)] (Ms₀ : Finset M)

/-- (12) The naive speaker chooses uniformly among the messages of `Ms₀` true at her cell. It is
Franke's unbiased belief in the literal sender, the sender of level 0. -/
noncomputable def naiveSpeaker [Countable T] : ProbabilityTheory.Kernel T M :=
  Franke2011.unbiased fun t ↦ Ms₀.filter (· ~[R] t)

instance [Countable T] : IsFiniteKernel (naiveSpeaker R Ms₀) :=
  inferInstanceAs (IsFiniteKernel (Franke2011.unbiased _))

omit [Countable M] in
theorem naiveSpeaker_real_singleton [Countable T] (t : T) (m : M) :
    (naiveSpeaker R Ms₀ t).real {m} =
      if m ∈ Ms₀ ∧ m ~[R] t then ((Ms₀.filter (· ~[R] t)).card : ℝ)⁻¹ else 0 := by
  rw [naiveSpeaker, Franke2011.unbiased_real_singleton]
  simp only [mem_filter]

/-- The cardinality form of identification by the naive speaker at a flat prior: the message is
true at the cell, and every other remaining cell where it is true makes more messages true. -/
def CountIdentifies : Criterion M T := fun _ Ts m t ↦
  ∀ t' ∈ Ts, t' ≠ t → (m ∈ Ms₀ ∧ m ~[R] t) ∧
    (m ~[R] t' → (Ms₀.filter (· ~[R] t)).card < (Ms₀.filter (· ~[R] t')).card)

instance [DecidableEq T] (Ms : Finset M) (Ts : Finset T) (m : M) (t : T) :
    Decidable (CountIdentifies R Ms₀ ↑Ms ↑Ts m t) :=
  decidable_of_iff (∀ t' ∈ Ts, t' ≠ t → (m ∈ Ms₀ ∧ m ~[R] t) ∧
    (m ~[R] t' → (Ms₀.filter (· ~[R] t)).card < (Ms₀.filter (· ~[R] t')).card))
    (by simp [CountIdentifies])

-- footnote 20
theorem probMirrorIdentifies_uniformOn_naiveSpeaker_iff [Fintype T] [Nonempty T] {Ms : Set M}
    {Ts : Set T} {m : M} {t : T} :
    ProbMirrorIdentifies (uniformOn Set.univ) (naiveSpeaker R Ms₀) Ms Ts m t ↔
      CountIdentifies R Ms₀ Ms Ts m t := by
  simp only [ProbMirrorIdentifies, CountIdentifies]
  refine forall₂_congr fun t' _ ↦ imp_congr_right fun _ ↦ ?_
  rw [RSA.listener_real_singleton_lt_iff_of_forall_eq _ _ uniformOn_univ_singleton_eq
      uniformOn_univ_singleton_ne_zero, naiveSpeaker_real_singleton, naiveSpeaker_real_singleton]
  have hpos {s : T} (hs : m ∈ Ms₀ ∧ m ~[R] s) : (0 : ℝ) < (Ms₀.filter (· ~[R] s)).card :=
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
  (sem : M → Finset T)

instance : DecidablePred (· ∈ ({p | p.2 ∈ sem p.1} : SetRel M T)) :=
  fun p ↦ inferInstanceAs (Decidable (p.2 ∈ sem p.1))

/-- **The naive speaker is the RSA speaker at vanishing rationality.** At a flat prior and no
cost, the rational speaker of the Rational Speech Acts model weighs each true message by the
inverse size of its extension to the power of her rationality, and as the rationality goes to
zero she chooses uniformly among the true messages, as the naive speaker (12) does. -/
theorem tendsto_speaker_naiveSpeaker (t : T) (m : M) :
    Tendsto (fun α : ℝ ↦ (RSA.speaker α 0 (RSA.listener (uniformOn Set.univ)
        (RSA.truthful fun u ↦ (sem u : Set T))) Measure.dirac t).real {m}) (𝓝[>] 0)
      (𝓝 ((naiveSpeaker {p | p.2 ∈ sem p.1} univ t).real {m})) := by
  convert RSA.tendsto_speaker_uniformOn_dirac_real_singleton_nhdsGT_zero sem t m using 2
  rw [naiveSpeaker_real_singleton]
  simp only [mem_univ, true_and, Set.mem_ofPred_eq]
  split_ifs with h <;> simp only [div_eq_inv_mul, mul_one, mul_zero]

end Limit

/-! ### Disjunctions (§§2–5)

A message is the disjunction or the conjunction of a set of logically independent atoms, and a
cell is the set of atoms that hold. -/

namespace Disjunction

/-- How a message combines its atoms. -/
inductive Connective where
  | or | and
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Connective := ⊤

instance : DiscreteMeasurableSpace Connective := ⟨fun _ ↦ trivial⟩

variable {ι : Type*}

/-- A disjunction holds at a cell when one of its atoms does, a conjunction when all of them do. -/
def Connective.Holds : Connective → Finset ι → Finset ι → Prop
  | .or, S, c => ∃ i ∈ S, i ∈ c
  | .and, S, c => S ⊆ c

instance [DecidableEq ι] : ∀ (k : Connective) (S c : Finset ι), Decidable (k.Holds S c)
  | .or, S, c => inferInstanceAs (Decidable (∃ i ∈ S, i ∈ c))
  | .and, S, c => inferInstanceAs (Decidable (S ⊆ c))

/-- A message is a connective and its set of atoms; an atom is the disjunction of itself alone. -/
abbrev Msg (ι : Type*) := Connective × Finset ι

/-- A cell is the set of atoms that hold there. -/
abbrev Cell (ι : Type*) := Finset ι

/-- A message is true at a cell when its connective holds of its atoms there. -/
def truth : SetRel (Msg ι) (Cell ι) := {p | p.1.1.Holds p.1.2 p.2}

@[simp]
theorem or_truth {S c : Finset ι} : (Connective.or, S) ~[truth] c ↔ ∃ i ∈ S, i ∈ c :=
  Iff.rfl

instance [DecidableEq ι] : DecidablePred (· ∈ (truth : SetRel (Msg ι) (Cell ι))) :=
  fun p ↦ inferInstanceAs (Decidable (p.1.1.Holds p.1.2 p.2))

variable [Fintype ι] [DecidableEq ι]

/-- The cells at which a message is true. -/
def extension (m : Msg ι) : Finset (Cell ι) := univ.filter (m ~[truth] ·)

/-- The extension of a message of `Ms`: the meaning in a game of Franke's whose messages are those
of `Ms`. -/
def extensionOn (Ms : Finset (Msg ι)) (m : {m // m ∈ Ms}) : Finset (Cell ι) := extension m.1

/-- The atoms, each the disjunction of itself alone. -/
def atoms : Finset (Msg ι) := univ.image fun i ↦ (.or, {i})

/-- The disjunctions of the nonempty sets of atoms: the alternatives of the disjunction of all
atoms, its disjuncts among them. -/
def disjunctions : Finset (Msg ι) := (univ.filter fun S : Finset ι ↦ S.Nonempty).image (.or, ·)

/-- van Rooij's alternatives: the atoms, the conjunctions of two atoms, and the disjunction of all
atoms. -/
def vanRooij : Finset (Msg ι) :=
  atoms ∪ (univ.filter fun S : Finset ι ↦ S.card = 2).image (.and, ·) ∪ {(.or, univ)}

/-- **Number independence on the grammatical theory** ((16), (20)). Against the disjunctions of
the nonempty sets of atoms, exhaustification by innocent exclusion and inclusion strengthens the
disjunction of any nonempty set of atoms to the cell where exactly those atoms hold: each of its
disjuncts holds and every other atom fails. The worlds where a single disjunct holds are the
minimal ones; no alternative is excludable but the disjunctions of other atoms, and all the
others are includable. -/
theorem exhIEII_or {S : Finset ι} (hS : S.Nonempty) :
    Exhaustification.exhIEII
      ((fun m ↦ (extension m : Set (Cell ι))) '' (↑(disjunctions (ι := ι)) : Set (Msg ι)))
      (extension (.or, S) : Set (Cell ι)) = {S} := by
  open Exhaustification in
  have hALT {a : Set (Cell ι)} :
      a ∈ (fun m ↦ (extension m : Set (Cell ι))) '' (↑(disjunctions (ι := ι)) : Set (Msg ι)) ↔
        ∃ T : Finset ι, T.Nonempty ∧ a = {c | ∃ i ∈ T, i ∈ c} := by
    simp only [disjunctions, coe_image, coe_filter, Set.mem_image, Set.mem_ofPred_eq,
      mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨T, hT, rfl⟩, rfl⟩
      exact ⟨T, hT, by ext c; simp [extension]⟩
    · rintro ⟨T, hT, rfl⟩
      exact ⟨_, ⟨T, hT, rfl⟩, by ext c; simp [extension]⟩
  have hφ (c : Cell ι) : c ∈ (extension (.or, S) : Set (Cell ι)) ↔ ∃ i ∈ S, i ∈ c := by
    simp [extension]
  have hsingle (T : Finset ι) :
      (∃ w ∈ (fun i ↦ ({i} : Cell ι)) '' (S : Set ι), w ∈ {c : Cell ι | ∃ k ∈ T, k ∈ c}) ↔
        ∃ i ∈ S, i ∈ T := by
    simp only [Set.mem_image, Finset.mem_coe, Set.mem_ofPred_eq, exists_exists_and_eq_and,
      mem_singleton, exists_eq_right]
  have hM : IsMinimalCover ((fun m ↦ (extension m : Set (Cell ι))) ''
      (↑(disjunctions (ι := ι)) : Set (Msg ι))) (extension (.or, S) : Set (Cell ι))
      ((fun i ↦ ({i} : Cell ι)) '' (S : Set ι)) := by
    refine ⟨?_, fun w hw ↦ ?_, ?_⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact (hφ _).2 ⟨i, hi, mem_singleton_self i⟩
    · obtain ⟨i, hi, hiw⟩ := (hφ w).1 hw
      refine ⟨{i}, ⟨i, hi, rfl⟩, fun a ha hai ↦ ?_⟩
      obtain ⟨T, -, rfl⟩ := hALT.1 ha
      obtain ⟨j, hj, hji⟩ := hai
      rw [mem_singleton] at hji
      exact ⟨j, hj, hji ▸ hiw⟩
    · rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩ h
      obtain ⟨k, hk, hki⟩ := h _ (hALT.2 ⟨{j}, singleton_nonempty j, rfl⟩)
        ⟨j, mem_singleton_self j, mem_singleton_self j⟩
      rw [mem_singleton] at hk hki
      rw [← hki, hk]
      exact fun _ _ h ↦ h
  rw [hM.exhIEII_eq ⟨S, (hφ S).2 (hS.imp fun i hi ↦ ⟨hi, hi⟩), fun q hq ↦ ?_⟩]
  · ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      ext j
      have := h _ (hALT.2 ⟨{j}, singleton_nonempty j, rfl⟩)
      rw [hsingle] at this
      simpa using this
    · intro hw
      rw [hw]
      refine ⟨(hφ S).2 (hS.imp fun i hi ↦ ⟨hi, hi⟩), fun q hq ↦ ?_⟩
      obtain ⟨T, -, rfl⟩ := hALT.1 hq
      rw [hsingle]
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun ⟨i, hT, hS⟩ ↦ ⟨i, hS, hT⟩, fun ⟨i, hS, hT⟩ ↦ ⟨i, hT, hS⟩⟩
  · obtain ⟨T, -, rfl⟩ := hALT.1 hq
    rw [hsingle]
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun ⟨i, hT, hS⟩ ↦ ⟨i, hS, hT⟩, fun ⟨i, hS, hT⟩ ↦ ⟨i, hT, hS⟩⟩

theorem mem_disjunctions {m : Msg ι} :
    m ∈ disjunctions ↔ ∃ T : Finset ι, T.Nonempty ∧ m = (.or, T) := by
  simp [disjunctions, eq_comm]

-- the disjunctions true at a cell of `k` of the `n` atoms, those meeting it, number
-- `2 ^ n - 2 ^ (n - k)`
theorem card_filter_disjunctions (c : Cell ι) :
    (disjunctions.filter (· ~[truth] c)).card =
      2 ^ Fintype.card ι - 2 ^ (Fintype.card ι - c.card) := by
  have himg : disjunctions.filter (· ~[truth] c) =
      ((univ : Finset (Finset ι)).filter fun T ↦ ∃ i ∈ T, i ∈ c).image (.or, ·) := by
    ext m
    simp only [mem_filter, mem_disjunctions, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨T, -, rfl⟩, h⟩
      exact ⟨T, h, rfl⟩
    · rintro ⟨T, ⟨i, hi, hic⟩, rfl⟩
      exact ⟨⟨T, ⟨i, hi⟩, rfl⟩, i, hi, hic⟩
  have hdisj :
      ((univ : Finset (Finset ι)).filter fun T ↦ ¬ ∃ i ∈ T, i ∈ c) = (univ \ c).powerset := by
    ext T
    simp only [mem_filter, mem_univ, true_and, mem_powerset, not_exists, not_and]
    exact ⟨fun h i hi ↦ Finset.mem_sdiff.2 ⟨mem_univ i, h i hi⟩,
      fun h i hi ↦ (Finset.mem_sdiff.1 (h hi)).2⟩
  rw [himg, card_image_of_injective _ fun _ _ h ↦ (Prod.mk.inj h).2]
  have := card_filter_add_card_filter_not (s := (univ : Finset (Finset ι)))
    (fun T ↦ ∃ i ∈ T, i ∈ c)
  rw [hdisj, card_powerset, card_univ_sdiff, card_univ, Fintype.card_finset] at this
  omega

open Classical in
/-- **Three or more disjuncts** (§5.1). With at least three atoms, peeling the disjunctions by
probabilistic identification with the naive speaker at flat priors pairs each atom with the cell
where it alone holds and then stops: each remaining disjunction is true at two distinct cells of
two atoms, which the naive speaker treats alike, so no disjunction is strengthened. The
grammatical theory strengthens every one of them (`exhIEII_or`). -/
theorem peel_probMirrorIdentifies_of_three_le (h : 3 ≤ Fintype.card ι) :
    peel (ProbMirrorIdentifies (uniformOn Set.univ) (naiveSpeaker truth disjunctions))
        disjunctions univ = univ.image fun i ↦ ((.or, {i}), ({i} : Cell ι)) := by
  classical
  rw [peel_congr fun _ _ _ _ ↦ probMirrorIdentifies_uniformOn_naiveSpeaker_iff truth _]
  set C := CountIdentifies (truth (ι := ι)) disjunctions
  -- the naive speaker's comparison of two cells is the comparison of their sizes
  have hlt (t t' : Cell ι) : (disjunctions.filter (· ~[truth] t)).card <
      (disjunctions.filter (· ~[truth] t')).card ↔ t.card < t'.card := by
    rw [card_filter_disjunctions, card_filter_disjunctions,
      tsub_lt_tsub_iff_left_of_le (pow_le_pow_right₀ one_le_two tsub_le_self),
      Nat.pow_lt_pow_iff_right (by norm_num)]
    have := card_le_univ t
    have := card_le_univ t'
    omega
  have hC {Ms : Finset (Msg ι)} {Ts : Finset (Cell ι)} {m : Msg ι} {t : Cell ι} :
      C ↑Ms ↑Ts m t ↔ ∀ t' ∈ Ts, t' ≠ t → (m ∈ disjunctions ∧ m ~[truth] t) ∧
        (m ~[truth] t' → t.card < t'.card) := by
    simp only [C, CountIdentifies, Finset.mem_coe, hlt]
  have hne_of_true {T : Finset ι} {t : Cell ι} (h : (Connective.or, T) ~[truth] t) :
      t.Nonempty := let ⟨i, _, hi⟩ := h; ⟨i, hi⟩
  -- the first round pairs each atom with the cell where it alone holds
  have hU₁ : identified C disjunctions univ = univ.image fun i ↦ ((.or, {i}), ({i} : Cell ι)) := by
    ext ⟨m, t⟩
    simp only [mem_identified, mem_univ, true_and, mem_image, Prod.mk.injEq, hC]
    constructor
    · rintro ⟨hm, h⟩
      obtain ⟨T, ⟨i, hi⟩, rfl⟩ := mem_disjunctions.1 hm
      have ht : t = {i} := by
        by_contra hti
        obtain ⟨⟨-, htrue⟩, hcmp⟩ := h {i} trivial (Ne.symm hti)
        have := hcmp ⟨i, hi, mem_singleton_self i⟩
        have := card_pos.2 (hne_of_true htrue)
        simp only [card_singleton] at *
        omega
      subst ht
      refine ⟨i, ?_, rfl⟩
      congr 1
      ext j
      refine ⟨fun hj ↦ by rw [mem_singleton.1 hj]; exact hi, fun hj ↦ mem_singleton.2 ?_⟩
      by_contra hji
      have := (h {j} trivial (by simpa using hji)).2 ⟨j, hj, mem_singleton_self j⟩
      simp at this
    · rintro ⟨i, rfl, rfl⟩
      refine ⟨mem_disjunctions.2 ⟨{i}, singleton_nonempty i, rfl⟩, fun t' _ ht' ↦
        ⟨⟨mem_disjunctions.2 ⟨{i}, singleton_nonempty i, rfl⟩, i, mem_singleton_self i,
          mem_singleton_self i⟩, fun ⟨j, hj, hjt⟩ ↦ ?_⟩⟩
      rw [mem_singleton.1 hj] at hjt
      rw [card_singleton]
      by_contra hle
      exact ht' ((eq_singleton_iff_unique_mem.2 ⟨hjt, fun k hk ↦
        card_le_one.1 (not_lt.1 hle) k hk i hjt⟩))
  -- the second round identifies nothing
  have hfix : Function.IsFixedPt (step C) (step C ⟨∅, disjunctions, univ⟩) := by
    refine step_eq_self_of_identified_eq_empty (eq_empty_iff_forall_notMem.2 ?_)
    rintro ⟨m, t⟩ hp
    obtain ⟨hm, ht, h⟩ := mem_identified.1 hp
    simp only [step, hU₁, image_image, Function.comp_def, Finset.mem_sdiff, mem_image, mem_univ,
      true_and, not_exists] at hm ht h
    rw [hC] at h
    obtain ⟨hm, hm'⟩ := hm
    obtain ⟨T, hT, rfl⟩ := mem_disjunctions.1 hm
    have hT2 : 1 < T.card := by
      by_contra hle
      obtain ⟨i, rfl⟩ := card_eq_one.1 (le_antisymm (not_lt.1 hle) (card_pos.2 hT))
      exact hm' i rfl
    obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.1 hT2
    obtain ⟨k, -, hk⟩ := exists_mem_notMem_of_card_lt_card (s := {i, j}) (t := univ)
      (by rw [card_univ, card_pair hij]; omega)
    have hki : k ≠ i := fun e ↦ hk (by simp [e])
    have hkj : k ≠ j := fun e ↦ hk (by simp [e])
    have hpair (a b : ι) (hab : a ≠ b) : (({a, b} : Cell ι) ∈ univ \ univ.image fun l ↦ {l}) := by
      simp only [Finset.mem_sdiff, mem_univ, mem_image, true_and, not_exists]
      intro l hl
      have := congrArg card hl
      rw [card_singleton, card_pair hab] at this
      omega
    -- of the two cells {i, j} and {i, k}, one is not `t`
    obtain ⟨t', ht', hne, hmeet, hcard⟩ : ∃ t' : Cell ι, t' ∈ univ \ univ.image (fun l ↦ {l}) ∧
        t' ≠ t ∧ (Connective.or, T) ~[truth] t' ∧ t'.card = 2 := by
      by_cases hijt : ({i, j} : Cell ι) = t
      · refine ⟨{i, k}, hpair i k hki.symm, fun e ↦ hk ?_, ⟨i, hi, by simp⟩, card_pair hki.symm⟩
        have : k ∈ ({i, j} : Cell ι) := by rw [hijt, ← e]; simp
        exact this
      · exact ⟨{i, j}, hpair i j hij, hijt, ⟨i, hi, by simp⟩, card_pair hij⟩
    obtain ⟨⟨-, htrue⟩, hcmp⟩ := h t' ht' hne
    have h1 := hcmp hmeet
    have h0 := card_pos.2 (hne_of_true htrue)
    obtain ⟨l, rfl⟩ := card_eq_one.1 (show t.card = 1 by omega)
    exact ht l rfl
  have hcard : disjunctions.card ≠ 0 := card_ne_zero_of_mem (mem_disjunctions.2
    ⟨univ, univ_nonempty_iff.2 ((Fintype.card_pos_iff (α := ι)).1 (by omega)), rfl⟩)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard
  rw [peel, hn, Function.iterate_succ_apply, (hfix.iterate n).eq]
  simp [step, hU₁]

/-! #### Two atoms (§§2–4, §6) -/

-- §2.2, {*A*, *B*, *A and B*}
theorem peel_identifies_atoms_and :
    peel (Identifies truth) (insert (.and, univ) atoms) univ =
      {((.and, univ), univ), ((.or, {0}), {0}), ((.or, {1}), ({1} : Finset (Fin 2)))} := by
  decide

-- §3, {*A*, *B*}
theorem peel_identifies_atoms : peel (Identifies truth) (atoms (ι := Fin 2)) univ = ∅ := by
  decide

-- §3, {*A*, *B*}
theorem peel_mirrorIdentifies_atoms :
    peel (MirrorIdentifies truth) (atoms (ι := Fin 2)) univ =
      {((.or, {0}), {0}), ((.or, {1}), {1})} := by
  decide

-- §4.1
theorem peel_identifies_disjunctions :
    peel (Identifies truth) (disjunctions (ι := Fin 2)) univ = ∅ := by
  decide

-- §4.1
theorem peel_mirrorIdentifies_disjunctions :
    peel (MirrorIdentifies truth) (disjunctions (ι := Fin 2)) univ = ∅ := by
  decide

open Classical in
/-- **The conjunctive reading of disjunction** (§4.2). With the naive speaker and flat priors,
peeling by probabilistic identification first pairs *A* with the cell where only `A` holds and
*B* with the cell where only `B` holds, and then pairs *A or B* with the cell where both hold.
Neither identification (2) nor its mirror image (4) gets started on these alternatives. -/
theorem peel_probMirrorIdentifies_two :
    peel (ProbMirrorIdentifies (uniformOn Set.univ) (naiveSpeaker truth disjunctions))
        (disjunctions (ι := Fin 2)) univ =
      {((.or, {0}), {0}), ((.or, {1}), {1}), ((.or, univ), univ)} := by
  rw [peel_congr fun _ _ _ _ ↦ probMirrorIdentifies_uniformOn_naiveSpeaker_iff truth _]
  decide

private theorem cell_two (c : Cell (Fin 2)) : c = ∅ ∨ c = {0} ∨ c = {1} ∨ c = univ := by
  revert c; decide

private theorem naiveSpeaker_two_real (c : Cell (Fin 2)) (m : Msg (Fin 2)) :
    (naiveSpeaker truth disjunctions c).real {m} =
      if m ∈ disjunctions ∧ m ~[truth] c then
        ((if c = univ then 3 else if c = ∅ then 0 else 2 : ℕ) : ℝ)⁻¹ else 0 := by
  rw [naiveSpeaker_real_singleton,
    show (disjunctions.filter (· ~[truth] c)).card =
      if c = univ then 3 else if c = ∅ then 0 else 2 by revert c; decide]

/-- The listener of the naive speaker at a flat prior, on two atoms. -/
local notation "L₂" =>
  RSA.listener (uniformOn Set.univ) (naiveSpeaker truth (disjunctions (ι := Fin 2)))

-- fn. 22
theorem listener_or_tie :
    (L₂ (.or, univ)).real {{0}} = (L₂ (.or, univ)).real {{1}} ∧
      (L₂ (.or, univ)).real {univ} < (L₂ (.or, univ)).real {{0}} := by
  refine ⟨le_antisymm (not_lt.1 ?_) (not_lt.1 ?_), ?_⟩
  all_goals rw [RSA.listener_real_singleton_lt_iff_of_forall_eq _ _ uniformOn_univ_singleton_eq
    uniformOn_univ_singleton_ne_zero, naiveSpeaker_two_real, naiveSpeaker_two_real]
  · simp +decide
  · simp +decide
  · simp +decide
    norm_num

/-- **Sensitivity to priors** (§6.1, (22)). Any prior on which the cell where only `B` holds is
likelier than the cell where only `A` holds, and not too much less likely than the cell where
both hold, makes *A or B* identify the cell where only `B` holds in the first round of peeling,
so that the disjunction is strengthened to the wrong cell. The paper's case, where the other two
cells are each 0.9999 times as likely as it, is one. -/
theorem probMirrorIdentifies_or_of_prior {μ : Measure (Cell (Fin 2))} [IsFiniteMeasure μ]
    (h₁ : μ.real {{0}} < μ.real {{1}}) (h₂ : 2 * μ.real {univ} < 3 * μ.real {{1}})
    (Ms : Set (Msg (Fin 2))) :
    ProbMirrorIdentifies μ (naiveSpeaker truth disjunctions) Ms Set.univ (.or, univ) {1} := by
  have h₀ : 0 < μ.real {{1}} := measureReal_nonneg.trans_lt h₁
  rw [probMirrorIdentifies_iff]
  intro c _ hc
  rcases cell_two c with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hc
    | (simp only [naiveSpeaker_two_real]
       simp +decide
       linarith)

open Classical in
-- (22)
theorem or_mem_peel_of_prior {μ : Measure (Cell (Fin 2))} [IsFiniteMeasure μ]
    (h₁ : μ.real {{0}} < μ.real {{1}}) (h₂ : 2 * μ.real {univ} < 3 * μ.real {{1}}) :
    ((.or, univ), {1}) ∈
      peel (ProbMirrorIdentifies μ (naiveSpeaker truth disjunctions)) disjunctions univ :=
  identified_subset_peel _ _ (mem_identified.2 ⟨by decide, mem_univ _, by
    simpa using probMirrorIdentifies_or_of_prior h₁ h₂ ↑(disjunctions (ι := Fin 2))⟩)

-- (22)
theorem probMirrorIdentifies_atom_of_prior {μ : Measure (Cell (Fin 2))} [IsFiniteMeasure μ]
    (h : 3 * μ.real {{0}} < 2 * μ.real {univ}) (Ms : Set (Msg (Fin 2))) :
    ProbMirrorIdentifies μ (naiveSpeaker truth disjunctions) Ms Set.univ (.or, {0}) univ := by
  have h₀ : 0 < μ.real {univ} := by nlinarith [measureReal_nonneg (μ := μ) (s := {{0}})]
  rw [probMirrorIdentifies_iff]
  intro c _ hc
  rcases cell_two c with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hc
    | (simp only [naiveSpeaker_two_real]
       simp +decide
       linarith)

/-! #### Three atoms (§5) -/

open Classical in
-- (19)
theorem peel_probMirrorIdentifies_vanRooij :
    peel (ProbMirrorIdentifies (uniformOn Set.univ) (naiveSpeaker truth vanRooij))
        (vanRooij (ι := Fin 3)) univ =
      {((.or, {0}), {0}), ((.or, {1}), {1}), ((.or, {2}), {2}), ((.and, {0, 1}), {0, 1}),
        ((.and, {0, 2}), {0, 2}), ((.and, {1, 2}), {1, 2}), ((.or, univ), univ)} := by
  rw [peel_congr fun _ _ _ _ ↦ probMirrorIdentifies_uniformOn_naiveSpeaker_iff truth _]
  decide

open Classical in
-- fn. 31: with the two-way disjunctions added, *A or B or C* still identifies the cell where all
-- three hold; with the three-way conjunction added, it is paired only with the cell where none
-- holds, at which it is false, by the vacuous identification of the last remaining cell
theorem peel_probMirrorIdentifies_vanRooij_insert :
    ((.or, univ), univ) ∈ peel (ProbMirrorIdentifies (uniformOn Set.univ)
        (naiveSpeaker truth (vanRooij ∪ (univ.filter (·.card = 2)).image (.or, ·))))
        (vanRooij (ι := Fin 3) ∪ (univ.filter (·.card = 2)).image (.or, ·)) univ ∧
      (peel (ProbMirrorIdentifies (uniformOn Set.univ)
        (naiveSpeaker truth (insert (.and, univ) vanRooij)))
        (insert (.and, univ) (vanRooij (ι := Fin 3))) univ).filter (·.1 = (.or, univ)) =
        {((.or, univ), ∅)} ∧ ¬ (Connective.or, univ) ~[truth] (∅ : Cell (Fin 3)) := by
  rw [peel_congr fun _ _ _ _ ↦ probMirrorIdentifies_uniformOn_naiveSpeaker_iff truth _,
    peel_congr fun _ _ _ _ ↦ probMirrorIdentifies_uniformOn_naiveSpeaker_iff truth _]
  decide

/-! #### Franke's iterated best response on three atoms (footnotes 30 and 33)

Franke's light system ([franke-2011], `Franke2011.receiverChain`, `Franke2011.senderChain`) is
iterated best response at flat priors, its message type here the disjunctions and its meanings
their extensions. -/


/-- The meanings of Franke's game on the disjunctions of three atoms. -/
local notation "den₃" => extensionOn (ι := Fin 3) disjunctions

-- footnotes 30 and 33
theorem franke_naiveSpeaker :
    Franke2011.receiverStep den₃ (Franke2011.senderChain den₃ 2) ⟨(.or, univ), by decide⟩ =
        {{0, 1}, {0, 2}, {1, 2}} ∧
      Franke2011.receiverStep den₃ (Franke2011.senderChain den₃ 2) ⟨(.or, {0, 1}), by decide⟩ =
        {{0, 1}, {0, 2}, {1, 2}} ∧
      Franke2011.senderChain den₃ 3 = Franke2011.senderChain den₃ 2 := by
  decide +kernel

-- footnote 30
theorem franke_naiveHearer :
    (∀ c, (⟨(.or, univ), by decide⟩ : {m : Msg (Fin 3) // m ∈ disjunctions}) ∉
        Franke2011.senderStep den₃ (Franke2011.receiverChain den₃ 2) c) ∧
      Franke2011.receiverChain den₃ 2 ⟨(.or, univ), by decide⟩ = extension (.or, univ) ∧
      Franke2011.receiverChain den₃ 2 ⟨(.or, {0, 1}), by decide⟩ =
        {{0, 1}, {0, 2}, {1, 2}, univ} ∧
      Franke2011.receiverChain den₃ 3 = Franke2011.receiverChain den₃ 2 := by
  decide +kernel

end Disjunction

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

/-- Whether a message holds at a cell. -/
def Msg.Holds : Msg → Cell → Prop
  | .some, c => c ≠ .none
  | .many, c => c = .manyNotAll ∨ c = .all
  | .all, c => c = .all

instance : ∀ m c, Decidable (Msg.Holds m c)
  | .some, c => inferInstanceAs (Decidable (c ≠ .none))
  | .many, c => inferInstanceAs (Decidable (c = .manyNotAll ∨ c = .all))
  | .all, c => inferInstanceAs (Decidable (c = .all))

/-- The truth relation of the scale. -/
def truth : SetRel Msg Cell := {p | p.1.Holds p.2}

instance : DecidablePred (· ∈ truth) := fun p ↦ inferInstanceAs (Decidable (p.1.Holds p.2))

-- §2.2: three rounds
theorem peel_identifies :
    peel (Identifies truth) univ univ =
      {(.all, .all), (.many, .manyNotAll), (.some, .someNotMany)} := by
  decide

open Classical in
-- (14): one round
theorem identified_probMirrorIdentifies :
    identified (ProbMirrorIdentifies (uniformOn Set.univ) (naiveSpeaker truth univ)) univ univ =
        {(.all, .all), (.many, .manyNotAll), (.some, .someNotMany)} ∧
      peel (ProbMirrorIdentifies (uniformOn Set.univ) (naiveSpeaker truth univ)) univ univ =
        {(.all, .all), (.many, .manyNotAll), (.some, .someNotMany)} := by
  refine ⟨?_, ?_⟩
  · rw [show identified (ProbMirrorIdentifies (uniformOn Set.univ) (naiveSpeaker truth univ))
        univ univ = identified (CountIdentifies truth univ) univ univ from
      filter_congr fun _ _ ↦ probMirrorIdentifies_uniformOn_naiveSpeaker_iff truth univ]
    decide
  · rw [peel_congr fun _ _ _ _ ↦ probMirrorIdentifies_uniformOn_naiveSpeaker_iff truth univ]
    decide

private theorem naiveSpeaker_real (c : Cell) (m : Msg) :
    (naiveSpeaker truth univ c).real {m} =
      if m ~[truth] c then ((match c with
        | .none => 0 | .someNotMany => 1 | .manyNotAll => 2 | .all => 3 : ℕ) : ℝ)⁻¹ else 0 := by
  rw [naiveSpeaker_real_singleton, show (univ.filter (· ~[truth] c)).card = match c with
    | .none => 0 | .someNotMany => 1 | .manyNotAll => 2 | .all => 3 by revert c; decide]
  simp

-- (21)
theorem probMirrorIdentifies_some_of_prior {μ : Measure Cell} [IsFiniteMeasure μ]
    (h₁ : 2 * μ.real {.someNotMany} < μ.real {.manyNotAll})
    (h₂ : 2 * μ.real {.all} < 3 * μ.real {.manyNotAll}) (Ms : Set Msg) :
    ProbMirrorIdentifies μ (naiveSpeaker truth univ) Ms Set.univ .some .manyNotAll := by
  have h₀ : 0 < μ.real {.manyNotAll} := by
    nlinarith [measureReal_nonneg (μ := μ) (s := {Cell.someNotMany})]
  rw [probMirrorIdentifies_iff]
  rintro (_ | _ | _ | _) - h
  all_goals first
    | exact absurd rfl h
    | (simp +decide only [naiveSpeaker_real]
       norm_num
       linarith)

end Scale

/-! ### Infinite scales (§3)

Read as *at least*, the numerals partition the context set into the cells where John has exactly
`k` children. No numeral is true at a single cell, so identification (2) never starts, while each
numeral is the only one true at its own cell once the smaller numerals are peeled, so mirror-image
identification (4) peels the numerals one by one. Under a downward-entailing operator the truth
relation is the inverse one, and the two notions trade places. -/

namespace Numerals

/-- *John has `n` children*, read as *at least `n`*, is true at the cells where he has `k ≥ n`
children. -/
def atLeast : SetRel ℕ ℕ := {p | p.1 ≤ p.2}

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
theorem identifies_inv (n : ℕ) (Ts : Set ℕ) : Identifies atLeast.inv Ts {m | n ≤ m} n n :=
  mirrorIdentifies n Ts

-- §3, under a downward-entailing operator
theorem not_mirrorIdentifies_inv (Ms : Set ℕ) (n k : ℕ) :
    ¬ MirrorIdentifies atLeast.inv Set.univ Ms k n :=
  not_identifies Ms n k

end Numerals

end FoxKatzir2021
