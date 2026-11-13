module

public import Linglib.Logic.Assignment
public import Linglib.Data.Examples.Ogihara1989
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.PredicateAbstraction
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Events.Basic
public import Linglib.Semantics.Tense.Embedding
public import Linglib.Semantics.Tense.Reichenbach
public import Linglib.Syntax.Tree.Command
public import Studies.Partee1973

/-!
# Ogihara (1989): Temporal Reference in English and Japanese

A tense is an existential quantifier over times that [the context restricts to a salient
interval](##restricted_iff_exists_past), not a pronoun. English also has a rule at LF, after
Quantifier Raising, that deletes a tense under a local tense feature of the same value, and
Japanese does not; [composing the cells of the resulting LFs gives the readings of the
sentences](##rows_readings). A relative raised above the matrix tense escapes the rule and [covers
its narrow scope readings](##Model.sawWide_of_sawNarrow). A theory with no rule [wrongly dates what
*would* describes before the speech time](##triple_index_precedes_speech). A present under a past
is a report de re about a state, and [the state can tell apart two futures of one saying where an
attitude alone cannot](##minimal_pair), if the interval it occupies depends on the world.

## Implementation notes

* The fragment translates each syntactic rule into intensional logic, and the LFs are composed
  by those rules: a clause is a property of times, which the complementizer (9), the relative
  pronoun (12), the rule for a noun phrase raised to S (13a) and the matrix rule (1) close; a noun
  phrase, a trace included, is a quantifier; and a tense is its Aux. Individuals are rigid and a
  predicate takes its index of a world and an interval last, so that the intension and extension
  operators of the translations disappear and a rule that applies one translation to the
  intension of another is Functional Application. A transitive verb takes a quantifier and is
  extensional in it, as the derivations write `see'(j, x)`. The LFs are written out after QR; QR
  is not an operation here.
* Chapter 2's *command* is `sCommand` and chapter 3's *c-command* is `RoseTree.cCommand`, so the two
  statements of the rule are one definition, `Deletable`, at two relations. The auxiliaries are
  stacked in the order of their scope, the alternative p. 259 allows to the flat Aux with its
  Feature Percolation Convention. The two differ where a tense shares an Aux with *have + en*, as
  in *John had come*, where the perfect of a flat Aux c-commands its own tense; no row tests this. A
  VP-adjoined object scopes over the subject, harmlessly as those subjects are names. `Word.null`
  has no feature where pp. 259-267 print Ø with one, which changes no prediction, since a deleted
  tense shares the value of its local feature.
* `rows_readings` composes `Word.cell` along an LF and does not go through `Model.Holds`.
  `position_mem_cell` is the one-step link between them, and the `holds_` lemmas check LFs against
  their printed translations.
* The subset relation $\subseteq$ is `≤` of `NonemptyInterval`, and $<$ is
  `NonemptyInterval.Precedes`, which on closed intervals is the non-abutting order of p. 204 on
  dense time. The Japanese present has only its present translation here, not its future one
  (p. 211), so "simultaneous reading only" on (2b) is read as excluding the shifted reading. The
  aspect of the complement, which a simultaneous reading needs stative (p. 72), is not modelled, as
  the fragment does not either (p. 200).
* The second fragment is stated at its translations (64') and (69), which are premises here. The
  interval a state occupies depends on the world, which rule 16 (p. 334) allows and p. 332 does not
  settle; [with a rigid interval (64') cannot separate the cases of (24)](##doubleAccess_rigid_iff),
  and `Event.TemporalTrace`, which has no world, gives the times of events only.

## TODO

* A theorem that composing the cells agrees with `Model.Holds` on every LF.
* QR as an operation, so that a sentence's LFs are derived, and Aux copying (pp. 337-338), so that
  (64') and (69) are outputs.
* Hypotheses 3 to 5 of chapter 4, with the counterfactual of (48), the case against (52) on
  pp. 315-318, and the discriminators (50a,b) on p. 314 and (41) on p. 305.
* The anchoring conditions for tense of section 2.3.1, and the interaction of QR, intensionality and
  scope of section 2.2, with *seek* and the examples (62) and (66).
* The temporal adverbial clauses of section 2.4.4, and the second Japanese fragment.

## References

* [ogihara-1989]
* [partee-1973]
* [reichenbach-1947]
* [langacker-1969]
* [davidson-1967]
-/

@[expose] public section

namespace Ogihara1989

open Interpreter ModalLogic Tense Partee1973 PhraseStructure
  PhraseStructure.Tree Core.Order
open scoped Assignment Denotes SetRel

section ReferenceInterval

variable {T : Type*} [LinearOrder T] {P : NonemptyInterval T → Prop} {K σ : NonemptyInterval T}
  {g : ℕ → NonemptyInterval T} {n : ℕ}

/-- The past restricted to the salient interval `K` holds when the clause held at a past
subinterval of `K`, as *Yes, I saw her* (`Examples.ex_1_57`) says of the day, (58) of chapter 1. It
is Partee's past tense with its index bound by an existential quantifier over the subintervals of
`K`. -/
theorem restricted_iff_exists_past :
    ◇[Allen.toSetRel Allen.precedes] (fun t ↦ t ≤ K ∧ P t) σ ↔
      ∃ t ≤ K, Λ[n] (Past n P σ) g t := by
  simp [Past, Diamond, and_left_comm]

/-! ### The stove

*I didn't turn off the stove* (`Examples.ex_1_46a`), with `P` the times at which the speaker turns
off the stove and the time of the tense's index the salient interval. The sentence says that this
interval is past and has no subinterval at which the speaker turned off the stove. -/

-- (56): the salient interval is past, and the past restricted to it is denied
theorem no_subinterval_iff_not_restricted :
    Past n (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g ↔
      σ ~[Allen.toSetRel Allen.precedes] g n ∧
        ¬ ◇[Allen.toSetRel Allen.precedes] (fun t ↦ t ≤ g n ∧ P t) σ :=
  ⟨fun h ↦ ⟨h.1, fun ⟨t, _, hle, hP⟩ ↦ h.2 ⟨t, hle, hP⟩⟩, fun h ↦ ⟨h.1, fun ⟨t, hle, hP⟩ ↦
    h.2 ⟨t, Allen.mem_toSetRel_precedes.2 (NonemptyInterval.precedes_of_le_of_precedes hle
      (Allen.mem_toSetRel_precedes.1 h.1)), hle, hP⟩⟩⟩

-- p. 49: a speaker who turned off the stove at no subinterval did not at the interval
theorem no_subinterval_entails_deictic (h : Past n (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g) :
    Past n (fun t ↦ ¬ P t) σ g :=
  ⟨h.1, fun hP ↦ h.2 ⟨_, le_rfl, hP⟩⟩

-- p. 49: a speaker who turned off the stove within the interval did not at the interval, so
-- the referential reading is true where the sentence is false
theorem deictic_too_weak :
    ∃ (σ : NonemptyInterval ℤ) (g : ℕ → NonemptyInterval ℤ)
      (P : NonemptyInterval ℤ → Prop),
      Past 0 (fun t ↦ ¬ P t) σ g ∧ ¬ Past 0 (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g :=
  ⟨.pure 10, fun _ ↦ ⟨(0, 5), by decide⟩, (· = .pure 3),
    ⟨Allen.mem_toSetRel_precedes.2 (by decide), by decide⟩,
    fun h ↦ h.2 ⟨.pure 3, by decide, rfl⟩⟩

-- (46b) entails (56)
theorem never_entails_no_subinterval (hn : σ ~[Allen.toSetRel Allen.precedes] g n)
    (h : ¬ ◇[Allen.toSetRel Allen.precedes] P σ) : Past n (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g :=
  no_subinterval_iff_not_restricted.2 ⟨hn, fun ⟨t, ht, _, hP⟩ ↦ h ⟨t, ht, hP⟩⟩

-- p. 41: the sentence is true of a speaker who turned off the stove before the interval
theorem never_too_strong :
    ∃ (σ : NonemptyInterval ℤ) (g : ℕ → NonemptyInterval ℤ)
      (P : NonemptyInterval ℤ → Prop),
      Past 0 (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g ∧ ◇[Allen.toSetRel Allen.precedes] P σ := by
  refine ⟨.pure 10, fun _ ↦ ⟨(5, 6), by decide⟩, (· = .pure 1),
    ⟨Allen.mem_toSetRel_precedes.2 (by decide), ?_⟩, .pure 1,
    Allen.mem_toSetRel_precedes.2 (by decide), rfl⟩
  rintro ⟨t, ht, rfl⟩
  exact absurd ht (by decide)

end ReferenceInterval

/-! ### Logical forms

An LF is a tree with the node of each translation rule, so that the two statements of the
dissertation's rule read off it as they stand. -/

/-- The names of the fragment. A pronoun is the name it is bound to. -/
inductive Name
  | john | mary | bill | speaker | addressee | everybody
  deriving DecidableEq

/-- The one-place predicates of the fragment: common nouns, intransitive verbs and adjectives have
one semantic type, and `Cat` tells them apart. -/
inductive Pred
  | man | fish | ill | inAustin | laughing | supporter | holding | alive | ignorant | magicTricks
  | win | come | wellKnown
  deriving DecidableEq

/-- The transitive verbs of the fragment. -/
inductive TV
  | see | meet | buy | amuse
  deriving DecidableEq

/-- The words of the fragment that take a clausal complement, verbs and the noun *claim*, of one
semantic type. An object of *tell* or *ask* is left out, since no tense depends on it. -/
inductive Att
  | say | claim | think | tell | promise | ask | claimNoun
  deriving DecidableEq

/-- The terminals of an LF. Each morpheme that introduces a time carries the index `n` of its
reference interval $t_{Rn}$. -/
inductive Word
  /-- The past tense morpheme, *-ed* in English and *-ta* in Japanese. -/
  | past (n : ℕ)
  /-- The English present tense morpheme, which denotes the speech time. -/
  | pres
  /-- The empty tense that tense deletion leaves. -/
  | null
  /-- The Japanese present tense morpheme *-ru* in its present meaning. -/
  | ru
  /-- The future auxiliary. -/
  | woll (n : ℕ)
  /-- The perfect in its preterit meaning. -/
  | perf (n : ℕ)
  /-- The infinitive marker with a future meaning. -/
  | inf (n : ℕ)
  /-- The adjective *earlier*. -/
  | earlier (n : ℕ)
  /-- The adjective *current*. -/
  | current
  /-- A name. -/
  | name (c : Name)
  /-- A one-place predicate. -/
  | pred (c : Pred)
  /-- A transitive verb. -/
  | tv (c : TV)
  /-- A word with a clausal complement. -/
  | att (c : Att)
  /-- The indefinite article. -/
  | a
  /-- The possessive morpheme. -/
  | poss
  /-- The relative pronoun, in the complementizer of its clause. -/
  | who
  /-- The complementizer. -/
  | that
  deriving DecidableEq

namespace Word

/-- The tense feature of a word, as the cell it denotes (p. 178): [+past] on the past, the perfect
and *earlier*, [-past] on the present. -/
def feature? : Word → Option (Finset Ordering)
  | past _ | perf _ | earlier _ => some ⟦Tense.past⟧
  | pres | ru => some nonpast
  | _ => none

/-- The tense morphemes, the words that the rule can delete. -/
def IsTense : Word → Prop
  | past _ | pres | ru => True
  | _ => False

instance : DecidablePred IsTense := fun w ↦ by cases w <;> unfold IsTense <;> infer_instance

/-- The cell of a word: where it places a time against the time at which it is evaluated. The
English present has none, since it denotes the speech time wherever it is evaluated. -/
def cell : Word → Finset Ordering
  | past _ | perf _ | earlier _ => ⟦Tense.past⟧
  | null | ru | current => ⟦Tense.present⟧
  | woll _ | inf _ => ⟦Tense.future⟧
  | _ => ⊥

/-- The words that introduce a time. -/
def IsTime (w : Word) : Prop := w = pres ∨ w.cell ≠ ⊥

instance : DecidablePred IsTime := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

end Word

/-- An LF is a constituency tree over these terminals. -/
abbrev LF := Tree Cat Word

/-- The positions of the words of an LF that satisfy a predicate, in the order of the yield. -/
def wordPositions (t : LF) (P : Word → Prop) [DecidablePred P] : List TreePath :=
  (t.positionedTerminals.filter (P ·.2.2)).map (·.1)

/-- The word at a position of an LF. -/
def wordAt? (t : LF) (p : TreePath) : Option Word := (t.positionedTerminals.lookup p).map (·.2)

/-- The deepest position of a word in an LF, the lowest of the occurrences of a tense. -/
def lowestOf? (t : LF) (w : Word) : Option TreePath :=
  (wordPositions t (· = w)).argmax (·.toList.length)

/-- The tense feature at a position of an LF. -/
def featureAt? (t : LF) (p : TreePath) : Option (Finset Ordering) :=
  (wordAt? t p).bind Word.feature?

/-- The positions of the tense morphemes of an LF. -/
def tenses (t : LF) : Finset TreePath := (wordPositions t Word.IsTense).toFinset

/-- The positions of the tense features of an LF. -/
def features (t : LF) : Finset TreePath := (wordPositions t (·.feature?.isSome)).toFinset

/-- A tense `b` can be deleted when something in `F` is local for it and has the value of its
feature: it commands `b` under `R`, and no other member of `F` that it commands commands `b`. A
node commands itself on the reflexive relations of `Syntax/Command.lean`, so *other* excludes `b`
as well as the commander. -/
def Deletable (R : SetRel TreePath TreePath) (F : Finset TreePath) (t : LF) (b : TreePath) : Prop :=
  b ∈ tenses t ∧ ∃ a ∈ F, a ≠ b ∧ a ~[R] b ∧ featureAt? t a = featureAt? t b ∧
    ∀ c ∈ F, c ≠ a → c ≠ b → a ~[R] c → ¬ c ~[R] b

instance {R : SetRel TreePath TreePath} [∀ a b, Decidable (a ~[R] b)] {F : Finset TreePath}
    {t : LF} {b : TreePath} : Decidable (Deletable R F t b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The rule of chapter 2: delete a tense under an occurrence of the same morpheme that is local for
it, where a tense commands what the first S above it dominates. -/
abbrev TenseDeletable (t : LF) : TreePath → Prop := Deletable (sCommand t) (tenses t) t

/-- The rule of chapter 3: delete a tense morpheme whose feature has the value of its local tense
feature, where a feature c-commands what the first branching node above it dominates. -/
abbrev TenseFeatureDeletable (t : LF) : TreePath → Prop :=
  Deletable (RoseTree.cCommand t) (features t) t

/-- The LFs one application of the rule of chapter 3 gives, each with an empty tense. -/
def deletions (t : LF) : List LF :=
  ((wordPositions t Word.IsTense).filter (TenseFeatureDeletable t)).map fun b ↦
    t.replaceAt b.toList (Tree.terminal .Aux .null)

/-- One application of the rule of chapter 3, which is optional and may apply again. -/
abbrev Deletes (t t' : LF) : Prop := t' ∈ deletions t

/-- The LFs at most `n` applications of the rule give. -/
def lfsFrom : ℕ → LF → List LF
  | 0, t => [t]
  | n + 1, t => t :: (deletions t).flatMap (lfsFrom n)

/-! ### The shapes of the LFs

[S Tns (woll) (have + en) NP VP], with the auxiliaries in the order of their scope and the subject
below them, as rule (40.1) interprets it. -/

/-- A clause with a tense, further auxiliaries each over the next, and an untensed body. -/
def clause (t : Word) (ws : List Word) (b : LF) : LF :=
  .node .S [.terminal .Aux t, ws.foldr (fun w b ↦ .node .Aux [.terminal .Aux w, b]) b]

/-- A name as a subject. -/
def np (x : Name) : LF := .terminal .N (.name x)

/-- An untensed sentence, a subject and a predicate. -/
def untensed (subj vp : LF) : LF := .node .V [subj, vp]

/-- An intransitive predicate of a subject. -/
def intrans (subj : LF) (c : Pred) : LF := untensed subj (.terminal .V (.pred c))

/-- A verb with a clausal complement. -/
def complement (v : Att) (s : LF) : LF :=
  .node .V [.terminal .V (.att v), .node .C [.terminal .C .that, s]]

/-- *a* with a noun and a relative clause, whose relative pronoun binds the trace `k`. -/
def aNoun (n : Pred) (k : ℕ) (s : LF) : LF :=
  .node .N [.terminal .Det .a, .node .N [.terminal .N (.pred n),
    .node .C [.terminal .C .who, .bind k .C s]]]

/-- The clause of a relative whose subject is the trace `k`. -/
def relClause (k : ℕ) (t : Word) (ws : List Word) (c : Pred) : LF :=
  clause t ws (intrans (.trace k .N) c)

/-- A transitive verb with the trace `k` as its object and a subject. -/
def tvTrace (subj : LF) (v : TV) (k : ℕ) : LF :=
  untensed subj (.node .V [.terminal .V (.tv v), .trace k .N])

/-- The object `o` raised to the VP, within the scope of the tense. -/
def vpAdjoined (o : LF) (k : ℕ) (subj : LF) (v : TV) : LF :=
  .adjoin .V [o, .bind k .V (tvTrace subj v k)]

/-- A noun phrase raised to the S, outside the scope of the tense of `s`. -/
def raised (o : LF) (k : ℕ) (s : LF) : LF := .adjoin .S [o, .bind k .S s]

/-- *John said that Mary was in Austin* and its kin: a matrix clause over a complement. -/
def report (t : Word) (ws : List Word) (x : Name) (v : Att) (t' : Word) (ws' : List Word)
    (y : Name) (c : Pred) : LF :=
  clause t ws (untensed (np x) (complement v (clause t' ws' (intrans (np y) c))))

/-- *John said that Mary was ill* with the tense `t` in the complement, (1a) and (2a,b) of chapter
2, and in (49) with the empty tense. -/
def saidIll (t : Word) : LF := report (.past 1) [] .john .say t [] .mary .ill

/-- *John saw a man who was laughing* with the relative raised to the S, (46a'). -/
def sawWide (t : Word) : LF :=
  raised (aNoun .man 1 (relClause 1 t [] .laughing)) 0
    (clause (.past 1) [] (tvTrace (np .john) .see 0))

/-- *John saw a man who was laughing* with the relative raised to the VP, (46b') and (46c'). -/
def sawNarrow (t : Word) : LF :=
  clause (.past 1) [] (vpAdjoined (aNoun .man 1 (relClause 1 t [] .laughing)) 0 (np .john) .see)

/-- *John said that he would buy a fish that was still alive*, (37), with the tenses of the
complement and of the relative clause. -/
def saidFish (t t' : Word) : LF :=
  clause (.past 1) [] (untensed (np .john) (complement .say (clause t [.woll 3]
    (vpAdjoined (aNoun .fish 1 (relClause 1 t' [] .alive)) 0 (np .john) .buy))))

/-- (37) with the relative raised over every tense. -/
def saidFishWide : LF :=
  raised (aNoun .fish 1 (relClause 1 (.past 4) [] .alive)) 0
    (clause (.past 1) [] (untensed (np .john) (complement .say
      (clause (.past 2) [.woll 3] (tvTrace (np .john) .buy 0)))))

/-- *John met a man who will become his great supporter*, (42b), with the relative raised to the
S, (44). -/
def metWide : LF :=
  raised (aNoun .man 1 (relClause 1 .pres [.woll 3] .supporter)) 0
    (clause (.past 2) [] (tvTrace (np .john) .meet 0))

/-- The relative of (42) raised to the VP, with the tense `t` of *will* or *would*, (45) and
(43). -/
def metNarrow (t : Word) : LF :=
  clause (.past 2) [] (vpAdjoined (aNoun .man 1 (relClause 1 t [.woll 3] .supporter)) 0 (np .john)
    .meet)

/-- The possessive noun phrase of (60) and (61), with an adjective and a noun complement. -/
def claimNP (adj t : Word) : LF :=
  .node .N [.node .Det [np .john, .terminal .Det .poss],
    .node .N [.terminal .Adj adj, .node .N [.terminal .N (.att .claimNoun),
      .node .C [.terminal .C .that, clause t [.woll 3] (intrans (np .mary) .win)]]]]

/-- *John's earlier claim that Mary would win the prize is well-known*, (60b). -/
def claimClause (adj t : Word) : LF :=
  clause .pres [] (.node .V [claimNP adj t, .terminal .V (.pred .wellKnown)])

/-- *John met a man who would buy a fish which was still alive*, (70'). -/
def metBuyer : LF :=
  clause (.past 1) [] (vpAdjoined (aNoun .man 1 (clause (.past 2) [.woll 3]
    (vpAdjoined (aNoun .fish 5 (relClause 5 (.past 4) [] .alive)) 6 (.trace 1 .N) .buy))) 0
    (np .john) .meet)

-- (27a), (46a): "The Tense Deletion Rule does not apply. (The condition is not met.)"
theorem frozen_sawWide : ∃ b ∈ lowestOf? (sawWide (.past 2)) (.past 2),
    ¬ TenseDeletable (sawWide (.past 2)) b ∧ ¬ TenseFeatureDeletable (sawWide (.past 2)) b := by
  decide

-- (34) with its relative raised: the relative's tense is the deepest `.pres`, not the last
example : lowestOf? (raised (aNoun .man 1 (relClause 1 .pres [] .holding)) 0
    (clause .pres [.woll 1] (tvTrace (np .john) .meet 0))) .pres = some ⟨[0, 1, 1, 1, 0, 0]⟩ := by
  decide

-- (49)
theorem deletes_saidIll : Deletes (saidIll (.past 2)) (saidIll .null) := by decide

-- (27b), (46b)
theorem deletes_sawNarrow : Deletes (sawNarrow (.past 2)) (sawNarrow .null) := by decide

-- (37'): both lower pasts are deleted
theorem deletes_saidFish :
    Relation.ReflTransGen Deletes (saidFish (.past 2) (.past 4)) (saidFish .null .null) :=
  .head (by decide : Deletes _ (saidFish .null (.past 4))) (.single (by decide))

-- (59), (60b) and note 54 of chapter 2: the first rule misses the triggers that are not tenses
theorem tenseDeletable_misses_triggers :
    ∀ x ∈ [(report .pres [.woll 1, .perf 2] .john .claim (.past 3) [] .john .ill, Word.past 3),
        (claimClause (.earlier 1) (.past 2), .past 2)],
      ∃ b ∈ lowestOf? x.1 x.2, ¬ TenseDeletable x.1 b ∧ TenseFeatureDeletable x.1 b := by
  decide

-- (60b), (61), pp. 131-132: *earlier* triggers the rule and *current* does not
theorem current_not_trigger : ∃ b ∈ lowestOf? (claimClause .current (.past 2)) (.past 2),
    ¬ TenseFeatureDeletable (claimClause .current (.past 2)) b := by
  decide

-- p. 140: the rule generates (70'), which the consultants reject; p. 142 keeps the rule knowingly
theorem rule_generates_metBuyer :
    (∃ b ∈ lowestOf? metBuyer (.past 4), TenseFeatureDeletable metBuyer b) ∧
      (∃ b ∈ lowestOf? metBuyer (.past 2), TenseFeatureDeletable metBuyer b) ∧
      Examples.ex_2_70.readings = [("simultaneous", .unacceptable)] := by
  decide

/-! ### Interpretation -/

/-- The index of evaluation is a world and an interval. -/
abbrev Index (W T : Type*) [LE T] := W × NonemptyInterval T

/-- The basic types: individuals, intervals and indices. -/
inductive Atom
  | e | i | s
  deriving DecidableEq

/-- The domains of the basic types. -/
abbrev Dom (E W T : Type) [LE T] : Atom → Type
  | .e => E
  | .i => NonemptyInterval T
  | .s => Index W T

/-- The type of individuals. -/
abbrev ent : Ty Atom := .base .e

/-- The type of propositions. -/
abbrev prop : Ty Atom := .base .s ⇒ .t

/-- The type of properties of individuals, of a verb phrase and of a noun. -/
abbrev predicate : Ty Atom := ent ⇒ prop

/-- The type of a noun phrase, a quantifier. -/
abbrev quant : Ty Atom := predicate ⇒ prop

/-- The type of a clause before existential closure, a predicate of times. -/
abbrev tensed : Ty Atom := .base .i ⇒ prop

/-- The rules of the fragment that are not Functional Application: the rule that joins a noun to
its relative clause (7b), and the rule for a noun phrase raised to S (13a), which closes the
clause it abstracts over. -/
inductive Rule : Ty Atom → Ty Atom → Ty Atom → Type
  /-- A noun and its relative clause. -/
  | relative : Rule predicate predicate predicate
  /-- A noun phrase raised to S. -/
  | raising : Rule quant (ent ⇒ tensed) prop

/-- The translations of the two rules. -/
@[simp] def Rule.eval (E W T : Type) [LE T] : {l r u : Ty Atom} → Rule l r u →
    l.Dom (Dom E W T) → r.Dom (Dom E W T) → u.Dom (Dom E W T)
  | _, _, _, .relative, N, S => fun x i ↦ N x i ∧ S x i
  | _, _, _, .raising, Q, R => Q fun x i ↦ ∃ t, R x t i

/-- The rule of the two that applies to two types. -/
def Rule.rules (l r : Ty Atom) : List (Σ u, Rule l r u) :=
  (if h : l = predicate ∧ r = predicate then
    [⟨predicate, by obtain ⟨rfl, rfl⟩ := h; exact .relative⟩]
  else []) ++
  if h : l = quant ∧ r = (ent ⇒ tensed) then
    [⟨prop, by obtain ⟨rfl, rfl⟩ := h; exact .raising⟩]
  else []

/-- The two rules, as a language over the types. -/
@[reducible] def fragment : ManySorted.Language (Ty Atom) := .mk₂ (fun _ _ ↦ PEmpty) Rule

instance (E W T : Type) [LE T] : fragment.Structure (Ty.Dom (Dom E W T)) :=
  .mk₂ nofun (Rule.eval E W T)

instance : fragment.LocallyFinite :=
  .mk₂ (fun _ ↦ []) Rule.rules nofun fun m ↦ by cases m <;> simp [Rule.rules]

@[simp] theorem symbols_fragment (l r : Ty Atom) :
    ManySorted.Language.LocallyFinite.symbols (L := fragment) (.prod (.of l) (.of r)) =
      Rule.rules l r := rfl

section Interpretation

variable {E W T : Type} [LinearOrder T]

/-- A model of the fragment fixes the speech time $s^*$, the reference intervals $t_{Rn}$, and the
interpretation of the constants at each index. -/
structure Model (E W T : Type) [LE T] where
  /-- The speech time. -/
  speech : NonemptyInterval T
  /-- The reference intervals. -/
  ref : ℕ → NonemptyInterval T
  /-- The bearers of the names. -/
  name : Name → E
  /-- The extensions of the one-place predicates at an index. -/
  pred : Pred → E → Index W T → Prop
  /-- `tv c x y` holds when `x` stands to `y` in the relation `c`. -/
  tv : TV → E → E → Index W T → Prop
  /-- `att c p x` holds when `x` stands to the proposition `p` in the relation `c`. -/
  att : Att → (Index W T → Prop) → E → Index W T → Prop
  /-- `poss x y` holds when `y` is related to `x`, as a claim to its author. -/
  poss : E → E → Index W T → Prop
  /-- `truth x` holds at an index when `x` speaks the truth there. -/
  truth : E → Index W T → Prop

namespace Model

variable (M : Model E W T) (g : ℕ → E) {i : Index W T}

/-- The past restricted to the reference interval `n`: a time before the evaluation time within
that interval at which `p` holds. -/
def past (n : ℕ) (p : Index W T → Prop) : Index W T → Prop :=
  fun i ↦ ◇[Allen.toSetRel Allen.precedes] (fun t ↦ t ≤ M.ref n ∧ p (i.1, t)) i.2

/-- The future restricted to the reference interval `n`. -/
def fut (n : ℕ) (p : Index W T → Prop) : Index W T → Prop :=
  fun i ↦ ◇[Allen.toSetRel (Allen.ofPosition ⟦future⟧)] (fun t ↦ t ≤ M.ref n ∧ p (i.1, t)) i.2

/-- The English present, $\exists t[\mathrm{NOW}(t) \wedge \mathrm{AT}(t, p)]$: `p` at the speech
time, wherever it is evaluated. -/
def now (p : Index W T → Prop) : Index W T → Prop := fun i ↦ p (i.1, M.speech)

variable {M}

theorem past_iff {n : ℕ} {p : Index W T → Prop} :
    M.past n p i ↔ ∃ t, t.Precedes i.2 ∧ t ≤ M.ref n ∧ p (i.1, t) := by
  simp [past, Diamond]

theorem fut_iff {n : ℕ} {p : Index W T → Prop} :
    M.fut n p i ↔ ∃ t, i.2.Precedes t ∧ t ≤ M.ref n ∧ p (i.1, t) := by
  simp [fut, Diamond, Denotes.denote, Tense.denote]

theorem past_eq {n : ℕ} {p : Index W T → Prop} :
    M.past n p = fun i ↦ ∃ t, t.Precedes i.2 ∧ t ≤ M.ref n ∧ p (i.1, t) :=
  funext fun _ ↦ propext past_iff

theorem fut_eq {n : ℕ} {p : Index W T → Prop} :
    M.fut n p = fun i ↦ ∃ t, i.2.Precedes t ∧ t ≤ M.ref n ∧ p (i.1, t) :=
  funext fun _ ↦ propext fut_iff

theorem now_eq {p : Index W T → Prop} : M.now p = fun i ↦ p (i.1, M.speech) := rfl

variable (M)

/-- The translations of the words. A tense is its Aux, which holds its clause at a time the tense
describes (3d, 4b, with 5 and 14); *woll*, the perfect and *earlier* quantify over a time of their
own (3a, 3c, 16); a noun phrase is a quantifier (6b, 15, 8b) and a transitive verb takes one
(10b); the complementizer closes its clause (9), as the relative pronoun does (12). -/
def lex : Word → Σ a : Ty Atom, a.Dom (Dom E W T)
  | .past n => ⟨prop ⇒ tensed, fun p t i ↦ t.Precedes i.2 ∧ t ≤ M.ref n ∧ p (i.1, t)⟩
  | .pres => ⟨prop ⇒ tensed, fun p t i ↦ t = M.speech ∧ p (i.1, t)⟩
  | .null | .ru => ⟨prop ⇒ tensed, fun p t i ↦ t = i.2 ∧ p (i.1, t)⟩
  | .inf n => ⟨prop ⇒ tensed, fun p t i ↦ i.2.Precedes t ∧ t ≤ M.ref n ∧ p (i.1, t)⟩
  | .woll n => ⟨prop ⇒ prop, M.fut n⟩
  | .perf n => ⟨prop ⇒ prop, M.past n⟩
  | .earlier n => ⟨predicate ⇒ predicate, fun P x ↦ M.past n (P x)⟩
  | .current => ⟨predicate ⇒ predicate, id⟩
  | .name c => ⟨quant, fun P ↦ P (M.name c)⟩
  | .pred c => ⟨predicate, M.pred c⟩
  | .tv c => ⟨quant ⇒ predicate, fun Q x ↦ Q fun y ↦ M.tv c x y⟩
  | .att c => ⟨prop ⇒ predicate, M.att c⟩
  | .a => ⟨predicate ⇒ quant, fun P Q i ↦ ∃ x, P x i ∧ Q x i⟩
  | .poss => ⟨quant ⇒ predicate ⇒ quant,
      fun Q P R i ↦ ∃ y, (∀ z, P z i ∧ Q (fun x ↦ M.poss x z) i ↔ z = y) ∧ R y i⟩
  | .who => ⟨(ent ⇒ tensed) ⇒ predicate, fun R x i ↦ ∃ t, R x t i⟩
  | .that => ⟨tensed ⇒ prop, fun S i ↦ ∃ t, S t i⟩

/-- The rules: Functional Application, the two rules of the fragment, and abstraction over the
index of a trace, a variable over individuals. -/
abbrev rules : Interpreter ((application.sum fragment).withAbstraction fun _ ↦ ent) Node :=
  (typeDriven (application.sum fragment)).withAbstraction fun _ ↦ ent

/-- The translations of an LF, relative to an assignment: a word has its translation, and a trace
is the quantifier of the individual of its index. -/
def meanings (t : LF) : List (Σ a : Ty Atom, (ℕ → E) → a.Dom (Dom E W T)) :=
  t.values rules (ManySorted.Language.withAbstraction.structure (Assignments.total (Dom E W T) fun
      _ ↦ ent))
    (W := fun a ↦ (ℕ → E) → a.Dom (Dom E W T)) id fun
    | .inl w => [⟨(M.lex w).1, fun _ ↦ (M.lex w).2⟩]
    | .inr n => [⟨quant, fun g P ↦ P (g n)⟩]

/-- An LF holds at an index under an assignment when its translation is true there: a matrix
clause is closed over its time (1), and a clause a noun phrase is raised from is closed
already. -/
def Holds (t : LF) (i : Index W T) : Prop :=
  (∃ S, M.meanings t = [⟨tensed, S⟩] ∧ ∃ t', S g t' i) ∨ ∃ p, M.meanings t = [⟨prop, p⟩] ∧ p g i

/-- The necessary condition (54) of chapter 2 on the saying relation: a speaker who stands in it to
a proposition speaks the truth at the index exactly when the proposition is true there. -/
def Reliable : Prop := ∀ p x i, M.att .say p x i → (M.truth x i ↔ p i)

/-- A predicate is stable when what it is true of does not vary with the time. -/
def Stable (c : Pred) : Prop := ∀ x i t, M.pred c x i ↔ M.pred c x (i.1, t)

variable {M}

attribute [local simp] Holds meanings clause np untensed intrans complement aNoun relClause
  tvTrace vpAdjoined raised report saidIll sawWide sawNarrow metWide metNarrow saidFish claimNP
  claimClause lex Interpreter.withAbstraction typeDriven Assignments.total past_eq fut_eq now_eq
  Application.rules Rule.rules

/-! ### Complement clauses -/

-- (55) of chapter 2: the empty tense leaves the complement untensed, and a speaker who spoke the
-- truth said something true at the index of the saying, which is all that the simultaneous reading
-- amounts to
theorem Reliable.simultaneous (hM : M.Reliable) (h : M.Holds g (saidIll .null) i) :
    ∃ t, t.Precedes i.2 ∧ t ≤ M.ref 1 ∧
      (M.truth (M.name .john) (i.1, t) → M.pred .ill (M.name .mary) (i.1, t)) := by
  obtain ⟨t, ht, hR, hs⟩ := past_iff.1 (by simpa using h :
    M.past 1 (M.att .say (M.pred .ill (M.name .mary)) (M.name .john)) i)
  exact ⟨t, ht, hR, (hM _ _ _ hs).1⟩

-- (56) of chapter 2, the shifted reading the dissertation leaves to the reader
theorem Reliable.shifted (hM : M.Reliable) (h : M.Holds g (saidIll (.past 2)) i) :
    ∃ t, t.Precedes i.2 ∧ t ≤ M.ref 1 ∧ (M.truth (M.name .john) (i.1, t) →
      ∃ t', t'.Precedes t ∧ t' ≤ M.ref 2 ∧ M.pred .ill (M.name .mary) (i.1, t')) := by
  obtain ⟨t, ht, hR, hs⟩ := past_iff.1 (by simpa using h :
    M.past 1 (M.att .say (M.past 2 (M.pred .ill (M.name .mary))) (M.name .john)) i)
  exact ⟨t, ht, hR, fun hT ↦ past_iff.1 ((hM _ _ _ hs).1 hT)⟩

-- (3'') of chapter 4, the wrong prediction of the first fragment: a past claim about the speech
-- time, with no commitment about the time of the claim
theorem Reliable.now (hM : M.Reliable) (h : M.Holds g (saidIll .pres) i) :
    ∃ t, t.Precedes i.2 ∧ t ≤ M.ref 1 ∧
      (M.truth (M.name .john) (i.1, t) → M.pred .ill (M.name .mary) (i.1, M.speech)) := by
  obtain ⟨t, ht, hR, hs⟩ := past_iff.1 (by simpa using h :
    M.past 1 (M.att .say (M.now (M.pred .ill (M.name .mary))) (M.name .john)) i)
  exact ⟨t, ht, hR, (hM _ _ _ hs).1⟩

/-! ### Relative clauses

*John saw a man who was laughing*, (46), with the three derivations of its three-way ambiguity. -/

-- (46a'), line 4: the laughing and the seeing are unordered
theorem holds_sawWide : M.Holds g (sawWide (.past 3)) i ↔
    ∃ x, (M.pred .man x i ∧ M.past 3 (M.pred .laughing x) i) ∧
      M.past 1 (fun i ↦ M.tv .see (M.name .john) x i) i := by
  simp

-- (46b'), line 5: simultaneous
theorem holds_sawNarrow_null : M.Holds g (sawNarrow .null) i ↔
    M.past 1 (fun i ↦ ∃ x, (M.pred .man x i ∧ M.pred .laughing x i) ∧
      M.tv .see (M.name .john) x i) i := by
  simp

-- (46c'), line 4: shifted
theorem holds_sawNarrow_past : M.Holds g (sawNarrow (.past 2)) i ↔
    M.past 1 (fun i ↦ ∃ x, (M.pred .man x i ∧ M.past 2 (M.pred .laughing x) i) ∧
      M.tv .see (M.name .john) x i) i := by
  simp

/-- The wide scope reading of the relative covers both narrow scope readings, so that they do not
strike speakers as independent readings. This needs a man at the speech time who was one at the
past time, and a reference interval of the raised relative that contains the times the narrow
readings find. -/
theorem sawWide_of_sawNarrow (hman : ∀ x t, M.pred .man x (i.1, t) → M.pred .man x i)
    (hR₁ : M.ref 1 ≤ M.ref 3) (hR₂ : M.ref 2 ≤ M.ref 3)
    (h : M.Holds g (sawNarrow .null) i ∨ M.Holds g (sawNarrow (.past 2)) i) :
    M.Holds g (sawWide (.past 3)) i := by
  rw [holds_sawNarrow_null, holds_sawNarrow_past] at h
  rw [holds_sawWide]
  rcases h with h | h <;> obtain ⟨t, ht, htR, x, ⟨hn, hl⟩, hs⟩ := past_iff.1 h
  · exact ⟨x, ⟨hman x t hn, past_iff.2 ⟨t, ht, htR.trans hR₁, hl⟩⟩, past_iff.2 ⟨t, ht, htR, hs⟩⟩
  · obtain ⟨t', ht', htR', hl⟩ := past_iff.1 hl
    exact ⟨x, ⟨hman x t hn,
      past_iff.2 ⟨t', NonemptyInterval.precedes_trans ht' ht, htR'.trans hR₂, hl⟩⟩,
      past_iff.2 ⟨t, ht, htR, hs⟩⟩

-- p. 97: a laughing after the seeing comes from the wide scope reading alone
theorem not_holds_sawNarrow_of_precedes {a b : NonemptyInterval T} (hab : a.Precedes b)
    (hsee : ∀ i x, M.tv .see (M.name .john) x i → i.2 = a)
    (hlaugh : ∀ i x, M.pred .laughing x i → i.2 = b) :
    ¬ M.Holds g (sawNarrow .null) i ∧ ¬ M.Holds g (sawNarrow (.past 2)) i := by
  simp only [holds_sawNarrow_null, holds_sawNarrow_past, past_iff]
  grind [NonemptyInterval.precedes_irrefl, NonemptyInterval.precedes_asymm]

-- (44) line 4
theorem holds_metWide : M.Holds g metWide i ↔
    ∃ x, (M.pred .man x i ∧ M.now (M.fut 3 (M.pred .supporter x)) i) ∧
      M.past 2 (fun i ↦ M.tv .meet (M.name .john) x i) i := by
  simp

-- (45) line 4
theorem holds_metNarrow : M.Holds g (metNarrow .pres) i ↔
    M.past 2 (fun i ↦ ∃ x, (M.pred .man x i ∧ M.now (M.fut 3 (M.pred .supporter x)) i) ∧
      M.tv .meet (M.name .john) x i) i := by
  simp

-- p. 116: the present in a relative denotes the speech time wherever the relative is scoped
theorem metWide_iff_metNarrow (hman : M.Stable .man) :
    M.Holds g metWide i ↔ M.Holds g (metNarrow .pres) i := by
  simp only [holds_metWide, holds_metNarrow, past_iff]
  exact ⟨fun ⟨x, ⟨hn, hf⟩, t, ht, htR, hm⟩ ↦ ⟨t, ht, htR, x, ⟨(hman x i t).1 hn, hf⟩, hm⟩,
    fun ⟨t, ht, htR, x, ⟨hn, hf⟩, hm⟩ ↦ ⟨x, ⟨(hman x i t).2 hn, hf⟩, t, ht, htR, hm⟩⟩

-- p. 116: of a man who is a man only at the meeting, (45) line 4 holds and (44) line 4 does not
theorem metNarrow_not_metWide {a : NonemptyInterval T} {x : E} (ha : a.Precedes i.2)
    (haR : a ≤ M.ref 2) (hman : M.pred .man x (i.1, a)) (hnow : ∀ y, ¬ M.pred .man y i)
    (hf : M.now (M.fut 3 (M.pred .supporter x)) (i.1, a))
    (hm : M.tv .meet (M.name .john) x (i.1, a)) :
    M.Holds g (metNarrow .pres) i ∧ ¬ M.Holds g metWide i := by
  rw [holds_metNarrow, holds_metWide, past_iff]
  exact ⟨⟨a, ha, haR, x, ⟨hman, hf⟩, hm⟩, fun ⟨y, ⟨hn, _⟩, _⟩ ↦ hnow y hn⟩

-- (37'): the fish is alive at the time of the buying, which can follow the speech time
theorem holds_saidFish : M.Holds g (saidFish .null .null) i ↔
    M.past 1 (M.att .say (M.fut 3 fun i ↦ ∃ x, (M.pred .fish x i ∧ M.pred .alive x i) ∧
      M.tv .buy (M.name .john) x i) (M.name .john)) i := by
  simp

-- p. 123: the simultaneous reading of an English past in a narrow relative, (46b'), is what the
-- Japanese present gives, (47a''); in a wide relative that present is at the speech time, (47a')
theorem holds_ru : (M.Holds g (sawNarrow .ru) i ↔ M.Holds g (sawNarrow .null) i) ∧
    (M.Holds g (sawWide .ru) i ↔ ∃ x, (M.pred .man x i ∧ M.pred .laughing x i) ∧
      M.past 1 (fun i ↦ M.tv .see (M.name .john) x i) i) := by
  simp

-- p. 132: the undeleted *would* of (61) says nothing against a winning after the speech time
theorem would_undeleted_any_future {a b : NonemptyInterval T} {x : E} (ha : a.Precedes i.2)
    (haR : a ≤ M.ref 2) (hab : a.Precedes b) (hbR : b ≤ M.ref 3) (hw : M.pred .win x (i.1, b)) :
    M.past 2 (M.fut 3 (M.pred .win x)) i :=
  past_iff.2 ⟨a, ha, haR, fut_iff.2 ⟨b, hab, hbR, hw⟩⟩

-- (29), (30) line 11 of chapter 3: the empty tense of *would* leaves the winning after the
-- claiming, which *earlier* places before the time of *well-known*, and the noun phrase denotes the
-- unique claim made by John
theorem holds_claimClause : M.Holds g (claimClause (.earlier 1) .null) i ↔
    M.now (fun i ↦ ∃ y,
      (∀ z, M.past 1 (M.att .claimNoun (M.fut 3 (M.pred .win (M.name .mary))) z) i ∧
        M.poss (M.name .john) z i ↔ z = y) ∧ M.pred .wellKnown y i) i := by
  simp

/- A second tense in the place of an auxiliary has no translation: a tense gives a property of
times, and the tense above it takes a proposition. -/
example : ¬ M.Holds g (clause (.past 1) [.past 2] (intrans (np .john) .ill)) i := by simp

end Model

-- `Word.cell` is what the translation says: a time in the cell at which the argument holds
theorem position_mem_cell {M : Model E W T} {w : Word} {τ : (Index W T → Prop) → Index W T → Prop}
    {p : Index W T → Prop} {i : Index W T} (h : M.lex w = ⟨prop ⇒ prop, τ⟩) (hτ : τ p i) :
    ∃ t, t.position i.2 ∈ w.cell ∧ p (i.1, t) := by
  cases w <;> simp only [Model.lex, Sigma.mk.injEq, heq_eq_eq, true_and, reduceCtorEq, and_false,
    false_and, Ty.fn.injEq, Ty.base.injEq, and_true] at h <;> subst h
  case perf =>
    obtain ⟨t, ht, -, hp⟩ := Model.past_iff.1 hτ
    exact ⟨t, by simpa [Word.cell, Denotes.denote, Tense.denote] using ht, hp⟩
  case woll =>
    obtain ⟨t, ht, -, hp⟩ := Model.fut_iff.1 hτ
    exact ⟨t, by simpa [Word.cell, Denotes.denote, Tense.denote] using ht, hp⟩

-- and of a tense, whose time is the time of its clause
theorem position_mem_cell_of_tense {M : Model E W T} {w : Word}
    {τ : (Index W T → Prop) → NonemptyInterval T → Index W T → Prop} {p : Index W T → Prop}
    {t : NonemptyInterval T} {i : Index W T} (h : M.lex w = ⟨prop ⇒ tensed, τ⟩) (hw : w ≠ .pres)
    (hτ : τ p t i) : t.position i.2 ∈ w.cell ∧ p (i.1, t) := by
  cases w <;> simp only [Model.lex, Sigma.mk.injEq, heq_eq_eq, true_and, reduceCtorEq, and_false,
    false_and, Ty.fn.injEq, Ty.base.injEq, and_true] at h <;> subst h
  case pres => exact absurd rfl hw
  case null | ru => exact ⟨by simp [hτ.1, Word.cell, Denotes.denote, Tense.denote], hτ.2⟩
  case past | inf =>
    exact ⟨by simpa [Word.cell, Denotes.denote, Tense.denote] using hτ.1, hτ.2.2⟩

end Interpretation

/-! ### The sentences

A reading says how the time of a tense stands to the time of the verb above it, or to the speech
time. Each is computed from an LF by composing the cells of the words above the tense. -/

/-- A language has tense deletion: English does, Japanese does not. -/
abbrev HasDeletion (g : Glottocode) : Prop := g = Glottocode.english

/-- The LFs a language gives an LF: the rule is English. -/
def lfsOf (L : Glottocode) (t : LF) : List LF := if HasDeletion L then lfsFrom 3 t else [t]

/-- The words above a position that introduce a time, top down: the ones that c-command it. -/
def timesAbove (t : LF) (b : TreePath) : List TreePath :=
  (wordPositions t Word.IsTime).filter fun a ↦ a ≠ b ∧ a ~[RoseTree.cCommand t] b

/-- The cell of a time against the speech time: the cells of the words above it and its own,
composed from the top, the English present returning to the speech time. -/
def speechCell (t : LF) (b : TreePath) : Finset Ordering :=
  ((timesAbove t b ++ [b]).filterMap (wordAt? t)).foldl
    (fun C w ↦ if w = .pres then ⟦Tense.present⟧ else comp w.cell C) ⟦Tense.present⟧

/-- The cell of a time against the time `r`: the cell of its word when `r` is the time at which the
word is evaluated, and otherwise as the two times stand to the speech time. -/
def cellAgainst (t : LF) (b r : TreePath) : Finset Ordering :=
  match wordAt? t b with
  | some w =>
    if w ≠ .pres ∧ (timesAbove t b).getLast? = some r then w.cell
    else comp (speechCell t b) ((speechCell t r).image Ordering.swap)
  | none => ⊥

/-- The cell of a time against `r` over several LFs. -/
def cellIn (lfs : List LF) (b r : TreePath) : Finset Ordering :=
  (lfs.map (cellAgainst · b r)).foldr (· ⊔ ·) ⊥

-- the parameter of `pastUnderPast`, read off the tree
theorem cellIn_saidIll (L : Glottocode) :
    cellIn (lfsOf L (saidIll (.past 2))) ⟨[1, 1, 1, 1, 0]⟩ ⟨[0]⟩ =
      pastUnderPast (HasDeletion L) := by
  by_cases h : HasDeletion L
  · rw [show lfsOf L (saidIll (.past 2)) = lfsFrom 3 (saidIll (.past 2)) by simp [lfsOf, h],
      pastUnderPast_pos h]
    decide
  · rw [show lfsOf L (saidIll (.past 2)) = [saidIll (.past 2)] by simp [lfsOf, h],
      pastUnderPast_neg h]
    decide

-- (37), p. 107: the fish cannot be alive after the speech time if its relative is raised
theorem saidFishWide_before_speech :
    ∃ b ∈ lowestOf? saidFishWide (.past 4), speechCell saidFishWide b = ⟦Tense.past⟧ := by
  decide

/-- A reading against the time of the verb above a tense. -/
def reading? (w : String) : Option Ordering :=
  [("shifted", Ordering.lt), ("simultaneous", .eq), ("subsequent", .gt)].lookup w

/-- A reading against the speech time. -/
def speechReading? (w : String) : Option Ordering :=
  [("before the speech time", Ordering.lt), ("after the speech time", .gt)].lookup w

/-- A sentence with the LFs that QR gives it has the reading named `name` of the tense `w` against
the word `ref` when an LF that its language gives it places the time so. -/
def Predicted (L : Glottocode) (lfs : List LF) (w ref : Word) (name : String) : Prop :=
  (∃ o ∈ reading? name, ∃ t ∈ lfs, ∃ b ∈ lowestOf? t w, ∃ r ∈ lowestOf? t ref,
    o ∈ cellIn (lfsOf L t) b r) ∨
  ∃ o ∈ speechReading? name, ∃ t ∈ lfs, ∃ b ∈ lowestOf? t w, ∃ t' ∈ lfsOf L t, o ∈ speechCell t' b

instance (L : Glottocode) (lfs : List LF) (w ref : Word) (name : String) :
    Decidable (Predicted L lfs w ref name) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A sentence of two levels of embedding, the lowest clause with the past `past 4`. -/
def twoLevels (t : Word) (ws : List Word) (x : Name) (v : Att) (t' : Word) (ws' : List Word)
    (y : Name) (v' : Att) (c : Pred) : LF :=
  clause t ws (untensed (np x) (complement v (clause t' ws' (untensed (np y) (complement v'
    (clause (.past 4) [] (intrans (np y) c)))))))

/-- The rows on a tense, each with the LFs QR gives its sentence, the tense its readings are about
and the word for the time of the verb above it. -/
def rows : List (Datum × List LF × Word × Word) :=
  [(Examples.ex_2_1a, [saidIll (.past 2)], .past 2, .past 1),
   (Examples.ex_2_2a, [saidIll (.past 2)], .past 2, .past 1),
   (Examples.ex_2_2b, [saidIll .ru], .ru, .past 1),
   (Examples.ex_2_25a, [report (.past 1) [] .john .say .pres [] .mary .inAustin], .pres, .past 1),
   (Examples.ex_2_25b, [report (.past 1) [] .john .say (.past 2) [] .mary .inAustin], .past 2,
    .past 1),
   (Examples.ex_2_25c, [report .pres [.woll 1] .john .say .pres [] .mary .inAustin], .pres,
    .woll 1),
   (Examples.ex_2_27, [sawWide (.past 2), sawNarrow (.past 2)], .past 2, .past 1),
   (Examples.ex_2_28, [saidIll (.past 2)], .past 2, .past 1),
   (Examples.ex_2_33a, [metNarrow (.past 4)], .woll 3, .past 2),
   (Examples.ex_2_33b, [metWide, metNarrow .pres], .woll 3, .past 2),
   (Examples.ex_2_34,
    [clause .pres [.woll 1] (vpAdjoined (aNoun .man 1 (relClause 1 .pres [] .holding)) 0 (np .john)
      .meet),
     raised (aNoun .man 1 (relClause 1 .pres [] .holding)) 0
      (clause .pres [.woll 1] (tvTrace (np .john) .meet 0))], .pres, .woll 1),
   (Examples.ex_2_37, [saidFish (.past 2) (.past 4), saidFishWide], .past 4, .woll 3),
   (Examples.ex_2_47a, [sawWide .ru, sawNarrow .ru], .ru, .past 1),
   (Examples.ex_2_47b, [sawWide (.past 2), sawNarrow (.past 2)], .past 2, .past 1),
   (Examples.ex_2_59, [report .pres [.woll 1, .perf 2] .john .claim (.past 3) [] .john .ill],
    .past 3, .perf 2),
   (Examples.ex_2_97, [twoLevels (.past 1) [] .speaker .tell (.past 2) [.woll 3] .addressee .say
      .magicTricks], .past 4, .woll 3),
   (Examples.ex_2_103, [twoLevels (.past 1) [] .speaker .tell .pres [.woll 3] .addressee .say
      .magicTricks], .past 4, .woll 3),
   (Examples.ex_2_104, [twoLevels (.past 1) [] .john .promise (.inf 2) [] .john .say .ignorant],
    .past 4, .inf 2),
   (Examples.ex_2_105, [twoLevels .pres [.woll 1] .john .promise (.inf 2) [] .john .say .ignorant],
    .past 4, .inf 2),
   (Examples.ex_2_125, [report (.past 1) [] .john .say (.past 2) [.woll 3] .mary .come], .woll 3,
    .past 1),
   (Examples.ex_2_139a,
    [twoLevels (.past 1) [] .john .think .pres [.woll 2] .bill .claim .ignorant], .past 4, .woll 2),
   (Examples.ex_2_139b, [twoLevels (.past 1) [] .john .think (.past 2) [.woll 3] .bill .claim
      .ignorant], .past 4, .woll 3),
   (Examples.ex_2_139c, [twoLevels (.past 1) [] .john .ask (.inf 2) [] .bill .claim .ignorant],
    .past 4, .inf 2)]

/-- Every reading of the rows is available exactly when an LF that QR and the rule give the sentence
places the time so, by the composition of the cells above it. -/
theorem rows_readings :
    ∀ x ∈ rows, x.1.readings ≠ [] ∧ ∀ r ∈ x.1.readings,
      ((reading? r.1).isSome ∨ (speechReading? r.1).isSome) ∧
      (Predicted x.1.language x.2.1 x.2.2.1 x.2.2.2 r.1 ↔ r.2 = .acceptable) := by
  decide +kernel

/-! ### Theories without the rule -/

section Rivals

variable {W T : Type} [LinearOrder T]

-- (112)-(114) of chapter 2: under the permanence of the reference point the lowest clause of *John
-- decided that he would say that they were having their last meal* has its event at the reference
-- point of the clause of *would*, so the meal cannot coincide with the saying
theorem permanence_excludes_simultaneous (f₂ f₃ : ReichenbachFrame T)
    (hR : f₂.referenceTime = f₃.referenceTime) (h₂ : f₂.eventPosition = .gt)
    (h₃ : f₃.eventPosition = .eq) : f₃.eventTime ≠ f₂.eventTime := by
  grind [ReichenbachFrame.eventPosition_eq_gt, ReichenbachFrame.eventPosition_eq_eq]

/-- A tense operator of the three-index system of chapter 2, with the cell of its past feature
against the quasi-speech time `j` and the cell of its future feature against the evaluation time
`i`. The operator [-past][+fut], which also updates `j`, is not needed for (126). -/
def tns (C D : Finset Ordering) (φ : W → NonemptyInterval T → NonemptyInterval T → Prop)
    (w : W) (i j : NonemptyInterval T) : Prop :=
  ∃ t, t.position j ∈ C ∧ t.position i ∈ D ∧ φ w t j

/-- Without the rule, a past always means the past of the quasi-speech time, so *John said that Mary
would come to Austin* wrongly places the coming before the speech time, (126). -/
theorem triple_index_precedes_speech {E : Type} {M : Model E W T} (hM : M.Reliable) {w : W}
    (h : tns ⟦Tense.past⟧ ⟦Tense.future⟧ᶜ (fun w t j ↦ M.att .say
      (fun i ↦ tns ⟦Tense.past⟧ ⟦Tense.future⟧ (fun w t _ ↦ M.pred .come (M.name .mary) (w, t))
        i.1 i.2 j)
      (M.name .john) (w, t)) w M.speech M.speech) :
    ∃ t, t.Precedes M.speech ∧ (M.truth (M.name .john) (w, t) →
      ∃ t', t.Precedes t' ∧ t'.Precedes M.speech ∧ M.pred .come (M.name .mary) (w, t')) := by
  obtain ⟨t, ht, -, hs⟩ := h
  refine ⟨t, by simpa [Denotes.denote, Tense.denote] using ht, fun hT ↦ ?_⟩
  obtain ⟨t', ht', hf, hc⟩ := (hM _ _ _ hs).1 hT
  exact ⟨t', by simpa [Denotes.denote, Tense.denote] using hf,
    by simpa [Denotes.denote, Tense.denote] using ht', hc⟩

-- (125), p. 186: with the rule the past of *would* is empty, and in a model with a reliable speaker
-- the coming can follow the speech time
theorem would_can_follow_speech {a b c : T} (hab : a < b) (hbc : b < c) :
    ∃ M : Model Unit Unit T, M.Reliable ∧
      M.Holds (fun _ ↦ ()) (report (.past 1) [] .john .say .null [.woll 3] .mary .come)
        ((), M.speech) ∧
      ∀ i x, M.pred .come x i → M.speech.Precedes i.2 := by
  let M : Model Unit Unit T :=
    { speech := .pure b, ref := fun _ ↦ .pure a ⊔ .pure c, name := fun _ ↦ ()
      pred := fun _ _ i ↦ i.2 = .pure c, tv := fun _ _ _ _ ↦ True
      att := fun _ p _ i ↦ i.2 = .pure a ∧ p i, poss := fun _ _ _ ↦ True
      truth := fun _ _ ↦ True }
  refine ⟨M, fun _ _ _ h ↦ iff_of_true trivial h.2, ?_, ?_⟩
  · have hs : M.past 1 (M.att .say (M.fut 3 (M.pred .come (M.name .mary))) (M.name .john))
        ((), M.speech) :=
      Model.past_iff.2 ⟨.pure a, hab, le_sup_left, rfl,
        Model.fut_iff.2 ⟨.pure c, hab.trans hbc, le_sup_right, rfl⟩⟩
    simpa [Model.Holds, Model.meanings, report, clause, np, untensed, intrans, complement,
      Model.lex, Interpreter.withAbstraction, typeDriven, Assignments.total, Application.rules,
          Rule.rules, Model.past_eq, Model.fut_eq,
      Model.now_eq] using hs
  · rintro ⟨_, t⟩ _ h
    obtain rfl : t = .pure c := h
    exact hbc

end Rivals

/-! ### Double access

A present under a past. Chapter 4 rejects four hypotheses on the truth conditions of *John said
that Mary is pregnant*, of which the first two are stated here, and chapter 5 derives the sentence
as a de re report about a state. The theories are compared in one model. -/

section DoubleAccess

variable {E W Ev St T : Type*} [LinearOrder T]

/-- Hypothesis 1, (14): the speaker said the proposition, and it is true in the actual world at an
interval properly including the speech time and the time of the saying. -/
def Hypothesis1 (att : (Index W T → Prop) → E → Index W T → Prop) (p : Index W T → Prop) (x : E)
    (σ R : NonemptyInterval T) (w : W) : Prop :=
  ∃ t, t.Precedes σ ∧ t ≤ R ∧ att p x (w, t) ∧ ∃ t', σ < t' ∧ t ≤ t' ∧ p (w, t')

/-- Hypothesis 2, (20): the speaker said of an interval properly including the speech time and the
time of the saying that the proposition is true at it. -/
def Hypothesis2 (att : (Index W T → Prop) → E → Index W T → Prop) (p : Index W T → Prop) (x : E)
    (σ R : NonemptyInterval T) (w : W) : Prop :=
  ∃ t, t.Precedes σ ∧ t ≤ R ∧ ∃ t', σ < t' ∧ t ≤ t' ∧ att (fun i ↦ p (i.1, t')) x (w, t)

variable [Event.TemporalTrace Ev (NonemptyInterval T)]

open Event (τ)

/-- The proposition that a state obtains, (60b), and is of the kind `P`. A state occupies an
interval in each world. -/
def obtains (occ : St → W → NonemptyInterval T) (P : St → W → Prop) (s : St) : Index W T → Prop :=
  fun i ↦ i.2 ≤ occ s i.1 ∧ P s i.1

/-- (64'), the second fragment's translation of a present under a past: a state that obtains at the
speech time and a past event of saying of that state that it obtains and is of the kind `P`, a
report de re about the state. -/
def DoubleAccess (occ : St → W → NonemptyInterval T) (say : Ev → E → (Index W T → Prop) → W → Prop)
    (P : St → W → Prop) (x : E) (σ R : NonemptyInterval T) (w : W) : Prop :=
  ∃ s, σ ≤ occ s w ∧ ∃ e, (τ e).Precedes σ ∧ τ e ≤ R ∧ say e x (obtains occ P s) w

/-- The attitude of the first fragment that a Davidsonian saying relation gives: a saying of the
proposition at the time. -/
def attOf (say : Ev → E → (Index W T → Prop) → W → Prop) :
    (Index W T → Prop) → E → Index W T → Prop :=
  fun p x i ↦ ∃ e, τ e = i.2 ∧ say e x p i.1

variable {occ : St → W → NonemptyInterval T} {say : Ev → E → (Index W T → Prop) → W → Prop}
  {P : St → W → Prop} {x : E} {σ R : NonemptyInterval T} {w : W}

-- (17), p. 287: John is reported truly though Mary is not in the room at the speech time, and an
-- interval including the speech time at which she is would need her there then, by (59b)
theorem doubleAccess_not_hypothesis1 {e₀ : Ev} {s₀ : St} (he : (τ e₀).Precedes σ) (heR : τ e₀ ≤ R)
    (hsaid : say e₀ x (obtains occ P s₀) w) (hlast : σ ≤ occ s₀ w)
    (hm : ¬ ∃ s, σ ≤ occ s w ∧ P s w) :
    DoubleAccess occ say P x σ R w ∧
      ¬ Hypothesis1 (attOf say) (fun i ↦ ∃ s, i.2 ≤ occ s i.1 ∧ P s i.1) x σ R w := by
  refine ⟨⟨s₀, hlast, e₀, he, heR, hsaid⟩, ?_⟩
  rintro ⟨t, -, -, -, t', hσ, -, s, hs, hP⟩
  exact hm ⟨s, hσ.le.trans hs, hP⟩

/-- John's saying on June 20th and what he said are the same in the two cases of (24), so Hypothesis
2 cannot tell them apart, while (64') can: the state lasts through the report in one world and not
in the other. This needs the interval a state occupies to depend on the world. -/
theorem minimal_pair {w₁ w₂ : W} {e₀ : Ev} {s₀ : St} {p : Index W T → Prop}
    (hagree : ∀ e q, (τ e).Precedes σ → (say e x q w₁ ↔ say e x q w₂))
    (honly : ∀ e s, say e x (obtains occ P s) w₂ → s = s₀)
    (he : (τ e₀).Precedes σ) (heR : τ e₀ ≤ R) (hsaid : say e₀ x (obtains occ P s₀) w₁)
    (h₁ : σ ≤ occ s₀ w₁) (h₂ : ¬ σ ≤ occ s₀ w₂) :
    DoubleAccess occ say P x σ R w₁ ∧ ¬ DoubleAccess occ say P x σ R w₂ ∧
      (Hypothesis2 (attOf say) p x σ R w₁ ↔ Hypothesis2 (attOf say) p x σ R w₂) := by
  refine ⟨⟨s₀, h₁, e₀, he, heR, hsaid⟩, ?_, ?_⟩
  · rintro ⟨s, hs, e, -, -, hsay⟩
    exact h₂ (honly e s hsay ▸ hs)
  · constructor <;> rintro ⟨t, ht, htR, t', hσ, htt', e, hτ, hsay⟩ <;>
      refine ⟨t, ht, htR, t', hσ, htt', e, hτ, ?_⟩
    · exact (hagree e _ (hτ ▸ ht)).1 hsay
    · exact (hagree e _ (hτ ▸ ht)).2 hsay

-- p. 293 turned on (64'): with an interval independent of the world and one saying relation, (64')
-- cannot separate the two cases of (24) either
theorem doubleAccess_rigid_iff {w₁ w₂ : W} (hocc : ∀ s, occ s w₁ = occ s w₂)
    (hagree : ∀ e q, (τ e).Precedes σ → (say e x q w₁ ↔ say e x q w₂)) :
    DoubleAccess occ say P x σ R w₁ ↔ DoubleAccess occ say P x σ R w₂ := by
  constructor <;> rintro ⟨s, hs, e, he, heR, hsay⟩
  · exact ⟨s, hocc s ▸ hs, e, he, heR, (hagree e _ he).1 hsay⟩
  · exact ⟨s, (hocc s).symm ▸ hs, e, he, heR, (hagree e _ he).2 hsay⟩

-- p. 326: the claim is about a state there at the time of the saying, so a report of it by a
-- present under a past needs the state to last from the claim through the speech time
theorem DoubleAccess.exists_sup_le (hres : ∀ e s, say e x (obtains occ P s) w → τ e ≤ occ s w)
    (h : DoubleAccess occ say P x σ R w) :
    ∃ (s : St) (e : Ev), (τ e).Precedes σ ∧ say e x (obtains occ P s) w ∧ τ e ⊔ σ ≤ occ s w := by
  obtain ⟨s, hs, e, he, -, hsaid⟩ := h
  exact ⟨s, e, he, hsaid, _root_.sup_le (hres _ _ hsaid) hs⟩

-- (61)-(63), (49): with a factive verb the state is actual, so (63) entails the two conditions of
-- (62''), one direction of what p. 325 calls virtually equivalent
theorem factive_extended_now (hsay : ∀ e x p w, say e x p w → p (w, τ e))
    (h : DoubleAccess occ say P x σ R w) :
    ∃ (s : St) (e : Ev), (τ e).Precedes σ ∧ say e x (obtains occ P s) w ∧ P s w ∧
      ∃ t', σ < t' ∧ τ e ≤ t' ∧ t' ≤ occ s w := by
  obtain ⟨s, hs, e, he, -, hsaid⟩ := h
  obtain ⟨hes, hP⟩ := hsay _ _ _ _ hsaid
  exact ⟨s, e, he, hsaid, hP, τ e ⊔ σ, lt_of_le_of_ne le_sup_right fun heq ↦
    he.not_overlaps (NonemptyInterval.overlaps_of_le (heq ▸ le_sup_left)), le_sup_left,
    _root_.sup_le hes hs⟩

/-- The worlds consistent with the attitude a saying reports are not empty (p. 284). -/
def Consistent (say : Ev → E → (Index W T → Prop) → W → Prop) : Prop :=
  ∀ e x p w, say e x p w → ∃ w', p (w', τ e)

-- (67)-(69): given (69), the coming of *John said that Mary will come to Austin* follows the saying
theorem future_double_access {P : Ev → W → Prop} {R₁ R₂ : NonemptyInterval T}
    (hsay : Consistent say)
    (h : ∃ e : Ev, σ.Precedes (τ e) ∧ τ e ≤ R₁ ∧ ∃ e' : Ev, (τ e').Precedes σ ∧ τ e' ≤ R₂ ∧
      say e' x (fun i ↦ ∃ t, i.2.Precedes t ∧ t ≤ R₁ ∧ t = τ e ∧ P e i.1) w) :
    ∃ e e' : Ev, (τ e').Precedes (τ e) := by
  obtain ⟨e, -, -, e', -, -, hsaid⟩ := h
  obtain ⟨_, t, het, -, rfl, -⟩ := hsay _ _ _ _ hsaid
  exact ⟨e, e', het⟩

/-! The rows of chapter 4 that give a scenario are reports of a claim made at the time `a` by the
time `b`, about the state the scenario makes responsible for the claim (p. 296). A second state
obtains at the report, as Mary's being in the room does in (28) and Sue's second stay in (43). -/

/-- The interval of a state in a report: the state `0` occupies `I` in each world. -/
def reportOcc (b : T) (I : W → NonemptyInterval T) (s : Fin 2) (w : W) : NonemptyInterval T :=
  if s = 0 then I w else .pure b

/-- The kind of state a claim describes: the state `0` in the world `c`. -/
def reportKind (c : W) (s : Fin 2) (w : W) : Prop := s = 0 ∧ w = c

/-- The saying of a report: at the time `a` the speaker says of the state `0` that it obtains and is
of the kind the claim describes. -/
def reportSaid (a b : T) (I : W → NonemptyInterval T) (c : W) (e : NonemptyInterval T) (_ : E)
    (p : Index W T → Prop) (_ : W) : Prop :=
  e = .pure a ∧ p = obtains (reportOcc b I) (reportKind c) 0

theorem doubleAccess_report_iff {a b : T} (hab : a < b) {I : W → NonemptyInterval T} {c : W} :
    DoubleAccess (Ev := NonemptyInterval T) (reportOcc b I) (reportSaid a b I c) (reportKind c) x
      (.pure b) (.pure a ⊔ .pure b) w ↔ .pure b ≤ I w := by
  constructor
  · rintro ⟨s, hs, e, -, -, -, hp⟩
    have h0 : obtains (reportOcc b I) (reportKind c) s (c, I c) :=
      (congrFun hp (c, I c)).mpr (by simp [obtains, reportOcc, reportKind])
    obtain rfl : s = 0 := h0.2.1
    simpa [reportOcc] using hs
  · exact fun h ↦ ⟨0, by simpa [reportOcc] using h, .pure a, hab, le_sup_left, rfl, rfl⟩

/-- The reports of the scenarios in which the state lasts through the report. -/
def lastingReports : List Datum :=
  [Examples.ex_4_17d, Examples.ex_4_24_Case_1, Examples.ex_4_34d]

/-- The reports of the scenarios in which it does not. -/
def endingReports : List Datum :=
  [Examples.ex_4_24_Case_2, Examples.ex_4_27d, Examples.ex_4_28, Examples.ex_4_43c]

-- (17), (24), (27), (28), (34), (43), p. 296: a report is acceptable exactly when the state lasts.
-- Given which state each scenario is about, this does not separate (64') from Hypothesis 2, which
-- `minimal_pair` does
theorem rows_doubleAccess {a b : T} (hab : a < b) {I : W → NonemptyInterval T} {c : W} :
    (∀ row ∈ lastingReports, row.judgment = .acceptable) ∧
    (∀ row ∈ endingReports, row.judgment = .unacceptable) ∧
    (I w = .pure a ⊔ .pure b → DoubleAccess (Ev := NonemptyInterval T) (reportOcc b I)
      (reportSaid a b I c) (reportKind c) x (.pure b) (.pure a ⊔ .pure b) w) ∧
    (I w = .pure a → ¬ DoubleAccess (Ev := NonemptyInterval T) (reportOcc b I)
      (reportSaid a b I c) (reportKind c) x (.pure b) (.pure a ⊔ .pure b) w) :=
  ⟨by decide, by decide, fun h ↦ (doubleAccess_report_iff hab).2 (h ▸ le_sup_right),
    fun h ↦ mt (doubleAccess_report_iff hab).1 (h ▸ by simp [NonemptyInterval.le_def, hab])⟩

end DoubleAccess

end Ogihara1989
