module

public import Linglib.Data.Examples.Ogihara1989
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Composition.Tree
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
Japanese does not; [the readings of the sentences follow from the rule](##rows_readings). A relative
raised above the matrix tense escapes the rule, and [covers its narrow scope
readings](##Model.sawWide_of_sawNarrow). A theory with no rule [wrongly dates what *would* describes
before the speech time](##triple_index_precedes_speech). A present under a past is a report de re
about a state, [which lasts from the claim through the report](##DoubleAccess.exists_sup_le).

## Implementation notes

* An LF is a `PhraseStructure.Tree` and is interpreted by `Tree.interp`, at indices of a world and
  an interval, a clause denoting a proposition: the rule-by-rule translation of (40) comes out of
  type-driven composition, with `who` and `poss` carrying rules (7b) and (8b) of chapter 3. The LFs
  are written out after QR; QR is not an operation here.
* Chapter 2's *command* is `sCommand` and chapter 3's *c-command* is `RoseTree.cCommand`, both from
  `Syntax/Command.lean`, so the two statements of the rule are one definition, `Deletable`, at two
  relations. The auxiliaries are stacked in the order of their scope, the alternative p. 259 allows
  to the flat Aux with its Feature Percolation Convention. A VP-adjoined object scopes over the
  subject, harmlessly as the subjects are names, since a type-driven engine has no rule (40.4b).
* The subset relation $\subseteq$ is `≤` of `NonemptyInterval`, and $<$ is
  `NonemptyInterval.Precedes`, which on closed intervals is the non-abutting order of p. 204 on
  dense time. The Japanese present
  has only its present translation here, not its future one (p. 211). The aspect of the complement,
  which a simultaneous reading needs stative (p. 72), is not modelled, as the fragment does not
  either (p. 200).
* The second fragment is stated at its translations (64') and (69), with the times of events and
  states given by `Event.TemporalTrace`; its Aux copying and Davidsonian lexicon are not encoded.

## Errata

* Rule 14 on p. 273 translates the empty tense as PRES or as a future; p. 255, p. 274 and (40) give
  PRES alone, and the future translation would give (28) the subsequent reading p. 97 denies it.
* (44) line 4 and (45) line 4 are said to be equivalent (p. 116), and the wide scope reading to
  cover the narrow ones (p. 119). Both compare a noun at different times, which p. 148 takes to be
  read at the temporal index, so [they need a noun stable over time](##Model.metNarrow_not_metWide).
* The rule generates the LF (70') of [a sentence the consultants reject](##rule_overgenerates);
  p. 142 leaves this open.
* The explanation of (29) on pp. 267-268 reads c-command as "the first NP or S node", where the
  definition on p. 253 has the first branching node.
* The second line of (25c') prints *John Past say*, for *John Pres woll say*. The note on p. 261
  gives PRES as the choice for *want* and *promise*, for the future. (59') and (59'') have *say*
  for the *claim* of (59). The example on p. 137 is numbered (71), the number of the example on
  p. 140, where (65) is due. On pp. 326-327 *(63)* stands for (64'), and (65) has *pregnant* for
  the *in the room* of (64).

## TODO

* The anchoring conditions for tense of section 2.3.1 and the interaction of QR, intensionality and
  scope of section 2.2, with *seek* and the examples (62) and (66).
* Hypotheses 3 to 5 of chapter 4, with the counterfactual of (48).
* The temporal adverbial clauses of section 2.4.4, and the second Japanese fragment.

## References

* [ogihara-1989]
* [partee-1973]
* [prior-1967]
* [reichenbach-1947]
* [langacker-1969]
* [davidson-1967]
-/

@[expose] public section

namespace Ogihara1989

open Montague ModalLogic Tense Partee1973 PhraseStructure PhraseStructure.Tree Core.Order
open scoped Denotes SetRel Ty

section ReferenceInterval

variable {T : Type*} [LinearOrder T] {P : NonemptyInterval T → Prop} {K σ : NonemptyInterval T}
  {g : Assignment (NonemptyInterval T)} {n : ℕ}

/-- The past restricted to the salient interval `K` holds when the clause held at a past
subinterval of `K`, as *Yes, I saw her* (`Examples.ex_1_57`) says of the day, (58) of chapter 1. It
is Partee's past tense with its index bound by an existential quantifier over the subintervals of
`K`. -/
theorem restricted_iff_exists_past :
    ◇[Allen.toSetRel Allen.precedes] (fun t ↦ t ≤ K ∧ P t) σ ↔
      ∃ t ≤ K, lambdaAbsG n (Past n P σ) g t := by
  simp [Past, Diamond, and_left_comm]

/-! ### The stove

*I didn't turn off the stove* (`Examples.ex_1_46a`), with `P` the times at which the speaker turns
off the stove and the time of the tense's index the salient interval. The sentence says that this
interval is past and has no subinterval at which the speaker turned off the stove. -/

-- (56): the salient interval is past, and the past restricted to it is denied
theorem no_subinterval_iff_not_restricted :
    Past n (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g ↔
      Perspective.Presup Allen.precedes σ (g n) ∧
        ¬ ◇[Allen.toSetRel Allen.precedes] (fun t ↦ t ≤ g n ∧ P t) σ :=
  ⟨fun h ↦ ⟨h.1, fun ⟨t, _, hle, hP⟩ ↦ h.2 ⟨t, hle, hP⟩⟩, fun h ↦ ⟨h.1, fun ⟨t, hle, hP⟩ ↦
    h.2 ⟨t, Perspective.presup_precedes.2 (NonemptyInterval.precedes_of_le_of_precedes hle
      (Perspective.presup_precedes.1 h.1)), hle, hP⟩⟩⟩

-- p. 49: a speaker who turned off the stove at no subinterval did not at the interval
theorem no_subinterval_entails_deictic (h : Past n (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g) :
    Past n (fun t ↦ ¬ P t) σ g :=
  ⟨h.1, fun hP ↦ h.2 ⟨_, le_rfl, hP⟩⟩

-- p. 49: a speaker who turned off the stove within the interval did not at the interval, so
-- the referential reading is true where the sentence is false
theorem deictic_too_weak :
    ∃ (σ : NonemptyInterval ℤ) (g : Assignment (NonemptyInterval ℤ))
      (P : NonemptyInterval ℤ → Prop),
      Past 0 (fun t ↦ ¬ P t) σ g ∧ ¬ Past 0 (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g :=
  ⟨.pure 10, fun _ ↦ ⟨(0, 5), by decide⟩, (· = .pure 3),
    ⟨Perspective.presup_precedes.2 (by decide), by decide⟩,
    fun h ↦ h.2 ⟨.pure 3, by decide, rfl⟩⟩

-- (46b) entails (56)
theorem never_entails_no_subinterval (hn : Perspective.Presup Allen.precedes σ (g n))
    (h : ¬ ◇[Allen.toSetRel Allen.precedes] P σ) : Past n (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g :=
  ⟨hn, fun ⟨t, hle, hP⟩ ↦ h ⟨t, Perspective.presup_precedes.2
    (NonemptyInterval.precedes_of_le_of_precedes hle (Perspective.presup_precedes.1 hn)), hP⟩⟩

-- p. 41: the sentence is true of a speaker who turned off the stove before the interval
theorem never_too_strong :
    ∃ (σ : NonemptyInterval ℤ) (g : Assignment (NonemptyInterval ℤ))
      (P : NonemptyInterval ℤ → Prop),
      Past 0 (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g ∧ ◇[Allen.toSetRel Allen.precedes] P σ := by
  refine ⟨.pure 10, fun _ ↦ ⟨(5, 6), by decide⟩, (· = .pure 1),
    ⟨Perspective.presup_precedes.2 (by decide), ?_⟩, .pure 1,
    Perspective.presup_precedes.2 (by decide), rfl⟩
  rintro ⟨t, ht, rfl⟩
  exact absurd (NonemptyInterval.le_def.1 ht).1 (by decide)

end ReferenceInterval

/-! ### Logical forms

The trees below are the LFs of the fragments, with the node of each translation rule, so that the
two definitions of the dissertation's rule read off them as they stand. -/

/-- The value of a tense feature, [+past] or [-past]. -/
inductive Feature
  /-- [+past] -/
  | past
  /-- [-past] -/
  | nonpast
  deriving DecidableEq

/-- The names of the fragment. A pronoun is the name it is bound to. -/
inductive Name
  | john | mary | bill | speaker | addressee | everybody
  deriving DecidableEq

/-- The common nouns of the fragment. -/
inductive Noun
  | man | fish
  deriving DecidableEq

/-- The intransitive predicates of the fragment. -/
inductive IV
  | ill | inAustin | laughing | supporter | holding | alive | ignorant | magicTricks | win | come
  | wellKnown
  deriving DecidableEq

/-- The transitive verbs of the fragment. -/
inductive TV
  | see | meet | buy | amuse
  deriving DecidableEq

/-- The verbs of the fragment that take a clausal complement. An object of *tell* or *ask* is left
out, since no tense depends on it. -/
inductive Att
  | say | claim | think | tell | promise | ask
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
  /-- A common noun. -/
  | noun (c : Noun)
  /-- An intransitive predicate. -/
  | iv (c : IV)
  /-- A transitive verb. -/
  | tv (c : TV)
  /-- A verb with a clausal complement. -/
  | att (c : Att)
  /-- The noun *claim*, which takes a clausal complement. -/
  | claim
  /-- The indefinite article. -/
  | a
  /-- The possessive morpheme. -/
  | poss
  /-- The relative pronoun with the rule that joins a relative clause to its head noun. -/
  | who
  deriving DecidableEq

namespace Word

/-- The tense feature of a word: [+past] on the past, the perfect and *earlier*, [-past] on the
present. -/
def feature : Word → Option Feature
  | past _ | perf _ | earlier _ => some .past
  | pres | ru => some .nonpast
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

end Word

/-- An LF is a constituency tree over these terminals. -/
abbrev LF := Tree Cat Word

/-- The word at a position of an LF. -/
def wordAt (t : LF) (p : TreePath) : Option Word :=
  t[p.toList]?.bind fun s ↦ s.value.terminal?.map (·.2)

/-- The last position of a word in an LF, the lowest of the occurrences of a tense in a chain of
clauses. -/
def lastOf (t : LF) (w : Word) : Option TreePath :=
  ((t.vertices.map TreePath.mk).filter (wordAt t · = some w)).getLast?

/-- The tense feature at a position of an LF. -/
def featureAt (t : LF) (p : TreePath) : Option Feature := (wordAt t p).bind Word.feature

/-- The positions of the tense morphemes of an LF. -/
def tenses (t : LF) : Finset TreePath :=
  ((t.vertices.map TreePath.mk).filter fun p ↦ ∃ w ∈ wordAt t p, w.IsTense).toFinset

/-- The positions of the tense features of an LF. -/
def features (t : LF) : Finset TreePath :=
  ((t.vertices.map TreePath.mk).filter fun p ↦ (featureAt t p).isSome).toFinset

/-- `a` is local for `b` among the positions `F` under the command relation `R` when `a` commands
`b` and no other member of `F` that `a` commands commands `b`. A node commands itself on the
reflexive relations of `Syntax/Command.lean`, so *other* excludes `b` as well as `a`. -/
def IsLocal (R : SetRel TreePath TreePath) (F : Finset TreePath) (a b : TreePath) : Prop :=
  a ∈ F ∧ b ∈ F ∧ a ≠ b ∧ a ~[R] b ∧ ∀ c ∈ F, c ≠ a → c ≠ b → a ~[R] c → ¬ c ~[R] b

instance {R : SetRel TreePath TreePath} [∀ a b, Decidable (a ~[R] b)] {F : Finset TreePath}
    {a b : TreePath} : Decidable (IsLocal R F a b) := by
  unfold IsLocal; infer_instance

/-- A tense `b` can be deleted when something local for it has the value of its feature. -/
def Deletable (R : SetRel TreePath TreePath) (F : Finset TreePath) (t : LF) (b : TreePath) : Prop :=
  (∃ w ∈ wordAt t b, w.IsTense) ∧ ∃ a ∈ F, IsLocal R F a b ∧ featureAt t a = featureAt t b

instance {R : SetRel TreePath TreePath} [∀ a b, Decidable (a ~[R] b)] {F : Finset TreePath}
    {t : LF} {b : TreePath} : Decidable (Deletable R F t b) := by
  unfold Deletable; infer_instance

/-- The rule of chapter 2: delete a tense under an occurrence of the same morpheme that is local for
it, where a tense commands what the first S above it dominates. -/
abbrev TenseDeletable (t : LF) : TreePath → Prop := Deletable (sCommand t) (tenses t) t

/-- The rule of chapter 3: delete a tense morpheme whose feature has the value of its local tense
feature, where a feature c-commands what the first branching node above it dominates. -/
abbrev TenseFeatureDeletable (t : LF) : TreePath → Prop :=
  Deletable (RoseTree.cCommand t) (features t) t

/-- One application of the rule of chapter 3 at some position of an LF, leaving an empty tense. -/
def Deletes (t t' : LF) : Prop :=
  ∃ b, TenseFeatureDeletable t b ∧ t' = t.replaceAt b.toList (Tree.terminal .Aux .null)

/-! ### The shapes of the LFs

[S Tns (woll) (have + en) NP VP], with the auxiliaries in the order of their scope and the subject
below them, as rule (40.1) interprets it. -/

/-- The auxiliaries below the tense of a clause, each over the next. -/
def auxes : List Word → LF → LF
  | [], b => b
  | w :: ws, b => .node .Aux [.terminal .Aux w, auxes ws b]

/-- A clause with a tense, further auxiliaries and an untensed body. -/
def clause (t : Word) (ws : List Word) (b : LF) : LF := .node .S [.terminal .Aux t, auxes ws b]

/-- An untensed sentence, a subject and a predicate. -/
def untensed (x : Name) (vp : LF) : LF := .node .V [.terminal .N (.name x), vp]

/-- An intransitive predicate of a name. -/
def intrans (x : Name) (c : IV) : LF := untensed x (.terminal .V (.iv c))

/-- A verb with a clausal complement. -/
def complement (v : Att) (s : LF) : LF := .node .V [.terminal .V (.att v), .node .C [s]]

/-- *a* with a noun and a relative clause, whose relative pronoun binds the trace `k`. -/
def aNoun (n : Noun) (k : ℕ) (s : LF) : LF :=
  .node .N [.terminal .Det .a, .node .N [.terminal .N (.noun n),
    .node .C [.terminal .C .who, .bind k .C s]]]

/-- The clause of a relative whose subject is the trace `k`. -/
def relClause (k : ℕ) (t : Word) (ws : List Word) (c : IV) : LF :=
  clause t ws (.node .V [.trace k .N, .terminal .V (.iv c)])

/-- A transitive verb with the trace `k` as its object and a subject. -/
def tvTrace (x : Name) (v : TV) (k : ℕ) : LF :=
  untensed x (.node .V [.terminal .V (.tv v), .trace k .N])

/-- The object `np` raised to the VP, within the scope of the tense. -/
def vpAdjoined (np : LF) (k : ℕ) (x : Name) (v : TV) : LF :=
  .adjoin .V [np, .bind k .V (tvTrace x v k)]

/-- The object `np` raised to the S, outside the scope of the tense `t`. -/
def sAdjoined (np : LF) (k : ℕ) (t : Word) (x : Name) (v : TV) : LF :=
  .adjoin .S [np, .bind k .S (clause t [] (tvTrace x v k))]

/-- *John said that Mary was ill* with the tense `t` in the complement, (1a) and (2a,b) of chapter
2, and in (49) with the empty tense. -/
def saidIll (t : Word) : LF :=
  clause (.past 1) [] (untensed .john (complement .say (clause t [] (intrans .mary .ill))))

/-- *John saw a man who was laughing* with the relative raised to the S, (46a'). -/
def sawWide (t : Word) : LF :=
  sAdjoined (aNoun .man 1 (relClause 1 t [] .laughing)) 0 (.past 1) .john .see

/-- *John saw a man who was laughing* with the relative raised to the VP, (46b') and (46c'). -/
def sawNarrow (t : Word) : LF :=
  clause (.past 1) [] (vpAdjoined (aNoun .man 1 (relClause 1 t [] .laughing)) 0 .john .see)

-- (27a), (46a): "The Tense Deletion Rule does not apply. (The condition is not met.)"
theorem frozen_sawWide : ∃ b ∈ lastOf (sawWide (.past 2)) (.past 2),
    ¬ TenseDeletable (sawWide (.past 2)) b ∧ ¬ TenseFeatureDeletable (sawWide (.past 2)) b := by
  decide

-- (49)
theorem deletes_saidIll : Deletes (saidIll (.past 2)) (saidIll .null) :=
  ⟨⟨[1, 1, 1, 0, 0]⟩, by decide, rfl⟩

-- (27b), (46b)
theorem deletes_sawNarrow : Deletes (sawNarrow (.past 2)) (sawNarrow .null) :=
  ⟨⟨[1, 0, 1, 1, 1, 0, 0]⟩, by decide, rfl⟩

/-- *John said that he would buy a fish that was still alive*, (37), with the tenses of the
complement and of the relative clause. -/
def fish (t t' : Word) : LF :=
  clause (.past 1) [] (untensed .john (complement .say (clause t [.woll 3]
    (vpAdjoined (aNoun .fish 1 (relClause 1 t' [] .alive)) 0 .john .buy))))

-- (37'): both lower pasts are deleted, in either order
theorem deletes_fish :
    Relation.ReflTransGen Deletes (fish (.past 2) (.past 4)) (fish .null .null) :=
  .head ⟨⟨[1, 1, 1, 0, 0]⟩, by decide, rfl⟩ <|
    .single ⟨⟨[1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0]⟩, by decide, rfl⟩

/-- *John met a man who will become his great supporter*, (42b), with the relative raised to the S
or to the VP. -/
def metWide : LF :=
  sAdjoined (aNoun .man 1 (relClause 1 .pres [.woll 3] .supporter)) 0 (.past 2) .john .meet

/-- The relative of (42b) raised to the VP, (45). -/
def metNarrow : LF :=
  clause (.past 2) [] (vpAdjoined (aNoun .man 1 (relClause 1 .pres [.woll 3] .supporter)) 0 .john
    .meet)

/-- The possessive noun phrase of (60) and (61), with an adjective and a noun complement. -/
def claimNP (adj t : Word) : LF :=
  .node .N [.node .Det [.terminal .N (.name .john), .terminal .Det .poss],
    .node .N [.terminal .Adj adj, .node .N [.terminal .N .claim,
      .node .C [clause t [.woll 3] (intrans .mary .win)]]]]

/-- *John's earlier claim that Mary would win the prize is well-known*, (60b). -/
def claimClause (adj t : Word) : LF :=
  clause .pres [] (.node .V [claimNP adj t, .terminal .V (.iv .wellKnown)])

/-! ### Interpretation -/

section Interpretation

variable {E W T : Type} [LinearOrder T]

/-- The index of evaluation is a world and an interval. -/
abbrev Index (W T : Type) [LinearOrder T] := W × NonemptyInterval T

/-- A model of the fragment fixes the speech time $s^*$, the reference intervals $t_{Rn}$, and the
interpretation of the constants at each index. -/
structure Model (E W T : Type) [LinearOrder T] where
  /-- The speech time. -/
  s : NonemptyInterval T
  /-- The reference intervals. -/
  R : ℕ → NonemptyInterval T
  /-- The bearers of the names. -/
  name : Name → E
  /-- The extensions of the nouns at an index. -/
  noun : Noun → E → Index W T → Prop
  /-- The extensions of the intransitive predicates at an index. -/
  iv : IV → E → Index W T → Prop
  /-- `tv c x y` holds when `x` stands to `y` in the relation `c`. -/
  tv : TV → E → E → Index W T → Prop
  /-- `att c p x` holds when `x` stands to the proposition `p` in the relation `c`. -/
  att : Att → (Index W T → Prop) → E → Index W T → Prop
  /-- `claim p x` holds when `x` is a claim of `p`. -/
  claim : (Index W T → Prop) → E → Index W T → Prop
  /-- `poss x y` holds when `y` is related to `x`, as a claim to its author. -/
  poss : E → E → Index W T → Prop
  /-- `truth x` holds at an index when `x` speaks the truth there. -/
  truth : E → Index W T → Prop

namespace Model

variable (M : Model E W T) (g : Assignment E) {i : Index W T}

/-- The past restricted to the reference interval `n`: a time before the evaluation time within
that interval at which `p` holds. -/
def past (n : ℕ) (p : Index W T → Prop) : Index W T → Prop :=
  fun i ↦ ◇[Allen.toSetRel Allen.precedes] (fun t ↦ t ≤ M.R n ∧ p (i.1, t)) i.2

/-- The future restricted to the reference interval `n`. -/
def fut (n : ℕ) (p : Index W T → Prop) : Index W T → Prop :=
  fun i ↦ ◇[Allen.toSetRel (Allen.ofPosition ⟦future⟧)] (fun t ↦ t ≤ M.R n ∧ p (i.1, t)) i.2

/-- The English present, $\exists t[\mathrm{NOW}(t) \wedge \mathrm{AT}(t, p)]$: `p` at the speech
time, wherever it is evaluated. -/
def now (p : Index W T → Prop) : Index W T → Prop := fun i ↦ p (i.1, M.s)

variable {M}

theorem past_iff {n : ℕ} {p : Index W T → Prop} {i : Index W T} :
    M.past n p i ↔ ∃ t, t.Precedes i.2 ∧ t ≤ M.R n ∧ p (i.1, t) := by
  simp [past, Diamond, Allen.relation_mem_precedes]

theorem fut_iff {n : ℕ} {p : Index W T → Prop} {i : Index W T} :
    M.fut n p i ↔ ∃ t, i.2.Precedes t ∧ t ≤ M.R n ∧ p (i.1, t) := by
  simp [fut, Diamond, Allen.relation_mem_ofPosition, Denotes.denote, Tense.denote]

variable (M)

/-- The translations of the words, (40) and the lexicon of chapter 3. -/
def lex : Word → Option (Denotation E (Index W T))
  | .past n | .perf n => some ⟨(.s ⇒ .t) ⇒ .s ⇒ .t, M.past n⟩
  | .pres => some ⟨(.s ⇒ .t) ⇒ .s ⇒ .t, M.now⟩
  | .null | .ru => some ⟨(.s ⇒ .t) ⇒ .s ⇒ .t, id⟩
  | .woll n | .inf n => some ⟨(.s ⇒ .t) ⇒ .s ⇒ .t, M.fut n⟩
  | .earlier n => some ⟨(.e ⇒ .s ⇒ .t) ⇒ .e ⇒ .s ⇒ .t,
      fun (P : E → Index W T → Prop) x ↦ M.past n (P x)⟩
  | .current => some ⟨(.e ⇒ .s ⇒ .t) ⇒ .e ⇒ .s ⇒ .t, id⟩
  | .name c => some ⟨.e, M.name c⟩
  | .noun c => some ⟨.e ⇒ .s ⇒ .t, M.noun c⟩
  | .iv c => some ⟨.e ⇒ .s ⇒ .t, M.iv c⟩
  | .tv c => some ⟨.e ⇒ .e ⇒ .s ⇒ .t, fun y x ↦ M.tv c x y⟩
  | .att c => some ⟨(.s ⇒ .t) ⇒ .e ⇒ .s ⇒ .t, M.att c⟩
  | .claim => some ⟨(.s ⇒ .t) ⇒ .e ⇒ .s ⇒ .t, M.claim⟩
  | .a => some ⟨(.e ⇒ .s ⇒ .t) ⇒ (.e ⇒ .s ⇒ .t) ⇒ .s ⇒ .t,
      fun (P Q : E → Index W T → Prop) i ↦ ∃ x, P x i ∧ Q x i⟩
  | .poss => some ⟨.e ⇒ (.e ⇒ .s ⇒ .t) ⇒ (.e ⇒ .s ⇒ .t) ⇒ .s ⇒ .t,
      fun x (P Q : E → Index W T → Prop) i ↦ ∃ y, (∀ z, P z i ∧ M.poss x z i ↔ z = y) ∧ Q y i⟩
  | .who => some ⟨(.e ⇒ .s ⇒ .t) ⇒ (.e ⇒ .s ⇒ .t) ⇒ .e ⇒ .s ⇒ .t,
      fun (Q P : E → Index W T → Prop) x i ↦ P x i ∧ Q x i⟩

/-- An LF holds at an index under an assignment when it translates to a proposition true there. -/
def Holds (t : LF) (i : Index W T) : Prop :=
  match Tree.interp M.lex g t with
  | some ⟨.fn .s .t, p⟩ => p i
  | _ => False

/-- The necessary condition (54) of chapter 2 on the saying relation: a speaker who stands in it to
a proposition speaks the truth at the index exactly when the proposition is true there. -/
def Reliable : Prop := ∀ p x i, M.att .say p x i → (M.truth x i ↔ p i)

/-- A noun is stable when what it is true of does not vary with the time. -/
def Stable (c : Noun) : Prop := ∀ x i t, M.noun c x i ↔ M.noun c x (i.1, t)

variable {M}

attribute [local simp] Holds clause auxes untensed intrans complement aNoun relClause tvTrace
  vpAdjoined sAdjoined saidIll sawWide sawNarrow metWide metNarrow fish claimNP claimClause lex

/-! ### Complement clauses -/

-- (55) of chapter 2: the empty tense leaves the complement untensed, and a speaker who spoke the
-- truth said something true at the index of the saying, which is all that the simultaneous reading
-- amounts to
theorem simultaneous_of_truth (hM : M.Reliable) (h : M.Holds g (saidIll .null) i) :
    ∃ t, t.Precedes i.2 ∧ t ≤ M.R 1 ∧
      (M.truth (M.name .john) (i.1, t) → M.iv .ill (M.name .mary) (i.1, t)) := by
  obtain ⟨t, ht, hR, hs⟩ := past_iff.1 (by simpa using h :
    M.past 1 (M.att .say (M.iv .ill (M.name .mary)) (M.name .john)) i)
  exact ⟨t, ht, hR, (hM _ _ _ hs).1⟩

-- (56) of chapter 2, the shifted reading the dissertation leaves to the reader
theorem shifted_of_truth (hM : M.Reliable) (h : M.Holds g (saidIll (.past 2)) i) :
    ∃ t, t.Precedes i.2 ∧ t ≤ M.R 1 ∧ (M.truth (M.name .john) (i.1, t) →
      ∃ t', t'.Precedes t ∧ t' ≤ M.R 2 ∧ M.iv .ill (M.name .mary) (i.1, t')) := by
  obtain ⟨t, ht, hR, hs⟩ := past_iff.1 (by simpa using h :
    M.past 1 (M.att .say (M.past 2 (M.iv .ill (M.name .mary))) (M.name .john)) i)
  exact ⟨t, ht, hR, fun hT ↦ past_iff.1 ((hM _ _ _ hs).1 hT)⟩

-- (3'') of chapter 4, the wrong prediction of the first fragment: a past claim about the speech
-- time, with no commitment about the time of the claim
theorem now_of_truth (hM : M.Reliable) (h : M.Holds g (saidIll .pres) i) :
    ∃ t, t.Precedes i.2 ∧ t ≤ M.R 1 ∧
      (M.truth (M.name .john) (i.1, t) → M.iv .ill (M.name .mary) (i.1, M.s)) := by
  obtain ⟨t, ht, hR, hs⟩ := past_iff.1 (by simpa using h :
    M.past 1 (M.att .say (M.now (M.iv .ill (M.name .mary))) (M.name .john)) i)
  exact ⟨t, ht, hR, (hM _ _ _ hs).1⟩

/-! ### Relative clauses

*John saw a man who was laughing*, (46), with the three derivations of its three-way ambiguity. -/

-- (46a'), line 4: the laughing and the seeing are unordered
theorem holds_sawWide : M.Holds g (sawWide (.past 2)) i ↔
    ∃ x, (M.noun .man x i ∧ M.past 2 (M.iv .laughing x) i) ∧
      M.past 1 (fun i ↦ M.tv .see (M.name .john) x i) i := by
  simp

-- (46b'), line 5: simultaneous
theorem holds_sawNarrow_null : M.Holds g (sawNarrow .null) i ↔
    M.past 1 (fun i ↦ ∃ x, (M.noun .man x i ∧ M.iv .laughing x i) ∧
      M.tv .see (M.name .john) x i) i := by
  simp

-- (46c'), line 4: shifted
theorem holds_sawNarrow_past : M.Holds g (sawNarrow (.past 2)) i ↔
    M.past 1 (fun i ↦ ∃ x, (M.noun .man x i ∧ M.past 2 (M.iv .laughing x) i) ∧
      M.tv .see (M.name .john) x i) i := by
  simp

/-- The wide scope reading of the relative covers both narrow scope readings, so that they do not
strike speakers as independent readings. This needs a noun that holds at the speech time of what
it held of at the past time, and a reference interval of the relative tense wide enough to contain
the time the narrow reading finds. -/
theorem sawWide_of_sawNarrow (hman : M.Stable .man) (hR : M.R 1 ≤ M.R 2)
    (h : M.Holds g (sawNarrow .null) i ∨ M.Holds g (sawNarrow (.past 2)) i) :
    M.Holds g (sawWide (.past 2)) i := by
  rw [holds_sawNarrow_null, holds_sawNarrow_past] at h
  rw [holds_sawWide]
  rcases h with h | h <;> obtain ⟨t, ht, htR, x, ⟨hn, hl⟩, hs⟩ := past_iff.1 h
  · exact ⟨x, ⟨(hman x i t).2 hn, past_iff.2 ⟨t, ht, htR.trans hR, hl⟩⟩,
      past_iff.2 ⟨t, ht, htR, hs⟩⟩
  · obtain ⟨t', ht', htR', hl⟩ := past_iff.1 hl
    exact ⟨x, ⟨(hman x i t).2 hn,
      past_iff.2 ⟨t', NonemptyInterval.precedes_trans ht' ht, htR', hl⟩⟩,
      past_iff.2 ⟨t, ht, htR, hs⟩⟩

-- p. 97: a laughing after the seeing comes from the wide scope reading alone
theorem forward_shifted {a b : NonemptyInterval T} (hab : a.Precedes b)
    (hsee : ∀ i x, M.tv .see (M.name .john) x i → i.2 = a)
    (hlaugh : ∀ i x, M.iv .laughing x i → i.2 = b) :
    ¬ M.Holds g (sawNarrow .null) i ∧ ¬ M.Holds g (sawNarrow (.past 2)) i := by
  rw [holds_sawNarrow_null, holds_sawNarrow_past]
  constructor
  · intro h
    obtain ⟨t, -, -, x, ⟨-, hl⟩, hs⟩ := past_iff.1 h
    have hba : b = a := (hlaugh _ _ hl).symm.trans (hsee _ _ hs)
    exact NonemptyInterval.precedes_irrefl a (hba ▸ hab)
  · intro h
    obtain ⟨t, -, -, x, ⟨-, hl⟩, hs⟩ := past_iff.1 h
    obtain ⟨t', ht', -, hl⟩ := past_iff.1 hl
    obtain rfl : t = a := hsee _ _ hs
    obtain rfl : t' = b := hlaugh _ _ hl
    exact NonemptyInterval.precedes_asymm hab ht'

-- (44) line 4
theorem holds_metWide : M.Holds g metWide i ↔
    ∃ x, (M.noun .man x i ∧ M.now (M.fut 3 (M.iv .supporter x)) i) ∧
      M.past 2 (fun i ↦ M.tv .meet (M.name .john) x i) i := by
  simp

-- (45) line 4
theorem holds_metNarrow : M.Holds g metNarrow i ↔
    M.past 2 (fun i ↦ ∃ x, (M.noun .man x i ∧ M.now (M.fut 3 (M.iv .supporter x)) i) ∧
      M.tv .meet (M.name .john) x i) i := by
  simp

-- p. 116: the present in a relative denotes the speech time wherever the relative is scoped
theorem metWide_iff_metNarrow (hman : M.Stable .man) :
    M.Holds g metWide i ↔ M.Holds g metNarrow i := by
  simp only [holds_metWide, holds_metNarrow, past_iff]
  constructor
  · rintro ⟨x, ⟨hn, hf⟩, t, ht, htR, hm⟩
    exact ⟨t, ht, htR, x, ⟨(hman x i t).1 hn, hf⟩, hm⟩
  · rintro ⟨t, ht, htR, x, ⟨hn, hf⟩, hm⟩
    exact ⟨x, ⟨(hman x i t).2 hn, hf⟩, t, ht, htR, hm⟩

-- p. 116: of a man who is a man only at the meeting, (45) line 4 holds and (44) line 4 does not
theorem metNarrow_not_metWide {a : NonemptyInterval T} {x : E} (ha : a.Precedes i.2)
    (haR : a ≤ M.R 2) (hman : M.noun .man x (i.1, a)) (hnow : ∀ y, ¬ M.noun .man y i)
    (hf : M.now (M.fut 3 (M.iv .supporter x)) (i.1, a))
    (hm : M.tv .meet (M.name .john) x (i.1, a)) :
    M.Holds g metNarrow i ∧ ¬ M.Holds g metWide i := by
  rw [holds_metNarrow, holds_metWide, past_iff]
  refine ⟨⟨a, ha, haR, x, ⟨hman, hf⟩, hm⟩, ?_⟩
  rintro ⟨y, ⟨hn, -⟩, -⟩
  exact hnow y hn

-- (37'): the fish is alive at the time of the buying, which can follow the speech time
theorem holds_fish : M.Holds g (fish .null .null) i ↔
    M.past 1 (M.att .say (M.fut 3 fun i ↦ ∃ x, (M.noun .fish x i ∧ M.iv .alive x i) ∧
      M.tv .buy (M.name .john) x i) (M.name .john)) i := by
  simp

-- (29), (30) line 11 of chapter 3: the empty tense of *would* leaves the winning after the
-- claiming, which *earlier* places before the time of *well-known*, and the noun phrase denotes the
-- unique claim made by John
theorem holds_claimClause : M.Holds g (claimClause (.earlier 1) .null) i ↔
    M.now (fun i ↦ ∃ y, (∀ z, M.past 1 (M.claim (M.fut 3 (M.iv .win (M.name .mary))) z) i ∧
      M.poss (M.name .john) z i ↔ z = y) ∧ M.iv .wellKnown y i) i := by
  simp

-- (47a''), (47a'): the Japanese present is the time of the matrix verb in a narrow relative and the
-- speech time in a wide one
theorem holds_sawNarrow_ru : (M.Holds g (sawNarrow .ru) i ↔
    M.past 1 (fun i ↦ ∃ x, (M.noun .man x i ∧ M.iv .laughing x i) ∧
      M.tv .see (M.name .john) x i) i) ∧ (M.Holds g (sawWide .ru) i ↔
    ∃ x, (M.noun .man x i ∧ M.iv .laughing x i) ∧
      M.past 1 (fun i ↦ M.tv .see (M.name .john) x i) i) := by
  simp

end Model

-- `Word.cell` is what the translation says: a time in the cell at which the argument holds
theorem position_mem_cell {M : Model E W T} {w : Word} {τ : (Index W T → Prop) → Index W T → Prop}
    {p : Index W T → Prop} {i : Index W T} (h : M.lex w = some ⟨(.s ⇒ .t) ⇒ .s ⇒ .t, τ⟩)
    (hw : w ≠ .pres) (hτ : τ p i) : ∃ t, t.position i.2 ∈ w.cell ∧ p (i.1, t) := by
  cases w <;> simp only [Model.lex, Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and,
    reduceCtorEq, and_false, false_and, Ty.fn.injEq, and_true, reduceCtorEq] at h <;> subst h
  case pres => exact absurd rfl hw
  case null | ru => exact ⟨i.2, by simp [Word.cell, Denotes.denote, Tense.denote], hτ⟩
  case past | perf =>
    obtain ⟨t, ht, -, hp⟩ := Model.past_iff.1 hτ
    exact ⟨t, by simpa [Word.cell, Denotes.denote, Tense.denote] using ht, hp⟩
  case woll | inf =>
    obtain ⟨t, ht, -, hp⟩ := Model.fut_iff.1 hτ
    exact ⟨t, by simpa [Word.cell, Denotes.denote, Tense.denote] using ht, hp⟩

end Interpretation

/-! ### The sentences -/

/-- The two languages compared: English has the rule and Japanese does not. -/
inductive Language
  /-- English. -/
  | english
  /-- Japanese. -/
  | japanese
  deriving DecidableEq

/-- A language has tense deletion: English does, Japanese does not. -/
def Language.HasDeletion : Language → Prop
  | .english => True
  | .japanese => False

instance : DecidablePred Language.HasDeletion
  | .english => isTrue trivial
  | .japanese => isFalse id

/-- A tense is commanded in an LF when some other tense feature c-commands it. -/
def Commanded (t : LF) (b : TreePath) : Prop :=
  ∃ a ∈ features t, a ≠ b ∧ a ~[RoseTree.cCommand t] b

instance (t : LF) (b : TreePath) : Decidable (Commanded t b) := by unfold Commanded; infer_instance

/-- The positions of the time of a tense against the time of the verb above it: its cell, with the
position of the empty tense where the rule can delete it, and every position where it has escaped
every tense, as a relative raised over the matrix tense has. -/
def positionsAt (L : Language) (t : LF) (w : Word) : Finset Ordering :=
  match lastOf t w with
  | none => ⊥
  | some b =>
    if Commanded t b then
      w.cell ⊔ if L.HasDeletion ∧ TenseFeatureDeletable t b then ⟦Tense.present⟧ else ⊥
    else ⊤

-- the parameter of `pastUnderPast`, read off the tree
theorem positionsAt_saidIll (L : Language) :
    positionsAt L (saidIll (.past 2)) (.past 2) = pastUnderPast L.HasDeletion := by
  cases L <;> decide

/-- What a row says of a tense. -/
inductive Reading
  /-- The time of the tense stands so to the time of the verb above it. -/
  | position (o : Ordering)
  /-- The tense is empty at LF. -/
  | emptyTense
  deriving DecidableEq

/-- A reading a row names. -/
def reading? (w : String) : Option Reading :=
  [("shifted", Reading.position .lt), ("simultaneous", .position .eq),
    ("subsequent", .position .gt), ("empty tense", .emptyTense)].lookup w

/-- The language of a row, by its Glottocode. -/
def language? (g : Glottocode) : Option Language :=
  [(.english, Language.english), (.japanese, .japanese)].lookup g

/-- A sentence with the LFs that QR gives it has a reading of the tense `w` when one of its LFs
gives the tense that position, or its language deletes the tense in one of them. -/
def Predicted (L : Language) (lfs : List LF) (w : Word) : Reading → Prop
  | .position o => ∃ t ∈ lfs, o ∈ positionsAt L t w
  | .emptyTense => L.HasDeletion ∧ ∃ t ∈ lfs, ∃ b ∈ lastOf t w, TenseFeatureDeletable t b

instance (L : Language) (lfs : List LF) (w : Word) : DecidablePred (Predicted L lfs w) := fun r ↦ by
  cases r <;> unfold Predicted <;> infer_instance

/-- *John said that Mary was in Austin* and its kin: a matrix clause over a complement. -/
def report (t : Word) (ws : List Word) (x : Name) (v : Att) (t' : Word) (ws' : List Word)
    (y : Name) (c : IV) : LF :=
  clause t ws (untensed x (complement v (clause t' ws' (intrans y c))))

/-- A sentence of two levels of embedding, the lowest clause with the past `past 4`. -/
def twoLevels (t : Word) (ws : List Word) (x : Name) (v : Att) (t' : Word) (ws' : List Word)
    (y : Name) (v' : Att) (c : IV) : LF :=
  clause t ws (untensed x (complement v (clause t' ws' (untensed y (complement v'
    (clause (.past 4) [] (intrans y c)))))))

/-- The rows on a tense, each with the LFs of its sentence and the tense its readings are about. -/
def rows : List (Datum × List LF × Word) :=
  [(Examples.ex_2_1a, [saidIll (.past 2)], .past 2),
   (Examples.ex_2_2a, [saidIll (.past 2)], .past 2),
   (Examples.ex_2_2b, [saidIll .ru], .ru),
   (Examples.ex_2_25a, [report (.past 1) [] .john .say .pres [] .mary .inAustin], .pres),
   (Examples.ex_2_25b, [report (.past 1) [] .john .say (.past 2) [] .mary .inAustin], .past 2),
   (Examples.ex_2_25c, [report .pres [.woll 1] .john .say .pres [] .mary .inAustin], .pres),
   (Examples.ex_2_27, [sawWide (.past 2), sawNarrow (.past 2)], .past 2),
   (Examples.ex_2_28, [saidIll (.past 2)], .past 2),
   (Examples.ex_2_33a,
    [clause (.past 2) [] (vpAdjoined (aNoun .man 1 (relClause 1 (.past 4) [.woll 3] .supporter)) 0
      .john .meet)], .past 4),
   (Examples.ex_2_33b, [metWide, metNarrow], .pres),
   (Examples.ex_2_34,
    [clause .pres [.woll 1] (vpAdjoined (aNoun .man 1 (relClause 1 .pres [] .holding)) 0 .john
      .meet)], .pres),
   (Examples.ex_2_37, [fish (.past 2) (.past 4)], .past 4),
   (Examples.ex_2_47a, [sawWide .ru, sawNarrow .ru], .ru),
   (Examples.ex_2_47b, [sawWide (.past 2), sawNarrow (.past 2)], .past 2),
   (Examples.ex_2_59, [report .pres [.woll 1, .perf 2] .john .claim (.past 3) [] .john .ill],
    .past 3),
   (Examples.ex_2_60b, [claimClause (.earlier 1) (.past 2)], .past 2),
   (Examples.ex_2_61,
    [clause .pres [] (vpAdjoined (claimNP .current (.past 2)) 0 .everybody .amuse)], .past 2),
   (Examples.ex_2_97, [twoLevels (.past 1) [] .speaker .tell (.past 2) [.woll 3] .addressee .say
      .magicTricks], .past 4),
   (Examples.ex_2_103, [twoLevels (.past 1) [] .speaker .tell .pres [.woll 3] .addressee .say
      .magicTricks], .past 4),
   (Examples.ex_2_104, [twoLevels (.past 1) [] .john .promise (.inf 2) [] .john .say .ignorant],
    .past 4),
   (Examples.ex_2_105, [twoLevels .pres [.woll 1] .john .promise (.inf 2) [] .john .say .ignorant],
    .past 4),
   (Examples.ex_2_139a,
    [twoLevels (.past 1) [] .john .think .pres [.woll 2] .bill .claim .ignorant], .past 4),
   (Examples.ex_2_139b, [twoLevels (.past 1) [] .john .think (.past 2) [.woll 3] .bill .claim
      .ignorant], .past 4),
   (Examples.ex_2_139c, [twoLevels (.past 1) [] .john .ask (.inf 2) [] .bill .claim .ignorant],
    .past 4)]

/-- Every reading of the rows is available exactly when the sentence's LFs and the rule allow it. -/
theorem rows_readings :
    ∀ x ∈ rows, x.1.readings ≠ [] ∧ ∀ r ∈ x.1.readings, ∃ L ∈ language? x.1.language,
      ∃ ρ ∈ reading? r.1, (Predicted L x.2.1 x.2.2 ρ ↔ r.2 = .acceptable) := by
  decide +kernel

-- (59), (60b) and note 54 of chapter 2: the first rule misses the triggers that are not tenses
theorem tenseDeletable_misses_triggers :
    (∃ b ∈ lastOf (report .pres [.woll 1, .perf 2] .john .claim (.past 3) [] .john .ill) (.past 3),
      ¬ TenseDeletable (report .pres [.woll 1, .perf 2] .john .claim (.past 3) [] .john .ill) b ∧
      TenseFeatureDeletable (report .pres [.woll 1, .perf 2] .john .claim (.past 3) [] .john .ill)
        b) ∧
    (∃ b ∈ lastOf (claimClause (.earlier 1) (.past 2)) (.past 2),
      ¬ TenseDeletable (claimClause (.earlier 1) (.past 2)) b ∧
      TenseFeatureDeletable (claimClause (.earlier 1) (.past 2)) b) := by
  decide

/-- *John met a man who would buy a fish which was still alive*, (70'). -/
def metBuyer : LF :=
  clause (.past 1) [] (vpAdjoined (aNoun .man 1 (clause (.past 2) [.woll 3]
    (vpAdjoined (aNoun .fish 5 (relClause 5 (.past 4) [] .alive)) 6 .john .buy))) 0 .john .meet)

-- p. 140: the rule generates (70'), which the consultants reject; p. 142 leaves this open
theorem rule_overgenerates :
    (∃ b ∈ lastOf metBuyer (.past 4), TenseFeatureDeletable metBuyer b) ∧
      (∃ b ∈ lastOf metBuyer (.past 2), TenseFeatureDeletable metBuyer b) ∧
      Examples.ex_2_70.readings = [("simultaneous", .unacceptable)] := by
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
  simp only [ReichenbachFrame.eventPosition_eq_gt, ReichenbachFrame.eventPosition_eq_eq] at h₂ h₃
  rw [h₃, ← hR]
  exact h₂.ne

/-- The future feature of the three-index system of chapter 2. -/
inductive FutFeature
  /-- [+fut] -/
  | fut
  /-- [-fut] -/
  | nonfut

/-- The set of intervals a past feature denotes, against the quasi-speech time `j`. -/
def pastSet : Feature → NonemptyInterval T → NonemptyInterval T → Prop
  | .past, j, t => t.Precedes j
  | .nonpast, j, t => ¬ t.Precedes j

/-- The set of intervals a future feature denotes, against the evaluation time `i`. -/
def futSet : FutFeature → NonemptyInterval T → NonemptyInterval T → Prop
  | .fut, i, t => i.Precedes t
  | .nonfut, i, t => ¬ i.Precedes t

/-- The tense operators of the three-index system: only [-past][+fut] updates the quasi-speech
time. -/
def tns : Feature → FutFeature → (W → NonemptyInterval T → NonemptyInterval T → Prop) →
    W → NonemptyInterval T → NonemptyInterval T → Prop
  | .nonpast, .fut, φ, w, i, j => ∃ t, pastSet .nonpast j t ∧ futSet .fut i t ∧ φ w t t
  | α, β, φ, w, i, j => ∃ t, pastSet α j t ∧ futSet β i t ∧ φ w t j

/-- Without the rule, a past always means the past of the quasi-speech time, so *John said that Mary
would come to Austin* wrongly places the coming before the speech time, (126). -/
theorem triple_index_precedes_speech {E : Type} {M : Model E W T} (hM : M.Reliable) {w : W}
    (h : tns .past .nonfut (fun w t j ↦ M.att .say
      (fun i ↦ tns .past .fut (fun w t _ ↦ M.iv .come (M.name .mary) (w, t)) i.1 i.2 j)
      (M.name .john) (w, t)) w M.s M.s) :
    ∃ t, t.Precedes M.s ∧ (M.truth (M.name .john) (w, t) →
      ∃ t', t.Precedes t' ∧ t'.Precedes M.s ∧ M.iv .come (M.name .mary) (w, t')) := by
  obtain ⟨t, ht, -, hs⟩ := h
  refine ⟨t, ht, fun hT ↦ ?_⟩
  obtain ⟨t', ht', hf, hc⟩ := (hM _ _ _ hs).1 hT
  exact ⟨t', hf, ht', hc⟩

-- (125): with the rule, the past of *would* is empty, and nothing places the coming before the
-- speech time
theorem would_of_truth {E : Type} {M : Model E W T} (g : Assignment E) (hM : M.Reliable) {w : W}
    (h : M.Holds g (report (.past 1) [] .john .say .null [.woll 3] .mary .come) (w, M.s)) :
    ∃ t, t.Precedes M.s ∧ (M.truth (M.name .john) (w, t) →
      ∃ t', t.Precedes t' ∧ t' ≤ M.R 3 ∧ M.iv .come (M.name .mary) (w, t')) := by
  obtain ⟨t, ht, -, hs⟩ := Model.past_iff.1 (by
    simpa [Model.Holds, report, clause, auxes, untensed, intrans, complement, Model.lex] using h :
    M.past 1 (M.att .say (M.fut 3 (M.iv .come (M.name .mary))) (M.name .john)) (w, M.s))
  exact ⟨t, ht, fun hT ↦ Model.fut_iff.1 ((hM _ _ _ hs).1 hT)⟩

end Rivals

/-! ### Double access

A present under a past: chapter 4 rejects two hypotheses on the truth conditions of *John said
that Mary is pregnant*, and chapter 5 derives the sentence as a de re report about a state. -/

section DoubleAccess

variable {E W Ev St T : Type*} [LinearOrder T]

/-- Hypothesis 1, (14): the speaker said the proposition, and it is true in the actual world at an
interval properly including the speech time and the time of the saying. -/
def Hypothesis1 (att : (W × NonemptyInterval T → Prop) → E → W × NonemptyInterval T → Prop)
    (p : W × NonemptyInterval T → Prop) (x : E) (σ R : NonemptyInterval T) (w : W) : Prop :=
  ∃ t, t.Precedes σ ∧ t ≤ R ∧ att p x (w, t) ∧ ∃ t', σ < t' ∧ t ≤ t' ∧ p (w, t')

/-- Hypothesis 2, (20): the speaker said of an interval properly including the speech time and the
time of the saying that the proposition is true at it. -/
def Hypothesis2 (att : (W × NonemptyInterval T → Prop) → E → W × NonemptyInterval T → Prop)
    (p : W × NonemptyInterval T → Prop) (x : E) (σ R : NonemptyInterval T) (w : W) : Prop :=
  ∃ t, t.Precedes σ ∧ t ≤ R ∧ ∃ t', σ < t' ∧ t ≤ t' ∧ att (fun i ↦ p (i.1, t')) x (w, t)

-- (17): the report is true though the proposition is false at every time
theorem hypothesis1_fails
    {att : (W × NonemptyInterval T → Prop) → E → W × NonemptyInterval T → Prop}
    {p : W × NonemptyInterval T → Prop} {x : E} {σ R : NonemptyInterval T} {w : W}
    (hp : ∀ t, ¬ p (w, t)) :
    ¬ Hypothesis1 att p x σ R w ∧ Examples.ex_4_17d.judgment = .acceptable :=
  ⟨fun ⟨_, _, _, _, t', _, _, h⟩ ↦ hp t' h, rfl⟩

-- (24): John's attitude on June 20th is the same in both cases, and they are judged differently
theorem hypothesis2_fails
    (att : (W × NonemptyInterval T → Prop) → E → W × NonemptyInterval T → Prop)
    (p : W × NonemptyInterval T → Prop) (x : E) (σ R : NonemptyInterval T) (w : W) :
    ¬ ((Hypothesis2 att p x σ R w ↔ Examples.ex_4_24_Case_1.judgment = .acceptable) ∧
      (Hypothesis2 att p x σ R w ↔ Examples.ex_4_24_Case_2.judgment = .acceptable)) := by
  rintro ⟨h₁, h₂⟩
  exact absurd (h₂.1 (h₁.2 rfl)) (by decide)

variable [Event.TemporalTrace Ev T] [Event.TemporalTrace St T]

open Event (τ)

/-- (64'), the second fragment's translation of a present under a past: a state that obtains at
the speech time, (60b), and a past event of saying of that state that it obtains and is of the kind
`P`, a report de re about the state. -/
def DoubleAccess (say : Ev → E → (W × NonemptyInterval T → Prop) → W → Prop) (P : St → W → Prop)
    (x : E) (σ R : NonemptyInterval T) (w : W) : Prop :=
  ∃ s, σ ≤ τ s ∧ ∃ e, (τ e).Precedes σ ∧ τ e ≤ R ∧ say e x (fun i ↦ i.2 ≤ τ s ∧ P s i.1) w

/-- What the event says is true at its time in some world, the least that (11) of chapter 4
requires of a claim. -/
def Consistent (say : Ev → E → (W × NonemptyInterval T → Prop) → W → Prop) : Prop :=
  ∀ e x p w, say e x p w → ∃ w', p (w', τ e)

/-- A state of which a consistent claim is reported by a present under a past lasts from the claim
through the speech time, the second conjunct of Hypothesis 5: this is the double access of the
reading, and no assertion in any world about Mary. -/
theorem DoubleAccess.exists_sup_le {say : Ev → E → (W × NonemptyInterval T → Prop) → W → Prop}
    {P : St → W → Prop} {x : E} {σ R : NonemptyInterval T} {w : W} (hsay : Consistent say)
    (h : DoubleAccess say P x σ R w) :
    ∃ (s : St) (e : Ev), (τ e).Precedes σ ∧ τ e ⊔ σ ≤ τ s := by
  obtain ⟨s, hs, e, he, -, hsaid⟩ := h
  obtain ⟨_, hes, -⟩ := hsay _ _ _ _ hsaid
  exact ⟨s, e, he, sup_le hes hs⟩

-- (61)-(63), (49): with a factive verb the state is actual, so the sentence entails (62''): the
-- complement is true at an extended now including the time of the verb
theorem factive_extended_now {say : Ev → E → (W × NonemptyInterval T → Prop) → W → Prop}
    {P : St → W → Prop} {x : E} {σ R : NonemptyInterval T} {w : W}
    (hsay : ∀ e x p w, say e x p w → p (w, τ e)) (h : DoubleAccess say P x σ R w) :
    ∃ e : Ev, (τ e).Precedes σ ∧ ∃ t', σ < t' ∧ τ e ≤ t' ∧ ∃ s : St, t' ≤ τ s ∧ P s w := by
  obtain ⟨s, hs, e, he, -, hsaid⟩ := h
  obtain ⟨hes, hP⟩ := hsay _ _ _ _ hsaid
  refine ⟨e, he, τ e ⊔ σ, lt_of_le_of_ne le_sup_right fun heq ↦ ?_, le_sup_left, s,
    sup_le hes hs, hP⟩
  exact he.not_overlaps (NonemptyInterval.overlaps_of_le (heq ▸ le_sup_left))

-- (67)-(69): *John said that Mary will come to Austin* places the coming after the saying and
-- after the speech time, by the Aux copying that the temporal directionality isomorphism requires
theorem future_double_access {say : Ev → E → (W × NonemptyInterval T → Prop) → W → Prop}
    {P : Ev → W → Prop} {x : E} {σ R₁ R₂ : NonemptyInterval T} {w : W} (hsay : Consistent say)
    (h : ∃ e : Ev, σ.Precedes (τ e) ∧ τ e ≤ R₁ ∧ ∃ e' : Ev, (τ e').Precedes σ ∧ τ e' ≤ R₂ ∧
      say e' x (fun i ↦ ∃ t, i.2.Precedes t ∧ t ≤ R₁ ∧ t = τ e ∧ P e i.1) w) :
    ∃ e e' : Ev, σ.Precedes (τ e) ∧ (τ e').Precedes (τ e) := by
  obtain ⟨e, he, -, e', -, -, hsaid⟩ := h
  obtain ⟨_, t, het, -, rfl, -⟩ := hsay _ _ _ _ hsaid
  exact ⟨e, e', he, het⟩

/-! The rows of chapter 4 are reports of one claim at the time `a` by the time `b`: the state
responsible for the claim lasts through the report or ends before it. -/

/-- The worlds of a report: the actual one and the one the claim describes. -/
inductive World
  /-- The actual world. -/
  | actual
  /-- The world the claim describes. -/
  | claimed
  deriving DecidableEq

/-- The saying of a report: at the time `a` the speaker says of the state `I` that it obtains, in
the claimed world. -/
def said (a : T) (I : NonemptyInterval T) :
    NonemptyInterval T → E → (World × NonemptyInterval T → Prop) → World → Prop :=
  fun e _ p _ ↦ e = .pure a ∧ p = fun i ↦ i.2 ≤ I ∧ i.1 = .claimed

theorem doubleAccess_said_iff {a b : T} (hab : a < b) {I : NonemptyInterval T} {x : E} {w : World} :
    DoubleAccess (Ev := NonemptyInterval T) (St := NonemptyInterval T) (said a I)
        (fun _ w ↦ w = .claimed) x (.pure b) (.pure a ⊔ .pure b) w ↔ .pure b ≤ I := by
  constructor
  · rintro ⟨s, hs, e, -, -, -, hp⟩
    have hsI : s = I := le_antisymm
      ((congrFun hp (.claimed, s)).mp ⟨le_rfl, rfl⟩).1
      ((congrFun hp (.claimed, I)).mpr ⟨le_rfl, rfl⟩).1
    exact hsI ▸ hs
  · intro h
    exact ⟨I, h, .pure a, hab, le_sup_left, rfl, rfl⟩

/-- The interval of the state a row describes. -/
def stateOf (a b : T) (row : Datum) : Option (NonemptyInterval T) :=
  (row.feature? "state").bind ([("continues", NonemptyInterval.pure a ⊔ .pure b),
    ("ends", .pure a)].lookup ·)

-- (17), (24), (27), (28), (34), (35), (43): a report is acceptable exactly when the state
-- responsible for the claim lasts through it
theorem rows_doubleAccess {a b : T} (hab : a < b) {x : E} {w : World} :
    ∀ row ∈ [Examples.ex_4_17d, Examples.ex_4_24_Case_1, Examples.ex_4_24_Case_2, Examples.ex_4_27d,
        Examples.ex_4_28, Examples.ex_4_34d, Examples.ex_4_35, Examples.ex_4_43c],
      ∃ I ∈ stateOf a b row, (DoubleAccess (Ev := NonemptyInterval T) (St := NonemptyInterval T)
        (said a I) (fun _ w ↦ w = .claimed) x (.pure b) (.pure a ⊔ .pure b) w ↔
          row.judgment = .acceptable) := by
  have hno : ¬ (NonemptyInterval.pure b ≤ NonemptyInterval.pure a) := fun h ↦
    absurd (NonemptyInterval.le_def.1 h).2 (not_le.2 hab)
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact ⟨_, rfl, (doubleAccess_said_iff hab).trans (iff_of_true le_sup_right rfl)⟩
    | exact ⟨_, rfl, (doubleAccess_said_iff hab).trans (iff_of_false hno (by decide))⟩

end DoubleAccess

end Ogihara1989
