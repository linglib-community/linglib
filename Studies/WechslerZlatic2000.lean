module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Agreement.Hierarchy
public import Linglib.Data.Examples.WechslerZlatic2000

/-!
# Wechsler & Zlatić (2000): A Theory of Agreement and Its Application to Serbo-Croatian

This file formalizes [wechsler-zlatic-2000]'s theory of agreement. A noun carries two
feature bundles: CONCORD, with case, number and gender, read by NP-internal targets, and the
referential INDEX of [pollard-sag-1994], with person, number and gender, read by pronouns and
finite verbs. Declension class, concord, index and semantics are tied by a chain of three
binary constraints (4): a class I noun has masculine or neuter concord gender and a class II or
III noun feminine (`DecCon`); concord and index share number and gender (`ConInd`); a noun
restricted to females or males has feminine or masculine index, and an aggregate-denoting
count noun a plural one, other nouns a singular one (`IndSem`). A regular noun satisfies every
link, and a hybrid noun breaks one: *Steva* the first, *deca* the second, *makaze* the third,
while *braća* breaks two (`brokenLinks`). Of the seven two-type mismatch patterns a priori,
the three the theory predicts are the initial segments of the chain, and exactly those are
attested (`predicted_patterns`). Agreement itself is compatibility of a target's bundle with
the bundle it reads, which on *deca* puts feminine singular on the modifiers and neuter plural
on the pronoun at once (`deca_mixed_agreement`) and lets the concord-unmarked plural relative
pronoun *kojih* modify it. Since only the index touches the semantics, semantic agreement can
surface on a concord reader only if it surfaces on the pronouns: the index readers form a
lower set of [corbett-1991]'s Agreement Hierarchy however the open predicate position is
resolved (`indexReaders_lowerSet`).

## Implementation notes

Lexical entries carry the singular citation form's concord number for count nouns and the
lexically fixed values for collectives and pluralia tantum, whose declension is the value
"pl" of the paper's summary table rather than a numbered class, and whose concord gender,
left open there, is supplied as feminine. The disjunctively sex-specified nouns *sudija* and
*mušterija* are entered as their resolved variants. Concord-ending syncretism, participle
agreement, coordination resolution and the HPSG spell-out function are not formalized.

## References

* [wechsler-zlatic-2000]
* [corbett-1991]
* [corbett-1998]
* [pollard-sag-1994]
-/

@[expose] public section

namespace WechslerZlatic2000

/-! ### Feature bundles -/

/-- The Serbo-Croatian declension classes of Table 1, with pluralia tantum outside the
singular classification. -/
inductive Declension
  | I | II | III | pluralia
  deriving DecidableEq, Repr

/-- The lexical CONCORD features, number and gender; case is contextual. -/
structure ConcordF where
  number : Number
  gender : UD.Gender
  deriving DecidableEq, Repr

/-- The INDEX features (8): person, number and gender. -/
structure IndexF where
  person : Person
  number : Number
  gender : UD.Gender
  deriving DecidableEq, Repr

/-- The sex a noun's referent is lexically restricted to, if any (18). -/
inductive SexRestriction
  | female | male | unrestricted
  deriving DecidableEq, Repr

/-- The COUNT value of a count noun (22). -/
inductive Count
  | one | aggregate
  deriving DecidableEq, Repr

/-- The agreement-relevant lexical entry of a noun: the four positions of the chain. -/
structure Noun where
  decl : Declension
  concord : ConcordF
  index : IndexF
  sex : SexRestriction
  count : Option Count
  deriving DecidableEq, Repr

/-! ### The chain (4) -/

/-- DecCon (15): class I nouns have masculine or neuter concord gender, class II and III
nouns feminine; the constraint does not reach pluralia tantum. -/
def DecCon (n : Noun) : Prop :=
  match n.decl with
  | .I => n.concord.gender = .Masc ∨ n.concord.gender = .Neut
  | .II | .III => n.concord.gender = .Fem
  | .pluralia => True

/-- ConInd (17): concord and index share number and gender. -/
def ConInd (n : Noun) : Prop :=
  n.concord.number = n.index.number ∧ n.concord.gender = n.index.gender

/-- IndSemGen (18): a female-restricted noun has feminine index, a male-restricted one
masculine. -/
def IndSemGen (n : Noun) : Prop :=
  (n.sex = .female → n.index.gender = .Fem) ∧
    (n.sex = .male → n.index.gender = .Masc)

/-- IndSemNum (22): aggregate reference gives plural index, anything else singular. -/
def IndSemNum (n : Noun) : Prop :=
  match n.count with
  | some .aggregate => n.index.number = .plural
  | _ => n.index.number = .singular

/-- The index–semantics link, both halves. -/
def IndSem (n : Noun) : Prop := IndSemGen n ∧ IndSemNum n

instance (n : Noun) : Decidable (DecCon n) := by unfold DecCon; split <;> infer_instance
instance (n : Noun) : Decidable (ConInd n) := by unfold ConInd; infer_instance
instance (n : Noun) : Decidable (IndSemGen n) := by unfold IndSemGen; infer_instance
instance (n : Noun) : Decidable (IndSemNum n) := by unfold IndSemNum; split <;> infer_instance
instance (n : Noun) : Decidable (IndSem n) := inferInstanceAs (Decidable (_ ∧ _))

/-- The three links of the chain, left to right. -/
inductive ChainLink
  | decCon | conInd | indSem
  deriving DecidableEq, Repr, Fintype

/-- Whether a link holds of a noun. -/
def linkHolds (n : Noun) : ChainLink → Prop
  | .decCon => DecCon n
  | .conInd => ConInd n
  | .indSem => IndSem n

instance (n : Noun) (l : ChainLink) : Decidable (linkHolds n l) := by
  cases l <;> simp only [linkHolds] <;> infer_instance

/-- The mismatch pattern of a noun: its broken links (5). -/
def brokenLinks (n : Noun) : Finset ChainLink := Finset.univ.filter (λ l => ¬ linkHolds n l)

/-- A noun is regular when every link holds. -/
def Regular (n : Noun) : Prop := ∀ l, linkHolds n l

instance (n : Noun) : Decidable (Regular n) := inferInstanceAs (Decidable (∀ _, _))

/-! ### The lexicon (Table 3) -/

/-- *knjiga* 'book': regular class II. -/
def knjiga : Noun :=
  { decl := .II, concord := ⟨.singular, .Fem⟩, index := ⟨.third, .singular, .Fem⟩,
    sex := .unrestricted, count := some .one }

/-- *rad* 'work': regular class I. -/
def rad : Noun :=
  { decl := .I, concord := ⟨.singular, .Masc⟩,
    index := ⟨.third, .singular, .Masc⟩, sex := .unrestricted, count := some .one }

/-- *žena* 'woman': regular and female-denoting. -/
def žena : Noun :=
  { decl := .II, concord := ⟨.singular, .Fem⟩, index := ⟨.third, .singular, .Fem⟩,
    sex := .female, count := some .one }

/-- *muž* 'husband': regular and male-denoting. -/
def muž : Noun :=
  { decl := .I, concord := ⟨.singular, .Masc⟩,
    index := ⟨.third, .singular, .Masc⟩, sex := .male, count := some .one }

/-- *kit* 'whale': masculine with no sex restriction (21). -/
def kit : Noun := rad

/-- *Steva*: a male name declining in class II (28); *sudija* 'judge' and *mušterija*
'customer' applied to males pattern alike (19a), (30b). -/
def steva : Noun :=
  { decl := .II, concord := ⟨.singular, .Masc⟩,
    index := ⟨.third, .singular, .Masc⟩, sex := .male, count := some .one }

/-- *sudija* applied to a female (19b): the other resolution of the disjunction (20). -/
def sudijaFemale : Noun := { žena with }

/-- *mušterija* with the male restriction absent (30a), (32a). -/
def mušterijaUnsexed : Noun := knjiga

/-- *deca* 'children': feminine singular concord, neuter plural index (45). -/
def deca : Noun :=
  { decl := .II, concord := ⟨.singular, .Fem⟩, index := ⟨.third, .plural, .Neut⟩,
    sex := .unrestricted, count := some .aggregate }

/-- *gospoda* 'gentlemen': like *deca*, male-restricted with masculine plural index (40). -/
def gospoda : Noun :=
  { decl := .II, concord := ⟨.singular, .Fem⟩, index := ⟨.third, .plural, .Masc⟩,
    sex := .male, count := some .aggregate }

/-- *braća* 'brothers': male-restricted with feminine singular concord and neuter plural
index (39). -/
def braća : Noun :=
  { decl := .II, concord := ⟨.singular, .Fem⟩, index := ⟨.third, .plural, .Neut⟩,
    sex := .male, count := some .aggregate }

/-- *makaze* 'scissors' read as one pair: plural throughout against singular reference (35). -/
def makaze : Noun :=
  { decl := .pluralia, concord := ⟨.plural, .Fem⟩,
    index := ⟨.third, .plural, .Fem⟩, sex := .unrestricted, count := some .one }

/-- *devojče* 'girl': female-denoting with neuter index (11). -/
def devojče : Noun :=
  { decl := .I, concord := ⟨.singular, .Neut⟩, index := ⟨.third, .singular, .Neut⟩,
    sex := .female, count := some .one }

theorem regular_lexicon :
    Regular knjiga ∧ Regular rad ∧ Regular žena ∧ Regular muž ∧ Regular sudijaFemale ∧
      Regular mušterijaUnsexed := by
  decide

/-- The hybrid nouns break exactly the links of Table 3. -/
theorem hybrid_lexicon :
    brokenLinks steva = {.decCon} ∧ brokenLinks deca = {.conInd} ∧
      brokenLinks gospoda = {.conInd} ∧ brokenLinks makaze = {.indSem} ∧
      brokenLinks devojče = {.indSem} ∧ brokenLinks braća = {.conInd, .indSem} := by
  decide

/-! ### Seven patterns, three predicted -/

/-- A two-type mismatch pattern is a bipartition of the four chain positions, identified with
the cell of the declension position. -/
def bipartitions : Finset (Finset (Fin 4)) :=
  Finset.univ.filter λ S => (0 : Fin 4) ∈ S ∧ S ≠ Finset.univ

/-- The position of the break at a link. -/
def ChainLink.position : ChainLink → Fin 4
  | .decCon => 0
  | .conInd => 1
  | .indSem => 2

/-- The cell of the declension position when the chain breaks at one link: the positions up
to the break. -/
def cell (l : ChainLink) : Finset (Fin 4) := Finset.univ.filter (· ≤ l.position)

/-- A pattern the chain can produce is an initial segment of the chain. -/
def IsInitialSegment (S : Finset (Fin 4)) : Prop := ∀ i ∈ S, ∀ j, j ≤ i → j ∈ S

instance : DecidablePred IsInitialSegment := λ _ => inferInstanceAs (Decidable (∀ _, _))

/-- Seven patterns a priori (n. 3). -/
theorem seven_patterns : bipartitions.card = 7 := by decide

theorem predicted_patterns :
    bipartitions.filter IsInitialSegment = Finset.univ.image cell ∧
      (Finset.univ.image cell).card = 3 ∧
      brokenLinks steva = {.decCon} ∧ brokenLinks deca = {.conInd} ∧
        brokenLinks makaze = {.indSem} := by
  decide

/-! ### Agreement as compatibility -/

open Agreement (Bundle)

/-- The bundle of an NP-internal target: its case, and its concord number and gender where it
is marked for them. -/
def concordBundle (c : Case) (n : Flat Number) (g : Flat UD.Gender) : Bundle
  | .case => c
  | .number => n
  | .gender => g
  | _ => ⊥

/-- The bundle of an index-reading target, a pronoun or a finite verb. -/
def indexBundle (p : Person) (n : Number) (g : UD.Gender) : Bundle
  | .person => p
  | .number => n
  | .gender => g
  | _ => ⊥

/-- The noun's concord bundle at a case value. -/
def Noun.concordAt (n : Noun) (c : Case) : Bundle := concordBundle c n.concord.number n.concord.gender

/-- The noun's index bundle. -/
def Noun.indexTarget (n : Noun) : Bundle := indexBundle n.index.person n.index.number n.index.gender

/-- Concord: the target's bundle is compatible with the noun's concord at the case. -/
def ConcordAgrees (a : Bundle) (n : Noun) (c : Case) : Prop := Compat a (n.concordAt c)

/-- Index agreement: the target's bundle is compatible with the noun's index. -/
def IndexAgrees (p : Bundle) (n : Noun) : Prop := Compat p n.indexTarget

instance (a : Bundle) (n : Noun) (c : Case) : Decidable (ConcordAgrees a n c) :=
  inferInstanceAs (Decidable (Compat _ _))

instance (p : Bundle) (n : Noun) : Decidable (IndexAgrees p n) :=
  inferInstanceAs (Decidable (Compat _ _))

/-- *ovu dobru*: accusative feminine singular modifiers (41). -/
def ovu : Bundle := concordBundle .acc Number.singular UD.Gender.Fem

/-- *ona*: the neuter plural pronoun (41). -/
def ona : Bundle := indexBundle .third .plural .Neut

/-- *kojih*: the genitive plural relative pronoun, unmarked for concord number and gender
(57). -/
def kojih : Bundle := concordBundle .gen ⊥ ⊥

/-- On a regular noun the two bundles agree with the same targets (6). -/
theorem knjiga_agrees :
    ConcordAgrees (concordBundle .nom Number.singular UD.Gender.Fem) knjiga .nom ∧
      IndexAgrees (indexBundle .third .singular .Fem) knjiga := by
  decide

/-- Mixed agreement on *deca* (41): the feminine singular modifiers read CONCORD and the
neuter plural pronoun reads INDEX, while the crossed targets fail (62). -/
theorem deca_mixed_agreement :
    ConcordAgrees ovu deca .acc ∧ IndexAgrees ona deca ∧
      ¬ ConcordAgrees (concordBundle .acc Number.plural UD.Gender.Neut) deca .acc ∧
      ¬ IndexAgrees (indexBundle .third .singular .Fem) deca := by
  decide

/-- *kojih* agrees in concord with *deca* (56): unmarked features are compatible with
anything. -/
theorem kojih_agrees : ConcordAgrees kojih deca .gen := by decide

theorem compat_number_indexTarget_iff (n : Noun) (hn : ConInd n) (t : Bundle) :
    Compat (t .number) (n.indexTarget .number) ↔
      Compat (t .number) (n.concordAt .nom .number) := by
  simp only [Noun.indexTarget, Noun.concordAt, indexBundle, concordBundle, hn.1]

/-! ### The Agreement Hierarchy (63) -/

open _root_.Agreement

/-- Whether a position reads INDEX, given how the open predicate position resolves:
attributives lack indices, pronouns have them. -/
def readsIndex (predicate : Bool) : Position → Prop
  | .attributive => False
  | .predicate => predicate
  | .relativePronoun => True
  | .personalPronoun => True

instance (p : Bool) : DecidablePred (readsIndex p) := λ t => by
  cases t <;> simp only [readsIndex] <;> infer_instance

theorem indexReaders_lowerSet (p : Bool) : IsLowerSet {t | readsIndex p t} := by
  intro t u hle hmem
  revert t u
  cases p <;> decide

end WechslerZlatic2000
