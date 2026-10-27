module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Agreement.Hierarchy
public import Linglib.Data.Examples.WechslerZlatic2000

/-!
# Wechsler & Zlatić (2000): A Theory of Agreement and Its Application to Serbo-Croatian

This file formalizes [wechsler-zlatic-2000]'s theory of agreement. A noun carries two feature
bundles: CONCORD, with case, number and gender, read by NP-internal targets, and the referential
INDEX of [pollard-sag-1994], with person, number and gender, read by pronouns and finite verbs.
Declension class, concord, index and semantics are tied by a chain of three binary constraints
(4): `DecCon` (15), `ConInd` (17) and `IndSem` (18), (22). A regular noun satisfies every link,
so its agreement features are derived from its declension and semantics, not stipulated (26); a
hybrid noun breaks links, and the breaks cut the chain into contiguous cells, so of the seven
two-cell and six three-cell patterns a priori exactly the contiguous three and three can arise,
and exactly those are attested (n. 3, p. 824). Agreement itself is compatibility of a target's
bundle with the bundle it reads, which on *deca* puts feminine singular on the modifiers and
neuter plural on the pronoun at once, while a relative pronoun reads concord and index both,
through the features its form is marked for (57). Since only the index touches the semantics,
semantic agreement can surface on a concord reader only if it surfaces on the pronouns: the
index readers form a lower set of [corbett-1991]'s Agreement Hierarchy however the open
predicate position is resolved.

## Implementation notes

* Lexical entries carry the singular citation form's concord number for count nouns and the
  lexically fixed values for collectives and pluralia tantum, whose declension is the value
  "pl" of Table 3 rather than a numbered class, and whose concord gender, left open there, is
  supplied as feminine. The disjunctively sex-specified nouns *sudija* and *mušterija* are
  entered as their resolved variants (20), (32).
* The paper gives *telad*'s CONTENT (24) but no declension; the entries sit in the `DecCon`
  cells their concord genders force, class III for the feminine variant and class I for the
  neuter, a choice the paper does not make.
* *Majestad* (64) is recorded in the data; Spanish has no Serbo-Croatian declension, so it has
  no `Noun` entry. Coordination resolution ((51)–(53), n. 18), the participle question of §7.3
  ((13), (48), (49)) and n. 17's register effect are not formalized, so those rows pair only
  their unambiguous targets or none. Concord-ending syncretism and the HPSG spell-out function
  are not formalized.

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
def brokenLinks (n : Noun) : Finset ChainLink := Finset.univ.filter (fun l ↦ ¬ linkHolds n l)

/-- A noun is regular when every link holds. -/
def Regular (n : Noun) : Prop := ∀ l, linkHolds n l

instance (n : Noun) : Decidable (Regular n) := inferInstanceAs (Decidable (∀ _, _))

namespace Regular

variable {n : Noun}

/-- In a regular class II or III noun both genders are feminine, derived from the declension by
`DecCon` and `ConInd` rather than stipulated: of (26), "the only idiosyncratic information
stipulated in the above lexeme is declension class II" (p. 811). -/
theorem gender_derived (h : Regular n) (hd : n.decl = .II ∨ n.decl = .III) :
    n.concord.gender = .Fem ∧ n.index.gender = .Fem := by
  have hdc := h .decCon
  have hci := h .conInd
  simp only [linkHolds, DecCon, ConInd] at hdc hci
  rcases hd with hd | hd <;> rw [hd] at hdc <;> exact ⟨hdc, hci.2 ▸ hdc⟩

-- (15)
theorem gender_of_declI (h : Regular n) (hd : n.decl = .I) :
    n.concord.gender = .Masc ∨ n.concord.gender = .Neut := by
  have hdc := h .decCon
  simp only [linkHolds, DecCon] at hdc
  rwa [hd] at hdc

/-- In a regular noun both numbers are derived from the resolution of COUNT: "the INDEX number
values in 24 are derivable and need not be stipulated" (p. 811). -/
theorem index_number (h : Regular n) :
    n.index.number = (if n.count = some .aggregate then .plural else .singular) ∧
      n.concord.number = n.index.number := by
  have hsn := h .indSem
  have hci := h .conInd
  simp only [linkHolds, IndSem, IndSemNum, ConInd] at hsn hci
  refine ⟨?_, hci.1⟩
  rcases hc : n.count with - | - | - <;> rw [hc] at hsn <;> simp_all

end Regular

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
def kit : Noun :=
  { decl := .I, concord := ⟨.singular, .Masc⟩,
    index := ⟨.third, .singular, .Masc⟩, sex := .unrestricted, count := some .one }

/-- *dete* 'child': the singular of the inquorate pair (16), class I with neuter concord. -/
def dete : Noun :=
  { decl := .I, concord := ⟨.singular, .Neut⟩, index := ⟨.third, .singular, .Neut⟩,
    sex := .unrestricted, count := some .one }

/-- *Steva*: a male name declining in class II (28). -/
def steva : Noun :=
  { decl := .II, concord := ⟨.singular, .Masc⟩,
    index := ⟨.third, .singular, .Masc⟩, sex := .male, count := some .one }

/-- *sudija* 'judge' applied to a male (19a): the male resolution of the disjunction (20). -/
def sudijaMale : Noun :=
  { decl := .II, concord := ⟨.singular, .Masc⟩,
    index := ⟨.third, .singular, .Masc⟩, sex := .male, count := some .one }

/-- *sudija* applied to a female (19b): the other resolution of the disjunction (20). -/
def sudijaFemale : Noun :=
  { decl := .II, concord := ⟨.singular, .Fem⟩, index := ⟨.third, .singular, .Fem⟩,
    sex := .female, count := some .one }

/-- *mušterija* 'customer' with the male restriction present (30b), (32b). -/
def mušterijaMale : Noun :=
  { decl := .II, concord := ⟨.singular, .Masc⟩,
    index := ⟨.third, .singular, .Masc⟩, sex := .male, count := some .one }

/-- *mušterija* with the male restriction absent (30a), (32a). -/
def mušterijaUnsexed : Noun :=
  { decl := .II, concord := ⟨.singular, .Fem⟩, index := ⟨.third, .singular, .Fem⟩,
    sex := .unrestricted, count := some .one }

/-- *telad* '(a group of) calves' under its nonaggregate reading (24a): feminine singular
throughout. -/
def teladOne : Noun :=
  { decl := .III, concord := ⟨.singular, .Fem⟩, index := ⟨.third, .singular, .Fem⟩,
    sex := .unrestricted, count := some .one }

/-- *telad* under its aggregate reading (24b): neuter plural throughout. -/
def teladAggregate : Noun :=
  { decl := .I, concord := ⟨.plural, .Neut⟩, index := ⟨.third, .plural, .Neut⟩,
    sex := .unrestricted, count := some .aggregate }

/-- *sudije* 'judges': the aggregate variant of the plural stem, which loses the sex
restriction, so all features are feminine (33). -/
def sudijeAggregate : Noun :=
  { decl := .II, concord := ⟨.plural, .Fem⟩, index := ⟨.third, .plural, .Fem⟩,
    sex := .unrestricted, count := some .aggregate }

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

/-- *naočare* 'glasses' read as one pair: the *makaze* pattern (34). -/
def naočare : Noun :=
  { decl := .pluralia, concord := ⟨.plural, .Fem⟩,
    index := ⟨.third, .plural, .Fem⟩, sex := .unrestricted, count := some .one }

/-- *devojče* 'girl': female-denoting with neuter index (11). -/
def devojče : Noun :=
  { decl := .I, concord := ⟨.singular, .Neut⟩, index := ⟨.third, .singular, .Neut⟩,
    sex := .female, count := some .one }

theorem regular_lexicon :
    Regular knjiga ∧ Regular rad ∧ Regular žena ∧ Regular muž ∧ Regular kit ∧ Regular dete ∧
      Regular sudijaFemale ∧ Regular mušterijaUnsexed ∧ Regular teladOne ∧
      Regular teladAggregate ∧ Regular sudijeAggregate := by
  decide

/-- The hybrid nouns break exactly the links of Table 3. -/
theorem hybrid_lexicon :
    brokenLinks steva = {.decCon} ∧ brokenLinks sudijaMale = {.decCon} ∧
      brokenLinks mušterijaMale = {.decCon} ∧ brokenLinks deca = {.conInd} ∧
      brokenLinks gospoda = {.conInd} ∧ brokenLinks makaze = {.indSem} ∧
      brokenLinks naočare = {.indSem} ∧ brokenLinks devojče = {.indSem} ∧
      brokenLinks braća = {.conInd, .indSem} := by
  decide

/-! ### Patterns: breaks cut the chain into contiguous cells -/

/-- The position of the break at a link. -/
def ChainLink.position : ChainLink → Fin 4
  | .decCon => 0
  | .conInd => 1
  | .indSem => 2

/-- Two positions fall in one cell when no broken link cuts between them (5). -/
def SameCell (B : Finset ChainLink) (i j : Fin 4) : Prop :=
  ∀ l ∈ B, ¬ (min i j ≤ l.position ∧ l.position < max i j)

instance (B : Finset ChainLink) (i j : Fin 4) : Decidable (SameCell B i j) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The cells a set of breaks cuts the chain into. -/
def cells (B : Finset ChainLink) : Finset (Finset (Fin 4)) :=
  Finset.univ.image fun i ↦ Finset.univ.filter (SameCell B i)

/-- The cell of the declension position under a set of breaks. -/
def declCell (B : Finset ChainLink) : Finset (Fin 4) := Finset.univ.filter (SameCell B 0)

/-- An interval of chain positions. -/
def IsInterval (c : Finset (Fin 4)) : Prop := ∀ i ∈ c, ∀ j ∈ c, ∀ k, i ≤ k → k ≤ j → k ∈ c

instance : DecidablePred IsInterval := fun _ ↦ inferInstanceAs (Decidable (∀ _, _))

theorem cells_card : ∀ B : Finset ChainLink, (cells B).card = B.card + 1 := by decide

/-- "Only contiguous cells in a row are connected by constraints, so we predict exactly the
pattern observed" (p. 824): every cell any break set produces is an interval. -/
theorem cells_isInterval : ∀ B : Finset ChainLink, ∀ c ∈ cells B, IsInterval c := by decide

/-- A two-type mismatch pattern is a bipartition of the four chain positions, identified with
the cell of the declension position. -/
def bipartitions : Finset (Finset (Fin 4)) :=
  Finset.univ.filter fun S ↦ (0 : Fin 4) ∈ S ∧ S ≠ Finset.univ

-- n. 3
theorem seven_patterns : bipartitions.card = 7 := by decide

/-- The chain can produce exactly the bipartitions whose declension cell is an interval, the
declension cells of the three one-break patterns, and exactly those are attested (n. 3). -/
theorem predicted_patterns :
    bipartitions.filter IsInterval = (Finset.univ.image fun l : ChainLink ↦ declCell {l}) ∧
      (bipartitions.filter IsInterval).card = 3 ∧
      brokenLinks steva = {.decCon} ∧ brokenLinks deca = {.conInd} ∧
        brokenLinks makaze = {.indSem} := by
  decide

/-- A three-type pattern is a partition of the four positions into a doubleton and two
singletons, identified with its doubleton: six a priori, the three contiguous ones possible,
and *braća*, breaking `ConInd` and `IndSem`, shows the contiguous declension–concord
doubleton (p. 824). -/
theorem three_type_patterns :
    (Finset.univ.filter fun T : Finset (Fin 4) ↦ T.card = 2).card = 6 ∧
      ((Finset.univ.filter fun T : Finset (Fin 4) ↦ T.card = 2).filter IsInterval).card = 3 ∧
      cells (brokenLinks braća) = {{0, 1}, {2}, {3}} ∧
      declCell (brokenLinks braća) ∈
        (Finset.univ.filter fun T : Finset (Fin 4) ↦ T.card = 2).filter IsInterval := by
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

/-- The bundle of an index-reading target, a pronoun or a finite verb, in the features it is
marked for; finite verbs and auxiliaries are unmarked for gender (p. 816). -/
def indexBundle (p : Flat Person) (n : Flat Number) (g : Flat UD.Gender) : Bundle
  | .person => p
  | .number => n
  | .gender => g
  | _ => ⊥

/-- The noun's concord bundle at a case value. -/
def Noun.concordAt (n : Noun) (c : Case) : Bundle :=
  concordBundle c n.concord.number n.concord.gender

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
def ovu : Bundle := concordBundle .acc ↑Number.singular ↑UD.Gender.Fem

/-- *ona*: the neuter plural pronoun (41). -/
def ona : Bundle := indexBundle ↑Person.third ↑Number.plural ↑UD.Gender.Neut

-- (6)
theorem knjiga_agrees :
    ConcordAgrees (concordBundle .nom ↑Number.singular ↑UD.Gender.Fem) knjiga .nom ∧
      IndexAgrees (indexBundle ↑Person.third ↑Number.singular ↑UD.Gender.Fem) knjiga := by
  decide

/-- Mixed agreement on *deca* (41): the feminine singular modifiers read CONCORD and the
neuter plural pronoun reads INDEX, while the crossed targets fail. -/
theorem deca_mixed_agreement :
    ConcordAgrees ovu deca .acc ∧ IndexAgrees ona deca ∧
      ¬ ConcordAgrees (concordBundle .acc ↑Number.plural ↑UD.Gender.Neut) deca .acc ∧
      ¬ IndexAgrees (indexBundle ↑Person.third ↑Number.singular ↑UD.Gender.Fem) deca := by
  decide

-- p. 806
theorem indexAgrees_iff_concordAgrees {n : Noun} (hn : ConInd n) (c : Case)
    (num : Flat Number) (g : Flat UD.Gender) :
    IndexAgrees (indexBundle ⊥ num g) n ↔ ConcordAgrees (concordBundle c num g) n c := by
  simp only [IndexAgrees, ConcordAgrees, Noun.indexTarget, Noun.concordAt, compat_pi_iff]
  refine ⟨fun h d ↦ ?_, fun h d ↦ ?_⟩ <;> have h1 := h .number <;> have h2 := h .gender <;>
    cases d <;> simp_all [indexBundle, concordBundle, hn.1, hn.2, bot_compat,
      compat_self]

/-! ### Relative pronouns (57) -/

/-- A relative pronoun of (57): its case, the concord values its MOD admits of the head noun,
as disjuncts partial in number and gender, and the index features its form is marked for. -/
structure RelativePronoun where
  case : Case
  mod : List (Flat Number × Flat UD.Gender)
  index : Bundle

/-- A relative pronoun modifies a noun when the noun's concord fits one of its MOD disjuncts
and its marked index features are compatible with the noun's index: "all relative pronouns
agree with their head nouns in both CONCORD and INDEX, but not all pronouns are specified for
all features" (p. 821). -/
def Modifies (r : RelativePronoun) (n : Noun) : Prop :=
  (∃ m ∈ r.mod, Compat m.1 ↑n.concord.number ∧ Compat m.2 ↑n.concord.gender) ∧
    Compat r.index n.indexTarget

instance (r : RelativePronoun) (n : Noun) : Decidable (Modifies r n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- *koja*: nominative, its `-a` ending ambiguous between feminine singular and neuter
plural, hence the disjunctive MOD value (57). -/
def koja : RelativePronoun :=
  ⟨.nom, [(↑Number.singular, ↑UD.Gender.Fem), (↑Number.plural, ↑UD.Gender.Neut)], ⊥⟩

/-- *koju*: accusative feminine singular, unmarked for INDEX features (57). -/
def koju : RelativePronoun := ⟨.acc, [(↑Number.singular, ↑UD.Gender.Fem)], ⊥⟩

/-- *koje*: genitive feminine singular, unmarked for INDEX features (57). -/
def koje : RelativePronoun := ⟨.gen, [(↑Number.singular, ↑UD.Gender.Fem)], ⊥⟩

/-- *kojih*: the genitive plural INDEX form, unmarked for CONCORD (57). -/
def kojih : RelativePronoun := ⟨.gen, [(⊥, ⊥)], indexBundle ⊥ ↑Number.plural ⊥⟩

/-- All four relative pronouns modify *deca*, each through the features its form is marked
for ((54)–(56), (58)). -/
theorem relative_modifies_deca :
    Modifies koja deca ∧ Modifies koju deca ∧ Modifies koje deca ∧ Modifies kojih deca := by
  decide

-- p. 821
theorem kojih_not_modifies_knjiga : ¬ Modifies kojih knjiga ∧ Modifies koje knjiga := by
  decide

/-! ### The examples, paired -/

open Examples

/-- The route a target reads: concord at its case, or the index. -/
inductive Route
  | concord (case : Case)
  | index
  deriving DecidableEq, Repr

/-- A row paired with one glossed target: the example, the noun, the route and the number
and gender the target's form is marked for; the rows' pronouns and finite forms are all
third person. -/
structure RowTarget where
  ex : Datum
  noun : Noun
  route : Route
  number : Flat Number
  gender : Flat UD.Gender

/-- The target agrees with the noun through its route. -/
def RowTarget.Agrees (r : RowTarget) : Prop :=
  match r.route with
  | .concord c => ConcordAgrees (concordBundle c r.number r.gender) r.noun c
  | .index => IndexAgrees (indexBundle ↑Person.third r.number r.gender) r.noun

instance (r : RowTarget) : Decidable r.Agrees := by
  unfold RowTarget.Agrees; split <;> infer_instance

/-- The glossed targets of the acceptable examples, one entry per reader: determiners and
adjectives through concord at their case, pronouns, finite verbs and auxiliaries through the
index. Participles and coordinated predicates are not paired (§7.3). -/
def paired : List RowTarget :=
  [⟨ex_1, knjiga, .concord .nom, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_1, knjiga, .index, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_2, devojče, .index, ↑Number.singular, ↑UD.Gender.Neut⟩,
   ⟨ex_4, knjiga, .concord .nom, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_6, sudijaMale, .concord .nom, ↑Number.singular, ↑UD.Gender.Masc⟩,
   ⟨ex_6, sudijaMale, .index, ↑Number.singular, ↑UD.Gender.Masc⟩,
   ⟨ex_7, sudijaFemale, .concord .nom, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_7, sudijaFemale, .index, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_8, kit, .concord .nom, ↑Number.singular, ↑UD.Gender.Masc⟩,
   ⟨ex_9, kit, .index, ↑Number.singular, ↑UD.Gender.Masc⟩,
   ⟨ex_10, teladOne, .concord .nom, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_10, teladOne, .index, ↑Number.singular, ⊥⟩,
   ⟨ex_10, teladAggregate, .concord .nom, ↑Number.plural, ↑UD.Gender.Neut⟩,
   ⟨ex_10, teladAggregate, .index, ↑Number.plural, ⊥⟩,
   ⟨ex_11, teladAggregate, .index, ↑Number.plural, ⊥⟩,
   ⟨ex_12, steva, .concord .nom, ↑Number.singular, ↑UD.Gender.Masc⟩,
   ⟨ex_12, steva, .index, ↑Number.singular, ↑UD.Gender.Masc⟩,
   ⟨ex_13, mušterijaUnsexed, .concord .nom, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_13, mušterijaUnsexed, .index, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_14, mušterijaMale, .concord .nom, ↑Number.singular, ↑UD.Gender.Masc⟩,
   ⟨ex_14, mušterijaMale, .index, ↑Number.singular, ↑UD.Gender.Masc⟩,
   ⟨ex_15, sudijeAggregate, .concord .nom, ↑Number.plural, ↑UD.Gender.Fem⟩,
   ⟨ex_15, sudijeAggregate, .index, ↑Number.plural, ↑UD.Gender.Fem⟩,
   ⟨ex_16, naočare, .concord .nom, ↑Number.plural, ⊥⟩,
   ⟨ex_16, naočare, .index, ↑Number.plural, ⊥⟩,
   ⟨ex_17, braća, .index, ↑Number.plural, ↑UD.Gender.Neut⟩,
   ⟨ex_18, braća, .concord .acc, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_19, braća, .concord .inst, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_20, gospoda, .index, ↑Number.plural, ↑UD.Gender.Masc⟩,
   ⟨ex_21, deca, .concord .acc, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_21, deca, .index, ↑Number.plural, ↑UD.Gender.Neut⟩,
   ⟨ex_22, deca, .index, ↑Number.plural, ⊥⟩,
   ⟨ex_23, deca, .concord .nom, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_23, deca, .index, ↑Number.plural, ⊥⟩,
   ⟨ex_24, deca, .concord .nom, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_24, deca, .index, ↑Number.plural, ⊥⟩,
   ⟨ex_25, deca, .concord .inst, ↑Number.singular, ↑UD.Gender.Fem⟩,
   ⟨ex_29, deca, .index, ↑Number.plural, ⊥⟩,
   ⟨ex_32, deca, .index, ↑Number.plural, ⊥⟩,
   ⟨ex_33, deca, .index, ↑Number.plural, ⊥⟩]

/-- Each glossed target of an acceptable example agrees through its route. -/
theorem paired_agree : ∀ r ∈ paired, r.Agrees ∧ r.ex.judgment = .acceptable := by decide

/-- The starred alternants: the singular verb with distributive *telad* (23b), the neuter
plural pronoun with *gospoda* (40), the plural secondary predicate with *deca* (50), the
singular auxiliary under *koja* (54), and the singular resumptives of the *što*-relatives
(59), (62). -/
def starred : List RowTarget :=
  [⟨ex_11, teladAggregate, .index, ↑Number.singular, ⊥⟩,
   ⟨ex_20, gospoda, .index, ↑Number.plural, ↑UD.Gender.Neut⟩,
   ⟨ex_25, deca, .concord .inst, ↑Number.plural, ⊥⟩,
   ⟨ex_29, deca, .index, ↑Number.singular, ⊥⟩,
   ⟨ex_32, deca, .index, ↑Number.singular, ⊥⟩,
   ⟨ex_35, deca, .index, ↑Number.singular, ↑UD.Gender.Fem⟩]

/-- Each starred alternant fails to agree, and its row records the mark. -/
theorem starred_fail :
    ∀ r ∈ starred, ¬ r.Agrees ∧
      (r.ex.judgment = .unacceptable ∨ .unacceptable ∈ r.ex.alternatives.map Prod.snd) := by
  decide

-- (11b), §3.1
theorem pragmatic_devojče :
    ¬ IndexAgrees (indexBundle ↑Person.third ↑Number.singular ↑UD.Gender.Fem) devojče ∧
      ex_3.judgment = .acceptable := by
  decide

/-! ### The Agreement Hierarchy (63) -/

open _root_.Agreement

/-- Whether a position reads INDEX, given how the open predicate position resolves:
attributives lack indices, pronouns have them. -/
def readsIndex (predicate : Bool) : Position → Prop
  | .attributive => False
  | .predicate => predicate
  | .relativePronoun => True
  | .personalPronoun => True

instance (p : Bool) : DecidablePred (readsIndex p) := fun t ↦ by
  cases t <;> simp only [readsIndex] <;> infer_instance

theorem indexReaders_lowerSet (p : Bool) : IsLowerSet {t | readsIndex p t} := by
  intro t u hle hmem
  revert t u
  cases p <;> decide

end WechslerZlatic2000
