module

public import Linglib.Data.Examples.Charnavel2019
public import Linglib.Semantics.Reference.Logophoricity
public import Linglib.Syntax.Binding.Tree
public import Linglib.Data.Examples.Readers

/-!
# Charnavel (2019): Locality and Logophoricity: A Theory of Exempt Anaphora

Charnavel argues that no anaphor is exempt from Condition A: one without a pronounced local binder
is bound by a silent logophoric pronoun in the left periphery of its smallest spell-out domain,
which refers to the domain's logophoric center, an attitude holder or an empathy locus. Plain and
exempt anaphors [differ only in whether the binder is pronounced](##condition_overt). Here a
sentence is a tree with the indices the book prints and a silent pronoun whose index is that of a
logophoric center. An anaphor without a pronounced binder is [grammatical exactly when its
antecedent is such a center](##grammatical_iff_of_not_locallyBound), and [one with an inanimate
antecedent is plain](##locallyBound_overt_of_inanimate). The silent pronoun is no co-argument of a
pronoun and [never matters to Condition B](##condition_pronoun_iff). The predictions [match the
book's judgments](##acceptable_iff_grammatical), as [no exemption by position
can](##not_exists_forall_iff_tree); of the roles of Sells, the source and the pivot [each take in
the antecedent of an unacceptable anaphor](##exists_unacceptable_mem_centersOf_iff).

## Implementation notes

* A noun phrase with a subject is labelled `Det` and its subject is its first daughter; it is a
  spell-out domain for every position that subject c-commands, beside the clause `S` and the verb
  phrase `V`. Other noun phrases are `N`.
* The logophoric centers of a sentence are entered by index as the book's tests give them, the
  speaker being `0`. The tests themselves are not modelled.
* The silent pronouns of a representation share one index, so a sentence has one logophoric
  center at a time; each example has a single silent pronoun.
* The book leaves Condition B open and suggests that it holds over co-arguments. A pronoun's
  pronominal domain here holds the noun phrases of its smallest clause, verb phrase or noun phrase
  with a subject, which for a possessor is its own noun phrase, and leaves out the silent pronoun,
  which sits outside the complement of the logophoric operator; the trees do not draw that
  projection. With its binding domain instead, a pronoun would be [bound by the silent
  pronoun](##locallyBound_pronoun) in an example the book accepts.

## TODO

* Which bindings by a co-argument Condition B rules out: a strong pronoun escapes it under some
  predicates and not others, and the trees count every prepositional phrase in a verb phrase as
  an argument of the verb.
* Several silent pronouns in one representation, each referring to the center of its own domain,
  as in the shifts of perspective within a clause that the book builds its domains on.
* Plural and split antecedents, and with them exhaustive binding.
* The interpretation the logophoric operator imposes on its domain, read de se and from the
  center's own perspective.
* The long-distance anaphors of the last chapter, Icelandic *sig* and Mandarin *ziji* among them.

## References

* [charnavel-2019]
* [charnavel-sportiche-2016]
* [sells-1987]
-/

@[expose] public section

namespace Charnavel2019

open Core.Order PhraseStructure PhraseStructure.Tree Binding
open scoped Function

/-! ### Perspective centers -/

/-- The kinds of perspective center the book tells apart. -/
inductive Center where
  /-- The source of a report who holds no attitude toward its content. -/
  | nonAttitudinalSource
  /-- One whose thought or speech a clause reports, the speaker included. -/
  | attitudeHolder
  /-- One whose sensory or emotional experience the speaker takes up. -/
  | empathyLocus
  /-- A spatial point of reference, which need have no mental state. -/
  | deicticCenter
  deriving DecidableEq, Fintype, Repr

/-- A center is logophoric when its perspective is mental and first-personal, as an attitude
holder's and an empathy locus's are. -/
def Center.IsLogophoric (c : Center) : Prop := c = .attitudeHolder ∨ c = .empathyLocus

instance : DecidablePred Center.IsLogophoric := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The centers each role of Sells takes in, whole or in part, in the book's comparison of the two
taxonomies (Table 3.3). -/
def centersOf : LogophoricRole → Finset Center
  | .source => {.nonAttitudinalSource, .attitudeHolder}
  | .self => {.attitudeHolder, .empathyLocus}
  | .pivot => {.empathyLocus, .deicticCenter}

theorem exists_mem_centersOf_not_isLogophoric_iff {r : LogophoricRole} :
    (∃ c ∈ centersOf r, ¬ c.IsLogophoric) ↔ r ≠ .self := by
  cases r <;> decide

theorem isLogophoric_iff_exists_ne {c : Center} :
    c.IsLogophoric ↔ ∃ r r', r ≠ r' ∧ c ∈ centersOf r ∧ c ∈ centersOf r' := by
  cases c <;> decide

/-! ### Representations -/

/-- What stands at a noun phrase position. A pronounced item carries the index the book prints. -/
inductive Item where
  | anaphor (index : ℕ)
  | name (index : ℕ)
  | pronoun (index : ℕ)
  | trace (index : ℕ)
  /-- The silent logophoric pronoun, whose index is that of the logophoric center it refers to. -/
  | logophor
  deriving DecidableEq, Repr

namespace Item

/-- The index of an item when the silent pronoun bears the index `v`. -/
def index (v : ℕ) : Item → ℕ
  | anaphor i | name i | pronoun i | trace i => i
  | logophor => v

theorem index_congr {i : Item} (hi : i ≠ logophor) (v w : ℕ) : i.index v = i.index w := by
  cases i <;> simp_all [index]

/-- The binding class under which an item is checked. An anaphor falls under Condition A, a
pronoun under Condition B and a name under Condition C. -/
def class? : Item → Option BindingClass
  | anaphor _ => some .reflexive
  | name _ => some .rExpression
  | pronoun _ => some .pronoun
  | _ => none

end Item

/-- A representation is a tree whose noun phrases carry items. -/
abbrev Rep := Tree Cat (Option Item)

/-- A word that is no noun phrase. -/
abbrev w (c : Cat) : Rep := .terminal c none

/-- A one-word noun phrase. -/
abbrev dp (i : Item) : Rep := .terminal .N (some i)

/-- A noun phrase of a possessor, its subject, and a head noun. -/
abbrev poss (i : Item) : Rep := .node .Det [dp i, w .N]

/-- A prepositional phrase. -/
abbrev pp (x : Rep) : Rep := .node .P [w .P, x]

/-- A clause under its complementizer. -/
abbrev cp (x : Rep) : Rep := .node .C [w .C, x]

/-- The noun phrases of a representation, each with its position. -/
def nominals (t : Rep) : List (TreePath × Item) :=
  t.positionedTerminals.filterMap fun x ↦ x.2.2.map (x.1, ·)

/-- The type of noun phrases of a representation. -/
abbrev Nominal (t : Rep) : Type := {x // x ∈ nominals t}

/-- The pronounced noun phrases of a representation. -/
abbrev Overt (t : Rep) : Type := {x : Nominal t // x.1.2 ≠ .logophor}

variable {t : Rep} {v j : ℕ} {c : BindingClass}

/-- The subject of a noun phrase labelled `Det` is its first daughter. -/
def possessor (t : Rep) (m : TreePath) : Option TreePath :=
  if m ∈ labeled t {.Det} then some ⟨m.toList ++ [0]⟩ else none

/-- The spell-out domains that bound the domain of the position `b` are the clauses, the verb
phrases, and the noun phrases with a subject that c-commands `b`. -/
def spellout (t : Rep) (b : TreePath) : Set TreePath :=
  {m | m ∈ labeled t {.S, .V} ∨ m ∈ t.withAccessibleSubject (possessor t) (fun _ ↦ none) b}

instance (t : Rep) (b : TreePath) : DecidablePred (· ∈ spellout t b) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The clauses, the verb phrases and the noun phrases with a subject, which bound the
co-arguments of every position, a possessor's own noun phrase included. -/
def predicates (t : Rep) : Set TreePath := labeled t {.S, .V, .Det}

instance (t : Rep) : DecidablePred (· ∈ predicates t) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ labeled t _))

/-- The configuration on the noun phrases of `t` takes c-command. The binding domain of a position
is its smallest spell-out domain, and its pronominal domain holds its co-arguments, the noun
phrases of its smallest predicate other than the silent pronoun. -/
abbrev configuration (t : Rep) : Configuration (Nominal t) :=
  let s := (t.configuration (spellout t) fun _ ↦ predicates t).comap (·.1.1)
  { s with pronominalDomain := fun b ↦ {a ∈ s.pronominalDomain b | a.1.2 ≠ .logophor} }

/-- Two noun phrases are coindexed, the silent pronoun bearing `v`, when their items bear the same
index. -/
abbrev Coindexed (v : ℕ) (a b : Nominal t) : Prop := a.1.2.index v = b.1.2.index v

/-- A representation is licit, its silent pronoun bearing `v`, when coindexation meets Conditions A
and C on it with no anaphor exempt. -/
def Licit (t : Rep) (v : ℕ) : Prop := (configuration t).Satisfies (Coindexed v) ∅ (·.1.2.class?)

instance : Decidable (Licit t v) :=
  inferInstanceAs (Decidable ((configuration t).Satisfies (Coindexed v) ∅ _))

-- pp. 30, 32: a binder in the smallest spell-out domain is a binder in the clause.
theorem LocallyBound.clause {b : Nominal t} (h : (configuration t).LocallyBound (Coindexed v) b) :
    (t.clauseConfiguration.comap (·.1.1)).LocallyBound (Coindexed v) b :=
  let ⟨a, ha, hab⟩ := h
  ⟨a, upperPolar_anti _ (fun _ hm ↦ .inl (t.labeled_mono (by simp) hm)) ha, hab⟩

/-! ### The silent pronoun

Leaving the silent pronoun out of account turns Condition A on the whole representation into
Condition A on the pronounced noun phrases, with the anaphors the silent pronoun binds exempt. -/

/-- The configuration on the pronounced noun phrases alone. -/
abbrev overtConfiguration (t : Rep) : Configuration (Overt t) :=
  (configuration t).comap Subtype.val

/-- The pronounced noun phrases that the silent pronoun, bearing `v`, binds in their domain. Of
the anaphors, these are the ones that seem exempt. -/
abbrev silentlyBound (t : Rep) (v : ℕ) : Set (Overt t) :=
  (configuration t).covertlyBound (Coindexed v) Subtype.val

variable {b : Overt t}

theorem mem_silentlyBound_iff :
    b ∈ silentlyBound t v ↔ ∃ x ∈ (configuration t).domain b.1, x.1.2 = .logophor ∧
      (configuration t).Binds (Coindexed v) x b.1 := by
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ and_congr_left fun _ ↦ ?_
  simp [Overt]

theorem coindexed_onFun_val (v w : ℕ) :
    (Coindexed v on Subtype.val : Overt t → Overt t → Prop) =
      (Coindexed w on Subtype.val : Overt t → Overt t → Prop) := by
  ext a b
  rw [Function.onFun, Function.onFun, Coindexed, Coindexed, Item.index_congr a.2 v w,
    Item.index_congr b.2 v w]

/-- Condition A with the silent pronoun counted is Condition A among the pronounced noun phrases
with the silently bound anaphors exempt ((4), p. 217). -/
theorem condition_overt (hc : c.IsAnaphor) :
    (overtConfiguration t).Condition (Coindexed v on Subtype.val) (silentlyBound t v) b c ↔
      (configuration t).Condition (Coindexed v) ∅ b.1 c := by
  simpa using Configuration.condition_comap (E := ∅) Subtype.val_injective hc

-- p. 217
theorem eq_of_licit (ht : Licit t v) (hb : b.1.1.2 = .anaphor j)
    (hn : ¬ (overtConfiguration t).LocallyBound (Coindexed v on Subtype.val) b) : j = v := by
  obtain ⟨x, -, hx, hxb⟩ := mem_silentlyBound_iff.1 <|
    Configuration.mem_covertlyBound_of_condition Subtype.val_injective (.inl rfl)
      (ht b.1 .reflexive (by simp [hb, Item.class?])) hn
  simpa [Item.index, hx, hb] using hxb.2.1.symm

theorem condition_pronoun_overt {E : Set (Nominal t)} {F : Set (Overt t)} :
    (configuration t).Condition (Coindexed v) E b.1 .pronoun ↔
      (overtConfiguration t).Condition (Coindexed v on Subtype.val) F b .pronoun := by
  rw [← Configuration.condition_pronoun_comap Subtype.val_injective, and_iff_left]
  rintro ⟨x, hx, hxr, -⟩
  exact hxr ⟨⟨x, hx.2⟩, rfl⟩

/-- The silent pronoun is no co-argument of a pronoun, so whether a pronoun meets Condition B does
not depend on what the silent pronoun refers to (p. 230). -/
theorem condition_pronoun_iff (w : ℕ) {E : Set (Nominal t)} :
    (configuration t).Condition (Coindexed v) E b.1 .pronoun ↔
      (configuration t).Condition (Coindexed w) E b.1 .pronoun := by
  rw [condition_pronoun_overt (F := ∅), condition_pronoun_overt (F := ∅), coindexed_onFun_val v w]

/-! ### Sentences -/

/-- A sentence is a representation whose silent pronoun, if it has one, refers to a logophoric
center of its domain. -/
structure Sentence where
  /-- The representation, the index of its silent pronoun left open. -/
  tree : Rep
  /-- The indices of the logophoric centers of the silent pronoun's domain, which are the speaker,
  `0`, and those the book's tests make attitude holders or empathy loci, none of them inanimate. -/
  centers : Finset ℕ := {0}

/-- A sentence is grammatical when its representation is licit with the silent pronoun referring
to a logophoric center. -/
def Sentence.Grammatical (s : Sentence) : Prop := ∃ v ∈ s.centers, Licit s.tree v

instance (s : Sentence) : Decidable s.Grammatical :=
  inferInstanceAs (Decidable (∃ v ∈ s.centers, _))

/-- A sentence whose anaphor has no pronounced binder in its domain is grammatical exactly when its
antecedent is a logophoric center and the representation is licit with the silent pronoun
referring to that center (p. 217). -/
theorem grammatical_iff_of_not_locallyBound {s : Sentence} {b : Overt s.tree}
    (hb : b.1.1.2 = .anaphor j)
    (hn : ¬ (overtConfiguration s.tree).LocallyBound (Coindexed j on Subtype.val) b) :
    s.Grammatical ↔ j ∈ s.centers ∧ Licit s.tree j := by
  refine ⟨fun ⟨v, hv, ht⟩ ↦ ?_, fun h ↦ ⟨j, h⟩⟩
  obtain rfl := eq_of_licit ht hb (coindexed_onFun_val j v ▸ hn)
  exact ⟨hv, ht⟩

-- An anaphor whose antecedent is no logophoric center, as no inanimate antecedent is, is plain.
theorem locallyBound_overt_of_grammatical {s : Sentence} {b : Overt s.tree} (hs : s.Grammatical)
    (hb : b.1.1.2 = .anaphor j) (hj : j ∉ s.centers) :
    (overtConfiguration s.tree).LocallyBound (Coindexed j on Subtype.val) b :=
  not_not.1 fun hn ↦ hj ((grammatical_iff_of_not_locallyBound hb hn).1 hs).1

/-- *Cette auberge fait de l'ombre à son propre jardin.* The trace of the subject binds the
anaphor in the verb phrase. The inn is inanimate and so no center. -/
def innShade : Sentence where
  tree := .node .S [dp (.name 1),
    .node .V [dp (.trace 1), w .V, dp (.name 2), pp (poss (.anaphor 1))]]

/-- *Cette auberge bénéficie du fait que son propre jardin est plus spacieux.* The anaphor sits in
the subject of a tensed clause. -/
def innGarden : Sentence where
  tree := .node .S [dp (.name 1), .node .V [dp (.trace 1), w .V, pp (.node .N [w .N,
    cp (.node .S [dp .logophor, poss (.anaphor 1), .node .V [w .V, w .Adj]])])]]

/-- *Marie bénéficie du fait que son propre hôtel est plus spacieux.* The structure is that of the
inn sentence with an animate antecedent. The book runs no test on this sentence, and Marie is
entered as a center on the strength of the anaphor's being exempt. -/
def marieHotel : Sentence := { innGarden with centers := {0, 1} }

/-- *La Terre tourne sur elle-même.* -/
def earthSpins : Sentence where
  tree := .node .S [dp (.name 1), .node .V [dp (.trace 1), w .V, pp (dp (.anaphor 1))]]

/-- *La Terre tourne sur elle*, where the subject's trace, a co-argument of the pronoun, binds
it. -/
def earthSpinsPronoun : Sentence where
  tree := .node .S [dp (.name 1), .node .V [dp (.trace 1), w .V, pp (dp (.pronoun 1))]]

/-- *La Terre a bénéficié du fait que des photos d'elle-même ont montré les effets de la
pollution.* -/
def earthPhotos : Sentence where
  tree := .node .S [dp (.name 1), .node .V [dp (.trace 1), w .V, pp (.node .N [w .N,
    cp (.node .S [dp .logophor, .node .N [w .N, pp (dp (.anaphor 1))],
      .node .V [w .V, dp (.name 2)]])])]]

/-- *Robert dit que son rival a voté pour son propre projet.* Robert is the attitude holder of the
embedded clause. -/
def robertProject : Sentence where
  tree := .node .S [dp (.name 1), .node .V [w .V, cp (.node .S [dp (.name 2),
    .node .V [dp .logophor, w .V, pp (poss (.anaphor 1))]])]]
  centers := {0, 1}

/-- *Le courage de Paul a sauvé des flammes sa propre maison.* Paul is an empathy locus, and the
silent pronoun at the edge of the verb phrase does not c-command him. -/
def paulHouse : Sentence where
  tree := .node .S [.node .N [w .N, pp (dp (.name 1))],
    .node .V [dp .logophor, w .V, pp (dp (.name 2)), poss (.anaphor 1)]]
  centers := {0, 1}

/-- *Les commentaires des internautes sur elle-même ont atteint le moral de Lucie.* The subject
is a spell-out domain with its own silent pronoun, and Lucie, an empathy locus, lies outside
it. -/
def lucieMorale : Sentence where
  tree := .node .S [.node .Det [dp .logophor, w .N, pp (dp (.name 2)), pp (dp (.anaphor 1))],
    .node .V [w .V, .node .N [w .N, pp (dp (.name 1))]]]
  centers := {0, 1}

/-- *Les commentaires des internautes sur elle-même sur le blog de Lucie ont atteint son moral.*
Lucie now lies inside the domain of the silent pronoun. -/
def lucieBlog : Sentence where
  tree := .node .S [.node .Det [dp .logophor, w .N, pp (dp (.name 2)), pp (dp (.anaphor 1)),
      pp (.node .N [w .N, pp (dp (.name 1))])],
    .node .V [w .V, poss (.pronoun 1)]]
  centers := {0, 1}

/-- *Les commentaires des internautes sur elle(-même) et sa (propre) soeur ont atteint le moral de
Lucie*, with an anaphor and a pronoun in the domain of the silent pronoun. -/
def lucieSister (first second : ℕ → Item) : Sentence where
  tree := .node .S [.node .Det [dp .logophor, w .N, pp (dp (.name 2)),
      pp (.node .N [dp (first 1), w .Conj, poss (second 1)])],
    .node .V [w .V, .node .N [w .N, pp (dp (.name 1))]]]
  centers := {0, 1}

/-- *Irène tient de Paul qu'hier, plusieurs journaux ont parlé de lui-même.* Paul is the source
of the report and no attitude holder or empathy locus; Irène, `2`, can be the empathy locus. -/
def paulNewspapers : Sentence where
  tree := .node .S [dp (.name 2), .node .V [w .V, pp (dp (.name 1)), cp (.node .S [dp (.name 3),
    .node .V [dp .logophor, w .V, pp (dp (.anaphor 1))]])]]
  centers := {0, 2}

/-- *Le tableau à la gauche de l'épinette pourrait contenir une représentation d'elle-même.* The
virginal is a deictic center, and inanimate, so no logophoric center. -/
def virginal : Sentence where
  tree := .node .S [.node .N [w .N, pp (dp (.name 1))],
    .node .V [dp .logophor, w .V, .node .N [w .N, pp (dp (.anaphor 1))]]]

/-- *Le professeur de musique est placé à droite de sa propre élève.* The addressee, `2`, is the
empathy locus, and the trace of the subject binds the anaphor. -/
def teacherPlaced : Sentence where
  tree := .node .S [dp (.name 1),
    .node .V [dp .logophor, dp (.trace 1), w .V, pp (poss (.anaphor 1))]]
  centers := {0, 2}

/-- *Il semble qu'à la droite du professeur de musique, sa propre élève joue de l'épinette.* The
music teacher is a deictic center outside the tensed clause of the anaphor. -/
def teacherStudent : Sentence where
  tree := .node .S [w .Pron, .node .V [w .V, .node .C [w .C, pp (dp (.name 1)),
    .node .S [dp .logophor, poss (.anaphor 1), .node .V [w .V, dp (.name 3)]]]]]
  centers := {0, 2}

/-- *Julie pense que ma (propre) mère et sa (propre) mère devraient se parler*, with each
possessor an anaphor or a pronoun. Julie and the speaker are attitude holders. -/
def mothers (mine hers : ℕ → Item) : Sentence where
  tree := .node .S [dp (.name 1), .node .V [w .V, cp (.node .S [dp .logophor,
    .node .N [poss (mine 0), w .Conj, poss (hers 1)], .node .V [w .V]])]]
  centers := {0, 1}

/-- *Solange pense que Cyril est fier d'elle-même et de sa propre fille.* The silent pronoun
binds the first anaphor and the trace of Cyril the second. -/
def solangeCyril : Sentence where
  tree := .node .S [dp (.name 1), .node .V [w .V, cp (.node .S [dp (.name 2),
    .node .V [dp .logophor, dp (.trace 2), w .Adj, pp (dp (.anaphor 1)), w .Conj,
      pp (poss (.anaphor 2))]])]]
  centers := {0, 1}

/-- The examples, each with its sentence. -/
def sentences : List (Datum × Sentence) :=
  [(Examples.ex_2_2a, innShade), (Examples.ex_2_2b, innGarden), (Examples.ex_2_8b, marieHotel),
    (Examples.ex_2_3a, earthSpins), (Examples.ex_2_3b, earthPhotos),
    (Examples.ex_4_5, robertProject), (Examples.ex_4_12, paulHouse),
    (Examples.ex_4_14, lucieMorale), (Examples.ex_4_17, paulNewspapers),
    (Examples.ex_4_20, virginal), (Examples.ex_4_21a, teacherPlaced),
    (Examples.ex_4_21b, teacherStudent), (Examples.ex_4_25a, mothers .pronoun .anaphor),
    (Examples.ex_4_25, mothers .anaphor .anaphor), (Examples.ex_4_25b, mothers .anaphor .pronoun),
    (Examples.ex_4_27, solangeCyril), (Examples.ex_4_39a, lucieSister .anaphor .pronoun),
    (Examples.ex_4_39b, lucieSister .pronoun .anaphor), (Examples.ex_4_38, lucieBlog),
    (Examples.ex_4_43a, earthSpinsPronoun)]

theorem map_fst_sentences : sentences.map Prod.fst = Examples.all := rfl

/-- The kind of perspective center the paper's tests make the antecedent of an example. -/
def antecedent? (d : Datum) : Option Center :=
  d.parse? "antecedent"
    [("non-attitudinal source", .nonAttitudinalSource), ("attitude holder", .attitudeHolder),
      ("empathy locus", .empathyLocus), ("deictic center", .deicticCenter)]

/-- Each example is acceptable exactly when its sentence is grammatical. -/
theorem acceptable_iff_grammatical :
    ∀ p ∈ sentences, (p.1.judgment = .acceptable ↔ p.2.Grammatical) := by
  decide +kernel

-- (2b), (8b), p. 32
theorem not_exists_forall_iff_tree :
    ¬ ∃ P : Rep → Prop, ∀ p ∈ sentences, (p.1.judgment = .acceptable ↔ P p.2.tree) := by
  rintro ⟨P, h⟩
  have h₁ := h (Examples.ex_2_2b, innGarden) (by simp [sentences])
  have h₂ := h (Examples.ex_2_8b, marieHotel) (by simp [sentences])
  exact absurd (h₁.2 (h₂.1 rfl)) (by decide)

theorem locallyBound_pronoun :
    (configuration (lucieSister .pronoun .anaphor).tree).LocallyBound (Coindexed 1)
      ⟨(⟨[0, 3, 1, 0]⟩, .pronoun 1), by decide⟩ := by
  decide

theorem mem_centers_iff : ∀ p ∈ sentences,
    (∀ k ∈ antecedent? p.1, (1 ∈ p.2.centers ↔ k.IsLogophoric)) ∧
      (p.1.feature? "animacy" = some "inanimate" → 1 ∉ p.2.centers) := by
  decide

-- p. 32: inanimacy is a sufficient condition for plain anaphors.
theorem locallyBound_overt_of_inanimate : ∀ p ∈ sentences,
    p.1.feature? "animacy" = some "inanimate" → p.1.judgment = .acceptable →
      ∀ b : Overt p.2.tree, b.1.1.2 = .anaphor 1 →
        (overtConfiguration p.2.tree).LocallyBound (Coindexed 1 on Subtype.val) b :=
  fun p hp hi ha _ hb ↦ locallyBound_overt_of_grammatical
    ((acceptable_iff_grammatical p hp).1 ha) hb ((mem_centers_iff p hp).2 hi)

theorem licit_tree_antecedent :
    ∀ p ∈ sentences, (antecedent? p.1).isSome → Licit p.2.tree 1 := by
  decide +kernel

theorem exists_not_locallyBound_antecedent : ∀ p ∈ sentences, (antecedent? p.1).isSome →
    ∃ b : Overt p.2.tree, b.1.1.2 = .anaphor 1 ∧
      ¬ (overtConfiguration p.2.tree).LocallyBound (Coindexed 1 on Subtype.val) b := by
  decide +kernel

-- p. 179: where the tests classify the antecedent, the anaphor is acceptable exactly when the
-- antecedent is an attitude holder or an empathy locus.
theorem acceptable_iff_isLogophoric :
    ∀ p ∈ sentences, ∀ k ∈ antecedent? p.1, (p.1.judgment = .acceptable ↔ k.IsLogophoric) := by
  intro p hp k hk
  have hs : (antecedent? p.1).isSome := Option.isSome_of_mem hk
  obtain ⟨b, hb, hn⟩ := exists_not_locallyBound_antecedent p hp hs
  rw [acceptable_iff_grammatical p hp, grammatical_iff_of_not_locallyBound hb hn,
    ← (mem_centers_iff p hp).1 k hk]
  exact and_iff_left (licit_tree_antecedent p hp hs)

/-- The source and the pivot of Sells, and not the self, each take in the antecedent of an
unacceptable anaphor, a source that holds no attitude and a deictic center (Table 3.3). -/
theorem exists_unacceptable_mem_centersOf_iff {r : LogophoricRole} :
    (∃ d ∈ Examples.all, d.judgment ≠ .acceptable ∧ ∃ k ∈ antecedent? d, k ∈ centersOf r) ↔
      r ≠ .self := by
  cases r <;> decide

end Charnavel2019
