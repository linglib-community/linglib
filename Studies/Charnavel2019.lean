module

public import Linglib.Data.Examples.Charnavel2019
public import Linglib.Semantics.Reference.Logophoricity
public import Linglib.Syntax.Binding.Tree

/-!
# Charnavel (2019): Locality and Logophoricity: A Theory of Exempt Anaphora

Charnavel argues that no anaphor is exempt from Condition A. An anaphor that seems to lack a local
binder is bound by a silent logophoric pronoun at the edge of its spell-out domain, which refers
to the logophoric center of that domain, an attitude holder or an empathy locus. Plain and exempt
anaphors are then one element under one condition, and they differ in whether the binder is
pronounced. Here a sentence is a tree with the indices the book prints, the binding domain of a
position is its smallest spell-out domain, and a representation is licit when it meets Conditions
A and C with nothing exempt.

## Main statements

* `condition_overt`: Condition A with the silent pronouns counted is Condition A among the
  pronounced noun phrases with the anaphors the silent pronouns bind exempt.
* `locallyBound_overt_of_licit`, `index_eq_of_licit`: an anaphor that no silent pronoun is
  coindexed with, as an inanimate one, has a pronounced binder in its domain, and anaphors
  without pronounced binders in a domain with one silent pronoun corefer.
* `grammatical_iff`, `not_exists_forall_iff_rep`: the model gives the book's judgment on each
  example formalized here, and no condition on structure alone does, two of the examples having
  one structure and opposite judgments.
* `acceptable_iff_isLogophoric`, `exists_unacceptable_mem_centersOf_iff`: on the examples an
  anaphor without a pronounced binder is acceptable exactly when its antecedent is an attitude
  holder or an empathy locus, so the source and the pivot of Sells take in antecedents that
  exempt nothing and the self does not.

## Implementation notes

* A noun phrase with a subject is labelled `Det` and its subject is its first daughter; it is a
  spell-out domain for every position but that subject, beside the clause `S` and the verb phrase
  `V`. Other noun phrases are `N`.
* The logophoric centers of a sentence are entered by index as the book's tests give them, the
  speaker being `0`. The tests themselves are not modelled.
* Condition B is not checked. The book leaves it open and finds that the silent pronoun never
  triggers it, which a pronoun's having the domain of an anaphor would not allow
  (`condition_pronoun_overt`, `locallyBound_pronoun`).

## TODO

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
taxonomies. -/
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

/-- What stands at a noun phrase position, with its referential index. -/
inductive Item where
  | anaphor (index : ℕ)
  | name (index : ℕ)
  | pronoun (index : ℕ)
  | trace (index : ℕ)
  /-- The silent logophoric pronoun. -/
  | logophor (index : ℕ)
  deriving DecidableEq, Repr

namespace Item

/-- The referential index of an item. -/
def index : Item → ℕ
  | anaphor i | name i | pronoun i | trace i | logophor i => i

/-- The binding class under which an item is checked. An anaphor falls under Condition A and a
name under Condition C. -/
def class? : Item → Option BindingClass
  | anaphor _ => some .reflexive
  | name _ => some .rExpression
  | _ => none

/-- An item is silent when it is the logophoric pronoun. -/
def IsSilent : Item → Prop
  | logophor _ => True
  | _ => False

instance : DecidablePred IsSilent := fun i ↦ by cases i <;> unfold IsSilent <;> infer_instance

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
abbrev Overt (t : Rep) : Type := {x : Nominal t // ¬ x.1.2.IsSilent}

variable {t : Rep} {c : BindingClass}

/-- The spell-out domains that bound the domain of the position `b` are the clauses, the verb
phrases, and the noun phrases with a subject, their first daughter, other than `b`. -/
def spellout (t : Rep) (b : TreePath) : Set TreePath :=
  {m | m ∈ labeled t {.S, .V} ∨ m ∈ labeled t {.Det} ∧ ⟨m.toList ++ [0]⟩ ≠ b}

instance (t : Rep) (b : TreePath) : DecidablePred (· ∈ spellout t b) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∧ _))

/-- The configuration on the noun phrases of `t` takes c-command and the smallest spell-out
domain. -/
abbrev configuration (t : Rep) : Configuration (Nominal t) :=
  (t.configuration (spellout t)).comap (·.1.1)

/-- Two noun phrases are coindexed when their items bear the same index. -/
abbrev Coindexed (a b : Nominal t) : Prop := a.1.2.index = b.1.2.index

/-- A representation is licit when coindexation meets Conditions A and C on it with no anaphor
exempt. -/
def Licit (t : Rep) : Prop := (configuration t).Satisfies Coindexed ∅ (·.1.2.class?)

instance : Decidable (Licit t) :=
  inferInstanceAs (Decidable ((configuration t).Satisfies Coindexed ∅ _))

/-! ### The silent pronoun and the three conditions

Leaving the silent pronouns out of account turns each condition on the whole representation into
a condition on the pronounced noun phrases. For Condition A their bindees become exempt. -/

/-- The configuration on the pronounced noun phrases alone. -/
abbrev overtConfiguration (t : Rep) : Configuration (Overt t) :=
  (configuration t).comap Subtype.val

/-- The pronounced noun phrases that a silent pronoun binds in their domain. Of the anaphors,
these are the ones that seem exempt. -/
abbrev silentlyBound (t : Rep) : Set (Overt t) :=
  (configuration t).covertlyBound Coindexed Subtype.val

variable {b : Overt t}

theorem mem_silentlyBound_iff :
    b ∈ silentlyBound t ↔ ∃ x ∈ (configuration t).domain b.1, x.1.2.IsSilent ∧
      (configuration t).Binds Coindexed x b.1 := by
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ and_congr_left fun _ ↦ ?_
  simp [Overt]

theorem condition_overt (hc : c.IsAnaphor) :
    (overtConfiguration t).Condition (Coindexed on Subtype.val) (silentlyBound t) b c ↔
      (configuration t).Condition Coindexed ∅ b.1 c := by
  simpa using Configuration.condition_comap (E := ∅) Subtype.val_injective hc

theorem condition_rExpression_overt :
    ((overtConfiguration t).Condition (Coindexed on Subtype.val) ∅ b .rExpression ∧
      ¬ ∃ x : Nominal t, x.1.2.IsSilent ∧ (configuration t).Binds Coindexed x b.1) ↔
      (configuration t).Condition Coindexed ∅ b.1 .rExpression := by
  rw [← Configuration.condition_rExpression_comap (E := ∅) (F := ∅) Subtype.val_injective]
  refine and_congr_right fun _ ↦ not_congr (exists_congr fun x ↦ and_congr_left fun _ ↦ ?_)
  simp

theorem condition_pronoun_overt :
    ((overtConfiguration t).Condition (Coindexed on Subtype.val) ∅ b .pronoun ∧
      b ∉ silentlyBound t) ↔ (configuration t).Condition Coindexed ∅ b.1 .pronoun :=
  Configuration.condition_pronoun_comap Subtype.val_injective

theorem locallyBound_overt_of_licit (ht : Licit t) (hb : b.1.1.2.class? = some .reflexive)
    (h : ∀ x : Nominal t, x.1.2.IsSilent → ¬ Coindexed x b.1) :
    (overtConfiguration t).LocallyBound (Coindexed on Subtype.val) b := by
  refine ((condition_overt (.inl rfl)).2 (ht b.1 .reflexive hb)).resolve_left fun hE ↦ ?_
  obtain ⟨x, -, hx, hbind⟩ := mem_silentlyBound_iff.1 hE
  exact h x hx hbind.2.1

theorem index_eq_of_licit (ht : Licit t) {a b : Overt t}
    (ha : a.1.1.2.class? = some .reflexive) (hb : b.1.1.2.class? = some .reflexive)
    (hna : ¬ (overtConfiguration t).LocallyBound (Coindexed on Subtype.val) a)
    (hnb : ¬ (overtConfiguration t).LocallyBound (Coindexed on Subtype.val) b)
    (h : ∀ x ∈ (configuration t).domain a.1, ∀ y ∈ (configuration t).domain b.1,
      x.1.2.IsSilent → y.1.2.IsSilent → x = y) : a.1.1.2.index = b.1.1.2.index := by
  have hcov {x : Overt t} (hx : x.1.1.2.class? = some .reflexive)
      (hn : ¬ (overtConfiguration t).LocallyBound (Coindexed on Subtype.val) x) :
      x ∈ silentlyBound t :=
    Configuration.mem_covertlyBound_of_condition Subtype.val_injective (.inl rfl) (ht x.1 _ hx) hn
  exact Configuration.rel_of_mem_covertlyBound (L := Coindexed) (fun _ _ h ↦ h.symm)
    (fun _ _ _ h h' ↦ h.trans h')
    (fun x hx y hy hxr hyr ↦ h x hx y hy (by simpa [Overt] using hxr) (by simpa [Overt] using hyr))
    (hcov ha hna) (hcov hb hnb)

theorem condition_clause_of_condition {b : Nominal t} (hc : c.IsAnaphor)
    (h : (configuration t).Condition Coindexed ∅ b c) :
    (t.clauseConfiguration.comap (·.1.1)).Condition Coindexed ∅ b c :=
  Configuration.condition_mono hc (Configuration.comap_mono _ <| t.configuration_anti
    fun _ _ hm ↦ .inl (t.labeled_mono (by simp) hm)) h

/-! ### Sentences -/

/-- A sentence is given by its representation for each value of its silent pronoun and by the
logophoric centers the pronoun can refer to. -/
structure Sentence where
  /-- The representation in which the silent pronoun bears a given index. -/
  rep : ℕ → Rep
  /-- The indices of the logophoric centers of the pronoun's domain, which are the speaker, `0`,
  and those the book's tests make attitude holders or empathy loci, none of them inanimate. -/
  centers : Finset ℕ

/-- A sentence is grammatical when its representation is licit with the silent pronoun referring
to a logophoric center. -/
def Sentence.Grammatical (s : Sentence) : Prop := ∃ i ∈ s.centers, Licit (s.rep i)

instance (s : Sentence) : Decidable s.Grammatical :=
  inferInstanceAs (Decidable (∃ i ∈ s.centers, _))

/-- *Cette auberge fait de l'ombre à son propre jardin.* The trace of the subject binds the
anaphor in the verb phrase. The inn is inanimate and so no center. -/
def innShade : Sentence where
  rep _ := .node .S [dp (.name 1),
    .node .V [dp (.trace 1), w .V, dp (.name 2), pp (poss (.anaphor 1))]]
  centers := {0}

/-- *Cette auberge bénéficie du fait que son propre jardin est plus spacieux.* The anaphor sits in
the subject of a tensed clause. -/
def innGarden : Sentence where
  rep i := .node .S [dp (.name 1), .node .V [dp (.trace 1), w .V, pp (.node .N [w .N,
    cp (.node .S [dp (.logophor i), poss (.anaphor 1), .node .V [w .V, w .Adj]])])]]
  centers := {0}

/-- *Marie bénéficie du fait que son propre hôtel est plus spacieux.* The structure is that of the
inn sentence with an animate antecedent. The book runs no test on this sentence, and Marie is
entered as a center on the strength of the anaphor's being exempt. -/
def marieHotel : Sentence := { innGarden with centers := {0, 1} }

/-- *La Terre tourne sur elle-même.* -/
def earthSpins : Sentence where
  rep _ := .node .S [dp (.name 1), .node .V [dp (.trace 1), w .V, pp (dp (.anaphor 1))]]
  centers := {0}

/-- *La Terre a bénéficié du fait que des photos d'elle-même ont montré les effets de la
pollution.* -/
def earthPhotos : Sentence where
  rep i := .node .S [dp (.name 1), .node .V [dp (.trace 1), w .V, pp (.node .N [w .N,
    cp (.node .S [dp (.logophor i), .node .N [w .N, pp (dp (.anaphor 1))],
      .node .V [w .V, dp (.name 2)]])])]]
  centers := {0}

/-- *Robert dit que son rival a voté pour son propre projet.* Robert is the attitude holder of the
embedded clause. -/
def robertProject : Sentence where
  rep i := .node .S [dp (.name 1), .node .V [w .V, cp (.node .S [dp (.name 2),
    .node .V [dp (.logophor i), w .V, pp (poss (.anaphor 1))]])]]
  centers := {0, 1}

/-- *Le courage de Paul a sauvé des flammes sa propre maison.* Paul is an empathy locus, and the
silent pronoun at the edge of the verb phrase does not c-command him. -/
def paulHouse : Sentence where
  rep i := .node .S [.node .N [w .N, pp (dp (.name 1))],
    .node .V [dp (.logophor i), w .V, pp (dp (.name 2)), poss (.anaphor 1)]]
  centers := {0, 1}

/-- *Les commentaires des internautes sur elle-même ont atteint le moral de Lucie.* The subject
is a spell-out domain with its own silent pronoun, and Lucie, an empathy locus, lies outside
it. -/
def lucieMorale : Sentence where
  rep i := .node .S [.node .Det [dp (.logophor i), w .N, pp (dp (.name 2)), pp (dp (.anaphor 1))],
    .node .V [w .V, .node .N [w .N, pp (dp (.name 1))]]]
  centers := {0, 1}

/-- *Les commentaires des internautes sur elle-même sur le blog de Lucie ont atteint son moral.*
Lucie now lies inside the domain of the silent pronoun. -/
def lucieBlog : Sentence where
  rep i := .node .S [.node .Det [dp (.logophor i), w .N, pp (dp (.name 2)), pp (dp (.anaphor 1)),
      pp (.node .N [w .N, pp (dp (.name 1))])],
    .node .V [w .V, poss (.pronoun 1)]]
  centers := {0, 1}

/-- *Les commentaires des internautes sur elle(-même) et sa (propre) soeur ont atteint le moral de
Lucie*, with an anaphor and a pronoun in the domain of the silent pronoun. -/
def lucieSister (first second : ℕ → Item) : Sentence where
  rep i := .node .S [.node .Det [dp (.logophor i), w .N, pp (dp (.name 2)),
      pp (.node .N [dp (first 1), w .Conj, poss (second 1)])],
    .node .V [w .V, .node .N [w .N, pp (dp (.name 1))]]]
  centers := {0, 1}

/-- *Irène tient de Paul qu'hier, plusieurs journaux ont parlé de lui-même.* Paul is the source
of the report and no attitude holder or empathy locus; Irène, `2`, can be the empathy locus. -/
def paulNewspapers : Sentence where
  rep i := .node .S [dp (.name 2), .node .V [w .V, pp (dp (.name 1)), cp (.node .S [dp (.name 3),
    .node .V [dp (.logophor i), w .V, pp (dp (.anaphor 1))]])]]
  centers := {0, 2}

/-- *Le tableau à la gauche de l'épinette pourrait contenir une représentation d'elle-même.* The
virginal is a deictic center, and inanimate, so no logophoric center. -/
def virginal : Sentence where
  rep i := .node .S [.node .N [w .N, pp (dp (.name 1))],
    .node .V [dp (.logophor i), w .V, .node .N [w .N, pp (dp (.anaphor 1))]]]
  centers := {0}

/-- *Le professeur de musique est placé à droite de sa propre élève.* The addressee, `2`, is the
empathy locus, and the trace of the subject binds the anaphor. -/
def teacherPlaced : Sentence where
  rep i := .node .S [dp (.name 1),
    .node .V [dp (.logophor i), dp (.trace 1), w .V, pp (poss (.anaphor 1))]]
  centers := {0, 2}

/-- *Il semble qu'à la droite du professeur de musique, sa propre élève joue de l'épinette.* The
music teacher is a deictic center outside the tensed clause of the anaphor. -/
def teacherStudent : Sentence where
  rep i := .node .S [w .Pron, .node .V [w .V, .node .C [w .C, pp (dp (.name 1)),
    .node .S [dp (.logophor i), poss (.anaphor 1), .node .V [w .V, dp (.name 3)]]]]]
  centers := {0, 2}

/-- *Julie pense que ma (propre) mère et sa (propre) mère devraient se parler*, with each
possessor an anaphor or a pronoun. Julie and the speaker are attitude holders. -/
def mothers (mine hers : ℕ → Item) : Sentence where
  rep i := .node .S [dp (.name 1), .node .V [w .V, cp (.node .S [dp (.logophor i),
    .node .N [poss (mine 0), w .Conj, poss (hers 1)], .node .V [w .V]])]]
  centers := {0, 1}

/-- *Solange pense que Cyril est fier d'elle-même et de sa propre fille.* The silent pronoun
binds the first anaphor and the trace of Cyril the second. -/
def solangeCyril : Sentence where
  rep i := .node .S [dp (.name 1), .node .V [w .V, cp (.node .S [dp (.name 2),
    .node .V [dp (.logophor i), dp (.trace 2), w .Adj, pp (dp (.anaphor 1)), w .Conj,
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
    (Examples.ex_4_39b, lucieSister .pronoun .anaphor), (Examples.ex_4_38, lucieBlog)]

theorem map_fst_sentences : sentences.map Prod.fst = Examples.all := rfl

/-- The kind of perspective center the paper's tests make the antecedent of an example. -/
def antecedent? (d : Datum) : Option Center :=
  d.parse? "antecedent"
    [("non-attitudinal source", .nonAttitudinalSource), ("attitude holder", .attitudeHolder),
      ("empathy locus", .empathyLocus), ("deictic center", .deicticCenter)]

theorem grammatical_iff : ∀ p ∈ sentences, (p.1.judgment = .acceptable ↔ p.2.Grammatical) := by
  decide +kernel

theorem not_exists_forall_iff_rep :
    ¬ ∃ P : (ℕ → Rep) → Prop, ∀ p ∈ sentences, (p.1.judgment = .acceptable ↔ P p.2.rep) := by
  rintro ⟨P, h⟩
  have h₁ := h (Examples.ex_2_2b, innGarden) (by simp [sentences])
  have h₂ := h (Examples.ex_2_8b, marieHotel) (by simp [sentences])
  exact absurd (h₁.2 (h₂.1 rfl)) (by decide)

theorem locallyBound_pronoun :
    (configuration ((lucieSister .pronoun .anaphor).rep 1)).LocallyBound Coindexed
      ⟨(⟨[0, 3, 1, 0]⟩, .pronoun 1), by decide⟩ := by
  decide

theorem mem_centers_iff : ∀ p ∈ sentences,
    (∀ k ∈ antecedent? p.1, (1 ∈ p.2.centers ↔ k.IsLogophoric)) ∧
      (p.1.feature? "animacy" = some "inanimate" → 1 ∉ p.2.centers) := by
  decide

theorem licit_rep_antecedent :
    ∀ p ∈ sentences, (antecedent? p.1).isSome → Licit (p.2.rep 1) := by
  decide +kernel

theorem acceptable_iff_isLogophoric :
    ∀ d ∈ Examples.all, ∀ k ∈ antecedent? d, (d.judgment = .acceptable ↔ k.IsLogophoric) := by
  decide

theorem exists_unacceptable_mem_centersOf_iff {r : LogophoricRole} :
    (∃ d ∈ Examples.all, d.judgment ≠ .acceptable ∧ ∃ k ∈ antecedent? d, k ∈ centersOf r) ↔
      r ≠ .self := by
  cases r <;> decide

end Charnavel2019
