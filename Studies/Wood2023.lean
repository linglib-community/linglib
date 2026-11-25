module

public import Linglib.Morphology.DistributedMorphology.Nominalization
public import Linglib.Semantics.Composition.Rules
public import Linglib.Morphology.DistributedMorphology.Locality
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.InsideOut
public import Linglib.Languages.Icelandic.Nouns
public import Linglib.Data.Examples.Wood2023
public import Linglib.Data.Examples.Readers
public import Linglib.Morphology.Morph
public import Linglib.Morphology.Word.Features
public import Linglib.Morphology.Exponence.Basic

/-!
# Wood (2023): Icelandic Nominalizations and Allosemy

This file formalizes Wood's account of Icelandic deverbal nominalizations as complex
heads: a root categorized by v and then by n, with no verb phrase and no Voice, whose
ambiguity between complex event, simple event, and referring readings is allosemy of v and n
(`Derivation`). A complex event nominal has eventive v and zero n, so the noun inherits the
verb's meaning; the simple readings have zero v and a contentful n. Borer's Generalization,
that a complex event reading entails a morphologically related verb with that meaning, follows
from two facts: only v introduces the event variable, and n is not in the root's domain, so it
cannot condition root suppletion past v (`borers_generalization`). The nominal's external
argument is introduced by i*, the head that is Voice in the verbal domain, interpreted as an
agent in the context of an eventive nP and as a possessor otherwise (`IStar.alloseme`).

The form side is contextual allomorphy on the same complex head. The nominalizers *-un*,
*-ing*, *-sla*, *-stur* and the rest are exponents of one n, each listed for a set of roots or
for an overt verbalizer, with no elsewhere item (`Allomorphy.vocab`); Vocabulary Insertion runs
from the inside out over the concatenated neighbors, null exponents pruned
(`ComplexHead.insertAll`). Two of the book's descriptive generalizations are then theorems: the
nominalizer is chosen by the verbalizer whenever that is overt, since it hides the root, and by
the root otherwise (`Allomorphy.nominalizer_of_ne_zero`, `Allomorphy.nominalizer_of_eq_zero`),
so that *-k* takes *-un* and *-er* takes *-ing* whatever the root; and a root that no item
lists has no nominalization at all, the book's *borða* 'eat' (`Allomorphy.nominalizer_eq_none`).
Every segmentation in `Languages.Icelandic.Nouns` is derived this way
(`Allomorphy.fragment_realize`).

Special meaning is subject to phase locality: a dependency may cross at most one categorizer
(`Local`). A preposition heading the PP complement of a nominal is separated from the root by
v and n, so a preposition that conditions the root's meaning must adjoin to the complex n head
as a prefix, while one with its own meaning heads a PP, and one that does both is doubled
(`nominal_complement_not_local`). The same bound lets n condition an idiosyncratic root meaning
across v (`nominal_n_local`) and forbids it in *-væðing* nominals, where *-væða* is a compound
head attaching to a categorized word, so that two categorizers separate the root from the
outer n (`vaeda_n_not_local`). The prefixes *marg-* and *endur-* are event modifiers: *marg-*
adjoins to v and takes a predicate of eventualities, so it composes exactly on eventive v under
the zero and result allosemes of n (`margComposes_iff`), and *endur-*, which adjoins to v or to
n, is licensed also on simple event nominals (`Licensed`); the book's judgments on the prefixed
readings of *þvottur* and *prentun* are the rows of `Data.Examples.Wood2023`, checked one by one
(`rows_licensed`). Allosemy is contextual as allomorphy is: *aðdáun* and *viðvörun* share the
nominalizer *-un*, and only the second has a concrete entity reading
(`reading_not_by_nominalizer`).

## Implementation notes

*marg-* is licensed where the complex head with the prefix composes. That includes a result noun
built on eventive v, on which the book prints no judgment. *endur-* is licensed by a stated
condition: a simple event noun and a simple entity noun have the same type, so composition does
not tell them apart.

The exponents of the roots and affixes are the surface morphs of the language file, so the u-umlaut
of *söfn-un* and *vönt-un* is not undone and the theme vowel *-a* of the verb is absent, as
the book's own segmentation has it. The roots are identified by their forms. The prefixed
preposition of *við-ger-ð* adjoins to n and is not inserted by the vocabulary; the derivation
covers the root, v, and n. Wood's bound for allosemy, one intervening categorizer, is one
phase looser than `ComplexHead.Active` of the root, the bound the book keeps for root suppletion;
the study states the strict one through the substrate. A preposition adjoined to a complex head
has no spine position, since a head does not c-command its own adjunct, so the heads between a
preposition and the root are read off its attachment.

## References

* [wood-2023]
* [embick-2010]
* [embick-2015]
* [marantz-2013]
* [wood-marantz-2017]
* [myler-2016]
-/

@[expose] public section

namespace Wood2023

open DistributedMorphology DistributedMorphology.Allosemy Icelandic.Nouns
open Morphology hiding Feature
open Wood2023.Examples

/-! ### Vocabulary Insertion at v and n -/

namespace Allomorphy

/-- A Vocabulary Item of v or n may mention the category of its own head, or the exponent of a
concatenated neighbor, a root or an affix. -/
inductive Feature
  | cat (c : Minimalist.Cat)
  | exp (m : Morph)
  deriving DecidableEq, Repr

open Feature

/-- The zero exponent. -/
def zero : Morph := .suff ""

/-- A realized exponent presents itself as context. -/
def expFeatures (m : Morph) : Finset Feature := {exp m}

/-- The item spelling out n as `e` after the exponent `m`. -/
def nAfter (m : Morph) (e : String) : VocabularyItem Feature Morph :=
  ⟨{(0, (cat .n : Feature)), (-1, exp m)}, .suff e⟩

/-- The Vocabulary Items of v and n. v is *-k* after *sein* and, in a nominal only, after
*not*, *-er* after *analýs*, and zero elsewhere; n is *-ing* after *-er*, *-un* after *-k*
and after the roots the language file shows with *-un*, *-n*, *-ttur* and *-ð* after their roots,
and has no elsewhere item, as the rule (2.8) of the book has it. -/
def vocab : RuleSet (VocabularyItem Feature Morph) :=
  [⟨{(0, (cat .v : Feature)), (-1, exp (.root "sein"))}, .suff "k"⟩,
   ⟨{(0, (cat .v : Feature)), (-1, exp (.root "not")), (1, (cat .n : Feature))}, .suff "k"⟩,
   ⟨{(0, (cat .v : Feature)), (-1, exp (.root "analýs"))}, .suff "er"⟩,
   {(cat .v : Feature)} ⟷ zero,
   nAfter (.suff "er") "ing", nAfter (.suff "k") "un",
   nAfter (.root "opn") "un", nAfter (.root "söfn") "un", nAfter (.root "vönt") "un",
   nAfter (.root "prent") "un", nAfter (.root "vör") "un", nAfter (.root "dá") "un",
   nAfter (.root "önn") "un",
   nAfter (.root "misheyr") "n", nAfter (.root "þvo") "ttur", nAfter (.root "ger") "ð"]

/-- The roots the items of n list. -/
def listed : List String :=
  ["opn", "söfn", "vönt", "prent", "vör", "dá", "önn", "misheyr", "þvo", "ger"]

variable (r : String) (e : Morph)

/-- The root categorized by v and then by n, with the exponent of v if already inserted. -/
def word (v : Option Morph) : ComplexHead (Morpheme Feature Morph) (Morpheme Feature Morph) :=
  ⟨⟨∅, some (.root r), .after⟩,
    [⟨{(cat .v : Feature)}, v, .after⟩, ⟨{(cat .n : Feature)}, none, .after⟩]⟩

/-- Vocabulary Insertion at head `i`, over the concatenated neighbors with zero exponents
pruned. -/
abbrev insertAt (w : ComplexHead (Morpheme Feature Morph) (Morpheme Feature Morph)) (i : ℕ) :
    ComplexHead (Morpheme Feature Morph) (Morpheme Feature Morph) :=
  w.insertAt (· = zero) vocab .concatenation expFeatures .nondeletion i

/-- The morphs of a complex head after insertion from the inside out. -/
def realize (w : ComplexHead (Morpheme Feature Morph) (Morpheme Feature Morph)) : List Morph :=
  (w.insertAll (· = zero) vocab .concatenation expFeatures .nondeletion).exponents.filter
    (· ≠ zero)

theorem fragment_realize :
    ∀ w ∈ Icelandic.Nouns.deverbals,
      (w.preposition.map Morph.pref).toList ++ realize (word w.root none) = w.morphs := by
  decide

private theorem root_ne_zero : Morph.root r ≠ zero := by
  simp [zero, Morph.root, Morph.suff]

/-- In the context v presents, the root is inside and the bare n outside. -/
def vContext : Neighborhood (Finset Feature) :=
  ⟨{(cat .v : Feature)}, [{exp (.root r)}], [{(cat .n : Feature)}]⟩

/-- In the context n presents after the exponent `e` of v, the inner neighbor is v when it is
overt, and the root past a pruned zero v. -/
def nContext : Neighborhood (Finset Feature) :=
  if e = zero then ⟨{(cat .n : Feature)}, [{exp (.root r)}], []⟩
  else ⟨{(cat .n : Feature)}, [{(cat .v : Feature), exp e}], []⟩

theorem contextAt_word_zero :
    (word r none).contextAt (· = zero) .concatenation expFeatures 0 = vContext r := by
  have hi : List.idxOf? (some 0) [none, some 0, some 1] = some 1 := by decide
  simp [hi, vContext, word, ComplexHead.contextAt, ComplexHead.neighbors, ComplexHead.concat,
    ComplexHead.order_eq, ComplexHead.at?, ComplexHead.Pruned, ComplexHead.visible, expFeatures,
    List.range_succ, root_ne_zero]

theorem contextAt_word_one :
    (word r (some e)).contextAt (· = zero) .concatenation expFeatures 1 = nContext r e := by
  by_cases he : e = zero
  · have hi : List.idxOf? (some 1) [none, some 1] = some 1 := by decide
    simp [hi, he, nContext, word, ComplexHead.contextAt, ComplexHead.neighbors,
      ComplexHead.concat, ComplexHead.order_eq, ComplexHead.at?, ComplexHead.Pruned,
      ComplexHead.visible, expFeatures, List.range_succ, root_ne_zero]
  · have hi : List.idxOf? (some 1) [none, some 0, some 1] = some 2 := by decide
    simp [hi, he, nContext, word, ComplexHead.contextAt, ComplexHead.neighbors,
      ComplexHead.concat, ComplexHead.order_eq, ComplexHead.at?, ComplexHead.Pruned,
      ComplexHead.visible, expFeatures, List.range_succ, root_ne_zero]

theorem insertAt_word_zero :
    insertAt (word r none) 0 = word r (subsetPrinciple vocab (vContext r)) := by
  unfold insertAt ComplexHead.insertAt
  rw [contextAt_word_zero]
  cases h : winner? vocab (vContext r) <;>
    simp [h, word, subsetPrinciple_eq_map_winner?, Morpheme.IsRealized]

theorem insertAt_word_one :
    (insertAt (word r (some e)) 1).heads[1]? >>= (·.exp) =
      subsetPrinciple vocab (nContext r e) := by
  unfold insertAt ComplexHead.insertAt
  rw [contextAt_word_one]
  cases h : winner? vocab (nContext r e) <;>
    simp [h, word, subsetPrinciple_eq_map_winner?, Morpheme.IsRealized]

theorem subsetPrinciple_vContext_isSome : (subsetPrinciple vocab (vContext r)).isSome := by
  rw [subsetPrinciple_eq_map_winner?, Option.isSome_map, winner?_isSome_iff]
  exact ⟨{Feature.cat .v} ⟷ zero, by decide, by simp [vContext]⟩

/-- The exponent of v in the nominal of the root `r`. -/
def verbalizer : Morph := (subsetPrinciple vocab (vContext r)).getD zero

/-- The exponent of n in the nominal of the root `r`, if it has one. -/
def nominalizer : Option Morph :=
  ((word r none).insertAll (· = zero) vocab .concatenation expFeatures .nondeletion).heads[1]? >>=
    (·.exp)

theorem nominalizer_eq : nominalizer r = subsetPrinciple vocab (nContext r (verbalizer r)) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (subsetPrinciple_vContext_isSome r)
  unfold nominalizer
  rw [ComplexHead.insertAll, show (word r none).heads.length = 2 from rfl,
    ComplexHead.insertUpTo_succ, ComplexHead.insertUpTo_succ, ComplexHead.insertUpTo_zero]
  change (insertAt (insertAt (word r none) 0) 1).heads[1]? >>= _ = _
  rw [insertAt_word_zero, he, insertAt_word_one, verbalizer, he, Option.getD_some]

theorem nominalizer_of_ne_zero (h : verbalizer r ≠ zero) :
    nominalizer r = subsetPrinciple vocab
      ⟨{(cat .n : Feature)}, [{(cat .v : Feature), exp (verbalizer r)}], []⟩ := by
  simp [nominalizer_eq, nContext, h]

theorem nominalizer_of_eq_zero (h : verbalizer r = zero) :
    nominalizer r = subsetPrinciple vocab ⟨{(cat .n : Feature)}, [{exp (.root r)}], []⟩ := by
  simp [nominalizer_eq, nContext, h]

theorem nominalizer_of_k (h : verbalizer r = .suff "k") : nominalizer r = some (.suff "un") := by
  rw [nominalizer_of_ne_zero r (h ▸ by decide), h]; decide

theorem nominalizer_of_er (h : verbalizer r = .suff "er") :
    nominalizer r = some (.suff "ing") := by
  rw [nominalizer_of_ne_zero r (h ▸ by decide), h]; decide

theorem nominalizer_eq_none (h : verbalizer r = zero) (hr : r ∉ listed) :
    nominalizer r = none := by
  rw [nominalizer_of_eq_zero r h, subsetPrinciple, RuleSet.realize_eq_none_iff]
  simp [listed] at hr
  simp [RuleSet.applicable, vocab, nAfter, VocabularyItem.applies_iff, Neighborhood.mem_def,
    Morph.root, Morph.suff, zero, or_and_right, exists_or]
  simpa [eq_comm] using hr

theorem borda : nominalizer "borð" = none := nominalizer_eq_none _ (by decide) (by decide)

end Allomorphy

/-! ### The complex head and its readings -/

/-- Every head of the complex head is a categorizer, hence a phase head. -/
def Categorizer.Cyclic : Categorizer → Prop := fun _ ↦ True

instance : DecidablePred Categorizer.Cyclic := fun _ ↦ inferInstanceAs (Decidable True)

/-- A choice of allosemes for the v and n of a nominalization. -/
structure Derivation where
  v : Verbalizer.Alloseme
  n : Nominalizer.Alloseme
  deriving DecidableEq, Fintype

namespace Derivation

/-- The reading of the noun, that of its alloseme of n. -/
def reading (d : Derivation) : NominalizationReading := d.n.reading

/-- The heads of the nominalization, innermost first. -/
def heads (d : Derivation) : List Categorizer := [.v d.v, .n d.n]

/-- The complex event derivation has eventive v and zero n. -/
def cen : Derivation := ⟨.eventive, 0⟩

/-- The simple event derivation has zero v and the simple event alloseme of n. -/
def sen : Derivation := ⟨0, .simpleEvent⟩

/-- The simple entity derivation has zero v and the entity alloseme of n. -/
def simpleEntity : Derivation := ⟨0, .entity⟩

/-- The result derivation has eventive v and the result alloseme of n. -/
def result : Derivation := ⟨.eventive, .result⟩

theorem reading_cen : cen.reading = .complexEvent := rfl

theorem reading_sen : sen.reading = .simpleEvent := rfl

theorem reading_simpleEntity : simpleEntity.reading = .simpleEntity := rfl

theorem reading_result : result.reading = .result := rfl

/-- The nP denotes an event when v is eventive and n passes its meaning up unchanged. -/
def Eventive (d : Derivation) : Prop := d.v = .eventive ∧ d.n = 0

instance : DecidablePred Eventive := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem Eventive.reading_eq {d : Derivation} (h : d.Eventive) : d.reading = .complexEvent :=
  congrArg Nominalizer.Alloseme.reading h.2

end Derivation

/-! ### Complex heads -/

/-- The verb is the root categorized by eventive v. -/
def verb (r : Root) : ComplexHead Root Categorizer := ⟨r, [.v .eventive]⟩

/-- The nominalization is the root categorized by v and then by n. -/
def nominal (r : Root) (d : Derivation) : ComplexHead Root Categorizer := ⟨r, d.heads⟩

/-- A *-væða* verb is the root categorized by n, compounded with the v of *-væða*. -/
def vaedaVerb (r : Root) (a : Nominalizer.Alloseme) : ComplexHead Root Categorizer :=
  ⟨r, [.n a, .v .eventive]⟩

/-- A *-væðing* nominal is the *-væða* verb categorized by n. -/
def vaedaNominal (r : Root) (a c : Nominalizer.Alloseme) : ComplexHead Root Categorizer :=
  ⟨r, (vaedaVerb r a).heads ++ [.n c]⟩

/-! ### Borer's Generalization -/

/-- The position of n in the nominalization. -/
def nIdx (r : Root) (d : Derivation) : Fin (nominal r d).heads.length := ⟨1, Nat.one_lt_two⟩

theorem nominal_n_not_active_bot (r : Root) (d : Derivation) :
    ¬ (nominal r d).Active Categorizer.Cyclic (nIdx r d) ⊥ :=
  ComplexHead.not_active_bot_of_cyclic_of_cyclic (k := (⟨0, Nat.two_pos⟩ : Fin d.heads.length))
    (l := nIdx r d) (Fin.lt_def.2 Nat.zero_lt_one) trivial trivial

/-! ### The external argument -/

/-- The contentful allosemes of i*, the external-argument head that is Voice in the verbal
domain and Poss in the nominal domain. -/
inductive IStar.Contentful where
  | agent
  | possessor
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of i*. -/
abbrev IStar.Alloseme := WithZero IStar.Contentful

namespace IStar.Alloseme

@[match_pattern] def agent : IStar.Alloseme := WithZero.coe .agent

@[match_pattern] def possessor : IStar.Alloseme := WithZero.coe .possessor

end IStar.Alloseme

/-- i* is an agent in the context of an eventive complement and a possessor elsewhere. -/
def IStar.vocabulary : RuleSet (VocabularyItem Feature IStar.Alloseme) :=
  [⟨(complement {.eventive}).toFinset, .agent⟩, ∅ ⟷ .possessor]

/-- The alloseme of i* selected by its complement's features. -/
def IStar.alloseme (fs : Finset Feature) : IStar.Alloseme :=
  (subsetPrinciple IStar.vocabulary (complement fs)).getD .possessor

/-- An nP presents its category to i*, and eventivity when it denotes an event. -/
def Derivation.features (d : Derivation) : Finset Feature :=
  if d.Eventive then {.cat .n, .eventive} else {.cat .n}

theorem iStar_agent_iff (d : Derivation) :
    IStar.alloseme d.features = .agent ↔ d.Eventive := by
  by_cases h : d.Eventive
  · rw [Derivation.features, ite_eq_left h]; exact iff_of_true (by decide) h
  · rw [Derivation.features, ite_eq_right h]; exact iff_of_false (by decide) h

/-! ### Phase locality of special meaning -/

/-- Wood's phase locality lets a dependency conditioning special meaning cross at most one
categorizer. -/
def Local (between : List Categorizer) : Prop := between.length ≤ 1

/-- A preposition attaches to a complex head either adjoined to it or heading its complement
PP. -/
inductive Attachment where
  | adjunct
  | complement
  deriving DecidableEq, Repr

/-- The heads between a preposition and the root are every head of the complex head when the
preposition heads its complement, and all but the outermost when it adjoins to the complex head,
since a head does not c-command its own adjunct. -/
def interveners (s : ComplexHead Root Categorizer) : Attachment → List Categorizer
  | .complement => s.heads
  | .adjunct => s.heads.dropLast

theorem Local.adjunct_of_complement {s : ComplexHead Root Categorizer}
    (h : Local (interveners s .complement)) : Local (interveners s .adjunct) := by
  simp only [Local, interveners, List.length_dropLast] at h ⊢; omega

theorem verb_local (r : Root) (a : Attachment) : Local (interveners (verb r) a) := by
  cases a <;> simp [Local, interveners, verb]

theorem nominal_complement_not_local (r : Root) (d : Derivation) :
    ¬ Local (interveners (nominal r d) .complement) := by
  simp [Local, interveners, nominal, Derivation.heads]

theorem nominal_adjunct_local (r : Root) (d : Derivation) :
    Local (interveners (nominal r d) .adjunct) := by
  simp [Local, interveners, nominal, Derivation.heads]

theorem nominal_n_local (r : Root) (d : Derivation) : Local ((nominal r d).heads.take 1) := by
  simp [Local, nominal, Derivation.heads]

theorem vaeda_n_not_local (r : Root) (a c : Nominalizer.Alloseme) :
    ¬ Local ((vaedaNominal r a c).heads.take 2) := by
  simp [Local, vaedaNominal, vaedaVerb]

theorem vaeda_complement_not_local (r : Root) (a : Nominalizer.Alloseme) :
    ¬ Local (interveners (vaedaVerb r a) .complement) := by
  simp [Local, interveners, vaedaVerb]

/-! ### The prefixes *marg-* and *endur-* -/

/-- The event-modifying prefixes are iterative *marg-* 'many' and *endur-* 're-'. -/
inductive Prefix where
  | marg
  | endur
  deriving DecidableEq, Repr

/-! #### The meanings of the complex head -/

/-- The rules of the complex head: Functional Application and Predicate Conjunction. -/
abbrev grammar : ManySorted.Language (Interpreter.Ty Interpreter.Base) :=
  Interpreter.application.sum Interpreter.predicateModification

/-- The items a terminal of a complex head may be: the root is a predicate of entities or of
eventualities, as the head next to it requires, and eventive v is an activity. -/
def items {R : Type} : R ⊕ Categorizer → List (Σ a, Item a)
  | .inl _ => [⟨_, .rootEntity⟩, ⟨_, .rootEvent⟩]
  | .inr (.v .eventive) => [⟨_, .activity⟩]
  | .inr (.v _) => []
  | .inr (.n a) => a.items

/-- The types of the derivations of a nominalization, whatever its root. -/
def Derivation.types (d : Derivation) : List (Interpreter.Ty Interpreter.Base) :=
  ((⟨(), d.heads⟩ : ComplexHead Unit Categorizer).skeleton Categorizer.IsZero).elim [] fun s ↦
    ((Interpreter.typeDriven grammar).derivs items s).map (·.1)

-- The root's identity plays no part in which derivations there are.
theorem types_nominal (r : Root) (d : Derivation) :
    (((nominal r d).skeleton Categorizer.IsZero).elim [] fun s ↦
      ((Interpreter.typeDriven grammar).derivs items s).map (·.1)) = d.types := by
  rcases d with ⟨_ | ⟨⟨⟩⟩, _ | cn⟩ <;> (try cases cn) <;> rfl

/-- The allosemes of a nominalization compose on some construal of the root. -/
def Derivation.Composes (d : Derivation) : Prop := d.types ≠ []

instance : DecidablePred Derivation.Composes := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- Eventive v gives a predicate of eventualities, which among the allosemes of n only the
result alloseme takes, and which the noun keeps when n is pruned; with v pruned the root meets n
and takes the type it needs. -/
theorem Derivation.composes_iff (d : Derivation) :
    d.Composes ↔ (d.v = .eventive ∧ (d.n = 0 ∨ d.n = .result)) ∨
      (d.v = 0 ∧ (d.n = .simpleEvent ∨ d.n = .state ∨ d.n = .entity ∨ d.n = .result)) := by
  revert d
  decide

-- Among the derivations that compose, the complex event reading is that of eventive v under
-- the zero alloseme of n.
theorem Derivation.eventive_iff_reading {d : Derivation} (hc : d.Composes) :
    d.Eventive ↔ d.reading = .complexEvent := by
  revert d
  decide

-- Every reading but the content one has a derivation that composes.
theorem Derivation.exists_composes_reading {rd : NominalizationReading} (h : rd ≠ .content) :
    ∃ d : Derivation, d.Composes ∧ d.reading = rd := by
  revert rd
  decide

theorem borers_generalization (r : Root) {d : Derivation} (hc : d.Composes)
    (h : d.reading = .complexEvent) :
    d.v = .eventive ∧ ¬ (nominal r d).Active Categorizer.Cyclic (nIdx r d) ⊥ :=
  ⟨((Derivation.eventive_iff_reading hc).2 h).1, nominal_n_not_active_bot r d⟩

section Denotations

variable {E V : Type} (m : NominalizationModel E V) (ρ : RootMeaning E V)

/-- The denotations of a nominalization, one for each of its derivations. -/
def Derivation.denotations (d : Derivation) :
    List (Interpreter.Denotation E Unit { eventuality := V }) :=
  ((⟨(), d.heads⟩ : ComplexHead Unit Categorizer).skeleton Categorizer.IsZero).elim [] <|
    (Interpreter.typeDriven grammar).values
      (D := Interpreter.Ty.Dom (Interpreter.Base.Dom E Unit { eventuality := V })) inferInstance
      (Item.val m ρ) items

/-- The complex event noun has the meaning of the verb, a predicate of eventualities. -/
theorem denotations_cen :
    Derivation.cen.denotations m ρ = [⟨.vt, fun e ↦ ρ.onEvents e ∧ m.activity e⟩] :=
  rfl

-- The simple event noun: the entities the root holds of that are events.
theorem denotations_sen :
    Derivation.sen.denotations m ρ =
      [⟨.et, fun x ↦ ρ.onEntities x ∧ ∃ e, x = m.ev e ∧ ¬ m.stative e⟩] :=
  rfl

-- The simple entity noun.
theorem denotations_simpleEntity :
    Derivation.simpleEntity.denotations m ρ = [⟨.et, ρ.onEntities⟩] :=
  rfl

/-- The result noun built on the interpreted verb: what an activity of the root's kind
produced. -/
theorem denotations_result :
    Derivation.result.denotations m ρ =
      [⟨.et, fun x ↦ ∃ e, (ρ.onEvents e ∧ m.activity e) ∧ m.result x e⟩] :=
  rfl

end Denotations

/-! #### *marg-* by composition -/

/-- The meaning of *marg-*: a modifier of a predicate of eventualities. -/
inductive MargItem : Interpreter.Ty Interpreter.Base → Type
  | marg : MargItem (.fn .vt .vt)

/-- The items of a *marg-* nominalization: those of the complex head, and the prefix. -/
def margItems {R : Type} : Unit ⊕ R ⊕ Categorizer → List (Σ a, Item a ⊕ MargItem a)
  | .inl () => [⟨_, .inr .marg⟩]
  | .inr x => (items x).map fun ⟨a, i⟩ ↦ ⟨a, .inl i⟩

/-- The complex head of a *marg-* nominalization, the prefix adjoined to v. -/
def margNominal {R : Type} (s : ComplexHead R Categorizer) :
    Option (Interpreter.Skeleton Unit (Unit ⊕ R ⊕ Categorizer)) :=
  s.adjoinedSkeleton Categorizer.IsZero 1 ()

/-- *marg-* composes on a nominalization: the complex head with the prefix has a derivation,
whatever the root. -/
def MargComposes (d : Derivation) : Prop :=
  ((margNominal (⟨(), d.heads⟩ : ComplexHead Unit Categorizer)).elim []
    ((Interpreter.typeDriven grammar).derivs margItems)) ≠ []

instance : DecidablePred MargComposes := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- *marg-* needs an interpreted v to adjoin to and a predicate of eventualities below it, so
it composes exactly on eventive v under the allosemes of n that keep or take such a predicate,
the zero and the result allosemes. -/
theorem margComposes_iff (d : Derivation) :
    MargComposes d ↔ d.v = .eventive ∧ (d.n = 0 ∨ d.n = .result) := by
  revert d
  decide

/-- The meaning of *marg-* in a model whose iterated eventualities are `iter`, and of the other
terminals. -/
def margVal {E V : Type} (m : NominalizationModel E V) (ρ : RootMeaning E V) (iter : V → Prop) :
    {a : Interpreter.Ty Interpreter.Base} → Item a ⊕ MargItem a →
      a.Domain E Unit { eventuality := V }
  | _, .inl i => i.val m ρ
  | _, .inr .marg => fun P e ↦ P e ∧ iter e

-- (6.44c): the complex event reading of a *marg-* noun, iterated activities of the root's kind.
theorem values_margNominal_cen {E V : Type} (m : NominalizationModel E V) (ρ : RootMeaning E V)
    (iter : V → Prop) (r : Root) :
    (margNominal (nominal r .cen)).elim [] ((Interpreter.typeDriven grammar).values
        (D := Interpreter.Ty.Dom (Interpreter.Base.Dom E Unit { eventuality := V })) inferInstance
        (margVal m ρ iter) margItems) =
      [⟨.vt, fun e ↦ (ρ.onEvents e ∧ m.activity e) ∧ iter e⟩] :=
  rfl

/-! #### *endur-* -/

/-- *endur-* is licensed on a nominalization where v or n carries an event variable: under
eventive v, and under the simple event and result allosemes of n. -/
def EndurLicensed (d : Derivation) : Prop :=
  d.v = .eventive ∨ d.n = .simpleEvent ∨ d.n = .result

instance : DecidablePred EndurLicensed := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- A prefix is licensed on a nominalization: *marg-* where it composes, *endur-* where an event
variable is present. -/
def Licensed : Prefix → Derivation → Prop
  | .marg, d => MargComposes d
  | .endur, d => EndurLicensed d

instance (p : Prefix) (d : Derivation) : Decidable (Licensed p d) :=
  match p with
  | .marg => inferInstanceAs (Decidable (MargComposes d))
  | .endur => inferInstanceAs (Decidable (EndurLicensed d))

/-- The prefixes as the rows name them. -/
def prefixTable : List (String × Prefix) := [("marg-", .marg), ("endur-", .endur)]

/-- The readings as the rows name them, where the referring reading of *þvottur* is the simple
entity one and that of *endurprentun* the result. -/
def readingTable : List (String × Derivation) :=
  [("CEN", .cen), ("SEN", .sen), ("RN", .simpleEntity), ("result RN", .result)]

/-- A row of a prefixed nominal on a reading, as the prefix and the derivation. -/
def ofRow (ex : Datum) : Option (Prefix × Derivation) := do
  let p ← ex.parse? "prefix" prefixTable
  let d ← ex.parse? "reading" readingTable
  pure (p, d)

theorem rows_licensed :
    ∀ ex ∈ Examples.all, ∀ pd ∈ ofRow ex,
      (ex.judgment = .acceptable ↔ Licensed pd.1 pd.2) := by
  decide

/-! ### Allosemy conditioned by the root -/

/-- The judgments of the rows on a nominal of the language file under a reading. -/
def judgments (w : Deverbal) (reading : String) : List Judgment :=
  (Examples.all.filter fun ex ↦
    ex.feature? "nominal" = some (Morph.surface w.morphs) ∧
      ex.feature? "reading" = some reading).map (·.judgment)

theorem reading_not_by_nominalizer :
    addaun.nominalizer = vidvorun.nominalizer ∧
      judgments addaun "RN" = [.ungrammatical] ∧ judgments vidvorun "RN" = [.acceptable] := by
  decide

end Wood2023
