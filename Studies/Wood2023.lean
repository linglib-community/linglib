module

public import Linglib.Morphology.DistributedMorphology.Allosemy
public import Linglib.Morphology.DistributedMorphology.Locality
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.InsideOut
public import Linglib.Fragments.Icelandic.Nouns
public import Linglib.Data.Examples.Wood2023

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
Every segmentation in `Fragments.Icelandic.Nouns` is derived this way
(`Allomorphy.fragment_realize`).

Special meaning is subject to phase locality: a dependency may cross at most one categorizer
(`Local`). A preposition heading the PP complement of a nominal is separated from the root by
v and n, so a preposition that conditions the root's meaning must adjoin to the complex n head
as a prefix, while one with its own meaning heads a PP, and one that does both is doubled
(`nominal_complement_not_local`). The same bound lets n condition an idiosyncratic root meaning
across v (`nominal_n_local`) and forbids it in *-væðing* nominals, where *-væða* is a compound
head attaching to a categorized word, so that two categorizers separate the root from the
outer n (`vaeda_n_not_local`). The prefixes *marg-* and *endur-* are event modifiers: *marg-*
adjoins to v, *endur-* to v or to n, and each needs an event variable at its host, which
licenses *marg-* exactly on nominals whose v is eventive and *endur-* also on simple event and
result nominals but not on simple entities (`Licensed`); the book's judgments on the prefixed
readings of *þvottur* and *prentun* are the rows of `Data.Examples.Wood2023`, checked one by one
(`rows_licensed`). Allosemy is contextual as allomorphy is: *aðdáun* and *viðvörun* share the
nominalizer *-un*, and only the second has a concrete entity reading
(`reading_not_by_nominalizer`).

## Implementation notes

The exponents of the roots and affixes are the surface morphs of the fragment, so the u-umlaut
of *söfn-un* and *vönt-un* is not undone and the theme vowel *-a* of the verb is absent, as
the book's own segmentation has it. The roots are identified by their forms. The prefixed
preposition of *við-ger-ð* adjoins to n and is not inserted by the vocabulary; the derivation
covers the root, v, and n. Wood's bound for allosemy, one intervening categorizer, is one
phase looser than `ComplexHead.RootLocal`, the bound the book keeps for root suppletion; the study
states the strict one through the substrate. A preposition adjoined to a complex head has no
spine position, since a head does not c-command its own adjunct, so the heads between a
preposition and the root are read off its attachment. The event-modifier account licenses
*marg-* on a result nominal built on eventive v, a case the book does not test.

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

open DistributedMorphology DistributedMorphology.Allosemy Icelandic.Nouns Morphology.Exponence
open Wood2023.Examples
open Morphology (Morph)

/-! ### Vocabulary Insertion at v and n -/

namespace Allomorphy

/-- A Vocabulary Item of v or n may mention the category of its own head, or the exponent of a
concatenated neighbor, a root or an affix. -/
inductive Feature
  | cat (c : Categorizer)
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
and after the roots the fragment shows with *-un*, *-n*, *-ttur* and *-ð* after their roots,
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

/-- A head of the complex head is a categorizer with its alloseme. -/
inductive Head where
  | v (a : Verbalizer.Alloseme)
  | n (a : Nominalizer.Alloseme)
  deriving DecidableEq, Repr

/-- Every head of the complex head is a categorizer, hence a phase head. -/
def Head.Cyclic : Head → Prop := fun _ ↦ True

instance : DecidablePred Head.Cyclic := fun _ ↦ inferInstanceAs (Decidable True)

/-- A choice of allosemes for the v and n of a nominalization. -/
structure Derivation where
  v : Verbalizer.Alloseme
  n : Nominalizer.Alloseme
  deriving DecidableEq, Fintype

namespace Derivation

/-- The reading the allosemes yield. -/
def reading (d : Derivation) : Option NominalizationReading := readingFromAllosemes d.v d.n

/-- The heads of the nominalization, innermost first. -/
def heads (d : Derivation) : List Head := [.v d.v, .n d.n]

/-- The complex event derivation has eventive v and zero n. -/
def cen : Derivation := ⟨.eventive, .zero⟩

/-- The simple event derivation has zero v and the simple event alloseme of n. -/
def sen : Derivation := ⟨.zero, .simpleEvent⟩

/-- The simple entity derivation has zero v and the entity alloseme of n. -/
def simpleEntity : Derivation := ⟨.zero, .entity⟩

/-- The result derivation has eventive v and the result alloseme of n. -/
def result : Derivation := ⟨.eventive, .result⟩

theorem reading_cen : cen.reading = some .complexEvent := rfl

theorem reading_sen : sen.reading = some .simpleEvent := rfl

theorem reading_simpleEntity : simpleEntity.reading = some .simpleEntity := rfl

theorem reading_result : result.reading = some .result := rfl

/-- The nP denotes an event when v is eventive and n passes its meaning up unchanged. -/
def Eventive (d : Derivation) : Prop := d.v = .eventive ∧ d.n = .zero

instance : DecidablePred Eventive := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem eventive_iff (d : Derivation) : d.Eventive ↔ d.reading = some .complexEvent := by
  revert d; decide

theorem exists_reading (rd : NominalizationReading) : ∃ d : Derivation, d.reading = some rd := by
  cases rd
  exacts [⟨cen, rfl⟩, ⟨sen, rfl⟩, ⟨result, rfl⟩, ⟨⟨.zero, .state⟩, rfl⟩, ⟨simpleEntity, rfl⟩,
    ⟨⟨.zero, .content⟩, rfl⟩]

end Derivation

/-! ### Complex heads -/

/-- The verb is the root categorized by eventive v. -/
def verb (r : Root) : ComplexHead Root Head := ⟨r, [.v .eventive]⟩

/-- The nominalization is the root categorized by v and then by n. -/
def nominal (r : Root) (d : Derivation) : ComplexHead Root Head := ⟨r, d.heads⟩

/-- A *-væða* verb is the root categorized by n, compounded with the v of *-væða*. -/
def vaedaVerb (r : Root) (a : Nominalizer.Alloseme) : ComplexHead Root Head :=
  ⟨r, [.n a, .v .eventive]⟩

/-- A *-væðing* nominal is the *-væða* verb categorized by n. -/
def vaedaNominal (r : Root) (a c : Nominalizer.Alloseme) : ComplexHead Root Head :=
  ⟨r, (vaedaVerb r a).heads ++ [.n c]⟩

/-! ### Borer's Generalization -/

theorem nominal_n_not_rootLocal (r : Root) (d : Derivation) :
    ¬ (nominal r d).RootLocal Head.Cyclic ⟨1, Nat.one_lt_two⟩ :=
  ComplexHead.not_rootLocal_of_cyclic_of_cyclic (j := ⟨0, Nat.two_pos⟩)
    (Fin.mk_lt_mk.2 Nat.zero_lt_one) trivial trivial

theorem borers_generalization (r : Root) {d : Derivation}
    (h : d.reading = some .complexEvent) :
    d.v = .eventive ∧ ¬ (nominal r d).RootLocal Head.Cyclic ⟨1, Nat.one_lt_two⟩ :=
  ⟨((Derivation.eventive_iff d).2 h).1, nominal_n_not_rootLocal r d⟩

/-! ### The external argument -/

/-- The contentful allosemes of i*, the external-argument head that is Voice in the verbal
domain and Poss in the nominal domain. -/
inductive IStar.Contentful where
  | agent
  | possessor
  deriving DecidableEq, Repr, Fintype

/-- The allosemes of i*. -/
abbrev IStar.Alloseme := Allosemy.Alloseme IStar.Contentful

namespace IStar.Alloseme

@[match_pattern] def agent : IStar.Alloseme := Allosemy.Alloseme.of .agent

@[match_pattern] def possessor : IStar.Alloseme := Allosemy.Alloseme.of .possessor

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
    IStar.alloseme d.features = .agent ↔ d.reading = some .complexEvent := by
  rw [← Derivation.eventive_iff]
  by_cases h : d.Eventive
  · rw [Derivation.features, ite_eq_left h]; exact iff_of_true (by decide) h
  · rw [Derivation.features, ite_eq_right h]; exact iff_of_false (by decide) h

/-! ### Phase locality of special meaning -/

/-- Wood's phase locality lets a dependency conditioning special meaning cross at most one
categorizer. -/
def Local (between : List Head) : Prop := between.length ≤ 1

/-- A preposition attaches to a complex head either adjoined to it or heading its complement
PP. -/
inductive Attachment where
  | adjunct
  | complement
  deriving DecidableEq, Repr

/-- The heads between a preposition and the root are every head of the complex head when the
preposition heads its complement, and all but the outermost when it adjoins to the complex head,
since a head does not c-command its own adjunct. -/
def interveners (s : ComplexHead Root Head) : Attachment → List Head
  | .complement => s.heads
  | .adjunct => s.heads.dropLast

theorem Local.adjunct_of_complement {s : ComplexHead Root Head}
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

/-- At the complex head *marg-* adjoins to v, and *endur-* to v or n. -/
def Prefix.AdjoinsTo : Prefix → Head → Prop
  | .marg, .v _ => True
  | .marg, .n _ => False
  | .endur, _ => True

/-- A head's alloseme carries an event variable for eventive v and for the simple event and
result allosemes of n. -/
def Head.HasEvent : Head → Prop
  | .v a => a = .eventive
  | .n a => a = .simpleEvent ∨ a = .result

/-- A prefix is licensed on a nominalization when some head it adjoins to there carries an
event variable. -/
def Licensed (p : Prefix) (d : Derivation) : Prop :=
  ∃ h ∈ d.heads, p.AdjoinsTo h ∧ h.HasEvent

theorem licensed_marg_iff (d : Derivation) : Licensed .marg d ↔ d.v = .eventive := by
  simp [Licensed, Derivation.heads, Prefix.AdjoinsTo, Head.HasEvent]

theorem licensed_endur_iff (d : Derivation) :
    Licensed .endur d ↔ d.v = .eventive ∨ d.n = .simpleEvent ∨ d.n = .result := by
  simp [Licensed, Derivation.heads, Prefix.AdjoinsTo, Head.HasEvent]

theorem Licensed.endur {d : Derivation} (h : Licensed .marg d) : Licensed .endur d :=
  (licensed_endur_iff d).2 (Or.inl ((licensed_marg_iff d).1 h))

instance (p : Prefix) (d : Derivation) : Decidable (Licensed p d) :=
  match p with
  | .marg => decidable_of_iff _ (licensed_marg_iff d).symm
  | .endur => decidable_of_iff _ (licensed_endur_iff d).symm

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

/-- The judgments of the rows on a nominal of the fragment under a reading. -/
def judgments (w : Deverbal) (reading : String) : List Judgment :=
  (Examples.all.filter fun ex ↦
    ex.feature? "nominal" = some (Morph.surface w.morphs) ∧
      ex.feature? "reading" = some reading).map (·.judgment)

theorem reading_not_by_nominalizer :
    addaun.nominalizer = vidvorun.nominalizer ∧
      judgments addaun "RN" = [.ungrammatical] ∧ judgments vidvorun "RN" = [.acceptable] := by
  decide

end Wood2023
