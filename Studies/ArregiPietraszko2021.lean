module

public import Linglib.Core.Algebra.Free
public import Linglib.Syntax.Minimalist.Clause.VerbalSpine
public import Linglib.Data.Examples.ArregiPietraszko2021
public import Linglib.Data.Examples.HarizanovGribanova2019
public import Linglib.Data.Wordlist.ArregiPietraszko2021
public import Linglib.Fragments.Ndebele.Phonology
public import Linglib.Morphology.DistributedMorphology.Spellout
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Phonology.Hiatus
public import Studies.HarizanovGribanova2019
public import Studies.Pollock1989
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Arregi and Pietraszko (2021): The ups and downs of head displacement

Arregi and Pietraszko replace head raising and lowering by one syntactic operation, Generalized
Head Movement, in which a head shares its M-value, the morphological features that Vocabulary
Insertion spells out, with the head of its complement. The heads of a clause thus form a head
chain around one complex head, pronounced in the chain's highest strong position, or in its
highest position if none is strong. A chain that ends in a strong verb splits when a specifier
intervenes or the verb phrase is elided or fronted, and the verb's terminal, an orphan in the
half without the verb, is exponed as *do*.

## Implementation notes

* A clause is a `Minimalist.VerbalSpine`: the tag of its verb, the heads related to the verb,
  the heads whose specifier is pronounced, and what becomes of the verb phrase. A specifier
  intervenes when it is that of a head below the highest. A negative imperative, where Σ keeps C
  out of the verb's chain, is thereby the spine of a declarative.
* Strength is a property of the functional heads and, for the verb, of its tag, so that English
  lexical verbs are strong and its auxiliaries weak while Danish auxiliaries are strong too.
* Split-by-Deletion applies in every language, the possibility the paper raises for its typology
  of splitting; Split-by-Intervention is a setting.
* A language's settings record what the paper's data settle, so the fate of an orphan T is absent
  where no do-support or fronting datum shows it. The fates are the library's impoverishment and
  obliteration rules, and the elsewhere exponent comes from impoverishing the orphan at its own
  insertion only, which leaves its features to condition the stem.
* An M-value is an element of the free magma over the terminals, each product listing the lower
  constituent first. The operation leaves linear order open, and only the Ndebele prefix is
  linearized. Negative Merger applies to a chain, which makes its terminal an orphan there, an
  ordering the paper notes is indistinguishable from its own.

## References

* [arregi-pietraszko-2021]
* [baker-1985]
* [pollock-1989]
* [harizanov-gribanova-2019]
* [arregi-nevins-2012]
-/

@[expose] public section

namespace ArregiPietraszko2021

open Phonology FreeMagma DistributedMorphology Morphology Minimalist

/-! ### Head chains -/

/-- A head chain is a sequence of syntactic terminals, lowest first, that share one M-value, a
complex head over morphological terminals. -/
structure HeadChain where
  positions : List Cat
  mvalue : FreeMagma Cat

namespace HeadChain

/-- The morphological terminals of the M-value, lowest first. -/
def terminals (c : HeadChain) : List Cat := (FreeMagma.lift FreeMonoid.of c.mvalue).toList

/-- Generalized Head Movement, GenHM, relates a head to the chain of its complement's head. The
head joins the chain, and its morphological terminal attaches outside the shared M-value. -/
def extend (x : Cat) (c : HeadChain) : HeadChain := ⟨c.positions ++ [x], c.mvalue * of x⟩

/-- The chain that cyclic GenHM builds from `bottom` up through the heads `above`. -/
def ofHeads (bottom : Cat) (above : List Cat) : HeadChain :=
  ⟨bottom :: above, above.foldl (· * of ·) (of bottom)⟩

theorem extend_ofHeads (bottom x : Cat) (above : List Cat) :
    (ofHeads bottom above).extend x = ofHeads bottom (above ++ [x]) := by
  simp [extend, ofHeads]

/-- By the **Mirror Principle**, the terminals of a complex head are ordered as its heads are. -/
theorem terminals_ofHeads (bottom : Cat) (above : List Cat) :
    (ofHeads bottom above).terminals = bottom :: above := by
  simp [terminals, ofHeads, toList_lift_foldl_mul_of]

/-- GenHM derives the Mirror Principle: each terminal of a complex head attaches outside the
complex head of the heads below it. -/
theorem isLeftComb_mvalue_ofHeads (bottom : Cat) (above : List Cat) :
    (ofHeads bottom above).mvalue.IsLeftComb :=
  (isLeftComb_foldl_mul_of _ _).mpr (isLeftComb_of _)

/-- Orphan Assignment marks a morphological terminal in a chain that does not contain its
syntactic terminal. -/
def Orphan (c : HeadChain) (x : Cat) : Prop := x ∈ c.terminals ∧ x ∉ c.positions

instance (c : HeadChain) (x : Cat) : Decidable (c.Orphan x) := inferInstanceAs (Decidable (_ ∧ _))

theorem not_orphan_ofHeads (bottom x : Cat) (above : List Cat) :
    ¬ (ofHeads bottom above).Orphan x := by
  rw [Orphan, terminals_ofHeads]; exact fun h ↦ h.2 h.1

/-- Head Chain Pronunciation delinks every position of a chain but its highest strong one, or
its highest if none is strong. -/
def pronounced (strong : Finset Cat) (c : HeadChain) : Option Cat :=
  (c.positions.filter (· ∈ strong)).getLast?.or c.positions.getLast?

theorem mem_positions_of_pronounced {strong : Finset Cat} {c : HeadChain} {x : Cat}
    (h : c.pronounced strong = some x) : x ∈ c.positions := by
  rcases Option.or_eq_some_iff.mp h with h | ⟨-, h⟩
  · exact (List.mem_filter.mp (List.mem_of_getLast? h)).1
  · exact List.mem_of_getLast? h

theorem pronounced_of_forall_not_mem {strong : Finset Cat} {c : HeadChain}
    (h : ∀ x ∈ c.positions, x ∉ strong) : c.pronounced strong = c.positions.getLast? := by
  have : c.positions.filter (· ∈ strong) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx ↦ by simpa using h x hx
  rw [pronounced, this]; rfl

theorem pronounced_extend_of_mem {strong : Finset Cat} {x : Cat} (hx : x ∈ strong)
    (c : HeadChain) : (c.extend x).pronounced strong = some x := by
  simp [pronounced, extend, List.filter_append, hx]

end HeadChain

/-! ### Languages -/

/-- The fate of an orphan T at spell-out. The mark of an orphan does nothing to it, or makes
insertion at it disregard its tense and agreement, or impoverishes them, or obliterates the
terminal. -/
inductive OrphanFate
  | ignored | elsewhere | impoverished | obliterated
  deriving DecidableEq, Repr

/-- The settings of a language. -/
structure Language where
  /-- The strong functional heads, the positions that hold the pronunciation of a chain down. -/
  strong : Finset Cat := ∅
  /-- The tags of the verbs that are strong, holding the pronunciation of a chain in the verb. -/
  strongVerbs : Finset UD.UPOS := ∅
  /-- Whether a chain splits at a strong verb below an intervening specifier. -/
  splitByIntervention : Bool := false
  /-- Whether sentential negation is an adverbial, not the specifier of ΣP. -/
  adverbialNegation : Bool := false
  /-- The fate of an orphan T. -/
  orphanT : Option OrphanFate := none

/-- English has strong lexical verbs and Split-by-Intervention, and obliterates an orphan T. -/
def english : Language :=
  { strongVerbs := {.VERB}, splitByIntervention := true, orphanT := some .obliterated }

/-- French has no strong head. -/
def french : Language := {}

/-- Danish has strong verbs, auxiliaries among them, and a strong C, and no
Split-by-Intervention. -/
def danish : Language := { strong := {.C}, strongVerbs := {.VERB, .AUX} }

/-- Swedish has the Danish settings and ignores an orphan T. -/
def swedish : Language := { danish with orphanT := some .ignored }

/-- Monnese has strong lexical verbs, T and C, and Split-by-Intervention; its negation is an
adverbial, and it impoverishes an orphan T. -/
def monnese : Language :=
  { strong := {.T, .C}, strongVerbs := {.VERB}, splitByIntervention := true,
    adverbialNegation := true,
    orphanT := some .impoverished }

/-- Polish has weak verbs and impoverishes an orphan T. -/
def polish : Language := { orphanT := some .impoverished }

/-- Hebrew has weak verbs and impoverishes an orphan T. -/
def hebrew : Language := { orphanT := some .impoverished }

/-- Yiddish has weak verbs and gives an orphan T its elsewhere exponent. -/
def yiddish : Language := { orphanT := some .elsewhere }

/-- Spanish has no strong head in imperatives. -/
def spanish : Language := {}

/-- The Vallader of Scuol has a strong imperative T. -/
def vallader : Language := { strong := {.T} }

/-- Ndebele has a strong T. -/
def ndebele : Language := { strong := {.T} }

/-- The strong positions of a clause whose verb has the tag: the strong functional heads, and the
position of the verb if verbs with its tag are strong. -/
def Language.strongAt (L : Language) (verb : UD.UPOS) : Finset Cat :=
  if verb ∈ L.strongVerbs then insert .V L.strong else L.strong

/-! ### The spell-out of orphans -/

/-- The features of the terminals of a verbal word are the verb, T with its tense and agreement,
negation, and the mark of an orphan. -/
inductive Feat
  | verb | T | tense | agr | neg | orphan
  deriving DecidableEq, Repr

/-- The pieces of a verbal word are the stem, the allomorph of the stem that tense conditions,
the dummy verb, the finite and the infinitival exponent of T, and contracted negation. -/
inductive Piece
  | stem | finiteStem | dummy | finite | infinitival | contracted
  deriving DecidableEq, Repr

/-- The Vocabulary of a verbal word. An orphan verb is the dummy verb, a verb beside a T that
bears tense takes the allomorph that tense conditions, and the infinitival exponent is the
elsewhere exponent of T. -/
def vocabulary : RuleSet (VocabularyItem Feat Piece) :=
  [{.verb, .orphan} ⟷ .dummy, ⟨{(0, .verb), (1, .tense)}, .finiteStem⟩, {.verb} ⟷ .stem,
    {.T, .tense, .agr} ⟷ .finite, {.T} ⟷ .infinitival, {.neg} ⟷ .contracted]

theorem subsetPrinciple_eq_dummy_iff {n : Neighborhood (Finset Feat)} (hT : .T ∉ n.focus) :
    subsetPrinciple vocabulary n = some .dummy ↔ .verb ∈ n.focus ∧ .orphan ∈ n.focus := by
  let dummy : VocabularyItem Feat Piece := {.verb, .orphan} ⟷ .dummy
  constructor
  · intro h
    obtain ⟨i, hi, he, hs⟩ := subsetPrinciple_winner_mem h
    simp only [vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> cases he
    have hf := VocabularyItem.applies_ofFeatures.1 hs
    exact ⟨hf (by simp), hf (by simp)⟩
  · rintro ⟨hv, ho⟩
    have hT' : ∀ (fs : Finset Feat) (e : Piece), .T ∈ fs →
        ¬ Morphology.Applies (fs ⟷ e) n :=
      fun fs e h hs ↦ hT (VocabularyItem.applies_ofFeatures.1 hs h)
    have key : ∀ s ∈ vocabulary, Morphology.Applies s n →
        s = dummy ∨ s.specificity < dummy.specificity := by
      intro s hs ha
      simp only [vocabulary, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (by decide)
      · exact .inr (by decide)
      · exact absurd ha (hT' _ _ (by simp))
      · exact absurd ha (hT' _ _ (by simp))
      · exact .inr (by decide)
    exact RuleSet.realize_eq_of_forall_le (r := dummy) (by simp [vocabulary, dummy])
      (VocabularyItem.applies_ofFeatures.2 (by simp [Finset.insert_subset_iff, hv, ho]))
      (fun s hs ha ↦ (key s hs ha).elim (fun h ↦ h ▸ le_rfl) le_of_lt)
      (fun s hs ha he ↦ (key s hs ha).elim (fun h ↦ h ▸ rfl) fun h ↦ absurd he h.ne)

/-- Impoverishment deletes the tense and the agreement of an orphan T. -/
def impoverishment : List (ImpoverishmentRule (Finset Feat) Feat) :=
  [.ofFocus (fun b ↦ .T ∈ b ∧ .orphan ∈ b) .tense, .ofFocus (fun b ↦ .T ∈ b ∧ .orphan ∈ b) .agr]

/-- The focus of a neighborhood after impoverishment. -/
def impoverish (n : Neighborhood (Finset Feat)) : Finset Feat :=
  runChain (ImpoverishmentRule.apply Finset.erase) impoverishment n

/-- Obliteration deletes an orphan T. -/
def obliteration : ObliterationRule (Finset Feat) := ⟨fun n ↦ .T ∈ n.focus ∧ .orphan ∈ n.focus⟩

/-- Vocabulary Insertion at each terminal of a word, with no rule before it. -/
def insertion : Spellout (Finset Feat) Piece where
  modules := []
  insert n := (subsetPrinciple vocabulary n).toList

/-- The spell-out of a word under each fate of an orphan T. Impoverishment applies before
insertion, or to the orphan at its own insertion only, where its features still condition the
stem beside it. -/
def OrphanFate.spellout : OrphanFate → Spellout (Finset Feat) Piece
  | .ignored => insertion
  | .elsewhere => insertion.rewriteAt impoverish
  | .impoverished => insertion.rewriteBefore impoverish
  | .obliterated => { insertion with modules := [obliteration.apply] }

/-- The features of a terminal that has an exponent in a verbal word. -/
def feats : Cat → Option (Finset Feat)
  | .V => some {.verb}
  | .T => some {.T, .tense, .agr}
  | .Neg => some {.neg}
  | _ => none

/-- `c.domain` is the word of `c` as Vocabulary Insertion meets it, its terminals that have
exponents, each with the mark of an orphan if it is one. -/
def HeadChain.domain (c : HeadChain) : SpelloutDomain (Finset Feat) :=
  c.terminals.filterMap fun x ↦ (feats x).map fun fs ↦ if c.Orphan x then insert .orphan fs else fs

/-- The pieces of the word that a chain is pronounced as, terminal by terminal, or `none` where
its T is an orphan and what the language does to an orphan T is not recorded. -/
def HeadChain.word (L : Language) (c : HeadChain) : Option (List (List Piece)) :=
  (if c.Orphan .T then L.orphanT else some .ignored).map (·.spellout.pf c.domain)

/-- The four fates of an orphan T give the four forms of a fronted verb: a finite verb where the
orphan is ignored, the infinitival exponent on the stem that tense conditions where insertion
disregards the features of the orphan, a true infinitive under impoverishment, and a bare stem
under obliteration. -/
theorem fronted_forms :
    let fronted : HeadChain := ⟨[.V], (HeadChain.ofHeads .V [.T]).mvalue⟩
    OrphanFate.ignored.spellout.pf fronted.domain = [[.finiteStem], [.finite]] ∧
      OrphanFate.elsewhere.spellout.pf fronted.domain = [[.finiteStem], [.infinitival]] ∧
      OrphanFate.impoverished.spellout.pf fronted.domain = [[.stem], [.infinitival]] ∧
      OrphanFate.obliterated.spellout.pf fronted.domain = [[.stem]] := by
  decide

/-! ### Spines and chain splitting -/

/-- T is related to the verb, the subject pronounced in its specifier. -/
def declarative : VerbalSpine := { above := [.T], specifiers := {.T} }

/-- Σ stands between T and the verb, and its specifier, negation or verum focus, is pronounced. -/
def polarity : VerbalSpine := { above := [.Pol, .T], specifiers := {.Pol, .T} }

/-- Sentential negation in a language. -/
def negation (L : Language) : VerbalSpine := if L.adverbialNegation then declarative else polarity

/-- C is related to T and the specifier of T is not pronounced, as in a subject question, whose
Spec,TP holds a lower copy, a subject-initial verb-second clause, and an affirmative
imperative. -/
def toC : VerbalSpine := { above := [.T, .C] }

/-- C is related to T across the subject pronounced in Spec,TP. -/
def inversion : VerbalSpine := { toC with specifiers := {.T} }

/-- A chain that ends in a strong lexical verb splits at the verb when the language has
Split-by-Intervention and a pronounced specifier intervenes, or when the verb is unpronounced
under ellipsis or as the lower copy of a fronted verb phrase. -/
def Splits (L : Language) (x : VerbalSpine) : Prop :=
  x.verb = .VERB ∧ .VERB ∈ L.strongVerbs ∧ x.above ≠ [] ∧
    (L.splitByIntervention ∧ x.Intervenes ∨ x.vp ≠ .inSitu)

instance (L : Language) (x : VerbalSpine) : Decidable (Splits L x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The head chains of a clause at Spell-Out, with the strong positions of the clause. -/
structure Chains where
  /-- The chain of the verb's own position. -/
  verb : HeadChain
  /-- The chain of the highest head, whose word carries finite inflection. -/
  finite : HeadChain
  /-- The chain of the verb in a fronted copy of the verb phrase. -/
  fronted : Option HeadChain
  /-- The strong positions of the clause. -/
  strong : Finset Cat

/-- `derive L x` holds the chains of a clause. GenHM relates the verb to the heads above it, a
split leaves the verb alone in one half, and a fronted verb phrase carries a copy of the verb with
the whole M-value. -/
def derive (L : Language) (x : VerbalSpine) : Chains :=
  let c := HeadChain.ofHeads .V x.above
  let alone : HeadChain := ⟨[.V], c.mvalue⟩
  { verb := if Splits L x then alone else c
    finite := if Splits L x then ⟨x.above, c.mvalue⟩ else c
    fronted := if x.vp = .fronted then some alone else none
    strong := L.strongAt x.verb }

namespace Chains

/-- The position in which the finite word is pronounced. -/
def finitePosition (d : Chains) : Option Cat := d.finite.pronounced d.strong

/-- The finite word contains an orphan verb, exponed as *do*. -/
def DoSupport (d : Chains) : Prop := d.finite.Orphan .V

instance (d : Chains) : Decidable d.DoSupport := inferInstanceAs (Decidable (HeadChain.Orphan ..))

/-- The verb's M-value contains C, which conditions the imperative allomorphs of the verb. -/
def HasC (d : Chains) : Prop := .C ∈ d.verb.terminals

instance (d : Chains) : Decidable d.HasC := inferInstanceAs (Decidable (_ ∈ _))

end Chains

variable {L : Language} {x : VerbalSpine}

theorem splits_of_doSupport (h : (derive L x).DoSupport) : Splits L x := by
  by_contra hs
  simp only [Chains.DoSupport, derive, hs, ↓reduceIte] at h
  exact HeadChain.not_orphan_ofHeads _ _ _ h

/-- Do-support arises exactly where the chain of a strong verb splits. -/
theorem doSupport_iff (h : .V ∉ x.above) : (derive L x).DoSupport ↔ Splits L x := by
  refine ⟨splits_of_doSupport, fun hs ↦ ?_⟩
  have ht : (⟨x.above, (HeadChain.ofHeads .V x.above).mvalue⟩ : HeadChain).terminals =
      .V :: x.above := HeadChain.terminals_ofHeads .V x.above
  simp [Chains.DoSupport, derive, hs, HeadChain.Orphan, ht, h]

theorem not_doSupport_of_isAuxiliary (h : x.IsAuxiliary) : ¬ (derive L x).DoSupport :=
  fun hd ↦ absurd ((splits_of_doSupport hd).1.symm.trans h) (by decide)

theorem doSupport_iff_strong_of_ne_inSitu (h : .V ∉ x.above) (hne : x.above ≠ [])
    (hvp : x.vp ≠ .inSitu) (hv : x.verb = .VERB) :
    (derive L x).DoSupport ↔ .VERB ∈ L.strongVerbs := by
  simp [doSupport_iff h, Splits, hne, hvp, hv]

theorem doSupport_iff_of_intervenes (h : .V ∉ x.above) (hne : x.above ≠ [])
    (hvp : x.vp = .inSitu) (hi : x.Intervenes) (hv : x.verb = .VERB) :
    (derive L x).DoSupport ↔ .VERB ∈ L.strongVerbs ∧ L.splitByIntervention := by
  simp [doSupport_iff h, Splits, hne, hvp, hi, hv]

theorem finitePosition_declarative (hT : .T ∉ L.strongAt .VERB) :
    (derive L declarative).finitePosition = some (if .V ∈ L.strongAt .VERB then .V else .T) := by
  by_cases hV : Cat.V ∈ L.strongAt .VERB <;>
    simp [Chains.finitePosition, derive, Splits, declarative, VerbalSpine.Intervenes,
      HeadChain.pronounced, HeadChain.ofHeads, List.filter, hV, hT]

theorem danish_verb_second :
    (derive danish declarative).finitePosition = some .V ∧
      (derive danish inversion).finitePosition = some .C := by
  decide

theorem directionality_no_correlation :
    (derive english declarative).finitePosition = some .V ∧
      (derive monnese declarative).finitePosition = some .T ∧
      (derive english inversion).DoSupport ∧ (derive monnese inversion).DoSupport := by
  decide

theorem danish_do_support :
    (derive danish { toC with vp := .elided }).DoSupport ∧
      ¬ (derive danish inversion).DoSupport := by
  decide

theorem monnese_ellipsis :
    (derive monnese { declarative with vp := .elided }).DoSupport := by
  decide

theorem imperatives :
    (derive spanish toC).finitePosition = some .C ∧
      (derive vallader toC).finitePosition = some .T ∧
      (∀ L, (derive L toC).HasC ∧ ¬ (derive L declarative).HasC) := by
  refine ⟨by decide, by decide, fun L ↦ ?_⟩
  simp only [Chains.HasC, derive, Splits, toC, declarative, VerbalSpine.Intervenes]
  split_ifs <;> simp [HeadChain.terminals, HeadChain.ofHeads]

/-! ### Negative Merger -/

/-- Negative Merger, a postsyntactic rule, adjoins the M-value of the negation in the specifier
of ΣP to the M-value of a chain that contains Σ, outside what GenHM has built. -/
def HeadChain.negativeMerger (c : HeadChain) : HeadChain :=
  if .Pol ∈ c.positions then ⟨c.positions, c.mvalue * of .Neg⟩ else c

theorem HeadChain.terminals_negativeMerger {c : HeadChain} (h : .Pol ∈ c.positions) :
    c.negativeMerger.terminals = c.terminals ++ [.Neg] := by
  simp [negativeMerger, h, terminals]

/-- Negative Merger in a clause applies to each chain that contains Σ. -/
def Chains.negativeMerger (d : Chains) : Chains :=
  { d with verb := d.verb.negativeMerger, finite := d.finite.negativeMerger }

theorem Chains.doSupport_negativeMerger (d : Chains) :
    d.negativeMerger.DoSupport ↔ d.DoSupport := by
  simp only [DoSupport, negativeMerger, HeadChain.negativeMerger]
  split <;> simp [HeadChain.Orphan, HeadChain.terminals]

theorem Chains.finitePosition_negativeMerger (d : Chains) :
    d.negativeMerger.finitePosition = d.finitePosition := by
  simp only [finitePosition, negativeMerger, HeadChain.negativeMerger]
  split <;> rfl

theorem contracted_negation :
    let negated := (derive english (negation english)).negativeMerger
    let question : VerbalSpine := { above := [.Pol, .T, .C], specifiers := {.Pol, .T} }
    negated.finite.word english = some [[.dummy], [.finite], [.contracted]] ∧
      negated.verb.word english = some [[.stem]] ∧
      (derive english { negation english with verb := .AUX }).negativeMerger.finite.word english =
        some [[.finiteStem], [.finite], [.contracted]] ∧
      (derive english question).negativeMerger.finitePosition = some .C := by
  decide

theorem negation_outside_inflection :
    (HeadChain.ofHeads .V [.Neg, .T]).word english =
        some [[.stem], [.contracted], [.finite]] ∧
      (HeadChain.ofHeads .V [.Pol, .T]).negativeMerger.terminals =
        [.V, .Pol, .T, .Neg] := by
  decide

/-- The pieces that the segments of the paper's contracted forms write. -/
def segmentPieces : List (String × Piece) :=
  [("doe", .dummy), ("ha", .finiteStem), ("s", .finite), ("d", .finite), ("n't", .contracted)]

/-- The tag of the verb the paper takes a contracted form's verb to be. -/
def verbTag : Wordlist.Verb → UD.UPOS
  | .dummy => .VERB
  | .auxiliary => .AUX

theorem contracted_forms :
    ∀ a ∈ Wordlist.analyses, a.form.languageId = .english →
      ∃ verb ∈ a.verb.map verbTag,
        (derive english { negation english with verb }).negativeMerger.finite.word english =
          some (a.form.segments.map fun s ↦ (segmentPieces.lookup s).toList) := by
  decide +kernel

/-! ### The paper's examples -/

/-- The settings of a row's language, by Glottocode. -/
def languages : List (Glottocode × Language) :=
  [(.english, english), (.french, french), (.danish, danish), (.swedish, swedish),
    (.lombard, monnese), (.polish, polish), (.modernHebrew, hebrew), (.easternYiddish, yiddish),
    (.spanish, spanish), (.lowerEngadine, vallader)]

/-- The context each label of the rows names in a language. The elided verb-second clause is
subject-initial, and in the fronting ones the subject follows the finite verb. -/
def contexts (L : Language) : List (String × VerbalSpine) :=
  [("declarative", declarative), ("negation", negation L), ("verum", polarity),
    ("inversion", inversion), ("v2", inversion), ("subjectWh", toC),
    ("imperativeAff", toC), ("imperativeNeg", declarative),
    ("ellipsis", { declarative with vp := .elided }),
    ("ellipsisV2", { toC with vp := .elided }),
    ("fronting", { declarative with vp := .fronted }),
    ("frontingV2", { inversion with vp := .fronted })]

/-- The rows' labels for positions, verb forms and truth values. -/
def headLabels : List (String × Cat) := [("V", .V), ("T", .T), ("C", .C)]

@[inherit_doc headLabels]
def formLabels : List (String × List (List Piece)) :=
  [("finite", [[.finiteStem], [.finite]]), ("pseudoInfinitive", [[.finiteStem], [.infinitival]]),
    ("infinitive", [[.stem], [.infinitival]]), ("bare", [[.stem]])]

@[inherit_doc headLabels]
def boolLabels : List (String × Bool) := [("true", true), ("false", false)]

/-- A row that records `key` records under it the value `y`. -/
def Agrees {α : Type*} (r : Datum) (key : String) (table : List (String × α)) (y : Option α) :
    Prop :=
  r.feature? key = none ∨ ∃ x ∈ r.parse? key table, y = some x

instance {α : Type*} [DecidableEq α] (r : Datum) (key : String) (table : List (String × α))
    (y : Option α) : Decidable (Agrees r key table y) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The surface properties a row records are those of the chains. -/
def Chains.Matches (L : Language) (d : Chains) (r : Datum) : Prop :=
  Agrees r "finitePosition" headLabels d.finitePosition ∧
    Agrees r "doSupport" boolLabels ((d.finite.word L).map fun w ↦ decide ([.dummy] ∈ w)) ∧
    Agrees r "verbForm" formLabels (d.verb.word L) ∧
    Agrees r "imperativeForm" boolLabels (some (decide d.HasC)) ∧
    Agrees r "frontedForm" formLabels (d.fronted.bind (·.word L))

instance (L : Language) (d : Chains) (r : Datum) : Decidable (d.Matches L r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The settings of a row's language and the chains of its clause. -/
def derivation? (r : Datum) : Option (Language × Chains) := do
  let L ← r.byLanguage languages
  let cx ← r.parse? "context" (contexts L)
  let verb ← r.parse? "verbType" [("lexical", UD.UPOS.VERB), ("auxiliary", .AUX)]
  pure (L, derive L { cx with verb })

theorem rows_derived :
    ∀ r ∈ Examples.all, r.language ≠ .zimbabweanNdebele →
      ∃ p ∈ derivation? r, p.2.Matches p.1 r := by
  decide +kernel

theorem split_words :
    (derive english (negation english)).finite.word english = some [[.dummy], [.finite]] ∧
      (derive english (negation english)).verb.word english = some [[.stem]] ∧
      (derive monnese inversion).verb.word monnese = some [[.stem], [.infinitival]] := by
  decide

/-! ### Pollock's paradigm -/

/-- The settings of the languages Pollock compares. -/
def ofPollock : Pollock1989.Language → Language
  | .french => french
  | .english => english

theorem pollock_finite (l : Pollock1989.Language) (v : Pollock1989.Verb) :
    let verb : UD.UPOS := match v with | .lexical => .VERB | .auxiliary => .AUX
    ((derive (ofPollock l) { declarative with verb }).finitePosition = some .T ↔
        Pollock1989.top ⟨l, true⟩ v = .tense) ∧
      ((derive (ofPollock l) { negation (ofPollock l) with verb }).DoSupport ↔
        Pollock1989.NeedsDo ⟨l, true⟩ v) := by
  cases l <;> cases v <;> decide

/-! ### Ndebele relative prefixes -/

/-- The chain of an Ndebele relative clause holds T, a null C, the augment in D and the linker. -/
def relative : HeadChain := .ofHeads .T [.C, .D, .Lnk]

theorem relative_low :
    relative.pronounced ndebele.strong = some .T ∧ ∀ r ∈ Examples.all,
      Agrees r "relPrefixPosition" headLabels (relative.pronounced ndebele.strong) := by
  decide +kernel

/-- Where two vowels meet, identical vowels merge, /a/ coalesces with a following /i/ into /e/
and with a following /u/ into /o/, and /e/ elides before a vowel. -/
def resolve (j : Hiatus.Juncture) : List Segment :=
  if j.v1 = j.v2 ∨ j.v1 = Ndebele.e then j.elideV1
  else if j.v1 = Ndebele.a ∧ j.v2 = Ndebele.i then j.coalesce Ndebele.e
  else if j.v1 = Ndebele.a ∧ j.v2 = Ndebele.u then j.coalesce Ndebele.o
  else j.input

/-- Two exponents joined, with the hiatus between them resolved if there is one. -/
def join (x y : List Segment) : List Segment :=
  (Hiatus.Juncture.ofForms? x y).elim (x ++ y) resolve

/-- The exponent of a constituent of a complex head of prefixes. -/
structure Exponent where
  segments : List Segment
  deriving DecidableEq

/-- The exponent of a complex head is the product of the exponents of its two constituents,
lower first: the higher one is prefixed to the lower, and the hiatus between them resolved.
Cyclic spell-out, each constituent before the one containing it, is thus the homomorphism of
magmas `FreeMagma.lift e` that extends the exponents `e` of the terminals. -/
instance : Mul Exponent := ⟨fun x y ↦ ⟨join y.segments x.segments⟩⟩

/-- The segments the letters of the prefix table write. -/
def letters : List (Char × Segment) :=
  [('a', Ndebele.a), ('e', Ndebele.e), ('i', Ndebele.i), ('o', Ndebele.o), ('u', Ndebele.u),
    ('s', Ndebele.s), ('l', Ndebele.l)]

/-- A string of the prefix table as segments. -/
def transcribe? : List Char → Option (List Segment)
  | [] => some []
  | c :: cs => do pure ((← letters.lookup c) :: (← transcribe? cs))

/-- The exponents a row of the prefix table gives the heads of the relative prefix. -/
def exponents? (a : Wordlist.Analysis) : Option (Cat → Exponent) := do
  let lnk ← transcribe? (← a.lnk).toList
  let d ← transcribe? (← a.d).toList
  let t ← transcribe? (← a.t).toList
  pure fun | .Lnk => ⟨lnk⟩ | .D => ⟨d⟩ | .T => ⟨t⟩ | _ => ⟨[]⟩

theorem relative_prefixes :
    ∀ a ∈ Wordlist.analyses, a.form.languageId = .zimbabweanNdebele → ∃ e ∈ exponents? a,
      some (lift e relative.mvalue).segments = transcribe? a.form.form.toList ∧
        Hiatus.Free (lift e relative.mvalue).segments ∧
        ¬ Hiatus.Free (relative.terminals.reverse.flatMap fun h ↦ (e h).segments) := by
  decide +kernel

/-- The same terminals in the same order with the opposite bracketing, the linker innermost. -/
def nonMirror : FreeMagma Cat := of .T * (of .C * (of .D * of .Lnk))

/-- In class 9 the Mirror-obeying complex head spells out as the attested *e-* and the opposite
bracketing of the same terminals as *i-*. -/
theorem mirror_class9 :
    (FreeMagma.lift FreeMonoid.of nonMirror).toList = relative.terminals ∧
      ∃ e ∈ exponents? Wordlist.f_19_cl9.analysis,
        (lift e relative.mvalue).segments = [Ndebele.e] ∧
          (lift e nonMirror).segments = [Ndebele.i] := by
  decide +kernel

/-- Coalescence is not associative. An associative juncture rule would spell out every
bracketing of the same terminals alike, and the two bracketings of the class 9 prefix come out
differently, /i/ and /i/ merging before /a/ coalesces with them in one and after in the other. -/
theorem mul_not_assoc : ¬ ∀ x y z : Exponent, x * y * z = x * (y * z) := fun h ↦ by
  let _ : Semigroup Exponent := { (inferInstance : Mul Exponent) with mul_assoc := h }
  obtain ⟨hterm, hspell⟩ := mirror_class9
  obtain ⟨e, -, he, hi⟩ := hspell
  have := congrArg Exponent.segments
    (lift_eq_lift_of_lift_of_eq e (FreeMonoid.toList.injective hterm))
  exact absurd (he.symm.trans (this.symm.trans hi)) (by decide)

/-! ### Amalgamation -/

section Amalgamation

open HarizanovGribanova2019

theorem amalgamation_bracketing (x y z : Cat) :
    amalgamateSpine [.single z none, .single y (some .lowering), .single x (some .lowering)] =
        some [⟨z, (HeadChain.ofHeads z [y, x]).mvalue, none⟩] ∧
      amalgamateSpine [.single z none, .single y (some .raising), .single x (some .lowering)] =
        some [⟨z, of z * (of y * of x), none⟩] :=
  ⟨rfl, rfl⟩

theorem amalgamation_class9 :
    amalgamateSpine [.single .T none, .single .C (some .lowering), .single .D (some .lowering),
        .single .Lnk (some .lowering)] = some [⟨.T, relative.mvalue, none⟩] ∧
      ∃ a, amalgamateSpine [.single .T none, .single .C (some .lowering),
          .single .D (some .raising), .single .Lnk (some .lowering)] = some [a] ∧
        a.members = relative.terminals ∧ a.complex ≠ relative.mvalue ∧
        ∃ e ∈ exponents? Wordlist.f_19_cl9.analysis, (lift e a.complex).segments = [Ndebele.i] :=
  ⟨rfl, _, rfl, rfl, by decide, by decide +kernel⟩

theorem amalgamation_at_pronounced {lo hi rest : List Cat} {s b : Cat}
    (h : lo ++ s :: hi = b :: rest) (hnd : (b :: rest).Nodup) :
    (HeadChain.ofHeads b rest).pronounced {s} = some s ∧
      amalgamateSpine (lo.map (.single · (some .raising)) ++ .single s none ::
          hi.map (.single · (some .lowering))) =
        some [⟨s, (HeadChain.ofHeads b rest).mvalue, none⟩] := by
  refine ⟨?_, amalgamateSpine_raising_lowering h⟩
  have hs : s ∉ lo ++ hi := (List.nodup_cons.mp (List.nodup_middle.mp (h ▸ hnd))).1
  have h₁ : lo.filter (· = s) = [] :=
    List.filter_eq_nil_iff.mpr fun y hy ↦ by simpa using fun h : y = s ↦ hs (by simp [← h, hy])
  have h₂ : hi.filter (· = s) = [] :=
    List.filter_eq_nil_iff.mpr fun y hy ↦ by simpa using fun h : y = s ↦ hs (by simp [← h, hy])
  simp [HeadChain.pronounced, HeadChain.ofHeads, ← h, List.filter_append, h₁, h₂]

theorem amalgamation_keeps_verb_site (m : Cat → Option Direction)
    {out out' : List (Amalgam Cat)} {a a' : Amalgam Cat}
    (h : amalgamateSpine ([Cat.V, .T].map fun x ↦ .single x (m x)) = some out)
    (h' : amalgamateSpine ([Cat.V, .T, .C].map fun x ↦ .single x (m x)) = some out')
    (ha : a ∈ out) (ha' : a' ∈ out') (hV : .V ∈ a.members) (hV' : .V ∈ a'.members) :
    a'.site = a.site :=
  site_eq_of_append (extra := [Amalgam.single Cat.C (m .C)]) h h'
    (by simp [Amalgam.members, Amalgam.single]) ha ha' hV hV'

theorem doSupport_iff_intervener {L : Language} (hV : .VERB ∈ L.strongVerbs)
    (hs : L.splitByIntervention) :
    inversion.above = toC.above ∧ (derive L inversion).DoSupport ∧
      ¬ (derive L toC).DoSupport := by
  refine ⟨rfl, (doSupport_iff (by decide)).mpr ⟨rfl, hV, by decide, .inl ⟨hs, by decide⟩⟩,
    fun h ↦ ?_⟩
  have := splits_of_doSupport h
  simp [Splits, toC, VerbalSpine.Intervenes] at this

/-- The settings and context of a French or Danish clause among the verb-placement examples of
the amalgamation study. -/
def clauseOf (r : Datum) : Option (Language × VerbalSpine) :=
  let cx (L : Language) : VerbalSpine :=
    if r.feature? "diagnostic" = some "negation" then negation L else declarative
  List.lookup (r.language, r.feature? "clause")
    [((.french, none), (french, cx french)), ((.danish, some "embedded"), (danish, cx danish)),
      ((.danish, some "root"), (danish, toC))]

/-- The finite word of a clause whose verb has the tag is pronounced in T or above. -/
def PlacedHigh (L : Language) (x : VerbalSpine) (verb : UD.UPOS) : Prop :=
  (derive L { x with verb }).finitePosition ∈ [some .T, some .C]

instance (L : Language) (x : VerbalSpine) (verb : UD.UPOS) : Decidable (PlacedHigh L x verb) :=
  inferInstanceAs (Decidable (_ ∈ _))

theorem amalgamation_rows :
    ∀ r ∈ HarizanovGribanova2019.Examples.all,
      r.feature? "phenomenon" = some "finiteVerbPlacement" →
      r.feature? "diagnostic" ≠ some "coordination" → r.language ≠ .russian →
        ∃ p ∈ clauseOf r, ∃ b ∈ r.parse? "verbPrecedes" boolLabels, ∀ verb ∈ [UD.UPOS.VERB, .AUX],
          (r.judgment = .acceptable ↔ (b = true ↔ PlacedHigh p.1 p.2 verb)) := by
  decide +kernel

end Amalgamation

end ArregiPietraszko2021
