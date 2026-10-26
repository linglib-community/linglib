module

public import Linglib.Syntax.Clause.Chaining
public import Linglib.Fragments.Nungon.Clause
public import Linglib.Fragments.Manambu.Clause
public import Linglib.Fragments.Korean.Clause
public import Linglib.Fragments.Turkish.Clause

/-!
# Sarvasy & Aikhenvald (2025): Clause Chaining in the Languages of the World

This file formalizes the typological generalizations of the volume's introduction over the
clause-chaining systems of four of its languages. A clause chain is a sequence of medial
clauses, formally dependent and underspecified for inflectional categories, closed by one
independent clause, and the introduction surveys the parameters along which chaining varies:
the switch-reference marking of many medial-final languages, the categories medial verbs
retain, the relations medial forms encode, the two bridging constructions and the
non-canonical uses of medial clauses. The sample (`Language`) is Nungon and Manambu, whose
chapters describe switch-reference systems, and Korean and Turkish, which chain without
switch-reference; each language's medial forms are its fragment's carrier (`Language.Forms`),
and its retention profile (`Language.medialMorph`), bridging constructions
(`Language.bridging`) and stand-alone medial clauses (`Language.MedialStandsAlone`) are read
off the forms where the forms decide them and are the chapters' reports otherwise. The
generalizations proved are that same-subject medial forms leave the subject unindexed while
different-subject forms index it (`ss_forms_lack_subject_marking`), that Manambu's
switch-reference markers each encode a temporal or logical relation whereas Nungon's mark
subject continuity alone, the temporal relation coming from a switch-reference-neutral
construction (`relations_fused_with_sr`), that the chain's tense comes from the final verb in
the two Papuan languages while Korean admits tense before some medial suffixes
(`tense_from_final_verb`), that Turkish negates medial clauses individually
(`negated_individually`), that the medial verbs of both are converbs (`converb_form`), and that in
the sample switch-reference goes with the loss or reduction of medial tense (`sr_and_tense`).

## Implementation notes

The Korean and Turkish inventories come from reference grammars rather than the volume, whose
introduction discusses both languages; the volume's Turkish suffix list adds the two converbial
subordinators on a doubled verb, which the fragment records outside its carrier, as
`Turkish.DoubledConverb`. Turkish mood counts the modality markers of position 3, which only the
converbs on a tensed stem admit; the possibility suffixes of positions 1 and 2 may precede every
converb. Nungon's medial polarity is the earlier formalization's value, which chapter 7 does not
settle. Ku Waru and Korowai, formerly in the sample, are dropped: the former has no chapter in the
volume and the latter's switch-reference system was misrecorded as tracking several arguments.

## References

* [sarvasy-aikhenvald-2025]
* [sarvasy-2017]
* [aikhenvald-2025]
* [aikhenvald-2008]
* [sohn-1994]
* [sohn-1999]
* [goksel-kerslake-2005]
-/

@[expose] public section

namespace SarvasyAikhenvald2025

open Clause.Chaining

/-! ### The sample -/

/-- The four languages. -/
inductive Language where
  | nungon
  | manambu
  | korean
  | turkish
  deriving DecidableEq, Repr, Fintype

namespace Language

/-- The medial forms of a language, its fragment's carrier. -/
def Forms : Language → Type
  | nungon => Nungon.Medial
  | manambu => Manambu.MedialMarker
  | korean => Korean.Converb
  | turkish => Turkish.Converb

instance : (L : Language) → Fintype L.Forms
  | nungon => inferInstanceAs (Fintype Nungon.Medial)
  | manambu => inferInstanceAs (Fintype Manambu.MedialMarker)
  | korean => inferInstanceAs (Fintype Korean.Converb)
  | turkish => inferInstanceAs (Fintype Turkish.Converb)

instance : (L : Language) → MedialForm L.Forms
  | nungon => inferInstanceAs (MedialForm Nungon.Medial)
  | manambu => inferInstanceAs (MedialForm Manambu.MedialMarker)
  | korean => inferInstanceAs (MedialForm Korean.Converb)
  | turkish => inferInstanceAs (MedialForm Turkish.Converb)

/-- The tense medial verbs retain, which is none in Nungon, relative tense fused with the
marking in Manambu, and tense before the converbs that admit it in Korean and in Turkish. -/
def tense : Language → CategoryRetention
  | nungon => .absent
  | manambu => .restricted
  | korean => .ofPred Korean.Converb.AllowsTense
  | turkish => .ofPred Turkish.Converb.Tensed

/-- The mood medial verbs retain, which is none in the two Papuan languages, in Korean the
modal before the suffixes that admit it, and in Turkish the modality markers before the
converbs on a tensed stem. -/
def mood : Language → CategoryRetention
  | nungon | manambu => .absent
  | korean => .ofPred Korean.Converb.AllowsModal
  | turkish => .ofPred Turkish.Converb.Tensed

/-- Independent negation of the medial clause, which in Manambu and Turkish is as far as the
forms admit it, in Korean the negative adverbs and negative verb of a medial clause, and in
Nungon the earlier formalization's value. -/
def polarity : Language → CategoryRetention
  | nungon | korean => .full
  | manambu => .ofPred Manambu.MedialMarker.Negatable
  | turkish => .ofPred Turkish.Converb.Negatable

/-- The aspect medial verbs retain, which is none in Nungon, in Manambu aspect only before the
causal marker, which takes the tensed cross-referencing of a main verb, in Korean the perfect
before the suffixes that admit it, and in Turkish the aspect markers before the converbs on a
tensed stem. -/
def aspect : Language → CategoryRetention
  | nungon => .absent
  | manambu => .ofPred fun m : Manambu.MedialMarker ↦ m.inflection = .fullyInflected
  | korean => .ofPred Korean.Converb.AllowsTense
  | turkish => .ofPred Turkish.Converb.Tensed

/-- The retention profile of a language's medial verbs, agreement read off its forms. -/
def medialMorph (L : Language) : MedialMorphProfile
  | .tense => L.tense
  | .agreement => MedialForm.agreement L.Forms
  | .mood => L.mood
  | .polarity => L.polarity
  | .aspect => L.aspect

/-- The bridging constructions attested, both in the two Papuan languages and neither in
Korean and Turkish. -/
def bridging : Language → Finset BridgingType
  | nungon | manambu => {.recapitulative, .summary}
  | korean | turkish => ∅

/-- Medial clauses occur on their own in Nungon and Korean, in Manambu with the forms that
do, and not in Turkish. -/
def MedialStandsAlone : Language → Prop
  | nungon | korean => True
  | manambu => ∃ m : Manambu.MedialMarker, m.StandsAlone
  | turkish => False

end Language

/-! ### The generalizations -/

theorem ss_forms_lack_subject_marking :
    MedialForm.SSUnmarked Nungon.Medial ∧ MedialForm.SSUnmarked Manambu.MedialMarker ∧
      MedialForm.agreement Nungon.Medial = .restricted ∧
      MedialForm.agreement Manambu.MedialMarker = .restricted := by
  decide

theorem relations_fused_with_sr :
    (∀ m : Manambu.MedialMarker, m.sr ≠ none → m.relations.Nonempty) ∧
      (∃ r ∈ MedialForm.relationsMarked Manambu.MedialMarker, ¬ r.Temporal) ∧
      (∀ m : Nungon.Medial, m.sr ≠ none → m.relations = ∅) ∧
      ∃ m : Nungon.Medial, m.sr = none ∧ m.relations.Nonempty := by
  decide

theorem tense_from_final_verb :
    Language.tense .nungon = .absent ∧ Language.tense .manambu = .restricted ∧
      Language.tense .korean = .restricted := by
  decide

theorem negated_individually : Language.polarity .turkish = .full := by decide

theorem converb_form :
    (Language.medialMorph .korean).udVerbForm = .Conv ∧
      (Language.medialMorph .turkish).udVerbForm = .Conv ∧
      (∀ c : Korean.Converb, c.verbForm = (Language.medialMorph .korean).udVerbForm) ∧
      ∀ c : Turkish.Converb, c.verbForm = (Language.medialMorph .turkish).udVerbForm := by
  decide

theorem sr_and_tense : ∀ L : Language, MedialForm.HasSR L.Forms → L.tense ≠ .full := by
  decide

end SarvasyAikhenvald2025
