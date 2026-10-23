module

public import Linglib.Data.Examples.Stassen2000
public import Linglib.Fragments.English.Adpositions
public import Linglib.Fragments.English.Coordination
public import Linglib.Fragments.Farsi.Adpositions
public import Linglib.Fragments.Farsi.Coordination
public import Linglib.Fragments.Finnish.Coordination
public import Linglib.Fragments.Hausa.Adpositions
public import Linglib.Fragments.Hausa.Coordination
public import Linglib.Fragments.Japanese.Adpositions
public import Linglib.Fragments.Japanese.Coordination
public import Linglib.Fragments.Korean.Coordination
public import Linglib.Fragments.Latin.Coordination
public import Linglib.Fragments.Turkish.Coordination
public import Linglib.Fragments.Yakut.Case
public import Linglib.Fragments.Yakut.Coordination
public import Linglib.Syntax.WordOrder
public import Mathlib.Data.Finset.Grade

/-!
# Stassen (2000): AND-languages and WITH-languages

This file formalizes Stassen's typology of noun phrase conjunction. Its examples of the
coordinate strategy show where the coordinators of a construction stand, and the coordinate and
the comitative strategy contrast in four features whose sets form the Boolean lattice
`Finset Feature`. A language is an AND-language when one of its encodings has every feature
relevant to it, and a WITH-language otherwise. Pattern schemes place the subject and the
comitative phrase by the basic word order.

## Main results

* `coAB_not_mem_patterns`, `postpositive_of_not_medial`: no example preposes a lone
  coordinator on the first noun phrase, and the overt strategies other than a medial connective
  postpose their coordinators (§3).
* `attestations_side`: the Fragment coordinators of the examples stand where their morphs attach.
* `Language.isAnd_iff_top_mem`, `Language.not_isAnd_of_forall_notMem`: AND- and WITH-languages.
* `Language.relevant_le_insert_iff`: differentiating the linker of a hybrid gives every relevant
  feature exactly when the hybrid is the most advanced one.
* `english_and_not_isAlsoComitative`, `persian_not_isAlsoComitative`,
  `hausa_da_isAlsoComitative`, `japanese_to_isAlsoComitative`, `yakut_lin_isAlsoComitative`:
  whether the linker is the comitative marker.
* `adjacent_scheme_iff`, `shift_scheme_svo`: contiguity in the pattern schemes and the shift.

## Implementation notes

* The examples are those of §3, (9)–(53), in `Data/Examples/Stassen2000.json`. A medial
  connective, which the paper leaves in construction with either noun phrase, admits both
  patterns.
* Plural agreement is relevant only where verbs agree with their subject (`Language.relevant`),
  since the paper's AND-languages include languages without verb agreement.
* The schemes (107), (123) and (124) put the comitative phrase where the object stands.
* The correlations of cased and tensed languages with AND-status are stated by the paper without
  a cross-tabulation and are not formalized.

## TODO

* The word-order correlations (54) for the coordinate strategy, and the claim that a language
  postposing a lone coordinator typically also has polysyndeton (p. 14).
* Verb-final and verb-initial WITH-languages without agreement, (123a) and (124a), which can mark
  the new constituent neither by position nor by agreement, and the doubled comitative of (125).

## References

* [stassen-2000]
-/

@[expose] public section

namespace Stassen2000

open WordOrder

/-! ### The coordinate strategy, §3 -/

open Morphology (Morph)
open Coordinator (Pattern)

/-- A medial connective, a single linking morpheme between the two noun phrases, is in
construction with the second, A co-B, or with the first, A-co B, as each language decides
(p. 10). -/
def medial : Finset Pattern := {(none, some .before), (some .after, none)}

/-- The patterns the examples' labels admit, A-co B written `a'co_b` as Haspelmath writes it. -/
def patternLabels : List (String × Finset Pattern) :=
  [("asyndetic", {(none, none)}), ("medial", medial), ("a'co_b'co", {(some .after, some .after)}),
    ("a'co_b", {(some .after, none)}), ("a_b'co", {(none, some .after)})]

/-- The patterns an example admits. -/
def patterns (d : Datum) : Finset Pattern := (d.parse? "pattern" patternLabels).getD ∅

theorem patterns_nonempty : ∀ d ∈ Examples.all, (patterns d).Nonempty := by decide

/-- Monosyndetic preposing on the first noun phrase, the scheme AND-NP NP, is attested in no
example, as in none of the sample (p. 15). -/
theorem coAB_not_mem_patterns : ∀ d ∈ Examples.all, (some .before, none) ∉ patterns d := by
  decide

/-- The overt strategies other than medial monosyndeton postpose or suffix their connectives
(p. 12): in an example without a medial connective, no coordinator precedes its noun phrase. -/
theorem postpositive_of_not_medial : ∀ d ∈ Examples.all, patterns d ≠ medial →
    ∀ p ∈ patterns d, p.1 ≠ some .before ∧ p.2 ≠ some .before := by
  decide

/-- An example whose coordinator has a Fragment entry. -/
structure Attestation where
  datum : Datum
  coordinator : Coordinator

open Examples in
/-- The examples whose coordinators have Fragment entries: Persian *va*, Mahootian's *væ*, and
*-o*, Finnish *ja*, Turkish *ve*, Korean *-hago* and Latin *-que*. -/
def attestations : List Attestation :=
  [⟨ex20b, Farsi.Coordination.va⟩, ⟨ex22, Finnish.Coordination.ja⟩,
    ⟨ex27, Turkish.Coordination.ve⟩, ⟨ex45, Korean.Coordination.hago⟩,
    ⟨ex49, Farsi.Coordination.o⟩, ⟨ex51, Latin.Coordination.que⟩]

theorem attestations_conjunctive :
    ∀ a ∈ attestations, a.coordinator.role = .conjunctive := by
  decide

theorem attestations_side : ∀ a ∈ attestations, ∀ p ∈ patterns a.datum,
    ∀ s ∈ a.coordinator.morph.kind.side?, ∀ t ∈ [p.1, p.2], t ≠ none → t = some s := by
  decide

/-! ### Encodings -/

/-- The features of the coordinate strategy, the paper's (83), each opposed to a feature of the
comitative strategy. The two NPs have the same structural rank, form a constituent, govern dual
or plural agreement, and are linked by an item distinct from the comitative marker. An encoding
is the `Finset` of the features it has. -/
inductive Feature
  | equalRank
  | constituent
  | pluralAgreement
  | distinctMarker
  deriving DecidableEq, Repr, Fintype

/-! ### AND-languages and WITH-languages -/

/-- A language records whether its verbs agree with their subject, and its encodings of the
domain. -/
structure Language where
  /-- The verbs agree with their subject in person, number and gender. -/
  Agrees : Prop
  [decidableAgrees : Decidable Agrees]
  /-- The encodings of noun phrase conjunction. -/
  encodings : Finset (Finset Feature)

attribute [instance] Language.decidableAgrees

namespace Language

variable (l : Language)

/-- The coordinate features relevant to the language, plural agreement only where its verbs
agree. -/
def relevant : Finset Feature := if l.Agrees then ⊤ else {.pluralAgreement}ᶜ

/-- An AND-language has an encoding with every relevant coordinate feature. -/
def IsAnd : Prop := ∃ e ∈ l.encodings, l.relevant ≤ e

instance : Decidable l.IsAnd := inferInstanceAs (Decidable (∃ e ∈ _, _))

variable {l}

theorem relevant_of_agrees (h : l.Agrees) : l.relevant = ⊤ := by simp [relevant, h]

theorem isAnd_iff_top_mem (h : l.Agrees) : l.IsAnd ↔ ⊤ ∈ l.encodings := by
  simp [IsAnd, relevant_of_agrees h]

theorem distinctMarker_mem_relevant : .distinctMarker ∈ l.relevant := by
  unfold relevant; split_ifs <;> simp

theorem not_isAnd_of_forall_notMem (h : ∀ e ∈ l.encodings, .distinctMarker ∉ e) : ¬ l.IsAnd :=
  fun ⟨e, he, hle⟩ ↦ h e he (hle distinctMarker_mem_relevant)

variable (l) in
theorem erase_distinctMarker_covBy : l.relevant.erase .distinctMarker ⋖ l.relevant :=
  Finset.erase_covBy distinctMarker_mem_relevant

theorem relevant_le_insert_iff {e : Finset Feature} (he : e ≤ l.relevant)
    (hm : .distinctMarker ∉ e) :
    l.relevant ≤ insert .distinctMarker e ↔ e = l.relevant.erase .distinctMarker := by
  rw [Finset.subset_insert_iff]
  exact ⟨fun h ↦ (Finset.subset_erase.2 ⟨he, hm⟩).antisymm h, fun h ↦ h.ge⟩

/-- Without verb agreement, an encoding lacking only plural agreement makes an AND-language, as
the paper's AND-languages without agreement are; where verbs agree, the same encodings make a
WITH-language. -/
example : ({ Agrees := False, encodings := {⊥, {.pluralAgreement}ᶜ} } : Language).IsAnd ∧
    ¬ ({ Agrees := True, encodings := {⊥, {.pluralAgreement}ᶜ} } : Language).IsAnd := by
  decide

end Language

/-! ### The linker in the Fragments -/

theorem english_and_not_isAlsoComitative :
    ¬ English.Coordination.and_.IsAlsoComitative English.Adpositions.with_.morphs
      English.Adpositions.with_.functions := by
  decide

theorem persian_not_isAlsoComitative : ∀ c ∈ [Farsi.Coordination.va, Farsi.Coordination.o],
    ¬ c.IsAlsoComitative Farsi.Adpositions.ba.morphs Farsi.Adpositions.ba.functions := by
  decide

/-- Hausa *dà* 'and' is the comitative preposition *dà* 'with', (109). -/
theorem hausa_da_isAlsoComitative :
    Hausa.Coordination.da.IsAlsoComitative Hausa.Adpositions.da.morphs
      Hausa.Adpositions.da.functions := by
  decide

theorem japanese_to_isAlsoComitative :
    Japanese.Coordination.to_.IsAlsoComitative Japanese.Adpositions.«to».morphs
      Japanese.Adpositions.«to».functions := by
  decide

theorem yakut_lin_isAlsoComitative :
    Yakut.Coordination.lin.IsAlsoComitative (Yakut.Case.exponents .com)
      {Yakut.Case.label .com} := by
  decide

/-! ### Pattern schemes -/

/-- The elements of a pattern scheme with an intransitive predicate are the subject, the verb, and
the comitative phrase. -/
inductive Slot
  | subject
  | verb
  | comitative
  deriving DecidableEq, Repr, Fintype

/-- The slots of a scheme as the constituents of a clause, the comitative phrase in the object's
position. -/
def Slot.equivConstituent : Slot ≃ Constituent where
  toFun | .subject => .subject | .verb => .verb | .comitative => .object
  invFun | .subject => .subject | .verb => .verb | .object => .comitative
  left_inv := by decide
  right_inv := by decide

/-- The pattern scheme of a basic word order, the paper's (107), (123) and (124). The comitative
phrase stands in the canonical position of adverbial phrases, which in these schemes is the
object's. -/
def scheme (a : Arrangement Constituent 3) : Arrangement Slot 3 := Slot.equivConstituent.trans a

theorem adjacent_scheme_iff (a : Arrangement Constituent 3) :
    (scheme a).Adjacent .subject .comitative ↔ ¬ a.IsMedial .verb :=
  Arrangement.adjacent_iff_not_isMedial (z := Slot.verb) (by decide) (by decide) (by decide)

/-- In an SVO language the verb separates the two NPs, (107). -/
theorem not_adjacent_scheme_svo : ¬ (scheme .svo).Adjacent .subject .comitative := by decide

/-- SOV and VSO schemes are contiguous already, (123) and (124). -/
theorem adjacent_scheme_sov : (scheme .sov).Adjacent .subject .comitative := by decide

theorem adjacent_scheme_vso : (scheme .vso).Adjacent .subject .comitative := by decide

/-- The shift of the comitative phrase, the paper's (108), is the transposition of the verb and
the comitative phrase, which moves the comitative phrase across a medial verb. -/
def shift (s : Arrangement Slot 3) : Arrangement Slot 3 := (Equiv.swap .verb .comitative).trans s

theorem adjacent_shift {s : Arrangement Slot 3} (h : s.IsMedial .verb) :
    (shift s).Adjacent .subject .comitative := by
  refine (Arrangement.adjacent_iff_not_isMedial (z := Slot.verb) (by decide) (by decide)
    (by decide)).2 ?_
  have := s.injective.ne (show Slot.comitative ≠ .verb by decide)
  have := (s .comitative).isLt
  simp only [Arrangement.IsMedial, Arrangement.IsEnd, shift, Equiv.trans_apply,
    Equiv.swap_apply_left] at h this ⊢
  omega

/-- The shifted SVO scheme is the SOV scheme: (108) has the order of (123). -/
theorem shift_scheme_svo : shift (scheme .svo) = scheme .sov := Equiv.ext (by decide)

end Stassen2000
