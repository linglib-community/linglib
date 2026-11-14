module

public import Mathlib.Data.Finset.Option
public import Mathlib.Order.UpperLower.Basic
public import Linglib.Fragments.Arabic.ModernStandard.Case
public import Linglib.Fragments.Dargwa.Tanti.Case
public import Linglib.Fragments.Finnish.Case
public import Linglib.Fragments.Georgian.Case
public import Linglib.Fragments.German.Basel.Case
public import Linglib.Fragments.German.Case
public import Linglib.Fragments.Greek.Ancient.Case
public import Linglib.Fragments.Greek.StandardModern.Case
public import Linglib.Fragments.HindiUrdu.Case
public import Linglib.Fragments.Hungarian.Case
public import Linglib.Fragments.Icelandic.Case
public import Linglib.Fragments.Latin.Case
public import Linglib.Fragments.Mongolian.Case
public import Linglib.Fragments.Slavic.Belarusian.Case
public import Linglib.Fragments.Slavic.Cassubian.Case
public import Linglib.Fragments.Slavic.Czech.Case
public import Linglib.Fragments.Slavic.Polish.Case
public import Linglib.Fragments.Slavic.Russian.Case
public import Linglib.Fragments.Slavic.Serbian.Case
public import Linglib.Fragments.Slavic.Slovak.Case
public import Linglib.Fragments.Slavic.Slovenian.Case
public import Linglib.Fragments.Slavic.Sorbian.Case
public import Linglib.Fragments.Slavic.Ukrainian.Case
public import Linglib.Fragments.Tamil.Case
public import Linglib.Fragments.Telugu.Case
public import Linglib.Fragments.Turkish.Case
public import Linglib.Fragments.Yakut.Case

/-!
# Blake (1994): Case

Blake surveys inflectional case systems from two members to a dozen and finds that they tend to
be built up in one order: nominative, then accusative or ergative, genitive, dative, locative,
ablative or instrumental, and then the rest. A language with a case at some position usually has
a case at every position to its left, so that [systems built in this order lie along one line of
growth](##Conforms.total), as do [the systems he cites for the successive
stages](##systems_conform). The vocative is set aside, since it marks no relation of a dependent
to a head.

Blake stresses that this is a tendency and not an implicational universal. Bound pronouns can do
the work of a higher case, which leaves a gap: Nanai has no genitive, and [Warndarang lacks the
genitive, the dative and a second core case](##gaps_warndarang). And a case of several functions
bears one label, which leaves an apparent gap at the position of a function it is not labelled
for: [such a gap is a position that the functions fill](##gaps_subset_of_conforms). The lowest
case of a small system is an elsewhere case of this kind. The Latin ablative merges an older
ablative, instrumental and locative, its label in Blake's words somewhat arbitrary, and [the
locative position that the Latin labels skip is filled by its
functions](##gaps_latin_labels_subset).

## Implementation notes

The absolutive is placed with the nominative, since Blake calls the unmarked case of an ergative
system nominative. A local case is placed by its direction, the cases of rest with the locative
and the cases of source with the ablative. The purposive is not a `Case` value: Warndarang is
given without its purposive, which would sit with its allative past the ablative and instrumental,
and Toda and Irula, which add a purposive to the cases of Tamil, are not listed. The text was
checked in the second edition ([blake-2001]).

## TODO

Blake observes that no language has both a case for A and a case for P unless it has a fourth
case. This is not stated: the one fragment with both an ergative and an accusative,
`NezPerce.Case`, records the three cases of the relative pronoun only.

## References

* [blake-1994]
* [blake-2001]
* [stachowski-menz-1998]
* [suter-1992]
-/

@[expose] public section

namespace Blake1994

/-! ### The hierarchy -/

/-- The positions of the hierarchy, from the nominative down. Accusative and ergative share a
position, as do ablative and instrumental, and the cases past them all share the last. -/
inductive Position where
  | nom
  | accErg
  | gen
  | dat
  | loc
  | ablInst
  | other
  deriving DecidableEq, Fintype, Repr

/-- The place of a position in the sequence. -/
def Position.rank : Position → Fin 7
  | .nom => 0
  | .accErg => 1
  | .gen => 2
  | .dat => 3
  | .loc => 4
  | .ablInst => 5
  | .other => 6

theorem Position.rank_injective : Function.Injective Position.rank := by decide

instance : LinearOrder Position := LinearOrder.lift' Position.rank Position.rank_injective

/-- The position of a case. A local case goes by its direction, a case of rest with the locative
and a case of source with the ablative, and the vocative has no position. The oblique of a
two-case system is at the second position, the case that is likely to cover P or A but for which
Blake finds the label oblique more appropriate (p. 156). -/
def position : Case → Option Position
  | .nom | .abs => some .nom
  | .acc | .erg | .obl => some .accErg
  | .gen => some .gen
  | .dat => some .dat
  | .inst => some .ablInst
  | .voc => none
  | c =>
    match c.dirOf with
    | some .place => some .loc
    | some .source => some .ablInst
    | _ => some .other

/-- The positions an inventory fills. -/
def positions (inv : Finset Case) : Finset Position := inv.biUnion fun c ↦ (position c).toFinset

/-- An inventory conforms to the hierarchy when it fills every position to the left of each
position it fills. -/
def Conforms (inv : Finset Case) : Prop := IsLowerSet (positions inv : Set Position)

/-- The gaps of an inventory are the unfilled positions to the left of a filled one. -/
def gaps (inv : Finset Case) : Finset Position :=
  Finset.univ.filter fun q ↦ q ∉ positions inv ∧ ∃ p ∈ positions inv, q < p

variable {inv inv' : Finset Case} {p q : Position}

theorem mem_positions : p ∈ positions inv ↔ ∃ c ∈ inv, position c = some p := by
  simp [positions, Option.mem_def]

theorem mem_gaps : q ∈ gaps inv ↔ q ∉ positions inv ∧ ∃ p ∈ positions inv, q < p := by
  simp [gaps]

instance : Decidable (Conforms inv) :=
  inferInstanceAs (Decidable (∀ a b : Position, b ≤ a → a ∈ positions inv → b ∈ positions inv))

theorem conforms_iff_gaps_eq_empty : Conforms inv ↔ gaps inv = ∅ := by
  refine ⟨fun h ↦ Finset.eq_empty_of_forall_notMem fun q hq ↦ ?_, fun h p q hqp hp ↦ ?_⟩
  · obtain ⟨hq, p, hp, hqp⟩ := mem_gaps.1 hq
    exact hq (h hqp.le hp)
  · by_contra hq
    rcases hqp.eq_or_lt with rfl | hlt
    · exact hq hp
    · exact Finset.notMem_empty q (h ▸ mem_gaps.2 ⟨hq, p, hp, hlt⟩)

theorem positions_mono (h : inv ⊆ inv') : positions inv ⊆ positions inv' :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- Conforming systems lie along one line of growth, since of any two one fills every position
the other fills. -/
theorem Conforms.total (h : Conforms inv) (h' : Conforms inv') :
    positions inv ⊆ positions inv' ∨ positions inv' ⊆ positions inv := by
  simpa using IsLowerSet.total h h'

/-- A case of several functions bears one label, and this leaves only apparent gaps: when the
functions of a language's cases conform, each gap among its labels is a position that some case
fills with a function it is not labelled for. -/
theorem gaps_subset_of_conforms (h : inv ⊆ inv') (h' : Conforms inv') :
    gaps inv ⊆ positions inv' \ positions inv := fun q hq ↦ by
  obtain ⟨hq, p, hp, hqp⟩ := mem_gaps.1 hq
  exact Finset.mem_sdiff.2 ⟨h' hqp.le (positions_mono h hp), hq⟩

/-! ### The systems Blake cites -/

/-- Classical Armenian (73), with the Proto-Indo-European system less the vocative. -/
def classicalArmenian : Finset Case := {.nom, .acc, .gen, .dat, .loc, .abl, .inst}

/-- Nanai (76), where a bound pronoun cross-references the possessor. -/
def nanai : Finset Case := {.nom, .acc, .dat, .loc, .abl, .inst, .all}

/-- Warndarang (77) less its purposive, where bound pronouns cross-reference subject, object and
possessor. -/
def warndarang : Finset Case := {.nom, .loc, .abl, .inst, .all}

/-- Tarascan (78), where recipients and beneficiaries take the accusative and the locative covers
source and goal as well as location. -/
def tarascan : Finset Case := {.nom, .acc, .gen, .loc, .inst, .com}

/-- The systems Blake cites for the successive stages of the hierarchy, with the three cases of
Modern Greek, the four of Ancient Greek, German and Icelandic, the six of the Slavonic languages
and of Turkish, the seven of Classical Armenian and the eight of Tamil, each beside its vocative
where it has one. -/
def systems : List (Finset Case) :=
  [Finset.univ.image Greek.StandardModern.Case.label,
    Finset.univ.image Greek.Ancient.Case.label, Finset.univ.image German.Case.label,
    Finset.univ.image Icelandic.Case.label,
    Finset.univ.image Polish.Case.label, Finset.univ.image Czech.Case.label,
    Finset.univ.image Slovak.Case.label, Finset.univ.image Serbian.Case.label,
    Finset.univ.image Turkish.Case.label, classicalArmenian, Finset.univ.image Tamil.Case.label]

/-- The systems Blake cites at each stage of the hierarchy conform to it. -/
theorem systems_conform : ∀ inv ∈ systems, Conforms inv := by
  simp only [systems, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  decide

theorem gaps_nanai : gaps nanai = {.gen} := by decide

theorem gaps_tarascan : gaps tarascan = {.dat} := by decide

/-- Warndarang is missing the genitive, the dative and a second core case, ergative or
accusative. -/
theorem gaps_warndarang : gaps warndarang = {.accErg, .gen, .dat} := by decide

/-! ### Latin

Blake gives Latin as the five-case stage, nominative, accusative, genitive, dative and a last case
of many functions whose label is somewhat arbitrary. -/

theorem gaps_latin_labels : gaps (Finset.univ.image Latin.Case.label) = {.loc} := by decide

theorem conforms_latin_functions : Conforms (Finset.univ.biUnion Latin.Case.functions) := by
  decide

/-- The locative position that the Latin case labels skip is one the functions of the Latin
cases fill. -/
theorem gaps_latin_labels_subset :
    gaps (Finset.univ.image Latin.Case.label) ⊆
      positions (Finset.univ.biUnion Latin.Case.functions) \
        positions (Finset.univ.image Latin.Case.label) :=
  gaps_subset_of_conforms
    (Finset.image_subset_iff.2 fun c _ ↦
      Finset.mem_biUnion.2 ⟨c, Finset.mem_univ c, c.label_mem_functions⟩)
    conforms_latin_functions

/-! ### Ancient Greek

Blake sets the Ancient Greek dative beside the Latin one to show that cases are compared by the
functions they cover and not by their labels. Greek has no ablative, and the functions of the
Latin ablative fall to the Greek genitive, which expresses source, and to the Greek dative, which
expresses location and instrument, so that the Greek dative is the more comprehensive case. -/

theorem latin_abl_functions_ancient_greek :
    .abl ∉ Finset.univ.image Greek.Ancient.Case.label ∧
      Latin.Case.abl.functions ⊆
        Greek.Ancient.Case.gen.functions ∪ Greek.Ancient.Case.dat.functions := by
  decide

theorem latin_dat_functions_ssubset_ancient_greek :
    Latin.Case.dat.functions ⊂ Greek.Ancient.Case.dat.functions := by decide

/-! ### The other case inventories of the fragments

The inventories that do not conform each miss a position Blake's two sources of gaps account for.
Finnish has no dative, and its allative *-lle* has dative functions. Hungarian and Basel German
have no genitive, the dative marking the possessor, as in the Pama-Nyungan languages Blake
mentions. The grammatical cases of Dargwa skip the locative and the ablative, which belong to its
separate series of local cases. Mongolian, Yakut and Georgian have no locative: the Yakut dative
has taken over the function of the old locative, and the Georgian dative keeps it with a few
nouns. Where a fragment records the functions of its cases, the functions conform. -/

-- The three cases of Classical Arabic, which Blake cites, are those of the modern standard
-- language, and Hindi-Urdu has the direct and oblique of a two-case system.
theorem fragments_conform :
    ∀ inv ∈ [Finset.univ.image Arabic.ModernStandard.Case.label,
      Finset.univ.image HindiUrdu.Case.label, Finset.univ.image Telugu.Case.label,
      Finset.univ.image Belarusian.Case.label, Finset.univ.image Cassubian.Case.label,
      Finset.univ.image Russian.Case.label, Finset.univ.image Slovenian.Case.label,
      Finset.univ.image Sorbian.Upper.Case.label, Finset.univ.image Sorbian.Lower.Case.label,
      Finset.univ.image Ukrainian.Case.label],
      Conforms inv := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  decide

theorem gaps_finnish : gaps (Finset.univ.image Finnish.Case.label) = {.dat} := by decide

theorem conforms_finnish_functions : Conforms (Finset.univ.biUnion Finnish.Case.functions) := by
  decide

theorem gaps_hungarian : gaps (Finset.univ.image Hungarian.Case.label) = {.gen} := by decide

theorem gaps_dargwa : gaps (Finset.univ.image Dargwa.Tanti.Case.label) = {.loc, .ablInst} := by
  decide

theorem gaps_mongolian : gaps (Finset.univ.image Mongolian.Case.label) = {.loc} := by decide

theorem gaps_yakut : gaps (Finset.univ.image Yakut.Case.label) = {.loc} := by decide

theorem conforms_yakut_functions : Conforms (Finset.univ.biUnion Yakut.Case.functions) := by
  decide

theorem gaps_georgian : gaps (Finset.univ.image Georgian.Case.label) = {.loc} := by decide

theorem conforms_georgian_functions :
    Conforms (Finset.univ.biUnion Georgian.Case.functions) := by
  decide

theorem gaps_basel : gaps (Finset.univ.image German.Basel.Case.label) = {.gen} := by decide

end Blake1994
