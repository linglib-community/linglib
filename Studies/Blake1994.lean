module

public import Mathlib.Data.Finset.Option
public import Linglib.Core.Order.UpperLower.Finset
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
a case at every position to its left. Such a system fills the positions down to the last it
fills and no others, so that [the systems built in this order lie along one line of
growth](##Conforms.total), as do [the systems Blake cites for the successive
stages](##systems_conform). The vocative is set aside, since it marks no relation of a dependent
to a head.

Blake stresses that this is a tendency and not an implicational universal. Bound pronouns can do
the work of a higher case, which leaves a gap: Nanai has no genitive, and [Warndarang lacks the
genitive, the dative and a second core case](##gaps_warndarang). And a case of several functions
bears one label, which leaves an apparent gap at the position of a function it is not labelled
for: [such a gap is a position that the functions fill](##gaps_inventory_subset). The practice
Blake reports is to label a case for the highest of its functions, and under it [each apparent
gap lies below the label of a case that fills it](##LabelledForHighest.exists_lt_of_mem_gaps).
The lowest case of a small system is an elsewhere case of this kind. The Latin ablative merges an
older ablative, instrumental and locative, and its label, in Blake's words somewhat arbitrary, is
not that of its highest function: the Latin labels skip the locative position.

## Implementation notes

The absolutive is placed with the nominative, since Blake calls the unmarked case of an ergative
system nominative. A local case is placed by its direction, the cases of rest with the locative
and the cases of source with the ablative. The text was checked in the second edition
([blake-2001]).

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

instance : LocallyFiniteOrderBot Position := Fintype.toLocallyFiniteOrderBot

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
  inferInstanceAs (Decidable (IsLowerSet (positions inv : Set Position)))

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

-- A conforming inventory fills the positions down to the last it fills, and no others.
theorem Conforms.mem_positions_iff (h : Conforms inv) :
    p ∈ positions inv ↔ ↑p ≤ (positions inv).max :=
  IsLowerSet.mem_iff_le_max h

theorem Conforms.eq_empty_or_eq_Iic (h : Conforms inv) :
    positions inv = ∅ ∨ ∃ p, positions inv = Finset.Iic p :=
  IsLowerSet.eq_empty_or_eq_Iic h

/-- Systems that conform lie along one line of growth: of any two, one fills every position the
other fills. -/
theorem Conforms.total (h : Conforms inv) (h' : Conforms inv') :
    positions inv ⊆ positions inv' ∨ positions inv' ⊆ positions inv :=
  IsLowerSet.subset_or_subset h h'

-- A stage of the hierarchy is fixed by how many positions it fills.
theorem Conforms.positions_eq_of_card_eq (h : Conforms inv) (h' : Conforms inv')
    (hc : (positions inv).card = (positions inv').card) : positions inv = positions inv' := by
  rcases h.total h' with hs | hs
  · exact Finset.eq_of_subset_of_card_le hs hc.ge
  · exact (Finset.eq_of_subset_of_card_le hs hc.le).symm

theorem gaps_subset_of_conforms (h : inv ⊆ inv') (h' : Conforms inv') :
    gaps inv ⊆ positions inv' \ positions inv := fun q hq ↦ by
  obtain ⟨hq, p, hp, hqp⟩ := mem_gaps.1 hq
  exact Finset.mem_sdiff.2 ⟨h' hqp.le (positions_mono h hp), hq⟩

/-! ### Labels and functions -/

section System

variable (K : Type*) [Case.System K] [Fintype K]

/-- A case of several functions bears one label, and this leaves only apparent gaps: when the
functions of a language's cases conform, each gap among its labels is a position that some case
fills with a function it is not labelled for. -/
theorem gaps_inventory_subset (h : Conforms (Case.functionInventory K)) :
    gaps (Case.inventory K) ⊆
      positions (Case.functionInventory K) \ positions (Case.inventory K) :=
  gaps_subset_of_conforms (Case.inventory_subset_functionInventory K) h

/-- The cases of a system are labelled for the highest of their functions when each case that
has a function on the hierarchy is labelled at that position or to its left. -/
def LabelledForHighest : Prop :=
  ∀ k : K, ∀ c ∈ Case.System.functions k, ∀ q, position c = some q →
    ∃ p, position (Case.System.label k) = some p ∧ p ≤ q

instance : Decidable (LabelledForHighest K) := by
  unfold LabelledForHighest; infer_instance

variable {K}

/-- Labelling a case for the highest of its functions puts the apparent gaps where the lower
functions are: when the functions conform, each gap among the labels is filled by a function of
a case labelled to its left. -/
theorem LabelledForHighest.exists_lt_of_mem_gaps (hl : LabelledForHighest K)
    (hc : Conforms (Case.functionInventory K)) {g : Position}
    (hg : g ∈ gaps (Case.inventory K)) :
    ∃ k : K, ∃ p, position (Case.System.label k) = some p ∧ p < g ∧
      ∃ c ∈ Case.System.functions k, position c = some g := by
  obtain ⟨hf, hn⟩ := Finset.mem_sdiff.1 (gaps_inventory_subset K hc hg)
  obtain ⟨c, hcf, hcg⟩ := mem_positions.1 hf
  obtain ⟨k, hk⟩ := Case.mem_functionInventory.1 hcf
  obtain ⟨p, hp, hpg⟩ := hl k c hk g hcg
  refine ⟨k, p, hp, lt_of_le_of_ne hpg ?_, c, hk, hcg⟩
  rintro rfl
  exact hn (mem_positions.2 ⟨_, Case.label_mem_inventory k, hp⟩)

end System

/-! ### The systems Blake cites -/

/-- Classical Armenian (73), with the Proto-Indo-European system less the vocative. -/
def classicalArmenian : Finset Case := {.nom, .acc, .gen, .dat, .loc, .abl, .inst}

/-- Nanai (76), where a bound pronoun cross-references the possessor. -/
def nanai : Finset Case := {.nom, .acc, .dat, .loc, .abl, .inst, .all}

/-- Warndarang (77), where bound pronouns cross-reference subject, object and possessor. -/
def warndarang : Finset Case := {.nom, .loc, .abl, .inst, .all, .purp}

/-- Tarascan (78), where recipients and beneficiaries take the accusative and the locative covers
source and goal as well as location. -/
def tarascan : Finset Case := {.nom, .acc, .gen, .loc, .inst, .com}

/-- Toda and Irula (75), with a purposive beside the eight cases of Tamil. -/
def todaIrula : Finset Case := insert .purp (Case.inventory Tamil.Case)

/-- The systems Blake cites for the successive stages of the hierarchy, with the three cases of
Modern Greek, the four of Ancient Greek, German and Icelandic, the six of the Slavonic languages
and of Turkish, the seven of Classical Armenian, the eight of Tamil and the nine of Toda and
Irula, each beside its vocative where it has one. -/
def systems : List (Finset Case) :=
  [Case.inventory Greek.StandardModern.Case, Case.inventory Greek.Ancient.Case,
    Case.inventory German.Case, Case.inventory Icelandic.Case, Case.inventory Polish.Case,
    Case.inventory Czech.Case, Case.inventory Slovak.Case, Case.inventory Serbian.Case,
    Case.inventory Turkish.Case, classicalArmenian, Case.inventory Tamil.Case, todaIrula]

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

/-! ### Latin and Ancient Greek

Blake gives Latin as the five-case stage, nominative, accusative, genitive, dative and a last case
of many functions whose label is somewhat arbitrary. He sets the Ancient Greek dative beside the
Latin one to show that cases are compared by the functions they cover and not by their labels.
Greek has no ablative, and the functions of the Latin ablative fall to the Greek genitive, which
expresses source, and to the Greek dative, which expresses location and instrument, so that the
Greek dative is the more comprehensive case. -/

theorem gaps_latin : gaps (Case.inventory Latin.Case) = {.loc} := by decide

-- The ablative is labelled for source, and location is the higher of its functions.
theorem not_labelledForHighest_latin : ¬ LabelledForHighest Latin.Case := by decide

theorem latin_abl_functions_ancient_greek :
    .abl ∉ Case.inventory Greek.Ancient.Case ∧
      Latin.Case.abl.functions ⊆
        Greek.Ancient.Case.gen.functions ∪ Greek.Ancient.Case.dat.functions := by
  decide

theorem latin_dat_functions_ssubset_ancient_greek :
    Latin.Case.dat.functions ⊂ Greek.Ancient.Case.dat.functions := by decide

/-! ### The other case inventories of the fragments

The inventories that do not conform each miss a position Blake's two sources of gaps account for.
Finnish has no dative, and its allative *-lle* has dative functions. Hungarian and Basel German
have no genitive, the dative marking the possessor, as in the Pama-Nyungan languages Blake
mentions. Mongolian, Yakut and Georgian have no locative: the Mongolian dative expresses
location, the Yakut dative has taken over the function of the old locative, and the Georgian
dative keeps it with a few nouns. In each of these the functions conform, so that the gaps are
apparent. The grammatical cases of Dargwa skip the locative and the ablative, which belong to its
separate series of local cases. -/

-- The three cases of Classical Arabic, which Blake cites, are those of the modern standard
-- language, and Hindi-Urdu has the direct and oblique of a two-case system.
theorem fragments_conform :
    ∀ inv ∈ [Case.inventory Arabic.ModernStandard.Case, Case.inventory HindiUrdu.Case,
      Case.inventory Telugu.Case, Case.inventory Belarusian.Case, Case.inventory Cassubian.Case,
      Case.inventory Russian.Case, Case.inventory Slovenian.Case,
      Case.inventory Sorbian.Upper.Case, Case.inventory Sorbian.Lower.Case,
      Case.inventory Ukrainian.Case],
      Conforms inv := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  decide

theorem gaps_fragments :
    gaps (Case.inventory Finnish.Case) = {.dat} ∧
      gaps (Case.inventory Hungarian.Case) = {.gen} ∧
      gaps (Case.inventory German.Basel.Case) = {.gen} ∧
      gaps (Case.inventory Mongolian.Case) = {.loc} ∧
      gaps (Case.inventory Yakut.Case) = {.loc} ∧
      gaps (Case.inventory Georgian.Case) = {.loc} ∧
      gaps (Case.inventory Dargwa.Tanti.Case) = {.loc, .ablInst} := by
  decide

theorem functions_conform :
    ∀ inv ∈ [Case.functionInventory Latin.Case, Case.functionInventory Greek.Ancient.Case,
      Case.functionInventory Finnish.Case, Case.functionInventory Hungarian.Case,
      Case.functionInventory German.Basel.Case, Case.functionInventory Mongolian.Case,
      Case.functionInventory Yakut.Case, Case.functionInventory Georgian.Case],
      Conforms inv := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  decide

-- The datives that take in the locative are labelled for the higher function. The Finnish
-- allative and the Hungarian and Basel German datives are labelled for the lower one.
theorem labelledForHighest_fragments :
    LabelledForHighest Greek.Ancient.Case ∧ LabelledForHighest Mongolian.Case ∧
      LabelledForHighest Yakut.Case ∧ LabelledForHighest Georgian.Case ∧
      ¬ LabelledForHighest Finnish.Case ∧ ¬ LabelledForHighest Hungarian.Case ∧
      ¬ LabelledForHighest German.Basel.Case := by
  decide

end Blake1994
