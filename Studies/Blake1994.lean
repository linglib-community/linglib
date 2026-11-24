module

public import Mathlib.Data.Finset.Option
public import Mathlib.Order.UpperLower.Closure
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Languages.Arabic.ModernStandard.Case
public import Linglib.Languages.Dargwa.Tanti.Case
public import Linglib.Languages.Finnish.Case
public import Linglib.Languages.Georgian.Case
public import Linglib.Languages.German.Basel.Case
public import Linglib.Languages.German.Case
public import Linglib.Languages.Greek.Ancient.Case
public import Linglib.Languages.Greek.StandardModern.Case
public import Linglib.Languages.HindiUrdu.Case
public import Linglib.Languages.Hungarian.Case
public import Linglib.Languages.Icelandic.Case
public import Linglib.Languages.Latin.Case
public import Linglib.Languages.Mongolian.Case
public import Linglib.Languages.Slavic.Belarusian.Case
public import Linglib.Languages.Slavic.Cassubian.Case
public import Linglib.Languages.Slavic.Czech.Case
public import Linglib.Languages.Slavic.Polish.Case
public import Linglib.Languages.Slavic.Russian.Case
public import Linglib.Languages.Slavic.Serbian.Case
public import Linglib.Languages.Slavic.Slovak.Case
public import Linglib.Languages.Slavic.Slovenian.Case
public import Linglib.Languages.Slavic.Sorbian.Case
public import Linglib.Languages.Slavic.Ukrainian.Case
public import Linglib.Languages.Tamil.Case
public import Linglib.Languages.Telugu.Case
public import Linglib.Languages.Turkish.Case
public import Linglib.Languages.Yakut.Case

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
for: [such a gap is a position that the functions fill](##gaps_image_subset). The practice
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
case. This is not stated: the one language file with both an ergative and an accusative,
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

instance : OrderBot Position where
  bot := .nom
  bot_le := by decide

@[simp] theorem Position.bot_eq : (⊥ : Position) = .nom := rfl

instance : LocallyFiniteOrder Position := Fintype.toLocallyFiniteOrder

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

/-- The gaps of an inventory are the unfilled positions in the lower closure of the filled ones,
those to the left of a filled one. -/
def gaps (inv : Finset Case) : Finset Position :=
  Finset.univ.filter fun q ↦ (∃ p ∈ positions inv, q ≤ p) ∧ q ∉ positions inv

variable {inv inv' : Finset Case} {p q : Position}

theorem mem_positions : p ∈ positions inv ↔ ∃ c ∈ inv, position c = some p := by
  simp [positions, Option.mem_def]

theorem mem_gaps :
    q ∈ gaps inv ↔ q ∈ lowerClosure (positions inv : Set Position) ∧ q ∉ positions inv := by
  simp [gaps]

instance : Decidable (Conforms inv) :=
  inferInstanceAs (Decidable (IsLowerSet (positions inv : Set Position)))

theorem conforms_iff_gaps_eq_empty : Conforms inv ↔ gaps inv = ∅ := by
  refine ⟨fun h ↦ Finset.eq_empty_of_forall_notMem fun q hq ↦ ?_, fun h p q hqp hp ↦ ?_⟩
  · exact (mem_gaps.1 hq).2 (h.lowerClosure.subset (mem_gaps.1 hq).1)
  · by_contra hq
    exact Finset.notMem_empty q (h ▸ mem_gaps.2 ⟨⟨p, hp, hqp⟩, hq⟩)

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

theorem gaps_subset_of_isLowerSet {s : Finset Position} (h : positions inv ⊆ s)
    (hs : IsLowerSet (s : Set Position)) : gaps inv ⊆ s \ positions inv := fun _ hq ↦
  Finset.mem_sdiff.2
    ⟨lowerClosure_min (Finset.coe_subset.2 h) hs (mem_gaps.1 hq).1, (mem_gaps.1 hq).2⟩

theorem gaps_subset_of_conforms (h : inv ⊆ inv') (h' : Conforms inv') :
    gaps inv ⊆ positions inv' \ positions inv :=
  gaps_subset_of_isLowerSet (positions_mono h) h'

/-! ### Labels and functions -/

/-- The position of a function, that of the case named for it: S at the first position, A and P
at the second, and a spatial function by its direction. -/
def functionPosition : Case.Function → Option Position
  | .argument .S => some .nom
  | .argument .A | .argument .P => some .accErg
  | .argument .R => some .dat
  | .argument .T | .vocative => none
  | .possessor => some .gen
  | .instrumental => some .ablInst
  | f =>
    match f.direction? with
    | some .place => some .loc
    | some .source => some .ablInst
    | _ => some .other

/-- The positions a set of functions fills. -/
def functionPositions (fs : Finset Case.Function) : Finset Position :=
  fs.biUnion fun f ↦ (functionPosition f).toFinset

section Functions

variable {K : Type*} [Fintype K] (label : K → Case) (functions : K → Finset Case.Function)

/-- A case of several functions bears one label, and this leaves only apparent gaps: when the
functions of a language's cases conform, each gap among its labels is a position that some case
fills with a function it is not labelled for. -/
theorem gaps_image_subset
    (hm : ∀ k, (position (label k)).toFinset ⊆ functionPositions (functions k))
    (h : IsLowerSet (functionPositions (Finset.univ.biUnion functions) : Set Position)) :
    gaps (Finset.univ.image label) ⊆
      functionPositions (Finset.univ.biUnion functions) \ positions (Finset.univ.image label) :=
  gaps_subset_of_isLowerSet (fun q hq ↦ by
    obtain ⟨c, hc, hq⟩ := mem_positions.1 hq
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.biUnion_subset_biUnion_of_subset_left _
      (Finset.subset_biUnion_of_mem functions (Finset.mem_univ k))
      (hm k (Option.mem_toFinset.2 hq))) h

/-- Cases are labelled for the highest of their functions when each case that has a function on
the hierarchy is labelled at that position or to its left. -/
def LabelledForHighest : Prop :=
  ∀ k, ∀ q ∈ functionPositions (functions k), ∃ p, position (label k) = some p ∧ p ≤ q

instance : Decidable (LabelledForHighest label functions) := by
  unfold LabelledForHighest; infer_instance

variable {label functions}

/-- Labelling a case for the highest of its functions puts the apparent gaps where the lower
functions are: when the functions conform, each gap among the labels is filled by a function of
a case labelled to its left. -/
theorem LabelledForHighest.exists_lt_of_mem_gaps (hl : LabelledForHighest label functions)
    (hm : ∀ k, (position (label k)).toFinset ⊆ functionPositions (functions k))
    (hc : IsLowerSet (functionPositions (Finset.univ.biUnion functions) : Set Position))
    {g : Position} (hg : g ∈ gaps (Finset.univ.image label)) :
    ∃ k p, position (label k) = some p ∧ p < g ∧ g ∈ functionPositions (functions k) := by
  obtain ⟨hf, hn⟩ := Finset.mem_sdiff.1 (gaps_image_subset label functions hm hc hg)
  obtain ⟨f, hff, hfg⟩ := Finset.mem_biUnion.1 hf
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 hff
  have hgk : g ∈ functionPositions (functions k) := Finset.mem_biUnion.2 ⟨f, hk, hfg⟩
  obtain ⟨p, hp, hpg⟩ := hl k g hgk
  refine ⟨k, p, hp, lt_of_le_of_ne hpg ?_, hgk⟩
  rintro rfl
  exact hn (mem_positions.2 ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ k), hp⟩)

end Functions

-- The comparative values are themselves labelled for the highest of the functions they are
-- named for: the position of a value is the first its functions fill.
theorem labelledForHighest_functions : LabelledForHighest id Case.functions := by decide

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
def todaIrula : Finset Case := insert .purp (Finset.univ.image Tamil.Case.label)

/-- The systems Blake cites for the successive stages of the hierarchy, with the three cases of
Modern Greek, the four of Ancient Greek, German and Icelandic, the six of the Slavonic languages
and of Turkish, the seven of Classical Armenian, the eight of Tamil and the nine of Toda and
Irula, each beside its vocative where it has one. -/
def systems : List (Finset Case) :=
  [Finset.univ.image Greek.StandardModern.Case.label,
    Finset.univ.image Greek.Ancient.Case.label, Finset.univ.image German.Case.label,
    Finset.univ.image Icelandic.Case.label, Finset.univ.image Polish.Case.label,
    Finset.univ.image Czech.Case.label, Finset.univ.image Slovak.Case.label,
    Finset.univ.image Serbian.Case.label, Finset.univ.image Turkish.Case.label,
    classicalArmenian, Finset.univ.image Tamil.Case.label, todaIrula]

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

theorem gaps_latin : gaps (Finset.univ.image Latin.Case.label) = {.loc} := by decide

-- The ablative is labelled for source, and location is the higher of its functions.
theorem not_labelledForHighest_latin :
    ¬ LabelledForHighest Latin.Case.label Latin.Case.functions := by decide

theorem latin_abl_functions_ancient_greek :
    .abl ∉ Finset.univ.image Greek.Ancient.Case.label ∧
      Latin.Case.abl.functions ⊆
        Greek.Ancient.Case.gen.functions ∪ Greek.Ancient.Case.dat.functions := by
  decide

theorem ancient_greek_dat_functions :
    (∀ f ∈ [.spatial none .place, .instrumental],
        f ∈ Greek.Ancient.Case.dat.functions ∧ f ∉ Latin.Case.dat.functions) ∧
      .argument .R ∈ Greek.Ancient.Case.dat.functions ∧
      .argument .R ∈ Latin.Case.dat.functions := by decide

/-! ### The other case inventories of the language files

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
    ∀ inv ∈ [Finset.univ.image Arabic.ModernStandard.Case.label,
      Finset.univ.image HindiUrdu.Case.label, Finset.univ.image Telugu.Case.label,
      Finset.univ.image Belarusian.Case.label, Finset.univ.image Cassubian.Case.label,
      Finset.univ.image Russian.Case.label, Finset.univ.image Slovenian.Case.label,
      Finset.univ.image Sorbian.Upper.Case.label, Finset.univ.image Sorbian.Lower.Case.label,
      Finset.univ.image Ukrainian.Case.label],
      Conforms inv := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  decide

theorem gaps_fragments :
    gaps (Finset.univ.image Finnish.Case.label) = {.dat} ∧
      gaps (Finset.univ.image Hungarian.Case.label) = {.gen} ∧
      gaps (Finset.univ.image German.Basel.Case.label) = {.gen} ∧
      gaps (Finset.univ.image Mongolian.Case.label) = {.loc} ∧
      gaps (Finset.univ.image Yakut.Case.label) = {.loc} ∧
      gaps (Finset.univ.image Georgian.Case.label) = {.loc} ∧
      gaps (Finset.univ.image Dargwa.Tanti.Case.label) = {.loc, .ablInst} := by
  decide

theorem functions_conform :
    ∀ fs ∈ [Finset.univ.biUnion Latin.Case.functions,
      Finset.univ.biUnion Greek.Ancient.Case.functions,
      Finset.univ.biUnion Finnish.Case.functions, Finset.univ.biUnion Hungarian.Case.functions,
      Finset.univ.biUnion German.Basel.Case.functions,
      Finset.univ.biUnion Mongolian.Case.functions, Finset.univ.biUnion Yakut.Case.functions,
      Finset.univ.biUnion Georgian.Case.functions],
      IsLowerSet (functionPositions fs : Set Position) := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  decide

-- The datives that take in the locative are labelled for the higher function. The Finnish
-- allative and the Hungarian and Basel German datives are labelled for the lower one, and so is
-- the Georgian dative, which also marks the direct object in the first series of the verb.
theorem labelledForHighest_fragments :
    LabelledForHighest Greek.Ancient.Case.label Greek.Ancient.Case.functions ∧
      LabelledForHighest Mongolian.Case.label Mongolian.Case.functions ∧
      LabelledForHighest Yakut.Case.label Yakut.Case.functions ∧
      ¬ LabelledForHighest Georgian.Case.label Georgian.Case.functions ∧
      ¬ LabelledForHighest Finnish.Case.label Finnish.Case.functions ∧
      ¬ LabelledForHighest Hungarian.Case.label Hungarian.Case.functions ∧
      ¬ LabelledForHighest German.Basel.Case.label German.Basel.Case.functions := by
  decide

end Blake1994
