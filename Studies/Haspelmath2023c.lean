module

public import Linglib.Languages.English.Particles
public import Linglib.Languages.Slavic.Russian.QuestionParticles
public import Linglib.Languages.Turkish.QuestionParticles
public import Linglib.Morphology.Word.Distributional
public import Studies.Haspelmath2021c
public import Studies.Haspelmath2023
public import Studies.ZwickyPullum1983

/-!
# Haspelmath (2023): Types of clitics in the world's languages

A clitic is a bound morph that is neither an affix nor a root, where an affix always occurs on
roots of one class. A clitic is an enclitic when it can occur at the end of a free form but not at
the beginning, a proclitic when it can occur at the beginning but not at the end, an ambiclitic
when it can occur at both, and an interclitic when it can occur at neither. A second-position
clitic must occur directly after the first word of its clause. These are properties of a morph's
distribution over the free forms of its language, and this
file checks them against the paper's examples, and states where they agree with the attachment
the language files record for the same morphs, a label of the source, and with Zwicky and Pullum's
criterion of selection, of which lack of word-class selectivity is the first.

## Main definitions

* `Haspelmath2023c.IsEnclitic`, `IsProclitic`, `IsAmbiclitic`, `IsInterclitic`: the positional
  types of a clitic.
* `Haspelmath2023c.IsSecondPosition`: a clitic that follows the first word of every free form
  it occurs in.
* `Haspelmath2023c.selection`: Zwicky and Pullum's degree of selection of a morph, read off the
  classes of the roots it stands next to.

## Implementation notes

* An ambiclitic is taken to occur both at the end and at the beginning of free forms, so that the
  four positional types are exclusive.
* Second position is stated for the first word, the first maximal run of morphs joined as
  affixes; the first nominal or adverbial expression and clitic clusters are not represented.
* The Turkish verb forms are segmented into a stem and the past suffix, which the paper writes
  unsegmented. An adverb is a free morph with no root class.
* The roots of each example are its contentful morphs, as in `Studies.Haspelmath2023`.
* The degree of selection is that of a single category when one class of root is present at every
  occurrence of a morph, and low otherwise; a closed list of stems is not read off the free forms.
* In Zwicky and Pullum's three sentences each written word is one morph, a root when it is a noun,
  a verb or an adjective.
* The three Russian questions are joined with the 2021 paper's *znaeš' li?*, *zdorov li?* and
  *zdes' li?*, since in each of the questions a noun follows *li*.

## TODO

* Read the free forms from example rows in boundary notation.

## References

* [haspelmath-2023c]
* [haspelmath-2023]
* [haspelmath-2021c]
* [zwicky-pullum-1983]
-/

@[expose] public section

namespace Haspelmath2023c

open Morphology Morphology.Distributional

/-! ### Positional types -/

section Positional

variable {M : Type*} (F : List (List M)) (cls : M → Option RootClass) (x : M)

/-- The morph occurs at the end of a free form. -/
def OccursFinally : Prop := ∃ w ∈ F, w.getLast? = some x

/-- The morph occurs at the beginning of a free form. -/
def OccursInitially : Prop := ∃ w ∈ F, w.head? = some x

/-- An enclitic is a clitic that can occur at the end of a free form but not at the beginning. -/
def IsEnclitic : Prop := IsClitic F cls x ∧ OccursFinally F x ∧ ¬ OccursInitially F x

/-- A proclitic is a clitic that can occur at the beginning of a free form but not at the end. -/
def IsProclitic : Prop := IsClitic F cls x ∧ OccursInitially F x ∧ ¬ OccursFinally F x

/-- An ambiclitic is a clitic that can occur at the end of a free form and at the beginning. -/
def IsAmbiclitic : Prop := IsClitic F cls x ∧ OccursFinally F x ∧ OccursInitially F x

/-- An interclitic is a clitic that can occur neither at the end of a free form nor at the
beginning. -/
def IsInterclitic : Prop := IsClitic F cls x ∧ ¬ OccursFinally F x ∧ ¬ OccursInitially F x

variable {F cls x}

theorem isClitic_iff :
    IsClitic F cls x ↔
      IsEnclitic F cls x ∨ IsProclitic F cls x ∨ IsAmbiclitic F cls x ∨
        IsInterclitic F cls x := by
  unfold IsEnclitic IsProclitic IsAmbiclitic IsInterclitic
  by_cases hf : OccursFinally F x <;> by_cases hi : OccursInitially F x <;> simp [hf, hi]

theorem IsEnclitic.not_isProclitic (h : IsEnclitic F cls x) : ¬ IsProclitic F cls x :=
  fun h' ↦ h.2.2 h'.2.1

theorem not_isClitic_of_mem (h : [x] ∈ F) : ¬ IsClitic F cls x := fun hc ↦ hc.notMem h

section Decidable

variable (F cls x) [DecidableEq M]

instance : Decidable (OccursFinally F x) := inferInstanceAs (Decidable (∃ w ∈ F, _))

instance : Decidable (OccursInitially F x) := inferInstanceAs (Decidable (∃ w ∈ F, _))

instance : Decidable (IsEnclitic F cls x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : Decidable (IsProclitic F cls x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : Decidable (IsAmbiclitic F cls x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : Decidable (IsInterclitic F cls x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Decidable

end Positional

/-- The form directly follows the first word of the free form, the first run of forms joined as
affixes. -/
def FollowsFirstWord (x : Form) (w : List Form) : Prop :=
  ((Haspelmath2023.wordsAt .affix w).drop 1).head? = some [x]

instance (x : Form) (w : List Form) : Decidable (FollowsFirstWord x w) :=
  inferInstanceAs (Decidable (_ = _))

/-- A second-position clitic is a clitic that directly follows the first word of every free form
it occurs in. -/
def IsSecondPosition (F : List (List Form)) (cls : Form → Option RootClass) (x : Form) : Prop :=
  IsClitic F cls x ∧ ∀ w ∈ F, x ∈ w → FollowsFirstWord x w

instance (F : List (List Form)) (cls : Form → Option RootClass) (x : Form) :
    Decidable (IsSecondPosition F cls x) :=
  inferInstanceAs (Decidable (_ ∧ ∀ w ∈ F, _))

/-! ### Russian *li* -/

/-- The Russian action root *pročita* 'read'. -/
def procita : Form := ⟨.root "pročita", some .action⟩
/-- The Russian action root *čita* 'read'. -/
def cita : Form := ⟨.root "čita", some .action⟩
/-- The Russian past suffix *-la*. -/
def la : Form := ⟨.suff "la", none⟩
/-- The Russian object root *Anna*. -/
def anna : Form := ⟨.root "Anna", some .object⟩
/-- The Russian object root *knigu* 'book'. -/
def knigu : Form := ⟨.root "knigu", some .object⟩
/-- The Russian adverb *včera* 'yesterday'. -/
def vcera : Form := ⟨.free "včera", none⟩

/-- The language file's morphs for *li*, as forms that denote no action, object or property. -/
def liForms : List Form := Russian.QuestionParticles.li.morphs.map (⟨·, none⟩)

/-- The Russian questions *Pročita-la li Anna knigu?*, *Knigu li Anna pročita-la?* and
*Včera li Anna čita-la?*, with the language file's morph for *li*. -/
def questions : List (List Form) :=
  [[procita, la] ++ liForms ++ [anna, knigu], knigu :: liForms ++ [anna, procita, la],
   vcera :: liForms ++ [anna, cita, la]]

/-- The three questions together with *znaeš' li?*, *zdorov li?* and *zdes' li?*, in which
nothing follows *li*. -/
def russian : List (List Form) := Haspelmath2021c.russian ++ questions

open Haspelmath2021c (li) in
-- On the three questions alone *li* passes as an affix, since the noun *Anna* follows it in each.
theorem li_notMem_affixes :
    li ∉ affixes russian Form.meaning ∧ li ∈ affixes questions Form.meaning := by
  decide

/-- On these forms Russian *li* is a second-position clitic by the definition, and the language file
records that placement. -/
theorem li_isSecondPosition :
    (∀ m ∈ liForms, IsSecondPosition russian Form.meaning m) ∧
      .secondPosition ∈ Russian.QuestionParticles.li.placements := by
  decide

/-! ### Turkish *mI* -/

/-- The Turkish action root *gel* 'come'. -/
def gel : Form := ⟨.root "gel", some .action⟩
/-- The Turkish action root *öl* 'die'. -/
def ol : Form := ⟨.root "öl", some .action⟩
/-- The Turkish past suffix -DI. -/
def di : Form := ⟨.suff "DI", none⟩
/-- The Turkish object root *Ali*. -/
def ali : Form := ⟨.root "Ali", some .object⟩
/-- The Turkish adverb *dün* 'yesterday'. -/
def dun : Form := ⟨.free "dün", none⟩

/-- The language file's morphs for *mI*, as forms that denote no action, object or property. -/
def miForms : List Form := Turkish.QuestionParticles.mi.morphs.map (⟨·, none⟩)

/-- The Turkish questions *geldi mi?*, *öldü mü?*, *Ali mi?* and *dün mü?*, with the language file's
morph for *mI*. -/
def turkish : List (List Form) :=
  [[gel, di] ++ miForms, [ol, di] ++ miForms, ali :: miForms, dun :: miForms]

/-- Turkish *mI* follows a verb, a noun and an adverb and ends each question, so on these forms
it is an enclitic by the definition, and the language file labels it one. -/
theorem mi_isEnclitic :
    ∀ m ∈ miForms, IsEnclitic turkish Form.meaning m ∧ m.shape.kind = .bound .after .clitic := by
  decide

theorem mi_mem_affixes_of_verbs : ∀ m ∈ miForms, m ∈ affixes (turkish.take 2) Form.meaning := by
  decide

/-! ### English -/

/-- The English object root *friend*. -/
def friend : Form := ⟨.root "friend", some .object⟩
/-- The English object root *house*. -/
def house : Form := ⟨.root "house", some .object⟩
/-- The English article *the*. -/
def the : Form := ⟨.procl "the", none⟩
/-- The English object root *boy*. -/
def boy : Form := ⟨.root "boy", some .object⟩
/-- The English pronoun *I*. -/
def i : Form := ⟨.procl "I", none⟩
/-- The English action root *like*. -/
def like : Form := ⟨.root "like", some .action⟩
/-- The English property root *new*. -/
def new : Form := ⟨.root "new", some .property⟩
/-- The English object root *bike*. -/
def bike : Form := ⟨.root "bike", some .object⟩

open Haspelmath2023 (my s_gen «to» infinitives) in
/-- The English forms *my friend's*, *my friend's house* and *the boy I like's new bike*. -/
def genitives : List (List Form) :=
  [[my, friend, s_gen], [my, friend, s_gen, house], [the, boy, i, like, s_gen, new, bike]]

open Haspelmath2023 (s_gen «to» infinitives) in
theorem s_isEnclitic_to_isProclitic :
    IsEnclitic genitives Form.meaning s_gen ∧
      IsProclitic infinitives Form.meaning «to» := by
  decide

/-- The English possessive *our*. -/
def our : Form := ⟨.procl "our", none⟩
/-- The English property root *ambitious*. -/
def ambitious : Form := ⟨.root "ambitious", some .property⟩
/-- The English object root *proposal*. -/
def proposal : Form := ⟨.root "proposal", some .object⟩
/-- The English action root *fail*. -/
def fail : Form := ⟨.root "fail", some .action⟩
/-- The English past suffix *-ed*. -/
def ed : Form := ⟨.suff "ed", none⟩
/-- English *however*, written as a word. -/
def however : Form := ⟨.free "however", none⟩

/-- The English sentences with *however* at the beginning, in the middle and at the end. -/
def howevers : List (List Form) :=
  [[however, our, ambitious, proposal, fail, ed], [our, ambitious, proposal, however, fail, ed],
     [our, ambitious, proposal, fail, ed, however]]

theorem however_isAmbiclitic :
    IsAmbiclitic howevers Form.meaning however ∧ however.shape.kind = .free := by
  decide

theorem yes_not_isClitic (F : List (List Morph)) (cls : Morph → Option RootClass)
    (h : [English.PolarityParticles.yes] ∈ F) : ¬ IsClitic F cls English.PolarityParticles.yes :=
  not_isClitic_of_mem h

/-! ### Selection

Zwicky and Pullum's first criterion is that clitics show a low degree of selection with respect
to their hosts and affixes a high one, and the lack of word-class selectivity is that criterion
on the classes of roots. -/

section Selection

open Morphology.Diagnostics

variable {M : Type*} [DecidableEq M] (F : List (List M)) (cls : M → Option RootClass)

/-- The degree of selection of a morph is that of a single category when it selects a class of
root through the affixes, and low otherwise. -/
def selection (x : M) : SelectionDegree :=
  if ∃ c, Selects F cls (affixes F cls) x c then .singleCategory else .low

variable {F cls} {x : M}

/-- An affix shows a high degree of selection. -/
theorem isHighSelection_of_mem_affixes (h : x ∈ affixes F cls) :
    (selection F cls x).IsHighSelection := by
  simp [selection, SelectionDegree.IsHighSelection, (mem_affixes_iff.1 h).selects]

theorem notMem_affixes_of_selection_eq_low (h : selection F cls x = .low) : x ∉ affixes F cls :=
  fun ha ↦ isHighSelection_of_mem_affixes ha h

/-- The degree of selection of a morph is low when it selects no class of root even through
every morph that is not a root. -/
theorem selection_eq_low (h : ¬ ∃ c, Selects F cls {z | cls z = none} x c) :
    selection F cls x = .low := by
  simpa [selection] using fun c hc ↦ h ⟨c, hc.mono affixes_subset⟩

end Selection

/-- The English contracted auxiliary *'s*. -/
def contracted : Form := ⟨.encl "s", none⟩

/-- A noun as a form that denotes an object. -/
def noun (s : String) : Form := ⟨.root s, some .object⟩
/-- A verb as a form that denotes an action. -/
def verb (s : String) : Form := ⟨.root s, some .action⟩
/-- An adjective as a form that denotes a property. -/
def adj (s : String) : Form := ⟨.root s, some .property⟩
/-- A word that denotes no action, object or property. -/
def other (m : Morph) : Form := ⟨m, none⟩

/-- Zwicky and Pullum's sentences *The ball you hit's just broken my dining room window*, *Any
answer not entirely right's going to be marked as an error* and *The drive home tonight's been
really easy*. -/
def contractions : List (List Form) :=
  [[other (.procl "the"), noun "ball", other (.procl "you"), verb "hit", contracted,
    other (.free "just"), verb "broken", other (.procl "my"), verb "dining", noun "room",
    noun "window"],
   [other (.free "any"), noun "answer", other (.free "not"), other (.free "entirely"),
    adj "right", contracted, verb "going", other (.procl "to"), other (.free "be"),
    verb "marked", other (.free "as"), other (.procl "an"), noun "error"],
   [other (.procl "the"), noun "drive", other (.free "home"), other (.free "tonight"),
    contracted, other (.free "been"), other (.free "really"), adj "easy"]]

/-- The contracted auxiliary follows a verb, an adjective and an adverb in Zwicky and Pullum's
sentences, so its selection read off them is the low degree they record, and it is not an
affix. -/
theorem contracted_selection :
    selection contractions Form.meaning contracted =
        ZwickyPullum1983.cliticS.selection ∧
      contracted ∉ affixes contractions Form.meaning :=
  have h : selection contractions Form.meaning contracted = .low :=
    selection_eq_low (by decide)
  ⟨h, notMem_affixes_of_selection_eq_low h⟩

open Haspelmath2023 (s_gen) in
theorem selection_eq :
    selection howevers Form.meaning ed = ZwickyPullum1983.affixEd.selection ∧
      selection genitives Form.meaning s_gen = .low ∧
      selection howevers Form.meaning however = .low := by
  decide

end Haspelmath2023c
