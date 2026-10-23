module

public import Linglib.Data.Examples.VanCraenenbroeck2014
public import Linglib.Morphology.DistributedMorphology.RootCategorization

/-!
# van Craenenbroeck (2014): On diagnosing complement-taking roots

Harley argues that roots take complements from criteria that should diagnose one structure: a
noun and a verb of one root select their objects alike, *one* strands adjuncts and not arguments,
and an idiom built from a root and its object alone passivizes and nominalizes. The commentary finds
the criteria mismatched. In English and Frisian an argument that a noun and a verb select alike can
still be stranded by a proform, as only adjuncts were to be, and Dutch idioms that passivize and
survive as nominalized infinitives lose their reading under a nominalizing suffix. Arguments, like
adjuncts, would then be severed from the root, introduced by a functional head over it, and
proforms would stand for phrases at different heights.

The mismatch is that pronominalization and selection read different properties of a
configuration. A proform strands the argument when a phrase of its category separates the argument
from the root, and a noun and a verb select their objects alike when the argument is merged with
a head that categorizes nothing. Taking the argument as its complement, the root is not separated
from it; with the argument in the specifier of the categorizer, the categorizer selects it. Only
the argument in the specifier of a functional head over the root has both properties.

## Main statements

* `derives_iff`: of the root taking the argument as its complement, the root modifying the
  categorizer, the argument in the specifier of the categorizer, and the argument in the specifier
  of a functional head over the root, only the last derives the selection and the
  pronominalization examples.
* `not_fits`: no idiom domain derives the judgments of the idioms that passivize and survive as
  nominalized infinitives.

## Implementation notes

* A proform stands for a phrase of its category, and a selection restriction relates an argument
  to the head it is merged with. A configuration chooses the category of each proform, and the
  *to* that introduces the stranded argument of (11) is set aside, as the paper does.
* The configurations are shapes without words, which play no part in either reading; that of
  (14) is the functional projection as printed, without the categorizer above it.
* An idiom's domain is the root's phrase, vP or VoiceP, as in the classification the paper adopts.
  An idiomatic reading survives a form that alters no head of its domain: the passive alters
  Voice, and the nominalized infinitive, the Dutch counterpart of the English gerund, and the
  suffixal nominalization alter v.

## References

* [van-craenenbroeck-2014]
* [harley-2014]
* [embick-2004]
-/

@[expose] public section

namespace VanCraenenbroeck2014

open PhraseStructure DistributedMorphology
open DistributedMorphology.RootCategorization (Cat Lexicon Attachment specifierTree selector)
open Core.Order (TreePath)

/-! ### Pronominalization and selection -/

/-- In the configurations of a root and its argument, the root takes the argument as its
complement, as in (12), or modifies the categorizer whose complement it is, or the argument is in
the specifier of the categorizer, or in the specifier of a functional head over the root, as in
(14). -/
inductive Config
  | complement | modifier | specifier | severed
  deriving DecidableEq, Repr

/-- A configuration's phrase under a categorizer. -/
def Config.tree (x : Categorizer) : Config → Tree Cat Unit
  | .complement => Attachment.complement.tree ⟨x, (), (), ()⟩
  | .modifier => Attachment.modifier.tree ⟨x, (), (), ()⟩
  | .specifier => specifierTree ⟨x, (), (), ()⟩
  | .severed => .node .f [.terminal .d (), .node .f [.terminal .f (), .terminal .root ()]]

/-- The position of the root. -/
def Config.rootPos : Config → TreePath
  | .complement | .modifier => ⟨[0, 0]⟩
  | .specifier => ⟨[1, 0, 0]⟩
  | .severed => ⟨[1, 1]⟩

/-- The position of the argument. -/
def Config.argPos : Config → TreePath
  | .complement => ⟨[1, 1]⟩
  | .modifier => ⟨[1]⟩
  | .specifier | .severed => ⟨[0]⟩

/-- A proform strands the argument or includes it. -/
inductive Use
  | stranded | included
  deriving DecidableEq, Repr

/-- A proform of category `X` may stand for a phrase that contains the root and strands or
includes the argument. -/
def Config.Licenses (c : Config) (x : Categorizer) (X : Cat) : Use → Prop
  | .stranded => Strands X (c.tree x) c.rootPos c.argPos
  | .included =>
    ∃ p ∈ c.rootPos.toList.inits.map TreePath.mk, p ≤ c.argPos ∧ Replaceable X (c.tree x) p

instance (c : Config) (x : Categorizer) (X : Cat) : ∀ u, Decidable (c.Licenses x X u)
  | .stranded => inferInstanceAs (Decidable (Strands _ _ _ _))
  | .included => inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- The proforms of (11), (13) and (17), English *the same* or *likewise* and Frisian *ien*. -/
inductive Proform
  | sameLikewise | ien
  deriving DecidableEq, Repr

/-- The proforms as named in the rows. -/
def proformTable : List (String × Proform) := [("the same/likewise", .sameLikewise), ("ien", .ien)]

/-- The categories as named in the rows. -/
def categoryTable : List (String × Categorizer) := [("verb", .v), ("noun", .n)]

/-- The uses as named in the rows. -/
def useTable : List (String × Use) := [("stranded", .stranded), ("included", .included)]

/-- The categories of the selection examples (10) and (15). -/
def selectionData : List Categorizer :=
  Examples.all.filterMap fun d ↦
    if d.feature? "construction" = some "selection" then d.parse? "category" categoryTable
    else none

/-- The pronominalization examples (11), (13) and (17), each with the category of the
pronominalized phrase, the proform, its use and the judgment. -/
def pronominalizationData : List (Categorizer × Proform × Use × Judgment) :=
  Examples.all.filterMap fun d ↦ do
    guard (d.feature? "construction" = some "pronominalization")
    pure (← d.parse? "category" categoryTable, ← d.parse? "proform" proformTable,
      ← d.parse? "argument" useTable, d.judgment)

theorem length_data : selectionData.length = 4 ∧ pronominalizationData.length = 4 := by
  decide +kernel

/-- A configuration derives the examples when the argument is merged with one head in the nouns
and the verbs of the selection examples, and each proform has a category that licenses exactly
the uses the pronominalization examples accept. -/
def Config.Derives (c : Config) : Prop :=
  (∀ x ∈ selectionData, ∀ y ∈ selectionData,
    selector (c.tree x) c.argPos = selector (c.tree y) c.argPos) ∧
  ∀ r ∈ pronominalizationData, ∃ X, ∀ s ∈ pronominalizationData, s.2.1 = r.2.1 →
    (s.2.2.2 = .acceptable ↔ c.Licenses s.1 X s.2.2.1)

instance (c : Config) : Decidable c.Derives := inferInstanceAs (Decidable (_ ∧ _))

/-- **Only the severed argument derives the examples.** Where the root takes the argument as its
complement or modifies the categorizer no proform strands the argument, as
`RootCategorization.not_strands_argPos` shows in every context; where the argument is in the
specifier of the categorizer, the verb and the noun merge it with different heads. -/
theorem derives_iff (c : Config) : c.Derives ↔ c = .severed := by
  cases c <;> decide +kernel

/-! ### Idiomatization -/

/-- The domain of an idiom, the root's phrase, vP or VoiceP. -/
inductive Domain
  | root | v | voice
  deriving DecidableEq, Repr

/-- The height of a domain's head on the clausal spine. -/
def Domain.rank : Domain → ℕ
  | .root => 0
  | .v => 1
  | .voice => 2

/-- The forms of an idiom in (18)–(22). -/
inductive Form
  | active | passive | nominalizedInfinitive | nominalization
  deriving DecidableEq, Repr

/-- The lowest head a form alters. -/
def Form.altered : Form → Option Domain
  | .active => none
  | .passive => some .voice
  | .nominalizedInfinitive | .nominalization => some .v

/-- An idiomatic reading survives a form that alters no head of its domain. -/
def Survives (d : Domain) (f : Form) : Prop := ∀ h ∈ f.altered, d.rank < h.rank

instance (d : Domain) (f : Form) : Decidable (Survives d f) :=
  inferInstanceAs (Decidable (∀ h ∈ f.altered, _))

/-- The idioms of (18)–(22) are *iemand de bons geven* 'dump someone', *iemand de das omdoen* 'be
the end of someone', *de strijdbijl begraven* 'bury the hatchet' and *het ijs breken* 'break the
ice'. -/
inductive Idiom
  | bons | das | strijdbijl | ijs
  deriving DecidableEq, Repr

/-- The idioms as named in the rows. -/
def idiomTable : List (String × Idiom) :=
  [("bons", .bons), ("das", .das), ("strijdbijl", .strijdbijl), ("ijs", .ijs)]

/-- The forms as named in the rows. -/
def formTable : List (String × Form) :=
  [("active", .active), ("passive", .passive), ("nominalizedInfinitive", .nominalizedInfinitive),
    ("nominalization", .nominalization)]

/-- The idiom examples, the idiom and its form with the judgment of its idiomatic reading. -/
def idiomData : List (Idiom × Form × Judgment) :=
  Examples.all.filterMap fun d ↦ do
    pure (← d.parse? "idiom" idiomTable, ← d.parse? "form" formTable, d.judgment)

theorem length_idiomData : idiomData.length = 14 := by decide +kernel

/-- An idiom fits a domain when its reading survives exactly the forms its examples accept. -/
def Fits (i : Idiom) (d : Domain) : Prop :=
  ∀ r ∈ idiomData, r.1 = i → (r.2.2 = .acceptable ↔ Survives d r.2.1)

instance (i : Idiom) (d : Domain) : Decidable (Fits i d) :=
  inferInstanceAs (Decidable (∀ r ∈ idiomData, _))

theorem fits_bons_iff (d : Domain) : Fits .bons d ↔ d = .voice := by
  cases d <;> decide +kernel

theorem fits_das_iff (d : Domain) : Fits .das d ↔ d = .v := by
  cases d <;> decide +kernel

/-- **No domain fits.** The idioms that passivize and survive as nominalized infinitives should be
built from the root and its object alone, and then survive the suffixal nominalization too. -/
theorem not_fits (d : Domain) : ¬ Fits .strijdbijl d ∧ ¬ Fits .ijs d := by
  cases d <;> decide +kernel

end VanCraenenbroeck2014
