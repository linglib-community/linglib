module

public import Linglib.Syntax.Number.Inverse
public import Linglib.Syntax.Person.Basic

/-!
# Taos verbal agreement prefixes

The Taos (Kiowa-Tanoan, Northern Tiwa) verb carries a prefix that agrees with up to three
arguments, the agent, the goal and the object, linearized in that order ([watkins-1984]).
Persons are first, second and third; the agreement categories are singular, dual, plural and
inverse (`Number.Inverse.Category`), the last being what a D head shows when its inherent and
natural number value one feature both ways ([harbour-2011]). Objects in the paradigm are third
person, the dummy object *no*, or a reflexive. The complete paradigm is Table 3 of the online
appendix to [middleton-2026], from [kontak-kunkel-1987] as corroborated by [harrington-1916],
transcribed here cell by cell; `form` looks a cell up.

## Main declarations

* `Taos.Cell`, `Taos.prefixes`, `Taos.form`: the paradigm and its lookup.
* `Taos.classI` to `Taos.classIV`: the four noun classes by inherent number, with the agreement
  category each shows for each natural number (`Taos.classI_category` and kin, the appendix's
  Table 21).

## Implementation notes

* Forms are given as the appendix prints them, with acute for high tone, circumflex for
  falling tone and an ogonek for nasalization; ∅ is the empty string. A cell with two free
  variants (*ku* ~ *mây*) has two rows, and `form` returns the first.
* The appendix's Table 3 lists reflexive objects for the one-argument prefixes only; the
  reflexives of possessive and ditransitive prefixes appear in its Table 16 and are not
  transcribed here.
* Rows whose label spans several numbers in the source (a bare person, or *1s/d*) are
  expanded to one row per cell; the cells two such labels both cover (*1 3i* and *1i 3*,
  *3 3i* and *3i 3*) appear once.

## References

* [J. Middleton, *A remark on the ordering of impoverishment rules: differences between Taos
  and Basque*][middleton-2026]
* [C. Kontak and J. Kunkel, *Grammar sketch of Northern Tiwa, Taos dialect*][kontak-kunkel-1987]
* [J. P. Harrington, *The ethnogeography of the Tewa Indians*][harrington-1916]
* [D. Harbour, *Valence and atomic number*][harbour-2011]
* [D. Harbour, *The Kiowa case for feature insertion*][harbour-2003]
* [L. J. Watkins, *A grammar of Kiowa*][watkins-1984]
-/

@[expose] public section

namespace Taos

open Number.Inverse

/-- An agent or goal: its person and agreement category. -/
abbrev Argument := Person × Category

/-- The object a prefix agrees with: the dummy object *no*, a third person object of some
category, or a reflexive. -/
inductive Object where
  | dummy
  | third (n : Category)
  | reflexive
  deriving DecidableEq, Repr

/-- A cell of the paradigm: the agent, the goal and the object, each possibly absent. -/
structure Cell where
  /-- The agent. -/
  agent : Option Argument
  /-- The goal. -/
  goal : Option Argument
  /-- The object. -/
  object : Option Object
  deriving DecidableEq, Repr

/-- The paradigm, Table 3 of the appendix to [middleton-2026]. -/
def prefixes : List (Cell × String) := [
  (⟨some (.first, .singular), none, none⟩, "o"),
  (⟨some (.first, .singular), none, some .dummy⟩, "ti"),
  (⟨some (.first, .singular), none, some (.third .singular)⟩, "ti"),
  (⟨some (.first, .singular), none, some (.third .inverse)⟩, "pi"),
  (⟨some (.first, .singular), none, some (.third .plural)⟩, "o"),
  (⟨some (.first, .singular), none, some .reflexive⟩, "tǫ"),
  (⟨some (.first, .dual), none, none⟩, "on"),
  (⟨some (.first, .dual), none, some .dummy⟩, "ón"),
  (⟨some (.first, .dual), none, some (.third .singular)⟩, "ón"),
  (⟨some (.first, .dual), none, some (.third .inverse)⟩, "opén"),
  (⟨some (.first, .dual), none, some (.third .plural)⟩, "kôn"),
  (⟨some (.first, .dual), none, some .reflexive⟩, "kôn"),
  (⟨some (.first, .inverse), none, none⟩, "i"),
  (⟨some (.first, .inverse), none, some .dummy⟩, "í"),
  (⟨some (.first, .inverse), none, some (.third .singular)⟩, "í"),
  (⟨some (.first, .inverse), none, some (.third .inverse)⟩, "ipí"),
  (⟨some (.first, .inverse), none, some (.third .plural)⟩, "kîw"),
  (⟨some (.first, .inverse), none, some .reflexive⟩, "kímo"),
  (⟨some (.second, .singular), none, none⟩, "ǫ"),
  (⟨some (.second, .singular), none, some .dummy⟩, "o"),
  (⟨some (.second, .singular), none, some (.third .singular)⟩, "o"),
  (⟨some (.second, .singular), none, some (.third .inverse)⟩, "í"),
  (⟨some (.second, .singular), none, some (.third .plural)⟩, "ki"),
  (⟨some (.second, .singular), none, some .reflexive⟩, "ǫ"),
  (⟨some (.second, .dual), none, none⟩, "mon"),
  (⟨some (.second, .dual), none, some .dummy⟩, "món"),
  (⟨some (.second, .dual), none, some (.third .singular)⟩, "món"),
  (⟨some (.second, .dual), none, some (.third .inverse)⟩, "mopén"),
  (⟨some (.second, .dual), none, some (.third .plural)⟩, "môn"),
  (⟨some (.second, .dual), none, some .reflexive⟩, "môn"),
  (⟨some (.second, .inverse), none, none⟩, "mo"),
  (⟨some (.second, .inverse), none, some .dummy⟩, "mó"),
  (⟨some (.second, .inverse), none, some (.third .singular)⟩, "mó"),
  (⟨some (.second, .inverse), none, some (.third .inverse)⟩, "mopí"),
  (⟨some (.second, .inverse), none, some (.third .plural)⟩, "môw"),
  (⟨some (.second, .inverse), none, some .reflexive⟩, "mómo"),
  (⟨some (.third, .singular), none, none⟩, ""),
  (⟨some (.third, .singular), none, some .dummy⟩, ""),
  (⟨some (.third, .singular), none, some (.third .singular)⟩, ""),
  (⟨some (.third, .singular), none, some (.third .inverse)⟩, "i"),
  (⟨some (.third, .singular), none, some (.third .plural)⟩, "u"),
  (⟨some (.third, .singular), none, some .reflexive⟩, "mo"),
  (⟨some (.third, .dual), none, none⟩, "on"),
  (⟨some (.third, .dual), none, some .dummy⟩, "ón"),
  (⟨some (.third, .dual), none, some (.third .singular)⟩, "ón"),
  (⟨some (.third, .dual), none, some (.third .inverse)⟩, "opén"),
  (⟨some (.third, .dual), none, some (.third .plural)⟩, "on"),
  (⟨some (.third, .dual), none, some .reflexive⟩, "on"),
  (⟨some (.third, .inverse), none, none⟩, "i"),
  (⟨some (.third, .inverse), none, some .dummy⟩, "í"),
  (⟨some (.third, .inverse), none, some (.third .singular)⟩, "í"),
  (⟨some (.third, .inverse), none, some (.third .inverse)⟩, "ipí"),
  (⟨some (.third, .inverse), none, some (.third .plural)⟩, "iw"),
  (⟨some (.third, .inverse), none, some .reflexive⟩, "ímó"),
  (⟨some (.third, .plural), none, none⟩, "u"),
  (⟨none, some (.first, .singular), some .dummy⟩, "ôn"),
  (⟨none, some (.first, .singular), some (.third .singular)⟩, "ôn"),
  (⟨none, some (.first, .singular), some (.third .inverse)⟩, "ónôm"),
  (⟨none, some (.first, .singular), some (.third .plural)⟩, "ónôw"),
  (⟨none, some (.first, .dual), some .dummy⟩, "kôn"),
  (⟨none, some (.first, .dual), some (.third .singular)⟩, "kónôm"),
  (⟨none, some (.first, .dual), some (.third .inverse)⟩, "kónôm"),
  (⟨none, some (.first, .dual), some (.third .plural)⟩, "kónôw"),
  (⟨none, some (.first, .inverse), some .dummy⟩, "kí"),
  (⟨none, some (.first, .inverse), some (.third .singular)⟩, "kí"),
  (⟨none, some (.first, .inverse), some (.third .inverse)⟩, "kîm"),
  (⟨none, some (.first, .inverse), some (.third .plural)⟩, "kîw"),
  (⟨none, some (.second, .singular), none⟩, "o"),
  (⟨none, some (.second, .singular), some .dummy⟩, "kǫ́"),
  (⟨none, some (.second, .singular), some (.third .singular)⟩, "kǫ́"),
  (⟨none, some (.second, .singular), some (.third .inverse)⟩, "kôm"),
  (⟨none, some (.second, .singular), some (.third .plural)⟩, "kǫ̂w"),
  (⟨none, some (.second, .dual), some .dummy⟩, "môn"),
  (⟨none, some (.second, .dual), some (.third .singular)⟩, "mónôm"),
  (⟨none, some (.second, .dual), some (.third .inverse)⟩, "mónôm"),
  (⟨none, some (.second, .dual), some (.third .plural)⟩, "mónôw"),
  (⟨none, some (.second, .inverse), some .dummy⟩, "mó"),
  (⟨none, some (.second, .inverse), some (.third .singular)⟩, "môm"),
  (⟨none, some (.second, .inverse), some (.third .inverse)⟩, "môm"),
  (⟨none, some (.second, .inverse), some (.third .plural)⟩, "môw"),
  (⟨none, some (.third, .singular), some .dummy⟩, "ǫ́"),
  (⟨none, some (.third, .singular), some (.third .singular)⟩, "ǫ"),
  (⟨none, some (.third, .singular), some (.third .inverse)⟩, "óm"),
  (⟨none, some (.third, .singular), some (.third .plural)⟩, "ǫ́w"),
  (⟨none, some (.third, .dual), some .dummy⟩, "ón"),
  (⟨none, some (.third, .dual), some (.third .singular)⟩, "ónôm"),
  (⟨none, some (.third, .dual), some (.third .inverse)⟩, "ónôm"),
  (⟨none, some (.third, .dual), some (.third .plural)⟩, "ónôw"),
  (⟨none, some (.third, .inverse), some .dummy⟩, "í"),
  (⟨none, some (.third, .inverse), some (.third .singular)⟩, "îm"),
  (⟨none, some (.third, .inverse), some (.third .inverse)⟩, "îm"),
  (⟨none, some (.third, .inverse), some (.third .plural)⟩, "îw"),
  (⟨some (.first, .singular), some (.second, .singular), none⟩, "o"),
  (⟨some (.first, .singular), some (.second, .singular), some .dummy⟩, "kǫ́"),
  (⟨some (.first, .singular), some (.second, .singular), some (.third .singular)⟩, "kǫ́"),
  (⟨some (.first, .singular), some (.second, .singular), some (.third .inverse)⟩, "kôm"),
  (⟨some (.first, .singular), some (.second, .singular), some (.third .plural)⟩, "kǫ̂w"),
  (⟨some (.first, .dual), some (.second, .singular), none⟩, "o"),
  (⟨some (.first, .dual), some (.second, .singular), some .dummy⟩, "kǫ́"),
  (⟨some (.first, .dual), some (.second, .singular), some (.third .singular)⟩, "kǫ́"),
  (⟨some (.first, .dual), some (.second, .singular), some (.third .inverse)⟩, "kôm"),
  (⟨some (.first, .dual), some (.second, .singular), some (.third .plural)⟩, "kǫ̂w"),
  (⟨some (.first, .inverse), some (.second, .singular), none⟩, "o"),
  (⟨some (.first, .inverse), some (.second, .singular), some .dummy⟩, "kǫ́"),
  (⟨some (.first, .inverse), some (.second, .singular), some (.third .singular)⟩, "kǫ́"),
  (⟨some (.first, .inverse), some (.second, .singular), some (.third .inverse)⟩, "kôm"),
  (⟨some (.first, .inverse), some (.second, .singular), some (.third .plural)⟩, "kǫ̂w"),
  (⟨some (.first, .singular), some (.second, .dual), none⟩, "mopén"),
  (⟨some (.first, .singular), some (.second, .dual), some .dummy⟩, "mopén"),
  (⟨some (.first, .singular), some (.second, .dual), some (.third .singular)⟩, "mopénôm"),
  (⟨some (.first, .singular), some (.second, .dual), some (.third .inverse)⟩, "mopénôm"),
  (⟨some (.first, .singular), some (.second, .dual), some (.third .plural)⟩, "mopénôw"),
  (⟨some (.first, .dual), some (.second, .dual), none⟩, "mopén"),
  (⟨some (.first, .dual), some (.second, .dual), some .dummy⟩, "mopén"),
  (⟨some (.first, .dual), some (.second, .dual), some (.third .singular)⟩, "mopénôm"),
  (⟨some (.first, .dual), some (.second, .dual), some (.third .inverse)⟩, "mopénôm"),
  (⟨some (.first, .dual), some (.second, .dual), some (.third .plural)⟩, "mopénôw"),
  (⟨some (.first, .inverse), some (.second, .dual), none⟩, "mopén"),
  (⟨some (.first, .inverse), some (.second, .dual), some .dummy⟩, "mopén"),
  (⟨some (.first, .inverse), some (.second, .dual), some (.third .singular)⟩, "mopénôm"),
  (⟨some (.first, .inverse), some (.second, .dual), some (.third .inverse)⟩, "mopénôm"),
  (⟨some (.first, .inverse), some (.second, .dual), some (.third .plural)⟩, "mopénôw"),
  (⟨some (.first, .singular), some (.second, .inverse), none⟩, "mopí"),
  (⟨some (.first, .singular), some (.second, .inverse), some .dummy⟩, "mopí"),
  (⟨some (.first, .singular), some (.second, .inverse), some (.third .singular)⟩, "mopîm"),
  (⟨some (.first, .singular), some (.second, .inverse), some (.third .inverse)⟩, "mopîm"),
  (⟨some (.first, .singular), some (.second, .inverse), some (.third .plural)⟩, "mopîw"),
  (⟨some (.first, .dual), some (.second, .inverse), none⟩, "mopí"),
  (⟨some (.first, .dual), some (.second, .inverse), some .dummy⟩, "mopí"),
  (⟨some (.first, .dual), some (.second, .inverse), some (.third .singular)⟩, "mopîm"),
  (⟨some (.first, .dual), some (.second, .inverse), some (.third .inverse)⟩, "mopîm"),
  (⟨some (.first, .dual), some (.second, .inverse), some (.third .plural)⟩, "mopîw"),
  (⟨some (.first, .inverse), some (.second, .inverse), none⟩, "mopí"),
  (⟨some (.first, .inverse), some (.second, .inverse), some .dummy⟩, "mopí"),
  (⟨some (.first, .inverse), some (.second, .inverse), some (.third .singular)⟩, "mopîm"),
  (⟨some (.first, .inverse), some (.second, .inverse), some (.third .inverse)⟩, "mopîm"),
  (⟨some (.first, .inverse), some (.second, .inverse), some (.third .plural)⟩, "mopîw"),
  (⟨some (.first, .singular), some (.third, .inverse), some .dummy⟩, "ipí"),
  (⟨some (.first, .singular), some (.third, .inverse), some (.third .singular)⟩, "ipîm"),
  (⟨some (.first, .singular), some (.third, .inverse), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.first, .singular), some (.third, .inverse), some (.third .plural)⟩, "ipîw"),
  (⟨some (.first, .dual), some (.third, .inverse), some .dummy⟩, "ipí"),
  (⟨some (.first, .dual), some (.third, .inverse), some (.third .singular)⟩, "ipîm"),
  (⟨some (.first, .dual), some (.third, .inverse), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.first, .dual), some (.third, .inverse), some (.third .plural)⟩, "ipîw"),
  (⟨some (.first, .inverse), some (.third, .inverse), some .dummy⟩, "ipí"),
  (⟨some (.first, .inverse), some (.third, .inverse), some (.third .singular)⟩, "ipîm"),
  (⟨some (.first, .inverse), some (.third, .inverse), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.first, .inverse), some (.third, .inverse), some (.third .plural)⟩, "ipîw"),
  (⟨some (.first, .singular), some (.third, .singular), some .dummy⟩, "tǫ́"),
  (⟨some (.first, .singular), some (.third, .singular), some (.third .singular)⟩, "tǫ"),
  (⟨some (.first, .singular), some (.third, .singular), some (.third .inverse)⟩, "tóm"),
  (⟨some (.first, .singular), some (.third, .singular), some (.third .plural)⟩, "tǫ́w"),
  (⟨some (.first, .singular), some (.third, .dual), some .dummy⟩, "opén"),
  (⟨some (.first, .singular), some (.third, .dual), some (.third .singular)⟩, "opénôm"),
  (⟨some (.first, .singular), some (.third, .dual), some (.third .inverse)⟩, "opénôm"),
  (⟨some (.first, .singular), some (.third, .dual), some (.third .plural)⟩, "opénôw"),
  (⟨some (.first, .dual), some (.third, .dual), some .dummy⟩, "opén"),
  (⟨some (.first, .dual), some (.third, .dual), some (.third .singular)⟩, "opénôm"),
  (⟨some (.first, .dual), some (.third, .dual), some (.third .inverse)⟩, "opénôm"),
  (⟨some (.first, .dual), some (.third, .dual), some (.third .plural)⟩, "opénôw"),
  (⟨some (.first, .dual), some (.third, .singular), some .dummy⟩, "opén"),
  (⟨some (.first, .dual), some (.third, .singular), some (.third .singular)⟩, "opénôm"),
  (⟨some (.first, .dual), some (.third, .singular), some (.third .inverse)⟩, "opénôm"),
  (⟨some (.first, .dual), some (.third, .singular), some (.third .plural)⟩, "opénôw"),
  (⟨some (.first, .inverse), some (.third, .singular), some .dummy⟩, "ipí"),
  (⟨some (.first, .inverse), some (.third, .singular), some (.third .singular)⟩, "ipîm"),
  (⟨some (.first, .inverse), some (.third, .singular), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.first, .inverse), some (.third, .singular), some (.third .plural)⟩, "ipîw"),
  (⟨some (.first, .inverse), some (.third, .dual), some .dummy⟩, "ipí"),
  (⟨some (.first, .inverse), some (.third, .dual), some (.third .singular)⟩, "ipîm"),
  (⟨some (.first, .inverse), some (.third, .dual), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.first, .inverse), some (.third, .dual), some (.third .plural)⟩, "ipîw"),
  (⟨some (.second, .singular), some (.first, .singular), none⟩, "mây"),
  (⟨some (.second, .singular), some (.first, .singular), some .dummy⟩, "mó"),
  (⟨some (.second, .singular), some (.first, .singular), some (.third .singular)⟩, "môm"),
  (⟨some (.second, .singular), some (.first, .singular), some (.third .inverse)⟩, "môm"),
  (⟨some (.second, .singular), some (.first, .singular), some (.third .plural)⟩, "môw"),
  (⟨some (.second, .dual), some (.first, .singular), none⟩, "mây"),
  (⟨some (.second, .dual), some (.first, .singular), some .dummy⟩, "mó"),
  (⟨some (.second, .dual), some (.first, .singular), some (.third .singular)⟩, "môm"),
  (⟨some (.second, .dual), some (.first, .singular), some (.third .inverse)⟩, "môm"),
  (⟨some (.second, .dual), some (.first, .singular), some (.third .plural)⟩, "môw"),
  (⟨some (.second, .inverse), some (.first, .singular), none⟩, "mây"),
  (⟨some (.second, .inverse), some (.first, .singular), some .dummy⟩, "mó"),
  (⟨some (.second, .inverse), some (.first, .singular), some (.third .singular)⟩, "môm"),
  (⟨some (.second, .inverse), some (.first, .singular), some (.third .inverse)⟩, "môm"),
  (⟨some (.second, .inverse), some (.first, .singular), some (.third .plural)⟩, "môw"),
  (⟨some (.second, .singular), some (.first, .dual), none⟩, "ku"),
  (⟨some (.second, .singular), some (.first, .dual), none⟩, "mây"),
  (⟨some (.second, .singular), some (.first, .dual), some .dummy⟩, "mó"),
  (⟨some (.second, .singular), some (.first, .dual), some (.third .singular)⟩, "môm"),
  (⟨some (.second, .singular), some (.first, .dual), some (.third .inverse)⟩, "môm"),
  (⟨some (.second, .singular), some (.first, .dual), some (.third .plural)⟩, "môw"),
  (⟨some (.second, .singular), some (.first, .inverse), none⟩, "ku"),
  (⟨some (.second, .singular), some (.first, .inverse), none⟩, "mây"),
  (⟨some (.second, .singular), some (.first, .inverse), some .dummy⟩, "mó"),
  (⟨some (.second, .singular), some (.first, .inverse), some (.third .singular)⟩, "môm"),
  (⟨some (.second, .singular), some (.first, .inverse), some (.third .inverse)⟩, "môm"),
  (⟨some (.second, .singular), some (.first, .inverse), some (.third .plural)⟩, "môw"),
  (⟨some (.second, .dual), some (.first, .dual), none⟩, "ku"),
  (⟨some (.second, .dual), some (.first, .dual), none⟩, "mây"),
  (⟨some (.second, .dual), some (.first, .dual), some .dummy⟩, "mó"),
  (⟨some (.second, .dual), some (.first, .dual), some (.third .singular)⟩, "môm"),
  (⟨some (.second, .dual), some (.first, .dual), some (.third .inverse)⟩, "môm"),
  (⟨some (.second, .dual), some (.first, .dual), some (.third .plural)⟩, "môw"),
  (⟨some (.second, .dual), some (.first, .inverse), none⟩, "ku"),
  (⟨some (.second, .dual), some (.first, .inverse), none⟩, "mây"),
  (⟨some (.second, .dual), some (.first, .inverse), some .dummy⟩, "mó"),
  (⟨some (.second, .dual), some (.first, .inverse), some (.third .singular)⟩, "môm"),
  (⟨some (.second, .dual), some (.first, .inverse), some (.third .inverse)⟩, "môm"),
  (⟨some (.second, .dual), some (.first, .inverse), some (.third .plural)⟩, "môw"),
  (⟨some (.second, .inverse), some (.first, .dual), none⟩, "ku"),
  (⟨some (.second, .inverse), some (.first, .dual), none⟩, "mây"),
  (⟨some (.second, .inverse), some (.first, .dual), some .dummy⟩, "mó"),
  (⟨some (.second, .inverse), some (.first, .dual), some (.third .singular)⟩, "môm"),
  (⟨some (.second, .inverse), some (.first, .dual), some (.third .inverse)⟩, "môm"),
  (⟨some (.second, .inverse), some (.first, .dual), some (.third .plural)⟩, "môw"),
  (⟨some (.second, .inverse), some (.first, .inverse), none⟩, "ku"),
  (⟨some (.second, .inverse), some (.first, .inverse), none⟩, "mây"),
  (⟨some (.second, .inverse), some (.first, .inverse), some .dummy⟩, "mó"),
  (⟨some (.second, .inverse), some (.first, .inverse), some (.third .singular)⟩, "môm"),
  (⟨some (.second, .inverse), some (.first, .inverse), some (.third .inverse)⟩, "môm"),
  (⟨some (.second, .inverse), some (.first, .inverse), some (.third .plural)⟩, "môw"),
  (⟨some (.second, .singular), some (.third, .singular), some .dummy⟩, "ǫ́"),
  (⟨some (.second, .singular), some (.third, .singular), some (.third .singular)⟩, "ǫ"),
  (⟨some (.second, .singular), some (.third, .singular), some (.third .inverse)⟩, "óm"),
  (⟨some (.second, .singular), some (.third, .singular), some (.third .plural)⟩, "ǫ́w"),
  (⟨some (.second, .singular), some (.third, .dual), some .dummy⟩, "mopén"),
  (⟨some (.second, .singular), some (.third, .dual), some (.third .singular)⟩, "mopénôm"),
  (⟨some (.second, .singular), some (.third, .dual), some (.third .inverse)⟩, "mopénôm"),
  (⟨some (.second, .singular), some (.third, .dual), some (.third .plural)⟩, "mopénôw"),
  (⟨some (.second, .singular), some (.third, .inverse), some .dummy⟩, "mopí"),
  (⟨some (.second, .singular), some (.third, .inverse), some (.third .singular)⟩, "mopîm"),
  (⟨some (.second, .singular), some (.third, .inverse), some (.third .inverse)⟩, "mopîm"),
  (⟨some (.second, .singular), some (.third, .inverse), some (.third .plural)⟩, "mopîw"),
  (⟨some (.second, .dual), some (.third, .inverse), some .dummy⟩, "mopí"),
  (⟨some (.second, .dual), some (.third, .inverse), some (.third .singular)⟩, "mopîm"),
  (⟨some (.second, .dual), some (.third, .inverse), some (.third .inverse)⟩, "mopîm"),
  (⟨some (.second, .dual), some (.third, .inverse), some (.third .plural)⟩, "mopîw"),
  (⟨some (.second, .dual), some (.third, .singular), some .dummy⟩, "mopén"),
  (⟨some (.second, .dual), some (.third, .singular), some (.third .singular)⟩, "mopénôm"),
  (⟨some (.second, .dual), some (.third, .singular), some (.third .inverse)⟩, "mopénôm"),
  (⟨some (.second, .dual), some (.third, .singular), some (.third .plural)⟩, "mopénôw"),
  (⟨some (.second, .dual), some (.third, .dual), some .dummy⟩, "mopén"),
  (⟨some (.second, .dual), some (.third, .dual), some (.third .singular)⟩, "mopénôm"),
  (⟨some (.second, .dual), some (.third, .dual), some (.third .inverse)⟩, "mopénôm"),
  (⟨some (.second, .dual), some (.third, .dual), some (.third .plural)⟩, "mopénôw"),
  (⟨some (.second, .inverse), some (.third, .singular), some .dummy⟩, "mopí"),
  (⟨some (.second, .inverse), some (.third, .singular), some (.third .singular)⟩, "mopîm"),
  (⟨some (.second, .inverse), some (.third, .singular), some (.third .inverse)⟩, "mopîm"),
  (⟨some (.second, .inverse), some (.third, .singular), some (.third .plural)⟩, "mopîw"),
  (⟨some (.second, .inverse), some (.third, .dual), some .dummy⟩, "mopí"),
  (⟨some (.second, .inverse), some (.third, .dual), some (.third .singular)⟩, "mopîm"),
  (⟨some (.second, .inverse), some (.third, .dual), some (.third .inverse)⟩, "mopîm"),
  (⟨some (.second, .inverse), some (.third, .dual), some (.third .plural)⟩, "mopîw"),
  (⟨some (.second, .inverse), some (.third, .inverse), some .dummy⟩, "mopí"),
  (⟨some (.second, .inverse), some (.third, .inverse), some (.third .singular)⟩, "mopîm"),
  (⟨some (.second, .inverse), some (.third, .inverse), some (.third .inverse)⟩, "mopîm"),
  (⟨some (.second, .inverse), some (.third, .inverse), some (.third .plural)⟩, "mopîw"),
  (⟨some (.third, .singular), some (.third, .inverse), some .dummy⟩, "ipí"),
  (⟨some (.third, .singular), some (.third, .inverse), some (.third .singular)⟩, "ipîm"),
  (⟨some (.third, .singular), some (.third, .inverse), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.third, .singular), some (.third, .inverse), some (.third .plural)⟩, "ipîw"),
  (⟨some (.third, .dual), some (.third, .inverse), some .dummy⟩, "ipí"),
  (⟨some (.third, .dual), some (.third, .inverse), some (.third .singular)⟩, "ipîm"),
  (⟨some (.third, .dual), some (.third, .inverse), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.third, .dual), some (.third, .inverse), some (.third .plural)⟩, "ipîw"),
  (⟨some (.third, .inverse), some (.third, .inverse), some .dummy⟩, "ipí"),
  (⟨some (.third, .inverse), some (.third, .inverse), some (.third .singular)⟩, "ipîm"),
  (⟨some (.third, .inverse), some (.third, .inverse), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.third, .inverse), some (.third, .inverse), some (.third .plural)⟩, "ipîw"),
  (⟨some (.third, .singular), some (.third, .singular), some .dummy⟩, "ǫ́"),
  (⟨some (.third, .singular), some (.third, .singular), some (.third .singular)⟩, "ǫ"),
  (⟨some (.third, .singular), some (.third, .singular), some (.third .inverse)⟩, "óm"),
  (⟨some (.third, .singular), some (.third, .singular), some (.third .plural)⟩, "ǫ́w"),
  (⟨some (.third, .singular), some (.third, .dual), some .dummy⟩, "opén"),
  (⟨some (.third, .singular), some (.third, .dual), some (.third .singular)⟩, "opénôm"),
  (⟨some (.third, .singular), some (.third, .dual), some (.third .inverse)⟩, "opénôm"),
  (⟨some (.third, .singular), some (.third, .dual), some (.third .plural)⟩, "opénôw"),
  (⟨some (.third, .dual), some (.third, .dual), some .dummy⟩, "opén"),
  (⟨some (.third, .dual), some (.third, .dual), some (.third .singular)⟩, "opénôm"),
  (⟨some (.third, .dual), some (.third, .dual), some (.third .inverse)⟩, "opénôm"),
  (⟨some (.third, .dual), some (.third, .dual), some (.third .plural)⟩, "opénôw"),
  (⟨some (.third, .dual), some (.third, .singular), some .dummy⟩, "opén"),
  (⟨some (.third, .dual), some (.third, .singular), some (.third .singular)⟩, "opénôm"),
  (⟨some (.third, .dual), some (.third, .singular), some (.third .inverse)⟩, "opénôm"),
  (⟨some (.third, .dual), some (.third, .singular), some (.third .plural)⟩, "opénôw"),
  (⟨some (.third, .inverse), some (.third, .singular), some .dummy⟩, "ipí"),
  (⟨some (.third, .inverse), some (.third, .singular), some (.third .singular)⟩, "ipîm"),
  (⟨some (.third, .inverse), some (.third, .singular), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.third, .inverse), some (.third, .singular), some (.third .plural)⟩, "ipîw"),
  (⟨some (.third, .inverse), some (.third, .dual), some .dummy⟩, "ipí"),
  (⟨some (.third, .inverse), some (.third, .dual), some (.third .singular)⟩, "ipîm"),
  (⟨some (.third, .inverse), some (.third, .dual), some (.third .inverse)⟩, "ipîm"),
  (⟨some (.third, .inverse), some (.third, .dual), some (.third .plural)⟩, "ipîw")
]

/-- The prefix of a cell. -/
def form (c : Cell) : Option String := prefixes.lookup c

/-! ### Noun classes

The four classes by inherent number ([harbour-2003], [harbour-2011]; appendix Table 21):
'one or two', 'two or more', 'two', and 'any number'. -/

/-- Class I, inherently `[+minimal]`: 'one or two'. -/
def classI : Valuation := ⟨∅, {true}⟩

/-- Class II, inherently `[−atomic]`: 'two or more'. -/
def classII : Valuation := ⟨{false}, ∅⟩

/-- Class III, inherently `[−atomic +minimal]`: 'two'. -/
def classIII : Valuation := ⟨{false}, {true}⟩

/-- Class IV, with no inherent number: 'any number'. -/
def classIV : Valuation := ∅

/-- Class I agrees singular, dual, inverse for one, two, and more referents. -/
theorem classI_category :
    (classI.agree (.ofNumber .singular)).category = some .singular ∧
      (classI.agree (.ofNumber .dual)).category = some .dual ∧
      (classI.agree (.ofNumber .plural)).category = some .inverse := by
  decide

theorem classII_category :
    (classII.agree (.ofNumber .singular)).category = some .inverse ∧
      (classII.agree (.ofNumber .dual)).category = some .dual ∧
      (classII.agree (.ofNumber .plural)).category = some .plural := by
  decide

theorem classIII_category :
    (classIII.agree (.ofNumber .singular)).category = some .inverse ∧
      (classIII.agree (.ofNumber .dual)).category = some .dual ∧
      (classIII.agree (.ofNumber .plural)).category = some .inverse := by
  decide

theorem classIV_category :
    (classIV.agree (.ofNumber .singular)).category = some .singular ∧
      (classIV.agree (.ofNumber .dual)).category = some .dual ∧
      (classIV.agree (.ofNumber .plural)).category = some .plural := by
  decide

/-- Every inverse valuation of Table 21 contains the dual's values: the dual's features are a
proper part of the inverse's. -/
theorem dual_le_inverse :
    ∀ c ∈ [classI, classII, classIII, classIV], ∀ n ∈ [Number.singular, .dual, .plural],
    (c.agree (.ofNumber n)).IsInverse →
      (Valuation.ofNumber .dual).atomic ⊆ (c.agree (.ofNumber n)).atomic ∧
        (Valuation.ofNumber .dual).minimal ⊆ (c.agree (.ofNumber n)).minimal := by
  decide

end Taos
