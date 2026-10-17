module

public import Linglib.Semantics.Evidential.Defs

/-!
# Saraguro Kichwa evidentiality

Saraguro Kichwa (Quechuan, Loja Province, Ecuador) has a three-way contrast in matrix
declaratives: direct *-rka* and reportative *-shka*, both also past tenses, and inferential
*-shi*. The discourse-sensitive enclitic *=mi*, whose analysis is contested across Quechuan
varieties, is not an evidential of this variety; Martínez Vera's analysis of it is in
`Studies/MartinezVera2026.lean`.

## References

* [aikhenvald-2004]
* [martinez-vera-2026]
-/

@[expose] public section

namespace Quechua.SaraguroKichwa.Evidentiality

open Evidential

/-- The direct past *-rka* marks direct perceptual evidence. -/
def rka : Evidential :=
  { morphs := [.suff "rka"], covers := {.visual, .sensory} }

/-- The reportative past *-shka* marks that the speaker was told. -/
def shka : Evidential :=
  { morphs := [.suff "shka"], covers := {.hearsay, .quotative} }

/-- The inferential *-shi* marks inference or assumption. -/
def shi : Evidential :=
  { morphs := [.suff "shi"], covers := {.inference, .assumption} }

/-- The evidentials of matrix declaratives are direct *-rka*, reportative *-shka* and inferential
*-shi*. -/
def evidentials : List Evidential := [rka, shka, shi]

end Quechua.SaraguroKichwa.Evidentiality
