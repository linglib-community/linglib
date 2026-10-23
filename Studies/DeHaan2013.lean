module

public import Linglib.Data.WALS.Features.F77A
public import Studies.Aikhenvald2004
public import Linglib.Fragments.English.Evidentiality
public import Linglib.Fragments.Finnish.Evidentiality
public import Linglib.Fragments.Georgian.Evidentiality
public import Linglib.Fragments.German.Evidentiality
public import Linglib.Fragments.Japanese.Evidentiality
public import Linglib.Fragments.Korean.Evidentiality
public import Linglib.Fragments.Mandarin.Evidentiality
public import Linglib.Fragments.Romance.French.Evidentiality

/-!
# de Haan (2013): Semantic Distinctions of Evidentiality

This file formalizes de Haan's WALS map of the semantic distinctions of evidentiality, which
codes a language as having no grammatical evidentials, indirect evidentials only, or direct and
indirect ones. A direct evidential marks sensory evidence, an indirect one inference or report.
Only grammaticalized evidentials count, modal verbs, auxiliaries and particles among them, and no
language in the sample has direct evidentials without indirect ones.

The value of an inventory is read off what its evidentials cover (`value?`), and an inventory
of direct evidentials alone has none. On the Fragment languages the map never records fewer
distinctions than the inventory (`exists_mem_lookup_walsCode`). Where the two differ, the
inventory has no evidentials, or no direct one, because the Fragments follow Aikhenvald, who
counts modal and mood forms and the Georgian perfect as evidentiality strategies and reads the
Turkish and Bulgarian unmarked pasts as evidentiality-neutral. Taking the Turkish witnessed past
as a direct evidential, as the chapter glosses it, gives the map's value and turns Aikhenvald's
A2 system into an A1 (`turkish_di`). An inventory realizing one of Aikhenvald's kinds is off the
map exactly when the kind is A5, auditory against everything else (`value?_eq_none_iff`); its
one language, Euchee, is on the map without evidentials, coded after Wagner's grammar, which
takes the auditory *-ke* for a locative (`euchee`).

## Implementation notes

The map codes Georgian with direct and indirect evidentials, although the companion chapter on
coding says that the Georgian aorist, unlike the perfect, has not been formalized as a direct
evidential. Kashaya is placed on the map by the paradigm of a spontaneous remark.

## References

* [de-haan-2013]
* [de-haan-2013b]
* [aikhenvald-2004]
* [willett-1988]
* [linn-2000]
* [wagner-1934]
-/

@[expose] public section

namespace DeHaan2013

open Evidential Data.WALS.F77A

/-! ### The map's values -/

/-- The value on the map of the coverages of a language's evidentials. Some indirect evidential
covers inference or report, a parameter outside attested evidence, and a direct one covers
attested evidence alone; coverages that are all direct have no value. -/
def ofCovers (cs : List (Finset Parameter)) : Option EvidentialityDistinctions :=
  if ∃ c ∈ cs, ¬ c ⊆ EvidenceType.attested.block then
    some <| if ∃ c ∈ cs, c.Nonempty ∧ c ⊆ EvidenceType.attested.block then .directAndIndirect
      else .indirectOnly
  else if ∃ c ∈ cs, c.Nonempty then none else some .noGrammaticalEvidentials

/-- The value of an inventory on the map. -/
def value? (es : List Evidential) : Option EvidentialityDistinctions := ofCovers (es.map covers)

theorem ofCovers_perm {cs cs' : List (Finset Parameter)} (h : cs.Perm cs') :
    ofCovers cs = ofCovers cs' := by
  simp only [ofCovers, h.mem_iff]

theorem ofCovers_rows_eq_none_iff (k : Aikhenvald2004.Kind) :
    ∀ r ∈ k.rows, ofCovers (r.map Prod.snd) = none ↔ k = .A5 := by
  revert k; decide +kernel

theorem value?_eq_none_iff {es : List Evidential} {k : Aikhenvald2004.Kind}
    (h : Aikhenvald2004.Realizes es k) : value? es = none ↔ k = .A5 := by
  obtain ⟨r, hr, hp⟩ := h
  rw [value?, ofCovers_perm hp]
  exact ofCovers_rows_eq_none_iff k r hr

/-! ### The Fragment languages -/

/-- The Fragment languages on the map. -/
inductive Language
  | english | mandarin | finnish | german | french | japanese | korean | georgian
  | westGreenlandic | abkhaz | turkish | bulgarian | aymara | tariana | tuyuca | kashaya
  deriving DecidableEq, Repr, Fintype

/-- The WALS code of a language. -/
def Language.walsCode : Language → String
  | .english => "eng" | .mandarin => "mnd" | .finnish => "fin" | .german => "ger"
  | .french => "fre" | .japanese => "jpn" | .korean => "kor" | .georgian => "geo"
  | .westGreenlandic => "grw" | .abkhaz => "abk" | .turkish => "tur" | .bulgarian => "bul"
  | .aymara => "aym" | .tariana => "tar" | .tuyuca => "tuy" | .kashaya => "ksh"

/-- A language's evidentials, from its Fragment; for Kashaya, those of a spontaneous remark. -/
def Language.evidentials : Language → List Evidential
  | .english => English.Evidentiality.evidentials
  | .mandarin => Mandarin.Evidentiality.evidentials
  | .finnish => Finnish.Evidentiality.evidentials
  | .german => German.Evidentiality.evidentials
  | .french => French.Evidentiality.evidentials
  | .japanese => Japanese.Evidentiality.evidentials
  | .korean => Korean.Evidentiality.evidentials
  | .georgian => Georgian.Evidentiality.evidentials
  | .westGreenlandic => WestGreenlandic.Evidentiality.evidentials
  | .abkhaz => Abkhaz.Evidentiality.evidentials
  | .turkish => Turkish.Evidentiality.evidentials
  | .bulgarian => Bulgarian.Evidentiality.evidentials
  | .aymara => Aymara.Evidentiality.evidentials
  | .tariana => Tariana.Evidentiality.evidentials
  | .tuyuca => Tuyuca.Evidentiality.evidentials
  | .kashaya => Kashaya.Evidentiality.paradigm .spontaneous .imperfective

theorem value?_isSome (l : Language) : (value? l.evidentials).isSome := by
  revert l; decide +kernel

theorem exists_mem_lookup_walsCode (l : Language) :
    ∃ v ∈ allData.lookup l.walsCode, value? l.evidentials = some v ∨
      l.evidentials = [] ∧ v ≠ .noGrammaticalEvidentials ∨
      value? l.evidentials = some .indirectOnly ∧ v = .directAndIndirect := by
  revert l; decide +kernel

theorem westGreenlandic :
    value? WestGreenlandic.Evidentiality.evidentials = allData.lookup "grw" := by
  decide +kernel

/-- The Turkish witnessed past *-dI*, which the chapter glosses as a direct evidential and
Aikhenvald reads as evidentiality-neutral, taken as a firsthand term for what the speaker saw. -/
def di : Evidential := { morphs := [.suff "DI"], covers := {.visual} }

theorem turkish_di :
    value? (di :: Turkish.Evidentiality.evidentials) = allData.lookup "tur" ∧
      Aikhenvald2004.Realizes (di :: Turkish.Evidentiality.evidentials) .A1 := by
  decide +kernel

theorem euchee :
    value? [Aikhenvald2004.eucheeKe] = none ∧
      allData.lookup "yuc" = some .noGrammaticalEvidentials :=
  ⟨(value?_eq_none_iff Aikhenvald2004.euchee).2 rfl, by decide +kernel⟩

end DeHaan2013
