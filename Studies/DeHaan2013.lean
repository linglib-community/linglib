module

public import Linglib.Data.WALS.Features.F77A
public import Studies.Aikhenvald2004
public import Linglib.Fragments.English.Evidentiality
public import Linglib.Fragments.Georgian.Evidentiality
public import Linglib.Fragments.German.Evidentiality
public import Linglib.Fragments.Japanese.Evidentiality
public import Linglib.Fragments.Korean.Evidentiality
public import Linglib.Fragments.Romance.French.Evidentiality

/-!
# de Haan (2013): Semantic Distinctions of Evidentiality

De Haan's WALS map codes a language as having no grammatical evidentials, indirect ones only, or
direct and indirect ones, counting every grammaticalized evidential, auxiliaries and particles
among them; [an inventory of direct evidentials alone has no value](##value?_eq_none_iff). The
map's value of each Fragment language is [that of what de Haan counts](##lookup_walsCode): its
evidentials, its evidentiality strategies, and for Turkish, Bulgarian and Georgian a past read as
witnessed, which [makes an A1 system](##realizes_A1). Aikhenvald counts the evidentials alone, so
the map agrees with her [where a language has neither of the others](##lookup_walsCode_of_nil).
Of her kinds only A5 is off the map, and its one language, Euchee, is [coded without
evidentials](##euchee), after a grammar that takes the auditory *-ke* for a locative.

## Implementation notes

The pasts read as witnessed are this file's terms, not Fragment entries, since Aikhenvald reads
the Turkish *-dI* and the Bulgarian aorist as evidentiality-neutral. The chapter glosses *-dI* as
a direct evidential and lists Georgian among the languages contrasting witnessed with unwitnessed
pasts; the map codes Bulgarian after Friedman, whose confirmative past Aikhenvald takes for the
firsthand of an A1 system. The strategies the Fragments record are grammatical forms, which de
Haan counts; a complementation strategy, biclausal, he would not. Kashaya is placed on the map by
the paradigm of a spontaneous remark.

## TODO

Finnish, which the chapter says has evidentials derived from modal verbs, is left out until a
Fragment records them.

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

/-- An inventory is off the map exactly when it has a direct evidential and no indirect one. -/
theorem value?_eq_none_iff {es : List Evidential} :
    value? es = none ↔
      (∃ e ∈ es, e.IsDirect) ∧ ∀ e ∈ es, e.covers ⊆ EvidenceType.attested.block := by
  rw [value?, ofCovers]
  split_ifs with h₁ h₂
  · obtain ⟨_, hc, hn⟩ := h₁
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    simp only [false_iff, not_and]
    exact fun _ h ↦ hn (h e he)
  · have h : ∀ e ∈ es, e.covers ⊆ EvidenceType.attested.block := fun e he ↦
      by_contra fun hn ↦ h₁ ⟨_, List.mem_map_of_mem he, hn⟩
    obtain ⟨_, hc, hn⟩ := h₂
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    simp only [true_iff, IsOfType]
    exact ⟨⟨e, he, hn, h e he⟩, h⟩
  · simp only [false_iff, not_and]
    rintro ⟨e, he, hn, -⟩ -
    exact h₂ ⟨_, List.mem_map_of_mem he, hn⟩

theorem ofCovers_perm {cs cs' : List (Finset Parameter)} (h : cs.Perm cs') :
    ofCovers cs = ofCovers cs' := by
  simp only [ofCovers, h.mem_iff]

private theorem ofCovers_rows_eq_none_iff (k : Aikhenvald2004.Kind) :
    ∀ r ∈ k.rows, ofCovers (r.map Prod.snd) = none ↔ k = .A5 := by
  revert k; decide +kernel

theorem value?_eq_none_iff_of_realizes {es : List Evidential} {k : Aikhenvald2004.Kind}
    (h : Aikhenvald2004.Realizes es k) : value? es = none ↔ k = .A5 := by
  obtain ⟨r, hr, hp⟩ := h
  rw [value?, ofCovers_perm hp]
  exact ofCovers_rows_eq_none_iff k r hr

/-! ### The Fragment languages -/

/-- The Fragment languages on the map. -/
inductive Language
  | english | german | french | japanese | korean | georgian | westGreenlandic | abkhaz
  | turkish | bulgarian | aymara | tariana | tuyuca | kashaya
  deriving DecidableEq, Repr, Fintype

/-- The WALS code of a language. -/
def Language.walsCode : Language → String
  | .english => "eng" | .german => "ger" | .french => "fre" | .japanese => "jpn"
  | .korean => "kor" | .georgian => "geo" | .westGreenlandic => "grw" | .abkhaz => "abk"
  | .turkish => "tur" | .bulgarian => "bul" | .aymara => "aym" | .tariana => "tar"
  | .tuyuca => "tuy" | .kashaya => "ksh"

/-- A language's evidentials, from its Fragment; for Kashaya, those of a spontaneous remark. -/
def Language.evidentials : Language → List Evidential
  | .english => English.Evidentiality.evidentials
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

/-- A language's evidentiality strategies, from its Fragment; none where it records none. -/
def Language.strategies : Language → List Evidential
  | .german => German.Evidentiality.strategies
  | .french => French.Evidentiality.strategies
  | .georgian => Georgian.Evidentiality.strategies
  | .english | .japanese | .korean | .westGreenlandic | .abkhaz | .turkish | .bulgarian
  | .aymara | .tariana | .tuyuca | .kashaya => []

/-- The Turkish past *-dI*, which the chapter glosses as a direct evidential, taken as a
firsthand term for what the speaker saw. -/
def di : Evidential := { morphs := [.suff "DI"], covers := {.visual} }

/-- A past unmarked against the non-firsthand, taken as a firsthand term. -/
def unmarkedPast : Evidential := { morphs := [], covers := {.visual, .sensory} }

/-- A language's past read as witnessed: the Turkish *-dI*, and the Bulgarian and Georgian
aorists. -/
def Language.witnessed : Language → List Evidential
  | .turkish => [di]
  | .bulgarian | .georgian => [unmarkedPast]
  | _ => []

/-- The evidentials de Haan counts in a language. -/
def Language.counted (l : Language) : List Evidential :=
  l.witnessed ++ l.evidentials ++ l.strategies

/-- The map's value of each Fragment language is the value of the evidentials de Haan counts in
it: its evidentials, its evidentiality strategies, and a past read as witnessed. -/
theorem lookup_walsCode (l : Language) : allData.lookup l.walsCode = value? l.counted := by
  revert l; decide +kernel

/-- The map's value of a language with no evidentiality strategies and no past read as witnessed
is the value of its evidentials proper. -/
theorem lookup_walsCode_of_nil {l : Language} (h : l.strategies = []) (h' : l.witnessed = []) :
    allData.lookup l.walsCode = value? l.evidentials := by
  simp [lookup_walsCode, Language.counted, h, h']

/-- Read with its past as witnessed, each of Turkish, Bulgarian and Georgian has an A1 system,
firsthand against non-firsthand. -/
theorem realizes_A1 :
    ∀ l ∈ [Language.turkish, .bulgarian, .georgian], Aikhenvald2004.Realizes l.counted .A1 := by
  decide +kernel

/-- Euchee, the one language with an A5 system, auditory against everything else, has no value
on the map for its inventory and is coded without evidentials. -/
theorem euchee :
    value? [Aikhenvald2004.eucheeKe] = none ∧
      allData.lookup "yuc" = some .noGrammaticalEvidentials :=
  ⟨(value?_eq_none_iff_of_realizes Aikhenvald2004.euchee).2 rfl, by decide +kernel⟩

end DeHaan2013
