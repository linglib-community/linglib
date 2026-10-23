module

public import Linglib.Syntax.Case.Basic
public import Linglib.Data.UD.Features
public import Mathlib.Data.Fintype.Pi

/-!
# Modern Standard Arabic case

Modern Standard Arabic has three cases, the nominative (*rafʿ*), the genitive (*jarr*) and the
accusative (*naSb*), marked by a suffix at the end of a noun or adjective: in the base
declension *-u*, *-i* and *-a*, followed on an indefinite by nunation, a final *-n*
([ryding-2005] ch. 7 §5, p. 166). The spoken varieties do not mark case (p. 166), so the case
system is that of the written language.

A noun is in one of three states. It takes the definite article *al-*, or it is annexed, the first
term of a construct (*ʾiDaafa*) or a noun with a possessive suffix, with "neither the definite
article nor nunation" (ch. 8 §1.2.1, p. 211), or it takes nunation (ch. 7 §4, p. 156). The state is
a form and not a meaning: an annexed noun is definite or indefinite with the noun it annexes, and so
"looks definite because it does not have nunation, but it is not definite" when that noun is
indefinite (p. 160, fn. 40), and masculine names such as *muHammad-un* are "semantically definite,
but morphologically indefinite" (p. 164). The Universal Dependencies tag for definiteness, the value
of a token's definiteness feature, keeps the three states apart, the annexed noun being UD's
construct state ([de-marneffe-zeman-2021]).

A declension is "a class of substantives (nouns or adjectives) that exhibits similar
inflectional markings for case and definiteness" (§5.4, p. 182), and Ryding sorts nouns and
adjectives into eight of them (pp. 182–183), a classification she calls her own, "not
standardized" (p. 167). A declension is therefore given here by its endings, and a noun by its
stem and its declension, its form being the article, the stem and the ending. What a
declension's endings do not distinguish no noun of the declension distinguishes
(`Noun.form_eq_form_iff`). The triptote gives each case its own ending (§5.4.1, p. 183). The
dual, the two sound plurals and the indefinite diptote have one ending for the genitive and the
accusative, and "are considered to exhibit all three cases; it is just that the genitive and
accusative have exactly the same form" (§5.4.2, p. 187). The defectives have one for the
nominative and the genitive (§5.4.3, p. 197), and the indeclinables and the invariables one for
all three cases (§§5.4.4–5.4.5, pp. 199–200).

## Main declarations

* `Arabic.ModernStandard.Case`: the three cases, in the order of the grammars.
* `Arabic.ModernStandard.State`, `article`, `State.toUD`: the three states, the article of each,
  and their Universal Dependencies tags.
* `Arabic.ModernStandard.Declension`: a declension, by its endings, and the eight declensions.
* `Arabic.ModernStandard.Noun`, `Noun.form`: a noun by its stem and declension, and its form in
  each state and case.
* `Noun.form_eq_form_iff`, `Noun.injective_form_iff`: a noun distinguishes the cases its
  declension's endings distinguish.
* `Declension.triptote_injective`, `Declension.twoWay_eq_iff`, `Declension.diptote_eq_iff`,
  `Declension.defective_eq_iff`, `Declension.caseless_eq`: the cases each declension merges.
* `Declension.nunation`, `Declension.definite_eq_indefinite`, `Declension.construct_eq_definite`,
  `Declension.nuun_deletion`: how the endings mark the states.

## Implementation notes

The endings of the definite and the indefinite are read off the paradigm tables of §5.4
(pp. 184–201), one noun to a declension, and each noun's forms are checked against its table.
The annexed endings are the definite ones less the final *nuun* of the dual and the sound
masculine plural (pp. 189, 191, 211), checked against Ryding's examples of annexed nouns.

Ryding hyphenates morph boundaries, but not consistently (*al-bayt-u* and *bayt-u-n* beside
*al-muHaamii*, *mustashfan*), so the forms are her transliterations without the hyphens inside
the word, the boundary between stem and ending being given by the stem. The endings of the
defectives and the indeclinables are the ones Ryding names, *-in* (p. 198, fn. 99), *-ii*, *-an*
and *-aa* (p. 169, fn. 55); the ending of the invariables is their *-aa* (p. 169, fn. 55), and
the sound feminine plural's ending includes its suffix *-aat*, on which it is marked for case
(p. 191).

Ryding numbers the declensions but gives the two sound plurals different numbers on p. 183 and
p. 187, so the declensions go by name here. Her defective declension also takes in diptote
plurals such as *maqaah-in* 'cafés', whose indefinite accusative *maqaah-iy-a* has no nunation
(p. 198); `Declension.defective` is the declension of the singular *muHaam-in*. The five nouns
of the triptote, *ʾab* 'father' and the rest, which lengthen the case vowel when annexed
(pp. 186–187), are not represented.

## References

* [de-marneffe-zeman-2021]
* [ryding-2005]
-/

@[expose] public section

namespace Arabic.ModernStandard

/-- The three cases, in the order of the grammars. -/
inductive Case where
  /-- The nominative, *rafʿ*. -/
  | nom
  /-- The genitive, *jarr*. -/
  | gen
  /-- The accusative, *naSb*. -/
  | acc
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | gen => .gen
  | acc => .acc

/-- The three states of a noun, by how it is marked. -/
inductive State where
  /-- With the definite article. -/
  | definite
  /-- Annexed: the first term of a construct, or with a possessive suffix (p. 189). -/
  | construct
  /-- With nunation. -/
  | indefinite
  deriving DecidableEq, Fintype, Repr

/-- The Universal Dependencies tag of a state, `Cons`, UD's construct state, for an annexed
noun. -/
def State.toUD : State → UD.Definite
  | .definite => .Def
  | .construct => .Cons
  | .indefinite => .Ind

theorem State.toUD_injective : Function.Injective State.toUD := by
  decide

/-- The definite article *al-*, which a noun takes in the definite state and in no other. -/
def article : State → String
  | .definite => "al-"
  | .construct | .indefinite => ""

/-- The forms of the three cases, in the order of the grammars. -/
def forms (nom gen acc : String) : Case → String
  | .nom => nom
  | .gen => gen
  | .acc => acc

/-- A declension, by its endings: the ending of each case in each state ([ryding-2005]
p. 182). -/
abbrev Declension := State → Case → String

namespace Declension

/-- The triptote, with *-u*, *-i* and *-a*, followed by nunation on an indefinite (pp. 183–184). -/
def triptote : Declension
  | .definite | .construct => forms "u" "i" "a"
  | .indefinite => forms "un" "in" "an"

/-- The dual, nominative *-aani*, genitive and accusative *-ayni* (p. 188), which lose their
*-ni* when annexed (p. 189). -/
def dual : Declension
  | .definite | .indefinite => forms "aani" "ayni" "ayni"
  | .construct => forms "aa" "ay" "ay"

/-- The sound feminine plural in *-aat*, with *-u* and *-i* but no *-a* (p. 191). -/
def soundFemininePlural : Declension
  | .definite | .construct => forms "aatu" "aati" "aati"
  | .indefinite => forms "aatun" "aatin" "aatin"

/-- The sound masculine plural, nominative *-uuna*, genitive and accusative *-iina* (p. 190),
which lose their *-na* when annexed (p. 191). -/
def soundMasculinePlural : Declension
  | .definite | .indefinite => forms "uuna" "iina" "iina"
  | .construct => forms "uu" "ii" "ii"

/-- The diptote, without nunation and, when indefinite, with *-a* for the genitive as for the
accusative (pp. 192–193). -/
def diptote : Declension
  | .definite | .construct => forms "u" "i" "a"
  | .indefinite => forms "u" "a" "a"

/-- The defective, of words from roots ending in a semivowel, with one ending for the nominative
and the genitive (pp. 197–198). -/
def defective : Declension
  | .definite | .construct => forms "ii" "ii" "iya"
  | .indefinite => forms "in" "in" "iyan"

/-- The indeclinable, of nouns in *ʾalif maqSuura*, which mark definiteness but not case
(p. 199). -/
def indeclinable : Declension
  | .definite | .construct => fun _ ↦ "aa"
  | .indefinite => fun _ ↦ "an"

/-- The invariable, of nouns that mark neither case nor definiteness (p. 200). -/
def invariable : Declension := fun _ _ ↦ "aa"

end Declension

/-- A noun by its stem and its declension. -/
structure Noun where
  /-- The gloss. -/
  gloss : String
  /-- The stem, to which the article is prefixed and the ending suffixed. -/
  stem : String
  /-- The declension. -/
  declension : Declension

namespace Noun

/-- The form of a noun in a state and a case: the article, the stem and the ending of its
declension (p. 166). -/
def form (n : Noun) (s : State) (c : Case) : String :=
  article s ++ n.stem ++ n.declension s c

variable {n : Noun} {s : State} {c c' : Case}

@[simp]
theorem form_eq_form_iff : n.form s c = n.form s c' ↔ n.declension s c = n.declension s c' :=
  String.append_right_inj _

theorem injective_form_iff : Function.Injective (n.form s) ↔ Function.Injective (n.declension s) :=
  Function.Injective.of_comp_iff (fun _ _ ↦ (String.append_right_inj _).1) _

end Noun

/-! ### The nouns of Ryding's tables -/

/-- *bayt* 'house', triptote. -/
def bayt : Noun := ⟨"house", "bayt", .triptote⟩

/-- *bayt-aani* 'two houses', the dual of *bayt*, its suffix added "on the singular stem"
(p. 188). -/
def baytaani : Noun := { bayt with gloss := "two houses", declension := .dual }

/-- *intixaabaat* 'elections', sound feminine plural. -/
def intixaabaat : Noun := ⟨"elections", "intixaab", .soundFemininePlural⟩

/-- *muwaaTin-uuna* 'citizens', sound masculine plural. -/
def muwaatinuuna : Noun := ⟨"citizens", "muwaaTin", .soundMasculinePlural⟩

/-- *SaHraaʾ* 'desert', diptote. -/
def sahraa : Noun := ⟨"desert", "SaHraaʾ", .diptote⟩

/-- *muHaam-in* 'lawyer', defective. -/
def muhaamin : Noun := ⟨"lawyer", "muHaam", .defective⟩

/-- *mustashfan* 'hospital', indeclinable. -/
def mustashfan : Noun := ⟨"hospital", "mustashf", .indeclinable⟩

/-- *shakwaa* 'complaint', invariable. -/
def shakwaa : Noun := ⟨"complaint", "shakw", .invariable⟩

/-- *bayt* declines as in Ryding's table (p. 184). -/
example : bayt.form .definite = forms "al-baytu" "al-bayti" "al-bayta" ∧
    bayt.form .indefinite = forms "baytun" "baytin" "baytan" := by
  decide

/-- *bayt-aani* declines as in Ryding's table (p. 188). -/
example : baytaani.form .definite = forms "al-baytaani" "al-baytayni" "al-baytayni" ∧
    baytaani.form .indefinite = forms "baytaani" "baytayni" "baytayni" := by
  decide

/-- *intixaabaat* declines as in Ryding's table (p. 191). -/
example :
    intixaabaat.form .definite = forms "al-intixaabaatu" "al-intixaabaati" "al-intixaabaati" ∧
      intixaabaat.form .indefinite = forms "intixaabaatun" "intixaabaatin" "intixaabaatin" := by
  decide

/-- *muwaaTin-uuna* declines as in Ryding's table (p. 190). -/
example :
    muwaatinuuna.form .definite = forms "al-muwaaTinuuna" "al-muwaaTiniina" "al-muwaaTiniina" ∧
      muwaatinuuna.form .indefinite = forms "muwaaTinuuna" "muwaaTiniina" "muwaaTiniina" := by
  decide

/-- *SaHraaʾ* declines as in Ryding's table (p. 193). -/
example : sahraa.form .definite = forms "al-SaHraaʾu" "al-SaHraaʾi" "al-SaHraaʾa" ∧
    sahraa.form .indefinite = forms "SaHraaʾu" "SaHraaʾa" "SaHraaʾa" := by
  decide

/-- *muHaam-in* declines as in Ryding's table (p. 198). -/
example : muhaamin.form .definite = forms "al-muHaamii" "al-muHaamii" "al-muHaamiya" ∧
    muhaamin.form .indefinite = forms "muHaamin" "muHaamin" "muHaamiyan" := by
  decide

/-- *mustashfan* declines as in Ryding's table (p. 199). -/
example : mustashfan.form .definite = forms "al-mustashfaa" "al-mustashfaa" "al-mustashfaa" ∧
    mustashfan.form .indefinite = forms "mustashfan" "mustashfan" "mustashfan" := by
  decide

/-- *shakwaa* declines as in Ryding's table (p. 201). -/
example : shakwaa.form .definite = forms "al-shakwaa" "al-shakwaa" "al-shakwaa" ∧
    shakwaa.form .indefinite = forms "shakwaa" "shakwaa" "shakwaa" := by
  decide

/-- Ryding's annexed nouns: *Haqiibat-u* 'bag' of the indefinite *Haqiibat-u yad-in* 'a
handbag', without nunation (p. 160); the duals *waziir-aa* 'two ministers' and the plural
*muharrib-uu* 'smugglers' (p. 211) and *mutaxarrij-ii* 'graduates' (p. 191), without their
*nuun*; and the diptote *ʾafDal-i* 'best' of *min ʾafDal-i l-sanawaat-i* 'among the best years',
with the genitive *-i* (p. 178). -/
example : (⟨"bag", "Haqiibat", .triptote⟩ : Noun).form .construct .nom = "Haqiibatu" ∧
    (⟨"two ministers", "waziir", .dual⟩ : Noun).form .construct .nom = "waziiraa" ∧
    (⟨"smugglers", "muharrib", .soundMasculinePlural⟩ : Noun).form .construct .nom =
      "muharribuu" ∧
    (⟨"graduates", "mutaxarrij", .soundMasculinePlural⟩ : Noun).form .construct .gen =
      "mutaxarrijii" ∧
    (⟨"best", "ʾafDal", .diptote⟩ : Noun).form .construct .gen = "ʾafDali" := by
  decide

/-! ### Syncretism -/

namespace Declension

variable {s : State} {c c' : Case}

/-- The triptote distinguishes the three cases in every state, "each one differentiating a
particular case" (p. 183), and so establishes them for the declensions that merge them. -/
theorem triptote_injective (s : State) : Function.Injective (triptote s) := by
  decide +revert

/-- The dual and the sound plurals have "a specific nominative inflectional marker" and "merge
the genitive and accusative into just one other inflectional marker" (p. 187). -/
theorem twoWay_eq_iff :
    ∀ D ∈ [dual, soundFemininePlural, soundMasculinePlural], ∀ s c c',
      D s c = D s c' ↔ (c = .nom ↔ c' = .nom) := by
  decide

/-- The diptote distinguishes the three cases when definite or annexed and, when indefinite,
merges the genitive and the accusative (p. 192). -/
theorem diptote_eq_iff :
    diptote s c = diptote s c' ↔ c = c' ∨ s = .indefinite ∧ (c = .nom ↔ c' = .nom) := by
  decide +revert

/-- The defective's nominative and genitive "are identical", and its accusative is distinct
(p. 197). -/
theorem defective_eq_iff : defective s c = defective s c' ↔ (c = .acc ↔ c' = .acc) := by
  decide +revert

/-- The indeclinables show "no variation in case" (p. 199), nor do the invariables (p. 200). -/
theorem caseless_eq : ∀ D ∈ [indeclinable, invariable], ∀ s c c', D s c = D s c' := by
  decide

/-! ### The states -/

/-- The triptote and the sound feminine plural mark an indefinite by nunation, a final *-n*
after the ending of the definite (p. 166). -/
theorem nunation : ∀ D ∈ [triptote, soundFemininePlural], ∀ c,
    D .indefinite c = D .definite c ++ "n" := by
  decide

/-- The dual, the sound masculine plural and the invariables "do not take nunation when they are
indefinite" (p. 164), and their indefinite endings are their definite ones: the dual is "not
inflected for definiteness" (p. 188), and the invariables "vary neither in case nor in
definiteness" (p. 200). -/
theorem definite_eq_indefinite :
    ∀ D ∈ [dual, soundMasculinePlural, invariable], D .definite = D .indefinite := by
  decide

/-- An annexed noun has "neither the definite article nor nunation" (p. 211): outside the dual
and the sound masculine plural, its ending is that of the definite. -/
theorem construct_eq_definite :
    ∀ D ∈ [triptote, soundFemininePlural, diptote, defective, indeclinable, invariable],
      D .construct = D .definite := by
  decide

/-- The restriction on nunation applies "also to the final *nuun*s of the dual and the sound
masculine plural. These *nuun*s are deleted on the first term of a construct phrase" (p. 211). -/
theorem nuun_deletion :
    (∀ c, dual .definite c = dual .construct c ++ "ni") ∧
      ∀ c, soundMasculinePlural .definite c = soundMasculinePlural .construct c ++ "na" := by
  decide

end Declension

end Arabic.ModernStandard
