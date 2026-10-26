module

public import Linglib.Fragments.Georgian.Case
public import Mathlib.Order.Setoid.Basic

/-!
# Georgian noun declension

The declension of Georgian nouns, after Hewitt's tables of one noun for each class of stem. A
consonant stem, as *k'ac-i* 'man', takes seven distinct endings, and every modern plural takes the
same endings after the plural suffix *-eb-*. Many consonant stems lose a vowel by syncope in the
genitive, the instrumental and the adverbial singular and in the modern plural, as *gutan-i*
'plough', genitive *gutn-is(a)*. Most common nouns in *-a* and *-e*, as *zġva* 'sea'
and *t'q'e* 'wood', lose their vowel before the genitive and the instrumental endings, and keep
the seven cases apart too. The stems that keep their vowel, those in *-o*, *-u* and *-i*, the
proper names in *-a* and *-e* and a few common nouns such as *mela* 'fox', have *-s(a)* in the
genitive as in the dative, and the proper names and the *i*-stems have the nominative as
vocative. The old plural, still found in titles and set expressions, as *sabč'o-ta k'avšir-i*
'the Soviet Union', has *-n-i* and *-n-o* in the nominative and the vocative and one portmanteau
ending *-t(a)* in the other cases.

## Main statements

* `consonant_injective`, `plural_injective`: a consonant stem without syncope and every modern
  plural keep the seven cases apart (Hewitt pp. 33–34).
* `singular_gen_eq_dat`, `singular_voc_eq_nom`: the stems that keep their vowel have the dative as
  genitive, and the proper names and the *i*-stems the nominative as vocative (pp. 38–41).
* `ker_singular_le_ker_sota`: no singular is more syncretic than a proper name's, so the only
  syncretisms of the singular are genitive with dative and vocative with nominative.
* `oldPlural_eq_oldPlural_iff`: the old plural has one form for the five oblique cases (p. 33).

## Implementation notes

The forms are Hewitt's, in his transliteration and with his two forms of a vocative, and the
long form of an ending is in parentheses: *-s(a)* is *-s*, or *-sa* before a monosyllable such as
*da* 'and'. The old plural does not syncopate, so it takes the full stem. Its instrumental and
adverbial, which Hewitt gives in parentheses as rarely attested, if at all, are included.

## References

* [hewitt-1995]
-/

@[expose] public section

namespace Georgian.Declension

/-- The case endings of a consonant stem. -/
def ending : Case → String
  | .nom => "-i"
  | .voc => "-o"
  | .dat => "-s(a)"
  | .erg => "-ma"
  | .gen => "-is(a)"
  | .inst => "-it(a)"
  | .adv => "-ad(a)"

/-- The declension of a consonant stem, its endings after the stem, or after the stem reduced by
syncope in the genitive, the instrumental and the adverbial. -/
def consonant (stem : String) (reduced : String := stem) : Case → String
  | .gen => reduced ++ ending .gen
  | .inst => reduced ++ ending .inst
  | .adv => reduced ++ ending .adv
  | c => stem ++ ending c

/-- The modern plural, which declines the stem with the plural suffix *-eb-* as a consonant
stem. -/
def plural (stem : String) : Case → String := consonant (stem ++ "-eb")

/-- The old plural, with *-n-i* and *-n-o* in the nominative and the vocative and the portmanteau
*-t(a)* in the other cases. -/
def oldPlural (stem : String) : Case → String
  | .nom => stem ++ "-n-i"
  | .voc => stem ++ "-n-o"
  | _ => stem ++ "-t(a)"

/-- A noun by the forms of Hewitt's table: the singular, and for a common noun the modern and the
old plural. -/
structure Noun where
  /-- The singular. -/
  singular : Case → String
  /-- The modern plural. -/
  plural : Option (Case → String) := none
  /-- The old plural. -/
  oldPlural : Option (Case → String) := none

/-- *k'ac-i* 'man', a consonant stem. -/
def kaci : Noun where
  singular := consonant "k'ac"
  plural := some (plural "k'ac")
  oldPlural := some (oldPlural "k'ac")

/-- *gutan-i* 'plough', a consonant stem with syncope. -/
def gutani : Noun where
  singular := consonant "gutan" "gutn"
  plural := some (plural "gutn")
  oldPlural := some (oldPlural "gutan")

/-- *c'el-i* 'year', a consonant stem with syncope. -/
def celi : Noun where
  singular := consonant "c'el" "c'l"
  plural := some (plural "c'l")
  oldPlural := some (oldPlural "c'el")

/-- *mac'on-i* 'yoghurt', a consonant stem whose *-o-* reduces to *-v-*. -/
def maconi : Noun where
  singular := consonant "mac'on" "mac'vn"
  plural := some (plural "mac'vn")
  oldPlural := some (oldPlural "mac'on")

/-- *godor-i* 'basket', a consonant stem whose *-o-* is lost. -/
def godori : Noun where
  singular := consonant "godor" "godr"
  plural := some (plural "godr")
  oldPlural := some (oldPlural "godor")

/-- *zġva* 'sea', an *a*-stem, which loses its vowel in the genitive, the instrumental and the
adverbial singular and in the modern plural. -/
def zgva : Noun where
  singular
    | .nom => "zġva" | .voc => "zġva-o, zġva-v" | .dat => "zġva-s(a)" | .erg => "zġva-m(a)"
    | .gen => "zġv-is(a)" | .inst => "zġv-it(a)" | .adv => "zġv-ad(a)"
  plural := some (plural "zġv")
  oldPlural := some (oldPlural "zġva")

/-- *šota*, a proper name in *-a*. -/
def sota : Noun where
  singular
    | .nom | .voc => "šota" | .dat | .gen => "šota-s(a)" | .erg => "šota-m(a)"
    | .inst => "šota-ti" | .adv => "šota-d(a)"

/-- *t'q'e* 'wood, forest', an *e*-stem, which loses its vowel in the genitive and the
instrumental singular. -/
def tqe : Noun where
  singular
    | .nom => "t'q'e" | .voc => "t'q'e-o/t'q'e-v" | .dat => "t'q'e-s(a)" | .erg => "t'q'e-m(a)"
    | .gen => "t'q'-is(a)" | .inst => "t'q'-it(a)" | .adv => "t'q'e-d(a)"
  plural := some (plural "t'q'e")
  oldPlural := some (oldPlural "t'q'e")

/-- *elene* 'Helen', a proper name in *-e*. -/
def elene : Noun where
  singular
    | .nom | .voc => "elene" | .dat | .gen => "elene-s(a)" | .erg => "elene-m(a)"
    | .inst => "elene-ti" | .adv => "elene-d(a)"

/-- *uro* 'hammer', an *o*-stem. -/
def uro : Noun where
  singular
    | .nom => "uro" | .voc => "uro(-v)" | .dat | .gen => "uro-s(a)" | .erg => "uro-m(a)"
    | .inst => "uro-ti" | .adv => "uro-d(a)"
  plural := some (plural "uro")
  oldPlural := some (oldPlural "uro")

/-- *juju* 'breast', a *u*-stem. -/
def juju : Noun where
  singular
    | .nom => "juju" | .voc => "juju-v" | .dat | .gen => "juju-s(a)" | .erg => "juju-m(a)"
    | .inst => "juju-ti" | .adv => "juju-d(a)"
  plural := some (plural "juju")
  oldPlural := some (oldPlural "juju")

/-- *t'aksi* 'taxi', an *i*-stem. -/
def taksi : Noun where
  singular
    | .nom | .voc => "t'aksi" | .dat | .gen => "t'aksi-s(a)" | .erg => "t'aksi-m(a)"
    | .inst => "t'aksi-t(a)" | .adv => "t'aksi-d(a)"
  plural := some (plural "t'aksi")

/-- *giorgi* 'George', a proper name in *-i*. -/
def giorgi : Noun where
  singular
    | .nom | .voc => "giorgi" | .dat | .gen => "giorgi-s(a)" | .erg => "giorgi-m(a)"
    | .inst => "giorgi-t(a)" | .adv => "giorgi-d(a)"

/-- The nouns of Hewitt's tables. -/
def nouns : List Noun :=
  [kaci, gutani, celi, maconi, godori, zgva, sota, tqe, elene, uro, juju, taksi, giorgi]

/-! ### The cases the paradigms distinguish -/

theorem ending_injective : Function.Injective ending := by
  decide

/-- A consonant stem keeps the seven cases apart. -/
theorem consonant_injective (stem : String) : Function.Injective (consonant stem) := by
  have h c : consonant stem stem c = stem ++ ending c := by cases c <;> rfl
  exact fun c d hcd ↦ ending_injective ((String.append_right_inj stem).1 (by rwa [h, h] at hcd))

/-- Every modern plural keeps the seven cases apart. -/
theorem plural_injective (stem : String) : Function.Injective (plural stem) :=
  consonant_injective _

theorem singular_injective :
    ∀ n ∈ [kaci, gutani, celi, maconi, godori, zgva, tqe], Function.Injective n.singular := by
  decide

/-- The genitive singular is the dative in the stems that keep their vowel. -/
theorem singular_gen_eq_dat :
    ∀ n ∈ [sota, elene, uro, juju, taksi, giorgi], n.singular .gen = n.singular .dat := by
  decide

theorem singular_voc_eq_nom :
    ∀ n ∈ [sota, elene, taksi, giorgi], n.singular .voc = n.singular .nom := by
  decide

/-- No singular is more syncretic than a proper name's: the only syncretisms of the singular are
the genitive with the dative and the vocative with the nominative. -/
theorem ker_singular_le_ker_sota :
    ∀ n ∈ nouns, Setoid.ker n.singular ≤ Setoid.ker sota.singular := by
  simp only [Setoid.le_def, Setoid.ker_def]
  decide

/-- The old plural has one form for the five oblique cases, and distinct forms for the
nominative and the vocative. -/
theorem oldPlural_eq_oldPlural_iff {stem : String} {c d : Case} :
    oldPlural stem c = oldPlural stem d ↔
      c = d ∨ c ∉ ({.nom, .voc} : Finset Case) ∧ d ∉ ({.nom, .voc} : Finset Case) := by
  cases c <;> cases d <;> simp [oldPlural]

end Georgian.Declension
