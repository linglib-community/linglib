module

public import Linglib.Fragments.Georgian.Case

/-!
# Georgian noun declension

The declension of Georgian nouns, after Hewitt's tables of one noun for each class of stem. A
consonant stem, as *k'ac-i* 'man', takes seven distinct endings, and every modern plural takes the
same endings after the plural suffix *-eb-*. Most common nouns in *-a* and *-e*, as *zġva* 'sea'
and *t'q'e* 'wood', lose their vowel before the genitive and the instrumental endings, and keep
the seven cases apart too. The stems that keep their vowel, those in *-o*, *-u* and *-i*, the
proper names in *-a* and *-e* and a few common nouns such as *mela* 'fox', have *-s(a)* in the
genitive as in the dative, and the proper names and the *i*-stems have the nominative as
vocative. The old plural, still found in titles and set expressions, as *sabč'o-ta k'avšir-i*
'the Soviet Union', has *-n-i* and *-n-o* in the nominative and the vocative and one portmanteau
ending *-t(a)* in the other cases.

## Main statements

* `consonant_injective`, `plural_injective`: a consonant stem and every modern plural keep the
  seven cases apart (Hewitt pp. 33–34).
* `singular_gen_eq_dat`, `singular_voc_eq_nom`: the stems that keep their vowel have the dative as
  genitive, and the proper names and the *i*-stems the nominative as vocative (pp. 38–41).
* `injOn_singular`: the singulars keep apart every two cases other than the genitive and the
  vocative.
* `oldPlural_eq_oldPlural_iff`: the old plural has one form for the five oblique cases (p. 33).

## Implementation notes

The forms are Hewitt's, in his transliteration and with his two forms of a vocative, and the
long form of an ending is in parentheses: *-s(a)* is *-s*, or *-sa* before a monosyllable such as
*da* 'and'. The consonant stems whose vowel syncopates, as *gutan-i* 'plough', genitive
*gutn-is(a)*, are left out. The old plural instrumental and adverbial, which Hewitt gives in
parentheses as rarely attested, if at all, are included.

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

/-- The declension of a consonant stem, its endings after the stem. -/
def consonant (stem : String) (c : Case) : String := stem ++ ending c

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
def nouns : List Noun := [kaci, zgva, sota, tqe, elene, uro, juju, taksi, giorgi]

/-! ### The cases the paradigms distinguish -/

theorem ending_injective : Function.Injective ending := by
  decide

/-- A consonant stem keeps the seven cases apart. -/
theorem consonant_injective (stem : String) : Function.Injective (consonant stem) :=
  fun _ _ h ↦ ending_injective ((String.append_right_inj stem).1 h)

/-- Every modern plural keeps the seven cases apart. -/
theorem plural_injective (stem : String) : Function.Injective (plural stem) :=
  consonant_injective _

theorem singular_injective : ∀ n ∈ [kaci, zgva, tqe], Function.Injective n.singular := by
  decide

/-- The genitive singular is the dative in the stems that keep their vowel. -/
theorem singular_gen_eq_dat :
    ∀ n ∈ [sota, elene, uro, juju, taksi, giorgi], n.singular .gen = n.singular .dat := by
  decide

theorem singular_voc_eq_nom :
    ∀ n ∈ [sota, elene, taksi, giorgi], n.singular .voc = n.singular .nom := by
  decide

/-- The singulars keep apart every two cases other than the genitive and the vocative. -/
theorem injOn_singular : ∀ n ∈ nouns, Set.InjOn n.singular {.gen, .voc}ᶜ := by
  have h : ∀ n ∈ nouns, ∀ c ∉ ({.gen, .voc} : Finset Case), ∀ d ∉ ({.gen, .voc} : Finset Case),
      n.singular c = n.singular d → c = d := by
    decide
  exact fun n hn c hc d hd ↦ h n hn c (by simpa using hc) d (by simpa using hd)

/-- The old plural has one form for the five oblique cases, and distinct forms for the
nominative and the vocative. -/
theorem oldPlural_eq_oldPlural_iff {stem : String} {c d : Case} :
    oldPlural stem c = oldPlural stem d ↔
      c = d ∨ c ∉ ({.nom, .voc} : Finset Case) ∧ d ∉ ({.nom, .voc} : Finset Case) := by
  cases c <;> cases d <;> simp [oldPlural]

end Georgian.Declension
