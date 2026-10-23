module

public import Linglib.Syntax.Case.Basic

/-!
# Georgian case

Georgian has seven cases, the nominative, vocative, dative, ergative, genitive, instrumental and
adverbial, in essentially one declension for all nouns ([hewitt-1995] §3.1, p. 33). The modern
plural adds the same endings to the plural suffix *-eb-*. The older plural, still found in
archaising styles, has its own nominative and vocative and one portmanteau for the other cases,
rare if attested at all in the instrumental and the adverbial (pp. 33–34).

## Main definitions

* `Georgian.Case`, `Georgian.Case.label`: the seven cases, and the comparative value each is named
  for.
* `Georgian.kaci`: the declension of *k'ac-i* 'man', singular, plural and older plural (p. 34).

## Main results

* `Georgian.singular_kaci_injective`, `Georgian.plural_kaci_injective`: the modern declension
  keeps the seven cases apart in both numbers.
* `Georgian.oldPlural_kaci_oblique`: the older plural has one form for the dative, ergative and
  genitive.

## Implementation notes

The forms are Hewitt's, with the long variants of the four endings that have them in
parentheses. The older plural of the instrumental and the adverbial, which Hewitt gives in
parentheses as rarely attested, is left out.

## References

* [hewitt-1995]
-/

@[expose] public section

namespace Georgian

/-- The seven cases, in Hewitt's order. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The vocative. -/
  | voc
  /-- The dative. -/
  | dat
  /-- The ergative. -/
  | erg
  /-- The genitive. -/
  | gen
  /-- The instrumental. -/
  | inst
  /-- The adverbial, as in *briq'v-ada* 'as an idiot' (p. 34). -/
  | adv
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for, the essive for the adverbial. -/
def label : Case → _root_.Case
  | nom => .nom
  | voc => .voc
  | dat => .dat
  | erg => .erg
  | gen => .gen
  | inst => .inst
  | adv => .ess

/-- `forms nom voc dat erg gen inst adv` assigns each case its form. -/
def forms {α : Type*} (nom voc dat erg gen inst adv : α) : Case → α
  | .nom => nom
  | .voc => voc
  | .dat => dat
  | .erg => erg
  | .gen => gen
  | .inst => inst
  | .adv => adv

end Case

/-- The singular of *k'ac-i* 'man'. -/
def kaci.singular : Case → String :=
  Case.forms "k'ac-i" "k'ac-o" "k'ac-s(a)" "k'ac-ma" "k'ac-is(a)" "k'ac-it(a)" "k'ac-ad(a)"

/-- The plural of *k'ac-i* 'man'. -/
def kaci.plural : Case → String :=
  Case.forms "k'ac-eb-i" "k'ac-eb-o" "k'ac-eb-s(a)" "k'ac-eb-ma" "k'ac-eb-is(a)" "k'ac-eb-it(a)"
    "k'ac-eb-ad(a)"

/-- The older plural of *k'ac-i* 'man', where it is attested. -/
def kaci.oldPlural : Case → Option String :=
  Case.forms (some "k'ac-n-i") (some "k'ac-n-o") (some "k'ac-t(a)") (some "k'ac-t(a)")
    (some "k'ac-t(a)") none none

/-- The modern singular keeps the seven cases apart. -/
theorem singular_kaci_injective : Function.Injective kaci.singular := by
  decide

/-- The modern plural keeps the seven cases apart. -/
theorem plural_kaci_injective : Function.Injective kaci.plural := by
  decide

/-- The older plural has one form for the dative, ergative and genitive. -/
theorem oldPlural_kaci_oblique :
    kaci.oldPlural .dat = kaci.oldPlural .erg ∧ kaci.oldPlural .erg = kaci.oldPlural .gen := by
  decide

end Georgian
