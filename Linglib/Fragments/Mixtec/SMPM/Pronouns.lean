module

public import Linglib.Syntax.Gender.Basic
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# San Martín Peras Mixtec pronouns

San Martín Peras Mixtec (Mixtecan, Oto-Manguean; ISO 639-3 `jmx`) has a clitic and a non-clitic
series of personal pronouns, neither inflected for case. The local persons distinguish singular
and plural, and inclusive and exclusive in the first person plural; every local cell except the
inclusive has a form in both series. The nonlocal persons have clitics only, one for each of six
genders: neutral, feminine, masculine, liquid, wooden and animal. Only the neutral and the
feminine have separate plural clitics, so *=rà* means 'he' or 'they (all male)'. A clitic cannot
be coordinated, stand alone or bear focus. Where the non-clitic series has no form, a clitic is
strengthened by a demonstrative, as in *yé yo'o* 'we (incl.) here', or by the definite article
*mí*, which with a clitic also forms the reflexive, as in *mí =rà* 'himself'.

## Implementation notes

The genders are the carrier `Gender.Value`, visible only on the nonlocal clitics.
`Gender.Value.toLabel` gives the comparative label of the feminine and the masculine; the other
four genders have none. A clitic with no plural counterpart has `number := some .general`, so it
realizes both the singular and the plural third person. The strengthened forms are phrases and
are not entries; neither is the prevocalic allomorph *=(y)à* of the neutral clitic.

## References

* [ostrove-2026]
* [cardinaletti-starke-1999]
* [corbett-1991]
-/

@[expose] public section

namespace Mixtec.SMPM

/-! ### Gender -/

/-- The six genders of the nonlocal pronouns. -/
inductive Gender.Value where
  | neutral
  | feminine
  | masculine
  | liquid
  | wooden
  | animal
  deriving DecidableEq, Repr, Fintype

namespace Gender

/-- The clitic of each gender, singular where the gender has a plural clitic ((5)). -/
def Value.clitic : Value → String
  | .neutral => "=ñà"
  | .feminine => "=ñá"
  | .masculine => "=rà"
  | .liquid => "=rá"
  | .wooden => "=tún"
  | .animal => "=rí"

/-- The plural clitic of the neutral and the feminine, the only genders that distinguish
number ((5)). -/
def Value.pluralClitic : Value → Option String
  | .neutral => some "=nà"
  | .feminine => some "=ná"
  | _ => none

/-- The comparative label of a gender, which only the feminine and the masculine have. -/
def Value.toLabel : Value → Option Gender.Label
  | .feminine => some .feminine
  | .masculine => some .masculine
  | _ => none

theorem clitic_injective : Function.Injective Value.clitic := by decide

end Gender

/-! ### Clitics -/

/-- *=ì* is the first person singular clitic ((4), (61)). -/
def cl1sg : PersonalPronoun :=
  { form := "=ì", person := some .first, number := some .singular, strength := some .clitic }

/-- *=(y)é* is the first person plural inclusive clitic ((4), (61)). -/
def cl1plIncl : PersonalPronoun :=
  { form := "=(y)é", person := some .firstInclusive, number := some .plural,
    strength := some .clitic }

/-- *=ndú* is the first person plural exclusive clitic ((4), (61)). -/
def cl1plExcl : PersonalPronoun :=
  { form := "=ndú", person := some .firstExclusive, number := some .plural,
    strength := some .clitic }

/-- *=ú* is the second person singular clitic ((4), (61)). -/
def cl2sg : PersonalPronoun :=
  { form := "=ú", person := some .second, number := some .singular, strength := some .clitic }

/-- *=ndó* is the second person plural clitic ((4), (61)). -/
def cl2pl : PersonalPronoun :=
  { form := "=ndó", person := some .second, number := some .plural, strength := some .clitic }

/-- The nonlocal clitic of a gender is singular where the gender has a plural clitic, and
number-neutral otherwise ((5)). -/
def cl3 (g : Gender.Value) : PersonalPronoun :=
  { form := g.clitic, person := some .third,
    number := some (if g.pluralClitic.isSome then .singular else .general),
    gender := g.toLabel, strength := some .clitic }

/-- The nonlocal plural clitic of a gender, where it has one ((5)). -/
def cl3pl (g : Gender.Value) : Option PersonalPronoun :=
  g.pluralClitic.map fun f ↦
    { form := f, person := some .third, number := some .plural, gender := g.toLabel,
      strength := some .clitic }

/-- The clitic series. -/
def clitics : Finset PersonalPronoun :=
  {cl1sg, cl1plIncl, cl1plExcl, cl2sg, cl2pl} ∪
    Finset.univ.biUnion fun g ↦ insert (cl3 g) (cl3pl g).toFinset

/-! ### Non-clitics -/

/-- *yù'u* is the first person singular non-clitic ((4), (62)). -/
def str1sg : PersonalPronoun :=
  { form := "yù'u", person := some .first, number := some .singular, strength := some .strong }

/-- *ndú'ú* is the first person plural exclusive non-clitic ((4), (62)). -/
def str1plExcl : PersonalPronoun :=
  { form := "ndú'ú", person := some .firstExclusive, number := some .plural,
    strength := some .strong }

/-- *yô'o* is the second person singular non-clitic ((4), (62)). -/
def str2sg : PersonalPronoun :=
  { form := "yô'o", person := some .second, number := some .singular, strength := some .strong }

/-- *ndó'ó* is the second person plural non-clitic ((4), (62)). -/
def str2pl : PersonalPronoun :=
  { form := "ndó'ó", person := some .second, number := some .plural, strength := some .strong }

/-- The non-clitic series, which bears focus where a clitic cannot ((65), (66)). -/
def nonclitics : Finset PersonalPronoun := {str1sg, str1plExcl, str2sg, str2pl}

/-! ### The paradigm -/

/-- The personal pronouns. -/
def pronouns : Finset PersonalPronoun := clitics ∪ nonclitics

/-- The forms of each referential category. -/
def paradigm : Person.Category → Finset String := PersonalPronoun.paradigm pronouns

/-- The non-clitic series covers every category the clitics do except the inclusive and the
nonlocal persons ((62)). -/
theorem nonclitic_categories :
    nonclitics.biUnion (·.referential) =
      clitics.biUnion (·.referential) \ {.speakerAddresseeOthers, .other, .others} := by
  decide

theorem clitic_mem_paradigm_others_iff (g : Gender.Value) :
    g.clitic ∈ paradigm .others ↔ g.pluralClitic = none := by
  revert g; decide

/-- The reflexive of a clitic is the clitic after the definite article *mí*, as in *mí =rà*
'himself' ((71)). A possessor may take one without needing it: *mí =rí* 'its own' ((74)). -/
def reflexive (p : PersonalPronoun) : ReflexivePronoun :=
  { toPronoun := { p.toPronoun with form := "mí " ++ p.form, strength := none } }

end Mixtec.SMPM
