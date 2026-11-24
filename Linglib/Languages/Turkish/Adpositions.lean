module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# Turkish postpositions

The postpositions of Turkish as `Adposition` entries: so far the comitative-instrumental *-(y)lA*,
rarely the separate form *ile*, which forms postpositional phrases and is also the noun phrase
conjunction 'and', `Turkish.Coordination.ile` ([goksel-kerslake-2005], §8.1.4, §17.2.1).

## Main definitions

* `Turkish.Adpositions.ile`: the comitative-instrumental postposition.

## Implementation notes

* The entry records *-(y)lA* as an enclitic. Göksel and Kerslake call it the suffixal counterpart
  of the clitic *ile*, but unlike the case suffixes it is unstressable (§8.1.4), and
  [kornfilt-1997] describes it as cliticizing (§1.3.1.4). The separate form *ile* is not recorded.

## References

* [goksel-kerslake-2005]
* [kornfilt-1997]
-/

@[expose] public section

namespace Turkish.Adpositions

/-- *-(y)lA* 'with', in the company of someone or by means of something. -/
def ile : Adposition :=
  { morphs := [.encl "(y)lA"], linearization := {.post}, functions := {.comitative, .instrumental},
    complements := {some .np} }

end Turkish.Adpositions
