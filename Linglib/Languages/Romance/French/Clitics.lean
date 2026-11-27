module

public import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# French clitics

The reflexive clitic *se* stands in the object slot before the verb, *Il se voyait* 'He saw
himself' beside *Il la voyait* 'He saw her', and occurs only in the third person; the first and
second persons use the ordinary object clitics coreferentially, *je me vois*. Haspelmath counts
it among the reflexive argument indexes, while Reinhart and Siloni treat it as a voice marker.

## Main definitions

* `French.Clitics.se`: the third-person reflexive clitic.

## References

* [haspelmath-2023b]
-/

@[expose] public section

namespace French.Clitics

/-- *se*, third person reflexive, number-neutral. -/
def se : ReflexivePronoun :=
  { form := "se", person := some .third, number := some .general, strength := some .clitic }

end French.Clitics
