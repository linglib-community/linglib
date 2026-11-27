module

public import Linglib.Syntax.Voice.Basic

/-!
# Russian voice

The postfix *-sja*, *-s'* after a vowel, marks the reflexive voice, *My my-l-i-s'* 'We washed
(ourselves)'. It follows the tense and number suffixes, at the periphery of the verb form.

## Main definitions

* `Russian.reflexive`: the reflexive voice.

## References

* [haspelmath-2023b]
-/

@[expose] public section

namespace Russian

/-- The reflexive *-sja* cumulates the A and the P in one S. -/
def reflexive : Voice := Voice.reflexive.marked [.suff "sja"]

end Russian
