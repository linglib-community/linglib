module

public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic

/-!
# The English *to*-infinitive

The frame of a *to*-infinitive, the complement of verbs such as *try* and *believe* and of
adjectives such as *able*. An English infinitive has a subject of its own only when *for*
introduces it, so the subject of a bare *to*-infinitive is unpronounced.

## References

* [huddleston-pullum-2002]
-/

@[expose] public section

namespace English.Verbs

/-- The English *to*-infinitive. Its subject is unpronounced, since an infinitive has a subject
of its own only when *for* introduces one ([huddleston-pullum-2002] p. 1178). -/
def toInfinitive : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .infinitive) (subject := some .null)]⟩

end English.Verbs
