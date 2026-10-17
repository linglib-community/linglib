module

public import Linglib.Semantics.Presupposition.Trigger

/-!
# Cantonese *again*-elements

The Cantonese iterative presupposition triggers, following Matthews and Yip, are the preverbal
adverbs *jau* 又 and *zoi* 再, the counterparts of Mandarin *you* and *zai*
(`Fragments/Mandarin/Adverbs.lean`), the postverbal suffix *-faan* 返 'again, back', and the
postverbal repetitive *-gwo* 過 'again, anew', homophonous with the experiential aspect suffix of
`Fragments/Cantonese/Aspect.lean`. Their
association with the outer and inner aspect projections and their scope behaviour are the
analysis of Liu and Yip and live in `Studies/LiuYip2026.lean`.

## References

* [matthews-yip-1994]
* [liu-yip-2026]
* [lee-yip-to-appear]
-/

@[expose] public section

namespace Cantonese.Particles

open Presupposition

/-- The preverbal *jau6* 又 'again'. -/
def jau : TriggerItem := { form := "jau6", script := "又", triggerClass := .iterative }

/-- The preverbal *zoi3* 再 'again'. -/
def zoi : TriggerItem := { form := "zoi3", script := "再", triggerClass := .iterative }

/-- The postverbal *-faan1* 返 'again, back'. -/
def faan : TriggerItem := { form := "faan1", script := "返", triggerClass := .iterative }

/-- The postverbal repetitive *-gwo3* 過 'again, anew', redoing an event to set its outcome
right. -/
def gwo : TriggerItem := { form := "gwo3", script := "過", triggerClass := .iterative }

/-- The *again*-elements. -/
def all : List TriggerItem := [jau, zoi, faan, gwo]

end Cantonese.Particles
