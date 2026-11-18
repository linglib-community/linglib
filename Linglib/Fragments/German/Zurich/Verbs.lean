module

public import Linglib.Syntax.Category.Verb.Defs
public import Linglib.Fragments.German.Zurich.Case
public import Linglib.Syntax.Category.Verb.CaseFrame

/-!
# Zürich German verbs

This file defines the case-governing verbs of Shieber's Swiss German subordinate clauses, whose
informants spoke the Zürich dialect. Each entry is the root `Verb` with its case frame and the
inflected forms the clauses attest: *hälfe* 'help' takes a dative object, and *laa* 'let' and
*aastriiche* 'paint' take an accusative one.

## Implementation notes

An entry records its object's case and no complement frame. Whether the accusative of *laa* is
its own object or the subject of the infinitive it embeds is a question of structure that Shieber
leaves open.

## References

* [shieber-1985]
-/

@[expose] public section

namespace German.Zurich

/-- A Zürich German verb is the root entry with its case frame and its inflected forms. -/
structure Verb extends _root_.Verb, _root_.Verb.CaseFrame Case where
  subject := .nom
  /-- These are the inflected forms recorded besides the citation form. -/
  inflected : List String := []
  deriving BEq

/-- `v.forms` lists the citation form, then the inflected forms. -/
def Verb.forms (v : Verb) : List String := v.form :: v.inflected

namespace Verbs

/-- *hälfe* 'help', finite *hälfed*, takes a dative object. -/
def haelfe : Verb :=
  { morphs := [.root "hälfe"], inflected := ["hälfed"], objects := [.dat] }

/-- *laa* 'let', finite *lönd*, takes an accusative object. -/
def laa : Verb := { morphs := [.root "laa"], inflected := ["lönd"], objects := [.acc] }

/-- *aastriiche* 'paint' takes an accusative object. -/
def aastriiche : Verb := { morphs := [.root "aastriiche"], objects := [.acc] }

/-- `verbs` lists the entries. -/
def verbs : List Verb := [haelfe, laa, aastriiche]

end Verbs

end German.Zurich
