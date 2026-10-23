module

public import Linglib.Syntax.Minimalist.Ellipsis
public import Linglib.Data.Examples.Funakoshi2016

/-!
# Funakoshi (2016): Verb-Stranding Verb Phrase Ellipsis in Japanese

This file formalizes [funakoshi-2016]'s argument that Japanese has verb-stranding verb phrase
ellipsis. Adjuncts in Japanese were held never to be null; the paper shows that a manner,
instrumental or temporal adjunct is understood as null when the clause-mate object is null too or
the clause is intransitive, and never when an object stays overt, unless that object is
contrastively focused (its generalizations (12) and (59)). *Pro* and argument ellipsis reach
arguments only, so a null adjunct needs ellipsis of the verb phrase with the verb raised out of
it: [E] on Voice in the clausal spine of `Minimalist.Ellipsis` ([merchant-2001]), the verb
stranded above it. Everything in the site goes, so the object goes with the adjunct or escapes by
scrambling, and an object scrambled out of the site is a pseudogapping remnant, which must be
contrastively focused. Reason adverbial clauses scope above negation and so sit above the site;
they cannot be null even beside a null object. `NullAdjunct` states the derivation of the reading
and `nullAdjunct_iff` reads the generalizations off the spine: the adjunct attaches inside the
verb phrase and the object is not an unfocused overt remnant. The rival that keeps argument
ellipsis as the only strategy, the oblique movement of the adjunct onto a null argument,
undergenerates in intransitive clauses and overgenerates with null subjects and with reason
clauses (`rows_not_oblique`), and argument ellipsis alone derives no null adjunct at all. The
rows are the paper's ellipsis clauses under the null adjunct reading (`rows_predicted`).

## Implementation notes

* The paper's (40), where *okurete* 'late' resists the null reading in an intransitive clause,
  is left out: the paper attributes it to the adverb's degradation under negation in non-elliptical
  sentences as well.
* An overt object is recorded as contrastively focused or not; givenness is not recorded, so the
  functional account of §2.1, which the paper refutes with the new objects of (26) and (27), stays
  in the prose.
* The examples are `Data.Examples.Funakoshi2016`.

## References

* [funakoshi-2016]
* [merchant-2001]
-/

@[expose] public section

namespace Funakoshi2016

open Minimalist

/-- Where the adjunct attaches: inside the verb phrase, as manner, instrumental and temporal
adjuncts do, or above negation, as reason adverbial clauses do. -/
inductive Attachment
  | vp
  | reason
  deriving DecidableEq, Fintype, Repr

/-- The site of the adjunct, adjoined to VP, or to TP above the negation a reason clause
outscopes. -/
def Attachment.site : Attachment → ClauseSpine.Site
  | .vp => .adjunct .V
  | .reason => .adjunct .T

/-- The clause-mate object of the ellipsis clause: absent in an intransitive clause, null, overt
without contrastive focus, or overt and contrastively focused. -/
inductive ObjectStatus
  | absent
  | null
  | overt
  | focused
  deriving DecidableEq, Fintype, Repr

/-- An ellipsis clause under the null adjunct reading. -/
structure Config where
  adjunct : Attachment
  object : ObjectStatus
  subjectNull : Bool
  deriving DecidableEq, Repr

/-- The null adjunct reading by verb-stranding ellipsis, [E] on Voice deleting the verb phrase
with its adjuncts while the verb, raised to tense, is stranded: the adjunct sits in the site, and
the object, if any, is elided with it or extracted as a contrastively focused remnant. -/
def NullAdjunct (c : Config) : Prop :=
  Ellipsis.vpEllipsis.Deletes c.adjunct.site ∧ c.object ≠ .overt

instance : DecidablePred NullAdjunct := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- An adjunct is null iff it is inside the verb phrase and the object is not overt ((12), (59),
§2.2). -/
theorem nullAdjunct_iff (c : Config) : NullAdjunct c ↔ c.adjunct = .vp ∧ c.object ≠ .overt := by
  obtain ⟨a, o, s⟩ := c
  cases a <;> cases o <;> cases s <;> decide

/-- Takahashi's oblique movement: the adjunct adjoins to a null argument, and argument ellipsis
takes both. -/
def ObliqueMovement (c : Config) : Prop := c.object = .null ∨ c.subjectNull = true

instance : DecidablePred ObliqueMovement := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-! ### The paper's ellipsis clauses -/

/-- An ellipsis clause of the paper and whether its null adjunct reading is available. -/
structure Row where
  config : Config
  available : Bool
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let a ← ex.parse? "adjunct" [("vp", Attachment.vp), ("reason", .reason)]
  let o ← ex.parse? "object"
    [("absent", ObjectStatus.absent), ("null", .null), ("overt", .overt), ("focused", .focused)]
  let s ← ex.parse? "subjectNull" [("yes", true), ("no", false)]
  let v ← ex.parse? "available" [("yes", true), ("no", false)]
  pure ⟨⟨a, o, s⟩, v⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_predicted : ∀ r ∈ rows, (r.available = true ↔ NullAdjunct r.config) := by decide

theorem rows_exists_available : ∃ r ∈ rows, r.available = true := by decide

/-- Oblique movement undergenerates the intransitive (39) and overgenerates the null-subject
clauses (43) and (44) and the reason clause (32). -/
theorem rows_not_oblique : ¬ ∀ r ∈ rows, (r.available = true ↔ ObliqueMovement r.config) := by
  decide

end Funakoshi2016
