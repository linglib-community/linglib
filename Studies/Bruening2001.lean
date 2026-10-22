module

public import Linglib.Syntax.Minimalist.Agree.Basic

/-!
# Bruening 2001: QR obeys Superiority

[bruening-2001] accounts for frozen scope: *I gave a child each doll* has only the surface reading
while its dative counterpart *I gave a doll to each child* is ambiguous, and the freezing is not an
inability to move, since it holds between two objects but not between an object and the subject,
and it disappears under passivization. Quantifiers raise by attraction to a head bearing a
P-feature; by Shortest ([richards-1997]) the attractor takes the structurally highest candidate
first, and later movements tuck in beneath, so the attraction order, and with it the scope order,
is the base order.

The contrast then follows from structure alone. In the double object construction the first object
asymmetrically c-commands the second ([barss-lasnik-1986], [larson-1988], [pylkkanen-2008]), so
only the goal can be attracted first and scope is frozen; in the locative the direct object and the
PP are co-arguments that c-command each other, so either may go first and scope is free. The
subject sits in the attracting head's specifier, outside its domain, which is why the second object
can still scope over it and why a passivized double object construction is ambiguous again.

## References

* [bruening-2001]
* [richards-1997]
* [barss-lasnik-1986]
* [larson-1988]
* [pylkkanen-2008]
-/

@[expose] public section

namespace Bruening2001

open Minimalist Minimalist.SyntacticObject

/-! ### Attraction under Shortest -/

/-- The quantifiers among `qs` that the P-feature head `h` of `t` may attract first. Shortest
licenses attracting a quantifier first only when no other candidate asymmetrically c-commands it,
since such a candidate would form a smaller well-formed pair with the attractor, so these are the
candidates the head's probe finds among the positions it c-commands. -/
def firsts (t : LinearizedSyntacticObject) (h : SyntacticObject) (qs : List SyntacticObject) :
    Finset SyntacticObject :=
  t.goals (.relativized fun q ↦ decide (t.termAt q ∈ qs)) h

/-- Since later movements tuck in beneath earlier ones, the quantifier attracted first takes widest
scope, so scope is ambiguous exactly when two candidates may be attracted first. -/
def Ambiguous (t : LinearizedSyntacticObject) (h : SyntacticObject) (qs : List SyntacticObject) :
    Prop :=
  1 < (firsts t h qs).card

instance (t : LinearizedSyntacticObject) (h : SyntacticObject) (qs : List SyntacticObject) :
    Decidable (Ambiguous t h qs) :=
  inferInstanceAs (Decidable (1 < _))

/-! ### The double object construction -/

/-- The light verb bearing the P-feature that attracts quantifiers ([kratzer-1996]'s Voice). -/
def v : LinearizedSyntacticObject := .leaf ⟨.of .Voice [.V] "v[P]", 400⟩
/-- The applicative head introducing the first object ([pylkkanen-2008]). -/
def appl : LinearizedSyntacticObject := .leaf ⟨.of .Appl [.D] "Appl", 402⟩
def gave : LinearizedSyntacticObject := .leaf ⟨.of .V [.Appl] "gave", 404⟩
def ozzy : LinearizedSyntacticObject := .leaf ⟨.of .D [] "Ozzy", 406⟩
/-- The first object, the goal. -/
def aGirl : LinearizedSyntacticObject := .leaf ⟨.of .D [] "a girl", 407⟩
/-- The second object, the theme. -/
def everyTelescope : LinearizedSyntacticObject := .leaf ⟨.of .D [] "every telescope", 408⟩
/-- The preposition of the locative variant. -/
def toP : LinearizedSyntacticObject := .leaf ⟨.of .P [.D] "to", 409⟩

/-- `{Ozzy, {v, {gave, {a girl, {Appl, every telescope}}}}}`. The first object is the argument of
the applicative head, merged above the projection containing the second, so it asymmetrically
c-commands it. -/
def doc : LinearizedSyntacticObject := {ozzy, {v, {gave, {aGirl, {appl, everyTelescope}}}}}

/-- The quantifiers competing for attraction in the double object construction. -/
def docQuantifiers : List SyntacticObject := [aGirl, everyTelescope]

-- The first object asymmetrically c-commands the second ([barss-lasnik-1986]).
example : AsymmCCommands doc aGirl everyTelescope := by decide

/-- Only the first object may be attracted first, since it asymmetrically c-commands the second,
so the derivation fixes the base order and the second object cannot come to scope over the first:
*I gave a (#different) child each doll*. -/
theorem doc_frozen : firsts doc v docQuantifiers = {↑aGirl} := by decide +kernel

/-- No two candidates may be attracted first, so the double object construction is unambiguous. -/
theorem doc_not_ambiguous : ¬ Ambiguous doc v docQuantifiers := by decide +kernel

/-! ### The locative variant -/

/-- The PP that pied-pipes the goal. -/
def toAGirl : LinearizedSyntacticObject := {toP, aGirl}

/-- `{Ozzy, {v, {gave, {every telescope, {to, a girl}}}}}`. The direct object and the PP are
co-arguments of the same head, hence sisters, and c-command each other. -/
def locative : LinearizedSyntacticObject := {ozzy, {v, {gave, {everyTelescope, toAGirl}}}}

/-- The candidates in the locative, the direct object and the PP that pied-pipes the goal. -/
def locativeQuantifiers : List SyntacticObject := [everyTelescope, toAGirl]

-- Direct object and PP c-command each other, so neither asymmetrically c-commands the other.
example :
    CCommands locative everyTelescope toAGirl ∧ CCommands locative toAGirl everyTelescope := by
  constructor <;> decide

/-- Either candidate may be attracted first, since mutually c-commanding candidates are
equidistant. -/
theorem locative_firsts :
    firsts locative v locativeQuantifiers = {↑everyTelescope, ↑toAGirl} := by decide +kernel

/-- So the locative is ambiguous: *I gave a doll to each child* has both readings. -/
theorem locative_ambiguous : Ambiguous locative v locativeQuantifiers := by
  rw [Ambiguous, locative_firsts]
  decide

/-! ### The freezing is relativized -/

/-- The subject is merged in the attractor's specifier, outside its c-command domain, so it never
competes with the objects for attraction, and either object can take scope over it even where the
two objects' relative scope is frozen. -/
theorem subject_not_attractable : firsts doc v [ozzy] = ∅ := by decide +kernel

/-- The passive of a double object construction. With no external argument, the goal raises to the
subject position, out of the attractor's domain, leaving the theme as the only candidate. -/
def passive : LinearizedSyntacticObject := {aGirl, {v, {gave, {appl, everyTelescope}}}}

/-- In the passive the derived subject is no longer attractable while the theme is, so Shortest
imposes no order between them and the ambiguity returns: *a (different) girl was given every
telescope*. -/
theorem passive_ambiguous : firsts passive v docQuantifiers = {↑everyTelescope} := by
  decide +kernel

end Bruening2001
