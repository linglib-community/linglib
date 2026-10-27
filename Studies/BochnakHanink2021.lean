module

public import Linglib.Fragments.Washo.Clause
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes
public import Studies.Hanink2021
public import Linglib.Syntax.Minimalist.Clause.Spine

/-!
# Bochnak & Hanink (2021): Clausal embedding in Washo: complementation vs. modification

This file formalizes Bochnak and Hanink's two strategies of clausal embedding in Washo. A
presuppositional predicate selects a nominalized clause as a DP complement. A
non-presuppositional predicate is intransitive, and its dependent-mood clause is an adjoined
modifier. We read selection off the Fragment's frames and derive Table 2 from it: a predicate
selects iff it takes the nominalizer as clause-typer, and the selected clause is a CP under D
while the modifier is a MoodP without C.

The nominalized complement is Hanink's familiar DP over the FPROP type-shift, so it denotes the
individual whose content is the embedded proposition. It is defined when that individual is
familiar, not when the proposition is true, which is the paper's case against a lexical factivity
presupposition (`not_factive`). The dependent mood is generalized conjunction, so a modifier
equates the content of the attitude event with its clause, and two modifiers on one event cannot
carry different contents (`stack_eq`).

## Implementation notes

* `Cat` has no mood head, so the MoodP of (47b) is the T-level spine; what matters is that it
  projects neither C nor D.
* The holder and theme arguments of the event semantics in (78) and (92) are not represented,
  the content function drops the paper's world index, and the independent mood *-i*, the
  identity (74), has no declaration.
* `not_factive` is a structural witness about the familiar DP, not a Washo datum.

## TODO

* Conjunction over propositions (97) in concessive adjuncts, and the tenseless simultaneous
  adjuncts of (100)–(101) (§5.5).

## References

* [bochnak-hanink-2021]
* [hanink-2021]
* [kastner-2015]
* [elliott-2016]
-/

@[expose] public section

namespace BochnakHanink2021

open Washo Minimalist
open scoped Denotes

/-! ### Selection -/

/-- A predicate selects if it has an internal-argument frame (§3.2.2). -/
def Selects (v : Washo.Verb) : Prop := ¬ v.toVerb.IsIntransitive

instance : DecidablePred Selects := fun v ↦ inferInstanceAs (Decidable (¬ v.toVerb.IsIntransitive))

theorem selects_iff_takes_ge : ∀ v ∈ verbs, Selects v ↔ v.toVerb.Takes ge := by
  decide

/-- The spine of a nominalized complement, a CP under a silent D (3). -/
def complementSpine : ClauseSpine := ClauseSpine.cP.append [.D]

/-- The spine of a dependent-mood modifier, a MoodP without C ((4), (47b)). -/
def modifierSpine : ClauseSpine := ClauseSpine.tP

/-- The spine of the clause a predicate embeds. -/
def spine (v : Washo.Verb) : ClauseSpine :=
  if Selects v then complementSpine else modifierSpine

-- Table 2
theorem spine_projects_D_iff :
    ∀ v ∈ verbs, (.D ∈ spine v ↔ v.typer = ge) ∧ (.C ∈ spine v ↔ v.typer = ge) := by
  decide

-- (53), (55)
theorem suus_selects_gumsuus_not : Selects suus ∧ ¬ Selects gumsuus := by
  decide

/-! ### Denotations -/

variable {E W : Type} (cont : E → W → Prop) (p q : W → Prop) (d : ℕ) (g : Assignment E) (s : W)

/-- The FPROP type-shift, the property of the individuals whose content is `p` (76). -/
def fprop : E → Prop := fun x ↦ cont x = p

/-- The nominalized complement with index `d`, the familiar DP over FPROP (77). -/
def complement : DefiniteDescription E W := .anaphoric (fun _ _ x ↦ fprop cont p x) d

-- (78)
theorem denote_complement :
    ⟦complement cont p d⟧ g s = iota fun x ↦ cont x = p ∧ Hanink2021.idxVar d g x := rfl

-- §5.3
theorem denote_complement_isSome_iff : (⟦complement cont p d⟧ g s).isSome ↔ cont (g d) = p :=
  DefiniteDescription.denote_anaphoric_isSome_iff _ _ _ _

/-- The complement can be defined at a situation where its content is false: familiarity is
not factivity (§5.3.1), the warrant for (86)–(87) in §5.3.2. -/
theorem not_factive :
    ∃ (cont : Unit → Bool → Prop) (p : Bool → Prop) (g : Assignment Unit) (s : Bool),
      (⟦complement cont p 0⟧ g s).isSome ∧ ¬ p s :=
  ⟨fun _ ↦ (· = true), (· = true), fun _ ↦ (), false,
    (denote_complement_isSome_iff ..).2 rfl, Bool.false_ne_true⟩

/-- The dependent mood is generalized conjunction (75). -/
def dependentMood {α : Type*} (P Q : α → Prop) : α → Prop := P ⊓ Q

-- (92)
theorem dependentMood_fprop (V : E → Prop) (x : E) :
    dependentMood (fprop cont p) V x ↔ cont x = p ∧ V x := Iff.rfl

/-- Two dependent-mood clauses on one event have the same content (§5.4). -/
theorem stack_eq (V : E → Prop) {x : E}
    (h : dependentMood (fprop cont p) (dependentMood (fprop cont q) V) x) : p = q :=
  h.1.symm.trans h.2.1

end BochnakHanink2021
