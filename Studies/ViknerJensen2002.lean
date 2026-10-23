module

public import Linglib.Semantics.Possession.Quantifier
public import Studies.Pustejovsky1995
public import Linglib.Data.Examples.ViknerJensen2002

/-!
# Vikner & Jensen (2002): A Semantic Analysis of the English Genitive

For Vikner and Jensen every prenominal genitive combines a genitive phrase such as *a girl's*
with a relational noun. A sortal head noun such as *car* is first shifted to a relational one,
and the relation it gets comes from its lexical entry: one of its qualia in Pustejovsky's sense
(what it is part of, who made it, what it is for), or the general relation of control.

The genitive *'s* contains a hidden definite (16): *each girl's teacher* says that each girl has
exactly one teacher, with *the* inside the scope of *each*. A definite composed outside the
genitive phrase, the Montagovian *the* (13), would scope over *each* and demand one teacher
shared by all the girls; the two analyses agree for a name such as *Mary's* and come apart for
a quantified possessor. The genitive is Peters and Westerståhl's possessive quantifier for a
whole possessor noun phrase with Russell's *the* as its quantifier over possessed things
(`clitic`).

The shifts Co (23), Ag (30) and Te (47) turn a sortal noun into a relational one by its
constitutive, agentive and telic quale; Ctr (33) uses control and Prag (36) a relation supplied
by the context. All five are Barker's relationalizer `π` (`Sense.shift`, `Sense.shiftWith`).
The four lexical interpretations of a genitive (`RelationType`) are the relational nouns that
rules (55e) and (55f) derive from a word sense (`Sense.genitive`). A restriction on a relation,
such as the requirement that a controller be animate, leaves a reading empty rather than ruling
it out (*the car's cake*). *Favourite* (43) turns a relation into the relation of being the one
most preferred among one's relata; it keeps the relation of a relational noun, and from a
sortal noun it can use only the telic quale. So *Mary's movie* has two lexical interpretations
(the movie she made, the movie she has at her disposal), *Mary's favourite movie* has one (the
movie she most likes to watch), and *Anne's favourite sky* has none.

## Implementation notes

A quale is stored with the possessor-like entity first: `q y x` says that `y` is the whole, the
maker or the user of `x`. This is the "passive" argument order the paper considers in a
footnote, and it makes every shift an instance of the relationalizer; no result depends on the
order. Restrictions on relations, such as animacy, are stated as assumptions about the relations,
since the paper leaves them out of its derivations. A noun with both a relational and a sortal
use, such as *teacher*, is two senses. Postnominal and predicative genitives, the sort
hierarchy, and the revised shifts for nouns with complements (53) are not formalized.

## References

* [vikner-jensen-2002]
* [pustejovsky-1995]
* [barker-1995], [barker-2011]
* [partee-1997]
* [peters-westerstahl-2006]
-/

@[expose] public section

namespace ViknerJensen2002

open Possession Quantifier Quantifier.GQ Quantifier.NP

variable {E S : Type*}

/-! ### The genitive clitic -/

/-- The genitive *'s* (16): given a possessor noun phrase `Q` and a relational noun `R`, it
returns the possessive quantifier for `Q` with Russell's *the* over the things `Q` stands in `R`
to. The noun needs no separate restriction, since a relational noun already says what the
possessed things are. -/
def clitic (Q : NP E) (R : E → E → S → Prop) (s : S) : NP E :=
  PossNP Q the (fun u x ↦ R u x s) (fun _ ↦ True)

/-- Spelled out, *Q's R is P* says that `Q` holds of the property of having exactly one `R`,
which is `P`; the definite is inside the scope of `Q`, as in (16). -/
theorem clitic_apply (Q : NP E) (R : E → E → S → Prop) (s : S) (P : E → Prop) :
    clitic Q R s P ↔ Q (fun u ↦ ∃ x, (∀ y, R u y s ↔ y = x) ∧ P x) := by
  simp only [clitic, PossNP, dom, the, π_apply, Pi.inf_apply, inf_Prop_eq, true_and]
  refine iff_of_eq (congrArg Q (funext fun a ↦ propext (and_iff_right_of_imp ?_)))
  rintro ⟨x, hx, -⟩
  exact ⟨x, (hx x).2 rfl⟩

/-- With a sortal noun `W` shifted by a relation `R`, the genitive is the possessive quantifier
whose possessed things are the `W`s and whose possession relation is `R`. -/
theorem clitic_pi (Q : NP E) (W : E → S → Prop) (R : E → E → S → Prop) (s : S) :
    clitic Q (π W R) s = PossNP Q the (fun u x ↦ R u x s) (fun x ↦ W x s) := by
  funext P
  simp only [clitic, PossNP, dom, the, π_apply, Pi.inf_apply, inf_Prop_eq, true_and]

/-- *a's R is P* entails that `a` has exactly one `R`: the hidden definite. -/
theorem existsUnique_of_clitic_individual {a : E} {R : E → E → S → Prop} {s : S}
    {P : E → Prop} (h : clitic (individual a) R s P) : ∃! y, R a y s := by
  obtain ⟨x, hx, -⟩ := (clitic_apply _ _ _ _).1 h
  exact ⟨x, (hx x).2 rfl, fun y hy ↦ (hx y).1 hy⟩

/-- If the possessor stands in the relation to nothing, for instance because a restriction on
the relation excludes it, the genitive is false: *the car's cake* on the control reading. -/
theorem not_clitic_individual {a : E} {R : E → E → S → Prop} {s : S} (h : ∀ x, ¬ R a x s)
    (P : E → Prop) : ¬ clitic (individual a) R s P := by
  rw [clitic_apply]
  rintro ⟨x, hx, -⟩
  exact h x ((hx x).2 rfl)

/-! ### The scope of the definite (§3.2.2) -/

/-- The alternative the paper rejects: the Montagovian *the* (13) applied outside the genitive
phrase, so that it scopes over the possessor quantifier. *Each girl's teacher is P* then says
that there is exactly one individual who is every girl's teacher, and it is `P`. -/
def wideDefinite (Q : NP E) (R : E → E → S → Prop) (s : S) : NP E :=
  the (fun y ↦ Q (fun u ↦ R u y s))

/-- With a name as possessor the two analyses agree. -/
theorem clitic_individual (a : E) (R : E → E → S → Prop) (s : S) :
    clitic (individual a) R s = wideDefinite (individual a) R s := by
  funext P
  exact propext ((clitic_apply _ _ _ _).trans Iff.rfl)

/-- With a quantified possessor they come apart: if two girls have different teachers, *each
girl's teacher* (11b) is true on the paper's analysis and false with *the* outside. -/
theorem exists_clitic_ne_wideDefinite :
    ∃ (Q : NP (Fin 4)) (R : Fin 4 → Fin 4 → Unit → Prop) (P : Fin 4 → Prop),
      clitic Q R () P ∧ ¬ wideDefinite Q R () P :=
  ⟨every (· < 2), fun u y _ ↦ u = 0 ∧ y = 2 ∨ u = 1 ∧ y = 3, fun _ ↦ True,
    by rw [clitic_apply]; unfold every; decide,
    by simp only [wideDefinite, the, every]; decide⟩

/-! ### Senses and meaning shifts (§3.2.1, §3.2.3) -/

/-- The four relations a prenominal genitive can express without help from the context (§3.1.2,
Table 1; [barker-2011] reproduces the classification). Any other relation is a pragmatic
interpretation, available only when the context supplies it. -/
inductive RelationType where
  /-- The relation the head noun itself expresses: *the girl's teacher* is the person who is
  the girl's teacher. -/
  | inherent
  /-- The possessee is part of the possessor: *the girl's nose*, *the car's roof*. -/
  | partWhole
  /-- The possessor made or brought about the possessee: *the girl's poem* is the poem she
  wrote. -/
  | agentive
  /-- The possessor, who must be animate, has the possessee at their disposal: *the girl's car*,
  whether she owns it, has borrowed it or has hired it. -/
  | control
  deriving DecidableEq, Repr

/-- A word sense (9) is either sortal, a property, or relational, a relation whose first
argument is the possessor: `sister' y x` says that `x` is a sister of `y`. -/
inductive ArgStructure (E S : Type*)
  | sortal (W : E → S → Prop)
  | relational (R : E → E → S → Prop)

/-- A word sense: its argument structure and its qualia. Each quale is a relation whose first
argument is the related entity: the whole the thing is part of (constitutive quale, (22)), its
maker (agentive quale) or its user (telic quale) (9). -/
structure Sense (E S : Type*) where
  arg : ArgStructure E S
  quale : Pustejovsky1995.QualeRole → Option (E → E → S → Prop)

namespace Sense

variable (σ : Sense E S)

/-- The sortal predicate of a sortal sense. -/
def sortal : Option (E → S → Prop) :=
  match σ.arg with
  | .sortal W => some W
  | .relational _ => none

/-- The inherent relation of a relational sense. -/
def inherent : Option (E → E → S → Prop) :=
  match σ.arg with
  | .sortal _ => none
  | .relational R => some R

/-- The shift of a sortal noun by one of its qualia: *the girl's poem* on the agentive shift is
the poem whose maker is the girl. Co (23), Ag (30) and Te (47) use the constitutive, agentive
and telic quale. -/
def shift (r : Pustejovsky1995.QualeRole) : Option (E → E → S → Prop) :=
  σ.sortal.bind fun W ↦ (σ.quale r).map (π W)

/-- The shift of a sortal noun by a relation that does not come from its lexical entry: Ctr (33)
uses control, Prag (36) a relation supplied by the context. -/
def shiftWith (R : E → E → S → Prop) : Option (E → E → S → Prop) :=
  σ.sortal.map (π · R)

/-- For each of the four lexical interpretations, the relational noun a sense provides to a
genitive, by rules (55e) and (55f): the noun's own relation, its constitutive or agentive quale,
or control (`ctrl`). `none` means the sense does not provide that interpretation. A pragmatic
reading, `shiftWith` with a contextual relation, is always available in addition. -/
def genitive (ctrl : E → E → S → Prop) : RelationType → Option (E → E → S → Prop)
  | .inherent => σ.inherent
  | .partWhole => σ.shift .constitutive
  | .agentive => σ.shift .agentive
  | .control => σ.shiftWith ctrl

/-- The lexical interpretations a genitive has with this sense as head noun (Table 2). -/
def lexical (ctrl : E → E → S → Prop) : Set RelationType :=
  {t | σ.genitive ctrl t ≠ none}

end Sense

/-- A controller must be animate, so an inanimate possessor has no control reading: *the car's
cake*, column 2 of Table 2. -/
theorem not_clitic_control {ctrl : E → E → S → Prop} {animate : E → S → Prop}
    (hctrl : ∀ y x s, ctrl y x s → animate y s) {a : E} {s : S} (ha : ¬ animate a s)
    (W : E → S → Prop) (P : E → Prop) : ¬ clitic (individual a) (π W ctrl) s P :=
  not_clitic_individual (fun _ h ↦ ha (hctrl _ _ _ h.2)) P

/-! ### *Favourite* (§4) -/

/-- *Favourite* (43): `x` is `y`'s favourite `R` when `x` is an `R` of `y`'s and `y` prefers
being related by `R` to `x` over being related to any other of its `R`s. `prefer T T' y s` says
that `y` prefers the state of affairs `T'` to `T`. -/
def favourite (prefer : (S → Prop) → (S → Prop) → E → S → Prop) (R : E → E → S → Prop) :
    E → E → S → Prop :=
  fun y x s ↦ R y x s ∧ ∀ z, R y z s ∧ z ≠ x → prefer (R y z) (R y x) y s

variable {prefer : (S → Prop) → (S → Prop) → E → S → Prop}

/-- A favourite relatum is a relatum, so *Anne's favourite sister* is a sister of Anne's. -/
theorem favourite_rel {R : E → E → S → Prop} {y x : E} {s : S} (h : favourite prefer R y x s) :
    R y x s :=
  h.1

/-- Under an asymmetric preference the favourite is unique (footnote 21). -/
theorem favourite_subsingleton {R : E → E → S → Prop} {y : E} {s : S}
    (h : ∀ T T', prefer T T' y s → ¬ prefer T' T y s) :
    {x | favourite prefer R y x s}.Subsingleton :=
  fun x hx x' hx' ↦ by_contra fun hne ↦ h _ _ (hx.2 x' ⟨hx'.1, Ne.symm hne⟩) (hx'.2 x ⟨hx.1, hne⟩)

/-- *Favourite N* by (55d) with (55e) and (55f): *favourite* applies to the noun's own relation
if the noun is relational, and to its telic quale (what it is used for) if it is sortal. -/
def Sense.favourite (σ : Sense E S) (prefer : (S → Prop) → (S → Prop) → E → S → Prop) :
    Option (E → E → S → Prop) :=
  (σ.inherent <|> σ.shift .telic).map (ViknerJensen2002.favourite prefer)

/-! ### Predictions (§3.3, §4) -/

section Predictions

variable (ctrl : E → E → S → Prop)

/-- *sister* is relational (9). -/
def sister (sister' : E → E → S → Prop) : Sense E S := ⟨.relational sister', fun _ ↦ none⟩

/-- *movie*, like *poem* and *car* in (9), is a sortal artifact with an agentive and a telic
quale. -/
def movie (movie' : E → S → Prop) (make watch : E → E → S → Prop) : Sense E S :=
  ⟨.sortal movie', fun r ↦ match r with
    | .agentive => some make
    | .telic => some watch
    | _ => none⟩

/-- *sky* is sortal with no telic quale (§4). -/
def sky (sky' : E → S → Prop) : Sense E S := ⟨.sortal sky', fun _ ↦ none⟩

variable (sister' : E → E → S → Prop) (movie' sky' : E → S → Prop) (make watch : E → E → S → Prop)

/-- *Anne's sister* and *Anne's favourite sister* express the same relation. -/
theorem sister_genitive_inherent : (sister sister').genitive ctrl .inherent = some sister' := rfl

theorem sister_favourite :
    (sister sister').favourite prefer = some (favourite prefer sister') := rfl

/-- *Mary's movie* has two lexical interpretations, the movie Mary made and the movie Mary
controls. -/
theorem movie_lexical : (movie movie' make watch).lexical ctrl = {.agentive, .control} := by
  ext t
  cases t <;> simp [Sense.lexical, Sense.genitive, Sense.shift, Sense.shiftWith, Sense.sortal,
    Sense.inherent, movie]

/-- *Mary's favourite movie* has one, the movie Mary prefers to watch, different from both. -/
theorem movie_favourite :
    (movie movie' make watch).favourite prefer = some (favourite prefer (π movie' watch)) := rfl

/-- *Anne's favourite sky* has no lexical interpretation, only pragmatic ones, since *sky* has no
telic quale. -/
theorem sky_favourite : (sky sky').favourite prefer = none := rfl

/-- The pragmatic reading of *Anne's favourite sky* is available all the same. -/
theorem sky_pragmatic (relatedTo : E → E → S → Prop) :
    (sky sky').shiftWith relatedTo = some (π sky' relatedTo) := rfl

end Predictions

end ViknerJensen2002
