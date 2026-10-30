module

public import Linglib.Semantics.Possession.Quantifier
public import Studies.Pustejovsky1995
public import Linglib.Data.Examples.ViknerJensen2002

/-!
# Vikner & Jensen (2002): A Semantic Analysis of the English Genitive

This file formalizes Vikner and Jensen's analysis of the English prenominal genitive. The
genitive `'s` combines a possessor noun phrase with a relational noun and carries an implicit
definite in the scope of the possessor (`clitic`, (16)). A sortal head noun is made relational by
Barker's relationalizer applied to one of its qualia or to the control relation (`Sense.shift`,
`Sense.shiftWith`).

## Implementation notes

A quale `q y x` takes the related entity first (`y` is the whole, maker or user of `x`), an order
the paper considers in a footnote, so that every shift is the relationalizer. Selectional
restrictions such as the animacy of a controller are hypotheses on the relations. A noun with a
relational and a sortal use is two senses. Postnominal and predicative genitives, the sort
hierarchy and the revised shifts for nouns with complements (53) are not formalized.

## References

* [vikner-jensen-2002]
* [pustejovsky-1995]
* [barker-1995], [barker-2011]
* [partee-1997]
* [peters-westerstahl-2006]
-/

@[expose] public section

namespace ViknerJensen2002

open Possession Quantifier Quantifier.Det

variable {E S : Type*}

/-! ### The genitive clitic -/

/-- The genitive `'s` (16) is the possessive quantifier of `Q` over the relational noun `R`, with
the definite as possessee quantifier. -/
def clitic (Q : Quantifier E) (R : E → E → S → Prop) (s : S) : Quantifier E :=
  PossNP Q the (fun u x ↦ R u x s) Set.univ

-- (16)
theorem clitic_apply (Q : Quantifier E) (R : E → E → S → Prop) (s : S) (P : Set E) :
    clitic Q R s P ↔ Q {u | ∃ x, (∀ y, R u y s ↔ y = x) ∧ x ∈ P} := by
  simp only [clitic, PossNP, the, π_apply, Set.inf_eq_inter, Set.univ_inter]
  refine iff_of_eq (congrArg Q (Set.ext fun a ↦ and_iff_right_of_imp ?_))
  rintro ⟨x, hx, -⟩
  exact ⟨x, trivial, (hx x).2 rfl⟩

theorem clitic_pi (Q : Quantifier E) (W : E → S → Prop) (R : E → E → S → Prop) (s : S) :
    clitic Q (π W R) s = PossNP Q the (fun u x ↦ R u x s) {x | W x s} :=
  funext fun _ ↦ congrArg Q <| Set.ext fun _ ↦ and_congr
    ⟨fun ⟨y, _, hy⟩ ↦ ⟨y, hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, trivial, hy⟩⟩
    (exists_congr fun _ ↦ and_congr_left' <| forall_congr' fun _ ↦
      iff_congr (and_iff_right trivial) .rfl)

theorem existsUnique_of_clitic_individual {a : E} {R : E → E → S → Prop} {s : S}
    {P : Set E} (h : clitic (individual a) R s P) : ∃! y, R a y s := by
  obtain ⟨x, hx, -⟩ := (clitic_apply _ _ _ _).1 h
  exact ⟨x, (hx x).2 rfl, fun y hy ↦ (hx y).1 hy⟩

theorem not_clitic_individual {a : E} {R : E → E → S → Prop} {s : S} (h : ∀ x, ¬ R a x s)
    (P : Set E) : ¬ clitic (individual a) R s P := by
  rw [clitic_apply]
  rintro ⟨x, hx, -⟩
  exact h x ((hx x).2 rfl)

/-! ### The scope of the definite (§3.2.2) -/

/-- The Montagovian definite (13) applied outside the genitive phrase, scoping over the
possessor quantifier. -/
def wideDefinite (Q : Quantifier E) (R : E → E → S → Prop) (s : S) : Quantifier E :=
  the {y | Q {u | R u y s}}

theorem clitic_individual (a : E) (R : E → E → S → Prop) (s : S) :
    clitic (individual a) R s = wideDefinite (individual a) R s := by
  funext P
  exact propext ((clitic_apply _ _ _ _).trans Iff.rfl)

/-- With a quantified possessor, `clitic` and `wideDefinite` differ (11b). -/
theorem exists_clitic_ne_wideDefinite :
    ∃ (Q : Quantifier (Fin 4)) (R : Fin 4 → Fin 4 → Unit → Prop) (P : Set (Fin 4)),
      clitic Q R () P ∧ ¬ wideDefinite Q R () P :=
  ⟨every {x | x < 2}, fun u y _ ↦ u = 0 ∧ y = 2 ∨ u = 1 ∧ y = 3, Set.univ,
    by rw [clitic_apply]; decide,
    by unfold wideDefinite the; decide⟩

/-! ### Senses and meaning shifts (§3.2.1, §3.2.3) -/

/-- The lexical interpretations of the genitive relation (§3.1.2, Table 1), as reproduced in
[barker-2011]. -/
inductive RelationType where
  /-- The relation of a relational head noun (*the girl's teacher*). -/
  | inherent
  /-- Whole and part (*the girl's nose*). -/
  | partWhole
  /-- Creator and creation (*the girl's poem*). -/
  | agentive
  /-- Control by an animate possessor (*the girl's car*). -/
  | control
  deriving DecidableEq, Repr

/-- The argument structure of a sense (9) is a property, or a relation with the possessor first, so
that `sister' y x` reads *x is a sister of y*. -/
inductive ArgStructure (E S : Type*)
  | sortal (W : E → S → Prop)
  | relational (R : E → E → S → Prop)

/-- A word sense (9) is an argument structure with its qualia, each a relation whose first argument
is the related entity, that is the whole (22), the maker or the user. -/
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

/-- Shift a sortal sense by one of its qualia, giving Co (23), Ag (30) and Te (47). -/
def shift (r : Pustejovsky1995.QualeRole) : Option (E → E → S → Prop) :=
  σ.sortal.bind fun W ↦ (σ.quale r).map (π W)

/-- Shift a sortal sense by a given relation, giving Ctr (33) for control and Prag (36) for a
contextual relation. -/
def shiftWith (R : E → E → S → Prop) : Option (E → E → S → Prop) :=
  σ.sortal.map (π · R)

/-- The relational noun a sense provides for each lexical interpretation, by rules (55e) and
(55f), or `none`. -/
def genitive (ctrl : E → E → S → Prop) : RelationType → Option (E → E → S → Prop)
  | .inherent => σ.inherent
  | .partWhole => σ.shift .constitutive
  | .agentive => σ.shift .agentive
  | .control => σ.shiftWith ctrl

/-- The lexical interpretations a sense admits (Table 2). -/
def lexical (ctrl : E → E → S → Prop) : Set RelationType :=
  {t | σ.genitive ctrl t ≠ none}

end Sense

/-- An inanimate possessor has no control reading (*the car's cake*, Table 2). -/
theorem not_clitic_control {ctrl : E → E → S → Prop} {animate : E → S → Prop}
    (hctrl : ∀ y x s, ctrl y x s → animate y s) {a : E} {s : S} (ha : ¬ animate a s)
    (W : E → S → Prop) (P : Set E) : ¬ clitic (individual a) (π W ctrl) s P :=
  not_clitic_individual (fun _ h ↦ ha (hctrl _ _ _ h.2)) P

/-! ### *Favourite* (§4) -/

/-- The meaning of *favourite* (43), under which `x` is `y`'s favourite `R` iff `x` is an `R` of
`y`'s and `y` prefers it to its other `R`s, where `prefer T T' y s` means that `y` prefers `T'` to
`T`. -/
def favourite (prefer : (S → Prop) → (S → Prop) → E → S → Prop) (R : E → E → S → Prop) :
    E → E → S → Prop :=
  fun y x s ↦ R y x s ∧ ∀ z, R y z s ∧ z ≠ x → prefer (R y z) (R y x) y s

variable {prefer : (S → Prop) → (S → Prop) → E → S → Prop}

theorem favourite_rel {R : E → E → S → Prop} {y x : E} {s : S} (h : favourite prefer R y x s) :
    R y x s :=
  h.1

-- footnote 21
theorem favourite_subsingleton {R : E → E → S → Prop} {y : E} {s : S}
    (h : ∀ T T', prefer T T' y s → ¬ prefer T' T y s) :
    {x | favourite prefer R y x s}.Subsingleton :=
  fun x hx x' hx' ↦ by_contra fun hne ↦ h _ _ (hx.2 x' ⟨hx'.1, Ne.symm hne⟩) (hx'.2 x ⟨hx.1, hne⟩)

/-- *Favourite N* (55d–f) applies *favourite* to the relation of a relational sense or to the telic
shift of a sortal one. -/
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

theorem sky_pragmatic (relatedTo : E → E → S → Prop) :
    (sky sky').shiftWith relatedTo = some (π sky' relatedTo) := rfl

end Predictions

end ViknerJensen2002
