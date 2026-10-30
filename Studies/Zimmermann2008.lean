module

public import Linglib.Data.Examples.Zimmermann2008
public import Linglib.Fragments.Hausa.Determiners
public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Data.Finset.Card

/-!
# Zimmermann (2008): Quantification in Hausa

This file formalizes the scopal and quantificational observations of [zimmermann-2008]'s
chapter on the Hausa quantifier system in [matthewson-2008], whose inventory the fragment
`Hausa.Determiners` types after [newman-2000] and [jaggar-2001]. Bare indefinite noun phrases
always scope under negation, whether they follow or precede the negation marker, (11)–(14); the
chapter's preferred account makes them predicates whose existential force comes from the verb,
after van Geenhoven, so that negation over the verb yields a negative existential in either
position (`bareVerb`, `neg_bareVerb_iff`, `bare_no_wide_scope`). The marked indefinite *wani* is
an existential that is ambiguous under verb-phrase negation between the negative existential
and the some-not reading, (69), which come apart on a three-passenger model
(`wani_wide_scope`, `wani_narrow_scope_false`). The distributive universal *koo*+*wh* reads
as a negative existential under verb-phrase negation, (73), and as a negative universal under
sentence negation, (74): the first is the universal scoping over the negation
(`every_neg_iff_not_some`), and the two readings differ on the model
(`kowWh_negation_readings_diverge`). The collective universal *duk* takes a plural or mass
argument, (85)–(86), combines with collective predicates that the distributive *koo*+*wh*
rejects, (89)–(90) (`duk_collective`, `not_every_collective`), and yields the negative
universal under either negation, (91) (`neg_duk_iff`).

## Implementation notes

* The chapter leaves the choice among generalized-quantifier, indeterminate-pronoun and
  choice-function analyses of the class-B quantifiers open (§3.2.5); *wani* and *koo*+*wh* are
  read here as the determiner denotations `Det.some` and `every`, the first of the three.
* A collective predicate is one that holds only of pluralities of at least two members; the
  distributive universal applies it member by member and so fails.
* The binding differences of §4.2.3 and the adverbial quantifiers of §6 are not represented,
  nor are the plural-argument requirement of *duk*, (86), and the focus rescue of a subject
  *koo*+*wh*, (75) against (78).
* The collective rows are read by `collective_rows`, and the scope columns of the bare and
  *wani* rows are checked against the readings the analyses generate in `bare_scope_rows` and
  `wani_scope_rows`.

## References

* [zimmermann-2008]
* [matthewson-2008]
* [newman-2000]
* [jaggar-2001]
-/

@[expose] public section

namespace Zimmermann2008

open Hausa.Determiners Quantifier Quantifier.Det

variable {α E : Type*}

/-! ### Bare indefinites under negation, §2.1.3 -/

/-- A verb that forms a complex predicate with a bare indefinite argument: the existential
force comes from the verb, `λP λe. ∃x, P x ∧ V x e`. -/
def bareVerb (V : α → E → Prop) (P : α → Prop) (e : E) : Prop := ∃ x, P x ∧ V x e

/-- Negation over the verb yields the negative existential, (14): no bare-indefinite reading
scopes over negation, wherever the noun phrase sits. -/
theorem neg_bareVerb_iff (V : α → E → Prop) (P : α → Prop) (e : E) :
    ¬ bareVerb V P e ↔ ∀ x, P x → ¬ V x e := by
  simp [bareVerb]

/-! ### A three-passenger domain -/

/-- Three passengers, *faasinjojî*: Audù, Bàlki and Càdi. -/
inductive Faasinjee
  | audu | balki | cadi
  deriving DecidableEq, Repr, Fintype

/-- *yā daurà wàndà* 'buckled their seatbelt': Audù and Bàlki did, Càdi did not. -/
def Daura : Faasinjee → Prop
  | .audu => True
  | .balki => True
  | .cadi => False

instance : DecidablePred Daura := λ x => match x with
  | .audu => isTrue trivial
  | .balki => isTrue trivial
  | .cadi => isFalse id

/-- The bare-indefinite reading of *passengers didn't buckle* is false on the model while the
wide-scope some-not reading is true (13). -/
theorem bare_no_wide_scope :
    ¬ ¬ bareVerb (λ x (_ : Unit) => Daura x) (λ _ => True) () ∧
      ∃ x : Faasinjee, ¬ Daura x :=
  ⟨λ h => h ⟨.audu, trivial, trivial⟩, ⟨.cadi, id⟩⟩

/-! ### The class-B quantifiers, §3.2 -/

theorem wani_wide_scope : Det.some Set.univ {x : Faasinjee | ¬ Daura x} :=
  ⟨.cadi, trivial, id⟩

/-- The negative existential reading, no passenger buckled their seatbelt, (69i), fails: Audù
did. -/
theorem wani_narrow_scope_false : ¬ ¬ ∃ x : Faasinjee, Daura x :=
  λ h => h ⟨.audu, trivial⟩

-- (69)
theorem wani_ambiguity_witness :
    Det.some Set.univ {x : Faasinjee | ¬ Daura x} ∧ ¬ ¬ ∃ x : Faasinjee, Daura x :=
  ⟨wani_wide_scope, wani_narrow_scope_false⟩

/-- The universal over the negation is the negative existential: *koo*+*wh* under verb-phrase
negation, (73), *I saw no one*. -/
theorem every_neg_iff_not_some (R S : Set α) : every R Sᶜ ↔ ¬ Det.some R S :=
  no_iff_not_some

/-- The negative existential of (73) and the negative universal of (74) differ on the model. -/
theorem kowWh_negation_readings_diverge :
    ¬ every Set.univ {x : Faasinjee | Daura x} ∧ ¬ every Set.univ {x : Faasinjee | ¬ Daura x} :=
  ⟨fun h ↦ h (Set.mem_univ Faasinjee.cadi), fun h ↦ h (Set.mem_univ Faasinjee.audu) trivial⟩

/-! ### The two universals, §4 -/

/-- The distributive universal *koo*+*wh*: the determiner denotation `every` over a set of
individuals. -/
def kowWhSem (R S : Set α) : Prop := every R S

/-- The collective universal *duk*: its plural or mass argument, (85)–(86), is a plurality, and
the predicate applies to the plurality as a whole. -/
def dukSem (R : Finset α) (S : Finset α → Prop) : Prop := S R

/-- A collective predicate such as *tàaru* 'gather' or *keewàyee* 'surround' holds only of
pluralities with at least two members. -/
def Collective (S : Finset α → Prop) : Prop := ∀ s, S s → 2 ≤ s.card

/-- *Duk* combines with a collective predicate, (90): the students gathered as a group. -/
theorem duk_collective {R : Finset α} {S : Finset α → Prop} (h : S R) : dukSem R S := h

/-- *Koo*+*wh* cannot combine with a collective predicate, (89): applying it member by member
asks each singleton to gather, which no collective predicate allows. -/
theorem not_every_collective {R : Finset α} {S : Finset α → Prop} (hS : Collective S)
    (hR : R.Nonempty) : ¬ kowWhSem ↑R {x | S {x}} := by
  obtain ⟨x, hx⟩ := hR
  intro h
  have := hS {x} (h hx)
  simp at this

/-- *Duk* under negation is the negative universal *not all*, (91), under verb-phrase and
sentence negation alike: for a distributive predicate, not every member satisfies it. -/
theorem neg_duk_iff (R : Finset α) (P : α → Prop) :
    ¬ dukSem R (fun s ↦ ∀ x ∈ s, P x) ↔ ¬ every ↑R {x | P x} := by
  simp [dukSem, every, Set.subset_def]

theorem kowWh_daura_false : ¬ kowWhSem Set.univ {x : Faasinjee | Daura x} :=
  fun h ↦ h (Set.mem_univ Faasinjee.cadi)

/-! ### The data -/

section Data

open Examples

/-- The universal of a collective-predicate row. -/
inductive RowUniversal where
  | kowWh
  | duk
  deriving DecidableEq, Repr

/-- A collective test row: its universal quantifier. -/
def collectiveTest? (e : Datum) : Option RowUniversal := do
  let q ← e.parse? "quantifier" [("koo+wh", .kowWh), ("duk", .duk)]
  let _ ← e.parse? "predicate" [("collective", ())]
  pure q

/-- The collective rows (89)–(90): the distributive universal rejects a collective predicate,
which cannot hold of singletons (`not_every_collective`), and the collective universal takes it
(`duk_collective`). -/
theorem collective_rows : ∀ e ∈ Examples.all, e.Fits collectiveTest? fun q ↦
    match q with
    | .kowWh => .rejected
    | .duk => .accepted := by
  decide

theorem collective_read : Datum.ReadCount collectiveTest? Examples.all 2 := by decide

/-- The scope column of the bare-indefinite rows (11)–(13) is the one reading the predicative
analysis generates, the negative existential (`neg_bareVerb_iff`, `bare_no_wide_scope`). -/
theorem bare_scope_rows : ∀ e ∈ Examples.all, ∀ _ ∈ e.parse? "indefinite" [("bare", ())],
    e.feature? "scope" = some "NEG > ∃" := by
  decide

/-- The scope column of the object *wani* rows (69) is the ambiguity the three-passenger model
witnesses (`wani_ambiguity_witness`). -/
theorem wani_scope_rows : ∀ e ∈ Examples.all, ∀ _ ∈ e.parse? "indefinite" [("wani", ())],
    ∀ s ∈ e.feature? "scope", s = "ambiguous" := by
  decide

theorem scope_read :
    ((Examples.all.filter fun e => (e.parse? "indefinite" [("bare", ())]).isSome).length,
      (Examples.all.filter fun e => (e.parse? "indefinite" [("wani", ())]).isSome ∧
        (e.feature? "scope").isSome).length) = (3, 2) := by
  decide

end Data

end Zimmermann2008
