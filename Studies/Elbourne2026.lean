module

public import Linglib.Data.Examples.Elbourne2026
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Mode.Basic
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Modification.Classification
public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Powerset

/-!
# Elbourne (2026): Adjectives without syntactic categories

Elbourne replaces syntactic categories by semantic types in a grammar that composes by functional
application alone, and gives every adjective the type ⟨eit,eit⟩ of a function on noun meanings,
where [application does the work of predicate modification](##simulates_predicateModification).
[Nothing that takes a noun merges with an adjective](##not_merges_of_takes_noun), which excludes
*Every red is attractive*, while [a copula takes just the adjectives without compulsory
features](##merges_copula_iff), which excludes *The president is former*. The copula applies the
adjective to the trivial noun, where [a privative adjective is a
contradiction](##copula_eq_bot_of_isPrivative), and [*former* and an intersective adjective
differ in their two orders](##exists_not_commute_former), a difference of scope rather than type.

## Implementation notes

* The types are those over `Interpreter.Base`, with the type `i` of time intervals left as a
  variable, entity first as printed. The meanings are `Modifier (I → E → Prop)`, times first as
  in the substrate's `Modifier.former`, with conjuncts reordered, so that the second meaning
  (32) of *a* is `Modifier.intersective`.
* The syntax of §2 enters through the selector features of (8) and External Merge (4a), which
  puts the bearer of `E_R` on the left as the function. Predicate Abstraction and traces are Lean
  binders; Scope Economy (7) is not represented.
* *Agent* and *Theme* are the relations of an `ArgumentStructure.ThematicFrame`, and `CUL` is a
  function from events to times.

## Errata

* (54) gives *local* a compulsory `E_R`, which by the account of (42) keeps it from standing
  alone after the copula, as in *This bar is local*; the optional ⟨`E_R`⟩ of *cute* would not.
* The feature left on little v after (20) is named `i⟨et,t⟩` in the text; it is `i⟨eit,it⟩`, as
  in (8) and in the tree.

## References

* [elbourne-2026]
* [elbourne-2024]
* [collins-stabler-2016]
* [heim-kratzer-1998]
* [parsons-1970]
* [lewis-1970]
* [montague-1973]
* [kamp-partee-1995]
* [mcnally-boleda-2004]
* [morzycki-2015]
* [cresswell-1976]
-/

@[expose] public section

namespace Elbourne2026

open Interpreter Modifier Elbourne2026.Examples

/-! ### Types and selector features -/

/-- The type ⟨e,it⟩ of nouns, where `i` is the type of time intervals. -/
def eit (i : Ty Base) : Ty Base := .e ⇒ i ⇒ .t

/-- The selector features `E_L` and `E_R` (1) trigger External Merge (4) with a constituent to
the left or to the right. -/
inductive Selector
  | eL
  | eR
  deriving DecidableEq

/-- The syntactic features of a lexical entry (8) are the compulsory ones and, in angle brackets,
the optional ones. -/
structure Features where
  /-- Features every use of the entry carries. -/
  compulsory : Finset Selector
  /-- Features an entry may enter the derivation with or without. -/
  optional : Finset Selector
  /-- A feature of an entry is either compulsory or optional. -/
  disjoint : Disjoint compulsory optional := by decide

namespace Features

/-- An entry can enter a derivation with its compulsory features together with any choice of its
optional ones. -/
def bundles (f : Features) : Finset (Finset Selector) :=
  f.optional.powerset.image (f.compulsory ∪ ·)

/-- An entry takes a noun to its right by External Merge (4a) when one of its bundles carries
`E_R`. -/
def TakesNoun (f : Features) : Prop := ∃ b ∈ f.bundles, Selector.eR ∈ b

/-- By Argument Interpretability (6) a constituent selected by a selector feature, as the
adjective is by the copula's `E_R`, contains no uninterpretable feature, so an entry is selectable
when one of its bundles is empty. -/
def Selectable (f : Features) : Prop := ∅ ∈ f.bundles

theorem selectable_iff (f : Features) : f.Selectable ↔ f.compulsory = ∅ := by
  simp only [Selectable, bundles, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨_, _, h⟩
    exact (Finset.union_eq_empty.mp h).1
  · intro h
    exact ⟨∅, Finset.empty_subset _, by rw [h, Finset.empty_union]⟩

theorem takesNoun_iff (f : Features) : f.TakesNoun ↔ Selector.eR ∈ f.compulsory ∪ f.optional := by
  simp only [TakesNoun, bundles, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨_, ⟨_, ha, rfl⟩, h⟩
    exact Finset.union_subset_union_right ha h
  · intro h
    exact ⟨_, ⟨f.optional, Finset.Subset.refl _, rfl⟩, h⟩

/-- *cute* (8) has an optional `E_R`, as most adjectives do (§3.2), *red* (37) among them. -/
def cute : Features where
  compulsory := ∅
  optional := {Selector.eR}

/-- *former* and *mere* (§3.2) have a compulsory `E_R`. -/
def former : Features where
  compulsory := {Selector.eR}
  optional := ∅

/-- Russian short-form adjectives (§4.2) have no selector features. -/
def shortForm : Features where
  compulsory := ∅
  optional := ∅

/-- Russian long-form adjectives (§4.2) have optional `E_R` and `E_L`. -/
def longForm : Features where
  compulsory := ∅
  optional := {Selector.eR, Selector.eL}

end Features

section Merge

variable (i : Ty Base)

/-- Functional Application (9), the one rule of composition: by External Merge (4a) the left
daughter, the bearer of `E_R`, is the function, and its argument has the type of the right. -/
def Applies (σ τ : Ty Base) : Prop := ∃ ρ, σ = (τ ⇒ ρ)

/-- An adjective with features `f` merges with a sister of type `σ` when either it takes the
sister as its noun by `E_R`, or the sister takes the adjective, which by Argument
Interpretability (6) then carries no feature. -/
def Merges (f : Features) (σ : Ty Base) : Prop :=
  Applies (eit i ⇒ eit i) σ ∧ f.TakesNoun ∨ Applies σ (eit i ⇒ eit i) ∧ f.Selectable

variable {i} {f : Features}

section Composition

variable {E W : Type}

/-- The meanings of a structure by Functional Application (9) alone, its leaves being their own
lexical entries. -/
def byApplication (t : PhraseStructure.Tree Unit (Denotation E W)) : List (Denotation E W) :=
  t.values (typeDriven application) (D := Ty.Dom (Base.Dom E W)) inferInstance id
    (Sum.elim (fun x ↦ [x]) fun _ ↦ [])

/-- The meanings of a structure in the grammar of the ⟨e,t⟩ theory, which adds Predicate
Modification to Functional Application (§3.1). -/
def withModification (t : PhraseStructure.Tree Unit (Denotation E W)) :
    List (Denotation E W) :=
  t.values (typeDriven (application.sum predicateModification))
    (D := Ty.Dom (Base.Dom E W)) inferInstance id (Sum.elim (fun x ↦ [x]) fun _ ↦ [])

-- (24)–(26): *cute donkey* means by Functional Application alone, with *cute* a function on
-- noun meanings, what it means by Predicate Modification with *cute* a property.
theorem byApplication_cute_donkey (cute donkey : E → Prop) :
    byApplication (W := W)
        (.bin (.leaf ⟨.et ⇒ .et, intersective cute⟩) (.leaf ⟨.et, donkey⟩)) =
      withModification (.bin (.leaf ⟨.et, cute⟩) (.leaf ⟨.et, donkey⟩)) :=
  rfl

-- (26): the one meaning of *cute donkey*, the conjunction.
example (cute donkey : E → Prop) :
    byApplication (W := W)
        (.bin (.leaf ⟨.et ⇒ .et, intersective cute⟩) (.leaf ⟨.et, donkey⟩)) =
      [⟨.et, cute ⊓ donkey⟩] :=
  rfl

-- Without the rule, two properties do not combine.
example (cute donkey : E → Prop) :
    byApplication (W := W) (.bin (.leaf ⟨.et, cute⟩) (.leaf ⟨.et, donkey⟩)) = [] :=
  rfl

/-- The lift of a property to a function on noun meanings: what an adjective of the ⟨et,et⟩
theory is to the adjective of the ⟨e,t⟩ theory, as *cute* (24b) is to the property of being
cute. -/
inductive Lift {B : Type} : Ty B → Ty B → Type
  /-- The lift. -/
  | lift {a : Ty B} : Lift (a ⇒ .t) ((a ⇒ .t) ⇒ a ⇒ .t)

/-- A lifted property is the intersective modifier of that property. -/
def Lift.eval {B : Type} (D : B → Type) : {a b : Ty B} → Lift a b → a.Dom D → b.Dom D
  | _, _, .lift, p => fun q x ↦ p x ∧ q x

/-- The grammar whose one rule lifts a property. -/
@[reducible] def lifting {B : Type} : ManySorted.Language (Ty B) :=
  .mk₂ Lift fun _ _ _ ↦ PEmpty

instance {B : Type} (D : B → Type) : (lifting (B := B)).Structure (Ty.Dom D) :=
.mk₂ (Lift.eval D) nofun

/-- Whatever the ⟨e,t⟩ theory derives with Functional Application and Predicate Modification,
Functional Application derives with the same value once the modifier is lifted, at any type and
over any domains, so the theory does without Predicate Modification (§3.1) and research under
the ⟨e,t⟩ theory translates into it (§3.3). The lift is of words in Elbourne's lexicon and of
any left daughter here; the converse fails for *former* (§3.4). -/
theorem simulates_predicateModification {B : Type} (D : B → Type) :
    ManySorted.Language.Structure.Simulates
      (inferInstance : (application.sum lifting).Structure (Ty.Dom D))
      (inferInstance :
        (application.sum predicateModification).Structure (Ty.Dom D)) where
  funMap {σ _} f := by
    obtain m | m := f
    · rcases σ with _ | _ | ⟨_ | _ | _, _ | _ | _⟩ <;> first
        | (cases m; done)
        | exact ⟨ManySorted.Language.Deriv.binary (.inl m) (.leaf (.left .here))
            (.leaf (.right .here)), fun _ ↦ rfl⟩
    · rcases σ with _ | _ | ⟨_ | _ | _, _ | _ | _⟩ <;> first
        | (cases m; done)
        | (obtain ⟨⟩ := m
           exact ⟨ManySorted.Language.Deriv.binary (.inl .fa)
            (ManySorted.Language.Deriv.unary (.inr .lift) (.leaf (.left .here)))
            (.leaf (.right .here)), fun _ ↦ rfl⟩)

end Composition

-- §3.1: an adjective takes a noun in attributive position by its `E_R`.
theorem merges_noun_iff : Merges i f (eit i) ↔ Selector.eR ∈ f.compulsory ∪ f.optional := by
  simp [Merges, Applies, eit, Features.takesNoun_iff]

/-- Whatever takes an adjective as its argument, such as the copula with its tense, of type
⟨⟨eit,eit⟩,eit⟩, takes just the adjectives without compulsory features. The types work out for
*The president is former* (42), and the compulsory `E_R` of *former* excludes it. -/
theorem merges_copula_iff (ρ : Ty Base) : Merges i f ((eit i ⇒ eit i) ⇒ ρ) ↔ f.compulsory = ∅ := by
  simp [Merges, Applies, eit, Features.selectable_iff]

/-- Nothing that takes a noun merges with an adjective in either role, neither a determiner, of
type ⟨eit,⟨eit,it⟩⟩, nor the second meaning (32) of *a*, of type ⟨eit,⟨eit,eit⟩⟩. This excludes
*Joe is a former* (36) and *Every red is attractive* (37) by type alone. -/
theorem not_merges_of_takes_noun (ρ : Ty Base) : ¬ Merges i f (eit i ⇒ ρ) := by
  simp [Merges, Applies, eit]

/-- A row on the position of an adjective, read as the merge of the adjective with its sister. -/
structure Row where
  /-- The example. -/
  datum : Datum
  /-- The features of its adjective. -/
  features : Features
  /-- The type of the adjective's sister. -/
  sister : Ty Base

variable (i)

/-- The rows on the positions of adjectives, the sister being the copula with its tense, a
determiner, or a noun. -/
def distribution : List Row :=
  [⟨ex_28, .cute, (eit i ⇒ eit i) ⇒ eit i⟩, ⟨ex_36, .former, eit i ⇒ eit i ⇒ i ⇒ .t⟩,
    ⟨ex_37, .cute, eit i ⇒ eit i ⇒ i ⇒ .t⟩, ⟨ex_42, .former, (eit i ⇒ eit i) ⇒ eit i⟩,
    ⟨ex_45, .former, eit i⟩, ⟨ex_64_long, .longForm, (eit i ⇒ eit i) ⇒ eit i⟩,
    ⟨ex_64_short, .shortForm, (eit i ⇒ eit i) ⇒ eit i⟩, ⟨ex_65a, .longForm, eit i⟩,
    ⟨ex_65b, .shortForm, eit i⟩]

theorem rows_merge :
    ∀ r ∈ distribution i, (r.datum.judgment = .acceptable ↔ Merges i r.features r.sister) := by
  simp only [distribution, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true, merges_noun_iff, merges_copula_iff, not_merges_of_takes_noun, iff_false]
  decide

end Merge

/-! ### Predicative position -/

section Meanings

variable {I E : Type*}

/-- The copula BE of (8), `λR⟨i,it⟩.λG⟨eit,eit⟩.λx.λt.∃t'(R(t')(t) & G(λy.λt''.⊤)(x)(t'))`,
applies the adjective to the trivial noun `⊤` at a time that the tense relation `R` locates. -/
def copula (R : I → I → Prop) (G : Modifier (I → E → Prop)) : I → E → Prop :=
  fun t x ↦ ∃ t', R t' t ∧ G ⊤ t' x

theorem copula_intersective (R : I → I → Prop) (Q : I → E → Prop) :
    copula R (intersective Q) = fun t x ↦ ∃ t', R t' t ∧ Q t' x := by
  funext t x
  simp only [copula, intersective, inf_top_eq]

-- (28)–(30)
theorem fido_was_cute [LT I] (cute : I → E → Prop) (o : E) (t : I) :
    copula (· < ·) (intersective cute) t o ↔ ∃ t' < t, cute t' o := by
  rw [copula_intersective]

/-- A determiner of (8) is a classical determiner applied at the evaluation time: *every*,
`λf⟨e,it⟩.λg⟨e,it⟩.λt.∀x(f(x)(t) → g(x)(t))`, is `Quantifier.Det.every`, and *some* and the
quantificational *a* are `Quantifier.Det.some`. -/
def atTime (D : Quantifier.Det E) (f g : I → E → Prop) (t : I) : Prop :=
  D {x | f t x} {x | g t x}

@[simp] theorem atTime_every {f g : I → E → Prop} {t : I} :
    atTime Quantifier.Det.every f g t ↔ ∀ x, f t x → g t x :=
  Iff.rfl

@[simp] theorem atTime_some {f g : I → E → Prop} {t : I} :
    atTime Quantifier.Det.some f g t ↔ ∃ x, f t x ∧ g t x :=
  Iff.rfl

-- (31)–(33): *a dog* under its second meaning (32) and the copula, and Montague's quantificational
-- *a* with the *is* of identity, give the same truth conditions.
theorem fido_is_a_dog (R : I → I → Prop) (dog : I → E → Prop) (o : E) (t : I) :
    copula R (intersective dog) t o ↔
      ∃ t', R t' t ∧ atTime Quantifier.Det.some dog (fun _ y ↦ o = y) t' := by
  simp [copula_intersective]

/-- Under the copula a privative adjective holds of nothing, since it maps the trivial noun to a
property disjoint from it. *The president is former* (42), whose types work out, is a
contradiction on the meaning (44) of *former*, a semantic explanation §3.2 leaves open; and a
privative *fake* needs the index or the deleted noun of footnote 31 for *That fur is fake*. -/
theorem copula_eq_bot_of_isPrivative {G : Modifier (I → E → Prop)} (hG : IsPrivative G)
    (R : I → I → Prop) : copula R G = ⊥ := by
  funext t x
  simp [copula, hG.map_top]

-- (42)
theorem copula_former [LT I] (R : I → I → Prop) : copula R (former : Modifier (I → E → Prop)) = ⊥ :=
  copula_eq_bot_of_isPrivative former_isPrivative R

/-! ### Non-subsective adjectives -/

-- (44)–(46): *former* is `Modifier.former`, and both its positive and its negative condition are
-- asserted.
theorem john_was_a_former_judge [LT I] (judge : I → E → Prop) (j : E) (t : I) :
    copula (· < ·) (intersective (former judge)) t j ↔
      ∃ t' < t, (∃ t'' < t', judge t'' j) ∧ ¬ judge t' j := by
  rw [copula_intersective]
  exact Iff.rfl

-- §3.4: no property combined intersectively with a noun gives the meaning of *former*.
theorem intersective_ne_former [Preorder I] {t' t : I} (h : t' < t) [Nonempty E]
    (Q : I → E → Prop) : intersective Q ≠ former :=
  fun e ↦ former_not_isSubsective h
    (e ▸ intersective_isIntersective Q : IsIntersective former).isSubsective

/-! ### Relational adjectives -/

/-- *localᵢ* (54), `λf⟨e,it⟩.λx.λt.f(x)(t) & local(x)(σ(i))(t)`. The relatum `z` is the value of
the index under the assignment, so the adjective stays within the type rather than taking an
internal argument. -/
def localTo (near : I → E → E → Prop) (z : E) : Modifier (I → E → Prop) :=
  intersective fun t x ↦ near t x z

variable {S : Type*} (F : ArgumentStructure.ThematicFrame E S) (cul : S → I)

/-- A transitive verb such as *inspect* (8) or *enter* (56d),
`λR⟨i,it⟩.λx.λe.λt.P(e) & Theme(e)(x) & R(CUL(e))(t)`, where `CUL(e)` is the culmination of
`e`, the last time at which it obtains. -/
def transitive (P : S → Prop) (R : I → I → Prop) (x : E) (e : S) (t : I) : Prop :=
  P e ∧ F.theme x e ∧ R (cul e) t

/-- Little v (8), (56f), `λF⟨s,it⟩.λx.λt.∃e(F(e)(t) & Agent(e)(x))`. -/
def littleV (G : S → I → Prop) : I → E → Prop :=
  fun t x ↦ ∃ e, G e t ∧ F.agent x e

-- (14), (20)–(21)
theorem inverse_scope [LT I] (woman donkey : I → E → Prop) (inspection : S → Prop) (t : I) :
    atTime Quantifier.Det.some donkey (fun t x ↦ atTime Quantifier.Det.every woman
        (littleV F (transitive F cul inspection (· < ·) x)) t) t ↔
      ∃ x, donkey t x ∧ ∀ y, woman t y →
        ∃ e, inspection e ∧ F.theme x e ∧ cul e < t ∧ F.agent y e := by
  simp only [atTime_every, atTime_some, littleV, transitive, and_assoc]

-- (14), (22)–(23)
theorem surface_scope [LT I] (woman donkey : I → E → Prop) (inspection : S → Prop) (t : I) :
    atTime Quantifier.Det.every woman (fun t y ↦ atTime Quantifier.Det.some donkey
        (fun t x ↦ littleV F (transitive F cul inspection (· < ·) x) t y) t) t ↔
      ∀ y, woman t y → ∃ x, donkey t x ∧
        ∃ e, inspection e ∧ F.theme x e ∧ cul e < t ∧ F.agent y e := by
  simp only [atTime_every, atTime_some, littleV, transitive, and_assoc]

-- (55)–(58): *everyone* (56a) is *every* restricted to persons.
theorem everyone_entered_a_local_bar [LT I] (person bar : I → E → Prop)
    (near : I → E → E → Prop) (entering : S → Prop) (t : I) :
    atTime Quantifier.Det.every person (fun t x ↦ atTime Quantifier.Det.some (localTo near x bar)
        (fun t y ↦ littleV F (transitive F cul entering (· < ·) y) t x) t) t ↔
      ∀ x, person t x → ∃ y, bar t y ∧ near t y x ∧
        ∃ e, entering e ∧ F.theme y e ∧ cul e < t ∧ F.agent x e := by
  simp only [atTime_every, atTime_some, localTo, intersective_apply, Pi.inf_apply, inf_Prop_eq,
    littleV, transitive, and_assoc, and_left_comm (a := near t _ _)]

/-! ### Replies to criticisms -/

/-- *former*, the fragment's non-subsective adjective, and some intersective adjective give
different meanings in their two orders, as *presumpte* 'alleged' and *jove* 'young' do in *jove
presumpte assassí* (92a) and *presumpte jove assassí* (92b). An adjective commutes with every
intersective one just when it is intersective itself, so the difference is one of scope between
two functions of one type. -/
theorem exists_not_commute_former [Preorder I] {t' t : I} (h : t' < t) [Nonempty E] :
    ∃ Y, ¬ Function.Commute (former : Modifier (I → E → Prop)) (intersective Y) := by
  simpa [isIntersective_iff_forall_commute] using
    fun hi : IsIntersective (former : Modifier (I → E → Prop)) ↦
      former_not_isSubsective h hi.isSubsective

-- (92): an intersective adjective outside *former* is asserted, but inside it need not hold,
-- since *former* is not subsective.
theorem exists_former_intersective_not [Preorder I] {t' t : I} (h : t' < t) [Nonempty E] :
    ∃ (Y N : I → E → Prop) (s : I) (x : E), former (intersective Y N) s x ∧ ¬ Y s x := by
  by_contra hc
  refine former_not_isSubsective (E := E) h
    (isSubsective_iff_forall_map_inf_le.mpr fun Y N s x hs ↦ ?_)
  by_contra hY
  exact hc ⟨Y, N, s, x, hs, hY⟩

variable {D : Type*}

/-- A gradable adjective with a degree argument (100) denotes
`λd.λf⟨e,it⟩.λx.λt.f(x)(t) & tall(x)(t)(d)`, of type ⟨d,eiteit⟩. -/
def gradable (P : I → E → D → Prop) (d : D) : Modifier (I → E → Prop) :=
  intersective fun t x ↦ P t x d

/-- The positive morpheme, which goes back to [cresswell-1976], in the form (104),
`λG⟨d,et⟩.λx.∃d(d > standard(G) & G(d)(x))`, transposed to ⟨d,eiteit⟩ as §4.6 proposes. -/
def pos [LT D] (standard : (D → Modifier (I → E → Prop)) → D) (G : D → Modifier (I → E → Prop)) :
    Modifier (I → E → Prop) :=
  fun N t x ↦ ∃ d, standard G < d ∧ G d N t x

-- §4.6: with the positive morpheme a gradable adjective is intersective, of type ⟨eit,eit⟩.
theorem pos_gradable [LT D] (standard : (D → Modifier (I → E → Prop)) → D)
    (P : I → E → D → Prop) :
    pos standard (gradable P) =
      intersective fun t x ↦ ∃ d, standard (gradable P) < d ∧ P t x d := by
  funext N t x
  simp only [pos, gradable, intersective_apply, Pi.inf_apply, inf_Prop_eq, ← and_assoc,
    exists_and_right]

end Meanings

end Elbourne2026
