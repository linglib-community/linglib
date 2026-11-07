module

public import Linglib.Data.Examples.Elbourne2026
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.ArgumentStructure.ThematicRole
public import Linglib.Semantics.Composition.Mode
public import Linglib.Semantics.Modification.Classification
public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Powerset

/-!
# Elbourne (2026): Adjectives without syntactic categories

Elbourne replaces syntactic categories by semantic types in a grammar that composes by functional
application alone, and gives every adjective the type ⟨eit,eit⟩ of a function on noun meanings.
[Nothing that takes a noun merges with an adjective](##not_merges_of_takes_noun), which excludes
*Every red is attractive*, while [a copula takes just the adjectives without compulsory
features](##merges_copula_iff), which excludes *The president is former*. The copula applies the
adjective to the trivial noun, where [a privative adjective is a
contradiction](##copula_eq_bot_of_isPrivative), and [two adjectives commute just when the outer
one is intersective](##comp_intersective_comm_iff), a difference of scope rather than of type.

## Implementation notes

* The types are `Montague.Ty` over a type `i` of time intervals left as a variable, entity first
  as printed. The meanings are `Modifier (I → E → Prop)`, times first as in the substrate's
  `Modifier.former`, with conjuncts reordered, so that the second meaning (32) of *a* is
  `Modifier.intersective`.
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

open Montague Modifier Elbourne2026.Examples

/-! ### Types and selector features -/

/-- The type ⟨e,it⟩ of nouns, where `i` is the type of time intervals. -/
def eit (i : Ty) : Ty := .e ⇒ i ⇒ .t

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
def cute : Features := ⟨∅, {Selector.eR}⟩

/-- *former* and *mere* (§3.2) have a compulsory `E_R`. -/
def former : Features := ⟨{Selector.eR}, ∅⟩

/-- Russian short-form adjectives (§4.2) have no selector features. -/
def shortForm : Features := ⟨∅, ∅⟩

/-- Russian long-form adjectives (§4.2) have optional `E_R` and `E_L`. -/
def longForm : Features := ⟨∅, {Selector.eR, Selector.eL}⟩

end Features

section Merge

variable (i : Ty)

/-- An adjective with features `f` merges with a sister of type `σ` when Functional Application
(9) applies with the left daughter, the bearer of `E_R` (4a), as the function: either the
adjective takes the sister as its noun by `E_R`, or the sister takes the adjective, which by
Argument Interpretability (6) then carries no feature. -/
def Merges (f : Features) (σ : Ty) : Prop :=
  (Mode.functionalLeft? (eit i ⇒ eit i) σ).isSome ∧ f.TakesNoun ∨
    (Mode.functionalLeft? σ (eit i ⇒ eit i)).isSome ∧ f.Selectable

variable {i} {f : Features}

-- §3.1: an adjective takes a noun in attributive position by its `E_R`.
theorem merges_noun_iff : Merges i f (eit i) ↔ Selector.eR ∈ f.compulsory ∪ f.optional := by
  simp [Merges, Mode.functionalLeft?, eit, Features.takesNoun_iff]

/-- Whatever takes an adjective as its argument, such as the copula with its tense, of type
⟨⟨eit,eit⟩,eit⟩, takes just the adjectives without compulsory features. The types work out for
*The president is former* (42), and the compulsory `E_R` of *former* excludes it. -/
theorem merges_copula_iff (ρ : Ty) : Merges i f ((eit i ⇒ eit i) ⇒ ρ) ↔ f.compulsory = ∅ := by
  simp [Merges, Mode.functionalLeft?, eit, Features.selectable_iff]

/-- Nothing that takes a noun merges with an adjective in either role, neither a determiner, of
type ⟨eit,⟨eit,it⟩⟩, nor the second meaning (32) of *a*, of type ⟨eit,⟨eit,eit⟩⟩. This excludes
*Joe is a former* (36) and *Every red is attractive* (37) by type alone. -/
theorem not_merges_of_takes_noun (ρ : Ty) : ¬ Merges i f (eit i ⇒ ρ) := by
  simp [Merges, Mode.functionalLeft?, eit]

variable (i)

/-- The rows on the positions of adjectives, each with its adjective's features and the type of
the sister it merges with: the copula with its tense, a determiner, or a noun. -/
def distribution : List (Datum × Features × Ty) :=
  [(ex_28, .cute, (eit i ⇒ eit i) ⇒ eit i), (ex_36, .former, eit i ⇒ eit i ⇒ i ⇒ .t),
    (ex_37, .cute, eit i ⇒ eit i ⇒ i ⇒ .t), (ex_42, .former, (eit i ⇒ eit i) ⇒ eit i),
    (ex_45, .former, eit i), (ex_64_long, .longForm, (eit i ⇒ eit i) ⇒ eit i),
    (ex_64_short, .shortForm, (eit i ⇒ eit i) ⇒ eit i), (ex_65a, .longForm, eit i),
    (ex_65b, .shortForm, eit i)]

theorem rows_merge : ∀ r ∈ distribution i, (r.1.judgment = .acceptable ↔ Merges i r.2.1 r.2.2) := by
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

-- (31)–(33): *a dog* under its second meaning (32) and the copula, and Montague's quantificational
-- *a* with the *is* of identity, give the same truth conditions.
theorem fido_is_a_dog (R : I → I → Prop) (dog : I → E → Prop) (o : E) (t : I) :
    copula R (intersective dog) t o ↔
      ∃ t', R t' t ∧ atTime Quantifier.Det.some dog (fun _ y ↦ o = y) t' := by
  simp [copula_intersective, atTime, Quantifier.Det.some, Set.Nonempty]

/-- Under the copula a privative adjective holds of nothing, since it maps the trivial noun to a
property disjoint from it. *The president is former* (42), whose types work out, is a
contradiction on the meaning (44) of *former*, a semantic explanation §3.2 leaves open; and a
privative *fake* needs the index or the deleted noun of footnote 31 for *That fur is fake*. -/
theorem copula_eq_bot_of_isPrivative {G : Modifier (I → E → Prop)} (hG : IsPrivative G)
    (R : I → I → Prop) : copula R G = ⊥ := by
  have h : G ⊤ = ⊥ := disjoint_top.mp (hG ⊤)
  funext t x
  simp [copula, h]

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
  simp only [atTime, Quantifier.Det.some, Quantifier.Det.every, Set.Nonempty, Set.subset_def,
    Set.mem_inter_iff, Set.mem_ofPred_eq, littleV, transitive, and_assoc]

-- (14), (22)–(23)
theorem surface_scope [LT I] (woman donkey : I → E → Prop) (inspection : S → Prop) (t : I) :
    atTime Quantifier.Det.every woman (fun t y ↦ atTime Quantifier.Det.some donkey
        (fun t x ↦ littleV F (transitive F cul inspection (· < ·) x) t y) t) t ↔
      ∀ y, woman t y → ∃ x, donkey t x ∧
        ∃ e, inspection e ∧ F.theme x e ∧ cul e < t ∧ F.agent y e := by
  simp only [atTime, Quantifier.Det.some, Quantifier.Det.every, Set.Nonempty, Set.subset_def,
    Set.mem_inter_iff, Set.mem_ofPred_eq, littleV, transitive, and_assoc]

-- (55)–(58): *everyone* (56a) is *every* restricted to persons.
theorem everyone_entered_a_local_bar [LT I] (person bar : I → E → Prop)
    (near : I → E → E → Prop) (entering : S → Prop) (t : I) :
    atTime Quantifier.Det.every person (fun t x ↦ atTime Quantifier.Det.some (localTo near x bar)
        (fun t y ↦ littleV F (transitive F cul entering (· < ·) y) t x) t) t ↔
      ∀ x, person t x → ∃ y, bar t y ∧ near t y x ∧
        ∃ e, entering e ∧ F.theme y e ∧ cul e < t ∧ F.agent x e := by
  simp only [atTime, Quantifier.Det.some, Quantifier.Det.every, Set.Nonempty, Set.subset_def,
    Set.mem_inter_iff, Set.mem_ofPred_eq, localTo, intersective_apply₂, littleV, transitive,
    and_assoc, and_left_comm (a := near t _ _)]

/-! ### Replies to criticisms -/

/-- Two adjectives give the same meaning in either order, for every noun, exactly when the outer
one is intersective. This is McNally and Boleda's observation on *jove presumpte assassí* 'young
alleged murderer' (92a) and *presumpte jove assassí* (92b), and makes their difference one of
scope between two functions of one type. -/
theorem comp_intersective_comm_iff {M : Modifier (I → E → Prop)} :
    (∀ Y, M ∘ intersective Y = intersective Y ∘ M) ↔ IsIntersective M := by
  rw [isIntersective_iff_map_inf]
  refine ⟨fun h N Y ↦ ?_, fun h Y ↦ funext fun N ↦ ?_⟩
  · rw [inf_comm N, inf_comm (M N)]
    exact congrFun (h Y) N
  · change M (Y ⊓ N) = Y ⊓ M N
    rw [inf_comm Y N, inf_comm Y (M N)]
    exact h N Y

-- (92): an intersective *jove* commits the speaker to youth when it is outermost; innermost it
-- does so under an outer adjective, for every noun, exactly when that adjective is subsective,
-- which *presumpte* 'alleged' is not.
theorem forall_map_intersective_le_iff {M : Modifier (I → E → Prop)} :
    (∀ Y N, M (intersective Y N) ≤ Y) ↔ IsSubsective M :=
  ⟨fun h N ↦ by simpa [intersective] using h N N, fun h _ _ ↦ (h _).trans inf_le_left⟩

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
  simp only [pos, gradable, intersective_apply₂]
  exact propext ⟨fun ⟨d, hd, h, hN⟩ ↦ ⟨⟨d, hd, h⟩, hN⟩, fun ⟨⟨d, hd, h⟩, hN⟩ ↦ ⟨d, hd, h, hN⟩⟩

end Meanings

end Elbourne2026
