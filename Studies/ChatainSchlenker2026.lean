module

public import Linglib.Data.Examples.ChatainSchlenker2026
public import Linglib.Logic.Trivalent.Knowledge
public import Linglib.Logic.Trivalent.Part
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.PredicateAbstraction
public import Linglib.Semantics.Composition.Mode.Combine
public import Linglib.Semantics.Composition.Constituency
public import Mathlib.Data.PFun
public import Linglib.Semantics.Alternatives.WithAlternatives
public import Linglib.Semantics.Modification.Basic
public import Linglib.Data.Examples.Readers

/-!
# Chatain and Schlenker (2026): Local accommodation without covert operators

This file formalizes the argument that local accommodation is not the work of a covert node `A`,
Bochvar's assertion operator, but of Free Enrichment, which conjoins a contextual restriction `R`
in Strong Kleene with an elementary predicate. An operator whose meaning ignores context
accommodates at every argument of a λ-abstract or at none, so an elided clause would copy its
antecedent's choice. One enrichment can project at one argument and accommodate at another, and
can accommodate one of a trigger's two presuppositions while the other projects.

## Implementation notes

A trivalent predicate `P : E → W → Trivalent` is undefined where its presupposition fails. Free
Enrichment (62) is `Modifier.intersective` at `fun x w ↦ ofProp (R x w)`, written out below as
`ofProp (R x w) ⊓ P x w`. In the derivation of (26) *take out* is a function into a partial truth
value, a gap being an effect that the other words are applied through, and Free Enrichment is a
map on the lexicon, `if R d w then P w d else false`, which agrees with the Strong Kleene
conjunction because `R` is two-valued (`enrichment_eq_meetMiddle`); the composition rules (63)
are then functional application and abstraction. With partial truth values a type of their own,
`A` is a possible word meaning, a function from them to truth values: the case against it is the
parallelism of ellipsis, not its meaning.

The paper's truth values are three, 1, 0 and #. In the derivation a partial truth value stands
for them, undefined for #, and `Trivalent.ofPart` reads it back.

## TODO

* Intermediate accommodation (55), Homer's diagnostic (§4.2.1), and the constraint on Free
  Enrichment that (77) calls for (§5.2.2).

## References

* [chatain-schlenker-2026]
* [beaver-krahmer-2001]
* [bochvar-1938]
* [romoli-2011]
-/

@[expose] public section

namespace ChatainSchlenker2026

open Bilattice Trivalent

universe u

section StrongKleene

variable {E W : Type*}

/-! ### Operators and parallelism -/

/-- An operator applied pointwise that keeps defined values defined, such as `A`, negation or
their composite, either keeps the gap of every argument or fills the gap of every argument, so an
elided clause accommodates exactly when its antecedent does (Table 1). -/
theorem pointwise_projects_or_accommodates (f : Trivalent → Trivalent)
    (hf : ∀ a, a ≠ .undefined → f a ≠ .undefined) (P : E → W → Trivalent) :
    (∀ x, gapExt (f ∘ P x) = gapExt (P x)) ∨ ∀ x, gapExt (f ∘ P x) = ∅ := by
  rcases eq_or_ne (f .undefined) .undefined with h | h
  · exact .inl fun x ↦ gapExt_comp (fun a ↦ ⟨fun hfa ↦ by_contra fun ha ↦ hf a ha hfa,
      fun ha ↦ ha ▸ h⟩) (P x)
  · refine .inr fun x ↦ (isBivalent_iff_gapExt_eq_empty _).1 (isBivalent_comp (fun a ↦ ?_) (P x))
    rcases eq_or_ne a .undefined with rfl | ha
    · exact h
    · exact hf a ha

/-- Bochvar's `A` keeps defined values defined, so Table 1 applies to it: inserted in an elided
clause, it would have to be in the antecedent too ([beaver-krahmer-2001]'s floating `A`). -/
example (P : E → W → Trivalent) :
    (∀ x, gapExt ((fun a ↦ ofProp (a = .true)) ∘ P x) = gapExt (P x)) ∨
      ∀ x, gapExt ((fun a ↦ ofProp (a = .true)) ∘ P x) = ∅ :=
  pointwise_projects_or_accommodates _ (fun _ _ ↦ ofProp_ne_undefined) P

/-! ### Free Enrichment -/

/-- Free Enrichment (62) is intersective modification by the restriction. -/
example (R : E → W → Prop) [∀ x, DecidablePred (R x)] (P : E → W → Trivalent) :
    Modifier.intersective (fun x w ↦ ofProp (R x w)) P = fun x w ↦ ofProp (R x w) ⊓ P x w :=
  rfl

/-- An enrichment trivial at `Y` and entailing the presupposition at `X` lets the presupposition
project at `Y` and accommodates it at `X`, so the antecedent and the elided clause of (26) can
share one λ-abstract and differ ((66)–(70)) ((71)). -/
theorem enrichment_projects_and_accommodates (P : E → W → Trivalent) (R : E → W → Prop)
    [∀ x, DecidablePred (R x)] {X Y : E} (hY : ∀ w, R Y w) (hX : ∀ w, R X w → P X w ≠ .undefined) :
    gapExt (fun w ↦ ofProp (R Y w) ⊓ P Y w) = gapExt (P Y) ∧
      gapExt (fun w ↦ ofProp (R X w) ⊓ P X w) = ∅ := by
  simp only [gapExt_ofProp_inf]
  exact ⟨Set.inter_eq_right.2 fun w _ ↦ hY w,
    Set.eq_empty_of_forall_notMem fun w h ↦ hX w h.1 h.2⟩

/-- The antecedent is the shared λ-abstract at an alternative to the elided clause's focused
argument, so it lies in that clause's focus value and semantic parallelism holds ((71)). The
focus monad puts the arguments and the clause meanings in one universe. -/
example {E W : Type u} (P : E → W → Trivalent) (R : E → W → Prop)
    [∀ x, DecidablePred (R x)] (X Y : E) :
    (fun w ↦ (ofProp (R Y w) ⊓ P Y w)ᶜ) ∈
      ((fun x w ↦ (ofProp (R x w) ⊓ P x w)ᶜ) <$> WithAlternatives.focused X).alternatives := by
  rw [WithAlternatives.alternatives_map_focused]; exact ⟨Y, rfl⟩

/-- Enrichment by definedness is local accommodation by `A` (§5.2). -/
theorem enrichment_by_definedness (P : E → W → Trivalent) :
    (fun x w ↦ ofProp (P x w ≠ .undefined) ⊓ P x w) = fun x w ↦ ofProp (P x w = .true) :=
  funext fun _ ↦ funext fun _ ↦ ofProp_ne_undefined_inf_self _

-- (75)
theorem enrichment_eq_meetMiddle (R : Prop) [Decidable R] (a : Trivalent) :
    ofProp R ⊓ a = meetMiddle (ofProp R) a :=
  (meetMiddle_eq_inf_of_left_ne_undefined _ _ ofProp_ne_undefined).symm

/-! ### Partial accommodation -/

/-- Enriching a trigger that presupposes `S ∩ T` by `S` accommodates `S` and leaves the
conditional presupposition that `S` implies `T` (§5.2.1), while `A` above the trigger leaves no
presupposition at all ((35), `Trivalent.gapExt_ofProp`), as does the substrate's
accommodation of every trigger at once
(`Presupposition.Formula.isBivalent_middleKleene_accommodate`). -/
theorem partial_accommodation (S T : Set W) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    {f : W → Trivalent} (hf : IsBivalent f) :
    gapExt (fun w ↦ ofProp (w ∈ S) ⊓ transplication (ofProp (w ∈ S ∩ T)) (f w)) = S \ T := by
  ext w; by_cases hS : w ∈ S <;> by_cases hT : w ∈ T <;> simp [hS, hT, hf.ne_undefined]

/-- One of the two presuppositions of a double trigger, *notice* (36) or *return the book to the
library* (38). -/
inductive Slot where
  | first
  | second
  deriving DecidableEq

/-- The slot of each presupposition name the examples use. -/
def slots : List (String × Slot) :=
  [("alive", .first), ("possession", .first), ("unpopular", .second), ("ownership", .second)]

/-- The presupposition a slot picks out of a pair. -/
def Slot.set (S T : Set W) : Slot → Set W
  | .first => S
  | .second => T

instance {S T : Set W} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    (q : Slot) → DecidablePred (· ∈ Slot.set S T q)
  | .first => inferInstanceAs (DecidablePred (· ∈ S))
  | .second => inferInstanceAs (DecidablePred (· ∈ T))

/-- Each example accommodates one presupposition of its trigger and projects the other, so
enriching by the accommodated one leaves exactly the other's conditional gap ((34), (38),
(39)). -/
theorem partial_accommodation_rows (S T : Set W) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    {f : W → Trivalent} (hf : IsBivalent f) : ∀ row ∈ Examples.all,
    ∀ q ∈ row.parse? "accommodated" slots, ∀ r ∈ row.parse? "projected" slots,
      q ≠ r ∧ gapExt (fun w ↦ ofProp (w ∈ Slot.set S T q) ⊓
        transplication (ofProp (w ∈ S ∩ T)) (f w)) = Slot.set S T q \ Slot.set S T r := by
  have h : ∀ row ∈ Examples.all, ∀ q ∈ row.parse? "accommodated" slots,
      ∀ r ∈ row.parse? "projected" slots, q ≠ r := by decide +kernel
  refine fun row hrow q hq r hr ↦ ⟨h row hrow q hq r hr, ?_⟩
  cases q <;> cases r <;> first
    | exact absurd rfl (h row hrow _ hq _ hr)
    | exact partial_accommodation S T hf
    | simpa [Slot.set, Set.inter_comm] using partial_accommodation T S hf

/-! ### Projection and accommodation -/

/-- In a knowledge-monotone context `C`, the reading on which the presupposition projects entails
the reading on which it is accommodated locally (§4.1). -/
theorem projection_entails_accommodation {C : Trivalent → Trivalent}
    (hC : ∀ a b, a ≤ₖ b → C a ≤ₖ C b) {a : Trivalent}
    (h : C a = .true) : C (ofProp (a = .true)) = .true := by
  have := hC _ _ (kLE_ofProp_eq_true a)
  rw [h] at this
  rcases kLE_iff.1 this with h' | h'
  · exact absurd h' (by decide)
  · exact h'.symm

/-- Ann's sentence in (26) entails its locally accommodated reading. -/
example {a : Trivalent} (h : aᶜ = .true) : (ofProp (a = .true))ᶜ = .true :=
  projection_entails_accommodation (fun _ _ ↦ compl_kLE_compl) h

end StrongKleene

/-! ### Composition

The derivation of `Examples.ex_26`. -/

section Composition

open Interpreter PhraseStructure PhraseStructure.Tree

/-- The base sort of the derivation: the days. -/
inductive Atom
  | e
  deriving DecidableEq

/-- The domain of the base sort over days `D`. -/
abbrev Atom.Dom (D : Type) : Atom → Type
  | .e => D

/-- The words of (26): the days, negation, and *take the lab rat out of its cage*. -/
inductive Word (D : Type) where
  | day (d : D)
  | not
  | takeOut

/-- The words and traces of (26) by semantic type: a day, negation of a truth value, *take out*
a function from days to partial truth values, and a trace a day. -/
inductive Item (D : Type) : Ty Atom → Type
  | day (d : D) : Item D (.base .e)
  | not : Item D (.t ⇒ .t)
  | takeOut : Item D (.base .e ⇒ .comp .M .t)
  | trace (n : ℕ) : Item D (.base .e)

/-- The item a leaf is. -/
def items {D : Type} : Word D ⊕ ℕ → List (Σ a, Item D a)
  | .inl (.day d) => [⟨_, .day d⟩]
  | .inl .not => [⟨_, .not⟩]
  | .inl .takeOut => [⟨_, .takeOut⟩]
  | .inr n => [⟨_, .trace n⟩]

variable {D W : Type}

/-- The λ-abstract `[λ₁ [not [t₁ take-out]]]` that the antecedent and the elided clause share. -/
def vp : Tree Unit (Word D) := .binder 1 (.bin (.leaf .not) (.bin (.tr 1) (.leaf .takeOut)))

/-- The clause `[d vp]`, the antecedent of (26) at Monday and its elided clause at Wednesday. -/
def clause (d : D) : Tree Unit (Word D) := .bin (.leaf (.day d)) vp

variable (P : W → D →. Prop) (R : D → W → Prop) (w : W) (g : ℕ → D) (d : D)

open Classical in
/-- The lexicon of (26) at a world `w`, where *take out* is the partial predicate `P w` enriched
by `R` (62). -/
noncomputable def Item.val : {a : Ty Atom} → Item D a → (ℕ → D) → a.Dom (Atom.Dom D)
  | _, .day d => fun _ ↦ d
  | _, .not => fun _ p ↦ ¬ p
  | _, .takeOut => fun _ d ↦ if R d w then P w d else Part.some False
  | _, .trace n => fun i ↦ i n

/-- The meanings of a tree at a world, relative to an assignment of days to indices: by
functional application through effects, and abstraction over an index. -/
noncomputable def meanings (t : Tree Unit (Word D)) :
    List (Σ a : Ty Atom, (ℕ → D) → a.Dom (Atom.Dom D)) :=
  t.values ((effectDriven application).withAbstraction fun _ ↦ .base .e)
    (ManySorted.Language.withAbstraction.structure (Assignments.total (Atom.Dom D) fun _ ↦ .base
        .e))
    (Item.val P R w) items

open Classical in
-- (67): the clause has one meaning, a partial truth value at each assignment.
theorem meanings_clause : meanings P R w (clause d) =
    [⟨.comp .M .t, fun _ ↦ (if R d w then P w d else Part.some False).map Not⟩] :=
  rfl

open Classical in
/-- The three-valued readout of the clause's meaning is the Strong Kleene negation of the
enriched predicate, so the derivation and `enrichment_projects_and_accommodates` describe one
object ((67)). -/
theorem ofPart_clause :
    ofPart ((if R d w then P w d else Part.some False).map Not) =
      (ofProp (R d w) ⊓ ofPart (P w d))ᶜ := by
  rw [ofPart_map_not, ofPart_ite_some_false]

/-- A clause fails of its presupposition at an assignment when it has a meaning undefined
there. -/
def PresupFailure : Prop :=
  ∃ v, (⟨.comp .M .t, v⟩ : Σ a : Ty Atom, (ℕ → D) → a.Dom (Atom.Dom D)) ∈
    meanings P R w (clause d) ∧ ¬ (v g).Dom

/-- The clause fails exactly where the enrichment holds and the predicate is undefined ((68),
(70)). -/
theorem presupFailure_clause : PresupFailure P R w g d ↔ R d w ∧ ¬ (P w d).Dom := by
  classical
  simp only [PresupFailure, meanings_clause, List.mem_singleton, Sigma.mk.injEq, heq_eq_eq,
    true_and, exists_eq_left]
  by_cases h : R d w <;> simp [h]

/-- With an enrichment trivial at `Y` and entailing the presupposition at `X`, the clause shared
by the antecedent and the elided clause fails at `Y` exactly where the presupposition does and
never fails at `X` ((66)–(70)). -/
theorem clause_projects_and_accommodates {X Y : D} (hY : ∀ w, R Y w)
    (hX : ∀ w, R X w → (P w X).Dom) :
    (PresupFailure P R w g Y ↔ ¬ (P w Y).Dom) ∧ ¬ PresupFailure P R w g X := by
  simp only [presupFailure_clause]
  exact ⟨and_iff_right (hY w), fun h ↦ h.2 (hX w h.1)⟩

theorem presupFailure_clause_iff_mem_gapExt [DecidablePred (R d)] :
    PresupFailure P R w g d ↔ w ∈ gapExt fun w ↦ ofProp (R d w) ⊓ ofPart (P w d) := by
  rw [presupFailure_clause, gapExt_ofProp_inf, Set.mem_inter_iff, mem_gapExt,
    ofPart_eq_undefined_iff, Set.mem_ofPred_eq]

/-- `A` (7) maps the value 1 to 1 and the other two values to 0, so it is a function from partial
truth values to truth values, and a word of that type takes a partial truth value by functional
application: `A` is a possible word meaning, as the paper has it. -/
example : (typeDriven (application (B := Atom))).binary () (.comp .M .t ⇒ .t) (.comp .M .t) =
    [⟨.t, .fa⟩] :=
  rfl

end Composition

end ChatainSchlenker2026
