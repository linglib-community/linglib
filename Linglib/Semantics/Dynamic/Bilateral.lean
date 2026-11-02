module

public import Linglib.Semantics.Dynamic.State
public import Linglib.Semantics.Dynamic.Update

/-!
# Bilateral Update Semantics

This file defines Bilateral Update Semantics. A *bilateral denotation* pairs a positive update, the
state that survives asserting a sentence, with a negative update, the state that survives denying
it, over states of world–assignment pairs with partial assignments. Negation swaps the two, as in
Krahmer and Muskens's bilateral DRT, so [double negation is the identity](##BilateralDen.neg_neg).
Conjunction and disjunction compose the updates cell by cell along the strong Kleene tables, the
third value being the *unknown update*, the points that subsist in neither, and
[de Morgan's laws hold in both dimensions](##BilateralDen.neg_disj). An existential introduces its
referent by random assignment in its positive update; its negative update keeps the points that
subsist in the negative update of its scope and not in the positive one, so at a novel referent
[it is bivalent](##BilateralDen.unknownUpdate_exists_pred1).

## Implementation notes

A point subsists in a state when some point of the state extends it, which is Groenendijk, Stokhof
and Veltman's descent; Elliott, and Elliott and Sudo, gloss descent this way but define it by
inclusion of domains. The negative update of an existential is Elliott's. Elliott and Sudo's
compares worlds instead, and agrees with it at states whose points define no referent.

## References

* [elliott-2023]
* [elliott-sudo-2025]
* [krahmer-muskens-1995]
* [groenendijk-stokhof-veltman-1996]
-/

@[expose] public section

open DynamicSemantics

variable {W V E : Type*}

/-- A bilateral denotation: a positive update `s[φ]⁺`, the result of asserting a sentence, and a
negative update `s[φ]⁻`, the result of denying it. -/
@[ext] structure BilateralDen (W V E : Type*) where
  /-- The positive update. -/
  positive : CCP (Possibility W V (Flat E))
  /-- The negative update. -/
  negative : CCP (Possibility W V (Flat E))

namespace BilateralDen

variable {φ ψ : BilateralDen W V E} {s : Set (Possibility W V (Flat E))}
  {p : Possibility W V (Flat E)}

/-! ### Atomic sentences -/

/-- A worldly atom keeps the points where the proposition holds, positively, or fails,
negatively. -/
def atom (pred : W → Prop) : BilateralDen W V E where
  positive s := {p ∈ s | pred p.world}
  negative s := {p ∈ s | ¬ pred p.world}

/-- Unary predication at `t` keeps the points where `t` is defined and its value satisfies the
predicate, positively, or fails it, negatively: a point where `t` is undefined survives
neither. -/
def pred1 (P : E → W → Prop) (t : V) : BilateralDen W V E where
  positive s := {p ∈ s | ∃ e : E, p.assignment t = ↑e ∧ P e p.world}
  negative s := {p ∈ s | ∃ e : E, p.assignment t = ↑e ∧ ¬ P e p.world}

/-- Binary predication at `t₁` and `t₂`, defined where both are. -/
def pred2 (P : E → E → W → Prop) (t₁ t₂ : V) : BilateralDen W V E where
  positive s := {p ∈ s | ∃ e₁ : E, p.assignment t₁ = ↑e₁ ∧
    ∃ e₂ : E, p.assignment t₂ = ↑e₂ ∧ P e₁ e₂ p.world}
  negative s := {p ∈ s | ∃ e₁ : E, p.assignment t₁ = ↑e₁ ∧
    ∃ e₂ : E, p.assignment t₂ = ↑e₂ ∧ ¬ P e₁ e₂ p.world}

theorem positive_union_negative_atom (pred : W → Prop) (s : Set (Possibility W V (Flat E))) :
    (atom pred).positive s ∪ (atom pred).negative s = s := by
  ext p
  simp only [atom, Set.mem_union, Set.mem_ofPred_eq, ← and_or_left, em, and_true]

theorem negative_pred1 (P : E → W → Prop) (t : V) :
    (pred1 P t).negative = (pred1 (fun e w ↦ ¬ P e w) t).positive := rfl

variable {x : V}

theorem positive_pred1_of_novel (P : E → W → Prop) (hx : State.Novel s x) :
    (pred1 P x).positive s = ∅ :=
  Set.eq_empty_of_forall_notMem fun p ⟨hp, _, he, _⟩ ↦ Flat.coe_ne_bot (he.symm.trans (hx p hp))

theorem negative_pred1_of_novel (P : E → W → Prop) (hx : State.Novel s x) :
    (pred1 P x).negative s = ∅ :=
  positive_pred1_of_novel (fun e w ↦ ¬ P e w) hx

/-! ### Negation -/

/-- Negation swaps the positive and the negative update. -/
def neg (φ : BilateralDen W V E) : BilateralDen W V E where
  positive := φ.negative
  negative := φ.positive

@[inherit_doc] scoped prefix:max "~" => neg

/-- Double negation is the identity, definitionally. -/
@[simp] theorem neg_neg (φ : BilateralDen W V E) : ~~φ = φ := rfl

/-! ### The unknown update and assertability -/

/-- The *unknown* update `s[φ]?`: the points of `s` that subsist in neither update, the dynamic
counterpart of the third strong Kleene value. -/
def unknownUpdate (φ : BilateralDen W V E)
    (s : Set (Possibility W V (Flat E))) : Set (Possibility W V (Flat E)) :=
  {p ∈ s | p ∉ lowerClosure (φ.positive s) ∧ p ∉ lowerClosure (φ.negative s)}

/-- A sentence is *assertable* at `c` when its unknown update there is empty: every point of `c`
subsists in one of its updates. -/
def Assertable (φ : BilateralDen W V E) (c : Set (Possibility W V (Flat E))) : Prop :=
  φ.unknownUpdate c = ∅

theorem unknownUpdate_neg (φ : BilateralDen W V E) (s) :
    (~φ).unknownUpdate s = φ.unknownUpdate s := by
  ext p
  simp only [unknownUpdate, neg, Set.mem_ofPred_eq,
    and_comm (a := p ∉ lowerClosure (φ.negative s))]

theorem unknownUpdate_atom (pred : W → Prop) (s) :
    (atom pred (V := V) (E := E)).unknownUpdate s = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hp, hpos, hneg⟩ ↦ ?_
  by_cases h : pred p.world
  · exact hpos (subset_lowerClosure ⟨hp, h⟩)
  · exact hneg (subset_lowerClosure ⟨hp, h⟩)

theorem unknownUpdate_pred1_of_novel (P : E → W → Prop) (hx : State.Novel s x) :
    (pred1 P x).unknownUpdate s = s := by
  ext p
  simp [unknownUpdate, positive_pred1_of_novel P hx, negative_pred1_of_novel P hx]

/-! ### Connectives -/

/-- Conjunction: the positive update sequences the positive updates, the verifying strong Kleene
cell; the negative update is the union of the five falsifying cells, each a sequence of
updates. -/
def conj (φ ψ : BilateralDen W V E) : BilateralDen W V E where
  positive s := ψ.positive (φ.positive s)
  negative s :=
    ψ.positive (φ.negative s) ∪ ψ.negative (φ.negative s)
      ∪ ψ.unknownUpdate (φ.negative s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative (φ.unknownUpdate s)

@[inherit_doc] scoped infixl:65 " ⊙ " => conj

/-- Disjunction: the positive update is the union of the five verifying strong Kleene cells; the
negative update sequences the negative updates. The cell `ψ.positive (φ.negative s)` lets the
denial of a negated existential in the first disjunct introduce a referent for the second. -/
def disj (φ ψ : BilateralDen W V E) : BilateralDen W V E where
  positive s :=
    ψ.positive (φ.positive s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.unknownUpdate (φ.positive s) ∪ ψ.positive (φ.negative s)
      ∪ ψ.positive (φ.unknownUpdate s)
  negative s := ψ.negative (φ.negative s)

@[inherit_doc] scoped infixl:60 " ⊕ " => disj

/-- De Morgan: `¬(φ ∨ ψ)` is `¬φ ∧ ¬ψ`, in both dimensions. -/
theorem neg_disj (φ ψ : BilateralDen W V E) : ~(φ ⊕ ψ) = (~φ) ⊙ (~ψ) := by
  refine BilateralDen.ext rfl (funext fun s ↦ ?_)
  show ψ.positive (φ.positive s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.unknownUpdate (φ.positive s) ∪ ψ.positive (φ.negative s)
      ∪ ψ.positive (φ.unknownUpdate s)
    = ψ.negative (φ.positive s) ∪ ψ.positive (φ.positive s)
      ∪ (~ψ).unknownUpdate (φ.positive s) ∪ ψ.positive (φ.negative s)
      ∪ ψ.positive ((~φ).unknownUpdate s)
  rw [unknownUpdate_neg φ s, unknownUpdate_neg ψ (φ.positive s),
    Set.union_comm (ψ.negative (φ.positive s)) (ψ.positive (φ.positive s))]

/-- De Morgan: `¬(φ ∧ ψ)` is `¬φ ∨ ¬ψ`, in both dimensions. -/
theorem neg_conj (φ ψ : BilateralDen W V E) : ~(φ ⊙ ψ) = (~φ) ⊕ (~ψ) := by
  refine BilateralDen.ext (funext fun s ↦ ?_) rfl
  show ψ.positive (φ.negative s) ∪ ψ.negative (φ.negative s)
      ∪ ψ.unknownUpdate (φ.negative s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative (φ.unknownUpdate s)
    = ψ.negative (φ.negative s) ∪ ψ.positive (φ.negative s)
      ∪ (~ψ).unknownUpdate (φ.negative s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative ((~φ).unknownUpdate s)
  rw [unknownUpdate_neg φ s, unknownUpdate_neg ψ (φ.negative s),
    Set.union_comm (ψ.negative (φ.negative s)) (ψ.positive (φ.negative s))]

/-! ### Quantifiers -/

section Quantifiers
variable [DecidableEq V]

/-- Existential quantification: the positive update asserts the scope after random assignment at
`x`; the negative update keeps the points of `s` that subsist in the negative update of the scope
after random assignment and not in its positive update, so it introduces no referent. -/
def exists_ (x : V) (φ : BilateralDen W V E) : BilateralDen W V E where
  positive s := φ.positive (State.randomAssign s x)
  negative s := {p ∈ s | p ∉ lowerClosure (φ.positive (State.randomAssign s x)) ∧
    p ∈ lowerClosure (φ.negative (State.randomAssign s x))}

/-- Universal quantification, the dual `∀x φ = ¬∃x ¬φ`. -/
def forall_ (x : V) (φ : BilateralDen W V E) : BilateralDen W V E :=
  ~(exists_ x (~φ))

/-- Egli's positive equivalence, definitionally: `(∃x φ) ∧ ψ` and `∃x (φ ∧ ψ)` have the same
positive update, so an existential binds into a later conjunct. The negative updates differ in
general, since a denied existential introduces no referent and a denied conjunction can. -/
theorem egli (x : V) (φ ψ : BilateralDen W V E) (s) :
    ((exists_ x φ) ⊙ ψ).positive s = (exists_ x (φ ⊙ ψ)).positive s := rfl

theorem negative_exists_subset (x : V) (φ : BilateralDen W V E) (s) :
    (exists_ x φ).negative s ⊆ s :=
  Set.sep_subset _ _

/-- At a novel referent, a point subsists after random assignment and a predication iff its world
has a witness. -/
theorem mem_lowerClosure_positive_pred1_randomAssign (P : E → W → Prop) (hp : p ∈ s)
    (hx : State.Novel s x) :
    p ∈ lowerClosure ((pred1 P x).positive (State.randomAssign s x)) ↔ ∃ e, P e p.world := by
  constructor
  · rintro ⟨q, ⟨-, e, -, hP⟩, hpq⟩
    exact ⟨e, (Possibility.le_def.mp hpq).1 ▸ hP⟩
  · rintro ⟨e, hP⟩
    exact ⟨p.update x ↑e, ⟨⟨p, hp, e, rfl⟩, e, by simp, hP⟩,
      Possibility.le_update_of_eq_bot (hx p hp) _⟩

/-- At a novel referent, the denial of `∃x P(x)` keeps the points whose world has no `P`. -/
theorem negative_exists_pred1 [Nonempty E] (P : E → W → Prop) (hx : State.Novel s x) :
    (exists_ x (pred1 P x)).negative s = {p ∈ s | ∀ e, ¬ P e p.world} := by
  ext p
  refine ⟨fun ⟨hp, hpos, _⟩ ↦ ⟨hp, fun e he ↦
    hpos ((mem_lowerClosure_positive_pred1_randomAssign P hp hx).2 ⟨e, he⟩)⟩,
    fun ⟨hp, h⟩ ↦ ⟨hp, fun hpos ↦ ?_, ?_⟩⟩
  · obtain ⟨e, he⟩ := (mem_lowerClosure_positive_pred1_randomAssign P hp hx).1 hpos
    exact h e he
  · obtain ⟨e⟩ := ‹Nonempty E›
    exact (mem_lowerClosure_positive_pred1_randomAssign (fun e w ↦ ¬ P e w) hp hx).2 ⟨e, h e⟩

/-- At a novel referent, `∃x P(x)` is bivalent: every point subsists in one of its updates. -/
theorem unknownUpdate_exists_pred1 [Nonempty E] (P : E → W → Prop) (hx : State.Novel s x) :
    (exists_ x (pred1 P x)).unknownUpdate s = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hp, hpos, hneg⟩ ↦ hneg (subset_lowerClosure ?_)
  rw [negative_exists_pred1 P hx]
  exact ⟨hp, fun e he ↦ hpos ((mem_lowerClosure_positive_pred1_randomAssign P hp hx).2 ⟨e, he⟩)⟩

end Quantifiers

end BilateralDen
