module

public import Linglib.Core.Basic.Sign
public import Linglib.Logic.Trivalent.Basic
public import Linglib.Semantics.Dynamic.State
public import Linglib.Semantics.Dynamic.Update

/-!
# Bilateral Update Semantics

This file defines Bilateral Update Semantics. A *bilateral update* pairs a positive update, the
state that survives asserting a sentence, with a negative update, the state that survives denying
it, over states of world–assignment pairs with partial assignments; the *unknown update* keeps the
points that subsist in neither, so a sentence updates a state at each of the three truth values.
Negation swaps the positive and negative updates, as in Krahmer and Muskens's bilateral DRT, so
[it negates the truth value](##DynamicSemantics.BilateralUpdate.update_neg). A binary truth
function [lifts](##DynamicSemantics.BilateralUpdate.lift) to the union, over the cells of its
table, of the updates by the two operands in turn; conjunction and disjunction lift the strong
Kleene tables, so [de Morgan's laws hold](##DynamicSemantics.BilateralUpdate.neg_disj). Atomic
sentences are the static updates of trivalent propositions over points.

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

namespace DynamicSemantics

variable {W V E : Type*}

/-- A bilateral update: a positive update `s[φ]⁺`, the result of asserting a sentence, and a
negative update `s[φ]⁻`, the result of denying it. -/
@[ext] structure BilateralUpdate (W V E : Type*) where
  /-- The positive update. -/
  positive : CCP (Possibility W V (Flat E))
  /-- The negative update. -/
  negative : CCP (Possibility W V (Flat E))

namespace BilateralUpdate

variable {φ ψ : BilateralUpdate W V E} {s : Set (Possibility W V (Flat E))}
  {p : Possibility W V (Flat E)}

/-! ### Negation and the unknown update -/

/-- Negation swaps the positive and the negative update. -/
def neg (φ : BilateralUpdate W V E) : BilateralUpdate W V E where
  positive := φ.negative
  negative := φ.positive

@[inherit_doc] scoped prefix:max "~" => neg

@[simp] theorem positive_neg (φ : BilateralUpdate W V E) : (~φ).positive = φ.negative := rfl
@[simp] theorem negative_neg (φ : BilateralUpdate W V E) : (~φ).negative = φ.positive := rfl

/-- Double negation is the identity, definitionally. -/
@[simp] theorem neg_neg (φ : BilateralUpdate W V E) : ~~φ = φ := rfl

/-- The *unknown* update `s[φ]?`: the points of `s` that subsist in neither update. -/
def unknownUpdate (φ : BilateralUpdate W V E)
    (s : Set (Possibility W V (Flat E))) : Set (Possibility W V (Flat E)) :=
  {p ∈ s | p ∉ lowerClosure (φ.positive s) ∧ p ∉ lowerClosure (φ.negative s)}

/-- A sentence is *assertable* at `c` when its unknown update there is empty: every point of `c`
subsists in one of its updates. -/
def Assertable (φ : BilateralUpdate W V E) (c : Set (Possibility W V (Flat E))) : Prop :=
  φ.unknownUpdate c = ∅

theorem unknownUpdate_neg (φ : BilateralUpdate W V E) (s) :
    (~φ).unknownUpdate s = φ.unknownUpdate s := by
  ext p
  simp only [unknownUpdate, neg, Set.mem_ofPred_eq,
    and_comm (a := p ∉ lowerClosure (φ.negative s))]

/-- The update at a truth value: positive at `1`, negative at `-1` and unknown at `0`. -/
def update (φ : BilateralUpdate W V E) : SignType → CCP (Possibility W V (Flat E))
  | .pos => φ.positive
  | .neg => φ.negative
  | .zero => φ.unknownUpdate

@[simp] theorem update_one (φ : BilateralUpdate W V E) : φ.update 1 = φ.positive := rfl
@[simp] theorem update_neg_one (φ : BilateralUpdate W V E) : φ.update (-1) = φ.negative := rfl
@[simp] theorem update_zero (φ : BilateralUpdate W V E) : φ.update 0 = φ.unknownUpdate := rfl

/-- Negation negates the truth value at which a sentence updates. -/
theorem update_neg (φ : BilateralUpdate W V E) (a : SignType) : (~φ).update a = φ.update (-a) := by
  cases a
  exacts [funext (unknownUpdate_neg φ), rfl, rfl]

/-! ### Static updates -/

/-- The static update of a trivalent proposition over points: it keeps the points where the
proposition is true, positively, and where it is false, negatively. -/
def ofTrivalent (v : Possibility W V (Flat E) → SignType) : BilateralUpdate W V E where
  positive := CCP.up (posSupport v)
  negative := CCP.up (negSupport v)

variable {v : Possibility W V (Flat E) → SignType}

@[simp] theorem mem_positive_ofTrivalent : p ∈ (ofTrivalent v).positive s ↔ p ∈ s ∧ v p = 1 :=
  Iff.rfl

@[simp] theorem mem_negative_ofTrivalent : p ∈ (ofTrivalent v).negative s ↔ p ∈ s ∧ v p = -1 :=
  Iff.rfl

theorem positive_ofTrivalent_of_eq_zero (h : ∀ p ∈ s, v p = 0) : (ofTrivalent v).positive s = ∅ :=
  Set.eq_empty_of_forall_notMem fun p ⟨hp, h1⟩ ↦ by simp [h p hp] at h1

theorem negative_ofTrivalent_of_eq_zero (h : ∀ p ∈ s, v p = 0) : (ofTrivalent v).negative s = ∅ :=
  Set.eq_empty_of_forall_notMem fun p ⟨hp, h1⟩ ↦ by simp [h p hp] at h1

/-- Where a trivalent proposition is undefined throughout, every point is unknown. -/
theorem unknownUpdate_ofTrivalent_of_eq_zero (h : ∀ p ∈ s, v p = 0) :
    (ofTrivalent v).unknownUpdate s = s := by
  ext p
  simp [unknownUpdate, positive_ofTrivalent_of_eq_zero h, negative_ofTrivalent_of_eq_zero h]

/-- Where a trivalent proposition is defined throughout, no point is unknown. -/
theorem unknownUpdate_ofTrivalent_of_ne_zero (h : ∀ p ∈ s, v p ≠ 0) :
    (ofTrivalent v).unknownUpdate s = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hp, hpos, hneg⟩ ↦ ?_
  match hv : v p with
  | .pos => exact hpos (subset_lowerClosure ⟨hp, hv⟩)
  | .neg => exact hneg (subset_lowerClosure ⟨hp, hv⟩)
  | .zero => exact h p hp hv

open scoped Classical in
/-- A worldly atom: the proposition at the world of a point. -/
noncomputable def atom (pred : W → Prop) : BilateralUpdate W V E :=
  ofTrivalent fun p ↦ SignType.ofProp (pred p.world)

open scoped Classical in
/-- Unary predication at `t`: undefined where `t` is, and otherwise the predicate at its value. -/
noncomputable def pred1 (P : E → W → Prop) (t : V) : BilateralUpdate W V E :=
  ofTrivalent fun p ↦ Flat.recBotCoe (C := fun _ ↦ SignType) 0
    (fun e ↦ SignType.ofProp (P e p.world)) (p.assignment t)

open scoped Classical in
/-- Binary predication at `t₁` and `t₂`: undefined where either is. -/
noncomputable def pred2 (P : E → E → W → Prop) (t₁ t₂ : V) : BilateralUpdate W V E :=
  ofTrivalent fun p ↦ Flat.recBotCoe (C := fun _ ↦ SignType) 0 (fun e₁ ↦
    Flat.recBotCoe (C := fun _ ↦ SignType) 0 (fun e₂ ↦ SignType.ofProp (P e₁ e₂ p.world))
      (p.assignment t₂)) (p.assignment t₁)

@[simp] theorem mem_positive_atom {pred : W → Prop} :
    p ∈ (atom pred).positive s ↔ p ∈ s ∧ pred p.world := by
  simp [atom]

@[simp] theorem mem_negative_atom {pred : W → Prop} :
    p ∈ (atom pred).negative s ↔ p ∈ s ∧ ¬ pred p.world := by
  simp [atom]

@[simp] theorem mem_positive_pred1 {P : E → W → Prop} {t : V} :
    p ∈ (pred1 P t).positive s ↔ p ∈ s ∧ ∃ e : E, p.assignment t = ↑e ∧ P e p.world := by
  simp only [pred1, mem_positive_ofTrivalent]
  refine and_congr_right fun _ ↦ ?_
  induction p.assignment t using Flat.recBotCoe <;> simp

@[simp] theorem mem_negative_pred1 {P : E → W → Prop} {t : V} :
    p ∈ (pred1 P t).negative s ↔ p ∈ s ∧ ∃ e : E, p.assignment t = ↑e ∧ ¬ P e p.world := by
  simp only [pred1, mem_negative_ofTrivalent]
  refine and_congr_right fun _ ↦ ?_
  induction p.assignment t using Flat.recBotCoe <;> simp

@[simp] theorem mem_positive_pred2 {P : E → E → W → Prop} {t₁ t₂ : V} :
    p ∈ (pred2 P t₁ t₂).positive s ↔ p ∈ s ∧ ∃ e₁ : E, p.assignment t₁ = ↑e₁ ∧
      ∃ e₂ : E, p.assignment t₂ = ↑e₂ ∧ P e₁ e₂ p.world := by
  simp only [pred2, mem_positive_ofTrivalent]
  refine and_congr_right fun _ ↦ ?_
  induction p.assignment t₁ using Flat.recBotCoe <;>
    induction p.assignment t₂ using Flat.recBotCoe <;> simp

@[simp] theorem mem_negative_pred2 {P : E → E → W → Prop} {t₁ t₂ : V} :
    p ∈ (pred2 P t₁ t₂).negative s ↔ p ∈ s ∧ ∃ e₁ : E, p.assignment t₁ = ↑e₁ ∧
      ∃ e₂ : E, p.assignment t₂ = ↑e₂ ∧ ¬ P e₁ e₂ p.world := by
  simp only [pred2, mem_negative_ofTrivalent]
  refine and_congr_right fun _ ↦ ?_
  induction p.assignment t₁ using Flat.recBotCoe <;>
    induction p.assignment t₂ using Flat.recBotCoe <;> simp

theorem negative_atom (pred : W → Prop) (s : Set (Possibility W V (Flat E))) :
    (atom pred (V := V) (E := E)).negative s = {p ∈ s | ¬ pred p.world} :=
  Set.ext fun _ ↦ mem_negative_atom

theorem unknownUpdate_atom (pred : W → Prop) (s) :
    (atom pred (V := V) (E := E)).unknownUpdate s = ∅ :=
  unknownUpdate_ofTrivalent_of_ne_zero fun _ _ ↦ by simp

theorem neg_pred1 (P : E → W → Prop) (t : V) :
    ~(pred1 P t) = pred1 (fun e w ↦ ¬ P e w) t := by
  ext s p <;> simp

theorem negative_pred1 (P : E → W → Prop) (t : V) :
    (pred1 P t).negative = (pred1 (fun e w ↦ ¬ P e w) t).positive := by
  rw [← neg_pred1, positive_neg]

theorem negative_pred2 (P : E → E → W → Prop) (t₁ t₂ : V) :
    (pred2 P t₁ t₂).negative = (pred2 (fun a b w ↦ ¬ P a b w) t₁ t₂).positive := by
  ext s p
  simp

variable {x : V}

theorem positive_pred1_of_novel (P : E → W → Prop) (hx : State.Novel s x) :
    (pred1 P x).positive s = ∅ :=
  positive_ofTrivalent_of_eq_zero fun p hp ↦ by simp [hx p hp]

theorem negative_pred1_of_novel (P : E → W → Prop) (hx : State.Novel s x) :
    (pred1 P x).negative s = ∅ :=
  negative_ofTrivalent_of_eq_zero fun p hp ↦ by simp [hx p hp]

theorem unknownUpdate_pred1_of_novel (P : E → W → Prop) (hx : State.Novel s x) :
    (pred1 P x).unknownUpdate s = s :=
  unknownUpdate_ofTrivalent_of_eq_zero fun p hp ↦ by simp [hx p hp]

/-! ### Connectives -/

/-- The lift of a binary truth function `f`: at `1` and `-1`, the union over the cells of the table
with that value of the update by `φ` at the row's value followed by `ψ` at the column's. -/
def lift (f : SignType → SignType → SignType) (φ ψ : BilateralUpdate W V E) :
    BilateralUpdate W V E where
  positive s := ⋃ (a) (b) (_ : f a b = 1), ψ.update b (φ.update a s)
  negative s := ⋃ (a) (b) (_ : f a b = -1), ψ.update b (φ.update a s)

variable {f : SignType → SignType → SignType}

@[simp] theorem mem_positive_lift :
    p ∈ (lift f φ ψ).positive s ↔ ∃ a b, f a b = 1 ∧ p ∈ ψ.update b (φ.update a s) := by
  simp [lift]

@[simp] theorem mem_negative_lift :
    p ∈ (lift f φ ψ).negative s ↔ ∃ a b, f a b = -1 ∧ p ∈ ψ.update b (φ.update a s) := by
  simp [lift]

/-- Negating a lift lifts the dual truth function to the negated operands. -/
theorem neg_lift (f : SignType → SignType → SignType) (φ ψ : BilateralUpdate W V E) :
    ~(lift f φ ψ) = lift (fun a b ↦ -f (-a) (-b)) (~φ) (~ψ) := by
  have key (c : SignType) (p) (s) : (∃ a b, f a b = c ∧ p ∈ ψ.update b (φ.update a s)) ↔
      ∃ a b, -f (-a) (-b) = -c ∧ p ∈ (~ψ).update b ((~φ).update a s) := by
    simp only [update_neg, neg_inj]
    exact ⟨fun ⟨a, b, h, hp⟩ ↦ ⟨-a, -b, by simpa using h, by simpa using hp⟩,
      fun ⟨a, b, h, hp⟩ ↦ ⟨-a, -b, h, hp⟩⟩
  ext s p
  · change p ∈ (lift f φ ψ).negative s ↔ _
    rw [mem_negative_lift, mem_positive_lift, key (-1)]
    simp
  · change p ∈ (lift f φ ψ).positive s ↔ _
    rw [mem_positive_lift, mem_negative_lift, key 1]

/-- Conjunction lifts strong Kleene conjunction. -/
def conj (φ ψ : BilateralUpdate W V E) : BilateralUpdate W V E := lift (· ⊓ ·) φ ψ

@[inherit_doc] scoped infixl:65 " ⊙ " => conj

/-- Disjunction lifts strong Kleene disjunction. -/
def disj (φ ψ : BilateralUpdate W V E) : BilateralUpdate W V E := lift (· ⊔ ·) φ ψ

@[inherit_doc] scoped infixl:60 " ⊕ " => disj

/-- Conjunction is verified only by verifying both conjuncts in turn. -/
@[simp] theorem positive_conj : (φ ⊙ ψ).positive s = ψ.positive (φ.positive s) := by
  ext p
  simp [conj]

/-- Disjunction is falsified only by falsifying both disjuncts in turn. -/
@[simp] theorem negative_disj : (φ ⊕ ψ).negative s = ψ.negative (φ.negative s) := by
  ext p
  simp [disj]

/-- De Morgan: `¬(φ ∨ ψ)` is `¬φ ∧ ¬ψ`, in both dimensions. -/
theorem neg_disj (φ ψ : BilateralUpdate W V E) : ~(φ ⊕ ψ) = (~φ) ⊙ (~ψ) := by
  rw [disj, neg_lift]
  simp only [SignType.neg_sup, _root_.neg_neg]
  rfl

/-- De Morgan: `¬(φ ∧ ψ)` is `¬φ ∨ ¬ψ`, in both dimensions. -/
theorem neg_conj (φ ψ : BilateralUpdate W V E) : ~(φ ⊙ ψ) = (~φ) ⊕ (~ψ) := by
  rw [conj, neg_lift]
  simp only [SignType.neg_inf, _root_.neg_neg]
  rfl

/-! ### Responsibility -/

/-- The part of a compound's update at `v` that its first operand is responsible for: the cells
where the first operand has value `v`. -/
def firstPart (v : SignType) (φ ψ : BilateralUpdate W V E) (s : Set (Possibility W V (Flat E))) :
    Set (Possibility W V (Flat E)) :=
  ⋃ b, ψ.update b (φ.update v s)

/-- The part of a compound's update at `v` that its second operand is responsible for: the cells
where the second operand has value `v`. -/
def secondPart (v : SignType) (φ ψ : BilateralUpdate W V E) (s : Set (Possibility W V (Flat E))) :
    Set (Possibility W V (Flat E)) :=
  ⋃ a, ψ.update v (φ.update a s)

@[simp] theorem mem_firstPart {v : SignType} :
    p ∈ firstPart v φ ψ s ↔ ∃ b, p ∈ ψ.update b (φ.update v s) :=
  Set.mem_iUnion

@[simp] theorem mem_secondPart {v : SignType} :
    p ∈ secondPart v φ ψ s ↔ ∃ a, p ∈ ψ.update v (φ.update a s) :=
  Set.mem_iUnion

/-- A disjunction is verified by its first or its second disjunct. -/
theorem positive_disj_eq_union : (φ ⊕ ψ).positive s = firstPart 1 φ ψ s ∪ secondPart 1 φ ψ s := by
  ext p
  simp only [disj, mem_positive_lift, SignType.sup_eq_one_iff, Set.mem_union, mem_firstPart,
    mem_secondPart]
  constructor
  · rintro ⟨a, b, h | h, hp⟩ <;> subst h
    exacts [.inl ⟨b, hp⟩, .inr ⟨a, hp⟩]
  · rintro (⟨b, hp⟩ | ⟨a, hp⟩)
    exacts [⟨1, b, .inl rfl, hp⟩, ⟨a, 1, .inr rfl, hp⟩]

theorem firstPart_neg (v : SignType) (φ ψ : BilateralUpdate W V E) (s) :
    firstPart v (~φ) (~ψ) s = firstPart (-v) φ ψ s := by
  ext p
  simp only [mem_firstPart, update_neg]
  exact ⟨fun ⟨b, hp⟩ ↦ ⟨-b, hp⟩, fun ⟨b, hp⟩ ↦ ⟨-b, by simpa using hp⟩⟩

theorem secondPart_neg (v : SignType) (φ ψ : BilateralUpdate W V E) (s) :
    secondPart v (~φ) (~ψ) s = secondPart (-v) φ ψ s := by
  ext p
  simp only [mem_secondPart, update_neg]
  exact ⟨fun ⟨a, hp⟩ ↦ ⟨-a, hp⟩, fun ⟨a, hp⟩ ↦ ⟨-a, by simpa using hp⟩⟩

/-! ### Quantifiers -/

section Quantifiers
variable [DecidableEq V]

/-- Existential quantification: the positive update asserts the scope after random assignment at
`x`; the negative update keeps the points of `s` that subsist in the negative update of the scope
after random assignment and not in its positive update, so it introduces no referent. -/
def exists_ (x : V) (φ : BilateralUpdate W V E) : BilateralUpdate W V E where
  positive s := φ.positive (State.randomAssign s x)
  negative s := {p ∈ s | p ∉ lowerClosure (φ.positive (State.randomAssign s x)) ∧
    p ∈ lowerClosure (φ.negative (State.randomAssign s x))}

/-- Universal quantification, the dual `∀x φ = ¬∃x ¬φ`. -/
def forall_ (x : V) (φ : BilateralUpdate W V E) : BilateralUpdate W V E :=
  ~(exists_ x (~φ))

/-- Egli's positive equivalence: `(∃x φ) ∧ ψ` and `∃x (φ ∧ ψ)` have the same positive update, so
an existential binds into a later conjunct. The negative updates differ in general, since a denied
existential introduces no referent and a denied conjunction can. -/
theorem egli (x : V) (φ ψ : BilateralUpdate W V E) (s) :
    ((exists_ x φ) ⊙ ψ).positive s = (exists_ x (φ ⊙ ψ)).positive s := by
  simp [exists_]

theorem negative_exists_subset (x : V) (φ : BilateralUpdate W V E) (s) :
    (exists_ x φ).negative s ⊆ s :=
  Set.sep_subset _ _

/-- At a novel referent, a point subsists after random assignment and a predication iff its world
has a witness. -/
theorem mem_lowerClosure_positive_pred1_randomAssign (P : E → W → Prop) (hp : p ∈ s)
    (hx : State.Novel s x) :
    p ∈ lowerClosure ((pred1 P x).positive (State.randomAssign s x)) ↔ ∃ e, P e p.world := by
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨-, e, -, hP⟩ := mem_positive_pred1.1 hq
    exact ⟨e, (Possibility.le_def.mp hpq).1 ▸ hP⟩
  · rintro ⟨e, hP⟩
    exact ⟨p.update x ↑e, mem_positive_pred1.2 ⟨⟨p, hp, e, rfl⟩, e, by simp, hP⟩,
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
    have := (mem_lowerClosure_positive_pred1_randomAssign (fun e w ↦ ¬ P e w) hp hx).2 ⟨e, h e⟩
    rwa [← neg_pred1] at this

/-- At a novel referent, `∃x P(x)` is bivalent: every point subsists in one of its updates. -/
theorem unknownUpdate_exists_pred1 [Nonempty E] (P : E → W → Prop) (hx : State.Novel s x) :
    (exists_ x (pred1 P x)).unknownUpdate s = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hp, hpos, hneg⟩ ↦ hneg (subset_lowerClosure ?_)
  rw [negative_exists_pred1 P hx]
  exact ⟨hp, fun e he ↦ hpos ((mem_lowerClosure_positive_pred1_randomAssign P hp hx).2 ⟨e, he⟩)⟩

end Quantifiers

end BilateralUpdate

end DynamicSemantics
