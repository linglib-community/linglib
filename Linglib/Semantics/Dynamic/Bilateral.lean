module

public import Linglib.Logic.Trivalent.Proposition
public import Linglib.Logic.Trivalent.Connectives
public import Linglib.Logic.Trivalent.Part
public import Linglib.Semantics.Dynamic.State
public import Linglib.Semantics.Dynamic.Update

/-!
# Bilateral Update Semantics

A **bilateral update** pairs a positive update, the state that survives asserting a sentence, with a
negative update, the state that survives denying it, over states of world–assignment pairs with
partial assignments. The **unknown update** keeps the points that subsist in neither, so a sentence
updates a state at each of the three truth values. Negation swaps the positive and negative updates,
as in Krahmer and Muskens's bilateral DRT, so [it negates the truth
value](##DynamicSemantics.BilateralUpdate.update_neg). A binary truth function
[lifts](##DynamicSemantics.BilateralUpdate.lift) to the union, over the cells of its table, of the
updates by the two operands in turn; conjunction and disjunction lift the strong Kleene tables, so
[de Morgan's laws hold](##DynamicSemantics.BilateralUpdate.neg_disj). Atomic sentences are the
static updates of trivalent propositions over points.
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

/-- A **bilateral update** is a pair of updates. Its positive update, written `s[φ]⁺`, is the result
of asserting a sentence at a state, and its negative update, `s[φ]⁻`, the result of denying it. -/
@[ext] structure BilateralUpdate (W V E : Type*) where
  /-- The positive update. -/
  positive : CCP (Possibility W V (Part E))
  /-- The negative update. -/
  negative : CCP (Possibility W V (Part E))

namespace BilateralUpdate

variable {φ ψ : BilateralUpdate W V E} {s : Set (Possibility W V (Part E))}
  {p : Possibility W V (Part E)}

/-!
### Negation and the unknown update

A sentence with a pronoun that has no antecedent is neither true nor false. The points of a state at
which a sentence is neither form its unknown update, which Elliott calls presupposition failure. A
sentence can be asserted at a state where that update is empty.
-/

/-- **Negation** swaps the positive and the negative update. -/
def neg (φ : BilateralUpdate W V E) : BilateralUpdate W V E where
  positive := φ.negative
  negative := φ.positive

@[inherit_doc] scoped prefix:max "~" => neg

@[simp] theorem positive_neg (φ : BilateralUpdate W V E) : (~φ).positive = φ.negative := rfl
@[simp] theorem negative_neg (φ : BilateralUpdate W V E) : (~φ).negative = φ.positive := rfl

/-- Negating twice gives back the same update, by definition. -/
@[simp] theorem neg_neg (φ : BilateralUpdate W V E) : ~~φ = φ := rfl

/-- The **unknown update** of a sentence at a state, written `s[φ]?`, keeps the points of the state
that subsist in neither its positive nor its negative update. -/
def unknownUpdate (φ : BilateralUpdate W V E)
    (s : Set (Possibility W V (Part E))) : Set (Possibility W V (Part E)) :=
  {p ∈ s | p ∉ lowerClosure (φ.positive s) ∧ p ∉ lowerClosure (φ.negative s)}

/-- A sentence is **assertable** at a state when its unknown update there is empty, that is, when
every point of the state subsists in one of its two updates. -/
def Assertable (φ : BilateralUpdate W V E) (c : Set (Possibility W V (Part E))) : Prop :=
  φ.unknownUpdate c = ∅

theorem unknownUpdate_neg (φ : BilateralUpdate W V E) (s) :
    (~φ).unknownUpdate s = φ.unknownUpdate s := by
  ext p
  simp only [unknownUpdate, neg, Set.mem_ofPred_eq,
    and_comm (a := p ∉ lowerClosure (φ.negative s))]

/-- The **update at a truth value** is the positive update at true, the negative update at false and
the unknown update at undefined. -/
def update (φ : BilateralUpdate W V E) : Trivalent → CCP (Possibility W V (Part E))
  | .true => φ.positive
  | .false => φ.negative
  | .undefined => φ.unknownUpdate

@[simp] theorem update_true (φ : BilateralUpdate W V E) : φ.update .true = φ.positive := rfl
@[simp] theorem update_false (φ : BilateralUpdate W V E) : φ.update (.false) = φ.negative := rfl
@[simp] theorem update_undefined (φ : BilateralUpdate W V E) :
    φ.update .undefined = φ.unknownUpdate := rfl

/-- Negation negates the truth value at which a sentence updates. -/
theorem update_neg (φ : BilateralUpdate W V E) (a : Trivalent) : (~φ).update a = φ.update (aᶜ) := by
  cases a
  exacts [rfl, funext (unknownUpdate_neg φ), rfl]

/-!
### Static updates

An atomic sentence introduces no referent and only tests the points of a state. It is given by a
three-valued proposition over points, and its two updates keep the points where that proposition is
true and where it is false. A predication is undefined at a point that gives its variable no value.
-/

/-- The **static update** of a three-valued proposition over points introduces no referent. Its
positive update keeps the points where the proposition is true, and its negative update the points
where it is false. -/
def ofTrivalent (v : Possibility W V (Part E) → Trivalent) : BilateralUpdate W V E where
  positive := CCP.up (Trivalent.posExt v)
  negative := CCP.up (Trivalent.negExt v)

variable {v : Possibility W V (Part E) → Trivalent}

@[simp] theorem mem_positive_ofTrivalent : p ∈ (ofTrivalent v).positive s ↔ p ∈ s ∧ v p = .true :=
  Iff.rfl

@[simp] theorem mem_negative_ofTrivalent : p ∈ (ofTrivalent v).negative s ↔ p ∈ s ∧ v p = .false :=
  Iff.rfl

theorem positive_ofTrivalent_of_eq_undefined (h : ∀ p ∈ s, v p = .undefined) :
    (ofTrivalent v).positive s = ∅ :=
  Set.eq_empty_of_forall_notMem fun p ⟨hp, h1⟩ ↦ by simp [h p hp] at h1

theorem negative_ofTrivalent_of_eq_undefined (h : ∀ p ∈ s, v p = .undefined) :
    (ofTrivalent v).negative s = ∅ :=
  Set.eq_empty_of_forall_notMem fun p ⟨hp, h1⟩ ↦ by simp [h p hp] at h1

/-- At a state where a three-valued proposition is undefined at every point, the unknown update of
its static update is the whole state. -/
theorem unknownUpdate_ofTrivalent_of_eq_undefined (h : ∀ p ∈ s, v p = .undefined) :
    (ofTrivalent v).unknownUpdate s = s := by
  ext p
  simp [unknownUpdate, positive_ofTrivalent_of_eq_undefined h,
      negative_ofTrivalent_of_eq_undefined h]

/-- At a state where a three-valued proposition is true or false at every point, the unknown update
of its static update is empty. -/
theorem unknownUpdate_ofTrivalent_of_ne_undefined (h : ∀ p ∈ s, v p ≠ .undefined) :
    (ofTrivalent v).unknownUpdate s = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hp, hpos, hneg⟩ ↦ ?_
  match hv : v p with
  | .true => exact hpos (subset_lowerClosure ⟨hp, hv⟩)
  | .false => exact hneg (subset_lowerClosure ⟨hp, hv⟩)
  | .undefined => exact h p hp hv

open scoped Classical in
/-- A **worldly atom** is the static update of a proposition about worlds. It is true at a point
when the proposition holds at the point's world, whatever the assignment, and false otherwise. -/
noncomputable def atom (pred : W → Prop) : BilateralUpdate W V E :=
  ofTrivalent fun p ↦ Trivalent.ofProp (pred p.world)

/-- **Unary predication** of a variable is true at a point where the predicate holds of the
variable's value, false where it does not, and undefined where the variable has no value. -/
noncomputable def pred1 (P : E → W → Prop) (t : V) : BilateralUpdate W V E :=
  ofTrivalent fun p ↦ Trivalent.ofPart ((p.assignment t).map fun e ↦ P e p.world)

/-- **Binary predication** of two variables is true or false at a point according to whether the
relation holds of their values, and undefined where either has no value. -/
noncomputable def pred2 (P : E → E → W → Prop) (t₁ t₂ : V) : BilateralUpdate W V E :=
  ofTrivalent fun p ↦ Trivalent.ofPart <|
    (p.assignment t₁).bind fun e₁ ↦ (p.assignment t₂).map fun e₂ ↦ P e₁ e₂ p.world

@[simp] theorem mem_positive_atom {pred : W → Prop} :
    p ∈ (atom pred).positive s ↔ p ∈ s ∧ pred p.world := by
  simp [atom]

@[simp] theorem mem_negative_atom {pred : W → Prop} :
    p ∈ (atom pred).negative s ↔ p ∈ s ∧ ¬ pred p.world := by
  simp [atom]

@[simp] theorem mem_positive_pred1 {P : E → W → Prop} {t : V} :
    p ∈ (pred1 P t).positive s ↔ p ∈ s ∧ ∃ e ∈ p.assignment t, P e p.world := by
  simp only [pred1, mem_positive_ofTrivalent, Trivalent.ofPart_eq_true_iff, Part.mem_map_iff,
    exists_exists_and_eq_and]

@[simp] theorem mem_negative_pred1 {P : E → W → Prop} {t : V} :
    p ∈ (pred1 P t).negative s ↔ p ∈ s ∧ ∃ e ∈ p.assignment t, ¬ P e p.world := by
  simp only [pred1, mem_negative_ofTrivalent, Trivalent.ofPart_eq_false_iff, Part.mem_map_iff,
    exists_exists_and_eq_and]

@[simp] theorem mem_positive_pred2 {P : E → E → W → Prop} {t₁ t₂ : V} :
    p ∈ (pred2 P t₁ t₂).positive s ↔
      p ∈ s ∧ ∃ e₁ ∈ p.assignment t₁, ∃ e₂ ∈ p.assignment t₂, P e₁ e₂ p.world := by
  simp only [pred2, mem_positive_ofTrivalent, Trivalent.ofPart_eq_true_iff, Part.mem_bind_iff,
    Part.mem_map_iff]
  exact and_congr_right fun _ ↦ ⟨fun ⟨_, ⟨e₁, h₁, e₂, h₂, rfl⟩, h⟩ ↦ ⟨e₁, h₁, e₂, h₂, h⟩,
    fun ⟨e₁, h₁, e₂, h₂, h⟩ ↦ ⟨_, ⟨e₁, h₁, e₂, h₂, rfl⟩, h⟩⟩

@[simp] theorem mem_negative_pred2 {P : E → E → W → Prop} {t₁ t₂ : V} :
    p ∈ (pred2 P t₁ t₂).negative s ↔
      p ∈ s ∧ ∃ e₁ ∈ p.assignment t₁, ∃ e₂ ∈ p.assignment t₂, ¬ P e₁ e₂ p.world := by
  simp only [pred2, mem_negative_ofTrivalent, Trivalent.ofPart_eq_false_iff, Part.mem_bind_iff,
    Part.mem_map_iff]
  exact and_congr_right fun _ ↦ ⟨fun ⟨_, ⟨e₁, h₁, e₂, h₂, rfl⟩, h⟩ ↦ ⟨e₁, h₁, e₂, h₂, h⟩,
    fun ⟨e₁, h₁, e₂, h₂, h⟩ ↦ ⟨_, ⟨e₁, h₁, e₂, h₂, rfl⟩, h⟩⟩

theorem negative_atom (pred : W → Prop) (s : Set (Possibility W V (Part E))) :
    (atom pred (V := V) (E := E)).negative s = {p ∈ s | ¬ pred p.world} :=
  Set.ext fun _ ↦ mem_negative_atom

theorem unknownUpdate_atom (pred : W → Prop) (s) :
    (atom pred (V := V) (E := E)).unknownUpdate s = ∅ :=
  unknownUpdate_ofTrivalent_of_ne_undefined fun _ _ ↦ by simp

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
  positive_ofTrivalent_of_eq_undefined fun p hp ↦ Trivalent.ofPart_eq_undefined_iff.2 (hx p hp)

theorem negative_pred1_of_novel (P : E → W → Prop) (hx : State.Novel s x) :
    (pred1 P x).negative s = ∅ :=
  negative_ofTrivalent_of_eq_undefined fun p hp ↦ Trivalent.ofPart_eq_undefined_iff.2 (hx p hp)

theorem unknownUpdate_pred1_of_novel (P : E → W → Prop) (hx : State.Novel s x) :
    (pred1 P x).unknownUpdate s = s :=
  unknownUpdate_ofTrivalent_of_eq_undefined fun p hp ↦ Trivalent.ofPart_eq_undefined_iff.2 (hx p hp)

/-!
### Connectives

The connectives come from the strong Kleene truth tables. A compound is verified by the union of the
ways of verifying it, one for each cell of the table whose value is true, and falsified likewise. A
cell is the update by the first operand at the row's value, followed by the second at the column's.
-/

/-- The **lift** of a binary truth function to bilateral updates has as its positive update the
union, over the cells of the function's table whose value is true, of the update by the first
operand at the row's value followed by the second at the column's. Its negative update is the same
union over the cells whose value is false. -/
def lift (f : Trivalent → Trivalent → Trivalent) (φ ψ : BilateralUpdate W V E) :
    BilateralUpdate W V E where
  positive s := ⋃ (a) (b) (_ : f a b = .true), ψ.update b (φ.update a s)
  negative s := ⋃ (a) (b) (_ : f a b = .false), ψ.update b (φ.update a s)

variable {f : Trivalent → Trivalent → Trivalent}

@[simp] theorem mem_positive_lift :
    p ∈ (lift f φ ψ).positive s ↔ ∃ a b, f a b = .true ∧ p ∈ ψ.update b (φ.update a s) := by
  simp [lift]

@[simp] theorem mem_negative_lift :
    p ∈ (lift f φ ψ).negative s ↔ ∃ a b, f a b = .false ∧ p ∈ ψ.update b (φ.update a s) := by
  simp [lift]

/-- The negation of a lift is the lift, to the negated operands, of the truth function that negates
both of its arguments and its value. -/
theorem neg_lift (f : Trivalent → Trivalent → Trivalent) (φ ψ : BilateralUpdate W V E) :
    ~(lift f φ ψ) = lift (fun a b ↦ (f (aᶜ) (bᶜ))ᶜ) (~φ) (~ψ) := by
  have key (c : Trivalent) (p) (s) : (∃ a b, f a b = c ∧ p ∈ ψ.update b (φ.update a s)) ↔
      ∃ a b, (f (aᶜ) (bᶜ))ᶜ = cᶜ ∧ p ∈ (~ψ).update b ((~φ).update a s) := by
    simp only [update_neg, InvolutiveCompl.compl_inj_iff]
    exact ⟨fun ⟨a, b, h, hp⟩ ↦ ⟨aᶜ, bᶜ, by simpa using h, by simpa using hp⟩,
      fun ⟨a, b, h, hp⟩ ↦ ⟨aᶜ, bᶜ, h, hp⟩⟩
  ext s p
  · change p ∈ (lift f φ ψ).negative s ↔ _
    rw [mem_negative_lift, mem_positive_lift, key (.false)]
    simp
  · change p ∈ (lift f φ ψ).positive s ↔ _
    rw [mem_positive_lift, mem_negative_lift, key .true]
    simp

/-- **Conjunction** is the lift of strong Kleene conjunction. -/
def conj (φ ψ : BilateralUpdate W V E) : BilateralUpdate W V E := lift (· ⊓ ·) φ ψ

@[inherit_doc] scoped infixl:65 " ⊙ " => conj

/-- **Disjunction** is the lift of strong Kleene disjunction. -/
def disj (φ ψ : BilateralUpdate W V E) : BilateralUpdate W V E := lift (· ⊔ ·) φ ψ

@[inherit_doc] scoped infixl:60 " ⊕ " => disj

/-- The positive update of a conjunction is the positive update of the first conjunct followed by
that of the second, so a conjunction is verified only by verifying both. -/
@[simp] theorem positive_conj : (φ ⊙ ψ).positive s = ψ.positive (φ.positive s) := by
  ext p
  simp [conj]

/-- The negative update of a disjunction is the negative update of the first disjunct followed by
that of the second, so a disjunction is falsified only by falsifying both. -/
@[simp] theorem negative_disj : (φ ⊕ ψ).negative s = ψ.negative (φ.negative s) := by
  ext p
  simp [disj]

/-- The negation of a disjunction is the conjunction of the negations, in the positive and the
negative update alike. -/
theorem neg_disj (φ ψ : BilateralUpdate W V E) : ~(φ ⊕ ψ) = (~φ) ⊙ (~ψ) := by
  rw [disj, neg_lift]
  simp only [Trivalent.compl_sup, Trivalent.compl_compl]
  rfl

/-- The negation of a conjunction is the disjunction of the negations, in the positive and the
negative update alike. -/
theorem neg_conj (φ ψ : BilateralUpdate W V E) : ~(φ ⊙ ψ) = (~φ) ⊕ (~ψ) := by
  rw [conj, neg_lift]
  simp only [Trivalent.compl_inf, Trivalent.compl_compl]
  rfl

/-!
### Responsibility

The cells that verify a disjunction are those where the first disjunct is true and those where the
second is. Each set is a part of the update that one disjunct answers for, and the two share the
cell where both are true. Elliott computes the positive update of a donkey disjunction one part at a
time.
-/

/-- The **first part** of a compound's update at a truth value, the part its first operand answers
for, is the union of the cells in which the first operand has that value. -/
def firstPart (v : Trivalent) (φ ψ : BilateralUpdate W V E) (s : Set (Possibility W V (Part E))) :
    Set (Possibility W V (Part E)) :=
  ⋃ b, ψ.update b (φ.update v s)

/-- The **second part** of a compound's update at a truth value, the part its second operand answers
for, is the union of the cells in which the second operand has that value. -/
def secondPart (v : Trivalent) (φ ψ : BilateralUpdate W V E) (s : Set (Possibility W V (Part E))) :
    Set (Possibility W V (Part E)) :=
  ⋃ a, ψ.update v (φ.update a s)

@[simp] theorem mem_firstPart {v : Trivalent} :
    p ∈ firstPart v φ ψ s ↔ ∃ b, p ∈ ψ.update b (φ.update v s) :=
  Set.mem_iUnion

@[simp] theorem mem_secondPart {v : Trivalent} :
    p ∈ secondPart v φ ψ s ↔ ∃ a, p ∈ ψ.update v (φ.update a s) :=
  Set.mem_iUnion

/-- The positive update of a disjunction is the union of its first and its second part at the value
true, so a disjunction is verified by its first disjunct or by its second. -/
theorem positive_disj_eq_union :
    (φ ⊕ ψ).positive s = firstPart .true φ ψ s ∪ secondPart .true φ ψ s := by
  ext p
  simp only [disj, mem_positive_lift, Trivalent.sup_eq_true_iff, Set.mem_union, mem_firstPart,
    mem_secondPart]
  constructor
  · rintro ⟨a, b, h | h, hp⟩ <;> subst h
    exacts [.inl ⟨b, hp⟩, .inr ⟨a, hp⟩]
  · rintro (⟨b, hp⟩ | ⟨a, hp⟩)
    exacts [⟨.true, b, .inl rfl, hp⟩, ⟨a, .true, .inr rfl, hp⟩]

theorem firstPart_neg (v : Trivalent) (φ ψ : BilateralUpdate W V E) (s) :
    firstPart v (~φ) (~ψ) s = firstPart (vᶜ) φ ψ s := by
  ext p
  simp only [mem_firstPart, update_neg]
  exact ⟨fun ⟨b, hp⟩ ↦ ⟨bᶜ, hp⟩, fun ⟨b, hp⟩ ↦ ⟨bᶜ, by simpa using hp⟩⟩

theorem secondPart_neg (v : Trivalent) (φ ψ : BilateralUpdate W V E) (s) :
    secondPart v (~φ) (~ψ) s = secondPart (vᶜ) φ ψ s := by
  ext p
  simp only [mem_secondPart, update_neg]
  exact ⟨fun ⟨a, hp⟩ ↦ ⟨aᶜ, hp⟩, fun ⟨a, hp⟩ ↦ ⟨aᶜ, by simpa using hp⟩⟩

/-!
### Quantifiers

Asserted, an existential introduces a referent: its positive update is that of its scope after
random assignment. Denied, it introduces none: its negative update keeps the points of the input
that subsist in the scope's negative update and not in its positive one. The universal is the dual.
-/

section Quantifiers
variable [DecidableEq V]

/-- The positive update of an **existential quantification** is that of its scope after random
assignment of the variable. Its negative update keeps the points of the input that subsist in the
scope's negative update after random assignment and not in its positive update, so a denied
existential introduces no referent. -/
def exists_ (x : V) (φ : BilateralUpdate W V E) : BilateralUpdate W V E where
  positive s := φ.positive (State.randomAssign s x)
  negative s := {p ∈ s | p ∉ lowerClosure (φ.positive (State.randomAssign s x)) ∧
    p ∈ lowerClosure (φ.negative (State.randomAssign s x))}

/-- **Universal quantification** is the dual of existential quantification, the negation of the
existential of the negated scope. -/
def forall_ (x : V) (φ : BilateralUpdate W V E) : BilateralUpdate W V E :=
  ~(exists_ x (~φ))

/-- The conjunction of an existential with a further sentence and the existential of the conjunction
have the same positive update, so an existential binds into a later conjunct; this is Egli's
equivalence. Their negative updates differ in general, since a denied existential introduces no
referent and a denied conjunction can. -/
theorem egli (x : V) (φ ψ : BilateralUpdate W V E) (s) :
    ((exists_ x φ) ⊙ ψ).positive s = (exists_ x (φ ⊙ ψ)).positive s := by
  simp [exists_]

theorem negative_exists_subset (x : V) (φ : BilateralUpdate W V E) (s) :
    (exists_ x φ).negative s ⊆ s :=
  Set.sep_subset _ _

/-- At a state where the variable is novel, a point subsists in the result of random assignment
followed by a predication exactly when some individual satisfies the predicate at the point's
world. -/
theorem mem_lowerClosure_positive_pred1_randomAssign (P : E → W → Prop) (hp : p ∈ s)
    (hx : State.Novel s x) :
    p ∈ lowerClosure ((pred1 P x).positive (State.randomAssign s x)) ↔ ∃ e, P e p.world := by
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨-, e, -, hP⟩ := mem_positive_pred1.1 hq
    exact ⟨e, (Possibility.le_def.mp hpq).1 ▸ hP⟩
  · rintro ⟨e, hP⟩
    exact ⟨p.update x (.some e), mem_positive_pred1.2 ⟨⟨p, hp, e, rfl⟩, e, by simp, hP⟩,
      Possibility.le_update_of_notMem (hx p hp) _⟩

/-- At a state where the variable is novel, and with at least one individual in the domain, the
negative update of `∃x P(x)` keeps the points at whose world nothing is `P`. -/
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

/-- At a state where the variable is novel, and with at least one individual in the domain, the
unknown update of `∃x P(x)` is empty, so every point subsists in its positive or its negative
update. -/
theorem unknownUpdate_exists_pred1 [Nonempty E] (P : E → W → Prop) (hx : State.Novel s x) :
    (exists_ x (pred1 P x)).unknownUpdate s = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hp, hpos, hneg⟩ ↦ hneg (subset_lowerClosure ?_)
  rw [negative_exists_pred1 P hx]
  exact ⟨hp, fun e he ↦ hpos ((mem_lowerClosure_positive_pred1_randomAssign P hp hx).2 ⟨e, he⟩)⟩

end Quantifiers

end BilateralUpdate

end DynamicSemantics
