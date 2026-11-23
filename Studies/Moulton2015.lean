module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Composition.Interpret
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Sorts
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Moulton (2015): CPs: copies and compositionality

A *that*-clause denotes a predicate of individuals with propositional content, such as ideas,
rumours and beliefs. For a content individual `x` and a world `w`, the content function gives the
proposition `cont x w` true at the worlds compatible with the content of `x` in `w`, and the
clause with proposition `p` holds of `x` in `w` when `cont x w = p`. Clauses with different
propositions hold of disjoint sets of individuals (`pairwise_disjoint_cont_eq`), so a second
clause cannot modify a noun that already has one.

The clause has the type of a noun, `⟨e,t⟩` at a world. With a content noun it combines by
Predicate Modification (`meanings_ideaThat`). A clause-taking verb wants an individual, so with
the clause as its sister no rule applies (`derive_inSitu`). In the tree `moved` the clause has
moved and left a trace of the type of individuals, the verb phrase with its eventuality argument
saturated by a variable is abstracted over the trace, the clause modifies the abstract, and
existential closure binds the content argument: its one meaning is the eventualities whose
holder is the subject and in which some individual with content `p` is explained
(`meanings_moved`).

The verb *believe* relates a content individual `x` and an eventuality `e` in `w` when the
content of `x` holds at every world compatible with what the holder of `e` believes in `w`. We
define `Believes cont dox holder a p w`, the report *`a` believes that `p`*, by existential
closure of the content individual and the eventuality; it is the closure over eventualities of
the meaning of `moved` with *believe* as its verb (`believes_iff_exists_meaning`). The report
holds exactly when `a` holds some eventuality, `p` is the content of some individual, and `p` is
true at every world compatible with what `a` believes (`believes_iff`); the last conjunct is the
truth condition of [hintikka-1969].

## Implementation notes

The holder of an eventuality is a function `holder : V → W → D`, where the paper writes a
definite description over a relation between individuals and eventualities. Propositions are
predicates of worlds, and the worlds compatible with what `a` believes in `w` are those `w`
accesses along `dox a`, so that Hintikka's truth condition is `□[dox a] p w`.

The trees are interpreted at a world, where the paper's rules are intensional, by Functional
Application, Predicate Modification and predicate abstraction, with the head that introduces the
holder joined to the verb phrase by the Event Identification of [kratzer-1996]. The tree `moved`
is the paper's (89) below its aspect head, with the lower copy of the clause as a trace.

## TODO

The movements that derive (89), and the paper's acceptability judgments, are not formalized.

## References

* [moulton-2015]
* [kratzer-2006]
* [kratzer-1996]
* [hintikka-1969]
-/

@[expose] public section

namespace Moulton2015

open ModalLogic Function

variable {X D V W : Type*} {cont : X → W → W → Prop} {dox : D → SetRel W W} {holder : V → W → D}
  {a : D} {p : W → Prop} {w : W}

-- fn. 10
theorem pairwise_disjoint_cont_eq (cont : X → W → W → Prop) (w : W) :
    Pairwise (Disjoint on fun p ↦ {x | cont x w = p}) :=
  pairwise_disjoint_fiber fun x ↦ cont x w

/-- fn. 12: *believe* holds of a content individual `x` and an eventuality `e` in `w` when the
content of `x` in `w` is true at every world compatible with what the holder of `e` believes. -/
def believe (cont : X → W → W → Prop) (dox : D → SetRel W W) (holder : V → W → D) (x : X) (e : V)
    (w : W) : Prop :=
  □[dox (holder e w)] (cont x w) w

/-- fn. 24: *`a` believes that `p`* holds in `w` when `a` holds an eventuality of believing some
content individual whose content in `w` is `p`. -/
def Believes (cont : X → W → W → Prop) (dox : D → SetRel W W) (holder : V → W → D) (a : D)
    (p : W → Prop) (w : W) : Prop :=
  ∃ e x, holder e w = a ∧ believe cont dox holder x e w ∧ cont x w = p

/-- A belief report holds exactly when the agent holds some eventuality, the clause's proposition
is the content of some individual, and the proposition is true at every world compatible with
what the agent believes. -/
theorem believes_iff :
    Believes cont dox holder a p w ↔
      (∃ e, holder e w = a) ∧ p ∈ Set.range (cont · w) ∧ □[dox a] p w :=
  ⟨fun ⟨e, x, ha, hb, hp⟩ ↦ ⟨⟨e, ha⟩, ⟨x, hp⟩, ha ▸ hp ▸ hb⟩,
    fun ⟨⟨e, ha⟩, ⟨x, hp⟩, h⟩ ↦ ⟨e, x, ha, by subst ha hp; exact h, hp⟩⟩

-- fn. 24
theorem Believes.box (h : Believes cont dox holder a p w) : □[dox a] p w :=
  (believes_iff.1 h).2.2

/-- Where every proposition is the content of some individual, a belief report of an agent who
holds some eventuality has Hintikka's truth condition. -/
theorem believes_iff_box (hc : Surjective (cont · w)) (ha : ∃ e, holder e w = a) :
    Believes cont dox holder a p w ↔ □[dox a] p w := by
  rw [believes_iff, hc.range_eq]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨ha, trivial, h⟩⟩

/-- Belief reports are closed under weakening of the clause to a proposition that is the content
of some individual. -/
theorem Believes.mono {q : W → Prop} (h : Believes cont dox holder a p w) (hpq : p ≤ q)
    (hq : q ∈ Set.range (cont · w)) : Believes cont dox holder a q w :=
  believes_iff.2 ⟨(believes_iff.1 h).1, hq, box_mono _ hpq w h.box⟩

/-- Hintikka's truth condition does not suffice for a belief report: with a single content
individual, whose content is the true proposition, the agent's alternatives verify that the world
is `true`, and no report with that clause holds. -/
example :
    □[(SetRel.id : SetRel Bool Bool)] (· = true) true ∧
      ¬ Believes (fun (_ : Unit) (_ _ : Bool) ↦ True) (fun (_ : Unit) ↦ SetRel.id)
        (fun (_ : Unit) _ ↦ ()) () (· = true) true :=
  ⟨box_id.2 rfl, fun h ↦ by
    obtain ⟨-, ⟨_, hx⟩, -⟩ := believes_iff.1 h
    exact Bool.false_ne_true ((congrFun hx false).mp trivial)⟩

/-! ### Composition -/

section Composition

open Interpreter PhraseStructure ManySorted

/-- The words of the trees, by semantic type at a world. -/
inductive Item : Ty Base → Type
  /-- The subject. -/
  | subject : Item .e
  /-- The head that introduces the holder of an eventuality. -/
  | holder : Item .evt
  /-- A clause-taking verb, (26). -/
  | verb : Item .evt
  /-- A content noun, (18). -/
  | noun : Item .et
  /-- The complementizer, (19b). -/
  | that : Item (.intens .t ⇒ .et)
  /-- The complementizer's sister, a proposition. -/
  | clause : Item (.intens .t)
  /-- Existential closure. -/
  | closure : Item (.et ⇒ .t)

/-- Functional Application, Predicate Modification and Event Identification. -/
abbrev grammar : Language (Ty Base) :=
  (application.sum predicateModification).sum (eventIdentification .e .v)

/-- The types of the indices: `2` is the index of an eventuality, and the others are indices of
individuals. -/
abbrev indexTy : ℕ → Ty Base := fun n ↦ if n = 2 then .v else .e

variable {E V W : Type} (cont : E → W → W → Prop) (holder : V → W → E) (verb : E → V → W → Prop)
  (noun : E → W → Prop) (a : E) (p : W → Prop) (w : W)

/-- The domains of the base sorts over individuals `E`, eventualities `V` and worlds `W`. -/
abbrev Dom (E V W : Type) : Base → Type := Base.Dom E W { eventuality := V }

/-- The denotations of the words at the world `w`: the complementizer (19b) relates a proposition
to the individuals whose content at `w` it is. -/
def Item.val : {b : Ty Base} → Item b → b.Dom (Dom E V W)
  | _, .subject => a
  | _, .holder => fun x e ↦ holder e w = x
  | _, .verb => fun x e ↦ verb x e w
  | _, .noun => fun x ↦ noun x w
  | _, .that => fun q x ↦ cont x w = q
  | _, .clause => p
  | _, .closure => fun P ↦ ∃ x, P x

/-- The leaf of a word. -/
def leaf {b : Ty Base} (i : Item b) : Tree Unit (Σ b, Item b) := .leaf ⟨b, i⟩

/-- The clause: the complementizer and its sister. -/
def cp : Tree Unit (Σ b, Item b) := .bin (leaf .that) (leaf .clause)

/-- (21): a content noun with a clause. -/
def nounThat : Tree Unit (Σ b, Item b) := .bin (leaf .noun) cp

/-- The verb phrase with the clause as the sister of the verb. -/
def inSitu : Tree Unit (Σ b, Item b) :=
  .bin (leaf .subject) (.bin (leaf .holder) (.bin (leaf .verb) cp))

/-- (89): the clause above the abstract over its trace `1`, under existential closure, with the
eventuality argument of the verb phrase saturated by the variable `2` and abstracted over. -/
def moved : Tree Unit (Σ b, Item b) :=
  .binder 2 (.bin (leaf .closure) (.bin cp (.binder 1
    (.bin (.bin (leaf .subject) (.bin (leaf .holder) (.bin (leaf .verb) (.tr 1)))) (.tr 2)))))

/-- The meanings of a tree at the world `w`, relative to an assignment. -/
def meanings (t : Tree Unit (Σ b, Item b)) :
    List (Σ b : Ty Base, (∀ n, (indexTy n).Dom (Dom E V W)) → b.Dom (Dom E V W)) :=
  t.interpret grammar (Dom E V W) indexTy (fun i _ ↦ Item.val cont holder verb noun a p w i)
    fun x ↦ [x]

-- (21)
theorem meanings_nounThat :
    meanings cont holder verb noun a p w nounThat =
      [⟨.et, fun _ x ↦ noun x w ∧ cont x w = p⟩] :=
  rfl

/-- With the clause as the sister of the verb no rule applies: the verb wants an individual, and
the clause is a predicate of individuals. -/
theorem derive_inSitu : inSitu.derive grammar indexTy (W := Item) (fun x ↦ [x]) = [] :=
  rfl

/-- (89): the moved clause modifies the abstract over its trace, and the one meaning of the
tree is the eventualities held by the subject in which some individual with content `p` is the
verb's content argument. -/
theorem meanings_moved :
    meanings cont holder verb noun a p w moved =
      [⟨.vt, fun _ e ↦ ∃ x, cont x w = p ∧ holder e w = a ∧ verb x e w⟩] :=
  rfl

-- fn. 24
theorem believes_iff_exists_meaning (dox : E → SetRel W W)
    (g : ∀ n, (indexTy n).Dom (Dom E V W)) :
    Believes cont dox holder a p w ↔
      ∃ m, ⟨.vt, m⟩ ∈ meanings cont holder (believe cont dox holder) noun a p w moved ∧
        ∃ e, m g e := by
  rw [meanings_moved]
  constructor
  · rintro ⟨e, x, ha, hb, hp⟩
    exact ⟨_, List.mem_singleton.2 rfl, e, x, hp, ha, hb⟩
  · rintro ⟨m, hm, e, he⟩
    obtain rfl := eq_of_heq (Sigma.mk.inj (List.mem_singleton.1 hm)).2
    obtain ⟨x, hp, ha, hb⟩ := he
    exact ⟨e, x, ha, hb, hp⟩

end Composition

end Moulton2015
