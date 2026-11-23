module

public import Linglib.Logic.Modal.Defs
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Moulton (2015): CPs: copies and compositionality

A *that*-clause denotes a predicate of individuals with propositional content, such as ideas,
rumours and beliefs. The content function gives, for a content individual `x` and a world `w`,
the proposition `cont x w` true at the worlds compatible with the content of `x` in `w`, and the
clause with proposition `p` holds of `x` in `w` when `cont x w = p`. A content noun and a clause
combine by predicate modification, and so does a clause with the verb phrase abstracted over the
verb's content argument, which existential closure then binds.

The verb *believe* relates a content individual `x` and an eventuality `e` in `w` when the
content of `x` holds at every world compatible with what the holder of `e` believes in `w`. The
closed report `Believes cont dox holder a p w` then holds exactly when `a` holds some eventuality,
`p` is the content of some individual, and `p` is true at every world compatible with what `a`
believes, as `believes_iff` states; the last conjunct is the truth condition of [hintikka-1969].

## Implementation notes

The holder of an eventuality is a function `holder : V → W → D`, where the paper writes a
definite description over a relation between individuals and eventualities. Propositions are
predicates of worlds, and the worlds compatible with what `a` believes in `w` are those `w`
accesses along `dox a`, so that Hintikka's truth condition is `□[dox a] p w`.

## TODO

The syntax of the paper, in which the clause moves and leaves a copy, is not formalized, and
neither are its acceptability judgments.

## References

* [moulton-2015]
* [kratzer-2006]
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
  Set.pairwise_disjoint_fiber _

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
    obtain ⟨-, ⟨-, hx⟩, -⟩ := believes_iff.1 h
    exact Bool.false_ne_true (congrFun hx false).mp trivial⟩

end Moulton2015
