module

public import Linglib.Syntax.Minimalist.Linearization.SpelloutDomain
public import Linglib.Data.Examples.FoxPesetsky2005

/-!
# Fox and Pesetsky (2005): Cyclic Linearization of Syntactic Structure

This file formalizes [fox-pesetsky-2005]'s account of successive cyclicity and Holmberg's
Generalization under cyclic linearization (`Minimalist.Linearization.Consistent`). The
derivational scenarios (13)–(15) are theorems over arbitrary terminals: movement from the left
edge of a domain converges, movement from a non-edge position crashes on the pair it reorders,
and moving the edge material along restores the order. Swedish Object Shift is these scenarios
with the verb, the object and an intervener as the terminals. The derivations the paper sketches
for its sentences spell out the snapshots it draws (`Sketch.spellouts_eq_phases`), and whether
they linearize predicts the sentences' judgments (`rows_predicted`).

## References

* [fox-pesetsky-2005]
-/

@[expose] public section

namespace FoxPesetsky2005

open Minimalist Linearization

variable {α : Type*} {X Y Z a : α}

/-! ### Derivational scenarios -/

-- (13)
theorem scenario1 [DecidableEq α] (hnd : [X, a, Y, Z].Nodup) :
    Consistent [[X, Y, Z], [X, a, Y, Z]] :=
  consistent_of_forall_sublist (by simp) hnd

-- (14)
theorem scenario2 : ¬ Consistent [[X, Y, Z], [Y, a, X, Z]] :=
  not_consistent_of_pair X Y ⟨[X, Y, Z], by simp, by simp⟩ ⟨[Y, a, X, Z], by simp, by simp⟩

-- (15)
theorem scenario3 [DecidableEq α] (hnd : [X, Y, a, Z].Nodup) :
    Consistent [[X, Y, Z], [X, Y, a, Z]] :=
  consistent_of_forall_sublist (by simp) hnd

theorem cycle {b c : α} : ¬ Consistent [[a, b], [b, c], [c, a]] := fun h ↦
  h a (.tail (.tail (.single ⟨[a, b], by simp, .refl _⟩) ⟨[b, c], by simp, .refl _⟩)
    ⟨[c, a], by simp, .refl _⟩)

/-! ### Holmberg's Generalization -/

section Holmberg

variable {S V O adv C aux XP : α}

-- (20)
theorem objectShift_verbToC [DecidableEq α] (hnd : [S, V, O, adv].Nodup) :
    Consistent [[V, O], [S, V, O, adv]] :=
  consistent_of_forall_sublist (by
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨(List.sublist_append_left [V, O] [adv]).cons S, .refl _⟩) hnd

-- (21)
theorem objectShift_embedded : ¬ Consistent [[V, O], [C, S, O, adv, V]] :=
  not_consistent_of_pair V O ⟨[V, O], by simp, by simp⟩
    ⟨[C, S, O, adv, V], by simp, by simp [List.sublist_cons_iff]⟩

-- (22)
theorem objectShift_aux : ¬ Consistent [[V, O], [S, aux, O, adv, V]] :=
  not_consistent_of_pair V O ⟨[V, O], by simp, by simp⟩
    ⟨[S, aux, O, adv, V], by simp, by simp [List.sublist_cons_iff]⟩

-- (24)
theorem objectShift_intervener : ¬ Consistent [[V, XP, O], [S, V, O, adv, XP]] :=
  not_consistent_of_pair XP O ⟨[V, XP, O], by simp, by simp⟩
    ⟨[S, V, O, adv, XP], by simp, by simp [List.sublist_cons_iff]⟩

-- (26)
theorem objectShift_intervener_fronted [DecidableEq α] (hnd : [XP, V, S, O, adv].Nodup) :
    Consistent [[XP, V, O], [XP, V, S, O, adv]] :=
  consistent_of_forall_sublist (by
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨.cons_cons XP (.cons_cons V (.cons S (.cons_cons O (List.nil_sublist _)))), .refl _⟩)
    hnd

end Holmberg

/-! ### The Swedish data -/

/-- A terminal is a word or phrase of the paper's Object Shift sketches. -/
inductive Terminal
  | S | V | O | adv | C | aux | XP
  deriving DecidableEq, Repr


/-- Each terminal spells out its own lexical item. -/
def Terminal.token : Terminal → LexicalItem.Token
  | .S => ⟨.of .D [], 1⟩
  | .V => ⟨.of .V [], 2⟩
  | .O => ⟨.of .D [], 3⟩
  | .adv => ⟨.of .Neg [], 4⟩
  | .C => ⟨.of .C [], 5⟩
  | .aux => ⟨.of .T [], 6⟩
  | .XP => ⟨.of .P [], 7⟩

/-- A lexical item spells out at most one terminal. -/
def Terminal.ofToken? (tok : LexicalItem.Token) : Option Terminal :=
  [Terminal.S, .V, .O, .adv, .C, .aux, .XP].find? (·.token = tok)

/-- The paper sketches the derivation of an Object Shift sentence as one of (20)–(22), (24) and
(26). -/
inductive Sketch
  /-- The finite verb moves to C (20). -/
  | verbToC
  /-- The complementizer of an embedded clause keeps the verb in VP (21). -/
  | embedded
  /-- An auxiliary moves to C and the verb stays in VP (22). -/
  | auxiliary
  /-- A first object or particle precedes the object in VP (24). -/
  | intervener
  /-- The intervener fronts through the VP edge (26). -/
  | intervenerFronted
  deriving DecidableEq, Repr

namespace Sketch

open Terminal

/-- The VP of a sketch is the verb with its object, preceded in (24) and (26) by the intervener,
which in (26) moves to the VP edge. -/
def vpSteps : Sketch → List Step
  | verbToC | embedded | auxiliary => [.em .right O.token]
  | intervener => [.em .right XP.token, .em .right O.token]
  | intervenerFronted =>
    [.em .right XP.token, .em .right O.token, .im XP.token]

/-- Above the VP the adverb adjoins, the object shifts and the subject merges, and then the
verb, the auxiliary or the intervener moves to C, as the bracketings (20b)–(22b), (24) and (26)
show. -/
def cpSteps : Sketch → List Step
  | verbToC =>
    [.em .left adv.token, .im O.token, .em .left S.token,
      .im V.token, .im S.token]
  | embedded =>
    [.em .left adv.token, .im O.token, .em .left S.token,
      .em .left C.token]
  | auxiliary =>
    [.em .left aux.token, .em .left adv.token, .im O.token,
      .em .left S.token, .im aux.token, .im S.token]
  | intervener =>
    [.em .left adv.token, .im O.token, .em .left S.token,
      .im V.token, .im S.token]
  | intervenerFronted =>
    [.em .left adv.token, .im O.token, .em .left S.token,
      .im V.token, .im XP.token]

/-- A sketch's derivation starts from the verb. -/
def derivation (s : Sketch) : Derivation := ⟨V.token, s.vpSteps ++ s.cpSteps⟩

/-- The VP is spelled out when it is built, and the CP at the end of the derivation. -/
def schedule (s : Sketch) : List (ℕ × ℕ) :=
  [(s.vpSteps.length, s.vpSteps.length), (s.derivation.length, s.derivation.length)]

/-- The paper draws these VP and CP snapshots. -/
def phases : Sketch → List (List Terminal)
  | verbToC => [[V, O], [S, V, O, adv]]
  | embedded => [[V, O], [C, S, O, adv, V]]
  | auxiliary => [[V, O], [S, aux, O, adv, V]]
  | intervener => [[V, XP, O], [S, V, O, adv, XP]]
  | intervenerFronted => [[XP, V, O], [XP, V, S, O, adv]]

theorem spellouts_eq_phases (s : Sketch) :
    s.schedule.map (fun p ↦ (s.derivation.spellout p.1 p.2).filterMap Terminal.ofToken?) =
      s.phases := by
  cases s <;> decide

/-- These feature values name the sketches in the example data. -/
def table : List (String × Sketch) :=
  [("verbToC", verbToC), ("embedded", embedded), ("auxiliary", auxiliary),
    ("intervener", intervener), ("intervenerFronted", intervenerFronted)]

end Sketch

theorem rows_predicted : ∀ ex ∈ Examples.all, ∀ s ∈ ex.parse? "sketch" Sketch.table,
    (ex.judgment = .acceptable ↔ s.derivation.Linearizes s.schedule) := by
  decide

end FoxPesetsky2005
