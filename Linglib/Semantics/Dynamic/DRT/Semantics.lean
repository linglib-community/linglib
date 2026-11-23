module

public import Linglib.Semantics.Dynamic.DRT.Syntax
public import Linglib.Semantics.Dynamic.Update

/-!
# The semantics of DRSs

A DRS denotes a relation between states and a condition a set of states. Given a relation
`intro U` for each universe `U` and a set of states for each atomic condition, the value of a DRS
`[U | γ₁, …, γₙ]` is `intro U` followed by the test of `γ₁ ∩ ⋯ ∩ γₙ`, and the complex conditions
`¬K`, `K ⇒ K'` and `K ∨ K'` are the sets `(dom K)ᶜ`, `core K (dom K')` and `dom K ∪ dom K'`.

We define an `Interpretation` as that data and `DRS.eval`, `Condition.eval` as the values it
determines. The empty DRS denotes the identity, and a merge denotes the composite of its parts
when introducing the second universe does not disturb the first conditions (`DRS.eval_merge`).

## References

* [kamp-reyle-1993]
* [muskens-1996]
* [groenendijk-stokhof-1991]
-/

@[expose] public section

open FirstOrder
open DynamicSemantics (Update)
open DynamicSemantics.Update (test)
open SetRel

namespace DRT

universe u v w

variable {L : Language.{u, v}} {V : Type w} {S : Type*} [DecidableEq V]

/-- An interpretation of DRSs in a type of states: the relation that introduces a universe of
discourse referents, and the states at which each atomic condition holds. -/
structure Interpretation (L : Language.{u, v}) (V : Type w) (S : Type*) [DecidableEq V] where
  /-- Introducing the referents of a universe. -/
  intro : Finset V → Update S
  /-- The states at which an atom holds. -/
  atom : L.Atom V → Set S
  /-- The states at which two referents have the same value. -/
  eq : V → V → Set S
  /-- Introducing no referent changes nothing. -/
  intro_empty : intro ∅ = SetRel.id
  /-- Introducing two universes in sequence introduces their union. -/
  intro_union (U U' : Finset V) : intro (U ∪ U') = intro U ○ intro U'

mutual
/-- The relation a DRS denotes: introduce its universe, then test its conditions. -/
def DRS.eval (I : Interpretation L V S) : DRS L V → Update S
  | ⟨U, cs⟩ => I.intro U ○ test (Condition.evalAll I cs)
/-- The set of states at which a condition holds. -/
def Condition.eval (I : Interpretation L V S) : Condition L V → Set S
  | .atom a => I.atom a
  | .eq u v => I.eq u v
  | .neg K => (DRS.eval I K).domᶜ
  | .imp a c => (DRS.eval I a).core (DRS.eval I c).dom
  | .dis l r => (DRS.eval I l).dom ∪ (DRS.eval I r).dom
/-- The set of states at which every condition of a list holds. -/
def Condition.evalAll (I : Interpretation L V S) : List (Condition L V) → Set S
  | [] => Set.univ
  | c :: cs => Condition.eval I c ∩ Condition.evalAll I cs
end

variable {I : Interpretation L V S} {s t : S}

@[simp] theorem DRS.eval_mk (U : Finset V) (cs : List (Condition L V)) :
    (DRS.mk U cs).eval I = I.intro U ○ test (Condition.evalAll I cs) := by
  rw [DRS.eval]

theorem DRS.eval_eq (K : DRS L V) :
    K.eval I = I.intro K.referents ○ test (Condition.evalAll I K.conditions) := by
  cases K
  exact DRS.eval_mk ..

@[simp] theorem Condition.eval_atom (a : L.Atom V) : (Condition.atom a).eval I = I.atom a := by
  rw [Condition.eval]

@[simp] theorem Condition.eval_eq (x y : V) :
    (Condition.eq x y : Condition L V).eval I = I.eq x y := by
  rw [Condition.eval]

@[simp] theorem Condition.eval_neg (K : DRS L V) :
    (Condition.neg K).eval I = (K.eval I).domᶜ := by
  rw [Condition.eval]

@[simp] theorem Condition.eval_imp (a c : DRS L V) :
    (Condition.imp a c).eval I = (a.eval I).core (c.eval I).dom := by
  rw [Condition.eval]

@[simp] theorem Condition.eval_dis (l r : DRS L V) :
    (Condition.dis l r).eval I = (l.eval I).dom ∪ (r.eval I).dom := by
  rw [Condition.eval]

@[simp] theorem Condition.evalAll_nil :
    Condition.evalAll I ([] : List (Condition L V)) = Set.univ := by
  rw [Condition.evalAll]

@[simp] theorem Condition.evalAll_cons (c : Condition L V) (cs : List (Condition L V)) :
    Condition.evalAll I (c :: cs) = c.eval I ∩ Condition.evalAll I cs := by
  rw [Condition.evalAll]

theorem Condition.mem_evalAll_iff {cs : List (Condition L V)} :
    s ∈ Condition.evalAll I cs ↔ ∀ c ∈ cs, s ∈ c.eval I := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

@[simp] theorem Condition.evalAll_append (cs ds : List (Condition L V)) :
    Condition.evalAll I (cs ++ ds) = Condition.evalAll I cs ∩ Condition.evalAll I ds := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, Set.inter_assoc]

theorem DRS.mem_eval_iff {K : DRS L V} :
    s ~[K.eval I] t ↔ s ~[I.intro K.referents] t ∧ t ∈ Condition.evalAll I K.conditions := by
  rw [DRS.eval_eq, Update.mem_comp_test]

@[simp] theorem DRS.eval_empty : (DRS.empty : DRS L V).eval I = SetRel.id := by
  rw [DRS.empty, DRS.eval_mk, I.intro_empty, Condition.evalAll_nil, Update.test_univ, comp_id]

/-- A merge denotes the composite of its parts when introducing the second universe leaves the
first conditions as they are. -/
theorem DRS.eval_merge (K₁ K₂ : DRS L V)
    (h : ∀ ⦃s t⦄, s ∈ (I.intro K₁.referents).cod → s ~[I.intro K₂.referents] t →
      (s ∈ Condition.evalAll I K₁.conditions ↔ t ∈ Condition.evalAll I K₁.conditions)) :
    (K₁.merge K₂).eval I = K₁.eval I ○ K₂.eval I := by
  ext ⟨s, t⟩
  rw [DRS.mem_eval_iff, DRS.referents_merge, DRS.conditions_merge, Condition.evalAll_append,
    I.intro_union]
  constructor
  · rintro ⟨⟨r, hsr, hrt⟩, h₁, h₂⟩
    exact ⟨r, DRS.mem_eval_iff.mpr ⟨hsr, (h ⟨s, hsr⟩ hrt).mpr h₁⟩, DRS.mem_eval_iff.mpr ⟨hrt, h₂⟩⟩
  · rintro ⟨r, hsr, hrt⟩
    obtain ⟨hsr, h₁⟩ := DRS.mem_eval_iff.mp hsr
    obtain ⟨hrt, h₂⟩ := DRS.mem_eval_iff.mp hrt
    exact ⟨⟨r, hsr, hrt⟩, (h ⟨s, hsr⟩ hrt).mp h₁, h₂⟩

end DRT
