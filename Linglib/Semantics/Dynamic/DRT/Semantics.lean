module

public import Linglib.Semantics.Dynamic.DRT.Syntax
public import Linglib.Semantics.Dynamic.Update

/-!
# The semantics of DRSs

An embedding `f` *verifies* a DRS `K` when it verifies each condition of `K`, and `g` *extends*
`f` on `K`, written `f[K]g`, when `g` adds values for the universe of `K`. The complex conditions
are verified as follows:

* `f` verifies `¬K` iff no `g` with `f[K]g` verifies `K`;
* `f` verifies `K ⇒ K'` iff every `g` with `f[K]g` that verifies `K` has an `h` with `g[K']h` that
  verifies `K'`;
* `f` verifies `K ∨ K'` iff some `g` with `f[K]g` verifies `K`, or some `g` with `f[K']g`
  verifies `K'`.

We define an `Interpretation` as a type of embeddings with its extension relations and the
embeddings verifying each atomic condition. The embeddings verifying a condition or a DRS are
`Condition.verifiers` and `DRS.verifiers`, written `f ⊨[I] γ` and `f ⊨[I] K`, and `DRS.eval` is
the relation `{(f, g) | f[K]g ∧ g ⊨ K}`, in terms of which the three clauses above are
`(dom K)ᶜ`, `core K (dom K')` and `dom K ∪ dom K'`.

The empty DRS denotes the identity, and a merge `K ⊕ K'` denotes the composite of its parts when
extending on `K'` does not change which embeddings verify `K` (`DRS.eval_merge`).

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

/-- An interpretation of DRSs in a type `S` of embeddings: the relation by which an embedding is
extended on a universe of discourse referents, and the embeddings verifying each atomic
condition. -/
structure Interpretation (L : Language.{u, v}) (V : Type w) (S : Type*) [DecidableEq V] where
  /-- `f[U]g`: the embedding `g` extends `f` on the universe `U`. -/
  extend : Finset V → Update S
  /-- The embeddings verifying an atom. -/
  atom : L.Atom V → Set S
  /-- The embeddings verifying an equation between referents. -/
  eq : V → V → Set S
  /-- Extending on the empty universe changes nothing. -/
  extend_empty : extend ∅ = SetRel.id
  /-- Extending on two universes in turn extends on their union. -/
  extend_union (U U' : Finset V) : extend (U ∪ U') = extend U ○ extend U'

mutual
/-- The relation a DRS denotes: `f` is related to `g` when `f[K]g` and `g` verifies `K`. -/
def DRS.eval (I : Interpretation L V S) : DRS L V → Update S
  | ⟨U, cs⟩ => I.extend U ○ test (Condition.verifiersAll I cs)
/-- The embeddings verifying a condition. -/
def Condition.verifiers (I : Interpretation L V S) : Condition L V → Set S
  | .atom a => I.atom a
  | .eq u v => I.eq u v
  | .neg K => (DRS.eval I K).domᶜ
  | .imp a c => (DRS.eval I a).core (DRS.eval I c).dom
  | .dis l r => (DRS.eval I l).dom ∪ (DRS.eval I r).dom
/-- The embeddings verifying every condition of a list. -/
def Condition.verifiersAll (I : Interpretation L V S) : List (Condition L V) → Set S
  | [] => Set.univ
  | c :: cs => Condition.verifiers I c ∩ Condition.verifiersAll I cs
end

/-- The embeddings verifying a DRS: those verifying each of its conditions. -/
def DRS.verifiers (I : Interpretation L V S) (K : DRS L V) : Set S :=
  Condition.verifiersAll I K.conditions

/-- `f ⊨[I] γ`: the embedding `f` verifies the condition `γ`. -/
scoped notation:50 f " ⊨[" I "] " γ:51 => f ∈ Condition.verifiers I γ

/-- `f ⊨[I] K`: the embedding `f` verifies the DRS `K`. -/
scoped notation:50 f " ⊨[" I "] " K:51 => f ∈ DRS.verifiers I K

variable {I : Interpretation L V S} {s t : S}

@[simp] theorem DRS.eval_mk (U : Finset V) (cs : List (Condition L V)) :
    (DRS.mk U cs).eval I = I.extend U ○ test (Condition.verifiersAll I cs) := by
  rw [DRS.eval]

theorem DRS.eval_eq (K : DRS L V) :
    K.eval I = I.extend K.referents ○ test (Condition.verifiersAll I K.conditions) := by
  cases K
  exact DRS.eval_mk ..

theorem Condition.verifiers_atom (a : L.Atom V) : (Condition.atom a).verifiers I = I.atom a := by
  rw [Condition.verifiers]

theorem Condition.verifiers_eq (x y : V) :
    (Condition.eq x y : Condition L V).verifiers I = I.eq x y := by
  rw [Condition.verifiers]

@[simp] theorem Condition.verifiers_neg (K : DRS L V) :
    (Condition.neg K).verifiers I = (K.eval I).domᶜ := by
  rw [Condition.verifiers]

@[simp] theorem Condition.verifiers_imp (a c : DRS L V) :
    (Condition.imp a c).verifiers I = (a.eval I).core (c.eval I).dom := by
  rw [Condition.verifiers]

@[simp] theorem Condition.verifiers_dis (l r : DRS L V) :
    (Condition.dis l r).verifiers I = (l.eval I).dom ∪ (r.eval I).dom := by
  rw [Condition.verifiers]

@[simp] theorem Condition.verifiersAll_nil :
    Condition.verifiersAll I ([] : List (Condition L V)) = Set.univ := by
  rw [Condition.verifiersAll]

@[simp] theorem Condition.verifiersAll_cons (c : Condition L V) (cs : List (Condition L V)) :
    Condition.verifiersAll I (c :: cs) = c.verifiers I ∩ Condition.verifiersAll I cs := by
  rw [Condition.verifiersAll]

theorem Condition.mem_verifiersAll_iff {cs : List (Condition L V)} :
    s ∈ Condition.verifiersAll I cs ↔ ∀ c ∈ cs, s ∈ c.verifiers I := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

@[simp] theorem Condition.verifiersAll_append (cs ds : List (Condition L V)) :
    Condition.verifiersAll I (cs ++ ds) =
      Condition.verifiersAll I cs ∩ Condition.verifiersAll I ds := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih, Set.inter_assoc]

theorem Condition.mem_verifiersAll_cons {c : Condition L V} {cs : List (Condition L V)} :
    s ∈ Condition.verifiersAll I (c :: cs) ↔ s ⊨[I] c ∧ s ∈ Condition.verifiersAll I cs := by
  rw [Condition.verifiersAll_cons, Set.mem_inter_iff]

theorem Condition.mem_verifiers_neg {K : DRS L V} :
    s ⊨[I] Condition.neg K ↔ ¬ ∃ t, s ~[K.eval I] t := by
  rw [Condition.verifiers_neg, Set.mem_compl_iff, mem_dom]

theorem Condition.mem_verifiers_imp {a c : DRS L V} :
    s ⊨[I] Condition.imp a c ↔ ∀ t, s ~[a.eval I] t → ∃ u, t ~[c.eval I] u := by
  rw [Condition.verifiers_imp]
  exact ⟨fun h t ht ↦ h ht, fun h t ht ↦ h t ht⟩

theorem Condition.mem_verifiers_dis {l r : DRS L V} :
    s ⊨[I] Condition.dis l r ↔ (∃ t, s ~[l.eval I] t) ∨ ∃ t, s ~[r.eval I] t := by
  rw [Condition.verifiers_dis, Set.mem_union, mem_dom, mem_dom]

theorem DRS.mem_verifiers_iff {K : DRS L V} : s ⊨[I] K ↔ ∀ γ ∈ K.conditions, s ⊨[I] γ :=
  Condition.mem_verifiersAll_iff

@[simp] theorem DRS.verifiers_empty : (DRS.empty : DRS L V).verifiers I = Set.univ :=
  Condition.verifiersAll_nil

@[simp] theorem DRS.verifiers_merge (K₁ K₂ : DRS L V) :
    (K₁.merge K₂).verifiers I = K₁.verifiers I ∩ K₂.verifiers I :=
  Condition.verifiersAll_append ..

theorem DRS.mem_eval_iff {K : DRS L V} :
    s ~[K.eval I] t ↔ s ~[I.extend K.referents] t ∧ t ⊨[I] K := by
  rw [DRS.eval_eq, Update.mem_comp_test, DRS.verifiers]

@[simp] theorem DRS.eval_empty : (DRS.empty : DRS L V).eval I = SetRel.id := by
  rw [DRS.empty, DRS.eval_mk, I.extend_empty, Condition.verifiersAll_nil, Update.test_univ,
    comp_id]

/-- The Merging Lemma: a merge denotes the composite of its parts when extending on the second
universe does not change which embeddings verify the first DRS. -/
theorem DRS.eval_merge (K₁ K₂ : DRS L V)
    (h : ∀ ⦃s t⦄, s ∈ (I.extend K₁.referents).cod → s ~[I.extend K₂.referents] t →
      (s ⊨[I] K₁ ↔ t ⊨[I] K₁)) :
    (K₁.merge K₂).eval I = K₁.eval I ○ K₂.eval I := by
  ext ⟨s, t⟩
  rw [DRS.mem_eval_iff, DRS.referents_merge, DRS.verifiers_merge,
    I.extend_union]
  constructor
  · rintro ⟨⟨r, hsr, hrt⟩, h₁, h₂⟩
    exact ⟨r, DRS.mem_eval_iff.mpr ⟨hsr, (h ⟨s, hsr⟩ hrt).mpr h₁⟩, DRS.mem_eval_iff.mpr ⟨hrt, h₂⟩⟩
  · rintro ⟨r, hsr, hrt⟩
    obtain ⟨hsr, h₁⟩ := DRS.mem_eval_iff.mp hsr
    obtain ⟨hrt, h₂⟩ := DRS.mem_eval_iff.mp hrt
    exact ⟨⟨r, hsr, hrt⟩, (h ⟨s, hsr⟩ hrt).mp h₁, h₂⟩

end DRT
