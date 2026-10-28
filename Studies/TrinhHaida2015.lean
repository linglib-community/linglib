module

public import Mathlib.Order.BooleanSubalgebra
public import Linglib.Semantics.Alternatives.Structural
public import Studies.FoxKatzir2011
public import Linglib.Data.Examples.TrinhHaida2015

/-!
# Trinh and Haida (2015): Constraining the Derivation of Alternatives

This file formalizes Trinh and Haida's Atomicity constraint and the argument from
symmetry that motivates it. Exhaustification `EXH(A)(S)` negates the innocently excludable
members of a domain `A` of alternatives, (1), the substrate's `exhIE`, and on Fox and Katzir's
theory `A` is the set of relevant members of the formal alternatives `F(S)`, which, relevance
being closed under negation and conjunction, amounts to the conditions (27): `A ⊆ F(S)`,
`S ∈ A`, and no member of `F(S)` outside `A` lies in the Boolean closure of `A`, `IsDomain`.
Two symmetric alternatives, partitioning the prejacent, are then kept or dropped together
whenever both are formal alternatives, `IsDomain.mem_of_isSymmetric`, so a domain holding one
without the other does not exist, `not_isDomain_pair_of_isSymmetric`, and no inference against
either arises. The puzzle, (20) against (21), is that *Bill went for a run and didn't smoke;
John only went for a run* does license the inference that John smoked, although *run and
smoked* is a formal alternative symmetric to the contextual *run and didn't smoke*, while
*Bill ate exactly three cookies; John only ate three* licenses no inference against *exactly
three*. Atomicity, (32), resolves it: expressions in the substitution source are syntactically
atomic, so once a contextual constituent has been substituted in, its parts cannot be
replaced, (33), and *run and smoked* is not derivable, `Subst` and `atoms_mem_source`. With it
gone, `{run, run ∧ ¬smoke}` satisfies (27) whenever running and smoking are independent among
non-runners, `run_smoke_isDomain`, and exhaustification yields *run and smoked*,
`exhIE_run_smoke`; with *four* derived by lexical replacement and equal to *three* without
*exactly three*, `{three, exactly three}` fails (27), the symmetric case.

## Implementation notes

Sentences are propositions `Set W` and the Boolean closure is mathlib's
`BooleanSubalgebra.closure`; membership in it respects any agreement between worlds on the
generators, `mem_iff_of_mem_closure`, which is how (27c) is refuted or established. The
derivation of alternatives is by substitution alone, as the paper takes Fox and Katzir's to
be, of a same-category source expression for a non-atomic constituent, and every substituted
expression enters marked atomic, so an alternative differs from the prejacent by whole source
expressions only; the substitution source, the sets `F(S)` of (35) and (42), and the
independence of the predicates are taken from the paper rather than computed from a lexicon.
The constraints (60b) and (60c) for the switching problem, bottom-up and non-weakening
replacement, and the indirect implicature of (54) are described by the rows. The examples are
the rows of `Data.Examples.TrinhHaida2015`.

## References

* [trinh-haida-2015]
* [fox-katzir-2011]
* [katzir-2007]
* [fox-2007]
* [rooth-1992]
* [kroch-1972]
-/

@[expose] public section

namespace TrinhHaida2015

open Alternatives Exhaustification Set

variable {W : Type*}

/-! ### Conditions on the domain of exhaustification (27) -/

/-- By (27), `A` is a domain of EXH for the prejacent `S` with formal alternatives `F` when it is
a subset of `F` containing `S` and every member of `F` in its Boolean closure. -/
structure IsDomain (F : Set (Set W)) (S : Set W) (A : Set (Set W)) : Prop where
  subset : A ⊆ F
  self_mem : S ∈ A
  closed : ∀ S' ∈ F, S' ∈ BooleanSubalgebra.closure A → S' ∈ A

theorem mem_iff_of_mem_closure {A : Set (Set W)} {p : Set W}
    (hp : p ∈ BooleanSubalgebra.closure A) {w v : W} (h : ∀ a ∈ A, w ∈ a ↔ v ∈ a) :
    w ∈ p ↔ v ∈ p := by
  refine BooleanSubalgebra.closure_bot_sup_induction (p := fun x _ ↦ (w ∈ x ↔ v ∈ x))
    (fun x hx ↦ h x hx) (by simp) (fun x _ y _ hx hy ↦ ?_) (fun x _ hx ↦ ?_) hp
  · show w ∈ x ∪ y ↔ v ∈ x ∪ y
    simp [hx, hy]
  · show w ∈ xᶜ ↔ v ∈ xᶜ
    simp [hx]

theorem notMem_closure_of_separates {A : Set (Set W)} {p : Set W} {w v : W}
    (h : ∀ a ∈ A, w ∈ a ↔ v ∈ a) (hw : w ∈ p) (hv : v ∉ p) :
    p ∉ BooleanSubalgebra.closure A :=
  fun hp ↦ hv ((mem_iff_of_mem_closure hp h).1 hw)

variable {F A : Set (Set W)} {S S₁ S₂ : Set W}

theorem isDomain_self (hS : S ∈ F) : IsDomain F S F := ⟨subset_rfl, hS, fun _ h _ ↦ h⟩

theorem IsDomain.compl_mem (hA : IsDomain F S A) (h₁ : S₁ ∈ A) (h₂ : S₁ᶜ ∈ F) : S₁ᶜ ∈ A :=
  hA.closed _ h₂ (BooleanSubalgebra.compl_mem (BooleanSubalgebra.subset_closure h₁))

theorem IsDomain.mem_of_isSymmetric (hA : IsDomain F S A) (h : IsSymmetric S S₁ S₂)
    (h₁ : S₁ ∈ A) (h₂ : S₂ ∈ F) : S₂ ∈ A :=
  hA.closed S₂ h₂ (h.sdiff_eq ▸ BooleanSubalgebra.sdiff_mem
    (BooleanSubalgebra.subset_closure hA.self_mem) (BooleanSubalgebra.subset_closure h₁))

/-- A domain cannot pair the prejacent with one of two symmetric formal alternatives (27), as in
(43), (46) and (49). -/
theorem not_isDomain_pair_of_isSymmetric (h : IsSymmetric S S₁ S₂) (hne₁ : S₁.Nonempty)
    (h₂ : S₂ ∈ F) : ¬ IsDomain F S {S, S₁} := by
  intro hA
  obtain ⟨a, ha⟩ := hne₁
  rcases hA.mem_of_isSymmetric h (by simp) h₂ with rfl | rfl
  · exact disjoint_left.1 h.disjoint ha (h.subset_left ha)
  · exact disjoint_left.1 h.disjoint ha ha

-- (36)
theorem isDomain_pair (hS : S ∈ F) (h₁ : S₁ ∈ F)
    (h : ∀ S' ∈ F, S' ∈ BooleanSubalgebra.closure {S, S₁} → S' = S ∨ S' = S₁) :
    IsDomain F S {S, S₁} :=
  ⟨by rintro _ (rfl | rfl) <;> assumption, by simp, fun S' hS' hc ↦ by
    rcases h S' hS' hc with rfl | rfl <;> simp⟩

/-! ### Symmetry breaking under Atomicity: run and smoke (section 3.2.2) -/

variable {run smoke : Set W}

/-- With *run ∧ smoke* underivable, `{run, run ∧ ¬smoke}` is a domain for the formal alternatives of
(35)–(36). -/
theorem run_smoke_isDomain {w v : W} (hw : w ∉ run ∧ w ∈ smoke)
    (hv : v ∉ run ∧ v ∉ smoke) :
    IsDomain {run, smoke, smokeᶜ, run ∩ smokeᶜ} run {run, run ∩ smokeᶜ} := by
  have hagree : ∀ a ∈ ({run, run ∩ smokeᶜ} : Set (Set W)), w ∈ a ↔ v ∈ a := by
    rintro _ (rfl | rfl) <;> simp [hw.1, hv.1]
  refine isDomain_pair (by simp) (by simp) ?_
  rintro _ (rfl | rfl | rfl | rfl) hc
  · exact Or.inl rfl
  · exact absurd hc (notMem_closure_of_separates hagree hw.2 hv.2)
  · exact absurd hc (notMem_closure_of_separates (fun a ha ↦ (hagree a ha).symm)
      (mem_compl hv.2) (not_not.2 hw.2))
  · exact Or.inr rfl

/-- The inference of (34) is that exhaustifying *run* against *run ∧ ¬smoke* yields
*run ∧ smoke*, given a world in which someone runs and smokes. -/
theorem exhIE_run_smoke {u : W} (hu : u ∈ run ∧ u ∈ smoke) :
    exhIE {run, run ∩ smokeᶜ} run = run ∩ smoke := by
  rw [exhIE_pair_sdiff (φ := run) (d := run ∩ smokeᶜ) ⟨u, hu.1, fun h ↦ h.2 hu.2⟩]
  ext x
  simp only [mem_sdiff, mem_inter_iff, mem_compl_iff]
  tauto

/-! ### Atomicity (32) -/

section Atomicity

open PhraseStructure

variable {C V : Type}

/-- A tree in the derivation of alternatives is built from the prejacent's own constituents and
the expressions substituted in from the source, which are atomic, their internal structure
inaccessible (32). Binder bodies are opaque as well. -/
inductive ATree (C V : Type) where
  | terminal (c : C) (w : V)
  | node (c : C) (children : List (ATree C V))
  | trace (n : ℕ) (c : C)
  | bind (n : ℕ) (c : C) (body : Tree C V)
  | atomic (c : C) (content : Tree C V)

namespace ATree

/-- The category of the root. -/
def cat : ATree C V → C
  | .terminal c _ | .node c _ | .trace _ c | .bind _ c _ | .atomic c _ => c

/-- The prejacent enters the derivation with no atomic expression, an adjunction structure as a
phrase. -/
def ofTree : Tree C V → ATree C V
  | RoseTree.node (.terminal c w) _ => .terminal c w
  | RoseTree.node (.phrase c _) cs => .node c (ofTreeList cs)
  | RoseTree.node (.trace n c) _ => .trace n c
  | .bind n c body => .bind n c body
  | RoseTree.node (.bind _ c) cs => .node c (ofTreeList cs)
where
  ofTreeList : List (Tree C V) → List (ATree C V)
  | [] => []
  | t :: ts => ofTree t :: ofTreeList ts

/-- The sentence a derivation tree stands for. -/
def expand : ATree C V → Tree C V
  | .terminal c w => .terminal c w
  | .node c cs => .node c (expandList cs)
  | .trace n c => .trace n c
  | .bind n c body => .bind n c body
  | .atomic _ t => t
where
  expandList : List (ATree C V) → List (Tree C V)
  | [] => []
  | t :: ts => expand t :: expandList ts

/-- The atomic expressions of a tree. -/
def atoms : ATree C V → List (Tree C V)
  | .node _ cs => atomsList cs
  | .atomic _ t => [t]
  | _ => []
where
  atomsList : List (ATree C V) → List (Tree C V)
  | [] => []
  | t :: ts => atoms t ++ atomsList ts

/-- By (60a), only a non-atomic expression is replaceable. -/
def Replaceable : ATree C V → Prop
  | .atomic _ _ => False
  | _ => True

mutual

theorem atoms_ofTree : ∀ t : Tree C V, (ofTree t).atoms = []
  | RoseTree.node (.terminal _ _) _ | RoseTree.node (.trace _ _) _ | .bind _ _ _ => rfl
  | RoseTree.node (.phrase _ _) cs => atomsList_ofTreeList cs
  | RoseTree.node (.bind _ _) [] => rfl
  | RoseTree.node (.bind _ _) (c₁ :: c₂ :: cs) => atomsList_ofTreeList (c₁ :: c₂ :: cs)

theorem atomsList_ofTreeList : ∀ cs : List (Tree C V), atoms.atomsList (ofTree.ofTreeList cs) = []
  | [] => rfl
  | t :: ts => by
    rw [ofTree.ofTreeList, atoms.atomsList, atoms_ofTree t, atomsList_ofTreeList ts]
    rfl

end

theorem mem_atomsList_set : ∀ (cs : List (ATree C V)) (i : Fin cs.length) (ψ : ATree C V)
    {a : Tree C V}, a ∈ atoms.atomsList (cs.set i ψ) →
      a ∈ ψ.atoms ∨ a ∈ atoms.atomsList cs
  | _ :: _, ⟨0, _⟩, ψ, a, h => by
    simp only [List.set_cons_zero, atoms.atomsList, List.mem_append] at h ⊢
    tauto
  | _ :: cs, ⟨i + 1, hi⟩, ψ, a, h => by
    simp only [List.set_cons_succ, atoms.atomsList, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · rcases mem_atomsList_set cs ⟨i, by simpa using hi⟩ ψ h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')

theorem mem_atomsList_of_getElem : ∀ (cs : List (ATree C V)) (i : Fin cs.length) {a : Tree C V},
    a ∈ (cs[i]).atoms → a ∈ atoms.atomsList cs
  | _ :: _, ⟨0, _⟩, a, h => by
    simp only [Fin.getElem_fin, List.getElem_cons_zero] at h
    simp only [atoms.atomsList, List.mem_append]
    exact Or.inl h
  | _ :: cs, ⟨i + 1, hi⟩, a, h => by
    simp only [Fin.getElem_fin, List.getElem_cons_succ] at h
    simp only [atoms.atomsList, List.mem_append]
    exact Or.inr (mem_atomsList_of_getElem cs ⟨i, by simpa using hi⟩ h)

end ATree

/-- In one substitution, (13a) under (32), a replaceable constituent is replaced by a
same-category expression of the source, which enters as atomic. Substitution is the only
operation, since [fox-katzir-2011]'s simplification is by substitution alone. -/
inductive Subst (source : List (Tree C V)) : ATree C V → ATree C V → Prop where
  | here {φ : ATree C V} {t : Tree C V} (hr : φ.Replaceable) (hcat : t.cat = φ.cat)
      (ht : t ∈ source) : Subst source φ (.atomic t.cat t)
  | inChild {c : C} {cs : List (ATree C V)} (i : Fin cs.length) {ψ : ATree C V}
      (h : Subst source cs[i] ψ) : Subst source (.node c cs) (.node c (cs.set i ψ))

/-- Derivability by successive substitution. -/
def Derivable (source : List (Tree C V)) : ATree C V → ATree C V → Prop :=
  Relation.ReflTransGen (Subst source)

/-- The formal alternatives of a prejacent under Atomicity are the sentences of the trees
derivable from it. -/
def formalAlternatives (source : List (Tree C V)) (φ : Tree C V) : Set (Tree C V) :=
  {ψ | ∃ t, Derivable source (ATree.ofTree φ) t ∧ t.expand = ψ}

theorem Subst.atoms_mem_source {source : List (Tree C V)} {φ ψ : ATree C V}
    (h : Subst source φ ψ) (hφ : ∀ a ∈ φ.atoms, a ∈ source) :
    ∀ a ∈ ψ.atoms, a ∈ source := by
  induction h with
  | here _ _ ht =>
    intro a ha
    simp only [ATree.atoms, List.mem_singleton] at ha
    exact ha ▸ ht
  | inChild i _ ih =>
    intro a ha
    rcases ATree.mem_atomsList_set _ i _ ha with h' | h'
    · exact ih (fun b hb ↦ hφ b (ATree.mem_atomsList_of_getElem _ i hb)) a h'
    · exact hφ a h'

/-- Every atomic expression of a derivable tree is a source expression, so an alternative differs
from the prejacent by whole source expressions, so the second step of (33), replacing inside
one, is impossible. -/
theorem atoms_mem_source {source : List (Tree C V)} {φ : Tree C V} {t : ATree C V}
    (h : Derivable source (ATree.ofTree φ) t) : ∀ a ∈ t.atoms, a ∈ source := by
  induction h with
  | refl => simp [ATree.atoms_ofTree]
  | tail _ hst ih => exact hst.atoms_mem_source ih

end Atomicity

end TrinhHaida2015
