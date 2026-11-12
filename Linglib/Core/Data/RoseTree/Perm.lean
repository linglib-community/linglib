/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
module

public import Linglib.Core.Data.RoseTree.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Multiset.ZeroCons

/-!
# Permutation of rose trees

`RoseTree.Perm t s` says that `t` and `s` agree up to reordering the children of every node. It is
the counterpart for rose trees of `List.Perm`, and `UnorderedTree` is the quotient by it. Two nodes
are related when their labels are equal and their children, as multisets, are related by
`Multiset.Rel Perm`; this is the only constructor, and reflexivity, symmetry and transitivity are
theorems.

## Main declarations

* `RoseTree.Perm`: the permutation relation.
* `RoseTree.Perm.induction_on`: induction on a proof of `Perm t s`, with the motive available
  on the related children.
* `RoseTree.isSetoid`: the setoid of which `UnorderedTree` is the quotient.
* `RoseTree.fold_rel`: a `fold` whose algebra is congruent along `Multiset.Rel S` carries `Perm`
  to `S`.
* `RoseTree.isPerm_iff`: the Boolean test `RoseTree.isPerm` decides `Perm`. It is a `fold`, so it
  reduces in the kernel and concrete instances of `Perm` close by `decide`.

## Implementation notes

`Perm` is nested through `Multiset.Rel`, so the `induction` tactic does not apply to it and its
recursor has a second motive on `Multiset.Rel Perm`. `Perm.induction_on` packages that motive
once; proofs by induction on `Perm` apply it and never mention the recursor.
-/

@[expose] public section

namespace RoseTree

variable {α β : Type*}

/-- Two rose trees are equal up to reordering the children of every vertex: equal labels over
children that are related as multisets. -/
inductive Perm : RoseTree α → RoseTree α → Prop where
  /-- Equal labels over children related as multisets. -/
  | node {a : α} {cs ds : List (RoseTree α)} :
      Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds → Perm (.node a cs) (.node a ds)

@[inherit_doc] scoped infixl:50 " ~ " => RoseTree.Perm

/-- Two nodes are related exactly when their labels are equal and their children are related by
`Multiset.Rel Perm`. -/
theorem perm_node_iff {a b : α} {cs ds : List (RoseTree α)} :
    Perm (.node a cs) (.node b ds) ↔
      a = b ∧ Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds :=
  ⟨fun | .node h => ⟨rfl, h⟩, fun ⟨hab, h⟩ ↦ hab ▸ .node h⟩

/-- Induction on a proof of `Perm t s`: to prove `motive t s`, prove it for two nodes with the
same label whose children are related, as multisets, by `Perm` and by `motive`. -/
@[elab_as_elim]
theorem Perm.induction_on {motive : RoseTree α → RoseTree α → Prop} {t s : RoseTree α}
    (h : Perm t s)
    (node : ∀ (a : α) (cs ds : List (RoseTree α)),
      Multiset.Rel (fun c d ↦ Perm c d ∧ motive c d) (↑cs : Multiset (RoseTree α)) ↑ds →
        motive (.node a cs) (.node a ds)) : motive t s :=
  Perm.rec (motive_1 := fun t s _ ↦ motive t s)
    (motive_2 := fun F G _ ↦ Multiset.Rel (fun c d ↦ Perm c d ∧ motive c d) F G)
    (fun _ ih ↦ node _ _ _ ih) .zero (fun h _ ih ihs ↦ .cons ⟨h, ih⟩ ihs) h

theorem Perm.value_eq {t s : RoseTree α} : Perm t s → t.value = s.value
  | .node _ => rfl

theorem Perm.children_rel {t s : RoseTree α} :
    Perm t s → Multiset.Rel Perm (↑t.children : Multiset (RoseTree α)) ↑s.children
  | .node h => h

/-! ### Equivalence -/

@[refl] theorem Perm.refl (t : RoseTree α) : Perm t t := by
  induction t with
  | node a cs ih => exact .node (Multiset.rel_refl_of_refl_on ih)

@[symm] theorem Perm.symm {t s : RoseTree α} (h : Perm t s) : Perm s t :=
  h.induction_on fun _ _ _ ih ↦ .node (Multiset.rel_flip.1 (ih.mono fun _ _ _ _ h ↦ h.2))

theorem Perm.trans {t s u : RoseTree α} (h₁ : Perm t s) : Perm s u → Perm t u := by
  refine h₁.induction_on (motive := fun t s ↦ ∀ {u}, Perm s u → Perm t u) fun a cs ds ih u h₂ ↦ ?_
  obtain ⟨b, es⟩ := u
  obtain ⟨rfl, h⟩ := perm_node_iff.1 h₂
  refine .node ?_
  generalize (↑cs : Multiset (RoseTree α)) = F, (↑ds : Multiset (RoseTree α)) = G,
    (↑es : Multiset (RoseTree α)) = H at ih h
  induction ih generalizing H with
  | zero => rw [Multiset.rel_zero_left] at h ⊢; exact h
  | cons hcd _ ih =>
    obtain ⟨e, H', hde, hH, rfl⟩ := Multiset.rel_cons_left.1 h
    exact .cons (hcd.2 hde) (ih _ hH)

instance : Trans (Perm (α := α)) Perm Perm := ⟨.trans⟩

instance : IsEquiv (RoseTree α) Perm where
  refl := .refl
  symm _ _ := .symm
  trans _ _ _ := .trans

protected theorem Perm.eqv : Equivalence (Perm (α := α)) :=
  ⟨.refl, .symm, .trans⟩

/-- The setoid of rose trees up to child reordering; the nonplanar quotient is
taken over it. -/
instance isSetoid : Setoid (RoseTree α) := ⟨Perm, Perm.eqv⟩

theorem Perm.node_of_perm {a : α} {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    Perm (.node a cs) (.node a ds) :=
  .node (Multiset.coe_eq_coe.2 h ▸ Multiset.rel_refl_of_refl_on fun t _ ↦ .refl t)

/-! ### Decidability

`isPerm` is the fold that compares labels and pairs the children greedily, as `List.isPerm` does
for `List.Perm`. A fold recurses structurally, so the instance it gives reduces in the kernel. -/

section Decidable

/-- Greedy pairing of tests with elements: each test of `ps` is paired with the first element of
`ds` still unpaired that passes it, and every test and element must be paired. The match is found
with `findIdx?` and removed with `eraseIdx`, so each test is evaluated once per comparison. -/
def isPermAux : List (β → Bool) → List β → Bool
  | [], ds => ds.isEmpty
  | p :: ps, ds =>
    match ds.findIdx? p with
    | some i => isPermAux ps (ds.eraseIdx i)
    | none => false

private theorem rel_perm_iff {F G : Multiset (RoseTree α)} :
    Multiset.Rel Perm F G ↔ F.map (Quotient.mk isSetoid) = G.map (Quotient.mk isSetoid) := by
  rw [← Multiset.rel_eq, Multiset.rel_map]
  simp only [Quotient.eq]
  exact Iff.rfl

/-- Greedy pairing decides `Multiset.Rel Perm` once the tests decide `Perm` on the members of the
two lists, which is what the induction hypothesis of `isPerm_iff` provides. -/
private theorem isPermAux_iff {r : RoseTree α → RoseTree α → Bool} :
    ∀ {cs ds : List (RoseTree α)}, (∀ c ∈ cs, ∀ d ∈ ds, r c d ↔ Perm c d) →
      (isPermAux (cs.map r) ds ↔ Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds)
  | [], ds, _ => by
    rw [List.map_nil, isPermAux, List.isEmpty_iff, Multiset.coe_nil, Multiset.rel_zero_left,
      Multiset.coe_eq_zero]
  | c :: cs, ds, h => by
    rw [List.map_cons, isPermAux]
    split
    · next i hi =>
      obtain ⟨hil, hci, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
      have hcd := (h c List.mem_cons_self _ (List.getElem_mem hil)).1 hci
      rw [isPermAux_iff fun x hx y hy ↦
          h x (List.mem_cons_of_mem _ hx) y ((List.eraseIdx_sublist _ _).subset hy),
        ← Multiset.coe_eq_coe.2 (List.getElem_cons_eraseIdx_perm hil), ← Multiset.cons_coe,
        ← Multiset.cons_coe, rel_perm_iff, rel_perm_iff, Multiset.map_cons, Multiset.map_cons,
        Quotient.sound hcd, Multiset.cons_inj_right]
    · next hi =>
      refine iff_of_false Bool.false_ne_true fun hr ↦ ?_
      obtain ⟨d, G, hcd, -, he⟩ := Multiset.rel_cons_left.1 (Multiset.cons_coe c cs ▸ hr)
      have hd : d ∈ ds := Multiset.mem_coe.1 (he ▸ Multiset.mem_cons_self d G)
      simpa [(h c List.mem_cons_self d hd).2 hcd] using List.findIdx?_eq_none_iff.1 hi d hd

variable [DecidableEq α] {t s : RoseTree α}

/-- `isPerm t s` tests whether `t` and `s` are equal up to reordering the children of every
vertex. -/
def isPerm (t : RoseTree α) : RoseTree α → Bool :=
  t.fold fun a ps s ↦ decide (a = s.value) && isPermAux ps s.children

theorem isPerm_node (a b : α) (cs ds : List (RoseTree α)) :
    isPerm (node a cs) (node b ds) = (decide (a = b) && isPermAux (cs.map isPerm) ds) := by
  rw [isPerm, fold_node]; rfl

theorem isPerm_iff : isPerm t s ↔ Perm t s := by
  induction t generalizing s with
  | node a cs ih =>
    obtain ⟨b, ds⟩ := s
    rw [isPerm_node, Bool.and_eq_true, decide_eq_true_eq, perm_node_iff,
      isPermAux_iff fun c hc _ _ ↦ ih c hc]

instance decidablePerm : DecidableRel (Perm (α := α)) :=
  fun _ _ ↦ decidable_of_iff _ isPerm_iff

instance : DecidableRel ((· ≈ ·) : RoseTree α → RoseTree α → Prop) :=
  decidablePerm

end Decidable

/-! ### Functoriality -/

/-- `RoseTree.map` preserves `Perm` (cf. `List.Perm.map`). -/
theorem Perm.map (f : α → β) {t s : RoseTree α} (h : Perm t s) : Perm (t.map f) (s.map f) := by
  refine h.induction_on fun a cs ds ih ↦ ?_
  rw [map_node, map_node]
  refine .node ?_
  rw [← Multiset.map_coe, ← Multiset.map_coe, Multiset.rel_map]
  exact ih.mono fun _ _ _ _ h ↦ h.2

/-! ### Fold invariance

A `fold` whose algebra is congruent along `Multiset.Rel S` of the folded children
carries `Perm` to `S` (`fold_rel`): the generic dissolver of per-function invariance
inductions, relational so that tree-valued folds descend too. `fold_perm` is the
`S := Eq` case; the counts below are such folds. -/

theorem fold_rel {S : β → β → Prop} {g : α → List β → β}
    (hg : ∀ (a : α) {l₁ l₂ : List β}, Multiset.Rel S ↑l₁ ↑l₂ → S (g a l₁) (g a l₂))
    {t s : RoseTree α} (h : Perm t s) : S (fold g t) (fold g s) := by
  refine h.induction_on fun a cs ds ih ↦ ?_
  rw [fold_node, fold_node]
  refine hg a ?_
  rw [← Multiset.map_coe, ← Multiset.map_coe, Multiset.rel_map]
  exact ih.mono fun _ _ _ _ h ↦ h.2

theorem fold_perm {g : α → List β → β}
    (hg : ∀ (a : α) (l₁ l₂ : List β), l₁.Perm l₂ → g a l₁ = g a l₂) :
    ∀ {t s : RoseTree α}, Perm t s → fold g t = fold g s :=
  fold_rel fun a {l₁ l₂} h ↦ hg a l₁ l₂ (Multiset.coe_eq_coe.mp (Multiset.rel_eq.mp h))

theorem numNodes_perm {t s : RoseTree α} (h : Perm t s) : t.numNodes = s.numNodes :=
  fold_perm (fun _ _ _ h' ↦ congrArg (· + 1) h'.sum_eq) h

private theorem flatten_perm_of_rel : ∀ {l₁ l₂ : List (List β)},
    Multiset.Rel List.Perm (↑l₁ : Multiset (List β)) ↑l₂ → l₁.flatten.Perm l₂.flatten
  | [], l₂, h => by
    rw [Multiset.coe_nil, Multiset.rel_zero_left, Multiset.coe_eq_zero] at h
    rw [h]
  | x :: xs, l₂, h => by
    obtain ⟨y, G, hxy, hG, he⟩ := Multiset.rel_cons_left.1 (Multiset.cons_coe x xs ▸ h)
    induction G using Quot.inductionOn with
    | h ys =>
      exact ((hxy.append (flatten_perm_of_rel hG)).trans (List.flatten_cons ▸ .refl _)).trans
        (Multiset.coe_eq_coe.1 he).flatten.symm

/-- Reordering children permutes the frontier. -/
theorem Perm.leafList_perm {t s : RoseTree α} (h : Perm t s) : t.leafList.Perm s.leafList := by
  refine fold_rel (S := List.Perm) (fun a {l₁ l₂} h' ↦ ?_) h
  have hc := Multiset.card_eq_card_of_rel h'
  rcases l₁ with _ | ⟨x, xs⟩ <;> rcases l₂ with _ | ⟨y, ys⟩
  · rfl
  · simp at hc
  · simp at hc
  · exact flatten_perm_of_rel h'

theorem numLeaves_perm {t s : RoseTree α} (h : Perm t s) : t.numLeaves = s.numLeaves :=
  h.leafList_perm.length_eq

theorem height_perm {t s : RoseTree α} (h : Perm t s) : t.height = s.height :=
  fold_perm (fun _ _ _ h' ↦ congrArg (· + 1) (h'.foldr_eq 0)) h

theorem arity_perm {t s : RoseTree α} (h : Perm t s) : t.arity = s.arity := by
  simpa [arity] using Multiset.card_eq_card_of_rel h.children_rel

end RoseTree
