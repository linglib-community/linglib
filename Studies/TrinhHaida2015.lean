module

public import Mathlib.Order.BooleanSubalgebra
public import Studies.FoxKatzir2011
public import Linglib.Syntax.Cat
public import Linglib.Syntax.Tree.Basic
public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Data.Examples.TrinhHaida2015

/-!
# Trinh and Haida (2015): Constraining the Derivation of Alternatives

This file formalizes Trinh and Haida's Atomicity constraint on the derivation of formal
alternatives and the argument from symmetry that motivates it. Exhaustification negates the
innocently excludable members of a domain `A`, which on Fox and Katzir's theory is the set of
relevant formal alternatives; relevance being closed under negation and conjunction, [such a
restriction is a set satisfying the three conditions](##isDomain_iff_exists) of `IsDomain`. A
domain holding one of two symmetric alternatives holds the other whenever it is a formal
alternative, so [no inference against either arises](##IsDomain.not_isInnocentlyExcludable).
The puzzle is that *Bill went for a run and didn't smoke; John only went for a run* does license
the inference that John smoked, although successive substitution [derives the symmetric *run and
smoked*](##ranAndSmoked_mem_substitutionAlternatives), while *Bill ate exactly three cookies;
John only ate three* licenses no inference against *exactly three*. Atomicity resolves it:
expressions of the substitution source are syntactically atomic, so a derivation [replaces
disjoint constituents of the prejacent by whole source expressions](##mem_formalAlternatives_node)
and [*run and smoked* is not derivable](##notMem_formalAlternatives_run). With it gone,
[`{run, run ∧ ¬smoke}` is a domain](##run_smoke_isDomain) whenever running and smoking are
independent among non-runners, and [exhaustification yields *run and
smoked*](##exhIE_run_smoke); *four*, a lexical replacement, stays derivable, so [the domain
`{three, exactly three}` does not exist](##not_isDomain_pair_of_isSymmetric). The same reasoning
[removes the symmetric counterpart of *not some*](##formalAlternatives_pass) from the
alternatives of *not all*.

## Implementation notes

* Sentences are propositions `Set W` in the conditions on domains, and labelled trees in the
  derivations. The sets of formal alternatives over which `run_smoke_isDomain` is stated are the
  paper's, as propositions; the trees are not interpreted.
* Substitution is [fox-katzir-2011]'s, `Tree.Substitutes`: it replaces a constituent
  by any expression of the source, of whatever category, as the paper's derivations do in
  replacing a NegP by a VP.
* A tree in a derivation under Atomicity carries each substituted expression as a leaf, so
  that nothing inside it can be replaced; [Atomicity only removes
  alternatives](##formalAlternatives_subset).
* The substitution sources are `FoxKatzir2011.contextualSource`, the constituents of the
  context sentence entering as the salient ones. The verb phrases of the first pair of trees are
  unanalysed, as in the paper's, and the lexicon of its source is empty; the conjunction is a
  daughter of the coordination.

## TODO

* The constraints on the switching problem, bottom-up and non-weakening replacement, are not
  formalized; the rows describe their examples.
* The multiple-disjunction alternatives, derivable under Atomicity in two steps, are not
  worked out.

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

open Alternatives Exhaustification PhraseStructure Set

variable {W : Type*}

/-! ### Conditions on the domain of exhaustification (27) -/

/-- By (27), `A` is a domain of EXH for the prejacent `S` with formal alternatives `F` when it is
a subset of `F` containing `S` and every member of `F` in its Boolean closure. -/
structure IsDomain (F : Set (Set W)) (S : Set W) (A : Set (Set W)) : Prop where
  subset : A ⊆ F
  self_mem : S ∈ A
  closed : ∀ S' ∈ F, S' ∈ BooleanSubalgebra.closure A → S' ∈ A

variable {F A : Set (Set W)} {S S₁ S₂ : Set W}

theorem isDomain_self (hS : S ∈ F) : IsDomain F S F := ⟨subset_rfl, hS, fun _ h _ ↦ h⟩

theorem isDomain_inter (C : BooleanSubalgebra (Set W)) (hS : S ∈ F) (hC : S ∈ C) :
    IsDomain F S (F ∩ C) :=
  ⟨inter_subset_left, ⟨hS, hC⟩, fun _ hS' hc ↦
    ⟨hS', BooleanSubalgebra.closure_le.2 inter_subset_right hc⟩⟩

theorem IsDomain.inter_closure (hA : IsDomain F S A) : F ∩ BooleanSubalgebra.closure A = A :=
  Subset.antisymm (fun S' h ↦ hA.closed S' h.1 h.2) fun _ h ↦
    ⟨hA.subset h, BooleanSubalgebra.subset_closure h⟩

-- (27)
theorem isDomain_iff_exists (hS : S ∈ F) :
    IsDomain F S A ↔ ∃ C : BooleanSubalgebra (Set W), S ∈ C ∧ F ∩ C = A :=
  ⟨fun hA ↦ ⟨_, BooleanSubalgebra.subset_closure hA.self_mem, hA.inter_closure⟩, by
    rintro ⟨C, hC, rfl⟩
    exact isDomain_inter C hS hC⟩

theorem IsDomain.compl_mem (hA : IsDomain F S A) (h₁ : S₁ ∈ A) (h₂ : S₁ᶜ ∈ F) : S₁ᶜ ∈ A :=
  hA.closed _ h₂ (BooleanSubalgebra.compl_mem (BooleanSubalgebra.subset_closure h₁))

theorem IsDomain.mem_of_isSymmetric (hA : IsDomain F S A) (h : IsSymmetric S S₁ S₂)
    (h₁ : S₁ ∈ A) (h₂ : S₂ ∈ F) : S₂ ∈ A :=
  hA.closed S₂ h₂ (h.mem_of_mem (BooleanSubalgebra.subset_closure hA.self_mem)
    (BooleanSubalgebra.subset_closure h₁))

/-- No domain licenses the inference against one of two symmetric formal alternatives, as with
*exactly three* in (41), *children and no twins* in (44) and *passed some and failed some* in
(47). -/
theorem IsDomain.not_isInnocentlyExcludable (hA : IsDomain F S A) (hfin : A.Finite)
    (h : IsSymmetric S S₁ S₂) (h₁ : S₁ ∈ A) (h₂ : S₂ ∈ F) (hne : S₁.Nonempty) :
    ¬ IsInnocentlyExcludable A S S₁ :=
  not_isInnocentlyExcludable_of_subset_union _ _ hfin h₁ (hA.mem_of_isSymmetric h h₁ h₂)
    h.union.symm.subset (h.symm.sdiff_eq.symm ▸ hne)

-- (43), (46)
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

section RunSmoke

variable {run smoke : Set W}

/-- With *run ∧ smoke* underivable, `{run, run ∧ ¬smoke}` is a domain for the formal alternatives
(35), as (36) says. -/
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

/-- Exhaustifying *run* against *run ∧ ¬smoke* yields *run ∧ smoke*, the inference of (34), given
a world in which someone runs and smokes. -/
theorem exhIE_run_smoke {u : W} (hu : u ∈ run ∧ u ∈ smoke) :
    exhIE {run, run ∩ smokeᶜ} run = run ∩ smoke := by
  rw [exhIE_pair_sdiff (φ := run) (d := run ∩ smokeᶜ) ⟨u, hu.1, fun h ↦ h.2 hu.2⟩]
  ext x
  simp only [mem_sdiff, mem_inter_iff, mem_compl_iff]
  tauto

end RunSmoke

/-! ### Atomicity (32)

A tree in a derivation under Atomicity is a `RoseTree (α ⊕ RoseTree α)`: a node labelled `.inl a`
is a node of the prejacent, and a leaf labelled `.inr s` is the source expression `s` marked AT,
its internal structure invisible. -/

section Substitution

variable {α : Type*}

private theorem forall₂_append_cons_tail {α : Type*} {r : α → α → Prop} {c c' : α} (hc : r c c') :
    ∀ {l₁ l₂ ms : List α}, List.Forall₂ (Relation.ReflTransGen r) ms (l₁ ++ c :: l₂) →
      List.Forall₂ (Relation.ReflTransGen r) ms (l₁ ++ c' :: l₂)
  | [], _, _, h => by
    obtain ⟨d, k, hd, hk, rfl⟩ := List.forall₂_cons_right_iff.1 h
    exact .cons (hd.tail hc) hk
  | _ :: _, _, _, h => by
    obtain ⟨d, k, hd, hk, rfl⟩ := List.forall₂_cons_right_iff.1 h
    exact .cons hd (forall₂_append_cons_tail hc hk)

variable {source : Set (RoseTree α)}

/-- The sentence a tree with AT-marked expressions stands for. -/
def expand : RoseTree (α ⊕ RoseTree α) → RoseTree α :=
  RoseTree.fold fun x cs ↦ x.elim (fun a ↦ .node a cs) id

@[simp] theorem expand_node_inl (a : α) (ms : List (RoseTree (α ⊕ RoseTree α))) :
    expand (.node (.inl a) ms) = .node a (ms.map expand) := by
  simp [expand]

@[simp] theorem expand_node_inr (s : RoseTree α) (ms : List (RoseTree (α ⊕ RoseTree α))) :
    expand (.node (.inr s) ms) = s := by
  simp [expand]

@[simp] theorem expand_map_inl (t : RoseTree α) : expand (t.map .inl) = t := by
  induction t with
  | node a cs ih =>
    rw [RoseTree.map_node, expand_node_inl, List.map_map,
      List.map_congr_left (f := expand ∘ RoseTree.map .inl) (g := id) ih, List.map_id]

/-- One substitution under Atomicity replaces an expression that is not AT-marked, (60a), with an
expression of the source, which enters AT-marked. -/
def SubstitutesAtomic (source : Set (RoseTree α)) :
    RoseTree (α ⊕ RoseTree α) → RoseTree (α ⊕ RoseTree α) → Prop :=
  RoseTree.Rewrites fun x y ↦ x.value.isLeft ∧ ∃ s ∈ source, y = .leaf (.inr s)

/-- The formal alternatives of `φ` under Atomicity are the sentences of the trees derived from it
by successive substitutions, none inside an AT-marked expression. -/
def formalAlternatives (source : Set (RoseTree α)) (φ : RoseTree α) : Set (RoseTree α) :=
  expand '' {m | Relation.ReflTransGen (SubstitutesAtomic source) (φ.map .inl) m}

theorem not_substitutesAtomic_leaf_inr {s : RoseTree α} {m : RoseTree (α ⊕ RoseTree α)} :
    ¬ SubstitutesAtomic source (.leaf (.inr s)) m := by
  intro h
  generalize hx : RoseTree.leaf (Sum.inr s) = x at h
  cases h with
  | here h => subst hx; simp at h
  | child => simp at hx

theorem reflTransGen_substitutesAtomic_node {a : α} {ms : List (RoseTree (α ⊕ RoseTree α))}
    {m : RoseTree (α ⊕ RoseTree α)} :
    Relation.ReflTransGen (SubstitutesAtomic source) (.node (.inl a) ms) m ↔
      (∃ s ∈ source, m = .leaf (.inr s)) ∨
      ∃ ms', List.Forall₂ (Relation.ReflTransGen (SubstitutesAtomic source)) ms ms' ∧
        m = .node (.inl a) ms' := by
  constructor
  · intro h
    induction h with
    | refl => exact .inr ⟨ms, List.forall₂_same.2 fun _ _ ↦ .refl, rfl⟩
    | tail _ hstep ih =>
      rcases ih with ⟨s, -, rfl⟩ | ⟨ms', hms', rfl⟩
      · exact absurd hstep not_substitutesAtomic_leaf_inr
      · generalize hx : RoseTree.node (Sum.inl a) ms' = x at hstep
        cases hstep with
        | here h => exact .inl h.2
        | child b l₁ l₂ hc =>
          obtain ⟨rfl, rfl⟩ := RoseTree.node.inj hx
          exact .inr ⟨_, forall₂_append_cons_tail hc hms', rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨ms', h, rfl⟩)
    · exact .single (.here ⟨rfl, s, hs, rfl⟩)
    · exact RoseTree.reflTransGen_rewrites_node (.inl a) [] h

/-- Under Atomicity an alternative of a tree is an expression of the source or the tree's own
root over alternatives of its daughters: a derivation amounts to one replacement of disjoint
constituents, so a replacement cannot feed another, as the second step of (33) would. -/
theorem mem_formalAlternatives_node {a : α} {cs : List (RoseTree α)} {ψ : RoseTree α} :
    ψ ∈ formalAlternatives source (.node a cs) ↔ ψ ∈ source ∨
      ∃ cs', List.Forall₂ (fun c c' ↦ c' ∈ formalAlternatives source c) cs cs' ∧
        ψ = .node a cs' := by
  simp only [formalAlternatives, mem_image, mem_ofPred_eq, RoseTree.map_node,
    reflTransGen_substitutesAtomic_node]
  constructor
  · rintro ⟨m, ⟨s, hs, rfl⟩ | ⟨ms', h, rfl⟩, rfl⟩
    · exact .inl (by simpa using hs)
    · refine .inr ⟨ms'.map expand, ?_, by simp⟩
      rw [List.forall₂_map_left_iff] at h
      rw [List.forall₂_map_right_iff]
      exact h.imp fun c m hm ↦ ⟨m, hm, rfl⟩
  · rintro (hs | ⟨cs', h, rfl⟩)
    · exact ⟨.leaf (.inr ψ), .inl ⟨ψ, hs, rfl⟩, by simp⟩
    · obtain ⟨ms', hms', rfl⟩ : ∃ ms', List.Forall₂ (Relation.ReflTransGen
          (SubstitutesAtomic source)) (cs.map (RoseTree.map .inl)) ms' ∧ ms'.map expand = cs' := by
        induction h with
        | nil => exact ⟨[], .nil, rfl⟩
        | cons hc _ ih =>
          obtain ⟨m, hm, rfl⟩ := hc
          obtain ⟨ms, hms, rfl⟩ := ih
          exact ⟨m :: ms, .cons hm hms, rfl⟩
      exact ⟨_, .inr ⟨ms', hms', rfl⟩, by simp⟩

theorem self_mem_formalAlternatives (φ : RoseTree α) : φ ∈ formalAlternatives source φ :=
  ⟨_, .refl, expand_map_inl φ⟩

theorem subset_formalAlternatives (φ : RoseTree α) : source ⊆ formalAlternatives source φ := by
  obtain ⟨a, cs⟩ := φ
  exact fun ψ hψ ↦ mem_formalAlternatives_node.2 (.inl hψ)

private theorem SubstitutesAtomic.expand {m m' : RoseTree (α ⊕ RoseTree α)}
    (h : SubstitutesAtomic source m m') :
    Relation.ReflTransGen (Tree.Substitutes source) (expand m) (expand m') := by
  induction h with
  | here h =>
    obtain ⟨-, s, hs, rfl⟩ := h
    exact .single (.here (by simpa using hs))
  | child a l₁ l₂ _ ih =>
    cases a with
    | inl a =>
      simp only [expand_node_inl, List.map_append, List.map_cons]
      exact ih.lift (fun x ↦ RoseTree.node a (l₁.map TrinhHaida2015.expand ++ x ::
        l₂.map TrinhHaida2015.expand)) fun _ _ hx ↦ .child a _ _ hx
    | inr s => rw [expand_node_inr, expand_node_inr]

theorem formalAlternatives_subset (φ : RoseTree α) :
    formalAlternatives source φ ⊆ Tree.substitutionAlternatives source φ := by
  rintro _ ⟨m, hm, rfl⟩
  have h : Relation.ReflTransGen (Tree.Substitutes source) (expand (φ.map .inl))
      (expand m) :=
    Relation.ReflTransGen.lift' expand (fun _ _ ↦ SubstitutesAtomic.expand) _ _ hm
  rwa [expand_map_inl] at h

end Substitution

/-! ### The derivations (31), (33) and (55) -/

section Derivations

/-- The words of (28) and (54), with the verb phrases of (28) unanalysed as in the paper's
trees. -/
inductive Word
  | bill | john | past | goForARun | and_ | not_ | smoke | committee | pass | all | some | students
  deriving DecidableEq

/-- *go for a run*, a VP. -/
def goForARun : Tree Cat Word := .terminal .V .goForARun

/-- *smoke*, the VP `β` of (31). -/
def smoke : Tree Cat Word := .terminal .V .smoke

/-- The T′ over a predicate. -/
def tense (p : Tree Cat Word) : Tree Cat Word := .node .Aux [.terminal .Aux .past, p]

/-- The NegP over a predicate. -/
def neg (p : Tree Cat Word) : Tree Cat Word := .node .Neg [.terminal .Neg .not_, p]

/-- The coordination of two T′s. -/
def conj (p q : Tree Cat Word) : Tree Cat Word := .node .Aux [p, .terminal .Conj .and_, q]

/-- The clause with subject `subj` over a T′. -/
def clause (subj : Word) (p : Tree Cat Word) : Tree Cat Word := .node .Aux [.terminal .N subj, p]

/-- *went for a run and didn't smoke*, the T′ `α` of (31). -/
def ranAndDidntSmoke : Tree Cat Word := conj (tense goForARun) (tense (neg smoke))

/-- The substitution source of (28) holds the constituents of *Bill went for a run and didn't
smoke* and of the prejacent *John went for a run*. -/
abbrev runSource : Set (Tree Cat Word) :=
  FoxKatzir2011.contextualSource ∅ (clause .john (tense goForARun))
    (clause .bill ranAndDidntSmoke).subtrees.toFinset

theorem clause_mem_formalAlternatives {source : Set (Tree Cat Word)} {subj : Word}
    {p q : Tree Cat Word} (h : q ∈ formalAlternatives source p) :
    clause subj q ∈ formalAlternatives source (clause subj p) :=
  mem_formalAlternatives_node.2
    (.inr ⟨_, .cons (self_mem_formalAlternatives _) (.cons h .nil), rfl⟩)

theorem tense_mem_formalAlternatives {source : Set (Tree Cat Word)} {p q : Tree Cat Word}
    (h : q ∈ formalAlternatives source p) :
    tense q ∈ formalAlternatives source (tense p) :=
  mem_formalAlternatives_node.2
    (.inr ⟨_, .cons (self_mem_formalAlternatives _) (.cons h .nil), rfl⟩)

-- (31): the T′ `α` replaces the prejacent's T′, then the VP `β` replaces the NegP inside it
theorem ranAndSmoked_mem_substitutionAlternatives :
    clause .john (conj (tense goForARun) (tense smoke)) ∈
      Tree.substitutionAlternatives runSource (clause .john (tense goForARun)) := by
  have h₁ : Tree.Substitutes runSource (clause .john (tense goForARun))
      (clause .john ranAndDidntSmoke) :=
    .child _ [_] [] (.here (by decide))
  have h₂ : Tree.Substitutes runSource (clause .john ranAndDidntSmoke)
      (clause .john (conj (tense goForARun) (tense smoke))) :=
    .child _ [_] [] (.child _ [_, _] [] (.child _ [_] [] (.here (by decide))))
  exact .tail (.single h₁) h₂

-- (35): *run ∧ ¬smoke*, *smoke* and *¬smoke* remain formal alternatives under Atomicity
theorem mem_formalAlternatives_run :
    clause .john ranAndDidntSmoke ∈
      formalAlternatives runSource (clause .john (tense goForARun)) ∧
    clause .john (tense smoke) ∈ formalAlternatives runSource (clause .john (tense goForARun)) ∧
    clause .john (tense (neg smoke)) ∈
      formalAlternatives runSource (clause .john (tense goForARun)) :=
  ⟨clause_mem_formalAlternatives (subset_formalAlternatives _ (by decide)),
    clause_mem_formalAlternatives
      (tense_mem_formalAlternatives (subset_formalAlternatives _ (by decide))),
    clause_mem_formalAlternatives (subset_formalAlternatives _ (by decide))⟩

/-- *John went for a run and smoked* is not a formal alternative of *John went for a run* under
Atomicity, the second step of (33) being barred, and neither is *John didn't go for a run*. -/
theorem notMem_formalAlternatives_run :
    clause .john (conj (tense goForARun) (tense smoke)) ∉
      formalAlternatives runSource (clause .john (tense goForARun)) ∧
    clause .john (tense (neg goForARun)) ∉
      formalAlternatives runSource (clause .john (tense goForARun)) := by
  constructor <;>
    simp [clause, conj, tense, neg, goForARun, smoke, ranAndDidntSmoke,
      FoxKatzir2011.contextualSource, Tree.substitutionSource,
      mem_formalAlternatives_node]

/-- The VP *the committee pass `q` of my students* of (55). -/
def pass (q : Word) : Tree Cat Word :=
  .node .V [.terminal .N .committee, .terminal .V .pass, .terminal .Det q, .terminal .N .students]

/-- The substitution source of (54) holds the scalar items and the constituents of the
prejacent (55), *the committee didn't pass all of my students*. -/
abbrev passSource : Set (Tree Cat Word) :=
  FoxKatzir2011.contextualSource {.terminal .Det .some, .terminal .Det .all}
    (tense (neg (pass .all))) ∅

-- (55): replacing NegP with VP and then *all* with *some* derives *passed some*
theorem passedSome_mem_substitutionAlternatives :
    tense (pass .some) ∈
      Tree.substitutionAlternatives passSource (tense (neg (pass .all))) := by
  have h₁ : Tree.Substitutes passSource (tense (neg (pass .all))) (tense (pass .all)) :=
    .child _ [_] [] (.here (by decide))
  have h₂ : Tree.Substitutes passSource (tense (pass .all)) (tense (pass .some)) :=
    .child _ [_] [] (.child _ [_, _] [_] (.here (by decide)))
  exact .tail (.single h₁) h₂

-- (54)
theorem formalAlternatives_pass :
    tense (neg (pass .some)) ∈ formalAlternatives passSource (tense (neg (pass .all))) ∧
    tense (pass .some) ∉ formalAlternatives passSource (tense (neg (pass .all))) := by
  refine ⟨tense_mem_formalAlternatives (mem_formalAlternatives_node.2 (.inr ⟨_, .cons
    (self_mem_formalAlternatives _) (.cons (mem_formalAlternatives_node.2 (.inr ⟨_, .cons
      (self_mem_formalAlternatives _) (.cons (self_mem_formalAlternatives _) (.cons
        (subset_formalAlternatives _ (by decide)) (.cons (self_mem_formalAlternatives _) .nil))),
      rfl⟩)) .nil), rfl⟩)), ?_⟩
  simp [tense, neg, pass, FoxKatzir2011.contextualSource, Tree.substitutionSource,
    mem_formalAlternatives_node]

end Derivations

end TrinhHaida2015
