/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.InductiveInference
public import Linglib.Core.Computability.LocallyTestable
public import Linglib.Core.Computability.PiecewiseTestable
public import Linglib.Phonology.Subregular.StrictlyLocal
public import Linglib.Phonology.Subregular.StrictlyPiecewise
public import Mathlib.Data.List.ReduceOption
public import Mathlib.Data.Multiset.Lattice

/-!
# Heinz, Kasprzik and Kötzing (2012): Learning in the limit with lattice-structured
hypothesis spaces

A lattice space maps each word to a node of an upper semilattice, every node being the join of the
nodes of finitely many words, and the language of a node is the words mapped at or below it. The
lattice learner keeps the join of the nodes it has seen, and so
[identifies every language of the class in the limit](##identifies_language). A class is a lattice
class [exactly when each finite set of words has a least language containing it and each language is
the least containing some finite set](##isLatticeClass_iff). The paper's subregular classes are
instances, on finite grammars: strictly local languages with arbitrary grammars are
[identifiable exactly when the alphabet is finite](##identifiable_isStrictlyLocal_iff), and the
width has to be given in advance, since [those strictly local at some width are not
identifiable](##not_identifiable_exists_isStrictlyLocal). Contrary to the paper,
[the elementwise intersections of two lattice classes need not be
identifiable](##not_identifiable_inter); they form a lattice class
[when no node has an infinite ascending chain below it](##isLatticeClass_inter).

## Implementation notes

The paper requires `f` and `⊔` to be computable and learners to be computable functions; here they
are arbitrary, so the results are those of ineffective identification. A learner conjectures a
language rather than an index, so the paper's condition that the indexing be one-to-one disappears.
A lattice space has a least element: the paper's learner needs one on the empty sample, and its
Theorem 4.7(iii) asks for a least language containing the empty set. The words form an arbitrary
type `W`, of which the paper's `Σ*` is an instance.

## TODO

The pattern languages, monomials and function-distinguishable classes of §5, the query complexity
of §6 and the VC-dimension characterization of §7 are not formalized.

## References

* [heinz-kasprzik-kotzing-2012]
* [gold-1967]
* [angluin-1980]
-/

@[expose] public section

namespace HeinzKasprzikKotzing2012

open InductiveInference Set Filter

universe u

variable {W : Type u}

/-! ### Lattice spaces and the lattice learner -/

section LatticeSpace

variable {V : Type*} [SemilatticeSup V] [OrderBot V] (f : W → V)

/-- `f` maps words to the nodes of a **lattice space** when every node is the join of the nodes of
finitely many words. -/
def IsLatticeSpace : Prop := ∀ v, ∃ D : Finset W, D.sup f = v

/-- The language of a grammar `v` consists of the words mapped at or below it. -/
def language (v : V) : Set W := {x | f x ≤ v}

/-- The lattice learner's grammar: the join of the nodes of the words seen so far. -/
def conjecture (σ : List (Option W)) : V := ((σ.reduceOption : Multiset W).map f).sup

/-- The lattice learner conjectures the language of the join of the nodes it has seen. -/
def learner : Learner W := fun σ ↦ language f (conjecture f σ)

variable {f}

omit [OrderBot V] in
@[simp] theorem mem_language {v : V} {x : W} : x ∈ language f v ↔ f x ≤ v := Iff.rfl

omit [OrderBot V] in
theorem language_mono : Monotone (language f) := fun _ _ hab _ hx ↦ le_trans hx hab

theorem conjecture_le_iff {σ : List (Option W)} {v : V} :
    conjecture f σ ≤ v ↔ content σ ⊆ language f v := by
  rw [conjecture, Multiset.sup_le]
  simp only [Multiset.mem_map, Multiset.mem_coe, List.reduceOption_mem_iff]
  exact ⟨fun h x hx ↦ h _ ⟨x, hx, rfl⟩, by rintro h _ ⟨x, hx, rfl⟩; exact h hx⟩

theorem conjecture_le_of_content_subset {σ τ : List (Option W)} (h : content σ ⊆ content τ) :
    conjecture f σ ≤ conjecture f τ :=
  conjecture_le_iff.mpr (h.trans (conjecture_le_iff.mp le_rfl))

theorem finset_sup_le_conjecture {D : Finset W} {σ : List (Option W)} (h : ↑D ⊆ content σ) :
    D.sup f ≤ conjecture f σ :=
  Finset.sup_le fun _ hx ↦ conjecture_le_iff.mp le_rfl (h hx)

theorem subset_language_finset_sup (D : Finset W) : ↑D ⊆ language f (D.sup f) :=
  fun _ hx ↦ Finset.le_sup hx

theorem identifies_language_finset_sup (D : Finset W) :
    Identifies (learner f) (language f (D.sup f)) := fun t ht ↦ by
  filter_upwards [Text.eventually_subset_content_take D.finite_toSet
    (ht ▸ subset_language_finset_sup D)] with n hn
  exact congrArg _ (le_antisymm
    (conjecture_le_iff.mpr (ht ▸ t.content_take_subset n)) (finset_sup_le_conjecture hn))

/-- Theorem 2.9: the lattice learner identifies every language of its lattice space. -/
theorem identifies_language (hf : IsLatticeSpace f) (v : V) :
    Identifies (learner f) (language f v) := by
  obtain ⟨D, rfl⟩ := hf v
  exact identifies_language_finset_sup D

-- Theorem 4.1: languages are ordered as their grammars are.
theorem language_subset_language_iff (hf : IsLatticeSpace f) {a b : V} :
    language f a ⊆ language f b ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, fun h ↦ language_mono h⟩
  obtain ⟨D, rfl⟩ := hf a
  exact Finset.sup_le fun _ hx ↦ h (subset_language_finset_sup D hx)

end LatticeSpace

/-! ### Examples 2.4 and 2.8, and Table 1 -/

/-- `fac k` maps a word to the set of its `k`-factors, its substrings of length `k`
(Example 2.4). -/
def fac {α : Type*} [DecidableEq α] (k : ℕ) (w : List α) : Finset (List α) :=
  (w.sublists.filter fun v ↦ v <:+: w ∧ v.length = k).toFinset

theorem mem_fac {α : Type*} [DecidableEq α] {k : ℕ} {v w : List α} :
    v ∈ fac k w ↔ v <:+: w ∧ v.length = k := by
  simp only [fac, List.mem_toFinset, List.mem_filter, List.mem_sublists, decide_eq_true_eq]
  exact ⟨And.right, fun h ↦ ⟨h.1.sublist, h⟩⟩

section Table1

/-- The letters of the paper's running example. -/
inductive Letter
  | a | b
  deriving DecidableEq

open Letter

-- Table 1: the grammar after each of `ab`, `abb`, `aba`, `bba`; it stops changing at `aba`.
theorem table1 :
    conjecture (fac 2) [some [a, b]] = {[a, b]} ∧
    conjecture (fac 2) [some [a, b], some [a, b, b]] = {[a, b], [b, b]} ∧
    conjecture (fac 2) [some [a, b], some [a, b, b], some [a, b, a]] = {[a, b], [b, b], [b, a]} ∧
    conjecture (fac 2) [some [a, b], some [a, b, b], some [a, b, a], some [b, b, a]] =
      {[a, b], [b, b], [b, a]} := by
  decide

-- Example 2.8: the language that forbids the 2-factor `aa`.
theorem language_table1 :
    language (fac 2) ({[a, b], [b, b], [b, a]} : Finset (List Letter)) = {w | ¬ [a, a] <:+: w} := by
  ext w
  refine ⟨fun h haa ↦ absurd (h (mem_fac.2 ⟨haa, rfl⟩)) (by decide), fun h x hx ↦ ?_⟩
  obtain ⟨hx', hlen⟩ := mem_fac.1 hx
  match x, hlen, hx' with
  | [a, a], _, hx' => exact absurd hx' h
  | [a, b], _, _ => decide
  | [b, a], _, _ => decide
  | [b, b], _, _ => decide

theorem identifies_table1 : Identifies (learner (fac 2)) {w | ¬ [a, a] <:+: w} ∧
    [a, b, b, b] ∈ {w : List Letter | ¬ [a, a] <:+: w} ∧
    [a, a, b] ∉ {w : List Letter | ¬ [a, a] <:+: w} := by
  refine ⟨?_, by decide, by decide⟩
  have := identifies_language_finset_sup (f := fac 2) {[a, b], [a, b, b], [a, b, a]}
  rwa [show Finset.sup {[a, b], [a, b, b], [a, b, a]} (fac 2) = {[a, b], [b, b], [b, a]} by decide,
    language_table1] at this

end Table1

/-! ### Properties of learners (Definition 2.7) -/

section Properties

variable (h : Learner W)

/-- A learner is **set-driven** when its conjecture depends only on the content of the data. -/
def IsSetDriven : Prop := ∀ σ τ, content σ = content τ → h σ = h τ

/-- A learner is **globally consistent** when its conjecture always contains the data. -/
def IsConsistent : Prop := ∀ σ, content σ ⊆ h σ

/-- A learner is **locally conservative** when it changes its conjecture only on a word the
conjecture excludes. -/
def IsConservative : Prop := ∀ σ x, h σ ≠ h (σ ++ [some x]) → x ∉ h σ

/-- A learner is **strongly monotone** when its conjectures only grow. -/
def IsStronglyMonotone : Prop := ∀ σ x, h σ ⊆ h (σ ++ [some x])

end Properties

section LearnerProperties

variable {V : Type*} [SemilatticeSup V] [OrderBot V] (f : W → V)

-- Theorem 2.9(i): the learner is iterative, updating its grammar by the join with the new node.
theorem conjecture_append_some (σ : List (Option W)) (x : W) :
    conjecture f (σ ++ [some x]) = conjecture f σ ⊔ f x := by
  refine le_antisymm (conjecture_le_iff.mpr ?_) (sup_le (conjecture_le_of_content_subset ?_) ?_)
  · rw [content_append, content_singleton_some]
    refine union_subset (conjecture_le_iff.mp le_sup_left) ?_
    rintro _ rfl
    exact le_sup_right
  · simp
  · exact conjecture_le_iff.mp le_rfl (by simp)

theorem isSetDriven_learner : IsSetDriven (learner f) := fun _ _ h ↦ congrArg (language f)
  (le_antisymm (conjecture_le_of_content_subset h.subset)
    (conjecture_le_of_content_subset h.superset))

theorem isConsistent_learner : IsConsistent (learner f) := fun _ ↦ conjecture_le_iff.mp le_rfl

theorem isConservative_learner : IsConservative (learner f) := fun σ x hne hx ↦
  hne <| congrArg (language f) <| by rw [conjecture_append_some]; exact (sup_eq_left.mpr hx).symm

theorem isStronglyMonotone_learner : IsStronglyMonotone (learner f) := fun σ x ↦
  language_mono (conjecture_le_of_content_subset (by simp))

end LearnerProperties

/-! ### Lattice classes -/

/-- A class of languages is a **lattice class** when it is the class of some lattice space. -/
def IsLatticeClass (𝓛 : Set (Set W)) : Prop :=
  ∃ (V : Type u) (_ : SemilatticeSup V) (_ : OrderBot V) (f : W → V),
    IsLatticeSpace f ∧ range (language f) = 𝓛

theorem IsLatticeClass.identifiable {𝓛 : Set (Set W)} (h : IsLatticeClass 𝓛) : Identifiable 𝓛 := by
  obtain ⟨V, _, _, f, hf, rfl⟩ := h
  exact ⟨learner f, fun _ ⟨v, hv⟩ ↦ hv ▸ identifies_language hf v⟩

/-- A class of languages is a lattice class exactly when each finite set of words has a least
language containing it and each language is the least language containing some finite set
(Theorem 4.7(iii), corrected). -/
theorem isLatticeClass_iff {𝓛 : Set (Set W)} :
    IsLatticeClass 𝓛 ↔ (∀ D : Finset W, ∃ M, IsLeast {L ∈ 𝓛 | ↑D ⊆ L} M) ∧
      ∀ L ∈ 𝓛, ∃ D : Finset W, IsLeast {L' ∈ 𝓛 | ↑D ⊆ L'} L := by
  classical
  constructor
  · rintro ⟨V, _, _, f, hf, rfl⟩
    have hleast : ∀ D : Finset W,
        IsLeast {L ∈ range (language f) | ↑D ⊆ L} (language f (D.sup f)) :=
      fun D ↦ ⟨⟨⟨_, rfl⟩, subset_language_finset_sup D⟩, by
        rintro _ ⟨⟨v, rfl⟩, hv⟩
        exact language_mono (Finset.sup_le fun _ hx ↦ hv hx)⟩
    refine ⟨fun D ↦ ⟨_, hleast D⟩, ?_⟩
    rintro _ ⟨v, rfl⟩
    obtain ⟨D, rfl⟩ := hf v
    exact ⟨D, hleast D⟩
  · rintro ⟨hleast, hgen⟩
    choose cl hcl using hleast
    choose gen hgen using hgen
    let _ : SemilatticeSup 𝓛 :=
      { (inferInstance : PartialOrder 𝓛) with
        sup := fun A B ↦ ⟨cl (gen A A.2 ∪ gen B B.2), (hcl _).1.1⟩
        le_sup_left := fun A B ↦ (hgen A A.2).2
          ⟨(hcl _).1.1, fun _ hx ↦ (hcl _).1.2 (by simp [Finset.mem_coe.mp hx])⟩
        le_sup_right := fun A B ↦ (hgen B B.2).2
          ⟨(hcl _).1.1, fun _ hx ↦ (hcl _).1.2 (by simp [Finset.mem_coe.mp hx])⟩
        sup_le := fun A B C hAC hBC ↦ (hcl _).2 ⟨C.2, by
          rw [Finset.coe_union]
          exact union_subset ((hgen A A.2).1.2.trans hAC) ((hgen B B.2).1.2.trans hBC)⟩ }
    let _ : OrderBot 𝓛 :=
      { bot := ⟨cl ∅, (hcl _).1.1⟩
        bot_le := fun A ↦ (hcl _).2 ⟨A.2, by simp⟩ }
    let f : W → 𝓛 := fun x ↦ ⟨cl {x}, (hcl _).1.1⟩
    have hsingle : ∀ x, x ∈ cl {x} := fun x ↦ (hcl {x}).1.2 (by simp)
    have hf_le : ∀ {x} {A : 𝓛}, f x ≤ A ↔ x ∈ A.1 := fun {x A} ↦
      ⟨fun h ↦ h (hsingle x), fun h ↦ (hcl {x}).2 ⟨A.2, by simpa using h⟩⟩
    refine ⟨𝓛, inferInstance, inferInstance, f, fun A ↦ ⟨gen A A.2, ?_⟩, ?_⟩
    · refine le_antisymm (Finset.sup_le fun x hx ↦ hf_le.mpr ((hgen A A.2).1.2 hx)) ?_
      refine (hgen A A.2).2 ⟨(Finset.sup (gen A A.2) f).2, fun x hx ↦ ?_⟩
      exact (Finset.le_sup (f := f) (Finset.mem_coe.mp hx)) (hsingle x)
    · refine Set.Subset.antisymm ?_ fun L hL ↦ ⟨⟨L, hL⟩, Set.ext fun _ ↦ hf_le⟩
      rintro _ ⟨A, rfl⟩
      have : language f A = A.1 := Set.ext fun _ ↦ hf_le
      rw [this]
      exact A.2

-- Theorem 4.7
theorem isLatticeClass_iff_exists_learner [Countable W] {𝓛 : Set (Set W)} :
    IsLatticeClass 𝓛 ↔ ∃ h : Learner W, IsSetDriven h ∧ IsConsistent h ∧ IsConservative h ∧
      IsStronglyMonotone h ∧ {L | Identifies h L} = 𝓛 := by
  classical
  constructor
  · rintro ⟨V, _, _, f, hf, rfl⟩
    refine ⟨learner f, isSetDriven_learner f, isConsistent_learner f, isConservative_learner f,
      isStronglyMonotone_learner f, Set.Subset.antisymm (fun L hL ↦ ?_) ?_⟩
    · obtain ⟨t, ht⟩ := Text.exists_content_eq L
      obtain ⟨n, hn⟩ := (hL t ht).exists
      exact ⟨_, hn⟩
    · rintro _ ⟨v, rfl⟩
      exact identifies_language hf v
  · rintro ⟨h, hsd, hcons, hcv, hmono, rfl⟩
    have hsnoc : ∀ ρ τ : List (Option W), h ρ ⊆ h (ρ ++ τ) := fun ρ τ ↦ by
      induction τ using List.reverseRecOn with
      | nil => simp
      | append_singleton τ a ih =>
        rw [← List.append_assoc]
        refine ih.trans ?_
        rcases a with _ | x
        · exact (hsd _ _ (by simp)).subset
        · exact hmono _ x
    have hstay : ∀ ρ τ : List (Option W), content τ ⊆ h ρ → h (ρ ++ τ) = h ρ := fun ρ τ ↦ by
      induction τ using List.reverseRecOn with
      | nil => simp
      | append_singleton τ a ih =>
        intro hτ
        rw [content_append] at hτ
        have hρ := ih (subset_union_left.trans hτ)
        rw [← List.append_assoc]
        rcases a with _ | x
        · rw [← hρ]; exact hsd _ _ (by simp)
        · by_contra hne
          have hx : x ∈ h ρ := hτ (Or.inr (by simp))
          exact hcv (ρ ++ τ) x (fun e ↦ hne (e.symm.trans hρ)) (hρ ▸ hx)
    have hleast : ∀ ρ : List (Option W), IsLeast {L | Identifies h L ∧ content ρ ⊆ L} (h ρ) := by
      intro ρ
      refine ⟨⟨fun t ht ↦ ?_, hcons ρ⟩, ?_⟩
      · filter_upwards [Text.eventually_subset_content_take (content_finite ρ)
          (ht ▸ hcons ρ)] with n hn
        have hsub : content (t.take n) ⊆ h ρ := ht ▸ t.content_take_subset n
        rw [← hstay ρ (t.take n) hsub]
        exact hsd _ _ (by rw [content_append]; exact (union_eq_right.mpr hn).symm)
      · rintro L ⟨hL, hρL⟩
        obtain ⟨t, ht⟩ := Text.exists_content_eq L
        have htext : Text.content (ρ ++ₛ t) = L := by
          rw [Text.content_appendStream, ht, union_eq_right.mpr hρL]
        obtain ⟨n, hn, hge⟩ := ((hL _ htext).and (eventually_ge_atTop ρ.length)).exists
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hge
        rw [Text.take_appendStream] at hn
        exact hn ▸ hsnoc ρ _
    have hfin : ∀ D : Finset W, content (D.toList.map some) = ↑D := fun D ↦ by
      ext; simp [content]
    refine isLatticeClass_iff.mpr ⟨fun D ↦ ⟨h (D.toList.map some), ?_⟩, fun L hL ↦ ?_⟩
    · have := hleast (D.toList.map some)
      rwa [hfin] at this
    · obtain ⟨t, ht⟩ := Text.exists_content_eq L
      obtain ⟨n, hn⟩ := (hL t ht).exists
      obtain ⟨D, hD⟩ := (content_finite (t.take n)).exists_finset_coe
      refine ⟨D, ?_⟩
      have hlst := hleast (t.take n)
      rw [hn, ← hD] at hlst
      exact hlst

/-! ### The conditions of Theorem 4.7 -/

theorem not_isLatticeClass_singleton {K : Set W} (hK : K ≠ univ) : ¬IsLatticeClass {K} := by
  obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem K).mp hK
  rintro ⟨V, _, _, f, _, hrange⟩
  have : language f (f x) ∈ ({K} : Set (Set W)) := hrange ▸ mem_range_self _
  exact hx (mem_singleton_iff.mp this ▸ (le_refl (f x) : x ∈ language f (f x)))

-- Theorem 4.7
theorem exists_learner_singleton (K : Set W) :
    ∃ h : Learner W, IsSetDriven h ∧ IsConsistent h ∧ IsConservative h ∧ IsStronglyMonotone h ∧
      Identifies h K := by
  have hsub : ∀ σ x, content (σ ++ [some x]) ⊆ K ↔ content σ ⊆ K ∧ x ∈ K := fun σ x ↦ by
    rw [content_append, content_singleton_some, union_subset_iff, singleton_subset_iff]
  refine ⟨fun σ ↦ {y | content σ ⊆ K → y ∈ K}, fun σ τ e ↦ by simp only [e],
    fun σ y hy hσ ↦ hσ hy, fun σ x hne hx ↦ hne (Set.ext fun y ↦ ?_),
    fun σ x y hy hσ ↦ hy ((hsub σ x).mp hσ).1, fun t ht ↦ .of_forall fun n ↦ Set.ext fun y ↦ ?_⟩
  · exact ⟨fun h hσ ↦ h ((hsub σ x).mp hσ).1, fun h hσ ↦ h ((hsub σ x).mpr ⟨hσ, hx hσ⟩)⟩
  · exact ⟨fun h ↦ h (ht ▸ t.content_take_subset n), fun h _ ↦ h⟩

-- Theorem 4.7
theorem forall_exists_isLeast_finite_union_univ (D : Finset W) :
    ∃ M, IsLeast {L ∈ {L : Set W | L.Finite ∨ L = univ} | ↑D ⊆ L} M := by
  refine ⟨↑D, ⟨.inl D.finite_toSet, subset_rfl⟩, ?_⟩
  rintro _ ⟨_, hL⟩
  exact hL

theorem not_identifiable_finite_union_univ [Countable W] [Infinite W] :
    ¬Identifiable {L : Set W | L.Finite ∨ L = univ} :=
  not_identifiable_of_finite_subsets (L := univ) (.inr rfl) infinite_univ fun _ _ hT ↦ .inl hT

/-! ### Finite joins and the chain condition -/

section ChainCondition

variable {V : Type*} [SemilatticeSup V] [OrderBot V] {f : W → V}

theorem exists_finset_forall_le {a : V} [WellFoundedGT (Iic a)] {S : Set W}
    (hS : S ⊆ language f a) : ∃ D : Finset W, ↑D ⊆ S ∧ ∀ x ∈ S, f x ≤ D.sup f := by
  classical
  have hsup : ∀ D : Finset W, ↑D ⊆ S → D.sup f ≤ a :=
    fun D hD ↦ Finset.sup_le fun _ hx ↦ hS (hD hx)
  let P : Set (Iic a) := {v | ∃ D : Finset W, ↑D ⊆ S ∧ D.sup f = v.1}
  have hne : P.Nonempty := ⟨⟨⊥, bot_le⟩, ∅, by simp, rfl⟩
  obtain ⟨⟨v, hv⟩, ⟨D, hDS, hDv⟩, hmax⟩ := (wellFounded_gt (α := Iic a)).has_min P hne
  have hDv' : D.sup f = v := hDv
  refine ⟨D, hDS, fun x hx ↦ ?_⟩
  have hins : ↑(insert x D) ⊆ S := by
    rw [Finset.coe_insert]; exact insert_subset hx hDS
  by_contra hle
  have h₁ : v ≤ (insert x D).sup f := hDv' ▸ Finset.sup_mono (Finset.subset_insert _ _)
  have h₂ : f x ≤ (insert x D).sup f := Finset.le_sup (Finset.mem_insert_self _ _)
  have hne' : v ≠ (insert x D).sup f := fun e ↦ hle (hDv' ▸ e ▸ h₂)
  exact hmax ⟨_, hsup _ hins⟩ ⟨_, hins, rfl⟩ (Subtype.mk_lt_mk.mpr (lt_of_le_of_ne h₁ hne'))

-- Definition 2.3, n. 2
theorem isLatticeClass_range_language [∀ v : V, WellFoundedGT (Iic v)] (f : W → V) :
    IsLatticeClass (range (language f)) := by
  refine isLatticeClass_iff.mpr ⟨fun D ↦ ⟨language f (D.sup f), ⟨⟨_, rfl⟩,
    subset_language_finset_sup D⟩, ?_⟩, ?_⟩
  · rintro _ ⟨⟨v, rfl⟩, hv⟩
    exact language_mono (Finset.sup_le fun _ hx ↦ hv hx)
  · rintro _ ⟨a, rfl⟩
    obtain ⟨D, hD, hle⟩ := exists_finset_forall_le (a := a) (S := language f a) subset_rfl
    refine ⟨D, ⟨⟨_, rfl⟩, hD⟩, ?_⟩
    rintro _ ⟨⟨v, rfl⟩, hv⟩ x hx
    exact (hle x hx).trans (Finset.sup_le fun _ hy ↦ hv hy)

end ChainCondition

/-! ### Products of lattice spaces (§3) -/

section Product

variable {V₁ V₂ : Type*} [SemilatticeSup V₁] [OrderBot V₁] [SemilatticeSup V₂] [OrderBot V₂]

omit [OrderBot V₁] [OrderBot V₂] in
theorem language_prod (f₁ : W → V₁) (f₂ : W → V₂) (a : V₁) (b : V₂) :
    language (fun x ↦ (f₁ x, f₂ x)) (a, b) = language f₁ a ∩ language f₂ b := rfl

/-- Under the chain condition the elementwise intersections of two classes form a lattice class. -/
theorem isLatticeClass_inter [∀ v : V₁, WellFoundedGT (Iic v)] [∀ v : V₂, WellFoundedGT (Iic v)]
    (f₁ : W → V₁) (f₂ : W → V₂) :
    IsLatticeClass {L | ∃ a b, L = language f₁ a ∩ language f₂ b} := by
  classical
  refine isLatticeClass_iff.mpr ⟨fun D ↦ ⟨language f₁ (D.sup f₁) ∩ language f₂ (D.sup f₂),
    ⟨⟨_, _, rfl⟩, subset_inter (subset_language_finset_sup D) (subset_language_finset_sup D)⟩,
    ?_⟩, ?_⟩
  · rintro _ ⟨⟨a, b, rfl⟩, hD⟩
    exact inter_subset_inter
      (language_mono (Finset.sup_le fun _ hx ↦ (hD hx).1))
      (language_mono (Finset.sup_le fun _ hx ↦ (hD hx).2))
  · rintro _ ⟨a, b, rfl⟩
    obtain ⟨D₁, hD₁, hle₁⟩ := exists_finset_forall_le (f := f₁) (a := a)
      (S := language f₁ a ∩ language f₂ b) inter_subset_left
    obtain ⟨D₂, hD₂, hle₂⟩ := exists_finset_forall_le (f := f₂) (a := b)
      (S := language f₁ a ∩ language f₂ b) inter_subset_right
    refine ⟨D₁ ∪ D₂, ⟨⟨_, _, rfl⟩, by rw [Finset.coe_union]; exact union_subset hD₁ hD₂⟩, ?_⟩
    rintro _ ⟨⟨a', b', rfl⟩, hD⟩ x hx
    refine ⟨(hle₁ x hx).trans (Finset.sup_le fun y hy ↦ (hD ?_).1),
      (hle₂ x hx).trans (Finset.sup_le fun y hy ↦ (hD ?_).2)⟩
    · simp [Finset.mem_coe.mp hy]
    · simp [Finset.mem_coe.mp hy]

/-- The first lattice space of the counterexample to modularity: words are the natural numbers and
one further word `none`, whose node lies above every finite set of numbers. The class is the finite
sets of numbers together with all words, learnable because `none` is a telltale of all words. -/
def counterexample₁ : Option ℕ → WithTop (Finset ℕ)
  | some n => (({n} : Finset ℕ) : WithTop (Finset ℕ))
  | none => ⊤

/-- The second lattice space: a word's node records whether it is `none`. The class is the numbers
and all words. -/
def counterexample₂ : Option ℕ → Bool
  | some _ => false
  | none => true

theorem isLatticeSpace_counterexample₁ : IsLatticeSpace counterexample₁ := by
  classical
  refine fun v ↦ ?_
  induction v using WithTop.recTopCoe with
  | top => exact ⟨{none}, by simp [counterexample₁]⟩
  | coe F =>
    induction F using Finset.induction_on with
    | empty => exact ⟨∅, rfl⟩
    | insert n F _ ih =>
      obtain ⟨D, hD⟩ := ih
      refine ⟨insert (some n) D, ?_⟩
      rw [Finset.sup_insert, hD, Finset.insert_eq]
      exact (WithTop.coe_sup _ _).symm

theorem isLatticeSpace_counterexample₂ : IsLatticeSpace counterexample₂ := by
  rintro (_ | _)
  · exact ⟨∅, rfl⟩
  · exact ⟨{none}, by simp [counterexample₂]⟩

theorem language_counterexample₁_coe (F : Finset ℕ) :
    language counterexample₁ (F : WithTop (Finset ℕ)) = some '' (F : Set ℕ) := by
  ext (_ | n)
  · simp [counterexample₁]
  · simp [counterexample₁, WithTop.coe_le_coe]

theorem language_counterexample₂_false : language counterexample₂ false = range some := by
  ext (_ | n) <;> simp [counterexample₂]

/-- **Lattice classes are not closed under elementwise intersection**: both classes here are lattice
classes, yet their intersections contain the numbers and all their finite subsets. The word `none`
is what made the finite sets and all words learnable, and intersection discards it. -/
theorem not_identifiable_inter :
    ¬Identifiable {L | ∃ a b, L = language counterexample₁ a ∩ language counterexample₂ b} := by
  have huniv₁ : language counterexample₁ ⊤ = univ :=
    eq_univ_of_forall fun x ↦ show counterexample₁ x ≤ ⊤ from le_top
  have huniv₂ : language counterexample₂ true = univ :=
    eq_univ_of_forall fun x ↦ show counterexample₂ x ≤ true from le_top
  refine not_identifiable_of_finite_subsets (L := range some)
    ⟨⊤, false, ?_⟩ (infinite_range_of_injective (Option.some_injective ℕ)) fun T hT hfin ↦ ?_
  · rw [huniv₁, univ_inter, language_counterexample₂_false]
  · have hF : (some ⁻¹' T).Finite := hfin.preimage (Option.some_injective ℕ).injOn
    refine ⟨(hF.toFinset : Finset ℕ), true, ?_⟩
    rw [huniv₂, inter_univ, language_counterexample₁_coe, hF.coe_toFinset,
      image_preimage_eq_of_subset hT]

-- §3
theorem not_isLatticeSpace_prod :
    ¬IsLatticeSpace fun x ↦ (counterexample₁ x, counterexample₂ x) := fun h ↦
  not_identifiable_inter ⟨learner _, by
    rintro _ ⟨a, b, rfl⟩
    exact identifies_language h (a, b)⟩

end Product

/-! ### `V_kSP` is not a lattice -/

section SubsequenceSets

open List

private theorem sublist_or_sublist : ∀ w : List Bool, [true] <+ w → [false] <+ w →
    [true, false] <+ w ∨ [false, true] <+ w
  | [], ht, _ => by simp at ht
  | true :: w, _, hf => .inl (cons_sublist_cons.mpr (by simpa using hf))
  | false :: w, ht, _ => .inr (cons_sublist_cons.mpr (by simpa using ht))

theorem not_exists_isLUB_subseqSet :
    ¬∃ v : range (subseqSet 2 : List Bool → Set (List Bool)),
      IsLUB {⟨_, mem_range_self [true]⟩, ⟨_, mem_range_self [false]⟩} v := by
  rintro ⟨⟨_, w, rfl⟩, hub, hlb⟩
  have ht : [true] <+ w :=
    (hub (mem_insert _ _) (show [true] ∈ subseqSet 2 [true] by simp)).1
  have hf : [false] <+ w :=
    (hub (mem_insert_of_mem _ rfl) (show [false] ∈ subseqSet 2 [false] by simp)).1
  have hmem (u : List Bool) (h₁ : [true] <+ u) (h₂ : [false] <+ u) :
      subseqSet 2 w ⊆ subseqSet 2 u := by
    refine hlb (a := ⟨_, mem_range_self u⟩) ?_
    rintro _ (rfl | rfl) s hs
    · exact ⟨hs.1.trans h₁, hs.2⟩
    · exact ⟨hs.1.trans h₂, hs.2⟩
  rcases sublist_or_sublist w ht hf with h | h
  · exact absurd (hmem [false, true] (by simp) (by simp) ⟨h, by simp⟩).1 (by decide)
  · exact absurd (hmem [true, false] (by simp) (by simp) ⟨h, by simp⟩).1 (by decide)

end SubsequenceSets

/-! ### Grammars as sets of features

A word is mapped to a finite set of features and a grammar permits a set of them, the shape of all
the paper's subregular examples. With finite grammars this is a lattice class, and with arbitrary
grammars it is learnable exactly when finitely many features occur at all. -/

section Features

variable {X : Type*}

theorem isLatticeClass_finite_grammars [DecidableEq X] (F : W → Finset X) :
    IsLatticeClass {L | ∃ G : Finset X, L = {w | F w ⊆ G}} := by
  have : ∀ v : Finset X, WellFoundedGT (Iic v) := fun v ↦
    have : Finite (Iic v) := (Finset.finite_toSet v.powerset).subset fun u hu ↦ by simpa using hu
    Finite.to_wellFoundedGT
  have heq : {L | ∃ G : Finset X, L = {w | F w ⊆ G}} = range (language F) :=
    Set.ext fun L ↦ ⟨fun ⟨G, hG⟩ ↦ ⟨G, hG.symm⟩, fun ⟨G, hG⟩ ↦ ⟨G, hG.symm⟩⟩
  rw [heq]
  exact isLatticeClass_range_language F

theorem isLatticeClass_factorsThrough (vec : W → X) (hvec : (range vec).Finite) :
    IsLatticeClass {L : Set W | Function.FactorsThrough (· ∈ L) vec} := by
  classical
  have heq : {L : Set W | Function.FactorsThrough (· ∈ L) vec} =
      {L | ∃ G : Finset X, L = {w | ({vec w} : Finset X) ⊆ G}} := by
    ext L
    constructor
    · intro hL
      refine ⟨(hvec.subset (image_subset_range vec L)).toFinset, Set.ext fun w ↦ ?_⟩
      simp only [Finset.singleton_subset_iff, Finite.mem_toFinset, mem_image]
      exact ⟨fun hw ↦ ⟨w, hw, rfl⟩, fun ⟨v, hv, e⟩ ↦ (hL e).mp hv⟩
    · rintro ⟨G, rfl⟩ u v e
      simp [e]
  rw [heq]
  exact isLatticeClass_finite_grammars _

-- Definition 2.5, n. 3
theorem identifiable_range_iff [Countable W] (F : W → Set X) (hF : ∀ w, (F w).Finite) :
    Identifiable (range fun G : Set X ↦ {w | F w ⊆ G}) ↔ (⋃ w, F w).Finite := by
  refine ⟨fun h ↦ ?_, fun h ↦ identifiable_of_finite ?_⟩
  · obtain ⟨T, hT, -, hno⟩ := (identifiable_iff.mp h).2 univ
      ⟨univ, eq_univ_of_forall fun _ ↦ subset_univ _⟩
    by_contra hinf
    have hG : (⋃ w ∈ T, F w).Finite := hT.biUnion fun w _ ↦ hF w
    obtain ⟨x, hx, hxG⟩ := (Set.not_subset.mp fun hsub ↦ hinf (hG.subset hsub) :
      ∃ x ∈ ⋃ w, F w, x ∉ ⋃ w ∈ T, F w)
    obtain ⟨w₀, hw₀⟩ := mem_iUnion.mp hx
    refine hno {w | F w ⊆ ⋃ w ∈ T, F w} ⟨_, rfl⟩ (fun w hw ↦ subset_biUnion_of_mem hw) ?_
    exact (subset_univ _).ssubset_of_ne fun e ↦ hxG
      ((show w₀ ∈ {w | F w ⊆ ⋃ w ∈ T, F w} from e ▸ mem_univ w₀) hw₀)
  · refine (h.finite_subsets.image fun G ↦ {w | F w ⊆ G}).subset ?_
    rintro _ ⟨G, rfl⟩
    refine ⟨G ∩ ⋃ w, F w, inter_subset_right, Set.ext fun w ↦ ?_⟩
    exact ⟨fun hw x hx ↦ (hw hx).1, fun hw x hx ↦ ⟨hw hx, mem_iUnion.mpr ⟨w, hx⟩⟩⟩

end Features

/-! ### Subregular languages (§3) -/

section Subregular

variable {α : Type u}

theorem isLatticeClass_strictlyLocal (k : ℕ) :
    IsLatticeClass {L : Set (List α) | ∃ G : Finset (Augmented α),
      L = StrictlyLocalGrammar.language k (G : Set (Augmented α))} := by
  classical
  have heq : {L : Set (List α) | ∃ G : Finset (Augmented α),
      L = StrictlyLocalGrammar.language k (G : Set (Augmented α))} =
      {L | ∃ G : Finset (Augmented α), L = {w | fac k (boundary k w) ⊆ G}} :=
    Set.ext fun L ↦ exists_congr fun G ↦ by
      refine iff_of_eq (congrArg _ (Set.ext fun w ↦ ?_))
      simp only [Finset.subset_iff, mem_fac]
      exact ⟨fun h f hf ↦ h f hf.2 hf.1, fun h f hl hf ↦ h ⟨hf, hl⟩⟩
  rw [heq]
  exact isLatticeClass_finite_grammars _

theorem isLatticeClass_strictlyPiecewise (k : ℕ) :
    IsLatticeClass {L : Set (List α) | ∃ G : Finset (List α),
      L = StrictlyPiecewiseGrammar.language k (G : Set (List α))} := by
  classical
  have heq : {L : Set (List α) | ∃ G : Finset (List α),
      L = StrictlyPiecewiseGrammar.language k (G : Set (List α))} =
      {L | ∃ G : Finset (List α),
        L = {w | (w.sublists.filter fun s ↦ s.length ≤ k).toFinset ⊆ G}} :=
    Set.ext fun L ↦ exists_congr fun G ↦ by
      refine iff_of_eq (congrArg _ (Set.ext fun w ↦ ?_))
      simp only [Finset.subset_iff, List.mem_toFinset, List.mem_filter, List.mem_sublists,
        decide_eq_true_eq]
      exact ⟨fun h s hs ↦ h s hs.2 hs.1, fun h s hl hs ↦ h ⟨hs, hl⟩⟩
  rw [heq]
  exact isLatticeClass_finite_grammars _

theorem isLatticeClass_isLocallyTestable [Finite α] (k : ℕ) :
    IsLatticeClass {L : Set (List α) | Language.IsLocallyTestable L k} :=
  isLatticeClass_factorsThrough (List.kTestVector k) (List.finite_range_kTestVector k)

theorem isLatticeClass_isPiecewiseTestable [Finite α] (k : ℕ) :
    IsLatticeClass {L : Set (List α) | Language.IsPiecewiseTestable L k} :=
  isLatticeClass_factorsThrough (subseqSet k) (finite_range_subseqSet k)

/-- At a fixed width the strictly local languages, whose grammars may be infinite, are identifiable
exactly when the alphabet is finite. -/
theorem identifiable_isStrictlyLocal_iff [Countable α] {k : ℕ} (hk : 1 ≤ k) :
    Identifiable {L : Set (List α) | Language.IsStrictlyLocal L k} ↔ Finite α := by
  let F : List α → Set (Augmented α) := fun w ↦ {f | f <:+: boundary k w ∧ f.length = k}
  have hclass : {L : Set (List α) | Language.IsStrictlyLocal L k} =
      range fun G : Set (Augmented α) ↦ {w | F w ⊆ G} :=
    Set.ext fun L ↦ exists_congr fun G ↦ by rw [StrictlyLocalGrammar.language_eq_core]; rfl
  have hfin (w : List α) : (F w).Finite :=
    (List.finite_toSet (boundary k w).sublists).subset fun _ hf ↦ List.mem_sublists.mpr hf.1.sublist
  rw [hclass, identifiable_range_iff F hfin]
  constructor
  · intro hfin
    by_contra hinf
    have : Infinite α := not_finite_iff_infinite.mp hinf
    refine infinite_of_injective_forall_mem (f := fun a : α ↦
      List.replicate (k - 1) none ++ [some a]) (fun a b hab ↦ by simpa using hab) (fun a ↦ ?_) hfin
    refine mem_iUnion.mpr ⟨[a], ⟨[], List.replicate (k - 1) none, ?_⟩, ?_⟩
    · simp [boundary]
    · simp only [List.length_append, List.length_replicate, List.length_singleton]; omega
  · intro _
    refine (List.finite_length_eq (Option α) k).subset fun f hf ↦ ?_
    obtain ⟨w, hw⟩ := mem_iUnion.mp hf
    exact hw.2

theorem identifiable_isStrictlyPiecewise_iff [Countable α] {k : ℕ} (hk : 1 ≤ k) :
    Identifiable {L : Set (List α) | Language.IsStrictlyPiecewise L k} ↔ Finite α := by
  have hlang : ∀ G : Set (List α), StrictlyPiecewiseGrammar.language k G =
      {w | subseqSet k w ⊆ G} := fun G ↦
    Set.ext fun w ↦ ⟨fun h s hs ↦ h s hs.2 hs.1, fun h s hl hs ↦ h ⟨hs, hl⟩⟩
  have hclass : {L : Set (List α) | Language.IsStrictlyPiecewise L k} =
      range fun G : Set (List α) ↦ {w | subseqSet k w ⊆ G} :=
    Set.ext fun L ↦ exists_congr fun G ↦ by rw [hlang]
  have hfin : ∀ w : List α, (subseqSet k w).Finite := fun w ↦
    (List.finite_toSet w.sublists).subset fun s hs ↦ List.mem_sublists.mpr hs.1
  rw [hclass, identifiable_range_iff _ hfin]
  constructor
  · intro hf
    by_contra hinf
    have : Infinite α := not_finite_iff_infinite.mp hinf
    refine infinite_of_injective_forall_mem (f := fun a : α ↦ [a])
      (fun a b hab ↦ by simpa using hab) (fun a ↦ ?_) hf
    exact mem_iUnion.mpr ⟨[a], List.Sublist.refl _, by simpa using hk⟩
  · intro _
    refine (List.finite_length_le α k).subset fun s hs ↦ ?_
    obtain ⟨w, hw⟩ := mem_iUnion.mp hs
    exact hw.2

private theorem strictMono_length_le [Nonempty α] :
    StrictMono fun n : ℕ ↦ {w : List α | w.length ≤ n} := by
  refine strictMono_nat_of_lt_succ fun n ↦ ⟨fun _ h ↦ Nat.le_succ_of_le h, fun hsub ↦ ?_⟩
  have := hsub (show List.replicate (n + 1) (Classical.arbitrary α) ∈
    {w : List α | w.length ≤ n + 1} by simp)
  simp at this

private theorem iUnion_length_le : ⋃ n : ℕ, {w : List α | w.length ≤ n} = univ :=
  eq_univ_of_forall fun w ↦ mem_iUnion.mpr ⟨w.length, show w.length ≤ w.length from le_rfl⟩

theorem not_identifiable_exists_isStrictlyLocal [Countable α] [Nonempty α] :
    ¬Identifiable {L : Set (List α) | ∃ k, Language.IsStrictlyLocal L k} := by
  refine not_identifiable_of_strictMono_iUnion strictMono_length_le (fun n ↦ ?_) ?_
  · refine ⟨n + 1, {f | none ∈ f}, Set.ext fun w ↦ ?_⟩
    rw [StrictlyLocalGrammar.mem_language_iff_window (by omega)]
    constructor
    · intro h
      by_contra hlen
      have hlen' : n < w.length := not_le.mp hlen
      have := h 0 (by omega) (by omega)
      obtain ⟨j, hj⟩ := (List.mem_ofFn' _ _).mp this
      have hnone := List.getElem?_int_eq_none_iff.mp hj
      have := j.2
      omega
    · intro h i hi₁ _
      have hw : (w.length : ℤ) ≤ n := by exact_mod_cast (show w.length ≤ n from h)
      refine (List.mem_ofFn' _ _).mpr ?_
      rcases lt_or_ge i 0 with hi | hi
      · exact ⟨⟨0, by omega⟩, List.getElem?_int_eq_none_iff.mpr (by push_cast; omega)⟩
      · exact ⟨⟨n, by omega⟩, List.getElem?_int_eq_none_iff.mpr (by push_cast; omega)⟩
  · rw [iUnion_length_le]
    exact ⟨1, univ, eq_univ_of_forall fun _ _ _ _ ↦ mem_univ _⟩

theorem not_identifiable_exists_isStrictlyPiecewise [Countable α] [Nonempty α] :
    ¬Identifiable {L : Set (List α) | ∃ k, Language.IsStrictlyPiecewise L k} := by
  refine not_identifiable_of_strictMono_iUnion strictMono_length_le (fun n ↦ ?_) ?_
  · refine ⟨n + 1, {s | s.length ≤ n}, Set.ext fun w ↦ ⟨fun h ↦ ?_, fun h s _ hs ↦ ?_⟩⟩
    · by_contra hlen
      have hlen' : n + 1 ≤ w.length := Nat.lt_of_not_le hlen
      have := h (w.take (n + 1)) (by simp) (List.take_sublist _ _)
      simp only [mem_ofPred_eq, List.length_take, min_eq_left hlen'] at this
      omega
    · exact hs.length_le.trans h
  · rw [iUnion_length_le]
    exact ⟨0, univ, eq_univ_of_forall fun _ _ _ _ ↦ mem_univ _⟩

end Subregular

end HeinzKasprzikKotzing2012
