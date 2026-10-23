module

public import Linglib.Data.Examples.Hyman2003
public import Linglib.Morphology.Morphotactics.AffixTemplate
public import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
public import Studies.Baker1985
public import Mathlib.Data.List.Sections

/-!
# Hyman 2003: suffix ordering in Bantu

Hyman argues that the order of the Bantu verbal extensions, causative, applicative,
reciprocal and passive, is driven by a Pan-Bantu default template, CARP (5), not by semantic
scope or by Baker's Mirror Principle: Chichewa realizes both scopes of causative and
applicative as *-its-il-* (3), a reciprocal inside a causative surfaces in the templatic order
*-its-an-* as well as the mirror order *-an-its-* while the mirror order has only the
compositional reading (2), a reciprocal inside an applicative surfaces as templatic *-il-an-*
or with the reciprocal doubled, *-an-il-an-*, never as *-an-il-* (13), and no extension repeats
(18). The two pressures, TEMPLATE, which licenses a sequence in the template's order, and the
suffix-specific MIRROR constraints, which license a sequence in the order of scope, are
ranked, violably and sometimes freely, as in Optimality Theory: a candidate succeeds at the
first licensor down the ranking by which every sequence and every doubling in it is licensed,
and a doubled suffix must be a mirror override repaired by a templatic sequence, licensed by
the conjunction of the two (16). Chimwiini ranks only the template (19), and the syntax of
Chichewa passives (22)–(23) shows the order of syntactic operations varying under one fixed
affix order, so the Mirror Principle holds, if at all, as a violable constraint (§3).

## Main definitions

* `Ext`, `carp`, `templatic`: the extensions, the CARP template and an input's templatic
  realization.
* `Licensor`, `Licensor.licenses`, `LicensedBy`: TEMPLATE, MIRROR and their conjunction, what
  each licenses of a candidate, and full licensing by a set of them.
* `candidates`, `tableau`, `Grammar`, `Grammar.outputs`: the candidates of an input, Hyman's
  evaluation under a ranking as an OT tableau, a partially ordered set of licensors, and the
  outputs across its linear extensions.
* `chichewa`, `chimwiini`, `passiveGrammar`: the grammars of §2, §3 and (12).

## Main results

* `mem_carp_language`, `licensedBy_template_iff`: the template admits exactly the strings rising
  in its order, and those are what TEMPLATE alone licenses.
* `licensedBy_iff_templatic`, `chimwiini_outputs`: among an input's candidates the template
  alone licenses only the templatic realization, the only output of a template-only grammar
  (19).
* `outputs_isChain_ne`, `doubling_licensed`: no output repeats a suffix, and a doubled suffix
  is a mirror override the template repairs.
* `asymmetric_compositionality`, `causative_applicative`, `applicative_reciprocal`, `passive`:
  (2), (3) with (7), (13) with (16), and (12).
* `three_suffixes`: the appendix's table for three extensions.
* `scope_not_recoverable`, `mirror_predicts_distinct_words`, `rows_passive`: one affix order
  for two syntactic derivations (§3), which Baker's architecture would keep apart and
  whose passives his rules derive from scope.
* `rows_outputs`: the paper's forms.

## Implementation notes

* Hyman's tableaux mark the sequences a licensor licenses rather than violations; the
  evaluation, a candidate winning at the first rank by which all its sequences are licensed,
  is the lexicographic minimization of the profile whose `k`-th entry says whether the top
  `k + 1` licensors fail to license the candidate, so it is a substrate `Tableau`.
* The conjunction `MIRROR (x, y) & TEMPLATE` licenses an adjacent `x y` followed by `x`, the
  templatic repair of a mirror override, and the doubling of `x` in any `x … y x`. This
  follows §2's generalization that doubling yields A-B-A only when A-B is a mirror override;
  the appendix's tableaux (48c, e) also mark *mang-an-its-il-an* successful, licensing its
  doubled *-an-* without the conjunction, which the model does not derive.
* Chichewa's licensors are TEMPLATE, MIRROR (R, C) and the conjunction for (R, A), freely
  ranked, as the appendix ranks them; MIRROR (A, C) is not activated and MIRROR (R, A) alone is
  dominated by TEMPLATE, so neither ever licenses an output.
* Baker's rules run on Chichewa with the Chamorro-type causative and the passive of the
  first object, the asymmetric-object setting of (22)–(23).

## TODO

* Table (48) diverges from the model on two forms (`three_suffixes`): the paper's licensing of
  non-adjacent sequences, invoked for *-an- … -il-an-*, is not defined and would settle both.
* The elaborated template CARCP (28) with the short causative, and the phonological
  templatic requirements of §5.

## References

* [hyman-2003]
* [hyman-mchombo-1992]
* [alsina-1999]
* [abasheikh-1978]
* [baker-1985]
* [anttila-1997]
-/

@[expose] public section

namespace Hyman2003

open Morphology OptimalityTheory

/-! ### The template -/

/-- The Proto-Bantu verbal extensions of the template (5): causative, applicative, reciprocal,
passive. -/
inductive Ext
  | C
  | A
  | R
  | P
  deriving DecidableEq, Repr, Fintype

/-- The Pan-Bantu default template (5), CARP: the extensions as suffix slots in the order
Causative-Applicative-Reciprocal-Passive. -/
def carp : AffixTemplate Ext := { suffixSlots := [.C, .A, .R, .P] }

/-- An extension's position in the template. -/
def Ext.slot (x : Ext) : ℕ := carp.slots.idxOf x

theorem slot_injective : Function.Injective Ext.slot := by
  intro x y; cases x <;> cases y <;> decide

/-- The extensions in the order of the template. -/
instance : LinearOrder Ext := LinearOrder.lift' Ext.slot slot_injective

theorem carp_sortedLT : carp.slots.SortedLT := by decide

/-- The template admits exactly the strings of extensions rising in its order. -/
theorem mem_carp_language {c : List Ext} : c ∈ carp.language ↔ c.SortedLT := by
  rw [carp.mem_language_iff_sublist rfl]
  refine ⟨fun h ↦ (carp_sortedLT.pairwise.sublist h).sortedLT, fun h ↦ ?_⟩
  exact List.sublist_of_subperm_of_sortedLE
    (List.subperm_of_subset h.nodup fun x _ ↦ by cases x <;> decide) h.sortedLE
    carp_sortedLT.sortedLE

/-- A morphosyntactic input, the extensions in order of scope, innermost first, as in the
bracketing `[[[V] x] y]`. -/
abbrev Input := List Ext

/-- In the input, `x` is within the scope of `y`. -/
def Input.Inside (i : Input) (x y : Ext) : Prop := x ∈ i ∧ y ∈ i ∧ i.idxOf x < i.idxOf y

instance (i : Input) (x y : Ext) : Decidable (i.Inside x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A candidate output, the suffixes in surface order, innermost first. -/
abbrev Candidate := List Ext

/-- The templatic realization of an input, the template's slots filled by its extensions. -/
def templatic (i : Input) : Candidate := carp.slots.filter (· ∈ i)

theorem templatic_sortedLT (i : Input) : (templatic i).SortedLT :=
  (carp_sortedLT.pairwise.sublist List.filter_sublist).sortedLT

theorem mem_templatic {i : Input} {x : Ext} : x ∈ templatic i ↔ x ∈ i := by
  simp [templatic, show ∀ y : Ext, y ∈ carp.slots by decide]

/-! ### Licensors -/

/-- The licensors of suffix sequences. TEMPLATE licenses a sequence in the template's order
(6a), MIRROR (x, y) licenses the sequence `x y` when `x` is within the scope of `y` (6b), and
their conjunction licenses a mirror override repaired by a templatic sequence, `x y x` (16). -/
inductive Licensor
  | template
  | mirror (x y : Ext)
  | mirrorTemplate (x y : Ext)
  deriving DecidableEq, Repr

/-- What a candidate needs licensed, each adjacent pair, by the position of its first member,
and each extension it doubles. -/
inductive Demand
  | pair (k : ℕ)
  | doubling (x : Ext)
  deriving DecidableEq, Repr

/-- A candidate's demands. -/
def demands (c : Candidate) : List Demand :=
  (List.range (c.length - 1)).map .pair ++ (c.dedup.filter fun x ↦ 1 < c.count x).map .doubling

/-- A licensor meets a demand of a candidate for an input. TEMPLATE meets a pair rising in the
template, MIRROR (x, y) the pair `x y` with `x` inside `y`, and the conjunction either pair of
an `x y x` with `x` inside `y` and the doubling of `x` in any `x … y x`. -/
def Licensor.licenses (i : Input) (c : Candidate) : Licensor → Demand → Prop
  | .template, .pair k => ∃ x y : Ext, c[k]? = some x ∧ c[k + 1]? = some y ∧ x < y
  | .mirror x y, .pair k => i.Inside x y ∧ c[k]? = some x ∧ c[k + 1]? = some y
  | .mirrorTemplate x y, .pair k => i.Inside x y ∧
      (c[k]? = some x ∧ c[k + 1]? = some y ∧ c[k + 2]? = some x ∨
        c[k]? = some y ∧ c[k + 1]? = some x ∧ 1 ≤ k ∧ c[k - 1]? = some x)
  | .mirrorTemplate x y, .doubling z => z = x ∧ i.Inside x y ∧
      ∃ j ∈ List.range c.length, ∃ k ∈ List.range c.length,
        j < k ∧ c[j]? = some x ∧ c[k]? = some y ∧ c[k + 1]? = some x
  | .template, .doubling _ => False
  | .mirror _ _, .doubling _ => False

instance (i : Input) (c : Candidate) : (l : Licensor) → (d : Demand) →
    Decidable (l.licenses i c d)
  | .template, .pair _ => inferInstanceAs (Decidable (∃ _ _ : Ext, _ ∧ _ ∧ _))
  | .mirror _ _, .pair _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .mirrorTemplate _ _, .pair _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))
  | .mirrorTemplate _ _, .doubling _ =>
      inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ _ ∈ _, ∃ _ ∈ _, _))
  | .template, .doubling _ => inferInstanceAs (Decidable False)
  | .mirror _ _, .doubling _ => inferInstanceAs (Decidable False)

/-- A candidate is licensed by a set of licensors when each of its demands is met by one. -/
def LicensedBy (i : Input) (S : List Licensor) (c : Candidate) : Prop :=
  ∀ d ∈ demands c, ∃ l ∈ S, l.licenses i c d

instance (i : Input) (S : List Licensor) (c : Candidate) : Decidable (LicensedBy i S c) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ∃ _ ∈ _, _))

theorem LicensedBy.mono {i : Input} {S T : List Licensor} (h : S ⊆ T) {c : Candidate}
    (hc : LicensedBy i S c) : LicensedBy i T c :=
  fun d hd ↦ (hc d hd).imp fun _ hl ↦ ⟨h hl.1, hl.2⟩

/-! ### Evaluation -/

/-- The candidates of an input, its templatic realization and every sequence over its
extensions that realizes each of them, repeats none immediately and doubles at most one. -/
def candidates (i : Input) : Finset Candidate :=
  insert (templatic i)
    ((List.sections (List.replicate i.dedup.length i.dedup) ++
        List.sections (List.replicate (i.dedup.length + 1) i.dedup)).filter fun c ↦
      (∀ x ∈ i, x ∈ c) ∧ c.IsChain (· ≠ ·)).toFinset

/-- The constraint at rank `k` of a ranking of licensors: violated by a candidate the top
`k + 1` licensors do not license. -/
def constraints (i : Input) (order : List Licensor) : ConstraintSet Candidate (Fin order.length) :=
  fun k ↦ Constraint.binary fun c ↦ ¬ LicensedBy i (order.take (k + 1)) c

/-- Hyman's evaluation under a ranking. A candidate succeeds at the first licensor down the
ranking by which all of its demands are licensed, the lexicographic minimum of the cumulative
profile. -/
def tableau (i : Input) (order : List Licensor) : Tableau Candidate order.length :=
  ⟨candidates i, constraints i order⟩

/-- A grammar, licensors under a partial order ([anttila-1997]'s partially ordered
constraints) evaluated under each linear extension. Free ranking is the discrete order. -/
structure Grammar where
  /-- The number of licensors. -/
  n : ℕ
  /-- The licensors. -/
  licensor : Fin n → Licensor
  /-- The ranking, a partial order on the licensors. -/
  order : Fin n → Fin n → Prop
  [isPartialOrder : IsPartialOrder (Fin n) order]
  [decidableRel : DecidableRel order]

attribute [instance] Grammar.isPartialOrder Grammar.decidableRel

namespace Grammar

variable (G : Grammar)

/-- The linear extensions of the grammar's order. -/
def rankings : Finset (Ranking (Fin G.n) G.n) := consistentTotalOrders G.order

/-- The licensors in the order of a ranking, most dominant first. -/
def ranked (σ : Ranking (Fin G.n) G.n) : List Licensor :=
    (List.finRange G.n).map fun p ↦ G.licensor (σ p)

/-- The outputs of an input, the winners under some linear extension. -/
def outputs (i : Input) : Finset Candidate :=
  G.rankings.biUnion fun σ ↦ (tableau i (G.ranked σ)).optimal

/-- A grammar of freely ranked licensors. -/
def free {n : ℕ} (licensor : Fin n → Licensor) : Grammar :=
  { n := n, licensor := licensor, order := (· = ·) }

/-- A grammar of two licensors, the first ranked above the second. -/
def two (l₁ l₂ : Licensor) : Grammar :=
  { n := 2, licensor := ![l₁, l₂], order := (1 : Ranking (Fin 2) 2).toRel }

end Grammar

/-- Chichewa (§2, appendix) ranks TEMPLATE, MIRROR (R, C) and the conjunction for (R, A)
freely. -/
def chichewa : Grammar := .free ![.template, .mirror .R .C, .mirrorTemplate .R .A]

/-- Chimwiini (19) has the template alone. -/
def chimwiini : Grammar := .free ![.template]

/-! ### The template alone

The template licenses exactly the templatic realization: a candidate all of whose pairs rise
in the template and which doubles nothing is the template's slots filled by its extensions. -/

private theorem forall₂_mem_replicate_iff {α : Type*} {l : List α} :
    ∀ {c : List α} {n : ℕ}, List.Forall₂ (· ∈ ·) c (List.replicate n l) ↔
      c.length = n ∧ ∀ x ∈ c, x ∈ l
  | [], 0 => by simp
  | [], n + 1 => by simp [List.replicate_succ]
  | _ :: _, 0 => by simp
  | a :: c, n + 1 => by
    simp only [List.replicate_succ, List.forall₂_cons, List.length_cons, add_left_inj,
      List.mem_cons, forall_eq_or_imp, forall₂_mem_replicate_iff]
    tauto

private theorem mem_sections_replicate {α : Type*} {l c : List α} {n : ℕ} :
    c ∈ List.sections (List.replicate n l) ↔ c.length = n ∧ ∀ x ∈ c, x ∈ l := by
  rw [List.mem_sections, forall₂_mem_replicate_iff]

theorem mem_candidates {i : Input} {c : Candidate} :
    c ∈ candidates i ↔ c = templatic i ∨
      ((c.length = i.dedup.length ∨ c.length = i.dedup.length + 1) ∧ ∀ x ∈ c, x ∈ i) ∧
        (∀ x ∈ i, x ∈ c) ∧ c.IsChain (· ≠ ·) := by
  simp only [candidates, Finset.mem_insert, List.mem_toFinset, List.mem_filter, List.mem_append,
    mem_sections_replicate, List.mem_dedup, decide_eq_true_eq, ← or_and_right]

theorem templatic_mem_candidates (i : Input) : templatic i ∈ candidates i :=
  Finset.mem_insert_self _ _

/-- The template alone licenses exactly the strings it admits: every pair rises in its order,
so no suffix doubles. -/
theorem licensedBy_template_iff {i : Input} {c : Candidate} :
    LicensedBy i [.template] c ↔ c ∈ carp.language := by
  rw [mem_carp_language]
  refine ⟨fun h ↦ List.IsChain.sortedLT (List.isChain_iff_getElem.mpr fun k hk ↦ ?_),
    fun hs d hd ↦ ⟨.template, List.mem_singleton_self _, ?_⟩⟩
  · obtain ⟨l, hl, hlic⟩ := h (.pair k) (by
      simp only [demands, List.mem_append, List.mem_map, List.mem_range]
      exact .inl ⟨k, by omega, rfl⟩)
    rw [List.mem_singleton] at hl
    subst hl
    obtain ⟨x, y, hx, hy, hxy⟩ := hlic
    rw [List.getElem?_eq_getElem (by omega), Option.some_inj] at hx hy
    rwa [hx, hy]
  · simp only [demands, List.mem_append, List.mem_map, List.mem_range, List.mem_filter,
      decide_eq_true_eq] at hd
    rcases hd with ⟨k, hk, rfl⟩ | ⟨x, ⟨-, hcount⟩, rfl⟩
    · exact ⟨_, _, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        List.isChain_iff_getElem.mp hs.isChain k (by omega)⟩
    · exact absurd hcount (by simpa using List.nodup_iff_count_le_one.mp hs.nodup x)

theorem licensedBy_template_templatic (i : Input) : LicensedBy i [.template] (templatic i) :=
  licensedBy_template_iff.mpr (mem_carp_language.mpr (templatic_sortedLT i))

/-- A candidate the template alone licenses is the templatic realization. -/
theorem licensedBy_iff_templatic {i : Input} {c : Candidate} (hc : c ∈ candidates i) :
    LicensedBy i [.template] c ↔ c = templatic i := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ licensedBy_template_templatic i⟩
  rcases mem_candidates.mp hc with rfl | ⟨⟨-, hsub⟩, hcov, -⟩
  · rfl
  exact (mem_carp_language.mp (licensedBy_template_iff.mp h)).eq_of_mem_iff
    (templatic_sortedLT i) fun x ↦
      ⟨fun hx ↦ mem_templatic.mpr (hsub x hx), fun hx ↦ hcov x (mem_templatic.mp hx)⟩

/-- Under a template-only grammar, every input has exactly its templatic realization: Chimwiini
(19), where "it is not possible to put these extensions in any other order". -/
theorem chimwiini_outputs (i : Input) : chimwiini.outputs i = {templatic i} := by
  have hrank : chimwiini.rankings = {1} := by decide
  have hord : chimwiini.ranked 1 = [.template] := by decide
  rw [Grammar.outputs, hrank, Finset.singleton_biUnion, hord]
  refine Tableau.optimal_eq_singleton_iff.2 ⟨templatic_mem_candidates i, fun c hc hne ↦ ?_⟩
  have hcl : ¬ LicensedBy i [.template] c := fun h ↦ hne ((licensedBy_iff_templatic hc).mp h)
  show toLex (constraints i [.template] · (templatic i)) < toLex (constraints i [.template] · c)
  have : Unique (Fin [Licensor.template].length) := inferInstanceAs (Unique (Fin 1))
  rw [Pi.Lex.lt_iff_of_unique]
  simp [constraints, hcl, licensedBy_template_templatic]

/-! ### General properties of outputs -/

theorem outputs_isChain_ne {G : Grammar} {i : Input} {c : Candidate} (hc : c ∈ G.outputs i) :
    c.IsChain (· ≠ ·) := by
  obtain ⟨σ, -, hσ⟩ := Finset.mem_biUnion.mp hc
  rcases mem_candidates.mp (Tableau.optimal_subset hσ) with rfl | ⟨-, -, h⟩
  · exact (templatic_sortedLT i).nodup.isChain
  · exact h

theorem licensedBy_of_mem_optimal {i : Input} {order : List Licensor}
    (hT : .template ∈ order) {c : Candidate} (hc : c ∈ (tableau i order).optimal) :
    LicensedBy i order c := by
  by_contra h
  obtain ⟨k, hk, hkT⟩ := List.mem_iff_getElem.mp hT
  have hc' : ∀ j : Fin order.length, constraints i order j c = 1 := fun j ↦ by
    have : ¬ LicensedBy i (order.take (j + 1)) c :=
      fun h' ↦ h (h'.mono (List.take_subset _ _))
    simp [constraints, this]
  have hTk : constraints i order ⟨k, hk⟩ (templatic i) = 0 := by
    have : LicensedBy i (order.take (k + 1)) (templatic i) :=
      (licensedBy_template_templatic i).mono fun l hl ↦ by
        rw [List.mem_singleton] at hl
        subst hl
        exact List.mem_iff_getElem.mpr ⟨k, by simp; omega, by simp [List.getElem_take, hkT]⟩
    simp [constraints, this]
  refine Tableau.notMem_optimal_of_lt (templatic_mem_candidates i) ?_ hc
  show Pi.Lex (· < ·) (· < ·) (fun j ↦ constraints i order j (templatic i))
    (fun j ↦ constraints i order j c)
  refine Pi.lex_lt_of_lt wellFounded_lt (lt_of_le_of_ne (fun j ↦ ?_) fun heq ↦ ?_)
  · rw [hc']
    simp only [constraints, Constraint.binary_apply]
    split_ifs <;> omega
  · have := congrFun heq ⟨k, hk⟩
    rw [hTk, hc'] at this
    exact absurd this (by decide)

/-- A doubled suffix in an output is a mirror override repaired by the template: some
conjunction of the grammar licenses it, the generalization of §2 behind (16). -/
theorem doubling_licensed {G : Grammar} (hT : ∃ p, G.licensor p = .template) {i : Input}
    {c : Candidate} (hc : c ∈ G.outputs i) {x : Ext} (hx : 1 < c.count x) :
    ∃ y, (∃ p, G.licensor p = .mirrorTemplate x y) ∧ i.Inside x y := by
  obtain ⟨σ, -, hσ⟩ := Finset.mem_biUnion.mp hc
  have hTσ : Licensor.template ∈ G.ranked σ := by
    obtain ⟨p, hp⟩ := hT
    exact List.mem_map.mpr ⟨σ.symm p, List.mem_finRange _, by simp [hp]⟩
  have hd : Demand.doubling x ∈ demands c := by
    simp only [demands, List.mem_append, List.mem_map, List.mem_range, List.mem_filter,
      List.mem_dedup, decide_eq_true_eq, reduceCtorEq]
    exact .inr ⟨x, ⟨List.count_pos_iff.mp (by omega), hx⟩, rfl⟩
  obtain ⟨l, hl, hlic⟩ := licensedBy_of_mem_optimal hTσ hσ (.doubling x) hd
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hl
  cases hl' : G.licensor (σ p) with
  | mirrorTemplate x' y =>
    rw [hl'] at hlic
    obtain ⟨rfl, hin, -⟩ := hlic
    exact ⟨y, ⟨σ p, hl'⟩, hin⟩
  | template => rw [hl'] at hlic; exact hlic.elim
  | mirror _ _ => rw [hl'] at hlic; exact hlic.elim

/-! ### Chichewa (§2) -/

/-- Compositionality is asymmetric (2), (10). A reciprocalized causative surfaces only in the
templatic order *-its-an-*; a causativized reciprocal surfaces in the templatic order or in the
mirror order *-an-its-*, so the templatic order is ambiguous and the mirror order is not. -/
theorem asymmetric_compositionality :
    chichewa.outputs [.C, .R] = {[.C, .R]} ∧
      chichewa.outputs [.R, .C] = {[.C, .R], [.R, .C]} := by
  decide +kernel

/-- Both scopes of causative and applicative surface as *-its-il-* (3), (7). -/
theorem causative_applicative :
    chichewa.outputs [.C, .A] = {[.C, .A]} ∧ chichewa.outputs [.A, .C] = {[.C, .A]} := by
  decide +kernel

/-- A reciprocal inside an applicative inside a causative surfaces in the templatic order, with
the causative two slots out of its compositional place, and not in the compositional order
(8). -/
theorem reciprocal_applicative_causative :
    [.C, .A, .R] ∈ chichewa.outputs [.R, .A, .C] ∧
      [.R, .A, .C] ∉ chichewa.outputs [.R, .A, .C] := by
  decide +kernel

/-- A reciprocalized applicative surfaces as *-il-an-*, and an applicativized reciprocal as
*-il-an-* or with the reciprocal doubled, *-an-il-an-*, never as *-an-il-* or *-il-an-il-*
(13), (14), (16), (17). -/
theorem applicative_reciprocal :
    chichewa.outputs [.A, .R] = {[.A, .R]} ∧
      chichewa.outputs [.R, .A] = {[.A, .R], [.R, .A, .R]} := by
  decide +kernel

/-- No output repeats an extension, Menn and MacWhinney's Repeated Morph Constraint (18). -/
theorem repeated_morph (G : Grammar) (i : Input) (x : Ext) : [x, x] ∉ G.outputs i :=
  fun h ↦ by simpa using outputs_isChain_ne h

/-- The appendix's table (48) of the six scopes of three extensions. The model derives every
output Hyman lists but *-an-its-il-an-*, whose doubled reciprocal his tableaux license without
the conjunction, and derives *-an-its-il-* for the scopes with the reciprocal inside the
causative, which he stars: its pairs *-an-its-* and *-its-il-* are each licensed, and the paper
states no constraint on the non-adjacent *-an- … -il-*. -/
theorem three_suffixes :
    chichewa.outputs [.C, .A, .R] = {[.C, .A, .R]} ∧
    chichewa.outputs [.A, .C, .R] = {[.C, .A, .R]} ∧
    chichewa.outputs [.C, .R, .A] = {[.C, .A, .R], [.C, .R, .A, .R]} ∧
    chichewa.outputs [.A, .R, .C] = {[.C, .A, .R], [.A, .R, .C], [.R, .C, .A]} ∧
    chichewa.outputs [.R, .C, .A] =
      {[.R, .A, .R, .C], [.A, .R, .C], [.C, .A, .R], [.C, .R, .A, .R], [.R, .C, .A]} ∧
    chichewa.outputs [.R, .A, .C] =
      {[.R, .A, .R, .C], [.A, .R, .C], [.C, .A, .R], [.C, .R, .A, .R], [.R, .C, .A]} := by
  decide +kernel

/-! ### Applicative and passive (11), (12) -/

/-- What a Chichewa applicative licenses (11). -/
inductive Applicative
  | benefactive
  | recipient
  | instrument
  | locative
  | circumstance
  deriving DecidableEq, Repr

/-- MIRROR (P, A) ranks against TEMPLATE by what the applicative licenses (12), below it for a
benefactive, recipient or instrument, freely for a locative and above it for a circumstance. -/
def passiveGrammar : Applicative → Grammar
  | .locative => .free ![.template, .mirror .P .A]
  | .circumstance => .two (.mirror .P .A) .template
  | _ => .two .template (.mirror .P .A)

/-- An applicative of a passive surfaces as *-il-idw-*, as *-idw-il-* too for a locative, and
only as *-idw-il-* for a circumstance (11). -/
theorem passive (a : Applicative) :
    (passiveGrammar a).outputs [.P, .A] =
      match a with
      | .locative => {[.A, .P], [.P, .A]}
      | .circumstance => {[.P, .A]}
      | _ => {[.A, .P]} := by
  cases a <;> decide +kernel

/-! ### Template morphology and syntax (§3)

The two scopes of causative and applicative surface alike in Chichewa, so the affix order does
not recover the syntactic derivation; the passives (22)–(23) show the derivations differ, the
instrument becoming subject under one scope and the causee under the other. [baker-1985]'s
rules derive the subjects from the scope order, and his single-process architecture would
have kept the two words apart. -/

theorem scope_not_recoverable :
    chichewa.outputs [.C, .A, .P] = {[.C, .A, .P]} ∧
      chichewa.outputs [.A, .C, .P] = {[.C, .A, .P]} := by
  decide +kernel

/-- Under the Mirror Principle the two derivations build different words, *-its-il-idw-* and
*-il-its-idw-*. -/
theorem mirror_predicts_distinct_words :
    (Baker1985.word (.root "lim")
      [(.causative, .suff "its"), (.applicative, .suff "il"), (.passive, .suff "idw")]).toList ≠
    (Baker1985.word (.root "lim")
      [(.applicative, .suff "il"), (.causative, .suff "its"), (.passive, .suff "idw")]).toList := by
  decide +kernel

/-- [baker-1985]'s process for an extension. -/
def Ext.toProcess : Ext → Baker1985.Process
  | .C => .causative
  | .A => .applicative
  | .R => .reciprocal
  | .P => .passive

/-- Chichewa under [baker-1985]'s rules: the Chamorro-type causative, whose causee becomes the
object, and the passive of the first object. -/
def chichewaRules : Baker1985.Grammar := ⟨.chamorro, false⟩

/-! ### The paper's examples -/

/-- An extension by its letter in the template. -/
def Ext.of? : Char → Option Ext
  | 'C' => some .C
  | 'A' => some .A
  | 'R' => some .R
  | 'P' => some .P
  | _ => none

/-- A row's feature as a sequence of extensions. -/
def exts? (r : Datum) (key : String) : Option (List Ext) :=
  (r.feature? key).bind fun s ↦ s.toList.mapM Ext.of?

/-- A row's scope order, innermost first. -/
def scope? (r : Datum) : Option Input := exts? r "scope"

/-- A row's suffix order, innermost first. -/
def suffixes? (r : Datum) : Option Candidate := exts? r "suffixes"

/-- A row's grammar. -/
def grammar? (r : Datum) : Option Grammar :=
  match r.language with
  | "nyan1308" => some chichewa
  | "chim1312" => some chimwiini
  | _ => none

/-- The passive subject a row reports. -/
def subject? (r : Datum) : Option Baker1985.Arg :=
  r.parse? "subject" [("instrument", .applied), ("causee", .agent)]

/-- Every form the paper judges is acceptable exactly when it is an output of its scope. -/
theorem rows_outputs :
    ∀ r ∈ Examples.all, subject? r = none → ∀ G ∈ grammar? r, ∀ i ∈ scope? r,
      ∀ c ∈ suffixes? r, (r.judgment = .acceptable ↔ c ∈ G.outputs i) := by
  decide +kernel

/-- A passive is acceptable exactly when [baker-1985]'s rules, run in the order of scope, make
the reported argument the subject, and its affix order is the one output of either scope
(22)–(23). -/
theorem rows_passive :
    ∀ r ∈ Examples.all, ∀ i ∈ scope? r, ∀ a ∈ subject? r,
      (r.judgment = .acceptable ↔
        ∃ st ∈ Baker1985.outcomes chichewaRules (i.map Ext.toProcess)
          (Baker1985.initial false true), st.subjects = [a]) ∧
      ∀ c ∈ suffixes? r, c ∈ chichewa.outputs i := by
  decide +kernel

end Hyman2003
