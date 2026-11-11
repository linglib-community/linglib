module

public import Linglib.Data.Examples.Hyman2003
public import Linglib.Morphology.Morphotactics.AffixTemplate
public import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
public import Studies.Baker1985
public import Mathlib.Data.List.Sections
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Hyman 2003: suffix ordering in Bantu

Hyman argues that the order of the Bantu verbal extensions, causative, applicative, reciprocal
and passive, follows a Pan-Bantu template, CARP, and not semantic scope or Baker's Mirror
Principle. TEMPLATE licenses sequences in the template's order, and suffix-specific MIRROR
constraints license a sequence in the order of scope as an override; the licensors are ranked,
sometimes freely, and a candidate succeeds at the first licensor down the ranking by which it is
licensed. In Chichewa a reciprocal inside a causative surfaces in the templatic order or the
mirror order, [while the mirror order has only the compositional
reading](##asymmetric_compositionality), and a reciprocal inside an applicative surfaces in the
templatic order or [with the reciprocal doubled](##applicative_reciprocal), a mirror override
that the template repairs. The model reproduces the paper's five tableaux for three extensions
[ranking by ranking](##tableaux_49), and [no licensed candidate repeats a
suffix](##outputs_isChain_ne).

## Implementation notes

* Hyman's tableaux mark the sequences a licensor licenses rather than violations. A candidate is
  licensed by a set of licensors when every suffix lies in a sequence one of them licenses and
  every adjacent pair either rises in the template or is an override one of them licenses. The
  evaluation, a candidate winning at the first rank by which it is licensed, is the
  lexicographic minimization of the profile whose `k`-th entry says whether the top `k + 1`
  licensors fail to license the candidate, so it is a substrate `Tableau`.
* A pair in the template's order needs no licensor of its own, only its two suffixes do: in the
  paper's tableaux *mang-an-its-il-an-* succeeds by MIRROR (R, C) and the conjunction with
  TEMPLATE ranked below both.
* The conjunction `MIRROR (x, y) & TEMPLATE` licenses the three suffixes of an `x … y x`,
  adjacent or not, all or nothing. A candidate doubles a suffix only where a conjunction of the
  grammar licenses the doubling, whatever its rank: the same form also succeeds with the
  conjunction ranked last and not invoked.
* Chichewa's licensors are TEMPLATE, MIRROR (R, C) and the conjunction for (R, A), freely
  ranked, as the appendix ranks them; MIRROR (A, C) is not activated and MIRROR (R, A) alone is
  dominated by TEMPLATE, so neither ever licenses an output.
* Baker's rules run on Chichewa with the Chamorro-type causative and the passive of the
  first object, the asymmetric-object setting of the passives of §3.

## TODO

* The model derives *mang-an-its-il-* for the three scopes with the reciprocal inside the
  causative, a form the paper stars (`three_suffixes`, and the last ranking of `tableaux_49`):
  its two adjacent sequences are licensed by MIRROR (R, C) and TEMPLATE, and nothing in the
  paper's licensing rules out the reciprocal preceding the applicative at a distance.
* The elaborated template CARCP with the short causative, and the phonological templatic
  requirements of §5.

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

theorem mem_carp_language {c : List Ext} : c ∈ carp.language ↔ c.SortedLT := by
  rw [carp.mem_language_iff_sublist (by decide) rfl]
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

/-- The suffixes of a candidate that lie in a sequence a licensor licenses, by position.
TEMPLATE licenses the templatic runs, so every suffix; MIRROR (x, y) the two suffixes of an
adjacent `x y` with `x` inside `y`; and the conjunction the three suffixes of an `x … y x` with
`x` inside `y`, the override and its repair, all or nothing. -/
def Licensor.licenses (i : Input) (c : Candidate) : Licensor → ℕ → Prop
  | .template, _ => True
  | .mirror x y, k => i.Inside x y ∧
      (c[k]? = some x ∧ c[k + 1]? = some y ∨ 1 ≤ k ∧ c[k - 1]? = some x ∧ c[k]? = some y)
  | .mirrorTemplate x y, k => i.Inside x y ∧
      ∃ j ∈ List.range c.length, ∃ m ∈ List.range c.length,
        j < m ∧ c[j]? = some x ∧ c[m]? = some y ∧ c[m + 1]? = some x ∧
          (k = j ∨ k = m ∨ k = m + 1)

/-- A licensor licenses the adjacent pair at a position as an override of the template: MIRROR
(x, y) the pair `x y` with `x` inside `y`, and the conjunction the same pair when the repair
`x` follows. TEMPLATE overrides nothing. -/
def Licensor.overrides (i : Input) (c : Candidate) : Licensor → ℕ → Prop
  | .template, _ => False
  | .mirror x y, k => i.Inside x y ∧ c[k]? = some x ∧ c[k + 1]? = some y
  | .mirrorTemplate x y, k => i.Inside x y ∧
      c[k]? = some x ∧ c[k + 1]? = some y ∧ c[k + 2]? = some x

/-- A licensor licenses the doubling of an extension: the conjunction for `(x, y)` in a
candidate with `x … y x` and `x` inside `y`, a mirror override that the template repairs. -/
def Licensor.doubles (i : Input) (c : Candidate) : Licensor → Ext → Prop
  | .mirrorTemplate x y, z => z = x ∧ i.Inside x y ∧
      ∃ j ∈ List.range c.length, ∃ m ∈ List.range c.length,
        j < m ∧ c[j]? = some x ∧ c[m]? = some y ∧ c[m + 1]? = some x
  | .template, _ => False
  | .mirror _ _, _ => False

instance (i : Input) (c : Candidate) : (l : Licensor) → (k : ℕ) → Decidable (l.licenses i c k)
  | .template, _ => inferInstanceAs (Decidable True)
  | .mirror _ _, _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))
  | .mirrorTemplate _ _, _ => inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, ∃ _ ∈ _, _))

instance (i : Input) (c : Candidate) : (l : Licensor) → (k : ℕ) → Decidable (l.overrides i c k)
  | .template, _ => inferInstanceAs (Decidable False)
  | .mirror _ _, _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .mirrorTemplate _ _, _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (i : Input) (c : Candidate) : (l : Licensor) → (x : Ext) → Decidable (l.doubles i c x)
  | .mirrorTemplate _ _, _ => inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ _ ∈ _, ∃ _ ∈ _, _))
  | .template, _ => inferInstanceAs (Decidable False)
  | .mirror _ _, _ => inferInstanceAs (Decidable False)

/-- A candidate is licensed by a set of licensors when every suffix lies in a sequence one of
them licenses and every adjacent pair either rises in the template or is an override one of them
licenses. -/
def LicensedBy (i : Input) (S : List Licensor) (c : Candidate) : Prop :=
  (∀ k ∈ List.range c.length, ∃ l ∈ S, l.licenses i c k) ∧
    ∀ k ∈ List.range (c.length - 1),
      (∃ x y : Ext, c[k]? = some x ∧ c[k + 1]? = some y ∧ x < y) ∨ ∃ l ∈ S, l.overrides i c k

instance (i : Input) (S : List Licensor) (c : Candidate) : Decidable (LicensedBy i S c) :=
  inferInstanceAs (Decidable ((∀ _ ∈ _, ∃ _ ∈ _, _) ∧ ∀ _ ∈ _, (∃ _ _ : Ext, _) ∨ ∃ _ ∈ _, _))

theorem LicensedBy.mono {i : Input} {S T : List Licensor} (h : S ⊆ T) {c : Candidate}
    (hc : LicensedBy i S c) : LicensedBy i T c :=
  ⟨fun k hk ↦ (hc.1 k hk).imp fun _ hl ↦ ⟨h hl.1, hl.2⟩,
    fun k hk ↦ (hc.2 k hk).imp_right fun ⟨l, hl, ho⟩ ↦ ⟨l, h hl, ho⟩⟩

theorem Input.Inside.ne {i : Input} {x y : Ext} (h : i.Inside x y) : x ≠ y :=
  fun hxy ↦ absurd h.2.2 (hxy ▸ lt_irrefl _)

theorem LicensedBy.isChain_ne {i : Input} {S : List Licensor} {c : Candidate}
    (hc : LicensedBy i S c) : c.IsChain (· ≠ ·) := by
  refine List.isChain_iff_getElem.mpr fun k hk ↦ ?_
  rcases hc.2 k (List.mem_range.mpr (by omega)) with ⟨x, y, hx, hy, hxy⟩ | ⟨l, -, hl⟩
  · rw [List.getElem?_eq_getElem (by omega), Option.some_inj] at hx hy
    rw [hx, hy]
    exact hxy.ne
  · cases l with
    | template => exact hl.elim
    | mirror x y =>
      obtain ⟨hin, hx, hy⟩ := hl
      rw [List.getElem?_eq_getElem (by omega), Option.some_inj] at hx hy
      rw [hx, hy]
      exact hin.ne
    | mirrorTemplate x y =>
      obtain ⟨hin, hx, hy, -⟩ := hl
      rw [List.getElem?_eq_getElem (by omega), Option.some_inj] at hx hy
      rw [hx, hy]
      exact hin.ne

/-! ### Evaluation -/

/-- The candidates of an input under a set of licensors: its templatic realization, and every
sequence over its extensions that realizes each of them and doubles at most one, where one of the
licensors licenses the doubling. -/
def candidates (ls : List Licensor) (i : Input) : Finset Candidate :=
  insert (templatic i)
    ((List.sections (List.replicate i.dedup.length i.dedup) ++
        List.sections (List.replicate (i.dedup.length + 1) i.dedup)).filter fun c ↦
      (∀ x ∈ i, x ∈ c) ∧ ∀ x ∈ i, 1 < c.count x → ∃ l ∈ ls, l.doubles i c x).toFinset

/-- The constraint at rank `k` of a ranking of licensors: violated by a candidate the top
`k + 1` licensors do not license. -/
def constraints (i : Input) (order : List Licensor) : ConstraintSet Candidate (Fin order.length) :=
  fun k ↦ Constraint.binary fun c ↦ ¬ LicensedBy i (order.take (k + 1)) c

/-- Hyman's evaluation under a ranking. A candidate succeeds at the first licensor down the
ranking by which it is licensed, the lexicographic minimum of the cumulative profile. -/
def tableau (i : Input) (order : List Licensor) : Tableau Candidate order.length :=
  ⟨candidates order i, constraints i order⟩

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
def rankings : Finset (Ranking (Fin G.n) G.n) := Ranking.linearExtensions G.order

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

theorem mem_candidates {ls : List Licensor} {i : Input} {c : Candidate} :
    c ∈ candidates ls i ↔ c = templatic i ∨
      ((c.length = i.dedup.length ∨ c.length = i.dedup.length + 1) ∧ ∀ x ∈ c, x ∈ i) ∧
        (∀ x ∈ i, x ∈ c) ∧ ∀ x ∈ i, 1 < c.count x → ∃ l ∈ ls, l.doubles i c x := by
  simp only [candidates, Finset.mem_insert, List.mem_toFinset, List.mem_filter, List.mem_append,
    mem_sections_replicate, List.mem_dedup, decide_eq_true_eq, ← or_and_right]

theorem templatic_mem_candidates (ls : List Licensor) (i : Input) :
    templatic i ∈ candidates ls i :=
  Finset.mem_insert_self _ _

theorem licensedBy_template_iff {i : Input} {c : Candidate} :
    LicensedBy i [.template] c ↔ c ∈ carp.language := by
  rw [mem_carp_language]
  refine ⟨fun h ↦ List.IsChain.sortedLT (List.isChain_iff_getElem.mpr fun k hk ↦ ?_),
    fun hs ↦ ⟨fun _ _ ↦ ⟨.template, List.mem_singleton_self _, trivial⟩, fun k hk ↦ .inl ?_⟩⟩
  · rcases h.2 k (List.mem_range.mpr (by omega)) with ⟨x, y, hx, hy, hxy⟩ | ⟨l, hl, ho⟩
    · rw [List.getElem?_eq_getElem (by omega), Option.some_inj] at hx hy
      rwa [hx, hy]
    · rw [List.mem_singleton] at hl
      subst hl
      exact ho.elim
  · rw [List.mem_range] at hk
    exact ⟨_, _, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      List.isChain_iff_getElem.mp hs.isChain k (by omega)⟩

theorem licensedBy_template_templatic (i : Input) : LicensedBy i [.template] (templatic i) :=
  licensedBy_template_iff.mpr (mem_carp_language.mpr (templatic_sortedLT i))

theorem licensedBy_iff_templatic {ls : List Licensor} {i : Input} {c : Candidate}
    (hc : c ∈ candidates ls i) :
    LicensedBy i [.template] c ↔ c = templatic i := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ licensedBy_template_templatic i⟩
  rcases mem_candidates.mp hc with rfl | ⟨⟨-, hsub⟩, hcov, -⟩
  · rfl
  exact (mem_carp_language.mp (licensedBy_template_iff.mp h)).eq_of_mem_iff
    (templatic_sortedLT i) fun x ↦
      ⟨fun hx ↦ mem_templatic.mpr (hsub x hx), fun hx ↦ hcov x (mem_templatic.mp hx)⟩

-- (19)
theorem chimwiini_outputs (i : Input) : chimwiini.outputs i = {templatic i} := by
  have hrank : chimwiini.rankings = {1} := by decide
  have hord : chimwiini.ranked 1 = [.template] := by decide
  rw [Grammar.outputs, hrank, Finset.singleton_biUnion, hord]
  refine Tableau.optimal_eq_singleton_iff.2 ⟨templatic_mem_candidates _ i, fun c hc hne ↦ ?_⟩
  have hcl : ¬ LicensedBy i [.template] c := fun h ↦ hne ((licensedBy_iff_templatic hc).mp h)
  show toLex (constraints i [.template] · (templatic i)) < toLex (constraints i [.template] · c)
  have : Unique (Fin [Licensor.template].length) := inferInstanceAs (Unique (Fin 1))
  rw [Pi.Lex.lt_iff_of_unique]
  simp [constraints, hcl, licensedBy_template_templatic]

/-! ### General properties of outputs -/

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
  refine Tableau.notMem_optimal_of_lt (templatic_mem_candidates _ i) ?_ hc
  show Pi.Lex (· < ·) (· < ·) (fun j ↦ constraints i order j (templatic i))
    (fun j ↦ constraints i order j c)
  refine Pi.lex_lt_of_lt wellFounded_lt (lt_of_le_of_ne (fun j ↦ ?_) fun heq ↦ ?_)
  · rw [hc']
    simp only [constraints, Constraint.binary_apply]
    split_ifs <;> omega
  · have := congrFun heq ⟨k, hk⟩
    rw [hTk, hc'] at this
    exact absurd this (by decide)

theorem Grammar.template_mem_ranked {G : Grammar} (hT : ∃ p, G.licensor p = .template)
    (σ : Ranking (Fin G.n) G.n) : Licensor.template ∈ G.ranked σ := by
  obtain ⟨p, hp⟩ := hT
  exact List.mem_map.mpr ⟨σ.symm p, List.mem_finRange _, by simp [hp]⟩

/-- No output of a grammar with the template repeats a suffix immediately, the Repeated Morph
Constraint (18): every output is licensed, and nothing licenses the pair `x x`. -/
theorem outputs_isChain_ne {G : Grammar} (hT : ∃ p, G.licensor p = .template) {i : Input}
    {c : Candidate} (hc : c ∈ G.outputs i) : c.IsChain (· ≠ ·) := by
  obtain ⟨σ, -, hσ⟩ := Finset.mem_biUnion.mp hc
  exact (licensedBy_of_mem_optimal (G.template_mem_ranked hT σ) hσ).isChain_ne

-- §2, (16)
theorem doubling_licensed {G : Grammar} {i : Input} {c : Candidate} (hc : c ∈ G.outputs i)
    {x : Ext} (hx : 1 < c.count x) :
    ∃ y, (∃ p, G.licensor p = .mirrorTemplate x y) ∧ i.Inside x y := by
  obtain ⟨σ, -, hσ⟩ := Finset.mem_biUnion.mp hc
  rcases mem_candidates.mp (Tableau.optimal_subset hσ) with rfl | ⟨⟨-, hsub⟩, -, hd⟩
  · exact absurd hx (by simpa using
      List.nodup_iff_count_le_one.mp (templatic_sortedLT i).nodup x)
  · obtain ⟨l, hl, hlic⟩ := hd x (hsub x (List.count_pos_iff.mp (by omega))) hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hl
    cases hl' : G.licensor (σ p) with
    | mirrorTemplate x' y =>
      rw [hl'] at hlic
      obtain ⟨rfl, hin, -⟩ := hlic
      exact ⟨y, ⟨σ p, hl'⟩, hin⟩
    | template => rw [hl'] at hlic; exact hlic.elim
    | mirror _ _ => rw [hl'] at hlic; exact hlic.elim

/-! ### Chichewa (§2) -/

/-- A reciprocalized causative surfaces only as *-its-an-*, a causativized reciprocal as *-its-an-*
or *-an-its-* ((2), (10)). -/
theorem asymmetric_compositionality :
    chichewa.outputs [.C, .R] = {[.C, .R]} ∧
      chichewa.outputs [.R, .C] = {[.C, .R], [.R, .C]} := by
  decide +kernel

-- (3), (7)
theorem causative_applicative :
    chichewa.outputs [.C, .A] = {[.C, .A]} ∧ chichewa.outputs [.A, .C] = {[.C, .A]} := by
  decide +kernel

-- (8)
theorem reciprocal_applicative_causative :
    [.C, .A, .R] ∈ chichewa.outputs [.R, .A, .C] ∧
      [.R, .A, .C] ∉ chichewa.outputs [.R, .A, .C] := by
  decide +kernel

/-- A reciprocalized applicative surfaces as *-il-an-*, an applicativized reciprocal as *-il-an-* or
*-an-il-an-* ((13), (14), (16), (17)). -/
theorem applicative_reciprocal :
    chichewa.outputs [.A, .R] = {[.A, .R]} ∧
      chichewa.outputs [.R, .A] = {[.A, .R], [.R, .A, .R]} := by
  decide +kernel

-- (18)
theorem repeated_morph {G : Grammar} (hT : ∃ p, G.licensor p = .template) (i : Input) (x : Ext) :
    [x, x] ∉ G.outputs i :=
  fun h ↦ by simpa using outputs_isChain_ne hT h

-- (48)
theorem three_suffixes :
    chichewa.outputs [.C, .A, .R] = {[.C, .A, .R]} ∧
    chichewa.outputs [.A, .C, .R] = {[.C, .A, .R]} ∧
    chichewa.outputs [.C, .R, .A] = {[.C, .A, .R], [.C, .R, .A, .R]} ∧
    chichewa.outputs [.A, .R, .C] = {[.C, .A, .R], [.A, .R, .C], [.R, .C, .A]} ∧
    chichewa.outputs [.R, .C, .A] =
      {[.R, .A, .R, .C], [.A, .R, .C], [.C, .A, .R], [.C, .R, .A, .R], [.R, .C, .A, .R],
        [.R, .C, .A]} ∧
    chichewa.outputs [.R, .A, .C] =
      {[.R, .A, .R, .C], [.A, .R, .C], [.C, .A, .R], [.C, .R, .A, .R], [.R, .C, .A, .R],
        [.R, .C, .A]} := by
  decide +kernel

/-- The five tableaux (49) for a reciprocal inside an applicative inside a causative: the winners
under each ranking of TEMPLATE, the conjunction for (R, A) and MIRROR (R, C). The last, with
MIRROR (R, C) over TEMPLATE over the conjunction, has the paper's three winners and the starred
*-an-its-il-*. -/
theorem tableaux_49 :
    (tableau [.R, .A, .C] [.template, .mirrorTemplate .R .A, .mirror .R .C]).optimal =
      {[.C, .A, .R]} ∧
    (tableau [.R, .A, .C] [.mirrorTemplate .R .A, .template, .mirror .R .C]).optimal =
      {[.C, .A, .R], [.C, .R, .A, .R]} ∧
    (tableau [.R, .A, .C] [.mirrorTemplate .R .A, .mirror .R .C, .template]).optimal =
      {[.R, .A, .R, .C], [.R, .C, .A, .R]} ∧
    (tableau [.R, .A, .C] [.mirror .R .C, .mirrorTemplate .R .A, .template]).optimal =
      {[.R, .A, .R, .C], [.R, .C, .A, .R]} ∧
    (tableau [.R, .A, .C] [.mirror .R .C, .template, .mirrorTemplate .R .A]).optimal =
      {[.A, .R, .C], [.C, .A, .R], [.R, .C, .A, .R], [.R, .C, .A]} := by
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

-- (11)
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

-- §3
theorem scope_not_recoverable :
    chichewa.outputs [.C, .A, .P] = {[.C, .A, .P]} ∧
      chichewa.outputs [.A, .C, .P] = {[.C, .A, .P]} := by
  decide +kernel

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
  r.byLanguage [(.nyanja, chichewa), (.chimwiini, chimwiini)]

/-- The passive subject a row reports. -/
def subject? (r : Datum) : Option Baker1985.Arg :=
  r.parse? "subject" [("instrument", .applied), ("causee", .agent)]

/-- Every form the paper judges, the starred *-an-its-il-* apart, is acceptable exactly when it
is an output of its scope. -/
theorem rows_outputs :
    ∀ r ∈ Examples.all, subject? r = none → ∀ G ∈ grammar? r, ∀ i ∈ scope? r,
      ∀ c ∈ suffixes? r, c ≠ [.R, .C, .A] → (r.judgment = .acceptable ↔ c ∈ G.outputs i) := by
  decide +kernel

-- (22), (23) [baker-1985]
theorem rows_passive :
    ∀ r ∈ Examples.all, ∀ i ∈ scope? r, ∀ a ∈ subject? r,
      (r.judgment = .acceptable ↔
        ∃ st ∈ Baker1985.outcomes chichewaRules (i.map Ext.toProcess)
          (Baker1985.initial false true), st.subjects = [a]) ∧
      ∀ c ∈ suffixes? r, c ∈ chichewa.outputs i := by
  decide +kernel

end Hyman2003
