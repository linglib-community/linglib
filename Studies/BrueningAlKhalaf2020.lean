module

public import Linglib.Syntax.WordOrder
public import Linglib.Syntax.Cat
public import Linglib.Data.Examples.BrueningAlKhalaf2020
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.ReduceOption
public import Mathlib.Data.List.Sections
public import Mathlib.Data.List.TFAE

/-!
# Bruening and Al Khalaf 2020: category mismatches in coordination

Coordinated arguments must match in category, and they violate selection in two configurations
only: a clause beside a noun phrase where only noun phrases are selected, and a non-*ly* adverb
beside an adjective before a noun. A clause can be a noun phrase under a null N, which bears none
of the semantic selectional features (S-features) a selector checks. C-selection persists and is
checked against every conjunct; S-features are checked once, at the first stage of a left-to-right
derivation at which the selector meets part of the coordination, against the conjunct on top of the
coordination's stack of features. So [a selector checks the conjunct next to
it](##checkedOnce_eq_toList_nearest), [which it selects in its own
category](##mem_cats_of_mem_nearest), and [the mismatches coordination permits are those of
ellipsis and leftward displacement](##admits_tfae). A non-*ly* adverb has a
silent Adv head, which ellipsis can take with the noun of the first of two coordinated N′s, so
that [it can be coordinated with an adjective that follows it](##nominalCoordination_iff). The
paper's examples are the rows of `Data/Examples/BrueningAlKhalaf2020`.

## Implementation notes

* Coordinated predicates bear the supercategory Pred of Sag, Gazdar, Wasow and Weisler, which is
  all coordination compares, so they need only `Satisfies`. The coordinator is left implicit.
* A clause displaced to the left is related to the selected position by a null operator of
  category NP, which bears S-features, as (72a) requires; any other phrase displaced to the left,
  and every phrase displaced to the right ((94), (95)), leaves its copy there.
* Argument–modifier coordination (§2.1) is not formalized. The questionable (69) counts as
  excluded.

## References

* [bruening-alkhalaf-2020]
* [munn-1993]
* [sag-etal-1985]
* [zhang-2010]
-/

@[expose] public section

namespace BrueningAlKhalaf2020

open PhraseStructure (Cat)
open PhraseStructure.Cat (N V Adj Adv P)

variable {α : Type*}

/-! ### Conjuncts -/

/-- A phrase enters a coordination as a phrase of its own category or, if it is a clause, as the
complement of the null N (78), a noun phrase whose semantically empty head bears no S-features
(§4.2). The null N has category N and default φ-features, which enter number resolution ((93b)). -/
inductive Conjunct where
  /-- A phrase of category `c`, bearing S-features. -/
  | phrase (c : Cat)
  /-- A clause under the null N. -/
  | nullN
  deriving DecidableEq

namespace Conjunct

/-- `x.cat` is the category the conjunct `x` projects. -/
def cat : Conjunct → Cat
  | phrase c => c
  | nullN => N

/-- `ofCat c` lists the conjuncts a phrase of category `c` can be, itself and, for a clause, the
noun phrase the null N makes of it. -/
def ofCat : Cat → List Conjunct
  | .C => [phrase .C, nullN]
  | c => [phrase c]

theorem mem_ofCat {x : Conjunct} {c : Cat} : x ∈ ofCat c ↔ x = phrase c ∨ c = .C ∧ x = nullN := by
  unfold ofCat; split <;> simp_all

theorem eq_phrase_of_mem_ofCat {x : Conjunct} {c : Cat} (h : x ∈ ofCat c) (hx : x ≠ nullN) :
    x = phrase c :=
  (mem_ofCat.1 h).resolve_right fun h ↦ hx h.2

end Conjunct

/-! ### The left-to-right derivation -/

section Derivation

variable [DecidableEq α]

/-- A derivation built from left to right merges the selector, written `none`, and the conjuncts
`some x` in the order they are pronounced, the selector first if it precedes the coordination
(§4.3). -/
def derivationOrder : HeadDirection → List α → List (Option α)
  | .headInitial, cs => none :: cs.map some
  | .headFinal, cs => cs.map some ++ [none]

/-- A selector checks its S-features once, at the first stage of the derivation at which it and
part of the coordination have been merged ((87), (91b)), against the conjunct merged last, which
is on top of the coordination's stack of features ((92)); the features then delete (§4.3). -/
def checkedOnce (d : HeadDirection) (cs : List α) : List α :=
  ((derivationOrder d cs).inits.findSome? fun s ↦
    if none ∈ s then s.reduceOption.getLast? else none).toList

/-- The directionality effect falls out of the derivation: a selector that precedes a coordination
checks its first conjunct, one that follows it the last (§4.3). -/
theorem checkedOnce_eq_toList_nearest (d : HeadDirection) (cs : List α) :
    checkedOnce d cs = (d.nearest cs).toList := by
  cases d
  · rcases cs with _ | ⟨c, _ | _⟩ <;> simp [checkedOnce, derivationOrder, List.reduceOption]
  · have : (cs.map some).reduceOption = cs := by simp [List.reduceOption, List.filterMap_map]
    rw [checkedOnce, derivationOrder.eq_def, List.inits_append, List.findSome?_append,
      List.findSome?_eq_none_iff.2 fun s hs ↦ ite_eq_right_iff.2 fun h ↦ ?_]
    · simp [List.reduceOption_append, this]
    · simpa using ((List.mem_inits _ _).1 hs).subset h

@[simp] theorem mem_checkedOnce {d : HeadDirection} {cs : List α} {x : α} :
    x ∈ checkedOnce d cs ↔ x ∈ d.nearest cs := by
  rw [checkedOnce_eq_toList_nearest, Option.mem_toList, Option.mem_def]

end Derivation

/-! ### Licensing -/

open Conjunct

variable {check : List Conjunct → List Conjunct} {cats : Finset Cat} {d : HeadDirection}
  {ps : List Cat} {p : Cat}

/-- Coordination combines phrases of one category only, since a coordinator selects a category
and projects it (82). -/
def Coordinable (cs : List Conjunct) : Prop :=
  ∀ x ∈ cs, ∀ y ∈ cs, x.cat = y.cat

/-- A coordination satisfies a selector that c-selects `cats` and checks its S-features against
the conjuncts `check cs` when every conjunct is of a c-selected category, c-selection persisting
and being checked against each (85), and none of the conjuncts in `check cs` is the null N, which
cannot check S-features (fn. 27). -/
def Satisfies (check : List Conjunct → List Conjunct) (cats : Finset Cat)
    (cs : List Conjunct) : Prop :=
  (∀ x ∈ cs, x.cat ∈ cats) ∧ nullN ∉ check cs

/-- A coordinated argument is licensed when its conjuncts share a category and satisfy the
selector. -/
def Licensed (check : List Conjunct → List Conjunct) (cats : Finset Cat)
    (cs : List Conjunct) : Prop :=
  Coordinable cs ∧ Satisfies check cats cs

instance : DecidablePred Coordinable :=
  fun cs ↦ inferInstanceAs (Decidable (∀ x ∈ cs, ∀ y ∈ cs, x.cat = y.cat))

instance : DecidablePred (Satisfies check cats) :=
  fun cs ↦ inferInstanceAs (Decidable ((∀ x ∈ cs, x.cat ∈ cats) ∧ nullN ∉ check cs))

instance : DecidablePred (Licensed check cats) :=
  fun cs ↦ inferInstanceAs (Decidable (Coordinable cs ∧ Satisfies check cats cs))

/-- A coordination of phrases of the categories `ps` is admitted under `L` when some choice of
conjuncts for them satisfies `L`. -/
def Admits (L : List Conjunct → Prop) (ps : List Cat) : Prop :=
  ∃ cs ∈ (ps.map ofCat).sections, L cs

instance {L : List Conjunct → Prop} [DecidablePred L] : Decidable (Admits L ps) :=
  inferInstanceAs (Decidable (∃ cs ∈ (ps.map ofCat).sections, L cs))

theorem Admits.mono {L L' : List Conjunct → Prop} (h : ∀ cs, L cs → L' cs) (hL : Admits L ps) :
    Admits L' ps :=
  let ⟨cs, hcs, hL⟩ := hL; ⟨cs, hcs, h cs hL⟩

theorem Admits.satisfies (h : Admits (Licensed check cats) ps) : Admits (Satisfies check cats) ps :=
  h.mono fun _ ↦ And.right

theorem mem_sections_map_ofCat {cs : List Conjunct} :
    cs ∈ (ps.map ofCat).sections ↔ List.Forall₂ (fun x c ↦ x ∈ ofCat c) cs ps := by
  rw [List.mem_sections, List.forall₂_map_right_iff]

theorem Admits.forall_mem {L : List Conjunct → Prop} {P : Conjunct → Prop} {Q : Cat → Prop}
    (h : Admits L ps) (hL : ∀ cs, L cs → ∀ x ∈ cs, P x) (hQ : ∀ x c, x ∈ ofCat c → P x → Q c) :
    ∀ p ∈ ps, Q p := by
  obtain ⟨cs, hcs, hcs'⟩ := h
  have hP := hL cs hcs'
  clear hcs'
  induction mem_sections_map_ofCat.1 hcs with
  | nil => simp
  | cons hxp _ ih =>
    rw [List.forall_mem_cons] at hP ⊢
    exact ⟨hQ _ _ hxp hP.1, ih (mem_sections_map_ofCat.2 ‹_›) hP.2⟩

theorem licensed_swap_reverse {cs : List Conjunct} :
    Licensed (checkedOnce d.swap) cats cs.reverse ↔ Licensed (checkedOnce d) cats cs := by
  simp [Licensed, Coordinable, Satisfies, checkedOnce_eq_toList_nearest,
    HeadDirection.nearest_swap_reverse]

-- §3.1, p. 33
theorem admits_swap_reverse :
    Admits (Licensed (checkedOnce d.swap) cats) ps.reverse ↔
      Admits (Licensed (checkedOnce d) cats) ps := by
  simp only [Admits, mem_sections_map_ofCat]
  refine ⟨fun ⟨cs, hcs, h⟩ ↦ ⟨cs.reverse, ?_, ?_⟩, fun ⟨cs, hcs, h⟩ ↦ ⟨cs.reverse, ?_, ?_⟩⟩
  · rwa [← List.forall₂_reverse_iff, List.reverse_reverse]
  · rwa [← licensed_swap_reverse, List.reverse_reverse]
  · exact List.forall₂_reverse_iff.2 hcs
  · exact licensed_swap_reverse.2 h

-- §3.2
theorem mem_cats_or_of_admits (h : Admits (Satisfies check cats) ps) :
    ∀ p ∈ ps, p ∈ cats ∨ p = .C ∧ N ∈ cats :=
  h.forall_mem (fun _ h ↦ h.1) fun x _ hx hc ↦ by
    rcases mem_ofCat.1 hx with rfl | ⟨rfl, rfl⟩
    exacts [.inl hc, .inr ⟨rfl, hc⟩]

/-- The phrase next to the selector is selected in its own category (§3.1). -/
theorem mem_cats_of_mem_nearest (h : Admits (Licensed (checkedOnce d) cats) ps) :
    ∀ p ∈ d.nearest ps, p ∈ cats := by
  have key {ps : List Cat} (h : Admits (Licensed (checkedOnce .headInitial) cats) ps) :
      ∀ p ∈ ps.head?, p ∈ cats := by
    obtain ⟨cs, hcs, -, hsel, hS⟩ := h
    cases mem_sections_map_ofCat.1 hcs with
    | nil => simp
    | @cons x p _ _ hxp _ =>
      intro q hq
      obtain rfl := Option.mem_some_iff.1 hq
      have := hsel x List.mem_cons_self
      rwa [eq_phrase_of_mem_ofCat hxp fun h ↦ hS (by simp [h])] at this
  cases d
  · exact key h
  · simpa [List.head?_reverse] using key (admits_swap_reverse (d := .headFinal) |>.2 h)

/-- A phrase displaced to the left is related to the position its selector selects by a phrase of
category `displacedLeft c`: a clause, base-generated in an Ā-position, by a null operator of
category NP (p. 21), and any other phrase by its copy. -/
def displacedLeft (c : Cat) : Cat := if c = .C then N else c

/-- The mismatches coordination permits are those of ellipsis and of leftward displacement: a
phrase of a category the selector does not c-select can be coordinated iff it can be stranded by
ellipsis of the selector ((80)), iff it can be displaced to the left, and iff it is a clause where
noun phrases are selected (§3.2). -/
theorem admits_tfae (hp : p ∉ cats) : List.TFAE
    [∃ q, Admits (Licensed (checkedOnce d) cats) [q, p] ∨
        Admits (Licensed (checkedOnce d) cats) [p, q],
      Admits (Licensed (fun _ ↦ []) cats) [p],
      Admits (Licensed (checkedOnce d) cats) [displacedLeft p],
      p = .C ∧ N ∈ cats] := by
  tfae_have 1 → 4 := by
    rintro ⟨q, h | h⟩ <;> exact (mem_cats_or_of_admits h.satisfies p (by simp)).resolve_left hp
  tfae_have 2 → 4 := fun h ↦ (mem_cats_or_of_admits h.satisfies p (by simp)).resolve_left hp
  tfae_have 3 → 4 := fun h ↦ by
    have := mem_cats_of_mem_nearest h (displacedLeft p) (by cases d <;> rfl)
    by_cases hC : p = .C
    · exact ⟨hC, by simpa [displacedLeft, hC] using this⟩
    · exact absurd (by simpa [displacedLeft, hC] using this) hp
  tfae_have 4 → 1 := by
    rintro ⟨rfl, hN⟩
    refine ⟨N, ?_⟩
    cases d
    · exact .inl ⟨[phrase N, nullN], by simp [ofCat],
        by simp [Licensed, Coordinable, Satisfies, cat, hN, checkedOnce_eq_toList_nearest]⟩
    · exact .inr ⟨[nullN, phrase N], by simp [ofCat],
        by simp [Licensed, Coordinable, Satisfies, cat, hN, checkedOnce_eq_toList_nearest]⟩
  tfae_have 4 → 2 := by
    rintro ⟨rfl, hN⟩
    exact ⟨[nullN], by simp [ofCat], by simp [Licensed, Coordinable, Satisfies, cat, hN]⟩
  tfae_have 4 → 3 := by
    rintro ⟨rfl, hN⟩
    refine ⟨[phrase N], by simp [ofCat, displacedLeft], ?_⟩
    cases d <;> simp [Licensed, Coordinable, Satisfies, cat, hN, checkedOnce_eq_toList_nearest]
  tfae_finish

-- fn. 30
theorem mem_cats_of_admits_id (h : Admits (Satisfies id cats) ps) : ∀ p ∈ ps, p ∈ cats :=
  h.forall_mem (P := fun x ↦ x.cat ∈ cats ∧ x ≠ nullN)
    (fun _ h x hx ↦ ⟨h.1 x hx, fun e ↦ h.2 (e ▸ hx)⟩)
    fun x _ hx ⟨hc, hn⟩ ↦ by rwa [eq_phrase_of_mem_ofCat hx hn] at hc

/-! ### Adverbs -/

/-- The head that makes an adverb of an adjective (97) is silent in *once*, *soon* and *now* and
the suffix *-ly* elsewhere. Both are semantically empty (98). -/
inductive AdvHead where
  /-- The silent head of *once*, *soon* and *now*. -/
  | silent
  /-- The suffix *-ly*. -/
  | ly
  deriving DecidableEq, Fintype

/-- Two prenominal modifiers, each an adjective (`none`) or an adverb with its head, can be
coordinated as N′s with the first noun elided (102) when the PF ban on adverbs modifying N′ (99)
finds no Adv head on either. Ellipsis can take the Adv head of the first along with the noun only
if it is silent, empty in sound as well as meaning ((103)). -/
def NominalCoordination (m₁ m₂ : Option AdvHead) : Prop :=
  (∀ h ∈ m₁, h = .silent) ∧ m₂ = none

/-- A displaced prenominal modifier escapes the ban on adverbs modifying N′ when its copy adjoined
to N′ can be partial, leaving out its Adv head ((100)), which it can only if the head is silent
(pp. 31–32). -/
def Displaced (m : Option AdvHead) : Prop :=
  ∀ h ∈ m, h = .silent

instance (m₁ m₂ : Option AdvHead) : Decidable (NominalCoordination m₁ m₂) :=
  inferInstanceAs (Decidable ((∀ h ∈ m₁, h = .silent) ∧ m₂ = none))

instance : DecidablePred Displaced := fun m ↦ inferInstanceAs (Decidable (∀ h ∈ m, h = .silent))

/-- A non-*ly* adverb can be coordinated with an adjective before a noun, if the adjective comes
last; an adverb in *-ly* cannot (p. 15). -/
theorem nominalCoordination_iff {m₁ m₂ : Option AdvHead} :
    NominalCoordination m₁ m₂ ↔ m₁ ≠ some .ly ∧ m₂ = none := by
  rcases m₁ with _ | _ | _ <;> simp [NominalCoordination]

-- (56), (57)
theorem displaced_iff {m : Option AdvHead} : Displaced m ↔ m ≠ some .ly := by
  rcases m with _ | _ | _ <;> simp [Displaced]

/-! ### The paper's examples -/

open Examples

/-- `catOf? s` is the category the paper's label `s` names. -/
def catOf? (s : String) : Option Cat :=
  [("NP", N), ("AP", Adj), ("AdvP", Adv), ("PP", P), ("CP", Cat.C), ("VP", V)].lookup s

/-- `phrases? e` lists the categories of a row's conjuncts, in order. -/
def phrases? (e : Datum) : Option (List Cat) := (e.features "conjunct").mapM catOf?

/-- `selects? e` is the set of categories a row's selector c-selects. -/
def selects? (e : Datum) : Option (Finset Cat) :=
  ((e.features "selects").mapM catOf?).map List.toFinset

/-- `side? e` says whether a row's selector precedes or follows what it selects. -/
def side? (e : Datum) : Option HeadDirection :=
  e.parse? "selector" [("precedes", .headInitial), ("follows", .headFinal)]

/-- `modifiers? e` lists a row's prenominal modifiers, in order. -/
def modifiers? (e : Datum) : Option (List (Option AdvHead)) :=
  (e.features "modifier").mapM
    ([("AP", none), ("non-ly AdvP", some .silent), ("-ly AdvP", some .ly)].lookup ·)

theorem construction_rows : ∀ e ∈ Examples.all, e.feature? "construction" ∈ [some "predicate",
    some "argument", some "ellipsis", some "leftward displacement", some "rightward displacement",
    some "prenominal", some "displaced modifier"] := by
  decide

-- (20)–(22), (51b)
theorem predicate_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "predicate" →
    ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e, ∃ d ∈ side? e,
      (Admits (Satisfies (checkedOnce d) cats) ps ↔ e.judgment = .acceptable) := by
  decide

/-- The model decides the arguments, alone or coordinated, before or after their selector
((2)–(3), (39)–(43), (49)–(51), (64), (68)–(69), (77)). -/
theorem argument_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "argument" →
    ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e, ∃ d ∈ side? e,
      (Admits (Licensed (checkedOnce d) cats) ps ↔ e.judgment = .acceptable) := by
  decide

-- (41), (43)
theorem argument_rows_first : ∀ e ∈ Examples.all, e.feature? "construction" = some "argument" →
    side? e = some .headFinal → 2 ≤ (e.features "conjunct").length →
    ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e,
      (Admits (Licensed (List.take 1) cats) ps ↔ e.judgment ≠ .acceptable) := by
  decide

-- (54), (55), (60), (62), (63b), (76)
theorem ellipsis_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "ellipsis" →
    ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e,
      (Admits (Licensed (fun _ ↦ []) cats) ps ↔ e.judgment = .acceptable) := by
  decide

-- (59), (61), (63a), (71), (72)
theorem leftward_rows : ∀ e ∈ Examples.all,
    e.feature? "construction" = some "leftward displacement" →
    ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e, ∃ d ∈ side? e,
      (Admits (Licensed (checkedOnce d) cats) (ps.map displacedLeft) ↔
        e.judgment = .acceptable) := by
  decide

-- (73), (74)
theorem rightward_rows : ∀ e ∈ Examples.all,
    e.feature? "construction" = some "rightward displacement" →
    ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e, ∃ d ∈ side? e,
      (Admits (Licensed (checkedOnce d) cats) ps ↔ e.judgment = .acceptable) := by
  decide

-- (44), p. 15, (56a), (57a)
theorem prenominal_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "prenominal" →
    ∃ ms ∈ modifiers? e,
      ((ms = [none] ∨ ∃ m₁ m₂, ms = [m₁, m₂] ∧ NominalCoordination m₁ m₂) ↔
        e.judgment = .acceptable) := by
  decide

-- (56b), (56c), (57b), (57c), (58), (101d)
theorem displaced_modifier_rows : ∀ e ∈ Examples.all,
    e.feature? "construction" = some "displaced modifier" →
    ∃ ms ∈ modifiers? e, ((∃ m, ms = [m] ∧ Displaced m) ↔ e.judgment = .acceptable) := by
  decide

end BrueningAlKhalaf2020
