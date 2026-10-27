module

public import Linglib.Syntax.WordOrder
public import Linglib.Syntax.Cat
public import Linglib.Data.Examples.BrueningAlKhalaf2020
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.Sections

/-!
# Bruening and Al Khalaf 2020: category mismatches in coordination

Bruening and Al Khalaf argue that coordinated arguments must match in category and may violate
selection in two configurations only, a clause beside a noun phrase where only noun phrases are
selected and a non-*ly* adverb beside an adjective before a noun. The violating conjunct is never
the one next to the selector, and the two violations are those ellipsis and displacement permit.
They derive the clausal case from a null N that makes a noun phrase of a clause but bears none of
the semantic selectional features (S-features) a selector checks, with c-selection checked against
every conjunct and S-features checked once, as soon as possible, in a structure built from left to
right. A coordinate phrase stacks its conjuncts' features by recency, so a selector that precedes it
checks the first conjunct and one that follows it the last, `HeadDirection.nearest`, where the
accounts that make the first conjunct prominent check `List.take 1`. The adverbial case rests on a
silent Adv head that ellipsis or a partial copy can leave out. The paper's examples are the rows of
`Data/Examples/BrueningAlKhalaf2020`.

## Main definitions

* `Conjunct`: a phrase as it enters a coordination, itself or a clause under the null N.
* `Licensed`, `Satisfies`, `Admits`: the conditions on coordinated arguments and predicates.
* `checkedOnce`: the conjunct a selector checks its S-features against, once.
* `NominalCoordination`, `Displaced`: an adverb's two escapes from the ban on modifying a noun.

## Main results

* `mem_cats_of_mem_nearest`: the phrase next to the selector is selected in its own category.
* `mem_cats_or_of_admits`: the only violation is a clause where a noun phrase is selected.
* `exists_admits_iff_admits_elided`: a phrase may violate selection in a coordination exactly when
  ellipsis of the selector may strand it.
* `mem_cats_of_admits_id`: speakers whose S-features persist admit no violation in coordination.
* `nominalCoordination_iff`, `displaced_iff`: a non-*ly* adverb may modify a noun when coordinated
  before an adjective or displaced.
* `argument_rows` and its siblings: the model's verdict on each example is its judgment.

## Implementation notes

* Coordinated predicates bear the supercategory Pred of Sag, Gazdar, Wasow and Weisler, which is
  all coordination compares, so they need only `Satisfies`. The coordinator is left implicit.
* Argument–modifier coordination (§2.1) and the displacement of clauses (§§4.1, 4.5) are not
  formalized. The questionable (69) counts as excluded.

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

variable {α β : Type*}

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

/-- A conjunct bears S-features unless its head is the null N, which is semantically empty
(fn. 27). -/
def Contentful : Conjunct → Prop
  | phrase _ => True
  | nullN => False

instance : DecidablePred Contentful := fun x ↦ by cases x <;> unfold Contentful <;> infer_instance

/-- `ofCat c` lists the conjuncts a phrase of category `c` can be, itself and, for a clause, the
noun phrase the null N makes of it. -/
def ofCat : Cat → List Conjunct
  | .C => [phrase .C, nullN]
  | c => [phrase c]

theorem mem_ofCat {x : Conjunct} {c : Cat} : x ∈ ofCat c ↔ x = phrase c ∨ c = .C ∧ x = nullN := by
  unfold ofCat; split <;> simp_all

theorem eq_phrase_of_mem_ofCat {x : Conjunct} {c : Cat} (h : x ∈ ofCat c) (hx : x.Contentful) :
    x = phrase c := by
  rcases mem_ofCat.1 h with h | ⟨-, rfl⟩
  exacts [h, hx.elim]

end Conjunct

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
and being checked against each (85), and the conjuncts in `check cs` bear S-features (88). -/
def Satisfies (check : List Conjunct → List Conjunct) (cats : Finset Cat)
    (cs : List Conjunct) : Prop :=
  (∀ x ∈ cs, x.cat ∈ cats) ∧ ∀ x ∈ check cs, x.Contentful

/-- A selector on side `d` checks its S-features once, as soon as it can, and they then delete
(§4.3). The coordinate phrase stacks its conjuncts' features by recency (92), so a selector that
precedes it checks the stack of the first conjunct alone ((87), (90)) and one that follows it the
finished stack, whose last conjunct is on top ((92)). -/
def checkedOnce (d : HeadDirection) (cs : List Conjunct) : List Conjunct := (d.nearest cs).toList

@[simp] theorem mem_checkedOnce {cs : List Conjunct} {x : Conjunct} :
    x ∈ checkedOnce d cs ↔ x ∈ d.nearest cs :=
  Option.mem_toList

/-- A coordinated argument is licensed when its conjuncts share a category and satisfy the
selector. -/
def Licensed (check : List Conjunct → List Conjunct) (cats : Finset Cat)
    (cs : List Conjunct) : Prop :=
  Coordinable cs ∧ Satisfies check cats cs

instance : DecidablePred Coordinable := fun _ ↦ by unfold Coordinable; infer_instance

instance : DecidablePred (Satisfies check cats) := fun _ ↦ by unfold Satisfies; infer_instance

instance : DecidablePred (Licensed check cats) := fun _ ↦ by unfold Licensed; infer_instance

/-- A coordination of phrases of the categories `ps` is admitted under `L` when some choice of
conjuncts for them satisfies `L`. -/
def Admits (L : List Conjunct → Prop) (ps : List Cat) : Prop :=
  ∃ cs ∈ (ps.map ofCat).sections, L cs

instance {L : List Conjunct → Prop} [DecidablePred L] : Decidable (Admits L ps) := by
  unfold Admits; infer_instance

theorem Admits.mono {L L' : List Conjunct → Prop} (h : ∀ cs, L cs → L' cs) (hL : Admits L ps) :
    Admits L' ps :=
  let ⟨cs, hcs, hL⟩ := hL; ⟨cs, hcs, h cs hL⟩

theorem Admits.satisfies (h : Admits (Licensed check cats) ps) : Admits (Satisfies check cats) ps :=
  h.mono fun _ ↦ And.right

theorem mem_sections_map_ofCat {cs : List Conjunct} :
    cs ∈ (ps.map ofCat).sections ↔ List.Forall₂ (fun x c ↦ x ∈ ofCat c) cs ps := by
  rw [List.mem_sections, List.forall₂_map_right_iff]

private theorem exists_mem_of_rel_some {R : α → β → Prop} {o : Option α} {b : β}
    (h : Option.Rel R o (some b)) : ∃ a ∈ o, R a b := by
  cases h; exact ⟨_, rfl, ‹_›⟩

private theorem exists_mem_of_forall₂ {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => absurd hb List.not_mem_nil
  | _, _, .cons hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hR⟩ := exists_mem_of_forall₂ h b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hR⟩

theorem Admits.exists_mem {L : List Conjunct → Prop} (h : Admits L ps) :
    ∃ cs, L cs ∧ ∀ p ∈ ps, ∃ x ∈ cs, x ∈ ofCat p :=
  let ⟨cs, hcs, hL⟩ := h; ⟨cs, hL, exists_mem_of_forall₂ (mem_sections_map_ofCat.1 hcs)⟩

/-- A phrase of a category the selector does not c-select can only be a clause under the null N
(§3.2). -/
theorem mem_cats_or_of_admits (h : Admits (Satisfies check cats) ps) :
    ∀ p ∈ ps, p ∈ cats ∨ p = .C ∧ N ∈ cats := by
  obtain ⟨cs, ⟨hsel, -⟩, hcs⟩ := h.exists_mem
  intro p hp
  obtain ⟨x, hx, hxp⟩ := hcs p hp
  rcases mem_ofCat.1 hxp with rfl | ⟨rfl, rfl⟩
  · exact .inl (hsel _ hx)
  · exact .inr ⟨rfl, hsel _ hx⟩

/-- The phrase next to the selector is selected in its own category (§3.1). -/
theorem mem_cats_of_mem_nearest (h : Admits (Satisfies (checkedOnce d) cats) ps) :
    ∀ p ∈ d.nearest ps, p ∈ cats := by
  obtain ⟨cs, hcs, hsel, hS⟩ := h
  intro p hp
  have hrel := HeadDirection.rel_nearest (mem_sections_map_ofCat.1 hcs) d
  rw [Option.mem_def.1 hp] at hrel
  obtain ⟨x, hx, hxp⟩ := exists_mem_of_rel_some hrel
  have := hsel x (HeadDirection.mem_of_mem_nearest hx)
  rwa [eq_phrase_of_mem_ofCat hxp (hS x (mem_checkedOnce.2 hx))] at this

/-- A phrase of a category the selector does not c-select can be coordinated iff it can be stranded
by ellipsis of the selector (§3.3, (80)). -/
theorem exists_admits_iff_admits_elided (hp : p ∉ cats) :
    (∃ q, Admits (Licensed (checkedOnce d) cats) [q, p] ∨
        Admits (Licensed (checkedOnce d) cats) [p, q]) ↔
      Admits (Licensed (fun _ ↦ []) cats) [p] := by
  constructor
  · rintro ⟨q, h | h⟩ <;>
    · rcases mem_cats_or_of_admits h.satisfies p (by simp) with h | ⟨rfl, hNP⟩
      · exact absurd h hp
      · exact ⟨[nullN], by simp [ofCat], by simp [Licensed, Coordinable, Satisfies, hNP, cat]⟩
  · intro h
    rcases mem_cats_or_of_admits h.satisfies p (by simp) with h | ⟨rfl, hNP⟩
    · exact absurd h hp
    refine ⟨N, ?_⟩
    cases d
    · exact .inl ⟨[phrase N, nullN], by simp [ofCat],
        by simp [Licensed, Coordinable, Satisfies, checkedOnce, cat, hNP, Contentful]⟩
    · exact .inr ⟨[nullN, phrase N], by simp [ofCat],
        by simp [Licensed, Coordinable, Satisfies, checkedOnce, cat, hNP, Contentful]⟩

/-- For speakers who reject (3a), whose S-features persist, no conjunct can be a clause under the
null N (fn. 30). -/
theorem mem_cats_of_admits_id (h : Admits (Satisfies id cats) ps) : ∀ p ∈ ps, p ∈ cats := by
  obtain ⟨cs, ⟨hsel, hS⟩, hcs⟩ := h.exists_mem
  intro p hp
  obtain ⟨x, hx, hxp⟩ := hcs p hp
  have := hsel x hx
  rwa [eq_phrase_of_mem_ofCat hxp (hS x hx)] at this

/-! ### Adverbs -/

/-- The head that makes an adverb of an adjective (97) is silent in *once*, *soon* and *now* and
the suffix *-ly* elsewhere. Both are semantically empty (98). -/
inductive AdvHead where
  /-- The silent head of *once*, *soon* and *now*. -/
  | silent
  /-- The suffix *-ly*. -/
  | ly
  deriving DecidableEq, Fintype

/-- When PF deletes the material after a modifier, by ellipsis of the noun in the first of two
coordinated N′s (103) or in the lower copy of a displaced modifier (100), a silent Adv head, empty
in sound and meaning, goes with it, and *-ly* stays. -/
def AdvHead.afterDeletion : AdvHead → Option AdvHead
  | silent => none
  | ly => some ly

/-- Two prenominal modifiers, each an adjective (`none`) or an adverb with its head, can be
coordinated as N′s with the first noun elided (102) when the PF ban on adverbs modifying N′ (99)
finds no Adv head left on either. The ellipsis takes a silent head on the first along with the
noun (103). -/
def NominalCoordination (m₁ m₂ : Option AdvHead) : Prop :=
  m₁.bind AdvHead.afterDeletion = none ∧ m₂ = none

/-- A displaced prenominal modifier, adjoined to the noun phrase, escapes the ban on adverbs
modifying N′ when its lower copy, adjoined to N′, can leave out its Adv head (100). -/
def Displaced (m : Option AdvHead) : Prop :=
  m.bind AdvHead.afterDeletion = none

instance (m₁ m₂ : Option AdvHead) : Decidable (NominalCoordination m₁ m₂) := by
  unfold NominalCoordination; infer_instance

instance : DecidablePred Displaced := fun _ ↦ by unfold Displaced; infer_instance

/-- A non-*ly* adverb can be coordinated with an adjective before a noun, if the adjective comes
last; an adverb in *-ly* cannot (p. 15). -/
theorem nominalCoordination_iff {m₁ m₂ : Option AdvHead} :
    NominalCoordination m₁ m₂ ↔ m₁ ≠ some .ly ∧ m₂ = none := by
  rcases m₁ with _ | _ | _ <;> simp [NominalCoordination, AdvHead.afterDeletion]

/-- The adverbs that may be displaced to modify a noun are the non-*ly* ones ((56), (57)). -/
theorem displaced_iff {m : Option AdvHead} : Displaced m ↔ m ≠ some .ly := by
  rcases m with _ | _ | _ <;> simp [Displaced, AdvHead.afterDeletion]

/-! ### The paper's examples -/

open Examples

/-- `catOf? s` is the category the paper's label `s` names. -/
def catOf? (s : String) : Option Cat :=
  [("NP", N), ("AP", Adj), ("PP", P), ("CP", Cat.C), ("VP", V)].lookup s

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
    some "argument", some "ellipsis", some "prenominal", some "displacement"] := by
  decide

-- (20), (22)
theorem predicate_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "predicate" →
    ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e, ∃ d ∈ side? e,
      (Admits (Satisfies (checkedOnce d) cats) ps ↔ e.judgment = .acceptable) := by
  decide

/-- The model decides the arguments, alone or coordinated, before or after their selector
((2)–(3), (39)–(43), (49)–(50), (64), (68)–(69), (77)). -/
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

-- (54), (55), (60), (62), (76)
theorem ellipsis_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "ellipsis" →
    ∃ ps ∈ phrases? e, ∃ cats ∈ selects? e,
      (Admits (Licensed (fun _ ↦ []) cats) ps ↔ e.judgment = .acceptable) := by
  decide

-- (44), p. 15, (56a), (57a)
theorem prenominal_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "prenominal" →
    ∃ ms ∈ modifiers? e,
      ((ms = [none] ∨ ∃ m₁ m₂, ms = [m₁, m₂] ∧ NominalCoordination m₁ m₂) ↔
        e.judgment = .acceptable) := by
  decide

-- (56b), (57c)
theorem displacement_rows : ∀ e ∈ Examples.all, e.feature? "construction" = some "displacement" →
    ∃ ms ∈ modifiers? e, ((∃ m, ms = [m] ∧ Displaced m) ↔ e.judgment = .acceptable) := by
  decide

end BrueningAlKhalaf2020
