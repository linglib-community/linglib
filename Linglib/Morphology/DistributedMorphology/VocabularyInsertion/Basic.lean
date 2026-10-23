module

public import Linglib.Morphology.DistributedMorphology.Neighborhood
public import Linglib.Morphology.Exponence.Select
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Vocabulary Insertion

A Vocabulary Item pairs its site with the exponent that realizes it. The site is the finite set of
positioned features the item mentions, `(0, f)` for a feature it spells out at its own terminal and
`(i, f)` for one it requires of the terminal at offset `i`, its contextual environment `/ __ ]X]`.
An item applies in a neighborhood that bears every positioned feature of its site, so one item is
more specific than another exactly when its site is larger. Form and meaning share the type, an
alloseme being an item whose exponent is a denotation (`DistributedMorphology/Allosemy.lean`). The
items of List 2 compete for insertion at each terminal, and the Subset Principle picks the
applicable item whose site is largest. The competition is the shared exponence engine's selection
by specificity, so it inherits that engine's laws: Impoverishment changes the winner only by
deleting a feature the winning item mentions, and an antihomophonous vocabulary realizes no ABA
pattern across nested neighborhoods.

## Main definitions

* `DistributedMorphology.VocabularyItem`: a site and its exponent; `fs ⟷ e` is the context-free
  item spelling out the finite set `fs`.
* `DistributedMorphology.VocabularyItem.specificity`: the number of features an item puts on its
  terminal, then the number it puts on the context.
* `DistributedMorphology.winner?`, `DistributedMorphology.subsetPrinciple`: the Subset
  Principle's winning item and its exponent.

## Main statements

* `DistributedMorphology.VocabularyItem.applySet_subset_iff`: an item is more specific than another
  exactly when its site contains the other's.
* `DistributedMorphology.winner?_isElsewhereWinner`: the winner is an Elsewhere winner of the
  shared core.
* `DistributedMorphology.winner?_eq_head?_applicable`: over a vocabulary listed by non-increasing
  specificity, the winner is the first applicable item.
* `DistributedMorphology.winner?_retreat`: deleting features from the neighborhood can only make
  the winner less specific, retreat to the general case.
* `DistributedMorphology.isContiguous_subsetPrinciple`: an antihomophonous vocabulary realizes
  contiguous patterns over neighborhoods ordered by inclusion.

## References

* [halle-marantz-1993]
* [halle-1997]
* [mcginnis-2013]
* [arregi-nevins-2012]
-/

@[expose] public section

namespace DistributedMorphology

/-- A Vocabulary Item pairs the finite set of positioned features it mentions, those it spells
out at offset `0` and those it requires of the terminals at other offsets, with its exponent. -/
@[ext]
structure VocabularyItem (F E : Type*) where
  /-- The positioned features the item mentions. -/
  site : Finset (ℤ × F)
  /-- The exponent the item inserts. -/
  exponent : E

variable {F E : Type*}

namespace VocabularyItem

/-- Items are compared field by field, so two sites listing the same features in different orders
are equal. -/
instance [DecidableEq F] [DecidableEq E] : DecidableEq (VocabularyItem F E) :=
  fun _ _ ↦ decidable_of_iff _ VocabularyItem.ext_iff.symm

/-- The context-free item spelling out the features `fs` at its own terminal. -/
def ofFeatures (fs : Finset F) (e : E) : VocabularyItem F E := ⟨fs.map (.sectR 0 F), e⟩

/-- The features the item spells out at its own terminal. -/
def features [DecidableEq F] (i : VocabularyItem F E) : Finset F :=
  (i.site.filter (·.1 = 0)).image Prod.snd

end VocabularyItem

/-- `fs ⟷ e` is the context-free Vocabulary Item spelling out `fs` as `e`. -/
scoped infixr:25 " ⟷ " => VocabularyItem.ofFeatures

namespace VocabularyItem

variable {fs : Finset F} {e : E} {x : ℤ × F}

@[simp] theorem site_ofFeatures : (fs ⟷ e).site = fs.map (.sectR 0 F) := rfl

@[simp] theorem exponent_ofFeatures : (fs ⟷ e).exponent = e := rfl

@[simp] theorem mem_site_ofFeatures : x ∈ (fs ⟷ e).site ↔ x.1 = 0 ∧ x.2 ∈ fs := by
  obtain ⟨i, f⟩ := x
  simp [eq_comm, and_comm]

@[simp] theorem mem_features [DecidableEq F] {i : VocabularyItem F E} {f : F} :
    f ∈ i.features ↔ (0, f) ∈ i.site := by
  simp [features]

@[simp] theorem features_ofFeatures [DecidableEq F] : (fs ⟷ e).features = fs := by
  ext; simp

end VocabularyItem

end DistributedMorphology

namespace DistributedMorphology.VocabularyItem

open Morphology.Exponence

variable {F E : Type*} {i j : VocabularyItem F E} {n : Neighborhood (Finset F)}

/-- A Vocabulary Item exposes the shared exponence interface: its contexts are neighborhoods, and
it applies in those bearing every positioned feature of its site. -/
instance : Rule (VocabularyItem F E) (Neighborhood (Finset F)) E :=
  ⟨exponent, fun i n ↦ ∀ x ∈ i.site, x ∈ n⟩

theorem applies_iff : Applies i n ↔ ∀ x ∈ i.site, x ∈ n := Iff.rfl

theorem applies_iff_subset_toFinset [DecidableEq F] : Applies i n ↔ i.site ⊆ n.toFinset := by
  simp [applies_iff, Finset.subset_iff]

theorem applies_iff_ofFinset_subset [DecidableEq F] :
    Applies i n ↔ Neighborhood.ofFinset i.site ⊆ n := by
  rw [applies_iff_subset_toFinset]
  exact (Neighborhood.gc_ofFinset_toFinset _ _).symm

theorem applySet_eq [DecidableEq F] : applySet i = Set.Ici (Neighborhood.ofFinset i.site) :=
  Set.ext fun _ ↦ applies_iff_ofFinset_subset

@[simp] theorem applies_ofFeatures {fs : Finset F} {e : E} :
    Applies (fs ⟷ e) n ↔ fs ⊆ n.focus := by
  simp [applies_iff, Neighborhood.mem_def, Finset.subset_iff]

theorem elsewhere_applies (e : E) (n : Neighborhood (Finset F)) :
    Applies ((∅ : Finset F) ⟷ e) n := by
  simp [applies_iff]

theorem applies_mono {n' : Neighborhood (Finset F)} (h : Applies i n) (hn : n ⊆ n') :
    Applies i n' :=
  fun _ hx ↦ Neighborhood.mem_of_subset hn (h _ hx)

/-- Specificity is reverse inclusion of sites: an item applies in fewer neighborhoods exactly when
its site is larger, since principal up-sets are ordered reversely to their generators. -/
theorem applySet_subset_iff : applySet i ⊆ applySet j ↔ j.site ⊆ i.site := by
  classical
  rw [applySet_eq, applySet_eq, Set.Ici_subset_Ici, Neighborhood.ofFinset_subset_ofFinset]

theorem applySet_ssubset_iff : applySet i ⊂ applySet j ↔ j.site ⊂ i.site := by
  simp only [Set.ssubset_def, Finset.ssubset_def, applySet_subset_iff]

/-- An item's specificity counts the features its site puts on the terminal, then those it puts
on the context: the terminal's features decide, as the Subset Principle chooses the item
matching most of them ([halle-1997]), and context breaks ties ([mcginnis-2013]). -/
def specificity (i : VocabularyItem F E) : ℕ ×ₗ ℕ :=
  toLex ((i.site.filter (·.1 = 0)).card, (i.site.filter (·.1 ≠ 0)).card)

theorem specificity_lt_of_applySet_ssubset (hij : applySet i ⊂ applySet j) :
    j.specificity < i.specificity := by
  classical
  have hs := applySet_ssubset_iff.1 hij
  have h₀ := Finset.filter_subset_filter (·.1 = 0) hs.subset
  have h₁ := Finset.filter_subset_filter (·.1 ≠ 0) hs.subset
  refine Prod.Lex.toLex_lt_toLex.mpr ((Finset.card_le_card h₀).lt_or_eq.imp id fun heq ↦
    ⟨heq, Finset.card_lt_card (h₁.ssubset_of_ne fun h₂ ↦ hs.ne ?_)⟩)
  rw [← Finset.filter_union_filter_not_eq (·.1 = 0) j.site,
    ← Finset.filter_union_filter_not_eq (·.1 = 0) i.site,
    Finset.eq_of_subset_of_card_le h₀ heq.ge]
  exact congrArg (_ ∪ ·) h₂

@[simp] theorem not_specificity_lt_elsewhere (i : VocabularyItem F E) (e : E) :
    ¬ i.specificity < ((∅ : Finset F) ⟷ e).specificity := by
  simp [specificity, Prod.Lex.toLex_lt_toLex]

instance [DecidableEq F] :
    DecidableRel (Applies : VocabularyItem F E → Neighborhood (Finset F) → Prop) :=
  fun i n ↦ inferInstanceAs (Decidable (∀ x ∈ i.site, x ∈ n))

end DistributedMorphology.VocabularyItem

namespace DistributedMorphology

open Morphology.Exponence

/-! ### The Subset Principle -/

section SubsetPrinciple

variable {F E : Type*} [DecidableEq F] {items : RuleSet (VocabularyItem F E)}
  {n n' : Neighborhood (Finset F)} {i i' : VocabularyItem F E} {e : E}

/-- The Subset Principle's winning item is the applicable item of greatest `specificity`, the
earliest under ties. -/
def winner? (items : RuleSet (VocabularyItem F E)) (n : Neighborhood (Finset F)) :
    Option (VocabularyItem F E) :=
  items.selectBy VocabularyItem.specificity n

/-- The **Subset Principle** yields the exponent of the most specific item whose site the
neighborhood contains, and `none` iff no item applies. -/
def subsetPrinciple (items : RuleSet (VocabularyItem F E)) (n : Neighborhood (Finset F)) :
    Option E :=
  items.realize VocabularyItem.specificity n

theorem subsetPrinciple_winner_mem (h : subsetPrinciple items n = some e) :
    ∃ i ∈ items, i.exponent = e ∧ Applies i n := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i, RuleSet.selectBy_mem hi, rfl, RuleSet.selectBy_applies hi⟩

theorem winner?_isSome_iff : (winner? items n).isSome ↔ ∃ i ∈ items, Applies i n :=
  RuleSet.selectBy_isSome_iff

/-- On a vocabulary listed by non-increasing specificity, the winner is the first applicable
item. -/
theorem winner?_eq_head?_applicable (h : items.Pairwise fun i j ↦ j.specificity ≤ i.specificity) :
    winner? items n = (items.applicable n).head? :=
  RuleSet.selectBy_eq_head?_applicable h

theorem subsetPrinciple_eq_map_winner? :
    subsetPrinciple items n = (winner? items n).map (·.exponent) := rfl

theorem subsetPrinciple_eq_head?_applicable
    (h : items.Pairwise fun i j ↦ j.specificity ≤ i.specificity) :
    subsetPrinciple items n = ((items.applicable n).head?).map (·.exponent) := by
  rw [subsetPrinciple_eq_map_winner?, winner?_eq_head?_applicable h]

/-- The winner is an Elsewhere winner of the shared core, with no faithfulness hypothesis, since
`VocabularyItem.specificity` is strictly antitone outright. -/
theorem winner?_isElsewhereWinner (h : winner? items n = some i) :
    items.IsElsewhereWinner applySet n i :=
  RuleSet.selectBy_isElsewhereWinner
    (fun _ _ _ _ h ↦ VocabularyItem.specificity_lt_of_applySet_ssubset h) h

theorem subsetPrinciple_realizes (h : subsetPrinciple items n = some e) :
    items.Realizes applySet n e :=
  RuleSet.realize_realizes (fun _ _ _ _ h ↦ VocabularyItem.specificity_lt_of_applySet_ssubset h) h

theorem winner?_eq_of_subset (hsub : n' ⊆ n) (h : winner? items n = some i) (hi : Applies i n') :
    winner? items n' = some i :=
  RuleSet.selectBy_eq_some_of_applies (fun _ _ hs ↦ VocabularyItem.applies_mono hs hsub) h hi

/-- **Retreat to the general case.** Shrinking the neighborhood, deleting features by
Impoverishment, can only make the winner weakly less specific, which is why impoverishment yields
syncretism with a more general exponent rather than a different specific one. -/
theorem winner?_retreat (hsub : n' ⊆ n) (h' : winner? items n' = some i') :
    ∃ i, winner? items n = some i ∧ i'.specificity ≤ i.specificity := by
  have hi' : Applies i' n := VocabularyItem.applies_mono (RuleSet.selectBy_applies h') hsub
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
    (winner?_isSome_iff.mpr ⟨i', RuleSet.selectBy_mem h', hi'⟩)
  exact ⟨i, hi, RuleSet.le_of_selectBy_eq_some hi (RuleSet.selectBy_mem h') hi'⟩

/-- An antihomophonous vocabulary realizes no ABA pattern over neighborhoods ordered by inclusion:
an exponent inserted at two nested neighborhoods is inserted at every neighborhood between
them. -/
theorem isContiguous_subsetPrinciple (hv : items.Antihomophonous) :
    IsContiguous (subsetPrinciple items) :=
  RuleSet.isContiguous_realize_of_monotone hv fun _ _ _ _ hn hs ↦ VocabularyItem.applies_mono hs hn

end SubsetPrinciple

end DistributedMorphology
