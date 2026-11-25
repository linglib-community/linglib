module

public import Linglib.Morphology.Nanosyntax.Lexicalization
public import Linglib.Morphology.Exponence.Select

/-!
# Nanosyntax: lexical entries and the Superset Principle

A lexical entry of nanosyntax pairs an exponent with a stored syntactic object. An entry spells
out an object its stored object contains, the Superset Principle, which is
`Minimalist.Next.SyntacticObject.ContainsOrEq`. When several entries match, the Elsewhere Condition
prefers the one that matches in fewer environments. One entry is at least as specific as another
exactly when the other's stored object contains its own (`LexicalEntry.applySet_subset_iff`), so
`spellout` takes the matching entry with the smallest stored object, an Elsewhere winner
(`spellout_realizes`).

The spellable objects of a lexicon are closed under constituents (`isLowerSpellout_spellout`),
and none has an unlabelled node unless an entry stores one
(`not_hasUnlabelled_of_spellout_isSome`), the two hypotheses of the general results on the
lexicalization algorithm.

`LexicalEntry.MatchesFeatures` is the rival matching by sets of features, which every match by
containment satisfies (`LexicalEntry.Matches.matchesFeatures`), and `featureSpellout` its
spellout, which reads only features (`isFeatureSpellout_featureSpellout`).

## Implementation notes

* Matching is identity with a constituent of the stored object, the formulation in which
  evacuation leaves no trace. Stored objects are unordered, so matching does not read the order
  of daughters.

## TODO

* Matching by identity ignoring traces, and matching of spans.
* The Foot Condition of [taraldsen-et-al-2018], and the matching relation of [taraldsen-2018],
  which pairs a node of the stored object with the root of the syntactic one and asks their
  daughters to match each other both ways.

## References

* [starke-2009]
* [caha-2009]
* [starke-2018]
* [taraldsen-2018]
* [taraldsen-et-al-2018]
* [vandenwyngaerd-2018]
-/

@[expose] public section

namespace Morphology.Nanosyntax

open Morphology Minimalist.Next SyntacticObject

variable {F : Type} {α : Type*}

/-! ### Lexical entries and matching -/

/-- A nanosyntactic lexical entry pairs a stored syntactic object with its exponent. -/
structure LexicalEntry (F : Type) (α : Type*) where
  /-- The stored syntactic object. -/
  tree : SyntacticObject (Option F)
  /-- The exponent. -/
  exponent : α

/-- An entry matches a syntactic object that its stored object contains, the Superset Principle
of [caha-2009]. -/
def LexicalEntry.Matches (e : LexicalEntry F α) (t : SyntacticObject (Option F)) : Prop :=
  e.tree.ContainsOrEq t

instance [DecidableEq F] (e : LexicalEntry F α) (t : SyntacticObject (Option F)) :
    Decidable (e.Matches t) :=
  inferInstanceAs (Decidable (SyntacticObject.ContainsOrEq _ _))

/-- A lexical entry is a rule of the exponence core, applicable where it matches. -/
instance : ExponenceRule (LexicalEntry F α) (SyntacticObject (Option F)) α :=
  ⟨LexicalEntry.exponent, fun e t ↦ e.Matches t⟩

instance [DecidableEq F] :
    DecidableRel (Applies : LexicalEntry F α → SyntacticObject (Option F) → Prop) :=
  fun e t ↦ inferInstanceAs (Decidable (e.Matches t))

@[simp] theorem LexicalEntry.applies_iff {e : LexicalEntry F α} {t : SyntacticObject (Option F)} :
    Applies e t ↔ e.Matches t := Iff.rfl

@[simp] theorem LexicalEntry.exponent_eq (e : LexicalEntry F α) :
    ExponenceRule.exponent e = e.exponent := rfl

/-- One entry is at least as specific as another exactly when the other's stored object contains
its stored object. -/
theorem LexicalEntry.applySet_subset_iff {a b : LexicalEntry F α} :
    applySet a ⊆ applySet b ↔ b.tree.ContainsOrEq a.tree :=
  ⟨fun h ↦ h (Relation.ReflTransGen.refl : a.tree.ContainsOrEq a.tree),
    fun h _ hc ↦ h.trans hc⟩

private theorem numNodes_lt_of_applySet_ssubset {s r : LexicalEntry F α}
    (hlt : applySet s ⊂ applySet r) :
    s.tree.toUnorderedTree.numNodes < r.tree.toUnorderedTree.numNodes := by
  have hcon := LexicalEntry.applySet_subset_iff.mp hlt.le
  refine numNodes_lt_of_contains (contains_iff_containsOrEq_and_ne.2 ⟨hcon, fun heq ↦ ?_⟩)
  exact hlt.not_ge (LexicalEntry.applySet_subset_iff.mpr (heq ▸ Relation.ReflTransGen.refl))

/-! ### Spellout -/

section

variable [DecidableEq F] {L : RuleSet (LexicalEntry F α)} {s t : SyntacticObject (Option F)}

/-- `spellout L t` is the exponent of the matching entry with the smallest stored object, the
first listed on ties, and `none` where no entry matches. -/
def spellout (L : RuleSet (LexicalEntry F α)) (t : SyntacticObject (Option F)) : Option α :=
  L.realize (fun e : LexicalEntry F α ↦ OrderDual.toDual e.tree.toUnorderedTree.numNodes) t

/-- Smallest-object selection realizes the exponent of an Elsewhere winner. -/
theorem spellout_realizes {x : α} (h : spellout L t = some x) : L.Realizes applySet t x :=
  RuleSet.realize_realizes
    (f := fun e : LexicalEntry F α ↦ OrderDual.toDual e.tree.toUnorderedTree.numNodes)
    (fun _ _ _ _ h ↦ OrderDual.toDual_lt_toDual.2 (numNodes_lt_of_applySet_ssubset h)) h

theorem spellout_eq_none_iff : spellout L t = none ↔ ∀ e ∈ L, ¬ e.Matches t := by
  simp [spellout, RuleSet.realize_eq_none_iff, RuleSet.applicable, List.filter_eq_nil_iff]

theorem spellout_isSome_iff : (spellout L t).isSome ↔ ∃ e ∈ L, e.Matches t := by
  simp [spellout, RuleSet.realize, RuleSet.selectBy_isSome_iff]

/-- The spellable objects of a lexicon are closed under constituents. -/
theorem isLowerSpellout_spellout (L : RuleSet (LexicalEntry F α)) :
    IsLowerSpellout (spellout L) := fun _ _ hst ht ↦ by
  obtain ⟨e, he, hm⟩ := spellout_isSome_iff.1 ht
  exact spellout_isSome_iff.2 ⟨e, he, ContainsOrEq.trans hm hst⟩

/-- A lexicon none of whose entries stores an unlabelled node spells out no object with one. -/
theorem not_hasUnlabelled_of_spellout_isSome (hL : ∀ e ∈ L, ¬ HasUnlabelled e.tree)
    (h : (spellout L s).isSome) : ¬ HasUnlabelled s := fun ⟨u, hu, hu'⟩ ↦ by
  obtain ⟨e, he, hm⟩ := spellout_isSome_iff.1 h
  exact hL e he ⟨u, ContainsOrEq.trans hm hu, hu'⟩

end

/-! ### Matching by features -/

/-- The Revised Superset Principle of [vandenwyngaerd-2018]: an entry spells out an object
whose features are among the features of its stored object. -/
def LexicalEntry.MatchesFeatures (e : LexicalEntry F α) (t : SyntacticObject (Option F)) : Prop :=
  features t ⊆ features e.tree

instance [DecidableEq F] (e : LexicalEntry F α) (t : SyntacticObject (Option F)) :
    Decidable (e.MatchesFeatures t) :=
  decidable_of_iff (∀ g ∈ features t, g ∈ features e.tree) Multiset.subset_iff.symm

/-- An entry that matches an object by containment matches it by features. -/
theorem LexicalEntry.Matches.matchesFeatures {e : LexicalEntry F α} {t : SyntacticObject (Option F)}
    (h : e.Matches t) : e.MatchesFeatures t :=
  Multiset.subset_of_le (features_le_of_mem_terms (mem_terms.2 h))

/-- `featureSpellout L t` is the exponent of the entry with the fewest features among those
matching `t` by features, the first listed on ties. -/
def featureSpellout [DecidableEq F] (L : RuleSet (LexicalEntry F α))
    (t : SyntacticObject (Option F)) :
    Option α :=
  ((L.filter fun e ↦ e.MatchesFeatures t).argmin fun e ↦ (features e.tree).card).map (·.exponent)

theorem featureSpellout_isSome_iff [DecidableEq F] {L : RuleSet (LexicalEntry F α)}
    {t : SyntacticObject (Option F)} :
    (featureSpellout L t).isSome ↔ ∃ e ∈ L, e.MatchesFeatures t := by
  rw [featureSpellout, Option.isSome_map, ← Option.ne_none_iff_isSome, Ne, List.argmin_eq_none,
    List.filter_eq_nil_iff]
  simp

theorem isFeatureSpellout_featureSpellout [DecidableEq F] (L : RuleSet (LexicalEntry F α)) :
    IsFeatureSpellout (featureSpellout L) := fun _ _ hst ht ↦ by
  obtain ⟨e, he, hm⟩ := featureSpellout_isSome_iff.1 ht
  exact featureSpellout_isSome_iff.2 ⟨e, he, fun _ hg ↦ hm (hst hg)⟩

end Morphology.Nanosyntax
