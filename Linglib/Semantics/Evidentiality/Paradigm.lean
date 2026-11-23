module

public import Mathlib.Order.Partition.Finpartition
public import Linglib.Semantics.Evidentiality.Term

/-!
# Evidential paradigms

A language's inventory of evidentials is a `List Evidential`, in order of preference where the
language has one. It expresses the parameters its terms cover, `expressed es`, and is well
formed when its terms cover pairwise disjoint sets. The terms of a well-formed inventory
partition the parameters it expresses, a `Finpartition (expressed es)`.

Where several sources are at hand, the speaker uses the first term of the inventory covering one
of them, `preferred es S`. No term is selected exactly when the inventory expresses none of the
sources (`Evidential.preferred_eq_none`). In a well-formed inventory the term for a single
source is the one covering it, `preferred es {p} = some e ↔ e ∈ es ∧ p ∈ e.covers`
(`Evidential.WellFormed.preferred_singleton_eq_some`), so it does not depend on the order of the
inventory (`Evidential.WellFormed.preferred_singleton_perm`): the order of preference matters
only where sources compete.

## Implementation notes

An inventory is a list and not a function from parameters to terms, since it also records terms
that cover none of the six parameters, synonymous terms, and the order of preference. The
function is recovered as `fun p ↦ preferred es {p}`.

## References

* [aikhenvald-2004]
* [barnes-1984]
* [oswalt-1986]
-/

@[expose] public section

namespace Evidential

variable {es es' l : List Evidential} {e : Evidential} {p : Parameter} {S : Finset Parameter}

/-- The parameters an inventory expresses. -/
def expressed (es : List Evidential) : Finset Parameter := (es.map covers).toFinset.sup id

@[simp] theorem mem_expressed : p ∈ expressed es ↔ ∃ e ∈ es, p ∈ e.covers := by
  simp [expressed, Finset.mem_sup]

/-- An inventory is well formed when its terms are pairwise disjoint, so that no parameter is
covered twice; two entries with the same nonempty coverage count as one term covered twice. -/
def WellFormed (es : List Evidential) : Prop := es.Pairwise fun a b ↦ Disjoint a.covers b.covers

instance : DecidablePred WellFormed := fun es ↦
  inferInstanceAs (Decidable (es.Pairwise fun a b ↦ Disjoint a.covers b.covers))

theorem WellFormed.perm (h : WellFormed es) (hp : es.Perm es') : WellFormed es' :=
  List.Pairwise.perm h hp fun h ↦ h.symm

/-- The paradigm of a well-formed inventory: its terms partition the parameters it expresses. -/
def finpartition (es : List Evidential) (h : WellFormed es) : Finpartition (expressed es) :=
  Finpartition.ofErase (es.map covers).toFinset
    (Finset.supIndep_iff_pairwiseDisjoint.2 fun _ hx _ hy hxy ↦
      (h.map covers fun _ _ ↦ id).forall (List.mem_toFinset.1 hx) (List.mem_toFinset.1 hy) hxy)
    rfl

@[simp] theorem mem_parts_finpartition {h : WellFormed es} {c : Finset Parameter} :
    c ∈ (finpartition es h).parts ↔ c.Nonempty ∧ ∃ e ∈ es, e.covers = c := by
  simp [finpartition, Finset.nonempty_iff_ne_empty]

/-! ### Preferred evidentials -/

/-- The evidential an inventory in order of preference selects for the sources at hand, its
first term covering one of them. -/
def preferred (es : List Evidential) (S : Finset Parameter) : Option Evidential :=
  es.find? fun e ↦ ¬ Disjoint e.covers S

theorem mem_of_preferred_eq_some (h : preferred es S = some e) : e ∈ es :=
  List.mem_of_find?_eq_some h

theorem not_disjoint_of_preferred_eq_some (h : preferred es S = some e) :
    ¬ Disjoint e.covers S := by
  simpa using List.find?_some h

/-- No term is selected exactly when the inventory expresses none of the sources at hand. -/
theorem preferred_eq_none : preferred es S = none ↔ Disjoint (expressed es) S := by
  simp [preferred, expressed, Finset.disjoint_sup_left]

/-- The last term of an inventory is selected when it covers a source at hand and no earlier
term does. -/
theorem preferred_append_singleton_eq_some (he : e ∉ l) :
    preferred (l ++ [e]) S = some e ↔ ¬ Disjoint e.covers S ∧ ∀ x ∈ l, Disjoint x.covers S := by
  simp only [preferred, List.find?_append]
  cases h : l.find? (fun x ↦ decide ¬ Disjoint x.covers S) with
  | none => simp_all [List.find?_eq_none]
  | some x =>
    have hx := List.mem_of_find?_eq_some h
    have := List.find?_some h
    simp only [Option.some_or, Option.some.injEq]
    exact ⟨fun hxe ↦ (he (hxe ▸ hx)).elim, fun ⟨_, hall⟩ ↦ by simp_all⟩

/-- In a well-formed inventory the term for a single source is the term covering it. -/
theorem WellFormed.preferred_singleton_eq_some (h : WellFormed es) :
    preferred es {p} = some e ↔ e ∈ es ∧ p ∈ e.covers := by
  induction es with
  | nil => simp [preferred]
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 h
    by_cases hp : p ∈ a.covers
    · rw [show preferred (a :: l) {p} = some a by simp [preferred, hp], Option.some.injEq,
        List.mem_cons]
      refine ⟨fun h ↦ h ▸ ⟨.inl rfl, hp⟩, ?_⟩
      rintro ⟨rfl | he, hpe⟩
      exacts [rfl, (Finset.disjoint_left.1 (ha e he) hp hpe).elim]
    · rw [show preferred (a :: l) {p} = preferred l {p} by simp [preferred, hp], ih hl,
        List.mem_cons]
      exact ⟨fun ⟨he, hpe⟩ ↦ ⟨.inr he, hpe⟩,
        fun ⟨he, hpe⟩ ↦ ⟨he.resolve_left (by rintro rfl; exact hp hpe), hpe⟩⟩

/-- The term of a well-formed inventory for a single source does not depend on the order of
preference. -/
theorem WellFormed.preferred_singleton_perm (h : WellFormed es) (hp : es.Perm es')
    (p : Parameter) : preferred es {p} = preferred es' {p} :=
  Option.ext fun e ↦ by
    rw [h.preferred_singleton_eq_some, (h.perm hp).preferred_singleton_eq_some, hp.mem_iff]

end Evidential
