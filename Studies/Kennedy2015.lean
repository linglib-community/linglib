module

public import Linglib.Fragments.English.NumeralModifiers
public import Linglib.Semantics.Quantification.Numerals.Basic
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Pragmatics.NeoGricean.Basic

/-!
# Kennedy (2015): A "de-Fregean" Semantics (and Neo-Gricean Pragmatics) for Modified and Unmodified Numerals

This file formalizes the de-Fregean semantics of Kennedy: a numeral, bare or modified,
is a quantifier over degree properties, true of a property when its greatest degree stands in
the numeral's relation to the number, `max{n | D(n)} = m` for the bare numeral ((29)), `> m` and
`< m` for the Class A modifiers *more than* and *fewer than* ((41)), `≥ m` and `≤ m` for the
Class B modifiers *at least* and *at most* ((42)); this is the substrate's degree quantifier
`Degree.MaxIn` at the comparison's interval. Applied to the degrees a count reaches it is the
comparison of the count, so bare numerals are two-sided without a Horn scale
(`maxIn_interval_Iic`), and the one-sided readings of numerals under root modals ((31)–(34)) are
matters of scope, `Degree.HighScope`: a bare numeral scoping over a necessity modal names the
least count the modal requires and over a possibility modal the greatest it allows
(`necessity_wide_iff`, `possibility_wide_iff`).

The two classes of Nouwen differ in the ordering they express ((4)), exclusive for
Class A and inclusive for Class B. Over the English modifiers, whose class the Fragment reads
off the construction, this is a fact about every reading, stated in Kamp's classes of modifiers:
a Class A reading is disjoint from the number's two-sided meaning and a Class B reading is
extensive (`classA_exclusive`, `classB_inclusive`).

The ignorance inferences of the Class B modifiers are Sauerland's primary implicatures ((43))
over Kennedy's single alternative set, the five forms of one numeral ((46)): *at least m* is
asymmetrically entailed by the bare numeral and by *more than m* and by no other alternative, so
asserting it commits the speaker to ignorance of both, and *at most m* likewise with *fewer than
m* ((47), `commitment_ge`, `commitment_le`), while the bare numeral and the Class A forms are
entailed by no alternative at all and carry no ignorance (`commitment_eq_Iic`); and no primary
implicature strengthens to a secondary one ((44)), each of a Class B form contradicting the
assertion together with the other (`not_isSecondaryImplicature`).

## Implementation notes

The worlds of the pragmatics are counts, so a form's content is the set `c.interval m` of counts,
the alternatives are the five forms of the numeral, one for each `Degree.Comparison`, and the
neo-Gricean operators are `NeoGricean.commitment` and `NeoGricean.IsSecondaryImplicature`. A
root modal is the quantifier `every R` or `GQ.some R` over its accessible worlds `R`, and
the numeral's two scopes are `Degree.LowScope` and `Degree.HighScope` of `MaxIn {m}` over it. The
interactions of Class B modifiers with root modals (Section 4.2) are not formalized.

## References

* [kennedy-2015]
* [sauerland-2004]
* [nouwen-2010]
-/

@[expose] public section

namespace Kennedy2015

open Degree Numerals NeoGricean Quantifier Quantifier.GQ Set

/-! ### The de-Fregean semantics (Section 3)

(29), (41), (42): the numeral form `c m` is true of a degree property when its greatest degree
stands in the relation `c` to `m`, the substrate's `MaxIn (c.interval m)`. -/

theorem maxIn_interval_Iic (c : Comparison) (m n : ℕ) :
    MaxIn (c.interval m) (Iic n) ↔ n ∈ c.interval m :=
  maxIn_Iic

/-! ### The two classes (Section 1) -/

section Classes

open English.NumeralModifiers
open scoped Denotes

attribute [local simp] moreThan fewerThan over under atLeast atMost minimally maximally upTo from_
  exactly precisely about around approximately roughly almost nearly approximator shortOf

/-- Each reading of a Class A modifier (4a) is disjoint from the two-sided meaning of its number. -/
theorem classA_exclusive : ∀ w ∈ inventory, w.modifierClass = some .classA →
    ∀ m ∈ ⟦w⟧, ∀ n, Disjoint (m {n}) {n} := by
  simp [inventory, NumeralModifier.modifierClass, ModifierKind.modifierClass]

/-- A Class B modifier (4b) expresses an inclusive ordering, so each of its readings is extensive:
the number satisfies the modified numeral. -/
theorem classB_inclusive : ∀ w ∈ inventory, w.modifierClass = some .classB →
    ∀ m ∈ ⟦w⟧, Modifier.IsExtensive m := by
  simp [inventory, NumeralModifier.modifierClass, ModifierKind.modifierClass,
    Comparison.isExtensive_modifier_iff, Comparison.IsStrict]

end Classes

section Modals

variable {W : Type*} (R : W → Prop) (count : W → ℕ) (m : ℕ)

/-- Under a modal the bare numeral keeps its two-sided content in each accessible
world ((33a), (34a)). -/
theorem narrow_scope_two_sided (Q : NP W) :
    LowScope (MaxIn {m}) Q (Iic ∘ count) ↔ Q fun w ↦ count w = m :=
  lowScope_maxIn

private theorem isGLB_iff_isLeast {s : Set ℕ} : IsGLB s m ↔ IsLeast s m :=
  ⟨fun h ↦ h.isLeast <| by_contra fun hm ↦ absurd
      (h.2 (show m + 1 ∈ lowerBounds s from
        fun x hx ↦ Nat.lt_of_le_of_ne (h.1 hx) fun e ↦ hm (e ▸ hx))) (by omega),
    IsLeast.isGLB⟩

/-- Over a necessity modal the bare numeral is lower-bounded (33b), `m` being the least count the
modal requires. -/
theorem necessity_wide_iff :
    HighScope (MaxIn {m}) (every R) (Iic ∘ count) ↔ IsLeast (count '' {w | R w}) m :=
  highScope_maxIn_singleton_every.trans (isGLB_iff_isLeast m)

/-- Over a possibility modal the bare numeral is upper-bounded (34b), `m` being the greatest count
the modal allows. -/
theorem possibility_wide_iff :
    HighScope (MaxIn {m}) (GQ.some R) (Iic ∘ count) ↔ IsGreatest (count '' {w | R w}) m :=
  highScope_maxIn_singleton_some

end Modals

/-! ### Ignorance implicatures (Section 4.1) -/

/-- The alternatives of a numeral form (46) are the five forms of the same numeral, one for each
comparison, as sets of counts. -/
def alternatives (m : ℕ) : Set (Set ℕ) := Set.range fun c : Comparison ↦ c.interval m

private theorem interval_subset_iff (c c' : Comparison) {m : ℕ} (hm : 0 < m) :
    c.interval m ⊆ c'.interval m ↔
      (c.Rel 0 m → c'.Rel 0 m) ∧ (c.Rel m m → c'.Rel m m) ∧
        (c.Rel (m + 1) m → c'.Rel (m + 1) m) := by
  simp only [Set.subset_def, Comparison.mem_interval]
  refine ⟨fun h ↦ ⟨h 0, h m, h (m + 1)⟩, fun ⟨h0, hm', h1⟩ x hx ↦ ?_⟩
  cases c <;> cases c' <;>
    simp only [Comparison.Rel, imp_iff_not_or, not_true_eq_false, false_or] at h0 hm' h1 hx ⊢ <;>
    omega

theorem interval_ssubset_iff {m : ℕ} (hm : 0 < m) (c c' : Comparison) :
    c.interval m ⊂ c'.interval m ↔
      (c, c') ∈ [(Comparison.eq, Comparison.ge), (.eq, .le), (.gt, .ge), (.lt, .le)] := by
  rw [Set.ssubset_def, interval_subset_iff c c' hm, interval_subset_iff c' c hm]
  cases c <;> cases c' <;> simp [Comparison.Rel, imp_iff_not_or] <;> omega

/-- (47a): asserting *at least m* commits the speaker to not knowing that exactly `m` and not
knowing that more than `m`. -/
theorem commitment_ge {m : ℕ} (hm : 0 < m) :
    commitment (Comparison.ge.interval m) (alternatives m) = Iic (Comparison.ge.interval m) ∩
      (Iic (Comparison.eq.interval m))ᶜ ∩ (Iic (Comparison.gt.interval m))ᶜ := by
  ext s
  simp only [mem_commitment, alternatives, forall_mem_range, interval_ssubset_iff hm,
    mem_inter_iff, mem_compl_iff, mem_Iic]
  refine ⟨fun ⟨h, h'⟩ ↦ ⟨⟨h, h' .eq (by simp)⟩, h' .gt (by simp)⟩,
    fun ⟨⟨h, he⟩, hg⟩ ↦ ⟨h, fun c hc ↦ ?_⟩⟩
  cases c <;> simp at hc <;> assumption

/-- (47b): asserting *at most m* commits the speaker to not knowing that exactly `m` and not
knowing that fewer than `m`. -/
theorem commitment_le {m : ℕ} (hm : 0 < m) :
    commitment (Comparison.le.interval m) (alternatives m) = Iic (Comparison.le.interval m) ∩
      (Iic (Comparison.eq.interval m))ᶜ ∩ (Iic (Comparison.lt.interval m))ᶜ := by
  ext s
  simp only [mem_commitment, alternatives, forall_mem_range, interval_ssubset_iff hm,
    mem_inter_iff, mem_compl_iff, mem_Iic]
  refine ⟨fun ⟨h, h'⟩ ↦ ⟨⟨h, h' .eq (by simp)⟩, h' .lt (by simp)⟩,
    fun ⟨⟨h, he⟩, hl⟩ ↦ ⟨h, fun c hc ↦ ?_⟩⟩
  cases c <;> simp at hc <;> assumption

/-- No alternative entails the bare numeral or a Class A form, so asserting one commits the
speaker to no ignorance. -/
theorem commitment_eq_Iic {m : ℕ} (hm : 0 < m) {c : Comparison} (hc : c = .eq ∨ c.IsStrict) :
    commitment (c.interval m) (alternatives m) = Iic (c.interval m) := by
  ext s
  simp only [mem_commitment, alternatives, forall_mem_range, interval_ssubset_iff hm, mem_Iic,
    and_iff_left_iff_imp]
  intro _ c'
  cases c <;> cases c' <;> simp_all [Comparison.IsStrict]

/-- (44) strengthens no form of a numeral: the bare and Class A forms have no stronger
alternative, and either primary implicature of a Class B form strengthened contradicts the
assertion together with the other. -/
theorem not_isSecondaryImplicature {m : ℕ} (hm : 0 < m) (c : Comparison) (ψ : Set ℕ) :
    ¬ IsSecondaryImplicature (c.interval m) (alternatives m) ψ := by
  rw [isSecondaryImplicature_iff]
  rintro ⟨⟨c', rfl⟩, hψ, h⟩
  have block : ∀ c₁ : Comparison, (c₁, c) ∈
      [(Comparison.eq, Comparison.ge), (.eq, .le), (.gt, .ge), (.lt, .le)] →
      c.interval m \ c'.interval m ⊆ c₁.interval m → False := fun c₁ h₁ ↦
    h _ ⟨c₁, rfl⟩ ((interval_ssubset_iff hm _ _).2 h₁)
  have key := (interval_ssubset_iff hm c' c).1 hψ
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at key
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact block .gt (by simp) fun n ⟨h1, h2⟩ ↦ by simp at h1 h2 ⊢; omega
  · exact block .lt (by simp) fun n ⟨h1, h2⟩ ↦ by simp at h1 h2 ⊢; omega
  · exact block .eq (by simp) fun n ⟨h1, h2⟩ ↦ by simp at h1 h2 ⊢; omega
  · exact block .eq (by simp) fun n ⟨h1, h2⟩ ↦ by simp at h1 h2 ⊢; omega

end Kennedy2015
