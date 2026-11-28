module

public import Linglib.Morphology.Exponence.SpanRule

/-!
# Lexical entries over a containment hierarchy

A `SupersetRule` is a nanosyntax lexical entry over an `n`-grade containment hierarchy, storing
an initial span. By the Superset Principle it spells out every grade its span contains, and
spellout (`SupersetRule.spellout`) selects the matching entry storing the least structure.
Over an antihomophonous lexicon it realizes contiguous patterns. Spellout gaps propagate upward,
where the gaps of Elsewhere insertion propagate downward.

## References

* [bubnov-2026]
* [caha-2009]
* [dekier-2021]
* [starke-2009]
-/

@[expose] public section

namespace Morphology

variable {n : ℕ} {F : Type*}

/-- A nanosyntax lexical entry over an `n`-grade containment hierarchy stores the constituent
`[0, spans]`, with no contextual condition, in the pointer-free idealization of [caha-2009]. -/
structure SupersetRule (n : ℕ) (F : Type*) where
  /-- The exponent the entry spells out. -/
  exponent : F
  /-- The upper end of the stored constituent `[0, spans]`. -/
  spans : Fin n
  deriving DecidableEq, Repr

/-- An entry spells out every grade its stored constituent contains, the Superset Principle
([starke-2009]). -/
instance : ExponenceRule (SupersetRule n F) (Fin n) F :=
  ⟨SupersetRule.exponent, fun e g ↦ g ≤ e.spans⟩

instance : DecidableRel (Applies : SupersetRule n F → Fin n → Prop) :=
  fun e g ↦ inferInstanceAs (Decidable (g ≤ e.spans))

namespace SupersetRule

variable {e e' : SupersetRule n F} {g g' : Fin n} {φ : F}

@[simp] theorem applies_iff : Applies e g ↔ g ≤ e.spans := Iff.rfl

@[simp] theorem exponent_eq : ExponenceRule.exponent e = e.exponent := rfl

/-- An entry is more specific than another iff it stores the smaller constituent, the nanosyntax
principle Minimize Junk. -/
theorem applySet_subset_iff : applySet e ⊆ applySet e' ↔ e.spans ≤ e'.spans := Set.Iic_subset_Iic

theorem applySet_ssubset_iff : applySet e ⊂ applySet e' ↔ e.spans < e'.spans := Set.Iic_ssubset_Iic

/-! ### Superset spellout -/

/-- Superset spellout realizes at each grade the exponent of the matching entry storing the least
structure, the first listed on ties, and `none` where no entry matches. -/
abbrev spellout (v : RuleSet (SupersetRule n F)) : Paradigm n (Option F) :=
  v.realize fun e : SupersetRule n F ↦ OrderDual.toDual e.spans

variable {v : RuleSet (SupersetRule n F)}

/-- Spellout gaps propagate upward, since an entry matching a higher grade matches the lower one
too, [dekier-2021]'s paradigm-gap monotonicity for indefinites. -/
theorem spellout_eq_none_of_le (h : spellout v g = none) (hg : g ≤ g') : spellout v g' = none :=
  Option.map_eq_none_iff.mpr <| RuleSet.selectBy_eq_none_of_applies
    (fun _ _ hs ↦ le_trans hg hs) (Option.map_eq_none_iff.mp h)

theorem spellout_eq_of_le_spans (h : v.selectBy (fun e ↦ OrderDual.toDual e.spans) g = some e)
    (hg : g ≤ g') (he : g' ≤ e.spans) : spellout v g' = spellout v g :=
  congrArg (Option.map _) <|
    (RuleSet.selectBy_eq_some_of_applies (fun _ _ hs ↦ le_trans hg hs) h he).trans h.symm

/-- The loss of entries extends a form downward only. If an antihomophonous lexicon spells out a
form at a grade and, after losing entries, still spells it out at a higher grade, it spelled it
out there before ([bubnov-2026]). -/
theorem spellout_eq_some_of_filter_of_le (hv : v.Antihomophonous) {p : SupersetRule n F → Bool}
    (h : spellout v g = some φ) (h' : spellout (v.filter p) g' = some φ) (hg : g ≤ g') :
    spellout v g' = some φ := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨e', he', hφ⟩ := Option.map_eq_some_iff.mp h'
  obtain rfl := hv (List.mem_filter.mp (RuleSet.selectBy_mem he')).1 (RuleSet.selectBy_mem he) hφ
  rw [spellout_eq_of_le_spans he hg (RuleSet.selectBy_applies he'), h]

/-- Superset spellout over an antihomophonous lexicon is contiguous ([caha-2009]). -/
theorem isContiguous_spellout (hv : v.Antihomophonous) : IsContiguous (spellout v) :=
  RuleSet.isContiguous_realize_of_antitone hv fun _ _ _ _ hg hs ↦ le_trans hg hs

end SupersetRule

end Morphology
