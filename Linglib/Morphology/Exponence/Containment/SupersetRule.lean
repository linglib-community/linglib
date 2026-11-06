module

public import Linglib.Morphology.Exponence.Containment.SpanRule

/-!
# Lexical entries over a containment hierarchy

A `SupersetRule` is a nanosyntax lexical entry over an `n`-grade containment hierarchy, storing
an initial span. By the Superset Principle it spells out every grade its span contains, and
spellout (`SupersetRule.spellout`) selects the matching entry storing the least structure.
Elsewhere insertion is spellout [over the reversed hierarchy](##SpanRule.realize_eq_spellout_rev),
so the two engines generate
[the same fully realized patterns](##SupersetRule.generable_iff_spanRule_generable), the
contiguous ones. On partial patterns they part: spellout gaps propagate upward, Elsewhere gaps
downward.

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

theorem spellout_realizes (h : spellout v g = some φ) : v.Realizes applySet g φ :=
  RuleSet.realize_realizes (f := fun e : SupersetRule n F ↦ OrderDual.toDual e.spans)
    (fun _ _ _ _ h ↦ OrderDual.toDual_lt_toDual.2 (applySet_ssubset_iff.1 h)) h

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

/-! ### Duality -/

/-- A rule of exponence as the lexical entry that matches the reversed grades it applies at. -/
def SpanRule.toSupersetRule (it : SpanRule n F) : SupersetRule n F :=
  ⟨it.exponent, it.threshold.rev⟩

/-- Elsewhere insertion is Superset spellout over the reversed hierarchy: a rule applying from
its threshold up is an entry storing up to the reversed threshold, and the greatest threshold is
the least stored span. -/
theorem SpanRule.realize_eq_spellout_rev (v : RuleSet (SpanRule n F)) (g : Fin n) :
    SpanRule.realize v g = SupersetRule.spellout (v.map SpanRule.toSupersetRule) g.rev := by
  unfold SpanRule.realize SupersetRule.spellout RuleSet.realize
  rw [RuleSet.selectBy_map (c := g) (c' := g.rev) (f := SpanRule.threshold)
    (f' := fun e : SupersetRule n F ↦ OrderDual.toDual e.spans) (fun _ _ ↦ Fin.rev_le_rev)
    fun _ _ _ _ ↦ OrderDual.toDual_le_toDual.trans Fin.rev_le_rev, Option.map_map]
  rfl

namespace SupersetRule

/-- A pattern is **generable** when some antihomophonous lexicon spells it out in full. -/
def Generable (p : Paradigm n F) : Prop :=
  ∃ v : RuleSet (SupersetRule n F), v.Antihomophonous ∧ ∀ g, spellout v g = some (p g)

/-- A fully realized pattern arises from Superset spellout over an antihomophonous lexicon iff it
is contiguous, [caha-2009]'s Universal Contiguity sharpened to exact generative capacity. -/
theorem isContiguous_iff_generable (p : Paradigm n F) : IsContiguous p ↔ Generable p := by
  refine ⟨fun hp ↦ ?_, fun ⟨_, hv, hreal⟩ ↦ (isContiguous_comp_iff (Option.some_injective F)).1 <|
    (funext hreal : _ = some ∘ p) ▸ isContiguous_spellout hv⟩
  obtain ⟨v, -, hv, hreal⟩ :=
    (SpanRule.isContiguous_iff_generable _).1 (hp.comp_antitone Fin.rev_anti)
  refine ⟨v.map SpanRule.toSupersetRule, hv.map fun _ ↦ rfl, fun g ↦ ?_⟩
  rw [← Fin.rev_rev g, ← SpanRule.realize_eq_spellout_rev, hreal, Function.comp_apply]

instance [DecidableEq F] : DecidablePred (Generable : Paradigm n F → Prop) :=
  fun p ↦ decidable_of_iff _ (isContiguous_iff_generable p)

/-- Superset spellout and Elsewhere insertion from terminal rule sets generate the same fully
realized patterns, the contiguous ones. -/
theorem generable_iff_spanRule_generable (p : Paradigm n F) :
    Generable p ↔ SpanRule.Generable p :=
  (isContiguous_iff_generable p).symm.trans (SpanRule.isContiguous_iff_generable p)

end SupersetRule

end Morphology
