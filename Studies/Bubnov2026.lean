module

public import Linglib.Morphology.Nanosyntax.Lexicalization
public import Studies.DeganoAloni2025
public import Studies.Dekier2021
public import Studies.Haspelmath1997

/-!
# Bubnov (2026): Not all coexpressions are syncretisms: Limiting Nanosyntax

Indefinite pronouns coexpress the specific known, specific unknown and non-specific functions in
the patterns AAA, ABB, AAB and ABC and never in the pattern ABA. Dekier derives the gap from a
containment hierarchy whose most complex layer is the specific known one. Bubnov objects that a
hierarchy whose higher layers had exponents of their own would show morphological containment,
one marker built on another, which no indefinite paradigm does, and argues that the semantic
account of Degano and Aloni explains the gap better. There a form carries one restriction on
the variation and constancy of the indefinite's value and is used wherever the restriction is
met, so coexpression is underspecification rather than syncretism, the unattested pattern is the
type whose two restrictions exclude each other and can only be disjoined, and the complex type
is the specific unknown one, which no single restriction states.

The accounts come apart on diachrony. Semantically a change weakens a restriction, and every
attested change does. On a hierarchy the change the theory is known to allow is the loss of a
lexical entry, after which a surviving entry also spells out layers the lost one took from it,
all of them below the layers it had. A specific unknown form has become epistemic by gaining the
non-specific function and a non-specific form has become epistemic by gaining the specific
unknown one, so entry loss derives at most one of the two changes, whichever way the hierarchy
is ordered.

## Main results

* `containment_of_two_exponents`, `no_containment_of_bottom_entries`: a layer with an exponent
  of its own is a suffix on the form below it, and Dekier's lexicons have no such layer.
* `ordConnected_coverage`: a hierarchy ordered either way along the map gives each form an
  interval of the uses, so it excludes ABA as the semantic account does.
* `no_hierarchy_derives_both_changes`, `entry_loss_is_weakening`: on no hierarchy does entry
  loss derive both attested changes to the epistemic type, and what it derives is a semantic
  weakening.
* `specificUnknown_not_atomic`: no single restriction states the specific unknown type.
* `coexpression_is_underspecification`: each form of the four coexpression patterns is a single
  type.

## TODO

The paper calls the change from a specific to an unmarked form attested in one sentence of its
comparison and unattested in the next, in the discussion of entry loss and in a footnote on the
reversed hierarchy. It is taken as unattested here.

## References

* [bubnov-2026]
* [dekier-2021]
* [degano-aloni-2025]
* [haspelmath-1997]
* [aloni-port-2015]
-/

@[expose] public section

namespace Bubnov2026

open DeganoAloni2025 Dekier2021 Indefinite Team Morphology.Containment Morphology.Exponence
open Morphology.Nanosyntax
open Haspelmath1997 hiding russian

/-! ### Morphological containment -/

/-- A structure of two layers that is not spelled out by one exponent is spelled out by the
exponent of its lower layer and a suffix. Were a higher layer of the hierarchy to have an
exponent of its own, the marker of one function would thus be built on the marker of another,
the containment no indefinite paradigm shows. -/
theorem containment_of_two_exponents {F : Type*} [DecidableEq F]
    (L : RuleSet (LexicalEntry (Option F) String)) (f₁ f₂ : F) {x : String} {r : List String}
    (h₁ : exponents L [f₁] = some [x]) (h₂ : exponents L [f₁, f₂] = some r) (hr : r.length ≠ 1) :
    ∃ y, r = [x, y] := by
  rw [exponents_singleton] at h₁
  rw [exponents_pair] at h₂
  rcases h : treeSpellout L (.leaf (some f₁)) with - | x' <;> rw [h] at h₁ h₂
  · simp at h₁
  · obtain rfl : x' = x := by simpa using h₁
    rcases hw : treeSpellout L (merge f₂ (.leaf (some f₁))) with - | y
    · rcases hs : treeSpellout L (.leaf (some f₂)) with - | z
      · simp [hw, hs] at h₂
      · rcases ha : treeSpellout L (adjoin (.leaf (some f₁)) (.leaf (some f₂))) with - | w <;>
          simp [hw, hs, ha] at h₂
        · exact ⟨z, h₂.symm⟩
        · exact absurd (by simp [← h₂]) hr
    · simp [hw] at h₂
      exact absurd (by simp [← h₂]) hr

/-- A lexicon like Dekier's, every entry of which stores the lowest layer, gives each layer a
single exponent under the lexicalization algorithm, the one its spellout has there, so no
marker is built on another. -/
theorem no_containment_of_bottom_entries {n : ℕ} (L : RuleSet (SupersetRule n String))
    (g : Fin n) :
    exponents (L.map (LexicalEntry.ofSupersetRule some)) (List.range ((g : ℕ) + 1)) =
      (spellout L g).map fun x ↦ [x] := by
  simpa using exponents_ofSupersetRule (feat := id) Function.injective_id L g

/-! ### Complexity -/

/-- No single atom states the specific unknown requirement, whatever its variables, since a
constancy atom is closed under subteams, a variation atom under superteams, and the requirement
under neither. On the semantic account the specific unknown type is thus the complex one, the
specific known and the non-specific type each being a single atom, where the hierarchy makes
the specific known layer the most complex. -/
theorem specificUnknown_not_atomic {V E : Type*} [Nontrivial E] {v x : V} (hvx : v ≠ x)
    (Z : Finset V) (u : V) :
    (¬ ∀ T : Finset (V → E), IndefiniteType.specificUnknown.Requires T v x ↔ Dep T Z u) ∧
      ¬ ∀ T : Finset (V → E), IndefiniteType.specificUnknown.Requires T v x ↔ Var T Z u :=
  ⟨fun h ↦ IndefiniteType.not_isLowerSet_specificUnknown (E := E) hvx
      fun _ _ hT ht ↦ (h _).2 (((h _).1 ht).subset hT),
    fun h ↦ IndefiniteType.not_isUpperSet_specificUnknown (E := E) hvx
      fun _ _ hT ht ↦ (h _).2 (((h _).1 ht).superset hT)⟩

/-! ### Diachrony as weakening -/

theorem attested_changes_are_weakenings {V E : Type*} (T : Finset (V → E)) (v x : V) :
    (IndefiniteType.specificUnknown.Requires T v x → IndefiniteType.epistemic.Requires T v x) ∧
      (IndefiniteType.nonSpecific.Requires T v x → IndefiniteType.epistemic.Requires T v x) ∧
      (IndefiniteType.epistemic.Requires T v x → IndefiniteType.unmarked.Requires T v x) :=
  ⟨And.right, Team.Var.anti (Finset.empty_subset _), fun _ ↦ trivial⟩

/-! ### Diachrony as the loss of an entry

A hierarchy assigns each function a layer, and a lexicon then gives a form the functions at
whose layers it spells the form out. -/

section EntryLoss

variable {n : ℕ} {ℓ : SpecificityFunction → Fin n} {L : RuleSet (SupersetRule n String)}
  {φ : String} {t t' : IndefiniteType} {u u' : SpecificityFunction}

/-- The functions at which a lexicon spells out a form. -/
def coverage (ℓ : SpecificityFunction → Fin n) (L : RuleSet (SupersetRule n String))
    (φ : String) : Finset SpecificityFunction :=
  Finset.univ.filter fun u ↦ spellout L (ℓ u) = some φ

@[simp]
theorem mem_coverage : u ∈ coverage ℓ L φ ↔ spellout L (ℓ u) = some φ := by simp [coverage]

/-- A hierarchy ordering its layers as the map orders the uses, Dekier's or its reverse, complies
with the ban on ABA, since it gives each form an interval of the uses and so only a type whose
requirement is convex (`IndefiniteType.ordConnected_requires`). -/
theorem ordConnected_coverage (hℓ : Monotone ℓ ∨ Antitone ℓ) (hL : L.Antihomophonous) :
    (coverage ℓ L φ : Set SpecificityFunction).OrdConnected := by
  have h :=
    (isContiguous_iff_ordConnected_preimage _).1 (isContiguous_spellout hL) (some φ)
  have he : (coverage ℓ L φ : Set SpecificityFunction) = ℓ ⁻¹' (spellout L ⁻¹' {some φ}) := by
    ext; simp
  exact he ▸ hℓ.elim h.preimage_mono h.preimage_anti

/-- Entry loss derives the change from one type to another on a hierarchy when some lexicon
gives a form the first type and, with some of its entries lost, the second. -/
def LossDerives (ℓ : SpecificityFunction → Fin n) (t t' : IndefiniteType) : Prop :=
  ∃ (L : RuleSet (SupersetRule n String)) (lost : Finset (SupersetRule n String)) (φ : String),
    L.Antihomophonous ∧ coverage ℓ L φ = t.profile ∧
      coverage ℓ (L.filter (· ∉ lost)) φ = t'.profile

namespace LossDerives

theorem profile_subset (h : LossDerives ℓ t t') : t.profile ⊆ t'.profile := by
  obtain ⟨L, lost, φ, hL, ht, ht'⟩ := h
  obtain ⟨u', hu'⟩ := t'.profile_nonempty
  intro u hu
  rw [← ht'] at hu' ⊢
  rw [← ht] at hu
  exact mem_coverage.2 (RuleSet.realize_filter_eq_some hL (mem_coverage.1 hu) (mem_coverage.1 hu'))

theorem lt_of_mem_sdiff (h : LossDerives ℓ t t') (hu' : u' ∈ t'.profile \ t.profile)
    (hu : u ∈ t.profile) : ℓ u' < ℓ u := by
  obtain ⟨L, lost, φ, hL, ht, ht'⟩ := h
  rw [← ht, ← ht', Finset.mem_sdiff] at hu'
  rw [← ht] at hu
  exact lt_of_not_ge fun hle ↦ hu'.2 <| mem_coverage.2 <|
    spellout_eq_some_of_filter_of_le hL (mem_coverage.1 hu) (mem_coverage.1 hu'.1) hle

end LossDerives

/-- A change entry loss derives is a semantic weakening, so the hierarchy predicts a part of
what the semantic account predicts. -/
theorem entry_loss_is_weakening (h : LossDerives ℓ t t') {V E : Type*} (T : Finset (V → E))
    (v x : V) : t.Requires T v x → t'.Requires T v x := by
  simp only [IndefiniteType.requires_iff]
  exact fun ⟨u, hu, hT⟩ ↦ ⟨u, h.profile_subset hu, hT⟩

/-- On no hierarchy does entry loss derive both attested changes to the epistemic type. A
specific unknown form gains the non-specific function and a non-specific form the specific
unknown one, and each gain would put the gained function's layer below the other's. This holds
of Dekier's hierarchy and of its reverse alike. -/
theorem no_hierarchy_derives_both_changes (ℓ : SpecificityFunction → Fin n) :
    ¬ (LossDerives ℓ .specificUnknown .epistemic ∧ LossDerives ℓ .nonSpecific .epistemic) :=
  fun ⟨h, h'⟩ ↦ lt_asymm
    (h.lt_of_mem_sdiff (u' := .nonSpecific) (u := .specificUnknown) (by decide) (by decide))
    (h'.lt_of_mem_sdiff (u' := .specificUnknown) (u := .nonSpecific) (by decide) (by decide))

end EntryLoss

/-- On Dekier's hierarchy the loss of an entry `A` storing the non-specific layer makes the
specific unknown form `B` epistemic, (3) and (4). Entry loss also derives two unattested
changes there, a specific known form becoming specific and a specific form unmarked. -/
theorem entry_loss_derives_downward_changes :
    LossDerives layer .specificUnknown .epistemic ∧ LossDerives layer .specificKnown .specific ∧
      LossDerives layer .specific .unmarked :=
  ⟨⟨[⟨"A", 0⟩, ⟨"B", 1⟩], {⟨"A", 0⟩}, "B", by decide, by decide, by decide⟩,
    ⟨[⟨"A", 0⟩, ⟨"B", 1⟩, ⟨"C", 2⟩], {⟨"B", 1⟩}, "C", by decide, by decide, by decide⟩,
    ⟨[⟨"A", 0⟩, ⟨"C", 2⟩], {⟨"A", 0⟩}, "C", by decide, by decide, by decide⟩⟩

theorem entry_loss_misses_upward_changes :
    ¬ LossDerives layer .nonSpecific .epistemic ∧ ¬ LossDerives layer .epistemic .unmarked :=
  ⟨fun h ↦ no_hierarchy_derives_both_changes _ ⟨entry_loss_derives_downward_changes.1, h⟩,
    fun h ↦ absurd (h.lt_of_mem_sdiff (u' := .specificKnown) (u := .nonSpecific)
      (by decide) (by decide)) (by decide)⟩

theorem entry_loss_on_reversed_hierarchy :
    LossDerives (Fin.rev ∘ layer) .nonSpecific .epistemic ∧
      LossDerives (Fin.rev ∘ layer) .epistemic .unmarked ∧
      ¬ LossDerives (Fin.rev ∘ layer) .specificUnknown .epistemic :=
  have h : LossDerives (Fin.rev ∘ layer) .nonSpecific .epistemic :=
    ⟨[⟨"A", 0⟩, ⟨"B", 1⟩, ⟨"C", 2⟩], {⟨"B", 1⟩}, "C", by decide, by decide, by decide⟩
  ⟨h, ⟨[⟨"A", 0⟩, ⟨"C", 2⟩], {⟨"A", 0⟩}, "C", by decide, by decide, by decide⟩,
    fun h' ↦ no_hierarchy_derives_both_changes _ ⟨h', h⟩⟩

/-! ### Coexpression as underspecification -/

/-- Each form of the four coexpression patterns is a single type. English *some-* imposes no
restriction (AAA), Yakut *-eme* requires variation within an epistemic alternative and *-ere*
constancy within one (ABB), Latin *ali-* requires variation across the alternatives and *-dam*
constancy across them (AAB), and Russian *-nibud'*, *-to* and *koe-* require variation within an
alternative, variation across them and constancy across them, the entries (6) and (7). -/
theorem coexpression_is_underspecification :
    (∃ s ∈ english, s.toSeries = English.Indefinites.someSeries ∧ Instantiates s .unmarked) ∧
      (∃ s ∈ yakut, s.toSeries = Yakut.Indefinites.emeSeries ∧ Instantiates s .nonSpecific) ∧
      (∃ s ∈ yakut, s.toSeries = Yakut.Indefinites.ereSeries ∧ Instantiates s .specific) ∧
      (∃ s ∈ latin, s.toSeries = Latin.Indefinites.aliSeries ∧ Instantiates s .epistemic) ∧
      (∃ s ∈ latin, s.toSeries = Latin.Indefinites.damSeries ∧ Instantiates s .specificKnown) ∧
      (∃ s ∈ russian,
        s.toSeries = Russian.Indefinites.nibudSeries ∧ Instantiates s .nonSpecific) ∧
      (∃ s ∈ russian, s.toSeries = Russian.Indefinites.toSeries ∧ Instantiates s .epistemic) ∧
      ∃ s ∈ russian,
        s.toSeries = Russian.Indefinites.koeSeries ∧ Instantiates s .specificKnown := by
  decide

theorem to_is_specificUnknown_under_spellout :
    coverage layer (lexicon russian) Russian.Indefinites.toSeries.name =
      IndefiniteType.specificUnknown.profile := by
  decide

end Bubnov2026
