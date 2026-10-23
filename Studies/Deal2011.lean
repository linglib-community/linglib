module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Polarity.Basic
public import Linglib.Fragments.NezPerce.Modals
public import Linglib.Data.Examples.Deal2011

/-!
# Deal (2011): Modals without scales

This file formalizes [deal-2011]'s account of the Nez Perce modal *o'qa*, used where English
uses a possibility modal and where it uses a necessity modal in upward-entailing contexts, but
only where it uses a possibility modal elsewhere. *O'qa* is a possibility modal without a Horn
scale: two modals form a scale only when they quantify over the same domain, sharing a type of
modality, and no stronger Nez Perce modal shares *o'qa*'s (§2). A possibility claim without a
scalar implicature holds whenever there are accessible worlds of the prejacent, even when all
accessible worlds are, so in an upward-entailing context *o'qa* serves for both forces (§1).
Under negation the necessity claim is the weaker one, and *o'qa* serves only where a possibility
modal of English does (§3).

The claims are [kratzer-1981]'s simple possibility and necessity, and negation acts on them by
complement, the negative `Polarity`. A modal is appropriate where its claim holds and, if it has
a scalemate, the scalemate's claim fails when it is the stronger one there (`Appropriate`). The
contexts a modal serves for are then fixed by whether it has a scalemate and which claim is
stronger (`servesFor_iff`), and Table 1 follows (`flexible_iff`): a modal with a scale is
inflexible, a scale-free possibility modal is flexible only in upward-entailing contexts, and a
scale-free necessity modal only in downward-entailing ones.

## Implementation notes

* Forces are compared on the classical scale, weak necessity counting as necessity; the claims
  are simple possibility and necessity over a consistent modal base, with no ordering source.
* Negation stands in for the downward-entailing contexts of §3, the restrictions of universals
  and conditional antecedents, whose rows the `environment` feature marks; the paper treats
  conditional antecedents as not upward-entailing, leaving their monotonicity open (fn. 12).
* The rows are *o'qa*'s judgments by the force of the English modal of the context or
  translation. (11) and (12), where speakers find *o'qa* too weak a translation of a necessity
  claim, bear on the preference for possibility translations, which the paper attributes to
  *o'qa*'s being a possibility modal; they are not rows.

## References

* [deal-2011]
* [kratzer-1981]
-/

@[expose] public section

namespace Deal2011

open Modality

/-! ### Claims -/

section Claims

variable {W : Type*} (f : Background W) (p : W → Prop)

/-- The claim a modal of force `fo` makes about `p` over the base `f`: simple possibility, or
simple necessity for the universal forces. -/
def claim : ModalForce → Set W
  | .possibility => {w | simplePossibility f p w}
  | .weakNecessity | .necessity => {w | simpleNecessity f p w}

/-- In a context of polarity `π`, the claim of force `g` is stronger than that of `fo`:
necessity is the stronger claim in an upward-entailing context, possibility under negation. -/
def StrongerIn : Polarity → ModalForce → ModalForce → Prop
  | .positive, g, fo => fo.classical < g.classical
  | .negative, g, fo => g.classical < fo.classical

instance : ∀ π g fo, Decidable (StrongerIn π g fo)
  | .positive, _, _ => inferInstanceAs (Decidable (_ < _))
  | .negative, _, _ => inferInstanceAs (Decidable (_ < _))

variable {f p}

/-- Over a consistent base, a stronger claim entails a weaker one. -/
theorem smul_claim_subset (hf : ModalLogic.IsSerial f.accessible) {π : Polarity} {g fo : ModalForce}
    (h : StrongerIn π g fo) : π • claim f p g ⊆ π • claim f p fo := by
  have hnec : claim f p .necessity ⊆ claim f p .possibility := fun w hw ↦
    let ⟨v, hv⟩ := hf.serial w
    ⟨v, hv, hw v hv⟩
  cases π <;> cases g <;> cases fo <;>
    first
    | exact absurd h (by decide)
    | exact hnec
    | exact Set.compl_subset_compl.2 hnec

variable (f p)

/-- A modal of force `fo`, with a scalemate when `s`, is appropriate in a context of polarity
`π` where its claim holds and, if it has a scalemate whose claim is the stronger there, that
claim fails: the scalar implicature. -/
def Appropriate (π : Polarity) (fo : ModalForce) (s : Prop) : Set W :=
  π • claim f p fo ∩ {w | s → StrongerIn π fo.dual fo → w ∉ π • claim f p fo.dual}

end Claims

/-! ### Flexibility (§1, §3, Table 1) -/

/-- A modal of force `fo`, with a scalemate when `s`, serves in a context of polarity `π` for
the force `g` when, in every consistent model, it is appropriate wherever a modal of force `g`
with a scale, as in English, is. -/
def ServesFor (π : Polarity) (fo : ModalForce) (s : Prop) (g : ModalForce) : Prop :=
  ∀ (W : Type) (f : Background W), ModalLogic.IsSerial f.accessible → ∀ p : W → Prop,
    Appropriate f p π g True ⊆ Appropriate f p π fo s

/-- A modal serves for its own force, and without a scalemate for any force whose claim is
stronger than its own. -/
def Usable (π : Polarity) (fo : ModalForce) (s : Prop) (g : ModalForce) : Prop :=
  fo.classical = g.classical ∨ (¬ s ∧ StrongerIn π g fo)

instance (π : Polarity) (fo : ModalForce) (s : Prop) [Decidable s] (g : ModalForce) :
    Decidable (Usable π fo s g) :=
  inferInstanceAs (Decidable (_ ∨ _))

variable {W : Type*} {f : Background W} {p : W → Prop}

theorem appropriate_classical (π : Polarity) (fo : ModalForce) (s : Prop) :
    Appropriate f p π fo.classical s = Appropriate f p π fo s := by
  cases fo <;> cases π <;> rfl

/-- The two-world model in which both worlds are accessible from each. -/
private def bothAccessible : Background Bool := ⊥

private theorem isSerial_bothAccessible : ModalLogic.IsSerial bothAccessible.accessible :=
  ⟨fun _ ↦ ⟨true, by simp [bothAccessible]⟩⟩

variable {π : Polarity} {fo g : ModalForce} {s : Prop}

/-- Decides membership in the two-world model. -/
local macro "twoWorlds" : tactic =>
  `(tactic| (simp_all [Appropriate, claim, StrongerIn, bothAccessible,
    ModalForce.classical, ModalForce.dual, ModalForce.rank]; done))

private theorem not_servesFor_of (p : Bool → Prop)
    (hin : true ∈ Appropriate bothAccessible p π g True)
    (hout : true ∉ Appropriate bothAccessible p π fo s) : ¬ ServesFor π fo s g :=
  fun h ↦ hout (h Bool bothAccessible isSerial_bothAccessible p hin)

/-- The forces a modal serves for are its own and, if it has no scalemate, those whose claim is
stronger than its own. -/
theorem servesFor_iff : ServesFor π fo s g ↔ Usable π fo s g := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra hu
    simp only [Usable, not_or, not_and] at hu
    obtain ⟨hne, hsg⟩ := hu
    cases π <;> cases fo <;> cases g <;> try exact absurd rfl hne
    all_goals try have hs : s := by_contra fun hs ↦ hsg hs (by decide)
    all_goals first
      | refine not_servesFor_of (fun _ ↦ True) ?_ ?_ h <;> clear h <;> twoWorlds
      | refine not_servesFor_of (fun b ↦ b = true) ?_ ?_ h <;> clear h <;> twoWorlds
      | refine not_servesFor_of (fun _ ↦ False) ?_ ?_ h <;> clear h <;> twoWorlds
  · rintro (h | ⟨hs, h⟩) W f hf p w hw
    · rw [← appropriate_classical (fo := g), ← h, appropriate_classical] at hw
      exact ⟨hw.1, fun _ ↦ hw.2 trivial⟩
    · exact ⟨smul_claim_subset hf h hw.1, fun hs' ↦ absurd hs' hs⟩

/-- Table 1: a modal is flexible in a context of polarity `π`, serving for every force, exactly
when it has no scalemate and its own claim is the weaker there. A modal with a scale is never
flexible, a scale-free possibility modal is flexible in upward-entailing contexts only, and a
scale-free necessity modal in downward-entailing ones only. -/
theorem flexible_iff : (∀ g, ServesFor π fo s g) ↔ ¬ s ∧ StrongerIn π fo.dual fo := by
  simp only [servesFor_iff, Usable]
  refine ⟨fun h ↦ (h fo.dual).resolve_left (by cases fo <;> decide), fun h g ↦ ?_⟩
  cases π <;> cases fo <;> cases g <;> first | exact .inl rfl | exact .inr h

/-! ### Scales (§2) -/

/-- Two modals are scalemates, forming a Horn scale, when their lexical forces differ and they
share a flavour: only quantifiers over the same domain form a scale (§2.1). -/
def Scalemates (lex : ModalItem → ModalForce) (m m' : ModalItem) : Prop :=
  (lex m).classical ≠ (lex m').classical ∧ ∃ fl ∈ m.flavors, fl ∈ m'.flavors

/-- A modal has a scalemate in an inventory. -/
def HasScalemate (lex : ModalItem → ModalForce) (L : List ModalItem) (m : ModalItem) : Prop :=
  ∃ m' ∈ L, Scalemates lex m m'

instance (lex : ModalItem → ModalForce) (m m' : ModalItem) : Decidable (Scalemates lex m m') :=
  inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, _))

instance (lex : ModalItem → ModalForce) (L : List ModalItem) (m : ModalItem) :
    Decidable (HasScalemate lex L m) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A modal of the inventory `L` serves in a context of polarity `π` for the force `g`, given its
lexical force and whether it has a scalemate in `L`. -/
def ServesIn (lex : ModalItem → ModalForce) (L : List ModalItem) (π : Polarity) (m : ModalItem)
    (g : ModalForce) : Prop :=
  ServesFor π (lex m) (HasScalemate lex L m) g

/-- The Nez Perce modals are possibility modals (§2): *o'qa*, the participial construction,
which appears to express possibility, *'ax̂*, which speakers judge equivalent to *o'qa*, and the
epistemic particles 'maybe'. -/
def lexicalForce (_ : ModalItem) : ModalForce := .possibility

/-- *O'qa* is a quantifier without a scale (§2.6). -/
theorem oqa_scaleFree : ¬ HasScalemate lexicalForce NezPerce.modals NezPerce.oqa := by decide

theorem oqa_flexible :
    (∀ g, ServesIn lexicalForce NezPerce.modals .positive NezPerce.oqa g) ∧
      ¬ ∀ g, ServesIn lexicalForce NezPerce.modals .negative NezPerce.oqa g := by
  simp only [ServesIn, flexible_iff]
  decide

theorem oqa_forces :
    ∀ g, g.classical ∈ NezPerce.oqa.classical.forces ↔
      Usable .positive (lexicalForce NezPerce.oqa)
        (HasScalemate lexicalForce NezPerce.modals NezPerce.oqa) g := by
  decide

/-! ### Rows -/

/-- The modals the rows name, keyed by their forms. -/
def modalTable : List (String × ModalItem) := NezPerce.modals.map fun m ↦ (m.form, m)

/-- The polarity of a row's environment: negation, the restriction of a universal and a
conditional antecedent are not upward-entailing. -/
def polarityTable : List (String × Polarity) :=
  [("unembedded", .positive), ("existential restriction", .positive),
    ("conditional consequent", .positive), ("negation", .negative),
    ("universal restriction", .negative), ("conditional antecedent", .negative)]

/-- The force of the English modal of a row's context or translation. -/
def forceTable : List (String × ModalForce) :=
  [("possibility", .possibility), ("necessity", .necessity)]

theorem rows_resolve :
    ∀ e ∈ Examples.all, (e.parse? "modal" modalTable).isSome ∧
      (e.parse? "environment" polarityTable).isSome := by
  decide

/-- §1 and §3: *o'qa* is accepted in a context, or on a translation, exactly when it serves for
the force of the English modal there, both forces in upward-entailing environments and
possibility alone elsewhere. -/
theorem rows :
    ∀ e ∈ Examples.all, ∀ m ∈ e.parse? "modal" modalTable,
      ∀ π ∈ e.parse? "environment" polarityTable,
        (∀ g ∈ e.parse? "force" forceTable, (e.judgment = .acceptable ↔
          Usable π (lexicalForce m) (HasScalemate lexicalForce NezPerce.modals m) g)) ∧
        ∀ r ∈ e.readings, ∃ g ∈ forceTable.lookup r.1, (r.2 = .acceptable ↔
          Usable π (lexicalForce m) (HasScalemate lexicalForce NezPerce.modals m) g) := by
  decide

end Deal2011
