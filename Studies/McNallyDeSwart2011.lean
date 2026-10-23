module

public import Linglib.Fragments.Dutch.Adjectives
public import Linglib.Semantics.Modification.Basic

/-!
# McNally and de Swart (2011): Inflection and Derivation

This file formalizes the analysis of [mcnally-deswart-2011] of the three ways Dutch refers
to abstract objects such as colours, illustrated with *rood* 'red': the uninflected nominal
*het rood* and the derived *de roodheid* denote kinds, sets of subkinds, while the inflected
*het rode van de aardbeien* denotes a trope, the entity correlate of a relational property
instantiated in one bearer. The uninflected nominal of a root denotes the set of its subkinds,
the shades of the colour (`uninflectedNominal`); the derived nominal, the noun in *-heid* of
the root (`Dutch.Adjectives.heid`), denotes the same kind (`derivedNominal`); the inflectional
suffix is not a category-changing nominalizer but a valence-increasing operator turning the
adjective into a relation between an object and its aspect, which the determiner *het*, the
nominalization operator of [chierchia-1984] when it embeds an adjective phrase, reifies as a
trope (`inflectAdjective`, `inflectedWithHet`). The three forms differ in what the determiner
embeds and in what they denote, and the paper's distributional diagnostics follow from those
two coordinates: adjectival modification and determiners other than *het* need a noun, and
generic use needs a kind, so the inflected form alone fails all three (`Form`,
`inflected_diagnostics`, `fails_iff_inflected`). The paper's three rival analyses of the
inflected form are named for later comparison (`InflectedAnalysis`).

## Implementation notes

The roots and their forms come from the Dutch adjective fragment, and the paper's primitive
subkind relation is modelled as sharing a root; the model is extensional, so the kind denoted
by the derived nominal coincides with the uninflected one. The trope is the pair of the aspect
property and its bearer. The paper's observation that the inflected
construction is rare with concrete adjectives, and its extension to Dutch nominalized
infinitives and Spanish *lo*-nominals, are described in prose.

## References

* [L. McNally and H. de Swart, *Inflection and Derivation: How Adjectives and Nouns Refer to
  Abstract Objects* (2011)][mcnally-deswart-2011]
* [G. Chierchia, *Topics in the Syntax and Semantics of Infinitives and Gerunds*
  (1984)][chierchia-1984]
-/

@[expose] public section

namespace McNallyDeSwart2011

/-! ### Kinds: the uninflected and derived nominals -/

/-- A shade: an adjective entry of the fragment with an index, so that several shades belong
to one colour. -/
structure Shade where
  root : Dutch.Adjectives.Adjective
  idx : ℕ
  deriving DecidableEq, Repr

/-- The uninflected noun *rood* (19): the set of subkinds, the shades, of the colour. -/
def uninflectedNominal (a : Dutch.Adjectives.Adjective) : Set Shade := {s | s.root = a}

@[simp] theorem mem_uninflectedNominal {a : Dutch.Adjectives.Adjective} {s : Shade} :
    s ∈ uninflectedNominal a ↔ s.root = a :=
  Iff.rfl

/-- A prepositional modifier (20) meets the kind with the shades a contextual relation links to
the complement's entity. -/
def ppModifier {Entity : Type*} (R : Shade → Entity → Prop) (s : Entity) : Modifier (Set Shade) :=
  Modifier.intersective {x | R x s}

theorem isSubsective_ppModifier {Entity : Type*} (R : Shade → Entity → Prop) (s : Entity) :
    (ppModifier R s).IsSubsective :=
  (Modifier.intersective_isIntersective _).isSubsective

/-- The derived noun *roodheid* (24), the noun in *-heid* of the root, denotes the kind of the
root. -/
def derivedNominal (a : Dutch.Adjectives.Adjective) : Set Shade := uninflectedNominal a

/-! ### The trope: the inflected form -/

/-- The aspect relation a language pairs with each adjectival property: the relation between
a bearer and its aspect of that property. -/
def AspectOf (Entity : Type*) := (Shade → Prop) → Entity → Shade → Prop

/-- The inflectional suffix (25): a valence-increasing operator taking the adjective's property
to the aspect relation. -/
def inflectAdjective {Entity : Type*} (asp : AspectOf Entity) (P : Shade → Prop) :
    Entity → Shade → Prop :=
  asp P

/-- The trope *het rode van de aardbeien* (26): the aspect property saturated by the bearer,
reified by *het* together with its bearer. -/
def inflectedWithHet {Entity : Type*} (asp : AspectOf Entity) (P : Shade → Prop) (s : Entity) :
    (Shade → Prop) × Entity :=
  (inflectAdjective asp P s, s)

/-! ### The three forms and the diagnostics -/

/-- What the determiner embeds. -/
inductive Embedded where
  | noun
  | adjectivePhrase
  deriving DecidableEq, Repr

/-- The kind of abstract object a form denotes. -/
inductive AbstractObject where
  | kind
  | trope
  deriving DecidableEq, Repr

/-- A form of abstract reference: what the determiner embeds and what the whole denotes. -/
structure Form where
  embedded : Embedded
  denotation : AbstractObject
  deriving DecidableEq, Repr

/-- *het rood*: a neuter mass noun denoting a kind. -/
def uninflected : Form := ⟨.noun, .kind⟩

/-- *de roodheid*: a derived noun denoting a kind. -/
def derived : Form := ⟨.noun, .kind⟩

/-- *het rode van X*: an adjective phrase under *het*, denoting a trope. -/
def inflected : Form := ⟨.adjectivePhrase, .trope⟩

/-- Adjectival modification targets a noun (13). -/
def Form.AdmitsAdjectivalModification (f : Form) : Prop := f.embedded = .noun

/-- Determiners other than *het* select a noun; *het* alone carries the nominalization of an
adjective phrase (14). -/
def Form.AdmitsOtherDeterminers (f : Form) : Prop := f.embedded = .noun

/-- Generic use needs a kind (15). -/
def Form.AdmitsGeneric (f : Form) : Prop := f.denotation = .kind

instance : DecidablePred Form.AdmitsAdjectivalModification :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Form.AdmitsOtherDeterminers :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Form.AdmitsGeneric := fun _ ↦ inferInstanceAs (Decidable (_ = _))

theorem inflected_diagnostics :
    (¬ inflected.AdmitsAdjectivalModification ∧ ¬ inflected.AdmitsOtherDeterminers ∧
      ¬ inflected.AdmitsGeneric) ∧
    ∀ f ∈ [uninflected, derived],
      f.AdmitsAdjectivalModification ∧ f.AdmitsOtherDeterminers ∧ f.AdmitsGeneric := by
  decide

theorem fails_iff_inflected (f : Form) (hf : f ∈ [uninflected, derived, inflected]) :
    (¬ f.AdmitsAdjectivalModification ∨ ¬ f.AdmitsOtherDeterminers ∨ ¬ f.AdmitsGeneric) ↔
      f = inflected := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> decide

/-- The three analyses of the inflected form the paper weighs (§2.3): a category-changing
nominalization, ellipsis of a noun, and *het* as the nominalization operator over an adjective
phrase, the one adopted. -/
inductive InflectedAnalysis where
  | nominalisation
  | ellipsis
  | hetAsCap
  deriving DecidableEq, Repr

end McNallyDeSwart2011
