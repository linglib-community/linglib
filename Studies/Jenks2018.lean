module

public import Linglib.Data.Examples.Jenks2018
public import Linglib.Semantics.Reference.Description
public import Linglib.Semantics.Genericity.NominalMappingParameter
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.Mandarin.Determiners
public import Linglib.Fragments.Cantonese.Determiners
public import Linglib.Fragments.German.Determiners
public import Linglib.Fragments.Lakhota.Determiners
public import Linglib.Fragments.Akan.Determiners

/-!
# Jenks (2018): Articulated Definiteness without Articles

Jenks argues that Mandarin, which has no definite article, still distinguishes Schwarz's two
definites: a unique definite is a bare noun read by Chierchia's covert ι, and an anaphoric definite
is a demonstrative description whose demonstrative supplies the index of ι^x (22). Three principles
over a language's determiner inventory derive the distribution. The Blocking Principle (23) makes ι
available exactly when no overt determiner marks uniqueness, as in Mandarin but not in Cantonese,
whose [Clf-N] marks both presuppositions; ι^x is never a covert shift (Section 4.2); and Index!
(50) requires the indexed form wherever an index is available, unless the description is a
continuing topic (Section 5.3). The types of Table 2 are read off these principles: a
presupposition is marked where the bare noun cannot express it, so [a marked uniqueness brings a
marked familiarity](##isUpperSet_marked) and no language marks uniqueness alone.

## Implementation notes

* The Blocking Principle (23) is the theory layer's `Determiner.Inventory.Blocks`, under which an
  article blocks ι when it marks uniqueness and a demonstrative blocks nothing.
* The environments are the paper's six, read as `DefiniteDescription.Use`s, the donkey environment
  being an anaphoric use under quantification, and mapped to Schwarz's presupposition types by
  `DefiniteDescription.Use.strength`. The marked form is the language's form for the
  environment's presupposition: an article marking it or, for familiarity, a demonstrative, whose
  description is the strong article's. Cantonese's restricted demonstrative (57) is not modelled.
* Jenks types the index of ι^x as a property (Section 4.4); `DefiniteDescription.anaphoric` carries
  an individual index, so Section 4.4 is not formalized.

## References

* [jenks-2018]
* [schwarz-2009]
* [schwarz-2013]
* [chierchia-1998]
-/

@[expose] public section

namespace Jenks2018

open Determiner
open scoped Denotes
open DefiniteDescription (Restrictor)

/-! ### Environments and principles -/

/-- A description's discourse status (Section 5.3) is no topic, a continuing topic or a new one. -/
inductive Topic
  | none
  | continuing
  | new
  deriving DecidableEq, Repr

/-- An index is available exactly in the environments licensed by familiarity, Section 5.1:
prior mention of the referent or, in producer-product bridging, of its argument. -/
def IndexAvailable (env : DefiniteDescription.Use) : Prop := env.strength = .familiarity

/-- An inventory has a form for a presupposition when an article marks it or, for familiarity,
when it has a demonstrative, whose description is the strong article's
(`DemonstrativeDeterminer.denote_selector_eq_anaphoric`) and so supplies the index of ι^x. -/
def HasForm (inv : Inventory) : DefiniteDescription.Strength → Prop
  | .uniqueness => inv.Marks .uniqueness
  | .familiarity => inv.Marks .familiarity ∨ inv.Realizes .demonstrative

instance (inv : Inventory) : DecidablePred (HasForm inv) := fun p ↦ by
  cases p <;> unfold HasForm <;> infer_instance

/-- The bare noun is licit when the Blocking Principle (23) leaves ι available, no overt determiner
marking uniqueness, and, by Index! (50), no indexed form competes, or when the description is a
continuing topic (Section 5.3). -/
def BareLicit (inv : Inventory) (env : DefiniteDescription.Use) (t : Topic) : Prop :=
  ¬ inv.Blocks .iota ∧ (¬ (IndexAvailable env ∧ HasForm inv .familiarity) ∨ t = .continuing)

/-- The marked form is licit when the inventory has a form for the environment's presupposition. -/
def MarkedLicit (inv : Inventory) (env : DefiniteDescription.Use) : Prop := HasForm inv env.strength

instance (env : DefiniteDescription.Use) : Decidable (IndexAvailable env) := by
  unfold IndexAvailable; infer_instance

instance (inv : Inventory) (env : DefiniteDescription.Use) (t : Topic) :
    Decidable (BareLicit inv env t) := by
  unfold BareLicit; infer_instance

instance (inv : Inventory) (env : DefiniteDescription.Use) : Decidable (MarkedLicit inv env) := by
  unfold MarkedLicit; infer_instance

theorem not_bareLicit_of_indexAvailable {inv : Inventory} {env : DefiniteDescription.Use}
    {t : Topic}
    (h : IndexAvailable env) (hm : HasForm inv .familiarity) (ht : t ≠ .continuing) :
    ¬ BareLicit inv env t :=
  fun ⟨_, h'⟩ ↦ h'.elim (fun h'' ↦ h'' ⟨h, hm⟩) ht

/-! ### Type-shifting under blocking -/

/-- Mandarin has no overt exponent of uniqueness, so its bare nouns are unique definites by the
covert ι. -/
theorem not_blocks_iota_mandarin : ¬ Mandarin.Determiners.inventory.Blocks .iota := by
  decide

/-- Cantonese [Clf-N] marks uniqueness, so its bare nouns have no definite shift. -/
theorem blocks_iota_cantonese : Cantonese.Determiners.inventory.Blocks .iota := by
  decide

/-! ### The data -/

/-- A row records the language's inventory, the environment, the discourse status, and the
judgments on the bare and the marked form where the paper gives them. -/
structure Row where
  inventory : Inventory
  env : DefiniteDescription.Use
  topic : Topic
  bare : Option Bool
  marked : Option Bool

def envOf : String → Option DefiniteDescription.Use
  | "largerSituation" => some .largerSituation
  | "immediateSituation" => some .immediateSituation
  | "partWholeBridging" => some (.bridging .partWhole)
  | "producerBridging" => some (.bridging .relational)
  | "anaphoric" => some .anaphoric
  | "donkey" => some .anaphoric
  | _ => none

def topicOf : String → Option Topic
  | "none" => some .none
  | "continuing" => some .continuing
  | "new" => some .new
  | _ => none

/-- A row from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let inv ← match e.language with
    | "mand1415" => some Mandarin.Determiners.inventory
    | "cant1236" => some Cantonese.Determiners.inventory
    | _ => none
  let env ← (e.feature? "environment").bind envOf
  let t ← (e.feature? "topic").bind topicOf
  some ⟨inv, env, t, (e.feature? "bare").map (· == "ok"), (e.feature? "marked").map (· == "ok")⟩

/-- The Mandarin data of Sections 3 and 5 and the Cantonese data of Section 6. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- A judgment, where the paper gives one, agrees with a prediction. -/
def Agrees (p : Prop) : Option Bool → Prop
  | none => True
  | some b => p ↔ b = true

instance (p : Prop) [Decidable p] : ∀ o, Decidable (Agrees p o)
  | none => inferInstanceAs (Decidable True)
  | some _ => inferInstanceAs (Decidable (_ ↔ _))

/-- Row by row, the paper judges the bare noun licit exactly when `BareLicit` holds and the marked
form exactly when `MarkedLicit` does ((10), (20), (49), (51), (56)). -/
theorem rows_agree :
    ∀ r ∈ rows, Agrees (BareLicit r.inventory r.env r.topic) r.bare ∧
      Agrees (MarkedLicit r.inventory r.env) r.marked := by
  decide

/-! ### Demonstratives are strict (Section 4.3) -/

-- (27), (30)
theorem demonstrative_eq_some_iff {E W : Type} (R : Restrictor E W) (d : ℕ) (g : Assignment E)
    (s : W) (x : E) :
    ⟦DefiniteDescription.demonstrative R d⟧ g s = some x ↔ R g s (g d) ∧ x = g d :=
  DefiniteDescription.denote_anaphoric_eq_some_iff R d g s

/-- A demonstrative cannot covary through the situation pronoun, its referents at any two situations
coinciding. -/
theorem demonstrative_rigid {E W : Type} (R : Restrictor E W) (d : ℕ) (g : Assignment E)
    {s s' : W} {x x' : E} (h : ⟦DefiniteDescription.demonstrative R d⟧ g s = some x)
    (h' : ⟦DefiniteDescription.demonstrative R d⟧ g s' = some x') : x = x' :=
  DefiniteDescription.denote_anaphoric_rigid R d g s h h'

/-- The bare noun's covert ι does covary. Over the restrictor true of the situation itself, the bare
noun denotes each situation at that situation, so distinct situations give distinct referents. -/
theorem bare_covaries {W : Type} (g : Assignment W) (s : W) :
    ⟦DefiniteDescription.bare fun _ s x ↦ x = s⟧ g s = some s :=
  (DefiniteDescription.denote_bare_eq_some_iff _ _ _).2 ⟨rfl, fun _ h ↦ h⟩

/-! ### The typology (Table 2) -/

section Typology

open DefiniteDescription (Strength)

/-- A presupposition is marked when, outside a topic, the bare noun cannot express it in the
environments that call for it. -/
def Marked (inv : Inventory) (p : Strength) : Prop :=
  ∀ env : DefiniteDescription.Use, env.strength = p → ¬ BareLicit inv env .none

theorem marked_uniqueness_iff (inv : Inventory) : Marked inv .uniqueness ↔ inv.Blocks .iota := by
  refine ⟨fun h ↦ not_not.1 fun hι ↦ h .largerSituation rfl ⟨hι, .inl nofun⟩,
    fun hι _ _ h ↦ h.1 hι⟩

theorem marked_familiarity_iff (inv : Inventory) :
    Marked inv .familiarity ↔ inv.Blocks .iota ∨ HasForm inv .familiarity := by
  refine ⟨fun h ↦ ?_, fun h env he hb ↦ ?_⟩
  · by_contra hn
    exact h .anaphoric rfl ⟨(not_or.1 hn).1, .inl fun hx ↦ (not_or.1 hn).2 hx.2⟩
  · rcases h with h | h
    · exact hb.1 h
    · exact hb.2.elim (fun hn ↦ hn ⟨he, h⟩) nofun

instance (inv : Inventory) : DecidablePred (Marked inv)
  | .uniqueness => decidable_of_iff _ (marked_uniqueness_iff inv).symm
  | .familiarity => decidable_of_iff _ (marked_familiarity_iff inv).symm

/-- Since a bare noun without ι has no definite reading, a marked uniqueness brings a marked
familiarity: the marked presuppositions form an upper set in every language (p. 530). -/
theorem isUpperSet_marked (inv : Inventory) : IsUpperSet {p | Marked inv p} :=
  Strength.isUpperSet_iff.2 fun h ↦
    (marked_familiarity_iff inv).2 (.inl ((marked_uniqueness_iff inv).1 h))

variable (M : Strength → Prop) (ds : Inventory)

/-- A generally marked inventory marks both presuppositions with one form. -/
def IsGenerallyMarked : Prop := M .uniqueness ∧ M .familiarity ∧ ds.IsSyncretic

/-- A bipartite inventory marks both presuppositions, with distinct forms. -/
def IsBipartite : Prop := M .uniqueness ∧ M .familiarity ∧ ¬ ds.IsSyncretic

/-- A marked-unique inventory marks the unique presupposition only. -/
def IsMarkedUnique : Prop := M .uniqueness ∧ ¬ M .familiarity

/-- A marked-anaphoric inventory marks the anaphoric presupposition only. -/
def IsMarkedAnaphoric : Prop := ¬ M .uniqueness ∧ M .familiarity

theorem not_isMarkedUnique (inv : Inventory) : ¬ IsMarkedUnique (Marked inv) :=
  fun ⟨hu, hf⟩ ↦ hf (isUpperSet_marked inv (by decide : Strength.uniqueness ≤ .familiarity) hu)

/-- The fragments derive Table 2's columns, German being bipartite, Mandarin and Akan marked
anaphoric, and Cantonese and English generally marked. -/
theorem table2 :
    IsBipartite (Marked German.Determiners.inventory) German.Determiners.inventory ∧
      IsMarkedAnaphoric (Marked Mandarin.Determiners.inventory) ∧
      IsMarkedAnaphoric (Marked Akan.Determiners.inventory) ∧
      IsGenerallyMarked (Marked Cantonese.Determiners.inventory) Cantonese.Determiners.inventory ∧
      IsGenerallyMarked (Marked English.Determiners.inventory) English.Determiners.inventory := by
  simp only [IsBipartite, IsMarkedAnaphoric, IsGenerallyMarked]
  decide

end Typology

end Jenks2018
