module

public import Linglib.Data.Examples.Jenks2018
public import Linglib.Semantics.Reference.Description
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
continuing topic (Section 5.3).

## Implementation notes

* The environments are the paper's six, read as `DefiniteDescription.Use`s, the donkey environment
  being an anaphoric use under quantification, and mapped to Schwarz's presupposition types by
  `DefiniteDescription.Use.strength`. The marked form is the language's obligatory exponent of the
  environment's presupposition, the demonstrative in Mandarin and [Clf-N] in Cantonese, so
  Cantonese's restricted demonstrative (57) is not modelled.
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

/-- By the Blocking Principle (23), the covert ι is available exactly when no overt determiner
marks uniqueness. -/
def IotaAvailable (inv : Inventory) : Prop := ¬ inv.Marks .uniqueness

/-- An index is available exactly in the environments licensed by familiarity, Section 5.1:
prior mention of the referent or, in producer-product bridging, of its argument. -/
def IndexAvailable (env : DefiniteDescription.Use) : Prop := env.strength = .familiarity

/-- The bare noun is licit when ι is available and, by Index! (50), no indexed form competes, or
when the description is a continuing topic (Section 5.3). -/
def BareLicit (inv : Inventory) (env : DefiniteDescription.Use) (t : Topic) : Prop :=
  IotaAvailable inv ∧ (¬ (IndexAvailable env ∧ inv.Marks .familiarity) ∨ t = .continuing)

/-- The marked form is licit when the inventory marks the environment's presupposition. -/
def MarkedLicit (inv : Inventory) (env : DefiniteDescription.Use) : Prop := inv.Marks env.strength

instance (inv : Inventory) : Decidable (IotaAvailable inv) := by
  unfold IotaAvailable; infer_instance

instance (env : DefiniteDescription.Use) : Decidable (IndexAvailable env) := by
  unfold IndexAvailable; infer_instance

instance (inv : Inventory) (env : DefiniteDescription.Use) (t : Topic) :
    Decidable (BareLicit inv env t) := by
  unfold BareLicit; infer_instance

instance (inv : Inventory) (env : DefiniteDescription.Use) : Decidable (MarkedLicit inv env) := by
  unfold MarkedLicit; infer_instance

theorem not_bareLicit_of_indexAvailable {inv : Inventory} {env : DefiniteDescription.Use}
    {t : Topic}
    (h : IndexAvailable env) (hm : inv.Marks .familiarity) (ht : t ≠ .continuing) :
    ¬ BareLicit inv env t :=
  fun ⟨_, h'⟩ ↦ h'.elim (fun h'' ↦ h'' ⟨h, hm⟩) ht

/-! ### Type-shifting under blocking -/

/-- Mandarin has no overt exponent of uniqueness, so its bare nouns are unique definites by the
covert ι. -/
theorem iotaAvailable_mandarin : IotaAvailable Mandarin.Determiners.inventory := by
  decide

/-- Cantonese [Clf-N] marks uniqueness, so its bare nouns have no definite shift. -/
theorem not_iotaAvailable_cantonese : ¬ IotaAvailable Cantonese.Determiners.inventory := by
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

variable (ds : Inventory)

/-- A bipartite inventory marks both presuppositions, with distinct forms. -/
def IsBipartite : Prop := ds.strengths = Finset.univ ∧ ¬ ds.IsSyncretic

/-- A marked-anaphoric inventory marks the anaphoric presupposition only. -/
def IsMarkedAnaphoric : Prop := ds.strengths = {.familiarity}

/-- A generally marked inventory marks both presuppositions with one form. -/
def IsGenerallyMarked : Prop := ds.IsSyncretic

/-- A marked-unique inventory marks the unique presupposition only. -/
def IsMarkedUnique : Prop := ds.strengths = {.uniqueness}

/-- The fragments derive Table 2's columns, German being bipartite, Mandarin marked anaphoric, and
Cantonese and English generally marked. -/
theorem table2 :
    IsBipartite German.Determiners.inventory ∧ IsMarkedAnaphoric Mandarin.Determiners.inventory ∧
      IsGenerallyMarked Cantonese.Determiners.inventory ∧
      IsGenerallyMarked English.Determiners.inventory :=
  ⟨⟨German.Determiners.strengths_inventory, German.Determiners.not_isSyncretic_inventory⟩,
    Mandarin.Determiners.strengths_inventory, Cantonese.Determiners.isSyncretic_inventory,
    English.Determiners.isSyncretic_inventory⟩

theorem not_isMarkedUnique_of_isUpperSet (h : IsUpperSet (ds.strengths : Set Strength)) :
    ¬ IsMarkedUnique ds := fun hu ↦ by
  have := Strength.isUpperSet_iff.1 h
  rw [IsMarkedUnique] at hu
  simp [hu] at this

/-- Table 2's languages with a fragment are German and Lakhota, Mandarin and Akan, and Cantonese
and English. -/
def table2Inventories : List Inventory :=
  [German.Determiners.inventory, Lakhota.Determiners.inventory, Mandarin.Determiners.inventory,
    Akan.Determiners.inventory, Cantonese.Determiners.inventory, English.Determiners.inventory]

/-- In each language of Table 2 the marked presuppositions form an upper set (p. 530). -/
theorem isUpperSet_strengths :
    ∀ ds ∈ table2Inventories, IsUpperSet (ds.strengths : Set Strength) := by
  simp only [Strength.isUpperSet_iff, Finset.mem_coe]
  decide

end Typology

end Jenks2018
