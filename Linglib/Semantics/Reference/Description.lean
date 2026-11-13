module

public import Linglib.Logic.Assignment
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Reference.Definite
public import Linglib.Semantics.Possession.Quantifier

/-!
# Definite descriptions

A definite description denotes `iota` of a restrictor at a context and a situation: the only
member of the restrictor there, and nothing when there is none or several. The
[uniqueness definite](##Definite.unique) is the weak article of Schwarz and the covert iota of a
bare noun. The [anaphoric definite](##Definite.anaphoric), his strong article, narrows the
restrictor to the value of an index, so that [the index selects the referent and the situation
only decides definedness](##Definite.mem_anaphoric), whereas the uniqueness definite's referent
covaries with the situation. The [possessive](##Definite.possessive) is the iota over the
restrictor relationalized by the possession relation, Barker's `Possession.π`, at the possessor,
and [anaphora is the possessive over identity to the
antecedent](##Definite.anaphoric_eq_possessive). An article strength [realizes one of the
two](##Definite.ofStrength).

## Implementation notes

The resource situation is a Reader argument of the denotation, as the assignment is: a situation
pronoun binding it, as Hanink proposes, is composition above the description,
`fun gs ↦ Definite.unique R g (gs n)`, not part of it. A bare noun read by the covert iota and a
noun with the weak article differ in form and not in meaning, as do a demonstrative and the strong
article, so each pair is one definite here; which forms a language has is a fact about its
determiner inventory. Indefinites do not denote a partial individual and are not descriptions. A
demonstrative's deictic content belongs to the determiner (`DemonstrativeDeterminer.denote`).

## References

* [schwarz-2009]
* [patel-grosz-grosz-2017]
* [hanink-2021]
* [moroney-2021]
* [russell-1905]
* [sharvy-1980]
* [barker-2011]
* [peters-westerstahl-2006]
-/

@[expose] public section

namespace Definite

variable {Ctx W E ι : Type*} {R : Ctx → W → Set E} {c : Ctx} {s : W} {x : E}

/-! ### The uniqueness definite -/

/-- The uniqueness definite over a restrictor denotes the only member of the restrictor at the
context and the situation: the Russellian iota, the weak article of [schwarz-2009]. -/
noncomputable def unique (R : Ctx → W → Set E) : Definite Ctx W E := fun c s ↦ iota (R c s)

/-- The uniqueness definite denotes `x` iff `x` is the unique satisfier of the restrictor at the
situation. -/
@[simp] theorem mem_unique : x ∈ unique R c s ↔ x ∈ R c s ∧ ∀ y ∈ R c s, y = x :=
  mem_iota

/-- The uniqueness definite is defined iff the restrictor has a unique satisfier at the
situation. -/
theorem unique_dom : (unique R c s).Dom ↔ ∃! x, x ∈ R c s :=
  iota_dom

/-- The uniqueness definite is undefined where the restrictor has two satisfiers. -/
theorem unique_eq_none_of_ne {y : E} (hx : x ∈ R c s) (hy : y ∈ R c s) (hne : x ≠ y) :
    unique R c s = Part.none :=
  iota_eq_none_of_ne hx hy hne

/-! ### The anaphoric definite -/

section Anaphoric

variable {R : (ι → E) → W → Set E} {d : ι} {g : ι → E}

/-- The anaphoric definite is the uniqueness definite over the restrictor narrowed to the value of
the index `d`, the strong article of [schwarz-2009]. -/
noncomputable def anaphoric (R : (ι → E) → W → Set E) (d : ι) : Definite (ι → E) W E :=
  unique fun g s ↦ R g s ∩ {g d}

/-- The anaphoric definite denotes `x` iff `x` is its antecedent and the restrictor holds of the
antecedent at the situation, so the index selects and the situation only decides definedness. -/
@[simp] theorem mem_anaphoric : x ∈ anaphoric R d g s ↔ g d ∈ R g s ∧ x = g d :=
  (Set.Subsingleton.mem_iota fun _ ha _ hb ↦ ha.2.trans hb.2.symm).trans
    ⟨fun ⟨h, hx⟩ ↦ ⟨hx ▸ h, hx⟩, fun ⟨h, hx⟩ ↦ ⟨hx ▸ h, hx⟩⟩

/-- The anaphoric definite is defined iff the restrictor holds of its antecedent at the
situation. -/
theorem anaphoric_dom : (anaphoric R d g s).Dom ↔ g d ∈ R g s := by
  rw [Part.dom_iff_mem]
  simp only [mem_anaphoric, exists_eq_right]

/-- Wherever the anaphoric definite is defined its referent is the antecedent, so the referent
does not covary with the situation. -/
theorem anaphoric_rigid {s' : W} {x' : E} (h : x ∈ anaphoric R d g s)
    (h' : x' ∈ anaphoric R d g s') : x = x' :=
  (mem_anaphoric.1 h).2.trans (mem_anaphoric.1 h').2.symm

/-- Where the antecedent is the only satisfier of the restrictor, the anaphoric definite denotes
as the uniqueness definite. -/
theorem anaphoric_eq_unique_of_forall_eq (h : ∀ y ∈ R g s, y = g d) :
    anaphoric R d g s = unique R g s :=
  congrArg iota <| Set.inter_eq_left.2 h

/-- An article strength realizes the uniqueness definite over a restrictor for uniqueness and the
anaphoric definite for familiarity, `idx` being the anaphoric index. -/
noncomputable def ofStrength (p : Strength) (R : (ι → E) → W → Set E) (idx : ι) :
    Definite (ι → E) W E :=
  match p with
  | .uniqueness => unique R
  | .familiarity => anaphoric R idx

@[simp] theorem ofStrength_uniqueness (idx : ι) : ofStrength .uniqueness R idx = unique R := rfl

@[simp] theorem ofStrength_familiarity (idx : ι) :
    ofStrength .familiarity R idx = anaphoric R idx := rfl

end Anaphoric

/-! ### The possessive -/

section Possessive

variable {possessor : Ctx → W → E} {rel : Ctx → W → E → E → Prop}

/-- The possessive is the uniqueness definite over the satisfiers of the restrictor that stand in
`rel` to the `possessor`. -/
noncomputable def possessive (R : Ctx → W → Set E) (possessor : Ctx → W → E)
    (rel : Ctx → W → E → E → Prop) : Definite Ctx W E :=
  unique fun c s ↦ Possession.π (R c s) (rel c s) (possessor c s)

/-- The possessive denotes `x` iff `x` is the unique satisfier of the restrictor that stands in the
possession relation to the possessor. -/
theorem mem_possessive :
    x ∈ possessive R possessor rel c s ↔
      (x ∈ R c s ∧ rel c s (possessor c s) x) ∧
        ∀ y, y ∈ R c s ∧ rel c s (possessor c s) y → y = x :=
  mem_iota

/-- The possessive is defined iff exactly one satisfier of the restrictor stands in the
possession relation to the possessor. -/
theorem possessive_dom :
    (possessive R possessor rel c s).Dom ↔ ∃! x, x ∈ R c s ∧ rel c s (possessor c s) x :=
  iota_dom

theorem possNP_iff_exists_mem_possessive (B : Set E) :
    Possession.PossNP (Quantifier.individual (possessor c s)) Quantifier.Det.the (rel c s)
        (R c s) B ↔ ∃ x ∈ possessive R possessor rel c s, x ∈ B := by
  rw [Possession.possNP_individual_the, Quantifier.Det.the_iff_exists_mem_iota]
  rfl

/-- The anaphoric definite is the possessive whose possessor is the antecedent and whose relation
is identity, so anaphora is relational anaphora to the referent itself. -/
theorem anaphoric_eq_possessive (R : (ι → E) → W → Set E) (d : ι) :
    anaphoric R d = possessive R (fun g _ ↦ g d) fun _ _ y x ↦ x = y := rfl

end Possessive

end Definite
