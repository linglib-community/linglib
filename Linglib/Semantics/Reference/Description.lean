module

public import Linglib.Logic.Assignment
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Reference.Definite
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Possession.Quantifier

/-!
# Nominal descriptions

A `DefiniteDescription E W` is a definite description over entities `E` at situations `W`: a bare
noun read by the covert iota, the weak (uniqueness) and strong (familiarity) articles of Schwarz, a
deictic demonstrative, and a possessive. Its denotation `⟦k⟧ g s`, relative to an entity assignment
and a resource situation, is the partial individual the description picks out, `none` when the
uniqueness presupposition fails. Every description is a Russellian iota over a restrictor at the
situation, narrowed by its form (`DefiniteDescription.restrictor`); the strong article and the
demonstrative narrow it to the indexed entity, so the anaphoric index selects the referent while the
situation only decides definedness (`mem_denote_anaphoric`, `denote_anaphoric_rigid`),
whereas the weak article's referent covaries with the situation. The possessive is the iota over the
restrictor relationalized by the possession relation, Barker's `Possession.π`, at the possessor.

## Main definitions

* `DefiniteDescription.Restrictor E W`: a property of entities at a situation, relative to an
  assignment.
* `DefiniteDescription E W`, `DefiniteDescription.restrictor`, `DefiniteDescription.denote`: the
  descriptions, the restrictor each narrows, and the iota over it.
* `DefiniteDescription.kind`, `DefiniteDescription.ofStrength`: the Frame-free kind and the
  description an article strength realizes.

## Main results

* `mem_denote_unique`, `mem_denote_anaphoric`, `mem_denote_possessive`:
  the referent conditions of the three iotas.
* `denote_bare_eq_unique`, `denote_demonstrative_eq_anaphoric`: the covert iota is the weak
  article, and deixis filters without selecting.
* `possNP_iff_exists_mem_denote_possessive`: the possessive description agrees with
  `Possession.PossNP` at an individual possessor.
* `denote_unique_restrictor`: every description is the weak article over its restrictor, and
  `denote_anaphoric_eq_unique_of_forall_eq` the strong and weak articles agree where the antecedent
  is the only satisfier.
* `denote_anaphoric_eq_possessive`: the strong article is the possessive over identity to the
  antecedent.

## Implementation notes

The resource situation is a Reader argument of the denotation, as the assignment is: a situation
pronoun binding it, as Hanink proposes, is composition above the description,
`fun gs ↦ ⟦k⟧ g (gs n)`, not a field of it. Indefinites do not denote a partial individual and are
not descriptions; `NominalKind.indefinite` records them for inventory typology only. A
demonstrative's deictic content and the presupposition it imposes belong to the determiner
(`DemonstrativeDeterminer.denote`), not to the description.

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

open scoped Denotes

/-- A restrictor is a set of entities at a situation, relative to an entity assignment. -/
abbrev DefiniteDescription.Restrictor (E W : Type) := (ℕ → E) → W → Set E

/-- A definite description is the covert iota of a bare noun, the weak or the strong article of
[schwarz-2009], a deictic demonstrative, or a possessive. -/
inductive DefiniteDescription (E W : Type) where
  /-- A bare noun read by the covert iota ([chierchia-1998], [dayal-2004]). -/
  | bare (restrictor : DefiniteDescription.Restrictor E W)
  /-- The weak article is the uniqueness definite. -/
  | unique (restrictor : DefiniteDescription.Restrictor E W)
  /-- The strong article is the familiarity definite whose antecedent is the `discourseIdx`-th
  entity of the assignment. -/
  | anaphoric (restrictor : DefiniteDescription.Restrictor E W) (discourseIdx : ℕ)
  /-- A deictic demonstrative ([moroney-2021]) is the strong article in its form, its deictic
  content being the determiner's. -/
  | demonstrative (restrictor : DefiniteDescription.Restrictor E W) (discourseIdx : ℕ)
  /-- A possessive picks the unique satisfier of the restrictor that stands in `relation` to the
  `possessor`. -/
  | possessive (restrictor : DefiniteDescription.Restrictor E W) (possessor : (ℕ → E) → W → E)
      (relation : (ℕ → E) → W → E → E → Prop)

namespace DefiniteDescription

variable {E W : Type} (R : Restrictor E W) (d : ℕ)
  (possessor : (ℕ → E) → W → E) (rel : (ℕ → E) → W → E → E → Prop) (g : ℕ → E)
  (s : W) {x : E}

/-! ### The Frame-free kind -/

/-- The kind of a description, its constructor with the payload erased. -/
def kind : DefiniteDescription E W → NominalKind
  | .bare _           => .bare
  | .unique _         => .unique
  | .anaphoric _ _    => .anaphoric
  | .demonstrative .. => .demonstrative
  | .possessive ..    => .possessive

/-- An article strength realizes the weak article over a restrictor for uniqueness and the strong
article for familiarity, `idx` being the strong article's anaphoric index. -/
def ofStrength (p : Strength) (R : Restrictor E W) (idx : ℕ) : DefiniteDescription E W :=
  match p with
  | .uniqueness  => .unique R
  | .familiarity => .anaphoric R idx

@[simp] theorem kind_ofStrength (p : Strength) (idx : ℕ) :
    (ofStrength p R idx).kind = p.toKind := by
  cases p <;> rfl

/-! ### The denotation -/

/-- A description's iota ranges over its restrictor, narrowed for the strong article and the
demonstrative to the indexed entity and for the possessive to what stands in the possession
relation to the possessor. -/
def restrictor : DefiniteDescription E W → Restrictor E W
  | .bare R | .unique R => R
  | .anaphoric R d | .demonstrative R d => fun g s ↦ R g s ∩ {g d}
  | .possessive R possessor rel => fun g s ↦ Possession.π (R g s) (rel g s) (possessor g s)

/-- A description picks out, at an assignment and a resource situation, the Russellian iota over its
restrictor ([schwarz-2009]). -/
noncomputable def denote (k : DefiniteDescription E W) : Definite (ℕ → E) W E :=
  fun g s ↦ iota (k.restrictor g s)

noncomputable instance : Denotes (DefiniteDescription E W) (Definite (ℕ → E) W E) := ⟨denote⟩

@[simp] theorem denote_bare : ⟦bare R⟧ g s = iota (R g s) := rfl

@[simp] theorem denote_unique : ⟦unique R⟧ g s = iota (R g s) := rfl

@[simp] theorem denote_anaphoric :
    ⟦anaphoric R d⟧ g s = iota (R g s ∩ {g d}) := rfl

@[simp] theorem denote_demonstrative :
    ⟦demonstrative R d⟧ g s = iota (R g s ∩ {g d}) := rfl

@[simp] theorem denote_possessive :
    ⟦possessive R possessor rel⟧ g s = iota (Possession.π (R g s) (rel g s) (possessor g s)) :=
  rfl

/-- The covert iota of a bare noun is the weak article; the two differ in form, not meaning. -/
theorem denote_bare_eq_unique : ⟦bare R⟧ = ⟦unique R⟧ := rfl

/-- A demonstrative denotes as the strong article with the same index, so deixis, a presupposition
on the referent, filters it without selecting it. -/
theorem denote_demonstrative_eq_anaphoric : ⟦demonstrative R d⟧ = ⟦anaphoric R d⟧ := rfl

/-- Every description denotes as the weak article over its restrictor, so the strong article is the
weak article over the restrictor narrowed to the antecedent. -/
theorem denote_unique_restrictor (k : DefiniteDescription E W) : ⟦unique k.restrictor⟧ = ⟦k⟧ := rfl

/-- The strong article is the possessive whose possessor is the antecedent and whose relation is
identity, so anaphora is relational anaphora to the referent itself. -/
theorem denote_anaphoric_eq_possessive :
    ⟦anaphoric R d⟧ = ⟦possessive R (fun g _ ↦ g d) fun _ _ y x ↦ x = y⟧ := rfl

/-! ### Referent conditions -/

theorem mem_denote (k : DefiniteDescription E W) :
    x ∈ ⟦k⟧ g s ↔ x ∈ k.restrictor g s ∧ ∀ y ∈ k.restrictor g s, y = x :=
  mem_iota

theorem denote_dom (k : DefiniteDescription E W) :
    (⟦k⟧ g s).Dom ↔ ∃! x, x ∈ k.restrictor g s :=
  iota_dom

/-- The weak article denotes `x` iff `x` is the unique satisfier of the restrictor at the
situation. -/
theorem mem_denote_unique : x ∈ ⟦unique R⟧ g s ↔ x ∈ R g s ∧ ∀ y ∈ R g s, y = x :=
  mem_iota

/-- The covert iota denotes `x` iff `x` is the unique satisfier of the restrictor at the
situation. -/
theorem mem_denote_bare : x ∈ ⟦bare R⟧ g s ↔ x ∈ R g s ∧ ∀ y ∈ R g s, y = x :=
  mem_iota

/-- The weak article is defined iff the restrictor has a unique satisfier at the situation. -/
theorem denote_unique_dom : (⟦unique R⟧ g s).Dom ↔ ∃! x, x ∈ R g s :=
  iota_dom

/-- The weak article is undefined where the restrictor has two satisfiers. -/
theorem denote_unique_eq_none_of_ne {y : E} (hx : x ∈ R g s) (hy : y ∈ R g s) (hne : x ≠ y) :
    ⟦unique R⟧ g s = Part.none :=
  iota_eq_none_of_ne hx hy hne

/-- The strong article denotes `x` iff `x` is its antecedent and the restrictor holds of the
antecedent at the situation, so the index selects and the situation only decides definedness. -/
theorem mem_denote_anaphoric : x ∈ ⟦anaphoric R d⟧ g s ↔ g d ∈ R g s ∧ x = g d :=
  (Set.Subsingleton.mem_iota fun _ ha _ hb ↦ ha.2.trans hb.2.symm).trans
    ⟨fun ⟨h, hx⟩ ↦ ⟨hx ▸ h, hx⟩, fun ⟨h, hx⟩ ↦ ⟨hx ▸ h, hx⟩⟩

/-- The strong article is defined iff the restrictor holds of its antecedent at the situation. -/
theorem denote_anaphoric_dom : (⟦anaphoric R d⟧ g s).Dom ↔ g d ∈ R g s := by
  rw [Part.dom_iff_mem]
  simp only [mem_denote_anaphoric, exists_eq_right]

/-- Wherever the strong article is defined its referent is the antecedent, so the referent does not
covary with the situation. -/
theorem denote_anaphoric_rigid {s' : W} {x' : E} (h : x ∈ ⟦anaphoric R d⟧ g s)
    (h' : x' ∈ ⟦anaphoric R d⟧ g s') : x = x' :=
  ((mem_denote_anaphoric R d g s).1 h).2.trans
    ((mem_denote_anaphoric R d g s').1 h').2.symm

/-- Where the antecedent is the only satisfier of the restrictor, the strong article denotes as the
weak one. -/
theorem denote_anaphoric_eq_unique_of_forall_eq (h : ∀ y ∈ R g s, y = g d) :
    ⟦anaphoric R d⟧ g s = ⟦unique R⟧ g s :=
  congrArg iota <| Set.inter_eq_left.2 h

/-- The possessive denotes `x` iff `x` is the unique satisfier of the restrictor that stands in the
possession relation to the possessor. -/
theorem mem_denote_possessive :
    x ∈ ⟦possessive R possessor rel⟧ g s ↔
      (x ∈ R g s ∧ rel g s (possessor g s) x) ∧
        ∀ y, y ∈ R g s ∧ rel g s (possessor g s) y → y = x :=
  mem_iota

/-- The possessive is defined iff exactly one satisfier of the restrictor stands in the
possession relation to the possessor. -/
theorem denote_possessive_dom :
    (⟦possessive R possessor rel⟧ g s).Dom ↔ ∃! x, x ∈ R g s ∧ rel g s (possessor g s) x :=
  iota_dom

theorem possNP_iff_exists_mem_denote_possessive (B : Set E) :
    Possession.PossNP (Quantifier.individual (possessor g s)) Quantifier.Det.the (rel g s)
        (R g s) B ↔ ∃ x ∈ ⟦possessive R possessor rel⟧ g s, x ∈ B := by
  rw [Possession.possNP_individual_the, Quantifier.Det.the_iff_exists_mem_iota, denote_possessive]

end DefiniteDescription

