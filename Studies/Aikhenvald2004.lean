module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.OrdConnected
public import Linglib.Semantics.Evidential.Basic
public import Linglib.Fragments.Turkish.Evidentiality
public import Linglib.Fragments.Abkhaz.Evidentiality
public import Linglib.Fragments.Slavic.Bulgarian.Evidentiality
public import Linglib.Fragments.Aymara.Evidentiality
public import Linglib.Fragments.Quechua.Evidentiality
public import Linglib.Fragments.Tuyuca.Evidentiality
public import Linglib.Fragments.Tariana.Evidentiality
public import Linglib.Fragments.Kashaya.Evidentiality
public import Linglib.Fragments.WestGreenlandic.Evidentiality
public import Linglib.Data.Examples.Aikhenvald2004

/-!
# Aikhenvald (2004): Evidentiality

This file formalizes the typology of grammatical evidentiality systems in chapter 2 of
Aikhenvald's *Evidentiality*. A system is classified by how many information sources a speaker
must choose among and how they are grouped: five kinds with two choices (A1–A5), five with
three, three with four and one with five (D1). Table 2.1 draws the systems as rows over the six
semantic parameters, each term spanning the parameters it covers, and leaves out the four kinds
organized around an evidentiality-neutral "everything else" term.

A kind's systems (`Kind.rows`) are its rows of the table, or, for an everything-else kind, the
marked terms opposed to the neutral one. Every term spans an interval of the parameters
(`Kind.ordConnected_cells`), and the letter counts the terms plus one for an everything-else
term (`Kind.length_rows`). An inventory realizes a kind when its evidentials cover the terms of
one of its systems, one evidential to a term (`Realizes`); it then realizes no other kind, is
well formed, and has as many evidentials as the kind has marked terms. Turkish, Abkhaz and
Bulgarian realize A2, their unmarked pasts read as evidentiality-neutral, Aymara and Cuzco
Quechua B1, Tuyuca and Tariana D1. The Kashaya performative lies outside the six parameters, so
a spontaneous remark realizes no kind; West Greenlandic's synonymous reported evidentials form no
paradigm, though each, read as a system on its own, is A3.

## Implementation notes

The rows follow Table 2.1 cell for cell, including its A4 term, which the table gives as
non-visual although the book's prose describes the Ngiyambaa sensory evidential as covering
seeing too. The A2 systems are the two opposites of a firsthand term the A1 rows draw, the book
describing the non-firsthand of both kinds as the opposite of the firsthand. An inventory
realizes a system only when it covers each term exactly, so a system whose term covers less
than its cell, as a B1 system whose first term is visual only, realizes none.

## References

* [aikhenvald-2004]
* [barnes-1984]
* [fortescue-2003]
* [oswalt-1986]
* [willett-1988]
-/

@[expose] public section

namespace Aikhenvald2004

open Evidential

/-! ### The systems -/

/-- The book's names for the terms of evidentiality systems. -/
inductive Term
  | firsthand | nonfirsthand | direct | visual | nonVisual | auditory | inferred | assumed
  | reported | quotative
  deriving DecidableEq, Repr

/-- The fourteen kinds of evidentiality system, the letter giving the number of choices and the
digit the grouping of information sources. -/
inductive Kind
  | A1 | A2 | A3 | A4 | A5 | B1 | B2 | B3 | B4 | B5 | C1 | C2 | C3 | D1
  deriving DecidableEq, Repr, Fintype

namespace Kind

/-- The number of evidentiality choices, counting an evidentiality-neutral term. -/
def choices : Kind → ℕ
  | .A1 | .A2 | .A3 | .A4 | .A5 => 2
  | .B1 | .B2 | .B3 | .B4 | .B5 => 3
  | .C1 | .C2 | .C3 => 4
  | .D1 => 5

/-- The kinds organized around an evidentiality-neutral "everything else" term. -/
def HasDefault (k : Kind) : Prop := k ∈ ({.A2, .A3, .A5, .B5} : Finset Kind)

instance : DecidablePred HasDefault := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

open Parameter in
/-- The systems of each kind, each the list of its marked terms with the parameters they cover.
They are the rows of Table 2.1, and for an everything-else kind the terms opposed to the neutral
one. -/
def rows : Kind → List (List (Term × Finset Parameter))
  | .A1 =>
    [[(.firsthand, {visual, sensory}),
        (.nonfirsthand, {inference, assumption, hearsay, quotative})],
      [(.firsthand, {visual}),
        (.nonfirsthand, {sensory, inference, assumption, hearsay, quotative})],
      [(.firsthand, {visual, sensory}), (.nonfirsthand, {inference, assumption})]]
  | .A2 =>
    [[(.nonfirsthand, {inference, assumption, hearsay, quotative})],
      [(.nonfirsthand, {sensory, inference, assumption, hearsay, quotative})]]
  | .A3 => [[(.reported, {hearsay, quotative})]]
  | .A4 => [[(.nonVisual, {sensory}), (.reported, {hearsay, quotative})]]
  | .A5 => [[(.auditory, {sensory})]]
  | .B1 =>
    [[(.direct, {visual, sensory}), (.inferred, {inference, assumption}),
      (.reported, {hearsay, quotative})]]
  | .B2 =>
    [[(.visual, {visual}), (.nonVisual, {sensory}), (.inferred, {inference, assumption})],
      [(.visual, {visual}), (.nonVisual, {sensory}),
        (.inferred, {inference, assumption, hearsay, quotative})]]
  | .B3 => [[(.visual, {visual}), (.nonVisual, {sensory}), (.reported, {hearsay, quotative})]]
  | .B4 =>
    [[(.nonVisual, {sensory}), (.inferred, {inference, assumption}),
      (.reported, {hearsay, quotative})]]
  | .B5 => [[(.reported, {hearsay}), (.quotative, {quotative})]]
  | .C1 =>
    [[(.visual, {visual}), (.nonVisual, {sensory}), (.inferred, {inference, assumption}),
      (.reported, {hearsay, quotative})]]
  | .C2 =>
    [[(.direct, {visual, sensory}), (.inferred, {inference}), (.assumed, {assumption}),
      (.reported, {hearsay, quotative})]]
  | .C3 =>
    [[(.direct, {visual, sensory}), (.inferred, {inference, assumption}), (.reported, {hearsay}),
      (.quotative, {quotative})]]
  | .D1 =>
    [[(.visual, {visual}), (.nonVisual, {sensory}), (.inferred, {inference}),
      (.assumed, {assumption}), (.reported, {hearsay, quotative})]]

/-- Every term covers an interval of the parameters, so that in Aikhenvald's order no term skips
one. -/
theorem ordConnected_cells (k : Kind) :
    ∀ r ∈ k.rows, ∀ c ∈ r, (c.2 : Set Parameter).OrdConnected := by
  revert k; decide +kernel

/-- Every term covers some parameter. -/
theorem nonempty_cells (k : Kind) : ∀ r ∈ k.rows, ∀ c ∈ r, c.2.Nonempty := by
  revert k; decide +kernel

/-- The terms of a system cover disjoint parameters. -/
theorem pairwise_disjoint_cells (k : Kind) :
    ∀ r ∈ k.rows, r.Pairwise fun c d ↦ Disjoint c.2 d.2 := by
  revert k; decide +kernel

/-- The letter of a kind counts the terms of each of its systems, plus one for an everything-else
term. -/
theorem length_rows (k : Kind) :
    ∀ r ∈ k.rows, r.length + (if k.HasDefault then 1 else 0) = k.choices := by
  revert k; decide +kernel

/-- No system gives each of the six parameters a term of its own. -/
theorem length_rows_lt (k : Kind) : ∀ r ∈ k.rows, r.length < Fintype.card Parameter := by
  revert k; decide +kernel

/-- Distinct kinds have no system in common, even up to the order of the terms. -/
theorem eq_of_perm (k k' : Kind) :
    ∀ r ∈ k.rows, ∀ r' ∈ k'.rows, (r.map Prod.snd).Perm (r'.map Prod.snd) → k = k' := by
  revert k k'; decide +kernel

/-- B1 groups the parameters into Willett's three types of evidence. -/
theorem B1_willett :
    B1.rows.map (·.map Prod.snd) =
      [[EvidenceType.attested.block, EvidenceType.inferring.block,
        EvidenceType.reported.block]] := by
  decide

/-- The names of the terms of a kind's systems. -/
def terms (k : Kind) : Finset Term := (k.rows.flatMap (·.map Prod.fst)).toFinset

/-- The non-firsthand term of an A2 system is that of an A1 system, the neutral term replacing
the firsthand one. -/
theorem A2_rows_subset : A2.rows ⊆ A1.rows.map (·.filter (·.1 ≠ .firsthand)) := by decide

end Kind

/-! ### Inventories -/

/-- An inventory realizes a kind when its evidentials cover the terms of one of the kind's
systems, one evidential to a term. -/
def Realizes (es : List Evidential) (k : Kind) : Prop :=
  ∃ r ∈ k.rows, (es.map covers).Perm (r.map Prod.snd)

instance (es : List Evidential) (k : Kind) : Decidable (Realizes es k) :=
  inferInstanceAs (Decidable (∃ r ∈ k.rows, _))

namespace Realizes

variable {es : List Evidential} {k k' : Kind}

/-- An inventory realizes at most one kind. -/
theorem eq (h : Realizes es k) (h' : Realizes es k') : k = k' := by
  obtain ⟨r, hr, hp⟩ := h
  obtain ⟨r', hr', hp'⟩ := h'
  exact Kind.eq_of_perm k k' r hr r' hr' (hp.symm.trans hp')

/-- The evidentials of an inventory realizing a kind each cover some parameter. -/
theorem nonempty (h : Realizes es k) {e : Evidential} (he : e ∈ es) : e.covers.Nonempty := by
  obtain ⟨r, hr, hp⟩ := h
  obtain ⟨c, hc, hce⟩ := List.mem_map.1 (hp.subset (List.mem_map_of_mem he))
  exact hce ▸ Kind.nonempty_cells k r hr c hc

/-- An inventory realizing a kind is well formed. -/
theorem wellFormed (h : Realizes es k) : WellFormed es := by
  obtain ⟨r, hr, hp⟩ := h
  exact List.pairwise_map.1 <|
    (List.pairwise_map.2 (Kind.pairwise_disjoint_cells k r hr)).perm hp.symm (·.symm)

/-- An inventory realizing a kind has one evidential for each of its marked terms. -/
theorem length_add (h : Realizes es k) :
    es.length + (if k.HasDefault then 1 else 0) = k.choices := by
  obtain ⟨r, hr, hp⟩ := h
  rw [← List.length_map (f := covers), hp.length_eq, List.length_map]
  exact Kind.length_rows k r hr

end Realizes

/-- An empty inventory, an evidentiality strategy or none at all, realizes no kind. -/
theorem not_realizes_nil (k : Kind) : ¬ Realizes [] k := by
  revert k; decide +kernel

/-! ### The Fragment languages -/

theorem turkish : Realizes Turkish.Evidentiality.evidentials .A2 := by decide

theorem abkhaz : Realizes Abkhaz.Evidentiality.evidentials .A2 := by decide

theorem bulgarian : Realizes Bulgarian.Evidentiality.evidentials .A2 := by decide

theorem aymara : Realizes Aymara.Evidentiality.evidentials .B1 := by decide

theorem quechua : Realizes Quechua.Evidentiality.evidentials .B1 := by decide

theorem tuyuca : Realizes Tuyuca.Evidentiality.evidentials .D1 := by decide

theorem tariana : Realizes Tariana.Evidentiality.evidentials .D1 := by decide

open Kashaya.Evidentiality in
/-- The Kashaya performative covers none of the six parameters, so in either aspect the
paradigm of a spontaneous remark realizes no kind. -/
theorem kashaya_spontaneous (a : Aspect.Perfectivity) (k : Kind) :
    ¬ Realizes (paradigm .spontaneous a) k := fun h ↦ by
  have := h.nonempty (e := performative a) List.mem_cons_self
  cases a <;> simp [performative] at this

/-- West Greenlandic's reported evidentials are synonymous, so they form no paradigm. -/
theorem westGreenlandic_not_wellFormed :
    ¬ WellFormed WestGreenlandic.Evidentiality.evidentials := by
  decide

/-- West Greenlandic's reported evidentials together realize no kind. -/
theorem westGreenlandic (k : Kind) : ¬ Realizes WestGreenlandic.Evidentiality.evidentials k :=
  fun h ↦ westGreenlandic_not_wellFormed h.wellFormed

/-- Each West Greenlandic reported evidential, read as a system on its own, is A3. -/
theorem westGreenlandic_A3 :
    ∀ e ∈ WestGreenlandic.Evidentiality.evidentials, Realizes [e] .A3 := by
  decide

/-! ### The book's examples -/

/-- The terms named by the examples' `term` feature. -/
def termNames : List (String × Term) :=
  [("firsthand", .firsthand), ("nonfirsthand", .nonfirsthand), ("direct", .direct),
    ("visual", .visual), ("nonvisual", .nonVisual), ("auditory", .auditory),
    ("inferred", .inferred), ("assumed", .assumed), ("reported", .reported),
    ("quotative", .quotative)]

/-- The kinds named by the examples' `system` feature. -/
def kindNames : List (String × Kind) :=
  [("A1", .A1), ("A2", .A2), ("A3", .A3), ("A4", .A4), ("A5", .A5), ("B1", .B1), ("B2", .B2),
    ("B3", .B3), ("B4", .B4), ("B5", .B5), ("C1", .C1), ("C2", .C2), ("C3", .C3), ("D1", .D1)]

/-- The parameters named by the examples' `source` feature. -/
def sourceNames : List (String × Parameter) :=
  [("visual", .visual), ("nonvisual", .sensory), ("inference", .inference),
    ("assumption", .assumption), ("report", .hearsay)]

/-- In every example the term used covers the source at hand, which lies in the cell of that
term in a system of the example's kind. -/
theorem examples_source_mem_cell :
    ∀ x ∈ Examples.all, ∀ k ∈ x.parse? "system" kindNames, ∀ t ∈ x.parse? "term" termNames,
      ∀ p ∈ x.parse? "source" sourceNames, ∃ r ∈ k.rows, ∃ c ∈ r, c.1 = t ∧ p ∈ c.2 := by
  decide

/-- The terms illustrated by the examples from a language. -/
def illustrated (lang : String) : Finset Term :=
  ((Examples.all.filter (·.language = lang)).filterMap (·.parse? "term" termNames)).toFinset

/-- The Tariana illustration runs through every term of a D1 system. -/
theorem tariana_illustration : illustrated "tari1256" = Kind.D1.terms := by
  decide

/-- The Wanka Quechua examples run through every term of a B1 system. -/
theorem wanka_illustration : illustrated "jauj1238" = Kind.B1.terms := by
  decide

/-- The Turkish examples, of report, inference and non-visual perception, all use the
non-firsthand term of an A2 system. -/
theorem turkish_illustration : illustrated "nucl1301" = Kind.A2.terms := by
  decide

end Aikhenvald2004
