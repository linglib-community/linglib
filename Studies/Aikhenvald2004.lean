module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.OrdConnected
public import Linglib.Semantics.Evidentiality.Paradigm
public import Linglib.Fragments.Turkish.Evidentiality
public import Linglib.Fragments.Abkhaz.Evidentiality
public import Linglib.Fragments.Slavic.Bulgarian.Evidentiality
public import Linglib.Fragments.Aymara.Evidentiality
public import Linglib.Fragments.Quechua.Evidentiality
public import Linglib.Fragments.Tuyuca.Evidentiality
public import Linglib.Fragments.Tariana.Evidentiality
public import Linglib.Fragments.Kashaya.Evidentiality
public import Linglib.Fragments.WestGreenlandic.Evidentiality
public import Linglib.Fragments.Georgian.Evidentiality
public import Linglib.Data.Examples.Aikhenvald2004
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

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
paradigm, though each, read as a system on its own, is A3; Euchee's auditory evidential is A5.

Where several sources are at hand, Tuyuca and Tariana prefer their evidentials in the order
visual, non-visual, inferred, reported, assumed, the order of their inventories. The assumed
evidential is then used only when assumption is the one source at hand
(`preferred_eq_assumed_iff`), and a speaker with both a report and visible results uses the
inferred evidential (`tariana_preferred_inferred`).

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
* [linn-2000]
* [oswalt-1986]
* [willett-1988]
-/

@[expose] public section

namespace Aikhenvald2004

open Evidential

/-! ### The systems -/

open Examples (Kind Term)

namespace Examples.Kind


/-- The number of evidentiality choices, counting an evidentiality-neutral term. -/
def choices : Kind → ℕ
  | .a1 | .a2 | .a3 | .a4 | .a5 => 2
  | .b1 | .b2 | .b3 | .b4 | .b5 => 3
  | .c1 | .c2 | .c3 => 4
  | .d1 => 5

/-- The kinds organized around an evidentiality-neutral "everything else" term. -/
def HasDefault (k : Kind) : Prop := k ∈ ({.a2, .a3, .a5, .b5} : Finset Kind)

instance : DecidablePred HasDefault := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

open Parameter in
/-- The systems of each kind, each the list of its marked terms with the parameters they cover.
They are the rows of Table 2.1, and for an everything-else kind the terms opposed to the neutral
one. -/
def rows : Kind → List (List (Term × Finset Parameter))
  | .a1 =>
    [[(.firsthand, {visual, sensory}),
        (.nonfirsthand, {inference, assumption, hearsay, quotative})],
      [(.firsthand, {visual}),
        (.nonfirsthand, {sensory, inference, assumption, hearsay, quotative})],
      [(.firsthand, {visual, sensory}), (.nonfirsthand, {inference, assumption})]]
  | .a2 =>
    [[(.nonfirsthand, {inference, assumption, hearsay, quotative})],
      [(.nonfirsthand, {sensory, inference, assumption, hearsay, quotative})]]
  | .a3 => [[(.reported, {hearsay, quotative})]]
  | .a4 => [[(.nonVisual, {sensory}), (.reported, {hearsay, quotative})]]
  | .a5 => [[(.auditory, {sensory})]]
  | .b1 =>
    [[(.direct, {visual, sensory}), (.inferred, {inference, assumption}),
      (.reported, {hearsay, quotative})]]
  | .b2 =>
    [[(.visual, {visual}), (.nonVisual, {sensory}), (.inferred, {inference, assumption})],
      [(.visual, {visual}), (.nonVisual, {sensory}),
        (.inferred, {inference, assumption, hearsay, quotative})]]
  | .b3 => [[(.visual, {visual}), (.nonVisual, {sensory}), (.reported, {hearsay, quotative})]]
  | .b4 =>
    [[(.nonVisual, {sensory}), (.inferred, {inference, assumption}),
      (.reported, {hearsay, quotative})]]
  | .b5 => [[(.reported, {hearsay}), (.quotative, {quotative})]]
  | .c1 =>
    [[(.visual, {visual}), (.nonVisual, {sensory}), (.inferred, {inference, assumption}),
      (.reported, {hearsay, quotative})]]
  | .c2 =>
    [[(.direct, {visual, sensory}), (.inferred, {inference}), (.assumed, {assumption}),
      (.reported, {hearsay, quotative})]]
  | .c3 =>
    [[(.direct, {visual, sensory}), (.inferred, {inference, assumption}), (.reported, {hearsay}),
      (.quotative, {quotative})]]
  | .d1 =>
    [[(.visual, {visual}), (.nonVisual, {sensory}), (.inferred, {inference}),
      (.assumed, {assumption}), (.reported, {hearsay, quotative})]]

theorem ordConnected_cells (k : Kind) :
    ∀ r ∈ k.rows, ∀ c ∈ r, (c.2 : Set Parameter).OrdConnected := by
  revert k; decide +kernel

theorem nonempty_cells (k : Kind) : ∀ r ∈ k.rows, ∀ c ∈ r, c.2.Nonempty := by
  revert k; decide +kernel

theorem pairwise_disjoint_cells (k : Kind) :
    ∀ r ∈ k.rows, r.Pairwise fun c d ↦ Disjoint c.2 d.2 := by
  revert k; decide +kernel

theorem length_rows (k : Kind) :
    ∀ r ∈ k.rows, r.length + (if k.HasDefault then 1 else 0) = k.choices := by
  revert k; decide +kernel

theorem length_rows_lt (k : Kind) : ∀ r ∈ k.rows, r.length < Fintype.card Parameter := by
  revert k; decide +kernel

theorem eq_of_perm (k k' : Kind) :
    ∀ r ∈ k.rows, ∀ r' ∈ k'.rows, (r.map Prod.snd).Perm (r'.map Prod.snd) → k = k' := by
  revert k k'; decide +kernel

theorem b1_willett :
    b1.rows.map (·.map Prod.snd) =
      [[EvidenceType.attested.block, EvidenceType.inferring.block,
        EvidenceType.reported.block]] := by
  decide

/-- The names of the terms of a kind's systems. -/
def terms (k : Kind) : Finset Term := (k.rows.flatMap (·.map Prod.fst)).toFinset

theorem a2_rows_subset : a2.rows ⊆ a1.rows.map (·.filter (·.1 ≠ .firsthand)) := by decide

end Examples.Kind

/-! ### Inventories -/

/-- An inventory realizes a kind when its evidentials cover the terms of one of the kind's
systems, one evidential to a term. -/
def Realizes (es : List Evidential) (k : Kind) : Prop :=
  ∃ r ∈ k.rows, (es.map covers).Perm (r.map Prod.snd)

instance (es : List Evidential) (k : Kind) : Decidable (Realizes es k) :=
  inferInstanceAs (Decidable (∃ r ∈ k.rows, _))

namespace Realizes

variable {es : List Evidential} {k k' : Kind}

theorem eq (h : Realizes es k) (h' : Realizes es k') : k = k' := by
  obtain ⟨r, hr, hp⟩ := h
  obtain ⟨r', hr', hp'⟩ := h'
  exact Kind.eq_of_perm k k' r hr r' hr' (hp.symm.trans hp')

theorem nonempty (h : Realizes es k) {e : Evidential} (he : e ∈ es) : e.covers.Nonempty := by
  obtain ⟨r, hr, hp⟩ := h
  obtain ⟨c, hc, hce⟩ := List.mem_map.1 (hp.subset (List.mem_map_of_mem he))
  exact hce ▸ Kind.nonempty_cells k r hr c hc

theorem wellFormed (h : Realizes es k) : WellFormed es := by
  obtain ⟨r, hr, hp⟩ := h
  exact List.pairwise_map.1 <|
    (List.pairwise_map.2 (Kind.pairwise_disjoint_cells k r hr)).perm hp.symm (·.symm)

theorem length_add (h : Realizes es k) :
    es.length + (if k.HasDefault then 1 else 0) = k.choices := by
  obtain ⟨r, hr, hp⟩ := h
  rw [← List.length_map (f := covers), hp.length_eq, List.length_map]
  exact Kind.length_rows k r hr

end Realizes

theorem not_realizes_nil (k : Kind) : ¬ Realizes [] k := by
  revert k; decide +kernel

/-! ### The Fragment languages -/

theorem turkish : Realizes Turkish.Evidentiality.evidentials .a2 := by decide

theorem abkhaz : Realizes Abkhaz.Evidentiality.evidentials .a2 := by decide

theorem bulgarian : Realizes Bulgarian.Evidentiality.evidentials .a2 := by decide

theorem aymara : Realizes Aymara.Evidentiality.evidentials .b1 := by decide

theorem quechua : Realizes Quechua.Evidentiality.evidentials .b1 := by decide

theorem tuyuca : Realizes Tuyuca.Evidentiality.evidentials .d1 := by decide

theorem tariana : Realizes Tariana.Evidentiality.evidentials .d1 := by decide

/-- Georgian, whose perfect is a strategy on Aikhenvald's reading, has no system of evidentials;
read as an evidential, as most grammars read it, the perfect makes one of the kind A2. -/
theorem georgian (k : Kind) :
    ¬ Realizes Georgian.Evidentiality.evidentials k ∧
      Realizes Georgian.Evidentiality.strategies .a2 :=
  ⟨not_realizes_nil k, by decide⟩

open Kashaya.Evidentiality in
theorem kashaya_spontaneous (a : Aspect.Perfectivity) (k : Kind) :
    ¬ Realizes (paradigm .spontaneous a) k := fun h ↦ by
  have := h.nonempty (e := performative a) List.mem_cons_self
  cases a <;> simp [performative] at this

theorem westGreenlandic_not_wellFormed :
    ¬ WellFormed WestGreenlandic.Evidentiality.evidentials := by
  decide

theorem westGreenlandic (k : Kind) : ¬ Realizes WestGreenlandic.Evidentiality.evidentials k :=
  fun h ↦ westGreenlandic_not_wellFormed h.wellFormed

theorem westGreenlandic_a3 :
    ∀ e ∈ WestGreenlandic.Evidentiality.evidentials, Realizes [e] .a3 := by
  decide

/-! ### Preferred evidentials -/

-- Diagram 10.1
theorem preferred_eq_assumed_iff (S : Finset Parameter) :
    (preferred Tuyuca.Evidentiality.evidentials S = some Tuyuca.Evidentiality.assumed ↔
        S = {.assumption}) ∧
      (preferred Tariana.Evidentiality.evidentials S = some Tariana.Evidentiality.assumed ↔
        S = {.assumption}) := by
  revert S; decide +kernel

theorem tariana_preferred_inferred :
    preferred Tariana.Evidentiality.evidentials {.inference, .hearsay} =
      some Tariana.Evidentiality.inferred := by
  decide +kernel

theorem tariana_preferred_singleton {es : List Evidential}
    (h : es.Perm Tariana.Evidentiality.evidentials) (p : Parameter) :
    preferred es {p} = preferred Tariana.Evidentiality.evidentials {p} :=
  (tariana.wellFormed.perm h.symm).preferred_singleton_perm h p

/-! ### Euchee -/

/-- The Euchee auditory evidential *-ke*, as Linn analyses it; an earlier grammar takes it for a
locative only. -/
def eucheeKe : Evidential := { morphs := [.suff "ke"], covers := {.sensory} }

theorem euchee : Realizes [eucheeKe] .a5 := by decide

/-! ### The book's examples -/

/-- The parameters an example's information source takes in. -/
def Examples.InfoSource.parameters : Examples.InfoSource → Finset Parameter
  | .visual => {.visual}
  | .nonvisual => {.sensory}
  | .inference => {.inference}
  | .assumption => {.assumption}
  | .report => {.hearsay, .quotative}
  | .nonfirsthand => {.inference, .assumption, .hearsay, .quotative}

theorem examples_source_subset_cell :
    ∀ x ∈ Examples.all, ∀ k ∈ Examples.kind x, ∀ t ∈ Examples.term x,
      ∀ s ∈ Examples.infoSource x, ∃ r ∈ k.rows, ∃ c ∈ r, c.1 = t ∧ s.parameters ⊆ c.2 := by
  decide

/-- The terms illustrated by the examples from a language. -/
def illustrated (lang : Glottocode) : Finset Term :=
  ((Examples.all.filter (·.language = lang)).filterMap Examples.term).toFinset

theorem tariana_illustration : illustrated .tariana = Kind.d1.terms := by
  decide

theorem wanka_illustration : illustrated .jaujaWancaQuechua = Kind.b1.terms := by
  decide

theorem turkish_illustration : illustrated .turkish = Kind.a2.terms := by
  decide

end Aikhenvald2004
