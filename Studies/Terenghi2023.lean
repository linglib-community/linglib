module

public import Mathlib.Tactic.Order
public import Linglib.Semantics.Reference.Determiner
public import Linglib.Data.Wordlist.Terenghi2023
public import Linglib.Data.Examples.Languages

/-!
# Terenghi (2023): Missing person

A demonstrative locates its referent near a discourse atom, the speaker, the hearer, both or
neither, and a measure can further class the vectors from that atom by length, so every system has a
person core that distance contrasts modify. The classes of lengths [partition the region near an
atom](##distanceClass_partition); Mundari [grades each of its terms, Brazilian Portuguese only its
non-local term and Satawal only its participant terms](##graded); and without a measure the
semantics [is Harbour's vicinity semantics](##locates_iff_presup). Spanish *ese* [has two readings
that overlap but differ](##ese_readings), as Harbour observes of person- and distance-based medials.

## Implementation notes

* A discourse atom is a participant set: the speaker's region `{speaker}`, the joint region
  `{speaker, addressee}`, the hearer's `{addressee}` and the others' `∅`. A term's anchors are the
  atoms its person features admit, so a cell of the person partitions of
  `Linglib/Syntax/Category/Pronoun/Demonstrative.lean`.
* The vector lengths are an abstract linear order; the context gives the length of the vector from
  each atom's region to each referent and the cut-offs `r₋ₙ` of the lengths, `r₋₀ = r` the maximal
  length for NEAR to apply. The paper's offsets `n₁ < n₂` are taken as `1` and `2`.
* The first, second and third terms of Mundari and Satawal anchor on the author, hearer and
  non-participant cells, and the local and non-local terms of Brazilian Portuguese on the
  participant and non-participant cells; a reinforcer that centres the local term on the speaker
  or the hearer narrows its anchors, and Satawal's contact term is the innermost class of its
  person term. The paper describes Mundari's third term as measuring distance from both
  participants; it anchors on the others' atom, as the non-participant term does throughout.

## TODO

* The change from ternary to binary systems as the loss of the last person feature to enter the
  derivation, the monotonicity bias, and the Last in–First out principle.
* The dual-anchor term as two structures, and the reanalysis of the participant feature as a
  measure.

## References

* [terenghi-2023]
* [harbour-2016]
-/

@[expose] public section

namespace Terenghi2023

open SpeechAct

/-! ### Proximity and distance classes -/

/-- The vectors of a context: the length of the vector from the region of each discourse atom to
each referent, and the cut-offs `r₋ₙ` of the lengths, `r₋₀` the maximal length for NEAR to
apply. -/
structure Vectors (E D : Type*) where
  length : Finset Role → E → D
  cut : ℕ → D

variable {E D : Type*} [LinearOrder D]

/-- NEAR: the referent lies at the end of a vector from the region of the atom shorter than the
maximal length. -/
def Vectors.Near (V : Vectors E D) (a : Finset Role) (y : E) : Prop := V.length a y < V.cut 0

instance (V : Vectors E D) (a : Finset Role) (y : E) : Decidable (V.Near a y) :=
  inferInstanceAs (Decidable (_ < _))

/-- A class of vector lengths: longer than the cut-off `r₋ₙ` for `n ∈ lower` and shorter than the
cut-off `r₋ₘ` for `m = upper`. -/
structure DistanceClass where
  lower : Option ℕ
  upper : ℕ
  deriving DecidableEq, Repr

/-- A length is in a class. -/
def DistanceClass.Mem (k : DistanceClass) (cut : ℕ → D) (v : D) : Prop :=
  (∀ n ∈ k.lower, cut n ≤ v) ∧ v < cut k.upper

instance (k : DistanceClass) (cut : ℕ → D) (v : D) : Decidable (k.Mem cut v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The innermost, middle and outermost classes of a three-way measure. -/
def DistanceClass.nearest : DistanceClass := ⟨none, 2⟩

@[inherit_doc DistanceClass.nearest]
def DistanceClass.nearer : DistanceClass := ⟨some 2, 1⟩

@[inherit_doc DistanceClass.nearest]
def DistanceClass.near : DistanceClass := ⟨some 1, 0⟩

/-- The classes of a three-way measure partition the lengths NEAR admits. -/
theorem distanceClass_partition {cut : ℕ → D} (h₂₁ : cut 2 < cut 1)
    {v : D} (hv : v < cut 0) :
    ∃! k, k ∈ [DistanceClass.nearest, .nearer, .near] ∧ k.Mem cut v := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases lt_or_ge v (cut 2) with h₂ | h₂
  · refine ⟨.nearest, ⟨.inl rfl, by simp [DistanceClass.nearest, DistanceClass.Mem, h₂]⟩, ?_⟩
    rintro k ⟨rfl | rfl | rfl, hk⟩ <;>
      simp_all [DistanceClass.nearest, DistanceClass.nearer, DistanceClass.near,
        DistanceClass.Mem] <;> order
  rcases lt_or_ge v (cut 1) with h₁ | h₁
  · refine ⟨.nearer, ⟨.inr (.inl rfl), by simp [DistanceClass.nearer, DistanceClass.Mem, h₂, h₁]⟩,
      ?_⟩
    rintro k ⟨rfl | rfl | rfl, hk⟩ <;>
      simp_all [DistanceClass.nearest, DistanceClass.nearer, DistanceClass.near,
        DistanceClass.Mem] <;> order
  · refine ⟨.near, ⟨.inr (.inr rfl), by simp [DistanceClass.near, DistanceClass.Mem, h₁, hv]⟩, ?_⟩
    rintro k ⟨rfl | rfl | rfl, hk⟩ <;>
      simp_all [DistanceClass.nearest, DistanceClass.nearer, DistanceClass.near,
        DistanceClass.Mem] <;> order

-- p. 124
theorem ordConnected_mem (k : DistanceClass) (cut : ℕ → D) :
    Set.OrdConnected {v | k.Mem cut v} :=
  ⟨fun _ hx _ hy _ hz ↦ ⟨fun n hn ↦ (hx.1 n hn).trans hz.1, hz.2.trans_lt hy.2⟩⟩

-- p. 124
theorem Vectors.near_of_length_le (V : Vectors E D) {a : Finset Role} {y y' : E}
    (h : V.length a y' ≤ V.length a y) (hy : V.Near a y) : V.Near a y' :=
  h.trans_lt hy

/-! ### Deictic terms -/

/-- A deictic term: the discourse atoms it anchors on and, if it carries a measure, the class of
lengths of its vectors. -/
structure DeicticTerm where
  anchors : Finset (Finset Role)
  distance : Option DistanceClass
  deriving DecidableEq

/-- A term locates a referent near one of its anchors, at a length in its class. -/
def DeicticTerm.Locates (t : DeicticTerm) (V : Vectors E D) (y : E) : Prop :=
  ∃ a ∈ t.anchors, V.Near a y ∧ ∀ k ∈ t.distance, k.Mem V.cut (V.length a y)

instance (t : DeicticTerm) (V : Vectors E D) (y : E) : Decidable (t.Locates V y) :=
  inferInstanceAs (Decidable (∃ a ∈ t.anchors, _))

section Harbour

variable {E' W P T : Type} [PartialOrder E'] (c : Kaplan.Context W E' P T) (V : Vectors E' D)

/-- Without a measure, a demonstrative locates its referent as in Harbour's semantics, the
vicinity of an anchor being NEAR its participants' atom, whenever every atom it admits is the
participants of some referent. -/
theorem locates_iff_presup (dem : DemonstrativeDeterminer) (R : DefiniteDescription.Restrictor E' W)
    (d : ℕ) (g : ℕ → E') (s : W) (h : ∀ a ∈ dem.deixis, ∃ x, c.participants x = a) :
    (dem.denote R d c {p | V.Near (c.participants p.1) p.2}).presup g s ↔
      (⟨dem.deixis, none⟩ : DeicticTerm).Locates V (g d) := by
  rw [DemonstrativeDeterminer.denote_presup]
  constructor
  · rintro ⟨x, hx, hn⟩
    exact ⟨_, hx, hn, by simp⟩
  · rintro ⟨a, ha, hn, -⟩
    obtain ⟨x, rfl⟩ := h a ha
    exact ⟨x, ha, hn⟩

end Harbour

/-! ### The paradigms -/

open Wordlist

/-- The atoms a printed term anchors on. -/
def Wordlist.Term.anchors : Term → Finset (Finset Role)
  | .dem1 => Person.first.participantSets
  | .dem2 => Person.second.participantSets
  | .dem3 | .nonLocal => Person.third.participantSets
  | .local => Person.third.participantSetsᶜ

/-- The anchors of a printed term under a subdivision, narrowed by a centring reinforcer. -/
def Wordlist.Subdivision.anchors (t : Term) : Subdivision → Finset (Finset Role)
  | .speakerCentred => t.anchors ∩ Person.first.participantSets
  | .addresseeCentred => t.anchors ∩ Person.second.participantSets
  | _ => t.anchors

/-- The class of lengths a subdivision measures. -/
def Wordlist.Subdivision.distance : Subdivision → Option DistanceClass
  | .nearest => some .nearest
  | .nearer => some .nearer
  | .near => some .near
  | .proximal | .contact => some ⟨none, 1⟩
  | .distal => some ⟨some 1, 0⟩
  | .unmarked | .speakerCentred | .addresseeCentred => none

/-- The term a printed cell is. -/
def analysis (c : Cell) : Option DeicticTerm :=
  Flat.recBotCoe (C := fun _ ↦ Option DeicticTerm) none
    (fun t ↦ some (Flat.recBotCoe (C := fun _ ↦ DeicticTerm) ⟨t.anchors, none⟩
      (fun s ↦ ⟨s.anchors t, s.distance⟩) c.subdivision)) c.term

/-- The terms of a language. -/
def terms (l : Glottocode) : List DeicticTerm :=
  (all.filter (·.lexeme.languageId = l)).filterMap (analysis ·.cell)

/-- A language measures the vectors from some anchors: a term on them carries a class. -/
def Graded (l : Glottocode) (a : Finset (Finset Role)) : Prop :=
  ∃ t ∈ terms l, t.anchors = a ∧ t.distance.isSome

instance (l : Glottocode) (a : Finset (Finset Role)) : Decidable (Graded l a) :=
  inferInstanceAs (Decidable (∃ t ∈ terms l, _))

/-- Mundari measures distance from each of its three terms, Brazilian Portuguese only from its
non-local term, and Satawal only from its first and second terms. -/
theorem graded :
    (∀ t ∈ [Term.dem1, .dem2, .dem3], Graded Glottocode.mundari t.anchors) ∧
      (Graded Glottocode.brazilianPortuguese Term.nonLocal.anchors ∧
        ¬ Graded Glottocode.brazilianPortuguese Term.local.anchors) ∧
      (Graded Glottocode.satawalese Term.dem1.anchors ∧
        Graded Glottocode.satawalese Term.dem2.anchors ∧
          ¬ Graded Glottocode.satawalese Term.dem3.anchors) := by
  decide +kernel

-- (19)
theorem mundari_terms :
    ∀ t ∈ [Term.dem1, .dem2, .dem3], ∀ k ∈ [DistanceClass.nearest, .nearer, .near],
      ⟨t.anchors, some k⟩ ∈ terms Glottocode.mundari := by
  decide +kernel

-- (3)
theorem portuguese_local_centred :
    ⟨Person.first.participantSets, none⟩ ∈ terms Glottocode.brazilianPortuguese ∧
      ⟨Person.second.participantSets, none⟩ ∈ terms Glottocode.brazilianPortuguese := by
  decide +kernel

/-! ### The dual anchor -/

/-- *ese* near the hearer. -/
def eseHearer : DeicticTerm := ⟨Person.second.participantSets, none⟩

/-- *ese* at an intermediate distance from the speaker. -/
def eseSpeaker : DeicticTerm := ⟨Person.first.participantSets, some .nearer⟩

/-- The vectors to one referent whose lengths from the speaker's atoms are `s` and from the other
atoms `h`, under the cut-offs `9 > 6 > 3`. -/
def config (s h : ℕ) : Vectors Unit ℕ :=
  ⟨fun a _ ↦ if Role.speaker ∈ a then s else h, fun n ↦ 9 - 3 * n⟩

/-- The two readings of *ese* overlap but differ: either may locate a referent the other does not,
and both may locate the same one. -/
theorem ese_readings :
    (eseHearer.Locates (config 8 1) () ∧ ¬ eseSpeaker.Locates (config 8 1) ()) ∧
      (eseSpeaker.Locates (config 4 12) () ∧ ¬ eseHearer.Locates (config 4 12) ()) ∧
        (eseHearer.Locates (config 4 2) () ∧ eseSpeaker.Locates (config 4 2) ()) := by
  decide

end Terenghi2023
