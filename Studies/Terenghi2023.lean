module

public import Mathlib.Tactic.Order
public import Linglib.Semantics.Reference.Determiner
public import Linglib.Data.Wordlist.Terenghi2023
public import Linglib.Data.Examples.Languages
public import Linglib.Languages.Romance.Spanish.Determiners

/-!
# Terenghi (2023): Missing person

A demonstrative locates its referent near a discourse atom, and a measure can further class the
vectors from that atom by length, so every system has a person core that distance contrasts modify.
A term locates the referents in the image of its anchors under a relation of atoms to referents,
and the measure narrows the relation: those of a three-way measure [partition
NEAR](##Vectors.existsUnique_near). Mundari [grades each of its terms, Brazilian Portuguese only its
non-local term and Satawal only its participant terms](##graded). A demonstrative read at such a
relation [denotes where its term locates](##mem_denote_near_iff), Harbour's semantics when there is
no measure. Spanish *ese* [has two readings that overlap but differ](##ese_readings), of which only
the hearer's [narrows the *ese* of the grammars](##ese_anchors).

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
* [butt-benjamin-2019]
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

/-- The relation of an atom to the referents NEAR it whose vector has a length in the class `k`,
and to every referent NEAR it when there is no class: a measure narrows the relation and leaves
the anchors alone. -/
def Vectors.near (V : Vectors E D) (k : Option DistanceClass) : SetRel (Finset Role) E :=
  {p | V.Near p.1 p.2 ∧ ∀ c ∈ k, c.Mem V.cut (V.length p.1 p.2)}

theorem Vectors.near_subset_near_none (V : Vectors E D) (k : Option DistanceClass) :
    V.near k ⊆ V.near none :=
  fun _ h ↦ ⟨h.1, by simp⟩

theorem Vectors.existsUnique_near (V : Vectors E D) (h₂₁ : V.cut 2 < V.cut 1) {a : Finset Role}
    {y : E} (h : (a, y) ∈ V.near none) :
    ∃! k, k ∈ [DistanceClass.nearest, .nearer, .near] ∧ (a, y) ∈ V.near (some k) := by
  obtain ⟨k, hk, huniq⟩ := distanceClass_partition h₂₁ h.1
  exact ⟨k, ⟨hk.1, h.1, by simpa using hk.2⟩,
    fun k' hk' ↦ huniq k' ⟨hk'.1, by simpa using hk'.2.2⟩⟩

/-- A term locates the referents in the image of its anchors under the relation of its class. -/
def DeicticTerm.Locates (t : DeicticTerm) (V : Vectors E D) (y : E) : Prop :=
  y ∈ (V.near t.distance).image t.anchors

instance (t : DeicticTerm) (V : Vectors E D) (y : E) : Decidable (t.Locates V y) :=
  inferInstanceAs (Decidable (∃ a ∈ t.anchors,
    V.Near a y ∧ ∀ k ∈ t.distance, k.Mem V.cut (V.length a y)))

/-- A demonstrative read at the relation of a class denotes what the anaphoric description does
where the term with its participant sets as anchors and that class locates the indexed referent:
Harbour's semantics with the vicinity of an anchor taken as NEAR its atom, and graded where the
term carries a measure. -/
theorem mem_denote_near_iff {E W : Type} (V : Vectors E D) (k : Option DistanceClass)
    (dem : DemonstrativeDeterminer) {R : (ℕ → E) → W → Set E} {d : ℕ} {g : ℕ → E} {s : W}
    {x : E} :
    x ∈ dem.denote R d (V.near k) g s ↔
      (⟨dem.deixis, k⟩ : DeicticTerm).Locates V (g d) ∧ x ∈ Definite.anaphoric R d g s :=
  DemonstrativeDeterminer.mem_denote

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

/-! ### Spanish

The language file enters the Spanish demonstratives as Butt and Benjamin describe them: *este* near
the
speaker, *ese* at any distance from the speaker, *aquel* away from both participants. -/

-- (10a); Table 3.2
/-- The grammar's *este* and *aquel* are the first and third terms of the ternary system, and its
*ese* covers the anchors of the second and third, as the *ese* of the Latin American binary system
does. -/
theorem spanish_anchors :
    Spanish.Determiners.este.deixis = Term.dem1.anchors ∧
      Spanish.Determiners.aquel.deixis = Term.dem3.anchors ∧
        Spanish.Determiners.ese.deixis = Term.dem2.anchors ∪ Term.dem3.anchors := by
  decide

theorem mem_denote_ese_of_mem_denote_aquel {E W : Type} (N : SetRel (Finset Role) E)
    {R : (ℕ → E) → W → Set E} {d : ℕ} {g : ℕ → E} {s : W} {x : E}
    (h : x ∈ Spanish.Determiners.aquel.denote R d N g s) :
    x ∈ Spanish.Determiners.ese.denote R d N g s := by
  rw [DemonstrativeDeterminer.mem_denote] at h ⊢
  exact ⟨SetRel.image_mono (Finset.coe_subset.2 (by decide)) h.1, h.2⟩

/-- *ese* near the hearer. -/
def eseHearer : DeicticTerm := ⟨Term.dem2.anchors, none⟩

/-- *ese* at an intermediate distance from the speaker. -/
def eseSpeaker : DeicticTerm := ⟨Term.dem1.anchors, some .nearer⟩

/-- The hearer reading narrows the grammar's *ese*, and the speaker reading anchors outside it. -/
theorem ese_anchors :
    eseHearer.anchors ⊆ Spanish.Determiners.ese.deixis ∧
      Disjoint eseSpeaker.anchors Spanish.Determiners.ese.deixis := by
  decide

/-- The vectors to one referent whose lengths from the speaker's atoms are `s`, from the hearer's
atom `h` and from the others' atom `o`, under the cut-offs `9 > 6 > 3`. -/
def config (s h o : ℕ) : Vectors Unit ℕ :=
  ⟨fun a _ ↦ if Role.speaker ∈ a then s else if Role.addressee ∈ a then h else o,
    fun n ↦ 9 - 3 * n⟩

theorem ese_not_aquel :
    (⟨Spanish.Determiners.ese.deixis, none⟩ : DeicticTerm).Locates (config 12 1 12) () ∧
      ¬ (⟨Spanish.Determiners.aquel.deixis, none⟩ : DeicticTerm).Locates (config 12 1 12) () := by
  decide

/-- The two readings of *ese* overlap but differ: either may locate a referent the other does not,
and both may locate the same one. -/
theorem ese_readings :
    (eseHearer.Locates (config 8 1 12) () ∧ ¬ eseSpeaker.Locates (config 8 1 12) ()) ∧
      (eseSpeaker.Locates (config 4 12 12) () ∧ ¬ eseHearer.Locates (config 4 12 12) ()) ∧
        (eseHearer.Locates (config 4 2 12) () ∧ eseSpeaker.Locates (config 4 2 12) ()) := by
  decide

end Terenghi2023
