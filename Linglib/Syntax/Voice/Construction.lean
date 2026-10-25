module

public import Linglib.Syntax.Category.Verb.Defs

/-!
# Constructions and the types of voice alternation

A *construction* of a verb gives each potential participant a status: a nominal term with a
transitivity-related role, a dative oblique, an incorporated noun, an implied participant, or
absent. Comparing an initial and a derived construction of one verb, a participant is
*nucleativized* when it becomes a core term and *denucleativized* when it ceases to be one, and a
denucleativized participant is maintained in participant structure or suppressed from it. The
oriented types of voice alternation, passivization, antipassivization, decausativization and the
rest, are defined from these notions, after Creissels.

## Main definitions

* `Voice.Status`, `Voice.Construction`: a participant's status, and a construction.
* `Voice.Construction.Nucleativized`, `Denucleativized`, `Suppressed`, `fate`: comparing two
  constructions.
* `Voice.Construction.IsPassivization`, `IsAntipassivization`, `IsDecausativization`,
  `IsASNucleativization`, `IsCumulation`, `IsApplicativization`, …: the types of voice
  alternation.
* `ArgumentFrame.status`, `Diathesis.construction`: the construction of a diathesis.

## Main statements

* `Voice.Construction.valency_eq_of_nucleativized_of_denucleativized`: nucleativization is not
  valency increase.
* `Voice.Construction.fate_eq_denucleativized_iff`: a participant's fate is denucleativized
  exactly when it is denucleativized within participant structure.
* `Voice.Construction.IsPassivization.not_isDecausativization`: passivization keeps the initial A
  in participant structure, decausativization does not.

## References

* [creissels-2024]
* [levin-1993]
-/

@[expose] public section

namespace Voice

/-! ### Transitivity-related roles -/

/-- The role of a nominal term in [creissels-2024]'s binary core-term system is one of the
core roles S, A and P, or X for an oblique. -/
inductive TermRole where
  /-- The sole core term of an intransitive clause. -/
  | S
  /-- The agent-like core term of a transitive clause. -/
  | A
  /-- The patient-like core term of a transitive clause. -/
  | P
  /-- An oblique. -/
  | X
  deriving DecidableEq, Repr

/-- The transitivity-related role of a comparative coding role, under which recipients and
themes are P-like core terms. -/
def TermRole.ofArgumentRole : ArgumentRole → TermRole
  | .S => .S
  | .A => .A
  | .P | .R | .T => .P

/-! ### Participant fate -/

/-- What a voice does to a core term of the initial construction. -/
inductive ParticipantFate where
  /-- Not a core term of the derived construction, but maintained in participant structure
      as an oblique or an implied participant. -/
  | denucleativized
  /-- Removed from participant structure. -/
  | suppressed
  /-- A core term of the derived construction. -/
  | maintained
  /-- One core term of the derived construction with another initial core term. -/
  | cumulated
  /-- Not a core term of the initial construction. -/
  | na
  deriving DecidableEq, Repr

/-- The fate removes the participant from core-term status. -/
def ParticipantFate.RemovesFromCoreStatus : ParticipantFate → Prop
  | .denucleativized | .suppressed => True
  | _ => False

instance : DecidablePred ParticipantFate.RemovesFromCoreStatus := fun f ↦ by
  cases f <;> unfold ParticipantFate.RemovesFromCoreStatus <;> infer_instance

/-! ### Constructions -/

/-- A construction expresses a potential participant of its verb as a nominal term with a
transitivity-related role, as a dative oblique or as an incorporated noun, leaves it implied but
unexpressed, or has it outside participant structure. -/
inductive Status where
  | term (r : TermRole)
  | dative
  | incorporated
  | implicit
  | absent
  deriving DecidableEq, Repr

namespace Status

/-- The role of the nominal term, datives counting as obliques. -/
def role : Status → Option TermRole
  | term r => some r
  | dative => some .X
  | _ => none

/-- A participant is nuclear when it is expressed as a core term. -/
def Nuclear : Status → Prop
  | term r => r ≠ .X
  | _ => False

instance : DecidablePred Nuclear := fun s ↦ by cases s <;> unfold Nuclear <;> infer_instance

end Status

/-- A construction of a verb gives each of its potential participants a status. -/
abbrev Construction (ι : Type*) := ι → Status

namespace Construction

variable {ι : Type*} (c d : Construction ι)

/-- A transitive construction has an A term and a P term. -/
def Transitive : Prop := (∃ i, c i = .term .A) ∧ ∃ i, c i = .term .P

/-- An impersonal construction has neither an A term nor an S term. -/
def Impersonal : Prop := ∀ i, c i ≠ .term .A ∧ c i ≠ .term .S

open Finset in
/-- The valency of a construction is its number of nuclear participants. -/
def valency [Fintype ι] : ℕ := #{i | (c i).Nuclear}

/-! Comparing an initial construction `c` with a derived construction `d` of the same verb. -/

/-- A participant that is not a core term of the initial construction is one of the derived
construction. -/
def Nucleativized (i : ι) : Prop := ¬ (c i).Nuclear ∧ (d i).Nuclear

/-- A core term of the initial construction is not one of the derived construction. -/
def Denucleativized (i : ι) : Prop := (c i).Nuclear ∧ ¬ (d i).Nuclear

/-- A core term of the initial construction is removed from participant structure. -/
def Suppressed (i : ι) : Prop := (c i).Nuclear ∧ d i = .absent

/-- A participant that is not a core term of the initial construction is expressed, differently,
by the derived construction. -/
def Introduced (i : ι) : Prop := ¬ (c i).Nuclear ∧ c i ≠ d i ∧ (d i).role.isSome

/-- A core term of the initial construction shares its derived A or S term with another initial
core term. A clause has one A and one S, so two participants with the same one share it. -/
def Cumulated (i : ι) : Prop :=
  (c i).Nuclear ∧ (d i = .term .A ∨ d i = .term .S) ∧ ∃ j, j ≠ i ∧ (c j).Nuclear ∧ d j = d i

/-- Some participant is nucleativized. -/
def Nucleativizes : Prop := ∃ i, c.Nucleativized d i

/-- Some participant is denucleativized. -/
def Denucleativizes : Prop := ∃ i, c.Denucleativized d i

/-- Some initial core term is cumulated with another. -/
def Cumulates : Prop := ∃ i, c.Cumulated d i

/-- The alternation is valency-increasing when it nucleativizes without denucleativizing. -/
structure IsValencyIncreasing : Prop where
  /-- Some participant becomes a core term. -/
  nucleativizes : c.Nucleativizes d
  /-- No initial core term ceases to be one. -/
  not_denucleativizes : ¬ c.Denucleativizes d

theorem isValencyIncreasing_iff :
    c.IsValencyIncreasing d ↔ c.Nucleativizes d ∧ ¬ c.Denucleativizes d :=
  ⟨fun h ↦ ⟨h.nucleativizes, h.not_denucleativizes⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- The alternation is valency-decreasing when it denucleativizes without nucleativizing. -/
structure IsValencyDecreasing : Prop where
  /-- Some initial core term ceases to be one. -/
  denucleativizes : c.Denucleativizes d
  /-- No participant becomes a core term. -/
  not_nucleativizes : ¬ c.Nucleativizes d

theorem isValencyDecreasing_iff :
    c.IsValencyDecreasing d ↔ c.Denucleativizes d ∧ ¬ c.Nucleativizes d :=
  ⟨fun h ↦ ⟨h.denucleativizes, h.not_nucleativizes⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- The alternation is symmetrical when it neither nucleativizes nor denucleativizes and does
not change the transitivity of the construction ([creissels-2024] §8.1.7). A cumulation changes
transitivity without doing either. -/
structure IsSymmetrical : Prop where
  /-- No participant becomes a core term. -/
  not_nucleativizes : ¬ c.Nucleativizes d
  /-- No initial core term ceases to be one. -/
  not_denucleativizes : ¬ c.Denucleativizes d
  /-- Transitivity is unaffected. -/
  transitive_iff : c.Transitive ↔ d.Transitive

theorem isSymmetrical_iff : c.IsSymmetrical d ↔
    ¬ c.Nucleativizes d ∧ ¬ c.Denucleativizes d ∧ (c.Transitive ↔ d.Transitive) :=
  ⟨fun h ↦ ⟨h.not_nucleativizes, h.not_denucleativizes, h.transitive_iff⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

theorem isSymmetrical_self : c.IsSymmetrical c :=
  ⟨fun ⟨_, h⟩ ↦ h.1 h.2, fun ⟨_, h⟩ ↦ h.2 h.1, .rfl⟩

variable {c d} in
theorem IsValencyIncreasing.not_isSymmetrical (h : c.IsValencyIncreasing d) :
    ¬ c.IsSymmetrical d := fun h' ↦ h'.not_nucleativizes h.nucleativizes

variable {c d} in
theorem IsValencyDecreasing.not_isSymmetrical (h : c.IsValencyDecreasing d) :
    ¬ c.IsSymmetrical d := fun h' ↦ h'.not_denucleativizes h.denucleativizes

section Fintype

variable [Fintype ι] [DecidableEq ι]

instance : Decidable c.Transitive := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable c.Impersonal := inferInstanceAs (Decidable (∀ _, _))
instance (i : ι) : Decidable (c.Nucleativized d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (c.Denucleativized d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (c.Suppressed d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (c.Introduced d i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ι) : Decidable (c.Cumulated d i) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (c.Nucleativizes d) := inferInstanceAs (Decidable (∃ _, _))
instance : Decidable (c.Denucleativizes d) := inferInstanceAs (Decidable (∃ _, _))
instance : Decidable (c.Cumulates d) := inferInstanceAs (Decidable (∃ _, _))
instance : Decidable (c.IsValencyIncreasing d) :=
  decidable_of_iff _ (isValencyIncreasing_iff c d).symm
instance : Decidable (c.IsValencyDecreasing d) :=
  decidable_of_iff _ (isValencyDecreasing_iff c d).symm
instance : Decidable (c.IsSymmetrical d) := decidable_of_iff _ (isSymmetrical_iff c d).symm

/-- An initial core term is suppressed when it leaves participant structure, cumulated when it
shares its derived core term with another, maintained when it remains a core term, and
denucleativized otherwise. -/
def fate (i : ι) : ParticipantFate :=
  if (c i).Nuclear then
    if d i = .absent then .suppressed
    else if (d i).Nuclear then if c.Cumulated d i then .cumulated else .maintained
    else .denucleativized
  else .na

theorem fate_eq_denucleativized_iff (i : ι) :
    c.fate d i = .denucleativized ↔ c.Denucleativized d i ∧ d i ≠ .absent := by
  unfold fate Denucleativized
  split_ifs <;> simp_all

theorem fate_eq_suppressed_iff (i : ι) : c.fate d i = .suppressed ↔ c.Suppressed d i := by
  unfold fate Suppressed
  split_ifs <;> simp_all

/-- An alternation may nucleativize one participant and denucleativize another, keeping the valency,
so nucleativization is not valency increase ([creissels-2024] §8.1.3). -/
theorem valency_eq_of_nucleativized_of_denucleativized {c d : Construction ι} {i j : ι}
    (hi : c.Nucleativized d i) (hj : c.Denucleativized d j)
    (h : ∀ k, k ≠ i → k ≠ j → ((c k).Nuclear ↔ (d k).Nuclear)) : c.valency = d.valency :=
  Finset.card_equiv (Equiv.swap i j) fun k ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hk : k = i
    · subst hk; rw [Equiv.swap_apply_left]; exact iff_of_false hi.1 hj.2
    by_cases hk' : k = j
    · subst hk'; rw [Equiv.swap_apply_right]; exact iff_of_true hj.1 hi.2
    rw [Equiv.swap_apply_of_ne_of_ne hk hk']; exact h k hk hk'

end Fintype

/-! ### The types of voice alternation -/

/-- The derived construction implies the same participants as the initial one. -/
def PreservesStructure : Prop := ∀ i, c i = .absent ↔ d i = .absent

/-- In passivization the initial construction is transitive, its A is denucleativized but
maintained in participant structure, and no participant is nucleativized ([creissels-2024]
§8.3.2.1). -/
structure IsPassivization : Prop where
  /-- The initial construction is transitive. -/
  transitive : c.Transitive
  /-- The initial A is not a core term of the derived construction. -/
  denucleativized_A : ∀ i, c i = .term .A → c.Denucleativized d i
  /-- The initial A stays in participant structure. -/
  maintained_A : ∀ i, c i = .term .A → d i ≠ .absent
  /-- No participant becomes a core term. -/
  not_nucleativizes : ¬ c.Nucleativizes d
  /-- The initial P remains a core term, as S in the canonical case and as P after a double-P
  construction (footnote 1 of §8.1.3). -/
  nuclear_P : ∀ i, c i = .term .P → (d i).Nuclear

/-- In I-passivization, the impersonal variant of passivization, the initial P keeps its coding,
so the derived construction has neither A nor S ([creissels-2024] §8.3.2.2). -/
structure IsImpersonalPassivization : Prop extends c.IsPassivization d where
  /-- The derived construction has neither A nor S. -/
  impersonal : d.Impersonal

/-- In antipassivization the initial construction is transitive, participant structure is
unchanged, the initial P is denucleativized and no participant is nucleativized, and the initial
A becomes the S of an intransitive construction, or keeps the role of A after a double-P
construction ([creissels-2024] §8.3.2). -/
structure IsAntipassivization : Prop where
  /-- The initial construction is transitive. -/
  transitive : c.Transitive
  /-- Participant structure is unchanged. -/
  preservesStructure : c.PreservesStructure d
  /-- An initial P is not a core term of the derived construction. -/
  denucleativized_P : ∃ i, c i = .term .P ∧ c.Denucleativized d i
  /-- No participant becomes a core term. -/
  not_nucleativizes : ¬ c.Nucleativizes d
  /-- The initial A becomes S, or stays A. -/
  A_to_S_or_A : ∀ i, c i = .term .A → d i = .term .S ∨ d i = .term .A

/-- In S-denucleativization the initial construction is intransitive, and its S is
denucleativized but maintained in participant structure, without nucleativization of any other
participant ([creissels-2024] §8.3.2.4). -/
structure IsSDenucleativization : Prop where
  /-- The initial construction is intransitive. -/
  not_transitive : ¬ c.Transitive
  /-- The initial construction has an S. -/
  exists_S : ∃ i, c i = .term .S
  /-- The initial S is not a core term of the derived construction. -/
  denucleativized_S : ∀ i, c i = .term .S → c.Denucleativized d i
  /-- The initial S stays in participant structure. -/
  maintained_S : ∀ i, c i = .term .S → d i ≠ .absent
  /-- No participant becomes a core term. -/
  not_nucleativizes : ¬ c.Nucleativizes d

/-- In decausativization the initial construction is transitive, its A is suppressed from
participant structure, and its P becomes the S of an intransitive construction ([creissels-2024]
§8.3.1.2). -/
structure IsDecausativization : Prop where
  /-- The initial construction is transitive. -/
  transitive : c.Transitive
  /-- The initial A leaves participant structure. -/
  suppressed_A : ∀ i, c i = .term .A → c.Suppressed d i
  /-- The initial P becomes S. -/
  P_to_S : ∀ i, c i = .term .P → d i = .term .S

/-- In A/S-nucleativization a participant is nucleativized and takes over the role of A or S, the
initial A or S coded as P or denucleativized. Causativization, where the new participant
instigates or controls the event, the A/S-nucleativization of an oblique, and concernativization,
where it is a concernee of the initial S or P, share this structure ([creissels-2024] §8.3.1.1,
§8.3.4). -/
structure IsASNucleativization (i : ι) : Prop where
  /-- The participant becomes a core term. -/
  nucleativized : c.Nucleativized d i
  /-- The participant is the derived A or S. -/
  eq_A_or_S : d i = .term .A ∨ d i = .term .S
  /-- The initial A or S becomes P or is denucleativized. -/
  A_or_S_to_P : ∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .P ∨ ¬ (d j).Nuclear

/-- In reflexivization and reciprocalization two participant roles expressed as A and P, or as S
and a dative oblique, are cumulated by the S term of the derived construction ([creissels-2024]
§8.3.3). -/
def IsCumulation : Prop :=
  ∃ a p, a ≠ p ∧ ((c a = .term .A ∧ c p = .term .P) ∨ (c a = .term .S ∧ c p = .dative)) ∧
    d a = .term .S ∧ d p = .term .S

/-- In applicativization the initial A or S keeps the role of A or S, and the derived
construction introduces, in a role other than A or S, an applied participant ([creissels-2024]
§8.3.5). -/
structure IsApplicativization (applied : ι) : Prop where
  /-- The initial A or S stays A or S. -/
  A_or_S_to_A_or_S : ∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .A ∨ d j = .term .S
  /-- The applied participant is introduced. -/
  introduced : c.Introduced d applied
  /-- The applied participant is not the derived A. -/
  ne_A : d applied ≠ .term .A
  /-- The applied participant is not the derived S. -/
  ne_S : d applied ≠ .term .S

/-- In P-applicativization the applied phrase is a P, and the initial A or S is the A of the
derived transitive construction. -/
structure IsPApplicativization (applied : ι) : Prop extends c.IsApplicativization d applied where
  /-- The applied participant is a P. -/
  eq_P : d applied = .term .P
  /-- The initial A or S becomes A. -/
  A_or_S_to_A : ∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .A

/-- In D-applicativization the applied phrase is a dative oblique. -/
structure IsDApplicativization (applied : ι) : Prop extends c.IsApplicativization d applied where
  /-- The applied participant is a dative. -/
  eq_dative : d applied = .dative

/-- In X-applicativization the applied phrase is an ordinary oblique. -/
structure IsXApplicativization (applied : ι) : Prop extends c.IsApplicativization d applied where
  /-- The applied participant is an oblique. -/
  eq_X : d applied = .term .X

/-- In portative derivation an intransitive verb of motion becomes transitive, its S the A of the
derived construction and a carried entity its P ([creissels-2024] §8.3.7). -/
structure IsPortative (carried : ι) : Prop where
  /-- The initial construction is intransitive. -/
  not_transitive : ¬ c.Transitive
  /-- The carried entity becomes a core term. -/
  nucleativized : c.Nucleativized d carried
  /-- The carried entity is the P. -/
  eq_P : d carried = .term .P
  /-- The initial S becomes A. -/
  S_to_A : ∀ j, c j = .term .S → d j = .term .A

section Types

variable (i : ι)

theorem isPassivization_iff : c.IsPassivization d ↔
    c.Transitive ∧ (∀ i, c i = .term .A → c.Denucleativized d i) ∧
      (∀ i, c i = .term .A → d i ≠ .absent) ∧ ¬ c.Nucleativizes d ∧
      ∀ i, c i = .term .P → (d i).Nuclear :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩, fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

theorem isImpersonalPassivization_iff :
    c.IsImpersonalPassivization d ↔ c.IsPassivization d ∧ d.Impersonal :=
  ⟨fun h ↦ ⟨h.toIsPassivization, h.impersonal⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

theorem isAntipassivization_iff : c.IsAntipassivization d ↔
    c.Transitive ∧ c.PreservesStructure d ∧ (∃ i, c i = .term .P ∧ c.Denucleativized d i) ∧
      ¬ c.Nucleativizes d ∧ ∀ i, c i = .term .A → d i = .term .S ∨ d i = .term .A :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩, fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

theorem isSDenucleativization_iff : c.IsSDenucleativization d ↔
    ¬ c.Transitive ∧ (∃ i, c i = .term .S) ∧ (∀ i, c i = .term .S → c.Denucleativized d i) ∧
      (∀ i, c i = .term .S → d i ≠ .absent) ∧ ¬ c.Nucleativizes d :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩, fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

theorem isDecausativization_iff : c.IsDecausativization d ↔
    c.Transitive ∧ (∀ i, c i = .term .A → c.Suppressed d i) ∧
      ∀ i, c i = .term .P → d i = .term .S :=
  ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

theorem isASNucleativization_iff : c.IsASNucleativization d i ↔
    c.Nucleativized d i ∧ (d i = .term .A ∨ d i = .term .S) ∧
      ∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .P ∨ ¬ (d j).Nuclear :=
  ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

theorem isApplicativization_iff : c.IsApplicativization d i ↔
    (∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .A ∨ d j = .term .S) ∧
      c.Introduced d i ∧ d i ≠ .term .A ∧ d i ≠ .term .S :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩⟩

theorem isPApplicativization_iff : c.IsPApplicativization d i ↔
    c.IsApplicativization d i ∧ d i = .term .P ∧
      ∀ j, (c j = .term .A ∨ c j = .term .S) → d j = .term .A :=
  ⟨fun h ↦ ⟨h.toIsApplicativization, h.eq_P, h.A_or_S_to_A⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

theorem isDApplicativization_iff :
    c.IsDApplicativization d i ↔ c.IsApplicativization d i ∧ d i = .dative :=
  ⟨fun h ↦ ⟨h.toIsApplicativization, h.eq_dative⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

theorem isXApplicativization_iff :
    c.IsXApplicativization d i ↔ c.IsApplicativization d i ∧ d i = .term .X :=
  ⟨fun h ↦ ⟨h.toIsApplicativization, h.eq_X⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

theorem isPortative_iff : c.IsPortative d i ↔
    ¬ c.Transitive ∧ c.Nucleativized d i ∧ d i = .term .P ∧ ∀ j, c j = .term .S → d j = .term .A :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩⟩

variable [Fintype ι] [DecidableEq ι]

instance : Decidable (c.PreservesStructure d) := inferInstanceAs (Decidable (∀ _, _))
instance : Decidable (c.IsPassivization d) := decidable_of_iff _ (isPassivization_iff c d).symm
instance : Decidable (c.IsImpersonalPassivization d) :=
  decidable_of_iff _ (isImpersonalPassivization_iff c d).symm
instance : Decidable (c.IsAntipassivization d) :=
  decidable_of_iff _ (isAntipassivization_iff c d).symm
instance : Decidable (c.IsSDenucleativization d) :=
  decidable_of_iff _ (isSDenucleativization_iff c d).symm
instance : Decidable (c.IsDecausativization d) :=
  decidable_of_iff _ (isDecausativization_iff c d).symm
instance : Decidable (c.IsASNucleativization d i) :=
  decidable_of_iff _ (isASNucleativization_iff c d i).symm
instance : Decidable (c.IsCumulation d) := inferInstanceAs (Decidable (∃ _, _))
instance : Decidable (c.IsApplicativization d i) :=
  decidable_of_iff _ (isApplicativization_iff c d i).symm
instance : Decidable (c.IsPApplicativization d i) :=
  decidable_of_iff _ (isPApplicativization_iff c d i).symm
instance : Decidable (c.IsDApplicativization d i) :=
  decidable_of_iff _ (isDApplicativization_iff c d i).symm
instance : Decidable (c.IsXApplicativization d i) :=
  decidable_of_iff _ (isXApplicativization_iff c d i).symm
instance : Decidable (c.IsPortative d i) := decidable_of_iff _ (isPortative_iff c d i).symm

end Types

variable {c d}

theorem IsDecausativization.not_preservesStructure (h : c.IsDecausativization d) :
    ¬ c.PreservesStructure d :=
  let ⟨⟨a, ha⟩, _⟩ := h.transitive
  fun hp ↦ absurd ((hp a).mpr (h.suppressed_A a ha).2) (by simp [ha])

theorem IsPassivization.not_isDecausativization (h : c.IsPassivization d) :
    ¬ c.IsDecausativization d :=
  let ⟨⟨a, ha⟩, _⟩ := h.transitive
  fun h' ↦ h.maintained_A a ha (h'.suppressed_A a ha).2

theorem IsSDenucleativization.not_nuclear (h : c.IsSDenucleativization d)
    (hc : ∀ i, (c i).Nuclear → c i = .term .S) (i : ι) : ¬ (d i).Nuclear := fun hd ↦ by
  by_cases hi : (c i).Nuclear
  · exact (h.denucleativized_S i (hc i hi)).2 hd
  · exact h.not_nucleativizes ⟨i, hi, hd⟩

theorem IsPortative.not_isASNucleativization {i : ι} (h : c.IsPortative d i)
    (hS : ∃ s, c s = .term .S) (j : ι) : ¬ c.IsASNucleativization d j := fun h' ↦ by
  obtain ⟨s, hs⟩ := hS
  rcases h'.A_or_S_to_P s (.inr hs) with hP | hN
  · simp [h.S_to_A s hs] at hP
  · exact hN (by simp [h.S_to_A s hs, Status.Nuclear])

theorem IsSymmetrical.not_isPassivization (h : c.IsSymmetrical d) : ¬ c.IsPassivization d :=
  fun h' ↦
    let ⟨⟨a, ha⟩, _⟩ := h'.transitive
    h.not_denucleativizes ⟨a, h'.denucleativized_A a ha⟩

theorem IsSymmetrical.not_isASNucleativization (h : c.IsSymmetrical d) (i : ι) :
    ¬ c.IsASNucleativization d i :=
  fun h' ↦ h.not_nucleativizes ⟨i, h'.nucleativized⟩

end Construction

/-- The status a frame gives the participant of slot `s` is its transitivity-related role if `s` is
a core slot, X if it is an expressed oblique, and absent if it is an expletive or unfilled. An
incorporated noun expresses its participant without a term ([creissels-2024] §17.2.2). An
implicit slot leaves its participant implied, unless it is understood as the subject itself or as
its members; then the subject's term cumulates the two roles ([creissels-2024] §8.3.3). Levin's
understood reflexive and reciprocal objects are therefore cumulations, not implied participants. -/
def _root_.ArgumentFrame.status (fr : ArgumentFrame) (s : ArgumentFrame.Slot) : Status :=
  match fr.argumentRole s, fr.get? s with
  | some r, _ => .term (.ofArgumentRole r)
  | none, some .incorporated => .incorporated
  | none, some (.implicit (some .reflexive)) | none, some (.implicit (some .reciprocal)) =>
      (fr.argumentRole .external).elim .implicit (.term ∘ .ofArgumentRole)
  | none, some (.implicit _) => .implicit
  | none, some p => if p.IsExpressed then .term .X else .absent
  | none, none => .absent

/-- The construction of a diathesis gives each participant the status of its slot, absent where
the diathesis leaves it out. -/
def _root_.Diathesis.construction {n : ℕ} (d : Diathesis n) : Construction (Fin n) :=
  fun i ↦ (d.links.get i).elim .absent d.toArgumentFrame.status

end Voice
