/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Kawapanan.Shawi.Basic
public import Studies.Deal2024
public import Linglib.Syntax.Case.Dependent

/-!
# Dependent case by Agree: ergative in Shawi

Clem and Deal derive the Shawi ergative suffix *-ri* from Agree. The probe on v is Deal's
strictly descending grammar, [INT:φ, SAT:SPKR] with [PART] interacting dynamically:
it Agrees with a visible object and then, when the person hierarchy permits, with the subject, and
goal flagging carries the object's φ-features onto the subject, where *-ri* realizes the φ root
of the flag and object agreement on the subject realizes the rest. Ergative is thus the case of a
probe's second goal, and its distribution over Table 4 follows from the run of the probe over
the goals v can see: a high object and then the subject, or the subject alone when a
third-person object stays inside the categorizing v phase. Section 5 generalizes: a probe on v
yields ergative and a probe on T accusative, the person split of a language is the grammar of
its probe, and so global case splits range over the hierarchy effects of agreement (Tables 6–7).

## Main definitions

* `flag`, `DependentCase`: the goal flag a probe deposits on the last goal it reaches, and
  dependent case as a flag carrying an earlier goal's φ-features.
* `positions`, `goals`: the positions open to a Shawi object by its person and surface syntax,
  and the goals v meets for an object in either position.
* `Ergative`, `marking`: ergative on the subject, and Table 4's obligatory, optional and
  impossible cells.
* `oagrOnS`: object agreement on the subject, the object-agreement exponent of the flag.
* `Locus`: the probe on v or on T, ordering the goals of a transitive clause.

## Main results

* `dependentCase_iff_licit`: with two goals, dependent case on the second is Deal's licit
  Agree with both, so the PCC typology transfers to case splits.
* `halt_of_spkr_object`, `narrow_of_part_object`, `flag_of_third_object`, `flag_of_low_object`:
  the derivations (15), (17) and (19), (22), and (24) behind Table 4.
* `table4`, `marking_optional_iff`, `ergative_of_fronted_or_dropped`: the distribution of
  ergative, optionality as the structural ambiguity of third-person objects, and obligatory
  ergative with a fronted or dropped object.
* `oagrOnS_isSome`: object agreement on the subject only under ergative, and off the diagonal
  only for a first-person subject and a second-person object.
* `rule1_overgenerates`, `no_1_3_2_hierarchy`: the configurational rule fires where Shawi has
  no ergative, and no grammar of the probe space yields a 1>3>2 hierarchy.
* `dependentCase_noPCC`, `dependentCase_strong_iff`, `dependentCase_weak_iff`,
  `dependentCase_sd_iff`, `dependentCase_sd_off_diagonal_iff`: Tables 6–7, the four splits in
  either locus.

## Implementation notes

* Table 4 has no reflexive rows. The mechanism predicts ergative at 2→2 and none at 1→1, where a
  first-person object satisfies the probe, so the paper's "at least as high as" and its claim
  that object agreement on the subject is overt only at 1→2 are stated here off the diagonal;
  the paper expects the anaphor agreement effect to interfere there (§5.3).
* Locators are the paper's example and table numbers.

## References

* [clem-deal-2024]
* [deal-2024]
* [bejar-rezac-2009]
* [baker-2015]
* [barany-sheehan-2024]
* [baker-vinokurova-2010]
* [deal-2010]
* [clem-2019]
* [valenzuela-2011]
* [maslova-2003]
* [van-urk-2015]
-/

@[expose] public section

namespace ClemDeal2024

open Deal2024 Phi.PersonSegment

/-! ### Dependent case as the flag of a second goal -/

/-- A probe of grammar `g` walking `goals` in order deposits a flag on the last of them, `none` if
it never Agrees with that goal and otherwise the goals it Agreed with before, whose φ-features it
carries and transfers there with its own ((31)). -/
def flag (g : Deal2024.Grammar) (goals : List Person) : Option (List Person) :=
  let agreed := (run g goals).interacted.map (·.2)
  let last := goals.length - 1
  if last ∈ agreed then some ((agreed.filter (· < last)).filterMap fun i ↦ goals[i]?) else none

/-- A probe assigns dependent case when the last goal's flag carries the φ-features of an
    earlier goal, the structure a dependent-case vocabulary item realizes ((31), (34), (43)). -/
def DependentCase (g : Deal2024.Grammar) (goals : List Person) : Prop :=
  ∃ p l, flag g goals = some (p :: l)

instance (g : Deal2024.Grammar) (goals : List Person) : Decidable (DependentCase g goals) :=
  match h : flag g goals with
  | some (p :: l) => isTrue ⟨p, l, h⟩
  | some [] => isFalse fun ⟨_, _, h'⟩ ↦ by simp [h] at h'
  | none => isFalse fun ⟨_, _, h'⟩ ↦ by simp [h] at h'

theorem dependentCase_iff_licit (g : Deal2024.Grammar) (g₁ g₂ : Person) :
    DependentCase g [g₁, g₂] ↔ Licit g ⟨g₂, g₁⟩ := by
  revert g g₁ g₂
  decide +kernel

/-! ### Shawi: the v probe and the position of the object -/

/-- A Shawi object sits in the specifier of the categorizing v, above the phase boundary and
    visible to the v probe, or in its base position inside that phase, invisible to it ((30)). -/
inductive ObjectPosition
  | high
  | low
  deriving DecidableEq, Repr

/-- On the surface an object follows the subject (SOV or SVO), is fronted over it (OSV), or is
    dropped. -/
inductive ObjectSyntax
  | inSitu
  | fronted
  | dropped
  deriving DecidableEq, Repr

/-- An object of person `p` with surface syntax `x` may occupy these positions (§3.2). Local
    persons move to the high position obligatorily and third persons optionally, and fronting
    over the subject ((26b)) and pro-drop ((21a), as in Dinka [van-urk-2015]) require it. -/
def positions (p : Person) : ObjectSyntax → List ObjectPosition
  | .inSitu => if p.IsSAP then [.high] else [.high, .low]
  | .fronted | .dropped => [.high]

/-- The v probe meets a high object and then the subject ((22)), or the subject alone when the
    object is low or absent ((24)), by the cyclic expansion of [bejar-rezac-2009] ((13)). -/
def goals (subj obj : Person) : ObjectPosition → List Person
  | .high => [obj, subj]
  | .low => [subj]

/-- The subject is ergative when v, with [INT:φ, SAT:SPKR] and [PART] interacting dynamically
    (`Deal2024.strictlyDescending`, §3.1), Agrees with it as its second goal; *-ri* realizes the
    φ root of the flag it leaves there ((34)). -/
def Ergative (subj obj : Person) (pos : ObjectPosition) : Prop :=
  DependentCase strictlyDescending (goals subj obj pos)

instance (subj obj : Person) (pos : ObjectPosition) : Decidable (Ergative subj obj pos) :=
  inferInstanceAs (Decidable (DependentCase _ _))

/-! ### The derivations behind Table 4 -/

/-- A first-person object bears [SPKR] and satisfies the probe, which halts, so the subject is
    never reached, whatever its person (15). -/
theorem halt_of_spkr_object (subj obj : Person) (h : .speaker ∈ spec obj) :
    (run strictlyDescending [obj, subj]).satisfier.isSome ∧
      flag strictlyDescending [obj, subj] = none := by
  revert h; cases obj <;> cases subj <;> decide

/-- A second-person object lacks [SPKR] but bears [PART], so the probe is not satisfied but
    narrows to [INT:PART]; it then reaches the subject exactly when the subject bears [PART]
    ((17), (19)). -/
theorem narrow_of_part_object (subj obj : Person) (h₁ : .speaker ∉ spec obj)
    (h₂ : .participant ∈ spec obj) :
    (run strictlyDescending [obj, subj]).state = {.pi, .participant} ∧
      (flag strictlyDescending [obj, subj] = some [obj] ↔ .participant ∈ spec subj) := by
  revert h₁ h₂; cases obj <;> cases subj <;> decide

/-- A third-person object neither satisfies nor narrows the probe, so the subject is reached
    whatever its person (22). -/
theorem flag_of_third_object (subj obj : Person) (h : .participant ∉ spec obj) :
    flag strictlyDescending [obj, subj] = some [obj] := by
  revert h; cases obj <;> cases subj <;> decide

/-- With a low or absent object the probe expands and Agrees with the subject alone (24). The
    subject is Agreed with but is not a second goal, so its flag is empty and there is no
    ergative ((25)). -/
theorem flag_of_low_object (subj : Person) : flag strictlyDescending [subj] = some [] := by
  cases subj <;> decide

theorem not_ergative_low (subj obj : Person) : ¬ Ergative subj obj .low := by
  rintro ⟨p, l, h⟩
  simp [goals, flag_of_low_object] at h

/-! ### Table 4 -/

/-- The three values of a Table 4 cell. -/
inductive Marking
  | obligatory
  | optional
  | impossible
  deriving DecidableEq, Repr

/-- Table 4's cell for a subject and an in-situ object records whether the subject is ergative in
    every position open to the object, in some, or in none. -/
def marking (subj obj : Person) : Marking :=
  if ∀ pos ∈ positions obj .inSitu, Ergative subj obj pos then .obligatory
  else if ∃ pos ∈ positions obj .inSitu, Ergative subj obj pos then .optional
  else .impossible

/-- Ergative is obligatory at 1→2, impossible at 2→1, 3→1 and 3→2, and optional with a
    third-person object, as in Table 4. -/
theorem table4 :
    marking .first .second = .obligatory ∧ marking .first .third = .optional ∧
    marking .second .first = .impossible ∧ marking .second .third = .optional ∧
    marking .third .first = .impossible ∧ marking .third .second = .impossible ∧
    marking .third .third = .optional := by
  decide

/-- Optionality is the structural ambiguity of a third-person object ((23) against (24)), a cell
being optional exactly when the object may stay low. -/
theorem marking_optional_iff (subj obj : Person) :
    marking subj obj = .optional ↔ ¬ obj.IsSAP := by
  cases subj <;> cases obj <;> decide +kernel

/-- A third-person object fronted over the subject or dropped has moved high, and ergative
    becomes obligatory ((20)–(21), (26)). -/
theorem ergative_of_fronted_or_dropped (subj : Person) (x : ObjectSyntax) (hx : x ≠ .inSitu) :
    ∀ pos ∈ positions .third x, Ergative subj .third pos := by
  cases x <;> first | exact absurd rfl hx | (cases subj <;> decide)

/-! ### Object agreement on the subject -/

/-- Object agreement on the subject is the object-agreement exponent of the person the subject's
    flag carries, with the object's number ((36)), realizing the [PART, v] remainder of the flag
    once *-ri* has realized its φ root (§3.3). -/
def oagrOnS (subj obj : Person) (n : Number) (pos : ObjectPosition) : Option String :=
  (flag strictlyDescending (goals subj obj pos)).bind fun
    | [o] => Kawapanan.Shawi.objectMarker o n
    | _ => none

/-- Object agreement appears on the subject only if the subject is ergative (§2, fn. 7), and, off
the diagonal, is overt only for a first-person subject and a second-person object (§3.3), since a
third-person object has no exponent and no other pair lets the subject Agree. -/
theorem oagrOnS_isSome {subj obj : Person} {n : Number} {pos : ObjectPosition}
    (hne : subj.prominence ≠ obj.prominence)
    (h : (oagrOnS subj obj n pos).isSome) :
    Ergative subj obj pos ∧ .speaker ∈ spec subj ∧ obj = .second := by
  cases pos <;> revert subj obj n <;> decide +kernel

/-- A first-person exclusive augmented subject with a second-person augmented object bears *-ri*
    and the object's marker (12), a second-person subject with a first-person object bears
    neither (11), and a third-person object leaves *-ri* nothing to accompany (23a). -/
theorem oagrOnS_examples :
    oagrOnS .firstExclusive .second .augmented .high = some "-((n)ke)ma'" ∧
    oagrOnS .second .firstExclusive .minimal .high = none ∧
    Ergative .firstExclusive .third .high ∧
    oagrOnS .firstExclusive .third .minimal .high = none := by
  decide

/-! ### Configurational rules (§1, §4.1) -/

/-- Rule (1) ([baker-2015]) values the higher of two caseless NPs in one domain ergative whatever
    their persons, as `DependentCase.assignCases` does; Shawi withholds ergative at 2→1, 3→1 and 3→2
    with the object in v's domain ((7a–c)). -/
theorem rule1_overgenerates :
    ((DependentCase.assignCases .ergative (fun _ : Fin 2 ↦ none) [0, 1]).valueOf 0).map (·.1) =
      some .erg ∧
    ¬ Ergative .second .first .high ∧ ¬ Ergative .third .first .high ∧
    ¬ Ergative .third .second .high := by
  decide

/-- No grammar of [deal-2024]'s probe space yields a 1>3>2 hierarchy (§4.1). None makes 3→2 a
second-goal configuration while 2→3 is not, since a third-person first goal neither satisfies
nor narrows the probe. Rule (37) of [barany-sheehan-2024]'s kind, whose hierarchy is
stipulated, has no such limit. -/
theorem no_1_3_2_hierarchy (g : Deal2024.Grammar) (h : DependentCase g [.second, .third]) :
    DependentCase g [.third, .second] := by
  revert g
  decide +kernel

/-! ### The typology of global case splits (§5) -/

/-- The probe sits on v, between object and subject, so the object is its first goal and the
    dependent case of the subject is ergative ((40)), or on T above both, so the subject is first
    and the dependent case of the object is accusative ((41)). -/
inductive Locus
  | v
  | T
  deriving DecidableEq, Repr

/-- The goals of a transitive clause in the order a probe at `l` meets them. -/
def Locus.goals : Locus → Person → Person → List Person
  | .v, subj, obj => [obj, subj]
  | .T, subj, obj => [subj, obj]

/-- Without a split (§5.1), an insatiable probe with no dynamic interaction Agrees with both
    arguments whatever their persons, giving ergative on v (Nez Perce [deal-2010], Amahuaca
    [clem-2019]) and accusative on T (Sakha, [baker-vinokurova-2010]). -/
theorem dependentCase_noPCC (l : Locus) (subj obj : Person) :
    DependentCase noPCC (l.goals subj obj) := by
  cases l <;> cases subj <;> cases obj <;> decide

/-- Under the strong PCC of Table 7 there is dependent case iff the first goal is third person,
    on the subject when the object is third (Shiwilu, [valenzuela-2011]) and on the object when
    the subject is third (Yurok). -/
theorem dependentCase_strong_iff (g₁ g₂ : Person) :
    DependentCase strong [g₁, g₂] ↔ .participant ∉ spec g₁ := by
  cases g₁ <;> cases g₂ <;> decide

/-- Shiwilu has no ergative at 1→2 and ergative at 3→3 ((45a), (46b)). -/
example : ¬ DependentCase strong (Locus.v.goals .first .second) ∧
    DependentCase strong (Locus.v.goals .third .third) := by decide

/-- Under the weak PCC of Table 7 there is dependent case unless the first goal is local and the
    second is third, so on the object except in local→third (Kolyma Yukaghir, [maslova-2003]). -/
theorem dependentCase_weak_iff (g₁ g₂ : Person) :
    DependentCase weak [g₁, g₂] ↔
      (.participant ∈ spec g₁ → .participant ∈ spec g₂) := by
  cases g₁ <;> cases g₂ <;> decide

/-- Under the strictly descending PCC of Table 7 there is dependent case iff the first goal lacks
    [SPKR] and the second bears [PART] whenever the first does. -/
theorem dependentCase_sd_iff (g₁ g₂ : Person) :
    DependentCase strictlyDescending [g₁, g₂] ↔
      .speaker ∉ spec g₁ ∧ (.participant ∈ spec g₁ → .participant ∈ spec g₂) := by
  cases g₁ <;> cases g₂ <;> decide

/-- Off the diagonal the strictly descending split is the hierarchy 1>2>3, dependent case holding
exactly when the second goal outranks the first, the subject over the object with the probe on v
(Shawi) and the object over the subject with it on T (Kashmiri, fn. 42). -/
theorem dependentCase_sd_off_diagonal_iff (g₁ g₂ : Person)
    (h : g₁.prominence ≠ g₂.prominence) :
    DependentCase strictlyDescending [g₁, g₂] ↔ g₂.prominence > g₁.prominence :=
  (dependentCase_iff_licit _ _ _).trans (sd_off_diagonal_iff_outranks ⟨g₂, g₁⟩ h.symm)

/-- In the Kolyma Yukaghir accusative ((52)), *-ul* realizes [φ, PART] in the object's flag and
    *-gele* its φ root, so the form records whether the subject T Agreed with first was a local
    person. -/
def kolymaYukaghirAccusative (subj obj : Person) : Option String :=
  (flag weak (Locus.T.goals subj obj)).bind fun
    | [s] => some (if .participant ∈ spec s then "-ul" else "-gele")
    | _ => none

/-- The accusative is *-gele* at 3→1 and *-ul* at 1→2, and there is none at 1→3 (49). -/
theorem kolymaYukaghirAccusative_49 :
    kolymaYukaghirAccusative .third .first = some "-gele" ∧
    kolymaYukaghirAccusative .first .second = some "-ul" ∧
    kolymaYukaghirAccusative .first .third = none := by
  decide

end ClemDeal2024
