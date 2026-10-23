module

public import Linglib.Syntax.Minimalist.Case.Dependent
public import Linglib.Data.Examples.BakerVinokurova2010

/-!
# Baker & Vinokurova 2010: two modalities of case assignment in Sakha

Sakha's four structural cases split in half. Accusative and dative are dependent cases: an NP
is valued accusative when a distinct caseless NP c-commands it in the clause, and dative when
it c-commands one in the verb phrase, where there is no accusative rule. Nominative and
genitive are assigned by T and D under agreement, and there is no elsewhere case: an NP that no
rule and no head reaches must be pseudo-incorporated into the verb — an unshifted VP-internal
NP adjacent to it — or the structure is out. Object shift makes differential object marking a
phase effect; the causee of a causative is dative exactly when the base verb is transitive; a
passive theme is accusative exactly when a covert agent is present; the object of an agentive
nominalization is accusative though no v is present; a subject raised into an impersonal clause
stays unmarked; and a finite verb agrees with an NP exactly when it values that NP nominative.
A purely configurational grammar with elsewhere cases overgenerates the Case-filter and
agreement violations, and a purely Agree-based grammar never values a dative, and an accusative
only where a `v` probes.

## Main definitions

* `grammar`: the two-modality grammar of Sakha.
* `pureMarantz`, `pureChomsky`: the two pure grammars beside it.
* `subject`, `internal`, `possessor`, `pro`, `finite`: the NP positions and the finite probe
  the paper's derivations use.
* `Slot`, `candidates`: the NPs of a row's domain from the slots the rows name, highest first;
  the covert agent and object shift are the free choices where the paper leaves them free.
* `derive`, `Licensed`, `Agrees`, `Derivable`: assignment with the probes a row's morphology
  shows, the Case filter, the case–agreement link, and derivability under some choice.

## Main results

* `dom`, `ditransitive`, `causative`, `passive`, `agentive_nominal`, `raising`, `promise`,
  `possessed`: the paper's constructions.
* `no_elsewhere_case`, `pureChomsky_no_dative`, `pureChomsky_v_of_acc`: Sakha values nothing as
  unmarked, and an Agree-only grammar values nothing dative and an accusative only where a `v`
  probes, whatever the domain.
* `rows_case`: acceptability is derivability under the two-modality grammar.
* `pure_marantz_overgenerates`: without the Case filter and the agreement link, the
  configurational grammar derives rejected examples.

## References

* [baker-vinokurova-2010]
* [marantz-1991] — dependent case
* [chomsky-2000], [chomsky-2001] — case under Agree and phases
* [diesing-1992] — object shift of specific objects
* [vinokurova-2005] — the source of much of the data
-/

@[expose] public section

namespace BakerVinokurova2010

open Minimalist Case DependentCase

/-! ### The grammars -/

/-- The Sakha grammar of structural case values dative on the higher of two NPs in the verb
    phrase, accusative on the lower of two in the clause, and nominative from T and genitive
    from D under Agree, with no elsewhere case in any domain. -/
def grammar : CaseAssigners where
  domains := [(.D, {}), (.v, { high := some .dat }), (.C, { low := some .acc })]
  agree := [(.T, .nom), (.D, .gen)]

/-- A purely configurational grammar has the dependent dative and accusative, elsewhere
    nominative in the clause and verb phrase and elsewhere genitive in the noun phrase, and no
    Agree. -/
def pureMarantz : CaseAssigners where
  domains := [(.D, { unmarked := some .gen }), (.v, { high := some .dat, unmarked := some .nom }),
    (.C, { low := some .acc, unmarked := some .nom })]

/-- A purely Agree-based grammar values nominative from T, accusative from v and genitive from
    D, and has no dependent rule. -/
def pureChomsky : CaseAssigners where
  domains := [(.D, {}), (.v, {}), (.C, {})]
  agree := [(.T, .nom), (.v, .acc), (.D, .gen)]

theorem no_elsewhere_case {α : Type*} (np : α → PhasedNP) (probes : List (Cat × Cat))
    {xs : List α} {i : ℕ} {x : α} {c : Case} {m : Mechanism}
    (h : (grammar.assign np probes xs)[i]? = some (x, some (c, m))) : m ≠ .unmarked :=
  CaseAssigners.mechanism_ne_unmarked (by decide) h

theorem pureChomsky_no_dative {α : Type*} (np : α → PhasedNP) (probes : List (Cat × Cat))
    {xs : List α} {i : ℕ} {x : α} {m : Mechanism} (hx : xs[i]? = some x)
    (h : (pureChomsky.assign np probes xs)[i]? = some (x, some (.dat, m))) :
    (np x).lexicalCase = some .dat := by
  rcases hlex : (np x).lexicalCase with _ | c
  · exact absurd (CaseAssigners.case_mem_cases hlex h) (by decide)
  · have := CaseAssigners.assign_getElem?_of_some (g := pureChomsky) (probes := probes) hx hlex
    rw [this] at h
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h
    rw [h.1]

theorem pureChomsky_v_of_acc {α : Type*} (np : α → PhasedNP) (probes : List (Cat × Cat))
    {xs : List α} {i : ℕ} {x : α} {m : Mechanism} (hlex : (np x).lexicalCase = none)
    (h : (pureChomsky.assign np probes xs)[i]? = some (x, some (.acc, m))) :
    ∃ d, (Cat.v, d) ∈ probes := by
  obtain rfl := CaseAssigners.mechanism_eq_agree (by decide) hlex h
  obtain ⟨⟨hd, d⟩, hmem, hh⟩ := CaseAssigners.exists_probe_of_agree h
  obtain rfl : hd = .v := by
    change pureChomsky.agreeCase hd = some .acc at hh
    revert hh; cases hd <;> decide
  exact ⟨d, hmem⟩

/-! ### Positions -/

/-- A caseless NP merged in the clause. -/
def subject : PhasedNP := {}

/-- A caseless NP merged in the verb phrase, shifted to the clause edge or not. -/
def internal (shifted : Bool) : PhasedNP := { phase := .v, shifted }

/-- A caseless NP inside a noun phrase. -/
def possessor : PhasedNP := { phase := .D }

/-- The covert agent, merged in the clause. -/
def pro : PhasedNP := {}

/-- Finite T probing the clause. -/
def finite : List (Cat × Cat) := [(.T, .C)]

/-- The cases of a derivation, positionally. -/
def cases (g : CaseAssigners) (probes : List (Cat × Cat)) (nps : List PhasedNP) :
    List (Option Case) :=
  (g.assign id probes nps).map (·.2.map (·.1))

/-! ### The constructions -/

attribute [local simp] cases CaseAssigners.assign domainPass probePass
  Rules.dependentPass Rules.unmarkedPass Valuation.unvalued Valuation.fill Valuation.fillFrom
  lexicalValuation Valuation.initial CaseAssigners.derive CaseAssigners.rules
  CaseAssigners.agreeCase grammar pureMarantz PhasedNP.visible PhasedNP.spellOut subject internal
  possessor pro finite


theorem dom (shifted : Bool) :
    cases grammar finite [subject, internal shifted] =
      [some .nom, if shifted then some .acc else none] := by
  cases shifted <;> simp

theorem ditransitive (shifted : Bool) :
    cases grammar finite [subject, internal false, internal shifted] =
      [some .nom, some .dat, if shifted then some .acc else none] := by
  cases shifted <;> simp

theorem causative (shifted : Bool) :
    cases grammar finite [subject, internal false, internal shifted] =
      [some .nom, some .dat, if shifted then some .acc else none] ∧
    cases grammar finite [subject, internal shifted] =
      [some .nom, if shifted then some .acc else none] :=
  ⟨ditransitive shifted, dom shifted⟩

theorem passive :
    cases grammar finite [pro, internal true] = [some .nom, some .acc] ∧
    cases grammar finite [internal true] = [some .nom] ∧
    cases grammar finite [pro, internal false, internal true] =
      [some .nom, some .dat, some .acc] ∧
    cases grammar finite [internal false, internal true] = [some .dat, some .nom] := by
  simp

theorem agentive_nominal :
    cases grammar [] [pro, internal true] = [none, some .acc] ∧
    cases grammar [] [internal true] = [none] := by
  simp

/-- A subject raised to the clause edge is accusative exactly when the matrix clause has
    another NP; into an impersonal clause it is valued by T alone. -/
theorem raising :
    cases grammar finite [subject, internal true] = [some .nom, some .acc] ∧
    cases grammar finite [internal true] = [some .nom] := by
  simp

theorem promise :
    cases grammar finite [subject, internal false, internal true] =
      [some .nom, some .dat, some .acc] ∧
    cases grammar finite [subject, internal true] = [some .nom, some .acc] := by
  simp

theorem possessed :
    cases grammar (finite ++ [(.D, .D)]) [subject, possessor, internal true] =
      [some .nom, some .gen, some .acc] := by
  simp

theorem elsewhere_contrast :
    cases grammar finite [subject, internal false] = [some .nom, none] ∧
    cases grammar [] [subject] = [none] ∧
    cases pureMarantz finite [subject, internal false] = [some .nom, some .nom] ∧
    cases pureMarantz [] [subject] = [some .nom] := by
  simp

/-! ### The rows -/

/-- The NP slots the rows name, in c-command order. -/
inductive Slot
  | subject
  | causee
  | goal
  | raised
  | object
  | pObject
  | possessor
  deriving DecidableEq, Repr

/-- The prefix of a slot's feature keys. -/
def Slot.key : Slot → String
  | .subject => "subject"
  | .causee => "causee"
  | .goal => "goal"
  | .raised => "raised"
  | .object => "object"
  | .pObject => "pObject"
  | .possessor => "possessor"

/-- The slots highest first. -/
def Slot.all : List Slot :=
  [.subject, .causee, .goal, .raised, .object, .pObject, .possessor]

/-- The case a gloss shows, or nothing for a bare NP. -/
def parseCase? : String → Option (Option Case)
  | "NOM" => some (some .nom)
  | "bare" => some none
  | "ACC" => some (some .acc)
  | "DAT" => some (some .dat)
  | "GEN" => some (some .gen)
  | _ => none

/-- A valuation realizes a gloss: the case it shows, or, for a bare NP, no case or the
    nominative, which is unmarked. -/
def Realizes (v : Option (Case × Mechanism)) : Option Case → Prop
  | some c => v.map (·.1) = some c
  | none => v.map (·.1) = none ∨ v.map (·.1) = some .nom

instance (v : Option (Case × Mechanism)) (o : Option Case) : Decidable (Realizes v o) := by
  cases o <;> simp only [Realizes] <;> infer_instance

/-- A row states a yes/no property. -/
def yes (r : Datum) (k : String) : Bool := r.feature? k = some "yes"

/-- An NP of a row's domain has its position, whether it is covert, whether it is adjacent to
    the verb, and the case its gloss shows. -/
structure Occupant where
  np : PhasedNP
  slot : Option Slot := none
  covert : Bool := false
  adjacent : Bool := false
  observed : Option Case := none
  deriving DecidableEq, Repr

/-- A possessor is merged in the noun phrase, the objects, goal, causee and raised subject in
    the verb phrase, and the subject in the clause unless the predicate is unaccusative or takes
    a dative subject. -/
def Slot.phase (r : Datum) : Slot → Cat
  | .subject =>
    if yes r "unaccusative" || r.feature? "subjectPosition" = some "internal" then .v else .C
  | .causee | .goal | .raised | .object => .v
  | .pObject => .C
  | .possessor => .D

/-- A VP-merged NP shifts to the clause edge if it is specific and not if it is nonspecific, a
    raised subject always shifts, and the paper leaves the rest free. -/
def Slot.shifts (r : Datum) (s : Slot) : List Bool :=
  match s.phase r with
  | .v =>
    if s = .raised then [true]
    else match r.feature? (s.key ++ "Specific") with
      | some "yes" => [true]
      | some "no" => [false]
      | _ => [false, true]
  | _ => [false]

/-- The occupants a stated slot contributes, one per shift option. -/
def Slot.occupants (r : Datum) (s : Slot) : Option (List Occupant) :=
  ((r.feature? (s.key ++ "Case")).bind parseCase?).map fun c ↦
    (s.shifts r).map fun sh ↦
      { np := { phase := s.phase r, shifted := sh }, slot := some s,
        adjacent := yes r (s.key ++ "Adjacent"), observed := c }

/-- The covert agent is forced in a passive with an agent-oriented adverb and in an agentive
    nominalization, excluded when the subject is overt or the predicate unaccusative, and
    otherwise free in a passive or event nominalization. -/
def agentOptions (r : Datum) : List (List Occupant) :=
  if (r.feature? "subjectCase").isSome || yes r "unaccusative" then [[]]
  else if yes r "agentOrientedAdverb" || r.feature? "construction" = some "agentiveNominal" then
    [[{ np := pro, covert := true }]]
  else match r.feature? "construction" with
    | some "passive" | some "eventNominal" => [[{ np := pro, covert := true }], []]
    | _ => [[]]

/-- The domains a row may have are the covert agent, then each stated slot under each of its
    shift options. -/
def candidates (r : Datum) : List (List Occupant) :=
  (Slot.all.foldr (fun s acc ↦ match s.occupants r with
      | none => acc
      | some vs => vs.flatMap fun o ↦ acc.map (o :: ·)) [[]]).flatMap fun d ↦
    (agentOptions r).map (· ++ d)

/-- The probes a row's morphology shows are finite T where the verb agrees, the head noun's D
    reaching into the clause where it agrees with the subject, and the possessed noun's D
    where it agrees with its possessor. -/
def probes (r : Datum) : List (Cat × Cat) :=
  (if yes r "verbAgreement" then [(Cat.T, Cat.C)] else []) ++
    (if yes r "headNounAgreement" then [(Cat.D, Cat.C)] else []) ++
    (if yes r "possesseeAgreement" then [(Cat.D, Cat.D)] else [])

/-- The valuations of a domain's occupants. -/
def derive (g : CaseAssigners) (r : Datum) (d : List Occupant) :
    Valuation Occupant (Case × Mechanism) :=
  g.assign Occupant.np (probes r) d

/-- The Case filter requires a caseless overt NP to be pseudo-incorporated, an unshifted
    VP-internal NP adjacent to the verb. -/
def Licensed (o : Occupant) (v : Option (Case × Mechanism)) : Prop :=
  o.covert = true ∨ v.isSome ∨ (o.np.phase = .v ∧ o.np.shifted = false ∧ o.adjacent = true)

instance (o : Occupant) (v : Option (Case × Mechanism)) : Decidable (Licensed o v) := by
  unfold Licensed; infer_instance

/-- T agrees with the NP it values nominative: where a row states the verb's agreement
    target, an overt NP is nominative by Agree exactly when it is that target, so default
    agreement means no NP is. -/
def Agrees (r : Datum) (out : Valuation Occupant (Case × Mechanism)) : Prop :=
  (r.feature? "agreesWith").isSome → ∀ p ∈ out, p.1.covert = false →
    (p.2 = some (.nom, .agree) ↔ r.feature? "agreesWith" = p.1.slot.map Slot.key)

instance (r : Datum) (out : Valuation Occupant (Case × Mechanism)) :
    Decidable (Agrees r out) := by
  unfold Agrees; infer_instance

/-- A domain derives the row under a grammar: every overt NP gets the case its gloss shows,
    and under the Chomskian half — the Case filter and the case–agreement link — is licensed
    and agreed with accordingly. -/
def Derives (g : CaseAssigners) (chomskian : Bool) (r : Datum) (d : List Occupant) :
    Prop :=
  (∀ p ∈ derive g r d, p.1.covert = false →
    Realizes p.2 p.1.observed ∧ (chomskian = true → Licensed p.1 p.2)) ∧
  (chomskian = true → Agrees r (derive g r d))

instance (g : CaseAssigners) (chomskian : Bool) (r : Datum) (d : List Occupant) :
    Decidable (Derives g chomskian r d) := by
  unfold Derives; infer_instance

/-- Some choice of structure derives the row. -/
def Derivable (g : CaseAssigners) (chomskian : Bool) (r : Datum) : Prop :=
  ∃ d ∈ candidates r, Derives g chomskian r d

instance (g : CaseAssigners) (chomskian : Bool) (r : Datum) :
    Decidable (Derivable g chomskian r) := by
  unfold Derivable; infer_instance

theorem rows_case :
    ∀ r ∈ Examples.all, r.judgment = .acceptable ↔ Derivable grammar true r := by
  decide

theorem pure_marantz_overgenerates :
    ∃ r ∈ Examples.all, r.judgment ≠ .acceptable ∧ Derivable pureMarantz false r := by
  decide

end BakerVinokurova2010
