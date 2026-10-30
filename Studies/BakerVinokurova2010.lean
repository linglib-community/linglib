module

public import Linglib.Syntax.Minimalist.Case.Dependent
public import Linglib.Syntax.Minimalist.Case.SyntacticObject
public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Data.Examples.BakerVinokurova2010
public import Linglib.Data.Examples.Readers

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
* `transitive`, `ditransitiveClause`, `causativeClause`, `passiveClause`, `possessedClause`,
  `derivedCases`: derivations of the constructions, and the cases the grammar reads off them.
* `subject`, `internal`, `possessor`, `pro`, `finite`: hand-placed NP positions and the finite
  probe, which the rows use.
* `Slot`, `candidates`: the NPs of a row's domain from the slots the rows name, highest first;
  the covert agent and object shift are the free choices where the paper leaves them free.
* `derive`, `Licensed`, `Agrees`, `Derivable`: assignment with the probes a row's morphology
  shows, the Case filter, the case–agreement link, and derivability under some choice.

## Implementation notes

* The phase heads are v, whose complement is the paper's VP phase (note 6), C, and a D with a
  complement. Object shift is Internal Merge to the specifier of v, where the paper adjoins the
  object to VP ((11b)); either way the object leaves the VP phase for the clause's.
* The paper assigns the dative on the VP cycle, before the theme shifts ((14), (30)). Here a
  phase sees an NP through any copy in what it transfers on its own, so the shifted theme's
  lower copy, `<letter>` in (30), keeps the VP-cycle configuration.
* The covert agent of a passive is a nominal in the specifier of passive v, PRO in (28b), which
  competes for case but bears none (pp. 609–610, note 30).

## TODO

* Agentive nominalizations ((34)–(37)), raising ((39)–(47)) and *promise* on derivations: the
  nominalizer's own phase, where (4b) also applies, and the edge of the embedded *dien* clause,
  whose T values the raised subject before the matrix clause re-marks it accusative.

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
  rules
    | .v => { high := some .dat }
    | .C => { low := some .acc }
    | _ => {}
  agreeCase
    | .T => some .nom
    | .D => some .gen
    | _ => none

/-- A purely configurational grammar has the dependent dative and accusative, elsewhere
    nominative in the clause and verb phrase and elsewhere genitive in the noun phrase, and no
    Agree. -/
def pureMarantz : CaseAssigners where
  rules
    | .D => { unmarked := some .gen }
    | .v => { high := some .dat, unmarked := some .nom }
    | .C => { low := some .acc, unmarked := some .nom }
    | _ => {}

/-- A purely Agree-based grammar values nominative from T, accusative from v and genitive from
    D, and has no dependent rule. -/
def pureChomsky : CaseAssigners where
  agreeCase
    | .T => some .nom
    | .v => some .acc
    | .D => some .gen
    | _ => none

/-- Sakha values nothing as unmarked: an NP no rule and no head reaches stays caseless. -/
theorem no_elsewhere_case {α : Type*} (np : α → PhasedNP) (probes : List (Cat × Cat))
    (order : List Cat) {xs : List α} {i : ℕ} {x : α} {c : Case} {m : Mechanism}
    (h : (grammar.assign np probes order xs)[i]? = some (x, some (c, m))) : m ≠ .unmarked := by
  rw [CaseAssigners.assign] at h
  refine mechanism_ne_unmarked_of_assignBy ?_ h
  intro c _
  cases c <;> rfl

/-- The Agree-based grammar values nothing dative: a dative NP brought it from the lexicon. -/
theorem pureChomsky_no_dative {α : Type*} (np : α → PhasedNP) (probes : List (Cat × Cat))
    (order : List Cat) {xs : List α} {i : ℕ} {x : α} {m : Mechanism} (hx : xs[i]? = some x)
    (h : (pureChomsky.assign np probes order xs)[i]? = some (x, some (.dat, m))) :
    (np x).lexicalCase = some .dat := by
  rw [CaseAssigners.assign] at h
  rcases hlex : (np x).lexicalCase with _ | c
  · rcases case_mem_of_assignBy (lex := fun x ↦ (np x).lexicalCase) (x := x) hlex
      h with ⟨_, -, hc⟩ | ⟨_, -, ⟨_, _⟩, hp, rfl⟩
    · simp [pureChomsky, Rules.cases] at hc
    · obtain ⟨⟨hd, d⟩, -, -, hk⟩ := pureChomsky.mem_probesIn np hp
      revert hk; cases hd <;> simp [pureChomsky]
  · rw [assignBy_getElem?_of_some (lex := fun x ↦ (np x).lexicalCase) hx hlex] at h
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h
    rw [h.1]

/-- The Agree-based grammar values an NP accusative only where a `v` probes: in a derivation
    without one, an accusative NP brought its case from the lexicon. -/
theorem pureChomsky_v_of_acc {α : Type*} (np : α → PhasedNP) (probes : List (Cat × Cat))
    (order : List Cat) {xs : List α} {i : ℕ} {x : α} {m : Mechanism}
    (hlex : (np x).lexicalCase = none)
    (h : (pureChomsky.assign np probes order xs)[i]? = some (x, some (.acc, m))) :
    ∃ d, (Cat.v, d) ∈ probes := by
  rw [CaseAssigners.assign] at h
  obtain rfl := mechanism_eq_agree_of_assignBy (rules := pureChomsky.rules)
    (fun _ _ ↦ rfl) (lex := fun x ↦ (np x).lexicalCase) (x := x) hlex h
  obtain ⟨_, -, ⟨_, _⟩, hp, rfl⟩ := exists_probe_of_assignBy h
  obtain ⟨⟨hd, d⟩, hmem, -, hk⟩ := pureChomsky.mem_probesIn np hp
  obtain rfl : hd = .v := by revert hk; cases hd <;> simp [pureChomsky]
  exact ⟨d, hmem⟩

/-! ### Case read off derivations

Each construction is a schematic head-final derivation. The phase heads are v, whose complement
is the paper's VP phase, C, and a D with a complement, and each phase sees the NPs with a copy in
what its complement transfers on its own. -/

/-- The phase heads: v, C, and a D that takes a complement. -/
def IsPhaseHead (a : LexicalItem.Token) : Prop :=
  a.item.cat = .v ∨ a.item.cat = .C ∨ a.item.cat = .D ∧ a.item.sel ≠ []

instance : DecidablePred IsPhaseHead := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Schematic heads: nominals, an intransitive, a transitive and a ditransitive verb, the
causative verb, active and passive v, T and C, the covert agent of a passive, and a D with a
possessor in its complement. -/
def subjD : LexicalItem.Token := ⟨.of .D [], 1⟩
@[inherit_doc subjD] def objD : LexicalItem.Token := ⟨.of .D [], 2⟩
@[inherit_doc subjD] def goalD : LexicalItem.Token := ⟨.of .D [], 3⟩
@[inherit_doc subjD] def verb : LexicalItem.Token := ⟨.of .V [.D], 4⟩
@[inherit_doc subjD] def verb₂ : LexicalItem.Token := ⟨.of .V [.D, .D], 5⟩
@[inherit_doc subjD] def littleV : LexicalItem.Token := ⟨.of .v [.V], 6⟩
@[inherit_doc subjD] def tense : LexicalItem.Token := ⟨.of .T [.v], 7⟩
@[inherit_doc subjD] def comp : LexicalItem.Token := ⟨.of .C [.T], 8⟩
@[inherit_doc subjD] def possD : LexicalItem.Token := ⟨.of .D [], 9⟩
@[inherit_doc subjD] def noun : LexicalItem.Token := ⟨.of .N [.D], 10⟩
@[inherit_doc subjD] def det : LexicalItem.Token := ⟨.of .D [.N], 11⟩
@[inherit_doc subjD] def causeeD : LexicalItem.Token := ⟨.of .D [], 12⟩
@[inherit_doc subjD] def causVerb : LexicalItem.Token := ⟨.of .V [.V, .D], 13⟩
@[inherit_doc subjD] def verb₀ : LexicalItem.Token := ⟨.of .V [], 14⟩
@[inherit_doc subjD] def passiveV : LexicalItem.Token := ⟨.of .v [.V], 15⟩
@[inherit_doc subjD] def proD : LexicalItem.Token := ⟨.of .D [], 16⟩

/-- A transitive clause, its object shifted to the edge of vP or not. -/
def transitive (shifted : Bool) : Derivation :=
  ⟨verb, [.em .left objD, .em .right littleV] ++ (if shifted then [.im objD .left] else []) ++
    [.em .left subjD, .em .right tense, .em .right comp]⟩

/-- A ditransitive clause, its theme shifted or not. -/
def ditransitiveClause (shifted : Bool) : Derivation :=
  ⟨verb₂, [.em .left objD, .em .left goalD, .em .right littleV] ++
    (if shifted then [.im objD .left] else []) ++
    [.em .left subjD, .em .right tense, .em .right comp]⟩

/-- The possessed noun phrase `[D [possessor N]]`. -/
def possessedNP : LinearizedSyntacticObject :=
  .merge (.leaf det) (.merge (.leaf possD) (.leaf noun))

/-- A transitive clause whose shifted object is a possessed noun phrase. -/
def possessedClause : Derivation :=
  ⟨verb, [.em .left possessedNP, .em .right littleV, .im possessedNP.toSyntacticObject .left,
    .em .left subjD, .em .right tense, .em .right comp]⟩

/-- A morphological causative, the causee merged in the verb phrase the causative heads above the
base verb's, transitive or not; the base verb's object shifts, or the causee of an intransitive
base. -/
def causativeClause (transitiveBase shifted : Bool) : Derivation :=
  if transitiveBase then
    ⟨verb, [.em .left objD, .em .right causVerb, .em .left causeeD, .em .right littleV] ++
      (if shifted then [.im objD .left] else []) ++
      [.em .left subjD, .em .right tense, .em .right comp]⟩
  else
    ⟨verb₀, [.em .right causVerb, .em .left causeeD, .em .right littleV] ++
      (if shifted then [.im causeeD .left] else []) ++
      [.em .left subjD, .em .right tense, .em .right comp]⟩

/-- A passive, its theme shifted to the edge of the voice phrase, with a goal or not, and a covert
agent in the specifier of passive v or not ((28), (30)). -/
def passiveClause (agent goal : Bool) : Derivation :=
  ⟨if goal then verb₂ else verb, [.em .left objD] ++ (if goal then [.em .left goalD] else []) ++
    [.em .right passiveV, .im objD .left] ++ (if agent then [.em .left proD] else []) ++
    [.em .right tense, .em .right comp]⟩

/-- The cases Sakha's grammar values on the nominals `xs` of a derivation. -/
def derivedCases (d : Derivation) (xs : List LexicalItem.Token) : Option (List (Option Case)) :=
  d.externalize?.map fun t ↦
    (grammar.assignOn .raising t (complementDomain .raising t ∅) IsPhaseHead (fun _ ↦ none)
      (· ≠ proD) xs).map (·.2.map (·.1))

/-! ### Positions -/

/-- A caseless NP merged in the clause. -/
def subject : PhasedNP := {}

/-- A caseless NP merged in the verb phrase, shifted to the clause edge or not. -/
def internal (shifted : Bool) : PhasedNP :=
  { phase := .v, shiftsTo := if shifted then some .C else none }

/-- A caseless NP inside a noun phrase. -/
def possessor : PhasedNP := { phase := .D }

/-- The covert agent, merged in the clause, competing for case without bearing it. -/
def pro : PhasedNP := { bearsCase := false }

/-- Finite T probing the clause. -/
def finite : List (Cat × Cat) := [(.T, .C)]

/-- The domains of hand-placed NPs, innermost first. -/
def domainOrder : List Cat := [.D, .v, .C]

/-- The cases of hand-placed NPs, positionally. -/
def cases (g : CaseAssigners) (probes : List (Cat × Cat)) (nps : List PhasedNP) :
    List (Option Case) :=
  (g.assign id probes domainOrder nps).map (·.2.map (·.1))

/-! ### The constructions -/

/-- In differential object marking a shifted object is accusative and an unshifted one
    caseless, the subject nominative from T either way ((10), (11)). -/
theorem dom (shifted : Bool) :
    derivedCases (transitive shifted) [subjD, objD] =
      some [some .nom, if shifted then some .acc else none] := by
  cases shifted <;> decide +kernel

/-- In a ditransitive the goal is dative on the verb-phrase cycle whether or not the theme
    shifts, and the theme accusative exactly when it does ((13), (14)). -/
theorem ditransitive (shifted : Bool) :
    derivedCases (ditransitiveClause shifted) [subjD, goalD, objD] =
      some [some .nom, some .dat, if shifted then some .acc else none] := by
  cases shifted <;> decide +kernel

/-- In a causative the causee of a transitive base is dative, c-commanding the theme in the
    verb phrase, and the causee of an intransitive base, alone there, is accusative once it
    shifts and never dative ((23), (24)). -/
theorem causative (shifted : Bool) :
    derivedCases (causativeClause true shifted) [subjD, causeeD, objD] =
      some [some .nom, some .dat, if shifted then some .acc else none] ∧
    derivedCases (causativeClause false shifted) [subjD, causeeD] =
      some [some .nom, if shifted then some .acc else none] := by
  cases shifted <;> decide +kernel

/-- In a passive the shifted theme is accusative exactly when a covert agent is present, and
    nominative from T otherwise; a goal is dative either way ((26)–(30)). The agent itself takes
    no case, and T, agreeing with nothing, agrees by default (note 30). -/
theorem passive :
    derivedCases (passiveClause true false) [proD, objD] = some [none, some .acc] ∧
    derivedCases (passiveClause false false) [objD] = some [some .nom] ∧
    derivedCases (passiveClause true true) [proD, goalD, objD] =
      some [none, some .dat, some .acc] ∧
    derivedCases (passiveClause false true) [goalD, objD] = some [some .dat, some .nom] := by
  decide +kernel

/-- A possessor is genitive from its D, and invisible to the clause. -/
theorem possessed :
    derivedCases possessedClause [subjD, possD, det] =
      some [some .nom, some .gen, some .acc] := by
  decide +kernel

/-- An agentive nominalization has no T, but its covert agent makes the shifted object
    accusative; without the agent the object is caseless. -/
theorem agentive_nominal :
    cases grammar [] [pro, internal true] = [none, some .acc] ∧
    cases grammar [] [internal true] = [none] := by
  decide

/-- A subject raised to the clause edge is accusative exactly when the matrix clause has
    another NP; into an impersonal clause it is valued by T alone. -/
theorem raising :
    cases grammar finite [subject, internal true] = [some .nom, some .acc] ∧
    cases grammar finite [internal true] = [some .nom] := by
  decide

/-- Under *promise* the goal is dative once the raised subject is below it in the verb phrase,
    and accusative when nothing is. -/
theorem promise :
    cases grammar finite [subject, internal false, internal true] =
      [some .nom, some .dat, some .acc] ∧
    cases grammar finite [subject, internal true] = [some .nom, some .acc] := by
  decide

theorem elsewhere_contrast :
    cases grammar finite [subject, internal false] = [some .nom, none] ∧
    cases grammar [] [subject] = [none] ∧
    cases pureMarantz finite [subject, internal false] = [some .nom, some .nom] ∧
    cases pureMarantz [] [subject] = [some .nom] := by
  decide

/-- The positions the rows are stated over are those the derivations give: on each construction
    the hand-placed NPs value what the derivation does. -/
theorem derivedCases_eq_cases :
    (∀ b, derivedCases (transitive b) [subjD, objD] =
      some (cases grammar finite [subject, internal b])) ∧
    (∀ b, derivedCases (ditransitiveClause b) [subjD, goalD, objD] =
      some (cases grammar finite [subject, internal false, internal b])) ∧
    (∀ b, derivedCases (causativeClause true b) [subjD, causeeD, objD] =
      some (cases grammar finite [subject, internal false, internal b])) ∧
    (∀ b, derivedCases (causativeClause false b) [subjD, causeeD] =
      some (cases grammar finite [subject, internal b])) ∧
    (∀ a g, derivedCases (passiveClause a g) ((if a then [proD] else []) ++
        (if g then [goalD] else []) ++ [objD]) =
      some (cases grammar finite ((if a then [pro] else []) ++
        (if g then [internal false] else []) ++ [internal true]))) ∧
    derivedCases possessedClause [subjD, possD, det] =
      some (cases grammar (finite ++ [(.D, .D)]) [subject, possessor, internal true]) := by
  decide +kernel

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
      { np := { phase := s.phase r, shiftsTo := if sh then some .C else none }, slot := some s,
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
  g.assign Occupant.np (probes r) domainOrder d

/-- The Case filter requires a caseless overt NP to be pseudo-incorporated, an unshifted
    VP-internal NP adjacent to the verb. -/
def Licensed (o : Occupant) (v : Option (Case × Mechanism)) : Prop :=
  o.covert = true ∨ v.isSome ∨ (o.np.phase = .v ∧ o.np.shiftsTo = none ∧ o.adjacent = true)

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

/-- Each of the paper's Sakha examples is acceptable exactly when some structure derives the
    cases it shows under the two-modality grammar with the Case filter and the
    case–agreement link. -/
theorem rows_case :
    ∀ r ∈ Examples.all, r.judgment = .acceptable ↔ Derivable grammar true r := by
  decide

/-- Without the Case filter and the case–agreement link, the configurational grammar derives
    a rejected example — a bare object separated from the verb, an unagreed-with subject of a
    participial clause, a passive whose verb agrees with nothing though its theme is
    nominative. -/
theorem pure_marantz_overgenerates :
    ∃ r ∈ Examples.all, r.judgment ≠ .acceptable ∧ Derivable pureMarantz false r := by
  decide

end BakerVinokurova2010
