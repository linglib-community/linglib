module

public import Linglib.Data.Examples.ErlewineSommerlot2025
public import Linglib.Syntax.Minimalist.Linearization.SpelloutDomain
public import Linglib.Syntax.Minimalist.Label.RaisingHead

/-!
# Erlewine and Sommerlot (2025): Voice and Extraction in Malayic

This file formalizes the account of voice and Ā-extraction in Malayic in
[erlewine-sommerlot-2025]. The verbal domain has two heads, after Nomoto: v, which introduces the
agent and licenses one nominal, and Voice, which heads a phase with exactly one nominal specifier.
Every nominal is licensed by v or by T, so the nominal that v leaves unlicensed moves through
Spec,VoiceP to the subject position. Each clause's Minimalist derivation is built from its
parameters, and its VoiceP and CP Spell-outs, read off the derivation as Fox and Pesetsky's cyclic
linearization reads them, are the paper's snapshots. Vocabulary items realize Voice and v by their
adjacency at VoiceP Spell-out, a null Voice is pruned from the ordering statements, and a clause
is grammatical when it is licensed, meets the EPP and the vocabulary, affixes an overt Voice to
the verb, and linearizes.

The subject-only restriction on Ā-extraction follows, and so does its exception: a nominal other
than the agent can be extracted while the agent raises or stays low only when Voice is null, since
an overt Voice is ordered before the agent at VoiceP and after it at CP (57); the agent of a bare
passive cannot be extracted across its theme (60); *N-* on v rather than Voice allows object
extraction (§5.2); and the registers of Madurese differ in whether Voice has a null allomorph
(§5.3). The six grammars predict the judgments of the paper's examples.

## Main statements

* `ErlewineSommerlot2025.Clause.spellouts_eq`: the derivations spell out the paper's VoiceP and
  CP snapshots.
* `ErlewineSommerlot2025.Clause.schedule_eq`: the phases of Voice and C are complete when VoiceP
  is built and at the end.
* `ErlewineSommerlot2025.rows_grammatical`: the grammars predict every example's judgment.
* `ErlewineSommerlot2025.overt_voice_paradox`: an overt Voice blocks the order-preserving
  extraction of two nominals (57).

## Implementation notes

* A clause is its syntactic parameters, and the exponents of Voice and v are chosen after VoiceP
  Spell-out. Each phase, of Voice or C, is spelled out when the next head projects over it
  (`Minimalist.Derivation.phaseSchedule`). v+V is one terminal of category v, the paper not
  showing V-to-v movement, and one terminal stands for T with its auxiliaries.
* The active v always projects its agent (30). The ban on an agent licensed by the passive v
  moving to Spec,VoiceP is the antilocality the paper tentatively suggests (§3.3).
* Desa's T licenses a nominal in situ instead of attracting one under nominal Ā-extraction (§3.3).
  Kuching Malay's Voice is always null, and Jakarta Indonesian's *di-* passive is taken from
  Standard Indonesian (§5.2).
* Ditransitive, possessor and embedded-argument extraction (§4.4), ellipsis (§4.5) and the
  Kendayan passives (§5.2) are not modelled.

## References

* [erlewine-sommerlot-2025]
* [nomoto-2015]
* [nomoto-2021]
* [fox-pesetsky-2005]
* [embick-noyer-2001]
* [jeoung-2017]
-/

@[expose] public section

namespace ErlewineSommerlot2025

open Minimalist Linearization ErlewineSommerlot2025.Examples
open scoped List

/-- The two flavours of v (§3.1). -/
inductive VFlavor
  | act
  | pass
  deriving DecidableEq, Repr, Fintype

/-- A bivalent verb's nominal arguments are its agent and its theme. -/
inductive Nominal
  | agent
  | theme
  deriving DecidableEq, Repr, Fintype

/-- C attracts a nominal or a PP to Spec,CP. -/
inductive Extracted
  | nominal (n : Nominal)
  | pp
  deriving DecidableEq, Repr, Fintype

/-- Voice and v are realized as *me-*, *N-*, *di-* or *e-* across the languages. -/
inductive Exponent
  | me
  | n
  | di
  | e
  deriving DecidableEq, Repr, Fintype

/-- A Spell-out orders nominals, the nonnominal specifier, Voice, the complex head v+V, and T with
its auxiliaries. -/
inductive Term
  | dp (n : Nominal)
  | pp
  | voice
  | verb
  | aux
  deriving DecidableEq, Repr, Fintype

/-- Each terminal spells out its own lexical item, v+V that of the light verb it projects, which
selects the theme; Voice selects vP and T selects VoiceP. -/
def Term.token : Term → LexicalItem.Token
  | .dp .agent => ⟨.of .D [], 1⟩
  | .dp .theme => ⟨.of .D [], 2⟩
  | .pp => ⟨.of .P [], 3⟩
  | .voice => ⟨.of .Voice [.v], 4⟩
  | .verb => ⟨.of .v [.D], 5⟩
  | .aux => ⟨.of .T [.Voice], 6⟩

/-- A lexical item spells out at most one terminal. -/
def Term.ofToken? (tok : LexicalItem.Token) : Option Term :=
  [Term.dp .agent, .dp .theme, .pp, .voice, .verb, .aux].find? (·.token = tok)

/-- The complementizer that attracts the Ā-extracted phrase is silent. -/
def C₀ : LexicalItem.Token := ⟨.of .C [.T], 7⟩

/-- Voice and C head phases. -/
def IsPhaseHead (a : LexicalItem.Token) : Prop := a = Term.voice.token ∨ a = C₀

instance : DecidablePred IsPhaseHead := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- An extracted phrase is a nominal or the PP. -/
def Extracted.term : Extracted → Term
  | .nominal n => .dp n
  | .pp => .pp

/-- A bivalent clause is fixed by the flavour of v, whether v projects the agent, the nominal moved
to Spec,VoiceP, the nominal T attracts to Spec,TP if any, and what C attracts if anything. -/
structure Clause where
  flavor : VFlavor
  agentProjected : Bool
  spec : Nominal
  subject : Option Nominal
  extracted : Option Extracted
  deriving DecidableEq, Repr, Fintype

namespace Clause

variable (c : Clause)

/-! ### The derivation and its Spell-outs -/

/-- VoiceP is built from the theme: v+V merges, then the PP that will be extracted, the agent in
Spec,vP, and Voice; the nominal specifier raises, and the PP raises above it (30), (42). -/
def voicePSteps : List Step :=
  [.em .left Term.verb.token] ++
    (if c.extracted = some .pp then [.em .right Term.pp.token] else [] : List Step) ++
    (if c.agentProjected then [.em .left (Term.dp .agent).token] else [] : List Step) ++
    ([.em .left Term.voice.token, .im (Term.dp c.spec).token] : List Step) ++
    (if c.extracted = some .pp then [.im Term.pp.token] else [] : List Step)

/-- Above VoiceP, T with its auxiliaries merges and attracts the subject, and C merges and
attracts the extracted phrase. -/
def cpSteps : List Step :=
  [.em .left Term.aux.token] ++
    (c.subject.map fun s ↦ Step.im (Term.dp s).token).toList ++
    [.em .left C₀] ++ (c.extracted.map fun x ↦ Step.im x.term.token).toList

/-- A clause's derivation starts from the theme. -/
def derivation : Derivation := ⟨(Term.dp .theme).token, c.voicePSteps ++ c.cpSteps⟩

/-- Each phase is spelled out when it is complete. -/
def schedule : List (ℕ × ℕ) := c.derivation.phaseSchedule .raising IsPhaseHead

/-- The derivation's Spell-outs read as terminals, before vocabulary insertion. -/
def spellouts : List (List Term) :=
  c.schedule.map fun p ↦ (c.derivation.spellout p.1 p.2).filterMap Term.ofToken?

/-- The clause projects the theme, and the agent when v projects it. -/
def nominals : List Nominal := if c.agentProjected then [.agent, .theme] else [.theme]

/-- The agent stays in Spec,vP at VoiceP Spell-out when it is projected and not the nominal
specifier. -/
def AgentInSitu : Prop := c.agentProjected = true ∧ c.spec ≠ .agent

instance : Decidable c.AgentInSitu := inferInstanceAs (Decidable (_ ∧ _))

/-- At VoiceP Spell-out (55a) the PP precedes the nominal specifier, then Voice, the agent if it
stays in Spec,vP, v+V, and the theme if it stays in situ. -/
def voiceP : List Term :=
  (if c.extracted = some .pp then [.pp] else [] : List Term) ++
    ([.dp c.spec, .voice] : List Term) ++
    (if c.AgentInSitu then [.dp .agent] else [] : List Term) ++ ([.verb] : List Term) ++
    (if c.spec = .theme then [] else [.dp .theme] : List Term)

/-- By CP Spell-out the extracted phrase and the subject have left VoiceP, in that order. -/
def moved : List Term :=
  ((c.extracted.map Extracted.term).toList ++ (c.subject.map Term.dp).toList).dedup

/-- At CP Spell-out (56b) the moved phrases precede the auxiliaries and the rest of VoiceP. -/
def cP : List Term := c.moved ++ [.aux] ++ c.voiceP.filter (· ∉ c.moved)

/-- The clause's word order is its CP Spell-out with Voice affixed to the verb. -/
def surface : List Term := c.cP.filter (· ≠ .voice)

/-- Voice and v are linearly adjacent at VoiceP Spell-out. -/
def Adjacent : Prop := [Term.voice, .verb] <:+: c.voiceP

instance : Decidable c.Adjacent := List.decidableInfix _ _

/-- v licenses a nominal inside VoiceP: the active v the theme it c-commands, the passive v the
agent in its specifier (§3.1). -/
def LicensedByV : Nominal → Prop
  | .theme => c.flavor = .act
  | .agent => c.flavor = .pass ∧ c.agentProjected = true

instance (n : Nominal) : Decidable (c.LicensedByV n) := by
  cases n <;> unfold LicensedByV <;> infer_instance

/-- The Ā-extracted nominal, if any. -/
def aBar : Option Nominal :=
  match c.extracted with
  | some (.nominal n) => some n
  | _ => none

/-- A clause is well formed when the active v projects its agent (30), the specifier, the subject
and the extracted nominal are projected, and no agent licensed by the passive v moves to
Spec,VoiceP (§3.3). -/
def WellFormed : Prop :=
  (c.flavor = .act → c.agentProjected = true) ∧ c.spec ∈ c.nominals ∧
    (∀ s ∈ c.subject, s ∈ c.nominals) ∧ (∀ n ∈ c.aBar, n ∈ c.nominals) ∧
    ¬ (c.flavor = .pass ∧ c.spec = .agent)

instance : Decidable c.WellFormed := by unfold WellFormed; infer_instance

/-- Every well-formed clause's derivation spells out the paper's VoiceP and CP snapshots. -/
theorem spellouts_eq : ∀ c : Clause, c.WellFormed → c.spellouts = [c.voiceP, c.cP] := by
  decide +kernel

/-- The phase of Voice is complete when VoiceP is built, and that of C at the end. -/
theorem schedule_eq : ∀ c : Clause, c.WellFormed → c.schedule =
    [(c.voicePSteps.length, c.voicePSteps.length), (c.derivation.length, c.derivation.length)] := by
  decide +kernel

theorem adjacent_iff : ∀ c : Clause, c.Adjacent ↔ ¬ c.AgentInSitu := by
  decide +kernel

theorem nodup_cP : ∀ c : Clause, c.cP.Nodup := by
  decide +kernel

theorem voiceP_subset_cP : ∀ c : Clause, c.voiceP ⊆ c.cP := by
  decide +kernel

end Clause

/-! ### Exponence -/

/-- The exponents chosen for Voice and v at VoiceP Spell-out. -/
structure Exponence where
  voice : Option Exponent
  v : Option Exponent
  deriving DecidableEq, Repr

/-- The verb's prefix is the overt exponents, Voice's before v's. -/
def Exponence.affix (e : Exponence) : List Exponent := e.voice.toList ++ e.v.toList

/-- A null Voice is pruned from the ordering statements (l.1351–1354). -/
def Exponence.prune (e : Exponence) (l : List Term) : List Term :=
  if e.voice.isSome then l else l.filter (· ≠ .voice)

/-- The ordering statements of a clause under an exponence. -/
def Clause.phases (c : Clause) (e : Exponence) : List (List Term) :=
  [e.prune c.voiceP, e.prune c.cP]

theorem Clause.consistent_phases_iff (c : Clause) (e : Exponence) :
    Consistent (c.phases e) ↔ e.prune c.voiceP <+ e.prune c.cP := by
  unfold Clause.phases Exponence.prune
  split
  · exact consistent_pair_iff_sublist (c.nodup_cP) (c.voiceP_subset_cP)
  · exact consistent_pair_iff_sublist (c.nodup_cP.filter _)
      fun x hx ↦ List.mem_filter.2 ⟨c.voiceP_subset_cP (List.mem_filter.1 hx).1,
        (List.mem_filter.1 hx).2⟩

/-- An overt Voice prefixes to v+V by local dislocation, which needs adjacency (§3.1). -/
def LocalDislocation (c : Clause) (e : Exponence) : Prop := e.voice.isSome → c.Adjacent

instance (c : Clause) (e : Exponence) : Decidable (LocalDislocation c e) :=
  inferInstanceAs (Decidable (_ → _))

/-! ### Grammars -/

/-- A language's vocabulary items (§3.1, §4.1, §5) give the exponents Voice may take, by the
flavour of v and whether the two heads are adjacent, likewise for v, and whether T licenses a
nominal in situ under nominal Ā-extraction instead of attracting one. -/
structure Grammar where
  voice : VFlavor → Bool → List (Option Exponent)
  v : VFlavor → Bool → List (Option Exponent)
  inSitu : Bool

/-- In Desa (32) *me-* is optional before the active v, *di-* appears before the passive v and
Voice is null elsewhere, the active v is *N-*, and T licenses in situ under Ā-extraction. -/
def desa : Grammar where
  voice
    | .act, true => [some .me, none]
    | .pass, true => [some .di]
    | _, false => [none]
  v
    | .act, _ => [some .n]
    | .pass, _ => [none]
  inSitu := true

/-- In Standard Indonesian and Malay (49) *me-* and *N-* each appear only next to the other. -/
def standard : Grammar where
  voice
    | .act, true => [some .me]
    | .pass, true => [some .di]
    | _, false => [none]
  v
    | .act, true => [some .n]
    | _, _ => [none]
  inSitu := false

/-- In Jakarta Indonesian (§5.2) the optional *N-* realizes Voice. -/
def jakarta : Grammar where
  voice
    | .act, true => [some .n, none]
    | .pass, true => [some .di]
    | _, false => [none]
  v _ _ := [none]
  inSitu := false

/-- In Kuching Malay (§5.2) the optional *N-* realizes v and Voice is always null. -/
def kuching : Grammar where
  voice _ _ := [none]
  v
    | .act, _ => [some .n, none]
    | .pass, _ => [none]
  inSitu := false

/-- In polite Madurese (82) Voice is *N-* or *e-* next to v and null elsewhere. -/
def politeMadurese : Grammar where
  voice
    | .act, true => [some .n]
    | .pass, true => [some .e]
    | _, false => [none]
  v _ _ := [none]
  inSitu := false

/-- In familiar Madurese (83) Voice is *N-* or *e-* by the flavour of v alone, with no null
allomorph. -/
def familiarMadurese : Grammar where
  voice
    | .act, _ => [some .n]
    | .pass, _ => [some .e]
  v _ _ := [none]
  inSitu := false

namespace Grammar

variable (g : Grammar) (c : Clause) (e : Exponence)

/-- T licenses the nominal it attracts, or, where the EPP is relaxed under Ā-extraction, the one
nominal it c-commands that v leaves unlicensed. -/
def TLicenses (n : Nominal) : Prop :=
  match c.subject with
  | some s => n = s
  | none => g.inSitu = true ∧ c.aBar.isSome = true ∧ ¬ c.LicensedByV n

instance (n : Nominal) : Decidable (g.TLicenses c n) := by
  unfold TLicenses; split <;> infer_instance

/-- Every nominal is licensed, by v or by T (§3.1). -/
def Licensed : Prop := ∀ n ∈ c.nominals, c.LicensedByV n ∨ g.TLicenses c n

/-- T attracts a nominal, unless the language licenses in situ under nominal Ā-extraction, when
it attracts none. -/
def EPP : Prop :=
  if g.inSitu && c.aBar.isSome then c.subject = none else c.subject.isSome = true

/-- The exponents are those the vocabulary items allow, given the adjacency of Voice and v at
VoiceP Spell-out. -/
def Vocabulary : Prop :=
  e.voice ∈ g.voice c.flavor (decide c.Adjacent) ∧ e.v ∈ g.v c.flavor (decide c.Adjacent)

/-- A clause under an exponence is grammatical when it is well formed, licenses every nominal,
meets the EPP and the vocabulary, affixes an overt Voice, and linearizes. -/
def Grammatical : Prop :=
  c.WellFormed ∧ g.Licensed c ∧ g.EPP c ∧ g.Vocabulary c e ∧ LocalDislocation c e ∧
    Consistent (c.phases e)

instance : Decidable (g.Licensed c) := by unfold Licensed; infer_instance
instance : Decidable (g.EPP c) := by unfold EPP; infer_instance
instance : Decidable (g.Vocabulary c e) := by unfold Vocabulary; infer_instance
instance : Decidable (g.Grammatical c e) :=
  decidable_of_iff (c.WellFormed ∧ g.Licensed c ∧ g.EPP c ∧ g.Vocabulary c e ∧
    LocalDislocation c e ∧ e.prune c.voiceP <+ e.prune c.cP) <| by
    rw [Grammatical, Clause.consistent_phases_iff]

/-- The exponences the vocabulary items allow a clause. -/
def exponences : List Exponence :=
  (g.voice c.flavor (decide c.Adjacent)).flatMap fun ve ↦
    (g.v c.flavor (decide c.Adjacent)).map fun vx ↦ ⟨ve, vx⟩

/-- The grammar generates a construction when some grammatical clause extracts the phrase, has
the word order, and shows the prefix. -/
def Generates (extracted : Option Extracted) (order : List Term) (affix : List Exponent) : Prop :=
  ∃ c : Clause, c.extracted = extracted ∧ c.surface = order ∧
    ∃ e ∈ g.exponences c, e.affix = affix ∧ g.Grammatical c e

instance (x : Option Extracted) (order : List Term) (affix : List Exponent) :
    Decidable (g.Generates x order affix) := by
  unfold Generates; infer_instance

end Grammar

/-! ### The rows -/

/-- The grammars as named in the rows. -/
def grammarTable : List (String × Grammar) :=
  [("desa", desa), ("standard", standard), ("jakarta", jakarta), ("kuching", kuching),
    ("politeMadurese", politeMadurese), ("familiarMadurese", familiarMadurese)]

/-- The extracted phrases as named in the rows. -/
def extractedTable : List (String × Option Extracted) :=
  [("none", none), ("agent", some (.nominal .agent)), ("theme", some (.nominal .theme)),
    ("pp", some .pp)]

/-- The subjects as named in the rows. -/
def subjectTable : List (String × Option Nominal) :=
  [("none", none), ("agent", some .agent), ("theme", some .theme)]

/-- Whether the agent is low, as named in the rows. -/
def lowAgentTable : List (String × Bool) := [("yes", true), ("no", false)]

/-- The prefixes as named in the rows. -/
def affixTable : List (String × List Exponent) :=
  [("meN", [.me, .n]), ("N", [.n]), ("di", [.di]), ("e", [.e]), ("bare", [])]

/-- A row's labels describe a word order of the paper's schema `DP Aux* (DPag) v+V (DPth)`. -/
def surfaceOrder (extracted : Option Extracted) (subject : Option Nominal) (lowAgent : Bool) :
    List Term :=
  let moved : List Term :=
    ((extracted.map Extracted.term).toList ++ (subject.map Term.dp).toList).dedup
  moved ++ ([.aux] : List Term) ++ (if lowAgent then [.dp .agent] else [] : List Term) ++
    ([.verb] : List Term) ++ (if Term.dp .theme ∈ moved then [] else [.dp .theme] : List Term)

/-- A row gives a grammar, what is extracted, the word order, the prefix, and the judgment. -/
structure Row where
  grammar : Grammar
  extracted : Option Extracted
  order : List Term
  affix : List Exponent
  judgment : Judgment

/-- A row is read off an example's labels. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let extracted ← ex.parse? "extracted" extractedTable
  pure ⟨← ex.parse? "grammar" grammarTable, extracted,
    surfaceOrder extracted (← ex.parse? "subject" subjectTable)
      (← ex.parse? "lowAgent" lowAgentTable),
    ← ex.parse? "prefix" affixTable, ex.judgment⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

/-- The rows of the six grammars. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- Every example is acceptable exactly when its grammar generates its construction. -/
theorem rows_grammatical :
    ∀ r ∈ rows, r.judgment = .acceptable ↔ r.grammar.Generates r.extracted r.order r.affix := by
  decide +kernel

/-! ### The ordering paradoxes -/

/-- With Voice overt and the agent in Spec,vP at VoiceP Spell-out, raising the agent to Spec,TP
orders it before Voice at CP, against VoiceP (57). -/
theorem overt_voice_paradox (c : Clause) (e : Exponence) (hv : e.voice.isSome = true)
    (hi : c.AgentInSitu) (hs : c.subject = some .agent) : ¬ Consistent (c.phases e) := by
  have hnot : Term.voice ∉ c.moved := by
    unfold Clause.moved
    rcases c.extracted with _ | ⟨_⟩ | _ <;> rcases c.subject with _ | _ <;> simp [Extracted.term]
  have hagent : Term.dp .agent ∈ c.moved := by simp [Clause.moved, hs]
  simp only [Clause.phases, Exponence.prune, hv, ite_true]
  refine not_consistent_of_pair Term.voice (.dp .agent)
    ⟨c.voiceP, List.mem_cons_self, ?_⟩ ⟨c.cP, by simp, ?_⟩
  · unfold Clause.voiceP
    rw [ite_eq_left hi]
    exact ((by simp : [Term.voice, .dp .agent] <+ [Term.dp c.spec, .voice] ++ [.dp .agent]).trans
      ((List.sublist_append_right _ _).append_right _)).trans
      ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _))
  · unfold Clause.cP
    exact List.Sublist.append
      ((List.singleton_sublist.mpr hagent).trans (List.sublist_append_left _ [Term.aux]))
      (List.singleton_sublist.mpr
        (List.mem_filter.mpr ⟨by simp [Clause.voiceP], by simpa using hnot⟩))

-- (60)
theorem bare_passive_agent_paradox (c : Clause) (e : Exponence) (ha : c.agentProjected = true)
    (hsp : c.spec = .theme) (he : c.extracted = some (.nominal .agent))
    (hs : c.subject = some .theme) : ¬ Consistent (c.phases e) := by
  have hi : c.AgentInSitu := ⟨ha, by simp [hsp]⟩
  have hm : c.moved = [.dp .agent, .dp .theme] := by
    unfold Clause.moved; rw [he, hs]; decide
  have hv : [Term.dp .theme, .dp .agent] <+ c.voiceP := by
    unfold Clause.voiceP
    rw [ite_eq_left hi, ite_eq_left hsp, hsp]
    exact ((by simp :
      [Term.dp .theme, .dp .agent] <+ [Term.dp .theme, .voice] ++ [.dp .agent]).trans
      ((List.sublist_append_right _ _).append_right _)).trans
      ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _))
  have hc : [Term.dp .agent, .dp .theme] <+ c.cP := by
    unfold Clause.cP; rw [hm]
    exact (List.sublist_append_left _ [Term.aux]).trans (List.sublist_append_left _ _)
  unfold Clause.phases Exponence.prune
  split
  · exact not_consistent_of_pair _ _ ⟨_, by simp, hv⟩ ⟨_, by simp, hc⟩
  · exact not_consistent_of_pair (Term.dp .theme) (.dp .agent)
      ⟨c.voiceP.filter (fun x ↦ !decide (x = Term.voice)), by simp,
        by simpa using hv.filter (fun x ↦ !decide (x = Term.voice))⟩
      ⟨c.cP.filter (fun x ↦ !decide (x = Term.voice)), by simp,
        by simpa using hc.filter (fun x ↦ !decide (x = Term.voice))⟩

/-! ### The predictions of §5 -/

-- §5.2
theorem n_on_v_allows_object_extraction :
    kuching.Generates (some (.nominal .theme)) [.dp .theme, .dp .agent, .aux, .verb] [.n] ∧
      ¬ jakarta.Generates (some (.nominal .theme)) [.dp .theme, .dp .agent, .aux, .verb] [.n] := by
  decide +kernel

-- §5.3
theorem madurese_registers :
    politeMadurese.Generates none [.dp .theme, .aux, .dp .agent, .verb] [] ∧
      politeMadurese.Generates (some (.nominal .theme)) [.dp .theme, .dp .agent, .aux, .verb] [] ∧
      ¬ familiarMadurese.Generates none [.dp .theme, .aux, .dp .agent, .verb] [] ∧
      ¬ familiarMadurese.Generates (some (.nominal .theme))
        [.dp .theme, .dp .agent, .aux, .verb] [] := by
  decide +kernel

end ErlewineSommerlot2025
