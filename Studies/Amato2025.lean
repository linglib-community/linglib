module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Amato2025
public import Linglib.Syntax.Clause.Alignment
public import Linglib.Syntax.Minimalist.Feature.Valuation
public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Studies.Bobaljik2008

/-!
# Amato (2025): Nested Agree

The probes on a head are discharged one at a time, in an order fixed for the head. In
[amato-2025]'s *Nested Agree* a probe exploits the dependency its predecessor on the same head
established: when the predecessor targeted the goal `β`, the search of the next probe starts at
`β`, and what the head c-commands above `β` is outside its domain.

We take the domain of a head to be the list of the heads it c-commands, in c-command order. Two
operations bound a search within it. The Phase Impenetrability Condition bounds it from below:
`accessible phase dom` is the prefix of `dom` down to and including the first phase head. Nested
Agree bounds it from above: `nestedDomain dom (some β) = dom.dropWhile (· ≠ β)` is the suffix of
`dom` at `β`, and `nestedDomain dom none = dom`. One operation of a head `α`,
`nestedAgree act α dom prev t s`, is Agree of the probe of `α` for the feature `t` over the domain
nested under the goal `prev` of the previous operation, and `run act α dom ts s` discharges the
probes `ts` in order, each nested under the goal of the one before.

Every operation targets the closest matching goal of its own domain. A probe whose predecessor
targeted a goal that matches it targets that goal, whatever matches higher up, and never a goal
above it; when the predecessor's goal does not match, the search goes on below it; and a probe
whose predecessor found no goal searches the whole domain. In a domain without repetitions the
domains of successive operations are nested suffixes. Valuation only adds features, so a run
extends the state.

The derivations of the paper are runs of this engine over its trees. In Standard Italian the
person probe of Perf, nested under its Infl probe, targets v across the subject, and the perfect
auxiliary the Vocabulary Items insert is the one the transitivity class of the clause selects:
*avere* where v has copied a person value from a full object, *essere* with a defective v, a
reflexive object, direct or indirect, the impersonal *si* and the passive. The examples of the
paper have the auxiliary their derivations insert. With the two probes of Perf in the other order
the auxiliary follows the person of the subject, as in Ariellese. In ditransitive clauses, for
either order of the case probe and the ϕ-probe of v and whether or not Appl assigns dative, an
indirective agreement alignment comes with an indirective case alignment and a secundative case
alignment with a secundative agreement alignment, [barany-2024]'s gap. Across an Icelandic
dative, number agreement with the nominative is derived under one of the two orders of T's probes
within a clause and under neither across two, whatever the number of the dative, and the forms
of the verb in the examples of [ussery-2009] and [holmberg-hroarsdottir-2003] are acceptable
exactly when some order derives them. In Bulgarian multiple wh-fronting the order of the
wh-words that fronting derives is the acceptable one of [rudin-1988]'s two. The remaining
derivations are person agreement with the object in the Lak perfective and with the subject in
the present, subject agreement in Spanish VOS clauses, and Hindi-Urdu agreement, where T has
the person of the controller that [bobaljik-2008]'s accessibility of unmarked case picks, and no
value where both arguments are marked, as the verb shows in [mahajan-1990]'s examples.

## Implementation notes

A probe's domain is a list, the notation of the paper's linear diagrams, and the lists of the
trees are written out; they are not computed from syntactic objects. A probe whose predecessor
found no goal searches the whole domain, also when a probe before that one found a goal: the
paper's definition relates consecutive operations only. A valued probe, such as a case assigner,
matches a goal that bears the feature unvalued, and an unvalued probe matches any goal that bears
it, so a goal that matches without a value ends the search without valuing the probe, the paper's
defective intervention.

Where v assigns accusative to the recipient the theme is left without case, so the ditransitive
derivations give indirective and secundative case alignments and no neutral one, with both
objects accusative, which [barany-2024]'s generalization also covers.

Merge and binding inside v's cycle are not modelled: the reflexive enters v's cycle unvalued, as
it is when v probes it. The paper's person feature π and its ϕ are both the person dimension, and
the Icelandic number agreement is the number dimension. Participle agreement and the comparison
with principles of maximized matching are not formalized.

## TODO

* [holmberg-hroarsdottir-2003] report that in the construction of (29b) the agreeing form is
  possible beside the default one when the dative is plural. The derivation gives the default
  form for either number of the dative.
* The Ariellese paradigm of [dalessandro-roberts-2010] and the Lak and Spanish examples are not
  yet rows of the data.

## References

* [amato-2025]
* [barany-2024]
* [bobaljik-2008]
* [dalessandro-roberts-2010]
* [holmberg-hroarsdottir-2003]
* [mahajan-1990]
* [rudin-1988]
* [ussery-2009]
-/

@[expose] public section

namespace Amato2025

open Minimalist
open Minimalist.FeatureBundle (ofList)
open ArgumentStructure (TransitivityClass)
open Verb (PerfectAuxiliary)
open Alignment (IsIndirective IsSecundative)

variable {H : Type*}

/-! ### Search domains -/

/-- The part of a domain open to search under the PIC: down to and including the first phase
head, whose complement is closed. -/
def accessible (phase : H → Prop) [DecidablePred phase] : List H → List H
  | [] => []
  | h :: hs => h :: if phase h then [] else accessible phase hs

theorem accessible_prefix (phase : H → Prop) [DecidablePred phase] (dom : List H) :
    accessible phase dom <+: dom := by
  induction dom with
  | nil => exact List.prefix_rfl
  | cons h hs ih =>
    rw [accessible]
    split_ifs
    exacts [(List.prefix_cons_inj _).2 List.nil_prefix, (List.prefix_cons_inj _).2 ih]

variable [DecidableEq H]

/-- The domain of a probe whose predecessor on the same head targeted `prev`: the part of `dom`
from that goal down, and all of `dom` when the predecessor found no goal. -/
def nestedDomain (dom : List H) : Option H → List H
  | none => dom
  | some β => dom.dropWhile (· ≠ β)

variable {dom pre post : List H} {β γ δ : H}

@[simp] theorem nestedDomain_none : nestedDomain dom none = dom := rfl

theorem nestedDomain_suffix (dom : List H) (prev : Option H) : nestedDomain dom prev <:+ dom := by
  cases prev with
  | none => exact List.suffix_rfl
  | some β => exact List.dropWhile_suffix _

theorem nestedDomain_append_of_notMem (hβ : β ∉ pre) :
    nestedDomain (pre ++ post) (some β) = nestedDomain post (some β) :=
  List.dropWhile_append_of_pos fun a ha ↦ by simpa using fun (h : a = β) ↦ hβ (h ▸ ha)

theorem nestedDomain_append_cons (hβ : β ∉ pre) :
    nestedDomain (pre ++ β :: post) (some β) = β :: post := by
  rw [nestedDomain_append_of_notMem hβ]; simp [nestedDomain]

-- the domains of successive operations are nested
theorem nestedDomain_suffix_cons (hnd : (pre ++ β :: post).Nodup) (hγ : γ ∈ β :: post) :
    nestedDomain (pre ++ β :: post) (some γ) <:+ β :: post := by
  rw [nestedDomain_append_of_notMem fun h ↦ (List.nodup_append.1 hnd).2.2 γ h γ hγ rfl]
  exact nestedDomain_suffix _ _

/-! ### Nested Agree -/

variable (act : H → FeatureType → Prop) [∀ h t, Decidable (act h t)]

/-- (1): One operation of the head `α`, Agree of its probe for `t` over the domain nested under
the goal `prev` of its previous operation. A goal that `act` marks inactive at `t` is matched
without valuing. -/
def nestedAgree (α : H) (dom : List H) (prev : Option H) (t : FeatureType) (s : FeatureState H) :
    Probe.Result H (FeatureState H) :=
  (s.probe α t (act · t)).agree (fun g s ↦ s.value α t g) s (nestedDomain dom prev)

/-- The probes `ts` of `α` discharged in order over `dom`, the first nested under `prev` and each
later one under the goal of the one before. Returns the goal of each probe and the resulting
state. -/
def runFrom (α : H) (dom : List H) :
    Option H → List FeatureType → FeatureState H → List (Option H) × FeatureState H
  | _, [], s => ([], s)
  | prev, t :: ts, s =>
    let r := nestedAgree act α dom prev t s
    let rest := runFrom α dom r.satisfier ts r.state
    (r.satisfier :: rest.1, rest.2)

/-- The probes `ts` of `α` discharged in order over `dom`. -/
def run (α : H) (dom : List H) (ts : List FeatureType) (s : FeatureState H) :
    List (Option H) × FeatureState H :=
  runFrom act α dom none ts s

variable {act} {α : H} {prev : Option H} {t : FeatureType} {ts : List FeatureType}
  {s : FeatureState H}

@[simp] theorem runFrom_nil : runFrom act α dom prev [] s = ([], s) := rfl

theorem runFrom_cons :
    runFrom act α dom prev (t :: ts) s =
      ((nestedAgree act α dom prev t s).satisfier ::
          (runFrom act α dom (nestedAgree act α dom prev t s).satisfier ts
            (nestedAgree act α dom prev t s).state).1,
        (runFrom act α dom (nestedAgree act α dom prev t s).satisfier ts
          (nestedAgree act α dom prev t s).state).2) :=
  rfl

-- every operation targets the closest matching goal of its own domain
theorem nestedAgree_satisfier :
    (nestedAgree act α dom prev t s).satisfier =
      (nestedDomain dom prev).find? (s.Matches α t ·) :=
  Probe.agree_satisfier

/-- A probe whose predecessor targeted a goal that matches it targets that goal. -/
theorem nestedAgree_satisfier_of_matches (hβ : β ∈ dom) (h : s.Matches α t β) :
    (nestedAgree act α dom (some β) t s).satisfier = some β := by
  obtain ⟨pre, post, rfl, hpre⟩ := List.eq_append_cons_of_mem hβ
  rw [nestedAgree_satisfier, nestedDomain_append_cons hpre,
    List.find?_cons_of_pos (by simpa using h)]

-- §2, downward expansion
theorem nestedAgree_satisfier_of_not_matches (hβ : β ∉ pre) (h : ¬ s.Matches α t β) :
    (nestedAgree act α (pre ++ β :: post) (some β) t s).satisfier =
      post.find? (s.Matches α t ·) := by
  rw [nestedAgree_satisfier, nestedDomain_append_cons hβ,
    List.find?_cons_of_neg (by simpa using h)]

theorem mem_nestedDomain_of_satisfier
    (h : (nestedAgree act α dom prev t s).satisfier = some γ) : γ ∈ nestedDomain dom prev :=
  List.mem_of_find?_eq_some (nestedAgree_satisfier (act := act) ▸ h)

/-- A probe never targets a goal above the goal of its predecessor, whether or not it matches. -/
theorem nestedAgree_satisfier_ne (hnd : (pre ++ β :: post).Nodup) (hδ : δ ∈ pre) :
    (nestedAgree act α (pre ++ β :: post) (some β) t s).satisfier ≠ some δ := by
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.1 hnd
  intro h
  have hmem := mem_nestedDomain_of_satisfier h
  rw [nestedDomain_append_cons fun hm ↦ hdisj β hm β (by simp) rfl] at hmem
  exact hdisj δ hδ δ hmem rfl

theorem le_nestedAgree_state : s ≤ (nestedAgree act α dom prev t s).state :=
  s.le_agree_state α t _ _

theorem le_runFrom : s ≤ (runFrom act α dom prev ts s).2 := by
  induction ts generalizing prev s with
  | nil => exact le_rfl
  | cons t ts ih => exact (le_nestedAgree_state (act := act)).trans ih

theorem le_run : s ≤ (run act α dom ts s).2 := le_runFrom

/-! ### Multiple Agree and movement -/

/-- Under Multiple Agree `[∗wh∗]` reaches every matching goal in c-command order (§4.2.3). -/
def multipleAgree (s : FeatureState H) (α : H) (t : FeatureType) (dom : List H) : List H :=
  ((Probe.insatiable (s.Matches α t)).agree (fun g s ↦ s.value α t g) s dom).interacted

/-- In (36) the Merge feature `[·wh·]`, nested under the last goal of `[∗wh∗]`, raises it first, and
each later application, its landing site being above the probe, searches the remaining domain
afresh. The result lists the movers in order of movement. -/
def whFronting (s : FeatureState H) (α : H) (dom : List H) : List H :=
  let p := Probe.relativized (s.Matches α .wh)
  match (multipleAgree s α .wh dom).getLast? with
  | none => []
  | some β => (p.search (nestedDomain dom (some β))).toList ++ rest p dom.length (dom.erase β)
where
  rest (p : Probe H) : Nat → List H → List H
  | 0, _ => []
  | n + 1, d =>
    match p.search d with
    | none => []
    | some g => g :: rest p n (d.erase g)

/-! ### The paper's heads -/

/-- The heads of the paper's trees. -/
inductive Head
  | t | perf | asp | c | v | voice | appl | verb
  | dpSbj | dpObj | dpR | dpT | dpDat | dpNom | si | whSbj | whObj
  deriving DecidableEq, Repr, Fintype

/-- v and Voice are phase heads (§3.4.2, fn. 18). -/
def IsPhase (h : Head) : Prop := h = .v ∨ h = .voice

instance : DecidablePred IsPhase := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Every goal values its probe. -/
def AllActive : Head → FeatureType → Prop := fun _ _ ↦ True

instance (h : Head) (t : FeatureType) : Decidable (AllActive h t) :=
  inferInstanceAs (Decidable True)

/-- `[ϕ:p]`. -/
def person (p : Person) : Σ t : FeatureType, FeatureSlot t.Slot :=
  ⟨.person, ↑(FeatureType.Slot.ofValue .person p)⟩

private theorem eq_or_eq_of_perm_pair {α : Type*} {a b : α} {l : List α} (h : l.Perm [a, b]) :
    l = [a, b] ∨ l = [b, a] := by
  match l, h.length_eq with
  | [x, y], _ =>
    have hx : x ∈ [a, b] := h.subset (by simp)
    have hy : y ∈ [a, b] := h.subset (by simp)
    have ha : a ∈ [x, y] := h.symm.subset (by simp)
    have hb : b ∈ [x, y] := h.symm.subset (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy ha hb
    grind

/-! ### Standard Italian auxiliary selection (§3)

Perf bears `[∗Infl:perf∗]` and `[∗π:_∗]`, ordered as in (7) or (22). v first runs its own
cycle over its complement ((9), (16), (19)); Perf then probes the vP, and T the PerfP (11). -/

/-- The paper has two Voice heads, Voice_imp of the impersonal *si* (§3.4.4) and Voice_pass (fn.
18). -/
inductive VoiceHead where
  | impersonal
  | passive
  deriving DecidableEq, Repr, Fintype

/-- A clause of §3.4 has v's class (`TransitivityClass`; an unergative verb is transitive with a
covert cognate object bearing default features, fn. 10) under no Voice head, or under Voice_imp
(§3.4.4) or Voice_pass (fn. 18). A v that is not defective may be the quirky v of (19), which
selects an ApplP with the indirect object in its specifier and assigns it dative; in a reflexive
clause the indirect object is then the reflexive. -/
structure Clause where
  verb : TransitivityClass
  voice : Option VoiceHead := none
  quirky : Bool := false
  deriving DecidableEq, Repr

/-- Before Agree, with subject person `p`, Perf bears `[∗Infl:perf∗], [∗π:_∗]`; T `[∗case:nom∗],
[∗ϕ:_∗]`; a transitive v `[Infl:_], [∗case:acc∗], [∗π:_∗]`, a quirky v `[∗case:dat∗]` in place of
accusative (19), and a defective v `[Infl:_]` (15); Voice_imp `[Infl:_], [π:_]` (20), Voice_pass
`[Infl:_]`; the subject `[ϕ:p], [case:_]`; a full object `[ϕ:3], [case:_]`, accusative from Appl
under a quirky v (the unaccusative theme, `[ϕ:p]`), a reflexive object, direct (16) or indirect
(19), `[ϕ:_], [case:_]`; a full indirect object `[ϕ:3], [case:_]`; and *si* `[π:_], [case:_]`. -/
def initial (cl : Clause) (p : Person) : Head → FeatureBundle
  | .perf => ofList [⟨.infl, .valued .perf⟩, ⟨.person, .unvalued⟩]
  | .t => ofList [⟨.case, .valued .nom⟩, ⟨.person, .unvalued⟩]
  | .v =>
    match cl.verb with
    | .unaccusative => ofList [⟨.infl, .unvalued⟩]
    | _ => ofList [⟨.infl, .unvalued⟩,
        if cl.quirky then ⟨.case, .valued .dat⟩ else ⟨.case, .valued .acc⟩, ⟨.person, .unvalued⟩]
  | .voice =>
    match cl.voice with
    | some .impersonal =>
      ofList [⟨.infl, .unvalued⟩, ⟨.person, .unvalued⟩]
    | some .passive => ofList [⟨.infl, .unvalued⟩]
    | _ => ⊥
  | .si => ofList [⟨.person, .unvalued⟩, ⟨.case, .unvalued⟩]
  | .dpSbj => ofList [person p, ⟨.case, .unvalued⟩]
  | .dpR =>
    match cl.verb with
    | .reflexive => ofList [⟨.person, .unvalued⟩, ⟨.case, .unvalued⟩]
    | _ => ofList [person .third, ⟨.case, .unvalued⟩]
  | .dpObj =>
    match cl.verb with
    | .unaccusative => ofList [person p, ⟨.case, .unvalued⟩]
    | .reflexive =>
      if cl.quirky then ofList [person .third, ⟨.case, .valued .acc⟩]
      else ofList [⟨.person, .unvalued⟩, ⟨.case, .unvalued⟩]
    | _ => ofList [person .third,
        if cl.quirky then ⟨.case, .valued .acc⟩ else ⟨.case, .unvalued⟩]
  | _ => ⊥

/-- The heads v c-commands: its complement in (9) and (16), and the ApplP of (19) under a quirky
v. -/
def vDomain (cl : Clause) : List Head :=
  if cl.quirky then [.dpR, .appl, .verb, .dpObj] else [.verb, .dpObj]

/-- The heads Perf c-commands, in order: (10) and (18) for a transitive v and (15) for a defective
one, under the Voice layer of (20) when there is one. -/
def belowPerf (cl : Clause) : List Head :=
  (match cl.voice with
    | some .impersonal => [.si, .voice]
    | some .passive => [.voice]
    | none => []) ++
  match cl.verb with
  | .unaccusative => [.dpObj, .v, .verb]
  | _ => .dpSbj :: .v :: vDomain cl

/-- In v's cycle ((9), (16), (19)) v assigns its case and then π-agrees; a defective v does
neither. -/
def vCycle (cl : Clause) (p : Person) : List (Option Head) × FeatureState Head :=
  run AllActive .v (vDomain cl) (if cl.verb = .unaccusative then [] else [.case, .person])
    (initial cl p)

/-- Perf's cycle under the feature ordering `ord`. -/
def perfCycle (ord : List FeatureType) (cl : Clause) (p : Person) :
    List (Option Head) × FeatureState Head :=
  run AllActive .perf (accessible IsPhase (belowPerf cl)) ord (vCycle cl p).2

/-- In T's cycle (11) T assigns nominative and then ϕ-agrees. -/
def tCycle (ord : List FeatureType) (cl : Clause) (p : Person) :
    List (Option Head) × FeatureState Head :=
  run AllActive .t (accessible IsPhase (.perf :: belowPerf cl)) [.case, .person]
    (perfCycle ord cl p).2

/-- The state after v, Perf and T have probed. -/
def derive (ord : List FeatureType) (cl : Clause) (p : Person) : FeatureState Head :=
  (tCycle ord cl p).2

/-- Standard Italian orders its probes by argument structure, Infl before person (7). -/
def standardItalian : List FeatureType := [.infl, .person]

/-- Ariellese orders its probes by the subject, person before Infl (22). -/
def ariellese : List FeatureType := [.person, .infl]

/-- In Perf's domain in (10) the subject is c-commanded first, then v. -/
example : accessible IsPhase (belowPerf ⟨.transitive, none, false⟩) = [.dpSbj, .v] := by decide

/-- In (10) the subject matches the person probe of Perf, which targets v below it. -/
example (p : Person) :
    (perfCycle [.infl] ⟨.transitive, none, false⟩ p).2.Matches .perf .person .dpSbj := by
  revert p; decide

-- (10), (18)
theorem perf_targets_v (c : TransitivityClass) (hc : c ≠ .unaccusative) (q : Bool) (p : Person) :
    (perfCycle standardItalian ⟨c, none, q⟩ p).1 = [some .v, some .v] := by
  revert c q p; decide

-- (15)
theorem perf_unaccusative (q : Bool) (p : Person) :
    (perfCycle standardItalian ⟨.unaccusative, none, q⟩ p).1 = [some .v, none] := by
  revert q p; decide

-- (19)
theorem v_targets_reflexive (p : Person) :
    (vCycle ⟨.reflexive, none, true⟩ p).1 = [some .dpR, some .dpR] := by
  revert p; decide

-- (20)
theorem perf_impersonal (c : TransitivityClass) (q : Bool) (p : Person) :
    (perfCycle standardItalian ⟨c, some .impersonal, q⟩ p).1 = [some .voice, some .voice] := by
  revert c q p; decide

-- (11)
theorem t_targets_subject (c : TransitivityClass) (hc : c ≠ .unaccusative) (q : Bool)
    (p : Person) : (tCycle standardItalian ⟨c, none, q⟩ p).1 = [some .dpSbj, some .dpSbj] := by
  revert c q p; decide

/-- The Vocabulary Items (14) insert `/AVERE/ ↔ Perf[π:α]`, and `/ESSERE/` elsewhere. -/
def standardItalianAux (s : FeatureState Head) : PerfectAuxiliary :=
  if (s .perf .person).unbotD ⊥ ≠ ⊥ then .have else .be

/-- In Standard Italian the derivation inserts the auxiliary the transitivity class of the clause
selects. -/
theorem standardItalian_aux (c : TransitivityClass) (q : Bool) (p : Person) :
    standardItalianAux (derive standardItalian ⟨c, none, q⟩ p) = c.canonicalSelection := by
  revert c q p; decide

-- (5d), fn. 18
theorem standardItalian_voice (c : TransitivityClass) (f : VoiceHead) (q : Bool) (p : Person) :
    standardItalianAux (derive standardItalian ⟨c, some f, q⟩ p) = .be := by
  revert c f q p; decide

/-- The clause of the derivations for each clause type of the examples: (5b) and (5c) have the
reflexive as the indirect object of a quirky v, and (5d) the impersonal over a transitive vP. -/
def ofExample : Examples.Clause → Clause
  | .transitive => ⟨.transitive, none, false⟩
  | .unergative => ⟨.unergative, none, false⟩
  | .unaccusative => ⟨.unaccusative, none, false⟩
  | .directReflexive => ⟨.reflexive, none, false⟩
  | .indirectReflexive => ⟨.reflexive, none, true⟩
  | .impersonal => ⟨.transitive, some .impersonal, false⟩

/-- The auxiliary a lexeme of the examples is, if it is one. -/
def Examples.Lexeme.auxiliary? : Examples.Lexeme → Option PerfectAuxiliary
  | .avere => some .have
  | .essere => some .be
  | _ => none

/-- Each of the examples (4) and (5), all with a third person subject, has the auxiliary the
derivation of its clause type inserts. -/
theorem auxiliary_example (x : Examples.Example) :
    (x.lexemes .auxiliary).filterMap (·.auxiliary?) =
      (x.clause.map fun c ↦
        standardItalianAux (derive standardItalian (ofExample c) .third)).toList := by
  revert x; decide

/-- Ariellese (23) inserts `/AVERE/ ↔ Perf[π:-participant]`. -/
def arielleseAux (s : FeatureState Head) : PerfectAuxiliary :=
  if s .perf .person = ↑(FeatureType.Slot.ofValue .person .third) then .have else .be

-- (22), (21), §3.5
theorem ariellese_aux (c : TransitivityClass) (q : Bool) (p : Person) :
    arielleseAux (derive ariellese ⟨c, none, q⟩ p) = if p = .third then .have else .be := by
  revert c q p; decide

/-- Tufillese (24) inserts `/AVERE/ ↔ Perf[π:α] / T[ϕ:3sg]`. -/
def tufilleseAux (s : FeatureState Head) : PerfectAuxiliary :=
  if (s .perf .person).unbotD ⊥ ≠ ⊥ ∧ s .t .person = ↑(FeatureType.Slot.ofValue .person .third) then
    .have
  else .be

-- §3.5
theorem tufillese_aux (c : TransitivityClass) (q : Bool) (p : Person) :
    tufilleseAux (derive standardItalian ⟨c, none, q⟩ p) =
      if c.canonicalSelection = .have ∧ p = .third then .have else .be := by
  revert c q p; decide

/-! ### Case and agreement in ditransitive clauses (§4.1.1) -/

/-- In (25)–(28) v bears `[∗case:acc∗], [∗ϕ:_∗]` over `DP_R … Appl … V … DP_T`, the recipient
already dative from Appl or not. -/
def ditransitiveInitial (applDat : Bool) : Head → FeatureBundle
  | .v => ofList [⟨.case, .valued .acc⟩, ⟨.person, .unvalued⟩]
  | .dpR => ofList
      [person .third, if applDat then ⟨.case, .valued .dat⟩ else ⟨.case, .unvalued⟩]
  | .dpT => ofList [person .third, ⟨.case, .unvalued⟩]
  | _ => ⊥

/-- The derivation of (25)–(28), in which v's probes, in the order `ts`, search the recipient,
Appl, the verb and the theme. -/
def ditransitive (ts : List FeatureType) (applDat : Bool) :
    List (Option Head) × FeatureState Head :=
  run AllActive .v [.dpR, .appl, .verb, .dpT] ts (ditransitiveInitial applDat)

/-- The goal of v's ϕ-probe. -/
def phiGoal (ts : List FeatureType) (applDat : Bool) : Option Head :=
  ((ts.zip (ditransitive ts applDat).1).lookup .person).join

/-- The case of each object, the recipient and the theme as the derivation leaves them and P
with the accusative v assigns a transitive object; S and A are not read. -/
def caseMarking (ts : List FeatureType) (applDat : Bool) : ArgumentRole → FeatureSlot (Flat Case)
  | .R => (ditransitive ts applDat).2 .dpR .case
  | .T => (ditransitive ts applDat).2 .dpT .case
  | _ => .valued .acc

/-- Whether v ϕ-agrees with each object. It agrees with a transitive object P and with whichever
of the recipient and the theme its ϕ-probe finds; S and A are not read. -/
def agreement (ts : List FeatureType) (applDat : Bool) : ArgumentRole → Bool
  | .R => phiGoal ts applDat = some .dpR
  | .T => phiGoal ts applDat = some .dpT
  | _ => true

-- (25)
theorem ditransitive_caseFirst_dat :
    IsIndirective (caseMarking [.case, .person] true) ∧
      IsIndirective (agreement [.case, .person] true) ∧
      phiGoal [.case, .person] true = some .dpT := by
  decide

-- (26)
theorem ditransitive_caseFirst_noDat :
    IsSecundative (caseMarking [.case, .person] false) ∧
      IsSecundative (agreement [.case, .person] false) := by
  decide

-- (27)
theorem ditransitive_phiFirst_dat :
    IsIndirective (caseMarking [.person, .case] true) ∧
      IsSecundative (agreement [.person, .case] true) := by
  decide

-- (28)
theorem ditransitive_phiFirst_noDat :
    IsSecundative (caseMarking [.person, .case] false) ∧
      IsSecundative (agreement [.person, .case] false) := by
  decide

/-- Table 1 of [barany-2024]: however v orders its case probe and its ϕ-probe, and whether or not
Appl assigns dative, an indirective agreement alignment comes with an indirective case
alignment. -/
theorem isIndirective_caseMarking_of_agreement {ts : List FeatureType}
    (hts : ts.Perm [.case, .person]) (d : Bool) :
    IsIndirective (agreement ts d) → IsIndirective (caseMarking ts d) := by
  rcases eq_or_eq_of_perm_pair hts with rfl | rfl <;> (revert d; decide)

-- (26), (28): a secundative case alignment comes with a secundative agreement alignment
theorem isSecundative_agreement_of_caseMarking {ts : List FeatureType}
    (hts : ts.Perm [.case, .person]) (d : Bool) :
    IsSecundative (caseMarking ts d) → IsSecundative (agreement ts d) := by
  rcases eq_or_eq_of_perm_pair hts with rfl | rfl <;> (revert d; decide)

/-! ### Icelandic DAT-NOM constructions (§4.1.2) -/

/-- (29a) versus (29b). -/
inductive Clausal
  | monoclausal | biclausal
  deriving DecidableEq, Repr, Fintype

/-- T `[∗case:nom∗], [∗ϕ:_∗]` over `DP_dat … DP_nom`, the dative of number `n` and the nominative
plural; in (29b) the lower T has already assigned nominative. -/
def icelandicInitial (k : Clausal) (n : FeatureType.number.Value) : Head → FeatureBundle
  | .t => ofList [⟨.case, .valued .nom⟩, ⟨.number, .unvalued⟩]
  | .dpDat => ofList [⟨.number, .valued n⟩, ⟨.case, .valued .dat⟩]
  | .dpNom =>
    match k with
    | .monoclausal => ofList [⟨.number, .valued .plural⟩, ⟨.case, .unvalued⟩]
    | .biclausal => ofList [⟨.number, .valued .plural⟩, ⟨.case, .valued .nom⟩]
  | _ => ⊥

/-- Datives are defective goals for ϕ-Agree, matched but never valuing. -/
def IcelandicActive (h : Head) (t : FeatureType) : Prop := ¬ (h = .dpDat ∧ t = .number)

instance (h : Head) (t : FeatureType) : Decidable (IcelandicActive h t) :=
  inferInstanceAs (Decidable (¬ _))

/-- T's number slot after its probes, in the order `ts`, have searched a dative of number `n`
and the nominative. -/
def icelandic (k : Clausal) (n : FeatureType.number.Value) (ts : List FeatureType) :
    FeatureSlot FeatureType.number.Slot :=
  (run IcelandicActive .t [.dpDat, .dpNom] ts (icelandicInitial k n)).2 .t .number

-- (29a)
theorem icelandic_monoclausal_caseFirst (n : FeatureType.number.Value) :
    icelandic .monoclausal n [.case, .number] = .valued .plural := by
  revert n; decide

-- (29a)
theorem icelandic_monoclausal_phiFirst (n : FeatureType.number.Value) :
    icelandic .monoclausal n [.number, .case] = .unvalued := by
  revert n; decide

-- (29b)
theorem icelandic_biclausal (n : FeatureType.number.Value) {ts : List FeatureType}
    (hts : ts.Perm [.case, .number]) : icelandic .biclausal n ts = .unvalued := by
  rcases eq_or_eq_of_perm_pair hts with rfl | rfl <;> (revert n; decide)

/-- The construction of the derivations for each construction of the examples. -/
def Examples.Construction.clausal : Examples.Construction → Clausal
  | .monoclausal => .monoclausal
  | .biclausal => .biclausal

/-- T's number slot under each form of the verb: plural for the agreeing form, and no value for
the default one. -/
def Examples.Agreement.slot : Examples.Agreement → FeatureSlot FeatureType.number.Slot
  | .number => .valued .plural
  | .default => .unvalued

-- (29): a form of the verb is acceptable exactly when one of the two orders of T's probes
-- derives it
theorem icelandic_example (x : Examples.Example) (n : FeatureType.number.Value) :
    ∀ k ∈ x.construction, ∀ f ∈ x.agreement,
      (icelandic k.clausal n [.case, .number] = f.slot ∨
          icelandic k.clausal n [.number, .case] = f.slot) ↔
        x.datum.judgment = .acceptable := by
  revert x n; decide

/-! ### Person agreement in Lak (§4.2.1) -/

/-- In (32) Asp bears `[∗Infl:perf∗], [∗π:_∗]`, v `[Infl:_], [∗π:_∗]` and T `[∗π:_∗]`, with
subject person `ps` and object person `po`. -/
def lakInitial (ps po : Person) : Head → FeatureBundle
  | .asp => ofList [⟨.infl, .valued .perf⟩, ⟨.person, .unvalued⟩]
  | .t => ofList [⟨.person, .unvalued⟩]
  | .v => ofList [⟨.infl, .unvalued⟩, ⟨.person, .unvalued⟩]
  | .dpSbj => ofList [person ps]
  | .dpObj => ofList [person po]
  | _ => ⊥

/-- The state after v has agreed with the object. -/
def lakAfterV (ps po : Person) : FeatureState Head :=
  (run AllActive .v [.dpObj] [.person] (lakInitial ps po)).2

/-- Asp's person slot in the perfective, after Asp has agreed with v. -/
def lak (ps po : Person) : FeatureSlot FeatureType.person.Slot :=
  (run AllActive .asp (accessible IsPhase [.dpSbj, .v, .dpObj]) [.infl, .person]
    (lakAfterV ps po)).2 .asp .person

/-- T's person slot in the present, where there is no Asp and no Infl-Agree. -/
def lakPresent (ps po : Person) : FeatureSlot FeatureType.person.Slot :=
  (run AllActive .t (accessible IsPhase [.dpSbj, .v, .dpObj]) [.person] (lakAfterV ps po)).2
    .t .person

-- (31c), (31d)
theorem lak_agrees_with_object (ps po : Person) :
    lak ps po = ↑(FeatureType.Slot.ofValue .person po) := by
  revert ps po; decide

-- (31a)
theorem lakPresent_agrees_with_subject (ps po : Person) :
    lakPresent ps po = ↑(FeatureType.Slot.ofValue .person ps) := by
  revert ps po; decide

/-! ### Subject agreement in Spanish VOS (§4.2.2) -/

/-- In (34) T bears `[∗case:nom∗], [∗ϕ:_∗]` over the shifted object `[case:acc], [ϕ:α]` and the
subject `[case:_], [ϕ:β]`. -/
def vosInitial : Head → FeatureBundle
  | .t => ofList [⟨.case, .valued .nom⟩, ⟨.person, .unvalued⟩]
  | .dpObj => ofList [⟨.case, .valued .acc⟩, person .third]
  | .dpSbj => ofList [⟨.case, .unvalued⟩, person .third]
  | _ => ⊥

-- (33)
theorem vos_subject_agreement :
    (run AllActive .t [.dpObj, .dpSbj] [.case, .person] vosInitial).1 =
      [some .dpSbj, some .dpSbj] := by decide

/-! ### Bulgarian multiple wh-fronting (§4.2.3) -/

/-- In (36) C bears `[∗wh∗] ≻ [·wh·]` over wh-sbj in Spec,T, T, and wh-obj at the edge of vP. -/
def bulgarianInitial : Head → FeatureBundle
  | .c => ofList [⟨.wh, .unvalued⟩]
  | .whSbj | .whObj => ofList [⟨.wh, .valued true⟩]
  | _ => ⊥

/-- C's domain in (36). -/
def bulgarianDomain : List Head := accessible IsPhase [.whSbj, .t, .whObj, .v, .verb]

-- (35)
theorem bulgarian_order : whFronting bulgarianInitial .c bulgarianDomain = [.whObj, .whSbj] := by
  decide

/-- The wh-phrase of (36) a lexeme of the examples is, if it is one. -/
def Examples.Lexeme.head? : Examples.Lexeme → Option Head
  | .koj => some .whSbj
  | .kogo => some .whObj
  | _ => none

-- (35): an order of the wh-words is acceptable exactly when it is the order fronting derives,
-- each mover landing above the ones before it
theorem bulgarian_example (x : Examples.Example) (hx : x.lexemes .wh ≠ []) :
    (x.lexemes .wh).filterMap (·.head?) =
        (whFronting bulgarianInitial .c bulgarianDomain).reverse ↔
      x.datum.judgment = .acceptable := by
  revert x; decide

/-- Without Multiple Agree the wh-probe's first goal is the subject, the order minimality
alone predicts. -/
example :
    (Probe.relativized (FeatureState.Matches bulgarianInitial .c .wh)).search bulgarianDomain =
      some .whSbj := by decide

/-! ### Agreement with unmarked DPs in Hindi-Urdu (§4.3.1) -/

/-- The ergative subject is in Spec,Asp in (37)/(39), both arguments are case-marked in Spec,Asp in
(38a)/(40), and the unmarked subject is in Spec,v under imperfective Asp in (38b). -/
inductive HindiClause
  | ergSubject | bothMarked | unmarkedSubject
  deriving DecidableEq, Repr, Fintype

/-- T `[∗Infl:_∗], [∗ϕ:_∗]`; Asp `[Infl:perf]` or `[Infl:impf]`; v `[∗ϕ:_∗]`; the DPs
with the case Asp assigned them. -/
def hindiInitial (k : HindiClause) (ps po : Person) : Head → FeatureBundle
  | .t => ofList [⟨.infl, .unvalued⟩, ⟨.person, .unvalued⟩]
  | .asp => ofList [⟨.infl, .valued (if k = .unmarkedSubject then .impf else .perf)⟩]
  | .v => ofList [⟨.person, .unvalued⟩]
  | .dpSbj => ofList
      [person ps, if k = .unmarkedSubject then ⟨.case, .unvalued⟩ else ⟨.case, .valued .erg⟩]
  | .dpObj => ofList
      [person po, if k = .bothMarked then ⟨.case, .valued .acc⟩ else ⟨.case, .unvalued⟩]
  | _ => ⊥

/-- The heads T c-commands in (39), (40) and (38b), in order. -/
def hindiDomain : HindiClause → List Head
  | .ergSubject => [.dpSbj, .asp, .v, .verb, .dpObj]
  | .bothMarked => [.dpSbj, .dpObj, .asp, .v, .verb]
  | .unmarkedSubject => [.asp, .dpSbj, .v, .verb, .dpObj]

/-- T's person slot after v has probed its complement (empty in (40), the object having
moved, fn. 33) and T has Infl-agreed with Asp and, nested under it, probed for ϕ. -/
def hindi (k : HindiClause) (ps po : Person) : FeatureSlot FeatureType.person.Slot :=
  let s := (run AllActive .v (if k = .bothMarked then [] else [.verb, .dpObj]) [.person]
    (hindiInitial k ps po)).2
  (run AllActive .t (accessible IsPhase (hindiDomain k)) [.infl, .person] s).2 .t .person

-- (37)
theorem hindi_object_agreement (ps po : Person) :
    hindi .ergSubject ps po = ↑(FeatureType.Slot.ofValue .person po) := by
  revert ps po; decide

-- (38a)
theorem hindi_default_agreement (ps po : Person) : hindi .bothMarked ps po = .unvalued := by
  revert ps po; decide

-- (38b)
theorem hindi_subject_agreement (ps po : Person) :
    hindi .unmarkedSubject ps po = ↑(FeatureType.Slot.ofValue .person ps) := by
  revert ps po; decide

/-- The aspect of each clause: Asp is imperfective where the subject is unmarked. -/
def HindiClause.aspect : HindiClause → Aspect.Perfectivity
  | .unmarkedSubject => .imperfective
  | _ => .perfective

-- §4.3.1: in (37), (38a) and (38b) T has the person of the highest argument with unmarked case,
-- the controller of [bobaljik-2008], and no value where there is none
theorem hindi_eq_controller (k : HindiClause) (ps po : Person) :
    hindi k ps po =
      (Bobaljik2008.hindiController k.aspect (k = .bothMarked)).elim .unvalued fun r ↦
        ↑(FeatureType.Slot.ofValue .person (if r = .A then ps else po)) := by
  revert k ps po; decide

/-- The clause of the derivations for each marking of the examples. -/
def Examples.Marking.clause : Examples.Marking → HindiClause
  | .ergSubject => .ergSubject
  | .bothMarked => .bothMarked
  | .unmarkedSubject => .unmarkedSubject

/-- T's person slot when the verb shows the features of the subject, of the object, or neither. -/
def Examples.Controller.slot (ps po : Person) :
    Examples.Controller → FeatureSlot FeatureType.person.Slot
  | .subject => ↑(FeatureType.Slot.ofValue .person ps)
  | .object => ↑(FeatureType.Slot.ofValue .person po)
  | .default => .unvalued

-- (37), (38): in each example the verb shows the features of the argument T agrees with
theorem hindi_example (x : Examples.Example) (ps po : Person) :
    ∀ m ∈ x.marking, ∀ c ∈ x.controller, hindi m.clause ps po = c.slot ps po := by
  revert x ps po; decide

end Amato2025
