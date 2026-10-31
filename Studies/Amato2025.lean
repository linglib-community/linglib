module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Case.Alignment
public import Linglib.Syntax.Minimalist.Feature.Valuation
public import Linglib.Syntax.Minimalist.Probe.Agree
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection

/-!
# Amato (2025): Nested Agree and apparent minimality violations

Amato derives apparent minimality violations from *Nested Agree*
(Definition (1)): the probes on a head are extrinsically ordered, and a later
probe must exploit the dependency an earlier one established, so its search
starts from the earlier probe's goal — everything the head c-commands above
that goal lies outside its domain, and a structurally closer matching goal is
skipped with minimality respected at every step. `run` is that engine on the
substrate's `FeatureState.probe` and `FeatureState.agree`: a probe's domain is the
c-command-ordered list of accessible heads (the paper's own notation in (6),
(8), (32), (34)), read off a projection spine by `domain`, which stops at a
phase head's complement (PIC); a valued probe (a case assigner, `[∗Infl:perf∗]`)
matches only an unvalued slot and values its goal, an unvalued probe matches
any specified slot and is valued by an active goal (fn. 23, defective
intervention). Since valuation only adds features, [a run extends the state](##le_run).

The paper's derivations then run as stated: Standard Italian auxiliary
selection ((9)–(20), over the substrate's `TransitivityClass` and impersonal/passive
`Voice.Flavor`) under the Vocabulary Items (14), the Ariellese and Tufillese orderings and entries
(22)–(24), the ditransitive case/agreement alignments (25)–(28) with
Bárány's typological gap, Icelandic DAT-NOM (29a/b), Lak perfective
agreement (32), Spanish VOS (34), Bulgarian multiple wh-fronting (36), and
Hindi-Urdu (38)–(40). Out of scope: Merge and binding inside v's cycle (the SCC
ordering of (16)–(17) enters as v's input), participle agreement (§4.3.2), and
the Appendix's comparison with MME, Multitasking and ECoMPS.

## References

* [amato-2025]
* [barany-2024]
-/

@[expose] public section

namespace Amato2025

open Minimalist
open Minimalist.FeatureBundle (ofList)
open ArgumentStructure (TransitivityClass)
open Verb (PerfectAuxiliary)
open Alignment (IsIndirective IsSecundative)

variable {H : Type*} [DecidableEq H]

/-! ### The engine -/

/-- A projection has its specifiers, highest first, over its head. -/
structure Layer (H : Type*) where
  specs : List H
  head : H

/-- The heads a probe above these projections can reach, in c-command order — each
projection's specifiers then its head, down to and including the first phase head,
whose complement the PIC freezes. -/
def domain (phase : H → Bool) : List (Layer H) → List H
  | [] => []
  | l :: ls => l.specs ++ l.head :: (if phase l.head then [] else domain phase ls)

variable (act : H → FeatureType → Prop) [∀ h t, Decidable (act h t)]

/-- Discharge the probes on `α` in their extrinsic order over `dom` (Definition (1)).
Each probe searches for its closest matching goal from the previous probe's goal on —
reusing that "Agree-channel", so what `α` c-commands above it is outside the search —
and from the top of `dom` when the previous probe found no goal (§4.1.2). A goal that `act`
marks inactive at a dimension is matched without valuing (fn. 23). Returns each probe's goal and
the resulting state. -/
def run (α : H) (dom : List H) (ts : List FeatureType) (s : FeatureState H) :
    List (Option H) × FeatureState H :=
  go none ts s
where
  go : Option H → List FeatureType → FeatureState H → List (Option H) × FeatureState H
  | _, [], s => ([], s)
  | prev, t :: ts, s =>
    let r := (s.probe α t (act · t)).agree (fun g s ↦ s.agree α t g) s
      (prev.elim dom fun β ↦ dom.dropWhile fun x ↦ decide (x ≠ β))
    let rest := go r.satisfier ts r.state
    (r.satisfier :: rest.1, rest.2)

theorem le_run (α : H) (dom : List H) (ts : List FeatureType) (s : FeatureState H) :
    s ≤ (run act α dom ts s).2 := by
  suffices ∀ prev s, s ≤ (run.go act α dom prev ts s).2 from this none s
  induction ts with
  | nil => exact fun _ _ ↦ le_rfl
  | cons t ts ih => exact fun _ s ↦ (s.le_agree_state α t _ _).trans (ih _ _)

theorem nestedDomain {pre post : List H} {β : H} (hβ : β ∉ pre) :
    (pre ++ β :: post).dropWhile (fun x ↦ decide (x ≠ β)) = β :: post := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    have ha : a ≠ β := fun h ↦ hβ (h ▸ List.mem_cons.2 (Or.inl rfl))
    simpa [ha] using ih fun h ↦ hβ (List.mem_cons_of_mem _ h)

-- (2), (3)
theorem notMem_nestedDomain {pre post : List H} {β δ : H}
    (hnd : (pre ++ β :: post).Nodup) (hδ : δ ∈ pre) :
    δ ∉ (pre ++ β :: post).dropWhile (fun x ↦ decide (x ≠ β)) := by
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.1 hnd
  rw [nestedDomain fun h ↦ hdisj β h β (List.mem_cons.2 (Or.inl rfl)) rfl]
  exact fun h ↦ hdisj δ hδ δ h rfl

/-- Under Multiple Agree `[∗wh∗]` reaches every matching goal in c-command order (§4.2.3). -/
def multipleAgree (s : FeatureState H) (α : H) (t : FeatureType) (dom : List H) : List H :=
  dom.filter fun g ↦ decide (s.Matches α t g)

/-- In (36) the Merge feature `[·wh·]`, nested under the last goal of `[∗wh∗]`, raises it first, and
each later application, its landing site being above the probe, searches the remaining domain
afresh. The result lists the movers in order of movement. -/
def whFronting (s : FeatureState H) (α : H) (dom : List H) : List H :=
  let p := Probe.relativized (s.Matches α .wh)
  match (multipleAgree s α .wh dom).getLast? with
  | none => []
  | some β =>
    (p.search (dom.dropWhile fun x ↦ decide (x ≠ β))).toList ++ rest p dom.length (dom.erase β)
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
def isPhase : Head → Bool
  | .v | .voice => true
  | _ => false

/-- Every goal values its probe. -/
def AllActive : Head → FeatureType → Prop := fun _ _ ↦ True

instance (h : Head) (t : FeatureType) : Decidable (AllActive h t) := inferInstanceAs (Decidable True)

/-- `[ϕ:p]`. -/
def person (p : Person) : Σ t : FeatureType, FeatureSlot t.Value := ⟨.person, .valued p⟩

/-! ### Standard Italian auxiliary selection (§3)

Perf bears `[∗Infl:perf∗]` and `[∗π:_∗]`, ordered as in (7) or (22). v first runs its own
cycle over the object ((9), (16)); Perf then probes the vP, T the PerfP (11). -/

/-- The paper has two Voice heads, Voice_imp of the impersonal *si* (§3.4.4) and Voice_pass (fn.
18), both `Minimalist.Voice.passive`'s cell, an implicit external argument. -/
inductive VoiceHead where
  | impersonal
  | passive
  deriving DecidableEq, Repr

/-- A clause of §3.4 has v's class (`TransitivityClass`; an unergative verb is transitive with a
covert cognate object bearing default features, fn. 10) under no Voice head, or under Voice_imp
(§3.4.4) or Voice_pass (fn. 18). -/
structure Clause where
  verb : TransitivityClass
  voice : Option VoiceHead := none
  deriving DecidableEq, Repr

/-- Before Agree, with subject person `p`, Perf bears `[∗Infl:perf∗], [∗π:_∗]`; T `[∗case:nom∗],
[∗ϕ:_∗]`; a transitive v `[Infl:_], [∗case:acc∗], [∗π:_∗]` or, in (15), a defective v `[Infl:_]`;
Voice_imp `[Infl:_], [π:_]` (20), Voice_pass `[Infl:_]`; the subject `[ϕ:p], [case:_]`; a full
object `[ϕ:3], [case:_]` (the unaccusative theme, `[ϕ:p]`), a reflexive object `[ϕ:_], [case:_]`
(16); and *si* `[π:_], [case:_]`. -/
def initial (cl : Clause) (p : Person) : Head → FeatureBundle
  | .perf => ofList [⟨.infl, .valued .perf⟩, ⟨.person, .unvalued⟩]
  | .t => ofList [⟨.case, .valued .nom⟩, ⟨.person, .unvalued⟩]
  | .v =>
    match cl.verb with
    | .unaccusative => ofList [⟨.infl, .unvalued⟩]
    | _ => ofList [⟨.infl, .unvalued⟩, ⟨.case, .valued .acc⟩,
        ⟨.person, .unvalued⟩]
  | .voice =>
    match cl.voice with
    | some .impersonal =>
      ofList [⟨.infl, .unvalued⟩, ⟨.person, .unvalued⟩]
    | some .passive => ofList [⟨.infl, .unvalued⟩]
    | _ => ⊥
  | .si => ofList [⟨.person, .unvalued⟩, ⟨.case, .unvalued⟩]
  | .dpSbj => ofList [person p, ⟨.case, .unvalued⟩]
  | .dpObj =>
    match cl.verb with
    | .reflexive => ofList [⟨.person, .unvalued⟩, ⟨.case, .unvalued⟩]
    | .unaccusative => ofList [person p, ⟨.case, .unvalued⟩]
    | _ => ofList [person .third, ⟨.case, .unvalued⟩]
  | _ => ⊥

/-- The projections below Perf are (10)/(18) for a transitive v and (15) for a defective one, under
the Voice layer of (20) when there is one. -/
def perfSpine (cl : Clause) : List (Layer Head) :=
  (match cl.voice with
    | some .impersonal => [⟨[.si], .voice⟩]
    | some _ => [⟨[], .voice⟩]
    | none => []) ++
  match cl.verb with
  | .unaccusative => [⟨[.dpObj], .v⟩, ⟨[], .verb⟩]
  | _ => [⟨[.dpSbj], .v⟩, ⟨[], .verb⟩, ⟨[], .dpObj⟩]

/-- In v's cycle ((9), (16)) v assigns accusative and then π-agrees with the object; a defective v
does neither. -/
def afterV (cl : Clause) (p : Person) : FeatureState Head :=
  (run AllActive .v [.verb, .dpObj] (if cl.verb = .unaccusative then [] else [.case, .person])
    (initial cl p)).2

/-- Perf's cycle under the feature ordering `ord`. -/
def perfCycle (ord : List FeatureType) (cl : Clause) (p : Person) :
    List (Option Head) × FeatureState Head :=
  run AllActive .perf (domain isPhase (perfSpine cl)) ord (afterV cl p)

/-- In T's cycle (11) T assigns nominative and then ϕ-agrees. -/
def tCycle (ord : List FeatureType) (cl : Clause) (p : Person) :
    List (Option Head) × FeatureState Head :=
  run AllActive .t (domain isPhase (⟨[], .perf⟩ :: perfSpine cl)) [.case, .person]
    (perfCycle ord cl p).2

/-- The state after v, Perf and T have probed. -/
def derive (ord : List FeatureType) (cl : Clause) (p : Person) : FeatureState Head :=
  (tCycle ord cl p).2

/-- Standard Italian orders its probes by argument structure, Infl before person (7). -/
def standardItalian : List FeatureType := [.infl, .person]

/-- Ariellese orders its probes by the subject, person before Infl (22). -/
def ariellese : List FeatureType := [.person, .infl]

/-- In Perf's domain in (10) the subject is c-commanded first, then v. -/
example : domain isPhase (perfSpine ⟨.transitive, none⟩) = [.dpSbj, .v] := rfl

-- (10), (18)
theorem perf_targets_v (c : TransitivityClass) (hc : c ≠ .unaccusative) (p : Person) :
    (perfCycle standardItalian ⟨c, none⟩ p).1 = [some .v, some .v] := by
  revert c p; decide

-- (15)
theorem perf_unaccusative (p : Person) :
    (perfCycle standardItalian ⟨.unaccusative, none⟩ p).1 = [some .v, none] := by
  revert p; decide

-- (20)
theorem perf_impersonal (c : TransitivityClass) (p : Person) :
    (perfCycle standardItalian ⟨c, some .impersonal⟩ p).1 = [some .voice, some .voice] := by
  revert c p; decide

-- (11)
theorem t_targets_subject (p : Person) :
    (tCycle standardItalian ⟨.transitive, none⟩ p).1 = [some .dpSbj, some .dpSbj] := by
  revert p; decide

/-- The Vocabulary Items (14) insert `/AVERE/ ↔ Perf[π:α]`, and `/ESSERE/` elsewhere. -/
def standardItalianAux (s : FeatureState Head) : PerfectAuxiliary :=
  if (s .perf .person).toFlat ≠ ⊥ then .have else .be

-- (4), (5)
theorem standardItalian_aux (c : TransitivityClass) (p : Person) :
    standardItalianAux (derive standardItalian ⟨c, none⟩ p) = c.canonicalSelection := by
  revert c p; decide

-- (5d), fn. 18
theorem standardItalian_voice (c : TransitivityClass) (f : VoiceHead)
    (hf : f = .impersonal ∨ f = .passive) (p : Person) :
    standardItalianAux (derive standardItalian ⟨c, some f⟩ p) = .be := by
  rcases hf with rfl | rfl <;> (revert c p; decide)

/-- Ariellese (23) inserts `/AVERE/ ↔ Perf[π:-participant]`. -/
def arielleseAux (s : FeatureState Head) : PerfectAuxiliary :=
  if s .perf .person = .valued .third then .have else .be

-- (22), (21), §3.5
theorem ariellese_aux (c : TransitivityClass) (p : Person) :
    arielleseAux (derive ariellese ⟨c, none⟩ p) = if p = .third then .have else .be := by
  revert c p; decide

/-- Tufillese (24) inserts `/AVERE/ ↔ Perf[π:α] / T[ϕ:3sg]`. -/
def tufilleseAux (s : FeatureState Head) : PerfectAuxiliary :=
  if (s .perf .person).toFlat ≠ ⊥ ∧ s .t .person = .valued .third then .have else .be

-- §3.5
theorem tufillese_aux (c : TransitivityClass) (p : Person) :
    tufilleseAux (derive standardItalian ⟨c, none⟩ p) =
      if c.canonicalSelection = .have ∧ p = .third then .have else .be := by
  revert c p; decide

/-! ### Case and agreement in ditransitive clauses (§4.1.1) -/

/-- The two orderings of `[∗case∗]` and `[∗ϕ:_∗]` on a head. -/
inductive ProbeOrder
  | caseFirst | phiFirst
  deriving DecidableEq, Repr, Fintype

/-- The probes on v, in order. -/
def ProbeOrder.probes : ProbeOrder → List FeatureType
  | .caseFirst => [.case, .person]
  | .phiFirst => [.person, .case]

/-- In (25)–(28) v bears `[∗case:acc∗], [∗ϕ:_∗]` over `DP_R … Appl … V … DP_T`, the recipient
already dative from Appl or not. -/
def ditransitiveInitial (applDat : Bool) : Head → FeatureBundle
  | .v => ofList [⟨.case, .valued .acc⟩, ⟨.person, .unvalued⟩]
  | .dpR => ofList
      [person .third, if applDat then ⟨.case, .valued .dat⟩ else ⟨.case, .unvalued⟩]
  | .dpT => ofList [person .third, ⟨.case, .unvalued⟩]
  | _ => ⊥

/-- The derivation of (25)–(28), in which v's probes, in order `o`, search the recipient, Appl, the
verb and the theme. -/
def ditransitive (o : ProbeOrder) (applDat : Bool) : List (Option Head) × FeatureState Head :=
  run AllActive .v [.dpR, .appl, .verb, .dpT] o.probes (ditransitiveInitial applDat)

/-- The goal of v's ϕ-probe. -/
def phiGoal (o : ProbeOrder) (applDat : Bool) : Option Head :=
  match o, (ditransitive o applDat).1 with
  | .caseFirst, [_, a] | .phiFirst, [a, _] => a
  | _, _ => none

/-- The case of each object, the recipient and the theme as the derivation leaves them and P
with the accusative v assigns a transitive object; S and A are not read. -/
def caseMarking (o : ProbeOrder) (applDat : Bool) : ArgumentRole → FeatureSlot Case
  | .R => (ditransitive o applDat).2 .dpR .case
  | .T => (ditransitive o applDat).2 .dpT .case
  | _ => .valued .acc

/-- Whether v ϕ-agrees with each object. It agrees with a transitive object P and with whichever
of the recipient and the theme its ϕ-probe finds; S and A are not read. -/
def agreement (o : ProbeOrder) (applDat : Bool) : ArgumentRole → Bool
  | .R => phiGoal o applDat = some .dpR
  | .T => phiGoal o applDat = some .dpT
  | _ => true

-- (25)
theorem ditransitive_caseFirst_dat :
    IsIndirective (caseMarking .caseFirst true) ∧ IsIndirective (agreement .caseFirst true) ∧
      phiGoal .caseFirst true = some .dpT := by
  decide

-- (26)
theorem ditransitive_caseFirst_noDat :
    IsSecundative (caseMarking .caseFirst false) ∧ IsSecundative (agreement .caseFirst false) := by
  decide

-- (27)
theorem ditransitive_phiFirst_dat :
    IsIndirective (caseMarking .phiFirst true) ∧ IsSecundative (agreement .phiFirst true) := by
  decide

-- (28)
theorem ditransitive_phiFirst_noDat :
    IsSecundative (caseMarking .phiFirst false) ∧ IsSecundative (agreement .phiFirst false) := by
  decide

-- Table 1 [barany-2024]
theorem isIndirective_caseMarking_of_agreement (o : ProbeOrder) (d : Bool) :
    IsIndirective (agreement o d) → IsIndirective (caseMarking o d) := by
  revert o d; decide

/-! ### Icelandic DAT-NOM constructions (§4.1.2) -/

/-- (29a) versus (29b). -/
inductive Clausal
  | monoclausal | biclausal
  deriving DecidableEq, Repr, Fintype

/-- T `[∗case:nom∗], [∗ϕ:_∗]` over `DP_dat … DP_nom`; in (29b) the lower T has already
assigned nominative. -/
def icelandicInitial : Clausal → Head → FeatureBundle
  | _, .t => ofList [⟨.case, .valued .nom⟩, ⟨.number, .unvalued⟩]
  | _, .dpDat => ofList [⟨.number, .valued .plural⟩, ⟨.case, .valued .dat⟩]
  | .monoclausal, .dpNom =>
    ofList [⟨.number, .valued .plural⟩, ⟨.case, .unvalued⟩]
  | .biclausal, .dpNom => ofList [⟨.number, .valued .plural⟩, ⟨.case, .valued .nom⟩]
  | _, _ => ⊥

/-- Datives are defective goals for ϕ-Agree, matched but never valuing. -/
def IcelandicActive (h : Head) (t : FeatureType) : Prop := ¬ (h = .dpDat ∧ t = .number)

instance (h : Head) (t : FeatureType) : Decidable (IcelandicActive h t) :=
  inferInstanceAs (Decidable (¬ _))

/-- The two orderings that coexist on Icelandic T. -/
def icelandicOrder : ProbeOrder → List FeatureType
  | .caseFirst => [.case, .number]
  | .phiFirst => [.number, .case]

/-- T's number slot after probing. -/
def icelandic (k : Clausal) (o : ProbeOrder) : FeatureSlot FeatureType.number.Value :=
  (run IcelandicActive .t [.dpDat, .dpNom] (icelandicOrder o) (icelandicInitial k)).2 .t .number

-- (29a)
theorem icelandic_monoclausal_caseFirst :
    icelandic .monoclausal .caseFirst = .valued .plural := by decide

-- (29a)
theorem icelandic_monoclausal_phiFirst : icelandic .monoclausal .phiFirst = .unvalued := by
  decide

-- (29b)
theorem icelandic_biclausal (o : ProbeOrder) : icelandic .biclausal o = .unvalued := by
  revert o; decide

/-! ### Person agreement in the Lak perfective (§4.2.1) -/

/-- In (32) Asp bears `[∗Infl:perf∗], [∗π:_∗]` and v `[Infl:_], [∗π:_∗]`, with subject person `ps`
and object person `po`. -/
def lakInitial (ps po : Person) : Head → FeatureBundle
  | .asp => ofList [⟨.infl, .valued .perf⟩, ⟨.person, .unvalued⟩]
  | .v => ofList [⟨.infl, .unvalued⟩, ⟨.person, .unvalued⟩]
  | .dpSbj => ofList [person ps]
  | .dpObj => ofList [person po]
  | _ => ⊥

/-- Asp's person slot after v has agreed with the object and Asp with v. -/
def lak (ps po : Person) : FeatureSlot FeatureType.person.Value :=
  let s := (run AllActive .v [.dpObj] [.person] (lakInitial ps po)).2
  (run AllActive .asp (domain isPhase [⟨[.dpSbj], .v⟩, ⟨[], .dpObj⟩]) [.infl, .person] s).2
    .asp .person

-- (31c), (31d)
theorem lak_agrees_with_object (ps po : Person) : lak ps po = .valued po := by
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
def bulgarianDomain : List Head :=
  domain isPhase [⟨[.whSbj], .t⟩, ⟨[.whObj], .v⟩, ⟨[], .verb⟩]

-- (35)
theorem bulgarian_order : whFronting bulgarianInitial .c bulgarianDomain = [.whObj, .whSbj] := by
  decide

/-- Without Multiple Agree the wh-probe's first goal is the subject, the order minimality
alone predicts. -/
example : (Probe.relativized (FeatureState.Matches bulgarianInitial .c .wh)).search bulgarianDomain =
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

/-- The projections below T in (39), (40) and (38b). -/
def hindiSpine : HindiClause → List (Layer Head)
  | .ergSubject => [⟨[.dpSbj], .asp⟩, ⟨[], .v⟩, ⟨[], .verb⟩, ⟨[], .dpObj⟩]
  | .bothMarked => [⟨[.dpSbj, .dpObj], .asp⟩, ⟨[], .v⟩, ⟨[], .verb⟩]
  | .unmarkedSubject => [⟨[], .asp⟩, ⟨[.dpSbj], .v⟩, ⟨[], .verb⟩, ⟨[], .dpObj⟩]

/-- T's person slot after v has probed its complement (empty in (40), the object having
moved, fn. 33) and T has Infl-agreed with Asp and, nested under it, probed for ϕ. -/
def hindi (k : HindiClause) (ps po : Person) : FeatureSlot FeatureType.person.Value :=
  let s := (run AllActive .v (if k = .bothMarked then [] else [.verb, .dpObj]) [.person]
    (hindiInitial k ps po)).2
  (run AllActive .t (domain isPhase (hindiSpine k)) [.infl, .person] s).2 .t .person

-- (37)
theorem hindi_object_agreement (ps po : Person) : hindi .ergSubject ps po = .valued po := by
  revert ps po; decide

-- (38a)
theorem hindi_default_agreement (ps po : Person) : hindi .bothMarked ps po = .unvalued := by
  revert ps po; decide

-- (38b)
theorem hindi_subject_agreement (ps po : Person) :
    hindi .unmarkedSubject ps po = .valued ps := by
  revert ps po; decide

end Amato2025
