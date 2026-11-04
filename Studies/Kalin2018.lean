module

public import Linglib.Data.Examples.Kalin2018
public import Linglib.Syntax.Minimalist.Case.SyntacticObject
public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Order.Minimal
public import Linglib.Data.Examples.Readers

/-!
# Kalin (2018): Licensing and Differential Object Marking

This file formalizes [kalin-2018], which derives differential object marking from nominal
licensing rather than from object visibility, raising or differentiation. Two parameters
interact: which nominals require licensing, in Senaya only the specific ones, and where the
licensers are, every clause carrying an obligatory licenser that licenses the closest nominal
whatever its needs, and secondary licensers that merge only when the derivation would otherwise
crash, the Licensing Economy Principle, (36). In Senaya the marking is verbal agreement: in the
imperfective, Asp is the obligatory licenser and agrees with the subject as an S-suffix, and T is
a secondary licenser that agrees with a specific object as an L-suffix, (43) and (47); in the
perfective, Asp is no licenser and T is obligatory, so T agrees with the subject and a specific
object cannot be licensed at all, (49) and (50), the ban of (12). The licensing derivation
reproduces the agreement data (8) to (12) and (38) whatever the specificity of the subject
(`rows_agree`), and the toy nominative-accusative language of §3.1 shows differential marking by
a secondary v (`toy_animate_object`, `toy_inanimate_object`). The perfective ban is the paper's
argument against a theory without licensing: the dependent-case rules of [marantz-1991] value the
perfective object accusative, but a specific object there crashes
(`dependentCase_values_banned_object`).

The theory is formalized first. Every nominal bears a Case feature, unvalued unless a lexical
head has valued it, so every nominal is visible to a licenser; only some bear *uninterpretable*
Case ([pesetsky-torrego-2007]), and those alone crash the derivation when it goes unvalued. A
licenser is a head with a φ-probe that Agrees with the highest nominal in the phase domain it
probes whose Case is unvalued, the Agree of `Minimalist.agree`, and a secondary licenser
merges only as a last resort ([rezac-2011]). The derivation never sees which nominals need
licensing, since it runs on positions alone, and needs are read only by convergence. Licensing
is monotone in the licensers (`license_mono`), so the Licensing Economy Principle stated for each
secondary licenser coincides with the preference for a derivation with fewer licensers
(`economical_iff`). Licensing is the Agree modality of case assignment of
[baker-vinokurova-2010]: case assigners with no dependent or elsewhere case assign exactly what
the licensing derivation does (`assign_eq_map_license`), and read off Senaya's clauses and the toy
language's, whose phase heads place the nominals, case under the licensers values what licensing
does (`senayaCases_eq_license`, `toyCases_eq_license`).

## Implementation notes

* The agreement suffix is read off the licensing head, the S-suffix from Asp and the L-suffix
  from T, the analysis of [kalin-van-urk-2015] that the paper adopts in §4.1.
* In Senaya v is not a phase head (§4.1), so both arguments are in the domain T and Asp probe;
  in the toy language the object is in the domain of v, which the subject is not.
* Nominals are listed from the highest down; the licensers probing one phase domain are listed in
  merge order, the lowest first, and the domains spell out in the order given.
* Only structural licensing under c-command is modelled: an inherent licenser that values only
  its specifier is not.
* Word order and the position of agreement within the verbal complex are not modelled.

## References

* [kalin-2018]
* [kalin-van-urk-2015]
* [pesetsky-torrego-2007]
* [rezac-2011]
* [baker-vinokurova-2010]
* [marantz-1991]
-/

@[expose] public section

namespace Kalin2018

open Minimalist

section Licensing

open List

/-! ### Licensers and nominals -/

/-- Whether a licenser merges in every derivation or only as a last resort. -/
inductive LicenserKind where
  | obligatory
  | secondary
  deriving DecidableEq, Repr

/-- A licenser: a head with a φ-probe, the phase whose domain it probes, and whether it merges in
every derivation. -/
structure Licenser where
  head : Cat
  domain : Cat := .C
  kind : LicenserKind
  deriving DecidableEq, Repr

/-- A nominal together with whether it bears uninterpretable Case and so needs licensing. -/
structure LicensedNP extends PhasedNP where
  needsLicensing : Bool
  deriving DecidableEq, Repr

/-- What valued a nominal's Case: a lexical head, with the case it assigned, or a licenser. -/
inductive CaseValue where
  | lexical (c : _root_.Case)
  | licenser (l : Licenser)
  deriving DecidableEq, Repr

/-! ### The derivation -/

variable {n : ℕ}

/-- The nominals of a list as their phases, position by position. -/
def phased (nps : List LicensedNP) (j : Fin nps.length) : PhasedNP := nps[j].toPhasedNP

/-- The Case of each nominal before any licenser probes: valued only by a lexical head. -/
def initial (np : Fin n → PhasedNP) (i : Fin n) : FeatureSlot CaseValue :=
  (np i).case.map .lexical

/-- The Agree of licenser `l`. -/
def Licenser.agree (l : Licenser) (np : Fin n → PhasedNP) (st : Fin n → FeatureSlot CaseValue) :
    Fin n → FeatureSlot CaseValue :=
  Minimalist.agree (· < ·) (.licenser l) (Finset.univ.filter fun i ↦ (np i).Visible l.domain) st

/-- The licensers probing the domain of `c` merge, the lowest first. -/
def cycle (ls : List Licenser) (c : Cat) (np : Fin n → PhasedNP)
    (st : Fin n → FeatureSlot CaseValue) : Fin n → FeatureSlot CaseValue :=
  (ls.filter (·.domain == c)).foldl (fun st l ↦ l.agree np st) st

/-- The derivation: the phase domains `ds` spell out in order, each with its licensers. -/
def license (ds : List Cat) (ls : List Licenser) (np : Fin n → PhasedNP) :
    Fin n → FeatureSlot CaseValue :=
  ds.foldl (fun st c ↦ cycle ls c np st) (initial np)

/-- A derivation converges iff every nominal that needs licensing has its Case valued. -/
def Converges (ds : List Cat) (ls : List Licenser) (nps : List LicensedNP) : Prop :=
  ∀ i : Fin nps.length, nps[i].needsLicensing = true → (license ds ls (phased nps) i).value?.isSome

instance (ds : List Cat) (ls : List Licenser) (nps : List LicensedNP) :
    Decidable (Converges ds ls nps) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A nominal is DOM-marked iff a secondary licenser valued its Case. -/
def IsDOMMarked : Option CaseValue → Prop
  | some (.licenser l) => l.kind = .secondary
  | _ => False

instance : DecidablePred IsDOMMarked
  | some (.licenser l) => inferInstanceAs (Decidable (l.kind = .secondary))
  | some (.lexical _) | none => inferInstanceAs (Decidable False)

section Derivation

variable {l : Licenser} {ds : List Cat} {ls ls' : List Licenser} {nps : List LicensedNP}
  {np : Fin n → PhasedNP} {i : Fin n}

theorem extends_license (ds : List Cat) (ls : List Licenser) (np : Fin n → PhasedNP) :
    FeatureSlot.Extends {v | ∀ l, v = .licenser l → l ∈ ls} (initial np) (license ds ls np) := by
  have hstep (l : Licenser) (hl : l ∈ ls) (st : Fin n → FeatureSlot CaseValue) :
      FeatureSlot.Extends {v | ∀ l, v = .licenser l → l ∈ ls} st (l.agree np st) :=
    Minimalist.extends_agree.mono <| Set.singleton_subset_iff.2 <| by
      intro l' hl'
      cases hl'
      exact hl
  exact FeatureSlot.Extends.foldl _ (fun c _ st ↦ FeatureSlot.Extends.foldl _
    (fun l hl st ↦ hstep l (mem_of_mem_filter hl) st) st) _

theorem mem_of_license (h : license ds ls np i = .valued (.licenser l)) : l ∈ ls := by
  rcases (extends_license ds ls np).of_valued h with h | h
  · obtain ⟨_, -, hc⟩ := FeatureSlot.map_eq_valued_iff.1 h
    cases hc
  · exact h l rfl

/-! ### Monotonicity -/

private theorem unvalued_foldl_agree :
    ∀ {L L' : List Licenser}, L <+ L' → ∀ {s t : Fin n → FeatureSlot CaseValue},
      (∀ x, t x = .unvalued → s x = .unvalued) → ∀ x,
      L'.foldl (fun st l ↦ l.agree np st) t x = .unvalued →
        L.foldl (fun st l ↦ l.agree np st) s x = .unvalued
  | _, _, .slnil, _, _, h => h
  | _, _, .cons l hL, _, _, h => unvalued_foldl_agree hL fun x hx ↦ h x
    (Minimalist.extends_agree.unvalued hx)
  | _, _, .cons_cons l hL, _, _, h => unvalued_foldl_agree hL fun _ ↦
    Minimalist.agree_eq_unvalued_of_forall h

private theorem unvalued_foldl_cycle (h : ls <+ ls') (np : Fin n → PhasedNP) (ds : List Cat) :
    ∀ {s t : Fin n → FeatureSlot CaseValue}, (∀ x, t x = .unvalued → s x = .unvalued) → ∀ x,
      ds.foldl (fun st c ↦ cycle ls' c np st) t x = .unvalued →
        ds.foldl (fun st c ↦ cycle ls c np st) s x = .unvalued := by
  induction ds with
  | nil => exact id
  | cons c ds ih => exact fun hst ↦ ih (unvalued_foldl_agree (h.filter _) hst)

/-- Licensing is monotone in the licensers: what more licensers leave unvalued, fewer do. -/
theorem license_mono (h : ls <+ ls') (ds : List Cat) (np : Fin n → PhasedNP) (i : Fin n)
    (hi : license ds ls' np i = .unvalued) : license ds ls np i = .unvalued :=
  unvalued_foldl_cycle h np ds (fun _ h ↦ h) i hi

theorem Converges.mono (hc : Converges ds ls nps) (h : ls <+ ls') : Converges ds ls' nps := by
  intro i hn
  have hv := hc i hn
  cases hl : license ds ls' (phased nps) i with
  | valued v => rfl
  | unvalued => simp [license_mono h ds _ i hl] at hv
  | absent =>
    have hi := (extends_license ds ls' (phased nps)).eq_absent_iff.2 hl
    simp [(extends_license ds ls (phased nps)).eq_absent_iff.1 hi] at hv

theorem converges_of_forall_needsLicensing_eq_false
    (h : ∀ np ∈ nps, np.needsLicensing = false) : Converges ds ls nps :=
  fun i hn ↦ by simp [h _ (List.getElem_mem i.2)] at hn

end Derivation

/-! ### The Licensing Economy Principle -/

section Economy

variable {ds : List Cat} {ls : List Licenser} {nps : List LicensedNP} {S : Finset Licenser}

/-- The licensers of a clause when the secondaries in `S` are activated: the obligatory ones
and the activated ones, in place. -/
def activate (ls : List Licenser) (S : Finset Licenser) : List Licenser :=
  ls.filter fun l ↦ decide (l.kind = .obligatory ∨ l ∈ S)

/-- An activation is economical iff it converges and no activation of fewer licensers does: the
derivation with fewer licensers is preferred. -/
def Economical (ds : List Cat) (ls : List Licenser) (nps : List LicensedNP)
    (S : Finset Licenser) : Prop :=
  Minimal (fun S ↦ Converges ds (activate ls S) nps) S

theorem activate_sublist (ls : List Licenser) (S : Finset Licenser) : activate ls S <+ ls :=
  filter_sublist

theorem monotone_converges_activate (ds : List Cat) (ls : List Licenser)
    (nps : List LicensedNP) : Monotone fun S ↦ Converges ds (activate ls S) nps :=
  fun _ _ hS hc ↦ hc.mono <| monotone_filter_right _ fun _ ↦ by simpa using Or.imp_right (@hS _)

/-- An activation is economical iff it converges and no activated secondary licenser can be dropped,
the Licensing Economy Principle ((36) of [kalin-2018]). -/
theorem economical_iff : Economical ds ls nps S ↔
    Converges ds (activate ls S) nps ∧ ∀ l ∈ S, ¬ Converges ds (activate ls (S.erase l)) nps :=
  Finset.minimal_iff_forall_erase fun _ _ h hts ↦ monotone_converges_activate ds ls nps hts h

instance : Decidable (Economical ds ls nps S) := decidable_of_iff' _ economical_iff

theorem Economical.mem (h : Economical ds ls nps S) {l : Licenser} (hl : l ∈ S) :
    l ∈ ls ∧ l.kind = .secondary := by
  rw [economical_iff] at h
  by_contra hs
  have he : activate ls (S.erase l) = activate ls S := filter_congr fun x hx ↦ by
    by_cases hxl : x = l
    · subst hxl
      cases hk : x.kind <;> simp_all
    · simp [hxl]
  exact h.2 l hl (he ▸ h.1)

theorem Economical.subset_toFinset (h : Economical ds ls nps S) : S ⊆ ls.toFinset :=
  fun _ hl ↦ mem_toFinset.2 (h.mem hl).1

theorem exists_economical_iff : (∃ S, Economical ds ls nps S) ↔ Converges ds ls nps := by
  refine ⟨fun ⟨S, h⟩ ↦ (Minimal.prop h).mono (activate_sublist _ _), fun h ↦ ?_⟩
  refine exists_minimal_of_wellFoundedLT _ ⟨ls.toFinset, ?_⟩
  rwa [activate, filter_eq_self.2 fun l hl ↦ by simp [mem_toFinset.2 hl]]

theorem Economical.eq_empty (h : Economical ds ls nps S)
    (h₀ : Converges ds (activate ls ∅) nps) : S = ∅ :=
  (Minimal.eq_of_le h h₀ (Finset.empty_subset S)).symm

theorem Economical.not_isDOMMarked (h : Economical ds ls nps S)
    (h₀ : Converges ds (activate ls ∅) nps) (i : Fin nps.length) :
    ¬ IsDOMMarked (license ds (activate ls S) (phased nps) i).value? := by
  intro hdom
  cases hk : license ds (activate ls S) (phased nps) i with
  | valued v =>
    cases v with
    | lexical _ => simp [hk, IsDOMMarked] at hdom
    | licenser l =>
      simp only [hk, FeatureSlot.value?_valued, IsDOMMarked] at hdom
      have hl := mem_of_license hk
      simp [h.eq_empty h₀, activate, hdom] at hl
  | _ => simp [hk, IsDOMMarked] at hdom

end Economy

/-! ### Licensing as the Agree modality of case assignment -/

/-- The case and mechanism a Case value amounts to: the lexical case, or under Agree the case
`κ` gives the licensing head. -/
def CaseValue.assigned (κ : Cat → _root_.Case) :
    CaseValue → _root_.Case × _root_.Case.Mechanism
  | .lexical c => (c, .lexical)
  | .licenser l => (κ l.head, .functional)

theorem assign_eq_map_license (g : CaseAssigners) (ds : List Cat) (hg : ∀ c ∈ ds, g.rules c = {})
    (κ : Cat → _root_.Case) {ls : List Licenser}
    (hκ : ∀ l ∈ ls, g.agreeCase l.head = some (κ l.head)) (np : Fin n → PhasedNP) (i : Fin n) :
    g.assign .univ np (· < ·) (ls.map fun l ↦ (l.head, l.domain)) ds i =
      (license ds ls np i).map (CaseValue.assigned κ) := by
  let φ (st : Fin n → FeatureSlot CaseValue) (x : Fin n) :
      FeatureSlot (_root_.Case × _root_.Case.Mechanism) := (st x).map (CaseValue.assigned κ)
  let dom := g.domain .univ np (fun a b : Fin n ↦ a < b) (ls.map fun l ↦ (l.head, l.domain))
  have key (c : Cat) (L : List Licenser)
      (hL : ∀ l ∈ L, l.domain = c ∧ g.agreeCase l.head = some (κ l.head))
      (st : Fin n → FeatureSlot CaseValue) :
      ((L.map fun l ↦ (l.head, l.domain)).filterMap fun pr ↦
          (g.agreeCase pr.1).map fun k ↦
            ((k, _root_.Case.Mechanism.functional),
              Finset.univ.filter fun x ↦ (np x).Visible c)).foldl
        (fun st p ↦ Minimalist.agree (fun a b : Fin n ↦ a < b) p.1 p.2 st) (φ st) =
        φ (L.foldl (fun st l ↦ l.agree np st) st) := by
    induction L generalizing st with
    | nil => rfl
    | cons l L ih =>
      obtain ⟨hdom, hcase⟩ := hL l (mem_cons_self ..)
      have hstep : Minimalist.agree (fun a b : Fin n ↦ a < b) (κ l.head, .functional)
          (Finset.univ.filter fun x ↦ (np x).Visible c) (φ st) = φ (l.agree np st) := by
        funext x
        simp only [φ, Licenser.agree, hdom]
        exact (Minimalist.map_agree (lt := fun a b : Fin n ↦ a < b) (v := .licenser l)
          (CaseValue.assigned κ) x).symm
      rw [map_cons, filterMap_cons, hcase, Option.map_some, foldl_cons, foldl_cons, hstep,
        ih (fun l hl ↦ hL l (mem_cons_of_mem _ hl))]
  have hcycle (c : Cat) (hc : c ∈ ds) (st : Fin n → FeatureSlot CaseValue) :
      (dom c).pass (φ st) = φ (cycle ls c np st) := by
    have hr := hg c hc
    simp only [dom, CaseAssigners.domain, CaseDomain.pass]
    rw [DependentCase.Rules.elsewhere_pass_of_eq_none (by simp [hr]),
      DependentCase.Rules.dependent_pass_of_eq_none (by simp [hr]) (by simp [hr]),
      CaseAssigners.probesIn, filter_map, cycle]
    exact key c _ (fun l hl ↦ by
      obtain ⟨hl, hc⟩ := mem_filter.1 hl
      exact ⟨by simpa using hc, hκ l hl⟩) st
  have hinit : _root_.Case.lexical (fun x ↦ (np x).case) = φ (initial np) := by
    funext x
    simp only [_root_.Case.lexical, φ, initial]
    cases (np x).case <;> rfl
  suffices ∀ ds' ⊆ ds, ∀ st : Fin n → FeatureSlot CaseValue, assignBy (ds'.map dom) (φ st) =
      φ (ds'.foldl (fun st c ↦ cycle ls c np st) st) by
    change assignBy (ds.map dom) _ i = _
    rw [hinit, this ds (fun _ h ↦ h) (initial np)]
    rfl
  intro ds' hds' st
  induction ds' generalizing st with
  | nil => rfl
  | cons c ds' ih =>
    have := ih (fun c hc ↦ hds' (mem_cons_of_mem _ hc)) (cycle ls c np st)
    simp only [assignBy, map_cons, foldl_cons] at this ⊢
    rw [hcycle c (hds' mem_cons_self) st, this]

end Licensing

/-! ### Senaya's licensers -/

/-- Imperfective Asp, the obligatory licenser of the imperfective, (43). -/
def aspImpf : Licenser := { head := .Asp, kind := .obligatory }

/-- The T selecting imperfective Asp, a secondary licenser, (43). -/
def tImpf : Licenser := { head := .T, kind := .secondary }

/-- The T selecting perfective Asp, the one obligatory licenser of the perfective, (49). -/
def tPfv : Licenser := { head := .T, kind := .obligatory }

/-- The imperfective's licensers in merge order: Asp, then T. -/
def imperfective : List Licenser := [aspImpf, tImpf]

/-- The perfective's licenser: T alone. -/
def perfective : List Licenser := [tPfv]

/-- The one phase domain of a Senaya clause, v being no phase head. -/
def domains : List Cat := [.C]

/-- The agreement suffix a licensing head yields, an S-suffix from Asp and an L-suffix from T. -/
inductive Suffix
  | S
  | L
  deriving DecidableEq, Repr

/-- The suffix agreement with a head yields. -/
def headSuffix : Cat → Option Suffix
  | .Asp => some .S
  | .T => some .L
  | _ => none

/-- The suffix of a nominal's Case value: that of the head that licensed it, if any. -/
def suffixOf : Option CaseValue → Option Suffix
  | some (.licenser l) => headSuffix l.head
  | _ => none

/-- A Senaya nominal, which needs licensing exactly when specific, (40) to (42). -/
def nominal (specific : Bool) : LicensedNP := { needsLicensing := specific }

/-- A transitive clause's subject and object. -/
def transitive (subject object : Bool) : List LicensedNP :=
  [nominal subject, nominal object]

/-! ### The agreement data (Section 2.1) -/

/-- A row carries the aspect's licensers, the object if any, the subject's and the object's
suffix, and the judgment. -/
structure Row where
  clause : List Licenser
  object : Option Bool
  subjectSuffix : Suffix
  objectSuffix : Option Suffix
  grammatical : Bool

/-- A suffix feature value. -/
def suffixFeature : String → Option (Option Suffix)
  | "S" => some (some .S)
  | "L" => some (some .L)
  | "none" => some none
  | _ => none

/-- A row from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let cl ← match e.feature? "aspect" with
    | some "imperfective" => some imperfective
    | some "perfective" => some perfective
    | _ => none
  let obj ← match e.feature? "object" with
    | some "specific" => some (some true)
    | some "nonspecific" => some (some false)
    | some "none" => some none
    | _ => none
  let s ← (e.feature? "subject_suffix").bind suffixFeature
  let s ← s
  let o ← (e.feature? "object_suffix").bind suffixFeature
  some ⟨cl, obj, s, o, e.judgment = .acceptable⟩

/-- The Senaya data, (8) to (12) and (38). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The nominals of a row: a subject of the given specificity, and the row's object if any. -/
def Row.nominals (r : Row) (subject : Bool) : List LicensedNP :=
  nominal subject :: (r.object.map nominal).toList

/-- The suffixes of a row: the subject's, then the object's if there is an object. -/
def Row.suffixes (r : Row) : List (Option Suffix) :=
  some r.subjectSuffix :: (r.object.map fun _ ↦ r.objectSuffix).toList

/-- The suffixes a derivation spells out, nominal by nominal. -/
def suffixes {n : ℕ} (st : Fin n → FeatureSlot CaseValue) : List (Option Suffix) :=
  List.ofFn fun i ↦ suffixOf (st i).value?

private theorem rows_agree_aux : ∀ r ∈ rows, ∀ subject : Bool,
    (r.grammatical = true ↔ Converges domains r.clause (r.nominals subject)) ∧
    ∀ S ∈ r.clause.toFinset.powerset, Economical domains r.clause (r.nominals subject) S →
      suffixes (license domains (activate r.clause S) (phased (r.nominals subject))) =
        r.suffixes := by
  decide

theorem rows_agree : ∀ r ∈ rows, ∀ subject : Bool,
    (r.grammatical = true ↔ ∃ S, Economical domains r.clause (r.nominals subject) S) ∧
    ∀ S, Economical domains r.clause (r.nominals subject) S →
      suffixes (license domains (activate r.clause S) (phased (r.nominals subject))) =
        r.suffixes := by
  intro r hr subject
  obtain ⟨h₁, h₂⟩ := rows_agree_aux r hr subject
  exact ⟨h₁.trans exists_economical_iff.symm,
    fun S hS ↦ h₂ S (Finset.mem_powerset.2 hS.subset_toFinset) hS⟩

-- (47), (48)
theorem imperfective_object (subject : Bool) :
    Economical domains imperfective (transitive subject true) {tImpf} ∧
      List.ofFn
          (license domains (activate imperfective {tImpf}) (phased (transitive subject true))) =
        [.valued (.licenser aspImpf), .valued (.licenser tImpf)] ∧
    Economical domains imperfective (transitive subject false) ∅ ∧
      List.ofFn (license domains (activate imperfective ∅) (phased (transitive subject false))) =
        [.valued (.licenser aspImpf), .unvalued] := by
  cases subject <;> decide

/-! ### The toy language of Section 3.1 -/

/-- Finite T, the obligatory licenser of the toy language. -/
def toyT : Licenser := { head := .T, kind := .obligatory }

/-- v, a secondary licenser probing its own domain. -/
def toyV : Licenser := { head := .v, domain := .v, kind := .secondary }

/-- The toy language's licensers. -/
def toy : List Licenser := [toyV, toyT]

/-- The toy language's phase domains, v's spelling out before C's. -/
def toyDomains : List Cat := [.v, .C]

/-- A transitive clause of the toy language, in which a nominal needs licensing exactly when
animate: the subject above v, the object in its domain. -/
def toyTransitive (subject object : Bool) : List LicensedNP :=
  [{ needsLicensing := subject }, { phase := .v, needsLicensing := object }]

/-- An animate object activates v, without which the derivation crashes (24). -/
theorem toy_animate_object (subject : Bool) :
    ¬ Converges toyDomains (activate toy ∅) (toyTransitive subject true) ∧
    Economical toyDomains toy (toyTransitive subject true) {toyV} ∧
      List.ofFn (license toyDomains toy (phased (toyTransitive subject true))) =
        [.valued (.licenser toyT), .valued (.licenser toyV)] := by
  cases subject <;> decide

/-- An inanimate object activates nothing and goes unlicensed and unmarked, (23). -/
theorem toy_inanimate_object (subject : Bool) :
    Economical toyDomains toy (toyTransitive subject false) ∅ ∧
      List.ofFn (license toyDomains (activate toy ∅) (phased (toyTransitive subject false))) =
        [.valued (.licenser toyT), .unvalued] := by
  cases subject <;> decide

/-! ### Positions read off derivations

Senaya's clause is a schematic derivation whose only phase head is C, v being none (§4.1), and
the toy language's has v and C; the licensers are the heads whose domain they probe, deepest
first. Read off these derivations, case assignment under the licensers values what licensing
does on the nominals placed by hand. -/

/-- Schematic heads: subject and object nominals, a transitive and an intransitive verb, v, Asp,
T and C. -/
def subjD : LexicalItem.Token := ⟨.of .D [], 1⟩
@[inherit_doc subjD] def objD : LexicalItem.Token := ⟨.of .D [], 2⟩
@[inherit_doc subjD] def verb : LexicalItem.Token := ⟨.of .V [.D], 3⟩
@[inherit_doc subjD] def verb₀ : LexicalItem.Token := ⟨.of .V [], 4⟩
@[inherit_doc subjD] def littleV : LexicalItem.Token := ⟨.of .v [.V], 5⟩
@[inherit_doc subjD] def asp : LexicalItem.Token := ⟨.of .Asp [.v], 6⟩
@[inherit_doc subjD] def tense : LexicalItem.Token := ⟨.of .T [.Asp], 7⟩
@[inherit_doc subjD] def comp : LexicalItem.Token := ⟨.of .C [.T], 8⟩

/-- A clause with an object or without, the subject in the specifier of vP. -/
def clause (object : Bool) : Derivation :=
  if object then
    ⟨verb, [.em .left objD, .em .right littleV, .em .left subjD, .em .right asp,
      .em .right tense, .em .right comp]⟩
  else
    ⟨verb₀, [.em .right littleV, .em .left subjD, .em .right asp, .em .right tense,
      .em .right comp]⟩

/-- The nominals of a clause, highest first. -/
def clauseNominals (object : Bool) : List LexicalItem.Token :=
  if object then [subjD, objD] else [subjD]

/-- A label for the case each licensing head values, telling Asp's from T's; the cases chosen are
arbitrary. -/
def headCase : Cat → _root_.Case
  | .Asp => .nom
  | _ => .acc

/-- Case assignment under licensers `ls`: no dependent rules, and each licensing head values its
label under Agree. -/
def underLicensers (ls : List Licenser) : CaseAssigners where
  agreeCase c := if ls.any (·.head == c) then some (headCase c) else none

/-- Case read off a clause under licensers `ls`, C the only phase head. -/
def senayaCases (ls : List Licenser) (object : Bool) :
    Option (List (FeatureSlot (_root_.Case × _root_.Case.Mechanism))) :=
  (clause object).externalize?.map fun t ↦
    (clauseNominals object).map
      ((underLicensers ls).assignOn .raising t (complementDomain .raising t ∅) (·.item.cat = .C)
        (fun _ ↦ .unvalued) (clauseNominals object))

/-- Read off Senaya's clauses, case under each activation of the licensers values what licensing
does on the nominals placed by hand in the one phase domain. -/
theorem senayaCases_eq_license (object : Bool) :
    ∀ ls ∈ [activate imperfective ∅, activate imperfective {tImpf}, perfective],
      senayaCases ls object = some (List.ofFn fun i ↦
        (license domains ls (fun _ : Fin (clauseNominals object).length ↦ {}) i).map
          (CaseValue.assigned headCase)) := by
  cases object <;> decide +kernel

/-- Case read off a toy clause, v and C its phase heads. -/
def toyCases (ls : List Licenser) :
    Option (List (FeatureSlot (_root_.Case × _root_.Case.Mechanism))) :=
  (clause true).externalize?.map fun t ↦
    (clauseNominals true).map
      ((underLicensers ls).assignOn .raising t (complementDomain .raising t ∅)
        (fun a ↦ a.item.cat = .v ∨ a.item.cat = .C) (fun _ ↦ .unvalued) (clauseNominals true))

/-- Read off the toy language's transitive clause, case under each activation values what
licensing does on the object placed by hand in the domain of v. -/
theorem toyCases_eq_license :
    ∀ ls ∈ [activate toy ∅, toy],
      toyCases ls = some (List.ofFn fun i ↦
        (license toyDomains ls (phased (toyTransitive false false)) i).map
          (CaseValue.assigned headCase)) := by
  decide +kernel

/-! ### Licensing against dependent case -/

/-- Dependent case values a specific perfective object accusative, but licensing leaves it unvalued
and the derivation crashes (Section 2.1.3). -/
theorem dependentCase_values_banned_object (subject : Bool) :
    ((DependentCase.Rules.ofAlignment .accusative).pass (· < ·) .univ
      (_root_.Case.lexical fun j : Fin 2 ↦ (phased (transitive subject true) j).case)
      1).value?.map (·.1) = some .acc ∧
    ¬ Converges domains perfective (transitive subject true) := by
  cases subject <;> decide

end Kalin2018
