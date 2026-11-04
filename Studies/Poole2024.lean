module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Studies.BakerVinokurova2010
public import Linglib.Data.Examples.Poole2024
public import Linglib.Data.Examples.Readers

/-!
# Poole (2024): Dependent-case assignment could be Agree

This file formalizes [poole-2024]'s argument that dependent case, the innovation of
[marantz-1991]'s configurational model, can be assigned by Agree. A head carries the probe stack
(8): a φ-probe relativized to unmarked case, which values on the closest caseless DP and so
records that a second DP is present, followed by a case-assigning probe with the same
relativization, active only once the first is valued and, by the Principle of Minimal
Compliance, blind to the first probe's goal ([rackowski-richards-2005]). Low dependent case
comes from a stack on a head above both DPs, which meets them in c-command order; high
dependent case from a stack on the head that introduces the higher DP, which searches its
complement and then, by specifier–head Agree ([bejar-rezac-2009]), the specifier it merges
with. Either way the stack assigns nothing with fewer than two caseless DPs in its domain and
never marks the DP that unlocked it (`stack_eq_none_of_subsingleton`, `stack_ne_unlocker`).

The stack is itself a case rule: [it marks the DP with exactly one caseless DP met before
it](##assignDep_eq_passUnvalued), where the low dependent rule marks every DP with one or more above
it. So on a two-DP domain the stack assigns exactly what the dependent rule of the configurational
model assigns, low or high, whatever lexical case the DPs carry (`low_eq_dependent`,
`high_eq_dependent`); this is the paper's translation of any configurational account into an Agree
account. The two mechanisms part on a third caseless DP, which the configurational rule also marks
and a single stack, discharged once, does not (`stack_marks_once`). The Sakha
illustration of §5 puts a dative stack on V and an accusative stack on T; on every clause
shape of table (19) the two stacks assign the cases that the dative and accusative rules of
[baker-vinokurova-2010]'s Sakha grammar assign with no head probing
(`sakha_eq_bakerVinokurova`), and accusative appears on a DP
exactly when it is accessible to T and another caseless DP unlocks the stack, as in (15),
(18) and (20) (`accusative_rows`).

## Implementation notes

Probes are the substrate's `Probe.search` over the goals, so minimal compliance is the removal of
the unlocking goal. What the stack assigns is recorded as valued by a functional head, the
configurational rule as valued by a dependent rule, and the theorems compare the cases, which is the extensional equivalence the paper
argues for; the provenance is where the two models differ by design. Unmarked case, case
discrimination below the unmarked setting, and the negative c-command rules of §6.1 are not
formalized.

## References

* [poole-2024]
* [marantz-1991]
* [baker-vinokurova-2010]
* [rackowski-richards-2005]
* [bejar-rezac-2009]
-/

@[expose] public section

namespace Poole2024

open Case DependentCase Minimalist Examples

/-! ### The dependent-case probe stack (8) -/

section Stack

variable {ι : Type*} [DecidableEq ι] (s : ι → FeatureSlot (Case × Mechanism))

/-- The φ-probe relativized to unmarked case: it sees exactly the caseless DPs. -/
def unmarkedProbe : Probe ι := Probe.relativized fun x ↦ s x = .unvalued

/-- The stack (8) over the goals a head encounters in order: the DP assigned dependent case, if the
first probe finds a caseless DP to unlock the second and the second, ignoring that DP, finds
another. -/
def stack (gs : List ι) : Option ι :=
  ((unmarkedProbe s).search gs).bind fun g ↦ (unmarkedProbe s).search (gs.filter (· ≠ g))

/-- The stack assigning the case `c`: the DP it finds is valued `c` by Agree, every other goal
is left as it was. -/
def assignDep (c : Case) (gs : List ι) : ι → FeatureSlot (Case × Mechanism) :=
  (stack s gs).elim s (Function.update s · (.valued (c, .functional)))

/-- The case an NP carries. -/
def surface (x : ι) : Option Case := (s x).value?.map (·.1)

/-- The rule of a stack: the DP with exactly one caseless DP met before it takes the case. -/
def stackRule (c : Case) : CaseRule (Case × Mechanism) :=
  fun a _ ↦ if a = 1 then some (c, .functional) else none

variable {s} {gs : List ι}

theorem stack_eq_getElem? (hgs : gs.Nodup) :
    stack s gs = (gs.filter (s · = .unvalued))[1]? := by
  have hsearch (l : List ι) : (unmarkedProbe s).search l = (l.filter (s · = .unvalued)).head? := by
    simp [Probe.search, unmarkedProbe, List.head?_filter]
  rw [stack, hsearch]
  rcases hG : gs.filter (s · = .unvalued) with _ | ⟨g, G⟩
  · rfl
  · have hnd : (g :: G).Nodup := hG ▸ hgs.filter _
    rw [List.head?_cons, Option.bind_some, hsearch, List.filter_comm, hG,
      List.filter_cons_of_neg (by simp),
      List.filter_eq_self.2 fun y hy ↦ by
        have hne : y ≠ g := by
          rintro rfl
          exact (List.nodup_cons.1 hnd).1 hy
        simpa using hne]
    cases G <;> rfl

theorem stack_eq_none_of_subsingleton (hgs : gs.Nodup)
    (h : ∀ x ∈ gs, ∀ y ∈ gs, s x = .unvalued → s y = .unvalued → x = y) : stack s gs = none := by
  rw [stack_eq_getElem? hgs]
  rcases hG : gs.filter (s · = .unvalued) with _ | ⟨g, _ | ⟨g', G⟩⟩
  · rfl
  · rfl
  · have hmem (y : ι) (hy : y ∈ gs.filter (s · = .unvalued)) : y ∈ gs ∧ s y = .unvalued := by
      simpa using hy
    obtain ⟨h₁, h₁'⟩ := hmem g (by simp [hG])
    obtain ⟨h₂, h₂'⟩ := hmem g' (by simp [hG])
    have hnd : (g :: g' :: G).Nodup := hG ▸ hgs.filter _
    exact absurd (h g h₁ g' h₂ h₁' h₂') fun e ↦ (List.nodup_cons.1 hnd).1 (by simp [e])

theorem stack_ne_unlocker {g j : ι} (hs : (unmarkedProbe s).search gs = some g)
    (hj : stack s gs = some j) : j ≠ g := by
  rw [stack, hs, Option.bind_some] at hj
  simpa using (List.mem_filter.1 (Probe.mem_of_search_eq_some hj)).2

/-- The stack is the rule marking the DP with exactly one caseless DP met before it: the two probes
reach the second goal in the order the head meets them. -/
theorem assignDep_eq_passUnvalued (c : Case) {lt : ι → ι → Prop} [DecidableRel lt] [Std.Asymm lt]
    (hgs : gs.Pairwise lt) :
    assignDep s c gs = (stackRule c).passUnvalued lt gs.toFinset s := by
  have hnd : gs.Nodup := List.Pairwise.imp (fun {a b} (h : lt a b) ↦ by
    rintro rfl
    exact asymm h h) hgs
  set G := gs.filter (s · = .unvalued) with hG
  have hgoals : FeatureSlot.unvaluedIn gs.toFinset s = G.toFinset := by ext x; simp [hG]
  funext x
  rw [assignDep, stack_eq_getElem? hnd, ← hG]
  by_cases hx : x ∈ G
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hsx : s G[i] = .unvalued := by simpa using (List.mem_filter.1 hx).2
    rw [CaseRule.passUnvalued_getElem _ (hgs.filter _) hgoals i hi]
    by_cases hi1 : i = 1
    · subst hi1
      simp [stackRule, List.getElem?_eq_getElem hi]
    · have hne : ∀ h : 1 < G.length, G[i] ≠ G[1] := fun h e ↦
        hi1 ((hnd.filter _).getElem_inj_iff.1 e)
      rcases hl : G[1]? with _ | g
      · simp [stackRule, hi1, hsx]
      · obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hl
        simp [stackRule, hi1, hsx, Function.update_of_ne (hne h)]
  · have hnm : x ∉ FeatureSlot.unvaluedIn gs.toFinset s := fun h ↦ hx (by simpa [hG] using h)
    rw [CaseRule.passUnvalued_of_notMem hnm]
    rcases hl : G[1]? with _ | g
    · rfl
    · have hne : x ≠ g := by
        rintro rfl
        exact hx (List.mem_of_getElem? hl)
      exact Function.update_of_ne hne _ _

/-! ### Low and high dependent case against the configurational rules -/

/-- A stack on a head above two DPs assigns the lower one what the low dependent case rule (10)
assigns, whatever their lexical case. -/
theorem low_eq_dependent (c : Case) (l₀ l₁ : Option Case) (x : Fin 2) :
    surface (assignDep (lexical ![.offer l₀, .offer l₁]) c [0, 1]) x =
      surface (({ low := some c } : Rules).dependent.pass (· < ·) .univ
        (lexical ![.offer l₀, .offer l₁])) x := by
  cases l₀ <;> cases l₁ <;> fin_cases x <;> rfl

/-- A stack on the head introducing the higher DP, which meets its complement first and then its
specifier, assigns the specifier what the high dependent case rule (11) assigns, whatever their
lexical case. -/
theorem high_eq_dependent (c : Case) (l₀ l₁ : Option Case) (x : Fin 2) :
    surface (assignDep (lexical ![.offer l₀, .offer l₁]) c [1, 0]) x =
      surface (({ high := some c } : Rules).dependent.pass (· < ·) .univ
        (lexical ![.offer l₀, .offer l₁])) x := by
  cases l₀ <;> cases l₁ <;> fin_cases x <;> rfl

theorem stack_marks_once (c : Case) :
    (stackRule c).caseArray 3 = [none, some (c, .functional), none] ∧
      ({ low := some c } : Rules).dependent.caseArray 3 =
        [none, some (c, .dependent), some (c, .dependent)] :=
  ⟨rfl, rfl⟩

end Stack

/-! ### Sakha (§5) -/

/-- A Sakha clause shape of table (19): whether it has an external argument, an indirect object
in the specifier of VP, and a direct object in the complement of VP, the last either shifted out
of the VP phase or not. -/
structure Shape where
  ea : Bool
  io : Bool
  dobj : Option Bool
  deriving DecidableEq, Repr

/-- The three arguments: the external argument, the indirect object and the direct object. -/
inductive Arg
  | EA
  | IO
  | DO
  deriving DecidableEq, Repr

/-- The goals V meets: its complement, the direct object, then its specifier, the indirect
object. -/
def Shape.vGoals (s : Shape) : List Arg :=
  (s.dobj.map fun _ ↦ Arg.DO).toList ++ if s.io then [.IO] else []

/-- The goals T meets: the external argument, then the direct object if it has shifted out of VP;
the indirect object stays in the VP phase. -/
def Shape.tGoals (s : Shape) : List Arg :=
  (if s.ea then [.EA] else []) ++ if s.dobj = some true then [.DO] else []

/-- The case of an argument after the dative stack on V and the accusative stack on T
([poole-2024] (16), (17)). -/
def Shape.agree (s : Shape) (n : Arg) : Option Case :=
  surface (assignDep (assignDep (fun _ ↦ .unvalued) .dat s.vGoals) .acc s.tGoals) n

/-- The arguments of a shape, highest first. -/
def Shape.args (s : Shape) : List Arg :=
  (if s.ea then [.EA] else []) ++ (if s.io then [.IO] else []) ++
    (s.dobj.map fun _ ↦ Arg.DO).toList

/-- The arguments placed in [baker-vinokurova-2010]'s phases: the external argument merged in
the clause, the indirect object in the verb phrase, and the direct object in the verb phrase,
shifting into the clause when it shifts. -/
def Shape.np (s : Shape) : Arg → PhasedNP
  | .EA => BakerVinokurova2010.subject
  | .IO => BakerVinokurova2010.internal false
  | .DO => BakerVinokurova2010.internal (s.dobj.getD false)

/-- Table (19): on every clause shape the two stacks assign what the dependent rules of
[baker-vinokurova-2010]'s Sakha grammar assign, with no head probing. -/
theorem sakha_eq_bakerVinokurova (s : Shape) :
    s.args.map s.agree =
      BakerVinokurova2010.cases BakerVinokurova2010.grammar [] (s.args.map s.np) := by
  obtain ⟨ea, io, dobj⟩ := s
  cases ea <;> cases io <;> rcases dobj with _ | _ | _ <;> decide

/-- The goals of T's accusative stack in (15), (18) and (20): another caseless DP, if any, then
the DP in question, if accessible to T. -/
def tGoals (licensor accessible : Bool) : List Arg :=
  (if licensor then [.EA] else []) ++ if accessible then [.DO] else []

/-- A row's accusative marking, accessibility, and licensor, read from its features. -/
def interpret (r : Datum) : Option (Bool × Bool × Bool) := do
  let hasAcc ← match r.feature? "acc" with
    | some "yes" => some true
    | some "no" => some false
    | _ => none
  let accessible ← match r.feature? "accessible" with
    | some "yes" => some true
    | some "no" => some false
    | _ => none
  let licensor ← match r.feature? "licensor" with
    | some "yes" => some true
    | some "no" => some false
    | _ => none
  pure (hasAcc, accessible, licensor)

/-- A row is predicted: it is acceptable exactly when it carries accusative just in case T's
stack assigns it. -/
def Predicted (r : Datum) : Prop :=
  match interpret r with
  | some (hasAcc, accessible, licensor) =>
      r.judgment = .acceptable ↔
        hasAcc = (stack (fun _ ↦ .unvalued) (tGoals licensor accessible)).isSome
  | none => False

instance (r : Datum) : Decidable (Predicted r) := by
  unfold Predicted; split <;> infer_instance

/-- The shifted object and the raised embedded subject are accusative exactly when another caseless
DP unlocks T's stack ((15), (18), (20)). -/
theorem accusative_rows : ∀ r ∈ Examples.all, Predicted r := by
  decide

end Poole2024
