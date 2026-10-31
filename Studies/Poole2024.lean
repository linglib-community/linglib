module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Probe.Basic
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

On a two-DP domain the stack assigns exactly what the dependent rule of the configurational
model assigns, low or high, whatever lexical case the DPs carry (`low_eq_dependentPass`,
`high_eq_dependentPass`); this is the paper's translation of any configurational account into
an Agree account. The two mechanisms part on a third caseless DP, which the configurational
rule also marks and a single stack, discharged once, does not (`stack_marks_once`). The Sakha
illustration of §5 puts a dative stack on V and an accusative stack on T; on every clause
shape of table (19) the two stacks assign the cases that the dative and accusative rules of
[baker-vinokurova-2010]'s Sakha grammar assign with no head probing
(`sakha_eq_bakerVinokurova`), and accusative appears on a DP
exactly when it is accessible to T and another caseless DP unlocks the stack, as in (15),
(18) and (20) (`accusative_rows`).

## Implementation notes

Probes are the substrate's `Probe.search` over goals paired with their positions, so that
minimal compliance is the removal of the unlocking position and case is assigned by position;
the two-DP theorems then hold for arbitrary DPs and lexical cases by computation. What the
stack assigns is recorded as valued by Agree, the configurational rule as valued by a dependent
rule, and the theorems compare the cases, which is the extensional equivalence the paper
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

variable {α : Type*}

/-- A goal as a head sees it: an NP with its current valuation, at its position among the
goals the head encounters. -/
abbrev Goal (α : Type*) := (α × FeatureSlot (Case × Mechanism)) × ℕ

/-- The φ-probe relativized to unmarked case: it sees exactly the caseless DPs. -/
def unmarkedProbe : Probe (Goal α) := Probe.relativized fun g ↦ g.1.2 = .unvalued

/-- The stack (8) over the goals a head encounters in order: the position of the DP assigned
dependent case, if the first probe finds a caseless DP to unlock the second and the second,
ignoring that DP, finds another. -/
def stack (goals : Valuation α (Case × Mechanism)) : Option ℕ :=
  (unmarkedProbe.search goals.zipIdx).bind fun g ↦
    (unmarkedProbe.search (goals.zipIdx.filter (·.2 ≠ g.2))).map (·.2)

/-- The stack assigning the case `c`: the DP it finds is valued `c` by Agree, every other goal
is left as it was. -/
def assignDep (c : Case) (goals : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  match stack goals with
  | none => goals
  | some j => goals.zipIdx.map fun g ↦ if g.2 = j then (g.1.1, .valued (c, .agree)) else g.1

/-- The cases a list of valued NPs carries. -/
def surface (out : Valuation α (Case × Mechanism)) : List (Option Case) :=
  out.map (·.2.value?.map (·.1))

theorem stack_eq_none_of_subsingleton {goals : Valuation α (Case × Mechanism)}
    (h : ∀ i j, ∀ g ∈ goals.zipIdx, ∀ g' ∈ goals.zipIdx, g.2 = i → g'.2 = j →
      g.1.2 = .unvalued → g'.1.2 = .unvalued → i = j) :
    stack goals = none := by
  unfold stack
  rcases hs : unmarkedProbe.search goals.zipIdx with _ | g
  · rfl
  · simp only [Option.bind_some, Option.map_eq_none_iff, Probe.search_eq_none_iff, List.mem_filter,
      decide_eq_true_eq, and_imp]
    intro g' hg' hne hvis
    have hg := Probe.mem_of_search_eq_some hs
    have hv := Probe.sat_of_search_eq_some hs
    simp only [unmarkedProbe, Probe.relativized] at hv hvis
    exact hne (h g'.2 g.2 g' hg' g hg rfl rfl hvis hv)

theorem stack_ne_unlocker {goals : Valuation α (Case × Mechanism)} {g : Goal α} {j : ℕ}
    (hs : unmarkedProbe.search goals.zipIdx = some g) (hj : stack goals = some j) : j ≠ g.2 := by
  unfold stack at hj
  rw [hs, Option.bind_some, Option.map_eq_some_iff] at hj
  obtain ⟨g', hg', rfl⟩ := hj
  exact of_decide_eq_true (List.mem_filter.1 (Probe.mem_of_search_eq_some hg')).2

/-! ### Low and high dependent case against the configurational rules -/

/-- A stack on a head above two DPs assigns the lower one what the low dependent case rule (10)
assigns, whatever their lexical case. -/
theorem low_eq_dependentPass (c : Case) (lex : α → Option Case) (a b : α) :
    surface (assignDep c (lexicalValuation lex [a, b]))
      = surface (({ low := some c } : Rules).dependentPass (fun _ ↦ true)
          (lexicalValuation lex [a, b])) := by
  simp only [lexicalValuation, Valuation.initial, List.map_cons, List.map_nil]
  cases lex a <;> cases lex b <;> rfl

/-- A stack on the head introducing the higher DP assigns its specifier what the high dependent case
rule (11) assigns, whatever their lexical case. -/
theorem high_eq_dependentPass (c : Case) (lex : α → Option Case) (spec comp : α) :
    (surface (assignDep c (lexicalValuation lex [comp, spec]))).reverse
      = surface (({ high := some c } : Rules).dependentPass (fun _ ↦ true)
          (lexicalValuation lex [spec, comp])) := by
  simp only [lexicalValuation, Valuation.initial, List.map_cons, List.map_nil]
  cases lex spec <;> cases lex comp <;> rfl

theorem stack_marks_once (c : Case) (lex : α → Option Case) (a b d : α) (ha : lex a = none)
    (hb : lex b = none) (hd : lex d = none) :
    surface (assignDep c (lexicalValuation lex [a, b, d])) = [none, some c, none] ∧
      surface (({ low := some c } : Rules).dependentPass (fun _ ↦ true)
        (lexicalValuation lex [a, b, d])) = [none, some c, some c] := by
  simp only [lexicalValuation, Valuation.initial, List.map_cons, List.map_nil, ha, hb, hd]
  exact ⟨rfl, rfl⟩

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
def Shape.vGoals (s : Shape) : Valuation Arg (Case × Mechanism) :=
  (s.dobj.map fun _ ↦ (Arg.DO, (.unvalued : FeatureSlot (Case × Mechanism)))).toList ++
    (if s.io then [(.IO, .unvalued)] else [])

/-- The goals T meets after V's stack has run: the external argument, then the direct object if
it has shifted out of VP; the indirect object stays in the VP phase. -/
def Shape.tGoals (s : Shape) (vp : Valuation Arg (Case × Mechanism)) :
    Valuation Arg (Case × Mechanism) :=
  (if s.ea then [(.EA, .unvalued)] else []) ++
    (if s.dobj = some true then vp.filter (·.1 = .DO) else [])

/-- The case of an argument after the dative stack on V and the accusative stack on T
([poole-2024] (16), (17)). -/
def Shape.agree (s : Shape) (n : Arg) : Option Case :=
  let vp := assignDep .dat s.vGoals
  let tp := assignDep .acc (s.tGoals vp)
  ((tp.valueOf n).orElse fun _ ↦ vp.valueOf n).map (·.1)

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
def tGoals (licensor accessible : Bool) : Valuation Arg (Case × Mechanism) :=
  (if licensor then [(.EA, .unvalued)] else []) ++ (if accessible then [(.DO, .unvalued)] else [])

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
      r.judgment = .acceptable ↔ hasAcc = (stack (tGoals licensor accessible)).isSome
  | none => False

instance (r : Datum) : Decidable (Predicted r) := by
  unfold Predicted; split <;> infer_instance

/-- The shifted object and the raised embedded subject are accusative exactly when another caseless
DP unlocks T's stack ((15), (18), (20)). -/
theorem accusative_rows : ∀ r ∈ Examples.all, Predicted r := by
  decide

end Poole2024
