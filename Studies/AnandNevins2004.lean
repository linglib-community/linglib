module

public import Linglib.Semantics.Reference.Context.Basic
public import Linglib.Data.Examples.AnandNevins2004
public import Mathlib.Data.List.Basic
import all Init.Data.String.Pattern.Basic  -- for unfolding `String.Slice.Pattern.Internal.memcmpSlice`
import all Init.Data.String.Pattern.String  -- for unfolding `String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?`, `String.Slice.Pattern.ForwardSliceSearcher.startsWith`
import all Init.Data.String.Slice  -- for unfolding `String.Slice.startsWith`
import all Init.Data.String.TakeDrop  -- for unfolding `String.startsWith`

/-!
# Anand & Nevins 2004: shifty operators in changing contexts

In Zazaki every indexical may shift under *vano* 'say', and in Slave first-person indexicals
shift under *hadi*, yet indexicals in one speech-context domain never take their values from
different contexts (Shift-Together); in Slave the embedding verb decides which indexicals shift
and whether they must; and under two stacked reports a shifted indexical in the intermediate
clause blocks the lowest indexical from reaching the utterance context. The account: Kaplan's
context and index parameters are made the same type, an attitude verb quantifies over indices,
and a language's context-shifting operators overwrite the context from the index — all of it in
Zazaki, the author coordinate alone in Slave — so shifting is literal overwriting, whence
Shift-Together and the loss of the utterance context under an intermediate shift; lexical entries
pair verbs with operator options.

## Main definitions

* `Params`: the context–index pair; `I`, `you`, `here`, `now` read the context, `proSubj`
  and `logAddr` the index.
* `Op`: the context-shifting operators (2); `attitude` is (23b).
* `Entry`: a verb's operator options (39); `readings`, `readings₂` the values an indexical
  can take under one or two reports.

## References

* [anand-nevins-2004]
* [kaplan-1989] — context and index
* [schlenker-2003] — the lexical-underspecification rival and the Amharic data
* [stalnaker-1978] — `Op.all` as the diagonal operator
-/

@[expose] public section

namespace AnandNevins2004

open Kaplan

variable {W E P T : Type*}

/-! ### Two parameters of the same type -/

/-- Kaplan's context and index, both of context type (§3.1). -/
abbrev Params (W E P T : Type*) := Context W E P T × Context W E P T

/-- An expression interpreted relative to the two parameters. -/
abbrev Expr (W E P T : Type*) (R : Type*) := Params W E P T → R

/-- The indexicals read the context parameter (24). -/
def I : Expr W E P T E := fun p => p.1.agent

def you : Expr W E P T E := fun p => p.1.addressee

def here : Expr W E P T P := fun p => p.1.position

def now : Expr W E P T T := fun p => p.1.time

/-- Subject-controlled PRO reads the author of the index (41); the logophors read its author
and addressee (43). -/
def proSubj : Expr W E P T E := fun p => p.2.agent

def logAddr : Expr W E P T E := fun p => p.2.addressee

/-- The context-shifting operators (2): none, Zazaki's `all` overwriting every coordinate of
the context with the index, and Slave's `auth` overwriting the author coordinate alone. -/
inductive Op
  | none
  | all
  | auth
  deriving DecidableEq

/-- The rewriting an operator performs on the parameters. -/
def Op.act : Op → Params W E P T → Params W E P T
  | .none => id
  | .all => fun p => (p.2, p.2)
  | .auth => fun p => ({ p.1 with agent := p.2.agent }, p.2)

/-- (23b): an attitude verb quantifies over the indices compatible with the attitude and
leaves the context parameter untouched. -/
def attitude (acc : E → Context W E P T → Set (Context W E P T)) (x : E)
    (φ : Expr W E P T Prop) : Expr W E P T Prop :=
  fun p => ∀ j ∈ acc x p.2, φ (p.1, j)

/-- (26)–(28): with `all` as sister of *say*, the complement is evaluated at the reported
context alone, so every indexical in it shifts together. -/
theorem attitude_all (acc : E → Context W E P T → Set (Context W E P T)) (x : E)
    (φ : Expr W E P T Prop) (p : Params W E P T) :
    attitude acc x (φ ∘ Op.all.act) p ↔ ∀ j ∈ acc x p.2, φ (j, j) := Iff.rfl

/-- (30): under `auth` the first person reads the reported author while the second person
keeps the utterance addressee. -/
theorem I_auth (p : Params W E P T) : I (Op.auth.act p) = p.2.agent := rfl

theorem you_auth (p : Params W E P T) : you (Op.auth.act p) = p.1.addressee := rfl

/-- A shifted first person is read de se: under `all` it coincides with PRO (§5.1). -/
theorem I_all_eq_proSubj : (I ∘ Op.all.act : Expr W E P T E) = proSubj := rfl

/-! ### Lexical entries and readings -/

/-- A verb's operator options (39): Zazaki *vano* and Slave TELL take `all` optionally, Slave
WANT takes `auth` optionally, Slave SAY takes `auth` obligatorily, and the other Zazaki
attitude verbs take none (fn. 3). -/
abbrev Entry := List Op

def vano : Entry := [.none, .all]

def zazakiAttitude : Entry := [.none]

def slaveTell : Entry := [.none, .all]

def slaveWant : Entry := [.none, .auth]

def slaveSay : Entry := [.auth]

/-- The values an expression takes under a report with context `c` and reported context `j`,
one per operator option. -/
def readings {R : Type*} (e : Entry) (φ : Expr W E P T R) (c j : Context W E P T) : List R :=
  e.map fun o => φ (o.act (c, j))

/-- (13): the first and second person under *vano* read from the same context — the two mixed
pairs are not among the readings. -/
theorem readings_vano_I_you (c j : Context W E P T) :
    readings vano (fun p => (I p, you p)) c j = [(c.agent, c.addressee), (j.agent, j.addressee)] :=
  rfl

theorem mixed_notMem_readings_vano {c j : Context W E P T} (ha : c.agent ≠ j.agent)
    (hb : c.addressee ≠ j.addressee) :
    (c.agent, j.addressee) ∉ readings vano (fun p => (I p, you p)) c j ∧
      (j.agent, c.addressee) ∉ readings vano (fun p => (I p, you p)) c j := by
  simp [readings_vano_I_you, ha, ha.symm, hb, hb.symm]

/-- (17), (38b): under Slave SAY the first person is the reported author and the second the
utterance addressee, obligatorily. -/
theorem readings_slaveSay (c j : Context W E P T) :
    readings slaveSay (fun p => (I p, you p)) c j = [(j.agent, c.addressee)] := rfl

/-- (36): under Slave TELL both persons shift together. -/
theorem readings_slaveTell (c j : Context W E P T) :
    readings slaveTell (fun p => (I p, you p)) c j =
      [(c.agent, c.addressee), (j.agent, j.addressee)] := rfl

/-- (37), (38a): under Slave WANT the first person shifts optionally and the second never. -/
theorem readings_slaveWant (c j : Context W E P T) :
    readings slaveWant (fun p => (I p, you p)) c j =
      [(c.agent, c.addressee), (j.agent, c.addressee)] := rfl

/-! ### Multiple embedding -/

/-- Overwriting loses the utterance context (§3.4): after `all`, the context no longer depends
on what it was. -/
theorem opAll_forgets (c c' j : Context W E P T) :
    (Op.all.act (c, j)).1 = (Op.all.act (c', j)).1 := rfl

/-- Two stacked reports with reported contexts `j₁` (intermediate) and `j₂` (lowest): the
values of an expression in the lowest clause, one per pair of operator options. -/
def readings₂ {R : Type*} (e₁ e₂ : Entry) (φ : Expr W E P T R) (c j₁ j₂ : Context W E P T) :
    List R :=
  e₁.flatMap fun o₁ => e₂.map fun o₂ => φ (o₂.act ((o₁.act (c, j₁)).1, j₂))

/-- (33): with nothing forcing a shift in the intermediate clause, the lowest first person may
read the utterance author. -/
theorem readings₂_vano_I (c j₁ j₂ : Context W E P T) :
    readings₂ vano vano I c j₁ j₂ = [c.agent, j₂.agent, j₁.agent, j₂.agent] := rfl

/-- (32): a shifted second person in the intermediate clause diagnoses `all` there, after
which the lowest first person can only be the intermediate or the lowest reported author —
never the utterance author. -/
theorem lowerI_of_shifted_you {c j₁ j₂ : Context W E P T} {o₁ o₂ : Op} (h₁ : o₁ ∈ vano)
    (h₂ : o₂ ∈ vano) (hyou : you (o₁.act (c, j₁)) = j₁.addressee)
    (hne : c.addressee ≠ j₁.addressee) :
    I (o₂.act ((o₁.act (c, j₁)).1, j₂)) ∈ [j₁.agent, j₂.agent] := by
  simp only [vano, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl
  · exact absurd hyou hne
  · rcases h₂ with rfl | rfl <;> simp [I, Op.act]

/-! ### The paper's examples -/

/-- Whether an operator makes a coordinate read the reported context: the coordinate's value
after the operator on the distinguishing pair of contexts. -/
def Op.shifts (o : Op) (coord : Context Bool Bool Bool Bool → Bool) : Bool :=
  coord (o.act (⟨false, false, false, false, false⟩, ⟨true, true, true, true, true⟩)).1

def Entry.ofString? : String → Option Entry
  | "vano" => some vano
  | "zazaki_attitude" => some zazakiAttitude
  | "slave_tell" => some slaveTell
  | "slave_want" => some slaveWant
  | "slave_say" => some slaveSay
  | _ => none

def coordOfString? : String → Option (Context Bool Bool Bool Bool → Bool)
  | "I" => some Context.agent
  | "you" => some Context.addressee
  | "here" => some Context.position
  | "now" => some Context.time
  | _ => none

/-- Every recorded reading of a single embedded indexical is available exactly when some
operator option of the embedding verb's entry gives it: the reported-context reading when an
option shifts the coordinate, the utterance-context reading when one does not. -/
theorem rows_track_entries :
    ∀ r ∈ Examples.all, r.feature? "pragmatic_clash" = none →
      ∀ e ∈ ((r.feature? "entry").bind Entry.ofString?).toList,
        ∀ coord ∈ ((r.feature? "indexical").bind coordOfString?).toList,
        ∀ x ∈ r.readings,
          (x.1 = "reported context" → (x.2 = .acceptable ↔ ∃ o ∈ e, o.shifts coord = true)) ∧
          (x.1 = "utterance context" → (x.2 = .acceptable ↔ ∃ o ∈ e, o.shifts coord = false)) := by
  decide +kernel

/-- Shift-Together (16): wherever the paper lists mixed readings, they are unacceptable. -/
theorem rows_shift_together :
    ∀ r ∈ Examples.all, r.feature? "test" = some "shift_together" →
      ∀ x ∈ r.readings, x.1.startsWith "mixed" → x.2 = .unacceptable := by
  decide +kernel

end AnandNevins2004
