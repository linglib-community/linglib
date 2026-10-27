module

public import Linglib.Semantics.Attitudes.Doxastic
public import Linglib.Semantics.Reference.Kaplan

/-!
# Schlenker (2003): A Plea for Monsters

Schlenker treats attitude verbs as quantifiers over contexts. Kaplan's Fixity Thesis (1) holds that
an indexical's value is fixed by the context of the actual speech act, so that no operator shifts
contexts; Amharic, where the first person under *say* denotes the reported speaker (3), is the
counterexample (`not_stable_amharicI`). An attitude verb quantifies over the contexts
compatible with its subject's claim, binding a context variable to each (`Say`), and Hintikka's
quantification over worlds is the case where the embedded meaning reads only the world
(`say_world_only`, `doxastic_holdsAt_iff_say`). The Amharic second person shifts to the hearer of
the reported speech act (54) (`amharicYou_shifts`). A logophoric pronoun is the author of an
embedded context who is not the actual speaker (`Logophoric`), so none is first person.

## Implementation notes

A context variable bound by an attitude verb is a level of the context tower of
`Semantics/Reference/Context/Tower`, whose origin is the actual context: the verb binds each
compatible context, and an embedded meaning reads the tower, so a clause can mix shifted and
unshifted indexicals. An embedded clause is evaluated at the time and world of the
innermost context, as in (6). Shiftability is the choice between the origin and the innermost
access pattern; the paper's filtering and agreement mechanisms (§5.1.2, §5.1.3) are not modelled.

## References

* [schlenker-2003]
* [kaplan-1989]
* [hintikka-1962]
-/

@[expose] public section

namespace Schlenker2003

open ModalLogic Kaplan ContextTower
open scoped SetRel

variable {W E P T : Type*}

/-! ### Quantification over contexts -/

/-- (58b): `SAY⟨x,t,w⟩ cᵢ φ` holds iff `φ` holds with the context variable `cᵢ` bound to each
context compatible with the claim `x` makes at `t` in `w`, at the tower binding that context. -/
def Say (compat : E → T → W → Set (Context W E P T)) (x : E) (t : T) (w : W)
    (φ : ContextTower (Context W E P T) → Prop) (τ : ContextTower (Context W E P T)) : Prop :=
  ∀ c ∈ compat x t w, φ (τ.push c)

variable (compat : E → T → W → Set (Context W E P T)) (x : E) (t : T) (w : W) (p : W → Prop)
  (τ : ContextTower (Context W E P T)) (c : Context W E P T)

/-- (7): for a meaning that reads only the world of evaluation, quantification over contexts is
quantification over their worlds, the standard modal analysis. -/
theorem say_world_only :
    Say compat x t w (fun τ ↦ p τ.innermost.world) τ ↔
      ∀ w' ∈ Context.world '' compat x t w, p w' := by
  simp [Say]

/-- A doxastic predicate of `Doxastic.lean` holds iff its factivity and veridicality requirements
do and quantification over contexts whose worlds are its accessible worlds does. -/
theorem doxastic_holdsAt_iff_say (V : Doxastic.DoxasticPredicate W E)
    (hV : Context.world '' compat x t w = {w' | w ~[V.access x] w'}) :
    V.HoldsAt x p w ↔ (∀ _ ∈ V.factivity, p w) ∧ Doxastic.VeridicalityHolds V.veridicality p w ∧
      Say compat x t w (fun τ ↦ p τ.innermost.world) τ := by
  rw [say_world_only, hV, V.holdsAt_iff]
  rfl

/-! ### Shifted indexicals -/

/-- Amharic *I* (3) is the agent of the innermost context. -/
def amharicI : AccessPattern (Context W E P T) E := .innermost Context.agent

/-- The Amharic second person (54) is the addressee of the innermost context. -/
def amharicYou : AccessPattern (Context W E P T) E := .innermost Context.addressee

@[simp] theorem amharicI_resolve_push :
    amharicI.resolve (τ.push c) = c.agent := by
  simp [amharicI]

@[simp] theorem amharicYou_resolve_push :
    amharicYou.resolve (τ.push c) = c.addressee := by
  simp [amharicYou]

/-- Amharic *I* falsifies the Fixity Thesis (1), stability under every embedding, which English
*I* satisfies. -/
theorem not_stable_amharicI [Nontrivial E] [Nonempty W] [Nonempty P] [Nonempty T] :
    ¬ (amharicI : AccessPattern (Context W E P T) E).Stable := by
  rw [amharicI, AccessPattern.stable_innermost_iff]
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  obtain ⟨w⟩ := ‹Nonempty W›; obtain ⟨p⟩ := ‹Nonempty P›; obtain ⟨t⟩ := ‹Nonempty T›
  exact fun h ↦ hab (h ⟨a, a, w, t, p⟩ ⟨b, a, w, t, p⟩)

-- (3)
theorem amharicI_ne_I (h : c.agent ≠ τ.origin.agent) :
    amharicI.resolve (τ.push c) ≠
      Kaplan.I.resolve (τ.push c) := by
  simpa [Kaplan.I] using h

/-! ### Person features as presuppositions -/

/-- (77a): `+author(x, cᵢ)` says that `x` is the agent of the context at depth `d`, and
`+author*(x)` (75a) is the case `d = .origin`. -/
def AuthorAt (d : DepthSpec) (x : E) (t : ContextTower (Context W E P T)) : Prop :=
  x = (AccessPattern.mk d Context.agent).resolve t

/-- (80): a logophoric pronoun is `+author(x, cᵢ) ∧ −author*(x)`, the agent of the embedded
context who is not the actual speaker. -/
def Logophoric (d : DepthSpec) (x : E) (t : ContextTower (Context W E P T)) : Prop :=
  AuthorAt d x t ∧ ¬ AuthorAt .origin x t

instance [DecidableEq E] (d : DepthSpec) (x : E) (t : ContextTower (Context W E P T)) :
    Decidable (AuthorAt d x t) :=
  inferInstanceAs (Decidable (x = _))

instance [DecidableEq E] (d : DepthSpec) (x : E) (t : ContextTower (Context W E P T)) :
    Decidable (Logophoric d x t) :=
  inferInstanceAs (Decidable (AuthorAt d x t ∧ ¬ AuthorAt .origin x t))

theorem logophoric_local_of_ne (h : c.agent ≠ τ.origin.agent) :
    Logophoric .local c.agent (τ.push c) :=
  ⟨by simp [AuthorAt, AccessPattern.resolve], by simpa [AuthorAt, AccessPattern.resolve] using h⟩

-- (81)
theorem not_logophoric_origin_agent (d : DepthSpec) : ¬ Logophoric d τ.origin.agent τ :=
  fun h ↦ h.2 rfl

/-! ### A three-person, two-world model -/

/-- The speaker Alice, the reporter Bob and the hearer Carl. -/
inductive Person where
  | alice
  | bob
  | carl
  deriving DecidableEq, Repr

/-- The actual world and one alternative. -/
inductive World where
  | w0
  | w1
  deriving DecidableEq, Fintype, Repr

abbrev Ctx := Context World Person Unit Unit

/-- The context of the actual speech act: Alice speaking to Carl at the actual world. -/
def speechCtx : Ctx := ⟨.alice, .carl, .w0, (), ()⟩

/-- The contexts compatible with what `x` tells Alice: `x` speaking to Alice at either world. -/
def tellsAlice (x : Person) (_ : Unit) (_ : World) : Set Ctx :=
  {⟨x, .alice, .w0, (), ()⟩, ⟨x, .alice, .w1, (), ()⟩}

/-- Alice is happy only in the actual world; the others are happy in both. -/
def isHappy : Person → World → Prop
  | .alice, w => w = .w0
  | _, _ => True

-- (3)
theorem english_amharic_differ :
    ¬ Say tellsAlice .bob () .w0 (fun τ ↦ isHappy (Kaplan.I.resolve τ) τ.innermost.world)
        (.root speechCtx) ∧
      Say tellsAlice .bob () .w0 (fun τ ↦ isHappy (amharicI.resolve τ) τ.innermost.world)
        (.root speechCtx) := by
  simp [Say, tellsAlice, isHappy, speechCtx, Kaplan.I]

/-- In (54), the shifted Amharic second person of Bob's report is Alice, where English *you* is
Carl. -/
theorem amharicYou_shifts :
    Say tellsAlice .bob () .w0
      (fun τ ↦ amharicYou.resolve τ = .alice ∧ Kaplan.you.resolve τ = .carl) (.root speechCtx) := by
  simp [Say, tellsAlice, speechCtx, Kaplan.you]

end Schlenker2003
