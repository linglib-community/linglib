module

public import Linglib.Logic.Modal.Basic
public import Studies.Kaplan1989

/-!
# Schlenker (2003): A Plea for Monsters

Schlenker treats attitude verbs as quantifiers over contexts. Kaplan's Fixity Thesis (1) holds that
an indexical's value is fixed by the context of the actual speech act, so that no operator shifts
it; Amharic, where the first person under *say* denotes the reported speaker (3),
[is the counterexample](##not_isDirectlyReferential_amharicI). An attitude verb
[binds a context variable](##Say) to each context compatible with its subject's
claim, and Hintikka's quantification over worlds is
[the case where the embedded meaning reads only the world](##say_world_only). A
logophoric pronoun is the author of an embedded context who is not the actual speaker, so
[none is first person](##not_logophoric_agent).

## Implementation notes

A meaning is a `Character` whose context is the context of the actual speech act, the
paper's `c*`, and whose index is the assignment of contexts to context variables: a verb
evaluates its complement at the assignment updated at its variable, and a clause can mix shifted
and unshifted indexicals. An embedded clause reads its time and world from the context its verb
binds, as in (6). The paper's assignment also values individual, time and world variables, and
its pronouns are variables with presupposed features; here an indexical is the coordinate it
reads. The filtering and agreement mechanisms (§5.1.2, §5.1.3) are not modelled.

## References

* [schlenker-2003]
* [kaplan-1989]
* [hintikka-1962]
-/

@[expose] public section

namespace Schlenker2003

open ModalLogic SpeechAct
open scoped SetRel

variable {W E P T ι : Type*} [DecidableEq ι]

/-! ### Quantification over contexts -/

/-- (58b): `SAY⟨x,t,w⟩ cᵢ φ` holds iff `φ` holds with the context variable `cᵢ` bound to each
context compatible with the claim `x` makes at `t` in `w`. -/
def Say (compat : E → T → W → Set (Context W E P T)) (x : E) (t : T) (w : W) (i : ι)
    (φ : Character (Context W E P T) (ι → Context W E P T) Prop) :
    Character (Context W E P T) (ι → Context W E P T) Prop :=
  fun c s ↦ ∀ c' ∈ compat x t w, φ c (Function.update s i c')

variable (compat : E → T → W → Set (Context W E P T)) (x : E) (t : T) (w : W) (p : W → Prop)
  (i : ι) (c c' : Context W E P T) (s : ι → Context W E P T)

/-- (7): for a meaning that reads only the world of the bound context, quantification over
contexts is quantification over their worlds, the standard modal analysis. -/
theorem say_world_only :
    Say compat x t w i (fun _ s ↦ p (s i).world) c s ↔
      ∀ w' ∈ Context.world '' compat x t w, p w' := by
  simp [Say]

/-- Hintikka's box along an accessibility relation is quantification over contexts whose worlds
are the accessible ones. -/
theorem box_iff_say (R : SetRel W W)
    (hR : Context.world '' compat x t w = {w' | w ~[R] w'}) :
    □[R] p w ↔ Say compat x t w i (fun _ s ↦ p (s i).world) c s := by
  rw [say_world_only, hR]
  rfl

/-! ### Shifted indexicals -/

/-- Amharic *I* (3) is the agent of the context its variable is bound to. -/
def amharicI (i : ι) : Character (Context W E P T) (ι → Context W E P T) E :=
  fun _ s ↦ (s i).agent

/-- The Amharic second person (54) is the addressee of the context its variable is bound to. -/
def amharicYou (i : ι) : Character (Context W E P T) (ι → Context W E P T) E :=
  fun _ s ↦ (s i).addressee

omit [DecidableEq ι] in
@[simp] theorem amharicI_apply : amharicI i c s = (s i).agent := rfl

omit [DecidableEq ι] in
@[simp] theorem amharicYou_apply : amharicYou i c s = (s i).addressee := rfl

omit [DecidableEq ι] in
/-- Amharic *I* falsifies the Fixity Thesis (1): its value is not fixed by the context of the
actual speech act, as that of English *I* is. -/
theorem not_isDirectlyReferential_amharicI [Nontrivial E] [Nonempty W] [Nonempty P] [Nonempty T] :
    ¬ (amharicI i : Character (Context W E P T) _ E).IsDirectlyReferential := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  obtain ⟨w⟩ := ‹Nonempty W›; obtain ⟨p⟩ := ‹Nonempty P›; obtain ⟨t⟩ := ‹Nonempty T›
  exact fun h ↦ hab (h ⟨a, a, w, t, p⟩ (fun _ ↦ ⟨a, a, w, t, p⟩) fun _ ↦ ⟨b, a, w, t, p⟩)

variable {c c'}

-- (3)
theorem amharicI_ne_I (h : c'.agent ≠ c.agent) :
    amharicI i c (Function.update s i c') ≠ Kaplan1989.I c (Function.update s i c') := by
  simpa [Kaplan1989.I] using h

/-! ### Person features as presuppositions -/

/-- (77a): `+author(x, cᵢ)` says that `x` is the agent of the context `cᵢ`. -/
def Author (i : ι) (x : E) : Character (Context W E P T) (ι → Context W E P T) Prop :=
  fun _ s ↦ x = (s i).agent

/-- (75a): `+author*(x)` says that `x` is the agent of the actual speech act. -/
def AuthorStar (x : E) : Character (Context W E P T) (ι → Context W E P T) Prop :=
  fun c _ ↦ x = c.agent

/-- (80): a logophoric pronoun is `+author(x, cᵢ) ∧ −author*(x)`, the agent of the embedded
context who is not the actual speaker. -/
def Logophoric (i : ι) (x : E) : Character (Context W E P T) (ι → Context W E P T) Prop :=
  fun c s ↦ Author i x c s ∧ ¬ AuthorStar x c s

theorem logophoric_update_of_ne (h : c'.agent ≠ c.agent) :
    Logophoric i c'.agent c (Function.update s i c') :=
  ⟨by simp [Author], h⟩

omit [DecidableEq ι] in
variable (c) in
-- (81)
/-- No logophoric pronoun denotes the actual speaker. -/
theorem not_logophoric_agent : ¬ Logophoric i c.agent c s :=
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
theorem english_amharic_differ (i : ι) (s : ι → Ctx) :
    ¬ Say tellsAlice .bob () .w0 i (fun c s ↦ isHappy (Kaplan1989.I c s) (s i).world)
        speechCtx s ∧
      Say tellsAlice .bob () .w0 i (fun c s ↦ isHappy (amharicI i c s) (s i).world)
        speechCtx s := by
  simp [Say, tellsAlice, isHappy, speechCtx, Kaplan1989.I]

/-- In (54), the shifted Amharic second person of Bob's report is Alice, where English *you* is
Carl. -/
theorem amharicYou_shifts (i : ι) (s : ι → Ctx) :
    Say tellsAlice .bob () .w0 i
      (fun c s ↦ amharicYou i c s = .alice ∧ c.addressee = .carl) speechCtx s := by
  simp [Say, tellsAlice, speechCtx]

end Schlenker2003
