module

public import Linglib.Semantics.Presupposition.Context
public import Linglib.Semantics.Presupposition.FamilyVariant
public import Linglib.Data.Examples.TonhauserEtAl2013

/-!
# Tonhauser, Beaver, Roberts and Simons (2013): Toward a Taxonomy of Projective Content

A content projects when it survives the embedding of its trigger under negation, in a question,
under a possibility modal or in the antecedent of a conditional, the family of sentences.
Tonhauser, Beaver, Roberts and Simons sort projective contents by two properties, stated here
for a context, a set of worlds, and a content `m`, a proposition. A trigger imposes a strong
contextual felicity constraint when its sentence is acceptable only in contexts that entail
`m`. The content has obligatory local effect when a belief report with the trigger in its
complement is acceptable only where the holder's epistemic state, the local context of the
complement, entails `m`. The two properties cross to give four classes, and the diagnostics
applied to Paraguayan Guaraní and English find contents in all four.

## Main statements

* `TonhauserEtAl2013.excludes_matrix_iff`, `TonhauserEtAl2013.excludes_belief_iff`: a class
  rules out an utterance in a context that does not entail the content exactly when it has the
  constraint, and a belief report whose holder does not believe the content exactly when it has
  obligatory local effect.
* `TonhauserEtAl2013.judgment_rows`: each of the paper's examples is unacceptable exactly when
  the class of its content rules it out.
* `TonhauserEtAl2013.eq_of_excludes_iff`: a judgment in a neutral context and a judgment of a
  belief report separate the four classes.
* `TonhauserEtAl2013.acceptable_rows_of_ne_A`: local satisfaction gives every content both
  properties, and each of the other three classes has an acceptable example that this rules out.

## Implementation notes

* Acceptability is taken as given, as the contexts in which consultants accept a sentence. The
  context is the utterance context before any accommodation, so the argument against local
  satisfaction leaves the reply by accommodation open, as the paper notes.
* A member of the family of sentences is acceptable only where its clause is acceptable in its
  local context, the image of the context under a reflexive relation, so a constraint on that
  context projects (`StrongContextualFelicity.of_image`). Projection of the other contents is
  diagnosed by implication judgments, which are not modelled; the rows of (1) record such
  judgments.
* A stance to the negation of a content requires a consistent state, since the diagnostics need
  a belief predicate that enforces consistency.

## References

* [tonhauser-beaver-roberts-simons-2013]
* [chierchia-mcconnell-ginet-1990]
* [matthewson-2004]
* [karttunen-1974-presupposition]
* [heim-1983]
* [schlenker-2009]
-/

@[expose] public section

namespace TonhauserEtAl2013

open Presupposition

variable {W : Type*}

/-! ### Contexts and contents -/

/-- The stance of a body of information to a content `m`, which it entails, or leaves open
together with its negation, or contradicts while being consistent, (10). -/
inductive Stance
  | positive
  | neutral
  | negative
  deriving DecidableEq, Repr, Fintype

/-- The information `c` has the stance to the content `m`. -/
def Stance.Holds (c m : Set W) : Stance → Prop
  | positive => c ⊆ m
  | neutral => ¬ c ⊆ m ∧ ¬ c ⊆ mᶜ
  | negative => c.Nonempty ∧ c ⊆ mᶜ

theorem Stance.Holds.not_subset {s : Stance} {c m : Set W} (h : s.Holds c m)
    (hs : s ≠ .positive) : ¬ c ⊆ m := by
  cases s
  · exact absurd rfl hs
  · exact h.1
  · exact fun hm ↦ let ⟨_, hw⟩ := h.1; h.2 hw (hm hw)

private theorem Stance.exists_holds (s : Stance) : ∃ c m : Set Bool, s.Holds c m := by
  cases s
  · exact ⟨.univ, .univ, subset_rfl⟩
  · exact ⟨.univ, {true}, fun h ↦ Bool.false_ne_true (h trivial), fun h ↦ h trivial rfl⟩
  · exact ⟨{false}, {true}, ⟨false, rfl⟩, by rintro _ rfl; exact Bool.false_ne_true⟩

/-! ### The two properties -/

/-- The trigger's sentence, acceptable in the contexts `Acc`, is acceptable only in contexts
that entail `m`, (11). -/
def StrongContextualFelicity (m : Set W) (Acc : Set W → Prop) : Prop := ∀ c, Acc c → c ⊆ m

/-- A belief report with the trigger in its complement, acceptable in the contexts `Acc`, is
acceptable only in contexts that entail that the holder believes `m`, (40). The belief is the
core of `m` along the holder's doxastic accessibility `R`. -/
def ObligatoryLocalEffect (R : SetRel W W) (m : Set W) (Acc : Set W → Prop) : Prop :=
  StrongContextualFelicity (R.core m) Acc

section

variable {R : SetRel W W} {m : Set W} {Acc Acc' : Set W → Prop}

theorem obligatoryLocalEffect_iff :
    ObligatoryLocalEffect R m Acc ↔ ∀ c, Acc c → R.image c ⊆ m :=
  forall₂_congr fun _ _ ↦ SetRel.image_subset_iff.symm

/-- A local-context constraint on an embedded sentence projects to the embedding one along a
reflexive relation (24). -/
theorem StrongContextualFelicity.of_image [R.IsRefl] (h : StrongContextualFelicity m Acc)
    (hloc : ∀ c, Acc' c → Acc (R.image c)) : StrongContextualFelicity m Acc' :=
  fun c hc ↦ (SetRel.self_subset_image c).trans (h _ (hloc c hc))

/-- A constraint that must be met in the local context of a belief report gives the content
obligatory local effect, (41). -/
theorem StrongContextualFelicity.obligatoryLocalEffect (h : StrongContextualFelicity m Acc)
    (hloc : ∀ c, Acc' c → Acc (R.image c)) : ObligatoryLocalEffect R m Acc' :=
  obligatoryLocalEffect_iff.2 fun c hc ↦ h _ (hloc c hc)

end

/-! ### The four classes -/

/-- The classes of projective content, Table 1. -/
inductive ProjectiveClass
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr, Fintype

namespace ProjectiveClass

/-- The triggers of the class impose the strong contextual felicity constraint. -/
def StrongContextualFelicity (k : ProjectiveClass) : Prop := k = A ∨ k = D

/-- The contents of the class have obligatory local effect. -/
def ObligatoryLocalEffect (k : ProjectiveClass) : Prop := k = A ∨ k = C

instance : DecidablePred StrongContextualFelicity := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

instance : DecidablePred ObligatoryLocalEffect := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem eq_of_iff {k k' : ProjectiveClass}
    (hs : k.StrongContextualFelicity ↔ k'.StrongContextualFelicity)
    (ho : k.ObligatoryLocalEffect ↔ k'.ObligatoryLocalEffect) : k = k' := by
  revert hs ho; cases k <;> cases k' <;> decide

end ProjectiveClass

/-! ### The diagnostics -/

/-- A diagnostic configuration. A member of the family of sentences of the trigger's sentence is
uttered in a context with a given stance to the content, (12) and (24), or the sentence is the
complement of a belief report whose holder's epistemic state has a given stance, (41). -/
inductive Test
  | matrix (e : FamilyVariant) (s : Stance)
  | belief (s : Stance)
  deriving DecidableEq, Repr

/-- An instance of the test is acceptable, where `Acc e` holds of the contexts in which the
family member `e` is acceptable, `AccB` of those in which the belief report is, and `R` is the
holder's doxastic accessibility, so that `R.image {w}` is the holder's epistemic state at `w`. -/
def Test.Accepted (m : Set W) (R : SetRel W W) (Acc : FamilyVariant → Set W → Prop)
    (AccB : Set W → Prop) : Test → Prop
  | matrix e s => ∃ c, s.Holds c m ∧ Acc e c
  | belief s => ∃ c, ∃ w ∈ c, s.Holds (R.image {w}) m ∧ AccB c

/-- A class excludes a test when no content with the properties of the class has an acceptable
instance of it. A member of the family of sentences is acceptable only where its clause, whose
acceptability is `Acc₀`, is acceptable in its local context, the image of the context under the
member's relation. The modal's accessibility `M` is reflexive, what is the case being possible. -/
def Excludes (k : ProjectiveClass) (t : Test) : Prop :=
  ∀ (W : Type) (m : Set W) (M R : SetRel W W) [M.IsRefl] (Acc₀ : Set W → Prop)
    (Acc : FamilyVariant → Set W → Prop) (AccB : Set W → Prop),
    (∀ e c, Acc e c → Acc₀ ((e.rel M).image c)) →
    (k.StrongContextualFelicity → StrongContextualFelicity m Acc₀) →
    (k.ObligatoryLocalEffect → ObligatoryLocalEffect R m AccB) → ¬ t.Accepted m R Acc AccB

variable {k : ProjectiveClass} {e : FamilyVariant} {s : Stance}

/-- A class excludes an utterance in a context exactly when its triggers impose the constraint
and the context does not entail the content, (12). -/
theorem excludes_matrix_iff :
    Excludes k (.matrix e s) ↔ k.StrongContextualFelicity ∧ s ≠ .positive := by
  refine ⟨fun h ↦ ?_, fun ⟨hk, hs⟩ W m M R _ Acc₀ Acc AccB hloc hA _ ⟨c, hc, hacc⟩ ↦
    hc.not_subset hs ((hA hk).of_image (hloc e) c hacc)⟩
  by_contra hks
  obtain ⟨c, m, hc⟩ := s.exists_holds
  refine h Bool m .id .id (fun c' ↦ k.StrongContextualFelicity → c' ⊆ m)
    (fun _ c' ↦ k.StrongContextualFelicity → c' ⊆ m) (fun _ ↦ False)
    (fun e c' h hk ↦ by simpa using h hk) (fun hk _ h ↦ h hk) (fun _ _ h ↦ h.elim)
    ⟨c, hc, fun hk ↦ ?_⟩
  obtain rfl : s = .positive := by_contra fun hs ↦ hks ⟨hk, hs⟩
  exact hc

/-- A class excludes a belief report exactly when its contents have obligatory local effect and
the holder's epistemic state does not entail the content, (41). -/
theorem excludes_belief_iff :
    Excludes k (.belief s) ↔ k.ObligatoryLocalEffect ∧ s ≠ .positive := by
  refine ⟨fun h ↦ ?_, fun ⟨hk, hs⟩ W m M R _ Acc₀ Acc AccB _ _ hB ⟨c, w, hw, hd, hacc⟩ ↦
    hd.not_subset hs <| SetRel.image_subset_iff.2 <| Set.singleton_subset_iff.2 (hB hk c hacc hw)⟩
  by_contra hks
  obtain ⟨d, m, hd⟩ := s.exists_holds
  refine h Bool m .id (.ofSuccessors fun _ ↦ d) (fun _ ↦ False) (fun _ _ ↦ False)
    (fun c ↦ k.ObligatoryLocalEffect → (SetRel.ofSuccessors fun _ ↦ d).image c ⊆ m)
    (fun _ _ h ↦ h.elim) (fun _ _ h ↦ h.elim) (fun hk ↦ obligatoryLocalEffect_iff.2 fun _ h ↦ h hk)
    ⟨.univ, true, trivial, by simpa [SetRel.image_ofSuccessors] using hd, fun hk ↦ ?_⟩
  obtain rfl : s = .positive := by_contra fun hs ↦ hks ⟨hk, hs⟩
  exact fun v ⟨_, _, hv⟩ ↦ hd hv

instance (k : ProjectiveClass) : DecidablePred (Excludes k)
  | .matrix _ _ => decidable_of_iff' _ excludes_matrix_iff
  | .belief _ => decidable_of_iff' _ excludes_belief_iff

/-- The two diagnostics separate the four classes, in that classes excluding the same utterances
in a neutral context and the same belief reports are one class. -/
theorem eq_of_excludes_iff {k' : ProjectiveClass} (hs : s ≠ .positive)
    (hm : Excludes k (.matrix e .neutral) ↔ Excludes k' (.matrix e .neutral))
    (hb : Excludes k (.belief s) ↔ Excludes k' (.belief s)) : k = k' :=
  ProjectiveClass.eq_of_iff (by simpa [excludes_matrix_iff] using hm)
    (by simpa [excludes_belief_iff, hs] using hb)

/-! ### Local satisfaction -/

theorem Excludes.not_accepted_admits {W : Type} {t : Test} (h : Excludes .A t)
    (p : W → SignType) (M R : SetRel W W) [M.IsRefl] :
    ¬ t.Accepted (Function.support p) R (fun e c ↦ (e.rel M).image c ⊆ Function.support p)
      (fun c ↦ R.image c ⊆ Function.support p) :=
  h W _ M R (· ⊆ Function.support p) _ _ (fun _ _ h ↦ h) (fun _ _ h ↦ h)
    (fun _ _ h ↦ SetRel.image_subset_iff.1 h)

/-! ### The rows -/

/-- The names of the stances as example rows record them. -/
def Stance.table : List (String × Stance) :=
  [("m-positive", .positive), ("m-neutral", .neutral), ("m-negative", .negative)]

/-- The class that Table 2 assigns to the content of a row. -/
def class? (r : Datum) : Option ProjectiveClass :=
  r.parse? "class" [("A", .A), ("B", .B), ("C", .C), ("D", .D)]

/-- The diagnostic configuration of a row, a belief report when the row records the stance of
the holder's epistemic state and otherwise a family member in its utterance context. -/
def test? (r : Datum) : Option Test :=
  (r.parse? "holder" Stance.table).map .belief <|>
    r.environment?.bind fun e ↦ (r.parse? "context" Stance.table).map (.matrix e)

/-- Each example of a content in Table 2 is unacceptable exactly when the class of the content
excludes its configuration. -/
theorem judgment_rows :
    ∀ r ∈ Examples.all, ∀ k ∈ class? r, ∃ t ∈ test? r,
      (r.judgment = .unacceptable ↔ Excludes k t) := by
  decide

theorem exists_rows_of_class :
    ∀ k : ProjectiveClass,
      (∃ r ∈ Examples.all, class? r = some k ∧ ∃ e, test? r = some (.matrix e .neutral)) ∧
        ∃ r ∈ Examples.all, class? r = some k ∧ ∃ s ≠ Stance.positive,
          test? r = some (.belief s) := by
  decide

/-- Each class other than A has an acceptable example in a configuration that class A excludes,
so a theory of projection on which every projective content must be satisfied in its local
context does not extend to it (section 8). -/
theorem acceptable_rows_of_ne_A :
    ∀ k ≠ ProjectiveClass.A, ∃ r ∈ Examples.all, class? r = some k ∧ r.judgment = .acceptable ∧
      ∃ t ∈ test? r, Excludes .A t := by
  decide

end TonhauserEtAl2013
