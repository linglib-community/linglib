module

public import Linglib.Core.Control.Monad.Writer
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Conventional implicature

A two-dimensional meaning `TwoDim W α` pairs an at-issue value of type `α` with not-at-issue
content, a proposition over worlds `W` that the speaker contributes without putting it at issue.
Not-at-issue content only accumulates, so `TwoDim W` is the writer monad over propositions under
meet. Potts's rule of [CI application](##ConventionalImplicature.TwoDim.ciApply) is a bind that
hands its at-issue argument on unmodified, the connectives combine at-issue content
applicatively, so that CIs project from under each of them, and [conjoining the CIs a parsetree
logs](##ConventionalImplicature.TwoDim.ofWriter_bind) is a monad morphism.

Read as a presupposition, the not-at-issue content makes a two-dimensional proposition
[trivalent](##ConventionalImplicature.TwoDim.toTrivalent), and the connectives become the Weak
Kleene ones. Karttunen's filtering conditional is
[a bind](##ConventionalImplicature.TwoDim.impFilter), since its antecedent's at-issue content
decides whether its consequent's presupposition projects; it evaluates to
[the Middle Kleene conditional](##ConventionalImplicature.TwoDim.toTrivalent_impFilter), and [no
applicative combination](##ConventionalImplicature.TwoDim.exists_seq_notAtIssue_ne_impFilter)
presupposes what it does. The symmetric disjunction reads at-issue content where the not-at-issue
content fails, and so is [no trivalent
operation](##ConventionalImplicature.TwoDim.orKPSymmetric_not_trivalent).

## Implementation notes

* Potts interprets a parsetree as its root's at-issue term with the set of CI propositions on its
  nodes. The not-at-issue dimension here is the meet of that collection, so [a repeated CI adds
  nothing](##ConventionalImplicature.TwoDim.ofWriter_not_injective). That suits content whose
  repetition is redundant, but not the strengthening Potts reports for repeated expressives,
  which needs graded expressive content.
* The dimension also carries not-at-issue content that is not a CI in Potts's sense, such as
  presuppositions, the appositive impositions of AnderBois, Brasoveanu and Henderson, and
  evidential content. How an utterance updates the context with each kind is not modelled here.

## TODO

* Yagi presents the symmetric disjunction as a departure from an asymmetric rule of Karttunen
  and Peters, and Sharvit presents it as their rule. The 1979 chapter has not been checked, so
  `orKPSymmetric` is attributed to neither reading.

## References

* [potts-2005]
* [potts-2007b]
* [giorgolo-asudeh-2012]
* [karttunen-1973]
* [peters-1979]
* [anderbois-brasoveanu-henderson-2015]
* [karttunen-peters-1979]
* [yagi-2025]
* [sharvit-2025]
* [kalomoiros-schwarz-2021]
* [heim-1992]
* [van-der-sandt-1992]
* [delpinal-bassi-sauerland-2024]
-/

@[expose] public section

namespace ConventionalImplicature

universe u

/-- A two-dimensional meaning pairs an at-issue value with the not-at-issue proposition it
carries ([potts-2005]). *That bastard John is late* has at-issue content "John is late" and
not-at-issue content "the speaker disdains John". -/
@[ext]
structure TwoDim (W : Type u) (α : Type u) where
  /-- The at-issue value. -/
  atIssue : α
  /-- The not-at-issue content. -/
  notAtIssue : W → Prop

namespace TwoDim

variable {W α β : Type u}

/-! ### The monad -/

/-- Two-dimensional meanings form the writer monad over propositions under meet. A `pure`
value contributes no not-at-issue content, and composition meets the not-at-issue content of
its parts. -/
instance : Monad (TwoDim W) where
  pure a := ⟨a, ⊤⟩
  map f p := ⟨f p.atIssue, p.notAtIssue⟩
  seq f p := ⟨f.atIssue (p ()).atIssue, f.notAtIssue ⊓ (p ()).notAtIssue⟩
  bind p f := ⟨(f p.atIssue).atIssue, p.notAtIssue ⊓ (f p.atIssue).notAtIssue⟩

@[simp] theorem pure_atIssue (a : α) : (pure a : TwoDim W α).atIssue = a := rfl

@[simp] theorem pure_notAtIssue (a : α) : (pure a : TwoDim W α).notAtIssue = ⊤ := rfl

@[simp] theorem map_atIssue (f : α → β) (p : TwoDim W α) : (f <$> p).atIssue = f p.atIssue :=
  rfl

@[simp] theorem map_notAtIssue (f : α → β) (p : TwoDim W α) :
    (f <$> p).notAtIssue = p.notAtIssue := rfl

@[simp] theorem seq_atIssue (f : TwoDim W (α → β)) (p : TwoDim W α) :
    (f <*> p).atIssue = f.atIssue p.atIssue := rfl

@[simp] theorem seq_notAtIssue (f : TwoDim W (α → β)) (p : TwoDim W α) :
    (f <*> p).notAtIssue = f.notAtIssue ⊓ p.notAtIssue := rfl

@[simp] theorem bind_atIssue (p : TwoDim W α) (f : α → TwoDim W β) :
    (p >>= f).atIssue = (f p.atIssue).atIssue := rfl

@[simp] theorem bind_notAtIssue (p : TwoDim W α) (f : α → TwoDim W β) :
    (p >>= f).notAtIssue = p.notAtIssue ⊓ (f p.atIssue).notAtIssue := rfl

instance : LawfulMonad (TwoDim W) := LawfulMonad.mk' (TwoDim W)
  (id_map := fun _ ↦ rfl)
  (pure_bind := fun _ _ ↦ TwoDim.ext rfl (top_inf_eq _))
  (bind_assoc := fun _ _ _ ↦ TwoDim.ext rfl (inf_assoc ..))
  (bind_pure_comp := fun _ _ ↦ TwoDim.ext rfl (inf_top_eq _))
  (bind_map := fun _ _ ↦ rfl)

/-! ### CI application -/

/-- CI application ([potts-2005]) applies a CI functor `f` to an at-issue argument, hands the
argument on unmodified and adds the result to the not-at-issue content. -/
def ciApply (f : α → W → Prop) (p : TwoDim W α) : TwoDim W α := p >>= fun a ↦ ⟨a, f a⟩

@[simp] theorem ciApply_atIssue (f : α → W → Prop) (p : TwoDim W α) :
    (p.ciApply f).atIssue = p.atIssue := rfl

@[simp] theorem ciApply_notAtIssue (f : α → W → Prop) (p : TwoDim W α) :
    (p.ciApply f).notAtIssue = p.notAtIssue ⊓ f p.atIssue := rfl

/-! ### Connectives -/

section Connectives

variable (p q : TwoDim W (W → Prop))

/-- Negation complements the at-issue proposition and passes the not-at-issue content up. -/
def neg : TwoDim W (W → Prop) := compl <$> p

/-- Conjunction conjoins the at-issue propositions. -/
def and : TwoDim W (W → Prop) := (· ⊓ ·) <$> p <*> q

/-- Disjunction disjoins the at-issue propositions. -/
def or : TwoDim W (W → Prop) := (· ⊔ ·) <$> p <*> q

/-- Implication takes the conditional of the at-issue propositions. -/
def imp : TwoDim W (W → Prop) := (· ⇨ ·) <$> p <*> q

@[simp] theorem neg_atIssue : p.neg.atIssue = p.atIssueᶜ := rfl

@[simp] theorem neg_notAtIssue : p.neg.notAtIssue = p.notAtIssue := rfl

@[simp] theorem neg_neg : p.neg.neg = p := TwoDim.ext (compl_compl _) rfl

@[simp] theorem and_atIssue : (p.and q).atIssue = p.atIssue ⊓ q.atIssue := rfl

@[simp] theorem and_notAtIssue : (p.and q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

@[simp] theorem or_atIssue : (p.or q).atIssue = p.atIssue ⊔ q.atIssue := rfl

@[simp] theorem or_notAtIssue : (p.or q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

@[simp] theorem imp_atIssue : (p.imp q).atIssue = p.atIssue ⇨ q.atIssue := rfl

@[simp] theorem imp_notAtIssue : (p.imp q).notAtIssue = p.notAtIssue ⊓ q.notAtIssue := rfl

end Connectives

/-! ### Collecting at the root -/

/-- `ofWriter m` reads a computation that logs its CIs ([giorgolo-asudeh-2012]) as a
two-dimensional meaning, conjoining the log. -/
def ofWriter (m : Writer (List (W → Prop)) α) : TwoDim W α :=
  ⟨m.val, fun w ↦ ∀ c ∈ m.log, c w⟩

@[simp] theorem ofWriter_atIssue (m : Writer (List (W → Prop)) α) :
    (ofWriter m).atIssue = m.val := rfl

@[simp] theorem ofWriter_notAtIssue (m : Writer (List (W → Prop)) α) (w : W) :
    (ofWriter m).notAtIssue w ↔ ∀ c ∈ m.log, c w := Iff.rfl

@[simp] theorem ofWriter_pure (a : α) : ofWriter (pure a : Writer (List (W → Prop)) α) = pure a :=
  TwoDim.ext rfl (funext fun _ ↦ propext (by simp))

theorem ofWriter_bind (m : Writer (List (W → Prop)) α) (f : α → Writer (List (W → Prop)) β) :
    ofWriter (m >>= f) = ofWriter m >>= fun a ↦ ofWriter (f a) :=
  TwoDim.ext rfl (funext fun _ ↦ propext List.forall_mem_append)

theorem ofWriter_mk_cons_self (a : α) (c : W → Prop) (l : List (W → Prop)) :
    ofWriter (Writer.mk a (c :: c :: l)) = ofWriter (Writer.mk a (c :: l)) :=
  TwoDim.ext rfl (funext fun _ ↦ propext (by simp))

theorem ofWriter_not_injective [Nonempty α] :
    ¬ Function.Injective (ofWriter : Writer (List (W → Prop)) α → TwoDim W α) := fun h ↦ by
  simpa using congrArg Writer.log (h (ofWriter_mk_cons_self (Classical.arbitrary α) ⊤ []))

/-! ### Presuppositions as not-at-issue content -/

section Trivalent

open Classical

variable (p q : TwoDim W (W → Prop)) {w : W}

/-- A two-dimensional proposition evaluates to the trivalent proposition undefined where its
not-at-issue content fails and the classical value of its at-issue content elsewhere. -/
noncomputable def toTrivalent : W → Trivalent :=
  fun w ↦ Trivalent.transplication (Trivalent.ofProp (p.notAtIssue w))
    (Trivalent.ofProp (p.atIssue w))

@[simp] theorem toTrivalent_eq_true_iff :
    p.toTrivalent w = .true ↔ p.notAtIssue w ∧ p.atIssue w := by
  simp [toTrivalent]

@[simp] theorem toTrivalent_eq_false_iff :
    p.toTrivalent w = .false ↔ p.notAtIssue w ∧ ¬ p.atIssue w := by
  simp [toTrivalent]

@[simp] theorem toTrivalent_eq_undefined_iff : p.toTrivalent w = .undefined ↔ ¬ p.notAtIssue w := by
  simp [toTrivalent]

theorem toTrivalent_neg : p.neg.toTrivalent = p.toTrivalentᶜ := by
  funext w; by_cases h : p.notAtIssue w <;> by_cases a : p.atIssue w <;> simp [toTrivalent, h, a]

theorem toTrivalent_and : (p.and q).toTrivalent w = (p.toTrivalent w).meetWeak (q.toTrivalent w) :=
  by by_cases h : p.notAtIssue w <;> by_cases h' : q.notAtIssue w <;> by_cases a : p.atIssue w <;>
    by_cases b : q.atIssue w <;> simp [toTrivalent, h, h', a, b] <;> rfl

theorem toTrivalent_or : (p.or q).toTrivalent w = (p.toTrivalent w).joinWeak (q.toTrivalent w) :=
  by by_cases h : p.notAtIssue w <;> by_cases h' : q.notAtIssue w <;> by_cases a : p.atIssue w <;>
    by_cases b : q.atIssue w <;> simp [toTrivalent, h, h', a, b] <;> rfl

theorem toTrivalent_imp :
    (p.imp q).toTrivalent w = ((p.toTrivalent w)ᶜ).joinWeak (q.toTrivalent w) := by
  by_cases h : p.notAtIssue w <;> by_cases h' : q.notAtIssue w <;> by_cases a : p.atIssue w <;>
    by_cases b : q.atIssue w <;> simp [toTrivalent, h, h', a, b, himp_eq] <;> rfl

/-- The filtering conditional presupposes what its antecedent does, and what its consequent does
only where the antecedent's at-issue content holds. This is the conditional presupposition by
which [peters-1979] renders the filter of [karttunen-1973], and the one [sharvit-2025] gives for
the connectives of [karttunen-peters-1979]. -/
def impFilter : TwoDim W (W → Prop) := p >>= fun a ↦ ⟨a ⇨ q.atIssue, a ⇨ q.notAtIssue⟩

@[simp] theorem impFilter_atIssue : (p.impFilter q).atIssue = p.atIssue ⇨ q.atIssue := rfl

@[simp] theorem impFilter_notAtIssue :
    (p.impFilter q).notAtIssue = p.notAtIssue ⊓ (p.atIssue ⇨ q.notAtIssue) := rfl

theorem imp_notAtIssue_le_impFilter_notAtIssue :
    (p.imp q).notAtIssue ≤ (p.impFilter q).notAtIssue :=
  inf_le_inf_left _ le_himp

/-- The filtering conditional evaluates to the Middle Kleene conditional of [peters-1979]. -/
theorem toTrivalent_impFilter :
    (p.impFilter q).toTrivalent w = ((p.toTrivalent w)ᶜ).joinMiddle (q.toTrivalent w) := by
  by_cases h : p.notAtIssue w <;> by_cases h' : q.notAtIssue w <;> by_cases a : p.atIssue w <;>
    by_cases b : q.atIssue w <;> simp [toTrivalent, h, h', a, b, himp_eq]

/-- Filtering needs the bind: an at-issue operator applied to two meanings presupposes the same
whatever their at-issue content, so none presupposes what the filtering conditional does. -/
theorem exists_seq_notAtIssue_ne_impFilter [Nonempty W] :
    ∃ p q : TwoDim W (W → Prop), ∀ f : (W → Prop) → (W → Prop) → W → Prop,
      (f <$> p <*> q).notAtIssue ≠ (p.impFilter q).notAtIssue := by
  refine ⟨⟨⊥, ⊤⟩, ⟨⊥, ⊥⟩, fun f h ↦ ?_⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  simpa using congrFun h w

/-- The symmetric two-dimensional disjunction presupposes `(A(ψ) ∨ Π(φ)) ∧ (A(φ) ∨ Π(ψ))` and
asserts `A(φ) ∨ A(ψ)`: each disjunct's presupposition projects unless the other disjunct's
at-issue content holds. It is [yagi-2025]'s Definition 2 and the disjunction [sharvit-2025]
gives for the connectives of [karttunen-peters-1979]; [kalomoiros-schwarz-2021] give experimental
support for the symmetry. -/
def orKPSymmetric : TwoDim W (W → Prop) :=
  ⟨p.atIssue ⊔ q.atIssue, fun w ↦ (q.atIssue w ∨ p.notAtIssue w) ∧ (p.atIssue w ∨ q.notAtIssue w)⟩

theorem orKPSymmetric_comm : orKPSymmetric p q = orKPSymmetric q p :=
  TwoDim.ext (sup_comm ..) (funext fun _ ↦ propext and_comm)

/-- When the disjuncts' presuppositions conflict, a defined symmetric disjunction is true, so it is
never both defined and false there ([yagi-2025] §2.2). -/
theorem orKPSymmetric_atIssue_of_conflict (h : ¬ (p.notAtIssue w ∧ q.notAtIssue w))
    (hp : (orKPSymmetric p q).notAtIssue w) : (orKPSymmetric p q).atIssue w := by
  obtain ⟨h₁, h₂⟩ := hp
  by_cases hp : p.notAtIssue w
  · exact Or.inl (h₂.resolve_right fun hq ↦ h ⟨hp, hq⟩)
  · exact Or.inr (h₁.resolve_right hp)

theorem orKPSymmetric_not_trivalent (w : W) :
    ¬ ∃ f : Trivalent → Trivalent → Trivalent,
      ∀ p q : TwoDim W (W → Prop),
        (orKPSymmetric p q).toTrivalent w = f (p.toTrivalent w) (q.toTrivalent w) := by
  rintro ⟨f, hf⟩
  have h₁ := hf ⟨fun _ ↦ True, fun _ ↦ False⟩ ⟨fun _ ↦ True, fun _ ↦ False⟩
  have h₂ := hf ⟨fun _ ↦ False, fun _ ↦ False⟩ ⟨fun _ ↦ True, fun _ ↦ False⟩
  simp [orKPSymmetric, toTrivalent] at h₁ h₂
  exact absurd (h₁.trans h₂.symm) (by decide)

/-- Embedding under a negative factive, *x is unaware that p*, presupposes that the complement
holds, its presupposition included, and asserts that `x` does not believe its at-issue content.
The complement's presupposition so projects to the evaluation world, the transparent rule of
[van-der-sandt-1992], and not into `x`'s beliefs, the opaque rule of [heim-1992];
[delpinal-bassi-sauerland-2024] derive free choice under *unaware* with either. -/
def negFactive (believes : (W → Prop) → W → Prop) : TwoDim W (W → Prop) :=
  ⟨fun w ↦ ¬ believes p.atIssue w, fun w ↦ p.notAtIssue w ∧ p.atIssue w⟩

end Trivalent

end TwoDim

end ConventionalImplicature
