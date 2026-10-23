module

public import Linglib.Semantics.Composition.Writer
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Conventional implicature

This file defines two-dimensional meanings, the carrier of Potts's logic of conventional
implicatures (CIs). A two-dimensional meaning has an at-issue value, which composes as usual,
and not-at-issue content, a proposition the speaker contributes without putting it at issue;
`TwoDim W α` pairs an at-issue value of type `α` with not-at-issue content over worlds `W`.
Not-at-issue content only accumulates, so `TwoDim W` is the writer monad over propositions
under meet. Applying an at-issue operator with `f <$> p` passes the not-at-issue content up
(`map_notAtIssue`), and binding with `p >>= f` lets at-issue content feed later not-at-issue
content but never the reverse (`bind_atIssue`). Potts's rule of CI application, which applies a
CI functor `f` to an at-issue argument and returns the argument unmodified, is
`p >>= fun a ↦ ⟨a, f a⟩`. The connectives `neg`, `and`, `or` and `imp` act on at-issue
propositions and meet the not-at-issue content of their parts, so CIs project from under every
connective.

Potts collects the CIs of a parsetree at its root, and Giorgolo and Asudeh recast that
collection as a writer monad whose log lists the CIs. The map `ofWriter` conjoins such a log.
It is a monad morphism (`ofWriter_pure`, `ofWriter_bind`), so composing two-dimensional meanings
node by node predicts what collecting at the root does. Conjoining forgets how the log was
itemized, for instance how often a CI was contributed (`ofWriter_not_injective`).

Karttunen and Peters treat presupposition the same way, as not-at-issue content. A
two-dimensional proposition evaluates to a trivalent one (`toTrivalent`), undefined where its
not-at-issue content fails, and the connectives here then evaluate to the Weak Kleene ones
(`toTrivalent_and`). The two part at Karttunen's filtering: a filtering conditional presupposes
at most what the unfiltered one does (`imp_notAtIssue_subset_support`), and less in
general, because its antecedent's at-issue content can satisfy its consequent's presupposition,
which no at-issue operator on two-dimensional meanings allows (`exists_notAtIssue_ne_support`). Two
operations read the at-issue content where the not-at-issue content fails, and so are no
trivalent operations: Karttunen and Peters's symmetric disjunction (`orKPSymmetric_not_trivalent`)
and embedding under a negative factive (`negFactive`).

## Main definitions

* `TwoDim`: an at-issue value and not-at-issue content, with its `Monad` instance.
* `TwoDim.neg`, `TwoDim.and`, `TwoDim.or`, `TwoDim.imp`: the connectives on propositions.
* `TwoDim.ofWriter`: the conjunction of a writer's log of CIs.
* `TwoDim.toTrivalent`: the trivalent proposition, undefined where the not-at-issue content fails.
* `TwoDim.orKPSymmetric`, `TwoDim.negFactive`: the symmetric two-dimensional disjunction and
  embedding under a negative factive.

## Implementation notes

The not-at-issue dimension is the meet of the collected content rather than the collection, so a
repeated CI adds nothing. That suits content whose repetition is redundant, but not the
strengthening Potts reports for repeated expressives, which needs graded expressive content.
The dimension also carries not-at-issue content that is not a CI in Potts's sense, such as the
appositive impositions of AnderBois, Brasoveanu and Henderson and evidential content. How an
utterance updates the context with each kind is not modelled here.

## References

* [potts-2005]
* [potts-2007b]
* [giorgolo-asudeh-2012]
* [karttunen-1973]
* [anderbois-brasoveanu-henderson-2015]
* [karttunen-peters-1979]
* [yagi-2025]
* [kalomoiros-schwarz-2021]
* [heim-1992]
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
noncomputable def toTrivalent : W → SignType :=
  Set.indicator {w | p.notAtIssue w} fun w ↦ SignType.ofProp (p.atIssue w)

@[simp] theorem toTrivalent_eq_one_iff : p.toTrivalent w = 1 ↔ p.notAtIssue w ∧ p.atIssue w := by
  simp [toTrivalent]

@[simp] theorem toTrivalent_eq_neg_one_iff :
    p.toTrivalent w = -1 ↔ p.notAtIssue w ∧ ¬ p.atIssue w := by
  simp [toTrivalent]

@[simp] theorem toTrivalent_eq_zero_iff : p.toTrivalent w = 0 ↔ ¬ p.notAtIssue w := by
  simp [toTrivalent]

theorem toTrivalent_neg : p.neg.toTrivalent = -p.toTrivalent := by
  funext w; by_cases h : p.notAtIssue w <;> by_cases a : p.atIssue w <;> simp [toTrivalent, h, a]

theorem toTrivalent_and : (p.and q).toTrivalent w = (p.toTrivalent w).meetWeak (q.toTrivalent w) :=
  by by_cases h : p.notAtIssue w <;> by_cases h' : q.notAtIssue w <;> by_cases a : p.atIssue w <;>
    by_cases b : q.atIssue w <;> simp [toTrivalent, h, h', a, b] <;> rfl

theorem toTrivalent_or : (p.or q).toTrivalent w = (p.toTrivalent w).joinWeak (q.toTrivalent w) :=
  by by_cases h : p.notAtIssue w <;> by_cases h' : q.notAtIssue w <;> by_cases a : p.atIssue w <;>
    by_cases b : q.atIssue w <;> simp [toTrivalent, h, h', a, b] <;> rfl

theorem toTrivalent_imp :
    (p.imp q).toTrivalent w = (-p.toTrivalent w).joinWeak (q.toTrivalent w) := by
  by_cases h : p.notAtIssue w <;> by_cases h' : q.notAtIssue w <;> by_cases a : p.atIssue w <;>
    by_cases b : q.atIssue w <;> simp [toTrivalent, h, h', a, b, himp_eq] <;> rfl

theorem imp_notAtIssue_subset_support :
    {w | (p.imp q).notAtIssue w} ⊆
      Function.support fun w ↦ (-p.toTrivalent w).joinMiddle (q.toTrivalent w) := fun w h ↦ by
  simp only [Set.mem_ofPred_eq, imp_notAtIssue, Pi.inf_apply, inf_Prop_eq] at h
  simp [h.1, h.2]

theorem exists_notAtIssue_ne_support [Nonempty W] :
    ∃ p q : TwoDim W (W → Prop), ∀ f : (W → Prop) → (W → Prop) → W → Prop,
      {w | (f <$> p <*> q).notAtIssue w} ≠
        Function.support fun w ↦ (-p.toTrivalent w).joinMiddle (q.toTrivalent w) := by
  refine ⟨⟨⊥, ⊤⟩, ⟨⊥, ⊥⟩, fun f h ↦ ?_⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  have := congrArg (w ∈ ·) h
  simp at this

/-- The symmetric two-dimensional disjunction of the [karttunen-peters-1979] tradition projects
`(A(ψ) ∨ Π(φ)) ∧ (A(φ) ∨ Π(ψ))` and asserts `A(φ) ∨ A(ψ)`. The literal 1979 formulation was
asymmetric, projecting the first disjunct's presupposition unconditionally; this is the symmetric
variant of [yagi-2025]'s Definition 2, for whose symmetry [kalomoiros-schwarz-2021] give
experimental support. -/
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
    ¬ ∃ f : SignType → SignType → SignType,
      ∀ p q : TwoDim W (W → Prop),
        (orKPSymmetric p q).toTrivalent w = f (p.toTrivalent w) (q.toTrivalent w) := by
  rintro ⟨f, hf⟩
  have h₁ := hf ⟨fun _ ↦ True, fun _ ↦ False⟩ ⟨fun _ ↦ True, fun _ ↦ False⟩
  have h₂ := hf ⟨fun _ ↦ False, fun _ ↦ False⟩ ⟨fun _ ↦ True, fun _ ↦ False⟩
  simp [orKPSymmetric, toTrivalent] at h₁ h₂
  exact absurd (h₁.trans h₂.symm) (by decide)

/-- Embedding under a negative factive, *x is unaware that p*, presupposes that the complement
holds and asserts that `x` does not believe its at-issue content. Presupposing that the complement
holds, rather than only its at-issue content as [heim-1992] does for atomic complements, is
[delpinal-bassi-sauerland-2024]'s treatment; the two part when the complement has its own
presupposition. -/
def negFactive (believes : (W → Prop) → W → Prop) : TwoDim W (W → Prop) :=
  ⟨fun w ↦ ¬ believes p.atIssue w, fun w ↦ p.notAtIssue w ∧ p.atIssue w⟩

end Trivalent

end TwoDim

end ConventionalImplicature
