module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Syntax.Command

/-!
# Höhle (1992): Über Verum-Fokus im Deutschen

This file formalizes [hohle-1992]'s analysis of *verum focus*: the accent on a German finite
verb in initial position, or on a subordinating particle such as *daß*, that highlights a meaning
element VERUM paraphrasable as "it is true that", as in *Karl SCHREIBT ein Drehbuch* replying to
the claim that Karl is writing a screenplay. The paper's argument runs from assumption (13), that
VERUM is assigned to the accented word and highlighted as a semantic focus, to a rejection of the
reading of VERUM as an illocution-type operator: verum focus occurs in embedded verb-second
clauses and on complementizers, and in *er HÖRT ihr nicht zu* VERUM lies in the scope of the
negation, so it must be a truth predicate whose scope follows from the syntax.

The scope rule (60) lets the meaning element of a constituent `K₁` lie in the scope of that of
`K₂` iff `K₁` stands in a structural relation SR to `K₂`; `SR` reads it as c-command with
reconstruction of a fronted finite verb to its trace. On the peripheral structure of (76), a
clause `[Φ Π]` whose position Φ is filled by a complementizer or by a finite verb binding a trace
in Π, the negation in Π c-commands the verb's trace but not Φ, so `Scoping.negOverVerum` is
admissible for verum focus on the finite verb and not for verum focus on *daß*. The felicity
condition is that the background thought, the argument of VERUM, is known from the context
(`Appropriate`); this derives the contrast of (55): after *ich hoffe, daß Karl ihr zuhört*, the
verb-second reply is appropriate and the *daß* reply is not. `IntroducesVerum` is the
non-segmental rule (97) of the final section, which introduces VERUM over any bare Π next to a
non-empty sister; it decides which accents yield verum focus across complementizers, fronted
verbs, relative and interrogative pronouns without a particle, and verb-final verbs.

## Implementation notes

* Clauses are `PhraseStructure.Tree`s over the labels of (76) and (97), with Π flat inside; the
  trace bindings that reconstruction respects are given as an explicit list, footnote 7's
  pseudo-reconstruction, and Höhle's relation SR is left open in the paper.
* VERUM is the identity on propositions, so the two scopings of (56) have the same content
  (`content_focusBackground`) and differ only in what is background.
* "Known from the context" is membership in a set of propositions the context makes known; the
  question under discussion plays no role.
* The assumption of §7 that there is no verum focus on a verb-final finite verb, and the
  copula and full-verb judgments of (71) and (72), are recorded in the example rows only.

## References

* [hohle-1992]
-/

@[expose] public section

namespace Hohle1992

open Core.Order PhraseStructure
open RoseTree (cCommand)

/-! ### The peripheral structure of (76) -/

/-- The constituent labels are the clause, the position in front of Φ holding a Vorfeld constituent
or a relative or interrogative phrase, the peripheral position Φ of (76), its complement Π
(Mittelfeld, verbal complex and Nachfeld), and inside Π the negation particle, the verb position and
other material. -/
inductive Node
  | clause
  | front
  | phi
  | pi
  | neg
  | verb
  | other
  deriving DecidableEq, Repr

/-- In (55a) *er HÖRT ihr nicht zu* the finite verb fills Φ and binds a trace in Π. -/
def fClause : Tree Node String :=
  .node .clause [.terminal .front "er",
    .node .clause [.terminal .phi "hört",
      .node .pi [.terminal .other "ihr", .terminal .neg "nicht", .terminal .other "zu",
        .trace 1 .verb]]]

/-- In (55b) *daß er ihr nicht zuhört* the complementizer fills Φ and binds nothing. -/
def cClause : Tree Node String :=
  .node .clause [.terminal .phi "daß",
    .node .pi [.terminal .other "er", .terminal .other "ihr", .terminal .neg "nicht",
      .terminal .verb "zuhört"]]

/-- In (81) *WER hat den Hund getreten* an interrogative pronoun precedes a filled Φ. -/
def whClause : Tree Node String :=
  .node .clause [.terminal .front "wer",
    .node .clause [.terminal .phi "hat",
      .node .pi [.terminal .other "den", .terminal .other "Hund", .terminal .other "getreten",
        .trace 1 .verb]]]

/-- In (82a) *DER das Buch gelesen hat* a relative pronoun precedes an empty Φ (91ii). -/
def rwClause : Tree Node String :=
  .node .clause [.terminal .front "der",
    .node .clause [.node .phi [],
      .node .pi [.terminal .other "das", .terminal .other "Buch", .terminal .other "gelesen",
        .terminal .verb "hat"]]]

/-- In (77a) and (80a) *der WO das Buch gelesen hat* a relative pronoun stands in front of a Φ
filled by the dialectal relative particle. -/
def woClause : Tree Node String :=
  .node .clause [.terminal .front "der",
    .node .clause [.terminal .phi "wo",
      .node .pi [.terminal .other "das", .terminal .other "Buch", .terminal .other "gelesen",
        .terminal .verb "hat"]]]

/-- In (68b) *daß sie damit aufHÖRT* the finite verb stays in final position inside Π. -/
def finalClause : Tree Node String :=
  .node .clause [.terminal .phi "daß",
    .node .pi [.terminal .other "sie", .terminal .other "damit", .terminal .other "auf",
      .terminal .verb "hört"]]

/-! ### The scope rule (60) -/

/-- The relation SR of (60), read as c-command with reconstruction (footnote 7). `k₁` stands
in SR to `k₂` in `t` when `k₂` c-commands `k₁` or a trace that `k₁` binds. -/
def SR (t : Tree Node String) (binds : List (TreePath × TreePath)) (k₁ k₂ : TreePath) : Prop :=
  (k₂, k₁) ∈ cCommand t ∨ ∃ b ∈ binds, b.1 = k₁ ∧ (k₂, b.2) ∈ cCommand t

instance (t : Tree Node String) (binds : List (TreePath × TreePath)) (k₁ k₂ : TreePath) :
    Decidable (SR t binds k₁ k₂) := by
  unfold SR; infer_instance

/-- A negated clause with verum focus records its tree, the trace bindings, the position of the
accented word carrying VERUM and the position of the negation particle. -/
structure Configuration where
  tree : Tree Node String
  binds : List (TreePath × TreePath)
  focus : TreePath
  neg : TreePath

/-- In (55a) verum focus is on the fronted finite verb, reconstructed to its trace. -/
def negatedF : Configuration := ⟨fClause, [(⟨[1, 0]⟩, ⟨[1, 1, 3]⟩)], ⟨[1, 0]⟩, ⟨[1, 1, 1]⟩⟩

/-- In (55b) verum focus is on the complementizer. -/
def negatedC : Configuration := ⟨cClause, [], ⟨[0]⟩, ⟨[1, 2]⟩⟩

/-- The two scopings of VERUM relative to the negation, paraphrased in (56a) and (56b). -/
inductive Scoping
  | negOverVerum
  | verumOverNeg
  deriving DecidableEq

/-- Applied to VERUM and the negation, (60) says that VERUM may lie in the scope of the negation iff
the accented constituent stands in SR to the negation particle, and conversely. -/
def Scoping.Admissible (c : Configuration) : Scoping → Prop
  | .negOverVerum => SR c.tree c.binds c.focus c.neg
  | .verumOverNeg => SR c.tree c.binds c.neg c.focus

instance (c : Configuration) (s : Scoping) : Decidable (s.Admissible c) := by
  cases s <;> unfold Scoping.Admissible <;> infer_instance

/-- The negation of (55a) c-commands the trace of the fronted verb, so VERUM may lie in its
scope. -/
theorem negOverVerum_admissible_negatedF : Scoping.negOverVerum.Admissible negatedF := by decide

theorem verumOverNeg_admissible_negatedF : Scoping.verumOverNeg.Admissible negatedF := by decide

/-- The complementizer of (55b) neither is c-commanded by the negation nor binds a trace, so
VERUM cannot lie in the negation's scope. -/
theorem not_negOverVerum_admissible_negatedC : ¬ Scoping.negOverVerum.Admissible negatedC := by
  decide

theorem verumOverNeg_admissible_negatedC : Scoping.verumOverNeg.Admissible negatedC := by decide

/-! ### Focus–background structure and appropriateness -/

/-- Höhle's class WF of meaning elements by which a speaker signals an attitude to the truth of
a thought, each occurring as `E(p)` and recursively embeddable; the scope data use VERUM, a
truth predicate, and the negation. -/
inductive WF
  | verum
  | neg

variable {W : Type*}

/-- The extension of a WF element. VERUM, a truth predicate, maps a thought to itself. -/
def WF.apply : WF → Set W → Set W
  | .verum, p => p
  | .neg, p => pᶜ

/-- A focus–background structure consists of the highlighted chain of WF elements, outermost
first, and the background thought they apply to. -/
structure FocusBackground (W : Type*) where
  focus : List WF
  background : Set W

/-- The content expressed by a focus–background structure. -/
def FocusBackground.content (s : FocusBackground W) : Set W :=
  s.focus.foldr WF.apply s.background

/-- By (56), with VERUM in the scope of the negation, the negation joins the highlighted part and
the background is the thought `p` itself; with VERUM above the negation, the background is the
negated thought. -/
def Scoping.focusBackground (p : Set W) : Scoping → FocusBackground W
  | .negOverVerum => ⟨[.neg, .verum], p⟩
  | .verumOverNeg => ⟨[.verum], pᶜ⟩

/-- VERUM is truth-conditionally inert, so the two scopings of (56) express the same content and
differ only in what is background. -/
theorem content_focusBackground (p : Set W) (s : Scoping) :
    (s.focusBackground p).content = pᶜ := by
  cases s <;> rfl

/-- Höhle's condition on verum focus is that the background thought is known from the context. A
negated clause expressing the thought `p` is appropriate when some scoping that (60) admits
has its background among the propositions `known` from the context. -/
def Appropriate (known : Set (Set W)) (c : Configuration) (p : Set W) : Prop :=
  ∃ s : Scoping, s.Admissible c ∧ (s.focusBackground p).background ∈ known

theorem appropriate_negatedF_iff (known : Set (Set W)) (p : Set W) :
    Appropriate known negatedF p ↔ p ∈ known ∨ pᶜ ∈ known := by
  constructor
  · rintro ⟨s, -, hs⟩
    cases s
    · exact Or.inl hs
    · exact Or.inr hs
  · rintro (h | h)
    · exact ⟨.negOverVerum, negOverVerum_admissible_negatedF, h⟩
    · exact ⟨.verumOverNeg, verumOverNeg_admissible_negatedF, h⟩

theorem appropriate_negatedC_iff (known : Set (Set W)) (p : Set W) :
    Appropriate known negatedC p ↔ pᶜ ∈ known := by
  constructor
  · rintro ⟨s, hs, hb⟩
    cases s
    · exact absurd hs not_negOverVerum_admissible_negatedC
    · exact hb
  · exact fun h ↦ ⟨.verumOverNeg, verumOverNeg_admissible_negatedC, h⟩

/-- In (55a) after (55c), *ich hoffe, daß Karl ihr zuhört* makes the thought known, and the
verb-second reply *er HÖRT ihr nicht zu* is appropriate. -/
theorem appropriate_negatedF_singleton (p : Set W) : Appropriate {p} negatedF p :=
  (appropriate_negatedF_iff _ p).2 (Or.inl rfl)

/-- In (55b) after (55c), *daß er ihr nicht zuhört* is inappropriate, since the negated thought is
not known. -/
theorem not_appropriate_negatedC_singleton [Nonempty W] (p : Set W) :
    ¬ Appropriate {p} negatedC p := by
  rw [appropriate_negatedC_iff, Set.mem_singleton_iff]
  intro h
  obtain ⟨w⟩ := ‹Nonempty W›
  by_cases hw : w ∈ p
  · have hw' := hw
    rw [← h] at hw'
    exact hw' hw
  · have hw' : w ∈ pᶜ := hw
    rw [h] at hw'
    exact hw hw'

/-! ### The non-segmental introduction of VERUM (97) -/

/-- A tree is phonologically empty when its yield is empty. -/
def PhonEmpty (t : Tree Node String) : Prop := t.yield = []

instance (t : Tree Node String) : Decidable (PhonEmpty t) := by unfold PhonEmpty; infer_instance

/-- A constituent of the form `[σ Π σ]` with `σ` phonologically empty is a `Π` itself, or a node
among whose daughters is a `Π` and the others are phonologically empty. -/
def IsBarePi (t : Tree Node String) : Prop :=
  t.cat = .pi ∨
    ∃ c ∈ t.children, Tree.cat c = .pi ∧ ∀ d ∈ t.children, Tree.cat d ≠ .pi → PhonEmpty d

instance (t : Tree Node String) : Decidable (IsBarePi t) := by unfold IsBarePi; infer_instance

/-- By (97), in a local tree `[Kₖ Kⱼ Kᵢ]` whose second daughter is a bare `Π` and whose first
daughter is not phonologically empty, VERUM is introduced over the translation of `Kᵢ`; by (98ii)
it is assigned to `Kⱼ`, so an accent on `Kⱼ` yields verum focus. -/
def IntroducesVerum (t : Tree Node String) (kj : TreePath) : Prop :=
  match kj.toList.getLast?, t.subtreeAt kj.toList.dropLast with
  | some 0, some (Tree.node _ [a, b]) => ¬ PhonEmpty a ∧ IsBarePi b
  | _, _ => False

instance (t : Tree Node String) (kj : TreePath) : Decidable (IntroducesVerum t kj) := by
  unfold IntroducesVerum; split <;> infer_instance

/-- The fronted finite verb of (55a) is the non-empty sister of Π. -/
theorem introducesVerum_fClause_phi : IntroducesVerum fClause ⟨[1, 0]⟩ := by decide

/-- The complementizer of (55b) is the non-empty sister of Π. -/
theorem introducesVerum_cClause_phi : IntroducesVerum cClause ⟨[0]⟩ := by decide

/-- In (77a) the relative particle *wo* filling Φ carries VERUM. -/
theorem introducesVerum_woClause_phi : IntroducesVerum woClause ⟨[1, 0]⟩ := by decide

/-- In (82a) the relative pronoun in front of an empty Φ carries VERUM, the RW-verum focus of
§9. -/
theorem introducesVerum_rwClause_front : IntroducesVerum rwClause ⟨[0]⟩ := by decide

/-- In (80a), with the particle *wo* filling Φ, the relative pronoun's sister is not a bare Π, so
its accent yields no verum focus. -/
theorem not_introducesVerum_woClause_front : ¬ IntroducesVerum woClause ⟨[0]⟩ := by decide

/-- In (81) the interrogative pronoun in front of a fronted verb yields no verum focus. -/
theorem not_introducesVerum_whClause_front : ¬ IntroducesVerum whClause ⟨[0]⟩ := by decide

/-- In (68b) the verb-final finite verb inside Π yields no verum focus. -/
theorem not_introducesVerum_finalClause_verb : ¬ IntroducesVerum finalClause ⟨[1, 3]⟩ := by
  decide

end Hohle1992
