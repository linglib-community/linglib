module

public import Linglib.Syntax.Cat
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Semantics.Presupposition.Strengthening
public import Linglib.Data.Examples.LoGuercio2025

/-!
# Lo Guercio (2025): Maximize Conventional Implicatures!

This file formalizes Lo Guercio's anti-conventional implicatures: scalar
inferences that arise from comparing the conventionally implicated content of formal
alternatives, as scalar implicatures compare at-issue content and antipresuppositions
presuppositional content. Conventionally implied meaning is a restriction on the contexts
of felicitous use, so one sentence has stronger such content than another when its felicity
set is a proper subset of the other's, and the principle Maximize Conventional Implicatures!
forbids a sentence when a formal alternative in the sense of Katzir and of Fox and
Katzir, one no more complex than it, has stronger content. All three principles
have this form, here along conventional-implicature content (`Blocked`), and
`Presupposition.strengthen` computes the inference along it as along presuppositions.

The worked case is the epithet. Out of the blue, *John arrived first* carries no inference
that John is no bastard, because *that bastard John arrived first* is not a formal
alternative: the epithet construction is a determiner phrase with three daughters, which no
chain of deletions, contractions, and substitutions from a source of lexical items and
one-daughter phrases can build (`outOfBlue_no_ACI`, through
`no_wideDP_outOfBlue`). Once *that bastard Pedro* has been
mentioned, its phrase enters the substitution source, the epithet alternative is derived by
substituting it for the subject and then *John* for *Pedro*, the paper's derivation (24)
(`epithet_alternative_priorMention`), and the inference arises (`priorMention_yes_ACI`): the
bare sentence is then used exactly where the speaker does not hold the attitude
(`strengthen_priorMention`), where out of the blue it is used whatever the attitude
(`strengthen_outOfBlue`).

## Implementation notes

The felicity-set semantics of the paper's (12) is `expressiveCI`: a sentence is felicitous
at a world unless it contains the epithet construction and the speaker does not hold the
attitude there. The honorific *don/doña* of the paper's §3.2.1, the Japanese honorifics of
its §3.2.2, the expressive adjectives of its §3.2.4, and the embeddability and oddness
discussion of its §4 are rows of `Data/Examples/LoGuercio2025.json` and prose, not
theorems.

## References

* [lo-guercio-2025]
* [katzir-2007]
* [fox-katzir-2011]
* [gutzmann-2015]
* [kaplan-1999]
-/

@[expose] public section

namespace LoGuercio2025

open PhraseStructure.Tree Presupposition
open PhraseStructure

/-! ### The epithet as a structural alternative -/

/-- Vocabulary for the epithet example. -/
inductive EWord where
  | john | pedro | arrived | first | andThen
  | that_ | bastard
  deriving DecidableEq, Repr

instance : BEq EWord := ⟨fun a b ↦ decide (a = b)⟩
instance : LawfulBEq EWord where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

open EWord

/-- The lexical items, terminals only. -/
def epithetLex : Finset (Tree Cat EWord) :=
  {.terminal .N .john, .terminal .N .pedro,
   .terminal .V .arrived, .terminal .Adv .first,
   .terminal .Conj .andThen,
   .terminal .Det .that_, .terminal .N .bastard}

/-- The predicate *arrived first*. -/
def arrivedFirst : Tree Cat EWord := .node .V [.terminal .V .arrived, .terminal .Adv .first]

/-- *[DP John] arrived first*, the first conjunct of the paper's (20a) as its (24) parses it. -/
def johnArrived : Tree Cat EWord := .node .S [.node .Det [.terminal .N .john], arrivedFirst]

/-- *[DP that bastard John] arrived first*, the paper's (20b). -/
def bastardJohnArrived : Tree Cat EWord :=
  .node .S [.node .Det [.terminal .Det .that_, .terminal .N .bastard, .terminal .N .john],
    arrivedFirst]

/-- *[DP that bastard Pedro]*, mentioned in the second conjunct of (20a). -/
def bastardPedroDP : Tree Cat EWord :=
  .node .Det [.terminal .Det .that_, .terminal .N .bastard, .terminal .N .pedro]

/-- *[DP that bastard Pedro] arrived first*, the intermediate step of the derivation (24). -/
def bastardPedroArrived : Tree Cat EWord := .node .S [bastardPedroDP, arrivedFirst]

/-- After the mention the substitution source holds the lexical items and the contextually
relevant epithet phrase ([fox-katzir-2011]). -/
def priorContextLex : Finset (Tree Cat EWord) :=
  insert bastardPedroDP epithetLex

/-- A determiner phrase with at least two daughters. -/
def WideDP (t : Tree Cat EWord) : Prop := t.cat = .Det ∧ 2 ≤ t.children.length

/-- The epithet construction is a determiner phrase *that bastard X*. -/
def IsEpithet : Tree Cat EWord → Prop
  | .node .Det [.terminal .Det .that_, .terminal .N .bastard, _] => True
  | _ => False

instance : DecidablePred WideDP := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsEpithet := fun t ↦ by unfold IsEpithet; split <;> infer_instance

theorem WideDP.of_isEpithet {t : Tree Cat EWord} (h : IsEpithet t) : WideDP t := by
  unfold IsEpithet at h; split at h
  · exact ⟨rfl, by simp⟩
  · exact h.elim

/-- A tree contains the epithet construction. -/
def HasEpithet (φ : Tree Cat EWord) : Prop := ∃ s ∈ φ.subtrees, IsEpithet s

instance : DecidablePred HasEpithet := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem no_wideDP_outOfBlue {ψ : Tree Cat EWord}
    (h : ψ ∈ structuralAlternatives epithetLex johnArrived) : ∀ t ∈ ψ.subtrees, ¬ WideDP t := by
  have key {t : Tree Cat EWord} :
      t.Licensed (fun l ks ↦ ¬ (Label.cat l = Cat.Det ∧ 2 ≤ ks.length)) ↔
        ∀ s ∈ t.subtrees, ¬ WideDP s :=
    RoseTree.licensed_iff_forall_mem_subtrees.trans
      (forall₂_congr fun _ _ ↦ by simp [WideDP, Tree.cat])
  refine key.1 (licensed_of_atMostAsComplex (fun s hs ↦ key.2 ?_)
    (fun _ ks i _ h ⟨h1, h2⟩ ↦ h ⟨h1, ?_⟩)
    (fun _ _ _ _ _ _ h ⟨h1, h2⟩ ↦ h ⟨h1, by simpa using h2⟩) (key.2 (by decide)) h)
  · revert s hs
    exact forall_mem_substitutionSource.2 ⟨by decide, by decide⟩
  · have := List.length_eraseIdx_le ks i
    omega

theorem epithet_not_alternative_outOfBlue :
    bastardJohnArrived ∉ structuralAlternatives epithetLex johnArrived :=
  fun h ↦ no_wideDP_outOfBlue h (Tree.node .Det [.terminal .Det .that_, .terminal .N .bastard,
    .terminal .N .john]) (by decide) (by decide)

/-- After the mention, the epithet sentence is a structural alternative by derivation (24). -/
theorem epithet_alternative_priorMention :
    bastardJohnArrived ∈ structuralAlternatives priorContextLex johnArrived := by
  have step1 : RoseTree.Rewrites (StructuralOp (substitutionSource priorContextLex johnArrived))
      johnArrived bastardPedroArrived :=
    RoseTree.Rewrites.set _ (cs := [Tree.node Cat.Det [Tree.terminal Cat.N john], arrivedFirst])
      ⟨0, by decide⟩
      (.here (StructuralOp.subst rfl (Set.mem_union_left _ (by simp [priorContextLex]))))
  have step2 : RoseTree.Rewrites (StructuralOp (substitutionSource priorContextLex johnArrived))
      bastardPedroArrived bastardJohnArrived :=
    RoseTree.Rewrites.set _ (cs := [bastardPedroDP, arrivedFirst]) ⟨0, by decide⟩
      (RoseTree.Rewrites.set _ (cs := [Tree.terminal Cat.Det that_, Tree.terminal Cat.N bastard,
          Tree.terminal Cat.N pedro]) ⟨2, by decide⟩
        (.here (StructuralOp.subst rfl
          (Set.mem_union_left _ (by simp [priorContextLex, epithetLex])))))
  exact Relation.ReflTransGen.head step1 (Relation.ReflTransGen.single step2)

/-! ### Conventionally implicated content as felicity sets -/

/-- The worlds settle whether the speaker believes that John is a bastard. -/
abbrev World : Type := Bool

/-- Under the felicity-set content of the paper's (12), a sentence with the epithet construction is
felicitous only where the speaker holds the attitude; any other sentence is felicitous
everywhere. -/
def expressiveCI (φ : Tree Cat EWord) : Set World := {w | HasEpithet φ → w = true}

theorem epithet_ciStronger_than_bare :
    expressiveCI bastardJohnArrived ⊂ expressiveCI johnArrived :=
  LE.le.ssubset_of_not_superset (fun _ _ h ↦ absurd h (by decide))
    (Set.not_subset.2 ⟨false, fun h ↦ absurd h (by decide),
      fun h ↦ Bool.false_ne_true (h (by decide))⟩)

/-! ### The inference -/

/-- Maximize Conventional Implicatures! forbids a sentence with a formal alternative of strictly
stronger conventional-implicature content. -/
def Blocked (lex : Finset (Tree Cat EWord)) (φ : Tree Cat EWord) : Prop :=
  ∃ φ' ∈ structuralAlternatives lex φ, expressiveCI φ' ⊂ expressiveCI φ

/-- Out of the blue the bare sentence does not violate the principle, since every formal
alternative is free of the epithet construction, so none has stronger content. -/
theorem outOfBlue_no_ACI :
    ¬ Blocked epithetLex johnArrived := by
  rintro ⟨φ', hφ', hss⟩
  obtain ⟨w, -, h_alt⟩ := Set.not_subset.1 hss.2
  exact h_alt fun ⟨s, hs, hse⟩ ↦ absurd (WideDP.of_isEpithet hse) (no_wideDP_outOfBlue hφ' s hs)

/-- After the mention the bare sentence violates the principle, since the epithet sentence is a
formal alternative with stronger content. -/
theorem priorMention_yes_ACI :
    Blocked priorContextLex johnArrived :=
  ⟨bastardJohnArrived, epithet_alternative_priorMention, epithet_ciStronger_than_bare⟩

private theorem expressiveCI_johnArrived : expressiveCI johnArrived = Set.univ :=
  Set.eq_univ_of_forall fun _ h ↦ absurd h (by decide)

theorem strengthen_outOfBlue :
    strengthen (structuralAlternatives epithetLex) expressiveCI johnArrived = Set.univ := by
  rw [strengthen_eq_self fun ψ hψ hss ↦ outOfBlue_no_ACI ⟨ψ, hψ, hss⟩, expressiveCI_johnArrived]

theorem strengthen_priorMention :
    strengthen (structuralAlternatives priorContextLex) expressiveCI johnArrived = {false} := by
  ext w
  cases w
  · simp only [Set.mem_singleton_iff, iff_true]
    refine mem_strengthen_iff.2 ⟨expressiveCI_johnArrived ▸ Set.mem_univ _,
      fun ψ _ hψ hss ↦ hss.ne ?_⟩
    rw [expressiveCI_johnArrived]
    exact Set.eq_univ_of_forall fun _ h ↦ absurd (hψ h) Bool.false_ne_true
  · simp only [Set.mem_singleton_iff, Bool.true_eq_false, iff_false]
    exact Set.disjoint_left.1 (disjoint_strengthen_of_ssubset epithet_alternative_priorMention
      epithet_ciStronger_than_bare) (fun _ ↦ rfl)

end LoGuercio2025
