module

public import Linglib.Logic.Modal.Epistemic
public import Linglib.Discourse.Role
public import Mathlib.Order.Concept

/-!
# Ney (2026): Insinuative reference and the coordination account

In *insinuative reference* ([ney-2026]) a speaker uses a demonstrative, or another expression
whose meaning must be supplemented in context, so that an innocuous *avowable* referent and a
taboo *unavowed* referent are both possible semantic values; she intends the unavowed one and
keeps the ability to deny it. Ney argues that the unavowed referent is a genuine semantic value
(claim (i)), yet after the utterance it is available from the common ground neither that it is
one (iia) nor that the speaker intended it to be (iib). This challenges the coordination account
of [king-2013], on which a use has `o` as its semantic value iff (A) the speaker intends `o` and
(B) a competent, reasonable, attentive hearer who knows the common ground would recognise that
intention: given that the hearer's reasonableness is common ground (⟨TWO⟩), (B) seems to carry
the intention and the reference into the common ground (⟨THREE⟩, ⟨FOUR⟩). Ney's reply is that
the step needs a hidden premise, ⟨TWO*⟩, that it is common ground that a reasonable hearer would
recognise the intention. Each interlocutor has a *conception of reasonableness*, her beliefs
about which referential intentions every reasonable hearer would recognise; the account's
conception is the intersection of the interlocutors'; and in insinuative reference the
interlocutors share the relevant conception without that being common ground.

Hearers and the intentions they would recognise form a formal context in the sense of
`Mathlib.Order.Concept`: the hearers reasonable by a conception's lights are its `lowerPolar`,
and (B) over a set of hearers is membership in its `upperPolar`. The revised account
(`Model.semanticValues`) quantifies over the hearers reasonable by the lights of at least one
interlocutor, as Ney's revised statement does, and for conceptions closed under recognition this
is the intersection of the conceptions (`Model.semanticValues_eq`); without closure the
intersection formulation is strictly stronger (`exists_mem_upperPolar_iUnion_not_mem`). The
chain is `Model.commonKnowledge_mem_recognized` (⟨TWO⟩ and ⟨TWO*⟩ give ⟨THREE⟩) and
`Model.commonKnowledge_mem_intends` (⟨THREE⟩ contradicts (iib)). The reply is
`Model.not_commonKnowledge_mem_semanticValues` and `Model.not_commonKnowledge_mem_intends`: a
conception that is not common ground blocks (iia), and the speaker's blocks (iib). On a frame
where each interlocutor knows her own conception and nothing about the other's, example (2)
satisfies claim (i), ⟨TWO⟩, (iia) and (iib) together, with the speaker privately believing
that the addressee recognises her intention (`insinuation`). On the same frame, the John Lennon
example, whose referent every conception licenses, reaches the common ground (`lennon`).
Deniability therefore sits in ⟨TWO*⟩ rather than ⟨TWO⟩, which is why denying ⟨TWO⟩, Ney's
rejected first pass, would make the Lennon reference deniable too.

## Implementation notes

A model fixes one use of a supplementive, so a conception of reasonableness restricted to the
use is a set of candidate referents. What King's idealised hearer knows of the common ground,
and the audience properties the common ground attributes to them ([king-2014b], via Ney's
footnote 1), are absorbed into the recognition relation. The common ground is common knowledge
among the interlocutors, the iterated mutual acceptance Ney describes ([stalnaker-2002]), and
accessibility is read as "for all `a` knows", the modality of Ney's reasoning for ⟨TWO*⟩; the
`Filter` common ground of `Discourse.CommonGround` inherits the results through
`Filter.GroundedIn` (`insinuation.not_mem_of_groundedIn`). The speaker's intended referents form
a set, since claim (i) lets avowable referents be semantic values as well. The paper passes from
the intersection of the conceptions to "reasonable by the lights of at least one" with "Thus";
the `IsIntent` field states the closure this step needs, on the reading that a conception's
"implicit and explicit beliefs" include whatever every hearer reasonable by it recognises.

## TODO

Ney's three arguments for claim (i) against reading insinuative reference as indirect speech,
the anaphora argument among them, the dialogue evidence for (iia) and (iib), and the reply
about uptake need an implicature, anaphora and update apparatus; here they are premises. The
distinctions from [camp-2018]'s insinuation and from dogwhistles ([henderson-mccready-2024]) are
not formalized, and the paper's examples are not yet rows of `Data/Examples`.

## References

* [ney-2026]
* [king-2013]
* [king-2014b]
* [stalnaker-2002]
* [camp-2018]
* [henderson-mccready-2024]
-/

@[expose] public section

namespace Ney2026

open Set Discourse Order ModalLogic SetRel

/-! ### Conceptions of reasonableness -/

/-- The intersection formulation ([ney-2026] p. 326) is at least as strong as "reasonable by the
lights of at least one" (p. 327), and strictly stronger for conceptions that are not closed
under recognition: a hearer recognising everything counts as reasonable by either conception
below, a hearer recognising nothing only by their empty intersection. -/
theorem exists_mem_upperPolar_iUnion_not_mem :
    ∃ (r : Bool → Bool → Prop) (K : Role → Set Bool) (e : Bool),
      e ∈ upperPolar r (⋃ a, lowerPolar r (K a)) ∧ e ∉ upperPolar r (lowerPolar r (⋂ a, K a)) := by
  refine ⟨fun h _ ↦ h = true, fun | .speaker => {true} | .addressee => {false}, true, ?_, ?_⟩
  · rintro h ⟨_, ⟨a, rfl⟩, hh⟩
    cases a <;> exact hh rfl
  · intro h
    exact Bool.false_ne_true (h (fun b hb ↦ by cases b <;> simp_all [Role.forall_role]))

/-- A conversation about one use of a supplementive, with worlds `W`, hearers `H` and candidate
semantic values `E`. -/
structure Model (W H E : Type*) where
  /-- `w ~[belief a] v`: at `w`, for all `a` knows, the world is `v`. -/
  belief : Role → SetRel W W
  /-- `recognizes h e`: hearer `h` would recognise an intention to make `e` the semantic value. -/
  recognizes : H → E → Prop
  /-- `a`'s conception of reasonableness at `w`, restricted to the use: the referents such that,
  by `a`'s lights, every reasonable hearer would recognise an intention to refer to them
  ([ney-2026] p. 326). -/
  conception : Role → W → Set E
  /-- A conception contains whatever every hearer reasonable by its lights recognises. -/
  isIntent_conception : ∀ a w, IsIntent recognizes (conception a w)
  /-- The referents the speaker intends to be semantic values of the use. -/
  intends : W → Set E
  /-- The speaker intends only what, by her own lights, a reasonable hearer would recognise:
  otherwise the utterance would not be an apt way to refer ([ney-2026] p. 326). -/
  intends_subset_conception : ∀ w, intends w ⊆ conception .speaker w
  /-- The actual addressee. -/
  addressee : W → H

namespace Model

variable {W H E : Type*} (M : Model W H E) {o : E} {w : W}

/-! ### The revised coordination account -/

/-- The hearers reasonable by the lights of at least one interlocutor ([ney-2026] p. 327). -/
def reasonable (w : W) : Set H := ⋃ a, lowerPolar M.recognizes (M.conception a w)

/-- A hearer reasonable by either interlocutor's lights is reasonable by the intersection of
their conceptions ([ney-2026] p. 326). -/
theorem reasonable_subset (w : W) :
    M.reasonable w ⊆ lowerPolar M.recognizes (⋂ a, M.conception a w) :=
  iUnion_subset fun a ↦ lowerPolar_anti _ (iInter_subset _ a)

/-- The semantic values of the use at `w` on the revised coordination account ([ney-2026]
p. 327): the referents the speaker intends whose intended reference every hearer reasonable by
the lights of at least one interlocutor would recognise. -/
def semanticValues (w : W) : Set E := M.intends w ∩ upperPolar M.recognizes (M.reasonable w)

/-- The relevant conception is the intersection of the interlocutors' ([ney-2026] p. 326). -/
theorem semanticValues_eq (w : W) :
    M.semanticValues w = M.intends w ∩ ⋂ a, M.conception a w := by
  simp only [semanticValues, reasonable, upperPolar_iUnion,
    fun a ↦ isIntent_iff.1 (M.isIntent_conception a w)]

@[simp] theorem mem_semanticValues :
    o ∈ M.semanticValues w ↔ o ∈ M.intends w ∧ ∀ a, o ∈ M.conception a w := by
  simp [semanticValues_eq]

theorem semanticValues_subset_intends (w : W) : M.semanticValues w ⊆ M.intends w :=
  inter_subset_left

/-- The referents whose intended reference the addressee recognises. -/
def recognized (w : W) : Set E := M.intends w ∩ {e | M.recognizes (M.addressee w) e}

/-! ### The prima facie challenge -/

/-- ⟨TWO⟩ and ⟨TWO*⟩ give ⟨THREE⟩ ([ney-2026] pp. 322, 325): if it is common ground that the
addressee is reasonable and that `o` is a semantic value, it is common ground that the addressee
recognises the intention to refer to `o`. -/
theorem commonKnowledge_mem_recognized
    (two : CommonKnowledge M.belief univ (fun v ↦ M.addressee v ∈ M.reasonable v) w)
    (twoStar : CommonKnowledge M.belief univ (o ∈ M.semanticValues ·) w) :
    CommonKnowledge M.belief univ (o ∈ M.recognized ·) w :=
  fun v hv ↦ ⟨(twoStar v hv).1, (twoStar v hv).2 (two v hv)⟩

/-- ⟨THREE⟩ is incompatible with (iib) ([ney-2026] p. 322): a common-ground recognition of the
intention makes the intention common ground. -/
theorem commonKnowledge_mem_intends
    (three : CommonKnowledge M.belief univ (o ∈ M.recognized ·) w) :
    CommonKnowledge M.belief univ (o ∈ M.intends ·) w :=
  fun v hv ↦ (three v hv).1

/-! ### The response -/

/-- If it is not common ground that `a`'s conception licenses `o`, it is not common ground that
`o` is a semantic value (iia): ⟨TWO*⟩ fails ([ney-2026] pp. 325–326). -/
theorem not_commonKnowledge_mem_semanticValues (a : Role)
    (h : ¬ CommonKnowledge M.belief univ (o ∈ M.conception a ·) w) :
    ¬ CommonKnowledge M.belief univ (o ∈ M.semanticValues ·) w :=
  fun hv ↦ h fun v h' ↦ (M.mem_semanticValues.1 (hv v h')).2 a

/-- If it is not common ground that the speaker's conception licenses `o`, it is not common
ground that she intends `o` (iib): she can deny the intention by denying the conception
([ney-2026] p. 326). -/
theorem not_commonKnowledge_mem_intends
    (h : ¬ CommonKnowledge M.belief univ (o ∈ M.conception .speaker ·) w) :
    ¬ CommonKnowledge M.belief univ (o ∈ M.intends ·) w :=
  fun hi ↦ h fun v h' ↦ M.intends_subset_conception v (hi v h')

end Model

theorem isIntent_mem {E : Type*} (C : Set E) : IsIntent (fun (h : Set E) e ↦ e ∈ h) C :=
  isIntent_iff.2 <| ext fun _ ↦ ⟨fun h ↦ h fun _ hb ↦ hb, fun he _ hC ↦ hC he⟩

/-! ### Private conceptions -/

/-- A world records which interlocutors hold a conception licensing the unavowed referent. -/
abbrev World := Finset Role

/-- Each interlocutor knows whether she holds the conception and nothing about the other. -/
def privately (a : Role) : SetRel World World := {p | a ∈ p.1 ↔ a ∈ p.2}

instance (a : Role) : IsS5Frame (privately a) where
  refl _ := Iff.rfl
  eucl _ _ _ h₁ h₂ := h₁.symm.trans h₂

/-! ### Example (2) -/

/-- The possible referents of *they* in (2), "They are crossing the border, bringing drugs,
disease and crime" ([ney-2026] p. 307): the unavowed Hispanic immigrants and the avowable gang
members and drug smugglers (p. 308). -/
inductive Referent where
  | hispanicImmigrants
  | smugglers

open Referent

/-- Example (2): every conception licenses the avowable referent, and the insinuative one also
licenses the unavowed referent; the speaker intends the unavowed referent when her conception
licenses it and the avowable one otherwise; the addressee recognises what either conception
requires. -/
def insinuation : Model World (Set Referent) Referent where
  belief := privately
  recognizes h e := e ∈ h
  conception a w := {e | e = smugglers ∨ a ∈ w}
  isIntent_conception _ _ := isIntent_mem _
  intends w := {if .speaker ∈ w then hispanicImmigrants else smugglers}
  intends_subset_conception w e he := by
    simp only [mem_singleton_iff] at he
    split_ifs at he with h <;> simp [he, h]
  addressee w := {e | e = smugglers ∨ .speaker ∈ w ∨ .addressee ∈ w}

namespace insinuation

/-- In fact both interlocutors hold the conception ([ney-2026] p. 326). -/
theorem mem_conception (a : Role) : hispanicImmigrants ∈ insinuation.conception a .univ := by
  simp [insinuation]

theorem mem_semanticValues : hispanicImmigrants ∈ insinuation.semanticValues .univ := by
  simp [insinuation]

/-- The speaker does not know the addressee shares her conception ([ney-2026] p. 326). -/
theorem not_knows_speaker :
    ¬ □[insinuation.belief .speaker] (hispanicImmigrants ∈ insinuation.conception .addressee ·)
      .univ :=
  fun h ↦ by simpa [insinuation] using h {.speaker} (by simp [insinuation, privately])

/-- The addressee does not know the speaker shares hers ([ney-2026] p. 326). -/
theorem not_knows_addressee :
    ¬ □[insinuation.belief .addressee] (hispanicImmigrants ∈ insinuation.conception .speaker ·)
      .univ :=
  fun h ↦ by simpa [insinuation] using h {.addressee} (by simp [insinuation, privately])

/-- The speaker knows that the addressee recognises the unavowed intention, an individual
belief ([ney-2026] p. 325). -/
theorem knows_mem_recognized :
    □[insinuation.belief .speaker] (hispanicImmigrants ∈ insinuation.recognized ·) .univ :=
  fun v hv ↦ by
    have hs : .speaker ∈ v := (show (.univ, v) ∈ privately .speaker from hv).1 (Finset.mem_univ _)
    simp [insinuation, Model.recognized, hs]

/-- For all the addressee knows, the speaker does not know that the addressee recognises the
unavowed intention ([ney-2026] p. 325). -/
theorem not_knows_knows_mem_recognized :
    ¬ □[insinuation.belief .addressee]
      (□[insinuation.belief .speaker] (hispanicImmigrants ∈ insinuation.recognized ·)) .univ :=
  fun h ↦ by
    simpa [insinuation, Model.recognized] using h {.addressee} (by simp [insinuation, privately])
      {.addressee} (by simp [insinuation, privately])

/-- ⟨TWO⟩: it is common ground that the addressee is reasonable ([ney-2026] p. 325). -/
theorem commonKnowledge_two :
    CommonKnowledge insinuation.belief univ
      (fun v ↦ insinuation.addressee v ∈ insinuation.reasonable v) .univ :=
  fun _ _ ↦ mem_iUnion.2 ⟨.addressee, fun _ he ↦ by
    rcases he with he | he <;> simp [insinuation, he]⟩

theorem not_commonKnowledge_mem_semanticValues :
    ¬ CommonKnowledge insinuation.belief univ (hispanicImmigrants ∈ insinuation.semanticValues ·)
      .univ :=
  Model.not_commonKnowledge_mem_semanticValues _ .addressee <|
    mt (box_of_commonKnowledge (mem_univ .speaker)) not_knows_speaker

theorem not_commonKnowledge_mem_intends :
    ¬ CommonKnowledge insinuation.belief univ (hispanicImmigrants ∈ insinuation.intends ·)
      .univ :=
  Model.not_commonKnowledge_mem_intends _ <|
    mt (box_of_commonKnowledge (mem_univ .addressee)) not_knows_addressee

theorem not_mem_of_groundedIn {cg : Filter World} (h : cg.GroundedIn insinuation.belief univ)
    (hw : Finset.univ ∈ cg.ker) : {v | hispanicImmigrants ∈ insinuation.intends v} ∉ cg :=
  fun hp ↦ not_commonKnowledge_mem_intends (h.commonKnowledge hw hp)

/-- The eavesdropper ([ney-2026] pp. 325–326): where only the speaker holds the conception, the
addressee recognises the intention, yet the unavowed referent is not a semantic value. -/
theorem eavesdropper :
    hispanicImmigrants ∈ insinuation.recognized {.speaker} ∧
      hispanicImmigrants ∉ insinuation.semanticValues {.speaker} := by
  simp [insinuation, Model.recognized]

end insinuation

/-! ### The Lennon example -/

/-- The possible referents in "this is where John Lennon was born", said pointing across a
busy street ([ney-2026] p. 324). -/
inductive LennonReferent where
  | house
  | car

open LennonReferent

/-- The Lennon example on the same frame: every conception licenses the house. -/
def lennon : Model World (Set LennonReferent) LennonReferent where
  belief := privately
  recognizes h e := e ∈ h
  conception _ _ := {house}
  isIntent_conception _ _ := isIntent_mem _
  intends _ := {house}
  intends_subset_conception _ := subset_rfl
  addressee _ := {house}

/-- With ⟨TWO⟩ as in example (2), the reference to the house is common ground: denying ⟨TWO*⟩,
not ⟨TWO⟩, separates insinuative reference from ordinary reliance on a reasonable hearer
([ney-2026] p. 324). -/
theorem lennon_commonKnowledge_mem_recognized :
    CommonKnowledge lennon.belief univ (house ∈ lennon.recognized ·) .univ :=
  lennon.commonKnowledge_mem_recognized
    (fun _ _ ↦ mem_iUnion.2 ⟨.speaker, fun _ ↦ id⟩) fun _ _ ↦ by simp [lennon]

end Ney2026
