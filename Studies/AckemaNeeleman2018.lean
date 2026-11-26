module

public import Linglib.Data.Examples.AckemaNeeleman2018
public import Linglib.Data.Examples.Readers
public import Linglib.Languages.Dutch.Pronouns
public import Linglib.Languages.English.Pronouns
public import Linglib.Morphology.Exponence.SubsetRule
public import Linglib.Morphology.Word.Leipzig
public import Linglib.Syntax.Feature.Person.Configuration
public import Linglib.Syntax.Feature.Person.Specification
public import Studies.Cysouw2003
public import Studies.Harbour2016

/-!
# Ackema and Neeleman (2018): Features of Person: From the Inventory of Persons to Their Morphological Realization

Ackema and Neeleman derive the inventory of persons from two privative features that act as
partial functions on a layered set, a set with a chain of predecessors: $\mathrm{PROX}(S) =
\mathrm{Pred}(S)$ discards the outermost layer and $\mathrm{DIST}(S) = S - \mathrm{Pred}(S)$
selects it, and neither applies to a set with no predecessor. Their input is the person space,
three nested sets $S_i \subseteq S_{i+u} \subseteq S_{i+u+o}$ with the speaker an obligatory
member of the first and an addressee of the second. The features have an output for five
structures: the third person `[DIST]`, the second `[PROX–DIST]`, the first `[PROX–PROX]`, the
inclusive `[PROX]`, and the structure with no feature.

Number says how many members the output of person has and leaves the set as it is. A number node
is defined on a set $S$ when $|S| \in C$ and $S \neq S_{i+u+o}$, where its features generate the
cardinalities $C$ from the natural numbers: `AUG` keeps the numbers above a reference number
$n_R$, and `MIN` the least number of its input when that is positive, so that `MIN` has no output
unless `AUG` has applied. In a relative number system number sees the output of person and
$n_R$ is the number of the speaker and the addressee in it, where that is positive; in an absolute
system, and with neither in the set, $n_R = 1$. Under Maximal Encoding a number node is used
only for the cardinalities that no node of the language with more features allows. An absolute
system then has no inclusive without number, its two obligatory members exceeding $n_R = 1$,
which leaves three pronouns without number and four with `AUG`; a relative system has the
inclusive of exactly two. The sets a number node is used for are those of the number value it
is named after: the singular, the plural and the dual in an absolute system, and the minimal, the
augmented and the unit augmented in a relative one. Without a dual, the pronouns of an absolute
system divide the referential categories as Cysouw's Mandara type does and those of a relative
system as his Maranao type.

Only `[DIST]` can deliver the empty set, and no number node but the one with no feature allows a
cardinality of zero, so an expletive is a third person pronoun without number. Spell-out rules
mention features with multiplicity, and under Maximal Encoding the applicable rule mentioning the
most is used: Dutch has no rule mentioning two `PROX`, so *wij* realizes both the inclusive and
the exclusive. No natural class holds the inclusive and the second person without the exclusive.
Impoverishing `DIST` under `PROX` in the plural still brings the two together, and it turns a
plural paradigm that Harbour's parameters generate into one they never generate.

## Implementation notes

* A layered set carries its predecessors, so the set a feature leaves unlayered has none. The
  book defines the predecessor on the three sets of the person space.
* A person space is finite, so that the cardinality of a set is a natural number, as the number
  node requires.
* The condition $S \neq S_{i+u+o}$ is read on layered sets: the inclusive delivers $S_{i+u}$ with
  its predecessor, which is not the input of person even in a space with no others.
* Maximal Encoding compares the number nodes of a language on the cardinality they allow, the
  condition on the input of person being common to them, and counts their features.
* The features are defined over any type with a difference, so the same definitions compute the
  participants a structure delivers in the person space of the speaker and the addressee alone.
* The referential categories of a pronoun are read off the configurations with at most three
  others that it covers.
* The impersonal *men* is given the structure with no feature and no number node, the book's
  bare $N_\Pi$; its generic and arbitrary readings are not modelled.
* Gender is not analysed, so the third person singular rule inserts *hij* where the book lists
  *hij*, *zij* and *het*.

## TODO

* The feature `UP` of the trial, and the associative effect in the plural of the first and second
  person.
* The honorific feature and the polite pronouns recruited by impoverishment.
* The context operators that fix the speaker and the addressee, their shifting, and the
  co-incidence of discourse roles in self-talk.

## References

* [P. Ackema and A. Neeleman, *Features of Person: From the Inventory of Persons to Their
  Morphological Realization* (2018)][ackema-neeleman-2018]
* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
* [D. Harbour, *Impossible Persons* (2016)][harbour-2016]
-/

@[expose] public section

namespace AckemaNeeleman2018

open Morphology SpeechAct

variable {α β γ E : Type*}

/-! ### Layered sets and the person features -/

/-- A layered set is a set with the chain of its predecessors, the nearest first. A set with no
predecessor is unlayered. -/
structure Layered (β : Type*) where
  /-- The set itself. -/
  set : β
  /-- `Pred S`, `Pred (Pred S)` and so on. -/
  preds : List β
  deriving DecidableEq

namespace Layered

/-- `Pred S`, with the predecessors that remain. -/
def pred : Layered β → Option (Layered β)
  | ⟨_, []⟩ => none
  | ⟨_, p :: ps⟩ => some ⟨p, ps⟩

/-- The image of a layered set under a map of sets. -/
def map (g : β → γ) (S : Layered β) : Layered γ := ⟨g S.set, S.preds.map g⟩

end Layered

/-- The two privative person features. -/
inductive Feature
  | prox
  | dist
  deriving DecidableEq

section SDiff

variable [SDiff β] [SDiff γ] {S T : Layered β} {fs : List Feature} {g : β → γ}

namespace Feature

/-- (6): `PROX S = Pred S` discards the outermost layer of a layered set and
`DIST S = S − Pred S` selects it, leaving an unlayered set. Neither applies to an unlayered
set. -/
def apply : Feature → Layered β → Option (Layered β)
  | .prox, S => S.pred
  | .dist, S => S.pred.map fun P ↦ ⟨S.set \ P.set, []⟩

theorem length_preds_lt {f : Feature} (h : f.apply S = some T) :
    T.preds.length < S.preds.length := by
  rcases S with ⟨s, _ | ⟨p, ps⟩⟩ <;> cases f <;> simp [apply, Layered.pred] at h <;> simp [← h]

theorem apply_map (hg : ∀ s t, g (s \ t) = g s \ g t) (f : Feature) (S : Layered β) :
    f.apply (S.map g) = (f.apply S).map (.map g) := by
  rcases S with ⟨s, _ | ⟨p, ps⟩⟩ <;> cases f <;> simp [apply, Layered.pred, Layered.map, hg]

end Feature

namespace Layered

/-- The output of a person feature structure on a layered set, its features applied in order. -/
def eval (S : Layered β) (fs : List Feature) : Option (Layered β) :=
  fs.foldlM (fun S f ↦ f.apply S) S

@[simp] theorem eval_nil (S : Layered β) : S.eval [] = some S := rfl

@[simp] theorem eval_cons (S : Layered β) (f : Feature) (fs : List Feature) :
    S.eval (f :: fs) = (f.apply S).bind (·.eval fs) := by
  simp [eval]

-- a structure has an output iff it is no longer than the chain and only its last feature is DIST
theorem isSome_eval_iff :
    (S.eval fs).isSome ↔ fs.length ≤ S.preds.length ∧ ∀ f ∈ fs.dropLast, f = .prox := by
  induction fs generalizing S with
  | nil => simp
  | cons f fs ih =>
    rw [eval_cons]
    rcases S with ⟨s, _ | ⟨p, ps⟩⟩
    · cases f <;> simp [Feature.apply, pred]
    · cases f <;> simp only [Feature.apply, pred, Option.map_some, Option.bind_some, ih] <;>
        cases fs <;> simp

theorem length_preds_add_length_le (h : S.eval fs = some T) :
    T.preds.length + fs.length ≤ S.preds.length := by
  induction fs generalizing S with
  | nil => simp [Option.some.inj h]
  | cons f fs ih =>
    obtain ⟨U, hU, hT⟩ := Option.bind_eq_some_iff.1 (eval_cons S f fs ▸ h)
    grind [f.length_preds_lt hU, ih hT]

theorem eval_eq_some_self_iff : S.eval fs = some S ↔ fs = [] :=
  ⟨fun h ↦ List.length_eq_zero_iff.1 (by have := length_preds_add_length_le h; omega),
    fun h ↦ h ▸ rfl⟩

theorem eval_map (hg : ∀ s t, g (s \ t) = g s \ g t) (S : Layered β) (fs : List Feature) :
    (S.map g).eval fs = (S.eval fs).map (map g) := by
  induction fs generalizing S with
  | nil => rfl
  | cons f fs ih => cases h : f.apply S <;> simp [Feature.apply_map hg, h, ih]

end Layered

end SDiff

/-! ### The person space -/

/-- (4): the person space is a nest of three finite sets. The speaker is an obligatory member
of the innermost, `Sᵢ`, and an addressee of the next, `Sᵢ₊ᵤ`; their other members are associates
of the two, and the remaining members of the whole space `Sᵢ₊ᵤ₊ₒ` are the others. -/
structure PersonSpace (α : Type*) where
  /-- The speaker `i`. -/
  speaker : α
  /-- The addressee `u`. -/
  addressee : α
  /-- `Sᵢ`. -/
  Si : Finset α
  /-- `Sᵢ₊ᵤ`. -/
  Siu : Finset α
  /-- `Sᵢ₊ᵤ₊ₒ`. -/
  Siuo : Finset α
  speaker_mem : speaker ∈ Si
  addressee_mem : addressee ∈ Siu
  addressee_notMem : addressee ∉ Si
  Si_subset : Si ⊆ Siu
  Siu_subset : Siu ⊆ Siuo

namespace PersonSpace

variable (S : PersonSpace α)

/-- (5): the input to the person features is the whole space, with predecessor `Sᵢ₊ᵤ`, whose
predecessor is `Sᵢ`. -/
def layered : Layered (Finset α) := ⟨S.Siuo, [S.Siu, S.Si]⟩

/-- The bearer of a discourse role. -/
def atom : Role → α
  | .speaker => S.speaker
  | .addressee => S.addressee

theorem speaker_ne_addressee : S.speaker ≠ S.addressee := fun h ↦
  S.addressee_notMem (h ▸ S.speaker_mem)

theorem atom_injective : Function.Injective S.atom := by
  rintro (_ | _) (_ | _) h
  exacts [rfl, absurd h S.speaker_ne_addressee, absurd h.symm S.speaker_ne_addressee, rfl]

theorem one_lt_card_Siu : 1 < S.Siu.card :=
  Finset.one_lt_card.2 ⟨_, S.Si_subset S.speaker_mem, _, S.addressee_mem, S.speaker_ne_addressee⟩

theorem one_lt_card_Siuo : 1 < S.Siuo.card :=
  S.one_lt_card_Siu.trans_le (Finset.card_le_card S.Siu_subset)

/-- The person space of the speaker and the addressee alone. -/
def roles : PersonSpace Role :=
  ⟨.speaker, .addressee, {.speaker}, .univ, .univ, Finset.mem_singleton_self _, Finset.mem_univ _,
    by decide, Finset.subset_univ _, subset_rfl⟩

variable [DecidableEq α]

/-- The discourse roles whose bearers are in a set. -/
def rolesIn (s : Finset α) : Finset Role := Finset.univ.filter (S.atom · ∈ s)

/-- The configuration of a set: the discourse roles whose bearers it contains and the number of
its other members. -/
def config (s : Finset α) : Person.Configuration := ⟨S.rolesIn s, s.card - (S.rolesIn s).card⟩

theorem rolesIn_Si : S.rolesIn S.Si = {.speaker} := by
  ext r; cases r <;> simp [rolesIn, atom, S.speaker_mem, S.addressee_notMem]

theorem rolesIn_Siu : S.rolesIn S.Siu = .univ := by
  ext r; cases r <;> simp [rolesIn, atom, S.Si_subset S.speaker_mem, S.addressee_mem]

theorem rolesIn_Siuo : S.rolesIn S.Siuo = .univ := by
  ext r
  cases r <;> simp [rolesIn, atom, S.Siu_subset (S.Si_subset S.speaker_mem),
    S.Siu_subset S.addressee_mem]

theorem rolesIn_sdiff (s t : Finset α) :
    S.rolesIn (s \ t) = S.rolesIn s \ S.rolesIn t := by
  ext; simp [rolesIn]

theorem card_rolesIn_le (s : Finset α) : (S.rolesIn s).card ≤ s.card :=
  Finset.card_le_card_of_injOn S.atom (fun _ hr ↦ (Finset.mem_filter.1 hr).2)
    S.atom_injective.injOn

theorem card_config (s : Finset α) : (S.config s).card = s.card :=
  Nat.add_sub_cancel' (S.card_rolesIn_le s)

end PersonSpace

/-! ### The inventory of persons -/

/-- Third person `[DIST]`. -/
def third : List Feature := [.dist]

/-- Second person `[PROX–DIST]`. -/
def second : List Feature := [.prox, .dist]

/-- First person `[PROX–PROX]`. -/
def first : List Feature := [.prox, .prox]

/-- First person inclusive `[PROX]`. -/
def inclusive : List Feature := [.prox]

/-- The four persons. -/
def persons : List (List Feature) := [inclusive, first, second, third]

section Semantics

variable [DecidableEq α] (S : PersonSpace α) {fs : List Feature} {L : Layered (Finset α)}

theorem eval_third : S.layered.eval third = some ⟨S.Siuo \ S.Siu, []⟩ := rfl

theorem eval_second : S.layered.eval second = some ⟨S.Siu \ S.Si, []⟩ := rfl

theorem eval_first : S.layered.eval first = some ⟨S.Si, []⟩ := rfl

theorem eval_inclusive : S.layered.eval inclusive = some ⟨S.Siu, [S.Si]⟩ := rfl

/-- The person features have an output for exactly five structures, the four persons and the
structure with no feature. -/
theorem isSome_eval_layered_iff :
    (S.layered.eval fs).isSome ↔ fs ∈ [[], inclusive, first, second, third] := by
  rw [Layered.isSome_eval_iff]
  change fs.length ≤ 2 ∧ _ ↔ _
  rcases fs with _ | ⟨f, _ | ⟨g, _ | ⟨h, fs⟩⟩⟩
  · decide
  · cases f <;> decide
  · cases f <;> cases g <;> decide
  · simp [inclusive, first, second, third]

variable {S} in
theorem eq_nil_or_of_eval (h : S.layered.eval fs = some L) :
    fs = [] ∨ fs = inclusive ∨ fs = first ∨ fs = second ∨ fs = third := by
  simpa using (isSome_eval_layered_iff S).1 (Option.isSome_of_eq_some h)

variable {S} in
theorem ne_layered_iff (h : S.layered.eval fs = some L) : L ≠ S.layered ↔ fs ≠ [] :=
  not_congr ⟨fun e ↦ Layered.eval_eq_some_self_iff.1 (e ▸ h), fun e ↦ by simpa [e] using h.symm⟩

variable {S} in
theorem nonempty_of_eval (h : S.layered.eval fs = some L) (hfs : fs ≠ third) : L.set.Nonempty := by
  rcases eq_nil_or_of_eval h with rfl | rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj h
  exacts [Finset.card_pos.1 (Nat.zero_lt_of_lt S.one_lt_card_Siuo),
    Finset.card_pos.1 (Nat.zero_lt_of_lt S.one_lt_card_Siu), ⟨_, S.speaker_mem⟩,
    ⟨_, Finset.mem_sdiff.2 ⟨S.addressee_mem, S.addressee_notMem⟩⟩, absurd rfl hfs]

/-! ### Participants

The speaker and the addressee are placed alike in every person space, so the participants in
the set a feature structure delivers do not depend on the space. -/

/-- The discourse participants in the set a feature structure delivers, computed in the space of
the speaker and the addressee alone. -/
def participants (fs : List Feature) : Option (Finset Role) :=
  (PersonSpace.roles.layered.eval fs).map (·.set)

theorem rolesIn_eval (fs : List Feature) :
    (S.layered.eval fs).map (S.rolesIn ·.set) = participants fs := by
  have h := Layered.eval_map (g := S.rolesIn) S.rolesIn_sdiff S.layered fs
  rw [show S.layered.map S.rolesIn = PersonSpace.roles.layered by
    simp [PersonSpace.layered, Layered.map, S.rolesIn_Si, S.rolesIn_Siu, S.rolesIn_Siuo,
      PersonSpace.roles]] at h
  simp [participants, h, Function.comp_def, Layered.map]

variable {S} in
theorem participants_eq_of_eval (h : S.layered.eval fs = some L) :
    participants fs = some (S.rolesIn L.set) := by
  simpa [h] using (rolesIn_eval S fs).symm

-- the four persons deliver the participant sets of the four person specifications
theorem participants_persons :
    (participants inclusive).toFinset = Person.Specification.firstInclusive.sets ∧
      (participants first).toFinset = Person.Specification.firstExclusive.sets ∧
      (participants second).toFinset = Person.second.participantSets ∧
      (participants third).toFinset = Person.third.participantSets := by
  decide

end Semantics

/-! ### Number

Number is interpreted on the output of the person features, which it leaves as it is. The
features of a number node generate the cardinalities it allows from the natural numbers. -/

/-- The number features. -/
inductive NumberFeature
  | aug
  | min
  deriving DecidableEq

namespace NumberFeature

variable {nR : ℕ} {C : Set ℕ} {f : NumberFeature}

/-- `AUG` keeps the numbers above the reference number `nR`, and `MIN` the least number of its
input when that is positive. -/
def apply (nR : ℕ) : NumberFeature → Set ℕ → Set ℕ
  | .aug, C => {n ∈ C | nR < n}
  | .min, C => {n ∈ C | 0 < n ∧ ∀ m ∈ C, n ≤ m}

theorem apply_subset : f.apply nR C ⊆ C := by cases f <;> exact Set.sep_subset ..

theorem pos_of_mem_apply {n : ℕ} (h : n ∈ f.apply nR C) : 0 < n := by
  cases f
  exacts [Nat.zero_lt_of_lt h.2, h.2.1]

instance decidableMemApply (nR : ℕ) : (f : NumberFeature) → (C : Set ℕ) →
    [DecidablePred (· ∈ C)] → DecidablePred (· ∈ f.apply nR C)
  | .aug, C, _ => fun n ↦ inferInstanceAs (Decidable (n ∈ C ∧ nR < n))
  | .min, C, _ => fun n ↦ decidable_of_iff (n ∈ C ∧ 0 < n ∧ ∀ m < n, m ∉ C) <|
      and_congr_right fun _ ↦ and_congr_right fun _ ↦
        ⟨fun h m hm ↦ not_lt.1 fun hlt ↦ h m hlt hm, fun h m hlt hm ↦ (h m hm).not_gt hlt⟩

end NumberFeature

section Cardinalities

variable {nR n : ℕ} {ns : List NumberFeature} {N : List (List NumberFeature)}

/-- The cardinalities a number node allows: its features applied in order to the natural
numbers. -/
def cardinalities (nR : ℕ) (ns : List NumberFeature) : Set ℕ :=
  ns.foldl (fun C f ↦ f.apply nR C) .univ

instance decidableMemFoldl (nR : ℕ) : (ns : List NumberFeature) → (C : Set ℕ) →
    [DecidablePred (· ∈ C)] → DecidablePred (· ∈ ns.foldl (fun C f ↦ f.apply nR C) C)
  | [], _, inst => inst
  | f :: ns, C, _ => decidableMemFoldl nR ns (f.apply nR C)

instance (nR : ℕ) (ns : List NumberFeature) : DecidablePred (· ∈ cardinalities nR ns) :=
  @decidableMemFoldl nR ns .univ fun _ ↦ isTrue trivial

theorem foldl_apply_subset (ns : List NumberFeature) (C : Set ℕ) :
    ns.foldl (fun C f ↦ f.apply nR C) C ⊆ C := by
  induction ns generalizing C with
  | nil => exact subset_rfl
  | cons f ns ih => exact (ih _).trans NumberFeature.apply_subset

@[simp] theorem cardinalities_nil : cardinalities nR [] = .univ := rfl

@[simp] theorem cardinalities_aug : cardinalities nR [.aug] = Set.Ioi nR := by
  ext; simp [cardinalities, NumberFeature.apply]

@[simp] theorem cardinalities_aug_min : cardinalities nR [.aug, .min] = {nR + 1} := by
  ext n
  simp only [cardinalities, List.foldl_cons, List.foldl_nil, NumberFeature.apply, Set.mem_univ,
    true_and, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun ⟨h, _, hm⟩ ↦ le_antisymm (hm _ (Nat.lt_succ_self nR)) h,
    by rintro rfl; exact ⟨Nat.lt_succ_self nR, Nat.succ_pos nR, fun _ hm ↦ hm⟩⟩

-- `MIN` applies only after `AUG`: applied first it leaves no cardinality
theorem cardinalities_min_cons (ns : List NumberFeature) : cardinalities nR (.min :: ns) = ∅ :=
  Set.subset_empty_iff.1 <| (foldl_apply_subset ns _).trans fun _ h ↦
    absurd (h.2.2 0 trivial) (Nat.not_le.2 h.2.1)

theorem zero_mem_cardinalities_iff : 0 ∈ cardinalities nR ns ↔ ns = [] := by
  cases ns with
  | nil => simp
  | cons f ns =>
    refine iff_of_false (fun h ↦ ?_) (List.cons_ne_nil _ _)
    exact (NumberFeature.pos_of_mem_apply (foldl_apply_subset ns _ h)).ne' rfl

/-- Maximal Encoding for number: among the number nodes `N` of a language, the node `ns` expresses
the cardinality `n` when it allows `n` and no node with more features does. -/
@[mk_iff]
structure Expresses (N : List (List NumberFeature)) (nR n : ℕ) (ns : List NumberFeature) :
    Prop where
  /-- The node is one of the language's. -/
  mem : ns ∈ N
  /-- The node allows the cardinality. -/
  mem_cardinalities : n ∈ cardinalities nR ns
  /-- No node with more features allows it. -/
  maximal : ∀ ns' ∈ N, ns.length < ns'.length → n ∉ cardinalities nR ns'

instance : Decidable (Expresses N nR n ns) := decidable_of_iff' _ (expresses_iff ..)

/-- The number nodes of a language with `AUG` and no `MIN`. -/
def augNodes : List (List NumberFeature) := [[], [.aug]]

/-- The number nodes of a language with `AUG` and `MIN`. -/
def augMinNodes : List (List NumberFeature) := [[], [.aug], [.aug, .min]]

@[simp] theorem expresses_augNodes_nil : Expresses augNodes nR n [] ↔ n ≤ nR := by
  simp [expresses_iff, augNodes]

@[simp] theorem expresses_augNodes_aug : Expresses augNodes nR n [.aug] ↔ nR < n := by
  simp [expresses_iff, augNodes]

@[simp] theorem expresses_augMinNodes_nil : Expresses augMinNodes nR n [] ↔ n ≤ nR := by
  simp only [expresses_iff, augMinNodes]; simp; omega

@[simp] theorem expresses_augMinNodes_aug : Expresses augMinNodes nR n [.aug] ↔ nR + 1 < n := by
  simp only [expresses_iff, augMinNodes]; simp; omega

@[simp] theorem expresses_augMinNodes_aug_min :
    Expresses augMinNodes nR n [.aug, .min] ↔ n = nR + 1 := by
  simp [expresses_iff, augMinNodes]

end Cardinalities

/-- A number system is relative when number sees the output of person, the two sharing a node,
and absolute when it does not. -/
inductive NumberSystem
  | absolute
  | relative
  deriving DecidableEq

/-- The reference number of `AUG`: the number of the speaker and the addressee in the output of
person where number sees it and it is positive, and otherwise 1. -/
def NumberSystem.referenceNumber : NumberSystem → ℕ → ℕ
  | .absolute, _ => 1
  | .relative, n => if 0 < n then n else 1

/-- A pronoun is a person feature structure under a number node. -/
structure Pronoun where
  /-- The person feature structure. -/
  person : List Feature
  /-- The features of the number node. -/
  number : List NumberFeature
  deriving DecidableEq

section Denotes

variable [DecidableEq α] {σ : NumberSystem} {N : List (List NumberFeature)} {p : Pronoun}
  {S : PersonSpace α} {L : Layered (Finset α)}

/-- A pronoun of a language with the number nodes `N` denotes a set in a person space when its
person features deliver the set, the set is not their input, and its number node expresses the
cardinality of the set. -/
@[mk_iff]
structure Pronoun.Denotes (σ : NumberSystem) (N : List (List NumberFeature)) (p : Pronoun)
    (S : PersonSpace α) (L : Layered (Finset α)) : Prop where
  /-- The person features deliver the set. -/
  eval : S.layered.eval p.person = some L
  /-- Number is not defined on the input of person. -/
  ne_layered : L ≠ S.layered
  /-- The number node expresses the cardinality of the set. -/
  expresses : Expresses N (σ.referenceNumber (S.rolesIn L.set).card) L.set.card p.number

instance : Decidable (p.Denotes σ N S L) := decidable_of_iff' _ (Pronoun.denotes_iff ..)

/-- The pronouns of a language, each person under each of its number nodes. -/
def pronouns (N : List (List NumberFeature)) : List Pronoun :=
  persons.flatMap fun fs ↦ N.map (⟨fs, ·⟩)

/-- The pronouns of a language with a denotation: all but the inclusive without number in an
absolute number system. -/
def inventory (σ : NumberSystem) (N : List (List NumberFeature)) : List Pronoun :=
  (pronouns N).filter fun p ↦ ¬(σ = .absolute ∧ p = ⟨inclusive, []⟩)

/-- A person space with `a` associates of the speaker, `b` of the addressee and `c` others. -/
private def space (a b c : ℕ) : PersonSpace ℕ where
  speaker := 0
  addressee := a + 1
  Si := .range (a + 1)
  Siu := .range (a + b + 2)
  Siuo := .range (a + b + c + 2)
  speaker_mem := Finset.mem_range.2 (Nat.succ_pos a)
  addressee_mem := Finset.mem_range.2 (by omega)
  addressee_notMem := Finset.notMem_range_self
  Si_subset := Finset.range_mono (by omega)
  Siu_subset := Finset.range_mono (by omega)

/-- In a language with `AUG`, with or without `MIN`, the pronouns with a denotation in some
person space are every person under every number node, except that an absolute number system
has no inclusive without number: its set has two obligatory members, more than the reference
number, which `AUG` encodes. -/
theorem mem_inventory_iff (hN : N = augNodes ∨ N = augMinNodes) :
    p ∈ inventory σ N ↔ ∃ (S : PersonSpace ℕ) (L : Layered (Finset ℕ)), p.Denotes σ N S L := by
  refine ⟨fun h ↦ ?_, fun ⟨S, L, h⟩ ↦ ?_⟩
  · rcases hN with rfl | rfl <;> cases σ <;> fin_cases h
    all_goals first
      | exact ⟨space 0 0 0, _, rfl, by decide, by decide⟩
      | exact ⟨space 2 2 3, _, rfl, by decide, by decide⟩
      | exact ⟨space 1 1 2, _, rfl, by decide, by decide⟩
      | exact ⟨space 1 0 0, _, rfl, by decide, by decide⟩
  · obtain ⟨fs, ns⟩ := p
    have hfs : fs ∈ persons := by
      have := eq_nil_or_of_eval h.eval
      simpa [persons, (ne_layered_iff h.eval).1 h.ne_layered] using this
    refine List.mem_filter.2 ⟨List.mem_flatMap.2 ⟨fs, hfs, List.mem_map.2 ⟨ns, h.expresses.mem,
      rfl⟩⟩, decide_eq_true ?_⟩
    rintro ⟨rfl, hp⟩
    obtain ⟨rfl, rfl⟩ := Pronoun.mk.inj hp
    obtain rfl := Option.some.inj h.eval
    exact h.expresses.maximal [.aug] (by rcases hN with rfl | rfl <;> decide) Nat.zero_lt_one
      (cardinalities_aug ▸ S.one_lt_card_Siu)

/-- A pronoun covers a configuration when its person features deliver the configuration's
participants and its number node expresses the configuration's number of members. -/
def Pronoun.Covers (σ : NumberSystem) (N : List (List NumberFeature)) (p : Pronoun)
    (x : Person.Configuration) : Prop :=
  participants p.person = some x.participants ∧
    Expresses N (σ.referenceNumber x.participants.card) x.card p.number

instance : DecidablePred (p.Covers σ N) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem Pronoun.Denotes.covers (h : p.Denotes σ N S L) : p.Covers σ N (S.config L.set) :=
  ⟨participants_eq_of_eval h.eval, (S.card_config L.set).symm ▸ h.expresses⟩

private theorem exists_config_eq {fs : List Feature} {x : Person.Configuration} (hfs : fs ≠ [])
    (h : participants fs = some x.participants) :
    ∃ (S : PersonSpace ℕ) (L : Layered (Finset ℕ)),
      S.layered.eval fs = some L ∧ S.config L.set = x := by
  obtain ⟨P, k⟩ := x
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.1 h
  have h2 : (Finset.univ : Finset Role).card = 2 := rfl
  rcases eq_nil_or_of_eval hL with rfl | rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj hL
  · exact absurd rfl hfs
  · refine ⟨space k 0 0, _, eval_inclusive _,
      Person.Configuration.ext (PersonSpace.rolesIn_Siu _) ?_⟩
    simp only [PersonSpace.config, PersonSpace.rolesIn_Siu]
    simp [space, h2]
  · refine ⟨space k 0 0, _, eval_first _, Person.Configuration.ext (PersonSpace.rolesIn_Si _) ?_⟩
    simp only [PersonSpace.config, PersonSpace.rolesIn_Si]
    simp [space]
  · refine ⟨space 0 k 0, _, eval_second _, Person.Configuration.ext ?_ ?_⟩ <;>
      simp only [PersonSpace.config, PersonSpace.rolesIn_sdiff, PersonSpace.rolesIn_Siu,
        PersonSpace.rolesIn_Si, Finset.card_sdiff_of_subset (PersonSpace.Si_subset _)]
    · decide
    · simp [space, show (Finset.univ \ {Role.speaker} : Finset Role).card = 1 from rfl]
  · refine ⟨space 0 0 k, _, eval_third _, Person.Configuration.ext ?_ ?_⟩ <;>
      simp only [PersonSpace.config, PersonSpace.rolesIn_sdiff, PersonSpace.rolesIn_Siu,
        PersonSpace.rolesIn_Siuo, Finset.card_sdiff_of_subset (PersonSpace.Siu_subset _)]
    · decide
    · simp [space]

-- the configurations a pronoun covers are those of the sets it denotes
theorem covers_iff {x : Person.Configuration} (hp : p.person ≠ []) :
    p.Covers σ N x ↔
      ∃ (S : PersonSpace ℕ) (L : Layered (Finset ℕ)), p.Denotes σ N S L ∧ S.config L.set = x := by
  refine ⟨fun h ↦ ?_, fun ⟨S, L, h, hx⟩ ↦ hx ▸ h.covers⟩
  obtain ⟨S, L, hL, rfl⟩ := exists_config_eq hp h.1
  exact ⟨S, L, ⟨hL, (ne_layered_iff hL).2 hp, S.card_config L.set ▸ h.2⟩, rfl⟩

/-- The referential categories of the configurations a pronoun covers. -/
def Pronoun.categories (σ : NumberSystem) (N : List (List NumberFeature)) (p : Pronoun) :
    Finset Person.Category :=
  ((Person.Configuration.bounded .univ).filter (p.Covers σ N)).biUnion (·.category.toFinset)

end Denotes

/-! ### Number values and paradigm types

The configurations a number node is used for are those of a number value: of the singular, the
plural and the dual in an absolute system and of the minimal, the augmented and the unit augmented
in a relative one. -/

section Values

open Person.Configuration

theorem covers_absolute : ∀ fs ∈ persons, ∀ P ∈ participants fs,
    (bounded {P}).filter (Pronoun.Covers .absolute augMinNodes ⟨fs, []⟩) = covered {P} .singular ∧
      (bounded {P}).filter (Pronoun.Covers .absolute augMinNodes ⟨fs, [.aug, .min]⟩) =
        covered {P} .dual ∧
      (bounded {P}).filter (Pronoun.Covers .absolute augNodes ⟨fs, [.aug]⟩) =
        covered {P} .plural := by
  decide

theorem covers_relative : ∀ fs ∈ persons, ∀ P ∈ participants fs,
    (bounded {P}).filter (Pronoun.Covers .relative augMinNodes ⟨fs, []⟩) = covered {P} .minimal ∧
      (bounded {P}).filter (Pronoun.Covers .relative augMinNodes ⟨fs, [.aug, .min]⟩) =
        covered {P} .unitAugmented ∧
      (bounded {P}).filter (Pronoun.Covers .relative augNodes ⟨fs, [.aug]⟩) =
        covered {P} .augmented := by
  decide

end Values

theorem map_categories_inventory :
    (inventory .absolute augNodes).map (·.categories .absolute augNodes) =
        [{.speakerAddressee, .speakerAddresseeOthers}, {.speaker}, {.speakerOthers}, {.addressee},
          {.addresseeOthers}, {.other}, {.others}] ∧
      (inventory .relative augNodes).map (·.categories .relative augNodes) =
        [{.speakerAddressee}, {.speakerAddresseeOthers}, {.speaker}, {.speakerOthers},
          {.addressee}, {.addresseeOthers}, {.other}, {.others}] := by
  decide

/-- Two referential categories fall under one pronoun of an absolute number system with `AUG`
exactly when Cysouw's Mandara type gives them one form, and under one pronoun of a relative
system exactly when his Maranao type does. -/
theorem pattern_iff (c d : Person.Category) :
    (Cysouw2003.Kind.mandara.pattern c d ↔ ∃ p ∈ inventory .absolute augNodes,
        c ∈ p.categories .absolute augNodes ∧ d ∈ p.categories .absolute augNodes) ∧
      (Cysouw2003.Kind.maranao.pattern c d ↔ ∃ p ∈ inventory .relative augNodes,
        c ∈ p.categories .relative augNodes ∧ d ∈ p.categories .relative augNodes) := by
  revert c d; decide

/-! ### Expletives -/

section Expletives

variable {σ : NumberSystem} {N : List (List NumberFeature)} {p : Pronoun} {fs : List Feature}

/-- A person feature structure can be empty when it delivers the empty set in some person
space. -/
def CanBeEmpty (fs : List Feature) : Prop :=
  ∃ (S : PersonSpace ℕ) (L : Layered (Finset ℕ)), S.layered.eval fs = some L ∧ L.set = ∅

theorem canBeEmpty_iff : CanBeEmpty fs ↔ fs = third :=
  ⟨fun ⟨_, _, h, he⟩ ↦ by_contra fun hfs ↦ (nonempty_of_eval h hfs).ne_empty he,
    fun h ↦ h ▸ ⟨space 0 0 0, _, rfl, by decide⟩⟩

instance : DecidablePred CanBeEmpty := fun _ ↦ decidable_of_iff _ canBeEmpty_iff.symm

/-- A pronoun can be an expletive when it denotes the empty set in some person space. -/
def Pronoun.CanBeExpletive (σ : NumberSystem) (N : List (List NumberFeature)) (p : Pronoun) :
    Prop :=
  ∃ (S : PersonSpace ℕ) (L : Layered (Finset ℕ)), p.Denotes σ N S L ∧ L.set = ∅

/-- In either number system, only the third person without number can be an expletive: `DIST`
alone can deliver the empty set, and every number feature requires a positive cardinality. -/
theorem canBeExpletive_iff : p.CanBeExpletive σ N ↔ p = ⟨third, []⟩ ∧ [] ∈ N := by
  refine ⟨fun ⟨S, L, h, he⟩ ↦ ?_, ?_⟩
  · obtain ⟨fs, ns⟩ := p
    obtain rfl : fs = third := canBeEmpty_iff.1 ⟨S, L, h.eval, he⟩
    have h0 := h.expresses.mem_cardinalities
    rw [he, Finset.card_empty, zero_mem_cardinalities_iff] at h0
    exact ⟨by rw [show ns = [] from h0], h0 ▸ h.expresses.mem⟩
  · rintro ⟨rfl, hN⟩
    refine ⟨space 0 0 0, _, ⟨rfl, by decide, hN, trivial, fun ns _ hlt h0 ↦ ?_⟩, by decide⟩
    rw [show (_ : Finset ℕ).card = 0 by decide, zero_mem_cardinalities_iff] at h0
    simp [h0] at hlt

instance : Decidable (p.CanBeExpletive σ N) := decidable_of_iff _ canBeExpletive_iff.symm

end Expletives

/-! ### The examples

A subject pronoun is read from its entry in the language file, whose agreement person and number
select the feature structures it can realize, and the agreement of a finite verb from its
gloss. -/

open Examples (Example Lexeme)

/-- The entry of a subject pronoun. -/
def Examples.Lexeme.entry : Lexeme → _root_.Pronoun
  | .it => English.Pronouns.it.toPronoun
  | .i => English.Pronouns.i.toPronoun
  | .you => English.Pronouns.you.toPronoun
  | .men => Dutch.Pronouns.men

/-- The language of a subject pronoun. -/
def Examples.Lexeme.language : Lexeme → Glottocode
  | .men => .dutch
  | _ => .english

/-- The pronouns of an absolute system with `AUG` that an agreement person and number are
compatible with: those whose participants the person covers, every participant set where no
person is given, and whose number node covers the configurations of the number. -/
def structures (person : Option Person) (number : Option Number) : List Pronoun :=
  (inventory .absolute augNodes).filter fun p ↦ ∃ P ∈ participants p.person,
    P ∈ (Person.Specification.ofPersonClusivity person none).sets ∧ ∀ n ∈ number,
      (Person.Configuration.bounded {P}).filter (p.Covers .absolute augNodes) =
        Person.Configuration.covered {P} n

/-- The pronouns analysed as bare `N_Π`, with no person feature and no number node. -/
def featureless : List Lexeme := [.men]

/-- A subject pronoun can be an expletive when a structure it realizes can be one, and a
featureless pronoun when the structure with no feature can be empty. -/
def Examples.Lexeme.CanBeExpletive (l : Lexeme) : Prop :=
  if l ∈ featureless then CanBeEmpty []
  else ∃ p ∈ structures l.entry.person l.entry.number, p.CanBeExpletive .absolute augNodes

instance : DecidablePred Lexeme.CanBeExpletive := fun l ↦ by
  unfold Lexeme.CanBeExpletive; infer_instance

-- an expletive subject is acceptable iff its pronoun can be an expletive, and default agreement
-- iff a pronoun with its person and number can be
theorem acceptable_iff_canBeExpletive :
    (∀ x : Example, x.phenomenon = some .expletive → x.lexemes .subject ≠ [] ∧
      ∀ l ∈ x.lexemes .subject, (x.datum.judgment = .acceptable ↔ l.CanBeExpletive)) ∧
    ∀ x : Example, x.phenomenon = some .defaultAgreement →
      ∃ s ∈ x.datum.spans, Examples.label? s = some .agreement ∧ ∃ w ∈ (s.words x.datum).head?,
        (x.datum.judgment = .acceptable ↔ ∃ p ∈ structures (w.features .person)
          (w.features .number), p.CanBeExpletive .absolute augNodes) := by
  decide +kernel

theorem lexeme_language :
    ∀ x : Example, ∀ l ∈ x.lexemes .subject, x.datum.language = l.language := by
  decide +kernel

-- each subject span is printed as its entry is written, up to capitals
theorem subject_forms :
    ∀ x : Example, ∀ s ∈ x.datum.spans, ∀ l ∈ Examples.lexeme? s,
      ∃ w ∈ (s.words x.datum).head?,
        w.word.map Char.toLower = l.entry.form.toList.map Char.toLower := by
  decide +kernel

/-! ### Spell-out and Maximal Encoding -/

/-- What a spell-out rule reads of a pronoun: its person features and its number features, each
counted with multiplicity. -/
def Pronoun.bundle (p : Pronoun) : Multiset Feature × Multiset NumberFeature :=
  (p.person, p.number)

section NaturalClasses

variable {r : SubsetRule (Multiset Feature × Multiset NumberFeature) E}
  {ns : List NumberFeature}

theorem shared_features :
    (first : Multiset Feature) ∩ second = {.prox} ∧ (second : Multiset Feature) ∩ third = {.dist} ∧
      (first : Multiset Feature) ∩ third = 0 := by
  decide

theorem applies_second_of_first_of_third (h₁ : Applies r (⟨first, ns⟩ : Pronoun).bundle)
    (h₃ : Applies r (⟨third, ns⟩ : Pronoun).bundle) : Applies r (⟨second, ns⟩ : Pronoun).bundle :=
  SubsetRule.applies_of_inf_le h₁ h₃
    ⟨(by decide : (first : Multiset Feature) ⊓ third ≤ second), inf_le_left⟩

theorem applies_first_of_inclusive_of_second (h₁ : Applies r (⟨inclusive, ns⟩ : Pronoun).bundle)
    (h₂ : Applies r (⟨second, ns⟩ : Pronoun).bundle) : Applies r (⟨first, ns⟩ : Pronoun).bundle :=
  SubsetRule.applies_of_inf_le h₁ h₂
    ⟨(by decide : (inclusive : Multiset Feature) ⊓ second ≤ first), inf_le_left⟩

-- a rule that mentions no number feature cannot tell the exclusive from the first singular
theorem applies_exclusive_iff_first (m : Multiset Feature) (e : E) :
    Applies (⟨(m, 0), e⟩ : SubsetRule (Multiset Feature × Multiset NumberFeature) E)
        (⟨first, [.aug]⟩ : Pronoun).bundle ↔
      Applies (⟨(m, 0), e⟩ : SubsetRule (Multiset Feature × Multiset NumberFeature) E)
        (⟨first, []⟩ : Pronoun).bundle := by
  simp [Pronoun.bundle]

end NaturalClasses

open Dutch.Pronouns in
/-- (33): the spell-out rules of the Dutch strong subject pronouns, none of which mentions two
`PROX`. -/
def dutch : RuleSet (SubsetRule (Multiset Feature × Multiset NumberFeature) PersonalPronoun) :=
  [⟨({.prox}, 0), ik⟩, ⟨({.prox, .dist}, 0), jij⟩, ⟨({.dist}, 0), hij⟩,
    ⟨({.prox}, {.aug}), wij⟩, ⟨({.prox, .dist}, {.aug}), jullie⟩, ⟨({.dist}, {.aug}), zij_pl⟩]

open Dutch.Pronouns in
-- under Maximal Encoding the Dutch rules give the inclusive and the exclusive one form
theorem dutch_paradigm :
    (inventory .absolute augNodes).map (dutch.realize SubsetRule.card ∘ Pronoun.bundle) =
      [some wij, some ik, some wij, some jij, some jullie, some hij, some zij_pl] := by
  decide

-- each Dutch pronoun denotes the referential categories that the pronouns it realizes cover
theorem dutch_referential : ∀ r ∈ dutch, ∀ c,
    c ∈ r.exponent.referential ↔
      ∃ p ∈ inventory .absolute augNodes, dutch.realize SubsetRule.card p.bundle = some r.exponent ∧
        c ∈ p.categories .absolute augNodes := by
  decide

/-- (34): a rule set with a rule mentioning two `PROX` and a rule mentioning one, both with
`AUG`. -/
def clusive (a b : E) : RuleSet (SubsetRule (Multiset Feature × Multiset NumberFeature) E) :=
  [⟨({.prox, .prox}, {.aug}), a⟩, ⟨({.prox}, {.aug}), b⟩]

theorem clusive_split (a b : E) :
    (clusive a b).realize SubsetRule.card (⟨first, [.aug]⟩ : Pronoun).bundle = some a ∧
      (clusive a b).realize SubsetRule.card (⟨inclusive, [.aug]⟩ : Pronoun).bundle = some b :=
  ⟨rfl, rfl⟩

/-! ### Zwicky's generalization

No natural class holds the inclusive and the second person without the exclusive, so no rule
marks them alike to the exclusion of the exclusive. Impoverishment can still bring them
together: deleting `DIST` under `PROX` in the plural gives the second person plural the
inclusive's structure. In a language that spells out one and two `PROX` apart, the exclusive is
then marked apart from the inclusive and the second person. -/

/-- Impoverishment of `DIST` under `PROX` in the plural: the second person plural loses its
`DIST`. -/
def impoverishDist : Pronoun → Pronoun
  | ⟨[.prox, .dist], [.aug]⟩ => ⟨[.prox], [.aug]⟩
  | p => p

/-- The system a realization of the plural pronouns induces on participant sets: two are related
when pronouns with those participants are realized alike. -/
def pluralGraph [DecidableEq E] (f : Pronoun → Option E) : Finset (Finset Role × Finset Role) :=
  Finset.univ.filter fun P ↦ ∃ p ∈ inventory .absolute augNodes,
    ∃ q ∈ inventory .absolute augNodes, p.number = [.aug] ∧ q.number = [.aug] ∧
      participants p.person = some P.1 ∧ participants q.person = some P.2 ∧ f p = f q

/-- Plural rules for two `PROX`, one `PROX`, `PROX` with `DIST`, and `DIST`. -/
def pluralRules : RuleSet (SubsetRule (Multiset Feature × Multiset NumberFeature) (Fin 4)) :=
  [⟨({.prox, .prox}, {.aug}), 0⟩, ⟨({.prox}, {.aug}), 1⟩, ⟨({.prox, .dist}, {.aug}), 2⟩,
    ⟨({.dist}, {.aug}), 3⟩]

-- without impoverishment the plural paradigm is the quadripartition
theorem pluralGraph_pluralRules :
    pluralGraph (pluralRules.realize SubsetRule.card ∘ Pronoun.bundle) =
      Harbour2016.graph {.speaker, .addressee} := by
  decide

-- with it, the inclusive goes with the second person and the exclusive stands apart
theorem pluralGraph_pluralRules_impoverishDist :
    pluralGraph (pluralRules.realize SubsetRule.card ∘ Pronoun.bundle ∘ impoverishDist) =
      Harbour2016.graph {.addressee, .participant} := by
  decide

/-- Impoverishing `DIST` under `PROX` in the plural turns a plural paradigm that Harbour's
parameters generate into one they never generate, the tripartition of Zwicky's
generalization. -/
theorem impoverishDist_not_mem_image_graph :
    pluralGraph (pluralRules.realize SubsetRule.card ∘ Pronoun.bundle) ∈
        Finset.univ.image Harbour2016.Setting.graph ∧
      pluralGraph (pluralRules.realize SubsetRule.card ∘ Pronoun.bundle ∘ impoverishDist) ∉
        Finset.univ.image Harbour2016.Setting.graph := by
  rw [pluralGraph_pluralRules, pluralGraph_pluralRules_impoverishDist,
    Harbour2016.graph_mem_image_iff, Harbour2016.graph_mem_image_iff]
  decide

end AckemaNeeleman2018
