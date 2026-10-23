module

public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Logic.Equiv.Defs
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Quantification.NumberTree
public import Linglib.Semantics.Quantification.Witness
public import Linglib.Data.Examples.Cooper2023

/-!
# Cooper (2023): From Perception to Communication: A Theory of Types for Action and Meaning

Cooper's theory of types with records reads a type as true when something witnesses it. A
modal type system assigns objects to types in each of a family of possibilities, and subtyping is
inclusion of witnesses in every possibility, so an attitude, which matches its complement against
a type of the agent's information state, depends on which postulates restrict the possibilities.
A witness for a quantified sentence is a witness set with a function into or out of it, following
Barwise and Cooper's two procedures for monotone quantifiers, and the sets a witness carries are
the anaphora sets the noun phrase makes available. Scope ambiguity comes from storing a
quantifier in the context and retrieving it over the sentence, and binding from marking pronouns
as local or reflexive.

## Main statements

* `Venus.not_believe_oneStar`, `Venus.believe_oneStar_reporter`: the ancients do not believe
  that Hesperus is Phosphorus under their own postulates, and do under the reporter's.
* `nonempty_generalWCIncr_iff_toGQ`, `nonempty_generalWCDecr_iff_toGQ`: the general witness
  conditions are Barwise and Cooper's two procedures for the tree quantifier of their relation.
* `witnessType_propAtLeast_iff`: a probabilistic witness condition of §7.3 is its cardinal one.
* `WitnessCondition.exists_set_subset`: each witness condition can be met by a witness whose
  set lies in the anaphora set it makes available, which `anaphora_rows` checks against the
  book's judgements.

## Implementation notes

* Within one possibility, types are Lean's own, and a property is `E → Type`. A modal type
  system assigns shared objects to types, so subtyping, and every attitude built on it,
  compares witnesses across possibilities. The postulates for transitive verbs are hypotheses
  on Lean types.
* A negated type `¬T` (Ch. 7, (69)) is the function type `T → Empty`.
* Proportional thresholds are cross-multiplied `n / d` over a nonempty extension, and the
  thresholds `θ_q(P)` are parameters, shared by *few* and *a few* only where stated.
* Context labels are chosen distinct by hand rather than incremented at combination, and a
  stored quantifier keeps its foreground, its background merged at storage. Localisation folds
  the whole assignment into a property's domain, and alignment supplies the constant assignment
  at the antecedent's witness.

## TODO

* The closure of a content type under the operations (Ch. 8, (21), (89)) and the combination
  of content types (23)–(24) are not modelled: each reading is derived by composing the
  operations by hand.
* The asymmetric merge `∧̣` of a type with a point of view (Ch. 6, (55)–(58)) is not defined:
  an information state lists which types are such merges.
* The number of a pronoun is not modelled, so the contrast between *it* and *they* with a
  universal antecedent, (46b)–(46e), is recorded in the rows but not derived.
* A reflexive inside a verb phrase (*The guru revealed Kim to himself*) and picture noun
  phrases are outside the treatment, as in the book.
* Purification is determiner-independent, so both donkey readings are predicted for every
  determiner; the experimental record of [denic-sudo-2022] on non-monotonic determiners and
  the question-based selection of [champollion-bumford-henderson-2019] are the tests to
  state.

## References

* [R. Cooper, *From Perception to Communication* (2023)][cooper-2023]
* [J. Barwise, R. Cooper, *Generalized Quantifiers and Natural Language*
  (1981)][barwise-cooper-1981]
* [J. van Benthem, *Questions about Quantifiers* (1984)][van-benthem-1984]
* [L. M. Moxey, A. J. Sanford, *Quantifiers and Focus* (1987)][moxey-sanford-1987]
* [A. Kratzer, *What 'must' and 'can' must and can mean* (1977)][kratzer-1977]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [E. Breitholtz, *Enthymemes and Topoi in Dialogue* (2020)][breitholtz-2020]
* [G. Chierchia, *Dynamics of Meaning* (1995)][chierchia-1995b]
* [M. Kanazawa, *Weak vs. Strong Readings of Donkey Sentences* (1994)][kanazawa-1994]
* [A. Ranta, *Type-Theoretical Grammar* (1994)][ranta-1994]
* [R. Montague, *The Proper Treatment of Quantification in Ordinary English* (1973)][montague-1973]
* [M. Denić, Y. Sudo, *Donkey Anaphora in Non-Monotonic Environments* (2022)][denic-sudo-2022]
* [L. Champollion, D. Bumford, R. Henderson, *Donkeys under Discussion*
  (2019)][champollion-bumford-henderson-2019]
-/

@[expose] public section

namespace Cooper2023

open Quantifier Quantifier.GQ Quantifier.NP

variable {E : Type}

/-! ## Properties, quantifiers and their contents (Chs. 3, 4) -/

/-- A property (30) gives each individual its type of situations. -/
abbrev Ppty (E : Type) := E → Type

/-- A quantifier maps properties to types, as Montague's ⟨⟨e,t⟩,t⟩ does. -/
abbrev Quant (E : Type) := Ppty E → Type

/-- A property is witnessed at an individual of its property extension `[↓P]`. -/
abbrev Ppty.Witnessed (P : Ppty E) (a : E) : Prop := Nonempty (P a)

/-- `SemPropName(a)` (33) applies a property to the individual `a`. -/
def SemPropName (a : E) : Quant E := fun P ↦ P a

/-- The particular witness condition for `exist(P, Q)` (Ch. 7, (63)) provides an individual with the
first property and the second. Its `x`-field is what singular anaphora picks up in *A dog is
barking. It is right outside my window* (Ch. 7, (64)). -/
structure ParticularWCExist (P Q : Ppty E) where
  x : E
  pWit : P x
  qWit : Q x

/-- The particular witness condition for `no(P, Q)` (Ch. 7, (70)) shows that every witness of the
first property precludes the second, by a function into the negated type (69). -/
structure ParticularWCNo (P Q : Ppty E) where
  f : (a : E) → P a → Q a → Empty

/-- `exist(P, Q)` is witnessed iff the property extensions of `P` and `Q` overlap, (55). -/
theorem nonempty_particularWCExist_iff {P Q : Ppty E} :
    Nonempty (ParticularWCExist P Q) ↔ ∃ a, Nonempty (P a) ∧ Nonempty (Q a) :=
  ⟨fun ⟨w⟩ ↦ ⟨w.x, ⟨w.pWit⟩, ⟨w.qWit⟩⟩, fun ⟨a, ⟨p⟩, ⟨q⟩⟩ ↦ ⟨⟨a, p, q⟩⟩⟩

theorem some_of_particularWCExist {P Q : Ppty E} (w : ParticularWCExist P Q) :
    GQ.some P.Witnessed Q.Witnessed :=
  ⟨w.x, ⟨w.pWit⟩, ⟨w.qWit⟩⟩

theorem no_of_particularWCNo {P Q : Ppty E} (w : ParticularWCNo P Q) :
    no P.Witnessed Q.Witnessed :=
  fun a ⟨p⟩ ⟨q⟩ ↦ (w.f a p q).elim

/-- `SemIndefArt` (37) sends a restrictor property to the existential quantifier over it, whose
witness under the particular condition of Ch. 7 (63) is an individual with the restrictor and the
scope. -/
def SemIndefArt (restr : Ppty E) : Quant E := ParticularWCExist restr

/-- `SemBe` (78), Montague's copula, is the property of being the quantifier's witness. -/
def SemBe (Q : Quant E) : Ppty E := fun x ↦ Q fun y ↦ PLift (x = y)

/-- The universal quantifier is a function from the restrictor's witnesses to the scope's, the
function witness of §7.2.4 after [ranta-1994], which, as Cooper notes at (27), yields no witness set
for plural anaphora; the set-based condition (72) is `GeneralWCIncr` with `CardRel.every`. -/
def SemUniversal (restr scope : Ppty E) : Type := (x : E) → restr x → scope x

/-- `no(P, Q)` under its particular witness condition (Ch. 7, (70)) holds when every witness of the
restrictor precludes the scope. -/
def SemNo (restr scope : Ppty E) : Type := ParticularWCNo restr scope

/-- *a is a P*, the copula over the indefinite article, is witnessed iff `P(a)` is (92), so the
compositional content and the construction-based content of (86)–(87) are distinct but equivalent
types. -/
theorem nonempty_semBe_semIndefArt_iff (P : Ppty E) (a : E) :
    Nonempty (SemBe (SemIndefArt P) a) ↔ Nonempty (P a) :=
  ⟨fun ⟨⟨_, h, ⟨rfl⟩⟩⟩ ↦ ⟨h⟩, fun ⟨h⟩ ↦ ⟨⟨a, h, ⟨rfl⟩⟩⟩⟩

/-- *a P is a*, with the quantifiers in the other order, is witnessed iff `P(a)` is as well (94c);
only the construction expresses `P(a)` itself, and (89) *A conductor is Dudamel* is odd. -/
theorem nonempty_semIndefArt_semBe_semPropName_iff (P : Ppty E) (a : E) :
    Nonempty (SemIndefArt P (SemBe (SemPropName a))) ↔ Nonempty (P a) :=
  ⟨fun ⟨⟨_, h, ⟨rfl⟩⟩⟩ ↦ ⟨h⟩, fun ⟨h⟩ ↦ ⟨⟨a, h, ⟨rfl⟩⟩⟩⟩

/-- A quantifier is monotone increasing when a witness for a property gives one for any larger
property. -/
def Quant.IsMonIncr (Q : Quant E) : Prop :=
  ∀ P P' : Ppty E, (∀ x, P x → P' x) → Nonempty (Q P) → Nonempty (Q P')

theorem isMonIncr_semIndefArt (restr : Ppty E) : Quant.IsMonIncr (SemIndefArt restr) :=
  fun _ _ h ⟨w⟩ ↦ ⟨⟨w.x, w.pWit, h _ w.qWit⟩⟩

/-- A parametric content (§4.3, (14)) pairs a background type, the context it requires, with a
foreground function from contexts of that type to contents. -/
structure Parametric (C : Type*) where
  bg : Type
  fg : bg → C

/-! #### *Dudamel is a conductor* (82c) -/

namespace Dudamel

inductive Ind | dudamel | beethoven deriving DecidableEq, Repr
inductive Conductor : Ind → Type | mk : Conductor .dudamel

/-- *is a conductor* (81c) is the copula over the indefinite article. -/
def IsAConductor : Ppty Ind := SemBe (SemIndefArt Conductor)
def dudamelIsAConductor : SemPropName .dudamel IsAConductor := ⟨.dudamel, .mk, ⟨rfl⟩⟩

theorem beethovenIsAConductor_isEmpty : IsEmpty (SemPropName .beethoven IsAConductor) :=
  ⟨fun | ⟨.dudamel, _, ⟨h⟩⟩ => nomatch h | ⟨.beethoven, h, _⟩ => nomatch h⟩

end Dudamel

/-! ## Modality and intensionality without possible worlds (Ch. 6)

A modal type system is a family of possibilities over shared types, and modality and the
attitudes compare witnesses across its possibilities. -/

/-! ### Modal type systems (§6.3) -/

/-- A possibility says which types occur in it and which objects witness them. Only a type of the
possibility has witnesses in it. -/
structure Possibility (Ty Obj : Type) where
  occurs : Ty → Prop
  witnesses : Ty → Obj → Prop
  occurs_of_witnesses ⦃T : Ty⦄ ⦃a : Obj⦄ : witnesses T a → occurs T

/-- A modal system of types (§1.4.3.5, (54)) is a family of possibilities over shared types. -/
abbrev ModalSystem (M Ty Obj : Type) := M → Possibility Ty Obj

namespace ModalSystem

variable {M M' Ty Obj : Type} (ms : ModalSystem M Ty Obj) (T₁ T₂ T : Ty)

/-- The extension of `T` (1a) gives its witnesses in each possibility. -/
def extension (T : Ty) (p : M) : Set Obj := {a | (ms p).witnesses T a}

/-- `T` occurs in the type system of the possibility `p`. -/
def Occurs (p : M) (T : Ty) : Prop := (ms p).occurs T

/-- `T₁` is a restrictive subtype of `T₂` (1b) when its extension is included in that of `T₂` in
every possibility. -/
def SubtypeR : Prop := ms.extension T₁ ≤ ms.extension T₂

/-- `T₁` and `T₂` are restrictively equivalent (1a) when they have the same extension in every
possibility. -/
def EquivR : Prop := ms.extension T₁ = ms.extension T₂

/-- `T` is restrictively necessary (1c) when it is witnessed in every possibility. -/
def NecR : Prop := ∀ p, (ms.extension T p).Nonempty

/-- `T` is restrictively possible (1d) when it is witnessed in some possibility. -/
def PossR : Prop := ∃ p, (ms.extension T p).Nonempty

/-- `T₁` is an inclusive subtype of `T₂` (2b; Ch. 1, (55)) when its extension is included in that of
`T₂` wherever both types occur. -/
def SubtypeI : Prop :=
  ∀ p, ms.Occurs p T₁ → ms.Occurs p T₂ → ms.extension T₁ p ⊆ ms.extension T₂ p

/-- `T₁` and `T₂` are inclusively equivalent (2a) when they have the same extension wherever both
occur. -/
def EquivI : Prop :=
  ∀ p, ms.Occurs p T₁ → ms.Occurs p T₂ → ms.extension T₁ p = ms.extension T₂ p

/-- `T` is inclusively necessary, by the rule (4c), when it occurs in some possibility and is
witnessed wherever it occurs. -/
def NecI : Prop := (∃ p, ms.Occurs p T) ∧ ∀ p, ms.Occurs p T → (ms.extension T p).Nonempty

/-- `T` is inclusively possible, by the rule (4d), when it is witnessed in a possibility in which it
occurs. The definition (2d) prints the conjunction as an implication. -/
def PossI : Prop := ∃ p, ms.Occurs p T ∧ (ms.extension T p).Nonempty

variable {ms T₁ T₂ T}

/-- Restrictive equivalence is subtyping both ways (3b). -/
theorem equivR_iff : ms.EquivR T₁ T₂ ↔ ms.SubtypeR T₁ T₂ ∧ ms.SubtypeR T₂ T₁ :=
  le_antisymm_iff

/-- Inclusive equivalence is subtyping both ways (4b). -/
theorem equivI_iff : ms.EquivI T₁ T₂ ↔ ms.SubtypeI T₁ T₂ ∧ ms.SubtypeI T₂ T₁ := by
  grind [EquivI, SubtypeI, Set.Subset.antisymm_iff]

theorem SubtypeR.trans {T₃ : Ty} (h : ms.SubtypeR T₁ T₂) (h' : ms.SubtypeR T₂ T₃) :
    ms.SubtypeR T₁ T₃ :=
  le_trans h h'

theorem SubtypeR.subtypeI (h : ms.SubtypeR T₁ T₂) : ms.SubtypeI T₁ T₂ := fun p _ _ ↦ h p

theorem EquivR.equivI (h : ms.EquivR T₁ T₂) : ms.EquivI T₁ T₂ := fun p _ _ ↦ congrFun h p

theorem NecR.necI [Nonempty M] (h : ms.NecR T) : ms.NecI T :=
  have ⟨p⟩ := ‹Nonempty M›
  ⟨⟨p, (ms p).occurs_of_witnesses (h p).some_mem⟩, fun p _ ↦ h p⟩

theorem PossR.possI (h : ms.PossR T) : ms.PossI T := by
  grind [PossR, PossI, Occurs, extension, Possibility.occurs_of_witnesses, Set.Nonempty]

/-- Subtyping in a modal system holds in any restriction of it, and restricting attention to some of
the possibilities is what a postulate does (p. 261). -/
theorem SubtypeI.comp (h : ms.SubtypeI T₁ T₂) (ι : M' → M) :
    ModalSystem.SubtypeI (ms ∘ ι) T₁ T₂ :=
  fun p ↦ h (ι p)

end ModalSystem

/-! #### Restrictive against inclusive necessity

Snow is possible but not necessary, and once it does not occur in the second possibility it is
inclusively but not restrictively necessary. -/

namespace Weather

inductive Ty | rain | snow deriving DecidableEq
inductive Obj | a | b deriving DecidableEq

/-- Both types occur in both possibilities; rain is witnessed in both, snow in the first. -/
def system : ModalSystem (Fin 2) Ty Obj
  | 0 => ⟨fun _ ↦ True, fun | .rain, .a => True | .snow, .b => True | _, _ => False,
      fun _ _ _ ↦ trivial⟩
  | 1 => ⟨fun _ ↦ True, fun | .rain, .a => True | _, _ => False, fun _ _ _ ↦ trivial⟩

/-- As `system`, but snow does not occur in the second possibility. -/
def restricted : ModalSystem (Fin 2) Ty Obj
  | 0 => ⟨fun _ ↦ True, fun | .rain, .a => True | .snow, .b => True | _, _ => False,
      fun _ _ _ ↦ trivial⟩
  | 1 => ⟨(· = .rain), fun | .rain, .a => True | _, _ => False,
      fun | .rain, _, _ => rfl | .snow, .a, h => h.elim | .snow, .b, h => h.elim⟩

theorem necR_rain : system.NecR .rain := fun | 0 => ⟨.a, trivial⟩ | 1 => ⟨.a, trivial⟩

theorem possR_snow : system.PossR .snow := ⟨0, .b, trivial⟩

theorem not_necR_snow : ¬ system.NecR .snow := fun h ↦ nomatch h 1

theorem restricted_necI_snow : restricted.NecI .snow :=
  ⟨⟨0, trivial⟩, fun | 0, _ => ⟨.b, trivial⟩ | 1, h => nomatch h⟩

theorem restricted_not_necR_snow : ¬ restricted.NecR .snow := fun h ↦ nomatch h 1

end Weather

/-! ### Modality with topoi (§6.4)

The last version of `nec` and `poss`, (23)–(24), takes a topos in place of Kratzer's ideal. -/

/-- A topos (20) is a dependent type from situations of a background type to types. -/
abbrev Topos := Parametric Type

/-- Two types are compatible (17) when something is of both. -/
def Compatible (T₁ T₂ : Type) : Prop := Nonempty (T₁ × T₂)

/-- A witness of `nec(T, B, τ)` (23) is a situation of the background type `B`, with `B` a subtype
of the topos's domain and the type the topos returns for the situation a subtype of `T`. -/
structure Nec (T B : Type) (τ : Topos) where
  sit : B
  sub : B → τ.bg
  incl : τ.fg (sub sit) → T

/-- A witness of `poss(T, B, τ)` (24) is as for `Nec`, with the returned type compatible with
`T`. -/
structure Poss (T B : Type) (τ : Topos) where
  sit : B
  sub : B → τ.bg
  compat : Compatible (τ.fg (sub sit)) T

/-- Necessity yields possibility when the topos returns an inhabited type. -/
def Nec.toPoss {T B : Type} {τ : Topos} (h : Nec T B τ) (hne : Nonempty (τ.fg (h.sub h.sit))) :
    Poss T B τ :=
  ⟨h.sit, h.sub, hne.map fun w ↦ (w, h.incl w)⟩

/-! #### *Mary should eat her broccoli* (25)–(31)

Eating the broccoli is necessary under the deontic topos and under the bouletic one, (29). -/

namespace Dinner

inductive Ind | broccoli | mary | plate deriving DecidableEq, Repr

-- The ptypes of the base situation (26), each witnessed by its fact.
inductive Broccoli : Ind → Type | mk : Broccoli .broccoli
inductive Child : Ind → Type | mk : Child .mary
inductive Plate : Ind → Type | mk : Plate .plate
inductive Have : Ind → Ind → Type | mk : Have .mary .plate
inductive On : Ind → Ind → Type | mk : On .broccoli .plate
inductive Love : Ind → Ind → Type | mk : Love .mary .broccoli
inductive Eat : Ind → Ind → Type | mk : Eat .mary .broccoli

/-- Food, of which broccoli is a subtype (27), is witnessed by broccoli. -/
inductive Food : Ind → Type | ofBroccoli {x : Ind} : Broccoli x → Food x

/-- The base situation type (26) has its manifest fields fixed here by the ptypes' witnesses. -/
structure Base where
  (x : Ind) (c₁ : Broccoli x) (y : Ind) (c₂ : Child y) (z : Ind) (c₃ : Plate z)
  (e₁ : Have y z) (e₂ : On x z) (e₃ : Love y x)

/-- The background of the deontic topos (28a) is a child with food on her plate. -/
structure OnPlate where
  (x : Ind) (c₁ : Food x) (y : Ind) (c₂ : Child y) (z : Ind) (c₃ : Plate z)
  (e₁ : Have y z) (e₂ : On x z)

/-- The background of the bouletic topos (28b) is a child loving some food. -/
structure Loves where
  (x : Ind) (c₁ : Food x) (y : Ind) (c₂ : Child y) (e₃ : Love y x)

/-- The deontic topos τ₁ (28a) sends a child with food on her plate to her eating it. -/
def deontic : Topos := ⟨OnPlate, fun r ↦ Eat r.y r.x⟩

/-- The bouletic topos τ₂ (28b) sends a child loving some food to her eating it. -/
def bouletic : Topos := ⟨Loves, fun r ↦ Eat r.y r.x⟩

/-- The base situation has the broccoli on Mary's plate, and Mary loving it. -/
def base : Base := ⟨.broccoli, .mk, .mary, .mk, .plate, .mk, .mk, .mk, .mk⟩

/-- Eating the broccoli is necessary under the deontic topos (29a), the base type being a subtype of
the topos's domain by (27) and the topos returning the type itself (30). -/
def necDeontic : Nec (Eat .mary .broccoli) Base deontic where
  sit := base
  sub b := ⟨b.x, .ofBroccoli b.c₁, b.y, b.c₂, b.z, b.c₃, b.e₁, b.e₂⟩
  incl := id

/-- Eating the broccoli is necessary under the bouletic topos as well (29b). -/
def necBouletic : Nec (Eat .mary .broccoli) Base bouletic where
  sit := base
  sub b := ⟨b.x, .ofBroccoli b.c₁, b.y, b.c₂, b.e₃⟩
  incl := id

end Dinner

/-! ### Intensionality (§6.5)

An attitude matches its complement against a type of the agent's information state up to
relabelling, so whose postulates restrict the possibilities decides the report (pp. 261–262). -/

namespace ModalSystem

variable {M M' Ty Obj : Type} {ms : ModalSystem M Ty Obj} {r : Setoid Ty} {T₁ T₂ T₂' : Ty}

variable (ms r) in
/-- `T₁ ⊑⇝ T₂` (39) holds when `T₁` is a subtype, in the sense of Ch. 1 (55), of some relabelling of
`T₂`, the relabellings of a type being its class under `r`. -/
def SubtypeRelabel (T₁ T₂ : Ty) : Prop := ∃ T, r T₂ T ∧ ms.SubtypeI T₁ T

/-- Matching is blind to the relabelling of the complement (41). -/
theorem subtypeRelabel_congr (h : r T₂ T₂') :
    ms.SubtypeRelabel r T₁ T₂ ↔ ms.SubtypeRelabel r T₁ T₂' :=
  ⟨fun ⟨T, hT, hs⟩ ↦ ⟨T, r.iseqv.trans (r.iseqv.symm h) hT, hs⟩,
    fun ⟨T, hT, hs⟩ ↦ ⟨T, r.iseqv.trans h hT, hs⟩⟩

theorem SubtypeRelabel.comp (h : ms.SubtypeRelabel r T₁ T₂) (ι : M' → M) :
    ModalSystem.SubtypeRelabel (ms ∘ ι) r T₁ T₂ :=
  have ⟨T, hT, hs⟩ := h
  ⟨T, hT, hs.comp ι⟩

end ModalSystem

/-- An agent's total information state (91) gives the types of each agent's long-term memory,
religious beliefs and desires, and records which types are merges of a type with a complete point of
view on it (55). -/
structure InfoState (Agent Ty : Type) where
  ltm : Agent → Ty
  rbel : Agent → Ty
  des : Agent → Ty
  /-- `pov M T` says that `M` is the asymmetric merge `T ∧̣ T'` of `T` with a complete point of view
  `T'` on it. -/
  pov : Ty → Ty → Prop

/-- `s.Matches ms r I T` is the least relation closed under the two conditionals of (58), by which
the information type `I` matches `T` when `I ⊑⇝ T`, or when `I` matches some `T₁` whose merge with a
point of view on it is a subtype of `T` up to relabelling. Belief (58) matches the long-term memory,
worship (81) the religious beliefs against the quantifier exported over `worship†`, and `want†` (92)
the desires. -/
inductive InfoState.Matches {M Agent Ty Obj : Type} (s : InfoState Agent Ty)
    (ms : ModalSystem M Ty Obj) (r : Setoid Ty) (I : Ty) : Ty → Prop
  | subtype {T : Ty} : ms.SubtypeRelabel r I T → s.Matches ms r I T
  | pov {T₁ M T : Ty} : s.Matches ms r I T₁ → s.pov M T₁ → ms.SubtypeRelabel r M T →
      s.Matches ms r I T

namespace InfoState.Matches

variable {M M' Agent Ty Obj : Type} {s : InfoState Agent Ty} {ms : ModalSystem M Ty Obj}
  {r : Setoid Ty} {I T T' : Ty}

/-- An attitude toward a type is one toward any relabelling of it (41). -/
theorem congr (h : s.Matches ms r I T) (hT : r T T') : s.Matches ms r I T' := by
  cases h with
  | subtype h => exact .subtype ((ModalSystem.subtypeRelabel_congr hT).1 h)
  | pov h₁ hp h => exact .pov h₁ hp ((ModalSystem.subtypeRelabel_congr hT).1 h)

theorem comp (h : s.Matches ms r I T) (ι : M' → M) : s.Matches (ms ∘ ι) r I T := by
  induction h with
  | subtype h => exact .subtype (h.comp ι)
  | pov _ hp h ih => exact .pov ih hp (h.comp ι)

end InfoState.Matches

/-! #### Hesperus and Phosphorus, (52)–(53)

The ancients cannot exclude a possibility in which Phosphorus is another body than Venus; the
reporter can (p. 262). -/

namespace Venus

inductive Body | venus | mars

/-- The types are (52), and (53b), which identifies the second body with the first. -/
inductive Ty | twoStars | oneStar

/-- In the actual possibility Phosphorus is Venus; in the other, which the ancients cannot exclude,
it is Mars. -/
inductive Possib | actual | alternative
def phosphorus : Possib → Body | .actual => .venus | .alternative => .mars

/-- In the modal system Hesperus is Venus throughout, and the records are the pairs of their two
bodies. -/
def system : ModalSystem Possib Ty (Body × Body) := fun p ↦
  ⟨fun _ ↦ True,
    fun | .twoStars, (x, y) => x = .venus ∧ y = phosphorus p
        | .oneStar, (x, y) => (x = .venus ∧ y = phosphorus p) ∧ y = x,
    fun _ _ _ ↦ trivial⟩

/-- Before learning, the ancients' information state has (52) as its long-term memory. -/
def ancients : InfoState Unit Ty := ⟨fun _ ↦ .twoStars, fun _ ↦ .twoStars, fun _ ↦ .twoStars, ⊥⟩

/-- (53b) is a structural subtype of (52), having its fields and one more. -/
theorem oneStar_subtypeR : system.SubtypeR .oneStar .twoStars := fun _ _ h ↦ h.1

theorem not_twoStars_subtypeI : ¬ system.SubtypeI .twoStars .oneStar := fun h ↦
  nomatch (h .alternative trivial trivial (a := (.venus, .mars)) ⟨rfl, rfl⟩).2

theorem believe_twoStars : ancients.Matches system ⊥ (ancients.ltm ()) .twoStars :=
  .subtype ⟨_, rfl, fun _ _ _ _ h ↦ h⟩

/-- Under their own postulates the ancients do not believe that Hesperus is Phosphorus. -/
theorem not_believe_oneStar : ¬ ancients.Matches system ⊥ (ancients.ltm ()) .oneStar := by
  rintro (⟨T, rfl, hs⟩ | ⟨_, hp, _⟩)
  exacts [not_twoStars_subtypeI hs, hp]

/-- Under the reporter's postulates, which exclude the alternative, they do. -/
theorem believe_oneStar_reporter :
    ancients.Matches (system ∘ fun _ : Unit ↦ .actual) ⊥ (ancients.ltm ()) .oneStar :=
  .subtype ⟨_, rfl, fun _ _ _ _ h ↦ ⟨h, h.2.trans h.1.symm⟩⟩

/-- Learning (53) keeps the belief in (52). -/
theorem learned_believe_twoStars :
    { ancients with ltm := fun _ ↦ Ty.oneStar }.Matches system ⊥ .oneStar .twoStars :=
  .subtype ⟨_, rfl, oneStar_subtypeR.subtypeI⟩

end Venus

/-! #### Intensional transitive verbs, (63)–(68), (87)

Following Montague a transitive verb's predicate takes a quantifier (64), and postulates make
it extensional (65), a successful search a finding (66), and booking require existence (87). -/

/-- A transitive verb has a predicate taking a quantifier (64) and a variant `p†` between
individuals. -/
structure TransVerb (E : Type) where
  pred : E → Quant E → Type
  dagger : E → E → Type

/-- A verb is extensional (65) when its ptype is equivalent to the quantifier exported over `p†`. -/
def TransVerb.IsExtensional (v : TransVerb E) : Prop :=
  ∀ a Q, Nonempty (v.pred a Q ≃ Q (v.dagger a))

/-- With (65), *a finds a P* is witnessed only by a `P` that is found. -/
theorem TransVerb.IsExtensional.exists_of_semIndefArt {v : TransVerb E} (hv : v.IsExtensional)
    {a : E} {P : Ppty E} (h : Nonempty (v.pred a (SemIndefArt P))) :
    ∃ x, Nonempty (P x) ∧ Nonempty (v.dagger a x) :=
  have ⟨e⟩ := hv a (SemIndefArt P)
  have ⟨w⟩ := h
  ⟨(e w).x, ⟨(e w).pWit⟩, ⟨(e w).qWit⟩⟩

/-- A successful search is a finding (66). -/
structure SuccessfulSeek (E : Type) (seek find : E → Quant E → Type) where
  successful : Type → Type
  findOfSuccessful : ∀ a Q, successful (seek a Q) → find a Q

/-- With (66), and (65) for *find*, a successful search for a unicorn finds one, so there is
one (p. 268). -/
theorem SuccessfulSeek.exists_of_successful {seek : E → Quant E → Type} {find : TransVerb E}
    (hs : SuccessfulSeek E seek find.pred) (hf : find.IsExtensional) {a : E} {P : Ppty E}
    (h : Nonempty (hs.successful (seek a (SemIndefArt P)))) :
    ∃ x, Nonempty (P x) ∧ Nonempty (find.dagger a x) :=
  hf.exists_of_semIndefArt (h.map (hs.findOfSuccessful a _))

/-- Booking a monotone increasing quantifier's worth of tables requires tables to be, without
requiring a specific one (87). -/
def BookRequiresBeing (book : E → Quant E → Type) (be : Ppty E) : Prop :=
  ∀ a Q, Quant.IsMonIncr Q → Nonempty (book a Q) → Nonempty (Q be)

/-- Under (87), *Kim booked a table but there were no tables* is inconsistent (68a). -/
theorem exists_of_book {book : E → Quant E → Type} {be : Ppty E} (h : BookRequiresBeing book be)
    {a : E} {Table : Ppty E} (hb : Nonempty (book a (SemIndefArt Table))) :
    ∃ x, Nonempty (Table x) :=
  have ⟨w⟩ := h a _ (isMonIncr_semIndefArt Table) hb
  ⟨w.x, ⟨w.pWit⟩⟩

/-! ## Witness-based quantification (Ch. 7)

Purification lowers a property's restriction into its body, and a quantified ptype is witnessed
by a witness set with a function into or out of it. -/

/-- A restricted property (7b) places conditions on the individual in its domain and returns a
body. -/
structure Restricted (E : Type) where
  restr : E → Type
  body : (x : E) → restr x → Type

/-- A property is pure (7a) when its restriction is trivial. -/
def Restricted.IsPure (P : Restricted E) : Prop := ∀ x, Nonempty (Unique (P.restr x))

/-- Purification `𝔓(P)` (12) lowers the restriction into the body under the local context. -/
def Purify (P : Restricted E) : Ppty E := fun x ↦ (c : P.restr x) × P.body x c

/-- Universal purification `𝔓∀(P)` (13) requires the body under every way of meeting the
restriction. -/
def PurifyUniv (P : Restricted E) : Ppty E := fun x ↦ (c : P.restr x) → P.body x c

/-- Aligning two paths in the domain by a manifest field (Ch. 8, (51)–(52)) is a further restriction
of the domain, through which the body is read. -/
def Restricted.align (P : Restricted E) (R : E → Type) (f : ∀ x, R x → P.restr x) :
    Restricted E :=
  ⟨R, fun x c ↦ P.body x (f x c)⟩

/-- Property restriction `P|ℱ` (Ch. 5, (98)) narrows the domain by a property, aligning along the
projection. -/
def Restricted.restrictBy (P : Restricted E) (R : Ppty E) : Restricted E :=
  P.align (fun x ↦ R x × P.restr x) fun _ ↦ Prod.snd

theorem nonempty_purify_iff (P : Restricted E) (x : E) :
    Nonempty (Purify P x) ↔ ∃ c : P.restr x, Nonempty (P.body x c) :=
  nonempty_sigma

theorem nonempty_purifyUniv_iff (P : Restricted E) (x : E) :
    Nonempty (PurifyUniv P x) ↔ ∀ c : P.restr x, Nonempty (P.body x c) :=
  Classical.nonempty_pi

theorem Restricted.IsPure.nonempty_purify_iff_nonempty_purifyUniv {P : Restricted E}
    (h : P.IsPure) (x : E) : Nonempty (Purify P x) ↔ Nonempty (PurifyUniv P x) := by
  rw [nonempty_purify_iff, nonempty_purifyUniv_iff]
  obtain ⟨u⟩ := h x
  exact ⟨fun ⟨c, hc⟩ c' ↦ (u.uniq c).trans (u.uniq c').symm ▸ hc, fun hall ↦ ⟨u.default, hall _⟩⟩

/-! ### Types of witness sets (§7.2.4)

A witness set of `qʷ(P)` is a subset of `[↓P]` whose cardinality stands in a relation to
`|[↓P]|`, read on van Benthem's tree of numbers as Cooper reads determiners (p. 298). -/

/-- The cardinality clause of a type of witness sets is a relation between `|X|` and `|[↓P]|`. -/
abbrev CardRel := ℕ → ℕ → Prop

namespace CardRel

/-- `existʷ` (21) requires a singleton. Cooper notes the departure from [barwise-cooper-1981], whose
witness sets for *a* have at least one member. -/
def exist : CardRel := fun x _ ↦ x = 1

/-- `exist_plʷ` (22), plural *some*, requires at least two. -/
def existPl : CardRel := fun x _ ↦ 2 ≤ x

/-- `noʷ` (23)–(24) requires the empty set. -/
def no : CardRel := fun x _ ↦ x = 0

/-- `everyʷ` (25)–(26) requires the whole extension. -/
def every : CardRel := fun x p ↦ x = p

/-- `many_aʷ` (30) requires at least `θ`, as does `a_few_aʷ` (34) at the threshold of `few_aʷ`. -/
def atLeast (θ : ℕ) : CardRel := fun x _ ↦ θ ≤ x

/-- `few_aʷ` (32) requires at most `θ`. -/
def atMost (θ : ℕ) : CardRel := fun x _ ↦ x ≤ θ

/-- `mostʷ` (29), `many_pʷ` (31) and, at the threshold of `few_pʷ`, `a_few_pʷ` (35) require at least
the proportion `n / d` of a nonempty extension, cross-multiplied. -/
def propAtLeast (n d : ℕ) : CardRel := fun x p ↦ 0 < p ∧ n * p ≤ d * x

/-- `few_pʷ` (33) requires at most the proportion `n / d` of a nonempty extension. -/
def propAtMost (n d : ℕ) : CardRel := fun x p ↦ 0 < p ∧ d * x ≤ n * p

/-- The complement witness sets of `few_a` (81b) hold all but at most `θ` of the extension. -/
def compAtMost (θ : ℕ) : CardRel := fun x p ↦ p - θ ≤ x

/-- The complement witness sets of `few_p` (82b) hold at least the proportion `1 - n / d` of a
nonempty extension. -/
def compPropAtMost (n d : ℕ) : CardRel := fun x p ↦ 0 < p ∧ (d - n) * p ≤ d * x

theorem monotone_existPl (p : ℕ) : Monotone (existPl · p) := fun _ _ hxy h ↦ h.trans hxy

theorem monotone_atLeast (θ p : ℕ) : Monotone (atLeast θ · p) := fun _ _ hxy h ↦ h.trans hxy

theorem antitone_atMost (θ p : ℕ) : Antitone (atMost θ · p) := fun _ _ hxy h ↦ hxy.trans h

theorem monotone_propAtLeast (n d p : ℕ) : Monotone (propAtLeast n d · p) :=
  fun _ _ hxy h ↦ ⟨h.1, h.2.trans (Nat.mul_le_mul_left d hxy)⟩

theorem antitone_propAtMost (n d p : ℕ) : Antitone (propAtMost n d · p) :=
  fun _ _ hxy h ↦ ⟨h.1, (Nat.mul_le_mul_left d hxy).trans h.2⟩

theorem monotone_compAtMost (θ p : ℕ) : Monotone (compAtMost θ · p) :=
  fun _ _ hxy h ↦ h.trans hxy

theorem monotone_compPropAtMost (n d p : ℕ) : Monotone (compPropAtMost n d · p) :=
  fun _ _ hxy h ↦ ⟨h.1, h.2.trans (Nat.mul_le_mul_left d hxy)⟩

theorem ofSizes_no : NumberTree.ofSizes no = NumberTree.no := rfl

theorem ofSizes_every : NumberTree.ofSizes every = NumberTree.all := by
  grind [NumberTree.ofSizes, every, NumberTree.all]

theorem ofSizes_atLeast (θ : ℕ) : NumberTree.ofSizes (atLeast θ) = NumberTree.atLeast θ := rfl

theorem ofSizes_atMost (θ : ℕ) : NumberTree.ofSizes (atMost θ) = NumberTree.atMost θ := rfl

/-- The complement witness sets of `few_a` (81b), read on the tree of numbers, are the inner
negation of `few_aʷ`. -/
theorem innerNeg_ofSizes_compAtMost (θ : ℕ) :
    (NumberTree.ofSizes (compAtMost θ)).innerNeg = NumberTree.ofSizes (atMost θ) := by
  funext a b; grind [NumberTree.innerNeg_apply, NumberTree.ofSizes_apply, compAtMost, atMost]

/-- The complement witness sets of `few_p` (82b), read on the tree of numbers, are the inner
negation of `few_pʷ`. -/
theorem innerNeg_ofSizes_compPropAtMost (n d : ℕ) :
    (NumberTree.ofSizes (compPropAtMost n d)).innerNeg = NumberTree.ofSizes (propAtMost n d) := by
  funext a b
  simp only [NumberTree.innerNeg_apply, NumberTree.ofSizes_apply, compPropAtMost, propAtMost,
    eq_iff_iff]
  rw [Nat.sub_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  omega

end CardRel

section WitnessType

open scoped Finset

variable [Fintype E] (P : E → Prop) [DecidablePred P] {c : CardRel} {X : Finset E}

/-- The type `qʷ(P)` of witness sets (20)–(35) holds the subsets of the extension `[↓P]` whose
cardinality stands in the relation `c` to the extension's. -/
def WitnessType (c : CardRel) (X : Finset E) : Prop := X ⊆ ({x | P x} : Finset E) ∧ c #X #{x | P x}

variable {P}

/-- A witness set of `qʷ(P)` is a witness set over `P`, in the sense of [barwise-cooper-1981] (20a),
of the tree quantifier of `qʷ`'s relation. -/
theorem witnessType_iff_witness :
    WitnessType P c X ↔ Witness ((NumberTree.ofSizes c).toGQ P) P (· ∈ X) := by
  have hsub : X ⊆ ({x | P x} : Finset E) ↔ ∀ x, x ∈ X → P x := by simp [Finset.subset_iff]
  refine (and_congr_right fun h ↦ ?_).trans (and_congr_left' hsub)
  have hX : {x | P x ∧ x ∈ X} = (X : Set E) :=
    Set.ext fun x ↦ ⟨And.right, fun hx ↦ ⟨hsub.1 h x hx, hx⟩⟩
  have hP : {x | P x ∧ x ∈ X}.ncard + {x | P x ∧ x ∉ X}.ncard = {x | P x}.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _
  rw [hX, Set.ncard_coe_finset] at hP
  rw [NumberTree.toGQ_apply, NumberTree.ofSizes_apply, hX, Set.ncard_coe_finset, Nat.add_comm, hP,
    Set.ncard_setOf_eq_card_filter]

theorem everyW_iff_witness : WitnessType P .every X ↔ Witness (every P) P (· ∈ X) := by
  rw [witnessType_iff_witness, CardRel.ofSizes_every, ← every_eq_toGQ_all]

theorem noW_iff_witness : WitnessType P .no X ↔ Witness (no P) P (· ∈ X) := by
  rw [witnessType_iff_witness, CardRel.ofSizes_no, ← no_eq_toGQ_no]

/-- Cooper's singleton witness sets for `exist` (21) are the minimal B&C witness sets of
`some P`. -/
theorem existW_iff_minimal_witness [DecidableEq E] :
    WitnessType P .exist X ↔ Minimal (fun Y : Finset E ↦ Witness (GQ.some P) P (· ∈ Y)) X := by
  simp only [WitnessType, CardRel.exist, Witness, GQ.some, minimal_iff_forall_lt,
    Finset.card_eq_one]
  constructor
  · rintro ⟨hs, a, rfl⟩
    have hPa : P a := (Finset.mem_filter.1 (hs (Finset.mem_singleton_self a))).2
    refine ⟨⟨fun x hx ↦ Finset.mem_singleton.1 hx ▸ hPa, a, hPa, Finset.mem_singleton_self a⟩,
      fun Y hY ⟨_, b, _, hb⟩ ↦ ?_⟩
    rw [Finset.ssubset_singleton_iff.1 hY] at hb
    exact Finset.notMem_empty b hb
  · rintro ⟨⟨hs, a, hPa, haX⟩, hmin⟩
    refine ⟨fun x hx ↦ Finset.mem_filter.2 ⟨Finset.mem_univ x, hs x hx⟩, a, ?_⟩
    refine (eq_of_le_of_not_lt (Finset.singleton_subset_iff.2 haX) fun hlt ↦ hmin hlt
      ⟨fun x hx ↦ Finset.mem_singleton.1 hx ▸ hPa, a, hPa, Finset.mem_singleton_self a⟩).symm

/-- The complement in `[↓P]` of a witness set of `few_aʷ(P)` is a complement witness set
(81b). -/
theorem WitnessType.compAtMost_sdiff [DecidableEq E] {θ : ℕ} (h : WitnessType P (.atMost θ) X) :
    WitnessType P (.compAtMost θ) (({x | P x} : Finset E) \ X) :=
  ⟨Finset.sdiff_subset, by
    have := h.2
    simp only [CardRel.compAtMost, CardRel.atMost] at this ⊢
    rw [Finset.card_sdiff_of_subset h.1]
    omega⟩

end WitnessType

/-! ### Witness sets and probabilities (§7.3)

The probability (36) of a witness set within `[↓P]` is `|X| / |[↓P]|`, (51)–(52), so each
probabilistic witness condition (41)–(58) is its cardinal one. -/

section Probability

open MeasureTheory ProbabilityTheory
open scoped Finset ENNReal

variable [MeasurableSpace E] [MeasurableSingletonClass E] {X P : Finset E}

/-- The probability of a witness set given the property is the proportion of the extension it takes,
(51)–(52). -/
theorem uniformOn_of_subset (h : X ⊆ P) : uniformOn (P : Set E) X = #X / #P := by
  rw [uniformOn_apply_of_finite P.finite_toSet, Set.inter_eq_right.2 (Finset.coe_subset.2 h),
    Set.ncard_coe_finset, Set.ncard_coe_finset]

/-- The probability is `0` exactly for the empty witness set (43). -/
theorem uniformOn_eq_zero_iff_of_subset (h : X ⊆ P) : uniformOn (P : Set E) X = 0 ↔ X = ∅ := by
  rw [uniformOn_eq_zero_iff P.finite_toSet, Set.inter_eq_right.2 (Finset.coe_subset.2 h),
    Finset.coe_eq_empty]

/-- The probability is `1 / |[↓P]|` exactly for a singleton witness set (41). -/
theorem uniformOn_eq_inv_iff_of_subset (h : X ⊆ P) (hP : P.Nonempty) :
    uniformOn (P : Set E) X = (#P : ℝ≥0∞)⁻¹ ↔ #X = 1 := by
  have := uniformOn_eq_inv_ncard_iff (t := X) P.finite_toSet (Finset.coe_nonempty.2 hP)
  rwa [Set.inter_eq_right.2 (Finset.coe_subset.2 h), Set.ncard_coe_finset,
    Set.ncard_coe_finset] at this

/-- The probability is `1` exactly for the whole extension (44). -/
theorem uniformOn_eq_one_iff_of_subset (h : X ⊆ P) (hP : P.Nonempty) :
    uniformOn (P : Set E) X = 1 ↔ X = P := by
  rw [uniformOn_eq_one_iff P.finite_toSet (Finset.coe_nonempty.2 hP), Finset.coe_subset]
  exact ⟨h.antisymm, Eq.ge⟩

/-- The probabilistic witness condition for *most* (50) is the cardinal one (29). -/
theorem witnessType_propAtLeast_iff [Fintype E] {P : E → Prop} [DecidablePred P] {n d : ℕ}
    (hd : 0 < d) (hX : X ⊆ ({x | P x} : Finset E)) (hP : 0 < #{x | P x}) :
    WitnessType P (.propAtLeast n d) X ↔
      (n / d : ℝ≥0∞) ≤ uniformOn (({x | P x} : Finset E) : Set E) X := by
  rw [le_uniformOn_iff (Finset.finite_toSet _) (Finset.coe_nonempty.2 (Finset.card_pos.1 hP)),
    Set.inter_eq_right.2 (Finset.coe_subset.2 hX), Set.ncard_coe_finset, Set.ncard_coe_finset,
    ← ENNReal.mul_div_right_comm,
    ENNReal.div_le_iff (by simpa using hd.ne') (by simp), ← Nat.cast_mul, ← Nat.cast_mul,
    Nat.cast_le, mul_comm _ d]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨hX, hP, h⟩⟩

end Probability

/-- An experience base (37) holds the judgements `[sit = a, type = T]` an agent remembers. -/
abbrev ExperienceBase (E Ty : Type) := Finset (E × Ty)

/-- The extension of a type with respect to the experience base (38) holds the situations judged of
it. The estimate `p_𝔍(T₁ ‖ T₂)` (39) is the uniform measure on the extension of `T₂` at that of
`T₁`, the extension of `T₁ ∧ T₂` being the intersection (37b). -/
def ExperienceBase.extension {Ty : Type} [DecidableEq E] [DecidableEq Ty]
    (𝔍 : ExperienceBase E Ty) (T : Ty) : Finset E :=
  (𝔍.filter (·.2 = T)).image Prod.fst

/-! ### Witness conditions for quantificational ptypes (§7.4)

The general conditions (59) are Barwise and Cooper's two procedures for monotone quantifiers
(p. 298), so by their C11 each holds when the tree quantifier of `qʷ` does. -/

section WitnessCondition

open scoped Finset

variable [Fintype E] {P : E → Prop} [DecidablePred P] {c : CardRel} {Q Q' : Ppty E}

variable (P c Q) in
/-- The general witness condition for monotone increasing quantifiers (59a) provides a witness set
and a function from its members into the scope. -/
structure GeneralWCIncr where
  X : Finset E
  witness : WitnessType P c X
  f : ∀ a ∈ X, Q a

variable (P c Q) in
/-- The general witness condition for monotone decreasing quantifiers (59b) provides a witness set
and a function into it from the objects with both properties. -/
structure GeneralWCDecr where
  X : Finset E
  witness : WitnessType P c X
  f : ∀ a, P a → Q.Witnessed a → a ∈ X

variable (P c Q) in
/-- The particular witness conditions for `no` over `everyʷ(P)` (70) and for `few` over its
complement witness sets (85)–(86) provide a witness set of `qʷ(P)` whose members each preclude the
scope, the negated type (69) being a function into `Empty`. -/
abbrev ParticularWCNeg : Type := GeneralWCIncr P c fun a ↦ Q a → Empty

/-- A witness for a scope is one for any larger scope, so (59a) is increasing in the scope. -/
def GeneralWCIncr.mapScope (g : ∀ a, Q a → Q' a) (w : GeneralWCIncr P c Q) :
    GeneralWCIncr P c Q' :=
  ⟨w.X, w.witness, fun a ha ↦ g a (w.f a ha)⟩

/-- A witness for a scope is one for any smaller scope, so (59b) is decreasing in the scope. -/
def GeneralWCDecr.comapScope (g : ∀ a, Q' a → Q a) (w : GeneralWCDecr P c Q) :
    GeneralWCDecr P c Q' :=
  ⟨w.X, w.witness, fun a hP ⟨q⟩ ↦ w.f a hP ⟨g a q⟩⟩

open Classical in
/-- For a relation closed upwards in `|X|`, (59a) is witnessed exactly when the tree quantifier
holds of `P` and `Q`, by Barwise and Cooper's C11(i). -/
theorem nonempty_generalWCIncr_iff_toGQ (hc : ∀ p, Monotone (c · p)) :
    Nonempty (GeneralWCIncr P c Q) ↔ (NumberTree.ofSizes c).toGQ P Q.Witnessed := by
  rw [((NumberTree.conservative_toGQ _).livesOn P).monotone_apply_iff
    ((NumberTree.scopeMonotone_ofSizes hc).toGQ P)]
  refine ⟨fun ⟨w⟩ ↦ ⟨(· ∈ w.X), witnessType_iff_witness.1 w.witness, fun a ha ↦ ⟨w.f a ha⟩⟩,
    fun ⟨w, hw, hQ⟩ ↦ ⟨⟨{x | w x}, witnessType_iff_witness.2 ?_, fun a ha ↦ (hQ a ?_).some⟩⟩⟩
  · simpa using hw
  · simpa using ha

open Classical in
/-- For a relation closed downwards in `|X|`, (59b) is witnessed exactly when the tree quantifier
holds of `P` and `Q`, by C11(ii). -/
theorem nonempty_generalWCDecr_iff_toGQ (hc : ∀ p, Antitone (c · p)) :
    Nonempty (GeneralWCDecr P c Q) ↔ (NumberTree.ofSizes c).toGQ P Q.Witnessed := by
  rw [((NumberTree.conservative_toGQ _).livesOn P).antitone_apply_iff
    ((NumberTree.scopeAntitone_ofSizes hc).toGQ P)]
  refine ⟨fun ⟨w⟩ ↦ ⟨(· ∈ w.X), witnessType_iff_witness.1 w.witness,
      fun a ⟨hQ, hP⟩ ↦ w.f a hP hQ⟩,
    fun ⟨w, hw, hPQ⟩ ↦ ⟨⟨{x | w x}, witnessType_iff_witness.2 ?_,
      fun a hP hQ ↦ by simpa using hPQ a ⟨hQ, hP⟩⟩⟩⟩
  simpa using hw

open Classical in
theorem GeneralWCIncr.X_subset (w : GeneralWCIncr P c Q) :
    w.X ⊆ ({x | P x ∧ Q.Witnessed x} : Finset E) :=
  fun a ha ↦ Finset.mem_filter.2
    ⟨Finset.mem_univ a, (Finset.mem_filter.1 (w.witness.1 ha)).2, ⟨w.f a ha⟩⟩

open Classical in
theorem ParticularWCNeg.X_subset (w : ParticularWCNeg P c Q) :
    w.X ⊆ ({x | P x ∧ ¬ Q.Witnessed x} : Finset E) :=
  fun a ha ↦ Finset.mem_filter.2
    ⟨Finset.mem_univ a, (Finset.mem_filter.1 (w.witness.1 ha)).2, fun ⟨q⟩ ↦ (w.f a ha q).elim⟩

open Classical in
theorem GeneralWCDecr.subset_X (w : GeneralWCDecr P c Q) :
    ({x | P x ∧ Q.Witnessed x} : Finset E) ⊆ w.X :=
  fun a ha ↦ (Finset.mem_filter.1 ha).2.elim (w.f a)

open Classical in
/-- Under (59b) with a relation closed downwards, a witness can be traded for one whose witness set
is exactly the objects with both properties, which is the sense in which the general condition for
*few* makes REFSET anaphora available (p. 315). -/
theorem GeneralWCDecr.exists_X_eq (hc : ∀ p, Antitone (c · p)) (w : GeneralWCDecr P c Q) :
    ∃ w' : GeneralWCDecr P c Q, w'.X = ({x | P x ∧ Q.Witnessed x} : Finset E) :=
  ⟨⟨_, ⟨Finset.monotone_filter_right _ fun _ _ h ↦ h.1,
      hc _ (Finset.card_le_card w.subset_X) w.witness.2⟩,
    fun a hP hQ ↦ Finset.mem_filter.2 ⟨Finset.mem_univ a, hP, hQ⟩⟩, rfl⟩

/-- `everyʷ` is not closed upwards, but a witness set within `[↓P]` of its cardinality is all of it,
which gives the truth condition of (72). -/
theorem nonempty_generalWCIncr_every_iff :
    Nonempty (GeneralWCIncr P .every Q) ↔ every P Q.Witnessed :=
  ⟨fun ⟨w⟩ a ha ↦ ⟨w.f a (Finset.eq_of_subset_of_card_le w.witness.1 w.witness.2.ge ▸
      Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩)⟩,
    fun h ↦ ⟨⟨{x | P x}, ⟨subset_rfl, rfl⟩,
      fun a ha ↦ (h a (Finset.mem_filter.1 ha).2).some⟩⟩⟩

/-- A singleton set of an object with `P` all of whose members have `Q` exists just in case an
object has both (62), so the truth condition of (60) is *some*. -/
theorem nonempty_generalWCIncr_exist_iff [DecidableEq E] :
    Nonempty (GeneralWCIncr P .exist Q) ↔ GQ.some P Q.Witnessed :=
  ⟨fun ⟨w⟩ ↦
      have ⟨a, ha⟩ := Finset.card_eq_one.1 w.witness.2
      have haX : a ∈ w.X := ha ▸ Finset.mem_singleton_self a
      ⟨a, (Finset.mem_filter.1 (w.witness.1 haX)).2, ⟨w.f a haX⟩⟩,
    fun ⟨a, hPa, ⟨q⟩⟩ ↦ ⟨⟨{a},
      ⟨Finset.singleton_subset_iff.2 (Finset.mem_filter.2 ⟨Finset.mem_univ a, hPa⟩),
        Finset.card_singleton a⟩,
      fun _ hb ↦ (Finset.mem_singleton.1 hb).symm ▸ q⟩⟩⟩

/-- `many_a` (77) and `a_few_a` (89) are the counting quantifier *at least `θ`*. -/
theorem nonempty_generalWCIncr_atLeast_iff {θ : ℕ} :
    Nonempty (GeneralWCIncr P (.atLeast θ) Q) ↔ atLeast θ P Q.Witnessed :=
  nonempty_generalWCIncr_iff_toGQ (CardRel.monotone_atLeast θ)

/-- `few_a` (79) is *at most `θ`*. -/
theorem nonempty_generalWCDecr_atMost_iff {θ : ℕ} :
    Nonempty (GeneralWCDecr P (.atMost θ) Q) ↔ atMost θ P Q.Witnessed :=
  nonempty_generalWCDecr_iff_toGQ (CardRel.antitone_atMost θ)

/-- `most` (74), `many_p` (78) and `a_few_p` (90) are the proportional threshold quantifier
over a nonempty restrictor. -/
theorem nonempty_generalWCIncr_propAtLeast_iff {n d : ℕ} :
    Nonempty (GeneralWCIncr P (.propAtLeast n d) Q) ↔
      0 < {x | P x}.ncard ∧ (NumberTree.threshold n d).toGQ P Q.Witnessed := by
  rw [nonempty_generalWCIncr_iff_toGQ (CardRel.monotone_propAtLeast n d),
    ← Set.ncard_inter_add_ncard_sdiff_eq_ncard {x | P x} {x | Q.Witnessed x}]
  exact and_congr_left' (by rw [Nat.add_comm]; rfl)

/-- With the threshold `few` and `a few` share (34), `few_a` and `a_few_a` together are *exactly
`θ`*. -/
theorem few_and_aFew_iff {θ : ℕ} :
    Nonempty (GeneralWCDecr P (.atMost θ) Q) ∧ Nonempty (GeneralWCIncr P (.atLeast θ) Q) ↔
      exactly θ P Q.Witnessed := by
  rw [nonempty_generalWCDecr_atMost_iff, nonempty_generalWCIncr_atLeast_iff,
    exactly_eq_atLeast_inf_atMost]
  exact and_comm

theorem nonempty_particularWCNeg_iff_toGQ (hc : ∀ p, Monotone (c · p)) :
    Nonempty (ParticularWCNeg P c Q) ↔ (NumberTree.ofSizes c).innerNeg.toGQ P Q.Witnessed := by
  rw [nonempty_generalWCIncr_iff_toGQ hc, NumberTree.toGQ_innerNeg]
  exact iff_of_eq (congrArg ((NumberTree.ofSizes c).toGQ P) (funext fun _ ↦
    propext ⟨fun ⟨g⟩ ⟨q⟩ ↦ (g q).elim, fun h ↦ ⟨fun q ↦ (h ⟨q⟩).elim⟩⟩))

/-- The particular condition for `few_a` (85) is witnessed iff the general one (79) is, its
complement witness sets being the inner negation of `few_aʷ`. -/
theorem nonempty_particularWCNeg_compAtMost_iff {θ : ℕ} :
    Nonempty (ParticularWCNeg P (.compAtMost θ) Q) ↔ Nonempty (GeneralWCDecr P (.atMost θ) Q) := by
  rw [nonempty_particularWCNeg_iff_toGQ (CardRel.monotone_compAtMost θ),
    CardRel.innerNeg_ofSizes_compAtMost,
    nonempty_generalWCDecr_iff_toGQ (CardRel.antitone_atMost θ)]

/-- The particular condition for `few_p` (86) is witnessed iff the general one (80) is. -/
theorem nonempty_particularWCNeg_compPropAtMost_iff {n d : ℕ} :
    Nonempty (ParticularWCNeg P (.compPropAtMost n d) Q) ↔
      Nonempty (GeneralWCDecr P (.propAtMost n d) Q) := by
  rw [nonempty_particularWCNeg_iff_toGQ (CardRel.monotone_compPropAtMost n d),
    CardRel.innerNeg_ofSizes_compPropAtMost,
    nonempty_generalWCDecr_iff_toGQ (CardRel.antitone_propAtMost n d)]

/-- The set-based `no`, the witness set of every object with `P` each precluding `Q`, is
witnessed iff the particular condition (70) is. -/
theorem nonempty_particularWCNeg_every_iff :
    Nonempty (ParticularWCNeg P .every Q) ↔ Nonempty (ParticularWCNo (fun a ↦ PLift (P a)) Q) :=
  nonempty_generalWCIncr_every_iff.trans
    ⟨fun h ↦ ⟨⟨fun a p ↦ (h a p.down).some⟩⟩, fun ⟨w⟩ a p ↦ ⟨w.f a ⟨p⟩⟩⟩

/-- The particular condition for `exist` (63) gives the general one (60), with the singleton
of its individual. -/
def ParticularWCExist.toGeneralWCIncr [DecidableEq E] {R : Ppty E} (w : ParticularWCExist R Q)
    (h : ∀ a, R a → P a) : GeneralWCIncr P .exist Q :=
  ⟨{w.x}, ⟨Finset.singleton_subset_iff.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h _ w.pWit⟩),
    Finset.card_singleton _⟩, fun _ ha ↦ (Finset.mem_singleton.1 ha).symm ▸ w.qWit⟩

/-- The particular condition for `no` (70) gives the general one (67), with the empty witness
set. -/
def ParticularWCNo.toGeneralWCDecr {R : Ppty E} (w : ParticularWCNo R Q) (h : ∀ a, P a → R a) :
    GeneralWCDecr P .no Q :=
  ⟨∅, ⟨Finset.empty_subset _, Finset.card_empty⟩, fun a hP ⟨q⟩ ↦ (w.f a (h a hP) q).elim⟩

end WitnessCondition

/-! ### Anaphora sets (§7.4.1)

REFSET, MAXSET and COMPSET ([moxey-sanford-1987], p. 313) are read off the sets the witnesses
carry, MAXSET being the content's `restr` path. -/

/-- REFSET, MAXSET and COMPSET are the anaphora sets a quantified noun phrase can make available. -/
inductive AnaphoraRef where
  /-- REFSET is the witness individual or set, as in *A dog barked. It heard an intruder.*
  (103d). -/
  | refset
  /-- MAXSET is the full extension, as in *A dog barked. They do when they notice an intruder.*
  (103a). -/
  | maxset
  /-- COMPSET is the complement witness set, as in *Few dogs barked. They did not hear the
  intruder.* (113d). -/
  | compset
  deriving DecidableEq, Repr

open Classical in
/-- `ref.set P Q` is the set each anaphora-set kind names over the properties `P` and `Q`. -/
noncomputable def AnaphoraRef.set [Fintype E] (P : E → Prop) [DecidablePred P] (Q : Ppty E) :
    AnaphoraRef → Finset E
  | .refset => {x | P x ∧ Q.Witnessed x}
  | .maxset => {x | P x}
  | .compset => {x | P x ∧ ¬ Q.Witnessed x}

/-- REFSET and COMPSET are disjoint, so a nonempty witness set within the one is not within the
other, and no witness of (59a) supplies COMPSET, as (76) and (92) show for *most* and *a few*. -/
theorem AnaphoraRef.disjoint_set_refset_compset [Fintype E] (P : E → Prop) [DecidablePred P]
    (Q : Ppty E) : Disjoint (AnaphoraRef.refset.set P Q) (AnaphoraRef.compset.set P Q) := by
  classical
  simp only [AnaphoraRef.set, Finset.disjoint_left, Finset.mem_filter]
  exact fun _ h h' ↦ h'.2.2 h.2.2

/-- The witness conditions of §7.4 are told apart by the paths their witnesses provide. -/
inductive WitnessCondition where
  /-- The general condition (59a) provides a witness set and a function from it into the scope. -/
  | generalIncr
  /-- The general condition (59b) provides a witness set and a function into it from the objects
  with both properties. -/
  | generalDecr
  /-- The particular condition for `exist` (63) provides an individual with both properties. -/
  | particularExist
  /-- The particular condition for `no` (70) provides the set of all objects with the first
  property, each precluding the scope. -/
  | particularNo
  /-- The particular conditions for `few` (85)–(86) provide a complement witness set, each member
  precluding the scope. -/
  | particularFewComp
  deriving DecidableEq, Repr

namespace WitnessCondition

variable [Fintype E] (P : E → Prop) [DecidablePred P] (c : CardRel) (Q : Ppty E)

/-- `wc.Witness P c Q` is the type of witnesses of each condition over a restrictor `P`, a
cardinality relation `c` and a scope `Q`, the condition for `no` (70) fixing `everyʷ`. -/
def Witness : WitnessCondition → Type
  | .generalIncr => GeneralWCIncr P c Q
  | .generalDecr => GeneralWCDecr P c Q
  | .particularExist => ParticularWCExist (fun a ↦ PLift (P a)) Q
  | .particularNo => ParticularWCNeg P .every Q
  | .particularFewComp => ParticularWCNeg P c Q

variable {P c Q}

/-- A witness carries its witness set, or the singleton of its individual. -/
def set : (wc : WitnessCondition) → wc.Witness P c Q → Finset E
  | .generalIncr, w => GeneralWCIncr.X w
  | .generalDecr, w => GeneralWCDecr.X w
  | .particularExist, w => {ParticularWCExist.x w}
  | .particularNo, w => GeneralWCIncr.X w
  | .particularFewComp, w => GeneralWCIncr.X w

/-- `wc.anaphora` is the anaphora set a condition's witness provides beyond the content's `restr`
field. -/
def anaphora : WitnessCondition → AnaphoraRef
  | .generalIncr | .generalDecr | .particularExist => .refset
  | .particularNo | .particularFewComp => .compset

/-- Every witnessed condition has a witness whose set lies in the condition's anaphora set, for
(59b) under a relation closed downwards, so the anaphora set is read off the witnesses. -/
theorem exists_set_subset (wc : WitnessCondition)
    (hc : wc = .generalDecr → ∀ p, Antitone (c · p)) (w : wc.Witness P c Q) :
    ∃ w' : wc.Witness P c Q, wc.set w' ⊆ wc.anaphora.set P Q := by
  cases wc with
  | generalIncr => exact ⟨w, GeneralWCIncr.X_subset w⟩
  | generalDecr =>
    obtain ⟨w', h⟩ := GeneralWCDecr.exists_X_eq (hc rfl) w
    exact ⟨w', h.le⟩
  | particularExist =>
    classical
    exact ⟨w, Finset.singleton_subset_iff.2 (Finset.mem_filter.2
      ⟨Finset.mem_univ _, (ParticularWCExist.pWit w).down, ⟨ParticularWCExist.qWit w⟩⟩)⟩
  | particularNo => exact ⟨w, ParticularWCNeg.X_subset w⟩
  | particularFewComp => exact ⟨w, ParticularWCNeg.X_subset w⟩

end WitnessCondition

/-- The English fragment names eight quantifier relations. -/
inductive QuantName where
  | exist | existPl | no | every | most | many | few | aFew
  deriving DecidableEq, Repr

/-- §7.4 assigns each quantifier relation its witness conditions, the particular ones for `exist`
(63) and `no` (70), the general one elsewhere, and for `few` the general (79)–(80) and the
particular (85)–(86) as alternatives. -/
def QuantName.conditions : QuantName → List WitnessCondition
  | .exist => [.particularExist]
  | .existPl | .every | .most | .many | .aFew => [.generalIncr]
  | .no => [.particularNo]
  | .few => [.generalDecr, .particularFewComp]

/-- A quantified noun phrase makes available MAXSET, from the content's `restr` field, and the set
of each of its witness conditions. -/
def anaphoraAvailable (q : QuantName) : List AnaphoraRef :=
  .maxset :: q.conditions.map WitnessCondition.anaphora

/-! ### The dogs fragment

Three dogs, two of them barking, witness *a dog barks* (63), *most dogs bark* (74) and *few
dogs barked* (87), and refute *no dog barks*. -/

namespace Dogs

open MeasureTheory ProbabilityTheory
open scoped Finset ENNReal

inductive Ind | fido | rex | spot | luna deriving DecidableEq, Repr, Fintype
instance : MeasurableSpace Ind := ⊤
instance : MeasurableSingletonClass Ind := ⟨fun _ ↦ trivial⟩
def IsDog (x : Ind) : Prop := x ≠ .luna
instance : DecidablePred IsDog := fun _ ↦ by unfold IsDog; infer_instance
def Bark (x : Ind) : Prop := x = .fido ∨ x = .spot
instance : DecidablePred Bark := fun _ ↦ by unfold Bark; infer_instance

/-- The property `dog'` (61a) lifts being a dog to a type. -/
def dog : Ppty Ind := fun x ↦ PLift (IsDog x)

/-- The property `bark'` (61b) lifts barking to a type. -/
def bark : Ppty Ind := fun x ↦ PLift (Bark x)

/-- *A dog barks* (63) is witnessed by Fido. -/
def aDogBarks : SemIndefArt dog bark := ⟨.fido, ⟨nofun⟩, ⟨.inl rfl⟩⟩

theorem noDogBarks_isEmpty : IsEmpty (SemNo dog bark) :=
  ⟨fun ⟨f⟩ ↦ (f .fido ⟨nofun⟩ ⟨.inl rfl⟩).elim⟩

/-- *No dog barks* with the witness set of every dog, whose members *they* picks up in (71), is
false as well. -/
theorem noDogBarksSet_isEmpty : IsEmpty (ParticularWCNeg IsDog .every bark) :=
  ⟨fun w ↦ (nonempty_particularWCNeg_every_iff.1 ⟨w⟩).elim noDogBarks_isEmpty.false⟩

/-- *Most dogs bark* (74) is witnessed by the set of Fido and Spot, two of the three dogs, each
barking, which *they* picks up in (75). The threshold `3 / 5` lies in the range `.5 < θ_most(P) < 1`
of the book's appendix type list. -/
def mostDogsBark : GeneralWCIncr IsDog (.propAtLeast 3 5) bark :=
  ⟨{.fido, .spot}, ⟨by decide, by simp only [CardRel.propAtLeast]; decide⟩,
    fun a ha ↦ ⟨by revert a; decide⟩⟩

/-- By its probability (50), the same witness set holds at least three fifths of the dogs. -/
theorem mostDogsBark_uniformOn :
    (3 / 5 : ℝ≥0∞) ≤ uniformOn (({x | IsDog x} : Finset Ind) : Set Ind) mostDogsBark.X := by
  exact_mod_cast (witnessType_propAtLeast_iff (by decide) mostDogsBark.witness.1 (by decide)).1
    mostDogsBark.witness

/-- *Few dogs barked. They didn't hear the intruder* (87) is witnessed under the particular
condition for `few_p` (86), with `θ_fewp = 2 / 3`, by the complement witness set of Rex, who does
not bark. -/
def fewDogsBark : ParticularWCNeg IsDog (.compPropAtMost 2 3) bark :=
  ⟨{.rex}, ⟨by decide, by simp only [CardRel.compPropAtMost]; decide⟩,
    fun a ha ⟨h⟩ ↦ absurd h (Finset.mem_singleton.1 ha ▸ by decide)⟩

/-- Under the general condition (80) the same content says that at most two thirds of the dogs
bark. -/
theorem fewDogsBark_general : Nonempty (GeneralWCDecr IsDog (.propAtMost 2 3) bark) :=
  nonempty_particularWCNeg_compPropAtMost_iff.1 ⟨fewDogsBark⟩

inductive Ty | dog | bark deriving DecidableEq, Repr

/-- An experience base of three dogs, two of which were judged to bark. -/
def experience : ExperienceBase Ind Ty :=
  {(.fido, .dog), (.rex, .dog), (.spot, .dog), (.fido, .bark), (.spot, .bark)}

/-- The estimate `p_𝔍(bark ‖ dog)` (39) is two thirds. -/
theorem bark_given_dog :
    uniformOn (experience.extension .dog : Set Ind) (experience.extension .bark) = 2 / 3 := by
  rw [uniformOn_apply_finset,
    show #(experience.extension .dog ∩ experience.extension .bark) = 2 by decide,
    show #(experience.extension .dog) = 3 by decide]
  norm_num

end Dogs

/-! ## Type-based underspecification (Ch. 8)

Storage and retrieval give scope ambiguity (17)–(19), locality marking constrains anaphoric
combination (28)–(88), and localisation with purification gives the donkey readings
(49)–(66). -/

/-! ### Parametric contents and their context types (§8.2–8.3) -/

/-- A context type (§4.3, (16); §8.2, (10); §8.3, (82)) says what a content requires of the context,
namely the quantifiers in the store `𝔮` (11) under their labels and the labels of pronouns, `𝔰`,
among them those marked local, `𝔩`, and reflexive, `𝔯`. -/
structure CntxtType (E : Type) where
  store : ℕ → Option ((ℕ → E) → Quant E)
  pronouns : Finset ℕ
  locals : Finset ℕ
  reflexives : Finset ℕ

namespace CntxtType

/-- The empty context type requires nothing. -/
instance : EmptyCollection (CntxtType E) := ⟨⟨fun _ ↦ none, ∅, ∅, ∅⟩⟩

/-- The merge `∧̣` of two context types joins their fields, the first's store taking precedence. -/
def merge (a b : CntxtType E) : CntxtType E :=
  ⟨fun i ↦ (a.store i).or (b.store i), a.pronouns ∪ b.pronouns, a.locals ∪ b.locals,
    a.reflexives ∪ b.reflexives⟩

/-- `T ⊖ xᵢ` (18) removes the label from the store and the pronouns, with the markings that depend
on it (19). -/
def erase (T : CntxtType E) (i : ℕ) : CntxtType E :=
  ⟨Function.update T.store i none, T.pronouns.erase i, T.locals.erase i, T.reflexives.erase i⟩

end CntxtType

/-- A parametric content (14) over the contexts of Ch. 8, which assign individuals to labels, pairs
a background context type with a foreground giving a content for each assignment. -/
structure Content (E : Type) (C : Type*) where
  bg : CntxtType E
  fg : (ℕ → E) → C

namespace Content

variable {C D : Type*}

/-- Application `α @ β` applies a functor content to an argument, merging the backgrounds. -/
def app (α : Content E (C → D)) (β : Content E C) : Content E D :=
  ⟨α.bg.merge β.bg, fun g ↦ α.fg g (β.fg g)⟩

/-- `α.given i a` is the content given the value `a` for the label `i`, the context specification
`c[𝔰.xᵢ = a]` behind retrieval (19), reflexivisation (84) and the alignment of a pronoun with its
antecedent (42)–(44). -/
def given (α : Content E C) (i : ℕ) (a : E) : Content E C :=
  ⟨α.bg.erase i, fun g ↦ α.fg (Function.update g i a)⟩

/-- A content is plugged (16) when it requires nothing in the store. -/
def IsPlugged (α : Content E C) : Prop := ∀ i, α.bg.store i = none

/-- Storage (17) puts the quantifier into the store under `i`, and the content of the label's value
takes its place. -/
def store (i : ℕ) (𝒬 : Content E (Quant E)) : Content E (Quant E) :=
  ⟨CntxtType.merge ⟨Function.update (fun _ ↦ none) i (some 𝒬.fg), {i}, ∅, ∅⟩ 𝒬.bg,
    fun g ↦ SemPropName (g i)⟩

/-- A pronoun (75) has the content of its label's value, marked local. -/
def pronoun (i : ℕ) : Content E (Quant E) :=
  ⟨⟨fun _ ↦ none, {i}, {i}, ∅⟩, fun g ↦ SemPropName (g i)⟩

/-- A reflexive (83) has the content of its label's value, marked reflexive. -/
def reflexive (i : ℕ) : Content E (Quant E) :=
  ⟨⟨fun _ ↦ none, {i}, ∅, {i}⟩, fun g ↦ SemPropName (g i)⟩

/-- Retrieval (19) gives the quantifier stored under `i` scope over the content as a property of the
label's value, and removes it from the store; with nothing stored there the content is unchanged.
The purification that (19) applies to the property is the identity here, the foreground being total
in the assignment. -/
def retrieve (i : ℕ) (α : Content E Type) : Content E Type :=
  match α.bg.store i with
  | some 𝒬 => ⟨α.bg.erase i, fun g ↦ 𝒬 g fun a ↦ (α.given i a).fg g⟩
  | none => α

/-- The relabelling `[α]𝔰.xⱼ ⇝ 𝔰.xᵢ` reads the label `j` as `i`, and drops `j` from the
background. -/
def relabel (α : Content E C) (j i : ℕ) : Content E C :=
  ⟨α.bg.erase j, fun g ↦ α.fg (Function.update g j (g i))⟩

/-- Anaphoric combination `α @ᵢ,ⱼ β` (28), (76) is defined when the functor requires the
label `i` and the argument requires `j` as a pronoun that is neither a stored quantifier's
nor marked local. -/
def AnaphoricDefined (α : Content E (C → D)) (i j : ℕ) (β : Content E C) : Prop :=
  i ∈ α.bg.pronouns ∧ j ∈ β.bg.pronouns ∧ β.bg.store j = none ∧ j ∉ β.bg.locals

instance (α : Content E (C → D)) (i j : ℕ) (β : Content E C) :
    Decidable (α.AnaphoricDefined i j β) := by
  unfold AnaphoricDefined; infer_instance

/-- Anaphoric combination `α @ᵢ,ⱼ β` (28) is the application with `j` relabelled to `i`. -/
def anaphoricApp (α : Content E (C → D)) (i j : ℕ) (β : Content E C) : Content E D :=
  (α.app β).relabel j i

/-- The boundary operation `B` (77) clears the local marking at the sentence. -/
def boundary (α : Content E C) : Content E C := ⟨{ α.bg with locals := ∅ }, α.fg⟩

/-- Reflexivisation `ℜ` (84) binds the reflexive `i` to the property's argument, discharging its
label and clearing all reflexive marking. -/
def reflexivize (P : Content E (Ppty E)) (i : ℕ) : Content E (Ppty E) :=
  ⟨{ P.bg.erase i with reflexives := ∅ }, fun g x ↦ (P.given i x).fg g x⟩

/-- Principle A (85) excludes at the verb phrase (88) a content with a reflexive still marked. -/
def IsAnaphorFree (α : Content E C) : Prop := α.bg.reflexives = ∅

instance (α : Content E C) : Decidable α.IsAnaphorFree := by
  unfold IsAnaphorFree; infer_instance

end Content

/-! #### *Every boy hugged a dog* (§8.1, (1))

With each boy hugging a different dog, the surface reading (1a) is witnessed and the inverse
reading (1b) is not. -/

namespace Hugging

inductive Ind | tom | bill | fido | rex deriving DecidableEq
def Boy : Ppty Ind | .tom | .bill => PUnit | _ => Empty
def Dog : Ppty Ind | .fido | .rex => PUnit | _ => Empty
def Hug : Ind → Ind → Type | .tom, .fido | .bill, .rex => PUnit | _, _ => Empty
def everyBoy : Content Ind (Quant Ind) := ⟨∅, fun _ ↦ SemUniversal Boy⟩
def aDog : Content Ind (Quant Ind) := ⟨∅, fun _ ↦ SemIndefArt Dog⟩

/-- *hugged* is a transitive verb over its object quantifier (Ch. 6, (63)). -/
def hugged : Content Ind (Quant Ind → Ppty Ind) := ⟨∅, fun _ Q x ↦ Q (Hug x)⟩

/-- Reading (1a) keeps the quantifiers in surface order. -/
def surface : Content Ind Type := everyBoy.app (hugged.app aDog)

/-- Reading (1b) stores the object quantifier (17) and retrieves it (19) over the sentence. -/
def inverse : Content Ind Type := (everyBoy.app (hugged.app (Content.store 0 aDog))).retrieve 0

theorem not_isPlugged_stored : ¬ (everyBoy.app (hugged.app (Content.store 0 aDog))).IsPlugged :=
  fun h ↦ nomatch h 0

theorem isPlugged_inverse : inverse.IsPlugged := fun i ↦ by rcases i with _ | i <;> rfl

/-- (1b) is the indefinite over the universal. -/
theorem inverse_fg (g : ℕ → Ind) :
    inverse.fg g = SemIndefArt Dog fun y ↦ SemUniversal Boy fun x ↦ Hug x y :=
  rfl

/-- Reading (1a) is witnessed, every boy having hugged a dog. -/
def surfaceWitness (g : ℕ → Ind) : surface.fg g
  | .tom, _ => ⟨.fido, ⟨⟩, ⟨⟩⟩
  | .bill, _ => ⟨.rex, ⟨⟩, ⟨⟩⟩
  | .fido, h => nomatch h
  | .rex, h => nomatch h

/-- Reading (1b) is not, no dog having been hugged by every boy. -/
theorem inverse_isEmpty (g : ℕ → Ind) : IsEmpty (inverse.fg g) :=
  ⟨fun | ⟨.fido, _, h⟩ => nomatch h .bill ⟨⟩ | ⟨.rex, _, h⟩ => nomatch h .tom ⟨⟩
       | ⟨.tom, h, _⟩ => nomatch h | ⟨.bill, h, _⟩ => nomatch h⟩

end Hugging

/-! ### Localisation and donkey anaphora (§8.3) -/

/-- Localisation `ℒ` (49) folds the assignment a content requires into the property's domain under
the label `𝔠`, giving a restricted property. -/
def localize (P : Content E (Ppty E)) : Restricted E := ⟨fun _ ↦ ℕ → E, fun x g ↦ P.fg g x⟩

/-! #### *No dog which chases a cat catches it* (46a)

Under the particular condition for `no`, (55) says that no dog which chases a cat catches the
cat it chases. -/

namespace Chasing

inductive Ind | dog₁ | dog₂ | cat₁ | cat₂ deriving DecidableEq
def Dog : Ppty Ind | .dog₁ | .dog₂ => PUnit | _ => Empty
def Cat : Ppty Ind | .cat₁ | .cat₂ => PUnit | _ => Empty
def Chase : Ind → Ind → Type | .dog₁, .cat₁ | .dog₂, .cat₂ => PUnit | _, _ => Empty

/-- *catches* is a transitive verb over its object quantifier (Ch. 6, (63)). -/
def catches (Catch : Ind → Ind → Type) : Content Ind (Quant Ind → Ppty Ind) :=
  ⟨∅, fun _ Q x ↦ Q (Catch x)⟩

/-- In *catches it* (47) the context supplies the referent of the pronoun's label. -/
def catchesIt (Catch : Ind → Ind → Type) : Content Ind (Ppty Ind) :=
  (catches Catch).app (Content.pronoun 1)

/-- The restrictor *dog which chases a cat*, as the domain of (50), holds a dog with a cat it
chases. -/
def DogChasesACat : Ppty Ind := fun x ↦ Dog x × ((c : Ind) × Cat c × Chase x c)

/-- The scope (51) is *catches it* localised, restricted by the restrictor and aligned so that the
pronoun's label is the chased cat. -/
def scope (Catch : Ind → Ind → Type) : Restricted Ind :=
  ((localize (catchesIt Catch)).restrictBy DogChasesACat).align DogChasesACat
    fun _ r ↦ (r, fun _ ↦ r.2.1)

/-- The sentence (55) is `no(restr, scope)` with the scope purified. -/
def Sentence (Catch : Ind → Ind → Type) : Type := SemNo DogChasesACat (Purify (scope Catch))

/-- The sentence is true when no dog catches anything. -/
def noCatching : Sentence (fun _ _ ↦ Empty) := ⟨fun _ _ ⟨_, h⟩ ↦ h⟩

theorem sentence_isEmpty : IsEmpty (Sentence Chase) :=
  ⟨fun ⟨f⟩ ↦ (f .dog₁ ⟨⟨⟩, .cat₁, ⟨⟩, ⟨⟩⟩ ⟨⟨⟨⟩, .cat₁, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩).elim⟩

end Chasing

/-! #### *Every farmer who owns a donkey likes it* (58)–(66)

`𝔓` gives the weak reading and `𝔓∀` the strong one of [kanazawa-1994], separated by a farmer who
owns two donkeys and likes one. -/

namespace Donkeys

inductive Ind | farmer₁ | farmer₂ | donkey₁ | donkey₂ deriving DecidableEq
def Farmer : Ppty Ind | .farmer₁ | .farmer₂ => PUnit | _ => Empty
def Donkey : Ppty Ind | .donkey₁ | .donkey₂ => PUnit | _ => Empty

/-- The first farmer owns both donkeys, the second the second. -/
def Own : Ind → Ind → Type
  | .farmer₁, .donkey₁ | .farmer₁, .donkey₂ | .farmer₂, .donkey₂ => PUnit
  | _, _ => Empty

def Like : Ind → Ind → Type | .farmer₁, .donkey₁ | .farmer₂, .donkey₂ => PUnit | _, _ => Empty

/-- *farmer who owns a donkey* holds a farmer with a donkey she owns. -/
def FarmerOwnsADonkey : Ppty Ind := fun x ↦ Farmer x × ((d : Ind) × Donkey d × Own x d)

/-- *likes* is a transitive verb over its object quantifier (Ch. 6, (63)). -/
def likes : Content Ind (Quant Ind → Ppty Ind) := ⟨∅, fun _ Q x ↦ Q (Like x)⟩

/-- *likes it* (61) is localised (62)–(63), restricted (64) and aligned (65), the pronoun's label
being the owned donkey. -/
def likesIt : Restricted Ind :=
  ((localize (likes.app (Content.pronoun 1))).restrictBy FarmerOwnsADonkey).align FarmerOwnsADonkey
    fun _ r ↦ (r, fun _ ↦ r.2.1)

/-- The weak reading (59) holds, every farmer who owns a donkey liking some donkey she owns. -/
def weak : SemUniversal FarmerOwnsADonkey (Purify likesIt)
  | .farmer₁, _ => ⟨⟨⟨⟩, .donkey₁, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  | .farmer₂, _ => ⟨⟨⟨⟩, .donkey₂, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  | .donkey₁, ⟨h, _⟩ => nomatch h
  | .donkey₂, ⟨h, _⟩ => nomatch h

/-- The strong reading (60), (66) fails, since the first farmer does not like the second donkey. -/
theorem strong_isEmpty : IsEmpty (SemUniversal FarmerOwnsADonkey (PurifyUniv likesIt)) :=
  ⟨fun f ↦ nomatch f .farmer₁ ⟨⟨⟩, .donkey₁, ⟨⟩, ⟨⟩⟩ ⟨⟨⟩, .donkey₂, ⟨⟩, ⟨⟩⟩⟩

end Donkeys

/-! ### Pronouns, locality and reflexives (30)–(36), (67)–(88)

A stored *no girl* binds *she* past the embedded boundary, the local *him* of *Sam likes him*
cannot combine with *Sam* (Principle B), and *himself* is bound by reflexivisation. -/

namespace Binding

inductive Ind | sam | kim | ann deriving DecidableEq
def Girl : Ppty Ind | .ann => PUnit | _ => Empty
inductive Fail : Ind → Type
inductive Like : Ind → Ind → Type | mk : Like .sam .sam

/-- A witness of `think(x, T)` is a thought with the type's witness. -/
structure Think (x : Ind) (T : Type) where
  thought : T

def sam : Content Ind (Quant Ind) := ⟨∅, fun _ ↦ SemPropName .sam⟩
def noGirl : Content Ind (Quant Ind) := ⟨∅, fun _ ↦ SemNo Girl⟩
def failed : Content Ind (Ppty Ind) := ⟨∅, fun _ ↦ Fail⟩

/-- *thinks* takes a ptype of thinking. -/
def thinks : Content Ind (Type → Ppty Ind) := ⟨∅, fun _ T x ↦ Think x T⟩

/-- *likes* is a transitive verb over its object quantifier (Ch. 6, (63)). -/
def likes : Content Ind (Quant Ind → Ppty Ind) := ⟨∅, fun _ Q x ↦ Q (Like x)⟩

/-- In *thinks she failed* (31) the embedded *she failed* is a sentence, so its pronoun is no longer
local past the boundary. -/
def thinksSheFailed : Content Ind (Ppty Ind) :=
  thinks.app (Content.boundary ((Content.pronoun 1).app failed))

/-- The stored subject (34) combines anaphorically with the pronoun, (35). -/
theorem anaphoricDefined_thinksSheFailed :
    (Content.store 0 noGirl).AnaphoricDefined 0 1 thinksSheFailed := by
  decide

theorem not_anaphoricDefined_of_no_boundary :
    ¬ (Content.store 0 noGirl).AnaphoricDefined 0 1
      (thinks.app ((Content.pronoun 1).app failed)) := by
  decide

/-- *No girl thinks she failed* (36), the stored *no girl* retrieved over the anaphoric combination,
is `no(girl', λx. think(x, fail(x)))`. -/
theorem noGirlThinksSheFailed (g : ℕ → Ind) :
    (((Content.store 0 noGirl).anaphoricApp 0 1 thinksSheFailed).retrieve 0).fg g =
      SemNo Girl (fun x ↦ Think x (Fail x)) :=
  rfl

/-- In *likes him* (69) the pronoun is marked local. -/
def likesHim : Content Ind (Ppty Ind) := likes.app (Content.pronoun 1)

/-- Within the clause *him* cannot be related to the stored *Sam* (71), which is Principle B,
(72)–(73). -/
theorem not_anaphoricDefined_likesHim :
    ¬ (Content.store 0 sam).AnaphoricDefined 0 1 likesHim := by
  decide

/-- *likes himself* is reflexivised (84). -/
def likesHimself : Content Ind (Ppty Ind) := (likes.app (Content.reflexive 1)).reflexivize 1

/-- The reflexivised property is `like(x, x)` (68c). -/
theorem likesHimself_fg (g : ℕ → Ind) (x : Ind) : likesHimself.fg g x = Like x x := rfl

/-- Reflexivisation clears the marking for the verb phrase's filter (88). -/
theorem isAnaphorFree_likesHimself : likesHimself.IsAnaphorFree := by decide

theorem not_isAnaphorFree_likesReflexive : ¬ (likes.app (Content.reflexive 1)).IsAnaphorFree := by
  decide

/-- *Sam likes himself* (73), the stored *Sam* retrieved, is witnessed by Sam's liking
himself. -/
def samLikesHimself (g : ℕ → Ind) : (((Content.store 0 sam).app likesHimself).retrieve 0).fg g :=
  Like.mk

end Binding

/-! #### *A man walked. He whistled.* (37)–(44)

The pronoun's label is given the man of the previous utterance's witness (42)–(44). -/

namespace Whistling

inductive Ind | john | mary deriving DecidableEq
def Man : Ppty Ind | .john => PUnit | .mary => Empty
def Walk : Ppty Ind | .john => PUnit | .mary => Empty
def Whistle : Ppty Ind | .john => PUnit | .mary => Empty

/-- The content of *a man walked* (38) is the particular condition for `exist`. -/
def AManWalked : Type := SemIndefArt Man Walk

/-- John walked. -/
def aManWalked : AManWalked := ⟨.john, ⟨⟩, ⟨⟩⟩

/-- *he whistled* (39) requires the pronoun's label of the context. -/
def heWhistled : Content Ind Type :=
  Content.boundary ((Content.pronoun 0).app ⟨∅, fun _ ↦ Whistle⟩)

/-- Given the previous utterance's witness, the pronoun's label is no longer required and the
content is that the man whistled, (42)–(44). -/
theorem heWhistled_given (w : AManWalked) (g : ℕ → Ind) :
    (heWhistled.given 0 w.x).bg.pronouns = ∅ ∧ (heWhistled.given 0 w.x).fg g = Whistle w.x :=
  ⟨rfl, rfl⟩

def heWhistledWitness (g : ℕ → Ind) : (heWhistled.given 0 aManWalked.x).fg g := ⟨⟩

end Whistling

/-! ### The book's examples

The rows of `Data/Examples/Cooper2023.json` with a `quantifier` feature are the anaphora
examples of §7.4, §7.4.1 and §8.3, each reading named by the anaphora set its pronoun picks
up. -/

/-- `quantNames` pairs each row's determiner with the quantifier relation it names. -/
def quantNames : List (String × QuantName) :=
  [("a", .exist), ("some", .existPl), ("no", .no), ("every", .every), ("most", .most),
    ("many", .many), ("few", .few), ("a few", .aFew)]

/-- `anaphoraRefs` pairs each reading's name with the anaphora set it names. -/
def anaphoraRefs : List (String × AnaphoraRef) :=
  [("refset", .refset), ("maxset", .maxset), ("compset", .compset)]

/-- A reading of a pronoun with a quantified antecedent is acceptable exactly when a witness
for the content provides a path to its anaphora set. -/
theorem anaphora_rows : ∀ row ∈ Examples.all, ∀ v ∈ row.feature? "quantifier",
    ∃ q ∈ quantNames.lookup v, ∀ r ∈ row.readings,
      ∃ ref ∈ anaphoraRefs.lookup r.1, (r.2 = .acceptable ↔ ref ∈ anaphoraAvailable q) := by
  decide

end Cooper2023
