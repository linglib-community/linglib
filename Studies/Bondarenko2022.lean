module

public import Linglib.Fragments.Buryat.Complementizers
public import Linglib.Fragments.Korean.Complementizers
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes
public import Linglib.Data.Examples.Bondarenko2022
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.Readers
public import Linglib.Morphology.Word.Leipzig
public import Linglib.Semantics.Composition.Interpret
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Mereology.Exemplification
public import Linglib.Semantics.Modality.Content
public import Mathlib.Order.Hom.Lattice

/-!
# Bondarenko (2022): Anatomy of an Attitude

Individuals are ordered by parthood, situations are individuals, and a proposition is a set of
situations. The individuals carry the topology whose open sets are the sets closed under parts, so
that the persistent propositions are the closed sets. Some individuals, such as claims, rumours and
beliefs, have propositional content, which a partial function `cont` gives. An embedded clause is a
predicate of individuals built by two heads. The Cont head takes a proposition `p` to the
individuals whose content is `p`, the set `cont.preimage {p}`. The Comp head takes a predicate `P`
to the parts of the evaluation situation that exemplify `P`, in the sense of
`Mereology.Exemplifies`: the interior points of `P`, all of whose parts are in `P`, and its isolated
points, the minimal members of `P`. A Cont-CP has both heads and a Sit-CP has Comp alone, so a
Sit-CP with proposition `p` holds of the parts of the evaluation situation that exemplify `p`.

Content is fixed by equality. Clauses with different propositions then hold of disjoint sets of
individuals, so that two clauses do not stack on one noun [moulton-2009] or conjoin, and a clause is
not monotone in its proposition. A disjunction of clauses holds of the individuals whose content is
one of the two propositions, none of which has the disjunction of the propositions as its content
unless one proposition entails the other [bassi-bondarenko-2021]. Where the facts of a world
correspond one to one to its true propositions, exactly one fact has a given true proposition as its
content [elliott-2020-embedding]. On the rival semantics, on which the content entails the
proposition, a clause is a homomorphism of intersections `subsetClause cont`: stacked clauses have
the meaning of the conjunction, a clause is closed under weakening of its proposition, and a fact is
not unique, since the content of the fact with a stronger true proposition also entails the
clause's.

A Sit-CP holds only where its proposition is true, if the proposition is persistent. The clauses
differ in how much of the proposition they depend on, in the sense of `Set.DependsOn`. Whether a
part of the evaluation situation exemplifies a proposition depends on the proposition only among the
parts of that situation, a clause of the subset semantics depends on it only within the content of
the individual, and a clause of the equality semantics depends on the whole of it. So a Sit-CP is
referentially transparent: descriptions that pick out one individual in the evaluation situation,
and keep their reference in its parts, may be substituted for one another. Something with a proper
part in a set and a part outside it does not exemplify the set, so a clause with Comp does not hold
of a larger individual that contains what the clause describes. Where the situations of a verb form
an antichain and have proper parts, the proposition that one of them is part of a situation is
exemplified by those situations alone, by `IsAntichain.exemplifies_upperClosure_iff`, so a Sit-CP
holds of the situations of its verb.

Content nouns denote contentful individuals that are not situations, and situation nouns denote
situations without content. A predicate of truth is defined of the contentful individuals and a
predicate of occurrence of the situations, and the rows of the two diagnostics are acceptable
exactly where the extension of the noun's sort lies in the domain of the predicate in every
model.

With a verb, a clause modifies the verb's situation argument by Predicate Modification, or it is
nominalized and is the argument of a head that introduces a participant. The trees are
interpreted by Functional Application and Predicate Modification. A clause that is not
nominalized has no derivation as the argument of such a head, and a proposition without Comp has
none with a noun. A Sit-CP that modifies a verb has a derivation, and its meaning is the
situations of the verb that exemplify the clause's proposition. In a model with a thinking and
an eating there are none, while the thinking exemplifies the predicate of having the content
that there is eating.

In Buryat and Korean the Cont head has an exponent, and Comp has one allomorph next to a nominal
projection and another next to a verb. The clause-typing morphemes that the rows mark on the
Buryat complements of *hanaxa* 'think' and on the Korean complements of nouns are those the
exponents give for the heads of the clause and for what the clause combines with.

## Implementation notes

* Situations are individuals, so one type carries both and a predicate of situations is a
  predicate of individuals. In the trees the sort `s` types only the proposition that Cont and
  Comp take, which the thesis supplies by intensional application. Comp is entered at both types
  with one meaning, where the thesis applies it to a proposition because a set of situations is a
  set of individuals.
* A nominalized clause denotes the individual that a choice function `the` picks from the
  clause's predicate, where the thesis has a definite or an indefinite determiner.
* The thesis holds that no situation exemplifies two propositions that both characterize a
  situation by what exists within it. This is shown in a model. In general what exemplifies two
  sets exemplifies their intersection, `Mereology.Exemplifies.inter`.
* Buryat *hanaxa* quantifies over doxastic alternatives in both of its frames, which differ in
  opacity and factivity. Its nominalized reading, 'remember', is factive through the
  presupposition that the event its complement describes started before the thinking, which the
  fragment records on the nominalized frame.

## TODO

* The non-Boolean conjunction of clauses, and the clauses of Russian, whose Cont head has no
  exponent.
* The verbs of occurrence, whose situation argument a Sit-CP modifies.

## References

* [bondarenko-2022]
* [kratzer-2006]
* [kratzer-2012]
* [moulton-2009]
* [moulton-2015]
* [bassi-bondarenko-2021]
* [elliott-2020-embedding]
-/

@[expose] public section

namespace Bondarenko2022

open Mereology Buryat

/-! ### Equality and subset content -/

section Content

open Modality ModalLogic

variable {X W : Type*} {cont : X →. Set W} {x : X} {p q : Set W} {fact : Set X} {w : W}

/-- On the equality semantics, clauses with different propositions hold of disjoint sets of
individuals, so that two clauses do not stack on one noun or conjoin. -/
theorem pairwise_disjoint_preimage_singleton (cont : X →. Set W) :
    Pairwise (Function.onFun Disjoint fun p : Set W ↦ cont.preimage {p}) :=
  fun _ _ h ↦ cont.disjoint_preimage_of_disjoint (Set.disjoint_singleton.2 h)

-- ch. 2 (189)
theorem not_monotone_preimage_singleton :
    ¬ Monotone fun p : Set Bool ↦ (PFun.pure {true} : Unit →. Set Bool).preimage {p} := fun h ↦ by
  obtain ⟨_, rfl, hq⟩ := @h {true} Set.univ (Set.subset_univ _) () ⟨_, rfl, Part.mem_some _⟩
  exact Bool.false_ne_true (Part.mem_some_iff.1 hq ▸ Set.mem_univ false : false ∈ ({true} : Set _))

/-- On the subset semantics of ch. 1 (10) a clause holds of the individuals whose content entails
its proposition. It preserves intersections, so that stacked clauses mean the conjunction, ch. 1
(11), and it is monotone, the closure under entailment of ch. 2 (188). -/
def subsetClause (cont : X →. Set W) : InfHom (Set W) (Set X) where
  toFun p := cont.preimage (Set.Iic p)
  map_inf' p q := by
    rw [← PFun.preimage_inter, Set.Iic_inter_Iic]

@[simp]
theorem subsetClause_apply : subsetClause cont p = cont.preimage (Set.Iic p) := rfl

-- ch. 1 (14)
theorem mem_subsetClause_iff :
    x ∈ subsetClause cont p ↔ x ∈ cont.Dom ∧ □[compatible cont] (· ∈ p) x :=
  mem_preimage_Iic_iff

-- ch. 3 (19), (20); (24), (25) of [bassi-bondarenko-2021]
theorem disjoint_preimage_union_preimage_singleton_union (cont : X →. Set W) (hpq : ¬ p ⊆ q)
    (hqp : ¬ q ⊆ p) :
    Disjoint (cont.preimage {p} ∪ cont.preimage {q}) (cont.preimage {p ∪ q}) := by
  rw [← PFun.preimage_union]
  refine cont.disjoint_preimage_of_disjoint (Set.disjoint_singleton_right.2 ?_)
  rintro (h | h)
  exacts [hqp (h ▸ Set.subset_union_right), hpq (h ▸ Set.subset_union_left)]

-- ch. 2 (179), (180); (282), (283) of [elliott-2020-embedding]
theorem existsUnique_fact_preimage_singleton
    (hinj : ∀ x ∈ fact, ∀ y ∈ fact, ∀ p, p ∈ cont x → p ∈ cont y → x = y)
    (hsurj : ∀ p, w ∈ p → ∃ x ∈ fact, p ∈ cont x) (hp : w ∈ p) :
    ∃! x, x ∈ fact ∧ x ∈ cont.preimage {p} := by
  obtain ⟨x, hx, hpx⟩ := hsurj p hp
  refine ⟨x, ⟨hx, p, rfl, hpx⟩, ?_⟩
  rintro y ⟨hy, _, rfl, hpy⟩
  exact hinj y hy x hx _ hpy hpx

-- ch. 2 (181), (182); (284) of [elliott-2020-embedding]
theorem not_existsUnique_fact_subsetClause (hsurj : ∀ p, w ∈ p → ∃ x ∈ fact, p ∈ cont x)
    (hq : w ∈ q) (hqp : q ⊂ p) : ¬ ∃! x, x ∈ fact ∧ x ∈ subsetClause cont p := by
  rintro ⟨_, -, h⟩
  obtain ⟨y, hy, hpy⟩ := hsurj p (hqp.subset hq)
  obtain ⟨z, hz, hqz⟩ := hsurj q hq
  obtain rfl := (h y ⟨hy, p, Set.mem_Iic.2 le_rfl, hpy⟩).trans
    (h z ⟨hz, q, Set.mem_Iic.2 hqp.subset, hqz⟩).symm
  exact hqp.ne (Part.mem_unique hqz hpy)

-- ch. 2 (163)
theorem dependsOn_mem_cont_iff (hx : x ∈ cont.Dom) {s : Set W} :
    Set.DependsOn (· ∈ cont x) s ↔ s = Set.univ := by
  obtain ⟨c, hc⟩ := Part.dom_iff_mem.1 hx
  refine ⟨fun h ↦ Set.eq_univ_of_forall fun w ↦ by_contra fun hws ↦ ?_,
    fun h ↦ h ▸ Set.dependsOn_univ _⟩
  have h₁ : s ∩ c = c := Part.mem_unique ((iff_of_eq (h c)).2 hc) hc
  have h₂ : insert w c = c := Part.mem_unique
    ((iff_of_eq (h (insert w c))).1 (by rwa [Set.inter_insert_of_notMem hws, h₁])) hc
  exact hws (Set.inter_eq_right.1 h₁ (h₂ ▸ Set.mem_insert w c))

theorem dependsOn_mem_subsetClause_iff {s : Set W} :
    Set.DependsOn (x ∈ subsetClause cont ·) s ↔ ∀ c ∈ cont x, c ⊆ s := by
  refine ⟨fun h c hc ↦ ?_, fun h p ↦ propext ⟨?_, ?_⟩⟩
  · obtain ⟨d, hd, hdc⟩ := (h Set.univ).mpr ⟨c, Set.subset_univ c, hc⟩
    exact Part.mem_unique hdc hc ▸ (Set.mem_Iic.1 hd).trans Set.inter_subset_left
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c, (Set.mem_Iic.1 hc).trans Set.inter_subset_right, hcx⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c, Set.subset_inter (h c hcx) hc, hcx⟩

end Content

/-! ### Clauses with Comp -/

section Comp

variable {E : Type*} [TopologicalSpace E] [PartialOrder E] [Topology.IsLowerSet E] {p : Set E}
  {s x : E}

-- ch. 2, on (159)
theorem mem_of_exemplifies_of_le (hp : IsClosed p) (hx : Exemplifies p x) (hxs : x ≤ s) : s ∈ p :=
  Topology.IsLowerSet.isClosed_iff_isUpper.1 hp hxs hx.mem

-- ch. 2 (164)
theorem dependsOn_exemplifies_of_le (hx : x ≤ s) :
    Set.DependsOn (Exemplifies · x) (Set.Iic s) :=
  (dependsOn_exemplifies_Iic x).mono (Set.Iic_subset_Iic.2 hx)

/-- A Sit-CP is referentially transparent: descriptions `a` and `b` that pick out one individual
in the evaluation situation `s`, and keep their reference in the parts of `s`, may be substituted
for one another in the clause's proposition without changing which parts of `s` exemplify it. -/
theorem exemplifies_substitution {D : Type*} {a b : E → D} {R : D → Set E}
    (ha : ∀ y ≤ s, a y = a s) (hb : ∀ y ≤ s, b y = b s) (hab : a s = b s) (hx : x ≤ s) :
    Exemplifies {y | y ∈ R (a y)} x ↔ Exemplifies {y | y ∈ R (b y)} x :=
  iff_of_eq <| (dependsOn_exemplifies_Iic x).congr <| Set.ext fun y ↦ and_congr_right fun hy ↦ by
    have hys := (Set.mem_Iic.1 hy).trans hx
    simp only [Set.mem_ofPred_eq, ha y hys, hb y hys, hab]

-- ch. 2 (120)–(122)
theorem substitution_valid_iff_situation :
    ∀ r ∈ Examples.all, ∀ n ∈ Examples.nounSort r, ∀ i ∈ Examples.inference r,
      (i = .valid ↔ n = .situation) := by
  decide +kernel

end Comp

/-! ### Nominal sorts -/

/-- The two sorts of clause-taking noun, content nouns (*idea*, *claim*, *rumor*) and situation
nouns (*situation*, *event*, *case*). -/
inductive NominalSort where
  | content
  | situation
  deriving DecidableEq, Fintype, Repr

/-- The individuals that a noun of each sort may denote, where `S` is the set of situations:
contentful individuals that are not situations, and situations without content. -/
def NominalSort.extension {E W : Type*} (S : Set E) (cont : E →. Set W) : NominalSort → Set E
  | .content => cont.Dom \ S
  | .situation => S \ cont.Dom

namespace NominalSort

variable {n : NominalSort}

theorem forall_extension_subset_dom_iff :
    (∀ (E W : Type) (S : Set E) (cont : E →. Set W), n.extension S cont ⊆ cont.Dom) ↔
      n = .content := by
  refine ⟨fun h ↦ ?_, by rintro rfl _ _ _ _; exact Set.sdiff_subset⟩
  cases n
  · rfl
  · exact (h Unit Unit Set.univ (fun _ ↦ Part.none) (a := ()) ⟨trivial, id⟩).elim

theorem forall_extension_subset_iff :
    (∀ (E W : Type) (S : Set E) (cont : E →. Set W), n.extension S cont ⊆ S) ↔
      n = .situation := by
  refine ⟨fun h ↦ ?_, by rintro rfl _ _ _ _; exact Set.sdiff_subset⟩
  cases n
  · exact (h Unit Unit ∅ (fun _ ↦ Part.some ∅) (a := ()) ⟨trivial, id⟩).elim
  · rfl

end NominalSort

/-- The sort of noun a row names. -/
def Examples.NounSort.toNominalSort : Examples.NounSort → NominalSort
  | .content => .content
  | .situation => .situation

-- ch. 2 (105)–(107)
theorem truthPredicates_iff_extension_subset_dom :
    ∀ r ∈ Examples.all, Examples.diagnostic r = some .truthPredicates →
      ∀ n ∈ Examples.nounSort r,
        (r.judgment = .acceptable ↔ ∀ (E W : Type) (S : Set E) (cont : E →. Set W),
          n.toNominalSort.extension S cont ⊆ cont.Dom) := by
  simp only [NominalSort.forall_extension_subset_dom_iff]
  decide +kernel

-- ch. 2 (108)–(112)
theorem occurrencePredicates_iff_extension_subset :
    ∀ r ∈ Examples.all, Examples.diagnostic r ∈ [some .occurrencePredicates, some .notice] →
      ∀ n ∈ Examples.nounSort r,
        (r.judgment = .acceptable ↔ ∀ (E W : Type) (S : Set E) (cont : E →. Set W),
          n.toNominalSort.extension S cont ⊆ S) := by
  simp only [NominalSort.forall_extension_subset_iff]
  decide +kernel

/-! ### Clauses with nouns and verbs -/

section Composition

open Interpreter PhraseStructure ManySorted

/-- The heads of §4.4 that introduce a participant. -/
inductive ThetaHead where
  | causer
  | theme
  | aboutAttitude
  deriving DecidableEq, Repr

/-- The words of the trees, by semantic type. -/
inductive Item : Ty Base → Type
  /-- The proposition of the embedded clause below its left periphery. -/
  | tp : Item (.intens .t)
  /-- The Cont head, ch. 2 (150). -/
  | cont : Item (.intens .t ⇒ .et)
  /-- The Comp head, ch. 2 (151). -/
  | comp : Item (.et ⇒ .et)
  /-- The Comp head with a proposition as its sister. -/
  | compProp : Item (.intens .t ⇒ .et)
  /-- A noun. -/
  | noun : Item .et
  /-- A verb, a predicate of situations. -/
  | verb : Item .et
  /-- A head that introduces a participant, ch. 4 (5). -/
  | theta (θ : ThetaHead) : Item (.et ⇒ .e ⇒ .et)
  /-- The determiner of a nominalized clause. -/
  | the : Item (.et ⇒ .e)

/-- Functional Application and Predicate Modification. -/
abbrev grammar : Language (Ty Base) := application.sum predicateModification

variable {E : Type} [TopologicalSpace E] [PartialOrder E] (cont : E →. Set E) (s₀ : E)
  (p : Set E)
  (noun verb : E → Prop) (role : ThetaHead → E → E) (the : (E → Prop) → E)

/-- The denotations of the words at the evaluation situation `s₀`: Cont holds of a proposition
and an individual whose content it is, Comp of a predicate and a part of `s₀` that exemplifies it,
and a head that introduces a participant of a predicate of situations, an individual and a
situation of the predicate in which the individual has the head's role. -/
def Item.val : {a : Ty Base} → Item a → a.Dom (Base.Dom E E)
  | _, .tp => (· ∈ p)
  | _, .cont => fun q x ↦ x ∈ cont.preimage {{w | q w}}
  | _, .comp => fun P x ↦ x ≤ s₀ ∧ Exemplifies {y | P y} x
  | _, .compProp => fun q x ↦ x ≤ s₀ ∧ Exemplifies {y | q y} x
  | _, .noun => noun
  | _, .verb => verb
  | _, .theta θ => fun P y e ↦ P e ∧ role θ e = y
  | _, .the => the

/-- The leaf of a word. -/
def leaf {a : Ty Base} (i : Item a) : Tree Unit (Σ a, Item a) := .leaf ⟨a, i⟩

/-- A Cont-CP, ch. 2 (152b): Comp above Cont above the proposition. -/
def contCP : Tree Unit (Σ a, Item a) := .bin (leaf .comp) (.bin (leaf .cont) (leaf .tp))

/-- A Sit-CP, ch. 2 (155a): Comp above the proposition. -/
def sitCP : Tree Unit (Σ a, Item a) := .bin (leaf .compProp) (leaf .tp)

/-- A noun with the proposition as its sister. -/
def nounTP : Tree Unit (Σ a, Item a) := .bin (leaf .noun) (leaf .tp)

/-- A clause as a modifier of a verb, ch. 4 (12). -/
def modifier (cp : Tree Unit (Σ a, Item a)) : Tree Unit (Σ a, Item a) := .bin cp (leaf .verb)

/-- A nominalized clause as the argument of a head that introduces a participant, ch. 4 (11). -/
def argument (θ : ThetaHead) (cp : Tree Unit (Σ a, Item a)) : Tree Unit (Σ a, Item a) :=
  .bin (.bin (leaf .verb) (leaf (.theta θ))) (.bin (leaf .the) cp)

/-- A clause that is not nominalized in the position of such an argument. -/
def bareArgument (θ : ThetaHead) (cp : Tree Unit (Σ a, Item a)) : Tree Unit (Σ a, Item a) :=
  .bin (.bin (leaf .verb) (leaf (.theta θ))) cp

/-- The meanings of a tree at the evaluation situation `s₀`. -/
def meanings (t : Tree Unit (Σ a, Item a)) :
    List (Σ a : Ty Base, (ℕ → E) → a.Dom (Base.Dom E E)) :=
  t.interpret grammar (Base.Dom E E) (fun _ ↦ .e)
    (fun i _ ↦ Item.val cont s₀ p noun verb role the i) fun w ↦ [w]

-- ch. 2 (152b)
theorem meanings_contCP :
    meanings cont s₀ p noun verb role the contCP =
      [⟨.et, fun _ x ↦ x ≤ s₀ ∧ Exemplifies (cont.preimage {p}) x⟩] :=
  rfl

-- ch. 2 (155a)
theorem meanings_sitCP :
    meanings cont s₀ p noun verb role the sitCP = [⟨.et, fun _ x ↦ x ≤ s₀ ∧ Exemplifies p x⟩] :=
  rfl

-- ch. 2 (165)–(168)
theorem derive_nounTP : nounTP.derive grammar (fun _ ↦ .e) (W := Item) (fun w ↦ [w]) = [] :=
  rfl

-- ch. 4 (24)
theorem meanings_modifier_contCP :
    meanings cont s₀ p noun verb role the (modifier contCP) =
      [⟨.et, fun _ x ↦ (x ≤ s₀ ∧ Exemplifies (cont.preimage {p}) x) ∧ verb x⟩] :=
  rfl

-- ch. 4 (26)
theorem meanings_modifier_sitCP :
    meanings cont s₀ p noun verb role the (modifier sitCP) =
      [⟨.et, fun _ x ↦ (x ≤ s₀ ∧ Exemplifies p x) ∧ verb x⟩] :=
  rfl

-- ch. 4 (20)
theorem meanings_argument_contCP (θ : ThetaHead) :
    meanings cont s₀ p noun verb role the (argument θ contCP) =
      [⟨.et, fun _ e ↦ verb e ∧
        role θ e = the fun x ↦ x ≤ s₀ ∧ Exemplifies (cont.preimage {p}) x⟩] := by
  cases θ <;> rfl

-- ch. 4 (21)
theorem meanings_argument_sitCP (θ : ThetaHead) :
    meanings cont s₀ p noun verb role the (argument θ sitCP) =
      [⟨.et, fun _ e ↦ verb e ∧ role θ e = the fun x ↦ x ≤ s₀ ∧ Exemplifies p x⟩] := by
  cases θ <;> rfl

/-- A clause that is not nominalized saturates no head that introduces a participant: the head
with its verb wants an individual, and no rule applies to it and a predicate of individuals. -/
theorem derive_bareArgument (θ : ThetaHead) :
    (bareArgument θ contCP).derive grammar (fun _ ↦ .e) (W := Item) (fun w ↦ [w]) = [] ∧
      (bareArgument θ sitCP).derive grammar (fun _ ↦ .e) (W := Item) (fun w ↦ [w]) = [] := by
  cases θ <;> exact ⟨rfl, rfl⟩

end Composition

/-! ### A model of the two paths

The situations are the sets of two events, a thinking `0` and an eating `1`, ordered by
inclusion, and the thinking has the content that there is eating. -/

section Model

attribute [local instance] Topology.lowerSet

/-- The situations in which there is thinking. -/
def thinking : Set (Finset (Fin 2)) := {x | 0 ∈ x}

/-- The situations in which there is eating. -/
def eating : Set (Finset (Fin 2)) := {x | 1 ∈ x}

instance : DecidablePred (· ∈ thinking) := fun x ↦ inferInstanceAs (Decidable (0 ∈ x))

instance : DecidablePred (· ∈ eating) := fun x ↦ inferInstanceAs (Decidable (1 ∈ x))

/-- The content function: the thinking has the content that there is eating, and nothing else
has content. -/
def thought : Finset (Fin 2) →. Set (Finset (Fin 2)) := PFun.res (fun _ ↦ eating) {{0}}

/-- No situation of the model exemplifies both the proposition that there is thinking and the
proposition that there is eating, so a Sit-CP that modifies *think* holds of nothing. -/
theorem not_exemplifies_thinking_and_eating :
    ∀ x, ¬ (Exemplifies eating x ∧ Exemplifies thinking x) := by
  decide

-- ch. 4 (24), (25)
theorem exemplifies_thought_and_thinking :
    Exemplifies (thought.preimage {eating}) {0} ∧ Exemplifies thinking {0} := by
  have h : thought.preimage {eating} = {{0}} := by ext x; simp [thought, PFun.mem_res]
  exact ⟨h ▸ (Set.subsingleton_singleton.isAntichain _).exemplifies_iff.2 rfl, by decide⟩

-- ch. 2 (198)–(201)
theorem not_exemplifies_eating_sup : {0, 1} ∈ eating ∧ ¬ Exemplifies eating {0, 1} := by
  decide

end Model

/-! ### Exponents of Cont and Comp -/

/-- The exponents of the heads of an embedded clause, ch. 4 (33) and (46): of Cont, and of Comp
next to a nominal projection and next to a verb. -/
structure Exponence where
  /-- The exponent of Cont. -/
  cont : Complementizer
  /-- The allomorph of Comp next to each licensing category. -/
  comp : Complementizer.Licenser ↪ Complementizer

/-- Ch. 4 (33): in Buryat *gɘ* 'say' expones Cont, and Comp is the participle *-Aːša* next to a
nominal projection and the converb *-žA* next to a verb. -/
def buryat : Exponence where
  cont := ge
  comp := ⟨fun | .nominal => aasha | .verbal => zha, by decide⟩

/-- Ch. 4 (46): in Korean the declarative *-ta* expones Cont, and Comp is the adnominal *-nun*
next to a nominal projection and *-ko* next to a verb. -/
def korean : Exponence where
  cont := Korean.Complementizers.ta
  comp := ⟨fun | .nominal => Korean.Complementizers.nun | .verbal => Korean.Complementizers.ko,
    by decide⟩

/-- The clause-typing morphemes of a clause with the given heads next to the licensing category
`l`, in the order of the heads. -/
def Exponence.typers (v : Exponence) :
    Examples.ClauseType → Complementizer.Licenser → List Complementizer
  | .contCP, l => [v.cont, v.comp l]
  | .sitCP, l => [v.comp l]

-- the allomorphs of Comp are the fragments' entries licensed by each category
theorem licenser_comp :
    ∀ v ∈ [buryat, korean], ∀ l, (v.comp l).licenser = some l := by
  decide

-- the exponents are the fragments' inventories
theorem complementizers_eq :
    complementizers = [buryat.cont, buryat.comp .nominal, buryat.comp .verbal] ∧
      Korean.Complementizers.complementizers =
        [korean.cont, korean.comp .nominal, korean.comp .verbal] :=
  ⟨rfl, rfl⟩

/-- The fragment entry of a clause-typing morpheme that a row names. -/
def Examples.Lexeme.entry : Examples.Lexeme → Complementizer
  | .ge => Buryat.ge
  | .aasha => Buryat.aasha
  | .zha => Buryat.zha
  | .ta => Korean.Complementizers.ta
  | .nun => Korean.Complementizers.nun

/-- The clause-typing morphemes that a row marks on its embedded clause, in order. -/
def typers (e : Datum) : List Complementizer :=
  e.spans.filterMap fun s ↦ (Examples.lexeme? s).map (·.entry)

/-- The exponents of a row's language. -/
def exponence? (e : Datum) : Option Exponence :=
  e.byLanguage [(.russiaBuriat, buryat), (.korean, korean)]

/-- The heads of a row's embedded clause: as the row gives them, and otherwise with Cont where
the clause combines with a content noun and without it where it combines with a situation
noun. -/
def clause? (e : Datum) : Option Examples.ClauseType :=
  Examples.clauseType e <|>
    (Examples.nounSort e).map fun | .content => .contCP | .situation => .sitCP

/-- What a row's embedded clause combines with: a nominal projection if the clause modifies a
noun or its marked word bears a case, and a verb otherwise. -/
def licenser (e : Datum) : Complementizer.Licenser :=
  if (Examples.nounSort e).isSome ∨ ∃ s ∈ e.spans, ∃ w ∈ s.words e, (w.features .case).isSome
  then .nominal else .verbal

-- ch. 4 (30)–(32), Tables 4.2 and 4.3; ch. 2 (106)–(112), (121), (122)
theorem typers_eq :
    ∀ r ∈ Examples.all, ∀ v ∈ exponence? r, ∀ c ∈ clause? r,
      typers r = v.typers c (licenser r) := by
  decide +kernel

example : Datum.ReadCount (fun r ↦ (exponence? r).bind fun _ ↦ clause? r) Examples.all 13 := by
  decide +kernel

-- §4.4.3
theorem hanaxa_typers :
    (ArgumentFrame.finiteClause.Takes (buryat.comp .verbal) ∧
        ¬ ArgumentFrame.finiteClause.Takes (buryat.comp .nominal)) ∧
      (nominalizedFrame.Takes (buryat.comp .nominal) ∧
        ¬ nominalizedFrame.Takes (buryat.comp .verbal)) ∧
      hanaxa.typers complementizers = [aasha, zha] := by
  decide

/-- *hanaxa* has one attitude in both of its frames, and is veridical with a nominalized
complement, 'remember', and not with a bare CP, 'think': the frames differ in factivity alone
(§4.4.3). -/
theorem hanaxa_isVeridical_nominalized :
    hanaxa.attitudeOn ArgumentFrame.finiteClause = hanaxa.attitudeOn nominalizedFrame ∧
      (∀ a ∈ hanaxa.attitudeOn nominalizedFrame,
        a.IsVeridical (hanaxa.factivityOn nominalizedFrame)) ∧
      ∀ a ∈ hanaxa.attitudeOn ArgumentFrame.finiteClause,
        ¬ a.IsVeridical (hanaxa.factivityOn ArgumentFrame.finiteClause) := by
  decide

end Bondarenko2022
