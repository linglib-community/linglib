module

public import Linglib.Data.Examples.Grano2026
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Semantics.Degree.Boundedness
public import Linglib.Semantics.Modality.Typology
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Card

/-!
# Grano (2026): Variable-force modality in English infinitival relatives

An infinitival relative such as *a book for you to read* has a deontic modal whose force varies
between possibility (*could*) and weak necessity (*should*), and the possibility reading needs a
weakly interpreted weak quantifier: *there is a book for you to read* has both readings, *every
book for you to read* only the second (the determiner-modal generalization, §2). Grano puts
possibility and weak necessity on one deontic scale and gives the relative a silent gradable
modal, a counterpart of *should* relating a degree to the measure of a proposition (31). The
positive morpheme binds its degree argument at *should*'s threshold, giving weak necessity (33),
and existential closure strengthened above the scale's least degree gives possibility (48). By
Diesing's Mapping Hypothesis existential closure applies only inside the verb phrase, where only
weakly interpreted weak quantifiers are interpreted (§5), and Gen or an adverb of quantification
binding the degree in its restriction has the same effect (§6). Overt *should* has dedicated
possibility modals beside it, which block existential closure (§4.5).

Here a binder sets a standard on the deontic scale, the positive morpheme that of weak necessity
and the other two that of possibility. On a scale on which two propositions meeting *should*'s
threshold are jointly permissible, two cats meet a force's standard consistently with *you may
adopt at most one cat* exactly when the force is possibility, and the judgments of (8)–(10)
follow from the readings the binders at each position give.

## Main statements

* `closure_covBy`: existential closure above the least degree only just escapes triviality.
* `unselective_iff`: binding the degree in the restriction of a universal is local existential
  closure, (63)–(65).
* `consistent_iff`: two cats meet a force's standard consistently with the preamble of (8)–(10)
  exactly when the force is possibility.
* `cat_rows`, `reading_rows`: the judgments of (1), (2), (8)–(10), (61), (66) and (67).
* `not_admits_contextual`: the scale has a least degree, so Interpretive Economy excludes the
  relative standard of the positive morpheme (§7).

## Implementation notes

The paper derives the oddness of (9) from agglomeration, `□p ∧ □q` implying `□(p ∧ q)` (p. 716).
The degree semantics (33) does not deliver agglomeration, and a scale whose measure of a
conjunction is the lesser measure, which delivers it at every threshold, delivers it for
possibility too, so that (8) would be odd as well (`not_atMostOne_of_inf`). The argument needs
only that two propositions meeting the weak necessity threshold be jointly permissible
(`JointlyPermissible`), which a counting measure with a threshold above half has
(`countingModel`). Gen and the adverbs of quantification are universal binders, as in (63).

## Errata

* (72) binds the degree outside Gen with `= d`, so every relevant firefighter's measure is the
  same degree (`eq72_uniform`). Its gloss, "meets or exceeds d", is the reading the text
  describes and is strictly weaker (`eq72_gloss_weaker`). The glosses of (62) and (73) also read
  `= d` as "meets or exceeds d", a difference a universal or existential binder does not notice
  but a proportional one would; with `= d` the pairs counted are as many as the individuals
  (`ncard_pairs`).

## TODO

* The overgeneration of (73), matrix existential closure binding the subject of the relative,
  which the paper leaves open (§6.2).
* The adjacency account of (35), the comparatives (39)–(44), and predicate infinitives (fn. 22).

## References

* [grano-2026]
* [diesing-1992]
* [deal-2011]
* [kennedy-2007]
* [lassiter-2017]
-/

@[expose] public section

namespace Grano2026

open Modality Degree

/-! ### Binders of the degree argument (§4, §6) -/

section Binders
variable {α D : Type*} [LinearOrder D] [OrderBot D] {θ θ' : D}

/-- The positive morpheme binds the degree argument at *should*'s threshold, (32)–(33). -/
theorem pos_iff (μ : α → D) (x : α) :
    (∃ d, μ x = d ∧ θ ≤ d) ↔ μ x ∈ ModalForce.standard θ θ' .weakNecessity := by
  simp [ModalForce.standard]

/-- Existential closure strengthened above the least degree, (48). -/
theorem closure_iff (μ : α → D) (x : α) :
    (∃ d, μ x = d ∧ ⊥ < d) ↔ μ x ∈ ModalForce.standard θ θ' .possibility := by
  simp [ModalForce.standard]

/-- Existential closure above the least degree only just escapes triviality: the standard of
possibility covers the one every degree meets (p. 729). -/
theorem closure_covBy : (⊥ : UpperSet D) ⋖ ModalForce.standard θ θ' .possibility := by
  rw [← UpperSet.Ici_bot]
  exact UpperSet.Ici_covBy_Ioi ⊥

/-- An unselective universal binding the degree in its restriction, (62), is local existential
closure, (63)–(65). -/
theorem unselective_iff (μ : α → D) (A B : α → Prop) :
    (∀ x d, A x ∧ μ x = d ∧ ⊥ < d → B x) ↔
      ∀ x, A x ∧ μ x ∈ ModalForce.standard θ θ' .possibility → B x := by
  simp [ModalForce.standard]

/-- The restriction of (62) fixes the degree as the measure, so the pairs an unselective binder
counts are as many as the individuals, and a proportional adverb such as *for the most part*
(66) gives the possibility reading as well. -/
theorem ncard_pairs (μ : α → D) (A : α → Prop) :
    {q : α × D | A q.1 ∧ μ q.1 = q.2 ∧ ⊥ < q.2}.ncard = {x | A x ∧ ⊥ < μ x}.ncard := by
  have : {q : α × D | A q.1 ∧ μ q.1 = q.2 ∧ ⊥ < q.2} =
      (fun x ↦ (x, μ x)) '' {x | A x ∧ ⊥ < μ x} := by
    ext ⟨x, d⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨hA, rfl, hd⟩
      exact ⟨x, ⟨hA, hd⟩, rfl, rfl⟩
    · rintro ⟨y, ⟨hA, hd⟩, rfl, rfl⟩
      exact ⟨hA, rfl, hd⟩
  rw [this, Set.ncard_image_of_injective _ fun x y h ↦ (Prod.mk.inj h).1]

end Binders

/-- The binders of the silent modal's degree argument: the positive morpheme, existential
closure, and an unselective binder of a restriction. -/
inductive Binder
  | pos
  | closure
  | unselective
  deriving DecidableEq, Fintype

/-- The force a binder gives: weak necessity for the positive morpheme (`pos_iff`), possibility
for existential closure and an unselective binder (`closure_iff`, `unselective_iff`). -/
def Binder.force : Binder → ModalForce
  | .pos => .weakNecessity
  | .closure | .unselective => .possibility

/-! ### The determiner-modal generalization (§2, §5) -/

/-- Where the nominal holding the relative is interpreted: inside the verb phrase, as a weakly
interpreted weak quantifier; in the restriction of Gen or an adverb of quantification; or under
a strong quantifier or a strongly interpreted weak one, outside both. -/
inductive Position
  | insideVP
  | restriction
  | strong
  deriving DecidableEq, Fintype

/-- The binders available at a position: the positive morpheme always, existential closure only
inside the verb phrase by the Mapping Hypothesis ([diesing-1992]), and an unselective binder in
its restriction. -/
def available : Position → Finset Binder
  | .insideVP => {.pos, .closure}
  | .restriction => {.pos, .unselective}
  | .strong => {.pos}

/-- The modals of (8)–(10): overt *could* and *should*, and the silent modal of the relative. -/
inductive Modal
  | could
  | should
  | null
  deriving DecidableEq

/-- The deontic forces a modal has at a position: an overt modal its own, its degree argument
never existentially closed (`exists_possibility_scalemate`), and the silent modal those of the
binders available there. -/
def readings : Modal → Position → Finset ModalForce
  | .could, _ => English.Auxiliaries.could.forcesOf .deontic
  | .should, _ => English.Auxiliaries.should.forcesOf .deontic
  | .null, p => (available p).image Binder.force

/-- The silent modal has the possibility reading exactly where its nominal is not under a strong
quantifier. -/
theorem possibility_mem_readings_null_iff {p : Position} :
    .possibility ∈ readings .null p ↔ p ≠ .strong := by
  cases p <;> decide

/-- The positive morpheme being always available, so is the weak necessity reading (p. 739). -/
theorem weakNecessity_mem_readings_null (p : Position) : .weakNecessity ∈ readings .null p := by
  cases p <;> decide

/-- The weakest force a modal item expresses, the lexical force of an item of one force. -/
def lexicalForce (m : ModalItem) : ModalForce :=
  if .possibility ∈ m.forces then .possibility
  else if .weakNecessity ∈ m.forces then .weakNecessity else .necessity

/-- Overt *should* has a scalemate of possibility force among the English modals, a dedicated
possibility modal sharing its deontic flavour, which blocks existential closure of its degree
argument (§4.5). -/
theorem exists_possibility_scalemate :
    ∃ m ∈ English.Auxiliaries.modals.map (·.toModalItem),
      ModalItem.Scalemates lexicalForce English.Auxiliaries.should.toModalItem m ∧
        lexicalForce m = .possibility := by
  decide

/-! ### The preamble of (8)–(10) -/

section Preamble
variable {P C D : Type*} [Min P] [LinearOrder D] [OrderBot D] (μ : P → D) (adopt : C → P)

/-- The preamble *you may adopt at most one cat*: adopting two cats is impermissible. -/
def AtMostOne : Prop := ∀ a b, a ≠ b → μ (adopt a ⊓ adopt b) = ⊥

/-- Two cats meet a standard, as a continuation asserting cats that meet its relative's modal
does. -/
def TwoMeet (U : UpperSet D) : Prop := ∃ a b, a ≠ b ∧ μ (adopt a) ∈ U ∧ μ (adopt b) ∈ U

/-- Two propositions meeting the weak necessity threshold are jointly permissible. -/
def JointlyPermissible (θ : D) : Prop := ∀ p q, θ ≤ μ p → θ ≤ μ q → ⊥ < μ (p ⊓ q)

variable {μ adopt} {θ θ' : D} {f : ModalForce}

/-- On a scale where propositions meeting the weak necessity threshold are jointly permissible,
two cats meeting the standard of a force stronger than possibility contradict the preamble, as
the continuations of (9) do. -/
theorem not_atMostOne (h : JointlyPermissible μ θ) (hθθ' : θ ≤ θ') (hf : f ≠ .possibility)
    (h2 : TwoMeet μ adopt (ModalForce.standard θ θ' f)) : ¬ AtMostOne μ adopt := by
  obtain ⟨a, b, hab, ha, hb⟩ := h2
  have key : ∀ x, μ x ∈ ModalForce.standard θ θ' f → θ ≤ μ x := by
    cases f
    exacts [fun x hx ↦ hθθ'.trans hx, fun x hx ↦ hx, absurd rfl hf]
  exact fun hm ↦ (h _ _ (key _ ha) (key _ hb)).ne' (hm a b hab)

/-- On a scale whose measure of a conjunction is the lesser measure, possibility agglomerates
too, so the continuations of (8) would contradict the preamble. -/
theorem not_atMostOne_of_inf (hμ : ∀ p q, μ (p ⊓ q) = min (μ p) (μ q))
    (h2 : TwoMeet μ adopt (ModalForce.standard θ θ' .possibility)) : ¬ AtMostOne μ adopt := by
  obtain ⟨a, b, hab, ha, hb⟩ := h2
  exact fun hm ↦ (lt_min ha hb).ne' (by rw [← hμ]; exact hm a b hab)

end Preamble

/-- The permissible worlds of a model with two cats, worlds `1` and `2` adopting one of them,
`3` both and `0` neither: those where at most one cat is adopted. -/
def permissible : Finset (Fin 4) := {0, 1, 2}

/-- The degree of permission of a proposition, the number of permissible worlds where it
holds. -/
def count (p : Finset (Fin 4)) : ℕ := (p ∩ permissible).card

/-- Adopting either cat. -/
def adoptCat : Bool → Finset (Fin 4)
  | false => {1, 3}
  | true => {2, 3}

/-- With the threshold above half the permissible worlds, the counting measure makes
propositions meeting it jointly permissible, and two cats meet the standard of possibility
consistently with the preamble. -/
theorem countingModel :
    JointlyPermissible count 2 ∧ AtMostOne count adoptCat ∧
      TwoMeet count adoptCat (ModalForce.standard 2 2 .possibility) :=
  ⟨by unfold JointlyPermissible; decide, by unfold AtMostOne; decide, false, true, by decide,
    show 0 < count _ by decide, show 0 < count _ by decide⟩

/-- Two cats meet a force's standard consistently with the preamble, on a counting scale where
propositions meeting the weak necessity threshold are jointly permissible, exactly when the
force is possibility (p. 716). -/
theorem consistent_iff (f : ModalForce) :
    (∃ θ : ℕ, JointlyPermissible count θ ∧ AtMostOne count adoptCat ∧
      TwoMeet count adoptCat (ModalForce.standard θ θ f)) ↔ f = .possibility := by
  refine ⟨fun ⟨θ, hj, ha, ht⟩ ↦ by_contra fun hf ↦ not_atMostOne hj le_rfl hf ht ha, ?_⟩
  rintro rfl
  exact ⟨2, countingModel⟩

/-! ### The judgments -/

/-- The modals the rows name. -/
def modalTable : List (String × Modal) := [("could", .could), ("should", .should), ("for", .null)]

/-- The positions of a row's nominal, by the interpretation the paper gives its quantifier: weak,
strong, either for *several cats* in subject position (p. 717), or in the restriction of Gen or an
adverb of quantification. -/
def interpretationTable : List (String × Finset Position) :=
  [("weak", {.insideVP}), ("strong", {.strong}), ("either", {.insideVP, .strong}),
    ("generic", {.restriction}), ("adverb", {.restriction})]

/-- The forces the readings of a row name. -/
def forceTable : List (String × ModalForce) :=
  [("possibility", .possibility), ("weakNecessity", .weakNecessity)]

/-- A continuation of the preamble is accepted when its modal has the possibility reading on every
parse, rejected when on none, and divides speakers otherwise (`consistent_iff`). -/
def band (m : Modal) (ps : Finset Position) : Judgment.Band :=
  if ∀ p ∈ ps, .possibility ∈ readings m p then .accepted
  else if ∀ p ∈ ps, .possibility ∉ readings m p then .rejected else .divided

theorem rows_resolve :
    ∀ e ∈ Examples.all, (e.parse? "modal" modalTable).isSome ∧
      (e.parse? "interpretation" interpretationTable).isSome := by
  decide

/-- The continuations of (8)–(10) are judged as the readings of their modals predict. -/
theorem cat_rows :
    ∀ e ∈ Examples.all.filter (·.readings.isEmpty), ∀ m ∈ e.parse? "modal" modalTable,
      ∀ ps ∈ e.parse? "interpretation" interpretationTable, e.judgment.band = band m ps := by
  decide

/-- A reading of (1), (2), (61), (66) or (67) is available exactly when a binder available at
the nominal's position gives it. -/
theorem reading_rows :
    ∀ e ∈ Examples.all, ∀ m ∈ e.parse? "modal" modalTable,
      ∀ ps ∈ e.parse? "interpretation" interpretationTable, ∀ r ∈ e.readings,
        ∀ f ∈ forceTable.lookup r.1, (r.2 = .acceptable ↔ ∃ p ∈ ps, f ∈ readings m p) := by
  decide

/-! ### Interpretive Economy (§7) -/

/-- The silent modal's scale has a least degree, impermissibility (p. 728), so Interpretive
Economy admits no contextual standard on it: the relative standard of the positive morpheme is
a counterexample, as *likely* is ([kennedy-2007], [lassiter-2017]). -/
theorem not_admits_contextual {D : Type*} [LinearOrder D] [OrderBot D] :
    ¬ (Boundedness.ofOrder D).Admits .contextual :=
  Boundedness.not_admits_contextual_of_ne_open fun h ↦ by
    simpa [h, Boundedness.HasMin] using Boundedness.hasMin_ofOrder_of_orderBot (D := D)

/-! ### Errata: (72) -/

section Errata
variable {β D : Type*} [LinearOrder D] [OrderBot D]

/-- (72) as printed binds the degree outside Gen with `= d`, so every relevant firefighter's
measure is one degree. -/
theorem eq72_uniform {F : β → Prop} {ν : β → D} (h : ∃ d, ⊥ < d ∧ ∀ y, F y → ν y = d)
    {y y' : β} (hy : F y) (hy' : F y') : ν y = ν y' := by
  obtain ⟨d, -, hd⟩ := h
  rw [hd y hy, hd y' hy']

/-- The gloss of (72), "meets or exceeds d", holds of two firefighters of different positive
degrees, of which the printed formula fails. -/
theorem eq72_gloss_weaker :
    (∃ d : ℕ, ⊥ < d ∧ ∀ y : Fin 2, d ≤ ![1, 2] y) ∧
      ¬ ∃ d : ℕ, ⊥ < d ∧ ∀ y : Fin 2, ![1, 2] y = d :=
  ⟨⟨1, by decide, by decide⟩, fun ⟨_, _, hd⟩ ↦ absurd ((hd 0).trans (hd 1).symm) (by decide)⟩

end Errata

end Grano2026
