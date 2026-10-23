module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Linglib.Semantics.Exhaustification.DomainAlternatives
public import Linglib.Semantics.Exhaustification.PreExhaustified
public import Linglib.Data.Examples.AlonsoOvalleMoghiseh2025a

/-!
# Alonso-Ovalle & Moghiseh (2025): existential free choice items

Farsi *yek-i* DPs are existential free choice items: plain existentials in downward
entailing contexts, free choice under deontic modals and modal variation under epistemic
ones (§2), but, unlike *irgendein* or *vreun*, grammatical and non-modal when unembedded,
where they convey uniqueness (§2.4). In [chierchia-2013]'s framework the DP introduces the
scalar alternative *at least two* and the pre-exhaustified domain alternatives
(`Excluder.preExhaustify`, by innocent exclusion as in (56f)). Under a modal, negating the
domain alternatives gives free choice (`deontic_tolerant`, the general
`freeChoice_of_proper`), but negating the scalar alternative too is too strong
under ◇ and too weak under □ (`deontic_tolerant_box`); in a conditional antecedent
exhaustification is vacuous (`conditional_vacuous`). Unembedded, the contradiction-tolerant
operator yields ⊥ (`root_tolerant`, (92)); modal insertion (85)–(87) rescues *irgendein*
(`modal_insertion`), while *yek-i* prunes the domain alternatives, and partial scalar
exhaustification gives uniqueness (`root_scalar`) where partial domain exhaustification
returns the scalar alternative itself, which the Economy Principle (94) blocks
(`root_domain`). Fox's contradiction-free operator does not deliver (103): the paper's (101)
omits the maximal exclusion `{¬(b₁∧¬b₂), ¬(b₂∧¬b₁)}`, so no alternative is innocently
excludable and exhaustification is vacuous (`root_innocent`).

The embedded uniqueness of §5 needs split exhaustification, scalar below the modal and domain
above it (113): `split_diamond` and `split_box` derive (119)–(120), leaving ◇(b₁∧b₂) open,
while the single-operator LFs (143)–(146) are too weak or too strong (`single_below`,
`single_above`, `two_innocent`). Below *if*, scalar exhaustification weakens the sentence
(`conditional_weakening`), so Maximize Strength (132) prunes it. The scenario verdicts of
§§2–5 are checked in `rows_agree` on five-book models, and Table 2's typology in
`table2_rows`.

## References

* [alonso-ovalle-moghiseh-2025a]
* [chierchia-2013]
* [kratzer-shimoyama-2002]
* [alonso-ovalle-menendez-benito-2010]
* [falaus-2014]
* [fox-2007]
* [bar-lev-fox-2020]
* [aloni-port-2015]
-/

@[expose] public section

namespace AlonsoOvalleMoghiseh2025a

open Exhaustification ModalLogic Finset
open scoped SetRel

/-! ### The two-book model (§3) -/

/-- A world records which of the two books Forood bought. -/
abbrev Buy := Finset (Fin 2)

/-- Book `i` is bought at `v`. -/
def buys (v : Buy) (i : Fin 2) : Prop := i ∈ v

instance (v : Buy) : DecidablePred (buys v) := fun i => inferInstanceAs (Decidable (i ∈ v))

/-- The proposition denoted by a decidable predicate on worlds. -/
abbrev prop {W : Type*} [Fintype W] (p : W → Prop) [DecidablePred p] : Finset W :=
  univ.filter p

/-- The assertion (56c) is that Forood bought a book. -/
def assertion : Finset Buy := prop (claim buys univ)

/-- The scalar alternative (54) is that Forood bought at least two books. -/
def scalar : Finset Buy := prop (2 ≤ ·.card)

/-- Exactly one book is bought. -/
def exactlyOne : Finset Buy := prop (·.card = 1)

/-- The domain alternatives (55) restrict the claim to each proper subdomain. -/
def domainAlts : Finset (Finset Buy) :=
  (subdomainAlternatives .proper univ).image fun S => prop (claim buys S)

/-- The pre-exhaustified domain alternatives are *only b₁* and *only b₂* (56f). -/
theorem preExhaustify_domainAlts :
    innocent.preExhaustify domainAlts = {prop (· = {0}), prop (· = {1})} := by decide

/-! ### Modal contexts (§3, §5) -/

/-- A nonempty modal base collects the permitted, or epistemically possible, buy-worlds. -/
abbrev Base := {A : Finset Buy // A.Nonempty}

instance : Fintype Base := Subtype.fintype fun A : Finset Buy => A.Nonempty
instance : DecidableEq Base := Subtype.instDecidableEq

/-- A modal world pairs a modal base with the actual buy-world; accessibility keeps the base
and moves to one of its worlds, so the frame is serial. -/
abbrev Modal := Base × Buy

instance : DecidableEq Modal := instDecidableEqProd
instance : Fintype Modal := instFintypeProd Base Buy

/-- An accessible world has the same modal base and lies in it. -/
def acc : SetRel Modal Modal := {p | p.2.1 = p.1.1 ∧ p.2.2 ∈ p.1.1.1}

instance (m m' : Modal) : Decidable (m ~[acc] m') :=
  inferInstanceAs (Decidable (m'.1 = m.1 ∧ m'.2 ∈ m.1.1))

/-- The modal world with base `A` and actual buy-world `v`. -/
def world (A : Finset Buy) (v : Buy) (h : A.Nonempty := by decide) : Modal := (⟨A, h⟩, v)

/-- Book `i` is bought at the modal world `m`. -/
def buysM (m : Modal) (i : Fin 2) : Prop := i ∈ m.2

instance (m : Modal) : DecidablePred (buysM m) := fun i => inferInstanceAs (Decidable (i ∈ m.2))

/-- A proposition about the buy-world, evaluated at a modal world. -/
def at' (p : Finset Buy) : Finset Modal := prop (·.2 ∈ p)

/-- ◇ as an operation on propositions. -/
def dia (p : Finset Modal) : Finset Modal := prop (◇[acc] (· ∈ p))

/-- □ as an operation on propositions. -/
def box' (p : Finset Modal) : Finset Modal := prop (□[acc] (· ∈ p))

/-- The alternatives of a modalized clause apply the modal pointwise (fn. 15). -/
def lift (M : Finset Modal → Finset Modal) (ALT : Finset (Finset Buy)) :
    Finset (Finset Modal) :=
  ALT.image (M ∘ at')

/-- Free choice holds at a modal world when each book is permitted. -/
def fc (m : Modal) : Prop := FreeChoice acc m univ buysM

instance : DecidablePred fc := fun m => inferInstanceAs (Decidable (FreeChoice acc m univ buysM))

/-- Exhaustifying ◇(b₁∨b₂) over all alternatives at once gives free choice together with the
unattested ¬◇(b₁∧b₂) (61). -/
theorem deontic_tolerant :
    tolerant.exh ({dia (at' scalar)} ∪ innocent.preExhaustify (lift dia domainAlts))
        (dia (at' assertion)) = prop fc \ dia (at' scalar) := by decide +kernel

/-- Under □ the same exhaustification is too weak — it holds where Forood may buy more than one book
(67)–(68). -/
theorem deontic_tolerant_box :
    world {{0}, {1}, {0, 1}} {0} ∈
      tolerant.exh ({box' (at' scalar)} ∪ innocent.preExhaustify (lift box' domainAlts))
        (box' (at' assertion)) := by decide +kernel

/-- Modal insertion rescues an unembedded *irgendein* — the result is contingent and conveys
ignorance about each book (85)–(87). -/
theorem modal_insertion :
    let φ := tolerant.exh ({box' (at' scalar)} ∪ innocent.preExhaustify (lift box' domainAlts))
      (box' (at' assertion))
    φ.Nonempty ∧ φ ⊆ dia (prop (buysM · 0)) ∩ dia (prop (buysM · 1)) ∩
      dia (prop (¬ buysM · 0)) ∩ dia (prop (¬ buysM · 1)) := by decide +kernel

/-! ### Unembedded *yek-i* DPs (§4) -/

/-- Unembedded, the contradiction-tolerant operator yields ⊥ (92). -/
theorem root_tolerant :
    tolerant.exh ({scalar} ∪ innocent.preExhaustify domainAlts) assertion = ∅ := by decide

/-- Partial scalar exhaustification gives uniqueness (93a). -/
theorem root_scalar : innocent.exh {scalar} assertion = exactlyOne := by decide

/-- Partial domain exhaustification returns the scalar alternative itself, so the Exhaustification
Economy Principle blocks it (93b)–(94). -/
theorem root_domain : innocent.exh (innocent.preExhaustify domainAlts) assertion = scalar := by
  decide

/-- No alternative is innocently excludable, so the root operator is vacuous and the derivation of
uniqueness in (101)–(103) fails. -/
theorem root_innocent :
    innocent.exh ({scalar} ∪ innocent.preExhaustify domainAlts) assertion = assertion := by decide

/-! ### Split exhaustification (§5) -/

/-- Scalar exhaustification below ◇ and domain exhaustification above it give free choice with
embedded uniqueness, compatible with ◇(b₁∧b₂) (119). -/
theorem split_diamond :
    innocent.exh (innocent.preExhaustify (lift dia domainAlts)) (dia (at' exactlyOne)) =
      prop fc ∩ dia (at' exactlyOne) ∧
    world {{0}, {1}, {0, 1}} {0} ∈
      innocent.exh (innocent.preExhaustify (lift dia domainAlts)) (dia (at' exactlyOne)) := by
  decide +kernel

/-- Under □, every permitted world has exactly one book bought and each book is permitted (120).
-/
theorem split_box :
    innocent.exh (innocent.preExhaustify (lift box' domainAlts)) (box' (at' exactlyOne)) =
      prop fc ∩ box' (at' exactlyOne) := by decide +kernel

/-- A single contradiction-free operator below ◇ is vacuous (`root_innocent`), so the result is
◇(b₁∨b₂) — too weak for free choice (143). -/
theorem single_below :
    world {{0}} {0} ∈
      dia (at' (innocent.exh ({scalar} ∪ innocent.preExhaustify domainAlts) assertion)) ∧
      ¬ fc (world {{0}} {0}) := by decide +kernel

/-- A single contradiction-free operator above ◇ negates the scalar alternative, forbidding ◇(b₁∧b₂)
(146). -/
theorem single_above :
    innocent.exh ({dia (at' scalar)} ∪ innocent.preExhaustify (lift dia domainAlts))
        (dia (at' assertion)) = prop fc \ dia (at' scalar) := by decide +kernel

/-- Two contradiction-free operators, below and above ◇, also forbid ◇(b₁∧b₂) (144)–(145). -/
theorem two_innocent :
    innocent.exh ({dia (at' scalar)} ∪ innocent.preExhaustify (lift dia domainAlts))
        (dia (at' exactlyOne)) = (prop fc ∩ dia (at' exactlyOne)) \ dia (at' scalar) := by
  decide +kernel

/-! ### Downward entailing contexts (§3, §5) -/

/-- A world of the conditional (77) records the books read and whether Forood gets a gift. -/
abbrev Cond := Buy × Bool

/-- *If Forood reads a book, he gets a gift* (78b). -/
def conditional : Finset Cond := prop fun c => claim buys univ c.1 → c.2 = true

/-- The conditional with scalar exhaustification in its antecedent (130e). -/
def conditionalUnique : Finset Cond := prop fun c => c.1.card = 1 → c.2 = true

/-- The domain alternatives of the conditional (78d). -/
def condAlts : Finset (Finset Cond) :=
  (subdomainAlternatives .proper (univ : Finset (Fin 2))).image fun S =>
    prop fun c => claim buys S c.1 → c.2 = true

/-- The scalar alternative is entailed and the domain alternatives are vacuous, so the plain
existential reading survives; likewise for (135) (78)–(80). -/
theorem conditional_vacuous :
    tolerant.exh {prop fun c : Cond => 2 ≤ c.1.card → c.2 = true} conditional = conditional ∧
      innocent.exh (innocent.preExhaustify condAlts) conditional = conditional ∧
      innocent.exh (innocent.preExhaustify condAlts) conditionalUnique = conditionalUnique := by
  decide

/-- Scalar exhaustification inside the antecedent weakens the conditional, which Maximize Strength
(132) forbids (131). -/
theorem conditional_weakening : conditional ⊂ conditionalUnique := by decide

/-! ### The paper's verdicts -/

/-- Five books; a scenario fixes the permitted or epistemically possible buy-worlds. -/
abbrev Buy₅ := Finset (Fin 5)

def buys₅ (v : Buy₅) (i : Fin 5) : Prop := i ∈ v

instance (v : Buy₅) : DecidablePred (buys₅ v) := fun i => inferInstanceAs (Decidable (i ∈ v))

/-- Accessibility from any world to the scenario's possibilities. -/
def scenarioAcc (A : Finset Buy₅) : SetRel Buy₅ Buy₅ := .ofSuccessors fun _ ↦ ↑A

instance (A : Finset Buy₅) (u v : Buy₅) : Decidable (u ~[scenarioAcc A] v) :=
  inferInstanceAs (Decidable (v ∈ A))

/-- The possibilities a row's `scenario` feature names. -/
def scenario : String → Option (Finset Buy₅)
  | "permitted24" | "required28" | "known34" => some {{0}, {1}, {2}}
  | "known31" => some {∅, {0}, {1}, {2}}
  | "anyNumber104" => some (univ.filter (·.Nonempty))
  | "twoBooks108" => some (univ.filter (·.card = 2))
  | _ => none

/-- Under a modal over the possibilities `A`, a plain existential needs the claim under the
modal, *irgendein* free choice, *algún* modal variation, and *yek-i* free choice or modal
variation by flavor together with embedded uniqueness. -/
def verdict (A : Finset Buy₅) : String → String → Option Bool
  | "yek", "deontic possibility" => some (decide (◇[scenarioAcc A] (claim buys₅ univ) ∅))
  | "yek", "deontic necessity" => some (decide (□[scenarioAcc A] (claim buys₅ univ) ∅))
  | "irgendein", _ => some (decide (FreeChoice (scenarioAcc A) ∅ univ buys₅))
  | "algún", _ => some (decide (ModalVariation (scenarioAcc A) ∅ univ buys₅))
  | "yek-i", "deontic possibility" =>
    some (decide (FreeChoice (scenarioAcc A) ∅ univ buys₅ ∧ ◇[scenarioAcc A] (·.card = 1) ∅))
  | "yek-i", "deontic necessity" =>
    some (decide (FreeChoice (scenarioAcc A) ∅ univ buys₅ ∧ □[scenarioAcc A] (·.card = 1) ∅))
  | "yek-i", "epistemic possibility" =>
    some (decide (ModalVariation (scenarioAcc A) ∅ univ buys₅ ∧ ◇[scenarioAcc A] (·.card = 1) ∅))
  | "yek-i", "epistemic necessity" =>
    some (decide (ModalVariation (scenarioAcc A) ∅ univ buys₅ ∧ □[scenarioAcc A] (·.card = 1) ∅))
  | _, _ => none

/-- A row's predicted verdict from its `scenario`, `item`, and `modal` features. -/
def predicted (row : Datum) : Option Bool :=
  match row.feature? "scenario", row.feature? "item", row.feature? "modal" with
  | some s, some i, some m => scenario s >>= fun A => verdict A i m
  | _, _, _ => none

theorem rows_agree : ∀ row ∈ Examples.all, row.FitsVerdict predicted id := by
  decide +kernel

theorem rows_read :
    (Examples.all.filter fun row =>
      row.verdict.isSome ∧ (predicted row).isSome).length = 10 := by
  decide +kernel

/-- An unembedded EFCI is ungrammatical exactly when it allows neither modal insertion nor partial
exhaustification (Table 2). -/
theorem table2_rows :
    ∀ row ∈ Examples.all, (row.feature? "modalInsertion").isSome →
      (row.feature? "partialExhaustification").isSome →
      (row.judgment = .ungrammatical ↔
        row.feature? "modalInsertion" = some "no" ∧
          row.feature? "partialExhaustification" = some "no") := by decide +kernel

end AlonsoOvalleMoghiseh2025a
