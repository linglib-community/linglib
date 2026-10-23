module

public import Linglib.Semantics.Aspect.Telicity
public import Linglib.Semantics.ArgumentStructure.Affectedness
public import Linglib.Data.Examples.Filip2012

/-!
# Filip (2012): Lexical aspect

This file formalizes the mereological core of [filip-2012]'s survey of lexical aspect. The
telic/atelic distinction is diagnosed by temporal adverbials — *in an hour* with telic and
*for an hour* with atelic predicates (1) — and, following [krifka-1998], telic predicates are
taken as quantized (23) and atelic ones as cumulative (24), the substrate's `QUA` and `CUM`.
Aspectual composition (25)–(27) is [krifka-1989]'s: the predicate an incremental verb forms
with its object is quantized or cumulative as the object is, the substrate's
`vp_qua` and `vp_cum` for a strictly incremental relation, while a verb without the
incremental mapping, like *watch*, is atelic whatever its object (26). Hence the three
classes of (28): telic verbs, whose eventualities have no proper parts in the relation
(`Quantized`, `telic_of_quantized`); atelic verbs, whose relation persists to the parts of an
eventuality, the subinterval property (19) (`Persistent`, `not_telic_of_persistent`); and
incremental verbs, lexically unmarked for telicity because their non-degeneracy provides both
a quantized and a cumulative object (`incremental_underspecified`). Incrementality and
telicity are independent (29): a quantized verb is not strictly incremental
(`not_sinc_of_quantized`), and an incremental verb with a cumulative object is atelic. The
diagnostic data (1), (25), (26), (31), (37) are rows of `Data/Examples/Filip2012.json`, and
`rows_test` checks the adverbial judgments against the telicity the classification assigns.

## Implementation notes

* Telicity is identified with quantization "for the purposes of this summary" (§7), so the
  telic/atelic contrast is the substrate's `QUA`/`CUM` and the atelic verbs' persistence is
  stated with `≤` on eventualities.
* The verb classes of the rows are the chapter's: *recover* and *reach* telic, *swim* and
  *watch* atelic, *eat* and *prove* incremental; `Row.Telic` states the classification's
  verdict, whose semantic content is the theorems above.
* The chapter's surveys of Vendler's and Dowty's classifications (§§3–6) and of degree-based
  approaches (§8) summarize other authors' analyses and are not formalized here.

## References

* [filip-2012]
* [krifka-1989]
* [krifka-1998]
* [bennett-partee-1972]
* [vendler-1957]
* [dowty-1979]
-/

@[expose] public section

namespace Filip2012

open Mereology ArgumentStructure Aspect

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-! ### Telic and atelic predicates (23)–(24) -/

/-- (23): a telic predicate is quantized. -/
abbrev Telic (P : β → Prop) : Prop := QUA P

/-- (24): an atelic predicate is cumulative. -/
abbrev Atelic (P : β → Prop) : Prop := CUM P

theorem isTelic_of_telic {precedes : β → β → Prop} (h : NoPartPrecedes precedes) {P : β → Prop}
    (hP : Telic P) : IsTelic precedes P :=
  isTelic_of_qua h hP

/-! ### The three classes of verbs (28) -/

/-- A telic verb (28i): no eventuality in its relation has a proper part in it — *recover*,
*arrive*, *burst*. -/
def Quantized (θ : α → β → Prop) : Prop := ∀ x e, θ x e → ∀ y e', e' < e → ¬ θ y e'

/-- An atelic verb (28ii): its relation persists to the parts of an eventuality, the subinterval
property (19) — *run*, *watch*, *believe*. -/
def Persistent (θ : α → β → Prop) : Prop := ∀ x e, θ x e → ∀ e', e' ≤ e → θ x e'

omit [SemilatticeSup α] in
theorem telic_of_quantized {θ : α → β → Prop} (h : Quantized θ) (OBJ : α → Prop) :
    Telic (VP θ OBJ) :=
  qua_of_forall λ _ _ ⟨_, _, hθ⟩ hlt ⟨_, _, hθ'⟩ => h _ _ hθ _ _ hlt hθ'

omit [SemilatticeSup α] in
/-- (26): an atelic verb forms no telic predicate whatever its object: a proper part of one of
its eventualities is one too. -/
theorem not_telic_of_persistent {θ : α → β → Prop} (h : Persistent θ) (OBJ : α → Prop)
    {e e' : β} (hlt : e' < e) (he : VP θ OBJ e) : ¬ Telic (VP θ OBJ) := λ hQ =>
  let ⟨x, hx, hθ⟩ := he
  hQ ⟨x, hx, h x e hθ e' hlt.le⟩ he hlt.ne hlt.le

theorem atelic_of_persistent {θ : α → β → Prop} (hθ : SUM θ) {OBJ : α → Prop}
    (hObj : CUM OBJ) : Atelic (VP θ OBJ) :=
  vp_cum hθ hObj

/-- An incremental verb is lexically unmarked for telicity, being telic with some quantized object
and atelic with some cumulative one ((27), (28iii), (29ii)). -/
theorem incremental_underspecified {θ : α → β → Prop} (h : SINC θ) (hU : UP θ) (hs : SUM θ) :
    (∃ OBJ : α → Prop, QUA OBJ ∧ Telic (VP θ OBJ) ∧ ∃ e, VP θ OBJ e) ∧
    (∃ OBJ : α → Prop, CUM OBJ ∧ Atelic (VP θ OBJ) ∧ ¬ Telic (VP θ OBJ)) := by
  obtain ⟨x, y, e, e', hlt, hlt', hθ, hθ'⟩ := h.extended
  refine ⟨⟨(· = x), singleton_qua x, vp_qua hU h.mso (singleton_qua x), e, x, rfl, hθ⟩,
    ⟨λ _ => True, λ _ _ _ _ => trivial, vp_cum hs (λ _ _ _ _ => trivial), λ hQ => ?_⟩⟩
  exact hQ ⟨y, trivial, hθ'⟩ ⟨x, trivial, hθ⟩ hlt'.ne hlt'.le

/-- (29i): telicity does not require incrementality — a quantized verb is not strictly
incremental, its eventualities having no proper parts in the relation. -/
theorem not_sinc_of_quantized {θ : α → β → Prop} (h : Quantized θ) : ¬ SINC θ := λ hS =>
  let ⟨x, y, e, e', _, hlt', hθ, hθ'⟩ := hS.extended
  h x e hθ y e' hlt' hθ'

/-! ### The adverbial diagnostic (1) over the chapter's data -/

/-- The verb classes of (28). -/
inductive VerbClass where
  | telic
  | atelic
  | incremental
  deriving DecidableEq, Repr

/-- The object's reference: quantized, cumulative, or absent. -/
inductive Object where
  | quantized
  | cumulative
  | none
  deriving DecidableEq, Repr

/-- The temporal adverbials of (1). -/
inductive Adverbial where
  | inNP
  | forNP
  deriving DecidableEq, Repr

/-- A sentence of the diagnostic with its verb's class, its object's reference, its adverbial,
and the chapter's judgment. -/
structure Row where
  cls : VerbClass
  obj : Object
  adverbial : Adverbial
  judgment : Judgment
  deriving DecidableEq, Repr

/-- The telicity the classification assigns: telic verbs form telic predicates
(`telic_of_quantized`), atelic verbs never do (`not_telic_of_persistent`), and incremental
verbs follow their object ((27): `vp_qua`, `vp_cum`). -/
def Row.Telic (r : Row) : Prop :=
  match r.cls, r.obj with
  | .telic, _ => True
  | .atelic, _ => False
  | .incremental, .quantized => True
  | .incremental, _ => False

instance (r : Row) : Decidable r.Telic := by unfold Row.Telic; split <;> infer_instance

def classTable : List (String × VerbClass) :=
  [("telic", .telic), ("atelic", .atelic), ("incremental", .incremental)]

def objectTable : List (String × Object) :=
  [("quantized", .quantized), ("cumulative", .cumulative), ("none", .none)]

def adverbialTable : List (String × Adverbial) := [("in", .inNP), ("for", .forNP)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let cls ← ex.parse? "verbClass" classTable
  let obj ← ex.parse? "object" objectTable
  let adverbial ← ex.parse? "adverbial" adverbialTable
  pure ⟨cls, obj, adverbial, ex.judgment⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The *in* adverbial is acceptable exactly with telic predicates, the *for* adverbial with atelic
ones ((1), (25), (26), (31), (37)). -/
theorem rows_test : ∀ r ∈ rows, (r.judgment = .acceptable ↔ (r.adverbial = .inNP ↔ r.Telic)) := by
  decide

end Filip2012
