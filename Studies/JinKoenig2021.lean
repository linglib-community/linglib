module

public import Linglib.Data.Examples.JinKoenig2021
public import Studies.Karttunen1974
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Negation
public import Linglib.Fragments.Romance.French.Negation
public import Linglib.Fragments.Januubi.Negation
public import Linglib.Fragments.Mandarin.Negation
public import Linglib.Fragments.ZarmaSonrai.Negation

/-!
# Jin and Koenig (2021): A Cross-Linguistic Study of Expletive Negation

Jin and Koenig give a typology of expletive negation, a negator in the dependent of a lexical item,
triggered by the item's meaning, that contributes no negation to the dependent's proposition.
English, French, Januubi, Mandarin and Zarma-Sonrai share its trigger classes (`ENTriggerClass`). A
trigger's meaning activates both its argument and the argument's negation, at distinct worlds, times
or entities or within the meaning itself, (13); the substrate's operators deliver this dual
inference for *before*, *impossible* and comparatives (`before_dual`, `impossible_dual`,
`comparative_dual`), and the verbal triggers are the negative-valence attitudes and the verbs whose
affirmation implies the negation of their complement (`english_triggers`). The paper's examples are
rows whose negators are the markers of the languages' fragments, the negators the paper calls
standard being the fragments' standard negators (`kind_eq_standard_iff`), and they carry its negator
facts (`mandarin_negators`, `french_ne_of_entrenched`, `januubi_maa`).

## Implementation notes

* The survey tables, Tables 1 to 4, are counts over a convenience sample that the paper itself
  declines to draw inferences from; they are not encoded. The per-language blocking of a class,
  Sections 6.4 and 7, is `blocking`.
* The propositional-attitude condition is not derived from the preferential semantics, whose
  valence is a label; the paper's production model is not formalized.
* Under *fear* the paper reports the Januubi prohibitive *laa* without an example, so no row
  records it.

## References

* [jin-koenig-2021]
* [heim-1992]
* [dell-1986]
-/

@[expose] public section

namespace JinKoenig2021

/-! ### The dual inference (Section 5.5) -/

/-- In (13), a trigger's meaning activates its argument and the argument's negation at distinct
points of a domain, worlds, times or entities. -/
def DualInference {X : Type*} (p : X → Prop) : Prop := (∃ x, p x) ∧ ∃ y, ¬ p y

/-! ### Temporal operators (Section 6.2) -/

open Tense Anscombe1964 Karttunen1974 in
/-- *q before p* says that *p* holds at some time and fails at the time of *q*, which precedes
every time of *p*, (13b). -/
theorem before_dual {T : Type*} [LinearOrder T] {A B : Set (NonemptyInterval T)}
    (h : Tense.beforeEver A B) (hB : (timeTrace B).Nonempty) :
    DualInference (· ∈ timeTrace B) :=
  ⟨hB, let ⟨t, _, ht⟩ := h; ⟨t, fun hmem ↦ lt_irrefl t (ht t hmem)⟩⟩

/-! ### Logical operators (Section 6.3) -/

open Modality in
/-- *impossible p* is the necessity of `¬p`, so `p` fails at the best worlds and, if it holds
anywhere, the meaning activates both, (13c). -/
theorem impossible_dual {W : Type*} (f g : Background W) (p : W → Prop)
    (w : W) (h : necessity f g (fun w' ↦ ¬ p w') w) (hb : (bestWorlds f g w).Nonempty)
    (hp : ∃ x, p x) : DualInference p :=
  let ⟨w', hw'⟩ := hb
  ⟨hp, w', (necessity_iff f g _ w).1 h w' hw'⟩

open Modality in
theorem possibility_of_not_impossible {W : Type*} (f g : Background W)
    (p : W → Prop) (w : W) (h : ¬ necessity f g (fun w' ↦ ¬ p w') w) : possibility f g p w := by
  rw [necessity_iff] at h
  rw [possibility_iff]
  by_contra hne
  exact h fun w' hw' ↦ fun hp ↦ hne ⟨w', hw', hp⟩

/-- *q without p* is `q ∧ ¬p`, the negation in the meaning, (13c). -/
def withoutSem {W : Type*} (q p : Set W) : Set W := q ∩ pᶜ

theorem withoutSem_subset_compl {W : Type*} (q p : Set W) : withoutSem q p ⊆ pᶜ :=
  Set.inter_subset_right

/-- *q unless p* says that if not `p` then `q`, so `¬p` holds in the suppositive worlds,
(13c). -/
def unlessSem {W : Type*} (q p : Set W) : Set W := Conditional.materialImp pᶜ q

theorem mem_of_mem_unlessSem {W : Type*} {q p : Set W} {w : W} (h : w ∈ unlessSem q p)
    (hp : w ∉ p) : w ∈ q :=
  h hp

/-! ### Comparatives (Section 6.4) -/

/-- *Y is more Q than Z* says that `Y` has `Q` to its own degree and `Z` does not, the two
predications of (13d) over distinct entities. -/
theorem comparative_dual {Entity α : Type*} [LinearOrder α] (μ : Entity → α) (y z : Entity)
    (h : μ z < μ y) : DualInference fun e ↦ μ y ≤ μ e :=
  ⟨⟨y, le_rfl⟩, ⟨z, not_le.2 h⟩⟩

/-! ### Verbal triggers -/

/-- A verb triggers expletive negation (§5.5) when it is a negative-valence preferential
attitude (*fear*) or its affirmation implies the negation of its complement (*forget*,
*prevent*). -/
def IsExpletiveNegationTrigger (v : Verb) : Prop :=
  v.attitude.bind Attitude.valence = some .negative ∨ v.implicative.positive = .some .negative

instance : DecidablePred IsExpletiveNegationTrigger := fun _ ↦
  inferInstanceAs (Decidable (_ ∨ _))

open English
open English.Verbs hiding Verb
theorem english_triggers :
    IsExpletiveNegationTrigger fear.toVerb ∧ IsExpletiveNegationTrigger dread.toVerb ∧
      IsExpletiveNegationTrigger worry.toVerb ∧ IsExpletiveNegationTrigger forget.toVerb ∧
      IsExpletiveNegationTrigger prevent.toVerb :=
  ⟨.inl rfl, .inl rfl, .inl rfl, .inr rfl, .inr rfl⟩

/-! ### Trigger classes (Tables 5 and 6) -/

/-- The trigger classes of Table 5, each named by a representative concept. -/
inductive ENTriggerClass where
  | fear
  | regret
  | deny
  | forget
  | before
  | cannotWait
  | since
  | rarely
  | impossible
  | without
  | unless
  | moreThan
  | differentThan
  | tooTo
  deriving DecidableEq, Repr, Fintype

/-- The trigger concepts of Table 6, one representative per subclass. -/
inductive ENConcept where
  | fear
  | avoid
  | regret
  | complain
  | adviseAgainst
  | deny
  | hide
  | despair
  | forget
  | delay
  | refuse
  | stop
  | prevent
  | almost
  | barely
  | before
  | cannotWait
  | since
  | rarely
  | impossible
  | difficult
  | without
  | unless
  | onlyDependsOn
  | moreThan
  | lessThan
  | differentThan
  | tooTo
  deriving DecidableEq, Repr, Fintype

/-- The class of a concept. -/
def ENConcept.cls : ENConcept → ENTriggerClass
  | .fear | .avoid => .fear
  | .regret | .complain | .adviseAgainst => .regret
  | .deny | .hide | .despair => .deny
  | .forget | .delay | .refuse | .stop | .prevent | .almost | .barely => .forget
  | .before => .before
  | .cannotWait => .cannotWait
  | .since => .since
  | .rarely => .rarely
  | .impossible | .difficult => .impossible
  | .without => .without
  | .unless | .onlyDependsOn => .unless
  | .moreThan | .lessThan => .moreThan
  | .differentThan => .differentThan
  | .tooTo => .tooTo

/-! ### The examples -/

/-- The five languages of Section 4. -/
inductive Language
  | english
  | french
  | januubi
  | mandarin
  | zarmaSonrai
  deriving DecidableEq, Repr

open Negation in
/-- The standard negators of a language, from its fragment. -/
def Language.standard : Language → List Marker
  | .english => English.Negation.standard
  | .french => French.Negation.standard
  | .januubi => Januubi.Negation.standard
  | .mandarin => Mandarin.Negation.negators.map (·.marker)
  | .zarmaSonrai => ZarmaSonrai.Negation.standard

open Negation in
/-- The negators of a language's fragment, under the forms the rows cite them by. -/
def Language.negators : Language → List (String × Marker)
  | .english => [("not", English.Negation.not)]
  | .french => [("ne pas", French.Negation.nePas), ("ne", French.Negation.ne)]
  | .januubi => [("maa", Januubi.Negation.maa), ("laa", Januubi.Negation.laa)]
  | .mandarin =>
    [("bù", Mandarin.Negation.bu.marker), ("méi", Mandarin.Negation.mei.marker),
      ("bié", Mandarin.Negation.bie), ("bùgāi", Mandarin.Negation.bugai)]
  | .zarmaSonrai =>
    [("si", ZarmaSonrai.Negation.si), ("mana", ZarmaSonrai.Negation.mana),
      ("sinda", ZarmaSonrai.Negation.sinda)]

/-- An example uses the standard negator, a dedicated expletive negator (French *ne* alone), an
imperative negator (Mandarin *bié*), a deontic one (Mandarin *bùgāi*) or a copular one
(Zarma-Sonrai *sinda*). -/
inductive NegatorKind
  | standard
  | dedicated
  | imperative
  | deontic
  | copular
  deriving DecidableEq, Repr

/-- A row records the language, the trigger concept, the negator, its kind, and for French
whether the paper reports the use as entrenched. -/
structure Row where
  language : Language
  concept : ENConcept
  negator : Negation.Marker
  kind : NegatorKind
  entrenched : Option Bool
  deriving DecidableEq

def languageOf : String → Option Language
  | "stan1293" => some .english
  | "stan1290" => some .french
  | "gulf1241" => some .januubi
  | "mand1415" => some .mandarin
  | "zarm1239" => some .zarmaSonrai
  | _ => none

def conceptOf : String → Option ENConcept
  | "fear" => some .fear
  | "avoid" => some .avoid
  | "regret" => some .regret
  | "complain" => some .complain
  | "deny" => some .deny
  | "hide" => some .hide
  | "forget" => some .forget
  | "delay" => some .delay
  | "barely" => some .barely
  | "before" => some .before
  | "cannotWait" => some .cannotWait
  | "rarely" => some .rarely
  | "onlyDependsOn" => some .onlyDependsOn
  | "differentThan" => some .differentThan
  | "tooTo" => some .tooTo
  | _ => none

def kindOf : String → Option NegatorKind
  | "standard" => some .standard
  | "dedicated" => some .dedicated
  | "imperative" => some .imperative
  | "deontic" => some .deontic
  | "copular" => some .copular
  | _ => none

/-- A row from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let l ← languageOf e.language
  let c ← (e.feature? "concept").bind conceptOf
  let n ← e.parse? "negator" l.negators
  let k ← (e.feature? "negator_kind").bind kindOf
  some ⟨l, c, n, k, (e.feature? "entrenched").map (· == "high")⟩

/-- The examples of Sections 1, 2 and 6. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (e.feature? "negator").isSome →
    (Row.ofDatum e).isSome := by
  decide

theorem kind_eq_standard_iff :
    ∀ r ∈ rows, r.kind = .standard ↔ r.negator ∈ r.language.standard := by
  decide

theorem mandarin_negators :
    ∀ r ∈ rows, r.language = .mandarin →
      (r.kind = .imperative ↔ r.concept = .fear) ∧
        (r.kind = .deontic ↔ r.concept.cls = .regret) := by
  decide

/-- French marks its entrenched uses with *ne* alone, Section 5.5. -/
theorem french_ne_of_entrenched :
    ∀ r ∈ rows, r.language = .french → r.entrenched = some true →
      r.negator = French.Negation.ne := by
  decide

theorem januubi_maa : ∀ r ∈ rows, r.language = .januubi → r.negator = Januubi.Negation.maa := by
  decide

/-! ### Blocked classes (Sections 6.4 and 7) -/

/-- Why a trigger class fails to license expletive negation in a language, Section 7. -/
inductive ENBlockingReason where
  /-- The language disprefers modal operators in complement clauses. -/
  | modalRestriction
  /-- Comparative complements admit only noun phrases. -/
  | npOnlyComplement
  /-- The concept is expressed analytically with a necessary negation. -/
  | analyticNegation
  deriving DecidableEq, Repr

/-- A concept can fail to trigger expletive negation in a language for three reasons. Januubi admits
only noun phrases as complements of comparatives and disprefers the modal that the *regret* class
needs; Januubi, Mandarin and Zarma-Sonrai express *too … to* as 'too … so that … not'; and Mandarin
and Zarma-Sonrai express *without* as 'q not p', where the negation is part of the meaning. -/
def blocking : Language → ENConcept → Option ENBlockingReason
  | .januubi, .moreThan | .januubi, .lessThan => some .npOnlyComplement
  | .januubi, .regret => some .modalRestriction
  | .januubi, .tooTo | .mandarin, .tooTo | .zarmaSonrai, .tooTo => some .analyticNegation
  | .mandarin, .without | .zarmaSonrai, .without => some .analyticNegation
  | _, _ => none

theorem blocking_eq_none_of_mem : ∀ r ∈ rows, blocking r.language r.concept = none := by decide

end JinKoenig2021
