module

public import Mathlib.Data.Fintype.Prod
public import Linglib.Semantics.Causation.CausalModel.Dependence
public import Linglib.Semantics.Presupposition.Implicative
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Fragments.Finnish.Verbs
public import Linglib.Data.Examples.Nadathur2023

/-!
# Nadathur (2023)

Nadathur analyses an implicative as Karttunen's presupposition–proposition pair with causal
conditions, the paper's Proposal (32). The verb presupposes that its prerequisite is causally
necessary for the complement and, if it is two-way, causally sufficient, both relative to a
background situation, and it asserts the prerequisite. Under this causal interpretation of the
conditions (`causalInterpretation`), which is sound at every context of the background, a verb
implies what its implication signature says.

In the paper's Dreyfus scenario, an eight-vertex causal model, the nerve that *dare* names is
causally necessary and sufficient for sending the message, so *dare* is felicitous there and its
assertion and denial decide the message (`dare_felicitous_for_msg`, `msg_of_dare`,
`not_msg_of_not_dare`). The nerve is necessary but not sufficient for establishing communication and
for spying, so *dare* is infelicitous there (`dare_infelicitous_for_com`,
`dare_infelicitous_for_spy`). Each of the paper's Finnish minimal pairs implies what the signature
of its verb's Fragment entry says for its matrix polarity (`rows_agree`), and its complement is a
Fragment verb in the infinitive and case that verb governs (`complement_mem_infinitiveForms`).

## Implementation notes

A fact is a variable with a value, and the worlds of the causal interpretation are the contexts
where the background holds; the interpretation needs the context to reach the model only at its
roots, as in the paper's dynamics. The sufficiency verdicts are decided over the finite model; the
necessity verdicts are proved through the equations, which make every path to the effect run through
the nerve.

Definition 10b ranges over the consistent supersituations of Definition 9b
(`IsConsistentSupersituation`), and over them the verdicts on (34c) and (34d) fail: settling the
message, which the background leaves open, reaches communication without the nerve
(`Consistent.not_nrv_necessary_for_com`). The paper argues those verdicts from the background
variables alone, so necessity is read over the exogenous settlements, a subset of the consistent
supersituations (`isConsistentSupersituation_of_isExogenousSettlement`).

## TODO

The *manage* examples need set-valued prerequisites, one of them the
conjunction of courage, a listener, and an ungarbled message, while the substrate's
sufficiency semantics takes a single prerequisite vertex.

## References

* [nadathur-2023-implicatives]
* [nadathur-2019]
* [baglini-francez-2016]
* [karttunen-1971]
-/

@[expose] public section

namespace Nadathur2023

open CausalModel Implicative Presupposition NaturalLogic

/-! ### Consistent supersituations -/

section Consistent

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α) [M.IsAcyclic]

/-- `IsConsistentSupersituation M s s'` says that `s'` is a consistent supersituation of `s`
(Definition 9b). It extends `s`, and to each variable with parents that it newly settles it gives
the only value the strict development of `s` could settle there. -/
def IsConsistentSupersituation (s s' : ∀ v, Flat (α v)) : Prop :=
  s ≤ s' ∧ ∀ v, s v = ⊥ → (∃ w, M.graph.Adj w v) → ∀ x : α v, s' v = ↑x →
    ∀ z, M.CausallyEntails s v z → z = x

variable {M}

theorem isConsistentSupersituation_of_isExogenousSettlement {s s' : ∀ v, Flat (α v)}
    (h : M.IsExogenousSettlement s s') : IsConsistentSupersituation M s s' :=
  ⟨h.1, fun v hv ⟨w, hw⟩ x hx _ _ ↦
    absurd hw ((h.2 v hv (by rw [hx]; exact Flat.coe_ne_bot)).1 w)⟩

instance [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)] [Fintype V]
    [∀ v, Fintype (α v)] [DecidableRel M.graph.Adj] (s s' : ∀ v, Flat (α v)) :
    Decidable (IsConsistentSupersituation M s s') :=
  haveI : ∀ v, Decidable (s v = ⊥ → (∃ w, M.graph.Adj w v) → ∀ x : α v, s' v = ↑x →
      ∀ z, M.CausallyEntails s v z → z = x) := fun _ ↦ inferInstance
  inferInstanceAs (Decidable (_ ∧ _))

end Consistent

/-! ### Proposal (32) -/

section Interpretation

variable {U V : Type*} [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]
  [M.ContextAtRoots]

/-- The causal interpretation of the conditions over the contexts where the background `s` holds. A
fact is a variable with a value, and one fact is sufficient (Definition 10a) or necessary
(Definition 10b, over the exogenous settlements) for another relative to `s`, which does not settle
the first (the preamble of Definition 10). -/
def causalInterpretation (s : V → Flat Bool) : Interpretation (V × Bool) (M.contexts s) where
  Holds a u := M.solve ⊥ u a.1 = a.2
  neg a := (a.1, !a.2)
  holds_neg a u := by rcases a with ⟨v, x⟩; cases x <;> simp
  Sufficient a b _ := ¬ M.CausallyEntails s a.1 a.2 ∧ M.CausallySufficient s a.1 a.2 b.1 b.2
  Necessary a b _ :=
    ¬ M.CausallyEntails s a.1 a.2 ∧ M.CausallyNecessary M.IsExogenousSettlement s a.1 a.2 b.1 b.2
  holds_of_sufficient {_ _ u} h := h.2.solve_eq u.2
  holds_of_necessary {_ _ u} h := h.2.solve_eq u.2

end Interpretation

/-- The vertices of the Dreyfus scenario are INT (Dreyfus intends to spy), NRV (he has the
nerve), LST (a German is listening on the correct frequency), BRK (the message is garbled), SEC
(he collects secrets), MSG (he sends a radio message), COM (he establishes communication) and
SPY (he spies for the Germans) ([nadathur-2023-implicatives] §6.1.1, Figure 3). -/
inductive V | INT | NRV | LST | BRK | SEC | MSG | COM | SPY
  deriving DecidableEq, Fintype, Repr

/-- In the causal graph SEC reads INT, MSG reads INT and NRV, COM reads MSG, LST and BRK, and SPY
reads SEC and COM, with INT, NRV, LST and BRK exogenous. -/
def edges : Finset (V × V) :=
  {(.INT, .SEC), (.INT, .MSG), (.NRV, .MSG), (.MSG, .COM), (.LST, .COM), (.BRK, .COM),
    (.SEC, .SPY), (.COM, .SPY)}

/-- The context settles the intention, the nerve, the listener, and the garbling. -/
structure Context where
  INT : Bool
  NRV : Bool
  LST : Bool
  BRK : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The Dreyfus model, with the negative `¬BRK` precondition encoded directly in the COM
equation. -/
def dreyfusModel : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .INT => fun u _ ↦ u.INT
    | .NRV => fun u _ ↦ u.NRV
    | .LST => fun u _ ↦ u.LST
    | .BRK => fun u _ ↦ u.BRK
    | .SEC => fun _ x ↦ x .INT
    | .MSG => fun _ x ↦ x .INT && x .NRV
    | .COM => fun _ x ↦ x .MSG && x .LST && !x .BRK
    | .SPY => fun _ x ↦ x .SEC && x .COM

instance : DecidableRel dreyfusModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : dreyfusModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the background Dreyfus intends to spy and has already collected secrets (INT = SEC = 1),
and NRV, LST and BRK are unresolved. -/
def dreyfusBg : V → Flat Bool := [.INT ← true, .SEC ← true]

instance : dreyfusModel.ContextAtRoots :=
  ⟨fun {v w} hw _ _ _ ↦ by cases v <;> first | rfl | (exfalso; revert hw; revert w; decide)⟩

/-- *Dreyfus dared to `e`*, a verb of the two-way signature `+/−` under the causal interpretation,
with the nerve as the prerequisite. -/
noncomputable def dare (e : V) : dreyfusModel.contexts dreyfusBg → SignType :=
  sentence (causalInterpretation dreyfusModel dreyfusBg) ⟨.some .positive, .some .negative⟩
    (.NRV, true) (e, true)

theorem nrv_sufficient_for_msg :
    ¬ dreyfusModel.CausallyEntails dreyfusBg .NRV true ∧
      dreyfusModel.CausallySufficient dreyfusBg .NRV true .MSG true := by
  decide

/-! The no-alternative clauses follow from the equations: a variable the development settles
settles each parent to the value its equation needs (`CausalModel.CausallyEntails.parent_eq`), so
settling MSG true needs NRV true, settling COM true needs MSG true, and settling SPY true needs
COM true. -/

section Equations

variable {s : V → Flat Bool}

theorem nrv_of_msg (hs : s .MSG = ⊥) (h : dreyfusModel.CausallyEntails s .MSG true) :
    dreyfusModel.CausallyEntails s .NRV true :=
  h.parent_eq hs (by decide) fun _ _ hy ↦ by simpa using (Bool.and_eq_true_iff.1 hy).2

theorem msg_of_com (hs : s .COM = ⊥) (h : dreyfusModel.CausallyEntails s .COM true) :
    dreyfusModel.CausallyEntails s .MSG true :=
  h.parent_eq hs (by decide) fun _ _ hy ↦ by
    simpa using (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hy).1).1

theorem com_of_spy (hs : s .SPY = ⊥) (h : dreyfusModel.CausallyEntails s .SPY true) :
    dreyfusModel.CausallyEntails s .COM true :=
  h.parent_eq hs (by decide) fun _ _ hy ↦ by simpa using (Bool.and_eq_true_iff.1 hy).2

end Equations

/-- The Dreyfus background with the nerve, listener and ungarbled message settled. -/
def resolved : V → Flat Bool :=
  Function.update (Function.update (Function.update dreyfusBg .NRV ↑true) .LST ↑true) .BRK ↑false

theorem nrv_necessary_for_msg :
    ¬ dreyfusModel.CausallyEntails dreyfusBg .NRV true ∧
      dreyfusModel.CausallyNecessary dreyfusModel.IsExogenousSettlement dreyfusBg .NRV true .MSG
        true :=
  ⟨by decide, by decide, ⟨_, .refl _, by decide, by decide⟩, fun _ _ hc h ↦ nrv_of_msg hc h⟩

/-- *Dreyfus dared to send a message to the Germans* (34a) is felicitous. -/
theorem dare_felicitous_for_msg (u : dreyfusModel.contexts dreyfusBg) : dare .MSG u ≠ 0 := by
  rw [dare, sentence, Set.indicator_apply_ne_zero]
  exact ⟨⟨fun _ hq ↦ by obtain rfl := Flat.coe_inj.1 hq; exact nrv_sufficient_for_msg,
    fun _ hq ↦ by obtain rfl := Flat.coe_inj.1 hq; exact nrv_necessary_for_msg⟩, by simp⟩

/-- (34a) entails that Dreyfus sent the message. -/
theorem msg_of_dare {u : dreyfusModel.contexts dreyfusBg} (h : dare .MSG u = 1) :
    dreyfusModel.solve ⊥ u .MSG = true := by
  have h' : (Polarity.positive • dare .MSG) u = 1 := by simpa using h
  exact holds_signed_of_implied_eq (m := .positive) (q := .positive) rfl h'

/-- (34b) *Dreyfus did not dare to send a message to the Germans* entails that he did not send
it. -/
theorem not_msg_of_not_dare {u : dreyfusModel.contexts dreyfusBg}
    (h : (-dare .MSG) u = 1) : dreyfusModel.solve ⊥ u .MSG ≠ true := by
  have h' : (Polarity.negative • dare .MSG) u = 1 := by simpa using h
  exact ((causalInterpretation dreyfusModel dreyfusBg).holds_neg _ u).1
    (holds_signed_of_implied_eq (m := .negative) (q := .negative) rfl h')

/-- *?/# Dreyfus dared to establish communication with the Germans* (34c) is infelicitous, since NRV
is not causally sufficient for COM. -/
theorem dare_infelicitous_for_com (u : dreyfusModel.contexts dreyfusBg) : dare .COM u = 0 := by
  rw [dare, sentence]
  exact Set.indicator_of_notMem (fun h ↦
    (by decide : ¬ dreyfusModel.CausallySufficient dreyfusBg .NRV true .COM true)
      (h.1 .positive rfl).2) _

/-- *?/# Dreyfus dared to spy for the Germans* (34d) is infelicitous, since NRV is not causally
sufficient for SPY. -/
theorem dare_infelicitous_for_spy (u : dreyfusModel.contexts dreyfusBg) : dare .SPY u = 0 := by
  rw [dare, sentence]
  exact Set.indicator_of_notMem (fun h ↦
    (by decide : ¬ dreyfusModel.CausallySufficient dreyfusBg .NRV true .SPY true)
      (h.1 .positive rfl).2) _

-- (34c)
theorem nrv_necessary_for_com :
    dreyfusModel.CausallyNecessary dreyfusModel.IsExogenousSettlement dreyfusBg .NRV true .COM
      true :=
  ⟨by decide, ⟨resolved, by decide, by decide, by decide⟩, fun _ hset hc h ↦
    nrv_of_msg (hset.eq_bot (by decide) ⟨.INT, by decide⟩) (msg_of_com hc h)⟩

-- (34d)
theorem nrv_necessary_for_spy :
    dreyfusModel.CausallyNecessary dreyfusModel.IsExogenousSettlement dreyfusBg .NRV true .SPY
      true :=
  ⟨by decide, ⟨resolved, by decide, by decide, by decide⟩, fun _ hset hc h ↦
    nrv_of_msg (hset.eq_bot (by decide) ⟨.INT, by decide⟩)
      (msg_of_com (hset.eq_bot (by decide) ⟨.MSG, by decide⟩) (com_of_spy hc h))⟩

/-! ### Definition 10b over consistent supersituations

Definition 10b quantifies over the consistent supersituations of the background. One of them
settles the message, which the background leaves open, together with a listener and an ungarbled
message, and so reaches communication and spying without the nerve. -/

namespace Consistent

/-- The Dreyfus background with the message sent, a German listening, and the message
ungarbled. -/
def messageSent : V → Flat Bool :=
  [.INT ← true, .SEC ← true, .MSG ← true, .LST ← true, .BRK ← false]

-- (34a)
theorem nrv_necessary_for_msg :
    dreyfusModel.CausallyNecessary (IsConsistentSupersituation dreyfusModel) dreyfusBg .NRV true
      .MSG true :=
  ⟨by decide, ⟨Function.update dreyfusBg .NRV ↑true, by decide, by decide, by decide⟩,
    fun _ _ hc h ↦ nrv_of_msg hc h⟩

/-- Over consistent supersituations NRV is not causally necessary for COM, against the paper's
verdict on (34c), since settling the message reaches communication without the nerve. -/
theorem not_nrv_necessary_for_com :
    ¬ dreyfusModel.CausallyNecessary (IsConsistentSupersituation dreyfusModel) dreyfusBg .NRV
      true .COM true :=
  fun h ↦ absurd (h.2.2 messageSent (by decide) (by decide) (by decide)) (by decide)

-- (34d)
theorem not_nrv_necessary_for_spy :
    ¬ dreyfusModel.CausallyNecessary (IsConsistentSupersituation dreyfusModel) dreyfusBg .NRV
      true .SPY true :=
  fun h ↦ absurd (h.2.2 messageSent (by decide) (by decide) (by decide)) (by decide)

end Consistent

/-! ### The Finnish implicatives

*Onnistua* is the bleached two-way verb, and *uskaltaa*, *viitsiä*, *malttaa*, *hennoa*,
*kehdata* and *ehtiä* name their prerequisites, courage, engagement, patience,
hard-heartedness, the lack of shame and time. *Jaksaa* names strength and *mahtua* being small
enough, and both imply only when negated, as does *pystyä*, which the paper also allows might be
a modal; *laiminlyödä* and *epäröidä* reverse the polarity. The Fragment's entries carry these
signatures. -/

/-- A minimal-pair member records the implication signature of its verb, the polarity of its
matrix, and the polarity of the complement the paper says it implies, if any. -/
structure Row where
  signature : ImplicationSignature
  matrix : Polarity
  entails : Flat Polarity

/-- A row from the paper's features, with the signature of the Fragment's entry for its verb. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let k ← e.parse? "verb" (Finnish.verbs.map fun v ↦ (v.form, v.implicative))
  let m ← e.parse? "matrix" [("positive", Polarity.positive), ("negated", .negative)]
  let ent : Flat Polarity ← e.parse? "entails"
    [("complement", ↑Polarity.positive), ("negation", ↑Polarity.negative), ("nothing", ⊥)]
  some ⟨k, m, ent⟩

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (Row.ofDatum e).isSome := by
  decide

/-- The rows of the paper's Finnish minimal pairs. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_agree : ∀ r ∈ rows, r.signature.implied r.matrix = r.entails := by
  decide

/-- The complement of an example, its word glossed as an infinitive. -/
def complement? (e : Datum) : Option (List Phonology.Segment) := do
  let w ← e.glossedTokens.find? fun w ↦ decide (['I', 'N', 'F'] <:+: w.2.toList)
  (w.1.toList.filter (· ≠ '-')).mapM Finnish.ofChar

theorem complement_mem_infinitiveForms : ∀ e ∈ Examples.all, ∃ v ∈ Finnish.verbs,
    e.feature? "verb" = some v.form ∧ ∃ ic ∈ v.complement, ∃ x ∈ complement? e,
      ∃ u ∈ Finnish.verbs, x ∈ u.infinitiveForms ic.1 ic.2 := by
  decide +kernel

end Nadathur2023
