module

public import Studies.BeaverCondoravdi2003
public import Linglib.Semantics.Events.Basic
public import Linglib.Fragments.Japanese.TemporalConnectives
public import Linglib.Data.Examples.OgiharaSteinertThrelkeld2024

/-!
# Ogihara and Steinert-Threlkeld (2024): Limitations of a Modal Analysis of Before and After

Beaver and Condoravdi take *A before B* to say that a time of `A` precedes the earliest time of
`B` across the alternatives of the world at that time, worlds agreeing with it up to the time.
Ogihara and Steinert-Threlkeld argue that this cannot make an anti-veridical *before* true: once
the main clause is settled by the history up to its time, as Mozart's death is, it holds in every
alternative, and a temporal clause it precludes occurs afterwards in none (§2). Their revision
relativizes the equivalence of worlds to an eventuality, two worlds being equivalent at an
interval for an eventuality when a counterpart of it starts with it and runs alongside it up to
the interval and the worlds are identical before it starts (17). *A before B* is then true if `B`
holds in the world after the main-clause interval, false if it holds there otherwise, and
otherwise true iff the interval precedes the earliest one at which, in an alternative for an
eventuality ongoing at it, the counterpart of the eventuality causes a `B`-eventuality (19). In
one history of Mozart's death the revision makes (6a) true through an alternative that Beaver and
Condoravdi's initial branch point condition excludes, while their analysis makes it false. Both
analyses fail on a temporal clause confined to times no later than the main clause, as Ohtani's
tenth win of the season is to the season. With the season the same in every world, no model makes
(20a)–(20c) or the Japanese (21) true, though all are acceptable.

## Main definitions

* `EventFrame`, `EventFrame.Equiv`: eventualities across worlds and the equivalence (17).
* `Alternatives`, `Alternatives.before`: the alternatives (18) and the revised *before* (19).

## Main results

* `not_before_of_settled`: Beaver and Condoravdi's *before* fails when the main clause is settled
  at its times and precludes the temporal clause afterwards, and `not_settled_mozart`: their own
  Mozart model leaves the death unsettled.
* `EventFrame.Equiv.anti`: the downward closure (18c) follows from (17).
* `Mozart.before_dies_finishes`, `Mozart.not_before_dies_finishes`: in one history the revision
  verifies (6a) counterfactually and the original analysis does not.
* `Alternatives.not_before_of_causedTimes_eq_empty`: without an eventuality that could lead to it,
  an anti-veridical *before* is false, the oddity of (14).
* `not_before_of_le`, `Alternatives.not_before_of_le`: both analyses fail on a temporal clause
  confined to times no later than the main clause (§5.1), though (20a)–(20c) and (21) are
  acceptable, `rows_bcCounterexample`.
* `rows_connective_tense`: the non-past of (21) is the tense the fragment records for *mae*.

## Implementation notes

* A main clause settled at a time holds there in every historical alternative of the world,
  Condoravdi's `HistoricalAlternatives.settled`.
* An interval `I₂ ≤ I₀` of (19ii) is one that does not follow `I₀`, so (19i) and (19ii) divide the
  `B`-intervals of the world, and (19iii) applies exactly when the world has none. The earliest
  interval of (19iii) is the one that starts first, and precedence is that of fn. 22.
* The event continuation condition (18b) is stated without its proviso *as long as this is
  reasonable*.
* The comparison with the progressive (§3) is not formalized. The non-committal readings of
  §5.2, which contextual plausibility governs, are recorded in the example rows only.

## References

* [ogihara-steinert-threlkeld-2024]
* [beaver-condoravdi-2003]
* [condoravdi-2002]
* [landman-1992]
-/

@[expose] public section

namespace OgiharaSteinertThrelkeld2024

open Event (τ)
open OgiharaSteinertThrelkeld2024.Examples Temporal HistoricalAlternatives

/-! ### Beaver and Condoravdi's alternatives (§2) -/

section Original

open BeaverCondoravdi2003

variable {W T : Type*} [LinearOrder T] {A B : Set (W × T)} {w : W}

/-- If the main clause is settled at its times and precludes the temporal clause afterwards,
initial-branch-point alternatives never make *A before B* true (§2). -/
theorem not_before_of_settled {F : TWFrame W T} (a : Alternatives F B)
    (hA : ∀ t, (w, t) ∈ A → F.alternatives.settled {w} t fun v ↦ (v, t) ∈ A)
    (hAB : ∀ v t t', (v, t) ∈ A → (v, t') ∈ B → t' < t) : ¬ before A B a.alt w := by
  rintro ⟨t, ht, e, ⟨⟨v, hv, he⟩, -⟩, hte⟩
  exact (hAB v t e ((hA t ht w (Set.mem_singleton w) v (a.subset_alternatives _ hv)).1 ht)
    he).asymm hte

/-- Beaver and Condoravdi's Mozart model makes the counterfactual *before* true only by leaving
the death unsettled at its time, Mozart living on in an alternative that agrees with the world
before it. -/
theorem not_settled_mozart :
    ¬ frame.alternatives.settled {World.early} 1 fun v ↦ (v, 1) ∈ dies := by
  intro h
  have := (h .early rfl .later (mem_alternatives_of_le_one le_rfl _ _)).1 rfl
  simp [dies, World.death] at this

/-- Alternatives parting before the main-clause time may instantiate the temporal clause before it,
and then *A before B* fails (§2). -/
theorem not_lt_of_isLeast_of_lt {alt : HistoricalAlternatives W T} {v : W} {t t' e : T}
    (hv : v ∈ alt (w, t)) (hB : (v, t') ∈ B) (ht' : t' < t)
    (he : IsLeast (instTimes (alt (w, t)) B) e) : ¬ t < e :=
  fun hte ↦ not_lt_of_ge (he.2 ⟨v, hv, hB⟩) (ht'.trans hte)

/-- A temporal clause confined to times no later than `hi` makes *A before B* false for main-clause
times from `hi` on (§5.1). -/
theorem not_before_of_le {alt : HistoricalAlternatives W T} {hi : T}
    (hB : ∀ v t, (v, t) ∈ B → t ≤ hi) (hA : ∀ t, (w, t) ∈ A → hi ≤ t) : ¬ before A B alt w :=
  fun ⟨t, ht, _, ⟨⟨_, _, he⟩, _⟩, hte⟩ ↦ lt_irrefl t (hte.trans_le ((hB _ _ he).trans (hA t ht)))

end Original

/-! ### Eventuality-relative alternatives (§4) -/

section Revision

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-- Eventualities across worlds over a history of the worlds. Each eventuality lies in one world
(fn. 20), a counterpart of an eventuality starts when it does (fn. 18), and the continuation of
one eventuality may cause another, in the loose sense of (19). -/
structure EventFrame (W T E : Type*) [LinearOrder T] [Event.TemporalTrace E T] where
  /-- The historical equivalence of the worlds, identity before a time. -/
  history : TWFrame W T
  /-- The world an eventuality lies in. -/
  world : E → W
  /-- `e₂` is a counterpart of `e₁`. -/
  Counterpart : E → E → Prop
  /-- Counterparts start at the same time. -/
  fst_eq : ∀ ⦃e₁ e₂⦄, Counterpart e₁ e₂ → (τ e₁).fst = (τ e₂).fst
  /-- The continuation of `e₁` causes `e₂`. -/
  Causes : E → E → Prop

namespace EventFrame

variable (M : EventFrame W T E)

/-- A world `w₂` is equivalent at `I` to the world of `e₁` for `e₁` (17) when an eventuality of
`w₂` is a counterpart of `e₁`, both occur throughout `[start e₁, start I)`, and the worlds are
identical before `e₁` starts. -/
def Equiv (I : NonemptyInterval T) (e₁ : E) (w₂ : W) : Prop :=
  ∃ e₂, M.world e₂ = w₂ ∧ M.Counterpart e₁ e₂ ∧ Set.Ico (τ e₁).fst I.fst ⊆ ↑(τ e₁) ∧
    Set.Ico (τ e₁).fst I.fst ⊆ ↑(τ e₂) ∧ M.history.sim (τ e₁).fst (M.world e₁) w₂

variable {M} {I I' : NonemptyInterval T} {e : E} {w : W}

/-- Equivalence at an interval gives equivalence at any earlier one (18c), which (17) already
entails. -/
theorem Equiv.anti (h : M.Equiv I e w) (hI : I'.Precedes I) : M.Equiv I' e w := by
  obtain ⟨e₂, hw, hc, h₁, h₂, hs⟩ := h
  have h : Set.Ico (τ e).fst I'.fst ⊆ Set.Ico (τ e).fst I.fst :=
    Set.Ico_subset_Ico_right (I'.fst_le_snd.trans hI.le)
  exact ⟨e₂, hw, hc, h.trans h₁, h.trans h₂, hs⟩

end EventFrame

/-- An eventuality holds throughout an interval abutting `I₀`, one ending where `I₀` begins
(19iii). -/
def HoldsAbutting (e : E) (I₀ : NonemptyInterval T) : Prop :=
  ∃ J : NonemptyInterval T, J.snd = I₀.fst ∧ (J : Set T) ⊆ ↑(τ e)

/-- An eventuality holds throughout an interval abutting `I₀` iff it is ongoing at the start of `I₀`
(fn. 23). -/
theorem holdsAbutting_iff {e : E} {I₀ : NonemptyInterval T} :
    HoldsAbutting e I₀ ↔ I₀.fst ∈ τ e := by
  refine ⟨fun ⟨J, hJ, h⟩ ↦ ?_, fun h ↦ ⟨.pure I₀.fst, rfl, by simpa using h⟩⟩
  rw [← hJ]
  exact h ⟨J.fst_le_snd, le_rfl⟩

/-- The eventuality-relative alternatives (18) of a world at an interval for an eventuality of the
world (fn. 23), equivalent to the world (18a), in which the counterpart of the eventuality
develops beyond the interval (18b). -/
structure Alternatives (M : EventFrame W T E) where
  /-- The alternatives of a world at an interval for an eventuality. -/
  alt : W → NonemptyInterval T → E → Set W
  /-- The eventuality lies in the world, and its alternatives are equivalent to it (18a). -/
  equiv_of_mem : ∀ ⦃w I e v⦄, v ∈ alt w I e → M.world e = w ∧ M.Equiv I e v
  /-- The counterpart of the eventuality develops beyond the interval (18b). -/
  continues : ∀ ⦃w I e v⦄, v ∈ alt w I e →
    ∃ e₂, M.world e₂ = v ∧ M.Counterpart e e₂ ∧ I.snd < (τ e₂).snd

namespace Alternatives

variable {M : EventFrame W T E} (a : Alternatives M) (A B : Set (W × NonemptyInterval T × E))

/-- The intervals at which, in an alternative for an eventuality of `w₀` holding throughout an
interval abutting `I₀`, a counterpart of the eventuality causes a `B`-eventuality (19iii). -/
def causedTimes (w₀ : W) (I₀ : NonemptyInterval T) : Set (NonemptyInterval T) :=
  {I₁ | ∃ e₁, M.world e₁ = w₀ ∧ HoldsAbutting e₁ I₀ ∧ ∃ w₁ ∈ a.alt w₀ I₀ e₁, ∃ e₂,
    M.world e₂ = w₁ ∧ M.Counterpart e₁ e₂ ∧ ∃ e₃, M.Causes e₂ e₃ ∧ (w₁, I₁, e₃) ∈ B}

/-- *A before B* at `⟨w₀, I₀, e₀⟩` (19) is true if `B` holds in `w₀` after `I₀` (i), false if it
holds in `w₀` at an interval not after `I₀` (ii), and otherwise true iff `I₀` precedes the
earliest interval at which a counterpart in an alternative causes a `B`-eventuality (iii). -/
def before (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧ (¬ ∃ I₂ e, ¬ I₀.Precedes I₂ ∧ (w₀, I₂, e) ∈ B) ∧
    ((∃ I₂ e, I₀.Precedes I₂ ∧ (w₀, I₂, e) ∈ B) ∨
      ∃ s, IsLeast ((·.fst) '' a.causedTimes B w₀ I₀) s ∧ I₀.snd < s)

variable {a A B} {w₀ : W} {I₀ I₁ : NonemptyInterval T} {e₀ : E}

theorem exists_mem_of_mem_causedTimes (h : I₁ ∈ a.causedTimes B w₀ I₀) : ∃ v e, (v, I₁, e) ∈ B :=
  let ⟨_, _, _, w₁, _, _, _, _, e₃, _, hB⟩ := h
  ⟨w₁, e₃, hB⟩

/-- An anti-veridical *before* is false when no eventuality at the main-clause interval could lead
to the temporal clause (14). -/
theorem not_before_of_causedTimes_eq_empty (hB : ∀ I e, (w₀, I, e) ∉ B)
    (h : a.causedTimes B w₀ I₀ = ∅) : ¬ a.before A B w₀ I₀ e₀ := by
  rintro ⟨-, -, ⟨I, e, -, hIe⟩ | ⟨s, ⟨⟨I₁, hI₁, -⟩, -⟩, -⟩⟩
  · exact hB I e hIe
  · exact (h ▸ hI₁ : I₁ ∈ (∅ : Set (NonemptyInterval T)))

/-- A temporal clause confined to intervals ending by `hi` makes *A before B* false at main-clause
intervals starting from `hi` on (§5.1). -/
theorem not_before_of_le {hi : T} (hB : ∀ v I e, (v, I, e) ∈ B → I.snd ≤ hi)
    (hI : hi ≤ I₀.fst) : ¬ a.before A B w₀ I₀ e₀ := by
  have key (I : NonemptyInterval T) (h : ∃ v e, (v, I, e) ∈ B) (hlt : I₀.snd < I.fst) : False :=
    let ⟨v, e, hve⟩ := h
    lt_irrefl _ (hlt.trans_le (I.fst_le_snd.trans ((hB v I e hve).trans (hI.trans I₀.fst_le_snd))))
  rintro ⟨-, -, ⟨I, e, hP, hIe⟩ | ⟨s, ⟨⟨I₁, hI₁, rfl⟩, -⟩, hs⟩⟩
  exacts [key I ⟨w₀, e, hIe⟩ hP, key I₁ (exists_mem_of_mem_causedTimes hI₁) hs]

end Alternatives

/-! ### Mozart (6a)

Mozart works on the Requiem from time `0` and dies at `1`. In a world where his health is better
at `0`, a counterpart of the work runs on until `3` and causes the completion at `2`. The worlds
differ in a fact about time `0`, settled from time `1` on, so the healthier world is no historical
alternative of the actual one at the death, but it is equivalent to it for the work, which began
at `0`. -/

namespace Mozart

/-- The actual world and the world of better health. -/
inductive World where
  | actual
  | healthy
  deriving DecidableEq

/-- The eventualities are the death, the work on the Requiem, its counterpart, and the
completion. -/
inductive Eventuality where
  | death
  | work
  | work'
  | completion
  deriving DecidableEq

instance : Event.TemporalTrace Eventuality ℤ where
  τ
    | .death => .pure 1
    | .work => ⟨(0, 1), by decide⟩
    | .work' => ⟨(0, 3), by decide⟩
    | .completion => .pure 2

/-- The worlds agree on everything but Mozart's health at time `0`, a fact settled from time `1`
on. -/
def history : TWFrame World ℤ := .ofDatedFacts (fun _ : Unit ↦ 1) fun w _ ↦ w = .healthy

/-- The eventualities of the two worlds. -/
def frame : EventFrame World ℤ Eventuality where
  history := history
  world
    | .death | .work => .actual
    | .work' | .completion => .healthy
  Counterpart e e' := e = .work ∧ e' = .work'
  fst_eq := by rintro _ _ ⟨rfl, rfl⟩; rfl
  Causes e e' := e = .work' ∧ e' = .completion

/-- The healthier world is the alternative of the actual one for the work, at intervals ending by
`2`. -/
def alternatives : Alternatives frame where
  alt w I e := {v | w = .actual ∧ e = .work ∧ I.snd ≤ 2 ∧ v = .healthy}
  equiv_of_mem := by
    rintro w I e v ⟨rfl, rfl, hI, rfl⟩
    have := I.fst_le_snd
    refine ⟨rfl, .work', rfl, ⟨rfl, rfl⟩, fun x ⟨h₀, h₁⟩ ↦ ⟨h₀, ?_⟩, fun x ⟨h₀, h₁⟩ ↦ ⟨h₀, ?_⟩,
      fun _ h ↦ ?_⟩
    · change x ≤ 1; omega
    · change x ≤ 3; omega
    · change (1 : ℤ) ≤ 0 at h; omega
  continues := by
    rintro w I e v ⟨rfl, rfl, hI, rfl⟩
    exact ⟨.work', rfl, ⟨rfl, rfl⟩, by change I.snd < 3; omega⟩

/-- *Mozart died*, the death at `1`. -/
def dies : Set (World × NonemptyInterval ℤ × Eventuality) := {(.actual, .pure 1, .death)}

/-- *Mozart finished the Requiem*, the completion at `2` in the healthier world. -/
def finishes : Set (World × NonemptyInterval ℤ × Eventuality) := {(.healthy, .pure 2, .completion)}

/-- The revision makes *Mozart died before he finished the Requiem* (6a) true at the death. -/
theorem before_dies_finishes : alternatives.before dies finishes .actual (.pure 1) .death := by
  refine ⟨rfl, fun ⟨_, _, _, h⟩ ↦ by simp [finishes] at h, .inr ⟨2, ⟨⟨.pure 2, ?_, rfl⟩, ?_⟩, ?_⟩⟩
  · exact ⟨.work, rfl, holdsAbutting_iff.2 (by decide), .healthy, ⟨rfl, rfl, by decide, rfl⟩,
      .work', rfl, ⟨rfl, rfl⟩, .completion, ⟨rfl, rfl⟩, rfl⟩
  · rintro _ ⟨I₁, hI₁, rfl⟩
    obtain ⟨v, e, h⟩ := Alternatives.exists_mem_of_mem_causedTimes hI₁
    simp only [finishes, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rw [h.2.1]
    rfl
  · decide

theorem not_mem_finishes (I : NonemptyInterval ℤ) (e : Eventuality) :
    (World.actual, I, e) ∉ finishes := by
  simp [finishes]

theorem healthy_not_mem_alternatives : World.healthy ∉ history.alternatives (.actual, 1) :=
  fun h ↦ nomatch (h () le_rfl).2 rfl

/-- *Mozart died* and *Mozart finished the Requiem* as Beaver and Condoravdi's clauses, at times. -/
def diesAt : Set (World × ℤ) := {(.actual, 1)}

/-- Mozart's completion of the Requiem at `2` in the healthier world. -/
def finishesAt : Set (World × ℤ) := {(.healthy, 2)}

/-- In the same history Beaver and Condoravdi's *before* makes (6a) false, the death being settled
at its time, whatever their alternatives. -/
theorem not_before_dies_finishes (a : BeaverCondoravdi2003.Alternatives history finishesAt) :
    ¬ BeaverCondoravdi2003.before diesAt finishesAt a.alt .actual := by
  refine not_before_of_settled a (fun t ht ↦ ?_) fun v t t' hv hv' ↦ ?_
  · obtain rfl : t = 1 := (Prod.mk.inj ht).2
    rintro _ rfl v hv
    cases v
    · rfl
    · exact absurd hv healthy_not_mem_alternatives
  · obtain rfl : v = .actual := (Prod.mk.inj hv).1
    simp [finishesAt] at hv'

end Mozart

end Revision

/-! ### The examples -/

/-- The counterexamples of §5.1, (20a)–(20c) and the Japanese (21), are acceptable, though both
analyses make them false in every model, `not_before_of_le` and `Alternatives.not_before_of_le`.
-/
theorem rows_bcCounterexample :
    ∀ r ∈ Examples.all, r.feature? "construction" = some "bc_counterexample" →
      r.judgment = .acceptable := by
  decide

/-- An anti-veridical *before* is acceptable iff an eventuality at its time could lead to its
temporal clause ((6a), (14)). -/
theorem rows_precursor :
    ∀ r ∈ Examples.all, r.feature? "precursor" ≠ none →
      (r.judgment = .acceptable ↔ r.feature? "precursor" = some "true") := by
  decide

/-- The *before*-clause of (21) is non-past under a past, the tense the fragment records for
*mae*. -/
theorem rows_connective_tense :
    ∀ r ∈ Examples.all, ∀ c ∈ r.parse? "connective" [("mae", Japanese.TemporalConnectives.mae)],
      r.parse? "embeddedTense" [("present", Tense.present), ("past", .past)] = c.tense := by
  decide

end OgiharaSteinertThrelkeld2024
