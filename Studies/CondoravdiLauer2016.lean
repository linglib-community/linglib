module

public import Linglib.Semantics.Attitudes.Preference.Structure
public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Semantics.Mood.Defs
public import Linglib.Data.Examples.CondoravdiLauer2016
public import Studies.VonFintelIatridou2005
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Sigma
public import Linglib.Data.Examples.Readers

/-!
# Condoravdi and Lauer 2016: anankastic conditionals are just conditionals

Condoravdi and Lauer argue that *If you want to go to Harlem, you have to take the A train* is
a regular hypothetical indicative conditional: the problem Sæbø found, that the antecedent
goal must enter the ordering of the modal, and the one von Fintel and Iatridou and
von Stechow, Krasikova and Penka added, that conflicting actual goals must not, are both resolved
by the lexical meanings involved once *want* reports an action-relevant preference. On that
reading *want* says its complement is a maximal element of the agent's effective preference
structure, a strict partial order on propositions that is consistent with the agent's beliefs, so
hypothesizing a preference for Harlem hypothesizes the absence of every preference the agent knows
to be incompatible with it. The conditional has the double-modal structure of Frank, a
covert necessity over the speaker's beliefs, ordered by stereotypicality and restricted by the
antecedent, with the priority modal over the historical alternatives in its scope, whose ordering
source at each world is the agent's maximal effective preferences there. The same setting covers
the near-anankastics of strengthened goals, teleological consequences and specializations, which
differ from anankastics only in the pragmatic implication that the temporal relation of goal and
prejacent invites; reading *want* or the modal differently gives the non-anankastic and deontic
cases.

## Implementation notes

* Both modals are Kratzer's `necessity`, as (88) says, the outer one the restrictor conditional,
  which is Kratzer's limit-free necessity and agrees with `necessity` at the best worlds under the
  Limit Assumption, as on every model here. The priority modal's ordering source is
  `orderingSource P a`, the maximal preferences of `P a v` at each world `v`, so an anankastic is
  `conditionalNecessity` with no operator of its own, and Sæbø's rival restricts the same
  ordering source where the paper restricts the outer modal base.
* The effective preferences are taken consistent relative to the historical alternatives, which
  (66) relative to the agent's beliefs gives when those beliefs lie among them; it keeps out the
  atypical continuations the paper leaves to a separate mechanism.
* Each scenario is a small model with its own world type. In the Hoboken scenario the speaker is
  uncertain about the addressee's goal, with an empty stereotypical ordering, so the Harlem
  sentence is true through its antecedent worlds rather than vacuously.

## TODO

* Informal in the paper and not formalized: the temporal interpretation of the internal
  antecedent and the prejacent, the pragmatic derivation of the means-of implication, the
  strong/weak modal contrast of (96) and (97), purpose constructions, informational asymmetry,
  the consistency of the double-modal readings of (81) and (82), and the closure condition that
  would validate conjunction introduction for effective preferences.

## References

* [C. Condoravdi and S. Lauer, *Anankastic conditionals are just conditionals*
  (2016)][condoravdi-lauer-2016]
* [C. Condoravdi and S. Lauer, *Performative verbs and performative acts*
  (2011)][condoravdi-lauer-2011]
* [K. J. Sæbø, *Necessary conditions in a natural language* (2001)][saebo-2001]
* [K. von Fintel and S. Iatridou, *What to do if you want to go to Harlem: Anankastic
  conditionals and related matters* (2005)][von-fintel-iatridou-2005]
* [A. von Stechow, S. Krasikova and D. Penka, *Anankastic conditionals again*
  (2006)][vonstechow-krasikova-penka-2006]
* [J. Huitink, *Modals, conditionals and compositionality* (2008)][huitink-2008]
* [A. Frank, *Context dependence in modal constructions* (1996)][frank-1996]
* [S. Kaufmann and M. Schwager, *A unified analysis of conditional imperatives*
  (2009)][kaufmann-schwager-2009]
* [R. M. Hare, *Wanting: Some pitfalls* (1971)][hare-1971]
* [D. Levinson, *Probabilistic model-theoretic semantics for want* (2003)][levinson-2003]
* [T. E. Zimmermann, *Monotonicity in opaque verbs* (2006)][zimmermann-2006]
* [A. Kratzer, *The notional category of modality* (1981)][kratzer-1981]
-/

@[expose] public section

namespace CondoravdiLauer2016

open Desire.Preferential Modality Conditional.Restrictor

section General

variable {A W : Type*} {P : A → W → PreferenceStructure W} {a : A} {p q : Set W} {w : W}
  {B : W → Set W}

/-! ### The semantics of *want*

`Want P a p w` is (69): `p` is a maximal element of the structure `P a w` that a preferential
background assigns to `a` at `w`, (68); the effective preference structure is the consistent
and realistic one that guides action, (66) and (67), realism derivable from consistency,
`PreferenceStructure.Consistent.realistic`, footnote 30. `WantSufficient` and `WantNecessary`
are the success-oriented and Quine–Hintikka alternatives of (71), after [zimmermann-2006],
downward and upward entailing, `WantSufficient.anti` and `WantNecessary.mono`. The
mere-desire and effective readings that [hare-1971] and [levinson-2003] observe are two
backgrounds for one predicate. -/

-- (71c), §5.5
theorem not_monotone_want [Nontrivial W] :
    ¬ Monotone (Want (fun (_ : Unit) _ ↦ .single {w}) () · w) := fun h ↦
  Set.singleton_ne_univ w (h (Set.subset_univ {w}) ⟨rfl, fun _ _ h ↦ h⟩).1.symm

theorem not_antitone_want [Nontrivial W] :
    ¬ Antitone (Want (fun (_ : Unit) _ ↦ .single Set.univ) () · w) := fun h ↦
  Set.singleton_ne_univ w (h (Set.subset_univ {w}) ⟨rfl, fun _ _ h ↦ h⟩).1

-- (52), (53), §2.3, §5.4
theorem want_both (p q : Set W) :
    Want (fun (_ : Unit) _ ↦ .discrete {p, q}) () p w ∧
      Want (fun (_ : Unit) _ ↦ .discrete {p, q}) () q w := by
  simp [Want]

-- (56), (58), §5.2
theorem no_third_effective {r : Set W} (hC : (P a w).Consistent (B w)) (hp : Want P a p w)
    (hq : Want P a q w) (hr : Want P a r w) : (B w ∩ (p ∩ q ∩ r)).Nonempty :=
  hC.inter_sInter_maxElts_nonempty.mono <| Set.inter_subset_inter_right _ <|
    Set.subset_inter (Set.subset_inter (Set.sInter_subset_of_mem hp) (Set.sInter_subset_of_mem hq))
      (Set.sInter_subset_of_mem hr)

/-- Three unranked preferences over three worlds, pairwise compatible but jointly
inconsistent. -/
def threeWay : PreferenceStructure (Fin 3) :=
  .discrete {{w | w ≠ 2}, {w | w ≠ 0}, {w | w ≠ 1}}

-- footnote 29, (66) [condoravdi-lauer-2011]
theorem threeWay_pairwise_not_consistent :
    (∀ p ∈ threeWay.prefs, ∀ q ∈ threeWay.prefs, (p ∩ q).Nonempty) ∧
      ¬ threeWay.Consistent Set.univ := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) <;> exact Set.nonempty_def.2 (by decide)
  · obtain ⟨_, _, _, _, h⟩ := h threeWay.prefs subset_rfl (by
      ext w
      fin_cases w <;> simp [threeWay, PreferenceStructure.discrete])
    exact h

/-! ### Previous approaches -/

-- (26), §3.2.2, (88), footnote 46 [von-fintel-iatridou-2005]
theorem necessity_designatedGoal_iff_haveTo {f : Background W} {p r : W → Prop}
    (h : ((f.restrict p).accessibleWorlds w).Nonempty) :
    necessity f (fun _ ↦ {p}) r w ↔ VonFintelIatridou2005.haveTo f p r w := by
  have hf : f ⊔ (fun _ ↦ {p}) = f.restrict p := funext fun _ ↦ Set.union_singleton
  rw [VonFintelIatridou2005.haveTo, conditionalNecessity_bot_iff, necessity_iff, necessity_iff,
    bestWorlds_bot, bestWorlds_eq_accessibleWorlds_sup (hf ▸ h), hf]

/-! ### Double-modal structure -/

-- (81), (83), (76b), §6.2 [kaufmann-schwager-2009]
theorem single_modal_strengthening {f g : Background W} {α β γ : W → Prop}
    (h₁ : conditionalNecessity f g α γ w)
    (h₂ : conditionalNecessity f g (fun v ↦ α v ∧ β v) (fun v ↦ ¬ γ v) w) :
    ∀ u ∈ bestWorlds (f.restrict α) g w, ¬ β u := by
  intro u hu hβ
  have hu' := Background.mem_accessibleWorlds_restrict.1 hu.1
  exact necessity_of_conditionalNecessity h₂ u (mem_bestWorlds_of_subset
    (fun v hv ↦ Background.accessibleWorlds_restrict_mono (fun _ h ↦ h.1) hv)
    hu (Background.mem_accessibleWorlds_restrict.2 ⟨hu'.1, hu'.2, hβ⟩))
    (necessity_of_conditionalNecessity h₁ u hu)

/-! ### The analysis -/

/-- On its teleological construal, §7.1, the priority modal is ordered at each world `v` by the
maximal preferences of `P a v`, so that `orderingSource EP a` is the paper's `g_epA`. -/
def orderingSource (P : A → W → PreferenceStructure W) (a : A) : Background W :=
  fun v ↦ (P a v).maxElts

-- §2.3
theorem bestWorlds_orderingSource {f : Background W} {v : W}
    (hC : (P a v).Consistent (f.accessibleWorlds v)) :
    bestWorlds f (orderingSource P a) v = f.accessibleWorlds v ∩ ⋂₀ (P a v).maxElts := by
  have h : (f ⊔ orderingSource P a).accessibleWorlds v =
      f.accessibleWorlds v ∩ ⋂₀ (P a v).maxElts := by
    rw [Background.accessibleWorlds_sup]
    rfl
  rw [bestWorlds_eq_accessibleWorlds_sup (h ▸ hC.inter_sInter_maxElts_nonempty), h]

private theorem mem_bestWorlds_bot_restrict {α : W → Prop} {v : W} (hα : α v) :
    v ∈ bestWorlds ((⊥ : Background W).restrict α) ⊥ w := by
  rw [bestWorlds_bot, Background.mem_accessibleWorlds_restrict]
  exact ⟨by simp, hα⟩

-- (90)
theorem want_disjoint (hC : ∀ w, (P a w).Consistent (B w)) (h : ∀ w, B w ∩ (p ∩ q) = ∅) :
    Disjoint {w | Want P a p w} {w | Want P a q w} :=
  Set.disjoint_left.2 fun w hp hq ↦
    ((hC w).inter_inter_nonempty_of_mem_maxElts hp hq).ne_empty (h w)

-- §7.1.1
theorem not_want_of_mem_restricted {f : Background W} (hC : ∀ w, (P a w).Consistent (B w))
    (h : ∀ w, B w ∩ (p ∩ q) = ∅) {v : W}
    (hv : v ∈ (f.restrict (Want P a p)).accessibleWorlds w) : ¬ Want P a q v :=
  Set.disjoint_left.1 (want_disjoint hC h) (Background.mem_accessibleWorlds_restrict.1 hv).2

/-- Under consistency (66), the conditional (88) holds iff its paraphrase (89) does, and compatible
goals such as comfort in (92) remain. -/
theorem conditionalNecessity_orderingSource_iff {f₁ g₁ f₂ : Background W} {α : W → Prop}
    (hC : ∀ v ∈ bestWorlds (f₁.restrict α) g₁ w, (P a v).Consistent (f₂.accessibleWorlds v))
    (hlim : LimitAssumption (f₁.restrict α) g₁ w) :
    conditionalNecessity f₁ g₁ α (necessity f₂ (orderingSource P a) (· ∈ q)) w ↔
      ∀ v ∈ bestWorlds (f₁.restrict α) g₁ w, f₂.accessibleWorlds v ∩ ⋂₀ (P a v).maxElts ⊆ q := by
  simp only [conditionalNecessity_iff_necessity hlim, necessity_iff]
  refine forall₂_congr fun v hv ↦ ?_
  rw [bestWorlds_orderingSource (hC v hv)]
  rfl

end General

/-! ### The Hoboken scenario

Von Fintel and Iatridou's stranger on the platform, §2.3 and §7.1.1: the speaker knows the
facts about the trains but not the addressee's goal, which is Hoboken. -/

namespace HobokenScenario

/-- Where the addressee wants to go. -/
inductive Goal
  | harlem | hoboken
  deriving DecidableEq

/-- The two trains. -/
inductive Train
  | aTrain | path
  deriving DecidableEq

/-- A world records the addressee's goal, the train taken, and which train goes to Harlem, the
other going to Hoboken. -/
structure World where
  /-- The addressee's effective goal. -/
  goal : Goal
  /-- The train the addressee takes. -/
  train : Train
  /-- The train that goes to Harlem. -/
  harlemTrain : Train
  deriving DecidableEq

variable {w : World}

/-- The addressee goes to Harlem. -/
def harlem : Set World := {w | w.train = w.harlemTrain}

/-- The addressee goes to Hoboken. -/
def hoboken : Set World := {w | w.train ≠ w.harlemTrain}

/-- The addressee takes the A train. -/
def aTrain : Set World := {w | w.train = .aTrain}

/-- The addressee takes the PATH train. -/
def path : Set World := {w | w.train = .path}

/-- The proposition a goal is a preference for. -/
def Goal.dest : Goal → Set World
  | .harlem => HobokenScenario.harlem
  | .hoboken => HobokenScenario.hoboken

/-- The addressee's effective preference structure is the single preference for the goal. -/
def ep (_ : Unit) (w : World) : PreferenceStructure World := .single w.goal.dest

/-- The addressee's mere desires are both destinations, unranked, at every world. -/
def desire (_ : Unit) (_ : World) : PreferenceStructure World := .discrete {harlem, hoboken}

/-- The speaker believes that the A train goes to Harlem. -/
def fBelS : Background World := fun _ ↦ {fun v ↦ v.harlemTrain = .aTrain}

/-- In the historical alternatives before boarding the goal and the routes are settled and the
train is not. -/
def fHist : Background World :=
  fun v ↦ {fun u ↦ u.goal = v.goal, fun u ↦ u.harlemTrain = v.harlemTrain}

/-- The world where the A train goes to Harlem and the addressee, heading for Hoboken, takes the
PATH train. -/
def w₀ : World := ⟨.hoboken, .path, .aTrain⟩

private theorem mem_fBelS {v : World} :
    v ∈ fBelS.accessibleWorlds w ↔ v.harlemTrain = .aTrain := by
  simp [fBelS]

private theorem mem_fHist {u v : World} :
    u ∈ fHist.accessibleWorlds v ↔ u.goal = v.goal ∧ u.harlemTrain = v.harlemTrain := by
  simp [fHist]

theorem consistent_ep (v : World) : (ep () v).Consistent (fHist.accessibleWorlds v) := by
  refine PreferenceStructure.consistent_single ?_
  obtain ⟨g, t, h⟩ := v
  cases g <;> cases h
  exacts [⟨⟨.harlem, .aTrain, .aTrain⟩, rfl, mem_fHist.2 ⟨rfl, rfl⟩⟩,
    ⟨⟨.harlem, .path, .path⟩, rfl, mem_fHist.2 ⟨rfl, rfl⟩⟩,
    ⟨⟨.hoboken, .path, .aTrain⟩, nofun, mem_fHist.2 ⟨rfl, rfl⟩⟩,
    ⟨⟨.hoboken, .aTrain, .path⟩, nofun, mem_fHist.2 ⟨rfl, rfl⟩⟩]

theorem bestWorlds_fHist (v : World) :
    bestWorlds fHist (orderingSource ep ()) v = fHist.accessibleWorlds v ∩ v.goal.dest := by
  rw [bestWorlds_orderingSource (consistent_ep v)]
  simp [ep]

theorem harlem_inter_hoboken : harlem ∩ hoboken = ∅ := by
  ext
  simp [harlem, hoboken]

-- (90), §7.1.1
theorem w₀_excluded :
    w₀ ∈ fBelS.accessibleWorlds w₀ ∧
      w₀ ∉ (fBelS.restrict (Want ep () harlem)).accessibleWorlds w₀ :=
  ⟨mem_fBelS.2 rfl, fun h ↦ not_want_of_mem_restricted (q := hoboken) consistent_ep
    (fun _ ↦ by rw [harlem_inter_hoboken, Set.inter_empty]) h ⟨rfl, fun _ _ h ↦ h⟩⟩

private theorem mem_bestWorlds_fBelS {α : World → Prop} {v : World}
    (hv : v.harlemTrain = .aTrain) (hα : α v) : v ∈ bestWorlds (fBelS.restrict α) ⊥ w := by
  rw [bestWorlds_bot, Background.mem_accessibleWorlds_restrict]
  exact ⟨mem_fBelS.2 hv, hα⟩

private theorem anankastic_dest {d t : Set World}
    (hd : ∀ u : World, u.harlemTrain = .aTrain → (u ∈ d ↔ u ∈ t)) :
    conditionalNecessity fBelS ⊥ (Want ep () d) (necessity fHist (orderingSource ep ()) (· ∈ t))
      w := by
  refine (conditionalNecessity_orderingSource_iff (fun v _ ↦ consistent_ep v) (.bot _ _)).2
    fun v hv u ⟨hu, hdu⟩ ↦ ?_
  have hv' := Background.mem_accessibleWorlds_restrict.1 hv.1
  exact (hd u ((mem_fHist.1 hu).2.trans (mem_fBelS.1 hv'.1))).1 (hdu d hv'.2)

/-- The Harlem sentence (1) is true at every world, the Hoboken world included, §7.1.1. -/
theorem anankastic_harlem :
    conditionalNecessity fBelS ⊥ (Want ep () harlem)
      (necessity fHist (orderingSource ep ()) (· ∈ aTrain)) w :=
  anankastic_dest fun u hu ↦ by simp [harlem, aTrain, hu]

-- (15)
theorem anankastic_hoboken :
    conditionalNecessity fBelS ⊥ (Want ep () hoboken)
      (necessity fHist (orderingSource ep ()) (· ∈ path)) w :=
  anankastic_dest fun ⟨_, t, _⟩ hu ↦ by cases t <;> simp_all [hoboken, path]

/-- The conditional (14), *if you want to go to Harlem, you can take the PATH train*, is false at
every world (§2.3). -/
theorem not_possibility_path :
    ¬ conditionalNecessity fBelS ⊥ (Want ep () harlem)
      (possibility fHist (orderingSource ep ()) (· ∈ path)) w := fun h ↦ by
  obtain ⟨u, hu, hpath⟩ := necessity_of_conditionalNecessity h ⟨.harlem, .aTrain, .aTrain⟩
    (mem_bestWorlds_fBelS rfl ⟨rfl, fun _ _ h ↦ h⟩)
  rw [mem_bestAccessible, bestWorlds_fHist] at hu
  have := (mem_fHist.1 hu.1).2
  simp_all [Goal.dest, harlem, path]

-- (105), §7.2.1
theorem not_anankastic_desire :
    ¬ conditionalNecessity fBelS ⊥ (Want desire () harlem)
      (necessity fHist (orderingSource ep ()) (· ∈ aTrain)) w₀ := fun h ↦
  nomatch necessity_of_conditionalNecessity h w₀
    (mem_bestWorlds_fBelS rfl ⟨.inl rfl, fun _ _ h ↦ h⟩) w₀
    (by rw [mem_bestAccessible, bestWorlds_fHist]; exact ⟨mem_fHist.2 ⟨rfl, rfl⟩, nofun⟩)

private theorem w₀_mem_bestWorlds : w₀ ∈ bestWorlds fBelS (orderingSource ep ()) w₀ := by
  rw [bestWorlds_orderingSource
    ((consistent_ep w₀).mono fun _ hu ↦ mem_fBelS.2 (mem_fHist.1 hu).2)]
  exact ⟨mem_fBelS.2 rfl, by simp [ep, w₀]; exact nofun⟩

-- §2.3
theorem saebo_harlem :
    ¬ necessity fBelS ((orderingSource ep ()).restrict (· ∈ harlem)) (· ∈ aTrain) w₀ :=
  not_necessity_insert (q := (· ∈ hoboken)) ⟨rfl, fun _ _ h ↦ h⟩
    (fun _ h h' ↦ h h') w₀_mem_bestWorlds nofun nofun

-- (14)
theorem saebo_path :
    possibility fBelS ((orderingSource ep ()).restrict (· ∈ harlem)) (· ∈ path) w₀ :=
  ⟨w₀, mem_bestWorlds_insert (q := (· ∈ hoboken)) ⟨rfl, fun _ _ h ↦ h⟩
    (fun _ h h' ↦ h h') w₀_mem_bestWorlds nofun, rfl⟩

end HobokenScenario

/-! ### Compatible goals and their ranking

Von Stechow, Krasikova and Penka's two trains to Vladivostok, (92): the Chinese train is the more
comfortable and here also the dearer. Going, comfort and economy are pairwise compatible but not
jointly realizable, so by (66) an effective structure ranks comfort and cost, and the ranking
decides whether *you have to take the Chinese train* is true, §7.1.1. -/

namespace VladivostokScenario

/-- What the addressee does. -/
inductive World
  | russian | chinese | home
  deriving DecidableEq

variable {w : World}

/-- The addressee goes to Vladivostok. -/
def vladivostok : Set World := {w | w ≠ .home}

/-- The addressee does not ride the uncomfortable Russian train. -/
def comfort : Set World := {w | w ≠ .russian}

/-- The addressee does not pay for the Chinese train. -/
def cheap : Set World := {w | w ≠ .chinese}

/-- The addressee takes the Chinese train. -/
def takeChinese : Set World := {.chinese}

/-- The addressee takes the Russian train. -/
def takeRussian : Set World := {.russian}

theorem vladivostok_ne_comfort : vladivostok ≠ comfort :=
  fun h ↦ (Set.ext_iff.1 h .home).2 nofun rfl

theorem vladivostok_ne_cheap : vladivostok ≠ cheap :=
  fun h ↦ (Set.ext_iff.1 h .home).2 nofun rfl

theorem comfort_ne_cheap : comfort ≠ cheap :=
  fun h ↦ (Set.ext_iff.1 h .russian).2 nofun rfl

/-- The addressee's preferences. -/
def prefs : Set (Set World) := {vladivostok, comfort, cheap}

theorem not_consistent_discrete : ¬ (PreferenceStructure.discrete prefs).Consistent Set.univ :=
  fun h ↦ by
    obtain ⟨u, -, hu⟩ := h.inter_sInter_maxElts_nonempty
    rw [PreferenceStructure.maxElts_discrete] at hu
    have h₁ : u ∈ vladivostok := hu _ (.inl rfl)
    have h₂ : u ∈ comfort := hu _ (.inr (.inl rfl))
    have h₃ : u ∈ cheap := hu _ (.inr (.inr rfl))
    cases u <;> simp_all [vladivostok, comfort, cheap]

/-- The effective preferences when comfort outranks cost. -/
def comfortFirst (_ : Unit) (_ : World) : PreferenceStructure World :=
  .rankBelow prefs comfort_ne_cheap.symm

/-- The effective preferences when cost outranks comfort, which is then a mere desire. -/
def costFirst (_ : Unit) (_ : World) : PreferenceStructure World :=
  .rankBelow prefs comfort_ne_cheap

private theorem maxElts_comfortFirst : (comfortFirst () w).maxElts = prefs \ {cheap} :=
  PreferenceStructure.maxElts_rankBelow _ (show comfort ∈ prefs from .inr (.inl rfl))

private theorem maxElts_costFirst : (costFirst () w).maxElts = prefs \ {comfort} :=
  PreferenceStructure.maxElts_rankBelow _ (show cheap ∈ prefs from .inr (.inr rfl))

private theorem chinese_mem : World.chinese ∈ ⋂₀ (prefs \ {cheap}) := by
  rintro _ ⟨ht | ht | ht, htc⟩
  exacts [ht ▸ nofun, ht ▸ nofun, absurd ht htc]

private theorem russian_mem : World.russian ∈ ⋂₀ (prefs \ {comfort}) := by
  rintro _ ⟨ht | ht | ht, htc⟩
  exacts [ht ▸ nofun, absurd ht htc, ht ▸ nofun]

private theorem consistent_comfortFirst (v : World) :
    (comfortFirst () w).Consistent ((⊥ : Background World).accessibleWorlds v) := by
  rw [Background.accessibleWorlds_bot]
  exact PreferenceStructure.consistent_rankBelow _ ⟨_, trivial, chinese_mem⟩
    ⟨_, trivial, russian_mem⟩

private theorem consistent_costFirst (v : World) :
    (costFirst () w).Consistent ((⊥ : Background World).accessibleWorlds v) := by
  rw [Background.accessibleWorlds_bot]
  exact PreferenceStructure.consistent_rankBelow _ ⟨_, trivial, russian_mem⟩
    ⟨_, trivial, chinese_mem⟩

/-- With comfort ranked over cost, (92) is true: the only comfortable way to Vladivostok is the
Chinese train. -/
theorem haveTo_chinese_comfortFirst :
    conditionalNecessity ⊥ ⊥ (Want comfortFirst () vladivostok)
      (necessity ⊥ (orderingSource comfortFirst ()) (· ∈ takeChinese)) w := by
  refine (conditionalNecessity_orderingSource_iff (fun v _ ↦ consistent_comfortFirst v)
    (.bot _ _)).2
    fun _ _ u ⟨_, hu⟩ ↦ ?_
  rw [maxElts_comfortFirst] at hu
  have h₁ : u ∈ vladivostok := hu _ ⟨.inl rfl, vladivostok_ne_cheap⟩
  have h₂ : u ∈ comfort := hu _ ⟨.inr (.inl rfl), comfort_ne_cheap⟩
  cases u <;> simp_all [vladivostok, comfort, takeChinese]

theorem haveTo_russian_costFirst :
    conditionalNecessity ⊥ ⊥ (Want costFirst () vladivostok)
      (necessity ⊥ (orderingSource costFirst ()) (· ∈ takeRussian)) w := by
  refine (conditionalNecessity_orderingSource_iff (fun v _ ↦ consistent_costFirst v) (.bot _ _)).2
    fun _ _ u ⟨_, hu⟩ ↦ ?_
  rw [maxElts_costFirst] at hu
  have h₁ : u ∈ vladivostok := hu _ ⟨.inl rfl, vladivostok_ne_comfort⟩
  have h₃ : u ∈ cheap := hu _ ⟨.inr (.inr rfl), comfort_ne_cheap.symm⟩
  cases u <;> simp_all [vladivostok, cheap, takeRussian]

-- (92), §7.1.1
theorem not_haveTo_chinese_costFirst :
    ¬ conditionalNecessity ⊥ ⊥ (Want costFirst () vladivostok)
      (necessity ⊥ (orderingSource costFirst ()) (· ∈ takeChinese)) w := fun h ↦ by
  have hw : Want costFirst () vladivostok w := by
    rw [Want, maxElts_costFirst]
    exact ⟨.inl rfl, vladivostok_ne_comfort⟩
  have := (conditionalNecessity_orderingSource_iff (fun v _ ↦ consistent_costFirst v)
    (.bot _ _)).1 h w
    (mem_bestWorlds_bot_restrict hw) ⟨by simp, maxElts_costFirst (w := w) ▸ russian_mem⟩
  exact nomatch this

end VladivostokScenario

/-! ### Strengthened goals

The near-anankastic (29b), *if you want to travel to that place, you should get a vaccine*, §4.1
and §7.1.2: the vaccine is not a precondition for travelling, but with being safe a second maximal
effective preference beside travelling, the analysis of (88) makes the conditional true. -/

namespace VaccineScenario

/-- Whether the addressee travels there. -/
inductive Trip
  | go | stay
  deriving DecidableEq

/-- Whether the addressee gets the vaccine. -/
inductive Shot
  | vaccine | none
  deriving DecidableEq

/-- A world records the trip and the shot. -/
structure World where
  /-- Whether the addressee travels. -/
  trip : Trip
  /-- Whether the addressee is vaccinated. -/
  shot : Shot
  deriving DecidableEq

variable {w : World}

/-- The addressee travels to that place. -/
def travel : Set World := {w | w.trip = .go}

/-- The addressee is safe, never travelling unvaccinated. -/
def safe : Set World := {w | w.trip = .go → w.shot = .vaccine}

/-- The addressee gets the vaccine. -/
def vaccinated : Set World := {w | w.shot = .vaccine}

/-- The addressee effectively prefers both to travel and to be safe, unranked. -/
def ep (_ : Unit) (_ : World) : PreferenceStructure World := .discrete {travel, safe}

/-- Travelling as the only maximal preference, the strong construal of the antecedent in
[huitink-2008] that a singleton `max` would derive, footnote 31. -/
def strong (_ : Unit) (_ : World) : PreferenceStructure World := .single travel

/-- (29b) is true: every continuation realizing both preferences is vaccinated. -/
theorem should_vaccine :
    conditionalNecessity ⊥ ⊥ (Want ep () travel)
      (necessity ⊥ (orderingSource ep ()) (· ∈ vaccinated)) w := by
  refine (conditionalNecessity_orderingSource_iff (fun _ _ ↦
    PreferenceStructure.consistent_discrete ⟨⟨.go, .vaccine⟩, by simp, ?_⟩) (.bot _ _)).2
      fun _ _ u ⟨_, hu⟩ ↦ ?_
  · rintro _ (rfl | rfl)
    exacts [rfl, fun _ ↦ rfl]
  · exact (hu safe ⟨.inr rfl, fun _ _ h ↦ h⟩) (hu travel ⟨.inl rfl, fun _ _ h ↦ h⟩)

-- (29b)
theorem not_should_vaccine_strong :
    ¬ conditionalNecessity ⊥ ⊥ (Want strong () travel)
      (necessity ⊥ (orderingSource strong ()) (· ∈ vaccinated)) w := fun h ↦
  nomatch necessity_of_conditionalNecessity h w
    (mem_bestWorlds_bot_restrict (α := Want strong () travel) ⟨rfl, fun _ _ h ↦ h⟩)
    ⟨.go, .none⟩
    (by
      rw [mem_bestAccessible, bestWorlds_orderingSource
        (PreferenceStructure.consistent_single (p := travel)
          (B := (⊥ : Background World).accessibleWorlds w) ⟨⟨.go, .none⟩, rfl, by simp⟩)]
      exact ⟨by simp, by simp [strong, travel]⟩)

end VaccineScenario

/-! ### The double-modal structure at work

The airport sequence (83) of §6.2, where getting a ride is the preferred way and the speaker will
not drive while the trains run on time. On the double-modal structure both conditionals are true,
the outer modal evaluating (83a) in typical worlds without track repairs; a single modal ordered
by the addressee's goals cannot make both true. The addressee's preference for a ride is left out,
since the single-modal readings conflict without it. -/

namespace AirportScenario

/-- Whether there is repair work on the tracks. -/
inductive Tracks
  | clear | repairs
  deriving DecidableEq, Fintype

/-- How the addressee gets to the airport. -/
inductive Way
  | train | ride | stay
  deriving DecidableEq, Fintype

/-- A world records the state of the tracks and the way the addressee goes. -/
structure World where
  /-- The state of the tracks. -/
  tracks : Tracks
  /-- The way the addressee goes. -/
  way : Way
  deriving DecidableEq, Fintype

variable {w : World}

/-- The addressee gets to the airport by noon, by a ride or by train on clear tracks. -/
def noon : Set World := {w | w.way = .ride ∨ w.way = .train ∧ w.tracks = .clear}

/-- The addressee takes the train. -/
def byTrain : Set World := {w | w.way = .train}

/-- The speaker gives the addressee a ride. -/
def byRide : Set World := {w | w.way = .ride}

/-- There is repair work on the tracks. -/
def repairs : Set World := {w | w.tracks = .repairs}

/-- The addressee's effective preference is to get to the airport by noon. -/
def ep (_ : Unit) (_ : World) : PreferenceStructure World := .single noon

/-- The stereotypical ordering source, by which the trains typically run on time. -/
def gNorm : Background World := fun _ ↦ {fun v ↦ v.tracks = .clear}

/-- In the historical alternatives the state of the tracks is settled, and the speaker gives no
ride while the trains run on time. -/
def fHist : Background World :=
  fun v ↦ {fun u ↦ u.tracks = v.tracks, fun u ↦ u.tracks = .clear → u.way ≠ .ride}

private theorem mem_fHist {u v : World} :
    u ∈ fHist.accessibleWorlds v ↔ u.tracks = v.tracks ∧ (u.tracks = .clear → u.way ≠ .ride) := by
  simp [fHist]

private theorem consistent_ep (v : World) : (ep () v).Consistent (fHist.accessibleWorlds v) := by
  refine PreferenceStructure.consistent_single ?_
  obtain ⟨t, _⟩ := v
  cases t
  exacts [⟨⟨.clear, .train⟩, .inr ⟨rfl, rfl⟩, mem_fHist.2 ⟨rfl, nofun⟩⟩,
    ⟨⟨.repairs, .ride⟩, .inl rfl, mem_fHist.2 ⟨rfl, nofun⟩⟩]

/-- The conditional (83a) is true, since in the typical worlds the train is the only way to be there
by noon. -/
theorem should_train :
    conditionalNecessity ⊥ gNorm (Want ep () noon)
      (necessity fHist (orderingSource ep ()) (· ∈ byTrain)) w := by
  refine (conditionalNecessity_orderingSource_iff (fun v _ ↦ consistent_ep v) (.of_finite _ _ _)).2
    fun v hv u ⟨hu, hn⟩ ↦ ?_
  have hc : ((((⊥ : Background World).restrict (Want ep () noon)) ⊔ gNorm).accessibleWorlds
      w).Nonempty := by
    refine ⟨⟨.clear, .train⟩, ?_⟩
    rw [Background.accessibleWorlds_sup]
    exact ⟨Background.mem_accessibleWorlds_restrict.2 ⟨by simp, rfl, fun _ _ h ↦ h⟩,
      fun _ hp ↦ by rw [Set.mem_singleton_iff.1 hp]⟩
  rw [bestWorlds_eq_accessibleWorlds_sup hc, Background.accessibleWorlds_sup] at hv
  obtain ⟨ht, hr⟩ := mem_fHist.1 hu
  rcases hn noon ⟨rfl, fun _ _ h ↦ h⟩ with h | ⟨h, -⟩
  · exact absurd h (hr (ht.trans (hv.2 _ rfl)))
  · exact h

/-- (83b) is true: with repairs on the tracks only a ride gets the addressee there by noon. -/
theorem should_ride :
    conditionalNecessity ⊥ gNorm (fun v ↦ Want ep () noon v ∧ v ∈ repairs)
      (necessity fHist (orderingSource ep ()) (· ∈ byRide)) w := by
  refine (conditionalNecessity_orderingSource_iff (fun v _ ↦ consistent_ep v) (.of_finite _ _ _)).2
    fun v hv u ⟨hu, hn⟩ ↦ ?_
  have hvr : v.tracks = .repairs := (Background.mem_accessibleWorlds_restrict.1 hv.1).2.2
  rcases hn noon ⟨rfl, fun _ _ h ↦ h⟩ with h | ⟨-, h⟩
  · exact h
  · exact nomatch h.symm.trans ((mem_fHist.1 hu).1.trans hvr)

-- (83a), (83b)
theorem not_single_modal :
    ¬ (conditionalNecessity ⊥ (orderingSource ep ()) (Want ep () noon) (· ∈ byTrain) w ∧
      conditionalNecessity ⊥ (orderingSource ep ()) (fun v ↦ Want ep () noon v ∧ v ∈ repairs)
        (· ∈ byRide) w) := fun ⟨h₁, h₂⟩ ↦ by
  refine single_modal_strengthening h₁
    (Filter.mem_of_superset h₂ fun _ hr ht ↦ nomatch hr.symm.trans ht)
    ⟨.repairs, .ride⟩ ?_ rfl
  rw [bestWorlds_orderingSource
    (PreferenceStructure.consistent_single ⟨⟨.repairs, .ride⟩, .inl rfl,
      Background.mem_accessibleWorlds_restrict.2 ⟨by simp, rfl, fun _ _ h ↦ h⟩⟩)]
  exact ⟨Background.mem_accessibleWorlds_restrict.2 ⟨by simp, rfl, fun _ _ h ↦ h⟩,
    fun _ ht ↦ ht.1 ▸ .inl rfl⟩

end AirportScenario

/-! ### The rows

The construal rows classify the paper's conditionals by the reading of *want* and the construal
of the modal; the other rows instantiate the theorems above. -/

/-- The reading of the desire predicate. -/
inductive WantReading
  | effective | mere | weak
  deriving DecidableEq

/-- The construal of the modal in the consequent. -/
inductive ModalConstrual
  | teleological | deontic | speakerTeleological
  deriving DecidableEq

/-- The interpretation the paper assigns. -/
inductive Interpretation
  | anankastic | nearAnankastic | nonAnankastic
  deriving DecidableEq

/-- The relation the prejacent bears to the goal, §7.1.2, is a means to it, a precondition for it,
a means to a strengthened goal, a consequence of it, a specialization of it, or none. -/
inductive Implication
  | means | precondition | strengthenedGoal | consequence | specialization | none
  deriving DecidableEq

/-- The implications a purpose or conditional row may record. -/
def implications : List (String × Implication) :=
  [("means", .means), ("precondition", .precondition), ("strengthenedGoal", .strengthenedGoal),
    ("consequence", .consequence), ("specialization", .specialization), ("none", .none)]

/-- A construal row. -/
structure Construal where
  /-- The reading of *want*. -/
  want : WantReading
  /-- The construal of the modal. -/
  modal : ModalConstrual
  /-- The interpretation. -/
  interpretation : Interpretation
  /-- The implication. -/
  implication : Implication

/-- The configuration a construal row records. -/
def Construal.ofRow (row : Datum) : Option Construal := do
  guard (row.feature? "construction" = some "construal")
  return ⟨← row.parse? "want"
      [("effective", WantReading.effective), ("mere", .mere), ("weak", .weak)],
    ← row.parse? "modal" [("teleological", ModalConstrual.teleological), ("deontic", .deontic),
      ("speakerTeleological", .speakerTeleological)],
    ← row.parse? "interpretation" [("anankastic", Interpretation.anankastic),
      ("nearAnankastic", .nearAnankastic), ("nonAnankastic", .nonAnankastic)],
    ← row.parse? "implication" implications⟩

-- (88), §7.2.1
theorem anankastic_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "construal" →
    ∃ c ∈ Construal.ofRow row,
      (c.interpretation = .anankastic → c.want = .effective ∧ c.modal = .teleological) := by
  decide

-- §4, §7.1.2
theorem implication_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "construal" →
    ∃ c ∈ Construal.ofRow row, c.want = .effective → c.modal = .teleological →
      (c.interpretation = .anankastic ↔
        c.implication = .means ∨ c.implication = .precondition) := by
  decide

/-- The reading of *want* an incompatible-wants row records. -/
def WantReading.ofRow (row : Datum) : Option WantReading := do
  guard (row.feature? "construction" = some "incompatibleWants")
  row.parse? "construal" [("mere", WantReading.mere), ("effective", .effective)]

-- (52), (55)
theorem incompatible_rows : ∀ row ∈ Examples.all,
    row.feature? "construction" = some "incompatibleWants" →
    ∃ r ∈ WantReading.ofRow row, (row.JudgedFelicitous ↔ r = .mere) := by
  decide

/-- The mood a row records for a conditional whose antecedent the speaker has just excluded. -/
def moodOfRow (row : Datum) : Option Mood.Grammatical := do
  guard (row.feature? "construction" = some "mood")
  row.parse? "mood" [("indicative", Mood.Grammatical.indicative), ("subjunctive", .subjunctive)]

-- (91), (98)
theorem mood_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "mood" →
    ∃ m ∈ moodOfRow row, (row.judgment = .acceptable ↔ m = .subjunctive) := by
  decide

/-- The implication a purpose row records. -/
def Implication.ofRow (row : Datum) : Option Implication := do
  guard (row.feature? "construction" = some "purpose")
  row.parse? "implication" implications

-- §7.1.3
theorem purpose_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "purpose" →
    ∃ i ∈ Implication.ofRow row,
      (row.judgment = .acceptable ↔ i = .means ∨ i = .precondition) := by
  decide

end CondoravdiLauer2016
