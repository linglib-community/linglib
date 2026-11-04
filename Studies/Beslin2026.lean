/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.Merchant2013
public import Linglib.Data.Examples.AnandHardtMcCloskey2025
public import Linglib.Data.Examples.Beslin2026
public import Linglib.Data.Examples.Languages
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Minimalist.Verbal.LittleV

/-!
# Bešlin (2026): Apparent voice mismatches in K'iche' ellipsis

The antecedent of a TP ellipsis in K'iche' can contain an antipassive where the elided verb must be
active transitive. Bešlin analyses the antipassive as the active without an internal argument, so
that [it lacks features of the transitive where the Kaqchikel antipassive
clashes](##antipassive_split), and concludes that identity on ellipsis must be nondistinctness, the
absence of a feature clash, which [predicts the judgments](##rows_predicted) as [no equivalence
relation does, on any domain](##not_forall_licit_of_equivalence). With the stranded prepositions of
Anand, Hardt and McCloskey the judgments [fix the domain](##rows_predicted_on_iff), which reaches
Voice and stops below T. Nondistinctness [rules out nothing exactly when every feature is
privative](##forall_nondistinct_iff_subsingleton).

## Implementation notes

* (49d) as printed compares all the material in the ellipsis site. The condition here compares only
  the argument domain of [anand-hardt-mccloskey-2025], which their stranded prepositions require.

## Errata

* P. 27 takes (65) as causativization, but its source, [burukina-polinsky-2025] footnote 14, gives
  it as no causative.
* P. 25 needs a clash between [v:TV] and [v:ITV] only for (53), which that source did not replicate
  (its p. 717); its own selection, read privatively, [has none](##antipassive_split).
* Misprints: (11) lacks the star p. 6 implies, footnote 2 reverses its direction, p. 25 prints vITV
  for vTV, (12) glosses 'I' as ABS3SG, and (53) glosses 'sell' as 'buy'.

## TODO

* Merchant's *plain* in (40b), (41b) and (45a) should reduce to the root clause, as (48b) does.
* The Case clause of (49b).

## References

* [beslin-2026]
* [ranero-2021]
* [burukina-polinsky-2025]
* [anand-hardt-mccloskey-2025]
-/

@[expose] public section

namespace Beslin2026

open Minimalist Minimalist.Ellipsis ClauseSpine Minimalist.Voice
open DistributedMorphology (Root)

/-! ### Structures -/

/-- The selection of the [v:TV] of (57b), S:V in the Table 3 of [burukina-polinsky-2025]. The paper
reads it as a value, where the K'iche' [D] is the same difference in selection read privatively. -/
def vTV : SelStack := [.V]

/-- The selection of the [v:ITV] of (57a), S:V,N. -/
def vITV : SelStack := [.V, .N]

/-- The root of the preposition of (47), (48) and [anand-hardt-mccloskey-2025]. The paper does not
say that *to* is a root, but (49d) needs it to be for (48b): an extra functional head is no clash.
-/
def preposition : Root := ⟨0⟩

/-- A verbal structure. A head it lacks has the empty bundle. -/
structure Verb where
  /-- The Voice head, `⊥` if the structure projects none. -/
  voice : WithBot Head := ⊥
  /-- The event structure of v, where the structure records it. -/
  events : Flat (List LittleV) := ⊥
  /-- The selection of v, read as a value. -/
  selection : Flat SelStack := ⊥
  /-- The selectional [D] of v. -/
  d : Flat Unit := ⊥
  /-- The roots in situ beside the verb. Having none differs from having one, the second clause of
  (49d), and a movement tail leaves them unspecified, so a tail matches anything. -/
  roots : Flat (List Root) := ↑([] : List Root)
  /-- The roots in an adjunct of VoiceP. -/
  high : Flat (List Root) := ↑([] : List Root)
  deriving DecidableEq

/-- The feature bundle of a site, one part per kind of head: a Voice head, the features of a v, and
the roots. -/
abbrev Bundle :=
  WithBot Head × (Flat (List LittleV) × Flat SelStack × Flat Unit) × Flat (List Root)

namespace Verb

/-- The bundle a structure gives each site. A head it lacks has the empty bundle. -/
def content (σ : Verb) : Site → Bundle
  | .head .Voice => (σ.voice, ⊥, ⊥)
  | .head .v => (⊥, (σ.events, σ.selection, σ.d), ⊥)
  | .head .V => (⊥, ⊥, σ.roots)
  | .adjunct .Voice => (⊥, ⊥, σ.high)
  | _ => ⊥

/-- The v of the structure selects an internal argument: [D] in K'iche' (43b), [v:TV] in Kaqchikel
(57b). It is read only for a remnant in the role P; the [D] of (72b) selects an external argument.
-/
def SelectsObject (σ : Verb) : Prop := σ.d = ↑() ∨ σ.selection = ↑vTV

instance (σ : Verb) : Decidable σ.SelectsObject := inferInstanceAs (Decidable (_ ∨ _))

end Verb

/-- Active Voice with the [ERG] that licenses ergative case on the external argument. -/
def voiceErg : Head := { agentive with features := .single .case .erg }

/-- The K'iche' antipassive (43a): active Voice, and a v without [D]. -/
def kicheAntipassive : Verb := { voice := agentive }

/-- The K'iche' active transitive (43b): active Voice with [ERG], and a v with [D]. -/
def kicheTransitive : Verb := { voice := voiceErg, d := ↑() }

/-- K'iche' agent focus, without Voice as footnote 4 suggests. -/
def kicheAgentFocus : Verb := { d := ↑() }

/-- A K'iche' passive, which the paper does not draw, with the v of the transitive. -/
def kichePassive : Verb := { voice := passive, d := ↑() }

/-- An inherent intransitive, a small vP. -/
def intransitive : Verb := {}

/-- The Kaqchikel antipassive (57a), a small vP with [v:ITV]. -/
def kaqchikelAntipassive : Verb := { selection := ↑vITV }

/-- The Kaqchikel active transitive (57b), which prints Voice[ERG] alone: given the ACT of (56b) and
the [D] of (43), and [v:TV]. -/
def kaqchikelTransitive : Verb := { voice := voiceErg, selection := ↑vTV }

/-- Kaqchikel agent focus: no Voice ([ranero-2021]), and a v that can only be [v:TV] or unspecified
(`selection_le_of_nondistinct`). -/
def kaqchikelAgentFocus : Verb := { selection := ↑vTV }

/-- A Kaqchikel passive. -/
def kaqchikelPassive : Verb := { voice := passive, selection := ↑vTV }

/-- An active transitive of English, Italian or BCS. -/
def active : Verb := { voice := agentive, d := ↑() }

/-- *ate* in (46), on the assumption p. 18 grants conditionally, that it has no internal argument.
-/
def activeIntransitive : Verb := { voice := agentive }

/-- An active transitive with a preposition in situ. -/
def activeTo : Verb := { active with roots := ↑[preposition] }

/-- An active transitive with a preposition in a movement tail. -/
def activeTail : Verb := { active with roots := ⊥ }

/-- An active transitive with a preposition in situ in an adjunct of VoiceP. -/
def activeHigh : Verb := { active with high := ↑[preposition] }

/-- An English passive. -/
def englishPassive : Verb := { voice := passive, d := ↑() }

/-- The inchoative of (72a), v[BECOME], as a `LittleV` event structure: change over a state. -/
def inchoative : Verb := { events := ↑[LittleV.vGO, .vBE] }

/-- The causative of (72b), v[CAUS] with [D], as an activity over a state; the two differ at the
higher head (`LittleV.Causative.not_inchoative`). -/
def causative : Verb := { events := ↑[LittleV.vDO, .vBE], d := ↑() }

/-- A *se*-reflexive of Italian or BCS, on VoiceREFL. -/
def seReflexive : Verb := { voice := reflexive }

/-! ### The conditions of (49) -/

/-- A Syntactic Identity Condition: when the elided structure may stand to its antecedent under an
ellipsis. -/
abbrev SIC := Ellipsis clausalSpine → Verb → Verb → Prop

/-- Nondistinctness, on the argument domain, which leaves out T and polarity. -/
def nondistinct : SIC := fun e a t ↦ e.Nondistinct a.content t.content

instance (e : Ellipsis clausalSpine) (a t : Verb) : Decidable (nondistinct e a t) :=
  inferInstanceAs (Decidable (e.Nondistinct _ _))

/-- The grid of (49): the two clauses stand in `R` at the sites of `D` inside the deletion domain.
(49a) is `Eq` on the verbal spine, (49b) and (49c) are `Eq` on an argument structure and an eventive
core, and (49d) as printed is `Compat` on everything. -/
def relatedOn (R : Bundle → Bundle → Prop) (D : Set Site) : SIC :=
  fun e a t ↦ ∀ x ∈ D ∩ e.domain, R (a.content x) (t.content x)

/-! ### The rows -/

/-- An example: an ellipsis with its antecedent, elided structure and the role of its remnant, if a
core one, or a causative with the structure its vCAUS merges on. -/
inductive Clause
  | ellipsis (e : Ellipsis clausalSpine) (a t : Verb) (ρ : Option ArgumentRole)
  | causative (base : Verb)
  deriving DecidableEq

/-- The example is licit under a condition: an ellipsis meets it and a remnant in the role P has a
source in the site, and vCAUS merges on a vP, not a VoiceP (p. 26), as its selection requires. -/
def Clause.Licit (C : SIC) : Clause → Prop
  | .ellipsis e a t ρ => C e a t ∧ (ρ = some .P → t.SelectsObject)
  | .causative base => base.voice = ⊥

instance : DecidablePred (Clause.Licit nondistinct)
  | .ellipsis _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .causative _ => inferInstanceAs (Decidable (_ = _))

/-- An example of the paper with its judgment. -/
structure Row where
  /-- The example. -/
  clause : Clause
  /-- Its judgment. -/
  judgment : Judgment

/-- The structures of the forms of a language. -/
def formsOf : List (Glottocode × List (String × Verb)) :=
  [(.kiche, [("antipassive", kicheAntipassive), ("transitive", kicheTransitive),
      ("agentFocus", kicheAgentFocus), ("passive", kichePassive),
      ("intransitive", intransitive)]),
    (.kaqchikel, [("antipassive", kaqchikelAntipassive), ("transitive", kaqchikelTransitive),
      ("agentFocus", kaqchikelAgentFocus), ("passive", kaqchikelPassive)]),
    (.english, [("transitive", active), ("transitiveTo", activeTo),
      ("transitiveTail", activeTail), ("intransitive", activeIntransitive), ("active", active),
      ("passive", englishPassive), ("inchoative", inchoative), ("causative", causative)]),
    (.italian, [("active", active), ("reflexive", seReflexive)]),
    (.serbianCroatianBosnian, [("active", active), ("reflexive", seReflexive)])]

/-- Read a row. In the order `causThenBase` the antipassive is formed on a causative, whose vCAUS
merges on an intransitive. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let forms ← ex.byLanguage formsOf
  let clause ← match ex.feature? "construction" with
    | some "ellipsis" => do
      let e ← ex.parse? "ellipsis" [("tp", sluicing), ("vp", vpEllipsis)]
      let a ← ex.parse? "antecedent" forms
      let t ← ex.parse? "target" forms
      let ρ ← ex.parse? "remnant" [("object", some ArgumentRole.P), ("subject", some .A),
        ("oblique", none), ("none", none)]
      pure (Clause.ellipsis e a t ρ)
    | some "causative" => do
      let base ← ex.parse? "base" forms
      match ex.feature? "order" with
      | some "caus" => pure (Clause.causative base)
      | some "causThenBase" => pure (Clause.causative intransitive)
      | _ => none
    | _ => none
  pure ⟨clause, ex.judgment⟩

/-- Read a row of [anand-hardt-mccloskey-2025]: a preposition without a counterpart in the
antecedent, in situ in the argument domain if it marks an argument and in an adjunct of VoiceP if
not. -/
def Row.ofStranded (ex : Datum) : Option Row := do
  let t ← ex.parse? "ppType" [("argument", activeTo), ("nonargument", activeHigh)]
  pure ⟨.ellipsis sluicing active t none, ex.judgment⟩

/-- The paper's examples and the stranded prepositions of [anand-hardt-mccloskey-2025]. -/
def rows : List Row :=
  Examples.all.filterMap Row.ofDatum ++
    AnandHardtMcCloskey2025.Examples.all.filterMap Row.ofStranded

theorem length_rows :
    rows.length = Examples.all.length + AnandHardtMcCloskey2025.Examples.all.length := by
  decide +kernel

/-- Nondistinctness on the argument domain predicts the judgments: the K'iche' mismatch, its absence
in Kaqchikel, the English voice and transitivity alternations, the stranded prepositions and the
reflexives of Italian and BCS. -/
theorem rows_predicted : ∀ r ∈ rows, (.marginal ≤ r.judgment ↔ r.clause.Licit nondistinct) := by
  decide +kernel

/-! ### Identity and the domain -/

/-- The sites the structures give features to. -/
def contentful : Set Site := {.head .V, .head .v, .head .Voice, .adjunct .Voice}

theorem Verb.content_of_notMem (σ : Verb) {x : Site} (hx : x ∉ contentful) : σ.content x = ⊥ := by
  fun_cases Verb.content σ x <;> simp_all [contentful]

theorem Verb.content_eq_of_ne {σ τ : Verb} {x y : Site} (hx : x ≠ y)
    (h : ∀ z ∈ contentful, z ≠ y → σ.content z = τ.content z) : σ.content x = τ.content x := by
  by_cases hc : x ∈ contentful
  · exact h x hc hx
  · rw [σ.content_of_notMem hc, τ.content_of_notMem hc]

/-- No equivalence relation predicts the judgments, on any domain, so neither an identity condition
such as (49a)–(49c) nor identity of any abstraction of the bundles does: a domain without Voice
admits the English voice mismatch (69a), and on a domain with it, the Kaqchikel mismatches (51) and
(52) and the K'iche' mismatch (1) chain the passive to the active. -/
theorem not_forall_licit_of_equivalence {R : Bundle → Bundle → Prop} (hR : Equivalence R)
    (D : Set Site) : ¬ ∀ r ∈ rows, (.marginal ≤ r.judgment ↔ r.clause.Licit (relatedOn R D)) := by
  intro h
  have licit : ∀ {a t : Verb} {ρ : Option ArgumentRole},
      (∃ r ∈ rows, r.clause = .ellipsis sluicing a t ρ ∧ .marginal ≤ r.judgment) →
        Site.head .Voice ∈ D → R (a.content (.head .Voice)) (t.content (.head .Voice)) := by
    rintro a t ρ ⟨r, hr, hc, hj⟩ hD
    have hl := (h r hr).1 hj
    rw [hc] at hl
    exact hl.1 _ ⟨hD, mem_domain.2 (by decide)⟩
  obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows,
      r.clause = .ellipsis sluicing englishPassive active (some .A) ∧ ¬ .marginal ≤ r.judgment := by
    decide +kernel
  refine hj ((h r hr).2 ?_)
  rw [hc]
  refine ⟨fun x hx ↦ ?_, by simp⟩
  by_cases hV : x = .head .Voice
  · subst hV
    have h₁ := licit (a := kaqchikelPassive) (t := kaqchikelAgentFocus) (ρ := some .A)
      (by decide +kernel) hx.1
    have h₂ := licit (a := kaqchikelAgentFocus) (t := kaqchikelTransitive) (ρ := some .P)
      (by decide +kernel) hx.1
    have h₃ := licit (a := kicheAntipassive) (t := kicheTransitive) (ρ := some .P)
      (by decide +kernel) hx.1
    exact hR.trans (hR.trans h₁ h₂) (hR.symm h₃)
  · rw [Verb.content_eq_of_ne (τ := active) hV (by
      rintro z (rfl | rfl | rfl | rfl) hz <;> first | rfl | exact absurd rfl hz)]
    exact hR.refl _

theorem relatedOn_compat_of_ne {D : Set Site} {y : Site} (hy : y ∉ D) {e : Ellipsis clausalSpine}
    {a t : Verb} (h : ∀ z ∈ contentful, z ≠ y → a.content z = t.content z) :
    relatedOn Compat D e a t :=
  fun x hx ↦ by
    rw [Verb.content_eq_of_ne (ne_of_mem_of_not_mem hx.1 hy) h]
    exact compat_self _

/-- The judgments fix the domain of nondistinctness: they are predicted exactly on the sets of sites
containing V (48b), v (70b) and Voice (69a) and not the adjunction site of VoiceP (13a). -/
theorem rows_predicted_on_iff {D : Set Site} :
    (∀ r ∈ rows, (.marginal ≤ r.judgment ↔ r.clause.Licit (relatedOn Compat D))) ↔
      ({.head .V, .head .v, .head .Voice} : Set Site) ⊆ D ∧ .adjunct .Voice ∉ D := by
  refine ⟨fun h ↦ ⟨fun x hx ↦ by_contra fun hxD ↦ ?_, fun hD ↦ ?_⟩,
    fun ⟨hD, hA⟩ r hr ↦ (rows_predicted r hr).trans ?_⟩
  · rcases hx with rfl | rfl | rfl
    · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows,
          r.clause = .ellipsis sluicing active activeTo none ∧ ¬ .marginal ≤ r.judgment := by
        decide +kernel
      exact hj ((h r hr).2 (hc ▸ ⟨relatedOn_compat_of_ne hxD (by
        rintro z (rfl | rfl | rfl | rfl) hz <;> first | rfl | exact absurd rfl hz), by simp⟩))
    · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows,
          r.clause = .ellipsis vpEllipsis inchoative causative none ∧
            ¬ .marginal ≤ r.judgment := by
        decide +kernel
      exact hj ((h r hr).2 (hc ▸ ⟨relatedOn_compat_of_ne hxD (by
        rintro z (rfl | rfl | rfl | rfl) hz <;> first | rfl | exact absurd rfl hz), by simp⟩))
    · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows,
          r.clause = .ellipsis sluicing englishPassive active (some .A) ∧
            ¬ .marginal ≤ r.judgment := by
        decide +kernel
      exact hj ((h r hr).2 (hc ▸ ⟨relatedOn_compat_of_ne hxD (by
        rintro z (rfl | rfl | rfl | rfl) hz <;> first | rfl | exact absurd rfl hz), by simp⟩))
  · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows,
        r.clause = .ellipsis sluicing active activeHigh none ∧ .marginal ≤ r.judgment := by
      decide +kernel
    have hl := (h r hr).1 hj
    rw [hc] at hl
    exact absurd (hl.1 _ ⟨hD, mem_domain.2 (by decide)⟩) (by decide +kernel)
  · rcases r.clause with ⟨e, a, t, ρ⟩ | base
    · refine and_congr_left' ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
      · by_cases hc : x ∈ contentful
        · rcases hc with rfl | rfl | rfl | rfl
          · exact h ⟨hx.2, by decide⟩
          · exact h ⟨hx.2, by decide⟩
          · exact h ⟨hx.2, by decide⟩
          · exact absurd hx.1 hA
        · rw [a.content_of_notMem hc]
          exact bot_compat _
      · by_cases hc : x ∈ contentful
        · rcases hc with rfl | rfl | rfl | rfl
          · exact h _ ⟨hD (by simp), hx.1⟩
          · exact h _ ⟨hD (by simp), hx.1⟩
          · exact h _ ⟨hD (by simp), hx.1⟩
          · exact absurd hx.2 (by decide)
        · rw [a.content_of_notMem hc]
          exact bot_compat _
    · rfl

-- [anand-hardt-mccloskey-2025]
theorem T_notMem_of_lowerSet {D : Set Site}
    (h : ∀ r ∈ rows, (.marginal ≤ r.judgment ↔ r.clause.Licit (relatedOn Compat D)))
    (hD : ∀ x y, clausalSpine.rank x ≤ clausalSpine.rank y → y ∈ D → x ∈ D) : .head .T ∉ D :=
  fun hT ↦ (rows_predicted_on_iff.1 h).2 (hD _ _ (by decide) hT)

-- [merchant-2013]
theorem merchant_rows_predicted : ∀ r ∈ Merchant2013.rows,
    (.marginal ≤ r.judgment ↔ ∀ k ∈ r.clause.ellipsis,
      (Merchant2013.analysis k).Nondistinct (fun x ↦ Flat.some (r.clause.antecedent x))
        (fun x ↦ Flat.some (r.clause.target x)) ∧
      ∀ a ∈ r.clause.again, (Merchant2013.analysis k).Spares a.site) := by
  intro r hr
  refine (Merchant2013.rows_predicted r hr).trans <| forall₂_congr fun k _ ↦ and_congr_left' ?_
  rw [nondistinct_coe_iff]
  refine ⟨fun h ↦ h.mono fun _ hx ↦ hx.1, fun h x hx ↦ ?_⟩
  by_cases hm : x ∈ [Site.head .Voice, .head .v]
  · refine h ⟨hx, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> decide
  · exact r.clause.antecedent_eq_target hm

/-! ### K'iche' and Kaqchikel -/

-- (43)
theorem kicheAntipassive_le : kicheAntipassive.content ≤ kicheTransitive.content := fun x ↦ by
  by_cases hx : x ∈ contentful
  · rcases hx with rfl | rfl | rfl | rfl
    · exact le_rfl
    · exact ⟨le_rfl, ⟨le_rfl, le_rfl, bot_le⟩, le_rfl⟩
    · exact ⟨WithBot.coe_le_coe.2 ⟨rfl, rfl, le_rfl, le_rfl, le_rfl, bot_le⟩, le_rfl, le_rfl⟩
    · exact le_rfl
  · simp [Verb.content_of_notMem _ hx]

-- `Merchant2013.deletes_v`
theorem kiche_alternation_survives :
    sluicing.Deletes (.head .v) ∧ kicheAntipassive.d ≠ kicheTransitive.d ∧
      nondistinct sluicing kicheAntipassive kicheTransitive :=
  ⟨by decide, by decide, nondistinct_of_le kicheAntipassive_le⟩

/-- [burukina-polinsky-2025]'s Kaqchikel antipassive, in the terms of their Table 3: vITV, which
selects a nominal, and no Voice. -/
def tableAntipassive : Verb := { d := ↑() }

/-- [burukina-polinsky-2025]'s Kaqchikel transitive: vTV, which selects no nominal, and VoiceTV,
which selects one and bears [ERG]. -/
def tableTransitive : Verb := { voice := voiceErg }

/-- The two antipassives split: the K'iche' one only lacks features of its transitive, and the
Kaqchikel one, on the paper's structures, clashes with its transitive. The Kaqchikel half rests on
Ranero's judgment (53): read privatively, as they read it, the selection in the inventory of
[burukina-polinsky-2025] gives no clash, as they report for their own consultants. -/
theorem antipassive_split :
    kicheAntipassive.content ≤ kicheTransitive.content ∧
      ¬ nondistinct sluicing kaqchikelAntipassive kaqchikelTransitive ∧
      nondistinct sluicing tableAntipassive tableTransitive :=
  ⟨kicheAntipassive_le, by decide +kernel, by decide +kernel⟩

-- (51), (52)
theorem selection_le_of_nondistinct {σ : Verb}
    (h : nondistinct sluicing σ kaqchikelTransitive) :
    σ.selection ≤ (↑vTV : Flat SelStack) := by
  have hc : Compat σ.selection (↑vTV : Flat SelStack) :=
    (compat_prod_iff.1 (compat_prod_iff.1 (compat_prod_iff.1 (compat_prod_iff.1
      (h (x := .head .v) ⟨by decide, by decide⟩)).2).1).2).1
  rcases eq_or_ne σ.selection ⊥ with hb | hb
  · exact hb ▸ bot_le
  · obtain ⟨f, hf⟩ := Flat.ne_bot_iff_exists.1 hb
    rw [hf] at hc ⊢
    rw [Flat.compat_coe_coe.1 hc]

/-- [ranero-2021]'s Kaqchikel antipassive (56a): Voice[AP] over the v of a transitive. -/
def raneroAntipassive : Verb :=
  { voice := ({ agentive with value := .antipassive } : Head), selection := ↑vTV }

-- (53), (56), (57)
theorem ranero_clashes_only_at_voice :
    ¬ nondistinct sluicing raneroAntipassive kaqchikelTransitive ∧
      nondistinct vpEllipsis raneroAntipassive kaqchikelTransitive ∧
      ¬ nondistinct vpEllipsis kaqchikelAntipassive kaqchikelTransitive := by
  decide +kernel

-- pp. 30–31, (70b)
theorem d_alternant_overgenerates : nondistinct vpEllipsis {} { d := ↑() } := by
  decide +kernel

-- footnote 4
example : nondistinct sluicing kicheAntipassive kicheAgentFocus := by
  decide +kernel

/-! ### Theories of features -/

/-- §4.2. Nondistinctness rules out nothing exactly when every feature is privative, with at most
one value, so ellipsis detects the features that are not. -/
theorem forall_nondistinct_iff_subsingleton {ι : Type*} {κ : ι → Type*} {s : ClauseSpine}
    {e : Ellipsis s} {x : Site} (hx : x ∈ e.argumentDomain) :
    (∀ a t : Site → ∀ i, Flat (κ i), e.Nondistinct a t) ↔ ∀ i, Subsingleton (κ i) := by
  classical
  refine ⟨fun h i ↦ ⟨fun u v ↦ ?_⟩, fun _ _ _ _ _ ↦
    compat_pi_iff.2 fun _ ↦ Flat.compat_of_subsingleton⟩
  simpa using (h (fun _ ↦ Function.update ⊥ i ↑u) (fun _ ↦ Function.update ⊥ i ↑v) hx).apply i

-- (69), p. 32
theorem clash_in_value_not_D :
    ¬ Compat agentive passive ∧ Compat agentive { agentive with hasD := false } := by
  decide +kernel

-- pp. 31–32
theorem reflexive_same_cell_clash :
    reflexive.params = agentive.params ∧ ¬ Compat reflexive agentive := by
  decide +kernel

end Beslin2026
