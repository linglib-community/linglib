/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.Merchant2013
public import Linglib.Data.Examples.Beslin2026
public import Linglib.Data.Examples.Languages

/-!
# Bešlin (2026): Apparent voice mismatches in K'iche' ellipsis

The antecedent of a TP ellipsis in K'iche' can contain an antipassive where the elided verb must be
active transitive. Bešlin analyses the antipassive as the active without an internal argument, so
that [it lacks features of the transitive where the Kaqchikel antipassive
clashes](##antipassive_split), and concludes that the identity condition on ellipsis must be
nondistinctness, the absence of a feature clash, which [predicts the judgments](##rows_predicted).
[No equivalence relation does, on any domain](##not_forall_licit_of_equivalence), and the judgments
[fix the domain of nondistinctness only from below](##rows_predicted_on_iff). Nondistinctness [rules
out nothing exactly when every feature is privative](##forall_nondistinct_iff_subsingleton), so
ellipsis detects the features that are not.

## Implementation notes

* A structure gives a bundle to V, v and Voice, and a head it lacks has the empty bundle. The
  dimensions of a bundle are the paper's: a value of Voice and a flavor of v, which are multivalued,
  and the [D] and [ERG] that p. 32 reads as privative. (57b) prints Voice[ERG] alone; it is given
  the ACT of (56b) and the [D] of (43). The paper draws no passive and no agent focus: passives here
  have the v of the transitive, and agent focus has no Voice, as footnote 4 suggests for K'iche'
  without pursuing it. Its v in Kaqchikel can only be [v:TV] or unspecified
  (`flavor_le_tv_of_nondistinct`), so not the third head of [burukina-polinsky-2025].
* The ACT and PASS of the paper are not cells of `Minimalist.Voice.Head`: its [D] is privative and
  apart from ACT, and the cells of active and passive [differ only in ±D](##agentive_passive_clash).
  Its VoiceREFL has no cell either (`params_eq_agentive`).
* An object remnant needs a source in the site, which is why the antipassive cannot be the elided
  verb in (1)–(3). `SelectsObject` is read for no other purpose; the [D] of (72b) selects an
  external argument. The diagnostics of §3.2 are read as this predicate and those of §3.1 as the
  choice of TP ellipsis, rather than encoded as rows.
* A root in situ is a value of a total dimension, and a movement tail leaves the dimension
  unspecified, so a tail matches anything. The paper does not say that the *to* of (48b) is a root,
  but (49d) as printed needs it to be, since an extra functional head is no clash; Chung's Case
  clause in (49b) is the other route to (48b).
* The causatives read the restriction of p. 26, that a vP cannot be merged on top of a VoiceP, as a
  selectional property of vCAUS, as [burukina-polinsky-2025] state it for languages like these;
  their footnote 16 notes languages that causativize verbs of any adicity.
* The status suffixes of footnote 12 and the [EPP] of footnote 19 would differ without clashing in
  the same way as [ERG], and are left out. (70a) is not a row, being a nonelliptical control. With
  the substrate's `LittleV` the alternants of (70) differ at the higher head as with (72)
  (`LittleV.Causative.not_inchoative`).
* `Voice` in `Syntax/Voice/`, under which `Fragments/Mayan/Kiche/Voice.lean` lists the absolutive
  antipassive, relates diatheses and is silent on heads, which leaves room for the paper's
  conclusion that one label covers different structures.

## Errata

* P. 27 offers (65) as a suffix order and concludes that causativization gives independent evidence
  that the Kaqchikel antipassive lacks Voice. Its source, footnote 14 of [burukina-polinsky-2025],
  gives the sentence as one without a causativizing sub-event, with -isa spelling out an applicative
  head, and states that Kaqchikel antipassives cannot causativize. The row records the paper's
  reading.
* The paper adopts the Kaqchikel structures of [burukina-polinsky-2025] without mentioning that they
  did not replicate (53) (their p. 717), and [their Table 3 has no clash](##antipassive_split), as
  p. 24 grants. P. 25 adds the clash through its (ii), that only [v:TV] selects a VP with an
  internal argument, where they say that nothing in the selection of vITV precludes one, and p. 31's
  claim that the distribution requires clashing features does not follow: different selection needs
  only different heads.
* The text on p. 6 says the antipassive cannot be used in (11), which prints it without a star, and
  footnote 2 calls the direction opposite to antipassive–active "antipassive–active".
* P. 25 prints vITV twice, the first for vTV, and p. 31 recalls [TR] and [ITR] for the [v:TV] and
  [v:ITV] of p. 24.
* (12) glosses the prefix of 'I'm walking' ABS3SG; (1)–(3) gloss the elided verb's prefixes
  ERG3SG-ABS3SG in the order opposite to the form; (53) and (54) gloss the elided *k'ay* 'buy'
  against 'sell' in the antecedent, and (54) repeats (53) with PST for NPST and Juan for Juana.

## TODO

* T lies inside a TP ellipsis, so (49d) read literally rejects a clash in tense
  (`Minimalist.Ellipsis.nondistinct_update_iff`), while [anand-hardt-mccloskey-2025] survey tense,
  modality and polarity mismatches in sluicing. Every row here has matching T, though (1), (35) and
  (36) have negation in the antecedent alone. Either T and polarity lie outside the domain, or by
  the logic of §4.2 their features are privative.
* `merchant_rows_predicted` treats each of Merchant's v heads as a full value. His *plain* in (40b),
  (41b) and (45a) is the absence of a preposition, which should reduce to the root clause as (48b)
  does; the *to* of (41b) is at v there and at V here.
* The second clause of (49b). The conditions (49a)–(49c) are read from the paper's statements of
  them, and [ranero-2021] was not at hand.
* The alternative of footnote 15 of [burukina-polinsky-2025] for K'iche', no vP recursion, which
  (64) bears on.

## References

* [beslin-2026]
* [ranero-2021]
* [burukina-polinsky-2025]
* [folli-harley-2005]
* [merchant-2013]
* [chung-2013]
* [rudin-2019]
* [anand-hardt-mccloskey-2025]
-/

@[expose] public section

namespace Beslin2026

open Minimalist Minimalist.Ellipsis ClauseSpine Minimalist.Voice

/-! ### Features -/

/-- The values of Voice the paper prints: ACT, PASS, Voice[AP] in (56a) and VoiceREFL. -/
inductive VoiceValue
  | act
  | pass
  | ap
  | refl
  deriving DecidableEq, Repr

/-- The flavors of v: [folli-harley-2005]'s causative and inchoative v (72), and [v:TV] and [v:ITV],
which the paper reads as values on pp. 24–25. -/
inductive Flavor
  | cause
  | become
  | tv
  | itv
  deriving DecidableEq, Repr

/-- A root outside the verb in situ in the clause: the preposition of (47), (48). -/
inductive Root
  | to
  deriving DecidableEq, Repr

/-- The feature dimensions of the paper's structures. -/
inductive Dim
  | voice
  | flavor
  | d
  | erg
  | roots
  deriving DecidableEq, Fintype, Repr

/-- The values of a dimension. [D] and [ERG] are privative, with a single value. -/
abbrev Dim.Value : Dim → Type
  | .voice => VoiceValue
  | .flavor => Flavor
  | .d | .erg => Unit
  | .roots => List Root

instance (i : Dim) : DecidableEq i.Value := by cases i <;> exact inferInstance

/-- A feature bundle, a slot at each dimension. -/
abbrev Bundle := (i : Dim) → Flat i.Value

/-- The bundle with the listed features, empty elsewhere. -/
def Bundle.of (l : List (Σ i : Dim, i.Value)) : Bundle :=
  l.foldr (fun p b ↦ Function.update b p.1 ↑p.2) ⊥

/-! ### Structures -/

/-- Voice[ACT] with [D]. -/
def actVoice : Bundle := .of [⟨.voice, .act⟩, ⟨.d, ()⟩]

/-- Voice[ACT] with [D] and the [ERG] that licenses ergative case on the external argument. -/
def ergVoice : Bundle := .of [⟨.voice, .act⟩, ⟨.d, ()⟩, ⟨.erg, ()⟩]

/-- Voice[PASS]. -/
def passVoice : Bundle := .of [⟨.voice, .pass⟩]

/-- A v or Voice selecting a nominal, and nothing else. -/
def onlyD : Bundle := .of [⟨.d, ()⟩]

/-- A v of one flavor. -/
def flavored (f : Flavor) : Bundle := .of [⟨.flavor, f⟩]

/-- A verbal structure: the bundles of its Voice, `⊥` if it projects none, of its v and of V. -/
structure Verb where
  /-- The bundle of Voice. -/
  voice : Bundle := ⊥
  /-- The bundle of v. -/
  v : Bundle := ⊥
  /-- The bundle of V. -/
  root : Bundle := .of [⟨.roots, []⟩]
  deriving DecidableEq

namespace Verb

/-- The bundle a structure gives each site. -/
def content (σ : Verb) : Site → Bundle
  | .head .Voice => σ.voice
  | .head .v => σ.v
  | .head .V => σ.root
  | _ => ⊥

/-- The v of the structure selects an internal argument: [D] in K'iche' (43b), [v:TV] in Kaqchikel
(57b). -/
def SelectsObject (σ : Verb) : Prop := σ.v .d = ↑() ∨ σ.v .flavor = ↑Flavor.tv

instance (σ : Verb) : Decidable σ.SelectsObject := inferInstanceAs (Decidable (_ ∨ _))

end Verb

/-- The K'iche' antipassive (43a): active Voice, and a v without [D]. -/
def kicheAntipassive : Verb := { voice := actVoice }

/-- The K'iche' active transitive (43b): active Voice with [ERG], and a v with [D]. -/
def kicheTransitive : Verb := { voice := ergVoice, v := onlyD }

/-- K'iche' agent focus. -/
def kicheAgentFocus : Verb := { v := onlyD }

/-- A K'iche' passive. -/
def kichePassive : Verb := { voice := passVoice, v := onlyD }

/-- An inherent intransitive, a small vP. -/
def intransitive : Verb := {}

/-- The Kaqchikel antipassive (57a), a small vP with [v:ITV]. -/
def kaqchikelAntipassive : Verb := { v := flavored .itv }

/-- The Kaqchikel active transitive (57b): Voice with [ERG], and [v:TV]. -/
def kaqchikelTransitive : Verb := { voice := ergVoice, v := flavored .tv }

/-- Kaqchikel agent focus: no Voice ([ranero-2021]). -/
def kaqchikelAgentFocus : Verb := { v := flavored .tv }

/-- A Kaqchikel passive. -/
def kaqchikelPassive : Verb := { voice := passVoice, v := flavored .tv }

/-- An active transitive of English, Italian or BCS. -/
def active : Verb := { voice := actVoice, v := onlyD }

/-- *ate* in (46), on the assumption p. 18 grants conditionally, that it has no internal argument.
-/
def activeIntransitive : Verb := { voice := actVoice }

/-- An active transitive with *to* in situ. -/
def activeTo : Verb := { active with root := .of [⟨.roots, [.to]⟩] }

/-- An active transitive with *to* in a movement tail. -/
def activeTail : Verb := { active with root := ⊥ }

/-- An English passive. -/
def englishPassive : Verb := { voice := passVoice, v := onlyD }

/-- The inchoative of (72a), v[BECOME]. -/
def inchoative : Verb := { v := flavored .become }

/-- The causative of (72b), v[CAUS] with [D]. -/
def causative : Verb := { v := .of [⟨.flavor, .cause⟩, ⟨.d, ()⟩] }

/-- A *se*-reflexive of Italian or BCS, on VoiceREFL. -/
def seReflexive : Verb := { voice := .of [⟨.voice, .refl⟩] }

/-! ### The conditions of (49) -/

/-- A Syntactic Identity Condition: when the elided structure may stand to its antecedent under an
ellipsis. -/
abbrev SIC := Ellipsis clausalSpine → Verb → Verb → Prop

/-- (49d), nondistinctness. -/
def nondistinct : SIC := fun e a t ↦ e.Nondistinct a.content t.content

instance (e : Ellipsis clausalSpine) (a t : Verb) : Decidable (nondistinct e a t) :=
  inferInstanceAs (Decidable (e.Nondistinct _ _))

/-- The grid of (49): the two clauses stand in `R` at the sites of `D` inside the deletion domain.
(49a) is `Eq` on the verbal spine; (49b) and (49c) are `Eq` on an argument structure and an eventive
core. -/
def relatedOn (R : Bundle → Bundle → Prop) (D : Set Site) : SIC :=
  fun e a t ↦ ∀ x ∈ D ∩ e.domain, R (a.content x) (t.content x)

/-! ### The rows -/

/-- What an ellipsis leaves behind, as far as the prediction needs. -/
inductive Remnant
  | object
  | subject
  | oblique
  | none
  deriving DecidableEq, Repr

/-- An example: an ellipsis with its antecedent, elided structure and remnant, or a causative with
the structure its vCAUS merges on. -/
inductive Clause
  | ellipsis (e : Ellipsis clausalSpine) (a t : Verb) (ρ : Remnant)
  | causative (base : Verb)
  deriving DecidableEq

/-- The example is licit under a condition: an ellipsis meets it and an object remnant has a source
in the site, and vCAUS merges on a vP, not a VoiceP. -/
def Clause.Licit (C : SIC) : Clause → Prop
  | .ellipsis e a t ρ => C e a t ∧ (ρ = .object → t.SelectsObject)
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
      let ρ ← ex.parse? "remnant" [("object", Remnant.object), ("subject", .subject),
        ("oblique", .oblique), ("none", .none)]
      pure (Clause.ellipsis e a t ρ)
    | some "causative" => do
      let base ← ex.parse? "base" forms
      match ex.feature? "order" with
      | some "caus" => pure (Clause.causative base)
      | some "causThenBase" => pure (Clause.causative intransitive)
      | _ => none
    | _ => none
  pure ⟨clause, ex.judgment⟩

/-- The paper's examples. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem length_rows : rows.length = Examples.all.length := by decide +kernel

/-- Nondistinctness predicts the judgments: the K'iche' mismatch, its absence in Kaqchikel, the
English voice and transitivity alternations, the stranded preposition and the reflexives of Italian
and BCS. -/
theorem rows_predicted : ∀ r ∈ rows, (.marginal ≤ r.judgment ↔ r.clause.Licit nondistinct) := by
  decide +kernel

/-! ### Identity and the domain -/

/-- The heads the structures give features to. -/
def core : Set Site := {.head .V, .head .v, .head .Voice}

theorem Verb.content_of_notMem_core (σ : Verb) {x : Site} (hx : x ∉ core) : σ.content x = ⊥ := by
  fun_cases Verb.content σ x <;> simp_all [core]

theorem Verb.content_eq_of_ne {σ τ : Verb} {x y : Site} (hx : x ≠ y)
    (h : ∀ z ∈ core, z ≠ y → σ.content z = τ.content z) : σ.content x = τ.content x := by
  by_cases hc : x ∈ core
  · exact h x hc hx
  · rw [σ.content_of_notMem_core hc, τ.content_of_notMem_core hc]

/-- No equivalence relation predicts the judgments, on any domain, so neither an identity condition
such as (49a)–(49c) nor identity of any abstraction of the bundles does: a domain without Voice
admits the English voice mismatch (69a), and on a domain with it, the Kaqchikel mismatches (51) and
(52) and the K'iche' mismatch (1) chain the passive to the active. -/
theorem not_forall_licit_of_equivalence {R : Bundle → Bundle → Prop} (hR : Equivalence R)
    (D : Set Site) : ¬ ∀ r ∈ rows, (.marginal ≤ r.judgment ↔ r.clause.Licit (relatedOn R D)) := by
  intro h
  have licit : ∀ {a t : Verb} {ρ : Remnant},
      (∃ r ∈ rows, r.clause = .ellipsis sluicing a t ρ ∧ .marginal ≤ r.judgment) →
        Site.head .Voice ∈ D → R a.voice t.voice := by
    rintro a t ρ ⟨r, hr, hc, hj⟩ hD
    have hl := (h r hr).1 hj
    rw [hc] at hl
    exact hl.1 _ ⟨hD, mem_domain.2 (by decide)⟩
  obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows,
      r.clause = .ellipsis sluicing englishPassive active .subject ∧ ¬ .marginal ≤ r.judgment := by
    decide +kernel
  refine hj ((h r hr).2 ?_)
  rw [hc]
  refine ⟨fun x hx ↦ ?_, by simp⟩
  by_cases hV : x = .head .Voice
  · subst hV
    have h₁ : R passVoice ⊥ := licit (a := kaqchikelPassive) (t := kaqchikelAgentFocus)
      (ρ := .subject) (by decide +kernel) hx.1
    have h₂ : R ⊥ ergVoice := licit (a := kaqchikelAgentFocus) (t := kaqchikelTransitive)
      (ρ := .object) (by decide +kernel) hx.1
    have h₃ : R actVoice ergVoice := licit (a := kicheAntipassive) (t := kicheTransitive)
      (ρ := .object) (by decide +kernel) hx.1
    exact hR.trans (hR.trans h₁ h₂) (hR.symm h₃)
  · rw [Verb.content_eq_of_ne (τ := active) hV (by
      rintro z (rfl | rfl | rfl) hz <;> first | rfl | exact absurd rfl hz)]
    exact hR.refl _

theorem relatedOn_compat_of_ne {D : Set Site} {y : Site} (hy : y ∉ D) {e : Ellipsis clausalSpine}
    {a t : Verb} (h : ∀ z ∈ core, z ≠ y → a.content z = t.content z) : relatedOn Compat D e a t :=
  fun x hx ↦ by
    rw [Verb.content_eq_of_ne (ne_of_mem_of_not_mem hx.1 hy) h]
    exact compat_self _

/-- The judgments fix the domain of nondistinctness only from below: they are predicted exactly on
the sets of sites containing V (48b), v (70b) and Voice (69a). They do not decide between the whole
elided clause of (49d) and the eventive core of (49c), since no structure gives T a feature. -/
theorem rows_predicted_on_iff {D : Set Site} :
    (∀ r ∈ rows, (.marginal ≤ r.judgment ↔ r.clause.Licit (relatedOn Compat D))) ↔ core ⊆ D := by
  refine ⟨fun h x hx ↦ by_contra fun hxD ↦ ?_, fun hD r hr ↦ (rows_predicted r hr).trans ?_⟩
  · rcases hx with rfl | rfl | rfl
    · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows,
          r.clause = .ellipsis sluicing active activeTo .oblique ∧ ¬ .marginal ≤ r.judgment := by
        decide +kernel
      exact hj ((h r hr).2 (hc ▸ ⟨relatedOn_compat_of_ne hxD (by
        rintro z (rfl | rfl | rfl) hz <;> first | rfl | exact absurd rfl hz), by simp⟩))
    · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows,
          r.clause = .ellipsis vpEllipsis inchoative causative .none ∧
            ¬ .marginal ≤ r.judgment := by
        decide +kernel
      exact hj ((h r hr).2 (hc ▸ ⟨relatedOn_compat_of_ne hxD (by
        rintro z (rfl | rfl | rfl) hz <;> first | rfl | exact absurd rfl hz), by simp⟩))
    · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows,
          r.clause = .ellipsis sluicing englishPassive active .subject ∧
            ¬ .marginal ≤ r.judgment := by
        decide +kernel
      exact hj ((h r hr).2 (hc ▸ ⟨relatedOn_compat_of_ne hxD (by
        rintro z (rfl | rfl | rfl) hz <;> first | rfl | exact absurd rfl hz), by simp⟩))
  · rcases r.clause with ⟨e, a, t, ρ⟩ | base
    · refine and_congr_left' ⟨fun h x hx ↦ h hx.2, fun h x hx ↦ ?_⟩
      by_cases hc : x ∈ core
      · exact h x ⟨hD hc, hx⟩
      · rw [a.content_of_notMem_core hc]
        exact bot_compat _
    · rfl

-- [merchant-2013]
theorem merchant_rows_predicted : ∀ r ∈ Merchant2013.rows,
    (.marginal ≤ r.judgment ↔ ∀ k ∈ r.clause.ellipsis,
      (Merchant2013.analysis k).Nondistinct (fun x ↦ Flat.some (r.clause.antecedent x))
        (fun x ↦ Flat.some (r.clause.target x)) ∧
      ∀ a ∈ r.clause.again, (Merchant2013.analysis k).Spares a.site) := by
  simpa only [nondistinct_coe_iff, Merchant2013.Licit] using Merchant2013.rows_predicted

/-! ### K'iche' and Kaqchikel -/

-- (43)
theorem kicheAntipassive_le : kicheAntipassive.content ≤ kicheTransitive.content := fun x ↦ by
  by_cases hx : x ∈ core
  · rcases hx with rfl | rfl | rfl <;> decide +kernel
  · simp [Verb.content_of_notMem_core _ hx]

-- `Merchant2013.deletes_v`
theorem kiche_alternation_survives :
    sluicing.Deletes (.head .v) ∧
      kicheAntipassive.content (.head .v) ≠ kicheTransitive.content (.head .v) ∧
      sluicing.Nondistinct kicheAntipassive.content kicheTransitive.content :=
  ⟨by decide, by decide +kernel, nondistinct_of_le kicheAntipassive_le⟩

/-- [burukina-polinsky-2025]'s Kaqchikel antipassive, in the terms of their Table 3: vITV, which
selects a nominal, and no Voice. -/
def tableAntipassive : Verb := { v := onlyD }

/-- [burukina-polinsky-2025]'s Kaqchikel transitive: vTV, which selects no nominal, and VoiceTV,
which selects one and bears [ERG]. -/
def tableTransitive : Verb := { voice := .of [⟨.d, ()⟩, ⟨.erg, ()⟩] }

/-- The two antipassives split: the K'iche' one only lacks features of its transitive, and the
Kaqchikel one, on the paper's structures, clashes with its transitive. The Kaqchikel half rests on
Ranero's judgment (53): in the inventory [burukina-polinsky-2025] give, which has no flavors in the
paper's sense, the two do not clash, as they report for their own consultants. -/
theorem antipassive_split :
    kicheAntipassive.content ≤ kicheTransitive.content ∧
      ¬ sluicing.Nondistinct kaqchikelAntipassive.content kaqchikelTransitive.content ∧
      sluicing.Nondistinct tableAntipassive.content tableTransitive.content :=
  ⟨kicheAntipassive_le, by decide +kernel, by decide +kernel⟩

-- (51), (52)
theorem flavor_le_tv_of_nondistinct {σ : Verb}
    (h : sluicing.Nondistinct σ.content kaqchikelTransitive.content) :
    σ.v .flavor ≤ (↑Flavor.tv : Flat Flavor) := by
  have hc : Compat (σ.v .flavor) (↑Flavor.tv : Flat Flavor) :=
    (h (x := .head .v) (mem_domain.2 (by decide))).apply .flavor
  rcases eq_or_ne (σ.v .flavor) ⊥ with hb | hb
  · exact hb ▸ bot_le
  · obtain ⟨f, hf⟩ := Flat.ne_bot_iff_exists.1 hb
    rw [hf] at hc ⊢
    rw [Flat.compat_coe_coe.1 hc]

-- (53), (56), (57)
theorem ranero_clashes_only_at_voice :
    ¬ sluicing.Nondistinct
        ({ voice := .of [⟨.voice, .ap⟩], v := flavored .tv } : Verb).content
        kaqchikelTransitive.content ∧
      vpEllipsis.Nondistinct ({ voice := .of [⟨.voice, .ap⟩], v := flavored .tv } : Verb).content
        kaqchikelTransitive.content ∧
      ¬ vpEllipsis.Nondistinct kaqchikelAntipassive.content kaqchikelTransitive.content := by
  decide +kernel

-- pp. 30–31, (70b)
theorem d_alternant_overgenerates :
    vpEllipsis.Nondistinct ({} : Verb).content ({ v := onlyD } : Verb).content :=
  nondistinct_of_le fun x ↦ by
    by_cases hx : x ∈ core
    · rcases hx with rfl | rfl | rfl <;> decide +kernel
    · simp [Verb.content_of_notMem_core _ hx]

-- footnote 4
example : sluicing.Nondistinct kicheAntipassive.content kicheAgentFocus.content := by
  decide +kernel

/-! ### Theories of features -/

/-- §4.2. Nondistinctness rules out nothing exactly when every feature is privative, with at most
one value, so ellipsis detects the features that are not. -/
theorem forall_nondistinct_iff_subsingleton {ι : Type*} {κ : ι → Type*} {s : ClauseSpine}
    {e : Ellipsis s} {x : Site} (hx : e.Deletes x) :
    (∀ a t : Site → ∀ i, Flat (κ i), e.Nondistinct a t) ↔ ∀ i, Subsingleton (κ i) := by
  classical
  refine ⟨fun h i ↦ ⟨fun u v ↦ ?_⟩, fun _ _ _ _ _ ↦
    compat_pi_iff.2 fun _ ↦ Flat.compat_of_subsingleton⟩
  simpa using (h (fun _ ↦ Function.update ⊥ i ↑u) (fun _ ↦ Function.update ⊥ i ↑v) hx).apply i

/-- A Voice cell with ±D read as the paper reads [D] (p. 32), the bearing or lacking of a privative
feature. -/
def privative (p : Params) : Flat Unit × Flat Bool := (if p.1 = ↑true then ↑() else ⊥, p.2)

-- (69), p. 32
theorem agentive_passive_clash :
    agentive.params.2 = passive.params.2 ∧ ¬ Compat agentive.params passive.params ∧
      Compat (privative agentive.params) (privative passive.params) :=
  ⟨rfl, by simp [compat_prod_iff, Head.params, agentive, passive],
    compat_prod_iff.2 ⟨Flat.compat_of_subsingleton, by simp [privative, Head.params, agentive,
      passive]⟩⟩

-- pp. 31–32
theorem params_eq_agentive {h : Head} (hD : h.HasD) (hθ : h.IsThematic) :
    h.params = agentive.params := by
  simp_all [Head.params, Head.HasD, Head.IsThematic, agentive]

end Beslin2026
