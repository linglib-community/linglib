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
public import Linglib.Fragments.Mayan.Kaqchikel.Extraction
public import Linglib.Fragments.Mayan.Kaqchikel.Voice
public import Linglib.Fragments.Mayan.Kiche.Voice
public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Minimalist.Verbal.LittleV

/-!
# Bešlin (2026): Apparent voice mismatches in K'iche' ellipsis

The antecedent of a TP ellipsis in K'iche' can contain an antipassive where the elided verb must be
active transitive. Bešlin analyses the antipassive as the active without an internal argument and
concludes that identity on ellipsis must be nondistinctness, the absence of a feature clash. An
analysis here gives each surface voice of each language a structure. The paper's [predicts the
judgments](##rows_predicted), while [no analysis does under identity, on any
domain](##not_predicts_eq), and [none does uniformly across languages](##not_predicts_uniform), one
label covering different structures. With the stranded prepositions of Anand, Hardt and McCloskey
the judgments [fix the domain](##predicts_on_iff), which reaches Voice and stops below T.
Nondistinctness [rules out nothing exactly when every feature is
privative](##forall_nondistinct_iff_subsingleton).

## Implementation notes

* (49d) as printed compares all the material in the ellipsis site. The condition here compares only
  the argument domain of [anand-hardt-mccloskey-2025], which their stranded prepositions require.

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
  deriving DecidableEq

/-- The v of the structure selects an internal argument: [D] in K'iche' (43b), [v:TV] in Kaqchikel
(57b). It is read only for a remnant in the role P; the [D] of (72b) selects an external
argument. -/
def Verb.SelectsObject (σ : Verb) : Prop := σ.d = ↑() ∨ σ.selection = ↑vTV

instance (σ : Verb) : Decidable σ.SelectsObject := inferInstanceAs (Decidable (_ ∨ _))

/-- Active Voice with the [ERG] that licenses ergative case on the external argument. -/
def voiceErg : Head := { agentive with features := .single .case .erg }

/-- The K'iche' antipassive (43a): active Voice, and a v without [D]. -/
def kicheAntipassive : Verb := { voice := agentive }

/-- The K'iche' active transitive (43b): active Voice with [ERG], and a v with [D]. -/
def kicheTransitive : Verb := { voice := voiceErg, d := ↑() }

/-- K'iche' agent focus, without Voice as footnote 4 suggests. -/
def kicheAgentFocus : Verb := { d := ↑() }

/-- A passive, which the paper does not draw, with the v of the K'iche' or English transitive. -/
def passiveD : Verb := { voice := passive, d := ↑() }

/-- The Kaqchikel antipassive (57a), a small vP with [v:ITV]. -/
def kaqchikelAntipassive : Verb := { selection := ↑vITV }

/-- The Kaqchikel active transitive (57b), which prints Voice[ERG] alone: given the ACT of (56b) and
the [D] of (43), and [v:TV]. -/
def kaqchikelTransitive : Verb := { voice := voiceErg, selection := ↑vTV }

/-- Kaqchikel agent focus: no Voice ([ranero-2021]), and a v that can only be [v:TV] or unspecified
(`selection_le_of_predicts`). -/
def kaqchikelAgentFocus : Verb := { selection := ↑vTV }

/-- A Kaqchikel passive, which the paper does not draw, with the v of the transitive. -/
def kaqchikelPassive : Verb := { voice := passive, selection := ↑vTV }

/-- An active transitive of English, Italian or BCS. -/
def activeD : Verb := { voice := agentive, d := ↑() }

/-- *ate* in (46), on the assumption p. 18 grants conditionally, that it has no internal
argument. -/
def activeImplicit : Verb := { voice := agentive }

/-- The inchoative of (72a), v[BECOME], as a `LittleV` event structure: change over a state. -/
def inchoative : Verb := { events := ↑[LittleV.vGO, .vBE] }

/-- The causative of (72b), v[CAUS] with [D], as an activity over a state; the two differ at the
higher head (`LittleV.Causative.not_inchoative`). -/
def causative : Verb := { events := ↑[LittleV.vDO, .vBE], d := ↑() }

/-- A *se*-reflexive of Italian or BCS, on VoiceREFL. -/
def seReflexive : Verb := { voice := reflexive }

/-! ### Analyses -/

/-- The voice of an inherently intransitive verb, a small vP in (58)–(61). -/
abbrev intransitiveVoice : _root_.Voice := _root_.Voice.refl .intransitive

/-- The voice of *ate* in (46). -/
abbrev implicitVoice : _root_.Voice := _root_.Voice.leaveImplicit .np 0

/-- A form of an example: a surface voice of a language, that of a radical verb in the Mayan
languages, and the roots in situ beside the verb and in an adjunct of VoiceP. Having no root differs
from having one, the second clause of (49d), and a movement tail leaves them unspecified, so a tail
matches anything. -/
structure Form where
  /-- The language. -/
  language : Glottocode
  /-- The surface voice. -/
  voice : _root_.Voice
  /-- The roots in situ beside the verb. -/
  roots : Flat (List Root) := ↑([] : List Root)
  /-- The roots in situ in an adjunct of VoiceP. -/
  high : Flat (List Root) := ↑([] : List Root)
  deriving DecidableEq

/-- The root of the preposition of (47), (48) and [anand-hardt-mccloskey-2025]. The paper does not
say that *to* is a root, but (49d) needs it to be for (48b): an extra functional head is no
clash. -/
def preposition : Root := ⟨0⟩

/-- An analysis gives each surface voice of each language a structure. -/
abbrev Analysis := Glottocode → _root_.Voice → Verb

/-- The feature bundle of a site, one part per kind of head: a Voice head, the features of a v, and
the roots. -/
abbrev Bundle :=
  WithBot Head × (Flat (List LittleV) × Flat SelStack × Flat Unit) × Flat (List Root)

instance (a b : Bundle) : Decidable (a = b) := decidable_of_iff _ Prod.ext_iff.symm

namespace Analysis

/-- The structure an analysis gives a form. -/
def verb (f : Analysis) (x : Form) : Verb := f x.language x.voice

/-- The bundle an analysis gives each site of a form. -/
def content (f : Analysis) (x : Form) : Site → Bundle
  | .head .Voice => ((f.verb x).voice, ⊥, ⊥)
  | .head .v => (⊥, ((f.verb x).events, (f.verb x).selection, (f.verb x).d), ⊥)
  | .head .V => (⊥, ⊥, x.roots)
  | .adjunct .Voice => (⊥, ⊥, x.high)
  | _ => ⊥

end Analysis

/-- The structures the paper gives the voices of each language. -/
def structures : List (Glottocode × List (_root_.Voice × Verb)) :=
  [(.kiche, [(Kiche.active .radical, kicheTransitive),
      (Kiche.absolutiveAntipassive .radical, kicheAntipassive),
      (Kiche.agentFocus .radical, kicheAgentFocus), (Kiche.simplePassive .radical, passiveD),
      (intransitiveVoice, {})]),
    (.kaqchikel, [(Kaqchikel.active, kaqchikelTransitive),
      (Kaqchikel.antipassive, kaqchikelAntipassive),
      (Kaqchikel.agentFocus .radical, kaqchikelAgentFocus), (Kaqchikel.passive, kaqchikelPassive),
      (intransitiveVoice, {})]),
    (.english, [(_root_.Voice.active, activeD), (implicitVoice, activeImplicit),
      (_root_.Voice.passive, passiveD), (_root_.Voice.anticausative, inchoative),
      (_root_.Voice.causative, causative)]),
    (.italian, [(_root_.Voice.active, activeD), (_root_.Voice.reflexive, seReflexive)]),
    (.serbianCroatianBosnian, [(_root_.Voice.active, activeD),
      (_root_.Voice.reflexive, seReflexive)])]

/-- The paper's analysis. -/
def paper : Analysis := fun l v ↦ ((structures.lookup l).bind (List.lookup v)).getD {}

/-! ### The conditions of (49) -/

/-- A Syntactic Identity Condition on the bundles of the antecedent and the elided clause. -/
abbrev SIC := Ellipsis clausalSpine → (Site → Bundle) → (Site → Bundle) → Prop

/-- Nondistinctness, on the argument domain, which leaves out T and polarity. -/
def nondistinct : SIC := fun e a t ↦ e.Nondistinct a t

instance (e : Ellipsis clausalSpine) (a t : Site → Bundle) : Decidable (nondistinct e a t) :=
  inferInstanceAs (Decidable (e.Nondistinct _ _))

/-- The grid of (49): the two clauses stand in `R` at the sites of `D` inside the deletion domain.
(49a) is `Eq` on the verbal spine, (49b) and (49c) are `Eq` on an argument structure and an eventive
core, and (49d) as printed is `Compat` on everything. -/
def relatedOn (R : Bundle → Bundle → Prop) (D : Set Site) : SIC :=
  fun e a t ↦ ∀ x ∈ D ∩ e.domain, R (a x) (t x)

/-! ### The rows -/

/-- An example: an ellipsis with its antecedent, elided form and the role of its remnant, if a core
one, or a causative with the form its vCAUS merges on. -/
inductive Clause
  | ellipsis (e : Ellipsis clausalSpine) (a t : Form) (ρ : Option ArgumentRole)
  | causative (base : Form)
  deriving DecidableEq

/-- The example is licit under a condition and an analysis: an ellipsis meets the condition and a
remnant in the role P has a source in the site, and vCAUS merges on a vP, not a VoiceP (p. 26), as
its selection requires. -/
def Clause.Licit (C : SIC) (f : Analysis) : Clause → Prop
  | .ellipsis e a t ρ =>
    C e (f.content a) (f.content t) ∧ (ρ = some .P → (f.verb t).SelectsObject)
  | .causative b => (f.verb b).voice = ⊥

instance (f : Analysis) : DecidablePred (Clause.Licit nondistinct f)
  | .ellipsis _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .causative _ => inferInstanceAs (Decidable (_ = _))

/-- An example of the paper with its judgment. -/
structure Row where
  /-- The example. -/
  clause : Clause
  /-- Its judgment. -/
  judgment : Judgment

/-- The English active with a preposition in situ. -/
def activeTo : Form :=
  { language := .english, voice := _root_.Voice.active, roots := ↑[preposition] }

/-- The English active with a preposition in a movement tail. -/
def activeTail : Form := { language := .english, voice := _root_.Voice.active, roots := ⊥ }

/-- The English active with a preposition in situ in an adjunct of VoiceP. -/
def activeHigh : Form :=
  { language := .english, voice := _root_.Voice.active, high := ↑[preposition] }

/-- The forms of a row, by the name its features give them. -/
def formsOf : List (Glottocode × List (String × Form)) :=
  let of (l : Glottocode) (v : _root_.Voice) : Form := { language := l, voice := v }
  [(.kiche, [("antipassive", of .kiche (Kiche.absolutiveAntipassive .radical)),
      ("transitive", of .kiche (Kiche.active .radical)),
      ("agentFocus", of .kiche (Kiche.agentFocus .radical)),
      ("passive", of .kiche (Kiche.simplePassive .radical)),
      ("intransitive", of .kiche intransitiveVoice)]),
    (.kaqchikel, [("antipassive", of .kaqchikel Kaqchikel.antipassive),
      ("transitive", of .kaqchikel Kaqchikel.active),
      ("agentFocus", of .kaqchikel (Kaqchikel.agentFocus .radical)),
      ("passive", of .kaqchikel Kaqchikel.passive),
      ("intransitive", of .kaqchikel intransitiveVoice)]),
    (.english, [("transitive", of .english _root_.Voice.active), ("transitiveTo", activeTo),
      ("transitiveTail", activeTail), ("intransitive", of .english implicitVoice),
      ("active", of .english _root_.Voice.active), ("passive", of .english _root_.Voice.passive),
      ("inchoative", of .english _root_.Voice.anticausative),
      ("causative", of .english _root_.Voice.causative)]),
    (.italian, [("active", of .italian _root_.Voice.active),
      ("reflexive", of .italian _root_.Voice.reflexive)]),
    (.serbianCroatianBosnian, [("active", of .serbianCroatianBosnian _root_.Voice.active),
      ("reflexive", of .serbianCroatianBosnian _root_.Voice.reflexive)])]

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
      match ex.feature? "order" with
      | some "caus" => pure (Clause.causative (← ex.parse? "base" forms))
      | some "causThenBase" =>
        pure (Clause.causative { language := ex.language, voice := intransitiveVoice })
      | _ => none
    | _ => none
  pure ⟨clause, ex.judgment⟩

/-- Read a row of [anand-hardt-mccloskey-2025]: a preposition without a counterpart in the
antecedent, in situ in the argument domain if it marks an argument and in an adjunct of VoiceP if
not. -/
def Row.ofStranded (ex : Datum) : Option Row := do
  let t ← ex.parse? "ppType" [("argument", activeTo), ("nonargument", activeHigh)]
  pure ⟨.ellipsis sluicing { language := .english, voice := _root_.Voice.active } t none,
    ex.judgment⟩

/-- The paper's examples and the stranded prepositions of [anand-hardt-mccloskey-2025]. -/
def rows : List Row :=
  Examples.all.filterMap Row.ofDatum ++
    AnandHardtMcCloskey2025.Examples.all.filterMap Row.ofStranded

theorem length_rows :
    rows.length = Examples.all.length + AnandHardtMcCloskey2025.Examples.all.length := by
  decide +kernel

/-- A condition and an analysis predict the judgments. -/
def Predicts (C : SIC) (f : Analysis) : Prop :=
  ∀ r ∈ rows, (.marginal ≤ r.judgment ↔ r.clause.Licit C f)

/-- Nondistinctness on the argument domain, with the paper's analysis, predicts the judgments: the
K'iche' mismatch, its absence in Kaqchikel, the English voice and transitivity alternations, the
stranded prepositions and the reflexives of Italian and BCS. -/
theorem rows_predicted : Predicts nondistinct paper := by
  unfold Predicts
  decide +kernel

/-! ### Identity and the domain -/

/-- The K'iche' antipassive and active as forms. -/
abbrev kAP : Form := { language := .kiche, voice := Kiche.absolutiveAntipassive .radical }

/-- The K'iche' active. -/
abbrev kTV : Form := { language := .kiche, voice := Kiche.active .radical }

/-- No analysis makes identity predict the judgments, on any domain: the English alternation (70b)
puts v in the domain, and (1) then needs the antipassive and the transitive to agree at v, though
only the transitive can be the source of an object remnant. -/
theorem not_predicts_eq (D : Set Site) (f : Analysis) : ¬ Predicts (relatedOn Eq D) f := by
  intro h
  have hv : Site.head .v ∈ D := by
    by_contra hD
    obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows, r.clause = .ellipsis vpEllipsis
        { language := .english, voice := _root_.Voice.anticausative }
        { language := .english, voice := _root_.Voice.causative } none ∧
        ¬ .marginal ≤ r.judgment := by
      decide +kernel
    refine hj ((h r hr).2 (hc ▸ ⟨fun x hx ↦ ?_, by simp⟩))
    have hx' : ∀ y ∈ clausalSpine.sites, vpEllipsis.Deletes y →
        y = .head .V ∨ y = .adjunct .V ∨ y = .head .v := by
      decide +kernel
    rcases hx' x (ClauseSpine.Deletes.mem_sites hx.2) hx.2 with rfl | rfl | rfl
    · rfl
    · rfl
    · exact absurd hx.1 hD
  obtain ⟨r₁, hr₁, hc₁, hj₁⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing kAP kTV (some .P) ∧
      .marginal ≤ r.judgment := by
    decide +kernel
  obtain ⟨r₂, hr₂, hc₂, hj₂⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing kAP kAP (some .P) ∧
      ¬ .marginal ≤ r.judgment := by
    decide +kernel
  have hl := (h r₁ hr₁).1 hj₁
  rw [hc₁] at hl
  obtain ⟨he, hs⟩ := hl
  have hat := he (.head .v) ⟨hv, mem_domain.2 (by decide)⟩
  simp only [Analysis.content, Prod.mk.injEq, true_and, and_true] at hat
  refine hj₂ ((h r₂ hr₂).2 (hc₂ ▸ ⟨fun _ _ ↦ rfl, fun _ ↦ ?_⟩))
  rcases hs rfl with hd | hsel
  · exact .inl (hat.2.2.trans hd)
  · exact .inr (hat.2.1.trans hsel)

/-- No analysis predicts the judgments uniformly across languages, under any condition, one label
covering different structures: the K'iche' and the Kaqchikel antipassive are the same surface voice,
and only the K'iche' one (55) can antecede an active in the ellipsis site (53). -/
theorem not_predicts_uniform (C : SIC) (g : _root_.Voice → Verb) :
    ¬ Predicts C (fun _ ↦ g) := by
  intro h
  obtain ⟨r₁, hr₁, hc₁, hj₁⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing kAP kTV (some .P) ∧
      .marginal ≤ r.judgment := by
    decide +kernel
  obtain ⟨r₂, hr₂, hc₂, hj₂⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing
      { language := .kaqchikel, voice := Kaqchikel.antipassive }
      { language := .kaqchikel, voice := Kaqchikel.active } (some .P) ∧
      ¬ .marginal ≤ r.judgment := by
    decide +kernel
  have hl := (h r₁ hr₁).1 hj₁
  rw [hc₁] at hl
  exact hj₂ ((h r₂ hr₂).2 (hc₂ ▸ hl))

/-- The sites an analysis can give a nonempty bundle. -/
def contentful : List Site := [.head .V, .head .v, .head .Voice, .adjunct .Voice]

theorem Analysis.content_of_notMem (f : Analysis) (a : Form) {x : Site} (hx : x ∉ contentful) :
    f.content a x = ⊥ := by
  fun_cases Analysis.content f a x <;> simp_all [contentful]

theorem relatedOn_compat_of_ne {D : Set Site} {y : Site} (hy : y ∉ D) {e : Ellipsis clausalSpine}
    {f : Analysis} {a t : Form}
    (h : ∀ x ∈ contentful, x ≠ y → Compat (f.content a x) (f.content t x)) :
    relatedOn Compat D e (f.content a) (f.content t) := fun x hx ↦ by
  by_cases hc : x ∈ contentful
  · exact h x hc (ne_of_mem_of_not_mem hx.1 hy)
  · rw [f.content_of_notMem a hc]
    exact bot_compat _

/-- The judgments fix the domain of nondistinctness: with the paper's analysis they are predicted
exactly on the sets of sites containing V (48b), v (70b) and Voice (69a) and not the adjunction site
of VoiceP (13a). -/
theorem predicts_on_iff {D : Set Site} :
    Predicts (relatedOn Compat D) paper ↔
      ({.head .V, .head .v, .head .Voice} : Set Site) ⊆ D ∧ .adjunct .Voice ∉ D := by
  refine ⟨fun h ↦ ⟨fun x hx ↦ by_contra fun hxD ↦ ?_, fun hD ↦ ?_⟩,
    fun ⟨hD, hA⟩ r hr ↦ (rows_predicted r hr).trans ?_⟩
  · rcases hx with rfl | rfl | rfl
    · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing
          { language := .english, voice := _root_.Voice.active } activeTo none ∧
          ¬ .marginal ≤ r.judgment := by
        decide +kernel
      exact hj ((h r hr).2 (hc ▸ ⟨relatedOn_compat_of_ne hxD (by decide +kernel), by simp⟩))
    · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows, r.clause = .ellipsis vpEllipsis
          { language := .english, voice := _root_.Voice.anticausative }
          { language := .english, voice := _root_.Voice.causative } none ∧
          ¬ .marginal ≤ r.judgment := by
        decide +kernel
      exact hj ((h r hr).2 (hc ▸ ⟨relatedOn_compat_of_ne hxD (by decide +kernel), by simp⟩))
    · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing
          { language := .english, voice := _root_.Voice.passive }
          { language := .english, voice := _root_.Voice.active } (some .A) ∧
          ¬ .marginal ≤ r.judgment := by
        decide +kernel
      exact hj ((h r hr).2 (hc ▸ ⟨relatedOn_compat_of_ne hxD (by decide +kernel), by simp⟩))
  · obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing
        { language := .english, voice := _root_.Voice.active } activeHigh none ∧
        .marginal ≤ r.judgment := by
      decide +kernel
    have hl := (h r hr).1 hj
    rw [hc] at hl
    exact absurd (hl.1 _ ⟨hD, mem_domain.2 (by decide)⟩) (by decide +kernel)
  · rcases r.clause with ⟨e, a, t, ρ⟩ | base
    · refine and_congr_left' ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
      · by_cases hc : x ∈ contentful
        · simp only [contentful, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl
          · exact h ⟨hx.2, by decide⟩
          · exact h ⟨hx.2, by decide⟩
          · exact h ⟨hx.2, by decide⟩
          · exact absurd hx.1 hA
        · rw [paper.content_of_notMem a hc]
          exact bot_compat _
      · by_cases hc : x ∈ contentful
        · simp only [contentful, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl
          · exact h _ ⟨hD (by simp), hx.1⟩
          · exact h _ ⟨hD (by simp), hx.1⟩
          · exact h _ ⟨hD (by simp), hx.1⟩
          · exact absurd hx.2 (by decide)
        · rw [paper.content_of_notMem a hc]
          exact bot_compat _
    · rfl

-- [anand-hardt-mccloskey-2025]
theorem T_notMem_of_lowerSet {D : Set Site} (h : Predicts (relatedOn Compat D) paper)
    (hD : ∀ x y, clausalSpine.rank x ≤ clausalSpine.rank y → y ∈ D → x ∈ D) : .head .T ∉ D :=
  fun hT ↦ (predicts_on_iff.1 h).2 (hD _ _ (by decide) hT)

-- (52), (51), (1), (69a), footnote 18
theorem not_predicts_paper_of_equivalence {R : Bundle → Bundle → Prop} (hR : Equivalence R)
    (D : Set Site) : ¬ Predicts (relatedOn R D) paper := by
  intro h
  have licit : ∀ {a t : Form} {ρ : Option ArgumentRole},
      (∃ r ∈ rows, r.clause = .ellipsis sluicing a t ρ ∧ .marginal ≤ r.judgment) →
        Site.head .Voice ∈ D →
          R (paper.content a (.head .Voice)) (paper.content t (.head .Voice)) := by
    rintro a t ρ ⟨r, hr, hc, hj⟩ hD
    have hl := (h r hr).1 hj
    rw [hc] at hl
    exact hl.1 _ ⟨hD, mem_domain.2 (by decide)⟩
  obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing
      { language := .english, voice := _root_.Voice.passive }
      { language := .english, voice := _root_.Voice.active } (some .A) ∧
      ¬ .marginal ≤ r.judgment := by
    decide +kernel
  refine hj ((h r hr).2 (hc ▸ ⟨fun x hx ↦ ?_, by simp⟩))
  by_cases hV : x = .head .Voice
  · subst hV
    have h₁ := licit (a := { language := .kaqchikel, voice := Kaqchikel.passive })
      (t := { language := .kaqchikel, voice := Kaqchikel.agentFocus .radical }) (ρ := some .A)
      (by decide +kernel) hx.1
    have h₂ := licit (a := { language := .kaqchikel, voice := Kaqchikel.agentFocus .radical })
      (t := { language := .kaqchikel, voice := Kaqchikel.active }) (ρ := some .P)
      (by decide +kernel) hx.1
    have h₃ := licit (a := kAP) (t := kTV) (ρ := some .P) (by decide +kernel) hx.1
    have e₁ : paper.content { language := .english, voice := _root_.Voice.passive } (.head .Voice) =
        paper.content { language := .kaqchikel, voice := Kaqchikel.passive } (.head .Voice) := by
      decide +kernel
    have e₂ : paper.content { language := .english, voice := _root_.Voice.active } (.head .Voice) =
        paper.content kAP (.head .Voice) := by
      decide +kernel
    rw [e₁, e₂]
    exact hR.trans (hR.trans h₁ h₂) (hR.symm h₃)
  · have he : ∀ y ∈ contentful, y ≠ .head .Voice →
        paper.content { language := .english, voice := _root_.Voice.passive } y =
          paper.content { language := .english, voice := _root_.Voice.active } y := by
      decide +kernel
    by_cases hc : x ∈ contentful
    · rw [he x hc hV]
      exact hR.refl _
    · rw [paper.content_of_notMem _ hc, paper.content_of_notMem _ hc]
      exact hR.refl _

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

/-! ### What the rows force, and what rests on one row -/

-- (69a), (71)
theorem voice_clash_of_predicts {f : Analysis} (h : Predicts nondistinct f) :
    ¬ Compat (f .english _root_.Voice.passive).voice (f .english _root_.Voice.active).voice := by
  intro hc
  obtain ⟨r₁, hr₁, hc₁, hj₁⟩ : ∃ r ∈ rows, r.clause = .ellipsis vpEllipsis
      { language := .english, voice := _root_.Voice.passive }
      { language := .english, voice := _root_.Voice.active } none ∧
      .marginal ≤ r.judgment := by
    decide +kernel
  obtain ⟨r₂, hr₂, hc₂, hj₂⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing
      { language := .english, voice := _root_.Voice.passive }
      { language := .english, voice := _root_.Voice.active } (some .A) ∧
      ¬ .marginal ≤ r.judgment := by
    decide +kernel
  have hl := (h r₁ hr₁).1 hj₁
  rw [hc₁] at hl
  refine hj₂ ((h r₂ hr₂).2 (hc₂ ▸ ⟨fun x hx ↦ ?_, by simp⟩))
  by_cases hm : x ∈ contentful
  · simp only [contentful, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact compat_self _
    · exact hl.1 ⟨by decide, by decide⟩
    · exact compat_prod_iff.2 ⟨hc, compat_self _⟩
    · exact absurd hx.2 (by decide)
  · rw [f.content_of_notMem _ hm]
    exact bot_compat _

-- (63), (65)
theorem antipassive_voice_of_predicts {C : SIC} {f : Analysis} (h : Predicts C f) :
    (f .kiche (Kiche.absolutiveAntipassive .radical)).voice ≠ ⊥ ∧
      (f .kaqchikel Kaqchikel.antipassive).voice = ⊥ := by
  obtain ⟨r₁, hr₁, hc₁, hj₁⟩ : ∃ r ∈ rows, r.clause = .causative kAP ∧
      ¬ .marginal ≤ r.judgment := by
    decide +kernel
  obtain ⟨r₂, hr₂, hc₂, hj₂⟩ : ∃ r ∈ rows, r.clause =
      .causative { language := .kaqchikel, voice := Kaqchikel.antipassive } ∧
      .marginal ≤ r.judgment := by
    decide +kernel
  have hl := (h r₂ hr₂).1 hj₂
  rw [hc₂] at hl
  exact ⟨fun hv ↦ hj₁ ((h r₁ hr₁).2 (hc₁ ▸ hv)), hl⟩

-- (51)
theorem selection_le_of_predicts {f : Analysis} (h : Predicts nondistinct f)
    (hTV : (f .kaqchikel Kaqchikel.active).selection = ↑vTV) :
    (f .kaqchikel (Kaqchikel.agentFocus .radical)).selection ≤ (↑vTV : Flat SelStack) := by
  obtain ⟨r, hr, hc, hj⟩ : ∃ r ∈ rows, r.clause = .ellipsis sluicing
      { language := .kaqchikel, voice := Kaqchikel.agentFocus .radical }
      { language := .kaqchikel, voice := Kaqchikel.active } (some .P) ∧
      .marginal ≤ r.judgment := by
    decide +kernel
  have hl := (h r hr).1 hj
  rw [hc] at hl
  have hb := (compat_prod_iff.1 (compat_prod_iff.1 (compat_prod_iff.1
    (hl.1 (x := .head .v) ⟨by decide, by decide⟩)).2).1).2
  have hs : Compat (f .kaqchikel (Kaqchikel.agentFocus .radical)).selection
      (↑vTV : Flat SelStack) :=
    hTV ▸ (compat_prod_iff.1 hb).1
  rcases eq_or_ne (f .kaqchikel (Kaqchikel.agentFocus .radical)).selection ⊥ with hb' | hb'
  · exact hb' ▸ bot_le
  · obtain ⟨σ, hσ⟩ := Flat.ne_bot_iff_exists.1 hb'
    rw [hσ] at hs ⊢
    rw [Flat.compat_coe_coe.1 hs]

/-- Ranero's Kaqchikel antipassive (56a): Voice[AP] over the v of a transitive. -/
def raneroAntipassive : Verb :=
  { voice := ({ agentive with value := .antipassive } : Head), selection := ↑vTV }

/-- The paper's analysis with Ranero's antipassive. -/
def ranero : Analysis := fun l v ↦
  if l = .kaqchikel ∧ v = Kaqchikel.antipassive then raneroAntipassive else paper l v

-- (56), (57), (65)
theorem ranero_mispredicts_iff : ∀ r ∈ rows,
    ((.marginal ≤ r.judgment ↔ r.clause.Licit nondistinct ranero) ↔
      r.clause ≠ .causative { language := .kaqchikel, voice := Kaqchikel.antipassive }) := by
  decide +kernel

/-- The structures of [burukina-polinsky-2025]'s Table 3, with its selection read privatively: vITV
and vAF select a nominal, vTV selects none, and VoiceTV selects one and bears [ERG]. -/
def table : Analysis := fun l v ↦
  if l = .kaqchikel then
    if v = Kaqchikel.active then { voice := voiceErg, selection := ↑vTV }
    else if v = Kaqchikel.antipassive ∨ v = Kaqchikel.agentFocus .radical then { d := ↑() }
    else paper l v
  else paper l v

-- (53), p. 717 of [burukina-polinsky-2025]
theorem table_mispredicts_iff : ∀ r ∈ rows,
    ((.marginal ≤ r.judgment ↔ r.clause.Licit nondistinct table) ↔
      r.clause ≠ .ellipsis sluicing { language := .kaqchikel, voice := Kaqchikel.antipassive }
        { language := .kaqchikel, voice := Kaqchikel.active } (some .P)) := by
  decide +kernel

/-- One analysis of all the languages: the K'iche' structures, wherever a surface voice has them. -/
def uniform : _root_.Voice → Verb := fun v ↦
  (List.lookup v [(Kiche.active .radical, kicheTransitive),
    (Kiche.absolutiveAntipassive .radical, kicheAntipassive),
    (Kiche.agentFocus .radical, kicheAgentFocus), (Kiche.simplePassive .radical, passiveD),
    (Kaqchikel.agentFocus .radical, kicheAgentFocus), (Kaqchikel.passive, passiveD),
    (implicitVoice, activeImplicit), (_root_.Voice.anticausative, inchoative),
    (_root_.Voice.causative, causative), (_root_.Voice.reflexive, seReflexive)]).getD {}

-- (53), (65), p. 28
theorem uniform_mispredicts_iff : ∀ r ∈ rows,
    ((.marginal ≤ r.judgment ↔ r.clause.Licit nondistinct fun _ ↦ uniform) ↔
      r.clause ≠ .ellipsis sluicing { language := .kaqchikel, voice := Kaqchikel.antipassive }
        { language := .kaqchikel, voice := Kaqchikel.active } (some .P) ∧
      r.clause ≠ .causative { language := .kaqchikel, voice := Kaqchikel.antipassive }) := by
  decide +kernel

/-- The paper's analysis without [ERG]. -/
def withoutErg : Analysis := fun l v ↦
  if (paper l v).voice = ↑voiceErg then { paper l v with voice := agentive } else paper l v

-- (43), which no row tests
theorem predicts_withoutErg : Predicts nondistinct withoutErg := by
  unfold Predicts
  decide +kernel

-- (43)
theorem kicheAntipassive_le : paper.content kAP ≤ paper.content kTV := fun x ↦ by
  have ha : paper.verb kAP = kicheAntipassive := by decide +kernel
  have ht : paper.verb kTV = kicheTransitive := by decide +kernel
  by_cases hx : x ∈ contentful
  · simp only [contentful, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact le_rfl
    · simp only [Analysis.content, ha, ht]
      exact ⟨le_rfl, ⟨le_rfl, le_rfl, bot_le⟩, le_rfl⟩
    · simp only [Analysis.content, ha, ht]
      exact ⟨WithBot.coe_le_coe.2 ⟨rfl, rfl, le_rfl, le_rfl, le_rfl, bot_le⟩, le_rfl, le_rfl⟩
    · exact le_rfl
  · simp [Analysis.content_of_notMem _ _ hx]

-- `Merchant2013.deletes_v`
theorem kiche_alternation_survives :
    sluicing.Deletes (.head .v) ∧ (paper.verb kAP).d ≠ (paper.verb kTV).d ∧
      nondistinct sluicing (paper.content kAP) (paper.content kTV) :=
  ⟨by decide, by decide +kernel, nondistinct_of_le kicheAntipassive_le⟩

-- pp. 30–31, (70b)
theorem d_alternant_overgenerates :
    nondistinct vpEllipsis (Analysis.content (fun _ _ ↦ {}) kAP)
      (Analysis.content (fun _ _ ↦ { d := ↑() }) kAP) := by
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
