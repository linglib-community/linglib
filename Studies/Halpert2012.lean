module

public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Fragments.Zulu.Clause
public import Linglib.Data.Examples.Halpert2012

/-!
# Halpert (2012): Argument Licensing and Agreement in Zulu

Halpert argues that Zulu has structural licensing, but by heads other than the familiar ones. A
Licensing head L⁰ above vP probes every phrase in vP and licenses the highest, and the verb V⁰
licenses its complement when a causative or applicative head has passed it a case feature, the
pattern Halpert relates to Burzio's generalization. Nominals with the augment vowel and clauses
headed by *ukuthi* are licensed intrinsically, while augmentless nominals and clauses headed by
*sengathi* must be local to a licensing head in whichever vP they end up, and augmented nominals
still intervene. An augmentless embedded subject may thus stay in the embedded vP or raise into the
matrix vP, but not stop between. The verb shows L⁰'s probing, conjoint when it finds a goal and
disjoint when it fails, and A-movement out of vP precedes the probing, the one order Chomsky's
Activity Condition leaves.

## Main definitions

* `Halpert2012.Clause`: a clause after A-movement, its vP split at V⁰'s c-command domain.
* `Halpert2012.Clause.Converges`: every phrase needing licensing is reached by L⁰ or V⁰.
* `Halpert2012.Clause.spellout`: the verb form L⁰'s probing determines.

## Main results

* `Halpert2012.Clause.converges_iff`: the licensing generalization of §3.3.3.
* `Halpert2012.Clause.countP_le_one`, `Halpert2012.Clause.countP_le_two`: one phrase needing
  licensing in a vP without extensions, two with them.
* `Halpert2012.Clause.spellout_eq_disjoint_iff`: the verb is disjoint iff vP is empty.
* `Halpert2012.search_eq_search_evacuate`: under Activity, probing before A-movement reaches the
  goal probing after it reaches.
* `Halpert2012.Clause.rows`: the paradigms of chapters 3 and 4.

## Implementation notes

Phrases that left vP or attach above it are listed in `Clause.outside` without positions. A row
records the clause it is about and, when that clause is embedded, the clause embedding it, each
licensed by its own L⁰; a raised phrase is recorded where it lands, and temporal adverbs whose
position the source leaves open are not recorded. A prefixed oblique enters as the nominal inside
it (§4.4.2), and noun class, which plays no role in licensing, is not recorded. Every row with an
augmentless nominal is in a downward-entailing context, the semantic condition of §3.2.

## TODO

That *fisa* 'wish' does not raise its embedded subject for most speakers ((152b)) is a lexical
fact outside the model. Some speakers accept (141b) (footnote 8).

## References

* [halpert-2012]
* [burzio-1986]
* [chomsky-2000]
* [chomsky-2001]
-/

@[expose] public section

namespace Halpert2012

open Minimalist

/-! ### Goals -/

/-- A goal is a phrase that L⁰ can probe, and every phrase inside vP is one (§4.4). -/
inductive Goal where
  /-- The goal is a nominal, with or without the augment vowel. -/
  | nominal (augment : Bool)
  /-- The goal is a clause, headed by a complementizer or by none. -/
  | clause (c : Option Complementizer)
  /-- The goal is an adverb, such as *kahle* 'well'. -/
  | adverb
  deriving DecidableEq, Repr

/-- A phrase needs structural licensing when it has no intrinsic licenser, that is, when it is a
nominal without the augment or a clause headed by *sengathi* (Table 4.1). -/
def Goal.NeedsL : Goal → Prop
  | .nominal augment => augment = false
  | .clause c => c = some Zulu.sengathi
  | .adverb => False

instance : DecidablePred Goal.NeedsL
  | .nominal _ => inferInstanceAs (Decidable (_ = _))
  | .clause _ => inferInstanceAs (Decidable (_ = _))
  | .adverb => inferInstanceAs (Decidable False)

/-! ### Licensing -/

/-- An extension is a verbal suffix that introduces an argument and a case feature, the causative
*-is-* or the applicative *-el-* (§3.3.2). -/
inductive Extension where
  | caus
  | appl
  deriving DecidableEq, Repr

/-- A clause after A-movement (§4.5) records the phrases outside vP, the phrases in vP above V⁰'s
c-command domain from the top, V⁰'s c-command domain with its complement first, and the verb's
extensions. -/
structure Clause where
  outside : List Goal := []
  above : List Goal := []
  vDomain : List Goal := []
  extensions : List Extension := []
  deriving DecidableEq, Repr

namespace Clause

variable {c : Clause}

/-- `c.vP` lists the phrases in vP from the top, L⁰'s search domain. -/
def vP (c : Clause) : List Goal := c.above ++ c.vDomain

/-- L⁰ is the indiscriminate probe, which every phrase satisfies, so that its search ends at the
highest phrase in vP (pp. 168, 174). -/
def L : Probe Goal := Probe.indiscriminate

/-- V⁰ probes its c-command domain indiscriminately (142b). -/
def V : Probe Goal := Probe.indiscriminate

/-- V⁰ licenses when an extension has passed it its case feature (142). There is one V⁰ however
many extensions the verb carries, so a causative and an applicative together add one licenser,
not two ((140), (141)). -/
def Inherits (c : Clause) : Prop := c.extensions ≠ []

instance : DecidablePred Inherits := fun c ↦ inferInstanceAs (Decidable (c.extensions ≠ []))

/-- A clause converges when no phrase outside vP needs licensing and every phrase in vP that does
is reached by L⁰'s search or, when V⁰ has inherited case, by V⁰'s search of its domain ((113),
(122)). L⁰'s search reaches into V⁰'s domain only when nothing is above it, and then it reaches
the phrase V⁰'s search reaches, so with case inheritance L⁰ licenses above V⁰'s domain and V⁰
within it. -/
def Converges (c : Clause) : Prop :=
  (∀ g ∈ c.outside, ¬ g.NeedsL) ∧
    if c.Inherits then
      L.AllLicensed (·.NeedsL) c.above ∧ V.AllLicensed (·.NeedsL) c.vDomain
    else L.AllLicensed (·.NeedsL) c.vP

instance : DecidablePred Converges := fun c ↦ by unfold Converges; infer_instance

/-- A clause converges iff only the highest phrase of vP, or of V⁰'s domain when nothing is above or
case is inherited, needs licensing (§3.3.3, p. 112). -/
theorem converges_iff :
    c.Converges ↔ (∀ g ∈ c.outside, ¬ g.NeedsL) ∧ (∀ g ∈ c.above.tail, ¬ g.NeedsL) ∧
      (∀ g ∈ c.vDomain.tail, ¬ g.NeedsL) ∧
        ∀ g ∈ c.vDomain.head?, g.NeedsL → c.above = [] ∨ c.Inherits := by
  unfold Converges vP L V
  by_cases hi : c.Inherits <;>
    simp only [hi, ↓reduceIte, Probe.indiscriminate_allLicensed_iff, or_true, implies_true,
      and_true, or_false]
  rcases c.above with _ | ⟨u, us⟩ <;> rcases c.vDomain with _ | ⟨l, ls⟩ <;>
    simp [or_imp, forall_and]
  tauto

/-- Without an extension one phrase in vP at most needs licensing (p. 93, (127)). -/
theorem countP_le_one (h : c.Converges) (hc : c.extensions = []) :
    c.vP.countP (decide ·.NeedsL) ≤ 1 := by
  have hi : ¬ c.Inherits := not_not.2 hc
  simp only [Converges, hi, ↓reduceIte] at h
  exact h.2.countP_le_one

/-- Two phrases in vP at most need licensing, whatever extensions the verb carries (p. 105,
(135), (141)). -/
theorem countP_le_two (h : c.Converges) : c.vP.countP (decide ·.NeedsL) ≤ 2 := by
  by_cases hi : c.Inherits
  · simp only [Converges, hi, ↓reduceIte] at h
    rw [vP, List.countP_append]
    have := h.2.1.countP_le_one
    have := h.2.2.countP_le_one
    omega
  · simp only [Converges, hi, ↓reduceIte] at h
    have := h.2.countP_le_one
    omega

end Clause

/-! ### The conjoint and disjoint verb forms -/

/-- A present-tense verb is conjoint, with ∅-, or disjoint, with *ya-* (§4.2). -/
inductive VerbForm where
  | conjoint
  | disjoint
  deriving DecidableEq, Repr

namespace Clause

variable {c : Clause}

/-- The verb is conjoint when L⁰'s search finds a goal in vP and disjoint, the overt member, when
it fails, a failure that does not crash the derivation (§4.3, p. 166). -/
def spellout (c : Clause) : VerbForm :=
  if (L.search c.vP).isSome then .conjoint else .disjoint

/-- The verb is disjoint iff vP is empty after A-movement, the generalization (180). -/
theorem spellout_eq_disjoint_iff : c.spellout = .disjoint ↔ c.vP = [] := by
  cases h : c.vP <;> simp [spellout, h, L]

end Clause

/-! ### Timing -/

/-- `evacuate base` is the vP left after A-movement, where `base` lists the phrases of vP from the
top, each marked with whether it moves out (§4.5). -/
def evacuate (base : List (Goal × Bool)) : List Goal := (base.filter (!·.2)).map Prod.fst

/-- Under the Activity Condition (270), L⁰ probing before A-movement reaches the same goal as after,
so free ordering derives nothing new (§4.5.1). -/
theorem search_eq_search_evacuate {base : List (Goal × Bool)} (h : ∀ x ∈ base.head?, x.2 = false) :
    Clause.L.search (base.map Prod.fst) = Clause.L.search (evacuate base) := by
  cases base with
  | nil => rfl
  | cons x t =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'] at h
    simp [evacuate, h, Clause.L, Probe.search, Probe.indiscriminate, Probe.relativized]

/-- Without Activity, L⁰ probing before the subject moves would spell out the conjoint where
(184a) is disjoint. -/
example : (Clause.L.search [.nominal true]).isSome ∧
    Clause.L.search (evacuate [(.nominal true, true)]) = none := by
  decide

/-! ### The paradigms -/

/-- `Goal.ofCode s` is the phrase that a row's code `s` names. -/
def Goal.ofCode : String → Option Goal
  | "+aug" => some (.nominal true)
  | "-aug" => some (.nominal false)
  | "cp" => some (.clause none)
  | "ukuthi" => some (.clause (some Zulu.ukuthi))
  | "sengathi" => some (.clause (some Zulu.sengathi))
  | "adverb" => some .adverb
  | _ => none

/-- `Extension.ofCode s` is the extension that a row's code `s` names. -/
def Extension.ofCode : String → Option Extension
  | "caus" => some .caus
  | "appl" => some .appl
  | _ => none

/-- `Clause.ofKeys row outside above vDomain extension` is the clause whose phrases and
extensions the row lists under the four keys. -/
def Clause.ofKeys (row : Datum) (outside above vDomain extension : String) : Option Clause := do
  let outside ← (row.features outside).mapM Goal.ofCode
  let above ← (row.features above).mapM Goal.ofCode
  let vDomain ← (row.features vDomain).mapM Goal.ofCode
  let extensions ← (row.features extension).mapM Extension.ofCode
  return ⟨outside, above, vDomain, extensions⟩

/-- `Clause.ofRow row` is the clause the row is about. -/
def Clause.ofRow (row : Datum) : Option Clause :=
  Clause.ofKeys row "outside" "above" "vDomain" "extension"

/-- `Clause.matrixOfRow row` is the clause embedding it, empty when the row records none. -/
def Clause.matrixOfRow (row : Datum) : Option Clause :=
  Clause.ofKeys row "matrixOutside" "matrixAbove" "matrixVDomain" "matrixExtension"

/-- `VerbForm.ofRow row` is the verb form the row records, where the alternation shows. -/
def VerbForm.ofRow (row : Datum) : Option VerbForm :=
  row.parse? "verbForm" [("conjoint", .conjoint), ("disjoint", .disjoint)]

example : ∀ row ∈ Examples.all, (Clause.ofRow row).isSome ∧ (Clause.matrixOfRow row).isSome := by
  decide

/-- A sentence of the paradigms of chapters 3 and 4 is acceptable exactly when its clause and the
clause embedding it converge, each licensed by its own L⁰, and its verb form, where recorded,
spells out L⁰'s probing. -/
theorem Clause.rows : ∀ row ∈ Examples.all, ∀ c ∈ Clause.ofRow row, ∀ m ∈ Clause.matrixOfRow row,
    (row.judgment = .acceptable ↔
      m.Converges ∧ c.Converges ∧ ∀ f ∈ VerbForm.ofRow row, c.spellout = f) := by
  decide

end Halpert2012
