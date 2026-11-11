module

public import Linglib.Data.Examples.Aremu2025a
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.Yoruba.Focus
public import Linglib.Fragments.Yoruba.Pronouns
public import Linglib.Fragments.Yoruba.Relativization
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Syntax.Minimalist.Locality.AntiLocality
public import Linglib.Syntax.Reflex
public import Studies.BrananErlewine2023

/-!
# Aremu (2025): Focus sensitivity in Mabia and Yoruboid

In Yorùbá a focus stays in place or fronts before *ni*. A fronted object moves and [meets
islands](##rows_derivable); a fronted subject is resumed and does not. One exclusive operator,
silent or *kàn*, takes its order from the particle on its associate: [*nìkan* excludes what the
prejacent does not entail and *lásán* what ranks higher](##rows_continuations). It can [scope above
a modal that its associate scopes below](##split_scope).

## Implementation notes

* Chapters number their examples apart; a bare number is chapter 3's.
* Anti-locality applies to every link, so derivations keep the AspP of ch. 1 (27), and it covers
  the gap of (203), which p. 115 calls a *that*-trace effect.
* A contextual scale is the entry ch. 5 (50) over [cumulative
  alternatives](##exclusive_reaches_eq), our reading of p. 170.
* Resumption as a last resort (p. 115) is applied to the local subject too, which p. 108 argues
  from islands.

## TODO

* Kasem and Kusaal, whose gapped local subjects (209), (210) anti-locality bars unless they skip
  Spec,TP; additives and scalar additives.
* Object resumption (fn. 60), the verb copy of (161), LF movement (197), (199), and the obviation
  that anti-locality predicts under an embedded *ni*.
* Scope, ellipsis, backward association, the reply to Yip and Adedeji, and the evaluative heads.

## References

* [aremu-2025a]
* [awobuluyi-1978]
* [branan-erlewine-2023]
* [coppock-beaver-2014]
* [erlewine-2016]
* [erlewine-2020]
* [hirsch-2017]
-/

@[expose] public section

namespace Aremu2025a

open Core.Order Reflex OrderDual Focus Set Minimalist Minimalist.LinearizedSyntacticObject
open BrananErlewine2023 (LeftAlignedOn prominent xp)

/-! ### Derivations -/

/-- The focus head with EPP (202-a). -/
def ni : LexicalItem.Token := ⟨.of .Foc [.T] Yoruba.ni.form, 0⟩

/-- The focus head without EPP (202-b). -/
def nullFoc : LexicalItem.Token := ⟨.of .Foc [.T], 1⟩

def tense : LexicalItem.Token := ⟨.of .T [.Asp], 2⟩
def asp : LexicalItem.Token := ⟨.of .Asp [.v], 3⟩
def littleV : LexicalItem.Token := ⟨.of .v [.V], 4⟩
def lexicalV : LexicalItem.Token := ⟨.of .V [.D], 5⟩
def focusDP : LexicalItem.Token := ⟨.of .D [], 6⟩
def pronoun : LexicalItem.Token := ⟨.of .D [], 7⟩
def otherDP : LexicalItem.Token := ⟨.of .D [], 8⟩
def matrixDP : LexicalItem.Token := ⟨.of .D [], 9⟩
def matrixV : LexicalItem.Token := ⟨.of .V [.C], 10⟩
def noun : LexicalItem.Token := ⟨.of .N [.C], 11⟩
def conjunct : LexicalItem.Token := ⟨.of .D [], 12⟩
def embeddedDP : LexicalItem.Token := ⟨.of .D [], 13⟩
def rel : LexicalItem.Token := ⟨.of .C [.T] "tí", 20⟩
def before : LexicalItem.Token := ⟨.of .C [.T] "kí", 21⟩
def ati : LexicalItem.Token := ⟨.of .D [.D] "àti", 22⟩
def wipe : LexicalItem.Token := ⟨.of .C [.T] "wípé", 23⟩
def embeddedNi : LexicalItem.Token := ⟨.of .Foc [.T] Yoruba.ni.form, 24⟩

/-- What the site of the focus is embedded in. -/
inductive Domain
  | matrix | complement | focusClause | relative | adjunct | coordinate
  deriving DecidableEq, Repr

/-- The function of the focus. -/
inductive Associate
  | subject | object
  deriving DecidableEq, Repr

/-- What surfaces at the site of the focus. -/
inductive Site
  | gap | pronoun | inSitu
  deriving DecidableEq, Repr

/-- A focus moves if it leaves a gap, or is an object, whose pronoun does not stop it (191-b). -/
def FocusMoves (a : Associate) (s : Site) : Prop := s = .gap ∨ a = .object ∧ s = .pronoun

instance (a : Associate) (s : Site) : Decidable (FocusMoves a s) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The focused subject, or the pronoun that resumes it. -/
def subjectDP : Site → LexicalItem.Token
  | .pronoun => pronoun
  | _ => focusDP

/-- A clause, ch. 1 (27). -/
def tp (s : LexicalItem.Token) (vp : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
  s * (tense * (asp * (s * (littleV * vp))))

/-- The clause holding the site of the focus. -/
def inner : Associate → Site → LinearizedSyntacticObject
  | .subject, s => tp (subjectDP s) (lexicalV * otherDP)
  | .object, _ => tp otherDP (lexicalV * focusDP)

/-- A clause with the site of the focus in a conjunct. -/
def coordinated : Associate → Site → LinearizedSyntacticObject
  | .subject, s =>
    let c : LinearizedSyntacticObject := subjectDP s * (ati * conjunct)
    c * (tense * (asp * (c * (littleV * (lexicalV * otherDP)))))
  | .object, _ => tp otherDP (lexicalV * (focusDP * (ati * conjunct)))

/-- The clause below the focus head; a moving focus stops at the edge of a complement. -/
def body (d : Domain) (a : Associate) (s : Site) : LinearizedSyntacticObject :=
  let embed (c : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
    tp matrixDP (matrixV * (if FocusMoves a s then focusDP * (wipe * c) else wipe * c))
  match d with
  | .matrix => inner a s
  | .coordinate => coordinated a s
  | .complement => embed (inner a s)
  | .focusClause => embed (embeddedDP * (embeddedNi * inner a s))
  | .relative => tp matrixDP (matrixV * (noun * (rel * inner a s)))
  | .adjunct => tp matrixDP ((before * inner a s) * (lexicalV * otherDP))

/-- A focus in place under the silent head (201), any other in Spec,FocP (187), (190). -/
def sentence (d : Domain) (a : Associate) (s : Site) : LinearizedSyntacticObject :=
  if s = .inSitu then nullFoc * body d a s else focusDP * (ni * body d a s)

/-- The island heads of (175), (184)–(186), (191), (192). -/
def islandHeads : List LexicalItem.Token := [rel, before, ati]

/-- No link is too short (183), and none leaves an island. -/
def Derivable (t : LinearizedSyntacticObject) : Prop :=
  ObeysAntiLocality .raising t ∧ ¬ CrossesIsland .raising t focusDP (· ∈ islandHeads)

instance (t : LinearizedSyntacticObject) : Decidable (Derivable t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Resumption is the last resort where a gap is prohibited (p. 115). -/
def siteOf (d : Domain) (a : Associate) : Site :=
  if Derivable (sentence d a .gap) then .gap else .pronoun

-- (182), (183) [erlewine-2016]
theorem subject_too_close :
    ¬ ObeysAntiLocality .raising (sentence .matrix .subject .gap) ∧
      ObeysAntiLocality .raising (sentence .matrix .subject .pronoun) ∧
      ObeysAntiLocality .raising (sentence .matrix .object .gap) := by
  decide +kernel

/-- The derivation a row records. -/
def derivationOf? (r : Datum) : Option LinearizedSyntacticObject := do
  let d ← r.parse? "domain" [("matrix", Domain.matrix), ("complement", .complement),
    ("focusClause", .focusClause), ("relative", .relative), ("adjunct", .adjunct),
    ("coordinate", .coordinate)]
  let a ← r.parse? "associate" [("subject", Associate.subject), ("object", .object)]
  let s ← r.parse? "site" [("gap", Site.gap), ("pronoun", .pronoun), ("inSitu", .inSitu)]
  pure (sentence d a s)

/-- A row is ungrammatical exactly when a link of its derivation is too short or leaves an island,
which only movement can do. -/
theorem rows_derivable :
    ∀ r ∈ Examples.all, r.feature? "domain" ≠ none →
      ∃ t ∈ derivationOf? r, (Derivable t ↔ r.judgment ≠ .ungrammatical) := by
  decide +kernel

-- (176-b), pp. 105–106: were *ni* an island head, as on a cleft analysis, this would be out.
theorem extraction_over_ni :
    Derivable (sentence .focusClause .object .gap) ∧
      CrossesIsland .raising (sentence .focusClause .object .gap) focusDP
        (· ∈ embeddedNi :: islandHeads) := by
  decide +kernel

/-! ### Answers

Constituents are positions by grammatical function in `[subject [verb object adjunct]]`, ordered by
containment. -/

def clause : TreePath := ⟨[]⟩
def subject : TreePath := ⟨[0]⟩
def vp : TreePath := ⟨[1]⟩
def verb : TreePath := ⟨[1, 0]⟩
def object : TreePath := ⟨[1, 1]⟩
def adjunct : TreePath := ⟨[1, 2]⟩

/-- The positions the rows name. -/
def positionNames : List (String × TreePath) :=
  [("clause", clause), ("subject", subject), ("vp", vp), ("verb", verb), ("object", object),
    ("adjunct", adjunct)]

/-- The phrases Branan and Erlewine's rule aligns. -/
def clausePhrases : List TreePath :=
  prominent (.node .v [xp .D "S", .node .V [.terminal .V "V", xp .D "O", xp .P "A"]]) []

/-- A subject, or a non-subject, whose focus behaves alike (p. 110). -/
def Associate.ofPosition (m : TreePath) : Associate :=
  if m = Aremu2025a.subject then .subject else .object

theorem siteOf_ofPosition_eq_pronoun_iff {m : TreePath} :
    siteOf .matrix (.ofPosition m) = .pronoun ↔ m = subject := by
  by_cases hm : m = subject
  · subst hm; exact iff_of_true (by decide +kernel) rfl
  · simpa [Associate.ofPosition, hm] using (by decide +kernel : siteOf .matrix .object ≠ .pronoun)

/-- An answer to a question. -/
structure Answer where
  /-- The logical focus. -/
  focus : TreePath
  /-- What it fronts before *ni*. -/
  fronted : Option TreePath
  /-- The number of the focus, which a resumptive agrees with. -/
  number : Number := .singular

variable {a : Answer} {m : TreePath}

namespace Answer

/-- The pronoun that would resume the focus, in the past or present sentences of the rows. -/
def pronoun (a : Answer) : Option PersonalPronoun :=
  Yoruba.Pronouns.pastPresentSubject .third a.number

/-- The resumptive of a fronted subject. -/
def resumptive (a : Answer) : Finset (Reflex TreePathᵒᵈ) :=
  (a.pronoun.map fun r ↦ .morpheme (toDual subject) [.free r.form]).toFinset

/-- A fronted constituent is followed by *ni*, and resumed where a gap is out or else displaced. -/
def reflexes (a : Answer) : Finset (Reflex TreePathᵒᵈ) :=
  match a.fronted with
  | none => ∅
  | some m => {.morpheme (toDual m) [.free Yoruba.ni.form]} ∪
      if siteOf .matrix (.ofPosition m) = .pronoun then a.resumptive
      else {.displacement (toDual m)}

theorem reflexes_eq_empty (h : a.fronted = none) : a.reflexes = ∅ := by
  simp [reflexes, h]

theorem exactlyTargets_reflexes (h : a.fronted = some m) :
    ExactlyTargets a.reflexes (toDual m) := by
  intro ρ hρ
  simp only [reflexes, h, siteOf_ofPosition_eq_pronoun_iff, Finset.mem_union,
    Finset.mem_singleton] at hρ
  obtain rfl | hρ := hρ
  · rfl
  · split_ifs at hρ with hm
    · simp only [resumptive, Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff] at hρ
      obtain ⟨r, -, rfl⟩ := hρ
      simp [hm]
    · simp_all

theorem reflexes_nonempty (h : a.fronted = some m) : a.reflexes.Nonempty :=
  ⟨.morpheme (toDual m) [.free Yoruba.ni.form], by simp [reflexes, h]⟩

-- p. 108: the displacement reflex is what the chain of the focus shows.
theorem displacement_mem_reflexes_iff (h : a.fronted = some m) :
    .displacement (toDual m) ∈ a.reflexes ↔
      links .raising (sentence .matrix (.ofPosition m) (siteOf .matrix (.ofPosition m))) focusDP
        ≠ [] := by
  by_cases hm : m = subject
  · have : siteOf .matrix (.ofPosition m) = .pronoun := siteOf_ofPosition_eq_pronoun_iff.2 hm
    subst hm
    simp only [reflexes, h, this, resumptive, ite_true, Finset.mem_union, Finset.mem_singleton,
      Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff]
    exact iff_of_false (by simp) (by decide +kernel)
  · have h₁ : siteOf .matrix (.ofPosition m) ≠ .pronoun :=
      fun e ↦ hm (siteOf_ofPosition_eq_pronoun_iff.1 e)
    have h₂ : Associate.ofPosition m = .object := by simp [Associate.ofPosition, hm]
    simp only [reflexes, h, h₁, ite_false, Finset.mem_union, Finset.mem_singleton, or_true,
      true_iff]
    rw [h₂]
    decide +kernel

-- (217-a)
theorem antiPiedPipes_iff :
    AntiPiedPipes a.reflexes (toDual a.focus) ↔ ∃ m ∈ a.fronted, a.focus < m := by
  cases h : a.fronted with
  | none => simp [reflexes_eq_empty h, AntiPiedPipes]
  | some m =>
    rw [(exactlyTargets_reflexes h).antiPiedPipes_iff (reflexes_nonempty h)]
    simp

/-- A focused subject fronts, and what fronts is the focus or, in a focused clause, the phrase
left-aligned with it. -/
def Licensed (a : Answer) : Prop :=
  (a.focus = subject → a.fronted = some subject) ∧
    ∀ m ∈ a.fronted, clause < m ∧
      (m = a.focus ∨ a.focus = clause ∧ LeftAlignedOn clausePhrases m clause)

instance : Decidable a.Licensed := inferInstanceAs (Decidable (_ ∧ _))

/-- A fronted focus is exhaustive and one in place is not (p. 99). -/
def Exhaustive (a : Answer) : Prop := a.fronted = some a.focus

instance : Decidable a.Exhaustive := inferInstanceAs (Decidable (_ = _))

-- §3.4.2: Yorùbá marks a proper part of the focus only as the subject of a focused clause.
theorem licensed_antiPiedPipes_iff :
    (a.Licensed ∧ AntiPiedPipes a.reflexes (toDual a.focus)) ↔
      a.focus = clause ∧ a.fronted = some subject := by
  rw [antiPiedPipes_iff]
  constructor
  · rintro ⟨⟨-, h⟩, m, hm, hlt⟩
    obtain ⟨hc, rfl | ⟨hf, x, hx, y, hy, hxy⟩⟩ := h m hm
    · exact absurd hlt (lt_irrefl _)
    · obtain rfl : y = subject := by
        simpa [show BrananErlewine2023.leftmost clausePhrases clause = some subject by
          decide +kernel, eq_comm] using hy
      obtain rfl : x = subject :=
        (by decide +kernel : ∀ x ∈ clausePhrases, x.LeftAligned subject → x = subject) x
          (List.mem_of_find?_eq_some hx) hxy
      obtain rfl := (BrananErlewine2023.le_of_mem_leftmost hx).lt_or_eq.resolve_left
        fun hlt ↦ hc.not_ge (TreePath.le_parent_of_lt hlt)
      exact ⟨hf, hm⟩
  · rintro ⟨hf, hs⟩
    refine ⟨⟨fun h ↦ absurd (hf.symm.trans h) (by decide), fun m hm ↦ ?_⟩, subject, hs,
      hf ▸ by decide⟩
    obtain rfl : m = subject := by simpa [hs, eq_comm] using hm
    exact ⟨by decide, .inr ⟨hf, by decide +kernel⟩⟩

end Answer

-- (166-c), p. 103: Branan and Erlewine's rule allows what Yorùbá rejects.
theorem leftAligned_not_licensed :
    LeftAlignedOn clausePhrases object vp ∧
      ¬ ({ focus := vp, fronted := some object } : Answer).Licensed := by
  decide +kernel

-- (160-b), (162-b)
theorem not_perceptible : ¬ Perceptible fun a : {a : Answer // a.Licensed} ↦ a.1.reflexes :=
  fun h ↦ Finset.not_nonempty_empty (h ⟨{ focus := object, fronted := none }, by decide +kernel⟩)

/-- The relativizable position of a constituent. -/
def relativePosition? (m : TreePath) : Option Relativization.Position :=
  if m = subject then some .subject
  else if m = object then some .directObject
  else if m = adjunct then some .oblique
  else none

-- Fronting treats positions as relativization with *tí* does [awobuluyi-1978], which a cleft
-- analysis would explain and `extraction_over_ni` rules out.
theorem gap_mem_relTi_realize_iff {p : Relativization.Position} (ha : a.fronted = some m)
    (h : relativePosition? m = some p) :
    .gap ∈ Yoruba.relTi.realize p ↔ .displacement (toDual m) ∈ a.reflexes := by
  rw [Answer.displacement_mem_reflexes_iff ha]
  unfold relativePosition? at h
  split_ifs at h with h₁ h₂ h₃ <;> cases h <;> subst_vars <;> decide +kernel

/-! ### One exclusive operator

A world is the set of alternatives true in it. -/

section Exclusive

variable {ι : Type*} {i c : ι}

/-- The alternative `i` holds in a world. -/
def holds {W : Type*} [Membership ι W] (i : ι) : Set W := {w | i ∈ w}

@[simp] theorem mem_holds {W : Type*} [Membership ι W] {w : W} : w ∈ holds i ↔ i ∈ w := .rfl

/-- The entry ch. 5 (50), *kàn* or silent, over the alternatives `P`. -/
noncomputable abbrev exclusive {W : Type*} (P : ι → Set W) (i : ι) : W → Trivalent :=
  only (· ⊆ ·) (range P) id (P i)

theorem exclusive_eq_true_iff {W : Type*} {P : ι → Set W} {w : W} (hP : ∀ j, P i ⊆ P j → j = i) :
    exclusive P i w = .true ↔ w ∈ P i ∧ ∀ j, j ≠ i → w ∉ P j := by
  rw [exclusive, ← only_eq_eq_only_subset_range hP, only_eq_eq_true_iff (mem_univ i)]
  simp

theorem holds_subset_holds {j : ι} (h : holds i ⊆ (holds j : Set (Set ι))) : j = i := by
  simpa using h (mem_singleton i)

/-- Something at or above `i` holds. -/
def reaches [Preorder ι] (i : ι) : Set (Set ι) := {w | ∃ j ∈ w, i ≤ j}

-- ch. 5 (56): cumulative alternatives give Coppock and Beaver's strength parameter.
theorem exclusive_reaches_eq [PartialOrder ι] :
    exclusive reaches i = only (· ≥ ·) univ holds i := by
  have hc (j k : ι) : reaches k ⊆ reaches j ↔ j ≤ k :=
    ⟨fun h ↦ by simpa [reaches] using h (show ({k} : Set ι) ∈ reaches k from ⟨k, rfl, le_rfl⟩),
      fun hjk _ ⟨m, hm, hkm⟩ ↦ ⟨m, hm, hjk.trans hkm⟩⟩
  have hL : atLeast (· ⊆ ·) (range reaches) id (reaches i) = atLeast (· ≥ ·) univ holds i := by
    refine Set.ext fun w ↦ ⟨?_, fun ⟨j, _, hw, hij⟩ ↦
      ⟨_, mem_range_self i, ⟨j, hw, hij⟩, subset_rfl⟩⟩
    rintro ⟨_, ⟨k, rfl⟩, hw, hk⟩
    obtain ⟨j, hj, hij⟩ := hk hw
    exact ⟨j, mem_univ j, hj, hij⟩
  have hM : atMost (· ⊆ ·) (range reaches) id (reaches i) = atMost (· ≥ ·) univ holds i := by
    refine Set.ext fun w ↦ ⟨fun h j _ hj ↦ (hc j i).1 (h _ (mem_range_self j) ⟨j, hj, le_rfl⟩), ?_⟩
    rintro h _ ⟨j, rfl⟩ ⟨k, hk, hjk⟩
    exact (hc j i).2 (hjk.trans (h k (mem_univ k) hk))
  funext w
  rw [exclusive, only, only, hL, hM]

/-- The scale a particle sets, ch. 5 (66). -/
inductive Scale
  | entailment | contextual
  deriving DecidableEq, Repr

variable [PartialOrder ι] {s : Scale} {w : Set ι}

/-- The alternatives of a scale: atomic under entailment, cumulative on a contextual scale. -/
def Scale.alternative : Scale → ι → Set (Set ι)
  | .entailment => holds
  | .contextual => reaches

/-- What the exclusive over a scale lets hold along with the prejacent `i`. -/
def Scale.Allows : Scale → ι → ι → Prop
  | .entailment, i, j => j = i
  | .contextual, i, j => j ≤ i

instance [DecidableEq ι] [DecidableLE ι] : ∀ (s : Scale) (i j : ι), Decidable (s.Allows i j)
  | .entailment, i, j => inferInstanceAs (Decidable (j = i))
  | .contextual, i, j => inferInstanceAs (Decidable (j ≤ i))

theorem Scale.allows_refl (s : Scale) (i : ι) : s.Allows i i := by cases s <;> simp [Scale.Allows]

theorem exclusive_alternative_eq_true_iff :
    exclusive s.alternative i w = .true ↔ i ∈ w ∧ ∀ j ∈ w, s.Allows i j := by
  cases s
  · rw [Scale.alternative, exclusive_eq_true_iff fun _ ↦ holds_subset_holds]
    simp only [mem_holds, Scale.Allows]
    grind
  · rw [Scale.alternative, exclusive_reaches_eq]
    refine only_ge_eq_true_iff.trans ?_
    simp [IsGreatest, upperBounds, Scale.Allows]

/-- *He is only `i`. He is also `c`*, of another `c`, can hold together. -/
def Scale.Compatible (s : Scale) (i c : ι) : Prop :=
  c ≠ i ∧ ∃ w, exclusive s.alternative i w = .true ∧ additive (· = ·) univ holds c w = .true

theorem compatible_iff : s.Compatible i c ↔ c ≠ i ∧ s.Allows i c := by
  refine and_congr_right fun hc ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨w, h₁, h₂⟩
    exact (exclusive_alternative_eq_true_iff.1 h₁).2 c (additive_eq_true_iff.1 h₂).2
  · refine ⟨{c, i}, exclusive_alternative_eq_true_iff.2 ⟨by simp, ?_⟩,
      additive_eq_true_iff.2 ⟨⟨i, mem_univ _, by simp, hc⟩, by simp⟩⟩
    rintro j (rfl | rfl)
    exacts [h, s.allows_refl _]

instance [DecidableEq ι] [DecidableLE ι] : Decidable (s.Compatible i c) :=
  decidable_of_iff _ compatible_iff.symm

/-- The exclusive is true where just the alternatives in `l` hold. -/
def Scale.TrueOf (s : Scale) (i : ι) (l : List ι) : Prop :=
  exclusive s.alternative i {x | x ∈ l} = .true

theorem trueOf_iff {l : List ι} : s.TrueOf i l ↔ i ∈ l ∧ ∀ j ∈ l, s.Allows i j :=
  exclusive_alternative_eq_true_iff.trans (by simp)

instance [DecidableEq ι] [DecidableLE ι] {l : List ι} : Decidable (s.TrueOf i l) :=
  decidable_of_iff _ trueOf_iff.symm

-- (158), p. 99: exhaustivity is what rules out the additive continuation of a bare answer.
theorem exists_additive_iff (hc : c ≠ i) :
    (∃ w : Set ι, (if a.Exhaustive then exclusive holds i w = .true else i ∈ w) ∧
      additive (· = ·) univ holds c w = .true) ↔ ¬ a.Exhaustive := by
  by_cases h : a.Exhaustive
  · simp only [h, ite_true, not_true_eq_false, iff_false]
    exact fun ⟨w, h₁, h₂⟩ ↦ hc (compatible_iff (s := .entailment) |>.1 ⟨hc, w, h₁, h₂⟩).2
  · simp only [h, ite_false, not_false_eq_true, iff_true]
    exact ⟨{c, i}, by simp, additive_eq_true_iff.2 ⟨⟨i, mem_univ _, by simp, hc⟩, by simp⟩⟩

end Exclusive

section Negation

variable {ι : Type*} {i : ι} {w : Set ι}

-- ch. 5 (58): under negation the prejacent survives.
theorem exclusive_holds_eq_false_iff :
    exclusive holds i w = .false ↔ i ∈ w ∧ ∃ j ∈ w, j ≠ i := by
  rw [exclusive, ← only_eq_eq_only_subset_range fun _ ↦ holds_subset_holds]
  simp only [only_eq_false_iff, mem_atLeast, mem_atMost, mem_univ, true_and, mem_holds,
    true_implies]
  grind

-- ch. 5 (59): under negation only something higher holds, not the prejacent.
theorem exclusive_reaches_eq_false_iff [LinearOrder ι] :
    exclusive reaches i w = .false ↔ ∃ j ∈ w, i < j := by
  rw [exclusive_reaches_eq]
  simp only [only_eq_false_iff, mem_atLeast, mem_atMost, mem_univ, true_and, mem_holds,
    true_implies, not_forall, exists_prop, ge_iff_le, not_le]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun ⟨j, hj, hij⟩ ↦ ⟨⟨j, hj, hij.le⟩, j, hj, hij⟩⟩

end Negation

/-- The scale of a particle. -/
def scaleOf? (r : Datum) : Option Scale :=
  r.parse? "particle" [(Yoruba.nikan.form, Scale.entailment), (Yoruba.lasan.form, .contextual)]

/-- Ranks on the scales of ch. 5 (52), (53). -/
def ranks : List (String × Fin 3) :=
  [("bronze", 0), ("silver", 1), ("gold", 2), ("cleaner", 0), ("student", 1), ("professor", 2)]

/-- Each particle's scale predicts its continuations: none after *nìkan*, and after *lásán* one
that ranks lower (ch. 5 (52), (53)). -/
theorem rows_continuations :
    ∀ r ∈ Examples.all, r.feature? "also" ≠ none →
      ∃ s ∈ scaleOf? r, ∃ i ∈ r.parse? "prejacent" ranks, ∃ c ∈ r.parse? "also" ranks,
        (s.Compatible i c ↔ r.JudgedFelicitous) := by
  decide +kernel

/-- With bronze and silver won, *lásán* is true and *nìkan* false, so the particle is not vacuous
(ch. 5 (57)). -/
theorem rows_won :
    ∀ r ∈ Examples.all, r.features "won" ≠ [] →
      ∃ s ∈ scaleOf? r, ∃ i ∈ r.parse? "prejacent" ranks, ∃ l ∈ r.parseAll? "won" ranks,
        (s.TrueOf i l ↔ r.JudgedFelicitous) := by
  decide +kernel

-- ch. 4 (60)–(64), p. 178: *lásán* and *péré* need a prejacent below the standard, *nìkan* does
-- not. (60-c) rejects only an evaluative reading, and in (62-d) six is not an alternative.
theorem rows_standard :
    ∀ r ∈ Examples.all, r.feature? "standard" ≠ none →
      ∃ n ∈ r.nat? "value", ∃ d ∈ r.nat? "standard",
        ((r.feature? "particle" ≠ some Yoruba.nikan.form → n < d) ↔ r.JudgedFelicitous) := by
  decide +kernel

/-! ### Split scope -/

/-- Three fowls, enough to tell two from more. -/
abbrev Fowl := Fin 3

/-- Which fowls Adam slaughters. -/
abbrev World := Finset Fowl

abbrev slaughter : Fowl → Set World := holds

/-- *n fowls*, as at least `n`, with scope `f`. -/
def numeral (f : Fowl → Set World) (n : ℕ) : Set World :=
  {w | Quantifier.Det.atLeast n univ {x | w ∈ f x}}

/-- Any two fowls are required, and more are allowed. -/
def required : SetRel World World := {p | 2 ≤ p.2.card}

theorem mem_required {w v : World} : (w, v) ∈ required ↔ 2 ≤ v.card := .rfl

theorem mem_numeral_slaughter {n : ℕ} {w : World} : w ∈ numeral slaughter n ↔ n ≤ w.card := by
  simp [numeral, Quantifier.Det.atLeast_apply, Set.ncard_coe_finset]

theorem mem_core_numeral {n : ℕ} {w : World} : w ∈ required.core (numeral slaughter n) ↔ n ≤ 2 :=
  ⟨fun h ↦ mem_numeral_slaughter.1 (h (b := {0, 1}) (mem_required.2 (by decide))),
    fun h _ hv ↦ mem_numeral_slaughter.2 (h.trans hv)⟩

theorem mem_numeral_core {n : ℕ} {w : World} :
    w ∈ numeral (fun x ↦ required.core (slaughter x)) n ↔ n = 0 := by
  have h0 (x : Fowl) (w : World) : w ∉ required.core (slaughter x) := fun hw ↦ by
    simpa using hw (b := Finset.univ.erase x) (by simp [required, Finset.card_erase_of_mem])
  simp [numeral, Quantifier.Det.atLeast_apply, h0]

/-- Ch. 5 (30-c) is true with the operator above *require* and the numeral below it, and false on
both scopes of a quantifier of the two with an individual trace, (31), (32) [hirsch-2017]. -/
theorem split_scope (w : World) :
    (Examples.ch5_30c.JudgedFelicitous ↔
      exclusive (fun n ↦ required.core (numeral slaughter n)) 2 w = .true) ∧
    w ∉ required.core {v | exclusive (numeral slaughter) 2 v = .true} ∧
    exclusive (numeral fun x ↦ required.core (slaughter x)) 2 w ≠ .true := by
  refine ⟨iff_of_true (by decide) (only_eq_true_iff.2 ⟨⟨_, ⟨2, rfl⟩, mem_core_numeral.2 le_rfl,
    subset_rfl⟩, ?_⟩), fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro _ ⟨n, rfl⟩ hw v -
    exact mem_core_numeral.2 (mem_core_numeral.1 hw)
  · have hu := only_eq_true_iff.1 (h (b := Finset.univ) (mem_required.2 (by decide)))
    have h3 := hu.2 _ ⟨3, rfl⟩ (mem_numeral_slaughter.2 (by decide))
    exact absurd (mem_numeral_slaughter.1 (h3 (mem_numeral_slaughter.2
      (show 2 ≤ ({0, 1} : Finset Fowl).card by decide)))) (by decide)
  · obtain ⟨⟨_, ⟨n, rfl⟩, hw, hsub⟩, -⟩ := only_eq_true_iff.1 h
    exact two_ne_zero (mem_numeral_core.1 (hsub hw))

/-! ### Concord -/

section Concord

variable {α β : Type*} {a : α} {b : β} {w : Set (α × β)}

/-- One operator over the pairs, ch. 5 (47). -/
noncomputable def concord (a : α) (b : β) : Set (α × β) → Trivalent :=
  exclusive holds (a, b)

/-- Two operators, ch. 5 (49). -/
noncomputable def double (a : α) (b : β) : Set (α × β) → Trivalent :=
  exclusive (fun x ↦ {w | exclusive (fun y ↦ holds (x, y)) b w = .true}) a

private theorem only_b_eq_true_iff {x : α} :
    exclusive (fun y ↦ holds (x, y)) b w = .true ↔ (x, b) ∈ w ∧ ∀ y, y ≠ b → (x, y) ∉ w :=
  exclusive_eq_true_iff fun j h ↦ by
    simpa using h (show ({(x, b)} : Set (α × β)) ∈ holds (x, b) from rfl)

theorem concord_eq_true_iff : concord a b w = .true ↔ w = {(a, b)} := by
  rw [concord, exclusive_eq_true_iff fun _ ↦ holds_subset_holds, eq_singleton_iff_unique_mem]
  simp only [mem_holds, ne_eq, not_imp_not]

theorem double_eq_true_iff :
    double a b w = .true ↔ ((a, b) ∈ w ∧ ∀ y, y ≠ b → (a, y) ∉ w) ∧
      ∀ x, x ≠ a → ¬ ((x, b) ∈ w ∧ ∀ y, y ≠ b → (x, y) ∉ w) := by
  rw [double, exclusive_eq_true_iff fun j h ↦ ?_]
  · simp only [mem_ofPred_eq, only_b_eq_true_iff]
  · have h₀ := only_b_eq_true_iff.1 (h (a := {(a, b)}) (only_b_eq_true_iff.2 (by simp)))
    simpa using h₀.1

/-- The concord reading entails the double one (ch. 5 (46-c), (120)). -/
theorem double_of_concord (h : concord a b w = .true) : double a b w = .true := by
  obtain rfl := concord_eq_true_iff.1 h
  simp [double_eq_true_iff]

-- ch. 5 p. 168: `a` alone ate only `b`, and `c` ate `b` and `d`.
theorem not_concord_of_double {c : α} {d : β} (hc : c ≠ a) (hd : d ≠ b) :
    double a b {(a, b), (c, b), (c, d)} = .true ∧ concord a b {(a, b), (c, b), (c, d)} ≠ .true := by
  refine ⟨double_eq_true_iff.2 ?_, fun h ↦ ?_⟩
  · simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
    grind
  · have := (eq_singleton_iff_unique_mem.1 (concord_eq_true_iff.1 h)).2 (c, b) (by simp)
    simp_all

end Concord

/-! ### The rows of the answers -/

/-- The answer a row records. -/
def Answer.ofRow? (r : Datum) : Option Answer :=
  (r.parse? "focus" positionNames).map fun focus ↦
    { focus, fronted := r.parse? "fronted" positionNames
      number := (r.parse? "number" [("plural", Number.plural)]).getD .singular }

/-- The word after *ni*. -/
def afterNi (r : Datum) : Option String :=
  ((r.surfaceTokens.dropWhile (· != Yoruba.ni.form)).drop 1).head?

/-- The model accepts a licensed answer with *ni* exactly when it fronts, an additive only when it
is not exhaustive, and its pronoun after *ni* exactly when it fronts the subject. -/
def Accepts (a : Answer) (r : Datum) : Prop :=
  a.Licensed ∧ (Yoruba.ni.form ∈ r.surfaceTokens ↔ a.fronted ≠ none) ∧
    (r.feature? "continuation" = some "additive" → ¬ a.Exhaustive) ∧
    (afterNi r = a.pronoun.map (·.form) ↔ a.fronted = some subject)

instance (a : Answer) (r : Datum) : Decidable (Accepts a r) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- (157)–(169), (188)
theorem rows_answers :
    ∀ r ∈ Examples.all, r.feature? "focus" ≠ none →
      ∃ a ∈ Answer.ofRow? r, (Accepts a r ↔ r.JudgedFelicitous) := by
  decide +kernel

end Aremu2025a
