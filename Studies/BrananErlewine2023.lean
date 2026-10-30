module

public import Linglib.Core.Data.RoseTree.Positions
public import Linglib.Data.Examples.BrananErlewine2023
public import Linglib.Semantics.Focus.Particles
public import Linglib.Syntax.Minimalist.ExtendedProjection
public import Linglib.Syntax.Reflex
public import Linglib.Syntax.Tree.Basic

/-!
# Branan and Erlewine (2023): Anti-pied-piping

A language marks a focus on some constituent, by a particle or by moving it, and that constituent
need not be the focus. It may properly contain the focus, which is Ross's pied-piping, or be
properly contained in it, which Branan and Erlewine call anti-pied-piping and document in over
sixty languages. They conclude that a focus particle has no meaning of its own. It flags an
unpronounced operator that takes the whole focus in its scope, and it is adjoined, when a phase
is spelled out, to a phrase left-aligned with the focus once the phrases that bear no prominence
are skipped. Focus movement moves the phrase so marked, so one rule governs both, and it does not
tell pied-piping from anti-pied-piping.

## Implementation notes

* A phase is a constituency tree over the categories of the functional sequence, in the order
  it is spelled out. Its spine is the path of categories extending to the category of the phase,
  and the prominent phrases, the paper's ●-marked ones, are the phrases off the spine that an
  example does not report as skipped.
* The examples name constituents (subject, predicate, the fronted phrase), and a frame finds
  each as the first node of its tree spelling a given string of words, so positions are read off
  bracketings and none is typed in. Clause frames are schematic, and the frames of the English,
  Latin and Russian examples carry their words.
* The judged readings are those the paper prints. Where it marks one string for two speakers'
  grammars, the weak variant stands for the language.

## TODO

* The timing of placement: particles adjoin before scrambling, so a host need not be leftmost on
  the surface, and adjuncts merged late cannot host a particle for a focus on the predicate.
* The ratings of object fronting across accented and unaccented subjects in German, and the
  survey of languages by genus in the appendix.
* Narrow focus on a lexical verb, for which no phrase is left-aligned (`sov_verb`) and
  languages differ in what they do, and the obligatory anti-pied-piping of Miyara Yaeyaman, where
  the rule also allows the focused predicate itself to host the particle.
* The realization of prominence as phrasal stress, and the paper's argument from Hausa that
  placement does not track stress itself.

## References

* [branan-erlewine-2023]
* [ross-1967]
-/

@[expose] public section

namespace BrananErlewine2023

open Core.Order PhraseStructure Minimalist Focus.Particles Reflex OrderDual

/-! ### The particle is not a quantifier -/

section Semantics

variable {W σ : Type*} {C : Set σ} {α : σ} {β : σ → Set W} {D : Set (Set W)} {ψ : Set W} {w : W}

open Classical in
/-- On the quantificational theory a particle meaning *only* composes with its sister `α` and
then with its scope `β`, presupposing `β α` and asserting that `β` is false of every other
alternative to `α` in `C` ((72)). -/
noncomputable def quantifierOnly (C : Set σ) (α : σ) (β : σ → Set W) : W → SignType :=
  (β α).indicator fun w ↦ SignType.ofProp (∀ γ ∈ C, γ ≠ α → w ∉ β γ)

-- (73)
theorem quantifierOnly_eq_only (hα : α ∈ C) (hβ : Set.InjOn β C) :
    quantifierOnly C α β = only (· = ·) (β '' C) (β α) := by
  have hL : β α = atLeast (· = ·) (β '' C) (β α) := Set.ext fun _ ↦
    ⟨fun h ↦ ⟨_, Set.mem_image_of_mem β hα, h, rfl⟩, by rintro ⟨_, _, h, rfl⟩; exact h⟩
  have hM (w : W) : (∀ γ ∈ C, γ ≠ α → w ∉ β γ) ↔ w ∈ atMost (· = ·) (β '' C) (β α) :=
    (forall₂_congr fun γ hγ ↦
      ⟨fun h hw ↦ (congrArg β (not_not.1 fun hne ↦ h hne hw)).symm,
        fun h hne hw ↦ hne (hβ hγ hα (h hw).symm)⟩).trans Set.forall_mem_image.symm
  funext w
  refine SignType.eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · rw [only_eq_zero_iff, ← hL]
    simp [quantifierOnly]
  · rw [only_eq_one_iff, ← hL, ← hM]
    simp [quantifierOnly]

/-- A particle on a proper part of its focus is not a quantifier over alternatives to its sister.
Where the scope holds of the sister and of nothing else, the quantifier is true whatever
alternatives it is given, though an alternative `ψ` to the whole focus is true as well, so that
the operator associating with that focus is false. -/
theorem quantifierOnly_ne_only (C : Set σ) (hψ : ψ ∈ D) (hne : ψ ≠ β α) (hw : w ∈ ψ)
    (hwα : w ∈ β α) (hβ : ∀ γ, γ ≠ α → w ∉ β γ) :
    quantifierOnly C α β ≠ only (· = ·) D (β α) := by
  intro h
  have hq : quantifierOnly C α β w = 1 := by
    simp only [quantifierOnly, Trivalent.indicator_apply_eq_one_iff, SignType.ofProp_eq_one_iff]
    exact ⟨hwα, fun γ _ hγ ↦ hβ γ hγ⟩
  rw [h, only_eq_one_iff] at hq
  exact notMem_atMost hψ hw hne.symm hq.2

-- The paper's pseudo-English "Peter read only Hamlet" (79), a world being what Peter did.
inductive Book | hamlet | macbeth
inductive Deed | read (b : Book) | swim
def read (b : Book) : Set (Set Deed) := {w | .read b ∈ w}
def swam : Set (Set Deed) := {w | .swim ∈ w}

-- (79), (81)
theorem peter_read_only_hamlet :
    quantifierOnly Set.univ Book.hamlet read {.read .hamlet, .swim} = 1 ∧
      only (· = ·) {read .hamlet, read .macbeth, swam} (read .hamlet)
        {.read .hamlet, .swim} = -1 := by
  simp only [quantifierOnly, Trivalent.indicator_apply_eq_one_iff, SignType.ofProp_eq_one_iff,
    only_eq_neg_one_iff]
  refine ⟨⟨by simp [read], ?_⟩, mem_atLeast.2 ⟨read .hamlet, by simp, by simp [read], rfl⟩,
    fun h ↦ ?_⟩
  · rintro (_ | _) - h
    · exact absurd rfl h
    · simp [read]
  · have := congrArg ({Deed.swim} ∈ ·) (mem_atMost.1 h swam (by simp) (by simp [swam]))
    simp [read, swam] at this

end Semantics

/-! ### Prominence

When a phase is spelled out, every phrase outside the extended projection of the phase head
bears abstract prominence, the paper's ●, unless it is indefinite, given or otherwise light
((115), (119)). -/

variable {W : Type*}

/-- A position is on the spine of a phase when its category and that of every node above it
extend to the category of the phase, so that it belongs to the extended projection containing
the phase head. -/
def OnSpine (t : Tree Cat W) (p : TreePath) : Prop :=
  ∀ l ∈ p.toList.inits, ∃ s ∈ t[l]?, (Tree.cat s).ExtendsTo t.cat

instance (t : Tree Cat W) (p : TreePath) : Decidable (OnSpine t p) := by
  unfold OnSpine; infer_instance

/-- The prominent phrases of a phase are the phrases off its spine other than the `skipped`
ones, listed in document order. -/
def prominent (t : Tree Cat W) (skipped : List TreePath) : List TreePath :=
  (t.vertices.map TreePath.mk).filter fun p ↦
    p ∈ RoseTree.positionsWhere (fun s ↦ s.value.IsPhrase) t ∧ ¬ OnSpine t p ∧ p ∉ skipped

/-! ### Left-alignment relative to the prominent phrases -/

section LeftAlignedOn

variable {m : List TreePath} {X Y Z : TreePath}

/-- `leftmost m X` is the first phrase of `m` that the constituent at `X` contains. With `m` in
document order it is the one that begins earliest, and the largest that does. -/
def leftmost (m : List TreePath) (X : TreePath) : Option TreePath := m.find? (X ≤ ·)

theorem le_of_mem_leftmost {a : TreePath} (h : a ∈ leftmost m X) : X ≤ a := by
  simpa using List.find?_some h

/-- Two constituents are left-aligned on `m` when the leftmost phrase of `m` in the one and
the leftmost in the other are left-aligned ((118)). -/
def LeftAlignedOn (m : List TreePath) (X Y : TreePath) : Prop :=
  ∃ a ∈ leftmost m X, ∃ b ∈ leftmost m Y, a.LeftAligned b

instance : Decidable (LeftAlignedOn m X Y) := by unfold LeftAlignedOn; infer_instance

namespace LeftAlignedOn

@[symm] protected theorem symm (h : LeftAlignedOn m X Y) : LeftAlignedOn m Y X :=
  let ⟨a, ha, b, hb, hab⟩ := h; ⟨b, hb, a, ha, hab.symm⟩

@[trans] protected theorem trans (h₁ : LeftAlignedOn m X Y) (h₂ : LeftAlignedOn m Y Z) :
    LeftAlignedOn m X Z := by
  obtain ⟨a, ha, b, hb, hab⟩ := h₁
  obtain ⟨b', hb', c, hc, hbc⟩ := h₂
  obtain rfl := Option.mem_unique hb hb'
  exact ⟨a, ha, c, hc, hab.trans hbc⟩

/-- Of two left-aligned constituents one contains the other. -/
theorem symmGen_le (h : LeftAlignedOn m X Y) : Relation.SymmGen (· ≤ ·) X Y := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  rcases hab.le_or_ge with h | h
  · exact List.prefix_or_prefix_of_prefix ((le_of_mem_leftmost ha).trans h) (le_of_mem_leftmost hb)
  · exact List.prefix_or_prefix_of_prefix (le_of_mem_leftmost ha) ((le_of_mem_leftmost hb).trans h)

/-- Two constituents left-aligned with a third overlap, so of two separate phrases at most one
is left-aligned with a given focus, which is the leftmost effect. -/
theorem symmGen_le_of_common (h₁ : LeftAlignedOn m X Z) (h₂ : LeftAlignedOn m Y Z) :
    Relation.SymmGen (· ≤ ·) X Y :=
  (h₁.trans h₂.symm).symmGen_le

end LeftAlignedOn

theorem leftAlignedOn_self : LeftAlignedOn m X X ↔ (leftmost m X).isSome :=
  ⟨fun ⟨a, ha, _⟩ ↦ Option.isSome_iff_exists.2 ⟨a, ha⟩,
    fun h ↦ let ⟨a, ha⟩ := Option.isSome_iff_exists.1 h; ⟨a, ha, a, ha, .refl a⟩⟩

-- n. 45
theorem not_leftAlignedOn_of_leftmost_eq_none (h : leftmost m Y = none) : ¬ LeftAlignedOn m X Y :=
  fun ⟨_, _, b, hb, _⟩ ↦ by simp [h] at hb

end LeftAlignedOn

/-! ### Particle placement -/

/-- When a phase is spelled out, a particle adjoins to a phrase left-aligned with the focus,
preferably to such a phrase, or to any phrase overlapping the focus, in the strong, the weak and
the free variant of the rule ((117)). -/
inductive LeftmostRequirement
  | strong
  | weak
  | free
  deriving DecidableEq, Repr

namespace LeftmostRequirement

variable {r : LeftmostRequirement} {m : List TreePath} {host focus : TreePath}

/-- The phrases a variant lets host the particle for a focus. -/
def Allows : LeftmostRequirement → List TreePath → TreePath → TreePath → Prop
  | strong, m, host, focus => LeftAlignedOn m host focus
  | weak, _, host, focus | free, _, host, focus => Relation.SymmGen (· ≤ ·) host focus

/-- The phrases a variant lets host the particle at no cost. -/
def Favors : LeftmostRequirement → List TreePath → TreePath → TreePath → Prop
  | strong, m, host, focus | weak, m, host, focus => LeftAlignedOn m host focus
  | free, _, host, focus => Relation.SymmGen (· ≤ ·) host focus

instance : Decidable (r.Allows m host focus) := by cases r <;> unfold Allows <;> infer_instance

instance : Decidable (r.Favors m host focus) := by cases r <;> unfold Favors <;> infer_instance

theorem Favors.allows (h : r.Favors m host focus) : r.Allows m host focus := by
  cases r
  exacts [h, LeftAlignedOn.symmGen_le h, h]

theorem Allows.symmGen_le (h : r.Allows m host focus) : Relation.SymmGen (· ≤ ·) host focus := by
  cases r
  exacts [LeftAlignedOn.symmGen_le h, h, h]

/-- The rule is symmetric in host and focus, so it does not distinguish pied-piping from
anti-pied-piping (§6.4). -/
theorem allows_comm : r.Allows m host focus ↔ r.Allows m focus host := by
  cases r <;> grind [Allows, LeftAlignedOn.symm, Relation.SymmGen]

theorem favors_comm : r.Favors m host focus ↔ r.Favors m focus host := by
  cases r <;> grind [Favors, LeftAlignedOn.symm, Relation.SymmGen]

theorem Allows.exactlyTargets_or_piedPipes_or_antiPiedPipes (h : r.Allows m host focus)
    {s : Finset (Reflex TreePathᵒᵈ)} (hs : s.Nonempty) (hhost : ExactlyTargets s (toDual host)) :
    ExactlyTargets s (toDual focus) ∨ PiedPipes s (toDual focus) ∨
      AntiPiedPipes s (toDual focus) := by
  rw [hhost.exactlyTargets_iff hs, hhost.piedPipes_iff hs, hhost.antiPiedPipes_iff hs,
    toDual_lt_toDual, toDual_lt_toDual, toDual_inj]
  rcases h.symmGen_le with h | h
  · exact h.eq_or_lt.imp_right .inl
  · exact h.eq_or_lt.elim (fun e ↦ .inl e.symm) fun h ↦ .inr (.inr h)

end LeftmostRequirement

/-! ### Phases and their constituents -/

/-- The constituents the examples name. -/
inductive Part
  | sentence | subject | predicate | object | verb | goal | theme
  | adjective | phrase | wh | demonstrative
  deriving DecidableEq, Repr

/-- A phase as it is spelled out, with the words of the constituents the examples name. -/
structure Frame where
  /-- The phase, in the order in which it is linearized. -/
  phase : Tree Cat String
  /-- The words each named constituent spells. -/
  brackets : List (Part × List String)

namespace Frame

variable (fr : Frame)

/-- The position of a named constituent, the first node spelling its words. -/
def site (c : Part) : Option TreePath :=
  (fr.brackets.lookup c).bind fun ws ↦
    (fr.phase.vertices.map TreePath.mk).find? fun p ↦ ∃ s ∈ fr.phase[p]?,
      Tree.yield s = ws

/-- A variant of the rule lets the constituent `host` of a frame host the particle for a focus
on `focus`, the constituents of `skipped` bearing no prominence. -/
def Allows (r : LeftmostRequirement) (host focus : Part) (skipped : List Part := []) : Prop :=
  ∃ h ∈ fr.site host, ∃ f ∈ fr.site focus,
    r.Allows (prominent fr.phase (skipped.filterMap fr.site)) h f

instance (r : LeftmostRequirement) (host focus : Part) (skipped : List Part) :
    Decidable (fr.Allows r host focus skipped) := by unfold Allows; infer_instance

end Frame

/-- A phrase over one word. -/
def xp (c : Cat) (w : String) : Tree Cat String := .node c [.terminal c w]

/-- A verb-final transitive clause, `[S [O V]]`. -/
def sov : Frame where
  phase := .node .v [xp .D "S", .node .V [xp .D "O", .terminal .V "V"]]
  brackets := [(.sentence, ["S", "O", "V"]), (.subject, ["S"]), (.predicate, ["O", "V"]),
    (.object, ["O"]), (.verb, ["V"])]

/-- A verb-medial transitive clause, `[S [V O]]`. -/
def svo : Frame where
  phase := .node .v [xp .D "S", .node .V [.terminal .V "V", xp .D "O"]]
  brackets := [(.sentence, ["S", "V", "O"]), (.subject, ["S"]), (.predicate, ["V", "O"]),
    (.object, ["O"]), (.verb, ["V"])]

/-- A verb-initial transitive clause, `[V S O]`. -/
def vso : Frame where
  phase := .node .v [.terminal .V "V", xp .D "S", xp .D "O"]
  brackets := [(.sentence, ["V", "S", "O"]), (.subject, ["S"]), (.object, ["O"])]

/-- An intransitive clause, `[S [V]]`. -/
def sv : Frame where
  phase := .node .v [xp .D "S", .node .V [.terminal .V "V"]]
  brackets := [(.sentence, ["S", "V"]), (.subject, ["S"]), (.predicate, ["V"])]

/-- A verb-final ditransitive clause with the theme before the goal. -/
def themeGoalV : Frame where
  phase := .node .v [xp .D "S", .node .V [xp .D "Theme", xp .D "Goal", .terminal .V "V"]]
  brackets := [(.predicate, ["Theme", "Goal", "V"]), (.theme, ["Theme"]), (.goal, ["Goal"])]

/-- A verb-final ditransitive clause with the goal before the theme. -/
def goalThemeV : Frame where
  phase := .node .v [xp .D "S", .node .V [xp .D "Goal", xp .D "Theme", .terminal .V "V"]]
  brackets := [(.predicate, ["Goal", "Theme", "V"]), (.goal, ["Goal"]), (.theme, ["Theme"])]

/-- A verb-medial ditransitive clause with the goal before the theme. -/
def vGoalTheme : Frame where
  phase := .node .v [xp .D "S", .node .V [.terminal .V "V", xp .D "Goal", xp .D "Theme"]]
  brackets := [(.predicate, ["V", "Goal", "Theme"]), (.goal, ["Goal"]), (.theme, ["Theme"])]

/-- A clause whose object holds an attributive adjective, `[S [V [D [A N]]]]`. -/
def adjectiveObject : Frame where
  phase := .node .v [xp .D "S", .node .V [.terminal .V "V",
    .node .D [.terminal .D "D", .node .N [xp .A "A", .terminal .N "N"]]]]
  brackets := [(.object, ["D", "A", "N"]), (.adjective, ["A"])]

/-- *you frame [whose picture]* ((122a)). -/
def whosePicture : Frame where
  phase := .node .v [xp .D "you", .node .V [.terminal .V "frame",
    .node .D [xp .D "whose", .terminal .N "picture"]]]
  brackets := [(.phrase, ["whose", "picture"]), (.wh, ["whose"])]

/-- *you frame [a picture of whom]* ((122b)). -/
def pictureOfWhom : Frame where
  phase := .node .v [xp .D "you", .node .V [.terminal .V "frame",
    .node .D [.terminal .D "a", .node .N [.terminal .N "picture",
      .node .P [.terminal .P "of", xp .D "whom"]]]]]
  brackets := [(.phrase, ["a", "picture", "of", "whom"]), (.wh, ["whom"])]

/-- *you see [[[whose brother]'s friend]'s father]*. -/
def whoseBrothersFriendsFather : Frame where
  phase := .node .v [xp .D "you", .node .V [.terminal .V "see",
    .node .D [.node .D [.node .D [xp .D "whose", .terminal .N "brother's"],
      .terminal .N "friend's"], .terminal .N "father"]]]
  brackets := [(.phrase, ["whose", "brother's", "friend's", "father"]), (.wh, ["whose"])]

/-- *you see [the father of [[whose brother]'s friend]]*. -/
def fatherOfWhoseBrothersFriend : Frame where
  phase := .node .v [xp .D "you", .node .V [.terminal .V "see",
    .node .D [.terminal .D "the", .node .N [.terminal .N "father",
      .node .P [.terminal .P "of", .node .D [.node .D [xp .D "whose", .terminal .N "brother's"],
        .terminal .N "friend"]]]]]]
  brackets := [(.phrase, ["the", "father", "of", "whose", "brother's", "friend"]),
    (.wh, ["whose"])]

/-- *you speak [to [[which student]'s friend]]*. -/
def toWhichStudentsFriend : Frame where
  phase := .node .v [xp .D "you", .node .V [.terminal .V "speak",
    .node .P [.terminal .P "to", .node .D [.node .D [xp .D "which", .terminal .N "student's"],
      .terminal .N "friend"]]]]
  brackets := [(.phrase, ["to", "which", "student's", "friend"]), (.wh, ["which"])]

/-- Latin *[ob [eās rēs]]* 'because of these things'. The source prints the phrase alone, so it
is the root here and bears no prominence whether or not its preposition is light. -/
def obEasRes : Frame where
  phase := .node .P [.terminal .P "ob", .node .D [xp .Dem "eās", .terminal .N "rēs"]]
  brackets := [(.phrase, ["ob", "eās", "rēs"]), (.demonstrative, ["eās"])]

/-- Russian *on ženilsja [na sestre [druga [č’ej materi]]]*. -/
def naSestreDrugaCejMateri : Frame where
  phase := .node .v [xp .D "on", .node .V [.terminal .V "ženilsja",
    .node .P [.terminal .P "na", .node .D [.terminal .N "sestre",
      .node .D [.terminal .N "druga", .node .D [xp .D "č’ej", .terminal .N "materi"]]]]]]
  brackets := [(.phrase, ["na", "sestre", "druga", "č’ej", "materi"]), (.wh, ["č’ej"])]

/-- *the government prescribes [the height of the lettering on the covers of which]*. -/
def heightOfTheLettering : Frame where
  phase := .node .v [.node .D [.terminal .D "the", .terminal .N "government"],
    .node .V [.terminal .V "prescribes",
    .node .D [.terminal .D "the", .node .N [.terminal .N "height",
      .node .P [.terminal .P "of", .node .D [.terminal .D "the", .node .N [.terminal .N "lettering",
        .node .P [.terminal .P "on", .node .D [.terminal .D "the", .node .N [.terminal .N "covers",
          .node .P [.terminal .P "of", xp .D "which"]]]]]]]]]]]
  brackets := [(.phrase, ["the", "height", "of", "the", "lettering", "on", "the", "covers", "of",
    "which"]), (.wh, ["which"])]

/-! ### The leftmost effect in a clause -/

-- (64)
theorem sov_strong :
    sov.Allows .strong .subject .sentence ∧ ¬ sov.Allows .strong .object .sentence ∧
      sov.Allows .strong .object .predicate ∧ ¬ sov.Allows .strong .subject .predicate := by
  decide +kernel

-- n. 17
theorem svo_strong :
    svo.Allows .strong .object .predicate ∧ ¬ svo.Allows .strong .subject .predicate := by
  decide +kernel

-- §6.1
theorem sov_strong_skipped :
    sov.Allows .strong .object .sentence [.subject] ∧
      ¬ sov.Allows .strong .subject .sentence [.subject] := by
  decide +kernel

-- n. 45
theorem sov_verb (c : Part) : ¬ sov.Allows .strong c .verb := by
  cases c <;> decide +kernel

-- (123)
theorem toWhichStudentsFriend_strong :
    toWhichStudentsFriend.Allows .strong .phrase .wh [.phrase] ∧
      ¬ toWhichStudentsFriend.Allows .strong .phrase .wh := by
  decide +kernel

-- (125), (126)
theorem not_strong_of_free :
    ¬ naSestreDrugaCejMateri.Allows .strong .phrase .wh ∧
      ¬ heightOfTheLettering.Allows .strong .phrase .wh := by
  decide +kernel

/-! ### The examples -/

/-- The constituent the morphosyntax marks is the focus, properly contains it, or is properly
contained in it ((76)–(78)). -/
inductive Mismatch
  | none
  | piedPiping
  | antiPiedPiping
  deriving DecidableEq, Repr

/-- A focus is marked by a particle on a phrase or by movement of the phrase. -/
inductive Process
  | particle
  | movement
  deriving DecidableEq, Repr

/-- The relation of host to focus that a label names. -/
def Mismatch.Holds : Mismatch → TreePath → TreePath → Prop
  | none, host, focus => host = focus
  | piedPiping, host, focus => host < focus
  | antiPiedPiping, host, focus => focus < host

instance (k : Mismatch) (host focus : TreePath) : Decidable (k.Holds host focus) := by
  cases k <;> unfold Mismatch.Holds <;> infer_instance

/-- The phase of each example, by the paper's number. -/
def frame : String → Option Frame
  | "(2)" | "(4)" | "(17b)" | "(18b)" | "(21)" | "(30a)" | "(30b)" | "(38)" | "(66a)" | "(66b)"
  | "(111a)" | "(111b)" => some sov
  | "(7)" | "(109a)" | "(109b)" | "(114a)" | "(114b)" => some svo
  | "(8)" => some sv
  | "(70a)" | "(70b)" => some vso
  | "(68a)" | "(68b)" => some themeGoalV
  | "(65)" | "(67)" => some goalThemeV
  | "(1)" | "(69a)" | "(69b)" => some vGoalTheme
  | "(3)" => some adjectiveObject
  | "(120a)" => some whosePicture
  | "(120b)" => some pictureOfWhom
  | "(121a)" => some whoseBrothersFriendsFather
  | "(121b)" => some fatherOfWhoseBrothersFriend
  | "(123)" => some toWhichStudentsFriend
  | "(124)" => some obEasRes
  | "(125)" => some naSestreDrugaCejMateri
  | "(126)" => some heightOfTheLettering
  | _ => none

/-- The examples name constituents by these labels. -/
def partLabels : List (String × Part) :=
  [("sentence", .sentence), ("subject", .subject), ("predicate", .predicate),
    ("object", .object), ("verb", .verb), ("goal", .goal), ("theme", .theme),
    ("adjective", .adjective), ("phrase", .phrase), ("wh", .wh),
    ("demonstrative", .demonstrative)]

/-- A row records of an example how it marks focus, the prominent phrases of its phase, the
phrase that hosts the particle or moves, the focus of each reading with its judgment, the variant
of the rule the paper reports for the construction, and the mismatch the paper labels it
with. -/
structure Row where
  process : Process
  prominent : List TreePath
  host : TreePath
  readings : List (TreePath × Judgment)
  requirement : Option LeftmostRequirement
  mismatch : Option Mismatch

/-- The row of an example. -/
def Row.ofDatum (d : Datum) : Option Row := do
  let fr ← frame d.source.paperLabel
  let process ← d.parse? "process" [("particle", Process.particle), ("movement", .movement)]
  let host ← (d.parse? "msf" partLabels).bind fr.site
  let skipped ← (d.features "skipped").mapM fun n ↦ (partLabels.lookup n).bind fr.site
  let readings ← d.readings.mapM fun rd ↦
    ((partLabels.lookup rd.1).bind fr.site).map (·, rd.2)
  pure ⟨process, BrananErlewine2023.prominent fr.phase skipped, host, readings,
    d.parse? "leftmost" [("strong", .strong), ("weak", .weak), ("free", .free)],
    d.parse? "mismatch" [("none", .none), ("piedPiping", .piedPiping),
      ("antiPiedPiping", .antiPiedPiping)]⟩

/-- The examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

theorem data_length : data.length = Examples.all.length := by decide +kernel

/-- An example is unmarked on a reading exactly when the variant of the rule that the paper
reports for its construction favors the phrase it marks for the focus of that reading. -/
theorem acceptable_iff_favors :
    ∀ d ∈ data, ∀ r ∈ d.requirement, ∀ rd ∈ d.readings,
      (rd.2 = .acceptable ↔ r.Favors d.prominent d.host rd.1) := by
  decide +kernel

theorem allows_of_marginal :
    ∀ d ∈ data, ∀ r ∈ d.requirement, ∀ rd ∈ d.readings,
      rd.2 = .marginal → r.Allows d.prominent d.host rd.1 := by
  decide +kernel

theorem not_allows_of_ungrammatical :
    ∀ d ∈ data, ∀ r ∈ d.requirement, ∀ rd ∈ d.readings,
      rd.2 = .ungrammatical → ¬ r.Allows d.prominent d.host rd.1 := by
  decide +kernel

theorem mismatch_holds :
    ∀ d ∈ data, ∀ k ∈ d.mismatch, ∀ rd ∈ d.readings, k.Holds d.host rd.1 := by
  decide +kernel

-- (1), (8)
theorem exists_mismatch (p : Process) (k : Mismatch) :
    ∃ d ∈ data, d.process = p ∧ d.mismatch = some k := by
  cases p <;> cases k <;> decide +kernel

end BrananErlewine2023
