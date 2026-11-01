module

public import Linglib.Core.Algebra.Free
public import Linglib.Core.Data.List.Sublist
public import Linglib.Data.Examples.HarizanovGribanova2019
public import Mathlib.Algebra.Free
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.List.Pairwise
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Harizanov and Gribanova (2019): Whither head movement?

Harizanov and Gribanova divide the work of head movement between two operations. Words are
formed by postsyntactic amalgamation: a head whose feature is [M:+] Raises into the next head
up, a head whose feature is [M:−] Lowers into the nearest head below, and the result is a
head-adjunction structure in the position of the target. Displacement is syntactic movement of a
head to the root, which comes first and forms no word. How complex a verb is and where it is
pronounced therefore vary independently, the same verbal complex surfacing in T in French, in
Neg in Russian and in V in Danish.

## Implementation notes

* A spine lists the heads of an extended projection, lowest first, each with its [M] feature;
  specifiers and adjuncts, which are islands for amalgamation, are left out. A head that has
  moved in the syntax occupies two positions of the spine, the paper's multidominance.
* A complex head is an element of the free magma over the heads, each product listing the lower
  constituent first. The paper's adjunction structures are unordered.
* Chain Reduction pronounces the highest occurrence, as in the paper's German, Danish and
  Russian derivations.
* The paper also places the English verbal complex in v, but takes T to join the English verb
  by an operation other than amalgamation, one that an intervening specifier blocks. No English
  derivation is given here.

## TODO

* The pronunciation of both occurrences of the verb in Hebrew bare-infinitive fronting.
* French nonfinite clauses, whose verbs stay low; the paper gives their [M] features no
  derivation.

## References

* [harizanov-gribanova-2019]
* [embick-noyer-2001]
* [travis-1984]
-/

@[expose] public section

namespace HarizanovGribanova2019

open FreeMagma

/-! ### Amalgamation -/

/-- The direction of amalgamation that the [M] feature of a head demands. A head with [M:+]
Raises into the next head up and a head with [M:−] Lowers into the nearest head below. -/
inductive Direction
  | raising | lowering
  deriving DecidableEq, Repr

variable {H : Type*}

/-- A complex head in the course of the postsyntactic derivation. -/
structure Amalgam (H : Type*) where
  /-- The head whose position the complex head occupies. -/
  site : H
  /-- The head-adjunction structure, each product listing the lower constituent first. -/
  complex : FreeMagma H
  /-- The [M] feature projected from the site. -/
  m : Option Direction
  deriving DecidableEq, Repr

namespace Amalgam

/-- A lexical head with its [M] feature, before any amalgamation. -/
def single (h : H) (m : Option Direction) : Amalgam H := ⟨h, of h, m⟩

/-- The heads that a complex head contains, lowest first. -/
def members (a : Amalgam H) : List H := (FreeMagma.lift FreeMonoid.of a.complex).toList

end Amalgam

/-- Bottom-up amalgamation. `below` lists the complex heads already formed, nearest first,
`pending` is the complex head that has Raised and awaits the next head up, and `above` lists the
heads still to be considered, lowest first. A Raising head adjoins to the next head up, whose
[M] feature the complex keeps, a Lowering head adjoins to the nearest complex head below, and a
demanded operation with no target is a derivation that does not converge. -/
def amalgamate : List (Amalgam H) → Option (FreeMagma H) → List (Amalgam H) →
    Option (List (Amalgam H))
  | below, none, [] => some below
  | _, some _, [] => none
  | below, pending, a :: above =>
    let complex := pending.elim a.complex (· * a.complex)
    match a.m, below with
    | none, below => amalgamate ({ a with complex } :: below) none above
    | some .raising, below => amalgamate below (some complex) above
    | some .lowering, [] => none
    | some .lowering, b :: below =>
      amalgamate ({ b with complex := b.complex * complex } :: below) none above

/-- The complex heads that amalgamation forms on a spine, lowest first, or `none` when the
postsyntactic derivation does not converge. -/
def amalgamateSpine (spine : List (Amalgam H)) : Option (List (Amalgam H)) :=
  (amalgamate [] none spine).map List.reverse

/-- Syntactic movement of the head `y` to the root, which precedes amalgamation, gives `y` a
second occurrence at the top of the spine. -/
def moveToRoot (spine : List (Amalgam H)) (y : H) : List (Amalgam H) :=
  spine ++ [Amalgam.single y none]

private theorem flatMap_members_amalgamate {below : List (Amalgam H)}
    {pending : Option (FreeMagma H)} {above out : List (Amalgam H)}
    (h : amalgamate below pending above = some out) :
    out.reverse.flatMap Amalgam.members =
      below.reverse.flatMap Amalgam.members ++
        pending.elim [] (fun x ↦ (FreeMagma.lift FreeMonoid.of x).toList) ++
        above.flatMap Amalgam.members := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;> cases pending <;>
      simp only [amalgamate, ha] at h <;>
      first | simpa [List.append_assoc, Amalgam.members] using ih h | simp at h

/-- The complex heads partition the spine in the order of syntactic composition: the affixes of
a complex head mirror that order, and no head gains or loses an occurrence. -/
theorem flatMap_members_amalgamateSpine {spine out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) :
    out.flatMap Amalgam.members = spine.flatMap Amalgam.members := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  simpa using flatMap_members_amalgamate h'

theorem members_infix_of_mem_amalgamateSpine {spine out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) {a : Amalgam H} (ha : a ∈ out) :
    a.members <:+: spine.flatMap Amalgam.members :=
  flatMap_members_amalgamateSpine h ▸ List.infix_of_mem_flatten (List.mem_map_of_mem ha)

theorem mem_of_mem_amalgamateSpine_of_nodup [DecidableEq H] {spine out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) (hnd : (spine.flatMap Amalgam.members).Nodup)
    {a : Amalgam H} (ha : a ∈ out) {x y z : H} (hx : x ∈ a.members) (hy : y ∈ a.members)
    (hz : z ∈ spine.flatMap Amalgam.members)
    (hxz : (spine.flatMap Amalgam.members).idxOf x ≤ (spine.flatMap Amalgam.members).idxOf z)
    (hzy : (spine.flatMap Amalgam.members).idxOf z ≤ (spine.flatMap Amalgam.members).idxOf y) :
    z ∈ a.members :=
  (members_infix_of_mem_amalgamateSpine h ha).mem_of_idxOf_le_of_le hnd hx hy hz hxz hzy

theorem amalgamate_append {below : List (Amalgam H)} {pending : Option (FreeMagma H)}
    {above out : List (Amalgam H)} (extra : List (Amalgam H))
    (h : amalgamate below pending above = some out) :
    amalgamate below pending (above ++ extra) = amalgamate out none extra := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;>
      simp only [List.cons_append, amalgamate, ha] at h ⊢ <;> first | exact ih h | simp at h

theorem amalgamateSpine_moveToRoot {spine out : List (Amalgam H)} (y : H)
    (h : amalgamateSpine spine = some out) :
    amalgamateSpine (moveToRoot spine y) = some (out ++ [Amalgam.single y none]) := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  rw [amalgamateSpine, moveToRoot, amalgamate_append _ h']
  cases out' <;> simp [amalgamate, Amalgam.single]

private theorem exists_site_eq_of_amalgamate {below : List (Amalgam H)}
    {pending : Option (FreeMagma H)} {extra res : List (Amalgam H)}
    (h : amalgamate below pending extra = some res) {b : Amalgam H} (hb : b ∈ below) :
    ∃ r ∈ res, r.site = b.site ∧ b.members <+: r.members := by
  induction extra generalizing below pending res b with
  | nil =>
    cases pending with
    | none =>
      obtain rfl : below = res := by simpa [amalgamate] using h
      exact ⟨b, hb, rfl, List.prefix_rfl⟩
    | some _ => simp [amalgamate] at h
  | cons a extra ih =>
    rcases below with _ | ⟨b₀, bs⟩
    · simp at hb
    rcases ha : a.m with _ | _ | _ <;> simp only [amalgamate, ha] at h
    · exact ih h (List.mem_cons_of_mem _ hb)
    · exact ih h hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · obtain ⟨r, hr, hs, hm⟩ := ih h (List.mem_cons_self ..)
        exact ⟨r, hr, hs, (List.prefix_append _ _).trans (by simpa [Amalgam.members] using hm)⟩
      · exact ih h (List.mem_cons_of_mem _ hb)

theorem exists_site_eq_of_append {spine extra out out' : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) (h' : amalgamateSpine (spine ++ extra) = some out')
    {a : Amalgam H} (ha : a ∈ out) : ∃ a' ∈ out', a'.site = a.site ∧ a.members <+: a'.members := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h'
  rw [amalgamate_append extra hr] at hr'
  simpa using exists_site_eq_of_amalgamate hr' (List.mem_reverse.mp ha)

theorem site_eq_of_append {spine extra out out' : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) (h' : amalgamateSpine (spine ++ extra) = some out')
    (hnd : ((spine ++ extra).flatMap Amalgam.members).Nodup) {a a' : Amalgam H} (ha : a ∈ out)
    (ha' : a' ∈ out') {x : H} (hx : x ∈ a.members) (hx' : x ∈ a'.members) : a'.site = a.site := by
  obtain ⟨b, hb, hs, hm⟩ := exists_site_eq_of_append h h' ha
  rw [← flatMap_members_amalgamateSpine h', List.nodup_flatMap] at hnd
  by_contra hne
  have : Std.Symm (Function.onFun List.Disjoint (Amalgam.members (H := H))) :=
    ⟨fun _ _ hd ↦ hd.symm⟩
  exact hnd.2.forall hb ha' (fun hba ↦ hne (hba ▸ hs)) (hm.subset hx) hx'

open Amalgam

theorem raising_and_lowering (x y z : H) :
    amalgamateSpine [single z (some .raising), single y none, single x (some .lowering)] =
      some [⟨y, of z * of y * of x, none⟩] :=
  rfl

theorem lowering_twice (x y z : H) :
    amalgamateSpine [single z none, single y (some .lowering), single x (some .lowering)] =
      some [⟨z, of z * of y * of x, none⟩] :=
  rfl

theorem lowering_without_target (x y z : H) :
    amalgamateSpine [single z (some .raising), single y (some .lowering), single x none] = none :=
  rfl

private theorem amalgamate_raising (below : List (Amalgam H)) (pending : Option (FreeMagma H))
    (lo : List H) (above : List (Amalgam H)) :
    amalgamate below pending (lo.map (single · (some .raising)) ++ above) =
      amalgamate below (lo.foldl (fun p h ↦ some (p.elim (of h) (· * of h))) pending) above := by
  induction lo generalizing pending with
  | nil => rfl
  | cons h lo ih => cases below <;> simpa [amalgamate, single] using ih _

private theorem amalgamate_none (below : List (Amalgam H)) (pending : Option (FreeMagma H))
    (s : H) (above : List (Amalgam H)) :
    amalgamate below pending (single s none :: above) =
      amalgamate (⟨s, pending.elim (of s) (· * of s), none⟩ :: below) none above := by
  cases pending <;> cases below <;> rfl

private theorem amalgamate_lowering (b : Amalgam H) (below : List (Amalgam H)) (hi : List H) :
    amalgamate (b :: below) none (hi.map (single · (some .lowering))) =
      some ({ b with complex := hi.foldl (· * of ·) b.complex } :: below) := by
  induction hi generalizing b with
  | nil => rfl
  | cons h hi ih => simpa [amalgamate, single] using ih _

private theorem foldl_raising (p : FreeMagma H) (lo : List H) :
    lo.foldl (fun p h ↦ some (p.elim (of h) (· * of h))) (some p) =
      some (lo.foldl (· * of ·) p) := by
  induction lo generalizing p with
  | nil => rfl
  | cons h lo ih => simpa using ih _

/-- The complex head of a spine can sit at any of its heads. With the heads below Raising and
the heads above Lowering, all the heads form one complex head there, each added to the complex
head of the heads below it. -/
theorem amalgamateSpine_raising_lowering {lo hi rest : List H} {s b : H}
    (h : lo ++ s :: hi = b :: rest) :
    amalgamateSpine (lo.map (single · (some .raising)) ++ single s none ::
        hi.map (single · (some .lowering))) =
      some [⟨s, rest.foldl (· * of ·) (of b), none⟩] := by
  rw [amalgamateSpine, amalgamate_raising, amalgamate_none, amalgamate_lowering]
  cases lo with
  | nil =>
    obtain ⟨rfl, rfl⟩ : s = b ∧ hi = rest := by simpa using h
    rfl
  | cons l lo =>
    obtain ⟨rfl, rfl⟩ : l = b ∧ lo ++ s :: hi = rest := by simpa using h
    simp [foldl_raising]

private theorem forall_isLeftComb_amalgamate {below : List (Amalgam H)}
    {pending : Option (FreeMagma H)} {hs : List (H × Option Direction)} {out : List (Amalgam H)}
    (h : amalgamate below pending (hs.map fun p ↦ single p.1 p.2) = some out) :
    (∀ a ∈ out, a.complex.IsLeftComb) ↔
      (∀ b ∈ below, b.complex.IsLeftComb) ∧ (∀ p ∈ pending, p.IsLeftComb) ∧
        ((pending.map fun _ ↦ Direction.raising) :: hs.map (·.2)).IsChain
          fun p q ↦ ¬ (p = some .raising ∧ q = some .lowering) := by
  induction hs generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate]
  | cons x hs ih =>
    obtain ⟨x, m⟩ := x
    rcases m with _ | _ | _ <;> cases below <;> cases pending <;>
      simp only [List.map_cons, amalgamate, single] at h <;>
      first
        | cases h
        | (rw [ih h]; rcases hs with _ | ⟨⟨y, n⟩, hs⟩ <;>
            simp [List.isChain_cons_cons] <;> tauto)

/-- Every complex head of a convergent derivation adds one head at a time, the bracketing that
mirrors the order of syntactic composition, exactly when no head Lowers right after a head has
Raised into it. -/
theorem forall_isLeftComb_iff {hs : List (H × Option Direction)} {out : List (Amalgam H)}
    (h : amalgamateSpine (hs.map fun p ↦ single p.1 p.2) = some out) :
    (∀ a ∈ out, a.complex.IsLeftComb) ↔
      (hs.map (·.2)).IsChain fun p q ↦ ¬ (p = some .raising ∧ q = some .lowering) := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  have := forall_isLeftComb_amalgamate hr
  rcases hs with _ | ⟨⟨y, n⟩, hs⟩ <;> simp_all [List.isChain_cons_cons]

/-- Chain Reduction pronounces the highest occurrence of a head, and a complex head formed at
one occurrence of a moved head belongs to all of them. `PronouncedFrom spine h x` says that the
complex head containing `h` is thereby pronounced in the position of `x` or above it. -/
def PronouncedFrom [DecidableEq H] (spine : List (Amalgam H)) (h x : H) : Prop :=
  ∃ out ∈ amalgamateSpine spine, ∃ a ∈ out,
    h ∈ a.members ∧ a.site ∈ (spine.map (·.site)).dropWhile (· ≠ x)

instance [DecidableEq H] (spine : List (Amalgam H)) (h x : H) :
    Decidable (PronouncedFrom spine h x) :=
  inferInstanceAs (Decidable (∃ out ∈ amalgamateSpine spine, _))

/-! ### The clausal spine -/

/-- The heads of the clausal spine in the paper's derivations. -/
inductive ClausalHead
  | V | v | Asp | Neg | T | Top
  deriving DecidableEq, Repr

open ClausalHead

/-- The Russian clause, in which V, v and Asp Raise and T Lowers. -/
def russian : List (Amalgam ClausalHead) :=
  [single V (some .raising), single v (some .raising), single Asp (some .raising), single Neg none,
    single T (some .lowering)]

/-- The Danish clause, in which v and T Lower. -/
def danish : List (Amalgam ClausalHead) :=
  [single V none, single v (some .lowering), single T (some .lowering)]

/-- The French finite clause, in which V, v and Neg Raise. The negator *pas* is a specifier and
not on the spine. -/
def french : List (Amalgam ClausalHead) :=
  [single V (some .raising), single v (some .raising), single Neg (some .raising), single T none]

/-- The German clause, in which V Raises into T. -/
def german : List (Amalgam ClausalHead) := [single V (some .raising), single T none]

/-- The Hebrew clause with a topic, in which V Raises into T. -/
def hebrew : List (Amalgam ClausalHead) :=
  [single V (some .raising), single T none, single Top none]

theorem russian_amalgamateSpine :
    amalgamateSpine russian = some [⟨.Neg, of V * of v * of Asp * of .Neg * of T, none⟩] :=
  rfl

theorem danish_amalgamateSpine : amalgamateSpine danish = some [⟨V, of V * of v * of T, none⟩] :=
  rfl

theorem french_amalgamateSpine :
    amalgamateSpine french = some [⟨T, of V * of v * of .Neg * of T, none⟩] :=
  rfl

/-! ### Syntactic movement of a head -/

theorem german_root :
    amalgamateSpine (moveToRoot german T) = some [⟨T, of V * of T, none⟩, single T none] :=
  rfl

theorem danish_root :
    amalgamateSpine (moveToRoot danish V) = some [⟨V, of V * of v * of T, none⟩, single V none] :=
  amalgamateSpine_moveToRoot V danish_amalgamateSpine

theorem russian_polarity_focus :
    amalgamateSpine (moveToRoot russian .Neg) =
      some [⟨.Neg, of V * of v * of Asp * of .Neg * of T, none⟩, single .Neg none] :=
  amalgamateSpine_moveToRoot .Neg russian_amalgamateSpine

theorem hebrew_fronting :
    amalgamateSpine (moveToRoot hebrew V) =
      some [⟨T, of V * of T, none⟩, single .Top none, single V none] :=
  rfl

theorem skipping :
    amalgamateSpine [single (0 : Fin 6) none, single 5 (some .lowering), single 4 none,
        single 3 none, single 2 (some .raising), single 1 (some .raising), single 0 none] =
      some [⟨0, of 0 * of 5, none⟩, single 4 none, single 3 none, ⟨0, of 2 * of 1 * of 0, none⟩] :=
  rfl

/-! ### Verb placement -/

/-- `spine? r` is the spine of the clause of `r`, a French or Russian finite clause, a Danish
embedded clause, or a Danish root clause, in which V has moved. -/
def spine? (r : Datum) : Option (List (Amalgam ClausalHead)) :=
  List.lookup (r.language, r.feature? "clause")
    [((.french, none), french), ((.russian, none), russian),
      ((.danish, some "embedded"), danish), ((.danish, some "root"), moveToRoot danish V)]

/-- The canonical tests for verb movement place a finite verb before a low adverb, sentential
negation or a floating quantifier exactly when it is pronounced in T or above. The paper's
examples of French, Danish and Russian finite clauses are acceptable in exactly the order that
the position of the verbal complex predicts. -/
theorem verb_placement :
    ∀ r ∈ Examples.all, r.feature? "phenomenon" = some "finiteVerbPlacement" →
      r.feature? "diagnostic" ≠ some "coordination" →
        ∃ s ∈ spine? r, ∃ b ∈ r.parse? "verbPrecedes" [("true", true), ("false", false)],
          (r.judgment = .acceptable ↔ (b = true ↔ PronouncedFrom s V T)) := by
  decide +kernel

end HarizanovGribanova2019
