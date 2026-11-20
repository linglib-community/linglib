module

public import Linglib.Syntax.Minimalist.Category
public import Linglib.Core.Data.List.Sublist
public import Linglib.Data.Examples.HarizanovGribanova2019
public import Mathlib.Algebra.Free
public import Mathlib.Algebra.FreeMonoid.FreeSemigroup
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
* A complex head is an element of the free magma over the heads. The paper's adjunction
  structures are unordered; each product here lists the lower constituent first, so that the
  heads of a complex head, read off in order, are a stretch of the spine.
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

/-- A head of the spine with the [M] feature its lexical item is specified for. -/
structure Terminal (H : Type*) where
  /-- The head. -/
  head : H
  /-- The [M] feature, absent on a head that does not amalgamate. -/
  m : Option Direction
  deriving DecidableEq, Repr

/-- A complex head that amalgamation has formed. -/
structure Amalgam (H : Type*) where
  /-- The head whose position the complex head occupies. -/
  site : H
  /-- The head-adjunction structure, each product listing the lower constituent first. -/
  complex : FreeMagma H
  deriving DecidableEq, Repr

/-- The heads that a complex head contains, lowest first. -/
def Amalgam.members (a : Amalgam H) : List H := (toFreeSemigroup a.complex).toFreeMonoid.toList

/-- Bottom-up amalgamation. `below` lists the complex heads already formed, nearest first,
`pending` is the complex head that has Raised and awaits the next head up, and `above` lists the
heads still to be considered, lowest first. A Raising head adjoins to the next head up, whose
[M] feature the complex takes on, a Lowering head adjoins to the nearest complex head below, and
a demanded operation with no target is a derivation that does not converge. -/
def amalgamate : List (Amalgam H) → Option (FreeMagma H) → List (Terminal H) →
    Option (List (Amalgam H))
  | below, none, [] => some below
  | _, some _, [] => none
  | below, pending, a :: above =>
    let complex := pending.elim (of a.head) (· * of a.head)
    match a.m, below with
    | none, below => amalgamate (⟨a.head, complex⟩ :: below) none above
    | some .raising, below => amalgamate below (some complex) above
    | some .lowering, [] => none
    | some .lowering, b :: below => amalgamate (⟨b.site, b.complex * complex⟩ :: below) none above

/-- The complex heads that amalgamation forms on a spine, lowest first, or `none` when the
postsyntactic derivation does not converge. -/
def amalgamateSpine (spine : List (Terminal H)) : Option (List (Amalgam H)) :=
  (amalgamate [] none spine).map List.reverse

/-- Syntactic movement of the head `y` to the root, which precedes amalgamation, gives `y` a
second occurrence at the top of the spine. -/
def moveToRoot (spine : List (Terminal H)) (y : H) : List (Terminal H) := spine ++ [⟨y, none⟩]

private theorem flatMap_members_amalgamate {below : List (Amalgam H)}
    {pending : Option (FreeMagma H)} {above : List (Terminal H)} {out : List (Amalgam H)}
    (h : amalgamate below pending above = some out) :
    out.reverse.flatMap Amalgam.members =
      below.reverse.flatMap Amalgam.members ++
        pending.elim [] (fun x ↦ (toFreeSemigroup x).toFreeMonoid.toList) ++
        above.map (·.head) := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;> cases pending <;>
      simp only [amalgamate, ha] at h <;>
      first | simpa [List.append_assoc, Amalgam.members] using ih h | simp at h

/-- The complex heads partition the spine in the order of syntactic composition: the affixes of
a complex head mirror that order, and no head gains or loses an occurrence. -/
theorem flatMap_members_amalgamateSpine {spine : List (Terminal H)} {out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) :
    out.flatMap Amalgam.members = spine.map (·.head) := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  simpa using flatMap_members_amalgamate h'

theorem members_infix_of_mem_amalgamateSpine {spine : List (Terminal H)} {out : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) {a : Amalgam H} (ha : a ∈ out) :
    a.members <:+: spine.map (·.head) :=
  flatMap_members_amalgamateSpine h ▸ List.infix_of_mem_flatten (List.mem_map_of_mem ha)

theorem mem_of_mem_amalgamateSpine_of_nodup [DecidableEq H] {spine : List (Terminal H)}
    {out : List (Amalgam H)} (h : amalgamateSpine spine = some out)
    (hnd : (spine.map (·.head)).Nodup) {a : Amalgam H} (ha : a ∈ out) {x y z : H}
    (hx : x ∈ a.members) (hy : y ∈ a.members) (hz : z ∈ spine.map (·.head))
    (hxz : (spine.map (·.head)).idxOf x ≤ (spine.map (·.head)).idxOf z)
    (hzy : (spine.map (·.head)).idxOf z ≤ (spine.map (·.head)).idxOf y) :
    z ∈ a.members :=
  (members_infix_of_mem_amalgamateSpine h ha).mem_of_idxOf_le_of_le hnd hx hy hz hxz hzy

theorem amalgamate_append {below : List (Amalgam H)} {pending : Option (FreeMagma H)}
    {above : List (Terminal H)} {out : List (Amalgam H)} (extra : List (Terminal H))
    (h : amalgamate below pending above = some out) :
    amalgamate below pending (above ++ extra) = amalgamate out none extra := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;>
      simp only [List.cons_append, amalgamate, ha] at h ⊢ <;> first | exact ih h | simp at h

theorem amalgamateSpine_moveToRoot {spine : List (Terminal H)} {out : List (Amalgam H)} (y : H)
    (h : amalgamateSpine spine = some out) :
    amalgamateSpine (moveToRoot spine y) = some (out ++ [⟨y, of y⟩]) := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  rw [amalgamateSpine, moveToRoot, amalgamate_append _ h']
  cases out' <;> simp [amalgamate]

private theorem exists_site_eq_of_amalgamate {below : List (Amalgam H)}
    {pending : Option (FreeMagma H)} {extra : List (Terminal H)} {res : List (Amalgam H)}
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

theorem exists_site_eq_of_append {spine extra : List (Terminal H)} {out out' : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) (h' : amalgamateSpine (spine ++ extra) = some out')
    {a : Amalgam H} (ha : a ∈ out) : ∃ a' ∈ out', a'.site = a.site ∧ a.members <+: a'.members := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h'
  rw [amalgamate_append extra hr] at hr'
  simpa using exists_site_eq_of_amalgamate hr' (List.mem_reverse.mp ha)

theorem site_eq_of_append {spine extra : List (Terminal H)} {out out' : List (Amalgam H)}
    (h : amalgamateSpine spine = some out) (h' : amalgamateSpine (spine ++ extra) = some out')
    (hnd : ((spine ++ extra).map (·.head)).Nodup) {a a' : Amalgam H} (ha : a ∈ out)
    (ha' : a' ∈ out') {x : H} (hx : x ∈ a.members) (hx' : x ∈ a'.members) : a'.site = a.site := by
  obtain ⟨b, hb, hs, hm⟩ := exists_site_eq_of_append h h' ha
  rw [← flatMap_members_amalgamateSpine h', List.nodup_flatMap] at hnd
  by_contra hne
  have : Std.Symm (Function.onFun List.Disjoint (Amalgam.members (H := H))) :=
    ⟨fun _ _ hd ↦ hd.symm⟩
  exact hnd.2.forall hb ha' (fun hba ↦ hne (hba ▸ hs)) (hm.subset hx) hx'

theorem raising_and_lowering (x y z : H) :
    amalgamateSpine [⟨z, some .raising⟩, ⟨y, none⟩, ⟨x, some .lowering⟩] =
      some [⟨y, of z * of y * of x⟩] :=
  rfl

theorem lowering_twice (x y z : H) :
    amalgamateSpine [⟨z, none⟩, ⟨y, some .lowering⟩, ⟨x, some .lowering⟩] =
      some [⟨z, of z * of y * of x⟩] :=
  rfl

theorem lowering_without_target (x y z : H) :
    amalgamateSpine [⟨z, some .raising⟩, ⟨y, some .lowering⟩, ⟨x, none⟩] = none :=
  rfl

private theorem amalgamate_raising (below : List (Amalgam H)) (pending : Option (FreeMagma H))
    (lo : List H) (above : List (Terminal H)) :
    amalgamate below pending (lo.map (Terminal.mk · (some .raising)) ++ above) =
      amalgamate below (lo.foldl (fun p h ↦ some (p.elim (of h) (· * of h))) pending) above := by
  induction lo generalizing pending with
  | nil => rfl
  | cons h lo ih => cases below <;> simpa [amalgamate] using ih _

private theorem amalgamate_none (below : List (Amalgam H)) (pending : Option (FreeMagma H))
    (s : H) (above : List (Terminal H)) :
    amalgamate below pending (⟨s, none⟩ :: above) =
      amalgamate (⟨s, pending.elim (of s) (· * of s)⟩ :: below) none above := by
  cases pending <;> cases below <;> rfl

private theorem amalgamate_lowering (b : Amalgam H) (below : List (Amalgam H)) (hi : List H) :
    amalgamate (b :: below) none (hi.map (Terminal.mk · (some .lowering))) =
      some (⟨b.site, hi.foldl (· * of ·) b.complex⟩ :: below) := by
  induction hi generalizing b with
  | nil => rfl
  | cons h hi ih => simpa [amalgamate] using ih _

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
    amalgamateSpine (lo.map (Terminal.mk · (some .raising)) ++ ⟨s, none⟩ ::
        hi.map (Terminal.mk · (some .lowering))) =
      some [⟨s, rest.foldl (· * of ·) (of b)⟩] := by
  rw [amalgamateSpine, amalgamate_raising, amalgamate_none, amalgamate_lowering]
  cases lo with
  | nil =>
    obtain ⟨rfl, rfl⟩ : s = b ∧ hi = rest := by simpa using h
    rfl
  | cons l lo =>
    obtain ⟨rfl, rfl⟩ : l = b ∧ lo ++ s :: hi = rest := by simpa using h
    simp [foldl_raising]

/-- Chain Reduction pronounces the highest occurrence of a head, and a complex head formed at
one occurrence of a moved head belongs to all of them. `PronouncedFrom spine h x` says that the
complex head containing `h` is thereby pronounced in the position of `x` or above it. -/
def PronouncedFrom [DecidableEq H] (spine : List (Terminal H)) (h x : H) : Prop :=
  ∃ out ∈ amalgamateSpine spine, ∃ a ∈ out,
    h ∈ a.members ∧ a.site ∈ (spine.map (·.head)).dropWhile (· ≠ x)

instance [DecidableEq H] (spine : List (Terminal H)) (h x : H) :
    Decidable (PronouncedFrom spine h x) :=
  inferInstanceAs (Decidable (∃ out ∈ amalgamateSpine spine, _))

/-! ### The clausal spine -/

open Minimalist.Cat

/-- The Russian clause, in which V, v and Asp Raise and T Lowers. -/
def russian : List (Terminal Minimalist.Cat) :=
  [⟨V, some .raising⟩, ⟨v, some .raising⟩, ⟨Asp, some .raising⟩, ⟨.Neg, none⟩, ⟨T, some .lowering⟩]

/-- The Danish clause, in which v and T Lower. -/
def danish : List (Terminal Minimalist.Cat) :=
  [⟨V, none⟩, ⟨v, some .lowering⟩, ⟨T, some .lowering⟩]

/-- The French finite clause, in which V, v and Neg Raise. The negator *pas* is a specifier and
not on the spine. -/
def french : List (Terminal Minimalist.Cat) :=
  [⟨V, some .raising⟩, ⟨v, some .raising⟩, ⟨.Neg, some .raising⟩, ⟨T, none⟩]

/-- The German clause, in which V Raises into T. -/
def german : List (Terminal Minimalist.Cat) := [⟨V, some .raising⟩, ⟨T, none⟩]

/-- The Hebrew clause with a topic, in which V Raises into T. -/
def hebrew : List (Terminal Minimalist.Cat) := [⟨V, some .raising⟩, ⟨T, none⟩, ⟨Top, none⟩]

theorem russian_amalgamateSpine :
    amalgamateSpine russian = some [⟨.Neg, of V * of v * of Asp * of .Neg * of T⟩] :=
  rfl

theorem danish_amalgamateSpine : amalgamateSpine danish = some [⟨V, of V * of v * of T⟩] :=
  rfl

theorem french_amalgamateSpine :
    amalgamateSpine french = some [⟨T, of V * of v * of .Neg * of T⟩] :=
  rfl

/-! ### Syntactic movement of a head -/

theorem german_root :
    amalgamateSpine (moveToRoot german T) = some [⟨T, of V * of T⟩, ⟨T, of T⟩] :=
  rfl

theorem danish_root :
    amalgamateSpine (moveToRoot danish V) = some [⟨V, of V * of v * of T⟩, ⟨V, of V⟩] :=
  amalgamateSpine_moveToRoot V danish_amalgamateSpine

theorem russian_polarity_focus :
    amalgamateSpine (moveToRoot russian .Neg) =
      some [⟨.Neg, of V * of v * of Asp * of .Neg * of T⟩, ⟨.Neg, of .Neg⟩] :=
  amalgamateSpine_moveToRoot .Neg russian_amalgamateSpine

theorem hebrew_fronting :
    amalgamateSpine (moveToRoot hebrew V) = some [⟨T, of V * of T⟩, ⟨.Top, of .Top⟩, ⟨V, of V⟩] :=
  rfl

theorem skipping :
    amalgamateSpine [⟨(0 : Fin 6), none⟩, ⟨5, some .lowering⟩, ⟨4, none⟩, ⟨3, none⟩,
        ⟨2, some .raising⟩, ⟨1, some .raising⟩, ⟨0, none⟩] =
      some [⟨0, of 0 * of 5⟩, ⟨4, of 4⟩, ⟨3, of 3⟩, ⟨0, of 2 * of 1 * of 0⟩] :=
  rfl

/-! ### Verb placement -/

/-- `spine? r` is the spine of the clause of `r`, a French or Russian finite clause, a Danish
embedded clause, or a Danish root clause, in which V has moved. -/
def spine? (r : Datum) : Option (List (Terminal Minimalist.Cat)) :=
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
