module

public import Linglib.Semantics.Reference.Context.Overwrite
public import Linglib.Data.Examples.Deal2020
public import Mathlib.Data.Finset.Powerset

/-!
# Deal (2020): A Theory of Indexical Shift

Indexical shift comes from shifty operators at the edge of attitude complements, each overwriting
coordinates of the context with those of the index the attitude quantifies over. The operators sit
in a functional sequence, OP_LOC > OP_ADDR > OP_AUTH > OP_TIME (152), and a complement projects a
bottom segment of it (128), so an indexical class shifts only if the classes below it do (G2). The
complementizer may sit anywhere in the sequence; operators below it overwrite from the index and
force de se readings, those above it overwrite from the attitude event and do not (G3).

## Main definitions

* `sequence`, `stack n`: the functional sequence of shifty operators, lowest first, and a
  complement projecting the lowest `n` of them.
* `comp`, `eventOp`: the finite complementizer (140) and an event-based shifter (143)–(144).
* `complement n p`: a complement of size `n` with the complementizer after the lowest `p`.
* `Verb`: the complements a verb selects and where their complementizer sits.

## Main results

* `stack_eq`, `holdsAt_stack`: stacked operators overwrite the union of their coordinates (172),
  and unembedded they are vacuous (65).
* `mem_shifted_of_lt`: (G2); `mem_ofBundles_iff`: bundled classes shift together (§4.4).
* `complement_apply` and the `apply_complementContext` lemmas: an indexical in a complement reads
  the index, the attitude event or the utterance context by its class's position relative to C,
  (G3).
* `medial_eq_lowest`: Local Determination (77) in (83).
* `rows_shift`, `rows_deSe`, `rows_nonDeSe`, `rows_double_report`: the rows' judgments.

## Implementation notes

The rows are `Data.Examples.Deal2020`. Nez Perce has no temporal indexicals, so its complements'
OP_TIME is unobservable; the example of Anderson English is filed as English.

## TODO

* (G1), the hierarchy of verbs by complement size (§3.2.2), has no rows.
* (171): Nez Perce 'think' with a second person, which needs the defective addressee of (140c);
  the obligatoriness of Uyghur shift from bundling C with the operators (173).
* The quotation, role shift, fake indexical and indexiphor boundaries of chapter 5.

## References

* [deal-2020]
* [anand-nevins-2004]
-/

@[expose] public section

namespace Deal2020

open Kaplan (Character Context shiftyOp)
open Kaplan.Context (Coord dependsOn_agent equivPi localDepth overwrite)

universe u

variable {W E P T : Type u} {α : Type*}

/-! ### The functional sequence -/

/-- The functional sequence of shifty operators (152), lowest first: OP_TIME, OP_AUTH, OP_ADDR,
OP_LOC, each overwriting one coordinate of the context with that of the index (126). -/
def sequence : List Coord := [.time, .agent, .addressee, .position]

/-- A class's position in the sequence. -/
def rank (k : Coord) : ℕ := sequence.idxOf k

/-- The operators `l` stacked over `χ`, the first innermost. -/
def stackOf (l : List Coord) (χ : Character (Context W E P T) (Context W E P T) α) :
    Character (Context W E P T) (Context W E P T) α :=
  l.foldl (fun χ k ↦ shiftyOp {k} χ) χ

/-- A complement projecting the lowest `n` operators of the sequence (128). -/
def stack (n : ℕ) : Character (Context W E P T) (Context W E P T) α →
    Character (Context W E P T) (Context W E P T) α :=
  stackOf (sequence.take n)

/-- The classes a complement projecting the lowest `n` operators shifts. -/
def shifted (n : ℕ) : Finset Coord := (sequence.take n).toFinset

theorem mem_shifted_iff {n : ℕ} {k : Coord} : k ∈ shifted n ↔ k ∈ sequence ∧ rank k < n := by
  rw [shifted, List.mem_toFinset]
  refine ⟨fun h ↦ ?_, fun ⟨h, h'⟩ ↦ (List.mem_take_iff_idxOf_lt h).2 h'⟩
  have hk := List.mem_of_mem_take h
  exact ⟨hk, (List.mem_take_iff_idxOf_lt hk).1 h⟩

theorem shifted_mono : Monotone shifted := fun _ _ h _ hk ↦
  mem_shifted_iff.2 ⟨(mem_shifted_iff.1 hk).1, (mem_shifted_iff.1 hk).2.trans_le h⟩

theorem stackOf_eq (l : List Coord) (χ : Character (Context W E P T) (Context W E P T) α) :
    stackOf l χ = shiftyOp l.toFinset χ := by
  induction l generalizing χ with
  | nil => simp [stackOf]
  | cons k l ih =>
    simp only [stackOf, List.foldl_cons] at ih ⊢
    rw [ih, Kaplan.shiftyOp_shiftyOp, List.toFinset_cons, Finset.insert_eq, Finset.union_comm]

/-- A stack of operators overwrites the union of their coordinates: the operators of (126) make
noninteracting changes to the context, and a lexical bundle is their composition (172). -/
theorem stack_eq (n : ℕ) (χ : Character (Context W E P T) (Context W E P T) α) :
    stack n χ = shiftyOp (shifted n) χ :=
  stackOf_eq _ χ

/-- (65): unembedded, a stack of operators is vacuous, since a sentence is true at a context when
it is true at that context taken as its own index (64). -/
theorem holdsAt_stack (n : ℕ) (χ : Character (Context W E P T) (Context W E P T) Prop)
    (c : Context W E P T) : (stack n χ).HoldsAt id c ↔ χ.HoldsAt id c := by
  rw [stack_eq]
  exact Kaplan.holdsAt_shiftyOp _ χ c

/-- (G2): in a complement of any size, an indexical class shifts only if every class below it in
the sequence shifts as well. -/
theorem mem_shifted_of_lt {n : ℕ} {k k' : Coord} (hk : k ∈ shifted n) (hk' : k' ∈ sequence)
    (h : rank k' < rank k) : k' ∈ shifted n :=
  mem_shifted_iff.2 ⟨hk', h.trans (mem_shifted_iff.1 hk).2⟩

/-! ### The complementizer and the de se -/

variable {Ev : Type*}

/-- The finite complementizer (140): it takes the attitude event `e` and quantifies over the indices
`R e` centered on what the event's external argument identifies in it as herself, her addressee,
her location and her time. -/
def comp (R : Ev → Set (Context W E P T))
    (χ : Character (Context W E P T) (Context W E P T) Prop) :
    Ev → Character (Context W E P T) (Context W E P T) Prop :=
  fun e c _ ↦ ∀ i ∈ R e, χ c i

/-- An event-based shifter (143)–(144): it overwrites the coordinates `s` of the context with those
of the attitude event, its author, addressee, location and time `ev e`. -/
def eventOp (ev : Ev → Context W E P T) (s : Finset Coord)
    (φ : Ev → Character (Context W E P T) (Context W E P T) Prop) :
    Ev → Character (Context W E P T) (Context W E P T) Prop :=
  fun e c i ↦ φ e (overwrite s c (ev e)) i

/-- The event-based shifters `l` stacked over `φ`, the first innermost. -/
def eventStackOf (ev : Ev → Context W E P T) (l : List Coord)
    (φ : Ev → Character (Context W E P T) (Context W E P T) Prop) :
    Ev → Character (Context W E P T) (Context W E P T) Prop :=
  l.foldl (fun φ k ↦ eventOp ev {k} φ) φ

theorem eventStackOf_eq (ev : Ev → Context W E P T) (l : List Coord)
    (φ : Ev → Character (Context W E P T) (Context W E P T) Prop) :
    eventStackOf ev l φ = eventOp ev l.toFinset φ := by
  induction l generalizing φ with
  | nil => funext e c i; simp [eventStackOf, eventOp]
  | cons k l ih =>
    simp only [eventStackOf, List.foldl_cons] at ih ⊢
    funext e c i
    simp only [ih, eventOp, Kaplan.Context.overwrite_overwrite, List.toFinset_cons,
      Finset.insert_eq, Finset.union_comm]

/-- The classes shifted from the index, and so read de se, in a complement of size `n` with the
complementizer after the lowest `p` operators. -/
def deSe (n p : ℕ) : Finset Coord := shifted (min p n)

/-- The classes shifted from the attitude event in the same complement. -/
def eventShifted (n p : ℕ) : Finset Coord := shifted n \ shifted p

/-- A complement of size `n` with the complementizer after the lowest `p` operators (145)–(148):
the operators below the complementizer, overwriting from the index, then the complementizer, then
the operators above it, overwriting from the event. -/
def complement (n p : ℕ) (R : Ev → Set (Context W E P T)) (ev : Ev → Context W E P T)
    (χ : Character (Context W E P T) (Context W E P T) Prop) :
    Ev → Character (Context W E P T) (Context W E P T) Prop :=
  eventStackOf ev ((sequence.take n).filter (· ∉ sequence.take p)) (comp R (stack (min p n) χ))

theorem complement_apply (n p : ℕ) (R : Ev → Set (Context W E P T)) (ev : Ev → Context W E P T)
    (χ : Character (Context W E P T) (Context W E P T) Prop) (e : Ev) (c i : Context W E P T) :
    complement n p R ev χ e c i ↔ ∀ i' ∈ R e,
      χ (overwrite (deSe n p) (overwrite (eventShifted n p) c (ev e)) i') i' := by
  have : ((sequence.take n).filter (· ∉ sequence.take p)).toFinset = eventShifted n p := by
    ext k; simp [eventShifted, shifted]
  rw [complement, eventStackOf_eq, this, stack_eq]
  rfl

section apply_complementContext

variable {f : Context W E P T → α} {k : Coord} (hf : DependsOn (f ∘ equivPi.symm) {k}) {n p : ℕ}
  (c x i : Context W E P T)
include hf

/-- In a complement, an indexical whose operator sits below the complementizer reads the centered
index: TP⟨author(i), addr(i), …⟩ in Nez Perce (145). -/
theorem apply_complementContext_of_mem_deSe (h : k ∈ deSe n p) :
    f (overwrite (deSe n p) (overwrite (eventShifted n p) c x) i) = f i :=
  Kaplan.Context.apply_overwrite_of_subset hf (by simpa using h) _ _

/-- An indexical whose operator sits above the complementizer reads the attitude event:
TP⟨…, LOC(e)⟩ in Nez Perce (145). -/
theorem apply_complementContext_of_mem_eventShifted (h : k ∈ eventShifted n p) :
    f (overwrite (deSe n p) (overwrite (eventShifted n p) c x) i) = f x := by
  have hk : k ∉ deSe n p := fun hk ↦
    (Finset.mem_sdiff.1 h).2 (shifted_mono (min_le_left p n) hk)
  rw [Kaplan.Context.apply_overwrite_of_disjoint hf (by simpa using hk),
    Kaplan.Context.apply_overwrite_of_subset hf (by simpa using h)]

theorem apply_complementContext_of_notMem (h : k ∉ shifted n) :
    f (overwrite (deSe n p) (overwrite (eventShifted n p) c x) i) = f c := by
  have h₁ : k ∉ deSe n p := fun hk ↦ h (shifted_mono (min_le_right p n) hk)
  have h₂ : k ∉ eventShifted n p := fun hk ↦ h (Finset.mem_sdiff.1 hk).1
  rw [Kaplan.Context.apply_overwrite_of_disjoint hf (by simpa using h₁),
    Kaplan.Context.apply_overwrite_of_disjoint hf (by simpa using h₂)]

end apply_complementContext

/-! ### Local Determination -/

/-- (83): in *Katie says that I think that I am here*, the medial clause's first person is the
author of the medial thought, so whatever operators the two complements carry, the lowest first
person refers as the medial one does: both shifted or neither (77). -/
theorem medial_eq_lowest (s₁ s₂ : Finset Coord) (c j₁ j₂ : Context W E P T)
    (hj₂ : j₂.agent = (overwrite s₁ c j₁).agent) :
    (overwrite s₂ (overwrite s₁ c j₁) j₂).agent = (overwrite s₁ c j₁).agent :=
  Kaplan.Context.apply_overwrite_of_apply_eq (f := Context.agent) dependsOn_agent hj₂

/-! ### Lexical bundling -/

/-- OP_PERS, the bundle of OP_AUTH and OP_ADDR (58), (172). -/
abbrev opPers : Finset Coord := {.agent, .addressee}

/-- OP_ADV, the Korean bundle of OP_LOC and OP_TIME (§4.2.2). -/
abbrev opAdv : Finset Coord := {.position, .time}

/-- (172): OP_PERS is the composition of OP_ADDR and OP_AUTH. -/
theorem shiftyOp_opPers (χ : Character (Context W E P T) (Context W E P T) α) :
    shiftyOp {.addressee} (shiftyOp {.agent} χ) = shiftyOp opPers χ := by
  rw [Kaplan.shiftyOp_shiftyOp]
  rfl

/-- The coordinate sets a complement may overwrite when its verb selects the sizes `ns` (128). -/
def ofSizes (ns : Finset ℕ) : Finset (Finset Coord) := ns.image shifted

/-- The coordinate sets a complement may overwrite with any combination of the bundles `bs`, each
bundle overwriting all its coordinates or none (§4.2.2). -/
def ofBundles (bs : Finset (Finset Coord)) : Finset (Finset Coord) :=
  bs.powerset.image fun t ↦ t.sup id

theorem mem_of_mem_ofSizes {ns : Finset ℕ} {s : Finset Coord} (hs : s ∈ ofSizes ns) {k k' : Coord}
    (hk : k ∈ s) (hk' : k' ∈ sequence) (h : rank k' < rank k) : k' ∈ s := by
  obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hs
  exact mem_shifted_of_lt hk hk' h

/-- Classes that belong to the same bundles shift together: (G2) can fail only where a bundle joins
nonadjacent operators, and such a failure shows as co-shifting, as of Korean locatives and temporals
in (175) (§4.4). -/
theorem mem_ofBundles_iff {bs : Finset (Finset Coord)} {k k' : Coord}
    (h : ∀ b ∈ bs, k ∈ b ↔ k' ∈ b) {s : Finset Coord} (hs : s ∈ ofBundles bs) : k ∈ s ↔ k' ∈ s := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
  simp only [Finset.mem_sup, id]
  exact exists_congr fun b ↦ and_congr_right fun hb ↦ h b (Finset.mem_powerset.1 ht hb)

/-! ### The languages -/

/-- A verb's complements: the coordinate sets they may overwrite, and the number of operators below
their complementizer where the book places it. -/
structure Verb where
  /-- The coordinate sets the verb's complements may overwrite. -/
  options : Finset (Finset Coord)
  /-- The number of operators below the complementizer. -/
  cPosition : Option ℕ

/-- Nez Perce verbs of speech and thought (130): OP_PERS (172), optionally with OP_LOC above it,
or neither (§3.1.3), with C between OP_LOC and OP_ADDR (145). -/
def nezPerce : Verb := ⟨ofSizes {0, 3, 4}, some 3⟩

/-- Zazaki *vano* 'say': the whole sequence or none of it, with C above it (147). -/
def zazakiSay : Verb := ⟨ofSizes {0, 4}, some 4⟩

/-- Uyghur 'say': OP_ADDR and OP_AUTH obligatorily, with C between them (146). -/
def uyghurSay : Verb := ⟨ofSizes {3}, some 2⟩

/-- Slave *hadi* 'say': OP_AUTH obligatorily (§3.1.3); the book does not place its C. -/
def slaveSay : Verb := ⟨ofSizes {2}, none⟩

/-- Dhaasanac 'say': the person shifters, whose optionality the book does not report, with C below
OP_AUTH (148). (148) predates OP_TIME; C is placed above it here, which no row tests. -/
def dhaasanacSay : Verb := ⟨ofSizes {3}, some 1⟩

/-- Korean 'say': OP_PERS and OP_ADV in any combination (§4.2.2), with C above them. -/
def koreanSay : Verb := ⟨ofBundles {opPers, opAdv}, some 4⟩

/-- Korean 'think': OP_ADV alone (161), (162), with C above it. -/
def koreanThink : Verb := ⟨ofBundles {opAdv}, some 4⟩

/-- Anderson English 'say': OP_TIME alone, with C below it (167). -/
def andersonSay : Verb := ⟨ofSizes {0, 1}, some 0⟩

/-- The rows' verbs. -/
def verb? : String → Option Verb
  | "nezperce_say" | "nezperce_think" => some nezPerce
  | "zazaki_say" => some zazakiSay
  | "uyghur_say" => some uyghurSay
  | "slave_say" => some slaveSay
  | "dhaasanac_say" => some dhaasanacSay
  | "korean_say" => some koreanSay
  | "korean_think" => some koreanThink
  | "anderson_say" => some andersonSay
  | _ => none

/-- The coordinate each indexical of the rows reads. -/
def coord? : String → Option Coord
  | "I" => some .agent
  | "you" => some .addressee
  | "here" => some .position
  | "today" | "tomorrow" | "yesterday" => some .time
  | _ => none

/-- The positions, among a row's indexicals, of those a named reading takes from the reported
context. -/
def shifted? : String → Option (Finset ℕ)
  | "reported context" | "both reported" => some {0, 1}
  | "utterance context" | "both utterance" => some ∅
  | "first reported only" => some {0}
  | "second reported only" => some {1}
  | _ => none

/-- The depth, among the utterance context and two reported ones, from which a named reading of
the lowest of two reports takes its indexicals. -/
def depth? : String → Option ℕ
  | "utterance context" => some 0
  | "intermediate reported context" => some 1
  | "lowest reported context" => some 2
  | _ => none

/-- A row's verb, and the coordinates its indexicals read. -/
def verbCoords? (r : Datum) : Option (Verb × List Coord) :=
  ((r.feature? "verb").bind verb?).bind fun v ↦ ((r.features "indexical").mapM coord?).map (v, ·)

/-- Every judged reading of the rows' indexicals is available, at worst marginal, exactly when a
complement the verb selects overwrites the coordinates of the indexicals the reading shifts and no
others: (G2) and Shift Together (72) in Nez Perce, Uyghur and Slave, and Korean's bundles. -/
theorem rows_shift :
    ∀ r ∈ Examples.all, ∀ p ∈ (verbCoords? r).toList, ∀ x ∈ r.readings,
      ∀ ps ∈ (shifted? x.1).toList,
        (.marginal ≤ x.2 ↔ ∃ s ∈ p.1.options, ∀ q ∈ p.2.zipIdx, (q.1 ∈ s ↔ q.2 ∈ ps)) := by
  decide +kernel

/-- A judged de se reading of the rows' shifted indexicals is available exactly when a complement
the verb selects shifts their coordinates. -/
theorem rows_deSe :
    ∀ r ∈ Examples.all, ∀ p ∈ (verbCoords? r).toList, ∀ x ∈ r.readings, x.1 = "de se" →
      (.marginal ≤ x.2 ↔ ∃ s ∈ p.1.options, ∀ k ∈ p.2, k ∈ s) := by
  decide +kernel

/-- (G3) in the rows: a judged non-de se reading of the rows' shifted indexicals is available
exactly when a complement the verb selects shifts their coordinates with operators above the
complementizer, `eventShifted n c = shifted n \ shifted c`. -/
theorem rows_nonDeSe :
    ∀ r ∈ Examples.all, ∀ p ∈ (verbCoords? r).toList, ∀ c ∈ p.1.cPosition.toList,
      ∀ x ∈ r.readings, x.1 = "non-de se" →
        (.marginal ≤ x.2 ↔ ∃ s ∈ p.1.options, ∀ k ∈ p.2, k ∈ s \ shifted c) := by
  decide +kernel

/-- (87): in the lowest of two reports, a reading of a first person is available exactly when
complements of the two verbs make it read the context at that depth (Local Determination), the
lowest complement overwriting the addressee to shift its second person. -/
theorem rows_double_report :
    ∀ r ∈ Examples.all, r.feature? "lowest_shift" = some "yes" →
      ∀ p ∈ (verbCoords? r).toList, ∀ v₂ ∈ ((r.feature? "lower_verb").bind verb?).toList,
        ∀ x ∈ r.readings, ∀ d ∈ (depth? x.1).toList,
          (.marginal ≤ x.2 ↔ ∃ s₁ ∈ p.1.options, ∃ s₂ ∈ v₂.options, .addressee ∈ s₂ ∧
            ∀ k ∈ p.2, localDepth [s₁, s₂] k = d) := by
  decide +kernel

example : (Examples.all.filter fun r ↦ (verbCoords? r).isSome).length = 24 := by decide +kernel

end Deal2020
