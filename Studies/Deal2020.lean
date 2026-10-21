module

public import Studies.AnandNevins2004
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

* `sequence`: the functional sequence of shifty operators, lowest first.
* `stack n`: a complement projecting the lowest `n` operators.
* `comp`, `eventOp`: the finite complementizer (140) and an event-based shifter (143)–(144).
* `complement n p`: a complement of size `n` with the complementizer after the lowest `p`.

## Main results

* `stack_eq`, `shiftyOp_opPers`: stacked operators overwrite the union of their coordinates, and a
  bundle is their composition (172).
* `mem_shifted_of_lt`: (G2); `mem_ofBundles_iff`: bundled classes shift together (§4.4).
* `apply_complementContext`, `mem_deSe_of_lt`: an indexical in a complement reads the index, the
  attitude event or the utterance context by its class's position relative to C; (G3).
* `medial_eq_lowest`, `lowest_of_agent_mem`: Local Determination (77) in (83) and (87).
* `rows_shift`, `rows_deSe`, `rows_nonDeSe`, `rows_double_report`: the rows' judgments.

## Implementation notes

A language's verbs are given by the coordinate sets their complements may overwrite (`options?`),
built from sizes of bottom segments or from bundles, and by the position of the complementizer
(`cPosition?`); the rows are `Data.Examples.Deal2020`. Nez Perce has no temporal indexicals, so its
complements' OP_TIME is unobservable. The example of Anderson English is filed as English.

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
open Kaplan.Context (Coord overwrite DependsOn)

variable {W E P T α : Type*}

/-! ### The functional sequence -/

/-- The functional sequence of shifty operators (152), lowest first: OP_TIME, OP_AUTH, OP_ADDR,
OP_LOC, each overwriting one coordinate of the context with that of the index (126). -/
def sequence : List Coord := [.time, .agent, .addressee, .position]

theorem sequence_nodup : sequence.Nodup := by decide

/-- The operators of the sequence stacked over `χ`, the first innermost. -/
def stackOf (l : List Coord) (χ : Character (Context W E P T) (Context W E P T) α) :
    Character (Context W E P T) (Context W E P T) α :=
  l.foldl (fun χ k ↦ shiftyOp {k} χ) χ

/-- A complement projecting the lowest `n` operators of the sequence (128). -/
def stack (n : ℕ) : Character (Context W E P T) (Context W E P T) α →
    Character (Context W E P T) (Context W E P T) α :=
  stackOf (sequence.take n)

/-- The classes a complement projecting the lowest `n` operators shifts. -/
def shifted (n : ℕ) : Finset Coord := (sequence.take n).toFinset

theorem mem_shifted_iff {n : ℕ} {k : Coord} :
    k ∈ shifted n ↔ k ∈ sequence ∧ sequence.idxOf k < n := by
  rw [shifted, List.mem_toFinset]
  refine ⟨fun h ↦ ?_, fun ⟨h, h'⟩ ↦ (List.mem_take_iff_idxOf_lt h).2 h'⟩
  have hk := List.mem_of_mem_take h
  exact ⟨hk, (List.mem_take_iff_idxOf_lt hk).1 h⟩

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

/-- (G2): in a complement of any size, an indexical class shifts only if every class below it in
the sequence shifts as well. -/
theorem mem_shifted_of_lt {n : ℕ} {k k' : Coord} (hk : k ∈ shifted n) (hk' : k' ∈ sequence)
    (h : sequence.idxOf k' < sequence.idxOf k) : k' ∈ shifted n :=
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

/-- The classes shifted from the index, and so read de se, in a complement of size `n` with the
complementizer after the lowest `p` operators. -/
def deSe (n p : ℕ) : Finset Coord := shifted (min p n)

/-- The classes shifted from the attitude event in the same complement. -/
def eventShifted (n p : ℕ) : Finset Coord := shifted n \ shifted p

/-- A complement of size `n` with the complementizer after the lowest `p` operators (145)–(148):
the operators above the complementizer overwrite from the event, those below it from the index. -/
def complement (n p : ℕ) (R : Ev → Set (Context W E P T)) (ev : Ev → Context W E P T)
    (χ : Character (Context W E P T) (Context W E P T) Prop) :
    Ev → Character (Context W E P T) (Context W E P T) Prop :=
  eventOp ev (eventShifted n p) (comp R (shiftyOp (deSe n p) χ))

theorem complement_apply (n p : ℕ) (R : Ev → Set (Context W E P T)) (ev : Ev → Context W E P T)
    (χ : Character (Context W E P T) (Context W E P T) Prop) (e : Ev) (c i : Context W E P T) :
    complement n p R ev χ e c i ↔ ∀ i' ∈ R e,
      χ (overwrite (deSe n p) (overwrite (eventShifted n p) c (ev e)) i') i' :=
  Iff.rfl

/-- In a complement, an indexical of class `k` reads the centered index when its operator is below
the complementizer, the attitude event when it is above, and the utterance context when the
complement projects no operator for it: TP⟨author(i), addr(i), LOC(e)⟩ in Nez Perce (145). -/
theorem apply_complementContext {f : Context W E P T → α} {k : Coord} (hf : DependsOn f {k})
    (n p : ℕ) (c x i : Context W E P T) :
    f (overwrite (deSe n p) (overwrite (eventShifted n p) c x) i) =
      if k ∈ deSe n p then f i else if k ∈ eventShifted n p then f x else f c := by
  split_ifs with h₁ h₂
  · exact hf.apply_overwrite_of_subset (Finset.singleton_subset_iff.2 h₁) _ _
  · rw [hf.apply_overwrite_of_disjoint (Finset.disjoint_singleton_left.2 h₁),
      hf.apply_overwrite_of_subset (Finset.singleton_subset_iff.2 h₂)]
  · rw [hf.apply_overwrite_of_disjoint (Finset.disjoint_singleton_left.2 h₁),
      hf.apply_overwrite_of_disjoint (Finset.disjoint_singleton_left.2 h₂)]

/-- (G3): an indexical class must be read de se only if every class below it in the sequence must
be as well. -/
theorem mem_deSe_of_lt {n p : ℕ} {k k' : Coord} (hk : k ∈ deSe n p) (hk' : k' ∈ sequence)
    (h : sequence.idxOf k' < sequence.idxOf k) : k' ∈ deSe n p :=
  mem_shifted_of_lt hk hk' h

/-- The de se classes are shifted. -/
theorem deSe_subset (n p : ℕ) : deSe n p ⊆ shifted n := fun _ hk ↦
  mem_shifted_iff.2 ⟨(mem_shifted_iff.1 hk).1, (mem_shifted_iff.1 hk).2.trans_le (min_le_right p n)⟩

/-! ### Local Determination -/

/-- (83): in *Katie says that I think that I am here*, the medial clause's first person is the
author of the medial thought, so whatever operators the two complements carry, the lowest first
person refers as the medial one does: both shifted or neither (77). -/
theorem medial_eq_lowest (s₁ s₂ : Finset Coord) (c j₁ j₂ : Context W E P T)
    (hj₂ : j₂.agent = (overwrite s₁ c j₁).agent) :
    (overwrite s₂ (overwrite s₁ c j₁) j₂).agent = (overwrite s₁ c j₁).agent := by
  by_cases h : Coord.agent ∈ s₂ <;> simp [h, hj₂]

/-- (87): under an operator overwriting the author at the lowest complement's edge, the lowest first
person refers to the lowest reported author whatever the intermediate complement carries. -/
theorem lowest_of_agent_mem {s₂ : Finset Coord} (h : Coord.agent ∈ s₂) (s₁ : Finset Coord)
    (c j₁ j₂ : Context W E P T) : (overwrite s₂ (overwrite s₁ c j₁) j₂).agent = j₂.agent := by
  simp [h]

/-! ### Lexical bundling -/

/-- OP_PERS, the bundle of OP_AUTH and OP_ADDR (58), (172). -/
def opPers : Finset Coord := {.agent, .addressee}

/-- OP_ADV, the Korean bundle of OP_LOC and OP_TIME (§4.2.2). -/
def opAdv : Finset Coord := {.position, .time}

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

/-- (G2) for every complement built from sizes. -/
theorem mem_of_mem_ofSizes {ns : Finset ℕ} {s : Finset Coord} (hs : s ∈ ofSizes ns) {k k' : Coord}
    (hk : k ∈ s) (hk' : k' ∈ sequence) (h : sequence.idxOf k' < sequence.idxOf k) : k' ∈ s := by
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

/-- The coordinate sets the complements of the rows' verbs may overwrite. Nez Perce projects
OP_PERS (172) and optionally OP_LOC above it, and Zazaki the whole sequence or none of it (§3.1.3);
Uyghur projects OP_ADDR and OP_AUTH obligatorily (146), Slave *hadi* 'say' OP_AUTH alone, and
Dhaasanac the person shifters (148), whose optionality the book does not report; Korean 'say'
combines OP_PERS and OP_ADV freely and 'think' takes OP_ADV alone (§4.2.2), and Anderson English
takes OP_TIME alone (§4.1). -/
def options? : String → Option (Finset (Finset Coord))
  | "nezperce_say" | "nezperce_think" => some (ofSizes {0, 3, 4})
  | "zazaki_say" => some (ofSizes {0, 4})
  | "uyghur_say" => some (ofSizes {3})
  | "slave_say" => some (ofSizes {2})
  | "dhaasanac_say" => some (ofSizes {3})
  | "korean_say" => some (ofBundles {opPers, opAdv})
  | "korean_think" => some (ofBundles {opAdv})
  | "anderson_say" => some (ofSizes {0, 1})
  | _ => none

/-- The number of operators below the complementizer in the rows' verbs' complements: C above
OP_LOC in Zazaki (147) and Korean, between OP_LOC and OP_ADDR in Nez Perce (145), between OP_ADDR
and OP_AUTH in Uyghur (146), below OP_AUTH in Dhaasanac (148), and below OP_TIME in Anderson English
(167). (148) predates OP_TIME; Dhaasanac's C is placed above it here, which no row tests. -/
def cPosition? : String → Option ℕ
  | "nezperce_say" | "nezperce_think" => some 3
  | "zazaki_say" | "korean_say" | "korean_think" => some 4
  | "uyghur_say" => some 2
  | "dhaasanac_say" => some 1
  | "anderson_say" => some 0
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

/-- The coordinate sets a row's verb may overwrite, and the coordinates its indexicals read. -/
def verbCoords? (r : Datum) : Option (Finset (Finset Coord) × List Coord) :=
  ((r.feature? "verb").bind options?).bind fun e ↦ ((r.features "indexical").mapM coord?).map (e, ·)

/-- Every judged reading of the rows' indexicals is available, at worst marginal, exactly when a
complement the verb selects overwrites the coordinates of the indexicals the reading shifts and no
others: (G2) and Shift Together (72) in Nez Perce, Uyghur and Slave, and Korean's bundles. -/
theorem rows_shift :
    ∀ r ∈ Examples.all, ∀ p ∈ (verbCoords? r).toList, ∀ x ∈ r.readings,
      ∀ ps ∈ (shifted? x.1).toList,
        (.marginal ≤ x.2 ↔ ∃ s ∈ p.1, ∀ q ∈ p.2.zipIdx, (q.1 ∈ s ↔ q.2 ∈ ps)) := by
  decide +kernel

/-- A judged de se reading of the rows' shifted indexicals is available exactly when a complement
the verb selects shifts their coordinates. -/
theorem rows_deSe :
    ∀ r ∈ Examples.all, ∀ p ∈ (verbCoords? r).toList, ∀ x ∈ r.readings, x.1 = "de se" →
      (.marginal ≤ x.2 ↔ ∃ s ∈ p.1, ∀ k ∈ p.2, k ∈ s) := by
  decide +kernel

/-- (G3) in the rows: a judged non-de se reading of the rows' shifted indexicals is available
exactly when a complement the verb selects shifts their coordinates with operators above the
complementizer, `eventShifted n c = shifted n \ shifted c`. -/
theorem rows_nonDeSe :
    ∀ r ∈ Examples.all, ∀ p ∈ (verbCoords? r).toList,
      ∀ c ∈ ((r.feature? "verb").bind cPosition?).toList, ∀ x ∈ r.readings, x.1 = "non-de se" →
        (.marginal ≤ x.2 ↔ ∃ s ∈ p.1, ∀ k ∈ p.2, k ∈ s \ shifted c) := by
  decide +kernel

/-- (87): in the lowest of two reports, a reading of a first person is available exactly when
complements of the two verbs make it read the context at that depth (Local Determination), the
lowest complement overwriting the addressee to shift its second person. -/
theorem rows_double_report :
    ∀ r ∈ Examples.all, r.feature? "lowest_shift" = some "yes" →
      ∀ p ∈ (verbCoords? r).toList, ∀ e₂ ∈ ((r.feature? "lower_verb").bind options?).toList,
        ∀ x ∈ r.readings, ∀ d ∈ [("utterance context", 0), ("intermediate reported context", 1),
            ("lowest reported context", 2)], x.1 = d.1 →
          (.marginal ≤ x.2 ↔ ∃ s₁ ∈ p.1, ∃ s₂ ∈ e₂, .addressee ∈ s₂ ∧
            ∀ k ∈ p.2, AnandNevins2004.depth₂ s₁ s₂ k = d.2) := by
  decide +kernel

example : (Examples.all.filter fun r ↦ (verbCoords? r).isSome).length = 24 := by decide +kernel

end Deal2020
