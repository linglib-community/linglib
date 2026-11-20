module

public import Linglib.Phonology.Segmental.Sonority.Obstruent
public import Studies.Anttila1997
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Parker (2002): the sonority hierarchy

`Parker2002.Class` is the sixteen sonority classes: the four obstruent classes of
`Phonology.ObstruentClass` below twelve further classes in a chain. `Class.rankWith o` ranks them
with the obstruents ranked by `ObstruentClass.rank o`; it is injective unless `o = .eq`. The
order on `Class` is the one the rankings share, `a ≤ b ↔ ∀ o, rankWith o a ≤ rankWith o b`, a
partial order in which only the voiceless fricatives and the voiced stops are unordered, and
every strictly monotone ranking of the sixteen classes induces the order of some `rankWith o`
(`Class.le_iff_rankWith_le`).

`Class.toSonority` sends a class to its class in the hierarchy of obstruents, nasals, liquids,
glides and vowels. That hierarchy coarsens every `rankWith o` (`Class.coarsens_toSonority`), and
the classes it merges are contiguous on each.

The five vowel classes are ordered by height and peripherality, low above mid above high above
/ə/ above /ɨ/. `Class.nucleusEmbedding` embeds the nuclear sonority of Anttila's Finnish
grammar, which orders nuclei by height alone, as the low, mid and high vowels.

## Implementation notes

The source's table of the sixteen classes lists the voiced stops and the voiceless fricatives at
two ranks in either order, the voiced stops higher by default. `Class.rankWith` takes the order
as an argument instead of fixing the default, and `Class` carries the partial order instead of a
linear one, so that a statement about `≤` holds on both rankings. The acoustic measurements and
the regression of sonority on intensity have no counterpart here.

## References

* [parker-2002]
* [anttila-1997]
-/

@[expose] public section

namespace Parker2002

open Phonology ObstruentClass

/-- Table 5.28: the sonority classes. -/
inductive Class where
  /-- The obstruents of a class. -/
  | obstruent (o : ObstruentClass)
  /-- /h/. -/
  | h
  /-- The nasals. -/
  | nasal
  /-- The trills. -/
  | trill
  /-- The flaps. -/
  | flap
  /-- The laterals. -/
  | lateral
  /-- English /r/. -/
  | rhotic
  /-- The glides. -/
  | glide
  /-- /ɨ/. -/
  | highCentral
  /-- /ə/. -/
  | schwa
  /-- The high vowels other than /ɨ/. -/
  | high
  /-- The mid vowels other than /ə/. -/
  | mid
  /-- The low vowels. -/
  | low
  deriving DecidableEq, Repr, Fintype

namespace Class

/-- Table 5.28: the rank of a class, with the obstruents ranked by `ObstruentClass.rank o`. The table as
printed is `rankWith .lt`, `rankWith .gt` exchanges its second and third ranks, and `rankWith .eq`
merges them. -/
def rankWith (o : Ordering) : Class → ℕ
  | obstruent x => ObstruentClass.rank o x
  | h => 5 | nasal => 6 | trill => 7 | flap => 8 | lateral => 9 | rhotic => 10 | glide => 11
  | highCentral => 12 | schwa => 13 | high => 14 | mid => 15 | low => 16

theorem rankWith_injective {o : Ordering} (ho : o ≠ .eq) : Function.Injective (rankWith o) := by
  revert o
  decide +kernel

/-- The order the rankings of Table 5.28 share, in which only the voiceless fricatives and the
voiced stops are unordered (p. 241). -/
instance : PartialOrder Class :=
  PartialOrder.lift (fun c ↦ (rankWith .lt c, rankWith .gt c)) fun _ _ h ↦
    rankWith_injective (by decide) (congrArg Prod.fst h)

instance : DecidableLE Class := fun a b ↦
  inferInstanceAs (Decidable (rankWith .lt a ≤ rankWith .lt b ∧ rankWith .gt a ≤ rankWith .gt b))

instance : DecidableLT Class := decidableLTOfDecidableLE

theorem le_iff_forall_rankWith_le {a b : Class} : a ≤ b ↔ ∀ o, rankWith o a ≤ rankWith o b := by
  revert a b
  decide +kernel

@[simp] theorem obstruent_le_obstruent {x y : ObstruentClass} : obstruent x ≤ obstruent y ↔ x ≤ y := by
  revert x y
  decide

theorem strictMono_obstruent : StrictMono obstruent := by
  simp only [StrictMono]
  decide

theorem strictMono_rankWith (o : Ordering) : StrictMono (rankWith o) := by
  revert o
  simp only [StrictMono]
  decide +kernel

/-- A ranking of the classes strictly monotone for the shared order induces the order of the
ranking of Table 5.28 that compares the voiceless fricatives with the voiced stops as it does
(p. 241). -/
theorem le_iff_rankWith_le {α : Type*} [LinearOrder α] {r : Class → α} (hr : StrictMono r)
    (x y : Class) :
    r x ≤ r y ↔
      rankWith (compare (r (obstruent voicelessFricative)) (r (obstruent voicedStop))) x ≤
        rankWith (compare (r (obstruent voicelessFricative)) (r (obstruent voicedStop))) y := by
  have key : ∀ x y : Class, (∃ a b, x = obstruent a ∧ y = obstruent b) ∨ x ≤ y ∨ y ≤ x := by
    decide +kernel
  obtain ⟨a, b, rfl, rfl⟩ | h | h := key x y
  · exact le_iff_rank_le (hr.comp strictMono_obstruent) a b
  · exact iff_of_true (hr.monotone h) ((strictMono_rankWith _).monotone h)
  · rcases h.eq_or_lt with rfl | h
    · simp
    · exact iff_of_false (hr h).not_ge (strictMono_rankWith _ h).not_ge

/-- The class of the hierarchy of obstruents, nasals, liquids, glides and vowels that a class
falls in, with /h/ among the obstruents. -/
def toSonority : Class → Sonority
  | obstruent _ | h => .obstruent
  | nasal => .nasal
  | trill | flap | lateral | rhotic => .liquid
  | glide => .glide
  | highCentral | schwa | high | mid | low => .vowel

/-- The hierarchy of obstruents, nasals, liquids, glides and vowels coarsens Table 5.28, however
the voiceless fricatives and the voiced stops are ranked (p. 241). -/
theorem coarsens_toSonority (o : Ordering) : Sonority.Coarsens toSonority (rankWith o) := by
  revert o
  unfold Sonority.Coarsens
  decide +kernel

theorem monotone_toSonority : Monotone toSonority := fun a b h ↦ coarsens_toSonority .lt a b h.1

/-- `toSonority` as an order homomorphism. -/
@[simps]
def toSonorityHom : Class →o Sonority := ⟨toSonority, monotone_toSonority⟩

-- p. 240: a language conflates the scale by collapsing adjacent ranks
theorem contiguous_toSonority (o : Ordering) (c : Sonority) :
    Sonority.Contiguous (rankWith o) (toSonority ⁻¹' {c}) :=
  .of_coarsens (coarsens_toSonority o) ⟨{c}, Set.ordConnected_singleton, rfl⟩

/-! ### Vowels -/

/-- (1.9): the nuclear sonority of [anttila-1997] among the classes, as the low, mid and high
vowels. -/
def ofNucleus : Anttila1997.Sonority → Class
  | .a => low
  | .o => mid
  | .i => high

theorem strictMono_ofNucleus : StrictMono ofNucleus := by
  simp only [StrictMono]
  decide

/-- `ofNucleus` as an order embedding. -/
def nucleusEmbedding : Anttila1997.Sonority ↪o Class :=
  .ofStrictMono ofNucleus strictMono_ofNucleus

@[simp] theorem coe_nucleusEmbedding : ⇑nucleusEmbedding = ofNucleus := rfl

@[simp] theorem toSonority_ofNucleus (s : Anttila1997.Sonority) :
    toSonority (ofNucleus s) = .vowel := by
  cases s <;> rfl

end Class

end Parker2002
