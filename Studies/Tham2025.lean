module

public import Linglib.Core.SocialChoice.Rules
public import Linglib.Data.Examples.Tham2025

/-!
# Tham (2025): Multidimensionality and the Scalar Components of Physical Disturbance Predicates

This file formalizes [tham-2025]'s account of physical disturbance predicates, change-of-state
verbs such as *crack*, *dent* and *scratch* and their deverbal adjectives, whose root has a
count noun form naming an irregularity in an affected host ([karmo-1977]). The paper argues
that the predicates are associated with a gradable scale closed at both ends, against the
two-point scale of [rappaport-hovav-2014] and the partial, upper-open scale of
[rotstein-winter-2004]: the verb has durative uses and the adjective comparative ones,
(10)–(11), both take *completely* and *partially*, (15), (20)–(21), and both telic and atelic
uses of the verb entail the adjectival state, (14), (17). The adjective is multidimensional in
the sense of [sassoon-2013] and [solt-2018a]: *badly* evokes the quantity, quality or
positioning of the disturbances, (22)–(25), and respect phrases individuate the dimensions,
(28). The three scalar components have three sources (section 3.4): the lower bound is the
existence of a disturbance, so unmodified predication is objective, (26); the gradable interval
comes from the dimensions, so degree-modified predication admits faultless disagreement, (27);
and the upper bound is the spatial extent of the host, (33).

The adjective's measure function (47b) is the weighted extent of the disturbances relative to
the host's spatial extent, `degree`, with the weights the context's dimensions; the positive
form (46) compares it with a degree, `Pos`. A weighting positive on every dimension makes the
degree positive exactly when some disturbance has positive extent, `degree_pos_iff`, so
whether the host is cracked does not depend on the weighting, `degree_pos_iff_degree_pos`,
while the weightings that select single dimensions, the respect phrases `respect`, can rank two
hosts oppositely, `more_respect_and_more_respect`. A disturbance within the host's extent has a
degree at most one, `degree_le_one`, and the same disturbance on a smaller host has a higher
degree, `degree_lt_degree_of_lt`. The verb (48) describes an event whose final degree meets the
root's standard and exceeds the initial degree by a difference degree, `Event`, `Verb`: every
use of the verb entails the adjective at the standard, `Verb.pos_final`, and the verb modified
by a high difference degree entails the adjective modified by the same degree, `Verb.pos`, but
not conversely, since a pre-existing crack that grows a little leaves the windshield badly
cracked without its having cracked badly, `Event.pos_not_verb`.

## Implementation notes

The measure sums over an index type of dimensions, each with a nonnegative extent measure on
hosts, in the profile vocabulary of `SocialChoice`; the paper's comparative at a
weighting is the utilitarian rule on the extent profile when the hosts have the same spatial
extent, `more_iff_utilitarian`. A respect phrase is the weighting `Pi.single i 1`, so respect
phrases and quantification over respects are the paper's grammatical access to dimensions for
the adjective; the paper's claim that the verb allows only conceptual access, and its speculation
that the difference degree is the reason, are not formalized. The examples are the rows of
`Data.Examples.Tham2025`; the consultant counts of section 4.2 and the online survey of section
3.2.2 are recorded in their comments.

## References

* [tham-2025]
* [karmo-1977]
* [rappaport-hovav-2014]
* [rotstein-winter-2004]
* [sassoon-2013]
* [solt-2018a]
* [kennedy-levin-2008]
* [kennedy-mcnally-2005]
* [ruiz-faroldi-2022]
-/

@[expose] public section

namespace Tham2025

open SocialChoice Finset Matrix

/-! ### The adjective (section 5.2, (46)–(47)) -/

section Adjective

variable {ι α K : Type*} [Fintype ι] [Field K]

/-- The degree of disturbance of a host (47b) is the extent of its disturbances along each
dimension, weighted by the context, relative to its spatial extent. -/
def degree (k : ι → K) (v : Profile ι α K) (spatial : α → K) (x : α) : K :=
  k ⬝ᵥ v x / spatial x

/-- A respect phrase weights the single dimension it names. -/
def respect [DecidableEq ι] (i : ι) : ι → K := Pi.single i 1

variable {k : ι → K} {v : Profile ι α K} {spatial : α → K} {x y : α}

/-- *Completely* (20), (33) says that the disturbance exhausts the host's extent. -/
theorem degree_eq_one_iff (hs : spatial x ≠ 0) : degree k v spatial x = 1 ↔ k ⬝ᵥ v x = spatial x :=
  div_eq_one_iff_eq hs

theorem degree_respect [DecidableEq ι] {i : ι} :
    degree (respect i) v spatial x = v x i / spatial x := by
  rw [degree, respect, single_dotProduct, one_mul]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The positive form (46) holds when the host is disturbed to degree `d` or beyond. -/
def Pos (k : ι → K) (v : Profile ι α K) (spatial : α → K) (d : K) (x : α) : Prop :=
  d ≤ degree k v spatial x

/-- The comparative holds when `x` is more disturbed than `y`. -/
def More (k : ι → K) (v : Profile ι α K) (spatial : α → K) (x y : α) : Prop :=
  degree k v spatial y < degree k v spatial x

theorem degree_nonneg (hk : ∀ i, 0 ≤ k i) (hv : ∀ i, 0 ≤ v x i) (hs : 0 ≤ spatial x) :
    0 ≤ degree k v spatial x :=
  div_nonneg (sum_nonneg fun i _ ↦ mul_nonneg (hk i) (hv i)) hs

theorem degree_pos_iff (hk : ∀ i, 0 < k i) (hv : ∀ i, 0 ≤ v x i) (hs : 0 < spatial x) :
    0 < degree k v spatial x ↔ ∃ i, 0 < v x i := by
  rw [degree, div_pos_iff_of_pos_right hs, dotProduct,
    (sum_nonneg fun i _ ↦ mul_nonneg (hk i).le (hv i)).lt_iff_ne, ne_comm, ne_eq,
    sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_nonneg (hk i).le (hv i)]
  push Not
  exact exists_congr fun i ↦ by
    simp only [mem_univ, true_and, mul_ne_zero_iff_left (hk i).ne', (hv i).lt_iff_ne']

theorem degree_pos_iff_degree_pos {k' : ι → K} (hk : ∀ i, 0 < k i) (hk' : ∀ i, 0 < k' i)
    (hv : ∀ i, 0 ≤ v x i) (hs : 0 < spatial x) :
    0 < degree k v spatial x ↔ 0 < degree k' v spatial x := by
  rw [degree_pos_iff hk hv hs, degree_pos_iff hk' hv hs]

theorem degree_le_one (h : k ⬝ᵥ v x ≤ spatial x) (hs : 0 < spatial x) :
    degree k v spatial x ≤ 1 :=
  (div_le_one₀ hs).2 h

theorem degree_lt_degree_of_lt {spatial' : α → K} (h0 : 0 < k ⬝ᵥ v x) (hs : 0 < spatial' x)
    (h : spatial' x < spatial x) : degree k v spatial x < degree k v spatial' x :=
  div_lt_div_of_pos_left h0 hs h

theorem more_iff_utilitarian (hs : spatial x = spatial y) (hs0 : 0 < spatial x) :
    More k v spatial x y ↔ utilitarian k v x y ∧ ¬ utilitarian k v y x := by
  rw [More, degree, degree, ← hs, div_lt_div_iff_of_pos_right hs0, utilitarian, utilitarian,
    lt_iff_le_not_ge]

/-! ### Respect phrases (sections 3.2.2 and 4.2) -/

variable [DecidableEq ι] {i j : ι}

/-- In *more dented with respect to dent size* (28a), (42a), the comparative under a respect
phrase compares the named dimension alone. -/
theorem more_respect_iff (hs : spatial x = spatial y) (hs0 : 0 < spatial x) :
    More (respect i) v spatial x y ↔ v y i < v x i := by
  rw [More, degree_respect, degree_respect, ← hs, div_lt_div_iff_of_pos_right hs0]

/-- Degree-modified predication allows faultless disagreement (27), (28a), since two hosts can each
be more disturbed than the other with respect to some dimension. -/
theorem more_respect_and_more_respect (hs : spatial x = spatial y) (hs0 : 0 < spatial x)
    (hi : v y i < v x i) (hj : v x j < v y j) :
    More (respect i) v spatial x y ∧ More (respect j) v spatial y x :=
  ⟨(more_respect_iff hs hs0).2 hi, (more_respect_iff hs.symm (hs ▸ hs0)).2 hj⟩

end Adjective

/-! ### The verb (section 5.2, (48)) -/

section Verb

variable {σ K : Type*} [Field K] [LinearOrder K]

/-- A physical disturbance event (48) is a change between states whose final degree of
disturbance meets the root's standard and exceeds the initial degree. The initial degree may
already meet the standard, when the host bears an earlier disturbance. -/
structure Event (μ : σ → K) (std : K) where
  /-- The state at the start of the event. -/
  init : σ
  /-- The state at the end of the event. -/
  final : σ
  lt : μ init < μ final
  std_le : std ≤ μ final

variable {μ : σ → K} {std : K}

/-- The difference degree of an event is the degree of change it describes. -/
def Event.diff (e : Event μ std) : K := μ e.final - μ e.init

/-- The verb at a difference degree, its degree argument in (48). -/
def Verb (d : K) (e : Event μ std) : Prop := d ≤ e.diff

/-- *Cracked completely/slightly* entails *is cracked* (17a), since every event entails the
adjectival state at the root's standard, whatever its difference degree. -/
theorem Verb.pos_final {d : K} {e : Event μ std} (_ : Verb d e) : std ≤ μ e.final := e.std_le

theorem Event.pos_not_verb {d : K} (e : Event μ std) (hd : d ≤ μ e.final) (h : e.diff < d) :
    d ≤ μ e.final ∧ ¬ Verb d e :=
  ⟨hd, not_le.2 h⟩

variable [IsStrictOrderedRing K]

theorem Event.diff_pos (e : Event μ std) : 0 < e.diff := sub_pos.2 e.lt

/-- *Cracked badly* entails *badly cracked*, since the difference degree is at most the final
degree. -/
theorem Verb.pos {d : K} {e : Event μ std} (h : Verb d e) (h0 : 0 ≤ μ e.init) :
    d ≤ μ e.final :=
  h.trans (sub_le_self _ h0)

end Verb

end Tham2025
