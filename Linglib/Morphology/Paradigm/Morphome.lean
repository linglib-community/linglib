module

public import Linglib.Core.Data.Setoid.Basic
public import Linglib.Morphology.Paradigm.Basic
public import Mathlib.Order.Setoid.Partition
public import Mathlib.Data.Set.Subsingleton

/-!
# Morphomes: syncretism classes with no natural characterization

A realization map `p : Cell → F` assigns a form to each paradigm cell. Its
**syncretism** relation — cells receiving the same form — is the kernel setoid
`Setoid.ker p`, and the syncretism classes are its equivalence classes. A
**morphome** ([aronoff-1994] coined the term) is a systematic syncretism that
does not define a natural class; [herce-2023] adopts the working definition "a
systematic morphological syncretism which does not define a (syntactically or
semantically) natural class" (Trommer 2016, quoted approvingly).

Naturalness is a **parameter** `Natural : Set Cell → Prop`, not stipulated
here. [herce-2023] operationalizes a natural class as one "coextensive with
a value (e.g. SG) or conjunction of values (e.g. 1SG)" and treats
naturalness as *gradient*, so `Natural` is best read as a threshold slice of
that scale; the value-or-conjunction predicate is its canonical
instantiation, `IsValueConjunction`: the cells agreeing with some cell on
some of the paradigm's features, each feature given as the partition of
cells it induces.
Systematicity — recurrence of the pattern under more than one exponent or
allomorph — is a separate criterion the consumer establishes.

Two limitations, per [baerman-2015]'s three-way analysis space for
syncretism (morphosyntactic identity / underspecification / morphological
stipulation, p. 146): an **elsewhere** form's fiber is typically also
nontrivial and non-natural (one specified cell, the default covers the
unnatural rest — Skou, p. 145), so `IsMorphome` is necessary but not
sufficient for stipulation-hood; distinguishing the two needs opposition
structure or the systematicity criterion above. And **directional**
syncretism (a cell wearing another cell's form "in place of the expected"
one, p. 142) is invisible to the symmetric kernel.

The vocabulary here is deliberately just "morphome": [herce-2023] rejects
Round's rhizomorphome ~ metamorphome ~ meromorphome subdivision as needless
jargon, and "metasyncretism" does not appear in the book.

## Main declarations

* `Morphology.syncretismClass` — the class (fiber) of a given cell
* `Morphology.formCells` — the cells a form realizes, the `Finset` face of the class
* `Morphology.formCellsOf` — the cells a table with defective or overabundant cells gives a form
* `Morphology.IsMorphome` — a nontrivial syncretism class failing `Natural`
* `Morphology.IsValueConjunction` — the cells agreeing with a witness on a set of features,
  [herce-2023]'s natural class
-/

@[expose] public section

namespace Morphology

variable {Cell F : Type*}

/-- The syncretism class of a cell `a`: every cell realized as `a` is. -/
def syncretismClass (p : Cell → F) (a : Cell) : Set Cell := {x | p x = p a}

theorem syncretismClass_mem_classes (p : Cell → F) (a : Cell) :
    syncretismClass p a ∈ (Setoid.ker p).classes :=
  Setoid.mem_classes (Setoid.ker p) a

/-- The cells `p` realizes as the form `f`: the syncretism class of any cell realized as `f`,
as a `Finset`. -/
def formCells [Fintype Cell] [DecidableEq F] (p : Cell → F) (f : F) : Finset Cell :=
  Finset.univ.filter (p · = f)

@[simp] theorem mem_formCells [Fintype Cell] [DecidableEq F] {p : Cell → F} {f : F} {c : Cell} :
    c ∈ formCells p f ↔ p c = f := by
  simp [formCells]

/-- The cells a table `p` gives the form `f`, where a cell may have no form or several: the
`Finset` face of a defective or overabundant paradigm, and of a segmented realization at one of
its exponents. -/
def formCellsOf [Fintype Cell] [DecidableEq F] (p : Cell → Finset F) (f : F) : Finset Cell :=
  Finset.univ.filter (f ∈ p ·)

@[simp] theorem mem_formCellsOf [Fintype Cell] [DecidableEq F] {p : Cell → Finset F} {f : F}
    {c : Cell} : c ∈ formCellsOf p f ↔ f ∈ p c := by
  simp [formCellsOf]

theorem coe_formCells [Fintype Cell] [DecidableEq F] (p : Cell → F) (a : Cell) :
    (formCells p (p a) : Set Cell) = syncretismClass p a := by
  ext c; simp [syncretismClass]

/-- A **morphome** ([herce-2023]): a syncretism class of `p` that groups
more than one cell (`Set.Nontrivial`) yet is not a `Natural` class — a
grouping visible only in the realization, with no phonological, syntactic,
or semantic characterization ([aronoff-1994]'s "morphology by itself").
`Natural` is a parameter (see the module docstring). -/
def IsMorphome (p : Cell → F) (Natural : Set Cell → Prop) (c : Set Cell) : Prop :=
  c ∈ (Setoid.ker p).classes ∧ c.Nontrivial ∧ ¬ Natural c

/-- The syncretism class of `a` is a morphome once it is nontrivial and
unnatural — the shape a concrete paradigm instantiates. -/
theorem isMorphome_syncretismClass (p : Cell → F) (Natural : Set Cell → Prop)
    (a : Cell) (hnt : (syncretismClass p a).Nontrivial)
    (hnat : ¬ Natural (syncretismClass p a)) :
    IsMorphome p Natural (syncretismClass p a) :=
  ⟨syncretismClass_mem_classes p a, hnt, hnat⟩

/-- The `Finset` face of `isMorphome_syncretismClass`: the cells a form realizes are a
morphome once there are at least two of them and they are not a natural class. -/
theorem isMorphome_of_formCells [Fintype Cell] [DecidableEq F] (p : Cell → F) (a : Cell)
    (Natural : Set Cell → Prop) {X : Finset Cell} (hX : formCells p (p a) = X)
    (hnt : 1 < X.card) (hnat : ¬ Natural ↑X) : IsMorphome p Natural ↑X := by
  have hX' : (↑X : Set Cell) = syncretismClass p a := by rw [← hX, coe_formCells]
  rw [hX']
  exact isMorphome_syncretismClass p Natural a
    (hX' ▸ Finset.nontrivial_coe.mpr (Finset.one_lt_card_iff_nontrivial.mp hnt)) (hX' ▸ hnat)

/-! ### Natural classes as value conjunctions

[herce-2023] takes a natural class to be one "coextensive with a value or conjunction of
values". A paradigm's features are the partitions of its cells they induce, the kernels of
the feature projections; a value conjunction is then the set of cells agreeing with some cell
on some of the features. -/

variable {ι : Type*}

/-- A set of cells is a **value conjunction** for the features `feats` when it consists of
the cells agreeing with some cell on some of the features. -/
def IsValueConjunction (feats : ι → Setoid Cell) (X : Set Cell) : Prop :=
  ∃ (S : Finset ι) (c₀ : Cell), X = {c | ∀ i ∈ S, feats i c c₀}

/-- On a finite paradigm, being a value conjunction is a finite search over the features and
the witness cell. -/
theorem isValueConjunction_coe_iff [Fintype Cell] [DecidableEq Cell] (feats : ι → Setoid Cell)
    [∀ i, DecidableRel (feats i)] (X : Finset Cell) :
    IsValueConjunction feats ↑X ↔
      ∃ (S : Finset ι) (c₀ : Cell), Finset.univ.filter (fun c ↦ ∀ i ∈ S, feats i c c₀) = X := by
  simp only [IsValueConjunction, ← Finset.coe_inj, Finset.coe_filter, Finset.mem_univ, true_and,
    eq_comm]

end Morphology
