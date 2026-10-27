module

public import Linglib.Core.Data.Fin.VecNotation
public import Linglib.Core.ModelTheory.Atom
public import Linglib.Semantics.Dynamic.DRS.Realizers
public import Studies.Cooper2023

/-!
# Chatzikyriakidis, Cooper, Gregoromichelaki and Sutton (2025): Types and the Structure of Meaning

Ranta models an agent's beliefs as a context, a sequence of hypotheses about variables, and Cooper
recasts the context as a record type whose labels play the role of the variables. An agent believes
a type when its belief type is a subtype of some relabelling of it, so the labels of a complement
make no difference to the truth of a belief report. They make a difference to anaphora. In Geach's
*Hob thinks a witch has blighted Bob's mare, and Nob wonders whether she (the same witch) killed
Cob's sow*, the two belief contexts overlap in the label of the witch, so that Nob's question is
about Hob's witch although no witch need exist. Ranta separates the actual beliefs, the hypotheses
in an agent's context, from those that follow from it; on record types, what an agent believes in
every modal system is exactly its actual beliefs up to relabelling. The datum is
`Data/Examples/ChatzikyriakidisEtAl2025.json`.

## Implementation notes

* A field `ℓ : P(ℓ₁, …, ℓₙ)` is the atom `P(ℓ, ℓ₁, …, ℓₙ)`, its witness first, and a record type
  is a set of such atoms. A possibility is a structure for the predicates, every record type occurs
  in every possibility, and labels are flat, so a path such as `idᵢ.x` is one label.
* A relabelling is a permutation of the labels, extending a one-one relabelling of a record type's
  finitely many labels, so the relabellings of a record type are its orbit.
* The free model behind the actual-belief theorems is the structure a record type presents on its
  labels.
* The alignment of §2.3.2, and the alignment of discourse referents the Element compares it with
  in §2.3.3, is gluing of basic DRSs along a cover of contexts in the sense of Abramsky and
  Sadrzadeh.

## TODO

* Manifest fields (31), and the point of view by which a Roman reports Alexander's belief about
  Zeus with the name *Jupiter*.
* Nested record types, whose relabellings preserve the prefix order of paths, so that a belief in
  some boy who runs, (21), stays apart from a belief in the type of boys who run, (23).
* Section 3 of the Element, on polysemy, copredication and counting.

## References

* [chatzikyriakidis-etal-2025]
* [ranta-1994]
* [cooper-2023]
* [geach-1967]
* [abramsky-sadrzadeh-2014]
-/

@[expose] public section

namespace ChatzikyriakidisEtAl2025

open Cooper2023 FirstOrder Language MulAction Pointwise

/-! ### Record types over a modal system -/

section RecType

variable {L : Language.{0, 0}} {M α E : Type}

/-- The modal system of record types over a family of structures, one for each possibility. A
record type occurs in every possibility, and a record witnesses it there when it realizes each of
its fields. -/
def recTypes (S : M → L.Structure E) : ModalSystem M (Set (L.Atom α)) (α → E) := fun p ↦
  letI := S p
  { occurs _ := True
    witnesses T r := r ∈ Atom.realizers E T
    occurs_of_witnesses _ _ _ := trivial }

variable {S : M → L.Structure E} {T T₁ T₂ B : Set (L.Atom α)} {p : M} {r : α → E}

theorem mem_extension_recTypes :
    r ∈ (recTypes S).extension T p ↔ letI := S p; ∀ a ∈ T, a.Realize r :=
  .rfl

theorem extension_recTypes_union : (recTypes S).extension (T₁ ∪ T₂) p =
    (recTypes S).extension T₁ p ∩ (recTypes S).extension T₂ p :=
  letI := S p; Atom.realizers_union T₁ T₂

theorem mem_extension_recTypes_smul (σ : Equiv.Perm α) :
    r ∈ (recTypes S).extension (σ • T) p ↔ r ∘ σ ∈ (recTypes S).extension T p :=
  letI := S p; Atom.mem_realizers_smul

theorem subtypeR_recTypes_of_subset (h : T₂ ⊆ T₁) : (recTypes S).SubtypeR T₁ T₂ :=
  fun p ↦ letI := S p; Atom.realizers_anti h

theorem subtypeRelabel_of_smul_subset (σ : Equiv.Perm α) (h : σ • T ⊆ B) :
    (recTypes S).SubtypeRelabel (orbitRel (Equiv.Perm α) _) B T :=
  ⟨σ • T, ⟨σ⁻¹, inv_smul_smul σ T⟩, (subtypeR_recTypes_of_subset h).subtypeI⟩

theorem subtypeRelabel_smul (σ : Equiv.Perm α) :
    (recTypes S).SubtypeRelabel (orbitRel (Equiv.Perm α) _) B (σ • T) ↔
      (recTypes S).SubtypeRelabel (orbitRel (Equiv.Perm α) _) B T :=
  ModalSystem.subtypeRelabel_congr ⟨σ, rfl⟩

end RecType

/-! ### Actual beliefs (§2.3.1)

A record type presents a structure on its labels, in which a map of labels is a witness of
another record type exactly when it carries its fields into those of the first. So the beliefs
that hold in every modal system are the ones the belief type contains, up to relabelling. -/

section ActualBelief

variable {L : Language.{0, 0}} [L.IsRelational] {α : Type} {T T₁ T₂ B : Set (L.Atom α)}

theorem forall_subtypeR_recTypes_iff :
    (∀ (M E : Type) (S : M → L.Structure E), (recTypes S).SubtypeR T₁ T₂) ↔ T₂ ⊆ T₁ := by
  refine ⟨fun h ↦ ?_, fun h _ _ _ ↦ subtypeR_recTypes_of_subset h⟩
  simpa using Atom.forall_realizers_subset_preimage_iff (T := T₂) (B := T₁) (f := id).1
    fun E inst ↦ h Unit E (fun _ ↦ inst) ()

/-- A belief type believes a type in every modal system exactly when it contains the fields of some
relabelling of it, as an actual belief. -/
theorem forall_subtypeRelabel_recTypes_iff :
    (∀ (M E : Type) (S : M → L.Structure E),
      (recTypes S).SubtypeRelabel (orbitRel (Equiv.Perm α) _) B T) ↔
      ∃ σ : Equiv.Perm α, σ • T ⊆ B := by
  refine ⟨fun h ↦ ?_, fun ⟨σ, h⟩ _ _ _ ↦ subtypeRelabel_of_smul_subset σ h⟩
  obtain ⟨_, ⟨σ, rfl⟩, hs⟩ := h Unit (Atom.Canonical B) fun _ ↦ inferInstance
  refine ⟨σ⁻¹, ?_⟩
  rw [inv_smul_smul]
  simpa using Atom.Canonical.of_comp_mem_realizers_iff (f := id).1 <|
    hs () trivial trivial (Atom.Canonical.of_mem_realizers B)

end ActualBelief

/-! ### *Kim believes that some woman is a conductor*, (32)–(35) -/

namespace Kim

/-- The predicates of (32)–(35), each taking its witness as first argument. -/
inductive Rel : ℕ → Type
  | ind : Rel 1
  | woman : Rel 2
  | conductor : Rel 2

/-- The language of the predicates of (32)–(35). -/
abbrev lang : Language := ⟨fun _ ↦ Empty, Rel⟩

instance : lang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- The labels of (32) and (34). The path `idᵢ.x` of (32) is the label `«idᵢ.x»`. -/
inductive Label | x | c | e | «idᵢ.x» | «idᵢ.e» | «idⱼ.e»
  deriving DecidableEq

/-- The fields of Kim's belief type (32). -/
def belief : Set (lang.Atom Label) :=
  {⟨Rel.ind, ![.«idᵢ.x»]⟩, ⟨Rel.woman, ![.«idᵢ.e», .«idᵢ.x»]⟩,
    ⟨Rel.conductor, ![.«idⱼ.e», .«idᵢ.x»]⟩}

/-- The complement (34) of the report. -/
def complement : Set (lang.Atom Label) :=
  {⟨Rel.ind, ![.x]⟩, ⟨Rel.woman, ![.c, .x]⟩, ⟨Rel.conductor, ![.e, .x]⟩}

/-- The relabelling (35a). -/
def relabelling : Equiv.Perm Label :=
  Equiv.swap .x .«idᵢ.x» * Equiv.swap .c .«idᵢ.e» * Equiv.swap .e .«idⱼ.e»

-- (34), (35a), (32), (35b)
theorem relabelling_smul_complement : relabelling • complement = belief := by
  simp [relabelling, complement, belief, Set.smul_set_insert, Atom.smul_def, Atom.map,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, Equiv.swap_apply_def]

/-- Whatever its labelling, (34) is believed by any belief type with the fields of (32), in every
modal system. -/
theorem believes {M E : Type} (S : M → lang.Structure E) {B : Set (lang.Atom Label)}
    (hB : belief ⊆ B) (τ : Equiv.Perm Label) :
    (recTypes S).SubtypeRelabel (orbitRel (Equiv.Perm Label) _) B (τ • complement) :=
  (subtypeRelabel_smul τ).2 <|
    subtypeRelabel_of_smul_subset relabelling (relabelling_smul_complement ▸ hB)

end Kim

/-! ### Intentional identity

Hob believes that a witch blighted Bob's mare, and Nob, who believes only that there is a witch,
wonders whether she killed Cob's sow. In the actual possibility there are no witches; in the other,
one witch blighted the mare and another killed the sow. -/

namespace HobNob

/-- The predicates of the Hob–Nob sentence, each taking its witness as first argument. -/
inductive Rel : ℕ → Type
  | ind : Rel 1
  | witch : Rel 2
  | blightedBobsMare : Rel 2
  | killedCobsSow : Rel 2
  deriving DecidableEq

/-- The language of the predicates of the Hob–Nob sentence. -/
abbrev lang : Language := ⟨fun _ ↦ Empty, Rel⟩

/-- The witch `x`, her being one `c`, the blighting `b` and the killing `k`, and another label
`y`. -/
inductive Label | x | y | c | b | k
  deriving DecidableEq

/-- The context Hob and Nob share, that there is a witch. -/
def witch : Set (lang.Atom Label) := {⟨Rel.ind, ![.x]⟩, ⟨Rel.witch, ![.c, .x]⟩}

/-- Hob's belief that a witch blighted Bob's mare. -/
def hob : Set (lang.Atom Label) := insert ⟨Rel.blightedBobsMare, ![.b, .x]⟩ witch

/-- The content of Nob's question, that she killed Cob's sow, with *she* the witch of the shared
context. -/
def nob : Set (lang.Atom Label) := insert ⟨Rel.killedCobsSow, ![.k, .x]⟩ witch

inductive Possib | actual | twoWitches
  deriving DecidableEq

/-- Two women and a situation. -/
inductive Obj | w₁ | w₂ | s
  deriving DecidableEq

/-- The ptypes that hold in each possibility. Both women are individuals in both, and in
`twoWitches` both are witches, `w₁` blighted Bob's mare and `w₂` killed Cob's sow, in the situation
`s`. -/
def holds (p : Possib) : ∀ {n}, Rel n → (Fin n → Obj) → Prop
  | _, .ind, xs => xs 0 ≠ .s
  | _, .witch, xs => p = .twoWitches ∧ (xs 1 = .w₁ ∨ xs 1 = .w₂) ∧ xs 0 = .s
  | _, .blightedBobsMare, xs => p = .twoWitches ∧ xs 1 = .w₁ ∧ xs 0 = .s
  | _, .killedCobsSow, xs => p = .twoWitches ∧ xs 1 = .w₂ ∧ xs 0 = .s

/-- The possibilities as structures. -/
abbrev system (p : Possib) : lang.Structure Obj where
  RelMap := holds p

@[simp] theorem relMap_system {p : Possib} {n : ℕ} (R : Rel n) (xs : Fin n → Obj) :
    @Structure.RelMap lang Obj (system p) n R xs ↔ holds p R xs :=
  .rfl

/-- No witch exists. -/
theorem extension_witch_actual : (recTypes system).extension witch .actual = ∅ := by
  ext r
  simp [mem_extension_recTypes, Atom.Realize, witch, holds]

/-- Hob believes that there is a witch. -/
theorem believes_witch :
    (recTypes system).SubtypeRelabel (orbitRel (Equiv.Perm Label) _) hob witch :=
  subtypeRelabel_of_smul_subset 1 (by simp [hob])

theorem not_believes_blighted :
    ¬ (recTypes system).SubtypeRelabel (orbitRel (Equiv.Perm Label) _) witch hob := by
  rintro ⟨T, ⟨σ, hσ : σ • T = hob⟩, h⟩
  let r : Label → Obj := fun ℓ ↦ if ℓ = .c then .s else .w₂
  have hr : r ∈ (recTypes system).extension T .twoWitches :=
    h .twoWitches trivial trivial <| by simp [mem_extension_recTypes, Atom.Realize, witch, holds, r]
  rw [← inv_smul_smul σ T, hσ, mem_extension_recTypes_smul, mem_extension_recTypes] at hr
  have := hr _ (Set.mem_insert _ _)
  simp [Atom.Realize, holds, r] at this
  grind

/-! #### Aligning the two contexts

Hob's belief context and the content of Nob's question each have their own referents, Nob's witch
being `y`. Aligning them on the witch is a cover of the discourse that sends both witches to one
referent, and gluing along it gives the merge of their record types; a cover that keeps the
witches apart gives the merge with Nob's witch relabelled. -/

open DRT

/-- `lit A x̄` is the positive literal `A(x̄)` over a context. -/
def lit {γ : Context lang Label} {n : ℕ} (r : Rel n) (args : Fin n → Label)
    (hr : ⟨n, r⟩ ∈ γ.vocab := by decide +kernel) (h : ∀ i, args i ∈ γ.vars := by decide +kernel) :
    Literal γ :=
  ⟨⟨⟨n, r⟩, hr⟩, fun i ↦ ⟨args i, h i⟩, true⟩

@[simp] theorem atom_lit {γ : Context lang Label} {n : ℕ} (r : Rel n) (args : Fin n → Label)
    (hr : ⟨n, r⟩ ∈ γ.vocab) (h : ∀ i, args i ∈ γ.vars) : (lit r args hr h).atom = ⟨r, args⟩ :=
  rfl

/-- `hom f` is the context morphism acting as `f` on referents. -/
def hom {γ γ' : Context lang Label} (f : Label → Label)
    (hf : ∀ t ∈ γ.vars, f t ∈ γ'.vars := by decide +kernel)
    (hL : γ.vocab ⊆ γ'.vocab := by decide +kernel) : γ ⟶ γ' :=
  ⟨hL, fun t ↦ ⟨f t, hf t t.2⟩⟩

/-- Hob's belief context, with the witch `x`. -/
abbrev hobCtx : Context lang Label :=
  ⟨{⟨1, .ind⟩, ⟨2, .witch⟩, ⟨2, .blightedBobsMare⟩}, {.x, .c, .b}⟩

/-- The context of Nob's question, with the witch `y`. -/
abbrev nobCtx : Context lang Label :=
  ⟨{⟨1, .ind⟩, ⟨2, .witch⟩, ⟨2, .killedCobsSow⟩}, {.y, .c, .k}⟩

/-- Hob's belief over Hob's context, and the content of Nob's question over Nob's. -/
def sections : ∀ i, Theory (![hobCtx, nobCtx] i)
  | 0 => ⟨{lit .ind ![.x], lit .witch ![.c, .x], lit .blightedBobsMare ![.b, .x]},
      by decide +kernel⟩
  | 1 => ⟨{lit .ind ![.y], lit .witch ![.c, .y], lit .killedCobsSow ![.k, .y]}, by decide +kernel⟩

/-- The vocabulary of the discourse. -/
abbrev vocab : Finset (Σ n, lang.Relations n) :=
  {⟨1, .ind⟩, ⟨2, .witch⟩, ⟨2, .blightedBobsMare⟩, ⟨2, .killedCobsSow⟩}

/-- The discourse with one witch. -/
abbrev sameCtx : Context lang Label := ⟨vocab, {.x, .c, .b, .k}⟩

/-- The discourse with two witches. -/
abbrev apartCtx : Context lang Label := ⟨vocab, {.x, .y, .c, .b, .k}⟩

/-- The cover of the discourse that sends Nob's witch to Hob's. -/
def sameCover : Cover sameCtx (Fin 2) where
  part := ![hobCtx, nobCtx]
  map
    | 0 => hom id
    | 1 => hom fun | .y => .x | t => t
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The cover of the discourse that keeps the witches apart. -/
def apartCover : Cover apartCtx (Fin 2) where
  part := ![hobCtx, nobCtx]
  map
    | 0 => hom id
    | 1 => hom id
  exists_map_eq := by decide +kernel
  exists_mem_vocab := by decide +kernel

/-- The gluing of the two contexts along the aligning cover. -/
def sameGlue : Theory sameCtx :=
  ⟨sameCover.pushforward sections, by decide +kernel⟩

/-- The gluing of the two contexts along the cover that keeps the witches apart. -/
def apartGlue : Theory apartCtx :=
  ⟨apartCover.pushforward sections, by decide +kernel⟩

theorem isGluing_sameGlue : sameCover.IsGluing (presheaf lang Label) sections sameGlue := by
  decide +kernel

theorem isGluing_apartGlue : apartCover.IsGluing (presheaf lang Label) sections apartGlue := by
  decide +kernel

/-- Gluing along the aligning cover merges Hob's belief and the content of Nob's question as
record types. -/
theorem atom_image_sameGlue :
    Literal.atom '' (sameGlue.lits : Set (Literal sameCtx)) = hob ∪ nob := by
  have : sameGlue.lits = {lit .ind ![.x], lit .witch ![.c, .x], lit .blightedBobsMare ![.b, .x],
      lit .killedCobsSow ![.k, .x]} := by decide +kernel
  rw [this]
  ext a
  simp [hob, nob, witch]
  tauto

theorem atom_image_apartGlue :
    Literal.atom '' (apartGlue.lits : Set (Literal apartCtx)) =
      hob ∪ Equiv.swap Label.x .y • nob := by
  have : apartGlue.lits = {lit .ind ![.x], lit .witch ![.c, .x], lit .blightedBobsMare ![.b, .x],
      lit .ind ![.y], lit .witch ![.c, .y], lit .killedCobsSow ![.k, .y]} := by decide +kernel
  rw [this]
  ext a
  simp [hob, nob, witch, Set.smul_set_insert, Atom.smul_def, Atom.map, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, Equiv.swap_apply_def]
  tauto

/-- *She (the same witch)*. Aligned on the witch, Hob's belief and the content of Nob's question
are not both true where different witches blighted the mare and killed the sow, since their
witnesses are the compatible pairs of local witnesses and compatibility gives both one witch. -/
theorem same_witch : (recTypes system).extension (hob ∪ nob) .twoWitches = ∅ := by
  let _ := system .twoWitches
  refine Set.eq_empty_of_forall_notMem fun r hr ↦ ?_
  rw [mem_extension_recTypes, ← Atom.mem_realizers, ← atom_image_sameGlue,
    ← Theory.comp_val_mem_realizers_iff (by decide +kernel)] at hr
  obtain ⟨g, hg⟩ := sameCover.realizersEquiv (M := Obj) (x := sections) rfl ⟨_, hr⟩
  have h₀ := (g 0).2 (lit .blightedBobsMare ![.b, .x]) (by decide +kernel)
  have h₁ := (g 1).2 (lit .killedCobsSow ![.k, .y]) (by decide +kernel)
  have h := hg 0 1 ⟨.x, by decide⟩ ⟨.y, by decide⟩ rfl
  simp [Literal.Holds, lit, holds] at h₀ h₁
  simp_all

/-- Keeping the witches apart, which leaves Nob's beliefs as they are, makes Hob's belief and the
content of Nob's question true together. -/
theorem other_witch :
    ((recTypes system).extension (hob ∪ Equiv.swap Label.x .y • nob) .twoWitches).Nonempty := by
  let _ := system .twoWitches
  refine ⟨fun | .x => .w₁ | .y => .w₂ | _ => .s, ?_⟩
  rw [mem_extension_recTypes, ← Atom.mem_realizers, ← atom_image_apartGlue,
    ← Theory.comp_val_mem_realizers_iff (by decide +kernel), apartCover.mem_realizers_iff rfl]
  intro i
  fin_cases i <;> intro l hl <;>
    simp only [sections, Finset.mem_insert, Finset.mem_singleton] at hl <;>
    rcases hl with rfl | rfl | rfl <;> simp [Literal.Holds, lit, apartCover, hom, holds]

end HobNob

end ChatzikyriakidisEtAl2025
