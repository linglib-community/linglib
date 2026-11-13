module

public import Linglib.Logic.Aristotelian.Square
public import Linglib.Semantics.Focus.Control
public import Studies.Magri2009

/-!
# Spector (2014): Scalar Implicatures, Blindness and Common Knowledge

Spector proposes that a sentence is infelicitous when every one of its alternatives is trivial in
the context: known to be false, known to be true, or equivalent there to the sentence itself.
[Contextually equivalent alternatives](##Spector2014.not_noTrivialAlternatives_of_inter_eq)
are the case that rules out both *some* and *each* of siblings who share a name, where a
mismatch between the strengthened meaning and common knowledge
[rules out only *some*](##Spector2014.not_odd_all). The condition
[also rules out *John has one wife*](##Spector2014.not_noTrivialAlternatives_one_wife), whose
strengthened meaning [agrees with common knowledge](##Spector2014.not_odd_one_wife), and it
[allows any numeral](##Spector2014.noTrivialAlternatives_univ_Ici) where nothing is known.
Triviality [is lost as the context grows](##Spector2014.NoTrivialAlternatives.mono_context), so
information that falls short of common knowledge leaves a sentence felicitous.

## Implementation notes

A context is the set of worlds compatible with common knowledge, and contextual equivalence of
`φ` and `ψ` in `C` is written `φ ∩ C = ψ ∩ C`. Numerals have their *at least* meaning, `Set.Ici`
over the number of wives, gloves or brothers.

## TODO

* Speaker-equivalence, and the conditions on restrictors and on the smallest constituent in which
  two lexical items are speaker-equivalent, are not represented.

## References

* [spector-2014]
* [magri-2009]
* [rooth-1992]
-/

@[expose] public section

namespace Spector2014

open Set Aristotelian

variable {W : Type*} {C C' φ ψ : Set W} {ALT ALT' : Set (Set W)}

/-! ### Trivial alternatives -/

/-- A proposition `ψ` is trivial given `φ` in the context `C` when it is false throughout `C`,
true throughout `C`, or equivalent to `φ` in `C` (15). -/
def IsTrivial (C φ ψ : Set W) : Prop :=
  Disjoint ψ C ∨ C ⊆ ψ ∨ φ ∩ C = ψ ∩ C

/-- Some alternative of `φ` is not trivial in the context (15b). -/
def NoTrivialAlternatives (C : Set W) (ALT : Set (Set W)) (φ : Set W) : Prop :=
  ∃ ψ ∈ ALT, ¬ IsTrivial C φ ψ

theorem isTrivial_self : IsTrivial C φ φ := .inr (.inr rfl)

theorem isTrivial_univ_iff : IsTrivial univ φ ψ ↔ ψ = ∅ ∨ ψ = univ ∨ φ = ψ := by
  simp only [IsTrivial, disjoint_univ, univ_subset_iff, inter_univ]

theorem IsTrivial.anti (h : IsTrivial C φ ψ) (hC : C' ⊆ C) : IsTrivial C' φ ψ :=
  h.imp (·.mono_right hC) <| Or.imp hC.trans fun h ↦ by
    rw [← inter_eq_self_of_subset_right hC, ← inter_assoc, ← inter_assoc, h]

/-- A sentence with a non-trivial alternative keeps it when less is common knowledge. -/
theorem NoTrivialAlternatives.mono_context (h : NoTrivialAlternatives C' ALT φ) (hC : C' ⊆ C) :
    NoTrivialAlternatives C ALT φ :=
  let ⟨ψ, hψ, hn⟩ := h
  ⟨ψ, hψ, fun ht ↦ hn (ht.anti hC)⟩

theorem NoTrivialAlternatives.mono (h : NoTrivialAlternatives C ALT φ) (hA : ALT ⊆ ALT') :
    NoTrivialAlternatives C ALT' φ :=
  let ⟨ψ, hψ, hn⟩ := h
  ⟨ψ, hA hψ, hn⟩

theorem noTrivialAlternatives_univ_iff :
    NoTrivialAlternatives univ ALT φ ↔ ∃ ψ ∈ ALT, ψ ≠ ∅ ∧ ψ ≠ univ ∧ φ ≠ ψ := by
  simp only [NoTrivialAlternatives, isTrivial_univ_iff, not_or]

/-- When all the alternatives are contextually equivalent to the sentence, it cannot be used
(14). -/
theorem not_noTrivialAlternatives_of_inter_eq (h : ∀ ψ ∈ ALT, φ ∩ C = ψ ∩ C) :
    ¬ NoTrivialAlternatives C ALT φ :=
  fun ⟨ψ, hψ, hn⟩ ↦ hn (.inr (.inr (h ψ hψ)))

-- a non-trivial set of alternatives satisfies the presupposition of the focus operator
theorem NoTrivialAlternatives.squiggleSet {fv : Set (Set W)} (h : NoTrivialAlternatives C ALT φ)
    (hfv : ALT ⊆ fv) (hφ : φ ∈ ALT) : Focus.SquiggleSet φ fv ALT :=
  let ⟨ψ, hψ, hn⟩ := h
  ⟨hfv, hφ, ψ, hψ, fun he ↦ hn (he ▸ isTrivial_self)⟩

/-! ### Some and each

The alternatives *some of these kids* and *each of these kids* over the vertices of the triangle
of opposition, siblings sharing their last name in the worlds other than
`someNotAll`. -/

/-- The `I` and `A` corners of the square. -/
abbrev someAll : Set (Set Triangle) := {↑Triangle.corners.I, ↑Triangle.corners.A}

theorem corners_I_inter_ne_someNotAll :
    (↑Triangle.corners.I : Set Triangle) ∩ {w | w ≠ .someNotAll} = {.all} := by
  ext w
  cases w <;> simp [Triangle.corners]

theorem corners_A_inter_ne_someNotAll :
    (↑Triangle.corners.A : Set Triangle) ∩ {w | w ≠ .someNotAll} = {.all} := by
  ext w
  cases w <;> simp [Triangle.corners]

-- (2), (22)
theorem not_noTrivialAlternatives_someAll {φ : Set Triangle} (hφ : φ ∈ someAll) :
    ¬ NoTrivialAlternatives {w | w ≠ .someNotAll} someAll φ :=
  not_noTrivialAlternatives_of_inter_eq fun ψ hψ ↦ by
    have h : ∀ χ ∈ someAll, χ ∩ {w | w ≠ Triangle.someNotAll} = {Triangle.all} := by
      rintro χ (rfl | rfl)
      exacts [corners_I_inter_ne_someNotAll, corners_A_inter_ne_someNotAll]
    rw [h φ hφ, h ψ hψ]

private theorem corners_A_ssubset_I :
    (↑Triangle.corners.A : Set Triangle) ⊂ ↑Triangle.corners.I :=
  Finset.coe_ssubset.2 (by decide)

-- (2a)
theorem odd_some : Magri2009.Odd {w | w ≠ .someNotAll} someAll ↑Triangle.corners.I := by
  rw [Magri2009.odd_pair_iff (nonempty_of_ssubset corners_A_ssubset_I),
    corners_I_inter_ne_someNotAll]
  exact singleton_subset_iff.2 (Finset.mem_coe.2 (by decide))

/-- The strengthened meaning of *each* does not contradict the common knowledge that makes it
equivalent to *some* (2b). -/
theorem not_odd_all : ¬ Magri2009.Odd {w | w ≠ .someNotAll} someAll ↑Triangle.corners.A := by
  have h : Exhaustification.exhIE someAll (↑Triangle.corners.A : Set Triangle) =
      ↑Triangle.corners.A :=
    Exhaustification.exhIE_eq_self_of_forall _ _ <| by
      rintro a (rfl | rfl) -
      exacts [corners_A_ssubset_I.subset, subset_rfl]
  rw [Magri2009.Odd, h]
  exact not_disjoint_iff.2 ⟨.all, Finset.mem_coe.2 (by decide), by simp⟩

/-! ### Numerals -/

-- (13)
theorem noTrivialAlternatives_univ_Ici (n : ℕ) :
    NoTrivialAlternatives univ (range Ici) (Ici n) :=
  noTrivialAlternatives_univ_iff.2 ⟨Ici (n + 1), ⟨_, rfl⟩, nonempty_Ici.ne_empty,
    fun h ↦ by simpa using h.ge (mem_univ 0), fun h ↦ by simpa using Ici_injective h⟩

/-- Where nobody has more than one wife, every alternative of *John has one wife* is trivial
(11a). -/
theorem not_noTrivialAlternatives_one_wife :
    ¬ NoTrivialAlternatives (Iic 1) (range Ici) (Ici 1) := by
  rintro ⟨_, ⟨n, rfl⟩, h⟩
  refine h ?_
  obtain _ | _ | n := n
  · exact .inr (.inl fun _ _ ↦ Nat.zero_le _)
  · exact isTrivial_self
  · exact .inl (disjoint_left.2 fun x hx hx' ↦ by simp only [mem_Ici, mem_Iic] at hx hx'; omega)

/-- Yet its strengthened meaning, exactly one wife, agrees with that knowledge (11a). -/
theorem not_odd_one_wife : ¬ Magri2009.Odd (Iic 1) (Ici '' Ici 2) (Ici 1) := by
  have hU : ⋃₀ (Ici '' Ici (2 : ℕ)) = Ici 2 := by
    ext x
    simp only [sUnion_image, mem_iUnion, mem_Ici, exists_prop]
    exact ⟨fun ⟨n, hn, hx⟩ ↦ hn.trans hx, fun hx ↦ ⟨2, le_rfl, hx⟩⟩
  have h1 : (1 : ℕ) ∈ Ici 1 \ ⋃₀ (Ici '' Ici (2 : ℕ)) := by rw [hU]; simp
  rw [Magri2009.Odd, Exhaustification.exhIE_eq_sdiff_sUnion ⟨1, h1⟩]
  exact not_disjoint_iff.2 ⟨1, h1, by simp⟩

-- (11b)
theorem not_noTrivialAlternatives_two_gloves :
    ¬ NoTrivialAlternatives {0, 2} (range Ici) (Ici 2) := by
  rintro ⟨_, ⟨n, rfl⟩, h⟩
  refine h ?_
  obtain _ | _ | _ | n := n
  · exact .inr (.inl fun _ _ ↦ Nat.zero_le _)
  · refine .inr (.inr ?_)
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_insert_iff, mem_singleton_iff]
    omega
  · exact isTrivial_self
  · refine .inl (disjoint_left.2 fun x hx hx' ↦ ?_)
    simp only [mem_Ici, mem_insert_iff, mem_singleton_iff] at hx hx'
    omega

end Spector2014
