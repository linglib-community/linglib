module

public import Linglib.Data.Statistics.Schema

/-!
# Cinque2005: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Cinque2005.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The 24 orders of demonstrative, numeral, adjective and noun, each with whether it is attested and,
if so, the frequency label the paper gives from its survey of the typological literature, and the
number of marked options the paper's discussion of each derivation states. The paper prints no count
for (6b) and (6p) and none for the unattested orders.

## References

* [cinque-2005]
-/

@[expose] public section

namespace Cinque2005

open Data.Statistics

/-- The label of an order in (6). -/
inductive Label where
  /-- (6a): (6a) -/
  | a
  /-- (6b): (6b) -/
  | b
  /-- (6c): (6c) -/
  | c
  /-- (6d): (6d) -/
  | d
  /-- (6e): (6e) -/
  | e
  /-- (6f): (6f) -/
  | f
  /-- (6g): (6g) -/
  | g
  /-- (6h): (6h) -/
  | h
  /-- (6i): (6i) -/
  | i
  /-- (6j): (6j) -/
  | j
  /-- (6k): (6k) -/
  | k
  /-- (6l): (6l) -/
  | l
  /-- (6m): (6m) -/
  | m
  /-- (6n): (6n) -/
  | n
  /-- (6o): (6o) -/
  | o
  /-- (6p): (6p) -/
  | p
  /-- (6q): (6q) -/
  | q
  /-- (6r): (6r) -/
  | r
  /-- (6s): (6s) -/
  | s
  /-- (6t): (6t) -/
  | t
  /-- (6u): (6u) -/
  | u
  /-- (6v): (6v) -/
  | v
  /-- (6w): (6w) -/
  | w
  /-- (6x): (6x) -/
  | x
  deriving DecidableEq, Repr, Fintype

/-- A category of the nominal phrase. -/
inductive Category where
  /-- Dem: the demonstrative -/
  | dem
  /-- Num: the cardinal numeral -/
  | num
  /-- A: the adjective -/
  | adj
  /-- N: the noun -/
  | noun
  deriving DecidableEq, Repr, Fintype

/-- The frequency an order is attested with, as (6) labels it. -/
inductive Frequency where
  /-- very many languages: very many languages -/
  | veryMany
  /-- many languages: many languages -/
  | many
  /-- few languages: few languages -/
  | few
  /-- very few languages: very few languages -/
  | veryFew
  /-- ∅: unattested -/
  | unattested
  deriving DecidableEq, Repr, Fintype

/-- A row of (6), pp. 319-320; counts pp. 321-324: an order of the four categories with its
frequency and the number of marked options the paper states for its derivation. -/
structure Order where
  /-- The label. -/
  label : Label
  /-- The order, left to right. -/
  order : List Category
  /-- The frequency. -/
  frequency : Frequency
  /-- The number of marked options stated for the order's derivation. -/
  markedOptions : Option ℕ
  deriving DecidableEq, Repr

/-- The 24 rows of (6), pp. 319-320; counts pp. 321-324, in the paper's order; from a sample of
languages coded from their descriptions; checked against the page images. -/
def orders : List Order :=
  [⟨.a, [.dem, .num, .adj, .noun], .veryMany, some 0⟩,
   ⟨.b, [.dem, .num, .noun, .adj], .many, none⟩,
   ⟨.c, [.dem, .noun, .num, .adj], .veryFew, some 2⟩,
   ⟨.d, [.noun, .dem, .num, .adj], .few, some 1⟩,
   ⟨.e, [.num, .dem, .adj, .noun], .unattested, none⟩,
   ⟨.f, [.num, .dem, .noun, .adj], .unattested, none⟩,
   ⟨.g, [.num, .noun, .dem, .adj], .unattested, none⟩,
   ⟨.h, [.noun, .num, .dem, .adj], .unattested, none⟩,
   ⟨.i, [.adj, .dem, .num, .noun], .unattested, none⟩,
   ⟨.j, [.adj, .dem, .noun, .num], .unattested, none⟩,
   ⟨.k, [.adj, .noun, .dem, .num], .veryFew, some 2⟩,
   ⟨.l, [.noun, .adj, .dem, .num], .few, some 1⟩,
   ⟨.m, [.dem, .adj, .num, .noun], .unattested, none⟩,
   ⟨.n, [.dem, .adj, .noun, .num], .veryFew, some 2⟩,
   ⟨.o, [.dem, .noun, .adj, .num], .many, some 1⟩,
   ⟨.p, [.noun, .dem, .adj, .num], .veryFew, none⟩,
   ⟨.q, [.num, .adj, .dem, .noun], .unattested, none⟩,
   ⟨.r, [.num, .adj, .noun, .dem], .veryFew, some 2⟩,
   ⟨.s, [.num, .noun, .adj, .dem], .few, some 2⟩,
   ⟨.t, [.noun, .num, .adj, .dem], .few, some 1⟩,
   ⟨.u, [.adj, .num, .dem, .noun], .unattested, none⟩,
   ⟨.v, [.adj, .num, .noun, .dem], .unattested, none⟩,
   ⟨.w, [.adj, .noun, .num, .dem], .veryFew, some 1⟩,
   ⟨.x, [.noun, .adj, .num, .dem], .veryMany, some 0⟩]

end Cinque2005
