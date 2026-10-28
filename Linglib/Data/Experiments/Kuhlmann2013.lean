module

public import Linglib.Data.Experiments.Schema

/-!
# Kuhlmann2013: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/Kuhlmann2013.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The evaluation of sections 7.4 and 8.4: the lexicalized LCFRS rules extracted from the training
sections of the five genuine dependency treebanks of the 2006 CoNLL shared task, counted as tokens,
and the trees they are extracted from, with the number of rules and of trees lost when the yield
functions are restricted to fan-out 1, to fan-out at most 2, and to well-nested yield functions of
fan-out at most 2. A tree is lost when its construction tree contains a rule the restriction
excludes. Table 3 prints the first two restrictions, and Table 4 repeats its columns and adds the
third.

## References

* [kuhlmann-2013]
-/

@[expose] public section

namespace Kuhlmann2013

open Data.Experiments

/-- The treebank, by the language the paper names it for. -/
inductive Treebank where
  /-- Arabic: the Prague Arabic Dependency Treebank -/
  | arabic
  /-- Czech: the Prague Dependency Treebank of Czech -/
  | czech
  /-- Danish: the Danish Dependency Treebank -/
  | danish
  /-- Slovene: the Slovene Dependency Treebank -/
  | slovene
  /-- Turkish: the Metu-Sabancı treebank of Turkish -/
  | turkish
  deriving DecidableEq, Repr, Fintype

/-- A restriction on the yield functions of the extracted rules. -/
inductive Restriction where
  /-- fan-out = 1: yield functions of fan-out 1 -/
  | fanOutOne
  /-- fan-out ≤ 2: yield functions of fan-out at most 2 -/
  | fanOutLeTwo
  /-- + well-nested: well-nested yield functions of fan-out at most 2 -/
  | wellNested
  deriving DecidableEq, Repr, Fintype

/-- A row of Tables 3 and 4, pp. 376 and 379: the number of rules extracted from a treebank and
of its trees. -/
structure Size where
  /-- The number of rules extracted, counted as tokens. -/
  rules : ℕ
  /-- The number of trees. -/
  trees : ℕ
  deriving DecidableEq, Repr

/-- The cells of Tables 3 and 4, pp. 376 and 379, by treebank; checked against the page images. -/
def size : Treebank → Size
  | .arabic => ⟨5839, 1460⟩  -- the text's 0.74% rule loss at fan-out 1 is 411 of 55,839 rules
  | .czech => ⟨1322111, 72703⟩
  | .danish => ⟨99576, 5190⟩
  | .slovene => ⟨30284, 1534⟩
  | .turkish => ⟨62507, 4997⟩

/-- A row of Tables 3 and 4, pp. 376 and 379: the rules and trees of a treebank a restriction
loses. -/
structure Loss where
  /-- The number of rules the restriction excludes. -/
  rules : ℕ
  /-- The number of trees whose construction tree contains an excluded rule. -/
  trees : ℕ
  deriving DecidableEq, Repr

/-- The cells of Tables 3 and 4, pp. 376 and 379, by treebank and restriction; checked against
the page images. -/
def loss : Treebank → Restriction → Loss
  | .arabic, .fanOutOne => ⟨411, 163⟩
  | .arabic, .fanOutLeTwo => ⟨1, 1⟩
  | .arabic, .wellNested => ⟨2, 2⟩
  | .czech, .fanOutOne => ⟨22283, 16831⟩
  | .czech, .fanOutLeTwo => ⟨328, 312⟩
  | .czech, .wellNested => ⟨407, 382⟩
  | .danish, .fanOutOne => ⟨1229, 811⟩
  | .danish, .fanOutLeTwo => ⟨11, 9⟩
  | .danish, .wellNested => ⟨17, 15⟩
  | .slovene, .fanOutOne => ⟨530, 340⟩
  | .slovene, .fanOutLeTwo => ⟨14, 11⟩
  | .slovene, .wellNested => ⟨17, 13⟩
  | .turkish, .fanOutOne => ⟨924, 580⟩
  | .turkish, .fanOutLeTwo => ⟨54, 33⟩
  | .turkish, .wellNested => ⟨68, 43⟩

end Kuhlmann2013
