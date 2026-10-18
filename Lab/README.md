# `Lab/`: theories under development

`Lab` holds theories that no paper has published yet: a collaboration's results in progress,
an extension of a published theory to a fragment its author did not treat, or a theory an agent
proposes. It is where the construction step of the loop happens; `Linglib` and `Studies` remain
the archive, and `Eval` scores a theory here against the same data and the same stated linking
hypotheses as an archived one.

```
Lab/{Project}/{Topic}.lean       -- namespace Lab.{Project}
```

## Rules

- **Imports point in.** A `Lab` file may import `Linglib`, `Studies` and `Eval`. Nothing outside
  `Lab` imports it, so the archive never rests on unpublished work.
- **The archive's standards apply.** Derive rather than stipulate, cite with `[key]` links, state
  the full claim and mark it `sorry` rather than weaken it. A `Lab` file is a default build
  target: a change elsewhere that breaks it is fixed, or the file is deleted, in the same pull
  request.
- **Provenance in the header.** The module docstring says whose work the file records and what
  state it is in: which claims come from the authors, which were derived here, and what still
  needs checking against what the authors intended.
- **Scored by `Eval`.** A theory over a fragment that `Eval` has data for is scored through the
  same linking hypothesis as the registered accounts (`Eval.Presupposition.Theory`), never through a
  rule of its own.
- **Graduation.** When a paper publishes the content, the file moves to `Studies/AuthorYear.lean`
  and the paper's account is registered in `Eval`. A definition that a second paper consumes
  moves to the theory layer.
