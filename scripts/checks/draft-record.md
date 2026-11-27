# Draft a record

Instructions for an agent (for Claude Code, say "follow `scripts/checks/draft-record.md`" or copy
this file to a skill) that drafts a faithfulness record for a paper and its study file, then has the
Lean back-translated and compared with the paper's claims.

Read `checks/README.md` first: it defines the record, the kinds and the relations. This skill
produces an **unsigned draft** for a human to check. Never sign anything, and never write a
sign-off into the ledger: sign-offs are made by people.

Arguments: the paper (a PDF or text file the reviewer provides), its bibliography key in
`references.bib`, and the study file (`Studies/<Name>.lean`). Ask for whichever is missing. Do not
fetch the paper yourself. If the key is not in `references.bib`, stop and say so.

The one rule: **fidelity to the paper.** The claims are written from the paper alone. The Lean is
mapped onto them, never the other way. Where the Lean disagrees with a claim, the disagreement goes
in `relation` and `notes`; the claim stays as the paper has it.

## Stages

Run each of stages 1 and 2 in a fresh subagent (Agent tool, no `fork`), so that it starts with no
context of yours. Give it the named prompt file as its instructions, and only the inputs named.

1. **Claims.** Subagent inputs: `scripts/checks/draft-claims-prompt.md` and the paper. Nothing
   else: not the study file, not the existing `checks/` file, not this conversation. It returns
   TOML items (`id`, `kind`, `label`, `claim`). Save them as the draft's items.
2. **Mapping.** Subagent inputs: `scripts/checks/draft-mapping-prompt.md`, the claims from stage 1,
   and the study file, with access to read the repository's Lean. It must not see the paper. It
   returns `decls`, `relation` and `notes` per item, and the declarations that match no item.
3. **Assemble** `checks/<key>.toml`: `source = "<key>"`, a header comment saying the file is an
   unsigned draft and how it was made, then each item with the claim from stage 1 and the mapping
   from stage 2, unedited. If the file exists, do not overwrite it: write the draft to the
   scratchpad, not `checks/` (every `checks/*.toml` is read as a record), and tell the reviewer it
   must be merged by hand. Verify every `decls` name with `python3 scripts/checks.py status <key>`
   (`broken` means a name does not resolve); fix a wrong name only by asking the mapping subagent
   again, not by guessing.
4. **Back-translate and compare.** `checks.py review` does both. Each item's Lean is described
   by a blind model that has not seen the paper or the record (`gloss`), and a second model that has
   seen neither the paper nor the Lean compares that description with the claim. Run:

   ```
   python3 scripts/checks.py review <key> --command "scripts/checks/gloss-claude.sh claude-sonnet-5-5" > review.md
   ```

   Costs a fair share of a usage limit, so ask the reviewer before running it, and which model to
   use. Do not run it from a context that has read the Lean or the paper: it needs none of it.
5. **Report** to the reviewer, in this order, without editing the claims in response:
   * **Looks unfaithful:** the items in the review's first group, each with the difference the
     comparison found. These are where the reviewer should look first, in the Lean.
   * **Needs a look:** items whose comparison was unclear, items whose mapping subagent chose
     `variant`, `specializes` or `missing`, and the declarations that match no item.
   * **Looks right:** items whose back-translation agreed with an `exact` relation. Say that this
     is the lowest-risk group, not that it is verified: both models can be wrong, and the
     reviewer still signs.
   * Doubts the claims stage recorded ("The paper does not say whether…"), since a reviewer should
     check those against the paper.

   Do not rerun a stage until it comes out the way you expected. A disagreement between the stages
   is the output.

Tell the reviewer what they still have to do: read each claim against the paper, since stage 1 is
a model's reading; read the flagged Lean; then sign with `checks.py sign`.
