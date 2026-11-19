# Agent Guide for vyper-hol workflow

## CRITICAL: Tool Usage

Prefer using dedicated tools instead of bash operation:
- **Read tool** for ALL file reading (not `cat`, `head`, `tail`, `less`)
- Prefer a dedicated search tool when available; otherwise use `rg`, `grep`, or `git grep`, keeping searches scoped and output bounded.
- **Write/Edit tools** for file modifications (not `echo`, `sed`, `awk`)
- **`holbuild`** for HOL operations/builds and proof feedback when authorized. The old HOL4 MCP tools (`hol_send`, `hol_file_init`, `hol_state_at`, MCP `holmake`, etc.) are deprecated and should not be used.

## Completion Standard

If you are working on a proof, your task is NOT complete until:
- All cheats are removed from the proof
- The build passes with no CHEAT warnings

**Documenting "what's left to do" is NOT completion.** If you can describe what work remains, then do that work - don't just write it down and stop. Keep working until the proof is actually done or you hit a genuine blocker requiring human input.

## CRITICAL: Never Delete Proof Code

**NEVER replace a proof with `cheat` without preserving the original.**

If you need to temporarily cheat a proof for debugging:
1. Comment out the original proof code (don't delete it)
2. Add `cheat` below the commented code
3. Add a comment explaining why it's cheated

```sml
(* TEMPORARILY CHEATED - investigating proof/build issue
Proof
  Induct_on `fuel` >- rw[...] >>
  ...original proof...
QED
*)
Proof
  cheat
QED
```

Deleting proof code to replace with cheat is NEVER acceptable.

## Project Structure

```
syntax/          # Vyper AST (vyperAST) and its ML syntax functions
frontend/        # annotated JSON import and translation into the AST
semantics/       # the definitional interpreter (vyperInterpreter) and its layers
semantics/cv/    # CPS/small-step interpreter and cv translations
semantics/type/  # static type system and the check_contract checker
semantics/prop/  # properties of the semantics (type soundness, frames, ...)
lowering/        # Vyper-to-Venom compiler (lowering/defs/) and its proofs
venom/           # Venom IR: defs/, analysis/, passes/ (one directory per pass),
                 # simulation/, proofs/, codegen/, compiler/
bytecode/        # bytecode parity against the pinned Vyper compiler
tests/           # semantics tests and the generated Vyper test-suite replays
tools/, docs/    # scripts and documentation
```

### Design Principles
- **Reusability**: DFG and equivalence infrastructure can be used by other passes
- **Incremental building**: Each file builds independently, Holmake handles deps
- **Separation of concerns**: Analysis vs transformation vs correctness proof
- **Modular file sizes**: Aim for 100-500 LOC per file (soft limit)

### File Organization Guidelines (soft limits)
- **50 LINES PER PROOF MAX** otherwise you have trouble keeping track.
- **~10-15 files max per directory** - use subdirectories if significantly more
- **~100-500 LOC per file** - split larger files by logical section when practical
- **Clear dependency chains** - avoid circular dependencies between files
- **Name files by content type**:
  - `*DefsScript.sml` - type definitions and basic operations
  - `*EquivScript.sml` - equivalence proofs
  - `*TransformScript.sml` - transformation definitions
  - `*BlockScript.sml`/`*FunctionScript.sml` - correctness proofs by scope

## Building

Use direct script edits plus `holbuild` for HOL proof development and build validation.

**Workflow: Edit / holbuild / loop**
1. Edit the `.sml` file directly
2. Run `holbuild` — on proof failure it prints the goal state (via goalfrag)
3. Read the goal state, edit proof, re-run `holbuild` until it passes

**Build time:** Keep under 30s. If longer, refactor the proof.

**Theory files:** `.sig` and `.uo` files are generated in the `.holbuild/` subdir, never in the source directory. Don't try to load theories (`load "fooTheory"`) that haven't been built yet - run `holbuild` first.

**No interactive mode:** Do not use interactive proof-state workflows, including `g()`, `e()`, or `p()`.

Use **holbuild** for HOL4 build/proof feedback when authorized by the user.

The old HOL4 MCP workflow is deprecated. Do **not** use `hol_send`, `hol_file_init`,
`hol_state_at`, or MCP `holmake` for proof development.

When proof-tool use is authorized, prefer a holbuild-centered workflow:
1. Edit the relevant theory file.
2. Run holbuild/build feedback on the file or target theory.
3. Use the reported goal/error context to refine the proof.
4. Keep changes small and re-check frequently.

**Never use `--skip-goalfrag`:** It is not allowed.

**Checking for cheats:** check theories for cheats, oracles or axioms with `holbuild check THEORY[:THEOREM]`, never with `Thm.tag`/`Tag.dest_tag` or `null (hyp th)` checks in a script (CI rejects them). To have CI enforce a theory or theorem clean, add its selector to `.github/holbuild-check-targets.txt`.

### File Conventions (repo-specific)

Local test/scratch files use **dot prefixes** (gitignored), except buildable
scratch theories, which use ordinary `<name>Script.sml` names because holbuild
ignores dot-prefixed sources. Remove scratch theories and other probes before
publication.

- `.hol_init.sml` - auto-loaded on session start
- `.hol_test.sml` - temporary test scripts

Try to keep theory files under 500 LOC (soft limit).

A hand-written theory is built by default, and by CI, only if a build root in
`holproject.toml` imports or refers to it, directly or through other theories.
(Generated replay theories and the coverage report have their own CI job.) The
roots are a few rollups, one per purpose. When you add a theory, import it from
the theory that uses it, or add it to the rollup that fits, under the matching
comment: the results go in `vyperHol` or its sub-rollups (`vyperSemanticsHol`,
`venomAnalysisHol`, `venomPassesHol`, `vyperLoweringHol`), language tests in `tests/vyperTestsHol`, lowering and
compiler checks in `lowering/loweringChecks`, and Venom checks in
`venom/venomChecks`. Pinned-Python witnesses go in
`lowering/evalCompilerWitnesses`.

### Naming conventions

The proofs should not depend on automatically generated variable names. Use `rename1` when needed.

When generalizing a definition (adding parameters), the general version gets the clean name. If the old simpler version is kept as a helper, it gets a suffix (`_simple`, `_helper`). Never the reverse (`_gen`, `_ctx`). Top-level API = shortest, clearest name.

## HOL4 Tactics Reference

For monadic/list preservation proofs and other branch-heavy HOL4 scripts, also read `docs/HOL4_PROOF_CONTROL_LESSONS.md`. It records project-specific lessons about controlling parallel subgoals, preserving specialized facts, and using `drule_all` safely.

### Fast tactics (prefer these)
- `simp[thm]` - simplification
- `gvs[AllCaseEqs()]` - case analysis with simplification, clears assumptions
- `fs[]` - full simplification (keeps all assumptions)
- `FIRST [tac1, tac2]` - try in order, stop on first success
- `drule_all thm` - forward reasoning, matches all antecedents from assumptions

### When to use what
- **Case splits:** `Cases_on \`term\` >> gvs[]`
- **Induction on lists:** `Induct_on \`list\``
- **Mutual recursion induction:** `ho_match_mp_tac fn_ind`
- **Forward reasoning:** `drule_all thm >> simp[]` (better than `irule` for tricky instantiation)
- **Existential witnesses:** `qexists_tac \`witness\``
- **State equivalence chains:** `irule state_equiv_trans >> qexists_tac \`mid\` >> gvs[]`

### Parallel vs Sequential Subgoals
- **`>-` (THEN1):** Solve first subgoal only, fail if it doesn't close
- **`>|` (parallel):** Give a tactic for each subgoal: `Cases_on x >> gvs[] >| [tac1, tac2]`
- **`>>` (THEN):** Apply tactic to all resulting subgoals

### Avoiding proof explosion
- **NEVER:** `rpt metis_tac[...]` on many subgoals - exponential blowup
- **NEVER:** `metis_tac` on goals with large search space - can hang forever
- **NEVER:** `fs[complex_recursive_def]` - use `simp[Once def]` instead
- **Instead:** Use explicit `>-` for each case, or `FIRST [drule_all ..., fallback]`
- **Pattern:** `Cases_on \`x\` >> fs[] >> FIRST [drule_all helper >> simp[], gvs[AllCaseEqs()]]`

### Performance-Critical Patterns
- `simp[Once def]` not `fs[def]` for recursive defs (avoids blowup)
- `irule thm` not `metis_tac[thm]` (direct vs search)
- Unfold assumptions separately: `qpat_x_assum \`pat\` mp_tac >> simp[Once def] >> strip_tac`
- RHS only: `CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [def]))`

### State Equivalence Patterns
- Step equiv: `drule_all step_inst_state_equiv >> strip_tac >> simp[]`
- Chaining: `irule state_equiv_trans >> qexists_tac \`s_mid\` >> gvs[]`
- run_block induction: `ho_match_mp_tac run_block_ind >> ...`

## Proof structure guidelines

Theorem statements should have minimal preconditions, maximal useful conclusions, and accurate natural-language comments when present. Avoid catch-all theorem conclusions like `_ => T`/`_ => F` when enumerating constructors would make coverage clear.

Avoid long proofs. If you encounter difficulties with a complex subgoal, formulate this exact subgoal as a helper lemma and prove it separately. Make sure you can use the formulated helper lemma in the original proof.

When proving a theorem by induction or by cases with many complex cases:
- prove directly only simple cases that can be closed with at most 3 tactics,
- formulate a helper lemma stating the exact subgoal for each complex case that requires more than 3 tactics to close.

Re-use existing theorems as much as possible. Before creating a new helper lemma, always check if an existing theorem can be applied directly.

Before handing in proof work, check it for restated theorems with `python3 -I tools/dupscan.py <worktree> <base-ref> <verifereum checkout>`. For each SAME, ALPHA or WITHIN-NEW hit, confirm that the matched theorem is live (not inside a comment) and states the same fact, then remove the copy; read each FUZZY hit by eye.

## Key Theories

Source semantics:
- `vyperASTTheory` (`syntax/`): `expr`, `stmt`, `toplevel`
- `vyperInterpreterTheory` (`semantics/`): `evaluate_def` (`eval_stmts`, `eval_expr`), `load_contract`, `call_external`
- `vyperTypeSystemTheory`, `vyperTypeContractTheory` (`semantics/type/`): `well_typed_expr`, `check_contract`
- `vyperTypeSoundnessTheory` (`semantics/prop/`); the `vyperSemanticsHol` rollup lists the semantics results

Compiler:
- `compileVyperTheory` (`lowering/defs/`): `compile_vyper`
- `e2eCorrectnessTheory`, `e2eDeployCorrectnessTheory` (`lowering/`): `vyper_call_correct`, `e2e_deploy_correctness`

Venom:
- `venomInstTheory` (`venom/defs/`): `instruction`, `opcode`, `is_terminator`
- `venomStateTheory` (`venom/defs/`): `venom_state`, `lookup_var`, `update_var`, `eval_operand`
- `venomExecSemanticsTheory` (`venom/defs/`): `step_inst_base`, `run_block`, `exec_result`
- `dfgDefsTheory` (`venom/analysis/dfg/defs/`): `dfg_analysis`, `dfg_build_function`, `well_formed_dfg`
- `stateEquivTheory` (`venom/simulation/defs/`): `state_equiv`, `result_equiv`; `execEquivProofsTheory` (`venom/proofs/`) lifts them through `step_inst` and `run_block` (`step_inst_result_equiv`, `run_block_result_equiv`)

## Debugging Tips

1. **Variable conflicts:** Names like `fn`, `f` conflict with HOL4. Use `func` or type annotations
2. **Pair returns:** Use `Cases_on \`fn args\`>> fs[]` to split
3. **irule not matching:** Try `drule` or `drule_all` for forward reasoning
4. **fs not simplifying:** May need type-specific theorems like `exec_result_distinct`

## Reference Repos

- `vyper-ref/` - Vyper compiler source (reference for Venom IR semantics)
- `~/verifereum/` - Verifereum EVM formalization (provides word256, memory model)

If these symlinks are missing, ask the operator to provide access.

## Proof Strategy

**When proofs get complex:** Step back, look for helper lemmas, consider refactoring definitions, and validate incrementally with `holbuild`. Cheats are temporary scaffolding only.

**Signs you're on wrong track:** Many nested TRY blocks, dozens of subgoals, slow tactics, unpredictable variable names (`h''` etc.) → stop and reconsider.

## HOL4

### sg vs by vs suffices_by

These are related but different:
- **`'tm' by tac`** - Proves `tm` using `tac`, adds result as assumption. `tac` MUST close `tm`.
- **`sg 'tm' >- tac`** - Creates `tm` as first subgoal, applies `tac` to it. `tac` MUST close `tm`.
- **`sg 'tm' >> tac`** - Creates `tm` as subgoal, applies `tac` to ALL subgoals (including continuation)
- **`'tm' suffices_by tac`** - Sets `tm ==> goal` as new goal, proves with `tac`

**Common mistake:** Using `sg tm >- tac` when `tac` doesn't fully close the subgoal. The error "first subgoal not solved by second tactic" means `tac` didn't close `tm`.

### metis_tac/irule Issues

- `metis_tac[]` struggles with quantifier instantiation - use `gvs[]` or explicit `first_x_assum irule >> simp[]`
- If `irule thm` fails, try `drule_all thm` for forward reasoning

### ALOOKUP/MAP/FILTER Proofs

When proving properties about `ALOOKUP` on mapped or filtered lists:

1. **Use abbreviations systematically** - Abbreviate complex terms to make proof structure clear:
   ```sml
   \\ qmatch_goalsub_abbrev_tac`option_CASE alo`
   \\ `alo = SOME z` suffices_by simp[]
   ```

2. **Show function equality for MAP** - When using `ALOOKUP_MAP_KEY_INJ`:
   ```sml
   \\ qmatch_goalsub_abbrev_tac`MAP fi`
   \\ `fi = $, src_id ## I` by simp[Abbr`fi`, FUN_EQ_THM, FORALL_PROD]
   \\ pop_assum SUBST_ALL_TAC
   ```

3. **Substitute in the right direction** - Use `SUBST1_TAC o SYM` when needed:
   ```sml
   \\ pop_assum $ SUBST1_TAC o SYM
   ```

4. **For drule with extra quantifiers** - Use `drule_all_then` with `qspec_then`:
   ```sml
   \\ drule_all_then(qspec_then`src_id_opt`strip_assume_tac) lookup_callable_function_eq_ALOOKUP_module_fns
   ```

5. **Chain drules properly** - Use `drule_at_then`:
   ```sml
   \\ drule_at_then Any drule ALOOKUP_FLAT_MAP_module_fns
   ```

6. **For filter equality** - Abbreviate predicate, prove equality, substitute:
   ```sml
   \\ qmatch_goalsub_abbrev_tac`ALOOKUP (FILTER P ls) k`
   \\ `P = λ(k,v). ¬MEM k cx.stk` by simp[Abbr`P`,FUN_EQ_THM,FORALL_PROD]
   \\ pop_assum SUBST_ALL_TAC
   ```

7. **Avoid `rw[]` too early** - Use `rpt gen_tac \\ simp[]` then `strip_tac` to control when hypotheses are introduced

8. **Use `reverse strip_tac`** - To handle disjunctive cases in the natural order after `CaseEq"option"`

## HOL4 Script Style

Use modern syntax for HOL4 script files. Scripts should start with the `Theory` keyword and use `Ancestors` and `Libs` to specify dependencies, rather than using `open` explicitly.

**Ancestors vs Libs**: Theories (anything ending in `Theory`) go in `Ancestors`, never in `Libs`. Only non-theory libraries belong in `Libs` (e.g. `Defn`, `TotalDefn`, `pairLib`, `BasicProvers`). Note: `Ancestors` opens only the *named* theories — transitive ancestors are loaded but not opened. List a theory explicitly if you need its theorem names in scope.

Example:
```sml
Theory myTheory
Ancestors
  parentTheory1 parentTheory2 finite_map
Libs
  pairLib

(* definitions and theorems here *)
```

## Code Documentation Style

- **Section headers:** `(* ===== Section Name ===== *)`
- **Annotations:** `(* TOP-LEVEL: ... *)`, `(* Helper: ... *)`, `(* KEY LEMMA: ... *)`
- **File headers:** List TOP-LEVEL defs/thms (API) vs Helper (internal)

## Code Simplification

- **Consolidate similar theorems:** If 12 cases have the same proof, make one theorem with /\
- **Derive corollaries:** Prove general case, derive specifics via `metis_tac[general_thm]`
- **Reuse theorems:** `drule_all existing_thm` instead of re-proving inline
- **Combine case tactics:** If all case branches have identical proofs, apply tactic after case split
- **Remove unused defs:** `grep -r "defname" *.sml` to check if actually used
