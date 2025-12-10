# Agent Guide for Venom HOL4 Verification

**IMPORTANT: After conversation compaction, ALWAYS read this file (CLAUDE.md or AGENTS.md) and PLAN.md to restore context.**

Always read .claude/settings.json to learn what tool uses are available to you and to give higher precedence to those tools.

## CRITICAL: Tool Usage

**NEVER use bash for file operations.** Use the dedicated tools instead:
- **Read tool** for ALL file reading (not `cat`, `head`, `tail`, `less`)
- **Grep tool** for searching file contents (not `grep`, `rg`)
- **Write/Edit tools** for file modifications (not `echo`, `sed`, `awk`)

Only use Bash for:
- Running `Holmake` builds
- Running `~/hol-agents/hol-agent-helper.sh` commands
- Git operations (`git grep`, `git status`, etc.)

**Why:** Bash file operations require permission prompts. The dedicated tools don't.

## Completion Standard

If you are working on a proof, your task is NOT complete until:
- All cheats are removed from the proof
- The build passes with no CHEAT warnings

**Documenting "what's left to do" is NOT completion.** If you can describe what work remains, then do that work - don't just write it down and stop. Keep working until the proof is actually done or you hit a genuine blocker requiring human input.

## Project Structure

```
venom-semantics/theories/     # HOL4 theory files
├── venomStateScript.sml      # State definitions (~200 LOC)
├── venomInstScript.sml       # Instruction definitions (~300 LOC)
├── venomSemScript.sml        # Operational semantics (~450 LOC)
│
├── dfgDefsScript.sml         # DFG types, build, well-formedness (~300 LOC)
├── dfgOriginsScript.sml      # Origin computation, phi_single_origin (~400 LOC)
│
├── stateEquivScript.sml      # State equivalence definitions (~300 LOC)
├── execEquivScript.sml       # Execution equivalence theorems (~400 LOC)
│
├── phiTransformScript.sml    # PHI elimination transformations (~220 LOC)
├── phiWellFormedScript.sml   # Well-formedness definitions (~250 LOC)
├── phiBlockScript.sml        # Block-level correctness (~480 LOC)
└── phiFunctionScript.sml     # Function-level correctness (~230 LOC)
```

### File Dependencies
```
venomStateScript.sml
    ↓
venomInstScript.sml
    ↓
venomSemScript.sml
    ↓
dfgDefsScript.sml
    ↓
dfgOriginsScript.sml ←──────────────┐
    ↓                               │
stateEquivScript.sml                │
    ↓                               │
execEquivScript.sml                 │
    ↓                               │
phiTransformScript.sml ─────────────┤
    ↓                               │
phiWellFormedScript.sml             │
    ↓                               │
phiBlockScript.sml                  │
    ↓                               │
phiFunctionScript.sml ──────────────┘
```

### Design Principles
- **Reusability**: DFG and equivalence infrastructure can be used by other passes
- **Incremental building**: Each file builds independently, Holmake handles deps
- **Separation of concerns**: Analysis vs transformation vs correctness proof
- **Modular file sizes**: Aim for 100-500 LOC per file (soft limit)

### File Organization Guidelines (soft limits)
- **~10-15 files max per directory** - use subdirectories if significantly more
- **~100-500 LOC per file** - split larger files by logical section when practical
- **Clear dependency chains** - avoid circular dependencies between files
- **Name files by content type**:
  - `*DefsScript.sml` - type definitions and basic operations
  - `*EquivScript.sml` - equivalence proofs
  - `*TransformScript.sml` - transformation definitions
  - `*BlockScript.sml`/`*FunctionScript.sml` - correctness proofs by scope

## Building

```bash
VFMDIR=/home/ubuntu/verifereum Holmake --qof
```

**Build time:** Keep under 30s. If longer, refactor the proof.

**Theory files:** `.sig` and `.uo` files are generated in the `.hol/` subdir, never in the source directory. Don't try to load theories (`load "fooTheory"`) that haven't been built yet - run `Holmake` first.

## Interactive HOL Sessions

Use the helper script for debugging proofs:

```bash
# Start session (from theories directory)
~/hol-agents/hol-agent-helper.sh start

# Check status
~/hol-agents/hol-agent-helper.sh status

# Send simple commands (no backquotes)
~/hol-agents/hol-agent-helper.sh send 'open arithmeticTheory;'

# Send commands with backquotes - use a file
# Write to hol_cmd.sml, then:
~/hol-agents/hol-agent-helper.sh send:hol_cmd.sml

# IMPORTANT: ALWAYS check output using the helper script's log command
# NEVER use raw file paths like ~/.hol/hol_output.log directly
~/hol-agents/hol-agent-helper.sh log | tail -50

# Stop
~/hol-agents/hol-agent-helper.sh stop
```

**CRITICAL: Always use `~/hol-agents/hol-agent-helper.sh log` for checking HOL output. Do NOT access raw log files directly.**

### Initialization

For code that should always run at session start (loading theories, etc.), put it in `.hol_init.sml` in the working directory. This is auto-loaded by `start`.

**IMPORTANT:** Before issuing any commands, check the contents of `.hol_init.sml` to see what's already loaded. Don't duplicate load commands.

### Sending Commands

For commands with HOL term quotations (backquotes), **always use a temp file**:

```sml
(* .hol_cmd.sml *)
g `!n. n + 0 = n`;
e (Induct_on `n`);
```

Then: `~/hol-agents/hol-agent-helper.sh send:.hol_cmd.sml`

### File Naming Conventions

Local test/scratch files should use **dot prefixes** to keep them gitignored:

- `.hol_cmd.sml` - command file for sending to HOL session
- `.hol_init.sml` - auto-loaded on session start
- `.hol_test.sml` - temporary test scripts

These `.hol*` files are gitignored. Avoid unprefixed names like `test.sml` or `hol_cmd.sml` which will show up in git status.

### File Size
Try to keep files under 500 LOC for better context management (soft limit, not strict).

## HOL4 Tactics Reference

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

### Large Case Splits (e.g., 90+ opcode cases)
When case-splitting on a datatype with many constructors:
- **rw vs gvs/simp:** `rw[defs]` is slightly faster than `gvs[defs]` (~0.88s vs ~1.1s for 93 goals)
- **Single-pass simplification:** After case split, `gvs[step_inst_def, transform_inst_def, AllCaseEqs()]`
  processes ALL goals in one pass (~1s), solving most and leaving only the interesting cases
- **FIRST for remaining cases:** Use `FIRST [irule thm1 >> simp[], irule thm2 >> simp[], fallback]`
  to handle remaining goals efficiently
- **Pattern for opcode proofs:**
  ```sml
  Cases_on `inst.inst_opcode` >>
  gvs[step_inst_def, transform_inst_def, AllCaseEqs()] >>
  FIRST [
    irule exec_binop_transform >> simp[],
    irule exec_unop_transform >> simp[],
    irule exec_modop_transform >> simp[],
    simp[transform_operands_def] >> rpt (drule_all transform_operand_sound >> strip_tac >> gvs[])
  ]
  ```
- **Key insight:** gvs/simp/rw with `AllCaseEqs()` can handle most cases automatically;
  only special cases (like exec_binop needing irule) require explicit tactics

### State Equivalence Patterns
- Step equiv: `drule_all step_inst_state_equiv >> strip_tac >> simp[]`
- Chaining: `irule state_equiv_trans >> qexists_tac \`s_mid\` >> gvs[]`
- run_block induction: `ho_match_mp_tac run_block_ind >> ...`

## Key Theories

### venomSemTheory
- `step_inst` - single instruction semantics
- `run_block` - execute basic block (has termination proof)
- `run_block_ind` - induction principle for run_block proofs
- `eval_operand` - evaluate operand to value
- `exec_result` - OK, Halt, Revert, Error

### venomStateTheory
- `venom_state` - record with vs_vars, vs_memory, vs_storage, etc.
- `lookup_var`, `update_var` - variable operations

### venomInstTheory
- `instruction` - record with inst_id, inst_opcode, inst_operands, inst_output
- `opcode` - PHI, ASSIGN, ADD, SUB, etc.
- `is_terminator` - check if opcode is JMP, JNZ, STOP, REVERT

### dfgDefsTheory (DFG Definitions)
- `dfg` - type alias for `(string, instruction) fmap`
- `build_dfg_fn` - build DFG from function
- `well_formed_dfg` - DFG maps vars to instructions that produce them
- `dfg_ids` - set of instruction IDs in DFG range
- `phi_var_operands`, `assign_var_operand` - PHI/ASSIGN helpers

### dfgOriginsTheory (Origin Computation)
- `get_origins` - compute origin instructions through PHI/ASSIGN chains
- `compute_origins` - wrapper with empty visited set
- `phi_single_origin` - find single origin for PHI elimination
- `phi_operands_direct` - well-formedness for single-origin PHIs
- `phi_operands_direct_flookup` - key lemma for correctness

### stateEquivTheory (State Equivalence Definitions)
- `state_equiv` - states are equivalent (same vars, memory, storage, etc.)
- `var_equiv` - variable-only equivalence
- `result_equiv` - result equivalence (OK states equiv, Halt states equiv, etc.)
- `state_equiv_refl/sym/trans` - equivalence relation properties
- Helper theorems: `eval_operand_state_equiv`, `update_var_state_equiv`, etc.

### execEquivTheory (Execution Equivalence)
- `step_inst_state_equiv` - step_inst preserves state_equiv
- `step_in_block_state_equiv` - step_in_block preserves state_equiv
- `run_block_state_equiv` - run_block preserves state_equiv
- `step_inst_result_equiv` - step_inst preserves result_equiv
- `run_block_result_equiv` - run_block preserves result_equiv

## Debugging Tips

1. **Variable conflicts:** Names like `fn`, `f` conflict with HOL4. Use `func` or type annotations
2. **Pair returns:** Use `Cases_on \`fn args\`>> fs[]` to split
3. **irule not matching:** Try `drule` or `drule_all` for forward reasoning
4. **fs not simplifying:** May need type-specific theorems like `exec_result_distinct`

## Reference Repos

- `vyper-ref/` - Vyper compiler source (reference for Venom IR semantics)
- `verifereum-ref/` - Verifereum EVM formalization (provides word256, memory model)

If these symlinks are missing, ask the operator to provide access.

## Proof Strategy

**When proofs get complex:** Step back, look for helper lemmas, consider refactoring definitions. Use `p()` to debug. Cheats are temporary scaffolding only.

**Signs you're on wrong track:** Many nested TRY blocks, dozens of subgoals, slow tactics, unpredictable variable names (`h''` etc.) → stop and reconsider.

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

## HOL4 Script Style

Use modern syntax for HOL4 script files. Scripts should start with the `Theory` keyword and use `Ancestors` and `Libs` to specify dependencies, rather than using `open` explicitly.

Example:
```sml
Theory myTheory
Ancestors
  parentTheory1 parentTheory2
Libs
  someLib

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

## Session Continuity

- Update `PLAN.md` with progress and remaining work
- Test proofs interactively before committing to the file
- Document any blocking issues and potential approaches
- When interrupted, save detailed debugging state to PLAN.md for session recovery

## Parallel Development Strategy

When builds are slow (>30s), use this parallel workflow:
1. **Start the build in background**: `VFMDIR=/home/ubuntu/verifereum Holmake --qof 2>&1 | tail -50 &`
2. **Simultaneously debug interactively**: Start a HOL session and test proof tactics
3. **Commit progress incrementally**: Don't wait for builds to complete before committing working changes
4. **Benefits**:
   - Build failures don't block interactive exploration
   - Can identify performance issues interactively while build runs
   - Faster iteration on proof tactics
