# DOSSIER: dft_step

PLAN: `PLAN_dft_step.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0001 |  |
| C1.2 | proved |  | E0003 |  |
| C1.3 | proved |  | E0005 |  |
| C1.4 | proved |  | E0007 |  |
| C1.5 | proved |  | E0008 |  |
| C1.6 | proved |  | E0010 |  |
| C1.7 | proved |  | E0011 |  |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0001`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 6 holbuild, 1,180,434 tok (1,178,583 in, 1,851 out, 1,141,120 cached), 1320.4s, $0.2075480

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 6 holbuild, 1,180,434 tok (1,178,583 in, 1,851 out, 1,141,120 cached), 1320.4s, $0.2075480)
  - Induct on fuel using dfs_step_measure_dec and good-state preservation; specialize to scheduler initial state using filter-length bounds. -> Both non-SSA stack termination boundaries build cleanly. entry_instructions_length is local to completeness, so its short filter bound was used inline. Polynomial bound uses rewrite_tac then decide_tac to avoid simp EXP_2 looping. (`TO_dft_step-20261102T060309Z_m0022_t001`)

### Evidence refs

- `TO_dft_step-20261102T060309Z_m0022_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0003`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 27 steps, 26 tools, 9 holbuild, 2,373,064 tok (2,370,738 in, 2,326 out, 2,335,232 cached), 2313.3s, $0.3277952

### Attempts / Evidence

- `E0002` (progressed, tool_limit, actual effort: 1 sessions, 2 msgs, 24 steps, 23 tools, 9 holbuild, 1,720,708 tok (1,718,209 in, 2,499 out, 1,611,264 cached), 7166.3s, $0.4000064)
  - Define emit-accounting invariant with ALL_DISTINCT of output ids ++ stack_emit_ids; prove initialization and dfs_step preservation. -> Build clean through dfs_step_preserves_emit_accounting. Added FUNPOW lift and schedule-output corollary subsequently, but those remain unverified because scheduler allocation unavailable. (`TO_dft_step-20261102T060309Z_m0047_t001`)
  - Build extended helper theory with 1800s then maximum 3600s wall-clock limits. -> Both calls spent entire time queued in srun, with no resource allocation or HOL execution. Latest source suffix unverified. (`TO_dft_step-20261102T060309Z_m0050_t001`, `TO_dft_step-20261102T060309Z_m0051_t001`)
- `E0003` (proved, , actual effort: 1 sessions, 2 msgs, 27 steps, 26 tools, 9 holbuild, 2,373,064 tok (2,370,738 in, 2,326 out, 2,335,232 cached), 2313.3s, $0.3277952)
  - Lift emitted/pending-id accounting over FUNPOW, derive unconditional schedule distinctness, combine with existing non-pseudo provenance to establish dft_block distinct ids. -> dftNonSsaTheory builds cleanly. Non-pseudo output already supplied by schedule_output_from_block; no duplicate lemma added. Prefix id distinctness is proved by short inline list induction; disjointness follows from input id uniqueness and non-pseudo provenance. (`TO_dft_step-20261102T123913Z_m0081_t001`)

### Evidence refs

- `TO_dft_step-20261102T123913Z_m0081_t001` (use `read_tool_output` for exact output)

## C1.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0005`
- blocker: 
- actual effort: 1 sessions, 4 msgs, 50 steps, 49 tools, 15 holbuild, 3,178,967 tok (3,175,496 in, 3,471 out, 3,107,072 cached), 1167.6s, $0.4822652

### Attempts / Evidence

- `E0004` (progressed, other, actual effort: 1 sessions, 6 msgs, 72 steps, 71 tools, 21 holbuild, 8,634,794 tok (8,626,149 in, 8,645 out, 8,391,680 cached), 2879.9s, $1.3945560)
  - Prove data_dep_has_output, last_not_dependency, entry_instructions_last, entry_initial_bottom, schedule_last_id using existing bottom_inv and C1.1 stack completion. -> All five boundaries are build-verified through schedule_last_id. This confirms the planned non-SSA terminator scheduling argument and reuses the existing bottom invariant. (`TO_dft_step-20261102T123913Z_m0144_t001`)
  - Lift scheduled final id to exact final instruction in dft_block_last with nonflippable terminator and provenance. -> Unfinished consumer skeleton. Currently times out in local terminator-fields subgoal because inst_wf_def is expanded across the whole context (including EVERY inst_wf). Second attempt used is_terminator_def as though it were a disjunction, but it is constructor equations, so no split occurred. Resume exact_last still contains FAIL_TAC probe; downstream provenance application not yet verified. (`TO_dft_step-20261102T123913Z_m0155_t001`, `TO_dft_step-20261102T123913Z_m0159_t001`)
- `E0005` (proved, , actual effort: 1 sessions, 4 msgs, 50 steps, 49 tools, 15 holbuild, 3,178,967 tok (3,175,496 in, 3,471 out, 3,107,072 cached), 1167.6s, $0.4822652)
  - Use no-output terminator, backward EDA, entry tail, existing bottom_inv and empty-stack completion to derive schedule_last_id; lift by source-id injectivity to dft_block_last and bb_succs equality. -> All boundaries and Finalise dft_block_last compile cleanly. Terminator constructor subproof required context pruning and simplification of is_terminator before inst_wf; reused dftCorrectness.all_distinct_map_mem_inj for exact identity. (`TO_dft_step-20261102T123913Z_m0205_t001`, `TO_dft_step-20261102T123913Z_m0212_t001`)

### Evidence refs

- `TO_dft_step-20261102T123913Z_m0212_t001` (use `read_tool_output` for exact output)

## C1.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0007`
- blocker: 
- actual effort: 1 sessions, 6 msgs, 82 steps, 81 tools, 26 holbuild, 8,894,599 tok (8,884,411 in, 10,188 out, 8,767,616 cached), 1593.4s, $1.2122316

### Attempts / Evidence

- `E0006` (progressed, other, actual effort: 1 sessions, 3 msgs, 46 steps, 45 tools, 15 holbuild, 4,538,358 tok (4,534,002 in, 4,356 out, 4,459,136 cached), 700.9s, $0.6392056)
  - Establish pure-instruction EDA lookup by fold invariant and uniqueness; bound ADD [op; Label lbl] data deps by one; show sorting short child lists is identity. -> Clean dftNonSsaTheory build through add_label_children_sorted. The exceptional label ADD cannot flip, independent of SSA. Generic shape transport and guarded flip/inst_wf boundaries remain. (`TO_dft_step-20261102T123913Z_m0261_t001`)
- `E0007` (proved, , actual effort: 1 sessions, 6 msgs, 82 steps, 81 tools, 26 holbuild, 8,894,599 tok (8,884,411 in, 10,188 out, 8,767,616 cached), 1593.4s, $1.2122316)
  - Prove pure ADD child-list sorting identity, generic dfs_pred_state initialization/step/FUNPOW and schedule/dft_block predicate transport. -> Generic guarded-flip boundary dft_block_pred compiles; code_end ADD never flips without SSA. (`TO_dft_step-20261102T123913Z_m0269_t001`)
  - Finite opcode/operand guarded flip shape and inst_wf boundaries in dftShape; derive dft_block_inst_wf and dft_block_inst_shape; export pseudo-inclusive instruction source, operand membership, and exact special-opcode source. -> dftShapeTheory clean. inst_shape transport needs only distinct ids, inst_wf transport needs no distinctness. special source handles ASSIGN/PHI/GAS/RETPC_PARAM/INVOKE/CALL/STATICCALL/RET/RETFMP/DRET/PARAM/FMP_PARAM/STOP/RETURN; existing flip id/output lemmas are reused. (`TO_dft_step-20261102T123913Z_m0300_t001`)

### Evidence refs

- `TO_dft_step-20261102T123913Z_m0300_t001` (use `read_tool_output` for exact output)

## C1.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0008`
- blocker: 
- actual effort: 1 sessions, 8 msgs, 111 steps, 110 tools, 34 holbuild, 9,493,448 tok (9,479,298 in, 14,150 out, 9,329,024 cached), 2594.6s, $1.3749504

### Attempts / Evidence

- `E0008` (proved, , actual effort: 1 sessions, 8 msgs, 111 steps, 110 tools, 34 holbuild, 9,493,448 tok (9,479,298 in, 14,150 out, 9,329,024 cached), 2594.6s, $1.3749504)
  - Prove non-SSA PHI prefix and unique terminator position using dft_block_last, distinct ids and instruction provenance; package dft_block_rel with pseudo-filter equality and nonpseudo from_block. -> All block boundaries build. Avoided inaccessible private dftCorrectness lemmas by using public instruction source and inline finite flip analysis. (`TO_dft_step-20261102T123913Z_m0350_t001`, `TO_dft_step-20261102T123913Z_m0356_t001`)
  - Lift LIST_REL dft_block_rel through label lookup/replacement, dft_process_one, dft_loop_step and FUNPOW once; derive wf_function, fn_inst_wf, inst_shape and instruction-id inclusion. -> New dftLiftingTheory builds cleanly, with dft_fn_block_rel and all requested function exports; no cheats added. (`TO_dft_step-20261102T123913Z_m0403_t001`, `TO_dft_step-20261102T123913Z_m0417_t001`, `TO_dft_step-20261102T123913Z_m0424_t001`)

### Evidence refs

- `TO_dft_step-20261102T123913Z_m0424_t001` (use `read_tool_output` for exact output)

## C1.6

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0010`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 41 steps, 40 tools, 12 holbuild, 2,681,278 tok (2,677,184 in, 4,094 out, 2,614,144 cached), 619.7s, $0.4284344

### Attempts / Evidence

- `E0009` (progressed, other, actual effort: 1 sessions, 3 msgs, 26 steps, 25 tools, 6 holbuild, 3,370,651 tok (3,366,280 in, 4,371 out, 3,187,200 cached), 1030.3s, $0.7205900)
  - Add global instruction/special-source boundaries, generic copy_phi_var_mono by rule induction, GAS/RETPC closure transport, and opaque_use_ok preservation. -> All these helpers build, as does dft_shape_first_rel. Current uncommitted compiler file has these verified helpers followed by an unfinished first-PHI proof; frozen final cheat remains untouched. (`TO_dft_step-20261102T123913Z_m0447_t001`, `TO_dft_step-20261102T123913Z_m0452_t001`)
  - Use related first blocks' equal pseudo filters to preserve no PHI in the first block. -> Routine variable naming bug: live instruction is i, but proof refers to free e. Failure is at line109 proving pseudo-filter membership of e from facts about i. Rename live i to e after rpt strip_tac or replace e by i consistently. No mathematical/interface blocker. (`TO_dft_step-20261102T123913Z_m0452_t001`, `TO_dft_step-20261102T123913Z_m0455_t001`)
- `E0010` (proved, , actual effort: 1 sessions, 3 msgs, 41 steps, 40 tools, 12 holbuild, 2,681,278 tok (2,677,184 in, 4,094 out, 2,614,144 cached), 619.7s, $0.4284344)
  - Complete first-block PHI/predecessor preservation; transport fn_shape_ok, invocation, label references and opcode exclusions; assemble dft_shape_o1_fn. -> All C1.6 helpers and complete O1 function-shape transport build. Frozen final contract remains original cheat for C1.7. (`TO_dft_step-20261102T123913Z_m0499_t001`)

### Evidence refs

- `TO_dft_step-20261102T123913Z_m0499_t001` (use `read_tool_output` for exact output)

## C1.7

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0011`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 32 steps, 31 tools, 3 holbuild, 2,717,436 tok (2,715,015 in, 2,421 out, 2,675,200 cached), 565.3s, $0.3713600

### Attempts / Evidence

- `E0011` (proved, , actual effort: 1 sessions, 2 msgs, 32 steps, 31 tools, 3 holbuild, 2,717,436 tok (2,715,015 in, 2,421 out, 2,675,200 cached), 565.3s, $0.3713600)
  - Unfold dispatcher and step contract, extract input membership and shape via lookup_unique_function_member, apply shape transport and id inclusion. -> Frozen dft_step_contract proved as-is. Final build of target and all three added helper theories succeeds without cheat warnings. (`TO_dft_step-20261102T123913Z_m0537_t001`)
  - Audit task changes and generated proof tags. -> Only compiler proof and three helper theories changed from task baseline. No cheats/new axioms/hh in task files; generated .dat proof tags are DISK_THM only. This build environment has no generated Theory.txt index, so used exported .sig and serialized .dat audit. Helpers distinguish non-SSA deletion/guarded-flip properties from existing SSA permutation lemmas. (`TO_dft_step-20261102T123913Z_m0515_t001`, `TO_dft_step-20261102T123913Z_m0523_t001`, `TO_dft_step-20261102T123913Z_m0532_t001`, `TO_dft_step-20261102T123913Z_m0533_t001`, `TO_dft_step-20261102T123913Z_m0534_t001`, `TO_dft_step-20261102T123913Z_m0535_t001`)

### Evidence refs

- `TO_dft_step-20261102T123913Z_m0537_t001` (use `read_tool_output` for exact output)
- `TO_dft_step-20261102T123913Z_m0532_t001` (use `read_tool_output` for exact output)
