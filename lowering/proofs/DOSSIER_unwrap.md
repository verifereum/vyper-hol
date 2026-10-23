# DOSSIER: unwrap

PLAN: `lowering/proofs/PLAN_unwrap.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0001 |  |
| C1.2 | progressed | missing_helper | E0002 | Ask strategist for a boundary/grouping refinement of C1.2 before constructing a large consumer proof. |
| C1.2.1 | proved |  | E0003 |  |
| C1.2.2 | progressed | missing_helper | E0004 | Request compact composition interface addition from strategist; loop source not yet edited. |
| C1.2.2.1 | proved |  | E0005 |  |
| C1.2.2.2 | proved |  | E0006 |  |
| C1.3 | proved |  | E0008 |  |
| C1.4 | proved |  | E0009 |  |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0001`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 53 steps, 52 tools, 13 holbuild, 3,389,051 tok (3,384,302 in, 4,749 out, 3,319,168 cached), 629.9s, $0.5096748

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 3 msgs, 53 steps, 52 tools, 13 holbuild, 3,389,051 tok (3,384,302 in, 4,749 out, 3,319,168 cached), 629.9s, $0.5096748)
  - Non-code load by location cases, exclusion of label operands via vacuous precondition; allocation via bind, return and emit_op. -> Both boundary lemmas proved and target builds. BETA_RULE specialization is needed for emit_op's higher-order R; primitive admissibility requires non-label operand syntactically. (`TO_unwrap-20261023T092756Z_m0054_t001`)

### Evidence refs

- `TO_unwrap-20261023T092756Z_m0054_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `progressed`
- diagnosis: `missing_helper`
- latest episode: `E0002`
- blocker: Current loop plan lacks reusable plain-input emission boundary and manageable subproof grouping; direct repetition of C1.1 consequence plumbing at each stage will exceed proof-size guideline.
- actual effort: 1 sessions, 3 steps, 2 tools, 238,099 tok (237,676 in, 423 out, 232,192 cached), 26.9s, $0.0384172
- next: Ask strategist for a boundary/grouping refinement of C1.2 before constructing a large consumer proof.

### Attempts / Evidence

- `E0002` (progressed, missing_helper, actual effort: 1 sessions, 3 steps, 2 tools, 238,099 tok (237,676 in, 423 out, 232,192 cached), 26.9s, $0.0384172)
  - Inspect fixed word-copy sequence and primitive rule interfaces before implementation. -> Sequence contains three fresh labels, counter allocation, and 17 emit/new-block stages. Primitive rules require unconditional instruction admissibility and do not directly match plain-operand preconditions; C1.1 exposed the recurring non-label side condition. No C1.2 source edits yet. (`TO_unwrap-20261023T092756Z_m0062_t001`, `TO_unwrap-20261023T092756Z_m0063_t001`)

### Evidence refs

- `TO_unwrap-20261023T092756Z_m0062_t001` (use `read_tool_output` for exact output)
- `TO_unwrap-20261023T092756Z_m0063_t001` (use `read_tool_output` for exact output)

## C1.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0003`
- blocker: 
- actual effort: 1 sessions, 7 steps, 6 tools, 1 holbuild, 594,924 tok (594,126 in, 798 out, 584,192 cached), 68.9s, $0.0862672

### Attempts / Evidence

- `E0003` (proved, , actual effort: 1 sessions, 7 steps, 6 tools, 1 holbuild, 594,924 tok (594,126 in, 798 out, 584,192 cached), 68.9s, $0.0862672)
  - Unfold shape_step only at boundary; specialize state-conditional admissibility, then drule_all existing emit rule and semantic conclusion. -> Both state-conditioned emission interfaces proved in four tactic lines each; target builds. (`TO_unwrap-20261023T092756Z_m0072_t001`)

### Evidence refs

- `TO_unwrap-20261023T092756Z_m0072_t001` (use `read_tool_output` for exact output)

## C1.2.2

### Current Status

- result: `progressed`
- diagnosis: `missing_helper`
- latest episode: `E0004`
- blocker: Need pure-precondition elimination rule to move compiler_label facts into HOL context for new_block, plus stable framing of load results.
- actual effort: 1 sessions, 4 steps, 3 tools, 362,804 tok (362,277 in, 527 out, 355,584 cached), 39.8s, $0.0542144
- next: Request compact composition interface addition from strategist; loop source not yet edited.

### Attempts / Evidence

- `E0004` (progressed, missing_helper, actual effort: 1 sessions, 4 steps, 3 tools, 362,804 tok (362,277 in, 527 out, 355,584 cached), 39.8s, $0.0542144)
  - Inspect label allocation and new_block composition interfaces before adding loop skeleton. -> fresh_label places compiler_label l in state predicate, whereas new_block requires LP lbl as a theorem outside that predicate. No shape_step pure-precondition elimination rule exists among composition rules. Cannot extract pure label facts with the current interface without unfolding shape_step at consumer level. (`TO_unwrap-20261023T092756Z_m0081_t001`, `TO_unwrap-20261023T092756Z_m0082_t001`)

### Evidence refs

- `TO_unwrap-20261023T092756Z_m0081_t001` (use `read_tool_output` for exact output)
- `TO_unwrap-20261023T092756Z_m0082_t001` (use `read_tool_output` for exact output)

## C1.2.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0005`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 5 steps, 4 tools, 2 holbuild, 483,876 tok (483,466 in, 410 out, 475,904 cached), 52.2s, $0.0668144

### Attempts / Evidence

- `E0005` (proved, , actual effort: 1 sessions, 1 msgs, 5 steps, 4 tools, 2 holbuild, 483,876 tok (483,466 in, 410 out, 475,904 cached), 52.2s, $0.0668144)
  - rw[shape_step_def] followed by small metis discharge -> Pure-precondition rule proved; theory build clean apart from allowed existing cheats. (`TO_unwrap-20261023T092756Z_m0090_t001`)

### Evidence refs

- `TO_unwrap-20261023T092756Z_m0090_t001` (use `read_tool_output` for exact output)

## C1.2.2.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0006`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 37 steps, 36 tools, 15 holbuild, 4,168,865 tok (4,161,106 in, 7,759 out, 4,104,448 cached), 537.3s, $0.6013508

### Attempts / Evidence

- `E0006` (proved, , actual effort: 1 sessions, 2 msgs, 37 steps, 36 tools, 15 holbuild, 4,168,865 tok (4,161,106 in, 7,759 out, 4,104,448 cached), 537.3s, $0.6013508)
  - Compose fixed word-copy program using fresh-label pure-pre elimination, stable emission-under rules, pointer-load frame, and consequence to discard dead operands. Use named Resume blocks at stage boundaries. -> Full storage/transient-to-memory loop shape helper proved, Finalise present, theory builds. ho_match_mp_tac is required for higher-order predicate interfaces; isolated literal/plain and branch-label side conditions discharged by simplification. (`TO_unwrap-20261023T092756Z_m0132_t001`)

### Evidence refs

- `TO_unwrap-20261023T092756Z_m0132_t001` (use `read_tool_output` for exact output)

## C1.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0008`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 30 steps, 29 tools, 9 holbuild, 1,751,427 tok (1,747,810 in, 3,617 out, 1,698,560 cached), 256.6s, $0.3045260

### Attempts / Evidence

- `E0007` (progressed, other, actual effort: 1 sessions, 2 msgs, 19 steps, 18 tools, 2 holbuild, 2,529,019 tok (2,526,691 in, 2,328 out, 2,365,056 cached), 238.2s, $0.5830556)
  - Added ensure-in-memory skeleton with memory return and shared storage/transient suspension; began framed buffer allocation. -> Latest checked failure is shared suspension connective requiring markerLib.RESUME_TAC (not unqualified RESUME_TAC). Qualified it but not yet rebuilt. In-progress rename ptr to src_ptr is incomplete: line 562 still uses ptr and must be repaired first. slot_copy/calldata remain FAIL_TAC probes, not cheats. (`TO_unwrap-20261023T092756Z_m0149_t001`, `TO_unwrap-20261023T092756Z_m0150_t001`, `TO_unwrap-20261023T092756Z_m0156_t001`)
- `E0008` (proved, , actual effort: 1 sessions, 2 msgs, 30 steps, 29 tools, 9 holbuild, 1,751,427 tok (1,747,810 in, 3,617 out, 1,698,560 cached), 256.6s, $0.3045260)
  - Finish shared storage/transient allocation and copy branches, and calldata fixed load/allocation/store/add/add/copy composition using suspended stages. -> compile_ensure_in_memory_shape finalised and target theory builds; all helper obligations checked without new cheats. (`TO_unwrap-20261023T092756Z_m0189_t001`)

### Evidence refs

- `TO_unwrap-20261023T092756Z_m0189_t001` (use `read_tool_output` for exact output)

## C1.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0009`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 31 steps, 30 tools, 3 holbuild, 2,375,297 tok (2,373,131 in, 2,166 out, 2,335,872 cached), 236.8s, $0.3297652

### Attempts / Evidence

- `E0009` (proved, , actual effort: 1 sessions, 2 msgs, 31 steps, 30 tools, 3 holbuild, 2,375,297 tok (2,373,131 in, 2,166 out, 2,335,872 cached), 236.8s, $0.3297652)
  - Value case split, exclude LocCode from precondition, weaken to plain pointer and dispatch to load/ensure boundaries. -> Exact frozen unwrap_value_shape proved; target build clean. Temporary ML oracle-tag audit passed and was removed. Task diff changes only new helper block and target cheat; exempt cheats untouched. (`TO_unwrap-20261023T092756Z_m0202_t001`, `TO_unwrap-20261023T092756Z_m0223_t001`, `TO_unwrap-20261023T092756Z_m0226_t001`)

### Evidence refs

- `TO_unwrap-20261023T092756Z_m0202_t001` (use `read_tool_output` for exact output)
- `TO_unwrap-20261023T092756Z_m0223_t001` (use `read_tool_output` for exact output)
- `TO_unwrap-20261023T092756Z_m0226_t001` (use `read_tool_output` for exact output)
