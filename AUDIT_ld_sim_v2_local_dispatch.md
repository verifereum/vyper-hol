# Local transition interface audit (C1.4.4)

This is a source/signature audit, NOT a proof of the aggregate preservation
statement or of `lower_dload_stage_sim`. Checked after commit 053cf779d.

## Execution contract and dispatch (read in execution order)

* `venomExecSemanticsScript.sml:1663-1723` defines the mutual runner.
  `step_inst` handles INVOKE by decoding, looking up, evaluating arguments,
  setting up a callee, and calling `run_blocks fuel`. An IntRet is merged and
  bound into the caller; Halt/Abort propagate; Error propagates; callee OK is
  an Error. For every other opcode it is exactly `step_inst_base`.
* `exec_block` fetches at the current index. Missing instruction is Error
  "block not terminated". A nonterminator OK result recurses after setting
  the index to SUC of the OLD index. A terminator OK result returns OK unless
  halted, in which case it returns Halt. IntRet/Halt/Abort/Error propagate.
  Instruction recursion does not decrement fuel.
* `run_blocks 0` is Error. At SUC fuel it looks up the block, evaluates PHIs
  in parallel, executes from `phi_prefix_length`, and recurs on an unhalted
  OK result using the predecessor fuel. Missing block/failed PHI is Error.
* `run_function` sets entry label/index; `run_context` finds entry function
  and resets previous block. Missing entry is Error.
* `ctx_sim_def` (o1PassContract:145) quantifies only source runs satisfying
  `terminates`; this means **anything except Error**, not just Halt/Abort
  (passSimulationDefs:96). `dead_result_rel_def` (ptrDiscipline:823) accepts
  only Halt/Halt and Abort/Abort. Thus top-level OK and IntRet must be
  excluded, NOT ignored. IntRet is excluded structurally by
  `entry_fn_no_return` in `o1_fn_shape`; a theorem lifting that exclusion
  through calls/run_blocks is still an integration obligation. run_blocks
  has no direct OK-return clause: it recurs on unhalted OK and turns halted
  OK into Halt, so a small result-shape theorem can exclude top-level OK.
* Errors (bad operand arity, undefined operand, invalid labels/index,
  missing fetch, fall-through, malformed INVOKE, out of fuel) need NO target
  matching under ctx_sim. The proof must use the source terminating run
  to rule out the encountered Error branch, not posit global totality.

## Common boundary convention

Abbreviations in this REPORT ONLY:
`J(s,t;Gamma)` means the existing `ld_joint_boundary vs C C' lo D stk PG G tn
fn inst s t n a U B HP H sites X ts`; Gamma denotes these ghost arguments.
`N(s1)` means `s1 with vs_inst_idx := SUC s.vs_inst_idx`.
Most ordinary `_next` lemmas require:

* J, o1_ctx_shape C, active_inst fn inst s;
* ptr_discipline lo C vs and opaque_use_ok fn for operand-sensitive cases;
* source `step_inst fuel C inst s = OK s1` and
  `active_inst fn inst2 N(s1)`.

They produce actual target `step_inst fuel C' inst t = OK t1`, a target
function lookup, `ld_joint_control u fn fn' s t`, `active_inst fn' inst t`,
and J at `N(s1)` and `t1 with vs_inst_idx := SUC t.vs_inst_idx`.
The next ghost arguments are PG unchanged, G=`step_prov PG G inst s1`,
tn=`step_taint inst s s1 tn`, H=`occurrence_step a HP H inst s1`;
other ghosts unchanged unless the row below says otherwise. These are
WHOLE boundaries (including source reachability, annotations, saved
frames, geometry, memory and shared state), not merely value kernels.
The runner, not step_inst, performs the PC increments.

Actual fetch is NOT active_inst. The latter selects a member block; with
duplicate labels it does not imply lookup_block. Under source shape,
labels are distinct; target fetch must still be connected to lookup and
get_instruction. Final HaltResult instead explicitly requires actual
source fetch in addition to active_inst. This is intentional.

## Opcode coverage matrix

All opcode constructors in venomInst:23-69 are partitioned below. File
names are under venom/compiler/; theorem prefix `ld_joint_` is omitted in
rows where unambiguous. `next` means the WHOLE common boundary above.

| Opcode(s) | Existing interface / file | Consumer conditions or remaining assembly |
|---|---|---|
| ADD SUB | arithmetic_next / JointArithmetic | Common next; affine relocation and taint handled inside |
| MUL Div SDIV Mod SMOD Exp SLT SGT AND OR XOR | binary_next / JointScalar | Common next; clean nonpointer operands |
| ADDMOD MULMOD | ternary_next / JointTernary | Common next |
| ISZERO NOT | unary_next / JointScalar | Common next |
| EQ LT GT | compare_next / JointCompare | Common next; positive-size compared-pointer access discipline inside |
| SHL SHR SAR | shift_next / JointShift | Common next |
| SIGNEXTEND BYTE OFFSET INITIAL_FMP | residual_scalar_next / JointResidualScalar | Common next; INITIAL_FMP is covered even if static source restrictions exclude it |
| CALLER ADDRESS CALLVALUE GAS ORIGIN GASPRICE CHAINID COINBASE TIMESTAMP NUMBER PREVRANDAO GASLIMIT BASEFEE BLOBBASEFEE CALLDATASIZE CODESIZE RETURNDATASIZE SELFBALANCE | read0_next / JointRead0 | Common next; shared/local projections give equal results (GAS consumes equal oracle) |
| BLOCKHASH BLOBHASH BALANCE EXTCODESIZE EXTCODEHASH CALLDATALOAD | read1_next / JointRead1 | Common next; exact opcode list in theorem |
| PARAM | param_next / JointParam | Whole next; source shape and success determine operand/output form |
| RETPC_PARAM | retpc_next / JointRetpc | Whole next; opaque availability, not equal numeric retpc required |
| ASSIGN | assign_next / JointAssign | Whole next including opaque self-assignment |
| BUMP | bump_next / JointBump | Whole next |
| NOP ASSERT ASSERT_UNREACHABLE | identity_next / JointIdentity | Whole next for OK; assert_abort handles abort separately |
| ALLOCA fresh | alloca_fresh_next / FreshNext:41 | Requires [Lit amount], [out], source id membership, source lookup NONE; headroom mem_inv and callee_first. Updates B via occurrence_sites_step and sites with ((a,id),(source frontier,target frontier,w2n amount)); all other ghosts as common next |
| ALLOCA repeated | alloca_repeated_next / RepeatedNext:35 | Requires literal/output shape and source lookup SOME(b,z); sites/B unchanged. Target allocation remains idempotent |
| MLOAD | mload_next / JointMemoryRead | Whole next; source-indexed masked memory and relocated read |
| MSTORE | mstore_next / JointMemoryWrite | Whole next; masked memory/taint rebuilt |
| MSTORE8 CALLDATACOPY CODECOPY RETURNDATACOPY EXTCODECOPY | clean_write_next / JointCleanWrite | Whole next under ~in_revert_forward; range destination/taint handled inside; failing RETURNDATACOPY has ordinary_abort |
| MCOPY | mcopy_next / JointRangeCopy | Whole next under ~in_revert_forward; both addresses relocated |
| ILOAD SHA3 | range_read_next / JointRangeRead | Whole next under ~in_revert_forward; SHA3 length uses shared general scalar interface |
| SLOAD TLOAD | storage_load_next / JointStorageRead | Whole next |
| SSTORE TSTORE | storage_store_next / JointStorageWrite | Whole next; shared taint update |
| ISTORE LOG | internal_effect_next / JointInternalEffects | Whole next under nonforward restriction; logs include relocated clean memory observations |
| CALL STATICCALL | call_next / JointExternal:857 | Whole next; additionally o1_src_inv D C vs and nonforward. Shared concrete/oracle effects inside, not assumed equal poststate |
| DELEGATECALL | delegatecall_next / JointExternal:283 | Whole next; nonforward, source successful concrete EVM execution |
| CREATE CREATE2 | create_next / JointExternal:519 | Whole next; nonforward; ordinary_abort for size failure |
| DLOADBYTES | dloadbytes_next / SuppliedSegmentNext:40 | Actual TWO step equations plus target block lookup/slice and WHOLE boundary at target index+2. Requires o1_run_state_ok, offset mem_inv, ptr discipline, opaque, nonforward; chooses source next instruction internally. No allocation metadata change |
| DLOAD | dload_next / SuppliedSegmentNext:178 | Actual FOUR step equations plus slice and WHOLE boundary at target index+4. Also headroom mem_inv and callee_first. X extended by generated scratch allocation on first visit, unchanged on repeated visit; n/a/U/B/sites unchanged |
| JMP JNZ DJMP | branch_entry / PhiEntry:93 | WHOLE post-PHI boundary, BUT ASSUMES target step OK, equal branch destination/prev_bb, source not halted, source enters_block and active next. Does NOT construct target branch execution. See gap B below |
| PHI | ld_env_eval_phis / Phi; ld_env_enters_block and branch_entry / PhiEntry | Parallel prefix evaluation, G/H=entry_prov, tn=entry_taint_vars. Not an ordinary executable body step. Need use wf/entry decomposition to exclude PHI body branch |
| INVOKE | boundary_call_invariant / InvokeArguments:58 | Constructs target arguments/setup/entry WHOLE boundary. Requires both callee lookups, covering supply+translation, callee distinct labels, source setup and source successful entry/active instruction. Pushes source frame and occurrence frame, saves target t, fresh owner n, counter SUC n; PG/HP from operand provenance, G/H empty, variable taint empty. It does NOT construct completed target run_blocks or step_inst INVOKE |
| RET | ret_step / JointReturn:36; boundary_return / JointReturnBoundary:10 | ret_step produces IntRet with equal iret_values and both adopt_fmp NONE; source endpoint unchanged. boundary_return merges current shared effects, binds outputs and produces WHOLE restored caller next boundary, removes current owner from B/sites/X, pops frames, restricts caller G/H and t_var on outputs. Requires source bind success, active caller next, saved call active INVOKE, caller labels distinct and current/saved caller cc_address equal. Completed target callee run/INVOKE equation still belongs to execution lifting |
| STOP SINK RETURN SELFDESTRUCT | halt_result / HaltResult:235 | Actual target Halt and dead_result_rel, no successor J required. Requires taint_within, ptr discipline, opaque, active AND actual source lookup/fetch, non-INVOKE. RETURN nonforward derived from actual fetch; slice may relocate. SELFDESTRUCT actual account changes preserved |
| REVERT | revert_result / AbortResult:24 | Actual target same-reason Abort and dead_result_rel; only J, active, source Abort; payload equality unnecessary |
| INVALID | step_inst_base INVALID clause (:1067) | Direct unconditional ExHalt_abort. No named joint wrapper; mechanical semantic dispatcher case, not missing invariant |
| MEMTOP DRET GETFMP SETFMP RETFMP FMP_PARAM | fn_ptr_ok_def :120-126 | Forbidden by ptr_discipline's EVERY fn_ptr_ok; must derive active instruction membership before contradiction. DRET also excluded by o1_fn_shape |
| DALLOCA | o1_src_inv_def :540 and ctx_has_dalloca_def | Forbidden globally; do not attempt preservation of dynamic allocation |

### Forward corridor and exceptional cases

`ld_joint_forward_abort_result` (AbortResult:8) consumes a J at a
RETURNDATACOPY in_revert_forward and the ACTUAL source exec_block Abort.
It returns actual target exec_block Abort at looked-up transformed block,
with the same reason and dead_result_rel. This is a whole suffix result;
no memory relation is demanded after the exempt copy. All other
nonforward restrictions can be discharged using actual fetch and
`revert_forward_at_opcode` except REVERT (handled directly).
`ld_joint_assert_abort` produces matching Abort for assertions.
`ld_joint_ordinary_abort` covers RETURNDATACOPY/CREATE/CREATE2 failures.
INVALID is direct. INVOKE terminal propagation requires the recursive
callee execution conclusion, not any of these local next lemmas.

## Premise provenance / important integration gaps

A. Ordinary next dispatcher not yet stated/proved. The common next signatures
match even for memory/external effects; there is no reason to redo their
memory kernels. But the dispatcher must derive successor active instruction.
`ld_nonterminator_successor` (Readiness:30) requires wf_function, active source,
nonterminator and unchanged current_bb; `ld_alloca_successor_active` specializes
this. Do not assume a successor in a theorem intended to cover a malformed
fall-through without first using wf or the source successful suffix.
Fresh ALLOCA literal/output shape and id membership come from fn_inst_wf,
active membership and successful ALLOCA inversion, not J alone.
Opaque use comes from fn_shape_ok; static exclusions from fn_ptr_ok and
~ctx_has_dalloca. Need compact eliminators/assembly, not more value helpers.

B. Branch actual execution construction is absent from PhiEntry signatures.
`ld_env_branch_transport` explicitly assumes BOTH source and target step.
Candidate missing boundary (usual J arguments expanded at implementation):
```
J /\ ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
MEM inst.inst_opcode [JMP;JNZ;DJMP] /\ step_inst fuel C inst s = OK s1
==> ?t1. step_inst fuel' C' inst t = OK t1 /\
    s1.vs_current_bb = t1.vs_current_bb /\
    s1.vs_prev_bb = t1.vs_prev_bb /\ ~s1.vs_halted
```
Check the not-halted conclusion against source halted flag; safest premise
`~s.vs_halted` may be needed, since J records only equality of halted flags.
Existing branch_entry already takes ~s1.vs_halted. Prefer proving the
execution/equal-control conclusion alone and retaining its existing halted
premise. J's environment/clean operands and equal labels should supply
branch condition/index equality. No such named construction was found by
grep of current compiler LowerDload theories.

C. Segment-to-runner composition: DLOAD and DLOADBYTES next theorems give
step equations at unincremented intermediate states; runner fetch increments
PC at each instruction. Need checked congruence (instruction semantics ignores
PC for these generated opcodes) plus fetch slice to chain exec_block. Their
current conclusions are not themselves exec_block equations. Candidate
continuation theorem: given each segment's lookup/slice and step equations,
and a continuation exec_block result from its endpoint, conclude the same
result from exec_block at its start. Instantiate lengths 2/4 without
re-proving data transport. Existing ForwardAbort contains fetch/suffix
composition facts but no generic proved segment continuation was found in
SuppliedSegmentExec (only exact local microsteps).

D. Calls/returns: boundary_call_invariant supplies the fresh callee relation;
boundary_return supplies restoration only after a related callee RET endpoint.
The saved relation stores caller control and shared-state-independent locals,
not the active_call premise or address equality as explicit clauses. Source
occurrence reachability/call history must supply them. Return proof must carry
call-entry address equality through callee steps. Callee-first names supplies
headroom bound, not a target run. Need recursive execution theorem with both
Halt/Abort and IntRet-return modes, then fuel monotonicity to reconcile target
callee and subsequent block budgets. Do not assume a target run exists in a
call-preservation premise.

E. Root/entry/termination integration: JointEntry:112 gives initial J only
after actual successful source enters_block and active inst, plus paired
function/supply lookups. Need exclude successful no-active entry using wf
terminated nonempty block/PHI-prefix facts. Prove top-level result-shape
exclusions noted above. Source success excludes missing fetch and PHI failure.

## Proposed aggregate interface (smallest next obligation)

Use existing relations, NO new definition. First assemble the ordinary
nonterminator dispatcher, NOT a falsely uniform single-step INVOKE theorem:
```
ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
  n a U B HP H sites X ts /\
o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs /\
callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
opaque_use_ok fn /\ active_inst fn inst s /\
(?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst) /\
~is_terminator inst.inst_opcode /\
~MEM inst.inst_opcode [INVOKE;DLOAD;DLOADBYTES;ALLOCA] /\
~in_revert_forward fn s /\ step_inst fuel C inst s = OK s1
==> ?inst2 t1 u fn'.
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_inst fuel C' inst t = OK t1 /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
  ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
    (step_taint inst s s1 tn) fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)
    (t1 with vs_inst_idx := SUC t.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst s1) sites X ts
```
This is explicitly only the unchanged one-instruction case. Then add
ALLOCA split and two expansion continuations; branch construction feeds
existing branch_entry. A run theorem can dispatch on those boundaries,
source exec_block result and recursive callee result, rather than unfold J.
The eventual block conclusion must be actual target exec_block at some fuel,
not just a list of semantic equations. Internal-return conclusions must
retain a full return endpoint J for boundary_return, not dead_result_rel
(which is false for IntRet).

## Readiness verdict and certification

NOT ready for a monolithic execution induction. Ordinary value/memory and
terminal boundaries now largely align, but B (actual branch construction)
and C (PC-correct segment continuation) are explicit local gaps. A is a
bounded dispatcher assembly proposal; D/E are run-lifting obligations,
not authorization to add circular premises. No theorem falsehood was
established by this audit.

Build: TO_ld_sim_v2-20261104T173029Z_m6337_t001, target
`o1ContractLowerDloadSimTheory`, success/up-to-date. Earlier rebuild after
HaltResult import: TO_ld_sim_v2-20261104T173029Z_m6274_t001.
IMPORTANT: target success is not cheat-free certification. Source still
contains the frozen theorem's `cheat` at Sim:137 (grep evidence
TO_ld_sim_v2-20261104T173029Z_m6338_t001); no completion claim is made.
