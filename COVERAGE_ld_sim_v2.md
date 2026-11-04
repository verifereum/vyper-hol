# C1.4.1.10 ordinary-step coverage ledger

Read-only semantic audit, 2026-11-04. No new HOL theorem or definition.
Build baseline: TO_ld_sim_v2-20261104T112406Z_m2847_t001 (Arithmetic and Sim).
This is NOT a proof of ordinary-step preservation or of the frozen theorem.

## Sources and exact signature convention

All dispatcher references below mean venom/defs/venomExecSemanticsScript.sml.
All joint theory references mean venom/compiler/o1LowerDload<Name>Script.sml.
The complete dispatcher is lines 559–1125; `is_terminator_def` is in
venom/defs/venomInstScript.sml:346–366. In particular external calls and
assertions are ordinary opcodes, not terminators.

To give full signatures without repeatedly copying the large argument lists,
use the following TEXTUAL abbreviations (not new HOL definitions):

```
J = ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
      n a U B HP H sites X ts
A = active_inst fn inst s
S = step_inst fuel C inst s = OK s1
N = active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Q = o1_ctx_shape C
P = ptr_discipline lo C vs /\ opaque_use_ok fn
R = ~in_revert_forward fn s
G1 = step_prov PG G inst s1
H1 = occurrence_step a HP H inst s1
T1 = step_taint inst s s1 tn

NEXT = ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
  ld_joint_boundary vs C C' lo D stk PG G1 T1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)
    (t1 with vs_inst_idx := SUC t.vs_inst_idx)
    n a U B HP H1 sites X ts
```

Every NEXT result preserves the WHOLE boundary, not only values: source
reachability/annotation, erasure, geometry, active frame and saved frames,
source-taint-indexed memory, shared observations, and returndata. Owner,
sites and scratch map are unchanged unless explicitly stated below. These
results require N: they are not block-exit, PHI-entry, or whole-run results.

## Existing full successors: full signatures via the schema above

| Opcodes | Existing theorem, source | Exact antecedent implying NEXT |
|---|---|---|
| ASSIGN | `ld_joint_assign_next`, JointAssign:213–226 | J /\ Q /\ A /\ opcode=ASSIGN /\ S /\ N |
| PARAM | `ld_joint_param_next`, JointParam:47–60 | J /\ Q /\ A /\ opcode=PARAM /\ S /\ N |
| ISZERO, NOT | `ld_joint_unary_next`, JointScalar:196–210 | J /\ Q /\ P /\ A /\ MEM opcode [ISZERO; NOT] /\ S /\ N |
| MUL, Div, Mod, SDIV, SMOD, Exp, SLT, SGT, AND, OR, XOR | `ld_joint_binary_next`, JointScalar:273–288 | J /\ Q /\ P /\ A /\ MEM opcode [MUL; Div; Mod; SDIV; SMOD; Exp; SLT; SGT; AND; OR; XOR] /\ S /\ N |
| SHL, SHR, SAR | `ld_joint_shift_next`, JointShift:98–112 | J /\ Q /\ P /\ A /\ MEM opcode [SHL; SHR; SAR] /\ S /\ N |
| ADDMOD, MULMOD | `ld_joint_ternary_next`, JointTernary:52–66 | J /\ Q /\ P /\ A /\ MEM opcode [ADDMOD; MULMOD] /\ S /\ N |
| ADD, SUB | `ld_joint_arithmetic_next`, JointArithmetic:157–171 | J /\ Q /\ P /\ A /\ MEM opcode [ADD; SUB] /\ S /\ N |
| SLOAD, TLOAD | `ld_joint_storage_load_next`, JointStorageRead:70–84 | J /\ P /\ Q /\ A /\ R /\ MEM opcode [SLOAD; TLOAD] /\ S /\ N |
| SSTORE, TSTORE | `ld_joint_storage_store_next`, JointStorageWrite:164–178 | J /\ P /\ Q /\ A /\ R /\ MEM opcode [SSTORE; TSTORE] /\ S /\ N |
| MLOAD | `ld_joint_mload_next`, JointMemoryRead:150–164 | J /\ Q /\ P /\ A /\ opcode=MLOAD /\ R /\ S /\ N |
| MSTORE | `ld_joint_mstore_next`, JointMemoryWrite:236–250 | J /\ Q /\ P /\ A /\ opcode=MSTORE /\ R /\ S /\ N |
| ALLOCA, repeated | `ld_joint_alloca_repeated_next`, RepeatedNext:35–50 | J /\ Q /\ A /\ opcode=ALLOCA /\ operands=[Lit amount] /\ outputs=[out] /\ FLOOKUP s.vs_allocas inst.inst_id=SOME(b,z) /\ S /\ N |
| ALLOCA, fresh | `ld_joint_alloca_fresh_next`, FreshNext:41–59 | J /\ Q /\ mem_inv dload_headroom_ok C vs /\ callee_first names C.ctx_functions /\ A /\ opcode=ALLOCA /\ operands=[Lit amount] /\ outputs=[out] /\ MEM inst.inst_id (fn_ir_inst_ids fn) /\ FLOOKUP s.vs_allocas inst.inst_id=NONE /\ S /\ N |

Fresh ALLOCA conclusion differs from NEXT exactly at B and sites: B becomes
`occurrence_sites_step a B inst s1`, and sites becomes
`sites |+ ((a,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n amount))`.
X remains unchanged. Freshness changes frontiers and masks newly allocated
source bytes; it does not initialize them. Repeated allocation only updates
an output variable. This is not DLOAD scratch allocation preservation.

## Residual exhaustive ordinary dispatcher families

Each branch not in the completed table occurs here, or is explicitly excluded
or delegated below. No assumption excludes a row unless expressly stated.
`var`, `memory`, `shared` refer to the checked update interfaces below,
not to already-proved instantiations of them.

| Dispatcher case | Operational result and annotation effects | Existing coverage / missing consumer |
|---|---|---|
| EQ, LT, GT (575–577) | exec_pure2 produces one Boolean word; output provenance NONE, taint empty; no memory/shared update | Missing full successor. Split scalar inputs from two pointers into same positive-size source site (access_ok:538–548). `lower_dload_translate_comparisons` in Sim:91 is arithmetic transport, NOT a joint successor. Need lift G provenance to occurrence H and sites and prove equal Boolean, then var. Not covered by SLT/SGT theorem. |
| SIGNEXTEND, BYTE (590–591) | exec_pure2; scalar result, output provenance NONE/taint empty | Proved by `ld_joint_residual_scalar_next` in JointResidualScalar: J /\ Q /\ P /\ A /\ membership in [SIGNEXTEND; BYTE; OFFSET; INITIAL_FMP] /\ S /\ N implies NEXT. |
| OFFSET (991–996) | exec_pure2 word_add, but out_prov/occurrence_out does NOT retain pointer provenance for OFFSET | Proved by `ld_joint_residual_scalar_next` with the same J /\ Q /\ P /\ A /\ family membership /\ S /\ N signature. Generic scalar transport excludes pointer use; labels agree via local fields. |
| INITIAL_FMP (674–677) | update_var out s.vs_initial_fmp; scalar clean output | Allowed by no_raw_fmp_ops (is_raw_fmp_opcode INITIAL_FMP=F). Proved by `ld_joint_residual_scalar_next` with the same J /\ Q /\ P /\ A /\ family membership /\ S /\ N signature, using local-field equality. |
| BUMP (679–689) | two update_var operations: ptr_out=base_val, next_out=base_val+sz; default provenance clears outputs and taint clears outputs | Allowed by no_raw_fmp_ops (is_raw_fmp_opcode BUMP=F). Missing two-output environment and boundary update; one-output var interface is insufficient as stated. Must establish operands cannot be live pointers, rather than assuming provenance retained. |
| RETPC_PARAM (701–705) | update_var out s.vs_return_pc_token, ignores literal idx operationally; provenance NONE, empty taint | Missing opaque-output successor. Token equality is not a local-field clause; use retpc availability part of ld_env_agree, not numeric equality. PARAM theorem does not include this opcode. |
| NOP (822–823) | OK s; wf outputs are empty, ghosts unchanged | Missing identity-state next boundary; no existing full theorem. One-output var interface does not apply directly. |
| ASSERT, ASSERT_UNREACHABLE (784–805) | clean condition nonzero: OK s; zero: Abort Revert_abort / ExHalt_abort, clears returndata and changes halt state | Missing normal identity-state next and exceptional observation branches. Scalar condition equality from taint/pointer/opaque use; aborted branch is a terminal observation consumer, not NEXT. |
| CALLER, ADDRESS, CALLVALUE, GAS, ORIGIN, GASPRICE, CHAINID, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, BASEFEE, BLOBBASEFEE, CALLDATASIZE, CODESIZE (825–843,857,919) | exec_read0 of equal local fields, one scalar clean output | Proved by `ld_joint_read0_next` in JointRead0, with J /\ Q /\ A /\ family membership /\ S /\ N; no memory access or operand discipline premise. |
| RETURNDATASIZE (877) | exec_read0 of equal boundary returndata length | Proved by `ld_joint_read0_next` with the same J /\ Q /\ A /\ family membership /\ S /\ N signature; equality comes from final boundary clause rather than local fields. |
| SELFBALANCE (853–854) | exec_read0 of account non-storage field | Proved by `ld_joint_read0_next` with the same J /\ Q /\ A /\ family membership /\ S /\ N signature; equality from ld_shared_accounts_fields, not exact account/storage equality. |
| BLOCKHASH, BLOBHASH, BALANCE, EXTCODESIZE, EXTCODEHASH, CALLDATALOAD (844–852,858–861,920–929) | exec_read1 from local data/account non-storage fields at clean scalar index; out provenance NONE and taint empty | Proved by `ld_joint_read1_next` in JointRead1: J /\ Q /\ P /\ A /\ family membership /\ S /\ N implies NEXT. Account balance/code/emptiness transport ignores storage differences. |
| ILOAD (934) | exec_read1 mload at scalar address; provenance NONE, taint=mem_word_taint at source offset | Missing full successor. fn_ptr_ok forbids pointer variables in operands. Requires fixed-region clean/masked word transport; existing MLOAD theorem only names MLOAD. Use var after word/environment proof; normal R and Revert suffix must be distinguished. |
| MSTORE8 (600) | exec_write2 mstore8; writes single low byte; written_taint default empty (taint_ok does not allow tainted MSTORE8 operands) | Missing byte-write memory agreement and memory successor. Clean value and valid relocated destination required. MSTORE full-word lemma does not cover this. |
| MCOPY (601–609) | OK(mcopy dst src size s), reads snapshot slice and writes memory; mem_taint kills destination and propagates source taint | Missing slice transport for two independently relocated ranges, including overlap/zero size, and memory successor. Existing word MSTORE kernel is not a byte-copy kernel. |
| CALLDATACOPY, CODECOPY (863–874,964–975) | OK(write_memory_with_expansion dst bytes s), bytes=zero-padded equal input-data slice; source/size clean scalar, destination may relocate; mem_taint kills destination taint | Missing general equal-byte range write geometry and memory successor. Fixed-region and mapped destination cases, zero size and target scratch disjointness required. |
| RETURNDATACOPY (879–893) | in bounds: same memory-write shape with unpadded equal returndata slice; OOB: Abort ExHalt_abort clearing returndata | Same missing byte-write successor + terminal OOB observation. OOB decision identical by clean offset/size and equal returndata. |
| EXTCODECOPY (977–989) | same memory-write shape, bytes from equal account code; scalar account, code offset and size | Same missing byte-write successor; get account code equality without demanding storage equality. |
| ISTORE (935–941) | OK(istore off value s): writes byte memory AND immutable bookkeeping; no outputs; t_mem and t_imm both change, value may be tainted | Proved normal successor: o1LowerDloadJointInternalEffectsTheory.ld_joint_internal_effect_next combines fixed-address masked memory write and immutable key update; fn_ptr_ok excludes provenance-bearing operands. |
| SHA3 (901–916) | reads zero-padded memory slice, update_var out hash; scalar clean output, provenance NONE | Missing clean slice equality (taint_ok prohibits tainted read outside about_to_revert), hash equality, var successor. Source taint exemption on Revert path is not evidence of hash equality. |
| LOG (998–1023) | OK(s with vs_logs := s.vs_logs ++ [ev]), memory-read slice, clean topics and size, possibly relocated memory address | Proved normal successor: o1LowerDloadJointInternalEffectsTheory.ld_joint_internal_effect_next transports clean payload slices and exact topics/size, appends identical events, and preserves the whole joint boundary. Offset may relocate; zero-size and zero-topic cases included. |
| CALL, STATICCALL, DELEGATECALL (1053–1086) | exec_ext_call/exec_delegatecall; may update variable, memory, returndata, accounts, logs, outcomes, requests etc.; consumes a call outcome | Missing external-effect successor/terminal cases, not an INVOKE. Address of memory buffer can relocate while call request data must agree. Taint semantics truncates written range to returned bytes; delegatecall requires clean storage/transient. None of three simple update interfaces applies directly. Family must be assigned by strategist, not silently delegated as an internal call. |
| CREATE, CREATE2 (1088–1106) | exec_create; clean value/salt, reads initcode slice, external outcome effects, one result variable | Missing external-effect successor/terminal cases; taint_ok requires clean storage/transient. Same combined-update issue as external calls. |
| DLOAD (944–948) | source exec_read1 yields clean scalar word, no source memory write; target ALLOCA32; ADD code_end; CODECOPY32; MLOAD | Proved by `ld_joint_dload_next` in SuppliedSegmentNext:178–201, including fresh/repeated scratch, whole boundary, source successor annotation and four actual supplied microsteps. Exact interface recorded below; not an ordinary one-step NEXT. |
| DLOADBYTES (950–961) | source write_memory_with_expansion dst padded data slice; target ADD code_end then CODECOPY | Proved normal segment by `ld_joint_dloadbytes_next` in SuppliedSegmentNext:40–57, with two actual supplied microsteps and whole boundary. No new scratch ALLOCA; X unchanged. Exact interface recorded below; Revert forwarding remains separate. |

### Excluded ordinary cases and default

- GETFMP, SETFMP, FMP_PARAM: source forbidden by fn_ptr_ok:120–128,
  also fmp_free_ctx/no_raw_fmp_ops where applicable. No target matching
  obligation for these as ORIGINAL source instructions.
- DALLOCA: excluded by `~ctx_has_dalloca C` in o1_src_inv:529–535.
- MEMTOP: excluded by fn_ptr_ok. Memory lengths need NOT agree; hence the
  read0 family above must not accidentally include MEMTOP.
- Sequential PHI: dispatcher returns Error "phi outside prefix" (807–811),
  inconsistent with S. Successful PHI PREFIX is a separate entry case below.
- Wildcard/default: Error "unknown opcode" (1123–1124), inconsistent with S.
  INVOKE is handled by step_inst, not by ordinary step_inst_base.

### Explicit non-ordinary branches (not claimed complete here)

JMP, JNZ, DJMP; RET, RETFMP, DRET; STOP, RETURN, REVERT, SINK,
SELFDESTRUCT, INVALID are all terminators by is_terminator_def. They belong
to control/call/terminal interfaces outside this diagnostic's proof scope.
RETFMP/DRET are additionally forbidden by source fn_ptr_ok.
INVOKE uses internal call/callee/saved-frame interfaces, also out of scope.
An ordinary instruction immediately preceding a terminator still has N;
the terminator's subsequent execution and block entry need separate lifting.

## PHI prefix: distinct missing two-state entry preservation

JointEntry:63–68 `ld_supply_successful_entry` has EXACT signature:
```
ir_supply_covers_fn u fn /\
lower_dload_function_supply u fn = (fn',u') /\
ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
enters_block fn s s1 /\ active_inst fn inst s1 ==>
enters_block fn' s s1 /\ ld_joint_control u fn fn' s1 s1
```
It establishes supplied alignment only from the SAME state. It is not
relocated PHI transfer. `ld_supply_phi_boundary` says eval_phis on original
and supplied instruction lists are equal for the SAME starting state, plus
equal prefix lengths/supply prefix. `non_retpc_phi_input` is only an opaque
input lemma. Missing: two-state parallel `eval_phis` success with equal
selected labels, all selected values available and related using PRE-entry
H/tn; update every PHI output's occurrence/provenance/taint in parallel,
construct actual target `enters_block`, recover whole post-entry boundary
and supplied control. Memory/shared/sites/X and saved frames are unchanged.
None of the one-output or sequential PC update interfaces below does this.

## Checked update interfaces and hard applicability limits

The exact signatures are available at JointAssign:160–180,
JointStorageWrite:76–94, JointMemoryWrite:187–205. Expanded common premises
are J /\ Q /\ A /\ ~MEM opcode [DLOAD;DLOADBYTES] /\ N.
All conclude `?u fn'. lookup_function ... /\ ld_joint_control ... /\
active_inst fn' inst t /\ <whole successor boundary>`; NONE constructs a
target operational step. Caller must establish that independently.

1. **var** additionally assumes `s1=update_var out x s`,
   `t1=update_var out y t`, G1/H1/T1 equal to their step definitions,
   source occurrence reachability and annotation at advanced PC with G1/H1/T1,
   `ld_env_agree sites fn H1 T1 s1 t1`, and unchanged T1.t_mem/t_stor/t_trans/t_imm.
   Concludes the NEXT boundary (without target step). It supports masked,
   relocated, or opaque output values, not just equal scalars, PROVIDED the
   environment premise is proved. Two-output BUMP, no-output identity,
   logs, PHI and combined external effects do not match its state shape.
2. **shared** assumes `s1=s with <|vs_accounts:=sa;vs_transient:=sx|>` and
   analogous target ta/tx; occurrence reachability and annotation at advanced
   PC with unchanged G/H/B and tn1; unchanged tn1.t_var and tn1.t_mem;
   `ld_shared_agree D s.vs_call_ctx.cc_address tn1 s1 t1`.
   Conclusion advances control with unchanged G/H/sites/X and tn1.
   This is NOT an arbitrary shared-fields update interface: logs, immutable
   bookkeeping, returndata and requests cannot be changed through it.
3. **memory** assumes `s1=s with vs_memory:=ms`, analogous target mt;
   occurrence reachability/annotation with unchanged G/H/B, tn1;
   unchanged tn1.t_var/t_stor/t_trans/t_imm; and
   `ld_memory_agree sites lo tn1.t_mem s1.vs_memory t1.vs_memory`.
   Conclusion advances control with unchanged G/H/sites/X and tn1.
   Applicable to pure range writes AFTER byte geometry and annotation facts
   are supplied. It does not support ISTORE's extra immutable update,
   external effects, target scratch allocation, or expanded PC transport.

`ld_joint_control_unchanged_next` (JointAssign:45–54) consumes current control,
distinct block labels, A, non-DLOAD opcode, and source next active instruction
at the PC increment; returns target current active inst and incremented
control. It requires unchanged block identity, not a jump/PHI proof.
`occ_frame_reachable_next` and `occurrence_annotation_next` are source-only
transitions used by completed next proofs; they do not imply target steps.

## Assumption transport and remaining integration checks

- o1_src_inv supplies ptr_discipline for an existential lo, dload offset and
  headroom mem_inv, no DALLOCA, fmp-free source (o1PassContract:529–535).
- Joint boundary supplies SOURCE occurrence reachability; source erasure to
  frame_reachable is needed before using access_ok/taint_ok. It does not
  assert target access_ok or target taint_ok and those must not be assumed.
- `access_ok` (ptrDiscipline:521–549) exempts memory accesses on
  in_revert_forward paths, but still constrains pointer comparisons to a
  SAME positive-size site and in-bounds (possibly one-past) values.
- `taint_ok` (557–576) permits tainted values only for ASSIGN, data shifts,
  full word stores. Its memory-read exemption is `about_to_revert`, not
  merely the normal taint mask. Thus existing R-restricted full successors
  leave a real Revert-suffix obligation; they do not cover all ordinary runs.
- `opaque_use_ok fn` is an additional premise of most successors, not part
  of J. It must be obtained from source shape/support, not asserted.
- Equality of accounts' non-storage fields follows from ld_shared_agree;
  account storage equality generally does not. Local fields include contexts,
  labels, code, data, FMP values, hashes and halted status, not memory length,
  variables, return token, or returndata (the latter is separate in J).
- No successful-target existential can be discharged by an environment-only
  helper. The completed *_step lemmas generally establish a step and an
  environment update; the *_next lemmas above add the other boundary fields.

## Requested strategy checkpoint (not an executor-created plan)

Residual natural interfaces are: (i) clean read0/read1 and remaining clean
pure ops plus opaque token and two-output/identity updates; (ii) same-site
pointer comparison; (iii) byte-slice read/write/copy kernels and combined
ISTORE/log effects; (iv) external effect protocol; (v) two-state PHI entry;
(vi) scratch-aware supplied DLOAD/DLOADBYTES segments; (vii) Revert forwarding.
The strategist must decide ownership/dependencies and de-risk these families
before new opcode leaves. In particular do not schedule more scalar leaves
as if they exhausted the dispatcher. Preserve all completed successors.

## Clean-write normal successors (C1.4.1.13.2.3)

`o1LowerDloadJointCleanWriteTheory.ld_joint_clean_write_next` now supplies the
full normal joint-boundary successor for MSTORE8, CALLDATACOPY, CODECOPY,
RETURNDATACOPY and EXTCODECOPY, under the same source safety and next-active
premises as MCOPY. Shared scalar and destination interfaces cover aliased
operands; the execution packet constructs the target write with identical
payload and handles padding and successful returndata bounds. Zero-length
writes use the empty-write byte relation and impose no address geometry.
RETURNDATACOPY's out-of-bounds Abort and Revert forwarding are not covered by
this normal-success theorem and remain separate obligations.

## Normal range-read successors (C1.4.1.13.3)

`o1LowerDloadJointRangeReadTheory` supplies `ld_joint_iload_step` and
`ld_joint_sha3_step`, and their single shared next-boundary consumer
`ld_joint_range_read_next` (opcode membership `[ILOAD; SHA3]`). ILOAD
transports masked words; SHA3 transports an equal scalar size and a clean
read slice before hashing. The generic `ld_memory_agree_clean_slice`
includes zero-length and padded reads. Both families require explicit
normal-path (`~in_revert_forward`) hypotheses; this is not Revert-suffix
coverage. The scalar SHA3 length proof excludes pointer provenance by the
source pointer-use discipline, including address/length operand aliasing.
No whole-run or final `ctx_sim` claim follows from these local successors.

## Supplied segment successor audit (C1.4.1.16.4.4)

Both public consumers in `o1LowerDloadSuppliedSegmentNextScript.sml` now
construct full successor boundaries, not conditional transport packets.
Using J/Q/P/A/S/R/G1/H1/T1 above:

- `ld_joint_dloadbytes_next` requires J /\ Q /\ P /\ A /\ R /\ S /\
  o1_run_state_ok vs /\ mem_inv dload_offset_ok C vs /\ opcode=DLOADBYTES.
  It existentially returns inst2, es, t2, t3, fn', bb'; lookup_function and
  lookup_block identify the supplied block, TAKE 2 (DROP t.vs_inst_idx
  bb'.bb_instructions)=es, LENGTH es=2 and the slice is in bounds.
  Its actual equations are step_inst fuel C' (EL 0 es) t=OK t2 and
  step_inst fuel C' (EL 1 es) t2=OK t3. Its whole boundary has source PC
  SUC s.vs_inst_idx and target PC t.vs_inst_idx+2, updated G1/T1/H1 and
  unchanged n/a/U/B/HP/sites/X/ts.
- `ld_joint_dload_next` requires J /\ Q /\ P /\ A /\ S /\
  o1_run_state_ok vs /\ mem_inv dload_offset_ok C vs /\
  mem_inv dload_headroom_ok C vs /\ callee_first names C.ctx_functions /\
  opcode=DLOAD. It returns inst2, es, t1,t2,t3,t4,fn',bb',X1 and the
  analogous in-bounds TAKE-4 slice. Four step_inst fuel C' equations execute
  EL 0 through EL 3 in order from t to t4. When the scratch key
  (a,inst.inst_id) is absent, X1 extends X with
  ((EL 0 es).inst_id,t.vs_alloca_next); otherwise X1=X.
  Its whole boundary has updated G1/T1/H1, source PC SUC s.vs_inst_idx,
  target PC t.vs_inst_idx+4, scratch X1 and unchanged remaining witnesses.

Neither requires successor reachability, annotation, geometry, offset numeric
bounds, generated-variable freshness or scratch credit as a premise. These
are derived inside Resources/Next using the original boundary and initial
invariants. Neither is a block-entry/terminal or whole-run theorem.
No new definitions or duplicate exported helpers were introduced by this
assembly. Resources and Next contain no cheat or deliberate failure tactic.
Validation: holbuild Resources, Next and Sim passed together
(tool_output:TO_ld_sim_v2-20261104T173029Z_m5475_t001). This does not certify
completion of the frozen theorem, which remains open.

## C1.4.1.17.1 exceptional-execution interface audit (2026-11-04)

This section supersedes the *exceptional* missing-consumer descriptions above;
normal supplied DLOAD/DLOADBYTES successors and the other completed normal
families remain completed. This is an interface diagnostic, NOT new checked
preservation. Current Sim build passed (TO_ld_sim_v2-20261104T173029Z_m5511_t001).

### Exact ordinary Abort inventory

Current dispatcher lines have shifted; references in this section are current.
A direct scan of venomExecSemantics:508–1145 gives the following exhaustive
ordinary Abort producers. REVERT and INVALID are terminators, delegated to
C1.4.3; propagated INVOKE aborts belong to C1.4.2, not this inventory.

| Ordinary producer | Source premise / target decision | Existing facts and residual consumer |
|---|---|---|
| ASSERT / ASSERT_UNREACHABLE (800–824) | one defined condition, zero; tags Revert_abort / ExHalt_abort respectively | `JointIdentity.ld_joint_assert_abort` already constructs matching target Abort. No new proof needed. |
| RETURNDATACOPY (898–912) | three defined operands [dst;src;len], and w2n src + w2n len exceeds returndata length | Boundary has equal returndata. Taint forbids tainted operand values here even on forwarding paths; fn_ptr_ok makes src/len non-pointers. `ld_joint_operand_clean` can give equal src/len after active/non-retpc premises. `ld_joint_operand_defined` supplies dst availability even when access geometry is exempt. Missing actual Abort consumer (normal in-bounds copy is already proved). |
| CREATE / CREATE2 (1107–1125, exec_create:509–529) | correct operand list and single output, all operands defined; w2n sz > 2 * max_code_size | `exec_create_abort_iff` gives exact inversion. Size is clean scalar; target offset need only be defined, not range-related, and no initcode equality or oracle request equality is needed in this branch. CREATE2 salt also must be defined. Existing normal CREATE transport assumes OK and cannot discharge this branch. Missing actual Abort consumer. |

For all these rows `dead_result_rel D (Abort a s1) (Abort b t1)` asks
ONLY `(a = Revert_abort ==> b = Revert_abort)` (ptrDiscipline:823–837).
It compares no state fields, returndata payload, logs, memory, or requests on
Abort. Nevertheless the target must actually Abort: Error is not related.
Matching identical tags is a sufficient and simple local interface.

### Exemptions are different, and their overlap is limited

* `contextCodegenRel:310–342`: revert_forward_pair bb i j has COPY at i,
  REVERT at j, ASSIGN only strictly between, and resolve_block_assigns
  constraints linking endpoints and a resolved zero source offset.
  `in_revert_forward` holds only at endpoints, NOT intermediate ASSIGNs.
* `ptrDiscipline:516–522`: about_to_revert holds at every REVERT, or at a
  RETURNDATACOPY immediately followed by an active REVERT. It has no operand
  resolution constraints. Hence neither predicate can replace the other.
* access_ok exempts memory ranges at in_revert_forward endpoints. taint_ok
  exempts memory-read taint at about_to_revert, but its operand-taint clause
  remains in force. A forwarding copy with intervening ASSIGNs is access-exempt
  but not about_to_revert. COPY reads returndata, not payload memory; this
  mismatch does not itself require equality of discarded memory.
* Standalone REVERT also needs no payload equality. Without forwarding,
  access_ok still constrains its source range; that is unnecessary for its
  Abort observation but may be needed by other invariants.

### Availability and supplied-control interfaces actually available

`ld_env_agree` includes equal definedness on fn_ir_vars even for opaque RETPC
variables; its value clause deliberately excludes those variables.
`ld_env_operand_defined` / `ld_env_operands_defined` require label equality
and operand membership, not non-retpc or taint facts. JointRelation exposes
`ld_joint_operand_defined` at the full boundary. Therefore first-copy operand
availability is already obtainable without any exempt-range transport.

`JointAssign.ld_supply_insts_append` composes supply over lists, and
`ld_supply_insts_index` identifies an unchanged instruction after an expanded
prefix. `ld_joint_control_unchanged_next` transports a current source/target
control boundary through a non-DLOAD instruction to a source next instruction.
`lower_dload_inst_supply_special` leaves every COPY/ASSIGN/REVERT unchanged,
including supply. Thus the entire suffix is syntactically unchanged AFTER the
possibly expanded prefix; it is not at the same numerical source/target index.
There is not yet an exported whole-suffix alignment theorem in this interface.
It follows structurally from append + identity supply, but remains to prove.

Availability-only transport suffices AFTER a successful copy: ASSIGN changes
only one variable, propagating definedness without comparing values; REVERT
needs two defined operands and always aborts Revert. Labels must agree and the
same suffix instructions must be fetched. At the copy itself availability is
NOT enough: if source succeeds and eventually reverts, target OOB would abort
ExHalt, which fails the one-way Revert-tag condition. Equal scalar src/len and
equal returndata length must therefore be retained at that first step.

### Proposed minimal HOL consumers (proposals, not registered theorems)

Use J, A, Q and P exactly as the textual schemas at the top of this ledger.
No new predicate definition is proposed. First an ordinary terminal interface:

```sml
J /\ Q /\ P /\ A /\
MEM inst.inst_opcode [RETURNDATACOPY; CREATE; CREATE2] /\
step_inst fuel C inst s = Abort reason s1 ==>
?t1. step_inst fuel C' inst t = Abort reason t1
```

No `~in_revert_forward` premise is needed: none of the branch guards reads
memory. The smallest missing prerequisites are a clean-scalar guard operand
projection valid at forwarding endpoints, and dispatcher inversion/assembly
using definedness for the other operands. Do not reuse the existing local
CREATE operand lemma: it demands non-forwarding and payload slice equality,
which are irrelevant to oversized-initcode abort.

A reusable post-copy suffix consumer can avoid the joint relation entirely:

```sml
s.vs_inst_idx = t.vs_inst_idx /\ s.vs_labels = t.vs_labels /\
(!v. v IN V ==> (IS_SOME (FLOOKUP s.vs_vars v) <=>
     IS_SOME (FLOOKUP t.vs_vars v))) /\
s.vs_inst_idx <= j /\ get_instruction bb j = SOME ri /\
ri.inst_opcode = REVERT /\
(!k ii v. s.vs_inst_idx <= k /\ k <= j /\
          get_instruction bb k = SOME ii /\ MEM (Var v) ii.inst_operands ==>
          v IN V) /\
(!k ii. s.vs_inst_idx <= k /\ k < j /\
        get_instruction bb k = SOME ii ==> ii.inst_opcode = ASSIGN) /\
exec_block fuel C bb s = Abort Revert_abort s1 ==>
?t1. exec_block fuel C' bb t = Abort Revert_abort t1
```

The restriction to V is essential: whole-environment availability is NOT
directly derivable from J, which tracks only fn_ir_vars and permits target
scratch variables. Choose V as the set of fn_ir_vars at integration; suffix
operand membership follows from bb belonging to fn. Paired single-variable
update preserves restricted agreement whether or not its output is in V.
This restricted-availability update/transport is a missing kernel, not an
extra whole-environment assumption to add at the final use site. Source Abort rules out malformed or
undefined source ASSIGN/REVERT and also ensures each required instruction is
present. No opaque variable numeric equality is needed.

Finally the integration consumer should hide source/target index shifting:

```sml
J /\ Q /\ P /\ A /\ inst.inst_opcode = RETURNDATACOPY /\
in_revert_forward fn s /\
lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
exec_block fuel C bb s = Abort reason s1 ==>
?fn' bb' t1. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  exec_block fuel C' bb' t = Abort reason t1
```

At an active COPY, the in_revert_forward endpoint must be the first endpoint
(opcode disjointness excludes being REVERT). Resolve constraints identify the
suffix but need not prove payload equality. Split OOB immediately; otherwise
perform target COPY with equal guard operands, drop memory agreement, and
apply restricted-availability suffix transport after alignment. Exact-tag
transport is stronger than dead_result_rel and seems sufficient without any
new definition. It remains unproved and must be planned before execution.

### Missing interfaces / non-gaps summary

Missing: ordinary OOB/oversized CREATE Abort consumer; restricted availability
update and ASSIGN*–REVERT execution kernel; unchanged supplied suffix alignment;
first-copy-to-suffix integration constructing actual target exec_block Abort.
Not missing: assertion Abort, normal COPY/CREATE successors, supplied DLOAD
segments. Not evidence of target Abort: stepWriteFootprintForward's
`assign_suffix_no_normal` and `revert_forward_pair_no_normal`, whose disjunction
reasoning explicitly permits Error. Run/terminator/call lifting is outside this
diagnostic. No HOL source, existing definition, or theorem statement changed.

### C1.4.1.17.5 integrated exceptional forwarding consumer

`o1LowerDloadForwardAbort.ld_joint_forward_abort` now constructs an actual
same-fuel target `exec_block` Abort with the identical reason from J, Q, P, A,
active RETURNDATACOPY, source `in_revert_forward`, block lookup and a source
block Abort. It returns the target function/block lookups as well as execution.
No non-forwarding assumption, target range safety, memory equality after COPY,
or equal numerical instruction indices is used. The generic
`ld_available_forward_abort` synchronizes the COPY guard and uses the aligned
restricted-availability suffix on success. `ld_joint_control_forward_fetch`
provides the relative-index alignment through the REVERT endpoint.

The exceptional ordinary guards are separately covered by
`o1LowerDloadExceptional.ld_joint_ordinary_abort` (COPY OOB and oversized
CREATE/CREATE2), alongside the existing ASSERT consumer. ForwardAbort is
imported by Sim. These results cover this exceptional family only: standalone
terminators, INVOKE, full run lifting and the frozen stage theorem remain open.

### C1.4.29 internal RET step consumer

`o1LowerDloadJointReturn.ld_joint_ret_step` consumes J, P, opaque_use_ok,
active RET and actual source `step_inst = IntRet ir s1`. It returns an actual
target `IntRet jr t`, equal `iret_values`, both adopt_fmp fields NONE and
`s1=s`. Its operand boundary `ld_joint_ret_front` proves equality only on
FRONT operands. Availability includes the final token, but value equality
does not: the opaque token may differ. The empty operand case is excluded by
source operational success, not by an additional theorem premise.

Equal `iret_values` supplies the common `vals` input to
`ld_return_local_restore` after rewriting the target list. That restoration
lemma still requires saved caller environment/parameters and successful
source bind_outputs. This RET step consumer does not establish target active
control, whole-boundary caller restoration, ownership restriction, credit
restoration, or INVOKE entry. It is imported into Sim but is not a proof of
the frozen stage theorem.
