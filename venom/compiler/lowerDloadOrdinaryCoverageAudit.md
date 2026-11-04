# Ordinary coverage checkpoint (reconciled through C1.11.5.64)

This is an interface audit, not a theorem or a claim that the frozen contract is proved.
Source snapshot: 765ee6583 (ambient grouped-write coverage). No semantic definitions or
existing theorem statements were changed. E0060/E0061 are the earlier terminal/assembly
reports. The external-effect proposals below are UNPROVED; the accepted write and
ambient certificates are not reclassified as missing.

## Exhaustive opcode partition

Universe: every constructor in venom/defs/venomInstScript.sml:23-69.
Dispatch: venom/defs/venomExecSemanticsScript.sml:559-1125. `checked` below
means a conditional effect, NOT a location-preservation or reachable-state theorem.
Abbreviated source names below all live in venom/compiler/ and end in Script.sml.

| Constructors | Status and checked interface / gap |
|---|---|
| ADD, SUB | checked ld_affine_effect, lowerDloadSafetyAffineEffects:153; updates selected H |
| MUL, Div, SDIV, Mod, SMOD, Exp, ADDMOD, MULMOD, SLT, SGT, ISZERO, AND, OR, XOR, NOT, SIGNEXTEND, BYTE, OFFSET | checked ld_scalar_pure_effect, lowerDloadSafetyScalarEffects:106-151; requires labels equality |
| EQ, LT, GT | checked ld_comparison_effect, lowerDloadSafetyComparisonEffects:172; requires access_ok and selected-site observations |
| SHL, SHR, SAR | checked ld_shift_effect, lowerDloadSafetyShiftEffects:128 |
| MLOAD | checked ld_mload_effect, lowerDloadSafetyMloadEffects:89; masked bytes, non-forward access |
| ILOAD | checked ld_iload_effect, lowerDloadSafetyIloadEffects:66; actual memory read, scalar immutable offset |
| MSTORE, MSTORE8 | checked effects in lowerDloadSafetyMemoryWriteEffects; premises assembled by ld_sync_memory_write_effect (WriteAssembly:187); live-successor ld_pair coverage in WriteCoverage:81 |
| MCOPY | checked ld_mcopy_effect (MemoryCopyEffects:42), ld_mcopy_zero_effect (EmptyCopy:15); grouped assembly and ambient live-successor coverage as for stores; zero-length needs no address containment |
| SLOAD, TLOAD | checked ld_storage_read_effect, lowerDloadSafetyStorageReadEffects:111 |
| SSTORE, TSTORE | checked ld_storage_write_effect, lowerDloadSafetyStorageWriteEffects:75; explicit scalar key and masked value premises NOT assembled |
| ASSIGN | checked ld_assign_effect, lowerDloadSafetyAssignSteps:78 |
| PARAM | checked ld_param_effect, lowerDloadSafetyParamEffects:103; selected output updates |
| RETPC_PARAM | checked ld_retpc_param_effect, lowerDloadSafetyRetpcEffects:39; opaque output, not token equality |
| PHI | step_inst_base always Error (:807-811), so cannot be a successful sequential step; block-entry eval_phis covered conditionally by ld_phis_effect, lowerDloadSafetyPhiEffects:53 |
| CALLER, ADDRESS, CALLVALUE, GAS, ORIGIN, GASPRICE, CHAINID, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, BASEFEE, BLOBBASEFEE, CALLDATASIZE, RETURNDATASIZE, CODESIZE | checked ld_environment_read_effect, lowerDloadSafetyEnvironmentReadEffects:77 |
| BLOCKHASH, BLOBHASH, CALLDATALOAD | checked ld_keyed_environment_read_effect, lowerDloadSafetyKeyedEnvironmentReadEffects:81 |
| BALANCE, SELFBALANCE, EXTCODESIZE, EXTCODEHASH | checked ld_account_read_effect, lowerDloadSafetyAccountReadEffects:142 |
| MEMTOP, GETFMP, SETFMP, RETFMP, DRET, FMP_PARAM | excluded at source member by fn_ptr_ok_def, ptrDiscipline:120-140. MEMTOP exclusion is NOT from o1_ctx_shape or fmp_free_ctx alone. ld_sync includes EVERY(fn_ptr_ok P). DRET also excluded by o1_fn_shape/no_dret. Raw FMP exclusion separately from fmp_free_ctx/no_raw_fmp_ops |
| DALLOCA | excluded at source by o1_src_inv (~ctx_has_dalloca), also fmp_free_ctx/no_raw_fmp_ops; no claim that arbitrary ld_sync excludes it |
| INITIAL_FMP, BUMP | missing effects. is_raw_fmp_opcode INITIAL_FMP/BUMP = F (venomInst:636-638); not justified as excluded by fmp_free_ctx. INITIAL_FMP observes equal ld_nonghost field; BUMP is two-output arithmetic. Need exact shape/ptr-use audit before assembly, not assumption of exclusion |
| NOP | missing identity effect/ghost and location assembly; dispatch OK s regardless of malformed fields |
| JMP, JNZ, DJMP | missing control effects plus enters_block/PHI/envelope reconstruction; equal untainted scalar selectors needed; DJMP OOB and invalid-label paths are Error |
| ASSERT, ASSERT_UNREACHABLE | missing guarded identity effects; successful nonzero branch OK s, zero branch Abort, malformed/undefined Error |
| STOP, SINK, RETURN, REVERT, SELFDESTRUCT, INVALID | terminal alternatives, not ordinary OK successors. STOP/SINK/RETURN/SELFDESTRUCT Halt; REVERT/INVALID Abort. Need active-state raw safety and no-OK/return classification at location/run consumer; no full common terminal family theorem yet |
| RET | internal IntRet, not ordinary OK; missing matching return witness/return binding at parent call coverage. Empty/undefined return values Error. Do not compare opaque final token |
| ALLOCA | separate allocation family, not covered by ordinary effects. Live maps/scratch/frontier helpers exist in lowerDloadSafetyRelation and lowerDloadScratchSafety, but no general assembled sequential-step theorem is claimed |
| DLOAD, DLOADBYTES | separate generated expansion phases, not unchanged ordinary instructions. lowerDloadScratchSafety and lowerDloadConfiguredOrigins supply conditional prefix safety; full synchronized phase/next-location assembly not established here |
| CALLDATACOPY, CODECOPY, EXTCODECOPY | genuinely missing copy effects. Equal external byte source plus equal scalar source offset/length; classified destination; EXTCODECOPY also scalar account. Existing ld_memory_write_low/slot can be reused, not duplicate overwrite proofs |
| RETURNDATACOPY | missing ordinary effect for in-bounds path and exceptional-path agreement; forwarding suffix explicitly permits loss of memory correspondence. E0060 ld_forward_prefix_raw covers target-only suffix raw safety, not paired copy effects |
| ISTORE | missing memory+immutable-bookkeeping effect; cannot count ld_mstore_effect as covering this opcode. Offset is nonpointer by fn_ptr_ok, but word taint and t_imm update still needed |
| SHA3 | missing read/observation effect. Non-forward taint_ok excludes tainted read bytes; classified memory read should give equal byte lists before hashing |
| LOG | missing history-only effect; no need for historical logs equality (ld_nonghost omits logs), but shape, operand definedness, memory access and unchanged projections still needed |
| CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2 | missing effects; dispatch/helpers audited below. CALL/STATICCALL need equal completion observations, NOT full request/outcome equality under masked storage; other three use equal concrete EVM inputs from empty storage masks. Returned bytes, masked adoption and scalar-output ghosts still need checked transport. No exclusion argument exists |
| INVOKE | not ordinary base success: default base branch is Error; actual step_inst handles recursive run_blocks. E0060 ld_invoke_no_return excludes caller resumption for terminal callee; general successful-call/return transport belongs to parent, not checked effects |

Every constructor is listed once. The default in step_inst_base has no other opcode
constructor beyond INVOKE. Excluded source constructors must still be excluded at
the transformed active location by structural origin facts; this is not automatic.

## Success, malformed shapes, and terminal alternatives

Most effects assume target OK and prove source OK, not failure equivalence. That is
appropriate for raw_reachable next/block rules, which require OK. Safety of the
current active instruction must be proved BEFORE running it, including Error,
Abort and Halt cases. Ignoring failed instructions would weaken the frozen goal.

fn_inst_wf follows from o1_fn_shape (o1PassContract:332-350). Use it for outputs=[]
when semantics does not check that field: MSTORE/MSTORE8 use exec_write2, MCOPY
checks only operands, NOP accepts any fields. Target OK alone does not justify
well-formed source outputs. Read/pure combinator success generally forces a single
output and operand arity; explicit source shape is still available. Malformed
operands leading to Error give no successful successor, but their active raw safety
is still a separate obligation. PHIs execute in parallel at block entry, never by
sequential step_inst_base success.

Terminal forwarding alternative is exactly the bounded suffix form already checked
in lowerDloadTerminalSafety:105-119: lookup_block current bb, revert_forward_pair bb i j,
i <= current index <= j, current get_instruction, initial frontier < dimword, and
RTC of successful sequential suffix steps from its entry state. ld_forward_prefix_raw
then yields raw_mem_ok without a source paired memory state. The eventual reachable
coverage statement must be ld_pair OR this explicit suffix witness. Neither generic
REVERT nor RET automatically produces that witness. ld_forward_run_blocks_no_normal
and ld_invoke_no_return forbid caller next for such a callee.

## Sequential advance consumer (now checked)

The candidate below is now `ld_sync_ordinary_advance` in
lowerDloadSafetyAdvanceScript.sml:6-34. Its effect and next-location premises
remain explicit, but reconstruction is no longer a missing theorem. For grouped
writes, ld_sync_memory_write_advance and ld_sync_memory_write_coverage_ambient
supply those premises from target success and a target active successor. Other
families must still provide their effects. The historical GAP names below label
inputs, not gaps in the checked constructor itself.

The following is the common *assembly* interface, using existing relations only.
It intentionally exposes its missing effect premise rather than asserting a new
all-opcode theorem. Variables are implicitly universally quantified. Sigma is not
needed for this local consumer; configured-supply equality is preserved separately.

```sml
ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
ld_global lo A (f::fs) /\
f.lf_src = s /\ f.lf_tgt = t /\
~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
t.vs_inst_idx = p /\
step_inst fuel C' inst t = OK ts /\
(* GAP E: an assembled family effect with the exact ghost update *)
step_inst fuel C inst s = OK ss /\
tn' = step_taint inst s ss tn /\
G' = step_prov PG G inst ss /\
f' = f with <| lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
               lf_tgt := ts with vs_inst_idx := SUC p;
               lf_H := H'; lf_tv := tn'.t_var |> /\
G' = ld_erase A o_f H' /\ ld_vars P A f' /\
ld_memory lo A tn' ss ts /\ ld_nonghost tn' ss ts /\
(* GAP L: source and target next locations and non-variable projections *)
active_inst fn next (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
(?Y. ld_envelope f.lf_supply fn
       (ss with vs_inst_idx := SUC s.vs_inst_idx)
       (SUC s.vs_inst_idx) Y (SUC p)) /\
ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
(* GAP H: changed H selects only live original sites *)
(!a. a IN FRANGE H' ==> a IN FDOM A) ==>
ld_sync lo P C vs0 stk PG G' tn' fn next
  (ss with vs_inst_idx := SUC s.vs_inst_idx)
  (ts with vs_inst_idx := SUC p) A (f'::fs) N /\
ld_global lo A (f'::fs)
```

This candidate is for unchanged, nonallocating sequential instructions only.
ALLOCA and DLOAD completion change A/E; jumps use frame_reachable_block and entry
provenance/taint; calls change stack; terminal suffix uses the disjunction above.
They must not be smuggled through GAP E. Live A and frame fn/supply/Q/E are unchanged
by this candidate, while H' is the family's explicit selected-provenance update.

The missing source next-active premise is deliberately visible in GAP L; ultimate
location coverage must derive it from source shape, target next-active, structural
image/envelope facts (not assume source successful termination). Source step fuel
can differ in general call/run transport; the local non-INVOKE case uses the same
fuel because dispatch reduces to base semantics. A stage/supply/context-image
interface is still needed when lifting this consumer back to ld_pair.

Critical recheck against lowerDloadSafetyRelation:123-154: the candidate now
explicitly exposes the next envelope as well as next active instruction. `ld_sync`
alone does not include source block-label uniqueness/shape; do not infer the next
envelope by matching an arbitrary existential block witness in ld_envelope.
The eventual structural boundary must derive this premise using source shape and
the singleton envelope. With this explicit premise, the remaining sync conjuncts
are structurally accounted for: maps/slots/intervals and charge use unchanged
allocas/frontiers, serial/fn/supply/Q/E and saved frames are unchanged, active
reachability uses frame_reachable_next (ptrDiscipline:458-466), and the new head
vars/tv/erasure are explicit. The global selected-range conjunct needs GAP H;
its Q part is inherited. Memory/nonghost do not inspect instruction index
(lowerDloadSafetyKernel:21-57). This reconstruction is now a checked HOL
constructor proof, with these inputs still explicit.

## Reconciled classified-write ledger

The former missing-premise table is superseded by these checked interfaces:

| Premise | Checked supplier |
|---|---|
| operand definedness, scalar/value/address observation, ptr restrictions | WriteAssembly:9-110 (ld_write_value_nonpointer through ld_write_address_observation) |
| positive write/read classification | ld_write_access_classified :112; ld_read_access_classified :126 |
| zero MCOPY | ld_mcopy_zero_effect, EmptyCopy:15; no classification of an empty range |
| word-byte width and MSTORE8 untainted low byte | TaintWidth and AssemblyPremises; consumed in ld_sync_memory_write_effect |
| source success, post vars/memory/nonghost, unchanged erased provenance, live H | ld_sync_memory_write_effect, WriteAssembly:187-207 |
| maps/global and next reconstruction | ld_sync_ordinary_advance, Advance:6; ld_sync_memory_write_advance, WriteAdvance:7 |
| singleton envelope and active source successor | ld_sync_ordinary_envelope, Locations:90; ld_envelope_singleton_next :33; ld_envelope_active_head :109 |
| source fn shape/wf/labels and target no-wrap | ld_sync_fn_shape, o1_fn_shape_components, ld_sync_labels, ld_sync_ambient_headroom in Ambient |
| source reachability -> raw reachability and mem_inv use | ld_frame_reachable_certificate :362, ld_frame_raw_reachable :410, ld_sync_source_mem_inv :417 |
| assembled live-successor pair | ld_sync_memory_write_coverage_ambient, WriteCoverage:81 |

The last theorem still requires ld_sync, ld_global, o1_ctx_shape C,
ptr_discipline lo C vs0, mem_inv dload_headroom_ok C vs0,
~in_revert_forward fn s, target OK, target next active instruction, configured
supply and stack order. It does NOT establish prefix exhaustiveness, current
instruction raw safety for every opcode, or a source invariant at an arbitrary
reachable target state. A source headroom mem_inv is available from o1_src_inv
only at final integration. Non-revert is a case alternative, not a projection
of o1_src_inv. Source raw reachability certificates include saved continuation
bookkeeping; they are not general successful external-call transport.

## Grouped remaining dependency graph (proposal, not new PLAN IDs)

1. External effects: outcome selection with masked accounts for CALL/STATICCALL;
   concrete EVM run-input equality for DELEGATECALL/CREATE/CREATE2; shared returned
   byte writer; output and taint/provenance reconstruction. Detailed audit follows.
2. Byte copies and immutable writes: CALLDATACOPY/CODECOPY/EXTCODECOPY,
   ordinary RETURNDATACOPY (plus exceptional-path handling), ISTORE. Reuse the
   checked low/slot overwrite boundaries and empty-write observation, not a second
   memory model. Forwarding RETURNDATACOPY uses the existing suffix alternative.
3. Observations/identity: SHA3, LOG, INITIAL_FMP, BUMP, NOP and assertions.
   Existing read/pure/storage effects still need reachable premise assembly.
4. Control/terminal: jump and PHI entry reconstruction; all terminal active-state
   safety and the explicit revert-forward witness. RET and INVOKE require parent
   call/run/return transport, not an ordinary OK consumer.
5. Existing-effect assembly: reuse Advance/Locations/Ambient, then pair-zero;
   do not duplicate grouped-write coverage. ALLOCA/DLOAD expansion completion has
   separate map/scratch/phase obligations, not the ordinary constructor.
6. All consumers + initialization + call-stack/expansion preservation -> target
   prefix coverage -> raw target invariant -> frozen theorem integration.

No completed parent or exhaustive ordinary theorem is claimed.

## External-family semantic audit (.51; proposals are NOT checked)

### Dispatch and observations actually used

Exact dispatch references are venomExecSemanticsScript.sml:1053-1106.
CALL requires seven defined operands, STATICCALL and DELEGATECALL six,
CREATE three, CREATE2 four. Every branch requires exactly one output in its
helper. Target OK therefore exposes these shapes, values and (for concrete EVM
branches) successful extraction. Source definedness still needs ld_vars and the
static nonopaque-use restrictions; target OK is not a source-success witness.

| Opcode | Source-success witness required after target OK | Semantic input agreement |
|---|---|---|
| CALL | exec_ext_call at source evaluated args; same Boolean success word, no run termination premise | equal target/value/input bytes/static flag and equal vs_outcomes; gas must be defined but its value is ignored |
| STATICCALL | same exec_ext_call witness with value=0 and static=T | equal target/input bytes/outcomes; static adoption disabled, gas ignored |
| DELEGATECALL | same run evm_s and SOME extraction as target | equal concrete EVM execution_state from make_venom_delegatecall_state; gas, target and input bytes equal |
| CREATE | same run evm_s and SOME extraction, output address equal | equal init code, sender account nonce, value, call context gas, concrete create state |
| CREATE2 | same as CREATE, using salt/code-hash address | additionally equal salt; address_for_create2 sees equal init code |

CALL/STATICCALL are NOT implemented by make_venom_call_state/run. The nearby
comment at venomExecSemantics:304-313 is historical; actual exec_ext_call:477-484
uses venom_call_request/consume_call_outcome. Request fields
(venomCallOracleDefs:11-19) are target, value, memory input bytes, static flag,
entire accounts and transient storage. They do NOT include gas, histories, oracle
list, allocation frontier, immutables, transaction or block fields. In particular
ld_nonghost does not imply request equality: masked caller storage may differ.
Do not attempt a request-equality theorem under just ld_nonghost.

Crucially take_outcome (extCallOracle:95-104) does not inspect masked storage:
computed_precompile depends only on value/target/data (80-83). The ordinary
nonempty case takes the identical head outcome, the empty case constructs a
failed_outcome using each request's own accounts/transient, and computed cases
also use that own-state failed_outcome, updating success/returnData. Thus full
outcome record equality is unnecessary and generally false even in computed
success. Need equality only of success, returnData, remaining outcomes, plus
masked post accounts/transient. adopt_outcome (115-119) chooses common supplied
accounts/transient on successful nonstatic ordinary adoption, or keeps each
prestate otherwise; computed adoption supplies each request's own state.
Histories are appended/kept but not read to choose a completion. Pending deletions
are appended/kept (126-130), not used in outcome selection or ld_nonghost.

DELEGATECALL uses actual run (venomExecSemantics:490-502). Code is looked up
from target accounts; make_venom_delegatecall_state:389-403 reads call address,
original caller, call value, static, supplied gas/calldata/code, all accounts and
transient, and venom_to_tx_params:318-332. CREATE/CREATE2 (:509-526) use init
bytes, sender account nonce (CREATE), salt/code-hash (CREATE2), cc_gas and value;
make_venom_create_state:409-423 transfers value and builds rollback with all
accounts/transient. make_sub_tx:336-345 and make_rollback:351-359 read no other
Venom fields. All transaction/block/prev-hash inputs agree by ld_nonghost. Account
nonstorage fields agree there too. taint_ok:573-575 supplies t_stor=t_trans={}
for these three opcodes, turning masked agreement into full accounts/transient
equality. This needs a small proved projection, not an assumption that storage
is always equal. Their run input has no memory except the already-read input
bytes, and no Venom logs/requests/immutables/frontier. Equal EVM inputs imply
identical run result by congruence without proving EVM termination independently.

### Post-state and ghost obligations

extract_venom_result:437-468 requires SOME(result,final_state) with singleton
contexts. It writes returndata, accounts, appended logs, memory and transient.
Success takes final rollback accounts/transient; failure retains each prestate.
CREATE uses retOff=retSize=0: no byte changes (memory list representation may
still expand), so reuse read-byte equality for empty writes, NOT memory-list
length equality. DELEGATECALL and oracle calls write only TAKE retSize returndata
at retOff. Return buffer lengths and data agree; return addresses may relocate.

All five preserve allocas, frontier, block labels, prev block, instruction index,
params and return-PC fields before the explicit sequential increment. update_var
binds their common scalar output. All outputs have empty out_taint (:332 onward).
Use H' = FDIFF f.lf_H (set inst.inst_outputs), erase/step_prov update and live-range
subset lemmas, as for existing scalar-output effects; do not leave stale selected
provenance on an overwritten output. Output ld_vars also needs proof that this
non-pointer-producing output cannot be an opaque or selected root use.

Memory: new_site_bytes empty; step_writes (:267-273) truncates call writes to
MIN requested length (LENGTH returndata); written_taint empty. Thus return bytes
clear the corresponding source taint, while all other masked byte agreement is
preserved by the general low/slot writers. CREATE/CREATE2 have no memory ranges.
IMM taint and immutable maps stay unchanged. For CALL/STATICCALL step_taint
adopt_reset (:397-410) depends on whether SOURCE accounts/transient changed,
not whether target changed. Must case-split source change, actual adoption and
computed/ordinary outcomes: if source changed, common ordinary adopted state
agrees fully and cleared mask is valid; if unchanged, the old source mask suffices
against adopted state. Do not assume the two change Booleans equal. Concrete EVM
branches keep t_stor/t_trans (already empty), and equal extracted states suffice.
ld_nonghost omits logs, requests and pending deletions, so no historical equality
is needed; old immutable masks and equal call/tx/block/etc projections persist.

### Access/taint premises and current-instruction safety

memLocDefs:240-257 and :287-323 describe requested return writes and input reads.
CALL uses ao/as at positions 3/4 and ro/rs at 5/6; STATICCALL/DELEGATECALL use
2/3 and 4/5. CREATE/CREATE2 read offset/size at 1/2 and write no Venom memory.
ptr_use_ok:85-100 allows a pointer only at the read/write ADDRESS position, once;
it does not allow a pointer length, gas, account, value or salt. Numeric operand
agreement must be proved for these shapes, including duplicate variable cases.
All operand taints are empty by taint_ok:559-566. Input bytes are untainted by
:567-572 outside about_to_revert; external effects cannot use the exception
silently. Need either ~in_revert_forward plus its checked implications or an
explicit terminal-forward alternative. Nonempty accesses classify via access_ok,
ld_maps/global and positive read/write classification, giving equal relocated
input bytes and safe target bounds. If input size=0, read_memory is [] at ANY
address: no containment premise. If return size=0 or actual returndata=[], no
bytes change; no address classification for the empty write is justified.
For raw safety, however a nonzero REQUESTED return buffer still needs its full
range below the frontier even when actual returndata is empty. Actual step_writes
is insufficient to prove current raw_mem_ok. The write classification must use
source_memory_write_ranges, not only the truncated step write. CREATE has only
input raw bounds. Target headroom and source access facts can establish current
raw safety without assuming step_inst succeeds; failed/undefined instructions
cannot be discarded from raw_reachable. Forward suffix uses its explicit
raw-safety witness separately.

### Proposed HOL boundaries for review (not inserted in SML)

First, a semantic selector boundary which deliberately does NOT require rq equality:

```sml
(* same exposed request inputs, possibly different account/storage fields *)
rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
rq.cr_data = rq'.cr_data /\ rq.cr_static = rq'.cr_static ==>
 SND (take_outcome rq os) = SND (take_outcome rq' os) /\
 (FST (take_outcome rq os)).co_success =
   (FST (take_outcome rq' os)).co_success /\
 (FST (take_outcome rq os)).co_returnData =
   (FST (take_outcome rq' os)).co_returnData
```

Second, the empty-mask projection (general, not one per opcode):

```sml
ld_nonghost tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
 s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
```

Then shared returned-byte update and masked account-adoption boundaries should
be designed in the same theory, independent of operand lists. Concrete EVM input
congruence should use the projection above plus ld_nonghost and equal input bytes,
rather than a new EVM simulation relation. These smaller boundaries must be
checked before authorizing the following grouped CONSUMER proposal:

```sml
ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
ld_global lo A (f::fs) /\ o1_ctx_shape C /\
ptr_discipline lo C vs0 /\ mem_inv dload_headroom_ok C vs0 /\
~in_revert_forward fn s /\
MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
step_inst fuel C' inst t = OK ts ==>
?ss H'. step_inst fuel C inst s = OK ss /\
 ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
                      lf_H := H'; lf_tv := (step_taint inst s ss tn).t_var|>) /\
 ld_memory lo A (step_taint inst s ss tn) ss ts /\
 ld_nonghost (step_taint inst s ss tn) ss ts /\
 step_prov PG G inst ss = ld_erase A o_f H' /\
 (!a. a IN FRANGE H' ==> a IN FDOM A) /\
 ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
 ss.vs_alloca_next = s.vs_alloca_next /\
 ts.vs_alloca_next = t.vs_alloca_next /\
 ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
 ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
 ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
```

Intended H' is the output-deletion map above. Active frame equalities are derived
from ld_sync_active, not new hypotheses. This consumer remains unproved; further
assembly uses existing ld_sync_ordinary_advance and Locations. The separate
current-state safety consumer must omit target OK entirely and conclude
raw_mem_ok C' (FST (lower_dload_function_supply f.lf_supply fn)) inst t,
using the same sync/global/shape/discipline/headroom and non-revert premises.
This is a proposed target, not an existing certificate.

Diagnostic conclusion: no concrete frozen-hypothesis mismatch was established.
Full CALL request equality IS an invalid intermediate goal; the correct boundary
is equal observable completion with masked state adoption. The next proof work
should validate these selector/empty-mask/update boundaries before attempting the
grouped effect or any exhaustive target-prefix theorem. Integrity check:
`holbuild(targets=[lowerDloadSafetyWriteCoverageTheory])` passed (TO_m3618),
with no edits to executable proof source during this diagnostic.

## Checked CALL/STATICCALL live-successor boundary (C1.11.5.58)

`lowerDloadOracleCallCoverageTheory` now exports
`ld_sync_oracle_call_advance` and `ld_sync_oracle_call_coverage_ambient`.
The former consumes the unique `ld_sync_oracle_call_effect` supplier from
`lowerDloadOracleCallAssemblyTheory`, `ld_envelope_singleton_next`, and
`ld_sync_ordinary_advance`. It retains the effect's existential selected map H'
and uses `step_prov PG G inst ss` (not the old G) at the successor. No equality
between H' and the internal output-deletion witness is asserted: allocation
identity erasure need not be injective. `ld_sync_current_bb` is a small sync
projection; consumers do not unfold sync.

The ambient consumer derives source shape and distinct labels from
`ld_sync_fn_shape`/`o1_fn_shape_components`, uses
`ld_sync_ordinary_envelope`, then reconstructs `ld_pair` with `ld_pair_zero`.
Configured supply and function stack order are preserved independently of H'.
Both conclusions require a successful target step AND an active target next
instruction; source next-active is derived from that target location, never
from source success alone.

This supersedes the unproved-consumer wording above only for CALL/STATICCALL.
DELEGATECALL, CREATE and CREATE2 are not covered by this certificate. Neither
terminal successors nor failing current calls nor revert-forward alternatives
are handled here. Non-revert, sync/global and source ambient certificates remain
explicit premises. Full target-prefix coverage and the frozen memory theorem
remain outstanding. Build of the new helper and task target passed together
(TO_ld_mem-20261104T033958Z_m4262_t001); the latter is not cheat-elimination evidence.

## Reconciliation after grouped arithmetic and reads (.64)

Baseline: 6177a2709. The initial table is a historical local-effect inventory;
this section supersedes its assembly statuses. Exhaustive constructor universe
rechecked against venomInstScript.sml:23-69. No frozen theorem completion is claimed.

### Checked consumers (do not reprove)

* Arithmetic: ld_sync_arithmetic_effect / ld_sync_arithmetic_coverage in
  lowerDloadSafetyArithmeticCoverage. Exactly the scalar/ADD/SUB/shift union;
  excludes unsigned comparisons. Sync/global, context shape, pointer discipline,
  pointer witness and target OK suffice for effects; coverage also needs target
  active successor, nonterminator/nonexpansion exclusions, supply and stack order.
* Observational reads: ld_sync_observational_read_effect / coverage in
  lowerDloadSafetyReadCoverage. Exactly environment read0, keyed environment,
  account introspection, SLOAD/TLOAD union. Same consumer premises as arithmetic.
* MSTORE/MSTORE8/MCOPY: ld_sync_memory_write_coverage_ambient in WriteCoverage;
  headroom mem_inv and non-forward premises remain explicit. Empty copy is covered.
* CALL/STATICCALL: current source exports ld_sync_oracle_call_coverage in
  OracleCallCoverage:9, using generic OrdinaryCoverage. This supersedes the older
  .58 names/implementation description above; no duplicate advance consumer is
  presently required. Headroom and non-forward premises remain explicit.

These are successor-location certificates, not current-instruction raw safety
or arbitrary target-prefix coverage. OrdinaryCoverage:ld_sync_ordinary_coverage
is the sole common unchanged-instruction adapter, accepting an existential source
success, H', updated vars/memory/nonghost, erasure/range, unchanged allocation and
control projections. Its target-next premise supplies the source next location.

### Residual interface table

| Family | Exact existing producer and unsupplied boundary | Missing output |
|---|---|---|
| ASSIGN | ld_assign_effect (AssignSteps:78); needs labels, membership, vars/memory/nonghost; selected H'=set_prov H outputs (first_prov H operands) | synchronized effect + ordinary coverage; range via existing first_prov selected-range boundary (currently local in ArithmeticCoverage) |
| LT/GT/EQ | ld_comparison_effect (ComparisonEffects:172); access_ok, global, FDOM A=ld_slots A frames and target endpoint bound in addition to ordinary vars/shape/ptr/taint | synchronized effect + ordinary coverage; no non-forward premise needed |
| MLOAD/ILOAD | ld_mload_effect (MloadEffects:89), ld_iload_effect (IloadEffects:66); access_ok, non-forward, endpoint bound; ILOAD additionally fn_ptr_ok | grouped synchronized effect + ordinary coverage |
| PARAM | ld_param_effect (ParamEffects:103); selected Q positions must belong to P fn_name; not a consequence of ld_vars alone | derive selected-position premise or preserve it at call setup, then sync/coverage; H' uses selected q, not always NONE |
| RETPC_PARAM | ld_retpc_param_effect (RetpcEffects:39); membership/vars/memory/nonghost; output opaque | sync/ordinary coverage, NONE provenance |
| PHI batch | ld_phis_effect (PhiEffects:53); EVERY member, shared predecessor/labels, successful target eval_phis; snapshot semantics | block entry/envelope synchronization; not ordinary sequential coverage (PHI base is Error) |
| SSTORE/TSTORE | ld_storage_write_effect (StorageWriteEffects:75); operands=[a;v], outputs=[], equal key evaluations, masked value agreement | operand/shape assembly then synchronized effect and ordinary coverage; H unchanged |
| CALLDATACOPY/CODECOPY/EXTCODECOPY | no complete producer; classify destination, equal scalar length/source offset, equal calldata/code/account bytes | semantic effect, sync and coverage |
| RETURNDATACOPY | no ordinary producer; in-bounds read and destination classification; forwarding branch loses paired memory | ordinary effect/coverage OR explicit terminal suffix witness |
| ISTORE | no complete producer; scalar offset plus masked word, memory and immutable taint bookkeeping | effect, sync and coverage |
| SHA3/LOG | no complete producer; untainted/classified source bytes for hash; log history omitted but operands/access still needed | effects, sync and coverage |
| INITIAL_FMP/BUMP | no complete producer; not excluded by fmp_free_ctx; BUMP two outputs | effects, sync and coverage |
| NOP/ASSERT/ASSERT_UNREACHABLE | no complete producer; identity on successful branch with ghost normalization; assertions need equal scalar untainted guard | effects/successor coverage plus Abort classification |
| DELEGATECALL/CREATE/CREATE2 | not covered by OracleCallCoverage; external empty-mask observation boundaries exist, not complete opcode producers | concrete EVM effect producers, sync and coverage |
| ALLOCA | maps/interval/charge infrastructure in Relation and ScratchSafety, not full assembled step | allocation-aware transition, selected output/map insertion, successor |
| DLOAD/DLOADBYTES | conditional expansion prefix raw safety in ScratchSafety/ConfiguredOrigins | expansion phase transport and completion, E/A updates, next location |
| JMP/JNZ/DJMP | no control producers; equal scalar selectors, successful destination and PHI batch | jump/block reachability and envelope reconstruction |
| RET/INVOKE | no general recursive call transport; RET uses IntRet not OK, final opaque token not compared | push/pop (.7), reachable source return witness and target-run induction (.8) |
| STOP/SINK/RETURN/REVERT/SELFDESTRUCT/INVALID | terminal, no ordinary OK successor | active raw safety and terminal classification; forward suffix where applicable |
| excluded FMP/DALLOCA family | historical exclusions in table above unchanged | transport source exclusion to transformed origin, not new effects |

### Proposed next grouped consumer interfaces (not theorems yet)

1. ASSIGN and RETPC_PARAM: same sync/global/shape/discipline + target OK interface
   as arithmetic, union [ASSIGN;RETPC_PARAM], existential H' (first_prov versus
   NONE). Reuse first_prov range helper by making the unique task-created helper
   public if authorized, rather than copying it. Apply OrdinaryCoverage once.
2. Classified reads/comparisons: union [MLOAD;ILOAD;LT;GT;EQ], arithmetic ambient
   premises plus mem_inv dload_headroom_ok C vs0 and non-forward. Extract access
   from sync/source discipline, slots from sync, bounds from ambient headroom.
   Export existential H'=set_prov H outputs NONE and common effect conclusion,
   followed by ordinary coverage. Non-forward is unnecessary for comparisons
   alone, so do not silently narrow its independent producer.
3. Storage writes: same arithmetic ambient interface for [SSTORE;TSTORE]; derive
   source shape outputs=[], source/target scalar key and masked value using
   WriteAssembly observation boundaries. Keep H'=H and feed ordinary adapter.
4. PARAM remains distinct until selected-position ownership is validated. PHI,
   allocation, expansion and jumps are structurally distinct, not extra cases
   to force into unchanged singleton coverage.

### Prefix ownership and remaining safety gap

PLAN C1.11.7 owns conditional push/pop: fresh serial and selected Q at entry;
return restricts A, restores caller frontier, and uses current callee memory and
taint. It must not assume a terminating source run. C1.11.8 owns recursion-matching
target-run induction producing a source frame_reachable IntRet witness, then
raw_reachable entry/next/block/callee rule coverage under exactly frozen
antecedents, existentially hiding lo/P/Sigma/ghosts. These are still unproved.

The final relation assertion must distinguish ld_pair from explicit target-only
forward suffix; ld_forward_prefix_raw is checked but does not establish the
witness for every relevant reachable state. Current raw safety is required even
when the active instruction subsequently Error/Abort/Halt. Neither checked
arithmetic/reads nor CALL/STATICCALL successor consumers prove that obligation.
No counterexample to the frozen statement has been established by this audit.

### Classified read consumer reconciliation (C1.11.5.66)

`lowerDloadSafetyClassifiedReadCoverage` now exports
`ld_sync_classified_read_effect` and `ld_sync_classified_read_coverage` for exactly
[MLOAD;ILOAD;LT;GT;EQ]. These discharge the two classified-read/comparison rows
above. The additional ambient premise is `mem_inv dload_headroom_ok C vs0`;
non-forward is required conditionally only for MLOAD/ILOAD. Active pointer
validity comes from synchronization, without an extra context-wide pointer
witness hypothesis. Target selected endpoints follow from slots/maps and ambient
headroom. H' is witnessed by `set_prov H inst.inst_outputs NONE`; coverage uses
the common OrdinaryCoverage adapter. This is successful live-successor coverage
only: current raw safety, terminal alternatives, control and target-prefix
integration remain open as described above.
