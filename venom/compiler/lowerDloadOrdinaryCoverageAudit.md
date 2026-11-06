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

### Storage write consumer reconciliation (C1.11.5.67)

`lowerDloadSafetyStorageWriteCoverage` exports `ld_sync_storage_write_effect`
and `ld_sync_storage_write_coverage` for [SSTORE;TSTORE], discharging the storage
write row above. Local operand assembly proves equal scalar keys and masked
(rather than equal) values; selected provenance stays H'=H. The common ordinary
adapter is used once. No headroom or non-forward premise is needed. As with the
other grouped consumers, this does not discharge current raw safety, control,
terminal alternatives or exhaustive target-prefix integration.

### Identity/assertion consumer reconciliation (C1.11.5.68)

`lowerDloadSafetyIdentityCoverage` exports `ld_sync_identity_effect` and
`ld_sync_identity_coverage` for exactly [NOP;ASSERT;ASSERT_UNREACHABLE].
Successful target assertions have equal scalar, untainted source guards; both
physical states are unchanged. Empty outputs normalize provenance and all taint
components; H'=H. The common ordinary adapter supplies the successor location.
No headroom, non-forward, or extra scalar-equality premise is required. Failed
assertions (Abort), malformed/undefined guards (Error), current raw safety,
control, PARAM ownership and exhaustive target-prefix coverage remain open.

## Selected PARAM ownership checkpoint (C1.11.5.69)

Consumer: `ld_param_effect` (ParamEffects:103-131) requires exactly
`!j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==> j IN P f.lf_fn.fn_name`.
It is needed to put PARAM's selected output in `fn_pv`, not to prove numerical
parameter agreement. Do not replace it by equal erased allocation pairs.

### Current clauses and the candidate sync projection

Relation:47-66 constrains H's domain to `fn_pv` and relates parameter values by
Q, but has no static positional constraint on Q. Relation:123-153 identifies
PG with Q's OPTION_MAP erasure and saved cf_params with saved Q's erasure.
Global:119-120 proves selected identities live, not positional permission.
`EVERY(fn_ptr_ok P)` is already a sync clause; adding it again supplies no
new reachability fact. A direct projection/simplification proof of the proposed
ownership candidate therefore has no supplying clause. This is NOT a checked
counterexample to the candidate: sync also contains source frame_reachable,
which could support a new semantic provenance-support induction. No such
induction theorem is currently supplied by ptrDiscipline. In particular it
would have to carry support of G, ownership of PG, and saved caller ownership
jointly; erased PG equality alone is not that induction.

### Establishment and preservation table (exact existing interfaces)

| Site | Existing checked interface | Remaining ownership obligation |
|---|---|---|
| Root | `ld_sync_entry` returns sync with stk=[], PG=[], G=FEMPTY; witness at Entry:54-56 has Q=[]; `ld_sync_source_entry` obtains P from o1_src_inv | Empty Q is vacuous even when initial vs_params is nonempty. Export through PG=[] and MAP length, or retain concrete entry witness. No new initial-state assumption needed. |
| INVOKE selection | `ld_arguments_permission`: ld_vars P A f /\ ptr_use_ok P (fn_pv P f.lf_fn) inst /\ opcode=INVOKE /\ decode_invoke inst=SOME(nm,args) /\ k<LENGTH args /\ EL k (MAP(op_prov H) args)=SOME a ==> k IN P nm | Construct callee Q as exactly MAP(op_prov caller.H) args, and identify callee.fn_name=nm via lookup. `fn_ptr_ok_def` supplies ptr_use_ok from source inst membership; `ld_arguments_erasure` supplies PG equality; `ld_arguments_live` supplies liveness, independently. No new pointer argument observation lemma needed. |
| Source call rule | frame_reachable_call (ptrDiscipline:484-494) sets PG=MAP(op_prov G) ops and saves caller PG in cf_params | This matches selected Q via `ld_arguments_erasure`, but does not itself assert ownership. Use permission at selected call construction, not inverse lookup of (base,size). |
| Ordinary / PARAM / block / expansion | All frame updates retaining lf_fn and lf_Q preserve the ownership formula by substitution; PARAM updates H, not Q | Retain ownership for EVERY saved frame, not just active HD; the ordinary adapter's existing ld_pair conclusion does not expose such an invariant. Any caller that needs ownership after that adapter must track it alongside the chosen frame witnesses, or obtain a separate source-reachability theorem. |
| Return | frame_reachable_ret (ptrDiscipline:495-508) restores f.cf_params and f.cf_fn; sync's saved-frame equations identify these with saved selected frame Q/function | Tail-frame ownership must have been retained while callee was active. Current callee Q cannot justify caller permission. Erasure restriction on A changes no Q positions or fn names. |

### Minimal invariant proposal, not a new definition or theorem

Carry alongside the coverage witness the single stack-wide formula
`EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
                   j IN P f.lf_fn.fn_name) frames`.
This is sufficient for the PARAM producer via HD; it is not a new hypothesis
of the frozen theorem. Establish it at the root (empty Q), push it using
`ld_arguments_permission`, preserve it when only src/tgt/H/tv/E change, and
recover it on pop via EVERY's tail. Configured supply, serial, A and erasure
changes do not affect it. No relation definition has been modified here.

Concrete next decomposition for strategist review: (1) prove unique empty,
frame-update, push and pop ownership boundaries in a task-created helper theory,
using existing Arguments permission rather than copying it; (2) choose explicitly
whether target-prefix witnesses carry the extra stack-wide formula, or instead
prove the larger joint source provenance-support induction and derive ownership
from sync. The first route is smaller but requires revising task-created
coverage witness interfaces at their ownership threading points; a conditional
PARAM coverage theorem alone is not a solution. Neither route is implemented
or asserted proved by this diagnostic. No counterexample to the frozen contract
has been produced. Terminal/current-state raw safety remains separate.

## Correlated ownership integration audit (C1.11.5.74)

This section supersedes the *unimplemented ownership proposal* at .69 above;
that historical diagnostic is not a claim about the current interfaces.
The invariant is still explicit syntax, not a new definition. Its quantifiers
are `?stk PG G tn fn inst s t0 A frames N X p h`; inside them lie sync, global,
configured supplies, active name order, image equality, envelope, prefix and
`ti = EL h X`, followed by stack-wide selected-Q permission on **frames**.
The same P is used in sync and permission. There is no independently quantified
ownership stack and no ownership assumption added to the frozen theorem.

### Checked establishment/preservation signatures

| Boundary | Exact supplying signature/source | Operational status |
|---|---|---|
| Root | `ld_sync_source_entry` (Entry:65-86) supplies `?lo P f`, reservation/discipline/static pointer witness, `f.lf_fn=fn`, configured `f.lf_supply=u`, `f.lf_Q=[]`, sync and global on `[f]`. | Entry source synchronization checked. Permission follows from Q=[]; selecting u=Sigma fn_name supplies configuration. Full target entry/image/location assembly still must use stage lookup/entry alignment and `ld_owned_pair_zero`; source entry alone does not do this. |
| Frame replacement | `ld_ownership_replace`: Own(f::fs), g.fn=f.fn, g.Q=f.Q imply Own(g::fs). | Algebra only; no semantic step supplied. |
| Ordinary advance | `ld_sync_ordinary_witness` exposes `newframe` with the same fn/Q and updated src/tgt/H/tv; `ld_sync_ordinary_owned_coverage` (OrdinaryCoverage:135-179) takes Own(f::fs), sync/global/shape, non-expansion non-control opcode, successful target/source steps, unchanged allocations/frontiers/block fields, new vars/memory/nonghost/erasure/range, target next active location, supply/name order. | Produces the full correlated existential above at the next target index. No family-by-family owned wrappers are necessary. Concrete effect producers must be applied before this adapter. |
| PARAM | `ld_sync_param_effect` (ParamCoverage:10-52) takes sync/global/Own, opcode=PARAM and target OK; returns source OK and all ordinary effect fields including selected H' liveness. `ld_sync_param_owned_coverage` (:54-85) additionally takes shape, target next active instruction, supplies/name order. | Concrete successful PARAM coverage checked, with Own inside the returned existential. This closes the PARAM ownership seam, not exhaustive opcode coverage. |
| Initial prefix | `ld_owned_pair_zero` (OwnedLocations:38-67) takes sync/global/config/order, distinct source labels, image equality, target active instruction and Own. | Packages the same frames at expansion h=0 using `ld_pair_zero_witness`. Does not simulate an expansion instruction. |
| Arbitrary prefix packaging | `ld_owned_prefix_pack` (OwnedLocations:8-36) takes all existential-body conjuncts, including existing prefix and Own. | Existential introduction only; no prefix advancement or completion. |
| INVOKE push | `ld_ownership_push_saved` (OwnedLocations:82-98) takes Own(caller::fs), saved fn/Q unchanged, caller vars and ptr_use_ok, INVOKE decoding `(nm,args)`, callee fn_name=nm and Q=MAP(op_prov caller.H) args. | Proves Own(callee::saved::fs) using `ld_arguments_permission`; operational call setup, allocation maps, sync and target/source recursion remain unimplemented consumers. |
| Return pop | `ld_ownership_pop` (OwnedLocations:71-80) takes Own(callee::saved::fs) and restored fn/Q=saved fn/Q. | Proves Own(restored::fs). Allocation restriction, erasure, memory/taint and actual source reachable return are separate obligations. |
| Forgetting | `ld_owned_coverage_pair` (OrdinaryCoverage:182-198) takes the entire correlated existential and concludes `ld_pair`. | One-way forgetting boundary only. Cannot recover Own from ld_pair. |

### Remaining operational consumers and exact frame transformations

* Ordinary unchanged-allocation families already have several sync effect
  producers (arithmetic, assignment/RETPC, classified reads, storage writes,
  identity/assertions, oracle CALL/STATICCALL and reads). Their existing ld_pair
  wrappers intentionally forget witnesses. New reachability induction must call
  the producers and `ld_sync_ordinary_owned_coverage` directly. It must NOT use
  those wrappers and then invent a separate owned stack. No such induction is
  implemented in the current task target. Copy/ISTORE/hash/log/remaining external
  calls/FMP interfaces still need complete effects as inventoried above.
* JMP/JNZ/DJMP/block PHIs: replace the head retaining fn/Q; establish source
  destination and PHI-batch step, new ghost/taint/vars, block and envelope alignment.
  `ld_phis_effect` is not a full owned block transition.
* Original ALLOCA: replace head retaining fn/Q, extend A and H by the selected
  original identity, preserve saved frames/maps/memory and global constraints,
  and reconstruct the successor envelope. Ownership replacement alone does not
  establish any allocation invariant.
* DLOAD/DLOADBYTES prefixes: retain the pre-expansion sync frames while h advances;
  completion replaces head retaining fn/Q and updates scratch E/charge and state.
  Checked conditional raw-prefix safety does not supply semantic prefix coverage
  or the completed synchronized successor.
* INVOKE: push `callee::saved::fs`, selected Q exactly MAP(op_prov caller.H) args;
  retain caller permission via saved fn/Q and use decoded nm equality for callee
  permission. Need concrete setup, new serial/maps, saved ghosts, active-stack
  charge and full sync/global/envelope. No source termination assumption allowed.
* Return: pop to restored saved tail, preserving its fn/Q. Need actual target-run
  induction to obtain source IntRet/frame_reachable_ret, caller frontier restore,
  map restriction, and current (not saved) memory/taint agreement.
* Terminal/failing-current states: keep owned sync/prefix coverage where available,
  or the separate target-only forward suffix disjunct. No fabricated owned frame
  witness is needed for that suffix. Successful OK successor lemmas do not prove
  safety before Error/Abort/Halt or terminal classification.

### Verification and scope

Build TO_ld_mem-20261104T190123Z_m5109_t001 checked OwnedLocations, PARAM,
Arithmetic, Assignment, ClassifiedRead, Read, StorageWrite, Identity and the
current task target. This is a passing build, NOT a zero-cheat certification:
`o1ContractLowerDloadMemScript.sml:23` still contains the original cheat and its
frozen theorem has not been changed. The target does not yet import the helper
coverage assembly. No counterexample has been verified. Remaining full coverage
and terminal integration require the next strategist-owned phase, not more
ownership algebra or redundant opcode-union wrappers.

## Operational block successor diagnostic (C1.11.5.78)

Status: **statement proposals only**, not exported HOL theorems. No control
simulation is certified by this section. Baselines: RootCoverage builds
(TO_ld_mem-20261104T190123Z_m5280_t001); actual PHI theory is
`lowerDloadSafetyPhiEffects`, which builds
(TO_ld_mem-20261104T190123Z_m5288_t001).

### Actual rule and finite dispatch audit

`frame_reachable_block` (ptrDiscipline:476-482) requires reachable source inst,
source activity, is_terminator, source step OK, source nonhalting poststate,
source enters_block, and activity in the entered source state. It keeps stk/PG,
sets G to `entry_prov fn ss G`, and tn to `entry_taint_vars fn ss tn`.
There is NO ordinary step_prov/step_taint update and NO SUC-index continuation.
`enters_block` (contextCodegenRel:248-253) looks up the destination, evaluates
parallel PHIs from the original snapshot, then overwrites the index with
`phi_prefix_length bb.bb_instructions`.

For successful nonhalting OK terminators, only JMP/JNZ/DJMP remain. Dispatch
(venomExecSemantics:638-666,739-801,1046ff) gives: JMP jumps to its syntactic
label; JNZ evaluates one word and tests nonzero; DJMP evaluates one word, uses
w2n as an index, checks the extracted label list and its bound. RET/RETFMP/DRET
return IntRet or Error, STOP/RETURN/SINK/SELFDESTRUCT return Halt (or Error),
REVERT returns Abort/Error, INVALID returns Abort. DRET is additionally excluded
by o1_fn_shape.no_dret; its exclusion is not needed for this dispatch split.
Do not exclude PHIs globally: o1_fn_shape requires first_block_no_phi only.

### Exact proposed operational consumer

The following is a HOL term proposal (free variables implicitly universal),
not source code to admit or a new invariant definition. Its antecedent uses a
synchronized original boundary; a reachability induction must first reduce a
terminator's singleton prefix to that boundary. `o1_src_inv D C vs0` is an
existing frozen premise supplying source taint safety; no source successful-run
hypothesis or scalar equality assumption is added.

```sml
ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
ld_global lo A (f::fs) /\ o1_ctx_shape C /\ o1_src_inv D C vs0 /\
EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
(!j k. j < k /\ k < LENGTH (f::fs) ==>
  list_precedes (EL j (f::fs)).lf_fn.fn_name
                (EL k (f::fs)).lf_fn.fn_name names) /\
EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
  j IN P f.lf_fn.fn_name) (f::fs) /\
is_terminator inst.inst_opcode /\
step_inst fuel C' inst t = OK ts /\ ~ts.vs_halted /\
enters_block (ld_image f) ts t1 /\ active_inst (ld_image f) ti t1 ==>
?stk' PG' G' tn' fn1 inst1 s1 t0 A' frames N' X p h.
  ld_sync lo P C vs0 stk' PG' G' tn' fn1 inst1 s1 t0 A' frames N' /\
  ld_global lo A' frames /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
  (!j k. j < k /\ k < LENGTH frames ==>
    list_precedes (EL j frames).lf_fn.fn_name
                  (EL k frames).lf_fn.fn_name names) /\
  ld_image f = ld_image (HD frames) /\
  ld_envelope (HD frames).lf_supply fn1 s1 s1.vs_inst_idx X p /\
  ld_prefix C' (ld_image f) X p h t0 t1 /\ ti = EL h X /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) frames
```

Intended witnesses are stk'=stk, PG'=PG, A'=A, N'=N, fn1=fn,
G'=entry_prov fn ss G, tn'=entry_taint_vars fn ss tn, and t0=t1.
Only the head frame changes; h=0 at the next envelope (not index zero).
This is exactly the RootCoverage existential body with successor target t1,
not ld_pair plus a separately quantified ownership witness.

### Proposed schematic block-entry transport boundary

This second proposal factors parallel entry effects from reachability and
location packaging. Poststates ss/ts are schematic terminator results: the
boundary must NOT unfold step_inst or demand equal vars/parameters. Selected
PHI provenance is polymorphic `phis_prov` applied to H; there is no inverse
lookup of erased allocation pairs. It introduces no new definitions.

```sml
f.lf_fn = fn /\ f.lf_src = ss /\ f.lf_tgt = ts /\
f.lf_tv = tn.t_var /\
ld_vars P A f /\ ld_memory lo A tn ss ts /\ ld_nonghost tn ss ts /\
ss.vs_prev_bb = ts.vs_prev_bb /\ ss.vs_current_bb = ts.vs_current_bb /\
ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
(!a. a IN FRANGE f.lf_H ==> a IN FDOM A) /\
enters_block (ld_image f) ts t1 ==>
?s1 H'. enters_block fn ss s1 /\
  ld_vars P A (f with <|lf_src := s1; lf_tgt := t1; lf_H := H';
    lf_tv := (entry_taint_vars fn ss tn).t_var|>) /\
  ld_memory lo A (entry_taint_vars fn ss tn) s1 t1 /\
  ld_nonghost (entry_taint_vars fn ss tn) s1 t1 /\
  entry_prov fn ss (ld_erase A o_f f.lf_H) = ld_erase A o_f H' /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) /\
  s1 = ss with <|vs_vars := s1.vs_vars; vs_inst_idx := s1.vs_inst_idx|> /\
  t1 = ts with <|vs_vars := t1.vs_vars; vs_inst_idx := t1.vs_inst_idx|>
```

The update equalities expose all unchanged non-variable/non-index fields
without requiring consumers to repeat PHI implementation unfolding. This helper
intentionally does not claim source activity or envelope alignment; those are
positional facts about the generated blocks and must be supplied separately.

### Premise-by-premise proof map / remaining gaps

1. Source function/member/active/ptr witness come from ld_sync_source and
   ld_sync's EVERY clauses. Shape gives distinct block labels, fn_shape_ok and
   instruction wellformedness via existing sync/shape projections. Labels and
   halted equality are ld_nonghost projections, not additional ambient premises.
2. Source terminator success/destination is NOT checked yet. For JMP the same
   syntactic label suffices. For JNZ/DJMP the tested/selected word must agree:
   ld_ptr_use_scalar excludes pointer variables (no pointer preserving op or
   memory ranges), taint_ok excludes tainted inputs, and opaque_use_ok excludes
   retpc use. Apply ld_vars_numeric_operands_equal (Values:236-245), or its
   operand boundary, using source taint from o1_src_inv/ptr_discipline and actual
   frame_reachable. Target OK supplies shape and definedness. No equality of
   arbitrary pointer words is available or needed. Both results are jump_to
   the same label: matching prev/current bb, unchanged vars/allocas/frontiers,
   memory and other metadata. Fuel and context are irrelevant for these base
   instructions, but the step_inst dispatch fact still needs a checked boundary.
3. Entry lookup must pair the destination blocks using indexed correspondence
   lower_dload_function_supply_block_at (ConfiguredOrigins:70ff) and distinct
   labels, NOT inverse active_inst membership. Existing
   lower_dload_insts_supply_phi_prefix (o1ContractLowerDload:437-442) establishes
   PHI-prefix ordering ONLY; it does not assert equality of prefix length or
   eval_phis. Need a checked leading-PHI identity/evaluation transport fact for
   supplied instruction lists. PHIs are singleton unchanged expansions; first
   non-PHI expands to non-PHIs. This makes the two PHI batches identical.
4. ld_phis_effect (PhiEffects:53-81) then supplies source eval_phis, new ld_vars,
   memory, nonghost and erasure commutation. It needs EVERY member in source
   fn_insts, equal labels/prev_bb and tn.t_var=lf_tv; all derive from the paired
   block and pre-entry frame. Use the pre-PHI snapshot throughout, never feed
   an updated variable into a later PHI. ld_phis_only_vars gives the schematic
   update equalities. FRANGE H' subset FDOM A still needs a finite-map induction
   through set_prov/phi_prov, selecting only old H entries (no new identities).
   ld_phis_effect does NOT export that range fact.
5. Apply frame_reachable_block only after source entry AND source activity are
   proved. Activity requires the entered source prefix index be in bounds:
   target activity at its PHI-prefix index plus generated-block correspondence
   and nonempty expansions imply a non-PHI source instruction exists there.
   RootCoverage's index-zero origin is inapplicable when PHIs exist. Need the
   envelope at j=phi_prefix_length source instructions and generated offset
   p=phi_prefix_length target instructions. Because leading PHIs are unchanged,
   p=j at this entry; neither need be zero. The next instruction can be DLOAD,
   so recover X (possibly four instructions), not a singleton assumption.
6. Form the replacement head with source s1, target t1, H', new t_var. Q, fn,
   supply, serial and E stay unchanged. Allocations/frontiers/params unchanged
   by jump+entry keep maps, slots, intervals, charge and saved-stack equations.
   ld_global numerical clauses are unchanged and its H range clause uses item
   4. Saved frames use CURRENT memory taint; entry changes only t_var, so their
   existing memory premises do not require a new saved-memory invariant.
7. Configured supply and name order are unchanged. ld_ownership_replace retains
   positional permission on this SAME replacement head::fs. With the new sync,
   global, image and target activity, ld_owned_pair_zero packages h=0 and the
   full correlated existential. Do not first forget to ld_pair.

Implementation is deliberately deferred for strategist review of these missing
interfaces. Control (this consumer), original allocation, generated prefixes,
INVOKE/return and failing/terminal/current-instruction safety remain unfinished;
.74's remaining-case ledger remains authoritative subject to the later checked
ISTORE reconciliation. No theorem statement/definition was changed and the
frozen contract's cheat remains unresolved.

### Checked block-entry effect and corrected dependency inventory (.79)

The .78 inspection missed existing stronger structural interfaces in
`lowerDloadConfiguredOriginsScript.sml`: `lower_dload_insts_supply_phi_length`
(:127ff) already proves PHI prefix length equality, and
`lower_dload_insts_supply_eval_phis` (:152ff) proves evaluation identity.
`lower_dload_function_supply_enters_block_origin` (:244ff) already combines
inverse lookup, those identities and entry packaging. These are reused, not
copied or reproved. Thus items 3 and the leading-PHI part of 4 above were
missing from the diagnostic inventory, NOT missing from source reality.

`lowerDloadSafetyUpdates` now exports `ld_set_prov_range`,
`ld_phi_prov_range`, and `ld_phis_prov_range`; the latter is exactly
`FRANGE (phis_prov prev H ins) SUBSET FRANGE H`. Selection reads original H,
not the recursively updated map. `lowerDloadSafetyEntry.ld_entry_effect`
exports the proposed schematic boundary without new hypotheses or definitions.
It reuses enters_block_origin and ld_phis_effect and exposes vars/index-only
poststate updates. This establishes selected range/erasure, source entry and
post-PHI vars/memory/nonghost; it does not establish source activity or sync.

Still unimplemented: successful terminator dispatch/destination reconstruction,
post-entry source active/envelope reconstruction at PHI-prefix length,
frame_reachable_block and same-frame owned coverage assembly. All allocation,
expansion, call/return and terminal/current-raw integration obligations listed
above also remain. No change to the frozen theorem or its original cheat.

## C1.11.5.80: successful branch destinations

`lowerDloadSafetyControl.ld_control_destination` proves a single combined
JMP/JNZ/DJMP boundary. Premises are `ld_vars P A f`, source/target labels
equality, `fn_shape_ok f.lf_fn`, `fn_ptr_ok P f.lf_fn`, source instruction
membership, source `taint_ok` with `tn.t_var = f.lf_tv`, opcode membership
in `[JMP; JNZ; DJMP]`, and target `step_inst fuelT CT inst f.lf_tgt = OK t1`.
Conclusion: some `lbl` satisfies `t1 = jump_to lbl f.lf_tgt` and
`step_inst fuelS CS inst f.lf_src = OK (jump_to lbl f.lf_src)` for arbitrary
source fuel/context. Selector equality is pointwise `eval_operand` equality;
no successful whole-list evaluation is assumed for label-bearing operands.
This resolves destination reconstruction only. Successful block entry, PHI
source activity, envelope, correlated ownership/synchronization packaging,
and general target reachability remain unproved integration obligations.

## C1.11.5.84: original ALLOCA successor interface audit

Status reconciliation: .81-.83 now prove entry active/envelope inversion,
branch effects and correlated owned branch/PHI-entry coverage, respectively.
`lowerDloadSafetyControlCoverage.ld_sync_control_owned_coverage` explicitly
requires the continuing target successor `~ts.vs_halted`. It uses the shared
`lowerDloadSafetyAdvance.ld_sync_head_update`, also consumed by ordinary
advance. Thus the block-entry gaps described above are closed locally, not
an exhaustive reachability proof. Original allocation is the next open case.

### Checked cached-site probe

`lowerDloadSafetyAllocation.ld_cached_alloca_pair` takes exactly
`ld_maps A f /\ inst.inst_outputs=[out] /\
 FLOOKUP f.lf_src.vs_allocas inst.inst_id=SOME(b,n)`.
It produces `c`, matching A and target lookups, both successful exec_alloca
results `update_var out (n2w b) f.lf_src` and
`update_var out (n2w c) f.lf_tgt`, and ld_maps for the updated frame.
Importantly, requested `szS` and `szT` are independently quantified. Cached
execution ignores BOTH requested sizes, including zero or values differing
from n. The proof consumes ld_maps_original and ld_maps_cached_original;
it does not duplicate their map proofs. Allocation maps/frontiers and BB
fields of these update_var results are unchanged by update_var_def.
This is checked execution/map evidence, NOT yet owned successor coverage.

### Exact effect / consumer candidate interfaces (NOT admitted theorems)

The notation in this section is only textual substitution, not new HOL
definitions. In both branches set `aid=inst.inst_id`, `k=(f.lf_serial,aid)`,
`H'=f.lf_H |+ (out,k)`, `tn'=step_taint inst s ss tn`,
`G'=step_prov PG G inst ss`, `sn=ss with vs_inst_idx:=SUC s.vs_inst_idx`,
`tt=ts with vs_inst_idx:=SUC p`, and
`g=f with <|lf_src:=sn; lf_tgt:=tt; lf_H:=H'; lf_tv:=tn'.t_var|>`.
The common preconditions are ld_sync lo P C vs0 stk PG G tn fn inst s t
A (f::fs) N, ld_global lo A (f::fs), o1_ctx_shape C, taint_ok fn tn inst s,
inst.inst_opcode=ALLOCA, inst.inst_outputs=[out], the singleton current
envelope ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p,
t.vs_inst_idx=p, and target step_inst fuel C' inst t=OK ts.
The semantic effect boundary belongs in lowerDloadSafetyAllocationScript.sml.

* Cached effect candidate: add FLOOKUP s.vs_allocas aid=SOME(b,n).
  Conclude there exist c,ss such that source step_inst fuel C inst s=OK ss,
  matching A/target lookups as in the checked probe,
  ss=update_var out (n2w b) s, ts=update_var out (n2w c) t,
  G'=ld_erase A o_f H', ld_vars P A g,
  ld_memory lo A tn' sn tt, ld_nonghost tn' sn tt, and
  (!a. a IN FRANGE H' ==> a IN FDOM A).
  A is unchanged; explicit poststate equalities give the other premises of
  ld_sync_head_update. No source/target requested-size equality is needed
  for exec_alloca. The step_inst adapter is simpler: target success forces
  inst.inst_operands=[Lit sz], so both sides use the very same literal.
* Fresh effect candidate: add FLOOKUP s.vs_allocas aid=NONE.
  Conclude there exist sz,ss such that both operand evaluations are the same
  sz, source step_inst fuel C inst s=OK ss, target site is absent,
  k NOTIN FDOM A, (!d. ~ld_private f d aid), and the two states are
  update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas:=s.vs_allocas |+ (aid,(s.vs_alloca_next,w2n sz));
              vs_alloca_next:=s.vs_alloca_next+w2n sz|>)
  and the analogous target state with t frontier. Put
  A'=A |+ (k,(s.vs_alloca_next,t.vs_alloca_next,w2n sz)).
  Required effect conclusions are G'=ld_erase A' o_f H', ld_vars P A' g,
  ld_memory lo A' tn' sn tt, ld_nonghost tn' sn tt,
  (!a. a IN FRANGE H' ==> a IN FDOM A'), and
  EVERY (ld_vars P A') fs plus preserved saved erasures. ld_maps for the
  head follows from ld_maps_fresh_original; tails must also be transported.

Owned-successor consumer (same candidate shape for either branch): add the
positional EVERY Q ownership premise on (f::fs), configured EVERY supply,
name order, active_inst fn next sn, and
(?Y. ld_envelope f.lf_supply fn sn sn.vs_inst_idx Y (SUC p)).
Conclude the EXACT existential body of ld_sync_control_owned_coverage,
with final target `tt`, target function `ld_image f`, and any active target
instruction at tt. In the cached case A stays A and frame g::fs; in fresh
case A becomes A' and frame g::fs. PG/stk are preserved only after the
saved erasure equalities below. The final packaging uses h=0 and Y, not
an assumed singleton next expansion. Place this consumer in a future
lowerDloadSafetyAllocationCoverage theory after effect/reconstruction checks.

### Premise-to-producer / changed-map table

| Obligation | Existing producer or precise missing boundary |
|---|---|
| Source/target active original site | ld_sync_active/source plus current envelope; ALLOCA is unchanged singleton supply expansion. Need operational adapter, not new pass structure. |
| Size operand defined / scalar equal | step_inst_base ALLOCA accepts ONLY [Lit sz]. Target OK supplies that syntactic form; no evaluation/taint/numeric-operand theorem is needed. Both sides use identical literal sz. Source step dispatch still needs proof. |
| Cached target lookup / successful execution | Checked ld_cached_alloca_pair. Actual n, not w2n requested size, is selected provenance size. |
| Source absence => target absence | ld_maps reverse clause permits private target entries. Must first exclude original aid from EVERY private generated ID by supply freshness and original instruction membership; source absence alone is insufficient. |
| k fresh in A | ld_sync FDOM A=ld_slots A frames, distinct serials, and source absence. ld_maps alone has no reverse-domain axiom for unused A entries. |
| Head fresh ld_maps | ld_maps_fresh_original requires both absences, k freshness and private exclusion, plus common sz executions. |
| Head intervals | ld_intervals_exec_alloca requires lo<=old frontier; derive from reachable-frontier boundary, NOT o1_run_state_ok alone. |
| Head vars including new selected output | Need allocation-output adapter to ld_vars update boundary; H' selects k, out in fn_pv, and wordrel uses b/c. Cached probe does NOT prove this. |
| Head G' erasure | step_prov/out_prov ALLOCA select poststate actual (base,size); show erasure of H' equals step_prov, using selected A lookup. |
| Head current tn' | step_taint/mem_taint/new_site_bytes: cached no new bytes; fresh interval entirely tainted. ALLOCA writes no memory. Do not equate stale fresh bytes. |
| Head ld_memory under A' | ld_memory_new_slot handles changed map only when old mask subset new and full new interval tainted; then update_var/index memory invariance. |
| Head ld_nonghost | ALLOCA changes vars/allocas/frontier, none compared by nonghost. Its taint-sensitive fields are t_imm/t_stor/t_trans; step_taint must leave these unchanged. |
| Every tail ld_maps A' | Need extension lemma for serial-distinct tail; new key cannot be a tail serial. Maps query A at every old source allocation. |
| Every tail ld_vars P A' | ld_wordrel_fresh_update already transports each old word relation when k NOTIN FDOM A. All selected H and Q in FDOM A by ld_global; fresh k changes none of their lookups. Domain/params remain unchanged. Need only a packaged vars/erasure extension boundary, not a duplicate wordrel theorem or per-frame replay. |
| Saved cf_prov and cf_params | ld_sync equates these with ld_erase A o_f H and MAP OPTION_MAP(ld_erase A) Q at each tail. Preserve erasure on all old supported identities under A'. cf_state/cf_tvar unchanged. |
| Head PG | Head Q unchanged, supported in FDOM A; preserve MAP OPTION_MAP(ld_erase A) Q under extension. |
| ld_slots / FDOM A' | Fresh head adds exactly k, tails unchanged; ld_slots_insert_head is existing numerical constructor, verify its premises rather than reprove. |
| ld_charge / every suffix frontier | E unchanged; both head frontiers grow by common w2n sz. Tail frontiers and charge unchanged. Cached invokes ld_sync_head_update; fresh violates its premises. |
| ld_global | Bounds/separation use old global numerical constraints and frontier extension; new zero-size site needs no positive-size assumption. Selected H' support is FDOM extension. Existing insert-head facts are conditional, not full sync reconstruction. |
| Supply/order/owned-Q | Frame fn, Q, supply, serial and E unchanged. Preserve same correlated witness, never independent ld_pair. |
| Successor source reachable / envelope | frame_reachable_next needs source OK; existing location boundary must cover next active instruction and supply offset. |

Minimal remaining package: (i) original-site freshness and successful allocation
operands/effects; (ii) one supported-map-extension transport boundary for H/Q,
wordrel/vars and saved erasures (reuse existing extension facts if already
present); (iii) fresh allocation-changing sync/global reconstruction; (iv)
correlated owned-successor consumer. Cached reconstruction can reuse
ld_sync_head_update once (i) supplies vars/provenance/taint effects. No new
definition, axiom, cheat, or speculative admitted theorem is introduced here.
Generated DLOAD scratch prefixes, INVOKE/return, failing/terminal states and
current raw safety remain separate outstanding obligations.

## C1.11.5.88: checked original-ALLOCA owned successor

`lowerDloadSafetyAllocationCoverageTheory` now exports
`ld_sync_owned_boundary_coverage` and `ld_sync_alloca_owned_coverage`.
The latter handles both cached and fresh original ALLOCA, retaining the same
correlated Q-ownership, supply and name-order witnesses. It is conditional on
the source next activity and next envelope, and target next activity; it does
not establish these location premises or current-instruction raw safety.
The next expansion is arbitrary Y, packaged at phase zero, not singleton.
Generated DLOAD scratch, call/return and exhaustive reachable coverage remain open.

An imported cached effect had a hidden kernel hypothesis despite earlier build
success. Its polymorphic cached-pair theorem is now type-instantiated before
druling, and only then specialized at the actual size. Type-instantiating the
ASSUME theorem produced by disch_then had changed that hypothesis and prevented
its discharge. The repaired effect is validated with VALID; permanent hyp=[]
checks cover cached pair/effect/advance, fresh advance and both owned-coverage
exports. Both allocation and allocation-coverage targets build with these checks.
No theorem statement or semantic definition changed in this repair.

## C1.11.5.89: reachability-induction compatibility audit

This is a source audit, not a coverage theorem. Rechecked unchanged allocation
and allocation-coverage targets with holbuild (TO_ld_mem-20261104T190123Z_m6207_t001).

### Actual elimination target and induction

`unitMemInvScript.sml:48-59,104-117` gives exactly

```
mem_inv M ctx vs0 <=>
  (?name fn lbl. ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl) /\
  !fn inst s. raw_reachable vs0 ctx fn inst s ==> M ctx fn inst s
raw_mem_ok ctx fn inst s <=>
  s.vs_alloca_next < dimword (:256) /\ inst_mem_ok_in_fn fn inst s
```

The relevant induction is `raw_reachable_ind`, generated by the four rules
in `venom/codegen/proofs/contextRawReachableScript.sml:26-57`. Its predicate
has arguments `vs0 ctx fn inst s`, all universally quantified. With the source
C, transformed C', lo, P, names and Sigma fixed, instantiate it by
`\v K fn' ti t. v = vs0 /\ K = C' ==> O fn' ti t`, where O is the
following *report abbreviation only*, not a proposed new HOL definition:

```
O fn' ti t =
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames
```

This is precisely the correlated existential exported by
`ld_owned_prefix_pack` (SafetyOwnedLocations:8-35), not bare ld_pair.
`ld_sync` (SafetyRelation:123-154) carries source frame_reachable, active
instruction, P well-formedness, selected provenance/parameter erasures,
serial freshness, live allocation domains, suffix frontier charges, suspended
source stack correspondence and memory/nonghost agreement. O additionally
retains global disjointness, configured supplies, stack order and Q ownership.
These are existentially correlated: do not separately obtain the last clause
from another witness. C's shape, ptr_discipline, stage freshness, headroom and
initial-state assumptions must stay fixed ambient hypotheses derived from
the frozen contract. They are not consequences of raw_reachable induction.

### Constructor map (actual rules, not imagined small-step rules)

| Actual rule | Target case | Existing boundary / remaining gap |
|---|---|---|
| entry, lines 27-36 | Target function entry and PHI entry | ld_owned_root_coverage (SafetyRootCoverage:31-70). Still supply stage entry lookup/original function and label distinctness from the ambient stage/shape. |
| next, lines 37-42 | Inside DLOAD/DLOADBYTES expansion, SUC h < LENGTH X | Keep the same source sync/frames/maps and extend ld_prefix using ld_prefix_extend (SafetyKernel:156). Must normalize arbitrary fuel to zero and align target index with p+h. No source step occurs. |
| next | Last instruction of singleton original expansion | Recover h=0, t=t0, ti=inst by ld_envelope_ordinary, ld_prefix_bound and ld_prefix_zero. Apply opcode owned coverage after deriving its effects and successor location. ALLOCA ledger below. |
| next | Last instruction of multi-instruction expansion | Must commit source DLOAD/DLOADBYTES step, allocation/scratch ghosts and taint to a new sync; existence of local scratch raw safety does not do this. No exhaustive owned completion theorem was identified. |
| block, lines 43-48 | JMP/JNZ/DJMP and successor PHIs | Singleton recovery followed by ld_sync_control_owned_coverage (SafetyControlCoverage:8-104), supplied source taint_ok. |
| callee, lines 49-56 | INVOKE callee entry | Requires singleton recovery plus paired decode/args/setup, push and entry with correlated ownership. Ownership push alone (SafetyOwnedLocations:82-98) is not the call-state constructor. |
| next, not a separate return constructor | Successful atomic INVOKE resumes caller | raw next permits INVOKE. Its target step contains a terminating internal run. The raw induction IH covers only the caller before the invocation, NOT that run or its return state. Needs a separate semantic-recursion induction with strengthened return postcondition; frame_reachable_ret needs a source IntRet witness. |
| no rule | IntRet, Error, Halt/Revert or no active successor | No successor coverage obligation, but current active instruction still needs raw safety. A halted block result cannot use block rule. Return is NOT a fifth raw_reachable constructor. |

Source `frame_reachable` is different (`ptrDisciplineScript.sml:456-509`):
next explicitly excludes INVOKE; call pushes a saved source frame; ret consumes
IntRet and bind_outputs/merge_callee_state and resumes the saved caller.
Consequently raw_reachable_ind alone is insufficient for the atomic INVOKE
case. O does retain a synchronized source boundary at all prefix positions,
but it does not retain a source *completed return* or an IH for the target's
nested run. This is an induction-strength gap, not missing ALLOCA arithmetic.
It must be resolved before claiming exhaustive coverage.

### Original ALLOCA branch premise ledger

Assume raw next's predecessor O fn' ti t, target `ti.inst_opcode = ALLOCA`,
step_inst fuel C' ti t = OK ts and target next activity. One must first split
whether ti is a generated scratch ALLOCA inside DLOAD or an original ALLOCA.
Opcode ALLOCA alone does NOT identify the source opcode! The following ledger
is only the original source ALLOCA branch after unpacking O and frames=f::fs.

| Premise of ld_sync_alloca_owned_coverage (SafetyAllocationCoverage:63-100) | Producer / status |
|---|---|
| sync, global, supply equality, order, Q ownership | Same unpacked O witness; frames nonempty follows ld_sync_active. |
| source inst opcode ALLOCA and source active | This branch test; active from ld_sync_source. |
| current singleton envelope, t.idx=p, ti=inst, t=t0 | Shape gives distinct block labels via ld_sync_fn_shape/o1_fn_shape_components. ld_envelope_ordinary proves X=[inst]; ld_prefix_bound gives h=0; ld_prefix_zero gives t=t0 and ti=inst. Current p=t0.idx is a head projection of ld_sync's envelope conjunct, using ld_sync_ordinary_envelope. |
| [Lit sz], [out] | Target successful step and ld_alloca_step (SafetyAllocation:28-36), then exec_alloca_def (venomExecSemantics:554-570). No taint equality needed for literal size. |
| MEM out (fn_ir_vars fn), out IN fn_pv P fn | Active member via ld_active_inst_member; fn_ptr_ok/ptr_use_ok gives ALLOCA output membership in fn_pv; fn_ir_vars includes outputs. Not supplied by raw next alone. |
| ir_supply_covers_fn f.supply fn | Must derive from stage configured supply Sigma and the original function; O has equality to Sigma but does NOT itself assert freshness. Keep ambient stage-supply coverage theorem. |
| ss equal to source case expression | Choose precisely the source exec_alloca result for sz, handling cached/fresh. exec_alloca succeeds once outputs=[out]; ld_alloca_step gives source step OK. No source-run success assumption is needed. |
| sn=ss with idx:=SUC s.idx; tt=ts with idx:=SUC p | Witness choices; raw next gives exactly target tt after t.idx=p. |
| active_inst fn next sn and successor envelope at SUC p | NOT additional induction assumptions: exec_alloca/update_var preserve current_bb on each side. ld_sync_control gives equal old blocks. Rebase current envelope from s to ss (ld_envelope_def depends on source state's current_bb only). Apply ld_envelope_singleton_next (SafetyLocations:33-75) with source state ss, j=s.idx, target state ts; target next activity is raw next's premise, image equality from ld_image_def. This yields BOTH source activity and Y envelope. Since ss.idx=s.idx, this is exactly sn and sn.idx. |
| target active at tt | Raw next premise, image equality from O. |
| o1_ctx_shape and ptr_discipline | Fixed ambient assumptions, not generated by O. |

Thus the .88 successor-location hypotheses are derivable in this actual
original-ALLOCA raw next branch; there is no reason to reopen its proof or
invent a duplicate singleton-next lemma. The work is branch classification
and supplying ambient shape/supply/ptr-use facts. For ordinary singleton
prefixes synchronized boundary recovery is sound, not an invariant gap.
For generated scratch ALLOCA the source stays at DLOAD and .88 must not be used.

### One next bounded interface, selected at the first expansion-next gap

Proposed structural theorem (not asserted/proved by this audit):

```
Theorem ld_prefix_position:
  ld_prefix C fn X p h t0 t /\ t0.vs_inst_idx = p ==>
  t.vs_inst_idx = p + h
```

No export of this statement was found in the task sources. It follows by
cases h=0 versus h=SUC k from the stored prefix trace; it should not unfold
ld_sync. `ld_prefix_predecessor` (SafetyKernel:176-192) exposes the final update
for positive h; zero uses ld_prefix_zero. This is the first positional premise
needed to match an actual raw next update (`SUC t.idx`) to ld_prefix_extend's
`SUC(p+h)` without duplicating trace reasoning in every expansion case. It
is not a proposed replacement for expansion completion or call/return.
The start-index premise is essential: ld_prefix does not constrain t0.idx
when h=0. At integration the premise follows from the stored sync envelope
and equality of the supplied envelope offset, not from prefix_active alone.
Arbitrary-fuel normalization additionally uses step_inst_non_invoke after
classifying generated opcodes. After this structural boundary, the strategist
must schedule multi-instruction completion and a strengthened target-run
return interface; another sequence of isolated opcode adapters cannot settle
those obligations.

## C1.2.3.2 current residual interface probe (2026-11-05)

This section supersedes the old concrete-CREATE audit above: current
`exec_create_def` (venomExecSemantics:528-538) uses the create outcome oracle,
NOT EVM `run`. Only DELEGATECALL still runs a concrete EVM. No full residual
producer is certified by this probe.

Checked use-site tests (both targets rebuilt, no cheats):
* `ld_sha3_observed_bytes` in OracleCallAssembly connects the common exact
  relocated read to SHA3's actual padded TAKE/DROP expression, not merely to a
  masked-word relation. Its inputs are source access/taint, non-revert/non-forward,
  actual evaluated offset/length, offset word relation and target map no-wrap.
* `ld_create_request_equal` in ExternalBoundary projects current init-code bytes,
  value and salt with empty storage/transient masks to EXACT create request
  equality. It deliberately has no historical-request premise.
* `ld_delegate_state_equal` in ExternalBoundary proves exact EVM input-state
  equality from nonghost and empty storage/transient masks, with common target,
  gas, input bytes, code and static flag. Each export has a kernel hyp=[] check.

### Finite premise ledger

All producers must deliver the full location-independent schema of
`ld_sync_observational_read_effect` (not just memory or final sync): source OK,
post vars/memory/nonghost, selected H support and erased provenance, unchanged
allocas/frontiers/current_bb/prev_bb/index. The common endpoint consumer handles
successor activity conditionally. Source instruction wf supplies outputs=[]
when dispatch itself ignores outputs. No new operational definition is needed.

| Family | Actual successful shape and byte inputs | Missing producer work |
|---|---|---|
| CODECOPY, CALLDATACOPY | Three operands dst/src/len, all defined; no output check. Common code/calldata from nonghost, scalar src/len from ptr-use and taint, translated dst from selected provenance. Bytes are padded TAKE len (DROP src data ++ REPLICATE len 0w). | Assemble operand observations once, positive classified write or zero write, apply ld_memory_write_classified; exact step_taint/prov and full structural postconditions. |
| EXTCODECOPY | Four defined operands account/dst/src/len; no output check. Account/src/len scalar. Nonghost preserves account code despite masked storage. | Same writer as above, with account-code projection; do not duplicate low/slot overwrite proofs. |
| RETURNDATACOPY | Three defined operands; successful path additionally src+len <= LENGTH returndata. Common returndata gives same bounds. Unlike padded copies uses TAKE len (DROP src returndata). | Same writer and full postconditions for ordinary non-forward path. OOB is Abort (not OK); current raw safety remains required. Forwarding path belongs to explicit target-only terminal suffix. |
| SHA3 | Two defined operands and exactly one output; actual hash consumes padded current bytes. ld_sha3_observed_bytes checked. | Bind common hash with existing scalar update, clear selected output, derive exact step_taint/prov and preserve other fields. |
| LOG | Lit topic count :: rest, LENGTH rest = count+2; REVERSE rest supplies offset, size, then topics. Successful nonstatic path has all these defined. Static with defined operands is Abort. | History-only update can preserve ld_memory/ld_nonghost without equating logs or even computed event data; derive scalar topic/size definedness and offset definedness, wf empty outputs and step_taint/prov. For exact public event agreement use ld_observed_memory_read after computing actual source read range. |
| DELEGATECALL | Six defined operands gas/account/input-off/input-len/output-off/output-cap; one output and SOME extract_venom_result of actual run. Empty storage/transient masks from taint_ok. Exact input EVM state equality checked. | Derive scalar gas/account/lengths, translated input/output offsets and current input-byte equality. Then transport SAME run result through extraction using each run's own prestate and relocated output write; equal EVM input is not the extraction theorem. Need classified returned bytes, common scalar success word, account/transient adoption, returndata and frame projections, then vars/taint/prov. |
| CREATE, CREATE2 | Three/four operands value/off/len[/salt], one output, len <= 2*max_code_size for OK; oversized init code is Abort. Common current init code gives exact request by checked ld_create_request_equal. | Derive scalar value/len/salt, translated init offset and exact observed bytes; transport consume_create_outcome at equal requests and equal queues through different local prestates. No returned-memory write. Establish common output/returndata/accounts/transient and retained projections; clear output H and apply actual step_taint. |

Zero length: all padded copy bytes and observed reads are []; no pointer
containment required. RETURNDATACOPY still checks src <= LENGTH returndata when
len=0; it must NOT be treated as unconditionally successful. CREATE's empty init
code still issues a request. DELEGATECALL's zero output cap still executes/extracts
and changes returndata/accounts as specified. LOG with size=0 still appends an
event, and SHA3 still binds the hash of [].

Taint is driven by `step_taint_def`, not changed-state guesses. For copies,
`mem_taint` removes actual `step_writes` from old tainted memory and the writes
are public; zero length removes nothing. SHA3/LOG have no writes or new sites.
All these observations have untainted scalar outputs; one-output bindings clear
selected provenance while wf empty-output instructions keep it. CREATE and
DELEGATECALL have already-empty storage/transient masks; `adopt_reset` only
matches CALL, so cannot be used as their reset rule. CALL/STATICCALL's existing
assembled effect remains reusable and event-based; equal queue alone is never a
request-agreement argument. Allocations/control are retained by all listed base
helpers, but this must be exported in each full producer, not inferred from the
memory relation.

### Requested refinement after this probe

Within the existing residual focus, schedule (1) one public-copy producer using
the shared classified writer; (2) SHA3 and LOG observation/identity producers;
(3) create-oracle completion plus concrete delegate extraction transport and
full effects; then (4) exhaustive endpoint assembly depending on these and the
accepted scalar prerequisite. The assembly must include ISTORE/storage writers,
NOP/assertions and all existing effects, original fresh/cached ALLOCA through
existing constructors, and existing DLOAD/DLOADBYTES endpoints. It must explicitly
exclude PHI/error-only and pointer/FMP-forbidden cases without treating INVOKE,
control or terminal instructions as ordinary OK steps. This is a missing-interface
ledger, not a substitute for those producer proofs or the parent coverage proof.

## C1.4.1 current-source reconciliation (2026-11-06)

This section supersedes missing-export claims in the earlier ledger, not the
requirements of the frozen theorem. `lowerDloadReturnReconstructionTheory`
was rebuilt cleanly at this checkpoint. No residual coverage theorem is claimed.

### Checked interfaces now present

* `ld_prefix_position` and `ld_prefix_next` (SafetyKernel:196,205) supersede the
  proposed positional helper above. No duplicate positional theorem is needed.
* `ld_full_endpoint` (FullEndpoint:12-60) is exhaustive for nonterminal,
  non-INVOKE source expansions, including original ALLOCA and both generated
  expansions. It exports source OK, correlated new allocation map/head frame,
  post memory/nonghost/vars/maps/global, unchanged saved-map entries, configured
  supplies/order/Q ownership, and synchronization CONDITIONAL on source next
  activity. The old residual copy/hash/create/delegate effect gaps are closed
  through OrdinaryEndpoint and its ancestors; do not reopen them.
* `ld_return_concrete_packages` and `ld_invoke_return_reconstruction`
  (ReturnReconstruction:9,36) reconstruct actual source IntRet executions with
  the nested semantic induction, not raw_reachable induction. The latter
  consumes covered ambient + sync + Stable, target decode/lookup/args/setup/run,
  and supplies source lookup/args/setup plus exact correlated Terminal.
* `ld_invoke_active_pop` (ReturnInvokePop:509-527) consumes that Terminal and
  target bind_outputs plus active successor. Its conclusion is Point at the
  caller successor, including correlated Stable and source return-continuation.
  No future successful caller execution is required. The guarded wrapper shares
  the same implementation. All these exports have kernel hyp=[] checks.

### Exact four-rule consumer ledger

Use the existing O existential at lines 1024-1037 (or a reviewed strengthening),
OR the explicit target-only forwarding suffix certificate. Preserve one set of
witnesses throughout; `ld_pair` alone loses the Q ownership correlation.

| raw rule | Current supplying export | Remaining unproved assembly |
|---|---|---|
| entry | ld_owned_root_coverage (RootCoverage:31) | Derive original entry lookup/label and distinct labels from stage+shape; establish transformed entry resolvability separately for mem_inv. No target success premise is allowed. |
| next, strict expansion interior | ld_prefix_next and ld_prefix_position; ReturnInterior provides a Point-based implementation | Classify generated non-INVOKE opcode and normalize arbitrary fuel to zero; keep same sync/global/ownership witnesses. No semantic gap or fresh ghost update here. |
| next, completed non-INVOKE expansion | ld_full_endpoint; ld_envelope_successor_location and ld_envelope_active_head | Derive non-revert alternative without a successful future-run guard; derive next source activity from target active successor, then apply conditional synchronization. Carry new Ar/g together and re-pack O at phase zero. ReturnNonterminal:11-115 demonstrates the construction but its Guard0/Guard1 premises prohibit using it directly as unconditional raw coverage. |
| block | ld_sync_control_entry (ControlCoverage:8-36), owned wrapper | Recover singleton, classify successful terminator as JMP/JNZ/DJMP (other terminal opcodes cannot supply live OK block transition), derive taint_ok from source reachable ptr discipline; apply to the actual target enters_block and active premises. No future-run guard needed in this export. |
| callee | ld_invoke_correlated_setup and ld_sync_call_push (ReturnInvokePush:86,164), ownership/global/order helpers | Generalize guarded entry/push boundary to actual target enters_block + active callee instruction. ld_setup_guarded_entry:220-235 uses Guard only to fetch active head (254-259); PHI predecessor NONE and entry-state identity are already checked. Raw callee activity supplies fetching instead. ld_invoke_guarded_push currently still exports a Guard-dependent Entry; it is NOT unconditional callee coverage. |
| next, atomic INVOKE | ld_invoke_return_reconstruction + ld_invoke_active_pop | Establish Stable and return-cont from the same O witnesses (choose self baseline fs/f/A, prove saved-reference locality from sync/global), recover singleton/location, decompose target successful call, and repack Point into O. Stable must not be assumed from an unrelated existential. This is assembly, not a missing nested induction. |

Ambient producers: `lower_dload_stage_covered_supplies` (ConfiguredOrigins:977)
provides configured Sigma and freshness; `o1_ctx_shape_distinct_names` :1001
supports lookup uniqueness. `ld_sync_supply_covered` (ReturnAlignment) combines
source membership, configured equality and covered supplies. `ld_sync_fn_shape`
and o1_fn_shape_components give label uniqueness and instruction wf.
`ld_sync_source_mem_inv` (SafetyAmbient:417) uses source frame-to-raw reachability,
not target safety. `ld_sync_ambient_headroom` :427 derives the boundary frontier
bound from source headroom and active-stack charge; `ld_sync_frontier_lower_bound`
:437 supplies lo <= target frontier. The ambient conjunction itself must be
extracted from frozen o1_src_inv/ctx_pass_stage once, not added to the theorem.

### Terminal suffix and CURRENT safety are still independent obligations

`ld_forward_prefix_raw` (TerminalSafety:105-114) is checked for an explicit
bounded RTC suffix certificate with initial frontier bound, lookup, current fetch
and inclusive i..j position. The source in_revert_forward alternative must be
transported syntactically to the target pair and initialized/extended as a
coverage alternative. No future successful run may be required. Terminal results
have no next-rule obligation, but every current prefix (even Error/Abort/Halt)
requires raw_mem_ok. `ld_forward_run_blocks_no_normal` and ld_invoke_no_return
prevent a forwarding callee from returning normally; they do not generate the
suffix certificate.

Current safety exports are PARTIAL: `lower_dload_supply_prefix_raw`
(ScratchSafety:164-174) covers all DLOAD phases once cached/fresh scratch size,
bounds and headroom premises are assembled from maps/charge; `ld_sync_oracle_call_raw`
(OracleCallSafety:110-115) covers CALL/STATICCALL without successful-step premise.
No general O -> raw_mem_ok export was found. Remaining ordinary/DLOADBYTES
current-safety work must transport classified read/write ranges and frontier
bounds for every opcode, including RETURN/REVERT/LOG/SHA3/CREATE/DELEGATECALL and
malformed/undefined operands. Do not use successful-effect theorems for this.
Instructions with no actual ranges still need the frontier conjunct. Scratch
ALLOCA must not be classified as an original source ALLOCA.

### Checkpoint conclusion

The semantic return and full endpoint gaps recorded by older sections are now
closed. Residual implementation is: ambient/entry, unconditional callee activity,
correlated next/branch/call assembly, forwarding-suffix alternative and general
current safety, followed by the four-rule induction. These need strategist-owned
executable leaves before proof edits. This audit adds no definitions or axioms,
and does not certify the frozen theorem (its single cheat remains at Mem:23).

## Current-range interface checkpoint (C1.4.8.1, 2026-11-06)

### Correction to the provisional LOG-zero concern

The provisional concern in E0089/STATE was **wrong**. The HOL list pattern
`ofst :: sz :: _ :: _` has three cons cells and an arbitrary final tail;
it does NOT require four elements. Thus a three-operand zero-topic LOG is
covered by mem_read_ops. The checked theorem
`lowerDloadRangeAuditTheory.ld_log_zero_topics_range_audit` states exactly:

```
!inst s.
  inst.inst_opcode = LOG /\
  inst.inst_operands = [Lit 0w; Lit 1w; Lit 0w] ==>
  mem_read_ops inst = SOME <| iao_ofst := Lit 0w;
    iao_size := SOME (Lit 1w); iao_max_size := SOME (Lit 1w) |> /\
  source_memory_read_ranges inst s = [(0,1)]
```

It builds without cheats (TO_ld_mem-20261105T144418Z_m3603_t001).
The attempted NONE version simplified to F, rather than verifying a
counterexample (m3600_t001). No LOG exception or protected-definition
change is needed for the proposed single-range transport theorem.

### Exact coverage packages: planned, not checked producers

O is the correlated existential displayed above at lines 1024-1037.
C1.4.6 proposes O+ by adding, **inside the same existential**, exactly

```
!g. MEM g (TL frames) ==>
  FRANGE g.lf_H SUBSET ld_slots A (TL frames) /\
  (!a. MEM (SOME a) g.lf_Q ==> a IN ld_slots A (TL frames))
```

The extra saved-tail locality is not a consequence of ld_global alone.
C1.4.7 proposes the following report abbreviation, not a HOL definition:

```
F C' fn' ti t =
  ?bb i j. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ i <= t.vs_inst_idx /\
    t.vs_inst_idx <= j /\ get_instruction bb t.vs_inst_idx = SOME ti /\
    t.vs_alloca_next < dimword (:256)
```

Neither O+ transition production nor F production/closure is a completed
export. The intended downstream induction carries O+ OR F. The actual
current-safety conclusion is `raw_mem_ok C' fn' ti t`, i.e.
`t.vs_alloca_next < dimword (:256) /\ inst_mem_ok_in_fn fn' ti t`;
see unitMemInvScript.sml and the elimination target above. Future successful
execution is not a premise of this goal.

### Exhaustive descriptor/range table audit

Read table: contextCodegenRelScript.sml:105-201. Descriptor table:
memLocDefsScript.sml:266-344. Write table: codegenRelScript.sml:131-225;
write descriptors: memLocDefsScript.sml:188-259.

* Fixed reads MLOAD/ILOAD select their sole operand and length 32.
* MCOPY reads operand 2 with operand 3 length; it additionally checks the
  destination evaluation. RETURN/REVERT/SHA3 select operands 1 and 2.
* CALL selects input offset/length 4/5, STATICCALL and DELEGATECALL 3/4.
  All other operand evaluations are guards, not equality requirements.
* CREATE selects 2/3 and guards value evaluation; CREATE2 additionally
  guards salt evaluation. Neither has a source write range.
* LOG requires a literal topic count, LENGTH rest = count+2, evaluated
  topics, and evaluated last two operands. These imply total length >=3,
  hence exactly the reverse-list shape accepted by its descriptor. The
  descriptor selects last operand as offset, penultimate as size. Malformed
  LOGs may have a descriptor but no range, harmless for membership transport.
* Fixed writes MSTORE/ISTORE length 32, MSTORE8 length 1, select destination
  operand 1 and additionally guard value evaluation.
* Sized writes MCOPY/CALLDATACOPY/RETURNDATACOPY/DLOADBYTES/CODECOPY use
  destination 1, size 3, and guard source evaluation. EXTCODECOPY uses
  destination 2, size 4, and also guards address evaluation.
* CALL output uses 6/7; STATICCALL and DELEGATECALL use 5/6. The range is
  output **capacity**, so equality must use iao_max_size, not iao_size
  (which is NONE for these outputs). All input evaluations are guards.
* DRET is exceptional in BOTH tables. Reads are multiple dynamic pairs;
  writes use parsed pairs and call-entry FMP. It has no descriptor. The
  generic theorem must exclude it. o1PassContractScript.sml:354-375 puts
  no_dret in o1_fn_shape, inherited by members under o1_ctx_shape. This,
  not fmp_free_ctx alone, excludes DRET at synchronized source points;
  target ordinary envelopes preserve opcode and generated instructions
  are ADD/ALLOCA/CODECOPY/MLOAD. A consumer must explicitly use this fact.
* Every other opcode returns [] in both semantic tables.

Thus the displayed C1.4.8.2 interface survives this audit: target-defined
operands imply source-defined operands, descriptor maximum-size equality
preserves length, and nonempty membership selects a descriptor outside
DRET. No address equality or step success is justified or needed here.
The proposed theorem itself remains unproved. LOG additionally needs the
routine list-evaluation definedness implication across its topic list.

access_ok (ptrDisciplineScript.sml:530-558) classifies nonempty ranges
ending above lo or using a provenance-bearing selected offset, under
~in_revert_forward. In a hypothetical missing-descriptor case it would
force the source range below lo, but transport would still need operand
observation; that hypothetical workaround is NOT needed for LOG.

### Generated DLOADBYTES: remaining unconditional prefix boundary

PublicTraceScript.sml:9-39 `ld_dloadbytes_trace_operands` explicitly assumes
`step_inst fuel C' (EL 1 X) t1 = OK u`. Its synchronized wrapper at
400-447 has the same success premise. Neither establishes safety of a
currently failing CODECOPY. Do not apply either in the raw-safety consumer.

For a nonempty current CODECOPY range, range membership supplies defined
dest, Var z and len at t1. The strict prefix at h=1 already contains the
successful ADD; ld_prefix_predecessor and ld_prefix_zero recover this
without CODECOPY success. The fresh temporary boundary
ld_dloadbytes_envelope_temporary (PublicTrace:196) gives z outside fn_ir_vars,
so dest and len cannot equal Var z. ADD updates only z and preserves code,
labels and frontier. Therefore their current evaluations can be moved
back to t0. The missing boundary should expose these prefix-only facts
(possibly conditioned on current range membership), not future success.

Checked reusable source interface `ld_dloadbytes_source_operands`
(PublicTrace:375-398) assumes ld_vars, equal labels, fn_shape_ok, fn_ptr_ok,
source membership, DLOADBYTES shape, taint_ok and target t0 evaluations;
it concludes source dest is defined and source off/len equal target off/len.
`ld_sync_dloadbytes_destination_cases` (449-489), with non-forwarding and
headroom, then concludes length zero, or equal low addresses with end<=lo,
or source/target offsets b+delta/c+delta with delta+length<=sz in A.
Combine with ld_alloc_target_frontier and lo<=frontier. ADD preserves the
frontier, so the bound applies at CODECOPY t1. No code-offset bound or
CODECOPY success is required merely for its memory range safety.
At h=0 ADD has empty ranges. Source forwarding must instead use F.

### Checkpoint disposition requested

No falsehood of the frozen theorem was found. The LOG suspicion is closed
by a checked theorem; generic transport needs no exceptional LOG branch.
Still missing: formal generic descriptor/range transport, its classified
frontier corollary, the prefix-only DLOADBYTES observation boundary, O+
transition producers, F producers/closure, and their final safety consumer.
Review C1.4.8.4 decomposition to give the missing prefix-only boundary its
own executable obligation before integration. Keep producer packages
explicitly dependency-gated; this source audit does not certify them.
