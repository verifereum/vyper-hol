# C1.11.5.34 ordinary coverage checkpoint

This is an interface audit, not a theorem or a claim that the frozen contract is proved.
Source snapshot: after 0bcbdd68c (classified MCOPY). No semantic definitions or theorem
statements were changed. E0060/E0061 are the earlier terminal/assembly reports.

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
| MSTORE, MSTORE8 | checked ld_mstore_effect :46, ld_mstore8_effect :154 in lowerDloadSafetyMemoryWriteEffects; classification/operand premises NOT assembled |
| MCOPY | checked ld_mcopy_effect, lowerDloadSafetyMemoryCopyEffects:42; independent classified addresses, snapshot mask; premises NOT assembled |
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
| CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2 | genuinely missing external-effect family. Need dispatch/helpers audit and equal semantic request inputs (not equality of historical requests), outcomes and masked account updates, copied return data, output/provenance/taint and frontier projections. taint_ok empties stor/trans for DELEGATECALL/CREATE/CREATE2 only. No exclusion argument exists |
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

## Exact candidate sequential advance consumer (NOT PROVED)

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
(lowerDloadSafetyKernel:21-57). This is an audited candidate, not a checked HOL
constructor proof.

## Classified-write premise ledger at that consumer

Use f=HD frames. ld_sync_active supplies ld_vars, source/target states and tv;
ld_sync_memory supplies ld_memory and ld_nonghost; ld_sync_ghosts supplies erasure.
ld_sync contains EVERY(ld_maps), FDOM A=ld_slots and member fn facts; ld_global is
separate, not a consequence of ld_sync. ld_alloc_bounds and ld_alloc_separate
(lowerDloadSafetyAllocBounds:6,23) supply overwrite separation only.

| Required premise | Present source/interface or exact remaining gap |
|---|---|
| opcode/operands and evaluated target arguments | OK inversion of dispatch (exec_write2 for stores, explicit MCOPY case); local step lemmas reconstruct but are not inversion lemmas |
| source operand definedness | ld_vars_operand_defined; shape/member/nonopaque handling; inversion assembly still absent |
| [] outputs | fn_inst_wf plus opcode cases; cannot infer from target OK |
| source/target destination classification | MISSING write analogue of ld_read_access_cases. Need access_ok, ~in_revert_forward, source write range, selected/scalar observation, target no-wrap bound; numerical (b,sz) not unique ghost identity |
| MCOPY source classification | ld_read_access_cases exists (:274) only for POSITIVE size and ~in_revert_forward. Need independent read operand mapping, correct mem_read_ops and source range, target c+sz<dimword; no general MCOPY consumer yet |
| MCOPY shared length | numeric untainted/nonopaque restrictions + ld_vars_numeric_operands_equal / ld_ptr_use_scalar; must prove length operand is not permitted pointer-address position. Not supplied by raw safety alone |
| zero-length classification | REAL INTERFACE GAP: access_ok only constrains nonempty ranges. Current effect demands low-or-slot even when len=0. Neither ld_read_access_cases nor future positive write inversion gives this. Need a zero-copy effect/assembly branch with no address classification, or a generalized effect interface approved by strategist. Do not add len>0 to frozen hypotheses |
| MSTORE value word_agree_except(op_taint) | ld_vars_value/scalar, fn_ptr_ok disallows storing pointer values; need opcode-specific ptr-use and opaque exclusion, including duplicate operand cases |
| MSTORE mask subset {j<32} | taint byte-width invariant needed from taint_within/step_taint reachability or a generic op_taint bound. Not a conclusion of ld_vars alone; no supplying theorem certified in this audit |
| MSTORE8 low-byte equality | ld_vars masked observation plus low-byte untaintedness; step_taint MSTORE8 clears all destination taint, so cannot merely reuse arbitrary masked word agreement. Need show op_taint value empty from taint_ok (MSTORE8 not permitted tainted store opcode), then ld_word_agree_empty |
| MCOPY copied-byte untaintedness | NOT required: ld_mcopy_effect handles snapshot source mask. No source/destination disjointness or positive length needed by that effect |
| ghost update | effect proves erased step_prov unchanged for [] outputs; H'=H works. Raw G'=G plus empty outputs reconstruction uses step_inst_non_invoke |
| maps/global/slots | provided by sync/global; preserve via unchanged allocas/frontiers. Need constructor/advance lemma rather than repeated ld_sync unfolding |
| next envelope/index | effect projections alone insufficient; source index+1 corresponds to p+1 only for singleton unchanged envelope and valid next active instruction. Missing GAP L constructor |

Access premises come from ptr_discipline at frame_reachable witnesses; taint_ok and
within-D come from taint_within at the same witness. ld_sync records reachability,
not these invariants as standalone conjuncts. Ambient source invariants must be
passed/extracted. ld_read_access_cases target no-wrap premise is likewise not in
ld_vars: derive from global head frontier and active headroom. Zero-size selected
sites are not enough to infer actual address containment.

## Grouped remaining dependency graph (proposal for strategist, not new PLAN IDs)

1. Shape/member/active and source-invariant extraction + operand restrictions
   -> classified access inversion (read/write, no-wrap), masked store observations.
2. Resolve zero-length copy interface separately; do not make classifications
   magically true. This blocks use of the current MCOPY effect in full assembly.
3. Group external-byte copies + ISTORE with reusable overwrite boundaries;
   group SHA3/LOG/control/assertions/identity/state reads with observation and
   control projections; audit external-call/create helpers as one semantic boundary.
4. Family effects + erased H/live-domain equations + index/envelope constructor
   -> singleton sequential advance consumer above.
5. Jump/block entry + ld_phis_effect -> block consumer; allocation/expansion
   constructors and call/run/return remain wider parent dependencies.
6. All local consumers + explicit terminal suffix alternative -> target-prefix
   coverage -> raw target invariant -> frozen theorem integration.

The immediate planning risk is not more isolated effect tactics: it is deriving
classification and mask premises at reachable locations, especially zero length,
and supplying a compact sync/next constructor. No completed parent is claimed.
