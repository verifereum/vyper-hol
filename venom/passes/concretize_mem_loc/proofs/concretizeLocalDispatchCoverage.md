# Local dispatch coverage checkpoint

Audit of `venomInstScript.sml:23-69`, `venomExecSemanticsScript.sml:597-1183,1647-1764` on the current base. This is an inventory, **not** a dispatcher proof. All constructors occur below; comma-separated constructors in a row have the same coverage classification, not necessarily the same semantic function. No executable definitions or theorem statements were changed.

## Status and obligation conventions

- **complete** means an actual concrete reachable ordinary-event boundary exists, subject to its stated interface (not that the final invariant establishes that interface).
- **conditional** means existing exported algebra/step boundaries leave integration premises; it does not mean opcode coverage is done.
- **missing** means no applicable complete guarded-relocation family boundary was found in the frameRelocation/concretizeLayout theories. Other exact-state/remap libraries are not automatically applicable.
- **excluded** always refers to a named frozen premise plus instruction membership in the current source function/context. Establishing that membership remains a frame/control obligation.
- **delegated** is the existing generic frame interface, not a claim that its instantiation is finished.

For every ordinary OK row the eventual output must include (V) target execution and successor guarded pointer/byte/domain relation, (G) actual resolved origin update and its `step_prov` erasure, (D) successor joint demand, (O) observation preservation, and (T) `relocation_taint_le next (step_taint inst s post tn) (step_taint target t tpost un)` for **independent** `un`. Existing equations evaluating target `step_taint` on **tn** do not alone discharge T. For no-memory operations D should use retained-demand inclusion, but this inclusion still needs the event/trace adapter. For terminals replace the OK postcondition by the appropriate result relation and frame terminal ghost interface. Error branches are not matched by OK-only lemmas; source termination must eliminate or explicitly match them.

## Existing interfaces actually available

All paths in this paragraph are under `venom/passes/shared/proofs/` unless prefixed `concretizeLayout` (under this document's directory).

1. `frameRelocationLocal.local_rel P ptr B R Obs s t` is exactly variable-domain equality, selected scalar agreement, paired guarded values, demanded memory-byte agreement, and `Obs s t`. It contains **no** labels, predecessor/control, parameter, transaction, block, call-context, gas-stream, code/data-section, or call-outcome equality. The concrete memory boundaries instantiate `P = (\u. F)` and `Obs = (\s t. dead_result_rel D (Halt s) (Halt t))`.
2. `frameRelocationScalarSteps.guarded_scalar_binary_step`: local_rel with guarded values; `scalar_binary_opcode`; `[a;b]`, `[v]`; equal labels; every variable input `clean_scalar`; Obs invariant under equal writes; source `step_inst_base = OK s'` imply target OK, origin_set NONE postrelation, source/target-on-tn taint equations and source prov erasure. Family is exactly ADD SUB MUL Div Mod SDIV SMOD Exp EQ LT GT SLT SGT AND OR XOR SIGNEXTEND BYTE. R is unchanged, and independent target taint and concrete cleanliness are not produced.
3. `frameRelocationAffineSteps.guarded_pointer_binary_step`: ADD/SUB `[Var w;a]`, same token/site lookup in rv, nonopaque w, scalar-clean a, equal labels, arbitrary paired variable-write Obs invariance, source OK imply target OK and pointer-preserving origin_set, actual source prov/taint equations. `guarded_scalar_add_pointer_step` handles swapped ADD. Concrete classification/cleanliness, successor demand and independent T remain adapters.
4. `frameRelocationCompareSteps.guarded_pointer_compare_step`: EQ/LT/GT of two nonopaque variables with **same token** and same (b,sz), source values in inclusive site bounds, strict source and target nonwrap, equal-write Obs invariant, source OK imply target OK, cleared result origin and clean taint. `frameRelocationCompareAccess` and concretize numeric interfaces support these conditions; do not invert a numeric base/size pair to deduce equal tokens. `access_ok` supplies same numerical site, not by itself token identity.
5. `frameRelocationGuardedSteps.retpc_guarded_assign_step`: ASSIGN `[Var w] [v]`, lookup source, equal labels, membership and arbitrary paired-write Obs invariance imply target execution, copied resolved origin/actual source taint, and prov erasure. `local_rel_assign_scalar` supplies scalar assignments, `local_rel_assign_opaque` supplies unequal opaque writes. These are not a complete concrete event/T adapter.
6. `frameRelocationPhi.retpc_parallel_phis`: source successful `eval_phis`, equal labels and previous block, membership of every instruction, paired-write Obs invariance imply successful target PHIs and local_rel with `resolved_phis` and `phis_taint`. `resolved_phis_erasure` is separate. R is unchanged; independent target PHI taint, demand/index/control transport remain integration obligations.
7. `frameRelocationAllocationSteps.local_rel_alloca_assign_step`: explicit ALLOCA/ASSIGN operands/outputs, existing-cache or fresh-cache source equation, retained-demand inclusion, output pointer/bytes and other-variable implications, **post Obs premise** imply source/target steps and post local_rel. It does not produce cache geometry, birth ghost, T or post observations. No memory zero-initialization occurs.
8. `concretizeLayoutLocalLoad.concretize_mload_local_complete`, `concretizeLayoutLocalStore.concretize_mstore_local_complete`, `concretizeLayoutLocalCopy.concretize_mcopy_local_complete`: actual source joint ordinary event, resolved/lifetime configuration and accepted layout/discipline context, non-exempt read, shape/membership, equal labels, guarded local_rel at demand c and independent relocation_taint_le yield target OK, actual source-ghost guarded local_rel at SUC c and independent T. Load additionally specifies `[opd] [v]` and source operand; store/copy have their own source operand envelopes. These are the three complete reachable memory boundaries; retain all their premises rather than treating them as unconditional simulations.
9. `frameRelocationStoreSteps.local_rel_mstore8_step`: `[opd;opv]`, paired operand evaluations, local_rel, produced-byte equality for one-byte destination, write-complement retained demand and **post Obs** imply paired execution and local_rel with unchanged ptr/B. No actual ghost/T producer is included. `mstore8_as_write_memory` already exists; do not duplicate it.
10. `frameRelocationOpaque.disciplined_retpc_operand_use` restricts opaque uses to ASSIGN, PHI, or final RET token; `opaque_return_token_step` drops that final token, and `setup_callee_opaque_token` explicitly allows different LAST args. These support return/frame work, not PARAM or RETPC_PARAM local integration.

## Canonical clean-value interface (main-table reconciliation)

`concretizeLayoutLocalValuesTheory.concretize_clean_value_local_complete`
handles `clean_value_shape inst /\ ~MEM inst.inst_opcode [ADD; SUB; EQ; LT; GT]`.
This includes ISZERO/NOT (one operand), ADDMOD/MULMOD (three), and the
nonpointer scalar binary families marked below (two), always with singleton
output and the theorem's full discipline, shape, resolved-configuration,
actual ordinary-event, incoming local relation and independent taint hypotheses.
It derives operand cleanliness, target success, actual origin erasure,
source/target step_taint, successor demand, dead-result observations and
`relocation_env`. It does **not** export `relocation_reader_context` preservation;
that is a separate consumer-side supplement, not missing unary execution.
These entries supersede the initial audit's stale missing/conditional labels;
no specialized unary producer is needed, and full dispatch remains outstanding.

## Exhaustive constructor inventory

The obligations column refines V/G/D/O/T above. All semantic helpers here are in `venomExecSemantics`; all rows with operand envelopes can also return Error for malformed/undefined operands. No row silently excludes Error. References B1..B10 refer to numbered boundaries above.

| Constructor(s) | Semantic helper / non-Error outcomes | Existing boundary; status | Reachable premises and outstanding obligations |
|---|---|---|---|
| ADD | exec_pure2 word_add / OK | reachable producer checked | concretizeLayoutLocalAffine.concretize_affine_local_complete covers scalar, pointer-left and pointer-right cases; derives pair shape, classification and cleanliness, preserves actual G, restricted successor D, independent target T and both environments. |
| SUB | exec_pure2 word_sub / OK | reachable producer checked | Same grouped concretize_affine_local_complete; reachable resolved support and affine discipline exclude a right pointer. No arbitrary pointer subtraction is claimed. |
| MUL, Div, SDIV, Mod, SMOD, Exp | exec_pure2 / OK | reachable clean-value producer checked | Canonical concretize_clean_value_local_complete derives clean inputs from discipline and supplies actual G/D/O/T; binary operand envelope and full incoming interface retained. |
| ADDMOD, MULMOD | exec_pure3 / OK | reachable clean-value producer checked | Canonical concretize_clean_value_local_complete handles the three-operand envelope, actual ghost updates and independent target taint; see interface below. |
| EQ, LT, GT | exec_pure2 / OK | complete reachable producer | `concretizeLayoutLocalCompare.concretize_compare_local_complete` covers origin-free scalars and pointer pairs. `concretize_comparison_geometry` derives same tokens via positive-site interior-byte cache uniqueness, and strict source/target endpoints; no positivity or same-token premise is added. Produces actual provenance erasure, successor demand, independent target taint and both environments. Stage/layout, source trace, resolved/lifetime, discipline and membership premises remain explicit; full dispatch is not certified. |
| SLT, SGT | exec_pure2 signed comparison / OK | reachable clean-value producer checked | Canonical concretize_clean_value_local_complete derives scalar cleanliness; no signed pointer comparison claim. Full incoming interface and binary envelope retained. |
| ISZERO | exec_pure1 / OK | reachable clean-value producer checked | concretizeLayoutLocalValuesTheory.concretize_clean_value_local_complete; see canonical clean-value interface below. Separate reader-context preservation is not exported. |
| AND, OR, XOR | exec_pure2 / OK | reachable clean-value producer checked | Canonical concretize_clean_value_local_complete derives clean scalar inputs and actual G/D/O/T; full incoming interface and binary envelope retained. |
| NOT | exec_pure1 / OK | reachable clean-value producer checked | Same canonical clean-value producer and interface as ISZERO; no specialized unary theorem needed. |
| SHL, SHR, SAR | exec_pure2 shift / OK | reachable masked-value producer checked | `concretize_shift_local_complete` in concretizeLayoutLocalShifts derives clean count and origin-free nonopaque operands; shifted value may differ under its byte mask. Uses frozen masked-word shift facts, actual source/independent target step_taint, cleared provenance, event-derived SUC demand restriction and both environment supplements. Single output is explicit; two operands follow from source success. No full-dispatch claim. |
| SIGNEXTEND, BYTE | exec_pure2 / OK | reachable clean-value producer checked | Canonical concretize_clean_value_local_complete handles both clean scalar inputs and actual G/D/O/T; not the shift taint exception. Full incoming interface retained. |
| MLOAD | exec_read1 mload / OK | B8; complete | Full concrete pre-interface still required: joint ordinary event, resolved/lifetime, nonexemption, labels, local_rel and independent T. Result origin is erased. |
| MSTORE | exec_write2 mstore / OK | B8; complete | Same concrete event/interface requirements; paired possibly tainted stored word and actual ghost/T handled. |
| MSTORE8 | exec_write2 mstore8 / OK | B9; complete | concretizeLayoutLocalStore8 exports concrete one-byte geometry and concretize_mstore8_local_complete: clean equal stored value from discipline, actual step_prov/step_taint, independent target taint inclusion, dead-result observation and restored-memory equalities retaining all execution-environment fields. Geometry shares coherent_written_interval with MSTORE. |
| MCOPY | direct mcopy / OK | B8; complete | Nonexempt concrete source event; zero/positive lengths, read/write geometry and independent T covered in accepted boundary. |
| MEMTOP | exec_read0 memory length / OK | excluded | `ptr_discipline_def` gives EVERY fn_ptr_ok; `fn_ptr_ok_def:123-126` excludes at member instruction. No equality of source/target memory lengths is available. |
| SLOAD | exec_read1 sload / OK | complete reachable masked producer | `concretizeLayoutLocalStateReads.concretize_state_read_local_complete` derives clean equal keys from reachable discipline/support, uses source-taint supplement for masked loaded words, and produces target OK, cleared provenance erasure, SUC demand, Obs0, independent target step_taint order, successor supplement and both environments. Explicit variable-update witnesses preserve all administrative fields. Singleton operand/output and full source trace/resolved/shape/membership premises remain; no equal storage values or post-observation premise. |
| SSTORE | static check or exec_write2 sstore / Abort ExHalt or OK | complete Abort producer; reachable OK complete | `concretize_static_write_abort_complete` in concretizeLayoutLocalTerminals handles static Abort. `concretize_state_write_local_complete` in concretizeLayoutLocalStateWrites derives the operand/output envelope from `o1_fn_shape` and clean key and nonopaque origin-free value from reachable discipline. Allows unequal tainted values; produces target OK, Obs0 local relation, actual unchanged provenance, actual keyed source taint, independent target taint inclusion, successor demand, actual-D supplement and both environments. Full dispatch/frame integration remains open. |
| TLOAD | exec_read1 tload / OK | complete reachable masked producer | `concretizeLayoutLocalStateReads.concretize_state_read_local_complete` groups TLOAD with SLOAD, using t_trans and the transient supplement. Produces target OK, cleared provenance erasure, SUC demand, Obs0, independent target step_taint order, successor supplement, both environments and paired update_var witnesses. Same singleton operand/output and reachable source envelope as SLOAD; no equal loaded-word premise. |
| TSTORE | static check or exec_write2 tstore / Abort ExHalt or OK | complete Abort producer; reachable OK complete | Same grouped static Abort export and `concretize_state_write_local_complete` as SSTORE. Actual keyed transient taint/supplement updates allow unequal masked values; target success, successor demand, independent target taint and both environments are proved. Full dispatch/frame integration remains open. |
| ILOAD | exec_read1 mload / OK | complete reachable boundary | `concretize_iload_local_complete` in `concretizeLayoutLocalLoad` consumes the source single-input/output/evaluation envelope, trace/resolved/lifetime/nonexempt premises, guarded local relation, independent taint and explicit environment supplements. Shared `concretize_word_load_execution_clean_lanes`, `concretize_word_load_demand_execution` and `concretize_word_load_local_complete` handle MLOAD/ILOAD once; old MLOAD exports remain compatibility corollaries. Produces target OK, masked clean-lane result, SUC demand relation, actual provenance erasure and independent target taint, preserving both environments. ILOAD reads vs_memory, not an immutable map; no full-memory or post-agreement premise. Terminal-exempt reads and frame admissibility remain open. |
| ISTORE | istore / OK | complete reachable nonexempt producer | `concretizeLayoutLocalIstore.concretize_istore_local_complete` reuses `concretize_istore_demand_execution` and geometry on the actual ISTORE event (not a fabricated MSTORE event). Produces target OK, SUC demanded-memory/guarded local relation with Obs0, actual erased step_prov, independent target step_taint order, immutable actual-D supplement and both environments. Clean equal fixed-region destination is derived; masked values may differ. Explicit two-operand/no-output/source-evaluation envelope and independent value-mask bound remain premises, together with the full trace/resolved/nonexempt interface. Full origin-step/frame/dispatch integration remains open. |
| JMP | jump_to / OK | complete reachable producer | `concretize_jmp_local_complete` in concretizeLayoutLocalJump: same label literal, actual unchanged provenance/source and independent target taint, retained successor demand, local relation and both environment supplements. Explicit incoming current_bb equality produces successor prev/current block and index alignment; no control equality inferred from Obs. |
| JNZ | condition then jump_to / OK | complete reachable producer | `concretize_conditional_jump_local_complete`: selector cleanliness derived from reachable discipline/resolved support; same selected label; actual G/D/O/T and both environments, with explicit incoming current_bb alignment. |
| DJMP | extract_labels, selector-indexed jump_to / OK or Error bounds | complete reachable OK producer | Same grouped export: equal selector yields same index/label, source OK supplies bounds. Actual G/D/O/T and control alignment; Error matching remains a dispatch obligation. |
| RET | eval_operands then IntRet | B10; delegated to generic frame boundary | Equal/related FRONT return values, not final opaque pc; saved frame params/origins/taints, return cache/lifetime/demand and merge. Existing opaque token fact is only one ingredient. |
| RETURN | memory slice, set_returndata, halt_state / Halt | missing | Relocated offset/size, demanded clean lanes, equal length and bytes outside D.d_ret using taint_within; terminal G/T. Equality of all return bytes is too strong. |
| REVERT | memory slice, revert_state / Abort Revert | complete terminal result producer | `concretize_revert_complete` in concretizeLayoutLocalTerminals transfers operand definedness using variable_domains and equal labels, producing Abort Revert and dead_result_rel without equal offsets, lengths or payload bytes. Consumers project domains via local_rel_domains and labels via relocation_env. RETURNDATACOPY's preceding event and global terminal dispatch remain pending. |
| STOP | halt_state, clear returndata / Halt | complete terminal result producer | `concretize_stop_sink_complete` in concretizeLayoutLocalTerminals consumes only incoming dead-result observation and source Halt; target Halt preserves observations with common empty returndata. No ordinary event or arity premises; terminal dispatch integration remains. |
| SINK | halt_state / Halt | complete terminal result producer | Same grouped export preserves existing returndata agreement and all other terminal observations; terminal dispatch integration remains. |
| PHI | base Error "phi outside prefix"; eval_phis / OK or Error | B6; conditional | Must use parallel block-entry interface. For a non-prefix PHI, successful source termination cannot continue through base Error; use wf shape and actual source execution, not a blanket absence claim. |
| PARAM | index vs_params then update_var / OK | `concretizeLayoutLocalParam.concretize_param_local_complete`; reachable producer checked | Consumes explicit indexed clean resolved parameter_roots, LENGTH rp alignment, PG erasure and resolution, ordinary trace, guarded local_rel, independent taint and both environments. Derives literal index and bound from source success, reuses resolved_parameter_step, produces target OK, actual origin_step resolution/provenance erasure, SUC demand, independently stepped target taint, preserved roots and both environments. Establishing/preserving indexed roots across full activation execution and dispatcher integration remain open; no parameter equality inferred from local_rel. |
| ASSIGN | eval_operand then update_var / OK | `concretizeLayoutLocalAssign.concretize_assign_local_complete`; complete singleton-output reachable boundary | Var/Lit/Label covered. Retains the canonical trace/resolved envelope, membership, both environment supplements, guarded local_rel and independent target taint. Derives operand from source success; preserves pointer/tainted/unequal opaque copies via B5 and retpc forward closure, constructs target OK, actual source prov/taint, independent target taint, SUC demand and both environments. No target-step or post-observation premise. Full dispatcher integration remains. |
| NOP | OK s | reachable producer checked | concretizeLayoutLocalNop.concretize_nop_local_complete derives empty outputs from o1_fn_shape and instruction membership, proves actual provenance/independent taint identities and successor-demand restriction, and preserves environment supplements. No operand-count assumption; full dispatch remains outstanding. |
| ALLOCA | exec_alloca / OK | B7; conditional | Existing/fresh cache split, source allocas_from lo, canonical selected target position, birth/lifetime and taint creation without memory writes, independent T and observation producer. Reuse canonical StepStructure facts. |
| DALLOCA | fmp allocation / OK | excluded | `~ctx_has_dalloca C`, its definition, context function membership and fn_insts membership exclude. No vs_alloca_next=0 argument. |
| DRET | pack_dret_dynamic / IntRet | excluded | fn_ptr_ok_def excludes DRET. Do not attempt dynamic return relocation. |
| GETFMP | update_var vs_fmp / OK | excluded | fn_ptr_ok_def excludes GETFMP. |
| SETFMP | update vs_fmp / OK | excluded | fn_ptr_ok_def excludes SETFMP. |
| RETFMP | eval_operands / IntRet with adopted fmp | excluded | fn_ptr_ok_def excludes RETFMP. |
| INITIAL_FMP | update_var vs_initial_fmp / OK | reachable producer checked with explicit initial_fmp equality | concretizeLayoutLocalInitialFmp.concretize_initial_fmp_local_complete derives empty operands from source success and preserves origin erasure, actual independent taint, successor demand, observations, environment supplements and initial_fmp equality. Incoming initial_fmp equality across activation remains a frame/dispatch obligation; it does not follow from local_rel. |
| BUMP | two ordered output writes / OK | reachable producer checked | concretizeLayoutLocalBump.concretize_bump_local_complete derives operand cleanliness from reachable discipline/resolved support, evaluates both operands in the prestate, and preserves actual two-output origin erasure and DRESTRICT taint, independent target taint, retained successor demand, observations and both environment supplements. No distinct-output or FMP equality premise. Frame/control alignment and dispatch consumption remain obligations. |
| INVOKE | base default Error; step_inst setup/run/merge/bind / OK,Halt,Abort,Error | delegated | Generic frame lifting, fuel, callee lookup/metadata, argument roots incl opaque pc, static call context, saved state/gas/params, returned values, lifetime/demand. Not an ordinary base step. |
| FMP_PARAM | vs_params index / OK | excluded | fn_ptr_ok_def excludes FMP_PARAM. |
| RETPC_PARAM | update_var vs_return_pc_token / OK | reachable opaque producer checked | concretizeLayoutLocalRetpc.concretize_retpc_param_local_complete derives opacity from source instruction membership and reuses parameter_roots_retpc_read. Preserves actual origin erasure, independent source/target taint, retained successor demand, observations and both environment supplements with unequal tokens and no literal-index bound. Frame/control alignment and dispatch consumption remain obligations. |
| CALLER, ADDRESS, CALLVALUE | exec_read0 call context / OK | complete | concretize_env_reader_local_complete consumes relocation_env (not inferred from Obs), actual ordinary event and independent taint order; constructs fresh clean result, actual G/T, successor D/O and environment. |
| ORIGIN, GASPRICE, CHAINID | exec_read0 tx context / OK | complete | concretizeLayoutLocalContextReaders.concretize_context_reader_local_complete consumes relocation_reader_context and relocation_env, actual ordinary event, singleton output and independent taint order; produces V/G/D/O/T and both supplements. Incoming context equality remains a frame-composition obligation. |
| COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, BASEFEE, BLOBBASEFEE | exec_read0 block context / OK | complete | Same grouped concretize_context_reader_local_complete boundary and explicit incoming frame/context obligations; no full-state equality assumed. |
| GAS | exec_gas / OK | complete | Reachable environment adapter consumes relocation_env with equal vs_gas_readings, consumes the same head (empty gives 0), preserves tails, constructs clean G/T and successor D/O. Obs alone supplies no gas-stream equality. |
| BLOCKHASH | exec_read1 blockhash / OK | complete | concretizeLayoutLocalIndexedContextReaders.concretize_indexed_context_reader_local_complete produces V/G/D/O/T and preserves both supplements from an actual ordinary event, source success, singleton input/output, source discipline, context wf, resolved configuration, function shape/membership, relocation_env, relocation_reader_context and independent taint order. Clean scalar index is now produced by the shared nonpointer_operand_clean boundary using reachable resolved support. Incoming environment/context supplements remain frame/dispatch obligations. |
| BLOBHASH | exec_read1 indexed tx blobhashes / OK | complete | Same grouped indexed-context boundary, including the out-of-bounds zero case; operand cleanliness is produced from reachable discipline/support, while incoming environment/context supplements remain obligations. |
| BALANCE | exec_read1 account balance / OK | complete reachable boundary | `concretize_balance_reader_local_complete` in `concretizeLayoutLocalBalanceReaders`: derives clean address and exact balance projection from masked account observation; constructs target step, actual ghosts, retained SUC demand and independent target taint. Incoming resolved frame, source trace/discipline and environment obligations remain open globally. |
| SELFBALANCE | exec_read0 own balance / OK | complete reachable boundary | Same grouped export; equal call address from `relocation_env`, exact balance projection despite dead storage. No operand restriction. Preserves both environment supplements; does not discharge frame admissibility. |
| CALLDATASIZE | exec_read0 calldata length / OK | complete reachable boundary | `concretize_calldata_reader_local_complete` in `concretizeLayoutLocalCalldataReaders`: calldata equality from `relocation_env`, unrestricted operands, actual ghosts and independent target taint, retained SUC demand and both environment supplements. Incoming source trace/discipline, resolved frame and admissibility obligations remain open globally. |
| CALLDATALOAD | exec_read1 calldata bytes / OK | complete reachable boundary | Same grouped export derives clean scalar offset using reachable discipline/resolved support and constructs equal clean result from equal calldata. No added cleanliness, successor-demand or post-observation premise; does not discharge frame admissibility. |
| CALLDATACOPY | write_memory_with_expansion / OK | complete reachable boundary | Grouped `concretize_calldatacopy_local_complete` in `concretizeLayoutLocalCalldataCopy` covers CALLDATACOPY/CODECOPY/DLOADBYTES through `clean_copy_source`, with explicit code/data equality and calldata equality from `relocation_env`. Derives scalar offset/size agreement and relocated destination; produces actual ghosts, SUC demand, independent target taint, both environment supplements and preserved code/data equality. Includes zero length and padded out-of-section offsets; no target-step, successor-demand, post-write payload-agreement or post-observation premise. Frame admissibility remains open globally. |
| RETURNDATASIZE | exec_read0 returndata length / OK | complete reachable boundary | `concretize_returndatasize_local_complete` in `concretizeLayoutLocalReturndataSize`: derives length equality from incoming observation, actual ghosts, retained SUC demand and independent target taint; preserves both environment supplements without operand restriction. Incoming trace/resolved-frame and global admissibility obligations remain open; no RETURNDATACOPY claim. |
| RETURNDATACOPY | bounds or memory write / Abort ExHalt or OK | complete nonexempt OK and bounds Abort; revert-forward pending | `concretize_returncopy_local_complete` in concretizeLayoutLocalReturnCopy derives target execution, actual ghosts, successor demand, independent target taint, Obs0, actual-D supplement and environment/reader/code/data preservation. Incoming Obs0 has an empty return mask, so copied bytes agree exactly. `concretize_returncopy_bounds_abort_complete` synchronizes bounds Abort and dead_result_rel D from reachable/resolved source and operand definedness, without destination geometry. Successful revert-forward copying requires terminal-aware composition and is not covered. |
| CODESIZE | exec_read0 code length / OK | complete reachable producer | `concretize_code_data_reader_local_complete` in concretizeLayoutLocalCodeDataReaders, with explicit code/data section equality supplement (also preserved); unrestricted operands for read0, actual G, successor D, observations, independent target T and both environment supplements. |
| CODECOPY | write_memory_with_expansion code slice / OK | complete reachable boundary | Same grouped `concretize_calldatacopy_local_complete` export, selecting `vs_code`; explicit code/data equality supplement is required and preserved. Actual G, successor demand and independent target taint; no cloned geometry or extra target-step premise. |
| EXTCODESIZE | exec_read1 account code length / OK | complete reachable producer | `concretize_extcodesize_local_complete` in concretizeLayoutLocalExtcodeSize: clean scalar address from reachable discipline; account code projection from masked account agreement; actual G, restricted successor D, observations, independent target T, and both environment supplements. |
| EXTCODEHASH | exec_read1 account code hash / OK | complete reachable producer | `concretize_extcodehash_local_complete` in concretizeLayoutLocalExtcodeHash: masked account agreement preserves code and account_empty (balance/nonce/code only, not storage); reachable clean address, actual G, restricted successor D, observations, independent target T and both environment supplements. |
| EXTCODECOPY | write_memory_with_expansion account code slice / OK | complete reachable boundary | `concretize_extcodecopy_local_complete` in `concretizeLayoutLocalExtcodeCopy` derives clean account/source-offset/size agreement from reachable discipline and resolved support; projects account code equality using `accounts_agree_except_code`. Uses shared `concretize_clean_write_geometry`, `clean_copy_ghosts` and `clean_copy_taint_order` from `concretizeLayoutLocalCalldataCopy`, not duplicated geometry. Produces target OK, actual source ghosts, SUC demand, independent target taint, both environment supplements and preserved code/data equality. Covers zero length and padded out-of-code offsets without account equality or target-step/post-agreement premises. Retains nonexempt-read guard; frame admissibility remains open globally. |
| SHA3 | Keccak memory slice then update_var / OK | complete reachable nonexempt boundary | `concretize_sha3_local_complete` in `concretizeLayoutLocalSha3` derives the two-input/single-output/evaluation envelope from the ordinary source event. Reachable resolved support makes size a clean equal scalar; variable-length `concretize_read_demand_geometry` and taint_ok give exact padded slice equality, including zero size, by inline public list extensionality (the existing general padded-slice Triviality is not exported; no duplicate helper added). Produces actual target OK, cleared result origin, SUC demand relation, provenance erasure, independent target taint and both environment supplements. No equal-offset/full-memory/hash/postcondition premise. Exempt paths and frame/dispatch admissibility remain open. |
| CALL | exec_ext_call or static-value guard / OK,Abort ExHalt,Error | missing | Equal clean gas/address/value/size, relocated argument/return ranges; request_agree_except, outcome consumption alignment, memory write and accounts/taint adoption, cc_static equality and static abort. |
| STATICCALL | exec_ext_call static=T / OK,Error | missing | As CALL without value guard; outcome stream and request agreement, return write geometry and independent T. |
| DELEGATECALL | exec_delegatecall / OK,Error | missing | Clean args and contract storage/transient taint empty from taint_ok; concrete EVM call boundary, memory write/observations and T. |
| CREATE, CREATE2 | exec_create or static guard / OK,Abort ExHalt,Error | missing | Clean initcode bytes/value/(salt); taint_ok emptiness for stor/trans; accounts/create state boundary, cc_static and definedness guard, actual G/D/O/T. |
| LOG | log record or static guard / OK,Abort ExHalt | complete Abort producer; reachable nonexempt OK complete | Same grouped static Abort export as SSTORE. `concretize_log_local_complete` in `concretizeLayoutLocalLog` derives all-arity operand normalization (including LOG0), clean size/topic equality via pointer-use discipline, and exact demanded padded data via `concretize_read_demand_geometry`. Produces identical appended entry with environment-supplied logger, actual unchanged provenance/taint, SUC demand restriction, independent target taint and both environments. No topic/data equality premises. Exempt paths and full frame/dispatch admissibility remain open. |
| SELFDESTRUCT | account balance transfer or static guard / Halt,Abort ExHalt | reachable terminal producers complete | `concretizeLayoutLocalSelfdestruct`: `concretize_selfdestruct_complete` and `concretize_selfdestruct_abort_complete` consume reachable discipline, resolved support, function shape/membership, relocation_env and guarded local_rel (arbitrary R; Halt observation for Halt, arbitrary Obs for Abort), plus actual source result. Operand equality is derived, not assumed. `accounts_agree_except_selfdestruct` preserves masked storage and balances through self-first transfer, including beneficiary=self. No ordinary event, successor demand or successor taint premise. Global dispatcher/frame integration remains unresolved. |
| INVALID | halt_state clear returndata / Abort ExHalt | complete terminal result producer | `concretize_invalid_complete` in concretizeLayoutLocalTerminals produces matching Abort and dead_result_rel directly, without incoming observation or arity premises. Terminal dispatch integration remains. |
| ASSERT | conditional revert_state / OK or Abort Revert | complete reachable OK and Abort producers | `concretize_assert_local_complete` and `concretize_assert_abort_complete` in concretizeLayoutLocalAssertions derive condition agreement from reachable discipline/resolved support. Actual ghosts, retained demand and independent T for OK; matching Revert abort with dead_result_rel, without ordinary-event premise for Abort. |
| ASSERT_UNREACHABLE | conditional halt_state / OK or Abort ExHalt | complete reachable OK and Abort producers | Same grouped exports: unchanged OK state and actual G/D/O/T; matching ExHalt abort separately. Global terminal dispatch remains pending. |
| DLOAD | exec_read1 data section slice / OK | complete reachable producer | `concretize_code_data_reader_local_complete` in concretizeLayoutLocalCodeDataReaders: explicit code/data equality supplement preserved; clean offset derived from reachable discipline, actual G, successor D, observations, independent target T and both environment supplements. |
| DLOADBYTES | write_memory_with_expansion data slice / OK | complete reachable boundary | Same grouped `concretize_calldatacopy_local_complete` export, selecting `vs_data_section`; explicit code/data equality supplement is required and preserved. Reuses destination/write complement and clean-byte taint arguments, including zero length. |
| OFFSET | exec_pure2 word_add / OK | reachable producer checked | concretizeLayoutLocalOffset.concretize_offset_local_complete derives clean variable operands from reachable nonpointer discipline, uses explicit relocation_env for label equality, and preserves actual origin erasure, independent source/target taint, restricted successor demand, observations and relocation_reader_context. Does not cover pointer-capable ADD/SUB or full dispatch. |

## Frozen exclusions and non-exclusions

`ptr_discipline_def` quantifies over frame-reachable configurations and provides `access_ok`, `taint_ok`, and per-function pointer discipline; use its actual projections rather than assuming all code shares the current activation's origins. For a reached instruction, membership in a context function plus `EVERY (fn_ptr_ok P)` yields the six fn_ptr_ok exclusions MEMTOP/DRET/GETFMP/SETFMP/RETFMP/FMP_PARAM. DALLOCA needs the separate context premise. INITIAL_FMP, BUMP, external calls, and environment reads are **not** excluded just because the pass is before another lowering. Any further o1 shape exclusion must be proved, not inferred from intended pipeline order.

`taint_ok` permits tainted variable operands only in ASSIGN, shift value position, and value positions of MSTORE/SSTORE/TSTORE/ISTORE; notably not MSTORE8. Memory read taint is allowed for MLOAD/ILOAD/MCOPY/RETURN, except `about_to_revert`. `access_ok` geometry is guarded by `~in_revert_forward`, a distinct condition. Never erase those guards while adapting complete memory lemmas.

## Wrappers and finite execution

1. `step_inst` is **not** a gas-charging wrapper: non-INVOKE is precisely step_inst_base. GAS consumption is in exec_gas. INVOKE decodes, looks up callee, evaluates args, sets up the callee, recursively executes, and merges/adopts/binds on IntRet; Halt/Abort/Error propagate. Static context is a state field preserved through setup/merge, and static write checks are in the base branches, not a common pre-step wrapper.
2. `exec_block` selects instruction by vs_inst_idx, propagates non-OK results, tests terminator/halted, and increments source index explicitly after nonterminator OK. Need target block/instruction alignment, next-index transport, no premature target halt and observation/control-frame invariance. `block_step` uses base only and is not an INVOKE simulation substitute.
3. `run_blocks` uses fuel, block lookup, parallel PHIs, phi_prefix_length reset and recursive block dispatch. B6 covers values for common PHI prefix only; origin/taint, successor demand, control and target transformed-prefix agreement still need composition.
4. `run_block` and `run_function` add block entry/entry-label setup. Canonical `concretizeStepStructure` already exports unchanged/nonalloca, PHI, terminator/nonterminator, labels, block/last/succs/cfg/reachability/id/wf facts. Reuse these plus frozen StepShape/Retpc/CallChecks; do not introduce duplicate transformation facts.
5. A terminating source context run can end Halt or Abort, not just an ordinary OK chain. `dead_result_rel` compares Halt observations, but Abort requires only `(source kind = Revert_abort ==> target kind = Revert_abort)`. This weaker Abort relation does not prove operand definedness or execution. The generic frame proof must connect local terminals to run_context and choose matching fuel; independent target taint is needed only where downstream simulation consumes it, not for a separate stage-taint theorem.

## Invariant sufficiency / grouped recommendation for strategist

The current memory Obs is a terminal observational relation, **not** a sufficient execution-state invariant. It omits gas streams, labels/control, params/token, call/tx/block contexts, code/data and outcome cursors. Counterexample reasoning at the interface level is immediate: two locally related states can have different CALLVALUE or GAS while having the same variables/memory/terminal observations. This is not a checked counterexample to the frozen theorem (the initial states there are identical); it demonstrates why wrapper/frame equalities must accompany local_rel. Do not strengthen frozen hypotheses or infer these equalities from dead_result_rel.

Highest-impact missing interface, described by inputs/outputs rather than a new admitted declaration:

- For an unchanged clean scalar value opcode, inputs must give the existing guarded local_rel, an actual source ordinary event, source discipline/shape, operand/output envelope, equality of the fields its semantic reader uses, source successful execution, current independent taint relation, and the event-derived retained-demand inclusion. Output must construct target successful execution, resolved `origin_set rv outputs NONE`, guarded bytes under **actual source step_taint**, successor joint demand and observations, actual prov erasure, and independent target step_taint order. Unary, ternary and state reads should share equal-write machinery; GAS additionally consumes paired gas streams; BUMP is multi-output and shifts cannot use the clean-result taint rule.
- The crucial side condition for a generic read0/read1 producer is reader equality on **related** states (and equal clean inputs for read1), not exact state equality. Prove this from a carried frame/environment invariant or account projection lemmas. Do not pass the desired post Obs as an unexplained premise.
- Group residual families by real state interface: (i) pure clean unary/ternary/scalar OFFSET, tainted shifts, scalar/opaque parameters and trivial NOP; (ii) immutable environment/read projections and GAS stream; (iii) byte producers for external-data copies, MSTORE8, ILOAD/ISTORE, hashing and return; (iv) storage/transient masked reads/writes and externally visible requests/outcomes; (v) control and terminal Abort/Halt, including revert-forward shortcuts. This is a recommendation, not authorization/scheduling of new work.
- Separately finish the existing concrete adapters for conditional scalar/affine/compare/assign/PHI/allocation boundaries. Do not expand each opcode into duplicate copies of their already-proved algebra.

## Verification

`holbuild` passed for concretizeLayoutLocalLoadTheory, concretizeLayoutLocalStoreTheory and concretizeLayoutLocalCopyTheory (TO_concretize_sim-20261105T054124Z_m9789_t001), and for frameRelocationScalarStepsTheory, frameRelocationAffineStepsTheory, frameRelocationCompareStepsTheory, frameRelocationGuardedStepsTheory, frameRelocationPhiTheory, frameRelocationAllocationStepsTheory, frameRelocationStoreStepsTheory, frameRelocationOpaqueTheory (TO_concretize_sim-20261105T054124Z_m9823_t001). This certifies the existing boundaries used by the inventory, not the missing families or final theorem. No probe theory ships.

## Checked reachable clean-value adapter

`concretizeLayoutLocalValuesTheory.concretize_clean_value_local_complete`
now covers ISZERO/NOT (one operand) and ADDMOD/MULMOD (three operands),
with one output, at an actual ordinary joint-trace event. Resolved reachable
support plus `fn_ptr_ok` excludes pointer origins; discipline supplies taint
cleanliness and the existing opaque-use boundary excludes return tokens.
No operand-cleanliness or successor-demand hypothesis is assumed. No writes
and the actual trace produce demand restriction. The conclusion includes
successful target execution, guarded successor values/memory/observations,
actual source provenance erasure, independent target `step_taint` inclusion,
and preservation of the minimal `relocation_env`.

Incoming obligations remain explicit: empty initial allocation cache,
`ptr_discipline`, context-wide pointer and instruction well-formedness,
resolved current config, local function shape/membership, operand-count and
output envelopes, successful source step, current guarded relation, independent
taint order and execution environment. This is not full dispatch/frame
composition. Binary clean-value cases, CALLVALUE/GAS reachable adapters and all
other outstanding inventory rows retain their previous conditional status.

## Checked reachable call-context/GAS adapter

`concretizeLayoutLocalEnvironmentTheory.concretize_env_reader_local_complete`
covers CALLER, ADDRESS, CALLVALUE and GAS at an ordinary joint-trace event. It derives
successor demand restriction from no writes and the explicit initial empty
allocation cache. It consumes current `relocation_env`, guarded `local_rel`,
independent taint order, one output and successful source execution; no operand
arity or cleanliness assumption is needed. It returns target execution,
successor guarded relation with actual source ghosts, provenance erasure,
independent target taint order and successor environment. These four readers are
therefore no longer merely conditional on arbitrary demand inclusion. This
does not produce the incoming environment at frame push/pop, cover other
execution readers, or close the remaining dispatch inventory.

## Checked nonpointer clean-family extension

`concretize_clean_value_local_complete` is generalized in place to
`clean_value_shape inst` excluding ADD/SUB/EQ/LT/GT, with the same incoming
and outgoing interfaces. In addition to ISZERO/NOT/ADDMOD/MULMOD it now covers
two-operand MUL, Div, Mod, SDIV, SMOD, Exp, SLT, SGT, AND, OR, XOR,
SIGNEXTEND and BYTE. The local classification, origin-exclusion and no-write
helpers were replaced by family versions, not duplicated. The former four-case
interface is a specialization of the single export. Pointer-capable arithmetic
and comparisons, shifts, frame environments and remaining inventory rows are
still outstanding; this extension supplies no new frame-composition result.

## Checked internal-call environment plumbing

`concretizeLayoutFrameEnvironmentTheory` produces both `relocation_env` and
`relocation_reader_context` through paired `setup_callee`,
`merge_callee_state`, `adopt_return_fmp` and successful `bind_outputs`.
`relocation_environment_return_plumbing` composes the actual return operations
and constructs successful target binding from its length agreement. Arguments,
opaque return tokens, return records, output lists and returned values may
all differ. Merge requires gas-tail equality of the completed callees, not
just the saved callers. No allocation-field equality is required.

This discharges only supplement preservation through call plumbing. Establishing
callee execution, related parameter roots, control alignment, external outcomes,
and the completed-callee gas agreement remains generic frame-composition work;
the INVOKE row is still delegated and uninstantiated. Verified together with
local environment and indexed-context reader consumers by holbuild
(TO_concretize_sim-20261105T054124Z_m10357_t001).

## Checked indexed parameter-root boundary

`concretizeLayoutParameterRootsTheory` defines `parameter_roots R xs ys`
by equal length and index-dependent pointwise `R`. Paired successful
`setup_callee` installs these roots; paired variable writes preserve them.
`parameter_roots_read` groups PARAM/FMP_PARAM, constructs the target successful
read from source success, and exposes the two read values related at `w2n idx`.
The values need not be equal. `parameter_roots_retpc_read` separately exposes
writes of the respective return-PC tokens without index bounds or token equality.
The existing `setup_callee_opaque_token` remains the token-setup boundary.

This is a generic semantic parameter interface, not a complete reachable PARAM
adapter: caller argument evaluation must still produce the indexed relation,
instantiated with resolved pointer/scalar/opaque classifications and parameter
taints. Origin/parameter-ghost transport, independent target taint, successor
demand, guarded output writes and control alignment remain obligations. FMP_PARAM
is still excluded by frozen fn_ptr_ok in the concrete simulation; its grouped
semantic read fact does not reclassify it as a clean scalar. RETPC_PARAM's
opaque-output adapter is now checked in concretizeLayoutLocalRetpc (see row above).
The parameter-root facts were verified by holbuild alongside the existing
frame/environment and local memory helpers (TO_concretize_sim-20261105T054124Z_m10375_t001,
TO_concretize_sim-20261105T054124Z_m10384_t001).

## Checked caller argument-root producer

`concretizeLayoutArgumentRootsTheory.argument_roots_evaluation` now constructs
successful target `eval_operands` and the concrete indexed `parameter_roots`
from the caller guarded local relation and label equality. Variable roots carry
both guarded pointer and source-mask byte relations; constants/labels carry
equality. `argument_roots_setup` composes evaluation with paired callee setup,
without assuming a parameter relation at the call site. Nonopaque roots expose
`copy_ptr`/`copy_bytes`; clean scalar roots imply equal values. Opaque roots
intentionally need not be equal. Empty argument lists and arbitrary list lengths
are included by structural induction.

This produces the caller-value portion of the incoming parameter interface;
callee resolved-origin/parameter-taint ghost transport, independent target taint,
control alignment and generic execution composition remain open. In particular
no callee execution or full INVOKE simulation is asserted. Build checked with
parameter and frame-environment theories
(TO_concretize_sim-20261105T054124Z_m10411_t001).

## Checked disciplined callee roots

`concretizeLayoutCalleeRootsTheory` normalizes the caller value roots to
`clean_resolved_root L` indexed by `MAP (resolved_op rv) ops` for a decoded
INVOKE. Discipline excludes opaque and tainted call arguments. Origin-free
roots give equality; resolved pointer roots retain token-specific displacement,
not equal values. `disciplined_invoke_setup_roots` installs these roots through
paired setup. The existing `resolution_arguments_erasure` identifies the erased
resolved argument vector with actual raw parameter provenance; it is reused,
not restated. The frozen call ghost clears variable taint rather than installing
a new parameter-taint vector. PARAM output preservation, callee local relation,
control and execution composition remain open. Build checked by holbuild
(TO_concretize_sim-20261105T054124Z_m10439_t001).

## Frame composition interface reconciliation (E0318 follow-up)

This section supersedes the stale PARAM row and the residual parameter-ghost
claims above, but does not promote the INVOKE row to complete.

| Composition use site | Authoritative existing exports | What remains |
|---|---|---|
| Evaluate caller arguments | `argument_roots_evaluation`, `argument_roots_setup` in concretizeLayoutArgumentRoots | Carry label equality and caller guarded relation; no equality of opaque arguments. |
| Normalize disciplined incoming roots | `disciplined_invoke_roots`, `disciplined_invoke_setup_roots` in concretizeLayoutCalleeRoots | Supply shape, instruction membership, fn_ptr_ok and taint_ok from reached caller. Output is clean_resolved_root indexed by MAP (resolved_op caller_rv) ops. |
| Install/read parameters | `parameter_roots_setup_callee`, `parameter_roots_read` in concretizeLayoutParameterRoots | Setup requires target blocks nonempty. FMP_PARAM remains excluded; RETPC_PARAM is separate and opaque. |
| PARAM actual successor | `resolved_parameter_step`, `resolved_call_parameter_step` in concretizeLayoutParameterSteps | Complete base-step value/origin/actual source and independent target taint preservation at unchanged R; generic paired-update Obs stability. No parameter-taint vector is needed. Event-derived next-demand restriction, control/index and actual step_inst connection remain outside this theorem. |
| Raw PG consistency | `resolution_arguments_erasure` in frameResolvedOrigins, consumed by resolved_call_parameter_step | Do not add another erasure assumption or restate this lemma. |
| Call environment | `relocation_environment_setup_callee` and `relocation_environment_return_plumbing` in concretizeLayoutFrameEnvironment | Both relocation_env and relocation_reader_context transported. Return needs equal completed-callee gas tails; no returned value relation, origin/taint restoration or control alignment is asserted. |

Residual generic call obligations are: paired callee lookup and entry/PHI
control; initialization of callee variable domains, origin maps and taints;
saved caller lifetime/resolution transport; recursive successful callee
execution at adequate common fuel; related returned FRONT values rather than
equal final return tokens; restoring caller origins/taints and output binding;
and demand preservation across push/pop. Environment return plumbing alone
cannot discharge these. No existing export above proves a callee run.

### Demand/history scope

`frameRelocationBinding.joint_relocation_demand` is indexed exclusively by
`q0::qs` and `es` of a **source** joint_trace. Its future observed read,
write-complement and activation_cache witnesses are source witnesses.
`joint_relocation_demand_retained` consumes source joint_trace and empty initial
allocation cache; `joint_relocation_demand_clean` and nonrevert properties
likewise concern that source trace. The concrete Layout local memory and
clean-value consumers use source ordinary events plus a target successful-step
witness they construct, not a target joint_trace premise. Independent target
taint inclusion is a pointwise successor invariant, not target-history
reflection. A search of concretizeLayout proof sources found no target-trace,
target-history or reflection premise. Thus this audit identifies **no current
local demand consumer requiring universal target-history reflection**.
This does not prove it unnecessary for every unfinished terminal/external
request boundary; those interfaces must be audited when designed. In
particular no removed stage-taint-only obligation is silently reinstated.

### Existing execution replay and exact branch facts

`venom/compiler/frameExecutionPrefixScript.sml` already provides
`prefix_step_fuel_mono`, `prefix_exec_fuel_mono`, `local_return_suffix_next`,
`local_return_suffix_block`, `execution_prefix_continuation` and
`execution_prefix_return`. These construct existential-fuel IntRet suffixes
through wf functions and active instructions. Reuse them for that interface;
they are not a fixed-fuel, arbitrary-result finite block-prefix relation.
No generic finite segment replay export was found in the searched frame
libraries. A new segment boundary must not duplicate those return-suffix facts.

Actual exec_block (venomExecSemanticsScript.sml:1732-1745) has no independent
pre-state halted test: a successful nonterminator continues with post-state
index set to SUC of the **pre-state** index, regardless of post.vs_halted.
Terminator OK converts to Halt exactly when post.vs_halted; all non-OK
constructors propagate immediately. These exact conditions, not an invented
no-halt transition, govern the finite replay definition. INVOKE can only be
used through an actual step_inst witness; replay does not construct recursive
callee fuel. run_blocks separately resets the index after parallel PHIs and
uses the decremented block fuel. Forward unequal-length source/target prefixes
remain compatible with this interface.

## Finite replay and residual call boundary checkpoint (E0320 onward)

`frameBlockSegments` supplies fixed-fuel arbitrary-result replay and paired
replay for independent finite nonterminator prefixes. Its update uses the
pre-step index and has no post-halted test. `concretizeLayoutParameterSegments`
consumes `resolved_parameter_step` through actual `step_inst` and builds both
segments plus next-control alignment. The local/ghost relation remains on the
post states, not on index-updated states for arbitrary Obs.

`concretizeLayoutCallControl` checks paired setup control and empty variable
maps, and restores the saved caller control through actual merge/adopt/bind.
Paired caller control gives next-index control after the call. The completed
callee controls and returned tokens need not agree. `paired_return_values`
uses `opaque_return_token_step` for actual RET wrappers with independent final
tokens, retaining LIST_REL only on the returned FRONT values (possibly empty).
It does not derive that value relation from local_rel. Existing
`return_bind_allocation_frame` and `frame_cache_separated_pop` remain the
allocation-frame and separation restoration interfaces; no copies were added.

### Precise still-missing composition interfaces

- Entry control equality alone does not relate PHI-selected values or
  establish the callee guarded relation: empty variable maps are available,
  but the incoming parameter resolution, ghost variable taint, demanded
  memory and observation supplements must be assembled at the source push.
- Source `joint_transition` provides push/pop events and saved caller ghosts;
  no theorem here transports the full saved caller resolved origin map and
  guarded variable relation across a recursively executed callee. Callee
  memory changes must preserve bytes demanded on return in the caller.
- `paired_return_values` deliberately assumes related FRONT values. To produce
  them requires the reached RET discipline/opaque exclusion, operand reads,
  and current resolved value relation, plus the actual source taint mask.
  Output binding must then pair returned roots with the saved caller origin
  map and actual pop taint update, not copy the callee variable map wholesale.
- Current local producers consume ordinary source events. They do not yet
  establish source push/pop demand inclusion or exclude new callee accesses
  from saved caller demanded bytes. Activation identity must survive changes
  in stack depth without treating equal numerical bases as equal origins.
- Replay is at fixed fuel; completed step witnesses are inputs. Successful
  non-error fuel monotonicity exists in frameExecutionPrefix. No helper here
  constructs a common adequate target fuel for recursive INVOKE/run_blocks,
  pairs terminal Error/Halt/Abort outcomes, or supplies PHI/block-exit control.

These are residual obligations, not new assumptions asserted by the stage
contract or a certification of generic recursive simulation. The next PLAN
refinement must explicitly own PHI entry, recursive block/call replay and fuel,
caller saved-root/returned-root binding and source push/pop demand transport.

## Parallel PHI value/ghost checkpoint

`concretizeLayoutLocalPhi.concretize_parallel_phis_transport` now consumes
successful source `eval_phis`, the guarded incoming relation, independent
`relocation_taint_le`, both environment supplements, equal previous block,
and membership of all instructions in the current function. It produces
successful target parallel PHIs, resolved output origins and their actual
`phis_prov` erasure, source `phis_taint` masks, independently computed target
`phis_taint` inclusion, and both preserved environment supplements.
The observation is concretely `dead_result_rel D` on Halt, not an assumed
post-observation. Demand R remains unchanged in this value-only boundary.
Selections use original maps, including aliased destinations and inputs;
no output-distinctness or equality of parameter values is assumed.

The existing `venomExecProofs.eval_phis_only_updates_vs_vars` is the canonical
field-frame fact: successful PHIs change only `vs_vars`. Reuse it for control,
code/data, initial FMP, parameters and allocation metadata; no duplicate
field-preservation lemma was added. `phis_taint_subset` and
`relocation_taint_le_phis` provide the independent-mask monotonicity boundary.
The actual OriginBlock event adapter (preceding terminator, next demand,
index reset and transformed-prefix alignment) remains open; this checkpoint
does not apply ordinary-event demand retention to a block event.

## D0007 owned-interface checkpoint (2026-11-06)

All formerly delegated LocalState/LocalExternal/LocalHaltAbort overlays are
removed. No theorem from those theories is available or assumed. State OK,
external calls/create, RETURNDATACOPY and RETURN remain **missing** concrete
families; terminal Abort exports already listed remain reusable.

### Checked composition, not a new permanent wrapper

A temporary `nop_interface_probe` was checked by holbuild
(TO_concretize_sim-20261105T171004Z_m12642_t001), then removed from the working
sources. It takes the exact antecedent of `concretize_nop_local_complete`,
replaces its observation by `concretize_local_obs`, and adds
`concretize_supplement D tn s t`. It derives target execution, successor
local_rel, actual provenance erasure, independent target taint order, both
environments and successor supplement. The actual task D is independent of
the universal local-observation mask. No family obligation is assumed.
`concretizeLayoutBlockEntryTheory` also builds on the current base
(TO_concretize_sim-20261105T171004Z_m12631_t001).

The observation definition is *partially applied* in local_rel. Rewriting its
pointwise equation with simp does not rewrite that argument. The checked
specialization uses `rewrite_tac[lambdify (lambdify
concretize_local_obs_def)]`, then `drule_all` on the existing producer with
its free D instantiated to the fixed local mask. This is definitional
specialization, not an additional lemma. NOP has post=s and unchanged actual
taint, so supplement preservation is immediate. Nontrivial variable writers
must use `concretize_supplement_fields` or its update_var/control corollaries;
the NOP experiment does not certify those opcodes' supplement adapters.

### Common certificate proposal

Keep incoming source trace/resolved/lifetime/membership/shape and layout
premises exactly as in the applicable accepted family. Carry, separately:

- local_rel with fixed concretize_local_obs at current joint demand;
- relocation_taint_le for independent source tn and target un;
- concretize_supplement D tn s t (actual task mask);
- relocation_env and relocation_reader_context;
- code/data-section equality, initial-FMP equality, current/previous block and
  instruction-index alignment where needed; indexed parameter_roots with
  resolved rp and parameter-taint/length alignment, and PG erasure/support.

An ordinary OK output constructs target success (never assumes it), actual
resolved origin_step and step_prov erasure, local_rel at successor demand
using actual source step_taint, independent target step_taint order,
source-taint-indexed successor supplement, and preservation of each required
administrative field. Output origins cannot uniformly be origin_set NONE:
ASSIGN/affine preserve pointers, PARAM imports roots, ALLOCA introduces one.
PHIs remain a block-entry certificate. RETURN/Halt/Abort use separate exits,
not ordinary post local_rel.

`frameIndexedCertificates.indexed_base_def:23-30` consumes every non-Error base
result, not only OK. Its Q must preserve result shape and permit OK exit back
into indexed_entry; indexed_push/pop/phi additionally consume callee lookup,
argument/root setup, returned values, saved caller state and block-prefix
alignment. No control/root field is supplied by local_rel itself. This
checkpoint does not construct A/R/Q or prove indexed_base.

### Exact missing semantic bridges, source backed

1. **Masked SLOAD/TLOAD** (`venomState.sload_def/tload_def`,
   `ptrDiscipline.out_taint_def:332-354`): at equal clean keys and equal call
   address, supplement implies
   `word_agree_except (key_taint tn.t_stor key) (sload key s) (sload key t)`
   and the analogous t_trans/tload statement. This must feed paired masked
   output writes and actual independent target out_taint, not equal-word
   machinery. Need shared pointwise masked-store update algebra for
   key_update and then full successor supplement. ISTORE additionally needs
   memory-write geometry and imms domain/update agreement. No such complete
   family is asserted here.
2. **Request/outcome bridge** (`venomCallOracleDefs:11-44,76-98`): derive
   `request_agree_except D rq rq'` for constructed requests from clean scalar
   inputs, relocated equal clean input slices and the *request clause* of
   taint_within. Equal incoming outcome streams must align take_outcome;
   agreement of requests alone is not that stream equality. Transport
   adopt_outcome, record_request, deletion/log append, exact returned oracle
   bytes and ret-buffer writes; rebuild successor supplement with actual
   adopt_reset taint. `exec_delegatecall_def:512-525` instead runs concrete
   EVM semantics: it is NOT an oracle consumer. Its run/extract transport
   requires a separate boundary under the actual taint_ok restrictions;
   CALL/CREATE oracle proofs cannot silently cover DELEGATECALL.
3. **Final observation** (`ptrDiscipline:862-883`): for final_taint vs0 C sh
   tn R, taint_within provides current-address storage/transient, immutable
   and return mask inclusion. Need a boundary combining supplement D tn sh th,
   equal terminal logs/deletions/halted fields, equal return length and
   lane equality outside R into `dead_result_rel D (Halt sh) (Halt th)`.
   RETURN (`venomExecSemantics:808-817`) constructs its own padded slice and
   sets returndata; prove length and clean-lane equality from demand geometry,
   then use this boundary. Do NOT require concretize_local_obs sh th after
   RETURN: its empty d_ret demands exact payload equality, too strong for
   tainted return lanes. Incoming Obs0 remains appropriate before the halt.
4. **ALLOCA still conditional**: local_rel_alloca_assign_step's pointer,
   bytes and post-Obs premises are not generated by its execution equations.
   Cached and fresh branches need activation_lookup/canonical position,
   allocas_from lo, origin introduction/retention and independent target taint;
   demand restriction must exclude newly born bytes and use lifetime/layout
   separation for retained bytes, including zero size. Unchanged accounts,
   transient, immutables, requests/outcomes give supplement; paired allocator
   updates preserve Obs0 but must be proved from the concrete steps. No
   positivity premise from the comparison proof licenses allocating zero size.

These are interface findings for strategist refinement, not admitted HOL
statements or completion claims. No executable/frozen source was changed.
