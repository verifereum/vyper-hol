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

## Exhaustive constructor inventory

The obligations column refines V/G/D/O/T above. All semantic helpers here are in `venomExecSemantics`; all rows with operand envelopes can also return Error for malformed/undefined operands. No row silently excludes Error. References B1..B10 refer to numbered boundaries above.

| Constructor(s) | Semantic helper / non-Error outcomes | Existing boundary; status | Reachable premises and outstanding obligations |
|---|---|---|---|
| ADD | exec_pure2 word_add / OK | B2,B3; conditional | Scalar/pointer-left/pointer-right split from fn_ptr_ok and resolved origin; clean scalar from taint_ok and nonopaque use; G/D/T adapters. |
| SUB | exec_pure2 word_sub / OK | B2,B3; conditional | Pointer-left or scalar only under affine discipline; do not assume arbitrary pointer subtraction covered; G/D/T adapters. |
| MUL, Div, SDIV, Mod, SMOD, Exp | exec_pure2 / OK | B2; conditional | All inputs clean nonpointer/nonopaque; actual source proof from discipline; D/T adapters. |
| ADDMOD, MULMOD | exec_pure3 / OK | missing | Three clean scalar inputs, clean result origin/taint, V/G/D/O/T producer; B2 is binary only. |
| EQ, LT, GT | exec_pure2 / OK | B2,B4; conditional | Scalar or same-site pointer pair; same lifetime token and numeric bounds must be derived; no mere numeric-origin inversion; D/T adapters. |
| SLT, SGT | exec_pure2 signed comparison / OK | B2; conditional | Must be scalar; access_ok's unsigned pointer comparison clause does not authorize signed pointer comparisons. |
| ISZERO | exec_pure1 / OK | missing | Clean scalar, nonpointer/nonopaque input from discipline; unary result clearing and V/G/D/O/T. Existing base dispatch equation alone is not preservation. |
| AND, OR, XOR | exec_pure2 / OK | B2; conditional | Clean scalar inputs; no pointer/opaque or tainted use; D/T adapters. |
| NOT | exec_pure1 / OK | missing | Same unary family as ISZERO. |
| SHL, SHR, SAR | exec_pure2 shift / OK | missing | Clean shift amount; value may be tainted by taint_ok. Need byte-mask shift/SAR propagation, actual `out_taint` and independent T. Scalar_binary_opcode explicitly omits these. |
| SIGNEXTEND, BYTE | exec_pure2 / OK | B2; conditional | Both inputs clean scalar (not the shift taint exception); D/T adapters. |
| MLOAD | exec_read1 mload / OK | B8; complete | Full concrete pre-interface still required: joint ordinary event, resolved/lifetime, nonexemption, labels, local_rel and independent T. Result origin is erased. |
| MSTORE | exec_write2 mstore / OK | B8; complete | Same concrete event/interface requirements; paired possibly tainted stored word and actual ghost/T handled. |
| MSTORE8 | exec_write2 mstore8 / OK | B9; complete | concretizeLayoutLocalStore8 exports concrete one-byte geometry and concretize_mstore8_local_complete: clean equal stored value from discipline, actual step_prov/step_taint, independent target taint inclusion, dead-result observation and restored-memory equalities retaining all execution-environment fields. Geometry shares coherent_written_interval with MSTORE. |
| MCOPY | direct mcopy / OK | B8; complete | Nonexempt concrete source event; zero/positive lengths, read/write geometry and independent T covered in accepted boundary. |
| MEMTOP | exec_read0 memory length / OK | excluded | `ptr_discipline_def` gives EVERY fn_ptr_ok; `fn_ptr_ok_def:123-126` excludes at member instruction. No equality of source/target memory lengths is available. |
| SLOAD | exec_read1 sload / OK | missing | Clean scalar key and same call address; dead storage may differ. Need masked word agreement using tn/un storage taints, not full word equality or equal accounts. G clearing, D, O and independent T. |
| SSTORE | static check or exec_write2 sstore / Abort ExHalt or OK | missing | Static guard compares cc_static and operand definedness (before helper arity checking); clean key, value may be tainted; observable storage agreement outside D, taint_within, actual G/T; static terminal branch separately. |
| TLOAD | exec_read1 tload / OK | missing | As SLOAD for transient store and t_trans; same call address required. |
| TSTORE | static check or exec_write2 tstore / Abort ExHalt or OK | missing | As SSTORE for transient storage. |
| ILOAD | exec_read1 mload / OK | missing | fn_ptr_ok forces nonpointer variable operands; memory-backed, not a finite-map lookup! Needs fixed-region demand, clean-lane result, source/target taint and G; MLOAD opcode-specific theorem cannot simply rewrite to ILOAD. |
| ISTORE | istore / OK | missing | Fixed-region clean scalar address by fn_ptr_ok, tainted value allowed; writes memory AND immutable bookkeeping. Need both demanded memory and imms_agree_except, actual G/T. |
| JMP | jump_to / OK | missing | Same label literal; prev/current block and index alignment, unchanged values, retained demand and ghost/T. Obs alone does not give control equality. |
| JNZ | condition then jump_to / OK | missing | Clean scalar/nonopaque/nonpointer condition, same selected label; control plus G/D/O/T. |
| DJMP | extract_labels, selector-indexed jump_to / OK or Error bounds | missing | Equal clean selector and label environment, same label list, bounds/error matching; control plus G/D/O/T. |
| RET | eval_operands then IntRet | B10; delegated to generic frame boundary | Equal/related FRONT return values, not final opaque pc; saved frame params/origins/taints, return cache/lifetime/demand and merge. Existing opaque token fact is only one ingredient. |
| RETURN | memory slice, set_returndata, halt_state / Halt | missing | Relocated offset/size, demanded clean lanes, equal length and bytes outside D.d_ret using taint_within; terminal G/T. Equality of all return bytes is too strong. |
| REVERT | memory slice, revert_state / Abort Revert | missing | Exempt reads may be tainted; source/target operand definedness/address need not imply equal payload. Match Abort Revert; do not invoke nonexempt MLOAD/MCOPY geometry. |
| STOP | halt_state, clear returndata / Halt | missing | No operands needed by semantics. Produce terminal dead_result_rel from pre-observations and common empty returndata; terminal ghost adapter. |
| SINK | halt_state / Halt | missing | Preserve existing returndata agreement and other observations; terminal ghost adapter. |
| PHI | base Error "phi outside prefix"; eval_phis / OK or Error | B6; conditional | Must use parallel block-entry interface. For a non-prefix PHI, successful source termination cannot continue through base Error; use wf shape and actual source execution, not a blanket absence claim. |
| PARAM | index vs_params then update_var / OK | missing | Related parameter vectors with resolved rp/PG, bounds and output byte taint; local_rel says nothing about vs_params. Need explicit scalar/pointer entry roots, origin_set and independent parameter taint. |
| ASSIGN | eval_operand then update_var / OK | B5; conditional | Var/constant/Label split; labels equality, retpc forward closure. Actual ghost available for variable copy; demand/T and concrete event adapter remain. |
| NOP | OK s | missing | State unchanged, but step_prov and step_taint still depend on outputs; use wf outputs or compute actual ghost updates. Demand c->SUC c still required. |
| ALLOCA | exec_alloca / OK | B7; conditional | Existing/fresh cache split, source allocas_from lo, canonical selected target position, birth/lifetime and taint creation without memory writes, independent T and observation producer. Reuse canonical StepStructure facts. |
| DALLOCA | fmp allocation / OK | excluded | `~ctx_has_dalloca C`, its definition, context function membership and fn_insts membership exclude. No vs_alloca_next=0 argument. |
| DRET | pack_dret_dynamic / IntRet | excluded | fn_ptr_ok_def excludes DRET. Do not attempt dynamic return relocation. |
| GETFMP | update_var vs_fmp / OK | excluded | fn_ptr_ok_def excludes GETFMP. |
| SETFMP | update vs_fmp / OK | excluded | fn_ptr_ok_def excludes SETFMP. |
| RETFMP | eval_operands / IntRet with adopted fmp | excluded | fn_ptr_ok_def excludes RETFMP. |
| INITIAL_FMP | update_var vs_initial_fmp / OK | missing | NOT excluded by fn_ptr_ok. Need equality/meaning of initial_fmp across activation and scalar root taint/G; local_rel alone insufficient. |
| BUMP | two output writes / OK | missing | NOT excluded by fn_ptr_ok. Must inspect ptr_use_ok to derive scalar restrictions; paired double-write, actual multi-output set_prov erasure and taint, D/O/T. |
| INVOKE | base default Error; step_inst setup/run/merge/bind / OK,Halt,Abort,Error | delegated | Generic frame lifting, fuel, callee lookup/metadata, argument roots incl opaque pc, static call context, saved state/gas/params, returned values, lifetime/demand. Not an ordinary base step. |
| FMP_PARAM | vs_params index / OK | excluded | fn_ptr_ok_def excludes FMP_PARAM. |
| RETPC_PARAM | update_var vs_return_pc_token / OK | B10; missing local adapter | Tokens may differ; guard opaque output, origin erase, actual taint and independent T, no equality of LAST args. |
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
| CALLDATACOPY | write_memory_with_expansion / OK | missing | Same calldata/source scalar offset/size, relocated destination and write-complement; written bytes/taint plus independent T and unchanged observations. |
| RETURNDATASIZE | exec_read0 returndata length / OK | complete reachable boundary | `concretize_returndatasize_local_complete` in `concretizeLayoutLocalReturndataSize`: derives length equality from incoming observation, actual ghosts, retained SUC demand and independent target taint; preserves both environment supplements without operand restriction. Incoming trace/resolved-frame and global admissibility obligations remain open; no RETURNDATACOPY claim. |
| RETURNDATACOPY | bounds or memory write / Abort ExHalt or OK | missing | Equal lengths imply same OOB branch; bytes can differ in dead tainted lanes. Revert-forward exemption requires terminal-aware path, not unjustified clean equality. Destination relocation/write complement, actual T, or Abort result. |
| CODESIZE | exec_read0 code length / OK | complete reachable producer | `concretize_code_data_reader_local_complete` in concretizeLayoutLocalCodeDataReaders, with explicit code/data section equality supplement (also preserved); unrestricted operands for read0, actual G, successor D, observations, independent target T and both environment supplements. |
| CODECOPY | write_memory_with_expansion code slice / OK | missing | Equal code, clean source scalar offset/size, destination/write geometry and T. |
| EXTCODESIZE | exec_read1 account code length / OK | complete reachable producer | `concretize_extcodesize_local_complete` in concretizeLayoutLocalExtcodeSize: clean scalar address from reachable discipline; account code projection from masked account agreement; actual G, restricted successor D, observations, independent target T, and both environment supplements. |
| EXTCODEHASH | exec_read1 account code hash / OK | complete reachable producer | `concretize_extcodehash_local_complete` in concretizeLayoutLocalExtcodeHash: masked account agreement preserves code and account_empty (balance/nonce/code only, not storage); reachable clean address, actual G, restricted successor D, observations, independent target T and both environment supplements. |
| EXTCODECOPY | write_memory_with_expansion account code slice / OK | missing | Clean external address/source offset/size; account code agreement, destination geometry and T. |
| SHA3 | Keccak memory slice then update_var / OK | missing | Clean demanded input bytes from taint_ok except exempt terminal path; equal hashes and cleared result origin; geometry plus G/D/O/T. |
| CALL | exec_ext_call or static-value guard / OK,Abort ExHalt,Error | missing | Equal clean gas/address/value/size, relocated argument/return ranges; request_agree_except, outcome consumption alignment, memory write and accounts/taint adoption, cc_static equality and static abort. |
| STATICCALL | exec_ext_call static=T / OK,Error | missing | As CALL without value guard; outcome stream and request agreement, return write geometry and independent T. |
| DELEGATECALL | exec_delegatecall / OK,Error | missing | Clean args and contract storage/transient taint empty from taint_ok; concrete EVM call boundary, memory write/observations and T. |
| CREATE, CREATE2 | exec_create or static guard / OK,Abort ExHalt,Error | missing | Clean initcode bytes/value/(salt); taint_ok emptiness for stor/trans; accounts/create state boundary, cc_static and definedness guard, actual G/D/O/T. |
| LOG | log record or static guard / OK,Abort ExHalt | missing | Clean topic count/topics/size, demanded clean data bytes, same logger address; append identical event, actual G/D/T; static guard before operand envelope. |
| SELFDESTRUCT | account balance transfer or static guard / Halt,Abort ExHalt | missing | Clean beneficiary, same self address, account balance update preserves dead relation; pending deletion/result handling per actual semantics (this branch only transfers balance); static Abort separate. |
| INVALID | halt_state clear returndata / Abort ExHalt | missing | No operand checks; dead_result_rel Abort clause suffices once target Abort produced; terminal ghost adapter. |
| ASSERT | conditional revert_state / OK or Abort Revert | missing | Equal clean condition; actual ghost/no-write T in OK case, matching revert terminal in false case. |
| ASSERT_UNREACHABLE | conditional halt_state / OK or Abort ExHalt | missing | Equal clean condition; OK and exceptional terminal handled separately. |
| DLOAD | exec_read1 data section slice / OK | complete reachable producer | `concretize_code_data_reader_local_complete` in concretizeLayoutLocalCodeDataReaders: explicit code/data equality supplement preserved; clean offset derived from reachable discipline, actual G, successor D, observations, independent target T and both environment supplements. |
| DLOADBYTES | write_memory_with_expansion data slice / OK | missing | Equal data section, clean scalar source offset/size, relocated destination/write geometry and T. |
| OFFSET | exec_pure2 word_add / OK | missing | Not in scalar_binary_opcode; label lookup equality required; pointer Label arithmetic forbidden by fn_ptr_ok for ADD/SUB only, so inspect ptr_use_ok rather than assuming OFFSET pointer preservation. Need actual origin/taint rule. |

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
semantic read fact does not reclassify it as a clean scalar. RETPC_PARAM still
needs the opaque-output adapter. Verified by holbuild alongside the existing
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
