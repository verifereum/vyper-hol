# DSE integration audit (C2.4.26.19)

This is a source/signature audit, **not a semantic completeness certificate**.
The frozen proofs and public wrappers have not been edited. Existing family
proofs remain the implementation; the interfaces below are proposed obligations,
not assumed facts. Baseline build: ResidualSimpleSteps and DelegateCallSteps clean.

## Exhaustive supported-space map

M = Memory, K = Storage or Transient. Rows partition `dse_opcode_coverage`
(expanding its two named predicates); Error on the original side is exempt.
Names below are theorem names in the correspondingly named helper theories.
“Indexed” means local agreement after common SUC cursor updates and pending-at
at SUC on the original raw result. “Raw” means local agreement before updates.
Retention still has to be supplied when composing same-instruction semantics
with `dse_inst`; do not infer retention from a successful simulation alone.

| Opcodes | M interface | K interface | Result/retention and gaps |
|---|---|---|---|
| ADD SUB MUL Div Mod SDIV SMOD Exp ADDMOD MULMOD EQ LT GT SLT SGT ISZERO AND OR XOR NOT SHL SHR SAR SIGNEXTEND BYTE | `dse_local_agrees_pure_step`, indexed | same | `dse_pure_result_cases` OK/Error; retention follows no memory-definition effect, no separate retention theorem |
| CALLER ADDRESS CALLVALUE GAS ORIGIN GASPRICE CHAINID COINBASE TIMESTAMP NUMBER PREVRANDAO GASLIMIT BASEFEE BLOBBASEFEE BLOCKHASH BLOBHASH CALLDATASIZE CALLDATALOAD RETURNDATASIZE CODESIZE DLOAD | `dse_local_agrees_frame_read_step`, indexed | same | `dse_frame_read_result_cases`; `dse_frame_read_retained` uses successful OK plus sound ids. DLOAD has a static write: guarded no-clobber/retention only |
| MLOAD SLOAD TLOAD | `dse_local_agrees_load_step`, indexed | same | `dse_load_result_cases` OK/Error; no deletion since no write effect |
| MSTORE MSTORE8 | `dse_local_agrees_mstore_step` retained, `dse_local_agrees_mstore_deleted_step` deleted | retained other-space branch of first theorem | `dse_mstore_result_cases`; deletion requires sound occurrence and empty outputs; pending set existential |
| SSTORE TSTORE | `dse_local_agrees_key_store_step` other-space | same-space retained or `dse_local_agrees_key_store_deleted_step` deleted | `dse_key_store_result_cases`; pending set existential |
| MCOPY | `dse_local_agrees_mcopy_step` retained or `dse_local_agrees_mcopy_deleted_step` | other-space branch of retained theorem | `dse_mcopy_result_cases`; pending set existential |
| CALLDATACOPY CODECOPY DLOADBYTES | `dse_local_agrees_external_copy_step` or `dse_local_agrees_external_copy_deleted_step` | other-space branch | `dse_external_copy_result_cases` |
| RETURNDATACOPY | `dse_local_agrees_returndatacopy_step` | same theorem | `dse_returndatacopy_result_cases`, `dse_returndatacopy_non_ok`, `dse_returndatacopy_abort_match`; `dse_returndatacopy_not_effects_in_space` excludes selection |
| EXTCODECOPY | `dse_local_agrees_extcodecopy_step` | same theorem | `dse_extcodecopy_result_cases`, `dse_extcodecopy_not_effects_in_space` |
| OFFSET ASSIGN NOP PARAM FMP_PARAM RETPC_PARAM INITIAL_FMP BUMP | **missing RegisterSteps** | same | Need retained OK continuation and OK/Error classification; no implementation in proofs directory |
| ALLOCA | **missing AllocationSteps** | same | Need fresh-allocation extension plus pending witness transport, indexed OK continuation and result classification |
| GETFMP SETFMP DALLOCA | `dse_local_agrees_fmp_step`, indexed | same | `dse_fmp_result_cases`, `dse_fmp_retained`; DALLOCA is raw FMP operation, not ALLOCA map extension |
| JMP JNZ DJMP | `dse_jump_local_step`, raw | same | `dse_jump_result_cases`, `dse_jump_retained`. Gives both alloca-map equalities, but **no pending-at successor transport** |
| RET RETFMP DRET | BarrierSteps | BarrierSteps | `dse_barrier_inputs/result/retained`; exact inputs, so all result constructors match. RET-specific `dse_ret_intret_step/result_cases` also available; do not require other variants to fit RET-only interface |
| STOP SINK | `dse_stop_halt_step` | BarrierSteps | `dse_stop_result_cases`, `dse_terminal_retained` |
| RETURN REVERT | `dse_return_halt_step`, `dse_revert_abort_step` | RETURN barrier, REVERT same memory-terminal theorem | `dse_return_result_cases`, `dse_revert_result_cases`, `dse_memory_terminal_retained`; precise Memory read, not barrier |
| INVALID PHI | `dse_invalid_abort`, `dse_phi_error` | same | INVALID abort; PHI always errors in step_inst (prefix evaluation separate); selection excluded by no memory-definition effect |
| SELFDESTRUCT | `dse_selfdestruct_memory_step` | BarrierSteps | `dse_selfdestruct_results`, `dse_selfdestruct_retained` |
| ASSERT ASSERT_UNREACHABLE | `dse_local_agrees_assertion_step`, indexed OK; `dse_assertion_abort_step` | same | `dse_assertion_result_cases`, `dse_assertion_retained` |
| BALANCE SELFBALANCE EXTCODESIZE EXTCODEHASH | `dse_local_agrees_account_step`, indexed | same | `dse_account_result_cases`, `dse_account_retained`; account_empty observation already covered |
| MEMTOP ILOAD | BarrierSteps | `dse_key_memory_reader_step` raw + `dse_key_memory_reader_pending_step` | `dse_memory_reader_results`, `dse_memory_reader_retained` |
| SHA3 LOG | `dse_observer_step` | same | `dse_observer_result_cases`, `dse_observer_retained`; pending continuation separately in `dse_observer_pending_step` |
| ISTORE | **missing** exact overwrite + immutable bookkeeping | **missing** common Memory/immutable update, no K clobber | effects exclude selection; see precise proposed statements below |
| INVOKE | BarrierSteps | BarrierSteps | same-input result equality avoids recursive unfolding; `dse_barrier_ok` supplies empty pending continuation; retention sound-id guarded |
| CALL STATICCALL | `dse_call_memory_step`, raw | BarrierSteps | `dse_call_results` OK/Error; raw theorem gives both alloca equalities. Memory retention under sound ids still needs exposing (effects for CALL; successful outputs for STATICCALL if needed) |
| DELEGATECALL | `dse_delegatecall_memory_step`, raw | BarrierSteps | `dse_delegatecall_results` OK/Error; Memory retention must be exposed from effects/sound ids, not assumed |
| CREATE CREATE2 | `dse_create_memory_step`, raw | BarrierSteps | `dse_create_memory_retained`; raw theorem gives original alloca equality only. **Missing Memory Abort simulation and complete result classification**: OK-only theorem does not discharge oversized-initcode Abort. K retention needs sound ids (`dse_create_key_retention_counterexample` refutes arbitrary-ids retention) |

BarrierSteps applies exactly to `dse_barrier_case`, not every external opcode
in every space. In particular ISTORE reads empty, not undefined.
The table accounts for all constructors in OpcodeCoverage; it deliberately
reports missing interfaces instead of treating static coverage as a dispatcher.

## ISTORE: exact boundary to prove

`istore a v s = (mstore a v s with vs_immutables := s.vs_immutables |+ (a,v))`.
`mem_write_ops` supplies the same fixed-size-32 descriptor as MSTORE;
`bp_get_write_location` uses it in Memory. `write_effects ISTORE` contains
both Eff_MEMORY and Eff_IMMUTABLES. Thus effects_in_space is false for all
three supported spaces. Under the sound-id occurrence lemma ISTORE is retained.
It cannot use the external no-clobber theorem: it can completely cover an old
pending region. Generalize the MSTORE static-region/size/clobber boundary to
include ISTORE rather than copying its region proof. The operational write
bytes are `word_to_bytes v T` (length 32).

Proposed local update interface (no let):
```
inst.inst_opcode = ISTORE /\
dse_local_agrees AddrSp_Memory P s t /\
eval_operand addr s = SOME a /\ eval_operand value s = SOME v ==>
dse_local_agrees AddrSp_Memory
  (FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+32)) P)
  (istore (w2n a) v s) (istore (w2n a) v t)
```
The operand premises are not necessary for this update-only lemma; the most
general reusable form takes numeric `a` and bytes32 `v` directly and filters
by `a <= b /\ b+m <= a+32`. This separates common immutable-map congruence
from step extraction. There is no dedicated ready immutable-update local
boundary in Local/StoreSteps: add/generalize common field-update congruence
once, not two step copies. Local agreement includes equal immutable maps.

Proposed pending interface, with numeric `a` substituted by `w2n a` below:
```
dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
EL idx bb.bb_instructions = inst /\ inst.inst_opcode = ISTORE /\
inst.inst_operands = [addr; value] /\ eval_operand addr s = SOME a /\
bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s ==>
dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx)
  (FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+32)) P)
  (istore (w2n a) v s)
```
Use `dse_pending_at_overwrite_step` and `dse_pending_at_allocas_extend`:
ISTORE preserves allocas. The required static clobber fact is exactly
`MEM (loc,(b,m)) P /\ dse_inst_clobbers bp AddrSp_Memory loc inst ==>
w2n a <= b /\ b+m <= w2n a+32` under these same safety/access premises.
For K retain P, use unchanged selected-space storage/transient and common
Memory/immutable updates, empty K write location, SUC pending step.
The full ISTORE family should expose the same indexed existential P1,t1
conclusion as MSTORE, plus OK/Error cases and sound-id retention.

## Other-space pass boundary (not literal identity)

For `sp NOTIN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient}`,
`is_memory_def_opcode sp opc` is false. Therefore dse_inst and dse_single_pass
are identities even for arbitrary ids. OWHILE then either returns SOME fn
(if the initial analysis set is empty) or NONE (constant-state loop with true
guard). In either case the exact useful statement is
```
sp NOTIN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
dse_function_space analysis_fn sp fn = clear_nops_function fn
```
No soundness hypothesis is needed. Under all_dead_stores the first set is
necessarily empty, so a simpler proof may use this premise and avoid the
constant-loop theorem. Literal equality to fn is wrong in the presence of NOPs.
Use existing `clear_nops_function_dse_equiv` for run semantics, not all-opcode
simulation for these spaces. OWHILE fallback and cleanup must both be covered.

## Common dispatcher contract to schedule

Use one common antecedent A, spelled here as a specification abbreviation
only (no new HOL definition is proposed):
```
sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
wf_function fn /\
all_dead_stores ids (cfg_analyze fn) FEMPTY bp sp fn /\
lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
get_instruction bb s.vs_inst_idx = SOME inst /\
dse_local_agrees sp P s t /\
dse_pending_at (cfg_analyze fn) bp sp fn bb s.vs_inst_idx P s /\
alloca_inv s /\ bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s
```
Check whether allocation also needs bounds/freshness hypotheses already supplied
by alloca_inv and successful execution before freezing this interface.
Do not add arbitrary safe_inv on t; original safety is supplied by caller.

Continuing nonterminator statement:
```
A /\ ~is_terminator inst.inst_opcode /\
step_inst fuel ctx inst s = OK s1 ==>
?P1 t1. step_inst fuel ctx (dse_inst ids sp inst) t = OK t1 /\
 dse_local_agrees sp P1 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
                         (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
 dse_pending_at (cfg_analyze fn) bp sp fn bb (SUC s.vs_inst_idx) P1 s1
```
Existing indexed families already match; raw families need only common cursor
updates (`dse_local_agrees_inst_idx`). Pending-at depends on allocas rather than
cursor, so standardize this once at consumer boundary, not per-opcode duplicates.

Jump statement:
```
A /\ inst.inst_opcode IN {JMP; JNZ; DJMP} /\
step_inst fuel ctx inst s = OK s1 /\
lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb1 ==>
?t1. step_inst fuel ctx (dse_inst ids sp inst) t = OK t1 /\
 dse_local_agrees sp P s1 t1 /\
 dse_pending_at (cfg_analyze fn) bp sp fn bb1 0 P s1
```
Requires actual successor proof plus wf final-terminator position and empty
clobber to advance suffix deadness through jump; `dse_jump_local_step` alone is
insufficient. Reuse Liveness successor/label/suffix facts, add a pending-level
boundary rather than rebuilding EVERY manually in the dispatcher. If the target
block is absent, original run errors later; keep the lookup conditional.

Terminal statement (each constructor separately):
```
A /\ step_inst fuel ctx inst s = Halt s1 ==>
?t1. step_inst fuel ctx (dse_inst ids sp inst) t = Halt t1 /\ dse_equiv sp s1 t1
```
Similarly Abort; for IntRet preserve its returned value list as well as state
relation, using the actual constructor argument order in venomState. Do not
use this coarse boundary on OK. This covers CREATE Abort and assertion Abort,
not only syntactic terminators. Original Error requires no target simulation.
A result dispatcher can combine these only after complete constructor coverage.

External sibling prerequisites: RegisterSteps (OFFSET/ASSIGN/NOP/parameter and
FMP constants/BUMP) and AllocationSteps (ALLOCA) must provide indexed continuing
contract above, result-class exclusion and retention. Allocation must establish
`!aid pair. FLOOKUP s.vs_allocas aid = SOME pair ==>
FLOOKUP s1.vs_allocas aid = SOME pair` (or the existing extension relation)
for original pending witnesses, not equality of the whole allocation map.
These files do not yet exist; no certification or sibling edit was performed.

## Coherent remaining-work request

Schedule durable boundaries together: ISTORE + shared static-region/update
abstraction, other-space cleanup identity, CREATE Memory non-OK completion,
jump pending-successor transport, existing register/allocation siblings, then
one interface-normalizing all-opcode dispatcher. Include sound-id retention
for external Memory calls in that integration boundary. Do not start frozen
proofs or assume all-opcode completion from family builds. The source reveals
missing CREATE Abort and jump pending transport beyond the old ISTORE-only
residual inventory; these are required work, not evidence of task falsehood.
