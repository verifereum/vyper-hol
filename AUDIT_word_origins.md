# C1.20: scalar-result provenance origin audit

This is a source/interface diagnostic, NOT a proof of scalar closure or a
counterexample to the frozen target. All paths below mean a constructively
selected successful execution of the emitted fragment, not arbitrary paths in
a containing function. `clean` means `op_prov G op = NONE` at the actual result
endpoint. Numeric addresses, untainted values, fresh variable names, and
`safe_operand` do not by themselves mean clean.

## Checked transfer interface (no new duplicate theory)

Duplicate search found precisely the required general boundary already in
`lowering/bodyPtrWordBuiltinsScalarScript.sml`:

* `first_prov_none`, lines 7--14: absent FLOOKUP for every variable operand
  implies absent first_prov.
* `scalar_out_prov_none`, lines 16--27: non-allocation/non-PARAM instructions
  have absent output provenance when ADD/SUB/ASSIGN inputs are in a clean set.
* `step_prov_scalar_set`, lines 29--43: all old clean-set variables AND all
  outputs remain absent; this handles even multiple outputs.
* `ghost_step_scalar_set`, lines 45--60: lifts the previous fact to an OK
  non-INVOKE ghost step.

For the requested ADD/SUB/ASSIGN specialization take
`scalars = {x | MEM (Var x) inst.inst_operands}`. There is no missing arithmetic
transfer lemma. Adding a new leaf restating it would violate uniqueness.
Isolated `holbuild(['bodyPtrWordBuiltinsScalarTheory'])` passed, as did retained
`bodyPtrWordBuiltinsAbsCalibrationTheory` (tool outputs m1711, m1686).

`ptrDisciplineScript.sml:154--198` is the exact implementation: op_prov only
looks up Var; first_prov takes the first tracked operand; out_prov propagates
only ADD/SUB/ASSIGN, creates provenance for ALLOCA/DALLOCA/PARAM, and otherwise
returns NONE. set_prov deletes all outputs unless there is exactly one output
and SOME provenance. These are origin facts, not safety proofs of the inputs.

## Exhaustive outer expression partition

References in this section abbreviate `lowering/defs/exprLoweringScript.sml`
as EL. The complete outer match is EL:2935--3029. Result annotations, not the
threaded `ty`, control unwrap at EL:965--978 and lower_value at EL:2002--2006.

| Outer constructor | Terminal origin / dependency |
|---|---|
| Literal | EL:1453--1481: Bool/Int/Decimal/fixed Bytes/address fallback are Lit (clean); dynamic Bytes and String allocate LocatedValue. A word LocatedValue is subsequently loaded, not forwarded. Typing matches StringL to StringT; invalid annotations cannot be silently used to infer a word result. |
| Name | EL:1490--1501: PtrVar/MemLoc become LocatedValue; missing entry INVALID then Lit 0. Word unwrap is a load, including PtrVar parameters. A PARAM pointer is never directly a scalar Name result. |
| IfExp | EL:2942--2969,2425--2434: word result is ASSIGN of selected arm's unwrap into result_var; needs selected recursive arm cleanliness and preservation to ASSIGN. Nonword result can forward/materialize a pointer, and must NOT be called clean. No PHI instruction is emitted by this branch. |
| Builtin AddMod/MulMod/PowMod256 all-Name fast paths | EL:2893--2921: each Name is unwrapped first, then ADDMOD/MULMOD/Exp clears its result; no additional address-origin case. |
| Builtin general | Complete dispatch table below. |
| TypeBuiltin | Complete dispatch table below. |
| Subscript | EL:2278--2325: every branch returns LocatedValue ret_ty. Map hash, tuple/struct offset, array bounds/index arithmetic may produce a tracked place; scalar unwrap loads it. Need recursive base/index simulations and safe address arithmetic, NOT a clean base pointer. |
| Attribute | EL:2331--2351: ADD of field offset returns LocatedValue. Same load boundary as Subscript. |
| StructLit | EL:2984--2995,2354ff: allocation-backed LocatedValue; even malformed scalar annotation would unwrap by load. Well-typed StructLit has StructT, not a scalar. |
| FlagMember | EL:2996--2999: Lit. |
| TopLevelName | EL:3000--3009: LocatedValue storage/transient/code literal address, then scalar load; missing module entry INVALID/Lit. |
| Call | Complete call table below. |
| Pop | EL:3012--3029,1152ff: returns element LocatedValue; scalar unwrap loads, independent of whether place arithmetic carries provenance. Needs target/place and mutation simulation. |

Every scalar LocatedValue above uses `compile_ptr_load`: contextScript.sml:
134--140 gives MLOAD/SLOAD/TLOAD/CALLDATALOAD or immutable-load helper. In the
runtime-only frame (~ce_is_ctor), immutable load is DLOAD
(contextScript.sml:116--124), not a PARAM or returned buffer pointer. Memory accesses still require
coverage and taint facts; cleanliness of the final load does not prove them.

## Complete builtin dispatch partition (EL:3032--3307)

| Branches | Terminal origins / dependencies |
|---|---|
| Bop Add/Sub/UnsafeAdd/UnsafeSub | EL:294--338,596--677: ADD/SUB propagate; clamp_and_return forwards; wrap_truncate either forwards or SIGNEXTEND/AND clears. Need both recursively lowered scalar operands clean, retained until the writer. |
| Bop Mul/Div/Mod/Exp and unsafe Mul/Div | MUL/Div/SDIV/SMOD/Mod/Exp final result clears; later checks/clamps return that same fresh result. EL:349--446,487--550. |
| Bop And/Or/XOr/ShL/ShR/comparisons/Min/Max | EL:561--677: ordinary result opcodes clear. compile_select ends XOR (builtinSimple:23--28). Eq may nevertheless be UNSAFE before clearing its own output if inputs track incompatible sites. |
| Bop In/NotIn | Flag branch AND/ISZERO clears; list-literal branch equality chain and variable-array loop (EL:705--830) produce booleans. ASSIGN accumulators require literal/ordinary boolean origins and loop preservation. Pointers used to load elements are not scalar results. |
| Not | ISZERO or compile_invert NOT/XOR (EL:2852--2858) clears. Bytestring-typed Not result can still be represented as a stack operand by this compiler; typing/semantics must be respected rather than assuming every StackValue is scalar. |
| Neg | EL:1886ff: SUB propagates recursively lowered input; clamping forwards. |
| Abs | builtinSimple:114ff: SUB propagates input; EQ safety needs clean input (or suitable same-site facts); final compile_select XOR clears. |
| Env | EL:1508--1527: final CALLER/ADDRESS/CALLVALUE/etc or BLOCKHASH clears; PrevHash SUB starts from cleared NUMBER. SelfAddr is an EVM address value, not allocation provenance. |
| Acc | EL:2866--2885: Balance/Codesize/Codehash/IsContract clear via BALANCE/EXTCODESIZE/EXTCODEHASH/GT; Address forwards recursive scalar address; Code emits INVALID then Lit 0. |
| Keccak256 | builtinHashing:24--48: SHA3 clears, scratch allocations never returned as hash. |
| Sha256 | builtinHashing:93--135: output MLOAD clears, input/output scratch pointers not returned. |
| CalldataLen | CALLDATASIZE clears. |
| Len | builtinSimple:37ff: compile_ptr_load, hence clears; source is a value/place dependency, not a clean scalar dependency. |
| BlockHash/BlobHash | builtinMisc:163--179: BLOCKHASH/BLOBHASH clear. |
| AddMod/MulMod/PowMod256 | builtinMath:64--82: ADDMOD/MULMOD/Exp clear. Modulus ASSERT needs the corresponding taint/simulation facts. |
| Ceil/Floor | builtinMisc:188--208: final SDIV clears; adjusted ADD/SUB requires clean scalar input for intermediate propagation. |
| AsWeiValue | builtinMisc:222--260: scale=1 integer branch forwards v; other integer branch MUL clears; decimal branch Div/MUL then Div clears. Forwarded v requires recursive cleanliness. |
| ECRecover | builtinMisc:32--52: final MLOAD clears. |
| ECAdd/ECMul | builtinMisc:105--156: return allocated output buffer as LocatedValue (as_ptr_val), not scalar stack value. If word unwrap were requested, it loads. Typed result is aggregate. |
| CalldataSlice/Concat/Slice/Uint2Str | EL:3128--3134,3199--3261: memory pointer result (allocation or allocation-derived ADD), wrapped LocatedValue; legitimate nonword values must retain provenance. Slice msg.data/self.code/extcode paths are explicitly distinct, including the extcode address recursive operand. |
| MethodId | EL:3271--3285: literal BytesL fixed4 => Lit; runtime fixed4 => SHR then SHL (clears); bytestring result is allocation-backed LocatedValue. builtinHashing:65--85. |
| MakeArray | EL:3286--3304: allocation-backed LocatedValue, tuple/array writes; typed result nonword. |

This table exhausts the builtin datatype cases present in the dispatcher;
unsupported Bop fallbacks emit INVALID then Lit 0, never a raw address.
`well_typed_builtin_app_def` constrains arities; the frozen theorem only
provides the recursive premise when builtin_args_length_ok holds. Ill-arity
paths must be discharged via typing/aborts, not by applying that premise
unconditionally. Existing `exprWordOperand` classifications
`nonword_builtin_cases` and `nonword_type_builtin_cases` (lines 34--82) are
useful named typing partitions, not dynamic provenance theorems.

## Complete type-builtin partition (EL:3309--3405)

* Convert: zero-capacity bytestring-to-word => Lit 0. Bytestring widening =>
  allocated pointer (nonword destination). Otherwise mk_convert_op followed
  by compile_type_convert. Exact exhaustive convert-op origins below.
* Empty: word => Lit 0; nonword => allocated LocatedValue.
* MaxValue/MinValue/Epsilon: Lit.
* Extract32: final MLOAD through compile_extract32_load then
  compile_clamp_basetype forwards raw, so clean writer origin; checks need
  coverage for source, not source pointer cleanliness.
* AbiEncode: allocation-backed LocatedValue through lower_abi_encode.
* AbiDecode: allocation-backed LocatedValue through lower_abi_decode; scalar
  unwrap loads it. An intermediate buffer is not a scalar result.

Complete compile_type_convert partition (EL:1659--1869):

| Operation | Origin |
|---|---|
| ConvToBool | ISZERO clears |
| ConvIntToInt | returns v after optional checks/clamp; needs recursively clean scalar |
| ConvBytesToInt | SAR/SHR clears then optional clamp forwards |
| ConvIntToBytesM | SHL clears (pre-check EQ safety may need clean input) |
| ConvIntToDecimal | MUL clears |
| ConvDecimalToInt | SDIV clears |
| ConvBoolToDecimal | MUL clears |
| ConvToAddress | returns v after bound assertion; needs recursively clean scalar |
| ConvBytesToAddress | SHR clears then optional checks |
| ConvToFlag | returns v after optional clamp; needs recursively clean scalar |
| ConvBytesMToDecimal | SAR clears then optional checks |
| ConvBytesMToBytesM | returns v even for downcast; needs recursively clean scalar |
| ConvBytestringToBool/Int/Decimal/BytesM | load_bytestring_as_word (EL:1615--1631) loads then SHR/SAR; final ISZERO/shift clears; not pointer forwarding |
| ConvBytestringCast | returns original bytestring pointer after optional length assertion; NONWORD destination |
| ConvIdentity | forwards v; typing exclusion is critical |

mk_convert_op (EL:1907--1991) contains ConvIdentity fallbacks even from
aggregate source to word target at the raw compiler level. Do NOT claim raw
compiler closure without typing. `valid_conversion_def` plus
`well_typed_type_builtin_args_def` and well-formed source type exclude these
fallbacks for typed scalar targets. Existing `typed_convert_child` establishes
ann=target and a typed single child, but does not alone establish source is
word. `word_type_builtin_convert` (exprWordOperand:176ff) already performs the
necessary word-vs-bytestring classification using `well_typed_expr_type_well_formed`;
it proves safe_operand only, so its dynamic strengthening remains work.

## Complete call-target partition (EL:2626--2800)

* IntCall: returns_count>0 allocates a return buffer before INVOKE, stores
  INVOKE results, returns LocatedValue at declared ce_func_return_type.
  The returns_count>0/NONE buffer arm is unreachable by allocation branch
  equations; even that arm's direct INVOKE outputs are cleared by the
  actual successful INVOKE ghost rule, not by step_prov. With returns_count=0,
  return_buf_size>0 => LocatedValue; otherwise Lit 0. Word return loads from
  buffer. Need declared return-type agreement (lowered_value_type at EL:172--174),
  call-frame simulation, and retention of the return buffer across the call.
* ExtCall: absent address => INVALID/Lit 0. Shared call/return buffer always
  allocated, but return_abi_size=0 returns Lit 0 (EL:1064--1065). Nonzero size
  => result allocation, decode or default store, returned as LocatedValue,
  scalar unwrap loads. Default path returns result_op, NOT default_op
  (EL:918--950,1005--1088).
* Send: CALL success checked, Lit 0 result. Bad arity INVALID/Lit 0.
* RawCallTarget and RawCallCalldataTarget: builtinSystem:55--127: max_outsize=0
  returns CALL/STATICCALL/DELEGATECALL success or Lit 0, hence clean; positive
  size returns buffer/tuple allocation as LocatedValue. Calldata path's
  SETFMP has no scalar output. Bad arity INVALID/Lit 0.
* RawLog/RawRevert/SelfDestructTarget: INVALID/Lit 0 in expression compiler.
* CreateTarget: compile_create_call (EL:2584ff) dispatches creation helpers;
  builtinCreate's compile_create_dispatch/compile_create_copy/
  compile_create_blueprint_append end CREATE/CREATE2; check_create_result
  returns that same value, not the code allocation. Invalid argument branches
  return Lit 0. Constructor-argument buffer allocations are not result origins.

INVOKE: ptrSafeRunScript.sml:58--81 clears caller output provenance with
DRESTRICT after decode/lookup/eval/setup success. Callee begins with FEMPTY
and argument PG=MAP(op_prov G) ops; returned provenance is NOT copied into
caller result variables. Invalid setup branches leave G unchanged but cannot
be treated as a successful return. Memory/taint and pointer safety still
need the call theorem.

PHI: ptrDisciplineScript.sml:200--225 resolves the predecessor-selected
operand and reads its provenance in the PRE-BLOCK G0 (parallel semantics).
A generic step_prov(PHI) clearing lemma would be wrong for block entry.
Compiler IfExp uses ASSIGN+JMP, not PHI. Any entry PHIs in the containing
function need the actual emitted-entry/endpoint argument; no arbitrary
whole-function writer invariant is justified by this audit.

ALLOCA/DALLOCA/PARAM: these are real non-clean origins. Along typed scalar
result routes above they are buffer/place operands then consumed by a load,
not forwarded scalar endpoints. PARAM occurs at function entry, outside
compile_expr's scalar result generation. DALLOCA-created scratch buffers in
creation/call code remain pointers, while CREATE/CALL success result clears.
This is a syntactic origin classification, NOT a proof that every path
preserves older scalar variables or that every memory access is safe.

## Exact candidate strengthened operand interface (not added as a theorem)

The following candidate deliberately uses existing predicates and adds no new
definition. It asks for the same existential outcome as expr_sim_ptr with a
clean scalar fact in its normal post. No claim that it is proved:

```sml
!cx e d PG tops ctx func cenv env ty es sa sb op s0 G0 tn0.
  body_expr_ptr_ok cx e /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_word_type (expr_type e) /\
  lower_value compile_expr cenv ty e sa = (op, sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
    (bind (eval_expr cx e) (read_result cx)) (es, s0, G0, tn0)
    (\res ee G tn t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\
      ptr_val_ok cx (expr_type e) v op G tn t /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\ op_prov G op = NONE)
    (\res ee gt r. expr_exit res r)
```

### Premise/dependency map and verdict

* Frozen body_exprs_ptr_ok supplies body_expr_ptr_ok for member arguments
  conditional on arity. `body_expr_ptr_ok_def` supplies expr_sim_ptr and
  expr_vv_sim_ptr under body_inv/expr_body_pre.
* Outer frame supplies the fn/code/freshness/gas/state/ghost/PC premises;
  operand precondition lemmas transfer body pre and typing. Typed scalar
  argument facts must be derived per selected builtin, not assumed for all Not.
* expr_body_pre includes typing, supported internal calls and no EVM-run;
  unlike expr_sim_pre it does NOT ban internal calls (exprSimHypsDefs:136--160).
* Existing expr_sim_ptr normal post has untainted scalar value but no clean
  provenance (bodyPtrDefs:216--243, ptr_val_ok:136--139). Consequence cannot
  strengthen that post to cleanliness. Existing safe_operand/word_result_ok
  facts constrain syntax and fresh ranges, not dynamic G.
* Missing proof obligations: recursive scalar origin/preservation theorem;
  typing/annotation alignment for forwarders and calls; selected-arm/loop
  transfer; clean operands retained across evaluation of later arguments;
  call-frame ghost transport; and alignment of an origin path with the SAME
  gas_outcome_ptr witness supplied/constructed by the simulation. Separate
  existence of a clean syntactic trace is not enough.
* Thus NO-GO for a proof using only consequence on the frozen operand judgment.
  A separate constructive compiler-origin/path-strengthening argument is still
  required (possibly ghost-trace determinism aligning the chosen simulation
  path). This need not change any frozen judgment. No typed terminal scalar
  allocation/PARAM leak was identified. There is NO verified counterexample
  and this audit does not license claiming the target false.

Stop here for strategist review; no compiler induction or new runtime frame
was attempted. The scalar transfer deliverable is satisfied by existing,
isolated-build-checked helpers rather than adding duplicates.
