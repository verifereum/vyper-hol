# Expression allocation-trace dependency audit

Diagnostic only; no Entry or installed-image theorem is claimed. Source inspected:
exprLoweringScript.sml open bodies 2935-3406, raw equations 3408-3431;
exprLoweringPropsScript.sml 4542-4563 documents the existing three-way induction use.

## Proposed joint boundary

```
(!ce ty e s. allocation_trace s (SND (compile_expr ce ty e s))) /\
(!ce rt ty bi es s. allocation_trace s
  (SND (compile_builtin_dispatch ce rt ty bi es s))) /\
(!ce vt ty tb rt es s. allocation_trace s
  (SND (compile_type_builtin_dispatch ce vt ty tb rt es s)))
```

This is NOT proved. All state and environment parameters must be generalized.
compile_expr_raw_def supplies three guarded callbacks to expression body, but only
expr_child_callback to the builtin and type-builtin bodies. Guards use expr_size e
and list_size expr_size es respectively. The type-dispatch equation has a dead
`if F` mutual call, eliminated by simp.

Existing expr_child_callback_allocation_trace consumes
`!ce ty e s. expr_size e < bound ==> allocation_trace s (SND (cfn ce ty e s))`.
The builtin/type guard lemmas consume the analogous list_size bound, with all
requested types, builtin tag, environment and state quantified. Their conclusions
are TOTAL guarded callback contracts, including malformed/out-of-bound requests
via invalid_expr_call. Thus empty HD/EL args and extcode address extraction do not
require a new syntactic-size lemma in each producer. Do not substitute the raw
compiler for the total guarded callback before discharging its bound.

compile_expr_ind is exported from compile_expr_raw_ind (generated, not printed
by theorem search). The existing compile_expr_ci_mono proof uses
`ho_match_mp_tac compile_expr_ind`, three conjunctions, parameters and one IH
antecedent, then Once compile_expr_raw_def and the three body boundaries plus
three guard boundaries. This verifies the intended proof architecture in source,
not an allocation-trace induction proof. Exact generated IH goals remain to be
checked by a build when that proof is authorized.

## Existing boundary contract legend

Every unconditional theorem named `f_allocation_trace` below states
`!args s. allocation_trace s (SND (f args s))`.
Every callback producer needs a state-universal trace for the actual callback.
Existing ChildAllocationTrace strengthens global contracts as follows:
- lower_value_child: callback only at ce,ty,e, every state.
- tuple, multi_exprs, make_array/elements: callback at expr_type e for each MEM e es.
- struct_lit_child: callback at expr_type e for each MEM (name,e) fields.
- attribute_child: callback at ce,ty,base, every state.
- ifexp_child: three state-universal occurrences, bool condition and ty arms.
SubscriptAllocationTrace's compile_subscript boundary quantifies ce,t,e and s,
with `e=base \/ e=idx`; all requested types are allowed.
StoreAllocationTrace and UnwrapAllocationTrace are unconditional.
OperatorAllocationTrace's array-membership loop requires
`!op s. allocation_trace s (SND (loader op s))`; concrete variable-array wrapper
has no premises. Array-subscript loader contract needs only loader base.

## Complete open-body inventory (stop at proved boundaries)

### Pure expressions and places (exprLowering)

| Consumer | Existing boundary / missing contract |
|---|---|
| Literal | MISSING compile_literal_vv; dependencies compile_bytelike_literal and compile_store_byte_chunks (DROP32 recursion, not ordinary tail recursion) |
| Name | MISSING compile_name_vv; lookup returns or INVALID then return |
| IfExp | compile_expr_body_ifexp_child_allocation_trace; compile_ifexp_arm and materialize already unconditional |
| AddMod/MulMod/PowMod256 name fast paths | MISSING compile_addmod_names, compile_mulmod_names, compile_powmod256_names; depend on missing name and modular builtin traces, existing unwrap |
| ordinary Builtin / TypeBuiltin | callback trace supplied by corresponding guarded IH, no additional producer |
| Subscript | compile_subscript_allocation_trace with contract above |
| Attribute | compile_attribute_child_allocation_trace |
| StructLit | allocation plus compile_struct_lit_child_allocation_trace |
| FlagMember | state unchanged |
| TopLevelName | lookup returns unchanged state or INVALID |
| Call | MISSING compile_call (see call staging below) |
| Pop | MISSING compile_get_target_ptr and compile_dynarray_pop; target-pointer recursion on base_target, index lower_value, mapping/hash/array traces already available; pop composes ptr-load/store and emitters |

### Ordinary builtin dispatcher (exprLowering)

All callback occurrences are lower_value_child or direct callback, except
compile_multi_exprs and aggregate producers which use member contracts.

| Tags | Existing boundary / missing contract |
|---|---|
| Bop | compile_binop, list-membership in/notin, var-array-membership, bytestring_hash all unconditional; multi_exprs_child available for list literal; remaining emissions primitive |
| Not | MISSING compile_invert (type cases; XOR/NOT); bool case emitter |
| Neg | MISSING compile_neg (emitter/clamp chain) |
| Abs | MISSING compile_builtin_abs (builtinSimple) |
| Env | MISSING compile_env_var (exprLowering; finite opcode cases) |
| Acc | MISSING compile_acc (exprLowering; lower_value or INVALID); requires total callback contract |
| Keccak256 | MISSING compile_keccak256_bytes/bytesm/word (builtinHashing) |
| Sha256 | MISSING compile_sha256_bytes/bytesm/word (builtinHashing) |
| CalldataLen | MISSING compile_builtin_calldatasize (builtinSimple) |
| CalldataSlice | MISSING compile_slice_calldata (builtinBytes) |
| Len | MISSING compile_builtin_len (builtinSimple), depends existing ptr-load |
| BlockHash/BlobHash | MISSING compile_blockhash/compile_blobhash (builtinMisc) |
| AddMod/MulMod/PowMod256 | MISSING compile_addmod/mulmod/pow_mod256 (builtinMath) |
| Ceil/Floor | MISSING compile_ceil/floor (builtinMisc) |
| ECRecover/ECAdd/ECMul | MISSING compile_ecrecover/ecadd_points/ecmul_point (builtinMisc); existing unwrap covers located point operands |
| Concat | MISSING compile_concat (exprLowering; list recursion, lower_value, MCOPY/MSTORE; mismatch fallback return); allocation and header emitters already covered |
| Slice | MISSING compile_slice_calldata/code/out_buf/extcode/data, compile_bytestring_src and compile_assert_slice_bounds (builtinBytes); scratch allocation/store already covered |
| Uint2Str | MISSING compile_uint2str (builtinStrings; finite emitted CFG with reused ASSIGN variables, not recursive compilation) |
| AsWeiValue | MISSING compile_as_wei_value_decimal/int (builtinMisc) |
| MethodId | missing literal boundary or compile_method_id_runtime -> compile_method_id_hash / keccak helpers (builtinHashing) |
| MakeArray | compile_make_tuple_child / compile_make_array_child after allocation; no new aggregate trace needed |

### Type builtin dispatcher

| Tags | Existing boundary / missing contract |
|---|---|
| Convert | MISSING compile_bytestring_widen_copy, compile_type_convert -> load_bytestring_as_word, compile_int_clamp (exprLowering); conversion metadata pure |
| Empty | MISSING compile_builtin_empty_complex -> compile_zero_words (builtinSimple); word branch unchanged |
| MaxValue/MinValue/Epsilon | state unchanged; bounds pure |
| Extract32 | MISSING compile_bytestring_src, compile_extract32_load (builtinBytes); compile_clamp_basetype already proved |
| AbiEncode | MISSING compile_store_abi_tuple (exprLowering), lower_abi_encode (builtinAbi), compile_abi_encode_to_buf family (abiEncoder); tuple staging uses existing multi_exprs/alloc/store/unwrap |
| AbiDecode | MISSING lower_abi_decode (builtinAbi), compile_abi_decode_to_buf family (abiEncoder); existing unwrap |

ABI dependency closure: encode uses the mutual compile_abi_encode_child,
compile_abi_encode_to_buf, compile_abi_encode_complex_elems,
compile_abi_encode_dyn_loop (single Definition block at abiEncoder:230), and
nonrecursive compile_abi_encode_static, compile_abi_encode_static_info,
compile_abi_encode_dyn_static_loop. Decode has its own mutual block at :440
(to_buf, complex_elems, dyn_loop), plus getelemptr_abi,
compile_abi_decode_dyn_elem_ptr, compile_get_element_ptr/dynarray_elem_ptr,
compile_abi_decode_static and ABI clamp family (int, bytes, basetype).
compile_abi_decode_static's arbitrary clamp_fn must have a trace premise; its
actual use with compile_abi_clamp_basetype then discharges that premise.
Offset/size/needs_clamp metadata is pure and needs no trace. Existing memory
copy boundaries can terminate traversal whenever the actual definition uses them.

### Effects and call staging (all compile_call alternatives)

| Consumer | Missing boundary and dependencies |
|---|---|
| IntCall | compile_multi_vvs (callback list recursion), compile_stage_intcall_args (unwrap/materialize/copy), store_multi_results; emit_multi_op primitive trace also missing (must check output-origin restriction, opcode INVOKE) |
| ExtCall | compile_ext_call_kwargs/kwarg (parallel list recursion, lower_value/materialize), compile_external_call_kwargs, compile_extcall_store_values (list unwrap/store), compile_default_return_path, ABI encode/decode families; extcodesize and return_value_decode already done |
| Send | only child lower_value, finite list/length cases, CALL/ASSERT; no additional runtime helper |
| RawCallTarget | kwargs above; compile_raw_call_outbuf/finish (builtinSystem) |
| RawCallCalldataTarget | same plus compile_msg_data_to_memory (builtinSystem); SETFMP is ordinary non-ALLOCA emitter |
| RawLog/RawRevert/SelfDestructTarget | always INVALID, no need to prove unused builtinSystem semantic producer traces |
| CreateTarget | compile_create_call, compile_raw_create, compile_create_snapshot, compile_create_ctor_tuple, compile_create_blueprint_args, compile_create_salt (exprLowering); ABI encoder, compile_slot_to_memory, store/copy/unwrap, multi_vvs; builtinCreate dispatch/check_result/proxy_buf/copy/blueprint_check/blueprint_append |

Creation uses FIRST/FRONT/LAST/list splitting purely; arbitrary callback contract
avoids AST membership plumbing. Snapshot uses storage/transient slot-copy (missing
compile_slot_to_memory trace), existing immutable copy and dynamic memory copy.
compile_extcall_store_args and compile_store_words should only be added if reached
from an actual dependency above; they are not automatically required because their
names appear nearby. Legacy compile_raw_create_legacy, compile_create_proxy and
compile_create_blueprint are not the called entry points in compile_create_call.
Unused dynarray_append is not required by these three bodies.

## Coarse remaining batches for strategist scheduling

1. Scalar/literal/simple builtins: literal/name/chunks; modular-name fast paths;
   env/accessor/neg/invert; builtinMath/Simple/Misc/Hashing; Pop/target-pointer.
   List/drop recursion and target recursion are separate induction skeletons.
2. Bytestring/conversion: builtinBytes, uint2str emitted CFG, concat callback list
   recursion, full convert_op cases and empty/zero-word recursion.
3. ABI: general encoder and decoder mutual trace families, explicit clamp callback
   premise where necessary, then lower_abi wrappers and tuple staging.
4. Calls/create: output emitter boundary, staging/kwargs list inductions, raw call,
   creation primitives and slot-copy, then all compile_call branches.
5. Three open-body trace contracts under TOTAL abstract callbacks, followed by
   joint compile_expr_ind and existing guarded callback lifts. Must build each
   producer batch before inserting into joint recursion.

These are dependency inventory proposals, NOT new authorized PLAN components.

## Entry remains a separate problem

allocation_trace gives allocation origin intervals and protected-tail persistence
for generated variables older than the entry counter. It permits the exact
Concat header ALLOCA;ADD32;ALLOCA64;MSTORE0, so cannot imply Entry. A supported
producer proof must additionally establish internal bad-window absence and P2/P3
frontier exclusion, with offset-sensitive saved-buffer history (tuple_history),
then preserve each finalized block separately. Support restrictions matter at
Concat dispatch. Calls/ABI/imported wrappers still require full Entry contracts;
function and runtime/deploy installation are not covered by this audit.

Additional primitive reached by creation: compile_alloc_dynamic (context:252)
is exactly emit_op DALLOCA [size_op], so it needs at most a one-line boundary
using allocation_trace_emit_op_snd, not an ALLOCA fresh-output extension.
