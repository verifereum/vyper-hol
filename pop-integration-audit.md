# Compiler integration diagnostic (2026-11-06)

This is a proposal/report, NOT a logical certificate. No theorem below has been admitted or proved. `bodyPtrPopProducerAuditScript.sml` is absent from OWNED_FILES.txt, so it has not been edited. Baseline `holbuild(bodyPtrPopCalldataSliceBoundaryTheory)` passes (TO_pop-20261106T070927Z_m3355_t001).

## 1. Consumer and invariant

`bodySimScript.sml:63-67` supplies supported_program tops and raw lower_vyper_runtime_unit/deploy_unit success. It does not supply supported_expr for an arbitrary fragment that satisfies fn_has_code. The desired bridge remains a theorem about every block of those raw units, not a source-occurrence inversion.

Existing interface: `pop_comp_boundary s` is pop_boundary_clean on cs_current_insts and EVERY complete-window exclusion on cs_blocks (bodyPtrPopCompilerBoundary:7-11). Its bind theorem at 28-32 requires arbitrary intermediate results/states. In particular, an environment-sensitive IH cannot be passed to it until that IH's extra premise is discharged for EVERY callback invocation.

### Candidate preservation family (UNVERIFIED)

First try universal compile environments, rather than inventing a semantic environment invariant:

```sml
!tops cenv ty e sa r sb.
  supported_expr tops e /\ pop_comp_boundary sa /\
  compile_expr cenv ty e sa = (r,sb) ==> pop_comp_boundary sb

!tops bindings cfn cenv bt sa r sb.
  IS_SOME (supported_target_info tops bindings bt) /\
  (!cenv' ty e s v t. supported_expr tops e /\ pop_comp_boundary s /\
      cfn cenv' ty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\ compile_get_target_ptr cfn cenv bt sa = (r,sb)
  ==> pop_comp_boundary sb

!tops bindings cenv lctx ty s sa r sb.
  supported_stmt tops bindings s /\ pop_comp_boundary sa /\
  compile_stmt cenv lctx ty s sa = (r,sb) ==> pop_comp_boundary sb

!tops bindings cenv lctx ty ss sa r sb.
  supported_stmts tops bindings ss /\ pop_comp_boundary sa /\
  compile_stmts cenv lctx ty ss sa = (r,sb) ==> pop_comp_boundary sb
```

All variables are universally quantified, especially cenv and ty. NO equality between source type and compiler ty, typing judgment, acyclic metadata premise, or global module-location invariant is claimed necessary for these *syntactic* preservation proposals. This is an unverified design choice, not a proved fact. If a helper needs semantic typing to avoid a bad opcode path, the all-environments statement must be rejected/refined at that point, not silently assumed.

Important Pop check: supported_effect_expr admits Pop only on TopLevelNameTarget (supportedExprs:84-85); pure Pop is false. compile_get_target_ptr TopLevelNameTarget (exprLowering:2038-2048) returns Lit in EVERY environment lookup branch, including missing/immutable cases. Thus literal operand shape alone does NOT require module-environment agreement. Location can still be LocCode or default LocMemory, and those compile_dynarray_pop branches require their own contracts! The accepted literal *storage* contract alone is insufficient. This is a concrete gap in applying that contract to the proposed all-environments theorem.

Dispatcher auxiliary proposals, also UNVERIFIED:

```sml
!tops cenv ret_ty ty bi args sa r sb.
  supported_builtin_form tops ret_ty bi args /\
  EVERY (supported_pure_expr tops) args /\ pop_comp_boundary sa /\
  compile_builtin_dispatch cenv ret_ty ty bi args sa = (r,sb)
  ==> pop_comp_boundary sb
```

Exact analogous type-dispatch proposal (supportedExprForms:126-127 supplies this argument order):
```sml
!tops cenv vv_ty ty tb ret_ty args sa r sb.
 supported_type_builtin_form tops vv_ty tb ret_ty args /\
 EVERY (supported_pure_expr tops) args /\ pop_comp_boundary sa /\
 compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args sa = (r,sb)
 ==> pop_comp_boundary sb
```
These auxiliary forms must be strengthened if supported pure-place recursion is not implied by supported_expr. No result-type-only exclusion is legitimate.

## 2. Actual recursion and premise map

exprLowering:3408-3431 defines THREE mutually recursive functions; exported `compile_expr_ind` is an alias of `compile_expr_raw_ind` (3444). Measure: 2*expr_size e+2 for expressions, 2*list_size expr_size args+1 for either dispatcher. Open bodies at 2935/3032/type dispatcher receive structurally guarded callbacks. exprCallBounds:14-46 gives exact guards: expr_size child < bound, list_size expr_size args < bound. Invalid calls compile INVALID; this branch needs a non-ASSERT preservation fact, not an IH. Raw induction ranges over arbitrary cenv, ty and state through these callback congruences. Source closure must still be proved for actual callback arguments; size alone gives no support fact.

Constructor / helper | recursive inputs | state/environment change | missing premise/interface
---|---|---|---
Literal, Name, FlagMember, TopLevelName | none | incoming state or finite producer | name/unwrap can use arbitrary load locations; finite contract required
IfExp | cond, then, else | cenv unchanged; fresh labels/new blocks/different incoming states; ty threaded to arms | pure child support inversion, compile_ifexp_arm copy contract
Builtin | dispatcher args (plus AddMod/MulMod/PowMod256 name fast paths) | cenv unchanged, states threaded | supported_builtin_form + argument closure; fast paths need independent name/unwrap composition
TypeBuiltin | type dispatcher args | cenv unchanged | supported form and actual callback argument support; ABI/copy contracts
Subscript/Attribute | base/key through compile_subscript/compile_attribute | cenv unchanged; arbitrary intermediate states | pure/effect place predicates require their own closure lemmas, not merely supported_expr inversion
StructLit | field expressions | cenv unchanged, allocation then field traversal | supported field inversion and recursive materialization/copy
Call | positional/keyword arguments | cenv unchanged; INVOKE does not inline callee | supported call inversions; external ABI staging/return decode, internal callee packaging separately
Pop | supported root has NO child expression | compile_get_target_ptr leaves state unchanged for root | literal header at any cenv, but all locations must be certified or environment validity introduced
base target Subscript/Attribute | recursive bt, subscript key | cenv unchanged; sequential states | supported_target_info yields key support, recursive descriptor may differ
Pass/Break/Continue/empty Return | none | finite emission/block state | lctx alternatives include fallback INVALID
Expr/Return/AnnAssign/Assign/AugAssign/Append/Assert/Raise/Log | expressions/reasons/targets | same cenv per statement, state threaded | source support inversions; copies, guards, external/internal return helpers
If statement | condition and both bodies | cenv unchanged, lctx unchanged, new blocks | supported_stmts for both branches
For Range/Array | bounds/array + loop body | body_cenv from declare_local; InLoop exit incr; new blocks | support body remains tops/bindings indexed, not cenv indexed
statement list | head, tail | declare_stmt_local cenv s yields cenv', compile head AND tail under cenv'; block_is_terminated skips both | universal-cenv IH avoids environment transport; declarations still need state-boundary preservation

stmtLowering:787-1360 defines compile_stmt and compile_stmts mutually, generated `compile_stmt_ind`, measure 2*stmt_size+2 versus 2*list_size stmt_size+1. supported_stmt/supported_stmts are also mutual (supportedStmts:128-163), but use unchanged `bindings` for list tails and loop bodies. `declare_local` (stmtLowering:710-724) changes ce_var_type, ce_dynarray_capacity, optionally ce_vars, and fresh_var state. For-loop body compilation occurs at 1213/1315 under body_cenv, while list recursion at 1351-1353 uses cenv'. If an environment relation is later introduced it must tolerate these exact updates; fixed equality to build_compile_env cannot be the IH premise.

## 3. Callback / recursive producer contracts (UNVERIFIED)

Existing duplication search: compiler boundary bind/new_block already exist; local producer contracts are enumerated in ProducerAudit:80-232 and CalldataSliceBoundary. Do not duplicate these. Typed-copy and ABI recursive interfaces below are the missing semantic integration, not a request for another inventory.

Generic callback interface (no new definition proposed):
```sml
!x s y t. pop_comp_boundary s /\ callback x s = (y,t)
          ==> pop_comp_boundary t
```

For compile_abi_decode_static the exact useful contract is:
```sml
(load_opc = MLOAD \/ load_opc = CALLDATALOAD \/ load_opc = DLOAD) /\
(!v s u t. pop_comp_boundary s /\ clamp_fn v s = (u,t)
             ==> pop_comp_boundary t) /\
pop_comp_boundary sa /\
compile_abi_decode_static src dst load_opc clamp_fn sa = (r,sb)
==> pop_comp_boundary sb
```
abiEncoder:167-172 performs load; callback; MSTORE. The allowed-opcode premise prevents treating an arbitrary opcode argument as a safe load. A more general `load_opc <> ASSERT` version might work but has not been validated.

Typed-copy principal proposal:
```sml
!cenv dst dst_ty src src_ty sa r sb.
 pop_comp_boundary sa /\
 compile_store_memory_typed cenv dst dst_ty src src_ty sa = (r,sb)
 ==> pop_comp_boundary sb
```
Use generated compile_store_memory_typed_ind from context:671 onward, jointly with compile_typed_copy_fields, compile_copy_sarray_typed, compile_copy_dynarray_typed, compile_struct_typed_copy. There is no user callback parameter: these are actual mutually recursive compiler functions. Each sibling needs the same state implication for all its parameters. cenv is unchanged throughout recursion; non-acyclic metadata emits INVALID rather than recursing. Existing typed-copy domain/termination machinery should be reused, not an AST induction or a new fuel definition. Dynamic capacity assertion at 755-759 is followed by MSTORE; loop returns via new_block. Both whole paths need certificates. Unconditional cenv is plausible because metadata rejection is an explicit branch; not proved here.

ABI principal proposal:
```sml
!dst src load_opc hi info sa r sb.
 (load_opc = MLOAD \/ load_opc = CALLDATALOAD \/ load_opc = DLOAD) /\
 pop_comp_boundary sa /\
 compile_abi_decode_to_buf dst src load_opc hi info sa = (r,sb)
 ==> pop_comp_boundary sb
```
Use generated compile_abi_decode_to_buf_ind (abiEncoder:440-598), jointly with compile_abi_decode_complex_elems and compile_abi_decode_dyn_loop. Recursion order at 590 is lexicographic: (abi_dec_info_size info,1), (list_size of complex elems,0), (abi_dec_info_size elem_info,2). Preserve load_opc in recursive calls; hi/operands/offsets/state change freely. DecPrimWord supplies `\v. compile_abi_clamp_basetype v clamp_info` to compile_abi_decode_static; its contract above discharges that callback once clamps are proved. DynLoop calls decode on elem_info, not a compiler expression callback. Encoding has separate recursion and must not be conflated with decode.

## 4. Bounded consumer test: CalldataSlice

supportedExprForms:122 admits (CalldataSlice n,[a]); supported_pure_expr supplies argument support. Actual exprLowering:3128-3134 dispatcher is lower_value on HD args at expr_type start_e, THEN compile_slice_calldata start_op (Lit(n2w n)) (type_memory_bytes cenv ret_ty), THEN as_ptr_val. Accepted `pop_compile_slice_calldata_boundary` covers the second stage for arbitrary operands/sizes; no extra restriction on the start or n is needed by that certificate.

Missing intervening contracts: supported singleton inversion; callback preservation lifted through lower_value = callback + unwrap_value; unconditional unwrap_value boundary across all value/location branches; state-neutral as_ptr_val pair mapping; the guarded callback's successful and INVALID alternatives. This is a small real dispatcher consumer test, not another finite producer. It tests precisely whether an all-environments/source-supported callback contract composes through the existing bind theorem. The accepted slice theorem alone does not establish this chain.

## 5. Raw packaging entry/exit (UNVERIFIED proposals)

Entry: bodySim:63-67 -> supported_program + lower_vyper_*_unit success. compileVyper:1402-1428 builds packages from classify_functions and invokes `run_lowering` (NOT a checked optimizer). deploy counterpart is 1470 onward / run_deploy_lowering at 1498. vyperCompiler:630-671 starts initial_compile_state entry_label, runs runtime/deploy generation, and calls extract_context_with_internals. Need supported_program inversion for each external/internal/fallback/constructor package body and registration/guard wrappers; expression support cannot be extracted from arbitrary contained fragments.

Concrete proposed endpoints:
```sml
!label. pop_comp_boundary (initial_compile_state label)

!tops policy unit.
 supported_program tops /\ lower_vyper_runtime_unit tops policy = SOME unit
 ==> !fn bb. MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks
              ==> ~occurs5 pop_guarded5 bb.bb_instructions
```
The cu_context field is confirmed by vyperCompiler:646/676; ctx_functions and fn_blocks are used by its metadata/reachability functions. No HOL declaration has been made. For deploy add runtime_bytecode and lower_vyper_deploy_unit tops policy runtime_bytecode = SOME unit. The actual `extract_context_with_internals` result at vyperCompiler:137-149 is SOME (ctx,REVERSE cs_data_sections), before compiler-unit packaging. Its precise block-selection obligation can avoid field placeholders:

For every output raw function block, there exists an input block with the same bb_instructions in `REVERSE st.cs_blocks ++ [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>]`.

This is UNVERIFIED. Prove it through package_internal_blocks and mk_raw_function (selection/splitting by labels), then combine with pop_comp_boundary. Reversing/selecting whole blocks cannot create a new instruction window; do not assume this about a transform that concatenates instructions. Final lowering guards and metadata decoration need their actual context field transport checked.

## Review recommendation

Smallest next *semantic* proof: lower_value/unwrap_value preservation and the single supported CalldataSlice dispatcher branch with a universally source-supported callback, including guard fallback. Before further finite templates, decide whether all-environments Pop can be handled in every location; otherwise choose and PROBE a minimal environment relation retained by declare_local and function registration. Remaining families: finite dispatcher glue; mutually recursive copy; mutually recursive ABI encode/decode; supported expr/place/target recursion; mutual statements under cenv updates; module wrapper generation; block-selection packaging. None is discharged by this diagnostic. No frozen-target counterexample is known, and no global containment result is asserted.
