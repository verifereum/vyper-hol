# Supported open-body coverage audit (2026-11-07)

Diagnostic only: no compiler coverage theorem, containment theorem, or frozen-target counterexample is established here. Baseline `holbuild(bodyPtrPopCompilerRecursionBoundaryTheory)` passes (TO_pop-20261106T070927Z_m3961_t001). This report supersedes the expression/dispatcher coverage portions of pop-integration-audit.md, not its remaining statement/module obligations.

## Exact consumer and notation

The three premises are CompilerRecursionBoundaryScript.sml:34-54. All cenv, threaded ty, callback functions, and incoming states remain arbitrary. In this report C(s) means the existing pop_comp_boundary s (notation only, not a new HOL definition). H(cfn) abbreviates in prose:

```
!cenv ty e sa r sb. supportedExprs$supported_expr tops e /\
  pop_comp_boundary sa /\ cfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb
```

E e is supportedExprs$supported_expr tops e; B rt bi args is supported_builtin_form tops rt bi args /\ EVERY (supported_pure_expr tops) args; TT vt tb rt args is supported_type_builtin_form tops vt tb rt args /\ EVERY (supported_pure_expr tops) args. No environment agreement or source-typing assumption is available. The unrelated exprLoweringProps supported_expr must not be used accidentally.

Gap classes: **S** source-predicate/callback-domain bridge; **O** actual/open defining-equation bridge; **P** missing complete producer boundary; **F** final bind/case composition. A producer contract is not a dispatcher contract. A report row marked missing is not an admitted theorem.

## Existing exact interface dictionary

The following source signatures have been checked. Common convention in this paragraph only: `C sa /\ f ... sa = (r,sb) ==> C sb` means the exact state implication with all displayed producer parameters arbitrary.

* Materialization: pop_unwrap_value_boundary for unwrap_value cenv vv; pop_lower_value_boundary adds `(!s v t. C s /\ cfn cenv ty e s = (v,t) ==> C t)` to the implication for lower_value cfn cenv ty e. No rank guard. pop_ptr_load_boundary for compile_ptr_load ctor imm loc src; pop_ensure_in_memory_boundary for compile_ensure_in_memory ptr loc bytes n ctor imm; pop_fresh_var_boundary and pop_fresh_label_boundary. All unconditional on cenv/types/locations.
* AllocationBoundary: pop_compile_alloc_buffer_boundary; pop_compile_alloc_dynamic_boundary; pop_compile_fixed_region_with_id_boundary; pop_compile_slice_out_buf_boundary. emit_void contract requires opcode <> ASSERT. Materialization pop_emit_inst_boundary and ArithmeticBoundary pop_emit_op_boundary also require opcode <> ASSERT. CompilerBoundary pop_comp_boundary_return/bind/new_block supply composition, not individual ASSERT safety.
* ArithmeticBoundary: pop_compile_safe_add/sub/mul_boundary; DivisionFamilyBoundary: pop_compile_safe_div_boundary, pop_compile_safe_decimal_div_boundary, pop_compile_safe_mod_boundary; PowBoundary pop_compile_safe_pow_boundary. SmallMathBoundary pop_compile_neg_boundary, pop_compile_builtin_abs_boundary, pop_compile_addmod_boundary, pop_compile_mulmod_boundary, pop_compile_select_boundary. These are whole-producer state implications, with arbitrary operand/type/option parameters. No compile_binop boundary was found.
* MiscGuardBoundary pop_compile_as_wei_value_int_boundary (both signedness branches), pop_compile_blockhash_boundary, pop_compile_assert_slice_bounds_boundary. CalldataSliceBoundary pop_compile_slice_calldata_boundary covers arbitrary start, length, size.
* ConversionBoundary pop_compile_type_convert_boundary: unconditional state implication for compile_type_convert v cop. ClampBoundary pop_compile_clamp_basetype_boundary is separate. TypedCopyBoundary pop_compile_store_memory_boundary for compile_store_memory cenv src dst dst_ty src_ty and its mutually recursive typed-copy projections are unconditional. CopyBoundary covers compile_copy_memory, compile_copy_memory_dynamic, compile_with_byte_offset, compile_bytestring_copy_len, compile_store_bytestring.
* AbiEncodeBoundary: pop_compile_abi_encode_to_buf_boundary for compile_abi_encode_to_buf dst src info; projections for child, complex_elems, dyn_loop, all unconditional. AbiDecodeBoundary: pop_compile_abi_decode_to_buf_boundary for compile_abi_decode_to_buf dst src lop hi info requires lop <> ASSERT, plus C sa and equation; complex_elems/dyn_loop projections retain that restriction. They do NOT yet certify lower_abi_encode/lower_abi_decode wrappers.
* SupportedBoundary pop_toplevel_target_literal: compile_get_target_ptr cfn cenv (TopLevelNameTarget id) sa = ((op,lo,pt),sb) ==> sb = sa /\ ?h. op = Lit h. RootLocationBoundary pop_nonstorage_dynarray_boundary and pop_literal_all_locations_boundary cover nonstorage and literal storage/transient paths. `pop_literal_scaled_locations_boundary` is LOCAL to SupportedBoundary. pop_toplevel_expr_boundary and pop_supported_expr_boundary concern ACTUAL compile_expr, not compile_expr_body. This is an O gap, not a producer gap; expose/reuse the local scaled lemma rather than duplicating its proof.
* IfExpBoundary pop_ifexp_body_boundary is already arbitrary-callback: `(!a aty s v t. (a=cond_e \/ a=then_e \/ a=else_e) /\ C s /\ cfn cenv aty a s=(v,t) ==> C t) /\ C sa /\ compile_expr_body cfn bfn tfn cenv ty (IfExp rt cond_e then_e else_e) sa=(r,sb) ==> C sb`. pop_ifexp_child_body_boundary is guarded and is not the required interface; use the former. pop_compile_ifexp_arm_boundary is unconditional.
* MathIntegration pop_math_dispatch_boundary is arbitrary-callback: `(bi=Neg \/ bi=Abs \/ bi=AddMod \/ bi=MulMod) /\ supported_builtin_form tops ret_ty bi args /\ (!a aty s v t. MEM a args /\ C s /\ cfn cenv aty a s=(v,t) ==> C t) /\ C sa /\ compile_builtin_dispatch_body cfn cenv ret_ty ty bi args sa=(r,sb) ==> C sb`. pop_single_math_dispatch_boundary and pop_triple_math_dispatch_boundary give its singleton/triple cases. **pop_supported_math_dispatch_boundary instead compiles with expr_child_callback bound cfn** and assumes support AND size bound for cfn; it cannot directly discharge the arbitrary-callback closure premise.
* SliceIntegration pop_slice_dispatch_boundary: `(!s v t. C s /\ cfn cenv (expr_type a) a s=(v,t) ==> C t) /\ C sa /\ compile_builtin_dispatch_body cfn cenv ret_ty ty (CalldataSlice n) [a] sa=(r,sb) ==> C sb`. pop_supported_slice_dispatch_boundary is guarded; use pop_slice_dispatch_boundary and pop_slice_supported_form for the closure premise.

## Source bridges and a substantive domain warning

supportedExprs:110-113 proves E = pure OR effect definitionally, so pure => E is immediate by that equation (no new recursive theorem needed). supported_pure_exprs_every (:145-149), supported_pure_fields_every (:151-157) bridge list encodings to EVERY. supported_call_default_rejected (:137-143) and supported_external_call_contract (:124-135) are available. EffectClassification pop_supported_target_shape gives the root Pop inversion.

However **supported_place_expr is NOT definitionally E**. At supportedExprs:44-51 its TopLevelName case uses supported_place_root tops id, ignoring the expression's annotated ty; pure TopLevelName (:13-15) needs supported_storage_value tops id ty or immutable type equality. supported_place_root (supportedExprForms:216-227) also admits hashmap declarations, not just value declarations. Effect-place Subscript/Attribute likewise omit the supported_place_type conclusion required by effect_expr. No place=>E theorem was found in supported/. Thus Subscript/Attribute parent support does not currently justify all calls of an arbitrary H(cfn). This is a concrete S-interface gap, possibly a false intended open-body premise; NOT a proof of falsehood, and NOT a counterexample to Pop. A next probe should test the callback domain before attempting the whole expression premise. Possible strategist repair: enlarge E to include pure/effect place support and prove closure for that enlarged domain; that changes the closure instantiation, not the frozen theorem. Do not silently add typing or cenv agreement to the existing exact premise.

## Expression matrix (all constructors)

Definition locations below are in defs/exprLoweringScript.sml; support locations are in supported/supportedExprsScript.sml. Support elimination uses E definition followed by the displayed constructor equations, not unsupported source-occurrence inversion.

| Body branch | Source elimination / callback domain | Complete producers and exact coverage | Remaining |
|---|---|---|---|
| Literal, 2940 | pure true (:12), effect false; no callback, any annotation/literal | compile_literal_vv :1453-1482: return or compile_bytelike_literal then return. Return/allocation covered, but no complete literal-vv/bytelike contract found. pop_literal_stack_no_emit covers only returning StackValue, not allocated literals. | P finite bytelike + literal; F |
| Name, 2941 | pure true (:11), no callback | compile_name_vv :1490-1502: memory/pointer return or INVALID + return. return/pop_emit_inst_boundary apply. | P complete name contract; F |
| IfExp, 2942-2969 | pure :19-22 yields pure cond/then/else -> E; effect false; cond via lower_value Bool, arms via cfn at arbitrary threaded ty | fresh_var, fresh_label x3, JNZ, new_block x3, compile_ifexp_arm x2, ASSIGN/JMP x2 all covered by pop_ifexp_body_boundary | S finite inversion; F application only |
| Builtin AddMod three Names, 2970-2971 | pure Builtin :32-33, form has triple unsigned args; no callback actually invoked | compile_addmod_names :2893-2902 calls compile_name_vv/unwrap three times then compile_addmod. unwrap + addmod covered, name contract missing. Generic dispatcher theorem does NOT match this branch. | P name; O fast-path composition |
| Builtin MulMod three Names, 2972-2973 | same triple shape | compile_mulmod_names :2904-2913, name/unwrap x3 then compile_mulmod | P name; O fast-path composition |
| Builtin PowMod256 two Names, 2974-2975 | pure/form double unsigned args; no callback | compile_powmod256_names :2915-2922, name/unwrap x2 then compile_pow_mod256 (no whole boundary found) | P name, pow_mod256; O |
| Other Builtin, 2976-2977 | pure :32-33 gives B via supported_pure_exprs_every; effect false | bfn callback at (cenv,expr_type e,threaded ty,bi,args), directly justified by B-IH | S inversion; F, no dispatcher unfolding here |
| TypeBuiltin, 2978-2979 | pure :34-35 gives TT via pure_exprs_every; effect false | tfn callback at (cenv,expr_type e,threaded ty,tb,tbt_ret_ty,args) | S inversion; F |
| Subscript, 2980-2981 | pure :26-28 or effect :86-90; key pure/effect -> E; base supported_place_expr or supported_effect_place_expr is the DOMAIN GAP above | compile_subscript :2278-2325 invokes cfn base at threaded ty; Map branch lowers key at expr_type, optional compile_keccak256_key then compile_mapping_subscript; Tuple/Struct branch only compile_tuple_subscript (NO key callback); other ValPT lowers key at threaded ty then compile_array_subscript with loader compile_ptr_load. No whole place/array-subscript contracts found. ptr_load covered. All cenv-dependent Map/Val branches remain possible even if source supports only another descriptor. | S critical base-domain; P mapping/key/tuple/array helper certificates; F |
| Attribute, 2982-2983 | pure :29-31/effect :91-93; base place/effect-place, same DOMAIN GAP | compile_attribute :2331-2352 cfn base at threaded ty, ADD then return; opcode/return covered regardless field metadata | S critical; P or F complete attribute boundary |
| StructLit, 2984-2995 | pure :23-25 supplies supported_pure_fields; fields -> EVERY pure o SND -> E; effect false | alloc_buffer, compile_struct_lit :2354-2372 traverses fields; each cfn at expr_type, ADD, unwrap, compile_store_memory, recurse. All nonrecursive chunks covered by allocation/materialization/typed-copy contracts. | S field bridge; P list callback traversal; F |
| FlagMember, 2996-2999 | pure false :16, effect catchall false | state unchanged; no obligation after source inversion | eliminated |
| TopLevelName, 3000-3009 | pure :13-15, effect false; no callback | arbitrary cenv lookup: storage/transient/code LocatedValue return or INVALID. No environment agreement needed for boundary | P/F finite lookup contract |
| Call, 3010-3011 | pure false :37; effect :64-83 only IntCall/ExtCall/Send with NONE; all invoked args pure -> E | see call submatrix | S inversion; P call integration |
| Pop, 3012-3029 | pure false :36; effect :84-85 only TopLevelNameTarget; NameTarget, AttributeTarget, SubscriptTarget all rejected | compile_get_target_ptr root no cfn calls, literal in every cenv; compile_dynarray_pop all locations handled by existing producer library (including fallback memory/code) | O actual-compiler -> open-body bridge; F; no environment premise needed |

### Call submatrix (compile_call :2626-2800)

* IntCall NONE: support :64-68 excludes StructT result, requires function decl, pure args. compile_multi_vvs invokes cfn at each expr_type; then optional alloc_buffer, compile_stage_intcall_args, emit_multi_op/emit_op/emit_void INVOKE, store_multi_results. Allocation, unwrap, memory-store and non-ASSERT primitives covered; complete multi-vvs, stage and store-results contracts missing. Callee compilation is NOT a callback in this body.
* ExtCall NONE: support :72-78 gives arity, pure args, valid opts/static flag/return form. Address callback at AddressT, TAKE positional via multi_vvs, DROP keywords via compile_ext_call_kwargs (its recursion/domain needs membership preservation), optional GAS, compile_external_call_kwargs. The latter uses ABI encoding/decoding and return-size/extcodesize/default helpers. Existing ABI recursive contracts are prerequisites, not a certificate for this wrapper. Default_opt may arise from opts even though syntactic default_ret is NONE: inspect keyword producer rather than assuming no default path from NONE alone. Complete external-call/kwargs boundaries missing.
* Send F [a;v] NONE and Send T [a;v;g] NONE: :79-83; lower_value AddressT, Uint256, optional gas Uint256; emit CALL then ASSERT. Need a complete CALL/ASSERT template (bare ASSERT cannot use non-ASSERT interface). No such whole boundary located.
* All Call SOME default: rejected by supported_call_default_rejected. All other targets RawCallTarget, RawCallCalldataTarget, RawLog, RawRevert, SelfDestructTarget, CreateTarget and all wrong Send arities/results are rejected by pure=false and supported_effect_expr catchall. No callbacks from those branches enter this premise.

## Builtin dispatcher matrix (all constructors)

Forms at supportedExprForms:98-124 fix arity independently of threaded compiler ty. EVERY pure args supplies E for each HD/EL/MEM selection. Actual callbacks may return arbitrary vyper_value/types/operands; boundary proofs cannot assume source typing of those results.

| Form / body location | Callback invocations | Producers and existing coverage | Remaining |
|---|---|---|---|
| Bop op [a;b], 3035-3076 | generic lower_value a,b at expr_type a; branch-special e2 array-list elements/array callback and bytestring hashing are discussed below | compile_binop :607-678 calls safe add/sub/mul/div/decimal-div/mod/pow, wrapping emit+wrap_truncate, bitwise/shift, compare, min/max select. Safe arithmetic/pow/select covered; complete compare/wrap/binop missing. | S op restriction; P/F binop composition |
| Not [a], 3077-3086 | lower_value at expr_type a, NOT at ret_ty | Bool emits ISZERO; otherwise compile_invert (all expr_type branches, despite supported result ty Bool/uint256). Need complete invert, then composition. | P/F |
| Neg [a], 3087-3091 | lower_value at expr_type a | compile_neg covered, use arbitrary pop_math_dispatch_boundary | S pure=>E; F |
| Abs [a], 3092-3095 | lower_value at threaded ty | compile_builtin_abs covered by pop_math_dispatch_boundary | S/F |
| Env item [], 3096 | none | compile_env_var :1508-1528, all fixed opcodes incl PrevHash NUMBER/SUB/BLOCKHASH non-ASSERT | P/F finite env contract |
| Acc item [a], 3097-3099 | compile_acc :2866-2885 lowers a at AddressT | Balance BALANCE; Codesize EXTCODESIZE; Codehash EXTCODEHASH; IsContract EXTCODESIZE/GT; Address lower_value only. Code excluded by item<>Code. | P/F complete acc |
| CalldataSlice n [a], 3128-3134 | lower_value at expr_type a | pop_slice_dispatch_boundary + pop_slice_supported_form already arbitrary callback | S pure=>E; F |
| BlockHash [a], 3143-3146 | lower_value at threaded ty | pop_compile_blockhash_boundary | F |
| BlobHash [a], 3147-3150 | lower_value at threaded ty | compile_blobhash; no complete boundary located (non-ASSERT producer) | P/F |
| AddMod [a;b;c], 3151-3156 | lower_value all at threaded ty | pop_math_dispatch_boundary exact arbitrary-callback interface | S/F |
| MulMod [a;b;c], 3157-3162 | same | same | S/F |
| PowMod256 [a;b], 3171-3175 | lower_value both at threaded ty | compile_pow_mod256 (not compile_safe_pow); no whole contract found | P/F |
| ECRecover [a;b;c;d], 3176-3183 | lower_value all at threaded ty | compile_ecrecover alloc/stores/STATICCALL/ASSERT/MLOAD; no whole contract | P complete precompile template, F |
| ECAdd [a;b], 3184-3191 | cfn each at own expr_type, then unwrap each | compile_ecadd_points, not legacy compile_ecadd; allocation/stores/STATICCALL/ASSERT; no whole contract | P/F |
| ECMul [a;b], 3192-3198 | cfn a at own expr_type + unwrap; lower_value b at Uint256 | compile_ecmul_point, not legacy compile_ecmul; no whole contract | P/F |
| MakeArray NONE (Fixed n), 3286-3294 | compile_make_tuple traverses args (own expr_type) | alloc_buffer; make_tuple stores/copies; typed-copy/unwrap covered but list producer missing | P callback traversal; F |
| MakeArray (SOME elem) bnd, 3295-3304 | compile_make_array traverses args (own expr_type) | alloc_buffer; element materialization/store, dynamic length flag; complete list producer missing | P callback traversal; F |
| Uint2Str n [a], 3257-3261 | lower_value at threaded ty | compile_uint2str alloc, loop CFG, no complete boundary located | P loop composition, F |
| AsWeiValue d [a], 3262-3270 | lower_value at expr_type a | source demands supported_unsigned_type(expr_type a), excludes decimal branch; pop_compile_as_wei_value_int_boundary covers arbitrary signedness | S unsigned=>not_decimal; F |

**Bop subbranches.** supported_binop :39-70 admits Add/Sub/Mul/Div/Mod/Exp/UnsafeAdd/UnsafeSub/UnsafeMul/UnsafeDiv/And/Or/XOr/ShR/ShL/Eq/NotEq/Lt/LtE/Gt/GtE/Min/Max with their exact numeric/integer/word restrictions. In, NotIn, ExpMod are false. Thus :3046-3059 membership path eliminated by op alone (even arbitrary rhs annotation); :3060-3069 bytestring equality path requires Eq/NotEq with is_bytestring_type(expr_type a), whereas Eq/NotEq support needs supported_word_type(expr_type a). Need the explicit word=>not_bytestring bridge; inspect fixed BytesT versus dynamic bytes/string carefully. If not eliminated, hash producer is non-ASSERT and can instead be covered, but do not assume elimination from result type. Generic compile_binop can be proved for all op/type/option inputs if its actual producer cases permit it; that stronger contract removes unnecessary source arithmetic case plumbing. In/NotIn compile_binop branches themselves are no-ASSERT, but not the dispatcher membership helper.

**All unsupported builtin branches**: Keccak256 (:3100), Sha256 (:3113), CalldataLen (:3126), Len (:3135), Ceil (:3163), Floor (:3167), Concat (:3199), Slice (:3218, including msg.data/self.code/extcode/bytesM paths), MethodId (:3271), and MakeArray NONE with non-Fixed bound are rejected by supported_builtin_form catchall. Every supported constructor with wrong argument count is likewise rejected (MakeArray uses variable arity with element/layout predicate). No hash/slice runtime callback domain needs proving for these rejected forms. Constructor enumeration is exactly the case arms at :3034-3306; chain interactions are Call targets, not additional builtin arms.

## Type-builtin dispatcher matrix (all constructors)

Support :126-139 supplies TT with vv_ty in the support result position, not threaded ty. ret_ty is the target type. Every live argument is pure -> E.

| Form / body location | Callback domain and producers | Coverage / gap |
|---|---|---|
| Convert [a], 3312-3340 | lower_value at expr_type a. Zero-capacity bytestring shortcut returns unchanged after callback. Widen branch compile_bytestring_widen_copy; Flag target compile_type_convert ConvToFlag; others compile_type_convert(mk_convert_op ...) | pop_lower_value_boundary and pop_compile_type_convert_boundary unconditional; widen helper :1874 needs composition from alloc/copy contracts. Do not drop widening based on valid_conversion without proof; compiler lowered_value_type depends on arbitrary cenv. P/F widen + case composition |
| Empty [], 3341-3348 | no callback; word unchanged state; nonword compile_builtin_empty_complex size zero_length_only | allocation/primitive facts exist; complete empty-complex contract missing. P/F |
| MaxValue [], 3349-3350 | no callback, type_bounds only, state unchanged | F inversion/reflexivity |
| MinValue [], 3351-3352 | same | F |
| Epsilon [], 3353 | state unchanged | F |
| AbiEncode F (SOME mid) [a], 3362-3394 | support LENGTH mid=4 and target TupleT[t] with supported_tuple_type t. LENGTH args=1 and not ensure force SINGLE branch; compiler still dispatches on expr_type a being word, unrelated to target restriction. word: lower_value + alloc32/MSTORE, lower_abi_encode; nonword: cfn own type + unwrap, lower_abi_encode | encode_to_buf covered, lower_abi_encode wrapper in builtinAbi:44 missing. Multi-arg compile_multi_exprs/store_abi_tuple branch eliminated by arity/F, not by type. P wrapper; F |
| AbiDecode F [a], 3395-3405 | cfn at own type + unwrap. F makes wty=ret_ty; lower_abi_decode uses decode info and arbitrary cenv-derived sizes | decode_to_buf covered for loader<>ASSERT; lower_abi_decode wrapper (builtinAbi:79) guard/allocation composition missing. P wrapper; F |
| Extract32, 3354-3361 | no supported form at all | eliminated by supported_type_builtin_form catchall |

All Convert/Empty/Max/Min/Epsilon/Abi forms of other arity are rejected; AbiEncode ensure=T or method_id=NONE and AbiDecode unwrap=T rejected. Max/Min require vv_ty=ret_ty and numeric; Empty vv_ty=ret_ty plus supported_value_type; Epsilon decimal. These restrictions need not be used to prove state-neutral cases but must not be confused with threaded ty.

## Proposed semantic integration batches (not new PLAN IDs)

1. **Resolve the callback domain before universal expression integration.** Probe supported_place_expr/effect_place=>E, especially hashmap TopLevelName and mismatched annotations. Exact suspect implication: `!tops e. supported_place_expr tops e ==> supportedExprs$supported_expr tops e`. If false, strategist must choose enlarged E (pure OR effect OR place OR effect_place), or a separate direct actual-compiler/place closure. Neither is authorized as an executor edit here. No environment validity premise may be smuggled into the exact three premises.
2. **Shared finite scalar/base batch.** Proposed complete state implications `C sa /\ compile_name_vv cenv rt id sa=(r,sb) ==> C sb`, same for compile_literal_vv, compile_bytelike_literal, compile_env_var, compile_invert, compile_binop, compile_blobhash, compile_pow_mod256. Existing whole guard/arithmetic facts above are reused. Compose the three optimized Name helpers with name/unwrap/addmod/mulmod/pow; do not rewrite them as generic callback dispatch.
3. **Supported builtin open body.** Target exactly `!cfn. H(cfn) ==> !cenv rt ty bi args sa r sb. B rt bi args /\ C sa /\ compile_builtin_dispatch_body cfn cenv rt ty bi args sa=(r,sb) ==> C sb`. Split internally into scalar/MathIntegration+SliceIntegration, precompile (EC* complete templates), and aggregate/Uint2Str traversals. All use arbitrary callbacks, no rank guards. Proposed traversal contract: `(!a aty s v t. MEM a args /\ C s /\ cfn cenv aty a s=(v,t) ==> C t) /\ C sa /\ compile_make_array cfn cenv args elem esz has_lw buf sa=(r,sb) ==> C sb`; analogous compile_make_tuple. Search before adding. Need exact helper argument orders from definitions when implementing.
4. **Supported type open body.** Target exactly `!cfn. H(cfn) ==> !cenv vt ty tb rt args sa r sb. TT vt tb rt args /\ C sa /\ compile_type_builtin_dispatch_body cfn cenv vt ty tb rt args sa=(r,sb) ==> C sb`. Shared prerequisites: unconditional lower_abi_encode/lower_abi_decode wrapper boundaries (all sizes/info arbitrary, loader MLOAD discharges <>ASSERT), bytestring widening, empty-complex. Existing recursive encode/decode/copy proofs are retained, not reproved.
5. **Supported expression open body.** Target exactly first premise at RecursionBoundary:34-42 instantiated with E/B/TT, but only after batch 1 validates/repairs the domain. Reuse arbitrary pop_ifexp_body_boundary; expose scaled-literal Pop boundary and give compile_expr_body Pop contract (arbitrary cfn,bfn,tfn; no actual compile_expr hypothesis). Place traversal, struct fields, internal/external/send calls require their own complete callback contracts. Proposed root Pop statement: `C sa /\ compile_expr_body cfn bfn tfn cenv ty (Pop rt (TopLevelNameTarget id)) sa=(r,sb) ==> C sb`; this is independent of H(cfn) because root target ignores callback.
6. Apply the ALREADY PROVED pop_compile_mutual_boundary_closure after the three open-body obligations hold. No new numeric rank induction. Then statement/list lowering, wrappers and raw packaging remain separate obligations; expression coverage is not function containment.

### Consolidation proposal

Old templates placeholder should own only remaining shared finite/base, precompile and wrapper producers plus builtin/type open-body integration; do not spawn per-opcode descendants. Existing arithmetic/conversion/ABI/copy proofs become dependencies, not renewed work. Old storage placeholder should own the source-domain decision and place/root-Pop/aggregate/call open expression integration, with domain probe first. Old recursion placeholder is no longer a numeric-induction task: conditional recursion is completed; its remaining job is instantiating closure using the three semantic contracts after source-domain repair, then the separate statement/list layer. Packaging remains blocked on these and must still cover module wrappers, registration/callees, initial_compile_state and block-selection transport to actual raw contexts. These are recommendations for strategist review, not unilateral PLAN changes.

## Evidence and limits

Current definitions and signatures inspected in TO_pop-20261106T070927Z_m3962_t001 through m3990_t001 (especially m3964, m3965, m3966, m3971, m3972, m3976, m3977, m3979, m3981-m3984, m3986, m3988-m3990). Signature absence search m3985 found no complete named boundary for binop/name/literal/precompile/list/place/external-call/uint2str producers. Prior broad producer audit is used only as an index; its old 'missing copy/ABI' entries are now superseded by the accepted actual recursive producer signatures above. No claim of proven impossibility is made from an absent lemma. The callback-domain warning is a definition-level discrepancy requiring a checked probe, not an EVAL-confirmed counterexample. Frozen pop_expr_ptr_ok remains unchanged and open.

## Checked domain repair (2026-11-07, post-E0141)

`bodyPtrPopPlaceDomainProbeTheory` checks the narrow bridge false by EVAL; this is not a Pop counterexample. `bodyPtrPopCompileDomainTheory` now defines the authorized four-mode `pop_compile_domain` and checks source-child closure (TO_pop-20261106T070927Z_m4042_t001). This supersedes E=supported_expr in the proposed three-premise instantiation above; B and TT are unchanged. Supported-expression preservation will be a corollary of `pop_domain_supported`, not a new assumption. No compiler producer theorem is proved by this repair.

Callback row crosswalk against the checked interface:

* Literal, Name, FlagMember, TopLevelName and optimized AddMod/MulMod/PowMod256 Names have no recursive callbacks. The optimized cases still need actual finite producer composition, not callback closure.
* IfExp cond/arms: `pop_domain_ifexp_children`; includes callback at BoolT and arbitrary threaded arm ty without any type-index restriction on D.
* Generic Builtin and TypeBuiltin: `pop_domain_builtin_form` and `pop_domain_type_builtin_form` yield exactly B/TT, including EVERY pure args. All dispatcher singleton/double/triple/quadruple HD/EL uses and MakeArray list traversals use `pop_domain_pure_argument`; source form fixes arity before HD/EL reasoning. Unsupported membership/hash/slice/general forms remain eliminated as in the matrix, not additional domain obligations.
* Subscript base/key, in BOTH pure/place/effect/effect-place modes: `pop_domain_subscript_children`. Map key callback at expr_type and generic array key callback at threaded ty share this same untyped-in-compiler-ty D fact. Tuple/Struct indexing does not compile the key. Attribute base uses `pop_domain_attribute_child`. No declared-type equality or place=>supported_expr implication is used.
* StructLit list traversal: `pop_domain_struct_fields` yields EVERY pure o SND; `pop_domain_struct_child` yields D for each member field expression. The list traversal preserves membership as its tail shrinks; there is no synthetic expression callback.
* Calls: `pop_domain_call_support` retains the exact effect-form restriction, `pop_domain_call_default` forces syntactic default NONE, `pop_domain_call_args` yields EVERY pure. Thus address, TAKE positional, DROP keyword, Send value/gas and internal argument callbacks all use `pop_domain_pure_argument` plus ordinary list membership. `compile_ext_call_kwargs` compiles members of its supplied keyword list (including keyword default, if any); it introduces no new source expression. Callback types remain arbitrary, so AddressT/Uint256/own-type versus threaded-type differences do not require a domain bridge.
* TypeBuiltin Convert and both ABI forms compile only the selected pure argument. Empty/Max/Min/Epsilon have no callbacks. Unsupported Extract32 has no remaining obligation.
* Pop: `pop_domain_pop_target` gives TopLevelNameTarget and supported_storage_dynamic_array, even after the union enlargement. Root target lowering has no child callback; nested/local targets remain excluded from D. A separate open-body producer contract is still required.

No callback site in the audited three supported open bodies remains outside D. This is source-domain closure only: missing producer/open-equation/final-composition rows above, statements and packaging remain open. The repaired domain definition is justified in the source comment as the shared interface for all three closure premises; existing read-only source predicates and the frozen target were not modified.

## Current interface diagnostic (E0147/E0148, 2026-11-07)

Coverage updates supersede earlier 'missing' cells, without certifying open bodies:
* AccessorBoundary supplies environment/account, invert/blobhash/powmod and optimized Name producers (see source for exact projection names); BinopBoundary supplies unconditional compare, wrap_truncate, compile_binop.
* TypeWrapperSupport/TypeWrapperBoundary now supply zero_words and complete EQ/ASSERT and range/ASSERT guards plus unconditional compile_bytestring_widen_copy, compile_builtin_empty_complex, lower_abi_encode, lower_abi_decode. Decoder MLOAD discharges the recursive decoder loader restriction. Both new leaves built, committed dbd06afc2. No standalone ASSERT claim.

Remaining producer contracts verified against actual definitions:
* builtinMisc:32,105,135: compile_ecrecover hash v r s; compile_ecadd_points p1 p2; compile_ecmul_point p scalar. Require unconditional C-preservation with arbitrary operands. All allocation/memory stages have boundaries. Missing common whole guard is `do success <- emit_op STATICCALL args; emit_void ASSERT [success] od`; a two-instruction no-SUB suffix, analogous to the checked EQ guard. Do not use legacy ecadd/ecmul.
* exprLowering:2183-2226: compile_make_tuple cfn cenv args buf offset; compile_make_array_elems cfn cenv args elem_ty elem_size has_length_word buf index; compile_make_array cfn cenv args elem_ty elem_size has_length_word buf. Induct args, generalize offset/index and states; callbacks satisfy `!a aty s v t. MEM a args /\ C s /\ cfn cenv aty a s=(v,t) ==> C t`. Tail membership implies original membership. No relation between callback value type and source annotation is needed: unwrap/store boundaries already unconditional.
* builtinStrings:26-94 compile_uint2str val n_digits buf_size emits a finite six-label CFG, with no recursive compiler call. Compose alloc, fresh_var/label, emit op/inst/void and new_block boundaries. No ASSERT. SUB before MSTORE is harmless without ASSERT; use existing primitive boundary, not a new runtime loop invariant.

Open expression interface:
* Four-mode pop_compile_domain and its child projections remain authoritative. Place helpers compile_subscript/attribute, struct traversal, multi_vvs, stage_intcall_args/store_multi_results and external_call_kwargs still need whole contracts. Keyword recursion exprLowering:2461 follows simultaneous k/e tails; each callback is on a member of original expression list. EKDefault with nonword return calls compile_materialize_vv; syntactic default NONE does not erase this branch. Additional guard templates include CALL/ASSERT for Send, and extcodesize/return-size/default-call guards. All must remain whole guards.
* Root open Pop must be established independently of actual compile_expr theorem, exposing local scaled-literal boundary rather than duplicating it. Existing bodyPtrPopRootCase:20 exports universal `body_pop_root_ptr_ok`; C1.root_current should build this leaf and inspect drift, not reprove its nine-instruction execution from scratch. NameTarget local-memory case is distinct and requires returned-buffer extent plus current word provenance.

Statement / packaging interfaces and induction:
* stmtLowering:787-1360 mutually defines compile_stmt and compile_stmts; compile_stmts tails update cenv after AnnAssign and control-body recursive calls appear in If/For. Use generated compile_stmt_ind (verify exported exact conjuncts before proof) or AST mutual induction; list-only induction misses nested bodies. Statement callbacks must be supported in the environment evolved by declare_local, not merely original cenv. Assignment targets require place-domain closure; augmented assignment invokes binop, load/store; assert/raise/return/control-flow whole guards remain. Expression preservation alone proves none of these.
* moduleLowering:610 compile_guarded_body wraps compile_stmts in optional nonreentrant lock/unlock and termination; :632 external body first registers positional args; :643 fallback has whole CALLVALUE/ISZERO/ASSERT; :658 internal function declares PARAM/RETPC_PARAM, allocates/captures, then body. These are further producer obligations, not trivial packaging rewrites.
* bodySim:61-88 body_inv selects lower_vyper_runtime_unit or lower_vyper_deploy_unit with ctx=unit.cu_context. compileVyper:1402 runtime unit classifies tops, packages/target-installs external/internal/fallback functions and invokes run_lowering. vyperCompiler:630 run_lowering initializes state, invokes compile_generate_runtime, extracts context_with_internals, and checks lowering_context_ok. Thus need boundary initialization + generate-runtime preservation AND each separately compiled internal function before extracting every block. Deploy additionally requires run_deploy_lowering path and immutable-context update. Policy/context checks are not themselves a compiler boundary invariant.
* Actual consumer bodyPtrPopEntryInterface:8 projects SAME func lookup from stmt_state_rel. fn_has_code relates arbitrary fragment suffix/prefix to blocks in that func, not compiler reachability of sa. The final universal exclusion theorem must quantify every function and block in the selected unit context; apply membership then window/sublist algebra. No source occurrence of the queried nested Pop is available or needed for exclusion. No proof of that universal raw-context bridge exists yet.

Evidence: TO_pop-20261106T070927Z_m4190_t001 through m4212_t001. Diagnostic only: producer scope can now be de-risked without opcode children, while dispatchers/expression/statements/packaging still require actual composition and universal source-support transport.

## Statement interface validation (2026-11-07)

Expression preservation is now checked in bodyPtrPopMutualBoundary, not merely
hypothesized. Statement preservation and actual raw-context packaging are still open.

### Exact intended contracts (no extra typing/environment agreement)

```sml
supported_stmt tops bindings s /\ pop_comp_boundary sa /\
compile_stmt ce lc ty s sa = (r,sb) ==> pop_comp_boundary sb

supported_stmts tops bindings ss /\ pop_comp_boundary sa /\
compile_stmts ce lc ty ss sa = (r,sb) ==> pop_comp_boundary sb
```

Quantify all ce, lc, ty, sa, r, sb, and retain arbitrary bindings. The actual
`supported_function_body` (supportedProgram:30) supplies supported_stmts with
`args ++ supported_stmts_bindings T ss ++ supported_stmts_bindings F ss`.
Its nonmain-type and internal-call exclusions are not needed for these proposed
stronger compiler-boundary contracts. No support predicate is changed.

### Checked recursion interface

`pop_statement_boundary_induction` in bodyPtrPopStatementBoundary is proved by
the actual compile_stmt_ind. It exposes all statements via one constructor case
step, If's two same-context lists, For's arbitrary body environment and InLoop
labels, and a separate list-cons step with arbitrary declaration environment.
The generated cons IH is guarded by `~block_is_terminated cs`; the checked
interface retains this guard rather than postulating an unproved fresh state.
The compiler induction order is statement predicate first, list predicate second,
each with four arguments (ce,lc,ty,source). The state is universally quantified
*inside* these predicates. recInduct on an unannotated polymorphic test did not
align; ho_match_mp_tac with compile_env and type annotations does.
Range IH contains a let-bound is_signed equality; array IH contains arr_ty,
is_dynamic, count, arr_elem_ty equalities. The checked interface eliminates these
incidental values. For bodies still quantify arbitrary ce' and loop labels.
AnnAssign's declare_stmt_local changes the environment for both head and tail.
Support uses fixed syntactic bindings, not cenv, so no support-environment frame
is required for that tail.

### Constructor-complete reachable inventory

| Supported constructor | Expression/recursive obligations | Whole producers still missing |
|---|---|---|
| Pass | none | comp_return (existing) |
| Break, Continue | any lc; InLoop JMP, NoLoop INVALID fallback | existing emit_inst boundary |
| Expr e | supported_expr e | actual expression boundary, discard |
| AnnAssign id vtyp e | supported_expr e; declared place/copy guards | emit_local_alloca, compile_assign_value, declare_local/declare_stmt_local for list |
| Assign (BaseTarget bt) e | supported_expr e; supported_target OR supported_target_info = SOME (ValPT t) plus copy guard | supported target ptr traversal, compile_store_at_loc, compile_assign_value |
| Assign (TupleTarget ts) e | supported_expr e; EVERY flat supported_target | compile_tuple_load_all/store_all/unpack (two-pass) |
| AugAssign target_ty bt op e | supported_expr e; supported_target OR supported_aug_target | target traversal, dispatch loads/stores; compile_binop already universally checked |
| Append target e | supported_pure_expr e; target necessarily TopLevelNameTarget | compile_dynarray_append; typed store staging already available |
| If c yes no | pure c; supported lists yes/no | emit_jmp_if_not_terminated; rest fresh labels/new_block/JNZ/JMP existing |
| Assert c reason | pure c; Bare/Unreachable/Reason only | compile_reason_message, compile_revert_with_reason |
| Raise reason | Bare/Unreachable/Reason only | same reason producers; bare REVERT/INVALID existing |
| Log id es | pure es, event field layout | compile_log_eval_all, compile_log_topic_ops, compile_log_store_data; ABI encoder already checked |
| Return NONE | none; arbitrary environment return PC/ctor exit/nonreentrant | compile_nonreentrant_unlock (and existing opcode boundaries) |
| Return (SOME e) | supported_expr e | internal return, from_env wrapper, external return; typed normalization already checked |
| For Range a b | literal IntL endpoints OR pure a/b; supported loop list | declare_local, emit_local_alloca, compile_range_bound_checks, emit_jmp_if_not_terminated |
| For Array e | e exactly Name (ArrayT elem (Fixed m)) name, hence pure; supported loop list | same allocation/jmp helpers, compile_iter_elem_copy; dynamic ASSERT branch unreachable even with arbitrary cenv because arr_ty is expr_type e |

All actual stmt constructors are covered. AssertCustomError/RaiseCustomError are
rejected by support. Supported_target permits only name/top, one-level top
subscript with supported_expr key, or top attribute. supported_target_info
recurses through arbitrary nested target bases and requires supported_expr on
*every* subscript key before returning SOME; therefore every such callback key
is in pop_compile_domain by pop_domain_supported. This implication needs its own
checked projection/traversal proof before use; the table is not that proof.
Reason literals are pure regardless of annotation (supported_pure_expr literal
is T); compile_reason_message has a special typed-string shortcut and otherwise
calls compile_expr. Array iterator Name is likewise unconditionally pure.

### Proposed producer signatures, after duplicate search

For every expression-free producer `p` below the exact common contract is
`pop_comp_boundary sa /\ p sa = (r,sb) ==> pop_comp_boundary sb`, with **all**
listed arguments arbitrary. These are proposed obligations, not theorems:

- `declare_local ce id ty`, `declare_stmt_local ce s`, `emit_local_alloca ce id`,
  `emit_jmp_if_not_terminated label`.
- `compile_store_at_loc imm dst val lo`;
  `compile_assign_value ce dst loc val prim src_lo dst_ty src_ty da_info mem_size`.
- `compile_load_tuple_elements ce src tys offset`;
  `compile_internal_return ce val rpc count ret_ty src_ty elem_types ret_buf`;
  `compile_internal_return_from_env ce ty src_ty val rpc`;
  `compile_external_return val prim raw enc_info max_size nr key transient view`;
  `compile_nonreentrant_unlock key transient view`.
- `compile_revert_with_reason ce vv msg_ty mem_size`;
  `compile_log_topic_ops topics`; `compile_log_store_data ce data buf offset`.
- `compile_tuple_load_all ce src tys offset`;
  `compile_iter_elem_copy ce elem dst size loc slot_addressed target_ty elem_ty`.
- `compile_dynarray_append ce target val ws elem_size elem_ty src_ty cap prim load_op store_op`
  needs `load_op <> ASSERT /\ store_op <> ASSERT` in the raw signature, or a
  location-indexed wrapper using load_opc_for/store_opc_for loc. Its checked
  definition (exprLowering:1099) has load; LT; ASSERT, then ADD/MUL/ADD, typed
  copy or store, then ADD/store. The LT/ASSERT pair needs a whole guard
  boundary. No new definition is needed. Do not assert preservation for
  arbitrary raw ASSERT load/store opcodes.
- `compile_range_bound_checks start end rounds bound signed`: whole guard,
  both SGT/GT; ISZERO; ASSERT triples. Do not use unconditional ASSERT boundary.

Expression-containing producer contracts retain explicit support:
`EVERY (supported_pure_expr tops) es` for compile_log_eval_all;
`supported_string_reason tops e` for compile_reason_message;
`EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt | _ => F) ts`
for tuple store/unpack, and a target-info/target support disjunction for target
pointer compilation. They may be generalized to callback-local preservation only
if the actual producer accepts a callback (tuple unpack/log helpers use actual
compile_expr, not an open callback).

Existing matches: pop_compile_supported_boundary, pop_compile_mutual_boundary,
pop_lower_value_boundary + pop_unwrap_value_boundary, pop_compile_binop_boundary,
pop_compile_store_memory_boundary, pop_compile_store_memory_typed_boundary,
pop_abi_encode_boundary_mutual and pop_comp_boundary_new_block. Searches found
no universal statement producer/target_ptr/append/return contracts. Concrete
pop_global_assignment_boundary/pop_global_return_boundary are not substitutes.
