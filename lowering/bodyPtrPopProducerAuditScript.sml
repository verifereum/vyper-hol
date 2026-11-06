Theory bodyPtrPopProducerAudit
Ancestors
  exprLowering emitHelper compileEnv venomInst list context

(* Div/mod are the other arithmetic producers of two ISZEROs followed by
   ASSERT. The very next instruction is inside their template, so no later
   monadic continuation can insert the Pop decrement at this position. *)
Theorem pop_unsigned_div_opcodes:
  ~is_signed_type ty /\ compile_safe_div x y ty sa = (out,sb) ==>
  MAP (\i. i.inst_opcode)
    (DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts) =
    [ISZERO; ISZERO; ASSERT; Div]
Proof
  strip_tac >>
  gvs[compile_safe_div_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, mk_inst_def, rich_listTheory.DROP_APPEND1]
QED

Theorem pop_mod_opcodes:
  compile_safe_mod x y ty sa = (out,sb) ==>
  MAP (\i. i.inst_opcode)
    (DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts) =
    [ISZERO; ISZERO; ASSERT; if is_signed_type ty then SMOD else Mod]
Proof
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, mk_inst_def, rich_listTheory.DROP_APPEND1] >> strip_tac >> gvs[rich_listTheory.DROP_APPEND1]
QED

(* Producer audit (compiler-shape evidence, NOT a language-exclusion theorem).
   Store-adjacent templates:
   - compile_ptr_store / compile_store_at_loc: one store; the preceding code
     belongs to the caller and cannot be ignored.
   - compile_dynarray_pop: SUB immediately before the header store; root Pop
     gets a literal header from compile_get_target_ptr's TopLevelNameTarget.
   - compile_dynarray_append: element store follows address ADD (or copy),
     header store follows ADD, not SUB (exprLowering 1099-1134).
   - compile_word_copy_loop: load/address then store, followed by loop control
     (context); dynamic array copies have ADD before element store and an
     exit-block-start header store (context 930-981).
   - compile_nonreentrant_enter/exit: literal slot and literal stored value;
     enter has a single ISZERO then ASSERT (context 388-420).
   - Assign / AugAssign can join an UnsafeSub directly to a store. Therefore
     a SUB/STORE pair alone is NOT an invariant. Checked Sub instead emits
     range/overflow checks after SUB (exprLowering 318-337).
   - Calls have INVOKE in the caller. The same audit must apply to callee
     bodies; generic memory/precompile calls do not emit storage opcodes.

   The useful candidate invariant is a forbidden five-instruction window:
     SLOAD/TLOAD [Var h] -> a; ISZERO a -> b; ISZERO b -> c;
     ASSERT c; SUB [a; Lit 1] -> d.
   Retain identities and outputs, not just this opcode string. Source Pop is
   the intended owner of this prefix; supported root Pop has a literal h.
   Div/mod also have the double-negation assertion, but consume it internally
   with Div/SDIV/Mod/SMOD, before any continuation. Negation's SUB has left
   operand Lit 0 and predecessor SGT/ASSERT; PrevHash's SUB follows NUMBER;
   floor's SUB follows SLT; byte extraction has left Lit 32. String conversion,
   create-size and range-loop SUB sites likewise need their fixed local
   neighbors included in a formal template proof.

   Cross-bind cases still require a language induction, not inspection alone:
   a suffix of one operand can meet the ASSERT of addmod/mulmod (which then
   must emit ADDMOD/MULMOD), or a copy/conversion guard; returned operands and
   partial windows must be tracked. Bare source Assert uses JNZ/new blocks,
   not ASSERT. ABI clamps use SHR/SHL or SIGNEXTEND/EQ before their ASSERT;
   module entry checks and nonreentrancy have one ISZERO, not two.

   Transport domain: bodySim.body_inv_def requires a raw lower_vyper_*_unit.
   compileVyper.lower_vyper_*_unit calls vyperCompiler.run_*_lowering, then
   extract_context_with_internals: reverse finalized blocks, append current
   block, split at internal labels, package unchanged basic blocks. No IR
   optimization is run on this path. checked_unit_pipeline is separate.
   This supports a block-local window invariant; it is not permission to infer
   source occurrence from fn_has_code. A universal proof must additionally
   establish the invariant from initial_compile_state through all wrappers,
   supported expression/statement lowering, and internal function bodies. *)

(* Residual coverage manifest, 2026-11-06 (diagnostic, not a proof).
   Scope: raw runtime/deploy lowering used by body_inv, including external,
   internal, fallback and constructor bodies. Paths below are relative to
   lowering/defs; numbers identify definition/assertion sites, not premises.
   This refines the earlier audit above after the boundary-contract work.

   Accepted whole-helper pop_comp_boundary contracts:
   - exprLowering compile_clamp / clamp_and_return / compile_clamp_basetype
     (233-287): pop_compile_clamp_boundary,
     pop_clamp_and_return_boundary, pop_compile_clamp_basetype_boundary
     in bodyPtrPopClampBoundary.
   - compile_safe_add/sub/mul and compile_mul_overflow_check (294-389):
     pop_compile_safe_add/sub/mul_boundary and
     pop_compile_mul_overflow_boundary in bodyPtrPopArithmeticBoundary.
   - compile_safe_div / compile_safe_decimal_div / compile_safe_mod (391-445):
     pop_compile_safe_div_boundary, pop_compile_safe_decimal_div_boundary,
     pop_compile_safe_mod_boundary in bodyPtrPopDivisionFamilyBoundary.
   - compile_safe_pow (487-559), all option/type branches:
     pop_compile_safe_pow_boundary in bodyPtrPopPowBoundary.
   - Literal storage Pop: pop_literal_storage_boundary in
     bodyPtrPopLiteralBoundary. This does NOT certify arbitrary Var headers.
   Accepted generic interfaces: pop_emit_op_boundary for non-ASSERT opcodes;
   pop_comp_boundary_return/bind/new_block; pop_no_sub_finished_template for
   a nonempty no-SUB suffix ending non-ASSERT. No contract below is implied
   merely by an opcode observation or by a clean fragment in isolation.

   Reachable non-Pop ASSERT families still lacking whole-helper contracts:
   A. Conversion, exprLowering 1615-1868:
      compile_int_clamp (1635; ASSERT 1645/1652) is NOT compile_clamp.
      compile_type_convert branches at 1677/1683/1690,1712/1719,
      1736/1743,1755/1762,1775/1786,1809/1823,1849/1863.
      Guards end AND/ASSERT, comparison/ISZERO/ASSERT,
      SIGNEXTEND/EQ/ASSERT, or SHL/ISZERO/ASSERT. load_bytestring_as_word
      (1615) contains SUB [Lit 32; length], no ASSERT; shift opcode must
      be SAR or SHR (not arbitrary). compile_type_builtin_dispatch_body
      Convert -> mk_convert_op -> compile_type_convert, and optional
      compile_bytestring_widen_copy -> context copy. Fixed finite cases,
      no compiler callback inside compile_type_convert. Missing contracts
      for int clamp, bytestring preamble and conversion; source validity
      may eliminate cases but must not be assumed from result typing alone.
   B. Small builtins reached by supported_builtin_form:
      builtinMath compile_addmod (70, ASSERT72) / compile_mulmod (79,81):
      bare ASSERT input, immediately followed ADDMOD/MULMOD. Need whole
      two-instruction contract (never certify bare ASSERT independently).
      exprLowering compile_neg (1886,1890): SGT/ASSERT/SUB [Lit0;v].
      builtinSimple compile_builtin_abs (114,122): SUB then
      SLT/EQ/AND/ISZERO/ASSERT, followed compile_select.
      builtinMisc compile_as_wei_value_int (222,240): MUL/Div/EQ/ISZERO/
      OR, optional signed AND, ASSERT; supported form requires unsigned
      operand. Decimal helper (246,251) is source-excluded by that form.
      builtinMisc compile_blockhash (163,170/173): NUMBER/SUB then
      SLT/ISZERO/ASSERT and LT/ASSERT, ending BLOCKHASH.
      compile_ecrecover (32,50), compile_ecadd_points (105,130),
      compile_ecmul_point (135,154): allocation/stores/STATICCALL/ASSERT;
      ecrecover ends MLOAD, point helpers return at ASSERT. No callbacks,
      but need allocation + fixed-suffix contracts; no guarded4 suffix
      follows STATICCALL. Legacy scalar compile_ecadd/ecmul are not the
      ECAdd/ECMul dispatch destinations (exprLowering 3176-3198).
      builtinBytes compile_assert_slice_bounds (26,35): ADD/LT/GT/OR/
      ISZERO/ASSERT; reachable via CalldataSlice -> compile_slice_calldata.
      Its allocation preamble/copy suffix also need composition contracts.
      Uint2Str uses compile_uint2str and block transitions; no direct ASSERT.
   C. External calls and ABI:
      exprLowering compile_extcodesize_check (883,886): EXTCODESIZE/ASSERT;
      compile_return_value_decode (897,902): LT/ISZERO/ASSERT then select/ADD;
      compile_call Send (2717,2730): CALL/ASSERT. IntCall emits INVOKE;
      callee bodies are separately lowered, not spliced at the call.
      compile_external_call_kwargs (1005) invokes encoding, return-size
      checks, decoding and new blocks. Supported calls reject defaults;
      compile_default_return_path is therefore not a required branch there.
      builtinAbi lower_abi_decode (79,88/97): EQ or LT/ISZERO before ASSERT,
      then allocation and compile_abi_decode_to_buf. AbiEncode uses
      compile_abi_encode_to_buf (no direct ASSERT, but copy/loop contracts).
      abiEncoder compile_abi_int_clamp (40,47/52),
      compile_abi_bytes_clamp (60,65), compile_abi_clamp_basetype BoolClamp
      (71,80): SIGNEXTEND/EQ or SHR/SHL/ISZERO guards; distinct from the
      accepted exprLowering clamps. compile_getelemptr_abi (399,412),
      compile_abi_decode_dyn_elem_ptr (420,428/432): LT/ISZERO or GT/ISZERO.
      compile_abi_decode_to_buf DecBytestring (446,451/460), DecDynArray
      (475,480/490), DecComplex (520,531): capacity/end comparisons.
      Recursive decode complex-elements/dyn-loop, static decode callback,
      and all MLOAD/CALLDATALOAD/DLOAD loader choices need contracts; arbitrary
      loader opcodes cannot be assumed safe. ABI paths are reached from
      function argument registration, external returns, and TypeBuiltin.
   D. Context/copy and statements (not more arithmetic):
      context compile_copy_dynarray_typed (751,758), mutually defined with
      compile_store_memory_typed (671): MLOAD/GT/ISZERO/ASSERT then MSTORE,
      copy or recursive element loop/new_block. Reachable through aggregate
      assignment/materialization/argument staging/returns; recursive contract
      missing. Other context copy/allocation helpers have no direct ASSERT;
      compile_alloc_buffer/dynamic/fixed_region_with_id (241/252/272)
      still need metadata/non-ASSERT emission transport, not new guard facts.
      stmtLowering compile_range_bound_checks (628,636/640):
      (S)GT/ISZERO/ASSERT twice; fixed helper missing.
      For-loop dynamic iterator branch (1250-1280, ASSERT1277): after
      new_block/ASSIGN, GT/ISZERO/ASSERT then JMP; body/copy callbacks need
      recursion contract. Source Assert uses JNZ and blocks, not ASSERT.
      Append (exprLowering1099,1109) load/LT/ASSERT then address/copy/stores;
      array_subscript (1362,1379) OR/ISZERO/ASSERT after bounds checks:
      these belong to storage/place recursive interfaces, not conversion.

   Source exclusions (supportedExprForms 98-138; supportedExprs 63-103):
   In/NotIn rejected, hence compile_var_array_membership ASSERT819 excluded.
   Keccak/Sha256/Hash-create/rawcall/system/create/slice-other-than-CalldataSlice
   are not admitted builtin/call forms: builtinHashing ASSERT103/118/134,
   builtinSystem138, builtinCreate180/238 and unsupported general branches
   are not extra raw-unit obligations. builtinMisc floor/ceil are excluded.
   supported forms do admit Env/Acc except Code, BlobHash/PowMod256, arrays,
   literals/structs/places: no direct ASSERT beyond listed helper calls.
   These are source restrictions to PROVE during recursion, not global
   opcode absence assumptions. Bytecode/eval and typedCopyCounterexample
   theories are tests/independent producers, not executable raw-unit callees.

   Wrapper obligations, reserved for packaging/storage leaves:
   context compile_nonreentrant_lock (392,398/406): literal SLOAD/TLOAD,
   one ISZERO/ASSERT; unlock (414) no ASSERT. moduleLowering
   compile_selector_dispatch_dense (ASSERT266): OR/ISZERO/ASSERT then DJMP;
   compile_fallback_body (643,649), compile_entry_checks (737,742/749),
   compile_generate_deploy (825,836): CALLVALUE/ISZERO or calldata LT/ISZERO.
   All reached only under their dispatch/payability/constructor branches.
   compile_generate_runtime -> external_fn_bodies / fallback / internal_fns;
   deploy -> constructor registration/body / ctor internal_fns. Registration
   uses ABI decoders, guarded bodies use nonreentrant and compile_stmts.
   Raw extract_context_with_internals reverses/selects whole blocks and
   splits at labels, not instructions; no optimizer or ASSERT synthesis.
   Need initial-state, block-selection, callee and source-interface theorems.

   Next bounded candidate: A (int-clamp + bytestring preamble + conversion),
   then B small builtin families. C/D and wrappers remain explicit gaps.
   Census includes both emit_void ASSERT and emit_inst ASSERT; variable-opcode
   emitters require opcode constraints (division, shift and ABI/location loads).
   This manifest is finite source evidence only: neither universal compiler
   exclusion nor pop_expr_ptr_ok nor a counterexample has been established. *)
