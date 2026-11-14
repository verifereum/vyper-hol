(* ABI decode / external-call tuple producer checkpoint. *)
Theory tupleAssignImmutableDeployDecodeBoundary
Ancestors
  abiBuiltinDecodeCorrect abiBuiltinDecodeSetup abiBuiltinDecodeHeader
  abiBuiltinValidUnwrap abiBuiltinDecodeEffect abiDecoderEffect abiBuiltinAllocation
  exprSimExtCallCase exprLowering exprLoweringProps context
  compileEnv venomState finite_map words list arithmetic
  supportedProgram supportedStmtTraverse supportedExprTraverse exprSafeOperandBuiltins
Libs
  monadsyntax

(* The actual builtin returns its allocation operand for every decoder shape,
   including same-layout, dynamic members, and a zero-byte empty tuple. *)
Theorem tuple_immutable_decode_allocation_site:
  lower_abi_decode data info mn mx sz st = (out,final) /\
  fn_has_code st final func ==>
  ?inputs hs buf ready.
    abi_builtin_decode_header data mn mx st = (inputs,hs) /\
    compile_alloc_buffer sz hs = (buf,ready) /\ out = buf.buf_operand /\
    hs.cs_next_id = abi_builtin_decode_output_site st mn mx /\
    st.cs_next_id <= hs.cs_next_id /\ hs.cs_next_id < ready.cs_next_id /\
    ready.cs_next_id <= final.cs_next_id
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_decode_code >> strip_tac >>
  drule abi_builtin_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  qexistsl [`inputs`, `header_st`, `buf`, `ready`] >>
  gvs[abi_builtin_decode_output_site_def]
QED

(* The recursive decoder's effect preserves the output ALLOCA entry because
   that entry precedes the recursive decoder, not because LocMemory is fresh. *)
Theorem tuple_immutable_decode_retains_output:
  abi_builtin_allocation_frame next site sz initial prepared /\
  ((FLOOKUP initial.vs_allocas site = NONE /\ d = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas site = SOME (d,sz)) /\
  abi_decoder_effect first last lo hi nv limit_st d sz b cap prepared actual /\
  site < lo ==>
  FLOOKUP actual.vs_allocas site = SOME (d,sz)
Proof
  simp[abi_builtin_allocation_frame_def, abi_decoder_effect_def,
       abi_decoder_scratch_frame_def] >> strip_tac >>
  `FLOOKUP actual.vs_allocas site = FLOOKUP prepared.vs_allocas site` by
    metis_tac[] >>
  Cases_on `FLOOKUP initial.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

(* The external return tail returns its output allocation in BOTH keyword
   default branches, never the shared ABI input buffer or default operand.
   Call's final NONE is not evidence that has_default is false. *)
Theorem tuple_immutable_external_decode_tail:
  (do result <- compile_alloc_buffer sz;
      if has_default then
        compile_default_return_path ce ty dty input result.buf_operand def
          addr skip mn mx di
      else
        do hi <- compile_return_value_decode mn mx;
           compile_abi_decode_to_buf result.buf_operand (Lit 0w) MLOAD input hi di;
           comp_return result.buf_operand od od) sr = (out,sb) ==>
  ?buf ready. compile_alloc_buffer sz sr = (buf,ready) /\ out = buf.buf_operand
Proof
  Cases_on `has_default` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[compile_default_return_result]
QED

(* This premise is already in the frozen caller; it is not a proposed fix. *)
Theorem tuple_immutable_decode_target_occurs:
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (TupleTarget gs) (TypeBuiltin ann (AbiDecode F) ty args)) ==>
    occurs_abi_decode_target target tops) ==>
  occurs_abi_decode_target ty tops
Proof
  strip_tac >> first_x_assum irule >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def,
       expr_abi_decode_target_root_def]
QED

(* Interface / frozen-caller discharge ledger (bounded checkpoint only).

   RAW AbiDecode F
   ---------------
   supported_type_builtin_shape's AbiDecode F case requires [a], annotation =
   decoded type, supported_tuple_type, and at least two tuple members. Thus a
   top-level empty tuple is excluded here, although a tuple can contain empty
   or zero-layout members. The boundary facts above do not need positivity.
   compile_type_builtin_dispatch_body_def first compiles HD args, unwraps the
   Bytes input, then calls lower_abi_decode. F makes wrapped_ty = ret_ty.
   The result is as_ptr_val vv_ty LocMemory (out,final); for a tuple,
   unwrap_value just returns out. Reuse compile_abi_decode_memory_trace when
   the Bytes argument is already LocatedValue/LocMemory; nonmemory input
   needs its existing unwrap simulation first.

   tuple_immutable_decode_allocation_site binds the ACTUAL final operand out
   to the output allocation, identifies site = abi_builtin_decode_output_site
   st mn mx, and proves st.next_id <= site < final.next_id from fn_has_code.
   The recursive descriptor does not change that returned operand. There is
   no same-layout identity shortcut in lower_abi_decode. Dynamic bytes/string
   members likewise decode into the output; recursive decoding may additionally
   allocate scratch. The generic statement covers sz=0, but makes no runtime
   allocation assertion merely from compilation.

   Existing source-success runtime boundary to REUSE:
     lower_abi_decode_valid_unwrap (unwrap=F, ty=TupleT tys)
   Inputs: source evaluate_type_builtin success on [BytesV bs], coherent
   compiler/source decoder metadata, compile equation, fn_has_code and the
   phi-prefix condition, typed input Bytes memory and evaluated live data
   operand, abi_builtin_decode_resources, counter bounds, fresh_vars_wrt,
   not halted and runtime/compiler PC alignment.
   Outputs at ONE actual state: eval_operand out = SOME (n2w d), complete
   val_in_memory tv v d, abi_builtin_decode_effect, PC alignment, not halted,
   abi_decode_sim. This theorem supports source-valid (not only canonical)
   inputs; do NOT add canonical bytes equality as a frozen task premise.

   Caller routes versus still-unproved obligations:
   * Frozen type_stmt and expr_sim_inv give typing/environment agreement;
     body_inv supplies module and metadata agreement. These must be used to
     instantiate decoder coherence, type layout and source-success facts.
   * tuple_immutable_decode_target_occurs discharges the decoded target's
     occurrence DIRECTLY from the frozen statement occurrence premise; use
     body_inv's tops = cx_tops cx when entering expression body_pre. Occurrence
     is needed for the ABI unspecified-behaviour exemption; it is not itself
     a memory allocator bound or decoder scratch reservation.
   * expr_sim_inv / stmt_state_rel and input vv_post supply typed input memory
     and fresh registers at the actual post-input/unwrap state, not at the
     original statement state. Compiler counter monotonicity and fn_has_code
     splitting supply the subfragment limits and code containment.
   * resources expands to min<=LENGTH bs<=max, max<2**256, nonwrapping input
     and output ends, output/scratch disjointness, input payload disjoint from
     output+scratch, an absent-or-reused output allocation entry, and
     abi_decoder_budget on abi_builtin_allocate_state. These are NOT all
     consequences of the occurrence predicate. Constructing a suitable d,b,cap,
     first,last from the actual statement state is outstanding internal work.
   * The EXPORTED abi_builtin_decode_effect preserves allocation entries
     OUTSIDE [st.next_id,final.next_id); it deliberately says nothing about
     the new output site INSIDE that interval. Therefore its final post alone
     does not prove the desired retained allocation entry. Reuse the proof's
     prepared state, abi_builtin_allocation_frame and abi_decoder_effect:
     tuple_immutable_decode_retains_output proves the missing entry from that
     existing intermediate interface (site < recursive decoder start).
   * A strengthened whole-run boundary must retain that entry at the SAME
     actual state as the value, plus stmt_state_rel/local-region separation,
     containment/footprint <= type_memory_bytes and a gas_marked_path.
     abi_decode_sim is a run_from continuation relation, NOT such a gas path.
     No common-witness gas/ownership join has been proved in this checkpoint.

   EXTERNAL Call (TupleT tys) (ExtCall ...) args NONE
   ------------------------------------------------
   supported_external_call_contract permits pure target/positional/keyword
   operands, word argument types, supported_external_return_type, distinct
   opts and static ==> no EKValue; length args = 1 + argc + length opts.
   Important: the final NONE rules out the AST default expression field,
   NOT the EKDefault keyword. compile_ext_call_kwargs can set default_opt and
   hence has_default even in this syntax. Both return branches are covered by
   tuple_immutable_external_decode_tail. compile_default_return_result is
   reused rather than duplicating its proof. A default is STORED into the
   result allocation, not returned as a borrowed pointer.

   compile_call's ExtCall clause computes wrapped_return from signature ret,
   ret_mem_bytes = type_memory_bytes cenv ret, and dec_info at wrapped_return.
   Type annotation/signature ret agreement is a typing discharge, not an
   unconditional compiler equation. For ret = TupleT tys the NoneT branch is
   impossible. needs_external_call_wrap is false for LENGTH tys > 1, but TRUE
   for lengths 0/1: keep the wrapped descriptor in these cases. The singleton
   wrapper preserves memory size (reuse abi_decode_output_size); the result
   still occupies the tuple envelope, including zero bytes for TupleT [].
   The generic tail theorem does not assume a particular descriptor or size.
   The full helper allocates the shared call/return ABI
   buffer FIRST, then argument staging, CALL/STATICCALL and fail/cont blocks,
   then the distinct result allocation. The tail theorem is instantiated at
   sr, the compiler state entering the successful-call continuation block;
   its size is ret_mem_bytes, not ABI cap. The returned vv is LocatedValue
   ann (mk_ptr out LocMemory), and tuple unwrap is the identity on out.
   No same-layout/bytes member branch aliases buf_op as the returned operand.

   Runtime contracts to reuse, NOT duplicate:
     extcall_request_setup -> extcall_call_step -> extcall_return_values
   request_ready identifies the actual ABI buffer allocation, age interval,
   local/old-allocation/immutable/default separation, and source request.
   extcall_returned carries this after the call and returndata observation.
   extcall_return_values takes expr_body_pre, cap/layout equation, exact
   return-tail equation, code/ID distinctness and extcall_returned; it exports
   gas_summary_at ending in vv_post, at sb. These existing admitted ancestor
   facts are task-authorized; no new admission is added here.
   Frozen body_expr_ok and stmt_exprs_ok/call_evaluation_safe are the routes
   to expr_body_pre and operand simulations; support alone is not a runtime
   request_ready assertion. EKDefault requires its typed default-ready facts.
   The raw builtin target-occurrence premise is NOT a new requirement on an
   ExtCall: its ABI return type is governed by the signature/support metadata.

   Outstanding external ownership boundary: strengthen/derive the successful
   return-tail post to retain the result allocation entry, its sr-site age
   inside the full expression interval, entire tuple envelope and nonlocal
   separation at the gas_summary witness. vv_post's same-layout memory case
   does not already export those facts. The compiler tail equation above
   establishes operand identity only, not runtime freshness. Decode scratch
   and default-store frames must preserve the result allocation there. This
   is internal proof work, not evidence of a missing external premise.

   Disprove-first audit: checked the apparent alias branches (same-layout,
   zero output, default result). Both raw decode and both external tail
   branches return their allocated operand; no borrowed-return path was found.
   Reusing an ALLOCA at an already visited site is explicitly permitted by the
   resource contract: "fresh" must mean the age-bounded owned region, not
   unconditional absence in initial.vs_allocas. These facts do not rule out
   other bugs or constitute a checked counterexample to the frozen theorem.
   C0's gate remains closed pending actual-caller runtime ownership/gas joins
   and target-evaluation AND earlier-store pending-value preservation.
*)
