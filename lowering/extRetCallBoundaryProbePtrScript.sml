Theory extRetCallBoundaryProbePtr
Ancestors
  extRetNormalizeContractProbePtr intCallStep exprLowering context
  compileEnv emitHelper intCallReturnMem valueEncoding vyperValue
  stmtLowering exprLoweringProps emitHelperProps valueCopy intCallReturn
  venomExecSemantics venomInst venomState bodyPtrDefs

Definition nested_call_probe_memory_def:
  nested_call_probe_memory =
    REPLICATE 287 (0w:word8) ++ [1w] ++
    REPLICATE 31 0w ++ [11w] ++
    REPLICATE 31 0w ++ [1w] ++
    REPLICATE 31 0w ++ [22w]
End

(* The actual empty-argument internal-call producer. The emitted call takes
   exactly the allocated 128-byte buffer, not an annotation-sized 192-byte
   buffer. Execution of the callee is deliberately not assumed here. *)
Theorem nested_call_buffer_producer_probe:
  !cfn ce st buf sa u sb aty dret pvs.
    ce.ce_func_info "f" = (0,128,pvs) /\
    ce.ce_func_return_type "f" =
      ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2) /\
    compile_alloc_buffer 128 st = (buf,sa) /\
    emit_void INVOKE
      [Label (internal_fn_label (ce.ce_func_ids "f") "f"
                (ce.ce_func_param_types "f") ce.ce_is_ctor);
       buf.buf_operand] sa = (u,sb) ==>
    compile_call cfn ce aty aty (IntCall (NONE,"f")) [] dret st =
      (LocatedValue
         (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2))
         (base_ptr buf),sb)
Proof
  rpt strip_tac >>
  simp[compile_call_def, nsid_to_string_def, compile_multi_vvs_def,
       compile_stage_intcall_args_def, comp_return_def]
QED

(* Conditional endpoint experiment using the existing callee return contract,
   not an invented annotated post. A run still has to establish intret_mem_q. *)
Theorem nested_call_return_endpoint_incompatible_probe:
  !fn ce cx bw es ir s.
    let word = BaseTV (UintT 256) in
    let sty = ArrayTV (ArrayTV word (Dynamic 1)) (Fixed 2) in
    let aty = ArrayTV (ArrayTV word (Dynamic 2)) (Fixed 2) in
    let v = ArrayV (SArrayV
      [(0,ArrayV (DynArrayV [IntV 11]));
       (1,ArrayV (DynArrayV [IntV 22]))]) in
    intret_mem_q fn ce cx sty bw v es (IntRet ir s) ==>
    ~val_in_memory aty v (w2n bw) s.vs_memory
Proof
  simp[intret_mem_q_def, val_in_memory_def, type_memory_size_def,
       val_to_w256_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `i2w 22 = 1w` mp_tac >> EVAL_TAC >>
  simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

(* The probes below execute the actual emitted return suffix at explicit
   literal operands and concrete entry bytes. They avoid assuming the full
   stmt_state_rel required by compile_internal_return_memory_frag. They do
   not construct a complete source callee or prove its entry is reachable.
   Consequently none is a counterexample to external_frame_ret_ok_ptr. *)

(* Isolate the actual memory-return suffix, with literal source, return
   buffer and return PC. This is compiler output, not a hand-written copy. *)
Theorem nested_call_return_suffix_shape_probe:
  !ce sa sb.
    type_memory_bytes ce
      (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2)) = 128 /\
    compile_internal_return ce (SOME (Lit 256w)) (Lit 0w) 0
      (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2))
      (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2))
      [] (SOME (Lit 512w)) sa = ((),sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id MCOPY [Lit 512w; Lit 256w; Lit 128w] [];
       mk_inst (sa.cs_next_id + 1) RET [Lit 0w] []]
Proof
  rpt strip_tac >>
  gvs[compile_internal_return_def, compile_store_memory_def,
      is_word_type_def, is_bytestring_type_def,
      numeralTheory.numeral_suc, compile_copy_memory_def,
      emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, emit_def, comp_return_def, emitted_insts_def] >>
  qpat_x_assum `_ = ((),sb)` mp_tac >>
  rewrite_tac[numLib.num_CONV ``128``, compile_copy_memory_def] >>
  simp[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem nested_call_return_suffix_run_probe:
  !ce sa sb s.
    type_memory_bytes ce
      (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2)) = 128 /\
    compile_internal_return ce (SOME (Lit 256w)) (Lit 0w) 0
      (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2))
      (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2))
      [] (SOME (Lit 512w)) sa = ((),sb) ==>
    run_inst_seq (emitted_insts sa sb) s =
      IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
        (mcopy 512 256 128 s)
Proof
  rpt strip_tac >> drule_all nested_call_return_suffix_shape_probe >>
  strip_tac >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
       eval_operand_def, eval_operands_def, wordsTheory.dimword_def]
QED

(* Concrete entry bytes: [[11],[22]] at 256. At the copied result, the
   widened second header address (512+96) holds 22, not the length 1. *)
Theorem nested_call_copied_second_header_probe:
  !s.
    mem_word_at 608
      (mcopy 512 256 128
        (s with vs_memory := nested_call_probe_memory)).vs_memory = 22w
Proof
  gen_tac >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:8)``]
QED

Theorem nested_call_suffix_entry_representation_probe:
  val_in_memory
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Fixed 2))
    (ArrayV (SArrayV
      [(0,ArrayV (DynArrayV [IntV 11]));
       (1,ArrayV (DynArrayV [IntV 22]))]))
    256 nested_call_probe_memory
Proof
  simp[val_in_memory_def, type_memory_size_def, val_to_w256_def] >>
  EVAL_TAC >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:8)``]
QED

(* INVOKE's successful return merge retains precisely the callee's copied
   bytes. This probes the merge itself; setup_callee/run_blocks and the
   pointer ghost are not asserted by this concrete suffix experiment. *)
Theorem nested_call_merge_second_header_probe:
  !caller callee ret.
    callee.vs_memory =
      (mcopy 512 256 128
        (caller with vs_memory := nested_call_probe_memory)).vs_memory ==>
    mem_word_at 608
      (adopt_return_fmp ret (merge_callee_state caller callee)).vs_memory = 22w
Proof
  rpt strip_tac >> Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def,
       nested_call_copied_second_header_probe]
QED

(* This is the exact annotation-indexed conjunct used by expr_sim_ptr's
   normal post, refuted independently of the chosen ghost and taint. *)
Theorem nested_call_annotation_ptr_post_impossible_probe:
  !cx op G tn s.
    eval_operand op s = SOME 512w /\ mem_word_at 608 s.vs_memory = 22w ==>
    ~ptr_val_ok cx
      (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (Fixed 2))
      (ArrayV (SArrayV
        [(0,ArrayV (DynArrayV [IntV 11]));
         (1,ArrayV (DynArrayV [IntV 22]))])) op G tn s
Proof
  rpt strip_tac >>
  gvs[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def,
      evaluate_type_def, type_slot_size_def, wordsTheory.dimword_def] >>
  first_x_assum (qspec_then `s.vs_memory` mp_tac) >>
  simp[mem_agree_outside_def, val_in_memory_def, type_memory_size_def,
       val_to_w256_def, wordsTheory.dimword_def] >>
  EVAL_TAC
QED

(* Boundary conclusion and remaining limitation:
   - The source entry bytes satisfy the callee's declared representation.
   - Its emitted suffix is MCOPY 128 followed by RET; running it copies
     1,11,1,22 to the caller buffer. Successful INVOKE's state merge keeps
     the word 22 at offset 96. No choice of ghost/taint can make the
     annotation-indexed ptr_val_ok normal post true at that endpoint.
   - expr_sim_ptr_def:239 requires exactly that annotation-indexed post;
     expr_vv_sim_ptr_def:268 and ptr_vv_ok_def:153-155 require its memory
     counterpart for a LocatedValue at LocMemory. Thus using an actual
     declared-layout endpoint does NOT justify changing the post's type.
   Missing for a full-program contradiction is a reachable expression entry
   satisfying ALL universal simulation premises (fn_has_code, ghost_inv,
   gas_admissible, state relation, etc.), its complete INVOKE execution,
   and deterministic identification of that endpoint with the counted
   simulation endpoint. The explicit byte entry here is not that premise.
   A protected-definition change is NOT justified by this suffix experiment;
   first determine whether universal simulation excludes changed-layout calls
   and exploit that fact, or supply an execution-sensitive layout bridge.
   Frozen theorem falsehood and normalization pointer safety remain open. *)
