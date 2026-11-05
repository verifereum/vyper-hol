Theory extRetCallBoundaryProbePtr
Ancestors
  extRetNormalizeContractProbePtr intCallStep exprLowering context
  compileEnv emitHelper intCallReturnMem valueEncoding vyperValue

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

(* Execution mapping still to be discharged (not claimed by these probes):
   intCallReturnMem.compile_internal_return_memory_frag yields intret_mem_q
   for an actual internal return, under its expression-value, state, freshness,
   type-size and buffer endpoint premises. The theorem above then rules out
   val_in_memory at the widened annotation at that SAME state. intCallReturn's
   invoke_intret_state_rel transports the callee state back to the caller;
   its memory preservation must be checked before applying this contradiction
   to expr_post. Neither probe executes the complete callee or establishes the
   entry premises of compile_internal_return_memory_frag for a source program.
   Remaining experiment: instantiate a callee returning [[11],[22]], trace
   its actual writes, INVOKE merge and pointer ghost; then compare with the
   universal expr_sim_ptr/expr_vv_sim_ptr endpoint. The conditional incompatibility
   alone is not evidence that external_frame_ret_ok_ptr is false. *)
