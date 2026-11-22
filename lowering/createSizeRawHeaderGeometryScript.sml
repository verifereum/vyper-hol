(* Allocation and byte widths at the actual raw CREATE snapshot site. *)
Theory createSizeRawHeaderGeometry
Ancestors
  createBlueprintRawCopyLayout exprLowering exprLoweringProps compileEnv
  copyExecution abiDecoderBytesTyped abiEncodeArgsCase loweringHalt
  exprPtrUnwrapAllocSeparation fragExec emitHelperProps loweringPosts
  exprSimHyps valueEncodingProps context words arithmetic pair

Theorem create_raw_snapshot_alloc_interval:
  compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,sm) /\
  compile_create_snapshot ce vv ty a = (snap,b) /\ fn_has_code a b fn ==>
  snap = buf.buf_operand /\ fn_has_code a sm fn
Proof
  strip_tac >>
  `snap = buf.buf_operand /\ cs_extends sm b` by
    (qpat_x_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
     simp[compile_create_snapshot_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >>
     Cases_on `vv_location vv` >> simp[]
     >- (gvs[comp_bind_def] >> rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
         metis_tac[ci_mono_emit_op, ci_mono_compile_copy_memory_dynamic, ci_mono_trans,
                   ci_mono_def, SND]) >>
     rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >>
     simp[comp_bind_def, compile_slot_to_memory_shape] >>
     rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[comp_return_def, slot_copy_extends] >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, ci_mono_emit_op,
               ci_mono_compile_copy_memory_dynamic, ci_mono_trans, ci_mono_def, SND]) >>
  metis_tac[compile_alloc_buffer_extends, fn_has_code_split]
QED

Theorem create_raw_header_capacity:
  expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  lowered_value_type ce e = BaseT (BytesT (Dynamic n)) ==>
  32 <= type_memory_bytes ce (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size (BaseTV (BytesT (Dynamic n))) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) < 2 ** 64
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic k))) /\
   ~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_copy_ok >> strip_tac >>
  `type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits, abi_args_fits_memory_bytes] >>
  assume_tac (Q.INST [`n` |-> `n`, `ce` |-> `ce`] abi_decoder_bytes_copy_size) >>
  gvs[] >> decide_tac
QED

Theorem create_raw_header_slot_nonwrap:
  compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,sm) /\
  fn_has_code a sm fn /\ stmt_state_rel H ctx fn ce cx es u /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2 ** 64 ==>
  w2n (n2w (buffer_allocation_base u a.cs_next_id) : bytes32) +
    32 * ((type_memory_bytes ce ty + 31) DIV 32) < dimword (:256)
Proof
  strip_tac >> drule_all unwrap_alloc_typed_loop_bound >> strip_tac >>
  `buffer_allocation_base u a.cs_next_id < dimword (:256)` by
    (qpat_x_assum `_ + _ < 2 ** 256` mp_tac >> simp[dimword_def] >> decide_tac) >>
  `32 * ((type_memory_bytes ce ty + 31) DIV 32) = 32 * type_slot_size tv` by
    (simp[type_memory_size_slots, Once MULT_COMM, ADD_DIV_ADD_DIV]) >>
  simp[w2n_n2w, dimword_def] >>
  qpat_x_assum `_ + _ < 2 ** 256` mp_tac >> simp[] >> decide_tac
QED
