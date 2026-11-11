(* The singleton word source is the actual reusable ALLOCA followed by MSTORE. *)
Theory bodyAbiEncodeWordMemory
Ancestors
  abiBuiltinEncodeWord abiEncodeAllocationPhase windowPhaseMem
  abiEncoderWindowChild abiEncoderWindow abiEncoderWindowPhase
  abiEncoderRegisteredEffect loweringHalt emitHelperProps fragExec
  compileEnv venomState venomExecSemantics valueEncodingProps
  instIdxIndep finite_map words list pred_set arithmetic memContinuation exprLoweringProps freshWrites

Theorem abi_encode_word_stage_mem[local]:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\
  fn_has_code st staged func /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  eval_operand value_op s = SOME w /\
  (!x. value_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t sb. window_phase ctx func st staged {st.cs_next_id} [] s t /\
    mem_cont_sim ctx func s t /\
    eval_operand buf.buf_operand t = SOME (n2w sb) /\ mload sb t = w /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at staged x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (sb,32) /\
    sb+32 <= t.vs_alloca_next /\ sb+32 < dimword (:256) /\
    ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ sb = s.vs_alloca_next) \/
     FLOOKUP s.vs_allocas st.cs_next_id = SOME (sb,32))
Proof
  strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule window_child_void_shape >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `32 < dimword (:256)` by simp_tac (srw_ss()) [dimword_def] >>
  drule_all abi_encode_alloc_window_phase >>
  disch_then (qx_choose_then `u` (qx_choose_then `d`
    (map_every assume_tac o CONJUNCTS))) >>
  rename1 `window_phase ctx func st allocated _ _ s u` >>
  `eval_operand value_op u = SOME w` by metis_tac[window_phase_operand] >>
  `alloca_inv u /\ alloca_room ctx func u /\ ~u.vs_halted /\
   u.vs_current_bb = allocated.cs_current_bb /\
   u.vs_inst_idx = LENGTH allocated.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `d < dimword (:256)` by decide_tac >>
  drule_all window_cursor_store_phase_mem >> strip_tac >>
  qexistsl_tac [`(mstore d w u) with vs_inst_idx := LENGTH staged.cs_current_insts`, `d`] >>
  conj_tac
  >- (irule window_phase_chain >>
      qexistsl_tac [`{st.cs_next_id}`, `[]`, `allocated`, `{st.cs_next_id}`, `[]`, `u`] >> simp[]) >>
  conj_tac >- metis_tac[mem_cont_sim_trans] >>
  conj_tac
  >- (pure_rewrite_tac[eval_op_inst_idx] >> simp[]) >>
  conj_tac
  >- (`mload d (mstore d w u) = w` by simp_tac (srw_ss()) [venomMemPropsTheory.mload_mstore_same] >>
      pop_assum mp_tac >> simp_tac (srw_ss()) [mload_def]) >>
  conj_tac >- metis_tac[not_fresh_at_mono, LESS_EQ_REFL] >>
  simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM] >>
  asm_rewrite_tac[]
QED

(* Compiler trace and source input share exactly the safe staging endpoint.
   The phase retains all older variables, allocation rows and local framing. *)
Theorem abi_encode_word_source_window_mem:
  is_word_type (expr_type e) /\
  lower_value cfn ce (expr_type e) e origin = (value_op,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty
    (AbiEncode F method_id) ret_ty [e] origin = (vv,final) /\
  fn_has_code arg_st final func /\ alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas arg_st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  eval_operand value_op s = SOME w /\
  (!x. value_op = Var x ==> not_fresh_at arg_st x) /\
  has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  word_to_bytes w T = enc at av /\
  ~s.vs_halted /\ s.vs_current_bb = arg_st.cs_current_bb /\
  s.vs_inst_idx = LENGTH arg_st.cs_current_insts ==>
  ?buf allocated staged out t sb.
    compile_alloc_buffer 32 arg_st = (buf,allocated) /\
    emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\
    lower_abi_encode F (OPTION_MAP bytes_method_id_word method_id) buf.buf_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
      (abi_size_bound ce.ce_struct_fields (expr_type e)) staged = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory) /\
    fn_has_code arg_st staged func /\ fn_has_code staged final func /\
    staged.cs_next_var <= final.cs_next_var /\ staged.cs_next_id <= final.cs_next_id /\
    window_phase ctx func arg_st staged {arg_st.cs_next_id} [] s t /\
    mem_cont_sim ctx func s t /\
    eval_operand buf.buf_operand t = SOME (n2w sb) /\ mload sb t = w /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at staged x) /\
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e)) at av sb 32 t.vs_memory /\
    FLOOKUP t.vs_allocas arg_st.cs_next_id = SOME (sb,32) /\
    sb+32 <= t.vs_alloca_next /\ sb+32 < dimword (:256) /\
    ((FLOOKUP s.vs_allocas arg_st.cs_next_id = NONE /\ sb = s.vs_alloca_next) \/
     FLOOKUP s.vs_allocas arg_st.cs_next_id = SOME (sb,32))
Proof
  strip_tac >> drule_all compile_abi_encode_word_trace >> strip_tac >>
  drule_all abi_builtin_encode_word_context >> strip_tac >>
  drule_all abi_encode_word_stage_mem >>
  disch_then (qx_choose_then `t` (qx_choose_then `sb`
    (map_every assume_tac o CONJUNCTS))) >>
  `abi_encoder_input (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
    at av sb 32 t.vs_memory` by
    metis_tac[abi_builtin_encode_staged_word_input] >>
  `abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
    at av sb 32 t.vs_memory` by
    (`type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e) = AbiCopy 32` by
       metis_tac[abi_builtin_encode_word_info] >>
     qpat_x_assum `abi_encoder_input _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `type_to_abi_enc_info _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abiEncoderInputTheory.abi_encoder_input_copy_iff, abi_encoder_window_copy_iff]) >>
  qexistsl_tac [`buf`, `allocated`, `staged`, `out`, `t`, `sb`] >> asm_rewrite_tac[]
QED
