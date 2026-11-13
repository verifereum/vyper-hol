(* Re-establish body state at the actual singleton word staging endpoint. *)
Theory bodyAbiEncodeWordResultMemory
Ancestors
  bodyAbiEncodeWordMemory bodyAbiEncodeResultMemory bodyAbiEncodeAllocationState bodyAbiEncodeWordOutputFrame abiEncoderWindowContract abiEncodeWordWindowGrowth
  abiEncoderWindowPhase abiEncoderWindowMemFrame abiEncoderRegisteredEffect
  abiBuiltinEncodeWord abiEncoderWindowChild abiEncoderWindow fragExec
  abiCallerLocalScratch exprSimAlloc loweringHalt emitHelperProps localPtrsProps exprSimProps exprLoweringProps compileEnv loweringPosts
  venomState venomInst venomMemDefs valueEncoding finite_map pred_set words list arithmetic


Theorem abi_encode_word_source_state_mem:
  is_word_type (expr_type e) /\
  lower_value cfn ce (expr_type e) e origin = (value_op,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty
    (AbiEncode F method_id) ret_ty [e] origin = (vv,final) /\
  fn_has_code arg_st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce arg_st /\
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
    stmt_state_rel ctx func ce cx ee t /\ local_ptrs_reserved ce staged /\
    window_phase ctx func arg_st staged {arg_st.cs_next_id} [] s t /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    eval_operand buf.buf_operand t = SOME (n2w sb) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at staged x) /\
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e)) at av sb 32 t.vs_memory /\
    FLOOKUP t.vs_allocas arg_st.cs_next_id = SOME (sb,32) /\
    sb+32 <= t.vs_alloca_next /\ sb+32 < dimword (:256)
Proof
  strip_tac >> drule_all compile_abi_encode_word_trace >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule window_child_void_shape >> strip_tac >>
  drule lower_abi_encode_extends >> strip_tac >>
  `cs_extends arg_st staged` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code arg_st allocated func` by metis_tac[fn_has_code_split] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas arg_st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    (rpt strip_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[mk_inst_def, dimword_def]) >>
  `alloca_inv s /\ alloca_room ctx func s` by fs[stmt_state_rel_def] >>
  drule_all abi_encode_word_source_window_mem >> strip_tac >>
  `buf' = buf /\ allocated' = allocated` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `buf' = buf` SUBST_ALL_TAC >>
  qpat_x_assum `allocated' = allocated` SUBST_ALL_TAC >>
  `staged' = staged` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `staged' = staged` SUBST_ALL_TAC >>
  `out' = out` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `out' = out` SUBST_ALL_TAC >>
  `stmt_state_rel ctx func ce cx ee t` by
    (irule abi_encode_word_stage_state >> asm_rewrite_tac[] >>
     qpat_assum `MEM (mk_inst _ _ _ _) _` (irule_at Any) >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     qpat_assum `window_phase _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexistsl [`32`, `sb`] >> simp_tac (srw_ss()) [dimword_def] >>
     asm_rewrite_tac[] >>
     metis_tac[local_ptrs_reserved_fresh, LESS_EQ_REFL]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `local_ptrs_reserved ce staged` by
    (irule local_ptrs_reserved_next_var >> qexists `arg_st` >>
     asm_rewrite_tac[] >> simp_tac arith_ss []) >>
  qexistsl [`buf`, `allocated`, `staged`, `out`, `t`, `sb`] >>
  asm_rewrite_tac[] >> first_x_assum irule >> first_assum ACCEPT_TAC
QED
