(* Open-input companion: retain complete builtin finish and frame guarantees. *)
Theory abiScratchBuiltinOpenSource
Ancestors
  abiScratchBuiltinSource abiEncoderSharedRecursive abiEncoderSharedContract
  abiEncoderProps builtinAbi exprLoweringProps compileEnv context emitHelperProps
  abiDecoderContract abiScratchEncoderContract contractABI words arithmetic
  abiEncoderCounters abiBuiltinEncodeCode abiEncoderAppend fragExec

Theorem abi_scratch_builtin_body_finish_open:
  compile_abi_encode_to_buf dst src (type_to_abi_enc_info sf ce ty) ready = (len_op,body_end) /\
  abi_builtin_encode_finish buf len_op mid_size body_end = ((),final) /\
  fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (type_to_abi_enc_info sf ce ty,at,av) (ready,src,dst)
    (sb,source_cap) (p+32+mid_size,LENGTH (enc at av)) (first,last,b,cap) initial /\
  eval_operand buf initial = SOME (n2w p) /\ abi_decoder_operand_live ready.cs_next_var buf /\
  abi_footprint_disjoint p (32+mid_size+LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ first <= ready.cs_next_id /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = ready.cs_current_bb /\
  initial.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH (enc at av)+mid_size) /\
    mem_bytes_at (p+32+mid_size) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_bytes_at (p+32) mid_size actual.vs_memory = mem_bytes_at (p+32) mid_size initial.vs_memory /\
    abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
      limit_st p (32+mid_size+LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends body_end final` by (irule cs_extends_same_block >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `abi_encoder_shared (type_to_abi_enc_info sf ce ty)` by
    simp[abi_encoder_shared_translation] >>
  `body_end.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_id <= last /\
   body_end.cs_next_id <= final.cs_next_id` by
    (Cases_on `mid_size > 0` >> gvs[] >> decide_tac) >>
  qpat_assum `final.cs_blocks = body_end.cs_blocks` (fn blocks =>
    qpat_assum `final.cs_current_bb = body_end.cs_current_bb` (fn label =>
    qpat_assum `ready.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [blocks,label]))) >>
  drule_all abi_encoder_shared_run >> strip_tac >>
  first_x_assum (qspec_then `ctx` strip_assume_tac) >>
  drule abi_encoder_shared_endpoint_sim >> strip_tac >>
  qpat_x_assum `abi_encoder_shared_endpoint _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_endpoint_def]) >>
  `p < dimword (:256)` by
    (qpat_x_assum `abi_encoder_shared_input _ _ _ _ _ _` mp_tac >>
     simp[abi_encoder_shared_input_def] >> strip_tac >> decide_tac) >>
  irule abi_scratch_builtin_compose >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`body_end`, `len_op`] >> fs[AC ADD_COMM ADD_ASSOC]
QED
