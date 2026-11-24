Theory abiEncodeValuesFinish
Ancestors
  abiEncodeValuesLayout abiEncodeValuesPhases abiEncoderWindowPhase
  exprSimAbiEncodeExecFrame abiEncoderTuple abiEncoderOpenInput
  fragGasOriginPtr bodyPtrDefs ptrDiscipline fragExec emitHelper
  compileEnv valueEncodingDefs contractABI venomState venomInst
  words finite_map pred_set list

(* The last cursor load returns the size that the heads and tails occupy. *)
Theorem abi_encode_values_finish_run:
  emit_op MLOAD [Var cursor] st = (out,en) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\ ptr_covers G tn cursor s 32 /\
  slot + 32 <= s.vs_alloca_next /\ mem_word_at slot s.vs_memory = n2w (hl + tl) /\
  (!i. slot <= i /\ i < slot + 32 ==> i NOTIN tn.t_mem) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  LIST_REL abi_encoder_layout_valid tys vs /\
  hl = head_lengths tys 0 /\ tl = LENGTH (FLAT (abi_tuple_tails tys vs)) /\
  abi_encoder_tuple_prefix hl tys vs d s.vs_memory /\
  (!i. d <= i /\ i < d + hl ==> i NOTIN tn.t_mem) /\
  (!i. d + hl <= i /\ i < d + hl + tl ==> i NOTIN tn.t_mem) /\
  bytes = enc (Tuple tys) (ListV vs) ==>
  ?t G' tn'.
    eval_operand out t = SOME (n2w (LENGTH bytes)) /\ op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    mem_bytes_at d (LENGTH bytes) t.vs_memory = bytes /\
    (!i. d <= i /\ i < d + LENGTH bytes ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en {} [] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\ t.vs_memory = s.vs_memory /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    run_inst_seq (emitted_insts st en) s = OK (t with vs_inst_idx := s.vs_inst_idx)
Proof
  strip_tac >>
  drule_all abi_encode_values_output_ready >> strip_tac >>
  drule_all abi_encode_values_cursor_load_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  qpat_x_assum `hl = _` SUBST_ALL_TAC >>
  qpat_x_assum `tl = _` SUBST_ALL_TAC >>
  qpat_x_assum `bytes = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  qpat_assum `!j. d <= j /\ j < d + head_lengths tys 0 + _ ==> _`
    (qspec_then `i` mp_tac) >>
  impl_tac >- decide_tac >> strip_tac >> metis_tac[]
QED

Theorem abi_encode_values_finish:
  emit_op MLOAD [Var cursor] st = (out,en) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\ ptr_covers G tn cursor s 32 /\
  slot + 32 <= s.vs_alloca_next /\ mem_word_at slot s.vs_memory = n2w (hl + tl) /\
  (!i. slot <= i /\ i < slot + 32 ==> i NOTIN tn.t_mem) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  LIST_REL abi_encoder_layout_valid tys vs /\
  hl = head_lengths tys 0 /\ tl = LENGTH (FLAT (abi_tuple_tails tys vs)) /\
  abi_encoder_tuple_prefix hl tys vs d s.vs_memory /\
  (!i. d <= i /\ i < d + hl ==> i NOTIN tn.t_mem) /\
  (!i. d + hl <= i /\ i < d + hl + tl ==> i NOTIN tn.t_mem) /\
  bytes = enc (Tuple tys) (ListV vs) ==>
  ?t G' tn'.
    eval_operand out t = SOME (n2w (LENGTH bytes)) /\ op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    mem_bytes_at d (LENGTH bytes) t.vs_memory = bytes /\
    (!i. d <= i /\ i < d + LENGTH bytes ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en {} [] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\ t.vs_memory = s.vs_memory /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> drule_all abi_encode_values_finish_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED
